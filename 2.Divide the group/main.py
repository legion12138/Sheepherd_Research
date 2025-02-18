from utils import gui
from utils import common
from utils import sheep
import numpy as np
import time
import math
from strategy_pattern import shepherdR
from strategy_pattern import sheepR
from strategy_pattern import behaviors as cb

def init_sheep(canvas_local, n):
    agents = {}
    X = list()
    for i in range(n):
        np.random.seed(i)
        x = np.random.randint(200, 300)
        y = np.random.randint(300, 400)
        X.append([x, y])
        agents['sheep' + str(i)] = sheep.Agent(canvas_local, x - 5, y - 5, x + 5, y + 5, 'green')

    herd_a = sheep.Agent(canvas_local, 50, 550, 60, 560, 'red')
    return np.array(X, np.float64), agents, herd_a

def draw_centers_on_canvas(canvas_local, centers):
    canvas_local.delete("center")
    for center in centers:
        x, y = center
        canvas_local.create_oval(x - 5, y - 5, x + 5, y + 5, fill="blue", tags="center")

def angle_between(x, y):
    dot_product = np.dot(x, y)
    norm_x = np.linalg.norm(x)
    norm_y = np.linalg.norm(y)
    if norm_x == 0 or norm_y == 0:
        cos_theta = 0
    else:
        cos_theta = np.clip(dot_product / (norm_x * norm_y), -1.0, 1.0)
    angle = np.arccos(cos_theta)
    return angle


def run_animation(all_sheep, sheep_dict, herd, canvas_local):
    step = 0
    r_dist = 60
    r_rep = 14
    speed = 5
    n = len(all_sheep)
    app_dist = n + 50
    fn = math.sqrt(n) * r_rep
    last_vector = np.zeros((n, 2), dtype=np.float32)
    theta = math.pi / 6
    count = 0
    flag = 0
    centers = []
    
    herd_instance = shepherdR.Shepherd(cb.NewCBehavior())

    while True:
        herd_point = herd.position2point().copy()
        g_mean = np.array([np.mean(all_sheep[:, 0]), np.mean(all_sheep[:, 1])])
        max_cluster, min_cluster, sheep_group = herd_instance.optics_clustering(all_sheep, 10)
        if angle_between(min_cluster - max_cluster, herd_point - max_cluster)- 90.0 > 20:
            herd_instance.driving(herd, max_cluster, min_cluster, speed, app_dist)
        else:
            herd_instance.open(herd, max_cluster, speed, app_dist)
        
        sheepR.sheep_move(herd_point, all_sheep, r_dist, r_rep, speed, sheep_dict, last_vector)

        tk.update()
        time.sleep(0.01)

        if step > 5000:
            for per_sheep in sheep_dict.values():
                per_sheep.delete()
            herd.delete()
            break

        step += 1

    return step

if __name__ == '__main__':
    tk, canvas = gui.init_tkinter()
    steps = []
    for n in range(50, 51):
        all_sheep, sheep_dict, shepherd_a = init_sheep(canvas, n)
        step = run_animation(all_sheep, sheep_dict, shepherd_a, canvas)
        print("current {}, dispersion {}:".format(n, step))
        steps.append(step)
    print("knn farthest dist animation over!")
    common.print_list(steps)
    tk.mainloop()
