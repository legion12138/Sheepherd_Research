import cv2
import numpy as np
import matplotlib.pyplot as plt
import csv
import matplotlib.animation as animation
import matplotlib.font_manager as fm
import pandas as pd
import math
import time  # 导入time模块
import math
from math import sqrt
# 1. 导入图片
image_path = 'd:/Code/Python/assets/route2.jpg'  # 图片路径
image = cv2.imread(image_path)
gray = cv2.cvtColor(image, cv2.COLOR_BGR2GRAY)

# 2. 边缘检测
edges = cv2.Canny(gray, 50, 150)

# 3. 轮廓检测
contours, _ = cv2.findContours(edges, cv2.RETR_TREE, cv2.CHAIN_APPROX_SIMPLE)

# 4. 提取轨迹坐标
# 选择最大的轮廓作为轨迹（假设图像中只有一个主要轮廓）
largest_contour = max(contours, key=cv2.contourArea)
x_coords = largest_contour[:, 0, 0]
y_coords = largest_contour[:, 0, 1]
y_coords = -y_coords+1500  # 反转 x 轴的值
#提取x,y坐标的范围，为后续动态调整坐标轴做准备
x_min, x_max = np.min(x_coords), np.max(x_coords)
y_min, y_max = np.min(y_coords), np.max(y_coords)
# 5. 将坐标导出到CSV文件中
csv_file_path = 'd:/Code/Python/route_coordinates.csv'  # 保存的CSV文件路径
with open(csv_file_path, mode='w', newline='') as file:
    writer = csv.writer(file)
    writer.writerow(['x', 'y'])  # 写入表头
    for x, y in zip(x_coords, y_coords):
        writer.writerow([x, y])


# 设置中文字体
zhfont1 = fm.FontProperties(fname='C:/Windows/Fonts/simsun.ttc')  # 指定中文字体文件路径

# 参数
L = 2000  # 场地大小
N = 10  # 绵羊数量
k = int(0.7 * N)  # 最近邻居数量
rs = 40  # 绵羊感知距离
ra = 10  # 绵羊相互作用距离
δ = 5  # 绵羊每时间步移动距离
δs1 = 10  # 牧羊犬每时间步移动距离
δs2 = 10 
h = 0.5  # 绵羊之间的相互吸引参数
c = 1.05  # 绵羊对牧羊犬的反应参数
ρa = 2  # 绵羊之间的排斥参数
ρs = 1  # 绵羊对牧羊犬的排斥参数
e = 0.5  # 噪声参数
ec = ra  # 牧羊犬收集行为的参数
max_distance = 20  # 允许的最大偏离距离
f_N = ra * N**(2/3)  # 计算参数f_N
count=0
# 读取目标点
# 获取CSV文件的总行数
#nrows=int(total_rows/2)
total_rows = sum(1 for row in open('route_coordinates.csv')) - 1  # 减去标题行
target_df = pd.read_csv('route_coordinates.csv')  
x = target_df['x'].to_numpy()
y = target_df['y'].to_numpy()
target_points = np.column_stack((x, y))  # 合并 x 和 y 为二维数组

# 初始化位置
R = 100  # 绵羊位置相对于中心的最大偏移量
center = np.array([327, 1440])  # 中心位置  
offsets = (np.random.rand(N, 2) * 2 - 1) * R  # 生成随机偏移量
sheep_positions = center + offsets  # 绵羊位置
previous_positions = np.copy(sheep_positions)  # 上一步羊的位置与当前位置相同
sheepdog1_position = [330, 1450]  # 第一只牧羊犬初始位置
sheepdog2_position = [330, 1450]  # 第一只牧羊犬初始位置

# 计算k只羊的局部中心位置
def local_center_mass(sheep_positions, i, k):
    distances = np.linalg.norm(sheep_positions - sheep_positions[i], axis=1)
    nearest_neighbors = sheep_positions[np.argsort(distances)[:k]]
    return np.mean(nearest_neighbors, axis=0)


# 更新绵羊位置
def update_sheep_positions(sheep_positions, previous_positions, sheepdog1_position, sheepdog2_position):
    new_positions = []
    new_previous_positions = np.copy(sheep_positions)  # 更新当前位置作为下一次迭代的上一位置
    for i, position in enumerate(sheep_positions):
        LCM = local_center_mass(sheep_positions, i, k)
        #计算向局部中心靠近的向量
        direction_to_center = (LCM - position) / np.linalg.norm(LCM - position)
        #计算羊群排斥力
        repulsion = np.zeros(2)
        for j, other_position in enumerate(sheep_positions):
            if i != j and np.linalg.norm(position - other_position) < ra:
                repulsion += (position - other_position) / np.linalg.norm(position - other_position)
        #羊与牧羊犬1的排斥力
        if np.linalg.norm(position - sheepdog1_position) < rs:
            direction_to_dog1 = (position - sheepdog1_position) / np.linalg.norm(position - sheepdog1_position)
        else:
            direction_to_dog1 = np.zeros(2)
        #羊与牧羊犬2的排斥力
        if np.linalg.norm(position - sheepdog2_position) < rs:
            direction_to_dog2 = (position - sheepdog2_position) / np.linalg.norm(position - sheepdog2_position)
        else:
            direction_to_dog2 = np.zeros(2)
        #噪音
        noise = np.random.randn(2)
        
       # 计算惯性项
        inertia = -position + previous_positions[i]
        norm=np.linalg.norm(inertia)
        if norm==0:
            inertia=0
        else :
            inertia/=np.linalg.norm(inertia)
        Hi_prime = h * inertia+ c * direction_to_center + ρa * repulsion + ρs * (direction_to_dog1 + direction_to_dog2) + e * noise 
        Hi_prime /= np.linalg.norm(Hi_prime)
        
        new_position = position + δ * Hi_prime
        
        # 确保位置在边界内
        if new_position[0] < 0 or new_position[0] > L:
            new_position[0] = position[0] - δ * Hi_prime[0]
        if new_position[1] < 0 or new_position[1] > L:
            new_position[1] = position[1] - δ * Hi_prime[1]
        
        new_positions.append(new_position)
    return np.array(new_positions),new_previous_positions

# 第一只牧羊犬驱赶函数
def drive_sheep(sheep_positions, sheepdog_position, index,initial_drive=True,flag=False):
    GCM = np.mean(sheep_positions, axis=0)  # 计算羊群的全局中心
    target_point = target_points[index]
    next_target_point = target_points[index + 1]
    flag=False
    if initial_drive:
        # 初始阶段，将羊群质心驱赶到目标点的位置
        direction_to_target=GCM-target_point
        if np.linalg.norm(direction_to_target) < 10:  # 如果接近目标位置，完成初始驱赶
            initial_drive = False  # 完成初始驱赶，切换到正常驱赶模式
            Pd = GCM + (direction_to_target / np.linalg.norm(direction_to_target)) * f_N
        else:
            Pd = GCM + (direction_to_target / np.linalg.norm(direction_to_target)) * f_N
        direction = (Pd - sheepdog_position) / np.linalg.norm(Pd - sheepdog_position)
        new_position = sheepdog_position + δs1 * direction
    else:
        # 计算相邻目标点的切线方向
        if next_target_point[0] == target_point[0]:
            if next_target_point[1]>target_point[1]:
                tangent_slope = 1000.0
            else:
                tangent_slope = -1000.0
        else:
            tangent_slope = (next_target_point[1] - target_point[1]) / (next_target_point[0] - target_point[0])
        
        tangent_direction = np.array([1, tangent_slope])#将切线的数值转化为向量
        tangent_direction /= np.linalg.norm(tangent_direction)
        direction_to=GCM-target_point
        direction_to /=np.linalg.norm(direction_to)
        tangent_direction=0.3*tangent_direction+0.7*direction_to
        #Pd = GCM + tangent_direction * (f_N if (next_target_point[0] - target_point[0]) < 0 else -f_N)#将两种情况变为四种情况
        Pd=GCM + tangent_direction*f_N
        direction = (Pd - sheepdog_position) / np.linalg.norm(Pd - sheepdog_position)
        new_position = sheepdog_position + δs1 * direction
        if np.linalg.norm(abs(target_point-GCM)) < 50: # 如果绵羊距离全局中心质量的最大距离小于f_N
            flag=True
            index += 1
    
    return new_position, index, initial_drive,flag
#第二只牧羊犬的驱赶
def drive_sheep_initial(sheep_positions, sheepdog_position):
    target_point = target_points[0]
    GCM = np.mean(sheep_positions, axis=0)  # 计算未在目标区域内的绵羊的全局中心质量
    direction_to_target=GCM-target_point
    Pd = GCM + (direction_to_target / np.linalg.norm(direction_to_target)) * f_N
    direction = (Pd - sheepdog_position) / np.linalg.norm(Pd - sheepdog_position)
    new_position = sheepdog_position + δs2 * direction
    
    # 边界检查与反弹
    if new_position[0] < 0 or new_position[0] > L:
        new_position[0] = sheepdog_position[0] - δs2 * direction[0]  # 如果超出边界，反弹
    if new_position[1] < 0 or new_position[1] > L:
        new_position[1] = sheepdog_position[1] - δs2 * direction[1]  # 如果超出边界，反弹
    
    return new_position  # 返回更新后的牧羊犬位置
# 第二只牧羊犬的聚集函数
def collect_sheep(sheep_positions, sheepdog_position):
    GCM = np.mean(sheep_positions, axis=0)  # 计算绵羊的全局中心
    distances = np.linalg.norm(sheep_positions - GCM, axis=1)  # 计算所有绵羊到全局中心的距离
    furthest_sheep_index = np.argmax(distances)  # 找到距离全局中心最远的绵羊
    furthest_sheep_position = sheep_positions[furthest_sheep_index]  # 获取最远绵羊的位置
    direction_to_furthest_sheep = furthest_sheep_position - GCM  # 计算朝向最远绵羊的方向
    norm = np.linalg.norm(direction_to_furthest_sheep)  # 计算方向的模长
    if norm == 0:  # 如果模长为零
        direction = np.zeros(2)  # 方向设为零
    else:
        direction = direction_to_furthest_sheep / norm  # 标准化方向向量
    Pc = ec * direction + furthest_sheep_position  # 计算牧羊犬新的目标点
    direction_to_pc = Pc - GCM  # 计算牧羊犬到目标点的方向
    norm = np.linalg.norm(direction_to_pc)  # 计算方向的模长
    if norm == 0:  # 如果模长为零
        new_position = sheepdog_position  # 位置保持不变
    else:
        new_position = sheepdog_position + δs2 * direction_to_pc / norm  # 更新牧羊犬位置
    
    # 边界检查与反弹
    if new_position[0] < 0 or new_position[0] > L:
        new_position[0] = sheepdog_position[0] - δs2 * direction_to_pc[0] / norm  # 如果超出边界，反弹
    if new_position[1] < 0 or new_position[1] > L:
        new_position[1] = sheepdog_position[1] - δs2 * direction_to_pc[1] / norm  # 如果超出边界，反弹
    
    return new_position  # 返回更新后的牧羊犬位置
# 第二只牧羊犬调整羊群质心的位置
def adjust_sheep_center_with_second_dog(sheep_positions, target_point, sheepdog2_position):
    GCM = np.mean(sheep_positions, axis=0)  # 计算羊群的质心
    Pd = f_N * (GCM - target_point) / np.linalg.norm(GCM - target_point) + GCM  # 计算驱赶目标点
    direction = (Pd - sheepdog2_position) / np.linalg.norm(Pd - sheepdog2_position)  # 计算驱赶方向
    new_position = sheepdog2_position + δs2 * direction  # 更新牧羊犬位置
    return new_position
# 记录羊群质心轨迹的列表
sheep_center_trajectory = []

# 修改模拟函数，记录羊群中心轨迹
def simulate_shepherding(sheep_positions, previous_positions, sheepdog1_position, sheepdog2_position, Flag, max_steps=8000):
    positions = []
    sheepdog1_trajectory = [sheepdog1_position.copy()]
    sheepdog2_trajectory = [sheepdog2_position.copy()]
    initial_drive = True  # 初始驱赶标志
    index = 0
    recording_center_trajectory = False  # 是否开始记录羊群中心轨迹
    flag=False
    time_steps = []  # 用于存储每个时间步长

    for step in range(max_steps):
        start_time = time.time()  # 记录开始时间
        Flag+=1
        sheep_positions, previous_positions = update_sheep_positions(sheep_positions, previous_positions, sheepdog1_position, sheepdog2_position)
        
        GCM = np.mean(sheep_positions, axis=0)  # 计算羊群的质心
        if index >= len(target_points) - 2:
            break  # 完成所有目标点后停止
        else:
            target_point = target_points[0]
            sheepdog1_position, index, initial_drive,flag = drive_sheep(sheep_positions, sheepdog1_position, index, initial_drive,flag)
            
            # 如果羊群质心到达初始目标位置，开始记录羊群质心轨迹
            if not recording_center_trajectory and np.linalg.norm(GCM - target_point) < 10:
                recording_center_trajectory = True  # 开始记录质心轨迹
            
            if recording_center_trajectory and  flag:
                sheep_center_trajectory.append(GCM.copy())  # 记录质心坐标
            
            if initial_drive:
                if np.max(np.linalg.norm(sheep_positions - GCM, axis=1)) < f_N:  # 如果绵羊距离全局中心质量的最大距离小于f_N
                    sheepdog2_position = drive_sheep_initial(sheep_positions, sheepdog2_position)
                else:
                    sheepdog2_position = collect_sheep(sheep_positions, sheepdog2_position)
            else:
                if np.linalg.norm(abs(target_point - GCM)) < 10:  # 如果羊群质心在轨迹附近
                    sheepdog2_position = collect_sheep(sheep_positions, sheepdog2_position)  # 牧羊犬聚集绵羊
                else:  # 如果羊群质心偏离航线，需要让羊群回归正轨
                    next_target_point = target_points[index]
                    sheepdog2_position = adjust_sheep_center_with_second_dog(sheep_positions, next_target_point, sheepdog2_position)
        
        positions.append((sheep_positions.copy(), sheepdog1_position.copy(), sheepdog2_position.copy()))
        sheepdog1_trajectory.append(sheepdog1_position.copy())
        sheepdog2_trajectory.append(sheepdog2_position.copy())
        end_time = time.time()  # 记录结束时间
        time_step = end_time - start_time  # 计算时间步长
        time_steps.append(time_step)  # 将时间步长添加到列表

    return positions, previous_positions, sheepdog1_trajectory, sheepdog2_trajectory, sheep_center_trajectory,Flag

# 运行模拟
for i in range(1):
    Flag=0
    positions, previous_positions, sheepdog1_trajectory, sheepdog2_trajectory, sheep_center_trajectory ,Flag= simulate_shepherding(
    sheep_positions, previous_positions, sheepdog1_position, sheepdog2_position,Flag)
    print(f"时间步长：{Flag}")
    csv_file_path ='d:/Code/Python/sheep_center_new.csv'
    with open(csv_file_path,mode='w',newline='') as file:
        writer = csv.writer(file)
        writer.writerow(['x', 'y'])  # 写入表头
        for n in zip(sheep_center_trajectory):
            z=n[0]
            x=int(z[0])
            y=int(z[1])
            writer.writerow([x,y])
    # 确保文件有 'x' 和 'y' 列
    df = pd.read_csv(csv_file_path)
    if 'x' in df.columns and 'y' in df.columns:
        # 提取坐标
        x_coords = df['x'].to_numpy()
        y_coords = df['y'].to_numpy()

        # 计算相邻点之间的距离
        distances = np.sqrt(np.diff(x_coords)**2 + np.diff(y_coords)**2)

        # 计算总距离
        total_distance_sheep = np.sum(distances)
    print(f"羊群中心走过距离：{total_distance_sheep}")
    #将坐标导出到CSV文件中
    csv_file_path = 'd:/Code/Python/sheepdog1_new.csv'  # 保存的CSV文件路径
    with open(csv_file_path, mode='w', newline='') as file:
        writer = csv.writer(file)
        writer.writerow(['x', 'y'])  # 写入表头
        for n in zip(sheepdog1_trajectory):
            z=n[0]
            x=int(z[0])
            y=int(z[1])
            writer.writerow([x,y])
    # 读取CSV文件
    file_path2 = 'd:/Code/Python/sheepdog1_new.csv'
    df = pd.read_csv(file_path2)

    # 确保文件有 'x' 和 'y' 列
    if 'x' in df.columns and 'y' in df.columns:
        # 提取坐标
        x_coords = df['x'].to_numpy()
        y_coords = df['y'].to_numpy()

        # 计算相邻点之间的距离
        distances = np.sqrt(np.diff(x_coords)**2 + np.diff(y_coords)**2)

        # 计算总距离
        total_distance1 = np.sum(distances)
    
    #将坐标导出到CSV文件中
    csv_file_path = 'd:/Code/Python/sheepdog2_new.csv'  # 保存的CSV文件路径
    with open(csv_file_path, mode='w', newline='') as file:
        writer = csv.writer(file)
        writer.writerow(['x', 'y'])  # 写入表头
        for n in zip(sheepdog2_trajectory):
            z=n[0]
            x=int(z[0])
            y=int(z[1])
            writer.writerow([x,y])
    # 读取CSV文件
    file_path3 = 'd:/Code/Python/sheepdog2_new.csv'
    df = pd.read_csv(file_path3)

    # 确保文件有 'x' 和 'y' 列
    if 'x' in df.columns and 'y' in df.columns:
        # 提取坐标
        x_coords = df['x'].to_numpy()
        y_coords = df['y'].to_numpy()

        # 计算相邻点之间的距离
        distances = np.sqrt(np.diff(x_coords)**2 + np.diff(y_coords)**2)

        # 计算总距离
        total_distance2 = np.sum(distances)
    print(f"牧羊犬所走平均距离：{(total_distance1+total_distance2)/2}")
    total_row1 = sum(1 for row in open('route_coordinates.csv')) - 1  # 减去标题行
    total_row2= sum(1 for row in open('sheep_center_new.csv'))-1
    target_df = pd.read_csv('route_coordinates.csv')  
    x1 = target_df['x'].to_numpy()
    x1=np.array(x1)
    y1 = target_df['y'].to_numpy()
    y1=np.array(y1)
    target_df = pd.read_csv('sheep_center_new.csv')  
    x2 = target_df['x'].to_numpy()
    x2=np.array(x2)
    y2 = target_df['y'].to_numpy()
    y2=np.array(y2)
    len_c=min(total_row1,total_row2)
    sum_c=0.0
    for j in range(len_c):
        sum_c=sum_c+sqrt((x1[j]-x2[j])**2+(y1[j]-y2[j])**2)

    print(f"偏离度：{sum_c/len_c}")
    # 动画
    fig, ax = plt.subplots()
    ax.set_xlim(x_min - 500, x_max + 500)  
    ax.set_ylim(y_min - 500, y_max + 500)
    sheep_scatter = ax.scatter(sheep_positions[:, 0], sheep_positions[:, 1], color='blue', label='绵羊')
    sheepdog1_scatter = ax.scatter(sheepdog1_position[0], sheepdog1_position[1], color='red', label='牧羊犬1')
    sheepdog2_scatter = ax.scatter(sheepdog2_position[0], sheepdog2_position[1], color='green', label='牧羊犬2')

    # 绘制目标点的曲线
    target_path, = ax.plot(target_points[:, 0], target_points[:, 1], 'g--', label='目标路径')

    # 绘制羊群质心轨迹
    center_trajectory_line, = ax.plot([], [], 'orange', label='羊群质心轨迹')

    def update(frame):
        sheep_positions, sheepdog1_position, sheepdog2_position = positions[frame]
        sheep_scatter.set_offsets(sheep_positions)
        sheepdog1_scatter.set_offsets(sheepdog1_position)
        sheepdog2_scatter.set_offsets(sheepdog2_position)

        # 更新质心轨迹
        if len(sheep_center_trajectory) > frame:
            center_trajectory_line.set_data(
                [point[0] for point in sheep_center_trajectory[:frame]],
                [point[1] for point in sheep_center_trajectory[:frame]]
            )

        return sheep_scatter, sheepdog1_scatter, sheepdog2_scatter, center_trajectory_line

    ani = animation.FuncAnimation(fig, update, frames=len(positions), interval=50, blit=True)
    plt.legend(prop=zhfont1)
    plt.show()



