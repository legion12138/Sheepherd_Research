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
image_path = 'd:/Code/Python/assets/route.jpg'  # 图片路径
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
csv_file_path = 'd:/Code/Python/route_coordinates3.csv'  # 保存的CSV文件路径
with open(csv_file_path, mode='w', newline='') as file:
    writer = csv.writer(file)
    writer.writerow(['x', 'y'])  # 写入表头
    for x, y in zip(x_coords, y_coords):
        writer.writerow([x, y])