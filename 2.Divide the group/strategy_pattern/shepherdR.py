import numpy as np
from numpy import linalg as la
from sklearn.cluster import KMeans
from sklearn.cluster import DBSCAN
from sklearn.cluster import OPTICS
import math

class Shepherd:
    def __init__(self, b):
        self.behavior = b
    
    #调整牧羊犬至指定位置
    def driving(self, herd, max,min, speed, app_dist):
        speeds = speed * 1.0
        herd_point = herd.position2point()
        temp=min-max
        gt_dist = np.array([-temp[1], temp[0]])
        Pd = (gt_dist/np.linalg.norm(gt_dist)) * app_dist + max
        rd = (Pd - herd_point) / np.linalg.norm(Pd - herd_point) * speeds

        herd.x = rd[0]
        herd.y = rd[1]
        herd.draw()

    #冲散羊群
    def open(self, herd,g_mean, speed,app_dist):
        speeds = speed * 1.0
        herd_point = herd.position2point()
    
        gt_dist = -herd_point+g_mean
        # 角度转换为弧度
        theta = np.deg2rad(60)  # 将5度转换为弧度

        # 定义2D旋转矩阵
        rotation_matrix = np.array([
            [np.cos(theta), -np.sin(theta)],
            [np.sin(theta), np.cos(theta)]
        ])

        # 旋转gt_dist向量
        rotated_gt_dist = np.dot(rotation_matrix, gt_dist)

        Pd = rotated_gt_dist / np.linalg.norm(rotated_gt_dist) * app_dist + g_mean
        rd = (Pd - herd_point) / np.linalg.norm(Pd - herd_point) * speeds

        herd.x = rd[0]
        herd.y = rd[1]
        herd.draw()
    '''
    #最原始驱赶
    def open(self, herd,all_sheep, speed,app_dist):
        speeds = speed * 1.0
        herd_point = herd.position2point()
        g_mean = np.array([np.mean(all_sheep[:, 0]), np.mean(all_sheep[:, 1])])
    
        gt_dist = -herd_point+g_mean
        # 角度转换为弧度
        theta = np.deg2rad(60)  # 将5度转换为弧度

        # 定义2D旋转矩阵
        rotation_matrix = np.array([
            [np.cos(theta), -np.sin(theta)],
            [np.sin(theta), np.cos(theta)]
        ])

        # 旋转gt_dist向量
        rotated_gt_dist = np.dot(rotation_matrix, gt_dist)

        Pd = rotated_gt_dist / np.linalg.norm(rotated_gt_dist) * app_dist + g_mean
        rd = (Pd - herd_point) / np.linalg.norm(Pd - herd_point) * speeds

        herd.x = rd[0]
        herd.y = rd[1]
        herd.draw()
    '''
    '''
    def k_means(self,all_sheep, num):
        n_clusters=num
        # 初始化KMeans，设置聚类的数量和随机种子
        kmeans = KMeans(n_clusters=n_clusters, random_state=0)
    
        # 将羊群的坐标传入KMeans进行聚类
        kmeans.fit(all_sheep)
    
        # 获取聚类的中心点坐标
        cluster_centers = kmeans.cluster_centers_
    
        # 获取每个羊所属的聚类标签
        labels = kmeans.labels_
    
        # 创建一个字典存储每个聚类中心附近的羊的坐标
        sheep_near_centers = {i: [] for i in range(n_clusters)}
    
        # 将每只羊根据其所属聚类存入对应的数组
        for i, sheep in enumerate(all_sheep):
            cluster_label = labels[i]  # 获取该羊所属的聚类标签
            sheep_near_centers[cluster_label].append(sheep)  # 将羊的坐标加入对应聚类的数组
    
        # 将字典中每个聚类的羊群坐标转换为数组格式
        for cluster in sheep_near_centers:
            sheep_near_centers[cluster] = np.array(sheep_near_centers[cluster])
    
        # 返回聚类中心坐标和每个聚类中的羊群坐标
        return cluster_centers, sheep_near_centers
    '''
    #计算羊群聚类中心坐标点
    def optics_clustering(self, all_sheep, min_samples):
        # 初始化OPTICS算法，设置最小样本数
        optics = OPTICS(min_samples=min_samples)
    
        # 使用OPTICS对羊群的坐标进行聚类
        optics.fit(all_sheep)
    
        # 获取每只羊所属的聚类标签，-1表示噪声点（不属于任何聚类）
        labels = optics.labels_
    
        # 获取不同簇的标签数，排除噪声点（标签为-1的点）
        unique_labels = set(labels) - {-1}
    
        # 创建一个字典存储每个聚类中心附近的羊的坐标
        sheep_near_centers = {label: [] for label in unique_labels}
    
        # 将每只羊根据其所属聚类存入对应的数组
        for i, sheep in enumerate(all_sheep):
            cluster_label = labels[i]  # 获取该羊所属的聚类标签
            if cluster_label != -1:  # 排除噪声点
                sheep_near_centers[cluster_label].append(sheep)  # 将羊的坐标加入对应聚类的数组
    
        # 将字典中每个聚类的羊群坐标转换为数组格式
        for cluster in sheep_near_centers:
            sheep_near_centers[cluster] = np.array(sheep_near_centers[cluster])
    
        # 找到包含羊群最多的聚类
        max_sheep_cluster = max(sheep_near_centers, key=lambda x: len(sheep_near_centers[x]))
        min_sheep_cluster = min(sheep_near_centers, key=lambda x: len(sheep_near_centers[x]))
        # 获取该聚类的中心点，中心点可以定义为羊群坐标的平均值
        max_cluster_center = np.mean(sheep_near_centers[max_sheep_cluster], axis=0)
        min_cluster_center = np.mean(sheep_near_centers[min_sheep_cluster],axis=0)
        # 返回最多羊群聚类的中心坐标和羊群的坐标
        return max_cluster_center, min_cluster_center,sheep_near_centers[max_sheep_cluster]

    def switch(self, all_sheep, target, fn, theta):
        return self.behavior.check(all_sheep, target, fn, theta)