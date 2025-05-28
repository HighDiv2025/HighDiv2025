import numpy as np


# 读取文件并将每一行转换为向量
def read_vectors_from_file(filename):
    vectors = []
    with open(filename, "r") as file:
        for line in file:
            # 忽略行号部分，去除行号后解析每行的 `var:val` 数据
            values = line.strip().split(":", 1)[-1].split(",")  # 去掉行号部分
            vector = [float(val.split(":")[1]) for val in values]
            vectors.append(vector)
    return np.array(vectors)


# 计算多个向量之间的平均距离
def calculate_mean_distance(vectors):
    n = len(vectors)  # 向量的个数
    total_distance = 0  # 距离总和
    count = 0  # 计算总的向量对数量

    # 遍历所有的向量对，计算它们的距离
    for i in range(n):
        for j in range(i + 1, n):  # 确保每对向量只计算一次
            # 计算欧氏距离
            distance = np.linalg.norm(vectors[i] - vectors[j])
            total_distance += distance
            count += 1

    # 计算平均距离
    mean_distance = total_distance / count if count != 0 else 0
    return mean_distance


# 文件路径
filename = "vectors.txt"

# 读取文件中的向量
vectors = read_vectors_from_file(filename)

# 计算平均距离
mean_dist = calculate_mean_distance(vectors)
print(f"平均距离: {mean_dist}")
