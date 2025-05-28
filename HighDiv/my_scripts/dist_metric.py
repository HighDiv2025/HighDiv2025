import numpy as np


# 读取文件并将每一行转换为向量
def read_vectors_from_file(filename):
    vectors = []
    with open(filename, "r") as file:
        for line in file:
            # 去掉行号部分，去除行号和开头的空白，剩余部分是 var:val 数据
            line = line.strip().split(":", 1)[-1]  # 忽略行号部分

            # 用 ';' 分割每个 var:val 对
            values = line.split(";")
            vector = []
            for val in values:
                val = val.strip()  # 去掉可能的前后空白
                # print(val)
                if val:  # 如果值不为空
                    parts = val.split(":")
                    if len(parts) == 2:  # 确保分割后的部分有两个元素
                        try:
                            # 将值转换为浮动数值并添加到向量
                            vector.append(float(parts[1]))
                        except ValueError:
                            print(
                                f"Warning: Value '{val}' cannot be converted to float."
                            )
                    else:
                        print(f"Warning: Skipping malformed value '{val}'.")
                # else:
                #     print(f"Warning: Skipping empty value.")

            if vector:  # 只有在成功解析了向量的情况下，才将其添加到 vectors 列表
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
filename = "/mnt/f/MeGA/samples/mega/time_limit_900/QF_LIA/20180326-Bromberger/more_slacked/CAV_2009_benchmarks/smt/35-vars/v35_problem__004.smt2.slack.smt2.samples"

# 读取文件中的向量
vectors = read_vectors_from_file(filename)

# 计算平均距离
mean_dist = calculate_mean_distance(vectors)
print(f"平均距离: {mean_dist}")
