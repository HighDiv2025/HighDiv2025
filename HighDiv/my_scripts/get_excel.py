import os
import pandas as pd

def extract_percentage(filepath):
    """从文件中读取百分数"""
    with open(filepath, 'r') as file:
        content = file.read().strip()
    return content

def scan_directory(directory):
    """扫描目录并提取所有文件的百分数，并记录其上层文件夹名"""
    data = []
    for root, dirs, files in os.walk(directory):
        for filename in files:
            if filename.endswith(".out"):  # 假设文件是文本文件，你可以根据需要更改
                filepath = os.path.join(root, filename)
                percentage = extract_percentage(filepath)
                filename_without_ext = os.path.splitext(filename)[0]
                parent_folder = os.path.basename(root)  # 获取上级目录的名字
                data.append([parent_folder + '/' + filename_without_ext, percentage])
    return data

def save_to_csv(data, output_file):
    """将数据保存到CSV文件"""
    df = pd.DataFrame(data, columns=['Filename', 'Percentage'])
    df.to_csv(output_file, index=False, encoding='utf-8')  # 保存为CSV

# 使用示例
directory = 'calc_res/QF_LIA/QF_LIA_time900'  # 替换为你的文件夹路径
output_file = 'csv_dir/HighDiv_time900.csv'  # 输出CSV文件名
data = scan_directory(directory)
save_to_csv(data, output_file)
