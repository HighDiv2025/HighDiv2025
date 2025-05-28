import pandas as pd

def convert_percentages_to_decimal(file_path, output_path):
    # 读取Excel文件，跳过表头
    df = pd.read_excel(file_path, skiprows=[0])
    
    # 假设后两列是我们需要的百分数列，提取它们
    percent_columns = df.iloc[:, -2:]
    
    # 准备存储转换后的数据
    decimals = []
    
    # 尝试将百分数转换为小数
    for index, row in percent_columns.iterrows():
        try:
            # 检查是否包含非预期的错误日志或其他非数字字符
            if any(isinstance(item, str) and 'Traceback' in item for item in row):
                print(f"跳过错误日志所在行 {index + 1}")
                continue  # 跳过这行
            
            decimal_values = [float(value.strip('%')) / 100 for value in row]
            decimals.append(decimal_values)
        except ValueError as e:
            print(f"转换错误在行 {index + 1}: {row.tolist()} - {str(e)}")

    # 写入到txt文件，格式化为每行两个小数，用空格分隔
    with open(output_path, 'w') as f:
        for decimal_values in decimals:
            if len(decimal_values) == 2:
                f.write(f"{decimal_values[0]} {decimal_values[1]}\n")
            else:
                f.write("数据错误\n")

# 使用示例
file_path = 'excel_file/merge_megab_ls_res.xlsx'  # Excel文件的路径
output_path = 'ls_vs_megab.txt'  # 输出的txt文件路径

convert_percentages_to_decimal(file_path, output_path)
