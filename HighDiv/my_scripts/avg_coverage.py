import os
import re

def find_percentage_in_file(filepath):
    with open(filepath, 'r') as file:
        content = file.read()
    percentages = re.findall(r'(\d+\.\d+)%', content)
    percentages = [float(p) for p in percentages]
    return percentages

def process_folder(directory):
    total_percent = 0
    count = 0
    for root, dirs, files in os.walk(directory):
        if files:  # 检查当前目录下是否有文件
            current_folder_total = 0
            current_folder_count = 0
            for file in files:
                if file.endswith('.out'):
                    file_path = os.path.join(root, file)
                    percentages = find_percentage_in_file(file_path)
                    if percentages:
                        current_folder_total += sum(percentages)
                        current_folder_count += len(percentages)
            if current_folder_count > 0:
                # 计算当前文件夹的平均百分比
                current_folder_avg = current_folder_total / current_folder_count
                total_percent += current_folder_total
                count += current_folder_count
                # 将结果写入文件
                result_file_path = os.path.join(root, 'average_percentage.txt')
                with open(result_file_path, 'w') as result_file:
                    result_file.write(f'Average Percentage: {current_folder_avg:.2f}%\n')
    if count > 0:
        return total_percent / count
    else:
        return None

if __name__ == "__main__":
    directory = input("Enter the directory path to process: ")
    average = process_folder(directory)
    if average is not None:
        print(f"Overall average percentage: {average:.2f}%")
    else:
        print("No percentage values found in any .out files.")
