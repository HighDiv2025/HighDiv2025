import os

def remove_last_line_from_file(file_path):
    # 打开文件并读取所有行
    with open(file_path, 'r') as file:
        lines = file.readlines()
    
    # 如果文件有内容，删除最后一行
    if lines:
        with open(file_path, 'w') as file:
            file.writelines(lines[:-1])

def traverse_and_remove_last_line(root_dir):
    # 遍历指定目录下的所有文件和文件夹
    for root, dirs, files in os.walk(root_dir):
        for file in files:
            # 检查文件扩展名是否为 .samples
            if file.endswith('.samples'):
                file_path = os.path.join(root, file)
                print(f"处理文件: {file_path}")
                remove_last_line_from_file(file_path)

if __name__ == "__main__":
    # 输入要处理的文件夹路径
    directory_path = input("请输入文件夹路径: ")
    traverse_and_remove_last_line(directory_path)
    print("处理完成！")