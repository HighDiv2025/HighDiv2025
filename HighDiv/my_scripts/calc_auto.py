import os
import subprocess


def find_leaf_directories(root_dir):
    leaf_dirs = []
    for current_dir, dirs, files in os.walk(root_dir):
        # 如果当前目录下没有子目录，则认为是叶子目录
        if not dirs:
            leaf_dirs.append(current_dir)
    return leaf_dirs


def execute_command_on_leaf_dirs(root_dir):
    leaf_dirs = find_leaf_directories(root_dir)
    for leaf_dir in leaf_dirs:
        # 计算相对路径，从当前工作目录到叶子目录
        relative_path = os.path.relpath(leaf_dir, os.getcwd())
        # 构建命令
        command = f"my_scripts/calc_metric_parallel.sh {relative_path}"
        print(f"Executing command: {command}")
        # 执行命令
        subprocess.run(command, shell=True)


if __name__ == "__main__":
    root_directory = "QF_LIA"  # 请将此处替换为您的根目录路径
    execute_command_on_leaf_dirs(root_directory)
