import os
import subprocess


def run_benchmark_script(base_path):
    # # 将传入的基础路径转换为绝对路径
    # base_path = os.path.abspath(base_path)

    # 遍历所有文件夹
    for root, dirs, files in os.walk(base_path, topdown=True):
        # 过滤掉那些包含子目录的目录
        if not dirs:
            # 构建相对路径
            relative_path = os.path.relpath(root, start=base_path)
            # 目标目录
            target_dir = f"samples/{base_path}/{relative_path}"
            # 确保目标目录存在
            os.makedirs(target_dir, exist_ok=True)

            # 构建命令
            command = f"my_scripts/run_benchmarks.sh 1000 {base_path}/{relative_path} {target_dir}"

            # 执行命令
            print(f"Executing command: {command}")  # 打印将要执行的命令
            subprocess.run(command, shell=True)

            # 等待当前命令执行完成后再继续下一个文件夹
            print(f"Finished processing: {relative_path}")


if __name__ == "__main__":
    # 定义要遍历的基础路径（这里假设是相对于当前脚本工作目录的相对路径）
    base_directory = "LIA_bench"
    # 调用函数
    run_benchmark_script(base_directory)
