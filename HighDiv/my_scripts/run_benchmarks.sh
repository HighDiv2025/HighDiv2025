#!/bin/bash

# 检查参数数量
if [ "$#" -ne 3 ]; then
  echo "Usage: $0 <n_samples> <input_directory> <output_directory>"
  exit 1
fi

# 从命令行参数获取样本数、输入文件夹和输出文件夹
n_samples="$1"
input_directory="$2"
output_directory="$3"
log_subfolder="$output_directory/logs"  # 定义日志文件的子文件夹

# 创建输出文件夹和日志子文件夹，如果不存在的话
mkdir -p "$output_directory"
mkdir -p "$log_subfolder"

# 使用 GNU parallel 来并行执行命令，并将标准输出和错误输出重定向到日志文件 
find "$input_directory" -name '*.smt2' -type f | parallel -j 15 --bar \
  timeout --kill-after=30 3605 "./highdiv  -t 3600 -n $n_samples -o $output_directory -s 0 -m hybrid -i -m 2ls {} > $log_subfolder/\$(basename {} .smt2).log 2>&1"

echo "All processes have completed."
