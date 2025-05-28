#!/bin/bash

SAMPLE_FILE="$1"
SMT_DIR="$2"
PYTHON_SCRIPT="$3"
MODE="$4"
OUTPUT_DIR="$5"

BASE_NAME=$(basename "$SAMPLE_FILE" .samples)
SMT_FILE="$SMT_DIR/$BASE_NAME"
OUTPUT_FILE="$OUTPUT_DIR/$BASE_NAME.out"

echo "Processing sample file: $SAMPLE_FILE"
echo "Corresponding SMT file: $SMT_FILE"
echo "Output will be saved to: $OUTPUT_FILE"

if [ -f "$SMT_FILE" ]; then
    python3 "$PYTHON_SCRIPT" -s "$SAMPLE_FILE" -f "$SMT_FILE" -m "$MODE" > "$OUTPUT_FILE" 2>&1
    if [ $? -ne 0 ]; then
        echo "运行 Python 脚本时出错：$PYTHON_SCRIPT" >> "$OUTPUT_FILE"
    fi
else
    echo "对应的 .smt2 文件不存在：$SMT_FILE" > "$OUTPUT_FILE"
fi
