#!/bin/bash

# 定义要操作的目录
BUILD_DIR="../z3/build/"

# 执行卸载操作
make -C $BUILD_DIR uninstall
if [ $? -ne 0 ]; then
  echo "Uninstall failed"
  exit 1
fi

# 使用 23 个并行任务进行编译
make -C $BUILD_DIR -j 12
if [ $? -ne 0 ]; then
  echo "Build failed"
  exit 1
fi

# 执行安装操作
make -C $BUILD_DIR -j 12 install
if [ $? -ne 0 ]; then
  echo "Install failed"
  exit 1
fi

cp "$BUILD_DIR/z3" ./z3pp
echo "copy z3 to this dir"

echo "All steps completed successfully"
