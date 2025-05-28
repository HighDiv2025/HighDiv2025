import pandas as pd

def merge_excel_files(file1, file2, output_file):
    # 读取两个 Excel 文件
    df1 = pd.read_excel(file1, usecols=[0, 1], header=None)
    df2 = pd.read_excel(file2, usecols=[0, 1], header=None)
    
    # 为了处理没有列名的情况，我们手动指定列名
    df1.columns = ['Filename', 'Percentage']
    df2.columns = ['Filename', 'Percentage']
    
    # 使用 merge 函数合并两个 DataFrame，基于"Filename"列进行内部合并
    merged_df = pd.merge(df1, df2, on='Filename', suffixes=('_1', '_2'))
    
    # 将合并后的 DataFrame 保存到新的 Excel 文件
    merged_df.to_excel(output_file, index=False)

# 设置文件路径
file1 = 'excel_file/megab_res.xlsx'
file2 = 'excel_file/ls_res.xlsx'
output_file = 'merge_megab_ls_res.xlsx'

# 调用函数执行合并
merge_excel_files(file1, file2, output_file)
