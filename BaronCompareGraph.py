import pandas as pd
import matplotlib.pyplot as plt
import math

df_back = pd.read_csv('baronDeterBackResult.csv')
df_smt = pd.read_csv('z3_baronresults.csv')

df_back.rename(columns={
    'height': 'Height',
    'width': 'Width',
    'boardnum': 'Boardnum',
    'time_s': 'StrategiesTime'
}, inplace=True)

df_smt.rename(columns={
    'TimeSeconds': 'SMTTime'
}, inplace=True)

merged = pd.merge(df_back, df_smt, on=['Height', 'Width', 'Boardnum'])

merged['BoardSize'] = merged['Height'].astype(str) + 'x' + merged['Width'].astype(str)

merged.sort_values(by=['Height', 'Width', 'Boardnum'], inplace=True)
board_sizes = sorted(merged['BoardSize'].unique(), key=lambda x: (int(x.split('x')[0]), int(x.split('x')[1])))


graphs_per_file = 2
num_files = math.ceil(len(board_sizes) / graphs_per_file)

for file_idx in range(num_files):
    fig, axes = plt.subplots(1, graphs_per_file, figsize=(12, 5), sharex=False, sharey=False)
    axes = axes.flatten()
    
    for i in range(graphs_per_file):
        board_idx = file_idx * graphs_per_file + i
        if board_idx >= len(board_sizes):
            fig.delaxes(axes[i])
            continue
        
        board_size = board_sizes[board_idx]
        ax = axes[i]
        data = merged[merged['BoardSize'] == board_size]

        ax.plot(data['Boardnum'], data['StrategiesTime'], marker='o', label='Strategies (incl. backtracking)')
        ax.plot(data['Boardnum'], data['SMTTime'], marker='x', label='SMT')

        ax.set_title(f'{board_size}')
        ax.set_xlabel('Board Number')
        ax.set_ylabel('Time (s)')
        ax.grid(True)
        ax.legend()
        ax.set_xticks(data['Boardnum'])
    
    fig.suptitle('SMT vs Solving Strategies - Standard Variant', fontsize=16)
    plt.tight_layout(rect=[0, 0, 1, 0.95])
    
    fig.savefig(f'smt_vs_strategies_part{file_idx + 1}.png')
    plt.close(fig)
