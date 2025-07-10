import pandas as pd
import matplotlib.pyplot as plt
import math

df_back = pd.read_csv('baronDeterBackResult.csv')
df_smt = pd.read_csv('z3_baronresults.csv')

df_back.rename(columns={
    'height': 'Height',
    'width': 'Width',
    'boardnum': 'Boardnum',
    'time_s': 'BacktrackingTime'
}, inplace=True)

df_smt.rename(columns={
    'TimeSeconds': 'SMTTime'
}, inplace=True)

merged = pd.merge(df_back, df_smt, on=['Height', 'Width', 'Boardnum'])

merged['BoardSize'] = merged['Height'].astype(str) + 'x' + merged['Width'].astype(str)

merged.sort_values(by=['Height', 'Width', 'Boardnum'], inplace=True)
board_sizes = sorted(merged['BoardSize'].unique(), key=lambda x: (int(x.split('x')[0]), int(x.split('x')[1])))

num_plots = len(board_sizes)
cols = 3
rows = math.ceil(num_plots / cols)

fig, axes = plt.subplots(rows, cols, figsize=(16, 10), sharex=False, sharey=False)
axes = axes.flatten()

for i, board_size in enumerate(board_sizes):
    ax = axes[i]
    data = merged[merged['BoardSize'] == board_size]

    ax.plot(data['Boardnum'], data['BacktrackingTime'], marker='o', label='Backtracking')
    ax.plot(data['Boardnum'], data['SMTTime'], marker='x', label='SMT')

    ax.set_title(f'{board_size}')
    ax.set_xlabel('Board Number')
    ax.set_ylabel('Time (s)')
    ax.grid(True)
    ax.legend()

    ax.set_xticks(data['Boardnum'])

for j in range(i + 1, len(axes)):
    fig.delaxes(axes[j])

fig.suptitle('SMT vs Solving Strategies - Standard Variant', fontsize=16)
plt.tight_layout(rect=[0, 0, 1, 0.97])
plt.show()
