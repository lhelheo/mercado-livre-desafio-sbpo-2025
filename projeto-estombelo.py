from csp import backtracking_search
from csp import CSP

import itertools

# Dados do exemplo
pedidos = {
    0: [2, 0, 1],
    1: [1, 1, 0],
    2: [0, 2, 1],
    3: [1, 0, 2]
}
corredores = {
    0: [2, 1, 1],
    1: [1, 2, 1],
    2: [1, 1, 2]
}
LB = 3
UB = 6


# Descobre dinamicamente o número de itens
num_itens = len(next(iter(pedidos.values())))

# Variáveis: subconjunto de pedidos (wave)
# Domínio: todas combinações possíveis de pedidos (subconjuntos)
pedido_ids = list(pedidos.keys())
dominio_pedidos = []
for r in range(1, len(pedido_ids)+1):
    for subset in itertools.combinations(pedido_ids, r):
        # Calcula total de itens
        total = sum(sum(pedidos[p][i] for i in range(num_itens)) for p in subset)
        if LB <= total <= UB:
            dominio_pedidos.append(subset)

# Variáveis do CSP: só uma, a wave
variables = ['wave']
domains = {'wave': dominio_pedidos}
neighbors = {'wave': []}

def wave_constraint(A, a, B, b):
    # Só uma variável, sempre retorna True
    return True


csp = CSP(variables, domains, neighbors, wave_constraint)

def objetivo(wave):
    # Para um subconjunto de pedidos, encontra o menor conjunto de corredores que atende todos os itens
    pedidos_selecionados = wave
    itens_necessarios = [0]*num_itens
    for p in pedidos_selecionados:
        for i in range(num_itens):
            itens_necessarios[i] += pedidos[p][i]
    # Busca subconjuntos de corredores que suprem todos os itens
    melhor_valor = 0
    melhor_corredores = None
    for r in range(1, len(corredores)+1):
        for subset in itertools.combinations(corredores.keys(), r):
            atende = True
            for i in range(num_itens):
                total_disp = sum(corredores[c][i] for c in subset)
                if itens_necessarios[i] > total_disp:
                    atende = False
                    break
            if atende:
                valor = sum(itens_necessarios) / len(subset)
                if valor > melhor_valor:
                    melhor_valor = valor
                    melhor_corredores = subset
    return melhor_valor, melhor_corredores


# Busca a wave ótima testando todas as waves viáveis
melhor_valor = 0
melhor_wave = None
melhor_corredores = None
for wave in dominio_pedidos:
    valor, corredores_usados = objetivo(wave)
    if valor > melhor_valor:
        melhor_valor = valor
        melhor_wave = wave
        melhor_corredores = corredores_usados

if melhor_wave:
    print(f"Wave otima: pedidos {melhor_wave}")
    print(f"Corredores usados: {melhor_corredores}")
    print(f"Valor objetivo: {melhor_valor}")
else:
    print("Nenhuma solução viável encontrada.")