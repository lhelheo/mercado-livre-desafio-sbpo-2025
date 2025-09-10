from csp import backtracking_search, CSP, mrv, lcv
import itertools

# --- Definição dos Dados do Problema ---

# Dicionário de pedidos. A chave é o ID do pedido.
# O valor é uma lista onde o índice representa o tipo do item e o valor é a quantidade.

pedidos = {
    0: [3, 0, 1, 0, 0],
    1: [0, 1, 0, 1, 0],
    2: [0, 0, 1, 0, 2],
    3: [1, 0, 2, 1, 1],
    4: [0, 1, 0, 0, 0],
}

# Dicionário de corredores. A chave é o ID do corredor.
# O valor é uma lista com a quantidade de cada tipo de item disponível no corredor.
corredores = {
    0: [2, 2, 1, 0, 1],  # Corredor 0: 2 do tipo 0, 2 do tipo 1, 1 do tipo 2, 0 do tipo 3, 1 do tipo 4
    1: [2, 1, 2, 0, 1],  # Corredor 1: 2 do tipo 0, 1 do tipo 1, 2 do tipo 2, 0 do tipo 3, 1 do tipo 4
    2: [0, 2, 0, 1, 2],  # Corredor 2: 0 do tipo 0, 2 do tipo 1, 0 do tipo 2, 1 do tipo 3, 2 do tipo 4
    3: [2, 1, 0, 1, 1],  # Corredor 3: 2 do tipo 0, 1 do tipo 1, 0 do tipo 2, 1 do tipo 3, 1 do tipo 4
    4: [0, 1, 2, 1, 2],  # Corredor 4: 0 do tipo 0, 1 do tipo 1, 2 do tipo 2, 1 do tipo 3, 2 do tipo 4
}

# Limite inferior (Lower Bound) e superior (Upper Bound) para o número total de itens na wave.
LB = 5
UB = 12

# Determina o número de tipos de item com base no primeiro pedido.
num_itens = len(next(iter(pedidos.values())))

# --- Configuração do CSP ---

# As variáveis do problema são os próprios pedidos.
variables = list(pedidos.keys())

# O domínio de cada variável é binário: 1 se o pedido está na wave, 0 se não está.
domains = {v: [0, 1] for v in variables}

def get_total_itens(assignment):
    """Calcula o número total de itens em todos os pedidos selecionados para a wave."""
    total = 0
    pedidos_selecionados = [p for p in assignment if assignment.get(p, 0) == 1]
    if not pedidos_selecionados:
        return 0
    # Soma a quantidade de todos os itens em todos os pedidos selecionados.
    total = sum(sum(pedidos[p][i] for i in range(num_itens)) for p in pedidos_selecionados)
    return total

def get_necessidades_itens(pedidos_selecionados):
    """Calcula a necessidade total para cada tipo de item com base nos pedidos selecionados."""
    itens_necessarios = [0] * num_itens
    for p in pedidos_selecionados:
        for i in range(num_itens):
            itens_necessarios[i] += pedidos[p][i]
    return itens_necessarios

def encontra_melhores_corredores(pedidos_selecionados):
    """
    Encontra a combinação de corredores que atende aos itens necessários com a melhor
    métrica de eficiência (total de itens / número de corredores).
    Retorna o melhor valor e a combinação de corredores.
    """
    if not pedidos_selecionados:
        return 0, None

    itens_necessarios = get_necessidades_itens(pedidos_selecionados)
    melhor_valor = -1
    melhor_corredores = None

    # Itera sobre todas as combinações possíveis de corredores (de 1 até o total de corredores).
    for r in range(1, len(corredores) + 1):
        for subset in itertools.combinations(corredores.keys(), r):
            atende = True
            # Verifica se a combinação de corredores atual atende à necessidade de todos os itens.
            for i in range(num_itens):
                total_disp = sum(corredores[c][i] for c in subset)
                if itens_necessarios[i] > total_disp:
                    atende = False
                    break
            # Se atende, calcula o valor (eficiência) e atualiza se for o melhor até agora.
            if atende:
                valor = sum(itens_necessarios) / len(subset)
                if valor > melhor_valor:
                    melhor_valor = valor
                    melhor_corredores = subset
    return melhor_valor, melhor_corredores

class CSPComRestricaoGlobalCorrigido(CSP):
    """
    Classe CSP personalizada para o problema de formação de waves.
    Herda da classe CSP base e implementa as restrições globais do problema.
    """
    def __init__(self, variables, domains, neighbors, pedidos, corredores, LB, UB):
        super().__init__(variables, domains, neighbors, None)
        self.pedidos = pedidos
        self.corredores = corredores
        self.LB = LB
        self.UB = UB
        self.num_itens = len(next(iter(pedidos.values())))

    def nconflicts(self, var, val, assignment):
        """Calcula o número de conflitos para uma atribuição parcial. Usado pelo solver de backtracking."""
        temp_assignment = assignment.copy()
        temp_assignment[var] = val

        pedidos_selecionados = [p for p in temp_assignment if temp_assignment.get(p) == 1]

        # Restrição 1 (Poda): Se o total de itens já excede o limite superior, é um conflito.
        # Isso permite podar ramos da árvore de busca antecipadamente.
        total = get_total_itens(temp_assignment)
        if total > self.UB:
            return 1  # Conflito de UB

        # Se todas as variáveis foram atribuídas, verifica as restrições finais.
        if len(temp_assignment) == len(self.variables):
            # Restrição 2: O total de itens deve ser maior ou igual ao limite inferior.
            if total < self.LB:
                return 1

            # Restrição 3: Deve existir uma combinação de corredores que atenda aos pedidos.
            melhor_valor, melhor_corredores = encontra_melhores_corredores(pedidos_selecionados)
            if melhor_corredores is None:
                return 1 # Conflito de corredores

        return 0  # Sem conflitos

    def goal_test(self, state):
        """Verifica se uma atribuição completa (estado final) é uma solucao válida."""
        assignment = dict(state)

        # 1. Garante que a atribuição está completa.
        if not set(assignment.keys()) == set(self.variables):
            return False

        # 2. Verifica a restrição de total de itens (LB e UB).
        total = get_total_itens(assignment)
        if not (self.LB <= total <= self.UB):
            return False

        # 3. Verifica a restrição de disponibilidade nos corredores.
        pedidos_selecionados = [p for p in assignment if assignment.get(p) == 1]
        _, corredores_usados = encontra_melhores_corredores(pedidos_selecionados)
        return corredores_usados is not None

# --- Execução e Saída ---

# Instancia o problema CSP.
# Como as restrições são globais e não entre pares de variáveis, a vizinhança é vazia.
csp = CSPComRestricaoGlobalCorrigido(variables, domains, {}, pedidos, corredores, LB, UB)

def gerar_todas_atribuicoes(variables, domains):
    """Gera todas as atribuições possíveis para as variáveis do CSP."""
    dom_lists = [domains[v] for v in variables]
    for values in itertools.product(*dom_lists):
        yield dict(zip(variables, values))

solucao = backtracking_search(csp, select_unassigned_variable=mrv, order_domain_values=lcv)

# Agora, busca todas as atribuições possíveis e filtra as viáveis
solucoes_viaveis = []
for atrib in gerar_todas_atribuicoes(variables, domains):
    if csp.goal_test(atrib):
        pedidos_selecionados = [p for p in pedidos if atrib.get(p, 0) == 1]
        valor, corredores_usados = encontra_melhores_corredores(pedidos_selecionados)
        if corredores_usados:
            solucoes_viaveis.append({
                "atrib": atrib,
                "pedidos": pedidos_selecionados,
                "corredores": corredores_usados,
                "valor": valor
            })

if solucoes_viaveis:
    solucoes_viaveis.sort(key=lambda x: x["valor"], reverse=True)
    melhor_valor = solucoes_viaveis[0]["valor"]
    print("Solucoes viaveis encontradas pelo CSP:")
    for idx, res in enumerate(solucoes_viaveis):
        destaque = " <--- MELHOR SOLUCAO" if res["valor"] == melhor_valor else ""
        print(f"\nSolucao {idx+1}:")
        print(f"Wave: pedidos {res['pedidos']}")
        print(f"Corredores usados: {res['corredores']}")
        print(f"Valor objetivo (eficiencia): {res['valor']:.2f}{destaque}")
else:
    print("Nenhuma solucao viavel para a wave encontrada pelo CSP.")