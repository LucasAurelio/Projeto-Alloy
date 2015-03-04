open util/ordering [Time]

module EmprestimoDeLivros

//FALTA:
//- definir que quando uma operação estiver sendo executada as outras não podem 
//(para have um controle do que está acontecendo)
//
//
//

// ---- ASSINATURAS ---- //

sig Time{}

one sig Universidade{
	blocos: set Bloco
}

sig Bloco{
	organizador: one Organizador,
	alunosCadastrados: Aluno -> Time,
	livrosDisponiveis: Livro some -> Time,
	livrosEmprestados: Livro -> Time,
	livrosReservados: Livro -> Time
}

one sig CAA, CD, CN extends Bloco{}

sig Aluno{
	nomeAluno: Nome,
	matriculaAluno: Matricula,
	livrosEmprestadosComAluno: Livro set -> Time,
	livrosReservadosPeloAluno: Livro set -> Time,
	livrosPraDoar: Livro set -> Time
}

sig Organizador{}

sig Livro{}

sig Nome{}

sig Matricula{}

// ---- FUNÇÕES ---- //

fun quantidadeTotalDeLivrosNoBloco[b: Bloco, t: Time]: set Livro {
	b.livrosDisponiveis.t + b.livrosEmprestados.t
}

// ---- PREDICADOS ---- //

pred cadaBlocoTemDe1a10Livros[]{
	all b1: Bloco, t: Time | #quantidadeTotalDeLivrosNoBloco[b1,t] < 11
}

pred nomesDevemSerDiferentes[]{
	all n1: Nome | one n1.~nomeAluno
}

pred matriculasDevemSerDiferentes[]{
	all mat1: Matricula | one mat1.~matriculaAluno
}

pred init[t: Time]{
	t = first => #Bloco.alunosCadastrados.t = 0 
}

pred cadastrarAluno[t, t': Time, a: Aluno, b: Bloco ]{
	a not in b.alunosCadastrados.t
	b.alunosCadastrados.t' = b.alunosCadastrados.t + a
}

pred emprestarLivro[l: Livro, b: Bloco, t,t': Time, a: Aluno]{
	a in b.alunosCadastrados.t
	l in b.livrosDisponiveis.t and (l not in a.livrosReservadosPeloAluno.t)
	a.livrosEmprestadosComAluno.t' = a.livrosEmprestadosComAluno.t + l
	b.livrosDisponiveis.t' = b.livrosDisponiveis.t - l
	b.livrosEmprestados.t' = b.livrosEmprestados.t + l
}

pred devolverLivro[l: Livro, b: Bloco, t,t': Time, a: Aluno]{
	l in a.livrosEmprestadosComAluno.t
	l in b.livrosEmprestados.t
	b.livrosDisponiveis.t' = b.livrosDisponiveis.t + l
	b.livrosEmprestados.t' = b.livrosEmprestados.t - l
}

pred reservarLivro[l: Livro, t, t': Time, a: Aluno, b: Bloco]{
	a in b.alunosCadastrados.t
	l in b.livrosEmprestados.t and (l not in a.livrosReservadosPeloAluno.t)
	a.livrosReservadosPeloAluno.t' = a.livrosReservadosPeloAluno.t + l
	b.livrosReservados.t' = b.livrosReservados.t + l
}

pred emprestarLivroReservado[l: Livro, t, t': Time, a: Aluno, b: Bloco]{
	a in b.alunosCadastrados.t
	l in b.livrosDisponiveis.t and (l in a.livrosReservadosPeloAluno.t)
	a.livrosEmprestadosComAluno.t' = a.livrosEmprestadosComAluno.t + l
	a.livrosReservadosPeloAluno.t' = a.livrosReservadosPeloAluno.t - l
	b.livrosDisponiveis.t' = b.livrosDisponiveis.t - l
	b.livrosEmprestados.t' = b.livrosEmprestados.t + l
}

pred doarLivro[l: Livro, b: Bloco, t, t': Time, a: Aluno]{
	a in b.alunosCadastrados.t
	#quantidadeTotalDeLivrosNoBloco[b,t] < 11 and (l in a.livrosPraDoar.t)
	b.livrosDisponiveis.t' = b.livrosDisponiveis.t + l
	a.livrosPraDoar.t' = a.livrosPraDoar.t - l	
}

pred restricoesLivro[]{
	all l1: Livro, t: Time,b1: Bloco| (l1 in b1.livrosEmprestados.t) => (l1 not in b1.livrosDisponiveis.t)
	all l1: Livro, t: Time | one l1.~(livrosDisponiveis.t)
	all l1: Livro, t: Time | one l1.~(livrosEmprestadosComAluno.t)
	all l1: Livro, t: Time | one l1.~(livrosEmprestados.t)
	all l1: Livro, t: Time | one l1.~(livrosReservadosPeloAluno.t)
	all l1: Livro, t: Time | one l1.~(livrosReservados.t)
}

pred show[]{}

// ---- FATOS ---- //

fact Sistema{
	#Bloco = 3
	CAA + CN + CD = Universidade.blocos
	cadaBlocoTemDe1a10Livros
	restricoesLivro
	all helper:Organizador | one helper.~organizador
	all mat: Matricula | one mat.~matriculaAluno
	all n: Nome | one n.~nomeAluno
	
}

fact traces{
	init[first]
	all pre: Time-last | let pos = pre.next |
	some b: Bloco, a: Aluno, l: Livro |
	cadastrarAluno[pre, pos, a, b] or
	emprestarLivro[l, b, pre, pos, a] or
	devolverLivro[l, b, pre, pos, a]or
	reservarLivro[l, pre, pos, a, b]or
	emprestarLivroReservado[l,pre,pos,a,b]or
	doarLivro[l, b, pre, pos, a]
}

run show for 10
