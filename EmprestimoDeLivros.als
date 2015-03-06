open util/ordering [Time]

module EmprestimoDeLivros
/*
A biblioteca central da UFCG está em reforma e por enquanto não está emprestando livros.
Três alunos do curso Ciência da Computação decidiram emprestar alguns livros.
Cada aluno tem um local para receber os alunos do curso: Bloco CAA, Bloco CN  e Bloco CD.
Para pegar emprestado ou reservar algum livro o aluno deve ter um cadastro com seu nome, endereço e período.
Cada um dos locais têm no máximo 10 livros para emprestar aos alunos.
Quando um livro for emprestado ele deixa de estar disponível, havendo um registro de quem está com o livro.
Se um aluno deseja pegar um livro que está indisponível ele pode reservar.
Os alunos também podem doar livros de Computação para estes locais.
*/

// ---- ASSINATURAS ---- //

sig Time{}

one sig Universidade{
	blocos: set Bloco
}

abstract sig Bloco{
	organizador: one Organizador,
	alunosCadastrados: Aluno -> Time,
	livrosDisponiveis: Livro some -> Time,
	livrosEmprestados: Livro -> Time,
	livrosReservados: Livro -> Time
}

one sig CAA, CD, CN extends Bloco{}

sig Aluno{
	nomeAluno: one Nome,
	matriculaAluno: one Matricula,
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
	all b1: Bloco, t: Time | #quantidadeTotalDeLivrosNoBloco[b1,t] < 11 and
											#quantidadeTotalDeLivrosNoBloco[b1,t] > 0
}

pred nomesDevemSerDiferentes[]{
	all n1: Nome | one n1.~nomeAluno
}

pred matriculasDevemSerDiferentes[]{
	all mat1: Matricula | one mat1.~matriculaAluno
}

pred init[t: Time]{
	no (Bloco.alunosCadastrados).t
	no (Bloco.livrosEmprestados).t
	no (Bloco.livrosReservados).t
	no (Aluno.livrosEmprestadosComAluno).t
	no (Aluno.livrosReservadosPeloAluno).t
}

pred cadastrarAluno[t, t': Time, a: Aluno, b: Bloco]{
	a not in b.alunosCadastrados.t
	b.alunosCadastrados.t' = b.alunosCadastrados.t + a
	
	all b2:Bloco-b | b2.alunosCadastrados.t = b2.alunosCadastrados.t'
	all b2:Bloco | b2.livrosDisponiveis.t = b2.livrosDisponiveis.t'
	all b2:Bloco | b2.livrosEmprestados.t = b2.livrosEmprestados.t'
	all b2:Bloco | b2.livrosReservados.t = b2.livrosReservados.t'
	all a2:Aluno | a2.livrosEmprestadosComAluno.t = a2.livrosEmprestadosComAluno.t'
	all a2:Aluno | a2.livrosReservadosPeloAluno.t = a2.livrosReservadosPeloAluno.t'
	all a2:Aluno | a2.livrosPraDoar.t = a2.livrosPraDoar.t'
}

pred emprestarLivro[l: Livro, b: Bloco, t,t': Time, a: Aluno]{
	a in b.alunosCadastrados.t
	l in b.livrosDisponiveis.t and (l !in a.livrosReservadosPeloAluno.t)
	a.livrosEmprestadosComAluno.t' = a.livrosEmprestadosComAluno.t + l
	b.livrosDisponiveis.t' = b.livrosDisponiveis.t - l
	b.livrosEmprestados.t' = b.livrosEmprestados.t + l

	all b2:Bloco | b2.alunosCadastrados.t = b2.alunosCadastrados.t'
	all b2:Bloco-b | b2.livrosDisponiveis.t = b2.livrosDisponiveis.t'
	all b2:Bloco-b | b2.livrosEmprestados.t = b2.livrosEmprestados.t'
	all b2:Bloco | b2.livrosReservados.t = b2.livrosReservados.t'
	all a2:Aluno-a | a2.livrosEmprestadosComAluno.t = a2.livrosEmprestadosComAluno.t'
	all a2:Aluno | a2.livrosReservadosPeloAluno.t = a2.livrosReservadosPeloAluno.t'
	all a2:Aluno | a2.livrosPraDoar.t = a2.livrosPraDoar.t'
}

pred devolverLivro[l: Livro, b: Bloco, t,t': Time, a: Aluno]{
	l in a.livrosEmprestadosComAluno.t
	l in b.livrosEmprestados.t
	b.livrosDisponiveis.t' = b.livrosDisponiveis.t + l
	b.livrosEmprestados.t' = b.livrosEmprestados.t - l

	all b2:Bloco | b2.alunosCadastrados.t = b2.alunosCadastrados.t'
	all b2:Bloco-b | b2.livrosDisponiveis.t = b2.livrosDisponiveis.t'
	all b2:Bloco-b | b2.livrosEmprestados.t = b2.livrosEmprestados.t'
	all b2:Bloco | b2.livrosReservados.t = b2.livrosReservados.t'
	all a2:Aluno | a2.livrosEmprestadosComAluno.t = a2.livrosEmprestadosComAluno.t'
	all a2:Aluno | a2.livrosReservadosPeloAluno.t = a2.livrosReservadosPeloAluno.t'
	all a2:Aluno | a2.livrosPraDoar.t = a2.livrosPraDoar.t'
}

pred reservarLivro[l: Livro, t, t': Time, a: Aluno, b: Bloco]{
	a in b.alunosCadastrados.t
	l in b.livrosEmprestados.t and (l not in a.livrosReservadosPeloAluno.t)
	l not in a.livrosEmprestadosComAluno.t
	a.livrosReservadosPeloAluno.t' = a.livrosReservadosPeloAluno.t + l
	b.livrosReservados.t' = b.livrosReservados.t + l
	
	all b2:Bloco | b2.alunosCadastrados.t = b2.alunosCadastrados.t'
	all b2:Bloco | b2.livrosDisponiveis.t = b2.livrosDisponiveis.t'
	all b2:Bloco | b2.livrosEmprestados.t = b2.livrosEmprestados.t'
	all b2:Bloco-b | b2.livrosReservados.t = b2.livrosReservados.t'
	all a2:Aluno | a2.livrosEmprestadosComAluno.t = a2.livrosEmprestadosComAluno.t'
	all a2:Aluno-a | a2.livrosReservadosPeloAluno.t = a2.livrosReservadosPeloAluno.t'
	all a2:Aluno | a2.livrosPraDoar.t = a2.livrosPraDoar.t'
}

pred emprestarLivroReservado[l: Livro, t, t': Time, a: Aluno, b: Bloco]{
	a in b.alunosCadastrados.t
	l in b.livrosDisponiveis.t and (l in a.livrosReservadosPeloAluno.t)
	a.livrosEmprestadosComAluno.t' = a.livrosEmprestadosComAluno.t + l
	a.livrosReservadosPeloAluno.t' = a.livrosReservadosPeloAluno.t - l
	b.livrosDisponiveis.t' = b.livrosDisponiveis.t - l
	b.livrosEmprestados.t' = b.livrosEmprestados.t + l

	all b2:Bloco | b2.alunosCadastrados.t = b2.alunosCadastrados.t'
	all b2:Bloco-b | b2.livrosDisponiveis.t = b2.livrosDisponiveis.t'
	all b2:Bloco-b | b2.livrosEmprestados.t = b2.livrosEmprestados.t'
	all b2:Bloco | b2.livrosReservados.t = b2.livrosReservados.t'
	all a2:Aluno-a | a2.livrosEmprestadosComAluno.t = a2.livrosEmprestadosComAluno.t'
	all a2:Aluno-a | a2.livrosReservadosPeloAluno.t = a2.livrosReservadosPeloAluno.t'
	all a2:Aluno | a2.livrosPraDoar.t = a2.livrosPraDoar.t'
}

pred doarLivro[l: Livro, b: Bloco, t, t': Time, a: Aluno]{
	a in b.alunosCadastrados.t
	#quantidadeTotalDeLivrosNoBloco[b,t] < 11 and (l in a.livrosPraDoar.t)
	b.livrosDisponiveis.t' = b.livrosDisponiveis.t + l
	a.livrosPraDoar.t' = a.livrosPraDoar.t - l

	all b2:Bloco | b2.alunosCadastrados.t = b2.alunosCadastrados.t'
	all b2:Bloco-b | b2.livrosDisponiveis.t = b2.livrosDisponiveis.t'
	all b2:Bloco | b2.livrosEmprestados.t = b2.livrosEmprestados.t'
	all b2:Bloco | b2.livrosReservados.t = b2.livrosReservados.t'
	all a2:Aluno | a2.livrosEmprestadosComAluno.t = a2.livrosEmprestadosComAluno.t'
	all a2:Aluno | a2.livrosReservadosPeloAluno.t = a2.livrosReservadosPeloAluno.t'
	all a2:Aluno-a | a2.livrosPraDoar.t = a2.livrosPraDoar.t'
}

pred restricoesLivro[]{
	all l: Livro, t:Time | l in Bloco.livrosDisponiveis.t => l !in (Bloco.livrosEmprestados.t + Aluno.livrosPraDoar.t)
	all l: Livro, t:Time | l in Bloco.livrosEmprestados.t => l !in (Bloco.livrosDisponiveis.t + Aluno.livrosPraDoar.t)
	all l: Livro, t:Time | l in Aluno.livrosPraDoar.t => l !in (Bloco.livrosDisponiveis.t + Bloco.livrosEmprestados.t)
	
	all l1: Livro, t: Time | lone l1.~(livrosDisponiveis.t)
	all l1: Livro, t: Time | lone l1.~(livrosEmprestadosComAluno.t)
	all l1: Livro, t: Time | lone l1.~(livrosEmprestados.t)
	all l1: Livro, t: Time | lone l1.~(livrosReservadosPeloAluno.t)
	all l1: Livro, t: Time | lone l1.~(livrosReservados.t)
}

pred show[]{}

// ---- FATOS ---- //

fact Sistema{
	CAA + CN + CD = Universidade.blocos
	cadaBlocoTemDe1a10Livros
	restricoesLivro
	nomesDevemSerDiferentes
	matriculasDevemSerDiferentes
	all helper:Organizador | one helper.~organizador
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

// ---- ASSERTS ---- //

assert testeNumeroDeBlocosIgualATres{
	#Bloco = 3
}

assert testeTodoBlocoTemEntreUmEDezLivros{
	all b:Bloco, t:Time | #(quantidadeTotalDeLivrosNoBloco[b, t]) > 0 and 
									#(quantidadeTotalDeLivrosNoBloco[b, t]) < 11
}

assert testeLivroPertenceAUnicoBloco {
	all l: Livro, b: Bloco, t: Time | (l in b.livrosDisponiveis.t => (all b2:Bloco-b | l ! in b2.livrosDisponiveis.t))
}

assert testeLivroUnicaListaDeAluno {
	all l:Livro, a:Aluno, t:Time | l in a.livrosEmprestadosComAluno.t =>
										(l !in a.livrosReservadosPeloAluno.t and l !in a.livrosPraDoar.t)
	all l:Livro, a:Aluno, t:Time | l in a.livrosReservadosPeloAluno.t =>
										(l !in a.livrosEmprestadosComAluno.t and l !in a.livrosPraDoar.t)
	all l:Livro, a:Aluno, t:Time | l in a.livrosPraDoar.t =>
										(l !in a.livrosEmprestadosComAluno.t and l !in a.livrosReservadosPeloAluno.t)
}

assert alunoNaoReservaLivroJaPegoPorEle{
	all pre: Time-last | let pos = pre.next | all a:Aluno, l:Livro |
		l in a.livrosReservadosPeloAluno.pos => l !in a.livrosEmprestadosComAluno.pre
}

check testeNumeroDeBlocosIgualATres for 6
check testeTodoBlocoTemEntreUmEDezLivros for 11
check testeLivroPertenceAUnicoBloco for 6
check testeLivroUnicaListaDeAluno for 6
check alunoNaoReservaLivroJaPegoPorEle for 6

run show for 5
