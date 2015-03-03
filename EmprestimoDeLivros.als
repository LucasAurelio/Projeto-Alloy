open util/ordering [Time]

module EmprestimoDeLivros

// ---- ASSINATURAS ---- //

sig Time{}

one sig Universidade{
	blocos: set Bloco
}

sig Bloco{
	organizador: one Organizador,
	alunosCadastrados: Aluno -> Time,
	livros: Livro some -> Time
}

one sig CAA, CD, CN extends Bloco{}

sig Aluno{
	nomeAluno: Nome,
	matriculaAluno: Matricula,
	statusAluno: StatusCadastro one -> Time,
	livrosEmprestados: Livro set -> Time,
	//--- Mudei ---//
	livrosReservados: Livro set -> Time,
	livrosPraDoar: Livro set -> Time
}

sig Organizador{
	nomeOrganizador: Nome,
	matriculaOrganizador: Matricula
}

sig Livro{
	nomeLivro: Nome,
	autorLivro: Autor,
	statusLivro: Status one -> Time
}

abstract sig StatusCadastro{}

one sig Cadastrado, NaoCadastrado extends StatusCadastro{}

abstract sig Status{}

//--- Mudei ---//
sig Emprestado, Livre extends Status{}

sig Nome{}

sig Matricula{}

sig Autor{}

// ---- FUNÇÕES ---- //

fun alunosNoBloco[b: Bloco, t: Time]: set Aluno {
	b.alunosCadastrados.t
}

fun livrosNoBloco[b: Bloco, t: Time]: set Livro {
	b.livros.t
}

fun livrosPorAluno[a: Aluno, t: Time]: set Livro {
	a.livrosEmprestados.t
}

fun todosOsNomes[a: Aluno, o: Organizador, l: Livro]: set Nome{
	 a.nomeAluno + o.nomeOrganizador + l.nomeLivro
}

// ---- PREDICADOS ---- //

pred verificaRelacaoAlunosEBlocosCadastrados[]{
	all a1: Aluno, b1: Bloco, t: Time |  a1 in b1.alunosCadastrados.t => a1.statusAluno.t = Cadastrado
		all a1: Aluno, t: Time | a1.statusAluno.t = NaoCadastrado => #a1.livrosEmprestados = 0
}

pred cadaBlocoTemDe1a10Livros[]{
	all b1: Bloco | #b1.livros < 11
}

pred nomesDevemSerDiferentes[]{ //tem que consertar
	all a1:Aluno, a2:Aluno-a1 | a1.nomeAluno != a2.nomeAluno
	all o1:Organizador, o2:Organizador-o1 | o1.nomeOrganizador != o2.nomeOrganizador
	all l1:Livro, l2:Livro-l1 | l1.nomeLivro != l2.nomeLivro
	all a1:Aluno, o1:Organizador| a1.nomeAluno != o1.nomeOrganizador
	all a1:Aluno, l1: Livro | a1.nomeAluno != l1.nomeLivro
	all o1:Organizador, l1: Livro | o1.nomeOrganizador != l1.nomeLivro
}

pred matriculasDevemSerDiferentes[]{ //tem que consertar
	all a1:Aluno, a2:Aluno-a1 | a1.matriculaAluno != a2.matriculaAluno
	all o1:Organizador, o2:Organizador-o1 | o1.matriculaOrganizador != o2.matriculaOrganizador
	all a1:Aluno, o1:Organizador | a1.matriculaAluno != o1.matriculaOrganizador
}

pred alunoNaoCadastradoNaoPodeTerLivro[]{
	all a: Aluno, t: Time | a.statusAluno.t in NaoCadastrado => #a.livrosEmprestados = 0 
}

pred alunoCadastradoPrecisaPertencerABloco[]{
	all a: Aluno, t: Time | (a.statusAluno.t  in Cadastrado) => one a.~(alunosCadastrados.t)
}

//--- Mudei ---//
pred init[t: Time]{
	t = first => Aluno.statusAluno.t = NaoCadastrado 
}

pred cadastrarAluno[t, t': Time, a: Aluno, b: Bloco ]{
	a.statusAluno.t in NaoCadastrado
	a.statusAluno.t' = Cadastrado
}

pred alocaAluno[t, t': Time, a: Aluno, b: Bloco]{
	a.statusAluno.t in Cadastrado
	a not in b.alunosCadastrados.t
	b.alunosCadastrados.t' = b.alunosCadastrados.t + a
}

pred locarLivro[l: Livro, b: Bloco, t,t': Time, a: Aluno]{
	l in b.livros.t
	l.statusLivro.t in Livre
	l.statusLivro.t' = Emprestado
	a.livrosEmprestados.t' = a.livrosEmprestados.t + l	
}

pred devolverLivro[l: Livro, b: Bloco, t,t': Time, a: Aluno]{
	l in (a.livrosEmprestados).t
	l.statusLivro.t in Emprestado
	l.statusLivro.t' = Livre
	b.livros.t' = b.livros.t + l
}

//--- Mudei ---//
pred reservarLivro[l: Livro, t, t': Time, a: Aluno]{
	l.statusLivro.t = Emprestado
	a.livrosReservados.t' = (a.livrosReservados.t + l)
	l.statusLivro.t = Livre and (l in a.livrosReservados.t)
	a.livrosEmprestados.t' = (a.livrosEmprestados.t + l)
	a.livrosReservados.t' = (a.livrosReservados.t - l)
}

//--- Mudei ---//
pred doarLivro[l: Livro, b: Bloco, t, t': Time, a: Aluno]{
	#b.livros.t < 11 and (l in a.livrosPraDoar.t)
	b.livros.t' = b.livros.t + l
	a.livrosPraDoar.t' = a.livrosPraDoar.t - l
	 
	
}

pred restricoesLivro[]{
	all a1: Aluno, l1:Livro, t: Time | l1 in a1.livrosEmprestados.t => l1.statusLivro.t = Emprestado
	all a1: Aluno, l1: Livro, t:Time | l1 !in a1.livrosEmprestados.t => l1.statusLivro.t = Livre
	all l1: Livro, a1: Aluno ,a2: Aluno, t: Time |  l1 in a1.livrosEmprestados.t => l1 not in a2.livrosEmprestados.t
	all l1: Livro, t: Time | one l1.~(livros.t)
}

pred show[]{}

// ---- FATOS ---- //

fact Sistema{
	#Bloco = 3
	CAA + CN + CD = Universidade.blocos
	verificaRelacaoAlunosEBlocosCadastrados
	cadaBlocoTemDe1a10Livros
	restricoesLivro
	alunoCadastradoPrecisaPertencerABloco
	all helper:Organizador | one helper.~organizador
	all mat: Matricula | one mat.~matriculaAluno
	all n: Nome | one n.~nomeAluno
	all mat: Matricula | one mat.~matriculaOrganizador
	all n: Nome | one n.~nomeOrganizador
	all n: Nome | one n.~nomeLivro
	all autor: Autor | one autor.~autorLivro
	
}

fact traces{
	init[first]
	all pre: Time-last | let pos = pre.next |
	some b: Bloco, a: Aluno, l: Livro |
	cadastrarAluno[pre, pos, a, b] or
	alocaAluno[pre, pos, a, b] or
	locarLivro[l, b, pre, pos, a] or
	devolverLivro[l, b, pre, pos, a]or
	//--- Mudei ---//
	reservarLivro[l, pre, pos, a]or
	doarLivro[l, b, pre, pos, a]
}

run show for 10
