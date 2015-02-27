module EmprestimoDeLivros

one sig EmprestimoDeLivros{
	locais: set Bloco
}

sig Bloco{
	organizador: one Organizador,
	alunos: set Aluno,
	livros: some Livro
}
one sig BlocoCAA, BlocoCN, BlocoCD extends Bloco{}

sig Pessoa{}
sig Organizador extends Pessoa{}
sig Aluno extends Pessoa{}

sig Livro{}


// Facts
fact{
	#Bloco = 3
	Pessoa = Aluno + Organizador // so cria objetos do tipo(subclasse) Aluno ou Organizador
	BlocoCAA+BlocoCN+BlocoCD = EmprestimoDeLivros.locais // faz o sistema ter apenas esses 3 blocos
	all helper:Organizador | one helper.~organizador // cria um unico objeto Organizador para cada bloco
	all book:Livro | one book.~livros // faz cada objeto Livro ser parte de um bloco
	all student:Aluno | some student.~alunos // todo objeto Aluno esta cadastrado a pelo menos um bloco
}

pred show[]{}
run show for 5
