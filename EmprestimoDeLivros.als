module EmprestimoDeLivros
open util/ordering[Time]

one sig EmprestimoDeLivros{
	locais: set Bloco
}

sig Time{}

sig Bloco{
	organizador: one Organizador,
	alunosCadastrados: set Aluno,
	livros: some Livro
}
one sig BlocoCAA, BlocoCN, BlocoCD extends Bloco{}

sig Pessoa{
	nome: one Nome,
	matricula: one Matricula
}

sig Organizador extends Pessoa{

}

sig Aluno extends Pessoa{
	statusAluno: StatusCadastro one -> Time
}

sig Livro{
	nomeLivro: one NomeLivro,
	nomeAutor: one Autor,
	statusLivro: one Status
}

sig Nome{}

sig NomeLivro{}

sig Matricula{}

sig Status{}

sig Autor{}

abstract sig StatusCadastro{}

sig Cadastrado, NaoCadastrado extends StatusCadastro{}



// ---- FACT ---- //
fact{
	#Bloco = 3
	Pessoa = Aluno + Organizador // so cria objetos do tipo(subclasse) Aluno ou Organizador
	BlocoCAA+BlocoCN+BlocoCD = EmprestimoDeLivros.locais // faz o sistema ter apenas esses 3 blocos
	all helper:Organizador | one helper.~organizador // cria um unico objeto Organizador para cada bloco
	all book:Livro | one book.~livros // faz cada objeto Livro ser parte de um bloco
	all aluno: Aluno | one aluno.~alunosCadastrados
	all mat: Matricula | one mat.~matricula
	all n: Nome | one n.~nome
	all n: NomeLivro | one n.~nomeLivro
	all autor: Autor | one autor.~nomeAutor
	all status: Status | one status.~statusLivro
}

// ---- ASSERT ---- //

// ---- PRED ---- //
pred cadaBlocoTem1a10Livros[]{
	all b: Bloco | #b.livros < 11
}

pred show[]{}


run show for 15 but 1 Aluno
