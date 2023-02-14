gen-lexer-parser:
	mono "packages/FsLexYacc.10.0.0/build/fslex/netcoreapp3.0/fslex.dll" "Lexer.fsl" -o "Lexer.fs" --unicode --module "TinyML.Lexer"
	mono "packages/FsLexYacc.10.0.0/build/fsyacc/netcoreapp3.0/fsyacc.dll" -o "Parser.fs" --module TinyML.Parser -v Parser.fsy
