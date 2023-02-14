# TinyML

Simple interpreter for the core language of ML.

## Build (Linux)

dev deps:
- dotnet-sdk
- dotnet-runtime
- mono
- nuget

build:
```bash
nuget restore
make gen-lexer-parser
dotnet build
```

## Run

the project comes in 4 configurations:
* "`Debug`"
* "`Release`"
* "`Debug Interactive`"
* "`Release Interactive`"

to run a project in a specific configuration:
```bash
dotnet run --configuration <configuration> # default configuration is "Debug"
```