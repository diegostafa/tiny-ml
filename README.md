# TinyML

Simple interpreter for the core language of ML.

## Build (Linux)

dev deps:
- dotnet-sdk
- dotnet-runtime
- mono
- nuget

project deps:
```
dotnet add package Fsharp.Core
dotnet add package FsLexYacc
dotnet add package FsLexYacc.runtime
dotnet add package System.ValueTuple
```

build:
```
dotnet build
```