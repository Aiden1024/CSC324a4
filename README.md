# CSC324a4

This project is a basic proof checker for purely implicational minimal logic in miniKanren, made in Racket

Purely implicational minimal logic include propositions and proofs.

A proposition is a logical statement that makes a claim. The types of propositions used in this project are Constants (A, B, any symbol) and 
implications (A -> B meaning "A implies B").

The grammar for Propositions is as follows:
  <proposition> ::= IDENTIFIER | '(' <proposition> '->' <proposition ')'
  
A proof is a logical argument explaingn how a proposition is true. The grammar for Proofs is as follows.
  <proof> ::= '(' use <proposition ')'
               | '(' assume <proposition> <proof> ')'
               | '(' modus-ponens <proof> <proof> ')'
               
We implemented two different types of proof checking.

proofo: Takes a proposition and a proof. The relation holds if the proof is valid for the proposition
prove: Takes a proposition and returns a proof if one exists.

*Note: This project was created as an assignment for CSC324 at University of Toronto Mississauga. 
For students looking at this repo while taking the course, do so at your own risk. Do not plagarize, Markus will detect you.
