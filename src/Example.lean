import Aesop
open IO

def cirno : String := "Cirno's Perfect Arithmetics Class has begun!"

example : α → α :=
  by aesop

def main : IO Unit :=
  println cirno
