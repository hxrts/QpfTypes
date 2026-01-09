import Qpf

-- Simple inductive to test recOn and casesOn wrappers.
data Simple α where
  | nil : Simple α
  | cons : α → Simple α → Simple α

#check Simple.recOn
#check Simple.casesOn
#check Simple.rec
#check Simple.drec
