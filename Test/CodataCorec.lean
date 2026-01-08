import Qpf

codata SimpleCo α where
  | cons : α → SimpleCo α → SimpleCo α

-- Ensure the macro generates a corecursor.
#check SimpleCo.corec
