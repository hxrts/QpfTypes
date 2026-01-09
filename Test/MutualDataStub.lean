import Qpf

/-!
# Mutual data (no cross references)

This checks the syntax wrapper for `mutual` blocks. It does *not* test
mutual recursion (which is still unsupported).
-/

mutual
  data Foo α where
    | mk : Foo α

  data Bar β where
    | mk : Bar β
end

#check Foo
#check Bar
