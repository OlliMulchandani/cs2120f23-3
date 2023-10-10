def crazy (f : String -> String) (a : String) := (f a)
#eval crazy (String.append "Hello") " World!"


def xor : Bool → Bool → Bool
| true, true => false
| true, false => true
| false, true => true
| false, false => false

#eval xor true false