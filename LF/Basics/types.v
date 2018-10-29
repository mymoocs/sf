Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.
Inductive color : Type :=
  | black : color
  | white : color
  | primary : rgb -> color.

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.