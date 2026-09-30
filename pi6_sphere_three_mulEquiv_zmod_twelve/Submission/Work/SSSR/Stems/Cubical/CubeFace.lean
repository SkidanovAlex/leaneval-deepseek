import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

open scoped unitInterval Topology
namespace Work.SSSR.Stems.Cubical

/-- The cube `I^n`, as a type. -/
abbrev IC (n : ℕ) := Fin n → unitInterval

end Work.SSSR.Stems.Cubical
