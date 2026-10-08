import Submission.Work.Hall.Basic
import Submission.Work.Hall.HallMain
import Submission.Work.Hall.Main.isHall_conj
import Submission.Work.Hall.Main.le_conj_of_isPiNat
import Submission.Work.Hall.SchurZassenhaus.hall_schurZassenhaus_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# P. Hall's theorems for finite solvable groups (area A1)

This module collects the main results of area A1 (`Submission/Work/Hall`) under their stable names.
Everything is proved in the imported modules; see `Submission/Work/Hall/NOTES.md` for the layout.
-/

open scoped Pointwise

namespace Work.Hall

/-- `C_π` (P. Hall): two Hall `π`-subgroups of a finite solvable group are conjugate. -/
theorem isHall_conj {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] {π : ℕ → Prop}
    {H K : Subgroup G} (hH : IsHall π H) (hK : IsHall π K) :
    ∃ g : G, K = MulAut.conj g • H :=
  Main.isHall_conj hH hK

/-- `D_π` (P. Hall): every `π`-subgroup of a finite solvable group lies in a conjugate of a given
Hall `π`-subgroup. -/
theorem le_conj_of_isPiNat {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] {π : ℕ → Prop}
    {H K : Subgroup G} (hH : IsHall π H) (hK : IsPiNat π (Nat.card K)) :
    ∃ g : G, K ≤ MulAut.conj g • H :=
  Main.le_conj_of_isPiNat hH hK

/-- Conjugacy of complements of a normal Hall subgroup (Schur–Zassenhaus, conjugacy part;
`N` solvable, e.g. any subgroup of a solvable group). -/
theorem schurZassenhaus_conj {G : Type*} [Group G] [Finite G] {N H K : Subgroup G} [N.Normal]
    (hsol : Group.IsSolvable N) (hc : (Nat.card N).Coprime N.index) (hH : N.IsComplement' H)
    (hK : N.IsComplement' K) : ∃ g : G, K = MulAut.conj g • H :=
  SchurZassenhaus.hall_schurZassenhaus_conj hsol hc hH hK

end Work.Hall
