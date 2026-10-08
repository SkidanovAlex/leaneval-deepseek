import Mathlib
import Submission.Work.BG.S02
import Submission.OddOrder.GroupTheory.ConjClassSet

/-!
# Area BG: auxiliary definitions for the proof of Theorem 3.2 (Bender–Glauberman 1981)

`T = H₀ ∖ U` is Bender–Glauberman's TI-subset.  For the counting argument of the proof of
Theorem 3.2 (p. 208) the two finsets

* `Tfin C` — the set `T ⊆ G` itself, and
* `TconjFin C` — its union of `G`-conjugates `T^G = 𝒞_G(T)`,

are needed.  They are defined as the finsets underlying the corresponding `Set`s, so that the
TI-counting lemma `OddOrder.GroupTheory.IsTISubset.sum_conjClassSet` applies syntactically.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-- `T = H₀ ∖ U` of Bender–Glauberman's Hypothesis 1.2, as a finset of `G`. -/
noncomputable def Tfin (C : Sec2Ctx G) : Finset G :=
  (Set.toFinite (Tset C.P.H0 C.P.U)).toFinset

/-- The union `T^G = 𝒞_G(T)` of the `G`-conjugates of `T = H₀ ∖ U`, as a finset of `G`. -/
noncomputable def TconjFin (C : Sec2Ctx G) : Finset G :=
  (Set.toFinite (OddOrder.GroupTheory.conjClassSet (Tset C.P.H0 C.P.U))).toFinset

@[simp] theorem mem_Tfin {C : Sec2Ctx G} {x : G} : x ∈ Tfin C ↔ x ∈ Tset C.P.H0 C.P.U := by
  classical rw [Tfin, Set.Finite.mem_toFinset]

@[simp] theorem mem_TconjFin {C : Sec2Ctx G} {x : G} :
    x ∈ TconjFin C ↔ x ∈ OddOrder.GroupTheory.conjClassSet (Tset C.P.H0 C.P.U) := by
  classical rw [TconjFin, Set.Finite.mem_toFinset]

end Work.BG
