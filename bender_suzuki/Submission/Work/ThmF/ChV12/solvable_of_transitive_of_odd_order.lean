import Mathlib
import Submission.Work.ThmF.ChV12.transitive_orbit_basics
import Submission.Work.ThmF.ChV12.Fitting_cyclic_fpf
import Submission.Work.ThmF.ChV12.solvable_of_cyclic_normal_irreducible
import Submission.Work.ThmF.ChV12.isSolvable_of_transitive_of_primitive_ppd
import Submission.Work.ThmF.ChV12.isSolvable_of_transitive_of_card_two_pow_six
import Submission.Work.PGroup.exists_prime_orderOf_two_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV12
-- **(2026-10-07, area owner).**  Per the lead's ruling the odd-order theorem may be assumed,
-- so this node carries `(hFT : FeitThompsonProp)`; the FT-free route survives as the
-- `PpdClosureProp`/`TransitiveLinearSolvable` definitions (`ChV12/ppdClosureProp_holds.lean`).


/-- For a finite group `A` with at most two elements, `MulAut A` is trivial. -/
private theorem subsingleton_mulAut_of_card_le_two {A : Type} [Group A] [Finite A]
    (hcard : Nat.card A ≤ 2) : Subsingleton (MulAut A) := by
  haveI : Fintype A := Fintype.ofFinite A
  -- at most one non-identity element
  have huniq : ∀ x y : A, x ≠ 1 → y ≠ 1 → x = y := by
    intro x y hx hy
    by_contra hxy
    have h3 : 3 ≤ Fintype.card A := by
      have hinj : Function.Injective (fun i : Fin 3 => (![x, y, 1] : Fin 3 → A) i) := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
      calc 3 = Fintype.card (Fin 3) := (Fintype.card_fin 3).symm
        _ ≤ Fintype.card A := Fintype.card_le_of_injective _ hinj
    have h2 : Fintype.card A ≤ 2 := by rwa [Nat.card_eq_fintype_card] at hcard
    omega
  refine ⟨fun σ τ => MulEquiv.ext (fun a => ?_)⟩
  by_cases ha : a = 1
  · rw [ha, map_one, map_one]
  · have hσa : σ a ≠ 1 := fun h => ha (σ.injective (by rw [h, map_one]))
    have hτa : τ a ≠ 1 := fun h => ha (τ.injective (by rw [h, map_one]))
    rw [huniq (σ a) a hσa ha, huniq (τ a) a hτa ha]

/-- **(2026-10-07, area owner, second pass.)**  The *statement* of this node is

> an odd-order group `D` acting faithfully and transitively on the non-identity elements of an
> elementary abelian `2`-group is solvable,

which is **exactly** the conclusion of `FeitThompsonProp` applied to `↥D` (`hodd` plus
`Nat.card ↥D = Nat.card D`).  The elaborate `ppd` route through
`isSolvable_of_transitive_of_primitive_ppd` / `even_card_closure_of_two_ppd` that this node used to
carry is therefore unnecessary now that the odd-order theorem is a hypothesis: it is part of the
*Feit–Thompson-free* route, which is out of scope (see `ChV12/ppdClosureProp_holds.lean`).  The body
below is the direct proof; the transitivity hypothesis is not needed for it.  The former proof is
recorded in `NOTES.md` §12. -/
theorem solvable_of_transitive_of_odd_order (hFT : Submission.Blueprint.FeitThompsonProp) {A D : Type} [Group A] [Group D] [Finite A] [Finite D]
    (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x)
    (hodd : Odd (Nat.card D)) (ρ : D →* MulAut A) (hfaith : Function.Injective ρ)
    (htrans : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ d : D, ρ d a = b) :
    Group.IsSolvable D :=
  hFT D hodd

end Work.ThmF.ChV12

