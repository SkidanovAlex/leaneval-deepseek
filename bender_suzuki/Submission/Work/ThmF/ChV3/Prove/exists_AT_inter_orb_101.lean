import Mathlib
import Submission.Work.ThmF.ChV3.Prove.OrbitCountDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.exists_AT_inter_orb_101`

Existence of a subgroup lying both in `AT R T P` (subgroups of `R` of order `|P|`, not inside
`T`, different from `P`) and in the `N_G(R)`-orbit of `P`.

This is the "witness" half of `orb_eq_AT_union_101`: `hRn : C_G(P) ≤ N_G(R)` together with
`hNG : N_G(P) = C_G(P)` and `hNGne : N_G(R) ≠ N_G(P)` produce `g₀ ∈ N_G(R) \ C_G(P)`, and
`A₀ = g₀ P g₀⁻¹` has all the required properties:

* `A₀ ≤ R` because `g₀` normalizes `R` and `P ≤ R`;
* `Nat.card A₀ = Nat.card P` because conjugation is injective;
* `A₀ ⊄ T` by hypothesis (`hno`);
* `A₀ ≠ P` since `g₀ P g₀⁻¹ = P` would give `g₀ ∈ N_G(P) = C_G(P)`, contradicting the choice
  of `g₀`;
* `A₀ ∈ orb P (N_G(R))` by construction.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Pointwise

namespace Work.ThmF.ChV3.Prove

open Work.ThmF.ChV3

theorem exists_AT_inter_orb_101 {G : Type} [Group G] [Finite G] {P R T : Subgroup G}
    (hRn : Work.ThmF.ChV3.CG P ≤ Work.ThmF.ChV3.NG R)
    (hNG : Work.ThmF.ChV3.NG P = Work.ThmF.ChV3.CG P)
    (hPR : P ≤ R)
    (hno : ∀ g : G, ¬ Work.ThmF.ChV3.cj g P ≤ T)
    (hNGne : Work.ThmF.ChV3.NG R ≠ Work.ThmF.ChV3.NG P) :
    ∃ A0 : Subgroup G, A0 ∈ Work.ThmF.ChV3.Prove.AT R T P ∧
      A0 ∈ Work.ThmF.ChV3.Prove.orb P (Work.ThmF.ChV3.NG R) := by
  classical
  -- `N_G(R) ≠ C_G(P)`, using `hNG`
  have hne : NG R ≠ CG P := fun h => hNGne (h.trans hNG.symm)
  have hnotsub : ¬ (NG R ≤ CG P) := fun h => hne (le_antisymm h hRn)
  -- a witness `g₀ ∈ N_G(R) \ C_G(P)`
  obtain ⟨g0, hg0N, hg0notC⟩ := Set.not_subset.mp hnotsub
  -- `A₀ = g₀ P g₀⁻¹`
  refine ⟨cj g0 P, ⟨?_, card_cj g0 P, hno g0, ?_⟩, g0, hg0N, rfl⟩
  · -- `A₀ ≤ R`: `g₀` normalizes `R` and `P ≤ R`
    simpa [show cj g0 R = R from (cj_eq_self_iff g0 R).mpr hg0N] using cj_mono hPR g0
  · -- `A₀ ≠ P`: otherwise `g₀ ∈ N_G(P) = C_G(P)`
    intro h
    exact hg0notC (hNG ▸ (cj_eq_self_iff g0 P).mp h)

end Work.ThmF.ChV3.Prove
