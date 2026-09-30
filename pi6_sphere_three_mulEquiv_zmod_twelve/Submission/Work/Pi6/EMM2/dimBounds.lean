import Mathlib
import Submission.Work.Pi6.EMM2.Statements
import Submission.Work.Pi6.EMM2.SerreKit
import Submission.Work.Pi6.EMM2.SSKit
import Submission.Work.Pi6.EMM2.K2F9Kit
import Submission.Work.Pi6.EMM2.K4Kit
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.EMM2

/-- **The dimension bounds `dim H³, H⁴ ≤ 1` of the `K(ℤ/2,2)` forcing (threshold `9`).**

For a Serre spectral sequence `S` over `𝔽₂` through total degree `6` of `p : E → B`
(`F := fiber p (p e₀)`) with `H⁰(B) = 𝔽₂`, `H¹(B) = 0`, `H⁰(F) = 𝔽₂`, `H¹(F) = H³(F) = 0`,
`dim H²(F) = 1`, all of `H^≤6(B)`, `H^≤6(F)` finite dimensional, `H³(E) = 0` and `dim H⁴(E) = 1`:
`dim H³(B) ≤ 1` and `dim H⁴(B) ≤ 1`.

Route: `Work.Pi6.EMM2.finrank_row0_bound` (the telescoped row-`0` bound) with `n = 3` and `n = 4`;
the sums evaluate to `dim H¹(B)·dim H¹(F) + dim H⁰(B)·dim H²(F) = 1` (resp.
`dim H²(B)·dim H¹(F) + dim H¹(B)·dim H²(F) + dim H⁰(B)·dim H³(F) = 0`), using
`finrank_eq_zero_of_isZero` for the vanishing factors. -/
theorem dimBounds
    {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (S : Work.Pi6.CohSS (ZMod 2)) (hS : Work.Pi6.IsSerreMSS S p e₀ 6)
    (hB0 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) B 0) = 1)
    (hB1 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) B 1))
    (hF0 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) 0) = 1)
    (hF1 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) 1))
    (hF2 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) 2) = 1)
    (hF3 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) 3))
    (hFinB : ∀ s : ℕ, s ≤ 6 → FiniteDimensional (ZMod 2) (Work.Pi6.Coh (ZMod 2) B s))
    (hFinF : ∀ q : ℕ, q ≤ 6 → FiniteDimensional (ZMod 2)
      (Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) q))
    (hE3 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) E 3))
    (hE4 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) E 4) = 1) :
    Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) B 3) ≤ 1 ∧
      Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) B 4) ≤ 1 := by
  have hF1' : Module.finrank (ZMod 2)
      (Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) 1) = 0 :=
    K2F9.finrank_eq_zero_of_isZero hF1
  have hF3' : Module.finrank (ZMod 2)
      (Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) 3) = 0 :=
    K2F9.finrank_eq_zero_of_isZero hF3
  have hB1' : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) B 1) = 0 :=
    K2F9.finrank_eq_zero_of_isZero hB1
  have hE3' : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) E 3) = 0 :=
    K2F9.finrank_eq_zero_of_isZero hE3
  constructor
  · -- `n = 3`: the telescoped bound with the sum evaluated to `1`
    have hb := finrank_row0_bound S p e₀ 6 hS hFinB hFinF hF0 3 (by norm_num)
    have hs : (∑ r ∈ Finset.range (3 - 1),
        Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) B (3 - (r + 2))) *
          Module.finrank (ZMod 2)
            (Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) (r + 1))) = 1 := by
      rw [show (3 : ℕ) - 1 = 2 from rfl]
      rw [Finset.sum_range_succ (n := 1), Finset.sum_range_succ (n := 0),
        Finset.sum_range_zero]
      norm_num
      rw [hB1', hF1', hB0, hF2]
    rw [hE3', zero_add, hs] at hb
    exact hb
  · -- `n = 4`: the telescoped bound with the sum evaluated to `0`
    have hb := finrank_row0_bound S p e₀ 6 hS hFinB hFinF hF0 4 (by norm_num)
    have hs : (∑ r ∈ Finset.range (4 - 1),
        Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) B (4 - (r + 2))) *
          Module.finrank (ZMod 2)
            (Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) (r + 1))) = 0 := by
      rw [show (4 : ℕ) - 1 = 3 from rfl]
      rw [Finset.sum_range_succ (n := 2), Finset.sum_range_succ (n := 1),
        Finset.sum_range_succ (n := 0), Finset.sum_range_zero]
      norm_num
      rw [hF1', hB1', hF3']
      simp
    rw [hE4, hs] at hb
    simp only [add_zero] at hb
    exact hb

end Work.Pi6.EMM2
