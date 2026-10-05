import Mathlib
import Submission.Work.RPA3.Defs

namespace Work.RPA3

/-- Every `LagFamily` can be reparametrised in `τ` so that its embedding and Lagrangian conditions
hold for *all* `τ ∈ ℝ` (not only on `[0,1]`), without changing the `τ = 0` and `τ = 1` slices.

Construction: `ρ := Real.smoothTransition` (smooth, `ρ 0 = 0`, `ρ 1 = 1`, `0 ≤ ρ ≤ 1`), and
`L'.ℓ τ x t := L.ℓ (ρ τ) (x,t)`.  Then `ρ τ ∈ [0,1]` for every `τ`, so each field of
`LagFamilyAll` is the corresponding field of `L` at `ρ τ` (composition with the smooth `ρ` gives
`smooth`; `per`, `std`, `start`, `start_surj`, `symm` are pointwise unchanged; `inj`, `imm`, `lag`
hold for all `τ` because `ρ τ ∈ Icc 0 1`).  The slices at `τ = 0` and `τ = 1` are unchanged because
`ρ 0 = 0` and `ρ 1 = 1`. -/
theorem exists_reparam (L : Work.RPA3.LagFamily) :
    ∃ L' : Work.RPA3.LagFamilyAll, (∀ x t, L'.ℓ 1 (x, t) = L.ℓ 1 (x, t)) ∧
      (∀ x t, L'.ℓ 0 (x, t) = L.ℓ 0 (x, t)) := by
  have hmem : ∀ τ : ℝ, Real.smoothTransition τ ∈ Set.Icc (0 : ℝ) 1 := fun τ =>
    ⟨Real.smoothTransition.nonneg τ, Real.smoothTransition.le_one τ⟩
  refine ⟨
    { ℓ := fun τ xt => L.ℓ (Real.smoothTransition τ) xt
      smooth := L.smooth.comp
        (((Real.smoothTransition.contDiff (n := 8)).comp contDiff_fst).prodMk contDiff_snd)
      per := fun τ x t => L.per (Real.smoothTransition τ) x t
      inj := fun τ x t x' t' k h => L.inj (Real.smoothTransition τ) (hmem τ) x t x' t' k h
      imm := fun τ x t a b h => L.imm (Real.smoothTransition τ) (hmem τ) x t a b h
      lag := fun τ x t => L.lag (Real.smoothTransition τ) x t
      X0 := L.X0
      std := fun τ x t h => L.std (Real.smoothTransition τ) x t h
      start := fun x t => by
        simp only [Real.smoothTransition.zero]
        exact L.start x t
      start_surj := fun z hz => by
        obtain ⟨x, t, ht⟩ := L.start_surj z hz
        exact ⟨x, t, by simpa only [Real.smoothTransition.zero] using ht⟩
      symm := fun τ x t => L.symm (Real.smoothTransition τ) x t }, ?_, ?_⟩
  · intro x t
    simp only [Real.smoothTransition.one]
  · intro x t
    simp only [Real.smoothTransition.zero]

end Work.RPA3
