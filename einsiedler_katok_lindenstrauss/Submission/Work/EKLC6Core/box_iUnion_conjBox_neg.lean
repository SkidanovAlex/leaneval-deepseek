import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.conjBox_nhds
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLProd.aDiag_nsmul
import Submission.Work.EKLContract.Lemmas.V_open_one

/-!
# `EKLC6Core.box_iUnion_conjBox_neg` — the conjugated boxes fill up `U`

For a horospherical subgroup `U ≤ SL₃(ℝ)` (`IsHoro U`) and an exponent vector `t` that
*contracts* the whole of `U` along the diagonal flow,

`aDiag tⁿ · u · (aDiag tⁿ)⁻¹ → 1`   for every `u ∈ U`,

the conjugated boxes `conjBox U (-n·t) = aDiag(-n t) · B₁^U · aDiag(n t)` exhaust `U`:

`⋃_{n ∈ ℕ} conjBox U (-(n • t)) = U`.

The mathematics is elementary.  Every `conjBox U s` is the image of `Box1 U ⊆ U` under
conjugation by `aDiag s`, and `IsHoro U` says that the diagonal group normalises `U`, so each
`conjBox U s` is contained in `U`.  Conversely, for `g ∈ U` the contraction hypothesis gives
`hₙ := aDiag tⁿ · g · (aDiag tⁿ)⁻¹ ∈ V 1` for all large `n`, hence `hₙ ∈ Box1 U`; and
conjugating back by `aDiag(-n t) = (aDiag tⁿ)⁻¹` recovers `g`, i.e. `g ∈ conjBox U (-(n • t))`.

This is the "big box" half of the geometry of the entropy contribution of Pisa 7.6/7.18: the
leafwise measures are normalised on `B₁^U`, and the large contracted boxes `conjBox U (-n t)`
grow to all of `U` (while dually `⋂ₙ conjBox U (n • t) = {1}`, `box_iInter_conjBox`).
-/

namespace Work.EKLC6Core

open Work.EKLContract

noncomputable section

/-! ## Elementary API for the boxes -/

/-- Every conjugated box is contained in the subgroup: `conjBox U s ⊆ U`. -/
theorem conjBox_subset_U {U : Subgroup SL3} (hU : IsHoro U) (s : Fin 3 → ℝ) :
    conjBox U s ⊆ (U : Set SL3) := by
  rintro g ⟨h, hh, rfl⟩
  exact hU.2.1 s h hh.1

/-- `aDiag` at the real multiple `(n : ℝ) • t` is the `n`-th power of `aDiag t`. -/
theorem aDiag_real_nsmul (t : Fin 3 → ℝ) (n : ℕ) :
    aDiag (((n : ℝ)) • t) = aDiag t ^ n := by
  rw [← Work.EKLProd.aDiag_nsmul t n]
  congr 1
  ext i
  simp [nsmul_eq_mul]

/-- The inverse statement: `aDiag (-((n : ℝ) • t)) = (aDiag t ^ n)⁻¹`. -/
theorem aDiag_neg_real_nsmul (t : Fin 3 → ℝ) (n : ℕ) :
    aDiag (-(((n : ℝ)) • t)) = (aDiag t ^ n)⁻¹ := by
  rw [← aDiag_inv_eq_neg, aDiag_real_nsmul]

/-! ## The exhaustion of `U` -/

theorem box_iUnion_conjBox_neg {U : Subgroup Work.EKLContract.SL3} (hU : Work.EKLContract.IsHoro U)
    {t : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1)) :
    (⋃ n : ℕ, Work.EKLC6Core.conjBox U (-(((n : ℝ)) • t))) = U := by
  refine Set.Subset.antisymm (fun g hg => ?_) (fun g hg => ?_)
  · rw [Set.mem_iUnion] at hg
    obtain ⟨n, hn⟩ := hg
    exact conjBox_subset_U hU _ hn
  · -- `V 1` is a neighbourhood of `1`, hence the contracting conjugates eventually lie in `Box1 U`
    have hVopen := Work.EKLContract.Lemmas.V_open_one 1 zero_lt_one
    have hV : V 1 ∈ nhds (1 : SL3) := hVopen.1.mem_nhds hVopen.2
    obtain ⟨n, hn⟩ : ∃ n : ℕ, aDiag t ^ n * g * (aDiag t ^ n)⁻¹ ∈ V 1 :=
      ((hcontr g hg).eventually_mem hV).exists
    rw [Set.mem_iUnion]
    refine ⟨n, ?_⟩
    rw [conjBox, conjBy, Set.mem_image]
    refine ⟨aDiag t ^ n * g * (aDiag t ^ n)⁻¹, ⟨?_, ?_⟩, ?_⟩
    · -- the conjugate stays in `U` (normalisation by the diagonal flow)
      have h := hU.2.1 (((n : ℝ)) • t) g hg
      rwa [aDiag_real_nsmul] at h
    · -- and lies in the normalising box `B₁^U`
      intro i j
      exact le_of_lt (hn i j)
    · -- conjugating back by `aDiag (-(n t)) = (aDiag t ^ n)⁻¹` recovers `g`
      rw [aDiag_neg_real_nsmul t n]
      group

end

end Work.EKLC6Core
