import Mathlib
import Submission.Work.MRMT.Found.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal Topology

namespace Work.MRMT.Found

/-! ## The `L²`-Cauchy property of `∂(F n)` on compact sets

The principal data `d : PrincipalData μ` carries the hypothesis that `∂(F n)` converges in
`L²` on every compact set (`dz_tendsto`, stated with `eLpNorm`).  The lemma here extracts the
Cauchy form of that statement for the *unnormalised* `lintegral` of `‖∂F n − ∂F m‖²`, which
is the form the limit construction downstream consumes.

The only bridge needed is that `∫⁻ ‖f‖ₑ ^ 2` is dominated by the *square* of the `L²`
seminorm; in the measurable case the two agree (this is `eLpNorm`'s defining formula with
`p = 2`, and `(x ^ (1/2)) ^ 2 = x`), and in the non-measurable case `eLpNorm = ⊤` makes the
inequality vacuous. -/

/-- The `lintegral` of `‖f‖ₑ ^ 2` is at most the square of the `L²` seminorm of `f`.

For an a.e. strongly measurable `f` this is an equality: `eLpNorm f 2 ν` is by definition
`(∫⁻ ‖f‖ₑ ^ 2) ^ (1/2)`, and squaring inverts the square root.  For a non-measurable `f` the
right hand side is `⊤` and everything is trivial.  (This direction — `lintegral ≤ square` —
is the one that needs no measurability.) -/
lemma lintegral_enorm_sq_le_eLpNorm_sq_two (f : ℂ → ℂ) (ν : Measure ℂ) :
    ∫⁻ z, ‖f z‖ₑ ^ 2 ∂ν ≤ (eLpNorm f (2 : ℝ≥0∞) ν) ^ 2 := by
  by_cases hf : AEStronglyMeasurable f ν
  · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
    simp only [ENNReal.toReal_ofNat]
    rw [show ((1 : ℝ) / 2) = ((2 : ℕ) : ℝ)⁻¹ by norm_num,
      ENNReal.rpow_inv_natCast_pow (by norm_num)]
    simp
  · rw [eLpNorm_of_not_aestronglyMeasurable hf]
    simp

/-- **Cauchy property of `∂(F n)` in `L²` on compact sets.**

Since `∂(F n)` converges to some `D` in `L²` on every compact `K`, the differences
`∂(F n) − ∂(F m)` have arbitrarily small `L²`-energy on `K`.  Concretely: for every `ε > 0`
there is `N` such that for all `n, m ≥ N` the `lintegral` of `‖∂(F n) − ∂(F m)‖²` over `K`
is at most `ofReal ε`.

The proof picks `η > 0` with `4η² ≤ ε` (e.g. `η = min 1 (ε/4)`), takes `N` beyond which
`eLpNorm (∂F n − D) 2 (volume.restrict K) ≤ ofReal η`, and combines the triangle inequality
for `eLpNorm` with the previous lemma:
`∫⁻_K ‖∂F n − ∂F m‖ₑ² ≤ (eLpNorm (∂F n − ∂F m))² ≤ (2η)² = 4η² ≤ ε`. -/
theorem dz_lintegral_cauchy {μ : ℂ → ℂ} (d : Work.MRMT.Found.PrincipalData μ) {K : Set ℂ}
    (hK : IsCompact K) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ z in K, ENNReal.ofReal ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z
        - Work.MRMT.dz ((d.Fn m) : ℂ → ℂ) z‖ ^ 2 ≤ ENNReal.ofReal ε := by
  intro ε hε
  -- the `L²` limit `D` of `∂(F n)`
  obtain ⟨D, hD⟩ := d.dz_tendsto
  -- the tolerance `η > 0` with `4η² ≤ ε`
  set η : ℝ := min 1 (ε / 4) with hηdef
  have hηpos : 0 < η := lt_min one_pos (by linarith)
  have hηle1 : η ≤ 1 := min_le_left _ _
  have hηle : η ≤ ε / 4 := min_le_right _ _
  have hηsq : η ^ 2 ≤ η := by nlinarith [hηpos, hηle1]
  have h4 : 4 * η ^ 2 ≤ ε := by nlinarith [hηsq, hηle]
  -- `∂(F n)` is eventually within `η` of `D` in `L²` on `K`
  have hev : ∀ᶠ n in Filter.atTop,
      eLpNorm (fun z => Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z - D z) (2 : ℝ≥0∞)
        (volume.restrict K) ≤ ENNReal.ofReal η :=
    (ENNReal.tendsto_nhds_zero.mp (hD K hK)) (ENNReal.ofReal η)
      (ENNReal.ofReal_pos.mpr hηpos)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N, fun n m hn hm => ?_⟩
  -- the **seminorm** Cauchy estimate
  have hsq := lintegral_enorm_sq_le_eLpNorm_sq_two
    (fun z => Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z - Work.MRMT.dz ((d.Fn m) : ℂ → ℂ) z)
    (volume.restrict K)
  have htri : eLpNorm (fun z => Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z
        - Work.MRMT.dz ((d.Fn m) : ℂ → ℂ) z)
      (2 : ℝ≥0∞) (volume.restrict K) ≤
      eLpNorm (fun z => Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z - D z) (2 : ℝ≥0∞)
        (volume.restrict K) +
      eLpNorm (fun z => Work.MRMT.dz ((d.Fn m) : ℂ → ℂ) z - D z) (2 : ℝ≥0∞)
        (volume.restrict K) := by
    have h := eLpNorm_sub_le (μ := volume.restrict K) (p := (2 : ℝ≥0∞))
      (f := fun z => Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z - D z)
      (g := fun z => Work.MRMT.dz ((d.Fn m) : ℂ → ℂ) z - D z) (by norm_num)
    have hfun : ((fun z => Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z - D z)
        - (fun z => Work.MRMT.dz ((d.Fn m) : ℂ → ℂ) z - D z))
        = fun z => Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z
            - Work.MRMT.dz ((d.Fn m) : ℂ → ℂ) z := by
      funext z
      simp only [Pi.sub_apply]
      ring
    rw [← hfun]
    exact h
  calc ∫⁻ z in K, ENNReal.ofReal ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z
        - Work.MRMT.dz ((d.Fn m) : ℂ → ℂ) z‖ ^ 2
      = ∫⁻ z, ‖(fun z => Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z
          - Work.MRMT.dz ((d.Fn m) : ℂ → ℂ) z) z‖ₑ ^ 2 ∂(volume.restrict K) := by simp
    _ ≤ (eLpNorm (fun z => Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z
          - Work.MRMT.dz ((d.Fn m) : ℂ → ℂ) z) (2 : ℝ≥0∞) (volume.restrict K)) ^ 2 := hsq
    _ ≤ (eLpNorm (fun z => Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z - D z) (2 : ℝ≥0∞)
            (volume.restrict K) +
          eLpNorm (fun z => Work.MRMT.dz ((d.Fn m) : ℂ → ℂ) z - D z) (2 : ℝ≥0∞)
            (volume.restrict K)) ^ 2 := by
        gcongr
    _ ≤ (ENNReal.ofReal η + ENNReal.ofReal η) ^ 2 := by
        gcongr
        · exact hN n hn
        · exact hN m hm
    _ = ENNReal.ofReal (4 * η ^ 2) := by
        rw [← ENNReal.ofReal_add hηpos.le hηpos.le,
          ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ η + η)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal h4

end Work.MRMT.Found
