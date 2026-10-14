import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.windowExt_holder_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Spatial Hölder regularity of the two-sided time-extension `windowExt`

`windowExt ω S` glues the strip vorticity `ω` to its affine continuation with the endpoint
`∂ₜ`-slices below `0` and above `S` (`WindowExtDefs`).  The current file shows that, whenever the
strip bundle `BSAdmissibleStripFull` holds and the `∂ₜ`-slices are *x*-Hölder uniformly on the
strip (the extra hypothesis `hxH`), the extension is spatially Hölder with a single exponent and
constant, uniformly on the unit window `Ioo (t₀-1) (t₀+1)` around any `t₀`.

The mathematics is elementary: on each of the three time-regimes the extension is either a single
strip slice (globally `α`-Hölder) or an affine combination `ω(·,τ) + (t-τ) • ∂ₜω(·,τ)` of two
globally Hölder maps, and the extension is globally bounded by `M + Λ M₁`.  Combining the Hölder
bound valid for `‖a-b‖ ≤ 1` with the global bound via `‖a-b‖^e ≥ 1` for `‖a-b‖ ≥ 1` produces the
uniform constant.
-/

noncomputable section

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology

namespace Work.CoreResiduals.BiotSavart

/-- `HolderWith` in the `dist` form, rewritten as a norm inequality. -/
theorem holderWith_norm_sub_le {H : NNReal} {r : NNReal} {f : R3 → R3}
    (h : HolderWith H r f) (a b : R3) :
    ‖f a - f b‖ ≤ (H : ℝ) * ‖a - b‖ ^ (r : ℝ) := by
  have hd := h.dist_le a b
  simpa only [dist_eq_norm] using hd

/-- `rpow` is antitone on `(0,1]`: for `0 ≤ r ≤ 1` and `0 < e ≤ p` one has `r ^ p ≤ r ^ e`. -/
theorem rpow_le_rpow_of_le_one {r p e : ℝ} (he : 0 < e) (hep : e ≤ p) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) : r ^ p ≤ r ^ e := by
  rcases eq_or_lt_of_le hr0 with h | h
  · subst h
    rw [Real.zero_rpow (ne_of_gt (lt_of_lt_of_le he hep)), Real.zero_rpow (ne_of_gt he)]
  · exact Real.rpow_le_rpow_of_exponent_ge h hr1 hep

/-- The small-distance Hölder bound for an affine combination of two globally Hölder maps. -/
theorem add_smul_holder_small {f g : R3 → R3} {s A B p q e : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 < e) (hep : e ≤ p) (heq : e ≤ q)
    (hf : ∀ a b : R3, ‖f a - f b‖ ≤ A * ‖a - b‖ ^ p)
    (hg : ∀ a b : R3, ‖g a - g b‖ ≤ B * ‖a - b‖ ^ q) :
    ∀ a b : R3, ‖a - b‖ ≤ 1 →
      ‖(f a + s • g a) - (f b + s • g b)‖ ≤ (A + |s| * B) * ‖a - b‖ ^ e := by
  intro a b hab
  have hr0 : 0 ≤ ‖a - b‖ := norm_nonneg _
  calc ‖(f a + s • g a) - (f b + s • g b)‖
      = ‖(f a - f b) + s • (g a - g b)‖ := by
        simp only [sub_eq_add_neg, smul_add, smul_neg]; abel
    _ ≤ ‖f a - f b‖ + ‖s • (g a - g b)‖ := norm_add_le _ _
    _ = ‖f a - f b‖ + |s| * ‖g a - g b‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ A * ‖a - b‖ ^ p + |s| * (B * ‖a - b‖ ^ q) := by
        gcongr
        · exact hf a b
        · exact hg a b
    _ ≤ A * ‖a - b‖ ^ e + |s| * (B * ‖a - b‖ ^ e) := by
        have hp1 : ‖a - b‖ ^ p ≤ ‖a - b‖ ^ e := rpow_le_rpow_of_le_one he hep hr0 hab
        have hq1 : ‖a - b‖ ^ q ≤ ‖a - b‖ ^ e := rpow_le_rpow_of_le_one he heq hr0 hab
        have hA' : A * ‖a - b‖ ^ p ≤ A * ‖a - b‖ ^ e := mul_le_mul_of_nonneg_left hp1 hA
        have hB2 : B * ‖a - b‖ ^ q ≤ B * ‖a - b‖ ^ e := mul_le_mul_of_nonneg_left hq1 hB
        have hB' : |s| * (B * ‖a - b‖ ^ q) ≤ |s| * (B * ‖a - b‖ ^ e) :=
          mul_le_mul_of_nonneg_left hB2 (abs_nonneg s)
        linarith
    _ = (A + |s| * B) * ‖a - b‖ ^ e := by ring

/-- Combine a Hölder bound valid on `‖a-b‖ ≤ 1` with a global bound `D` into a single global
Hölder bound with exponent `e > 0` and constant `max K D`. -/
theorem le_max_mul_rpow_of_split {f : R3 → R3} {K D e : ℝ} (he : 0 < e) (hD : 0 ≤ D)
    (hsmall : ∀ a b : R3, ‖a - b‖ ≤ 1 → ‖f a - f b‖ ≤ K * ‖a - b‖ ^ e)
    (hbig : ∀ a b : R3, ‖f a - f b‖ ≤ D) :
    ∀ a b : R3, ‖f a - f b‖ ≤ max K D * ‖a - b‖ ^ e := by
  intro a b
  by_cases h : ‖a - b‖ ≤ 1
  · exact le_trans (hsmall a b h)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) e))
  · rw [not_le] at h
    have h1 : (1:ℝ) ≤ ‖a - b‖ ^ e := Real.one_le_rpow (le_of_lt h) (le_of_lt he)
    have hmax : 0 ≤ max K D := le_trans hD (le_max_right _ _)
    calc ‖f a - f b‖ ≤ D := hbig a b
      _ ≤ max K D := le_max_right _ _
      _ = max K D * 1 := (mul_one _).symm
      _ ≤ max K D * ‖a - b‖ ^ e := mul_le_mul_of_nonneg_left h1 hmax

/-- **Spatial Hölder regularity of the two-sided time-extension.**  Under the full strip bundle
`BSAdmissibleStripFull` and the uniform-in-time `x`-Hölder continuity of the `∂ₜ`-slices `hxH`,
the extension `windowExt ω S` is spatially Hölder with a single exponent and constant on the unit
window `Ioo (t₀-1) (t₀+1)` around any `t₀`. -/
theorem windowExt_holder_bound {α : NNReal} (hα : 0 < (α : ℝ)) {ω : R3 → ℝ → R3} {R S : ℝ}
    (hS : 0 < S) (hbun : BSAdmissibleStripFull α ω R S)
    (hxH : ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : R3, ∀ t ∈ Set.Icc (0:ℝ) S,
      ‖FiniteTimeSingularity.timeDeriv ω a t - FiniteTimeSingularity.timeDeriv ω b t‖
        ≤ C * ‖a - b‖ ^ c)
    (t₀ : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ t ∈ Set.Ioo (t₀ - 1) (t₀ + 1), ∀ a b : R3,
      ‖windowExt ω S a t - windowExt ω S b t‖ ≤ C * ‖a - b‖ ^ c := by
  obtain ⟨⟨hRpos, hsupp, hbdd, hholder, htholder, hmeas⟩, ⟨hdiff, hbd1, hmeas1⟩, hthH⟩ := hbun
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨H, hH⟩ := hholder
  obtain ⟨M₁, hM₁⟩ := hbd1
  obtain ⟨c, hcpos, C, hCnonneg, hxHx⟩ := hxH
  have hMnonneg : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_refl 0, le_of_lt hS⟩ (0 : R3))
  have hM₁nonneg : 0 ≤ M₁ := le_trans (norm_nonneg _) (hM₁ 0 ⟨le_refl 0, le_of_lt hS⟩ (0 : R3))
  have hHnonneg : (0:ℝ) ≤ (H:ℝ) := H.coe_nonneg
  set e : ℝ := min (α : ℝ) c with he_def
  have hepos : 0 < e := lt_min hα hcpos
  have heα : e ≤ (α : ℝ) := min_le_left _ _
  have hec : e ≤ c := min_le_right _ _
  have h0mem : (0:ℝ) ∈ Set.Icc 0 S := ⟨le_refl 0, le_of_lt hS⟩
  have hSmem : S ∈ Set.Icc (0:ℝ) S := ⟨le_of_lt hS, le_refl S⟩
  set Λ : ℝ := |t₀| + 1 + S with hΛ_def
  have hΛnonneg : 0 ≤ Λ := by rw [hΛ_def]; linarith [abs_nonneg t₀, hS]
  set Kx : ℝ := (H:ℝ) + Λ * C with hKx_def
  have hKxnonneg : 0 ≤ Kx := by
    rw [hKx_def]; exact add_nonneg hHnonneg (mul_nonneg hΛnonneg hCnonneg)
  set Mb : ℝ := M + Λ * M₁ with hMb_def
  have hMbnonneg : 0 ≤ Mb := by
    rw [hMb_def]; exact add_nonneg hMnonneg (mul_nonneg hΛnonneg hM₁nonneg)
  have hH0 : ∀ a b : R3, ‖ω a 0 - ω b 0‖ ≤ (H:ℝ) * ‖a - b‖ ^ (α:ℝ) :=
    fun a b => holderWith_norm_sub_le (hH 0 h0mem) a b
  have hHS : ∀ a b : R3, ‖ω a S - ω b S‖ ≤ (H:ℝ) * ‖a - b‖ ^ (α:ℝ) :=
    fun a b => holderWith_norm_sub_le (hH S hSmem) a b
  have hD0 : ∀ a b : R3,
      ‖FiniteTimeSingularity.timeDeriv ω a 0 - FiniteTimeSingularity.timeDeriv ω b 0‖
        ≤ C * ‖a - b‖ ^ c := fun a b => hxHx a b 0 h0mem
  have hDS : ∀ a b : R3,
      ‖FiniteTimeSingularity.timeDeriv ω a S - FiniteTimeSingularity.timeDeriv ω b S‖
        ≤ C * ‖a - b‖ ^ c := fun a b => hxHx a b S hSmem
  refine ⟨e, hepos, max Kx (2 * Mb), ?_⟩
  intro t ht a b
  -- global bound on `|t|` and `|t - S|` on the unit window
  have htabs : |t| ≤ Λ := by
    rw [hΛ_def]
    have h1 : |t| ≤ |t₀| + 1 :=
      abs_le.mpr ⟨by linarith [ht.1, neg_abs_le t₀], by linarith [ht.2, le_abs_self t₀]⟩
    linarith [hS]
  have htSabs : |t - S| ≤ Λ := by
    rw [hΛ_def, abs_sub_le_iff]
    constructor <;> linarith [ht.1, ht.2, le_abs_self t₀, neg_abs_le t₀, hS]
  -- global boundedness of the extension on the window
  have hBig : ∀ y : R3, ‖windowExt ω S y t‖ ≤ Mb := by
    intro y
    rcases lt_or_ge t 0 with ht0 | ht0
    · rw [windowExt_of_nonpos (le_of_lt ht0), hMb_def]
      calc ‖ω y 0 + t • FiniteTimeSingularity.timeDeriv ω y 0‖
          ≤ ‖ω y 0‖ + ‖t • FiniteTimeSingularity.timeDeriv ω y 0‖ := norm_add_le _ _
        _ = ‖ω y 0‖ + |t| * ‖FiniteTimeSingularity.timeDeriv ω y 0‖ := by
              rw [norm_smul, Real.norm_eq_abs]
        _ ≤ M + Λ * M₁ := by
              have h2 : |t| * ‖FiniteTimeSingularity.timeDeriv ω y 0‖ ≤ Λ * M₁ :=
                mul_le_mul htabs (hM₁ 0 h0mem y) (norm_nonneg _) hΛnonneg
              linarith [hM 0 h0mem y]
    · rcases lt_or_ge t S with htS | htS
      · rw [windowExt_of_mem_Icc ⟨ht0, le_of_lt htS⟩, hMb_def]
        linarith [hM t ⟨ht0, le_of_lt htS⟩ y, mul_nonneg hΛnonneg hM₁nonneg]
      · rw [windowExt_of_ge hS htS, hMb_def]
        calc ‖ω y S + (t - S) • FiniteTimeSingularity.timeDeriv ω y S‖
            ≤ ‖ω y S‖ + ‖(t - S) • FiniteTimeSingularity.timeDeriv ω y S‖ := norm_add_le _ _
          _ = ‖ω y S‖ + |t - S| * ‖FiniteTimeSingularity.timeDeriv ω y S‖ := by
                rw [norm_smul, Real.norm_eq_abs]
          _ ≤ M + Λ * M₁ := by
                have h2 : |t - S| * ‖FiniteTimeSingularity.timeDeriv ω y S‖ ≤ Λ * M₁ :=
                  mul_le_mul htSabs (hM₁ S hSmem y) (norm_nonneg _) hΛnonneg
                linarith [hM S hSmem y]
  have hbig2 : ∀ a b : R3, ‖windowExt ω S a t - windowExt ω S b t‖ ≤ 2 * Mb := by
    intro a b
    calc ‖windowExt ω S a t - windowExt ω S b t‖
        ≤ ‖windowExt ω S a t‖ + ‖windowExt ω S b t‖ := norm_sub_le _ _
      _ ≤ Mb + Mb := add_le_add (hBig a) (hBig b)
      _ = 2 * Mb := by ring
  -- the small-distance Hölder bound, by time-regime
  have hsmall : ∀ a b : R3, ‖a - b‖ ≤ 1 →
      ‖windowExt ω S a t - windowExt ω S b t‖ ≤ Kx * ‖a - b‖ ^ e := by
    intro a b hab
    rcases lt_or_ge t 0 with ht0 | ht0
    · have h := add_smul_holder_small
        (f := fun y : R3 => ω y 0) (g := fun y : R3 => FiniteTimeSingularity.timeDeriv ω y 0)
        (s := t) (A := (H:ℝ)) (B := C) (p := (α:ℝ)) (q := c) (e := e)
        hHnonneg hCnonneg hepos heα hec hH0 hD0 a b hab
      simp only [windowExt_of_nonpos (le_of_lt ht0)]
      refine le_trans h (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) e))
      rw [hKx_def]
      linarith [mul_le_mul_of_nonneg_right htabs hCnonneg]
    · rcases lt_or_ge t S with htS | htS
      · have h := holderWith_norm_sub_le (hH t ⟨ht0, le_of_lt htS⟩) a b
        simp only [windowExt_of_mem_Icc ⟨ht0, le_of_lt htS⟩]
        have hpe : ‖a - b‖ ^ (α:ℝ) ≤ ‖a - b‖ ^ e :=
          rpow_le_rpow_of_le_one hepos heα (norm_nonneg _) hab
        have h1 : (H:ℝ) * ‖a - b‖ ^ (α:ℝ) ≤ (H:ℝ) * ‖a - b‖ ^ e :=
          mul_le_mul_of_nonneg_left hpe hHnonneg
        have h2 : (H:ℝ) * ‖a - b‖ ^ e ≤ Kx * ‖a - b‖ ^ e :=
          mul_le_mul_of_nonneg_right (by rw [hKx_def]; linarith [mul_nonneg hΛnonneg hCnonneg])
            (Real.rpow_nonneg (norm_nonneg _) e)
        exact le_trans (le_trans h h1) h2
      · have h := add_smul_holder_small
          (f := fun y : R3 => ω y S) (g := fun y : R3 => FiniteTimeSingularity.timeDeriv ω y S)
          (s := t - S) (A := (H:ℝ)) (B := C) (p := (α:ℝ)) (q := c) (e := e)
          hHnonneg hCnonneg hepos heα hec hHS hDS a b hab
        simp only [windowExt_of_ge hS htS]
        refine le_trans h (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) e))
        rw [hKx_def]
        linarith [mul_le_mul_of_nonneg_right htSabs hCnonneg]
  exact le_max_mul_rpow_of_split hepos (by linarith [hMbnonneg]) hsmall hbig2 a b

end Work.CoreResiduals.BiotSavart
end
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.windowExt_localBdd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open Set

/-- **Local boundedness of the two-sided extension.**  On any bounded time window
`Ioo (t₀-1) (t₀+1)` the extension `windowExt ω S y ·` is uniformly bounded in `y`, with a bound
`M + (|t₀|+1+|S|)·|M₁|` built from the strip bound `M` on `ω` and the strip bound `M₁` on `∂ₜω`.

Indeed, on `Ioo (t₀-1) (t₀+1)` one has `|t| ≤ |t₀|+1`; below the strip the extension is
`ω y 0 + t • ∂ₜω(y,0)`, inside it is `ω y t`, and above it is
`ω y S + (t-S) • ∂ₜω(y,S)`, and each of the three terms is bounded by `M` resp.
`(|t₀|+1+|S|)·|M₁|` using the triangle inequality and `‖c • v‖ = |c| ‖v‖`. -/
theorem windowExt_localBdd {α : NNReal} {ω : R3 → ℝ → R3} {R S : ℝ}
    (hS : 0 < S) (hbun : BSAdmissibleStripFull α ω R S) (t₀ : ℝ) :
    ∃ M : ℝ, ∀ t ∈ Set.Ioo (t₀ - 1) (t₀ + 1), ∀ y : R3, ‖windowExt ω S y t‖ ≤ M := by
  obtain ⟨hb, htd, _htdh⟩ := hbun
  obtain ⟨_hR, _hsupp, hMb, _hH, _hN, _hmeas⟩ := hb
  obtain ⟨M, hM⟩ := hMb
  obtain ⟨_hdiff, hM₁b, _hmeas₁⟩ := htd
  obtain ⟨M₁, hM₁⟩ := hM₁b
  refine ⟨M + (|t₀| + 1 + |S|) * |M₁|, ?_⟩
  intro t ht y
  have hnn : (0 : ℝ) ≤ (|t₀| + 1 + |S|) * |M₁| :=
    mul_nonneg (by positivity) (abs_nonneg M₁)
  have hSnn : (0 : ℝ) ≤ |t₀| + 1 + |S| := by positivity
  -- `|t| ≤ |t₀| + 1` on the window
  have htB : |t| ≤ |t₀| + 1 := by
    have h1 : |t - t₀| < 1 := by
      rw [abs_lt]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    calc |t| = |(t - t₀) + t₀| := by ring_nf
      _ ≤ |t - t₀| + |t₀| := abs_add_le _ _
      _ ≤ |t₀| + 1 := by linarith
  have hb1 : ‖ω y 0‖ ≤ M := hM 0 ⟨le_refl 0, le_of_lt hS⟩ y
  have hb1S : ‖ω y S‖ ≤ M := hM S ⟨le_of_lt hS, le_refl S⟩ y
  have hb2 : ‖FiniteTimeSingularity.timeDeriv ω y 0‖ ≤ |M₁| :=
    le_trans (hM₁ 0 ⟨le_refl 0, le_of_lt hS⟩ y) (le_abs_self M₁)
  have hb2S : ‖FiniteTimeSingularity.timeDeriv ω y S‖ ≤ |M₁| :=
    le_trans (hM₁ S ⟨le_of_lt hS, le_refl S⟩ y) (le_abs_self M₁)
  rcases le_or_gt t 0 with hle | hlt
  · -- below the strip
    rw [windowExt_of_nonpos hle]
    have hmul : |t| * ‖FiniteTimeSingularity.timeDeriv ω y 0‖
        ≤ (|t₀| + 1 + |S|) * |M₁| := by
      calc |t| * ‖FiniteTimeSingularity.timeDeriv ω y 0‖
          ≤ (|t₀| + 1) * |M₁| :=
            mul_le_mul htB hb2 (norm_nonneg _) (by positivity)
        _ ≤ (|t₀| + 1 + |S|) * |M₁| :=
            mul_le_mul_of_nonneg_right (by linarith [abs_nonneg S]) (abs_nonneg M₁)
    calc ‖ω y 0 + t • FiniteTimeSingularity.timeDeriv ω y 0‖
        ≤ ‖ω y 0‖ + ‖t • FiniteTimeSingularity.timeDeriv ω y 0‖ := norm_add_le _ _
      _ = ‖ω y 0‖ + |t| * ‖FiniteTimeSingularity.timeDeriv ω y 0‖ := by
            rw [norm_smul, Real.norm_eq_abs]
      _ ≤ M + (|t₀| + 1 + |S|) * |M₁| := add_le_add hb1 hmul
  · by_cases h2 : t ≤ S
    · -- inside the strip
      rw [windowExt_of_mem_Icc ⟨le_of_lt hlt, h2⟩]
      exact le_trans (hM t ⟨le_of_lt hlt, h2⟩ y) (le_add_of_nonneg_right hnn)
    · -- above the strip
      rw [windowExt_of_ge hS (le_of_lt (lt_of_not_ge h2))]
      have h1 : |t - S| ≤ |t₀| + 1 + |S| := by
        calc |t - S| ≤ |t| + |S| := abs_sub _ _
          _ ≤ |t₀| + 1 + |S| := by linarith
      have hmul : |t - S| * ‖FiniteTimeSingularity.timeDeriv ω y S‖
          ≤ (|t₀| + 1 + |S|) * |M₁| :=
        mul_le_mul h1 hb2S (norm_nonneg _) hSnn
      calc ‖ω y S + (t - S) • FiniteTimeSingularity.timeDeriv ω y S‖
          ≤ ‖ω y S‖ + ‖(t - S) • FiniteTimeSingularity.timeDeriv ω y S‖ := norm_add_le _ _
        _ = ‖ω y S‖ + |t - S| * ‖FiniteTimeSingularity.timeDeriv ω y S‖ := by
              rw [norm_smul, Real.norm_eq_abs]
        _ ≤ M + (|t₀| + 1 + |S|) * |M₁| := add_le_add hb1S hmul

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.FTS.Regularity.clockBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Regularity

/-- **Uniform bounds on the clock and its first-order combinations.**  On the fake-time strip
`[0,S]` the amplitude `A` and the scaling `B` are bounded away from `0` and their derivatives are
bounded, so all four quantities appearing in the dynamic-rescaling chain rule —
`A⁻¹`, `A'/A²`, `B⁻¹`, `B'/B` — are uniformly bounded by a single constant

  `M = max (max a₀⁻¹ b₀⁻¹) (max (|a₂|/a₀²) (|b₂|/b₀))`,

where `a₀`/`b₀` are the positive lower bounds of `A`/`B` and `a₂`/`b₂` the bounds on
`|A'|`/`|B'|`.  This is the elementary input of the time-Hölder estimates for `∂_τω`. -/
theorem clockBounds {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg α S A B g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S,
      |(A τ)⁻¹| ≤ M ∧ |deriv A τ / (A τ) ^ 2| ≤ M ∧ |(B τ)⁻¹| ≤ M ∧
        |deriv B τ / B τ| ≤ M := by
  obtain ⟨a₀, a₁, ha₀, ha⟩ := h.hAb
  obtain ⟨b₀, b₁, hb₀, hb⟩ := h.hBb
  obtain ⟨a₂, ha₂⟩ := h.hAd
  obtain ⟨b₂, hb₂⟩ := h.hBd
  refine ⟨max (max a₀⁻¹ b₀⁻¹) (max (|a₂| / a₀ ^ 2) (|b₂| / b₀)), ?_, ?_⟩
  · have h1 : 0 ≤ a₀⁻¹ := inv_nonneg.mpr ha₀.le
    exact le_trans h1 (le_trans (le_max_left a₀⁻¹ b₀⁻¹)
      (le_max_left (max a₀⁻¹ b₀⁻¹) (max (|a₂| / a₀ ^ 2) (|b₂| / b₀))))
  · intro τ hτ
    have hApos : 0 < A τ := h.hA τ hτ
    have hBpos : 0 < B τ := h.hB τ hτ
    have hAle : a₀ ≤ A τ := (ha τ hτ).1
    have hBle : b₀ ≤ B τ := (hb τ hτ).1
    have hP : |(A τ)⁻¹| ≤ a₀⁻¹ := by
      rw [abs_inv, abs_of_pos hApos, inv_le_inv₀ hApos ha₀]
      exact hAle
    have hQ : |(B τ)⁻¹| ≤ b₀⁻¹ := by
      rw [abs_inv, abs_of_pos hBpos, inv_le_inv₀ hBpos hb₀]
      exact hBle
    have hR : |deriv A τ / (A τ) ^ 2| ≤ |a₂| / a₀ ^ 2 := by
      rw [abs_div, abs_of_nonneg (sq_nonneg (A τ))]
      exact div_le_div₀ (abs_nonneg a₂) (le_trans (ha₂ τ hτ) (le_abs_self a₂))
        (pow_pos ha₀ 2) (pow_le_pow_left₀ ha₀.le hAle 2)
    have hT : |deriv B τ / B τ| ≤ |b₂| / b₀ := by
      rw [abs_div, abs_of_pos hBpos]
      exact div_le_div₀ (abs_nonneg b₂) (le_trans (hb₂ τ hτ) (le_abs_self b₂)) hb₀ hBle
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact le_trans hP (le_trans (le_max_left a₀⁻¹ b₀⁻¹)
        (le_max_left (max a₀⁻¹ b₀⁻¹) (max (|a₂| / a₀ ^ 2) (|b₂| / b₀))))
    · exact le_trans hR (le_trans (le_max_left (|a₂| / a₀ ^ 2) (|b₂| / b₀))
        (le_max_right (max a₀⁻¹ b₀⁻¹) (max (|a₂| / a₀ ^ 2) (|b₂| / b₀))))
    · exact le_trans hQ (le_trans (le_max_right a₀⁻¹ b₀⁻¹)
        (le_max_left (max a₀⁻¹ b₀⁻¹) (max (|a₂| / a₀ ^ 2) (|b₂| / b₀))))
    · exact le_trans hT (le_trans (le_max_right (|a₂| / a₀ ^ 2) (|b₂| / b₀))
        (le_max_right (max a₀⁻¹ b₀⁻¹) (max (|a₂| / a₀ ^ 2) (|b₂| / b₀))))

end Work.FTS.Regularity
end
-- ===== merged: Submission.Work.FTS.Regularity.clockLipschitz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Regularity

/-- **The self-similar clock `B` is Lipschitz on the fake-time strip `[0,S]`.**

`RegPkg` makes `B` differentiable on `[0,S]` with bounded `deriv`; the mean value theorem on the
convex interval `[0,S]` then turns that bound into a global Lipschitz constant
`K = max b₂ 0`, where `b₂` bounds `deriv B`.  (The `max` with `0` is what makes `K` nonnegative
regardless of the sign of the supplied bound.) -/
theorem clockLipschitz {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg α S A B g) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      |B τ - B τ'| ≤ K * |τ - τ'| := by
  obtain ⟨b₂, hb₂⟩ := h.hBd
  refine ⟨max b₂ 0, le_max_right _ _, fun τ hτ τ' hτ' => ?_⟩
  have hdiff : ∀ x ∈ Set.Icc (0 : ℝ) S, DifferentiableAt ℝ B x :=
    fun x hx => (h.hBdiff x hx).differentiableAt
  have hbound : ∀ x ∈ Set.Icc (0 : ℝ) S, ‖deriv B x‖ ≤ max b₂ 0 := fun x hx => by
    rw [Real.norm_eq_abs]
    exact le_trans (hb₂ x hx) (le_max_left _ _)
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Icc 0 S) hτ' hτ
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  simpa [abs_sub_comm] using hmvt

end Work.FTS.Regularity
end
-- ===== merged: Submission.Work.FTS.Regularity.dtgZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Regularity

theorem dtgZero {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg α S A B g) :
    ∃ L : ℝ, 0 < L ∧ ∀ z θ τ : ℝ, L < z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      deriv (fun s => g z θ s) τ = 0 := by
  obtain ⟨L, hLpos, hL⟩ := h.hsupp
  refine ⟨L, hLpos, fun z θ τ hz _ hτ => ?_⟩
  -- The full profile vanishes at every time of the strip above the support radius `L`, and the
  -- leading profile `F_*` is time-independent, so `s ↦ g z θ s` is constant on `[0,S]`.
  refine deriv_eq_zero_of_const_on_Icc h.hS ?_ τ hτ
  intro s hs t ht
  have h1 : Work.Construction.Fstar (pExp α) z θ + g z θ s = 0 := hL s hs z θ hz.le
  have h2 : Work.Construction.Fstar (pExp α) z θ + g z θ t = 0 := hL t ht z θ hz.le
  linarith

end Work.FTS.Regularity
end
-- ===== merged: Submission.Work.FTS.Regularity.dzProfFullZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter Topology

namespace Work.FTS.Regularity

theorem dzProfFullZero {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg α S A B g) :
    ∃ L : ℝ, 0 < L ∧ ∀ z θ τ : ℝ, L < z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      deriv (fun z' => profFull α g z' θ τ) z = 0 := by
  obtain ⟨L, hLpos, hL⟩ := h.hsupp
  refine ⟨L, hLpos, fun z θ τ hz _ hτ => ?_⟩
  have hev : (fun z' => profFull α g z' θ τ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show z ∈ Set.Ioi L from hz)] with z' hz'
    exact hL τ hτ z' θ hz'.le
  rw [hev.deriv_eq]
  simp

end Work.FTS.Regularity
end
-- ===== merged: Submission.Work.FTS.Regularity.physVort_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set

namespace Work.FTS.Regularity

/-- The azimuthal vector field `e_θ` is a unit vector, and `0` on the axis (`radial x = 0`). -/
theorem norm_eTheta_le_one (x : R3) : ‖Work.Cyl.eTheta x‖ ≤ 1 := by
  by_cases h : Work.Cyl.radial x = 0
  · simp [Work.Cyl.eTheta, h]
  · rw [Work.Cyl.norm_eTheta x h]

/-- The polar angle `θ(x) = arctan(x₃/r)` satisfies `|θ(x)| ∈ [0,π/2]`. -/
theorem abs_theta_mem_Iθ (y : R3) : |Work.Cyl.theta y| ∈ Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ, Set.mem_Icc]
  have h := Real.arctan_mem_Ioo (Work.Cyl.axial y / Work.Cyl.radial y)
  rw [Work.Cyl.theta]
  exact ⟨abs_nonneg _, le_of_lt (abs_lt.mpr ⟨h.1, h.2⟩)⟩

/-- **Pointwise bound of the self-similar profile.**  For `z ≥ 0`, `|θ| ∈ Iθ` and `τ` in the
strip, `|F(z,θ,τ)| ≤ 20·(3α) + N`, where `N` bounds the perturbation `g`. -/
theorem abs_profile_le {α S N : ℝ} {g : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hN : ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S → |g z θ τ| ≤ N)
    {z θ τ : ℝ} (hz : 0 ≤ z) (hθ : |θ| ∈ Work.Spaces.Iθ) (hτ : τ ∈ Set.Icc 0 S) :
    |Work.ConstructionInstance.profile (pExp α) (gSlice g τ) z θ| ≤ 20 * pExp α + N := by
  have hp : 0 < pExp α := pExp_pos hα
  have hp1 : pExp α ≤ 1 := pExp_le_one hα13
  have key : ∀ θ' ∈ Work.Spaces.Iθ,
      |Work.Construction.Fstar (pExp α) z θ' + g z θ' τ| ≤ 20 * pExp α + N := by
    intro θ' hθ'
    have h1 := Work.ConstructionInstance.Fstar_abs_le hp hp1 hz hθ'
    have hp3 : 0 ≤ pExp α / 3 := (div_pos hp (by norm_num)).le
    have hG1 := Work.ConstructionInstance.Gamma_le_one (β := pExp α / 3) hp3 hθ'
    have hG0 := Work.ConstructionInstance.Gamma_nonneg (β := pExp α / 3) hθ'
    have h2 : 20 * pExp α * Work.ConstructionInstance.Gamma (pExp α / 3) θ'
        ≤ 20 * pExp α := by nlinarith
    have h3 := hN z θ' τ hz hθ' hτ
    calc |Work.Construction.Fstar (pExp α) z θ' + g z θ' τ|
        ≤ |Work.Construction.Fstar (pExp α) z θ'| + |g z θ' τ| := abs_add_le _ _
      _ ≤ 20 * pExp α + N := add_le_add (le_trans h1 h2) h3
  rw [Work.ConstructionInstance.profile]
  split_ifs with h
  · exact key θ (by simpa [abs_of_nonneg h] using hθ)
  · rw [abs_neg]
    exact key (-θ) (by simpa [abs_of_neg (not_le.mp h)] using hθ)

/-- **THE PHYSICAL VORTICITY IS UNIFORMLY BOUNDED ON THE STRIP.** -/
theorem physVort_bound {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.Regularity.RegPkg α S A B g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ y : Work.FTS.Regularity.R3,
      ‖Work.FTS.Regularity.physVort α A B g y τ‖ ≤ M := by
  obtain ⟨a₀, a₁, ha₀, hA⟩ := h.hAb
  obtain ⟨N, hN⟩ := h.hg
  have hN0 : 0 ≤ N := hN.1
  have hpN : 0 ≤ 20 * pExp α + N := by
    have hp := pExp_pos h.hα
    linarith
  refine ⟨(1 / a₀) * (20 * pExp α + N), by positivity, fun τ hτ y => ?_⟩
  have hAτ : 0 < A τ := h.hA τ hτ
  have hBτ : 0 < B τ := h.hB τ hτ
  have hz0 : 0 ≤ Work.Cyl.rho y ^ pExp α / B τ :=
    div_nonneg (Real.rpow_nonneg (Work.Cyl.rho_nonneg y) _) hBτ.le
  have hprof := abs_profile_le h.hα h.hα13
    (fun z θ σ hz hθ hσ => hN.abs_le hz hθ hσ) hz0 (abs_theta_mem_Iθ y) hτ
  have hAinv : |(A τ)⁻¹| ≤ 1 / a₀ := by
    rw [abs_of_pos (inv_pos.mpr hAτ), one_div]
    exact (inv_le_inv₀ hAτ ha₀).mpr (hA τ hτ).1
  have he : ‖Work.Cyl.eTheta y‖ ≤ 1 := norm_eTheta_le_one y
  have hinner : |Work.ConstructionInstance.profile (pExp α) (gSlice g τ)
        (Work.Cyl.rho y ^ pExp α / B τ) (Work.Cyl.theta y)| * ‖Work.Cyl.eTheta y‖
      ≤ 20 * pExp α + N := by
    calc |Work.ConstructionInstance.profile (pExp α) (gSlice g τ)
          (Work.Cyl.rho y ^ pExp α / B τ) (Work.Cyl.theta y)| * ‖Work.Cyl.eTheta y‖
        ≤ (20 * pExp α + N) * 1 :=
          mul_le_mul hprof he (norm_nonneg _) hpN
      _ = 20 * pExp α + N := mul_one _
  calc ‖Work.FTS.Regularity.physVort α A B g y τ‖
      = ‖(A τ)⁻¹ • (Work.ConstructionInstance.profile (pExp α) (gSlice g τ)
            (Work.Cyl.rho y ^ pExp α / B τ) (Work.Cyl.theta y) • Work.Cyl.eTheta y)‖ := by
        rw [physVort_apply, Work.ConstructionInstance.omegaSz_apply]
    _ = |(A τ)⁻¹| * (|Work.ConstructionInstance.profile (pExp α) (gSlice g τ)
            (Work.Cyl.rho y ^ pExp α / B τ) (Work.Cyl.theta y)| * ‖Work.Cyl.eTheta y‖) := by
        simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ (1 / a₀) * (20 * pExp α + N) :=
        mul_le_mul hAinv hinner (by positivity) (by positivity)

end Work.FTS.Regularity
end
end
-- ===== merged: Submission.Work.FTS.Regularity.physVort_hasDerivAt_and_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology
open scoped Topology

namespace Work.FTS.Regularity

/-- `|a + b| ≤ |a| + |b|` for reals. -/
private theorem abs_add_le_aux_prv {a b : ℝ} : |a + b| ≤ |a| + |b| := by
  simpa [Real.norm_eq_abs] using norm_add_le a b

/-- The polar angle satisfies `|θ(x)| ∈ [0,π/2]`. -/
private theorem abs_theta_mem_Iθ_aux (y : R3) : |Work.Cyl.theta y| ∈ Work.Spaces.Iθ := by
  refine ⟨abs_nonneg _, ?_⟩
  rw [abs_le]
  rw [Work.Cyl.theta]
  exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _), le_of_lt (Real.arctan_lt_pi_div_two _)⟩

/-- The azimuthal frame vector is a unit vector (and `0` on the axis). -/
private theorem norm_eTheta_le_one_aux (x : R3) : ‖Work.Cyl.eTheta x‖ ≤ 1 := by
  by_cases h : Work.Cyl.radial x = 0
  · rw [Work.Cyl.eTheta, h, div_zero, zero_smul, norm_zero]
    norm_num
  · rw [Work.Cyl.norm_eTheta x h]

/-! ## Auxiliary objects for the physical vorticity's time derivative

The physical vorticity is `ω(x,τ) = A(τ)⁻¹ • (F(ρ(x)^{3α}/B(τ), θ(x), τ) • e_θ(x))`, where
`F = F_* + g = profFull` and the profile is extended oddly in `θ`.  We record (i) the odd
extension `profOdd` of `profFull` and its identification with `ConstructionInstance.profile`,
(ii) the resulting product form of `physVort`, (iii) the `z`-derivative box of `F_*`, and
(iv) the two chain rules (in `z` and along the curve `s ↦ (ρ^{3α}/B(s), s)`). -/

/-- The odd extension in `θ` of the full profile `F = F_* + g`. -/
def profOdd (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (z θ τ : ℝ) : ℝ :=
  if 0 ≤ θ then profFull α g z θ τ else -profFull α g z (-θ) τ

/-- `ConstructionInstance.profile (pExp α) (gSlice g τ)` is the odd extension of `profFull`. -/
theorem profile_eq_profOdd (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ z θ : ℝ) :
    Work.ConstructionInstance.profile (pExp α) (gSlice g τ) z θ = profOdd α g z θ τ := by
  by_cases hθ : 0 ≤ θ
  · rw [Work.ConstructionInstance.profile_of_nonneg hθ, profOdd, if_pos hθ]
    rfl
  · rw [Work.ConstructionInstance.profile_of_neg hθ, profOdd, if_neg hθ]
    simp

/-- **Product form of the physical vorticity**: `ω(x,τ) = A(τ)⁻¹ • (F(z,θ,τ) • e_θ(x))` with
`z = ρ(x)^{3α}/B(τ)`, `θ = θ(x)` and the odd extension of the full profile. -/
theorem physVort_eq_smul (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (x : R3) (τ : ℝ) :
    physVort α A B g x τ
      = (A τ)⁻¹ • (profOdd α g (Work.Cyl.rho x ^ pExp α / B τ) (Work.Cyl.theta x) τ
          • Work.Cyl.eTheta x) := by
  rw [physVort_apply, Work.ConstructionInstance.omegaSz_apply, profile_eq_profOdd]

/-- **The `z`-derivative box of `F_*`**: `|∂_zF_*(z,θ)| ≤ 20p` for `0 < p ≤ 1`, `z ≥ 0` and
`θ ∈ Iθ`.  (`∂_zF_* = p(Γ(θ)/c(p))·2(1-z)/(1+z)³`, `Γ/c ≤ 10` and the rational factor is `≤ 2`
in absolute value on `z ≥ 0`.) -/
theorem pzFstar_abs_le_aux {p z θ : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.pz (Work.Construction.Fstar p) z θ| ≤ 20 * p := by
  have hc := (Work.Spaces.c_bounds p hp hp1).1
  have hcpos : 0 < Work.Spaces.c p := by linarith
  have hG0 : 0 ≤ Work.Spaces.Gam p θ := (Work.Spaces.Gam_bounds p θ hp hθ).1
  have hDz : Work.Spaces.pz (Work.Construction.Fstar p) z θ
      = p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * (2 * (1 - z) / (1 + z) ^ 3) := by
    have hfun : (fun z' => Work.Construction.Fstar p z' θ)
        = fun z' => (p * (Work.Spaces.Gam p θ / Work.Spaces.c p)) * Work.FM.Fstar z' := by
      funext z'; rw [Work.Construction.Fstar]
    rw [Work.Spaces.pz, hfun, deriv_const_mul_field, Work.FM.deriv_Fstar z (by linarith)]
  have hgb0 : 0 ≤ Work.Spaces.Gam p θ / Work.Spaces.c p := div_nonneg hG0 hcpos.le
  have hgle : Work.Spaces.Gam p θ / Work.Spaces.c p ≤ 10 := by
    rw [div_le_iff₀ hcpos]; nlinarith [(Work.Spaces.Gam_bounds p θ hp hθ).2]
  have hfrac : |2 * (1 - z) / (1 + z) ^ 3| ≤ 2 := by
    have h1z : (0 : ℝ) < (1 + z) ^ 3 := by positivity
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos h1z,
      div_le_iff₀ h1z]
    have h3 : |1 - z| ≤ (1 + z) ^ 3 := by
      have h4 : |1 - z| ≤ 1 + z := by rw [abs_le]; constructor <;> linarith
      have h5 : (1 : ℝ) ≤ 1 + z := by linarith
      nlinarith [sq_nonneg (1 + z), h5]
    linarith
  rw [hDz, abs_mul, abs_mul, abs_of_nonneg hp.le, abs_of_nonneg hgb0]
  calc p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * |2 * (1 - z) / (1 + z) ^ 3|
      ≤ p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * 2 :=
        mul_le_mul_of_nonneg_left hfrac (mul_nonneg hp.le hgb0)
    _ ≤ p * 10 * 2 := by
        have h : p * (Work.Spaces.Gam p θ / Work.Spaces.c p) ≤ p * 10 :=
          mul_le_mul_of_nonneg_left hgle hp.le
        linarith
    _ = 20 * p := by ring

/-! ### The two chain rules -/

/-- **Chain rule for the perturbation along a curve.**  If `G : ℝ × ℝ → ℝ` is `C¹` on the open
strip `Ioi(-1) ×ˢ Ioo(-1)(S+1)` and `zfun` has derivative `z'` at `τ`, then
`s ↦ g (zfun s) θ s` (= `G (zfun s, s)` with `G q = g q.1 θ q.2`) has derivative
`z'·∂_zg + ∂_τg` at `τ`. -/
theorem gComp_hasDerivAt_aux {g : ℝ → ℝ → ℝ → ℝ} {θ S τ z' : ℝ} (_hθ : θ ∈ Work.Spaces.Iθ)
    (hcont : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hτ : τ ∈ Set.Ioo (-1) (S + 1)) {zfun : ℝ → ℝ} (hz : -1 < zfun τ)
    (hzfun : HasDerivAt zfun z' τ) :
    HasDerivAt (fun s => g (zfun s) θ s)
      (z' * Work.Spaces.pz (gSlice g τ) (zfun τ) θ
        + deriv (fun t => g (zfun τ) θ t) τ) τ := by
  set G : ℝ × ℝ → ℝ := fun q => g q.1 θ q.2 with hGdef
  have hopen : IsOpen (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (S + 1)) :=
    (isOpen_Ioi : IsOpen (Set.Ioi (-1 : ℝ))).prod
      (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) (S + 1)))
  have hmem : (zfun τ, τ) ∈ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1) := ⟨hz, hτ⟩
  have hnhds : (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)) ∈ 𝓝 (zfun τ, τ) :=
    hopen.mem_nhds (x := (zfun τ, τ)) hmem
  have hdiff : DifferentiableAt ℝ G (zfun τ, τ) :=
    (hcont.contDiffAt hnhds).differentiableAt (by norm_num)
  have hF : HasFDerivAt G (fderiv ℝ G (zfun τ, τ)) (zfun τ, τ) := hdiff.hasFDerivAt
  set L : ℝ × ℝ →L[ℝ] ℝ := fderiv ℝ G (zfun τ, τ) with hLdef
  have hcurve : HasDerivAt (fun s : ℝ => (zfun s, s)) ((z', (1 : ℝ)) : ℝ × ℝ) τ :=
    hzfun.prodMk (hasDerivAt_id τ)
  have hcomp : HasDerivAt (G ∘ fun s : ℝ => (zfun s, s)) (L (z', 1)) τ :=
    hF.comp_hasDerivAt (f := fun s : ℝ => (zfun s, s)) τ hcurve
  have hcomp' : HasDerivAt (fun s => g (zfun s) θ s) (L (z', 1)) τ := by
    simpa [hGdef, Function.comp_def] using hcomp
  -- the two partial derivatives, identified with `L (1,0)` and `L (0,1)`
  have hL1 : L (1, 0) = Work.Spaces.pz (gSlice g τ) (zfun τ) θ := by
    have h := hF.comp_hasDerivAt (f := fun s : ℝ => (s, τ)) (zfun τ)
      (HasDerivAt.prodMk (hasDerivAt_id (zfun τ)) (hasDerivAt_const (zfun τ) τ))
    have hd : deriv (fun s => G (s, τ)) (zfun τ) = L (1, 0) := h.deriv
    have hev : deriv (fun s => G (s, τ)) (zfun τ)
        = Work.Spaces.pz (gSlice g τ) (zfun τ) θ := by
      simp [hGdef, Work.Spaces.pz]
    exact hd.symm.trans hev
  have hL2 : L (0, 1) = deriv (fun t => g (zfun τ) θ t) τ := by
    have h := hF.comp_hasDerivAt (f := fun s : ℝ => (zfun τ, s)) τ
      (HasDerivAt.prodMk (hasDerivAt_const τ (zfun τ)) (hasDerivAt_id τ))
    have hd : deriv ((fun q : ℝ × ℝ => g q.1 θ q.2) ∘ fun s : ℝ => (zfun τ, s)) τ
        = L (0, 1) := h.deriv
    simpa [hGdef, Function.comp_def] using hd.symm
  have hval : L (z', 1) = z' * Work.Spaces.pz (gSlice g τ) (zfun τ) θ
      + deriv (fun t => g (zfun τ) θ t) τ := by
    have hsplit : ((z', (1 : ℝ)) : ℝ × ℝ) = z' • ((1, 0) : ℝ × ℝ) + (1 : ℝ) • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    rw [hsplit, map_add, map_smul, map_smul, hL1, hL2]
    simp
  rw [hval] at hcomp'
  exact hcomp'

/-- **The `z`-derivative of the full profile splits.**  If `(z',τ) ↦ g z' θ τ` is `C¹` on the
open strip, then `∂_z(F_* + g) = ∂_zF_* + ∂_zg` for `z > -1`. -/
theorem profFull_deriv_z_aux {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {θ z τ : ℝ}
    (hcont : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hz : -1 < z) (hτ : τ ∈ Set.Ioo (-1) (S + 1)) :
    deriv (fun z' => profFull α g z' θ τ) z
      = Work.Spaces.pz (Work.Construction.Fstar (pExp α)) z θ
        + Work.Spaces.pz (gSlice g τ) z θ := by
  set G : ℝ × ℝ → ℝ := fun q => g q.1 θ q.2 with hGdef
  have hopen : IsOpen (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (S + 1)) :=
    (isOpen_Ioi : IsOpen (Set.Ioi (-1 : ℝ))).prod
      (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) (S + 1)))
  have hmem : (z, τ) ∈ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1) := ⟨hz, hτ⟩
  have hnhds : (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)) ∈ 𝓝 (z, τ) :=
    hopen.mem_nhds (x := (z, τ)) hmem
  have hdiff : DifferentiableAt ℝ G (z, τ) :=
    (hcont.contDiffAt hnhds).differentiableAt (by norm_num)
  have hGdiff : DifferentiableAt ℝ (fun z' => g z' θ τ) z := by
    have hp : DifferentiableAt ℝ (fun z' : ℝ => (z', τ)) z := by fun_prop
    simpa [hGdef, Function.comp_def] using hdiff.comp z hp
  have hF : HasDerivAt (fun z' => Work.Construction.Fstar (pExp α) z' θ)
      (Work.Spaces.pz (Work.Construction.Fstar (pExp α)) z θ) z :=
    Work.ConstructionInstance.hasDerivAt_Fstar_z z θ hz
  have hG : HasDerivAt (fun z' => g z' θ τ) (deriv (fun z' => g z' θ τ) z) z :=
    hGdiff.hasDerivAt
  have hsum := hF.add hG
  have hfun : (fun z' => profFull α g z' θ τ)
      = fun z' => Work.Construction.Fstar (pExp α) z' θ + g z' θ τ := by
    funext z'; rw [profFull_apply]
  have hval : Work.Spaces.pz (gSlice g τ) z θ = deriv (fun z' => g z' θ τ) z := rfl
  rw [hfun, hval]
  exact hsum.deriv

/-! ### The bookkeeping functions of the derivative -/

/-- The slope of the self-similar variable `s ↦ ρ^{3α}/B(s)` at time `τ`. -/
def zSlope (α : ℝ) (B : ℝ → ℝ) (ρ τ : ℝ) : ℝ :=
  -(ρ ^ pExp α * deriv B τ / (B τ) ^ 2)

/-- The `z`-derivative of the full profile `F = F_* + g` at a `τ`-slice, written as the sum of
the two summands' `z`-derivatives. -/
def pzProf (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (z θ τ : ℝ) : ℝ :=
  Work.Spaces.pz (Work.Construction.Fstar (pExp α)) z θ + Work.Spaces.pz (gSlice g τ) z θ

/-- The `τ`-derivative of the odd extension of the profile along the curve
`s ↦ (ρ^{3α}/B(s), s)`, as a function of `(ρ, θ, τ)`. -/
def dProfOdd (α : ℝ) (B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (ρ θ τ : ℝ) : ℝ :=
  if 0 ≤ θ then zSlope α B ρ τ * pzProf α g (ρ ^ pExp α / B τ) θ τ
      + deriv (fun t => g (ρ ^ pExp α / B τ) θ t) τ
  else -(zSlope α B ρ τ * pzProf α g (ρ ^ pExp α / B τ) (-θ) τ
      + deriv (fun t => g (ρ ^ pExp α / B τ) (-θ) t) τ)

/-- The value of `∂_τω(x,τ)`. -/
def vortDt (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (x : R3) (τ : ℝ) : R3 :=
  (A τ)⁻¹ • (dProfOdd α B g (Work.Cyl.rho x) (Work.Cyl.theta x) τ • Work.Cyl.eTheta x)
    + (-(deriv A τ) / (A τ) ^ 2) • (profOdd α g (Work.Cyl.rho x ^ pExp α / B τ)
        (Work.Cyl.theta x) τ • Work.Cyl.eTheta x)

/-! ### The bound on the profile and its two derivatives -/

/-- `|F(z,θ,τ)| ≤ 20·3α + Ng` on the domain. -/
private theorem profFull_abs_le_aux {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {Ng : ℝ}
    (hp : 0 < pExp α) (hp1 : pExp α ≤ 1) (hNg : Jet α S Ng g) {z θ τ : ℝ} (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) (hτ : τ ∈ Set.Icc 0 S) :
    |profFull α g z θ τ| ≤ 20 * pExp α + Ng := by
  have hα0 : 0 ≤ α := by
    have h : pExp α / 3 = α := by rw [pExp]; ring
    rw [← h]; positivity
  have hF : |Work.Construction.Fstar (pExp α) z θ| ≤ 20 * pExp α := by
    have h1 := Work.ConstructionInstance.Fstar_abs_le (p := pExp α) hp hp1 hz hθ
    have h2 : Work.FTS.Regularity.Gamma (pExp α / 3) θ ≤ 1 := by
      rw [show pExp α / 3 = α by rw [pExp]; ring]
      exact Work.ConstructionInstance.Gamma_le_one hα0 hθ
    calc |Work.Construction.Fstar (pExp α) z θ|
        ≤ 20 * pExp α * Work.FTS.Regularity.Gamma (pExp α / 3) θ := h1
      _ ≤ 20 * pExp α * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 20 * pExp α := by ring
  have hg : |g z θ τ| ≤ Ng := hNg.abs_le hz hθ hτ
  calc |profFull α g z θ τ| = |Work.Construction.Fstar (pExp α) z θ + g z θ τ| := by
        rw [profFull_apply]
    _ ≤ 20 * pExp α + Ng := abs_add_le_aux_prv.trans (add_le_add hF hg)

/-- `|F(z,θ,τ)| ≤ 20·3α + Ng` for the odd extension, `|θ| ∈ Iθ`. -/
private theorem profOdd_abs_le_aux {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {Ng : ℝ}
    (hp : 0 < pExp α) (hp1 : pExp α ≤ 1) (hNg : Jet α S Ng g) {z θ τ : ℝ} (hz : 0 ≤ z)
    (hθ : |θ| ∈ Work.Spaces.Iθ) (hτ : τ ∈ Set.Icc 0 S) :
    |profOdd α g z θ τ| ≤ 20 * pExp α + Ng := by
  rw [profOdd]
  split_ifs with hθ0
  · exact profFull_abs_le_aux hp hp1 hNg hz ⟨hθ0, le_trans (le_abs_self θ) hθ.2⟩ hτ
  · rw [abs_neg]
    have hθ₁ : -θ ∈ Work.Spaces.Iθ := by
      have h : -θ = |θ| := (abs_of_neg (not_le.mp hθ0)).symm
      rw [h]; exact hθ
    exact profFull_abs_le_aux hp hp1 hNg hz hθ₁ hτ

/-- **The z-derivative of the profile is bounded, jointly with the support**: on the support
region `z ≤ L` this is the two global boxes, and for `z > L` the profile vanishes identically in
`z`, so its `z`-derivative does too. -/
private theorem pzProf_mul_abs_le_aux {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {L Npz : ℝ}
    (hp : 0 < pExp α) (hp1 : pExp α ≤ 1) (hL0 : 0 < L)
    (hsupp : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, L ≤ z → profFull α g z θ τ = 0)
    (hcont : ∀ θ' ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ' q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hnpz : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz (gSlice g τ) z θ| ≤ Npz)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) {z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |z * pzProf α g z θ τ| ≤ max L 1 * (20 * pExp α + Npz) := by
  have hNpz0 : 0 ≤ Npz :=
    le_trans (abs_nonneg _) (hnpz τ hτ 0 0 le_rfl ⟨le_rfl, by linarith [Real.pi_pos]⟩)
  rcases le_or_gt z L with hzL | hzL
  · have hstar := pzFstar_abs_le_aux hp hp1 hz hθ
    have hsum : |pzProf α g z θ τ| ≤ 20 * pExp α + Npz := by
      rw [pzProf]
      exact abs_add_le_aux_prv.trans (add_le_add hstar (hnpz τ hτ z θ hz hθ))
    calc |z * pzProf α g z θ τ| = z * |pzProf α g z θ τ| := by
          rw [abs_mul, abs_of_nonneg hz]
      _ ≤ L * (20 * pExp α + Npz) := mul_le_mul hzL hsum (abs_nonneg _) hL0.le
      _ ≤ max L 1 * (20 * pExp α + Npz) :=
          mul_le_mul_of_nonneg_right (le_max_left L 1) (by linarith)
  · have hzero : pzProf α g z θ τ = 0 := by
      have hz1 : -1 < z := by linarith
      have hτmem : τ ∈ Set.Ioo (-1) (S + 1) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      have hsplit := profFull_deriv_z_aux (α := α) (S := S) (g := g) (θ := θ) (z := z) (τ := τ)
        (hcont θ hθ) hz1 hτmem
      have hev : (fun z' : ℝ => profFull α g z' θ τ) =ᶠ[𝓝 z] (fun _ => 0) := by
        filter_upwards [(isOpen_Ioi : IsOpen (Set.Ioi L)).mem_nhds hzL] with z' hz'
        exact hsupp τ hτ z' θ hz'.le
      have h0 : deriv (fun z' : ℝ => profFull α g z' θ τ) z = 0 := by
        rw [Filter.EventuallyEq.deriv_eq hev]
        simp
      rw [pzProf, ← hsplit]
      exact h0
    rw [hzero, mul_zero, abs_zero]
    exact mul_nonneg (le_trans zero_le_one (le_max_right L 1)) (by linarith)

/-- **The bound on the `τ`-derivative of the profile along the curve.**  Only the combination
`z·∂_zF` (with `z = ρ^{3α}/B τ`) enters, so the compact support of the profile enters through
`hpzProf` and the rest is the two-sided clock box. -/
private theorem profFull_curve_deriv_bound_aux {α : ℝ} {B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    {ρ θ τ b₀ b₂ Npz Nd L : ℝ} (hρ : 0 ≤ ρ) (hθ : θ ∈ Work.Spaces.Iθ)
    (hBpos : 0 < B τ) (hb₀pos : 0 < b₀) (hb₀ : b₀ ≤ B τ) (hb₂ : |deriv B τ| ≤ b₂)
    (hb₂0 : 0 ≤ b₂) (hNd0 : 0 ≤ Nd)
    (hpzProf : |(ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) θ τ|
      ≤ max L 1 * (20 * pExp α + Npz))
    (hnd : |deriv (fun t => g (ρ ^ pExp α / B τ) θ t) τ| ≤ Nd) :
    |zSlope α B ρ τ * pzProf α g (ρ ^ pExp α / B τ) θ τ
        + deriv (fun t => g (ρ ^ pExp α / B τ) θ t) τ|
      ≤ (b₂ / b₀) * (max L 1 * (20 * pExp α + Npz)) + Nd := by
  have hBne : B τ ≠ 0 := ne_of_gt hBpos
  have hz0 : 0 ≤ ρ ^ pExp α / B τ := div_nonneg (Real.rpow_nonneg hρ _) hBpos.le
  have hsl : |zSlope α B ρ τ| = (ρ ^ pExp α / B τ) * (|deriv B τ| / B τ) := by
    rw [zSlope, abs_neg, abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg hρ _),
      abs_of_pos (pow_pos hBpos 2)]
    field_simp
  have hcoef : |deriv B τ| / B τ ≤ b₂ / b₀ :=
    (div_le_div_of_nonneg_right hb₂ hBpos.le).trans
      (div_le_div_of_nonneg_left hb₂0 hb₀pos hb₀)
  calc |zSlope α B ρ τ * pzProf α g (ρ ^ pExp α / B τ) θ τ
        + deriv (fun t => g (ρ ^ pExp α / B τ) θ t) τ|
      ≤ |zSlope α B ρ τ * pzProf α g (ρ ^ pExp α / B τ) θ τ|
          + |deriv (fun t => g (ρ ^ pExp α / B τ) θ t) τ| := abs_add_le _ _
    _ = |zSlope α B ρ τ| * |pzProf α g (ρ ^ pExp α / B τ) θ τ|
          + |deriv (fun t => g (ρ ^ pExp α / B τ) θ t) τ| := by
          rw [abs_mul]
    _ = (|deriv B τ| / B τ)
          * |(ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) θ τ|
          + |deriv (fun t => g (ρ ^ pExp α / B τ) θ t) τ| := by
          rw [hsl, abs_mul, abs_of_nonneg hz0]
          ring
    _ ≤ (b₂ / b₀) * (max L 1 * (20 * pExp α + Npz)) + Nd := by
          refine add_le_add ?_ hnd
          exact mul_le_mul hcoef hpzProf (abs_nonneg _) (div_nonneg hb₂0 hb₀pos.le)

/-! ### The chain rule for the odd-extended profile along the curve -/

/-- **The `τ`-derivative of the profile along `s ↦ (ρ^{3α}/B(s), s)`**, with the explicit value
`dProfOdd`.  This is the chain rule in the two variables `(z, τ)` — the diagonal curve moves in
both at once, so the joint `C¹` data `hcont` (not separate partial differentiability) is what is
used. -/
private theorem profOdd_hasDerivAt_aux {α S : ℝ} {B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {ρ θ τ : ℝ}
    (hθabs : |θ| ≤ Real.pi / 2) (hρ : 0 ≤ ρ)
    (hcont : ∀ θ' ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ' q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hτ : τ ∈ Set.Ioo (-1) (S + 1)) (hBpos : 0 < B τ) (hBd : HasDerivAt B (deriv B τ) τ) :
    HasDerivAt (fun s => profOdd α g (ρ ^ pExp α / B s) θ s) (dProfOdd α B g ρ θ τ) τ := by
  have hBne : B τ ≠ 0 := ne_of_gt hBpos
  have hz0 : 0 ≤ ρ ^ pExp α / B τ := div_nonneg (Real.rpow_nonneg hρ _) hBpos.le
  have hz1 : -1 < ρ ^ pExp α / B τ := by linarith
  have hz : HasDerivAt (fun s : ℝ => ρ ^ pExp α / B s) (zSlope α B ρ τ) τ := by
    have h := (hasDerivAt_const τ (ρ ^ pExp α)).div hBd hBne
    rw [zSlope]
    exact h.congr_deriv (by ring)
  -- the core: the derivative for a fixed angle in `Iθ`
  have hcore : ∀ θ₁ : ℝ, θ₁ ∈ Work.Spaces.Iθ →
      HasDerivAt (fun s => profFull α g (ρ ^ pExp α / B s) θ₁ s)
        (zSlope α B ρ τ * pzProf α g (ρ ^ pExp α / B τ) θ₁ τ
          + deriv (fun t => g (ρ ^ pExp α / B τ) θ₁ t) τ) τ := by
    intro θ₁ hθ₁
    have hF : HasDerivAt (fun s => Work.Construction.Fstar (pExp α) (ρ ^ pExp α / B s) θ₁)
        (Work.Spaces.pz (Work.Construction.Fstar (pExp α)) (ρ ^ pExp α / B τ) θ₁
          * zSlope α B ρ τ) τ :=
      HasDerivAt.comp (h := fun s : ℝ => ρ ^ pExp α / B s) τ
        (Work.ConstructionInstance.hasDerivAt_Fstar_z (ρ ^ pExp α / B τ) θ₁ hz1) hz
    have hG := gComp_hasDerivAt_aux hθ₁ (hcont θ₁ hθ₁) hτ hz1 hz
    have hsum := hF.add hG
    have heq : (fun s : ℝ => profFull α g (ρ ^ pExp α / B s) θ₁ s)
        = fun s => Work.Construction.Fstar (pExp α) (ρ ^ pExp α / B s) θ₁
            + g (ρ ^ pExp α / B s) θ₁ s := by
      funext s; exact profFull_apply α g _ θ₁ s
    rw [heq]
    refine hsum.congr_deriv ?_
    rw [pzProf]
    ring
  rw [dProfOdd]
  by_cases hθ0 : 0 ≤ θ
  · rw [if_pos hθ0]
    have hθ₁ : θ ∈ Work.Spaces.Iθ := ⟨hθ0, le_trans (le_abs_self θ) hθabs⟩
    have heq : (fun s : ℝ => profOdd α g (ρ ^ pExp α / B s) θ s)
        = fun s => profFull α g (ρ ^ pExp α / B s) θ s := by
      funext s; rw [profOdd, if_pos hθ0]
    rw [heq]
    exact hcore θ hθ₁
  · rw [if_neg hθ0]
    have hθ₁ : -θ ∈ Work.Spaces.Iθ :=
      ⟨by linarith [not_le.mp hθ0], by linarith [neg_le_abs θ, hθabs]⟩
    have hneg := (hcore (-θ) hθ₁).neg
    have heq : (fun s : ℝ => profOdd α g (ρ ^ pExp α / B s) θ s)
        = fun s => -profFull α g (ρ ^ pExp α / B s) (-θ) s := by
      funext s; rw [profOdd, if_neg hθ0]
    rw [heq]
    exact hneg

/-! ### The main theorem -/

theorem physVort_hasDerivAt_and_bound {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.Regularity.RegPkg α S A B g) :
    (∀ x : Work.FTS.Regularity.R3, ∀ τ ∈ Set.Icc 0 S,
        HasDerivAt (fun s => Work.FTS.Regularity.physVort α A B g x s)
          (FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x τ) τ) ∧
      (∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ x : Work.FTS.Regularity.R3,
        ‖FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x τ‖ ≤ M) := by
  classical
  obtain ⟨a₀, a₁, ha₀pos, hAb⟩ := h.hAb
  obtain ⟨b₀, b₁, hb₀pos, hBb⟩ := h.hBb
  obtain ⟨a₂, hAd⟩ := h.hAd
  obtain ⟨b₂, hBd⟩ := h.hBd
  obtain ⟨Ng, hNg⟩ := h.hg
  obtain ⟨Npz, hNpz⟩ := h.hpz
  obtain ⟨Nd, hNd⟩ := h.hgdoth
  obtain ⟨L, hLpos, hLsupp⟩ := h.hsupp
  have hp : 0 < pExp α := h.pExp_pos
  have hp1 : pExp α ≤ 1 := h.pExp_le_one
  have hS0 : 0 ≤ S := h.hS.le
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) S := ⟨le_rfl, hS0⟩
  have hNg0 : 0 ≤ Ng := hNg.1
  have hNpz0 : 0 ≤ Npz := hNpz.1
  have hNd0 : 0 ≤ Nd := hNd.1
  have ha₂0 : 0 ≤ a₂ := le_trans (abs_nonneg _) (hAd 0 h0mem)
  have hb₂0 : 0 ≤ b₂ := le_trans (abs_nonneg _) (hBd 0 h0mem)
  set M : ℝ := a₀⁻¹ * (b₂ / b₀ * (max L 1 * (20 * pExp α + Npz)) + Nd)
      + (a₂ / a₀ ^ 2) * (20 * pExp α + Ng) with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    have h1 : (0 : ℝ) ≤ max L 1 := le_trans zero_le_one (le_max_right L 1)
    have h2 : (0 : ℝ) ≤ 20 * pExp α + Npz := by linarith
    have h3 : (0 : ℝ) ≤ 20 * pExp α + Ng := by linarith
    positivity
  -- the three constants of the derivative bound
  have hdu : ∀ τ ∈ Set.Icc 0 S, ∀ ρ θ : ℝ, 0 ≤ ρ → |θ| ∈ Work.Spaces.Iθ →
      |dProfOdd α B g ρ θ τ|
        ≤ (b₂ / b₀) * (max L 1 * (20 * pExp α + Npz)) + Nd := by
    intro τ hτ ρ θ hρ hθmem
    have hθabs : |θ| ≤ Real.pi / 2 := hθmem.2
    have hBτ : 0 < B τ := h.hB τ hτ
    have hBτ₀ : b₀ ≤ B τ := (hBb τ hτ).1
    have hz0 : 0 ≤ ρ ^ pExp α / B τ := div_nonneg (Real.rpow_nonneg hρ _) hBτ.le
    have hpzProf : ∀ θ₁ ∈ Work.Spaces.Iθ,
        |(ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) θ₁ τ|
          ≤ max L 1 * (20 * pExp α + Npz) := fun θ₁ hθ₁ =>
      pzProf_mul_abs_le_aux hp hp1 hLpos hLsupp h.hcont
        (fun τ' hτ' z θ' hz' hθ' => hNpz.abs_le hz' hθ' hτ') hτ hz0 hθ₁
    rw [dProfOdd]
    split_ifs with hθ0
    · exact profFull_curve_deriv_bound_aux hρ ⟨hθ0, le_trans (le_abs_self θ) hθabs⟩ hBτ hb₀pos
        hBτ₀ (hBd τ hτ) hb₂0 hNd0
        (hpzProf θ ⟨hθ0, le_trans (le_abs_self θ) hθabs⟩)
        (hNd.abs_le hz0 ⟨hθ0, le_trans (le_abs_self θ) hθabs⟩ hτ)
    · rw [abs_neg]
      have hθ₁ : -θ ∈ Work.Spaces.Iθ :=
        ⟨by linarith [not_le.mp hθ0], by linarith [neg_le_abs θ, hθabs]⟩
      exact profFull_curve_deriv_bound_aux hρ hθ₁ hBτ hb₀pos hBτ₀ (hBd τ hτ) hb₂0 hNd0
        (hpzProf (-θ) hθ₁) (hNd.abs_le hz0 hθ₁ hτ)
  -- the derivative
  have hder : ∀ x : R3, ∀ τ ∈ Set.Icc 0 S,
      HasDerivAt (fun s => physVort α A B g x s) (vortDt α A B g x τ) τ := by
    intro x τ hτ
    have hmem : τ ∈ Set.Ioo (-1) (S + 1) := ⟨by linarith [hτ.1], by linarith [hτ.2, h.hS]⟩
    have hscal := profOdd_hasDerivAt_aux (α := α) (S := S) (B := B) (g := g)
      (ρ := Work.Cyl.rho x) (θ := Work.Cyl.theta x) (τ := τ)
      (abs_theta_mem_Iθ_aux x).2 (Work.Cyl.rho_nonneg x) h.hcont hmem
      (h.hB τ hτ) (h.hBdiff τ hτ)
    have hvec := hscal.smul_const (Work.Cyl.eTheta x)
    have hAinv : HasDerivAt (fun s : ℝ => (A s)⁻¹) (-(deriv A τ) / (A τ) ^ 2) τ :=
      (h.hAdiff τ hτ).inv (ne_of_gt (h.hA τ hτ))
    have hprod := hAinv.smul hvec
    have heq : (fun s : ℝ => physVort α A B g x s)
        = fun s : ℝ => (A s)⁻¹ • (profOdd α g (Work.Cyl.rho x ^ pExp α / B s)
            (Work.Cyl.theta x) s • Work.Cyl.eTheta x) := by
      funext s; rw [physVort_eq_smul]
    rw [heq, vortDt]
    exact hprod
  have htimeDeriv : ∀ x : R3, ∀ τ ∈ Set.Icc 0 S,
      FiniteTimeSingularity.timeDeriv (physVort α A B g) x τ = vortDt α A B g x τ := by
    intro x τ hτ
    rw [physVort_timeDeriv]
    exact (hder x τ hτ).deriv
  refine ⟨?_, ⟨M, hM0, ?_⟩⟩
  · intro x τ hτ
    rw [htimeDeriv x τ hτ]
    exact hder x τ hτ
  · intro τ hτ x
    have hAτ : 0 < A τ := h.hA τ hτ
    rw [htimeDeriv x τ hτ, vortDt]
    set ρ := Work.Cyl.rho x with hρdef
    set θ := Work.Cyl.theta x with hθdef
    set e : R3 := Work.Cyl.eTheta x with hedef
    have hρ0 : 0 ≤ ρ := Work.Cyl.rho_nonneg x
    have hθmem : |θ| ∈ Work.Spaces.Iθ := by rw [hθdef]; exact abs_theta_mem_Iθ_aux x
    have he1 : ‖e‖ ≤ 1 := by rw [hedef]; exact norm_eTheta_le_one_aux x
    have hAinv_le : (A τ)⁻¹ ≤ a₀⁻¹ := (inv_le_inv₀ hAτ ha₀pos).mpr ((hAb τ hτ).1)
    have hA2_le : |deriv A τ| / (A τ) ^ 2 ≤ a₂ / a₀ ^ 2 := by
      refine (div_le_div_of_nonneg_right (hAd τ hτ) (pow_pos hAτ 2).le).trans ?_
      exact div_le_div_of_nonneg_left ha₂0 (pow_pos ha₀pos 2)
        (pow_le_pow_left₀ ha₀pos.le (hAb τ hτ).1 2)
    have hu : ‖profOdd α g (ρ ^ pExp α / B τ) θ τ • e‖ ≤ 20 * pExp α + Ng :=
      calc ‖profOdd α g (ρ ^ pExp α / B τ) θ τ • e‖
          = |profOdd α g (ρ ^ pExp α / B τ) θ τ| * ‖e‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ |profOdd α g (ρ ^ pExp α / B τ) θ τ| * 1 :=
            mul_le_mul_of_nonneg_left he1 (abs_nonneg _)
        _ = |profOdd α g (ρ ^ pExp α / B τ) θ τ| := mul_one _
        _ ≤ 20 * pExp α + Ng :=
            profOdd_abs_le_aux hp hp1 hNg
              (div_nonneg (Real.rpow_nonneg hρ0 _) (h.hB τ hτ).le) hθmem hτ
    have hduE : ‖dProfOdd α B g ρ θ τ • e‖
        ≤ (b₂ / b₀) * (max L 1 * (20 * pExp α + Npz)) + Nd :=
      calc ‖dProfOdd α B g ρ θ τ • e‖ = |dProfOdd α B g ρ θ τ| * ‖e‖ := by
            rw [norm_smul, Real.norm_eq_abs]
        _ ≤ |dProfOdd α B g ρ θ τ| * 1 := mul_le_mul_of_nonneg_left he1 (abs_nonneg _)
        _ = |dProfOdd α B g ρ θ τ| := mul_one _
        _ ≤ (b₂ / b₀) * (max L 1 * (20 * pExp α + Npz)) + Nd := hdu τ hτ ρ θ hρ0 hθmem
    have hcoef1 : 0 ≤ b₂ / b₀ * (max L 1 * (20 * pExp α + Npz)) + Nd := by
      have h : 0 ≤ b₂ / b₀ * (max L 1 * (20 * pExp α + Npz)) :=
        mul_nonneg (div_nonneg hb₂0 hb₀pos.le)
          (mul_nonneg (le_trans zero_le_one (le_max_right L 1)) (by linarith))
      linarith
    have hcoef2 : 0 ≤ 20 * pExp α + Ng := by linarith
    calc ‖(A τ)⁻¹ • (dProfOdd α B g ρ θ τ • e)
          + (-(deriv A τ) / (A τ) ^ 2) • (profOdd α g (ρ ^ pExp α / B τ) θ τ • e)‖
        ≤ ‖(A τ)⁻¹ • (dProfOdd α B g ρ θ τ • e)‖
            + ‖(-(deriv A τ) / (A τ) ^ 2) • (profOdd α g (ρ ^ pExp α / B τ) θ τ • e)‖ :=
          norm_add_le _ _
      _ = (A τ)⁻¹ * ‖dProfOdd α B g ρ θ τ • e‖
            + |deriv A τ| / (A τ) ^ 2 * ‖profOdd α g (ρ ^ pExp α / B τ) θ τ • e‖ := by
          congr 1
          · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hAτ.le)]
          · rw [norm_smul, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (pow_pos hAτ 2)]
      _ ≤ a₀⁻¹ * (b₂ / b₀ * (max L 1 * (20 * pExp α + Npz)) + Nd)
            + (a₂ / a₀ ^ 2) * (20 * pExp α + Ng) :=
          add_le_add (mul_le_mul hAinv_le hduE (norm_nonneg _) (inv_nonneg.mpr ha₀pos.le))
            (mul_le_mul hA2_le hu (norm_nonneg _) (div_nonneg ha₂0 (pow_pos ha₀pos 2).le))
      _ = M := by rw [hMdef]

end Work.FTS.Regularity
end
end
-- ===== merged: Submission.Work.FTS.Regularity.physVort_support =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set

namespace Work.FTS.Regularity

/-! ## Compact support of the physical vorticity

The physical vorticity of the route is

  `physVort α A B g x τ = A(τ)⁻¹ · F(ρ(x)^{3α}/B(τ), θ(x), τ) · e_θ(x)`,

so it vanishes wherever the *profile* `F = F_* + g` does.  The interface `RegPkg` supplies the
compact support of the full profile in the self-similar variable `z`, uniformly on the strip
(`hsupp`), and the two-sided bound `B τ ≤ b₁` (`hBb`).  Hence the physical vorticity is supported
in a ball whose radius is controlled by `L · b₁` and the profile exponent `3α`.

The only two ingredients are (i) the dictionary between the profile of a `τ`-slice
(`ConstructionInstance.profile`) and the full profile `profFull`, and (ii) the elementary
observation that `t ^ s ≤ c` with `t ≥ 0`, `s > 0`, `c ≥ 0` forces `t ≤ max 1 (c ^ s⁻¹)`. -/

/-- The profile of a `τ`-slice agrees with the full profile `profFull` on the physical half plane
`0 ≤ θ`. -/
private lemma profile_gSlice_eq_profFull (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ z θ : ℝ)
    (hθ : 0 ≤ θ) :
    Work.ConstructionInstance.profile (pExp α) (gSlice g τ) z θ = profFull α g z θ τ := by
  rw [Work.ConstructionInstance.profile_of_nonneg hθ]
  rfl

/-- Off the physical half plane `θ ≥ 0` the profile of a `τ`-slice is the odd extension of the
full profile. -/
private lemma profile_gSlice_eq_neg_profFull (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ z θ : ℝ)
    (hθ : ¬ 0 ≤ θ) :
    Work.ConstructionInstance.profile (pExp α) (gSlice g τ) z θ
      = - profFull α g z (-θ) τ := by
  rw [Work.ConstructionInstance.profile_of_neg hθ]
  rfl

/-- If `t ≥ 0` and `t ^ s ≤ c` with `s > 0` and `c ≥ 0`, then `t ≤ max 1 (c ^ s⁻¹)`. -/
private lemma le_max_one_rpow_inv {s c t : ℝ} (hs : 0 < s) (_hc : 0 ≤ c) (ht : 0 ≤ t)
    (h : t ^ s ≤ c) : t ≤ max 1 (c ^ (1 / s)) := by
  rcases le_or_gt t 1 with h1 | h1
  · exact le_trans h1 (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    calc t = (t ^ s) ^ (1 / s) := by
          rw [← Real.rpow_mul ht s (1 / s), mul_one_div_cancel (ne_of_gt hs), Real.rpow_one]
      _ ≤ c ^ (1 / s) := Real.rpow_le_rpow (Real.rpow_nonneg ht s) h (by positivity)

/-- **The physical vorticity of a `RegPkg` profile is compactly supported, uniformly on the
strip `[0,S]`.**  The radius is `max 1 ((L · b₁) ^ (3α)⁻¹)`, where `L` bounds the support of the
full profile in `z` and `b₁` bounds the clock `B` above. -/
theorem physVort_support {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.Regularity.RegPkg α S A B g) :
    ∃ R : ℝ, 0 < R ∧ ∀ τ ∈ Set.Icc 0 S, ∀ y : Work.FTS.Regularity.R3,
      Work.FTS.Regularity.physVort α A B g y τ ≠ 0 → y ∈ Metric.closedBall 0 R := by
  obtain ⟨L, hLpos, hL⟩ := h.hsupp
  obtain ⟨b₀, b₁, hb₀pos, hBb⟩ := h.hBb
  have h0 : (0 : ℝ) ∈ Set.Icc 0 S := ⟨le_rfl, h.hS.le⟩
  have hb₁pos : 0 < b₁ := lt_of_lt_of_le hb₀pos (le_trans (hBb 0 h0).1 (hBb 0 h0).2)
  refine ⟨max 1 ((L * b₁) ^ (1 / pExp α)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro τ hτ y hy
  simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  -- the profile at the rescaled self-similar variable must be non-zero
  have hpne : Work.ConstructionInstance.profile (pExp α) (gSlice g τ)
      (Work.Cyl.rho y ^ pExp α / B τ) (Work.Cyl.theta y) ≠ 0 := by
    intro hz
    refine hy ?_
    rw [physVort_apply, Work.ConstructionInstance.omegaSz_apply, hz]
    simp
  -- hence the self-similar variable lies below the support radius `L`
  have hzL : Work.Cyl.rho y ^ pExp α / B τ ≤ L := by
    rcases le_or_gt 0 (Work.Cyl.theta y) with hθ | hθ
    · rw [profile_gSlice_eq_profFull α g τ _ _ hθ] at hpne
      by_contra hc
      exact hpne (hL τ hτ _ (Work.Cyl.theta y) (not_le.mp hc).le)
    · rw [profile_gSlice_eq_neg_profFull α g τ _ _ (not_le.mpr hθ), neg_ne_zero] at hpne
      by_contra hc
      exact hpne (hL τ hτ _ (-(Work.Cyl.theta y)) (not_le.mp hc).le)
  -- convert it into a bound on `ρ(y)`, using `B τ ≤ b₁`
  have hBτ : 0 < B τ := lt_of_lt_of_le hb₀pos (hBb τ hτ).1
  have hle : Work.Cyl.rho y ^ pExp α ≤ L * b₁ :=
    ((div_le_iff₀ hBτ).mp hzL).trans (mul_le_mul_of_nonneg_left (hBb τ hτ).2 hLpos.le)
  rw [← Work.Cyl.rho_eq_norm y]
  exact le_max_one_rpow_inv (pExp_pos h.hα) (mul_nonneg hLpos.le hb₁pos.le)
    (Work.Cyl.rho_nonneg y) hle

end Work.FTS.Regularity
end
end
-- ===== merged: Submission.Work.FTS.Regularity.profFullBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Regularity

/-- **The uniform bound of the full profile `F = F_* + g`.**  For every regularity package
`RegPkg α S A B g` there is a constant `M ≥ 0` with `|F(z,θ,τ)| ≤ M` for all `τ ∈ [0,S]`,
`z ≥ 0` and `θ ∈ Iθ`.  Since `pExp α = 3α ≤ 1` and `Γ ≤ 1` on `Iθ`, the explicit choice
`M = 20·(3α) + Cv` works, where `Cv` is the `L^∞` bound of `g` extracted from the angular
vanishing datum. -/
theorem profFullBounds {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg α S A B g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |profFull α g z θ τ| ≤ M := by
  obtain ⟨Cv, hCv0, hCv⟩ := h.abs_le_Cv
  have hp : 0 < pExp α := h.pExp_pos
  have hp1 : pExp α ≤ 1 := h.pExp_le_one
  refine ⟨20 * pExp α + Cv, by positivity, fun τ hτ z θ hz hθ => ?_⟩
  have hGam1 : Gamma (pExp α / 3) θ ≤ 1 :=
    Work.ConstructionInstance.Gamma_le_one (by positivity) hθ
  have hF := Work.ConstructionInstance.Fstar_abs_le hp hp1 hz hθ
  have hG := hCv τ hτ z θ hz hθ
  rw [profFull_apply]
  calc |Work.Construction.Fstar (pExp α) z θ + g z θ τ|
      ≤ |Work.Construction.Fstar (pExp α) z θ| + |g z θ τ| := abs_add_le _ _
    _ ≤ 20 * pExp α * Gamma (pExp α / 3) θ + Cv := add_le_add hF hG
    _ ≤ 20 * pExp α + Cv := by
        have h1 : 20 * pExp α * Gamma (pExp α / 3) θ ≤ 20 * pExp α := by
          simpa using mul_le_mul_of_nonneg_left hGam1 (show (0 : ℝ) ≤ 20 * pExp α by positivity)
        linarith

end Work.FTS.Regularity
end
