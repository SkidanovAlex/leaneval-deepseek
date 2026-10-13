import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.CoreResiduals.BiotSavart.WindowExtDefs

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
