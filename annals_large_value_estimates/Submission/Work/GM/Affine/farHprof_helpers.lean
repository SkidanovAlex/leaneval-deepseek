import Mathlib
import Submission.Work.GM.Affine.far_part_defs
import Submission.Work.GM.Affine.ghatFar_eq_sum_Wfar
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.psi1hat_decay
import Submission.Work.GM.Affine.region_I_bound
import Submission.Work.GM.Affine.WinMass_basic

/-!
# GM §9, region II: the window/tail decomposition of the far weight (self-contained copy)

The file `Submission/Work/GM/Affine/far_part_reduction.lean` contains, among other things, the
**proved** lemmas `split_indicator`, `summable_window_part`, `Wfar_eq_Wwin_add_Wtail`,
`Wwin_eq_finsum` and `ghatFar_window_eq_pairs`.  That file is currently *not importable* (it
imports the module `Submission.Work.GM.Affine.window_part_L2_estimate`, which has been deleted by
another node), so this file carries verbatim copies of exactly those lemmas, with the same names
and the same proofs, resting only on modules that do build.

Downstream users: `Work.GM.Affine.windowTrunc_L2_bound` (the window-part `L²` bound) and
`Work.GM.Affine.regionII_Hprof_bound` (the region-II far estimate in `∫(Hprof)²` form).
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The `ψ̂₁` family sampled on the lattice `M₃ℤ - M₃y` is summable (alias of
`summable_psi1hat_shift`, kept under the name used by the far-part development). -/
lemma summable_psi1hat_lattice (K M₃ y : ℝ) (hK : 0 < K) (hM₃ : 0 < M₃) :
    Summable (fun ℓ : ℤ => psi1hat K (M₃ * ((ℓ : ℝ) - y))) :=
  summable_psi1hat_shift K M₃ y hK hM₃

/-- The resonant part of the lattice sum is finitely supported. -/
lemma hasFiniteSupport_resonant_part (K M₃ y : ℝ) (hM₃ : 0 < M₃) :
    Function.HasFiniteSupport
      (fun ℓ : ℤ => if |(ℓ : ℝ) - y| ≤ 2 / M₃ then psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0) := by
  refine Set.Finite.subset (Set.finite_Icc (-(⌈|y| + 2 / M₃⌉)) ⌈|y| + 2 / M₃⌉) ?_
  intro ℓ hℓ
  rw [Function.mem_support] at hℓ
  rw [Set.mem_Icc]
  have hcast : ((⌈|y| + 2 / M₃⌉ : ℤ) : ℝ) ≥ |y| + 2 / M₃ := by
    have := Int.le_ceil (|y| + 2 / M₃); push_cast; linarith
  have hzero : |(ℓ : ℝ) - y| > 2 / M₃ → False := by
    intro hc
    exact hℓ (if_neg (not_le.mpr hc))
  constructor
  · by_contra h
    have h1 : ℓ ≤ -(⌈|y| + 2 / M₃⌉) - 1 := by omega
    have h2 : ((ℓ:ℤ) : ℝ) ≤ -((⌈|y| + 2 / M₃⌉ : ℤ) : ℝ) - 1 := by exact_mod_cast h1
    have h3 : ((ℓ:ℤ) : ℝ) < -(|y| + 2 / M₃) := by linarith
    have h5 : |((ℓ:ℤ) : ℝ) - y| ≥ -((ℓ:ℤ) : ℝ) - |y| := by
      have h6 : |((ℓ:ℤ) : ℝ)| ≤ |((ℓ:ℤ) : ℝ) - y| + |y| := by
        have h7 := abs_add_le (((ℓ:ℤ) : ℝ) - y) y
        rwa [sub_add_cancel] at h7
      have h8 : |((ℓ:ℤ) : ℝ)| ≥ -((ℓ:ℤ) : ℝ) := neg_le_abs _
      linarith
    exact hzero (by linarith)
  · by_contra h
    have h1 : (⌈|y| + 2 / M₃⌉) + 1 ≤ ℓ := by omega
    have h2 : ((⌈|y| + 2 / M₃⌉ : ℤ) : ℝ) + 1 ≤ ((ℓ:ℤ) : ℝ) := by exact_mod_cast h1
    have h3 : ((ℓ:ℤ) : ℝ) > |y| + 2 / M₃ := by linarith
    have h5 : |((ℓ:ℤ) : ℝ) - y| ≥ ((ℓ:ℤ) : ℝ) - |y| := by
      have h6 : |((ℓ:ℤ) : ℝ)| ≤ |((ℓ:ℤ) : ℝ) - y| + |y| := by
        have h7 := abs_add_le (((ℓ:ℤ) : ℝ) - y) y
        rwa [sub_add_cancel] at h7
      have h8 : |((ℓ:ℤ) : ℝ)| ≥ ((ℓ:ℤ) : ℝ) := le_abs_self _
      linarith
    exact hzero (by linarith)


/-- Elementary splitting of an indicator into its `≤ B` and `> B` parts. -/
lemma split_indicator (B c z : ℝ) (a : ℂ) :
    (if c < z then a else 0)
      = (if c < z ∧ z ≤ B then a else 0) + (if B < z ∧ c < z then a else 0) := by
  by_cases hcz : c < z
  · rw [if_pos hcz]
    rcases le_or_gt z B with h | h
    · rw [if_pos ⟨hcz, h⟩, if_neg (fun hh => absurd hh.1 (not_lt.mpr h)), add_zero]
    · rw [if_neg (fun hh => absurd hh.2 (not_le.mpr h)), if_pos ⟨h, hcz⟩, zero_add]
  · rw [if_neg hcz, if_neg (fun hh => absurd hh.1 hcz), if_neg (fun hh => absurd hh.2 hcz),
      add_zero]

lemma summable_window_part (K M₃ B y : ℝ) (hM₃ : 0 < M₃) :
    Summable (fun ℓ : ℤ =>
      if 2 / M₃ < |(ℓ : ℝ) - y| ∧ |(ℓ : ℝ) - y| ≤ B / M₃ then
        psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0) := by
  refine summable_of_hasFiniteSupport ?_
  refine Set.Finite.subset (Set.finite_Icc (-(⌈|y| + B / M₃⌉)) ⌈|y| + B / M₃⌉) ?_
  intro ℓ hℓ
  rw [Function.mem_support] at hℓ
  rw [Set.mem_Icc]
  have hcast : ((⌈|y| + B / M₃⌉ : ℤ) : ℝ) ≥ |y| + B / M₃ := by
    have := Int.le_ceil (|y| + B / M₃); push_cast; linarith
  have hzero : B / M₃ < |(ℓ : ℝ) - y| → False := fun hc =>
    hℓ (if_neg (fun h => absurd h.2 (not_le.mpr hc)))
  have hle : |((ℓ:ℤ) : ℝ)| ≤ |((ℓ:ℤ) : ℝ) - y| + |y| := by
    have h7 := abs_add_le (((ℓ:ℤ) : ℝ) - y) y
    rwa [sub_add_cancel] at h7
  constructor
  · by_contra h
    have h1 : ℓ ≤ -(⌈|y| + B / M₃⌉) - 1 := by omega
    have h2 : ((ℓ:ℤ) : ℝ) ≤ -((⌈|y| + B / M₃⌉ : ℤ) : ℝ) - 1 := by exact_mod_cast h1
    have h3 : ((ℓ:ℤ) : ℝ) < -(|y| + B / M₃) := by linarith
    have h8 : |((ℓ:ℤ) : ℝ)| ≥ -((ℓ:ℤ) : ℝ) := neg_le_abs _
    exact hzero (by linarith)
  · by_contra h
    have h1 : (⌈|y| + B / M₃⌉) + 1 ≤ ℓ := by omega
    have h2 : ((⌈|y| + B / M₃⌉ : ℤ) : ℝ) + 1 ≤ ((ℓ:ℤ) : ℝ) := by exact_mod_cast h1
    have h3 : ((ℓ:ℤ) : ℝ) > |y| + B / M₃ := by linarith
    have h8 : |((ℓ:ℤ) : ℝ)| ≥ ((ℓ:ℤ) : ℝ) := le_abs_self _
    exact hzero (by linarith)

/-- The far weight decomposes into its window part and its tail part. -/
lemma Wfar_eq_Wwin_add_Wtail (K M₃ B y : ℝ) (hK : 0 < K) (hM₃ : 0 < M₃) :
    Wfar K M₃ y = Wwin K M₃ B y + Wtail K M₃ B y := by
  have hfar : Summable
      (fun ℓ : ℤ => if |(ℓ : ℝ) - y| > 2 / M₃ then psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0) := by
    have h1 : (fun ℓ : ℤ => if |(ℓ : ℝ) - y| > 2 / M₃ then psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0)
        = fun ℓ : ℤ => psi1hat K (M₃ * ((ℓ : ℝ) - y))
            - (if |(ℓ : ℝ) - y| ≤ 2 / M₃ then psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0) := by
      funext ℓ
      by_cases h : |(ℓ : ℝ) - y| ≤ 2 / M₃
      · rw [if_neg (not_lt.mpr h), if_pos h]; ring
      · rw [if_pos (not_le.mp h), if_neg h]; ring
    rw [h1]
    exact (summable_psi1hat_lattice K M₃ y hK hM₃).sub
      (summable_of_hasFiniteSupport (hasFiniteSupport_resonant_part K M₃ y hM₃))
  have hwin : Summable (fun ℓ : ℤ =>
      if 2 / M₃ < |(ℓ : ℝ) - y| ∧ |(ℓ : ℝ) - y| ≤ B / M₃ then
        psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0) := summable_window_part K M₃ B y hM₃
  have htail : Summable (fun ℓ : ℤ =>
      if B / M₃ < |(ℓ : ℝ) - y| ∧ 2 / M₃ < |(ℓ : ℝ) - y| then
        psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0) := by
    have h1 : (fun ℓ : ℤ => if B / M₃ < |(ℓ : ℝ) - y| ∧ 2 / M₃ < |(ℓ : ℝ) - y|
        then psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0)
        = fun ℓ : ℤ => (if 2 / M₃ < |(ℓ : ℝ) - y| then psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0)
            - (if 2 / M₃ < |(ℓ : ℝ) - y| ∧ |(ℓ : ℝ) - y| ≤ B / M₃ then
                psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0) := by
      funext ℓ
      have hsp := split_indicator (B / M₃) (2 / M₃) |(ℓ : ℝ) - y| (psi1hat K (M₃ * ((ℓ : ℝ) - y)))
      rw [hsp]
      ring
    rw [h1]
    exact hfar.sub hwin
  have hsplit : (∑' ℓ : ℤ, if |(ℓ : ℝ) - y| > 2 / M₃ then psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0)
      = (∑' ℓ : ℤ, if 2 / M₃ < |(ℓ : ℝ) - y| ∧ |(ℓ : ℝ) - y| ≤ B / M₃ then
            psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0)
        + (∑' ℓ : ℤ, if B / M₃ < |(ℓ : ℝ) - y| ∧ 2 / M₃ < |(ℓ : ℝ) - y| then
            psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0) := by
    rw [← Summable.tsum_add hwin htail]
    refine tsum_congr (fun ℓ => ?_)
    have := split_indicator (B / M₃) (2 / M₃) |(ℓ : ℝ) - y| (psi1hat K (M₃ * ((ℓ : ℝ) - y)))
    simpa using this
  rw [Wfar, Wwin, Wtail, hsplit]
  ring


/-! ## The window pairs -/



/-- **The window weight is a finite `ℓ`-sum.** -/
lemma Wwin_eq_finsum (K T M₁ M₃ B : ℝ) (hM₁ : 0 < M₁) (hM₃ : 0 < M₃) {ξ : ℝ} {m₁ : ℤ}
    (hm₁ : m₁ ∈ R1 M₁) (hξ : |ξ| ≤ T ^ 6) :
    Wwin K M₃ B (ξ / (m₁ : ℝ)) =
      (M₃ : ℂ) * ∑ ℓ ∈ Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B),
        (if 2 / M₃ < |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ∧ |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ≤ B / M₃ then
          psi1hat K (M₃ * ((ℓ : ℝ) - ξ / (m₁ : ℝ))) else 0) := by
  have hm₁pos : M₁ < |(m₁ : ℝ)| := (Finset.mem_filter.mp hm₁).2
  have habs : M₁ ≤ |(m₁ : ℝ)| := le_of_lt hm₁pos
  have hy : |ξ / (m₁ : ℝ)| ≤ T ^ 6 / M₁ := by
    rw [abs_div]
    have h1 : |ξ| / |(m₁:ℝ)| ≤ T ^ 6 / |(m₁:ℝ)| :=
      div_le_div_of_nonneg_right hξ (abs_nonneg _)
    have h2 : T ^ 6 / |(m₁:ℝ)| ≤ T ^ 6 / M₁ :=
      div_le_div_of_nonneg_left (by positivity) hM₁ habs
    linarith
  have hceil : ((⌈T ^ 6 / M₁ + B / M₃⌉ : ℤ) : ℝ) ≥ T ^ 6 / M₁ + B / M₃ := by
    have := Int.le_ceil (T ^ 6 / M₁ + B / M₃); push_cast; linarith
  have hLbound : ((Lwin T M₁ M₃ B : ℤ) : ℝ) ≥ T ^ 6 / M₁ + B / M₃ + 1 := by
    rw [Lwin]; push_cast; linarith [hceil]
  rw [Wwin]
  congr 1
  refine tsum_eq_sum (fun ℓ hℓ => ?_)
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hℓ
  have hfar : B / M₃ < |(ℓ : ℝ) - ξ / (m₁ : ℝ)| := by
    rcases hℓ with h | h
    · have h1 : ℓ ≤ -(Lwin T M₁ M₃ B) - 1 := by omega
      have h2 : ((ℓ:ℤ) : ℝ) ≤ -((Lwin T M₁ M₃ B : ℤ) : ℝ) - 1 := by exact_mod_cast h1
      have h5 : |((ℓ:ℤ) : ℝ) - ξ / (m₁:ℝ)| ≥ -((ℓ:ℤ) : ℝ) - |ξ / (m₁:ℝ)| := by
        have h6 : |((ℓ:ℤ) : ℝ)| ≤ |((ℓ:ℤ) : ℝ) - ξ/(m₁:ℝ)| + |ξ/(m₁:ℝ)| := by
          have h7 := abs_add_le (((ℓ:ℤ) : ℝ) - ξ/(m₁:ℝ)) (ξ/(m₁:ℝ))
          rwa [sub_add_cancel] at h7
        have h8 : |((ℓ:ℤ) : ℝ)| ≥ -((ℓ:ℤ) : ℝ) := neg_le_abs _
        linarith
      linarith
    · have h1 : (Lwin T M₁ M₃ B) + 1 ≤ ℓ := by omega
      have h2 : ((Lwin T M₁ M₃ B : ℤ) : ℝ) + 1 ≤ ((ℓ:ℤ) : ℝ) := by exact_mod_cast h1
      have h5 : |((ℓ:ℤ) : ℝ) - ξ / (m₁:ℝ)| ≥ ((ℓ:ℤ) : ℝ) - |ξ / (m₁:ℝ)| := by
        have h6 : |((ℓ:ℤ) : ℝ)| ≤ |((ℓ:ℤ) : ℝ) - ξ/(m₁:ℝ)| + |ξ/(m₁:ℝ)| := by
          have h7 := abs_add_le (((ℓ:ℤ) : ℝ) - ξ/(m₁:ℝ)) (ξ/(m₁:ℝ))
          rwa [sub_add_cancel] at h7
        have h8 : |((ℓ:ℤ) : ℝ)| ≥ ((ℓ:ℤ) : ℝ) := le_abs_self _
        linarith
      linarith
  rw [if_neg (fun hh => absurd hh.2 (not_le.mpr hfar))]

/-- **The window part of `ghatFar` is the pair sum over `Pwin`.** -/
lemma ghatFar_window_eq_pairs (K T M₁ M₂ M₃ B : ℝ) (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {f : ℝ → ℝ} {ξ : ℝ} (hξ : |ξ| ≤ T ^ 6) :
    (∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
        Wwin K M₃ B (ξ / (m₁ : ℝ)))
      = ∑ p ∈ Pwin T M₁ M₃ B ξ, aTerm K M₂ M₃ f ξ p := by
  have h1 : (∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
        Wwin K M₃ B (ξ / (m₁ : ℝ)))
      = ∑ m₁ ∈ R1 M₁, ∑ ℓ ∈ Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B),
          (if 2 / M₃ < |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ∧ |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ≤ B / M₃ then
            aTerm K M₂ M₃ f ξ (m₁, ℓ) else 0) := by
    apply Finset.sum_congr rfl
    intro m₁ hm₁
    rw [Wwin_eq_finsum K T M₁ M₃ B hM₁ hM₃ hm₁ hξ, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    by_cases h : 2 / M₃ < |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ∧ |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ≤ B / M₃
    · rw [if_pos h, if_pos h]
      simp only [aTerm]
    · rw [if_neg h, if_neg h, mul_zero, mul_zero]
  rw [h1, Pwin, Finset.sum_filter]
  exact (Finset.sum_product (R1 M₁) (Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B))
    (fun p : ℤ × ℤ => if 2 / M₃ < |((p.2 : ℝ) - ξ / (p.1 : ℝ))| ∧
      |((p.2 : ℝ) - ξ / (p.1 : ℝ))| ≤ B / M₃ then aTerm K M₂ M₃ f ξ p else 0)).symm





lemma hasCompactSupport_of_suppHyp_far {C₀ : ℝ} {f : ℝ → ℝ} (h : SuppHyp C₀ f) :
    HasCompactSupport f := by
  refine HasCompactSupport.intro (K := Set.Icc (1 / C₀) C₀) isCompact_Icc ?_
  intro x hx
  by_contra hf0
  exact hx (h x hf0)

lemma norm_Fhat_le_integral_norm {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f)
    (ξ : ℝ) : ‖Fhat f ξ‖ ≤ ∫ u, ‖f u‖ := by
  have hcont : Continuous (fun u : ℝ => (f u : ℂ) * efun (-(u * ξ))) := by
    refine Continuous.mul (Complex.continuous_ofReal.comp hf) ?_
    unfold efun
    fun_prop
  have hcs' : HasCompactSupport (fun u : ℝ => (f u : ℂ) * efun (-(u * ξ))) :=
    (hcs.comp_left (g := fun z : ℝ => (z : ℂ)) (by simp)).mul_right
  have hint : Integrable (fun u : ℝ => (f u : ℂ) * efun (-(u * ξ))) :=
    hcont.integrable_of_hasCompactSupport hcs'
  have hFeq : Fhat f ξ = ∫ u : ℝ, (f u : ℂ) * efun (-(u * ξ)) := Fhat_eq_integral' f ξ
  rw [hFeq]
  calc ‖∫ u : ℝ, (f u : ℂ) * efun (-(u * ξ))‖ ≤ ∫ u : ℝ, ‖(f u : ℂ) * efun (-(u * ξ))‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ u : ℝ, ‖f u‖ := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
        simp only
        rw [norm_mul, norm_efun, mul_one]
        exact RCLike.norm_ofReal _

lemma norm_Bsum_le_const {M₂ : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) (hfnn : ∀ u, 0 ≤ f u) (hM₂ : 0 < M₂) (x : ℝ) :
    ‖Bsum f M₂ x‖ ≤ 4 * M₂ ^ 2 * ∫ u, f u := by
  have hFhat : ∀ y : ℝ, ‖Fhat f y‖ ≤ ∫ u, f u := by
    intro y
    have h := norm_Fhat_le_integral_norm hf hcs y
    have h2 : (∫ u, ‖f u‖) = ∫ u, f u := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      simp only
      rw [Real.norm_of_nonneg (hfnn u)]
    rwa [h2] at h
  have hIntnn : (0:ℝ) ≤ ∫ u, f u := integral_nonneg hfnn
  calc ‖Bsum f M₂ x‖ = ‖∑ m₂ ∈ R2 M₂, ((m₂ : ℝ) : ℂ) * Fhat f ((m₂ : ℝ) * x)‖ := rfl
    _ ≤ ∑ m₂ ∈ R2 M₂, ‖((m₂ : ℝ) : ℂ) * Fhat f ((m₂ : ℝ) * x)‖ := norm_sum_le _ _
    _ ≤ ∑ m₂ ∈ R2 M₂, (m₂ : ℝ) * (∫ u, f u) := by
        refine Finset.sum_le_sum (fun m₂ hm₂ => ?_)
        have hm₂pos : (0:ℝ) < (m₂ : ℝ) := R2_pos' hm₂
        have h1 : ‖((m₂ : ℝ) : ℂ) * Fhat f ((m₂ : ℝ) * x)‖
            = (m₂ : ℝ) * ‖Fhat f ((m₂ : ℝ) * x)‖ := by
          have hnorm : ‖((m₂ : ℝ) : ℂ)‖ = |(m₂ : ℝ)| := RCLike.norm_ofReal _
          rw [norm_mul, hnorm, abs_of_nonneg hm₂pos.le]
        rw [h1]
        exact mul_le_mul_of_nonneg_left (hFhat _) hm₂pos.le
    _ = (∑ m₂ ∈ R2 M₂, (m₂ : ℝ)) * (∫ u, f u) := (Finset.sum_mul _ _ _).symm
    _ ≤ (4 * M₂ ^ 2) * (∫ u, f u) := mul_le_mul_of_nonneg_right (sum_R2_le M₂ hM₂) hIntnn

/-- The truncated window weight vanishes when `B ≤ 2`: the window `2/M₃ < |ℓ-y| ≤ B/M₃` is empty. -/
lemma Wwin_le_two_eq_zero (K M₃ : ℝ) {B : ℝ} (hM₃ : 0 < M₃) (hB : B ≤ 2) (y : ℝ) :
    Wwin K M₃ B y = 0 := by
  rw [Wwin, mul_eq_zero]
  right
  have hfun : (fun ℓ : ℤ => (if 2 / M₃ < |(ℓ : ℝ) - y| ∧ |(ℓ : ℝ) - y| ≤ B / M₃ then
      psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0)) = fun _ => (0 : ℂ) := by
    funext ℓ
    rw [if_neg]
    intro h
    have h1 : 2 / M₃ < B / M₃ := lt_of_lt_of_le h.1 h.2
    have h2 : B / M₃ ≤ 2 / M₃ := div_le_div_of_nonneg_right hB hM₃.le
    linarith
  rw [hfun, tsum_zero]


end

end Work.GM.Affine
