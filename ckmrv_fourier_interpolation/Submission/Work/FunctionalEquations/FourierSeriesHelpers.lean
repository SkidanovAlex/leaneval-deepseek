import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.FunctionalEquations.CoefficientValuePattern

/-!
# Helper lemmas for the Fourier (Dirichlet) expansions of the generating functions

This file collects the elementary facts about the Dirichlet series
`∑_m c_m e^{2 π i m τ}` that the Section 8 part of the CKMRV development uses:
summability of a polynomially bounded coefficient family against the Dirichlet
kernel (and against the Dirichlet kernel times the rate `√(2m)`), the same for the
Schwartz seminorms of a Schwartz family, and the identities for the slash factor
`slashFactor n τ = (i/τ)^{n/2}` under `τ ↦ -1/τ`.

The functions `dirichletTerm`, `rate`, `slashFactor` are the vocabulary of `Work.FE`;
this file is the shared base of the Section 8 lemmas
`Work.FunctionalEquations.Section8FourierDataOfRigidity` and
`Work.FunctionalEquations.Section8ValueDataOfRigidity`.
-/

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

/-! ## Summability of Dirichlet series -/

/-- A polynomial weight times a geometric sequence with ratio `t ∈ [0,1)` is summable. -/
private lemma summable_nat_add_one_pow_mul_geometric {N : ℕ} {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) : Summable fun n : ℕ => ((n : ℝ) + 1) ^ N * t ^ n := by
  have htabs : ‖t‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg ht0]; exact ht1
  have hgeom : Summable fun n : ℕ => (n : ℝ) ^ N * t ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one N htabs
  have hgeom1 : Summable fun n : ℕ => t ^ n := summable_geometric_of_norm_lt_one htabs
  have hmain : Summable fun n : ℕ => (2 : ℝ) ^ N * (((n : ℝ) ^ N * t ^ n) + t ^ n) :=
    (hgeom.add hgeom1).mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmain
  have hb : ((n : ℝ) + 1) ^ N ≤ (2 : ℝ) ^ N * ((n : ℝ) ^ N + 1) := by
    have hmax : ((n : ℝ) + 1) ≤ 2 * max (n : ℝ) 1 := by
      rcases le_or_gt 1 (n : ℝ) with hh | hh
      · rw [max_eq_left hh]; linarith
      · rw [max_eq_right hh.le]; linarith
    have hstep : ((n : ℝ) + 1) ^ N ≤ (2 * max (n : ℝ) 1) ^ N :=
      pow_le_pow_left₀ (by positivity) hmax N
    have hmaxN : (max (n : ℝ) 1) ^ N ≤ (n : ℝ) ^ N + 1 := by
      rcases le_or_gt 1 (n : ℝ) with hh | hh
      · rw [max_eq_left hh]
        have : (0 : ℝ) ≤ (n : ℝ) ^ N := by positivity
        linarith
      · rw [max_eq_right hh.le]; simp
    calc ((n : ℝ) + 1) ^ N ≤ (2 * max (n : ℝ) 1) ^ N := hstep
      _ = (2 : ℝ) ^ N * (max (n : ℝ) 1) ^ N := by rw [mul_pow]
      _ ≤ (2 : ℝ) ^ N * ((n : ℝ) ^ N + 1) :=
          mul_le_mul_of_nonneg_left hmaxN (by positivity)
  calc ((n : ℝ) + 1) ^ N * t ^ n ≤ ((2 : ℝ) ^ N * ((n : ℝ) ^ N + 1)) * t ^ n :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (2 : ℝ) ^ N * (((n : ℝ) ^ N * t ^ n) + t ^ n) := by ring

/-- **Exponential decay beats polynomial growth, real form.** -/
theorem SummableRealMulExpNeg {k₀ : ℕ} {c : Set.Ici k₀ → ℝ} {N : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hc : ∀ m : Set.Ici k₀, 0 ≤ c m)
    (h : ∀ m : Set.Ici k₀, c m ≤ C * ((m.1 : ℝ) + 1) ^ N) {y : ℝ} (hy : 0 < y) :
    Summable fun m : Set.Ici k₀ => c m * Real.exp (-(2 * Real.pi * y * (m.1 : ℝ))) := by
  set t : ℝ := Real.exp (-(2 * Real.pi * y)) with ht
  have ht0 : 0 ≤ t := (Real.exp_pos _).le
  have ht1 : t < 1 := by rw [ht, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, hy]
  have hw : Summable fun m : Set.Ici k₀ => ((m.1 : ℝ) + 1) ^ N * t ^ (m.1) :=
    (summable_nat_add_one_pow_mul_geometric ht0 ht1).subtype _
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (hc m) (Real.exp_pos _).le)
    (fun m => ?_) (hw.mul_left C)
  have hexp : Real.exp (-(2 * Real.pi * y * (m.1 : ℝ))) = t ^ (m.1) := by
    rw [ht, ← Real.exp_nat_mul]
    congr 1
    ring
  calc c m * Real.exp (-(2 * Real.pi * y * (m.1 : ℝ)))
      ≤ (C * ((m.1 : ℝ) + 1) ^ N) * Real.exp (-(2 * Real.pi * y * (m.1 : ℝ))) :=
        mul_le_mul_of_nonneg_right (h m) (Real.exp_pos _).le
    _ = C * (((m.1 : ℝ) + 1) ^ N * Real.exp (-(2 * Real.pi * y * (m.1 : ℝ)))) := by ring
    _ = C * (((m.1 : ℝ) + 1) ^ N * t ^ (m.1)) := by rw [hexp]

/-- **A polynomially bounded family is summable against the Dirichlet kernel**, and against
the Dirichlet kernel times the rate `√(2m)`. -/
theorem SummableDirichletTerm {k₀ : ℕ} {c : Set.Ici k₀ → ℂ} {N : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ m : Set.Ici k₀, ‖c m‖ ≤ C * ((m.1 : ℝ) + 1) ^ N)
    {τ : ℂ} (hτ : 0 < τ.im) :
    (Summable fun m : Set.Ici k₀ => c m * dirichletTerm m.1 τ) ∧
    (Summable fun m : Set.Ici k₀ => (rate m.1 : ℂ) * c m * dirichletTerm m.1 τ) := by
  have hnorm : ∀ m : Set.Ici k₀, ‖dirichletTerm m.1 τ‖
      = Real.exp (-(2 * Real.pi * τ.im * (m.1 : ℝ))) := fun m => norm_dirichletTerm _ _
  have hmain : Summable fun m : Set.Ici k₀ =>
      (C * ((m.1 : ℝ) + 1) ^ N) * Real.exp (-(2 * Real.pi * τ.im * (m.1 : ℝ))) := by
    refine SummableRealMulExpNeg (N := N) (C := C) hC
      (fun m => mul_nonneg hC (by positivity)) (fun m => le_rfl) hτ
  have h1 : Summable fun m : Set.Ici k₀ => ‖c m‖ * ‖dirichletTerm m.1 τ‖ := by
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun m => ?_) hmain
    rw [hnorm]
    exact mul_le_mul_of_nonneg_right (h m) (Real.exp_pos _).le
  have hrate : Summable fun m : Set.Ici k₀ =>
      (‖c m‖ * ((m.1 : ℝ) + 1)) * Real.exp (-(2 * Real.pi * τ.im * (m.1 : ℝ))) := by
    refine SummableRealMulExpNeg (k₀ := k₀)
      (c := fun m : Set.Ici k₀ => ‖c m‖ * ((m.1 : ℝ) + 1))
      (N := N + 1) (C := C) hC (fun m => mul_nonneg (norm_nonneg _) (by positivity))
      (fun m => ?_) hτ
    rw [pow_succ]
    exact le_trans (mul_le_mul_of_nonneg_right (h m) (by positivity)) (le_of_eq (by ring))
  refine ⟨Summable.of_norm_bounded h1 (fun m => by rw [norm_mul]), ?_⟩
  refine Summable.of_norm_bounded hrate (fun m => ?_)
  have hr : ‖(rate m.1 : ℂ)‖ = rate m.1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (rate_nonneg m.1)]
  rw [norm_mul, norm_mul, hr, hnorm]
  have hrr : rate m.1 * ‖c m‖ * Real.exp (-(2 * Real.pi * τ.im * (m.1 : ℝ)))
      ≤ (‖c m‖ * ((m.1 : ℝ) + 1)) * Real.exp (-(2 * Real.pi * τ.im * (m.1 : ℝ))) := by
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    rw [mul_comm ‖c m‖]
    exact mul_le_mul_of_nonneg_right (rate_le m.1) (norm_nonneg _)
  calc rate m.1 * ‖c m‖ * Real.exp (-(2 * Real.pi * τ.im * (m.1 : ℝ)))
      = (rate m.1 * ‖c m‖) * Real.exp (-(2 * Real.pi * τ.im * (m.1 : ℝ))) := by ring
    _ ≤ _ := hrr

/-- **Seminorm summability of a polynomially bounded Dirichlet series of Schwartz
functions.**  Under an exponential bound on the scalars `c m` and a polynomial bound on
the `(k,l)` seminorms of `u m`, the seminorms of the terms `c m • u m` are summable. -/
theorem SummableSeminormSmulExp {n : ℕ} [NeZero n] {k₀ : ℕ}
    (u : Set.Ici k₀ → 𝓢(E n, ℂ)) (c : Set.Ici k₀ → ℂ) {y : ℝ} (hy : 0 < y)
    (hu : ∀ k l : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ m : Set.Ici k₀,
        (SchwartzMap.seminorm ℂ k l) (u m) ≤ C * ((m.1 : ℝ) + 1) ^ N)
    (hc : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ m : Set.Ici k₀,
        ‖c m‖ ≤ C * ((m.1 : ℝ) + 1) ^ N * Real.exp (-(2 * Real.pi * y * (m.1 : ℝ))))
    (k l : ℕ) :
    Summable fun m : Set.Ici k₀ => (SchwartzMap.seminorm ℂ k l) (c m • u m) := by
  obtain ⟨Cu, Nu, hCu, hu⟩ := hu k l
  obtain ⟨Cc, Nc, hCc, hc⟩ := hc
  have hA : ∀ m : Set.Ici k₀,
      ((SchwartzMap.seminorm ℂ k l) (c m • u m) : ℝ) ≤
        (Cu * Cc) * ((m.1 : ℝ) + 1) ^ (Nu + Nc)
          * Real.exp (-(2 * Real.pi * y * (m.1 : ℝ))) := by
    intro m
    rw [map_smul_eq_mul]
    have hpos : (0 : ℝ) ≤ ((m.1 : ℝ) + 1) := by positivity
    calc ‖c m‖ * ((SchwartzMap.seminorm ℂ k l) (u m) : ℝ)
        ≤ (Cc * ((m.1 : ℝ) + 1) ^ Nc * Real.exp (-(2 * Real.pi * y * (m.1 : ℝ))))
            * (Cu * ((m.1 : ℝ) + 1) ^ Nu) := by
          refine mul_le_mul (hc m) (hu m) (by positivity) (by positivity)
      _ = (Cu * Cc) * ((m.1 : ℝ) + 1) ^ (Nu + Nc)
            * Real.exp (-(2 * Real.pi * y * (m.1 : ℝ))) := by
          rw [pow_add]; ring
  have hbase : Summable fun m : Set.Ici k₀ =>
      ((m.1 : ℝ) + 1) ^ (Nu + Nc) * Real.exp (-(2 * Real.pi * y * (m.1 : ℝ))) := by
    refine SummableRealMulExpNeg (k₀ := k₀)
      (c := fun m : Set.Ici k₀ => ((m.1 : ℝ) + 1) ^ (Nu + Nc)) (N := Nu + Nc) (C := 1)
      zero_le_one (fun m => by positivity) (fun m => by simp) hy
  have hsum : Summable fun m : Set.Ici k₀ =>
      (Cu * Cc) * ((m.1 : ℝ) + 1) ^ (Nu + Nc)
        * Real.exp (-(2 * Real.pi * y * (m.1 : ℝ))) :=
    (hbase.mul_left (Cu * Cc)).congr fun m => by ring
  exact Summable.of_nonneg_of_le (fun m => by positivity) hA hsum

/-! ## The slash factor under `τ ↦ -1/τ` -/

/-- For `τ` in the upper half plane the base `i/τ` of the slash factor has positive real
part, so in particular its principal argument is not `π`. -/
lemma slashFactor_arg_ne_pi {n : ℕ} {τ : ℂ} (hτ : 0 < τ.im) :
    (Complex.I / τ).arg ≠ Real.pi := by
  intro h
  have hτ0 : τ ≠ 0 := by intro h0; rw [h0] at hτ; simp at hτ
  have hneg : (Complex.I / τ).re < 0 := (Complex.arg_eq_pi_iff.mp h).1
  have hpos : 0 < (Complex.I / τ).re := by
    rw [Complex.div_re, Complex.I_re, Complex.I_im]
    simp only [zero_mul, zero_div, one_mul, zero_add]
    exact div_pos hτ (Complex.normSq_pos.mpr hτ0)
  linarith

/-- `i / (-1/τ) = (i/τ)⁻¹` for `τ ≠ 0`. -/
lemma div_neg_inv_eq_inv (τ : ℂ) (hτ : τ ≠ 0) : Complex.I / (-1 / τ) = (Complex.I / τ)⁻¹ := by
  field_simp
  rw [sq, Complex.I_mul_I]
  norm_num

/-- The slash factor does not vanish on the upper half plane. -/
lemma slashFactor_ne_zero (n : ℕ) (τ : ℂ) (hτ : 0 < τ.im) : slashFactor n τ ≠ 0 := by
  have hτ0 : τ ≠ 0 := by intro h0; rw [h0] at hτ; simp at hτ
  rw [slashFactor]
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (div_ne_zero Complex.I_ne_zero hτ0))

/-- **The slash factor is inverted by `τ ↦ -1/τ`.** -/
lemma slashFactor_neg_inv {n : ℕ} (τ : ℂ) (hτ : 0 < τ.im) :
    slashFactor n (-1 / τ) = (slashFactor n τ)⁻¹ := by
  have hτ0 : τ ≠ 0 := by intro h0; rw [h0] at hτ; simp at hτ
  have harg := slashFactor_arg_ne_pi (n := n) hτ
  rw [slashFactor, div_neg_inv_eq_inv τ hτ0, Complex.inv_cpow _ _ harg]
  rfl

/-- **The product of the slash factors at `τ` and at `-1/τ` is one.** -/
lemma slashFactor_mul_neg_inv {n : ℕ} (τ : ℂ) (hτ : 0 < τ.im) :
    slashFactor n τ * slashFactor n (-1 / τ) = 1 := by
  rw [slashFactor_neg_inv (n := n) τ hτ, mul_inv_cancel₀ (slashFactor_ne_zero n τ hτ)]

/-- The value of a radial function is controlled by its zeroth radial derivative. -/
lemma norm_apply_le_of_radial {n : ℕ} [NeZero n] {g : E n → ℂ} (hg : Radial g)
    {C : ℝ} (h : ∀ x : E n, ‖radialDeriv 0 g x‖ ≤ C) (x : E n) : ‖g x‖ ≤ C := by
  have h0 : radialDeriv 0 g x = g (realIncl (n := n) ‖x‖) := by
    rw [radialDeriv, iteratedDeriv_zero]
  have heq : g (realIncl (n := n) ‖x‖) = g x :=
    hg _ _ (by rw [Work.Sampling.realIncl_norm, abs_of_nonneg (norm_nonneg x)])
  rw [← heq, ← h0]
  exact h x

end

end Work.FunctionalEquations
