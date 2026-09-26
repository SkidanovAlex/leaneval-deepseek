import Mathlib
import Submission.Work.FunctionalEquations.Gen
import Submission.Work.FunctionalEquations.PeriodicAddSmul
import Submission.Work.FunctionalEquations.EqZeroOfTsumExp
import Submission.Work.FunctionalEquations.CoefficientValuePattern
import Submission.Work.FunctionalEquations.GenSummableMulExpNeg
import Submission.Work.FunctionalEquations.GenEqZeroOfTsumExp

/-!
# The value/derivative pattern of the general-`k₀` interpolation basis (CKMRV, Section 8)

This is `Work.FunctionalEquations.CoefficientValuePattern` with the index set
`Set.Ici 1` replaced by the general `Set.Ici k₀`, `k₀ ≥ 1`, which is the form needed
for the Leech lattice (`k₀ = 2`): the interpolation basis constructed from an
`InterpolationSolutionGen n k₀` satisfies the Kronecker delta pattern

* `a_m(√(2k)) = δ_{km}`, `ã_m(√(2k)) = b_m(√(2k)) = b̃_m(√(2k)) = 0`;
* `D a_m(√(2k)) = D ã_m(√(2k)) = D b̃_m(√(2k)) = 0`, `D b_m(√(2k)) = δ_{km}`

for all `m, k ≥ k₀`.  The proof is the one of the paper (and of
`CoefficientValuePattern`): evaluate the four Fourier expansions of `F`, `F̃` and their
radial derivatives at the sample point `√(2k)`, compare the identity at `τ` and `τ + 1`
to split the periodic part `A` off the `τ · B` part, and recover the coefficients by
Fourier orthogonality on the line `Im τ = 1`.

The two analytic inputs, in their `Set.Ici k₀` form, are
`Work.FunctionalEquations.GenSummableMulExpNeg` and
`Work.FunctionalEquations.GenEqZeroOfTsumExp`.
-/

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

section GenHelpers

variable {k₀ : ℕ}

/-- The rate `√(2m)` is nonzero for every index `m ≥ k₀ ≥ 1`. -/
lemma rate_ne_zero_gen (hk : 1 ≤ k₀) (m : Set.Ici k₀) : (rate m.1 : ℂ) ≠ 0 := by
  have h : 0 < rate m.1 := rate_pos m.1 (le_trans hk m.2)
  rw [← Complex.ofReal_zero, Ne, Complex.ofReal_inj]
  exact ne_of_gt h

/-- A Dirichlet series indexed by `Set.Ici k₀` is `1`-periodic. -/
lemma periodic_tsum_gen (c : Set.Ici k₀ → ℂ) (τ : ℂ) :
    (∑' m : Set.Ici k₀, c m * dirichletTerm m.1 (τ + 1))
      = ∑' m : Set.Ici k₀, c m * dirichletTerm m.1 τ :=
  tsum_congr fun m => by rw [dirichletTerm_add_one]

/-- A series with a single nonzero coefficient: `∑_m δ_{km} a e^{2π i m τ} = a e^{2π i k τ}`. -/
lemma tsum_dirichletTerm_delta_gen (k : Set.Ici k₀) (a : ℂ) (τ : ℂ) :
    (∑' m : Set.Ici k₀, (if k = m then a else 0) * dirichletTerm m.1 τ)
      = a * dirichletTerm k.1 τ := by
  rw [tsum_eq_single k]
  · rw [if_pos rfl]
  · intro m hm
    rw [if_neg (fun h => hm h.symm), zero_mul]

/-- The series on the line `Im τ = 1`, in the form used by `GenEqZeroOfTsumExp`. -/
lemma tsum_form_eq_gen (c : Set.Ici k₀ → ℂ) (t : ℝ) :
    (∑' m : Set.Ici k₀, c m * dirichletTerm m.1 ((t:ℂ) + ((1:ℝ):ℂ)*Complex.I))
      = ∑' m : Set.Ici k₀, c m * Complex.exp (2 * (Real.pi:ℂ) * Complex.I * (m.1:ℝ)
          * ((t:ℂ) + ((1:ℝ):ℂ)*Complex.I)) :=
  tsum_congr fun m => by rw [dirichletTerm_ofReal]

/-- The difference of two polynomially bounded families is polynomially bounded. -/
lemma polyBoundSubGen {c c' : Set.Ici k₀ → ℂ} {N N' : ℕ} {C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (h : ∀ m, ‖c m‖ ≤ C * ((m.1:ℝ)+1)^N) (h' : ∀ m, ‖c' m‖ ≤ C' * ((m.1:ℝ)+1)^N') :
    ∀ m, ‖c m - c' m‖ ≤ (C + C') * ((m.1:ℝ)+1)^(max N N') := by
  intro m
  have h1 : (1:ℝ) ≤ (m.1:ℝ) + 1 := by
    have : (0:ℝ) ≤ (m.1:ℝ) := Nat.cast_nonneg _
    linarith
  have hN : ((m.1:ℝ)+1)^N ≤ ((m.1:ℝ)+1)^(max N N') :=
    pow_le_pow_right₀ h1 (le_max_left _ _)
  have hN' : ((m.1:ℝ)+1)^N' ≤ ((m.1:ℝ)+1)^(max N N') :=
    pow_le_pow_right₀ h1 (le_max_right _ _)
  calc ‖c m - c' m‖ ≤ ‖c m‖ + ‖c' m‖ := norm_sub_le _ _
    _ ≤ C * ((m.1:ℝ)+1)^N + C' * ((m.1:ℝ)+1)^N' := add_le_add (h m) (h' m)
    _ ≤ C * ((m.1:ℝ)+1)^(max N N') + C' * ((m.1:ℝ)+1)^(max N N') :=
        add_le_add (mul_le_mul_of_nonneg_left hN hC) (mul_le_mul_of_nonneg_left hN' hC')
    _ = (C + C') * ((m.1:ℝ)+1)^(max N N') := by ring

/-- Polynomial growth of a family makes the associated Dirichlet series absolutely
summable on every horizontal line of the upper half plane. -/
lemma summable_dirichletTerm_mul_gen {c : Set.Ici k₀ → ℂ}
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ m, ‖c m‖ ≤ C * ((m.1:ℝ)+1)^N)
    {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun m : Set.Ici k₀ => c m * dirichletTerm m.1 τ := by
  obtain ⟨C, hC, N, hbd⟩ := hb
  set x : Set.Ici k₀ → ℝ := fun m => 2 * Real.pi * τ.im * (m.1:ℝ) with hx
  have hcplx : Summable fun m : Set.Ici k₀ =>
      (‖c m‖ : ℂ) * Complex.exp (-(x m : ℂ)) := by
    have h := GenSummableMulExpNeg (c := fun m : Set.Ici k₀ => (‖c m‖ : ℂ)) hC hτ (fun m => by
      rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
      exact hbd m)
    refine h.congr fun m => ?_
    congr 2
    rw [hx]
    push_cast
    ring
  have hre : Summable fun m : Set.Ici k₀ => ((‖c m‖ : ℂ) * Complex.exp (-(x m : ℂ))).re :=
    ((Complex.hasSum_iff _ _).mp hcplx.hasSum).1.summable
  have hreal : Summable fun m : Set.Ici k₀ => ‖c m‖ * Real.exp (-(x m)) := by
    refine hre.congr fun m => ?_
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, ← Complex.ofReal_neg,
      Complex.exp_ofReal_re, zero_mul, sub_zero]
  exact Summable.of_norm_bounded hreal (fun m => by
    rw [norm_mul, norm_dirichletTerm, hx])

/-- **Uniqueness of Dirichlet series, coefficient form.**  A polynomially bounded family
whose Dirichlet series vanishes on the whole upper half plane is identically zero. -/
lemma coeffs_eq_zero_of_tsum_zero_gen {c : Set.Ici k₀ → ℂ}
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ m, ‖c m‖ ≤ C * ((m.1:ℝ)+1)^N)
    (hzero : ∀ τ : ℂ, 0 < τ.im → ∑' m : Set.Ici k₀, c m * dirichletTerm m.1 τ = 0) :
    ∀ m, c m = 0 := by
  obtain ⟨C, hC, N, hbd⟩ := hb
  have hsum : Summable fun m : Set.Ici k₀ =>
      c m * Complex.exp (-(2 * (Real.pi:ℂ) * ((1:ℝ):ℂ) * (m.1:ℝ))) :=
    GenSummableMulExpNeg (c := c) hC one_pos hbd
  refine GenEqZeroOfTsumExp (c := c) one_pos hsum fun t => ?_
  have hτ : 0 < ((t:ℂ) + ((1:ℝ):ℂ) * Complex.I).im := by simp
  rw [← tsum_form_eq_gen c t, hzero _ hτ]

/-- Two polynomially bounded Dirichlet series that agree on the upper half plane have the
same coefficients. -/
lemma coeffs_eq_of_tsum_eq_gen {c c' : Set.Ici k₀ → ℂ}
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ m, ‖c m‖ ≤ C * ((m.1:ℝ)+1)^N)
    (hb' : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ m, ‖c' m‖ ≤ C * ((m.1:ℝ)+1)^N)
    (heq : ∀ τ : ℂ, 0 < τ.im → ∑' m : Set.Ici k₀, c m * dirichletTerm m.1 τ
        = ∑' m : Set.Ici k₀, c' m * dirichletTerm m.1 τ) :
    ∀ m, c m = c' m := by
  obtain ⟨C, hC, N, hbd⟩ := hb
  obtain ⟨C', hC', N', hbd'⟩ := hb'
  have hsub : ∀ m, ‖c m - c' m‖ ≤ (C + C') * ((m.1:ℝ)+1)^(max N N') :=
    polyBoundSubGen hC hC' hbd hbd'
  have hzero : ∀ m, c m - c' m = 0 := by
    refine coeffs_eq_zero_of_tsum_zero_gen
      ⟨C + C', add_nonneg hC hC', max N N', hsub⟩ ?_
    intro τ hτ
    have hc : Summable fun m : Set.Ici k₀ => c m * dirichletTerm m.1 τ :=
      summable_dirichletTerm_mul_gen ⟨C, hC, N, hbd⟩ hτ
    have hc' : Summable fun m : Set.Ici k₀ => c' m * dirichletTerm m.1 τ :=
      summable_dirichletTerm_mul_gen ⟨C', hC', N', hbd'⟩ hτ
    rw [show (fun m : Set.Ici k₀ => (c m - c' m) * dirichletTerm m.1 τ)
        = (fun m : Set.Ici k₀ => c m * dirichletTerm m.1 τ
            - c' m * dirichletTerm m.1 τ) from funext fun m => by ring]
    rw [hc.tsum_sub hc', heq τ hτ, sub_self]
  intro m
  exact sub_eq_zero.mp (hzero m)

/-! ## Polynomial growth of the basis at a sample point -/

/-- The values of the four basis families at a sample point grow at most polynomially. -/
lemma value_bound_gen {n : ℕ} [NeZero n] (S : InterpolationSolutionGen n k₀)
    (k : Set.Ici k₀) (j : Fin 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ m : Set.Ici k₀,
      ‖(S.basis (m, j)).1 (samplePoint (n := n) (k.1 : ℝ))‖ ≤ C * ((m.1:ℝ)+1)^N := by
  obtain ⟨C, N, hC, h⟩ := S.growth_radial 0 0
  refine ⟨C, hC, N, fun m => ?_⟩
  have hx := h m j (samplePoint (n := n) (k.1 : ℝ))
  rw [pow_zero, one_mul] at hx
  rw [radialDeriv_zero_apply (⇑(S.basis (m, j)).1) (samplePoint (n := n) (k.1 : ℝ))
    (realIncl_norm_samplePoint (n := n) (k.1 : ℝ))] at hx
  exact hx

/-- The first radial derivatives of the four basis families at a sample point grow at
most polynomially. -/
lemma deriv_bound_gen {n : ℕ} [NeZero n] (S : InterpolationSolutionGen n k₀)
    (k : Set.Ici k₀) (j : Fin 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ m : Set.Ici k₀,
      ‖radialDeriv 1 (⇑(S.basis (m, j)).1) (samplePoint (n := n) (k.1 : ℝ))‖
        ≤ C * ((m.1:ℝ)+1)^N := by
  obtain ⟨C, N, hC, h⟩ := S.growth_radial 0 1
  refine ⟨C, hC, N, fun m => ?_⟩
  have hx := h m j (samplePoint (n := n) (k.1 : ℝ))
  rw [pow_zero, one_mul] at hx
  exact hx

/-- Multiplying a polynomially bounded family by the rate preserves polynomial bounds. -/
lemma rate_mul_bound_gen {v : Set.Ici k₀ → ℂ} {C : ℝ} {N : ℕ}
    (h : ∀ m, ‖v m‖ ≤ C * ((m.1:ℝ)+1)^N) :
    ∀ m, ‖(rate m.1 : ℂ) * v m‖ ≤ C * ((m.1:ℝ)+1)^(N+1) := by
  intro m
  have hr : 0 ≤ rate m.1 := Real.sqrt_nonneg _
  have hrle : rate m.1 ≤ (m.1:ℝ) + 1 := rate_le _
  have hpos : (0:ℝ) ≤ (m.1:ℝ) + 1 := by
    have : (0:ℝ) ≤ (m.1:ℝ) := Nat.cast_nonneg _
    linarith
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]
  calc rate m.1 * ‖v m‖ ≤ ((m.1:ℝ)+1) * (C * ((m.1:ℝ)+1)^N) :=
        mul_le_mul hrle (h m) (norm_nonneg _) hpos
    _ = C * ((m.1:ℝ)+1)^(N+1) := by rw [pow_succ]; ring

/-- The rate-weighted values of the basis families grow at most polynomially. -/
lemma rate_value_bound_gen {n : ℕ} [NeZero n] (S : InterpolationSolutionGen n k₀)
    (k : Set.Ici k₀) (j : Fin 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ m : Set.Ici k₀,
      ‖(rate m.1 : ℂ) * (S.basis (m, j)).1 (samplePoint (n := n) (k.1 : ℝ))‖
        ≤ C * ((m.1:ℝ)+1)^N := by
  obtain ⟨C, hC, N, h⟩ := value_bound_gen S k j
  exact ⟨C, hC, N+1, rate_mul_bound_gen h⟩

/-- The rate-weighted first radial derivatives of the basis families grow at most
polynomially. -/
lemma rate_deriv_bound_gen {n : ℕ} [NeZero n] (S : InterpolationSolutionGen n k₀)
    (k : Set.Ici k₀) (j : Fin 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ m : Set.Ici k₀,
      ‖(rate m.1 : ℂ) * radialDeriv 1 (⇑(S.basis (m, j)).1) (samplePoint (n := n) (k.1 : ℝ))‖
        ≤ C * ((m.1:ℝ)+1)^N := by
  obtain ⟨C, hC, N, h⟩ := deriv_bound_gen S k j
  exact ⟨C, hC, N+1, rate_mul_bound_gen h⟩

/-- The Kronecker delta family is polynomially bounded. -/
lemma delta_bound_gen (k : Set.Ici k₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ m : Set.Ici k₀,
      ‖(if k = m then (1:ℂ) else 0)‖ ≤ C * ((m.1:ℝ)+1)^N := by
  refine ⟨1, zero_le_one, 0, fun m => ?_⟩
  by_cases h : k = m <;> simp [h]

/-- The rate-weighted Kronecker delta family is polynomially bounded. -/
lemma delta_rate_bound_gen (k : Set.Ici k₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ m : Set.Ici k₀,
      ‖(if k = m then (rate k.1 : ℂ) else 0)‖ ≤ C * ((m.1:ℝ)+1)^N := by
  have hr : 0 ≤ rate k.1 := rate_nonneg _
  refine ⟨rate k.1, hr, 0, fun m => ?_⟩
  by_cases h : k = m
  · rw [if_pos h, Complex.norm_real, Real.norm_of_nonneg hr]
    simp
  · rw [if_neg h]
    simp only [norm_zero, pow_zero, mul_one]
    exact hr

/-! ## The Kronecker delta pattern -/

/-- **The value and radial-derivative pattern at a fixed sample radius.**  For every
`k ≥ k₀` the four basis families, evaluated (together with their first radial derivative)
at the sample point `√(2k)`, produce the four Kronecker deltas. -/
lemma value_pattern_at_gen {n : ℕ} [NeZero n] {k₀ : ℕ} (hk : 1 ≤ k₀)
    (S : InterpolationSolutionGen n k₀) (k : Set.Ici k₀) :
    (∀ m : Set.Ici k₀,
        (S.basis (m, 0)).1 (samplePoint (n := n) (k.1 : ℝ)) = (if k = m then 1 else 0)) ∧
    (∀ m : Set.Ici k₀, (S.basis (m, 1)).1 (samplePoint (n := n) (k.1 : ℝ)) = 0) ∧
    (∀ m : Set.Ici k₀, (S.basis (m, 2)).1 (samplePoint (n := n) (k.1 : ℝ)) = 0) ∧
    (∀ m : Set.Ici k₀, (S.basis (m, 3)).1 (samplePoint (n := n) (k.1 : ℝ)) = 0) ∧
    (∀ m : Set.Ici k₀,
        radialDeriv 1 (⇑(S.basis (m, 0)).1) (samplePoint (n := n) (k.1 : ℝ)) = 0) ∧
    (∀ m : Set.Ici k₀,
        radialDeriv 1 (⇑(S.basis (m, 1)).1) (samplePoint (n := n) (k.1 : ℝ)) = 0) ∧
    (∀ m : Set.Ici k₀,
        radialDeriv 1 (⇑(S.basis (m, 2)).1) (samplePoint (n := n) (k.1 : ℝ))
          = (if k = m then 1 else 0)) ∧
    (∀ m : Set.Ici k₀,
        radialDeriv 1 (⇑(S.basis (m, 3)).1) (samplePoint (n := n) (k.1 : ℝ)) = 0) := by
  classical
  set xk : E n := samplePoint (n := n) (k.1 : ℝ) with hxk
  have h2pii : 2 * (Real.pi:ℂ) * Complex.I ≠ 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  -- ### Splitting 1 : the expansion of `F` at `x_k`
  have hsplit1 : ∀ τ : ℂ, 0 < τ.im →
      (∑' m : Set.Ici k₀, (rate m.1 : ℂ) * (S.basis (m,2)).1 xk * dirichletTerm m.1 τ) = 0 ∧
      (∑' m : Set.Ici k₀, (S.basis (m,0)).1 xk * dirichletTerm m.1 τ)
        = dirichletTerm k.1 τ := by
    have h := periodic_split_UHP
      (A₁ := fun τ : ℂ => ∑' m : Set.Ici k₀, (S.basis (m,0)).1 xk * dirichletTerm m.1 τ)
      (A₂ := fun τ : ℂ => dirichletTerm k.1 τ)
      (B₁ := fun τ : ℂ => 2 * (Real.pi:ℂ) * Complex.I *
        (∑' m : Set.Ici k₀, (rate m.1 : ℂ) * (S.basis (m,2)).1 xk * dirichletTerm m.1 τ))
      (B₂ := fun _ : ℂ => 0)
      (fun τ _ => periodic_tsum_gen _ τ)
      (fun τ _ => dirichletTerm_add_one k.1 τ)
      (fun τ _ => by rw [periodic_tsum_gen
        (fun m : Set.Ici k₀ => (rate m.1 : ℂ) * (S.basis (m,2)).1 xk) τ])
      (fun _ _ => rfl)
      (fun τ hτ => by
        show (∑' m : Set.Ici k₀, (S.basis (m,0)).1 xk * dirichletTerm m.1 τ)
            + τ * (2 * (Real.pi:ℂ) * Complex.I *
              (∑' m : Set.Ici k₀, (rate m.1 : ℂ) * (S.basis (m,2)).1 xk * dirichletTerm m.1 τ))
          = dirichletTerm k.1 τ + τ * (0:ℂ)
        have h1 := S.expansion_F τ xk hτ
        have h2 := S.value_F k τ hτ
        linear_combination h2 - h1)
    intro τ hτ
    obtain ⟨hb, ha⟩ := h τ hτ
    exact ⟨(mul_eq_zero.mp hb).resolve_left h2pii, ha⟩
  -- ### Splitting 2 : the expansion of `F̃` at `x_k`
  have hsplit2 : ∀ τ : ℂ, 0 < τ.im →
      (∑' m : Set.Ici k₀, (rate m.1 : ℂ) * (S.basis (m,3)).1 xk * dirichletTerm m.1 τ) = 0 ∧
      (∑' m : Set.Ici k₀, (S.basis (m,1)).1 xk * dirichletTerm m.1 τ) = 0 := by
    have h := periodic_split_UHP
      (A₁ := fun τ : ℂ => ∑' m : Set.Ici k₀, (S.basis (m,1)).1 xk * dirichletTerm m.1 τ)
      (A₂ := fun _ : ℂ => 0)
      (B₁ := fun τ : ℂ => 2 * (Real.pi:ℂ) * Complex.I *
        (∑' m : Set.Ici k₀, (rate m.1 : ℂ) * (S.basis (m,3)).1 xk * dirichletTerm m.1 τ))
      (B₂ := fun _ : ℂ => 0)
      (fun τ _ => periodic_tsum_gen _ τ)
      (fun _ _ => rfl)
      (fun τ _ => by rw [periodic_tsum_gen
        (fun m : Set.Ici k₀ => (rate m.1 : ℂ) * (S.basis (m,3)).1 xk) τ])
      (fun _ _ => rfl)
      (fun τ hτ => by
        show (∑' m : Set.Ici k₀, (S.basis (m,1)).1 xk * dirichletTerm m.1 τ)
            + τ * (2 * (Real.pi:ℂ) * Complex.I *
              (∑' m : Set.Ici k₀, (rate m.1 : ℂ) * (S.basis (m,3)).1 xk * dirichletTerm m.1 τ))
          = (0:ℂ) + τ * (0:ℂ)
        have h1 := S.expansion_Ftilde τ xk hτ
        have h2 := S.value_Ftilde k τ hτ
        linear_combination h2 - h1)
    intro τ hτ
    obtain ⟨hb, ha⟩ := h τ hτ
    exact ⟨(mul_eq_zero.mp hb).resolve_left h2pii, ha⟩
  -- ### Splitting 3 : the radial derivative of the expansion of `F` at `x_k`
  have hsplit3 : ∀ τ : ℂ, 0 < τ.im →
      (∑' m : Set.Ici k₀,
          (rate m.1 : ℂ) * radialDeriv 1 (⇑(S.basis (m,2)).1) xk * dirichletTerm m.1 τ)
        = (rate k.1 : ℂ) * dirichletTerm k.1 τ ∧
      (∑' m : Set.Ici k₀, radialDeriv 1 (⇑(S.basis (m,0)).1) xk * dirichletTerm m.1 τ)
        = 0 := by
    have h := periodic_split_UHP
      (A₁ := fun τ : ℂ => ∑' m : Set.Ici k₀,
        radialDeriv 1 (⇑(S.basis (m,0)).1) xk * dirichletTerm m.1 τ)
      (A₂ := fun _ : ℂ => 0)
      (B₁ := fun τ : ℂ => 2 * (Real.pi:ℂ) * Complex.I *
        (∑' m : Set.Ici k₀,
          (rate m.1 : ℂ) * radialDeriv 1 (⇑(S.basis (m,2)).1) xk * dirichletTerm m.1 τ))
      (B₂ := fun τ : ℂ => 2 * (Real.pi:ℂ) * Complex.I * ((rate k.1 : ℂ) * dirichletTerm k.1 τ))
      (fun τ _ => periodic_tsum_gen _ τ)
      (fun _ _ => rfl)
      (fun τ _ => by rw [periodic_tsum_gen
        (fun m : Set.Ici k₀ =>
          (rate m.1 : ℂ) * radialDeriv 1 (⇑(S.basis (m,2)).1) xk) τ])
      (fun τ _ => by rw [dirichletTerm_add_one])
      (fun τ hτ => by
        show (∑' m : Set.Ici k₀, radialDeriv 1 (⇑(S.basis (m,0)).1) xk * dirichletTerm m.1 τ)
            + τ * (2 * (Real.pi:ℂ) * Complex.I *
              (∑' m : Set.Ici k₀,
                (rate m.1 : ℂ) * radialDeriv 1 (⇑(S.basis (m,2)).1) xk * dirichletTerm m.1 τ))
          = (0:ℂ) + τ * (2 * (Real.pi:ℂ) * Complex.I * ((rate k.1 : ℂ) * dirichletTerm k.1 τ))
        have h1 := S.expansion_F_radialDeriv 1 τ xk hτ
        have h2 := S.value_radialDeriv_F k τ hτ
        linear_combination h2 - h1)
    intro τ hτ
    obtain ⟨hb, ha⟩ := h τ hτ
    exact ⟨mul_left_cancel₀ h2pii hb, ha⟩
  -- ### Splitting 4 : the radial derivative of the expansion of `F̃` at `x_k`
  have hsplit4 : ∀ τ : ℂ, 0 < τ.im →
      (∑' m : Set.Ici k₀,
          (rate m.1 : ℂ) * radialDeriv 1 (⇑(S.basis (m,3)).1) xk * dirichletTerm m.1 τ) = 0 ∧
      (∑' m : Set.Ici k₀,
          radialDeriv 1 (⇑(S.basis (m,1)).1) xk * dirichletTerm m.1 τ) = 0 := by
    have h := periodic_split_UHP
      (A₁ := fun τ : ℂ => ∑' m : Set.Ici k₀,
        radialDeriv 1 (⇑(S.basis (m,1)).1) xk * dirichletTerm m.1 τ)
      (A₂ := fun _ : ℂ => 0)
      (B₁ := fun τ : ℂ => 2 * (Real.pi:ℂ) * Complex.I *
        (∑' m : Set.Ici k₀,
          (rate m.1 : ℂ) * radialDeriv 1 (⇑(S.basis (m,3)).1) xk * dirichletTerm m.1 τ))
      (B₂ := fun _ : ℂ => 0)
      (fun τ _ => periodic_tsum_gen _ τ)
      (fun _ _ => rfl)
      (fun τ _ => by rw [periodic_tsum_gen
        (fun m : Set.Ici k₀ =>
          (rate m.1 : ℂ) * radialDeriv 1 (⇑(S.basis (m,3)).1) xk) τ])
      (fun _ _ => rfl)
      (fun τ hτ => by
        show (∑' m : Set.Ici k₀, radialDeriv 1 (⇑(S.basis (m,1)).1) xk * dirichletTerm m.1 τ)
            + τ * (2 * (Real.pi:ℂ) * Complex.I *
              (∑' m : Set.Ici k₀,
                (rate m.1 : ℂ) * radialDeriv 1 (⇑(S.basis (m,3)).1) xk * dirichletTerm m.1 τ))
          = (0:ℂ) + τ * (0:ℂ)
        have h1 := S.expansion_Ftilde_radialDeriv 1 τ xk hτ
        have h2 := S.value_radialDeriv_Ftilde k τ hτ
        linear_combination h2 - h1)
    intro τ hτ
    obtain ⟨hb, ha⟩ := h τ hτ
    exact ⟨(mul_eq_zero.mp hb).resolve_left h2pii, ha⟩
  -- ### Extraction of the eight coefficient identities
  have hA : ∀ m : Set.Ici k₀, (S.basis (m,0)).1 xk = (if k = m then 1 else 0) := by
    refine coeffs_eq_of_tsum_eq_gen
      (c := fun m : Set.Ici k₀ => (S.basis (m,0)).1 xk)
      (c' := fun m : Set.Ici k₀ => if k = m then (1:ℂ) else 0)
      (value_bound_gen S k 0) (delta_bound_gen k) ?_
    intro τ hτ
    rw [tsum_dirichletTerm_delta_gen k (1:ℂ) τ, one_mul, ← (hsplit1 τ hτ).2]
  have hB : ∀ m : Set.Ici k₀, (S.basis (m,2)).1 xk = 0 := by
    have h := coeffs_eq_zero_of_tsum_zero_gen
      (c := fun m : Set.Ici k₀ => (rate m.1 : ℂ) * (S.basis (m,2)).1 xk)
      (rate_value_bound_gen S k 2) (fun τ hτ => (hsplit1 τ hτ).1)
    intro m
    exact (mul_eq_zero.mp (h m)).resolve_left (rate_ne_zero_gen hk m)
  have hC : ∀ m : Set.Ici k₀, (S.basis (m,1)).1 xk = 0 :=
    coeffs_eq_zero_of_tsum_zero_gen
      (c := fun m : Set.Ici k₀ => (S.basis (m,1)).1 xk)
      (value_bound_gen S k 1) (fun τ hτ => (hsplit2 τ hτ).2)
  have hD : ∀ m : Set.Ici k₀, (S.basis (m,3)).1 xk = 0 := by
    have h := coeffs_eq_zero_of_tsum_zero_gen
      (c := fun m : Set.Ici k₀ => (rate m.1 : ℂ) * (S.basis (m,3)).1 xk)
      (rate_value_bound_gen S k 3) (fun τ hτ => (hsplit2 τ hτ).1)
    intro m
    exact (mul_eq_zero.mp (h m)).resolve_left (rate_ne_zero_gen hk m)
  have hE : ∀ m : Set.Ici k₀, radialDeriv 1 (⇑(S.basis (m,0)).1) xk = 0 :=
    coeffs_eq_zero_of_tsum_zero_gen
      (c := fun m : Set.Ici k₀ => radialDeriv 1 (⇑(S.basis (m,0)).1) xk)
      (deriv_bound_gen S k 0) (fun τ hτ => (hsplit3 τ hτ).2)
  have hF : ∀ m : Set.Ici k₀, radialDeriv 1 (⇑(S.basis (m,2)).1) xk
      = (if k = m then 1 else 0) := by
    have h := coeffs_eq_of_tsum_eq_gen
      (c := fun m : Set.Ici k₀ => (rate m.1 : ℂ) * radialDeriv 1 (⇑(S.basis (m,2)).1) xk)
      (c' := fun m : Set.Ici k₀ => if k = m then (rate k.1 : ℂ) else 0)
      (rate_deriv_bound_gen S k 2) (delta_rate_bound_gen k)
      (fun τ hτ => by
        rw [tsum_dirichletTerm_delta_gen k (rate k.1) τ]
        exact (hsplit3 τ hτ).1)
    intro m
    have hm := h m
    by_cases hkm : k = m
    · subst hkm
      rw [if_pos rfl] at hm ⊢
      exact mul_left_cancel₀ (rate_ne_zero_gen hk k) (by rw [hm, mul_one])
    · rw [if_neg hkm] at hm ⊢
      exact (mul_eq_zero.mp hm).resolve_left (rate_ne_zero_gen hk m)
  have hG : ∀ m : Set.Ici k₀, radialDeriv 1 (⇑(S.basis (m,1)).1) xk = 0 :=
    coeffs_eq_zero_of_tsum_zero_gen
      (c := fun m : Set.Ici k₀ => radialDeriv 1 (⇑(S.basis (m,1)).1) xk)
      (deriv_bound_gen S k 1) (fun τ hτ => (hsplit4 τ hτ).2)
  have hH : ∀ m : Set.Ici k₀, radialDeriv 1 (⇑(S.basis (m,3)).1) xk = 0 := by
    have h := coeffs_eq_zero_of_tsum_zero_gen
      (c := fun m : Set.Ici k₀ => (rate m.1 : ℂ) * radialDeriv 1 (⇑(S.basis (m,3)).1) xk)
      (rate_deriv_bound_gen S k 3) (fun τ hτ => (hsplit4 τ hτ).1)
    intro m
    exact (mul_eq_zero.mp (h m)).resolve_left (rate_ne_zero_gen hk m)
  exact ⟨hA, hC, hB, hD, hE, hG, hF, hH⟩

end GenHelpers

/-- **The value/derivative pattern of the general-`k₀` interpolation basis (CKMRV,
Section 8).**  At the sample point of index `k ≥ k₀` the four coefficient families of an
interpolation solution have the values and radial derivatives of the Kronecker delta. -/
theorem ValuePatternGen {n : ℕ} [NeZero n] {k₀ : ℕ} (hk : 1 ≤ k₀)
    (S : InterpolationSolutionGen n k₀) :
    ∀ (m k : Set.Ici k₀),
      (S.basis (m, 0)).1 (samplePoint (n := n) (k.1 : ℝ)) = (if k = m then 1 else 0) ∧
      (S.basis (m, 1)).1 (samplePoint (n := n) (k.1 : ℝ)) = 0 ∧
      (S.basis (m, 2)).1 (samplePoint (n := n) (k.1 : ℝ)) = 0 ∧
      (S.basis (m, 3)).1 (samplePoint (n := n) (k.1 : ℝ)) = 0 ∧
      radialDeriv 1 (⇑(S.basis (m, 0)).1) (samplePoint (n := n) (k.1 : ℝ)) = 0 ∧
      radialDeriv 1 (⇑(S.basis (m, 1)).1) (samplePoint (n := n) (k.1 : ℝ)) = 0 ∧
      radialDeriv 1 (⇑(S.basis (m, 2)).1) (samplePoint (n := n) (k.1 : ℝ))
        = (if k = m then 1 else 0) ∧
      radialDeriv 1 (⇑(S.basis (m, 3)).1) (samplePoint (n := n) (k.1 : ℝ)) = 0 := by
  intro m k
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := value_pattern_at_gen hk S k
  exact ⟨h0 m, h1 m, h2 m, h3 m, h4 m, h5 m, h6 m, h7 m⟩

end

end Work.FunctionalEquations
