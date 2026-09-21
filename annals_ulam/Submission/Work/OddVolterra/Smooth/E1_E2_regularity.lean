import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Smooth.Slice
import Submission.Work.OddVolterra.Smooth.ParametricIntegral
import Submission.Work.OddVolterra.Existence.E1_E2_contDiff
import Submission.Work.Analysis.Calculus.iteratedDeriv_eq_zero_of_eq_zero_on_subinterval
import Submission.Work.Analysis.Calculus.parametric_iteratedDeriv_bound

/-!
# Regularity of the odd-case inhomogeneities `E₁`, `E₂`

`E₁ n h s = ∫_t ∂_u^{n+1} (ψ(u,t)^n √(ψ(u,t)))|_{u=s}` is an integral over the fixed
interval `[-profileX 1, profileX 1]`, where `ψ(u,t) = semicircle t ^ 2 - (u t + h u) ^ 2`
vanishes at the two endpoints `t = ±profileX 1` when `s = 1`.  Hence the integrand is only
dominated by `ψ(s,t)^{-1/2}`, which is a *non-uniform* (but integrable) bound; the continuity
at `s = 1` is therefore genuinely a dominated-convergence statement.

The proof below
* bounds the slice derivatives of `ψ` uniformly (Faà di Bruno, with a constant uniform in the
  base value `ψ(s,t)`; see `iteratedDeriv_rpow_comp_bound_uniform`),
* rewrites the integral by the substitution `t = profileX 1 * sin θ`, which turns the singular
  weight into a bounded one,
* applies the dominated convergence theorem.
-/

namespace Work.OddVolterra.Smooth

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

noncomputable section

open Commons.Geometry.Ulam

/-! ## A Faà di Bruno bound uniform in the base value -/

private lemma iteratedDeriv_rpow_uniform (p ρ : ℝ) (k : ℕ) :
    iteratedDeriv k (fun y : ℝ => y ^ p) ρ = (descPochhammer ℝ k).eval p * ρ ^ (p - (k : ℝ)) := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]

private lemma abs_descPochhammer_eval_le_uniform (p : ℝ) {k n : ℕ} (hk : k ≤ n) :
    |(descPochhammer ℝ k).eval p| ≤ ∏ i ∈ Finset.range (n + 1), (1 + |p| + (i : ℝ)) := by
  rw [descPochhammer_eval_eq_prod_range, Finset.abs_prod]
  have h1 : ∏ i ∈ Finset.range k, |p - (i : ℝ)| ≤ ∏ i ∈ Finset.range k, (1 + |p| + (i : ℝ)) := by
    apply Finset.prod_le_prod₀ (f := fun i : ℕ => |p - (i : ℝ)|) (g := fun i : ℕ => 1 + |p| + (i : ℝ))
    · intro i _; exact abs_nonneg _
    · intro i _
      have hle : |p - (i : ℝ)| ≤ |p| + (i : ℝ) := by
        rw [abs_sub_le_iff]
        constructor
        · have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
          linarith [le_abs_self p]
        · linarith [neg_le_abs p]
      linarith
  have h2 : ∏ i ∈ Finset.range k, (1 + |p| + (i : ℝ))
      ≤ ∏ i ∈ Finset.range (n + 1), (1 + |p| + (i : ℝ)) := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro i _
      have h1 : (0 : ℝ) ≤ |p| := abs_nonneg p
      have h2 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith
    · intro i _ _
      have h1 : (0 : ℝ) ≤ |p| := abs_nonneg p
      have h2 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith
  exact le_trans h1 h2

/-- Faà di Bruno bound, uniform in the base value `c`: the `k`-th derivative of `x ↦ Φ x ^ p`
at `0` is bounded by `K * (1 + c ^ (p - k))` with a constant `K` depending only on `p`, on the
order bound `K₀` and on the size bound `C`, but *not* on the lower bound `c ≤ Φ 0`. -/
theorem iteratedDeriv_rpow_comp_bound_uniform (p : ℝ) (K₀ : ℕ) {C : ℝ} (hC : 1 ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (k : ℕ) (c : ℝ) (Φ : ℝ → ℝ), k ≤ K₀ → 0 < c → c ≤ 1 →
      ContDiffAt ℝ K₀ Φ 0 → c ≤ Φ 0 → Φ 0 ≤ C →
      (∀ j ≤ K₀, |iteratedDeriv j Φ 0| ≤ C) →
      |iteratedDeriv k (fun x : ℝ => (Φ x) ^ p) 0| ≤ K * (1 + c ^ (p - (k : ℝ))) := by
  classical
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hC
  have hmax1 : (1 : ℝ) ≤ max (C ^ p) 1 := le_max_right _ _
  have hmax0 : (0 : ℝ) ≤ max (C ^ p) 1 := le_trans zero_le_one hmax1
  set B : ℝ := ∏ i ∈ Finset.range (K₀ + 1), (1 + |p| + (i : ℝ)) with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]; exact Finset.prod_nonneg (fun i _ => by positivity)
  set N : ℝ := ∑ k ∈ Finset.range (K₀ + 1), (Fintype.card (OrderedFinpartition k) : ℝ) with hNdef
  have hNnn : 0 ≤ N := by
    rw [hNdef]; exact Finset.sum_nonneg (fun k _ => Nat.cast_nonneg _)
  have hNge : ∀ k ≤ K₀, (Fintype.card (OrderedFinpartition k) : ℝ) ≤ N := by
    intro k hk
    refine Finset.single_le_sum (f := fun k => (Fintype.card (OrderedFinpartition k) : ℝ))
      (fun i _ => Nat.cast_nonneg (Fintype.card (OrderedFinpartition i))) ?_
    simp only [Finset.mem_range]
    omega
  refine ⟨B * max (C ^ p) 1 * C ^ K₀ * N, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (mul_nonneg hBnn hmax0) (pow_nonneg hCpos.le _)) hNnn
  intro k c Φ hk hc hc1 hΦK hcΦ hΦC hderiv
  have hΦk : ContDiffAt ℝ k Φ 0 := hΦK.of_le (by exact_mod_cast hk)
  have hΦpos : 0 < Φ 0 := lt_of_lt_of_le hc hcΦ
  have hΦnn : 0 ≤ Φ 0 := hΦpos.le
  have hck0 : (0 : ℝ) ≤ c ^ (p - (k : ℝ)) := Real.rpow_nonneg hc.le _
  have h1c : (1 : ℝ) ≤ 1 + c ^ (p - (k : ℝ)) := by linarith
  have hfac0 : (0 : ℝ) ≤ B * max (C ^ p) 1 * (1 + c ^ (p - (k : ℝ))) :=
    mul_nonneg (mul_nonneg hBnn hmax0) (by linarith)
  have hfac1 : (0 : ℝ) ≤ B * max (C ^ p) 1 * C ^ K₀ * (1 + c ^ (p - (k : ℝ))) :=
    mul_nonneg (mul_nonneg (mul_nonneg hBnn hmax0) (pow_nonneg hCpos.le _)) (by linarith)
  have hg : ContDiffAt ℝ k (fun y : ℝ => y ^ p) (Φ 0) :=
    Real.contDiffAt_rpow_const (n := k) (Or.inl hΦpos.ne')
  have hcomp : iteratedDeriv k (fun x : ℝ => Φ x ^ p) 0
      = ∑ σ : OrderedFinpartition k, iteratedDeriv σ.length (fun y : ℝ => y ^ p) (Φ 0) *
          ∏ j : Fin σ.length, iteratedDeriv (σ.partSize j) Φ 0 := by
    have h := iteratedDeriv_comp_eq_sum_orderedFinpartition (𝕜 := ℝ)
      (g := fun y : ℝ => y ^ p) (f := Φ) (x := 0) (i := k) (n := (k : ℕ∞ω)) hg hΦk le_rfl
    simpa [Function.comp_def] using h
  have hterm : ∀ σ : OrderedFinpartition k,
      |iteratedDeriv σ.length (fun y : ℝ => y ^ p) (Φ 0) *
        ∏ j : Fin σ.length, iteratedDeriv (σ.partSize j) Φ 0|
      ≤ B * max (C ^ p) 1 * C ^ K₀ * (1 + c ^ (p - (k : ℝ))) := by
    intro σ
    have hmk : σ.length ≤ k := σ.length_le
    have hmK : σ.length ≤ K₀ := le_trans hmk hk
    have hmlen : ((σ.length : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
    have h2 : |∏ j : Fin σ.length, iteratedDeriv (σ.partSize j) Φ 0| ≤ C ^ σ.length := by
      rw [Finset.abs_prod]
      calc ∏ j : Fin σ.length, |iteratedDeriv (σ.partSize j) Φ 0|
          ≤ ∏ _j : Fin σ.length, C :=
            Finset.prod_le_prod₀ (fun j _ => abs_nonneg _)
              (fun j _ => hderiv _ (le_trans (σ.partSize_le j) hk))
        _ = C ^ (σ.length) := by simp [Finset.prod_const, Fintype.card_fin]
    have hA : |iteratedDeriv σ.length (fun y : ℝ => y ^ p) (Φ 0)|
        ≤ B * max (C ^ p) 1 * (1 + c ^ (p - (k : ℝ))) := by
      rw [iteratedDeriv_rpow_uniform, abs_mul, abs_of_nonneg (Real.rpow_nonneg hΦnn _)]
      have hdesc : |(descPochhammer ℝ σ.length).eval p| ≤ B := by
        rw [hBdef]; exact abs_descPochhammer_eval_le_uniform p hmK
      have hpw : Φ 0 ^ (p - (σ.length : ℝ))
          ≤ max (C ^ p) 1 * (1 + c ^ (p - (k : ℝ))) := by
        by_cases hcase : 0 ≤ p - (σ.length : ℝ)
        · have hstep1 : Φ 0 ^ (p - (σ.length : ℝ)) ≤ C ^ (p - (σ.length : ℝ)) :=
            Real.rpow_le_rpow hΦnn hΦC hcase
          have hstep2 : C ^ (p - (σ.length : ℝ)) ≤ C ^ p :=
            Real.rpow_le_rpow_of_exponent_le hC (by linarith)
          calc Φ 0 ^ (p - (σ.length : ℝ)) ≤ C ^ p := le_trans hstep1 hstep2
            _ ≤ max (C ^ p) 1 := le_max_left _ _
            _ = max (C ^ p) 1 * 1 := (mul_one _).symm
            _ ≤ max (C ^ p) 1 * (1 + c ^ (p - (k : ℝ))) :=
                mul_le_mul_of_nonneg_left h1c hmax0
        · push Not at hcase
          have hstep1 : Φ 0 ^ (p - (σ.length : ℝ)) ≤ c ^ (p - (σ.length : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos hc hcΦ hcase.le
          have hstep2 : c ^ (p - (σ.length : ℝ)) ≤ c ^ (p - (k : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_ge hc hc1 (by linarith)
          calc Φ 0 ^ (p - (σ.length : ℝ)) ≤ c ^ (p - (k : ℝ)) := le_trans hstep1 hstep2
            _ ≤ 1 * (1 + c ^ (p - (k : ℝ))) := by linarith
            _ ≤ max (C ^ p) 1 * (1 + c ^ (p - (k : ℝ))) :=
                mul_le_mul_of_nonneg_right hmax1 (by linarith)
      calc |(descPochhammer ℝ σ.length).eval p| * Φ 0 ^ (p - (σ.length : ℝ))
          ≤ B * (max (C ^ p) 1 * (1 + c ^ (p - (k : ℝ)))) :=
            mul_le_mul hdesc hpw (Real.rpow_nonneg hΦnn _) hBnn
        _ = B * max (C ^ p) 1 * (1 + c ^ (p - (k : ℝ))) := by ring
    calc |iteratedDeriv σ.length (fun y : ℝ => y ^ p) (Φ 0) *
            ∏ j : Fin σ.length, iteratedDeriv (σ.partSize j) Φ 0|
        = |iteratedDeriv σ.length (fun y : ℝ => y ^ p) (Φ 0)| *
            |∏ j : Fin σ.length, iteratedDeriv (σ.partSize j) Φ 0| := abs_mul _ _
      _ ≤ (B * max (C ^ p) 1 * (1 + c ^ (p - (k : ℝ)))) * C ^ σ.length :=
            mul_le_mul hA h2 (abs_nonneg _) hfac0
      _ ≤ (B * max (C ^ p) 1 * (1 + c ^ (p - (k : ℝ)))) * C ^ K₀ :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC hmK) hfac0
      _ = B * max (C ^ p) 1 * C ^ K₀ * (1 + c ^ (p - (k : ℝ))) := by ring
  rw [hcomp]
  calc |∑ σ : OrderedFinpartition k, iteratedDeriv σ.length (fun y : ℝ => y ^ p) (Φ 0) *
          ∏ j : Fin σ.length, iteratedDeriv (σ.partSize j) Φ 0|
      ≤ ∑ σ : OrderedFinpartition k,
          |iteratedDeriv σ.length (fun y : ℝ => y ^ p) (Φ 0) *
            ∏ j : Fin σ.length, iteratedDeriv (σ.partSize j) Φ 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : OrderedFinpartition k,
          (B * max (C ^ p) 1 * C ^ K₀ * (1 + c ^ (p - (k : ℝ)))) :=
        Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = (Fintype.card (OrderedFinpartition k)) *
          (B * max (C ^ p) 1 * C ^ K₀ * (1 + c ^ (p - (k : ℝ)))) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ N * (B * max (C ^ p) 1 * C ^ K₀ * (1 + c ^ (p - (k : ℝ)))) :=
        mul_le_mul_of_nonneg_right (hNge k hk) hfac1
    _ = B * max (C ^ p) 1 * C ^ K₀ * N * (1 + c ^ (p - (k : ℝ))) := by ring


/-! ## Elementary facts about the window and the radicand -/

lemma tau_eq : tau = (1 : ℝ) / 10 := rfl

lemma one_sub_two_tau_eq : 1 - 2 * tau = (4 : ℝ) / 5 := by norm_num [tau]

lemma one_sub_tau_eq : 1 - tau = (9 : ℝ) / 10 := by norm_num [tau]

/-- `h` vanishes strictly above the transition window. -/
lemma h_eq_zero_of_gt {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) {u : ℝ}
    (hu : 1 - tau < u) : h u = 0 := by
  by_contra hne
  have hmem := hsupp hne
  rw [Set.mem_Icc] at hmem
  have h9 : (1 : ℝ) - tau = 9 / 10 := one_sub_tau_eq
  linarith [hmem.2]

lemma psi_eq_sq (h : ℝ → ℝ) (u t : ℝ) :
    psi h semicircle u t = (Real.sqrt (1 - t ^ 2)) ^ 2 - (u * t + h u) ^ 2 := by
  unfold psi line Commons.Geometry.Ulam.semicircle
  ring

lemma psi_eq_quad {h : ℝ → ℝ} {u t : ℝ} (ht : |t| ≤ 1) :
    psi h semicircle u t = 1 - t ^ 2 - (u * t + h u) ^ 2 := by
  rw [psi_eq_sq, Real.sq_sqrt (by nlinarith [abs_le.mp ht])]

lemma profileX_one_pos : 0 < profileX 1 := profileX_pos 1 (by norm_num)

lemma profileX_one_sq : (profileX 1) ^ 2 = (1 : ℝ) / 2 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [Commons.Geometry.Ulam.profileX, show (1 : ℝ) + 1 ^ 2 = 2 by norm_num, div_pow,
    one_pow, Real.sq_sqrt h2.le]

lemma sqrt_two_mul_profileX_one : Real.sqrt 2 * profileX 1 = 1 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [Commons.Geometry.Ulam.profileX, show (1 : ℝ) + 1 ^ 2 = 2 by norm_num, mul_one_div,
    div_self (ne_of_gt h2)]

lemma profileX_one_le_one : profileX 1 ≤ 1 := by
  rw [Commons.Geometry.Ulam.profileX]
  rw [div_le_one (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 1 + 1 ^ 2))]
  rw [show (1 : ℝ) + 1 ^ 2 = 2 by norm_num]
  exact Real.one_le_sqrt.mpr (by norm_num)

lemma abs_sin_le_one (θ : ℝ) : |Real.sin θ| ≤ 1 := by
  rw [abs_le]
  exact ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩

lemma abs_profileX_one_mul_sin_le_one (θ : ℝ) :
    |profileX 1 * Real.sin θ| ≤ 1 := by
  rw [abs_mul, abs_of_pos profileX_one_pos]
  calc profileX 1 * |Real.sin θ| ≤ 1 * 1 :=
        mul_le_mul profileX_one_le_one (abs_sin_le_one θ) (abs_nonneg _) zero_le_one
    _ = 1 := by ring

/-- The key numeric fact: inside `(0,1)` the value `u` plus its (small) window perturbation
stays below `1`, with `√2` normalising `profileX 1 = 1/√2`. -/
lemma add_sqrt_two_abs_h_lt_one {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    u + Real.sqrt 2 * |h u| < 1 := by
  have hs2 : Real.sqrt 2 < 3 / 2 := by
    have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  rcases lt_or_ge (1 - tau) u with hlt | hle
  · rw [h_eq_zero_of_gt hsupp hlt, abs_zero, mul_zero, add_zero]
    exact hu1
  · have hb : Real.sqrt 2 * |h u| ≤ (3 / 2) * (1 / 100) :=
      mul_le_mul hs2.le (hsmall u) (abs_nonneg _) (by norm_num)
    have h9 : (1 : ℝ) - tau = 9 / 10 := one_sub_tau_eq
    nlinarith

/-- Positivity of the radicand on the relevant region (this is the hypothesis under which the
moments are computed with the genuine square root). -/
lemma psi_pos_of_window {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100) {u t : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (ht : |t| ≤ profileX 1) : 0 < psi h semicircle u t := by
  have hX1pos := profileX_one_pos
  have hkey := add_sqrt_two_abs_h_lt_one hsupp hsmall hu0 hu1
  have hsq : Real.sqrt 2 * profileX 1 = 1 := sqrt_two_mul_profileX_one
  have ht1 : |t| ≤ 1 := le_trans ht profileX_one_le_one
  rw [psi_eq_quad ht1]
  have hb : |u * t + h u| < profileX 1 := by
    have h1 : |u * t + h u| ≤ u * |t| + |h u| := by
      calc |u * t + h u| ≤ |u * t| + |h u| := abs_add_le _ _
        _ = u * |t| + |h u| := by rw [abs_mul, abs_of_pos hu0]
    have h2 : u * |t| + |h u| ≤ u * profileX 1 + |h u| := by
      have := mul_le_mul_of_nonneg_left ht hu0.le
      linarith
    have h3 : u * profileX 1 + |h u| < profileX 1 := by
      have : Real.sqrt 2 * (u * profileX 1 + |h u|) < Real.sqrt 2 * profileX 1 := by
        rw [hsq]
        nlinarith [hkey, mul_pos (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)) hX1pos,
          Real.sqrt_nonneg 2]
      nlinarith [this, Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2), hX1pos]
    linarith
  have hsq' : (u * t + h u) ^ 2 < (profileX 1) ^ 2 := by
    have h := abs_lt.mp hb
    nlinarith [h.1, h.2, hX1pos]
  rw [profileX_one_sq] at hsq'
  have ht2 : t ^ 2 ≤ 1 / 2 := by
    have h := abs_le.mp ht
    nlinarith [h.1, h.2, profileX_one_sq, hX1pos]
  nlinarith [hsq', ht2]

/-! ## The radicand on the right end, in the `sin`-substitution -/

lemma psi_eq_quad_of_gt {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) {s t : ℝ}
    (hs : 1 - tau < s) (ht : |t| ≤ 1) :
    psi h semicircle s t = 1 - t ^ 2 * (1 + s ^ 2) := by
  rw [psi_eq_quad ht, h_eq_zero_of_gt hsupp hs]
  ring

/-- With `t = profileX 1 * sin θ` the radicand is `cos²θ + (1-s²) sin²θ / 2`. -/
lemma psi_sin_eq {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) {s : ℝ}
    (hs : 1 - tau < s) (θ : ℝ) :
    psi h semicircle s (profileX 1 * Real.sin θ)
      = Real.cos θ ^ 2 + (1 - s ^ 2) * Real.sin θ ^ 2 / 2 := by
  rw [psi_eq_quad_of_gt hsupp hs (abs_profileX_one_mul_sin_le_one θ), mul_pow,
    profileX_one_sq]
  have h := Real.sin_sq_add_cos_sq θ
  nlinarith [h]

lemma psi_sin_ge_cos_sq {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) {s : ℝ}
    (hs : 1 - tau < s) (hs1 : s ≤ 1) (θ : ℝ) :
    Real.cos θ ^ 2 ≤ psi h semicircle s (profileX 1 * Real.sin θ) := by
  rw [psi_sin_eq hsupp hs]
  have hs0 : 0 ≤ s := by
    have h9 : (1 : ℝ) - tau = 9 / 10 := one_sub_tau_eq
    linarith
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have hsin : (0 : ℝ) ≤ Real.sin θ ^ 2 := sq_nonneg _
  nlinarith [hsin, hs2]

lemma psi_sin_pos {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) {s : ℝ}
    (hs : 1 - tau < s) (hs1 : s < 1) (θ : ℝ) :
    0 < psi h semicircle s (profileX 1 * Real.sin θ) := by
  rw [psi_sin_eq hsupp hs]
  have hs0 : 0 ≤ s := by
    have h9 : (1 : ℝ) - tau = 9 / 10 := one_sub_tau_eq
    linarith
  have hs2 : s ^ 2 < 1 := by nlinarith
  have hcos := sq_nonneg (Real.cos θ)
  have hsin : (0 : ℝ) ≤ Real.sin θ ^ 2 := sq_nonneg _
  have hsincos := Real.sin_sq_add_cos_sq θ
  nlinarith [hcos, hsincos]


lemma profileX_one_lt_one : profileX 1 < 1 := by
  rcases lt_or_eq_of_le profileX_one_le_one with h | h
  · exact h
  · exfalso
    have hsq := profileX_one_sq
    rw [h] at hsq
    norm_num at hsq

lemma psi_le_one {h : ℝ → ℝ} {u t : ℝ} (ht : |t| ≤ 1) (hpos : 0 ≤ psi h semicircle u t) :
    psi h semicircle u t ≤ 1 := by
  rw [psi_eq_quad ht]
  nlinarith [sq_nonneg t, sq_nonneg (u * t + h u)]

lemma deriv_eq_zero_of_gt {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) {u : ℝ}
    (hu : 1 - tau < u) : deriv h u = 0 := by
  have h0 : h =ᶠ[𝓝 u] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
    exact h_eq_zero_of_gt hsupp hv
  have h1 : iteratedDeriv 1 h u = 0 :=
    Commons.Analysis.Calculus.iteratedDeriv_zero_of_zero_nhds (k := 1) h0
  have h2 : iteratedDeriv 1 h = deriv h := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_zero]
  rwa [h2] at h1

lemma iteratedDeriv_const_pos {c : ℝ} {m : ℕ} (hm : 1 ≤ m) (x : ℝ) :
    iteratedDeriv m (fun _ : ℝ => c) x = 0 := by
  rw [iteratedDeriv_const]
  simp [show m ≠ 0 by omega]

/-- Uniform bounds for all `u`-derivatives of order `≤ n+1` of the slices of `ψ`, on the box
`[-profileX 1, profileX 1] × [9/10, 1]`. -/
lemma psi_slice_deriv_bound (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ⊤ h) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ j ≤ n + 1, ∀ s ∈ Set.Icc (9 / 10 : ℝ) 1, ∀ t : ℝ,
      |t| ≤ profileX 1 →
      |iteratedDeriv j (fun u : ℝ => psi h semicircle u t) s| ≤ M := by
  set U : Set (ℝ × ℝ) := {q : ℝ × ℝ | |q.1| < 1} with hUdef
  have hUopen : IsOpen U := isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
  have hF : ContDiffOn ℝ ⊤ (fun q : ℝ × ℝ => psi h semicircle q.2 q.1) U := by
    have hpoly : ContDiff ℝ ⊤ (fun q : ℝ × ℝ => 1 - q.1 ^ 2 - (q.2 * q.1 + h q.2) ^ 2) := by
      fun_prop
    refine hpoly.contDiffOn.congr (fun q hq => ?_)
    have hq1 : |q.1| ≤ 1 := le_of_lt hq
    exact psi_eq_quad hq1
  set K : Set (ℝ × ℝ) := Set.Icc (-(profileX 1)) (profileX 1) ×ˢ Set.Icc (9 / 10 : ℝ) 1
    with hKdef
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKU : K ⊆ U := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [hUdef, Set.mem_setOf_eq]
    have hx1 : |x| ≤ profileX 1 := abs_le.mpr ⟨hx.1, hx.2⟩
    exact lt_of_le_of_lt hx1 profileX_one_lt_one
  choose Cj hCj using fun j =>
    Work.Analysis.Calculus.parametric_iteratedDeriv_bound
      (F := fun a b : ℝ => psi h semicircle b a) hUopen hF hKc hKU j
  refine ⟨max 1 (∑ j ∈ Finset.range (n + 2), max (Cj j) 1), le_max_left _ _, ?_⟩
  intro j hj s hs t ht
  have hmem : (t, s) ∈ K := by
    refine ⟨?_, hs⟩
    rw [abs_le] at ht
    exact ht
  have hb := hCj j (t, s) hmem
  have h1 : Cj j ≤ max (Cj j) 1 := le_max_left _ _
  have h2 : max (Cj j) 1 ≤ ∑ i ∈ Finset.range (n + 2), max (Cj i) 1 := by
    refine Finset.single_le_sum (f := fun i => max (Cj i) 1)
      (fun i _ => le_trans zero_le_one (le_max_right (Cj i) 1)) ?_
    simp only [Finset.mem_range]
    omega
  have h3 : (∑ i ∈ Finset.range (n + 2), max (Cj i) 1)
      ≤ max 1 (∑ i ∈ Finset.range (n + 2), max (Cj i) 1) := le_max_right _ _
  have hb' : |iteratedDeriv j (fun u : ℝ => psi h semicircle u t) s| ≤ Cj j := by
    simpa using hb
  linarith

/-- The `u`-derivatives of the slice `u ↦ lineSlope h u t` are bounded by `1` in the right
end region (where `h` vanishes identically). -/
lemma lineSlope_slice_bound {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) {s : ℝ}
    (hs : 1 - tau < s) {t : ℝ} (ht : |t| ≤ profileX 1) (m : ℕ) :
    |iteratedDeriv m (fun u : ℝ => lineSlope h u t) s| ≤ 1 := by
  have hconst : (fun u : ℝ => lineSlope h u t) =ᶠ[𝓝 s] (fun _ : ℝ => t) := by
    filter_upwards [isOpen_Ioi.mem_nhds hs] with u hu
    simp only [lineSlope]
    rw [deriv_eq_zero_of_gt hsupp hu, add_zero]
  rw [Filter.EventuallyEq.iteratedDeriv_eq _ hconst]
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    rw [iteratedDeriv_zero]
    have ht1 : |t| ≤ 1 := le_trans ht profileX_one_le_one
    exact ht1
  · rw [iteratedDeriv_const_pos h s]
    norm_num


/-! ## The main slice estimates -/

/-- The slice `u ↦ psi h semicircle u t` is smooth in `u`. -/
lemma contDiff_slice (h : ℝ → ℝ) (hh : ContDiff ℝ ⊤ h) (t : ℝ) :
    ContDiff ℝ ⊤ (fun u : ℝ => psi h semicircle u t) := by
  have hfe : (fun u : ℝ => psi h semicircle u t)
      = fun u : ℝ => (Real.sqrt (1 - t ^ 2)) ^ 2 - (u * t + h u) ^ 2 := by
    funext u; rw [psi_eq_sq]
  rw [hfe]
  fun_prop

/-- The Faà di Bruno bound for the first inhomogeneity: the `(n+1)`-st `u`-derivative of the
`E₁` integrand is dominated by `1 + ψ(s,t)^{-1/2}`. -/
lemma E1_slice_bound (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ⊤ h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, 9 / 10 < s → s < 1 → ∀ t : ℝ, |t| ≤ profileX 1 →
      |iteratedDeriv (n + 1)
        (fun u : ℝ => Work.OddVolterra.Existence.PhiF n h (u, t)) s|
        ≤ K * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ)) := by
  obtain ⟨M, hM1, hM⟩ := psi_slice_deriv_bound n hh
  obtain ⟨K, hK0, hK⟩ := iteratedDeriv_rpow_comp_bound_uniform ((n : ℝ) + 1 / 2) (n + 1)
    (C := M) hM1
  refine ⟨K, hK0, ?_⟩
  intro s hs0 hs1 t ht
  have h0s : (0 : ℝ) < s := by linarith
  have hpos : 0 < psi h semicircle s t := psi_pos_of_window hsupp hsmall h0s hs1 ht
  have hslice := contDiff_slice h hh t
  have hev : (fun u : ℝ => Work.OddVolterra.Existence.PhiF n h (u, t)) =ᶠ[𝓝 s]
      (fun u : ℝ => psi h semicircle u t ^ ((n : ℝ) + 1 / 2)) := by
    filter_upwards [Ioo_mem_nhds h0s hs1] with u hu
    have hupos : 0 < psi h semicircle u t := psi_pos_of_window hsupp hsmall hu.1 hu.2 ht
    show psi h semicircle u t ^ n * Real.sqrt (psi h semicircle u t)
      = psi h semicircle u t ^ ((n : ℝ) + 1 / 2)
    rw [← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_add hupos]
  rw [Filter.EventuallyEq.iteratedDeriv_eq _ hev]
  have hshift : iteratedDeriv (n + 1)
        (fun u : ℝ => psi h semicircle u t ^ ((n : ℝ) + 1 / 2)) s
      = iteratedDeriv (n + 1)
        (fun z : ℝ => psi h semicircle (z + s) t ^ ((n : ℝ) + 1 / 2)) 0 := by
    have hcomp := congr_fun (iteratedDeriv_comp_add_const (𝕜 := ℝ) (F := ℝ) (n + 1)
      (fun y : ℝ => psi h semicircle y t ^ ((n : ℝ) + 1 / 2)) s) 0
    simpa using hcomp.symm
  rw [hshift]
  have hsI : s ∈ Set.Icc (9 / 10 : ℝ) 1 := ⟨le_of_lt hs0, le_of_lt hs1⟩
  have hderiv : ∀ j ≤ n + 1,
      |iteratedDeriv j (fun z : ℝ => psi h semicircle (z + s) t) 0| ≤ M := by
    intro j hj
    have hsj : iteratedDeriv j (fun z : ℝ => psi h semicircle (z + s) t) 0
        = iteratedDeriv j (fun u : ℝ => psi h semicircle u t) s := by
      have hcomp := congr_fun (iteratedDeriv_comp_add_const (𝕜 := ℝ) (F := ℝ) j
        (fun y : ℝ => psi h semicircle y t) s) 0
      simpa using hcomp
    rw [hsj]
    exact hM j hj s hsI t ht
  have hsm : ContDiffAt ℝ (n + 1) (fun z : ℝ => psi h semicircle (z + s) t) 0 := by
    have h2 : ContDiff ℝ ⊤ (fun z : ℝ => z + s) := by fun_prop
    exact (hslice.comp h2).contDiffAt.of_le le_top
  have hΦC : psi h semicircle (0 + s) t ≤ M := by
    simpa using le_trans (psi_le_one (le_trans ht profileX_one_le_one) hpos.le) hM1
  have hbd := hK (n + 1) (psi h semicircle s t) (fun z : ℝ => psi h semicircle (z + s) t)
    (le_refl _) hpos (psi_le_one (le_trans ht profileX_one_le_one) hpos.le) hsm
    (by simpa using hpos.le) hΦC hderiv
  have hexp : (n : ℝ) + 1 / 2 - ((n + 1 : ℕ) : ℝ) = -(1 / 2) := by push_cast; ring
  rw [hexp] at hbd
  exact hbd


lemma sqrt_le_one_of_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : Real.sqrt x ≤ 1 := by
  rw [← Real.sqrt_one]
  exact Real.sqrt_le_sqrt hx1

lemma contDiff_lineSlope_slice {h : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) (t : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => lineSlope h u t) := by
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv h) := by
    simpa using ContDiff.iterate_deriv (𝕜 := ℝ) 1 hh
  have hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => t + deriv h u) :=
    contDiff_const.add h2
  simpa [lineSlope] using hd

/-- The Faà di Bruno bound for the second inhomogeneity: the `n`-th `u`-derivative of the `E₂`
integrand is dominated by `1 + ψ(s,t)^{-1/2}`. -/
lemma E2_slice_bound (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ⊤ h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, 9 / 10 < s → s < 1 → ∀ t : ℝ, |t| ≤ profileX 1 →
      |iteratedDeriv n
        (fun u : ℝ => Work.OddVolterra.Existence.PhiH n h (u, t)) s|
        ≤ K * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, zero_le_one, ?_⟩
    intro s hs0 hs1 t ht
    have h0s : (0 : ℝ) < s := by linarith
    have hpos : 0 < psi h semicircle s t := psi_pos_of_window hsupp hsmall h0s hs1 ht
    have h1 : (1 : ℝ) ≤ 1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ) := by
      have := Real.rpow_nonneg hpos.le (-(1 / 2) : ℝ); linarith
    have hls : |lineSlope h s t| ≤ 1 := by
      have := lineSlope_slice_bound hsupp (s := s) (t := t)
        (by rw [one_sub_tau_eq]; exact hs0) ht 0
      rwa [iteratedDeriv_zero] at this
    have hsq : Real.sqrt (psi h semicircle s t) ≤ 1 :=
      sqrt_le_one_of_le_one hpos.le (psi_le_one (le_trans ht profileX_one_le_one) hpos.le)
    have hnn : 0 ≤ Real.sqrt (psi h semicircle s t) := Real.sqrt_nonneg _
    have hb : |iteratedDeriv 0
        (fun u : ℝ => Work.OddVolterra.Existence.PhiH 0 h (u, t)) s| ≤ 1 := by
      rw [iteratedDeriv_zero]
      calc |Work.OddVolterra.Existence.PhiH 0 h (s, t)|
          = |Real.sqrt (psi h semicircle s t) * lineSlope h s t| := by
            simp [Work.OddVolterra.Existence.PhiH]
        _ = Real.sqrt (psi h semicircle s t) * |lineSlope h s t| := by
            rw [abs_mul, abs_of_nonneg hnn]
        _ ≤ 1 * 1 := mul_le_mul hsq hls (abs_nonneg _) zero_le_one
        _ = 1 := by ring
    calc |iteratedDeriv 0 (fun u : ℝ => Work.OddVolterra.Existence.PhiH 0 h (u, t)) s| ≤ 1 := hb
      _ ≤ 1 * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ)) := by rw [one_mul]; exact h1
  · obtain ⟨M, hM1, hM⟩ := psi_slice_deriv_bound (n - 1) hh
    obtain ⟨K1, hK10, hK1⟩ := iteratedDeriv_rpow_comp_bound_uniform
      (((n - 1 : ℕ) : ℝ) + 1 / 2) n (C := M) hM1
    refine ⟨max 1 (K1 * 2 ^ n), le_trans zero_le_one (le_max_left _ _), ?_⟩
    intro s hs0 hs1 t ht
    have h0s : (0 : ℝ) < s := by linarith
    have hpos : 0 < psi h semicircle s t := psi_pos_of_window hsupp hsmall h0s hs1 ht
    have hc1 : psi h semicircle s t ≤ 1 :=
      psi_le_one (le_trans ht profileX_one_le_one) hpos.le
    have hc0 : 0 ≤ psi h semicircle s t := hpos.le
    have hslice := contDiff_slice h hh t
    have hsI : s ∈ Set.Icc (9 / 10 : ℝ) 1 := ⟨le_of_lt hs0, le_of_lt hs1⟩
    have hev : (fun u : ℝ => Work.OddVolterra.Existence.PhiH n h (u, t)) =ᶠ[𝓝 s]
        (fun u : ℝ => (psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2))
          * lineSlope h u t) := by
      filter_upwards [Ioo_mem_nhds h0s hs1] with u hu
      have hupos : 0 < psi h semicircle u t := psi_pos_of_window hsupp hsmall hu.1 hu.2 ht
      show psi h semicircle u t ^ (n - 1) * Real.sqrt (psi h semicircle u t) * lineSlope h u t
        = (psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2)) * lineSlope h u t
      congr 1
      rw [← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_add hupos]
    rw [Filter.EventuallyEq.iteratedDeriv_eq _ hev]
    -- Leibniz
    have hf : ContDiffAt ℝ n (fun u : ℝ => psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2)) s := by
      have h2 : ContDiffAt ℝ n (fun y : ℝ => y ^ (((n - 1 : ℕ) : ℝ) + 1 / 2))
          (psi h semicircle s t) :=
        Real.contDiffAt_rpow_const (n := n) (Or.inl (ne_of_gt hpos))
      exact h2.comp s (hslice.contDiffAt.of_le le_top)
    have hle : ((n : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
      WithTop.coe_le_coe.mpr (le_top : (n : ℕ∞) ≤ ⊤)
    have hg : ContDiffAt ℝ n (fun u : ℝ => lineSlope h u t) s :=
      (contDiff_lineSlope_slice (hh.of_le le_top) t).contDiffAt.of_le hle
    have hleib := iteratedDerivWithin_mul (𝕜 := ℝ) (n := n) (x := s) (s := Set.univ)
      (f := fun u : ℝ => psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2))
      (g := fun u : ℝ => lineSlope h u t) (Set.mem_univ s) uniqueDiffOn_univ
      hf.contDiffWithinAt hg.contDiffWithinAt
    have hmul : iteratedDeriv n
        (fun u : ℝ => (psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2)) * lineSlope h u t) s
        = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
          * iteratedDeriv i (fun u : ℝ => psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2)) s
          * iteratedDeriv (n - i) (fun u : ℝ => lineSlope h u t) s := by
      rw [show (fun u : ℝ => (psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2))
            * lineSlope h u t)
          = ((fun u : ℝ => psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2))
            * fun u : ℝ => lineSlope h u t) from rfl]
      simpa [iteratedDerivWithin_univ] using hleib
    rw [hmul]
    -- the term-wise bound
    have hexp : ∀ i ≤ n, -(1 / 2 : ℝ) ≤ (((n - 1 : ℕ) : ℝ) + 1 / 2) - (i : ℝ) := by
      intro i hi
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]
        norm_num
      have hile : (i : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hi
      linarith
    have hderiv : ∀ j ≤ n,
        |iteratedDeriv j (fun z : ℝ => psi h semicircle (z + s) t) 0| ≤ M := by
      intro j hj
      have hsj : iteratedDeriv j (fun z : ℝ => psi h semicircle (z + s) t) 0
          = iteratedDeriv j (fun u : ℝ => psi h semicircle u t) s := by
        have hcomp := congr_fun (iteratedDeriv_comp_add_const (𝕜 := ℝ) (F := ℝ) j
          (fun y : ℝ => psi h semicircle y t) s) 0
        simpa using hcomp
      rw [hsj]
      exact hM j (by omega) s hsI t ht
    have hsm : ContDiffAt ℝ n (fun z : ℝ => psi h semicircle (z + s) t) 0 := by
      have h2 : ContDiff ℝ ⊤ (fun z : ℝ => z + s) := by fun_prop
      exact (hslice.comp h2).contDiffAt.of_le le_top
    have hΦC : psi h semicircle (0 + s) t ≤ M := by
      simpa using le_trans hc1 hM1
    have hfi : ∀ i ≤ n,
        |iteratedDeriv i (fun u : ℝ => psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2)) s|
        ≤ K1 * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ)) := by
      intro i hi
      have hshift : iteratedDeriv i
            (fun u : ℝ => psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2)) s
          = iteratedDeriv i
            (fun z : ℝ => psi h semicircle (z + s) t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2)) 0 := by
        have hcomp := congr_fun (iteratedDeriv_comp_add_const (𝕜 := ℝ) (F := ℝ) i
          (fun y : ℝ => psi h semicircle y t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2)) s) 0
        simpa using hcomp.symm
      rw [hshift]
      have hb := hK1 i (psi h semicircle s t) (fun z : ℝ => psi h semicircle (z + s) t)
        (by omega) hpos hc1 hsm (by simpa using hc0) hΦC hderiv
      have hmono : (psi h semicircle s t) ^ ((((n - 1 : ℕ) : ℝ) + 1 / 2) - (i : ℝ))
          ≤ (psi h semicircle s t) ^ (-(1 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hpos hc1 (hexp i hi)
      refine le_trans hb ?_
      apply mul_le_mul_of_nonneg_left ?_ hK10
      linarith
    have hgl : ∀ m, |iteratedDeriv m (fun u : ℝ => lineSlope h u t) s| ≤ 1 :=
      fun m => lineSlope_slice_bound hsupp (s := s) (t := t)
        (by rw [one_sub_tau_eq]; exact hs0) ht m
    calc |∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
            * iteratedDeriv i (fun u : ℝ => psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2)) s
            * iteratedDeriv (n - i) (fun u : ℝ => lineSlope h u t) s|
        ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
            * (K1 * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ))) * 1 := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
          intro i hi
          rw [Finset.mem_range] at hi
          have hi' : i ≤ n := by omega
          calc |(n.choose i : ℝ)
                * iteratedDeriv i (fun u : ℝ => psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2)) s
                * iteratedDeriv (n - i) (fun u : ℝ => lineSlope h u t) s|
              = (n.choose i : ℝ)
                * |iteratedDeriv i (fun u : ℝ => psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2)) s|
                * |iteratedDeriv (n - i) (fun u : ℝ => lineSlope h u t) s| := by
                rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (n.choose i))]
            _ ≤ (n.choose i : ℝ) * (K1 * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ))) * 1 := by
                exact mul_le_mul (mul_le_mul_of_nonneg_left (hfi i hi') (Nat.cast_nonneg _))
                  (hgl (n - i)) (abs_nonneg _)
                  (mul_nonneg (Nat.cast_nonneg _)
                    (mul_nonneg hK10 (by have := Real.rpow_nonneg hc0 (-(1 / 2) : ℝ); linarith)))
      _ = (K1 * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ))) * 2 ^ n := by
          have h1 : ∀ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * (K1 * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ))) * 1
              = (n.choose i : ℝ) * (K1 * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ))) := by
            intro i _; ring
          rw [Finset.sum_congr rfl h1]
          have h2 : ∑ x ∈ Finset.range (n + 1), (n.choose x : ℝ)
              * (K1 * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ)))
              = (∑ x ∈ Finset.range (n + 1), (n.choose x : ℝ))
                * (K1 * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ))) := (Finset.sum_mul ..).symm
          rw [h2, ← Nat.cast_sum, Nat.sum_range_choose]
          push_cast
          ring
      _ ≤ max 1 (K1 * 2 ^ n) * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ)) := by
          have hK1' : K1 * 2 ^ n ≤ max 1 (K1 * 2 ^ n) := le_max_right _ _
          have h1 : (0 : ℝ) ≤ 1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ) := by
            have := Real.rpow_nonneg hc0 (-(1 / 2) : ℝ); linarith
          calc (K1 * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ))) * 2 ^ n
              = (K1 * 2 ^ n) * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ)) := by ring
            _ ≤ max 1 (K1 * 2 ^ n) * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ)) :=
                mul_le_mul_of_nonneg_right hK1' h1


/-! ## The inhomogeneities as integrals of the partial-derivative iterates -/

/-- The partial-derivative iterate of the `E₁` integrand. -/
def G1 (n : ℕ) (h : ℝ → ℝ) : ℝ × ℝ → ℝ :=
  pderiv1Iter (Work.OddVolterra.Existence.psiPos h) (n + 1) (Work.OddVolterra.Existence.PhiF n h)

/-- The partial-derivative iterate of the `E₂` integrand. -/
def G2 (n : ℕ) (h : ℝ → ℝ) : ℝ × ℝ → ℝ :=
  pderiv1Iter (Work.OddVolterra.Existence.psiPos h) n (Work.OddVolterra.Existence.PhiH n h)

lemma contDiffOn_G1 (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G1 n h) (Work.OddVolterra.Existence.psiPos h) :=
  contDiffOn_pderiv1Iter (Work.OddVolterra.Existence.isOpen_psiPos hh)
    (Work.OddVolterra.Existence.contDiffOn_PhiF hh n) (n + 1)

lemma contDiffOn_G2 (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G2 n h) (Work.OddVolterra.Existence.psiPos h) :=
  contDiffOn_pderiv1Iter (Work.OddVolterra.Existence.isOpen_psiPos hh)
    (Work.OddVolterra.Existence.contDiffOn_PhiH hh n) n

/-! ## The `sin`-substitution -/

lemma cos_nonneg_of_mem_uIcc {θ : ℝ}
    (hθ : θ ∈ Set.uIcc (-(Real.pi / 2)) (Real.pi / 2)) : 0 ≤ Real.cos θ := by
  rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
  exact Real.cos_nonneg_of_mem_Icc hθ

lemma profileX_mul_sin_mem {θ : ℝ} (hθ : θ ∈ Set.uIcc (-(Real.pi / 2)) (Real.pi / 2)) :
    |profileX 1 * Real.sin θ| ≤ profileX 1 := by
  rw [abs_mul, abs_of_pos profileX_one_pos]
  exact mul_le_of_le_one_right profileX_one_pos.le (abs_sin_le_one θ)

/-- The change of variables `t = profileX 1 * sin θ`, in the form needed below. -/
lemma integral_comp_sin {g : ℝ → ℝ} :
    (∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        g (profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ))
      = ∫ t in (-(profileX 1))..(profileX 1), g t := by
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun θ : ℝ => profileX 1 * Real.sin θ)
    (f' := fun θ : ℝ => profileX 1 * Real.cos θ)
    (g := g) (a := -(Real.pi / 2)) (b := Real.pi / 2)
    (by fun_prop)
    (fun x hx => by
      have hder : HasDerivAt (fun θ : ℝ => Real.sin θ) (Real.cos x) x := Real.hasDerivAt_sin x
      simpa using hder.const_mul (profileX 1))
    (fun x hx => by
      have hx' : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        rwa [min_eq_left (by linarith [Real.pi_pos]),
          max_eq_right (by linarith [Real.pi_pos])] at hx
      exact mul_nonneg profileX_one_pos.le (Real.cos_pos_of_mem_Ioo hx').le)
  rw [show profileX 1 * Real.sin (-(Real.pi / 2)) = -(profileX 1) from by
        rw [Real.sin_neg, Real.sin_pi_div_two]; ring,
      show profileX 1 * Real.sin (Real.pi / 2) = profileX 1 from by
        rw [Real.sin_pi_div_two]; ring] at h
  exact h

/-- `ψ^{-1/2} · u ≤ 1` when `u ≥ 0` and `u² ≤ ψ`. -/
lemma rpow_neg_half_mul_le_one {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u) (hcu : u ^ 2 ≤ c) :
    c ^ (-(1 / 2) : ℝ) * u ≤ 1 := by
  have hsqrt : c ^ (-(1 / 2) : ℝ) = (Real.sqrt c)⁻¹ := by
    rw [show (-(1 / 2) : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg (le_of_lt hc),
      ← Real.sqrt_eq_rpow]
  rw [hsqrt]
  have hsp : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hle : u ≤ Real.sqrt c := (Real.le_sqrt hu hc.le).mpr hcu
  calc (Real.sqrt c)⁻¹ * u ≤ (Real.sqrt c)⁻¹ * Real.sqrt c :=
        mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hsp.le)
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hsp)

/-- The θ-bound for the first inhomogeneity. -/
lemma E1_theta_bound (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ⊤ h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 9 / 10 < s → s < 1 →
      ∀ θ ∈ Set.uIcc (-(Real.pi / 2)) (Real.pi / 2),
        |G1 n h (s, profileX 1 * Real.sin θ)| * (profileX 1 * Real.cos θ) ≤ C := by
  obtain ⟨K, hK0, hK⟩ := E1_slice_bound n hh hsupp hsmall
  refine ⟨max (2 * K * profileX 1) 0, le_max_right _ _, ?_⟩
  intro s hs0 hs1 θ hθ
  have hcos := cos_nonneg_of_mem_uIcc hθ
  have hX1 := profileX_one_pos
  have ht : |profileX 1 * Real.sin θ| ≤ profileX 1 := profileX_mul_sin_mem hθ
  have hpsi : 0 < psi h semicircle s (profileX 1 * Real.sin θ) :=
    psi_pos_of_window hsupp hsmall (by linarith) hs1 ht
  have hmem : (s, profileX 1 * Real.sin θ) ∈ Work.OddVolterra.Existence.psiPos h :=
    show 0 < psi h semicircle s (profileX 1 * Real.sin θ) from hpsi
  have hident : G1 n h (s, profileX 1 * Real.sin θ)
      = iteratedDeriv (n + 1)
        (fun u : ℝ => Work.OddVolterra.Existence.PhiF n h (u, profileX 1 * Real.sin θ)) s := by
    rw [G1, iteratedDeriv_eq_pderiv1Iter
      (Work.OddVolterra.Existence.isOpen_psiPos (hh.of_le le_top))
      (Work.OddVolterra.Existence.contDiffOn_PhiF (hh.of_le le_top) n) hmem (n + 1)]
  rw [hident]
  have hb := hK s hs0 hs1 (profileX 1 * Real.sin θ) ht
  have hge := psi_sin_ge_cos_sq hsupp (s := s) (by rw [one_sub_tau_eq]; exact hs0) hs1.le θ
  have hle : (psi h semicircle s (profileX 1 * Real.sin θ)) ^ (-(1 / 2) : ℝ) * Real.cos θ ≤ 1 :=
    rpow_neg_half_mul_le_one hpsi hcos hge
  have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hX1le : (0 : ℝ) ≤ profileX 1 := hX1.le
  refine le_trans ?_ (le_max_left _ _)
  calc |iteratedDeriv (n + 1)
          (fun u : ℝ => Work.OddVolterra.Existence.PhiF n h (u, profileX 1 * Real.sin θ)) s|
        * (profileX 1 * Real.cos θ)
      ≤ (K * (1 + (psi h semicircle s (profileX 1 * Real.sin θ)) ^ (-(1 / 2) : ℝ)))
        * (profileX 1 * Real.cos θ) := by
        apply mul_le_mul_of_nonneg_right hb
        positivity
    _ = K * profileX 1 * Real.cos θ
          + (K * profileX 1) * ((psi h semicircle s (profileX 1 * Real.sin θ)) ^ (-(1 / 2) : ℝ)
            * Real.cos θ) := by ring
    _ ≤ K * profileX 1 * 1 + (K * profileX 1) * 1 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hcos1 (mul_nonneg hK0 hX1le)
        · exact mul_le_mul_of_nonneg_left hle (mul_nonneg hK0 hX1le)
    _ = 2 * K * profileX 1 := by ring

/-- The θ-bound for the second inhomogeneity. -/
lemma E2_theta_bound (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ⊤ h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 9 / 10 < s → s < 1 →
      ∀ θ ∈ Set.uIcc (-(Real.pi / 2)) (Real.pi / 2),
        |G2 n h (s, profileX 1 * Real.sin θ)| * (profileX 1 * Real.cos θ) ≤ C := by
  obtain ⟨K, hK0, hK⟩ := E2_slice_bound n hh hsupp hsmall
  refine ⟨max (2 * K * profileX 1) 0, le_max_right _ _, ?_⟩
  intro s hs0 hs1 θ hθ
  have hcos := cos_nonneg_of_mem_uIcc hθ
  have hX1 := profileX_one_pos
  have ht : |profileX 1 * Real.sin θ| ≤ profileX 1 := profileX_mul_sin_mem hθ
  have hpsi : 0 < psi h semicircle s (profileX 1 * Real.sin θ) :=
    psi_pos_of_window hsupp hsmall (by linarith) hs1 ht
  have hmem : (s, profileX 1 * Real.sin θ) ∈ Work.OddVolterra.Existence.psiPos h :=
    show 0 < psi h semicircle s (profileX 1 * Real.sin θ) from hpsi
  have hident : G2 n h (s, profileX 1 * Real.sin θ)
      = iteratedDeriv n
        (fun u : ℝ => Work.OddVolterra.Existence.PhiH n h (u, profileX 1 * Real.sin θ)) s := by
    rw [G2, iteratedDeriv_eq_pderiv1Iter
      (Work.OddVolterra.Existence.isOpen_psiPos (hh.of_le le_top))
      (Work.OddVolterra.Existence.contDiffOn_PhiH (hh.of_le le_top) n) hmem n]
  rw [hident]
  have hb := hK s hs0 hs1 (profileX 1 * Real.sin θ) ht
  have hge := psi_sin_ge_cos_sq hsupp (s := s) (by rw [one_sub_tau_eq]; exact hs0) hs1.le θ
  have hle : (psi h semicircle s (profileX 1 * Real.sin θ)) ^ (-(1 / 2) : ℝ) * Real.cos θ ≤ 1 :=
    rpow_neg_half_mul_le_one hpsi hcos hge
  have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hX1le : (0 : ℝ) ≤ profileX 1 := hX1.le
  refine le_trans ?_ (le_max_left _ _)
  calc |iteratedDeriv n
          (fun u : ℝ => Work.OddVolterra.Existence.PhiH n h (u, profileX 1 * Real.sin θ)) s|
        * (profileX 1 * Real.cos θ)
      ≤ (K * (1 + (psi h semicircle s (profileX 1 * Real.sin θ)) ^ (-(1 / 2) : ℝ)))
        * (profileX 1 * Real.cos θ) := by
        apply mul_le_mul_of_nonneg_right hb
        positivity
    _ = K * profileX 1 * Real.cos θ
          + (K * profileX 1) * ((psi h semicircle s (profileX 1 * Real.sin θ)) ^ (-(1 / 2) : ℝ)
            * Real.cos θ) := by ring
    _ ≤ K * profileX 1 * 1 + (K * profileX 1) * 1 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hcos1 (mul_nonneg hK0 hX1le)
        · exact mul_le_mul_of_nonneg_left hle (mul_nonneg hK0 hX1le)
    _ = 2 * K * profileX 1 := by ring


/-! ## The inhomogeneities as `θ`-integrals -/

lemma E1_eq_theta_integral (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ⊤ h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100) {s : ℝ} (hs0 : 9 / 10 < s) (hs1 : s < 1) :
    E1 n h s = ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        G1 n h (s, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ) := by
  have hstep1 : E1 n h s = ∫ t in (-(profileX 1))..(profileX 1), G1 n h (s, t) := by
    unfold Work.OddVolterra.E1
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    have ht1 : |t| ≤ profileX 1 := by
      rw [Set.uIcc_of_le (by linarith [profileX_one_pos])] at ht
      exact abs_le.mpr ht
    have hpsi : 0 < psi h semicircle s t := psi_pos_of_window hsupp hsmall (by linarith) hs1 ht1
    have hmem : (s, t) ∈ Work.OddVolterra.Existence.psiPos h := hpsi
    show iteratedDeriv (n + 1) (fun u : ℝ => Work.OddVolterra.Existence.PhiF n h (u, t)) s
      = G1 n h (s, t)
    rw [iteratedDeriv_eq_pderiv1Iter (Work.OddVolterra.Existence.isOpen_psiPos (hh.of_le le_top))
      (Work.OddVolterra.Existence.contDiffOn_PhiF (hh.of_le le_top) n) hmem (n + 1)]
    rfl
  rw [hstep1]
  exact (integral_comp_sin (g := fun t => G1 n h (s, t))).symm

lemma E1_one_eq_theta_integral (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ⊤ h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100) :
    E1 n h 1 = ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        G1 n h (1, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ) := by
  have hstep1 : E1 n h 1 = ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
      (fun t : ℝ => iteratedDeriv (n + 1)
        (fun u : ℝ => Work.OddVolterra.Existence.PhiF n h (u, t)) 1)
        (profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ) := by
    rw [show E1 n h 1 = ∫ t in (-(profileX 1))..(profileX 1),
        (fun t : ℝ => iteratedDeriv (n + 1)
          (fun u : ℝ => Work.OddVolterra.Existence.PhiF n h (u, t)) 1) t from rfl]
    exact (integral_comp_sin (g := fun t : ℝ => iteratedDeriv (n + 1)
      (fun u : ℝ => Work.OddVolterra.Existence.PhiF n h (u, t)) 1)).symm
  rw [hstep1]
  refine intervalIntegral.integral_congr (fun θ hθ => ?_)
  by_cases htop : |θ| = Real.pi / 2
  · have hcos0 : Real.cos θ = 0 := by
      rcases (abs_eq (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 2)).mp htop with h | h
      · rw [h, Real.cos_pi_div_two]
      · rw [h, Real.cos_neg, Real.cos_pi_div_two]
    simp [hcos0]
  · have hθ' : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
      exact ⟨hθ.1, hθ.2⟩
    have habs : |θ| < Real.pi / 2 := lt_of_le_of_ne (abs_le.mpr ⟨hθ'.1, hθ'.2⟩) htop
    have hmem : (1, profileX 1 * Real.sin θ) ∈ Work.OddVolterra.Existence.psiPos h := by
      show 0 < psi h semicircle 1 (profileX 1 * Real.sin θ)
      rw [psi_sin_eq hsupp (s := 1) (by rw [one_sub_tau_eq]; norm_num)]
      have hc : 0 < Real.cos θ := by
        rw [abs_lt] at habs
        exact Real.cos_pos_of_mem_Ioo ⟨habs.1, habs.2⟩
      nlinarith [hc, sq_nonneg (Real.sin θ)]
    show iteratedDeriv (n + 1) (fun u : ℝ => Work.OddVolterra.Existence.PhiF n h (u, profileX 1 * Real.sin θ)) 1
      * (profileX 1 * Real.cos θ) = G1 n h (1, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ)
    rw [iteratedDeriv_eq_pderiv1Iter (Work.OddVolterra.Existence.isOpen_psiPos (hh.of_le le_top))
      (Work.OddVolterra.Existence.contDiffOn_PhiF (hh.of_le le_top) n) hmem (n + 1)]
    rfl

lemma E2_eq_theta_integral (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ⊤ h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100) {s : ℝ} (hs0 : 9 / 10 < s) (hs1 : s < 1) :
    E2 n h s = ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        G2 n h (s, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ) := by
  have hstep1 : E2 n h s = ∫ t in (-(profileX 1))..(profileX 1), G2 n h (s, t) := by
    unfold Work.OddVolterra.E2
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    have ht1 : |t| ≤ profileX 1 := by
      rw [Set.uIcc_of_le (by linarith [profileX_one_pos])] at ht
      exact abs_le.mpr ht
    have hpsi : 0 < psi h semicircle s t := psi_pos_of_window hsupp hsmall (by linarith) hs1 ht1
    have hmem : (s, t) ∈ Work.OddVolterra.Existence.psiPos h := hpsi
    show iteratedDeriv n (fun u : ℝ => Work.OddVolterra.Existence.PhiH n h (u, t)) s
      = G2 n h (s, t)
    rw [iteratedDeriv_eq_pderiv1Iter (Work.OddVolterra.Existence.isOpen_psiPos (hh.of_le le_top))
      (Work.OddVolterra.Existence.contDiffOn_PhiH (hh.of_le le_top) n) hmem n]
    rfl
  rw [hstep1]
  exact (integral_comp_sin (g := fun t => G2 n h (s, t))).symm

lemma E2_one_eq_theta_integral (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ⊤ h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100) :
    E2 n h 1 = ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        G2 n h (1, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ) := by
  have hstep1 : E2 n h 1 = ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
      (fun t : ℝ => iteratedDeriv n
        (fun u : ℝ => Work.OddVolterra.Existence.PhiH n h (u, t)) 1)
        (profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ) := by
    rw [show E2 n h 1 = ∫ t in (-(profileX 1))..(profileX 1),
        (fun t : ℝ => iteratedDeriv n
          (fun u : ℝ => Work.OddVolterra.Existence.PhiH n h (u, t)) 1) t from rfl]
    exact (integral_comp_sin (g := fun t : ℝ => iteratedDeriv n
      (fun u : ℝ => Work.OddVolterra.Existence.PhiH n h (u, t)) 1)).symm
  rw [hstep1]
  refine intervalIntegral.integral_congr (fun θ hθ => ?_)
  by_cases htop : |θ| = Real.pi / 2
  · have hcos0 : Real.cos θ = 0 := by
      rcases (abs_eq (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 2)).mp htop with h | h
      · rw [h, Real.cos_pi_div_two]
      · rw [h, Real.cos_neg, Real.cos_pi_div_two]
    simp [hcos0]
  · have hθ' : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
      exact ⟨hθ.1, hθ.2⟩
    have habs : |θ| < Real.pi / 2 := lt_of_le_of_ne (abs_le.mpr ⟨hθ'.1, hθ'.2⟩) htop
    have hmem : (1, profileX 1 * Real.sin θ) ∈ Work.OddVolterra.Existence.psiPos h := by
      show 0 < psi h semicircle 1 (profileX 1 * Real.sin θ)
      rw [psi_sin_eq hsupp (s := 1) (by rw [one_sub_tau_eq]; norm_num)]
      have hc : 0 < Real.cos θ := by
        rw [abs_lt] at habs
        exact Real.cos_pos_of_mem_Ioo ⟨habs.1, habs.2⟩
      nlinarith [hc, sq_nonneg (Real.sin θ)]
    show iteratedDeriv n (fun u : ℝ => Work.OddVolterra.Existence.PhiH n h (u, profileX 1 * Real.sin θ)) 1
      * (profileX 1 * Real.cos θ) = G2 n h (1, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ)
    rw [iteratedDeriv_eq_pderiv1Iter (Work.OddVolterra.Existence.isOpen_psiPos (hh.of_le le_top))
      (Work.OddVolterra.Existence.contDiffOn_PhiH (hh.of_le le_top) n) hmem n]
    rfl

/-! ## Dominated convergence for the `θ`-integrals -/

lemma theta_Ioo_mem_nhds : Set.Ioo (9 / 10 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := by
  have h1 : Set.Ioi (9 / 10 : ℝ) ∈ 𝓝[<] (1 : ℝ) :=
    nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num))
  have h2 : Set.Iio (1 : ℝ) ∈ 𝓝[<] (1 : ℝ) := self_mem_nhdsWithin
  have h := inter_mem h1 h2
  convert h using 1
  ext x
  simp [Set.mem_Ioo, Set.mem_Ioi, Set.mem_Iio]

lemma tendsto_theta_integral {h : ℝ → ℝ} {G : ℝ × ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hopen : IsOpen (Work.OddVolterra.Existence.psiPos h))
    (hG : ContinuousOn G (Work.OddVolterra.Existence.psiPos h))
    (hposS : ∀ s, 9 / 10 < s → s < 1 → ∀ θ,
      (s, profileX 1 * Real.sin θ) ∈ Work.OddVolterra.Existence.psiPos h)
    (hpos1 : ∀ θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
      (1, profileX 1 * Real.sin θ) ∈ Work.OddVolterra.Existence.psiPos h)
    (hbd : ∀ s, 9 / 10 < s → s < 1 →
      ∀ θ ∈ Set.uIcc (-(Real.pi / 2)) (Real.pi / 2),
        |G (s, profileX 1 * Real.sin θ)| * (profileX 1 * Real.cos θ) ≤ C) :
    Tendsto (fun s => ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        G (s, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ))
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        G (1, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ))) := by
  set F : ℝ → ℝ → ℝ :=
    fun s θ => G (s, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ) with hF
  set μ : Measure ℝ := volume.restrict (Set.Ioc (-(Real.pi / 2)) (Real.pi / 2)) with hμ
  have hab : -(Real.pi / 2) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hmeas : ∀ᶠ s in 𝓝[<] (1 : ℝ), AEStronglyMeasurable (F s) μ := by
    filter_upwards [theta_Ioo_mem_nhds] with s hs
    have hcont : Continuous (F s) := by
      have h1 : Continuous (fun θ : ℝ => G (s, profileX 1 * Real.sin θ)) :=
        hG.comp_continuous (by fun_prop) (hposS s hs.1 hs.2)
      have h2 : Continuous fun θ : ℝ => profileX 1 * Real.cos θ := by fun_prop
      exact h1.mul h2
    exact (hcont.aestronglyMeasurable (μ := volume)).mono_measure Measure.restrict_le_self
  have hbound : ∀ᶠ s in 𝓝[<] (1 : ℝ), ∀ᵐ θ ∂μ, ‖F s θ‖ ≤ C := by
    filter_upwards [theta_Ioo_mem_nhds] with s hs
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with θ hθ
    have hθIcc : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨hθ.1.le, hθ.2⟩
    have hθu : θ ∈ Set.uIcc (-(Real.pi / 2)) (Real.pi / 2) := by
      rwa [Set.uIcc_of_le hab]
    rw [Real.norm_eq_abs, hF, abs_mul,
      abs_of_nonneg (mul_nonneg profileX_one_pos.le (cos_nonneg_of_mem_uIcc hθu))]
    exact hbd s hs.1 hs.2 θ hθu
  have hint : Integrable (fun _ : ℝ => C) μ := by
    have h : MeasureTheory.IntegrableOn (fun _ : ℝ => C)
        (Set.Ioc (-(Real.pi / 2)) (Real.pi / 2)) volume :=
      MeasureTheory.integrableOn_const (μ := volume)
        (measure_Ioc_lt_top (μ := volume)).ne
        (by rw [Real.enorm_eq_ofReal hC]; exact ENNReal.ofReal_ne_top)
    exact h
  have hlim : ∀ᵐ θ ∂μ, Tendsto (fun s => F s θ) (𝓝[<] (1 : ℝ)) (𝓝 (F 1 θ)) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with θ hθ
    have hθIcc : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨hθ.1.le, hθ.2⟩
    by_cases htop : |θ| = Real.pi / 2
    · have hcos0 : Real.cos θ = 0 := by
        rcases (abs_eq (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 2)).mp htop with h | h
        · rw [h, Real.cos_pi_div_two]
        · rw [h, Real.cos_neg, Real.cos_pi_div_two]
      have hz : ∀ s : ℝ, F s θ = 0 := fun s => by
        simp [hF, hcos0]
      rw [show F 1 θ = 0 from hz 1]
      simpa [hz] using tendsto_const_nhds
    · have hmem : (1, profileX 1 * Real.sin θ) ∈ Work.OddVolterra.Existence.psiPos h := by
        have habs : |θ| < Real.pi / 2 := lt_of_le_of_ne (abs_le.mpr ⟨hθIcc.1, hθIcc.2⟩) htop
        rw [abs_lt] at habs
        exact hpos1 θ ⟨habs.1, habs.2⟩
      have hGc : ContinuousAt G (1, profileX 1 * Real.sin θ) :=
        hG.continuousAt (hopen.mem_nhds hmem)
      have hmap : ContinuousAt (fun s : ℝ => (s, profileX 1 * Real.sin θ)) 1 := by fun_prop
      have h1 : Tendsto (fun s : ℝ => G (s, profileX 1 * Real.sin θ)) (𝓝[<] (1 : ℝ))
          (𝓝 (G (1, profileX 1 * Real.sin θ))) :=
        (hGc.comp (x := (1 : ℝ)) hmap).tendsto.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto (fun s : ℝ => profileX 1 * Real.cos θ) (𝓝[<] (1 : ℝ))
          (𝓝 (profileX 1 * Real.cos θ)) := tendsto_const_nhds
      simpa [hF] using h1.mul h2
  have hdct := MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := μ)
    (F := F) (f := F 1) (fun _ : ℝ => C) hmeas hbound hint hlim
  have h1 : (fun s => ∫ θ, F s θ ∂μ)
      = fun s => ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), F s θ := by
    funext s
    rw [intervalIntegral.integral_of_le hab]
  have h2 : (∫ θ, F 1 θ ∂μ) = ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), F 1 θ := by
    rw [intervalIntegral.integral_of_le hab]
  rw [h1, h2] at hdct
  exact hdct


/-! ## Left limits at `s = 1` -/

lemma tendsto_E1 (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ⊤ h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100) :
    Tendsto (E1 n h) (𝓝[<] (1 : ℝ)) (𝓝 (E1 n h 1)) := by
  obtain ⟨C, hC0, hC⟩ := E1_theta_bound n hh hsupp hsmall
  have hdct := tendsto_theta_integral (G := G1 n h) hC0
    (Work.OddVolterra.Existence.isOpen_psiPos (hh.of_le le_top))
    (contDiffOn_G1 n (hh.of_le le_top)).continuousOn
    (fun s hs0 hs1 θ => psi_sin_pos hsupp (by rw [one_sub_tau_eq]; exact hs0) hs1 θ)
    (fun θ hθ => by
      show 0 < psi h semicircle 1 (profileX 1 * Real.sin θ)
      rw [psi_sin_eq hsupp (s := 1) (by rw [one_sub_tau_eq]; norm_num)]
      have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo hθ
      nlinarith [hc, sq_nonneg (Real.sin θ)])
    hC
  have h1 : (fun s => ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        G1 n h (s, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ))
      =ᶠ[𝓝[<] (1 : ℝ)] fun s => E1 n h s := by
    filter_upwards [theta_Ioo_mem_nhds] with s hs
    exact (E1_eq_theta_integral n hh hsupp hsmall hs.1 hs.2).symm
  have h2 : (∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        G1 n h (1, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ)) = E1 n h 1 :=
    (E1_one_eq_theta_integral n hh hsupp hsmall).symm
  rw [h2] at hdct
  exact hdct.congr' h1

lemma tendsto_E2 (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ⊤ h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100) :
    Tendsto (E2 n h) (𝓝[<] (1 : ℝ)) (𝓝 (E2 n h 1)) := by
  obtain ⟨C, hC0, hC⟩ := E2_theta_bound n hh hsupp hsmall
  have hdct := tendsto_theta_integral (G := G2 n h) hC0
    (Work.OddVolterra.Existence.isOpen_psiPos (hh.of_le le_top))
    (contDiffOn_G2 n (hh.of_le le_top)).continuousOn
    (fun s hs0 hs1 θ => psi_sin_pos hsupp (by rw [one_sub_tau_eq]; exact hs0) hs1 θ)
    (fun θ hθ => by
      show 0 < psi h semicircle 1 (profileX 1 * Real.sin θ)
      rw [psi_sin_eq hsupp (s := 1) (by rw [one_sub_tau_eq]; norm_num)]
      have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo hθ
      nlinarith [hc, sq_nonneg (Real.sin θ)])
    hC
  have h1 : (fun s => ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        G2 n h (s, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ))
      =ᶠ[𝓝[<] (1 : ℝ)] fun s => E2 n h s := by
    filter_upwards [theta_Ioo_mem_nhds] with s hs
    exact (E2_eq_theta_integral n hh hsupp hsmall hs.1 hs.2).symm
  have h2 : (∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        G2 n h (1, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ)) = E2 n h 1 :=
    (E2_one_eq_theta_integral n hh hsupp hsmall).symm
  rw [h2] at hdct
  exact hdct.congr' h1

lemma continuousWithinAt_Icc_one_of_tendsto {f : ℝ → ℝ} :
    Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 (f 1)) → ∀ a : ℝ, ContinuousWithinAt f (Set.Icc a 1) 1 := by
  intro h a
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hball : f ⁻¹' Metric.ball (f 1) ε ∈ 𝓝[<] (1 : ℝ) := h (Metric.ball_mem_nhds (f 1) hε)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.mem_nhdsWithin_iff.mp hball
  refine ⟨δ, hδ, fun y hy hdist => ?_⟩
  rcases eq_or_lt_of_le hy.2 with heq | hlt
  · rw [heq, dist_self]; exact hε
  · refine hδ' ⟨?_, hlt⟩
    exact hdist

lemma continuousWithinAt_Icc_of_Icc {f : ℝ → ℝ} {a b c : ℝ} (hab : a < b) (hb : b < c)
    (h : ContinuousWithinAt f (Set.Icc a b) a) : ContinuousWithinAt f (Set.Icc a c) a := by
  rw [Metric.continuousWithinAt_iff] at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := h ε hε
  refine ⟨min δ (b - a), lt_min hδ (by linarith), fun y hy hdist => ?_⟩
  rw [Real.dist_eq] at hdist
  have hy1 : a ≤ y := hy.1
  have hdist' : |y - a| < δ := lt_of_lt_of_le hdist (min_le_left _ _)
  have : y - a < b - a := lt_of_lt_of_le (abs_lt.mp hdist).2 (min_le_right _ _)
  exact hδ' ⟨hy1, by linarith⟩ hdist'

/-! ## The main theorem -/

lemma contDiffOn_E1_Icc (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ⊤ h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100) {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    ContDiffOn ℝ (⊤ : ℕ∞) (E1 n h) (Set.Icc a b) := by
  intro s hs
  have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
  have hs1 : s < 1 := lt_of_le_of_lt hs.2 hb
  have htube : ∀ t ∈ Set.uIcc (-(profileX 1)) (profileX 1),
      (s, t) ∈ Work.OddVolterra.Existence.psiPos h := by
    intro t ht
    have ht1 : |t| ≤ profileX 1 := by
      rw [Set.uIcc_of_le (by linarith [profileX_one_pos])] at ht
      exact abs_le.mpr ht
    exact psi_pos_of_window hsupp hsmall hs0 hs1 ht1
  have hcd := Work.OddVolterra.Existence.contDiffAt_integral_iteratedDeriv
    (W := Work.OddVolterra.Existence.psiPos h)
    (F := Work.OddVolterra.Existence.PhiF n h)
    (c := -(profileX 1)) (d := profileX 1)
    (Work.OddVolterra.Existence.isOpen_psiPos (hh.of_le le_top))
    (Work.OddVolterra.Existence.contDiffOn_PhiF (hh.of_le le_top) n) (n + 1) htube
  exact (show ContDiffAt ℝ (⊤ : ℕ∞) (E1 n h) s from hcd).contDiffWithinAt

lemma contDiffOn_E2_Icc (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ⊤ h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100) {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    ContDiffOn ℝ (⊤ : ℕ∞) (E2 n h) (Set.Icc a b) := by
  intro s hs
  have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
  have hs1 : s < 1 := lt_of_le_of_lt hs.2 hb
  have htube : ∀ t ∈ Set.uIcc (-(profileX 1)) (profileX 1),
      (s, t) ∈ Work.OddVolterra.Existence.psiPos h := by
    intro t ht
    have ht1 : |t| ≤ profileX 1 := by
      rw [Set.uIcc_of_le (by linarith [profileX_one_pos])] at ht
      exact abs_le.mpr ht
    exact psi_pos_of_window hsupp hsmall hs0 hs1 ht1
  have hcd := Work.OddVolterra.Existence.contDiffAt_integral_iteratedDeriv
    (W := Work.OddVolterra.Existence.psiPos h)
    (F := Work.OddVolterra.Existence.PhiH n h)
    (c := -(profileX 1)) (d := profileX 1)
    (Work.OddVolterra.Existence.isOpen_psiPos (hh.of_le le_top))
    (Work.OddVolterra.Existence.contDiffOn_PhiH (hh.of_le le_top) n) n htube
  exact (show ContDiffAt ℝ (⊤ : ℕ∞) (E2 n h) s from hcd).contDiffWithinAt

theorem E1_E2_regularity (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ⊤ h) {a : ℝ} (ha : 0 < a)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100) :
    ContinuousOn (Work.OddVolterra.E1 n h) (Set.Icc a 1) ∧
    ContinuousOn (Work.OddVolterra.E2 n h) (Set.Icc a 1) ∧
    (∀ b : ℝ, a ≤ b → b < 1 → ContDiffOn ℝ (⊤ : ℕ∞) (Work.OddVolterra.E1 n h) (Set.Icc a b)) ∧
    (∀ b : ℝ, a ≤ b → b < 1 → ContDiffOn ℝ (⊤ : ℕ∞) (Work.OddVolterra.E2 n h) (Set.Icc a b)) := by
  have htE1 := tendsto_E1 n hh hsupp hsmall
  have htE2 := tendsto_E2 n hh hsupp hsmall
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · have hCD := contDiffOn_E1_Icc n hh hsupp hsmall ha (b := (s + 1) / 2) (by linarith)
      rcases lt_or_eq_of_le hs.1 with hlt2 | heq2
      · have hmem : Set.Icc a ((s + 1) / 2) ∈ 𝓝 s := Icc_mem_nhds hlt2 (by linarith)
        exact ((hCD.contDiffAt hmem).continuousAt).continuousWithinAt
      · rw [← heq2]
        exact continuousWithinAt_Icc_of_Icc (by linarith) (by linarith)
          (hCD.continuousOn.continuousWithinAt ⟨le_refl a, by linarith⟩)
    · rw [heq]
      exact continuousWithinAt_Icc_one_of_tendsto htE1 a
  · intro s hs
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · have hCD := contDiffOn_E2_Icc n hh hsupp hsmall ha (b := (s + 1) / 2) (by linarith)
      rcases lt_or_eq_of_le hs.1 with hlt2 | heq2
      · have hmem : Set.Icc a ((s + 1) / 2) ∈ 𝓝 s := Icc_mem_nhds hlt2 (by linarith)
        exact ((hCD.contDiffAt hmem).continuousAt).continuousWithinAt
      · rw [← heq2]
        exact continuousWithinAt_Icc_of_Icc (by linarith) (by linarith)
          (hCD.continuousOn.continuousWithinAt ⟨le_refl a, by linarith⟩)
    · rw [heq]
      exact continuousWithinAt_Icc_one_of_tendsto htE2 a
  · intro b hab hb1
    exact contDiffOn_E1_Icc n hh hsupp hsmall ha hb1
  · intro b hab hb1
    exact contDiffOn_E2_Icc n hh hsupp hsmall ha hb1

end

end Work.OddVolterra.Smooth
