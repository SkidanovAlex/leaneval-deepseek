import Mathlib

namespace Work.FunctionalEquations

open scoped SchwartzMap

noncomputable section

/-!
# Comparing Schwartz seminorms

For a Schwartz function `g` on `ℝ^n` and `a + 1 ≤ P` we prove

`(SchwartzMap.seminorm ℂ a 1) g ≤ C * ((SchwartzMap.seminorm ℂ P 0) g + (SchwartzMap.seminorm ℂ 0 P) g)`

for a constant `C` depending only on `n` and `P`.  Equivalently: the weighted first derivative
`sup_x ‖x‖^a ‖Dg(x)‖` is controlled by the unweighted `P`-th derivative `sup ‖D^P g‖` together
with the weighted decay `sup_x ‖x‖^P ‖g(x)‖`.

The proof is the classical finite-difference (Landau–Kolmogorov) argument: the derivative at a
point is a fixed linear combination of the values at the `P` nodes `δ, 2δ, …, Pδ` (Lagrange
interpolation), with an error controlled by the `P`-th derivative (Taylor's theorem); the scale
`δ` is then chosen in terms of `‖x‖`.
-/

open Polynomial

/-! ## Two elementary auxiliary lemmas -/

/-- At `x = 0` the Taylor sum of `v` collapses to `v 0`. -/
private lemma sum_range_factorial_zero_pow {F : Type*} [AddCommMonoid F] [Module ℝ F]
    (N : ℕ) (hN : 1 ≤ N) (v : ℕ → F) :
    ∑ k ∈ Finset.range N, ((k.factorial : ℝ)⁻¹ * (0:ℝ) ^ k) • v k = v 0 := by
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    rw [zero_pow hk0, mul_zero, zero_smul]
  · intro h0
    simp at h0
    omega

/-- `↑(P-1) + 1 = ↑P` in the extended naturals, for `P ≥ 1`. -/
private lemma enat_cast_pred_add_one (P : ℕ) (hP1 : 1 ≤ P) :
    (↑(P-1) + 1 : WithTop ℕ∞) = (↑P : WithTop ℕ∞) := by
  obtain ⟨k, rfl⟩ : ∃ k, P = k + 1 := ⟨P - 1, (Nat.sub_add_cancel hP1).symm⟩
  simp

/-- Taylor's theorem with the crude remainder bound `A * x^(n+1)`. -/
theorem taylor_remainder_bound_iteratedDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (n : ℕ) {b A : ℝ} (hA : 0 ≤ A)
    (hf : ContDiff ℝ (n+1) f)
    (hbound : ∀ t ∈ Set.Icc 0 b, ‖iteratedDeriv (n+1) f t‖ ≤ A) :
    ∀ x ∈ Set.Icc 0 b,
      ‖f x - ∑ k ∈ Finset.range (n+1), ((k.factorial : ℝ)⁻¹ * x ^ k) • iteratedDeriv k f 0‖ ≤
        A * x ^ (n+1) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hx0 | hxpos
  · subst hx0
    have hsum : ∑ k ∈ Finset.range (n+1),
        ((k.factorial : ℝ)⁻¹ * (0:ℝ) ^ k) • iteratedDeriv k f 0 = f 0 :=
      sum_range_factorial_zero_pow (n+1) (Nat.succ_le_succ (Nat.zero_le n)) _
    rw [hsum, sub_self, norm_zero]
    simp [zero_pow (Nat.succ_ne_zero n)]
  · have hCd : ContDiffOn ℝ (↑n + 1) f (Set.Icc 0 x) := hf.contDiffOn
    have hrem := taylor_mean_remainder_bound (f := f) (a := 0) (b := x) (C := A) (x := x) (n := n)
      hxpos.le hCd (Set.right_mem_Icc.mpr hxpos.le) ?_
    · have htw : taylorWithinEval f n (Set.Icc 0 x) 0 x =
          ∑ k ∈ Finset.range (n+1), ((k.factorial : ℝ)⁻¹ * x ^ k) • iteratedDeriv k f 0 := by
        rw [taylor_within_apply]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hklt : k < n+1 := Finset.mem_range.mp hk
        have hCdk : ContDiffAt ℝ (k : ℕ∞) f 0 := hf.contDiffAt.of_le (by exact_mod_cast hklt.le)
        have hmem0 : (0:ℝ) ∈ Set.Icc 0 x := Set.mem_Icc.mpr ⟨le_rfl, hxpos.le⟩
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hxpos) hCdk hmem0, sub_zero]
      rw [htw] at hrem
      simp only [sub_zero] at hrem
      calc ‖f x - ∑ k ∈ Finset.range (n+1), ((k.factorial : ℝ)⁻¹ * x ^ k) • iteratedDeriv k f 0‖
          ≤ A * x ^ (n+1) / (n.factorial : ℝ) := hrem
        _ ≤ A * x ^ (n+1) := by
            rw [div_le_iff₀ (by positivity : (0:ℝ) < (n.factorial : ℝ))]
            have h1 : (1:ℝ) ≤ (n.factorial : ℝ) := by
              exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
            exact le_mul_of_one_le_right (mul_nonneg hA (pow_nonneg hxpos.le (n+1))) h1
    · intro y hy
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hxpos) (hf.contDiffAt) hy]
      exact hbound y ⟨hy.1, le_trans hy.2 hx.2⟩

/-! ## Lagrange coefficients -/

private lemma basisDivisor_eval_zero (x y : ℂ) :
    (Lagrange.basisDivisor x y).eval 0 = -(x - y)⁻¹ * y := by
  simp [Lagrange.basisDivisor]

private lemma basisDivisor_derivative_eval_zero (x y : ℂ) :
    (Polynomial.derivative (Lagrange.basisDivisor x y)).eval 0 = (x - y)⁻¹ := by
  simp [Lagrange.basisDivisor]

private lemma one_le_abs_natCast_sub (a b : ℕ) (hab : a ≠ b) : (1:ℝ) ≤ |(a:ℝ) - b| := by
  rcases lt_or_gt_of_ne hab with h | h
  · have h' : (a:ℝ) < (b:ℝ) := by exact_mod_cast h
    rw [abs_of_neg (by linarith)]
    have h2 : ((a:ℕ) + 1 : ℝ) ≤ (b:ℝ) := by
      have : (a:ℕ) + 1 ≤ b := Nat.succ_le_iff.mpr h
      exact_mod_cast this
    linarith
  · have h' : (b:ℝ) < (a:ℝ) := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]
    have h2 : ((b:ℕ) + 1 : ℝ) ≤ (a:ℝ) := by
      have : (b:ℕ) + 1 ≤ a := Nat.succ_le_iff.mpr h
      exact_mod_cast this
    linarith

/-- **Lagrange finite differences.**  For the `P` nodes `δ, 2δ, …, Pδ` there are coefficients
`d i` such that `Q'(0) = ∑ i, d i * Q ((i+1)δ)` for every polynomial of degree `< P`, and these
coefficients are bounded by `P^P / |δ|`. -/
theorem LagrangeDerivCoeff (P : ℕ) (δ : ℝ) (hδ : δ ≠ 0) :
    ∃ d : Fin P → ℂ, (∀ i, ‖d i‖ ≤ (P : ℝ) ^ P / |δ|) ∧
      ∀ Q : Polynomial ℂ, Q.degree < P →
        (Polynomial.derivative Q).eval 0 =
          ∑ i : Fin P, d i * Q.eval ((((i : ℕ) + 1 : ℝ) * δ : ℝ) : ℂ) := by
  classical
  set v : Fin P → ℂ := fun j => ((((j:ℕ)+1:ℝ)*δ:ℝ):ℂ) with hv
  refine ⟨fun i => (Polynomial.derivative (Lagrange.basis Finset.univ v i)).eval 0, ?_, ?_⟩
  · intro i
    dsimp only
    set s : Finset (Fin P) := (Finset.univ : Finset (Fin P)).erase i with hs
    have hδpos : 0 < |δ| := abs_pos.mpr hδ
    have hP1 : 1 ≤ P := by have := i.isLt; omega
    have hvn : ∀ b : Fin P, ‖v b‖ ≤ (P:ℝ) * |δ| := by
      intro b
      rw [hv]
      simp only [Complex.norm_real]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((b:ℕ):ℝ)+1)]
      have hb : ((b:ℕ):ℝ) + 1 ≤ (P:ℝ) := by
        have := b.isLt; exact_mod_cast Nat.succ_le_of_lt this
      exact mul_le_mul_of_nonneg_right hb (abs_nonneg δ)
    have hvd : ∀ a b : Fin P, a ≠ b → |δ| ≤ ‖v a - v b‖ := by
      intro a b hab
      have hab' : (a:ℕ) ≠ (b:ℕ) := fun h => hab (Fin.ext h)
      have heq : v a - v b = (((((a:ℕ):ℝ) + 1 - (((b:ℕ):ℝ) + 1)) * δ : ℝ) : ℂ) := by
        simp only [hv, ← Complex.ofReal_sub]
        congr 1
        ring
      have h1 := one_le_abs_natCast_sub (a:ℕ) (b:ℕ) hab'
      have h2 : |(((a:ℕ):ℝ) + 1 - (((b:ℕ):ℝ) + 1))| = |((a:ℕ):ℝ) - ((b:ℕ):ℝ)| := by
        ring_nf
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_mul, h2]
      exact le_mul_of_one_le_left (abs_nonneg δ) h1
    have hmem : ∀ a ∈ s, a ≠ i := by
      intro a ha; rw [hs] at ha; exact (Finset.mem_erase.mp ha).1
    have hs_card : s.card = P - 1 := by rw [hs]; simp
    have hbasis : Lagrange.basis Finset.univ v i =
        ∏ j ∈ s, Lagrange.basisDivisor (v i) (v j) := by rw [hs]; rfl
    rw [hbasis, Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum]
    have H : ∀ a ∈ s, ‖Polynomial.eval 0 ((∏ b ∈ s.erase a, Lagrange.basisDivisor (v i) (v b)) *
          Polynomial.derivative (Lagrange.basisDivisor (v i) (v a)))‖ ≤ (P:ℝ)^(P-1)/|δ| := by
      intro a ha
      have hai : a ≠ i := hmem a ha
      rw [Polynomial.eval_mul, Polynomial.eval_prod, norm_mul, norm_prod,
        basisDivisor_derivative_eval_zero]
      have hprod : (∏ b ∈ s.erase a,
          ‖Polynomial.eval 0 (Lagrange.basisDivisor (v i) (v b))‖) ≤ (P:ℝ)^(P-1) := by
        calc ∏ b ∈ s.erase a, ‖Polynomial.eval 0 (Lagrange.basisDivisor (v i) (v b))‖
            ≤ ∏ _b ∈ s.erase a, (P:ℝ) := by
              refine Finset.prod_le_prod₀ (fun b _ => norm_nonneg _) (fun b hb => ?_)
              have hbi : b ≠ i := hmem b (Finset.mem_of_mem_erase hb)
              have hd := hvd i b (Ne.symm hbi)
              rw [basisDivisor_eval_zero, norm_mul, norm_neg, norm_inv]
              have h1 : ‖v i - v b‖⁻¹ ≤ (1:ℝ)/|δ| := by
                simpa only [one_div] using one_div_le_one_div_of_le hδpos hd
              have h2 := hvn b
              calc ‖v i - v b‖⁻¹ * ‖v b‖ ≤ (1/|δ|) * ((P:ℝ)*|δ|) :=
                    mul_le_mul h1 h2 (norm_nonneg _) (div_nonneg zero_le_one (abs_nonneg δ))
                _ = P := by
                    have hδne : |δ| ≠ 0 := ne_of_gt hδpos
                    field_simp
          _ = (P:ℝ) ^ (s.erase a).card := Finset.prod_const _
          _ ≤ (P:ℝ) ^ (P-1) := by
              refine pow_le_pow_right₀ (show (1:ℝ) ≤ (P:ℝ) by exact_mod_cast hP1) ?_
              have := Finset.card_le_card (Finset.erase_subset a s)
              omega
      have hinv : ‖(v i - v a)⁻¹‖ ≤ (1:ℝ)/|δ| := by
        have hd := hvd i a (Ne.symm hai)
        simpa only [norm_inv, one_div] using one_div_le_one_div_of_le hδpos hd
      exact (mul_le_mul hprod hinv (norm_nonneg _)
        (pow_nonneg (Nat.cast_nonneg P) _)).trans_eq (by ring)
    calc ‖∑ a ∈ s, Polynomial.eval 0 ((∏ b ∈ s.erase a, Lagrange.basisDivisor (v i) (v b)) *
          Polynomial.derivative (Lagrange.basisDivisor (v i) (v a)))‖
        ≤ ∑ a ∈ s, ‖Polynomial.eval 0 ((∏ b ∈ s.erase a, Lagrange.basisDivisor (v i) (v b)) *
          Polynomial.derivative (Lagrange.basisDivisor (v i) (v a)))‖ := norm_sum_le _ _
      _ ≤ ∑ _a ∈ s, (P:ℝ)^(P-1)/|δ| := Finset.sum_le_sum H
      _ = s.card * ((P:ℝ)^(P-1)/|δ|) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((P-1 : ℕ) : ℝ) * ((P:ℝ)^(P-1)/|δ|) := by rw [hs_card]
      _ ≤ (P:ℝ)^P/|δ| := by
          rw [Nat.cast_sub hP1, Nat.cast_one]
          have h2 : ((P:ℝ) - 1) * (P:ℝ)^(P-1) ≤ (P:ℝ)^P := by
            calc ((P:ℝ) - 1) * (P:ℝ)^(P-1) ≤ (P:ℝ) * (P:ℝ)^(P-1) :=
                  mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (Nat.cast_nonneg P) _)
              _ = (P:ℝ)^P := by
                  rw [← pow_succ']
                  congr 1
                  omega
          calc ((P:ℝ) - 1) * ((P:ℝ)^(P-1)/|δ|) = (((P:ℝ) - 1) * (P:ℝ)^(P-1))/|δ| := by ring
            _ ≤ (P:ℝ)^P/|δ| := div_le_div_of_nonneg_right h2 (abs_nonneg δ)
  · intro Q hQ
    have hv_inj : Function.Injective v := by
      intro a b hab
      have h1 : ((a:ℕ)+1 : ℝ) * δ = ((b:ℕ)+1 : ℝ) * δ := by
        simpa [hv] using congrArg Complex.re hab
      have h2 : ((a:ℕ)+1 : ℝ) = ((b:ℕ)+1 : ℝ) := mul_right_cancel₀ hδ h1
      have h3 : (a:ℕ) + 1 = (b:ℕ) + 1 := by exact_mod_cast h2
      exact Fin.ext (Nat.succ.inj h3)
    have hdeg : Q.degree < (↑(Finset.univ : Finset (Fin P)).card : WithBot ℕ) := by
      simpa using hQ
    have hQeq : Q = Lagrange.interpolate Finset.univ v (fun i => Q.eval (v i)) :=
      Lagrange.eq_interpolate (s := Finset.univ) hv_inj.injOn hdeg
    conv_lhs => rw [hQeq]
    rw [Lagrange.interpolate_apply, Polynomial.derivative_sum, Polynomial.eval_finsetSum]
    simp only [Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring

/-! ## The chain rule along an affine line -/

/-- The `k`-th derivative along the line `t ↦ g (x + t • u)`, controlled by the norm of the
`k`-th Fréchet derivative of `g`. -/
private lemma norm_iteratedDeriv_affine_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℂ) (x u : E) (k : ℕ) (t : ℝ) (hg : ContDiff ℝ k g) :
    ‖iteratedDeriv k (fun s : ℝ => g (x + s • u)) t‖ ≤
      ‖iteratedFDeriv ℝ k g (x + t • u)‖ * ‖u‖^k := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hU : (fun s : ℝ => g (x + s • u)) =
      (fun y : E => g (x + y)) ∘ (ContinuousLinearMap.toSpanSingleton ℝ u) := by
    ext s; simp [ContinuousLinearMap.toSpanSingleton_apply]
  rw [hU]
  have hgc : ContDiff ℝ k (fun y : E => g (x + y)) := by
    show ContDiff ℝ k (g ∘ fun y : E => x + y)
    exact hg.comp (contDiff_const.add contDiff_id)
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.toSpanSingleton ℝ u)
      hgc t le_rfl]
  calc _ ≤ ‖iteratedFDeriv ℝ k (fun y : E => g (x + y))
          ((ContinuousLinearMap.toSpanSingleton ℝ u) t)‖ *
        ∏ _i : Fin k, ‖ContinuousLinearMap.toSpanSingleton ℝ u‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ k g (x + t • u)‖ * ‖u‖^k := by
        rw [ContinuousLinearMap.toSpanSingleton_apply, iteratedFDeriv_comp_add_left]
        simp [ContinuousLinearMap.norm_toSpanSingleton, Finset.prod_const]

/-! ## The core finite-difference estimate -/

/-- **Core finite-difference estimate.**  The derivative at `0` of a smooth `g : ℝ → ℂ` is
controlled by the values at the nodes `δ, 2δ, …, Pδ` (with constant `B`) and by the `P`-th
derivative (with constant `A`). -/
theorem finite_difference_core (P : ℕ) (hP : 2 ≤ P) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : ℝ → ℂ) (δ A B : ℝ), 0 < δ → 0 ≤ A → 0 ≤ B →
      ContDiff ℝ P g →
      (∀ t ∈ Set.Icc 0 (P*δ), ‖iteratedDeriv P g t‖ ≤ A) →
      (∀ i : Fin P, ‖g ((((i:ℕ)+1 : ℝ) * δ))‖ ≤ B) →
      ‖deriv g 0‖ ≤ K * (B / δ + A * δ ^ (P-1)) := by
  have hP1 : 1 ≤ P := by omega
  refine ⟨(P:ℝ)^(2*P+1) + 1, by positivity, ?_⟩
  intro g δ A B hδ hA hB hg hgd hgv
  obtain ⟨d, hdbd₀, hdid⟩ := LagrangeDerivCoeff P δ (ne_of_gt hδ)
  have hdbd : ∀ i : Fin P, ‖d i‖ ≤ (P:ℝ)^P / δ := fun i => by
    simpa [abs_of_pos hδ] using hdbd₀ i
  set v : ℕ → ℂ := fun k => iteratedDeriv k g 0 with hv
  set Q : Polynomial ℂ :=
    ∑ k ∈ Finset.range P, Polynomial.C (((k.factorial : ℝ)⁻¹ : ℂ) * v k) * Polynomial.X ^ k
    with hQ
  set T : ℝ → ℂ := fun x => Q.eval ((x:ℝ):ℂ) with hT
  have hTeq : ∀ x : ℝ, T x = ∑ k ∈ Finset.range P,
      ((k.factorial : ℝ)⁻¹ * x ^ k) • v k := by
    intro x
    rw [hT, hQ]
    dsimp only
    rw [Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [Complex.real_smul]
    push_cast
    ring_nf
  have hQdeg : Q.degree < (P : WithBot ℕ) := by
    rw [hQ]
    calc (∑ k ∈ Finset.range P,
          Polynomial.C (((k.factorial:ℝ)⁻¹:ℂ) * v k) * Polynomial.X^k).degree
        ≤ ((P-1 : ℕ) : WithBot ℕ) := by
          refine le_trans (Polynomial.degree_sum_le _ _) ?_
          refine Finset.sup_le fun k hk => ?_
          refine le_trans (Polynomial.degree_C_mul_X_pow_le k _) ?_
          rw [Finset.mem_range] at hk
          exact_mod_cast (by omega : k ≤ P - 1)
      _ < (P : WithBot ℕ) := by
          exact_mod_cast (by omega : P - 1 < P)
  have hQd : Q.derivative.eval 0 = deriv g 0 := by
    rw [hQ]
    have hcoeff : (Polynomial.derivative (∑ k ∈ Finset.range P,
        Polynomial.C (((k.factorial:ℝ)⁻¹:ℂ) * v k) * Polynomial.X^k)).eval 0 = v 1 := by
      rw [Polynomial.derivative_sum, Polynomial.eval_finsetSum]
      rw [Finset.sum_eq_single 1]
      · simp
      · intro k hk hk1
        rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow]
        simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0; simp
        · rw [zero_pow (by omega : k - 1 ≠ 0)]; ring
      · intro h1; simp at h1; omega
    rw [hcoeff, hv]
    simp [iteratedDeriv_one]
  have hTderiv : HasDerivAt T (deriv g 0) 0 := by
    have hfun : T = fun x : ℝ => ∑ k ∈ Finset.range P,
        ((k.factorial : ℝ)⁻¹ * x ^ k) • v k := funext hTeq
    rw [hfun]
    have hval : (∑ k ∈ Finset.range P,
        ((k.factorial : ℝ)⁻¹ * ((k:ℝ) * (0:ℝ) ^ (k-1))) • v k) = deriv g 0 := by
      rw [Finset.sum_eq_single 1]
      · simp [hv, iteratedDeriv_one]
      · intro k hk hk1
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0; simp
        · rw [zero_pow (by omega : k - 1 ≠ 0), mul_zero, mul_zero, zero_smul]
      · intro h1; simp at h1; omega
    rw [← hval]
    have hsum := HasDerivAt.sum (u := Finset.range P) (fun k _ =>
      ((hasDerivAt_pow k 0).const_mul ((k.factorial : ℝ)⁻¹)).smul_const (v k))
    have hfe : (∑ k ∈ Finset.range P, (fun y : ℝ => ((k.factorial : ℝ)⁻¹ * y ^ k) • v k)) =
        fun x : ℝ => ∑ k ∈ Finset.range P, ((k.factorial : ℝ)⁻¹ * x ^ k) • v k := by
      ext x; rw [Finset.sum_apply]
    rwa [hfe] at hsum
  have key : deriv g 0 = ∑ i : Fin P, d i * T ((((i:ℕ)+1 : ℝ) * δ)) := by
    have h1 : deriv T 0 = Q.derivative.eval 0 := hTderiv.deriv.trans hQd.symm
    calc deriv g 0 = deriv T 0 := hTderiv.deriv.symm
      _ = Q.derivative.eval 0 := h1
      _ = ∑ i : Fin P, d i * Q.eval ((((i:ℕ)+1 : ℝ) * δ : ℝ) : ℂ) := hdid Q hQdeg
      _ = ∑ i : Fin P, d i * T ((((i:ℕ)+1 : ℝ) * δ)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hT]
  have hrem : ∀ i : Fin P, ‖g ((((i:ℕ)+1 : ℝ) * δ)) - T ((((i:ℕ)+1 : ℝ) * δ))‖ ≤
      A * (P*δ)^P := by
    intro i
    have hi : (((i:ℕ)+1 : ℝ)) ≤ P := by
      have := i.isLt; exact_mod_cast Nat.succ_le_of_lt this
    have hx0 : 0 ≤ (((i:ℕ)+1 : ℝ) * δ) := by positivity
    have hxmem : (((i:ℕ)+1 : ℝ) * δ) ∈ Set.Icc 0 (P*δ) :=
      ⟨hx0, mul_le_mul_of_nonneg_right hi hδ.le⟩
    have hbnd : ∀ t ∈ Set.Icc 0 (P*δ), ‖iteratedDeriv ((P-1)+1) g t‖ ≤ A := by
      intro t ht
      rw [Nat.sub_add_cancel hP1]
      exact hgd t ht
    have hTay := taylor_remainder_bound_iteratedDeriv g (P-1) hA
      (hg.of_le (le_of_eq (enat_cast_pred_add_one P hP1))) hbnd
    have h1 := hTay _ hxmem
    rw [Nat.sub_add_cancel hP1] at h1
    rw [← hTeq] at h1
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hx0 (mul_le_mul_of_nonneg_right hi hδ.le) P) hA
  calc ‖deriv g 0‖ = ‖∑ i : Fin P, d i * T ((((i:ℕ)+1 : ℝ) * δ))‖ := by rw [key]
    _ ≤ ∑ i : Fin P, ‖d i * T ((((i:ℕ)+1 : ℝ) * δ))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin P, ((P:ℝ)^P/δ) * (B + A*(P*δ)^P) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul]
        refine mul_le_mul (hdbd i) ?_ (norm_nonneg _) (by positivity)
        calc ‖T ((((i:ℕ)+1 : ℝ) * δ))‖
            = ‖g ((((i:ℕ)+1 : ℝ) * δ)) -
                (g ((((i:ℕ)+1 : ℝ) * δ)) - T ((((i:ℕ)+1 : ℝ) * δ)))‖ := by ring_nf
          _ ≤ ‖g ((((i:ℕ)+1 : ℝ) * δ))‖ +
                ‖g ((((i:ℕ)+1 : ℝ) * δ)) - T ((((i:ℕ)+1 : ℝ) * δ))‖ := norm_sub_le _ _
          _ ≤ B + A*(P*δ)^P := add_le_add (hgv i) (hrem i)
    _ = (P:ℝ) * (((P:ℝ)^P/δ) * (B + A*(P*δ)^P)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ((P:ℝ)^(2*P+1) + 1) * (B/δ + A*δ^(P-1)) := by
        have hδne : δ ≠ 0 := ne_of_gt hδ
        have hKeq : (P:ℝ) * (((P:ℝ)^P/δ) * (B + A*(P*δ)^P)) =
            (P:ℝ)^(P+1) * (B/δ) + (P:ℝ)^(2*P+1) * (A * δ^(P-1)) := by
          have hδP : δ^P = δ * δ^(P-1) := by
            rw [← pow_succ', Nat.sub_add_cancel hP1]
          rw [mul_pow, hδP]
          field_simp
          ring
        rw [hKeq]
        have hBδ : 0 ≤ B/δ := div_nonneg hB hδ.le
        have hAd : 0 ≤ A * δ^(P-1) := mul_nonneg hA (pow_nonneg hδ.le _)
        have hK1 : (P:ℝ)^(P+1) ≤ (P:ℝ)^(2*P+1) + 1 := by
          have hle : (P:ℝ)^(P+1) ≤ (P:ℝ)^(2*P+1) :=
            pow_le_pow_right₀ (show (1:ℝ) ≤ (P:ℝ) by exact_mod_cast hP1) (by omega)
          linarith
        have hK2 : (P:ℝ)^(2*P+1) ≤ (P:ℝ)^(2*P+1) + 1 := by linarith
        have h1 : (P:ℝ)^(P+1) * (B/δ) ≤ ((P:ℝ)^(2*P+1) + 1) * (B/δ) :=
          mul_le_mul_of_nonneg_right hK1 hBδ
        have h2 : (P:ℝ)^(2*P+1) * (A * δ^(P-1)) ≤
            ((P:ℝ)^(2*P+1) + 1) * (A * δ^(P-1)) :=
          mul_le_mul_of_nonneg_right hK2 hAd
        have hexp : ((P:ℝ)^(2*P+1) + 1) * (B/δ + A*δ^(P-1)) =
            ((P:ℝ)^(2*P+1) + 1) * (B/δ) + ((P:ℝ)^(2*P+1) + 1) * (A*δ^(P-1)) := by ring
        rw [hexp]
        exact add_le_add h1 h2

/-! ## The weight comparison at a point -/

/-- The value of a Schwartz function at `y` is controlled by the `(P,0)`-seminorm divided by
`‖y‖^P`. -/
private lemma norm_apply_le_seminorm_div {n : ℕ} [NeZero n]
    (g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (P : ℕ) {y : EuclideanSpace ℝ (Fin n)} {m : ℝ}
    (hm : 0 < m) (hy : m ≤ ‖y‖) :
    ‖g y‖ ≤ (SchwartzMap.seminorm ℂ P 0) g / m ^ P := by
  have hS : 0 ≤ (SchwartzMap.seminorm ℂ P 0) g := apply_nonneg _ _
  have hyP : 0 < ‖y‖^P := pow_pos (lt_of_lt_of_le hm hy) P
  calc ‖g y‖ = (‖y‖^P * ‖g y‖) / ‖y‖^P := (mul_div_cancel_left₀ (‖g y‖) hyP.ne').symm
    _ ≤ (SchwartzMap.seminorm ℂ P 0) g / ‖y‖^P :=
        div_le_div_of_nonneg_right (by
          simpa only [norm_iteratedFDeriv_zero] using SchwartzMap.le_seminorm ℂ P 0 g y) hyP.le
    _ ≤ (SchwartzMap.seminorm ℂ P 0) g / m ^ P :=
        div_le_div_of_nonneg_left hS (pow_pos hm P) (pow_le_pow_left₀ hm.le hy P)

/-- Pointwise estimate: for a unit direction `u` with `0 ≤ ⟪x,u⟫` (so that the nodes
`x + t u`, `t ≥ 0`, are at least as far from the origin as `x`), the weighted directional
derivative is controlled by the two seminorms. -/
private lemma directional_bound {n : ℕ} [NeZero n] (P : ℕ) (hP : 2 ≤ P) (K : ℝ) (hK0 : 0 ≤ K)
    (hcore : ∀ (f : ℝ → ℂ) (δ A B : ℝ), 0 < δ → 0 ≤ A → 0 ≤ B → ContDiff ℝ P f →
      (∀ t ∈ Set.Icc 0 (P*δ), ‖iteratedDeriv P f t‖ ≤ A) →
      (∀ i : Fin P, ‖f ((((i:ℕ)+1 : ℝ) * δ))‖ ≤ B) →
      ‖deriv f 0‖ ≤ K * (B / δ + A * δ ^ (P-1)))
    (g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (a : ℕ) (ha : a + 1 ≤ P)
    (x u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (hxu : 0 ≤ inner ℝ x u) :
    ‖x‖^a * ‖(fderiv ℝ (g : EuclideanSpace ℝ (Fin n) → ℂ) x) u‖ ≤
      K * ((SchwartzMap.seminorm ℂ 0 P) g + (SchwartzMap.seminorm ℂ P 0) g) := by
  have hP1 : 1 ≤ P := by omega
  set A := (SchwartzMap.seminorm ℂ 0 P) g with hAdef
  set B := (SchwartzMap.seminorm ℂ P 0) g with hBdef
  have hA0 : 0 ≤ A := apply_nonneg _ _
  have hB0 : 0 ≤ B := apply_nonneg _ _
  have hder : deriv (fun s : ℝ => (g : EuclideanSpace ℝ (Fin n) → ℂ) (x + s • u)) 0 =
      (fderiv ℝ (g : EuclideanSpace ℝ (Fin n) → ℂ) x) u := by
    have hc : HasDerivAt (fun s : ℝ => x + s • u) u 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const u).const_add x
    have h2 := (SchwartzMap.hasFDerivAt g (x + 0 • u)).comp_hasDerivAt (0:ℝ) hc
    rw [zero_smul, add_zero] at h2
    simpa [Function.comp_def] using h2.deriv
  have hderiv : ∀ δ : ℝ, ∀ t ∈ Set.Icc 0 (P*δ),
      ‖iteratedDeriv P (fun s : ℝ => g (x + s • u)) t‖ ≤ A := by
    intro δ t ht
    refine le_trans (norm_iteratedDeriv_affine_le (g : _ → ℂ) x u P t (g.smooth P)) ?_
    rw [hu, one_pow, mul_one]
    have h3 := SchwartzMap.le_seminorm ℂ 0 P g (x + t • u)
    simpa using h3
  have hcd : ContDiff ℝ P (fun s : ℝ => g (x + s • u)) := by
    have h4 : ContDiff ℝ P ((g : EuclideanSpace ℝ (Fin n) → ℂ) ∘ fun s : ℝ => x + s • u) :=
      (g.smooth P).comp (by fun_prop)
    simpa [Function.comp_def] using h4
  rcases le_or_gt 1 ‖x‖ with hx1 | hx1
  · set δ : ℝ := (‖x‖⁻¹) ^ (P - a) with hδdef
    have hxpos : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx1
    have hxne : (‖x‖:ℝ) ≠ 0 := ne_of_gt hxpos
    have hδpos : 0 < δ := by rw [hδdef]; positivity
    have hnode : ∀ t : ℝ, 0 ≤ t → ‖x‖ ≤ ‖x + t • u‖ := by
      intro t ht
      have h2 : ‖x‖^2 ≤ ‖x + t • u‖^2 := by
        rw [norm_add_sq_real, real_inner_smul_right, norm_smul, hu, mul_one]
        nlinarith [hxu, ht, mul_nonneg ht hxu, sq_nonneg ‖t‖]
      nlinarith [norm_nonneg x, norm_nonneg (x + t • u)]
    have hval : ∀ i : Fin P,
        ‖(fun s : ℝ => g (x + s • u)) ((((i:ℕ)+1:ℝ)*δ))‖ ≤ B / ‖x‖^P :=
      fun i => norm_apply_le_seminorm_div g P hxpos (hnode _ (by positivity))
    have hb := hcore _ δ A (B / ‖x‖^P) hδpos hA0 (div_nonneg hB0 (pow_pos hxpos P).le)
      hcd (hderiv δ) hval
    have hdead : ‖x‖^a * ((B / ‖x‖^P) / δ) ≤ B := by
      have h1 : ‖x‖^a * ‖x‖^(P-a) = ‖x‖^P := by
        rw [← pow_add, Nat.add_sub_of_le (by omega : a ≤ P)]
      rw [hδdef, inv_pow, div_inv_eq_mul]
      have heq : ‖x‖^a * (B / ‖x‖^P * ‖x‖^(P-a)) = B := by
        rw [show ‖x‖^a * (B / ‖x‖^P * ‖x‖^(P-a))
              = (‖x‖^a * ‖x‖^(P-a)) * (B / ‖x‖^P) by ring, h1,
            mul_div_cancel₀ B (pow_ne_zero P hxne)]
      exact le_of_eq heq
    have hdlt : ‖x‖^a * (A * δ^(P-1)) ≤ A := by
      have hka : a ≤ (P - a) * (P - 1) := by
        have ha1 : a ≤ P - 1 := by omega
        have hPma : 1 ≤ P - a := by omega
        calc a ≤ P - 1 := ha1
          _ = 1 * (P-1) := (one_mul _).symm
          _ ≤ (P - a) * (P - 1) := Nat.mul_le_mul_right _ hPma
      have h1 : ‖x‖^a ≤ ‖x‖^((P-a)*(P-1)) := pow_le_pow_right₀ hx1 hka
      rw [hδdef, inv_pow, inv_pow, ← pow_mul]
      have h2 : ‖x‖^a * (‖x‖ ^ ((P - a) * (P - 1)))⁻¹ ≤ 1 := by
        rw [mul_inv_le_iff₀ (pow_pos hxpos _)]
        simpa using h1
      calc ‖x‖^a * (A * (‖x‖ ^ ((P - a) * (P - 1)))⁻¹)
          = A * (‖x‖^a * (‖x‖ ^ ((P - a) * (P - 1)))⁻¹) := by ring
        _ ≤ A * 1 := mul_le_mul_of_nonneg_left h2 hA0
        _ = A := mul_one A
    calc ‖x‖^a * ‖(fderiv ℝ (g : EuclideanSpace ℝ (Fin n) → ℂ) x) u‖
        = ‖x‖^a * ‖deriv (fun s : ℝ => g (x + s • u)) 0‖ := by rw [hder]
      _ ≤ ‖x‖^a * (K * ((B / ‖x‖^P) / δ + A * δ^(P-1))) := by gcongr
      _ = K * (‖x‖^a * ((B / ‖x‖^P) / δ) + ‖x‖^a * (A * δ^(P-1))) := by ring
      _ ≤ K * (B + A) := by
          refine mul_le_mul_of_nonneg_left ?_ hK0
          exact add_le_add hdead hdlt
      _ = K * (A + B) := by ring
  · have hxle : ‖x‖ ≤ 1 := le_of_lt hx1
    have hnode : ∀ t : ℝ, 1 ≤ t → 1 ≤ ‖x + t • u‖ := by
      intro t ht
      have h2 : (1:ℝ) ≤ ‖x + t • u‖^2 := by
        rw [norm_add_sq_real, real_inner_smul_right, norm_smul, hu, mul_one]
        have ht1 : (1:ℝ) ≤ ‖t‖ := by
          rw [Real.norm_of_nonneg (le_trans zero_le_one ht)]
          exact ht
        nlinarith [hxu, ht1, mul_nonneg (le_trans zero_le_one ht) hxu, sq_nonneg ‖x‖]
      nlinarith [norm_nonneg (x + t • u)]
    have hval : ∀ i : Fin P, ‖(fun s : ℝ => g (x + s • u)) ((((i:ℕ)+1:ℝ)*1))‖ ≤ B / 1^P :=
      fun i => norm_apply_le_seminorm_div g P one_pos
        (hnode _ (by
          have h : (1:ℕ) ≤ (i:ℕ) + 1 := Nat.succ_le_succ (Nat.zero_le _)
          have h2 : (1:ℝ) ≤ ((i:ℕ):ℝ) + 1 := by exact_mod_cast h
          simpa using h2))
    have hb := hcore _ 1 A (B / 1^P) one_pos hA0 (div_nonneg hB0 (pow_nonneg zero_le_one P))
      hcd (hderiv 1) hval
    have ha1 : ‖x‖^a ≤ 1 := pow_le_one₀ (norm_nonneg x) hxle
    calc ‖x‖^a * ‖(fderiv ℝ (g : EuclideanSpace ℝ (Fin n) → ℂ) x) u‖
        = ‖x‖^a * ‖deriv (fun s : ℝ => g (x + s • u)) 0‖ := by rw [hder]
      _ ≤ ‖x‖^a * (K * ((B / 1^P) / 1 + A * 1^(P-1))) := by gcongr
      _ ≤ K * (A + B) := by
          have h1 : (B / 1^P) / 1 = B := by ring
          have h2 : (1:ℝ)^(P-1) = 1 := one_pow _
          rw [h1, h2]
          calc ‖x‖^a * (K * (B + A * 1))
              = ‖x‖^a * (K * (B + A)) := by ring
            _ ≤ 1 * (K * (B + A)) :=
                mul_le_mul_of_nonneg_right ha1 (by positivity)
            _ = K * (A + B) := by ring

theorem SeminormCompareB1 {n : ℕ} [NeZero n] (P : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (a : ℕ), a + 1 ≤ P →
      (SchwartzMap.seminorm ℂ a 1) g ≤
        C * ((SchwartzMap.seminorm ℂ P 0) g + (SchwartzMap.seminorm ℂ 0 P) g) := by
  rcases Nat.lt_or_ge P 2 with hPlt | hPge
  · have hcases : P = 0 ∨ P = 1 := by omega
    rcases hcases with rfl | rfl
    · exact ⟨0, le_rfl, fun g a ha => by omega⟩
    · refine ⟨1, zero_le_one, fun g a ha => ?_⟩
      have ha0 : a = 0 := by omega
      subst ha0
      have h1 : (0:ℝ) ≤ (SchwartzMap.seminorm ℂ 1 0) g := apply_nonneg _ _
      have h2 : (0:ℝ) ≤ (SchwartzMap.seminorm ℂ 0 1) g := apply_nonneg _ _
      nlinarith
  · obtain ⟨K, hK0, hcore⟩ := finite_difference_core P hPge
    refine ⟨K + 1, by positivity, fun g a ha => ?_⟩
    refine SchwartzMap.seminorm_le_bound ℂ a 1 g (by positivity) fun x => ?_
    have hL : ‖iteratedFDeriv ℝ 1 (fun y : EuclideanSpace ℝ (Fin n) => g y) x‖ =
        ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => g y) x‖ := by
      simpa using (norm_iteratedFDeriv_fderiv (𝕜 := ℝ)
        (f := fun y : EuclideanSpace ℝ (Fin n) => (g y : ℂ)) (x := x) (n := 0))
    rw [hL]
    have hop : ‖(‖x‖^a) • (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => g y) x)‖ ≤
        (K + 1) * ((SchwartzMap.seminorm ℂ 0 P) g + (SchwartzMap.seminorm ℂ P 0) g) := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
      rcases eq_or_ne v 0 with rfl | hv
      · simp
      · have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
        have h2 : ‖(((‖x‖^a) • (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => g y) x)) v)‖ =
            ‖v‖ * (‖x‖^a * ‖(fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => g y) x)
              (‖v‖⁻¹ • v)‖) := by
          rw [smul_apply, norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) a)]
          have hvv : v = ‖v‖ • (‖v‖⁻¹ • v) := by
            rw [smul_smul, mul_inv_cancel₀ hvn, one_smul]
          conv_lhs => rw [hvv]
          rw [map_smul, norm_smul, Real.norm_of_nonneg (norm_nonneg v)]
          ring
        rw [h2]
        have hu : ‖‖v‖⁻¹ • v‖ = 1 := norm_smul_inv_norm hv
        have hdir : ‖x‖^a * ‖(fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => g y) x)
            (‖v‖⁻¹ • v)‖ ≤ K * ((SchwartzMap.seminorm ℂ 0 P) g +
              (SchwartzMap.seminorm ℂ P 0) g) := by
          rcases le_total 0 (inner ℝ x (‖v‖⁻¹ • v)) with hxu | hxu
          · exact directional_bound P hPge K hK0 hcore g a ha x _ hu hxu
          · have h := directional_bound P hPge K hK0 hcore g a ha x (-(‖v‖⁻¹ • v))
              (by simpa using hu) (by rw [inner_neg_right]; exact neg_nonneg.mpr hxu)
            rwa [map_neg, norm_neg] at h
        calc ‖v‖ * (‖x‖^a * ‖(fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => g y) x)
              (‖v‖⁻¹ • v)‖)
            ≤ ‖v‖ * (K * ((SchwartzMap.seminorm ℂ 0 P) g +
                (SchwartzMap.seminorm ℂ P 0) g)) :=
              mul_le_mul_of_nonneg_left hdir (norm_nonneg v)
          _ ≤ ‖v‖ * ((K + 1) * ((SchwartzMap.seminorm ℂ 0 P) g +
                (SchwartzMap.seminorm ℂ P 0) g)) := by
              gcongr; linarith
          _ = (K + 1) * ((SchwartzMap.seminorm ℂ 0 P) g + (SchwartzMap.seminorm ℂ P 0) g) *
                ‖v‖ := by ring
    calc ‖x‖^a * ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => g y) x‖
        = ‖(‖x‖^a) • (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => g y) x)‖ := by
          rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) a)]
      _ ≤ (K + 1) * ((SchwartzMap.seminorm ℂ 0 P) g + (SchwartzMap.seminorm ℂ P 0) g) := hop
      _ = (K + 1) * ((SchwartzMap.seminorm ℂ P 0) g + (SchwartzMap.seminorm ℂ 0 P) g) := by
          ring

end

end Work.FunctionalEquations
