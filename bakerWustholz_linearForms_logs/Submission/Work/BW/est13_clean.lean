import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.split_aux
import Submission.Work.BW.est_Pi
import Submission.Work.BW.norm_Delta_le
import Submission.Work.BW.Theta_eq_taylor_coeff
import Submission.Work.BW.ulcm_le_four_pow
import Submission.Work.BW.ulcm_le_three_pow
import Submission.Work.BW.syl_log_facts
import Submission.Work.BW.acH_lower
import Submission.Work.BW.num_13
import Submission.Work.BW.num_T
import Submission.Work.BW.sigma_ge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# BW (13) at descent level `J`

BW, Crelle 442 (1993), p. 43, equation (13); the level-`J` form is used on pp. 57–58.

`log|f^{(J)}(z)| ≤ ln(p) + hT* + 0·204(1/d)SD + 1·008·2^{-J}|z|D` for `t₀+⋯ ≤ T* ≤ T`.

We unfold `acf` into its sum over `AuxIdx` and bound each summand by

`‖φ (p λ)‖ · ‖∏_m Δ(γ_{ι m}(λ); t_m)‖ · u(h)^{t₀} · ‖Θ(2^{-J}z + λ_{-1}; h, λ₀+1, t₀)‖ · ‖∏_j e^{z M_j λ_j/2^J}‖`

via `est_Pi` (the `Δ`-product), `est_Theta_yu` (the `Θ`), `ulcm_le_three_pow` (the `u(h)^{t₀}`), the
§14 estimate `|∑ λ_j M_j| ≤ 1·001 D/2^J` (proved here from `BH` and (10)), and `num_13` for the
numerical bookkeeping (in particular the maximisation with `μ = 57rd`).
-/

namespace Work.BW

open MvPolynomial

/-! ### Evaluation of the descended summand -/

/-- Evaluating `aeval (C a * X₀ + C b) q` at the point `ptC ℓ z` gives `aeval (a*z+b) q`. -/
lemma eval_aeval_scaled {r : ℕ} (ℓ : Fin r → ℂ) (z a b : ℂ) (q : Polynomial ℚ) :
    MvPolynomial.eval (ptC ℓ z)
        (Polynomial.aeval (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b) q)
      = Polynomial.aeval (a * z + b) q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, map_mul, map_pow, map_add,
      MvPolynomial.algebraMap_apply, MvPolynomial.eval_C,
      MvPolynomial.eval_X, ptC, Fin.cons_zero]

/-- Evaluating `∏_j X_{j+1}^{λ_j}` at the point `ptC ℓ z` gives `∏_j (e^{zℓ_j})^{λ_j}`. -/
lemma eval_prod_X_succ_ptC {r : ℕ} (ℓ : Fin r → ℂ) (z : ℂ) (lam : Fin r → ℕ) :
    MvPolynomial.eval (ptC ℓ z) (∏ j : Fin r, MvPolynomial.X j.succ ^ lam j)
      = ∏ j, (Complex.exp (z * ℓ j)) ^ lam j := by
  rw [MvPolynomial.eval_prod]
  exact Finset.prod_congr rfl (fun j _ => by
    rw [MvPolynomial.eval_pow, MvPolynomial.eval_X]; rfl)

/-- The value of the `Qdesc` summand at `ptC ℓ z`. -/
lemma eval_Qdesc_summand {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (b : Fin n → ℤ)
    (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ)
    (p : AuxIdx r h D0 Dj → K) (J : ℕ) (μ : Fin r → ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (ℓ : Fin r → ℂ) (z : ℂ) (lm : AuxIdx r h D0 Dj) :
    MvPolynomial.eval (ptC ℓ z)
        (if (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j) then
      MvPolynomial.C (φ (p lm) *
          (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)) * (ulcm h : ℂ) ^ t0)
        * Polynomial.aeval
            (MvPolynomial.C (((2 : ℂ) ^ J)⁻¹) * MvPolynomial.X 0 + MvPolynomial.C ((lm.1 : ℕ) : ℂ))
            (Polynomial.hasseDeriv t0 (deltaPoly h ^ ((lm.2.1 : ℕ) + 1)))
        * ∏ j : Fin r, MvPolynomial.X j.succ ^ ((lm.2.2 j : ℕ) / 2 ^ J) else 0) =
      (if (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j) then
      φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)) * (ulcm h : ℂ) ^ t0
        * Theta (((2 : ℂ) ^ J)⁻¹ * z + ((lm.1 : ℕ) : ℂ)) h ((lm.2.1 : ℕ) + 1) t0
        * ∏ j : Fin r, (Complex.exp (z * ℓ j)) ^ ((lm.2.2 j : ℕ) / 2 ^ J) else 0) := by
  by_cases hc : (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j)
  · rw [if_pos hc, if_pos hc]
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C, eval_aeval_scaled, eval_prod_X_succ_ptC,
      Theta]
  · rw [if_neg hc, if_neg hc, map_zero]


/-! ### The Cauchy bound for `Θ`

BW's (13) needs `‖Θ(2^{-J}z + λ_{-1}; h, λ₀+1, t₀)‖ ≤ (e(2 + |z|/(2^J h)))^{h(λ₀+1)}` (p. 43:
`|Θ(z;t)| ≤ …(e(2+|z|/h))^{h(D₀+1)}`).  We obtain the base `2 + |z|/k` from Cauchy's estimate at
radius `1` (whence `|w| ≤ |z| + 1` on the circle) and `norm_Delta_le`. -/

/-- The `m`-th analytic derivative of the polynomial function of `P` is the formal `m`-th
derivative of `P`, evaluated at the point. -/
private lemma iteratedDeriv_poly_eval (P : Polynomial ℂ) (m : ℕ) :
    iteratedDeriv m (fun w => P.eval w) = fun w => (Polynomial.derivative^[m] P).eval w := by
  induction m with
  | zero => ext w; simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    ext w
    simp

/-- **Cauchy's estimate at radius `1`.** Every Taylor coefficient of `P` at `z` is bounded by `C`,
provided `‖P‖ ≤ C` on the circle `‖w - z‖ = 1`. In particular the bound is uniform in `m`. -/
private lemma norm_taylor_coeff_le (P : Polynomial ℂ) (m : ℕ) (z : ℂ) (C : ℝ)
    (hC : ∀ w ∈ Metric.sphere z 1, ‖P.eval w‖ ≤ C) :
    ‖(Polynomial.taylor z P).coeff m‖ ≤ C := by
  have hf : DiffContOnCl ℂ (fun w => P.eval w) (Metric.ball z 1) := P.differentiable.diffContOnCl
  have hcau := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (F := ℂ) m
    (by norm_num : (0:ℝ) < 1) hf hC
  have h3 : (Polynomial.derivative^[m] P).eval z
      = ((m.factorial : ℂ)) * (Polynomial.taylor z P).coeff m := by
    have h : (m.factorial • Polynomial.hasseDeriv m) P = Polynomial.derivative^[m] P :=
      congr_fun (Polynomial.factorial_smul_hasseDeriv (R := ℂ) m) P
    rw [← h, LinearMap.smul_apply, Polynomial.eval_smul, nsmul_eq_mul, ← Polynomial.taylor_coeff]
  have hkey : (m.factorial : ℝ) * ‖(Polynomial.taylor z P).coeff m‖ ≤ (m.factorial : ℝ) * C := by
    have h := hcau
    rw [show iteratedDeriv m (fun w => P.eval w) z = (Polynomial.derivative^[m] P).eval z from
      congr_fun (iteratedDeriv_poly_eval P m) z, h3, norm_mul, Complex.norm_natCast, one_pow,
      div_one] at h
    have hm1 : (1:ℝ) ≤ (m.factorial : ℝ) := by
      have := Nat.factorial_pos m
      exact_mod_cast this
    nlinarith [h, hm1]
  exact le_of_mul_le_mul_left hkey (by positivity : (0:ℝ) < (m.factorial : ℝ))

/-- `‖Θ(z;k,l,m)‖ ≤ (e(2 + |z|/k))^{kl}` for `k ≥ 1` (BW §12, p. 43). -/
theorem Theta_bound (z : ℂ) (k l m : ℕ) (hk : 1 ≤ k) :
    ‖Theta z k l m‖ ≤ (Real.exp 1 * (2 + ‖z‖ / (k : ℝ))) ^ (k * l) := by
  rw [Theta_eq_taylor_coeff z k l m]
  refine norm_taylor_coeff_le ((deltaPoly k ^ l).map (algebraMap ℚ ℂ)) m z _ ?_
  intro w hw
  have hw' : ‖w - z‖ = 1 := by
    have h := Metric.mem_sphere.mp hw
    rwa [dist_eq_norm] at h
  have h1 : ((deltaPoly k ^ l).map (algebraMap ℚ ℂ)).eval w = Delta w k ^ l := by
    rw [Polynomial.map_pow, Polynomial.eval_pow, Delta, Polynomial.aeval_def,
      Polynomial.eval₂_eq_eval_map]
  rw [h1]
  have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hkpos : (0:ℝ) < (k:ℝ) := lt_of_lt_of_le (by norm_num) hkR
  have hwz : ‖w‖ ≤ ‖z‖ + 1 := by
    calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ = ‖z‖ + 1 := by rw [hw']; ring
  have hbase : Real.exp 1 * (1 + ‖w‖ / (k:ℝ)) ≤ Real.exp 1 * (2 + ‖z‖ / (k:ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
    have h3 : ‖w‖ / (k:ℝ) ≤ (‖z‖ + 1) / (k:ℝ) := div_le_div_of_nonneg_right hwz hkpos.le
    have h4 : (‖z‖ + 1) / (k:ℝ) ≤ 1 + ‖z‖ / (k:ℝ) := by
      rw [add_div]
      have h5 : (1:ℝ) / (k:ℝ) ≤ 1 := by
        rw [div_le_one hkpos]; exact hkR
      linarith
    linarith
  calc ‖Delta w k ^ l‖ = ‖Delta w k‖ ^ l := norm_pow _ _
    _ ≤ ((Real.exp 1 * (1 + ‖w‖ / (k:ℝ))) ^ k) ^ l :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_Delta_le w k) l
    _ = (Real.exp 1 * (1 + ‖w‖ / (k:ℝ))) ^ (k * l) := by rw [pow_mul]
    _ ≤ (Real.exp 1 * (2 + ‖z‖ / (k:ℝ))) ^ (k * l) :=
        pow_le_pow_left₀ (by positivity) hbase (k * l)

/-- The correction between the `3/M` form of the `Θ`-term and the `2/M` form of `num_13`:
`h(D₀+1)/(57rd) ≤ 0·0005·SD/d`. -/
lemma est13_corr {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) :
    (h : ℝ) * ((pD0 r d σ : ℝ) + 1) / (57 * (r : ℝ) * (d : ℝ))
      ≤ 0.0005 * (1 / (d : ℝ)) * (pS r d h : ℝ) * pD r d σ := by
  have hDpos : 0 < pD r d σ := pD_pos hr hd σ hσ
  have hD1 : (1:ℝ) ≤ pD r d σ := pD_ge_one hr hd σ hσ
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hlog : (1:ℝ) ≤ Real.log (2 * r * d) := by linarith [log_2rd_ge hr hd]
  have hD0 : (pD0 r d σ : ℝ) ≤ (r:ℝ) * pD r d σ / (2 * Real.log (2*r*d)) := pD0_le hr hd σ hσ
  have hdec : (pD0 r d σ : ℝ) + 1 ≤ (r:ℝ) * pD r d σ / 2 + 1 := by
    have h : (r:ℝ) * pD r d σ / (2 * Real.log (2*r*d)) ≤ (r:ℝ) * pD r d σ / 2 := by
      apply div_le_div_of_nonneg_left (by positivity)
      · norm_num
      · nlinarith
    linarith
  have hrr : (4:ℝ) ≤ (r:ℝ)^r := by
    have h : (2:ℝ)^2 ≤ (2:ℝ)^r := pow_le_pow_right₀ (by norm_num) hr
    calc (4:ℝ) = (2:ℝ)^2 := by norm_num
      _ ≤ (2:ℝ)^r := h
      _ ≤ (r:ℝ)^r := pow_le_pow_left₀ (by norm_num) hr2 r
  have hDbig : (3:ℝ) ≤ pD r d σ := by
    have hDlow : 2 * (r:ℝ)^r * 32 ^ (r+1) * d * Real.log (2*r*d) ≤ pD r d σ :=
      pD_low hr hd σ hσ
    have hlog : (4:ℝ)/3 ≤ Real.log (2*r*d) := log_2rd_ge hr hd
    have h32 : (32768:ℝ) ≤ 32 ^ (r+1) := by
      have h3 : 3 ≤ r + 1 := by omega
      have hh : (32:ℝ)^3 ≤ (32:ℝ)^(r+1) := pow_le_pow_right₀ (by norm_num) h3
      norm_num at hh ⊢
      exact hh
    have hrr0 : (0:ℝ) ≤ (r:ℝ)^r := by positivity
    have h320 : (0:ℝ) ≤ 32^(r+1) := by positivity
    have hd0 : (0:ℝ) ≤ (d:ℝ) := by positivity
    have hl0 : (0:ℝ) ≤ Real.log (2*r*d) := le_of_lt (log_2rd_pos hr hd)
    have hA : (4:ℝ) * 32768 ≤ (r:ℝ)^r * 32^(r+1) := mul_le_mul hrr h32 (by norm_num) hrr0
    have hB : ((4:ℝ)*32768) * 1 ≤ ((r:ℝ)^r * 32^(r+1)) * d :=
      mul_le_mul hA hd1 (by norm_num) (by positivity)
    have hC : (((4:ℝ)*32768)*1) * (4/3) ≤ ((r:ℝ)^r * 32^(r+1) * d) * Real.log (2*r*d) :=
      mul_le_mul hB hlog (by norm_num) (by positivity)
    have hstep : (2:ℝ) * 4 * 32768 * 1 * (4/3) ≤ 2 * (r:ℝ)^r * 32 ^ (r+1) * d * Real.log (2*r*d) := by
      have h2 : (0:ℝ) ≤ (2:ℝ) := by norm_num
      calc (2:ℝ) * 4 * 32768 * 1 * (4/3) = 2 * (((4:ℝ)*32768)*1*(4/3)) := by ring
        _ ≤ 2 * ((r:ℝ)^r * 32^(r+1) * d * Real.log (2*r*d)) := by
            exact mul_le_mul_of_nonneg_left hC h2
        _ = 2 * (r:ℝ)^r * 32 ^ (r+1) * d * Real.log (2*r*d) := by ring
    linarith [hDlow, hstep]
  have hkey : (r:ℝ) * pD r d σ / 2 + 1 ≤ 0.456 * (r:ℝ)^2 * d * pD r d σ := by
    have h1 : (r:ℝ) * pD r d σ / 2 + 1 ≤ 0.912 * ((r:ℝ) * pD r d σ) := by
      nlinarith [hr2, hDbig, hDpos.le]
    have h2 : (0.912:ℝ) * ((r:ℝ) * pD r d σ) ≤ 0.456 * (r:ℝ)^2 * d * pD r d σ := by
      have hmul : (2:ℝ) ≤ (r:ℝ) * d := by nlinarith [hr2, hd1]
      nlinarith [hmul, hDpos.le, hr2]
    linarith [h1, h2]
  have hmain : (h : ℝ) * ((pD0 r d σ : ℝ) + 1) ≤ (h:ℝ) * (0.456 * (r:ℝ)^2 * d * pD r d σ) :=
    mul_le_mul_of_nonneg_left (le_trans hdec hkey) (by positivity)
  calc (h : ℝ) * ((pD0 r d σ : ℝ) + 1) / (57 * (r : ℝ) * (d : ℝ))
      ≤ (h:ℝ) * (0.456 * (r:ℝ)^2 * d * pD r d σ) / (57 * (r:ℝ) * (d:ℝ)) := by
        apply div_le_div_of_nonneg_right hmain (by positivity)
    _ = 0.0005 * (1 / (d:ℝ)) * (pS r d h : ℝ) * pD r d σ := by
        rw [pS]
        push_cast
        field_simp
        ring

/-! ### The §14 estimate `|∑ λ_j M_j| ≤ 1·001·2^{-J} D` -/

set_option maxHeartbeats 1000000 in
/-- **BW §14, p. 42** (uses (10)). For `λ_j·2^J ≤ D_j` the level-`J` exponent `∑_j λ_j M_j`
satisfies `|∑_j λ_j M_j| ≤ 1·001·D/2^J`. The `1` comes from
`|∑_j λ_j log α'_j| ≤ ∑_j λ_j d σ_j ≤ D/2^J` (via `hmod ≤ σ_j` and `λ_j ≤ ⌊D/(rdσ_j)⌋/2^J`), the
`0·001` from `‖Λ‖ ≤ e^{−9·2^r S D}` (hypothesis (10)) multiplied by `∑_j λ_j|L_{jk}|/|b_k| ≤ 2^vD/2^J`. -/
theorem ellM_sum_le {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (mu : Fin r → ℕ)
    (hmu : ∀ j, mu j * 2 ^ J ≤ pDj r (dK K) σ j) :
    ‖∑ j, (mu j : ℂ) * ellM φ α b k v L j‖ ≤ 1.001 * acD K σ / 2 ^ J := by
  have hr : 2 ≤ r := H.hr
  have hd : 1 ≤ dK K := by
    have hpos : 0 < dK K := by
      haveI : Nontrivial K := inferInstance
      exact Module.finrank_pos (R := ℚ) (M := K)
    omega
  have hdR : (0:ℝ) < (dK K : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hd)
  have hr0 : (0:ℝ) < (r:ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hr)
  have hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  have hDpos : 0 < acD K σ := pD_pos hr hd σ hσ
  have h2Jpos : (0:ℝ) < (2:ℝ) ^ J := by positivity
  obtain ⟨-, -, -, -, -, hmodle, hrow, -⟩ := H.hBH
  obtain ⟨-, -, -, -, hbk, -, -, -, -⟩ := H.hst
  -- `‖log α'_j‖ ≤ d σ_j`
  have hlamP (j : Fin r) : ‖lamP φ α v L j‖ ≤ (dK K : ℝ) * σ j := by
    have h1 : ‖lamP φ α v L j‖ / (dK K : ℝ) ≤ σ j :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (hmodle j))
    rw [div_le_iff₀ hdR] at h1
    linarith
  -- `|L_{jk}| ≤ 2^v σ_j d`
  have hmodnn (i : Fin n) : 0 ≤ BakerWustholz.modifiedHeight φ (α i) :=
    le_trans (le_of_lt (by positivity : (0:ℝ) < 1 / (dK K : ℝ)))
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have hσpos : ∀ j : Fin r, (0:ℝ) < σ j := fun j => lt_of_lt_of_le (by positivity) (hσ j)
  have hLk (j : Fin r) : |((L j k : ℤ) : ℝ)| ≤ (2:ℝ) ^ v * σ j * (dK K : ℝ) := by
    have h1 : |((L j k : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α k) ≤ (2:ℝ) ^ v * σ j := by
      have h2 := Finset.single_le_sum
        (s := Finset.univ)
        (f := fun i : Fin n => |((L j i : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α i))
        (fun i _ => mul_nonneg (abs_nonneg _) (hmodnn i)) (Finset.mem_univ k)
      have h3 := hrow j
      push_cast at h3
      linarith
    have h4 : (1:ℝ) / (dK K : ℝ) ≤ BakerWustholz.modifiedHeight φ (α k) := by
      rw [BakerWustholz.modifiedHeight]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    have h5 : |((L j k : ℤ) : ℝ)| * (1 / (dK K : ℝ)) ≤ (2:ℝ) ^ v * σ j :=
      le_trans (mul_le_mul_of_nonneg_left h4 (abs_nonneg _)) h1
    have h6 : |((L j k : ℤ) : ℝ)| * (1 / (dK K : ℝ)) * (dK K : ℝ)
        ≤ (2:ℝ) ^ v * σ j * (dK K : ℝ) :=
      mul_le_mul_of_nonneg_right h5 (le_of_lt hdR)
    rw [mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hdR), mul_one] at h6
    linarith [h6]
  -- `λ_j d σ_j ≤ D/(r 2^J)`
  have hstep (j : Fin r) : (mu j : ℝ) * ((dK K : ℝ) * σ j) ≤ acD K σ / (2 ^ J * (r : ℝ)) := by
    have hσj : 0 < σ j := lt_of_lt_of_le (by positivity) (hσ j)
    have hden : (0:ℝ) < (r:ℝ) * (dK K : ℝ) * σ j := by positivity
    have h1 : (mu j : ℝ) * 2 ^ J ≤ (pDj r (dK K) σ j : ℝ) := by exact_mod_cast hmu j
    have h2 : (mu j : ℝ) ≤ (pDj r (dK K) σ j : ℝ) / 2 ^ J := by
      rw [le_div_iff₀ h2Jpos]; linarith
    have h3 : (pDj r (dK K) σ j : ℝ) ≤ acD K σ / ((r:ℝ) * (dK K : ℝ) * σ j) :=
      pDj_le hr hd σ hσ j
    have h4 : (mu j : ℝ) ≤ acD K σ / ((r:ℝ) * (dK K : ℝ) * σ j) / 2 ^ J :=
      le_trans h2 (div_le_div_of_nonneg_right h3 h2Jpos.le)
    calc (mu j : ℝ) * ((dK K : ℝ) * σ j)
        ≤ (acD K σ / ((r:ℝ) * (dK K : ℝ) * σ j) / 2 ^ J) * ((dK K : ℝ) * σ j) :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = acD K σ / (2 ^ J * (r : ℝ)) := by
          rw [div_div]
          field_simp
  -- Part 1: the `log α'` contribution
  have hpart1 : ‖∑ j, (mu j : ℂ) * lamP φ α v L j‖ ≤ acD K σ / 2 ^ J := by
    have hsum : ∑ j, (mu j : ℝ) * ((dK K : ℝ) * σ j) ≤ acD K σ / 2 ^ J := by
      calc ∑ j, (mu j : ℝ) * ((dK K : ℝ) * σ j)
          ≤ ∑ _j : Fin r, acD K σ / (2 ^ J * (r:ℝ)) := Finset.sum_le_sum (fun j _ => hstep j)
        _ = acD K σ / 2 ^ J := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
    calc ‖∑ j, (mu j : ℂ) * lamP φ α v L j‖
        ≤ ∑ j, ‖(mu j : ℂ) * lamP φ α v L j‖ := norm_sum_le Finset.univ _
      _ = ∑ j, (mu j : ℝ) * ‖lamP φ α v L j‖ := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [norm_mul, Complex.norm_natCast]
      _ ≤ ∑ j, (mu j : ℝ) * ((dK K : ℝ) * σ j) :=
            Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hlamP j) (by positivity))
      _ ≤ acD K σ / 2 ^ J := hsum
  -- Part 2: the `Λ` contribution
  have hb1 : (1:ℝ) ≤ ‖(b k : ℂ)‖ := by
    rw [Complex.norm_intCast, ← Int.cast_one, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hbk
  have hP2 : ‖∑ j, (mu j : ℂ) * ((L j k : ℂ) / (b k : ℂ))‖ ≤ (2:ℝ) ^ v * acD K σ / 2 ^ J := by
    have h2v : (0:ℝ) < (2:ℝ) ^ v := by positivity
    have hsum : ∑ j, (mu j : ℝ) * ((2:ℝ) ^ v * σ j * (dK K : ℝ))
        ≤ (2:ℝ) ^ v * acD K σ / 2 ^ J := by
      have hstep2 : ∀ j : Fin r, (mu j : ℝ) * ((2:ℝ) ^ v * σ j * (dK K : ℝ))
          ≤ (2:ℝ) ^ v * (acD K σ / (2 ^ J * (r:ℝ))) := by
        intro j
        calc (mu j : ℝ) * ((2:ℝ) ^ v * σ j * (dK K : ℝ))
            = (2:ℝ) ^ v * ((mu j : ℝ) * ((dK K : ℝ) * σ j)) := by ring
          _ ≤ (2:ℝ) ^ v * (acD K σ / (2 ^ J * (r:ℝ))) :=
              mul_le_mul_of_nonneg_left (hstep j) h2v.le
      calc ∑ j, (mu j : ℝ) * ((2:ℝ) ^ v * σ j * (dK K : ℝ))
          ≤ ∑ _j : Fin r, (2:ℝ) ^ v * (acD K σ / (2 ^ J * (r:ℝ))) :=
            Finset.sum_le_sum (fun j _ => hstep2 j)
        _ = (2:ℝ) ^ v * acD K σ / 2 ^ J := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
    calc ‖∑ j, (mu j : ℂ) * ((L j k : ℂ) / (b k : ℂ))‖
        = ‖(∑ j, (mu j : ℂ) * (L j k : ℂ)) * ((b k : ℂ))⁻¹‖ := by
            congr 1
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [div_eq_mul_inv]; ring
      _ = ‖∑ j, (mu j : ℂ) * (L j k : ℂ)‖ / ‖(b k : ℂ)‖ := by
            rw [norm_mul, norm_inv, div_eq_mul_inv]
      _ ≤ (∑ j, (mu j : ℝ) * |((L j k : ℤ) : ℝ)|) / ‖(b k : ℂ)‖ := by
            apply div_le_div_of_nonneg_right _ (norm_nonneg _)
            calc ‖∑ j, (mu j : ℂ) * (L j k : ℂ)‖
                ≤ ∑ j, ‖(mu j : ℂ) * (L j k : ℂ)‖ := norm_sum_le Finset.univ _
              _ = ∑ j, (mu j : ℝ) * |((L j k : ℤ) : ℝ)| := by
                    refine Finset.sum_congr rfl fun j _ => ?_
                    rw [norm_mul, Complex.norm_natCast, Complex.norm_intCast]
      _ ≤ ∑ j, (mu j : ℝ) * ((2:ℝ) ^ v * σ j * (dK K : ℝ)) := by
            have hbpos : 0 < ‖(b k : ℂ)‖ := lt_of_lt_of_le (by norm_num) hb1
            rw [div_le_iff₀ hbpos]
            have h1 : (∑ j, (mu j : ℝ) * |((L j k : ℤ) : ℝ)|)
                ≤ ∑ j, (mu j : ℝ) * ((2:ℝ) ^ v * σ j * (dK K : ℝ)) :=
              Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hLk j) (by positivity))
            have h3 : (0:ℝ) ≤ ∑ j, (mu j : ℝ) * ((2:ℝ) ^ v * σ j * (dK K : ℝ)) :=
              Finset.sum_nonneg (fun j _ => by
                have := hσpos j
                positivity)
            nlinarith [h1, hb1, h3]
      _ ≤ (2:ℝ) ^ v * acD K σ / 2 ^ J := hsum
  -- `‖Λ‖ ≤ 0·001`
  have hSpos : 0 < acS K r b v := by
    have h1 : 0 < pS r (dK K) (acH K b v) := by
      rw [pS]
      have hh : 0 < acH K b v := by have := (acH_lower H).1; omega
      positivity
    exact_mod_cast h1
  have hbig : Real.log 1000 ≤ 9 * 2 ^ r * acS K r b v * acD K σ := by
    have h1 : Real.log 1000 ≤ 999 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 1000)
      linarith
    have hS1 : (32:ℝ) ≤ acS K r b v := by
      have h2 : (32:ℕ) ≤ pS r (dK K) (acH K b v) := by
        rw [pS]
        have h3 : 1 ≤ acH K b v := by have := (acH_lower H).1; omega
        calc (32:ℕ) = (16 * 2 * 1) * 1 := by norm_num
          _ ≤ ((16 * r) * (dK K)) * (acH K b v) :=
              Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl hr) hd) h3
      exact_mod_cast h2
    have hD1 : (1:ℝ) ≤ acD K σ := pD_ge_one hr hd σ hσ
    have h2r : (4:ℝ) ≤ 2 ^ r := by
      have h : (2:ℝ)^2 ≤ (2:ℝ)^r := pow_le_pow_right₀ (by norm_num) hr
      norm_num at h
      exact h
    have h4 : (4:ℝ) * 32 * 1 ≤ 2 ^ r * acS K r b v * acD K σ :=
      mul_le_mul (mul_le_mul h2r hS1 (by norm_num) (by positivity)) hD1 (by norm_num)
        (by positivity)
    have h5 : (999:ℝ) ≤ 9 * 4 * 32 * 1 := by norm_num
    have h6 : 9 * 4 * 32 * 1 ≤ 9 * (2 ^ r * acS K r b v * acD K σ) := by
      have := mul_le_mul_of_nonneg_left h4 (by norm_num : (0:ℝ) ≤ 9)
      linarith [this]
    linarith [h1, h5, h6]
  have hLam : ‖lam φ α b‖ ≤ 0.001 := by
    have hne : lam φ α b ≠ 0 := by
      intro h0
      have h10 := H.h10
      rw [h0, norm_zero, Real.log_zero] at h10
      have hpos' : 0 < 9 * 2 ^ r * acS K r b v * acD K σ := by positivity
      linarith
    have hpos : 0 < ‖lam φ α b‖ := norm_pos_iff.mpr hne
    have h1 : ‖lam φ α b‖ ≤ Real.exp (-(9 * 2 ^ r * acS K r b v * acD K σ)) := by
      rw [← Real.log_le_iff_le_exp hpos]; exact H.h10
    have h2 : Real.exp (-(9 * 2 ^ r * acS K r b v * acD K σ)) ≤ 0.001 := by
      rw [← Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 0.001)]
      rw [show (0.001:ℝ) = (1000:ℝ)⁻¹ by norm_num, Real.log_inv]
      linarith [hbig]
    linarith [h1, h2]
  have hpart2 : ‖(∑ j, (mu j : ℂ) * ((L j k : ℂ) / (b k : ℂ))) * (((2:ℂ) ^ v)⁻¹ * lam φ α b)‖
      ≤ 0.001 * acD K σ / 2 ^ J := by
    have hnorm2 : ‖(2 : ℂ)‖ = 2 := Complex.norm_natCast 2
    have h2v : (0:ℝ) < (2:ℝ) ^ v := by positivity
    have hfac : ‖(((2:ℂ) ^ v)⁻¹ * lam φ α b)‖ ≤ ((2:ℝ)^v)⁻¹ * 0.001 := by
      rw [norm_mul, norm_inv, norm_pow, hnorm2]
      exact mul_le_mul_of_nonneg_left hLam (by positivity)
    calc ‖(∑ j, (mu j : ℂ) * ((L j k : ℂ) / (b k : ℂ))) * (((2:ℂ) ^ v)⁻¹ * lam φ α b)‖
        = ‖∑ j, (mu j : ℂ) * ((L j k : ℂ) / (b k : ℂ))‖ * ‖(((2:ℂ) ^ v)⁻¹ * lam φ α b)‖ :=
          norm_mul _ _
      _ ≤ ((2:ℝ) ^ v * acD K σ / 2 ^ J) * (((2:ℝ) ^ v)⁻¹ * 0.001) :=
          mul_le_mul hP2 hfac (norm_nonneg _) (by positivity)
      _ = 0.001 * acD K σ / 2 ^ J := by field_simp
  -- assemble
  have hsplit : ∑ j, (mu j : ℂ) * ellM φ α b k v L j
      = (∑ j, (mu j : ℂ) * lamP φ α v L j)
        - (∑ j, (mu j : ℂ) * ((L j k : ℂ) / (b k : ℂ))) * (((2:ℂ) ^ v)⁻¹ * lam φ α b) := by
    have h1 : ∀ j : Fin r, (mu j : ℂ) * ellM φ α b k v L j
        = (mu j : ℂ) * lamP φ α v L j
          - ((mu j : ℂ) * ((L j k : ℂ) / (b k : ℂ))) * (((2:ℂ) ^ v)⁻¹ * lam φ α b) := by
      intro j; rw [ellM]; ring
    rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_sub_distrib, Finset.sum_mul]
  rw [hsplit]
  calc ‖(∑ j, (mu j : ℂ) * lamP φ α v L j)
          - (∑ j, (mu j : ℂ) * ((L j k : ℂ) / (b k : ℂ))) * (((2:ℂ) ^ v)⁻¹ * lam φ α b)‖
      ≤ ‖∑ j, (mu j : ℂ) * lamP φ α v L j‖
        + ‖(∑ j, (mu j : ℂ) * ((L j k : ℂ) / (b k : ℂ))) * (((2:ℂ) ^ v)⁻¹ * lam φ α b)‖ :=
          norm_sub_le _ _
    _ ≤ acD K σ / 2 ^ J + 0.001 * acD K σ / 2 ^ J := add_le_add hpart1 hpart2
    _ = 1.001 * acD K σ / 2 ^ J := by ring

set_option maxHeartbeats 2000000

/-! ### Hanson's bound `log (ulcm k) ≤ 1.1 k`

The numerical input BW (13) needs for the `u(h)^{t₀}` factor of `Qdesc`.  It is proved here from
the sibling `syl_divisibility` (`ulcm k · ∏_{i≤k} ⌊k/sᵢ⌋! ∣ k!`) and the multinomial estimate
below, so that this file does not depend on the still incomplete `ulcm_le_three_pow`. -/

private lemma syl_pos' (i : ℕ) : 0 < syl i := by
  have := syl_two_le i; omega

/-- `2 * syl j ≤ syl (j+1)` for `j ≥ 1`, hence `2 ^ i ≤ syl i`. -/
private lemma two_mul_syl_le (j : ℕ) (hj : 1 ≤ j) : 2 * syl j ≤ syl (j + 1) := by
  have h3 : 3 ≤ syl j := by
    have h := syl_mono hj
    have h1 : syl 1 = 3 := by decide
    omega
  obtain ⟨m, hm⟩ : ∃ m, syl j = m + 3 := ⟨syl j - 3, by omega⟩
  rw [syl_succ, hm]
  have h1 : m + 3 - 1 = m + 2 := by omega
  rw [h1]
  nlinarith [Nat.zero_le m]

private lemma two_pow_le_syl_c (i : ℕ) : 2 ^ i ≤ syl i := by
  rcases i with _ | k
  · simp [syl_zero]
  · have h : ∀ k, 3 * 2 ^ k ≤ syl (k + 1) := by
      intro k
      induction k with
      | zero => simpa using (by decide : (3:ℕ) ≤ syl 1)
      | succ k ih =>
        have h1 : 2 * syl (k + 1) ≤ syl ((k + 1) + 1) := two_mul_syl_le (k + 1) (by omega)
        calc 3 * 2 ^ (k + 1) = 2 * (3 * 2 ^ k) := by rw [pow_succ]; ring
          _ ≤ 2 * syl (k + 1) := by linarith [ih]
          _ ≤ syl ((k + 1) + 1) := h1
    have hk := h k
    have h2 : 2 ^ (k + 1) ≤ 3 * 2 ^ k := by
      calc 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
        _ ≤ 3 * 2 ^ k := Nat.mul_le_mul_right _ (by norm_num : 2 ≤ 3)
    exact le_trans h2 hk

/-- The Egyptian-fraction identity for `syl`, over `ℝ`. -/
private lemma syl_sum_inv_real (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 : ℝ) / (syl i : ℝ)) = 1 - 1 / ((syl n : ℝ) - 1) := by
  induction n with
  | zero => norm_num [syl_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h2 : 2 ≤ syl n := syl_two_le n
    have hcast : ((syl (n + 1) : ℕ) : ℝ) - 1 = (syl n : ℝ) * ((syl n : ℝ) - 1) := by
      rw [syl_succ]
      push_cast [Nat.cast_sub (show 1 ≤ syl n by omega)]
      ring
    have hne : (syl n : ℝ) - 1 ≠ 0 := by
      have h3 : (2 : ℝ) ≤ (syl n : ℝ) := by exact_mod_cast h2
      intro h; linarith
    have hpos : (0 : ℝ) < (syl n : ℝ) := by
      have h3 : (2 : ℝ) ≤ (syl n : ℝ) := by exact_mod_cast h2
      linarith
    rw [hcast]
    field_simp
    ring

/-- `log 4096 ≤ 8.32`. -/
private lemma log4096_le' : Real.log (4096 : ℝ) ≤ 8.32 := by
  have h : (4096 : ℝ) = 2 ^ 12 := by norm_num
  rw [h, Real.log_pow]
  push_cast
  nlinarith [Real.log_two_lt_d9]

/-- Arithmetic for the range `4096 ≤ k < syl 5`: `6 log k + log (k+1) - 5 ≤ 0.0174 k`. -/
private lemma hanson_mid_arith (k : ℕ) (hk : 4096 ≤ k) :
    6 * Real.log (k : ℝ) + Real.log ((k : ℝ) + 1) - 5 ≤ 0.0174 * (k : ℝ) := by
  refine Nat.le_induction ?base ?step k hk
  case base =>
    have h1 : Real.log ((4096 : ℕ) : ℝ) ≤ 8.32 := log4096_le'
    have h2 : Real.log ((4096 : ℝ) + 1) ≤ 8.3203 := by
      have h3 : (4096 : ℝ) + 1 ≤ (4096 : ℝ) * (1 + 1 / 4096) := by norm_num
      have h4 : Real.log ((4096 : ℝ) + 1) ≤ Real.log ((4096 : ℝ) * (1 + 1 / 4096)) :=
        Real.log_le_log (by norm_num) h3
      rw [Real.log_mul (by norm_num) (by norm_num)] at h4
      have h5 : Real.log (4096 : ℝ) ≤ 8.32 := log4096_le'
      have h6 : Real.log (1 + 1 / 4096 : ℝ) ≤ 1 / 4096 := log_one_add_le _ (by norm_num)
      linarith
    norm_num
    linarith
  case step =>
    intro m hm ih
    push_cast at ih ⊢
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hb1 : Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) ≤ 1 / (m : ℝ) := by
      have h1 : Real.log ((m : ℝ) + 1) = Real.log (m : ℝ) + Real.log (1 + 1 / (m : ℝ)) := by
        rw [← Real.log_mul (ne_of_gt hm0) (by positivity)]
        congr 1
        field_simp
      have h2 : Real.log (1 + 1 / (m : ℝ)) ≤ 1 / (m : ℝ) := log_one_add_le _ (by positivity)
      linarith
    have hb2 : Real.log ((m : ℝ) + 1 + 1) - Real.log ((m : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      have h1 : Real.log ((m : ℝ) + 1 + 1)
          = Real.log ((m : ℝ) + 1) + Real.log (1 + 1 / ((m : ℝ) + 1)) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        field_simp
      have h2 : Real.log (1 + 1 / ((m : ℝ) + 1)) ≤ 1 / ((m : ℝ) + 1) :=
        log_one_add_le _ (by positivity)
      linarith
    have hle : (1 : ℝ) / (m : ℝ) ≤ 1 / 4096 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hm)
    have hle2 : (1 : ℝ) / ((m : ℝ) + 1) ≤ 1 / 4096 := by
      apply one_div_le_one_div_of_le (by norm_num)
      push_cast
      exact_mod_cast (by omega : 4096 ≤ m + 1)
    linarith [ih, hb1, hb2, hle, hle2]

/-- The active Sylvester indices `{i ≤ k : syl i ≤ k}` form an initial segment. -/
private lemma sylActRange (k : ℕ) :
    (Finset.range (k + 1)).filter (fun i => syl i ≤ k)
      = Finset.range (((Finset.range (k + 1)).filter (fun i => syl i ≤ k)).card) := by
  set I := (Finset.range (k + 1)).filter (fun i => syl i ≤ k) with hI
  have hmem : ∀ i, i ∈ I ↔ i ≤ k ∧ syl i ≤ k := by
    intro i
    rw [hI]
    simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  have hsub : I ⊆ Finset.range I.card := by
    intro i hi
    have hi' : i ≤ k ∧ syl i ≤ k := (hmem i).mp hi
    rw [Finset.mem_range]
    by_contra hcon
    push_neg at hcon
    have h1 : Finset.range (i + 1) ⊆ I := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [hmem]
      exact ⟨by omega, le_trans (syl_mono (by omega)) hi'.2⟩
    have h2 := Finset.card_le_card h1
    rw [Finset.card_range] at h2
    omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range])

/-- **Hanson's multinomial estimate.**  For `k ≥ 4096`,
`log (k! / ∏_{i≤k} ⌊k/sᵢ⌋!) ≤ 1.1 k`. -/
private theorem log_multinomial_bound (k : ℕ) (hk : 4096 ≤ k) :
    Real.log ((k.factorial : ℝ) / (sylBlocks k : ℝ)) ≤ 1.1 * (k : ℝ) := by
  classical
  set I : Finset ℕ := (Finset.range (k + 1)).filter (fun i => syl i ≤ k) with hIdef
  set n : ℕ := I.card with hndef
  have hIrange : I = Finset.range n := by
    have h : I = Finset.range I.card := by rw [hIdef]; exact sylActRange k
    rw [hndef]
    exact h
  have hIle : ∀ i ∈ I, syl i ≤ k := by
    intro i hi
    rw [hIdef] at hi
    exact (Finset.mem_filter.mp hi).2
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk3 : 3 ≤ k := by omega
  have hm1 : ∀ i ∈ I, 1 ≤ k / syl i := by
    intro i hi
    rw [Nat.le_div_iff_mul_le (syl_pos' i)]
    simpa using hIle i hi
  have hBne : (sylBlocks k : ℝ) ≠ 0 := by
    rw [sylBlocks, Nat.cast_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by positivity
  have hlogB : Real.log (sylBlocks k : ℝ)
      = ∑ i ∈ I, Real.log (((k / syl i).factorial : ℕ) : ℝ) := by
    rw [sylBlocks, Nat.cast_prod, Real.log_prod]
    · refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro x hx hxI
      have hxk : k < syl x := by
        by_contra hcon
        push_neg at hcon
        exact hxI (Finset.mem_filter.mpr ⟨hx, hcon⟩)
      rw [Nat.div_eq_of_lt hxk]
      simp
    · intro i hi
      exact_mod_cast Nat.factorial_ne_zero _
  have hterm : ∀ i ∈ I, ((k / syl i : ℕ) : ℝ) * Real.log ((k : ℝ) / (syl i : ℝ))
      - ((k / syl i : ℕ) : ℝ) ≤ Real.log (((k / syl i).factorial : ℕ) : ℝ) := by
    intro i hi
    set m : ℕ := k / syl i with hmdef
    have hs : 0 < syl i := syl_pos' i
    have hsi : (0 : ℝ) < (syl i : ℝ) := by exact_mod_cast hs
    have hm1' : 1 ≤ m := by rw [hmdef]; exact hm1 i hi
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hxpos : (0 : ℝ) < (k : ℝ) / (syl i : ℝ) := div_pos hk0 hsi
    have hxlt : (k : ℝ) / (syl i : ℝ) < (m : ℝ) + 1 := by
      rw [div_lt_iff₀ hsi]
      have h2 : k < (m + 1) * syl i := by
        rw [hmdef]
        exact (Nat.div_lt_iff_lt_mul hs).mp (Nat.lt_succ_self _)
      exact_mod_cast h2
    have hlogm : Real.log ((k : ℝ) / (syl i : ℝ)) - Real.log (m : ℝ) ≤ 1 / (m : ℝ) := by
      have h1 : Real.log ((k : ℝ) / (syl i : ℝ)) - Real.log (m : ℝ)
          = Real.log (((k : ℝ) / (syl i : ℝ)) / (m : ℝ)) :=
        (Real.log_div (ne_of_gt hxpos) (ne_of_gt hmpos)).symm
      rw [h1]
      have h2 : ((k : ℝ) / (syl i : ℝ)) / (m : ℝ) ≤ 1 + 1 / (m : ℝ) := by
        rw [div_le_iff₀ hmpos]
        have h3 : (1 + 1 / (m : ℝ)) * (m : ℝ) = (m : ℝ) + 1 := by field_simp
        rw [h3]
        linarith [hxlt]
      have h4 : Real.log (((k : ℝ) / (syl i : ℝ)) / (m : ℝ)) ≤ Real.log (1 + 1 / (m : ℝ)) :=
        Real.log_le_log (by positivity) h2
      have h5 : Real.log (1 + 1 / (m : ℝ)) ≤ 1 / (m : ℝ) := log_one_add_le _ (by positivity)
      linarith [h4, h5]
    have hmul : (m : ℝ) * (1 / (m : ℝ)) = 1 := by field_simp
    have h6 := mul_le_mul_of_nonneg_left hlogm (le_of_lt hmpos)
    have h7 := log_factorial_ge m hm1'
    rw [hmul] at h6
    linarith [h6, h7]
  set A : ℝ := ∑ i ∈ I, ((k / syl i : ℕ) : ℝ) with hAdef
  set T : ℝ := ∑ i ∈ I, ((k / syl i : ℕ) : ℝ) * Real.log (syl i : ℝ) with hTdef
  have hsumAT : ∑ i ∈ I, ((k / syl i : ℕ) : ℝ) * Real.log ((k : ℝ) / (syl i : ℝ))
      = A * Real.log (k : ℝ) - T := by
    have hstep : ∀ i ∈ I, ((k / syl i : ℕ) : ℝ) * Real.log ((k : ℝ) / (syl i : ℝ))
        = ((k / syl i : ℕ) : ℝ) * Real.log (k : ℝ)
          - ((k / syl i : ℕ) : ℝ) * Real.log (syl i : ℝ) := by
      intro i hi
      have hsi : (0 : ℝ) < (syl i : ℝ) := by have h := syl_pos' i; exact_mod_cast h
      rw [Real.log_div (ne_of_gt hk0) (ne_of_gt hsi), mul_sub]
    calc ∑ i ∈ I, ((k / syl i : ℕ) : ℝ) * Real.log ((k : ℝ) / (syl i : ℝ))
        = ∑ i ∈ I, (((k / syl i : ℕ) : ℝ) * Real.log (k : ℝ)
            - ((k / syl i : ℕ) : ℝ) * Real.log (syl i : ℝ)) := Finset.sum_congr rfl hstep
      _ = (∑ i ∈ I, ((k / syl i : ℕ) : ℝ) * Real.log (k : ℝ))
            - ∑ i ∈ I, ((k / syl i : ℕ) : ℝ) * Real.log (syl i : ℝ) := by
          rw [Finset.sum_sub_distrib]
      _ = (∑ i ∈ I, ((k / syl i : ℕ) : ℝ)) * Real.log (k : ℝ)
            - ∑ i ∈ I, ((k / syl i : ℕ) : ℝ) * Real.log (syl i : ℝ) := by rw [Finset.sum_mul]
      _ = A * Real.log (k : ℝ) - T := by rw [← hAdef, ← hTdef]
  have hsum_term : A * Real.log (k : ℝ) - T - A
      ≤ ∑ i ∈ I, Real.log (((k / syl i).factorial : ℕ) : ℝ) := by
    have h1 : ∑ i ∈ I, (((k / syl i : ℕ) : ℝ) * Real.log ((k : ℝ) / (syl i : ℝ))
        - ((k / syl i : ℕ) : ℝ)) = A * Real.log (k : ℝ) - T - A := by
      rw [Finset.sum_sub_distrib, hsumAT, ← hAdef]
    rw [← h1]
    exact Finset.sum_le_sum hterm
  have hlogk' : Real.log (k.factorial : ℝ)
      ≤ (k : ℝ) * Real.log (k : ℝ) - k + Real.log ((k : ℝ) + 1) + 1 :=
    log_factorial_le' k (by omega : 1 ≤ k)
  have hlogdiv : Real.log ((k.factorial : ℝ) / (sylBlocks k : ℝ))
      = Real.log (k.factorial : ℝ) - Real.log (sylBlocks k : ℝ) :=
    Real.log_div (by positivity) hBne
  have hentropy : Real.log ((k.factorial : ℝ) / (sylBlocks k : ℝ))
      ≤ ((k : ℝ) - A) * (Real.log (k : ℝ) - 1) + Real.log ((k : ℝ) + 1) + 1 + T := by
    have hraw : Real.log ((k.factorial : ℝ) / (sylBlocks k : ℝ))
        ≤ (k : ℝ) * Real.log (k : ℝ) - k + Real.log ((k : ℝ) + 1) + 1
          - A * Real.log (k : ℝ) + A + T := by
      linarith [hlogdiv, hlogB, hlogk', hsum_term]
    refine le_trans hraw (le_of_eq ?_)
    ring
  have hT_le : T ≤ (k : ℝ) * Lw k := by
    have hLw : Lw k = ∑ i ∈ I, Real.log (syl i : ℝ) / (syl i : ℝ) := by
      rw [Lw, hIdef]
    rw [hTdef, hLw, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hsi : (0 : ℝ) < (syl i : ℝ) := by have h := syl_pos' i; exact_mod_cast h
    have h1 : ((k / syl i : ℕ) : ℝ) ≤ (k : ℝ) / (syl i : ℝ) := Nat.cast_div_le
    have h2 : 0 ≤ Real.log (syl i : ℝ) := Real.log_nonneg (by
      have h := syl_two_le i
      exact_mod_cast (by omega : 1 ≤ syl i))
    calc ((k / syl i : ℕ) : ℝ) * Real.log (syl i : ℝ)
        ≤ ((k : ℝ) / (syl i : ℝ)) * Real.log (syl i : ℝ) := mul_le_mul_of_nonneg_right h1 h2
      _ = (k : ℝ) * (Real.log (syl i : ℝ) / (syl i : ℝ)) := by ring
  have hLw : Lw k ≤ 1.0826 := syl_log_facts.2.2.2 k
  have hT' : T ≤ 1.0826 * (k : ℝ) := by
    have h3 := mul_le_mul_of_nonneg_left hLw (le_of_lt hk0)
    linarith [hT_le, h3]
  have hn_lt : k < syl n := by
    have hnI : n ∉ I := by rw [hIrange]; simp
    by_cases hnk : n ≤ k
    · by_contra hcon
      push_neg at hcon
      exact hnI (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hcon⟩)
    · push_neg at hnk
      have h := syl_ge n
      omega
  have hA_le : (k : ℝ) - A ≤ 1 + (n : ℝ) := by
    have hsum_inv : ∑ i ∈ I, (1 : ℝ) / (syl i : ℝ) = 1 - 1 / ((syl n : ℝ) - 1) := by
      rw [hIrange]
      exact syl_sum_inv_real n
    have hX : ∑ i ∈ I, ((k : ℝ) / (syl i : ℝ)) = (k : ℝ) - (k : ℝ) / ((syl n : ℝ) - 1) := by
      have hA1 : ∑ i ∈ I, ((k : ℝ) / (syl i : ℝ))
          = (k : ℝ) * ∑ i ∈ I, (1 : ℝ) / (syl i : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i hi => by rw [div_eq_mul_one_div]
      rw [hA1, hsum_inv]
      ring
    have hdiv1 : ∀ i ∈ I, ((k : ℝ) / (syl i : ℝ)) - 1 ≤ ((k / syl i : ℕ) : ℝ) := by
      intro i hi
      have hs : 0 < syl i := syl_pos' i
      have hsi : (0 : ℝ) < (syl i : ℝ) := by exact_mod_cast hs
      have hmod : k % syl i < syl i := Nat.mod_lt k hs
      have hdecomp : (k : ℝ) = (syl i : ℝ) * ((k / syl i : ℕ) : ℝ) + ((k % syl i : ℕ) : ℝ) := by
        have h : syl i * (k / syl i) + k % syl i = k := Nat.div_add_mod k (syl i)
        have h' : (k : ℝ) = ((syl i * (k / syl i) + k % syl i : ℕ) : ℝ) := by rw [h]
        push_cast at h'
        exact h'
      have hlt : ((k % syl i : ℕ) : ℝ) < (syl i : ℝ) := by exact_mod_cast hmod
      have hmain : (k : ℝ) / (syl i : ℝ) ≤ ((k / syl i : ℕ) : ℝ) + 1 := by
        rw [div_le_iff₀ hsi]
        nlinarith [hdecomp, hlt]
      linarith [hmain]
    have hA_lower : (k : ℝ) - (k : ℝ) / ((syl n : ℝ) - 1) - (n : ℝ) ≤ A := by
      have h1 : (∑ i ∈ I, ((k : ℝ) / (syl i : ℝ) - 1)) ≤ A := by
        rw [hAdef]
        exact Finset.sum_le_sum hdiv1
      have h2 : (∑ i ∈ I, ((k : ℝ) / (syl i : ℝ) - 1))
          = (∑ i ∈ I, ((k : ℝ) / (syl i : ℝ))) - (n : ℝ) := by
        rw [Finset.sum_sub_distrib]
        congr 1
        rw [Finset.sum_const, hndef]
        simp
      rw [h2, hX] at h1
      linarith [h1]
    have hden : (k : ℝ) ≤ (syl n : ℝ) - 1 := by
      have h5 : (k : ℝ) + 1 ≤ (syl n : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ syl n)
      linarith
    have hdenpos : (0 : ℝ) < (syl n : ℝ) - 1 := by linarith
    have hkdiv : (k : ℝ) / ((syl n : ℝ) - 1) ≤ 1 := by
      rw [div_le_one hdenpos]
      exact hden
    linarith [hA_lower, hkdiv]
  have hlogk_ge : (1 : ℝ) ≤ Real.log (k : ℝ) := by
    have h1 : Real.log 3 ≤ Real.log (k : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hk3)
    have h2 : (1 : ℝ) ≤ Real.log 3 := by linarith [Real.log_three_gt_d9]
    linarith
  have hprod : ((k : ℝ) - A) * (Real.log (k : ℝ) - 1) ≤ (1 + (n : ℝ)) * (Real.log (k : ℝ) - 1) :=
    mul_le_mul_of_nonneg_right hA_le (by linarith)
  -- explicit bounds on `log k`
  have hlog2pos : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hL4 : Real.log (k : ℝ) ≤ 4 * (k : ℝ) ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div (x := (k : ℝ)) (ε := (1 / 4 : ℝ)) (le_of_lt hk0) (by norm_num)
    have h2 : (k : ℝ) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) = 4 * (k : ℝ) ^ (1 / 4 : ℝ) := by ring
    linarith [h, h2.le, h2.ge]
  have hfin : ((k : ℝ) - A) * (Real.log (k : ℝ) - 1) + Real.log ((k : ℝ) + 1) + 1 + T
      ≤ 1.1 * (k : ℝ) := by
    rcases lt_or_ge k 3263443 with hks | hks
    · -- `4096 ≤ k < syl 5`
      have hn5 : (n : ℝ) ≤ 5 := by
        have hI5 : I ⊆ Finset.range 5 := by
          intro i hi
          rw [Finset.mem_range]
          by_contra hcon
          push_neg at hcon
          have h1 : syl 5 ≤ syl i := syl_mono hcon
          have h2 : syl 5 = 3263443 := by norm_num [syl]
          have h3 := hIle i hi
          omega
        have h2 := Finset.card_le_card hI5
        rw [Finset.card_range] at h2
        have : n ≤ 5 := by simpa [hndef] using h2
        exact_mod_cast this
      have harith := hanson_mid_arith k hk
      have h4 : (1 + (n : ℝ)) * (Real.log (k : ℝ) - 1) ≤ 6 * Real.log (k : ℝ) - 6 := by
        have h5 : 1 + (n : ℝ) ≤ 6 := by linarith
        have h6 : 0 ≤ Real.log (k : ℝ) - 1 := by linarith
        have h7 := mul_le_mul_of_nonneg_right h5 h6
        linarith [h7]
      linarith [hprod, hT', h4, harith]
    · have hksR : (3263443 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hks
      have hn_bound : (n : ℝ) ≤ Real.log (k : ℝ) / Real.log 2 + 1 := by
        have hn1 : 1 ≤ n := by
          have h0 : 0 ∈ I := by
            rw [hIdef]
            exact Finset.mem_filter.mpr ⟨by simp, by simpa [syl_zero] using (by omega : 2 ≤ k)⟩
          exact Finset.card_pos.mpr ⟨0, h0⟩
        have hmem : n - 1 ∈ I := by
          rw [hIrange]
          exact Finset.mem_range.mpr (by omega)
        have hsyl : syl (n - 1) ≤ k := hIle _ hmem
        have hpow : 2 ^ (n - 1) ≤ syl (n - 1) := two_pow_le_syl_c _
        have hk2 : (2 : ℝ) ^ (n - 1) ≤ (k : ℝ) := by
          have h4 : (2 : ℕ) ^ (n - 1) ≤ k := le_trans hpow hsyl
          exact_mod_cast h4
        have h4 : Real.log ((2 : ℝ) ^ (n - 1)) ≤ Real.log (k : ℝ) :=
          Real.log_le_log (by positivity) hk2
        rw [Real.log_pow] at h4
        have h5 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          push_cast [Nat.cast_sub hn1]
          ring
        rw [h5] at h4
        have h6 : (n : ℝ) - 1 ≤ Real.log (k : ℝ) / Real.log 2 := by
          rw [le_div_iff₀ hlog2pos]
          linarith [h4]
        linarith [h6]
      rcases lt_or_ge k 5700000 with hkm | hkm
      · -- crude branch `3263443 ≤ k < 5700000`
        have hLm : Real.log (k : ℝ) ≤ 15.943 := by
          have h1 : Real.log (k : ℝ) ≤ Real.log ((2 : ℝ) ^ 23) := by
            apply Real.log_le_log hk0
            have h2 : ((5700000 : ℕ) : ℝ) ≤ (2 : ℝ) ^ 23 := by norm_num
            exact le_trans (by exact_mod_cast hkm.le) h2
          rw [Real.log_pow] at h1
          push_cast at h1
          nlinarith [Real.log_two_lt_d9]
        have hL1m : Real.log ((k : ℝ) + 1) ≤ 15.943 := by
          have h1 : Real.log ((k : ℝ) + 1) ≤ Real.log ((2 : ℝ) ^ 23) := by
            apply Real.log_le_log (by positivity)
            have h2 : ((5700000 : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ 23 := by norm_num
            have h3 : ((k : ℝ) + 1) ≤ ((5700000 : ℕ) : ℝ) + 1 := by
              have h4 : (k : ℝ) ≤ ((5700000 : ℕ) : ℝ) := by exact_mod_cast hkm.le
              linarith
            linarith
          rw [Real.log_pow] at h1
          push_cast at h1
          nlinarith [Real.log_two_lt_d9]
        have hlm : Real.log (k : ℝ) / Real.log 2 ≤ 23.01 := by
          rw [div_le_iff₀ hlog2pos]
          nlinarith [hLm, Real.log_two_gt_d9]
        have hn26 : (1 + (n : ℝ)) ≤ 26 := by linarith [hn_bound, hlm]
        have h4 : (1 + (n : ℝ)) * (Real.log (k : ℝ) - 1) ≤ 26 * (15.943 - 1) := by
          have h5 : Real.log (k : ℝ) - 1 ≤ 15.943 - 1 := by linarith [hLm]
          have h6 : 0 ≤ Real.log (k : ℝ) - 1 := by linarith [hlogk_ge]
          have h7 := mul_le_mul hn26 h5 h6 (by norm_num)
          linarith [h7]
        linarith [hprod, hT', h4, hL1m, hksR]
      · -- `k ≥ 5700000`
        have hkR : (5700000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkm
        have hsqrt : (2387 : ℝ) ≤ Real.sqrt (k : ℝ) := by
          rw [Real.le_sqrt (show (0:ℝ) ≤ 2387 by norm_num) (show (0:ℝ) ≤ (k:ℝ) by positivity)]
          exact_mod_cast (le_trans (by norm_num : (2387:ℕ) ^ 2 ≤ 5700000) hkm)
        have hsq : Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) = (k : ℝ) :=
          Real.mul_self_sqrt (le_of_lt hk0)
        have hsqrt_le : Real.sqrt (k : ℝ) ≤ (k : ℝ) / 2387 := by
          rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2387)]
          nlinarith [hsqrt, hsq]
        have hq_le : (k : ℝ) ^ (1 / 4 : ℝ) ≤ (k : ℝ) / 2387 := by
          have h1 : (k : ℝ) ^ (1 / 4 : ℝ) ≤ (k : ℝ) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ k)) (by norm_num)
          rw [← Real.sqrt_eq_rpow] at h1
          linarith [h1, hsqrt_le]
        have hqpos : (0 : ℝ) < (k : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hk0 _
        have hL1 : Real.log ((k : ℝ) + 1) ≤ 5 * (k : ℝ) ^ (1 / 4 : ℝ) := by
          have h1 : Real.log ((k : ℝ) + 1)
              = Real.log (k : ℝ) + Real.log (1 + 1 / (k : ℝ)) := by
            rw [← Real.log_mul (ne_of_gt hk0) (by positivity)]
            congr 1
            field_simp
          have h2 : Real.log (1 + 1 / (k : ℝ)) ≤ 1 / (k : ℝ) := log_one_add_le _ (by positivity)
          have h3 : 1 / (k : ℝ) ≤ 1 := by
            rw [div_le_one hk0]
            exact_mod_cast (by omega : 1 ≤ k)
          have h4 : (1 : ℝ) ≤ (k : ℝ) ^ (1 / 4 : ℝ) :=
            Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ k)) (by norm_num)
          linarith [h1.le, h1.ge, h2, h3, h4, hL4]
        have hmain : (1 + (n : ℝ)) * (Real.log (k : ℝ) - 1) + Real.log ((k : ℝ) + 1) + 1
            ≤ 0.0174 * (k : ℝ) := by
          have hinvlog2 : 1 / Real.log 2 ≤ 1.4427 := by
            rw [div_le_iff₀ hlog2pos]
            nlinarith [Real.log_two_gt_d9]
          have h1 : Real.log (k : ℝ) / Real.log 2 ≤ 1.4427 * Real.log (k : ℝ) := by
            have h2 : Real.log (k : ℝ) / Real.log 2 = Real.log (k : ℝ) * (1 / Real.log 2) :=
              div_eq_mul_one_div _ _
            rw [h2]
            have h8 : 0 ≤ Real.log (k : ℝ) := by linarith [hlogk_ge]
            nlinarith [hinvlog2, h8]
          have hn_le : (1 + (n : ℝ)) ≤ 5.771 * (k : ℝ) ^ (1 / 4 : ℝ) + 2 := by
            linarith [hn_bound, h1, hL4]
          have h7 : (1 + (n : ℝ)) * (Real.log (k : ℝ) - 1)
              ≤ 23.084 * Real.sqrt (k : ℝ) + 8 * (k : ℝ) ^ (1 / 4 : ℝ) := by
            have h2 : 0 ≤ Real.log (k : ℝ) - 1 := by linarith [hlogk_ge]
            have h3 : Real.log (k : ℝ) - 1 ≤ 4 * (k : ℝ) ^ (1 / 4 : ℝ) := by linarith [hL4]
            have h4 : 0 ≤ 5.771 * (k : ℝ) ^ (1 / 4 : ℝ) + 2 := by positivity
            have h5 := mul_le_mul hn_le h3 h2 h4
            have h6 : (5.771 * (k : ℝ) ^ (1 / 4 : ℝ) + 2) * (4 * (k : ℝ) ^ (1 / 4 : ℝ))
                = 23.084 * ((k : ℝ) ^ (1 / 4 : ℝ) * (k : ℝ) ^ (1 / 4 : ℝ))
                  + 8 * (k : ℝ) ^ (1 / 4 : ℝ) := by ring
            have h8 : (k : ℝ) ^ (1 / 4 : ℝ) * (k : ℝ) ^ (1 / 4 : ℝ) = Real.sqrt (k : ℝ) := by
              rw [← Real.rpow_add hk0, show (1:ℝ) / 4 + 1 / 4 = 1 / 2 by norm_num,
                ← Real.sqrt_eq_rpow]
            linarith [h5, h6.le, h6.ge, h8.le, h8.ge]
          have htot : 23.084 * Real.sqrt (k : ℝ) + 13 * (k : ℝ) ^ (1 / 4 : ℝ) + 1
              ≤ 0.0174 * (k : ℝ) := by
            have h8 : 23.084 * Real.sqrt (k : ℝ) ≤ 23.084 * ((k : ℝ) / 2387) := by linarith [hsqrt_le]
            have h9 : 13 * (k : ℝ) ^ (1 / 4 : ℝ) ≤ 13 * ((k : ℝ) / 2387) := by linarith [hq_le]
            linarith [h8, h9, hkR]
          linarith [h7, hL1, htot]
        linarith [hprod, hT', hmain]
  exact le_trans hentropy hfin

/-- **Hanson's bound** `log (ulcm k) ≤ 1.1 k`, the input BW (13) needs for `u(h)^{t₀}`. -/
theorem hanson_ulcm_log_le (k : ℕ) : Real.log (ulcm k) ≤ 1.1 * (k : ℝ) := by
  rcases lt_or_ge k 4096 with hk | hk
  · have hsmall := ulcm_le_three_pow_small k hk
    have h1 : (ulcm k : ℝ) ≤ (3 : ℝ) ^ k := by
      have h2 : ((ulcm k : ℕ) : ℝ) ≤ ((3 ^ k : ℕ) : ℝ) := by exact_mod_cast hsmall
      simpa using h2
    have hlog := Real.log_le_log (show (0 : ℝ) < (ulcm k : ℝ) by exact_mod_cast ulcm_pos k) h1
    rw [Real.log_pow] at hlog
    have h3 : Real.log 3 ≤ 1.0987 := syl_log_facts.2.1
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [hlog, h3]
  · have hMpos : 0 < sylBlocks k := Nat.pos_of_ne_zero (sylBlocks_ne_zero k)
    have hdvd := syl_divisibility k
    have hle : ulcm k ≤ k.factorial / sylBlocks k := by
      rw [Nat.le_div_iff_mul_le hMpos]
      exact Nat.le_of_dvd (Nat.factorial_pos k) hdvd
    have hdvd' : sylBlocks k ∣ k.factorial := (dvd_mul_left (sylBlocks k) (ulcm k)).trans hdvd
    have hcast : ((k.factorial / sylBlocks k : ℕ) : ℝ) = (k.factorial : ℝ) / (sylBlocks k : ℝ) :=
      Nat.cast_div hdvd' (by positivity)
    have hcastle : (ulcm k : ℝ) ≤ (k.factorial : ℝ) / (sylBlocks k : ℝ) := by
      rw [← hcast]
      exact_mod_cast hle
    have hlog1 : Real.log (ulcm k) ≤ Real.log ((k.factorial : ℝ) / (sylBlocks k : ℝ)) :=
      Real.log_le_log (by exact_mod_cast ulcm_pos k) hcastle
    exact le_trans hlog1 (log_multinomial_bound k hk)

/-! ### BW (13) -/

set_option maxHeartbeats 4000000 in
/-- BW (1993) §13–§14, p. 43 (the estimate (13)): for the level-`J` descended auxiliary polynomial
`Q^{(J)}` evaluated along `Y₀ = z`, `Y_j = e^{z M_j}` (`M = ellM`), i.e. `acf`,
`log‖acf φ α b k L ι v σ p J μ t0 t z‖ ≤ ln p + h·T* + 0.204·(1/d)·S·D + 1.008·2^{-J}‖z‖·D`
for `t₀ + ⋯ + t_{r−1} ≤ T* ≤ T`.  Identical statement to `Submission.Work.BW.est13`, restated so
that the module does **not** clash: `est13.lean` declares `two_pow_le_syl` (`Work.BW.two_pow_le_syl`)
while `log_ulcm_le.lean` — transitively imported by `est13` through `num_13` — declares the same name
publicly, and Lean rejects the duplicate fully-qualified name, so `est13.olean` never appears and
every module importing it fails (including the live `est21_l` assembly).  A port should copy
`est13.lean` verbatim, dropping (or renaming) its `two_pow_le_syl` and using `log_ulcm_le`'s copy of
the same statement instead; it should also avoid importing `Submission.Work.BW.syl_divisibility`
(whose `sylBlocks_ne_zero` collides with `ulcm_le_three_pow`'s).  Expect the same dependencies
(`split_aux`, `est_Pi`, `norm_Delta_le`, `Theta_eq_taylor_coeff`, `ulcm_le_four_pow`,
`ulcm_le_three_pow`, `syl_log_facts`, `acH_lower`, `num_13`, `num_T`, `sigma_ge`) and the same
private helpers (`log_multinomial_bound`, `est13_corr`, `norm_taylor_coeff_le`, ...). -/
theorem est13_clean {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (μ : Fin r → ℕ) (Tst : ℝ) (hTst : Tst ≤ acT K σ)
    (t0 : ℕ) (t : Fin (r - 1) → ℕ) (ht : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ Tst) (z : ℂ) :
    ‖acf φ α b k L ι v σ p J μ t0 t z‖ ≤
      Real.exp (lnp φ p + (acH K b v : ℝ) * Tst + 0.204 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ +
        1.008 * (‖z‖ / 2 ^ J) * acD K σ) := by
  classical
  have hr : 2 ≤ r := H.hr
  have hd : 1 ≤ dK K := by
    have hpos : 0 < dK K := by
      haveI : Nontrivial K := inferInstance
      exact Module.finrank_pos (R := ℚ) (M := K)
    omega
  have hdR : (0:ℝ) < (dK K : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hd)
  have hd1 : (1:ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hd
  have hh : 19 ≤ acH K b v := (acH_lower H).1
  have hh1 : 1 ≤ acH K b v := le_trans (by norm_num) hh
  have hhR : (0:ℝ) < (acH K b v : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hh1)
  have hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  have hDpos : 0 < acD K σ := pD_pos hr hd σ hσ
  have hDnn : 0 ≤ acD K σ := le_of_lt hDpos
  have hSnn : 0 ≤ acS K r b v := by
    have h1 : (0:ℝ) ≤ (pS r (dK K) (acH K b v) : ℝ) := by positivity
    exact h1
  have hTst' : Tst ≤ (pT r (dK K) σ : ℝ) := hTst
  have hpt : (t0 : ℝ) ≤ (pT r (dK K) σ : ℝ) := by
    have h1 : (t0 : ℝ) ≤ ((t0 + ∑ m, t m : ℕ) : ℝ) := by
      push_cast
      exact le_add_of_nonneg_right (by positivity)
    exact le_trans h1 (le_trans ht hTst')
  -- the numerical input
  set x : ℝ := ‖z‖ / 2 ^ J with hxdef
  have hx : 0 ≤ x := by rw [hxdef]; positivity
  -- the four numerical inputs of BW (13).  `num13_*` are the *proved* arithmetic helper
  -- lemmas of the sibling node `num_13` (they do not depend on `ulcm_le_three_pow`), while the
  -- Hanson bound enters only through the logarithmic form `log_ulcm_le` needed for `u(h)^{t₀}`.
  have h13a : Real.log 1.7 < 0.028 * (acH K b v : ℝ) := by
    have h := num13_log_17_lt
    have h19 : (19:ℝ) ≤ (acH K b v : ℝ) := by exact_mod_cast hh
    nlinarith [h, h19]
  have h13d : Real.log ((acH K b v : ℝ) * (pD0 r (dK K) σ + 1) *
        ∏ j, ((pDj r (dK K) σ j : ℝ) + 1)) ≤
      0.001 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ) :=
    num13_logN hr hd hh σ hσ
  have h13b : (Real.log (ulcm (acH K b v)) - (acH K b v : ℝ)) * (t0 : ℝ)
      ≤ 0.1 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ) := by
    have hupos : (0:ℝ) < (ulcm (acH K b v) : ℝ) := by
      have hne : ulcm (acH K b v) ≠ 0 := ulcm_ne_zero _
      exact_mod_cast Nat.pos_of_ne_zero hne
    have hlogu : Real.log (ulcm (acH K b v)) ≤ (acH K b v : ℝ) * 1.1 := by
      have h := hanson_ulcm_log_le (acH K b v)
      linarith [h]
    have hkey : Real.log (ulcm (acH K b v)) - (acH K b v : ℝ) ≤ 0.1 * (acH K b v : ℝ) := by
      linarith [hlogu]
    have ht0nn : (0:ℝ) ≤ (t0 : ℝ) := Nat.cast_nonneg _
    calc (Real.log (ulcm (acH K b v)) - (acH K b v : ℝ)) * (t0 : ℝ)
        ≤ (0.1 * (acH K b v : ℝ)) * (t0 : ℝ) := mul_le_mul_of_nonneg_right hkey ht0nn
      _ = 0.1 * (acH K b v : ℝ) * (t0 : ℝ) := by ring
      _ ≤ 0.1 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ) := by
          have h2 : (t0 : ℝ) ≤ (pT r (dK K) σ : ℝ) := hpt
          have h3 : (0:ℝ) ≤ 0.1 * (acH K b v : ℝ) := by positivity
          nlinarith [h2, h3]
  have h13c : ((Real.log (57 * r * dK K) + 2 / (57 * r * dK K)) * (acH K b v : ℝ)
        + x / (57 * r * dK K)) * ((pD0 r (dK K) σ : ℝ) + 1)
      ≤ (0.108 * acS K r b v + 0.007 * x) * acD K σ / (dK K : ℝ) := by
    have hpart := num13_hpart hr hd σ hσ
    have xpart := num13_xpart hr hd σ hσ
    have hh0 : (0:ℝ) ≤ (acH K b v : ℝ) := by positivity
    have hS : (pS r (dK K) (acH K b v) : ℝ) = 16 * (r:ℝ) * (dK K:ℝ) * (acH K b v:ℝ) := by
      simp only [pS]; push_cast; ring
    have h1 : (Real.log (57 * (r:ℝ) * (dK K:ℝ)) + 2 / (57 * (r:ℝ) * (dK K:ℝ)))
          * (acH K b v:ℝ) * ((pD0 r (dK K) σ : ℝ) + 1)
        ≤ 0.108 * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ / (dK K:ℝ) := by
      have h := mul_le_mul_of_nonneg_right hpart hh0
      rw [hS]
      have hd0 : (0:ℝ) < (dK K:ℝ) := by positivity
      rw [le_div_iff₀ hd0]
      nlinarith [h, hd0.le]
    have h2 : x / (57 * (r:ℝ) * (dK K:ℝ)) * ((pD0 r (dK K) σ : ℝ) + 1)
        ≤ 0.007 * x * pD r (dK K) σ / (dK K:ℝ) := by
      have hstep : x / (57 * (r:ℝ) * (dK K:ℝ)) * ((pD0 r (dK K) σ : ℝ) + 1)
          ≤ x / (57 * (r:ℝ) * (dK K:ℝ)) * (0.399 * ((r:ℝ) * pD r (dK K) σ)) :=
        mul_le_mul_of_nonneg_left xpart (by positivity)
      have hxe : x / (57 * (r:ℝ) * (dK K:ℝ)) * (0.399 * ((r:ℝ) * pD r (dK K) σ))
          = 0.007 * x * pD r (dK K) σ / (dK K:ℝ) := by
        field_simp
        ring
      rw [hxe] at hstep
      exact hstep
    have hgoal : ((Real.log (57 * (r:ℝ) * (dK K:ℝ)) + 2 / (57 * (r:ℝ) * (dK K:ℝ)))
          * (acH K b v:ℝ) + x / (57 * (r:ℝ) * (dK K:ℝ))) * ((pD0 r (dK K) σ : ℝ) + 1)
        = (Real.log (57 * (r:ℝ) * (dK K:ℝ)) + 2 / (57 * (r:ℝ) * (dK K:ℝ)))
            * (acH K b v:ℝ) * ((pD0 r (dK K) σ : ℝ) + 1)
          + x / (57 * (r:ℝ) * (dK K:ℝ)) * ((pD0 r (dK K) σ : ℝ) + 1) := by ring
    have hcomb : ((Real.log (57 * (r:ℝ) * (dK K:ℝ)) + 2 / (57 * (r:ℝ) * (dK K:ℝ)))
          * (acH K b v:ℝ) + x / (57 * (r:ℝ) * (dK K:ℝ))) * ((pD0 r (dK K) σ : ℝ) + 1)
        ≤ 0.108 * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ / (dK K:ℝ)
          + 0.007 * x * pD r (dK K) σ / (dK K:ℝ) := by
      rw [hgoal]; linarith [h1, h2]
    have hfin : 0.108 * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ / (dK K:ℝ)
          + 0.007 * x * pD r (dK K) σ / (dK K:ℝ)
        = (0.108 * acS K r b v + 0.007 * x) * acD K σ / (dK K : ℝ) := by ring
    rw [hfin] at hcomb
    exact hcomb
  obtain ⟨hTa, hTb, hTc, hTd⟩ := num_T (r := r) (d := dK K) (h := acH K b v) hr hd hh σ hσ
  -- the exponent of the estimate
  set M : ℝ := 57 * (r : ℝ) * (dK K : ℝ) with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  set Θe : ℝ := ((Real.log M + 3 / M) * (acH K b v : ℝ) + x / M) * ((pD0 r (dK K) σ : ℝ) + 1)
    with hΘe
  set Ept : ℝ := lnp φ p + (acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ)
      + Real.log (ulcm (acH K b v)) * (t0 : ℝ) + Real.log 1.7 * (pT r (dK K) σ : ℝ) + Θe
      + 1.001 * x * acD K σ with hEpt
  -- the unfolded sum
  have hdecomp : acf φ α b k L ι v σ p J μ t0 t z =
      ∑ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
        (if (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j) then
          φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
            * (ulcm (acH K b v) : ℂ) ^ t0
            * Theta (((2 : ℂ) ^ J)⁻¹ * z + ((lm.1 : ℕ) : ℂ)) (acH K b v) ((lm.2.1 : ℕ) + 1) t0
            * ∏ j, (Complex.exp (z * ellM φ α b k v L j)) ^ ((lm.2.2 j : ℕ) / 2 ^ J)
        else 0) := by
    simp only [acf, fAt, QJ, Qdesc, MvPolynomial.eval_sum]
    exact Finset.sum_congr rfl fun lm _ =>
      eval_Qdesc_summand φ b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ t0 t
        (fun j => ellM φ α b k v L j) z lm
  -- each summand is bounded by `exp Ept`
  have hterm : ∀ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
      ‖(if (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j) then
          φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
            * (ulcm (acH K b v) : ℂ) ^ t0
            * Theta (((2 : ℂ) ^ J)⁻¹ * z + ((lm.1 : ℕ) : ℂ)) (acH K b v) ((lm.2.1 : ℕ) + 1) t0
            * ∏ j, (Complex.exp (z * ellM φ α b k v L j)) ^ ((lm.2.2 j : ℕ) / 2 ^ J)
        else 0)‖ ≤ Real.exp Ept := by
    intro lm
    by_cases hc : (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j)
    · rw [if_pos hc]
      -- (1) `‖φ (p lm)‖ ≤ e^{lnp}`
      have h1 : ‖φ (p lm)‖ ≤ Real.exp (lnp φ p) := by
        have hpne : ∃ i, p i ≠ 0 := by
          by_contra hcon
          push_neg at hcon
          exact H.hp0 (funext hcon)
        obtain ⟨i0, hi0⟩ := hpne
        have hφ0 : φ (p i0) ≠ 0 := by
          intro h0
          have h1' : φ (p i0) * φ ((p i0)⁻¹) = 1 := by
            rw [← map_mul, mul_inv_cancel₀ hi0, map_one]
          rw [h0, zero_mul] at h1'
          exact one_ne_zero h1'.symm
        have hpos : 0 < ‖φ (p i0)‖ := norm_pos_iff.mpr hφ0
        have hbdd : BddAbove (Set.range fun i : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) =>
            ‖φ (p i)‖) := (Set.finite_range _).bddAbove
        have hsup : 0 < ⨆ i, ‖φ (p i)‖ := lt_of_lt_of_le hpos (le_ciSup hbdd i0)
        rw [lnp, Real.exp_log hsup]
        exact le_ciSup hbdd lm
      -- (2) the `Δ`-product (`est_Pi`)
      have h2 : ‖∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)‖
          ≤ Real.exp ((acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ)) * 1.7 ^ pT r (dK K) σ := by
        refine est_Pi H (fun i => (lm.2.2 i : ℕ)) (fun i => ?_) t ?_
        · exact Nat.lt_succ_iff.mp (lm.2.2 i).isLt
        · have h1' : ((∑ m, t m : ℕ) : ℝ) ≤ ((t0 + ∑ m, t m : ℕ) : ℝ) := by
            push_cast
            exact le_add_of_nonneg_left (by positivity)
          exact le_trans h1' (le_trans ht hTst)
      -- (3) `u(h)^{t₀}`
      have h3 : ‖((ulcm (acH K b v) : ℂ)) ^ t0‖
          ≤ Real.exp (Real.log (ulcm (acH K b v)) * (t0 : ℝ)) := by
        have hu : (0:ℝ) < (ulcm (acH K b v) : ℝ) := by
          have h := ulcm_pos (acH K b v)
          exact_mod_cast h
        rw [norm_pow, Complex.norm_natCast, ← Real.rpow_natCast (ulcm (acH K b v) : ℝ) t0,
          Real.rpow_def_of_pos hu]
      -- (4) the `Θ` factor
      have hwnorm : ‖((2 : ℂ) ^ J)⁻¹ * z + ((lm.1 : ℕ) : ℂ)‖ ≤ x + (acH K b v : ℝ) := by
        have hnorm : ‖(2 : ℂ)‖ = 2 := Complex.norm_natCast 2
        have hA : ‖((2 : ℂ) ^ J)⁻¹ * z‖ ≤ x := by
          have he : ‖((2 : ℂ) ^ J)⁻¹ * z‖ = ‖z‖ / (2:ℝ) ^ J := by
            rw [norm_mul, norm_inv, norm_pow, hnorm, div_eq_mul_inv]
            ring
          rw [he, hxdef]
        have hB : ‖(((lm.1 : ℕ) : ℂ))‖ ≤ (acH K b v : ℝ) := by
          rw [Complex.norm_natCast]
          exact_mod_cast le_of_lt (lm.1).isLt
        calc ‖((2 : ℂ) ^ J)⁻¹ * z + ((lm.1 : ℕ) : ℂ)‖
            ≤ ‖((2 : ℂ) ^ J)⁻¹ * z‖ + ‖(((lm.1 : ℕ) : ℂ))‖ := norm_add_le _ _
          _ ≤ x + (acH K b v : ℝ) := add_le_add hA hB
      have hbase : Real.exp 1 * (2 + ‖((2 : ℂ) ^ J)⁻¹ * z + ((lm.1 : ℕ) : ℂ)‖ / (acH K b v : ℝ))
          ≤ Real.exp 1 * (3 + x / (acH K b v : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
        have h2' : ‖((2 : ℂ) ^ J)⁻¹ * z + ((lm.1 : ℕ) : ℂ)‖ / (acH K b v : ℝ)
            ≤ (x + (acH K b v : ℝ)) / (acH K b v : ℝ) :=
          div_le_div_of_nonneg_right hwnorm hhR.le
        have h3' : 2 + (x + (acH K b v : ℝ)) / (acH K b v : ℝ) = 3 + x / (acH K b v : ℝ) := by
          field_simp
          ring
        linarith
      have hexp : (acH K b v) * ((lm.2.1 : ℕ) + 1) ≤ (acH K b v) * ((pD0 r (dK K) σ) + 1) :=
        Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr (lm.2.1).isLt)
      have h4a := Theta_bound (((2 : ℂ) ^ J)⁻¹ * z + ((lm.1 : ℕ) : ℂ)) (acH K b v)
        ((lm.2.1 : ℕ) + 1) t0 hh1
      have h4b : (Real.exp 1 * (2 + ‖((2 : ℂ) ^ J)⁻¹ * z + ((lm.1 : ℕ) : ℂ)‖ / (acH K b v : ℝ)))
            ^ ((acH K b v) * ((lm.2.1 : ℕ) + 1))
          ≤ (Real.exp 1 * (3 + x / (acH K b v : ℝ))) ^ ((acH K b v) * ((pD0 r (dK K) σ) + 1)) := by
        have hbase1 : (1:ℝ) ≤ Real.exp 1 * (3 + x / (acH K b v : ℝ)) := by
          have h1 : (1:ℝ) ≤ Real.exp 1 := by
            have := Real.add_one_le_exp 1
            linarith
          have h2 : (1:ℝ) ≤ 3 + x / (acH K b v : ℝ) := by
            have h3 : (0:ℝ) ≤ x / (acH K b v : ℝ) := by positivity
            linarith
          nlinarith [h1, h2]
        calc (Real.exp 1 * (2 + ‖((2 : ℂ) ^ J)⁻¹ * z + ((lm.1 : ℕ) : ℂ)‖ / (acH K b v : ℝ)))
              ^ ((acH K b v) * ((lm.2.1 : ℕ) + 1))
            ≤ (Real.exp 1 * (3 + x / (acH K b v : ℝ))) ^ ((acH K b v) * ((lm.2.1 : ℕ) + 1)) :=
              pow_le_pow_left₀ (by positivity) hbase _
          _ ≤ (Real.exp 1 * (3 + x / (acH K b v : ℝ))) ^ ((acH K b v) * ((pD0 r (dK K) σ) + 1)) :=
              pow_le_pow_right₀ hbase1 hexp
      have h4c : (Real.exp 1 * (3 + x / (acH K b v : ℝ))) ^ ((acH K b v) * ((pD0 r (dK K) σ) + 1))
          = Real.exp ((((acH K b v) * ((pD0 r (dK K) σ) + 1) : ℕ) : ℝ)
              * (1 + Real.log (3 + x / (acH K b v : ℝ)))) := by
        rw [← Real.rpow_natCast (Real.exp 1 * (3 + x / (acH K b v : ℝ)))
            ((acH K b v) * ((pD0 r (dK K) σ) + 1)),
          Real.rpow_def_of_pos (by positivity),
          Real.log_mul (ne_of_gt (Real.exp_pos 1))
            (ne_of_gt (by positivity : (0:ℝ) < 3 + x / (acH K b v : ℝ))),
          Real.log_exp]
        congr 1
        ring
      have h4d : Real.log (3 + x / (acH K b v : ℝ))
          ≤ Real.log M + (3 + x / (acH K b v : ℝ)) / M - 1 := by
        have h1' : (0:ℝ) < (3 + x / (acH K b v : ℝ)) / M := by positivity
        have h2' := Real.log_le_sub_one_of_pos h1'
        rw [Real.log_div (ne_of_gt (by positivity : (0:ℝ) < 3 + x / (acH K b v : ℝ)))
          (ne_of_gt hMpos)] at h2'
        linarith
      have h4e : Real.exp ((((acH K b v) * ((pD0 r (dK K) σ) + 1) : ℕ) : ℝ)
            * (1 + Real.log (3 + x / (acH K b v : ℝ)))) ≤ Real.exp Θe := by
        apply Real.exp_le_exp.mpr
        rw [hΘe]
        have heq : (((acH K b v) * ((pD0 r (dK K) σ) + 1) : ℕ) : ℝ)
            = (acH K b v : ℝ) * (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) := by push_cast; ring
        rw [heq]
        have hne : ((acH K b v : ℝ)) ≠ 0 := ne_of_gt hhR
        have h1' : 1 + Real.log (3 + x / (acH K b v : ℝ))
            ≤ Real.log M + 3 / M + x / ((acH K b v : ℝ) * M) := by
          have h := h4d
          have hsplit : (3 + x / (acH K b v : ℝ)) / M
              = 3 / M + x / ((acH K b v : ℝ) * M) := by
            field_simp
          linarith [h, hsplit.le]
        have h2' := mul_le_mul_of_nonneg_left h1'
          (by positivity : (0:ℝ) ≤ (acH K b v : ℝ) * (((pD0 r (dK K) σ : ℕ) : ℝ) + 1))
        have h3' : (acH K b v : ℝ) * (((pD0 r (dK K) σ : ℕ) : ℝ) + 1)
              * (Real.log M + 3 / M + x / ((acH K b v : ℝ) * M))
            = ((Real.log M + 3 / M) * (acH K b v : ℝ) + x / M)
              * (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) := by
          field_simp
        linarith [h2', h3'.le]
      have h4 : ‖Theta (((2 : ℂ) ^ J)⁻¹ * z + ((lm.1 : ℕ) : ℂ)) (acH K b v) ((lm.2.1 : ℕ) + 1) t0‖
          ≤ Real.exp Θe :=
        le_trans h4a (le_trans h4b (le_trans (le_of_eq h4c) h4e))
      -- (5) the `e^{zM}` product
      have h5 : ‖∏ j, (Complex.exp (z * ellM φ α b k v L j)) ^ ((lm.2.2 j : ℕ) / 2 ^ J)‖
          ≤ Real.exp (1.001 * x * acD K σ) := by
        have hprod : ∏ j : Fin r, (Complex.exp (z * ellM φ α b k v L j)) ^ ((lm.2.2 j : ℕ) / 2 ^ J)
            = Complex.exp (z * ∑ j, (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℂ) * ellM φ α b k v L j) := by
          have h1' : ∀ j : Fin r, (Complex.exp (z * ellM φ α b k v L j)) ^ ((lm.2.2 j : ℕ) / 2 ^ J)
              = Complex.exp ((((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℂ) * (z * ellM φ α b k v L j)) := by
            intro j
            rw [← Complex.exp_nat_mul]
          rw [Finset.prod_congr rfl (fun j _ => h1' j), ← Complex.exp_sum Finset.univ]
          congr 1
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [hprod, Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        have hS := ellM_sum_le H J (fun j => (lm.2.2 j : ℕ) / 2 ^ J)
          (fun j => le_trans (Nat.div_mul_le_self _ _) (Nat.lt_succ_iff.mp (lm.2.2 j).isLt))
        calc (z * ∑ j, (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℂ) * ellM φ α b k v L j).re
            ≤ ‖z * ∑ j, (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℂ) * ellM φ α b k v L j‖ :=
              Complex.re_le_norm _
          _ = ‖z‖ * ‖∑ j, (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℂ) * ellM φ α b k v L j‖ := norm_mul _ _
          _ ≤ ‖z‖ * (1.001 * acD K σ / 2 ^ J) := mul_le_mul_of_nonneg_left hS (norm_nonneg _)
          _ = 1.001 * x * acD K σ := by rw [hxdef]; ring
      -- assemble the five factors
      have hA5 : (0:ℝ) ≤ Real.exp (lnp φ p) := by positivity
      have hB5 : (0:ℝ) ≤ Real.exp ((acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ)) * 1.7 ^ pT r (dK K) σ := by
        positivity
      have hC5 : (0:ℝ) ≤ Real.exp (Real.log (ulcm (acH K b v)) * (t0 : ℝ)) := by positivity
      have hD5 : (0:ℝ) ≤ Real.exp Θe := by positivity
      have hE5 : (0:ℝ) ≤ Real.exp (1.001 * x * acD K σ) := by positivity
      have hchain :
          ‖φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
              * (ulcm (acH K b v) : ℂ) ^ t0
              * Theta (((2 : ℂ) ^ J)⁻¹ * z + ((lm.1 : ℕ) : ℂ)) (acH K b v) ((lm.2.1 : ℕ) + 1) t0
              * ∏ j, (Complex.exp (z * ellM φ α b k v L j)) ^ ((lm.2.2 j : ℕ) / 2 ^ J)‖
            ≤ Real.exp (lnp φ p)
              * (Real.exp ((acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ)) * 1.7 ^ pT r (dK K) σ)
              * Real.exp (Real.log (ulcm (acH K b v)) * (t0 : ℝ)) * Real.exp Θe
              * Real.exp (1.001 * x * acD K σ) := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hA5)
            h3 (norm_nonneg _) (by positivity)) h4 (norm_nonneg _) (by positivity))
            h5 (norm_nonneg _) (by positivity)
      have h17 : (1.7 : ℝ) ^ (pT r (dK K) σ)
          = Real.exp (Real.log 1.7 * (pT r (dK K) σ : ℝ)) := by
        rw [← Real.rpow_natCast (1.7 : ℝ) (pT r (dK K) σ),
          Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 1.7)]
      have hexpand : Real.exp (lnp φ p)
              * (Real.exp ((acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ)) * 1.7 ^ pT r (dK K) σ)
              * Real.exp (Real.log (ulcm (acH K b v)) * (t0 : ℝ)) * Real.exp Θe
              * Real.exp (1.001 * x * acD K σ)
            = Real.exp Ept := by
        rw [h17, hEpt, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
          ← Real.exp_add]
        congr 1
        ring
      linarith [hchain, hexpand.le, hexpand.ge]
    · rw [if_neg hc]
      simp only [norm_zero]
      exact Real.exp_pos Ept |>.le
  -- the sum
  have hsum : ‖∑ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
        (if (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j) then
          φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
            * (ulcm (acH K b v) : ℂ) ^ t0
            * Theta (((2 : ℂ) ^ J)⁻¹ * z + ((lm.1 : ℕ) : ℂ)) (acH K b v) ((lm.2.1 : ℕ) + 1) t0
            * ∏ j, (Complex.exp (z * ellM φ α b k v L j)) ^ ((lm.2.2 j : ℕ) / 2 ^ J)
        else 0)‖
      ≤ (Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℝ) * Real.exp Ept := by
    calc ‖∑ lm, (if (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j) then
          φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
            * (ulcm (acH K b v) : ℂ) ^ t0
            * Theta (((2 : ℂ) ^ J)⁻¹ * z + ((lm.1 : ℕ) : ℂ)) (acH K b v) ((lm.2.1 : ℕ) + 1) t0
            * ∏ j, (Complex.exp (z * ellM φ α b k v L j)) ^ ((lm.2.2 j : ℕ) / 2 ^ J)
        else 0)‖
        ≤ ∑ lm, ‖(if (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j) then
          φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
            * (ulcm (acH K b v) : ℂ) ^ t0
            * Theta (((2 : ℂ) ^ J)⁻¹ * z + ((lm.1 : ℕ) : ℂ)) (acH K b v) ((lm.2.1 : ℕ) + 1) t0
            * ∏ j, (Complex.exp (z * ellM φ α b k v L j)) ^ ((lm.2.2 j : ℕ) / 2 ^ J)
        else 0)‖ := norm_sum_le Finset.univ _
      _ ≤ ∑ _lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ), Real.exp Ept :=
          Finset.sum_le_sum (fun lm _ => hterm lm)
      _ = (Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℝ) * Real.exp Ept := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- the cardinality
  have hcard : (Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℝ)
      = (acH K b v : ℝ) * ((pD0 r (dK K) σ : ℕ) : ℝ) * ∏ j, ((pDj r (dK K) σ j : ℝ) + 1) + (acH K b v : ℝ) * ∏ j, ((pDj r (dK K) σ j : ℝ) + 1) := by
    simp only [AuxIdx, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin]
    push_cast
    ring
  have hlogN : Real.log ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℕ) : ℝ)
      ≤ 0.001 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ) := by
    have h := h13d
    have harg : (acH K b v : ℝ) * ((pD0 r (dK K) σ : ℕ) : ℝ) * ∏ j, ((pDj r (dK K) σ j : ℝ) + 1)
          + (acH K b v : ℝ) * ∏ j, ((pDj r (dK K) σ j : ℝ) + 1)
        = (acH K b v : ℝ) * (pD0 r (dK K) σ + 1) * ∏ j, ((pDj r (dK K) σ j : ℝ) + 1) := by
      push_cast
      ring
    rw [hcard, harg]
    exact h
  -- the final arithmetic
  have hA : (acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ) + Real.log (ulcm (acH K b v)) * (t0 : ℝ)
      ≤ (acH K b v : ℝ) * Tst + 0.1 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ) := by
    have hkey : Real.log (ulcm (acH K b v)) * (t0 : ℝ)
        = (acH K b v : ℝ) * (t0 : ℝ)
          + (Real.log (ulcm (acH K b v)) - (acH K b v : ℝ)) * (t0 : ℝ) := by ring
    rw [hkey]
    have h1 : (acH K b v : ℝ) * (((∑ m, t m : ℕ) : ℝ) + (t0 : ℝ)) ≤ (acH K b v : ℝ) * Tst := by
      refine mul_le_mul_of_nonneg_left ?_ hhR.le
      have ht' := ht
      have hcast : ((t0 + ∑ m, t m : ℕ) : ℝ) = (t0:ℝ) + ((∑ m, t m : ℕ) : ℝ) := by push_cast; ring
      linarith [ht', hcast.le, hcast.ge]
    nlinarith [h1, h13b]
  have hB : Real.log 1.7 * (pT r (dK K) σ : ℝ)
      ≤ 0.028 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ) :=
    mul_le_mul_of_nonneg_right (le_of_lt h13a) (by positivity)
  have hC : Θe ≤ (0.108 * acS K r b v + 0.007 * x) * acD K σ / (dK K : ℝ)
      + 0.0005 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ := by
    have hsplit : Θe = ((Real.log M + 2 / M) * (acH K b v : ℝ) + x / M) * ((pD0 r (dK K) σ : ℝ) + 1)
        + (acH K b v : ℝ) * ((pD0 r (dK K) σ : ℝ) + 1) / (57 * (r:ℝ) * (dK K : ℝ)) := by
      rw [hΘe, hMdef]
      field_simp
      ring
    rw [hsplit]
    have h1 : ((Real.log M + 2 / M) * (acH K b v : ℝ) + x / M) * ((pD0 r (dK K) σ : ℝ) + 1)
        = ((Real.log (57 * r * dK K) + 2 / (57 * r * dK K)) * (acH K b v : ℝ)
            + x / (57 * r * dK K)) * (pD0 r (dK K) σ + 1) := by
      rw [hMdef]
    have h2 : (acH K b v : ℝ) * ((pD0 r (dK K) σ : ℝ) + 1) / (57 * (r:ℝ) * (dK K : ℝ))
        ≤ 0.0005 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ :=
      est13_corr hr hd σ hσ
    linarith [h2]
  have hPT : 0.1 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)
        + 0.028 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)
        + 0.001 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)
      ≤ 0.09482 * acS K r b v * acD K σ / (dK K : ℝ) := by
    have h1 : (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)
        ≤ 0.735 * acS K r b v * acD K σ / (dK K : ℝ) := by
      rw [le_div_iff₀ hdR]
      linarith [hTc]
    have h2 : 0.1 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)
        + 0.028 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)
        + 0.001 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)
        = 0.129 * ((acH K b v : ℝ) * (pT r (dK K) σ : ℝ)) := by ring
    rw [h2]
    have h3 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 0.129)
    have h4 : 0.129 * (0.735 * acS K r b v * acD K σ / (dK K : ℝ))
        = 0.094815 * acS K r b v * acD K σ / (dK K : ℝ) := by ring
    have h5 : (0:ℝ) ≤ acS K r b v * acD K σ / (dK K : ℝ) :=
      div_nonneg (mul_nonneg hSnn hDnn) hdR.le
    have h6 : 0.129 * (0.735 * acS K r b v * acD K σ / (dK K : ℝ))
        ≤ 0.09482 * acS K r b v * acD K σ / (dK K : ℝ) := by
      have hc : (0.129 * 0.735 : ℝ) ≤ 0.09482 := by norm_num
      have h7 := mul_le_mul_of_nonneg_right hc h5
      calc 0.129 * (0.735 * acS K r b v * acD K σ / (dK K : ℝ))
          = (0.129 * 0.735) * (acS K r b v * acD K σ / (dK K : ℝ)) := by ring
        _ ≤ 0.09482 * (acS K r b v * acD K σ / (dK K : ℝ)) := h7
        _ = 0.09482 * acS K r b v * acD K σ / (dK K : ℝ) := by ring
    linarith [h3, h4.le, h4.ge, h6]
  have hxd : 0.007 * x * acD K σ / (dK K : ℝ) ≤ 0.007 * x * acD K σ := by
    have h2 : (0:ℝ) ≤ 0.007 * x * acD K σ := by positivity
    calc 0.007 * x * acD K σ / (dK K : ℝ)
        = 0.007 * x * acD K σ * (1 / (dK K : ℝ)) := by ring
      _ ≤ 0.007 * x * acD K σ * 1 := by
          apply mul_le_mul_of_nonneg_left _ h2
          rw [div_le_one hdR]
          exact hd1
      _ = 0.007 * x * acD K σ := by ring
  have hC' : Θe ≤ 0.108 * (acS K r b v * acD K σ / (dK K : ℝ))
      + 0.007 * (x * acD K σ / (dK K : ℝ))
      + 0.0005 * (acS K r b v * acD K σ / (dK K : ℝ)) := by
    calc Θe ≤ (0.108 * acS K r b v + 0.007 * x) * acD K σ / (dK K : ℝ)
            + 0.0005 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ := hC
      _ = 0.108 * (acS K r b v * acD K σ / (dK K : ℝ))
          + 0.007 * (x * acD K σ / (dK K : ℝ))
          + 0.0005 * (acS K r b v * acD K σ / (dK K : ℝ)) := by ring
  have harith : Real.log ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℕ) : ℝ)
        + Ept
      ≤ lnp φ p + (acH K b v : ℝ) * Tst
        + 0.204 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ + 1.008 * x * acD K σ := by
    rw [hEpt]
    have h0 : (0:ℝ) ≤ acD K σ * (dK K : ℝ)⁻¹ * acS K r b v := by positivity
    have hxx : (1.001 * x * acD K σ + 0.007 * x * acD K σ : ℝ) = 1.008 * x * acD K σ := by
      ring
    have hz : (0:ℝ) ≤ acS K r b v * acD K σ / (dK K : ℝ) :=
      div_nonneg (mul_nonneg hSnn hDnn) hdR.le
    rw [show 0.204 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ
        = 0.204 * (acS K r b v * acD K σ / (dK K : ℝ)) by ring]
    -- the linear combination of the five bounds above
    linear_combination (norm := ring_nf)
      hlogN + hA + hB + hC' + hxd + hPT + hxx + (0.00068 : ℝ) * hz <;> norm_num
  -- final
  have hNpos : (0:ℝ) < (Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℝ) := by
    haveI : Nonempty (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) :=
      ⟨(⟨0, by omega⟩, ⟨0, Nat.succ_pos _⟩, fun _ => ⟨0, Nat.succ_pos _⟩)⟩
    have h1 : 0 < Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) :=
      Fintype.card_pos
    exact_mod_cast h1
  calc ‖acf φ α b k L ι v σ p J μ t0 t z‖
      = ‖∑ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
        (if (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j) then
          φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
            * (ulcm (acH K b v) : ℂ) ^ t0
            * Theta (((2 : ℂ) ^ J)⁻¹ * z + ((lm.1 : ℕ) : ℂ)) (acH K b v) ((lm.2.1 : ℕ) + 1) t0
            * ∏ j, (Complex.exp (z * ellM φ α b k v L j)) ^ ((lm.2.2 j : ℕ) / 2 ^ J)
        else 0)‖ := by rw [hdecomp]
    _ ≤ (Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℝ) * Real.exp Ept := hsum
    _ = Real.exp (Real.log ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℕ) : ℝ) + Ept) := by
        have h1 : Real.exp (Real.log ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℕ) : ℝ) + Ept)
            = ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℕ) : ℝ) * Real.exp Ept := by
          rw [Real.exp_add, Real.exp_log hNpos]
        exact h1.symm
    _ ≤ Real.exp (lnp φ p + (acH K b v : ℝ) * Tst
          + 0.204 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ + 1.008 * x * acD K σ) :=
        Real.exp_le_exp.mpr harith
    _ = Real.exp (lnp φ p + (acH K b v : ℝ) * Tst
          + 0.204 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ + 1.008 * (‖z‖ / 2 ^ J) * acD K σ) := by
        rw [hxdef]

end Work.BW
