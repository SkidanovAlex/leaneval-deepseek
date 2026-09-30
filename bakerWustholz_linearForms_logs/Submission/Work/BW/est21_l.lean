import Mathlib
import Submission.Work.BW.DefsAC

import Submission.Work.BW.taylorC_acf_expand_clean
import Submission.Work.BW.est21_l_vanish_n_red
import Submission.Work.BW.est21_dpoly_diff_final
import Submission.Work.BW.est21_l_count
import Submission.Work.BW.acH_lower
import Submission.Work.BW.sigma_ge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
namespace Work.BW

/-- BW (1993) §17, p. 47–50: the desired estimate for `f_m(l)`, the l-side input to (21).
Setting: `Q^{(J)}` is the level-`J` descended auxiliary polynomial (`QJ`); `acf` is its evaluation
along `Y₀ = z, Y_j = e^{z M_j}` with `M = ellM`, and `acg` along `Y_j = α'_j^z` (`lamP`).
Hypothesis: `g(l;t') = 0` for ALL twists `t'` with `t'_0 + … + t'_{r-1} ≤ T' + T''`.
Conclusion: `log‖taylorC (acf t) m l‖ ≤ ln(p) + h·T* + 0.282·(1/d)SD + 1.01·2^{-J}‖l‖D − 9·2^r SD`.
Route (BW §16–17, p. 46–50; every ingredient is already in the workspace). Write `V_λ P := fAt λ P l`
and let `D = ∂₀ + Σ_j ℓ_j Y_j∂_j` (`ℓ = ellM`) be the chain-rule operator of `iteratedDeriv_fAt`, so
`f^{(m)}(l) = V_ellM (D^[m] QJ(t0,t))`.  (1) `ellM_eq_sum_derVec` + `derVec_mem_span_iota`: the
`z`-derivative direction `M = ellM` is a ℂ-combination of `∂₀` and the `r−1` chosen `∂*`-directions
`E_m = eulerDer (derVec b k L (ι m) ·)`, hence `D^[m]` expands into `∂₀^a ∏E_m^{t'_m}` with
`a + Σt' = m`; by `applyDer_Qdesc_span` each such derivative of `Qdesc … J μ t0 t` is a combination
of the twists `QJ(t0+a, t')` with `Σt' ≤ Σt + Σt''`, whose orders are `≤ T' + T''`, so by `hvan` all
of them vanish at the `lamP`-point `l`.  Hence `f^{(m)}(l) = (V_ellM − V_lamP)(D^[m] QJ(t0,t))` (no
coefficient bound is needed for this step).  (2) The two evaluations of the SAME polynomial at the
`M`-point and at the `α'`-point differ by the factor `e^{δ} − 1`, `δ(z;λ) = z·(Σ_jλ_j)(M_j − lamP_j)`;
this is the `f − g` comparison of `est14` (`log‖acf − acg‖ ≤ ln p + hT* + (0.205/d + 1.01·2^{-J}‖z‖/S − 9·2^r)SD`),
which is linear in the polynomial, so it applies to `D^[m]QJ` and to its twist-expansion terms as
well; the `−9·2^r SD` comes from the standing smallness (10), `log‖1 − e^{δ}‖ ≤ 0.001((1/d)SD + ‖z‖D) − 9·2^r SD`.
(3) Bookkeeping: the `Σ_λ` of the difference (at most `2^T` terms; `num_17`: `T log 2 ≤ 0.027·SD/d`)
raises `0.205` to `0.226`; the `Σ_{a}∏E^{t'}`-expansion (at most `2^m`, `m ≤ T`, again `num_17`)
raises it to `0.255`; the `Σ_λ` of the derivative polynomial gives the final `0.282`.  Numeric inputs:
`num_17`, `num_kum` (`log 2 ≤ 0.001 SD`), `num_T` (`dhT ≤ 0.735 SD`), `acH_lower`, `sigma_ge`,
`num_D_lower`, `num_13`.  Proved helpers: `norm_Delta_le`, `norm_Theta_le`,
`norm_Delta_pow_le_sphere`, `est_Pi`, `est_Theta_yu`, `ulcm_le_three_pow`.  Auxiliary sizes:
`‖γ_m(λ)‖ ≤ e^{h+1}D`, and `‖l‖·Σ_jλ_j|M_j| ≤ 2^{-J}‖l‖D` (from `hmod(α'_j,lamP_j) ≤ σ_j` and
`Σ_jλ_jD_j ≤ D`).  Sanity: `m = 0` — `hvan` gives `g(l;t) = 0`, so `f(l) = (f−g)(l)` and `est14` at
`z = l` gives the claim with `0.205 ≤ 0.282`.  This is exactly BW's p. 49 estimate for `f^{(t)}(l)`,
which p. 50 combines with (15) to give (21); the final assembly is done in `Submission/Work/BW/est21`. -/
theorem est21_l {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (hJ : J ≤ pI r (dK K)) (μ : Fin r → ℕ) (Tst : ℝ)
    (hTst : Tst ≤ acT K σ) (Tp Tpp : ℝ) (hTp : 0 ≤ Tp) (hsum : Tp + Tpp ≤ Tst)
    (l : ℂ)
    (hvan : ∀ (t0' : ℕ) (t' : Fin (r - 1) → ℕ), ((t0' + ∑ m, t' m : ℕ) : ℝ) ≤ Tp + Tpp →
      acg φ α b k L ι v σ p J μ t0' t' l = 0)
    (t0 : ℕ) (t : Fin (r - 1) → ℕ) (ht : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ Tpp) (m : ℕ)
    (hm : (m : ℝ) ≤ Tp) :
    ‖taylorC (acf φ α b k L ι v σ p J μ t0 t) m l‖ ≤
      Real.exp (lnp φ p + (acH K b v : ℝ) * Tst + 0.282 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ +
        1.01 * (‖l‖ / 2 ^ J) * acD K σ - 9 * 2 ^ r * acS K r b v * acD K σ) := by
  classical
  -- BW's p. 48 expansion of `f_m` over the pairs `(a, t')` with `a + Σt' = m`
  set S : Finset (Fin (m + 1) × (Fin n → Fin (m + 1))) :=
    Finset.univ.filter (fun at' => (at'.1 : ℕ) + ∑ i, (at'.2 i : ℕ) = m) with hS
  set coeff : Fin (m + 1) × (Fin n → Fin (m + 1)) → ℂ := fun at' =>
    (((at'.1 : ℕ).factorial : ℂ))⁻¹ *
      ∏ i, (((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ)) ^ (at'.2 i : ℕ) /
        (((at'.2 i : ℕ).factorial : ℂ)) with hcoeff
  set PP : Fin (m + 1) × (Fin n → Fin (m + 1)) → MvPolynomial (Fin (r + 1)) ℂ := fun at' =>
    applyDer (fun i j => (derVec b k L i j : ℚ)) (at'.1 : ℕ) (fun i => (at'.2 i : ℕ))
      (QJ φ b k L ι v σ p J μ t0 t) with hPP
  have hmem : ∀ at' ∈ S, (at'.1 : ℕ) + ∑ i, (at'.2 i : ℕ) = m := by
    intro at' hat'
    simpa only [hS, Finset.mem_filter, Finset.mem_univ, true_and] using hat'
  have hd1 : 1 ≤ dK K := by
    have h := Module.finrank_pos (R := ℚ) (M := K)
    show 1 ≤ Module.finrank ℚ K
    omega
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) H.hr)
  have hdpos : (0 : ℝ) < (dK K : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hd1)
  have h19 : 19 ≤ acH K b v := (acH_lower H).1
  have hhpos : (0 : ℝ) < (acH K b v : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 19) h19)
  have hSpos : (0 : ℝ) < acS K r b v := by
    have h2 : (0 : ℝ) < (r : ℝ) := hrpos
    have h3 : (0 : ℝ) < (dK K : ℝ) := hdpos
    have h4 : (0 : ℝ) < (acH K b v : ℝ) := hhpos
    simp only [acS, pS]
    push_cast
    positivity
  have hSne : acS K r b v ≠ 0 := ne_of_gt hSpos
  have h0Tpp : 0 ≤ Tpp := by
    have h2 : (0 : ℝ) ≤ ((t0 + ∑ m, t m : ℕ) : ℝ) := by positivity
    linarith [ht]
  have hmT : (m : ℝ) ≤ acT K σ :=
    le_trans hm (le_trans (le_add_of_nonneg_right h0Tpp) (le_trans hsum hTst))
  have hzero : ∀ at' ∈ S, fAt (fun j => lamP φ α v L j) (PP at') l = 0 := by
    intro at' hat'
    have h1 := hmem at' hat'
    have hord : ((t0 + (at'.1 : ℕ) + ∑ i, (at'.2 i : ℕ) + ∑ m, t m : ℕ) : ℝ) ≤ Tp + Tpp := by
      have h2n : (t0 + (at'.1 : ℕ) + ∑ i, (at'.2 i : ℕ) + ∑ m, t m : ℕ)
          = (t0 + ∑ m, t m) + m := by omega
      have h2 : ((t0 + (at'.1 : ℕ) + ∑ i, (at'.2 i : ℕ) + ∑ m, t m : ℕ) : ℝ)
          = ((t0 + ∑ m, t m : ℕ) : ℝ) + (m : ℝ) := by
        rw [h2n]
        push_cast
        ring
      rw [h2]
      linarith [ht, hm]
    simpa only [hPP] using
      est21_l_vanish_n_red H J μ Tp Tpp l hvan t0 t (at'.1 : ℕ) (fun i => (at'.2 i : ℕ)) hord
  have hstep : taylorC (acf φ α b k L ι v σ p J μ t0 t) m l
      = ∑ at' ∈ S, coeff at' * (fAt (ellM φ α b k v L) (PP at') l
          - fAt (fun j => lamP φ α v L j) (PP at') l) := by
    rw [taylorC_acf_expand_clean H J μ t0 t m l, ← hS]
    refine Finset.sum_congr rfl fun at' hat' => ?_
    simp only [hcoeff, hPP]
    rw [show fAt (fun j => lamP φ α v L j)
        (applyDer (fun i j => (derVec b k L i j : ℚ)) (at'.1 : ℕ) (fun i => (at'.2 i : ℕ))
          (QJ φ b k L ι v σ p J μ t0 t)) l = 0 from hzero at' hat']
    ring
  have hterm : ∀ at' ∈ S,
      ‖coeff at' * (fAt (ellM φ α b k v L) (PP at') l
          - fAt (fun j => lamP φ α v L j) (PP at') l)‖
        ≤ Real.exp (lnp φ p + (acH K b v : ℝ) * Tst +
            (0.255 * (1 / (dK K : ℝ)) + 1.01 * ((‖l‖ / 2 ^ J) / acS K r b v) - 9 * 2 ^ r) *
              acS K r b v * acD K σ) := by
    intro at' hat'
    have h1 := hmem at' hat'
    have hord : ((t0 + (at'.1 : ℕ) + ∑ i, (at'.2 i : ℕ) + ∑ m, t m : ℕ) : ℝ) ≤ Tst := by
      have h2n : (t0 + (at'.1 : ℕ) + ∑ i, (at'.2 i : ℕ) + ∑ m, t m : ℕ)
          = (t0 + ∑ m, t m) + m := by omega
      have h2 : ((t0 + (at'.1 : ℕ) + ∑ i, (at'.2 i : ℕ) + ∑ m, t m : ℕ) : ℝ)
          = ((t0 + ∑ m, t m : ℕ) : ℝ) + (m : ℝ) := by
        rw [h2n]
        push_cast
        ring
      rw [h2]
      linarith [ht, hm, hsum]
    simpa only [hcoeff, hPP] using
      est21_dpoly_diff_final H J hJ μ Tst hTst t0 t (at'.1 : ℕ) (fun i => (at'.2 i : ℕ)) hord l
  have hcard : (S.card : ℝ) ≤ (((m + 1) ^ n : ℕ) : ℝ) := by
    have hinj : ∀ x ∈ S, ∀ y ∈ S, x.2 = y.2 → x = y := by
      intro x hx y hy hxy
      have hx1 := hmem x hx
      have hy1 := hmem y hy
      have h1 : (x.1 : ℕ) = (y.1 : ℕ) := by
        have hsum : ∑ i, (x.2 i : ℕ) = ∑ i, (y.2 i : ℕ) := by rw [hxy]
        omega
      exact Prod.ext (Fin.ext h1) hxy
    have hcard' : S.card ≤ (Finset.univ : Finset (Fin n → Fin (m + 1))).card :=
      calc S.card = (S.image (fun x => x.2)).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.univ : Finset (Fin n → Fin (m + 1))).card :=
            Finset.card_le_card (Finset.subset_univ _)
    have hc : (((Finset.univ : Finset (Fin n → Fin (m + 1))).card : ℕ) : ℝ)
        = (((m + 1) ^ n : ℕ) : ℝ) := by
      rw [Finset.card_univ, Fintype.card_fun]
      simp
    rw [← hc]
    exact_mod_cast hcard'
  have hcount : ((((m + 1) ^ n : ℕ)) : ℝ)
      ≤ Real.exp (0.027 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ) := by
    have h := est21_l_count H.hr h19 (acH_lower H).2 (fun j => sigma_ge H j) m hmT
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using h
  have hexpeq : lnp φ p + (acH K b v : ℝ) * Tst +
        (0.255 * (1 / (dK K : ℝ)) + 1.01 * ((‖l‖ / 2 ^ J) / acS K r b v) - 9 * 2 ^ r) *
          acS K r b v * acD K σ + 0.027 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ
      = lnp φ p + (acH K b v : ℝ) * Tst +
          0.282 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ +
        1.01 * (‖l‖ / 2 ^ J) * acD K σ - 9 * 2 ^ r * acS K r b v * acD K σ := by
    field_simp
    ring
  calc ‖taylorC (acf φ α b k L ι v σ p J μ t0 t) m l‖
      = ‖∑ at' ∈ S, coeff at' * (fAt (ellM φ α b k v L) (PP at') l
          - fAt (fun j => lamP φ α v L j) (PP at') l)‖ := by rw [hstep]
    _ ≤ ∑ at' ∈ S, ‖coeff at' * (fAt (ellM φ α b k v L) (PP at') l
          - fAt (fun j => lamP φ α v L j) (PP at') l)‖ := norm_sum_le _ _
    _ ≤ ∑ _at' ∈ S, Real.exp (lnp φ p + (acH K b v : ℝ) * Tst +
            (0.255 * (1 / (dK K : ℝ)) + 1.01 * ((‖l‖ / 2 ^ J) / acS K r b v) - 9 * 2 ^ r) *
              acS K r b v * acD K σ) := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * Real.exp (lnp φ p + (acH K b v : ℝ) * Tst +
            (0.255 * (1 / (dK K : ℝ)) + 1.01 * ((‖l‖ / 2 ^ J) / acS K r b v) - 9 * 2 ^ r) *
              acS K r b v * acD K σ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((((m + 1) ^ n : ℕ)) : ℝ) * Real.exp (lnp φ p + (acH K b v : ℝ) * Tst +
            (0.255 * (1 / (dK K : ℝ)) + 1.01 * ((‖l‖ / 2 ^ J) / acS K r b v) - 9 * 2 ^ r) *
              acS K r b v * acD K σ) := by
          exact mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ ≤ Real.exp (0.027 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ) *
          Real.exp (lnp φ p + (acH K b v : ℝ) * Tst +
            (0.255 * (1 / (dK K : ℝ)) + 1.01 * ((‖l‖ / 2 ^ J) / acS K r b v) - 9 * 2 ^ r) *
              acS K r b v * acD K σ) := by
          exact mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le
    _ = Real.exp (0.027 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ +
          (lnp φ p + (acH K b v : ℝ) * Tst +
            (0.255 * (1 / (dK K : ℝ)) + 1.01 * ((‖l‖ / 2 ^ J) / acS K r b v) - 9 * 2 ^ r) *
              acS K r b v * acD K σ)) :=
          (Real.exp_add (0.027 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ)
            (lnp φ p + (acH K b v : ℝ) * Tst +
              (0.255 * (1 / (dK K : ℝ)) + 1.01 * ((‖l‖ / 2 ^ J) / acS K r b v) - 9 * 2 ^ r) *
                acS K r b v * acD K σ)).symm
    _ = Real.exp (lnp φ p + (acH K b v : ℝ) * Tst +
          0.282 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ +
        1.01 * (‖l‖ / 2 ^ J) * acD K σ - 9 * 2 ^ r * acS K r b v * acD K σ) := by
          congr 1
          rw [add_comm]
          exact hexpeq

end Work.BW
