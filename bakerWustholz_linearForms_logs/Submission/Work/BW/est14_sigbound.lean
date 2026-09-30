import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.est14_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! ### Auxiliary facts for the exponent bound of BW (14)

The exponent `δ_λ = Σ_j (λ_j/2^J) z (M_j − L_j)` of the `λ`-th summand of `f^{(J)} − g^{(J)}`
satisfies `|δ_λ| ≤ |Λ| · ‖z‖ D / 2^J`, because `M_j − L_j = −(L_{jk}/b_k) 2^{−v} Λ`, the §11
estimate `Σ_j D_j |L_{jk}| ≤ 2^v D` holds, and `|b_k| ≥ 1`. -/

/-- `‖((2 : ℂ) ^ v)⁻¹‖ = ((2 : ℝ) ^ v)⁻¹`. -/
private lemma norm_inv_two_pow (v : ℕ) : ‖(((2 : ℂ) ^ v)⁻¹)‖ = ((2 : ℝ) ^ v)⁻¹ := by
  rw [norm_inv, norm_pow, Complex.norm_ofNat]

/-- The exact value of `‖(x : ℂ) / (y : ℂ)‖` for integers `x`, `y`. -/
private lemma norm_ratio_int (x y : ℤ) :
    ‖(x : ℂ) / (y : ℂ)‖ = |((x : ℤ) : ℝ)| / |((y : ℤ) : ℝ)| := by
  rw [norm_div, Complex.norm_intCast, Complex.norm_intCast]

/-- Triangle inequality for the exponent: the constants `z`, `(2^v)⁻¹` and `Λ = lam φ α b` factor
out of the sum defining `estSig`. -/
private lemma estSig_norm_aux {K : Type*} [Field K] {n r : ℕ} {h D0 : ℕ} {Dj : Fin r → ℕ}
    (φ : K →+* ℂ) (α : Fin n → K) (b : Fin n → ℤ) (k : Fin n) (v : ℕ)
    (L : Fin r → Fin n → ℤ) (J : ℕ) (z : ℂ) (lm : AuxIdx r h D0 Dj) :
    ‖estSig φ α b k v L J z lm‖ ≤
      ‖z‖ * ((2 : ℝ) ^ v)⁻¹ * ‖lam φ α b‖ *
        ∑ j : Fin r, (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ) *
          (|((L j k : ℤ) : ℝ)| / |((b k : ℤ) : ℝ)|) := by
  have hinner : ∀ j : Fin r,
      z * (ellM φ α b k v L j - lamP φ α v L j)
        = z * (-((((L j k : ℂ) / (b k : ℂ)) * ((2 : ℂ) ^ v)⁻¹) * lam φ α b)) := by
    intro j
    simp only [ellM]
    ring
  have hterm : ∀ j : Fin r,
      ‖((((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℂ)) *
          (z * (ellM φ α b k v L j - lamP φ α v L j))‖
        = ‖z‖ * ((2 : ℝ) ^ v)⁻¹ * ‖lam φ α b‖ *
            ((((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ) *
              (|((L j k : ℤ) : ℝ)| / |((b k : ℤ) : ℝ)|)) := by
    intro j
    rw [hinner j]
    simp only [norm_mul, norm_neg, norm_ratio_int, norm_inv_two_pow, norm_natCast]
    ring
  unfold estSig
  calc ‖∑ j : Fin r, ((((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℂ)) *
          (z * (ellM φ α b k v L j - lamP φ α v L j))‖
      ≤ ∑ j : Fin r, ‖((((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℂ)) *
          (z * (ellM φ α b k v L j - lamP φ α v L j))‖ :=
        norm_sum_le Finset.univ _
    _ = ∑ j : Fin r, ‖z‖ * ((2 : ℝ) ^ v)⁻¹ * ‖lam φ α b‖ *
          ((((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ) *
            (|((L j k : ℤ) : ℝ)| / |((b k : ℤ) : ℝ)|)) :=
        Finset.sum_congr rfl (fun j _ => hterm j)
    _ = ‖z‖ * ((2 : ℝ) ^ v)⁻¹ * ‖lam φ α b‖ *
          ∑ j : Fin r, ((((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ) *
            (|((L j k : ℤ) : ℝ)| / |((b k : ℤ) : ℝ)|)) := by
        rw [Finset.mul_sum]

/-- BW §11: the `λ`-weighted column estimate `Σ_j (λ_j/2^J)(|L_{jk}|/|b_k|) ≤ 2^v D / 2^J`. -/
private lemma sig_sum_aux {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ)
    (lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) :
    (∑ j : Fin r, (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ) *
        (|((L j k : ℤ) : ℝ)| / |((b k : ℤ) : ℝ)|))
      ≤ (2 : ℝ) ^ v * acD K σ / 2 ^ J := by
  obtain ⟨_, hr, hBH, _, _, _, _, _⟩ := H
  obtain ⟨_, _, _, _, hσpos, hα'hmod, hrow, _⟩ := hBH
  have hdR1 : (1 : ℝ) ≤ (dK K : ℝ) := by
    rw [Nat.one_le_cast_iff_ne_zero]
    exact (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hd0 : (0 : ℝ) < (dK K : ℝ) := lt_of_lt_of_le zero_lt_one hdR1
  have hr0 : (0 : ℝ) < (r : ℝ) := by
    have h2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hmh_ge : ∀ i : Fin n, 1 / (dK K : ℝ) ≤ BakerWustholz.modifiedHeight φ (α i) := by
    intro i
    simp only [BakerWustholz.modifiedHeight, dK]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hmh_nn : ∀ i : Fin n, 0 ≤ BakerWustholz.modifiedHeight φ (α i) :=
    fun i => le_trans (le_of_lt (one_div_pos.mpr hd0)) (hmh_ge i)
  have hσ : ∀ j : Fin r, 1 / (dK K : ℝ) ≤ σ j := by
    intro j
    have h1 : 1 / (dK K : ℝ) ≤ hmod (α' j) (lamP φ α v L j) := by
      simp only [hmod, dK]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    exact le_trans h1 (hα'hmod j)
  have hDnn : 0 ≤ pD r (dK K) σ := by
    simp only [pD]
    have hlog : 0 ≤ Real.log (2 * ↑r * ↑(dK K)) := by
      apply Real.log_nonneg
      have h2 : (1 : ℝ) ≤ (r : ℝ) := by
        exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hr)
      nlinarith [h2, hdR1]
    have hp : 0 ≤ ∏ j : Fin r, σ j := Finset.prod_nonneg (fun j _ => (hσpos j).le)
    have h1 : (0 : ℝ) ≤ 2 * (r : ℝ) ^ r := by positivity
    have h2 : (0 : ℝ) ≤ (32 * (dK K : ℝ)) ^ (r + 1) := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) hlog) hp
  -- the per-column bound `D_j |L_{jk}| ≤ 2^v D / r`
  have hcol : ∀ j : Fin r,
      (pDj r (dK K) σ j : ℝ) * |((L j k : ℤ) : ℝ)| ≤ (2 : ℝ) ^ v * pD r (dK K) σ / (r : ℝ) := by
    intro j
    have hσj : 0 < σ j := hσpos j
    have hLjk : |((L j k : ℤ) : ℝ)| ≤ (2 : ℝ) ^ v * σ j * (dK K : ℝ) := by
      have hsingle : |((L j k : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α k)
          ≤ ∑ i : Fin n, |((L j i : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α i) := by
        have hsub := Finset.sum_le_sum_of_subset_of_nonneg (s := ({k} : Finset (Fin n)))
          (f := fun i => |((L j i : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α i))
          (Finset.subset_univ _) (fun x _ _ => mul_nonneg (abs_nonneg _) (hmh_nn x))
        rwa [Finset.sum_singleton] at hsub
      have h1 : |((L j k : ℤ) : ℝ)| / (dK K : ℝ) ≤ (2 : ℝ) ^ v * σ j := by
        calc |((L j k : ℤ) : ℝ)| / (dK K : ℝ)
            = |((L j k : ℤ) : ℝ)| * (1 / (dK K : ℝ)) := by ring
          _ ≤ |((L j k : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α k) :=
              mul_le_mul_of_nonneg_left (hmh_ge k) (abs_nonneg _)
          _ ≤ ∑ i : Fin n, |((L j i : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α i) := hsingle
          _ ≤ (2 : ℝ) ^ v * σ j := hrow j
      rwa [div_le_iff₀ hd0] at h1
    have hfloor : (pDj r (dK K) σ j : ℝ) ≤ pD r (dK K) σ / ((r : ℝ) * (dK K : ℝ) * σ j) := by
      rw [pDj]
      refine Nat.floor_le ?_
      have hden : 0 < (r : ℝ) * (dK K : ℝ) * σ j := by positivity
      exact div_nonneg hDnn hden.le
    calc (pDj r (dK K) σ j : ℝ) * |((L j k : ℤ) : ℝ)|
        ≤ (pD r (dK K) σ / ((r : ℝ) * (dK K : ℝ) * σ j)) * ((2 : ℝ) ^ v * σ j * (dK K : ℝ)) :=
          mul_le_mul hfloor hLjk (abs_nonneg _) (div_nonneg hDnn (by positivity))
      _ = (2 : ℝ) ^ v * pD r (dK K) σ / (r : ℝ) := by
          rw [div_mul_eq_mul_div,
            div_eq_div_iff (by positivity : (r : ℝ) * (dK K : ℝ) * σ j ≠ 0)
              (ne_of_gt hr0)]
          ring
  have hDsum : (∑ j : Fin r, (pDj r (dK K) σ j : ℝ) * |((L j k : ℤ) : ℝ)|)
      ≤ (2 : ℝ) ^ v * acD K σ := by
    calc ∑ j : Fin r, (pDj r (dK K) σ j : ℝ) * |((L j k : ℤ) : ℝ)|
        ≤ ∑ _j : Fin r, (2 : ℝ) ^ v * pD r (dK K) σ / (r : ℝ) :=
          Finset.sum_le_sum (fun j _ => hcol j)
      _ = (r : ℝ) * ((2 : ℝ) ^ v * pD r (dK K) σ / (r : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (2 : ℝ) ^ v * acD K σ := by
          show (r : ℝ) * ((2 : ℝ) ^ v * pD r (dK K) σ / (r : ℝ))
              = (2 : ℝ) ^ v * pD r (dK K) σ
          rw [mul_div_assoc', mul_div_cancel_left₀ _ (ne_of_gt hr0)]
  -- assemble: `λ_j ≤ D_j` and `|b_k| ≥ 1`
  have hcast : (((2 : ℕ) ^ J : ℕ) : ℝ) = (2 : ℝ) ^ J := by push_cast; ring
  calc ∑ j : Fin r, (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ) *
          (|((L j k : ℤ) : ℝ)| / |((b k : ℤ) : ℝ)|)
      ≤ ∑ j : Fin r, ((pDj r (dK K) σ j : ℝ) / (2 : ℝ) ^ J) * |((L j k : ℤ) : ℝ)| := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        have hDj : (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ)
            ≤ (pDj r (dK K) σ j : ℝ) / (2 : ℝ) ^ J := by
          have hle : (lm.2.2 j : ℕ) ≤ pDj r (dK K) σ j :=
            Nat.lt_succ_iff.mp (lm.2.2 j).isLt
          have hdiv := Nat.cast_div_le (α := ℝ) (m := (lm.2.2 j : ℕ)) (n := 2 ^ J)
          rw [hcast] at hdiv
          exact le_trans hdiv (div_le_div_of_nonneg_right (by exact_mod_cast hle) (by positivity))
        have habs : |((L j k : ℤ) : ℝ)| / |((b k : ℤ) : ℝ)| ≤ |((L j k : ℤ) : ℝ)| := by
          rcases eq_or_ne (b k) 0 with hb | hb
          · rw [hb]; simp
          · have hb1 : (1 : ℝ) ≤ |((b k : ℤ) : ℝ)| := by
              have h1 : (1 : ℤ) ≤ |b k| := Int.one_le_abs hb
              calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
                _ ≤ ((|b k| : ℤ) : ℝ) := by exact_mod_cast h1
                _ = |((b k : ℤ) : ℝ)| := by rw [Int.cast_abs]
            calc |((L j k : ℤ) : ℝ)| / |((b k : ℤ) : ℝ)|
                ≤ |((L j k : ℤ) : ℝ)| / 1 :=
                  div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hb1
              _ = |((L j k : ℤ) : ℝ)| := by ring
        have hb0 : (0 : ℝ) ≤ (pDj r (dK K) σ j : ℝ) / (2 : ℝ) ^ J :=
          div_nonneg (by positivity) (by positivity)
        exact mul_le_mul hDj habs (div_nonneg (abs_nonneg _) (abs_nonneg _)) hb0
    _ = (1 / (2 : ℝ) ^ J) * ∑ j : Fin r, (pDj r (dK K) σ j : ℝ) * |((L j k : ℤ) : ℝ)| := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
    _ ≤ (1 / (2 : ℝ) ^ J) * ((2 : ℝ) ^ v * acD K σ) :=
        mul_le_mul_of_nonneg_left hDsum (by positivity)
    _ = (2 : ℝ) ^ v * acD K σ / (2 : ℝ) ^ J := by ring

/-- The exponent `δ_λ = Σ_j (λ_j/2^J) z (M_j - L_j)` of the `λ`-th summand of `f^{(J)} - g^{(J)}` satisfies `|δ_λ| ≤ |Λ| · ‖z‖ D / 2^J`, because `M_j - L_j = -(L_{jk}/b_k) 2^{-v} Λ`, `Σ_j D_j |L_{jk}| ≤ 2^v D` (BW §11) and `|b_k| ≥ 1`. -/
theorem est14_sigbound {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (z : ℂ)
    (lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) :
    ‖estSig φ α b k v L J z lm‖ ≤ ‖lam φ α b‖ * (‖z‖ * acD K σ / 2 ^ J) := by
  have hS := estSig_norm_aux φ α b k v L J z lm
  have hA := sig_sum_aux H J lm
  calc ‖estSig φ α b k v L J z lm‖
      ≤ ‖z‖ * ((2 : ℝ) ^ v)⁻¹ * ‖lam φ α b‖ *
          ∑ j : Fin r, (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ) *
            (|((L j k : ℤ) : ℝ)| / |((b k : ℤ) : ℝ)|) := hS
    _ ≤ ‖z‖ * ((2 : ℝ) ^ v)⁻¹ * ‖lam φ α b‖ * ((2 : ℝ) ^ v * acD K σ / 2 ^ J) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
    _ = ‖lam φ α b‖ * (‖z‖ * acD K σ / 2 ^ J) := by
        have hx : ((2 : ℝ) ^ v) ≠ 0 := by positivity
        calc ‖z‖ * ((2 : ℝ) ^ v)⁻¹ * ‖lam φ α b‖ * ((2 : ℝ) ^ v * acD K σ / 2 ^ J)
            = (‖z‖ * ‖lam φ α b‖) * (((2 : ℝ) ^ v)⁻¹ * (2 : ℝ) ^ v) *
                (acD K σ / 2 ^ J) := by ring
          _ = (‖z‖ * ‖lam φ α b‖) * 1 * (acD K σ / 2 ^ J) := by
                simp only [inv_mul_cancel₀ hx]
          _ = ‖lam φ α b‖ * (‖z‖ * acD K σ / 2 ^ J) := by ring

end Work.BW
