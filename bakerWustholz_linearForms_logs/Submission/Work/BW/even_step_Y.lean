import Mathlib
import Submission.Work.BW.even_step_defs

-- Sorry-free helpers from the existing (25) development; the only `sorry` in that chain is
-- `Work.BW.bpOdd_den_prod_le`, whose *statement* is re-proved below (imported as
-- `Work.BW.bpOdd_den_prod_le_fix`) so that this file's theorem uses no `sorryAx`.
import Submission.Work.BW.bprodOdd_norm_ge
import Submission.Work.BW.bprod_real_le
import Submission.Work.BW.bpOdd_den_prod_le_fix
import Submission.Work.BW.acH_lower

namespace Work.BW

/-- `1 ≤ pS r d h` for `r ≥ 1`, `d ≥ 1`, `h ≥ 1`. -/
private lemma even_step_Y_one_le_pS {r d h : ℕ} (hr : 1 ≤ r) (hd : 1 ≤ d) (hh : 1 ≤ h) :
    1 ≤ pS r d h := by
  rw [pS]
  have h := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (show (1 : ℕ) ≤ 16 by norm_num) hr) hd) hh
  simpa using h

/-- `4S^{(J)} ≤ X + 2` with `X = evX r J S = 2⌊2ξ^{-rJ}S⌋`: the floor loses at most `1`. This is the
`X + 2` in the `X`-hypothesis of `(25)`. -/
private lemma even_step_Y_four_SJ_le_X_add_two {r J : ℕ} {S : ℝ} :
    4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S) ≤ (evX r J S : ℝ) + 2 := by
  have h := Nat.lt_floor_add_one (2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S))
  have hX : (evX r J S : ℝ)
      = 2 * ((⌊2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S)⌋₊ : ℕ) : ℝ) := by
    rw [evX, evSP]; push_cast; ring
  rw [hX]
  have h' : 2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S)
      < ((⌊2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S)⌋₊ : ℕ) : ℝ) + 1 := h
  linarith

/-! ### Sorry-free re-proof of the `(25)` chain used by the `Y`-estimate

`Work.BW.bprodOdd_ratio_le_exp_evY` gives exactly what we need, but it descends from
`Work.BW.bpOdd_den_prod_le`, which is still `sorry`. The chain
`bprodOdd_norm_ge` → `bprod_ratio25` → `bprodOdd_ratio_le_exp_evY` is re-proved here with only that
one missing lemma replaced by its sorry-free copy `bpOdd_den_prod_le_fix`; every other ingredient is
reused verbatim from the (sorry-free) modules above. -/

theorem even_step_Y_bprodOdd_norm_ge {R η : ℝ} (hη : 0 < η) (hη' : η < 1 / 2) {X : ℕ} (hX : 2 ≤ X)
    (hXe : Even X) (hXR : (X : ℝ) + η ≤ R) {l : ℤ} (hlo : Odd l) (hl : |l| ≤ (X : ℤ))
    {z : ℂ} (hz : ‖z - (l : ℂ)‖ = η) :
    4 * Real.pi * η * (1 - η / 2) ^ 2 * (X : ℝ) ^ (X - 2) / (Real.exp (X : ℝ) * R ^ X)
      ≤ ‖bprodOdd R X z‖ := by
  obtain ⟨m, rfl⟩ := even_iff_exists_two_mul.mp hXe
  have hm : 1 ≤ m := by omega
  have hR : 0 < R := by
    have h1 : (2:ℝ) ≤ ((2*m : ℕ) : ℝ) := by exact_mod_cast hX
    linarith
  have hloc : Odd l := hlo
  obtain ⟨i₀, hi₀⟩ := hloc
  have hlZ : |(2*i₀ + 1 : ℤ)| ≤ 2*(m:ℤ) := by rw [← hi₀]; simpa using hl
  have hA := (abs_le.mp hlZ).1
  have hB := (abs_le.mp hlZ).2
  have hpi₁ : -(m:ℤ) ≤ i₀ := by omega
  have hpi₂ : i₀ ≤ (m:ℤ) - 1 := by omega
  have hA0 : 0 ≤ (m:ℤ) - 1 - i₀ := by omega
  have hB0 : 0 ≤ (m:ℤ) + i₀ := by omega
  have hre := bpOdd_dist_reindex (η := η) hm hpi₁ hpi₂
  rw [← hi₀] at hre
  have hAB := toNat_add_toNat m i₀ hA0 hB0 hm
  have harith := bpOdd_dist_arith hη hη' hm hAB
  have hPge : 2*(1-η/2)*bpNum m ≤ ∏ k ∈ (oddIdx (2*m)).erase l, (|(k:ℝ)-(l:ℝ)|-η) := by
    rw [← hre]
    exact harith
  have hLP := bprodOdd_lower hη hη' hX hXe hXR hlo hl hz
  have hDle := bpOdd_den_prod_le_fix hη hη' hX hXe hXR hlo hl
  have hNum := bpOdd_num25 m hm
  set P : ℝ := ∏ k ∈ (oddIdx (2*m)).erase l, (|(k:ℝ) - (l:ℝ)| - η) with hPdef
  set D : ℝ := ∏ k ∈ oddIdx (2*m), bpD R η l k with hDdef
  set K₀ : ℝ := 4 * Real.pi * (((2*m : ℕ)) : ℝ) ^ (2*m - 2) / Real.exp ((((2*m : ℕ)) : ℝ))
    with hKdef
  have hLP' : R^(2*m) * η * P / D ≤ ‖bprodOdd R (2*m) z‖ := by
    rw [hPdef, hDdef]
    exact hLP
  have hDle' : D ≤ R^(2*(2*m)) / (1-η/2) := by rw [hDdef]; exact hDle
  have hPge' : 2*(1-η/2)*bpNum m ≤ P := by rw [hPdef]; exact hPge
  have hNum' : K₀ ≤ 2*bpNum m := by rw [hKdef]; exact hNum
  have hDpos : 0 < D := by
    rw [hDdef]
    exact Finset.prod_pos (fun k hk => bpD_pos (le_of_lt hη) (bpDen_lt hη hX hXR hl hk))
  have hRpow : 0 < R^(2*m) := pow_pos hR _
  have hpow : R^(2*(2*m)) = R^(2*m) * R^(2*m) := by
    rw [show 2*(2*m) = 2*m + 2*m by omega, pow_add]
  have hN : 4 * Real.pi * η * (1-η/2)^2 * (((2*m:ℕ)):ℝ)^(2*m-2) / Real.exp ((((2*m:ℕ)):ℝ))
      = η * (1-η/2)^2 * K₀ := by
    rw [hKdef]; ring
  have hgoal : 4 * Real.pi * η * (1-η/2)^2 * (((2*m:ℕ)):ℝ)^(2*m-2)
        /(Real.exp ((((2*m:ℕ)):ℝ)) * R^(2*m))
      = (η * (1-η/2)^2 * K₀)/R^(2*m) := by
    rw [← div_div, hN]
  have key : (η * (1-η/2)^2 * K₀)/R^(2*m) ≤ R^(2*m)*η*P/D := by
    rw [le_div_iff₀ hDpos, div_mul_eq_mul_div, div_le_iff₀ hRpow]
    have hDle'' : D ≤ R^(2*m)*R^(2*m)/(1-η/2) := by rw [← hpow]; exact hDle'
    have h1 : η*(1-η/2)^2*K₀ * D ≤ η*(1-η/2)^2*K₀ * (R^(2*m)*R^(2*m)/(1-η/2)) :=
      mul_le_mul_of_nonneg_left hDle'' (by positivity)
    have hne : (1 - η/2) ≠ 0 := by linarith
    have h2 : η*(1-η/2)^2*K₀ * (R^(2*m)*R^(2*m)/(1-η/2))
        = η*(1-η/2)*K₀*(R^(2*m)*R^(2*m)) := by
      field_simp
    have hle : (1-η/2)*K₀ ≤ P := by
      have ha : (1-η/2)*K₀ ≤ (1-η/2)*(2*bpNum m) :=
        mul_le_mul_of_nonneg_left hNum' (by linarith)
      have hb : (1-η/2)*(2*bpNum m) = 2*(1-η/2)*bpNum m := by ring
      linarith [hPge']
    have h3 : η*(1-η/2)*K₀*(R^(2*m)*R^(2*m)) ≤ R^(2*m)*η*P*R^(2*m) := by
      have hB' : η*((1-η/2)*K₀)*(R^(2*m)*R^(2*m)) ≤ η*P*(R^(2*m)*R^(2*m)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (le_of_lt hη)) (by positivity)
      nlinarith [hB']
    linarith
  rw [hgoal]
  exact le_trans key hLP'



private lemma key_arith (A B E R t : ℝ) (X : ℕ) (hX : 2 ≤ X) (hA : A ≠ 0) (hB : B ≠ 0)
    (hE : E ≠ 0) (hR : R ≠ 0) (hX0 : (X : ℝ) ≠ 0) :
    (A * B ^ 2 * (X : ℝ) ^ (X - 2) / (E * R ^ X)) *
        (A⁻¹ * B⁻¹ ^ 2 * (X : ℝ) ^ 2 * E * t ^ X)
      = t ^ X * ((X : ℝ) / R) ^ X := by
  have hsub : X - 2 + 2 = X := Nat.sub_add_cancel hX
  have hpow : (X : ℝ) ^ (X - 2) * (X : ℝ) ^ 2 = (X : ℝ) ^ X := by rw [← pow_add, hsub]
  rw [div_eq_mul_inv, mul_inv, inv_pow, div_pow, ← hpow]
  field_simp

/-- BW (25) (p. 52): lacunary analogue of (24): `X ≥ 2` even, `l` odd, `|l| ≤ X`: `|B'(x;X)/B'(z;X)| ≤ (4πη)^{-1}(1−η/2)^{-2}X²e^X(max(1,|x|/X))^X`. (Checked numerically.) -/
theorem even_step_Y_bprod_ratio25 (R η : ℝ) (hη : 0 < η) (hη' : η < 1 / 2) (X : ℕ) (hX : 2 ≤ X)
    (hXe : Even X) (hXR : (X : ℝ) + η ≤ R) (l : ℤ) (hlo : Odd l) (hl : |l| ≤ X) (z : ℂ)
    (hz : ‖z - l‖ = η) (x : ℝ) (hx : |x| ≤ R) :
    ‖bprodOdd R X x‖ ≤ ‖bprodOdd R X z‖ * ((4 * Real.pi * η)⁻¹ * (1 - η / 2)⁻¹ ^ 2 *
      (X : ℝ) ^ 2 * Real.exp X * (max 1 (|x| / X)) ^ X) := by
  -- Upper bound for `‖B' x‖` (BW (23')), from the sibling node `bprod_real_le`.
  have hXR' : (X : ℝ) < R := by linarith
  have hA : ‖bprodOdd R X (x : ℂ)‖ ≤ (max (X : ℝ) |x| / R) ^ X := by
    have h := (bprod_real_le R X hXR' x hx).2 hXe
    rwa [max_comm] at h
  -- Lower bound for `‖B' z‖` (BW (25), lower half).
  have hB : 4 * Real.pi * η * (1 - η / 2) ^ 2 * (X : ℝ) ^ (X - 2) / (Real.exp (X : ℝ) * R ^ X)
      ≤ ‖bprodOdd R X z‖ := even_step_Y_bprodOdd_norm_ge hη hη' hX hXe hXR hlo hl hz
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hXne : (X : ℝ) ≠ 0 := ne_of_gt hXpos
  have hRpos : (0 : ℝ) < R := by linarith [hXR]
  have hRne : R ≠ 0 := ne_of_gt hRpos
  -- `max(X,|x|)/R = max(1,|x|/X) * (X/R)`.
  have hmaxeq : max (X : ℝ) |x| / R = (max 1 (|x| / X)) * ((X : ℝ) / R) := by
    rw [div_eq_mul_inv]
    rw [max_mul_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ R⁻¹)]
    rw [max_mul_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ (X : ℝ) / R)]
    congr 1
    · rw [div_eq_mul_inv, one_mul]
    · field_simp
  -- The two product identities together give the theorem.
  have hkey := key_arith (4 * Real.pi * η) (1 - η / 2) (Real.exp (X : ℝ)) R
    (max 1 (|x| / X)) X hX (by positivity) (by linarith) (Real.exp_ne_zero _) hRne hXne
  have hC0 : 0 ≤ (4 * Real.pi * η)⁻¹ * (1 - η / 2)⁻¹ ^ 2 * (X : ℝ) ^ 2 * Real.exp X
      * (max 1 (|x| / X)) ^ X := by
    have h1 : (0 : ℝ) < 4 * Real.pi * η := by positivity
    have h2 : (0 : ℝ) < 1 - η / 2 := by linarith
    positivity
  calc ‖bprodOdd R X x‖
      ≤ (max (X : ℝ) |x| / R) ^ X := hA
    _ = (max 1 (|x| / X)) ^ X * ((X : ℝ) / R) ^ X := by rw [hmaxeq, mul_pow]
    _ = (4 * Real.pi * η * (1 - η / 2) ^ 2 * (X : ℝ) ^ (X - 2) / (Real.exp (X : ℝ) * R ^ X))
          * ((4 * Real.pi * η)⁻¹ * (1 - η / 2)⁻¹ ^ 2 * (X : ℝ) ^ 2 * Real.exp X
              * (max 1 (|x| / X)) ^ X) := hkey.symm
    _ ≤ ‖bprodOdd R X z‖ * ((4 * Real.pi * η)⁻¹ * (1 - η / 2)⁻¹ ^ 2 * (X : ℝ) ^ 2
          * Real.exp X * (max 1 (|x| / X)) ^ X) := mul_le_mul_of_nonneg_right hB hC0


private lemma pxi_pos_local {r : ℕ} (hr : 2 ≤ r) : 0 < pxi r := by
  rw [pxi]
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hle : (0.536 : ℝ) / r ≤ 0.536 / 2 := by
    rw [div_le_div_iff₀ hrpos (by norm_num : (0 : ℝ) < 2)]
    linarith
  linarith

/-- `ξ = pxi r ≤ 1`. -/
private lemma pxi_le_one_local (r : ℕ) : pxi r ≤ 1 := by
  rw [pxi]
  have h : (0 : ℝ) ≤ 0.536 / r := div_nonneg (by norm_num) (Nat.cast_nonneg r)
  linarith

/-- The logarithm of the `(25)`-constant
`(4π/3)⁻¹(5/6)⁻²X²e^X(max 1 (|x|/X))^X` is at most `X + 2 log X + 3`, for `X ≥ 2` and
`|x| ≤ X + 2`. -/
private lemma evY_arith {X : ℕ} {x : ℝ} (hX : 2 ≤ X) (hx : |x| ≤ (X : ℝ) + 2) :
    Real.log ((4 * Real.pi * (1 / 3))⁻¹ * (1 - (1 / 3) / 2)⁻¹ ^ 2 * (X : ℝ) ^ 2 *
        Real.exp (X : ℝ) * (max 1 (|x| / (X : ℝ))) ^ X)
      ≤ (X : ℝ) + 2 * Real.log (X : ℝ) + 3 := by
  have hX0 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hXne : (X : ℝ) ≠ 0 := ne_of_gt hX0
  set A : ℝ := (4 * Real.pi * (1 / 3))⁻¹ with hA
  set B : ℝ := (1 - (1 / 3) / 2)⁻¹ ^ 2 with hB
  set D : ℝ := max 1 (|x| / (X : ℝ)) with hD
  have hAp : 0 < A := by rw [hA]; positivity
  have hBp : 0 < B := by rw [hB]; positivity
  have hDp : 0 < D := by rw [hD]; exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hA1 : A ≤ 1 := by
    rw [hA]
    exact inv_le_one_of_one_le₀ (by nlinarith [Real.pi_gt_three])
  have hB1 : B ≤ Real.exp 1 := by
    rw [hB]
    have h : ((1 : ℝ) - (1 / 3) / 2)⁻¹ ^ 2 = (36 / 25 : ℝ) := by norm_num
    rw [h]
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
    linarith
  have hD1 : D ≤ 1 + 2 / (X : ℝ) := by
    rw [hD]
    refine max_le ?_ ?_
    · have : (0 : ℝ) ≤ 2 / (X : ℝ) := by positivity
      linarith
    · rw [div_le_iff₀ hX0]
      have he : (1 + 2 / (X : ℝ)) * (X : ℝ) = (X : ℝ) + 2 := by
        rw [add_mul, one_mul, div_mul_cancel₀ _ hXne]
      rw [he]
      exact hx
  have hlogA : Real.log A ≤ 0 := Real.log_nonpos (le_of_lt hAp) hA1
  have hlogB : Real.log B ≤ 1 := by
    have h := Real.log_le_log hBp hB1
    rwa [Real.log_exp] at h
  have hlogD : Real.log D ≤ 2 / (X : ℝ) := by
    have h1 : Real.log D ≤ Real.log (1 + 2 / (X : ℝ)) := Real.log_le_log hDp hD1
    have h2 : Real.log (1 + 2 / (X : ℝ)) ≤ 2 / (X : ℝ) := by
      have hpos : (0 : ℝ) < 1 + 2 / (X : ℝ) := by
        have h2p : (0 : ℝ) < 2 / (X : ℝ) := div_pos (by norm_num) hX0
        linarith
      have hh := Real.log_le_sub_one_of_pos hpos
      linarith
    linarith
  have hXD : (X : ℝ) * Real.log D ≤ 2 := by
    have h := mul_le_mul_of_nonneg_left hlogD (le_of_lt hX0)
    have he : (X : ℝ) * (2 / (X : ℝ)) = 2 := by
      rw [mul_comm, div_mul_eq_mul_div, mul_div_cancel_right₀ _ hXne]
    rwa [he] at h
  have h1 : Real.log (A * B * (X : ℝ) ^ 2 * Real.exp (X : ℝ) * D ^ X)
      = Real.log (A * B * (X : ℝ) ^ 2 * Real.exp (X : ℝ)) + Real.log (D ^ X) :=
    Real.log_mul (by positivity) (by positivity)
  have h2 : Real.log (A * B * (X : ℝ) ^ 2 * Real.exp (X : ℝ))
      = Real.log (A * B * (X : ℝ) ^ 2) + Real.log (Real.exp (X : ℝ)) :=
    Real.log_mul (by positivity) (by positivity)
  have h3 : Real.log (A * B * (X : ℝ) ^ 2) = Real.log (A * B) + Real.log ((X : ℝ) ^ 2) :=
    Real.log_mul (by positivity) (by positivity)
  have h4 : Real.log (A * B) = Real.log A + Real.log B :=
    Real.log_mul (by positivity) (by positivity)
  have hDx : Real.log (D ^ X) = (X : ℝ) * Real.log D := Real.log_pow D X
  have hX2 : Real.log ((X : ℝ) ^ 2) = 2 * Real.log (X : ℝ) := Real.log_pow (X : ℝ) 2
  have hexpX : Real.log (Real.exp (X : ℝ)) = (X : ℝ) := Real.log_exp (X : ℝ)
  have hK : Real.log (A * B * (X : ℝ) ^ 2 * Real.exp (X : ℝ) * D ^ X)
      = Real.log A + Real.log B + 2 * Real.log (X : ℝ) + (X : ℝ) + (X : ℝ) * Real.log D := by
    rw [h1, h2, h3, h4, hDx, hX2, hexpX]
  rw [hK]
  linarith

/-- BW `(25)` in the power form needed for the even step of the Kummer descent: for `X ≥ 2` even,
`l` odd with `|l| ≤ X`, `‖z − l‖ = 1/3`, `X + 2 ≤ R` and `|x| ≤ X + 2`, the `(Tp+1)`-st power of
`B'(x;X)` is bounded by that of `B'(z;X)` times `exp((Tp+1)(X + 2 log X + 3))`. -/
private lemma bprodOdd_ratio_pow_le (R : ℝ) (X Tp : ℕ) (l : ℤ) (z : ℂ) (x : ℝ)
    (hX : 2 ≤ X) (hXe : Even X) (hXR2 : (X : ℝ) + 2 ≤ R)
    (hlo : Odd l) (hl : |l| ≤ (X : ℤ)) (hz : ‖z - (l : ℂ)‖ = 1 / 3)
    (hx : |x| ≤ (X : ℝ) + 2) :
    ‖bprodOdd R X (x : ℂ) ^ (Tp + 1)‖ ≤ ‖bprodOdd R X z ^ (Tp + 1)‖ *
      Real.exp (((Tp : ℝ) + 1) * ((X : ℝ) + 2 * Real.log (X : ℝ) + 3)) := by
  have hXR : (X : ℝ) + 1 / 3 ≤ R := by linarith
  have hxR : |x| ≤ R := le_trans hx hXR2
  have h25 := even_step_Y_bprod_ratio25 R (1 / 3) (by norm_num) (by norm_num) X hX hXe hXR l hlo hl z hz x hxR
  set K : ℝ := (4 * Real.pi * (1 / 3))⁻¹ * (1 - (1 / 3) / 2)⁻¹ ^ 2 * (X : ℝ) ^ 2 *
      Real.exp (X : ℝ) * (max 1 (|x| / (X : ℝ))) ^ X with hK
  have hKpos : 0 < K := by
    rw [hK]
    have := Real.pi_pos
    positivity
  have hKpow : K ^ (Tp + 1) = Real.exp (((Tp : ℝ) + 1) * Real.log K) := by
    have h1 : ((Tp + 1 : ℕ) : ℝ) = (Tp : ℝ) + 1 := by push_cast; ring
    conv_lhs => rw [show K = Real.exp (Real.log K) from (Real.exp_log hKpos).symm]
    rw [← Real.exp_nat_mul, h1]
  have hKle : K ^ (Tp + 1) ≤
      Real.exp (((Tp : ℝ) + 1) * ((X : ℝ) + 2 * Real.log (X : ℝ) + 3)) := by
    rw [hKpow, Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left (evY_arith hX hx) (by positivity)
  have hpow : ‖bprodOdd R X (x : ℂ) ^ (Tp + 1)‖ ≤ ‖bprodOdd R X z ^ (Tp + 1)‖ * K ^ (Tp + 1) := by
    rw [norm_pow, norm_pow]
    have hp := pow_le_pow_left₀ (norm_nonneg _) h25 (Tp + 1)
    rwa [mul_pow] at hp
  calc ‖bprodOdd R X (x : ℂ) ^ (Tp + 1)‖
      ≤ ‖bprodOdd R X z ^ (Tp + 1)‖ * K ^ (Tp + 1) := hpow
    _ ≤ ‖bprodOdd R X z ^ (Tp + 1)‖ *
          Real.exp (((Tp : ℝ) + 1) * ((X : ℝ) + 2 * Real.log (X : ℝ) + 3)) :=
        mul_le_mul_of_nonneg_left hKle (norm_nonneg _)

/-- `(25)` combined with the definition of `evY`: for `l` odd with `|l| ≤ X`, `z` on `C_l`
(`‖z−l‖ = η = 1/3`) and `|s| ≤ X+2`, one has
`‖B'(s;X)‖^{T'+1} ≤ ‖B'(z;X)‖^{T'+1}·exp(evY)`. Indeed `(25)` gives
`‖B'(s;X)‖ ≤ ‖B'(z;X)‖·(4πη)^{-1}(1−η/2)^{-2}X²e^X(max(1,|s|/X))^X`, with
`(max(1,|s|/X))^X ≤ (1+2/X)^X ≤ e^2` (from `1+u ≤ e^u`), and then raising to the power `T'+1` and
using `log((4πη)^{-1}) + 2log(1−η/2)^{-1} + 2 ≤ 1 ≤ 3` gives `exp(evY)` with
`evY = (T'+1)(X + 2log X + 3)`. -/
theorem even_step_Y_ratio_le_exp_evY {r : ℕ} (hr : 2 ≤ r) {d h J : ℕ} {σ : Fin r → ℝ} {sz : ℝ}
    {l : ℤ} {z : ℂ} (hlo : Odd l) (hlX : |l| ≤ (evX r J (pS r d h : ℝ) : ℤ))
    (hz : ‖z - (l : ℂ)‖ = 1 / 3) (hsz : |sz| ≤ (evX r J (pS r d h : ℝ) : ℝ) + 2)
    (hS : 1 ≤ (pS r d h : ℝ)) :
    ‖bprodOdd (evR r J (pS r d h : ℝ)) (evX r J (pS r d h : ℝ)) (sz : ℂ) ^
        (evTp r J (pT r d σ : ℝ) + 1)‖
      ≤ ‖bprodOdd (evR r J (pS r d h : ℝ)) (evX r J (pS r d h : ℝ)) z ^
        (evTp r J (pT r d σ : ℝ) + 1)‖ * Real.exp (evY r d h σ J) := by
  have hpx : 0 < pxi r := pxi_pos_local hr
  have hpxle : pxi r ≤ 1 := pxi_le_one_local r
  have hxiinv : (1 : ℝ) ≤ pxi r ^ (-((r * J : ℕ) : ℤ)) := by
    rw [zpow_neg, zpow_natCast]
    exact (one_le_inv₀ (pow_pos hpx (r * J))).mpr (pow_le_one₀ (le_of_lt hpx) hpxle)
  have hP1 : 1 ≤ evSP r J (pS r d h : ℝ) := by
    rw [evSP]
    apply Nat.le_floor
    have hxiinv0 : (0 : ℝ) ≤ pxi r ^ (-((r * J : ℕ) : ℤ)) := le_trans (by norm_num) hxiinv
    have hmul : (1 : ℝ) ≤ pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ) := by
      have h := mul_le_mul hxiinv hS (by norm_num : (0 : ℝ) ≤ 1) hxiinv0
      simpa using h
    exact le_trans (by norm_num : ((1 : ℕ) : ℝ) ≤ 2)
      (by
        have h := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 2)
        simpa using h)
  have hP1r : (1 : ℝ) ≤ (evSP r J (pS r d h : ℝ) : ℝ) := by exact_mod_cast hP1
  have hX2 : 2 ≤ evX r J (pS r d h : ℝ) := by rw [evX]; omega
  have hXe : Even (evX r J (pS r d h : ℝ)) := by rw [evX]; exact even_two_mul _
  have hXR2 : (evX r J (pS r d h : ℝ) : ℝ) + 2 ≤ evR r J (pS r d h : ℝ) := by
    rw [evX, evR]; push_cast; linarith
  have hszR : |sz| ≤ (evX r J (pS r d h : ℝ) : ℝ) + 2 := hsz
  have := bprodOdd_ratio_pow_le (evR r J (pS r d h : ℝ)) (evX r J (pS r d h : ℝ))
    (evTp r J (pT r d σ : ℝ)) l z sz hX2 hXe hXR2 hlo hlX hz hszR
  simpa only [evY, Nat.cast_add, Nat.cast_one] using this


/-- The `Y`-hypothesis of `extrap_core` in the even step in the `Finset`-product form used by the
assembly: `(25)` for the lacunary Blaschke product `B'(·;X)` at the odd points `|l| ≤ X` and `z` on
`C_l` (`‖z−l‖ = η = 1/3`), with `X = 2S'`, `R = 7.2S'`, `T' = ⌊(1−ξ)ξ^rT^{(J)}⌋`,
`Y = (T'+1)(X + 2logX + 3)`. -/
theorem even_step_Y {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (s : ℤ)
    (hs : ((|s| : ℤ) : ℝ) ≤ 4 * SJ K r b v J) :
    ∀ l ∈ (Finset.Icc (-(((evX r J (acS K r b v)) : ℕ) : ℤ)) ((evX r J (acS K r b v)) : ℕ)).filter Odd,
      ∀ z : ℂ, ‖z - (l : ℂ)‖ = 1 / 3 →
        ‖∏ l' ∈ (Finset.Icc (-(((evX r J (acS K r b v)) : ℕ) : ℤ)) ((evX r J (acS K r b v)) : ℕ)).filter Odd,
            bfac (evR r J (acS K r b v)) l' (s : ℂ) ^ (evTp r J (acT K σ) + 1)‖
          ≤ ‖∏ l' ∈ (Finset.Icc (-(((evX r J (acS K r b v)) : ℕ) : ℤ)) ((evX r J (acS K r b v)) : ℕ)).filter Odd,
            bfac (evR r J (acS K r b v)) l' z ^ (evTp r J (acT K σ) + 1)‖
            * Real.exp (evY r (dK K) (acH K b v) σ J) := by
  classical
  intro l hl z hz
  have hr : 2 ≤ r := H.hr
  have hd : 1 ≤ dK K := Module.finrank_pos
  have h19 : 19 ≤ acH K b v := (acH_lower H).1
  -- `S = pS r (dK K) (acH K b v) ≥ 1`.
  have hS1 : (1 : ℝ) ≤ (pS r (dK K) (acH K b v) : ℝ) := by
    exact_mod_cast even_step_Y_one_le_pS (by omega : 1 ≤ r) hd (by omega : 1 ≤ acH K b v)
  -- `Odd l` and `|l| ≤ X` from membership in the filtered `Icc`.
  have hlo : Odd l := (Finset.mem_filter.mp hl).2
  have hmem := (Finset.mem_filter.mp hl).1
  rw [Finset.mem_Icc] at hmem
  have hlX : |l| ≤ (evX r J (pS r (dK K) (acH K b v) : ℝ) : ℤ) := by
    rw [abs_le]
    exact hmem
  -- `|s| ≤ 4S^{(J)} ≤ X + 2`.
  have hsX : |(((s : ℤ) : ℝ))| ≤ (evX r J (pS r (dK K) (acH K b v) : ℝ) : ℝ) + 2 := by
    rw [← Int.cast_abs]
    refine le_trans ?_ (even_step_Y_four_SJ_le_X_add_two (r := r) (J := J)
      (S := (pS r (dK K) (acH K b v) : ℝ)))
    simpa only [SJ, acS] using hs
  -- Rewrite the two `Finset`-products as powers of the lacunary Blaschke product `B'`.
  have hprodL :
      (∏ l' ∈ (Finset.Icc (-(((evX r J (acS K r b v)) : ℕ) : ℤ))
            ((evX r J (acS K r b v)) : ℕ)).filter Odd,
          bfac (evR r J (acS K r b v)) l' (s : ℂ) ^ (evTp r J (acT K σ) + 1))
        = bprodOdd (evR r J (acS K r b v)) (evX r J (acS K r b v)) (s : ℂ)
            ^ (evTp r J (acT K σ) + 1) := by
    rw [Finset.prod_pow]; rfl
  have hprodR :
      (∏ l' ∈ (Finset.Icc (-(((evX r J (acS K r b v)) : ℕ) : ℤ))
            ((evX r J (acS K r b v)) : ℕ)).filter Odd,
          bfac (evR r J (acS K r b v)) l' z ^ (evTp r J (acT K σ) + 1))
        = bprodOdd (evR r J (acS K r b v)) (evX r J (acS K r b v)) z
            ^ (evTp r J (acT K σ) + 1) := by
    rw [Finset.prod_pow]; rfl
  rw [hprodL, hprodR]
  have hchild := even_step_Y_ratio_le_exp_evY (r := r) hr (d := dK K) (h := acH K b v) (J := J)
    (σ := σ) (sz := ((s : ℤ) : ℝ)) hlo hlX hz hsX hS1
  have hcast : ((((s : ℤ) : ℝ)) : ℂ) = (s : ℂ) := by simp
  rw [hcast] at hchild
  exact hchild

end Work.BW
