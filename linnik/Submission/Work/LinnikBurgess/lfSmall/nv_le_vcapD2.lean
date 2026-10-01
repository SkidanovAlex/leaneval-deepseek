import Mathlib
import Submission.Work.LinnikBurgess.lfSmall.two_defs
import Submission.Work.LinnikBurgess.defect2_mul_Uval_sq
import Submission.Work.LinnikBurgess.lfSmall.two_transfer_d2

namespace Work.LinnikBurgess.lfSmall

open Work.LinnikBurgess

/-- `vcap p T x ≤ T` for every `x`. -/
private lemma vcap_le_self (p T x : ℕ) : vcap p T x ≤ T := by
  rw [vcap]; split <;> simp

/-- Abstract `p`-adic core.  Given the integral congruence `p^e ∣ d₂u² + n'u − n w` with `u`
coprime to `p`, `m + T ≤ e`, `2 ≤ m`, and the support condition
`p^(m + vcap p T d₂ − 1) ∣ n`, the capped valuation of `n'` is at most that of `d₂`. -/
private theorem vcap_le_vcapD2_aux {p : ℕ} [Fact p.Prime] {e m T : ℕ} {d2 u w n nn' : ℤ}
    (hm : 2 ≤ m) (hmT : m + T ≤ e) (hTm : T + 1 ≤ m)
    (hcong : ((p : ℤ) ^ e) ∣ d2 * u ^ 2 + nn' * u - n * w)
    (hu : ¬ (p : ℤ) ∣ u)
    (hnn : ((p : ℤ) ^ (m + vcap p T d2.natAbs - 1)) ∣ n) :
    vcap p T nn'.natAbs ≤ vcap p T d2.natAbs := by
  have hd2val : vcap p T d2.natAbs
      = if d2 = 0 then T else min (padicValInt p d2) T := vcap_natAbs_eq_ite d2
  rcases eq_or_ne d2 0 with hd2 | hd2
  · rw [hd2val, if_pos hd2]
    exact vcap_le_self p T nn'.natAbs
  · rw [hd2val, if_neg hd2]
    by_cases hTk : T ≤ padicValInt p d2
    · rw [min_eq_right hTk]
      exact vcap_le_self p T nn'.natAbs
    · have hkT : padicValInt p d2 < T := not_le.mp hTk
      rw [min_eq_left (le_of_lt hkT)]
      have hvk : vcap p T d2.natAbs = padicValInt p d2 := by
        rw [hd2val, if_neg hd2, min_eq_left (le_of_lt hkT)]
      have hnnk : ((p : ℤ) ^ (m + padicValInt p d2 - 1)) ∣ n := by
        rw [hvk] at hnn; exact hnn
      have hTe : T ≤ e := le_trans (Nat.le_add_left T m) hmT
      have hke : padicValInt p d2 + 1 ≤ e := by omega
      have hkm : padicValInt p d2 + 1 ≤ m + padicValInt p d2 - 1 := by omega
      have hPd : ((p : ℤ) ^ padicValInt p d2) ∣ d2 := padicValInt_dvd d2
      have hnotPd : ¬ ((p : ℤ) ^ (padicValInt p d2 + 1)) ∣ d2 := fun h =>
        ((padicValInt_dvd_iff (padicValInt p d2 + 1) d2).mp h).elim hd2 (by omega)
      have hPn : ((p : ℤ) ^ (padicValInt p d2 + 1)) ∣ n :=
        dvd_trans (pow_dvd_pow _ hkm) hnnk
      have hPku : ((p : ℤ) ^ padicValInt p d2) ∣ nn' * u := by
        have h1 : ((p : ℤ) ^ padicValInt p d2) ∣ d2 * u ^ 2 :=
          dvd_mul_of_dvd_left hPd _
        have h3 : ((p : ℤ) ^ padicValInt p d2) ∣ d2 * u ^ 2 + nn' * u - n * w :=
          dvd_trans (pow_dvd_pow _ (by omega)) hcong
        have h2 : ((p : ℤ) ^ padicValInt p d2) ∣ n * w :=
          dvd_mul_of_dvd_left
            (dvd_trans
              (pow_dvd_pow _ (by omega : padicValInt p d2 ≤ padicValInt p d2 + 1)) hPn) w
        have h := dvd_add (dvd_sub h3 h1) h2
        have heq : (d2 * u ^ 2 + nn' * u - n * w) - d2 * u ^ 2 + n * w = nn' * u := by ring
        rwa [heq] at h
      have hPn' : ((p : ℤ) ^ padicValInt p d2) ∣ nn' := dvd_of_dvd_mul_of_not_dvd hu hPku
      have hnotPn' : ¬ ((p : ℤ) ^ (padicValInt p d2 + 1)) ∣ nn' := by
        intro hbad
        have hc : ((p : ℤ) ^ (padicValInt p d2 + 1)) ∣ d2 * u ^ 2 + nn' * u - n * w :=
          dvd_trans (pow_dvd_pow _ hke) hcong
        have h6 : ((p : ℤ) ^ (padicValInt p d2 + 1)) ∣ d2 * u ^ 2 := by
          have h := dvd_add (dvd_sub hc (dvd_mul_of_dvd_left hbad u))
            (dvd_mul_of_dvd_left hPn w)
          have heq : (d2 * u ^ 2 + nn' * u - n * w) - nn' * u + n * w = d2 * u ^ 2 := by ring
          rwa [heq] at h
        exact hnotPd (dvd_of_dvd_mul_sq_of_not_dvd hu h6)
      have hvn' : padicValInt p nn' = padicValInt p d2 :=
        padicValInt_eq_of_dvd_not_dvd hPn' hnotPn'
      have hn'ne : nn' ≠ 0 := fun h => hnotPn' (h ▸ dvd_zero _)
      rw [vcap_natAbs_eq_ite nn', if_neg hn'ne, hvn', min_eq_left (le_of_lt hkT)]

/-- **The capped derivative valuation is bounded by the capped second-defect valuation.**  At a
unit point `y` of `2` with `2 ^ (m + t − 1) ∣ N(y)` (`m = cubeLevel 2 e`, `N = critN a b`,
`t = vcap 2 T (defect2 2 e a b y)`, `T = capLevel 2 e`), the capped `2`-adic valuation of `N'(y)`
is at most `t`. -/
theorem nv_le_vcapD2 {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) {y : ℕ} (hy : UnitAt 2 y a b)
    (hN : ((2 ^ (cubeLevel 2 e + vcap 2 (capLevel 2 e) (defect2 2 e a b y).val - 1) : ℕ) : ℤ)
        ∣ (critN a b).eval (y : ℤ)) :
    nv e a b y ≤ vcap 2 (capLevel 2 e) (defect2 2 e a b y).val := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu : ¬ (2 : ℤ) ∣ (Uval y a b : ℤ) := by
    intro hd
    refine not_dvd_Uval_two hy ?_
    exact (Int.natCast_dvd_natCast (m := 2) (n := Uval y a b)).mp
      (by simpa only [Nat.cast_ofNat] using hd)
  have hm : 2 ≤ cubeLevel 2 e := by rw [cubeLevel_two]; omega
  have hmT : cubeLevel 2 e + capLevel 2 e ≤ e := cubeLevel_two_add_capLevel_two_le he
  have hTm : capLevel 2 e + 1 ≤ cubeLevel 2 e := capLevel_two_add_one_le_cubeLevel_two he
  have hnat : ((((defect2 2 e a b y).val : ℕ) : ℤ)).natAbs = (defect2 2 e a b y).val :=
    Int.natAbs_natCast _
  have hdiv : ((2 : ℤ) ^ (cubeLevel 2 e + vcap 2 (capLevel 2 e)
        ((((defect2 2 e a b y).val : ℕ) : ℤ)).natAbs - 1))
      ∣ (critN a b).eval (y : ℤ) := by
    have h : ((2 ^ (cubeLevel 2 e + vcap 2 (capLevel 2 e)
          ((((defect2 2 e a b y).val : ℕ) : ℤ)).natAbs - 1) : ℕ) : ℤ)
        ∣ (critN a b).eval (y : ℤ) := by
      rw [hnat]; exact hN
    rw [Nat.cast_pow] at h
    simpa only [Nat.cast_ofNat] using h
  have hmain := vcap_le_vcapD2_aux (p := 2) (e := e) (m := cubeLevel 2 e) (T := capLevel 2 e)
    (d2 := (((defect2 2 e a b y).val : ℕ) : ℤ)) (u := (Uval y a b : ℤ)) (w := (Wval y a b : ℤ))
    (n := (critN a b).eval (y : ℤ)) (nn' := (critN a b).derivative.eval (y : ℤ))
    hm hmT hTm (dvd_defect2_congr_two (p := 2) (e := e) a b hy) hu hdiv
  rw [hnat] at hmain
  show vcap 2 (capLevel 2 e) ((critN a b).derivative.eval (y : ℤ)).natAbs
      ≤ vcap 2 (capLevel 2 e) (defect2 2 e a b y).val
  exact hmain

end Work.LinnikBurgess.lfSmall
