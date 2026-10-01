import Mathlib
import Submission.Work.LinnikBurgess.lfSmall.two_defs
import Submission.Work.LinnikBurgess.defect2_mul_Uval_sq

namespace Work.LinnikBurgess.lfSmall

open Polynomial

/-!
# The second transfer for `p = 2`

This file proves `two_transfer_d2`: on the support of Lemma A₂ (unit points `y` with
`2 ^ (m + nv - 1) ∣ N(y)`, `m = cubeLevel 2 e`, `N = critN a b` the Wronskian,
`nv = vcap 2 T (N'(y))`, `T = capLevel 2 e`), the capped `2`-adic valuation of the second defect
`D₂(y) = defect2 2 e a b y` equals `nv`.

The proof is the exact analogue of `Work.LinnikBurgess.bval_transfer` for the prime `2`:
the algebraic identity
`D₂(y)·U(y)² = −N'(y)·U(y) + N(y)·W(y)`  in `ZMod (2^e)` (`defect2_mul_Uval_sq`),
with `U(y) = Uval y a b` a unit modulo `2^e`, is read as an integral congruence and determines the
valuations.  The only difference from the odd-prime case is the weaker support condition
`2^(m + nv - 1) ∣ N(y)` (with `nv` the *capped* valuation of `N'`), which is handled in
`transfer_d2_core`.
-/

/-! ## Arithmetic of the levels at `p = 2` -/

lemma cubeLevel_two (e : ℕ) : cubeLevel 2 e = (e + 3) / 3 := by
  rw [cubeLevel]; simp

lemma capLevel_two (e : ℕ) : capLevel 2 e = e - 2 * ((e + 3) / 3) := by
  rw [capLevel, cubeLevel_two]

lemma one_le_cubeLevel_two (e : ℕ) : 1 ≤ cubeLevel 2 e := by
  rw [cubeLevel_two]
  have h := Nat.div_add_mod (e + 3) 3
  have h' := Nat.mod_lt (e + 3) (by norm_num : 0 < 3)
  omega

lemma cubeLevel_two_add_capLevel_two_le {e : ℕ} (he : 13 ≤ e) :
    cubeLevel 2 e + capLevel 2 e ≤ e := by
  rw [cubeLevel_two, capLevel_two]
  have h := Nat.div_add_mod (e + 3) 3
  have h' := Nat.mod_lt (e + 3) (by norm_num : 0 < 3)
  omega

lemma capLevel_two_add_one_le_cubeLevel_two {e : ℕ} (he : 13 ≤ e) :
    capLevel 2 e + 1 ≤ cubeLevel 2 e := by
  rw [cubeLevel_two, capLevel_two]
  have h := Nat.div_add_mod (e + 3) 3
  have h' := Nat.mod_lt (e + 3) (by norm_num : 0 < 3)
  omega

/-! ## A `p`-adic kit for `ℤ` -/

/-- `p ^ j` is coprime to an integer not divisible by `p`. -/
lemma isCoprime_pow_of_not_dvd {p : ℕ} [Fact p.Prime] {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) (j : ℕ) :
    IsCoprime ((p : ℤ) ^ j) u := by
  have hnat : ¬ p ∣ u.natAbs := fun h =>
    hu (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h))
  rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.Coprime.pow_left j ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hnat)

/-- Cancelling a factor coprime to `p` from a `p`-power divisibility. -/
lemma dvd_of_dvd_mul_of_not_dvd {p : ℕ} [Fact p.Prime] {j : ℕ} {A u : ℤ}
    (hu : ¬ (p : ℤ) ∣ u) (h : (p : ℤ) ^ j ∣ A * u) : (p : ℤ) ^ j ∣ A :=
  (isCoprime_pow_of_not_dvd hu j).dvd_of_dvd_mul_right h

/-- The same, with the coprime factor squared. -/
lemma dvd_of_dvd_mul_sq_of_not_dvd {p : ℕ} [Fact p.Prime] {j : ℕ} {A u : ℤ}
    (hu : ¬ (p : ℤ) ∣ u) (h : (p : ℤ) ^ j ∣ A * u ^ 2) : (p : ℤ) ^ j ∣ A := by
  have hcop : IsCoprime ((p : ℤ) ^ j) (u ^ 2) := (isCoprime_pow_of_not_dvd hu j).pow_right
  exact hcop.dvd_of_dvd_mul_right h

/-- The `p`-adic valuation of a nonzero integer, read off from a sharp divisibility. -/
lemma padicValInt_eq_of_dvd_not_dvd {p : ℕ} [Fact p.Prime] {z : ℤ} {k : ℕ}
    (h1 : ((p : ℤ) ^ k) ∣ z) (h2 : ¬ ((p : ℤ) ^ (k + 1)) ∣ z) : padicValInt p z = k := by
  have hz : z ≠ 0 := fun h => h2 (by rw [h]; exact dvd_zero _)
  have hge : k ≤ padicValInt p z := ((padicValInt_dvd_iff k z).mp h1).resolve_left hz
  have hle : padicValInt p z ≤ k := by
    by_contra hcon
    exact h2 ((padicValInt_dvd_iff (k + 1) z).mpr (Or.inr (by omega)))
  omega

/-- `vcap p T` of `|z|` in the `ℤ`-valued shape used below. -/
lemma vcap_natAbs_eq_ite {p T : ℕ} (z : ℤ) :
    vcap p T z.natAbs = if z = 0 then T else min (padicValInt p z) T := by
  rw [vcap]
  by_cases h : z = 0
  · subst h; simp
  · have h' : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr h
    rw [if_neg h', if_neg h]
    rfl

/-! ## The integral congruence form of `defect2_mul_Uval_sq` -/

/-- The identity `defect2_mul_Uval_sq`, read as an integral congruence modulo `p ^ e`. -/
theorem dvd_defect2_congr_two {p e : ℕ} [Fact p.Prime] (a b : Fin 3 → ℕ) {y : ℕ}
    (hy : UnitAt p y a b) :
    ((p : ℤ) ^ e) ∣ (defect2 p e a b y).val * (Uval y a b : ℤ) ^ 2
      + (critN a b).derivative.eval (y : ℤ) * (Uval y a b : ℤ)
      - (critN a b).eval (y : ℤ) * (Wval y a b : ℤ) := by
  have hpm : ((p : ℤ) ^ e) = ((p ^ e : ℕ) : ℤ) := by push_cast; ring
  have key : ((((defect2 p e a b y).val * (Uval y a b : ℤ) ^ 2
      + (critN a b).derivative.eval (y : ℤ) * (Uval y a b : ℤ)
      - (critN a b).eval (y : ℤ) * (Wval y a b : ℤ) : ℤ)) : ZMod (p ^ e)) = 0 := by
    have h := defect2_mul_Uval_sq (p := p) (e := e) a b hy
    push_cast
    rw [ZMod.natCast_zmod_val]
    rw [h]
    ring
  rw [hpm, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact key

/-! ## `Uval` is coprime to `2` at a unit point -/

lemma not_dvd_Uval_two {y : ℕ} {a b : Fin 3 → ℕ} (hy : UnitAt 2 y a b) : ¬ 2 ∣ Uval y a b := by
  rw [Uval, sh3, sh3]
  intro h
  rcases Nat.prime_two.dvd_mul.mp h with h | h
  · rcases Nat.prime_two.dvd_mul.mp h with h | h
    · rcases Nat.prime_two.dvd_mul.mp h with h | h
      · exact (hy 0).1 h
      · exact (hy 1).1 h
    · exact (hy 2).1 h
  · rcases Nat.prime_two.dvd_mul.mp h with h | h
    · rcases Nat.prime_two.dvd_mul.mp h with h | h
      · exact (hy 0).2 h
      · exact (hy 1).2 h
    · exact (hy 2).2 h

/-! ## The valuation comparison (core) -/

/-- Abstract core: given the integral congruence
`p^e ∣ d₂ u² + n' u − n w`, with `u` coprime to `p`, `m + T ≤ e`, `T + 1 ≤ m`, and the support
condition `p^(m + nv − 1) ∣ n` where `nv = vcap p T |n'|`, the capped valuation of `d₂` is `nv`. -/
theorem transfer_d2_core {p : ℕ} [Fact p.Prime] {e m T nv : ℕ} {d2 u w nn nn' : ℤ}
    (hm : 1 ≤ m) (hmT : m + T ≤ e) (hTm : T + 1 ≤ m)
    (hnv : nv = vcap p T nn'.natAbs)
    (hcong : ((p : ℤ) ^ e) ∣ d2 * u ^ 2 + nn' * u - nn * w)
    (hu : ¬ (p : ℤ) ∣ u)
    (hnn : ((p : ℤ) ^ (m + nv - 1)) ∣ nn) :
    vcap p T d2.natAbs = nv := by
  rw [vcap_natAbs_eq_ite d2, hnv, vcap_natAbs_eq_ite nn']
  have hTe : T ≤ e := le_trans (Nat.le_add_left T m) hmT
  have hTle : T ≤ m + nv - 1 := by omega
  by_cases hd2 : d2 = 0
  · -- `d₂ = 0`: the cap `T` is reached
    rw [if_pos hd2]
    have hcong' : ((p : ℤ) ^ e) ∣ nn' * u - nn * w := by simpa [hd2] using hcong
    have hPTu : ((p : ℤ) ^ T) ∣ nn' * u := by
      have h1 : ((p : ℤ) ^ T) ∣ nn * w :=
        dvd_mul_of_dvd_left (dvd_trans (pow_dvd_pow _ hTle) hnn) w
      have h2 : ((p : ℤ) ^ T) ∣ nn' * u - nn * w :=
        dvd_trans (pow_dvd_pow _ hTe) hcong'
      have h3 : ((p : ℤ) ^ T) ∣ (nn' * u - nn * w) + nn * w := dvd_add h2 h1
      rwa [sub_add_cancel] at h3
    have hPT : ((p : ℤ) ^ T) ∣ nn' := dvd_of_dvd_mul_of_not_dvd hu hPTu
    by_cases hn' : nn' = 0
    · rw [if_pos hn']
    · rw [if_neg hn', min_eq_right (((padicValInt_dvd_iff T nn').mp hPT).resolve_left hn')]
  · -- `d₂ ≠ 0`
    rw [if_neg hd2]
    rcases lt_or_ge (padicValInt p d2) T with hk | hk
    · -- `v_p(d₂) = k < T`: then `v_p(n') = k`
      rw [min_eq_left (le_of_lt hk)]
      have hke : padicValInt p d2 + 1 ≤ e := by omega
      have hks : padicValInt p d2 + 1 ≤ m + nv - 1 := by omega
      have hPd : ((p : ℤ) ^ padicValInt p d2) ∣ d2 := padicValInt_dvd d2
      have hnotPd : ¬ ((p : ℤ) ^ (padicValInt p d2 + 1)) ∣ d2 := fun h =>
        ((padicValInt_dvd_iff (padicValInt p d2 + 1) d2).mp h).elim hd2 (by omega)
      have h1 : ((p : ℤ) ^ padicValInt p d2) ∣ nn' * u - nn * w := by
        have hc : ((p : ℤ) ^ padicValInt p d2) ∣ d2 * u ^ 2 + nn' * u - nn * w :=
          dvd_trans (pow_dvd_pow _ (by omega)) hcong
        have hp2 : ((p : ℤ) ^ padicValInt p d2) ∣ d2 * u ^ 2 := dvd_mul_of_dvd_left hPd _
        have h := dvd_sub hc hp2
        have heq : d2 * u ^ 2 + nn' * u - nn * w - d2 * u ^ 2 = nn' * u - nn * w := by ring
        rwa [heq] at h
      have h2 : ((p : ℤ) ^ (padicValInt p d2 + 1)) ∣ nn * w :=
        dvd_mul_of_dvd_left (dvd_trans (pow_dvd_pow _ hks) hnn) w
      have hPku : ((p : ℤ) ^ padicValInt p d2) ∣ nn' * u := by
        have hw : ((p : ℤ) ^ padicValInt p d2) ∣ nn * w :=
          dvd_trans (pow_dvd_pow _ (by omega)) h2
        have h := dvd_add h1 hw
        have heq : (nn' * u - nn * w) + nn * w = nn' * u := by ring
        rwa [heq] at h
      have hnotPku : ¬ ((p : ℤ) ^ (padicValInt p d2 + 1)) ∣ nn' * u := by
        intro hbad
        have h3 : ((p : ℤ) ^ (padicValInt p d2 + 1)) ∣ nn' * u - nn * w := dvd_sub hbad h2
        have hc : ((p : ℤ) ^ (padicValInt p d2 + 1)) ∣ d2 * u ^ 2 + nn' * u - nn * w :=
          dvd_trans (pow_dvd_pow _ hke) hcong
        have h4 : ((p : ℤ) ^ (padicValInt p d2 + 1)) ∣ d2 * u ^ 2 := by
          have h := dvd_sub hc h3
          have heq : d2 * u ^ 2 + nn' * u - nn * w - (nn' * u - nn * w) = d2 * u ^ 2 := by ring
          rwa [heq] at h
        exact hnotPd (dvd_of_dvd_mul_sq_of_not_dvd hu h4)
      have hPnn' : ((p : ℤ) ^ padicValInt p d2) ∣ nn' := dvd_of_dvd_mul_of_not_dvd hu hPku
      have hnotPnn' : ¬ ((p : ℤ) ^ (padicValInt p d2 + 1)) ∣ nn' :=
        fun h => hnotPku (dvd_mul_of_dvd_left h u)
      have hvnn' : padicValInt p nn' = padicValInt p d2 :=
        padicValInt_eq_of_dvd_not_dvd hPnn' hnotPnn'
      rw [if_neg (fun hn => hnotPnn' (by rw [hn]; exact dvd_zero _)), hvnn',
        min_eq_left (le_of_lt hk)]
    · -- `T ≤ v_p(d₂)`: then `v_p(n') ≥ T`
      rw [min_eq_right hk]
      have hPT : ((p : ℤ) ^ T) ∣ nn' := by
        have h1 : ((p : ℤ) ^ T) ∣ nn * w :=
          dvd_mul_of_dvd_left (dvd_trans (pow_dvd_pow _ hTle) hnn) w
        have h2 : ((p : ℤ) ^ T) ∣ d2 * u ^ 2 :=
          dvd_mul_of_dvd_left ((padicValInt_dvd_iff T d2).mpr (Or.inr hk)) _
        have h3 : ((p : ℤ) ^ T) ∣ d2 * u ^ 2 + nn' * u - nn * w :=
          dvd_trans (pow_dvd_pow _ hTe) hcong
        have h4 : ((p : ℤ) ^ T) ∣ nn' * u := by
          have h := dvd_add (dvd_sub h3 h2) h1
          have heq : d2 * u ^ 2 + nn' * u - nn * w - d2 * u ^ 2 + nn * w = nn' * u := by ring
          rwa [heq] at h
        exact dvd_of_dvd_mul_of_not_dvd hu h4
      by_cases hn' : nn' = 0
      · rw [if_pos hn']
      · rw [if_neg hn', min_eq_right (((padicValInt_dvd_iff T nn').mp hPT).resolve_left hn')]

/-! ## The transfer on the support -/

theorem two_transfer_d2 {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) {y : ℕ} (hy : UnitAt 2 y a b)
    (hN : ((2 ^ (cubeLevel 2 e + nv e a b y - 1) : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ)) :
    vcap 2 (capLevel 2 e) (defect2 2 e a b y).val = nv e a b y := by
  have hu : ¬ (2 : ℤ) ∣ (Uval y a b : ℤ) := by
    exact_mod_cast not_dvd_Uval_two hy
  have hN' : ((2 : ℤ) ^ (cubeLevel 2 e + nv e a b y - 1)) ∣ (critN a b).eval (y : ℤ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hN
  have hcore := transfer_d2_core (p := 2) (e := e) (m := cubeLevel 2 e) (T := capLevel 2 e)
    (nv := nv e a b y) (d2 := (((defect2 2 e a b y).val : ℕ) : ℤ))
    (u := (Uval y a b : ℤ)) (w := (Wval y a b : ℤ))
    (nn := (critN a b).eval (y : ℤ)) (nn' := (critN a b).derivative.eval (y : ℤ))
    (one_le_cubeLevel_two e) (cubeLevel_two_add_capLevel_two_le he)
    (capLevel_two_add_one_le_cubeLevel_two he) rfl
    (dvd_defect2_congr_two (p := 2) (e := e) a b hy) hu hN'
  simpa only [Int.natAbs_natCast] using hcore

end Work.LinnikBurgess.lfSmall
