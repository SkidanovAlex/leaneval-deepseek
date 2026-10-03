import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.ModEq
import Mathlib.RingTheory.Int.Basic

namespace Commons.NumberTheory.FriedlanderIwaniec

lemma nat_sq_neg_one_lift_unique {p e : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) (he : 1 ≤ e)
    {x y : ℕ} (hx : x < p ^ (e + 1)) (hy : y < p ^ (e + 1))
    (hxroot : p ^ (e + 1) ∣ x ^ 2 + 1) (hyroot : p ^ (e + 1) ∣ y ^ 2 + 1)
    (hproj : x % p ^ e = y % p ^ e) : x = y := by
  -- work in ℤ
  have hp_pos : (0:ℤ) < (p:ℤ) := by exact_mod_cast hp.pos
  have hpZ : Prime (p:ℤ) := by
    rw [Int.prime_iff_natAbs_prime]
    simpa using hp
  -- roots, cast to ℤ
  have hrootx : (p:ℤ)^(e+1) ∣ (x:ℤ)^2 + 1 := by
    have h : (((p ^ (e+1) : ℕ)) : ℤ) ∣ (x:ℤ)^2 + 1 := by exact_mod_cast hxroot
    simpa [Nat.cast_pow] using h
  have hrooty : (p:ℤ)^(e+1) ∣ (y:ℤ)^2 + 1 := by
    have h : (((p ^ (e+1) : ℕ)) : ℤ) ∣ (y:ℤ)^2 + 1 := by exact_mod_cast hyroot
    simpa [Nat.cast_pow] using h
  -- projection congruence, cast to ℤ
  have hdiv : (p:ℤ)^e ∣ (x:ℤ) - (y:ℤ) := by
    have h : (((p ^ e : ℕ)) : ℤ) ∣ (x:ℤ) - (y:ℤ) :=
      Nat.modEq_iff_dvd.mp (show y ≡ x [MOD p ^ e] from hproj.symm)
    simpa [Nat.cast_pow] using h
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (x:ℤ) - (y:ℤ) = (p:ℤ)^e * k := hdiv
  -- bounds
  have hbnd : |(x:ℤ) - (y:ℤ)| < (p:ℤ)^(e+1) := by
    have hX : (x:ℤ) < (p:ℤ)^(e+1) := by
      have h := (show (x:ℤ) < (((p^(e+1)) : ℕ) : ℤ) from by exact_mod_cast hx)
      simpa [Nat.cast_pow] using h
    have hY : (y:ℤ) < (p:ℤ)^(e+1) := by
      have h := (show (y:ℤ) < (((p^(e+1)) : ℕ) : ℤ) from by exact_mod_cast hy)
      simpa [Nat.cast_pow] using h
    have hXnn : (0:ℤ) ≤ (x:ℤ) := Int.natCast_nonneg x
    have hYnn : (0:ℤ) ≤ (y:ℤ) := Int.natCast_nonneg y
    rw [abs_lt]
    constructor <;> linarith
  -- divisibility chain
  have hfact : ((x:ℤ)^2 + 1) - ((y:ℤ)^2 + 1) = (p:ℤ)^e * (k * ((x:ℤ)+(y:ℤ))) := by
    have h1 : ((x:ℤ)^2 + 1) - ((y:ℤ)^2 + 1) = ((x:ℤ) - (y:ℤ)) * ((x:ℤ)+(y:ℤ)) := by ring
    rw [h1, hk]; ring
  have hdiff : (p:ℤ)^(e+1) ∣ (p:ℤ)^e * (k * ((x:ℤ)+(y:ℤ))) := by
    rw [← hfact]; exact Int.dvd_sub hrootx hrooty
  have hdiff2 : (p:ℤ)^e * (p:ℤ) ∣ (p:ℤ)^e * (k * ((x:ℤ)+(y:ℤ))) := by
    rwa [pow_succ] at hdiff
  have hPepow_ne : (p:ℤ)^e ≠ 0 := pow_ne_zero e (by exact_mod_cast hp.ne_zero)
  have hPk : (p:ℤ) ∣ k * ((x:ℤ)+(y:ℤ)) := (Int.mul_dvd_mul_iff_left hPepow_ne).mp hdiff2
  -- auxiliary: p does not divide 2
  have hpge3 : 3 ≤ p := by
    have hp2le : 2 ≤ p := hp.two_le
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hpodd
    · omega
  have hP2 : ¬ ((p:ℤ) ∣ (2:ℤ)) := by
    intro h
    have hp2 : p ∣ 2 := by
      have := (Int.natCast_dvd (m := p) (n := (2:ℤ))).mp h
      simpa using this
    have := Nat.le_of_dvd (by norm_num) hp2
    omega
  -- auxiliary: p does not divide y
  have hPy : ¬ ((p:ℤ) ∣ (y:ℤ)) := by
    intro h
    have hPe : (p:ℤ) ∣ (p:ℤ)^(e+1) := ⟨(p:ℤ)^e, pow_succ' (p:ℤ) e⟩
    have hy1 : (p:ℤ) ∣ (y:ℤ)^2 + 1 := dvd_trans hPe hrooty
    have hy2 : (p:ℤ) ∣ (y:ℤ)^2 := by
      have := dvd_mul_of_dvd_left h (y:ℤ)
      simpa [pow_two] using this
    have h1 : (p:ℤ) ∣ 1 := by
      have := Int.dvd_sub hy1 hy2
      simpa using this
    exact hpZ.not_dvd_one h1
  -- p does not divide x + y
  have hsum_not : ¬ ((p:ℤ) ∣ (x:ℤ) + (y:ℤ)) := by
    intro hsum
    have hPdvdPe : (p:ℤ) ∣ (p:ℤ)^e := by
      have := pow_dvd_pow (p:ℤ) he
      simpa using this
    have hPXY : (p:ℤ) ∣ (x:ℤ) - (y:ℤ) := by
      have := dvd_mul_of_dvd_left hPdvdPe k
      rwa [← hk] at this
    have h2Y : (p:ℤ) ∣ 2 * (y:ℤ) := by
      have := Int.dvd_sub hsum hPXY
      rwa [show (x:ℤ) + (y:ℤ) - ((x:ℤ) - (y:ℤ)) = 2 * (y:ℤ) by ring] at this
    rcases hpZ.dvd_or_dvd h2Y with h | h
    · exact hP2 h
    · exact hPy h
  have hPk_dvd : (p:ℤ) ∣ k := by
    rcases hpZ.dvd_or_dvd hPk with h | h
    · exact h
    · exact absurd h hsum_not
  -- bound on |k|
  have hkabs : |k| < (p:ℤ) := by
    have hPe_pos : (0:ℤ) < (p:ℤ)^e := pow_pos hp_pos e
    have habs : |(x:ℤ) - (y:ℤ)| = (p:ℤ)^e * |k| := by
      rw [hk, abs_mul, abs_of_pos hPe_pos]
    have h1 : (p:ℤ)^e * |k| < (p:ℤ)^e * (p:ℤ) := by
      rw [← pow_succ, ← habs]; exact hbnd
    exact (Int.mul_lt_mul_left hPe_pos).mp h1
  have hk_nat_lt : k.natAbs < p := by
    have h : (k.natAbs : ℤ) < (p:ℤ) := by rw [Int.natCast_natAbs]; exact hkabs
    exact_mod_cast h
  have hdvd_nat : p ∣ k.natAbs := by
    have h := (Int.natAbs_dvd_natAbs (a := (p:ℤ)) (b := k)).mpr hPk_dvd
    simpa using h
  have hk0 : k = 0 := by
    have : k.natAbs = 0 := Nat.eq_zero_of_dvd_of_lt hdvd_nat hk_nat_lt
    exact Int.natAbs_eq_zero.mp this
  have hXY : (x:ℤ) = (y:ℤ) := by
    have : (x:ℤ) - (y:ℤ) = 0 := by rw [hk, hk0, mul_zero]
    linarith
  exact_mod_cast hXY

end Commons.NumberTheory.FriedlanderIwaniec