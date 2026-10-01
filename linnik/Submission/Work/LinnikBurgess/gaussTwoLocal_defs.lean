import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Commons.NumberTheory.DirichletCharacter.criticalClass_gaussSum_primePow

/-!
# Local definitions for the two-term stationary phase (Lemma A / U2)
-/

open scoped BigOperators

set_option linter.style.haveILetI false

namespace Work.LinnikBurgess

/-- The two-term exponential `1 + p^m u + (p^m u)^2/2` in `ZMod (p^e)`. -/
noncomputable def Efun (p e m : ℕ) (u : ZMod (p ^ e)) : ZMod (p ^ e) :=
  1 + ((p ^ m : ℕ) : ZMod (p ^ e)) * u
    + (((p ^ m : ℕ) : ZMod (p ^ e)) * u) ^ 2 * (2 : ZMod (p ^ e))⁻¹

/-- `χ` composed with the two-term exponential. -/
noncomputable def psiFun (p e m : ℕ) (χ : DirichletCharacter ℂ (p ^ e)) (u : ZMod (p ^ e)) : ℂ :=
  χ (Efun p e m u)

/-- The quadratic Gauss sum over `ZMod (p ^ K)`: `∑ w, θ ^ ((α w + γ w^2).val)`. -/
noncomputable def gaussQuad (p K : ℕ) [NeZero (p ^ K)] (θ : ℂ) (α γ : ZMod (p ^ K)) : ℂ :=
  ∑ w : ZMod (p ^ K), θ ^ ((α * w + γ * w ^ 2).val)

lemma Efun_zero (p e m : ℕ) : Efun p e m 0 = 1 := by simp [Efun]

section Ring

variable {p e m : ℕ}

lemma Efun_add [Fact p.Prime] (hp2 : p ≠ 2) (h3 : e ≤ 3 * m)
    (u v : ZMod (p ^ e)) : Efun p e m (u + v) = Efun p e m u * Efun p e m v := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  set P : ZMod (p ^ e) := ((p ^ m : ℕ) : ZMod (p ^ e)) with hP
  have hP3 : P ^ 3 = 0 := by
    rw [hP, ← Nat.cast_pow, show (p ^ m) ^ 3 = p ^ (3 * m) by rw [← pow_mul]; ring,
      ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow p h3
  have h2p : Nat.Coprime 2 p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro h
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h1
    · exact hp.ne_one h1
    · exact hp2 h1
  have h2u : IsUnit (2 : ZMod (p ^ e)) :=
    (ZMod.isUnit_iff_coprime 2 (p ^ e)).mpr (h2p.pow_right e)
  set H : ZMod (p ^ e) := (2 : ZMod (p ^ e))⁻¹ with hH
  have h2 : (2 : ZMod (p ^ e)) * H = 1 := by rw [hH, ZMod.mul_inv_of_unit _ h2u]
  simp only [Efun]
  rw [← hP, ← hH]
  linear_combination ((P ^ 2 * u * v)) * h2
    + (-(u ^ 2 * v * H) - u * v ^ 2 * H - P * u ^ 2 * v ^ 2 * H ^ 2) * hP3

lemma Efun_neg [Fact p.Prime] (hp2 : p ≠ 2) (h3 : e ≤ 3 * m)
    (u : ZMod (p ^ e)) : Efun p e m (-u) = (Efun p e m u)⁻¹ := by
  have h := Efun_add (p := p) (e := e) (m := m) hp2 h3 (-u) u
  rw [neg_add_cancel, Efun_zero] at h
  have h' : Efun p e m u * Efun p e m (-u) = 1 := by rw [mul_comm]; exact h.symm
  exact (ZMod.inv_eq_of_mul_eq_one (p ^ e) (Efun p e m u) (Efun p e m (-u)) h').symm

lemma Efun_one_add [Fact p.Prime] (hp2 : p ≠ 2) (h3 : e ≤ 3 * m)
    (t : ZMod (p ^ e)) :
    Efun p e m (t - ((p ^ m : ℕ) : ZMod (p ^ e)) * t ^ 2 * (2 : ZMod (p ^ e))⁻¹)
      = 1 + ((p ^ m : ℕ) : ZMod (p ^ e)) * t := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  set P : ZMod (p ^ e) := ((p ^ m : ℕ) : ZMod (p ^ e)) with hP
  have hP3 : P ^ 3 = 0 := by
    rw [hP, ← Nat.cast_pow, show (p ^ m) ^ 3 = p ^ (3 * m) by rw [← pow_mul]; ring,
      ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow p h3
  have h2p : Nat.Coprime 2 p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro h
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h1
    · exact hp.ne_one h1
    · exact hp2 h1
  have h2u : IsUnit (2 : ZMod (p ^ e)) :=
    (ZMod.isUnit_iff_coprime 2 (p ^ e)).mpr (h2p.pow_right e)
  set H : ZMod (p ^ e) := (2 : ZMod (p ^ e))⁻¹ with hH
  have h2 : (2 : ZMod (p ^ e)) * H = 1 := by rw [hH, ZMod.mul_inv_of_unit _ h2u]
  simp only [Efun]
  rw [← hP, ← hH]
  linear_combination (-2 * t ^ 3 * H ^ 2 + P * t ^ 4 * H ^ 3) * hP3

lemma Efun_isUnit [Fact p.Prime] (hm : 1 ≤ m) (u : ZMod (p ^ e)) :
    IsUnit (Efun p e m u) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  set P : ZMod (p ^ e) := ((p ^ m : ℕ) : ZMod (p ^ e)) with hP
  have hPe : P ^ e = 0 := by
    rw [hP, ← Nat.cast_pow, show (p ^ m) ^ e = p ^ (m * e) by rw [← pow_mul],
      ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow p (by nlinarith)
  have hy : (P * u + (P * u) ^ 2 * (2 : ZMod (p ^ e))⁻¹) ^ e = 0 := by
    have h1 : P * u + (P * u) ^ 2 * (2 : ZMod (p ^ e))⁻¹
        = P * (u + P * u ^ 2 * (2 : ZMod (p ^ e))⁻¹) := by ring
    rw [h1, mul_pow, hPe, zero_mul]
  have hE : Efun p e m u = 1 + (P * u + (P * u) ^ 2 * (2 : ZMod (p ^ e))⁻¹) := by
    rw [Efun, ← hP]; ring
  rw [hE]
  exact IsNilpotent.isUnit_one_add ⟨e, hy⟩

end Ring

section Psi

variable {p e m : ℕ}

lemma psiFun_add [Fact p.Prime] (hp2 : p ≠ 2) (h3 : e ≤ 3 * m)
    (χ : DirichletCharacter ℂ (p ^ e)) (u v : ZMod (p ^ e)) :
    psiFun p e m χ (u + v) = psiFun p e m χ u * psiFun p e m χ v := by
  rw [psiFun, psiFun, psiFun, Efun_add hp2 h3, map_mul]

lemma psiFun_neg [Fact p.Prime] (hp2 : p ≠ 2) (h3 : e ≤ 3 * m)
    (χ : DirichletCharacter ℂ (p ^ e)) (u : ZMod (p ^ e)) :
    psiFun p e m χ (-u) = (psiFun p e m χ u)⁻¹ := by
  have h := psiFun_add (p := p) (e := e) (m := m) hp2 h3 χ (-u) u
  rw [neg_add_cancel] at h
  rw [psiFun, Efun_zero, map_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

/-- `conj (ψ u) = ψ (-u)` for `ψ = χ ∘ Efun`, since `Efun u` is a unit. -/
lemma psiFun_conj [Fact p.Prime] (hp2 : p ≠ 2) (h3 : e ≤ 3 * m) (hm : 1 ≤ m)
    (χ : DirichletCharacter ℂ (p ^ e)) (u : ZMod (p ^ e)) :
    (starRingEnd ℂ) (psiFun p e m χ u) = psiFun p e m χ (-u) := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e (Fact.out : p.Prime).ne_zero⟩
  rw [psiFun, psiFun,
    Commons.NumberTheory.DirichletCharacter.star_chi_eq_chi_inv χ _ (Efun_isUnit hm u),
    Efun_neg hp2 h3]

/-- The peeled phase is a power of `θ = ψ(1)`. -/
lemma psiFun_eq_theta_pow [Fact p.Prime] (hp2 : p ≠ 2) (h3 : e ≤ 3 * m)
    (χ : DirichletCharacter ℂ (p ^ e)) (u : ZMod (p ^ e)) :
    psiFun p e m χ u = (psiFun p e m χ 1) ^ u.val := by
  have hθ : ∀ n : ℕ,
      psiFun p e m χ ((n : ℕ) : ZMod (p ^ e)) = (psiFun p e m χ 1) ^ n := by
    intro n
    induction n with
    | zero => rw [Nat.cast_zero, psiFun, Efun_zero, map_one, pow_zero]
    | succ n ih =>
      rw [Nat.cast_succ, psiFun_add hp2 h3, ih, pow_succ]
  conv_lhs => rw [← ZMod.natCast_zmod_val u]
  exact hθ u.val

/-- `θ = ψ(1) = χ (1 + p^m + p^{2m}/2)` is a primitive `p^(e-m)`-th root of unity. -/
lemma psiFun_one_isPrimitiveRoot [Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (h3 : e ≤ 3 * m) (h2m : 2 * m ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive) :
    IsPrimitiveRoot (psiFun p e m χ 1) (p ^ (e - m)) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  have he : 2 ≤ e := by omega
  have hmp : m ≤ e := by omega
  set P : ZMod (p ^ e) := ((p ^ m : ℕ) : ZMod (p ^ e)) with hP
  have hE0 : Efun p e m (((p ^ (e - m) : ℕ)) : ZMod (p ^ e)) = 1 := by
    have hpm0 : P * ((p ^ (e - m) : ℕ) : ZMod (p ^ e)) = 0 := by
      rw [hP, ← Nat.cast_mul, ← pow_add, show m + (e - m) = e by omega, ZMod.natCast_self]
    simp only [Efun]; rw [← hP, hpm0]; ring
  have hE1 : Efun p e m (((p ^ (e - m - 1) : ℕ)) : ZMod (p ^ e))
      = ((1 + p ^ (e - 1) : ℕ) : ZMod (p ^ e)) := by
    have hpm : P * ((p ^ (e - m - 1) : ℕ) : ZMod (p ^ e))
        = ((p ^ (e - 1) : ℕ) : ZMod (p ^ e)) := by
      rw [hP, ← Nat.cast_mul, ← pow_add, show m + (e - m - 1) = e - 1 by omega]
    have hsq : (P * ((p ^ (e - m - 1) : ℕ) : ZMod (p ^ e))) ^ 2 * (2 : ZMod (p ^ e))⁻¹ = 0 := by
      have hz : (((p ^ ((e - 1) * 2)) : ℕ) : ZMod (p ^ e)) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]; exact pow_dvd_pow p (by omega)
      rw [hpm, ← Nat.cast_pow, show (p ^ (e - 1)) ^ 2 = p ^ ((e - 1) * 2) by rw [← pow_mul],
        hz, zero_mul]
    simp only [Efun]; rw [← hP, hsq, add_zero, hpm]; push_cast; ring
  have hval1 : (psiFun p e m χ 1) ^ (p ^ (e - m))
      = psiFun p e m χ (((p ^ (e - m) : ℕ)) : ZMod (p ^ e)) := by
    rw [psiFun_eq_theta_pow hp2 h3 χ (((p ^ (e - m) : ℕ)) : ZMod (p ^ e)), ZMod.val_natCast,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right hp.one_lt (by omega))]
  have hval2 : (psiFun p e m χ 1) ^ (p ^ (e - m - 1))
      = psiFun p e m χ (((p ^ (e - m - 1) : ℕ)) : ZMod (p ^ e)) := by
    rw [psiFun_eq_theta_pow hp2 h3 χ (((p ^ (e - m - 1) : ℕ)) : ZMod (p ^ e)), ZMod.val_natCast,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right hp.one_lt (by omega))]
  have h1 : (psiFun p e m χ 1) ^ (p ^ (e - m)) = 1 := by
    rw [hval1, psiFun, hE0, map_one]
  have h2 : (psiFun p e m χ 1) ^ (p ^ (e - m - 1)) ≠ 1 := by
    rw [hval2, psiFun, hE1]
    exact (Commons.NumberTheory.DirichletCharacter.chi_one_add_primePow_isPrimitiveRoot
      p e hp2 he χ hχ).ne_one hp.one_lt
  refine IsPrimitiveRoot.iff_orderOf.mpr ?_
  have hdiv : orderOf (psiFun p e m χ 1) ∣ p ^ (e - m) :=
    orderOf_dvd_iff_pow_eq_one.mpr h1
  obtain ⟨k, hkle, hk⟩ := (Nat.dvd_prime_pow hp).mp hdiv
  have hk_eq : k = e - m := by
    by_contra hne
    have hlt : k < e - m := lt_of_le_of_ne hkle hne
    exact h2 (orderOf_dvd_iff_pow_eq_one.mp (by rw [hk]; exact pow_dvd_pow p (by omega)))
  rw [hk_eq] at hk
  exact hk

end Psi

end Work.LinnikBurgess
