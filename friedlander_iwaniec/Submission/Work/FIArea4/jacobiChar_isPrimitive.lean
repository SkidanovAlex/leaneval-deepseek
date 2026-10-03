import Mathlib
import Submission.Work.FIArea4.JacobiChar

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **A unit of `ZMod m` on which the Jacobi character is `-1`, while its image under
`ZMod.unitsMap` is trivial.**

`m` squarefree and odd, `p` a prime divisor of `m`: the Chinese remainder theorem produces
`k ≡ 1 (mod m/p)`, `k ≡ v (mod p)` where `v` is a quadratic nonresidue mod `p`; then `k` is a
unit mod `m` and `J(k | m) = J(k | p) J(k | m/p) = (-1) · 1 = -1`. -/
private lemma exists_unit_unitsMap_eq_one_and_char_eq_neg_one {m p : ℕ} [NeZero m]
    (hsq : Squarefree m) (hodd : Odd m) (hp : p.Prime) (hpm : p ∣ m) (hd : m / p ∣ m) :
    ∃ u : (ZMod m)ˣ, ZMod.unitsMap hd u = 1 ∧ jacobiChar m (u : ZMod m) = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hm_pos : 0 < m := Nat.pos_of_neZero m
  have hp_le_m : p ≤ m := Nat.le_of_dvd hm_pos hpm
  have hdiv_pos : 0 < m / p := Nat.div_pos hp_le_m hp.pos
  have hdiv_ne_zero : m / p ≠ 0 := hdiv_pos.ne'
  -- `p` is odd, so the quadratic character mod `p` is nontrivial
  have hp_ne_two : p ≠ 2 := by
    intro h
    subst h
    have : Even m := even_iff_two_dvd.mpr hpm
    exact Nat.not_even_iff_odd.mpr hodd this
  have hF : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; exact hp_ne_two
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' (F := ZMod p) hF
  -- `v` is the representative of the quadratic nonresidue `a`
  set v : ℕ := (a : ZMod p).val with hv
  have hv_cast : ((v : ℕ) : ZMod p) = (a : ZMod p) := by
    rw [hv]; exact ZMod.natCast_zmod_val (a : ZMod p)
  have hJp : jacobiSym (v : ℤ) p = -1 := by
    have hleg : legendreSym p (v : ℤ) = -1 := by
      show quadraticChar (ZMod p) ((v : ℤ) : ZMod p) = -1
      rw [Int.cast_natCast, hv_cast]; exact ha
    rwa [jacobiSym.legendreSym.to_jacobiSym p (v : ℤ)] at hleg
  -- `m / p` and `p` are coprime because `m` is squarefree
  have hcop_np : Nat.Coprime (m / p) p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hpdvd
    have hpp : p * p ∣ m := by
      rw [← Nat.mul_div_cancel' hpm]
      exact mul_dvd_mul_left p hpdvd
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) hpp
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop_np 1 v
  have hk1z : (k : ZMod (m / p)) = 1 := by
    simpa using (ZMod.natCast_eq_natCast_iff' k 1 (m / p)).mpr hk1
  have hk2z : (k : ZMod p) = (v : ZMod p) := (ZMod.natCast_eq_natCast_iff' k v p).mpr hk2
  have hk_coprime_n : Nat.Coprime k (m / p) := by
    rw [← ZMod.isUnit_iff_coprime]
    rw [hk1z]; exact isUnit_one
  have hk_coprime_p : Nat.Coprime k p := by
    rw [← ZMod.isUnit_iff_coprime]
    rw [hk2z, hv_cast]; exact a.isUnit
  have hcop_km : Nat.Coprime k m := by
    have h2 := hk_coprime_p.mul_right hk_coprime_n
    rwa [Nat.mul_div_cancel' hpm] at h2
  -- the congruences lifted to `ℤ`, for the reductions `J(· | p)` and `J(· | m/p)`
  have hk2' : ((k : ℤ) % p = (v : ℤ) % p) := by
    have h : ((k % p : ℕ) : ℤ) = ((v % p : ℕ) : ℤ) := by rw [hk2]
    rwa [Int.natCast_emod, Int.natCast_emod] at h
  have hk1' : ((k : ℤ) % (m / p) = (1 : ℤ) % (m / p)) := by
    have h : ((k % (m / p) : ℕ) : ℤ) = ((1 % (m / p) : ℕ) : ℤ) := by rw [hk1]
    rwa [Int.natCast_emod, Int.natCast_emod] at h
  refine ⟨ZMod.unitOfCoprime k hcop_km, ?_, ?_⟩
  · apply Units.ext
    rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_natCast hd k, hk1z, Units.val_one]
  · rw [ZMod.coe_unitOfCoprime k hcop_km, jacobiChar_natCast]
    have hk : jacobiSym (k : ℤ) m = -1 := by
      conv_lhs => rw [← Nat.mul_div_cancel' hpm]
      rw [jacobiSym.mul_right' (k : ℤ) hp.ne_zero hdiv_ne_zero]
      have h1 : jacobiSym (k : ℤ) p = -1 := by
        rw [jacobiSym.mod_left' hk2', hJp]
      have h2 : jacobiSym (k : ℤ) (m / p) = 1 := by
        rw [jacobiSym.mod_left' hk1', jacobiSym.one_left]
      rw [h1, h2]; norm_num
    rw [hk]; norm_num

/-- A Dirichlet character of level a squarefree `m` whose conductor is not `m` factors through
`m / p` for some prime `p ∣ m`; contrapositively, if `χ` does not factor through any `m / p`
with `p ∣ m` prime, then `m` is its conductor. -/
private lemma conductor_eq_of_not_factorsThrough {m : ℕ} [NeZero m] (hm_pos : 0 < m)
    (hsq : Squarefree m) (χ : DirichletCharacter ℂ m)
    (h : ∀ p, p.Prime → p ∣ m → ¬ χ.FactorsThrough (m / p)) : χ.conductor = m := by
  have hdvd : χ.conductor ∣ m := DirichletCharacter.conductor_dvd_level χ
  refine le_antisymm (Nat.le_of_dvd hm_pos hdvd) ?_
  by_contra hcon
  have hlt : χ.conductor < m := lt_of_not_ge hcon
  have hc_mul : χ.conductor * (m / χ.conductor) = m := Nat.mul_div_cancel' hdvd
  have ht_ne_one : m / χ.conductor ≠ 1 := by
    intro hh
    rw [hh, mul_one] at hc_mul
    exact absurd hc_mul (ne_of_lt hlt)
  obtain ⟨p, hp, hpt⟩ := Nat.exists_prime_and_dvd ht_ne_one
  have hpm : p ∣ m := hpt.trans (Nat.div_dvd_of_dvd hdvd)
  have hpndvd : ¬ p ∣ χ.conductor := by
    intro hpc
    have hpp : p * p ∣ m := by rw [← hc_mul]; exact mul_dvd_mul hpc hpt
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) hpp
  have hcp : Nat.Coprime χ.conductor p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpndvd).symm
  have hcd : χ.conductor ∣ m / p := by
    refine hcp.dvd_of_dvd_mul_left ?_
    rw [Nat.mul_div_cancel' hpm]
    exact hdvd
  exact h p hp hpm
    ((DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ (Nat.div_dvd_of_dvd hpm)).mpr hcd)

/-- **The Jacobi character of a squarefree odd modulus is primitive.**
`χ = Work.FIArea4.jacobiChar m` is the character `a ↦ J(a.val | m)` (`Submission/Work/FIArea4/JacobiChar.lean`).
Proof plan: `DirichletCharacter.IsPrimitive χ ↔ χ.conductor = m` (`isPrimitive_def`), and
`χ.conductor ∣ m` (`conductor_dvd_level`). If `χ.conductor ≠ m` then, `m` being squarefree,
`χ.conductor ∣ m / p` for some prime `p ∣ m`, so `χ.FactorsThrough (m / p)`, i.e.
`(ZMod.unitsMap hd).ker ≤ χ.toUnitHom.ker` (`factorsThrough_iff_ker_unitsMap`,
`DirichletCharacter.mem_conductorSet_iff_conductor_dvd`). Exhibit a unit `u` of `ZMod m` with
`ZMod.unitsMap hd u = 1` (equivalently `u ≡ 1` mod `m / p`) but `χ u ≠ 1`: choose a quadratic
nonresidue `v` mod `p` (`FiniteField.exists_nonsquare`), let `u : ℕ` satisfy `u ≡ 1 [MOD m / p]`
and `u ≡ v [MOD p]` (`Nat.chineseRemainder'`, using `Nat.Coprime (m/p) p` from `Squarefree m`),
and use `ZMod.unitOfCoprime`. Then `χ u = J(u.val | m) = ∏_{q ∣ m} legendreSym q u.val =
legendreSym p u.val = -1`, because `u ≡ 1` modulo every prime `q ≠ p` dividing `m`. -/
theorem jacobiChar_isPrimitive {m : ℕ} [NeZero m] (hsq : Squarefree m) (hodd : Odd m)
    (h3 : 3 ≤ m) : (Work.FIArea4.jacobiChar m).IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  have hm_pos : 0 < m := by omega
  refine conductor_eq_of_not_factorsThrough hm_pos hsq (jacobiChar m) ?_
  intro p hp hpm hft
  have hd : m / p ∣ m := Nat.div_dvd_of_dvd hpm
  obtain ⟨u, hu1, hu2⟩ := exists_unit_unitsMap_eq_one_and_char_eq_neg_one hsq hodd hp hpm hd
  have hker := (DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := jacobiChar m) hd).mp hft
  have hmem : u ∈ (ZMod.unitsMap hd).ker := MonoidHom.mem_ker.mpr hu1
  have hone : MulChar.toUnitHom (jacobiChar m) u = 1 := MonoidHom.mem_ker.mp (hker hmem)
  have hval : jacobiChar m (u : ZMod m) = 1 := by
    have hcast := congrArg (fun x : ℂˣ => (x : ℂ)) hone
    simpa [MulChar.coe_toUnitHom] using hcast
  rw [hu2] at hval
  exact absurd hval (by norm_num)

end

end Work.FIArea4
