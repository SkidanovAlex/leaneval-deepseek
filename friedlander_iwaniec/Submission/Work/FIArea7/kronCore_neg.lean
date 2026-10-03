import Mathlib
import Submission.Work.FIArea7.KronTwoAux
import Submission.Work.FIArea7.kronCore

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

set_option maxHeartbeats 2000000

/-- For odd `a`, Mathlib's Jacobi symbol `J(2 | a)` (which is `1`, the Legendre symbol at `2`) is
the Kronecker symbol `χ₂(a) = kronTwo a`. -/
lemma jacobiSym_two_eq_kronTwo {a : ℕ} (ha : Odd a) : jacobiSym 2 a = kronTwo (a : ℤ) := by
  rw [jacobiSym.at_two ha, kronTwo_eq_chi8]
  norm_num

theorem kronCore_neg {u1 u2 : ℕ} {s1 s2 : ℤ}
    (hu1 : Odd u1) (hu2 : Odd u2) (h12 : u1.Coprime u2)
    (hcs1 : u1.Coprime s1.natAbs) (hcs2 : u2.Coprime s2.natAbs)
    (h4 : (u1 : ℤ) + (u2 : ℤ) ≡ 0 [ZMOD 4])
    (hD : (u1 : ℤ) * s2 + (u2 : ℤ) * s1 ≠ 0) :
    jacobiSym (-(((u1 * u2 : ℕ) : ℤ))) (((u1 : ℤ) * s2 + (u2 : ℤ) * s1).natAbs)
        * Work.FIArea7.kronTwo (((u1 * u2 : ℕ) : ℤ))
            ^ ((((u1 : ℤ) * s2 + (u2 : ℤ) * s1).natAbs).factorization 2)
      = (if 0 < (u1 : ℤ) * s2 + (u2 : ℤ) * s1 then (1 : ℤ) else -1)
        * (jacobiSym s1 u1 * jacobiSym s2 u2) := by
  have hDl0 : (u1 : ℤ) * s2 + (u2 : ℤ) * s1 ≠ 0 := hD
  set Dl : ℤ := (u1 : ℤ) * s2 + (u2 : ℤ) * s1 with hDldef
  set M : ℕ := Dl.natAbs with hMdef
  set ν : ℕ := M.factorization 2 with hνdef
  set n : ℕ := M / 2 ^ ν with hndef
  set ε : ℤ := (if 0 < Dl then (1 : ℤ) else -1) with hεdef
  set Az : ℤ := (((u1 * u2 : ℕ) : ℤ)) with hAzdef
  have hDlne : Dl ≠ 0 := by rw [hDldef]; exact hDl0
  -- basic oddness facts
  have hu1z : Odd ((u1 : ℤ)) := by exact_mod_cast hu1
  have hu2z : Odd ((u2 : ℤ)) := by exact_mod_cast hu2
  have haodd : Odd (u1 * u2) := hu1.mul hu2
  have haz : Odd Az := by rw [hAzdef]; exact_mod_cast haodd
  have hnegaz : Odd (-Az) := haz.neg
  -- the `2`-adic splitting of `M = |Dl|`
  have hMne : M ≠ 0 := (Int.natAbs_pos.mpr hDlne).ne'
  have h2dvd : 2 ^ ν ∣ M := by
    rw [hνdef]
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hMne).mpr le_rfl
  have hMsplit : 2 ^ ν * n = M := by rw [hndef]; exact Nat.mul_div_cancel' h2dvd
  have hnne : n ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hMne) h2dvd) (by positivity)).ne'
  have hfacn : n.factorization 2 = 0 := by
    rw [hndef, Nat.factorization_div h2dvd, Finsupp.tsub_apply,
      Nat.factorization_pow_self Nat.prime_two, ← hνdef]
    exact tsub_self ν
  have hnodd : Odd n := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro hcon
    have h1 := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hnne).mp hcon
    rw [hfacn] at h1
    omega
  -- the sign of `Dl`, and `Dl = ε |Dl|`
  have hεval : ε = 1 ∨ ε = -1 := by
    rw [hεdef]; split_ifs <;> simp
  have hεsq : ε * ε = 1 := by rcases hεval with h | h <;> rw [h] <;> norm_num
  have hDlM : Dl = ε * (M : ℤ) := by
    rcases lt_or_gt_of_ne hDlne with hneg | hpos
    · have hε : ε = -1 := by rw [hεdef]; exact if_neg (not_lt.mpr hneg.le)
      rw [hε, neg_one_mul]
      have hMv : (M : ℤ) = -Dl := by
        have htmp : ((((-Dl).natAbs : ℕ) : ℤ)) = -Dl := Int.natAbs_of_nonneg (by linarith)
        rw [Int.natAbs_neg] at htmp
        rw [hMdef]; exact htmp
      linarith
    · have hε : ε = 1 := by rw [hεdef]; exact if_pos hpos
      rw [hε, one_mul]
      have hMv : (M : ℤ) = Dl := by rw [hMdef]; exact Int.natAbs_of_nonneg hpos.le
      linarith
  -- parity facts coming from `u₁ + u₂ ≡ 0 (mod 4)`
  have ho1 : u1 % 2 = 1 := Nat.odd_iff.mp hu1
  have ho2 : u2 % 2 = 1 := Nat.odd_iff.mp hu2
  have h4n : (u1 + u2) % 4 = 0 := by
    have h := Int.natCast_modEq_iff.mp
      (show (((u1 + u2 : ℕ)) : ℤ) ≡ (((0 : ℕ)) : ℤ) [ZMOD (((4 : ℕ)) : ℤ)] from by
        push_cast; exact h4)
    rw [Nat.ModEq] at h
    simpa using h
  have hpq : (u1 / 2 + u2 / 2) % 2 = 1 := by omega
  have hAodd : ((u1 * u2) / 2) % 2 = 1 := by
    rw [mul_div_two_odd hu1 hu2]
    rw [show 2 * (u1 / 2) * (u2 / 2) + u1 / 2 + u2 / 2
          = 2 * ((u1 / 2) * (u2 / 2)) + (u1 / 2 + u2 / 2) by ring]
    omega
  have hE2even : Even ((u2 / 2) * (u1 / 2)) := by
    rw [Nat.even_iff, Nat.mul_mod]
    rcases Nat.mod_two_eq_zero_or_one (u1 / 2) with hh | hh <;>
      rcases Nat.mod_two_eq_zero_or_one (u2 / 2) with hh' | hh' <;>
      rw [hh, hh'] <;> norm_num <;> omega
  -- step 1: discard the `2`-part of the denominator `M`
  have hJn : jacobiSym (-Az) M = jacobiSym (-Az) n := by
    rw [← hMsplit, jacobiSym.mul_right' _ (pow_ne_zero ν (by norm_num)) hnne,
      jacobiSym.pow_right, jacobiSym_two_right_of_odd hnegaz, one_pow, one_mul]
  -- step 2: split off the `-1` in the numerator
  have hneg : jacobiSym (-Az) n = ZMod.χ₄ (n : ZMod 4) * jacobiSym Az n :=
    jacobiSym.neg Az hnodd
  have hchi4 : ZMod.χ₄ (n : ZMod 4) = (-1 : ℤ) ^ (n / 2) :=
    ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hnodd)
  -- step 3: quadratic reciprocity
  have hrec : jacobiSym Az n
      = (-1) ^ ((u1 * u2) / 2 * (n / 2)) * jacobiSym ((n : ℕ) : ℤ) (u1 * u2) :=
    jacobiSym.quadratic_reciprocity haodd hnodd
  have hmul : jacobiSym ((n : ℕ) : ℤ) (u1 * u2)
      = jacobiSym ((n : ℕ) : ℤ) u1 * jacobiSym ((n : ℕ) : ℤ) u2 :=
    jacobiSym.mul_right' _ hu1.pos.ne' hu2.pos.ne'
  -- step 4: express `J(n | uᵢ)` through `J(Dl | uᵢ)` and the `χ₂` correction
  have hD1 : jacobiSym ((M : ℕ) : ℤ) u1
      = kronTwo ((u1 : ℤ)) ^ ν * jacobiSym ((n : ℕ) : ℤ) u1 := by
    rw [← hMsplit]; push_cast
    rw [jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym_two_eq_kronTwo hu1]
  have hD2 : jacobiSym ((M : ℕ) : ℤ) u2
      = kronTwo ((u2 : ℤ)) ^ ν * jacobiSym ((n : ℕ) : ℤ) u2 := by
    rw [← hMsplit]; push_cast
    rw [jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym_two_eq_kronTwo hu2]
  have hk1 : kronTwo ((u1 : ℤ)) ^ ν * kronTwo ((u1 : ℤ)) ^ ν = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, kronTwo_sq_of_odd hu1z, one_pow]
  have hk2 : kronTwo ((u2 : ℤ)) ^ ν * kronTwo ((u2 : ℤ)) ^ ν = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, kronTwo_sq_of_odd hu2z, one_pow]
  have he1 : jacobiSym ε u1 * jacobiSym ε u1 = 1 := by
    rw [← jacobiSym.mul_left ε ε u1, hεsq, jacobiSym.one_left]
  have he2 : jacobiSym ε u2 * jacobiSym ε u2 = 1 := by
    rw [← jacobiSym.mul_left ε ε u2, hεsq, jacobiSym.one_left]
  have hDl1 : jacobiSym Dl u1
      = jacobiSym ε u1 * (kronTwo ((u1 : ℤ)) ^ ν * jacobiSym ((n : ℕ) : ℤ) u1) := by
    rw [hDlM, jacobiSym.mul_left, hD1]
  have hDl2 : jacobiSym Dl u2
      = jacobiSym ε u2 * (kronTwo ((u2 : ℤ)) ^ ν * jacobiSym ((n : ℕ) : ℤ) u2) := by
    rw [hDlM, jacobiSym.mul_left, hD2]
  have hflip1 : jacobiSym ((n : ℕ) : ℤ) u1
      = kronTwo ((u1 : ℤ)) ^ ν * (jacobiSym ε u1 * jacobiSym Dl u1) := by
    have hkey : kronTwo ((u1 : ℤ)) ^ ν
          * (jacobiSym ε u1 * (jacobiSym ε u1
              * (kronTwo ((u1 : ℤ)) ^ ν * jacobiSym ((n : ℕ) : ℤ) u1)))
        = jacobiSym ((n : ℕ) : ℤ) u1 := by
      rw [show kronTwo ((u1 : ℤ)) ^ ν
            * (jacobiSym ε u1 * (jacobiSym ε u1
                * (kronTwo ((u1 : ℤ)) ^ ν * jacobiSym ((n : ℕ) : ℤ) u1)))
          = (kronTwo ((u1 : ℤ)) ^ ν * kronTwo ((u1 : ℤ)) ^ ν)
            * (jacobiSym ε u1 * jacobiSym ε u1) * jacobiSym ((n : ℕ) : ℤ) u1 by ring]
      rw [hk1, he1]; ring
    rw [hDl1]
    exact hkey.symm
  have hflip2 : jacobiSym ((n : ℕ) : ℤ) u2
      = kronTwo ((u2 : ℤ)) ^ ν * (jacobiSym ε u2 * jacobiSym Dl u2) := by
    have hkey : kronTwo ((u2 : ℤ)) ^ ν
          * (jacobiSym ε u2 * (jacobiSym ε u2
              * (kronTwo ((u2 : ℤ)) ^ ν * jacobiSym ((n : ℕ) : ℤ) u2)))
        = jacobiSym ((n : ℕ) : ℤ) u2 := by
      rw [show kronTwo ((u2 : ℤ)) ^ ν
            * (jacobiSym ε u2 * (jacobiSym ε u2
                * (kronTwo ((u2 : ℤ)) ^ ν * jacobiSym ((n : ℕ) : ℤ) u2)))
          = (kronTwo ((u2 : ℤ)) ^ ν * kronTwo ((u2 : ℤ)) ^ ν)
            * (jacobiSym ε u2 * jacobiSym ε u2) * jacobiSym ((n : ℕ) : ℤ) u2 by ring]
      rw [hk2, he2]; ring
    rw [hDl2]
    exact hkey.symm
  -- step 5: reduce `J(Dl | uᵢ)` by the congruence `Dl ≡ u₂s₁` resp. `u₁s₂`
  have hDexp1 : jacobiSym Dl u1 = jacobiSym ((u2 : ℤ)) u1 * jacobiSym s1 u1 := by
    have hc : Dl ≡ (u2 : ℤ) * s1 [ZMOD (u1 : ℤ)] := by
      rw [Int.modEq_iff_dvd]; refine ⟨-s2, ?_⟩; rw [hDldef]; ring
    rw [jacobiSym.mod_left' hc.eq, jacobiSym.mul_left]
  have hDexp2 : jacobiSym Dl u2 = jacobiSym ((u1 : ℤ)) u2 * jacobiSym s2 u2 := by
    have hc : Dl ≡ (u1 : ℤ) * s2 [ZMOD (u2 : ℤ)] := by
      rw [Int.modEq_iff_dvd]; refine ⟨-s1, ?_⟩; rw [hDldef]; ring
    rw [jacobiSym.mod_left' hc.eq, jacobiSym.mul_left]
  have hrec2 : jacobiSym ((u2 : ℤ)) u1
      = (-1) ^ (u2 / 2 * (u1 / 2)) * jacobiSym ((u1 : ℤ)) u2 :=
    jacobiSym.quadratic_reciprocity hu2 hu1
  have hK2 : jacobiSym ((u1 : ℤ)) u2 * jacobiSym ((u1 : ℤ)) u2 = 1 := by
    have hg : ((u1 : ℤ)).gcd (↑u2) = 1 := by
      rw [Int.gcd_natCast_natCast]; exact h12
    have hh := jacobiSym.sq_one hg
    rwa [sq] at hh
  have hchi : kronTwo ((u1 : ℤ)) ^ ν * kronTwo ((u2 : ℤ)) ^ ν * kronTwo Az ^ ν = 1 := by
    have hχa : kronTwo Az = kronTwo ((u1 : ℤ)) * kronTwo ((u2 : ℤ)) := by
      rw [hAzdef, show (((u1 * u2 : ℕ) : ℤ)) = (u1 : ℤ) * (u2 : ℤ) by push_cast; ring,
        kronTwo_mul]
    rw [hχa, ← mul_pow, ← pow_add, ← two_mul, pow_mul, mul_pow,
      kronTwo_sq_of_odd hu1z, kronTwo_sq_of_odd hu2z, one_mul, one_pow]
  -- step 6: the residual sign identity
  have hA : (-1 : ℤ) ^ (n / 2) * (-1) ^ ((u1 * u2) / 2 * (n / 2)) = 1 := by
    rw [← pow_add]
    apply Even.neg_one_pow
    have hodd : Odd ((u1 * u2) / 2) := Nat.odd_iff.mpr hAodd
    obtain ⟨k, hk⟩ := hodd
    rw [show n / 2 + (u1 * u2) / 2 * (n / 2) = (n / 2) * (1 + (u1 * u2) / 2) by ring]
    rw [hk]
    exact Even.mul_left (⟨k + 1, by ring⟩ : Even (1 + (2 * k + 1))) (n / 2)
  have hB : (jacobiSym ε u1 * jacobiSym ε u2) * (-1 : ℤ) ^ (u2 / 2 * (u1 / 2)) = ε := by
    rcases hεval with hε1 | hε2
    · rw [hε1, jacobiSym.one_left, jacobiSym.one_left, one_mul, one_mul]
      exact Even.neg_one_pow hE2even
    · rw [hε2, jacobiSym.at_neg_one hu1, jacobiSym.at_neg_one hu2,
        ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hu1),
        ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hu2), ← pow_add, ← pow_add]
      exact Odd.neg_one_pow (Odd.add_even (Nat.odd_iff.mpr hpq) hE2even)
  have hsign : (-1 : ℤ) ^ (n / 2) * (-1) ^ ((u1 * u2) / 2 * (n / 2))
      * (jacobiSym ε u1 * jacobiSym ε u2) * (-1) ^ (u2 / 2 * (u1 / 2)) = ε := by
    rw [hA, one_mul]
    exact hB
  -- final assembly
  calc
    jacobiSym (-Az) M * kronTwo Az ^ ν
        = jacobiSym (-Az) n * kronTwo Az ^ ν := by rw [hJn]
    _ = (ZMod.χ₄ (n : ZMod 4) * jacobiSym Az n) * kronTwo Az ^ ν := by rw [hneg]
    _ = ((-1 : ℤ) ^ (n / 2) * jacobiSym Az n) * kronTwo Az ^ ν := by rw [hchi4]
    _ = ((-1 : ℤ) ^ (n / 2)
          * ((-1) ^ ((u1 * u2) / 2 * (n / 2)) * jacobiSym ((n : ℕ) : ℤ) (u1 * u2)))
          * kronTwo Az ^ ν := by rw [hrec]
    _ = ((-1 : ℤ) ^ (n / 2)
          * ((-1) ^ ((u1 * u2) / 2 * (n / 2))
            * (jacobiSym ((n : ℕ) : ℤ) u1 * jacobiSym ((n : ℕ) : ℤ) u2)))
          * kronTwo Az ^ ν := by rw [hmul]
    _ = ((-1 : ℤ) ^ (n / 2)
          * ((-1) ^ ((u1 * u2) / 2 * (n / 2))
            * ((kronTwo ((u1 : ℤ)) ^ ν * (jacobiSym ε u1 * jacobiSym Dl u1))
                * (kronTwo ((u2 : ℤ)) ^ ν * (jacobiSym ε u2 * jacobiSym Dl u2)))))
          * kronTwo Az ^ ν := by rw [hflip1, hflip2]
    _ = ((-1 : ℤ) ^ (n / 2)
          * ((-1) ^ ((u1 * u2) / 2 * (n / 2))
            * ((kronTwo ((u1 : ℤ)) ^ ν
                  * (jacobiSym ε u1 * ((-1) ^ (u2 / 2 * (u1 / 2))
                      * jacobiSym ((u1 : ℤ)) u2 * jacobiSym s1 u1)))
                * (kronTwo ((u2 : ℤ)) ^ ν
                  * (jacobiSym ε u2 * (jacobiSym ((u1 : ℤ)) u2 * jacobiSym s2 u2))))))
          * kronTwo Az ^ ν := by rw [hDexp1, hDexp2, hrec2]
    _ = ε * (jacobiSym s1 u1 * jacobiSym s2 u2) := by
      have hmain : ((-1 : ℤ) ^ (n / 2)
            * ((-1) ^ ((u1 * u2) / 2 * (n / 2))
              * ((kronTwo ((u1 : ℤ)) ^ ν
                    * (jacobiSym ε u1 * ((-1) ^ (u2 / 2 * (u1 / 2))
                        * jacobiSym ((u1 : ℤ)) u2 * jacobiSym s1 u1)))
                  * (kronTwo ((u2 : ℤ)) ^ ν
                    * (jacobiSym ε u2 * (jacobiSym ((u1 : ℤ)) u2 * jacobiSym s2 u2))))))
            * kronTwo Az ^ ν
          = ((-1 : ℤ) ^ (n / 2) * (-1) ^ ((u1 * u2) / 2 * (n / 2))
              * (jacobiSym ε u1 * jacobiSym ε u2) * (-1) ^ (u2 / 2 * (u1 / 2)))
            * (kronTwo ((u1 : ℤ)) ^ ν * kronTwo ((u2 : ℤ)) ^ ν * kronTwo Az ^ ν)
            * (jacobiSym ((u1 : ℤ)) u2 * jacobiSym ((u1 : ℤ)) u2)
            * (jacobiSym s1 u1 * jacobiSym s2 u2) := by ring
      rw [hmain, hsign, hchi, hK2]
      ring

end Work.FIArea7
