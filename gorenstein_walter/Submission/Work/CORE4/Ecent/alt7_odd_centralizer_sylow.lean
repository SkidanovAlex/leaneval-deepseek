import Mathlib
import Submission.Work.AUTA7.A7.CentralizerInvolution
import Submission.Work.AUTA7.A7.CentralizerOrderThree
import Submission.Work.A7.Defs

namespace Work.CORE4.Ecent

/-- In `A₇`, an element of odd order centralising a Sylow 2-subgroup is trivial.

Proof plan: `|D| = 8` (Sylow in a group of order 2520, `Work.A7.card_alternatingGroup_seven` and
`Sylow.card_eq_multiplicity`); the centre `Z(D)` of the 2-group `↥D` is nontrivial
(`IsPGroup.center_nontrivial`), so contains an involution `z` (take an appropriate 2-power of a
non-identity element of the centre, using `IsPGroup.iff_orderOf`).  Then `x ∈ C(D) ≤ C(z)` gives
`orderOf x ∣ |C_{A₇}(z)| = 24` (`Work.AUTA7.A7.CentralizerInvolution`) and `orderOf x` is odd, so
`orderOf x ∈ {1,3}`.  If `orderOf x = 3` then `D ≤ C_{A₇}(x)`, so `8 ∣ |C_{A₇}(x)|`; but
`Work.AUTA7.A7.CentralizerOrderThree` gives `|C_{A₇}(x)| = 36 ∨ |C_{A₇}(x)| = 9` — contradiction.
Hence `orderOf x = 1`, i.e. `x = 1`. -/
theorem alt7_odd_centralizer_sylow (D : Sylow 2 (alternatingGroup (Fin 7)))
    {x : alternatingGroup (Fin 7)} (hxodd : Odd (orderOf x))
    (hc : x ∈ Subgroup.centralizer
      ((D : Subgroup (alternatingGroup (Fin 7))) : Set (alternatingGroup (Fin 7)))) :
    x = 1 := by
  classical
  -- `|D| = 8 = 2 ^ 3`: `D` is a Sylow `2`-subgroup of `A₇` of order `2520 = 2 ^ 3 * 315`.
  have hcardD : Nat.card ↥(D : Subgroup (alternatingGroup (Fin 7))) = 8 := by
    rw [Sylow.card_eq_multiplicity, Work.A7.card_alternatingGroup_seven]
    have h1 : (2520:ℕ) = 2 ^ 3 * 315 := by norm_num
    rw [h1, Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]
    norm_num
  set C : Subgroup (alternatingGroup (Fin 7)) :=
    Subgroup.centralizer ((D : Subgroup (alternatingGroup (Fin 7))) : Set _) with hC
  -- An involution `wA` of `D` (Cauchy's theorem, since `|D| = 8` is even).
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(D : Subgroup (alternatingGroup (Fin 7)))) 2 (by rw [hcardD]; norm_num)
  set wA : alternatingGroup (Fin 7) :=
    ((w : (D : Subgroup (alternatingGroup (Fin 7)))) : alternatingGroup (Fin 7)) with hwAdef
  have hwA : orderOf wA = 2 := by
    rw [hwAdef]
    exact (orderOf_injective (Subgroup.subtype _) Subtype.val_injective w).trans hw
  have hw2 : wA * wA = 1 := by
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, hwA]
  have hwne : wA ≠ 1 := by
    intro h
    have h1 : orderOf wA = 1 := by rw [h, orderOf_one]
    rw [hwA] at h1
    exact absurd h1 (by norm_num)
  have hwAmem : wA ∈ (D : Subgroup (alternatingGroup (Fin 7))) := by
    rw [hwAdef]; exact w.2
  -- `C ≤ C_{A₇}(wA)`, so `|C| ∣ 24`.
  have hCle : C ≤ Subgroup.centralizer ({wA} : Set (alternatingGroup (Fin 7))) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp hy) wA hwAmem).symm
  have h24 : Nat.card ↥(Subgroup.centralizer ({wA} : Set (alternatingGroup (Fin 7)))) = 24 :=
    Work.AUTA7.A7.CentralizerInvolution hw2 hwne
  have hCdvd : Nat.card ↥C ∣ 24 := by
    have h := Subgroup.card_dvd_of_le hCle
    rwa [h24] at h
  -- `3 ∤ |C|`: otherwise `C` contains an element `cA` of order `3`, forcing `8 ∣ |C_{A₇}(cA)|`,
  -- but `|C_{A₇}(cA)|` is `36` or `9`.
  have h3 : ¬ 3 ∣ Nat.card ↥C := by
    intro h3dvd
    have hprime3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨c, hc3⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 3 h3dvd
    set cA : alternatingGroup (Fin 7) := ((c : ↥C) : alternatingGroup (Fin 7)) with hcAdef
    have hcA : orderOf cA = 3 := by
      rw [hcAdef]
      exact (orderOf_injective (Subgroup.subtype C) Subtype.val_injective c).trans hc3
    have hcAmemD : ∀ y ∈ (D : Subgroup (alternatingGroup (Fin 7))), y * cA = cA * y := by
      intro y hy
      rw [hcAdef]
      exact (Subgroup.mem_centralizer_iff.mp c.2) y hy
    have hDle : (D : Subgroup (alternatingGroup (Fin 7))) ≤
        Subgroup.centralizer ({cA} : Set (alternatingGroup (Fin 7))) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcAmemD y hy
    have h8dvd : 8 ∣ Nat.card ↥(Subgroup.centralizer ({cA} : Set (alternatingGroup (Fin 7)))) := by
      have h := Subgroup.card_dvd_of_le hDle
      rwa [hcardD] at h
    rcases Work.AUTA7.A7.CentralizerOrderThree hcA with h | h <;> rw [h] at h8dvd <;>
      norm_num at h8dvd
  -- `|C| ∣ 8`.
  have h8 : Nat.card ↥C ∣ 8 := by
    have hcop3 : Nat.Coprime (Nat.card ↥C) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).mpr h3).symm
    exact hcop3.dvd_of_dvd_mul_right (by simpa using hCdvd)
  -- `orderOf x ∣ |⟨x⟩| ∣ |C| ∣ 8`, and it is odd, hence it is `1`.
  have hxc : x ∈ C := by rw [hC]; exact hc
  have hdvd8 : orderOf x ∣ 8 := by
    rw [← Nat.card_zpowers x]
    exact (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxc)).trans h8
  have hcop : Nat.Coprime (orderOf x) 2 := Nat.coprime_two_right.mpr hxodd
  exact orderOf_eq_one_iff.mp ((hcop.pow_right 3).eq_one_of_dvd (by simpa using hdvd8))

end Work.CORE4.Ecent
