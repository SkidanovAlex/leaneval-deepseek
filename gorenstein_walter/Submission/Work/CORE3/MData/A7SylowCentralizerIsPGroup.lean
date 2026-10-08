/-
# `A₇`: the centralizer of a Sylow `2`-subgroup is a `2`-group

Let `S` be a Sylow `2`-subgroup of `A₇` and `C = C_{A₇}(S)`.  We show `IsPGroup 2 C`.

## The argument

Every Sylow `2`-subgroup `S` of `A₇` is dihedral of order `2 · 4 = 8` (`h7.2`).

1. `S` has an involution `w` (Cauchy's theorem, `exists_prime_orderOf_dvd_card'`), and
   `C ≤ C_{A₇}(w)`.  Since `|C_{A₇}(w)| = 24` for every non-identity involution `w` of `A₇`
   (`Work.AUTA7.A7.CentralizerInvolution`), we get `|C| ∣ 24`.
2. `3 ∤ |C|`: otherwise Cauchy's theorem produces `c ∈ C` of order `3`; then `S ≤ C_{A₇}(c)`, so
   `8 ∣ |C_{A₇}(c)|`.  But the centralizer of an element of order `3` in `A₇` has order `36`
   (a `3`-cycle) or `9` (a product of two disjoint `3`-cycles)
   (`Work.AUTA7.A7.CentralizerOrderThree`), and neither is divisible by `8`.
3. Hence `|C| ∣ 8 = 2³`, and `IsPGroup.of_card_dvd_pow` gives `IsPGroup 2 C`.

The two quoted `A₇`-computations live in the `AUTA7` area; the modules used here
(`Submission.Work.AUTA7.A7.CentralizerInvolution`, `Submission.Work.AUTA7.A7.CentralizerOrderThree`)
do not declare any `Work.GW2` name, so they can be imported alongside the canonical vocabulary of
`Submission.Work.ASM.Defs`.
-/
import Mathlib
import Submission.Work.ASM.Defs
import Submission.Work.A7.Defs
import Submission.Work.AUTA7.A7.CentralizerInvolution
import Submission.Work.AUTA7.A7.CentralizerOrderThree

namespace Work.CORE3.MData

/-- `A₇`: the centralizer of a Sylow `2`-subgroup is a `2`-group. -/
theorem A7SylowCentralizerIsPGroup (h7 : Work.GW2.A7ModelProp)
    (S : Sylow 2 (alternatingGroup (Fin 7))) :
    IsPGroup 2 ↥(Subgroup.centralizer
      ((S : Subgroup (alternatingGroup (Fin 7))) : Set (alternatingGroup (Fin 7)))) := by
  classical
  have hprime2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup (alternatingGroup (Fin 7)) :=
    Subgroup.centralizer ((S : Subgroup (alternatingGroup (Fin 7))) : Set _) with hC
  -- ## `|S| = 8` (`S` is dihedral of order `2 · 4 = 8`)
  have hcardS : Nat.card ↥(S : Subgroup (alternatingGroup (Fin 7))) = 8 := by
    obtain ⟨e⟩ := h7.2.1 S
    exact (Nat.card_congr e.toEquiv).trans (by rw [DihedralGroup.nat_card])
  -- ## an involution `w` of `S`
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(S : Subgroup (alternatingGroup (Fin 7)))) 2 (by rw [hcardS]; norm_num)
  set wA : alternatingGroup (Fin 7) :=
    ((w : (S : Subgroup (alternatingGroup (Fin 7)))) : alternatingGroup (Fin 7)) with hwAdef
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
  -- ## `C ≤ C_{A₇}(w)`, so `|C| ∣ 24`
  have hwAmem : wA ∈ (S : Subgroup (alternatingGroup (Fin 7))) := by
    rw [hwAdef]; exact w.2
  have hCle : C ≤ Subgroup.centralizer ({wA} : Set (alternatingGroup (Fin 7))) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp hx) wA hwAmem).symm
  have h24 : Nat.card ↥(Subgroup.centralizer ({wA} : Set (alternatingGroup (Fin 7)))) = 24 :=
    Work.AUTA7.A7.CentralizerInvolution hw2 hwne
  have hCdvd : Nat.card ↥C ∣ 24 := by
    have h := Subgroup.card_dvd_of_le hCle
    rwa [h24] at h
  -- ## `3 ∤ |C|`
  have h3 : ¬ 3 ∣ Nat.card ↥C := by
    intro h3dvd
    have hprime3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 3 h3dvd
    set cA : alternatingGroup (Fin 7) := ((c : ↥C) : alternatingGroup (Fin 7)) with hcAdef
    have hcA : orderOf cA = 3 := by
      rw [hcAdef]
      exact (orderOf_injective (Subgroup.subtype C) Subtype.val_injective c).trans hc
    have hcAmemS : ∀ y ∈ (S : Subgroup (alternatingGroup (Fin 7))), y * cA = cA * y := by
      intro y hy
      rw [hcAdef]
      exact (Subgroup.mem_centralizer_iff.mp c.2) y hy
    have hSle : (S : Subgroup (alternatingGroup (Fin 7))) ≤
        Subgroup.centralizer ({cA} : Set (alternatingGroup (Fin 7))) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcAmemS y hy
    have h8dvd : 8 ∣ Nat.card ↥(Subgroup.centralizer ({cA} : Set (alternatingGroup (Fin 7)))) := by
      have h := Subgroup.card_dvd_of_le hSle
      rwa [hcardS] at h
    rcases Work.AUTA7.A7.CentralizerOrderThree hcA with h | h <;> rw [h] at h8dvd <;>
      norm_num at h8dvd
  -- ## `|C| ∣ 8`, hence `C` is a `2`-group
  have h8 : Nat.card ↥C ∣ 8 := by
    have hcop : Nat.Coprime (Nat.card ↥C) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).mpr h3).symm
    exact hcop.dvd_of_dvd_mul_right (by simpa using hCdvd)
  exact IsPGroup.of_card_dvd_pow (p := 2) (n := 3) (by simpa using h8)

end Work.CORE3.MData
