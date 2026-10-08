import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.PSL2.Card

namespace Work.CORE4.Counting

theorem NormalizerCard (htorus : Work.GW2.L2TorusNormalizerProp)
    (pF kF k k' r : ℕ) [Fact pF.Prime]
    (hodd : Odd pF) (hq5 : 5 ≤ pF ^ kF)
    (hk : Even k) (hk' : Odd k')
    (hdisj : (2 * k = pF ^ kF + 1 ∧ 2 * k' = pF ^ kF - 1) ∨
             (2 * k = pF ^ kF - 1 ∧ 2 * k' = pF ^ kF + 1))
    (hr : r.Prime) (hr2 : r ≠ 2) (hrp : r ≠ pF) (hrk : r ∣ k)
    (Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))
    (hY : Nat.card Y = r) :
    Nat.card (Subgroup.normalizer (Y : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))) = 2 * k := by
  obtain ⟨_, h2card, ⟨e⟩⟩ := htorus pF kF hodd hq5 r hr hr2 hrp Y hY
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : IsCyclic Y := isCyclic_of_prime_card hY
  haveI : IsMulCommutative Y := IsCyclic.isMulCommutative
  have hle : Y ≤ Subgroup.centralizer
      (Y : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF))) :=
    Subgroup.le_centralizer Y
  have hdvd : r ∣ Nat.card (Subgroup.centralizer
      (Y : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))) := by
    rw [← hY]; exact Subgroup.card_dvd_of_le hle
  -- `k` and `k'` differ by `1`, and `{2k, 2k'} = {q+1, q-1}`.
  have hkd : k = k' + 1 ∨ k' = k + 1 := by
    rcases hdisj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; omega
    · right; omega
  -- since `r ∣ k` and `k, k'` are coprime, `r ∤ k'`.
  have hndvd : ¬ r ∣ k' := by
    intro h
    rcases hkd with hk | hk
    · have h1 : k - k' = 1 := by omega
      have hd : r ∣ k - k' := Nat.dvd_sub hrk h
      rw [h1] at hd
      have hle1 := Nat.le_of_dvd (by norm_num) hd
      have h2 := hr.two_le
      omega
    · have h1 : k' - k = 1 := by omega
      have hd : r ∣ k' - k := Nat.dvd_sub h hrk
      rw [h1] at hd
      have hle1 := Nat.le_of_dvd (by norm_num) hd
      have h2 := hr.two_le
      omega
  have hc : Nat.card (Subgroup.centralizer
        (Y : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))) = k ∨
      Nat.card (Subgroup.centralizer
        (Y : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))) = k' := by
    rcases h2card with h | h <;> rcases hdisj with ⟨a, b⟩ | ⟨a, b⟩ <;> omega
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  rcases hc with hc | hc
  · rw [hc]
  · exact absurd (hc ▸ hdvd) hndvd

end Work.CORE4.Counting
