import Mathlib
import Submission.Work.FIArea7.smallCInner2EpsAux.peelBigEpsDefs
import Submission.Work.FIArea7.smallCInner2EpsAux.peelSmallAux

set_option maxHeartbeats 2000000

namespace Work.FIArea7.smallCInner2EpsAux

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `⌊u/(z+1)⌋ < p` and `z < q` force `p*q > u`. -/
private lemma peelBigM_lt_mul_gt {u z p q : ℕ} (hz : 1 ≤ z) (hM : peelBigM u z < p)
    (hzq : z < q) : u < p * q := by
  rw [peelBigM] at hM
  have hdecomp : (z + 1) * (u / (z + 1)) + u % (z + 1) = u := Nat.div_add_mod u (z + 1)
  have hmod : u % (z + 1) < z + 1 := Nat.mod_lt u (by omega)
  have h2 : u < (u / (z + 1) + 1) * (z + 1) := by
    have h2' : u < (z + 1) * (u / (z + 1)) + (z + 1) := by
      calc u = (z + 1) * (u / (z + 1)) + u % (z + 1) := hdecomp.symm
        _ < (z + 1) * (u / (z + 1)) + (z + 1) := by omega
    have h4 : (z + 1) * (u / (z + 1)) + (z + 1) ≤ (u / (z + 1) + 1) * (z + 1) := by
      have he : (u / (z + 1) + 1) * (z + 1) = (z + 1) * (u / (z + 1)) + (z + 1) := by ring
      rw [he]
    exact lt_of_lt_of_le h2' h4
  have h3 : (u / (z + 1) + 1) * (z + 1) ≤ p * q := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- The count of primes `z < r ≤ u` dividing `p*q` is `ν(q,z)+1`. -/
private lemma nu_identity (u z p q : ℕ) (hp : p.Prime) (hzp : z < p) (hzq : z < q)
    (hle : p * q ≤ u) (hnd : ¬ p ∣ q) :
    Work.FIArea7.largePrimeCount u z (p * q) = Work.FIArea7.largePrimeCount u z q + 1 := by
  have hp1 : 1 ≤ p := hp.one_le
  have hpu : p ≤ u := by
    have : p * 1 ≤ p * q := Nat.mul_le_mul_left p (by omega)
    exact le_trans (by simpa using this) hle
  have hset : (Finset.Icc 1 u).filter (fun r => r.Prime ∧ z < r ∧ r ∣ p * q)
      = insert p ((Finset.Icc 1 u).filter (fun r => r.Prime ∧ z < r ∧ r ∣ q)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
    constructor
    · rintro ⟨⟨hr1, hru⟩, hrp, hzr, hrdvd⟩
      rcases (Nat.Prime.dvd_mul hrp).mp hrdvd with h | h
      · rcases hp.eq_one_or_self_of_dvd r h with h1 | h1
        · exact absurd h1 hrp.ne_one
        · exact Or.inl h1
      · exact Or.inr ⟨⟨hr1, hru⟩, hrp, hzr, h⟩
    · rintro (h | ⟨⟨hr1, hru⟩, hrp, hzr, hrdvd⟩)
      · rw [h]
        exact ⟨⟨hp1, hpu⟩, hp, hzp, Dvd.dvd.mul_right (dvd_refl p) q⟩
      · exact ⟨⟨hr1, hru⟩, hrp, hzr, Dvd.dvd.mul_left hrdvd p⟩
  have hnotmem : p ∉ (Finset.Icc 1 u).filter (fun r => r.Prime ∧ z < r ∧ r ∣ q) := by
    intro hmem
    rw [Finset.mem_filter] at hmem
    exact hnd hmem.2.2.2
  have hcard : ((Finset.Icc 1 u).filter (fun r => r.Prime ∧ z < r ∧ r ∣ p * q)).card
      = ((Finset.Icc 1 u).filter (fun r => r.Prime ∧ z < r ∧ r ∣ q)).card + 1 := by
    rw [hset, Finset.card_insert_of_notMem hnotmem]
  simp only [Work.FIArea7.largePrimeCount]
  exact hcard

theorem peelBig2_eq_bilin_sub_diag
    (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (k : ℤ) (c u z : ℕ) (P : ℝ → ℝ)
    (hz : 1 ≤ z) :
    Work.FIArea7.smallCInner2EpsAux.peelBig2 u z (Work.FIArea7.smallCInner2EpsAux.cTerm Pa chi k c P)
      = Work.FIArea7.smallCInner2EpsAux.peelBilinSum Pa chi k c u z P
        - Work.FIArea7.smallCInner2EpsAux.peelDiagSum Pa chi k c u z P := by
  set A : ℕ → ℕ → ℂ := fun p q =>
    (if p.Prime ∧ z < p ∧ z < q then
      (if Squarefree (p * q) ∧ p * q ≤ u then
        cTerm Pa chi k c P (p * q) / ((Work.FIArea7.largePrimeCount u z (p * q) : ℕ) : ℂ) else 0)
    else 0) with hAdef
  have hAf : ∀ p q, A p q =
      (if p.Prime ∧ z < p ∧ z < q then
        (if Squarefree (p * q) ∧ p * q ≤ u then
          cTerm Pa chi k c P (p * q) / ((Work.FIArea7.largePrimeCount u z (p * q) : ℕ) : ℂ) else 0)
      else 0) := fun p q => by simp only [hAdef]
  have hpoint : ∀ p q : ℕ, (if ¬ p ∣ q then peelT Pa chi k c u z P p q else 0) = A p q := by
    intro p q
    rw [hAf p q]
    by_cases hcond : p.Prime ∧ z < p ∧ z < q
    · rw [if_pos hcond]
      by_cases hpq : p ∣ q
      · rw [if_neg (fun h => h hpq)]
        rw [if_neg]
        intro h
        exact (Nat.squarefree_iff_prime_squarefree.mp h.1) p hcond.1 (mul_dvd_mul_left p hpq)
      · rw [if_pos hpq]
        by_cases hmn : p * q ≤ u
        · have hCop : Nat.Coprime p q := hcond.1.coprime_iff_not_dvd.mpr hpq
          have hAp : peelA Pa c z p = (ArithmeticFunction.moebius p : ℂ)
              * Work.FIArea7.nspInd Pa p * (if Nat.Coprime c p then (1:ℂ) else 0) := by
            unfold peelA; rw [if_pos ⟨hcond.1, hcond.2.1⟩]
          have hBq : peelB Pa c u z q = (ArithmeticFunction.moebius q : ℂ)
              * Work.FIArea7.nspInd Pa q * (if Nat.Coprime c q then (1:ℂ) else 0)
              * (((1 + Work.FIArea7.largePrimeCount u z q : ℕ):ℂ))⁻¹ := by
            unfold peelB; rw [if_pos hcond.2.2]
          have hmu : ((ArithmeticFunction.moebius (p*q) : ℤ) : ℂ)
              = ((ArithmeticFunction.moebius p : ℤ):ℂ) * ((ArithmeticFunction.moebius q : ℤ):ℂ) := by
            rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hCop.gcd_eq_one]
            push_cast; ring
          have h1nu : (1 + Work.FIArea7.largePrimeCount u z q : ℕ)
              = Work.FIArea7.largePrimeCount u z (p*q) := by
            have := nu_identity u z p q hcond.1 hcond.2.1 hcond.2.2 hmn hpq
            omega
          have hcoef : peelA Pa c z p * peelB Pa c u z q
              = (if Nat.Coprime c (p*q) then (1:ℂ) else 0) * Work.FIArea7.nspInd Pa (p*q)
                * (ArithmeticFunction.moebius (p*q) : ℂ)
                * (((Work.FIArea7.largePrimeCount u z (p*q):ℕ):ℂ))⁻¹ := by
            rw [hAp, hBq, coprimeInd_mul c p q, Work.FIArea7.nspInd_mul Pa hCop, hmu, h1nu]
            ring
          by_cases hsq : Squarefree (p * q)
          · rw [if_pos ⟨hsq, hmn⟩]
            unfold peelT cTerm
            rw [if_pos hmn]
            by_cases hcc : Nat.Coprime c (p*q)
            · rw [if_pos hcc, hcoef, if_pos hcc]
              ring
            · rw [if_neg hcc, hcoef, if_neg hcc]
              ring
          · rw [if_neg (fun h => hsq h.1)]
            have hmu0 : (ArithmeticFunction.moebius (p*q) : ℂ) = 0 := by
              rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq, Int.cast_zero]
            unfold peelT
            rw [if_pos hmn, hcoef, hmu0]
            ring
        · rw [if_neg (fun h => hmn h.2)]
          unfold peelT
          rw [if_neg hmn]
    · rw [if_neg hcond]
      by_cases hpq : p ∣ q
      · rw [if_neg (fun h => h hpq)]
      · rw [if_pos hpq]
        have hzero : peelT Pa chi k c u z P p q = 0 := by
          unfold peelT
          by_cases hmn : p * q ≤ u
          · rw [if_pos hmn]
            have hfac : peelA Pa c z p = 0 ∨ peelB Pa c u z q = 0 := by
              rcases not_and_or.mp hcond with h1 | h1
              · exact Or.inl (by unfold peelA; rw [if_neg (fun h => h1 h.1)])
              · rcases not_and_or.mp h1 with h2 | h2
                · exact Or.inl (by unfold peelA; rw [if_neg (fun h => h2 h.2)])
                · exact Or.inr (by unfold peelB; rw [if_neg h2])
            rcases hfac with h | h <;> rw [h] <;> ring
          · rw [if_neg hmn]
        rw [hzero]
  have hL : Work.FIArea7.smallCInner2EpsAux.peelBig2 u z (Work.FIArea7.smallCInner2EpsAux.cTerm Pa chi k c P)
      = ∑ p ∈ Finset.Icc 1 u, ∑ q ∈ Finset.Icc 1 u, A p q := by
    rw [peelBig2]
    simp only [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hp : p.Prime ∧ z < p
    · rw [if_pos hp]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      by_cases hq : z < q
      · rw [if_pos hq, hAf p q, if_pos (show p.Prime ∧ z < p ∧ z < q from ⟨hp.1, hp.2, hq⟩)]
      · rw [if_neg hq, hAf p q, if_neg (fun h : p.Prime ∧ z < p ∧ z < q => hq h.2.2)]
    · rw [if_neg hp]
      exact (Finset.sum_eq_zero (fun q _ => by
        rw [hAf p q, if_neg (fun h => hp ⟨h.1, h.2.1⟩)])).symm
  have hR : Work.FIArea7.smallCInner2EpsAux.peelBilinSum Pa chi k c u z P
        - Work.FIArea7.smallCInner2EpsAux.peelDiagSum Pa chi k c u z P
      = ∑ p ∈ Finset.Icc 1 (peelBigM u z), ∑ q ∈ Finset.Icc 1 (peelBigM u z), A p q := by
    rw [peelBilinSum, peelDiagSum]
    simp only [Finset.sum_filter]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [← hpoint p q]
    by_cases hpq : p ∣ q
    · rw [if_pos hpq, if_neg (fun h => h hpq)]; ring
    · rw [if_neg hpq, if_pos hpq]; ring
  have hred : (∑ p ∈ Finset.Icc 1 u, ∑ q ∈ Finset.Icc 1 u, A p q)
      = ∑ p ∈ Finset.Icc 1 (peelBigM u z), ∑ q ∈ Finset.Icc 1 (peelBigM u z), A p q := by
    have hsub : Finset.Icc 1 (peelBigM u z) ⊆ Finset.Icc 1 u := by
      intro p hp; rw [Finset.mem_Icc] at hp ⊢
      exact ⟨hp.1, le_trans hp.2 (Nat.div_le_self u (z + 1))⟩
    have houter : (∑ p ∈ Finset.Icc 1 (peelBigM u z), ∑ q ∈ Finset.Icc 1 u, A p q)
        = ∑ p ∈ Finset.Icc 1 u, ∑ q ∈ Finset.Icc 1 u, A p q := by
      refine Finset.sum_subset hsub (fun p hp hpn => ?_)
      refine Finset.sum_eq_zero (fun q _ => ?_)
      rw [Finset.mem_Icc] at hp
      have hMp : peelBigM u z < p := by
        by_contra hcon
        exact hpn (Finset.mem_Icc.mpr ⟨hp.1, by omega⟩)
      by_cases hcond : p.Prime ∧ z < p ∧ z < q
      · rw [hAf p q, if_pos hcond, if_neg]
        intro h
        exact absurd (peelBigM_lt_mul_gt hz hMp hcond.2.2) (not_lt.mpr h.2)
      · rw [hAf p q, if_neg hcond]
    rw [← houter]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mem_Icc] at hp
    refine (Finset.sum_subset hsub (fun q hq hqn => ?_)).symm
    rw [Finset.mem_Icc] at hq
    have hMq : peelBigM u z < q := by
      by_contra hcon
      exact hqn (Finset.mem_Icc.mpr ⟨hq.1, by omega⟩)
    by_cases hcond : p.Prime ∧ z < p ∧ z < q
    · rw [hAf p q, if_pos hcond, if_neg]
      intro h
      exact absurd (by rw [mul_comm]; exact peelBigM_lt_mul_gt hz hMq hcond.2.1) (not_lt.mpr h.2)
    · rw [hAf p q, if_neg hcond]
  rw [hL, hR, hred]

end

end Work.FIArea7.smallCInner2EpsAux
