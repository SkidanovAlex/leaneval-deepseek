import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.indicator_sigmaStrataFinset_incl_excl
import Submission.Work.KMTAreas.iwSL
import Submission.Work.KMTAreas.iwArithFreqs_subset_sigmaLe

namespace Work.KMTAreas

open Work.Analysis.IonescuWainger
open Work.BourgainPlan.IonescuWainger (QA arcPt sigmaSubAFinset mem_sigmaSubAFinset_iff_dvd_addOrderOf)

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem exists_iwSL_witness_sigmaSubAFinset (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l : ℕ}
    (hl : Work.Analysis.IonescuWainger.iwC0 ρ < l)
    {α : Work.Analysis.IonescuWainger.Circle}
    (hα : α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l) :
    ∃ A : Finset ℕ, A ⊆ Work.KMTAreas.iwSL ρ l ∧
      Work.Analysis.IonescuWainger.iwQ0 ρ l ∈ A ∧
      A.card ≤ Work.Analysis.IonescuWainger.iwD ρ + 1 ∧
      α ∈ Work.BourgainPlan.IonescuWainger.sigmaSubAFinset A := by
  classical
  obtain ⟨q, hqP, hqα⟩ := mem_iwArithFreqs.mp hα
  rw [mem_iwP] at hqP
  rcases hqP with ⟨hle, -⟩ | ⟨-, hqc⟩
  · exact absurd hle (not_le.mpr hl)
  obtain ⟨Q, hQ, w, hw, hqw⟩ := mem_iwPconcrete.mp hqc
  rw [hqw] at hqα
  have hD : iwD ρ ≠ 0 := Nat.succ_ne_zero _
  have hw_card : w.factorization.support.card ≤ iwD ρ := (mem_iwW.mp hw).2
  have hw_ne : w ≠ 0 := (pos_of_mem_iwW hw).ne'
  have hsupp : ∀ p ∈ w.factorization.support,
      p ∈ iwPrimeRange ρ l ∧ w.factorization p ≤ iwD ρ := by
    intro p hp
    have hne : w.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
    have h := iwW_factorization_le (ρ := ρ) (l := l) (q := p) hw
    by_cases hin : p ∈ iwPrimeRange ρ l
    · rw [if_pos hin] at h; exact ⟨hin, h⟩
    · rw [if_neg hin] at h; exact absurd (Nat.le_zero.mp h) hne
  have hw_dvd_supp : w ∣ ∏ p ∈ w.factorization.support, p ^ iwD ρ := by
    have hdvd' : (w.factorization.support).prod (fun p => p ^ w.factorization p) ∣
        (w.factorization.support).prod (fun p => p ^ iwD ρ) :=
      Finset.prod_dvd_prod_of_dvd _ _ (fun p hp => pow_dvd_pow p (hsupp p hp).2)
    have hfac : (w.factorization.support).prod (fun p => p ^ w.factorization p) = w :=
      Nat.prod_factorization_pow_eq_self hw_ne
    rwa [hfac] at hdvd'
  refine ⟨insert (iwQ0 ρ l) ((w.factorization.support).image (fun p => p ^ iwD ρ)),
    ?_, Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro a ha
    rw [iwSL]
    rw [Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · exact Finset.mem_insert_self _ _
    · rw [Finset.mem_image] at ha
      obtain ⟨p, hp, rfl⟩ := ha
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, (hsupp p hp).1, rfl⟩)
  · have him : ((w.factorization.support).image (fun p => p ^ iwD ρ)).card
        ≤ w.factorization.support.card := Finset.card_image_le
    have hci := Finset.card_insert_le (iwQ0 ρ l)
      ((w.factorization.support).image (fun p => p ^ iwD ρ))
    omega
  · have h2A : ∀ a ∈ insert (iwQ0 ρ l)
        ((w.factorization.support).image (fun p => p ^ iwD ρ)), 2 ≤ a := by
      intro a ha
      rw [Finset.mem_insert] at ha
      rcases ha with rfl | ha
      · exact two_le_iwQ0 ρ hρ l
      · rw [Finset.mem_image] at ha
        obtain ⟨p, hp, rfl⟩ := ha
        have hpprime : p.Prime := (IwMono.mem_iwPrimeRange_iff.mp (hsupp p hp).1).2.2
        calc 2 ≤ p := hpprime.two_le
          _ ≤ p ^ iwD ρ := Nat.le_self_pow hD p
    refine (mem_sigmaSubAFinset_iff_dvd_addOrderOf h2A α).mpr ?_
    have hdvd : (Q * w) ∣ QA (insert (iwQ0 ρ l)
        ((w.factorization.support).image (fun p => p ^ iwD ρ))) := by
      have hdisj : iwQ0 ρ l ∉ (w.factorization.support).image (fun p => p ^ iwD ρ) := by
        intro hmem
        rw [Finset.mem_image] at hmem
        obtain ⟨p, hp, hpe⟩ := hmem
        exact iwQ0_ne_pow_iwD (hsupp p hp).1 hpe.symm
      have hprod : QA (insert (iwQ0 ρ l)
            ((w.factorization.support).image (fun p => p ^ iwD ρ)))
          = iwQ0 ρ l * ∏ p ∈ w.factorization.support, p ^ iwD ρ := by
        rw [QA, Finset.prod_insert hdisj]
        congr 1
        simpa using Finset.prod_image (s := w.factorization.support)
          (g := fun p => p ^ iwD ρ) (f := id)
          (fun x _ y _ hxy => Nat.pow_left_injective hD hxy)
      rw [hprod]
      exact mul_dvd_mul (Nat.mem_divisors.mp hQ).1 hw_dvd_supp
    exact dvd_trans (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hqα) hdvd

end Work.KMTAreas
