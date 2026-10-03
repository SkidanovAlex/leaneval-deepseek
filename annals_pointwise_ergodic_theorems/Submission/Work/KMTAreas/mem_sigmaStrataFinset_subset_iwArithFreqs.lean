import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.StrataCompDefs
import Submission.Work.KMTAreas.iwArithFreqs_subset_sigmaLe
import Submission.Work.KMTAreas.prod_primePow_mem_iwW
import Submission.Work.KMTAreas.coprime_prod_primePow_iwQ0
import Submission.Work.KMTAreas.arcPt_one_mem_sigmaStrataFinset

/-!
# Which strata of the Ionescu–Wainger denominator set lie inside `(ℚ/ℤ)_{≤l}`

Let `ρ ∈ (0,1]`, `l > C⁰_ρ` (the regime where `P_{≤l} = iwPconcrete ρ l`), and let

  `S₀ = {Q_0^{(l)}} ∪ {p^{D_ρ} : p ∈ (N_0^{(l)}, 2^l] prime}`

be the "Tao denominator set" of Appendix A of Krause–Mirek–Tao.  For a finite `A ⊆ S₀` of
cardinality at most `D_ρ + 1` we characterise exactly when Tao's stratum `Σ_A` is contained in
the Ionescu–Wainger arithmetic frequency set `(ℚ/ℤ)_{≤l} = iwArithFreqs ρ l`:

  `Σ_A ⊆ (ℚ/ℤ)_{≤l}  ⟺  Q_0^{(l)} ∈ A  or  #A ≤ D_ρ`.

Indeed `q ∈ P_{≤l}` means `q = Q·w` with `Q ∣ Q_0^{(l)}` and `w` a product of at most `D_ρ`
distinct primes of the range (exponents `≤ D_ρ`), so a product of at most `D_ρ` such prime
powers is admissible, and adjoining `Q_0^{(l)}` one more; while `D_ρ + 1` distinct prime powers
`p^{D_ρ}`, `p` in the range, are *not* admissible, because their primes are coprime to every
prime factor of `Q_0^{(l)}` and there are more of them than `W_{≤l}` allows.
-/

namespace Work.KMTAreas

open Work.Analysis.IonescuWainger
open Work.BourgainPlan.IonescuWainger (QA arcPt sigmaStrataFinset sigmaSubAFinset
  QA_ne_zero sigmaStrataFinset_subset_sigmaSubAFinset zsmul_arcPt_eq_zero
  dvd_of_zsmul_arcPt_eq_zero)

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- Every element of the prime range `(N_0^{(l)}, 2^l]` is prime. -/
private lemma mem_iwPrimeRange_prime {ρ : ℝ} {l p : ℕ} (hp : p ∈ iwPrimeRange ρ l) :
    p.Prime := by
  rw [iwPrimeRange] at hp
  exact (Finset.mem_filter.mp hp).2

/-- Every element of the prime range is at least `2`. -/
private lemma two_le_of_mem_iwPrimeRange {ρ : ℝ} {l p : ℕ} (hp : p ∈ iwPrimeRange ρ l) :
    2 ≤ p := (mem_iwPrimeRange_prime hp).two_le

/-- **The structure of a subset of the Tao denominator set.**  For
`A ⊆ insert Q_0^{(l)} {p^{D_ρ}}`, removing `Q_0^{(l)}` leaves exactly the image of the primes
`p` of the range with `p^{D_ρ} ∈ A` (the element `Q_0^{(l)}` is never of the shape `p^{D_ρ}`). -/
private lemma erase_iwQ0_eq_image {ρ : ℝ} {l : ℕ} {A : Finset ℕ}
    (hAsub : A ⊆ insert (iwQ0 ρ l) ((iwPrimeRange ρ l).image (fun p => p ^ iwD ρ))) :
    A.erase (iwQ0 ρ l) =
      ((iwPrimeRange ρ l).filter (fun p => p ^ iwD ρ ∈ A)).image (fun p => p ^ iwD ρ) := by
  ext a
  constructor
  · intro ha
    rw [Finset.mem_erase] at ha
    obtain ⟨haQ0, haA⟩ := ha
    rw [Finset.mem_image]
    have h := hAsub haA
    rw [Finset.mem_insert] at h
    rcases h with h | h
    · exact absurd h haQ0
    · rw [Finset.mem_image] at h
      obtain ⟨p, hp, hpa⟩ := h
      exact ⟨p, Finset.mem_filter.mpr ⟨hp, by rw [hpa]; exact haA⟩, hpa⟩
  · intro ha
    rw [Finset.mem_image] at ha
    obtain ⟨p, hp, hpa⟩ := ha
    rw [Finset.mem_filter] at hp
    obtain ⟨hpP, hpA⟩ := hp
    rw [Finset.mem_erase]
    refine ⟨?_, by rw [← hpa]; exact hpA⟩
    intro h
    exact iwQ0_ne_pow_iwD hpP (h.symm.trans hpa.symm)

theorem mem_sigmaStrataFinset_subset_iwArithFreqs (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {l : ℕ} (hl : Work.Analysis.IonescuWainger.iwC0 ρ < l) {A : Finset ℕ}
    (hAsub : A ⊆ insert (Work.Analysis.IonescuWainger.iwQ0 ρ l)
      ((Work.Analysis.IonescuWainger.iwPrimeRange ρ l).image
        (fun p => p ^ Work.Analysis.IonescuWainger.iwD ρ)))
    (hAcard : A.card ≤ Work.Analysis.IonescuWainger.iwD ρ + 1) :
    Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A ⊆
        Work.Analysis.IonescuWainger.iwArithFreqs ρ l ↔
      (Work.Analysis.IonescuWainger.iwQ0 ρ l ∈ A ∨ A.card ≤ Work.Analysis.IonescuWainger.iwD ρ) := by
  classical
  have hD : iwD ρ ≠ 0 := Nat.succ_ne_zero _
  have hinj : Function.Injective (fun p : ℕ => p ^ iwD ρ) := Nat.pow_left_injective hD
  set S : Finset ℕ := (iwPrimeRange ρ l).filter (fun p => p ^ iwD ρ ∈ A) with hSdef
  set w : ℕ := S.prod (fun p => p ^ iwD ρ) with hwdef
  have hSp : S ⊆ iwPrimeRange ρ l := fun p hp => (Finset.mem_filter.mp hp).1
  have hSmem : ∀ p ∈ S, p ^ iwD ρ ∈ A := fun p hp => (Finset.mem_filter.mp hp).2
  have hPearase : A.erase (iwQ0 ρ l) = S.image (fun p => p ^ iwD ρ) := by
    rw [hSdef]; exact erase_iwQ0_eq_image hAsub
  have hcard_image : (S.image (fun p => p ^ iwD ρ)).card = S.card :=
    Finset.card_image_of_injective _ hinj
  have hQA_image : QA (S.image (fun p => p ^ iwD ρ)) = w := by
    have h : (S.image (fun p => p ^ iwD ρ)).prod (fun x => x) = S.prod (fun p => p ^ iwD ρ) :=
      Finset.prod_image (f := fun x : ℕ => x) (g := fun p : ℕ => p ^ iwD ρ) (s := S)
        (fun x _ y _ hxy => hinj hxy)
    rw [hwdef]; exact h
  -- every element of `A` is nonzero, so `Q_A ≠ 0`
  have hA_ne : ∀ q ∈ A, q ≠ 0 := by
    intro q hq
    have h := hAsub hq
    rw [Finset.mem_insert] at h
    rcases h with h | h
    · rw [h]; exact iwQ0_ne_zero ρ l
    · rw [Finset.mem_image] at h
      obtain ⟨p, hp, hpq⟩ := h
      rw [← hpq]
      exact pow_ne_zero _ (mem_iwPrimeRange_prime hp).ne_zero
  have hQA_ne : QA A ≠ 0 := QA_ne_zero hA_ne
  -- the inclusion holds as soon as `Q_A ∈ P_{≤l}`
  have hAQArith : QA A ∈ iwP ρ l → sigmaStrataFinset A ⊆ iwArithFreqs ρ l := by
    intro hmemP β hβ
    have hβ' := sigmaStrataFinset_subset_sigmaSubAFinset A hβ
    rw [sigmaSubAFinset, Finset.mem_image] at hβ'
    obtain ⟨a, -, rfl⟩ := hβ'
    rw [mem_iwArithFreqs]
    refine ⟨QA A, hmemP, ?_⟩
    rw [← natCast_zsmul]
    exact zsmul_arcPt_eq_zero hQA_ne dvd_rfl
  -- `w ∈ W_{≤l}` whenever `#S ≤ D_ρ`
  have hwW_of_card : S.card ≤ iwD ρ → w ∈ iwW ρ l := by
    intro hcardS
    rw [hwdef]; exact prod_primePow_mem_iwW hSp hcardS
  -- the case `Q_0^{(l)} ∈ A`: only the bound `#A ≤ D_ρ + 1` is used
  have hcaseQ0 : iwQ0 ρ l ∈ A → QA A ∈ iwP ρ l := by
    intro hQ0
    have hAeq : A = insert (iwQ0 ρ l) (S.image (fun p => p ^ iwD ρ)) := by
      rw [← Finset.insert_erase hQ0, hPearase]
    have hQ0notmem : iwQ0 ρ l ∉ S.image (fun p => p ^ iwD ρ) := by
      rw [Finset.mem_image]
      rintro ⟨p, hp, hpe⟩
      exact iwQ0_ne_pow_iwD (hSp hp) hpe.symm
    have hcardS : S.card ≤ iwD ρ := by
      have h1 : A.card = S.card + 1 := by
        rw [hAeq, Finset.card_insert_of_notMem hQ0notmem, hcard_image]
      omega
    have hQAeq : QA A = iwQ0 ρ l * w := by
      rw [hAeq]
      have h : (insert (iwQ0 ρ l) (S.image (fun p => p ^ iwD ρ))).prod (fun q => q)
          = iwQ0 ρ l * w := by
        rw [Finset.prod_insert hQ0notmem]
        rw [← hQA_image]
        rfl
      exact h
    rw [mem_iwP]
    exact Or.inr ⟨hl, mem_iwPconcrete.mpr
      ⟨iwQ0 ρ l, Nat.mem_divisors.mpr ⟨dvd_rfl, iwQ0_ne_zero ρ l⟩, w,
        hwW_of_card hcardS, hQAeq⟩⟩
  -- the case `Q_0^{(l)} ∉ A`, `#A ≤ D_ρ`
  have hcaseNotQ0 : iwQ0 ρ l ∉ A → A.card ≤ iwD ρ → QA A ∈ iwP ρ l := by
    intro hQ0 hcard
    have hAeq : A = S.image (fun p => p ^ iwD ρ) := by
      rw [← hPearase, Finset.erase_eq_of_notMem hQ0]
    have hcardS : S.card ≤ iwD ρ := by
      have h1 : A.card = S.card := by rw [hAeq, hcard_image]
      omega
    have hQAeq : QA A = 1 * w := by rw [hAeq, hQA_image, one_mul]
    rw [mem_iwP]
    exact Or.inr ⟨hl, mem_iwPconcrete.mpr
      ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, iwQ0_ne_zero ρ l⟩, w,
        hwW_of_card hcardS, hQAeq⟩⟩
  constructor
  · -- (⇒) contrapositive: `Q_0^{(l)} ∉ A` and `#A = D_ρ + 1` forbid the inclusion
    intro hL
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hQ0not, hcardgt⟩ := hcon
    have hcard_eq : A.card = iwD ρ + 1 := by omega
    have hAeq : A = S.image (fun p => p ^ iwD ρ) := by
      rw [← hPearase, Finset.erase_eq_of_notMem hQ0not]
    have hcardS : S.card = iwD ρ + 1 := by
      have h1 : A.card = S.card := by rw [hAeq, hcard_image]
      omega
    have hQAeq : QA A = w := by rw [hAeq, hQA_image]
    have h2A : ∀ a ∈ A, 2 ≤ a := by
      intro a ha
      have h := hAsub ha
      rw [Finset.mem_insert] at h
      rcases h with h | h
      · exact absurd (h ▸ ha) hQ0not
      · rw [Finset.mem_image] at h
        obtain ⟨p, hp, hpa⟩ := h
        rw [← hpa]
        exact le_trans (two_le_of_mem_iwPrimeRange hp) (Nat.le_self_pow hD p)
    have hβmem : arcPt (QA A) 1 ∈ sigmaStrataFinset A := arcPt_one_mem_sigmaStrataFinset h2A
    have hβnot : arcPt (QA A) 1 ∉ iwArithFreqs ρ l := by
      intro hβ
      rw [mem_iwArithFreqs] at hβ
      obtain ⟨q, hqP, hqβ⟩ := hβ
      rw [mem_iwP] at hqP
      rcases hqP with ⟨hle, -⟩ | ⟨-, hqc⟩
      · exact absurd hle (not_le.mpr hl)
      · rw [mem_iwPconcrete] at hqc
        obtain ⟨Q, hQmem, w', hw', hqeq⟩ := hqc
        have hQdvd : Q ∣ iwQ0 ρ l := (Nat.mem_divisors.mp hQmem).1
        -- `Q_A` divides `q`
        have hqβ' : (q : ℤ) • arcPt (QA A) 1 = 0 := by
          rw [natCast_zsmul]; exact hqβ
        have hdvd : QA A ∣ q :=
          dvd_of_zsmul_arcPt_eq_zero hQA_ne (by simpa using Nat.coprime_one_left (QA A)) hqβ'
        -- `Q_A` is coprime to `Q`, hence divides `w'`
        have hw'ne : w' ≠ 0 := by
          rintro rfl
          exact absurd ((mem_iwW.mp hw').1) (by
            rw [zero_dvd_iff]; exact iwProd_ne_zero ρ l)
        have hcop : Nat.Coprime (QA A) Q := by
          rw [hQAeq]; exact coprime_prod_primePow_iwQ0 hSp hQdvd
        have hQA_dvd_w' : QA A ∣ w' := by
          refine hcop.dvd_of_dvd_mul_left ?_
          rw [hqeq] at hdvd; exact hdvd
        -- the primes of `S` are prime divisors of `w'`
        have hSsub : S ⊆ w'.factorization.support := by
          intro p hp
          have hpP : p ∈ iwPrimeRange ρ l := hSp hp
          have hp_dvd_QA : p ∣ QA A := by
            have h1 : p ^ iwD ρ ∣ QA A := by
              rw [hQAeq]
              exact Finset.dvd_prod_of_mem (fun p => p ^ iwD ρ) hp
            exact dvd_trans (dvd_pow_self p hD) h1
          have hp_dvd_w' : p ∣ w' := dvd_trans hp_dvd_QA hQA_dvd_w'
          rw [Finsupp.mem_support_iff]
          intro hzero
          have h1 := (Nat.Prime.dvd_iff_one_le_factorization (mem_iwPrimeRange_prime hpP)
            hw'ne).mp hp_dvd_w'
          omega
        have hcardw' : w'.factorization.support.card ≤ iwD ρ := (mem_iwW.mp hw').2
        have := Finset.card_le_card hSsub
        omega
    exact hβnot (hL hβmem)
  · -- (⇐)
    intro hR
    have hmemP : QA A ∈ iwP ρ l := by
      by_cases hQ0 : iwQ0 ρ l ∈ A
      · exact hcaseQ0 hQ0
      · exact hcaseNotQ0 hQ0 (by
          rcases hR with h | h
          · exact absurd h hQ0
          · exact h)
    exact hAQArith hmemP

end Work.KMTAreas
