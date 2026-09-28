import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.DNC.moebius_dvdVec_sum
import Submission.Work.HP.DNC.int_smul_facts
import Submission.Work.HP.DNC.gcd_natAbs_le_floor

noncomputable section
open Finset Work.HP
namespace Work.HP.DNC

def box {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ℝ) : Finset (ι → ℤ) :=
  Fintype.piFinset (fun _ : ι => Finset.Icc (-((⌈A⌉₊ : ℕ) : ℤ)) ((⌈A⌉₊ : ℕ) : ℤ))

lemma mem_box_of_eNorm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ℝ) {a : ι → ℤ}
    (ha : eNorm a ≤ A) : a ∈ box A := by
  rw [box, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hle : |(a i : ℝ)| ≤ eNorm a := by
    have h1 : ((a i : ℝ))^2 ≤ ∑ j, ((a j : ℝ))^2 :=
      Finset.single_le_sum (f := fun j => ((a j : ℝ))^2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    simpa [eNorm] using Real.abs_le_sqrt h1
  have hA2 : |(a i : ℝ)| ≤ (⌈A⌉₊ : ℝ) := le_trans (le_trans hle ha) (Nat.le_ceil A)
  obtain ⟨h2, h3⟩ := abs_le.1 hA2
  constructor
  · exact_mod_cast (show -((⌈A⌉₊:ℕ):ℝ) ≤ ((a i : ℤ):ℝ) from by linarith)
  · exact_mod_cast (show ((a i : ℤ):ℝ) ≤ ((⌈A⌉₊:ℕ):ℝ) from h3)

lemma ncard_eq_filter_card {α : Type*} {s : Set α} {B : Finset α} [DecidablePred (· ∈ s)]
    (h : s ⊆ ↑B) : s.ncard = (B.filter (· ∈ s)).card := by
  have hfin : s.Finite := B.finite_toSet.subset h
  have htof : hfin.toFinset = B.filter (· ∈ s) := by
    ext x
    rw [Set.Finite.mem_toFinset, Finset.mem_filter]
    exact ⟨fun hx => ⟨h hx, hx⟩, fun hx => hx.2⟩
  rw [Set.ncard_eq_toFinset_card s hfin, htof]

lemma exists_smul_iff_dvd {ι : Type*} [Fintype ι] (k : ℕ) (a : ι → ℤ) :
    (∃ b : ι → ℤ, (k : ℤ) • b = a) ↔ (∀ i, (k : ℤ) ∣ a i) := by
  constructor
  · rintro ⟨b, hb⟩ i
    exact ⟨b i, by have := congr_fun hb i; simpa [Pi.smul_apply, smul_eq_mul] using this.symm⟩
  · intro h
    choose b hb using h
    refine ⟨b, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (hb i).symm

lemma not_isPrim_zero {ι : Type*} [Fintype ι] : ¬ IsPrim (0 : ι → ℤ) := by
  unfold IsPrim
  intro h
  have h0 : Finset.univ.gcd (0 : ι → ℤ) = 0 := Finset.gcd_eq_zero_iff.mpr (by intro x _; rfl)
  rw [h0] at h
  exact absurd h (by norm_num)

theorem moebius_prim_ncard {ι : Type*} [Fintype ι]
    (K : Set (ι → ℝ)) (hK : ∀ (s : ℝ) (t : ι → ℝ), 0 < s → (t ∈ K ↔ s • t ∈ K))
    (P : (ι → ℤ) → Prop) (A : ℝ) (hA : 0 ≤ A) :
    (({a : ι → ℤ | IsPrim a ∧ eNorm a ≤ A ∧ toR a ∈ K ∧ P a}.ncard : ℝ)) =
      ∑ k ∈ Finset.Icc 1 ⌊A⌋₊, (ArithmeticFunction.moebius k : ℝ) *
        (({b : ι → ℤ | b ≠ 0 ∧ eNorm b ≤ A / (k : ℝ) ∧ toR b ∈ K ∧ P ((k : ℤ) • b)}.ncard : ℝ)) := by
  classical
  have hmain : (({a : ι → ℤ | IsPrim a ∧ eNorm a ≤ A ∧ toR a ∈ K ∧ P a}.ncard : ℤ)) =
      ∑ k ∈ Finset.Icc 1 ⌊A⌋₊, (ArithmeticFunction.moebius k : ℤ) *
        (({b : ι → ℤ | b ≠ 0 ∧ eNorm b ≤ A / (k : ℝ) ∧ toR b ∈ K ∧ P ((k : ℤ) • b)}.ncard : ℤ)) := by
    set T : Set (ι → ℤ) := {a | IsPrim a ∧ eNorm a ≤ A ∧ toR a ∈ K ∧ P a} with hT
    set U : Set (ι → ℤ) := {a | a ≠ 0 ∧ eNorm a ≤ A ∧ toR a ∈ K ∧ P a} with hU
    set S : ℕ → Set (ι → ℤ) :=
      (fun k => {b | b ≠ 0 ∧ eNorm b ≤ A / (k : ℝ) ∧ toR b ∈ K ∧ P ((k : ℤ) • b)}) with hS
    set G : Finset ℕ := Finset.Icc 1 ⌊A⌋₊ with hG
    set Bx : Finset (ι → ℤ) := box A with hBx
    have hUmem : ∀ a, a ∈ U ↔ a ≠ 0 ∧ eNorm a ≤ A ∧ toR a ∈ K ∧ P a := by
      intro a; simp only [hU, Set.mem_setOf_eq]
    have hTmem : ∀ a, a ∈ T ↔ IsPrim a ∧ eNorm a ≤ A ∧ toR a ∈ K ∧ P a := by
      intro a; simp only [hT, Set.mem_setOf_eq]
    have hSmem : ∀ k b, b ∈ S k ↔ b ≠ 0 ∧ eNorm b ≤ A / (k:ℝ) ∧ toR b ∈ K ∧ P ((k:ℤ)•b) := by
      intro k b; simp only [hS, Set.mem_setOf_eq]
    have hGmem : ∀ k, k ∈ G ↔ 1 ≤ k ∧ k ≤ ⌊A⌋₊ := by
      intro k; rw [hG]; exact Finset.mem_Icc
    obtain ⟨hN1, hN2, hN3, hN4⟩ := int_smul_facts (ι := ι)
    have hTsub : T ⊆ ↑Bx := by
      intro a ha
      rw [hTmem] at ha
      rw [Finset.mem_coe, hBx]
      exact mem_box_of_eNorm_le A ha.2.1
    have hTU : T ⊆ U := by
      intro a ha
      rw [hTmem] at ha
      rw [hUmem]
      refine ⟨?_, ha.2.1, ha.2.2.1, ha.2.2.2⟩
      intro h0
      rw [h0] at ha
      exact not_isPrim_zero ha.1
    have hSsub : ∀ k, S k ⊆ ↑Bx := by
      intro k b hb
      rw [hSmem k b] at hb
      rw [Finset.mem_coe, hBx]
      apply mem_box_of_eNorm_le
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0] at hb
        simp only [Nat.cast_zero, div_zero] at hb
        exact hb.2.1.trans hA
      · have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hkpos
        have hk0' : (0:ℝ) < (k:ℝ) := by exact_mod_cast hkpos
        have hdiv : A / (k:ℝ) ≤ A := by
          rw [div_le_iff₀ hk0']; simpa using mul_le_mul_of_nonneg_left hk1 hA
        linarith [hb.2.1]
    have hcard : ∀ k, 1 ≤ k → (S k).ncard
        = (Bx.filter (fun a => a ∈ U ∧ ∃ b, (k:ℤ)•b = a)).card := by
      intro k hk
      rw [ncard_eq_filter_card (hSsub k)]
      rw [← Finset.card_image_of_injOn (f := fun b => (k:ℤ)•b)
        (fun b1 _ b2 _ heq => hN3 k b1 b2 hk heq)]
      congr 1
      ext a
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨b, ⟨hbBx, hbS⟩, hba⟩
        rw [hSmem k b] at hbS
        obtain ⟨hb0, hbA, hbK, hbP⟩ := hbS
        have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast (show (0:ℕ) < k by omega)
        have hmul : (k:ℝ) * (A / (k:ℝ)) = A := by field_simp
        refine ⟨?_, ?_, b, hba⟩
        · apply mem_box_of_eNorm_le
          rw [← hba, hN1]
          calc (k:ℝ) * eNorm b ≤ (k:ℝ) * (A/(k:ℝ)) := mul_le_mul_of_nonneg_left hbA hk0.le
            _ = A := hmul
        · rw [hUmem]
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro h0; exact hb0 ((hN4 k b hk).mp (hba.trans h0))
          · rw [← hba, hN1]
            calc (k:ℝ) * eNorm b ≤ (k:ℝ) * (A/(k:ℝ)) := mul_le_mul_of_nonneg_left hbA hk0.le
              _ = A := hmul
          · rw [← hba, hN2]
            exact (hK (k:ℝ) (toR b) hk0).mp hbK
          · rw [← hba]; exact hbP
      · rintro ⟨haBx, haU, b, hba⟩
        rw [hUmem] at haU
        obtain ⟨ha0, haA, haK, haP⟩ := haU
        have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast (show (0:ℕ) < k by omega)
        refine ⟨b, ⟨?_, ?_⟩, hba⟩
        · apply mem_box_of_eNorm_le
          have he : eNorm b ≤ eNorm a := by
            have hthis : eNorm a = (k:ℝ) * eNorm b := by rw [← hba, hN1]
            have hbn : 0 ≤ eNorm b := Real.sqrt_nonneg _
            have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
            calc eNorm b = 1 * eNorm b := by ring
              _ ≤ (k:ℝ) * eNorm b := mul_le_mul_of_nonneg_right hk1 hbn
              _ = eNorm a := hthis.symm
          exact he.trans haA
        · rw [hSmem k b]
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro h0; exact ha0 (hba.symm.trans ((hN4 k b hk).mpr h0))
          · rw [le_div_iff₀ hk0]
            have hthis : (k:ℝ) * eNorm b = eNorm a := by rw [← hba, hN1]
            nlinarith [hthis, haA]
          · have hta : toR a = (k:ℝ) • toR b := by rw [← hba, hN2]
            exact (hK (k:ℝ) (toR b) hk0).mpr (hta ▸ haK)
          · rw [hba]; exact haP
    have hstep1 : (∑ k ∈ G, (ArithmeticFunction.moebius k : ℤ) * ((S k).ncard : ℤ))
        = ∑ k ∈ G, (ArithmeticFunction.moebius k : ℤ)
            * ((Bx.filter (fun a => a ∈ U ∧ ∃ b, (k:ℤ)•b = a)).card : ℤ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hcard k ((hGmem k).mp hk).1]
    have hstepA : (∑ k ∈ G, (ArithmeticFunction.moebius k : ℤ)
            * ((Bx.filter (fun a => a ∈ U ∧ ∃ b, (k:ℤ)•b = a)).card : ℤ))
        = ∑ k ∈ G, ∑ a ∈ Bx, (ArithmeticFunction.moebius k : ℤ)
            * (if a ∈ U ∧ ∃ b, (k:ℤ)•b = a then (1:ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hb : ((Bx.filter (fun a => a ∈ U ∧ ∃ b, (k:ℤ)•b = a)).card : ℤ)
          = ∑ a ∈ Bx, (if a ∈ U ∧ ∃ b, (k:ℤ)•b = a then (1:ℤ) else 0) := by
        rw [← Finset.sum_boole (fun a => a ∈ U ∧ ∃ b, (k:ℤ)•b = a) Bx]
      rw [hb, Finset.mul_sum]
    have hstepB : (∑ k ∈ G, ∑ a ∈ Bx, (ArithmeticFunction.moebius k : ℤ)
            * (if a ∈ U ∧ ∃ b, (k:ℤ)•b = a then (1:ℤ) else 0))
        = ∑ a ∈ Bx, ∑ k ∈ G, (ArithmeticFunction.moebius k : ℤ)
            * (if a ∈ U ∧ ∃ b, (k:ℤ)•b = a then (1:ℤ) else 0) := by
      rw [Finset.sum_comm]
    have hstepC : (∑ a ∈ Bx, ∑ k ∈ G, (ArithmeticFunction.moebius k : ℤ)
            * (if a ∈ U ∧ ∃ b, (k:ℤ)•b = a then (1:ℤ) else 0))
        = ∑ a ∈ Bx, (if a ∈ T then (1:ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases haU : a ∈ U
      · have haUm : a ∈ U := haU
        rw [hUmem] at haU
        obtain ⟨ha0, haA, haK, haP⟩ := haU
        have hinner : (∑ k ∈ G, (ArithmeticFunction.moebius k : ℤ)
              * (if a ∈ U ∧ ∃ b, (k:ℤ)•b = a then (1:ℤ) else 0))
            = (if Finset.univ.gcd a = 1 then (1:ℤ) else 0) := by
          have hcongr : ∀ k, (ArithmeticFunction.moebius k : ℤ)
              * (if a ∈ U ∧ ∃ b, (k:ℤ)•b = a then (1:ℤ) else 0)
              = (if ∃ b, (k:ℤ)•b = a then (ArithmeticFunction.moebius k : ℤ) else 0) := by
            intro k
            by_cases hQ : ∃ b, (k:ℤ)•b = a
            · rw [if_pos (⟨haUm, hQ⟩ : a ∈ U ∧ ∃ b, (k:ℤ)•b = a), if_pos hQ, mul_one]
            · rw [if_neg (fun h => hQ h.2), mul_zero, if_neg hQ]
          rw [Finset.sum_congr rfl (fun k _ => hcongr k)]
          rw [← Finset.sum_filter]
          have hfilt : (G.filter (fun k : ℕ => ∃ b, (k:ℤ)•b = a))
              = (G.filter (fun k : ℕ => ∀ i, (k:ℤ) ∣ a i)) := by
            apply Finset.filter_congr
            intro k _
            exact exists_smul_iff_dvd k a
          rw [hfilt, Finset.sum_filter, hG]
          exact moebius_dvdVec_sum a ha0 ⌊A⌋₊ (gcd_natAbs_le_floor a ha0 A hA haA)
        have hTiff : a ∈ T ↔ Finset.univ.gcd a = 1 := by
          rw [hTmem]
          exact ⟨fun h => h.1, fun h => ⟨h, haA, haK, haP⟩⟩
        rw [hinner]
        simp only [hTiff]
      · have h0 : (∑ k ∈ G, (ArithmeticFunction.moebius k : ℤ)
              * (if a ∈ U ∧ ∃ b, (k:ℤ)•b = a then (1:ℤ) else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro k _
          rw [if_neg (fun h => haU h.1), mul_zero]
        have hnotT : ¬ (a ∈ T) := fun h => haU (hTU h)
        rw [h0, if_neg hnotT]
    rw [hstep1, hstepA, hstepB, hstepC, Finset.sum_boole, ← ncard_eq_filter_card hTsub]
  exact_mod_cast hmain

end Work.HP.DNC
