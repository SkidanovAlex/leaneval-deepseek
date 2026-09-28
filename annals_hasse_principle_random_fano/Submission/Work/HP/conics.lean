import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.ConicsDefs
import Submission.Work.HP.conics_sharp
import Submission.Work.HP.conics_lift
import Submission.Work.HP.conics_fail
import Submission.Work.HP.conics_prod
import Submission.Work.HP.conics_denom

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset Filter

namespace Work.HP

namespace Conics

/-- The number of integers `s` with `|s| ≤ C` is at most `2C + 3`. -/
theorem ncard_abs_int_le (C : ℝ) (hC : 0 ≤ C) :
    ({s : ℤ | |(s : ℝ)| ≤ C} : Set ℤ).ncard ≤ 2 * C + 3 := by
  have hn : C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
  have hcu : (⌈C⌉₊ : ℝ) < C + 1 := Nat.ceil_lt_add_one hC
  have hsub : ({s : ℤ | |(s : ℝ)| ≤ C} : Set ℤ) ⊆
      Set.Icc (-(⌈C⌉₊ : ℤ)) (⌈C⌉₊ : ℤ) := by
    intro s hs
    have hs' : |(s : ℝ)| ≤ C := hs
    rw [Set.mem_Icc]
    have h := abs_le.mp hs'
    refine ⟨?_, ?_⟩
    · have h1 : ((-(⌈C⌉₊ : ℤ) : ℤ) : ℝ) ≤ (s : ℝ) := by push_cast; linarith [h.1, hn]
      exact_mod_cast h1
    · have h1 : (s : ℝ) ≤ ((⌈C⌉₊ : ℤ) : ℝ) := by push_cast; linarith [h.2, hn]
      exact_mod_cast h1
  have hcard : (Set.Icc (-(⌈C⌉₊ : ℤ)) (⌈C⌉₊ : ℤ)).ncard = 2 * ⌈C⌉₊ + 1 := by
    rw [Set.ncard_Icc, Int.card_Icc]
    have h2 : ((⌈C⌉₊ : ℤ) + 1 - (-(⌈C⌉₊ : ℤ))) = ((2 * ⌈C⌉₊ + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h2, Int.toNat_natCast]
  have h1 : ({s : ℤ | |(s : ℝ)| ≤ C} : Set ℤ).ncard ≤ 2 * ⌈C⌉₊ + 1 :=
    (Set.ncard_le_ncard hsub (Set.finite_Icc _ _)).trans (le_of_eq hcard)
  have h2 : ((2 * ⌈C⌉₊ + 1 : ℕ) : ℝ) ≤ 2 * C + 3 := by
    push_cast
    linarith
  exact le_trans (by exact_mod_cast h1) h2

/-- Number of integers `t` in `[-A,A]` lying in a single residue class mod `Q`. -/
theorem int_class_bound (Q : ℕ) (hQ : 0 < Q) (r : ℤ) (A : ℝ) (hA : 0 ≤ A) :
    {t : ℤ | |(t : ℝ)| ≤ A ∧ (t : ZMod Q) = (r : ZMod Q)}.ncard ≤ 4 * A / Q + 3 := by
  classical
  by_cases hne : ({t : ℤ | |(t : ℝ)| ≤ A ∧ (t : ZMod Q) = (r : ZMod Q)} : Set ℤ).Nonempty
  · obtain ⟨t₀, ht₀⟩ := hne
    have hQt : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
    have hQz : (Q : ℤ) ≠ 0 := by omega
    have hdiv : ∀ t : ℤ, (t : ZMod Q) = (r : ZMod Q) → (Q : ℤ) ∣ (t - t₀) := by
      intro t htq
      have h1 : (t : ZMod Q) = (t₀ : ZMod Q) := htq.trans ht₀.2.symm
      have h2 : (Q : ℤ) ∣ t₀ - t := (ZMod.intCast_eq_intCast_iff_dvd_sub t t₀ Q).mp h1
      simpa using dvd_neg.mpr h2
    have hmem : ∀ t : ℤ, |(t : ℝ)| ≤ A → (t : ZMod Q) = (r : ZMod Q) →
        |(((t - t₀) / (Q : ℤ) : ℤ) : ℝ)| ≤ 2 * A / Q := by
      intro t htA htq
      have hd : (Q : ℤ) ∣ t - t₀ := hdiv t htq
      have hm : (Q : ℤ) * ((t - t₀) / (Q : ℤ)) = t - t₀ := Int.mul_ediv_cancel' hd
      have h2 : ((((t - t₀) / (Q : ℤ) : ℤ)) : ℝ) * (Q : ℝ) = (t : ℝ) - t₀ := by
        rw [mul_comm]
        have hz := congrArg (fun z : ℤ => (z : ℝ)) hm
        push_cast at hz
        exact hz
      have hmul : |(((t - t₀) / (Q : ℤ) : ℤ) : ℝ)| * (Q : ℝ) = |(t : ℝ) - t₀| := by
        rw [← abs_of_pos hQt, ← abs_mul, h2]
      have habs : |(t : ℝ) - t₀| ≤ 2 * A := by
        have h1 : |(t : ℝ) - (t₀ : ℝ)| ≤ |(t : ℝ)| + |(t₀ : ℝ)| := by
          simpa [sub_eq_add_neg, abs_neg] using abs_add_le (t : ℝ) (-(t₀ : ℝ))
        linarith [htA, ht₀.1]
      rw [le_div_iff₀ hQt, hmul]
      exact habs
    have hinj : Function.Injective (fun s : ℤ => t₀ + (Q : ℤ) * s) := by
      intro a b hab
      have h1 : (Q : ℤ) * a = (Q : ℤ) * b := by linarith [hab]
      exact mul_left_cancel₀ hQz h1
    have hsub : ({t : ℤ | |(t : ℝ)| ≤ A ∧ (t : ZMod Q) = (r : ZMod Q)} : Set ℤ) ⊆
        (fun s : ℤ => t₀ + (Q : ℤ) * s) '' {s : ℤ | |(s : ℝ)| ≤ 2 * A / Q} := by
      rintro t ⟨htA, htq⟩
      refine ⟨(t - t₀) / (Q : ℤ), hmem t htA htq, ?_⟩
      show t₀ + (Q : ℤ) * ((t - t₀) / (Q : ℤ)) = t
      rw [Int.mul_ediv_cancel' (hdiv t htq)]
      ring
    have hfinT : ({s : ℤ | |(s : ℝ)| ≤ 2 * A / Q} : Set ℤ).Finite := by
      have hn : 2 * A / Q ≤ (⌈2 * A / Q⌉₊ : ℝ) := Nat.le_ceil _
      refine Set.Finite.subset (Set.finite_Icc (-(⌈2 * A / Q⌉₊ : ℤ)) (⌈2 * A / Q⌉₊ : ℤ)) ?_
      intro s hs
      have hs' : |(s : ℝ)| ≤ 2 * A / Q := hs
      rw [Set.mem_Icc]
      have h := abs_le.mp hs'
      refine ⟨?_, ?_⟩
      · have h1 : ((-(⌈2 * A / Q⌉₊ : ℤ) : ℤ) : ℝ) ≤ (s : ℝ) := by push_cast; linarith [h.1, hn]
        exact_mod_cast h1
      · have h1 : (s : ℝ) ≤ ((⌈2 * A / Q⌉₊ : ℤ) : ℝ) := by push_cast; linarith [h.2, hn]
        exact_mod_cast h1
    have hfinimg : ((fun s : ℤ => t₀ + (Q : ℤ) * s) '' {s : ℤ | |(s : ℝ)| ≤ 2 * A / Q}).Finite :=
      hfinT.image _
    have h1 : ({t : ℤ | |(t : ℝ)| ≤ A ∧ (t : ZMod Q) = (r : ZMod Q)} : Set ℤ).ncard
        ≤ ((fun s : ℤ => t₀ + (Q : ℤ) * s) '' {s : ℤ | |(s : ℝ)| ≤ 2 * A / Q}).ncard :=
      Set.ncard_le_ncard hsub hfinimg
    have h2 : ((fun s : ℤ => t₀ + (Q : ℤ) * s) '' {s : ℤ | |(s : ℝ)| ≤ 2 * A / Q}).ncard
        = ({s : ℤ | |(s : ℝ)| ≤ 2 * A / Q} : Set ℤ).ncard :=
      Set.ncard_image_of_injective _ hinj
    have h3 : ({t : ℤ | |(t : ℝ)| ≤ A ∧ (t : ZMod Q) = (r : ZMod Q)} : Set ℤ).ncard
        ≤ ({s : ℤ | |(s : ℝ)| ≤ 2 * A / Q} : Set ℤ).ncard := by rw [← h2]; exact h1
    have h4 : (({s : ℤ | |(s : ℝ)| ≤ 2 * A / Q} : Set ℤ).ncard : ℝ) ≤ 2 * (2 * A / Q) + 3 :=
      ncard_abs_int_le _ (by positivity)
    have h5 : (({t : ℤ | |(t : ℝ)| ≤ A ∧ (t : ZMod Q) = (r : ZMod Q)} : Set ℤ).ncard : ℝ)
        ≤ 2 * (2 * A / Q) + 3 := le_trans (by exact_mod_cast h3) h4
    have h6 : 2 * (2 * A / Q) + 3 = 4 * A / Q + 3 := by ring
    rw [h6] at h5
    exact h5
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp only [Set.ncard_empty]
    have : (0 : ℝ) ≤ 4 * A / Q + 3 := by positivity
    simpa using this


/-- Number of integers `t` in `[-A,A]` subject to simultaneous congruences modulo pairwise
coprime moduli `m i`: at most `4A/(∏ m i) + 3`. -/
theorem int_simult_bound (k : ℕ) (m : Fin k → ℕ) (hm : ∀ i, 0 < m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j)) (c : Fin k → ℕ) (A : ℝ) (hA : 0 ≤ A) :
    {t : ℤ | |(t : ℝ)| ≤ A ∧ ∀ i, (t : ZMod (m i)) = (c i : ZMod (m i))}.ncard
      ≤ 4 * A / (∏ i, m i) + 3 := by
  classical
  by_cases hne : ({t : ℤ | |(t : ℝ)| ≤ A ∧
      ∀ i, (t : ZMod (m i)) = (c i : ZMod (m i))} : Set ℤ).Nonempty
  · obtain ⟨t₀, ht₀⟩ := hne
    have hQpos : 0 < ∏ i, m i := Finset.prod_pos (fun i _ => hm i)
    have hcong : ∀ t : ℤ, (∀ i, (t : ZMod (m i)) = (c i : ZMod (m i))) →
        (t : ZMod (∏ i, m i)) = (t₀ : ZMod (∏ i, m i)) := by
      intro t ht
      have hdvd : ∀ i, (m i : ℤ) ∣ (t - t₀) := by
        intro i
        have h1 : (t : ZMod (m i)) = (t₀ : ZMod (m i)) := (ht i).trans (ht₀.2 i).symm
        have h2 : (m i : ℤ) ∣ t₀ - t := (ZMod.intCast_eq_intCast_iff_dvd_sub t t₀ (m i)).mp h1
        simpa using dvd_neg.mpr h2
      have hQdvd : ((∏ i, m i : ℕ) : ℤ) ∣ (t - t₀) := by
        have key : ∀ s : Finset (Fin k), (∀ i ∈ s, (m i : ℤ) ∣ (t - t₀)) →
            ((∏ i ∈ s, m i : ℕ) : ℤ) ∣ (t - t₀) := by
          intro s
          induction s using Finset.induction_on with
          | empty => intro _; simp
          | insert a s ha ih =>
            intro hs
            rw [Finset.prod_insert ha]
            have h1 : (m a : ℤ) ∣ (t - t₀) := hs a (Finset.mem_insert_self a s)
            have h2 : ((∏ i ∈ s, m i : ℕ) : ℤ) ∣ (t - t₀) :=
              ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
            have hci : IsCoprime ((m a : ℕ) : ℤ) (((∏ i ∈ s, m i : ℕ)) : ℤ) := by
              rw [Int.isCoprime_iff_nat_coprime]
              simp only [Int.natAbs_natCast]
              exact Nat.Coprime.prod_right (fun i hi => hcop a i (fun h => ha (h ▸ hi)))
            simpa using hci.mul_dvd h1 h2
        simpa using key Finset.univ (fun i _ => hdvd i)
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      simpa [neg_sub] using dvd_neg.mpr hQdvd
    have hsub : ({t : ℤ | |(t : ℝ)| ≤ A ∧
        ∀ i, (t : ZMod (m i)) = (c i : ZMod (m i))} : Set ℤ) ⊆
        {t : ℤ | |(t : ℝ)| ≤ A ∧ (t : ZMod (∏ i, m i)) = (t₀ : ZMod (∏ i, m i))} := by
      rintro t ⟨htA, ht⟩
      exact ⟨htA, hcong t ht⟩
    have hfin : ({t : ℤ | |(t : ℝ)| ≤ A ∧
        (t : ZMod (∏ i, m i)) = (t₀ : ZMod (∏ i, m i))} : Set ℤ).Finite := by
      have hn : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
      refine Set.Finite.subset (Set.finite_Icc (-(⌈A⌉₊ : ℤ)) (⌈A⌉₊ : ℤ)) ?_
      rintro t ⟨htA, _⟩
      rw [Set.mem_Icc]
      have h := abs_le.mp htA
      refine ⟨?_, ?_⟩
      · have h1 : ((-(⌈A⌉₊ : ℤ) : ℤ) : ℝ) ≤ (t : ℝ) := by push_cast; linarith [h.1, hn]
        exact_mod_cast h1
      · have h1 : (t : ℝ) ≤ ((⌈A⌉₊ : ℤ) : ℝ) := by push_cast; linarith [h.2, hn]
        exact_mod_cast h1
    have h1 : ({t : ℤ | |(t : ℝ)| ≤ A ∧
        ∀ i, (t : ZMod (m i)) = (c i : ZMod (m i))} : Set ℤ).ncard
        ≤ ({t : ℤ | |(t : ℝ)| ≤ A ∧ (t : ZMod (∏ i, m i)) = (t₀ : ZMod (∏ i, m i))} : Set ℤ).ncard :=
      Set.ncard_le_ncard hsub hfin
    have h2 : (({t : ℤ | |(t : ℝ)| ≤ A ∧ (t : ZMod (∏ i, m i)) = (t₀ : ZMod (∏ i, m i))} : Set ℤ).ncard : ℝ)
        ≤ 4 * A / (∏ i, m i) + 3 := int_class_bound (∏ i, m i) hQpos t₀ A hA
    exact le_trans (by exact_mod_cast h1) h2
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp only [Set.ncard_empty]
    have : (0 : ℝ) ≤ 4 * A / (∏ i, m i) + 3 := by positivity
    simpa using this


/-- Residue-class form of `int_simult_bound`, with the residues given as elements of `ZMod`. -/
theorem coord_bound (k : ℕ) (m : Fin k → ℕ) (hm : ∀ i, 0 < m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (r : (i : Fin k) → ZMod (m i)) (A : ℝ) (hA : 0 ≤ A) :
    (({t : ℤ | |(t : ℝ)| ≤ A ∧ ∀ i, (t : ZMod (m i)) = r i} : Set ℤ).ncard : ℝ)
      ≤ 4 * A / (∏ i, m i) + 3 := by
  haveI : ∀ i, NeZero (m i) := fun i => ⟨(hm i).ne'⟩
  have hset : ({t : ℤ | |(t : ℝ)| ≤ A ∧ ∀ i, (t : ZMod (m i)) = r i} : Set ℤ) =
      {t : ℤ | |(t : ℝ)| ≤ A ∧ ∀ i, (t : ZMod (m i)) = ((r i).val : ZMod (m i))} := by
    ext t
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      exact ⟨h.1, fun i => by rw [h.2 i, ZMod.natCast_zmod_val]⟩
    · intro h
      exact ⟨h.1, fun i => by rw [h.2 i, ZMod.natCast_zmod_val]⟩
  rw [hset]
  exact int_simult_bound k m hm hcop (fun i => (r i).val) A hA

/-- Cardinality of a product of finite sets. -/
theorem ncard_pi_eq_prod {ι : Type*} [Fintype ι] {α : Type*} (S : ι → Set α)
    (h : ∀ i, (S i).Finite) :
    ({f : ι → α | ∀ i, f i ∈ S i} : Set (ι → α)).ncard = ∏ i, (S i).ncard := by
  have hset : ({f : ι → α | ∀ i, f i ∈ S i} : Set (ι → α)) = Set.pi Set.univ S := by
    ext f; simp [Set.pi]
  rw [hset, Set.ncard_def, Set.encard_pi_eq_prod_encard]
  have hcast : (∏ i, (S i).encard) = ((∏ i, (S i).ncard : ℕ) : ℕ∞) := by
    rw [Nat.cast_prod]
    exact Finset.prod_congr rfl (fun i _ => (h i).cast_ncard_eq.symm)
  rw [hcast]
  simp

/-- Box count for coefficient vectors satisfying simultaneous residue conditions modulo pairwise
coprime moduli. -/
theorem box_bound (k : ℕ) (m : Fin k → ℕ) (hm : ∀ i, 0 < m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (T : (i : Fin k) → Finset (Mon 2 2 → ZMod (m i))) (A : ℝ) (hA : 0 ≤ A) :
    {a : Mon 2 2 → ℤ | (∀ mm, |(a mm : ℝ)| ≤ A) ∧
        ∀ i, (fun mm => (a mm : ZMod (m i))) ∈ T i}.ncard
      ≤ (∏ i, (T i).card) * (4 * A / (∏ i, m i) + 3) ^ 6 := by
  classical
  set C : ℝ := 4 * A / (∏ i, m i) + 3 with hC
  have hCpos : (0:ℝ) ≤ C := by rw [hC]; positivity
  set K : ℕ := ⌊C⌋₊ with hK
  have hKC : (K : ℝ) ≤ C := Nat.floor_le hCpos
  set pr : Finset ((i : Fin k) → Mon 2 2 → ZMod (m i)) := Fintype.piFinset T with hpr
  have hprcard : pr.card = ∏ i, (T i).card := Fintype.card_piFinset T
  have hfib : ∀ r ∈ pr, ({a : Mon 2 2 → ℤ | (∀ mm, |(a mm : ℝ)| ≤ A) ∧
      ∀ mm i, (a mm : ZMod (m i)) = r i mm} : Set (Mon 2 2 → ℤ)).ncard ≤ K ^ 6 := by
    intro r _
    have hfinD : ∀ mm, ({t : ℤ | |(t : ℝ)| ≤ A ∧ ∀ i, (t : ZMod (m i)) = r i mm} : Set ℤ).Finite := by
      intro mm
      have hn : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
      refine Set.Finite.subset (Set.finite_Icc (-(⌈A⌉₊ : ℤ)) (⌈A⌉₊ : ℤ)) ?_
      rintro t ⟨htA, _⟩
      rw [Set.mem_Icc]
      have h := abs_le.mp htA
      refine ⟨?_, ?_⟩
      · have h1 : ((-(⌈A⌉₊ : ℤ) : ℤ) : ℝ) ≤ (t : ℝ) := by push_cast; linarith [h.1, hn]
        exact_mod_cast h1
      · have h1 : (t : ℝ) ≤ ((⌈A⌉₊ : ℤ) : ℝ) := by push_cast; linarith [h.2, hn]
        exact_mod_cast h1
    have heq : ({a : Mon 2 2 → ℤ | (∀ mm, |(a mm : ℝ)| ≤ A) ∧
        ∀ mm i, (a mm : ZMod (m i)) = r i mm} : Set (Mon 2 2 → ℤ)) =
        {a : Mon 2 2 → ℤ | ∀ mm, a mm ∈
          {t : ℤ | |(t : ℝ)| ≤ A ∧ ∀ i, (t : ZMod (m i)) = r i mm}} := by
      ext a
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h mm; exact ⟨h.1 mm, fun i => h.2 mm i⟩
      · intro h; exact ⟨fun mm => (h mm).1, fun mm i => (h mm).2 i⟩
    rw [heq, ncard_pi_eq_prod _ (fun mm => hfinD mm)]
    have hb : ∀ mm : Mon 2 2,
        ({t : ℤ | |(t : ℝ)| ≤ A ∧ ∀ i, (t : ZMod (m i)) = r i mm} : Set ℤ).ncard ≤ K := by
      intro mm
      have h1 := coord_bound k m hm hcop (fun i => r i mm) A hA
      rw [← hC] at h1
      rw [hK]
      exact Nat.le_floor h1
    calc ∏ mm : Mon 2 2, ({t : ℤ | |(t : ℝ)| ≤ A ∧
            ∀ i, (t : ZMod (m i)) = r i mm} : Set ℤ).ncard
        ≤ ∏ _mm : Mon 2 2, K := Finset.prod_le_prod (fun mm _ => hb mm)
      _ = K ^ 6 := by rw [Finset.prod_const, Finset.card_univ, card_mon]
  have hL : ({a : Mon 2 2 → ℤ | (∀ mm, |(a mm : ℝ)| ≤ A) ∧
      ∀ i, (fun mm => (a mm : ZMod (m i))) ∈ T i} : Set (Mon 2 2 → ℤ)) =
      ⋃ r ∈ pr, ({a : Mon 2 2 → ℤ | (∀ mm, |(a mm : ℝ)| ≤ A) ∧
        ∀ mm i, (a mm : ZMod (m i)) = r i mm} : Set (Mon 2 2 → ℤ)) := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro h
      refine ⟨fun i mm => (a mm : ZMod (m i)), ?_, h.1, fun mm i => rfl⟩
      rw [hpr, Fintype.mem_piFinset]
      exact fun i => h.2 i
    · rintro ⟨r, hr, hbox, hres⟩
      refine ⟨hbox, fun i => ?_⟩
      rw [hpr, Fintype.mem_piFinset] at hr
      have : (fun mm => (a mm : ZMod (m i))) = r i := funext fun mm => hres mm i
      rw [this]
      exact hr i
  have hstep : (⋃ r ∈ pr, ({a : Mon 2 2 → ℤ | (∀ mm, |(a mm : ℝ)| ≤ A) ∧
      ∀ mm i, (a mm : ZMod (m i)) = r i mm} : Set (Mon 2 2 → ℤ))).ncard
      ≤ pr.card * K ^ 6 := by
    calc _ ≤ ∑ r ∈ pr, ({a : Mon 2 2 → ℤ | (∀ mm, |(a mm : ℝ)| ≤ A) ∧
            ∀ mm i, (a mm : ZMod (m i)) = r i mm} : Set (Mon 2 2 → ℤ)).ncard :=
          Finset.set_ncard_biUnion_le pr _
      _ ≤ ∑ _r ∈ pr, K ^ 6 := Finset.sum_le_sum (fun r hr => hfib r hr)
      _ = pr.card * K ^ 6 := by rw [Finset.sum_const, smul_eq_mul]
  rw [hprcard] at hstep
  have hKC6 : ((K ^ 6 : ℕ) : ℝ) ≤ (4 * A / (∏ i, m i) + 3) ^ 6 := by
    have h1 : ((K : ℕ) : ℝ) ^ 6 ≤ (4 * A / (∏ i, m i) + 3) ^ 6 := by
      rw [← hC]; exact pow_le_pow_left₀ (by positivity) hKC 6
    calc ((K ^ 6 : ℕ) : ℝ) = ((K : ℕ) : ℝ) ^ 6 := by push_cast; ring
      _ ≤ (4 * A / (∏ i, m i) + 3) ^ 6 := h1
  have hA1 : ((⋃ r ∈ pr, ({a : Mon 2 2 → ℤ | (∀ mm, |(a mm : ℝ)| ≤ A) ∧
      ∀ mm i, (a mm : ZMod (m i)) = r i mm} : Set (Mon 2 2 → ℤ))).ncard : ℝ)
      ≤ (((∏ i, (T i).card) * K ^ 6 : ℕ) : ℝ) := by exact_mod_cast hstep
  rw [hL]
  refine le_trans hA1 ?_
  rw [Nat.cast_mul]
  exact mul_le_mul_of_nonneg_left hKC6 (Nat.cast_nonneg _)

theorem ncard_iUnion_finset {ι α : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → Set α) (hfin : ∀ i ∈ s, (t i).Finite)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (t i) (t j)) :
    (⋃ i ∈ (s : Set ι), t i).ncard = ∑ i ∈ s, (t i).ncard := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.sum_insert has]
    have h1 : (⋃ i ∈ ((insert a s : Finset ι) : Set ι), t i) =
        t a ∪ (⋃ i ∈ (s : Set ι), t i) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_union, Finset.coe_insert, Finset.mem_insert,
        exists_prop, exists_eq_or_imp, true_and]
      constructor
      · rintro ⟨i, (rfl | hi), hx⟩
        · exact Or.inl hx
        · exact Or.inr ⟨i, hi, hx⟩
      · rintro (h | ⟨i, hi, hx⟩)
        · exact ⟨a, Or.inl rfl, h⟩
        · exact ⟨i, Or.inr hi, hx⟩
    rw [h1]
    have hdisj' : Disjoint (t a) (⋃ i ∈ (s : Set ι), t i) := by
      rw [Set.disjoint_left]
      rintro x hx hxu
      rw [Set.mem_iUnion] at hxu
      obtain ⟨i, hxu⟩ := hxu
      rw [Set.mem_iUnion] at hxu
      obtain ⟨hi, hxi⟩ := hxu
      exact Set.disjoint_left.mp
        (hdisj a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
          (fun h => has (h ▸ hi))) hx hxi
    have hfinU : (⋃ i ∈ (s : Set ι), t i).Finite :=
      s.finite_toSet.biUnion (fun i hi => hfin i (Finset.mem_insert_of_mem hi))
    rw [Set.ncard_union_eq hdisj' (hfin a (Finset.mem_insert_self a s)) hfinU,
      ih (fun i hi => hfin i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj => hdisj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))]

/-- For an odd prime `p`, a form sharp on `⟨v⟩` vanishes at `v`. -/
theorem sharp_qf_eq_zero (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {a : Mon 2 2 → ZMod p}
    {v : Fin 3 → ZMod p} (h : SharpAt a v) : qf a v = 0 := by
  have h1 : pol a v v = 0 := h.2.1 v
  have h3 : v + v = (2 : ZMod p) • v := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply]
    ring
  have h2 : pol a v v = (2 : ZMod p) * qf a v := by
    rw [pol, h3, qf_smul]
    ring
  rw [h2] at h1
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hc
    have hc' : ((2 : ℤ) : ZMod p) = 0 := by simpa using hc
    have hd : (p : ℤ) ∣ (2 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp hc'
    have hle := Int.le_of_dvd (by norm_num) hd
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  exact (mul_eq_zero.mp h1).resolve_left h2ne


/-- The bad set mod `p^2` is a positive proportion `p^{-1}` of all forms. -/
theorem card_badform (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    p ^ 11 ≤ 8 * {A : Mon 2 2 → ZMod (p^2) | BadForm p A}.ncard := by
  classical
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp3 : 3 ≤ p := by omega
  set term : ZMod p × ZMod p → Set (Mon 2 2 → ZMod (p^2)) := fun c =>
    {A : Mon 2 2 → ZMod (p^2) | SharpAt (redC p A) ![1, c.1, c.2] ∧ II p A ![1, c.1, c.2]}
  have hterm : ∀ c, (p * (p - 1) * (p - 1) / 2) * ((p - 1) * p ^ 5) ≤ (term c).ncard := by
    intro c
    have heq : term c = ⋃ ā ∈ (Finset.univ : Finset {ā : Mon 2 2 → ZMod p // SharpAt ā ![1, c.1, c.2]}),
        {A : Mon 2 2 → ZMod (p^2) | redC p A = ā.val ∧ II p A ![1, c.1, c.2]} := by
      ext A
      constructor
      · intro hA
        refine Set.mem_iUnion.mpr ⟨⟨redC p A, hA.1⟩, ?_⟩
        refine Set.mem_iUnion.mpr ⟨Finset.mem_univ _, ?_⟩
        exact ⟨rfl, hA.2⟩
      · intro hA
        rw [Set.mem_iUnion] at hA
        obtain ⟨ā, hA⟩ := hA
        rw [Set.mem_iUnion] at hA
        obtain ⟨_, hA⟩ := hA
        exact ⟨by rw [hA.1]; exact ā.property, hA.2⟩
    rw [heq]
    have hfin : ∀ ā ∈ (Finset.univ : Finset {ā : Mon 2 2 → ZMod p // SharpAt ā ![1, c.1, c.2]}),
        ({A : Mon 2 2 → ZMod (p^2) | redC p A = ā.val ∧ II p A ![1, c.1, c.2]} : Set _).Finite :=
      fun ā _ => Set.Finite.subset Set.finite_univ (Set.subset_univ _)
    have hdisj : ∀ ā ∈ (Finset.univ : Finset {ā : Mon 2 2 → ZMod p // SharpAt ā ![1, c.1, c.2]}),
        ∀ ā' ∈ (Finset.univ : Finset {ā : Mon 2 2 → ZMod p // SharpAt ā ![1, c.1, c.2]}),
        ā ≠ ā' → Disjoint ({A : Mon 2 2 → ZMod (p^2) | redC p A = ā.val ∧ II p A ![1, c.1, c.2]} : Set _)
          ({A : Mon 2 2 → ZMod (p^2) | redC p A = ā'.val ∧ II p A ![1, c.1, c.2]} : Set _) := by
      intro ā _ ā' _ hne
      rw [Set.disjoint_left]
      rintro A ⟨h1, _⟩ ⟨h2, _⟩
      exact hne (Subtype.ext (h1.symm.trans h2))
    have hunion : (⋃ ā ∈ (Finset.univ : Finset {ā : Mon 2 2 → ZMod p // SharpAt ā ![1, c.1, c.2]}),
        ({A : Mon 2 2 → ZMod (p^2) | redC p A = ā.val ∧ II p A ![1, c.1, c.2]} : Set _)).ncard
        = ∑ ā ∈ (Finset.univ : Finset {ā : Mon 2 2 → ZMod p // SharpAt ā ![1, c.1, c.2]}),
          ({A : Mon 2 2 → ZMod (p^2) | redC p A = ā.val ∧ II p A ![1, c.1, c.2]} : Set _).ncard :=
      ncard_iUnion_finset _ _ hfin hdisj
    rw [hunion]
    have hone : ∀ ā : {ā : Mon 2 2 → ZMod p // SharpAt ā ![1, c.1, c.2]},
        ({A : Mon 2 2 → ZMod (p^2) | redC p A = ā.val ∧ II p A ![1, c.1, c.2]} : Set _).ncard
          = (p - 1) * p ^ 5 := fun ā => conics_lift p hp ā.val _ ā.property
    calc ∑ ā ∈ (Finset.univ : Finset {ā : Mon 2 2 → ZMod p // SharpAt ā ![1, c.1, c.2]}),
            ({A : Mon 2 2 → ZMod (p^2) | redC p A = ā.val ∧ II p A ![1, c.1, c.2]} : Set _).ncard
        = ∑ _ā ∈ (Finset.univ : Finset {ā : Mon 2 2 → ZMod p // SharpAt ā ![1, c.1, c.2]}),
            (p - 1) * p ^ 5 := Finset.sum_congr rfl (fun ā _ => hone ā)
      _ = Fintype.card {ā : Mon 2 2 → ZMod p // SharpAt ā ![1, c.1, c.2]} * ((p - 1) * p ^ 5) := by
            rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
      _ ≥ (p * (p - 1) * (p - 1) / 2) * ((p - 1) * p ^ 5) := by
            refine Nat.mul_le_mul_right _ ?_
            have h := conics_sharp p hp c.1 c.2
            have h' : p * (p - 1) * (p - 1) / 2
                ≤ ({ā : Mon 2 2 → ZMod p | SharpAt ā ![1, c.1, c.2]} : Set _).ncard := h
            rw [← Set.fintypeCard_eq_ncard] at h'
            exact h'
  have hsub : ∀ c, term c ⊆ {A : Mon 2 2 → ZMod (p^2) | BadForm p A} :=
    fun c A hA => ⟨![1, c.1, c.2], hA.1, hA.2⟩
  have hdisj : ∀ c c', c ≠ c' → Disjoint (term c) (term c') := by
    intro c c' hne
    rw [Set.disjoint_left]
    rintro A ⟨h1, _⟩ ⟨h2, _⟩
    apply hne
    have hz2 : qf (redC p A) ![1, c'.1, c'.2] = 0 := sharp_qf_eq_zero p hp h2
    obtain ⟨t, ht⟩ := h1.2.2 _ hz2
    have ht1 : t = 1 := by
      have := congrFun ht 0
      simpa [Pi.smul_apply] using this.symm
    have hv : (![1, c'.1, c'.2] : Fin 3 → ZMod p) = ![1, c.1, c.2] := by
      rw [ht, ht1, one_smul]
    have hc1 : c'.1 = c.1 := by
      have := congrFun hv 1; simpa using this
    have hc2 : c'.2 = c.2 := by
      have := congrFun hv 2; simpa using this
    exact Prod.ext hc1.symm hc2.symm
  have hfin : ∀ c ∈ (Finset.univ : Finset (ZMod p × ZMod p)), (term c).Finite :=
    fun c _ => Set.Finite.subset Set.finite_univ (Set.subset_univ _)
  have hdisj' : ∀ c ∈ (Finset.univ : Finset (ZMod p × ZMod p)),
      ∀ c' ∈ (Finset.univ : Finset (ZMod p × ZMod p)), c ≠ c' → Disjoint (term c) (term c') :=
    fun c _ c' _ h => hdisj c c' h
  have hu := ncard_iUnion_finset (Finset.univ : Finset (ZMod p × ZMod p)) term hfin hdisj'
  have hmain : (⋃ c ∈ ((Finset.univ : Finset (ZMod p × ZMod p)) : Set (ZMod p × ZMod p)),
      term c).ncard ≤ {A : Mon 2 2 → ZMod (p^2) | BadForm p A}.ncard :=
    Set.ncard_le_ncard (fun A hA => by
        rw [Set.mem_iUnion] at hA
        obtain ⟨c, hA⟩ := hA
        rw [Set.mem_iUnion] at hA
        obtain ⟨_, hc⟩ := hA
        exact hsub c hc)
      (Set.Finite.subset Set.finite_univ (Set.subset_univ _))
  have hsum : (∑ c ∈ (Finset.univ : Finset (ZMod p × ZMod p)),
        ((p * (p - 1) * (p - 1) / 2) * ((p - 1) * p ^ 5)))
      ≤ ∑ c ∈ (Finset.univ : Finset (ZMod p × ZMod p)), (term c).ncard :=
    Finset.sum_le_sum (fun c _ => hterm c)
  have hconst : (∑ c ∈ (Finset.univ : Finset (ZMod p × ZMod p)),
        ((p * (p - 1) * (p - 1) / 2) * ((p - 1) * p ^ 5)))
      = p ^ 2 * ((p * (p - 1) * (p - 1) / 2) * ((p - 1) * p ^ 5)) := by
    rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_prod, ZMod.card,
      ← pow_two]
  have hS : p ^ 2 * ((p * (p - 1) * (p - 1) / 2) * ((p - 1) * p ^ 5))
      ≤ {A : Mon 2 2 → ZMod (p^2) | BadForm p A}.ncard := by
    calc p ^ 2 * ((p * (p - 1) * (p - 1) / 2) * ((p - 1) * p ^ 5))
        = ∑ c ∈ (Finset.univ : Finset (ZMod p × ZMod p)),
            ((p * (p - 1) * (p - 1) / 2) * ((p - 1) * p ^ 5)) := hconst.symm
      _ ≤ ∑ c ∈ (Finset.univ : Finset (ZMod p × ZMod p)), (term c).ncard := hsum
      _ = (⋃ c ∈ ((Finset.univ : Finset (ZMod p × ZMod p)) : Set (ZMod p × ZMod p)),
            term c).ncard := hu.symm
      _ ≤ {A : Mon 2 2 → ZMod (p^2) | BadForm p A}.ncard := hmain
  have h2m : 2 * (p * (p - 1) * (p - 1) / 2) = p * (p - 1) * (p - 1) := by
    have heven : 2 ∣ p * (p - 1) * (p - 1) := by
      have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
      obtain ⟨k, hk⟩ := hodd
      have hk1 : p - 1 = 2 * k := by omega
      refine ⟨p * 2 * k * k, ?_⟩
      rw [hk1, hk]; ring
    exact Nat.mul_div_cancel' heven
  have harith : p ^ 11 ≤ 8 * (p ^ 2 * ((p * (p - 1) * (p - 1) / 2) * ((p - 1) * p ^ 5))) := by
    have h4 : ((p : ℤ)) ^ 3 ≤ 4 * ((p : ℤ) - 1) ^ 3 := by
      have hp3z : (3 : ℤ) ≤ (p : ℤ) := by omega
      have hfac : 4 * ((p : ℤ) - 1) ^ 3 - (p : ℤ) ^ 3
          = ((p : ℤ) - 3) * (3 * (p : ℤ) ^ 2 - 3 * (p : ℤ) + 3) + 5 := by ring
      have hpos : 0 ≤ 3 * (p : ℤ) ^ 2 - 3 * (p : ℤ) + 3 := by
        nlinarith [sq_nonneg ((p : ℤ) - 1), hp3z]
      nlinarith [hfac, hp3z, hpos]
    have h5 : p ^ 3 ≤ 4 * (p - 1) ^ 3 := by
      have hp1 : 1 ≤ p := by omega
      have hcast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
      have h4' := h4
      rw [← hcast] at h4'
      exact_mod_cast h4'
    have heq : 8 * (p ^ 2 * ((p * (p - 1) * (p - 1) / 2) * ((p - 1) * p ^ 5)))
        = 4 * p ^ 8 * (p - 1) ^ 3 := by
      have hA : 2 * (p ^ 2 * ((p * (p - 1) * (p - 1) / 2) * ((p - 1) * p ^ 5)))
          = p ^ 2 * (p * (p - 1) * (p - 1)) * ((p - 1) * p ^ 5) := by
        calc 2 * (p ^ 2 * ((p * (p - 1) * (p - 1) / 2) * ((p - 1) * p ^ 5)))
            = (2 * (p * (p - 1) * (p - 1) / 2)) * (p ^ 2 * ((p - 1) * p ^ 5)) := by ring
          _ = (p * (p - 1) * (p - 1)) * (p ^ 2 * ((p - 1) * p ^ 5)) := by rw [h2m]
          _ = p ^ 2 * (p * (p - 1) * (p - 1)) * ((p - 1) * p ^ 5) := by ring
      calc 8 * (p ^ 2 * ((p * (p - 1) * (p - 1) / 2) * ((p - 1) * p ^ 5)))
          = 4 * (2 * (p ^ 2 * ((p * (p - 1) * (p - 1) / 2) * ((p - 1) * p ^ 5)))) := by ring
        _ = 4 * (p ^ 2 * (p * (p - 1) * (p - 1)) * ((p - 1) * p ^ 5)) := by rw [hA]
        _ = 4 * p ^ 8 * (p - 1) ^ 3 := by ring
    rw [heq]
    calc p ^ 11 = p ^ 8 * p ^ 3 := by ring
      _ ≤ p ^ 8 * (4 * (p - 1) ^ 3) := Nat.mul_le_mul_left _ h5
      _ = 4 * p ^ 8 * (p - 1) ^ 3 := by ring
  exact le_trans harith (Nat.mul_le_mul_left 8 hS)

/-- The sup-norm box in `Mon 2 2 → ℤ` is finite. -/
theorem boxSet_finite (A : ℝ) :
    ({a : Mon 2 2 → ℤ | ∀ mm, |(a mm : ℝ)| ≤ A} : Set (Mon 2 2 → ℤ)).Finite := by
  refine Set.Finite.subset (Set.finite_range (fun u : ((mm : Mon 2 2) → ↥(Set.Icc (-(⌈A⌉₊ : ℤ)) (⌈A⌉₊ : ℤ))) =>
      fun mm => (u mm : ℤ))) ?_
  intro a ha
  refine ⟨fun mm => ⟨a mm, ?_⟩, rfl⟩
  rw [Set.mem_Icc]
  have h := abs_le.mp (ha mm)
  refine ⟨?_, ?_⟩
  · have h1 : ((-(⌈A⌉₊ : ℤ) : ℤ) : ℝ) ≤ (a mm : ℝ) := by push_cast; linarith [h.1, Nat.le_ceil A]
    exact_mod_cast h1
  · have h1 : (a mm : ℝ) ≤ ((⌈A⌉₊ : ℤ) : ℝ) := by push_cast; linarith [h.2, Nat.le_ceil A]
    exact_mod_cast h1

/-- Product monotonicity for nonnegative real factors. -/
theorem prod_le_prod_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    have h0s : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have h1s : ∀ i ∈ s, f i ≤ g i := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert has, Finset.prod_insert has]
    have ha := h1 a (Finset.mem_insert_self a s)
    have h0a := h0 a (Finset.mem_insert_self a s)
    refine le_trans (mul_le_mul_of_nonneg_right ha (Finset.prod_nonneg h0s)) ?_
    exact mul_le_mul_of_nonneg_left (ih h0s h1s) (le_trans h0a ha)

end Conics

open Filter in
theorem conics :
    Tendsto (fun A => ratio 2 2 A (fun a => ∀ p : ℕ, p.Prime → PrimModZero 2 2 a p 2))
      atTop (nhds 0) := by
  classical
  obtain ⟨c₀, hc₀pos, hc₀⟩ := conics_denom
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε'' : 0 < ε * c₀ / 15625 := by positivity
  have hprod : ∀ᶠ k : ℕ in atTop, (∏ i ∈ Finset.range k,
      (1 - 1 / (8 * ((Nat.nth Nat.Prime (i + 1) : ℕ) : ℝ)))) < ε * c₀ / 15625 :=
    (conics_prod).eventually_lt_const hε''
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hprod
  set pp : Fin k₀ → ℕ := fun i => Nat.nth Nat.Prime (i.val + 1) with hpp
  have hprime : ∀ i, (pp i).Prime := fun i => Nat.prime_nth_prime _
  have hne2 : ∀ i, pp i ≠ 2 := by
    intro i
    have h := Nat.add_two_le_nth_prime (i.val + 1)
    simp only [pp] at h ⊢
    omega
  have hinj : Function.Injective pp := by
    intro i j hij
    have h1 := congrArg Nat.primeCounting' hij
    simp only [pp] at h1
    rw [Nat.primeCounting'_nth_eq, Nat.primeCounting'_nth_eq] at h1
    exact Fin.ext (by omega)
  have hpos : ∀ i, 0 < pp i := fun i => (hprime i).pos
  haveI : ∀ i, NeZero ((pp i) ^ 2) := fun i => ⟨pow_ne_zero 2 (hpos i).ne'⟩
  set Q : ℕ := ∏ i, (pp i) ^ 2 with hQ
  set T : (i : Fin k₀) → Finset (Mon 2 2 → ZMod ((pp i)^2)) :=
    fun i => Finset.univ.filter (fun A => ¬ Conics.BadForm (pp i) A) with hT
  have hcop : ∀ i j, i ≠ j → ((pp i) ^ 2).Coprime ((pp j) ^ 2) := by
    intro i j hij
    have h1 : (pp i).Coprime (pp j) :=
      (Nat.coprime_primes (hprime i) (hprime j)).mpr (fun h => hij (hinj h))
    exact h1.pow 2 2
  have hTcard : ∀ i, ((T i).card : ℝ) ≤ (pp i : ℝ) ^ 12 * (1 - 1 / (8 * (pp i : ℝ))) := by
    intro i
    haveI : Fact (pp i).Prime := ⟨hprime i⟩
    have hbad := Conics.card_badform (pp i) (hne2 i)
    have hbadn : (Finset.univ.filter (fun A : Mon 2 2 → ZMod ((pp i)^2) =>
          Conics.BadForm (pp i) A)).card
        = ({A : Mon 2 2 → ZMod ((pp i)^2) | Conics.BadForm (pp i) A} : Set _).ncard := by
      rw [← Set.fintypeCard_eq_ncard]
      exact (Fintype.card_subtype _).symm
    have htot : (Finset.univ : Finset (Mon 2 2 → ZMod ((pp i)^2))).card = (pp i) ^ 12 := by
      rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Conics.card_mon]; ring
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Mon 2 2 → ZMod ((pp i)^2))))
      (p := fun A => Conics.BadForm (pp i) A)
    rw [htot] at hsplit
    have hT' : (T i).card = (Finset.univ.filter (fun A : Mon 2 2 → ZMod ((pp i)^2) =>
        ¬ Conics.BadForm (pp i) A)).card := by rw [hT]
    have hsum : (T i).card
        + ({A : Mon 2 2 → ZMod ((pp i)^2) | Conics.BadForm (pp i) A} : Set _).ncard
        = (pp i) ^ 12 := by
      rw [hT', ← hbadn, add_comm]; exact hsplit
    have h2n : (pp i) ^ 11 ≤ 8 * ({A : Mon 2 2 → ZMod ((pp i)^2) |
        Conics.BadForm (pp i) A} : Set _).ncard := hbad
    have h2 : ((pp i : ℝ)) ^ 11 ≤ 8 * (({A : Mon 2 2 → ZMod ((pp i)^2) |
        Conics.BadForm (pp i) A} : Set _).ncard : ℝ) := by exact_mod_cast h2n
    have h3 : ((T i).card : ℝ) = ((pp i : ℝ)) ^ 12
        - (({A : Mon 2 2 → ZMod ((pp i)^2) | Conics.BadForm (pp i) A} : Set _).ncard : ℝ) := by
      have hh := congrArg (fun n : ℕ => (n : ℝ)) hsum
      push_cast at hh
      linarith [hh]
    have h4 : ((pp i : ℝ)) ^ 11 / 8
        ≤ (({A : Mon 2 2 → ZMod ((pp i)^2) | Conics.BadForm (pp i) A} : Set _).ncard : ℝ) := by
      linarith [h2]
    have h6 : ((pp i : ℝ)) ^ 12 - ((pp i : ℝ)) ^ 11 / 8
        = (pp i : ℝ) ^ 12 * (1 - 1 / (8 * (pp i : ℝ))) := by
      have hpne : (pp i : ℝ) ≠ 0 := by exact_mod_cast (hpos i).ne'
      field_simp
    rw [h3, ← h6]
    linarith [h4]
  have hnum : ∀ᶠ A : ℝ in atTop, primCount 2 2 A (fun a => ∀ p : ℕ, p.Prime → PrimModZero 2 2 a p 2)
      ≤ (∏ i, (T i).card) * (4 * A / (Q : ℝ) + 3) ^ 6 := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with A hA
    have hsub : primSet 2 2 A (fun a => ∀ p : ℕ, p.Prime → PrimModZero 2 2 a p 2) ⊆
        {a : Mon 2 2 → ℤ | (∀ mm, |(a mm : ℝ)| ≤ A) ∧
          ∀ i, (fun mm => (a mm : ZMod ((pp i)^2))) ∈ T i} := by
      rintro a ⟨hprim, hnorm, hP⟩
      refine ⟨fun mm => ?_, fun i => ?_⟩
      · have h1 : |(a mm : ℝ)| ≤ eNorm a := by
          rw [eNorm]
          have h2 : ((a mm : ℝ)) ^ 2 ≤ ∑ i, ((a i : ℝ)) ^ 2 :=
            Finset.single_le_sum (f := fun i => ((a i : ℝ)) ^ 2)
              (fun i _ => sq_nonneg _) (Finset.mem_univ mm)
          calc |(a mm : ℝ)| = Real.sqrt (((a mm : ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
            _ ≤ Real.sqrt (∑ i, ((a i : ℝ)) ^ 2) := Real.sqrt_le_sqrt h2
        linarith [hnorm]
      · rw [hT, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, fun hbad =>
          @conics_fail (pp i) ⟨hprime i⟩ (hne2 i) a hbad (hP (pp i) (hprime i))⟩
    have hfin : ({a : Mon 2 2 → ℤ | (∀ mm, |(a mm : ℝ)| ≤ A) ∧
        ∀ i, (fun mm => (a mm : ZMod ((pp i)^2))) ∈ T i} : Set _).Finite :=
      Set.Finite.subset (Conics.boxSet_finite A) (fun a ha => ha.1)
    calc primCount 2 2 A (fun a => ∀ p : ℕ, p.Prime → PrimModZero 2 2 a p 2)
        = ((primSet 2 2 A (fun a => ∀ p : ℕ, p.Prime → PrimModZero 2 2 a p 2)).ncard : ℝ) := rfl
      _ ≤ (({a : Mon 2 2 → ℤ | (∀ mm, |(a mm : ℝ)| ≤ A) ∧
            ∀ i, (fun mm => (a mm : ZMod ((pp i)^2))) ∈ T i} : Set _).ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard hsub hfin
      _ ≤ (∏ i, (T i).card) * (4 * A / (Q : ℝ) + 3) ^ 6 := by
          rw [hQ]
          exact Conics.box_bound k₀ (fun i => (pp i)^2) (fun i => pow_pos (hpos i) 2) hcop T A
            (le_of_lt hA)
  have hc15 : (0:ℝ) < 15625 / c₀ := div_pos (by norm_num : (0:ℝ) < 15625) hc₀pos
  have hmain : ∀ᶠ A : ℝ in atTop, ratio 2 2 A (fun a => ∀ p : ℕ, p.Prime → PrimModZero 2 2 a p 2)
      ≤ (15625 / c₀) * (∏ i : Fin k₀, (1 - 1 / (8 * (pp i : ℝ)))) := by
    filter_upwards [hnum, hc₀, eventually_gt_atTop (0:ℝ), eventually_ge_atTop (3 * (Q : ℝ))] with
      A hn hden hApos hAQ
    have hq : (0 : ℝ) < (Q : ℝ) := by
      have hQQ : 0 < Q := Finset.prod_pos (fun i _ => pow_pos (hpos i) 2)
      exact_mod_cast hQQ
    have h5 : 4 * A / (Q : ℝ) + 3 ≤ 5 * A / (Q : ℝ) := by
      have h3 : 3 ≤ A / (Q : ℝ) := by
        rw [le_div_iff₀ hq]
        linarith
      have h4 : 5 * A / (Q : ℝ) = 4 * A / (Q : ℝ) + A / (Q : ℝ) := by ring
      rw [h4]; linarith
    have hD : (0:ℝ) < c₀ * A ^ 6 := mul_pos hc₀pos (pow_pos hApos 6)
    have hP0 : (0:ℝ) ≤ primCount 2 2 A (fun a => ∀ p : ℕ, p.Prime → PrimModZero 2 2 a p 2) :=
      Nat.cast_nonneg _
    have hX0 : (0:ℝ) ≤ (∏ i, (T i).card) * (4 * A / (Q:ℝ) + 3) ^ 6 :=
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by positivity) 6)
    have step1 : primCount 2 2 A (fun a => ∀ p : ℕ, p.Prime → PrimModZero 2 2 a p 2)
          / primCount 2 2 A (fun _ => True)
        ≤ ((∏ i, (T i).card) * (4 * A / (Q:ℝ) + 3) ^ 6) / (c₀ * A ^ 6) := by
      have hb : (0:ℝ) < primCount 2 2 A (fun _ => True) := by
        linarith [hden, hD]
      rw [le_div_iff₀ hD, div_mul_eq_mul_div, div_le_iff₀ hb]
      calc primCount 2 2 A (fun a => ∀ p : ℕ, p.Prime → PrimModZero 2 2 a p 2) * (c₀ * A ^ 6)
          ≤ ((∏ i, (T i).card) * (4 * A / (Q:ℝ) + 3) ^ 6) * (c₀ * A ^ 6) :=
            mul_le_mul_of_nonneg_right hn (le_of_lt hD)
        _ ≤ ((∏ i, (T i).card) * (4 * A / (Q:ℝ) + 3) ^ 6)
            * primCount 2 2 A (fun _ => True) := mul_le_mul_of_nonneg_left hden hX0
    calc ratio 2 2 A (fun a => ∀ p : ℕ, p.Prime → PrimModZero 2 2 a p 2)
        = primCount 2 2 A (fun a => ∀ p : ℕ, p.Prime → PrimModZero 2 2 a p 2)
          / primCount 2 2 A (fun _ => True) := rfl
      _ ≤ ((∏ i, (T i).card) * (4 * A / (Q:ℝ) + 3) ^ 6) / (c₀ * A ^ 6) := step1
      _ ≤ (∏ i, (T i).card) * (5 * A / (Q : ℝ)) ^ 6 / (c₀ * A ^ 6) := by
          rw [le_div_iff₀ hD, div_mul_cancel₀ _ (ne_of_gt hD)]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h5 6) (Nat.cast_nonneg _)
      _ = (15625 / c₀) * ∏ i : Fin k₀, ((T i).card : ℝ) / (pp i : ℝ) ^ 12 := by
          have hQ6 : (Q : ℝ) ^ 6 = ∏ i : Fin k₀, (pp i : ℝ) ^ 12 := by
            rw [hQ]
            push_cast
            rw [← Finset.prod_pow]
            exact Finset.prod_congr rfl (fun i _ => by ring)
          rw [div_pow, mul_pow, hQ6, Finset.prod_div_distrib, Finset.prod_pow]
          field_simp
          push_cast
          ring
      _ ≤ (15625 / c₀) * ∏ i : Fin k₀, (1 - 1 / (8 * (pp i : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hc15)
          refine Conics.prod_le_prod_nonneg _ _ _ (fun i _ => ?_) (fun i _ => ?_)
          · positivity
          · have h1 := hTcard i
            have hppos : (0 : ℝ) < (pp i : ℝ) := by exact_mod_cast hpos i
            have h2 : (0 : ℝ) < (pp i : ℝ) ^ 12 := pow_pos hppos 12
            rw [div_le_iff₀ h2]
            linarith [h1]
  filter_upwards [hmain] with A hb
  rw [Real.dist_eq, sub_zero]
  have hratio : 0 ≤ ratio 2 2 A (fun a => ∀ p : ℕ, p.Prime → PrimModZero 2 2 a p 2) := by
    rw [ratio]; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [abs_of_nonneg hratio]
  refine lt_of_le_of_lt hb ?_
  have hkval := hk₀ k₀ le_rfl
  have hprod' : (∏ i : Fin k₀, (1 - 1 / (8 * (pp i : ℝ)))) =
      ∏ i ∈ Finset.range k₀, (1 - 1 / (8 * ((Nat.nth Nat.Prime (i + 1) : ℕ) : ℝ))) := by
    simp only [pp]
    exact Fin.prod_univ_eq_prod_range
      (fun j : ℕ => 1 - 1 / (8 * ((Nat.nth Nat.Prime (j + 1) : ℕ) : ℝ))) k₀
  rw [hprod']
  calc (15625 / c₀) * (∏ i ∈ Finset.range k₀,
        (1 - 1 / (8 * ((Nat.nth Nat.Prime (i + 1) : ℕ) : ℝ))))
      < (15625 / c₀) * (ε * c₀ / 15625) :=
        mul_lt_mul_of_pos_left hkval hc15
    _ = ε := by field_simp

end Work.HP
