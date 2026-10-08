import Mathlib
import Submission.Work.BG.Thm43Defs

namespace Work.BG

private lemma fin2_if_zero {c : Prop} [Decidable c] (h : (if c then (0 : Fin 2) else 1) = 0) : c := by
  by_contra hc
  simp [hc] at h

private lemma fin2_if_one {c : Prop} [Decidable c] (h : (if c then (0 : Fin 2) else 1) = 1) : ¬ c := by
  intro hc
  simp [hc] at h

private def pat4 : Fin 4 → Fin 2 × Fin 2 :=
  ![((0 : Fin 2), (0 : Fin 2)), ((1 : Fin 2), (0 : Fin 2)),
    ((0 : Fin 2), (1 : Fin 2)), ((1 : Fin 2), (1 : Fin 2))]

private lemma pat4_inj : Function.Injective pat4 := by decide

/-- The map encoding the signs of a pair of `±1`-valued functions. -/
def signMap {ι : Type} (T : Finset ι) (p q : ι → ℤ) (i : ↥T) : Fin 2 × Fin 2 :=
  (if p (i : ι) = 1 then (0 : Fin 2) else 1, if q (i : ι) = 1 then (0 : Fin 2) else 1)

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 in
theorem hadamard : Work.GW2.C23.HadamardProp := by
  intro ι T a b c hcard hsign hab hac hbc
  classical
  set p : ι → ℤ := fun i => b i * a i with hp_def
  set q : ι → ℤ := fun i => c i * a i with hq_def
  have hp_sq : ∀ i ∈ T, p i ^ 2 = 1 := by
    intro i hi
    obtain ⟨ha, hb, _⟩ := hsign i hi
    simp only [hp_def]
    rw [mul_pow, hb, ha, one_mul]
  have hq_sq : ∀ i ∈ T, q i ^ 2 = 1 := by
    intro i hi
    obtain ⟨ha, _, hc⟩ := hsign i hi
    simp only [hq_def]
    rw [mul_pow, hc, ha, one_mul]
  have hp_sum : ∑ i ∈ T, p i = 0 := by
    simp only [hp_def]
    rw [Finset.sum_congr rfl (fun i _ => mul_comm (b i) (a i)), hab]
  have hq_sum : ∑ i ∈ T, q i = 0 := by
    simp only [hq_def]
    rw [Finset.sum_congr rfl (fun i _ => mul_comm (c i) (a i)), hac]
  have hpq_sum : ∑ i ∈ T, p i * q i = 0 := by
    have hpt : ∀ i ∈ T, p i * q i = b i * c i := by
      intro i hi
      obtain ⟨ha, _, _⟩ := hsign i hi
      simp only [hp_def, hq_def]
      calc (b i * a i) * (c i * a i) = (b i * c i) * a i ^ 2 := by ring
        _ = b i * c i := by rw [ha, mul_one]
    rw [Finset.sum_congr rfl hpt, hbc]
  have hp' : ∑ i : ↥T, p (i:ι) = 0 := by
    rw [← Finset.sum_subtype T (fun x => Iff.rfl) p, hp_sum]
  have hq' : ∑ i : ↥T, q (i:ι) = 0 := by
    rw [← Finset.sum_subtype T (fun x => Iff.rfl) q, hq_sum]
  have hpq' : ∑ i : ↥T, p (i:ι) * q (i:ι) = 0 := by
    rw [← Finset.sum_subtype T (fun x => Iff.rfl) (fun i => p i * q i), hpq_sum]
  have key : ∀ j : ↥T,
      ∑ i : ↥T, (1 + p (i:ι) * p (j:ι)) * (1 + q (i:ι) * q (j:ι)) = 4 := by
    intro j
    have expand : ∀ i : ↥T, (1 + p (i:ι) * p (j:ι)) * (1 + q (i:ι) * q (j:ι))
        = 1 + p (i:ι) * p (j:ι) + q (i:ι) * q (j:ι)
          + (p (i:ι) * q (i:ι)) * (p (j:ι) * q (j:ι)) := by
      intro i; ring
    rw [Finset.sum_congr rfl (fun i _ => expand i)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    rw [hp', hq', hpq']
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_one, zero_mul,
      add_zero]
    rw [hcard]
    norm_num
  have hterm : ∀ i : ↥T, (1 + p (i:ι) * p (i:ι)) * (1 + q (i:ι) * q (i:ι)) = 4 := by
    intro i
    have h1 : p (i:ι) * p (i:ι) = 1 := by rw [← sq, hp_sq i i.2]
    have h2 : q (i:ι) * q (i:ι) = 1 := by rw [← sq, hq_sq i i.2]
    rw [h1, h2]; norm_num
  have hnonneg : ∀ i j : ↥T,
      0 ≤ (1 + p (i:ι) * p (j:ι)) * (1 + q (i:ι) * q (j:ι)) := by
    intro i j
    have h1 : 0 ≤ 1 + p (i:ι) * p (j:ι) := by
      rcases sq_eq_one_iff.mp (hp_sq i i.2) with h | h <;>
        rcases sq_eq_one_iff.mp (hp_sq j j.2) with h' | h' <;> rw [h, h'] <;> norm_num
    have h2 : 0 ≤ 1 + q (i:ι) * q (j:ι) := by
      rcases sq_eq_one_iff.mp (hq_sq i i.2) with h | h <;>
        rcases sq_eq_one_iff.mp (hq_sq j j.2) with h' | h' <;> rw [h, h'] <;> norm_num
    exact mul_nonneg h1 h2
  have hφ_inj : Function.Injective (signMap T p q) := by
    intro i j hij
    by_contra hne
    have hle : ∑ k ∈ ({i, j} : Finset ↥T),
        (1 + p (k:ι) * p (i:ι)) * (1 + q (k:ι) * q (i:ι))
        ≤ ∑ k ∈ (Finset.univ : Finset ↥T),
        (1 + p (k:ι) * p (i:ι)) * (1 + q (k:ι) * q (i:ι)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => hnonneg k i)
    rw [key i] at hle
    have hpair : ∑ k ∈ ({i, j} : Finset ↥T),
        (1 + p (k:ι) * p (i:ι)) * (1 + q (k:ι) * q (i:ι))
        = 4 + (1 + p (j:ι) * p (i:ι)) * (1 + q (j:ι) * q (i:ι)) := by
      rw [Finset.sum_pair hne, hterm i]
    rw [hpair] at hle
    have hzero : (1 + p (j:ι) * p (i:ι)) * (1 + q (j:ι) * q (i:ι)) = 0 := by
      have h1 := hnonneg j i
      have h2 : (1 + p (j:ι) * p (i:ι)) * (1 + q (j:ι) * q (i:ι)) ≤ 0 := by linarith
      linarith
    rcases mul_eq_zero.mp hzero with hz | hz
    · have hpjpi : p (j:ι) * p (i:ι) = -1 := by linarith
      have hpij : p (i:ι) = p (j:ι) := by
        have h := congrArg Prod.fst hij
        simp only [signMap] at h
        rcases sq_eq_one_iff.mp (hp_sq i i.2) with h1 | h1 <;>
          rcases sq_eq_one_iff.mp (hp_sq j j.2) with h2 | h2 <;>
          rw [h1, h2] at h ⊢ <;> simp_all
      rw [← hpij, ← sq] at hpjpi
      have hsq := hp_sq i i.2
      linarith
    · have hqjqi : q (j:ι) * q (i:ι) = -1 := by linarith
      have hqij : q (i:ι) = q (j:ι) := by
        have h := congrArg Prod.snd hij
        simp only [signMap] at h
        rcases sq_eq_one_iff.mp (hq_sq i i.2) with h1 | h1 <;>
          rcases sq_eq_one_iff.mp (hq_sq j j.2) with h2 | h2 <;>
          rw [h1, h2] at h ⊢ <;> simp_all
      rw [← hqij, ← sq] at hqjqi
      have hsq := hq_sq i i.2
      linarith
  have hcard2 : Fintype.card ↥T = Fintype.card (Fin 2 × Fin 2) := by
    rw [Fintype.card_coe, hcard, Fintype.card_prod, Fintype.card_fin]
  have hφ_bij : Function.Bijective (signMap T p q) :=
    (Fintype.bijective_iff_injective_and_card (signMap T p q)).2 ⟨hφ_inj, hcard2⟩
  have hφ_surj : Function.Surjective (signMap T p q) := hφ_bij.2
  obtain ⟨x0, hx0⟩ := hφ_surj ((0 : Fin 2), (0 : Fin 2))
  obtain ⟨x1, hx1⟩ := hφ_surj ((1 : Fin 2), (0 : Fin 2))
  obtain ⟨x2, hx2⟩ := hφ_surj ((0 : Fin 2), (1 : Fin 2))
  obtain ⟨x3, hx3⟩ := hφ_surj ((1 : Fin 2), (1 : Fin 2))
  let y : Fin 4 → ↥T := ![x0, x1, x2, x3]
  have hy : ∀ k, signMap T p q (y k) = pat4 k := by
    intro k
    fin_cases k <;> simp [y, pat4, hx0, hx1, hx2, hx3]
  have hy_inj : Function.Injective y := by
    intro k l hkl
    exact pat4_inj (by rw [← hy k, ← hy l, hkl])
  refine ⟨fun k => (y k : ι), ?_, ?_, ?_, ?_⟩
  · intro k l hkl
    exact hy_inj (Subtype.ext hkl)
  · intro k
    exact (y k).2
  · intro k
    change b ((y k : ↥T) : ι) * a ((y k : ↥T) : ι) = ![1, -1, 1, -1] k
    have hpv : p ((y k : ↥T) : ι) = ![1, -1, 1, -1] k := by
      have h := congrArg Prod.fst (hy k)
      simp only [signMap] at h
      fin_cases k
      · simpa [pat4] using fin2_if_zero h
      · have hne : ¬ (p ((y 1 : ↥T) : ι) = 1) := fin2_if_one (by simpa [pat4] using h)
        rcases sq_eq_one_iff.mp (hp_sq (y 1) (y 1).2) with h1 | h1
        · exact absurd h1 hne
        · simpa using h1
      · simpa [pat4] using fin2_if_zero h
      · have hne : ¬ (p ((y 3 : ↥T) : ι) = 1) := fin2_if_one (by simpa [pat4] using h)
        rcases sq_eq_one_iff.mp (hp_sq (y 3) (y 3).2) with h1 | h1
        · exact absurd h1 hne
        · simpa using h1
    rw [show b ((y k : ↥T) : ι) * a ((y k : ↥T) : ι) = p ((y k : ↥T) : ι) by simp only [hp_def],
      hpv]
  · intro k
    change c ((y k : ↥T) : ι) * a ((y k : ↥T) : ι) = ![1, 1, -1, -1] k
    have hqv : q ((y k : ↥T) : ι) = ![1, 1, -1, -1] k := by
      have h := congrArg Prod.snd (hy k)
      simp only [signMap] at h
      fin_cases k
      · simpa [pat4] using fin2_if_zero h
      · simpa [pat4] using fin2_if_zero h
      · have hne : ¬ (q ((y 2 : ↥T) : ι) = 1) := fin2_if_one (by simpa [pat4] using h)
        rcases sq_eq_one_iff.mp (hq_sq (y 2) (y 2).2) with h1 | h1
        · exact absurd h1 hne
        · simpa using h1
      · have hne : ¬ (q ((y 3 : ↥T) : ι) = 1) := fin2_if_one (by simpa [pat4] using h)
        rcases sq_eq_one_iff.mp (hq_sq (y 3) (y 3).2) with h1 | h1
        · exact absurd h1 hne
        · simpa using h1
    rw [show c ((y k : ↥T) : ι) * a ((y k : ↥T) : ι) = q ((y k : ↥T) : ι) by simp only [hq_def],
      hqv]

end Work.BG
