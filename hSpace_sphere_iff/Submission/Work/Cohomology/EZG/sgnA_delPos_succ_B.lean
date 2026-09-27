import Mathlib
import Submission.Work.Cohomology.EZShuffleGen
import Submission.Work.Cohomology.EZG.cnt_succAbove

open Work.Cohomology

namespace Work.Cohomology.EZG

set_option linter.unusedVariables false

variable {n : ℕ}

/-- `Fin.succAbove p` maps `delPosP A p` bijectively onto `A`, when `p ∉ A`. -/
lemma image_succAbove_delPosP (A : Finset (Fin (n + 1))) (p : Fin (n + 1)) (hp : p ∉ A) :
    (delPosP A p).image (Fin.succAbove p) = A := by
  ext a
  rw [Finset.mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact mem_delPosP.mp ht
  · intro ha
    have hne : a ≠ p := fun h => hp (h ▸ ha)
    obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hne
    exact ⟨t, mem_delPosP.mpr (by rw [ht]; exact ha), ht⟩

/-- `cntB A` at `succAbove p t` in terms of `cntB (delPosP A p)` at `t`: exactly one complement
element of `A` (namely `p` itself) lies below `succAbove p t` but is lost after deleting the
position. -/
lemma cntB_succAbove (A : Finset (Fin (n + 1))) (p : Fin (n + 1)) (hp : p ∉ A) (t : Fin n) :
    cntB A (Fin.succAbove p t).val
      = cntB (delPosP A p) t.val + (if p.val ≤ t.val then 1 else 0) := by
  rw [cntB, cntB]
  have hST : ((Finset.univ \ delPosP A p).filter (fun u : Fin n => u.val < t.val)).card
      = (((Finset.univ \ A).filter
            (fun j : Fin (n + 1) => j.val < (Fin.succAbove p t).val)).erase p).card := by
    refine Finset.card_bij (fun u _ => Fin.succAbove p u) ?_ ?_ ?_
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hu
      obtain ⟨huB, hut⟩ := hu
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
        true_and]
      exact ⟨Fin.succAbove_ne p u, fun hA => huB (mem_delPosP.mpr hA),
        Fin.lt_def.mp (Fin.succAbove_lt_succAbove_iff.mpr (Fin.lt_def.mpr hut))⟩
    · intro u1 _ u2 _ h
      exact Fin.succAbove_right_injective h
    · intro j hj
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
        true_and] at hj
      obtain ⟨hjp, hjnA, hjt⟩ := hj
      obtain ⟨u, hu⟩ := Fin.exists_succAbove_eq (x := j) (y := p) hjp
      refine ⟨u, ?_, hu⟩
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
      refine ⟨fun huB => hjnA (by rw [← hu]; exact mem_delPosP.mp huB), ?_⟩
      exact Fin.lt_def.mp (Fin.succAbove_lt_succAbove_iff.mp
        (Fin.lt_def.mpr (by rw [hu]; exact hjt)))
  have hpS : p ∈ (Finset.univ \ A).filter
        (fun j : Fin (n + 1) => j.val < (Fin.succAbove p t).val) ↔ p.val ≤ t.val := by
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩
      exact (lt_val_succAbove_iff p t).mp h
    · intro h
      exact ⟨hp, (lt_val_succAbove_iff p t).mpr h⟩
  rw [hST]
  have hif : (if p ∈ (Finset.univ \ A).filter
        (fun j : Fin (n + 1) => j.val < (Fin.succAbove p t).val) then 1 else 0)
      = (if p.val ≤ t.val then 1 else 0) := by
    by_cases h : p ∈ (Finset.univ \ A).filter
        (fun j : Fin (n + 1) => j.val < (Fin.succAbove p t).val)
    · rw [if_pos h, if_pos (hpS.mp h)]
    · rw [if_neg h, if_neg (fun hh => h (hpS.mpr hh))]
  rw [← hif]
  by_cases h : p ∈ (Finset.univ \ A).filter
      (fun j : Fin (n + 1) => j.val < (Fin.succAbove p t).val)
  · rw [if_pos h, Finset.card_erase_add_one h]
  · rw [if_neg h, add_zero, Finset.erase_eq_self.mpr h]

/-- The number of elements of `delPosP A p` that are `≥ p` equals the number of elements of `A`
that are `> p`. -/
lemma card_filter_le_delPosP (A : Finset (Fin (n + 1))) (p : Fin (n + 1)) :
    ((delPosP A p).filter (fun t => p.val ≤ t.val)).card
      = (A.filter (fun i => p.val < i.val)).card := by
  have hImg : ((delPosP A p).filter (fun t => p.val ≤ t.val)).image (Fin.succAbove p)
      = A.filter (fun i => p.val < i.val) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨t, ⟨htB, htp⟩, rfl⟩
      exact ⟨mem_delPosP.mp htB,
        Fin.lt_def.mp ((Fin.lt_succAbove_iff_le_castSucc p t).mpr
          (Fin.le_def.mpr (by simpa using htp)))⟩
    · rintro ⟨hiA, hip⟩
      have hne : i ≠ p := by rintro rfl; exact (lt_irrefl _) hip
      obtain ⟨u, hu⟩ := Fin.exists_succAbove_eq (x := i) (y := p) hne
      refine ⟨u, ⟨?_, ?_⟩, hu⟩
      · exact mem_delPosP.mpr (by rw [hu]; exact hiA)
      · by_contra hcon
        rw [not_le] at hcon
        have hcomp : Fin.succAbove p u = u.castSucc :=
          Fin.succAbove_of_castSucc_lt p u (Fin.lt_def.mpr (by simpa using hcon))
        have hv : i.val = u.val := by rw [← hu, hcomp]; rfl
        omega
  have hc : (((delPosP A p).filter (fun t => p.val ≤ t.val)).image (Fin.succAbove p)).card
      = ((delPosP A p).filter (fun t => p.val ≤ t.val)).card :=
    Finset.card_image_of_injective _ (Fin.succAbove_right_injective (p := p))
  rw [hImg] at hc
  exact hc.symm

/-- Splitting `A` at the value of `p ∉ A`: the elements below `p` and those above `p` partition
`A`. -/
lemma card_filter_lt_add_cnt (A : Finset (Fin (n + 1))) (p : Fin (n + 1)) (hp : p ∉ A) :
    (A.filter (fun i => p.val < i.val)).card + cnt A p.val = A.card := by
  have h1 : A.filter (fun i => p.val < i.val) = A.filter (fun i => ¬ i.val < p.val) := by
    apply Finset.filter_congr
    intro i hi
    have hne : i.val ≠ p.val := fun h => hp (Fin.ext h ▸ hi)
    constructor <;> intro h <;> omega
  have h2 := Finset.card_filter_add_card_filter_not (s := A)
    (p := fun i : Fin (n + 1) => i.val < p.val)
  simp only [cnt]
  rw [h1]
  omega

/-- The key combinatorial identity: `invA A + p.val` versus `invA` of the deleted shuffle. -/
lemma invA_delPosP_add (A : Finset (Fin (n + 1))) (p : Fin (n + 1)) (hp : p ∉ A) :
    invA A + p.val = invA (delPosP A p) + A.card + cntB A p.val := by
  have hBA := image_succAbove_delPosP A p hp
  have hsum : invA A = (delPosP A p).sum (fun t => cntB A (Fin.succAbove p t).val) := by
    have h1 : ((delPosP A p).image (Fin.succAbove p)).sum (fun i => cntB A i.val)
        = (delPosP A p).sum (fun t => cntB A (Fin.succAbove p t).val) :=
      Finset.sum_image (fun _ _ _ _ h => Fin.succAbove_right_injective h)
    rw [hBA] at h1
    rw [← h1]
    simp only [invA, cntB]
  have hstep : (delPosP A p).sum (fun t => cntB A (Fin.succAbove p t).val)
      = (delPosP A p).sum
          (fun t => cntB (delPosP A p) t.val + (if p.val ≤ t.val then 1 else 0)) :=
    Finset.sum_congr rfl (fun t _ => cntB_succAbove A p hp t)
  have hinvB : (delPosP A p).sum (fun t => cntB (delPosP A p) t.val) = invA (delPosP A p) := by
    simp only [invA, cntB]
  rw [hsum, hstep, Finset.sum_add_distrib, ← Finset.card_filter, hinvB]
  have hD := card_filter_le_delPosP A p
  have hK := card_filter_lt_add_cnt A p hp
  have hcnt := cnt_add_cntB A (le_of_lt p.isLt)
  omega

theorem sgnA_delPos_succ_B {n : ℕ} (A : Finset (Fin (n + 1))) (q : Fin n)
    (hq : q.castSucc ∉ A) (hq' : q.succ ∉ A) :
    sgnA A * (-1 : ℤ) ^ (q.val + 1)
      = sgnA (delPosP A q.succ) * (-1 : ℤ) ^ A.card * (-1 : ℤ) ^ (cntB A (q.val + 1)) := by
  have hmain := invA_delPosP_add A q.succ hq'
  rw [Fin.val_succ] at hmain
  simp only [sgnA]
  simp only [← pow_add]
  exact congrArg ((-1 : ℤ) ^ ·) hmain

end Work.Cohomology.EZG
