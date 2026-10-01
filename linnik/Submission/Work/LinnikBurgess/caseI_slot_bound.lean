import Mathlib
import Submission.Work.LinnikBurgess.frameMod_bridge
import Submission.Work.LinnikBurgess.frame_count_prov_defs
import Submission.Work.LinnikBurgess.DLd_perm

/-!
# The per-slot bound of Case I

`sumI` is a sum over slots `(a, b) ∈ box3 H × box3 H` with the condition `condAB ∧ CaseI` and the
weight `wtAB m a b`.  This file bounds the *mass of the two non-pivot coordinates* of one slot: for
a fixed pivot `a 0` and a fixed second triple `b`, the total over `(a 1, a 2) ∈ [1,H]²` of the
Case-I-restricted weight is at most the `b`-weight times a uniform constant.

The two coordinates are handled by the two halves of the frame step:

* the admissible `a 2` lie in the frame set `frameStepSetD d H (a 0) (a 1) b` (because `condAB`
  carries `DLd`), whence `a1_half_caseI'`;
* the same bound with the roles of `a 1` and `a 2` exchanged covers the other half — the exchange is
  licensed by `DLd_perm`, since `critN`/`UnitAt` only see the multisets of the triples.
-/

open scoped BigOperators

namespace Work.LinnikBurgess

open Classical

/-- Membership in the frame set, from `DLd` and the box constraint: the predicate of
`frameStepSetD` is literally the `DLd`-condition for the triple `![a0, a1, a2]`. -/
theorem mem_frameStepSetD_of_DLd {d H a0 a1 : ℕ} {a2 : ℕ} (b : Fin 3 → ℕ)
    (ha2 : a2 ∈ Finset.Icc 1 H) (hDL : DLd d ![a0, a1, a2] b) :
    a2 ∈ frameStepSetD d H a0 a1 b := by
  classical
  unfold frameStepSetD DLd at *
  simp only [Finset.mem_filter, ha2, true_and] at hDL ⊢
  exact hDL

/-- The same membership with the last two entries of the triple exchanged (via `DLd_perm`), which is
what the `a 2`-coordinate form of the frame step needs. -/
theorem mem_frameStepSetD_of_DLd_swap {d H a0 a1 : ℕ} {a2 : ℕ} (b : Fin 3 → ℕ)
    (ha1 : a1 ∈ Finset.Icc 1 H) (hDL : DLd d ![a0, a1, a2] b) :
    a1 ∈ frameStepSetD d H a0 a2 b := by
  classical
  have hperm : DLd d ![a0, a2, a1] b := by
    have h := (DLd_perm ![a0, a1, a2] b (Equiv.swap 1 2)).mpr hDL
    have hfun : (fun l : Fin 3 => ![a0, a1, a2] ((Equiv.swap 1 2) l)) = ![a0, a2, a1] := by
      funext l
      fin_cases l <;> rfl
    rwa [hfun] at h
  exact mem_frameStepSetD_of_DLd b ha1 hperm

/-- Indicator-to-filtered-sum: if `F ⊆ G` then `∑ b ∈ G, (if b ∈ F then W b else 0) = ∑ b ∈ F, W b`. -/
private lemma sum_ite_mem_eq {G F : Finset ℕ} (W : ℕ → ℝ) (h : F ⊆ G) :
    (∑ b ∈ G, (if b ∈ F then W b else 0)) = ∑ b ∈ F, W b := by
  rw [← Finset.sum_filter]
  congr 1
  exact Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr h)

/-- Factor an indicator of a conjunction of a constant condition and a membership:
`∑_{a1, a2} [(a1 ≠ a0 ∧ a2 ∈ F a1)]·W = ∑_{a1 ≠ a0} ∑_{a2 ∈ F a1} W`. -/
private lemma sum_indicator_factor {H a0 : ℕ} {F : ℕ → Finset ℕ} {W : ℕ → ℕ → ℝ}
    (hF : ∀ a1, F a1 ⊆ Finset.Icc 1 H) :
    (∑ a1 ∈ Finset.Icc 1 H, ∑ a2 ∈ Finset.Icc 1 H,
        (if a1 ≠ a0 ∧ a2 ∈ F a1 then W a1 a2 else 0))
      = ∑ a1 ∈ (Finset.Icc 1 H).filter (fun a1 => a1 ≠ a0), ∑ a2 ∈ F a1, W a1 a2 := by
  have houter : ∀ a1 ∈ Finset.Icc 1 H,
      (∑ a2 ∈ Finset.Icc 1 H, (if a1 ≠ a0 ∧ a2 ∈ F a1 then W a1 a2 else 0))
        = (if a1 ≠ a0 then ∑ a2 ∈ F a1, W a1 a2 else 0) := by
    intro a1 _
    by_cases ha1 : a1 ≠ a0
    · rw [if_pos ha1]
      refine (Finset.sum_congr rfl (fun a2 _ => ?_)).trans (sum_ite_mem_eq (W a1) (hF a1))
      by_cases h2 : a2 ∈ F a1
      · rw [if_pos ⟨ha1, h2⟩, if_pos h2]
      · rw [if_neg (fun h => h2 h.2), if_neg h2]
    · rw [if_neg ha1]
      exact Finset.sum_eq_zero (fun a2 _ => if_neg (fun h => ha1 h.1))
  calc (∑ a1 ∈ Finset.Icc 1 H, ∑ a2 ∈ Finset.Icc 1 H,
          (if a1 ≠ a0 ∧ a2 ∈ F a1 then W a1 a2 else 0))
      = ∑ a1 ∈ Finset.Icc 1 H, (if a1 ≠ a0 then ∑ a2 ∈ F a1, W a1 a2 else 0) :=
        Finset.sum_congr rfl houter
    _ = ∑ a1 ∈ (Finset.Icc 1 H).filter (fun a1 => a1 ≠ a0), ∑ a2 ∈ F a1, W a1 a2 := by
        rw [Finset.sum_filter]

/-- **The per-slot bound of Case I.**  For a pivot slot `a ∈ box3 H` and an arbitrary second triple
`b`, the mass of the two non-pivot coordinates of the slot,

`∑_{a1, a2 ∈ [1,H]} [condAB ∧ CaseI] · wtAB m ![a 0, a1, a2] b`,

is at most the `b`-weight `wg m (a 0) (b 0)·wg m (a 0) (b 1)·wg m (a 0) (b 2)` times the uniform
constant `2·√H·6^ω(d)·4·(H²·τ(d)/d + H)·τ(m)`. -/
theorem caseI_pair_le {H m d g : ℕ} (hm : 0 < m) (hd : 0 < d) (hmd : Nat.Coprime m d)
    {a : Fin 3 → ℕ} (ha : a ∈ box3 H) (b : Fin 3 → ℕ) :
    (∑ a1 ∈ Finset.Icc 1 H, ∑ a2 ∈ Finset.Icc 1 H,
        (if condAB d g ![a 0, a1, a2] b ∧ CaseI ![a 0, a1, a2] b
          then wtAB m ![a 0, a1, a2] b else 0))
      ≤ (wg m (a 0) (b 0) * wg m (a 0) (b 1) * wg m (a 0) (b 2))
          * (2 * (Real.sqrt (H : ℝ) * ((6 : ℝ) ^ (d.primeFactors.card)
              * (4 * (((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) + (H : ℝ))
                  * ((m.divisors.card : ℝ)))))) := by
  classical
  obtain ⟨ha01, ha0H⟩ := box3_anchor ha
  set Bw : ℝ := wg m (a 0) (b 0) * wg m (a 0) (b 1) * wg m (a 0) (b 2) with hBw
  set C : ℝ := Real.sqrt (H : ℝ) * ((6 : ℝ) ^ (d.primeFactors.card)
      * (4 * (((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) + (H : ℝ))
          * ((m.divisors.card : ℝ)))) with hC
  let Ff : ℕ → Finset ℕ := fun a1 => (frameStepSetD d H (a 0) a1 b).filter (fun a2 => a2 ≠ a 0)
  let Fg : ℕ → Finset ℕ := fun a2 => (frameStepSetD d H (a 0) a2 b).filter (fun a1 => a1 ≠ a 0)
  let S : Finset ℕ := (Finset.Icc 1 H).filter (fun a1 => a1 ≠ a 0)
  have hwt : ∀ a1 a2 : ℕ, wtAB m ![a 0, a1, a2] b
      = (wg m (a 0) a1 * wg m (a 0) a2) * Bw := by
    intro a1 a2
    have h1 : (![a 0, a1, a2] : Fin 3 → ℕ) 0 = a 0 := by simp
    have h2 : (![a 0, a1, a2] : Fin 3 → ℕ) 1 = a1 := by simp
    have h3 : (![a 0, a1, a2] : Fin 3 → ℕ) 2 = a2 := by simp
    simp only [hBw, wtAB, h1, h2, h3]
  have hWnn : ∀ a1 a2 : ℕ, 0 ≤ (wg m (a 0) a1 * wg m (a 0) a2) * Bw := by
    intro a1 a2
    have h1 := wg_nonneg m (a 0) a1
    have h2 := wg_nonneg m (a 0) a2
    have h3 := wg_nonneg m (a 0) (b 0)
    have h4 := wg_nonneg m (a 0) (b 1)
    have h5 := wg_nonneg m (a 0) (b 2)
    rw [hBw]
    positivity
  -- pointwise domination by the two frame-step indicators
  have hpt : ∀ a1 ∈ Finset.Icc 1 H, ∀ a2 ∈ Finset.Icc 1 H,
      (if condAB d g ![a 0, a1, a2] b ∧ CaseI ![a 0, a1, a2] b
        then (wg m (a 0) a1 * wg m (a 0) a2) * Bw else 0)
        ≤ (if a1 ≠ a 0 ∧ a2 ∈ Ff a1 then (wg m (a 0) a1 * wg m (a 0) a2) * Bw else 0)
          + (if a2 ≠ a 0 ∧ a1 ∈ Fg a2 then (wg m (a 0) a1 * wg m (a 0) a2) * Bw else 0) := by
    intro a1 ha1 a2 ha2
    by_cases hcond : condAB d g ![a 0, a1, a2] b ∧ CaseI ![a 0, a1, a2] b
    · have hc := hcond.1
      have hne01 : a1 ≠ a 0 := by
        have h := hc.2.1
        simpa using h.symm
      have hne02 : a2 ≠ a 0 := by
        have h := hc.2.2.1
        simpa using h.symm
      have hDL : DLd d ![a 0, a1, a2] b := hc.2.2.2.1
      have hmem1 : a2 ∈ Ff a1 :=
        Finset.mem_filter.mpr ⟨mem_frameStepSetD_of_DLd b ha2 hDL, hne02⟩
      have hmem2 : a1 ∈ Fg a2 :=
        Finset.mem_filter.mpr ⟨mem_frameStepSetD_of_DLd_swap b (a2 := a2) ha1 hDL, hne01⟩
      rw [if_pos hcond, if_pos ⟨hne01, hmem1⟩, if_pos ⟨hne02, hmem2⟩]
      linarith [hWnn a1 a2]
    · rw [if_neg hcond]
      split_ifs <;> linarith [hWnn a1 a2]
  have hgoal : (∑ a1 ∈ Finset.Icc 1 H, ∑ a2 ∈ Finset.Icc 1 H,
        (if condAB d g ![a 0, a1, a2] b ∧ CaseI ![a 0, a1, a2] b
          then wtAB m ![a 0, a1, a2] b else 0))
      = ∑ a1 ∈ Finset.Icc 1 H, ∑ a2 ∈ Finset.Icc 1 H,
          (if condAB d g ![a 0, a1, a2] b ∧ CaseI ![a 0, a1, a2] b
            then (wg m (a 0) a1 * wg m (a 0) a2) * Bw else 0) := by
    refine Finset.sum_congr rfl (fun a1 _ => Finset.sum_congr rfl (fun a2 _ => ?_))
    by_cases h : condAB d g ![a 0, a1, a2] b ∧ CaseI ![a 0, a1, a2] b
    · rw [if_pos h, if_pos h, hwt a1 a2]
    · rw [if_neg h, if_neg h]
  have hFsub : ∀ a1 : ℕ, Ff a1 ⊆ Finset.Icc 1 H := by
    intro a1
    refine (Finset.filter_subset _ _).trans ?_
    intro x hx
    unfold frameStepSetD at hx
    exact (Finset.mem_filter.mp hx).1
  have hFsub' : ∀ a2 : ℕ, Fg a2 ⊆ Finset.Icc 1 H := hFsub
  have hA1 : (∑ a1 ∈ Finset.Icc 1 H, ∑ a2 ∈ Finset.Icc 1 H,
        (if a1 ≠ a 0 ∧ a2 ∈ Ff a1 then (wg m (a 0) a1 * wg m (a 0) a2) * Bw else 0))
      = Bw * (∑ a1 ∈ S, ∑ a2 ∈ Ff a1, wg m (a 0) a1 * wg m (a 0) a2) := by
    rw [sum_indicator_factor (H := H) (a0 := a 0) (F := Ff)
      (W := fun a1 a2 => (wg m (a 0) a1 * wg m (a 0) a2) * Bw) hFsub]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a1 _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a2 _ => by ring)
  have hA2 : (∑ a1 ∈ Finset.Icc 1 H, ∑ a2 ∈ Finset.Icc 1 H,
        (if a2 ≠ a 0 ∧ a1 ∈ Fg a2 then (wg m (a 0) a1 * wg m (a 0) a2) * Bw else 0))
      = Bw * (∑ a2 ∈ S, ∑ a1 ∈ Fg a2, wg m (a 0) a2 * wg m (a 0) a1) := by
    rw [Finset.sum_comm]
    rw [sum_indicator_factor (H := H) (a0 := a 0) (F := Fg)
      (W := fun a2 a1 => (wg m (a 0) a1 * wg m (a 0) a2) * Bw) hFsub']
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a2 _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a1 _ => by ring)
  have hsum : (∑ a1 ∈ Finset.Icc 1 H, ∑ a2 ∈ Finset.Icc 1 H,
        (if condAB d g ![a 0, a1, a2] b ∧ CaseI ![a 0, a1, a2] b
          then (wg m (a 0) a1 * wg m (a 0) a2) * Bw else 0))
      ≤ (∑ a1 ∈ Finset.Icc 1 H, ∑ a2 ∈ Finset.Icc 1 H,
          (if a1 ≠ a 0 ∧ a2 ∈ Ff a1 then (wg m (a 0) a1 * wg m (a 0) a2) * Bw else 0))
        + (∑ a1 ∈ Finset.Icc 1 H, ∑ a2 ∈ Finset.Icc 1 H,
          (if a2 ≠ a 0 ∧ a1 ∈ Fg a2 then (wg m (a 0) a1 * wg m (a 0) a2) * Bw else 0)) := by
    refine le_trans (Finset.sum_le_sum (fun a1 ha1 => Finset.sum_le_sum
      (fun a2 ha2 => hpt a1 ha1 a2 ha2))) ?_
    simp only [Finset.sum_add_distrib]
    exact le_rfl
  have hB1 : (∑ a1 ∈ S, ∑ a2 ∈ Ff a1, wg m (a 0) a1 * wg m (a 0) a2) ≤ C := by
    rw [hC]
    exact a1_half_caseI' hm hd hmd (a := a) ha b
  have hB2 : (∑ a2 ∈ S, ∑ a1 ∈ Fg a2, wg m (a 0) a2 * wg m (a 0) a1) ≤ C := by
    rw [hC]
    simpa only [mul_comm] using a1_half_caseI' hm hd hmd (a := a) ha b
  have hBw0 : 0 ≤ Bw := by
    have h3 := wg_nonneg m (a 0) (b 0)
    have h4 := wg_nonneg m (a 0) (b 1)
    have h5 := wg_nonneg m (a 0) (b 2)
    rw [hBw]
    positivity
  calc (∑ a1 ∈ Finset.Icc 1 H, ∑ a2 ∈ Finset.Icc 1 H,
          (if condAB d g ![a 0, a1, a2] b ∧ CaseI ![a 0, a1, a2] b
            then wtAB m ![a 0, a1, a2] b else 0))
      = (∑ a1 ∈ Finset.Icc 1 H, ∑ a2 ∈ Finset.Icc 1 H,
          (if condAB d g ![a 0, a1, a2] b ∧ CaseI ![a 0, a1, a2] b
            then (wg m (a 0) a1 * wg m (a 0) a2) * Bw else 0)) := hgoal
    _ ≤ (∑ a1 ∈ Finset.Icc 1 H, ∑ a2 ∈ Finset.Icc 1 H,
          (if a1 ≠ a 0 ∧ a2 ∈ Ff a1 then (wg m (a 0) a1 * wg m (a 0) a2) * Bw else 0))
        + (∑ a1 ∈ Finset.Icc 1 H, ∑ a2 ∈ Finset.Icc 1 H,
          (if a2 ≠ a 0 ∧ a1 ∈ Fg a2 then (wg m (a 0) a1 * wg m (a 0) a2) * Bw else 0)) := hsum
    _ = Bw * (∑ a1 ∈ S, ∑ a2 ∈ Ff a1, wg m (a 0) a1 * wg m (a 0) a2)
        + Bw * (∑ a2 ∈ S, ∑ a1 ∈ Fg a2, wg m (a 0) a2 * wg m (a 0) a1) := by rw [hA1, hA2]
    _ ≤ Bw * C + Bw * C :=
        add_le_add (mul_le_mul_of_nonneg_left hB1 hBw0) (mul_le_mul_of_nonneg_left hB2 hBw0)
    _ = Bw * (2 * C) := by ring
    _ = Bw * (2 * (Real.sqrt (H : ℝ) * ((6 : ℝ) ^ (d.primeFactors.card)
          * (4 * (((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) + (H : ℝ))
              * ((m.divisors.card : ℝ)))))) := by rw [hC]

end Work.LinnikBurgess
