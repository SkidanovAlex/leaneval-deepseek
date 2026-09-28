import Mathlib
import Submission.Work.RatHurewicz.Bridge.Defs

/-!
# The collapse `Iⁿ/∂Iⁿ → Sⁿ` factors through the simplex

The cumulative-coordinate map `H n : Iⁿ → Δⁿ`, `t ↦ ((∏_{i<j} t_i)(1-t_j))_j`, is a surjective
closed (hence quotient) map which sends the boundary `∂Iⁿ` of the cube exactly onto the simplicial
boundary `{z | ∃ j, z j = 0}` of `Δⁿ`.  Therefore the collapse `collapseMap n hn : Iⁿ → Sⁿ`
(which is constant on `∂Iⁿ`) descends along `H n` to a continuous map `s : Δⁿ → Sⁿ` with
`s ∘ H n = collapseMap n hn` and with `s` constant on the simplicial boundary of `Δⁿ`.

The descent is produced by `Topology.IsQuotientMap.lift`; the two ingredients are
* `H_surjective` — surjectivity of `H n`, via the explicit right inverse `Hinv n` given by the
  suffix sums `suf` of the coordinates (`H_tinv`), and
* `H_eq_or_boundary` — two points of the cube with the same image under `H n` are either equal or
  both lie on the boundary of the cube (equivalently, `H n` is injective off `∂Iⁿ`), which makes
  `collapseMap n hn` constant on the fibres of `H n`.
-/

open scoped unitInterval Topology Simplicial
open CategoryTheory AlgebraicTopology

namespace Work.RatHurewicz.Bridge

open Work.Stems.Cubical

noncomputable section

/-! ## Suffix sums of the coordinates of a simplex point -/

/-- The suffix sum `∑_{k ≥ j} z k` of the coordinates of a point of the standard simplex. -/
def suf (n : ℕ) (z : stdSimplex ℝ (Fin (n + 1))) (j : ℕ) : ℝ :=
  ∑ k : Fin (n + 1), if j ≤ (k : ℕ) then (z k : ℝ) else 0

@[simp]
theorem suf_zero (n : ℕ) (z : stdSimplex ℝ (Fin (n + 1))) : suf n z 0 = 1 := by
  rw [suf]
  simp only [Nat.zero_le, ↓reduceIte]
  exact z.2.2

theorem suf_nonneg (n : ℕ) (z : stdSimplex ℝ (Fin (n + 1))) (j : ℕ) : 0 ≤ suf n z j := by
  rw [suf]
  exact Finset.sum_nonneg fun k _ => by split_ifs with h; exacts [z.2.1 k, le_refl 0]

theorem suf_anti (n : ℕ) (z : stdSimplex ℝ (Fin (n + 1))) {j j' : ℕ} (h : j ≤ j') :
    suf n z j' ≤ suf n z j := by
  rw [suf, suf]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : j' ≤ (k : ℕ)
  · rw [if_pos hk, if_pos (le_trans h hk)]
  · rw [if_neg hk]
    split_ifs
    exacts [z.2.1 k, le_refl 0]

/-- The suffix sums are determined by the coordinates: `suf n z j = z j + suf n z (j+1)`. -/
theorem suf_succ (n : ℕ) (z : stdSimplex ℝ (Fin (n + 1))) {j : ℕ} (hj : j ≤ n) :
    suf n z j = z ⟨j, Nat.lt_succ_of_le hj⟩ + suf n z (j + 1) := by
  have hsplit : ∀ k : Fin (n + 1),
      (if j ≤ (k : ℕ) then (z k : ℝ) else 0)
        = (if (k : ℕ) = j then (z k : ℝ) else 0)
          + (if j + 1 ≤ (k : ℕ) then (z k : ℝ) else 0) := by
    intro k
    by_cases h : (k : ℕ) = j
    · rw [if_pos (by omega : j ≤ (k : ℕ)), if_pos h,
        if_neg (by omega : ¬ j + 1 ≤ (k : ℕ))]
      ring
    · by_cases hle : j ≤ (k : ℕ)
      · rw [if_pos hle, if_neg h, if_pos (by omega : j + 1 ≤ (k : ℕ)), zero_add]
      · rw [if_neg hle, if_neg h, if_neg (by omega : ¬ j + 1 ≤ (k : ℕ)), zero_add]
  have hfin : (∑ k : Fin (n + 1), if (k : ℕ) = j then (z k : ℝ) else 0)
      = z ⟨j, Nat.lt_succ_of_le hj⟩ := by
    rw [Finset.sum_eq_single ⟨j, Nat.lt_succ_of_le hj⟩]
    · simp
    · intro k _ hk
      rw [if_neg]
      intro h
      exact hk (Fin.ext h)
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [suf, Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib, hfin]
  rfl

/-- The suffix sums vanish past the last coordinate. -/
theorem suf_top (n : ℕ) (z : stdSimplex ℝ (Fin (n + 1))) : suf n z (n + 1) = 0 := by
  rw [suf]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [if_neg]
  omega

theorem suf_mul_div (n : ℕ) (z : stdSimplex ℝ (Fin (n + 1))) (j : ℕ) :
    suf n z j * (suf n z (j + 1) / suf n z j) = suf n z (j + 1) := by
  by_cases h : suf n z j = 0
  · have h' : suf n z (j + 1) = 0 :=
      le_antisymm (h ▸ suf_anti n z (Nat.le_succ j)) (suf_nonneg n z _)
    rw [h, h', zero_div, mul_zero]
  · exact mul_div_cancel₀ _ h

theorem suf_div_mem (n : ℕ) (z : stdSimplex ℝ (Fin (n + 1))) (j : ℕ) :
    suf n z (j + 1) / suf n z j ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨div_nonneg (suf_nonneg n z _) (suf_nonneg n z _), ?_⟩
  rcases eq_or_lt_of_le (suf_nonneg n z j) with h | h
  · have h' : suf n z (j + 1) = 0 :=
      le_antisymm (h ▸ suf_anti n z (Nat.le_succ j)) (suf_nonneg n z _)
    rw [← h, h', zero_div]
    norm_num
  · rw [div_le_one h]
    exact suf_anti n z (Nat.le_succ j)

/-! ## An explicit right inverse of `H n` -/

/-- A right inverse of `H n`, given by the ratios of consecutive suffix sums. -/
def Hinv (n : ℕ) (z : stdSimplex ℝ (Fin (n + 1))) : IC n :=
  fun i => ⟨suf n z (i.1 + 1) / suf n z i.1, suf_div_mem n z i.1⟩

theorem tval_Hinv (n : ℕ) (z : stdSimplex ℝ (Fin (n + 1))) {i : ℕ} (hi : i ≤ n) :
    tval n (Hinv n z) i = suf n z (i + 1) / suf n z i := by
  rcases lt_or_eq_of_le hi with h | h
  · rw [tval_of_lt _ h]
    rfl
  · rw [h, tval_of_le _ (by omega : ¬ n < n), suf_top, zero_div]

theorem Pnat_Hinv (n : ℕ) (z : stdSimplex ℝ (Fin (n + 1))) :
    ∀ k ≤ n, Pnat n (Hinv n z) k = suf n z k := by
  intro k
  induction k with
  | zero => intro _; rw [Pnat_zero, suf_zero]
  | succ k ih =>
    intro hk
    rw [Pnat_succ, ih (by omega), tval_Hinv n z (by omega)]
    exact suf_mul_div n z k

theorem Hfun_Hinv (n : ℕ) (z : stdSimplex ℝ (Fin (n + 1))) (j : Fin (n + 1)) :
    Hfun n (Hinv n z) j = z j := by
  rw [Hfun, Pnat_Hinv n z j.1 (Nat.lt_succ_iff.mp j.2),
    tval_Hinv n z (Nat.lt_succ_iff.mp j.2), mul_sub, mul_one, suf_mul_div]
  rw [suf_succ n z (Nat.lt_succ_iff.mp j.2)]
  have h : (⟨j.1, Nat.lt_succ_of_le (Nat.lt_succ_iff.mp j.2)⟩ : Fin (n + 1)) = j := Fin.ext rfl
  rw [h]
  ring

/-- `Hinv n` is a right inverse of `H n`. -/
theorem H_tinv (n : ℕ) (z : stdSimplex ℝ (Fin (n + 1))) : H n (Hinv n z) = z := by
  refine Subtype.ext (funext fun j => ?_)
  show ((H n) (Hinv n z)) j = z j
  rw [H_apply, Hfun_Hinv]

theorem H_surjective (n : ℕ) : Function.Surjective (H n) := fun z => ⟨Hinv n z, H_tinv n z⟩

/-! ## The boundary of the cube maps onto the boundary of the simplex -/

/-- A cube point whose image in the simplex has a vanishing coordinate lies on the cube
boundary. -/
theorem Hfun_zero_mem_boundary {n : ℕ} (t : IC n)
    (h : ∃ j : Fin (n + 1), Hfun n t j = 0) : t ∈ Cube.boundary (Fin n) := by
  obtain ⟨j, hj⟩ := h
  rw [Hfun] at hj
  rcases mul_eq_zero.mp hj with h1 | h2
  · rw [Pnat] at h1
    obtain ⟨i, hi, hti⟩ := Finset.prod_eq_zero_iff.mp h1
    rw [Finset.mem_range] at hi
    have hin : i < n := by omega
    have h0 : ((t ⟨i, hin⟩ : unitInterval) : ℝ) = 0 := by
      rw [← tval_of_lt t hin]
      exact hti
    exact ⟨⟨i, hin⟩, Or.inl (Subtype.ext (by simpa using h0))⟩
  · have htv : tval n t j.1 = 1 := by linarith
    have hjn : j.1 < n := by
      by_contra hc
      rw [tval_of_le t (by omega)] at htv
      norm_num at htv
    have h0 : ((t ⟨j.1, hjn⟩ : unitInterval) : ℝ) = 1 := by
      rw [← tval_of_lt t hjn]
      exact htv
    exact ⟨⟨j.1, hjn⟩, Or.inr (Subtype.ext (by simpa using h0))⟩

/-! ## The fibres of `H n` -/

theorem Pnat_succ_sub {n : ℕ} (t : IC n) (k : ℕ) (hk : k ≤ n) :
    Pnat n t (k + 1) = Pnat n t k - Hfun n t ⟨k, Nat.lt_succ_of_le hk⟩ := by
  rw [Pnat_succ]
  have h : Pnat n t k * tval n t k = Pnat n t k - Hfun n t ⟨k, Nat.lt_succ_of_le hk⟩ := by
    rw [Hfun]
    ring
  rw [h]

theorem Hfun_eq_of_H_eq {n : ℕ} {t t' : IC n} (Hz : H n t = H n t') (j : Fin (n + 1)) :
    Hfun n t j = Hfun n t' j := by
  rw [← H_apply, ← H_apply, Hz]

theorem Pnat_eq_of_H_eq {n : ℕ} {t t' : IC n} (Hz : H n t = H n t') :
    ∀ k ≤ n, Pnat n t k = Pnat n t' k := by
  intro k
  induction k with
  | zero => intro _; rw [Pnat_zero, Pnat_zero]
  | succ k ih =>
    intro hk
    rw [Pnat_succ_sub t k (by omega), Pnat_succ_sub t' k (by omega), ih (by omega),
      Hfun_eq_of_H_eq Hz]

/-- If two cube points have the same image under `H n`, they are equal unless both lie on the
boundary of the cube. -/
theorem H_eq_or_boundary (n : ℕ) {t t' : IC n} (Hz : H n t = H n t') :
    t = t' ∨ (t ∈ Cube.boundary (Fin n) ∧ t' ∈ Cube.boundary (Fin n)) := by
  by_cases h0 : ∃ j : Fin (n + 1), (H n t) j = 0
  · right
    refine ⟨Hfun_zero_mem_boundary t ?_, Hfun_zero_mem_boundary t' ?_⟩
    · obtain ⟨j, hj⟩ := h0
      exact ⟨j, by rw [← H_apply]; exact hj⟩
    · obtain ⟨j, hj⟩ := h0
      exact ⟨j, by rw [← H_apply, ← Hz]; exact hj⟩
  · left
    have hpos : ∀ j : Fin (n + 1), 0 < (H n t) j := by
      intro j
      rcases lt_or_eq_of_le ((H n t).2.1 j) with h | h
      · exact h
      · exact absurd ⟨j, h.symm⟩ h0
    have hPpos : ∀ k ≤ n, 0 < Pnat n t k := by
      intro k hk
      have hz : 0 < Pnat n t k * (1 - tval n t k) := by
        simpa [H_apply, Hfun] using hpos ⟨k, Nat.lt_succ_of_le hk⟩
      refine lt_of_le_of_ne (Pnat_nonneg t k) (fun h => ?_)
      rw [← h, zero_mul] at hz
      exact lt_irrefl (0 : ℝ) hz
    have hPeq := Pnat_eq_of_H_eq Hz
    have htval : ∀ k < n, tval n t k = tval n t' k := by
      intro k hk
      have hk' : k ≤ n := le_of_lt hk
      have e1 : tval n t k = 1 - (H n t) ⟨k, Nat.lt_succ_of_le hk'⟩ / Pnat n t k := by
        have hz' : (H n t) ⟨k, Nat.lt_succ_of_le hk'⟩ = Pnat n t k * (1 - tval n t k) := by
          rw [H_apply, Hfun]
        rw [hz', mul_div_cancel_left₀ _ (ne_of_gt (hPpos k hk'))]
        ring
      have e2 : tval n t' k = 1 - (H n t') ⟨k, Nat.lt_succ_of_le hk'⟩ / Pnat n t' k := by
        have hz' : (H n t') ⟨k, Nat.lt_succ_of_le hk'⟩ = Pnat n t' k * (1 - tval n t' k) := by
          rw [H_apply, Hfun]
        have hp : Pnat n t' k ≠ 0 := by
          rw [← hPeq k hk']
          exact ne_of_gt (hPpos k hk')
        rw [hz', mul_div_cancel_left₀ _ hp]
        ring
      rw [e1, e2, hPeq k hk', Hz]
    refine funext fun i => Subtype.ext ?_
    have h := htval i.1 i.2
    rwa [tval_of_lt t i.2, tval_of_lt t' i.2] at h

/-- The collapse `Iⁿ → Sⁿ` is constant on the fibres of `H n`. -/
theorem collapseMap_factorsThrough (n : ℕ) (hn : 1 ≤ n) :
    Function.FactorsThrough (⇑(Work.Stems.collapseMap n hn)) (⇑(H n)) := by
  intro t t' h
  rcases H_eq_or_boundary n h with heq | ⟨hb, hb'⟩
  · rw [heq]
  · rw [Work.Stems.collapseMap_boundary n hn hb, Work.Stems.collapseMap_boundary n hn hb']

/-- `H n` is a quotient map: it is a continuous surjection from a compact space to a Hausdorff
space. -/
theorem H_isQuotientMap (n : ℕ) : Topology.IsQuotientMap (H n) :=
  (Continuous.isClosedMap (H n).continuous).isQuotientMap (H n).continuous (H_surjective n)

/-! ## The collapse simplex -/

/-- **The collapse `Δⁿ → Sⁿ` of the boundary of the simplex.** -/
theorem exists_collapse_simplex (n : ℕ) (hn : 1 ≤ n) :
    ∃ (s : C(stdSimplex ℝ (Fin (n + 1)), Work.Stems.sphere n)) (y : Work.Stems.sphere n),
      s.comp (H n) = Work.Stems.collapseMap n hn ∧
      ∀ z : stdSimplex ℝ (Fin (n + 1)),
        (∃ j : Fin (n + 1), z j = 0) → s z = y := by
  have hquot := H_isQuotientMap n
  refine ⟨hquot.lift (Work.Stems.collapseMap n hn) (collapseMap_factorsThrough n hn),
    Work.Stems.collapseMap n hn 0, hquot.lift_comp _ _, ?_⟩
  intro z hz
  obtain ⟨j, hj⟩ := hz
  have hbd : Hinv n z ∈ Cube.boundary (Fin n) := by
    apply Hfun_zero_mem_boundary
    exact ⟨j, by rw [← H_apply, H_tinv]; exact hj⟩
  have hcomp : (hquot.lift (Work.Stems.collapseMap n hn) (collapseMap_factorsThrough n hn))
        (H n (Hinv n z)) = Work.Stems.collapseMap n hn (Hinv n z) :=
    congrArg (fun f : C(IC n, Work.Stems.sphere n) => f (Hinv n z))
      (hquot.lift_comp (Work.Stems.collapseMap n hn) (collapseMap_factorsThrough n hn))
  rw [show z = H n (Hinv n z) from (H_tinv n z).symm, hcomp]
  exact Work.Stems.collapseMap_boundary n hn hbd

end

end Work.RatHurewicz.Bridge
