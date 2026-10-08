/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Counting the elements of order `r` in `SL(2,q)`, `r` an odd prime

Putting together the pieces:

* `SplitCount` : the eigenvector double count gives
  `2 (q-1) · #{x : orderOf x = r ∧ HasEigenvector}  = (q²-1) · #{λ ∈ Fˣ : orderOf λ = r} · q`;
* `TraceClassCard` : for `Rootless t` the trace-`t` class is non-empty of size `q(q-1)` and its
  elements have order `r` exactly when `quad t ∣ X^r - 1`;
* `RootlessQuadDvd` : `2 · #{t : Rootless t ∧ quad t ∣ X^r - 1} = if r ∣ q+1 then r-1 else 0`;
* and `#{λ ∈ Fˣ : orderOf λ = r} = if r ∣ q-1 then r-1 else 0`.

Hence `2 (q-1) · #{x : orderOf x = r}` is `(q-1)(r-1)q(q-1)` when `r ∣ q+1` and
`(q-1)(r-1)q(q+1)` when `r ∣ q-1`.
-/
import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Props.Count.Defs
import Submission.Work.L2F.Props.Count.Basic
import Submission.Work.L2F.Props.Count.TraceClassCard
import Submission.Work.L2F.Props.Count.SplitCount
import Submission.Work.L2F.Props.Count.RootlessQuadDvd
import Submission.Work.L2F.Props.Count.PslOrderEqSl
import Submission.Work.L2F.Props.Count.SubgroupCount

open scoped MatrixGroups
open Matrix Polynomial

namespace Work.L2F.Count

variable {F : Type*} [Field F]

/-! ## Elementary counting helpers -/

/-- Cardinality of a decidable partition of a subtype. -/
theorem card_split {α : Type*} [Fintype α] (P Q : α → Prop) :
    Nat.card {x : α // P x} =
      Nat.card {x : α // P x ∧ Q x} + Nat.card {x : α // P x ∧ ¬ Q x} := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter P) (p := Q)
  simp only [Finset.filter_filter] at h1
  rw [natCard_subtype_eq_filter_card P, natCard_subtype_eq_filter_card (fun x => P x ∧ Q x),
    natCard_subtype_eq_filter_card (fun x => P x ∧ ¬ Q x)]
  exact h1.symm

theorem indicator_and_of {p q : Prop} (h : p) : indicator (p ∧ q) = indicator q := by
  by_cases hq : q
  · rw [indicator_eq_one ⟨h, hq⟩, indicator_eq_one hq]
  · rw [indicator_eq_zero (fun hpq => hq hpq.2), indicator_eq_zero hq]

/-- The number of elements of order `r` in `Fˣ`. -/
theorem card_units_orderOf (F : Type*) [Field F] [Fintype F] (r : ℕ) (hr : r.Prime) :
    Nat.card {u : Fˣ // orderOf u = r} = if r ∣ (Nat.card F - 1) then r - 1 else 0 := by
  classical
  by_cases hdvd : r ∣ Nat.card F - 1
  · rw [if_pos hdvd]
    have hfac : r ∣ Fintype.card Fˣ := by
      rw [← Nat.card_eq_fintype_card, Nat.card_units]
      exact hdvd
    have htot := IsCyclic.card_orderOf_eq_totient (α := Fˣ) hfac
    rw [Nat.totient_prime hr] at htot
    rw [← htot]
    exact natCard_subtype_eq_filter_card (fun u : Fˣ => orderOf u = r)
  · rw [if_neg hdvd, Nat.card_eq_zero]
    refine Or.inl ⟨fun u => ?_⟩
    have hmem : orderOf u.val ∣ Nat.card F - 1 := by
      have h1 : Nat.card (Subgroup.zpowers u.val) ∣ Nat.card Fˣ :=
        Subgroup.card_subgroup_dvd_card (Subgroup.zpowers u.val)
      rwa [Nat.card_zpowers, Nat.card_units] at h1
    rw [u.2] at hmem
    exact hdvd hmem

/-! ## The elements of order `r` without eigenvector, by traces -/

/-- The number of elements of order `r` without eigenvector is the sum over `t : F` of the
number of such elements of trace `t`. -/
theorem card_nonsplit_eq_sum_fibers [Fintype F] (h2 : (2 : F) ≠ 0) (r : ℕ) :
    Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
        orderOf x = r ∧ ¬ HasEigenvector F (x : Matrix (Fin 2) (Fin 2) F)}
      = ∑ t : F, Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
          (orderOf x = r ∧ ¬ HasEigenvector F (x : Matrix (Fin 2) (Fin 2) F))
            ∧ (x : Matrix (Fin 2) (Fin 2) F).trace = t} := by
  classical
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv
    (fun x : {x : Matrix.SpecialLinearGroup (Fin 2) F //
        orderOf x = r ∧ ¬ HasEigenvector F (x : Matrix (Fin 2) (Fin 2) F)} =>
      (x.1 : Matrix (Fin 2) (Fin 2) F).trace)).symm]
  rw [Nat.card_sigma]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  exact Nat.card_congr (subtypeSubtypeEquiv
    (fun x : Matrix.SpecialLinearGroup (Fin 2) F =>
      orderOf x = r ∧ ¬ HasEigenvector F (x : Matrix (Fin 2) (Fin 2) F))
    (fun x : Matrix.SpecialLinearGroup (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F).trace = t))

/-- The number of elements of order `r` of `SL(2,F)` without eigenvector is
`#{t : Rootless t, quad t ∣ X^r - 1} · q(q-1)`. -/
theorem card_nonsplit_orderOf (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) (r : ℕ)
    (hr : r.Prime) :
    Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
        orderOf x = r ∧ ¬ HasEigenvector F (x : Matrix (Fin 2) (Fin 2) F)}
      = Nat.card {t : F // Rootless F t ∧ quad F t ∣ (Polynomial.X ^ r - 1)}
        * (Nat.card F * (Nat.card F - 1)) := by
  classical
  rw [card_nonsplit_eq_sum_fibers (F := F) h2 r]
  have hstep : ∀ t : F,
      Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
          (orderOf x = r ∧ ¬ HasEigenvector F (x : Matrix (Fin 2) (Fin 2) F))
            ∧ (x : Matrix (Fin 2) (Fin 2) F).trace = t}
        = (Nat.card F * (Nat.card F - 1))
          * indicator (Rootless F t ∧ quad F t ∣ (Polynomial.X ^ r - 1)) := by
    intro t
    by_cases ht : Rootless F t
    · have h1 : Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
          (orderOf x = r ∧ ¬ HasEigenvector F (x : Matrix (Fin 2) (Fin 2) F))
            ∧ (x : Matrix (Fin 2) (Fin 2) F).trace = t}
          = Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
            (x : Matrix (Fin 2) (Fin 2) F).trace = t ∧ orderOf x = r} := by
        refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
        intro x
        constructor
        · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h3, h1⟩
        · rintro ⟨h3, h1⟩
          exact ⟨⟨h1, (not_hasEigenvector_iff_rootless x).mpr (by rw [h3]; exact ht)⟩, h3⟩
      rw [h1, Work.L2F.Props.Count.TraceClassCard F h2 ht r hr, indicator_and_of ht]
    · rw [indicator_eq_zero (fun hpq => ht hpq.1), mul_zero]
      refine Nat.card_eq_zero.mpr (Or.inl ⟨fun x => ?_⟩)
      have hR : Rootless F ((x.1 : Matrix (Fin 2) (Fin 2) F).trace) :=
        (not_hasEigenvector_iff_rootless x.1).mp x.2.1.2
      rw [x.2.2] at hR
      exact ht hR
  rw [Finset.sum_congr rfl (fun t _ => hstep t), ← Finset.mul_sum, sum_indicator]
  exact mul_comm _ _

/-! ## The count of elements of order `r` in `SL(2,F)` -/

/-- The number of elements of order `r` in `SL(2,F)`, when `r` is an odd prime dividing `q+1`. -/
theorem sl_count_of_dvd_add (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (hnsq : ∃ d : F, d ≠ 0 ∧ ∀ a : F, a * a ≠ d) (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrc : (r : F) ≠ 0) (hdvd : r ∣ Nat.card F + 1) :
    2 * (Nat.card F - 1) * Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
        orderOf x = r}
      = (Nat.card F - 1) * (r - 1) * Nat.card F * (Nat.card F - 1) := by
  classical
  have hq1 : 1 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.pos_of_ne_zero Fintype.card_ne_zero
  have hsplit := card_split (α := Matrix.SpecialLinearGroup (Fin 2) F)
    (fun x => orderOf x = r) (fun x => HasEigenvector F (x : Matrix (Fin 2) (Fin 2) F))
  have hA := Work.L2F.Props.Count.SplitCount F h2 r hr hr2 hrc
  have hB := card_nonsplit_orderOf F h2 r hr
  have hT := Work.L2F.Props.Count.RootlessQuadDvd F h2 hnsq r hr hr2
  have hM := card_units_orderOf F r hr
  have hnot : ¬ r ∣ Nat.card F - 1 := by
    intro h
    have hsub := Nat.dvd_sub hdvd h
    rw [show Nat.card F + 1 - (Nat.card F - 1) = 2 by omega] at hsub
    have hle := Nat.le_of_dvd (by norm_num) hsub
    have := hr.two_le
    omega
  rw [if_neg hnot] at hM
  rw [if_pos hdvd] at hT
  rw [hM] at hA
  have hA' : 2 * (Nat.card F - 1) * Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
      orderOf x = r ∧ HasEigenvector F (x : Matrix (Fin 2) (Fin 2) F)} = 0 := by
    rw [hA]; ring
  have hB' : 2 * (Nat.card F - 1) * Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
      orderOf x = r ∧ ¬ HasEigenvector F (x : Matrix (Fin 2) (Fin 2) F)}
      = (Nat.card F - 1) * (r - 1) * Nat.card F * (Nat.card F - 1) := by
    rw [hB, ← hT]; ring
  rw [hsplit, Nat.mul_add, hA', hB', zero_add]

/-- The number of elements of order `r` in `SL(2,F)`, when `r` is an odd prime dividing `q-1`. -/
theorem sl_count_of_dvd_sub (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (hnsq : ∃ d : F, d ≠ 0 ∧ ∀ a : F, a * a ≠ d) (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrc : (r : F) ≠ 0) (hdvd : r ∣ Nat.card F - 1) :
    2 * (Nat.card F - 1) * Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
        orderOf x = r}
      = (Nat.card F - 1) * (r - 1) * Nat.card F * (Nat.card F + 1) := by
  classical
  have hq1 : 1 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.pos_of_ne_zero Fintype.card_ne_zero
  have hsplit := card_split (α := Matrix.SpecialLinearGroup (Fin 2) F)
    (fun x => orderOf x = r) (fun x => HasEigenvector F (x : Matrix (Fin 2) (Fin 2) F))
  have hA := Work.L2F.Props.Count.SplitCount F h2 r hr hr2 hrc
  have hB := card_nonsplit_orderOf F h2 r hr
  have hT := Work.L2F.Props.Count.RootlessQuadDvd F h2 hnsq r hr hr2
  have hM := card_units_orderOf F r hr
  have hnot : ¬ r ∣ Nat.card F + 1 := by
    intro h
    have hsub := Nat.dvd_sub h hdvd
    rw [show Nat.card F + 1 - (Nat.card F - 1) = 2 by omega] at hsub
    have hle := Nat.le_of_dvd (by norm_num) hsub
    have := hr.two_le
    omega
  rw [if_pos hdvd] at hM
  rw [if_neg hnot] at hT
  rw [hM] at hA
  have hA' : 2 * (Nat.card F - 1) * Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
      orderOf x = r ∧ HasEigenvector F (x : Matrix (Fin 2) (Fin 2) F)}
      = (Nat.card F - 1) * (r - 1) * Nat.card F * (Nat.card F + 1) := by
    rw [hA]
    have hsq : Nat.card F ^ 2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) := by
      have := Nat.sq_sub_sq (Nat.card F) 1
      simpa using this
    rw [hsq]; ring
  have hT0 : Nat.card {t : F // Rootless F t ∧ quad F t ∣ (Polynomial.X ^ r - 1)} = 0 := by
    have := hT
    omega
  have hB' : 2 * (Nat.card F - 1) * Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
      orderOf x = r ∧ ¬ HasEigenvector F (x : Matrix (Fin 2) (Fin 2) F)} = 0 := by
    rw [hB, hT0]; ring
  rw [hsplit, Nat.mul_add, hA', hB', add_zero]

end Work.L2F.Count

namespace Work.L2F.Count

variable {F : Type*} [Field F]

/-- The number of subgroups of order `r` in `PSL(2,q)`, `r` an odd prime dividing `q+1`. -/
theorem prime_subgroup_count_add (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (hnsq : ∃ d : F, d ≠ 0 ∧ ∀ a : F, a * a ≠ d) (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrc : (r : F) ≠ 0) (hdvd : r ∣ Nat.card F + 1) :
    2 * Nat.card {Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) //
        Nat.card Y = r}
      = Nat.card F * (Nat.card F - 1) := by
  classical
  have hq1 : 1 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.pos_of_ne_zero Fintype.card_ne_zero
  have hr1 : 1 < r := hr.one_lt
  have hq2 : 1 < Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hsl := sl_count_of_dvd_add F h2 hnsq r hr hr2 hrc hdvd
  have hE : (r - 1) * Nat.card {Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) //
      Nat.card Y = r} = Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F // orderOf x = r} := by
    rw [Work.L2F.Props.Count.SubgroupCount (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) r hr,
      Work.L2F.Props.Count.PslOrderEqSl F h2 r hr hr2]
  have hmain : (Nat.card F - 1) * (r - 1) *
        (2 * Nat.card {Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) //
          Nat.card Y = r})
      = (Nat.card F - 1) * (r - 1) * (Nat.card F * (Nat.card F - 1)) := by
    rw [← hE] at hsl
    rw [show 2 * (Nat.card F - 1) *
          ((r - 1) * Nat.card {Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) //
            Nat.card Y = r})
        = (Nat.card F - 1) * (r - 1) *
          (2 * Nat.card {Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) //
            Nat.card Y = r}) by ring] at hsl
    rw [show (Nat.card F - 1) * (r - 1) * Nat.card F * (Nat.card F - 1)
        = (Nat.card F - 1) * (r - 1) * (Nat.card F * (Nat.card F - 1)) by ring] at hsl
    exact hsl
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (by omega) (by omega)) hmain

/-- The number of subgroups of order `r` in `PSL(2,q)`, `r` an odd prime dividing `q-1`. -/
theorem prime_subgroup_count_sub (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (hnsq : ∃ d : F, d ≠ 0 ∧ ∀ a : F, a * a ≠ d) (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrc : (r : F) ≠ 0) (hdvd : r ∣ Nat.card F - 1) :
    2 * Nat.card {Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) //
        Nat.card Y = r}
      = Nat.card F * (Nat.card F + 1) := by
  classical
  have hq1 : 1 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.pos_of_ne_zero Fintype.card_ne_zero
  have hr1 : 1 < r := hr.one_lt
  have hq2 : 1 < Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hsl := sl_count_of_dvd_sub F h2 hnsq r hr hr2 hrc hdvd
  have hE : (r - 1) * Nat.card {Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) //
      Nat.card Y = r} = Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F // orderOf x = r} := by
    rw [Work.L2F.Props.Count.SubgroupCount (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) r hr,
      Work.L2F.Props.Count.PslOrderEqSl F h2 r hr hr2]
  have hmain : (Nat.card F - 1) * (r - 1) *
        (2 * Nat.card {Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) //
          Nat.card Y = r})
      = (Nat.card F - 1) * (r - 1) * (Nat.card F * (Nat.card F + 1)) := by
    rw [← hE] at hsl
    rw [show 2 * (Nat.card F - 1) *
          ((r - 1) * Nat.card {Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) //
            Nat.card Y = r})
        = (Nat.card F - 1) * (r - 1) *
          (2 * Nat.card {Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) //
            Nat.card Y = r}) by ring] at hsl
    rw [show (Nat.card F - 1) * (r - 1) * Nat.card F * (Nat.card F + 1)
        = (Nat.card F - 1) * (r - 1) * (Nat.card F * (Nat.card F + 1)) by ring] at hsl
    exact hsl
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (by omega) (by omega)) hmain

end Work.L2F.Count
