import Submission.Work.Item3.EnergyBridge
import Submission.Work.Item3.SystemReducedImage

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
set_option autoImplicit false

/-!
# EnergyExtract: the aggregate data of a half-length-1 balanced factor

Extraction of the hypotheses of `EnergyBridge.energy_k1_factors` from the
aggregate configuration: an image aggregate `es` (with `SystemReduced es`)
whose `j`-th factor is `±α(a_p)` with word `[a] ++ [b]` (half-length 1) and
whose neighbours carry the covering words `X ++ invRev [a]` and
`invRev [b] ++ Z`.  The conclusion is the energy-descending `N`-preserving
single move.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- **The half-length-1 balanced factor data yields an energy move.**  The
balanced factor is at position `j + 1` (so that the left neighbour sits at the
literal index `j` and the right neighbour at `j + 2`, keeping every index
arithmetic-free and `SystemReduced` directly applicable). -/
theorem energy_step_factor_data {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) (es : List (FreeGroup (Fin n))) (_m : Fin n)
    (himg : ImageAggregate α es) (hred : SystemReduced es)
    {j : ℕ} (hj0 : j < es.length) (hj1 : j + 1 < es.length) (hj2 : j + 2 < es.length)
    {p : Fin n} (hbal : es[j + 1] = α (FreeGroup.of p) ∨
      es[j + 1] = (α (FreeGroup.of p))⁻¹)
    (a b : Fin n × Bool) (X Z : List (Fin n × Bool))
    (hmid : (es[j + 1]).toWord = [a] ++ [b])
    (hl : (es[j]).toWord = X ++ FreeGroup.invRev [a])
    (hr : (es[j + 2]).toWord = FreeGroup.invRev [b] ++ Z) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
      N (α * γ) ≤ N α ∧ eEnergy (α * γ) < eEnergy α := by
  classical
  -- neighbour coordinates
  obtain ⟨v, hvraw⟩ := aggregate_factor_coordinate α es himg hj0
  obtain ⟨u, huraw⟩ := aggregate_factor_coordinate α es himg hj2
  -- the balanced factor's element identity
  have hmk : FreeGroup.mk (coordWord α p) = α (FreeGroup.of p) := FreeGroup.mk_toWord
  have hfac : α (FreeGroup.of p) = FreeGroup.mk ([a] ++ [b]) ∨
      (α (FreeGroup.of p))⁻¹ = FreeGroup.mk ([a] ++ [b]) := by
    have hsrc : FreeGroup.mk ([a] ++ [b]) = es[j + 1] := by
      rw [← hmid]
      exact FreeGroup.mk_toWord
    rcases hbal with h | h
    · left
      rw [← h, ← hsrc]
    · right
      rw [← h, ← hsrc]
  -- a ≠ b
  have hredab : FreeGroup.IsReduced ([a] ++ [b]) := by
    rw [← hmid]
    exact FreeGroup.isReduced_toWord
  have hab : a.1 ≠ b.1 := fst_ne_of_factor α p a b hredab hfac
  -- covering forms for the neighbours
  have hv : coordWord α v = X ++ FreeGroup.invRev [a] ∨
      coordWord α v = [a] ++ FreeGroup.invRev X := by
    rcases hvraw with hv | hv
    · left
      show (α (FreeGroup.of v)).toWord = X ++ FreeGroup.invRev [a]
      rw [← hv]
      exact hl
    · right
      have h1 : α (FreeGroup.of v) = (es[j])⁻¹ := by rw [hv, inv_inv]
      show (α (FreeGroup.of v)).toWord = [a] ++ FreeGroup.invRev X
      rw [h1, FreeGroup.toWord_inv, hl, FreeGroup.invRev_append, FreeGroup.invRev_invRev]
  have hu : coordWord α u = FreeGroup.invRev [b] ++ Z ∨
      coordWord α u = FreeGroup.invRev Z ++ [b] := by
    rcases huraw with hu | hu
    · left
      show (α (FreeGroup.of u)).toWord = FreeGroup.invRev [b] ++ Z
      rw [← hu]
      exact hr
    · right
      have h1 : α (FreeGroup.of u) = (es[j + 2])⁻¹ := by rw [hu, inv_inv]
      show (α (FreeGroup.of u)).toWord = FreeGroup.invRev Z ++ [b]
      rw [h1, FreeGroup.toWord_inv, hr, FreeGroup.invRev_append, FreeGroup.invRev_invRev]
  -- word contradiction for equal adjacent factors (left)
  have heq_contr : (es[j]).toWord = (es[j + 1]).toWord → False := by
    intro hword
    have hwordL : X ++ FreeGroup.invRev [a] = [a] ++ [b] := hl.symm.trans (hword.trans hmid)
    have hlen : X.length = 1 := by
      have hc := congrArg List.length hwordL
      rw [List.length_append, List.length_append] at hc
      simp only [invRev_singleton, List.length_singleton] at hc
      omega
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
    have hword' : x :: (a.1, !a.2) :: ([] : List (Fin n × Bool)) = a :: b :: [] := by
      simpa [invRev_singleton] using hwordL
    have h1 := List.cons.inj hword'
    have h2 := List.cons.inj h1.2
    have hbrel : b = (a.1, !a.2) := h2.1.symm
    have hrel := (FreeGroup.isReduced_cons_cons.mp hredab).1
    have hsame : a.1 = b.1 := by rw [hbrel]
    have hcon := hrel hsame
    rw [hbrel] at hcon
    simp at hcon
  have heq_contr_r : (es[j + 2]).toWord = (es[j + 1]).toWord → False := by
    intro hword
    have hwordL : FreeGroup.invRev [b] ++ Z = [a] ++ [b] := hr.symm.trans (hword.trans hmid)
    have hlen : Z.length = 1 := by
      have hc := congrArg List.length hwordL
      rw [List.length_append, List.length_append] at hc
      simp only [invRev_singleton, List.length_singleton] at hc
      omega
    obtain ⟨z, rfl⟩ := List.length_eq_one_iff.mp hlen
    have hword' : (b.1, !b.2) :: z :: ([] : List (Fin n × Bool)) = a :: b :: [] := by
      simpa [invRev_singleton, List.append_assoc] using hwordL
    have h1 := List.cons.inj hword'
    have h2 := List.cons.inj h1.2
    have harel : a = (b.1, !b.2) := h1.1.symm
    have hrel := (FreeGroup.isReduced_cons_cons.mp hredab).1
    have hsame : a.1 = b.1 := by rw [harel]
    have hcon := hrel hsame
    rw [harel] at hcon
    simp at hcon
  have hvne : v ≠ p := by
    intro hvp
    subst hvp
    rcases hvraw with hv | hv <;> rcases hbal with hb | hb
    · exact heq_contr (by rw [hv, hb])
    · exact absurd (by rw [hv, hb] : es[j + 1] = (es[j])⁻¹) (hred.2 j hj1)
    · exact absurd (by rw [hb, hv]; simp : es[j + 1] = (es[j])⁻¹) (hred.2 j hj1)
    · exact heq_contr (by rw [hv, hb])
  have hune : u ≠ p := by
    intro hup
    subst hup
    rcases huraw with hu | hu <;> rcases hbal with hb | hb
    · exact heq_contr_r (by rw [hu, hb])
    · exact absurd (by rw [hu, hb]; simp : es[j + 2] = (es[j + 1])⁻¹) (hred.2 (j + 1) hj2)
    · exact absurd (by rw [hu, hb] : es[j + 2] = (es[j + 1])⁻¹) (hred.2 (j + 1) hj2)
    · exact heq_contr_r (by rw [hu, hb])
  -- the balanced row's word in the two orientations, then the energy move
  rcases hbal with hbal | hbal
  · have hp : coordWord α p = [a] ++ [b] := by
      rw [← hmid, hbal]
      rfl
    exact energy_k1_factors α hres hvne hune a b X Z true hab (by simpa using hp) hv hu
  · have hp : coordWord α p = FreeGroup.invRev [b] ++ FreeGroup.invRev [a] := by
      have h2 : (α (FreeGroup.of p)).toWord = ((es[j + 1])⁻¹).toWord := by
        rw [hbal, inv_inv]
      show (α (FreeGroup.of p)).toWord = FreeGroup.invRev [b] ++ FreeGroup.invRev [a]
      rw [h2, FreeGroup.toWord_inv, hmid, FreeGroup.invRev_append]
    exact energy_k1_factors α hres hvne hune a b X Z false hab (by simpa using hp) hv hu

/-- Getting the element at `j - 1 + 1` is getting it at `j`. -/
lemma getElem_sub_one_add_one {α : Type*} {l : List α} {j : ℕ} (h0 : 0 < j)
    (hj : j < l.length) : l[j - 1 + 1] = l[j] := by
  have h1 : l[j - 1 + 1]? = l[j]? := by
    congr 1
    omega
  rw [List.getElem?_eq_getElem (by omega : j - 1 + 1 < l.length),
    List.getElem?_eq_getElem hj] at h1
  simpa using h1

/-- Getting the element at `j - 1 + 2` is getting it at `j + 1`. -/
lemma getElem_sub_one_add_two {α : Type*} {l : List α} {j : ℕ} (h0 : 0 < j)
    (hj : j + 1 < l.length) : l[j - 1 + 2] = l[j + 1] := by
  have h1 : l[j - 1 + 2]? = l[j + 1]? := by
    congr 1
    omega
  rw [List.getElem?_eq_getElem (by omega : j - 1 + 2 < l.length),
    List.getElem?_eq_getElem hj] at h1
  simpa using h1

/-- **The half-length-1 balanced factor data yields an energy move** (balanced
factor at position `j`, so the left neighbour sits at `j - 1`). -/
theorem energy_step_factor_data' {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) (es : List (FreeGroup (Fin n))) (m : Fin n)
    (himg : ImageAggregate α es) (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hj0 : 0 < j) (hj1 : j + 1 < es.length)
    {p : Fin n} (hbal : es[j] = α (FreeGroup.of p) ∨ es[j] = (α (FreeGroup.of p))⁻¹)
    (a b : Fin n × Bool) (X Z : List (Fin n × Bool))
    (hmid : (es[j]).toWord = [a] ++ [b])
    (hl : (es[j - 1]).toWord = X ++ FreeGroup.invRev [a])
    (hr : (es[j + 1]).toWord = FreeGroup.invRev [b] ++ Z) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
      N (α * γ) ≤ N α ∧ eEnergy (α * γ) < eEnergy α := by
  have hshift1 : es[j - 1 + 1] = es[j] := getElem_sub_one_add_one hj0 hj
  have hshift2 : es[j - 1 + 2] = es[j + 1] := getElem_sub_one_add_two hj0 hj1
  refine energy_step_factor_data α hres es m himg hred
    (j := j - 1) (p := p) (by omega) (by omega) (by omega) ?_ a b X Z ?_ hl ?_
  · rcases hbal with h | h <;> [left; right] <;> rw [hshift1] <;> exact h
  · rw [hshift1]; exact hmid
  · rw [hshift2]; exact hr

/-- **The Fall-II half-length-1 configuration yields an energy move.**  This is
`energy_step_factor_data'` in the `RebalanceState` interface: the data is the
`ExactlyHalfAbsorbed` witness (an image aggregate of `S.α` whose `j`-th factor
is `±S.α(a_{row p})` with word `[a] ++ [b]`, the neighbours covered by
`X ++ invRev [a]` and `invRev [b] ++ Z`), with half-length `1`. -/
theorem energy_step_halfAbsorbed {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (hres : NoEndCancel n S.α) (m : Fin n) (j : ℕ)
    (hj : j < (imageAggregate S.α m).length) (hj0 : 0 < j)
    (hj1 : j + 1 < (imageAggregate S.α m).length)
    (hbal : (imageAggregate S.α m)[j] = S.α (FreeGroup.of (S.row p)) ∨
      (imageAggregate S.α m)[j] = (S.α (FreeGroup.of (S.row p)))⁻¹)
    (a b : Fin n × Bool) (X Z : List (Fin n × Bool))
    (hmid : ((imageAggregate S.α m)[j]).toWord = [a] ++ [b])
    (hl : ((imageAggregate S.α m)[j - 1]).toWord = X ++ FreeGroup.invRev [a])
    (hr : ((imageAggregate S.α m)[j + 1]).toWord = FreeGroup.invRev [b] ++ Z) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
      N (S.α * γ) ≤ N S.α ∧ eEnergy (S.α * γ) < eEnergy S.α :=
  energy_step_factor_data' S.α hres (imageAggregate S.α m) m
    (imageAggregate_isImageAggregate S.α m) (systemReduced_imageAggregate S.α m)
    hj hj0 hj1 hbal a b X Z hmid hl hr

/-- **The half-length-1 Fall-II configuration of an automorphism yields an
energy move** (coordinate form, no `RebalanceState` needed). -/
theorem energy_step_aggregate {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) (m : Fin n) {j : ℕ}
    (hj : j < (imageAggregate α m).length) (hj0 : 0 < j)
    (hj1 : j + 1 < (imageAggregate α m).length)
    {q : Fin n} (hbal : (imageAggregate α m)[j] = α (FreeGroup.of q) ∨
      (imageAggregate α m)[j] = (α (FreeGroup.of q))⁻¹)
    (a b : Fin n × Bool) (X Z : List (Fin n × Bool))
    (hmid : ((imageAggregate α m)[j]).toWord = [a] ++ [b])
    (hl : ((imageAggregate α m)[j - 1]).toWord = X ++ FreeGroup.invRev [a])
    (hr : ((imageAggregate α m)[j + 1]).toWord = FreeGroup.invRev [b] ++ Z) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
      N (α * γ) ≤ N α ∧ eEnergy (α * γ) < eEnergy α :=
  energy_step_factor_data' α hres (imageAggregate α m) m
    (imageAggregate_isImageAggregate α m) (systemReduced_imageAggregate α m)
    hj hj0 hj1 hbal a b X Z hmid hl hr

end Submission.Nielsen
