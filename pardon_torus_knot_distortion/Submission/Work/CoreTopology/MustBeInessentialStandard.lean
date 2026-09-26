import Submission.Work.CoreTopology.IntersectionNumberStandard
import Submission.Work.CoreTopology.EssentialLoop

/-!
# Pardon's `mustbeinessential` for the standard torus

For the standard torus and the standard `(p,q)` curve, the contrapositive of Pardon's
`mustbeinessential` can be proved once the loop in question is *compressing*: if a region
`S ⊆ ℝ³` contains a simple compressing essential loop `α` of the torus, then `S` meets the
`(p,q)` curve in at least `min p q = I(F, β)` points.  Indeed `α ⊆ S` and, by
`compressing_winding_dichotomy`, `α` has winding vector `(a,0)` or `(0,b)`, so
`min_le_encard_inter_standardCurve` gives `min p q ≤ |α ∩ β| ≤ |β ∩ S|`.

The remaining geometric input of Pardon's Lemma 2 — that an *innermost* essential component of
`S ∩ F` is (after eliminating the inessential intersections of the disc it bounds) compressing —
is kept as the explicit hypothesis `hclean` in the general form
`Work.CoreTopology.mustbeinessential`, which applies to an arbitrary parametrised torus.  Here we
record what is available unconditionally on the standard torus.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreTopology

noncomputable section

/-- The region `U ⊆ ℝ³` contains a *simple compressing* essential loop of the standard torus. -/
def ContainsCompressingLoop (U : Set R3) : Prop :=
  ∃ α : ClosedCurve standard, IsSimple standard α ∧ IsEssential standard α ∧
    BoundsDiskInComplement standard α ∧ ∀ t : ℝ, α.γ t ∈ U

/-- `S` meets the standard `(p,q)` curve in at least `min p q` points as soon as it contains a
simple closed curve of the torus whose (nonzero) winding vector has a vanishing component. -/
theorem le_encard_of_essential_loop_in (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (S : Set R3) (α : ClosedCurve standard)
    (hsimple : IsSimple standard α) (L : LiftOf standard α) (hne : L.winding ≠ (0, 0))
    (hdich : (L.winding).1 = 0 ∨ (L.winding).2 = 0) (hS : ∀ t : ℝ, α.γ t ∈ S) :
    (Nat.min p q : ℕ∞) ≤ Set.encard (Set.range (standardCurve p q).γ ∩ S) := by
  refine le_trans (min_le_encard_inter_standardCurve p q hp hq hc α hsimple L hne hdich) ?_
  apply Set.encard_mono
  rintro x ⟨⟨t, rfl⟩, hx⟩
  exact ⟨hx, hS t⟩

/-- **Pardon's `mustbeinessential`, contrapositive, for the standard torus.**  If a region
`S ⊆ ℝ³` contains a simple compressing essential loop of the standard torus, then `S` meets the
standard `(p,q)` curve in at least `min p q = I(F, β)` points. -/
theorem le_encard_of_compressing_loop_in (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (S : Set R3) (α : ClosedCurve standard)
    (hsimple : IsSimple standard α) (hess : IsEssential standard α)
    (hb : BoundsDiskInComplement standard α) (hS : ∀ t : ℝ, α.γ t ∈ S) :
    (Nat.min p q : ℕ∞) ≤ Set.encard (Set.range (standardCurve p q).γ ∩ S) := by
  have hess' : IsEssential standard α := hess
  rcases compressing_winding_dichotomy α hess' hb with h | h
  · obtain ⟨L, hw⟩ := hess
    exact le_encard_of_essential_loop_in p q hp hq hc S α hsimple L hw (Or.inr (h L)) hS
  · obtain ⟨L, hw⟩ := hess
    exact le_encard_of_essential_loop_in p q hp hq hc S α hsimple L hw (Or.inl (h L)) hS

/-- **Pardon's `mustbeinessential` for the standard torus, in the form used in the proof**: a
region of `ℝ³` meeting the standard `(p,q)` curve in fewer than `min p q = I(F, β)` points
contains no simple compressing essential loop of the torus. -/
theorem not_containsCompressingLoop_of_encard_lt (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (S : Set R3)
    (hS : Set.encard (Set.range (standardCurve p q).γ ∩ S) < (Nat.min p q : ℕ∞)) :
    ¬ ContainsCompressingLoop S := by
  rintro ⟨α, hsimple, hess, hb, hS'⟩
  exact absurd (le_encard_of_compressing_loop_in p q hp hq hc S α hsimple hess hb hS')
    (not_le.mpr hS)

end

end Work.CoreTopology
