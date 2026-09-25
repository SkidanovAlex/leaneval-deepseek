/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Sup-norms and Hölder seminorms built from the *global* iterated derivative

For functions `f : Y → ℂ` on a real normed space and an arbitrary set `Ω` we define

  `gDN i f Ω = ⨆ x ∈ Ω, ofReal ‖iteratedFDeriv ℝ i f x‖`,
  `gSN i α f Ω = ⨆ x ∈ Ω, ⨆ y ∈ Ω, ⨆ (x ≠ y), ofReal (‖D^i f x - D^i f y‖ / ‖x - y‖^α)`

using the *global* iterated derivative `iteratedFDeriv` (which agrees with the within derivative
`iteratedFDerivWithin ℝ i f Ω` when `Ω` is open).  This is convenient for sets such as the
hyperplane `{p.2 = 0}` or closed half spaces, for which the within derivatives differ from the
global ones at the boundary points.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.NN.Seeley.Setup

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

set_option linter.unusedSectionVars false

namespace Work.NN.Final

open Work.CR.Flat.Holder

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- Supremum over `Ω` of the norm of the global `i`-th iterated derivative. -/
noncomputable def gDN (i : ℕ) (f : Y → A) (Ω : Set Y) : ℝ≥0∞ :=
  ⨆ x ∈ Ω, ENNReal.ofReal ‖iteratedFDeriv ℝ i f x‖

/-- Hölder seminorm of order `α` of the global `i`-th iterated derivative, over a pair of
points of `Ω`. -/
noncomputable def gSN (i : ℕ) (α : ℝ) (f : Y → A) (Ω : Set Y) : ℝ≥0∞ :=
  ⨆ x ∈ Ω, ⨆ y ∈ Ω, ⨆ (_ : x ≠ y),
    ENNReal.ofReal (‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ / ‖x - y‖ ^ α)

lemma le_gDN (i : ℕ) {f : Y → A} {Ω : Set Y} {x : Y} (hx : x ∈ Ω) :
    ENNReal.ofReal ‖iteratedFDeriv ℝ i f x‖ ≤ gDN i f Ω :=
  le_iSup₂_of_le x hx le_rfl

lemma le_gSN (i : ℕ) (α : ℝ) {f : Y → A} {Ω : Set Y} {x y : Y}
    (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y) :
    ENNReal.ofReal (‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ / ‖x - y‖ ^ α)
      ≤ gSN i α f Ω :=
  le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))

lemma gDN_mono {Ω Ω' : Set Y} (h : Ω' ⊆ Ω) (i : ℕ) (f : Y → A) :
    gDN i f Ω' ≤ gDN i f Ω :=
  iSup₂_le fun x hx => le_iSup₂_of_le x (h hx) le_rfl

lemma gSN_mono {Ω Ω' : Set Y} (h : Ω' ⊆ Ω) (i : ℕ) (α : ℝ) (f : Y → A) :
    gSN i α f Ω' ≤ gSN i α f Ω :=
  iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy =>
    le_iSup₂_of_le x (h hx) (le_iSup₂_of_le y (h hy) (le_iSup_of_le hxy le_rfl))

lemma gDN_congr_of_isOpen {i : ℕ} {f g : Y → A} {Ω : Set Y} (hΩ : IsOpen Ω)
    (h : ∀ x ∈ Ω, f x = g x) : gDN i f Ω = gDN i g Ω := by
  have key : ∀ x ∈ Ω, iteratedFDeriv ℝ i f x = iteratedFDeriv ℝ i g x := by
    intro x hx
    have h1 : iteratedFDerivWithin ℝ i f Ω x = iteratedFDerivWithin ℝ i g Ω x :=
      Filter.EventuallyEq.iteratedFDerivWithin_eq (s := Ω)
        (Filter.eventuallyEq_of_mem self_mem_nhdsWithin h) (h x hx) i
    have e1 : Set.EqOn (iteratedFDerivWithin ℝ i f Ω) (iteratedFDeriv ℝ i f) Ω :=
      iteratedFDerivWithin_of_isOpen (s := Ω) (f := f) i hΩ
    have e2 : Set.EqOn (iteratedFDerivWithin ℝ i g Ω) (iteratedFDeriv ℝ i g) Ω :=
      iteratedFDerivWithin_of_isOpen (s := Ω) (f := g) i hΩ
    rw [← e1 hx, h1, e2 hx]
  refine le_antisymm (iSup₂_le fun x hx => ?_) (iSup₂_le fun x hx => ?_)
  · rw [key x hx]; exact le_gDN i hx
  · rw [← key x hx]; exact le_gDN i hx

lemma gSN_congr_of_isOpen {i : ℕ} {α : ℝ} {f g : Y → A} {Ω : Set Y} (hΩ : IsOpen Ω)
    (h : ∀ x ∈ Ω, f x = g x) : gSN i α f Ω = gSN i α g Ω := by
  have key : ∀ x ∈ Ω, iteratedFDeriv ℝ i f x = iteratedFDeriv ℝ i g x := by
    intro x hx
    have h1 : iteratedFDerivWithin ℝ i f Ω x = iteratedFDerivWithin ℝ i g Ω x :=
      Filter.EventuallyEq.iteratedFDerivWithin_eq (s := Ω)
        (Filter.eventuallyEq_of_mem self_mem_nhdsWithin h) (h x hx) i
    have e1 : Set.EqOn (iteratedFDerivWithin ℝ i f Ω) (iteratedFDeriv ℝ i f) Ω :=
      iteratedFDerivWithin_of_isOpen (s := Ω) (f := f) i hΩ
    have e2 : Set.EqOn (iteratedFDerivWithin ℝ i g Ω) (iteratedFDeriv ℝ i g) Ω :=
      iteratedFDerivWithin_of_isOpen (s := Ω) (f := g) i hΩ
    rw [← e1 hx, h1, e2 hx]
  refine le_antisymm
    (iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_)
    (iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_)
  · rw [key x hx, key y hy]; exact le_gSN i α hx hy hxy
  · rw [← key x hx, ← key y hy]; exact le_gSN i α hx hy hxy

@[simp] lemma gDN_zero_fun (i : ℕ) (Ω : Set Y) : gDN i (0 : Y → A) Ω = 0 := by
  refine le_antisymm ?_ bot_le
  refine iSup₂_le fun x _ => ?_
  simp

@[simp] lemma gSN_zero_fun (i : ℕ) (α : ℝ) (Ω : Set Y) : gSN i α (0 : Y → A) Ω = 0 := by
  refine le_antisymm ?_ bot_le
  refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun _ => ?_
  simp

/-- On an open set the global-derivative norms agree with `iDN`. -/
lemma gDN_eq_iDN {Ω : Set Y} (hΩ : IsOpen Ω) (i : ℕ) (f : Y → A) :
    gDN i f Ω = iDN i f Ω := by
  have e : Set.EqOn (iteratedFDerivWithin ℝ i f Ω) (iteratedFDeriv ℝ i f) Ω :=
    iteratedFDerivWithin_of_isOpen (s := Ω) (f := f) i hΩ
  refine le_antisymm (iSup₂_le fun x hx => ?_) (iSup₂_le fun x hx => ?_)
  · rw [← e hx]; exact le_iDN i hx
  · rw [e hx]; exact le_gDN i hx

/-- On an open set the global-derivative seminorms agree with `hSN`. -/
lemma gSN_eq_hSN {Ω : Set Y} (hΩ : IsOpen Ω) (i : ℕ) (α : ℝ) (f : Y → A) :
    gSN i α f Ω = hSN i α f Ω := by
  have e : Set.EqOn (iteratedFDerivWithin ℝ i f Ω) (iteratedFDeriv ℝ i f) Ω :=
    iteratedFDerivWithin_of_isOpen (s := Ω) (f := f) i hΩ
  refine le_antisymm
    (iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_)
    (iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_)
  · rw [← e hx, ← e hy]; exact le_hSN i α hx hy hxy
  · rw [e hx, e hy]; exact le_gSN i α hx hy hxy

end Work.NN.Final
