import Submission.Work.BoxShrink.PinchOff.Basic

/-!
# The sharpening of the residual: the loop form

The residual `Key` of the pinch (`Basic.lean`) is a statement about the *dimension* of a `ℚ`-span.
That is the right form for the bookkeeping, but it is not the form in which a geometric argument
(an isotopy, a flow, a routing of a path in the parameter plane) produces its conclusion: those
produce, for a *given* loop, another loop.  This module proves that the residual is *equivalent* to
its loop form

> `LoopForm`: if the box region realises a nonzero class and, moreover, every nonzero class realised
> in the box region has a **class independent of it** also realised in the box region ("the box
> region is full rank"), then some loop of one of the two half-regions has a nonzero class;

and to the span form of the key case:

> `keyCase_iff_noSpanJump`: the only way the residual can fail is a single configuration in which the
> box region spans the whole of `H₁(F;ℚ) = ℚ²` while the two half-regions together span nothing.

The point of the loop form is that it *localises* the residual to a single loop: instead of
producing a map of spans, an argument may start from the two loops that realise the two independent
classes and produce a third loop (in a half-region) with a nonzero class.  Equivalently, the
contrapositive of `Key` is: *if the union of the two half-regions contains no essential loop, then
the box region is not full rank*, and in that form the statement can be refuted or proved
configuration by configuration.

## Contents

* `zzLine`, `zzClass`, `zzIndep` -- the loop/class vocabulary of `ℚ² = H₁(F;ℚ)`;
* `exists_loop_winding_ne_zero_iff` -- a region realises a nonzero winding vector iff some loop of it
  has nonzero winding;
* `fullRankLoop_iff_finrank_two` -- **the linear algebra of the reduction**: the pair of conditions
  "some nonzero class is realised" and "every nonzero realised class has an independent partner" is
  exactly `finrank = 2`;
* `key_iff_loopForm` -- the residual in loop form;
* `keyCase_iff_noSpanJump` -- the residual in the "no `⊤ → ⊥` jump" form, in span terms.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- The `ℚ`-dimension of `ℚ² = H₁(F;ℚ)` is `2`. -/
theorem finrank_rat_sq : Module.finrank ℚ (ℚ × ℚ) = 2 := by
  rw [Module.finrank_prod, Module.finrank_self]

/-! ## The class vocabulary -/

/-- The image of a winding vector in `ℚ² = H₁(F;ℚ)`. -/
def zzCast (v : ℤ × ℤ) : ℚ × ℚ := ((v.1 : ℚ), (v.2 : ℚ))

/-- The `ℚ`-line spanned by a winding vector. -/
def zzLine (v : ℤ × ℤ) : Submodule ℚ (ℚ × ℚ) := ℚ ∙ zzCast v

/-- The class of a loop of the carrier, as an element of `ℚ² = H₁(F;ℚ)`. -/
def zzClass (γ : Work.CoreTopology.ClosedCurve P) : ℚ × ℚ :=
  zzCast (Work.SurgeryInvariance.windingOf P γ)

/-- `w` is not a multiple of `v` (as classes in `ℚ²`). -/
def zzIndep (w v : ℤ × ℤ) : Prop := zzCast w ∉ zzLine v

/-- The class of a loop of a region lies in the winding span of that region. -/
theorem zzClass_mem_windingSpan {X : Set R3} {γ : Work.CoreTopology.ClosedCurve P}
    (hγ : ∀ t : ℝ, γ t ∈ X) : zzClass γ ∈ Work.SurgeryInvariance.WindingSpan P X :=
  Submodule.subset_span ⟨γ, hγ, rfl⟩

/-- **A region realises a nonzero winding vector exactly when one of its loops has a nonzero
winding vector.** -/
theorem exists_loop_winding_ne_zero_iff {X : Set R3} :
    (∃ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ X) ∧
        Work.SurgeryInvariance.windingOf P γ ≠ 0) ↔
      Work.SurgeryInvariance.WindingSpan P X ≠ ⊥ := by
  constructor
  · rintro ⟨γ, hγ, hw⟩ hbot
    have : zzCast (Work.SurgeryInvariance.windingOf P γ) ∈
        (⊥ : Submodule ℚ (ℚ × ℚ)) := by
      rw [← hbot]
      exact zzClass_mem_windingSpan hγ
    rw [Submodule.mem_bot] at this
    exact hw (Work.SurgeryInvariance.intPair_cast_eq_zero_iff _ |>.mp this)
  · intro hne
    rw [Work.SurgeryInvariance.windingSpan_ne_bot_iff] at hne
    obtain ⟨γ, hess, hγ⟩ := hne
    exact ⟨γ, hγ, (Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P γ).mp hess⟩

/-! ## The linear algebra: full rank, in loop terms -/

/-- **The box region is full rank, in loop terms.**  It realises a nonzero class, and every nonzero
class it realises has an independent partner realised in it. -/
def FullRankLoop (X : Set R3) : Prop :=
  (∃ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ X) ∧
      Work.SurgeryInvariance.windingOf P γ ≠ 0) ∧
    (∀ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ X) →
      Work.SurgeryInvariance.windingOf P γ ≠ 0 →
      ∃ γ'' : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ'' t ∈ X) ∧
        zzIndep (Work.SurgeryInvariance.windingOf P γ'')
          (Work.SurgeryInvariance.windingOf P γ))

/-- **The linear algebra of the loop form.**  `FullRankLoop X` is exactly
`finrank (WindingSpan P X) = 2`, i.e. `WindingSpan P X = ⊤`.

The proof of the nontrivial direction is the observation that the span of a single nonzero vector of
`ℚ²` is a *proper* subspace of the winding span (it does not contain the class of the independent
partner), so `Submodule.finrank_lt_finrank_of_lt` bounds the winding span below by `1 + 1 = 2`. -/
theorem fullRankLoop_iff_finrank_two {X : Set R3} :
    FullRankLoop (P := P) X ↔
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P X) = 2 := by
  constructor
  · rintro ⟨⟨γ, hγ, hw⟩, hindep⟩
    obtain ⟨γ'', hγ'', hind⟩ := hindep γ hγ hw
    set v : ℚ × ℚ := zzCast (Work.SurgeryInvariance.windingOf P γ) with hv
    set w : ℚ × ℚ := zzCast (Work.SurgeryInvariance.windingOf P γ'') with hw'
    have hv0 : v ≠ 0 := by
      intro h
      exact hw (Work.SurgeryInvariance.intPair_cast_eq_zero_iff _ |>.mp h)
    have hvmem : v ∈ Work.SurgeryInvariance.WindingSpan P X := zzClass_mem_windingSpan hγ
    have hwmem : w ∈ Work.SurgeryInvariance.WindingSpan P X := zzClass_mem_windingSpan hγ''
    have hle : (ℚ ∙ v) ≤ Work.SurgeryInvariance.WindingSpan P X :=
      Submodule.span_le.mpr (by rintro x rfl; exact hvmem)
    have hne : (ℚ ∙ v) ≠ Work.SurgeryInvariance.WindingSpan P X := by
      intro h
      have hwm : w ∈ (ℚ ∙ v) := by rw [h]; exact hwmem
      have hmem : w ∈ zzLine (Work.SurgeryInvariance.windingOf P γ) := by
        simpa only [zzLine] using hwm
      exact hind hmem
    have hlt : (ℚ ∙ v) < Work.SurgeryInvariance.WindingSpan P X := lt_of_le_of_ne hle hne
    have h1 : Module.finrank ℚ ↥(ℚ ∙ v) = 1 := finrank_span_singleton hv0
    have h2 := Submodule.finrank_lt_finrank_of_lt hlt
    rw [h1] at h2
    have h3 := Work.BoxShrink.Pinch.finrank_windingSpan_le_two P X
    omega
  · intro hfin
    have hwne : Work.SurgeryInvariance.WindingSpan P X ≠ ⊥ := by
      intro h
      rw [h, Submodule.finrank_eq_zero.mpr rfl] at hfin
      omega
    refine ⟨(exists_loop_winding_ne_zero_iff (P := P)).mpr hwne, ?_⟩
    intro γ hγ hw
    by_contra hno
    -- if no independent partner exists, every realised class is a multiple of `v`, hence the span
    -- is contained in the line `ℚ v`, contradicting `finrank = 2`
    have hno' : ∀ δ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, δ t ∈ X) →
        zzCast (Work.SurgeryInvariance.windingOf P δ) ∈ zzLine
          (Work.SurgeryInvariance.windingOf P γ) := by
      intro δ hδ
      by_contra hcon
      exact hno ⟨δ, hδ, hcon⟩
    set v : ℚ × ℚ := zzCast (Work.SurgeryInvariance.windingOf P γ) with hv
    have hv0 : v ≠ 0 := fun h =>
      hw (Work.SurgeryInvariance.intPair_cast_eq_zero_iff _ |>.mp h)
    have hsub : Work.SurgeryInvariance.WindingSpan P X ≤ ℚ ∙ v := by
      rw [Work.SurgeryInvariance.WindingSpan, Submodule.span_le]
      rintro u ⟨δ, hδ, rfl⟩
      have h1 := hno' δ hδ
      rw [zzLine] at h1
      rwa [← hv] at h1
    have hle2 := Submodule.finrank_mono hsub
    rw [hfin, finrank_span_singleton hv0] at hle2
    omega

/-! ## The loop form of the residual -/

/-- **The residual in loop form.**  If the box region is full rank *read off its loops*
(`FullRankLoop`), then one of the two half-regions contains a loop with nonzero winding vector.

By `fullRankLoop_iff_finrank_two` this is the same hypothesis as the key case's
`finrank (WindingSpan Ω) = 2`, and by `exists_loop_winding_ne_zero_iff` the same conclusion as
`WindingSpan (Halves) ≠ ⊥`; the point of stating it in loop form is that an argument may now work
with the two loops realising the two independent classes. -/
def LoopForm : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    FullRankLoop (P := surface ψ) (Omega ψ s c σ) →
    ∃ γ' : Work.CoreTopology.ClosedCurve (surface ψ),
      (∀ t : ℝ, γ' t ∈ Halves ψ s c σ u) ∧
        Work.SurgeryInvariance.windingOf (surface ψ) γ' ≠ 0

/-- **`Key` is its loop form.** -/
theorem key_iff_loopForm : Key ↔ LoopForm := by
  constructor
  · intro h ψ s c σ u hS hZ hfull
    have hfin : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ)
        (Omega ψ s c σ)) = 2 :=
      (fullRankLoop_iff_finrank_two (P := surface ψ)).mp hfull
    have hstep := h ψ s c σ u hS hZ
    rw [hfin] at hstep
    have hne : Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) ≠ ⊥ := by
      intro hbot
      rw [hbot, Submodule.finrank_eq_zero.mpr rfl] at hstep
      omega
    exact (exists_loop_winding_ne_zero_iff (P := surface ψ)).mpr hne
  · intro h ψ s c σ u hS hZ
    have hbox := Work.BoxShrink.Pinch.finrank_windingSpan_le_two (surface ψ) (Omega ψ s c σ)
    rcases lt_or_ge (Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ)
        (Omega ψ s c σ))) 2 with hlt | hge
    · omega
    · have hfin : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ)
          (Omega ψ s c σ)) = 2 := le_antisymm hbox hge
      obtain ⟨γ', hγ', hw'⟩ := h ψ s c σ u hS hZ
        ((fullRankLoop_iff_finrank_two (P := surface ψ)).mpr hfin)
      have hne : Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) ≠ ⊥ :=
        (exists_loop_winding_ne_zero_iff (P := surface ψ)).mp ⟨γ', hγ', hw'⟩
      have hpos : 1 ≤ Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ)
          (Halves ψ s c σ u)) :=
        Nat.one_le_iff_ne_zero.mpr fun h0 =>
          hne (Submodule.finrank_eq_zero.mp h0)
      omega

/-! ## The residual in the "no `⊤ → ⊥` jump" form -/

/-- **The residual, in the span form of its key case**: the only failing configuration would have a
box region spanning the whole of `ℚ²` and two half-regions spanning nothing. -/
theorem keyCase_iff_noSpanJump :
    KeyCase ↔
      ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
        ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) →
        ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
        ¬ (Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) = ⊤ ∧
          Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) = ⊥) := by
  constructor
  · intro h ψ s c σ u hS hZ hbad
    obtain ⟨htop, hbot⟩ := hbad
    have hfin : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ)
        (Omega ψ s c σ)) = 2 := by
      rw [htop, finrank_top, Module.finrank_prod, Module.finrank_self]
    exact h ψ s c σ u hS hZ hfin hbot
  · intro h ψ s c σ u hS hZ hfin hbot
    have htop : Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [hfin]
      exact finrank_rat_sq.symm
    exact h ψ s c σ u hS hZ ⟨htop, hbot⟩

end

end Work.BoxShrink.PinchOff
