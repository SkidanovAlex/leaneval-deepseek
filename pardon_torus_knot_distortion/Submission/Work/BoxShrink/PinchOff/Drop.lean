import Submission.Work.BoxShrink.PinchOff.KeyTameClosed
import Submission.Work.BoxShrink.PinchOff.PerpBox
import Submission.Work.SurgeryInvariance.Span.union_eq_sup

/-!
# The residual of the pinch: the "both halves drop" case

The dimension bound of Pardon's Lemma 2.3 (`KeyTameClosed`, `KeyTameClosed.lean`) is

`finrank W(Ω) ≤ finrank W(Ω⁺ ∪ Ω⁻) + 1`

at a transverse, closed-tame configuration whose box sphere (`hS`) and slice (`hZ`) carry no
essential loop.  Since `W(Ω)` is a subspace of `ℚ²` its rank is at most `2`, and since a nonzero
subspace has rank at least `1`, the bound is **automatic** unless `W(Ω⁺ ∪ Ω⁻) = ⊥`: in that case
it says exactly `finrank W(Ω) ≤ 1`, i.e. `W(Ω)` is at most one-dimensional.

This module isolates that case, which is the *whole* remaining content of the residual:

* `DropCase` — the obligation: at a transverse closed-tame configuration with `hS` and `hZ`, if
  both half-regions are inessential then the box region is at most one-dimensional;
* `keyTameClosed_of_dropCase` / `dropCase_of_keyTameClosed` / `keyTameClosed_iff_dropCase` — the
  dimension bound *is* that obligation and nothing else;
* the easy inhabitants of `DropCase`: when the slice is empty (then `Ω = Ω⁺ ∪ Ω⁻`, so the
  hypothesis `W(Ω⁺ ∪ Ω⁻) = ⊥` is already the conclusion), and when the box region itself is
  inessential.

The remaining mathematics, in the words of the analysis recorded in `README.md` §32, is the
"both halves drop" case: `Ω = Ω⁺ ⊔ Σ ⊔ Ω⁻` with `Ω⁺`, `Ω⁻` planar (each inessential), `Σ` a union
of arcs whose ends lie on the box sphere (inessential by `hZ`), and `Ω` essential — the essential
class is then created by the *gluing* of the two planar pieces along the arcs, and (by the
one-parameter analysis of §32) it must be "born" at the level of one of the box's faces
perpendicular to the cutting plane.  No configuration of that shape is known.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **The "both halves drop" case of the residual.**  At a transverse, closed-tame configuration
whose box sphere and slice carry no essential loop, if the two half-regions together carry no
essential loop, then the box region is at most one-dimensional.

This is exactly the content of Pardon's dimension bound beyond the two facts that `W(Ω) ⊆ ℚ²` and
that a nonzero span has rank at least `1`. -/
def DropCase : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → TameClosedSlice ψ s c σ u →
    ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) = ⊥ →
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)) ≤ 1

/-- The box region of the surface lies in the whole ambient `ℚ² = H₁(T²; ℚ)`, so its winding span
has rank at most `2`. -/
theorem finrank_windingSpan_le_two (ψ : Submission.Diffeo) (X : Set R3) :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) X) ≤ 2 := by
  have h := Submodule.finrank_le
    (R := ℚ) (M := ℚ × ℚ) (Work.SurgeryInvariance.WindingSpan (surface ψ) X)
  rwa [Work.SurgeryInvariance.finrank_pair] at h

/-- **The residual is the "both halves drop" case**: the dimension bound for the pinch follows from
`DropCase`.  If the two half-regions span something, the bound is automatic; otherwise it is
exactly `DropCase`. -/
theorem keyTameClosed_of_dropCase (h : DropCase) : KeyTameClosed := by
  intro ψ s c σ u hT hTa hS hZ
  by_cases hbot : Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) = ⊥
  · have h1 := h ψ s c σ u hT hTa hS hZ hbot
    have h0 : Module.finrank ℚ
        ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)) = 0 := by
      rw [hbot, finrank_bot]
    rw [h0]
    omega
  · have h1 : 1 ≤ Module.finrank ℚ
        ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)) := by
      have hpos : 0 < Module.finrank ℚ
          ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)) :=
        (Module.finrank_pos_iff_of_free ℚ _).mpr (Submodule.nontrivial_iff_ne_bot.mpr hbot)
      omega
    have h2 := finrank_windingSpan_le_two ψ (Omega ψ s c σ)
    omega

/-- **The converse**: the dimension bound gives `DropCase` (apply it and read off the case in which
the halves span nothing). -/
theorem dropCase_of_keyTameClosed (h : KeyTameClosed) : DropCase := by
  intro ψ s c σ u hT hTa hS hZ hbot
  have hb := h ψ s c σ u hT hTa hS hZ
  have h0 : Module.finrank ℚ
      ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)) = 0 := by
    rw [hbot, finrank_bot]
  rw [h0] at hb
  omega

/-- **The residual is *exactly* the "both halves drop" case.** -/
theorem keyTameClosed_iff_dropCase : KeyTameClosed ↔ DropCase :=
  ⟨dropCase_of_keyTameClosed, keyTameClosed_of_dropCase⟩

/-- **The trivial inhabitant of `DropCase`**: if the box region is already inessential, the
conclusion `finrank W(Ω) ≤ 1` is immediate. -/
theorem dropCase_of_omega_eq_bot
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → TameClosedSlice ψ s c σ u →
      ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) →
      ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) = ⊥) :
    DropCase := by
  intro ψ s c σ u hT hTa hS hZ _
  have h0 : Module.finrank ℚ
      ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)) = 0 := by
    rw [h ψ s c σ u hT hTa hS hZ, finrank_bot]
  omega

/-- **`DropCase` when the slice is empty**: then `Ω = Ω⁺ ∪ Ω⁻` (`Omega_sdiff_Sigma`), so the
hypothesis `W(Ω⁺ ∪ Ω⁻) = ⊥` is already the conclusion. -/
theorem dropCase_of_sigma_eq_empty
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Sigma ψ s c σ u = ∅) :
    DropCase := by
  intro ψ s c σ u _ _ _ _ hbot
  have hom : Omega ψ s c σ = Halves ψ s c σ u := by
    have h1 := Omega_sdiff_Sigma (ψ := ψ) (s := s) (c := c) (σ := σ) (u := u)
    rw [h ψ s c σ u, sdiff_empty] at h1
    exact h1
  rw [hom]
  rw [hbot, finrank_bot]
  omega

/-- **`DropCase` when the slice is a union of circles alone**: the parent chapter's circles-only
theorem (`windingSpan_omega_eq_halves_of_trace_circles_holds`) gives `W(Ω) = W(Ω⁺ ∪ Ω⁻)`, so the
hypothesis `W(Ω⁺ ∪ Ω⁻) = ⊥` forces `W(Ω) = ⊥`. -/
theorem dropCase_of_sliceCirclesOnly
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      SliceCirclesOnly ψ s c σ u) :
    DropCase := by
  intro ψ s c σ u _ _ _ hZ hbot
  have heq := windingSpan_omega_eq_halves_of_trace_circles_holds (ψ := ψ) (s := s) (c := c)
    (σ := σ) (u := u) hZ (h ψ s c σ u)
  rw [hbot] at heq
  have h0 : Module.finrank ℚ
      ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)) = 0 := by
    rw [heq, finrank_bot]
  rw [h0]
  omega

/-! ## The slices at *every* level are inessential in the "both halves drop" case

The whole point of the "both halves drop" case is that the essential class of the box region has to
be created by the gluing of the two planar half-regions along the arcs of the slice.  The first
structural consequence is that *no* horizontal slice of the box can carry an essential loop: a slice
at a level strictly above the cutting plane lies in the upper half-region, and one at a level
strictly below lies in the lower half-region, so an essential loop in it would already be an
essential loop of `Ω⁺ ∪ Ω⁻`.
-/

/-- **A slice strictly above the cutting plane lies in the upper half-region.** -/
theorem Sigma_subset_halfUp_of_lt {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u u' : ℝ} (h : u < u') :
    Sigma ψ s c σ u' ⊆ HalfUp ψ s c σ u := by
  intro y hy
  rw [Sigma, Work.BoxShrink.Core.mem_sliceRegion] at hy
  rw [HalfUp, Work.BoxShrink.Core.mem_upperRegion]
  exact ⟨hy.1, hy.2.1, by rw [hy.2.2]; linarith⟩

/-- **A slice strictly below the cutting plane lies in the lower half-region.** -/
theorem Sigma_subset_halfDown_of_gt {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u u' : ℝ} (h : u' < u) :
    Sigma ψ s c σ u' ⊆ HalfDown ψ s c σ u := by
  intro y hy
  rw [Sigma, Work.BoxShrink.Core.mem_sliceRegion] at hy
  rw [HalfDown, Work.BoxShrink.Core.mem_lowerRegion]
  exact ⟨hy.1, hy.2.1, by rw [hy.2.2]; linarith⟩

/-- **An essential loop in a slice above the cutting plane is an essential loop of the upper
half-region.** -/
theorem windingSpan_halfUp_ne_bot_of_slice_essential {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u u' : ℝ} (h : u < u')
    (hess : (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u')) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (HalfUp ψ s c σ u) ≠ ⊥ := by
  intro hbot
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff] at hbot
  exact hbot ((surface ψ).containsEssentialLoop_mono (Sigma_subset_halfUp_of_lt h) hess)

/-- **An essential loop in a slice below the cutting plane is an essential loop of the lower
half-region.** -/
theorem windingSpan_halfDown_ne_bot_of_slice_essential {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u u' : ℝ} (h : u' < u)
    (hess : (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u')) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (HalfDown ψ s c σ u) ≠ ⊥ := by
  intro hbot
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff] at hbot
  exact hbot ((surface ψ).containsEssentialLoop_mono (Sigma_subset_halfDown_of_gt h) hess)

/-- **In the "both halves drop" case, the slice at *every* level is inessential.**  This is the
first structural consequence of the case, and it is what makes the remaining obligation a
statement about the *level sets* of the cutting-plane coordinate: an essential class can only be
created by the gluing along the arcs, never by a horizontal slice. -/
theorem slices_inessential_of_halves_bot {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hbot : Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) = ⊥)
    (hZ : ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u)) (u' : ℝ) :
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u') := by
  rcases lt_trichotomy u' u with h | h | h
  · intro hess
    have h1 := windingSpan_halfDown_ne_bot_of_slice_essential h hess
    have h2 : Work.SurgeryInvariance.WindingSpan (surface ψ) (HalfDown ψ s c σ u)
        ≤ Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) :=
      Work.SurgeryInvariance.WindingSpan_mono _ Set.subset_union_right
    rw [hbot] at h2
    exact h1 (le_bot_iff.mp h2)
  · subst h; exact hZ
  · intro hess
    have h1 := windingSpan_halfUp_ne_bot_of_slice_essential h hess
    have h2 : Work.SurgeryInvariance.WindingSpan (surface ψ) (HalfUp ψ s c σ u)
        ≤ Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) :=
      Work.SurgeryInvariance.WindingSpan_mono _ Set.subset_union_left
    rw [hbot] at h2
    exact h1 (le_bot_iff.mp h2)

end

end Work.BoxShrink.PinchOff
