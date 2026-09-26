import Mathlib
import Submission.Work.Smooth.JordanSeparation.loops_nullhomotopic_of_isOpen_of_isPreconnected_compl
import Submission.Work.Smooth.JordanSeparation.onePoint_locallyPathConnected

/-!
# Complementary domains of continua in the Riemann sphere are simply connected

If `D ⊆ S²` is open, non-empty and preconnected and its complement is preconnected, then `D` is
simply connected.  Equivalently: a domain `D` in `S²` is simply connected as soon as `S² ∖ D` is
connected, which is the classical statement that **every complementary domain of a continuum in
`S²` is simply connected**.

The plane analogue is false for unbounded domains (`K = {0}`: the component of `1` in `Kᶜ ⊆ ℂ` is
`ℂ ∖ {0}` with `π₁ = ℤ`), while on the sphere that component is `S² ∖ {0} ≅ ℂ`, which is simply
connected; so the sphere formulation is the correct one.

## Proof

Everything of substance is in the sibling file
`Submission.Work.Smooth.JordanSeparation.loops_nullhomotopic_of_isOpen_of_isPreconnected_compl`,
which proves the loop-level form

`Work.Smooth.JordanSeparation.loops_nullhomotopic_of_isOpen_of_isPreconnected_compl`:
every loop in an open `D ⊆ S²` with preconnected complement is null-homotopic in `D`.

From it the statement follows formally: `D` is path connected because it is an open preconnected
subset of the locally path connected sphere `OnePoint ℂ`
(`Work.Smooth.JordanSeparation.onePoint_locallyPathConnected`), and path connectedness together with
the loop condition is exactly `SimplyConnectedSpace ↥D` by
`simply_connected_iff_loops_nullhomotopic`.

## History of this file

This module previously contained a self-contained reduction of the statement to a single
maximality-type statement (`NullHomotopicAvoiding γ K` for `K` closed preconnected, via a Zorn
argument on the family of preconnected sets containing `K`, avoiding `range γ` and still not
admitting a null-homotopy whose image avoids them, together with an explicit growth argument); the
argument reduced the whole crux to the single configuration "the maximal member `M` is open with
`frontier M ⊆ range γ`".  That configuration is exactly the classical 1-asphericity of the
complement of a complementary domain of a continuum, and it is now available in the workspace
through the lattice-walk proof of `loops_nullhomotopic_of_isOpen_of_isPreconnected_compl`, which is
what is used below.
-/

open Set

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **Complementary domains of continua in the Riemann sphere are simply connected.**

If `D ⊆ OnePoint ℂ` is a non-empty open preconnected set whose complement is preconnected, then `D`
is simply connected. -/
theorem isSimplyConnected_of_isPreconnected_compl {D : Set (OnePoint ℂ)} (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDp : IsPreconnected D) (hDc : IsPreconnected Dᶜ) :
    IsSimplyConnected D := by
  rw [IsSimplyConnected, simply_connected_iff_loops_nullhomotopic]
  constructor
  · -- `D` is path connected: it is open and preconnected, and the sphere is locally path connected.
    haveI : LocallyPathConnectedSpace (OnePoint ℂ) := onePoint_locallyPathConnected
    rw [← isPathConnected_iff_pathConnectedSpace]
    exact (hDo.isConnected_iff_isPathConnected).mp ⟨hDne, hDp⟩
  · -- every loop in `D` is null-homotopic, by the loop-level form of the theorem
    intro a γ
    exact loops_nullhomotopic_of_isOpen_of_isPreconnected_compl hDo hDc a.2 γ

end

end Work.Smooth.JordanSeparation
