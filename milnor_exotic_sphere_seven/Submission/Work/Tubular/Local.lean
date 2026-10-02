import Submission.Work.Tubular.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The inverse function theorem step of the tubular neighbourhood theorem

The tubular map `(y,u) ↦ f y + A u` of a chart (`f` the chart representative of the embedding, `A` a
parametrisation of the normal directions) is, near a point `y₀` at which the derivative
`y ↦ Df(y₀) y + A u` is a linear isomorphism, a **local diffeomorphism**.  This file proves the
inverse function theorem in the set-theoretic form used by the construction
(`Work.Tubular.exists_localInverse_of_hasFDerivAt`):

if `f : E → F` is `C^∞`, `Df(a)` is invertible, and `Df` is invertible at every point of some
neighbourhood of `a`, then there are open sets `W ∋ a`, `U = f '' W` and a `C^∞` map `g : U → W`
with `f ∘ g = id` on `U` and `g ∘ f = id` on `W`.

Everything is obtained from the inverse function theorem in Mathlib
(`HasStrictFDerivAt.toOpenPartialHomeomorph` for the topological local inverse and
`OpenPartialHomeomorph.contDiffAt_symm` for its smoothness), so this file contains no new analysis:
it packages the IFT in the form the tubular neighbourhood proof consumes.

The hypothesis "`Df` is invertible near `a`" is automatic for `C^1` maps at a point with invertible
derivative (the set of invertible operators is open), and it is what makes the *inverse* smooth; the
topological part does not need it.
-/

open scoped Manifold ContDiff Topology

namespace Work.Tubular

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The inverse function theorem, in the form used by the tubular neighbourhood theorem.**

Let `f : E → F` be `C^∞`, let `φ` be a continuous linear equivalence that is the derivative of `f`
at `a`, and suppose that the derivative of `f` is invertible at every point of some neighbourhood of
`a` (this holds automatically when `f` is `C^1`, since the invertible operators are open).  Then `f`
is a local diffeomorphism at `a`: there are open `W ∋ a` and `U = f '' W`, and a `C^∞` inverse
`g : F → E` on them. -/
theorem exists_localInverse_of_hasFDerivAt (f : E → F) {a : E} (φ : E ≃L[ℝ] F)
    (hf : ContDiff ℝ ∞ f) (hφ : HasFDerivAt f (φ : E →L[ℝ] F) a)
    (hInv : ∃ W₀ : Set E, IsOpen W₀ ∧ a ∈ W₀ ∧
      ∀ x ∈ W₀, ∃ ψ : E ≃L[ℝ] F, HasFDerivAt f (ψ : E →L[ℝ] F) x) :
    ∃ (W : Set E) (U : Set F) (g : F → E), IsOpen W ∧ a ∈ W ∧ IsOpen U ∧ f '' W = U ∧
      Set.InjOn f W ∧ (∀ y ∈ U, f (g y) = y) ∧ (∀ x ∈ W, g (f x) = x) ∧
      ContinuousOn g U ∧ ContDiffOn ℝ ∞ g U := by
  have hstrict : HasStrictFDerivAt f (φ : E →L[ℝ] F) a :=
    hf.contDiffAt.hasStrictFDerivAt' hφ (by simp)
  obtain ⟨W₀, hW₀open, haW₀, hinv⟩ := hInv
  set Φ : OpenPartialHomeomorph E F := hstrict.toOpenPartialHomeomorph f with hΦ
  have haΦ : a ∈ Φ.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hΦcoe : ∀ x ∈ Φ.source, (Φ x : F) = f x := fun x _ => rfl
  refine ⟨W₀ ∩ Φ.source, Φ '' (W₀ ∩ Φ.source), Φ.symm, hW₀open.inter Φ.open_source,
    ⟨haW₀, haΦ⟩, Φ.isOpen_image_of_subset_source (hW₀open.inter Φ.open_source)
      Set.inter_subset_right, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `f '' W = U`
    rw [Set.image_congr (fun x hx => hΦcoe x hx.2)]
  · -- injectivity
    intro x hx y hy h
    exact Φ.injOn hx.2 hy.2 h
  · -- right inverse
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hmem : Φ.symm (Φ x) ∈ Φ.source := by rw [Φ.left_inv hx.2]; exact hx.2
    rw [← hΦcoe (Φ.symm (Φ x)) hmem]
    exact Φ.right_inv (Φ.map_source hx.2)
  · -- left inverse
    intro x hx
    exact Φ.left_inv hx.2
  · -- continuity
    exact Φ.continuousOn_symm.mono (by rintro y ⟨x, hx, rfl⟩; exact Φ.map_source hx.2)
  · -- smoothness
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxS : x ∈ Φ.source := hx.2
    obtain ⟨ψ, hψ⟩ := hinv x hx.1
    have heq : (fun z => (Φ z : F)) =ᶠ[𝓝 x] f :=
      Filter.eventuallyEq_of_mem (Φ.open_source.mem_nhds hxS) (fun z hz => hΦcoe z hz)
    have hψ' : HasFDerivAt (Φ : E → F) (ψ : E →L[ℝ] F) (Φ.symm (Φ x)) := by
      rw [Φ.left_inv hxS]
      exact hψ.congr_of_eventuallyEq heq
    have hfc : ContDiffAt ℝ ∞ (Φ : E → F) (Φ.symm (Φ x)) := by
      rw [Φ.left_inv hxS]
      exact hf.contDiffAt.congr_of_eventuallyEq heq
    exact (Φ.contDiffAt_symm (Φ.map_source hxS) hψ' hfc).contDiffWithinAt

end

end Work.Tubular
