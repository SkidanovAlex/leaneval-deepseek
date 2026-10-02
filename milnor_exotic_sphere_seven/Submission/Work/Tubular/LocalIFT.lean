import Submission.Work.Tubular.Local

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The local inverse theorem on an open set

`Work.Tubular.Local` proves the inverse function theorem in the set-theoretic form used by the
construction, for a *globally* `C^∞` map.  Here `f` is only assumed `C^∞` on an open set `W₀`
(which is what the tubular neighbourhood theorem actually has: the chart representative is `C^∞` on
the chart's target, not on all of `ℝ^N`), and the conclusion records additionally that the local
inverse maps the image back into `W` (which is what makes the local tube charts patch together).

* `Work.Tubular.exists_localInverse_of_contDiffOn` — the theorem;
* `Work.Tubular.isUnit_of_bijective`, `Work.Tubular.bijective_of_isUnit` — the two directions of the
  equivalence between invertibility of an endomorphism of a finite-dimensional space and its
  bijectivity, in the form needed to produce the local inverse theorem's hypothesis from an *open*
  condition on the derivative.
-/

open scoped Manifold ContDiff Topology

namespace Work.Tubular

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The inverse function theorem, on an open set.** Let `f : E → F` be `C^∞` on an open set
`W₀ ∋ a` containing `a`, let `Df(a)` be invertible, and suppose that `Df` is invertible at every
point of `W₀`.  Then `f` is a local diffeomorphism at `a`: there are open `W ∋ a`, `W ⊆ W₀`, and
`U = f '' W`, and a `C^∞` inverse `g : F → E` with `g '' U ⊆ W`. -/
theorem exists_localInverse_of_contDiffOn (f : E → F) (φ : E ≃L[ℝ] F) {W₀ : Set E}
    (hW₀ : IsOpen W₀) {a : E} (ha : a ∈ W₀) (hf : ContDiffOn ℝ ∞ f W₀)
    (hφ : HasFDerivAt f (φ : E →L[ℝ] F) a)
    (hInv : ∀ x ∈ W₀, ∃ ψ : E ≃L[ℝ] F, HasFDerivAt f (ψ : E →L[ℝ] F) x) :
    ∃ (W : Set E) (U : Set F) (g : F → E), IsOpen W ∧ a ∈ W ∧ W ⊆ W₀ ∧ IsOpen U ∧
      f '' W = U ∧ Set.InjOn f W ∧ (∀ y ∈ U, g y ∈ W) ∧ (∀ y ∈ U, f (g y) = y) ∧
      (∀ x ∈ W, g (f x) = x) ∧ ContinuousOn g U ∧ ContDiffOn ℝ ∞ g U := by
  have hstrict : HasStrictFDerivAt f (φ : E →L[ℝ] F) a :=
    (hf.contDiffAt (hW₀.mem_nhds ha)).hasStrictFDerivAt' hφ (by simp)
  set Φ : OpenPartialHomeomorph E F := hstrict.toOpenPartialHomeomorph f with hΦ
  have haΦ : a ∈ Φ.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hΦcoe : ∀ x ∈ Φ.source, (Φ x : F) = f x := fun x _ => rfl
  refine ⟨W₀ ∩ Φ.source, Φ '' (W₀ ∩ Φ.source), Φ.symm, hW₀.inter Φ.open_source,
    ⟨ha, haΦ⟩, Set.inter_subset_left, Φ.isOpen_image_of_subset_source (hW₀.inter Φ.open_source)
      Set.inter_subset_right, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Set.image_congr (fun x hx => hΦcoe x hx.2)]
  · intro x hx y hy h
    exact Φ.injOn hx.2 hy.2 h
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Φ.left_inv hx.2]
    exact hx
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hmem : Φ.symm (Φ x) ∈ Φ.source := by rw [Φ.left_inv hx.2]; exact hx.2
    rw [← hΦcoe (Φ.symm (Φ x)) hmem]
    exact Φ.right_inv (Φ.map_source hx.2)
  · intro x hx
    exact Φ.left_inv hx.2
  · exact Φ.continuousOn_symm.mono (by rintro y ⟨x, hx, rfl⟩; exact Φ.map_source hx.2)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxS : x ∈ Φ.source := hx.2
    obtain ⟨ψ, hψ⟩ := hInv x hx.1
    have heq : (fun z => (Φ z : F)) =ᶠ[𝓝 x] f :=
      Filter.eventuallyEq_of_mem (Φ.open_source.mem_nhds hxS) (fun z hz => hΦcoe z hz)
    have hψ' : HasFDerivAt (Φ : E → F) (ψ : E →L[ℝ] F) (Φ.symm (Φ x)) := by
      rw [Φ.left_inv hxS]
      exact hψ.congr_of_eventuallyEq heq
    have hfc : ContDiffAt ℝ ∞ (Φ : E → F) (Φ.symm (Φ x)) := by
      rw [Φ.left_inv hxS]
      exact (hf.contDiffAt (hW₀.mem_nhds hx.1)).congr_of_eventuallyEq heq
    exact (Φ.contDiffAt_symm (Φ.map_source hxS) hψ' hfc).contDiffWithinAt

end

end Work.Tubular
