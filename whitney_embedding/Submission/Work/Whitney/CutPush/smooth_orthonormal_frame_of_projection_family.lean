import Mathlib

/-!
# A smooth orthonormal frame field for a smooth family of orthogonal projections

`CutPush/NOTES_hasFingerData_S51.md` §4–§5.  This is brick 1 of the fibered route's assembly: the
smooth families `T t = range (PT t)`, `Ā t = ker (Φ t)` of the collar construction are given as
smooth families of *orthogonal projections*, whereas the whole family layer of brick 2
(`CutPush/frame_transfer_kernel.lean`, `CutPush/norm_gap_of_aligned_frames.lean`) consumes
orthonormal *frames* `c t`, `w t` of those planes.  This file supplies the frame field.

Statement (reviewed twice, both readers "looks correct as stated"):

    `∃ c : ℝ → Fin k → ℝ^m`, each `t ↦ c t i` smooth, each `c t` orthonormal, and
    `span (range (c t)) = range (P t)`.

Interface facts already on disk and consumed here:

* `exists_orthonormal_frame_of_projection` (below, proved): the **pointwise** statement — every
  orthogonal projection of rank `k` in `ℝ^m` has an orthonormal `k`-frame spanning its range.
  (Obtained from `Orthonormal.exists_orthonormalBasis_extension_of_card_eq` applied to the empty
  family in the submodule `range P`; the index type `Fin k` is the one the statement wants, so no
  reindexing is needed.)
* `exists_smooth_projection_range_family` / `exists_smooth_projection_ker_family`
  (`CutPush/smooth_range_projection_family.lean`, `CutPush/smooth_projection_kernel_family.lean`):
  the canonical smooth projections onto the range of a smooth family of injections and onto the
  kernel of a smooth family of surjections.

## Proof route for the main statement (bundle over the interval, no bundle theory)

1. **Column selection (open condition).**  At `t₀`, the columns `P t₀ e_i` (`i : Fin m`) span
   `range (P t₀)` (they are the images of a spanning set), so some `k`-subset `s` of them is a basis;
   the corresponding `k × k` minor of `t ↦ (P t e_i)_{i ∈ s}` is nonzero at `t₀`, hence on a
   neighbourhood `I (t₀)`.
2. **Local Gram–Schmidt.**  On `I (t₀)` the `s`-columns remain independent, and Gram–Schmidt
   (inductively: normalise, subtract the projections onto the previous vectors, normalise) is a
   composition of smooth operations with divisions by functions that do not vanish there, so it
   gives a smooth orthonormal frame of `range (P t)` on `I (t₀)`.
3. **Gluing.**  Over a compact parameter set (for the collar: `Set.Icc 0 1`) finitely many
   `I (t₀)` cover, and consecutive local frames are glued by Gram–Schmidt of
   `(1 - φ) • c₁ + φ • c₂`: on the overlap both frames span the same `k`-plane, so the transition
   matrix `T t` is orthogonal, and with `φ ≤ 1/2` the combined family is independent because
   `(1-φ) I + φ T` has quadratic form `(1-φ)‖x‖² + φ⟪x, T x⟫ ≥ (1 - 2φ)‖x‖² > 0`.
4. The statement over all of `ℝ` (as requested) needs step 3 only with a *locally finite* cover —
   e.g. run the compact argument on each `Set.Icc n (n+1)`, `n : ℤ` — and the frames can be kept
   fixed outside.  A variant with the parameters restricted to `Set.Icc 0 1` is what the collar
   consumes and is strictly easier (step 3 becomes finite by compactness alone).
-/

open scoped BigOperators

namespace Work.Whitney.CutPush

/-- **Pointwise: an orthogonal projection of rank `k` has an orthonormal `k`-frame for its range.**
No smoothness is involved. -/
theorem exists_orthonormal_frame_of_projection {m k : ℕ}
    (P : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hidem : P * P = P)
    (hsymm : ∀ x y : EuclideanSpace ℝ (Fin m), inner ℝ (P x) y = inner ℝ x (P y))
    (hrank : Module.finrank ℝ (LinearMap.range (P : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) = k) :
    ∃ c : Fin k → EuclideanSpace ℝ (Fin m),
      Orthonormal ℝ c ∧
      Submodule.span ℝ (Set.range c)
        = LinearMap.range (P : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
  classical
  set V : Submodule ℝ (EuclideanSpace ℝ (Fin m)) :=
    LinearMap.range (P : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) with hV
  have hcard : Module.finrank ℝ V = Fintype.card (Fin k) := by
    rw [Fintype.card_fin]; exact hrank
  have hvac : Orthonormal ℝ ((∅ : Set (Fin k)).domRestrict (fun _ : Fin k => (0 : V))) :=
    Orthonormal.of_isEmpty _
  obtain ⟨b, _⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (𝕜 := ℝ) (E := V) (ι := Fin k) (v := fun _ : Fin k => (0 : V)) (s := ∅) hcard hvac
  refine ⟨fun i => (b i : EuclideanSpace ℝ (Fin m)), ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro i j
    simpa using orthonormal_iff_ite.mp b.orthonormal i j
  · apply le_antisymm
    · intro x hx
      refine Submodule.span_le.mpr ?_ hx
      rintro y ⟨i, rfl⟩
      exact (b i).2
    · intro x hx
      have hrepr : x = ∑ i, (b.repr ⟨x, hx⟩) i • (b i : EuclideanSpace ℝ (Fin m)) := by
        have h := b.sum_repr (⟨x, hx⟩ : V)
        simpa using congrArg (fun w : V => (w : EuclideanSpace ℝ (Fin m))) h.symm
      rw [hrepr]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Work.Whitney.CutPush
