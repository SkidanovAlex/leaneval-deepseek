import Mathlib
import Submission.Work.ORP311.P311Defs
import Submission.Work.ORP311.hdim_translate
import Submission.Work.ORP311.piLp_l2_hilbertBasis

namespace Work.ORP311

open scoped InnerProductSpace

/-- **Faithfulness of the von Neumann dimension at zero** (Node P6 of the ORP311 route).

A `diagOp`-invariant subspace `K ⊆ ⊕_{i : Fin n} ℓ²(G)` whose von Neumann dimension vanishes
is trivial.

`hdim_translate` rewrites the dimension as `∑ i, ‖K.starProjection (hinclude n i (deltaG g))‖²`
for *every* `g : G`, so `hdim K = 0` forces the projection of every translated basis vector
`hinclude n i (δ_g)` to vanish.  These vectors are exactly the orthonormal family
`piLpBasisVec` whose span is dense (`span_piLpBasisVec_orthogonal_eq_bot`); since
`K.starProjection` is self-adjoint and vanishes on that family, it is orthogonal to `x` for
each `x ∈ K`, whence `x = 0`. -/
theorem eq_bot_of_hdim_eq_zero {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n : ℕ} (K : Submodule ℂ (Work.ORVonNeumann.Rep.HSum (G := G) n)) [K.HasOrthogonalProjection] (hK : ∀ g : G, ∀ x ∈ K, Work.ORVonNeumann.Rep.diagOp (G := G) n g x ∈ K) (h0 : Work.ORVonNeumann.Rep.hdim (G := G) K = 0) : K = ⊥ := by
  -- The projection onto an invariant subspace is equivariant for the diagonal action.
  have hKeq : Work.ORVonNeumann.Rep.Equivariant (G := G) K.starProjection :=
    Work.ORVonNeumann.Rep.equivariant_starProjection (G := G) hK
  -- `hdim K = 0` kills the projection of every translated basis vector `hinclude n i (δ_g)`.
  have hproj : ∀ (g : G) (i : Fin n),
      K.starProjection
        (Work.ORVonNeumann.Rep.hinclude (G := G) n i (Work.ORVonNeumann.Rep.deltaG g)) = 0 := by
    intro g i
    have hsum : (∑ i : Fin n,
        ‖K.starProjection
          (Work.ORVonNeumann.Rep.hinclude (G := G) n i (Work.ORVonNeumann.Rep.deltaG g))‖ ^ 2)
        = 0 := by
      rw [Work.ORP311.hdim_translate (G := G) K hKeq g, h0]
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (s := Finset.univ)
      (f := fun i : Fin n => ‖K.starProjection
        (Work.ORVonNeumann.Rep.hinclude (G := G) n i
          (Work.ORVonNeumann.Rep.deltaG g))‖ ^ 2)
      (fun j _ => sq_nonneg _)).mp hsum i (Finset.mem_univ i)
    have hnorm : ‖K.starProjection
        (Work.ORVonNeumann.Rep.hinclude (G := G) n i
          (Work.ORVonNeumann.Rep.deltaG g))‖ = 0 := by
      nlinarith [sq_nonneg ‖K.starProjection
        (Work.ORVonNeumann.Rep.hinclude (G := G) n i
          (Work.ORVonNeumann.Rep.deltaG g))‖]
    exact norm_eq_zero.mp hnorm
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hxproj : K.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
  -- Every `x ∈ K` is orthogonal to the total family `piLpBasisVec`.
  have hxorth : x ∈ (Submodule.span ℂ (Set.range (Work.ORP311.piLpBasisVec G n)))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨⟨g, i⟩, rfl⟩ := hz
        rw [Work.ORP311.piLpBasisVec_apply]
        have hy : PiLp.single (β := fun _ : Fin n => Work.ORVonNeumann.l2 G) 2 i
              (Work.ORVonNeumann.Rep.deltaG g)
            = Work.ORVonNeumann.Rep.hinclude (G := G) n i
                (Work.ORVonNeumann.Rep.deltaG g) := by
          rw [eq_comm]
          ext
          simp [Work.ORVonNeumann.Rep.hinclude]
        rw [hy, ← hxproj,
          ← Submodule.inner_starProjection_left_eq_right K
            (Work.ORVonNeumann.Rep.hinclude (G := G) n i
              (Work.ORVonNeumann.Rep.deltaG g)) x,
          hproj g i, inner_zero_left]
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
  rw [Work.ORP311.span_piLpBasisVec_orthogonal_eq_bot (G := G) n] at hxorth
  simpa using hxorth

end Work.ORP311
