import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnDiag
import Submission.Work.ORVonNeumann.Rep.vnDiagOpAdjoint
import Submission.Work.ORVonNeumann.Rep.delta1_separating
import Submission.Work.ORVonNeumann.Rep.vnAssembly
import Submission.Work.ORVonNeumann.Rep.vnBlockUpperAdjointKernel

/-!
# Translation invariance of the von Neumann dimension

The von Neumann dimension of a closed subspace `K ⊆ HSum n = ⊕_{i : Fin n} ℓ²(G)` is defined as
`hdim K = ∑ i, ‖K.starProjection (hdelta n i)‖ ^ 2`, i.e. it is computed on the basis vectors
`δ₁` of the summands.  The dimension of an *invariant* subspace — one whose projection is
equivariant for the block diagonal right regular action `diagOp n g = ⊕_i ρ g` — can be computed
on the translated vectors `δ_g` instead:

  `∑ i, ‖K.starProjection (hinclude n i (deltaG g))‖ ^ 2 = hdim K`.

The proof is a transport along the unitary `diagOp n g⁻¹`: it sends `δ₁` to `δ_g`
(`rightRegOp_inv_delta1`, `diagOp_hinclude`), it commutes with `K.starProjection` by
equivariance, and it preserves norms (`norm_diagOp`).

## Main result

* `Work.ORP311.hdim_translate` — the sum of the squared norms of the projections of the
  translated basis vectors equals `hdim K`.

## Auxiliary results (used by `hdim_translate`)

* `Work.ORP311.norm_rightRegOp` — `ρ g` preserves norms on `ℓ²(G)`;
* `Work.ORP311.norm_diagOp` — `diagOp n g` preserves norms on `HSum n`;
* `Work.ORP311.starProjection_diagOp` — an equivariant projection commutes with `diagOp`.
-/

namespace Work.ORP311

open scoped InnerProductSpace InnerProduct

/-- `ρ g` preserves the norm on `ℓ²(G)`: the right regular representation is by isometries. -/
theorem norm_rightRegOp {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] (g : G) (y : Work.ORVonNeumann.l2 G) :
    ‖Work.ORVonNeumann.Rep.rightRegOp (G := G) g y‖ = ‖y‖ := by
  have h : ∀ z : Work.ORVonNeumann.l2 G,
      ‖Work.ORVonNeumann.Rep.rightRegOp (G := G) g z‖ = ‖z‖ := by
    rw [← AddMonoidHomClass.isometry_iff_norm]
    exact Work.ORVonNeumann.Rep.rightRegOp_isometry g
  exact h y

/-- The block diagonal right regular action `diagOp n g = ⊕_{i : Fin n} ρ g` preserves norms. -/
theorem norm_diagOp {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] (n : ℕ) (g : G)
    (x : Work.ORVonNeumann.Rep.HSum (G := G) n) :
    ‖Work.ORVonNeumann.Rep.diagOp (G := G) n g x‖ = ‖x‖ := by
  -- Compute both squared norms with `PiLp.norm_sq_eq_of_L2`: `diagOp` acts coordinatewise by
  -- `ρ g`, which is an isometry, so the sums of the squared coordinate norms agree.
  have h1 := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => Work.ORVonNeumann.l2 G)
    (Work.ORVonNeumann.Rep.diagOp (G := G) n g x)
  have h2 := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => Work.ORVonNeumann.l2 G) x
  have h3 : (∑ i : Fin n,
        ‖((Work.ORVonNeumann.Rep.diagOp (G := G) n g x).ofLp i)‖ ^ 2)
      = ∑ i : Fin n, ‖x.ofLp i‖ ^ 2 :=
    Finset.sum_congr rfl fun i _ => by
      rw [Work.ORVonNeumann.Rep.diagOp_ofLp, norm_rightRegOp]
  have hs : ‖Work.ORVonNeumann.Rep.diagOp (G := G) n g x‖ ^ 2 = ‖x‖ ^ 2 := by rw [h1, h2, h3]
  nlinarith [norm_nonneg (Work.ORVonNeumann.Rep.diagOp (G := G) n g x), norm_nonneg x]

/-- An equivariant orthogonal projection commutes with the block diagonal right regular action. -/
theorem starProjection_diagOp {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] {n : ℕ}
    (K : Submodule ℂ (Work.ORVonNeumann.Rep.HSum (G := G) n)) [K.HasOrthogonalProjection]
    (hK : Work.ORVonNeumann.Rep.Equivariant (G := G) K.starProjection) (g : G)
    (x : Work.ORVonNeumann.Rep.HSum (G := G) n) :
    K.starProjection (Work.ORVonNeumann.Rep.diagOp (G := G) n g x)
      = Work.ORVonNeumann.Rep.diagOp (G := G) n g (K.starProjection x) := by
  have h := congrArg
    (fun f : Work.ORVonNeumann.Rep.HSum (G := G) n →L[ℂ] Work.ORVonNeumann.Rep.HSum (G := G) n
      => f x) (hK g)
  simpa only [ContinuousLinearMap.comp_apply] using h

theorem hdim_translate {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n : ℕ} (K : Submodule ℂ (Work.ORVonNeumann.Rep.HSum (G := G) n)) [K.HasOrthogonalProjection] (hK : Work.ORVonNeumann.Rep.Equivariant (G := G) K.starProjection) (g : G) : (∑ i : Fin n, ‖K.starProjection (Work.ORVonNeumann.Rep.hinclude (G := G) n i (Work.ORVonNeumann.Rep.deltaG g))‖ ^ 2) = Work.ORVonNeumann.Rep.hdim (G := G) K := by
  -- `ρ g⁻¹` sends `δ₁` to `δ_g`, so `diagOp n g⁻¹` sends the `i`-th basis vector `hdelta n i` to
  -- `hinclude n i (deltaG g)`.
  have hdelta : ∀ i : Fin n,
      Work.ORVonNeumann.Rep.hinclude (G := G) n i (Work.ORVonNeumann.Rep.deltaG g)
        = Work.ORVonNeumann.Rep.diagOp (G := G) n g⁻¹
            (Work.ORVonNeumann.Rep.hdelta (G := G) n i) := by
    intro i
    rw [Work.ORVonNeumann.Rep.hdelta_apply]
    have h := congrArg
      (fun f : Work.ORVonNeumann.l2 G →L[ℂ] Work.ORVonNeumann.Rep.HSum (G := G) n
        => f (Work.ORVonNeumann.delta1 G))
      (Work.ORVonNeumann.Rep.diagOp_hinclude (G := G) n g⁻¹ i)
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h, Work.ORVonNeumann.Rep.rightRegOp_inv_delta1]
  rw [Work.ORVonNeumann.Rep.hdim]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- Transport along `diagOp n g⁻¹` using equivariance and norm preservation.
  rw [hdelta i, starProjection_diagOp K hK g⁻¹, norm_diagOp]

end Work.ORP311
