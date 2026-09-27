import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.ChartBridge
import Submission.Work.Drive.ManifoldParity.Transfer
import Submission.Work.Drive.ManifoldParity.exists_tangential_field
import Submission.Work.Drive.ManifoldParity.even_ncard_bInterSet_of_tangential_field
import Submission.Work.Embedding.smooth_implicit_function_nhd
import Submission.Work.OneDim.one_manifold_dichotomy
import Submission.Work.OneDim.classify_connected_one_manifold

namespace Work.Drive

open Manifold in
open scoped Manifold ContDiff in
/-- **The mod-2 parity of the boundary intersections of two transverse chains in a smooth
4-manifold.**  This is the form the mod-2 intersection chapter takes when the ambient space is a
genuine 4-manifold rather than a vector space.  `Work.Drive.even_ncard_loopMeet_add_solidMeet`
(`Submission/Work/Drive/intersection_parity.lean`) proves the corresponding statement for
`D : ℝ² → ℝ⁴`, `N : ℝ³ → ℝ⁴` using the *difference map* `D (sqPart x) - N (cbPart x)`, which needs the
ambient to be a vector space; the capping of Hugelmeyer's configuration Möbius strip, however, lives in
the 4-manifold `ℝ × ℝP³`, so the counting arguments of Hugelmeyer's auxiliary results 3 and 4 need the
manifold form.

There are three hypotheses, matching the three hypotheses of `Submission.Drive.ParityProp` in the
vector-space case:

* `hD`, `hN`: the two chains are smooth;
* `htrans`: `D` and `N` meet transversally — at every pair with `D s = N t` the two tangent images
  together span the whole tangent space (they are submodules of the same tangent space, since
  `D s = N t`);
* `hface`: every *boundary* intersection is on exactly one face of the box and meets it
  transversally: either `s` has exactly one coordinate in `{0,1}`, the other and all of `t` are strictly
  inside, and some tangent vector `(σ,τ)` with `mfderiv D s σ = mfderiv N t τ` has `σ i ≠ 0`; or
  symmetrically for a coordinate of `t`.  This is the hypothesis whose absence makes the conclusion
  false.

The conclusion: the set of *boundary* intersections — pairs `(s,t)` in the two boxes with `D s = N t`
and `s` on the boundary of the square or `t` on the boundary of the cube — is finite and has even
cardinality.  Reason: the set `K` of *all* intersections inside the product of the two boxes is a
compact 1-dimensional manifold with boundary (transversality plus the implicit function result in
charts; `Submission/Work/Embedding/smooth_implicit_function_nhd` is the local input), its boundary is
exactly the boundary intersection set above, and a compact 1-manifold with boundary has an even number
of boundary points (`Submission/Work/OneDim/one_manifold_dichotomy`,
`classify_connected_one_manifold`).  The counts of `D ⋔ ∂N`, of `∂D ⋔ N` and of their sum are the
specialisations used by Hugelmeyer's auxiliary results 3 and 4.

(Definitional note: `Submission.Drive.unitBox m` is the box in `𝔼^{m+1}`, so `unitBox 1` is the box in
`𝔼²`, the domain of `D`, and `unitBox 2` the box in `𝔼³`, the domain of `N`.) -/
theorem transverse_inter_boundary_parity (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (hN : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) N)
    (htrans : ∀ (s : EuclideanSpace ℝ (Fin 2)) (t : EuclideanSpace ℝ (Fin 3)), D s = N t →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) D s).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) N t).toLinearMap = ⊤)
    (hface : ∀ (s : EuclideanSpace ℝ (Fin 2)) (t : EuclideanSpace ℝ (Fin 3)), D s = N t →
      s ∈ Submission.Drive.unitBox 1 → t ∈ Submission.Drive.unitBox 2 →
      (s ∈ Submission.Drive.unitBoxBdry 1 ∨ t ∈ Submission.Drive.unitBoxBdry 2) →
      (∃ i : Fin 2, (s i = 0 ∨ s i = 1) ∧ (∀ j : Fin 2, j ≠ i → s j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ j : Fin 3, t j ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) D s σ = mfderiv (𝓡 3) (𝓡 4) N t τ ∧ σ i ≠ 0)
      ∨ (∃ j : Fin 3, (t j = 0 ∨ t j = 1) ∧ (∀ k : Fin 3, k ≠ j → t k ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ i : Fin 2, s i ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) D s σ = mfderiv (𝓡 3) (𝓡 4) N t τ ∧ τ j ≠ 0)) :
    ({p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) |
        D p.1 = N p.2 ∧ p.1 ∈ Submission.Drive.unitBox 1 ∧ p.2 ∈ Submission.Drive.unitBox 2 ∧
        (p.1 ∈ Submission.Drive.unitBoxBdry 1 ∨ p.2 ∈ Submission.Drive.unitBoxBdry 2)}).Finite ∧
      Even ({p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) |
        D p.1 = N p.2 ∧ p.1 ∈ Submission.Drive.unitBox 1 ∧ p.2 ∈ Submission.Drive.unitBox 2 ∧
        (p.1 ∈ Submission.Drive.unitBoxBdry 1 ∨
          p.2 ∈ Submission.Drive.unitBoxBdry 2)}).ncard := by
  -- the two hypotheses of the target theorem, in the `ℝ⁵` coordinates of the mod-2 chapter
  have htrans' : ∀ x : Work.Drive.Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x) →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) D (Work.Drive.sqPart x)).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) N (Work.Drive.cbPart x)).toLinearMap = ⊤ :=
    fun x _ hx => htrans (Work.Drive.sqPart x) (Work.Drive.cbPart x) hx
  have hface' : ∀ x : Work.Drive.Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x) →
      x ∈ Submission.Drive.unitBoxBdry 4 →
      (∃ i : Fin 2, (Work.Drive.sqPart x i = 0 ∨ Work.Drive.sqPart x i = 1) ∧
          (∀ j : Fin 2, j ≠ i → Work.Drive.sqPart x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ j : Fin 3, Work.Drive.cbPart x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) D (Work.Drive.sqPart x) σ =
              mfderiv (𝓡 3) (𝓡 4) N (Work.Drive.cbPart x) τ ∧ σ i ≠ 0)
      ∨ (∃ j : Fin 3, (Work.Drive.cbPart x j = 0 ∨ Work.Drive.cbPart x j = 1) ∧
          (∀ k : Fin 3, k ≠ j → Work.Drive.cbPart x k ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ i : Fin 2, Work.Drive.sqPart x i ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) D (Work.Drive.sqPart x) σ =
              mfderiv (𝓡 3) (𝓡 4) N (Work.Drive.cbPart x) τ ∧ τ j ≠ 0) := by
    intro x hxbox hDx hxbdy
    have hb := (Work.Drive.mem_unitBox_iff_prod x).mp hxbox
    rcases (Work.Drive.mem_unitBoxBdry_iff_prod x hxbox).mp hxbdy with h | h
    · exact hface (Work.Drive.sqPart x) (Work.Drive.cbPart x) hDx hb.1 hb.2 (Or.inl h)
    · exact hface (Work.Drive.sqPart x) (Work.Drive.cbPart x) hDx hb.1 hb.2 (Or.inr h)
  -- a non-zero smooth compactly supported field tangent to the intersection set
  obtain ⟨V, hV, hVsupp, hVne, hVtan⟩ :=
    Work.Drive.ManifoldParity.exists_tangential_field D N hD hN htrans'
  -- the flow of that field pairs the boundary intersections up
  have hmain := Work.Drive.ManifoldParity.even_ncard_bInterSet_of_tangential_field
    D N hD hN htrans' hface' V hV hVsupp hVne hVtan
  refine ⟨?_, ?_⟩
  · exact (Work.Drive.prodBInterSet_finite_iff D N).mpr hmain.1
  · exact (Work.Drive.prodBInterSet_ncard D N).symm ▸ hmain.2

end Work.Drive
