import Submission.Work.SphHomology.Defs
import Submission.Work.SphHomology.Topology
import Submission.Work.SphHomology.PieceCharted
import Submission.Work.Cohomology.excision
import Submission.Work.Cohomology.relChains_vanishing_of_compact
import Submission.Work.Cohomology.localCohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-!
# The base case of the dimension bound for the sphere bundle

A closed subset `A` of the sphere bundle of a Euclidean bundle that is contained in the
trivialised piece over one set `Z.baseSet i` has vanishing relative homology `H_j(S, S∖A)` above
the dimension `8 + (k-1)` of that piece.

The proof excises the complement of the piece (`Work.Cohomology.excision`), identifies the piece
with the product `↥(Z.baseSet i) × S^{k-1}` (`Work.SphHomology.sphPiece_homeo`) — a charted space of
model dimension `8 + (k-1)` — and applies `Work.Cohomology.relChains_vanishing_of_compact`,
Hatcher's Lemma 3.27(b).
-/

open CategoryTheory AlgebraicTopology Limits
open scoped Topology
open Set Work.TangentClasses

namespace Work.SphHomology

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {k : ℕ}

/-- **The base case.**  Let `A` be a closed subset of the sphere bundle `S(Z)` of a Euclidean bundle
`Z` of rank `k ≥ 1` over a base charted on `ℝ⁸`, contained in the trivialised piece over
`Z.baseSet i`.  Then `H_j(S, S∖A) = 0` for `j > 8 + (k-1)`, the dimension of the piece. -/
theorem isZero_relChains_sphSub_of_subset_piece [CompactSpace B] [T2Space B]
    [ChartedSpace (EuclideanSpace ℝ (Fin 8)) B] (hk : 1 ≤ k)
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) (hZ : Work.Thom.IsEuclidean Z) (i : ι)
    {A : Set (Work.Thom.SphSub Z)} (hAcl : IsClosed A) (hAsub : A ⊆ sphOver Z (Z.baseSet i))
    {j : ℕ} (hj : 8 + (k - 1) < j) :
    IsZero ((Work.Cohomology.relChains (TopCat.of (Work.Thom.SphSub Z)) Aᶜ).homology j) := by
  classical
  haveI : CompactSpace (Work.Thom.SphSub Z) := compactSpace_sphSub Z hZ
  set P : Set (Work.Thom.SphSub Z) := sphOver Z (Z.baseSet i) with hP
  have hopenP : IsOpen P := isOpen_sphPiece Z i
  -- excision: `H_j(S, S∖A) ≅ H_j(P, P∖A)`
  obtain ⟨e₁⟩ := Work.Cohomology.excision (TopCat.of (Work.Thom.SphSub Z)) Aᶜ Pᶜ
    (by
      rw [hopenP.isClosed_compl.closure_eq, hAcl.isOpen_compl.interior_eq]
      intro x hx hxA
      exact hx (hAsub hxA)) j
  -- the double complement of the piece is the piece
  let A' : Set ↥(Pᶜᶜ) := {x | (x : Work.Thom.SphSub Z) ∈ Aᶜ}
  let A₂ : Set ↥P := {y | (y : Work.Thom.SphSub Z) ∈ Aᶜ}
  have hA'₂ : ∀ x : ↥(Pᶜᶜ), x ∈ A' ↔ complComplHomeo P x ∈ A₂ := by
    intro x
    rw [show x ∈ A' ↔ (x : Work.Thom.SphSub Z) ∈ Aᶜ from Iff.rfl,
      show complComplHomeo P x ∈ A₂ ↔
        ((complComplHomeo P x : ↥P) : Work.Thom.SphSub Z) ∈ Aᶜ from Iff.rfl,
      complComplHomeo_apply]
  obtain ⟨e₂⟩ := Work.Cohomology.relChains_homeomorph ↥(Pᶜᶜ) ↥P A' A₂ (complComplHomeo P) hA'₂ j
  -- identify the piece with the product model
  obtain ⟨Φ⟩ := sphPiece_homeo Z hZ i
  let M : Type := ↥(Z.baseSet i) × ModelSph (EuclideanSpace ℝ (Fin k))
  let A₃ : Set M := Φ ⁻¹' A₂
  obtain ⟨e₃⟩ := Work.Cohomology.relChains_homeomorph M ↥P A₃ A₂ Φ (fun q => Iff.rfl) j
  -- the complement of `A₃` is the image of `A`, which is compact
  let Ap : Set ↥P := {y | (y : Work.Thom.SphSub Z) ∈ A}
  let C : Set M := Φ.symm '' Ap
  have hAc : IsCompact A := hAcl.isCompact
  haveI : CompactSpace ↥A := isCompact_iff_compactSpace.mp hAc
  have hAp : IsCompact Ap := by
    rw [show Ap = Set.range (fun x : ↥A => (⟨(x : Work.Thom.SphSub Z), hAsub x.2⟩ : ↥P)) from
      Set.ext (fun y => ⟨fun hy => ⟨⟨(y : Work.Thom.SphSub Z), hy⟩, rfl⟩,
        fun ⟨x, hx⟩ => hx ▸ x.2⟩)]
    exact isCompact_range (by fun_prop)
  have hC : IsCompact C := hAp.image Φ.symm.continuous
  have hCA₃ : Cᶜ = A₃ := by
    ext q
    rw [Set.mem_compl_iff, Set.mem_preimage, Set.mem_image]
    constructor
    · intro hq
      show ¬ ((Φ q : ↥P) : Work.Thom.SphSub Z) ∈ A
      intro hcon
      exact hq ⟨Φ q, hcon, Φ.symm_apply_apply q⟩
    · intro hq
      rintro ⟨y, hy, hyq⟩
      exact hq (by rw [← hyq, Φ.apply_symm_apply]; exact hy)
  -- the product model is a charted space
  obtain ⟨cM⟩ := sphPiece_charted_prod (Z := Z) hk i
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (8 + (k - 1)))) M := cM
  have hprod : IsZero ((Work.Cohomology.relChains (TopCat.of M) A₃).homology j) := by
    rw [← hCA₃]
    exact Work.Cohomology.relChains_vanishing_of_compact (n := 8 + (k - 1)) (by omega)
      (M := TopCat.of M) C hC j hj
  exact IsZero.of_iso hprod (e₁ ≪≫ e₂ ≪≫ e₃.symm)

end

end Work.SphHomology
