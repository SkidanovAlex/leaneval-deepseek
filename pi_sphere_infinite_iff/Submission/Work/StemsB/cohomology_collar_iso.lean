import Submission.Work.StemsB.SerreCohomologyTargets
import Submission.Work.StemsB.RelCohTransport
import Submission.Work.StemsB.SerreSphereCollar
import Submission.Work.StemsB.CollarModel
import Submission.Work.Thom.ModelThomDefs
import Submission.Work.Thom.ModelThomBase

set_option synthInstance.maxHeartbeats 400000

/-!
# The relative cohomology of the collar pair of the sphere model

This file proves `Work.StemsB.CollarCohomology`: for every `b ≥ 1`, every space `Y` and every `j`,
the relative cohomology of the pair `(sphLoopBig b × Y, sphLoopCollar b × Y)` in degree `j + b` is
the cohomology of `Y` in degree `j`.

The proof composes five identifications:

1. `Work.StemsB.bigToEucRelChainMap` (coordinate extraction, a quasi-isomorphism of relative chain
   complexes, `Work.StemsB.isIso_bigToEucRelChains`): the model collar pair has the same relative
   cohomology as the Euclidean collar pair `(eucBig b × Y, eucCollarProd b Y)`;
2. `Work.StemsB.eucNormRelMap` (the sup-norm normalisation, again a quasi-isomorphism,
   `Work.StemsB.isIso_eucNormRelChains`): the Euclidean collar pair has the same relative
   cohomology as the cube pair `(↥(eucCube b) × Y, eucBdryProd b Y)`;
3. the pair homeomorphism `eucCube b ≃ₜ MBall b` (radial, carrying the cube boundary onto the unit
   sphere) — `Work.StemsB.eucCube_mBall_homeomorph`, proved below via
   `exists_homeomorph_image_interior_closure_frontier_eq_unitBall` — together with the commutation
   of the two product factors;
4. `Work.Thom.bijective_relCohMap_discFull`: the pair `(B × Dⁿ, B × Sⁿ⁻¹)` is a homotopy
   retract of `(B × ℝⁿ, B × Sⁿ⁻¹)`;
5. `Work.Thom.modelThom_all` (the model Thom class of the trivial bundle): `H^{j+n}(B × ℝⁿ,
   B × Sⁿ⁻¹) ≅ H^j(B)`.

The whole file is a chain of `Nonempty (· ≅ ·)` statements composed with `Iso.trans`.

This is the cohomological counterpart of `Work.StemsB.serreSphere_collar_iso`; it is the single
remaining ingredient of the cohomological Wang sequence over a sphere
(`Submission/Work/StemsB/SerreCohomologyTargets.lean`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.StemsB

noncomputable section

/-! ## 0. The cube pair is the ball pair

The closed cube `eucCube b = {|v|_∞ ≤ 1}` is a compact convex body with nonempty interior, so by
`exists_homeomorph_image_interior_closure_frontier_eq_unitBall` there is a homeomorphism of
`EuclideanSpace ℝ (Fin b)` carrying the cube onto the Euclidean unit ball and, consequently, the
frontier of the cube onto the unit sphere.  Restricting to the cube gives the pair homeomorphism we
need. -/

/-- The interior of the cube `eucCube b` is the open cube `{|v|_∞ < 1}`. -/
theorem interior_eucCube (b : ℕ) :
    interior (eucCube b) = {v : EuclideanSpace ℝ (Fin b) | ∀ i, |v i| < 1} := by
  have hset : eucCube b = (PiLp.homeomorph 2 (fun _ : Fin b => ℝ)) ⁻¹'
      (Set.pi Set.univ (fun _ : Fin b => Set.Icc (-1:ℝ) 1)) := by
    ext v
    rw [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h i; exact Set.mem_Icc.mpr (abs_le.mp (h i))
    · intro h i; exact abs_le.mpr (Set.mem_Icc.mp (h i))
  rw [hset, ← Homeomorph.preimage_interior, interior_pi_set Set.finite_univ]
  ext v
  rw [Set.mem_preimage, Set.mem_univ_pi]
  constructor
  · intro h i
    have hi := h i
    rw [interior_Icc, Set.mem_Ioo] at hi
    exact abs_lt.mpr hi
  · intro h i
    rw [interior_Icc, Set.mem_Ioo]
    exact abs_lt.mp (h i)

/-- The frontier of the cube `eucCube b` is the cube boundary `eucBdry b`. -/
theorem frontier_eucCube (b : ℕ) : frontier (eucCube b) = eucBdry b := by
  have hcube : eucCube b =
      {v : EuclideanSpace ℝ (Fin b) | coordSup b v ≤ 1} := by
    ext v
    simp only [eucCube, Set.mem_ofPred_eq]
    rw [coordSup_le_one_iff]
    constructor
    · intro h i; exact Set.mem_Icc.mpr (abs_le.mp (h i))
    · intro h i; exact abs_le.mpr (Set.mem_Icc.mp (h i))
  have hcompact : IsCompact (eucCube b) := by rw [hcube]; exact isCompact_coordSup_le_one b
  have hclosure : closure (eucCube b) = eucCube b := hcompact.isClosed.closure_eq
  rw [frontier, hclosure, interior_eucCube]
  ext v
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, eucBdry, not_forall, not_lt]
  constructor
  · rintro ⟨h1, i, hi⟩
    exact ⟨h1, i, le_antisymm (h1 i) hi⟩
  · rintro ⟨h1, i, hi⟩
    exact ⟨h1, i, by rw [hi]⟩

/-- The closed cube `eucCube b` is homeomorphic to the closed Euclidean unit ball of
`EuclideanSpace ℝ (Fin b)`, by a homeomorphism carrying the cube boundary `eucBdry b` onto the unit
sphere. -/
theorem eucCube_closedBall_homeomorph (b : ℕ) :
    ∃ e : ↥(eucCube b) ≃ₜ ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin b)) 1),
      ∀ x : ↥(eucCube b),
        (x : EuclideanSpace ℝ (Fin b)) ∈ eucBdry b ↔
          (e x : EuclideanSpace ℝ (Fin b)) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin b)) 1 := by
  have hcube : eucCube b =
      {v : EuclideanSpace ℝ (Fin b) | coordSup b v ≤ 1} := by
    ext v
    simp only [eucCube, Set.mem_ofPred_eq]
    rw [coordSup_le_one_iff]
    constructor
    · intro h i; exact Set.mem_Icc.mpr (abs_le.mp (h i))
    · intro h i; exact abs_le.mpr (Set.mem_Icc.mp (h i))
  have hconv : Convex ℝ (eucCube b) := by
    have h1 : eucCube b = ⋂ i : Fin b, {v : EuclideanSpace ℝ (Fin b) | |v i| ≤ 1} := by
      ext v; simp [eucCube]
    rw [h1]
    refine convex_iInter fun i => ?_
    have h2 : {v : EuclideanSpace ℝ (Fin b) | |v i| ≤ 1}
        = (fun v : EuclideanSpace ℝ (Fin b) => v i) ⁻¹' (Set.Icc (-1:ℝ) 1) := by
      ext v
      show |v i| ≤ 1 ↔ v i ∈ Set.Icc (-1:ℝ) 1
      rw [abs_le, Set.mem_Icc]
    rw [h2]
    exact (convex_Icc (-1:ℝ) 1).is_linear_preimage
      ⟨fun x y => by simp, fun c x => by simp⟩
  have hbdd : Bornology.IsBounded (eucCube b) := by
    rw [hcube]
    exact (isCompact_coordSup_le_one b).isBounded
  have hne : (interior (eucCube b)).Nonempty := by
    refine ⟨0, ?_⟩
    rw [interior_eucCube]
    exact fun i => by simp
  obtain ⟨h, _hbal, hclosedball, hsph⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv hne hbdd
  have hcompact : IsCompact (eucCube b) := by rw [hcube]; exact isCompact_coordSup_le_one b
  have hclosure : closure (eucCube b) = eucCube b := hcompact.isClosed.closure_eq
  have himg : h '' eucCube b = Metric.closedBall (0 : EuclideanSpace ℝ (Fin b)) 1 := by
    rw [← hclosure]; exact hclosedball
  refine ⟨(Homeomorph.image h (eucCube b)).trans (Homeomorph.setCongr himg), ?_⟩
  intro x
  have hx : (((Homeomorph.image h (eucCube b)).trans (Homeomorph.setCongr himg)) x :
      EuclideanSpace ℝ (Fin b)) = h (x : EuclideanSpace ℝ (Fin b)) := rfl
  rw [hx, ← hsph]
  constructor
  · intro hxbd
    exact ⟨x, by rw [frontier_eucCube]; exact hxbd, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hxy : y = x := h.injective hyx
    rw [← frontier_eucCube, ← hxy]
    exact hy

/-- The same homeomorphism, stated with the workspace's `MBall`/`mSph`. -/
theorem eucCube_mBall_homeomorph (b : ℕ) :
    ∃ e : ↥(eucCube b) ≃ₜ Work.Thom.MBall b,
      ∀ x : ↥(eucCube b),
        ((x : EuclideanSpace ℝ (Fin b)) ∈ eucBdry b ↔
          ((e x : Work.Thom.MBall b) : EuclideanSpace ℝ (Fin b)) ∈ Work.Thom.mSph b) := by
  obtain ⟨e₀, he₀⟩ := eucCube_closedBall_homeomorph b
  have hball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin b)) 1 = Work.Thom.mBall b := by
    ext v; simp [Work.Thom.mBall, Metric.closedBall, dist_eq_norm]
  have hsph : Metric.sphere (0 : EuclideanSpace ℝ (Fin b)) 1 = Work.Thom.mSph b := by
    ext v; simp [Work.Thom.mSph, Metric.sphere, dist_eq_norm]
  refine ⟨e₀.trans (Homeomorph.setCongr hball), ?_⟩
  intro x
  have hx : (((e₀.trans (Homeomorph.setCongr hball)) x : Work.Thom.MBall b) :
      EuclideanSpace ℝ (Fin b)) = (e₀ x : EuclideanSpace ℝ (Fin b)) := rfl
  rw [hx, ← hsph]
  exact he₀ x

/-! ## 1. The model Thom class of the trivial bundle

`Work.Thom.modelThom_all` provides a class `τ ∈ H^{b}(Y × ℝ^b, Y × S^{b-1})` for which cupping,
`x ↦ π^*(x) ⌣ τ`, is a bijection `H^j(Y) → H^{j+b}(Y × ℝ^b, Y × S^{b-1})`. -/

theorem nonempty_cohomology_model_thom (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (j : ℕ) :
    Nonempty (Work.Thom.Coh ℤ j Y ≅ Work.Thom.RelCoh ℤ (j + b)
      (Y × EuclideanSpace ℝ (Fin b)) {p | p.2 ∈ Work.Thom.mSph b}) := by
  obtain ⟨τ, hτ⟩ := Work.Thom.modelThom_all Y PUnit (n := b) hb
  let F : ↥(Work.Thom.Coh ℤ j Y) →ₗ[ℤ]
      ↥(Work.Thom.RelCoh ℤ (j + b) (Y × EuclideanSpace ℝ (Fin b))
        {p | p.2 ∈ Work.Thom.mSph b}) :=
    { toFun := fun x => (Work.Thom.mixedCupC ℤ
        {p : Y × EuclideanSpace ℝ (Fin b) | p.2 ∈ Work.Thom.mSph b} j b)
          ((Work.Thom.CohMap (Work.Thom.projFst Y b) ℤ j).hom x) τ
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp }
  exact ⟨(LinearEquiv.ofBijective F (hτ j)).toModuleIso⟩

/-! ## 2. The disc pair is a homotopy retract of the trivial bundle

`Work.Thom.bijective_relCohMap_discFull`: the inclusion of pairs
`(B × Dⁿ, B × Sⁿ⁻¹) → (B × ℝⁿ, B × Sⁿ⁻¹)` induces a bijection on relative cohomology. -/

theorem nonempty_relCoh_discFull (b m : ℕ) (Y : Type) [TopologicalSpace Y] :
    Nonempty (Work.Thom.RelCoh ℤ m (Y × EuclideanSpace ℝ (Fin b)) {p | p.2 ∈ Work.Thom.mSph b}
      ≅ Work.Thom.RelCoh ℤ m (Y × Work.Thom.MBall b) {q | q.2.1 ∈ Work.Thom.mSph b}) := by
  have hbij := Work.Thom.bijective_relCohMap_discFull Y b m
  let mm := Work.Thom.relCohMap
    (⟨fun q : Y × Work.Thom.MBall b => (q.1, q.2.1),
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)⟩ :
      C(Y × Work.Thom.MBall b, Y × EuclideanSpace ℝ (Fin b)))
    {q : Y × Work.Thom.MBall b | q.2.1 ∈ Work.Thom.mSph b}
    {p : Y × EuclideanSpace ℝ (Fin b) | p.2 ∈ Work.Thom.mSph b}
    (fun q hq => hq) ℤ m
  haveI : IsIso mm := (ConcreteCategory.isIso_iff_bijective mm).mpr hbij
  exact ⟨asIso mm⟩

/-! ## 3. The cube pair, the ball pair and the two orders of the product -/

/-- A pair homeomorphism carries relative cohomology to relative cohomology: transporting the
homeomorphism `eucCube b ≃ₜ MBall b` along `Y` identifies the ball pair with the cube pair (with
`Y` on the left). -/
theorem nonempty_relCoh_MBall_eucCube (b m : ℕ) (Y : Type) [TopologicalSpace Y] :
    Nonempty (Work.Thom.RelCoh ℤ m (Y × Work.Thom.MBall b) {q | q.2.1 ∈ Work.Thom.mSph b}
      ≅ Work.Thom.RelCoh ℤ m (Y × ↥(eucCube b)) {p | p.2.1 ∈ eucBdry b}) := by
  obtain ⟨e, he⟩ := eucCube_mBall_homeomorph b
  have he' : ∀ q : Y × ↥(eucCube b),
      q ∈ {p : Y × ↥(eucCube b) | p.2.1 ∈ eucBdry b} ↔
        (Homeomorph.prodCongr (Homeomorph.refl Y) e) q ∈
          {p : Y × Work.Thom.MBall b | p.2.1 ∈ Work.Thom.mSph b} := by
    intro q
    exact he q.2
  obtain ⟨iso⟩ := Work.Thom.relCohHomeomorph
    {p : Y × ↥(eucCube b) | p.2.1 ∈ eucBdry b}
    {p : Y × Work.Thom.MBall b | p.2.1 ∈ Work.Thom.mSph b}
    (Homeomorph.prodCongr (Homeomorph.refl Y) e) he' ℤ m
  exact ⟨iso⟩

/-- The two orders of the product give the same relative cohomology: swapping the factors is a
homeomorphism of pairs. -/
theorem nonempty_relCoh_swap_eucCube (b m : ℕ) (Y : Type) [TopologicalSpace Y] :
    Nonempty (Work.Thom.RelCoh ℤ m (Y × ↥(eucCube b)) {p | p.2.1 ∈ eucBdry b}
      ≅ Work.Thom.RelCoh ℤ m (↥(eucCube b) × Y) (eucBdryProd b Y)) := by
  have he : ∀ q : ↥(eucCube b) × Y,
      q ∈ eucBdryProd b Y ↔ (Homeomorph.prodComm ↥(eucCube b) Y) q ∈
        {p : Y × ↥(eucCube b) | p.2.1 ∈ eucBdry b} := by
    intro q
    exact Iff.rfl
  obtain ⟨iso⟩ := Work.Thom.relCohHomeomorph (eucBdryProd b Y)
    {p : Y × ↥(eucCube b) | p.2.1 ∈ eucBdry b} (Homeomorph.prodComm ↥(eucCube b) Y) he ℤ m
  exact ⟨iso⟩

/-- **The ball pair and the cube pair of `Y` have the same relative cohomology.**  Composition of
`nonempty_relCoh_MBall_eucCube` with the factor swap `nonempty_relCoh_swap_eucCube`. -/
theorem nonempty_relCoh_MBall_eucCubeProd (b m : ℕ) (Y : Type) [TopologicalSpace Y] :
    Nonempty (Work.Thom.RelCoh ℤ m (Y × Work.Thom.MBall b) {q | q.2.1 ∈ Work.Thom.mSph b}
      ≅ Work.Thom.RelCoh ℤ m (↥(eucCube b) × Y) (eucBdryProd b Y)) := by
  obtain ⟨e₁⟩ := nonempty_relCoh_MBall_eucCube b m Y
  obtain ⟨e₂⟩ := nonempty_relCoh_swap_eucCube b m Y
  exact ⟨e₁ ≪≫ e₂⟩

/-! ## 4. The Euclidean collar pair

The sup-norm normalisation `eucNormRelMap` is a quasi-isomorphism of relative chain complexes, so
it induces an isomorphism on relative cohomology. -/

theorem nonempty_relCoh_eucNorm (b m : ℕ) (Y : Type) [TopologicalSpace Y] :
    Nonempty (Work.Thom.RelCoh ℤ m (↥(eucCube b) × Y) (eucBdryProd b Y)
      ≅ Work.Thom.RelCoh ℤ m (↥(eucBig b) × Y) (eucCollarProd b Y)) :=
  nonempty_relCohomology_iso_of_relChains_quasiIso (eucNormRelMap (Y := Y) b)
    (isIso_eucNormRelChains (Y := Y) b) m

/-! ## 5. The model collar pair -/

theorem nonempty_relCoh_bigToEuc (b m : ℕ) (Y : Type) [TopologicalSpace Y] :
    Nonempty (Work.Thom.RelCoh ℤ m (↥(eucBig b) × Y) (eucCollarProd b Y)
      ≅ Work.Thom.RelCoh ℤ m (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) :=
  nonempty_relCohomology_iso_of_relChains_quasiIso (bigToEucRelChainMap (Y := Y) b)
    (isIso_bigToEucRelChains (Y := Y) b) m

/-! ## 6. The collar statement -/

/-- **The relative cohomology of the collar pair.**  `H^{j+b}(sphLoopBig b × Y, sphLoopCollar b × Y)
≅ H^j(Y)` for every `b ≥ 1`.  This is `Work.StemsB.CollarCohomology`. -/
theorem cohomology_collar_iso : Work.StemsB.CollarCohomology := by
  intro b hb Y _ j
  show Nonempty (Work.Thom.RelCoh ℤ (j + b) (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)
    ≅ Work.Thom.Coh ℤ j Y)
  obtain ⟨e₁⟩ := nonempty_cohomology_model_thom b hb Y j
  obtain ⟨e₂⟩ := nonempty_relCoh_discFull b (j + b) Y
  obtain ⟨e₃⟩ := nonempty_relCoh_MBall_eucCubeProd b (j + b) Y
  obtain ⟨e₄⟩ := nonempty_relCoh_eucNorm b (j + b) Y
  obtain ⟨e₅⟩ := nonempty_relCoh_bigToEuc b (j + b) Y
  exact ⟨(e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅).symm⟩

end

end Work.StemsB
