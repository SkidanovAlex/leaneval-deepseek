import Mathlib
import Submission.Work.Thom.subsingleton_OpenThom_of_lt_rank
import Submission.Work.Thom.Gysin

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The projection of the complement of the zero section is a cohomology isomorphism, for an
arbitrary finite-dimensional fibre

`Work.Thom.bijective_proj_zeroComplement` proves that for a real bundle `Z` over `B` with model
fibre `EuclideanSpace ℝ (Fin n)` and a Thom class `T : ThomClass Z n`, the pullback
`π_S^* : H^k(B;ℤ) → H^k(E∖0;ℤ)` along the projection of the sphere bundle `π_S = π ∘ (E∖0 ↪ E)` is
bijective whenever `k + 2 ≤ n`.

Here the fibre is an *arbitrary* finite-dimensional real normed space `F`, with
`Module.finrank ℝ F = n`.  Nothing in the argument used the Euclidean structure of the fibre, and
neither does the proof below: it is the same argument, run for a general `F`.

The one input that has to be supplied for a general fibre is the low-degree vanishing of the Thom
pair, `H^m(E, E∖0; ℤ) = 0` for `m < n`.  For the standard fibre `EuclideanSpace ℝ (Fin n)` that is
`Work.Thom.subsingleton_OpenThom_of_lt_rank`; for a general fibre it is assembled here:

* `Work.Thom.subsingleton_PieceCoh_genFibreAux` — the chart-local vanishing
  `H^m(Z|_W, Z|_W∖0) = 0` for `W` inside a chart, by transporting `F` to `ℝ^{finrank ℝ F}` along a
  continuous linear equivalence (`ContinuousLinearEquiv.ofFinrankEq`) and applying the Euclidean
  model;
* `Work.Thom.subsingleton_PieceCoh_genFibreGen` — the chart-local vanishing, unconditional;
* `Work.Thom.subsingleton_OpenThom_genFibre` — the global vanishing `H^m(E,E∖0;ℤ) = 0` for
  `m < finrank ℝ F`, by the transfinite Mayer–Vietoris induction of
  `Submission/Work/Thom/subsingleton_OpenThom_of_lt_rank.lean` run with the chart-local input
  `subsingleton_PieceCoh_genFibreGen` instead of the Euclidean one;
* `Work.Thom.bijective_proj_zeroComplement_gen` — the bijectivity of `π_S^*` for `k + 2 ≤ n`.
-/

open Work.TangentClasses

namespace Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## The chart-local vanishing for an arbitrary fibre (from the Euclidean model) -/

/-- **Vanishing of the relative cohomology of a bundle piece below the rank, for an arbitrary
finite-dimensional fibre, from the Euclidean model.**  If `H^m(W × ℝⁿ, W × (ℝⁿ∖0)) = 0` for every
space `W` and every `m < n` (`hEuc`), then for every real bundle `Z` over `B` with model fibre `F`
and every `W` contained in a single chart of `Z`, the relative cohomology of the piece over `W`
vanishes in degrees below `finrank ℝ F`. -/
theorem subsingleton_PieceCoh_genFibreAux
    (hEuc : ∀ (n : ℕ) (W : Type) [TopologicalSpace W] (m : ℕ), m < n →
      Subsingleton ((Work.Cohomology.relComplex ℤ (TopCat.of (W × (Fin n → ℝ)))
        {p : W × (Fin n → ℝ) | (p.2 : Fin n → ℝ) ≠ 0}).homology m))
    [FiniteDimensional ℝ F] (ι : Type) [Inhabited ι]
    (Z : RealBundle B F ι) (i : ι)
    {W : Set B} (hW : W ⊆ Z.baseSet i) {m : ℕ} (hm : m < Module.finrank ℝ F) :
    Subsingleton (PieceCoh Z W m) := by
  -- the chart homeomorphism `(X|_W, X|_W∖0) ≅ (↥W × F, ↥W × (F∖0))`
  obtain ⟨hW1, hW2⟩ := pieceChartHomeo Z i hW
  -- the fibre homeomorphism `F ≃ₜ ℝ^{finrank F}`
  have hfr : Module.finrank ℝ F =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ F))) := by
    rw [finrank_euclideanSpace_fin]
  let eF : F ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) :=
    ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := F)
      (F := EuclideanSpace ℝ (Fin (Module.finrank ℝ F))) hfr
  let e2 : ↥W × F ≃ₜ ↥W × (Fin (Module.finrank ℝ F) → ℝ) :=
    Homeomorph.prodCongr (Homeomorph.refl ↥W)
      (eF.toHomeomorph.trans (PiLp.homeomorph 2 (fun _ : Fin (Module.finrank ℝ F) => ℝ)))
  let e : ↥(Z.proj ⁻¹' W) ≃ₜ ↥W × (Fin (Module.finrank ℝ F) → ℝ) := hW1.trans e2
  have hiff : ∀ z : ↥(Z.proj ⁻¹' W),
      z ∈ {y : ↥(Z.proj ⁻¹' W) | (y : Z.TotalSpace) ∈ zeroComplement Z} ↔
        e z ∈ {p : ↥W × (Fin (Module.finrank ℝ F) → ℝ) |
          (p.2 : Fin (Module.finrank ℝ F) → ℝ) ≠ 0} := by
    intro z
    simp only [Set.mem_ofPred_eq]
    rw [hW2 z]
    have hthis : (e z).2 = (eF (hW1 z).2).ofLp := rfl
    rw [hthis]
    have key : (eF (hW1 z).2).ofLp ≠ 0 ↔ (hW1 z).2 ≠ 0 := by
      constructor
      · intro h h0
        apply h
        rw [h0, map_zero]
        rfl
      · intro h h0
        apply h
        exact (ContinuousLinearEquiv.map_eq_zero_iff eF).mp
          ((WithLp.ofLp_eq_zero (p := 2)).mp h0)
    exact key.symm
  -- relative cohomology is invariant under the homeomorphism of pairs
  obtain ⟨iso⟩ := Work.Cohomology.relCohomology_homeomorph_pairs
    {y : ↥(Z.proj ⁻¹' W) | (y : Z.TotalSpace) ∈ zeroComplement Z}
    {p : ↥W × (Fin (Module.finrank ℝ F) → ℝ) | (p.2 : Fin (Module.finrank ℝ F) → ℝ) ≠ 0}
    e hiff m
  exact Work.Cohomology.subsingleton_of_iso iso.symm (hEuc (Module.finrank ℝ F) ↥W m hm)

/-- **Vanishing of the relative cohomology of a bundle piece below the rank, for an arbitrary
finite-dimensional fibre.**  For a real vector bundle `Z` with model fibre `F` and a set `W ⊆ B`
contained in a single chart `i` of the bundle, the relative cohomology of the piece of the Thom
pair over `W`, `Work.Thom.PieceCoh Z W m = H^m(X|_W, X|_W ∖ 0)`, vanishes for
`m < finrank ℝ F`. -/
theorem subsingleton_PieceCoh_genFibreGen {B : Type} [TopologicalSpace B]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {ι : Type} [Inhabited ι] (Z : RealBundle B F ι) (i : ι)
    {W : Set B} (hW : W ⊆ Z.baseSet i) {m : ℕ} (hm : m < Module.finrank ℝ F) :
    Subsingleton (PieceCoh Z W m) :=
  subsingleton_PieceCoh_genFibreAux
    (fun n W _ m hm => subsingleton_relComplex_euclidean_punctured
      (fun n W _ m hm => subsingleton_relComplex_cube n W m hm) n W m hm)
    ι Z i hW hm

/-! ## The global vanishing for an arbitrary fibre -/

theorem subsingleton_OpenThom_genFibre {B : Type} [TopologicalSpace B]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {ι : Type} (Z : RealBundle B F ι) (m : ℕ)
    (hm : m < Module.finrank ℝ F) :
    Subsingleton (OpenThom Z m) := by
  classical
  obtain ⟨inst, hwf⟩ := exists_wellFoundedLT ι
  letI : LinearOrder ι := inst
  haveI : WellFoundedLT ι := hwf
  -- the cumulative pieces of the cover, at the level of the base and of the total space
  let Q : ι → Set B := fun i => ⋃ β ≤ i, Z.baseSet β
  let P : ι → Set B := fun i => ⋃ β < i, Z.baseSet β
  let Cov : ι → Set Z.TotalSpace := fun i => Z.proj ⁻¹' (Q i)
  -- `Q i = P i ∪ baseSet i`
  have hQP : ∀ i, Q i = P i ∪ Z.baseSet i := by
    intro i
    ext x
    simp only [Q, P, Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro ⟨β, hβ, hx⟩
      rcases lt_or_eq_of_le hβ with h | h
      · exact Or.inl ⟨β, h, hx⟩
      · exact Or.inr (h ▸ hx)
    · rintro (⟨β, hβ, hx⟩ | hx)
      · exact ⟨β, le_of_lt hβ, hx⟩
      · exact ⟨i, le_rfl, hx⟩
  -- `P i = ⋃ β < i, Q β`
  have hPQ : ∀ i, P i = ⋃ β < i, Q β := by
    intro i
    ext x
    simp only [P, Q, Set.mem_iUnion]
    constructor
    · rintro ⟨β, hβ, hx⟩
      exact ⟨β, hβ, β, le_rfl, hx⟩
    · rintro ⟨β, hβ, γ, hγ, hx⟩
      exact ⟨γ, lt_of_le_of_lt hγ hβ, hx⟩
  have hCovopen : ∀ i, IsOpen (Cov i) := by
    intro i
    exact (isOpen_iUnion fun β => isOpen_iUnion fun _ : β ≤ i => Z.isOpen_baseSet β).preimage
      Z.continuous_proj
  have hCovmono : Monotone Cov := by
    intro i j hij x hx
    simp only [Cov, Q, Set.mem_preimage, Set.mem_iUnion] at hx ⊢
    obtain ⟨β, hβ, hx⟩ := hx
    exact ⟨β, le_trans hβ hij, hx⟩
  -- the well-founded induction
  have key : ∀ i : ι, ∀ j ≤ m,
      Subsingleton (Work.Cohomology.pdCohSub (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Cov i) j) := by
    intro i
    refine WellFoundedLT.induction (motive := fun i : ι => ∀ j ≤ m,
      Subsingleton (Work.Cohomology.pdCohSub (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Cov i) j)) i ?_
    intro i ih j hj
    -- the union of the pieces of the smaller indices is the piece over `P i`
    have hPQ2 : (⋃ k : ↥(Set.Iio i), Q k.1) = P i := by
      ext x
      simp only [P, Q, Set.mem_iUnion]
      constructor
      · rintro ⟨k, β, hβ, hx⟩
        exact ⟨β, lt_of_le_of_lt hβ k.2, hx⟩
      · rintro ⟨β, hβ, hx⟩
        exact ⟨⟨β, hβ⟩, β, le_rfl, hx⟩
    have hprev_eq : (⋃ k : ↥(Set.Iio i), Cov k.1) = Z.proj ⁻¹' (P i) := by
      have h1 : (⋃ k : ↥(Set.Iio i), Cov k.1)
          = ⋃ k : ↥(Set.Iio i), Z.proj ⁻¹' (Q k.1) := rfl
      rw [h1, ← Set.preimage_iUnion, hPQ2]
    -- the transfinite union step on the smaller pieces
    have hlim := Work.Cohomology.subsingleton_pdCohSub_iUnion_of_wf (zeroComplement Z)
      (fun k : ↥(Set.Iio i) => Cov k.1) (fun k => hCovopen k.1)
      (fun a b hab => hCovmono hab) m (fun k j hj => ih k.1 k.2 j hj)
    have hUj : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of Z.TotalSpace)
        (zeroComplement Z) (Z.proj ⁻¹' (P i)) j) := hprev_eq ▸ hlim j hj
    -- the two-piece Mayer–Vietoris step, adding the chart `i`
    refine Work.Cohomology.subsingleton_pdCohSub_union (zeroComplement Z)
      (W := Cov i) (U := Z.proj ⁻¹' (P i)) (V := Z.proj ⁻¹' (Z.baseSet i))
      (hCovopen i) ?_ ?_ ?_ ?_ ?_ j hUj ?_ ?_
    · exact (isOpen_iUnion fun β => isOpen_iUnion fun _ : β < i => Z.isOpen_baseSet β).preimage
        Z.continuous_proj
    · exact (Z.isOpen_baseSet i).preimage Z.continuous_proj
    · refine Set.preimage_mono fun x hx => ?_
      simp only [P, Q, Set.mem_iUnion] at hx ⊢
      obtain ⟨β, hβ, hx⟩ := hx
      exact ⟨β, le_of_lt hβ, hx⟩
    · refine Set.preimage_mono fun x hx => ?_
      simp only [Q, Set.mem_iUnion]
      exact ⟨i, le_rfl, hx⟩
    · rw [← Set.preimage_union, ← hQP i]
    · haveI : Inhabited ι := ⟨i⟩
      exact subsingleton_PieceCoh_genFibreGen Z i (fun _ hx => hx) (by omega)
    · intro e he
      haveI : Inhabited ι := ⟨i⟩
      have hen : e < Module.finrank ℝ F := by omega
      have h1 : Subsingleton (PieceCoh Z (P i ∩ Z.baseSet i) e) :=
        subsingleton_PieceCoh_genFibreGen Z i (fun x hx => hx.2) hen
      simpa only [Set.preimage_inter, PieceCoh] using h1
  -- the whole base is the union of the cumulative pieces
  have huniv : (⋃ i : ι, Cov i) = Set.univ := by
    have hQB : (⋃ i : ι, Q i) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      refine Set.mem_iUnion.mpr ⟨Z.indexAt x, ?_⟩
      simp only [Q, Set.mem_iUnion] at *
      exact ⟨Z.indexAt x, le_rfl, Z.mem_baseSet_at x⟩
    have h1 : (⋃ i : ι, Cov i) = Z.proj ⁻¹' (⋃ i : ι, Q i) := (Set.preimage_iUnion).symm
    rw [h1, hQB, Set.preimage_univ]
  -- the transfinite union step over the whole index set
  have hfin := Work.Cohomology.subsingleton_pdCohSub_iUnion_of_wf (zeroComplement Z) Cov
    hCovopen hCovmono m (fun i j hj => key i j hj)
  have hsub : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of Z.TotalSpace)
      (zeroComplement Z) Set.univ m) := huniv ▸ hfin m le_rfl
  exact subsingleton_pdCoh_of_subsingleton_pdCohSub_univ (zeroComplement Z) m hsub

/-- The projection of the complement of the zero section is an isomorphism in low degrees,
for an arbitrary finite-dimensional fibre.  See the module docstring. -/
theorem bijective_proj_zeroComplement_gen
    {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {ι : Type} {n k : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (hF : Module.finrank ℝ F = n)
    (T : Work.Thom.ThomClass Z n) (hk : k + 2 ≤ n) :
    Function.Bijective
      ((Work.Thom.CohMap ((Work.Thom.bundleProj Z).comp
        (Work.Thom.subtypeMap (Work.Thom.zeroComplement Z))) ℤ k).hom) := by
  -- the target map is `gysinπ Z k`
  have hcomp : (CohMap ((bundleProj Z).comp (subtypeMap (zeroComplement Z))) ℤ k).hom
      = gysinπ Z k := by
    rw [CohMap_comp (subtypeMap (zeroComplement Z)) (bundleProj Z) ℤ k]
    rfl
  rw [hcomp]
  -- `π^* : H^k(B;ℤ) → H^k(E;ℤ)` is bijective
  have hπ := bijective_CohMap_bundleProj Z k
  -- the low-degree vanishing of the Thom pair
  have hrel : (relToAbs ℤ (zeroComplement Z) k).hom = 0 := by
    haveI : Subsingleton (OpenThom Z k) :=
      subsingleton_OpenThom_genFibre Z k (by omega)
    refine LinearMap.ext fun x => ?_
    have hx : x = 0 := Subsingleton.elim x 0
    show (relToAbs ℤ (zeroComplement Z) k).hom x = 0
    rw [hx]
    exact map_zero _
  have hδ : (pairδC (zeroComplement Z) k).hom = 0 := by
    haveI : Subsingleton (OpenThom Z (k + 1)) :=
      subsingleton_OpenThom_genFibre Z (k + 1) (by omega)
    refine LinearMap.ext fun x => ?_
    exact Subsingleton.elim _ _
  constructor
  · -- injectivity: `ker (restrCoh_k) = range (relToAbs_k) = 0`
    intro x y hxy
    have h1 : gysinπ Z k (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h1' : (restrCoh (zeroComplement Z) ℤ k).hom
        ((CohMap (bundleProj Z) ℤ k).hom (x - y)) = 0 := h1
    have h3 : (CohMap (bundleProj Z) ℤ k).hom (x - y) ∈
        (relToAbs ℤ (zeroComplement Z) k).hom.range := by
      rw [pairRange_eq_ker₂ (zeroComplement Z) k]
      exact h1'
    rw [hrel, LinearMap.range_zero] at h3
    have h4 : (CohMap (bundleProj Z) ℤ k).hom (x - y) = 0 := by simpa using h3
    exact sub_eq_zero.mp (hπ.1 (by rw [h4, map_zero]))
  · -- surjectivity: `range (restrCoh_k) = ker (pairδ_k) = ⊤`
    intro y
    have hy : y ∈ (restrCoh (zeroComplement Z) ℤ k).hom.range := by
      rw [pairRange_eq_ker₃ (zeroComplement Z) k, hδ, LinearMap.ker_zero]
      exact Submodule.mem_top
    obtain ⟨w, hw⟩ := hy
    obtain ⟨z, hz⟩ := hπ.2 w
    exact ⟨z, by
      show (restrCoh (zeroComplement Z) ℤ k).hom
        ((CohMap (bundleProj Z) ℤ k).hom z) = y
      rw [hz, hw]⟩


end

end Work.Thom
