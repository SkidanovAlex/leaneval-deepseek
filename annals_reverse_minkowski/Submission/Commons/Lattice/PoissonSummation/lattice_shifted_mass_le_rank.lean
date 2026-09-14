import Mathlib
import Submission.Commons.Lattice.PoissonSummation.lattice_shifted_mass_le

namespace Commons.Lattice.PoissonSummation

open scoped BigOperators
open Module
set_option autoImplicit false

noncomputable section

/-- Ambient space `EuclideanSpace ℝ (Fin n)`. -/
abbrev lsmE (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Real span of a `ℤ`-submodule of `E n`. -/
abbrev lsmSpan (n : ℕ) (ℒ : Submodule ℤ (lsmE n)) : Submodule ℝ (lsmE n) :=
  Submodule.span ℝ (ℒ : Set (lsmE n))

/-- Dimension of the real span. -/
abbrev lsmDim (n : ℕ) (ℒ : Submodule ℤ (lsmE n)) : ℕ := finrank ℝ (lsmSpan n ℒ)

/-- The coordinate space `EuclideanSpace ℝ (Fin (lsmDim ℒ))` isomorphic to the span. -/
abbrev lsmCoord (n : ℕ) (ℒ : Submodule ℤ (lsmE n)) := EuclideanSpace ℝ (Fin (lsmDim n ℒ))

/-- The canonical isometry from the real span onto the coordinate space. -/
abbrev lsmIso (n : ℕ) (ℒ : Submodule ℤ (lsmE n)) :
    lsmSpan n ℒ ≃ₗᵢ[ℝ] lsmCoord n ℒ :=
  (stdOrthonormalBasis ℝ (lsmSpan n ℒ)).repr

/-- The real-linear map `lsmCoord ℒ →ₗ E n` sending the transported coordinates back to the
ambient space (the isometry inverse followed by the inclusion of the span). -/
abbrev lsmToAmb (n : ℕ) (ℒ : Submodule ℤ (lsmE n)) : lsmCoord n ℒ →ₗ[ℝ] lsmE n :=
  (Submodule.subtype (lsmSpan n ℒ)).comp (lsmIso n ℒ).symm.toLinearMap

lemma lsmToAmb_injective {n : ℕ} (ℒ : Submodule ℤ (lsmE n)) : Function.Injective (lsmToAmb n ℒ) := by
  unfold lsmToAmb
  change Function.Injective (fun x : lsmCoord n ℒ => (((lsmIso n ℒ).symm x : lsmSpan n ℒ) : lsmE n))
  exact Function.Injective.comp Subtype.coe_injective (LinearIsometryEquiv.injective (lsmIso n ℒ).symm)

lemma lsmToAmb_continuous {n : ℕ} (ℒ : Submodule ℤ (lsmE n)) : Continuous (lsmToAmb n ℒ) := by
  unfold lsmToAmb
  change Continuous (fun x : lsmCoord n ℒ => (((lsmIso n ℒ).symm x : lsmSpan n ℒ) : lsmE n))
  have h1 : Continuous (fun x : lsmCoord n ℒ => ((lsmIso n ℒ).symm x : lsmSpan n ℒ)) :=
    (lsmIso n ℒ).symm.continuous
  have h2 : Continuous (fun y : lsmSpan n ℒ => (y : lsmE n)) := continuous_subtype_val
  exact h2.comp h1

/-- The transported lattice in the coordinate space: the preimage of `ℒ` under `lsmToAmb`. -/
def lsmLift (n : ℕ) (ℒ : Submodule ℤ (lsmE n)) : Submodule ℤ (lsmCoord n ℒ) where
  carrier := (lsmToAmb n ℒ) ⁻¹' (ℒ : Set (lsmE n))
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_preimage, SetLike.mem_coe] at ha hb ⊢
    rw [map_add]
    exact Submodule.add_mem ℒ ha hb
  smul_mem' := by
    intro z a ha
    simp only [Set.mem_preimage, SetLike.mem_coe] at ha ⊢
    rw [map_zsmul]
    exact Submodule.smul_mem ℒ z ha

instance lsmLift_discrete (n : ℕ) (ℒ : Submodule ℤ (lsmE n)) [DiscreteTopology ℒ] :
    DiscreteTopology (lsmLift n ℒ) := by
  let s : Set (lsmCoord n ℒ) := (lsmToAmb n ℒ) ⁻¹' (ℒ : Set (lsmE n))
  have hDs : DiscreteTopology (s : Set (lsmCoord n ℒ)) := by
    simpa [s] using (DiscreteTopology.preimage_of_continuous_injective
      (s := (ℒ : Set (lsmE n))) (f := lsmToAmb n ℒ) (lsmToAmb_continuous ℒ) (lsmToAmb_injective ℒ))
  have hts : (lsmLift n ℒ : Set (lsmCoord n ℒ)) ⊆ s := by
    intro x hx
    exact hx
  have hDl : DiscreteTopology ((lsmLift n ℒ : Set (lsmCoord n ℒ))) :=
    DiscreteTopology.of_subset (s := s) (t := (lsmLift n ℒ : Set (lsmCoord n ℒ))) hDs hts
  simpa using hDl

lemma lsmToAmb_range {n : ℕ} (ℒ : Submodule ℤ (lsmE n)) :
    (lsmToAmb n ℒ).range = lsmSpan n ℒ := by
  unfold lsmToAmb
  rw [LinearMap.range_comp]
  rw [show ((lsmIso n ℒ).symm.toLinearMap).range = ⊤ by
    exact LinearMap.range_eq_top.mpr (LinearEquiv.surjective (lsmIso n ℒ).symm.toLinearEquiv)]
  simp

instance lsmLift_isZLattice (n : ℕ) (ℒ : Submodule ℤ (lsmE n)) [DiscreteTopology ℒ] :
    IsZLattice ℝ (lsmLift n ℒ) where
  span_top := by
    classical
    have hinj : Function.Injective (lsmToAmb n ℒ) := lsmToAmb_injective ℒ
    have himg : (lsmToAmb n ℒ) '' (lsmLift n ℒ : Set (lsmCoord n ℒ)) = (ℒ : Set (lsmE n)) := by
      change (lsmToAmb n ℒ) '' ((lsmToAmb n ℒ) ⁻¹' (ℒ : Set (lsmE n))) = (ℒ : Set (lsmE n))
      rw [Set.image_preimage_eq_range_inter]
      have hsub : (ℒ : Set (lsmE n)) ⊆ Set.range (lsmToAmb n ℒ) := by
        intro x hx
        refine ⟨(lsmIso n ℒ) ⟨x, Submodule.subset_span hx⟩, ?_⟩
        simp [lsmToAmb]
      rw [Set.inter_comm, Set.inter_eq_left.mpr hsub]
    have hmapinj : Function.Injective (Submodule.map (R := ℝ) (R₂ := ℝ) (lsmToAmb n ℒ)) :=
      Submodule.map_injective_of_injective hinj
    apply hmapinj.eq_iff.mp
    change Submodule.map (lsmToAmb n ℒ) (Submodule.span ℝ (lsmLift n ℒ : Set (lsmCoord n ℒ))) =
      Submodule.map (lsmToAmb n ℒ) ⊤
    rw [Submodule.map_span, himg, Submodule.map_top, lsmToAmb_range]

lemma lsmLift_mem {n : ℕ} (ℒ : Submodule ℤ (lsmE n)) (z : lsmCoord n ℒ) :
    z ∈ lsmLift n ℒ ↔ (lsmToAmb n ℒ) z ∈ (ℒ : Set (lsmE n)) := by
  rfl

lemma lsmLift_finrank {n : ℕ} (ℒ : Submodule ℤ (lsmE n)) [DiscreteTopology ℒ] :
    finrank ℤ (lsmLift n ℒ) = lsmDim n ℒ := by
  rw [ZLattice.rank ℝ (lsmLift n ℒ)]
  dsimp [lsmDim, lsmCoord]
  rw [finrank_euclideanSpace]
  simp

/-- A `ℤ`-basis of the transported lattice indexed by `Fin (lsmDim ℒ)`. -/
def lsmLiftBasis {n : ℕ} (ℒ : Submodule ℤ (lsmE n)) [DiscreteTopology ℒ] :
    Basis (Fin (lsmDim n ℒ)) ℤ (lsmLift n ℒ) := by
  classical
  letI : Module.Free ℤ (lsmLift n ℒ) := ZLattice.module_free ℝ (lsmLift n ℒ)
  letI : Module.Finite ℤ (lsmLift n ℒ) := ZLattice.module_finite ℝ (lsmLift n ℒ)
  let ρ : Fin (finrank ℤ (lsmLift n ℒ)) ≃ Fin (lsmDim n ℒ) :=
    Equiv.cast (congrArg Fin (lsmLift_finrank ℒ))
  exact (Module.finBasis ℤ (lsmLift n ℒ)).reindex ρ

/-- The coordinate matrix of the transported lattice in the canonical coordinates. -/
def lsmLiftCoordMatrix {n : ℕ} (ℒ : Submodule ℤ (lsmE n)) [DiscreteTopology ℒ] :
    Matrix (Fin (lsmDim n ℒ)) (Fin (lsmDim n ℒ)) ℝ :=
  fun i j => ((((lsmLiftBasis ℒ) j : lsmLift n ℒ) : lsmCoord n ℒ) i)

lemma lsmLift_coordMatrix_apply {n : ℕ} (ℒ : Submodule ℤ (lsmE n)) [DiscreteTopology ℒ]
    (i j : Fin (lsmDim n ℒ)) :
    ((((lsmLiftBasis ℒ) j : lsmLift n ℒ) : lsmCoord n ℒ) i) = lsmLiftCoordMatrix ℒ i j := by
  rfl

lemma lsmLift_coordMatrix_det_ne_zero {n : ℕ} (ℒ : Submodule ℤ (lsmE n)) [DiscreteTopology ℒ] :
    (lsmLiftCoordMatrix ℒ).det ≠ 0 := by
  classical
  let d := lsmDim n ℒ
  let C : Basis (Fin d) ℝ (lsmCoord n ℒ) := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  let R : Basis (Fin d) ℝ (lsmCoord n ℒ) :=
    (lsmLiftBasis ℒ).ofZLatticeBasis ℝ (lsmLift n ℒ)
  have hAeq : lsmLiftCoordMatrix ℒ = C.toMatrix (fun j : Fin d => (R j : lsmCoord n ℒ)) := by
    ext i j
    rw [lsmLiftCoordMatrix]
    dsimp [C, R]
    rw [Basis.toMatrix_apply]
    rw [Module.Basis.ofZLatticeBasis_apply]
    rfl
  have hdetC : (C.toMatrix (fun j : Fin d => (R j : lsmCoord n ℒ))).det ≠ 0 := by
    have hflip := Module.Basis.toMatrix_mul_toMatrix_flip C R
    exact Matrix.det_ne_zero_of_right_inverse hflip
  rw [hAeq]
  exact hdetC


/-- The type equivalence between the original lattice and its transported copy in the
coordinate space, sending `y : ℒ` to its image under the isometry of the real span. -/
noncomputable def lsmLiftEquiv {n : ℕ} (ℒ : Submodule ℤ (lsmE n)) [DiscreteTopology ℒ] :
    ℒ ≃ lsmLift n ℒ where
  toFun := fun y =>
    ⟨(lsmIso n ℒ) ⟨(y : lsmE n), (Submodule.subset_span (y : ℒ).2)⟩, by
      rw [lsmLift_mem]
      simp [lsmToAmb]⟩
  invFun := fun z => by
    rcases z with ⟨z, hz⟩
    refine ⟨(lsmToAmb n ℒ) z, ?_⟩
    rw [lsmLift_mem] at hz
    exact hz
  left_inv := by
    intro y
    apply Subtype.ext
    simp [lsmToAmb]
  right_inv := by
    intro z
    apply Subtype.ext
    simp [lsmToAmb]

lemma lsmLiftEquiv_apply {n : ℕ} (ℒ : Submodule ℤ (lsmE n)) [DiscreteTopology ℒ] (y : ℒ) :
    ((lsmLiftEquiv ℒ y : lsmLift n ℒ) : lsmCoord n ℒ) =
      (lsmIso n ℒ) ⟨(y : lsmE n), (Submodule.subset_span (y : ℒ).2)⟩ := by
  rfl

lemma lsmLiftEquiv_norm {n : ℕ} (ℒ : Submodule ℤ (lsmE n)) [DiscreteTopology ℒ] (y : ℒ) :
    ‖((lsmLiftEquiv ℒ y : lsmLift n ℒ) : lsmCoord n ℒ)‖ = ‖(y : lsmE n)‖ := by
  rw [lsmLiftEquiv_apply]
  have hnorm := (lsmIso n ℒ).norm_map ⟨(y : lsmE n), (Submodule.subset_span (y : ℒ).2)⟩
  simp [hnorm]

lemma lsmLiftEquiv_norm_sub {n : ℕ} (ℒ : Submodule ℤ (lsmE n)) [DiscreteTopology ℒ]
    (y : ℒ) (u : lsmE n) (hu : u ∈ lsmSpan n ℒ) :
    ‖((lsmLiftEquiv ℒ y : lsmLift n ℒ) : lsmCoord n ℒ) - (lsmIso n ℒ) ⟨u, hu⟩‖ =
      ‖(y : lsmE n) - u‖ := by
  rw [lsmLiftEquiv_apply]
  have hnorm := (lsmIso n ℒ).norm_map
    (⟨(y : lsmE n), (Submodule.subset_span (y : ℒ).2)⟩ - ⟨u, hu⟩)
  rw [← (lsmIso n ℒ).map_sub]
  simpa using hnorm


lemma lsmLift_tsum_eq {n : ℕ} (ℒ : Submodule ℤ (lsmE n)) [DiscreteTopology ℒ] (s : ℝ) :
    (∑' y : ℒ, Real.exp (-Real.pi * ‖(y : lsmE n)‖ ^ 2 / s ^ 2)) =
      (∑' z : lsmLift n ℒ,
        Real.exp (-Real.pi * ‖(z : lsmCoord n ℒ)‖ ^ 2 / s ^ 2)) := by
  classical
  let e := lsmLiftEquiv ℒ
  have h1 : (∑' y : ℒ, Real.exp (-Real.pi * ‖(y : lsmE n)‖ ^ 2 / s ^ 2)) =
      ∑' y : ℒ, Real.exp (-Real.pi * ‖((e y : lsmLift n ℒ) : lsmCoord n ℒ)‖ ^ 2 / s ^ 2) := by
    apply tsum_congr
    intro y
    congr 1
    rw [lsmLiftEquiv_norm ℒ y]
  calc
    (∑' y : ℒ, Real.exp (-Real.pi * ‖(y : lsmE n)‖ ^ 2 / s ^ 2))
        = ∑' y : ℒ, Real.exp (-Real.pi * ‖((e y : lsmLift n ℒ) : lsmCoord n ℒ)‖ ^ 2 / s ^ 2) := h1
    _ = ∑' z : lsmLift n ℒ, Real.exp (-Real.pi * ‖(z : lsmCoord n ℒ)‖ ^ 2 / s ^ 2) := by
        exact Equiv.tsum_eq e (fun z : lsmLift n ℒ =>
          Real.exp (-Real.pi * ‖(z : lsmCoord n ℒ)‖ ^ 2 / s ^ 2))

lemma lsmLift_tsum_shifted_eq {n : ℕ} (ℒ : Submodule ℤ (lsmE n)) [DiscreteTopology ℒ]
    (s : ℝ) (u : lsmE n) (hu : u ∈ lsmSpan n ℒ) :
    (∑' y : ℒ, Real.exp (-Real.pi * ‖(y : lsmE n) - u‖ ^ 2 / s ^ 2)) =
      (∑' z : lsmLift n ℒ,
        Real.exp (-Real.pi * ‖(z : lsmCoord n ℒ) - (lsmIso n ℒ) ⟨u, hu⟩‖ ^ 2 / s ^ 2)) := by
  classical
  let e := lsmLiftEquiv ℒ
  have h1 : (∑' y : ℒ, Real.exp (-Real.pi * ‖(y : lsmE n) - u‖ ^ 2 / s ^ 2)) =
      ∑' y : ℒ, Real.exp (-Real.pi * ‖((e y : lsmLift n ℒ) : lsmCoord n ℒ) - (lsmIso n ℒ) ⟨u, hu⟩‖ ^ 2 / s ^ 2) := by
    apply tsum_congr
    intro y
    congr 1
    rw [lsmLiftEquiv_norm_sub ℒ y u hu]
  calc
    (∑' y : ℒ, Real.exp (-Real.pi * ‖(y : lsmE n) - u‖ ^ 2 / s ^ 2))
        = ∑' y : ℒ, Real.exp (-Real.pi * ‖((e y : lsmLift n ℒ) : lsmCoord n ℒ) - (lsmIso n ℒ) ⟨u, hu⟩‖ ^ 2 / s ^ 2) := h1
    _ = ∑' z : lsmLift n ℒ,
        Real.exp (-Real.pi * ‖(z : lsmCoord n ℒ) - (lsmIso n ℒ) ⟨u, hu⟩‖ ^ 2 / s ^ 2) := by
        exact Equiv.tsum_eq e (fun z : lsmLift n ℒ =>
          Real.exp (-Real.pi * ‖(z : lsmCoord n ℒ) - (lsmIso n ℒ) ⟨u, hu⟩‖ ^ 2 / s ^ 2))

/- Rank-generic Banaszczyk shifted mass (paper Claim 2.7): for ANY discrete Z-lattice
ℒ ≤ EuclideanSpace ℝ (Fin n) (not nec. full-rank) and a shift u in the real span of ℒ,
the shifted Gaussian mass of ℒ is at most its unshifted mass.  Route: view ℒ as a
full-rank lattice in its real span S (stdOrthonormalBasis ℝ S, repr : S ≃ₗᵢ E_d with
d = finrank ℝ S), transport to E_d, apply the full-rank
Commons.Lattice.PoissonSummation.lattice_shifted_mass_le (identity coordinate matrix),
and transport back (all sums equal under the isometry; Equiv.tsum_eq for the type
equivalences).  Module.Free comes from instModuleFree_of_discrete_submodule; IsZLattice
of the transported lattice from span = ⊤. -/
theorem lattice_shifted_mass_le_rank {n : ℕ} (ℒ : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology ℒ] (s : ℝ) (hs : 0 < s) (u : EuclideanSpace ℝ (Fin n))
    (hu : u ∈ Submodule.span ℝ (ℒ : Set (EuclideanSpace ℝ (Fin n)))) :
    (∑' y : ℒ, Real.exp (-Real.pi * ‖(y : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / s ^ 2)) ≤
      (∑' y : ℒ, Real.exp (-Real.pi * ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 / s ^ 2)) := by
  classical
  let ℒ₀ : Submodule ℤ (lsmCoord n ℒ) := lsmLift n ℒ
  have hu' : u ∈ lsmSpan n ℒ := by
    simpa [lsmSpan] using hu
  have hshift :
      (∑' y : ℒ, Real.exp (-Real.pi * ‖(y : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / s ^ 2)) =
        (∑' z : ℒ₀,
          Real.exp (-Real.pi * ‖(z : lsmCoord n ℒ) - (lsmIso n ℒ) ⟨u, hu'⟩‖ ^ 2 / s ^ 2)) := by
    simpa [ℒ₀] using (lsmLift_tsum_shifted_eq (n := n) ℒ s u hu')
  have hunshift :
      (∑' y : ℒ, Real.exp (-Real.pi * ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 / s ^ 2)) =
        (∑' z : ℒ₀, Real.exp (-Real.pi * ‖(z : lsmCoord n ℒ)‖ ^ 2 / s ^ 2)) := by
    simpa [ℒ₀] using (lsmLift_tsum_eq (n := n) ℒ s)
  have hle :
      (∑' z : ℒ₀,
        Real.exp (-Real.pi * ‖(z : lsmCoord n ℒ) - (lsmIso n ℒ) ⟨u, hu'⟩‖ ^ 2 / s ^ 2)) ≤
        (∑' z : ℒ₀, Real.exp (-Real.pi * ‖(z : lsmCoord n ℒ)‖ ^ 2 / s ^ 2)) := by
    have hfull := Commons.Lattice.PoissonSummation.lattice_shifted_mass_le
      (n := lsmDim n ℒ) (ℒ := ℒ₀) (b := lsmLiftBasis ℒ) (A := lsmLiftCoordMatrix ℒ)
      (hA := lsmLift_coordMatrix_det_ne_zero ℒ)
      (hAcoords := by
        intro i j
        rfl)
      s hs ((lsmIso n ℒ) ⟨u, hu'⟩)
    simpa [ℒ₀] using hfull
  calc
    (∑' y : ℒ, Real.exp (-Real.pi * ‖(y : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / s ^ 2))
        = (∑' z : ℒ₀,
            Real.exp (-Real.pi * ‖(z : lsmCoord n ℒ) - (lsmIso n ℒ) ⟨u, hu'⟩‖ ^ 2 / s ^ 2)) := hshift
    _ ≤ (∑' z : ℒ₀, Real.exp (-Real.pi * ‖(z : lsmCoord n ℒ)‖ ^ 2 / s ^ 2)) := hle
    _ = (∑' y : ℒ, Real.exp (-Real.pi * ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 / s ^ 2)) := hunshift.symm

end

end Commons.Lattice.PoissonSummation
