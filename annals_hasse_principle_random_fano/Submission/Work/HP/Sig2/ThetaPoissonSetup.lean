import Mathlib
import Submission.Work.HP.Sig2.ThetaDefs

/-!
# Lattice coordinates and Gram matrices for the theta Poisson identity

Setup for the proof of `Work.HP.Sig2.theta_lower`.  For a discrete `ℤ`-submodule
`Λ ⊆ ι → ℝ` (`ι` finite) we fix a `ℤ`-basis `latBasis Λ` of `Λ`, view its vectors in the
ambient space (`latCoe`), and introduce

* `latMap Λ`: the `ℝ`-linear map `x ↦ ∑ i, x i • latCoe Λ i`, whose range is `span ℝ Λ`;
* `latGram Λ i j = ⟪latCoe Λ i, latCoe Λ j⟫`, the Gram matrix of the basis;
* `latDualMap Λ m = ∑ i, ((latGram Λ)⁻¹ *ᵥ m) i • latCoe Λ i`, a `ℤ`-indexed bijection
  `ℤ^κ ≃ dualLat Λ` with `‖latDualMap Λ m‖² = mᵀ (latGram Λ)⁻¹ m` and
  `⟪latDualMap Λ m, latMap Λ x⟫ = m · x`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Module

namespace Work.HP.Sig2.ThetaPoisson

open Work.HP

variable {ι : Type*} [Fintype ι]

/-- The index type of the chosen `ℤ`-basis of `Λ`. -/
abbrev Idx (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] : Type _ :=
  Module.Free.ChooseBasisIndex ℤ Λ

/-- A `ℤ`-basis of a discrete lattice `Λ ⊆ ι → ℝ`. -/
noncomputable def latBasis (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] : Basis (Idx Λ) ℤ Λ :=
  Module.Free.chooseBasis ℤ Λ

/-- The basis vectors of `Λ`, viewed in the ambient space `ι → ℝ`. -/
noncomputable def latCoe (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] : Idx Λ → (ι → ℝ) :=
  fun i => ((latBasis Λ i : Λ) : ι → ℝ)

theorem span_latCoe (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] :
    Submodule.span ℤ (Set.range (latCoe Λ)) = Λ := by
  have h1 : Submodule.map (Submodule.subtype Λ) (Submodule.span ℤ (Set.range (latBasis Λ)))
      = Submodule.span ℤ (Set.range (latCoe Λ)) := by
    rw [Submodule.map_span]
    rw [← Set.range_comp]
    rfl
  calc Submodule.span ℤ (Set.range (latCoe Λ))
      = Submodule.map (Submodule.subtype Λ) (Submodule.span ℤ (Set.range (latBasis Λ))) := h1.symm
    _ = Submodule.map (Submodule.subtype Λ) ⊤ := by rw [(latBasis Λ).span_eq]
    _ = Λ := by rw [Submodule.map_top, Submodule.range_subtype]

theorem discreteTopology_span_latCoe (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] :
    DiscreteTopology (Submodule.span ℤ (Set.range (latCoe Λ))) := by
  rw [span_latCoe Λ]
  infer_instance

/-- The real span of the basis vectors is the real span of `Λ`. -/
theorem span_real_latCoe (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] :
    Submodule.span ℝ (Set.range (latCoe Λ)) = Submodule.span ℝ (Λ : Set (ι → ℝ)) := by
  rw [← Submodule.span_span_of_tower (R := ℤ) (S := ℝ) (Set.range (latCoe Λ)), span_latCoe Λ]

/-- The real dimension of the span of `Λ` is the `ℤ`-rank of `Λ`. -/
theorem finrank_span_latCoe (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (latCoe Λ))) = Fintype.card (Idx Λ) := by
  have h1 := Real.finrank_eq_int_finrank_of_discrete (E := ι → ℝ) (s := Set.range (latCoe Λ))
    (discreteTopology_span_latCoe Λ)
  simp only [Set.finrank] at h1
  rw [span_latCoe Λ] at h1
  rw [h1]
  exact Module.finrank_eq_card_chooseBasisIndex ℤ Λ

/-- The `ℝ`-linear coordinate map `x ↦ ∑ i, x i • latCoe Λ i`. -/
noncomputable def latMap (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] :
    (Idx Λ → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  Fintype.linearCombination ℝ (latCoe Λ)

theorem latMap_apply (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] (x : Idx Λ → ℝ) :
    latMap Λ x = ∑ i, x i • latCoe Λ i :=
  Fintype.linearCombination_apply ℝ _ x

theorem latMap_range (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] :
    (latMap Λ).range = Submodule.span ℝ (Set.range (latCoe Λ)) :=
  Fintype.range_linearCombination ℝ _

theorem latMap_injective (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] :
    Function.Injective (latMap Λ) := by
  rw [← LinearMap.ker_eq_bot]
  have hdim := LinearMap.finrank_range_add_finrank_ker (latMap Λ)
  rw [latMap_range Λ, finrank_span_latCoe Λ] at hdim
  have htop : Module.finrank ℝ (Idx Λ → ℝ) = Fintype.card (Idx Λ) := by
    rw [Module.finrank_fintype_fun_eq_card]
  rw [htop] at hdim
  have h0 : Module.finrank ℝ (LinearMap.ker (latMap Λ)) = 0 := by omega
  exact Submodule.finrank_eq_zero.mp h0

/-- The range of `latMap` is the real span of `Λ`. -/
theorem mem_range_latMap (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] {v : ι → ℝ} :
    v ∈ (latMap Λ).range ↔ v ∈ Submodule.span ℝ (Λ : Set (ι → ℝ)) := by
  rw [latMap_range, span_real_latCoe]

/-- The coordinates of an element of `Λ` in the chosen basis, read in the ambient space. -/
theorem latMap_equivFun (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] (m : Idx Λ → ℤ) :
    ((latBasis Λ).equivFun.symm m : ι → ℝ) = latMap Λ (fun i => (m i : ℝ)) := by
  rw [latMap, Fintype.linearCombination_apply, Basis.equivFun_symm_apply, Submodule.coe_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Submodule.coe_smul, Int.cast_smul_eq_zsmul]
    rfl

/-- The coordinate vector of an element of `Λ` is an integral combination of the basis. -/
theorem latMap_int_mem (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] (m : Idx Λ → ℤ) :
    latMap Λ (fun i => (m i : ℝ)) ∈ Λ := by
  rw [← latMap_equivFun Λ m]
  exact ((latBasis Λ).equivFun.symm m).2

/-- `latCoe Λ j = latMap Λ (Pi.single j 1)`. -/
theorem latMap_single (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] (j : Idx Λ) :
    latMap Λ (Pi.single j (1 : ℝ)) = latCoe Λ j := by
  rw [latMap_apply, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb]
    simp
  · intro h
    exact absurd (Finset.mem_univ j) h

/-! ## `dotR` calculus -/

lemma dotR_comm' (v w : ι → ℝ) : dotR v w = dotR w v := by
  simp only [dotR]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma dotR_smul_left' (c : ℝ) (v w : ι → ℝ) : dotR (c • v) w = c * dotR v w := by
  simp only [dotR, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma dotR_smul_right' (c : ℝ) (v w : ι → ℝ) : dotR v (c • w) = c * dotR v w := by
  simp only [dotR, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma dotR_sum_left' {κ : Type*} [Fintype κ] (f : κ → ι → ℝ) (w : ι → ℝ) :
    dotR (∑ i, f i) w = ∑ i, dotR (f i) w := by
  simp only [dotR, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

lemma dotR_sum_right' {κ : Type*} [Fintype κ] (v : ι → ℝ) (g : κ → ι → ℝ) :
    dotR v (∑ i, g i) = ∑ i, dotR v (g i) := by
  simp only [dotR, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

lemma rNorm_sq' (v : ι → ℝ) : rNorm v ^ 2 = dotR v v := by
  rw [rNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (v i)), dotR]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma rNorm_pos' {v : ι → ℝ} : 0 < rNorm v ↔ v ≠ 0 := by
  constructor
  · intro h hv
    rw [hv] at h
    simp [rNorm] at h
  · intro hv
    have h2 : rNorm v ^ 2 ≠ 0 := by
      intro h2
      apply hv
      rw [rNorm_sq'] at h2
      rw [dotR] at h2
      funext i
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (v i))).mp h2 i
        (Finset.mem_univ i)
      simpa using h3
    refine lt_of_le_of_ne (Real.sqrt_nonneg _) (fun h => h2 ?_)
    rw [← h]; ring

/-! ## The Gram matrix -/

/-- The Gram matrix of the chosen basis. -/
noncomputable def latGram (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] :
    Matrix (Idx Λ) (Idx Λ) ℝ :=
  Matrix.of fun i j => dotR (latCoe Λ i) (latCoe Λ j)

theorem dotR_latMap_mulVec (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ]
    (x y : Idx Λ → ℝ) :
    dotR (latMap Λ x) (latMap Λ y) = x ⬝ᵥ ((latGram Λ).mulVec y) := by
  have h1 : dotR (latMap Λ x) (latMap Λ y) = ∑ i, ∑ j, x i * y j * latGram Λ i j := by
    rw [latMap_apply, latMap_apply, dotR_sum_left']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dotR_sum_right']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dotR_smul_left', dotR_smul_right']
    simp only [latGram, Matrix.of_apply]
    ring
  rw [h1, show x ⬝ᵥ ((latGram Λ).mulVec y)
      = ∑ i, x i * (∑ j, (latGram Λ) i j * y j) from rfl]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem dotR_latMap (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] (x y : Idx Λ → ℝ) :
    dotR (latMap Λ x) (latMap Λ y) = ∑ i, ∑ j, x i * latGram Λ i j * y j := by
  rw [dotR_latMap_mulVec,
    show x ⬝ᵥ ((latGram Λ).mulVec y) = ∑ i, x i * (∑ j, (latGram Λ) i j * y j) from rfl]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `Pi.single j 1 ⬝ᵥ v = v j`. -/
lemma single_dotProduct {κ : Type*} [Fintype κ] [DecidableEq κ] (j : κ) (v : κ → ℝ) :
    Pi.single j (1 : ℝ) ⬝ᵥ v = v j := by
  simp only [dotProduct, Pi.single_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

theorem dotR_latCoe_latMap (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] (j : Idx Λ)
    (x : Idx Λ → ℝ) :
    dotR (latCoe Λ j) (latMap Λ x) = ((latGram Λ).mulVec x) j := by
  rw [← latMap_single Λ j, dotR_latMap_mulVec, single_dotProduct]

theorem latGram_symm (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] (i j : Idx Λ) :
    latGram Λ i j = latGram Λ j i := by
  simp only [latGram, Matrix.of_apply, dotR]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem latGram_transpose (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] :
    (latGram Λ).transpose = latGram Λ := by
  ext i j
  simp only [Matrix.transpose_apply]
  exact (latGram_symm Λ i j).symm

theorem latGram_quad (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] (x : Idx Λ → ℝ) :
    rNorm (latMap Λ x) ^ 2 = ∑ i, ∑ j, x i * latGram Λ i j * x j := by
  rw [rNorm_sq', dotR_latMap]

theorem latGram_posDef (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] :
    (latGram Λ).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · refine Matrix.IsHermitian.ext fun i j => ?_
    rw [star_trivial]
    exact latGram_symm Λ j i
  · intro x hx
    have hxl : latMap Λ x ≠ 0 := fun h => hx (latMap_injective Λ (by rw [h, map_zero]))
    rw [show star x ⬝ᵥ ((latGram Λ).mulVec x) = dotR (latMap Λ x) (latMap Λ x) from by
      rw [star_trivial, ← dotR_latMap_mulVec]]
    rw [← rNorm_sq']
    exact pow_pos (rNorm_pos'.mpr hxl) 2

theorem latGram_isUnit_det (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] :
    IsUnit (latGram Λ).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (latGram_posDef Λ).isUnit

theorem latGram_mul_inv (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] :
    latGram Λ * (latGram Λ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (latGram_isUnit_det Λ)

theorem latGram_inv_mul (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] :
    (latGram Λ)⁻¹ * latGram Λ = 1 :=
  Matrix.nonsing_inv_mul _ (latGram_isUnit_det Λ)

/-! ## The dual lattice coordinates -/

/-- The `ℤ^κ`-indexed map onto the dual lattice: `m ↦ ∑ i, ((latGram Λ)⁻¹ *ᵥ m) i • latCoe Λ i`. -/
noncomputable def latDualMap (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ]
    (m : Idx Λ → ℤ) : ι → ℝ :=
  latMap Λ ((latGram Λ)⁻¹.mulVec (fun i => (m i : ℝ)))

theorem latDualMap_def (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] (m : Idx Λ → ℤ) :
    latDualMap Λ m = latMap Λ ((latGram Λ)⁻¹.mulVec (fun i => (m i : ℝ))) := rfl

theorem latDualMap_apply (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] (m : Idx Λ → ℤ) :
    latDualMap Λ m = latMap Λ (fun i => ∑ j, (latGram Λ)⁻¹ i j * (m j : ℝ)) := rfl

theorem rNorm_latDualMap_sq (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] (m : Idx Λ → ℤ) :
    rNorm (latDualMap Λ m) ^ 2
      = ∑ i, ∑ j, (m i : ℝ) * (latGram Λ)⁻¹ i j * (m j : ℝ) := by
  rw [rNorm_sq', latDualMap, dotR_latMap_mulVec, Matrix.mulVec_mulVec, latGram_mul_inv,
    Matrix.one_mulVec, dotProduct_comm]
  rw [show (fun i => (m i : ℝ)) ⬝ᵥ ((latGram Λ)⁻¹.mulVec (fun i => (m i : ℝ)))
      = ∑ i, (m i : ℝ) * (∑ j, (latGram Λ)⁻¹ i j * (m j : ℝ)) from rfl]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem dotR_latDualMap_latMap (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ]
    (m : Idx Λ → ℤ) (x : Idx Λ → ℝ) :
    dotR (latDualMap Λ m) (latMap Λ x) = ∑ j, (m j : ℝ) * x j := by
  rw [latDualMap, dotR_latMap_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    latGram_transpose, Matrix.mulVec_mulVec, latGram_mul_inv, Matrix.one_mulVec]
  rw [show (fun i => (m i : ℝ)) ⬝ᵥ x = ∑ j, (m j : ℝ) * x j from rfl]

/-- The image of `latDualMap` lies in the dual lattice. -/
theorem latDualMap_mem_dualLat (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ]
    (m : Idx Λ → ℤ) : latDualMap Λ m ∈ dualLat Λ := by
  constructor
  · rw [← mem_range_latMap]
    exact ⟨_, rfl⟩
  · intro z hz
    have hz' : z = latMap Λ (fun i => (((latBasis Λ).equivFun ⟨z, hz⟩) i : ℝ)) := by
      rw [← latMap_equivFun Λ, LinearEquiv.symm_apply_apply]
    rw [hz']
    change ∃ k : ℤ,
      dotR (latDualMap Λ m) (latMap Λ fun i => (((latBasis Λ).equivFun ⟨z, hz⟩) i : ℝ)) = (k : ℝ)
    rw [dotR_latDualMap_latMap]
    exact ⟨∑ j, m j * (latBasis Λ).equivFun ⟨z, hz⟩ j, by push_cast; rfl⟩

theorem latDualMap_injective (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] :
    Function.Injective (latDualMap Λ) := by
  intro m m' h
  have hx : latMap Λ ((latGram Λ)⁻¹.mulVec (fun i => (m i : ℝ)))
      = latMap Λ ((latGram Λ)⁻¹.mulVec (fun i => (m' i : ℝ))) := h
  have hinj := latMap_injective Λ hx
  have hm : (fun i => (m i : ℝ)) = (fun i => (m' i : ℝ)) := by
    have := congrArg (fun v => (latGram Λ).mulVec v) hinj
    simpa [Matrix.mulVec_mulVec, latGram_mul_inv, Matrix.one_mulVec] using this
  funext i
  have := congrFun hm i
  exact_mod_cast this

theorem latDualMap_surjective (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] {w : ι → ℝ}
    (hw : w ∈ dualLat Λ) : ∃ m : Idx Λ → ℤ, latDualMap Λ m = w := by
  have hspan : w ∈ (latMap Λ).range := by
    rw [mem_range_latMap]; exact hw.1
  obtain ⟨x, hx⟩ := hspan
  have hint : ∀ j : Idx Λ, ∃ k : ℤ, dotR w (latCoe Λ j) = (k : ℝ) := by
    intro j
    obtain ⟨k, hk⟩ := hw.2 (latCoe Λ j) (latBasis Λ j).2
    exact ⟨k, by simpa [dotR] using hk⟩
  choose m hm using hint
  refine ⟨m, ?_⟩
  have hxeq : x = (latGram Λ)⁻¹.mulVec (fun i => (m i : ℝ)) := by
    conv_lhs => rw [← Matrix.one_mulVec x, ← latGram_inv_mul]
    rw [← Matrix.mulVec_mulVec]
    congr 1
    funext j
    rw [← dotR_latCoe_latMap Λ j x, hx, dotR_comm']
    exact hm j
  show latMap Λ ((latGram Λ)⁻¹.mulVec (fun i => (m i : ℝ))) = w
  rw [← hxeq, hx]

/-- The `ℤ^κ ≃ dualLat Λ` bijection `m ↦ ∑ i, ((latGram Λ)⁻¹ *ᵥ m) i • latCoe Λ i`. -/
noncomputable def latDualEquiv (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] :
    (Idx Λ → ℤ) ≃ dualLat Λ :=
  Equiv.ofBijective (fun m => (⟨latDualMap Λ m, latDualMap_mem_dualLat Λ m⟩ : dualLat Λ))
    ⟨fun m m' h => latDualMap_injective Λ (Subtype.ext_iff.mp h),
      fun w => let ⟨m, hm⟩ := latDualMap_surjective Λ w.2
        ⟨m, Subtype.ext hm⟩⟩

@[simp] theorem latDualEquiv_apply (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ]
    (m : Idx Λ → ℤ) :
    ((latDualEquiv Λ m : dualLat Λ) : ι → ℝ) = latDualMap Λ m := rfl

end Work.HP.Sig2.ThetaPoisson
