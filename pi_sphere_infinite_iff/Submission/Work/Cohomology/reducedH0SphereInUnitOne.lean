import Mathlib
import Submission.Work.Cohomology.DiskPairBasic
import Submission.Work.Cohomology.sphereInUnitHomologyIso

set_option synthInstance.maxHeartbeats 400000

/-!
# The reduced zeroth homology of `S⁰ = sphereInUnit 1`

The space `S⁰ = sphereInUnit 1 ⊆ D¹` is the two point space `{±e₀}`.  Its singular homology in
degree zero is therefore free of rank two, and the augmentation
`TopCat.singularHomology₀ε` — the map which sends each connected component to `1` — is the sum map
`ℤ ⊕ ℤ ⟶ ℤ`.  Its kernel is the reduced zeroth homology `H̃₀(S⁰) ≅ ℤ`, which is the statement
proved here.

The argument has three parts.

* Topological: `S⁰ = {±e₀}` has exactly two path components.  We work with the standard model
  `Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1`, where the two points and the non-existence of
  a path between them are proved using the intermediate value theorem applied to the coordinate
  function.  The result is transported to `sphereInUnit 1` along the homeomorphism
  `sphereInUnitHomeomorph`.
* Homological: Mathlib's `TopCat.singularHomology₀Iso` identifies `H₀(X)` with the coproduct of
  copies of the coefficient ring indexed by `ZerothHomotopy X`, and
  `TopCat.singularHomology₀Iso_sigma_desc_id` identifies the augmentation with the sum
  `Sigma.desc (fun _ ↦ 𝟙 R)`.  Through the bijection `ZerothHomotopy X ≃ Bool` and the canonical
  isomorphism of a binary coproduct with `Bool → ℤ`, the augmentation becomes the sum map `sig`.
* Algebraic: the kernel of `sig` is `ℤ`, exhibited by `f ↦ f true`.
-/

set_option maxHeartbeats 1000000
open CategoryTheory Limits AlgebraicTopology Metric
open scoped unitInterval

namespace Work.Cohomology

noncomputable section

/-! ## The two points of `S⁰` -/

noncomputable def vOne : EuclideanSpace ℝ (Fin 1) := (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ => 1)
noncomputable def vNegOne : EuclideanSpace ℝ (Fin 1) := (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ => -1)

lemma vOne_apply : (vOne : EuclideanSpace ℝ (Fin 1)) 0 = 1 := by simp [vOne]
lemma vNegOne_apply : (vNegOne : EuclideanSpace ℝ (Fin 1)) 0 = -1 := by simp [vNegOne]

lemma norm_fin_one (v : EuclideanSpace ℝ (Fin 1)) : ‖v‖ = |v 0| := by
  rw [EuclideanSpace.norm_eq]; simp [Real.sqrt_sq_eq_abs]

lemma vOne_norm : ‖vOne‖ = 1 := by rw [norm_fin_one, vOne_apply, abs_one]
lemma vNegOne_norm : ‖vNegOne‖ = 1 := by rw [norm_fin_one, vNegOne_apply, abs_neg, abs_one]

lemma vOne_mem_sphere : vOne ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact vOne_norm
lemma vNegOne_mem_sphere : vNegOne ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact vNegOne_norm

noncomputable def spOne : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := ⟨vOne, vOne_mem_sphere⟩
noncomputable def spNegOne : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 :=
  ⟨vNegOne, vNegOne_mem_sphere⟩

/-- The coordinate of a point of `S⁰ ⊆ ℝ¹` is `±1`. -/
lemma coord_eq_sphere (y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    (y : EuclideanSpace ℝ (Fin 1)) 0 = 1 ∨ (y : EuclideanSpace ℝ (Fin 1)) 0 = -1 := by
  have h : ‖(y : EuclideanSpace ℝ (Fin 1))‖ = 1 := by
    have hx := y.2
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx
    exact hx
  exact (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp
    ((norm_fin_one (y : EuclideanSpace ℝ (Fin 1))).symm.trans h)

lemma eq_spOne_of_coord (y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)
    (h : (y : EuclideanSpace ℝ (Fin 1)) 0 = 1) : y = spOne := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  simpa [spOne, vOne] using h

lemma eq_spNegOne_of_coord (y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)
    (h : (y : EuclideanSpace ℝ (Fin 1)) 0 = -1) : y = spNegOne := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  simpa [spNegOne, vNegOne] using h

lemma continuous_coord_sphere :
    Continuous (fun y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 =>
      (y : EuclideanSpace ℝ (Fin 1)) 0) := by
  exact (continuous_apply 0).comp ((PiLp.continuous_ofLp 2 (fun _ : Fin 1 => ℝ)).comp
    continuous_subtype_val)

/-- There is no path in `S⁰ ⊆ ℝ¹` from `e₀` to `-e₀`. -/
lemma not_joined_sphere : ¬ Joined spOne spNegOne := by
  rintro ⟨γ⟩
  have hcont : Continuous (fun t : I => (γ t : EuclideanSpace ℝ (Fin 1)) 0) :=
    continuous_coord_sphere.comp γ.continuous
  have h0 : (γ 0 : EuclideanSpace ℝ (Fin 1)) 0 = 1 := by
    rw [Path.source γ]; exact vOne_apply
  have h1 : (γ 1 : EuclideanSpace ℝ (Fin 1)) 0 = -1 := by
    rw [Path.target γ]; exact vNegOne_apply
  have hmem : (0:ℝ) ∈ Set.range (fun t : I => (γ t : EuclideanSpace ℝ (Fin 1)) 0) := by
    apply intermediate_value_univ (1 : I) (0 : I)
      (f := fun t : I => (γ t : EuclideanSpace ℝ (Fin 1)) 0) hcont
    rw [h1, h0]; norm_num
  obtain ⟨t, ht⟩ := hmem
  change (γ t : EuclideanSpace ℝ (Fin 1)) 0 = 0 at ht
  rcases coord_eq_sphere (γ t) with h | h
  · rw [h] at ht; exact absurd ht (by norm_num)
  · rw [h] at ht; exact absurd ht (by norm_num)

/-! ## Transport to `sphereInUnit 1` -/

noncomputable def phi : TopCat.of (sphereInUnit 1) ≃ₜ
    TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) := sphereInUnitHomeomorph 1

noncomputable def ptOne : sphereInUnit 1 := phi.symm spOne
noncomputable def ptNegOne : sphereInUnit 1 := phi.symm spNegOne

lemma phi_ptOne : phi ptOne = spOne := Homeomorph.apply_symm_apply phi spOne

lemma phi_ptNegOne : phi ptNegOne = spNegOne := Homeomorph.apply_symm_apply phi spNegOne

/-- Every point of `S⁰ = sphereInUnit 1` is one of the two points `±e₀`. -/
lemma eq_ptOne_or (x : sphereInUnit 1) : x = ptOne ∨ x = ptNegOne := by
  have h : phi x = spOne ∨ phi x = spNegOne := by
    rcases coord_eq_sphere (phi x) with h | h
    · exact Or.inl (eq_spOne_of_coord (phi x) h)
    · exact Or.inr (eq_spNegOne_of_coord (phi x) h)
  rcases h with h | h
  · left
    exact (Homeomorph.symm_apply_apply phi x).symm.trans (congrArg phi.symm h)
  · right
    exact (Homeomorph.symm_apply_apply phi x).symm.trans (congrArg phi.symm h)

lemma not_joined : ¬ Joined ptOne ptNegOne := by
  intro h
  refine not_joined_sphere ?_
  have h2 := h.map phi.continuous
  rwa [phi_ptOne, phi_ptNegOne] at h2

lemma mk_ptOne_ne_mk_ptNegOne :
    ZerothHomotopy.mk ptOne ≠ ZerothHomotopy.mk ptNegOne := by
  intro h
  exact not_joined (Quotient.exact h)

lemma mk_ptNegOne_ne_mk_ptOne :
    ZerothHomotopy.mk ptNegOne ≠ ZerothHomotopy.mk ptOne :=
  fun h => mk_ptOne_ne_mk_ptNegOne h.symm

/-- `S⁰ = sphereInUnit 1` has exactly two path components. -/
noncomputable def zerothEquivBool : ZerothHomotopy (TopCat.of (sphereInUnit 1)) ≃ Bool := by
  classical
  refine ⟨fun z => if z = ZerothHomotopy.mk ptOne then true else false,
    fun b => if b then ZerothHomotopy.mk ptOne else ZerothHomotopy.mk ptNegOne, ?_, ?_⟩
  · intro z
    show (if (if z = ZerothHomotopy.mk ptOne then true else false) = true then
      ZerothHomotopy.mk ptOne else ZerothHomotopy.mk ptNegOne) = z
    by_cases h : z = ZerothHomotopy.mk ptOne
    · rw [if_pos h, if_pos rfl, h]
    · have h2 : z = ZerothHomotopy.mk ptNegOne := by
        obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective z
        rcases eq_ptOne_or x with rfl | rfl
        · exact absurd rfl h
        · rfl
      rw [if_neg h, if_neg Bool.false_ne_true, h2]
  · intro b
    cases b
    · show (if (if (false : Bool) = true then ZerothHomotopy.mk ptOne
          else ZerothHomotopy.mk ptNegOne) = ZerothHomotopy.mk ptOne then true else false) = false
      rw [if_neg Bool.false_ne_true, if_neg mk_ptNegOne_ne_mk_ptOne]
    · show (if (if (true : Bool) = true then ZerothHomotopy.mk ptOne
          else ZerothHomotopy.mk ptNegOne) = ZerothHomotopy.mk ptOne then true else false) = true
      rw [if_pos rfl, if_pos rfl]

/-! ## The algebra of the augmentation -/

abbrev RZ : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-- The sum (augmentation) map `ℤ ⊕ ℤ ⟶ ℤ`, in the model `Bool → ℤ`. -/
noncomputable def sig : (Bool → ℤ) →ₗ[ℤ] ℤ where
  toFun f := f true + f false
  map_add' f g := by simp only [Pi.add_apply]; ring
  map_smul' n f := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The kernel of the sum map `Bool → ℤ` is `ℤ`, via the evaluation at `true`. -/
noncomputable def kerSigEquiv : LinearMap.ker sig ≃ₗ[ℤ] ℤ where
  toFun f := f.1 true
  map_add' f g := rfl
  map_smul' c f := rfl
  invFun n := ⟨fun b => if b then n else -n, by simp [sig]⟩
  left_inv f := by
    have hf : f.1 true + f.1 false = 0 := by simpa [sig] using f.2
    ext b
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]; linarith
    · simp
  right_inv n := by simp

/-- The kernel of `g ∘ₗ e` for a linear equivalence `e` and a linear map `g`. -/
noncomputable def kerCompEquiv {M N P : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] [AddCommGroup P] [Module ℤ P]
    (e : M ≃ₗ[ℤ] N) (g : N →ₗ[ℤ] P) :
    LinearMap.ker (g ∘ₗ (e : M →ₗ[ℤ] N)) ≃ₗ[ℤ] LinearMap.ker g where
  toFun x := ⟨e x.1, x.2⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp
  invFun y := ⟨e.symm y.1, by
    have h : (e : M →ₗ[ℤ] N) (e.symm y.1) = y.1 := LinearEquiv.apply_symm_apply e y.1
    show g ((e : M →ₗ[ℤ] N) (e.symm y.1)) = 0
    rw [h]
    exact y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp

/-! ## The main computation -/

theorem reducedH0SphereInUnitOne :
    Nonempty
      (ModuleCat.of ℤ (LinearMap.ker
          (TopCat.singularHomology₀ε (TopCat.of (Work.Cohomology.sphereInUnit 1))
            (ModuleCat.of ℤ ℤ)).hom) ≅ ModuleCat.of ℤ ℤ) := by
  classical
  let X : TopCat := TopCat.of (sphereInUnit 1)
  let hs := TopCat.singularHomology₀Iso X RZ
  have hε : hs.hom ≫ Sigma.desc (fun _ : ZerothHomotopy X => 𝟙 RZ)
      = TopCat.singularHomology₀ε X RZ :=
    TopCat.singularHomology₀Iso_sigma_desc_id X RZ
  let e : ZerothHomotopy X ≃ Bool := zerothEquivBool
  let Φ : (∐ (fun _ : ZerothHomotopy X => RZ)) ≅ (∐ (fun _ : Bool => RZ)) :=
    Sigma.whiskerEquiv e (fun _ => Iso.refl RZ)
  have hΦ : ∀ j : ZerothHomotopy X,
      Sigma.ι (fun _ : ZerothHomotopy X => RZ) j ≫ Φ.hom
        = Sigma.ι (fun _ : Bool => RZ) (e j) := by
    intro j
    rw [show Φ.hom = Sigma.map' e (fun _ => (Iso.refl RZ).inv) from rfl, Sigma.ι_comp_map']
    simp
  let Ψ : (∐ (fun _ : Bool => RZ)) ≅ ModuleCat.of ℤ (Bool → ℤ) :=
    ModuleCat.coprodIsoDirectSum (fun _ : Bool => RZ) ≪≫
      (DirectSum.linearEquivFunOnFintype ℤ Bool (fun _ => ℤ)).toModuleIso
  have hΨj : ∀ j : Bool,
      Sigma.ι (fun _ : Bool => RZ) j ≫ Ψ.hom ≫ ModuleCat.ofHom sig = 𝟙 RZ := by
    intro j
    rw [← Category.assoc]
    rw [show Sigma.ι (fun _ : Bool => RZ) j ≫ Ψ.hom
      = ModuleCat.ofHom ((DirectSum.linearEquivFunOnFintype ℤ Bool (fun _ => ℤ) : _ →ₗ[ℤ] _) ∘ₗ
          DirectSum.lof ℤ Bool (fun _ => ℤ) j) from by
      rw [show Ψ.hom = (ModuleCat.coprodIsoDirectSum (fun _ : Bool => RZ)).hom ≫
          (LinearEquiv.toModuleIso (DirectSum.linearEquivFunOnFintype ℤ Bool (fun _ => ℤ))).hom
            from rfl]
      rw [← Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom, LinearEquiv.toModuleIso_hom,
        ← ModuleCat.ofHom_comp]]
    rw [← ModuleCat.ofHom_comp]
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_ofHom, ModuleCat.hom_id]
    apply LinearMap.ext
    intro x
    show sig ((DirectSum.linearEquivFunOnFintype ℤ Bool (fun _ => ℤ))
          ((DirectSum.lof ℤ Bool (fun _ => ℤ) j) x)) = x
    rw [DirectSum.linearEquivFunOnFintype_lof]
    cases j <;> simp [sig, Pi.single_eq_same, Pi.single_eq_of_ne]
  have hd : Sigma.desc (fun _ : ZerothHomotopy X => 𝟙 RZ)
      = Φ.hom ≫ Ψ.hom ≫ ModuleCat.ofHom sig := by
    apply Sigma.hom_ext
    intro j
    rw [Sigma.ι_desc, ← Category.assoc, hΦ j]
    exact (hΨj (e j)).symm
  let E := (hs ≪≫ Φ ≪≫ Ψ).toLinearEquiv
  have hE : (TopCat.singularHomology₀ε X RZ).hom = sig ∘ₗ (E : _ →ₗ[ℤ] _) := by
    have h1 : TopCat.singularHomology₀ε X RZ = (hs ≪≫ Φ ≪≫ Ψ).hom ≫ ModuleCat.ofHom sig := by
      rw [← hε, hd]
      simp [Iso.trans_hom, Category.assoc]
    rw [h1, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    rfl
  have hker : LinearMap.ker (TopCat.singularHomology₀ε X RZ).hom ≃ₗ[ℤ] ℤ := by
    rw [hE]
    exact (kerCompEquiv E sig).trans kerSigEquiv
  exact ⟨LinearEquiv.toModuleIso hker⟩

end

end Work.Cohomology
