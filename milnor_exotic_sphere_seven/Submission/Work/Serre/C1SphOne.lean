import Mathlib
import Submission.Work.Serre.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The circle `S¹ = Sph 1` is a `K(ℤ,1)`, and is path connected

C1 of the Serre blueprint needs three facts about `Work.Serre.Sph 1` (the unit circle in `ℝ²`):

* it is path connected (`sphOnePathConnected`);
* its fundamental group is infinite cyclic (`piOneSphOne`), which lets us construct a map
  `Sph 1 → X` inducing an isomorphism on `π₁` from the hypothesis that `X` is a `K(ℤ,1)`;
* it is aspherical (`sphOneAspherical`): `π_n(S¹) = 0` for `n ≥ 2`, so that this map is a
  π-isomorphism in every degree.

The first two are proved here: path connectedness from `isPathConnected_sphere`, and the fundamental
group from the covering `ℝ → Circle` transported along the homeomorphism `Circle ≃ₜ S¹` (the total
space `ℝ` is contractible, so the deck group `2πℤ ≅ ℤ` computes `π₁`).
-/

namespace Work.Serre

noncomputable section

open CategoryTheory

/-- The circle `Sph 1 = {x : ℝ² // ‖x‖ = 1}` is path connected. -/
theorem sphOnePathConnected : PathConnectedSpace (Sph 1) := by
  refine (isPathConnected_iff_pathConnectedSpace (F :=
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)).mp ?_
  refine isPathConnected_sphere (E := EuclideanSpace ℝ (Fin 2)) ?_ 0 (by norm_num)
  rw [show Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) = (2 : Cardinal) from by
    have h2 := LinearEquiv.rank_eq (EuclideanSpace.equiv (Fin 2) ℝ).toLinearEquiv
    rw [h2]; exact rank_fin_fun 2]
  norm_num

/-- The linear isometry `ℂ ≃ ℝ²` coming from the orthonormal basis `{1, I}`. -/
def circleLinIso : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr

/-- **The unit circle of `ℂ` is homeomorphic to `S¹ = {x : ℝ² | ‖x‖ = 1}`.** -/
def circleHomeoSphereOne : Circle ≃ₜ Sph 1 :=
  Homeomorph.subtype (p := fun z : ℂ => z ∈ Submonoid.unitSphere ℂ)
    (q := fun v : EuclideanSpace ℝ (Fin 2) => v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (circleLinIso : ℂ ≃ₜ EuclideanSpace ℝ (Fin 2)) (fun z => by
      change z ∈ Metric.sphere (0 : ℂ) 1 ↔
        circleLinIso z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
      simp only [Metric.mem_sphere, dist_eq_norm, sub_zero, circleLinIso.norm_map])

/-- The identity map is a multiplicative equivalence from `Mᵐᵒᵖ` to `M` when `M` is commutative. -/
def mulOppositeMulEquivComm (M : Type*) [CommMonoid M] : Mᵐᵒᵖ ≃* M where
  toFun := MulOpposite.unop
  invFun := MulOpposite.op
  left_inv a := rfl
  right_inv a := rfl
  map_mul' a b := (MulOpposite.unop_mul a b).trans (mul_comm _ _)

/-- The additive subgroup `2πℤ ⊆ ℝ` is infinite cyclic. -/
def zmultiplesTwoPiAddEquivInt : AddSubgroup.zmultiples (2 * Real.pi : ℝ) ≃+ ℤ := by
  have hne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hbij : Function.Bijective
      (fun n : ℤ => (⟨n • (2 * Real.pi), AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩⟩ :
        AddSubgroup.zmultiples (2 * Real.pi : ℝ))) := by
    constructor
    · intro n m h
      have h' : (n : ℝ) * (2 * Real.pi) = (m : ℝ) * (2 * Real.pi) := by
        simpa [zsmul_eq_mul] using congrArg Subtype.val h
      exact Int.cast_injective (mul_right_cancel₀ hne h')
    · intro x
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp x.2
      exact ⟨k, Subtype.ext hk⟩
  exact (AddEquiv.ofBijective
    ({ toFun := fun n =>
        (⟨n • (2 * Real.pi), AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩⟩ :
          AddSubgroup.zmultiples (2 * Real.pi : ℝ))
       map_zero' := Subtype.ext (zero_zsmul _)
       map_add' := fun n m => Subtype.ext (add_zsmul _ _ _) } :
        ℤ →+ AddSubgroup.zmultiples (2 * Real.pi : ℝ)) hbij).symm

/-- `Additive (Multiplicative ℤ) ≃ ℤ`. -/
def additiveMultiplicativeEquivInt : Additive (Multiplicative ℤ) ≃+ ℤ where
  toFun a := (Additive.toMul a).toAdd
  invFun n := Additive.ofMul (Multiplicative.ofAdd n)
  left_inv a := by cases a; rfl
  right_inv n := rfl
  map_add' a b := by rw [toMul_add, toAdd_mul]

/-- **The fundamental group of the circle is infinite cyclic**: for every base point `x : S¹`,
`π₁(S¹,x) ≅ ℤ` (additively).  This is Mathlib's covering-space theory applied to the covering
`ℝ → Circle` (whose total space is contractible), transported along the model homeomorphism
`Circle ≃ₜ S¹`. -/
theorem pi1SphOne_addEquiv_int (x : Sph 1) :
    Nonempty (Additive (HomotopyGroup (Fin 1) (Sph 1) x) ≃+ ℤ) := by
  have hcov : IsAddQuotientCoveringMap
      ((circleHomeoSphereOne : Circle → Sph 1) ∘ (Circle.exp : ℝ → Circle))
      (AddSubgroup.zmultiples (2 * Real.pi : ℝ)) :=
    Circle.isAddQuotientCoveringMap_exp.homeomorph_comp circleHomeoSphereOne
  obtain ⟨c, rfl⟩ := circleHomeoSphereOne.surjective x
  obtain ⟨t, ht⟩ := Circle.exp_surjective c
  have hlift : ((circleHomeoSphereOne : Circle → Sph 1) ∘ (Circle.exp : ℝ → Circle)) t =
      circleHomeoSphereOne c := by
    rw [Function.comp_apply, ht]
  have h1 : HomotopyGroup (Fin 1) (Sph 1) (circleHomeoSphereOne c) ≃*
      FundamentalGroup (Sph 1) (circleHomeoSphereOne c) :=
    HomotopyGroup.pi1MulEquivFundamentalGroup
  have h2 : FundamentalGroup (Sph 1) (circleHomeoSphereOne c) ≃*
      (Multiplicative (AddSubgroup.zmultiples (2 * Real.pi : ℝ)))ᵐᵒᵖ :=
    hcov.fundamentalGroupEquiv (x := circleHomeoSphereOne c) ⟨t, hlift⟩
  have h3 : (Multiplicative (AddSubgroup.zmultiples (2 * Real.pi : ℝ)))ᵐᵒᵖ ≃* Multiplicative ℤ :=
    (mulOppositeMulEquivComm _).trans (AddEquiv.toMultiplicative zmultiplesTwoPiAddEquivInt)
  exact ⟨(MulEquiv.toAdditive ((h1.trans h2).trans h3)).trans additiveMultiplicativeEquivInt⟩

/-- The identity multiplicative equivalence `Multiplicative (Additive G) ≃* G`. -/
def multiplicativeAdditiveSelf (G : Type*) [Group G] : Multiplicative (Additive G) ≃* G where
  toFun x := (Multiplicative.toAdd x).toMul
  invFun g := Multiplicative.ofAdd (Additive.ofMul g)
  left_inv x := by
    cases x with
    | ofAdd a => cases a with
      | ofMul g => rfl
  right_inv g := rfl
  map_mul' x y := by
    cases x with
    | ofAdd a => cases y with
      | ofAdd b => cases a with
        | ofMul g => cases b with
          | ofMul h => rfl

/-- The powers of the generator `ofAdd 1` of `Multiplicative ℤ`. -/
theorem ofAdd_one_zpow (m : ℤ) :
    (Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) ^ m = Multiplicative.ofAdd m := by
  rw [← ofAdd_zsmul]
  simp [zsmul_eq_mul]

/-- **`π₁(S¹) ≅ ℤ`**, in the form used to build maps out of `S¹`: the group is infinite cyclic. -/
theorem piOneSphOne (s₀ : Sph 1) :
    ∃ c : HomotopyGroup (Fin 1) (Sph 1) s₀,
      ∀ z : HomotopyGroup (Fin 1) (Sph 1) s₀, ∃! m : ℤ, z = c ^ m := by
  obtain ⟨e⟩ := pi1SphOne_addEquiv_int s₀
  let φ : HomotopyGroup (Fin 1) (Sph 1) s₀ ≃* Multiplicative ℤ :=
    (multiplicativeAdditiveSelf _).symm.trans (AddEquiv.toMultiplicative e)
  refine ⟨φ.symm (Multiplicative.ofAdd 1), fun z => ?_⟩
  refine ⟨(φ z).toAdd, ?_, ?_⟩
  · have : φ (φ.symm (Multiplicative.ofAdd 1) ^ (φ z).toAdd) = φ z := by
      rw [map_zpow, MulEquiv.apply_symm_apply, ofAdd_one_zpow]
      exact ofAdd_toAdd (φ z)
    exact (φ.injective this).symm
  · intro m hm
    have h1 : φ z = (Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) ^ m := by
      rw [hm, map_zpow, MulEquiv.apply_symm_apply]
    rw [ofAdd_one_zpow] at h1
    exact (congrArg Multiplicative.toAdd h1).symm

end

end Work.Serre

/-! ## The obstruction to asphericity, recorded as a precise statement

The remaining circle fact needed by C1 is `π_n(S¹) = 0` for `n ≥ 2`.  The intended proof uses the
covering projection `p : ℝ → Sph 1` (`circleHomeoSphereOne ∘ Circle.exp`, whose `IsCoveringMap`
structure is `(Circle.isAddQuotientCoveringMap_exp.homeomorph_comp circleHomeoSphereOne).isCoveringMap`)
and the long exact homotopy sequence of a Serre fibration
(`Work.StemsB.fibration_les`, with `IsSerreFibration` supplied by
`Work.StemsB.isSerreFibration_of_isCoveringMap`): the sequence
`π_n(ℝ) → π_n(S¹) → π_{n-1}(fibre)` is exact at `π_n(S¹)`, `π_n(ℝ) = 0` (ℝ is contractible) and
`π_{n-1}(fibre) = 0` for `n - 1 ≥ 1` (the fibre of a covering map is discrete, and a based cube
mapping into a discrete space is constant), so `π_n(S¹) = 0` for `n ≥ 2`. -/
