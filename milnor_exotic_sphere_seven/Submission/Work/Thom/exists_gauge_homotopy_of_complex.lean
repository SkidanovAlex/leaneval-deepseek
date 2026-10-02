import Mathlib
import Submission.Work.Thom.exists_path_GL_complex

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Gauge homotopies for complex vector bundle cores over contractible overlaps

Let `Z` be a complex vector bundle core over `B` with fibre `EuclideanSpace ℂ (Fin m)`, and let
`U ⊆ Z.baseSet i`, `V ⊆ Z.baseSet j` be two pieces of a trivializing cover whose overlap `U ∩ V` is
contractible.  The main result of this file, `exists_gauge_homotopy_of_complex`, produces a
homotopy

`H : [0,1] × (U ∩ V) → (E →L[ℝ] E)`

from the real-linear coordinate change `x ↦ (Z.coordChange i j x).restrictScalars ℝ` to the
identity all of whose values are bijections.  This is the "real" input for the orientability of the
realification of a complex bundle, cf. `Work.Thom.isOrientedOver_of_gauge_homotopy`.

The argument is as follows.  Write `E = EuclideanSpace ℂ (Fin m)` and `X = ↥(U ∩ V)`, and put

* `A x = (Z.coordChange i j x).restrictScalars ℝ`,
* `B y = (Z.coordChange j i y).restrictScalars ℝ`.

The cocycle condition of the core (`VectorBundleCore.coordChange_comp`) says that `B y` is a
two-sided inverse of `A y` on the overlap, so every value of `A` and of `B` is a bijection
(`coordChange_bijective_of_mem_baseSet_inter`).

Choose `x₀ ∈ X` and let `G : [0,1] × X → X` be a homotopy from the constant map at `x₀` to the
identity, which exists because `X` is contractible (`ContinuousMap.id_nullhomotopic`).  Let
`δ : [0,1] → (E →L[ℝ] E)` be a path of bijections from `A x₀` to the identity, as provided by
`exists_path_of_bijective_complex_linear` below.  Note that `A x₀ = A x₀` and that
`B x₀ ∘ A x₀ = 1`.  We now set

`H (t, x) = A x ∘ B (G (t, x)) ∘ δ t`.

Because `G (0, x) = x₀` and `G (1, x) = x`, we get

* `H (0, x) = A x ∘ B x₀ ∘ A x₀ = A x`,
* `H (1, x) = A x ∘ B x ∘ 1 = 1`;

and every value is a composite of bijections.  Joint continuity is composition of the continuous
families `x ↦ A x`, `x ↦ B x`, `t ↦ δ t` with the (jointly continuous) composition of
`E →L[ℝ] E`.  No reparametrisation of the interval is needed, since the identity arises by
cancelling the two `x`-dependent factors against each other.

## The pointwise path

The auxiliary `exists_path_of_bijective_complex_linear` states that a *bijective* `ℂ`-linear
endomorphism `A` of `E` can be joined to the identity by a path of bijective *real*-linear maps.
The path is the complex interpolation `z ↦ (1 - z) • A + z • 1` of `A` and the identity, evaluated
along a continuous path `f : [0,1] → ℂ` from `0` to `1` which avoids the finite set of complex
numbers where the interpolation degenerates.

That exceptional set is finite because, choosing a `ℂ`-basis of `E`, the determinant of the
interpolation is the value at `z` of the polynomial `Work.Thom.pathPoly`; the roots of a nonzero
polynomial are finite (`Polynomial.finite_setOfPred_isRoot`), and the complement of a countable
subset of `ℂ` is path connected (`Set.Countable.isPathConnected_compl_of_one_lt_rank`, applicable
since `ℂ` has real dimension `2 > 1`).  Here the polynomial is nonzero because its value at `0` is
`det A ≠ 0` (as `A` is bijective).

This is the same argument as in `Work.Thom.exists_path_GL_complex`, run on endomorphisms of `E`
rather than on matrices; the additional ingredient is that the path of complex-linear maps must be
restricted to real scalars at the end, which preserves bijectivity and continuity
(`ContinuousLinearMap.continuous_restrictScalars`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Thom

open scoped Classical

variable {m : ℕ}

/-- On the intersection of the two base sets, a coordinate change of a vector bundle core is
bijective: `Z.coordChange j i x` is a two-sided inverse of `Z.coordChange i j x` there, by the
cocycle condition. -/
lemma coordChange_bijective_of_mem_baseSet_inter {B : Type} [TopologicalSpace B] {ι : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    {i j : ι} {x : B} (hx : x ∈ Z.baseSet i ∩ Z.baseSet j) :
    Function.Bijective (Z.coordChange i j x) := by
  constructor
  · intro v w hvw
    have h1 := Z.coordChange_comp i j i x ⟨hx, hx.1⟩ v
    have h2 := Z.coordChange_comp i j i x ⟨hx, hx.1⟩ w
    rw [hvw] at h1
    rw [Z.coordChange_self i x hx.1 v] at h1
    rw [Z.coordChange_self i x hx.1 w] at h2
    exact h1.symm.trans h2
  · intro w
    refine ⟨Z.coordChange j i x w, ?_⟩
    rw [Z.coordChange_comp j i j x ⟨hx.symm, hx.2⟩ w, Z.coordChange_self j x hx.2 w]

/-- **A bijective `ℂ`-linear endomorphism of `ℂ^m` is joined to the identity by a path of bijective
real-linear maps.**

The path is `t ↦ ((1 - f t) • A + f t • 1).restrictScalars ℝ` for a path `f : [0,1] → ℂ` from `0`
to `1` avoiding the (finite, hence countable, hence path-avoidable) zero set of the polynomial
`Work.Thom.pathPoly m M 1`, where `M` is the matrix of `A` in a fixed `ℂ`-basis: at such a point the
interpolation is invertible, and restricting scalars preserves this. -/
lemma exists_path_of_bijective_complex_linear (m : ℕ)
    (A : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))
    (hA : Function.Bijective A) :
    ∃ δ : C(unitInterval, EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℂ (Fin m)),
      δ 0 = A.restrictScalars ℝ ∧ δ 1 = 1 ∧ ∀ t : unitInterval, Function.Bijective (δ t) := by
  classical
  -- A `ℂ`-basis of the fibre, and the matrix of `A` with respect to it.
  let b : Module.Basis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)) := PiLp.basisFun 2 ℂ (Fin m)
  let M : Matrix (Fin m) (Fin m) ℂ := LinearMap.toMatrix b b A.toLinearMap
  -- The matrix of `A` is invertible.
  have hAun : IsUnit A.toLinearMap := by
    rw [LinearMap.isUnit_iff_ker_eq_bot]
    exact LinearMap.ker_eq_bot.mpr hA.injective
  have hMun : IsUnit M.det := by
    have h : M.det = LinearMap.det A.toLinearMap := LinearMap.det_toMatrix b A.toLinearMap
    rw [h]
    exact LinearMap.isUnit_det _ hAun
  -- The determinant polynomial of the interpolation `z ↦ (1 - z) • A + z • 1` is nonzero,
  -- because at `z = 0` it evaluates to `det A`.
  have hp_ne : pathPoly m M 1 ≠ 0 := by
    intro hp
    have h0 : (pathPoly m M 1).eval 0 = M.det := by
      rw [pathPoly_eval]
      simp
    rw [hp] at h0
    simp at h0
    exact hMun.ne_zero h0.symm
  -- At a non-root of the polynomial the interpolation is bijective.
  have hcrit : ∀ z : ℂ, (pathPoly m M 1).eval z ≠ 0 →
      Function.Bijective
        ((1 - z) • A + z • (1 : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))) := by
    intro z hz
    set T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
      (1 - z) • A + z • 1 with hT
    -- The matrix of the interpolation is the interpolation of the matrices.
    have hmat : LinearMap.toMatrix b b T.toLinearMap = (1 - z) • M + z • 1 := by
      rw [hT, ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
        ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_one]
      rw [map_add, map_smul, map_smul, LinearMap.toMatrix_one]
    have hdet : ((1 - z) • M + z • 1).det = LinearMap.det T.toLinearMap := by
      rw [← hmat]
      exact LinearMap.det_toMatrix b T.toLinearMap
    have hne : LinearMap.det T.toLinearMap ≠ 0 := by
      have h1 : (pathPoly m M 1).eval z = ((1 - z) • M + z • 1).det := pathPoly_eval m M 1 z
      rw [h1] at hz
      rwa [hdet] at hz
    -- A nonzero determinant means trivial kernel, hence bijectivity in finite dimension.
    have hker : T.toLinearMap.ker = ⊥ := by
      by_contra h
      exact hne ((LinearMap.det_eq_zero_iff_ker_ne_bot (f := T.toLinearMap)).mpr h)
    have hinj : Function.Injective ⇑T := by
      simpa using LinearMap.ker_eq_bot.mp hker
    refine ⟨hinj, ?_⟩
    simpa using LinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp hker)
  -- The exceptional set is the root set of the polynomial.
  set S : Set ℂ := {z | (pathPoly m M 1).eval z = 0} with hSdef
  have hS_count : S.Countable := by
    have hfin : ({z : ℂ | (pathPoly m M 1).IsRoot z}).Finite :=
      Polynomial.finite_setOfPred_isRoot hp_ne
    rw [show S = {z : ℂ | (pathPoly m M 1).IsRoot z} from by
      ext z; simp [hSdef, Polynomial.IsRoot.def]]
    exact hfin.countable
  have h0S : (0 : ℂ) ∈ Sᶜ := by
    simp only [hSdef, Set.mem_compl_iff, Set.mem_ofPred_eq]
    rw [pathPoly_eval]
    simpa using hMun.ne_zero
  have h1S : (1 : ℂ) ∈ Sᶜ := by
    simp only [hSdef, Set.mem_compl_iff, Set.mem_ofPred_eq]
    rw [pathPoly_eval]
    simp
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hconn : IsPathConnected (Sᶜ) :=
    Set.Countable.isPathConnected_compl_of_one_lt_rank hrank hS_count
  have hjoin : JoinedIn (Sᶜ) (0 : ℂ) 1 := hconn.joinedIn 0 h0S 1 h1S
  let f : Path (0 : ℂ) 1 := hjoin.somePath
  have hfmem : ∀ t : unitInterval, f t ∈ Sᶜ := fun t => hjoin.somePath_mem t
  have hcontT : Continuous fun z : ℂ =>
      ((1 - z) • A + z • (1 : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))) := by
    refine Continuous.add ?_ ?_
    · exact (continuous_const.sub continuous_id).smul continuous_const
    · exact continuous_id.smul continuous_const
  refine ⟨⟨fun t : unitInterval =>
      (((1 - (f t)) • A + (f t) •
        (1 : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)))).restrictScalars ℝ,
      ?_⟩, ?_, ?_, ?_⟩
  · exact (ContinuousLinearMap.continuous_restrictScalars ℝ).comp (hcontT.comp f.continuous)
  · show (((1 - (f (0 : unitInterval))) • A + (f (0 : unitInterval)) •
        (1 : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)))).restrictScalars ℝ
        = A.restrictScalars ℝ
    rw [f.source]
    ext v
    simp
  · show (((1 - (f (1 : unitInterval))) • A + (f (1 : unitInterval)) •
        (1 : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)))).restrictScalars ℝ = 1
    rw [f.target]
    ext v
    simp
  · intro t
    have ht := hfmem t
    rw [hSdef] at ht
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at ht
    simpa using hcrit (f t) ht

theorem exists_gauge_homotopy_of_complex (m : ℕ) (hm : 1 ≤ m)
    {B : Type} [TopologicalSpace B] {ι : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    {U V : Set B} {i j : ι} (hUi : U ⊆ Z.baseSet i) (hVj : V ⊆ Z.baseSet j)
    [ContractibleSpace ↥(U ∩ V)] :
    ∃ H : C(unitInterval × ↥(U ∩ V),
        EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℂ (Fin m)),
      (∀ x : ↥(U ∩ V), H (0, x) = (Z.coordChange i j (x : B)).restrictScalars ℝ) ∧
      (∀ x : ↥(U ∩ V), H (1, x) = 1) ∧
      (∀ t x, Function.Bijective (H (t, x))) := by
  classical
  -- `x₀` and a homotopy `G` from the constant map at `x₀` to the identity of `U ∩ V`.
  obtain ⟨x₀, hx₀⟩ := id_nullhomotopic ↥(U ∩ V)
  let G : ContinuousMap.Homotopy (ContinuousMap.const _ x₀) (ContinuousMap.id _) :=
    (Classical.choice hx₀).symm
  -- The overlap lies in both base sets.
  have hsub : ∀ x : ↥(U ∩ V), (x : B) ∈ Z.baseSet i ∩ Z.baseSet j :=
    fun x => ⟨hUi x.2.1, hVj x.2.2⟩
  have hsubji : ∀ x : ↥(U ∩ V), (x : B) ∈ Z.baseSet j ∩ Z.baseSet i :=
    fun x => ⟨hVj x.2.2, hUi x.2.1⟩
  -- The two coordinate changes, as continuous families of real-linear maps.
  have hcontA : Continuous fun x : ↥(U ∩ V) =>
      (Z.coordChange i j (x : B)).restrictScalars ℝ := by
    exact (ContinuousLinearMap.continuous_restrictScalars ℝ).comp
      ((Z.continuousOn_coordChange i j).comp_continuous continuous_subtype_val (fun x => hsub x))
  have hcontB : Continuous fun x : ↥(U ∩ V) =>
      (Z.coordChange j i (x : B)).restrictScalars ℝ := by
    exact (ContinuousLinearMap.continuous_restrictScalars ℝ).comp
      ((Z.continuousOn_coordChange j i).comp_continuous continuous_subtype_val (fun x => hsubji x))
  -- The path of bijective real-linear maps from `A x₀` to the identity.
  obtain ⟨δ, hδ0, hδ1, hδbij⟩ :=
    exists_path_of_bijective_complex_linear m (Z.coordChange i j (x₀ : B))
      (coordChange_bijective_of_mem_baseSet_inter Z (hsub x₀))
  -- Composition of real-linear endomorphisms is jointly continuous.
  have hcomp : Continuous fun q : (EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℂ (Fin m)) ×
      (EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℂ (Fin m)) => q.1 ∘SL q.2 :=
    (isBoundedBilinearMap_comp (𝕜 := ℝ)).continuous
  have comp_one : ∀ f : EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℂ (Fin m),
      f ∘SL (1 : EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℂ (Fin m)) = f := by
    intro f
    ext v
    rfl
  refine ⟨⟨fun p : unitInterval × ↥(U ∩ V) =>
      (Z.coordChange i j (p.2 : B)).restrictScalars ℝ ∘SL
        (((Z.coordChange j i ((G.toContinuousMap p : ↥(U ∩ V)) : B)).restrictScalars ℝ)
          ∘SL δ p.1), ?_⟩, ?_, ?_, ?_⟩
  · -- Joint continuity of the formula.
    refine hcomp.comp ((hcontA.comp continuous_snd).prodMk ?_)
    refine hcomp.comp ((hcontB.comp G.toContinuousMap.continuous).prodMk ?_)
    exact δ.continuous.comp continuous_fst
  · -- Value at `t = 0`: `A x ∘ B x₀ ∘ A x₀ = A x`.
    intro x
    have hG0 : (G.toContinuousMap (0, x) : ↥(U ∩ V)) = x₀ := by
      simp
    have hBA : (Z.coordChange j i (x₀ : B)).restrictScalars ℝ ∘SL
        (Z.coordChange i j (x₀ : B)).restrictScalars ℝ = 1 := by
      change (((Z.coordChange j i (x₀ : B)) ∘SL (Z.coordChange i j (x₀ : B))).restrictScalars ℝ)
        = 1
      rw [Z.coordChange_linear_comp i j i x₀ ⟨hsub x₀, (hsub x₀).1⟩]
      have hone : Z.coordChange i i (x₀ : B) = 1 := by
        ext v
        rw [Z.coordChange_self i (x₀ : B) (hsub x₀).1 v]
        rfl
      rw [hone]
      ext v
      rfl
    show ((Z.coordChange i j (x : B)).restrictScalars ℝ) ∘SL
        (((Z.coordChange j i ((G.toContinuousMap (0, x) : ↥(U ∩ V)) : B)).restrictScalars ℝ)
          ∘SL δ 0) = (Z.coordChange i j (x : B)).restrictScalars ℝ
    rw [hG0, hδ0, hBA, comp_one]
  · -- Value at `t = 1`: `A x ∘ B x ∘ 1 = 1`.
    intro x
    have hG1 : (G.toContinuousMap (1, x) : ↥(U ∩ V)) = x := by
      simp
    have hAB : (Z.coordChange i j (x : B)).restrictScalars ℝ ∘SL
        (Z.coordChange j i (x : B)).restrictScalars ℝ = 1 := by
      change (((Z.coordChange i j (x : B)) ∘SL (Z.coordChange j i (x : B))).restrictScalars ℝ) = 1
      rw [Z.coordChange_linear_comp j i j x ⟨hsubji x, (hsub x).2⟩]
      have hone : Z.coordChange j j (x : B) = 1 := by
        ext v
        rw [Z.coordChange_self j (x : B) (hsub x).2 v]
        rfl
      rw [hone]
      ext v
      rfl
    show ((Z.coordChange i j (x : B)).restrictScalars ℝ) ∘SL
        (((Z.coordChange j i ((G.toContinuousMap (1, x) : ↥(U ∩ V)) : B)).restrictScalars ℝ)
          ∘SL δ 1) = 1
    rw [hG1, hδ1]
    rw [comp_one, hAB]
  · -- Every value is bijective.
    intro t x
    show Function.Bijective ((Z.coordChange i j (x : B)).restrictScalars ℝ ∘SL
        (((Z.coordChange j i ((G.toContinuousMap (t, x) : ↥(U ∩ V)) : B)).restrictScalars ℝ)
          ∘SL δ t))
    have hAx : Function.Bijective ((Z.coordChange i j (x : B)).restrictScalars ℝ) := by
      simpa using coordChange_bijective_of_mem_baseSet_inter Z (hsub x)
    have hBy : Function.Bijective
        ((Z.coordChange j i ((G.toContinuousMap (t, x) : ↥(U ∩ V)) : B)).restrictScalars ℝ) := by
      simpa using
        coordChange_bijective_of_mem_baseSet_inter Z (hsubji (G.toContinuousMap (t, x) : ↥(U ∩ V)))
    simpa only [ContinuousLinearMap.coe_comp] using
      Function.Bijective.comp hAx (Function.Bijective.comp hBy (hδbij t))

end Work.Thom
