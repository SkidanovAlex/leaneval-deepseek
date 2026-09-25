/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.IdeleNorm
import Submission.NK.GlobalCFT.IdeleClassGroup

/-!
# The compactness of the norm-one idèle class group: auxiliary sets

For a number field `K` the **norm-one idèle class group** `C¹_K = 𝕀¹_K ⧸ Kˣ` is compact.  The
classical proof exhibits a *compact* set of representatives: there is a finite set `S` of
nonarchimedean places and a constant `C ≥ 1` such that every norm-one idèle can be multiplied by
an element of `Kˣ` into the set of idèles which

* are local units outside `S` (i.e. have `q`-adic norm `1` there),
* are integral at every finite place and bounded below by `C⁻¹` at the places of `S`, and
* have all their archimedean components in the annulus `[C⁻¹, C]`.

This file contains those two sets, together with the basic *content formula* expressing `|x|` for
an idèle which is a local unit outside `S` as a finite product of local absolute values, and a few
elementary closure properties used to assemble the argument.

## Main definitions

* `NK.GlobalCFT.IdeleClassGroup.IsBoundedIntegral`: the finite-place conditions,
* `NK.GlobalCFT.IdeleClassGroup.IsLocallyBounded`: the finite-place conditions together with the
  archimedean annulus,
* `NK.GlobalCFT.IdeleClassGroup.normOneBounded`: the idèles of content one satisfying
  `IsLocallyBounded`.

## Main results

* `NK.GlobalCFT.IdeleClassGroup.abs_val_eq_prod_of_norm_eq_one`: the content formula.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.IdeleClassGroup

variable {K : Type*} [Field K] [NumberField K]

/-- **The finite-place conditions.**  An idèle is *bounded-integral* for a finite set `S` of
nonarchimedean places and a constant `C` if its `q`-adic norm is `1` for `q ∉ S` (i.e. it is a
local unit there), it is integral at every finite place, and it is bounded below by `C⁻¹` at the
places of `S`. -/
def IsBoundedIntegral (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (C : ℝ) (x : Idele K) : Prop :=
  (∀ q, q ∉ S → ‖(x (Place.ofFinite q) : q.adicCompletion K)‖ = 1) ∧
  (∀ q, q ∈ S → C⁻¹ ≤ ‖(x (Place.ofFinite q) : q.adicCompletion K)‖ ∧
    ‖(x (Place.ofFinite q) : q.adicCompletion K)‖ ≤ 1)

/-- **The locally bounded idèles.**  An idèle is locally bounded for `S`, `C` if it satisfies the
finite-place conditions of `IsBoundedIntegral` and if in addition all its archimedean components
lie in the annulus of radii `C⁻¹` and `C`. -/
def IsLocallyBounded (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (C : ℝ) (x : Idele K) : Prop :=
  IsBoundedIntegral K S C x ∧
  ∀ w : InfinitePlace K,
    C⁻¹ ≤ ‖(x (Place.ofInfinite w) : w.Completion)‖ ∧
      ‖(x (Place.ofInfinite w) : w.Completion)‖ ≤ C

/-- The set of norm-one idèles which are locally bounded: the candidate compact set of
representatives for `C¹_K`. -/
def normOneBounded (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (C : ℝ) : Set (Idele K) :=
  {x | IsLocallyBounded K S C x ∧ x ∈ Idele.normOne K}

theorem mem_normOneBounded {S : Finset (HeightOneSpectrum (𝓞 K))} {C : ℝ} {x : Idele K} :
    x ∈ normOneBounded K S C ↔ IsLocallyBounded K S C x ∧ x ∈ Idele.normOne K := Iff.rfl

/-- The content of a principal idèle is one, so the content of an idèle is unchanged by
multiplication with a principal idèle. -/
theorem abs_mul_principalIdele (x : Idele K) (k : Kˣ) :
    Idele.abs K (Idele.principalIdele K k * x) = Idele.abs K x := by
  rw [map_mul, NK.GlobalCFT.IdeleNorm.globalCFT_abs_principalIdele, one_mul]

/-- The membership form of the hypothesis "local unit outside `S`" implies "`q`-adic norm one
outside `S`"; this is the version of the content formula used in the compactness argument. -/
theorem abs_val_eq_prod_of_localUnits {S : Finset (HeightOneSpectrum (𝓞 K))} {x : Idele K}
    (hfin : ∀ q, q ∉ S → x (Place.ofFinite q) ∈ Place.localUnits K (Place.ofFinite q)) :
    ((Idele.abs K x : ℝˣ) : ℝ) =
      (∏ q ∈ S, ‖(x (Place.ofFinite q) : q.adicCompletion K)‖) *
        ∏ w : InfinitePlace K, ‖(x (Place.ofInfinite w) : w.Completion)‖ ^ w.mult := by
  classical
  set T : Finset (Place K) := S.image Place.ofFinite ∪ Finset.univ.image Place.ofInfinite
  have hmul : Function.mulSupport (fun v : Place K => Idele.localAbs K v (x v)) ⊆ T := by
    intro v hv
    by_contra hcon
    have hv1 : v ∉ S.image Place.ofFinite := fun h => hcon (Finset.mem_union_left _ h)
    have hv2 : v ∉ Finset.univ.image Place.ofInfinite := fun h => hcon (Finset.mem_union_right _ h)
    rcases v with w | q
    · exact hv2 (Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩)
    · rw [Function.mem_mulSupport] at hv
      exact hv (by
        rw [Idele.localAbs_ofFinite_eq_one]
        exact hfin q (fun hq => hv1 (Finset.mem_image.mpr ⟨q, hq, rfl⟩)))
  have hdisj : Disjoint (S.image Place.ofFinite) (Finset.univ.image Place.ofInfinite) := by
    rw [Finset.disjoint_left]
    rintro v hv1 hv2
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hv1
    obtain ⟨w, -, hw⟩ := Finset.mem_image.mp hv2
    exact Place.ofInfinite_ne_ofFinite w q hw
  have hval : ((Idele.abs K x : ℝˣ) : ℝ) =
      ((∏ v ∈ T, Idele.localAbs K v (x v) : ℝˣ) : ℝ) := by
    congr 1
    rw [Idele.abs_apply, finprod_eq_prod_of_mulSupport_subset _ hmul]
  have hmap : ((∏ v ∈ T, Idele.localAbs K v (x v) : ℝˣ) : ℝ) =
      ∏ v ∈ T, ((Idele.localAbs K v (x v) : ℝˣ) : ℝ) :=
    map_prod (Units.coeHom ℝ) _ T
  rw [hval, hmap, Finset.prod_union hdisj]
  have h1 : ∀ q ∈ S,
      ((Idele.localAbs K (Place.ofFinite q) (x (Place.ofFinite q)) : ℝˣ) : ℝ) =
        ‖(x (Place.ofFinite q) : q.adicCompletion K)‖ := by
    intro q _
    rw [Idele.localAbs_ofFinite]
    exact Units.val_mk0 _
  have h2 : ∀ w : InfinitePlace K,
      ((Idele.localAbs K (Place.ofInfinite w) (x (Place.ofInfinite w)) : ℝˣ) : ℝ) =
        ‖(x (Place.ofInfinite w) : w.Completion)‖ ^ w.mult := by
    intro w
    rw [Idele.localAbs_ofInfinite, Units.val_pow_eq_pow_val, Units.val_mk0]
  rw [show (∏ v ∈ S.image Place.ofFinite,
        ((Idele.localAbs K v (x v) : ℝˣ) : ℝ)) =
      ∏ q ∈ S, ((Idele.localAbs K (Place.ofFinite q) (x (Place.ofFinite q)) : ℝˣ) : ℝ) from
    Finset.prod_image (fun a _ b _ h => Place.ofFinite_inj.mp h),
    show (∏ v ∈ Finset.univ.image Place.ofInfinite,
        ((Idele.localAbs K v (x v) : ℝˣ) : ℝ)) =
      ∏ w : InfinitePlace K,
        ((Idele.localAbs K (Place.ofInfinite w) (x (Place.ofInfinite w)) : ℝˣ) : ℝ) from
    Finset.prod_image (fun a _ b _ h => Place.ofInfinite_inj.mp h)]
  rw [Finset.prod_congr rfl h1, Finset.prod_congr rfl (fun w _ => h2 w)]

/-- The `q`-adic norm of a local unit at a finite place is one. -/
theorem norm_eq_one_of_mem_localUnits_ofFinite {q : HeightOneSpectrum (𝓞 K)}
    {y : (q.adicCompletion K)ˣ} (hy : y ∈ Place.localUnits K (Place.ofFinite q)) :
    ‖(y : q.adicCompletion K)‖ = 1 := by
  obtain ⟨hy1, hy2⟩ := (Place.mem_localUnits_ofFinite (q := q) (x := y)).mp hy
  have h1 : ‖(y : q.adicCompletion K)‖ ≤ 1 := by
    rw [Valued.toNormedField.norm_le_one_iff]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K q).mp hy1
  have h2 : ‖((y⁻¹ : (q.adicCompletion K)ˣ) : q.adicCompletion K)‖ ≤ 1 := by
    rw [Valued.toNormedField.norm_le_one_iff]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K q).mp hy2
  have hmul : ‖(y : q.adicCompletion K)‖ * ‖((y⁻¹ : (q.adicCompletion K)ˣ) : q.adicCompletion K)‖
      = 1 := by
    rw [← norm_mul]
    simp
  nlinarith [norm_nonneg (y : q.adicCompletion K), norm_nonneg ((y⁻¹ : (q.adicCompletion K)ˣ) : q.adicCompletion K)]

/-- The norm form of the content formula: an idèle whose `q`-adic norm is one outside `S` has
content equal to the product of the norms of its components over `S` and the archimedean
places. -/
theorem abs_val_eq_prod_of_norm_eq_one {S : Finset (HeightOneSpectrum (𝓞 K))} {x : Idele K}
    (h : ∀ q, q ∉ S → ‖(x (Place.ofFinite q) : q.adicCompletion K)‖ = 1) :
    ((Idele.abs K x : ℝˣ) : ℝ) =
      (∏ q ∈ S, ‖(x (Place.ofFinite q) : q.adicCompletion K)‖) *
        ∏ w : InfinitePlace K, ‖(x (Place.ofInfinite w) : w.Completion)‖ ^ w.mult := by
  refine abs_val_eq_prod_of_localUnits (K := K) (S := S) (x := x) (fun q hq => ?_)
  rw [Place.mem_localUnits_ofFinite]
  constructor
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff]
    exact le_of_eq (h q hq)
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff]
    rw [Units.val_inv_eq_inv_val, norm_inv, h q hq, inv_one]

/-- Locally boundedness is monotone in the constant. -/
theorem isBoundedIntegral_mono {S : Finset (HeightOneSpectrum (𝓞 K))} {C C' : ℝ}
    (hC : 0 < C) (h : C ≤ C') {x : Idele K} (hx : IsBoundedIntegral K S C x) :
    IsBoundedIntegral K S C' x := by
  refine ⟨hx.1, fun q hq => ⟨?_, (hx.2 q hq).2⟩⟩
  exact le_trans (inv_anti₀ hC h) (hx.2 q hq).1

/-- Locally boundedness is monotone in the constant. -/
theorem isLocallyBounded_mono {S : Finset (HeightOneSpectrum (𝓞 K))} {C C' : ℝ}
    (hC : 0 < C) (h : C ≤ C') {x : Idele K} (hx : IsLocallyBounded K S C x) :
    IsLocallyBounded K S C' x := by
  refine ⟨isBoundedIntegral_mono hC h hx.1, fun w => ⟨?_, le_trans (hx.2 w).2 h⟩⟩
  exact le_trans (inv_anti₀ hC h) (hx.2 w).1

/-- Multiplying a bounded-integral idèle by an idèle whose finite components all have norm `1`
preserves bounded-integralness. -/
theorem isBoundedIntegral_mul_of_norm_eq_one {S : Finset (HeightOneSpectrum (𝓞 K))} {C : ℝ}
    {y z : Idele K} (hz : ∀ q, ‖(z (Place.ofFinite q) : q.adicCompletion K)‖ = 1)
    (hy : IsBoundedIntegral K S C y) : IsBoundedIntegral K S C (z * y) := by
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · rw [NK.GlobalCFT.Idele.mul_apply, Units.val_mul, norm_mul, hz q, hy.1 q hq, one_mul]
  · rw [NK.GlobalCFT.Idele.mul_apply, Units.val_mul, norm_mul, hz q, one_mul]
    exact hy.2 q hq

end NK.GlobalCFT.IdeleClassGroup
