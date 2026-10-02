import Mathlib
import Submission.Work.ThomBordism.Grassmann.deg8Prelude
import Submission.Work.ThomBordism.Grassmann.deg8PathConnectedOG
import Submission.Work.ThomBordism.Grassmann.deg8RankZero
import Submission.Work.ThomBordism.Grassmann.eulerClassOddRank
import Submission.Work.ThomBordism.Grassmann.incidenceFibreCohomologyRat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-!
# The degree-eight rational cohomology of the oriented Grassmannian is at most two-dimensional

Target: `Work.ThomBordism.Grassmann.degreeEightFinrankLeTwo`:
for `k, m ≥ 10`, `finrank ℚ (H⁸(G̃r_k(ℝ^{k+m});ℚ)) ≤ 2`.

## The route (the Borel computation in degree 8)

Write `γ_k^m = tautologicalBundle k m` for the tautological oriented `k`-plane bundle over
`G_k := G̃r_k(ℝ^{k+m}) = OG k m`, and `S(γ_k^m) = zeroComplement (γ_k^m)` for its sphere bundle.
The three inputs are

* the **Gysin window** at source degree `a ≥ 0` (`Deg8.win_le`, `Deg8.win_odd_le`),
* the **incidence step** `H^j(S γ_k;ℚ) ≅ H^j(G_{k-1};ℚ)` (`Deg8.rank_S_eq_R`),
* the **degenerate window** `H^{k-1}(S γ_k;ℚ) = H^{k-1}(G_k;ℚ) ⊕ H^0(G_k;ℚ)` for odd `k`
  (`Deg8.rank_S_degen`, below), the source degree `-1` case.

The resulting chain for fixed `m ≥ 10` is

* `rank H⁸(G_9) + 1 = rank H⁸(G_8)` (degenerate, `k = 9`, `rank H⁰(G_9) = 1`),
* `rank H⁸(G_8) ≤ 1 + rank H⁸(G_7)`, `rank H⁸(G_7) ≤ rank H⁸(G_6)`,
* `rank H⁸(G_6) ≤ rank H²(G_6) + rank H⁸(G_5) = rank H⁸(G_5)`,
* `rank H⁸(G_5) + rank H⁴(G_5) ≤ rank H⁸(G_4)`,
* `rank H⁸(G_4) ≤ rank H⁴(G_4) + rank H⁸(G_3)`, `rank H⁸(G_3) ≤ 1`,
* `rank H⁴(G_4) = rank H⁴(G_5) + 1` (degenerate, `k = 5`),

whence `rank H⁸(G_9) + rank H⁴(G_5) ≤ rank H⁴(G_5) + 2`, i.e. `rank H⁸(G_9) ≤ 2`.
The degree-`2`/`4` inputs come from the same windows at `k = 2, 3`, and `H²(G_6) = 0` from the
degenerate window at `k = 3` followed by the stable-range steps.

Everything is carried out with `Module.rank` (cardinal-valued) so that no finiteness hypothesis on
the cohomology of `OG k m` is needed; the final step converts `rank ≤ 2` into `finrank ≤ 2` via
`Module.finrank_le_of_rank_le`.
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

open scoped TensorProduct

noncomputable section

namespace Deg8

/-- **Base change commutes with composition.** -/
theorem baseChange_comp {R A M N P : Type*} [CommRing R] [Semiring A] [Algebra R A]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N] [Module R P]
    (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    (g.comp f).baseChange A = (g.baseChange A).comp (f.baseChange A) := by
  refine LinearMap.ext fun x => ?_
  refine TensorProduct.induction_on
    (motive := fun x => (g.comp f).baseChange A x = ((g.baseChange A).comp (f.baseChange A)) x)
    x ?_ ?_ ?_
  · simp
  · intro a x
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul]
  · intro x y hx hy
    simp only [map_add, hx, hy]

/-! ## The weak odd-degree step -/

/-- **Weak odd step**: for odd `k` the Euler class of `γ_k` is rationally zero, so the rationalized
Gysin map `π^* : H^j(G_k;ℚ) → H^j(S γ_k;ℚ)` is injective, and hence
`rank H^j(G_k) ≤ rank H^j(S γ_k) = rank H^j(G_{k-1})`. -/
theorem rank_le_of_odd (m j k : ℕ) (hk1 : 1 ≤ k) (hk : Odd k) (hj1 : 1 ≤ j)
    (hj : j ≤ k + m - 3) :
    Module.rank ℚ (R m j k) ≤ Module.rank ℚ (R m j (k - 1)) := by
  have hT : (2 : ℤ) • (tautologicalThomClass k m).eulerClass = 0 :=
    eulerClassOddRank (tautologicalBundle k m) (by simp [RealBundle.rank])
      (tautologicalThomClass k m) hk
  have hle : Module.rank ℚ (R m j k) ≤ Module.rank ℚ (S m j k) := by
    by_cases hjk : j < k
    · have h0 : Function.Injective (Work.Thom.gysinπ (tautologicalBundle k m) j) :=
        injective_gysinπ_tautological k m j hjk
      have h1 : Function.Injective ((Work.Thom.gysinπ (tautologicalBundle k m) j).lTensor ℚ) :=
        Module.Flat.lTensor_preserves_injective_linearMap _ h0
      rw [← LinearMap.baseChange_eq_ltensor] at h1
      change Module.rank ℚ (ℚ ⊗[ℤ] ↑(Work.Thom.Coh ℤ j (OG k m)))
        ≤ Module.rank ℚ (ℚ ⊗[ℤ] ↑(Work.Thom.Coh ℤ j
          (Work.Thom.zeroComplement (tautologicalBundle k m))))
      rw [← rank_range_of_injective _ h1]
      exact Submodule.rank_le _
    · push Not at hjk
      have hvan : gysinEulerQ (tautologicalBundle k m) k (tautologicalThomClass k m) (j - k) = 0 :=
        gysinEulerQ_eq_zero_of_two_zsmul _ k (j - k) _ hT
      have hex := gysin_exact_at_base_rat (tautologicalBundle k m) k
        (tautologicalThomClass k m) (j - k)
      rw [LinearMap.exact_iff] at hex
      have hker : LinearMap.ker (gysinπQ (tautologicalBundle k m) ((j - k) + k)) = ⊥ := by
        rw [hex, hvan, LinearMap.range_zero]
      have h1 : Function.Injective (gysinπQ (tautologicalBundle k m) ((j - k) + k)) :=
        LinearMap.ker_eq_bot.mp hker
      rw [Nat.sub_add_cancel hjk] at h1
      change Module.rank ℚ (ℚ ⊗[ℤ] ↑(Work.Thom.Coh ℤ j (OG k m)))
        ≤ Module.rank ℚ (ℚ ⊗[ℤ] ↑(Work.Thom.Coh ℤ j
          (Work.Thom.zeroComplement (tautologicalBundle k m))))
      rw [← rank_range_of_injective _ h1]
      exact Submodule.rank_le _
  rwa [rank_S_eq_R k m j hk1 hj1 hj] at hle

/-! ## The degree-zero and degree-one inputs -/

/-- `H^0(G_k;ℚ)` is one-dimensional (`OG k m` is path connected for `1 ≤ m`). -/
theorem rank_zero_eq_one (k m : ℕ) (hm : 1 ≤ m) : Module.rank ℚ (R m 0 k) = 1 := by
  haveI : PathConnectedSpace (OG k m) := deg8PathConnectedOG k m hm
  exact deg8RankZero (OG k m)

/-- `H^j(OG 0 m;ℚ) = 0` for `j ≥ 1` (`OG 0 m` is a point). -/
theorem rank_OG_zero_eq_zero (m j : ℕ) (hj : 1 ≤ j) :
    Module.rank ℚ (R m j 0) = 0 := by
  haveI hsub : Subsingleton (Work.Thom.Coh ℤ j (OG 0 m)) :=
    (ModuleCat.isZero_iff_subsingleton).mp (isZero_cohomology_OG_zero m j hj)
  haveI hsubT : Subsingleton (ℚ ⊗[ℤ] ↑(Work.Thom.Coh ℤ j (OG 0 m))) := inferInstance
  rw [rank_eq_zero_iff]
  intro x
  exact ⟨1, one_ne_zero, by rw [@Subsingleton.elim _ hsubT x 0, smul_zero]⟩

/-- **The sphere bundle of the tautological line bundle**: `H^j(S γ_1;ℚ) = 0` for `j ≥ 1`, by the
incidence step at `k = 1`. -/
theorem rank_S_one_eq_zero (m j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ m - 2) :
    Module.rank ℚ (S m j 1) = 0 := by
  rw [rank_S_eq_R 1 m j (by norm_num) hj1 (by omega)]
  exact rank_OG_zero_eq_zero m j hj1

/-- **`H^j(G_1;ℚ) = 0` for `1 ≤ j`**: the `k = 1` case of the odd window shows
`2 · rank H^j(G_1) ≤ rank H^j(S γ_1) = 0`. -/
theorem rank_one_eq_zero (m j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ m - 2) :
    Module.rank ℚ (R m j 1) = 0 := by
  have hT : (2 : ℤ) • (tautologicalThomClass 1 m).eulerClass = 0 :=
    eulerClassOddRank (tautologicalBundle 1 m) (by simp [RealBundle.rank])
      (tautologicalThomClass 1 m) (by norm_num)
  have h := win_odd_le (tautologicalBundle 1 m) 1 (j - 1) (tautologicalThomClass 1 m) hT
  rw [Nat.sub_add_cancel hj1] at h
  have h0 : Module.rank ℚ (S m j 1) = 0 := rank_S_one_eq_zero m j hj1 hj
  have h2 : Module.rank ℚ (R m j 1) + Module.rank ℚ (R m j 1) ≤ (0 : Cardinal) :=
    le_trans h (le_of_eq h0)
  have hle : Module.rank ℚ (R m j 1) ≤ 0 := by
    have h3 : Module.rank ℚ (R m j 1) ≤ Module.rank ℚ (R m j 1) + Module.rank ℚ (R m j 1) := by
      calc Module.rank ℚ (R m j 1) = Module.rank ℚ (R m j 1) + 0 := (add_zero _).symm
        _ ≤ Module.rank ℚ (R m j 1) + Module.rank ℚ (R m j 1) :=
            add_le_add le_rfl (zero_le : (0 : Cardinal) ≤ Module.rank ℚ (R m j 1))
    exact le_trans h3 h2
  exact le_antisymm hle (zero_le)

/-! ## The degenerate window -/

/-- **The degenerate window** (source degree `-1`).  For odd `k ≥ 2` the rationalized `∪e` vanishes
(`Deg8.gysinEulerQ_eq_zero_of_two_zsmul`) and the rationalization of the long exact sequence of the
pair `(E, E∖0)` gives the short exact sequence

  `0 → H^{k-1}(G_k;ℚ) → H^{k-1}(S γ_k;ℚ) → H^0(G_k;ℚ) → 0`,

hence `rank H^{k-1}(S γ_k) = rank H^{k-1}(G_k) + rank H^0(G_k)`. -/
theorem rank_S_degen (k m : ℕ) (hk1 : 2 ≤ k) (hk : Odd k) :
    Module.rank ℚ (S m (k - 1) k)
      = Module.rank ℚ (R m (k - 1) k) + Module.rank ℚ (R m 0 k) := by
  have hT : (2 : ℤ) • (tautologicalThomClass k m).eulerClass = 0 :=
    eulerClassOddRank (tautologicalBundle k m) (by simp [RealBundle.rank])
      (tautologicalThomClass k m) hk
  -- the integral exactness at `H^{k-1}(S γ_k)`
  have hex : Function.Exact (Work.Thom.gysinπ (tautologicalBundle k m) (k - 1))
      (Work.Thom.pairδC (Work.Thom.zeroComplement (tautologicalBundle k m)) (k - 1)).hom := by
    rw [LinearMap.exact_iff]
    have hrange : LinearMap.range (Work.Thom.gysinπ (tautologicalBundle k m) (k - 1))
        = LinearMap.range ((Work.Thom.restrCoh (Work.Thom.zeroComplement (tautologicalBundle k m))
            ℤ (k - 1)).hom) := by
      have hcomp : Work.Thom.gysinπ (tautologicalBundle k m) (k - 1)
          = ((Work.Thom.restrCoh (Work.Thom.zeroComplement (tautologicalBundle k m)) ℤ (k-1)).hom).comp
            ((Work.Thom.CohMap (Work.Thom.bundleProj (tautologicalBundle k m)) ℤ (k-1)).hom) := rfl
      rw [hcomp, LinearMap.range_comp]
      rw [LinearMap.range_eq_top.mpr (Work.Thom.bijective_CohMap_bundleProj _ (k-1)).2]
      exact Submodule.map_top _
    rw [hrange]
    exact (Work.Thom.pairRange_eq_ker₃ (Work.Thom.zeroComplement (tautologicalBundle k m))
      (k - 1)).symm
  -- `relToAbs` vanishes rationally, from the vanishing of `∪e` in degree `0`
  have hrel0 : (Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement (tautologicalBundle k m))
      (0 + k)).hom.baseChange ℚ = 0 := by
    have hvan : (Work.Thom.gysinEuler (tautologicalThomClass k m) 0).baseChange ℚ = 0 :=
      gysinEulerQ_eq_zero_of_two_zsmul (tautologicalBundle k m) k 0 _ hT
    have hcomp : (Work.Thom.gysinEuler (tautologicalThomClass k m) 0).baseChange ℚ
        = (((Work.Thom.CohMap (Work.Thom.zeroSection (tautologicalBundle k m)) ℤ (0+k)).hom).baseChange ℚ).comp
          ((((Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement (tautologicalBundle k m))
            (0+k)).hom).baseChange ℚ).comp
            ((Work.Thom.thomMap (tautologicalBundle k m) k (tautologicalThomClass k m).τ 0).baseChange ℚ)) := by
      rw [show Work.Thom.gysinEuler (tautologicalThomClass k m) 0
          = ((Work.Thom.CohMap (Work.Thom.zeroSection (tautologicalBundle k m)) ℤ (0+k)).hom).comp
            (((Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement (tautologicalBundle k m)) (0+k)).hom).comp
              (Work.Thom.thomMap (tautologicalBundle k m) k (tautologicalThomClass k m).τ 0)) from rfl]
      rw [baseChange_comp, baseChange_comp]
    have hzero : (((Work.Thom.CohMap (Work.Thom.zeroSection (tautologicalBundle k m)) ℤ (0+k)).hom).baseChange ℚ).comp
          ((((Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement (tautologicalBundle k m)) (0+k)).hom).baseChange ℚ).comp
            ((Work.Thom.thomMap (tautologicalBundle k m) k (tautologicalThomClass k m).τ 0).baseChange ℚ)) = 0 := by
      rw [← hcomp]; exact hvan
    have hinjC : Function.Injective
        (((Work.Thom.CohMap (Work.Thom.zeroSection (tautologicalBundle k m)) ℤ (0+k)).hom).baseChange ℚ) := by
      have hinj : Function.Injective
          ((Work.Thom.CohMap (Work.Thom.zeroSection (tautologicalBundle k m)) ℤ (0+k)).hom) := by
        intro a b hab
        obtain ⟨a', ha'⟩ := (Work.Thom.bijective_CohMap_bundleProj (tautologicalBundle k m) (0+k)).2 a
        obtain ⟨b', hb'⟩ := (Work.Thom.bijective_CohMap_bundleProj (tautologicalBundle k m) (0+k)).2 b
        have hleft := Work.Thom.CohMap_zeroSection_comp_bundleProj (tautologicalBundle k m) (0+k)
        have ha'' : (Work.Thom.CohMap (Work.Thom.zeroSection (tautologicalBundle k m)) ℤ (0+k)).hom a
            = a' := by
          rw [← ha']; exact LinearMap.congr_fun hleft a'
        have hb'' : (Work.Thom.CohMap (Work.Thom.zeroSection (tautologicalBundle k m)) ℤ (0+k)).hom b
            = b' := by
          rw [← hb']; exact LinearMap.congr_fun hleft b'
        rw [ha'', hb''] at hab
        rw [← ha', ← hb', hab]
      have h2 : Function.Injective
          (((Work.Thom.CohMap (Work.Thom.zeroSection (tautologicalBundle k m)) ℤ (0+k)).hom).lTensor ℚ) :=
        Module.Flat.lTensor_preserves_injective_linearMap _ hinj
      rwa [← LinearMap.baseChange_eq_ltensor] at h2
    have hsurjTh : Function.Surjective
        ((Work.Thom.thomMap (tautologicalBundle k m) k (tautologicalThomClass k m).τ 0).baseChange ℚ) :=
      (LinearEquiv.baseChange ℤ ℚ _ _ ((tautologicalThomClass k m).thomEquiv 0)).surjective
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hsurjTh y
    have h1 : (((Work.Thom.CohMap (Work.Thom.zeroSection (tautologicalBundle k m)) ℤ (0+k)).hom).baseChange ℚ)
        ((((Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement (tautologicalBundle k m)) (0+k)).hom).baseChange ℚ)
          (((Work.Thom.thomMap (tautologicalBundle k m) k (tautologicalThomClass k m).τ 0).baseChange ℚ) x)) = 0 := by
      have hh := congrArg (fun f => f x) hzero
      simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hh
    refine hinjC ?_
    exact h1.trans (map_zero _).symm
  have hrel : (Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement (tautologicalBundle k m))
      ((k - 1) + 1)).hom.baseChange ℚ = 0 := by
    rw [show (k - 1) + 1 = 0 + k from by omega]
    exact hrel0
  have hsurjδ : Function.Surjective
      ((Work.Thom.pairδC (Work.Thom.zeroComplement (tautologicalBundle k m)) (k - 1)).hom.baseChange ℚ) := by
    rw [← LinearMap.range_eq_top]
    have hex2 : Function.Exact
        (Work.Thom.pairδC (Work.Thom.zeroComplement (tautologicalBundle k m)) (k - 1)).hom
        (Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement (tautologicalBundle k m)) ((k - 1) + 1)).hom := by
      rw [LinearMap.exact_iff]
      exact (Work.Thom.pairδC_ker_le (Work.Thom.zeroComplement (tautologicalBundle k m)) (k - 1)).symm
    have h2 := Module.Flat.lTensor_exact ℚ hex2
    rw [← LinearMap.baseChange_eq_ltensor, ← LinearMap.baseChange_eq_ltensor] at h2
    rw [LinearMap.exact_iff] at h2
    rw [← h2, hrel, LinearMap.ker_zero]
  have hinjπ : Function.Injective (gysinπQ (tautologicalBundle k m) (k - 1)) := by
    have h0 : Function.Injective (Work.Thom.gysinπ (tautologicalBundle k m) (k - 1)) :=
      injective_gysinπ_tautological k m (k - 1) (by omega)
    have h2 : Function.Injective ((Work.Thom.gysinπ (tautologicalBundle k m) (k - 1)).lTensor ℚ) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ h0
    rwa [← LinearMap.baseChange_eq_ltensor] at h2
  have hexR : Function.Exact (gysinπQ (tautologicalBundle k m) (k - 1))
      ((Work.Thom.pairδC (Work.Thom.zeroComplement (tautologicalBundle k m)) (k - 1)).hom.baseChange ℚ) := by
    have h2 := Module.Flat.lTensor_exact ℚ hex
    rwa [← LinearMap.baseChange_eq_ltensor, ← LinearMap.baseChange_eq_ltensor] at h2
  have hO : Module.rank ℚ (ℚ ⊗[ℤ] (Work.Thom.OpenThom (tautologicalBundle k m) ((k - 1) + 1) : Type))
      = Module.rank ℚ (R m 0 k) := by
    rw [show (k - 1) + 1 = 0 + k from by omega]
    exact (LinearEquiv.baseChange ℤ ℚ _ _
      ((tautologicalThomClass k m).thomEquiv 0)).rank_eq.symm
  have hge : Module.rank ℚ (R m (k - 1) k) + Module.rank ℚ (R m 0 k)
      ≤ Module.rank ℚ (S m (k - 1) k) := by
    have h := rank_add_le_of_shortExact (gysinπQ (tautologicalBundle k m) (k - 1))
      ((Work.Thom.pairδC (Work.Thom.zeroComplement (tautologicalBundle k m)) (k - 1)).hom.baseChange ℚ)
      hinjπ hsurjδ hexR
    rw [hO] at h
    exact h
  have hle : Module.rank ℚ (S m (k - 1) k) ≤ Module.rank ℚ (R m (k - 1) k) + Module.rank ℚ (R m 0 k) := by
    have h := rank_le_add_of_shortExact (gysinπQ (tautologicalBundle k m) (k - 1))
      ((Work.Thom.pairδC (Work.Thom.zeroComplement (tautologicalBundle k m)) (k - 1)).hom.baseChange ℚ)
      hinjπ hexR
    rw [hO] at h
    exact h
  exact le_antisymm hle hge

/-! ## The degree-eight chain -/

/-- **The degree-eight chain.**  For `m ≥ 10`, `rank H⁸(G̃r_9(ℝ^{9+m});ℚ) ≤ 2`. -/
theorem degreeEight_finrank_nine_le_two (m : ℕ) (hm : 10 ≤ m) :
    Module.finrank ℚ (Work.SignatureBordism.ratCohomology 8 (sset (OG 9 m))) ≤ 2 := by
  apply Module.finrank_le_of_rank_le
  -- Euler classes of the odd-rank tautological bundles
  have hT9 : (2 : ℤ) • (tautologicalThomClass 9 m).eulerClass = 0 :=
    eulerClassOddRank (tautologicalBundle 9 m) (by simp [RealBundle.rank])
      (tautologicalThomClass 9 m) (by norm_num)
  have hT5 : (2 : ℤ) • (tautologicalThomClass 5 m).eulerClass = 0 :=
    eulerClassOddRank (tautologicalBundle 5 m) (by simp [RealBundle.rank])
      (tautologicalThomClass 5 m) (by norm_num)
  have hT3 : (2 : ℤ) • (tautologicalThomClass 3 m).eulerClass = 0 :=
    eulerClassOddRank (tautologicalBundle 3 m) (by simp [RealBundle.rank])
      (tautologicalThomClass 3 m) (by norm_num)
  -- auxiliary rank zero and one values
  have hR1 : ∀ j : ℕ, 1 ≤ j → j ≤ 8 → Module.rank ℚ (R m j 1) = 0 :=
    fun j hj _ => rank_one_eq_zero m j hj (by omega)
  have hV : ∀ k : ℕ, Module.rank ℚ (R m 0 k) = 1 := fun k => rank_zero_eq_one k m (by omega)
  -- the incidence steps
  have hi98 : Module.rank ℚ (S m 8 9) = Module.rank ℚ (R m 8 8) :=
    rank_S_eq_R 9 m 8 (by norm_num) (by norm_num) (by omega)
  have hi86 : Module.rank ℚ (S m 8 6) = Module.rank ℚ (R m 8 5) :=
    rank_S_eq_R 6 m 8 (by norm_num) (by norm_num) (by omega)
  have hi84 : Module.rank ℚ (S m 8 4) = Module.rank ℚ (R m 8 3) :=
    rank_S_eq_R 4 m 8 (by norm_num) (by norm_num) (by omega)
  have hi85 : Module.rank ℚ (S m 8 5) = Module.rank ℚ (R m 8 4) :=
    rank_S_eq_R 5 m 8 (by norm_num) (by norm_num) (by omega)
  have hi45 : Module.rank ℚ (S m 4 5) = Module.rank ℚ (R m 4 4) :=
    rank_S_eq_R 5 m 4 (by norm_num) (by norm_num) (by omega)
  have hi41 : Module.rank ℚ (S m 4 1) = Module.rank ℚ (R m 4 0) :=
    rank_S_eq_R 1 m 4 (by norm_num) (by norm_num) (by omega)
  have hi21 : Module.rank ℚ (S m 2 1) = Module.rank ℚ (R m 2 0) :=
    rank_S_eq_R 1 m 2 (by norm_num) (by norm_num) (by omega)
  have hi22 : Module.rank ℚ (S m 2 2) = Module.rank ℚ (R m 2 1) :=
    rank_S_eq_R 2 m 2 (by norm_num) (by norm_num) (by omega)
  have hi42 : Module.rank ℚ (S m 4 2) = Module.rank ℚ (R m 4 1) :=
    rank_S_eq_R 2 m 4 (by norm_num) (by norm_num) (by omega)
  have hi62 : Module.rank ℚ (S m 6 2) = Module.rank ℚ (R m 6 1) :=
    rank_S_eq_R 2 m 6 (by norm_num) (by norm_num) (by omega)
  have hi82 : Module.rank ℚ (S m 8 2) = Module.rank ℚ (R m 8 1) :=
    rank_S_eq_R 2 m 8 (by norm_num) (by norm_num) (by omega)
  have hi23 : Module.rank ℚ (S m 2 3) = Module.rank ℚ (R m 2 2) :=
    rank_S_eq_R 3 m 2 (by norm_num) (by norm_num) (by omega)
  have hi44 : Module.rank ℚ (S m 4 4) = Module.rank ℚ (R m 4 3) :=
    rank_S_eq_R 4 m 4 (by norm_num) (by norm_num) (by omega)
  -- the degree-two vanishing
  have h22 : Module.rank ℚ (R m 2 2) ≤ 1 := by
    calc Module.rank ℚ (R m 2 2)
        ≤ Module.rank ℚ (R m 0 2) + Module.rank ℚ (S m 2 2) := win_le 2 m 2 le_rfl
      _ = Module.rank ℚ (R m 0 2) + Module.rank ℚ (R m 2 1) := by rw [hi22]
      _ = Module.rank ℚ (R m 0 2) := by rw [hR1 2 (by norm_num) (by norm_num), add_zero]
      _ = 1 := hV 2
  have h23 : Module.rank ℚ (R m 2 3) = 0 := by
    have hd := rank_S_degen 3 m (by norm_num) (by norm_num)
    rw [hi23] at hd
    have h0 : Module.rank ℚ (R m 0 3) = 1 := hV 3
    rw [h0] at hd
    have hthis : Module.rank ℚ (R m 2 3) + 1 ≤ (0 : Cardinal) + 1 := by
      rw [zero_add]
      calc Module.rank ℚ (R m 2 3) + 1 = Module.rank ℚ (R m 2 2) := hd.symm
        _ ≤ 1 := h22
    have hle : Module.rank ℚ (R m 2 3) ≤ 0 :=
      (Cardinal.add_le_add_iff_of_lt_aleph0 (γ := (1 : Cardinal)) (by norm_num)).mp hthis
    exact le_antisymm hle (zero_le)
  -- the descent for degree two
  have hd42 : Module.rank ℚ (R m 2 4) = Module.rank ℚ (R m 2 3) := by
    rw [rank_eq_of_descent 4 m 2 (by norm_num), rank_S_eq_R 4 m 2 (by norm_num) (by norm_num) (by omega)]
  have hd52 : Module.rank ℚ (R m 2 5) = Module.rank ℚ (R m 2 4) := by
    rw [rank_eq_of_descent 5 m 2 (by norm_num), rank_S_eq_R 5 m 2 (by norm_num) (by norm_num) (by omega)]
  have hd62 : Module.rank ℚ (R m 2 6) = Module.rank ℚ (R m 2 5) := by
    rw [rank_eq_of_descent 6 m 2 (by norm_num), rank_S_eq_R 6 m 2 (by norm_num) (by norm_num) (by omega)]
  have h26 : Module.rank ℚ (R m 2 6) = 0 := by rw [hd62, hd52, hd42, h23]
  -- the degree-four and degree-eight bounds
  have h42 : Module.rank ℚ (R m 4 2) ≤ 1 := by
    calc Module.rank ℚ (R m 4 2)
        ≤ Module.rank ℚ (R m 2 2) + Module.rank ℚ (S m 4 2) := win_le 2 m 4 (by norm_num)
      _ = Module.rank ℚ (R m 2 2) + Module.rank ℚ (R m 4 1) := by rw [hi42]
      _ = Module.rank ℚ (R m 2 2) := by rw [hR1 4 (by norm_num) (by norm_num), add_zero]
      _ ≤ 1 := h22
  have h43 : Module.rank ℚ (R m 4 3) ≤ 1 := by
    calc Module.rank ℚ (R m 4 3) ≤ Module.rank ℚ (R m 4 2) :=
          rank_le_of_odd m 4 3 (by norm_num) (by norm_num) (by norm_num) (by omega)
      _ ≤ 1 := h42
  have h44 : Module.rank ℚ (R m 4 4) ≤ 2 := by
    calc Module.rank ℚ (R m 4 4)
        ≤ Module.rank ℚ (R m 0 4) + Module.rank ℚ (S m 4 4) := win_le 4 m 4 le_rfl
      _ = Module.rank ℚ (R m 0 4) + Module.rank ℚ (R m 4 3) := by rw [hi44]
      _ = 1 + Module.rank ℚ (R m 4 3) := by rw [hV 4]
      _ ≤ 2 := by
          have := h43
          rw [show (2 : Cardinal) = 1 + 1 from by norm_num]
          exact add_le_add le_rfl this
  have h45 : Module.rank ℚ (R m 4 5) ≤ 1 := by
    have hd := rank_S_degen 5 m (by norm_num) (by norm_num)
    rw [hi45] at hd
    rw [hV 5] at hd
    have hthis : Module.rank ℚ (R m 4 5) + 1 ≤ (1 : Cardinal) + 1 := by
      rw [show (1 : Cardinal) + 1 = 2 from by norm_num, ← hd]
      exact h44
    exact (Cardinal.add_le_add_iff_of_lt_aleph0 (γ := (1 : Cardinal)) (by norm_num)).mp hthis
  have h83 : Module.rank ℚ (R m 8 3) ≤ 1 := by
    calc Module.rank ℚ (R m 8 3) ≤ Module.rank ℚ (R m 8 2) :=
          rank_le_of_odd m 8 3 (by norm_num) (by norm_num) (by norm_num) (by omega)
      _ ≤ Module.rank ℚ (R m 6 2) + Module.rank ℚ (S m 8 2) := win_le 2 m 8 (by norm_num)
      _ = Module.rank ℚ (R m 6 2) + Module.rank ℚ (R m 8 1) := by rw [hi82]
      _ = Module.rank ℚ (R m 6 2) := by rw [hR1 8 (by norm_num) (by norm_num), add_zero]
      _ ≤ Module.rank ℚ (R m 4 2) + Module.rank ℚ (S m 6 2) := win_le 2 m 6 (by norm_num)
      _ = Module.rank ℚ (R m 4 2) + Module.rank ℚ (R m 6 1) := by rw [hi62]
      _ = Module.rank ℚ (R m 4 2) := by rw [hR1 6 (by norm_num) (by norm_num), add_zero]
      _ ≤ 1 := h42
  -- the successive bounds
  have h98 : Module.rank ℚ (R m 8 9) + 1 = Module.rank ℚ (R m 8 8) := by
    have hd := rank_S_degen 9 m (by norm_num) (by norm_num)
    rw [hi98, hV 9] at hd
    exact hd.symm
  have h88 : Module.rank ℚ (R m 8 8) ≤ 1 + Module.rank ℚ (R m 8 7) := by
    calc Module.rank ℚ (R m 8 8)
        ≤ Module.rank ℚ (R m 0 8) + Module.rank ℚ (S m 8 8) := win_le 8 m 8 le_rfl
      _ = Module.rank ℚ (R m 0 8) + Module.rank ℚ (R m 8 7) := by rw [rank_S_eq_R 8 m 8 (by norm_num) (by norm_num) (by omega)]
      _ = 1 + Module.rank ℚ (R m 8 7) := by rw [hV 8]
  have h87 : Module.rank ℚ (R m 8 7) ≤ Module.rank ℚ (R m 8 6) :=
    rank_le_of_odd m 8 7 (by norm_num) (by norm_num) (by norm_num) (by omega)
  have h86 : Module.rank ℚ (R m 8 6) ≤ Module.rank ℚ (R m 8 5) := by
    calc Module.rank ℚ (R m 8 6)
        ≤ Module.rank ℚ (R m 2 6) + Module.rank ℚ (S m 8 6) := win_le 6 m 8 (by norm_num)
      _ = Module.rank ℚ (R m 2 6) + Module.rank ℚ (R m 8 5) := by rw [hi86]
      _ = Module.rank ℚ (R m 8 5) := by rw [h26, zero_add]
  have h85 : Module.rank ℚ (R m 8 5) + Module.rank ℚ (R m 4 5) ≤ Module.rank ℚ (R m 8 4) := by
    have h : Module.rank ℚ (R m 8 5) + Module.rank ℚ (R m 4 5) ≤ Module.rank ℚ (S m 8 5) :=
      win_odd_le (tautologicalBundle 5 m) 5 3 (tautologicalThomClass 5 m) hT5
    rw [hi85] at h
    exact h
  have h84 : Module.rank ℚ (R m 8 4) ≤ Module.rank ℚ (R m 4 4) + Module.rank ℚ (R m 8 3) := by
    calc Module.rank ℚ (R m 8 4)
        ≤ Module.rank ℚ (R m 4 4) + Module.rank ℚ (S m 8 4) := win_le 4 m 8 (by norm_num)
      _ = Module.rank ℚ (R m 4 4) + Module.rank ℚ (R m 8 3) := by rw [hi84]
  have h445 : Module.rank ℚ (R m 4 4) = Module.rank ℚ (R m 4 5) + 1 := by
    have hd := rank_S_degen 5 m (by norm_num) (by norm_num)
    rw [hi45, hV 5] at hd
    exact hd
  -- the chain
  have hchain : Module.rank ℚ (R m 8 9) + Module.rank ℚ (R m 4 5)
      ≤ 2 + Module.rank ℚ (R m 4 5) := by
    have h95 : Module.rank ℚ (R m 8 9) ≤ Module.rank ℚ (R m 8 5) := by
      have hstep : Module.rank ℚ (R m 8 9) + 1 ≤ Module.rank ℚ (R m 8 5) + 1 := by
        calc Module.rank ℚ (R m 8 9) + 1 = Module.rank ℚ (R m 8 8) := h98
          _ ≤ 1 + Module.rank ℚ (R m 8 7) := h88
          _ ≤ 1 + Module.rank ℚ (R m 8 6) := add_le_add le_rfl h87
          _ ≤ 1 + Module.rank ℚ (R m 8 5) := add_le_add le_rfl h86
          _ = Module.rank ℚ (R m 8 5) + 1 := add_comm _ _
      exact (Cardinal.add_le_add_iff_of_lt_aleph0 (γ := (1 : Cardinal)) (by norm_num)).mp hstep
    calc Module.rank ℚ (R m 8 9) + Module.rank ℚ (R m 4 5)
        ≤ Module.rank ℚ (R m 8 5) + Module.rank ℚ (R m 4 5) := add_le_add h95 le_rfl
      _ ≤ Module.rank ℚ (R m 8 4) := h85
      _ ≤ Module.rank ℚ (R m 4 4) + Module.rank ℚ (R m 8 3) := h84
      _ = (Module.rank ℚ (R m 4 5) + 1) + Module.rank ℚ (R m 8 3) := by rw [h445]
      _ ≤ (Module.rank ℚ (R m 4 5) + 1) + 1 := add_le_add le_rfl h83
      _ = 2 + Module.rank ℚ (R m 4 5) := by
          rw [add_assoc, show (1 : Cardinal) + 1 = 2 from by norm_num, add_comm]
  exact (Cardinal.add_le_add_iff_of_lt_aleph0 (γ := Module.rank ℚ (R m 4 5))
    (lt_of_le_of_lt h45 (by norm_num))).mp hchain

/-- **The `k`-reduction step.**  For `k ≥ 10` the degree-eight rational cohomology of
`G̃r_k(ℝ^{k+m})` has the same dimension as that of `G̃r_{k-1}(ℝ^{k+m})`: the Gysin descent plus the
incidence step. -/
theorem finrank_degreeEight_succ (k m : ℕ) (hk : 10 ≤ k) (hm : 10 ≤ m) :
    Module.finrank ℚ (Work.SignatureBordism.ratCohomology 8 (sset (OG k m))) =
      Module.finrank ℚ (Work.SignatureBordism.ratCohomology 8 (sset (OG (k-1) m))) := by
  have hbij := gysinπ_tautological_bijective k m 8 (by omega)
  have e1 : (Work.Thom.Coh ℤ 8 (OG k m)) ≃ₗ[ℤ]
      (Work.Thom.Coh ℤ 8 (Work.Thom.zeroComplement (tautologicalBundle k m))) :=
    LinearEquiv.ofBijective _ hbij
  obtain ⟨e2⟩ := incidenceFibreCohomologyRat k m 8 (by omega) (by norm_num) (by omega)
  calc Module.finrank ℚ (ℚ ⊗[ℤ] (Work.Thom.Coh ℤ 8 (OG k m) : Type))
      = Module.finrank ℚ (ℚ ⊗[ℤ] (Work.Thom.Coh ℤ 8
          (Work.Thom.zeroComplement (tautologicalBundle k m)) : Type)) :=
        (LinearEquiv.baseChange ℤ ℚ _ _ e1).finrank_eq
    _ = Module.finrank ℚ (ℚ ⊗[ℤ] (Work.Thom.Coh ℤ 8 (OG (k-1) m) : Type)) := e2.finrank_eq

/-- **The `k`-reduction**: for `k ≥ 9` (and `m ≥ 10`) the degree-eight rational cohomology of
`G̃r_k(ℝ^{k+m})` has the same dimension as that of `G̃r_9(ℝ^{9+m})`. -/
theorem finrank_degreeEight_reduce (k m : ℕ) (hk : 9 ≤ k) (hm : 10 ≤ m) :
    Module.finrank ℚ (Work.SignatureBordism.ratCohomology 8 (sset (OG k m))) =
      Module.finrank ℚ (Work.SignatureBordism.ratCohomology 8 (sset (OG 9 m))) := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      rw [finrank_degreeEight_succ (n+1) m (by omega) hm]
      exact ih

end Deg8

/-- **The target lemma**: for `k, m ≥ 10`, the degree-eight rational cohomology of the oriented
Grassmannian `G̃r_k(ℝ^{k+m})` is at most two-dimensional (it is spanned by `p₁²` and `p₂`). -/
theorem degreeEightFinrankLeTwo (k m : ℕ) (hk : 10 ≤ k) (hm : 10 ≤ m) :
    Module.finrank ℚ (Work.SignatureBordism.ratCohomology 8 (Work.ThomBordism.Grassmann.sset (Work.ThomBordism.Grassmann.OG k m))) ≤ 2 := by
  rw [Deg8.finrank_degreeEight_reduce k m (by omega) hm]
  exact Deg8.degreeEight_finrank_nine_le_two m hm

end

end Work.ThomBordism.Grassmann
