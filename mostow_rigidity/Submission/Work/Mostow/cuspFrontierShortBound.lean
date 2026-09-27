import Mathlib
import Submission.Work.Mostow.cuspFrontierShortBound_ROUTE
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.cuspParDispDefs
import Submission.Work.Mostow.cuspThinRegionDefs
import Submission.Work.Mostow.cuspThinRegion_eq_parDisp
import Submission.Work.Mostow.parDisp_lipschitz_invariant
import Submission.Work.Mostow.rotPacking
import Submission.Work.Mostow.stabParabOrEllip
import Submission.Work.Mostow.margulisCusp
import Submission.Work.Mostow.stabFlatActionCanon
import Submission.Work.Mostow.cuspHoro.flatActLevelOne
import Submission.Work.Mostow.cuspHoro.flatLinMulLambdaMat
import Submission.Work.Mostow.cuspZ2Defs
import Submission.Work.Mostow.StabLift
import Submission.Work.Mostow.LambdaMat_theta_eq_exp_smul
import Submission.Work.Mostow.stabFlatDefs
import Submission.Work.Mostow.flatLinNorm
import Submission.Work.Mostow.flatLinInnerZero
import Submission.Work.Mostow.normConjIsom
import Submission.Work.Mostow.rayStrictHoro

/-!
# The bound on the short set at the frontier of a cusp Margulis region

This file proves `Work.Mostow.cuspFrontierShortBound`: for a lattice `Γ <= PO(n,1)` (`n >= 2`),
a cusp `ξ ∈ parFixed Γ`, a level `θ > 0` of the elliptic gap at `ξ`, and a point `u` on the level
set `lev ξ u * parDisp Γ ξ (yc ξ u) = cEps ε` of the Margulis cusp region, at most `N` elements of
`Γ` move `u` by less than `ε/2`, with `N` and the threshold `ε₀` independent of `u` and of
`ε ≤ ε₀`.

The two halves of the argument are:

* `cuspFrontier_fixes_of_short`: for `ε` below a threshold depending only on `n`, the Margulis
  lemma `Work.Mostow.margulisCusp` (with `R = 1`), applied to a parabolic of `Γ_ξ` which is
  `2 parDisp`-short at `u`, shows that *every* element of `Γ` moving `u` by at most `1` fixes `ξ`.
* `cuspFrontierShortSetCard'`: on the level set no `(ε/2)`-short element is parabolic (such an
  element would witness `u ∈ cuspThinRegion Γ ξ ε`, contradicting `cuspThinRegion_eq_parDisp`), so
  the quotient `γ⁻¹γ'` of two distinct short elements is an elliptic of `Γ_ξ`; the elliptic gap
  `hgap`, the multiplicativity `flatLinMulLambdaMat` and the isometry property of `flatLin`
  separate the flat linear parts of the short elements by `θ`, and `rotPacking` bounds their
  number.

The two are combined in the final theorem.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open scoped Topology

noncomputable section

variable {n : ℕ}

theorem cuspFrontier_fixes_of_short (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (hdisc : IsDiscrete (SetLike.coe Γ))
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    {ξ : Submission.Mostow.E n} (hξ : ξ ∈ Work.Mostow.parFixed Γ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ u : Submission.Mostow.E n,
      Work.Mostow.lev ξ u * Work.Mostow.parDisp Γ ξ (Work.Mostow.yc ξ u) = Work.Mostow.cEps ε →
      ∀ γ : Γ, Submission.Mostow.hdist u
        ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) ≤ 1 →
        Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ := by
  obtain ⟨εM, hεMpos, hεM⟩ := Work.Mostow.margulisCusp n hn hA hI 1
  -- choose the level threshold so that `cosh εM > 1 + 2 (cEps ε)^2` for `ε ≤ ε₀`
  have h2 : Real.cosh (0:ℝ) < (Real.cosh εM + 3) / 4 := by
    rw [Real.cosh_zero]
    have h3 := Real.one_lt_cosh.mpr (ne_of_gt hεMpos)
    linarith
  have hpre : Real.cosh ⁻¹' Set.Iio ((Real.cosh εM + 3) / 4) ∈ 𝓝 (0:ℝ) :=
    Real.continuous_cosh.continuousAt (isOpen_Iio.mem_nhds h2)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨min (δ/2) 1, lt_min (by linarith) one_pos, min_le_right _ _, ?_⟩
  intro ε hε hεle u hu γ hγ
  have hεδ : ε < δ := lt_of_le_of_lt hεle (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have hcoshε : Real.cosh ε < (Real.cosh εM + 3) / 4 :=
    hδ (by rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hε]; exact hεδ)
  have hξS : ξ ∈ Sph n := hξ.1
  have hB : POBasic n := POBasic.ofProp hA
  have hId : HypIsoData n := HypIsoData.ofProp hI
  have hstab : ∀ (γ : Γ), bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0 :=
    fun γ hγ => hvan γ ξ hξ hγ
  have hL : 0 < lev ξ u := lev_pos ξ hξS u
  have hY : inner ℝ (yc ξ u) ξ = 0 := inner_yc hξS u
  obtain ⟨γ₀, hγ₀par, hγ₀fix⟩ := hξ.2
  have hpdp : 0 < parDisp Γ ξ (yc ξ u) :=
    parDisp_pos_of_discrete n hA hI Γ hdisc hξS hstab ⟨γ₀, hγ₀par, hγ₀fix⟩ hY
  have hSne : (parDispSet Γ ξ (yc ξ u)).Nonempty := ⟨_, γ₀, hγ₀par, hγ₀fix, rfl⟩
  have hSbdd : BddBelow (parDispSet Γ ξ (yc ξ u)) :=
    ⟨0, fun s hs => by
      simp only [parDispSet, Set.mem_setOf_eq] at hs
      obtain ⟨γ, -, -, rfl⟩ := hs
      positivity⟩
  have hpdp_sInf : 0 < sInf (parDispSet Γ ξ (yc ξ u)) := by
    have h := hpdp
    rwa [parDisp_eq_sInf] at h
  obtain ⟨s, hs, hlt⟩ :=
    (exists_mul_lt_iff_mul_sInf_lt (a := 1) (c := 2 * parDisp Γ ξ (yc ξ u))
      one_pos hSne hSbdd).mpr (by rw [parDisp_eq_sInf]; linarith)
  simp only [parDispSet, Set.mem_setOf_eq] at hs
  obtain ⟨q, hqpar, hqfix, rfl⟩ := hs
  -- the flat displacement of the parabolic `q` is less than twice the `parDisp`
  have hdlt : ‖yc ξ u - flatAct ξ (q : PO n 1) (yc ξ u)‖ < 2 * parDisp Γ ξ (yc ξ u) := by
    simpa using hlt
  -- the horospherical displacement formula
  have hlev0 : lev ξ ((q : PO n 1) • (0 : E n)) = 1 := by
    rw [Work.Mostow.cuspHoro.lev_smul_of_stab hI hξS hstab q hqfix,
      Work.Mostow.cuspHoro.lev_zero]
  have hcosh := Work.Mostow.cosh_hdist_smul_horo hB hId hξS hqfix hlev0 u
  have hcEps_sq : (cEps ε) ^ 2 = 2 * (Real.cosh ε - 1) := by
    rw [Work.Mostow.cEps]
    rw [Real.sq_sqrt (by have := Real.one_lt_cosh.mpr (ne_of_gt hε); linarith)]
  have hpose : 0 < 2 * parDisp Γ ξ (yc ξ u) := by linarith
  have hkey : Real.cosh (hdist u ((q : PO n 1) • u))
      < 1 + lev ξ u ^ 2 / 2 * (2 * parDisp Γ ξ (yc ξ u)) ^ 2 := by
    rw [hcosh]
    have hnn : 0 < lev ξ u ^ 2 / 2 := by positivity
    have hd2 : ‖yc ξ u - flatAct ξ (q : PO n 1) (yc ξ u)‖ ^ 2
        < (2 * parDisp Γ ξ (yc ξ u)) ^ 2 := by
      have h0 : 0 ≤ ‖yc ξ u - flatAct ξ (q : PO n 1) (yc ξ u)‖ := norm_nonneg _
      nlinarith [hdlt, hpose]
    nlinarith [hnn, hd2]
  have h1 : 1 + lev ξ u ^ 2 / 2 * (2 * parDisp Γ ξ (yc ξ u)) ^ 2
      = 4 * Real.cosh ε - 3 := by
    have hmid : lev ξ u ^ 2 / 2 * (2 * parDisp Γ ξ (yc ξ u)) ^ 2 = 2 * (cEps ε) ^ 2 := by
      rw [← hu]; ring
    rw [hmid, hcEps_sq]; ring
  have hcosh_lt : Real.cosh (hdist u ((q : PO n 1) • u)) < Real.cosh εM := by
    rw [h1] at hkey
    linarith
  have hθM : hdist u ((q : PO n 1) • u) < εM := by
    have hh := Real.cosh_lt_cosh.mp hcosh_lt
    rw [abs_of_nonneg (hId.nonneg u ((q : PO n 1) • u)), abs_of_pos hεMpos] at hh
    exact hh
  exact hεM Γ hdisc u ξ q γ hqpar hξS hqfix hθM hγ

theorem cfsb_sph_ne_zero {n : ℕ} {ξ : E n} (hξ : ξ ∈ Sph n) : ξ ≠ 0 := by
  intro h0
  have h1 : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  rw [h0] at h1
  simp at h1

/-- A linear isometry equivalence `E (n-1) ≃ₗᵢ[ℝ] ξ^⊥`. -/
noncomputable def cfsbXiEquiv (n : ℕ) (hn : 1 ≤ n) (ξ : E n) (hξ : ξ ≠ 0) :
    E (n - 1) ≃ₗᵢ[ℝ] xiPerp ξ := by
  haveI : Fact (Module.finrank ℝ (E n) = (n - 1) + 1) := ⟨by
    rw [finrank_euclideanSpace, Fintype.card_fin]; omega⟩
  exact ((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (n - 1) (v := ξ) hξ).repr).symm

/-- The flat (horospherical) action of `γ ∈ Γ` fixing `ξ` as an isometry of `ξ^⊥`. -/
noncomputable def cfsbFlatIsom (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ) (γ : Γ)
    (hγ : Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ) :
    Work.Mostow.xiPerp ξ ≃ᵢ Work.Mostow.xiPerp ξ :=
  Work.Mostow.flatIsom (Work.Mostow.POBasic.ofProp hA) (Work.Mostow.HypIsoData.ofProp hI)
    hξ.1 1 one_pos
    (Work.Mostow.cuspHoro.lev_smul_of_stab hI hξ.1 (fun δ hδ => hvan δ ξ hξ hδ) γ hγ)
    (Work.Mostow.cuspHoro.lev_smul_of_stab hI hξ.1 (fun δ hδ => hvan δ ξ hξ hδ) γ⁻¹
      (Work.Mostow.bd_inv_of hξ.1 (Work.Mostow.POBasic.ofProp hA) hγ))

/-- The transported linear part of the flat action. -/
noncomputable def cfsbFlatRot (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ) (γ : Γ)
    (hγ : Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ) :
    E (n - 1) ≃ₗᵢ[ℝ] E (n - 1) :=
  ((cfsbXiEquiv n (by omega) ξ (cfsb_sph_ne_zero hξ.1)).trans
    ((cfsbFlatIsom n hA hI Γ hvan ξ hξ γ hγ).toRealLinearIsometryEquiv.trans
      (cfsbXiEquiv n (by omega) ξ (cfsb_sph_ne_zero hξ.1)).symm))

/-- The linear part of the flat action, as an element of `E n`. -/
theorem cfsbFlatIsom_coe (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ) (γ : Γ)
    (hγ : Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ)
    {z : Submission.Mostow.E n} (hzperp : z ∈ Work.Mostow.xiPerp ξ) :
    ((((cfsbFlatIsom n hA hI Γ hvan ξ hξ γ hγ).toRealLinearIsometryEquiv
        ⟨z, hzperp⟩ :
        Work.Mostow.xiPerp ξ) : Submission.Mostow.E n))
      = Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat (γ : LeanEval.Geometry.MostowRigidity.PO n 1)) z := by
  have hz : inner ℝ z ξ = 0 := by
    rw [real_inner_comm]
    exact Work.Mostow.xiPerp_inner ⟨z, hzperp⟩
  have hb : Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0 := hvan γ ξ hξ hγ
  have hbus : Submission.Mostow.busemann ξ ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • (0 : Submission.Mostow.E n)) = 0 := by
    simpa [Work.Mostow.bCocy, hγ] using hb
  have hflat := Work.Mostow.stabFlatActionCanon n hA hI ξ hξ.1
    (γ : LeanEval.Geometry.MostowRigidity.PO n 1) hγ hbus
  have hz1 : Work.Mostow.yc ξ ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.hptOf ξ z 1)
      = Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat (γ : LeanEval.Geometry.MostowRigidity.PO n 1)) z
        + Work.Mostow.flatTrans ξ (Work.Mostow.LambdaMat (γ : LeanEval.Geometry.MostowRigidity.PO n 1)) :=
    (hflat.2.2.2 z 1 hz one_pos).2
  have hz0 : Work.Mostow.yc ξ ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.hptOf ξ (0 : Submission.Mostow.E n) 1)
      = Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat (γ : LeanEval.Geometry.MostowRigidity.PO n 1)) (0 : Submission.Mostow.E n)
        + Work.Mostow.flatTrans ξ (Work.Mostow.LambdaMat (γ : LeanEval.Geometry.MostowRigidity.PO n 1)) :=
    (hflat.2.2.2 (0 : Submission.Mostow.E n) 1 (by simp) one_pos).2
  rw [IsometryEquiv.toRealLinearIsometryEquiv_apply]
  rw [Submodule.coe_sub]
  have h1 : (((cfsbFlatIsom n hA hI Γ hvan ξ hξ γ hγ)
      ⟨z, hzperp⟩ :
      Work.Mostow.xiPerp ξ) : Submission.Mostow.E n)
      = Work.Mostow.yc ξ ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.hptOf ξ z 1) := rfl
  have h2 : (((cfsbFlatIsom n hA hI Γ hvan ξ hξ γ hγ) (0 : Work.Mostow.xiPerp ξ) :
      Work.Mostow.xiPerp ξ) : Submission.Mostow.E n)
      = Work.Mostow.yc ξ ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.hptOf ξ (0 : Submission.Mostow.E n) 1) := rfl
  rw [h1, h2, hz1, hz0, map_zero, zero_add, add_sub_cancel_right]

/-- The transported flat rotation applied to `φ.symm y`. -/
theorem cfsbFlatRot_symm (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ) (γ : Γ)
    (hγ : Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ)
    (y : Work.Mostow.xiPerp ξ) :
    cfsbFlatRot n hn hA hI Γ hvan ξ hξ γ hγ
        ((cfsbXiEquiv n (by omega) ξ (cfsb_sph_ne_zero hξ.1)).symm y)
      = (cfsbXiEquiv n (by omega) ξ (cfsb_sph_ne_zero hξ.1)).symm
          ((cfsbFlatIsom n hA hI Γ hvan ξ hξ γ hγ).toRealLinearIsometryEquiv y) := by
  simp only [cfsbFlatRot, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]

/-- **The parabolic exclusion at the frontier level set.** -/
lemma cfsb_not_isParabolic (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (hdisc : IsDiscrete (SetLike.coe Γ))
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    {ξ : Submission.Mostow.E n} (hξ : ξ ∈ Work.Mostow.parFixed Γ) {ε : ℝ} (hε : 0 < ε)
    {u : Submission.Mostow.E n}
    (hu : Work.Mostow.lev ξ u * Work.Mostow.parDisp Γ ξ (Work.Mostow.yc ξ u) = Work.Mostow.cEps ε)
    (q : Γ) (hqbd : Submission.Mostow.bd (q : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ)
    (hqd : Submission.Mostow.hdist u
      ((q : LeanEval.Geometry.MostowRigidity.PO n 1) • u) < ε) :
    ¬ Submission.Mostow.IsParabolic (q : LeanEval.Geometry.MostowRigidity.PO n 1) := by
  intro hqpar
  have hmem : u ∈ Work.Mostow.cuspThinRegion Γ ξ ε := ⟨q, hqpar, hqbd, hqd⟩
  obtain ⟨-, hiff⟩ := Work.Mostow.cuspThinRegion_eq_parDisp n hA hI Γ hdisc hvan hξ
  have hlt := (hiff ε hε u).mp hmem
  rw [hu] at hlt
  exact lt_irrefl _ hlt

/-- Two elements moving `u` by less than `δ` have their quotient moving `u` by less than `2δ`. -/
lemma cfsb_hdist_inv_mul_lt (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (g g' : PO n 1) (u : E n) {δ : ℝ}
    (hg : hdist u (g • u) < δ) (hg' : hdist u (g' • u) < δ) :
    hdist u ((g⁻¹ * g') • u) < 2 * δ := by
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  have hA' : POBasic n := POBasic.ofProp hA
  have h1 : (g⁻¹ * g') • u = g⁻¹ • (g' • u) := hA'.mul_smul g⁻¹ g' u
  rw [h1]
  have h2 : hdist u (g⁻¹ • (g' • u)) = hdist (g • u) (g' • u) := by
    have h := hI'.isom_smul g u (g⁻¹ • (g' • u))
    rw [← hA'.mul_smul g g⁻¹ (g' • u), mul_inv_cancel, hA'.one_smul] at h
    exact h.symm
  rw [h2]
  have h3 : hdist (g • u) (g' • u) ≤ hdist (g • u) u + hdist u (g' • u) := hI'.triangle _ _ _
  rw [hI'.symm (g • u) u] at h3
  linarith

/-- If `g`, `g'` fix `ξ` then so does `g⁻¹ * g'`. -/
lemma cfsb_bd_inv_mul (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) {ξ : E n} (hξ : ξ ∈ Sph n) {g g' : PO n 1}
    (hg : bd g ξ = ξ) (hg' : bd g' ξ = ξ) : bd (g⁻¹ * g') ξ = ξ := by
  have hA' : POBasic n := POBasic.ofProp hA
  have h1 : bd (g⁻¹ * g') ξ = bd g⁻¹ (bd g' ξ) := hA'.bd_mul g⁻¹ g' ξ hξ
  have h2 : bd g⁻¹ ξ = ξ := by
    have h := hA'.bd_mul g⁻¹ g ξ hξ
    rw [inv_mul_cancel, hA'.bd_one ξ hξ, hg] at h
    exact h.symm
  rw [h1, hg', h2]

/-- **θ-separation of the transported flat linear parts.** -/
theorem cfsbFlatRot_sep (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (hdisc : IsDiscrete (SetLike.coe Γ))
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ) {θ : ℝ} (hθ : 0 < θ)
    (hgap : ∀ (σ : Γ),
      Submission.Mostow.bd (σ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ → σ ≠ 1 →
      (∃ p : Submission.Mostow.E n, (σ : LeanEval.Geometry.MostowRigidity.PO n 1) • p = p) →
      ∃ y : Submission.Mostow.E n, inner ℝ y ξ = 0 ∧ ‖y‖ = 1 ∧
        θ ≤ ‖Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat (σ : LeanEval.Geometry.MostowRigidity.PO n 1)) y - y‖)
    {ε : ℝ} (hε : 0 < ε) {u : Submission.Mostow.E n}
    (hu : Work.Mostow.lev ξ u * Work.Mostow.parDisp Γ ξ (Work.Mostow.yc ξ u) = Work.Mostow.cEps ε)
    (hfix : ∀ γ : Γ, Submission.Mostow.hdist u
      ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) < ε / 2 →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ)
    {γ γ' : Γ} (hγs : Submission.Mostow.hdist u
      ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) < ε / 2)
    (hγ's : Submission.Mostow.hdist u
      ((γ' : LeanEval.Geometry.MostowRigidity.PO n 1) • u) < ε / 2)
    (hne : γ ≠ γ') :
    θ ≤ ‖Work.Mostow.opOf (cfsbFlatRot n hn hA hI Γ hvan ξ hξ γ (hfix γ hγs)) -
      Work.Mostow.opOf (cfsbFlatRot n hn hA hI Γ hvan ξ hξ γ' (hfix γ' hγ's))‖ := by
  have hγbd : Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ := hfix γ hγs
  have hγ'bd : Submission.Mostow.bd (γ' : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ := hfix γ' hγ's
  have hξS : ξ ∈ Sph n := hξ.1
  set q : Γ := γ⁻¹ * γ' with hqdef
  have hγq : γ * q = γ' := by rw [hqdef]; group
  have hqne : q ≠ 1 := by
    intro h1
    exact hne (by rw [← hγq, h1, mul_one])
  have hqcoe : (q : LeanEval.Geometry.MostowRigidity.PO n 1)
      = (γ : LeanEval.Geometry.MostowRigidity.PO n 1)⁻¹ * (γ' : LeanEval.Geometry.MostowRigidity.PO n 1) := by
    rw [hqdef, Subgroup.coe_mul, Subgroup.coe_inv]
  have hqbd : Submission.Mostow.bd (q : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ := by
    rw [hqcoe]
    exact cfsb_bd_inv_mul hA hI hξS hγbd hγ'bd
  have hqb : Work.Mostow.bCocy (q : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0 := hvan q ξ hξ hqbd
  have hqd : Submission.Mostow.hdist u ((q : LeanEval.Geometry.MostowRigidity.PO n 1) • u) < ε := by
    have h := cfsb_hdist_inv_mul_lt hA hI (γ : LeanEval.Geometry.MostowRigidity.PO n 1)
      (γ' : LeanEval.Geometry.MostowRigidity.PO n 1) u (δ := ε/2) hγs hγ's
    rw [hqcoe]
    linarith
  have hnpar : ¬ Submission.Mostow.IsParabolic (q : LeanEval.Geometry.MostowRigidity.PO n 1) :=
    cfsb_not_isParabolic n hA hI Γ hdisc hvan hξ hε hu q hqbd hqd
  have hell : ∃ p : Submission.Mostow.E n,
      (q : LeanEval.Geometry.MostowRigidity.PO n 1) • p = p := by
    rcases Work.Mostow.stabParabOrEllip n hn hA hI (q : LeanEval.Geometry.MostowRigidity.PO n 1)
      ξ hξS hqbd hqb with hp | hel
    · exact absurd hp hnpar
    · exact hel
  obtain ⟨z, hz, hzn, hθz⟩ := hgap q hqbd hqne hell
  have hzperp : z ∈ Work.Mostow.xiPerp ξ :=
    Work.Mostow.mem_xiPerp_iff.mpr (by rw [real_inner_comm]; exact hz)
  -- multiplicativity of the flat linear part
  have hcoe : (γ : LeanEval.Geometry.MostowRigidity.PO n 1) * (q : LeanEval.Geometry.MostowRigidity.PO n 1)
      = (γ' : LeanEval.Geometry.MostowRigidity.PO n 1) := by
    rw [← Subgroup.coe_mul, hγq]
  have hmul := (Work.Mostow.cuspHoro.flatLinMulLambdaMat n hA hI ξ hξS).1
    (γ : LeanEval.Geometry.MostowRigidity.PO n 1) (q : LeanEval.Geometry.MostowRigidity.PO n 1)
    hγbd hqbd (hvan γ ξ hξ hγbd) hqb z hz
  rw [hcoe] at hmul
  -- the norm computation
  set φ : E (n - 1) ≃ₗᵢ[ℝ] Work.Mostow.xiPerp ξ :=
    cfsbXiEquiv n (by omega) ξ (cfsb_sph_ne_zero hξS) with hφdef
  set y : E (n - 1) := φ.symm ⟨z, hzperp⟩ with hydef
  have hφy : φ y = ⟨z, hzperp⟩ := by rw [hydef]; exact LinearIsometryEquiv.apply_symm_apply φ _
  have hyz : ‖y‖ = 1 := by rw [hydef, LinearIsometryEquiv.norm_map]; exact hzn
  have hdiff : (cfsbFlatRot n hn hA hI Γ hvan ξ hξ γ hγbd) y
      - (cfsbFlatRot n hn hA hI Γ hvan ξ hξ γ' hγ'bd) y
      = φ.symm (((cfsbFlatIsom n hA hI Γ hvan ξ hξ γ hγbd).toRealLinearIsometryEquiv ⟨z, hzperp⟩)
          - ((cfsbFlatIsom n hA hI Γ hvan ξ hξ γ' hγ'bd).toRealLinearIsometryEquiv ⟨z, hzperp⟩)) := by
    rw [hydef, cfsbFlatRot_symm, cfsbFlatRot_symm, map_sub]
  have hnorm : ‖(cfsbFlatRot n hn hA hI Γ hvan ξ hξ γ hγbd) y
      - (cfsbFlatRot n hn hA hI Γ hvan ξ hξ γ' hγ'bd) y‖
      = ‖Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat (γ : LeanEval.Geometry.MostowRigidity.PO n 1)) z
        - Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat (γ' : LeanEval.Geometry.MostowRigidity.PO n 1)) z‖ := by
    rw [hdiff, LinearIsometryEquiv.norm_map, ← Submodule.norm_coe, Submodule.coe_sub,
      cfsbFlatIsom_coe n hA hI Γ hvan ξ hξ γ hγbd hzperp,
      cfsbFlatIsom_coe n hA hI Γ hvan ξ hξ γ' hγ'bd hzperp]
  -- the lower bound
  have hAeq : Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat (γ : LeanEval.Geometry.MostowRigidity.PO n 1)) z
      - Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat (γ' : LeanEval.Geometry.MostowRigidity.PO n 1)) z
      = Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat (γ : LeanEval.Geometry.MostowRigidity.PO n 1))
          (z - Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat (q : LeanEval.Geometry.MostowRigidity.PO n 1)) z) := by
    rw [hmul, map_sub]
  have hperp : inner ℝ (z - Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat (q : LeanEval.Geometry.MostowRigidity.PO n 1)) z) ξ = 0 := by
    rw [inner_sub_left, hz, Work.Mostow.flatLinInnerZero ξ hξS (Work.Mostow.LambdaMat (q : LeanEval.Geometry.MostowRigidity.PO n 1)) z, sub_zero]
  have hbusγ : Submission.Mostow.busemann ξ ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • (0 : Submission.Mostow.E n)) = 0 := by
    simpa [Work.Mostow.bCocy, hγbd] using hvan γ ξ hξ hγbd
  have hflatγ := Work.Mostow.stabFlatActionCanon n hA hI ξ hξS
    (γ : LeanEval.Geometry.MostowRigidity.PO n 1) hγbd hbusγ
  have hnormpres : ‖Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat (γ : LeanEval.Geometry.MostowRigidity.PO n 1))
      (z - Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat (q : LeanEval.Geometry.MostowRigidity.PO n 1)) z)‖
      = ‖z - Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat (q : LeanEval.Geometry.MostowRigidity.PO n 1)) z‖ :=
    hflatγ.2.2.1 _ hperp
  have hlow : θ ≤ ‖(cfsbFlatRot n hn hA hI Γ hvan ξ hξ γ hγbd) y
      - (cfsbFlatRot n hn hA hI Γ hvan ξ hξ γ' hγ'bd) y‖ := by
    rw [hnorm, hAeq, hnormpres, norm_sub_rev]
    exact hθz
  -- operator norm
  have hle := ContinuousLinearMap.le_opNorm
    (Work.Mostow.opOf (cfsbFlatRot n hn hA hI Γ hvan ξ hξ γ hγbd) -
      Work.Mostow.opOf (cfsbFlatRot n hn hA hI Γ hvan ξ hξ γ' hγ'bd)) y
  rw [ContinuousLinearMap.sub_apply, Work.Mostow.opOf_apply, Work.Mostow.opOf_apply] at hle
  rw [hyz, mul_one] at hle
  linarith

/-- **The cardinality bound for the short set at a frontier point** (local version). -/
theorem cuspFrontierShortSetCard' (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (hdisc : IsDiscrete (SetLike.coe Γ))
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    {ξ : Submission.Mostow.E n} (hξ : ξ ∈ Work.Mostow.parFixed Γ)
    {θ : ℝ} (hθ : 0 < θ)
    (hgap : ∀ (σ : Γ),
      Submission.Mostow.bd (σ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ → σ ≠ 1 →
      (∃ p : Submission.Mostow.E n, (σ : LeanEval.Geometry.MostowRigidity.PO n 1) • p = p) →
      ∃ y : Submission.Mostow.E n, inner ℝ y ξ = 0 ∧ ‖y‖ = 1 ∧
        θ ≤ ‖Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat (σ : LeanEval.Geometry.MostowRigidity.PO n 1)) y - y‖) :
    ∃ N : ℕ, ∀ (ε : ℝ), 0 < ε → ∀ u : Submission.Mostow.E n,
      Work.Mostow.lev ξ u * Work.Mostow.parDisp Γ ξ (Work.Mostow.yc ξ u) = Work.Mostow.cEps ε →
      (∀ γ : Γ, Submission.Mostow.hdist u
        ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) < ε / 2 →
        Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ) →
      {γ : Γ | Submission.Mostow.hdist u
        ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) < ε / 2}.ncard ≤ N := by
  obtain ⟨N, hN⟩ := Work.Mostow.rotPacking (n - 1) θ hθ
  refine ⟨N, fun ε hε u hu hfix => ?_⟩
  classical
  let T : Γ → (E (n - 1) ≃ₗᵢ[ℝ] E (n - 1)) := fun γ =>
    if h : Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ then
      cfsbFlatRot n hn hA hI Γ hvan ξ hξ γ h else 1
  have hT : ∀ (γ : Γ) (h : Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ),
      T γ = cfsbFlatRot n hn hA hI Γ hvan ξ hξ γ h := fun γ h => dif_pos h
  let F : Set Γ := {γ : Γ | Submission.Mostow.hdist u
    ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) < ε / 2}
  have hFmem : ∀ γ : Γ, γ ∈ F ↔ Submission.Mostow.hdist u
      ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) < ε / 2 := fun γ => Iff.rfl
  have hsep : ∀ γ ∈ F, ∀ γ' ∈ F, γ ≠ γ' → θ ≤ ‖Work.Mostow.opOf (T γ) - Work.Mostow.opOf (T γ')‖ := by
    intro γ hγ γ' hγ' hne
    have h1 : Submission.Mostow.hdist u
        ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) < ε / 2 := (hFmem γ).mp hγ
    have h2 : Submission.Mostow.hdist u
        ((γ' : LeanEval.Geometry.MostowRigidity.PO n 1) • u) < ε / 2 := (hFmem γ').mp hγ'
    rw [hT γ (hfix γ h1), hT γ' (hfix γ' h2)]
    exact cfsbFlatRot_sep n hn hA hI Γ hdisc hvan ξ hξ hθ hgap hε hu hfix h1 h2 hne
  have hsepS : ∀ A ∈ T '' F, ∀ B ∈ T '' F, A ≠ B →
      θ ≤ ‖Work.Mostow.opOf A - Work.Mostow.opOf B‖ := by
    rintro A ⟨γ, hγ, rfl⟩ B ⟨γ', hγ', rfl⟩ hAB
    exact hsep γ hγ γ' hγ' (fun h => hAB (by rw [h]))
  obtain ⟨-, hNc⟩ := hN (T '' F) hsepS
  have hinj : Set.InjOn T F := by
    intro γ hγ γ' hγ' heq
    by_contra hne
    have hge := hsep γ hγ γ' hγ' hne
    rw [heq] at hge
    have h0 : ‖Work.Mostow.opOf (T γ') - Work.Mostow.opOf (T γ')‖ = 0 := by simp
    rw [h0] at hge
    linarith
  have hcard : (T '' F).ncard = F.ncard := Set.InjOn.ncard_image hinj
  rw [← hcard]
  exact hNc

/-- **The short set at a frontier point of the cusp Margulis region has at most `N` elements.** -/
theorem cuspFrontierShortBound (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ) {θ : ℝ} (hθ : 0 < θ)
    (hgap : ∀ (σ : Γ),
      Submission.Mostow.bd (σ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ → σ ≠ 1 →
      (∃ p : Submission.Mostow.E n, (σ : LeanEval.Geometry.MostowRigidity.PO n 1) • p = p) →
      ∃ y : Submission.Mostow.E n, inner ℝ y ξ = 0 ∧ ‖y‖ = 1 ∧
        θ ≤ ‖Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat (σ : LeanEval.Geometry.MostowRigidity.PO n 1)) y - y‖) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ u : Submission.Mostow.E n,
      Work.Mostow.lev ξ u * Work.Mostow.parDisp Γ ξ (Work.Mostow.yc ξ u) = Work.Mostow.cEps ε →
      {γ : Γ | Submission.Mostow.hdist u
        ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) < ε / 2}.ncard ≤ N := by
  have hdisc : IsDiscrete (SetLike.coe Γ) := hΓ.1
  obtain ⟨ε₀, hε₀pos, hε₀le1, hε₀⟩ :=
    cuspFrontier_fixes_of_short n hn hA hI Γ hdisc hvan hξ
  obtain ⟨N, hN⟩ := cuspFrontierShortSetCard' n hn hA hI Γ hdisc hvan hξ hθ hgap
  refine ⟨ε₀, hε₀pos, N, fun ε hε hεle u hu => ?_⟩
  refine hN ε hε u hu (fun γ hγ => ?_)
  refine hε₀ ε hε hεle u hu γ ?_
  linarith [hγ, hεle, hε₀le1]

end

end Work.Mostow
