import Mathlib
import Submission.Work.Mostow.cuspCocompactDefs
import Submission.Work.Mostow.cuspThinRegion_eq_parDisp
import Submission.Work.Mostow.stabParabOrEllip
import Submission.Work.Mostow.margulisCusp
import Submission.Work.Mostow.rotPacking
import Submission.Work.Mostow.stabFlatAction
import Submission.Work.Mostow.stabFlatActionCanon
import Submission.Work.Mostow.flatLinNorm
import Submission.Work.Mostow.flatLinInnerZero
import Submission.Work.Mostow.cuspHoro.flatActLevelOne
import Submission.Work.Mostow.cuspHoro.flatLinMulLambdaMat
import Submission.Work.Mostow.LambdaMat_theta_eq_exp_smul
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.packingOfSeparated
import Submission.Work.Mostow.parShortFrontierPt

namespace Work.Mostow

noncomputable section

open Submission.Mostow LeanEval.Geometry.MostowRigidity

variable {n : ℕ}

/-- `cEps 0 = 0`. -/
lemma fsbc_cEps_zero : cEps 0 = 0 := by unfold cEps; simp

/-- `cEps` is positive at positive arguments. -/
lemma fsbc_cEps_pos {a : ℝ} (ha : 0 < a) : 0 < cEps a := by
  unfold cEps
  apply Real.sqrt_pos.mpr
  have : (1:ℝ) < Real.cosh a := Real.one_lt_cosh.mpr (ne_of_gt ha)
  linarith

/-- `cEps` is continuous at `0`. -/
lemma fsbc_cEps_continuousAt_zero : ContinuousAt cEps 0 := by unfold cEps; fun_prop

/-- For `a > 0` there is `0 < ε ≤ 1` with `2 * cEps ε ≤ cEps a`. -/
lemma fsbc_exists_cEps_small (a : ℝ) (ha : 0 < a) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 2 * cEps ε ≤ cEps a := by
  have hcont := fsbc_cEps_continuousAt_zero
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδpos, hδ⟩ := hcont (cEps a / 2) (by have := fsbc_cEps_pos ha; linarith)
  refine ⟨min δ 1 / 2, by positivity, by nlinarith [min_le_right δ 1], ?_⟩
  have hlt : dist (min δ 1 / 2) (0:ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : (0:ℝ) < min δ 1 / 2)]
    nlinarith [min_le_left δ 1]
  have h2 := hδ hlt
  rw [Real.dist_eq, fsbc_cEps_zero, sub_zero] at h2
  have hnn : 0 ≤ cEps (min δ 1 / 2) := by unfold cEps; positivity
  rw [abs_of_nonneg hnn] at h2
  linarith

theorem frontierShortStabBound (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    {ξ : Submission.Mostow.E n} (hξS : ξ ∈ Submission.Mostow.Sph n)
    (hξP : ξ ∈ Work.Mostow.parFixed Γ)
    (hvan : ∀ (γ : Γ) η, η ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) η = η →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) η = 0)
    {θ ε : ℝ} (hθ : 0 < θ) (hε : 0 < ε)
    (hgap : ∀ (γ : Γ) (A : Submission.Mostow.E n →ₗ[ℝ] Submission.Mostow.E n) (v : Submission.Mostow.E n),
      (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ≠ 1 →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      (∃ p : Submission.Mostow.E n, (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • p = p) →
      (∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 → inner ℝ (A y) ξ = 0) →
      (∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 → ‖A y‖ = ‖y‖) →
      (∀ (y : Submission.Mostow.E n) (D : ℝ), inner ℝ y ξ = 0 → 0 < D →
        Work.Mostow.lev ξ ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.hptOf ξ y D) = D ∧
        Work.Mostow.yc ξ ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.hptOf ξ y D) = A y + v) →
      ∃ y : Submission.Mostow.E n, inner ℝ y ξ = 0 ∧ ‖y‖ = 1 ∧ θ ≤ ‖A y - y‖) :
    ∃ N : ℕ, ∀ u : Submission.Mostow.E n,
      (∀ γ : Γ, Submission.Mostow.hdist u
        ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) < ε / 2 →
        Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ) →
      (∀ h : Γ, h ≠ 1 →
        Submission.Mostow.bd (h : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
        Submission.Mostow.IsParabolic (h : LeanEval.Geometry.MostowRigidity.PO n 1) →
        Submission.Mostow.hdist u ((h : LeanEval.Geometry.MostowRigidity.PO n 1) • u) < ε → False) →
      {γ : Γ | Submission.Mostow.hdist u
        ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) < ε / 2}.ncard ≤ N := by
  classical
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  have hξnorm : ‖ξ‖ = 1 := by
    simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξS
  have hξ1 : inner ℝ ξ ξ = 1 := by
    rw [real_inner_self_eq_norm_sq, hξnorm]; norm_num
  -- the orthogonal projection onto ξ^⊥
  let P : E n →L[ℝ] E n := ContinuousLinearMap.id ℝ (E n) - (innerSL ℝ ξ).smulRight ξ
  have hP_apply : ∀ y : E n, P y = y - (inner ℝ y ξ) • ξ := by
    intro y; simp [P, real_inner_comm]
  have hP_perp : ∀ y : E n, inner ℝ (P y) ξ = 0 := by
    intro y; rw [hP_apply y, inner_sub_left, real_inner_smul_left, hξ1]; ring
  have hP_le : ∀ y : E n, ‖P y‖ ≤ ‖y‖ := by
    intro y
    have hperp : inner ℝ (P y) ξ = 0 := hP_perp y
    have hsmul : ‖(inner ℝ y ξ) • ξ‖ ^ 2 = (inner ℝ y ξ) ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, hξnorm, mul_one, sq_abs]
    have hinner : inner ℝ (P y) ((inner ℝ y ξ) • ξ) = 0 := by
      rw [real_inner_smul_right, hperp, mul_zero]
    have hkey : ‖y‖ ^ 2 = ‖P y‖ ^ 2 + (inner ℝ y ξ) ^ 2 := by
      have hdec : y = P y + (inner ℝ y ξ) • ξ := by rw [hP_apply y]; abel
      conv_lhs => rw [hdec]
      rw [norm_add_sq_real, hinner, hsmul]
      ring
    nlinarith [norm_nonneg (P y), norm_nonneg y, sq_nonneg (inner ℝ y ξ), hkey]
  -- the operators B_γ = A_γ ∘ (projection onto ξ^⊥)
  let B : Γ → (E n →L[ℝ] E n) := fun γ =>
    (LinearMap.toContinuousLinearMap (flatLin ξ (LambdaMat ((γ : Γ) : PO n 1))) : E n →L[ℝ] E n).comp P
  have hB_apply : ∀ (γ : Γ) (y : E n),
      B γ y = flatLin ξ (LambdaMat (((γ : Γ) : PO n 1))) (y - (inner ℝ y ξ) • ξ) := by
    intro γ y
    have h1 : B γ y
        = (LinearMap.toContinuousLinearMap (flatLin ξ (LambdaMat ((γ : Γ) : PO n 1)))
            : E n →L[ℝ] E n) (P y) := rfl
    rw [h1, hP_apply y]
    rfl
  have hB_perp : ∀ (γ : Γ) (y : E n), inner ℝ y ξ = 0 →
      B γ y = flatLin ξ (LambdaMat (((γ : Γ) : PO n 1))) y := by
    intro γ y hy
    rw [hB_apply γ y, hy, zero_smul, sub_zero]
  -- the cocycle vanishes on the stabiliser
  have hbc : ∀ (γ : Γ), bd ((γ : Γ) : PO n 1) ξ = ξ → bCocy ((γ : Γ) : PO n 1) ξ = 0 :=
    fun γ hγ => hvan γ ξ hξP hγ
  have hθΛ : ∀ (γ : Γ), bd ((γ : Γ) : PO n 1) ξ = ξ →
      (LambdaMat ((γ : Γ) : PO n 1)).mulVec (theta ξ) = theta ξ := by
    intro γ hγ
    rw [LambdaMat_theta_eq_exp_smul n hA hI ((γ : Γ) : PO n 1) ξ hξS hγ, hbc γ hγ,
      neg_zero, Real.exp_zero, one_smul]
  -- the uniform norm bound on the ball
  have hB_le : ∀ (γ : Γ), bd ((γ : Γ) : PO n 1) ξ = ξ → ‖B γ‖ ≤ 1 := by
    intro γ hγ
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y => ?_)
    rw [one_mul, hB_apply γ y]
    have hperp : inner ℝ (y - (inner ℝ y ξ) • ξ) ξ = 0 := by
      rw [inner_sub_left, real_inner_smul_left, hξ1]; ring
    rw [flatLinNorm ξ hξS (LambdaMat ((γ : Γ) : PO n 1)) (LambdaMat_isJOrth _) (hθΛ γ hγ)
      (y - (inner ℝ y ξ) • ξ) hperp]
    rw [← hP_apply y]; exact hP_le y
  -- the pairwise separation
  have hsepB : ∀ u : E n,
      (∀ γ : Γ, hdist u ((γ : PO n 1) • u) < ε / 2 → bd ((γ : Γ) : PO n 1) ξ = ξ) →
      (∀ h : Γ, h ≠ 1 → bd ((h : Γ) : PO n 1) ξ = ξ →
        IsParabolic ((h : Γ) : PO n 1) → hdist u ((h : PO n 1) • u) < ε → False) →
      ∀ γ : Γ, hdist u ((γ : PO n 1) • u) < ε / 2 → ∀ γ' : Γ,
        hdist u ((γ' : PO n 1) • u) < ε / 2 → γ ≠ γ' → θ ≤ ‖B γ - B γ'‖ := by
    intro u hfix hnotpar γ hγF γ' hγ'F hne
    have hfixγ : bd ((γ : Γ) : PO n 1) ξ = ξ := hfix γ hγF
    have hfixγ' : bd ((γ' : Γ) : PO n 1) ξ = ξ := hfix γ' hγ'F
    set h : Γ := γ⁻¹ * γ' with hh
    have hhcoe : ((h : Γ) : PO n 1) = ((γ : Γ) : PO n 1)⁻¹ * ((γ' : Γ) : PO n 1) := rfl
    have hhne : h ≠ 1 := by
      intro h1
      have h2 : γ' = γ := by
        have := congrArg (fun z : Γ => γ * z) h1
        simpa [hh, mul_assoc] using this
      exact hne h2.symm
    have hhcoe_ne : ((h : Γ) : PO n 1) ≠ 1 := fun h1 => hhne (Subtype.ext h1)
    -- the boundary fixed point of h
    have hbdi : bd (((γ : Γ) : PO n 1))⁻¹ ξ = ξ := by
      have h1 : bd ((((γ : Γ) : PO n 1))⁻¹ * ((γ : Γ) : PO n 1)) ξ
          = bd (((γ : Γ) : PO n 1))⁻¹ (bd (((γ : Γ) : PO n 1)) ξ) :=
        hA'.bd_mul _ _ ξ hξS
      rw [inv_mul_cancel, hA'.bd_one ξ hξS, hfixγ] at h1
      exact h1.symm
    have hhfix : bd ((h : Γ) : PO n 1) ξ = ξ := by
      rw [hhcoe, hA'.bd_mul _ _ ξ hξS, hfixγ', hbdi]
    have hhbc : bCocy ((h : Γ) : PO n 1) ξ = 0 := hbc h hhfix
    -- movement
    have hhmov : hdist u ((h : PO n 1) • u) < ε := by
      have hcoeh : ((h : Γ) : PO n 1) • u
          = ((((γ : Γ) : PO n 1))⁻¹ * ((γ' : Γ) : PO n 1)) • u := by rw [hhcoe]
      rw [hcoeh]
      have e1 : hdist u (((((γ : Γ) : PO n 1))⁻¹ * ((γ' : Γ) : PO n 1)) • u)
          = hdist (((γ : Γ) : PO n 1) • u)
              (((γ : Γ) : PO n 1)
                • (((((γ : Γ) : PO n 1))⁻¹ * ((γ' : Γ) : PO n 1)) • u)) :=
        (hI'.isom_smul ((γ : Γ) : PO n 1) u _).symm
      rw [e1, hA'.mul_smul]
      have e2 : ((γ : Γ) : PO n 1) • ((((γ : Γ) : PO n 1))⁻¹ • (((γ' : Γ) : PO n 1) • u))
          = ((γ' : Γ) : PO n 1) • u := by
        rw [← hA'.mul_smul, mul_inv_cancel, hA'.one_smul]
      rw [e2]
      have t1 := hI'.triangle (((γ : Γ) : PO n 1) • u) u (((γ' : Γ) : PO n 1) • u)
      have s1 : hdist (((γ : Γ) : PO n 1) • u) u = hdist u (((γ : Γ) : PO n 1) • u) :=
        hI'.symm _ _
      linarith
    have hhnotpar : ¬ IsParabolic ((h : Γ) : PO n 1) := fun hp => hnotpar h hhne hhfix hp hhmov
    obtain ⟨p, hp⟩ :=
      (stabParabOrEllip n hn hA hI ((h : Γ) : PO n 1) ξ hξS hhfix hhbc).resolve_left hhnotpar
    have hβ : busemann ξ (((h : Γ) : PO n 1) • (0 : E n)) = 0 := by
      have h := hhbc; rw [bCocy, hhfix] at h; exact h
    obtain ⟨-, hAinner, hAnorm, hact⟩ :=
      stabFlatActionCanon n hA hI ξ hξS ((h : Γ) : PO n 1) hhfix hβ
    obtain ⟨y0, hy0perp, hy0norm, hy0gap⟩ :=
      hgap h (flatLin ξ (LambdaMat ((h : Γ) : PO n 1)))
        (flatTrans ξ (LambdaMat ((h : Γ) : PO n 1))) hhcoe_ne hhfix ⟨p, hp⟩ hAinner hAnorm hact
    -- the multiplication law
    have hAy0 : flatLin ξ (LambdaMat (((γ' : Γ) : PO n 1))) y0
        = flatLin ξ (LambdaMat (((γ : Γ) : PO n 1)))
            (flatLin ξ (LambdaMat (((h : Γ) : PO n 1))) y0) := by
      have hmul := (cuspHoro.flatLinMulLambdaMat n hA hI ξ hξS).1 ((γ : Γ) : PO n 1)
        ((h : Γ) : PO n 1) hfixγ hhfix (hbc γ hfixγ) hhbc y0 hy0perp
      have hprod : ((γ : Γ) : PO n 1) * ((h : Γ) : PO n 1) = ((γ' : Γ) : PO n 1) := by
        rw [hhcoe]; group
      rwa [hprod] at hmul
    -- the linear part of γ is an isometry on ξ^⊥
    have hisom : ‖flatLin ξ (LambdaMat (((γ : Γ) : PO n 1)))
          (flatLin ξ (LambdaMat (((h : Γ) : PO n 1))) y0 - y0)‖
        = ‖flatLin ξ (LambdaMat (((h : Γ) : PO n 1))) y0 - y0‖ := by
      refine flatLinNorm ξ hξS (LambdaMat ((γ : Γ) : PO n 1)) (LambdaMat_isJOrth _)
        (hθΛ γ hfixγ) _ ?_
      rw [inner_sub_left, flatLinInnerZero ξ hξS (LambdaMat ((h : Γ) : PO n 1)) y0, hy0perp,
        sub_zero]
    -- assemble
    have hmain : θ ≤ ‖B γ' y0 - B γ y0‖ := by
      calc θ ≤ ‖flatLin ξ (LambdaMat ((h : Γ) : PO n 1)) y0 - y0‖ := hy0gap
        _ = ‖flatLin ξ (LambdaMat ((γ : Γ) : PO n 1))
              (flatLin ξ (LambdaMat ((h : Γ) : PO n 1)) y0 - y0)‖ := hisom.symm
        _ = ‖flatLin ξ (LambdaMat ((γ : Γ) : PO n 1))
                (flatLin ξ (LambdaMat ((h : Γ) : PO n 1)) y0)
              - flatLin ξ (LambdaMat ((γ : Γ) : PO n 1)) y0‖ := by rw [map_sub]
        _ = ‖flatLin ξ (LambdaMat ((γ' : Γ) : PO n 1)) y0
              - flatLin ξ (LambdaMat ((γ : Γ) : PO n 1)) y0‖ := by rw [hAy0]
        _ = ‖B γ' y0 - B γ y0‖ := by rw [hB_perp γ' y0 hy0perp, hB_perp γ y0 hy0perp]
    have h1 : ‖B γ' y0 - B γ y0‖ ≤ ‖B γ' - B γ‖ * ‖y0‖ := by
      have h0 : B γ' y0 - B γ y0 = (B γ' - B γ) y0 := by rw [sub_apply]
      rw [h0]
      exact ContinuousLinearMap.le_opNorm _ y0
    calc θ ≤ ‖B γ' y0 - B γ y0‖ := hmain
      _ ≤ ‖B γ' - B γ‖ * ‖y0‖ := h1
      _ = ‖B γ' - B γ‖ := by rw [hy0norm, mul_one]
      _ = ‖B γ - B γ'‖ := norm_sub_rev _ _
  -- the packing bound
  obtain ⟨N, hN⟩ := packingOfSeparated (X := E n →L[ℝ] E n) hθ
  refine ⟨N, fun u hfix hnotpar => ?_⟩
  set F : Set Γ := {γ : Γ | hdist u ((γ : PO n 1) • u) < ε / 2} with hF
  have hinj : Set.InjOn B F := by
    intro γ hγ γ' hγ' hEq
    by_contra hne
    have h := hsepB u hfix hnotpar γ hγ γ' hγ' hne
    rw [hEq, sub_self, norm_zero] at h
    exact absurd h (not_le.mpr hθ)
  have hcard : (B '' F).ncard = F.ncard := Set.InjOn.ncard_image hinj
  have hball : ∀ x ∈ B '' F, ‖x‖ ≤ 1 := by
    rintro x ⟨γ, hγF, rfl⟩
    exact hB_le γ (hfix γ hγF)
  have hsep : ∀ x ∈ B '' F, ∀ y ∈ B '' F, x ≠ y → θ ≤ ‖x - y‖ := by
    rintro x ⟨γ, hγF, rfl⟩ y ⟨γ', hγ'F, rfl⟩ hxy
    exact hsepB u hfix hnotpar γ hγF γ' hγ'F (fun h => hxy (by rw [h]))
  rw [← hcard]
  exact hN (B '' F) hball hsep

/-- **The uniform bound on short elements at the frontier of the Margulis region at a cusp.**
For a lattice `Γ ≤ PO(n,1)` (`n ≥ 3`), a cusp `ξ ∈ parFixed Γ` at which the Busemann cocycle of
the stabiliser vanishes (`hvan`), and the elliptic gap `hgap` of `Γ_ξ`, there are `ε > 0` and `N`
such that for every flat point `y ∈ ξ^⊥` at most `N` elements `γ ∈ Γ` move the frontier point
`frontierPt Γ ξ ε y` by less than `ε/2`. -/
theorem frontierShortBoundCusp (n : ℕ) (hn : 3 ≤ n)
    (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) η, η ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) η = η →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) η = 0)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ)
    (θ : ℝ) (hθ : 0 < θ)
    (hgap : ∀ (γ : Γ) (A : Submission.Mostow.E n →ₗ[ℝ] Submission.Mostow.E n) (v : Submission.Mostow.E n),
      (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ≠ 1 →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      (∃ p : Submission.Mostow.E n, (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • p = p) →
      (∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 → inner ℝ (A y) ξ = 0) →
      (∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 → ‖A y‖ = ‖y‖) →
      (∀ (y : Submission.Mostow.E n) (D : ℝ), inner ℝ y ξ = 0 → 0 < D →
        Work.Mostow.lev ξ ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.hptOf ξ y D) = D ∧
        Work.Mostow.yc ξ ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.hptOf ξ y D) = A y + v) →
      ∃ y : Submission.Mostow.E n, inner ℝ y ξ = 0 ∧ ‖y‖ = 1 ∧ θ ≤ ‖A y - y‖) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 →
      {γ : Γ | Submission.Mostow.hdist (Work.Mostow.frontierPt Γ ξ ε y)
        ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.frontierPt Γ ξ ε y) < ε / 2}.ncard ≤ N := by
  have hdisc : IsDiscrete (SetLike.coe Γ) := hΓ.1
  have hξS : ξ ∈ Sph n := hξ.1
  have h2n : 2 ≤ n := by omega
  obtain ⟨εM, hεMpos, hεM⟩ := margulisCusp n h2n hA hI 1
  obtain ⟨ε, hεpos, hε1, hεc⟩ := fsbc_exists_cEps_small εM hεMpos
  obtain ⟨hparDispPos, hthin⟩ := cuspThinRegion_eq_parDisp n hA hI Γ hdisc hvan hξ
  refine ⟨ε, hεpos, ?_⟩
  obtain ⟨N, hN⟩ := frontierShortStabBound n h2n hA hI Γ hξS hξ hvan hθ hεpos hgap
  refine ⟨N, ?_⟩
  intro y hy
  set u : E n := frontierPt Γ ξ ε y with hu
  have hpos : 0 < cEps ε / parDisp Γ ξ y := div_pos (fsbc_cEps_pos hεpos) (hparDispPos y hy)
  have hu_thr : lev ξ u * parDisp Γ ξ (yc ξ u) = cEps ε := frontierPt_threshold hξS hy hpos
  have hfix : ∀ γ : Γ, hdist u ((γ : PO n 1) • u) < ε / 2 → bd (γ : PO n 1) ξ = ξ := by
    intro γ hγ
    obtain ⟨q, hqpar, hqfix, hqdist⟩ :=
      parShortFrontierPt n h2n hA hI Γ hdisc hvan hξ hεpos hεMpos hεc y hy
    exact hεM Γ hdisc u ξ q γ hqpar hξS hqfix hqdist (by linarith [hγ, hε1])
  have hnotpar : ∀ h : Γ, h ≠ 1 → bd (h : PO n 1) ξ = ξ → IsParabolic (h : PO n 1) →
      hdist u ((h : PO n 1) • u) < ε → False := by
    intro h hne hbd hpar hlt
    have hmem : u ∈ cuspThinRegion Γ ξ ε := ⟨h, hpar, hbd, hlt⟩
    rw [hthin ε hεpos u, hu_thr] at hmem
    exact lt_irrefl _ hmem
  exact hN u hfix hnotpar

end

end Work.Mostow
