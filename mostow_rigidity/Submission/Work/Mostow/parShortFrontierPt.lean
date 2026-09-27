import Mathlib
import Submission.Work.Mostow.cuspCocompactDefs
import Submission.Work.Mostow.cuspThinRegion_eq_parDisp

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

variable {n : ℕ}

/-- **A short parabolic element moves the frontier point.**

Let `Γ ≤ PO(n,1)` be a discrete subgroup, `ξ ∈ parFixed Γ` a cusp at which the Busemann cocycle
of the stabiliser vanishes, and `ε ≤ η` in the sense that `2 * cEps ε ≤ cEps η`.  Then for every
flat point `y ∈ ξ^⊥` there is a parabolic `q ∈ Γ` fixing `ξ` which moves the frontier
(threshold) point `frontierPt Γ ξ ε y` of the Margulis region `cuspThinRegion Γ ξ ε` by less
than `η`.

The proof is the horospherical law of cosines.  The frontier point `u = frontierPt Γ ξ ε y`
has level `L := lev ξ u = cEps ε / parDisp Γ ξ y`, and by definition of `parDisp` as an infimum
there is a parabolic `p` fixing `ξ` whose flat displacement `d` at `y` satisfies
`d < 2 * parDisp Γ ξ y`.  Hence `L * d < 2 * cEps ε ≤ cEps η`, and

`cosh (hdist u (p • u)) = 1 + L^2 * d^2 / 2 = 1 + (L * d)^2 / 2 < 1 + (cEps η)^2 / 2 = cosh η`,

so `hdist u (p • u) < η`. -/
theorem parShortFrontierPt (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (hdisc : IsDiscrete (SetLike.coe Γ))
    (hvan : ∀ (γ : Γ) η, η ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) η = η →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) η = 0)
    {ξ : Submission.Mostow.E n} (hξ : ξ ∈ Work.Mostow.parFixed Γ)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (hsmall : 2 * Work.Mostow.cEps ε ≤ Work.Mostow.cEps η)
    (y : Submission.Mostow.E n) (hy : inner ℝ y ξ = 0) :
    ∃ q : Γ, Submission.Mostow.IsParabolic (q : LeanEval.Geometry.MostowRigidity.PO n 1) ∧
      Submission.Mostow.bd (q : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
      Submission.Mostow.hdist (Work.Mostow.frontierPt Γ ξ ε y)
        ((q : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.frontierPt Γ ξ ε y) < η := by
  classical
  have hξS : ξ ∈ Sph n := hξ.1
  have hstab : ∀ (γ : Γ), bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0 :=
    fun γ hγ => hvan γ ξ hξ hγ
  -- the flat displacement of the parabolic stabiliser is strictly positive at `y`
  have hdpos : 0 < parDisp Γ ξ y :=
    parDisp_pos_of_discrete n hA hI Γ hdisc hξS hstab hξ.2 hy
  have hDne : parDisp Γ ξ y ≠ 0 := ne_of_gt hdpos
  have hEpspos : 0 < cEps ε := by
    rw [cEps, Real.sqrt_pos]
    have h1 : 1 < Real.cosh ε := Real.one_lt_cosh.mpr (ne_of_gt hε)
    linarith
  have hratio : 0 < cEps ε / parDisp Γ ξ y := div_pos hEpspos hdpos
  -- `parDisp` is an infimum, attained arbitrarily well: some parabolic moves the flat point `y`
  -- by less than twice `parDisp`
  have hbdd : BddBelow (parDispSet Γ ξ y) :=
    ⟨0, fun r hr => by obtain ⟨γ, -, -, rfl⟩ := hr; exact norm_nonneg _⟩
  have hneS : (parDispSet Γ ξ y).Nonempty :=
    ⟨_, hξ.2.choose, hξ.2.choose_spec.1, hξ.2.choose_spec.2, rfl⟩
  have hlt : sInf (parDispSet Γ ξ y) < 2 * parDisp Γ ξ y := by
    rw [← parDisp_eq_sInf]; linarith
  obtain ⟨s, hs, hsl⟩ := (csInf_lt_iff hbdd hneS).mp hlt
  obtain ⟨p, hppar, hpfix, rfl⟩ := hs
  refine ⟨p, hppar, hpfix, ?_⟩
  -- the level of the frontier point and the facts it preserves
  have hlevu : lev ξ (frontierPt Γ ξ ε y) = cEps ε / parDisp Γ ξ y :=
    lev_frontierPt hξS hy hratio
  have hycu : yc ξ (frontierPt Γ ξ ε y) = y := yc_frontierPt hξS hy hratio
  have hlevp : ∀ u : E n, lev ξ ((p : PO n 1) • u) = lev ξ u :=
    fun u => cuspHoro.lev_smul_of_stab hI hξS hstab p hpfix u
  have h0 : lev ξ ((p : PO n 1) • (0 : E n)) = 1 := by
    rw [hlevp (0 : E n), cuspHoro.lev_zero]
  -- the horospherical law of cosines
  have hcosh := cosh_hdist_smul_horo (POBasic.ofProp hA) (HypIsoData.ofProp hI) hξS hpfix h0
    (frontierPt Γ ξ ε y)
  rw [hlevu] at hcosh
  have hflat : ‖yc ξ (frontierPt Γ ξ ε y) - flatAct ξ (p : PO n 1) (yc ξ (frontierPt Γ ξ ε y))‖
      = ‖y - flatAct ξ (p : PO n 1) y‖ := by rw [hycu]
  rw [hflat] at hcosh
  -- the flat displacement bound gives `L * d < cEps η`
  have hd_lt : ‖y - flatAct ξ (p : PO n 1) y‖ < 2 * parDisp Γ ξ y := hsl
  have hLd : (cEps ε / parDisp Γ ξ y) * ‖y - flatAct ξ (p : PO n 1) y‖ < cEps η := by
    calc (cEps ε / parDisp Γ ξ y) * ‖y - flatAct ξ (p : PO n 1) y‖
        < (cEps ε / parDisp Γ ξ y) * (2 * parDisp Γ ξ y) :=
          mul_lt_mul_of_pos_left hd_lt hratio
      _ = 2 * cEps ε := by field_simp
      _ ≤ cEps η := hsmall
  -- hence `cosh (hdist …) < cosh η`
  have hcosh_eta : Real.cosh η = 1 + (cEps η) ^ 2 / 2 := by
    have hsq : (cEps η) ^ 2 = 2 * (Real.cosh η - 1) := by
      rw [cEps, Real.sq_sqrt]
      linarith [Real.one_le_cosh η]
    rw [hsq]; ring
  have hbound : Real.cosh (hdist (frontierPt Γ ξ ε y)
      ((p : PO n 1) • frontierPt Γ ξ ε y)) < Real.cosh η := by
    rw [hcosh, hcosh_eta]
    have hmul_nn : 0 ≤ (cEps ε / parDisp Γ ξ y) * ‖y - flatAct ξ (p : PO n 1) y‖ :=
      mul_nonneg (le_of_lt hratio) (norm_nonneg _)
    have hsq : ((cEps ε / parDisp Γ ξ y) * ‖y - flatAct ξ (p : PO n 1) y‖) ^ 2
        < (cEps η) ^ 2 :=
      pow_lt_pow_left₀ hLd hmul_nn (by norm_num)
    have hkey : (cEps ε / parDisp Γ ξ y) ^ 2 / 2 * ‖y - flatAct ξ (p : PO n 1) y‖ ^ 2
        = ((cEps ε / parDisp Γ ξ y) * ‖y - flatAct ξ (p : PO n 1) y‖) ^ 2 / 2 := by ring
    rw [hkey]
    linarith
  have hdist_nn : 0 ≤ hdist (frontierPt Γ ξ ε y) ((p : PO n 1) • frontierPt Γ ξ ε y) :=
    (HypIsoData.ofProp hI).nonneg _ _
  have h2 := Real.cosh_lt_cosh.mp hbound
  rw [abs_of_nonneg hdist_nn, abs_of_nonneg (le_of_lt hη)] at h2
  exact h2

end

end Work.Mostow
