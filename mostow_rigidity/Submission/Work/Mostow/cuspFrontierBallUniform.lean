import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.cuspParDispDefs
import Submission.Work.Mostow.cuspThinRegionDefs
import Submission.Work.Mostow.cuspThinRegion_eq_parDisp
import Submission.Work.Mostow.parDisp_lipschitz_invariant
import Submission.Work.Mostow.cuspHoro.flatDispEqLevOne
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.levYcFormula

namespace Work.Mostow

/-- `cEps ε = √(2 (cosh ε - 1))` is strictly increasing on the positive reals. -/
lemma cEps_lt_cEps_of_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) : cEps a < cEps b := by
  have hb : 0 < b := lt_trans ha hab
  have hcosh : Real.cosh a < Real.cosh b := by
    rw [Real.cosh_lt_cosh, abs_of_pos ha, abs_of_pos hb]; exact hab
  have h1 : 0 < 2 * (Real.cosh a - 1) := by
    have := Real.one_lt_cosh.mpr (ne_of_gt ha); linarith
  have h2 : 2 * (Real.cosh a - 1) < 2 * (Real.cosh b - 1) := by linarith
  rw [cEps, cEps]
  exact Real.sqrt_lt_sqrt (le_of_lt h1) h2

/-- **Uniform ball around the frontier of the Margulis cusp region.**

At a parabolic fixed point `η ∈ parFixed Γ` at which the Busemann cocycle of the stabiliser
vanishes, let `u` be any point of the level-`ε` frontier of the thin region, i.e.
`lev η u * parDisp Γ η (yc η u) = cEps ε`.  Then the whole hyperbolic ball of radius `r * ε`
about `u`, with `r = 1/4`, is contained in the thin region of the *doubled* level `2 * ε`.

The proof is uniform in `η` and in `ε` (any `ε > 0` works): writing
`D := parDisp Γ η (yc η u)` and using that `D` is the infimum of the flat displacements of the
parabolic elements of `Γ` fixing `η`, we choose a parabolic `q` fixing `η` whose flat
displacement at `yc η u` is below `cEps (2 * (1 - 1/4) * ε) / lev η u`.  The horospherical law of
cosines (`hdist_lt_iff_lev_mul_flatAct`) turns this into `hdist u (q • u) < 2 * (1 - 1/4) * ε`,
and the triangle inequality plus the isometry property of the action gives
`hdist w (q • w) ≤ 2 * (1/4) * ε + hdist u (q • u) < 2 * ε`. -/
theorem cuspFrontierBallUniform (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ r : ℝ, 0 < r ∧ ∀ η : Submission.Mostow.E n,
      η ∈ Work.Mostow.parFixed Γ → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ u : Submission.Mostow.E n,
      Work.Mostow.lev η u * Work.Mostow.parDisp Γ η (Work.Mostow.yc η u) = Work.Mostow.cEps ε →
      ∀ w : Submission.Mostow.E n, Submission.Mostow.hdist u w ≤ r * ε →
        w ∈ Work.Mostow.cuspThinRegion Γ η (2 * ε) := by
  refine ⟨1, one_pos, 1 / 4, by norm_num, ?_⟩
  intro η hη ε hε _hεle u hu w hw
  have hηS : η ∈ Submission.Mostow.Sph n := hη.1
  have hstab : ∀ (γ : Γ), Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) η = η →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) η = 0 :=
    fun γ hγ => hvan γ η hη hγ
  have hL : 0 < Work.Mostow.lev η u := Work.Mostow.lev_pos η hηS u
  -- the flat-displacement set at `yc η u` and its infimum `parDisp`
  have hSne : (Work.Mostow.parDispSet Γ η (Work.Mostow.yc η u)).Nonempty :=
    Work.Mostow.parDispSet_nonempty hη (Work.Mostow.yc η u)
  have hSbdd : BddBelow (Work.Mostow.parDispSet Γ η (Work.Mostow.yc η u)) :=
    Work.Mostow.parDispSet_bddBelow Γ η (Work.Mostow.yc η u)
  have hcEps_lt : Work.Mostow.cEps ε < Work.Mostow.cEps (2 * (1 - 1 / 4) * ε) := by
    refine Work.Mostow.cEps_lt_cEps_of_pos hε ?_
    linarith
  have h1 : Work.Mostow.lev η u * sInf (Work.Mostow.parDispSet Γ η (Work.Mostow.yc η u))
      = Work.Mostow.cEps ε := by
    simpa only [Work.Mostow.parDisp_eq_sInf] using hu
  have h2 : sInf (Work.Mostow.parDispSet Γ η (Work.Mostow.yc η u))
      < Work.Mostow.cEps (2 * (1 - 1 / 4) * ε) / Work.Mostow.lev η u := by
    rw [lt_div_iff₀ hL, mul_comm, h1]
    exact hcEps_lt
  -- a parabolic `q ∈ Γ` fixing `η` with small flat displacement at `yc η u`
  obtain ⟨s, hsS, hslt⟩ := exists_lt_of_csInf_lt hSne h2
  obtain ⟨q, hqpar, hqfix, hqeq⟩ := hsS
  have hdisp_lt : Work.Mostow.lev η u *
      ‖Work.Mostow.yc η u - Work.Mostow.flatAct η (q : LeanEval.Geometry.MostowRigidity.PO n 1)
        (Work.Mostow.yc η u)‖ < Work.Mostow.cEps (2 * (1 - 1 / 4) * ε) := by
    have h := mul_lt_mul_of_pos_left hslt hL
    rw [hqeq] at h
    have hc : Work.Mostow.lev η u *
        (Work.Mostow.cEps (2 * (1 - 1 / 4) * ε) / Work.Mostow.lev η u)
        = Work.Mostow.cEps (2 * (1 - 1 / 4) * ε) := by
      field_simp
    rw [hc] at h
    exact h
  -- the level is preserved by `q`
  have hleval : ∀ v : Submission.Mostow.E n,
      Work.Mostow.lev η ((q : LeanEval.Geometry.MostowRigidity.PO n 1) • v)
        = Work.Mostow.lev η v :=
    fun v => Work.Mostow.cuspHoro.lev_smul_of_stab hI hηS hstab q hqfix v
  have hε' : 0 < 2 * (1 - 1 / 4) * ε := by linarith
  have hdistqu : Submission.Mostow.hdist u
      ((q : LeanEval.Geometry.MostowRigidity.PO n 1) • u) < 2 * (1 - 1 / 4) * ε :=
    (Work.Mostow.hdist_lt_iff_lev_mul_flatAct n hA hI hηS
      (q : LeanEval.Geometry.MostowRigidity.PO n 1) hqfix hleval u hε').mpr hdisp_lt
  refine ⟨q, hqpar, hqfix, ?_⟩
  have hId : HypIsoData n := HypIsoData.ofProp hI
  have htri1 : Submission.Mostow.hdist w
        ((q : LeanEval.Geometry.MostowRigidity.PO n 1) • w) ≤
      Submission.Mostow.hdist w ((q : LeanEval.Geometry.MostowRigidity.PO n 1) • u)
        + Submission.Mostow.hdist ((q : LeanEval.Geometry.MostowRigidity.PO n 1) • u)
            ((q : LeanEval.Geometry.MostowRigidity.PO n 1) • w) :=
    hId.triangle w ((q : LeanEval.Geometry.MostowRigidity.PO n 1) • u)
      ((q : LeanEval.Geometry.MostowRigidity.PO n 1) • w)
  have htri2 : Submission.Mostow.hdist w
        ((q : LeanEval.Geometry.MostowRigidity.PO n 1) • u) ≤
      Submission.Mostow.hdist w u + Submission.Mostow.hdist u
        ((q : LeanEval.Geometry.MostowRigidity.PO n 1) • u) :=
    hId.triangle w u ((q : LeanEval.Geometry.MostowRigidity.PO n 1) • u)
  have hiso : Submission.Mostow.hdist ((q : LeanEval.Geometry.MostowRigidity.PO n 1) • u)
      ((q : LeanEval.Geometry.MostowRigidity.PO n 1) • w) = Submission.Mostow.hdist u w :=
    hId.isom_smul (q : LeanEval.Geometry.MostowRigidity.PO n 1) u w
  have hwu : Submission.Mostow.hdist w u ≤ (1 / 4) * ε := by
    rw [hId.symm w u]; exact hw
  linarith [htri1, htri2, hiso, hwu, hw, hdistqu]

end Work.Mostow
