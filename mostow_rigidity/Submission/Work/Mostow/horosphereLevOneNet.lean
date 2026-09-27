import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.flatEmbCocompact
import Submission.Work.Mostow.cuspZ2Defs
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.hptOf_yc
import Submission.Work.Mostow.hptOf_hdist
import Submission.Work.Mostow.stabFlatAction
import Submission.Work.Mostow.margulisCuspV2
import Submission.Work.Mostow.paraUniqueFixed
import Submission.Work.Mostow.horSpec
import Submission.Work.Mostow.flatActBasic
import Submission.Work.Mostow.BusemannLipschitz
import Submission.Work.Mostow.cuspFlatTranslationExists

/-!
# The level-one horosphere of a cusp is a net

For a lattice `Γ ≤ PO(n,1)`, a parabolic fixed point `ξ` whose stabiliser preserves the
horospherical levels (`hvan`) and a level-one point `v` at `ξ`, the `Γ`-orbit of the base point
comes within a uniform distance `R` of `v`.

The proof is assembled here from one geometric input, `Work.Mostow.flatTransExists` (a flat
translation in `Γ_ξ`, which for a lattice follows from finite covolume together with Bieberbach's
theorem), and the following steps:

* `lev_smul_of_bCocy_eq_zero`: an element of `Γ` fixing `ξ` with vanishing Busemann cocycle
  preserves all horospherical levels at `ξ`;
* `hdist_flatTrans_horosphereLevOneNet`: a flat translation displaces `u` by `arccosh (1 + (lev ξ u)² ‖v‖²/2)`, which
  tends to `0` as `lev ξ u → 0`;
* `thin_preciselyInvariant`: the thin region `{u | hdist u (δ • u) < ε}` of a parabolic flat
  translation is *precisely invariant*, by the Margulis lemma (`Work.Mostow.margulisCuspV2`) and
  the uniqueness of the parabolic fixed point (`Work.Mostow.paraUniqueFixed`);
* `hemb_of_flatTrans`: consequently the horoball of a suitable level is disjoint from all its
  `Γ`-translates (Shimizu's lemma, horoball form);
* `cuspHoro.flatCocompactEmb`: an embedded horoball forces `Γ_ξ` to act cocompactly on the
  level-one horosphere at `ξ`;
* the final step converts the compact fundamental set into a hyperbolic distance bound.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-! ## Level preservation from the vanishing Busemann cocycle -/

/-- An element of `PO n 1` fixing `ξ` whose Busemann cocycle at `ξ` vanishes preserves every
horospherical level at `ξ`. -/
lemma lev_smul_of_bCocy_eq_zero (hA : POActionProp n) (hI : HypIsometryProp n)
    {ξ : E n} (hξ : ξ ∈ Sph n) (δ : PO n 1) (hδ : bd δ ξ = ξ) (hc : bCocy δ ξ = 0) :
    ∀ u : E n, lev ξ (δ • u) = lev ξ u := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  intro u
  rw [lev_smul_self hI' hA' ξ hξ δ u hδ]
  have h0 : lev ξ (δ • (0 : E n)) = 1 := by
    rw [lev_eq_exp hξ,
      show busemann ξ (δ • (0 : E n)) = bCocy δ ξ from by rw [bCocy, hδ], hc, Real.exp_zero]
  rw [h0, mul_one]

/-! ## The displacement of a flat translation -/

/-- A horospherical flat translation displaces `u` by `arccosh (1 + (lev ξ u)² ‖v‖²/2)`. -/
lemma hdist_flatTrans_horosphereLevOneNet (hI : HypIsometryProp n) {ξ : E n} (hξ : ξ ∈ Sph n)
    (δ : PO n 1) (v : E n) (hlev : ∀ u : E n, lev ξ (δ • u) = lev ξ u)
    (hyc : ∀ u : E n, yc ξ (δ • u) = yc ξ u + v) :
    ∀ u : E n, hdist u (δ • u) = Real.arcosh (1 + (lev ξ u) ^ 2 * ‖v‖ ^ 2 / 2) := by
  have hvd : HypIsoData n := HypIsoData.ofProp hI
  intro u
  have hL : 0 < lev ξ u := lev_pos ξ hξ u
  have h := levYcFormula (ξ := ξ) hξ u (δ • u)
  rw [hlev u, hyc u] at h
  have hycv : yc ξ u - (yc ξ u + v) = -v := by abel
  rw [hycv, norm_neg, div_self (ne_of_gt hL), Real.log_one, Real.cosh_zero] at h
  have harg : (1 : ℝ) + (lev ξ u) ^ 2 * ‖v‖ ^ 2 / 2 = Real.cosh (hdist u (δ • u)) := by
    rw [h]; ring
  rw [harg]
  exact (Real.arcosh_cosh (hvd.nonneg u (δ • u))).symm

/-! ## Precise invariance of the thin region (Margulis) -/

/-- **The thin region of a parabolic element of `Γ_ξ` is precisely invariant.**  For
`δ ∈ Γ` parabolic fixing `ξ` there is `ε > 0` such that the `δ`-thin region
`{u | hdist u (δ • u) < ε}` is disjoint from each of its translates by elements of `Γ` not
fixing `ξ`. -/
lemma thin_preciselyInvariant (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n)
    (hI : HypIsometryProp n) (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ))
    {ξ : E n} (hξ : ξ ∈ Sph n) (δ : Γ) (hδpar : IsParabolic (δ : PO n 1))
    (hδfix : bd (δ : PO n 1) ξ = ξ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ γ : Γ, bd (γ : PO n 1) ξ ≠ ξ →
      Disjoint {u : E n | hdist u ((δ : PO n 1) • u) < ε}
        ((fun u : E n => (γ : PO n 1) • u) '' {u : E n | hdist u ((δ : PO n 1) • u) < ε}) := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  obtain ⟨εM, hεMpos, hM⟩ := margulisCuspV2 n hn hA hI 1
  refine ⟨min εM 1, lt_min hεMpos one_pos, ?_⟩
  intro γ hγ
  rw [Set.disjoint_left]
  intro u hu1 hu2
  obtain ⟨w, hw, hwu⟩ := hu2
  have hwu' : u = (γ : PO n 1) • w := hwu.symm
  -- the conjugate `σ = γ δ γ⁻¹` and its displacement of `u`
  set σ : Γ := ⟨(γ : PO n 1) * (δ : PO n 1) * (γ : PO n 1)⁻¹,
      mul_mem (mul_mem γ.2 δ.2) (inv_mem γ.2)⟩ with hσdef
  have hσcoe : (σ : PO n 1) = (γ : PO n 1) * (δ : PO n 1) * (γ : PO n 1)⁻¹ := rfl
  have hconj : hdist u ((σ : PO n 1) • u) = hdist w ((δ : PO n 1) • w) := by
    rw [hσcoe, hwu']
    have hrew : ((γ : PO n 1) * (δ : PO n 1) * (γ : PO n 1)⁻¹) • ((γ : PO n 1) • w)
        = (γ : PO n 1) • ((δ : PO n 1) • w) := by
      rw [hA'.mul_smul, hA'.mul_smul]
      congr 1
      rw [← hA'.mul_smul (γ : PO n 1)⁻¹ (γ : PO n 1) w, inv_mul_cancel, hA'.one_smul]
    rw [hrew, hI'.isom_smul]
  have h1 : hdist u ((δ : PO n 1) • u) < min εM 1 := hu1
  have h2 : hdist u ((σ : PO n 1) • u) ≤ 1 := by
    rw [hconj]
    exact le_of_lt (lt_of_lt_of_le hw (min_le_right _ _))
  have hlt' : hdist u ((δ : PO n 1) • u) < εM := lt_of_lt_of_le h1 (min_le_left _ _)
  have hfix' : bd (σ : PO n 1) ξ = ξ :=
    hM Γ hdisc u ξ δ σ hδpar hξ hδfix hlt' h2
  -- uniqueness of the parabolic fixed point
  have hσpar : IsParabolic (σ : PO n 1) := by
    rw [hσcoe]
    exact isParabolic_conj hA hI (γ : PO n 1) (δ : PO n 1) hδpar
  have hbdγ : bd (γ : PO n 1) ξ ∈ Sph n := hA'.bd_mem (γ : PO n 1) ξ hξ
  have h4 : bd (γ : PO n 1)⁻¹ (bd (γ : PO n 1) ξ) = ξ := by
    rw [← hA'.bd_mul (γ : PO n 1)⁻¹ (γ : PO n 1) ξ hξ, inv_mul_cancel, hA'.bd_one ξ hξ]
  have hσγ : bd (σ : PO n 1) (bd (γ : PO n 1) ξ) = bd (γ : PO n 1) ξ := by
    calc bd (σ : PO n 1) (bd (γ : PO n 1) ξ)
        = bd ((γ : PO n 1) * (δ : PO n 1) * (γ : PO n 1)⁻¹) (bd (γ : PO n 1) ξ) := by rw [hσcoe]
      _ = bd ((γ : PO n 1) * (δ : PO n 1)) (bd (γ : PO n 1)⁻¹ (bd (γ : PO n 1) ξ)) := by
            rw [hA'.bd_mul ((γ : PO n 1) * (δ : PO n 1)) ((γ : PO n 1)⁻¹) (bd (γ : PO n 1) ξ) hbdγ]
      _ = bd ((γ : PO n 1) * (δ : PO n 1)) ξ := by rw [h4]
      _ = bd (γ : PO n 1) (bd (δ : PO n 1) ξ) := by rw [hA'.bd_mul (γ : PO n 1) (δ : PO n 1) ξ hξ]
      _ = bd (γ : PO n 1) ξ := by rw [hδfix]
  exact hγ (paraUniqueFixed hA' hI' hσpar hξ hfix' hbdγ hσγ)

/-! ## Shimizu's lemma (horoball form) from a flat translation -/

/-- **Shimizu's lemma, horoball form.**  If `Γ_ξ` contains a parabolic *flat translation*
`δ` (fixing `ξ`, preserving the levels, with `yc ξ (δ • u) = yc ξ u + v`, `v ≠ 0`), then some
horoball at `ξ` is disjoint from all its `Γ`-translates. -/
lemma hemb_of_flatTrans (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ))
    {ξ : E n} (hξ : ξ ∈ Sph n) (δ : Γ) (v : E n) (hv : v ≠ 0)
    (hδpar : IsParabolic (δ : PO n 1)) (hδfix : bd (δ : PO n 1) ξ = ξ)
    (hc : bCocy (δ : PO n 1) ξ = 0)
    (hyc : ∀ u : E n, yc ξ ((δ : PO n 1) • u) = yc ξ u + v) :
    ∃ τ : ℝ, ∀ γ : Γ, bd (γ : PO n 1) ξ ≠ ξ →
      Disjoint (horoball ξ τ) (horoball (bd (γ : PO n 1) ξ) (τ + bCocy (γ : PO n 1) ξ)) := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  have hlevδ : ∀ u : E n, lev ξ ((δ : PO n 1) • u) = lev ξ u :=
    lev_smul_of_bCocy_eq_zero hA hI hξ (δ : PO n 1) hδfix hc
  have hdisp := hdist_flatTrans_horosphereLevOneNet hI hξ (δ : PO n 1) v hlevδ hyc
  obtain ⟨ε, hεpos, hprec⟩ := thin_preciselyInvariant n hn hA hI Γ hdisc hξ δ hδpar hδfix
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hcoshε : 1 < Real.cosh ε := Real.one_lt_cosh.mpr (ne_of_gt hεpos)
  have hspos : 0 < Real.sqrt (2 * (Real.cosh ε - 1)) := Real.sqrt_pos.mpr (by linarith)
  set τ : ℝ := Real.log (Real.sqrt (2 * (Real.cosh ε - 1)) / ‖v‖) with hτdef
  have hτpos : 0 < Real.sqrt (2 * (Real.cosh ε - 1)) / ‖v‖ := div_pos hspos hvpos
  have hexpτ : Real.exp τ = Real.sqrt (2 * (Real.cosh ε - 1)) / ‖v‖ := Real.exp_log hτpos
  -- the key estimate: if `lev ξ w < exp τ` then `hdist w (δ • w) < ε`
  have hkey : ∀ w : E n, lev ξ w < Real.exp τ → hdist w ((δ : PO n 1) • w) < ε := by
    intro w hw
    rw [hdisp w]
    have hw' : lev ξ w * ‖v‖ < Real.sqrt (2 * (Real.cosh ε - 1)) := by
      have h1 : lev ξ w < Real.sqrt (2 * (Real.cosh ε - 1)) / ‖v‖ := by rw [← hexpτ]; exact hw
      rw [lt_div_iff₀ hvpos] at h1
      linarith
    have hsq : (Real.sqrt (2 * (Real.cosh ε - 1))) ^ 2 = 2 * (Real.cosh ε - 1) :=
      Real.sq_sqrt (by linarith)
    have h2 : (lev ξ w) ^ 2 * ‖v‖ ^ 2 < 2 * (Real.cosh ε - 1) := by
      have h3 : (lev ξ w * ‖v‖) ^ 2 < (Real.sqrt (2 * (Real.cosh ε - 1))) ^ 2 := by
        have ha : 0 ≤ lev ξ w * ‖v‖ := mul_nonneg (le_of_lt (lev_pos ξ hξ w)) (le_of_lt hvpos)
        have hb0 : 0 ≤ Real.sqrt (2 * (Real.cosh ε - 1)) := Real.sqrt_nonneg _
        nlinarith [hw', ha, hb0]
      nlinarith [h3, hsq]
    have h4 : 1 + (lev ξ w) ^ 2 * ‖v‖ ^ 2 / 2 < Real.cosh ε := by linarith
    rw [show ε = Real.arcosh (Real.cosh ε) from (Real.arcosh_cosh (le_of_lt hεpos)).symm]
    exact (Real.arcosh_lt_arcosh (by positivity) (Real.cosh_pos ε)).mpr h4
  refine ⟨τ, fun γ hγ => ?_⟩
  rw [Set.disjoint_left]
  intro u hu1 hu2
  simp only [horoball, Set.mem_ofPred_eq] at hu1 hu2
  -- the level at `ξ` of `γ⁻¹ u`
  have hb : busemann ξ ((γ : PO n 1)⁻¹ • u)
      = busemann (bd (γ : PO n 1) ξ) u - bCocy (γ : PO n 1) ξ := by
    have h := hI'.busemann_cocycle (γ : PO n 1) ξ ((γ : PO n 1)⁻¹ • u) hξ
    have hsm : (γ : PO n 1) • ((γ : PO n 1)⁻¹ • u) = u := by
      rw [← hA'.mul_smul, mul_inv_cancel, hA'.one_smul]
    rw [hsm] at h
    rw [show bCocy (γ : PO n 1) ξ
      = busemann (bd (γ : PO n 1) ξ) ((γ : PO n 1) • (0 : E n)) from rfl]
    linarith
  have hu2' : busemann (bd (γ : PO n 1) ξ) u
      < τ + busemann (bd (γ : PO n 1) ξ) ((γ : PO n 1) • (0 : E n)) := hu2
  have hlevinv : lev ξ ((γ : PO n 1)⁻¹ • u) < Real.exp τ := by
    rw [lev_eq_exp hξ, Real.exp_lt_exp, hb]
    rw [show bCocy (γ : PO n 1) ξ
      = busemann (bd (γ : PO n 1) ξ) ((γ : PO n 1) • (0 : E n)) from rfl]
    linarith
  have hlevu : lev ξ u < Real.exp τ := by
    rw [lev_eq_exp hξ, Real.exp_lt_exp]
    exact hu1
  refine (Set.disjoint_left.mp (hprec γ hγ)) (hkey u hlevu) ?_
  exact ⟨(γ : PO n 1)⁻¹ • u, hkey ((γ : PO n 1)⁻¹ • u) hlevinv,
    by show (γ : PO n 1) • ((γ : PO n 1)⁻¹ • u) = u
       rw [← hA'.mul_smul, mul_inv_cancel, hA'.one_smul]⟩

/-! ## The geometric input: a flat translation in the cusp stabiliser -/

/-- **Flat translation in the cusp stabiliser.**  For a lattice `Γ ≤ PO(n,1)` and a parabolic
fixed point `ξ` with vanishing cocycle on `Γ_ξ`, the stabiliser contains a parabolic element
acting on the horospheres at `ξ` by a nonzero flat translation. -/
lemma flatTransExists (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hBb : ∀ m, BieberbachProp m) (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ)
    (hvan : ∀ (γ : Γ) η, η ∈ parFixed Γ → bd (γ : PO n 1) η = η → bCocy (γ : PO n 1) η = 0)
    (ξ : E n) (hξ : ξ ∈ parFixed Γ) :
    ∃ δ : Γ, IsParabolic (δ : PO n 1) ∧ bd (δ : PO n 1) ξ = ξ ∧ bCocy (δ : PO n 1) ξ = 0 ∧
      ∃ v : E n, v ≠ 0 ∧ inner ℝ v ξ = 0 ∧
        ∀ u : E n, yc ξ ((δ : PO n 1) • u) = yc ξ u + v :=
  cuspFlatTranslationExists n hn hA hI hBb Γ hΓ hvan ξ hξ

/-! ## The target -/

theorem horosphereLevOneNet (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (hBb : ∀ m, Submission.Mostow.BieberbachProp m)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) η, η ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) η = η →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) η = 0)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ) :
    ∃ R : ℝ, ∀ v : Submission.Mostow.E n, Work.Mostow.lev ξ v = 1 →
      ∃ γ : Γ, Submission.Mostow.hdist ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • v)
        (0 : Submission.Mostow.E n) ≤ R := by
  obtain ⟨δ, hδpar, hδfix, hc, v, hv, -, hyc⟩ := flatTransExists n hn hA hI hBb Γ hΓ hvan ξ hξ
  obtain ⟨τ, hemb⟩ := hemb_of_flatTrans n hn hA hI Γ hΓ.1 hξ.1 δ v hv hδpar hδfix hc hyc
  obtain ⟨K, hKc, hK⟩ := cuspHoro.flatCocompactEmb n hn hA hI Γ hΓ ξ hξ hvan τ hemb
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  have hcont : Continuous fun x : E n => hdist x (0 : E n) :=
    (Work.Mostow.hdist_continuous_left (0 : E n)).congr (fun x => (hI'.symm x 0).symm)
  obtain ⟨R, hR⟩ := hKc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨R, fun w hw => ?_⟩
  obtain ⟨γ, -, hγK⟩ := hK w hw
  refine ⟨γ, ?_⟩
  have hb := hR _ hγK
  rw [Real.norm_eq_abs, abs_of_nonneg (hI'.nonneg _ _)] at hb
  exact hb

end

end Work.Mostow
