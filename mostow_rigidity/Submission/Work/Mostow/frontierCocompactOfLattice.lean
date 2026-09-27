import Mathlib
import Submission.Work.Mostow.cuspCocompactDefs
import Submission.Work.Mostow.cuspThinRegion_eq_parDisp
import Submission.Work.Mostow.geomFiniteMultThick
import Submission.Work.Mostow.cuspThinBase
import Submission.Work.Mostow.parDisp_lipschitz_invariant
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.cuspHoro.flatDispEqLevOne
import Submission.Work.Mostow.paraUniqueFixed
import Submission.Work.Mostow.finite_translates_inter_compact

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

set_option maxHeartbeats 1000000

variable {n : ℕ}

lemma frontierPt_hdist_parabolic (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) η, η ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) η = η →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) η = 0)
    {ξ : Submission.Mostow.E n} (hξ : ξ ∈ Work.Mostow.parFixed Γ) {y : Submission.Mostow.E n}
    (hy : inner ℝ y ξ = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Γ, Submission.Mostow.IsParabolic (p : LeanEval.Geometry.MostowRigidity.PO n 1) ∧
      Submission.Mostow.bd (p : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
      Submission.Mostow.hdist (Work.Mostow.frontierPt Γ ξ ε y)
        ((p : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.frontierPt Γ ξ ε y)
        ≤ 2 * ε := by
  have hξS : ξ ∈ Sph n := hξ.1
  have hstab : ∀ (γ : Γ), bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0 :=
    fun γ hγ => hvan γ ξ hξ hγ
  have hdpos : 0 < parDisp Γ ξ y :=
    parDisp_pos_of_discrete n hA hI Γ hΓ.1 hξS hstab hξ.2 hy
  have hEpspos : 0 < cEps ε := by
    rw [cEps, Real.sqrt_pos]
    have h1 : 1 < Real.cosh ε := Real.one_lt_cosh.mpr (ne_of_gt hε)
    linarith
  have hratio : 0 < cEps ε / parDisp Γ ξ y := div_pos hEpspos hdpos
  have hlt : sInf (parDispSet Γ ξ y) < 2 * parDisp Γ ξ y := by
    rw [← parDisp_eq_sInf]; linarith
  obtain ⟨s, hs, hsl⟩ := (csInf_lt_iff (parDispSet_bddBelow Γ ξ y)
    (parDispSet_nonempty hξ y)).mp hlt
  obtain ⟨p, hppar, hpfix, rfl⟩ := hs
  refine ⟨p, hppar, hpfix, ?_⟩
  have hlevu : lev ξ (frontierPt Γ ξ ε y) = cEps ε / parDisp Γ ξ y :=
    lev_frontierPt hξS hy hratio
  have hycu : yc ξ (frontierPt Γ ξ ε y) = y := yc_frontierPt hξS hy hratio
  have hlevp : ∀ u : E n, lev ξ ((p : PO n 1) • u) = lev ξ u :=
    lev_smul_of_bCocy_zero hI hξS (p : PO n 1) hpfix (hstab p hpfix)
  have hflat : ‖yc ξ ((p : PO n 1) • frontierPt Γ ξ ε y) - yc ξ (frontierPt Γ ξ ε y)‖
      = ‖y - flatAct ξ (p : PO n 1) y‖ := by
    rw [cuspHoro.yc_smul_eq_flatAct hA hI ξ hξS (p : PO n 1) hpfix hlevp
      (frontierPt Γ ξ ε y), hycu]
    exact norm_sub_rev _ _
  have hdisp_lt : ‖yc ξ ((p : PO n 1) • frontierPt Γ ξ ε y) - yc ξ (frontierPt Γ ξ ε y)‖
      < 2 * parDisp Γ ξ y := by rw [hflat]; exact hsl
  have hcosh := cosh_hdist_of_level_preserving hI hξS (p : PO n 1) hlevp (frontierPt Γ ξ ε y)
  rw [hlevu] at hcosh
  have hcEps_sq : (cEps ε) ^ 2 = 2 * (Real.cosh ε - 1) := by
    rw [cEps, Real.sq_sqrt]
    have h1 : 1 ≤ Real.cosh ε := Real.one_le_cosh ε
    linarith
  have hdne : parDisp Γ ξ y ≠ 0 := ne_of_gt hdpos
  have hdisp_nn : 0 ≤ ‖yc ξ ((p : PO n 1) • frontierPt Γ ξ ε y) - yc ξ (frontierPt Γ ξ ε y)‖ :=
    norm_nonneg _
  have hsqq : ‖yc ξ ((p : PO n 1) • frontierPt Γ ξ ε y) - yc ξ (frontierPt Γ ξ ε y)‖ ^ 2
      < (2 * parDisp Γ ξ y) ^ 2 := by
    have := pow_lt_pow_left₀ hdisp_lt hdisp_nn (by norm_num : (2:ℕ) ≠ 0)
    simpa using this
  have hbound : Real.cosh (hdist (frontierPt Γ ξ ε y) ((p : PO n 1) • frontierPt Γ ξ ε y))
      < Real.cosh (2 * ε) := by
    rw [hcosh]
    have hpos : 0 < (cEps ε / parDisp Γ ξ y) ^ 2 := by positivity
    have hstep1 : 1 + (cEps ε / parDisp Γ ξ y) ^ 2
          * ‖yc ξ ((p : PO n 1) • frontierPt Γ ξ ε y)
              - yc ξ (frontierPt Γ ξ ε y)‖ ^ 2 / 2
        < 1 + (cEps ε / parDisp Γ ξ y) ^ 2 * (2 * parDisp Γ ξ y) ^ 2 / 2 := by
      nlinarith [hsqq, hpos]
    have htarget : 1 + (cEps ε / parDisp Γ ξ y) ^ 2 * (2 * parDisp Γ ξ y) ^ 2 / 2
        = 4 * Real.cosh ε - 3 := by
      rw [div_pow, hcEps_sq]
      field_simp
      ring
    have hcosh2 : Real.cosh (2 * ε) = 2 * (Real.cosh ε) ^ 2 - 1 := by
      rw [Real.cosh_two_mul]
      nlinarith [Real.cosh_sq_sub_sinh_sq ε]
    have h2 : 1 + (cEps ε / parDisp Γ ξ y) ^ 2 * (2 * parDisp Γ ξ y) ^ 2 / 2
        ≤ Real.cosh (2 * ε) := by
      rw [htarget, hcosh2]
      nlinarith [sq_nonneg (Real.cosh ε - 1)]
    linarith [hstep1, h2]
  have hlt2 : hdist (frontierPt Γ ξ ε y) ((p : PO n 1) • frontierPt Γ ξ ε y) < 2 * ε := by
    have h2 := (Real.cosh_lt_cosh.mp hbound)
    rw [abs_of_nonneg ((HypIsoData.ofProp hI).nonneg _ _),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * ε)] at h2
    exact h2
  exact le_of_lt hlt2

lemma finite_short_set (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    {Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)}
    (hdisc : IsDiscrete (SetLike.coe Γ)) (u : Submission.Mostow.E n) {δ : ℝ} :
    ({γ : Γ | Submission.Mostow.hdist u
      ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) < δ}).Finite := by
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  have hb : IsCompact ({w : E n | hdist u w ≤ max δ 0}) := hI'.ball_compact u (max δ 0)
  have h1 := finite_translates_inter_compact n hA hI hdisc (K₁ := {u})
    (K₂ := {w : E n | hdist u w ≤ max δ 0}) isCompact_singleton hb
  refine h1.subset ?_
  intro γ hγ
  refine ⟨γ • u, ⟨⟨u, rfl, rfl⟩, ?_⟩⟩
  show hdist u (γ • u) ≤ max δ 0
  exact le_trans (le_of_lt hγ) (le_max_left _ _)


theorem frontierCocompactOfLattice (n : ℕ) (hn : 3 ≤ n)
    (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) η, η ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) η = η →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) η = 0)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ)
    (hshort : ∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 →
      {γ : Γ | Submission.Mostow.hdist (Work.Mostow.frontierPt Γ ξ ε y)
        ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.frontierPt Γ ξ ε y) < ε / 2}.ncard ≤ N) :
    ∃ K : Set (Submission.Mostow.E n), IsCompact K ∧ ∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 →
      ∃ σ : Γ, Submission.Mostow.bd (σ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
        (σ : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.frontierPt Γ ξ ε y ∈ K := by
  classical
  have hξS : ξ ∈ Sph n := hξ.1
  have hpb : POBasic n := POBasic.ofProp hA
  have hvd : HypIsoData n := HypIsoData.ofProp hI
  have hstab : ∀ (γ : Γ), bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0 :=
    fun γ hγ => hvan γ ξ hξ hγ
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨K₀, hK₀c, hK₀⟩ := geomFiniteMultThick n (by omega) hA hI Γ hΓ (ε / 2) hε2 N
  let Y := {y : Submission.Mostow.E n // inner ℝ y ξ = 0}
  have hmult : ∀ y : Y, ({γ : Γ | Submission.Mostow.hdist (Work.Mostow.frontierPt Γ ξ ε y.1)
      ((γ : PO n 1) • Work.Mostow.frontierPt Γ ξ ε y.1) < ε / 2}).Finite ∧
      ({γ : Γ | Submission.Mostow.hdist (Work.Mostow.frontierPt Γ ξ ε y.1)
      ((γ : PO n 1) • Work.Mostow.frontierPt Γ ξ ε y.1) < ε / 2}).ncard ≤ N :=
    fun y => ⟨finite_short_set n hA hI hΓ.1 _ (δ := ε / 2), hshort y.1 y.2⟩
  let γf : Y → Γ := fun y =>
    Classical.choose (hK₀ (Work.Mostow.frontierPt Γ ξ ε y.1) (hmult y))
  have hγf : ∀ y : Y, (γf y : PO n 1) • Work.Mostow.frontierPt Γ ξ ε y.1 ∈ K₀ :=
    fun y => Classical.choose_spec (hK₀ (Work.Mostow.frontierPt Γ ξ ε y.1) (hmult y))
  let pf : Y → Γ := fun y =>
    Classical.choose (frontierPt_hdist_parabolic n hA hI Γ hΓ hvan hξ y.2 hε)
  have hpf : ∀ y : Y, IsParabolic (pf y : PO n 1) ∧ bd (pf y : PO n 1) ξ = ξ ∧
      hdist (Work.Mostow.frontierPt Γ ξ ε y.1)
        ((pf y : PO n 1) • Work.Mostow.frontierPt Γ ξ ε y.1) ≤ 2 * ε :=
    fun y => Classical.choose_spec (frontierPt_hdist_parabolic n hA hI Γ hΓ hvan hξ y.2 hε)
  let hf : Y → Γ := fun y => γf y * pf y * (γf y)⁻¹
  let cusp : Y → Submission.Mostow.E n := fun y => bd (γf y : PO n 1) ξ
  have hcoe_hf : ∀ y : Y, ((hf y : Γ) : PO n 1)
      = (γf y : PO n 1) * (pf y : PO n 1) * (γf y : PO n 1)⁻¹ := fun y => rfl
  have hcuspS : ∀ y : Y, cusp y ∈ Sph n := fun y => hpb.bd_mem (γf y : PO n 1) ξ hξS
  have hcusp_fix : ∀ y : Y, bd ((hf y : Γ) : PO n 1) (cusp y) = cusp y := by
    intro y
    rw [hcoe_hf y,
      hpb.bd_mul ((γf y : PO n 1) * (pf y : PO n 1)) ((γf y : PO n 1)⁻¹) (cusp y)
        (hcuspS y),
      show bd ((γf y : PO n 1)⁻¹) (cusp y) = ξ from bd_inv_bd hA hξS,
      hpb.bd_mul (γf y : PO n 1) (pf y : PO n 1) ξ hξS, (hpf y).2.1]
  have hpar_hf : ∀ y : Y, IsParabolic ((hf y : Γ) : PO n 1) := by
    intro y
    rw [hcoe_hf y]
    exact isParabolic_conj hA hI (γf y : PO n 1) (pf y : PO n 1) (hpf y).1
  have hkey : ∀ y y' : Y, hf y = hf y' → cusp y = cusp y' := by
    intro y y' heq
    have heq' : ((hf y : Γ) : PO n 1) = ((hf y' : Γ) : PO n 1) := by rw [heq]
    have h1 : bd ((hf y : Γ) : PO n 1) (cusp y') = cusp y' := by
      rw [heq']; exact hcusp_fix y'
    exact (paraUniqueFixed hpb hvd (hpar_hf y) (hcuspS y) (hcusp_fix y) (hcuspS y') h1).symm
  set H : Set Γ := {h : Γ | ∃ w ∈ K₀, hdist w ((h : PO n 1) • w) ≤ 2 * ε} with hHdef
  have hHmem : ∀ y : Y, hf y ∈ H := by
    intro y
    rw [hHdef]
    refine ⟨(γf y : PO n 1) • Work.Mostow.frontierPt Γ ξ ε y.1, hγf y, ?_⟩
    have h1 : ((γf y : PO n 1)⁻¹) • ((γf y : PO n 1) • Work.Mostow.frontierPt Γ ξ ε y.1)
        = Work.Mostow.frontierPt Γ ξ ε y.1 := by
      rw [← hpb.mul_smul, inv_mul_cancel, hpb.one_smul]
    show hdist ((γf y : PO n 1) • Work.Mostow.frontierPt Γ ξ ε y.1)
      (((hf y : Γ) : PO n 1) • ((γf y : PO n 1) • Work.Mostow.frontierPt Γ ξ ε y.1)) ≤ 2 * ε
    rw [hcoe_hf y, hpb.mul_smul, hpb.mul_smul, h1, hvd.isom_smul]
    exact (hpf y).2.2
  have hY0 : Y := ⟨0, by simp⟩
  obtain ⟨w₀, hw₀⟩ : K₀.Nonempty := ⟨_, hγf hY0⟩
  obtain ⟨M, hM⟩ := exists_hdist_le_of_isCompact hI hK₀c
  have hHfin : H.Finite := by
    rw [hHdef]
    have hR₀ : ∀ w ∈ K₀, hdist w₀ w ≤ hdist 0 w₀ + M := by
      intro w hw
      calc hdist w₀ w ≤ hdist w₀ 0 + hdist 0 w := hvd.triangle w₀ 0 w
        _ = hdist 0 w₀ + hdist 0 w := by rw [hvd.symm w₀ 0]
        _ ≤ hdist 0 w₀ + M := by linarith [hM w hw]
    have hb : IsCompact ({w : Submission.Mostow.E n | hdist w₀ w ≤ 2 * (hdist 0 w₀ + M) + 2 * ε})
        := hvd.ball_compact w₀ _
    have h1 := finite_translates_inter_compact n hA hI hΓ.1 (K₁ := {w₀})
      (K₂ := {w : Submission.Mostow.E n | hdist w₀ w ≤ 2 * (hdist 0 w₀ + M) + 2 * ε})
      isCompact_singleton hb
    refine h1.subset ?_
    rintro h ⟨w, hw, hd⟩
    refine ⟨(h : PO n 1) • w₀, ⟨⟨w₀, rfl, rfl⟩, ?_⟩⟩
    show hdist w₀ ((h : PO n 1) • w₀) ≤ 2 * (hdist 0 w₀ + M) + 2 * ε
    have hR₁ : hdist w₀ w ≤ hdist 0 w₀ + M := hR₀ w hw
    have hR₂ : hdist w w₀ ≤ hdist 0 w₀ + M := by
      rw [hvd.symm w w₀]; exact hR₀ w hw
    have htri := hvd.triangle w₀ w ((h : PO n 1) • w₀)
    have htri2 := hvd.triangle w ((h : PO n 1) • w) ((h : PO n 1) • w₀)
    have hiso : hdist ((h : PO n 1) • w) ((h : PO n 1) • w₀) = hdist w w₀ := hvd.isom_smul _ _ _
    linarith
  have hHr : (Set.range hf).Finite := by
    refine hHfin.subset ?_
    rintro h ⟨y, hy⟩
    rw [← hy]
    exact hHmem y
  have hcuspfin : (Set.range cusp).Finite := by
    haveI : Fintype (Set.range hf) := hHr.fintype
    let g : Set.range hf → Y := fun z => Classical.choose z.2
    have hg : ∀ z : Set.range hf, hf (g z) = z.1 := fun z => Classical.choose_spec z.2
    have hsub : Set.range cusp ⊆ (fun z : Set.range hf => cusp (g z)) '' Set.univ := by
      rintro _ ⟨y, rfl⟩
      exact ⟨⟨hf y, ⟨y, rfl⟩⟩, Set.mem_univ _, hkey (g ⟨hf y, ⟨y, rfl⟩⟩) y (hg ⟨hf y, ⟨y, rfl⟩⟩)⟩
    exact (Set.finite_univ.image (fun z : Set.range hf => cusp (g z))).subset hsub
  haveI : Fintype (Set.range cusp) := hcuspfin.fintype
  let θ : Set.range cusp → Γ := fun z => γf (Classical.choose (Set.mem_range.mp z.2))
  have hθ : ∀ z : Set.range cusp, Submission.Mostow.bd (((θ z : Γ)) : PO n 1) ξ = z.1 :=
    fun z => Classical.choose_spec (Set.mem_range.mp z.2)
  refine ⟨K₀ ∪ ⋃ z : Set.range cusp,
      ((fun u : Submission.Mostow.E n => (((θ z : Γ)) : PO n 1)⁻¹ • u) '' K₀),
    hK₀c.union (isCompact_iUnion (fun z => ?_)), ?_⟩
  · exact hK₀c.image (hpb.continuous_smul.comp (continuous_const.prodMk continuous_id))
  · intro y hy
    refine ⟨((θ ⟨cusp ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩⟩)⁻¹ * γf ⟨y, hy⟩ : Γ), ?_, ?_⟩
    · have hz1 : Submission.Mostow.bd (((θ ⟨cusp ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩⟩ : Γ)) : PO n 1) ξ
          = Submission.Mostow.bd ((γf ⟨y, hy⟩ : Γ) : PO n 1) ξ :=
        hθ ⟨cusp ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩⟩
      have hcoe : ((((θ ⟨cusp ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩⟩)⁻¹ * γf ⟨y, hy⟩ : Γ)) : PO n 1)
          = (((θ ⟨cusp ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩⟩ : Γ)) : PO n 1)⁻¹
            * ((γf ⟨y, hy⟩ : Γ) : PO n 1) := rfl
      rw [hcoe, hpb.bd_mul (((θ ⟨cusp ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩⟩ : Γ)) : PO n 1)⁻¹
          (((γf ⟨y, hy⟩ : Γ)) : PO n 1) ξ hξS, ← hz1]
      exact bd_inv_bd hA hξS
    · show ((((θ ⟨cusp ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩⟩)⁻¹ * γf ⟨y, hy⟩ : Γ)) : PO n 1)
        • Work.Mostow.frontierPt Γ ξ ε y ∈ _
      rw [show ((((θ ⟨cusp ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩⟩)⁻¹ * γf ⟨y, hy⟩ : Γ)) : PO n 1)
          = (((θ ⟨cusp ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩⟩ : Γ)) : PO n 1)⁻¹
            * ((γf ⟨y, hy⟩ : Γ) : PO n 1) from rfl, hpb.mul_smul]
      refine Set.mem_union_right _ (Set.mem_iUnion.mpr ?_)
      refine ⟨⟨cusp ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩⟩, ?_⟩
      refine ⟨(γf ⟨y, hy⟩ : PO n 1) • Work.Mostow.frontierPt Γ ξ ε y, hγf ⟨y, hy⟩, rfl⟩

end
end Work.Mostow
