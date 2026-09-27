import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.hptOf_yc
import Submission.Work.Mostow.flatActBasic
import Submission.Work.Mostow.cuspZ2Defs
import Submission.Work.Mostow.cuspZ2
import Submission.Work.Mostow.finite_translates_inter_compact
import Submission.Work.Mostow.geomFiniteCuspCocompact
import Submission.Work.Mostow.bieberbach

/-!
# A parabolic flat translation in the cusp stabiliser (self-contained copy)

This file re-homes the flat-translation argument (`Work.Mostow.csha_flatTransOfCocompact`)
from `Submission/Work/Mostow/cuspParabolicFlatTrans.lean`, so that the main file
`Submission/Work/Mostow/cuspShimizuHoroball.lean` does not depend on the modules that are
currently being restructured elsewhere in the workspace.

Given the cocompactness of the cusp stabiliser on a horosphere at `ξ`, the proof produces a
parabolic `δ ∈ Γ` fixing `ξ` which acts on the horospheres at `ξ` by a nontrivial flat
translation `y ↦ y + v` and preserves the levels.
-/

set_option maxHeartbeats 4000000

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}

/-! ## Elementary flat-translation calculus -/

/-- Elements of the cusp stabiliser preserve all horosphere levels at `ξ` (via `hvan`). -/
lemma csha_lev_of_bd (hA : POActionProp n) (hI : HypIsometryProp n) (Γ : Subgroup (PO n 1))
    (ξ : E n) (hξ : ξ ∈ Sph n)
    (hvan : ∀ (γ : Γ) η, η ∈ parFixed Γ → bd (γ : PO n 1) η = η → bCocy (γ : PO n 1) η = 0)
    (hξp : ξ ∈ parFixed Γ) :
    ∀ γ : Γ, bd (γ : PO n 1) ξ = ξ → ∀ u : E n,
      lev ξ ((γ : PO n 1) • u) = lev ξ u := by
  intro γ hγ u
  have h := lev_smul_self (HypIsoData.ofProp hI) (POBasic.ofProp hA) ξ hξ γ u hγ
  have h0 : lev ξ ((γ : PO n 1) • (0 : E n)) = 1 := by
    rw [lev_eq_exp hξ,
      show busemann ξ ((γ : PO n 1) • (0 : E n)) = bCocy (γ : PO n 1) ξ from by rw [bCocy, hγ],
      hvan γ ξ hξp hγ, Real.exp_zero]
  rw [h, h0, mul_one]

/-- The flat coordinate of `g • hptOf ξ y E` does not depend on the level `E`, when `g` fixes `ξ`
and preserves the levels. -/
lemma csha_yc_smul_level_indep (hI : HypIsometryProp n)
    (ξ : E n) (hξ : ξ ∈ Sph n) (g : PO n 1) (hg : bd g ξ = ξ)
    (hlev : ∀ u : E n, lev ξ (g • u) = lev ξ u) (y : E n) (hy : inner ℝ y ξ = 0)
    (E₁ E₂ : ℝ) (h₁ : 0 < E₁) (h₂ : 0 < E₂) :
    yc ξ (g • hptOf ξ y E₁) = yc ξ (g • hptOf ξ y E₂) := by
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  have hlev₁ : lev ξ (g • hptOf ξ y E₁) = E₁ := by
    rw [hlev, (hptOf_level ξ hξ E₁ h₁ y hy).1]
  have hlev₂ : lev ξ (g • hptOf ξ y E₂) = E₂ := by
    rw [hlev, (hptOf_level ξ hξ E₂ h₂ y hy).1]
  have hdist_g : hdist (g • hptOf ξ y E₁) (g • hptOf ξ y E₂)
      = hdist (hptOf ξ y E₁) (hptOf ξ y E₂) := hI'.isom_smul g _ _
  have hform₁ := levYcFormula hξ (g • hptOf ξ y E₁) (g • hptOf ξ y E₂)
  have hform₂ := levYcFormula hξ (hptOf ξ y E₁) (hptOf ξ y E₂)
  rw [hlev₁, hlev₂] at hform₁
  rw [(hptOf_level ξ hξ E₁ h₁ y hy).1, (hptOf_level ξ hξ E₂ h₂ y hy).1,
    (hptOf_level ξ hξ E₁ h₁ y hy).2, (hptOf_level ξ hξ E₂ h₂ y hy).2] at hform₂
  rw [hdist_g, hform₂] at hform₁
  simp only [sub_self, norm_zero, mul_zero, add_zero] at hform₁
  have hE : (0:ℝ) < E₁ * E₂ / 2 := by positivity
  have hkey : ‖yc ξ (g • hptOf ξ y E₁) - yc ξ (g • hptOf ξ y E₂)‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖yc ξ (g • hptOf ξ y E₁) - yc ξ (g • hptOf ξ y E₂)‖ ^ 2 :=
      pow_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)) 2
    nlinarith [hform₁]
  exact sub_eq_zero.mp (norm_eq_zero.mp hkey)

/-- A level-preserving isometry of the horospheres at `ξ` whose action at level one is the
translation by `w` translates the flat coordinate of *every* point by `w`. -/
lemma csha_yc_translation (hI : HypIsometryProp n) (ξ : E n) (hξ : ξ ∈ Sph n)
    (γ : PO n 1) (hγ : bd γ ξ = ξ) (hlev : ∀ u : E n, lev ξ (γ • u) = lev ξ u)
    (w : E n) (hw : ∀ y : E n, inner ℝ y ξ = 0 → flatAct ξ γ y = y + w) :
    ∀ u : E n, yc ξ (γ • u) = yc ξ u + w ∧ lev ξ (γ • u) = lev ξ u := by
  intro u
  have hu' : inner ℝ (yc ξ u) ξ = 0 := inner_yc hξ u
  have hpt : hptOf ξ (yc ξ u) (lev ξ u) = u :=
    hptOf_yc ξ hξ (lev ξ u) (lev_pos ξ hξ u) u rfl
  have hyc : yc ξ (hptOf ξ (yc ξ u) (lev ξ u)) = yc ξ u :=
    (hptOf_level ξ hξ (lev ξ u) (lev_pos ξ hξ u) (yc ξ u) hu').2
  have hindep : yc ξ (γ • hptOf ξ (yc ξ u) (lev ξ u))
      = yc ξ (γ • hptOf ξ (yc ξ u) 1) :=
    csha_yc_smul_level_indep hI ξ hξ γ hγ hlev (yc ξ u) hu' (lev ξ u) 1
      (lev_pos ξ hξ u) one_pos
  have hflat : flatAct ξ γ (yc ξ u) = yc ξ u + w := hw (yc ξ u) hu'
  have hfinal : yc ξ (γ • u) = yc ξ u + w := by
    calc yc ξ (γ • u) = yc ξ (γ • hptOf ξ (yc ξ u) (lev ξ u)) := by rw [hpt]
      _ = yc ξ (γ • hptOf ξ (yc ξ u) 1) := hindep
      _ = yc ξ (γ • horoPt ξ (yc ξ u)) := by rw [horoPt_eq_hptOf]
      _ = yc ξ u + w := hflat
  exact ⟨hfinal, hlev u⟩

/-- The hyperbolic displacement of a flat translation by `v ≠ 0`, at the point `u`. -/
lemma csha_flatTrans_disp (hI : HypIsometryProp n) (ξ : E n) (hξ : ξ ∈ Sph n)
    (δ : PO n 1) (v : E n)
    (hlev : ∀ u : E n, lev ξ (δ • u) = lev ξ u)
    (hyc : ∀ u : E n, yc ξ (δ • u) = yc ξ u + v) :
    ∀ u : E n, hdist u (δ • u) = Real.arcosh (1 + lev ξ u ^ 2 * ‖v‖ ^ 2 / 2) := by
  have hvd := HypIsoData.ofProp hI
  intro u
  have hL := lev_pos ξ hξ u
  have h := levYcFormula hξ u (δ • u)
  rw [hlev u, hyc u] at h
  have hycv : yc ξ u - (yc ξ u + v) = -v := by abel
  rw [hycv, norm_neg, div_self (ne_of_gt hL), Real.log_one, Real.cosh_zero] at h
  have h3 : 1 + lev ξ u ^ 2 * ‖v‖ ^ 2 / 2 = Real.cosh (hdist u (δ • u)) := by
    rw [h]; ring
  rw [h3]
  exact (Real.arcosh_cosh (hvd.nonneg u (δ • u))).symm

/-- A flat translation by `v ≠ 0` is parabolic. -/
lemma csha_flatTrans_parabolic (hA : POActionProp n) (hI : HypIsometryProp n) (ξ : E n)
    (hξ : ξ ∈ Sph n) (δ : PO n 1) (v : E n) (hv : v ≠ 0)
    (hlev : ∀ u : E n, lev ξ (δ • u) = lev ξ u)
    (hyc : ∀ u : E n, yc ξ (δ • u) = yc ξ u + v) :
    IsParabolic δ := by
  constructor
  · intro u hu
    have h := hyc u
    rw [hu] at h
    have h2 : v = 0 := by
      have h3 := congrArg (fun z => z - yc ξ u) h
      rw [add_sub_cancel_left, sub_self] at h3
      exact h3.symm
    exact hv h2
  · intro ε hε
    have hcosh : 1 < Real.cosh ε := Real.one_lt_cosh.mpr (ne_of_gt hε)
    have hv2 : 0 < ‖v‖ ^ 2 := by
      have : 0 < ‖v‖ := norm_pos_iff.mpr hv
      positivity
    set D : ℝ := Real.sqrt (2 * (Real.cosh ε - 1) / ‖v‖ ^ 2) * (1/2) with hDdef
    have hDpos : 0 < D :=
      mul_pos (Real.sqrt_pos.mpr (div_pos (by linarith) hv2))
        (by norm_num)
    have hD2 : D ^ 2 = (2 * (Real.cosh ε - 1) / ‖v‖ ^ 2) * (1/4) := by
      rw [hDdef, mul_pow,
        Real.sq_sqrt (le_of_lt (div_pos (by linarith) hv2))]
      ring
    refine ⟨hptOf ξ 0 D, ?_⟩
    have hlevH : lev ξ (hptOf ξ 0 D) = D := (hptOf_level ξ hξ D hDpos 0 (by simp)).1
    rw [csha_flatTrans_disp hI ξ hξ δ v hlev hyc, hlevH]
    have hkey : 1 + D ^ 2 * ‖v‖ ^ 2 / 2 < Real.cosh ε := by
      have hE : D ^ 2 * ‖v‖ ^ 2 / 2 = (Real.cosh ε - 1) / 4 := by
        rw [hD2]; field_simp
      rw [hE]; linarith
    rw [show ε = Real.arcosh (Real.cosh ε) from (Real.arcosh_cosh (le_of_lt hε)).symm,
      Real.arcosh_lt_arcosh (by positivity) (Real.cosh_pos ε)]
    exact hkey

/-! ## The assembly -/

/-- **A parabolic flat translation exists, assuming the cusp stabiliser is cocompact on its
horosphere.** -/
theorem csha_flatTransOfCocompact (n : ℕ) (hn : 2 ≤ n)
    (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    (hBb : ∀ m, Submission.Mostow.BieberbachProp m)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ)
    (hcoc : ∃ K : Set (Submission.Mostow.E n), IsCompact K ∧ ∀ u : Submission.Mostow.E n,
      Work.Mostow.lev ξ u = 1 → ∃ γ : Γ,
        Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
        (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u ∈ K) :
    ∃ δ : Γ, Submission.Mostow.IsParabolic (δ : LeanEval.Geometry.MostowRigidity.PO n 1) ∧
      Submission.Mostow.bd (δ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
      Work.Mostow.bCocy (δ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0 ∧
      ∃ v : Submission.Mostow.E n, v ≠ 0 ∧ inner ℝ v ξ = 0 ∧
        ∀ u : Submission.Mostow.E n,
          Work.Mostow.yc ξ ((δ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) =
            Work.Mostow.yc ξ u + v := by
  have hAb : POBasic n := POBasic.ofProp hA
  have hId : HypIsoData n := HypIsoData.ofProp hI
  have hξS : ξ ∈ Sph n := hξ.1
  have hdisc : IsDiscrete (SetLike.coe Γ) := hΓ.1
  -- the cusp stabiliser of `ξ` inside `Γ`, as a subgroup of `PO n 1`
  let G : Subgroup (PO n 1) :=
    { carrier := {γ | γ ∈ Γ ∧ bd γ ξ = ξ}
      mul_mem' := by
        intro a b ha hb
        refine ⟨Γ.mul_mem ha.1 hb.1, ?_⟩
        rw [hAb.bd_mul a b ξ hξS, hb.2, ha.2]
      one_mem' := ⟨Γ.one_mem, hAb.bd_one ξ hξS⟩
      inv_mem' := by
        intro a ha
        refine ⟨Γ.inv_mem ha.1, ?_⟩
        have h1 : bd (a⁻¹ * a) ξ = ξ := by rw [inv_mul_cancel, hAb.bd_one ξ hξS]
        rw [hAb.bd_mul a⁻¹ a ξ hξS, ha.2] at h1
        exact h1 }
  have hGmem : ∀ γ : PO n 1, γ ∈ G ↔ γ ∈ Γ ∧ bd γ ξ = ξ := fun γ => Iff.rfl
  have hGle : ∀ γ ∈ G, γ ∈ Γ := fun γ hγ => (hGmem γ).mp hγ |>.1
  have hGbd : ∀ γ ∈ G, bd γ ξ = ξ := fun γ hγ => (hGmem γ).mp hγ |>.2
  -- every element of the cusp stabiliser preserves the horosphere levels
  have hlevG : ∀ γ ∈ G, ∀ u : E n, lev ξ (γ • u) = lev ξ u := by
    intro γ hγ u
    have hfix : bd γ ξ = ξ := (hGmem γ).mp hγ |>.2
    have hc : bCocy γ ξ = 0 := hvan ⟨γ, (hGmem γ).mp hγ |>.1⟩ ξ hξ hfix
    have h := lev_smul_self hId hAb ξ hξS γ u hfix
    have h0 : lev ξ (γ • (0 : E n)) = 1 := by
      rw [lev_eq_exp hξS,
        show busemann ξ (γ • (0 : E n)) = bCocy γ ξ from by rw [bCocy, hfix], hc, Real.exp_zero]
    rw [h, h0, mul_one]
  -- the flat action of `G = Γ_ξ` on `ξ^⊥`
  set ρ : G →* (xiPerp ξ ≃ᵢ xiPerp ξ) :=
    cuspFlatHom hAb hId hξS 1 one_pos G hlevG with hρ
  have hρapp : ∀ (g : G) (y : xiPerp ξ), ρ g y = flatFun hξS 1 (g : PO n 1) y := fun g y => rfl
  -- properness of the flat action, from discreteness
  have hprop : ∀ u₀ : E n, lev ξ u₀ = 1 → ∀ K : Set (E n), IsCompact K →
      {g : G | (g : PO n 1) • u₀ ∈ K}.Finite := by
    intro u₀ _ K hK
    have hfin : {γ : Γ |
        (((fun u : E n => (γ : PO n 1) • u) '' ({u₀} : Set (E n))) ∩ K).Nonempty}.Finite :=
      finite_translates_inter_compact n hA hI hdisc isCompact_singleton hK
    refine (hfin.preimage (f := fun g : G => (⟨(g : PO n 1), hGle g g.2⟩ : Γ))
      (fun a _ b _ hab => Subtype.ext (congrArg (fun γ : Γ => (γ : PO n 1)) hab))).subset ?_
    rintro g hg
    exact ⟨(g : PO n 1) • u₀, ⟨u₀, by simp, rfl⟩, hg⟩
  have hpd : ∀ K : Set (xiPerp ξ), IsCompact K →
      {g : G | ((ρ g) '' K ∩ K).Nonempty}.Finite := by
    intro K hK
    refine (cuspFlatProper n hI ξ hξS 1 one_pos G hlevG hprop K hK).subset ?_
    rintro g ⟨z, ⟨y, hyK, hzy⟩, hzK⟩
    rw [hρapp g y] at hzy
    exact ⟨z, ⟨y, hyK, hzy⟩, hzK⟩
  -- cocompactness of the flat action, from the hypothesis `hcoc`
  have hcoc' : ∃ K : Set (xiPerp ξ), IsCompact K ∧ ∀ y : xiPerp ξ,
      ∃ g : G, ρ g y ∈ K := by
    obtain ⟨K, hKc, hK⟩ := hcoc
    have hcocG : ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n, lev ξ u = 1 →
        ∃ g : G, (g : PO n 1) • u ∈ K := by
      refine ⟨K, hKc, fun u hu => ?_⟩
      obtain ⟨γ, hγ, hγK⟩ := hK u hu
      exact ⟨⟨(γ : PO n 1), (hGmem _).mpr ⟨γ.2, hγ⟩⟩, hγK⟩
    obtain ⟨K', hK'c, hK'⟩ := cuspFlatCocompact n hI ξ hξS 1 one_pos G hlevG hcocG
    exact ⟨K', hK'c, fun x => by obtain ⟨g, hg⟩ := hK' x; exact ⟨g, by rwa [hρapp g x]⟩⟩
  -- Bieberbach's first theorem
  obtain ⟨T, v, hTfin, htrans, hspan⟩ :=
    bieberbachInnerProduct (hBb (Module.finrank ℝ (xiPerp ξ))) ρ hpd hcoc'
  haveI : T.FiniteIndex := hTfin
  -- `ξ^⊥` is nontrivial
  have hξ0 : ξ ≠ 0 := by
    intro h
    have h1 : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξS
    rw [h, norm_zero] at h1
    exact one_ne_zero h1.symm
  have htopne : (⊤ : Submodule ℝ (xiPerp ξ)) ≠ ⊥ := by
    intro h
    have h1 : Module.finrank ℝ (xiPerp ξ) = 0 := by
      have h2 := congrArg (fun (s : Submodule ℝ (xiPerp ξ)) => Module.finrank ℝ ↥s) h
      simpa using h2
    have h3 : Module.finrank ℝ (xiPerp ξ) = n - 1 := by
      have h4 : Module.finrank ℝ ↥(Submodule.span ℝ ({ξ} : Set (E n))) = 1 :=
        finrank_span_singleton hξ0
      have h5 := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ ({ξ} : Set (E n)))
      have h6 : Module.finrank ℝ (E n) = n := by rw [finrank_euclideanSpace]; simp
      rw [xiPerp]
      omega
    omega
  -- `T` is nontrivial, giving `t ∈ T`, `t ≠ 1`
  obtain ⟨t, htT, ht1⟩ : ∃ t ∈ T, t ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hv1 : v 1 = 0 := by
      have h := htrans 1 T.one_mem (0 : xiPerp ξ)
      rw [map_one] at h
      simpa using h.symm
    have hsub : (v '' (T : Set G)) ⊆ ({0} : Set (xiPerp ξ)) := by
      rintro z ⟨g, hg, rfl⟩
      rw [hcon g hg]
      simpa using hv1
    have hle : (⊤ : Submodule ℝ (xiPerp ξ)) ≤ ⊥ := by
      rw [← hspan]
      refine Submodule.span_le.mpr ?_
      rintro z hz
      rw [hsub hz]
      exact Submodule.zero_mem _
    exact htopne (le_bot_iff.mp hle)
  have hρt : ∀ x : xiPerp ξ, ρ t x = x + v t := htrans t htT
  have hinj : Function.Injective ρ := by
    intro a b hab
    have h1 : ρ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ∀ y : xiPerp ξ, flatFun hξS 1 ((a * b⁻¹ : G) : PO n 1) y = y := by
      intro y
      have h := congrArg (fun (e : xiPerp ξ ≃ᵢ xiPerp ξ) => e y) h1
      rw [hρapp (a * b⁻¹) y] at h
      simpa using h
    have h3 : a * b⁻¹ = 1 :=
      cuspFlatInjective n hA hI ξ hξS 1 one_pos G hGbd hlevG (a * b⁻¹) h2
    calc a = a * b⁻¹ * b := by group
      _ = 1 * b := by rw [h3]
      _ = b := one_mul b
  have hvt₀ : v t ≠ 0 := by
    intro h0
    have h1 : ρ t = 1 := by
      apply IsometryEquiv.ext
      intro x
      rw [hρt x, h0, add_zero]
      rfl
    exact ht1 (hinj (by rw [h1, map_one]))
  have hvt : (v t : E n) ≠ 0 := fun h => hvt₀ (Subtype.coe_injective h)
  -- the flat action of `t` is the translation by `v t`
  have htG : (t : PO n 1) ∈ G := t.2
  have htΓ : (t : PO n 1) ∈ Γ := (hGmem _).mp htG |>.1
  have hγt : bd ((t : G) : PO n 1) ξ = ξ := (hGmem _).mp htG |>.2
  have hlevt : ∀ u : E n, lev ξ (((t : G) : PO n 1) • u) = lev ξ u := hlevG (t : G) t.2
  have hlevel1 : ∀ y : E n, inner ℝ y ξ = 0 →
      yc ξ (((t : G) : PO n 1) • hptOf ξ y 1) = y + (v t : E n) := by
    intro y hy
    have h := congrArg (fun z : xiPerp ξ => (z : E n))
      (hρt ⟨y, mem_xiPerp_iff.mpr (by rw [real_inner_comm]; exact hy)⟩)
    rw [hρapp] at h
    simp only [flatFun_coe] at h
    rw [h]; rfl
  have hlevelD : ∀ y : E n, inner ℝ y ξ = 0 → ∀ D : ℝ, 0 < D →
      yc ξ (((t : G) : PO n 1) • hptOf ξ y D) = y + (v t : E n) := by
    intro y hy D hD
    rw [← hlevel1 y hy]
    exact csha_yc_smul_level_indep hI ξ hξS ((t : G) : PO n 1) hγt hlevt y hy D 1 hD one_pos
  have hw : ∀ y : E n, inner ℝ y ξ = 0 → flatAct ξ ((t : G) : PO n 1) y = y + (v t : E n) := by
    intro y hy
    rw [show flatAct ξ ((t : G) : PO n 1) y
      = yc ξ (((t : G) : PO n 1) • horoPt ξ y) from rfl, horoPt_eq_hptOf]
    exact hlevelD y hy 1 one_pos
  have hmain := csha_yc_translation hI ξ hξS ((t : G) : PO n 1) hγt hlevt (v t : E n) hw
  refine ⟨⟨(t : PO n 1), htΓ⟩, ?_, ?_, ?_, (v t : E n), hvt, xiPerp_inner' (v t), fun u => (hmain u).1⟩
  · exact csha_flatTrans_parabolic hA hI ξ hξS ((t : G) : PO n 1) (v t : E n) hvt
      (fun u => (hmain u).2) (fun u => (hmain u).1)
  · exact hγt
  · exact hvan ⟨(t : PO n 1), htΓ⟩ ξ hξ hγt


/-! ## The remaining obligation, and the state of the workspace

The single input of `Work.Mostow.cuspShimizuHoroball` that is not available in a buildable,
`sorry`-free form is the cocompactness of the cusp stabiliser on the level-one horosphere.  It is
stated elsewhere in the workspace as `Work.Mostow.cuspStabHorosphereCocompact` (a full proof was
written at `Submission/Work/Mostow/cuspStabHorosphereCocompact.lean`, but its import closure is
currently not buildable) and as `Work.Mostow.cuspCocompactLevOne`.  The statement below is that
statement, so that the reduction performed by `Work.Mostow.cuspShimizuHoroball` is machine-checked
independently of it.

The obstacles to closing it at the time of writing, in the order in which they bite:

* `Submission/Work/Mostow/cuspFlatTranslation.lean:419` is a `(deterministic) timeout at whnf`
  with the default `maxHeartbeats` (200000).  This file is in the import closure of
  `cuspShimizuPos` and hence of `cuspHoroballEmbedding`, `cuspCocompactAtLevel` and
  `cuspStabHorosphereCocompact`; raising the heartbeat limit there (or in a re-homed copy of its
  contents, as done for the flat-translation argument in this file) unblocks all of them.
* `Work.Mostow.cuspMargulisCommon` (used by `Work.Mostow.cuspPreciseInvariant`, the input of
  `cuspHoroballEmbedding`) currently rests on `sorryAx` (through
  `Submission/Work/Mostow/Margulis/nearId_pair_commuting.lean`), so the Shimizu route
  "cocompactness from the horoball embedding" is not yet axiom-clean.
* The routes that avoid the embedding (`Work.Mostow.cuspCocompactAllLevels` with a one-level
  cocompactness) are circular in substance: the flat translation and the cocompactness each
  need the other, cf. the design note `REFS/lead-design/NOTES_LEAD_geomFinite.md`.

Replacing this stub by `Work.Mostow.cuspStabHorosphereCocompact` (or by any honest proof of the
same statement, in particular one that avoids `cuspMargulisCommon`) finishes the proof. -/

theorem horosphereStabCocompactAux (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ) :
    ∃ K : Set (Submission.Mostow.E n), IsCompact K ∧ ∀ u : Submission.Mostow.E n,
      Work.Mostow.lev ξ u = 1 → ∃ γ : Γ,
        Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
        (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u ∈ K := by
  -- This is the level `t = 0` case of `Work.Mostow.geomFiniteCuspCocompact` (proved in
  -- `Submission/Work/Mostow/geomFiniteCuspCocompact.lean`), i.e. of `CuspCocompact Γ ξ`.
  obtain ⟨K, hKc, hK⟩ :=
    Work.Mostow.geomFiniteCuspCocompact n hn hA hI Work.Mostow.bieberbach Γ hΓ ξ hξ hvan 0
  refine ⟨K, hKc, fun u hu => ?_⟩
  refine hK u ?_
  have hlog : Submission.Mostow.busemann ξ u = Real.log (Work.Mostow.lev ξ u) := rfl
  rw [hlog, hu, Real.log_one]

end Work.Mostow
