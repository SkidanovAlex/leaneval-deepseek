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
import Submission.Work.Mostow.cuspHoroballEmbedding
import Submission.Work.Mostow.cuspCocompactAllLevels
import Submission.Work.Mostow.cuspCocompactAtLevel

/-!
# A parabolic flat translation in the cusp stabiliser of a lattice

If `Γ ≤ PO(n,1)` is a lattice, `ξ ∈ parFixed Γ` and every element of `Γ` fixing `ξ` preserves
the horosphere levels (`hvan`), then `Γ` contains a *parabolic* element `δ` fixing `ξ` which acts
on the horospheres of `ξ` as a **flat translation** `y ↦ y + v` with `v ≠ 0`, `v ⊥ ξ`.

The proof applies Bieberbach's theorem to the flat action of the cusp stabiliser `Γ_ξ`:

* the Shimizu (Margulis) embedding of the horoball at `ξ` is supplied by
  `Work.Mostow.cuspHoroballEmbedding`;
* `Work.Mostow.cuspCocompactAtLevel` and `Work.Mostow.cuspCocompactAllLevels` turn that embedding
  into cocompactness of the cusp stabiliser `Γ_ξ = cuspStab Γ ξ` on the level-one horosphere;
* the level `1` horosphere of `ξ` is identified with the Euclidean space `ξ^⊥ = xiPerp ξ` via the
  flat coordinate `yc ξ` (`cuspZ2Defs`), and the action of `Γ_ξ` becomes a Euclidean isometry
  action `cuspFlatHom`, properly discontinuous by discreteness of `Γ`;
* Bieberbach's first theorem (`bieberbachInnerProduct`) produces a finite-index subgroup `T` acting
  by translations whose vectors span `ξ^⊥`; `ξ^⊥ ≠ 0` forces some `t ∈ T`, `t ≠ 1`, and the flat
  action being faithful (`cuspFlatInjective`) gives a *nonzero* translation vector `v`;
* the translation property at level `1` upgrades to *all* levels (`cpt_yc_smul_level_indep`,
  `cpt_yc_translation`), and a flat translation with nonzero vector is parabolic
  (`cpt_flatTrans_parabolic`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ## Elementary flat-translation calculus -/

/-- Elements of the cusp stabiliser preserve all horosphere levels at `ξ` (via `hvan`). -/
lemma cpt_lev_of_bd (hA : POActionProp n) (hI : HypIsometryProp n) (Γ : Subgroup (PO n 1))
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
lemma cpt_yc_smul_level_indep (hI : HypIsometryProp n)
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
lemma cpt_yc_translation (hI : HypIsometryProp n) (ξ : E n) (hξ : ξ ∈ Sph n)
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
    cpt_yc_smul_level_indep hI ξ hξ γ hγ hlev (yc ξ u) hu' (lev ξ u) 1
      (lev_pos ξ hξ u) one_pos
  have hflat : flatAct ξ γ (yc ξ u) = yc ξ u + w := hw (yc ξ u) hu'
  have hfinal : yc ξ (γ • u) = yc ξ u + w := by
    calc yc ξ (γ • u) = yc ξ (γ • hptOf ξ (yc ξ u) (lev ξ u)) := by rw [hpt]
      _ = yc ξ (γ • hptOf ξ (yc ξ u) 1) := hindep
      _ = yc ξ (γ • horoPt ξ (yc ξ u)) := by rw [horoPt_eq_hptOf]
      _ = yc ξ u + w := hflat
  exact ⟨hfinal, hlev u⟩

/-- The hyperbolic displacement of a flat translation by `v ≠ 0`, at the point `u`. -/
lemma cpt_flatTrans_disp (hI : HypIsometryProp n) (ξ : E n) (hξ : ξ ∈ Sph n)
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
lemma cpt_flatTrans_parabolic (hA : POActionProp n) (hI : HypIsometryProp n) (ξ : E n)
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
    rw [cpt_flatTrans_disp hI ξ hξ δ v hlev hyc, hlevH]
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
theorem cuspParabolicFlatTrans_of_cocompact (n : ℕ) (hn : 2 ≤ n)
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
    exact cpt_yc_smul_level_indep hI ξ hξS ((t : G) : PO n 1) hγt hlevt y hy D 1 hD one_pos
  have hw : ∀ y : E n, inner ℝ y ξ = 0 → flatAct ξ ((t : G) : PO n 1) y = y + (v t : E n) := by
    intro y hy
    rw [show flatAct ξ ((t : G) : PO n 1) y
      = yc ξ (((t : G) : PO n 1) • horoPt ξ y) from rfl, horoPt_eq_hptOf]
    exact hlevelD y hy 1 one_pos
  have hmain := cpt_yc_translation hI ξ hξS ((t : G) : PO n 1) hγt hlevt (v t : E n) hw
  refine ⟨⟨(t : PO n 1), htΓ⟩, ?_, ?_, ?_, (v t : E n), hvt, xiPerp_inner' (v t), fun u => (hmain u).1⟩
  · exact cpt_flatTrans_parabolic hA hI ξ hξS ((t : G) : PO n 1) (v t : E n) hvt
      (fun u => (hmain u).2) (fun u => (hmain u).1)
  · exact hγt
  · exact hvan ⟨(t : PO n 1), htΓ⟩ ξ hξ hγt

/-! ## The main theorem

All the geometry is now available: `cuspCocompactAtLevel` (with the Shimizu embedding supplied by
`cuspHoroballEmbedding`) gives cocompactness of `Γ_ξ` at one horosphere level, and
`cuspCocompactAllLevels` transports it to the level-one horosphere.  Bieberbach's theorem then
produces the flat translation, as in `cuspParabolicFlatTrans_of_cocompact`. -/

theorem cuspParabolicFlatTrans (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (hBb : ∀ m, Submission.Mostow.BieberbachProp m)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ) :
    ∃ δ : Γ, Submission.Mostow.IsParabolic (δ : LeanEval.Geometry.MostowRigidity.PO n 1) ∧
      Submission.Mostow.bd (δ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
      Work.Mostow.bCocy (δ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0 ∧
      ∃ v : Submission.Mostow.E n, v ≠ 0 ∧ inner ℝ v ξ = 0 ∧
        ∀ u : Submission.Mostow.E n,
          Work.Mostow.yc ξ ((δ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) =
            Work.Mostow.yc ξ u + v := by
  have hξS : ξ ∈ Sph n := hξ.1
  have hstab : ∀ γ : Γ, bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0 :=
    fun γ hγ => hvan γ ξ hξ hγ
  -- the Shimizu embedding of the horoball at some level `τ`
  obtain ⟨τ, hemb⟩ := cuspHoroballEmbedding n hn hA hI hBb Γ hΓ hvan ξ hξ
  -- cocompactness of `Γ_ξ` at that level
  have hτ : ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n, busemann ξ u = τ →
      ∃ γ : Γ, bd (γ : PO n 1) ξ = ξ ∧ (γ : PO n 1) • u ∈ K :=
    cuspCocompactAtLevel n hn hA hI hBb Γ hΓ ξ hξ hstab τ hemb
  -- and hence, by horocyclic-flow equivariance, at every level
  obtain ⟨K, hKc, hK⟩ := (cuspCocompactAllLevels n hA hI Γ ξ hξS hstab τ hτ) 0
  refine cuspParabolicFlatTrans_of_cocompact n hn hA hI hBb Γ hΓ hvan ξ hξ ⟨K, hKc, ?_⟩
  intro u hu
  have hb : busemann ξ u = 0 := by
    have h : Real.exp (busemann ξ u) = 1 := by rw [← lev_eq_exp hξS u, hu]
    rw [← Real.log_exp (busemann ξ u), h, Real.log_one]
  obtain ⟨γ, hγ, hγK⟩ := hK u hb
  exact ⟨γ, hγ, hγK⟩

end

end Work.Mostow
