import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.cuspZ2Defs
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.hptOf_yc
import Submission.Work.Mostow.stabFlatAction
import Submission.Work.Mostow.flatLin_id_of_parabolic_two
import Submission.Work.Mostow.cuspCocompactAtLevel
import Submission.Work.Mostow.cuspCocompactAllLevels
import Submission.Work.Mostow.cuspZ2
import Submission.Work.Mostow.cuspShimizuHoroball
import Submission.Work.Mostow.cuspHoro.packingCount
import Submission.Work.Mostow.cuspParabolicFlatTrans
import Submission.Work.Mostow.cuspShimizuPreciseInvariant

/-!
# A parabolic flat translation in the cusp stabiliser

For a lattice `Γ ≤ PO(n,1)` (`n ≥ 2`), a parabolic fixed point `ξ ∈ parFixed Γ` of `Γ` and a
subgroup on which the Busemann cocycle at `ξ` vanishes (`hvan`), the stabiliser `Γ_ξ` contains a
*parabolic* element `δ` fixing `ξ` which acts on the horospheres of `ξ` as a flat translation
`y ↦ y + v` with `v ≠ 0` perpendicular to `ξ`.

This file proves the two ends of the argument:

* the case `n = 2` directly: on the one-dimensional space `ξ^⊥` the linear part of the flat action
  of any parabolic of `Γ_ξ` is `±1`, and `-1` would give a fixed point, hence the element is a pure
  flat translation (`flatLin_id_of_parabolic_two`);
* the assembly for `n ≥ 3`, which turns Shimizu's lemma for lattices
  (`∃ s, ∀ μ ∉ Γ_ξ, lev ξ u < s → s ≤ lev ξ (μ • u)`) into the flat translation, by
  Bieberbach's theorem applied to the flat action of `Γ_ξ` on `ξ^⊥`.

The remaining geometric input -- Shimizu's lemma for a lattice -- is the content of
`Work.Mostow.cuspShimizuPreciseInvariant`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

variable {n : ℕ}

/-! ## The case `n = 2` -/

/-- For `n = 2`, any parabolic element of `Γ` fixing `ξ` already provides the required flat
translation: its linear part is forced to be the identity on the one-dimensional space `ξ^⊥`. -/
theorem flatTranslation_two (hA : Submission.Mostow.POActionProp 2)
    (hI : Submission.Mostow.HypIsometryProp 2) (Γ : Subgroup (PO 2 1))
    (hvan : ∀ (γ : Γ) η, η ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : PO 2 1) η = η → Work.Mostow.bCocy (γ : PO 2 1) η = 0)
    (ξ : E 2) (hξ : ξ ∈ Work.Mostow.parFixed Γ) :
    ∃ δ : Γ, IsParabolic (δ : PO 2 1) ∧ bd (δ : PO 2 1) ξ = ξ ∧ bCocy (δ : PO 2 1) ξ = 0 ∧
      ∃ v : E 2, v ≠ 0 ∧ inner ℝ v ξ = 0 ∧
        ∀ u : E 2, yc ξ ((δ : PO 2 1) • u) = yc ξ u + v := by
  obtain ⟨γ, hpar, hfix⟩ := hξ.2
  have hξS : ξ ∈ Sph 2 := hξ.1
  have hpb : POBasic 2 := POBasic.ofProp hA
  have hvd : HypIsoData 2 := HypIsoData.ofProp hI
  have hbc : bCocy (γ : PO 2 1) ξ = 0 := hvan γ ξ hξ hfix
  have hβ : busemann ξ ((γ : PO 2 1) • (0 : E 2)) = 0 := by
    simpa only [bCocy, hfix] using hbc
  obtain ⟨A, v, hvperp, hAperp, hAnorm, hact⟩ :=
    stabFlatAction 2 hA hI ξ hξS (γ : PO 2 1) hfix hβ
  have hAid : ∀ y : E 2, inner ℝ y ξ = 0 → A y = y :=
    flatLin_id_of_parabolic_two hA hI ξ hξS (γ : PO 2 1) hpar hfix A v hvperp hAperp hAnorm hact
  -- `γ` preserves every horosphere of `ξ`
  have hlevγ : ∀ u : E 2, lev ξ ((γ : PO 2 1) • u) = lev ξ u := by
    intro u
    have hbus := hvd.busemann_cocycle (γ : PO 2 1) ξ u hξS
    rw [hfix, hβ, add_zero] at hbus
    rw [lev_eq_exp hξS u, lev_eq_exp hξS ((γ : PO 2 1) • u), hbus]
  -- its flat action is the translation by `v`
  have hyc : ∀ u : E 2, yc ξ ((γ : PO 2 1) • u) = yc ξ u + v := by
    intro u
    have hDpos : 0 < lev ξ u := lev_pos ξ hξS u
    have hkey := (hact (yc ξ u) (lev ξ u) (inner_yc hξS u) hDpos).2
    rw [hptOf_yc ξ hξS (lev ξ u) hDpos u rfl] at hkey
    rw [hkey, hAid (yc ξ u) (inner_yc hξS u)]
  refine ⟨γ, hpar, hfix, hbc, v, ?_, hvperp, hyc⟩
  -- a vanishing translation vector would make `γ` the identity, contradicting parabolicity
  intro hv0
  have hγ1 : (γ : PO 2 1) = 1 := by
    refine hpb.faithful (γ : PO 2 1) (fun w => ?_)
    have hDpos : 0 < lev ξ w := lev_pos ξ hξS w
    have h1 : hptOf ξ (yc ξ ((γ : PO 2 1) • w)) (lev ξ w) = (γ : PO 2 1) • w :=
      hptOf_yc ξ hξS (lev ξ w) hDpos ((γ : PO 2 1) • w) (hlevγ w)
    have h2 : hptOf ξ (yc ξ w) (lev ξ w) = w := hptOf_yc ξ hξS (lev ξ w) hDpos w rfl
    rw [hyc w, hv0, add_zero] at h1
    rw [← h1, h2]
  exact hpar.1 0 (by rw [hγ1, hpb.one_smul])

/-! ## The assembly for `n ≥ 3`

Given Shimizu's lemma for the cusp at `ξ` -- the precise invariance of a small horoball, in the
equivalent "level separation" form
`∃ s, 0 < s ∧ ∀ μ ∉ Γ_ξ, lev ξ u < s → s ≤ lev ξ (μ • u)` --
the packing arguments of `cuspCocompactAtLevel` and `cuspCocompactAllLevels` give that `Γ_ξ` acts
cocompactly on the horosphere of `ξ`; Bieberbach's theorem applied to the flat action of `Γ_ξ` on
`ξ^⊥` then produces a nonzero flat translation, whose Busemann cocycle vanishes by `hvan`. -/

theorem flatTranslation_of_shimizu (n : ℕ) (hn : 3 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (hBb : ∀ m, Submission.Mostow.BieberbachProp m)
    (Γ : Subgroup (PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) η, η ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : PO n 1) η = η → Work.Mostow.bCocy (γ : PO n 1) η = 0)
    (ξ : E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ)
    (hsh : ∃ s : ℝ, 0 < s ∧ ∀ (μ : Γ),
      Submission.Mostow.bd (μ : PO n 1) ξ ≠ ξ → ∀ u : E n,
        Work.Mostow.lev ξ u < s → s ≤ Work.Mostow.lev ξ ((μ : PO n 1) • u)) :
    ∃ δ : Γ, IsParabolic (δ : PO n 1) ∧ bd (δ : PO n 1) ξ = ξ ∧ bCocy (δ : PO n 1) ξ = 0 ∧
      ∃ v : E n, v ≠ 0 ∧ inner ℝ v ξ = 0 ∧
        ∀ u : E n, yc ξ ((δ : PO n 1) • u) = yc ξ u + v := by
  have hAb : POBasic n := POBasic.ofProp hA
  have hId : HypIsoData n := HypIsoData.ofProp hI
  have hξS : ξ ∈ Sph n := hξ.1
  have hdisc : IsDiscrete (SetLike.coe Γ) := hΓ.1
  -- the cusp stabiliser of `ξ` inside `Γ`
  let G : Subgroup (PO n 1) := cuspHoro.stabSub hAb Γ ξ hξS
  have hGmem : ∀ γ : PO n 1, γ ∈ G ↔ γ ∈ Γ ∧ bd γ ξ = ξ := fun γ => cuspHoro.mem_stabSub
  have hGle : ∀ γ ∈ G, γ ∈ Γ := fun γ hγ => (hGmem γ).mp hγ |>.1
  have hGbd : ∀ γ ∈ G, bd γ ξ = ξ := fun γ hγ => (hGmem γ).mp hγ |>.2
  have hlevG : ∀ γ ∈ G, ∀ u : E n, lev ξ (γ • u) = lev ξ u :=
    fun γ hγ u => cuspHoro.stabSub_lev hAb hId hvan hγ hξ u
  have hstab : ∀ γ : Γ, bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0 :=
    fun γ hγ => hvan γ ξ hξ hγ
  -- Shimizu's lemma in horoball form, at level `τ = log s`
  obtain ⟨s, hspos, hsep⟩ := hsh
  set τ : ℝ := Real.log s with hτdef
  have hexpτ : Real.exp τ = s := Real.exp_log hspos
  have hemb : ∀ (γ : Γ), bd (γ : PO n 1) ξ ≠ ξ →
      Disjoint (horoball ξ τ) (horoball (bd (γ : PO n 1) ξ) (τ + bCocy (γ : PO n 1) ξ)) := by
    intro γ hγ
    rw [Set.disjoint_left]
    intro u hu1 hu2
    simp only [horoball, Set.mem_ofPred_eq] at hu1 hu2
    have hηS : bd (γ : PO n 1) ξ ∈ Sph n := hAb.bd_mem (γ : PO n 1) ξ hξS
    have hη : bd ((γ : PO n 1)⁻¹) (bd (γ : PO n 1) ξ) = ξ := by
      have h1 : bd ((γ : PO n 1)⁻¹ * (γ : PO n 1)) ξ = ξ := by
        rw [inv_mul_cancel, hAb.bd_one ξ hξS]
      rw [hAb.bd_mul ((γ : PO n 1)⁻¹) (γ : PO n 1) ξ hξS] at h1
      exact h1
    have hcocy := hId.busemann_cocycle ((γ : PO n 1)⁻¹) (bd (γ : PO n 1) ξ) u hηS
    rw [hη] at hcocy
    have hbcinv : busemann ξ ((γ : PO n 1)⁻¹ • (0 : E n))
        = bCocy ((γ : PO n 1)⁻¹) (bd (γ : PO n 1) ξ) := by
      rw [bCocy, hη]
    have hbc : bCocy ((γ : PO n 1)⁻¹) (bd (γ : PO n 1) ξ) = - bCocy (γ : PO n 1) ξ := by
      have h := bCocy_mul hA hI ((γ : PO n 1)⁻¹) (γ : PO n 1) ξ hξS
      rw [inv_mul_cancel, bCocy_one hA hI ξ hξS] at h
      linarith
    have hdeep : busemann ξ ((γ : PO n 1)⁻¹ • u) < τ := by
      rw [hcocy, hbcinv, hbc]
      linarith
    have hlevlt : lev ξ ((γ : PO n 1)⁻¹ • u) < s := by
      rw [lev_eq_exp hξS, ← hexpτ, Real.exp_lt_exp]
      exact hdeep
    have hge := hsep γ hγ ((γ : PO n 1)⁻¹ • u) hlevlt
    have hround : (γ : PO n 1) • ((γ : PO n 1)⁻¹ • u) = u := by
      rw [← hAb.mul_smul, mul_inv_cancel, hAb.one_smul]
    rw [hround] at hge
    have hge' : τ ≤ busemann ξ u := by
      rw [hτdef, ← Real.log_exp (busemann ξ u), ← lev_eq_exp hξS u,
        Real.log_le_log_iff hspos (lev_pos ξ hξS u)]
      exact hge
    linarith
  -- cocompactness of `Γ_ξ` at the level `τ`, then at every level
  obtain ⟨K, hKc, hK⟩ :=
    cuspCocompactAtLevel n (by omega) hA hI hBb Γ hΓ ξ hξ hstab τ hemb
  have hC : CuspCocompact Γ ξ := cuspCocompactAllLevels n hA hI Γ ξ hξS hstab τ ⟨K, hKc, hK⟩
  -- cocompactness at level `1`, phrased for the stabiliser `G`
  have hcocG : ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n, lev ξ u = 1 →
      ∃ g : ↥G, (g : PO n 1) • u ∈ K := by
    obtain ⟨K', hK'c, hK'⟩ := hC 0
    refine ⟨K', hK'c, fun u hu => ?_⟩
    have hb : busemann ξ u = 0 := by
      have h1 : Real.exp (busemann ξ u) = 1 := by rw [← lev_eq_exp hξS u, hu]
      rw [← Real.log_exp (busemann ξ u), h1, Real.log_one]
    obtain ⟨γ, hγ, hγK⟩ := hK' u hb
    exact ⟨⟨(γ : PO n 1), (hGmem _).mpr ⟨γ.2, hγ⟩⟩, hγK⟩
  -- the flat action of `G` on `ξ^⊥` is cocompact
  obtain ⟨Kf, hKfc, hKf⟩ := cuspFlatCocompact n hI ξ hξS 1 one_pos G hlevG hcocG
  set ρ : ↥G →* (xiPerp ξ ≃ᵢ xiPerp ξ) := cuspFlatHom hAb hId hξS 1 one_pos G hlevG with hρdef
  have hρapp : ∀ (g : ↥G) (y : xiPerp ξ), ρ g y = flatFun hξS 1 (g : PO n 1) y := fun g y => rfl
  -- properness of the flat action, from discreteness of `Γ`
  have hprop : ∀ u₀ : E n, lev ξ u₀ = 1 → ∀ K : Set (E n), IsCompact K →
      {g : ↥G | (g : PO n 1) • u₀ ∈ K}.Finite := by
    intro u₀ _ K hK
    have hfin : {γ : Γ |
        (((fun u : E n => (γ : PO n 1) • u) '' ({u₀} : Set (E n))) ∩ K).Nonempty}.Finite :=
      finite_translates_inter_compact n hA hI hdisc isCompact_singleton hK
    refine (hfin.preimage (f := fun g : ↥G => (⟨(g : PO n 1), hGle g g.2⟩ : Γ))
      (fun a _ b _ hab => Subtype.ext (congrArg (fun γ : Γ => (γ : PO n 1)) hab))).subset ?_
    rintro g hg
    exact ⟨(g : PO n 1) • u₀, ⟨u₀, by simp, rfl⟩, hg⟩
  have hpd : ∀ K : Set (xiPerp ξ), IsCompact K →
      {g : ↥G | ((ρ g) '' K ∩ K).Nonempty}.Finite := by
    intro K hK
    refine (cuspFlatProper n hI ξ hξS 1 one_pos G hlevG hprop K hK).subset ?_
    rintro g ⟨z, ⟨y, hyK, hzy⟩, hzK⟩
    rw [hρapp g y] at hzy
    exact ⟨z, ⟨y, hyK, hzy⟩, hzK⟩
  have hcoc' : ∃ K : Set (xiPerp ξ), IsCompact K ∧ ∀ x : xiPerp ξ, ∃ g : ↥G, ρ g x ∈ K :=
    ⟨Kf, hKfc, fun x => by obtain ⟨g, hg⟩ := hKf x; exact ⟨g, by rwa [hρapp g x]⟩⟩
  -- Bieberbach's first theorem
  obtain ⟨T, w, hTfin, htrans, hspan⟩ :=
    bieberbachInnerProduct (hBb (Module.finrank ℝ (xiPerp ξ))) ρ hpd hcoc'
  haveI : T.FiniteIndex := hTfin
  have htopne : (⊤ : Submodule ℝ (xiPerp ξ)) ≠ ⊥ := by
    intro h
    have h1 : Module.finrank ℝ (xiPerp ξ) = 0 := by
      have h2 := congrArg (fun (s : Submodule ℝ (xiPerp ξ)) => Module.finrank ℝ ↥s) h
      simpa using h2
    have h3 : Module.finrank ℝ (xiPerp ξ) = n - 1 := xiPerpFinrank n hn ξ hξS
    omega
  obtain ⟨t, htT, ht1⟩ : ∃ t ∈ T, t ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hw1 : w 1 = 0 := by
      have h := htrans 1 T.one_mem (0 : xiPerp ξ)
      rw [map_one] at h
      simpa using h.symm
    have hsub : (w '' (T : Set ↥G)) ⊆ ({0} : Set (xiPerp ξ)) := by
      rintro z ⟨g, hg, rfl⟩
      rw [hcon g hg]
      simpa using hw1
    have hle : (⊤ : Submodule ℝ (xiPerp ξ)) ≤ ⊥ := by
      rw [← hspan]
      refine Submodule.span_le.mpr ?_
      rintro z hz
      rw [hsub hz]
      exact Submodule.zero_mem _
    exact htopne (le_bot_iff.mp hle)
  have hρt : ∀ x : xiPerp ξ, ρ t x = x + w t := fun x => htrans t htT x
  have hinj : Function.Injective ρ := by
    intro a b hab
    have h1 : ρ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ∀ y : xiPerp ξ, flatFun hξS 1 (((a * b⁻¹ : ↥G)) : PO n 1) y = y := by
      intro y
      have h := congrArg (fun (e : xiPerp ξ ≃ᵢ xiPerp ξ) => e y) h1
      rw [hρapp (a * b⁻¹) y] at h
      simpa using h
    have h3 : a * b⁻¹ = 1 :=
      cuspFlatInjective n hA hI ξ hξS 1 one_pos G hGbd hlevG (a * b⁻¹) h2
    calc a = a * b⁻¹ * b := by group
      _ = 1 * b := by rw [h3]
      _ = b := one_mul b
  have hwt₀ : w t ≠ 0 := by
    intro h0
    have h1 : ρ t = 1 := by
      apply IsometryEquiv.ext
      intro x
      rw [hρt x, h0, add_zero]
      rfl
    exact ht1 (hinj (by rw [h1, map_one]))
  have hwt : (w t : E n) ≠ 0 := fun h => hwt₀ (Subtype.coe_injective h)
  -- the flat action of `t` is the translation by `w t`
  have htG : ((t : ↥G) : PO n 1) ∈ G := (t : ↥G).2
  have htΓ : ((t : ↥G) : PO n 1) ∈ Γ := hGle ((t : ↥G) : PO n 1) htG
  have hγt : bd (((t : ↥G)) : PO n 1) ξ = ξ := hGbd ((t : ↥G) : PO n 1) htG
  have hlevt : ∀ u : E n, lev ξ ((((t : ↥G)) : PO n 1) • u) = lev ξ u :=
    hlevG ((t : ↥G) : PO n 1) htG
  have hlevel1 : ∀ y : E n, inner ℝ y ξ = 0 →
      yc ξ ((((t : ↥G)) : PO n 1) • hptOf ξ y 1) = y + (w t : E n) := by
    intro y hy
    have h := congrArg (fun z : xiPerp ξ => (z : E n))
      (hρt ⟨y, mem_xiPerp_iff.mpr (by rw [real_inner_comm]; exact hy)⟩)
    rw [hρapp ((t : ↥G))] at h
    simp only [flatFun_coe] at h
    rw [h]; rfl
  have hlevelD : ∀ y : E n, inner ℝ y ξ = 0 → ∀ D : ℝ, 0 < D →
      yc ξ ((((t : ↥G)) : PO n 1) • hptOf ξ y D) = y + (w t : E n) := by
    intro y hy D hD
    rw [← hlevel1 y hy]
    exact yc_smul_hptOf_levelIndep hA hI ξ hξS (((t : ↥G)) : PO n 1) hγt hlevt y hy D 1 hD one_pos
  have hyc_all : ∀ u : E n, yc ξ ((((t : ↥G)) : PO n 1) • u) = yc ξ u + (w t : E n) := by
    intro u
    have hDpos : 0 < lev ξ u := lev_pos ξ hξS u
    have h1 := hlevelD (yc ξ u) (inner_yc hξS u) (lev ξ u) hDpos
    rw [hptOf_yc ξ hξS (lev ξ u) hDpos u rfl] at h1
    exact h1
  -- `w t` is orthogonal to `ξ`
  have hwtperp : inner ℝ (w t : E n) ξ = 0 := by
    have h2 : (((ρ t (0 : xiPerp ξ)) : xiPerp ξ) : E n) = (w t : E n) := by
      have h3 := congrArg (fun z : xiPerp ξ => (z : E n)) (hρt (0 : xiPerp ξ))
      simpa using h3
    rw [← h2]
    exact xiPerp_inner' (ρ t (0 : xiPerp ξ))
  refine ⟨⟨(((t : ↥G)) : PO n 1), htΓ⟩, ?_, hγt,
    hvan ⟨(((t : ↥G)) : PO n 1), htΓ⟩ ξ hξ hγt, (w t : E n), hwt, hwtperp, hyc_all⟩
  exact flatTrans_isParabolic hξS hA hI (((t : ↥G)) : PO n 1) (w t : E n) hwt hyc_all hlevt


/-! ## The target -/

theorem cuspFlatTranslationExists (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (hBb : ∀ m, Submission.Mostow.BieberbachProp m)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) η, η ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) η = η →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) η = 0)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ) :
    ∃ δ : Γ, Submission.Mostow.IsParabolic (δ : LeanEval.Geometry.MostowRigidity.PO n 1) ∧
      Submission.Mostow.bd (δ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
      Work.Mostow.bCocy (δ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0 ∧
      ∃ v : Submission.Mostow.E n, v ≠ 0 ∧ inner ℝ v ξ = 0 ∧
        ∀ u : Submission.Mostow.E n,
          Work.Mostow.yc ξ ((δ : LeanEval.Geometry.MostowRigidity.PO n 1) • u)
            = Work.Mostow.yc ξ u + v := by
  by_cases h2 : n = 2
  · subst h2
    exact flatTranslation_two hA hI Γ hvan ξ hξ
  · have hn3 : 3 ≤ n := by omega
    exact flatTranslation_of_shimizu n hn3 hA hI hBb Γ hΓ hvan ξ hξ
      (Work.Mostow.cuspShimizuPreciseInvariant n hn hA hI Γ hΓ hvan ξ hξ)

end

end Work.Mostow
