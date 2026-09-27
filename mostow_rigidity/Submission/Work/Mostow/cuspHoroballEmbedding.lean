import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.cuspZ2Defs
import Submission.Work.Mostow.cuspZ2
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.hptOf_yc
import Submission.Work.Mostow.stabFlatAction
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.margulisCusp
import Submission.Work.Mostow.paraUniqueFixed
import Submission.Work.Mostow.flatLin_id_of_parabolic_two
import Submission.Work.Mostow.cuspStabCocompactOfLattice

/-!
# Embedding of the cusp horoballs (Shimizu's lemma)

Let `Γ ≤ PO n 1` be a lattice in `ℍⁿ` (`n ≥ 2`) and `ξ ∈ parFixed Γ` a parabolic fixed point
whose cusp is untwisted: `bCocy γ ξ = 0` for every `γ ∈ Γ` fixing `ξ` (hypothesis `hvan`).  Then
some horoball at `ξ` is disjoint from all its `Γ`-translates:

`∃ τ, ∀ γ : Γ, bd γ ξ ≠ ξ → Disjoint (horoball ξ τ) (horoball (bd γ ξ) (τ + bCocy γ ξ))`.

This is Shimizu's lemma, in the form needed by the cusp chapter (it is the `hemb` input of
`Work.Mostow.cuspCocompactAtLevel` and of `cuspHoro.flatCocompact`).

## Proof

* A *flat translation* is a parabolic `δ ∈ Γ` fixing `ξ` which preserves the horosphere levels
  and acts on the flat coordinate by `yc ξ (δ • u) = yc ξ u + v` with `v ≠ 0`
  (`Work.Mostow.cuspParabolicFlatTrans`).  For such an element the hyperbolic displacement of `u`
  is `arccosh (1 + (lev ξ u)^2 ‖v‖^2/2)` (`hdist_flatTrans_arccosh`), hence tends to `0` as
  `u` goes deeper into the cusp at `ξ`, *uniformly* in the flat coordinate
  (`hdist_flatTrans_lt_of_level`).
* Suppose the `τ`-horoball at `ξ` meets its `γ`-translate at a deep level, so that there is `u`
  with both `u` and `γ • u` below level `τ`.  Then `δ` is `ε`-short at `u` and the conjugate
  `σ = γ⁻¹ δ γ` is `ε`-short at `u` as well (because `σ`'s displacement at `u` equals `δ`'s
  displacement at `γ • u`).  The Margulis lemma `Work.Mostow.margulisCusp` (with `R = 1`) then
  forces `bd σ ξ = ξ`; but `σ` fixes the boundary point `bd γ⁻¹ ξ` as well, and a parabolic
  isometry has a unique fixed boundary point (`Work.Mostow.paraUniqueFixed`).  Hence
  `bd γ⁻¹ ξ = ξ`, i.e. `bd γ ξ = ξ`, contradiction.
* A flat translation exists: for `n = 2` any parabolic fixing `ξ` works (its flat linear part is
  `±1` on the one-dimensional space `ξ^⊥`, and `-1` would give a fixed point)
  (`Work.Mostow.flatLin_id_of_parabolic_two`); for `n ≥ 3` it is produced by Bieberbach's theorem
  from the cocompactness of `Γ_ξ` on the horosphere at `ξ`
  (`Work.Mostow.cuspStabCocompactOfLattice`, then Bieberbach via
  `Work.Mostow.bieberbachInnerProduct` applied to the flat action `Work.Mostow.cuspFlatHom`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

variable {n : ℕ}

/-- The flat coordinate at `ξ` of any point is orthogonal to `ξ`. -/
lemma yc_inner_eq_zero {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) : inner ℝ (yc ξ u) ξ = 0 := by
  have h1 : inner ℝ ξ ξ = 1 := by
    rw [real_inner_self_eq_norm_sq]
    have h : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
    rw [h]; norm_num
  rw [yc, real_inner_smul_left, wc, inner_sub_left, real_inner_smul_left, h1, mul_one, sub_self,
    mul_zero]

lemma short_finite (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ)) (u₀ : E n) (K : Set (E n))
    (hK : IsCompact K) : {γ : Γ | (γ : PO n 1) • u₀ ∈ K}.Finite := by
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  set R : ℝ := Real.arcosh (Real.sqrt (1 + M ^ 2)) + hdist (0 : E n) u₀ with hR
  refine (finite_nearStab (hA := POBasic.ofProp hA) (hI := hI') hdisc R).subset ?_
  intro γ hγ
  have hx : ‖(γ : PO n 1) • u₀‖ ≤ M := hM _ hγ
  have h1 : hdist (0 : E n) ((γ : PO n 1) • u₀) ≤ Real.arcosh (Real.sqrt (1 + M ^ 2)) := by
    have h0 : hdist (0 : E n) ((γ : PO n 1) • u₀) = Real.arcosh (tpart ((γ : PO n 1) • u₀)) := by
      rw [hdist]; simp [tpart]
    rw [h0]
    refine (Real.arcosh_le_arcosh (tpart_pos _) (Real.sqrt_pos.2 (by nlinarith [sq_nonneg M]))).mpr ?_
    rw [tpart]
    exact Real.sqrt_le_sqrt (by nlinarith [hx, norm_nonneg ((γ : PO n 1) • u₀), sq_nonneg (M - ‖(γ : PO n 1) • u₀‖)])
  have h2 : hdist ((γ : PO n 1) • u₀) ((γ : PO n 1) • (0 : E n)) = hdist u₀ (0 : E n) :=
    hI'.isom_smul _ _ _
  have htri := hI'.triangle (0 : E n) ((γ : PO n 1) • u₀) ((γ : PO n 1) • (0 : E n))
  rw [h2] at htri
  rw [hI'.symm u₀ 0] at htri
  show hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤ R
  rw [hR]
  linarith

/-- For `δ` fixing `ξ` and preserving the horosphere levels, the flat coordinate of `δ • ·`
on the horospheres of `ξ` does not depend on the level. -/
lemma yc_smul_level_indep (hI : HypIsometryProp n) {ξ : E n} (hξ : ξ ∈ Sph n) {δ : PO n 1}
    (hlev : ∀ u : E n, lev ξ (δ • u) = lev ξ u) {y : E n} (hy : inner ℝ y ξ = 0)
    {E₁ E₂ : ℝ} (h₁ : 0 < E₁) (h₂ : 0 < E₂) :
    yc ξ (δ • hptOf ξ y E₁) = yc ξ (δ • hptOf ξ y E₂) := by
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  have hlev₁ : lev ξ (hptOf ξ y E₁) = E₁ := (hptOf_level ξ hξ E₁ h₁ y hy).1
  have hlev₂ : lev ξ (hptOf ξ y E₂) = E₂ := (hptOf_level ξ hξ E₂ h₂ y hy).1
  have hyc₁ : yc ξ (hptOf ξ y E₁) = y := (hptOf_level ξ hξ E₁ h₁ y hy).2
  have hyc₂ : yc ξ (hptOf ξ y E₂) = y := (hptOf_level ξ hξ E₂ h₂ y hy).2
  have hd : hdist (hptOf ξ y E₁) (hptOf ξ y E₂)
      = hdist (δ • hptOf ξ y E₁) (δ • hptOf ξ y E₂) := (hI'.isom_smul δ _ _).symm
  have h1' := levYcFormula hξ (δ • hptOf ξ y E₁) (δ • hptOf ξ y E₂)
  have h2' := levYcFormula hξ (hptOf ξ y E₁) (hptOf ξ y E₂)
  rw [← hd, hlev (hptOf ξ y E₁), hlev (hptOf ξ y E₂), hlev₁, hlev₂] at h1'
  rw [hlev₁, hlev₂, hyc₁, hyc₂, sub_self, norm_zero] at h2'
  have hkey : (E₁ * E₂ / 2) * ‖yc ξ (δ • hptOf ξ y E₁) - yc ξ (δ • hptOf ξ y E₂)‖ ^ 2 = 0 := by
    linarith [h1', h2']
  have hpos : E₁ * E₂ / 2 ≠ 0 := by positivity
  have hzero : ‖yc ξ (δ • hptOf ξ y E₁) - yc ξ (δ • hptOf ξ y E₂)‖ ^ 2 = 0 := by
    exact (mul_eq_zero.mp hkey).resolve_left hpos
  have hnorm : ‖yc ξ (δ • hptOf ξ y E₁) - yc ξ (δ • hptOf ξ y E₂)‖ = 0 := by
    nlinarith [norm_nonneg (yc ξ (δ • hptOf ξ y E₁) - yc ξ (δ • hptOf ξ y E₂))]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)


/-- For a flat translation `δ` (`yc ξ (δ • u) = yc ξ u + v`, level preserving), the hyperbolic
distance to its translate is `arccosh (1 + (lev ξ u)^2 ‖v‖^2 / 2)`. -/
lemma hdist_flatTrans_arccosh {ξ : E n} (hξ : ξ ∈ Sph n) {δ : PO n 1} {v : E n}
    (hlev : ∀ u : E n, lev ξ (δ • u) = lev ξ u)
    (hyc : ∀ u : E n, yc ξ (δ • u) = yc ξ u + v) (u : E n) :
    hdist u (δ • u) = Real.arcosh (1 + (lev ξ u) ^ 2 * ‖v‖ ^ 2 / 2) := by
  have hD : 0 < lev ξ u := lev_pos ξ hξ u
  have h := hdist_of_lev_eq (D := lev ξ u) hξ hD rfl (hlev u)
  rw [h, hyc u]
  have h2 : yc ξ u - (yc ξ u + v) = -v := by abel
  rw [h2, norm_neg]
  congr 1
  ring

theorem flatTranslation_of_cocompact (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n)
    (hI : HypIsometryProp n) (hBb : ∀ m, BieberbachProp m) (Γ : Subgroup (PO n 1))
    (hΓ : HypLattice Γ)
    (hvan : ∀ (γ : Γ) η, η ∈ parFixed Γ → bd (γ : PO n 1) η = η → bCocy (γ : PO n 1) η = 0)
    (ξ : E n) (hξ : ξ ∈ parFixed Γ)
    (hcoc : ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n, lev ξ u = 1 → ∃ γ : Γ,
      bd (γ : PO n 1) ξ = ξ ∧ (γ : PO n 1) • u ∈ K) :
    ∃ δ : Γ, IsParabolic (δ : PO n 1) ∧ bd (δ : PO n 1) ξ = ξ ∧ bCocy (δ : PO n 1) ξ = 0 ∧
      ∃ v : E n, v ≠ 0 ∧ ∀ u : E n, yc ξ ((δ : PO n 1) • u) = yc ξ u + v := by
  have hξS : ξ ∈ Sph n := hξ.1
  have hAb : POBasic n := POBasic.ofProp hA
  have hId : HypIsoData n := HypIsoData.ofProp hI
  have hdisc : IsDiscrete (SetLike.coe Γ) := hΓ.1
  -- the cusp stabiliser
  let G : Subgroup (PO n 1) :=
    { carrier := {g | g ∈ Γ ∧ bd g ξ = ξ}
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
  have hGmem : ∀ g : PO n 1, g ∈ G ↔ g ∈ Γ ∧ bd g ξ = ξ := fun g => Iff.rfl
  have hGle : ∀ g ∈ G, g ∈ Γ := fun g hg => (hGmem g).mp hg |>.1
  have hGbd : ∀ g ∈ G, bd g ξ = ξ := fun g hg => (hGmem g).mp hg |>.2
  -- every element of the stabiliser preserves the horospheres at `ξ`
  have hlevG : ∀ g ∈ G, ∀ u : E n, lev ξ (g • u) = lev ξ u := by
    intro g hg u
    have hbc : bCocy g ξ = 0 := hvan ⟨g, hGle g hg⟩ ξ hξ (hGbd g hg)
    have hbus := hId.busemann_cocycle g ξ u hξS
    have h0 : busemann ξ (g • (0 : E n)) = 0 := by simpa only [bCocy, hGbd g hg] using hbc
    rw [hGbd g hg, h0, add_zero] at hbus
    rw [lev_eq_exp hξS u, lev_eq_exp hξS (g • u), hbus]
  -- properness of the action on the level-one horosphere
  have hprop : ∀ u₀ : E n, lev ξ u₀ = 1 → ∀ K : Set (E n), IsCompact K →
      {g : G | (g : PO n 1) • u₀ ∈ K}.Finite := by
    intro u₀ _ K hK
    refine (short_finite hA hI Γ hdisc u₀ K hK).preimage
      (f := fun g : G => (⟨(g : PO n 1), hGle g g.2⟩ : Γ)) ?_
    intro a _ b _ hab
    exact Subtype.ext (congrArg (fun z : Γ => (z : PO n 1)) hab)
  -- cocompactness of the action on the level-one horosphere
  have hcocG : ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n, lev ξ u = 1 →
      ∃ g : G, (g : PO n 1) • u ∈ K := by
    obtain ⟨K, hKc, hK⟩ := hcoc
    exact ⟨K, hKc, fun u hu => by
      obtain ⟨γ, hbd, hmem⟩ := hK u hu
      exact ⟨⟨(γ : PO n 1), ⟨γ.2, hbd⟩⟩, hmem⟩⟩
  -- the flat action, Bieberbach
  let ρ : G →* (xiPerp ξ ≃ᵢ xiPerp ξ) := cuspFlatHom hAb hId hξS 1 one_pos G hlevG
  have hfun : ∀ g : G, (ρ g : xiPerp ξ → xiPerp ξ) = fun y => flatFun hξS 1 (g : PO n 1) y := by
    intro g
    funext y
    change (cuspFlatHom hAb hId hξS 1 one_pos G hlevG g) y = flatFun hξS 1 (g : PO n 1) y
    simp only [cuspFlatHom_apply]
  have hpd : ∀ K : Set (xiPerp ξ), IsCompact K →
      {g : G | ((ρ g) '' K ∩ K).Nonempty}.Finite := by
    intro K hK
    simpa only [hfun] using cuspFlatProper n hI ξ hξS 1 one_pos G hlevG hprop K hK
  have hcc : ∃ K : Set (xiPerp ξ), IsCompact K ∧ ∀ x : xiPerp ξ, ∃ g : G, ρ g x ∈ K := by
    obtain ⟨K, hKc, hK⟩ := cuspFlatCocompact n hI ξ hξS 1 one_pos G hlevG hcocG
    exact ⟨K, hKc, fun x => by
      obtain ⟨g, hg⟩ := hK x
      refine ⟨g, ?_⟩
      rw [hfun g]
      exact hg⟩
  obtain ⟨T, v, hTfin, htrans, hspan⟩ :=
    bieberbachInnerProduct (hBb (Module.finrank ℝ (xiPerp ξ))) ρ hpd hcc
  -- a nonzero translation vector
  obtain ⟨t, htne⟩ : ∃ t : T, v (t : G) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hsub : (v '' (T : Set G)) ⊆ ({0} : Set (xiPerp ξ)) := by
      rintro x ⟨t, ht, rfl⟩
      have h0 : v t = 0 := hcon ⟨t, ht⟩
      simp [h0]
    have hbot : Submodule.span ℝ (v '' (T : Set G)) ≤ ⊥ := by
      rw [Submodule.span_le]
      intro x hx
      have := hsub hx
      simpa using this
    have hall : ∀ x : xiPerp ξ, x = 0 := by
      intro x
      have hxspan : x ∈ Submodule.span ℝ (v '' (T : Set G)) := by
        rw [hspan]; exact Submodule.mem_top
      have hx : x ∈ (⊥ : Submodule ℝ (xiPerp ξ)) := hbot hxspan
      simpa using hx
    haveI : Subsingleton (xiPerp ξ) := ⟨fun a b => by rw [hall a, hall b]⟩
    have hfr : Module.finrank ℝ (xiPerp ξ) = 0 := Module.finrank_zero_of_subsingleton
    have h2 := xiPerpFinrank n hn ξ hξS
    omega
  set g₀ : G := (t : G) with hg₀
  have hg₀lev : ∀ u : E n, lev ξ (g₀ • u) = lev ξ u := hlevG g₀ g₀.2
  have hg₀bd : bd (g₀ : PO n 1) ξ = ξ := hGbd g₀ g₀.2
  set δ : Γ := ⟨(g₀ : PO n 1), hGle g₀ g₀.2⟩ with hδdef
  have hδcoe : (δ : PO n 1) = (g₀ : PO n 1) := rfl
  set w : E n := ((v g₀ : xiPerp ξ) : E n) with hwdef
  have hwne : w ≠ 0 := by
    intro h
    apply htne
    have hh : ((v g₀ : xiPerp ξ) : E n) = ((0 : xiPerp ξ) : E n) := by
      rw [← hwdef]; exact h
    exact Subtype.ext hh
  -- the translation law, at level `1`
  have htrans1 : ∀ y : xiPerp ξ, flatFun hξS 1 (g₀ : PO n 1) y = y + v g₀ := by
    intro y
    have h := htrans g₀ t.2 y
    rwa [cuspFlatHom_apply] at h
  -- the translation law, at every level
  have hyc_all : ∀ u : E n, yc ξ ((δ : PO n 1) • u) = yc ξ u + w := by
    intro u
    have hE : 0 < lev ξ u := lev_pos ξ hξS u
    have h1 : (δ : PO n 1) • u = (g₀ : PO n 1) • hptOf ξ (yc ξ u) (lev ξ u) := by
      rw [hptOf_yc ξ hξS (lev ξ u) hE u rfl, hδcoe]
    rw [h1]
    have h2 : yc ξ ((g₀ : PO n 1) • hptOf ξ (yc ξ u) (lev ξ u))
        = yc ξ ((g₀ : PO n 1) • hptOf ξ (yc ξ u) 1) :=
      yc_smul_level_indep hI hξS hg₀lev (inner_yc hξS u) hE one_pos
    rw [h2]
    have hyc : yc ξ u ∈ xiPerp ξ :=
      mem_xiPerp_iff.mpr (by rw [real_inner_comm]; exact inner_yc hξS u)
    have h3 : yc ξ ((g₀ : PO n 1) • hptOf ξ (yc ξ u) 1)
        = ((flatFun hξS 1 (g₀ : PO n 1) ⟨yc ξ u, hyc⟩ : xiPerp ξ) : E n) :=
      flatFun_coe hξS 1 (g₀ : PO n 1) ⟨yc ξ u, hyc⟩
    rw [h3, htrans1 ⟨yc ξ u, hyc⟩]
    simp only [Submodule.coe_add, w]
  refine ⟨δ, ?_, ?_, ?_, w, hwne, hyc_all⟩
  · -- parabolicity
    constructor
    · intro u hu
      have h := hyc_all u
      rw [hu] at h
      have hz : w = 0 := by
        have h' := congrArg (fun z => z - yc ξ u) h
        have h'' : w = (0 : E n) := by simpa using h'.symm
        exact h''
      exact hwne hz
    · intro ε hε
      have hw2 : 0 < ‖w‖ ^ 2 := by
        have : 0 < ‖w‖ := norm_pos_iff.mpr hwne
        positivity
      set D : ℝ := Real.sqrt (2 * (Real.cosh ε - 1) / ‖w‖ ^ 2) * (1 / 2) with hDdef
      have hDpos : 0 < D := by
        rw [hDdef]
        exact mul_pos (Real.sqrt_pos.mpr (div_pos (by linarith [Real.one_lt_cosh.mpr (ne_of_gt hε)]) hw2))
          (by norm_num)
      have hD2 : D ^ 2 * ‖w‖ ^ 2 / 2 = (Real.cosh ε - 1) / 4 := by
        rw [hDdef, mul_pow, Real.sq_sqrt (le_of_lt (div_pos (by linarith [Real.one_lt_cosh.mpr (ne_of_gt hε)]) hw2))]
        field_simp
        ring
      refine ⟨hptOf ξ (0 : E n) D, ?_⟩
      have hlev₀ : lev ξ (hptOf ξ (0 : E n) D) = D :=
        (hptOf_level ξ hξS D hDpos (0 : E n) (by simp)).1
      rw [show ((δ : PO n 1) • hptOf ξ (0 : E n) D)
          = (g₀ : PO n 1) • hptOf ξ (0 : E n) D from by rw [hδcoe]]
      rw [hdist_flatTrans_arccosh hξS hg₀lev (fun u => by rw [hδcoe]; exact hyc_all u)
          (hptOf ξ (0 : E n) D), hlev₀]
      rw [← Real.arcosh_cosh (le_of_lt hε)]
      refine (Real.arcosh_lt_arcosh (by positivity) (Real.cosh_pos ε)).mpr ?_
      rw [hD2]
      linarith [Real.one_lt_cosh.mpr (ne_of_gt hε)]
  · rw [hδcoe]; exact hg₀bd
  · exact hvan δ ξ hξ (by rw [hδcoe]; exact hg₀bd)

/-- A point of level `< D` is moved by `δ` by less than `ε`, if `1 + D^2 ‖v‖^2/2 < cosh ε`. -/
lemma hdist_flatTrans_lt {ξ : E n} (hξ : ξ ∈ Sph n) {δ : PO n 1} {v : E n}
    (hlev : ∀ u : E n, lev ξ (δ • u) = lev ξ u)
    (hyc : ∀ u : E n, yc ξ (δ • u) = yc ξ u + v)
    {D ε : ℝ} (hDnn : 0 ≤ D) (hε : 0 < ε)
    (hbound : 1 + D ^ 2 * ‖v‖ ^ 2 / 2 < Real.cosh ε) {u : E n} (hu : lev ξ u < D) :
    hdist u (δ • u) < ε := by
  rw [hdist_flatTrans_arccosh hξ hlev hyc u, ← Real.arcosh_cosh (le_of_lt hε)]
  refine (Real.arcosh_lt_arcosh (by positivity) (Real.cosh_pos ε)).mpr ?_
  have h1 : lev ξ u ^ 2 < D ^ 2 := by
    have hpos : 0 < lev ξ u := lev_pos ξ hξ u
    nlinarith
  have h2 : (lev ξ u) ^ 2 * ‖v‖ ^ 2 / 2 ≤ D ^ 2 * ‖v‖ ^ 2 / 2 := by
    have := sq_nonneg ‖v‖
    nlinarith
  linarith

theorem preciseInvariant_of_flatTranslation (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ)
    (ξ : E n) (hξ : ξ ∈ parFixed Γ)
    (hδ : ∃ δ : Γ, IsParabolic (δ : PO n 1) ∧ bd (δ : PO n 1) ξ = ξ ∧
      bCocy (δ : PO n 1) ξ = 0 ∧
      ∃ v : E n, v ≠ 0 ∧ ∀ u : E n, yc ξ ((δ : PO n 1) • u) = yc ξ u + v) :
    ∃ τ : ℝ, ∀ γ : Γ, bd (γ : PO n 1) ξ ≠ ξ →
      ¬ ∃ u : E n, busemann ξ u < τ ∧ busemann ξ ((γ : PO n 1) • u) < τ := by
  have hξS : ξ ∈ Sph n := hξ.1
  obtain ⟨δ, hδpar, hδfix, hδbc, v, hvne, hyc⟩ := hδ
  have hpb : POBasic n := POBasic.ofProp hA
  have hvd : HypIsoData n := HypIsoData.ofProp hI
  have hδlev : ∀ u : E n, lev ξ ((δ : PO n 1) • u) = lev ξ u := by
    intro u
    have hbus := hvd.busemann_cocycle (δ : PO n 1) ξ u hξS
    have h0 : busemann ξ ((δ : PO n 1) • (0 : E n)) = 0 := by
      simpa only [bCocy, hδfix] using hδbc
    rw [hδfix, h0, add_zero] at hbus
    rw [lev_eq_exp hξS u, lev_eq_exp hξS ((δ : PO n 1) • u), hbus]
  -- Margulis constant
  obtain ⟨ε, hεpos, hεall⟩ := margulisCusp n (by omega) hA hI 1
  set e : ℝ := min ε 1 with hedef
  have hepos : 0 < e := lt_min hεpos one_pos
  have hele : e ≤ ε := min_le_left _ _
  have hele1 : e ≤ 1 := min_le_right _ _
  have hv2 : 0 < ‖v‖ ^ 2 := by
    have : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    positivity
  -- choose the level
  have hcoshe : 1 < Real.cosh e := Real.one_lt_cosh.mpr (ne_of_gt hepos)
  set D : ℝ := Real.sqrt (2 * (Real.cosh e - 1) / ‖v‖ ^ 2) * (1/2) with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]
    exact mul_pos (Real.sqrt_pos.mpr (div_pos (by linarith) hv2)) (by norm_num)
  have hDnn : 0 ≤ D := le_of_lt hDpos
  have hD2 : D ^ 2 * ‖v‖ ^ 2 / 2 = (Real.cosh e - 1) / 4 := by
    rw [hDdef, mul_pow, Real.sq_sqrt (le_of_lt (div_pos (by linarith) hv2))]
    field_simp
    ring
  have hbound : 1 + D ^ 2 * ‖v‖ ^ 2 / 2 < Real.cosh e := by
    rw [hD2]; linarith
  refine ⟨Real.log D, fun γ hγ => ?_⟩
  rintro ⟨u, hu1, hu2⟩
  have hle1 : lev ξ u < D := by
    rw [lev_eq_exp hξS u, ← Real.exp_log hDpos, Real.exp_lt_exp]; exact hu1
  have hle2 : lev ξ ((γ : PO n 1) • u) < D := by
    rw [lev_eq_exp hξS ((γ : PO n 1) • u), ← Real.exp_log hDpos, Real.exp_lt_exp]; exact hu2
  have h1 : hdist u ((δ : PO n 1) • u) < ε :=
    lt_of_lt_of_le (hdist_flatTrans_lt hξS hδlev hyc hDnn hepos hbound hle1) hele
  set σ : Γ := ⟨(γ : PO n 1)⁻¹ * (δ : PO n 1) * (γ : PO n 1),
    mul_mem (mul_mem (inv_mem γ.2) δ.2) γ.2⟩ with hσdef
  have hσcoe : (σ : PO n 1) = (γ : PO n 1)⁻¹ * (δ : PO n 1) * (γ : PO n 1) := rfl
  have hγσ : (γ : PO n 1) • ((σ : PO n 1) • u) = (δ : PO n 1) • ((γ : PO n 1) • u) := by
    rw [← hpb.mul_smul, hσcoe]
    have h1' : ((γ : PO n 1) * ((γ : PO n 1)⁻¹ * (δ : PO n 1) * (γ : PO n 1)))
        = (δ : PO n 1) * (γ : PO n 1) := by group
    rw [h1', hpb.mul_smul]
  have h2 : hdist u ((σ : PO n 1) • u) ≤ 1 := by
    have hA1 : hdist u ((σ : PO n 1) • u)
        = hdist ((γ : PO n 1) • u) ((γ : PO n 1) • ((σ : PO n 1) • u)) :=
      (hvd.isom_smul (γ : PO n 1) u ((σ : PO n 1) • u)).symm
    rw [hA1, hγσ]
    exact le_trans (le_of_lt (hdist_flatTrans_lt hξS hδlev hyc hDnn hepos hbound hle2)) hele1
  -- Margulis
  have hbdσ : bd (σ : PO n 1) ξ = ξ :=
    hεall Γ hΓ.1 u ξ δ σ hδpar hξS hδfix h1 h2
  have hηS : bd (γ : PO n 1)⁻¹ ξ ∈ Sph n := hpb.bd_mem _ _ hξS
  have hσpar : IsParabolic (σ : PO n 1) := by
    have h := isParabolic_conj hA hI (γ : PO n 1)⁻¹ (δ : PO n 1) hδpar
    simpa [hσcoe, inv_inv] using h
  have hη1 : bd (γ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) = ξ := by
    rw [← hpb.bd_mul (γ : PO n 1) ((γ : PO n 1)⁻¹) ξ hξS, mul_inv_cancel, hpb.bd_one ξ hξS]
  have hfixσ' : bd (σ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) = bd (γ : PO n 1)⁻¹ ξ := by
    have hcoe : (σ : PO n 1) = (γ : PO n 1)⁻¹ * ((δ : PO n 1) * (γ : PO n 1)) := by
      rw [hσcoe]; group
    rw [hcoe, hpb.bd_mul ((γ : PO n 1)⁻¹) ((δ : PO n 1) * (γ : PO n 1)) (bd (γ : PO n 1)⁻¹ ξ) hηS,
      hpb.bd_mul (δ : PO n 1) (γ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) hηS, hη1, hδfix]
  have heq : bd (γ : PO n 1)⁻¹ ξ = ξ :=
    paraUniqueFixed hpb hvd hσpar hξS hbdσ hηS hfixσ'
  refine hγ ?_
  have h3 : bd (γ : PO n 1) ξ = bd (γ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) := by rw [heq]
  rw [h3, hη1]

/-- The horoball form of the precise invariance. -/

theorem horoballEmbedding_of_flatTranslation (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n)
    (hI : HypIsometryProp n) (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ)
    (ξ : E n) (hξ : ξ ∈ parFixed Γ)
    (hδ : ∃ δ : Γ, IsParabolic (δ : PO n 1) ∧ bd (δ : PO n 1) ξ = ξ ∧
      bCocy (δ : PO n 1) ξ = 0 ∧
      ∃ v : E n, v ≠ 0 ∧ ∀ u : E n, yc ξ ((δ : PO n 1) • u) = yc ξ u + v) :
    ∃ τ : ℝ, ∀ γ : Γ, bd (γ : PO n 1) ξ ≠ ξ →
      Disjoint (horoball ξ τ)
        (horoball (bd (γ : PO n 1) ξ) (τ + bCocy (γ : PO n 1) ξ)) := by
  obtain ⟨t, ht⟩ := preciseInvariant_of_flatTranslation n hn hA hI Γ hΓ ξ hξ hδ
  have hpb : POBasic n := POBasic.ofProp hA
  have hvd : HypIsoData n := HypIsoData.ofProp hI
  have hξS : ξ ∈ Sph n := hξ.1
  refine ⟨t, fun γ hγ => ?_⟩
  rw [Set.disjoint_left]
  intro u hu1 hu2
  have hu1' : busemann ξ u < t := hu1
  have hu2' : busemann (bd (γ : PO n 1) ξ) u < t + bCocy (γ : PO n 1) ξ := hu2
  have hsmul : (γ : PO n 1) • ((γ : PO n 1)⁻¹ • u) = u := by
    rw [← hpb.mul_smul, mul_inv_cancel, hpb.one_smul]
  have hcocy : busemann (bd (γ : PO n 1) ξ) u
      = busemann ξ ((γ : PO n 1)⁻¹ • u) + bCocy (γ : PO n 1) ξ := by
    have h := hvd.busemann_cocycle (γ : PO n 1) ξ ((γ : PO n 1)⁻¹ • u) hξS
    rwa [hsmul] at h
  have hw1 : busemann ξ ((γ : PO n 1)⁻¹ • u) < t := by linarith
  have hw2 : busemann ξ ((γ : PO n 1) • ((γ : PO n 1)⁻¹ • u)) < t := by
    rw [hsmul]; exact hu1'
  exact ht γ hγ ⟨(γ : PO n 1)⁻¹ • u, hw1, hw2⟩

/-- **n = 2**: the flat linear part of a parabolic fixing `ξ` is the identity, so it acts on the
horocycles by a nonzero translation. -/
theorem flatTrans_of_lattice_two (hA : POActionProp 2) (hI : HypIsometryProp 2)
    (Γ : Subgroup (PO 2 1))
    (hvan : ∀ (γ : Γ) η, η ∈ parFixed Γ → bd (γ : PO 2 1) η = η → bCocy (γ : PO 2 1) η = 0)
    (ξ : E 2) (hξ : ξ ∈ parFixed Γ)
    :
    ∃ δ : Γ, IsParabolic (δ : PO 2 1) ∧ bd (δ : PO 2 1) ξ = ξ ∧ bCocy (δ : PO 2 1) ξ = 0 ∧
      ∃ v : E 2, v ≠ 0 ∧ ∀ u : E 2, yc ξ ((δ : PO 2 1) • u) = yc ξ u + v := by
  obtain ⟨γ, hpar, hfix⟩ := hξ.2
  have hξS : ξ ∈ Sph 2 := hξ.1
  have hpb : POBasic 2 := POBasic.ofProp hA
  have hvd : HypIsoData 2 := HypIsoData.ofProp hI
  have hbc : bCocy (γ : PO 2 1) ξ = 0 := hvan γ ξ hξ hfix
  have hβ : busemann ξ ((γ : PO 2 1) • (0 : E 2)) = 0 := by
    simpa only [bCocy, hfix] using hbc
  obtain ⟨A, v, hvperp, hAperp, hAnorm, hact⟩ :=
    stabFlatAction 2 hA hI ξ hξS (γ : PO 2 1) hfix hβ
  have hAid' : ∀ y : E 2, inner ℝ y ξ = 0 → A y = y :=
    flatLin_id_of_parabolic_two hA hI ξ hξS (γ : PO 2 1) hpar hfix A v hvperp hAperp hAnorm hact
  have hlevγ : ∀ u : E 2, lev ξ ((γ : PO 2 1) • u) = lev ξ u := by
    intro u
    have hbus := hvd.busemann_cocycle (γ : PO 2 1) ξ u hξS
    rw [hfix, hβ, add_zero] at hbus
    rw [lev_eq_exp hξS u, lev_eq_exp hξS ((γ : PO 2 1) • u), hbus]
  have hyc : ∀ u : E 2, yc ξ ((γ : PO 2 1) • u) = yc ξ u + v := by
    intro u
    have hDpos : 0 < lev ξ u := lev_pos ξ hξS u
    have hkey := (hact (yc ξ u) (lev ξ u) (yc_inner_eq_zero hξS u) hDpos).2
    rw [hptOf_yc ξ hξS (lev ξ u) hDpos u rfl] at hkey
    rw [hkey, hAid' (yc ξ u) (yc_inner_eq_zero hξS u)]
  refine ⟨γ, hpar, hfix, hbc, v, ?_, hyc⟩
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

/-- **`n ≥ 3`**: cocompactness of the cusp stabiliser on the horosphere (Bieberbach) provides a
flat translation for the cusp. -/
theorem flatTrans_of_lattice_ge3 (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n)
    (hI : HypIsometryProp n) (hBb : ∀ m, BieberbachProp m) (Γ : Subgroup (PO n 1))
    (hΓ : HypLattice Γ)
    (hvan : ∀ (γ : Γ) η, η ∈ parFixed Γ → bd (γ : PO n 1) η = η → bCocy (γ : PO n 1) η = 0)
    (ξ : E n) (hξ : ξ ∈ parFixed Γ) :
    ∃ δ : Γ, IsParabolic (δ : PO n 1) ∧ bd (δ : PO n 1) ξ = ξ ∧ bCocy (δ : PO n 1) ξ = 0 ∧
      ∃ v : E n, v ≠ 0 ∧ ∀ u : E n, yc ξ ((δ : PO n 1) • u) = yc ξ u + v := by
  obtain ⟨K, hKc, hK⟩ := cuspStabCocompactOfLattice n hn hA hI hBb Γ hΓ hvan ξ hξ
  exact flatTranslation_of_cocompact n hn hA hI hBb Γ hΓ hvan ξ hξ ⟨K, hKc, hK⟩

/-- **Shimizu's lemma (horoball form).**  For a lattice `Γ` and a parabolic fixed point `ξ` with
vanishing cocycle on the stabiliser, the horoball at `ξ` of some level is disjoint from all its
`Γ`-translates. -/
theorem cuspHoroballEmbedding (n : ℕ) (hn : 2 ≤ n)
    (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    (hBb : ∀ m, Submission.Mostow.BieberbachProp m)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ) :
    ∃ τ : ℝ, ∀ γ : Γ,
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ ≠ ξ →
      Disjoint (Submission.Mostow.horoball ξ τ)
        (Submission.Mostow.horoball
          (Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ)
          (τ + Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ)) := by
  by_cases h2 : n = 2
  · subst h2
    exact horoballEmbedding_of_flatTranslation 2 hn hA hI Γ hΓ ξ hξ
      (flatTrans_of_lattice_two hA hI Γ hvan ξ hξ)
  · have hn3 : 3 ≤ n := by omega
    exact horoballEmbedding_of_flatTranslation n hn hA hI Γ hΓ ξ hξ
      (flatTrans_of_lattice_ge3 n hn3 hA hI hBb Γ hΓ hvan ξ hξ)

end

end Work.Mostow
