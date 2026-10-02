import Mathlib
import Submission.Work.NAKANE.Defs
import Submission.Work.NAKANE.PotentialTop
import Submission.Work.NAKANE.NakaneHomeo
import Submission.Work.NAKANE.PhiProper.isCompact_Phi_preimage

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Injectivity of `Φ` on the exterior of the mandelbar from locality and injectivity at infinity

`Φ = Work.ParamRays.Phi` is the parameter Böttcher map, junk value `0` on the mandelbar `Mb`.
This file proves that **(R1)** (`Φ` is a local homeomorphism on `Mbᶜ`) together with injectivity of
`Φ` on a far annulus `{R ≤ ‖c‖}` already implies **(R2)** (`Φ` is injective on all of `Mbᶜ`).

The mechanism is the standard one for a proper local homeomorphism onto a connected space:

* `Φ` is injective near infinity, so some value at infinity has a *unique* preimage
  (`nonempty_uniqSet`);
* the set `uniqSet` of values with a unique preimage is open (closedness of `phiExt` from its
  properness, `isOpen_uniqSet`) and likewise the set `collSet` of values with two distinct preimages
  is open (`isOpen_collSet`);
* `uniqSet` and `collSet` partition the exterior disc, which is preconnected; as `uniqSet` is
  nonempty it is everything, so `collSet` is empty, i.e. `Φ` is injective.
-/

namespace Work.NAKANE.InjOfFar

open Classical Filter Set
open scoped Topology ComplexConjugate

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Properness of `phiExt` -/

/-- **`phiExt` is a proper map.**  The preimage of a compact subset of the exterior disc is compact
by `Work.NAKANE.PhiProper.isCompact_Phi_preimage`. -/
theorem isProperMap_phiExt : IsProperMap phiExt := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_phiExt, fun K hK => ?_⟩
  rw [Subtype.isCompact_iff]
  set K' : Set ℂ := (Subtype.val : ↥extDisc → ℂ) '' K with hK'def
  have hK'c : IsCompact K' := hK.image continuous_subtype_val
  have hK'1 : ∀ w ∈ K', 1 < ‖w‖ := by
    rintro w ⟨y, _hy, rfl⟩
    exact y.2
  have hV : (Subtype.val '' (phiExt ⁻¹' K) : Set ℂ)
      = {c : ℂ | c ∉ Mandelbar ∧ Phi c ∈ K'} := by
    ext c
    constructor
    · rintro ⟨x, hxK, rfl⟩
      refine ⟨x.2, ?_⟩
      exact ⟨phiExt x, hxK, rfl⟩
    · rintro ⟨hcM, hcPhi⟩
      obtain ⟨y, hyK, hy⟩ := hcPhi
      have he : phiExt ⟨c, hcM⟩ = y := Subtype.ext (by rw [phiExt_coe]; exact hy.symm)
      refine ⟨⟨c, hcM⟩, ?_, rfl⟩
      show phiExt ⟨c, hcM⟩ ∈ K
      rw [he]
      exact hyK
  rw [hV]
  exact Work.NAKANE.PhiProper.isCompact_Phi_preimage hK'c hK'1

/-- `phiExt` is a closed map. -/
theorem isClosedMap_phiExt : IsClosedMap phiExt := isProperMap_phiExt.isClosedMap

/-! ## The "unique preimage" and "collision" sets -/

/-- The values of the exterior disc having a **unique** preimage under `Φ`. -/
def uniqSet : Set ↥extDisc := {y | ∃! c : ↥Mbᶜ, phiExt c = y}

/-- The values of the exterior disc having **two distinct** preimages under `Φ`. -/
def collSet : Set ↥extDisc := {y | ∃ a b : ↥Mbᶜ, a ≠ b ∧ phiExt a = y ∧ phiExt b = y}

/-! ## Openness of the two sets -/

/-- The collision set is open: two distinct points giving the same value keep giving distinct
preimages in a neighbourhood, by the local homeomorphism property. -/
theorem isOpen_collSet (hloc : PhiLocalHomeo) : IsOpen collSet := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨a, b, hab, hay, hby⟩
  obtain ⟨ea, hae, hfeqa⟩ := hloc (a : ℂ) a.2
  obtain ⟨eb, hbe, hfeqb⟩ := hloc (b : ℂ) b.2
  have hab' : (a : ℂ) ≠ (b : ℂ) := fun h => hab (Subtype.ext h)
  have hdist : 0 < dist (a : ℂ) (b : ℂ) := dist_pos.mpr hab'
  set r : ℝ := dist (a : ℂ) (b : ℂ) / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  have hdisj : Disjoint (Metric.ball (a : ℂ) r) (Metric.ball (b : ℂ) r) :=
    Metric.ball_disjoint_ball (by rw [hrdef]; linarith)
  set Ua : Set ℂ := ea.source ∩ Mbᶜ ∩ Metric.ball (a : ℂ) r with hUadef
  set Ub : Set ℂ := eb.source ∩ Mbᶜ ∩ Metric.ball (b : ℂ) r with hUbdef
  have hUao : IsOpen Ua := by
    rw [hUadef]; exact (ea.open_source.inter isOpen_compl_Mb).inter Metric.isOpen_ball
  have hUbo : IsOpen Ub := by
    rw [hUbdef]; exact (eb.open_source.inter isOpen_compl_Mb).inter Metric.isOpen_ball
  have hUas : Ua ⊆ ea.source := fun z hz => hz.1.1
  have hUbs : Ub ⊆ eb.source := fun z hz => hz.1.1
  have hUaM : Ua ⊆ Mbᶜ := fun z hz => hz.1.2
  have hUbM : Ub ⊆ Mbᶜ := fun z hz => hz.1.2
  have hUaball : Ua ⊆ Metric.ball (a : ℂ) r := fun z hz => hz.2
  have hUbball : Ub ⊆ Metric.ball (b : ℂ) r := fun z hz => hz.2
  have hdisjU : Disjoint Ua Ub := hdisj.mono hUaball hUbball
  have himga : IsOpen (Phi '' Ua) := by
    rw [hfeqa]; exact ea.isOpen_image_of_subset_source hUao hUas
  have himgb : IsOpen (Phi '' Ub) := by
    rw [hfeqb]; exact eb.isOpen_image_of_subset_source hUbo hUbs
  have hay' : Phi (a : ℂ) = (y : ℂ) := congrArg Subtype.val hay
  have hby' : Phi (b : ℂ) = (y : ℂ) := congrArg Subtype.val hby
  have hyUa : (y : ℂ) ∈ Phi '' Ua :=
    ⟨(a : ℂ), ⟨⟨hae, a.2⟩, by rw [Metric.mem_ball, dist_self]; exact hr⟩, hay'⟩
  have hyUb : (y : ℂ) ∈ Phi '' Ub :=
    ⟨(b : ℂ), ⟨⟨hbe, b.2⟩, by rw [Metric.mem_ball, dist_self]; exact hr⟩, hby'⟩
  have hO : IsOpen (Phi '' Ua ∩ Phi '' Ub) := himga.inter himgb
  refine Filter.mem_of_superset
    ((continuous_subtype_val.continuousAt).preimage_mem_nhds (hO.mem_nhds ⟨hyUa, hyUb⟩)) ?_
  rintro y' hy'
  rw [Set.mem_preimage] at hy'
  obtain ⟨ha'y', hb'y'⟩ := hy'
  obtain ⟨a', ha'Ua, ha'eq⟩ := ha'y'
  obtain ⟨b', hb'Ub, hb'eq⟩ := hb'y'
  refine ⟨⟨a', hUaM ha'Ua⟩, ⟨b', hUbM hb'Ub⟩, ?_, ?_, ?_⟩
  · intro heq
    have hab'' : a' = b' := by simpa using congrArg Subtype.val heq
    rw [← hab''] at hb'Ub
    exact (Set.disjoint_left.mp hdisjU) ha'Ua hb'Ub
  · exact Subtype.ext (by rw [phiExt_coe]; exact ha'eq)
  · exact Subtype.ext (by rw [phiExt_coe]; exact hb'eq)

/-- The "unique preimage" set is open: if `y` has the single preimage `x`, a small neighbourhood of
`y` has all its preimages in a neighbourhood of `x` on which `Φ` is injective. -/
theorem isOpen_uniqSet (hloc : PhiLocalHomeo) : IsOpen uniqSet := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨c₀, hc₀, huniq⟩
  obtain ⟨e, hce, hfeq⟩ := hloc (c₀ : ℂ) c₀.2
  set A : Set ↥Mbᶜ := {x | (x : ℂ) ∉ e.source} with hAdef
  have hAclosed : IsClosed A := by
    rw [hAdef]
    exact (isClosed_compl_iff.mpr e.open_source).preimage continuous_subtype_val
  have hclosed : IsClosed (phiExt '' A) := isClosedMap_phiExt A hAclosed
  have hynot : y ∉ phiExt '' A := by
    rintro ⟨x, hxA, hxy⟩
    have hx0 : x = c₀ := huniq x hxy
    have : (x : ℂ) ∈ e.source := by rw [hx0]; exact hce
    exact hxA this
  refine Filter.mem_of_superset (hclosed.isOpen_compl.mem_nhds hynot) ?_
  rintro y' hy'
  rw [Set.mem_compl_iff, Set.mem_image] at hy'
  push_neg at hy'
  obtain ⟨x₀, hx₀⟩ := surjective_phiExt_of_localHomeo hloc y'
  refine ⟨x₀, hx₀, fun x' hx' => ?_⟩
  have hx'U : (x' : ℂ) ∈ e.source := by
    by_contra h
    exact (hy' x' h) hx'
  have hx₀U : (x₀ : ℂ) ∈ e.source := by
    by_contra h
    exact (hy' x₀ h) hx₀
  have h1 : Phi (x' : ℂ) = Phi (x₀ : ℂ) :=
    (congrArg Subtype.val hx').trans (congrArg Subtype.val hx₀).symm
  exact Subtype.ext (e.injOn hx'U hx₀U (hfeq ▸ h1))

/-! ## Non-emptiness from injectivity at infinity -/

/-- **Some value of the exterior disc has a unique preimage.**  Choose `w` far out, so that any
preimage `c` of `w` must lie beyond the radius `R` on which `Φ` is known to be injective. -/
theorem nonempty_uniqSet (hloc : PhiLocalHomeo) {R : ℝ}
    (hfar : Set.InjOn Work.ParamRays.Phi {c : ℂ | R ≤ ‖c‖}) : uniqSet.Nonempty := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R).bddAbove_image
    (continuous_paramPotential.continuousOn (s := Metric.closedBall (0 : ℂ) R))
  set M : ℝ := Real.exp (2 * B) with hMdef
  have hMpos : 0 < M := Real.exp_pos _
  set w : ℂ := ((max M 1 + 1 : ℝ) : ℂ) with hwdef
  have hwnorm : ‖w‖ = max M 1 + 1 := by
    have h1 : ‖w‖ = |max M 1 + 1| := by rw [hwdef]; exact RCLike.norm_ofReal _
    rw [h1, abs_of_nonneg (by positivity)]
  have hwR : M < ‖w‖ := by
    rw [hwnorm]
    have := le_max_left M 1
    linarith
  have hw1 : 1 < ‖w‖ := by
    rw [hwnorm]
    have := le_max_right M 1
    linarith
  obtain ⟨c, hcMb, hcPhi⟩ := Phi_surj_of_localHomeo hloc hw1
  have hfar_bound : ∀ z : ℂ, Work.ParamRays.Phi z = w → R ≤ ‖z‖ := by
    intro z hzPhi
    by_contra h
    rw [not_le] at h
    have hzMb : z ∉ Mb := by
      intro hzMb
      have hz0 : w = 0 := by rw [← hzPhi, Work.ParamRays.Phi_eq_zero_of_mem hzMb]
      rw [hz0, norm_zero] at hw1
      linarith
    have hzB : Work.ParamRays.paramPotential z ≤ B :=
      hB (a := Work.ParamRays.paramPotential z) (Set.mem_image_of_mem _ (by
        rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt h))
    have hnorm : ‖Work.ParamRays.Phi z‖
        = Real.exp (2 * Work.ParamRays.paramPotential z) :=
      Work.ParamRays.norm_Phi_eq_exp Work.Bottcher.bottcherExists_crit hzMb
    have hw_eq : ‖w‖ = Real.exp (2 * Work.ParamRays.paramPotential z) := by
      rw [← hzPhi, hnorm]
    have hleM : Real.exp (2 * Work.ParamRays.paramPotential z) ≤ M := by
      rw [hMdef]; exact Real.exp_le_exp.mpr (by linarith)
    rw [hw_eq] at hwR
    linarith
  refine ⟨⟨w, hw1⟩, ⟨c, hcMb⟩, ?_, ?_⟩
  · exact Subtype.ext hcPhi
  · rintro x hx
    have hxw : Work.ParamRays.Phi (x : ℂ) = w := congrArg Subtype.val hx
    exact Subtype.ext (hfar (hfar_bound x hxw) (hfar_bound c hcPhi) (by rw [hxw, hcPhi]))

/-! ## The main theorem -/

/-- **Injectivity of `Φ` on the exterior of the mandelbar from (R1) and injectivity near infinity.** Here `Mb` is the mandelbar, `Phi = Work.ParamRays.Phi` (the parameter Böttcher map, with the junk value `0` on `Mb`), `PhiLocalHomeo := IsLocalHomeomorphOn Phi Mbᶜ` and `PhiInjOn := Set.InjOn Phi Mbᶜ`. -/
theorem injOn_of_localHomeo_of_farInj (hloc : PhiLocalHomeo) {R : ℝ}
    (hfar : Set.InjOn Work.ParamRays.Phi {c : ℂ | R ≤ ‖c‖}) : PhiInjOn := by
  haveI : PreconnectedSpace ↥extDisc :=
    isPreconnected_iff_preconnectedSpace.mp
      (Work.ParamRays.isPreconnected_lt_norm (M := 1) (by norm_num))
  have hsurj : Function.Surjective phiExt := surjective_phiExt_of_localHomeo hloc
  have hCeq : uniqSetᶜ = collSet := by
    ext y
    constructor
    · intro hy
      rw [Set.mem_compl_iff] at hy
      obtain ⟨x₀, hx₀⟩ := hsurj y
      have htwo : ∃ x : ↥Mbᶜ, phiExt x = y ∧ x ≠ x₀ := by
        by_contra h
        push_neg at h
        exact hy ⟨x₀, hx₀, fun x hx => h x hx⟩
      obtain ⟨x, hx, hne⟩ := htwo
      exact ⟨x₀, x, hne.symm, hx₀, hx⟩
    · intro hy
      rw [Set.mem_compl_iff]
      rintro ⟨x, hx, huniq⟩
      obtain ⟨a, b, hab, hay, hby⟩ := hy
      exact hab ((huniq a hay).trans (huniq b hby).symm)
  have hPopen : IsOpen uniqSet := isOpen_uniqSet hloc
  have hCopen : IsOpen collSet := isOpen_collSet hloc
  have hPclosed : IsClosed uniqSet := by
    rw [← isOpen_compl_iff]
    rw [hCeq]
    exact hCopen
  have hne : (Set.univ ∩ uniqSet).Nonempty := by
    obtain ⟨y, hy⟩ := nonempty_uniqSet hloc hfar
    exact ⟨y, Set.mem_univ _, hy⟩
  have hsub : (Set.univ : Set ↥extDisc) ⊆ uniqSet :=
    (isPreconnected_univ).subset_isClopen ⟨hPclosed, hPopen⟩ hne
  have hPuniv : uniqSet = Set.univ := Set.Subset.antisymm (Set.subset_univ _) hsub
  have hCempty : collSet = ∅ := by
    rw [← hCeq, hPuniv, Set.compl_univ]
  intro a ha b hb hab
  by_contra hneab
  have hfy : phiExt ⟨a, ha⟩ = phiExt ⟨b, hb⟩ := by
    apply Subtype.ext
    simpa only [phiExt_coe, Phi_eq_ParamRays] using hab
  have hne' : (⟨a, ha⟩ : ↥Mbᶜ) ≠ ⟨b, hb⟩ := fun h => hneab (Subtype.ext_iff.mp h)
  have hmemC : phiExt ⟨a, ha⟩ ∈ collSet := ⟨⟨a, ha⟩, ⟨b, hb⟩, hne', rfl, hfy.symm⟩
  rw [hCempty] at hmemC
  exact hmemC

end

end Work.NAKANE.InjOfFar
