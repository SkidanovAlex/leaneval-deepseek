/-
# Nakane's homeomorphism theorem, reduced to its two classical inputs

`Work.ParamRays.NakaneHomeo` is the statement that the parameter Böttcher map `Φ` is a
homeomorphism of `Mbᶜ` onto the exterior disc `extDisc = {w : ℂ | 1 < ‖w‖}`.  This file reduces it
to two named inputs, and proves everything else:

* `Work.NAKANE.PhiLocalHomeo` **(R1)** — `Φ` is a local homeomorphism on `Mbᶜ` (Nakane 1993:
  `c ↦ Φ c` is real-analytic with nonvanishing Jacobian);
* `Work.NAKANE.PhiInjOn` **(R2)** — `Φ` is injective on `Mbᶜ` (the other half of Nakane's theorem).

What is proved here, unconditionally or from (R1) alone:

* `Work.NAKANE.isOpen_compl_Mb` : `Mbᶜ` is open (`Mb` is compact, hence closed);
* `Work.NAKANE.isOpen_image_Phi_of_localHomeo` : **(R1) alone** — for every open `U ⊆ Mbᶜ` the
  image `Φ '' U` is open, and hence `Φ '' Mbᶜ` is open in `ℂ`.  Indeed at `c ∈ Mbᶜ` the local
  homeomorphism is a partial homeomorphism `e` with `Φ = ⇑e` and `c ∈ e.source`; then
  `e '' (e.source ∩ U)` is open, contains `Φ c` and lies in `Φ '' U`;
* `Work.NAKANE.mem_image_Phi_of_localHomeo_of_one_lt` : **(R1) alone** — `Φ '' Mbᶜ` is *surjective*
  onto `extDisc`.  Its image is open in `ℂ` and its preimage in the subspace `↥extDisc` is also
  closed there (`Work.NAKANE.PhiClosed.mem_image_Phi_of_mem_closure`), hence clopen; `extDisc` is
  preconnected (`Work.ParamRays.isPreconnected_lt_norm`), so the image is everything;
* `Work.NAKANE.phiExt`, its continuity, the bijectivity from (R1)+(R2), and the open-map property
  from (R1);
* `Work.NAKANE.nakaneHomeo_of_localHomeo_of_injOn` : (R1) + (R2) ⟹ `Work.ParamRays.NakaneHomeo`.

The assembly is proved from the **weaker** input `∀ U ⊆ Mbᶜ, IsOpen U → IsOpen (Φ '' U)` together
with (R2): `Work.NAKANE.nakaneHomeo_of_openMap_of_injOn`.  (This is genuinely weaker than (R1): it
is what a proof of the real-analyticity of `c ↦ Φ c` with nonvanishing Jacobian would give, and it
can also be discharged from a holomorphy-plus-`Φ' ≠ 0` statement.)  The (R1)-versions are recorded
as corollaries.

Note that (R1) is *not* a consequence of the continuity of `Φ` alone, and (R2) is Nakane's
injectivity theorem; both are recorded as named propositions (see `Work.NAKANE.Defs`).
-/
import Submission.Work.NAKANE.PotentialTop
import Submission.Work.NAKANE.PhiClosed.mem_image_Phi_of_mem_closure

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology ComplexConjugate

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.NAKANE

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Elementary facts -/

/-- `Mb` is compact, hence closed. -/
theorem isClosed_Mb : IsClosed Mb := Work.ParamRays.isClosed_mandelbar

/-- The exterior of the mandelbar is open. -/
theorem isOpen_compl_Mb : IsOpen Mbᶜ := isClosed_Mb.isOpen_compl

/-- The mandelbar is contained in the closed ball of radius `2`. -/
theorem notMem_Mb_of_two_lt {c : ℂ} (hc : 2 < ‖c‖) : c ∉ Mb := by
  intro h
  have h1 := Work.ParamRays.mandelbar_subset_closedBall h
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  linarith

/-- The parameter Böttcher map sends the exterior of the mandelbar into the exterior disc. -/
theorem one_lt_norm_Phi {c : ℂ} (hc : c ∉ Mb) : 1 < ‖Work.ParamRays.Phi c‖ :=
  Work.ParamRays.one_lt_norm_Phi Work.Bottcher.bottcherExists_crit hc

/-! ## (R1) `Φ` is an open map on `Mbᶜ` -/

/-- **(R1) gives the open-map property of `Φ` on the exterior of the mandelbar.** -/
theorem isOpen_image_Phi_of_localHomeo (hloc : PhiLocalHomeo) {U : Set ℂ}
    (hU : IsOpen U) (hUM : U ⊆ Mbᶜ) : IsOpen (Work.ParamRays.Phi '' U) := by
  choose e he using hloc
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨c, hcU, rfl⟩
  have hcMb : c ∈ Mbᶜ := hUM hcU
  obtain ⟨hcsrc, hfeq⟩ := he c hcMb
  have hWopen : IsOpen ((e c hcMb) '' ((e c hcMb).source ∩ U)) :=
    OpenPartialHomeomorph.isOpen_image_of_subset_source (e c hcMb)
      ((e c hcMb).open_source.inter hU) Set.inter_subset_left
  have hmem : Work.ParamRays.Phi c ∈ (e c hcMb) '' ((e c hcMb).source ∩ U) :=
    ⟨c, ⟨hcsrc, hcU⟩, congrFun hfeq.symm c⟩
  have hsub : (e c hcMb) '' ((e c hcMb).source ∩ U) ⊆ Work.ParamRays.Phi '' U := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨z, hz.2, congrFun hfeq z⟩
  exact Filter.mem_of_superset (hWopen.mem_nhds hmem) hsub

/-- **(R1) alone: the image of `Mbᶜ` is open in `ℂ`.** -/
theorem isOpen_image_Phi_of_localHomeo' (hloc : PhiLocalHomeo) :
    IsOpen (Work.ParamRays.Phi '' Mbᶜ) :=
  isOpen_image_Phi_of_localHomeo hloc isOpen_compl_Mb subset_rfl

/-! ## (R1) alone: `Φ` is surjective onto the exterior disc -/

/-- **If the image of `Mbᶜ` is open, then `Φ` maps `Mbᶜ` onto the exterior disc.**  The trace of
the image on the preconnected `extDisc` is open and closed there, hence the whole of `extDisc`. -/
theorem mem_image_Phi_of_isOpen_of_one_lt (hopen : IsOpen (Work.ParamRays.Phi '' Mbᶜ)) {w : ℂ}
    (hw : 1 < ‖w‖) : w ∈ Work.ParamRays.Phi '' Mbᶜ := by
  have hS : IsOpen (Work.ParamRays.Phi '' Mbᶜ) := hopen
  have hpre : IsPreconnected ({z : ℂ | 1 < ‖z‖}) :=
    Work.ParamRays.isPreconnected_lt_norm (M := 1) (by norm_num)
  haveI : PreconnectedSpace ↥{z : ℂ | 1 < ‖z‖} := isPreconnected_iff_preconnectedSpace.mp hpre
  have hS'open : IsOpen {y : ↥{z : ℂ | 1 < ‖z‖} | (y : ℂ) ∈ Work.ParamRays.Phi '' Mbᶜ} :=
    hS.preimage continuous_subtype_val
  have hS'closed : IsClosed {y : ↥{z : ℂ | 1 < ‖z‖} | (y : ℂ) ∈ Work.ParamRays.Phi '' Mbᶜ} := by
    have h : {y : ↥{z : ℂ | 1 < ‖z‖} | (y : ℂ) ∈ Work.ParamRays.Phi '' Mbᶜ}
        = Subtype.val ⁻¹' closure (Work.ParamRays.Phi '' Mbᶜ) := by
      ext y
      exact ⟨fun hy => subset_closure hy,
        fun hy => Work.NAKANE.PhiClosed.mem_image_Phi_of_mem_closure hy y.2⟩
    rw [h]
    exact isClosed_closure.preimage continuous_subtype_val
  have h3 : (3 : ℂ) ∉ Mb := notMem_Mb_of_two_lt (by norm_num)
  have hne : (Set.univ ∩
      {y : ↥{z : ℂ | 1 < ‖z‖} | (y : ℂ) ∈ Work.ParamRays.Phi '' Mbᶜ}).Nonempty :=
    ⟨⟨Work.ParamRays.Phi 3, one_lt_norm_Phi h3⟩, Set.mem_univ _, ⟨3, h3, rfl⟩⟩
  have hsub := (isPreconnected_univ : IsPreconnected
      (Set.univ : Set ↥{z : ℂ | 1 < ‖z‖})).subset_isClopen ⟨hS'closed, hS'open⟩ hne
  exact hsub (Set.mem_univ (⟨w, hw⟩ : ↥{z : ℂ | 1 < ‖z‖}))

/-- **(R1) alone: `Φ` maps `Mbᶜ` onto the exterior disc.** -/
theorem mem_image_Phi_of_localHomeo_of_one_lt (hloc : PhiLocalHomeo) {w : ℂ} (hw : 1 < ‖w‖) :
    w ∈ Work.ParamRays.Phi '' Mbᶜ :=
  mem_image_Phi_of_isOpen_of_one_lt (isOpen_image_Phi_of_localHomeo' hloc) hw

/-- **(R1) alone: `Φ` is surjective onto the exterior disc**, in existential form. -/
theorem Phi_surj_of_localHomeo (hloc : PhiLocalHomeo) {w : ℂ} (hw : 1 < ‖w‖) :
    ∃ c : ℂ, c ∉ Mb ∧ Work.ParamRays.Phi c = w :=
  mem_image_Phi_of_localHomeo_of_one_lt hloc hw

/-! ## The map `Mbᶜ → extDisc` and its properties -/

/-- The parameter Böttcher map as a map of the exterior of the mandelbar onto the exterior disc. -/
def phiExt (c : ↥Mbᶜ) : ↥extDisc := ⟨Work.ParamRays.Phi c, one_lt_norm_Phi c.2⟩

theorem phiExt_coe (c : ↥Mbᶜ) : (phiExt c : ℂ) = Work.ParamRays.Phi c := rfl

/-- `phiExt` is continuous (unconditionally: `Φ` is continuous on `Mbᶜ`). -/
theorem continuous_phiExt : Continuous phiExt :=
  (continuousOn_Phi.domRestrict).subtype_mk fun c => one_lt_norm_Phi c.2

/-- **If the image of `Mbᶜ` is open, then `phiExt` is surjective.** -/
theorem surjective_phiExt_of_isOpen (hopen : IsOpen (Work.ParamRays.Phi '' Mbᶜ)) :
    Function.Surjective phiExt := by
  intro y
  obtain ⟨c, hcMb, hcPhi⟩ := mem_image_Phi_of_isOpen_of_one_lt hopen y.2
  exact ⟨⟨c, hcMb⟩, Subtype.ext hcPhi⟩

/-- **(R1) alone: `phiExt` is surjective.** -/
theorem surjective_phiExt_of_localHomeo (hloc : PhiLocalHomeo) :
    Function.Surjective phiExt :=
  surjective_phiExt_of_isOpen (isOpen_image_Phi_of_localHomeo' hloc)

/-- **(R2): `phiExt` is injective.** -/
theorem injective_phiExt_of_injOn (hinj : PhiInjOn) : Function.Injective phiExt := by
  intro x y hxy
  have h1 : Work.ParamRays.Phi (x : ℂ) = Work.ParamRays.Phi (y : ℂ) :=
    congrArg (fun z : ↥extDisc => (z : ℂ)) hxy
  exact Subtype.ext (hinj x.2 y.2 h1)

/-- **If `Φ` is an open map on the exterior of the mandelbar, then `phiExt` is an open map.** -/
theorem isOpenMap_phiExt_of_openOn
    (hopen : ∀ U : Set ℂ, U ⊆ Mbᶜ → IsOpen U → IsOpen (Work.ParamRays.Phi '' U)) :
    IsOpenMap phiExt := by
  intro U hU
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp hU
  refine isOpen_induced_iff.mpr ⟨Work.ParamRays.Phi '' (V ∩ Mbᶜ), ?_, ?_⟩
  · exact hopen (V ∩ Mbᶜ) Set.inter_subset_right (hV.inter isOpen_compl_Mb)
  · ext w
    constructor
    · rintro ⟨c, hcVU, hcw⟩
      refine ⟨⟨c, hcVU.2⟩, ?_, ?_⟩
      · exact hVU.symm ▸ hcVU.1
      · exact Subtype.ext hcw
    · rintro ⟨x, hxU, hxw⟩
      refine ⟨(x : ℂ), ⟨?_, x.2⟩, ?_⟩
      · exact Set.mem_preimage.mp (hVU.symm ▸ hxU)
      · exact congrArg Subtype.val hxw

/-- **(R1) alone: `phiExt` is an open map.** -/
theorem isOpenMap_phiExt (hloc : PhiLocalHomeo) : IsOpenMap phiExt :=
  isOpenMap_phiExt_of_openOn fun U hUM hU => isOpen_image_Phi_of_localHomeo hloc hU hUM

/-! ## Nakane's homeomorphism theorem -/

/-- **Nakane's homeomorphism theorem from openness and injectivity.**  If `Φ` is an open map on
the exterior of the mandelbar and injective there, then `Φ` is a homeomorphism of `Mbᶜ` onto
`{w : ℂ | 1 < ‖w‖}`.

(Note that openness on `Mbᶜ` is *strictly* weaker than (R1): `Φ` real-analytic with nonvanishing
Jacobian gives it, but so does any other route to the open-map property.  Injectivity on `Mbᶜ` is
Nakane's injectivity theorem.) -/
theorem nakaneHomeo_of_openMap_of_injOn
    (hopen : ∀ U : Set ℂ, U ⊆ Mbᶜ → IsOpen U → IsOpen (Work.ParamRays.Phi '' U))
    (hinj : PhiInjOn) : Work.ParamRays.NakaneHomeo :=
  ⟨Equiv.toHomeomorphOfContinuousOpen
      (Equiv.ofBijective phiExt
        ⟨injective_phiExt_of_injOn hinj,
          surjective_phiExt_of_isOpen (hopen Mbᶜ subset_rfl isOpen_compl_Mb)⟩)
      continuous_phiExt (isOpenMap_phiExt_of_openOn hopen),
    fun _ => rfl⟩

/-- **Nakane's homeomorphism theorem from its two classical inputs.**  If `Φ` is a local
homeomorphism on the exterior of the mandelbar (R1, Nakane 1993) and injective there (R2, Nakane's
injectivity theorem), then `Φ` is a homeomorphism of `Mbᶜ` onto `{w : ℂ | 1 < ‖w‖}`, in exactly
the form `Work.ParamRays.NakaneHomeo` consumed by `Work.Final.nakane_of_homeo_asymptotic`. -/
theorem nakaneHomeo_of_localHomeo_of_injOn (hloc : PhiLocalHomeo) (hinj : PhiInjOn) :
    Work.ParamRays.NakaneHomeo :=
  nakaneHomeo_of_openMap_of_injOn
    (fun U hUM hU => isOpen_image_Phi_of_localHomeo hloc hU hUM) hinj

end Work.NAKANE
