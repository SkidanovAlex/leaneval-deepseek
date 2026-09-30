/-
# Openness of the junction coordinate inclusion `jCoordM`

The *junction chart* of the `v`-th filling piece has the box
`Work.RTOwed.jBox v cU k W kx δ` in the polar coordinates `q = (r,θ,w₁,w₂)` and the coordinate
inclusion `Work.RTOwed.jCoordM a v D cU k W kx δ`, which is

* the inverse of the polar chart (`incW v ∘ cuspInvInner`) for `r ≤ rJ`, and
* the collar coordinate inclusion (`cuspCoordMTop ∘ polarToUHS`) for `rJ < r`.

This file proves that it is an **open map**.

The boundary `r = rJ` is the only place where the two formulas genuinely differ (they agree *at* the
junction by `Work.RTOwed.cuspInvOuter_polarToUHS_eq`, and for `r > rJ` below the radius
`jTop = R₀ − log β_max` the collar branch of `cuspCoordMTop` is the `incW`-branch and
`cuspInvOuter ∘ polarToUHS = cuspInvInner`, so the two branches coincide there as well).  Hence the
box is covered by the two open pieces

* `{q 0 < jTop}`, on which `jCoordM` is the polar coordinate inclusion
  `incW v ∘ fillProj ∘ (cuspInvInner, ·)` — the restriction of the polar chart to the open set
  `jPolarDom = jTarget ∩ {q 0 < jTop}`, an open embedding because `cuspInvInner` is the inverse of
  the polar chart on `jTarget = polarTargetS v cU k (polarBox ∩ {w ∈ W})`;
* `{rJ < q 0}`, on which `jCoordM` is `cuspCoordMTop ∘ polarToUHS`, the composite of two open
  embeddings (`polarToUHS` is an open embedding and `cuspCoordMTop` is one on its box);

and a map which is open on each member of an open cover is open
(`isOpenMap_of_forall_exists_open_nhds`).
-/
import Mathlib
import Submission.Work.RTOwed.FillBigDefs
import Submission.Work.RTOwed.polarToUHS_isOpenEmbedding
import Submission.Work.RTOwed.cuspInvOuter_polarToUHS_eq
import Submission.Work.Cusp.isOpenEmbedding_cuspCoordMTop
import Submission.Work.Cusp.isOpenMap_fillProj
import Submission.Work.Cusp.isOpenEmbedding_incW_interior
import Submission.Work.Cusp.isOpen_polarTargetS
import Submission.Work.Cusp.isOpen_polarBox
import Submission.Work.Cusp.isOpen_cuspBoxTop
import Submission.Work.Cusp.MChartAux
import Submission.Work.Cusp.exists_polarChartS
import Submission.Work.Cusp.cuspInvInner_nrm
import Submission.Work.Cusp.cuspInvInner_nrm_gt
import Submission.Work.Cusp.cuspInvInner_ThetaPolarS
import Submission.Work.Cusp.ThetaPolarS_cuspInvInner
import Submission.Work.Cusp.cuspInvOuter_mem_SqTop
import Submission.Work.Cusp.cuspInvOuter_nrm_eq_one_ceilingTop
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.TopWindow
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.abs_le_nrm
import Submission.Work.RTOwed.jBox_isOpen

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.RTOWed

open Work.Cusp
open Work.RTOwed
open Set.Notation

/-! ### A localization lemma for open maps -/

/-- **Openness is local on an open cover of the source.**  If every `x : X` has an open neighbourhood
`N x` on which `f` is an open map, then `f` is an open map. -/
lemma isOpenMap_of_forall_exists_open_nhds {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (h : ∀ x : X, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ IsOpenMap (N.domRestrict f)) :
    IsOpenMap f := by
  classical
  choose N hNo hxN hmap using h
  intro A hA
  have hcover : A = ⋃ x, A ∩ N x := by
    ext y; constructor
    · intro hy; exact mem_iUnion.mpr ⟨y, hy, hxN y⟩
    · intro hy; rcases mem_iUnion.mp hy with ⟨x, hyx⟩; exact hyx.1
  rw [hcover, image_iUnion]
  apply isOpen_iUnion
  intro x
  have hUN : IsOpen (A ∩ N x) := hA.inter (hNo x)
  have himg : f '' (A ∩ N x)
      = (N x).domRestrict f '' ((Subtype.val) ⁻¹' (A ∩ N x)) := by
    ext y; constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz.2⟩, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.1, hz, rfl⟩
  rw [himg]
  exact hmap x _ (hUN.preimage continuous_subtype_val)

/-! ### The two radii delimiting the polar piece -/

/-- **The top of the collar window, in radii**: `jTop = R₀ − log β_max` is the radius at which the
UHS height `e^{R₀−r}` equals the largest possible ceiling `β_max`.  For `q 0 < jTop` a point of the
box lies strictly above every ceiling, so `cuspCoordMTop` uses the `incW`-branch there. -/
def jTop : ℝ := R0 - Real.log betaMax

/-- `β_max = 3/2 > 0`. -/
lemma betaMax_pos : (0 : ℝ) < betaMax := by norm_num [betaMax]

/-- `R₀ − log β_max > r_J`: the collar window `(r_J, jTop)` is nonempty. -/
lemma rJ_lt_jTop : rJ < jTop := by
  have hlog : Real.log betaMax < 1 / 2 := by
    have h := Real.log_lt_log (by norm_num [betaMax]) (betaMax_lt_sJ)
    rw [sJ, Real.log_exp] at h
    exact h
  simp only [jTop, R0, rJ]
  linarith

/-! ### The polar target of a junction chart -/

/-- The polar chart box of a junction chart: `polarBox ∩ {w ∈ W}`. -/
def jBase (W : Set E2) : Set E4 := polarBox ∩ {q : E4 | (!₂[q 2, q 3] : E2) ∈ W}

/-- The polar target box of a junction chart (the target of the shifted polar chart with box
`jBase W`). -/
def jTarget (v : Work.Space.Cusp) (cU : ℝ) (k : Fin 4) (W : Set E2) : Set E4 :=
  polarTargetS v cU k (jBase W)

/-- The part of the polar target on which the polar coordinates lie below the collar window top:
this is an open set containing the junction `q 0 = rJ` on which `jCoordM` is the polar inclusion. -/
def jPolarDom (v : Work.Space.Cusp) (cU : ℝ) (k : Fin 4) (W : Set E2) : Set E4 :=
  jTarget v cU k W ∩ {q : E4 | q 0 < jTop}

/-- The preimage under `polarToUHS v` of the collar box: the source of the collar branch. -/
def jCollarDom (v : Work.Space.Cusp) (kx : E3) (δ : ℝ) : Set E4 :=
  {q : E4 | polarToUHS v q ∈ cuspBoxTop v kx δ}

lemma jBase_subset_polarBox (W : Set E2) : jBase W ⊆ polarBox := fun _ h => h.1

lemma isOpen_jBase {W : Set E2} (hW : IsOpen W) : IsOpen (jBase W) := by
  have h : IsOpen {q : E4 | (!₂[q 2, q 3] : E2) ∈ W} := hW.preimage (by fun_prop)
  exact isOpen_polarBox.inter h

lemma isOpen_jTarget (v : Work.Space.Cusp) (cU : ℝ) (k : Fin 4) {W : Set E2} (hW : IsOpen W) :
    IsOpen (jTarget v cU k W) :=
  isOpen_polarTargetS v cU k (jBase W) (isOpen_jBase hW)

lemma isOpen_jPolarDom (v : Work.Space.Cusp) (cU : ℝ) (k : Fin 4) {W : Set E2} (hW : IsOpen W) :
    IsOpen (jPolarDom v cU k W) := by
  have h : IsOpen {q : E4 | q 0 < jTop} :=
    isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0) continuous_const
  exact (isOpen_jTarget v cU k hW).inter h

lemma isOpen_jCollarDom (v : Work.Space.Cusp) (kx : E3) (δ : ℝ) :
    IsOpen (jCollarDom v kx δ) :=
  (isOpen_cuspBoxTop v kx δ).preimage (polarToUHS_isOpenEmbedding v).continuous

/-- **A point of the polar box below `jTop` has recovered layer parameter `< 1`**: on the inner
branch it is `q 0/(2 r_J) ≤ 1/2`, and on the collar branch the UHS height `e^{R₀−q 0}` is strictly
above every ceiling `β ≤ β_max`, so the collar formula `1 − A/(2J)` is strictly between `0` and
`1`. -/
lemma nrm_cuspInvInner_lt_one (v : Work.Space.Cusp) {q : E4} (hq : q ∈ polarBox)
    (h : q 0 < jTop) : nrm (cuspInvInner v q).1 < 1 := by
  by_cases hle : q 0 ≤ rJ
  · rw [cuspInvInner_nrm v q hq hle]
    have h0 : (0 : ℝ) < 2 * rJ := by norm_num [rJ]
    rw [div_lt_one h0]
    simp only [rJ] at hle ⊢
    linarith
  · have hgt : rJ < q 0 := lt_of_not_ge hle
    have heq : cuspInvOuter v (polarToUHS v q) = cuspInvInner v q :=
      cuspInvOuter_polarToUHS_eq v (le_of_lt hgt)
    rw [← heq]
    set x : E4 := polarToUHS v q with hx
    have hx3 : x 3 = Real.exp (R0 - q 0) := rfl
    -- the point lies strictly above every ceiling, hence in the unslabbed collar source
    have hbpos : (0 : ℝ) < beta (xOf x) := beta_pos _
    have hble : beta (xOf x) ≤ betaMax := beta_le_max _
    have hgtmax : betaMax < Real.exp (R0 - q 0) := by
      have h1 : Real.log betaMax < R0 - q 0 := by
        simp only [jTop] at h; linarith
      calc betaMax = Real.exp (Real.log betaMax) := (Real.exp_log betaMax_pos).symm
        _ < Real.exp (R0 - q 0) := Real.exp_lt_exp.mpr h1
    have hs1 : s1 < x 3 := by
      rw [hx3]
      exact lt_trans (by norm_num [s1, betaMax]) hgtmax
    have hltTop : x 3 < sTop := by
      rw [hx3]
      calc Real.exp (R0 - q 0) < Real.exp (R0 - rJ) := Real.exp_lt_exp.mpr (by linarith)
        _ = sJ := by simp only [sJ, R0, rJ]; norm_num
        _ < sTop := sJ_lt_sTop
    have hsrc : x ∈ cuspSourceTop v (xOf x) 1 :=
      ⟨⟨fun i => by simp, hs1, hltTop⟩, by rw [hx3]; exact le_of_lt (lt_of_le_of_lt hble hgtmax)⟩
    have hle1 : nrm (cuspInvOuter v x).1 ≤ 1 := (cuspInvOuter_nrm_Top v (xOf x) 1 x hsrc).2
    rcases lt_or_eq_of_le hle1 with h1 | h1
    · exact h1
    · exfalso
      have hceil := cuspInvOuter_nrm_eq_one_ceilingTop v (xOf x) 1 x hsrc h1
      have h2 : Real.exp (R0 - q 0) ≤ betaMax := by
        rw [← hx3, hceil]; exact hble
      have h3 : R0 - q 0 ≤ Real.log betaMax := by
        exact (Real.le_log_iff_exp_le betaMax_pos).mpr h2
      simp only [jTop] at h
      linarith


/-! ### The junction box lies in the polar target -/

/-- Every point of the junction box lies in the polar target `jTarget v cU k W`. -/
lemma jBox_subset_jTarget (v : Work.Space.Cusp) (cU : ℝ) (k : Fin 4) (W : Set E2)
    (kx : E3) (δ : ℝ) : jBox v cU k W kx δ ⊆ jTarget v cU k W := by
  intro q hq
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hq
  refine ⟨⟨⟨h1, ?_⟩, h3⟩, h4, h5⟩
  simp only [rBig] at h2
  simp only [rJ]
  linarith

/-- **`cuspInvInner` is an open map on the polar target of a junction chart.**  It is the inverse of
the shifted polar chart `ThetaPolarS`, which is an `OpenPartialHomeomorph` with source
`polarSourceS` and target `polarTargetS` (`Work.Cusp.exists_polarChartS`); its inverse is an open
embedding of the target (`OpenPartialHomeomorph.isOpenEmbedding_restrict`). -/
lemma isOpenMap_cuspInvInner_jTarget (v : Work.Space.Cusp) (cU : ℝ) (k : Fin 4) (W : Set E2)
    (hW : IsOpen W) :
    IsOpenMap (fun q : {q : E4 // q ∈ jTarget v cU k W} => cuspInvInner v q.1) := by
  obtain ⟨Φ, _hsrc, htgt, hval⟩ :=
    exists_polarChartS v cU k (jBase W) (isOpen_jBase hW) (jBase_subset_polarBox W)
  have hemb : IsOpenEmbedding (Φ.symm.source.domRestrict Φ.symm) := Φ.symm.isOpenEmbedding_restrict
  rw [show Φ.symm.source = jTarget v cU k W from Φ.symm_source.trans htgt] at hemb
  have hfun : (fun q : {q : E4 // q ∈ jTarget v cU k W} => Φ.symm q.1)
      = (fun q : {q : E4 // q ∈ jTarget v cU k W} => cuspInvInner v q.1) := by
    funext q
    have hinj : Function.Injective (fun z : E2 × E2 => ThetaPolarS v cU z.1 z.2) := by
      intro z z' h
      have h2 := congrArg (cuspInvInner v) h
      rwa [cuspInvInner_ThetaPolarS, cuspInvInner_ThetaPolarS] at h2
    have hx : q.1 ∈ Φ.target := by rw [htgt]; exact q.2
    have hright : Φ (Φ.symm q.1) = q.1 := Φ.right_inv hx
    have h1 : ThetaPolarS v cU (Φ.symm q.1).1 (Φ.symm q.1).2 = q.1 := by
      rw [← hval (Φ.symm q.1), hright]
    have h2 : ThetaPolarS v cU (cuspInvInner v q.1).1 (cuspInvInner v q.1).2 = q.1 :=
      ThetaPolarS_cuspInvInner v cU q.1 (jBase_subset_polarBox W q.2.1) q.2.2.1
    exact hinj (h1.trans h2.symm)
  have h2 : IsOpenMap (fun q : {q : E4 // q ∈ jTarget v cU k W} => Φ.symm q.1) :=
    hemb.isOpenMap
  rw [hfun] at h2
  exact h2

/-! ### The two branches of `jCoordM`, as maps out of the open pieces -/

/-- The polar coordinate inclusion on `jPolarDom`: `q ↦ incW v (fillProj (cuspInvInner v q))`. -/
noncomputable def jPolarInc (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : Work.Cusp.CuspGlueData a v) (cU : ℝ) (k : Fin 4) (W : Set E2)
    (q : {q : E4 // q ∈ jPolarDom v cU k W}) : a.Mhat :=
  a.incW v (fillProj a v D.tor
    ⟨cuspInvInner v q.1, nrm_cuspInvInner_lt_one v (jBase_subset_polarBox W q.2.1.1) q.2.2⟩)

/-- The collar coordinate inclusion on `jCollarDom`. -/
noncomputable def jCollarInc (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : Work.Cusp.CuspGlueData a v) (kx : E3) (δ : ℝ)
    (q : {q : E4 // q ∈ jCollarDom v kx δ}) : a.Mhat :=
  cuspCoordMTop a v D kx δ ⟨polarToUHS v q.1, q.2⟩

lemma jPolarDom_subset_jTarget (v : Work.Space.Cusp) (cU : ℝ) (k : Fin 4) (W : Set E2) :
    jPolarDom v cU k W ⊆ jTarget v cU k W := fun _ h => h.1

/-- **The polar inclusion is an open map**: it is the composite of the open embedding
`incW v` on the interior of the filling piece, the open projection `fillProj`, and the inverse polar
chart `cuspInvInner` on the open set `jPolarDom` (a restriction of `isOpenMap_cuspInvInner_jTarget`
to an open subset). -/
lemma isOpenMap_jPolarInc (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : Work.Cusp.CuspGlueData a v) (cU : ℝ) (k : Fin 4) (W : Set E2) (hW : IsOpen W) :
    IsOpenMap (jPolarInc a v D cU k W) := by
  have hrel : IsOpen (jTarget v cU k W ↓∩ jPolarDom v cU k W) := by
    have heq : (jTarget v cU k W ↓∩ jPolarDom v cU k W)
        = {x : {q : E4 // q ∈ jTarget v cU k W} | x.1 0 < jTop} := by
      ext x
      simp only [Set.mem_preimage, jPolarDom, Set.mem_inter_iff, Set.mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [heq]
    exact isOpen_Iio.preimage
      ((PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0).comp continuous_subtype_val)
  have hincl : IsOpenEmbedding (Set.inclusion (jPolarDom_subset_jTarget v cU k W)) :=
    Topology.IsOpenEmbedding.inclusion _ hrel
  have hcii : IsOpenMap (fun z : {q : E4 // q ∈ jPolarDom v cU k W} => cuspInvInner v z.1) :=
    (isOpenMap_cuspInvInner_jTarget v cU k W hW).comp hincl.isOpenMap
  let S : {q : E4 // q ∈ jPolarDom v cU k W} → {w : E2 × E2 // nrm w.1 < 1} :=
    fun z => ⟨cuspInvInner v z.1,
      nrm_cuspInvInner_lt_one v (jBase_subset_polarBox W z.2.1.1) z.2.2⟩
  have hS : IsOpenMap S := IsOpenMap.subtype_mk hcii _
  let P : {w : E2 × E2 // nrm w.1 < 1} → (fillInterior a v) :=
    fun z => ⟨fillProj a v D.tor z, z.2⟩
  have hP : IsOpenMap P := IsOpenMap.codRestrict (isOpenMap_fillProj a v D.tor) (fun z => z.2)
  let J : (fillInterior a v) → a.Mhat := fun p => a.incW v p.1
  have hJ : IsOpenMap J := (isOpenEmbedding_incW_interior a v).isOpenMap
  have hcomp : jPolarInc a v D cU k W = J ∘ P ∘ S := rfl
  rw [hcomp]
  exact hJ.comp (hP.comp hS)

/-- **The collar inclusion is an open map**: `cuspCoordMTop` is an open embedding of its box
(`Work.Cusp.isOpenEmbedding_cuspCoordMTop`) and `polarToUHS` is an open embedding. -/
lemma isOpenMap_jCollarInc (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : Work.Cusp.CuspGlueData a v) (kx : E3) (δ : ℝ) (hδ : δ ≤ 1/2) :
    IsOpenMap (jCollarInc a v D kx δ) := by
  let g : {q : E4 // q ∈ jCollarDom v kx δ} → {z : E4 // z ∈ cuspBoxTop v kx δ} :=
    fun q => ⟨polarToUHS v q.1, q.2⟩
  have h1 : IsOpenMap g :=
    IsOpenMap.subtype_map (polarToUHS_isOpenEmbedding v).isOpenMap (isOpen_jCollarDom v kx δ)
      (fun q hq => hq)
  have h2 : jCollarInc a v D kx δ = (cuspCoordMTop a v D kx δ) ∘ g := rfl
  rw [h2]
  exact (isOpenEmbedding_cuspCoordMTop a v D kx δ hδ).isOpenMap.comp h1

/-! ### `jCoordM` on the two open pieces -/

/-- A point of the junction box with `rJ < q 0` lies in the collar source. -/
lemma jBox_mem_jCollarDom (v : Work.Space.Cusp) {cU : ℝ} {k : Fin 4} {W : Set E2} {kx : E3}
    {δ : ℝ} (q : {q : E4 // q ∈ jBox v cU k W kx δ}) (hgt : rJ < q.1 0) :
    q.1 ∈ jCollarDom v kx δ := by
  obtain ⟨-, hub, -, -, -, hbox⟩ := q.2
  exact polarToUHS_mem_cuspBoxTop v kx δ hbox hgt hub

/-- **Below `jTop` the junction coordinate inclusion is the polar inclusion.**  For `q 0 ≤ rJ` this
is the definition of `jCoordM`; for `rJ < q 0 < jTop` the UHS height `e^{R₀−q 0}` is strictly above
every ceiling, so `cuspCoordMTop` uses its `incW`-branch and `cuspInvOuter ∘ polarToUHS` is
`cuspInvInner`. -/
lemma jCoordM_eq_jPolarInc (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : Work.Cusp.CuspGlueData a v) (cU : ℝ) (k : Fin 4) (W : Set E2) (kx : E3) (δ : ℝ)
    (q : {q : E4 // q ∈ jBox v cU k W kx δ}) (hq : q.1 0 < jTop) :
    jCoordM a v D cU k W kx δ q
      = jPolarInc a v D cU k W ⟨q.1, ⟨jBox_subset_jTarget v cU k W kx δ q.2, hq⟩⟩ := by
  by_cases hle : q.1 0 ≤ rJ
  · unfold jCoordM jPolarInc
    rw [dif_pos hle]
    refine congrArg (a.incW v) (Prod.ext (Subtype.ext rfl) rfl)
  · have hgt : rJ < q.1 0 := lt_of_not_ge hle
    have hH : ¬((polarToUHS v q.1) 3 < beta (xOf (polarToUHS v q.1))) := by
      have hb : beta (xOf (polarToUHS v q.1)) ≤ betaMax := beta_le_max _
      have hexp : betaMax < Real.exp (R0 - q.1 0) := by
        have h1 : Real.log betaMax < R0 - q.1 0 := by
          simp only [jTop] at hq; linarith
        calc betaMax = Real.exp (Real.log betaMax) := (Real.exp_log betaMax_pos).symm
          _ < Real.exp (R0 - q.1 0) := Real.exp_lt_exp.mpr h1
      rw [show (polarToUHS v q.1) 3 = Real.exp (R0 - q.1 0) from rfl]
      exact not_lt.mpr (le_of_lt (lt_of_le_of_lt hb hexp))
    have hci : cuspInvOuter v (polarToUHS v q.1) = cuspInvInner v q.1 :=
      cuspInvOuter_polarToUHS_eq v (le_of_lt hgt)
    unfold jCoordM jPolarInc
    rw [dif_neg hle]
    unfold cuspCoordMTop
    rw [dif_neg hH]
    refine congrArg (a.incW v) (Prod.ext ?_ ?_)
    · exact Subtype.ext (congrArg Prod.fst hci)
    · exact congrArg (fun z : E2 => D.tor.symm (fun i => (((z i : ℝ)) : AddCircle (1 : ℝ))))
        (congrArg Prod.snd hci)

/-- **Above `rJ` the junction coordinate inclusion is the collar inclusion.**  Here `cuspCoordMTop`
is applied to `polarToUHS v q` (with the box membership provided by `jBox_mem_jCollarDom`), which is
exactly the `else`-branch defining `jCoordM`. -/
lemma jCoordM_eq_jCollarInc (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : Work.Cusp.CuspGlueData a v) (cU : ℝ) (k : Fin 4) (W : Set E2) (kx : E3) (δ : ℝ)
    (q : {q : E4 // q ∈ jBox v cU k W kx δ}) (hgt : rJ < q.1 0) :
    jCoordM a v D cU k W kx δ q
      = jCollarInc a v D kx δ ⟨q.1, jBox_mem_jCollarDom v q hgt⟩ := by
  unfold jCoordM jCollarInc
  rw [dif_neg (not_le.mpr hgt)]

/-! ### The theorem -/

theorem jCoordM_isOpenMap (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : Work.Cusp.CuspGlueData a v) (cU : ℝ) (k : Fin 4) (W : Set Work.Cusp.E2)
    (kx : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    IsOpenMap (Work.RTOwed.jCoordM a v D cU k W kx δ) := by
  apply isOpenMap_of_forall_exists_open_nhds
  intro x
  have hcontval : Continuous (fun q : {q : E4 // q ∈ jBox v cU k W kx δ} => q.1 0) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0).comp continuous_subtype_val
  have hval : IsOpenMap ((Subtype.val) : {q : E4 // q ∈ jBox v cU k W kx δ} → E4) :=
    IsOpen.isOpenMap_subtype_val (jBox_isOpen v cU k W kx δ hW)
  by_cases hx : x.1 0 < jTop
  · let N : Set {q : E4 // q ∈ jBox v cU k W kx δ} := {q | q.1 0 < jTop}
    have hN : IsOpen N := isOpen_Iio.preimage hcontval
    let ii : N → {z : E4 // z ∈ jPolarDom v cU k W} :=
      Subtype.map (Subtype.val : {q : E4 // q ∈ jBox v cU k W kx δ} → E4)
        (fun q hq => (⟨jBox_subset_jTarget v cU k W kx δ q.2, hq⟩ : q.1 ∈ jPolarDom v cU k W))
    have hii : IsOpenMap ii :=
      IsOpenMap.subtype_map (f := (Subtype.val : {q : E4 // q ∈ jBox v cU k W kx δ} → E4))
        (s := N) (t := jPolarDom v cU k W) hval hN
        (fun q hq => (⟨jBox_subset_jTarget v cU k W kx δ q.2, hq⟩ : q.1 ∈ jPolarDom v cU k W))
    have heq : N.domRestrict (jCoordM a v D cU k W kx δ) = (jPolarInc a v D cU k W) ∘ ii := by
      funext q
      exact jCoordM_eq_jPolarInc a v D cU k W kx δ q.1 q.2
    refine ⟨N, hN, hx, ?_⟩
    rw [heq]
    exact (isOpenMap_jPolarInc a v D cU k W hW).comp hii
  · have hx2 : rJ < x.1 0 := lt_of_lt_of_le rJ_lt_jTop (not_lt.mp hx)
    let N : Set {q : E4 // q ∈ jBox v cU k W kx δ} := {q | rJ < q.1 0}
    have hN : IsOpen N := isOpen_Ioi.preimage hcontval
    let ii : N → {z : E4 // z ∈ jCollarDom v kx δ} :=
      Subtype.map (Subtype.val : {q : E4 // q ∈ jBox v cU k W kx δ} → E4)
        (fun q hq => jBox_mem_jCollarDom v q hq)
    have hii : IsOpenMap ii :=
      IsOpenMap.subtype_map (f := (Subtype.val : {q : E4 // q ∈ jBox v cU k W kx δ} → E4))
        (s := N) (t := jCollarDom v kx δ) hval hN (fun q hq => jBox_mem_jCollarDom v q hq)
    have heq : N.domRestrict (jCoordM a v D cU k W kx δ) = (jCollarInc a v D kx δ) ∘ ii := by
      funext q
      exact jCoordM_eq_jCollarInc a v D cU k W kx δ q.1 q.2
    refine ⟨N, hN, hx2, ?_⟩
    rw [heq]
    exact (isOpenMap_jCollarInc a v D kx δ hδ).comp hii

end Work.RTOWed
