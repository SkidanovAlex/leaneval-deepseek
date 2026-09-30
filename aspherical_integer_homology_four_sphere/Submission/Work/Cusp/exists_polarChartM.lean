/-
# The polar chart of the filling piece, as an open partial homeomorphism of `M̂`

The `(c,k)`-th polar chart of the `v`-th cusp is the open partial homeomorphism of `M̂` whose
underlying map is the *coordinate inclusion*
`polarCoordM a v tor c k W : polarBoxSect v c k W → M̂`,
the point of the filling piece obtained by inverting the shifted polar chart `ThetaPolarS`
(`Work.Cusp.exists_polarChartS`).

Everything the statement needs is now available:

* `isOpen_polarBoxSect`: the chart box `polarBoxSect v c k W` is open.  It is
  `{q | q ∈ polarBox ∧ wOf-image ∈ W ∧ q 0 < rJ} ∩ polarTargetS v c k univ`; the second factor is
  open by `isOpen_polarTargetS` (the half-open conditions `uqOf v q - c ∈ [0,1)` and the
  fractional-part condition together *are* the open condition `uqOf v q - c ∈ (k/4,(k+1)/4)`).
* `isOpenEmbedding_polarCoordM_aux`: `polarCoordM` is an open embedding.  Its continuity is the
  continuity of `incW v`, of `cuspInvInner` and of the torus reduction; its injectivity is the
  hypothesis `hsec` on the `w`-box `W` (which pins the lift `y` modulo `ℤ²`) together with the
  injectivity of `cuspInvInner` on the box; and it is an *open* map because it factors as

  `incW v ∘ fillProj ∘ cuspInvInner`,

  where `cuspInvInner` is an open embedding (`isOpenEmbedding_cuspInvInner_polarBoxSect`, obtained
  from the chart `exists_polarChartS`), `fillProj` is the projection of the cover of the filling
  piece onto it and is open (`isOpenMap_fillProj`, the "wedge of the covering map"), and finally
  the inclusion of the *interior* of the filling piece is an open embedding
  (`isOpenEmbedding_incW_interior`: the chart lands in `‖p‖∞ < 1/2`, strictly inside the filling
  piece, so the gluing on the boundary `‖p‖∞ = 1` is never met).

The partial homeomorphism itself is then `lift_openEmbedding`: the identity chart of the box
`polarBoxSect v c k W`, transported along the open embedding `polarCoordM`.  Its source is
`polarCoordM '' univ`, its target is the box, and on the box it inverts `polarCoordM` by
`OpenPartialHomeomorph.lift_openEmbedding_apply`.  The empty box (which occurs exactly when no lift
`wOf v y ∈ W` exists) is treated separately by the empty partial homeomorphism.
-/
import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.MChartAux
import Submission.Work.Cusp.ThetaPolarS_cuspInvInner
import Submission.Work.Cusp.isOpenEmbedding_cuspInvInner_polarBoxSect
import Submission.Work.Cusp.isOpenEmbedding_incW_interior
import Submission.Work.Cusp.isOpenMap_fillProj
import Submission.Work.Cusp.isOpen_polarBox
import Submission.Work.Cusp.isOpen_polarTargetS
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.nrm_smul

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology
open scoped Real InnerProductSpace

namespace Work.Cusp

/-- **The chart box `polarBoxSect v c k W` is open.**  It is the intersection of the open set
`{q | q ∈ polarBox ∧ w q ∈ W ∧ q 0 < rJ}` with `polarTargetS v c k univ`, which is open by
`isOpen_polarTargetS`: the half-open condition `uqOf v q - c ∈ [0,1)` together with the
fractional-part condition is exactly the open condition `uqOf v q - c ∈ (k/4,(k+1)/4)`. -/
private theorem isOpen_polarBoxSect (v : Fin 5) (c : ℝ) (k : Fin 4) (W : Set E2) (hW : IsOpen W) :
    IsOpen (polarBoxSect v c k W) := by
  have hP : IsOpen {q : E4 | q ∈ polarBox ∧ (!₂[q 2, q 3] : E2) ∈ W ∧ q 0 < rJ} := by
    have h1 : IsOpen (polarBox ∩ (fun q : E4 => (!₂[q 2, q 3] : E2)) ⁻¹' W) :=
      isOpen_polarBox.inter (hW.preimage (by fun_prop))
    have h2 : IsOpen {q : E4 | q 0 < rJ} :=
      isOpen_lt (by fun_prop : Continuous fun q : E4 => q 0) continuous_const
    have h3 : {q : E4 | q ∈ polarBox ∧ (!₂[q 2, q 3] : E2) ∈ W ∧ q 0 < rJ}
        = polarBox ∩ (fun q : E4 => (!₂[q 2, q 3] : E2)) ⁻¹' W ∩ {q : E4 | q 0 < rJ} := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
      tauto
    rw [h3]
    exact h1.inter h2
  have hQ : IsOpen (polarTargetS v c k Set.univ) := isOpen_polarTargetS v c k _ isOpen_univ
  have hset : polarBoxSect v c k W
      = {q : E4 | q ∈ polarBox ∧ (!₂[q 2, q 3] : E2) ∈ W ∧ q 0 < rJ}
        ∩ polarTargetS v c k Set.univ := by
    ext q
    simp only [polarBoxSect, polarTargetS, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_univ,
      true_and]
    tauto
  rw [hset]
  exact hP.inter hQ

/-- **On the chart box `polarBoxSect` the recovered layer parameter is `< 1`** — indeed `< 1/2`,
because `q 0 < rJ` selects the inner branch `t = q 0/(2 rJ)` of `cuspInvInner` and
`nrm (bndOfU _) = 1`.  This is what makes the chart land in the *interior* of the filling piece. -/
private theorem nrm_cuspInvInner_lt_one_polarBoxSect (v : Fin 5) (c : ℝ) (k : Fin 4) (W : Set E2)
    (q : E4) (hq : q ∈ polarBoxSect v c k W) : nrm (cuspInvInner v q).1 < 1 := by
  have hbox : q ∈ polarBox := hq.1
  have hq0 : q 0 < rJ := hq.2.2.1
  have hq0pos : 0 < q 0 := lt_trans (by norm_num) hbox.1
  simp only [cuspInvInner]
  rw [ite_eq_left (le_of_lt hq0), nrm_smul, nrm_bndOfU, mul_one,
    abs_of_pos (div_pos hq0pos (by rw [rJ]; norm_num))]
  rw [div_lt_one (by rw [rJ]; norm_num)]
  rw [rJ] at hq0 ⊢
  linarith

/-- **`polarCoordM` is continuous.**  It is `incW v ∘ fillProj ∘ cuspInvInner`, and each factor is
continuous (`cuspInvInner` by `continuous_cuspInvInner`, `fillProj` by its definition as a product
of the projection of the first coordinate with the `AddCircle` reduction of the torus
coordinates). -/
private theorem continuous_polarCoordM (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (c : ℝ) (k : Fin 4) (W : Set E2) :
    Continuous (polarCoordM a v tor c k W) := by
  have hz : ∀ q : {q : E4 // q ∈ polarBoxSect v c k W}, nrm (cuspInvInner v q.1).1 < 1 :=
    fun q => nrm_cuspInvInner_lt_one_polarBoxSect v c k W q.1 q.2
  have hcInv : Continuous (fun q : {q : E4 // q ∈ polarBoxSect v c k W} =>
      (⟨cuspInvInner v q.1, hz q⟩ : {z : E2 × E2 // nrm z.1 < 1})) :=
    ((continuous_cuspInvInner v).comp continuous_subtype_val).subtype_mk hz
  have hfill : Continuous (fillProj a v tor) := by
    change Continuous (fun z : {z : E2 × E2 // nrm z.1 < 1} =>
      ((⟨z.1.1, mem_sq_of_nrm_lt_one z.2⟩ : Work.Space.SquarePt),
       tor.symm (fun i => ((z.1.2 i : ℝ) : AddCircle (1 : ℝ)))))
    refine Continuous.prodMk ?_ ?_
    · exact Continuous.subtype_mk continuous_subtype_val.fst
        (fun z => mem_sq_of_nrm_lt_one z.2)
    · exact (Homeomorph.continuous tor.symm).comp (by fun_prop)
  have hmain : Continuous (fun q : {q : E4 // q ∈ polarBoxSect v c k W} =>
      a.incW v (fillProj a v tor (⟨cuspInvInner v q.1, hz q⟩))) :=
    (a.continuous_incW v).comp (hfill.comp hcInv)
  refine hmain.congr (fun q => ?_)
  simp only [polarCoordM, fillProj, sqPtOf]

/-- **`polarCoordM` is injective on the chart box**, for a `w`-box `W` on which the lift `y` of the
torus coordinates is determined by its class modulo `ℤ²` (the hypothesis `hsec`).

`incW v` is injective, so the two layer points and the two torus classes agree.  The latter gives
`y ≡ y' (mod ℤ²)`; the recovered `y = (cuspInvInner v q).2` satisfies
`wOf v y = (q 2, q 3) ∈ W` because `ThetaPolarS v c (cuspInvInner v q) = q` on the box
(`ThetaPolarS_cuspInvInner`, using `q 0 < rJ` and `uqOf v q - c ∈ [0,1)`), so `hsec` gives
`y = y'`.  Both `cuspInvInner v q` and `cuspInvInner v q'` therefore have the same two components,
and `cuspInvInner` is injective on the box (`isOpenEmbedding_cuspInvInner_polarBoxSect`). -/
private theorem injective_polarCoordM (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (c : ℝ) (k : Fin 4) (W : Set E2)
    (hW : IsOpen W)
    (hsec : ∀ y y' : E2, wOf v y ∈ W → wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    Function.Injective (polarCoordM a v tor c k W) := by
  intro q q' h
  simp only [polarCoordM] at h
  have hpair := a.incW_injective v h
  have h1 : (cuspInvInner v q.1).1 = (cuspInvInner v q'.1).1 := by
    have := congrArg (fun z : Work.Space.SquarePt × a.Torus v => (z.1 : E2)) hpair
    simpa using this
  have h2 : (fun i : Fin 2 => (((cuspInvInner v q.1).2 i : ℝ) : AddCircle (1 : ℝ))) =
      (fun i : Fin 2 => (((cuspInvInner v q'.1).2 i : ℝ) : AddCircle (1 : ℝ))) := by
    have := congrArg (fun z : Work.Space.SquarePt × a.Torus v => z.2) hpair
    exact tor.symm.injective this
  have hwq : wOf v (cuspInvInner v q.1).2 ∈ W := by
    have hT := ThetaPolarS_cuspInvInner v c q.1 q.2.1 q.2.2.2.2.1
    have hw : wOf v (cuspInvInner v q.1).2 = !₂[q.1 2, q.1 3] := by
      ext i
      fin_cases i
      · have := congrArg (fun z : E4 => z 2) hT
        simpa [ThetaPolarS] using this
      · have := congrArg (fun z : E4 => z 3) hT
        simpa [ThetaPolarS] using this
    rw [hw]
    exact q.2.2.1
  have hwq' : wOf v (cuspInvInner v q'.1).2 ∈ W := by
    have hT := ThetaPolarS_cuspInvInner v c q'.1 q'.2.1 q'.2.2.2.2.1
    have hw : wOf v (cuspInvInner v q'.1).2 = !₂[q'.1 2, q'.1 3] := by
      ext i
      fin_cases i
      · have := congrArg (fun z : E4 => z 2) hT
        simpa [ThetaPolarS] using this
      · have := congrArg (fun z : E4 => z 3) hT
        simpa [ThetaPolarS] using this
    rw [hw]
    exact q'.2.2.1
  have hy : (cuspInvInner v q.1).2 = (cuspInvInner v q'.1).2 :=
    hsec _ _ hwq hwq' (fun i => congrFun h2 i)
  have hc : cuspInvInner v q.1 = cuspInvInner v q'.1 := Prod.ext h1 hy
  exact (isOpenEmbedding_cuspInvInner_polarBoxSect v c k W hW).toIsEmbedding.injective hc

/-- **`polarCoordM` is an open map.**  It factors as `incW v ∘ fillProj ∘ cuspInvInner`: the first
and the third factor are open maps because they are the open embeddings of the interior of the
filling piece and the inverse of the polar chart on the box, and the middle one is the open
projection `fillProj` of the cover onto the filling piece (`isOpenMap_fillProj`). -/
private theorem isOpenMap_polarCoordM (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (c : ℝ) (k : Fin 4) (W : Set E2)
    (hW : IsOpen W) :
    IsOpenMap (polarCoordM a v tor c k W) := by
  have hz : ∀ q : {q : E4 // q ∈ polarBoxSect v c k W}, nrm (cuspInvInner v q.1).1 < 1 :=
    fun q => nrm_cuspInvInner_lt_one_polarBoxSect v c k W q.1 q.2
  have hcInv : IsOpenMap (fun q : {q : E4 // q ∈ polarBoxSect v c k W} => cuspInvInner v q.1) :=
    (isOpenEmbedding_cuspInvInner_polarBoxSect v c k W hW).isOpenMap
  have hcInv' : IsOpenMap (fun q : {q : E4 // q ∈ polarBoxSect v c k W} =>
      (⟨cuspInvInner v q.1, hz q⟩ : {z : E2 × E2 // nrm z.1 < 1})) :=
    hcInv.codRestrict (s := {z : E2 × E2 | nrm z.1 < 1}) hz
  have hgAmb : IsOpenMap (fun q : {q : E4 // q ∈ polarBoxSect v c k W} =>
      fillProj a v tor ⟨cuspInvInner v q.1, hz q⟩) :=
    (isOpenMap_fillProj a v tor).comp hcInv'
  have hU : ∀ q : {q : E4 // q ∈ polarBoxSect v c k W},
      fillProj a v tor ⟨cuspInvInner v q.1, hz q⟩ ∈ fillInterior a v := by
    intro q
    show Work.Space.sqNorm (fillProj a v tor ⟨cuspInvInner v q.1, hz q⟩).1 < 1
    simp only [fillProj, sqPtOf, Work.Space.sqNorm, Work.Space.nrm]
    exact hz q
  have hgU : IsOpenMap (fun q : {q : E4 // q ∈ polarBoxSect v c k W} =>
      (⟨fillProj a v tor ⟨cuspInvInner v q.1, hz q⟩, hU q⟩ : fillInterior a v)) :=
    hgAmb.codRestrict (s := fillInterior a v) hU
  have hι : IsOpenMap (fun p : fillInterior a v => a.incW v p.1) :=
    (isOpenEmbedding_incW_interior a v).isOpenMap
  have hopen : IsOpenMap ((fun p : fillInterior a v => a.incW v p.1) ∘
      fun q : {q : E4 // q ∈ polarBoxSect v c k W} =>
        (⟨fillProj a v tor ⟨cuspInvInner v q.1, hz q⟩, hU q⟩ : fillInterior a v)) :=
    hι.comp hgU
  have heq : ((fun p : fillInterior a v => a.incW v p.1) ∘
      fun q : {q : E4 // q ∈ polarBoxSect v c k W} =>
        (⟨fillProj a v tor ⟨cuspInvInner v q.1, hz q⟩, hU q⟩ : fillInterior a v))
      = polarCoordM a v tor c k W := by
    funext q
    simp only [Function.comp_apply, polarCoordM, fillProj, sqPtOf]
  rw [heq] at hopen
  exact hopen

/-- **`polarCoordM` is an open embedding.**  It is continuous, injective (by the section hypothesis
`hsec` on `W`) and an open map. -/
private theorem isOpenEmbedding_polarCoordM_aux (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (c : ℝ) (k : Fin 4) (W : Set E2)
    (hW : IsOpen W)
    (hsec : ∀ y y' : E2, wOf v y ∈ W → wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    Topology.IsOpenEmbedding (polarCoordM a v tor c k W) :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_polarCoordM a v tor c k W)
    (injective_polarCoordM a v tor c k W hW hsec)
    (isOpenMap_polarCoordM a v tor c k W hW)

theorem exists_polarChartM (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (c : ℝ) (k : Fin 4) (W : Set E2)
    (hW : IsOpen W)
    (hsec : ∀ y y' : E2, wOf v y ∈ W → wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    ∃ Φ : OpenPartialHomeomorph a.Mhat E4,
      Φ.source = polarCoordM a v tor c k W '' (Set.univ : Set {q : E4 // q ∈ polarBoxSect v c k W}) ∧
      Φ.target = polarBoxSect v c k W ∧
      ∀ q (hq : q ∈ polarBoxSect v c k W), Φ (polarCoordM a v tor c k W ⟨q, hq⟩) = q := by
  have hf : Topology.IsOpenEmbedding (polarCoordM a v tor c k W) :=
    isOpenEmbedding_polarCoordM_aux a v tor c k W hW hsec
  by_cases hne : (polarBoxSect v c k W).Nonempty
  · have hB : IsOpen (polarBoxSect v c k W) := isOpen_polarBoxSect v c k W hW
    let BB : TopologicalSpace.Opens E4 := ⟨polarBoxSect v c k W, hB⟩
    let e : OpenPartialHomeomorph BB E4 := BB.openPartialHomeomorphSubtypeCoe hne.to_subtype
    have hesrc : e.source = (Set.univ : Set BB) :=
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source BB hne.to_subtype
    have hetgt : e.target = polarBoxSect v c k W :=
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target BB hne.to_subtype
    have hecoe : (e : BB → E4) = Subtype.val :=
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe BB hne.to_subtype
    refine ⟨e.lift_openEmbedding hf, ?_, ?_, ?_⟩
    · rw [OpenPartialHomeomorph.lift_openEmbedding_source, hesrc]
    · rw [OpenPartialHomeomorph.lift_openEmbedding_target]
      exact hetgt
    · intro q hq
      rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
      simpa using congrFun hecoe (⟨q, hq⟩ : BB)
  · have hBe : polarBoxSect v c k W = ∅ := not_nonempty_iff_eq_empty.mp hne
    have hEmpty : IsEmpty {q : E4 // q ∈ polarBoxSect v c k W} :=
      (isEmpty_subtype _).mpr (fun x hx => by rw [hBe] at hx; exact hx)
    refine ⟨{ toFun := fun _ => (0 : E4)
              invFun := fun _ => Classical.arbitrary a.Mhat
              source := ∅
              target := ∅
              map_source' := by simp
              map_target' := by simp
              left_inv' := by simp
              right_inv' := by simp
              open_source := isOpen_empty
              open_target := isOpen_empty
              continuousOn_toFun := continuousOn_empty _
              continuousOn_invFun := continuousOn_empty _ }, ?_, ?_, ?_⟩
    · rw [Set.image_eq_empty.mpr (univ_eq_empty_iff.mpr hEmpty)]
    · exact hBe.symm
    · intro q hq
      rw [hBe] at hq
      exact absurd hq (by simp)

end Work.Cusp
