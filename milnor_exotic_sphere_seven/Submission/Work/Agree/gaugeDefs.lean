import Mathlib
import Submission.Work.Agree.crux
import Submission.Work.Agree.VkCharts
import Submission.Work.Agree.S4Bundle
import Submission.Work.Agree.fderiv_vMap_apply
import Submission.Work.Agree.vkTangent_coordChange_zero_one
import Submission.Work.Milnor.exists_proj

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `GeometryB`: the definitions used by the gauge construction

See `GEOMETRYB_PLAN.md` in this directory for the mathematics.  This file contains only the
definitions (and the easy lemmas about them); the substantial properties of the gauge are stated
and proved in the separate files `gaugeH0*`/`gaugeH1*`/`gaugeKey` in this directory.

Notation.  `Vk = Submission.Milnor.Vk (-2)`, `Z = Work.Agree.vkTangent h`,
`targetC = bundleComap (sum (clutchBundle 1 1) (clutchBundle 2 (-1))) discProj` (fibre `ℝ⁴ × ℝ⁴`),
`targetCore` = its transport along `fibEquiv = id × toQ` (fibre `MSpace8 = ℝ⁴ × ℍ`).  On `UX ∩ UY`
(where `UX = range ιX = Z.baseSet 0`, `UY = range ιY = Z.baseSet 1`) one has
`Z.cc 0 1 b = fderiv (vMap (-2)) (chartOfX 0 b) = [[A,0],[B,C]]` and
`targetCore.cc (false,false) (true,true) b = [[qTwist 1 1 u, 0],[0,C]]`; the gauge is
`H₀ = diag(η J,1) · (1 + a · [[0,0],[C⁻¹B,0]])` on `UX`, `H₁ = id` for `‖chartOfY 0 ·‖ ≤ 2/3` and
`H₁ = targetCore.cc (ff) (tt) · H₀ · Z.cc 1 0` otherwise.
-/

open scoped Manifold ContDiff Topology
open TopologicalSpace Set

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.Agree

open Work.TangentClasses
open Submission.Glue

noncomputable section

local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "HH" => Quaternion ℝ

/-! ## Chart identifications of the glueing -/

/-- `vkCover 0` is the chart of the glueing at `ιX 0`. -/
lemma vkCover_zero_chartOfX :
    (vkCover 0).1 = (Submission.Milnor.vData (-2)).chartOfX (0 : Submission.Milnor.MSpace8) := by
  rw [vkCover_zero]
  change (Submission.Milnor.vData (-2)).chartAt ((Submission.Milnor.vData (-2)).ιX 0)
    = (Submission.Milnor.vData (-2)).chartOfX (0 : Submission.Milnor.MSpace8)
  have h := Quotient.out_eq ((Submission.Milnor.vData (-2)).ιX (0 : Submission.Milnor.MSpace8))
  have hrel : (Submission.Milnor.vData (-2)).rel
      (Quotient.out ((Submission.Milnor.vData (-2)).ιX (0 : Submission.Milnor.MSpace8)))
      (Sum.inl 0) :=
    @Quotient.exact (Submission.Milnor.MSpace8 ⊕ Submission.Milnor.MSpace8)
      (Submission.Milnor.vData (-2)).setoid _ _ h
  rcases ho : Quotient.out ((Submission.Milnor.vData (-2)).ιX (0 : Submission.Milnor.MSpace8))
    with p | p
  · rw [ho] at hrel
    have hpq : p = 0 := hrel
    subst hpq
    exact Submission.Glue.Data.chartAt_of_out_inl _ ho
  · rw [ho] at hrel
    exfalso
    obtain ⟨hp, -⟩ := hrel
    have hp' : (0 : Submission.Milnor.MSpace8) ∈ Submission.Milnor.vOpens := hp
    rw [Submission.Milnor.mem_vOpens] at hp'
    exact hp' rfl

/-- `vkCover 1` is the chart of the glueing at `ιY 0`. -/
lemma vkCover_one_chartOfY :
    (vkCover 1).1 = (Submission.Milnor.vData (-2)).chartOfY (0 : Submission.Milnor.MSpace8) := by
  rw [vkCover_one]
  change (Submission.Milnor.vData (-2)).chartAt ((Submission.Milnor.vData (-2)).ιY 0)
    = (Submission.Milnor.vData (-2)).chartOfY (0 : Submission.Milnor.MSpace8)
  have h := Quotient.out_eq ((Submission.Milnor.vData (-2)).ιY (0 : Submission.Milnor.MSpace8))
  have hrel : (Submission.Milnor.vData (-2)).rel
      (Quotient.out ((Submission.Milnor.vData (-2)).ιY (0 : Submission.Milnor.MSpace8)))
      (Sum.inr 0) :=
    @Quotient.exact (Submission.Milnor.MSpace8 ⊕ Submission.Milnor.MSpace8)
      (Submission.Milnor.vData (-2)).setoid _ _ h
  rcases ho : Quotient.out ((Submission.Milnor.vData (-2)).ιY (0 : Submission.Milnor.MSpace8))
    with p | p
  · rw [ho] at hrel
    exfalso
    obtain ⟨hp, hq⟩ := hrel
    have hp' : p.1 ≠ 0 := hp
    have hq' : (Submission.Milnor.vMap (-2) p).1 = 0 := by
      have h2 : (((Submission.Milnor.vData (-2)).φ p : Submission.Milnor.MSpace8)).1 = 0 :=
        congrArg (fun z : Submission.Milnor.MSpace8 => z.1) hq
      rw [← h2]
      rfl
    exact absurd hq' (Submission.Milnor.invBase_ne_zero hp')
  · rw [ho] at hrel
    have hpq : p = 0 := hrel
    subst hpq
    exact Submission.Glue.Data.chartAt_of_out_inr _ ho

/-- The source of the chart `chartOfX x` of the glued space is the image of `ιX`. -/
lemma chartOfX_source (x : Submission.Milnor.MSpace8) :
    ((Submission.Milnor.vData (-2)).chartOfX x).source
      = Set.range (Submission.Milnor.vData (-2)).ιX := by
  rw [Submission.Glue.Data.chartOfX, OpenPartialHomeomorph.trans_source]
  have h : (chartAt Submission.Milnor.MSpace8 x).source = Set.univ := by
    rw [chartAt_self_eq]; rfl
  rw [h, Set.preimage_univ, Set.inter_univ, ← Submission.Glue.Data.homX_target]
  exact OpenPartialHomeomorph.symm_source _

/-- The source of the chart `chartOfY y` of the glued space is the image of `ιY`. -/
lemma chartOfY_source (y : Submission.Milnor.MSpace8) :
    ((Submission.Milnor.vData (-2)).chartOfY y).source
      = Set.range (Submission.Milnor.vData (-2)).ιY := by
  rw [Submission.Glue.Data.chartOfY, OpenPartialHomeomorph.trans_source]
  have h : (chartAt Submission.Milnor.MSpace8 y).source = Set.univ := by
    rw [chartAt_self_eq]; rfl
  rw [h, Set.preimage_univ, Set.inter_univ, ← Submission.Glue.Data.homY_target]
  exact OpenPartialHomeomorph.symm_source _

/-- The source of `vkCover 0` is the image of `ιX`. -/
lemma vkCover_zero_source :
    (vkCover 0).1.source = Set.range (Submission.Milnor.vData (-2)).ιX := by
  rw [vkCover_zero_chartOfX]
  exact chartOfX_source 0

/-- The source of `vkCover 1` is the image of `ιY`. -/
lemma vkCover_one_source :
    (vkCover 1).1.source = Set.range (Submission.Milnor.vData (-2)).ιY := by
  rw [vkCover_one_chartOfY]
  exact chartOfY_source 0

/-- The base set of `vkTangent h` at `0` is the image of `ιX`. -/
lemma vkTangent_baseSet_zero (h : ∀ x : Vk, ∃ i : Fin 2,
    x ∈ (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk).baseSet (vkCover i)) :
    (vkTangent h).baseSet 0 = Set.range (Submission.Milnor.vData (-2)).ιX := by
  rw [vkTangent, RealBundle.reindex_baseSet, tangentBundle_baseSet, vkCover_zero_source]

/-- The base set of `vkTangent h` at `1` is the image of `ιY`. -/
lemma vkTangent_baseSet_one (h : ∀ x : Vk, ∃ i : Fin 2,
    x ∈ (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk).baseSet (vkCover i)) :
    (vkTangent h).baseSet 1 = Set.range (Submission.Milnor.vData (-2)).ιY := by
  rw [vkTangent, RealBundle.reindex_baseSet, tangentBundle_baseSet, vkCover_one_source]

/-- The two hemispheres. -/
def gaugeUX : Set Vk := Set.range (Submission.Milnor.vData (-2)).ιX
def gaugeUY : Set Vk := Set.range (Submission.Milnor.vData (-2)).ιY

/-- The X-chart coordinate of a point of `Vk`. -/
def gaugeX (b : Vk) : E4 := ((Submission.Milnor.vData (-2)).chartOfX 0 b).1

/-- The second X-chart coordinate of a point of `Vk`. -/
def gaugeY (b : Vk) : HH := ((Submission.Milnor.vData (-2)).chartOfX 0 b).2

/-- The unit direction attached to the X-chart coordinate. -/
def gaugeU (b : Vk) : HH := ((Submission.Milnor.unitDir (gaugeX b) : Submission.Milnor.QS3) : HH)

/-- The first Y-chart coordinate of a point of `Vk`. -/
def gaugeXY (b : Vk) : E4 := ((Submission.Milnor.vData (-2)).chartOfY 0 b).1

/-- The norm of the first Y-chart coordinate. -/
def gaugeYNorm (b : Vk) : ℝ := ‖gaugeXY b‖

/-- `chartOfX 0` is the identity on the X-chart coordinates. -/
lemma chartOfX_iotaX (p : Submission.Milnor.MSpace8) :
    (Submission.Milnor.vData (-2)).chartOfX 0 ((Submission.Milnor.vData (-2)).ιX p) = p := by
  simp only [Submission.Glue.Data.chartOfX, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    chartAt_self_eq, OpenPartialHomeomorph.refl_apply, Submission.Glue.Data.homX_symm_apply]
  rfl

/-- `chartOfY 0` is the identity on the Y-chart coordinates. -/
lemma chartOfY_iotaY (p : Submission.Milnor.MSpace8) :
    (Submission.Milnor.vData (-2)).chartOfY 0 ((Submission.Milnor.vData (-2)).ιY p) = p := by
  simp only [Submission.Glue.Data.chartOfY, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    chartAt_self_eq, OpenPartialHomeomorph.refl_apply, Submission.Glue.Data.homY_symm_apply]
  rfl

/-- The Y-chart coordinate of `ιX p` is `vMap (-2) p`. -/
lemma chartOfY_iotaX (p : Submission.Milnor.MSpace8) (hp : p.1 ≠ 0) :
    (Submission.Milnor.vData (-2)).chartOfY 0 ((Submission.Milnor.vData (-2)).ιX p) =
      Submission.Milnor.vMap (-2) p := by
  have hι : (Submission.Milnor.vData (-2)).ιX p
      = (Submission.Milnor.vData (-2)).ιY (Submission.Milnor.vMap (-2) p) :=
    Quotient.sound ⟨hp, rfl⟩
  rw [hι, chartOfY_iotaY]

lemma gaugeX_iotaX (p : Submission.Milnor.MSpace8) :
    gaugeX ((Submission.Milnor.vData (-2)).ιX p) = p.1 := by
  simp only [gaugeX, chartOfX_iotaX]

lemma gaugeYNorm_iotaX (p : Submission.Milnor.MSpace8) (hp : p.1 ≠ 0) :
    gaugeYNorm ((Submission.Milnor.vData (-2)).ιX p) = ‖p.1‖⁻¹ := by
  simp only [gaugeYNorm, gaugeXY, chartOfY_iotaX p hp]
  exact Submission.Milnor.norm_invBase p.1

lemma gaugeU_iotaX (p : Submission.Milnor.MSpace8) :
    gaugeU ((Submission.Milnor.vData (-2)).ιX p)
      = ((Submission.Milnor.unitDir p.1 : Submission.Milnor.QS3) : HH) := by
  simp only [gaugeU, gaugeX_iotaX]

/-- The clutching direction of `discProj (ιX p)` is `unitDir p.1`. -/
lemma uDir_discProj_iotaX (p : Submission.Milnor.MSpace8) :
    uDir (discProj ((Submission.Milnor.vData (-2)).ιX p))
      = ((Submission.Milnor.unitDir p.1 : Submission.Milnor.QS3) : HH) := by
  rw [discProj_apply, Work.Milnor.vBaseMap_ιX]
  rfl

/-! ## The fibre transport `ℝ⁴ × ℝ⁴ ≃ ℝ⁴ × ℍ` and the target core -/

/-- The linear isometry equivalence `ℝ⁴ → ℍ` underlying `Work.Agree.toQ`. -/
def toQE : E4 ≃L[ℝ] HH :=
  LinearIsometryEquiv.toContinuousLinearEquiv
    (Quaternion.linearIsometryEquivTuple.symm : E4 ≃ₛₗᵢ[RingHom.id ℝ] HH)

/-- `id × ofQ`, the identification of the fibre `ℝ⁴ × ℝ⁴` of the target with the fibre
`MSpace8 = ℝ⁴ × ℍ` of the tangent bundle. -/
def fibEquiv : (E4 × E4) ≃L[ℝ] Submission.Milnor.MSpace8 :=
  (ContinuousLinearEquiv.refl ℝ E4).prodCongr toQE

@[simp] lemma fibEquiv_apply (p : E4 × E4) : fibEquiv p = (p.1, toQ p.2) := rfl

@[simp] lemma fibEquiv_symm_apply (p : Submission.Milnor.MSpace8) :
    fibEquiv.symm p = (p.1, ofQ p.2) := rfl

@[simp] lemma fibEquiv_coe_apply (p : E4 × E4) :
    (fibEquiv : (E4 × E4) →L[ℝ] Submission.Milnor.MSpace8) p = (p.1, toQ p.2) := rfl

@[simp] lemma fibEquiv_coe_symm_apply (p : Submission.Milnor.MSpace8) :
    (fibEquiv.symm : Submission.Milnor.MSpace8 →L[ℝ] (E4 × E4)) p = (p.1, ofQ p.2) := rfl

/-- The pullback of `TS⁴ ⊕ ξ` to the disc bundle. -/
def targetC : RealBundle Vk (E4 × E4) (Bool × Bool) :=
  Work.Thom.bundleComap (RealBundle.sum (clutchBundle (1 : ℤ) 1) (clutchBundle (2 : ℤ) (-1)))
    discProj

/-- The same bundle with the fibre `MSpace8`, obtained by transporting along `fibEquiv`. -/
def targetCore : RealBundle Vk Submission.Milnor.MSpace8 (Bool × Bool) :=
  Classical.choose (Work.Thom.exists_coreMapFibre fibEquiv targetC)

lemma targetCore_baseSet : targetCore.baseSet = targetC.baseSet :=
  (Classical.choose_spec (Work.Thom.exists_coreMapFibre fibEquiv targetC)).1

lemma targetCore_indexAt : targetCore.indexAt = targetC.indexAt :=
  (Classical.choose_spec (Work.Thom.exists_coreMapFibre fibEquiv targetC)).2.1

lemma targetCore_coordChange (i j : Bool × Bool) (b : Vk) :
    targetCore.coordChange i j b
      = (fibEquiv : (E4 × E4) →L[ℝ] Submission.Milnor.MSpace8).comp
          ((targetC.coordChange i j b).comp
            (fibEquiv.symm : Submission.Milnor.MSpace8 →L[ℝ] (E4 × E4))) :=
  (Classical.choose_spec (Work.Thom.exists_coreMapFibre fibEquiv targetC)).2.2.1 i j b

lemma nonempty_bundleIso_targetC_targetCore : Nonempty (Work.Thom.BundleIso targetC targetCore) :=
  (Classical.choose_spec (Work.Thom.exists_coreMapFibre fibEquiv targetC)).2.2.2

/-- The explicit form of the target transition on the overlap. -/
lemma targetC_coordChange_ff_tt (b : Vk) :
    targetC.coordChange (false, false) (true, true) b
      = (qTwist (1 : ℤ) 1 (uDir (discProj b))).prodMap
          (qTwist (2 : ℤ) (-1) (uDir (discProj b))) := rfl

/-! ## Conjugation, blocks, cutoffs -/

/-- Quaternionic conjugation as a real-linear map. -/
def conjQ : HH →L[ℝ] HH :=
  LinearMap.toContinuousLinearMap
    { toFun := star
      map_add' := fun a b => star_add a b
      map_smul' := fun c a => Quaternion.star_smul c a }

lemma conjQ_apply (a : HH) : conjQ a = star a := by simp [conjQ]

/-- `J = toQ ∘ (conjugation) ∘ ofQ` on the standard fibre `ℝ⁴`, i.e. `v ↦ \bar v`. -/
def gaugeJ : E4 →L[ℝ] E4 := ofQ.comp (conjQ.comp toQ)

lemma gaugeJ_apply (v : E4) : gaugeJ v = ofQ (star (toQ v)) := by
  simp only [gaugeJ, ContinuousLinearMap.comp_apply, conjQ_apply]

lemma gaugeJ_comp_J : gaugeJ.comp gaugeJ = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, gaugeJ, conjQ_apply, toQ_ofQ, star_star, ofQ_toQ]
  rfl

/-- The block matrix `[[A,0],[B,C]]` acting on `MSpace8 = ℝ⁴ × ℍ`. -/
def gaugeBlk (A : E4 →L[ℝ] E4) (B : E4 →L[ℝ] HH) (C : HH →L[ℝ] HH) :
    Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8 :=
  (A.comp (ContinuousLinearMap.fst ℝ E4 HH)).prod
    ((B.comp (ContinuousLinearMap.fst ℝ E4 HH)) +
      (C.comp (ContinuousLinearMap.snd ℝ E4 HH)))

@[simp] lemma gaugeBlk_apply (A : E4 →L[ℝ] E4) (B : E4 →L[ℝ] HH) (C : HH →L[ℝ] HH)
    (δ : E4) (ε : HH) : gaugeBlk A B C (δ, ε) = (A δ, B δ + C ε) := rfl

lemma gaugeBlk_comp (A A' : E4 →L[ℝ] E4) (B B' : E4 →L[ℝ] HH) (C C' : HH →L[ℝ] HH) :
    (gaugeBlk A B C).comp (gaugeBlk A' B' C')
      = gaugeBlk (A.comp A') (B.comp A' + C.comp B') (C.comp C') := by
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨δ, ε⟩ := v
  simp only [ContinuousLinearMap.comp_apply, gaugeBlk_apply, ContinuousLinearMap.add_apply,
    map_add, add_assoc]

@[simp] lemma gaugeBlk_id : gaugeBlk (1 : E4 →L[ℝ] E4) 0 (1 : HH →L[ℝ] HH) = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨δ, ε⟩ := v
  simp only [gaugeBlk_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.zero_apply,
    zero_add]

/-- The cutoff `a`: `0` for `s ≤ 1`, `1` for `s ≥ 3/2`. -/
def aCut (s : ℝ) : ℝ := min 1 (max 0 (2 * s - 2))

/-- `η(t) = -(max t 1)⁻²`; it equals `-t⁻²` for `t ≥ 1`. -/
def etaCut (t : ℝ) : ℝ := -((max t 1) ^ 2)⁻¹

lemma continuous_aCut : Continuous aCut := by
  unfold aCut; fun_prop

lemma continuous_etaCut : Continuous etaCut := by
  unfold etaCut
  have h : Continuous fun t : ℝ => (max t 1) ^ 2 := (continuous_id.max continuous_const).pow 2
  exact (h.inv₀ fun t => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le one_pos (le_max_right t 1)))).neg

lemma aCut_of_le_one {s : ℝ} (hs : s ≤ 1) : aCut s = 0 := by
  have h : 2 * s - 2 ≤ 0 := by linarith
  simp only [aCut, max_eq_left h, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

lemma aCut_of_ge {s : ℝ} (hs : 3 / 2 ≤ s) : aCut s = 1 := by
  have h : (1 : ℝ) ≤ 2 * s - 2 := by linarith
  have h0 : (0 : ℝ) ≤ 2 * s - 2 := le_trans zero_le_one h
  simp only [aCut, max_eq_right h0, min_eq_left h]

lemma etaCut_of_ge_one {t : ℝ} (ht : 1 ≤ t) : etaCut t = -(t ^ 2)⁻¹ := by
  simp only [etaCut, max_eq_left ht]

lemma etaCut_ne_zero (t : ℝ) : etaCut t ≠ 0 := by
  have h : (0 : ℝ) < max t 1 := lt_of_lt_of_le one_pos (le_max_right t 1)
  have h2 : (max t 1) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt h)
  simp only [etaCut, neg_ne_zero]
  exact inv_ne_zero h2

/-! ## The off-diagonal block and the gauge -/

/-- The (2,1) block of `fderiv (vMap (-2))` at the X-chart coordinate. -/
def gaugeBOff (b : Vk) : E4 →L[ℝ] HH :=
  (ContinuousLinearMap.snd ℝ E4 HH).comp
    ((fderiv ℝ (Submission.Milnor.vMap (-2)) ((Submission.Milnor.vData (-2)).chartOfX 0 b)).comp
      (((1 : E4 →L[ℝ] E4).prod (0 : E4 →L[ℝ] HH))))

/-! ## The second diagonal block `C`, and the two gauges -/

lemma gaugeBOff_apply (b : Vk) (δ : E4) :
    gaugeBOff b δ
      = (fderiv ℝ (Submission.Milnor.vMap (-2))
          ((Submission.Milnor.vData (-2)).chartOfX 0 b) (δ, 0)).2 := rfl

/-- `C⁻¹ = (w ↦ u⁻² w u)`, the inverse of `qTwist 2 (-1) u`. -/
def gaugeCinv (b : Vk) : HH →L[ℝ] HH :=
  toQ.comp ((qTwist (-2) 1 (gaugeU b)).comp ofQ)

/-- The (2,2) block of `fderiv (vMap (-2))` (transported to `ℍ`), i.e. `w ↦ u² w u⁻¹`. -/
def gaugeC (b : Vk) : HH →L[ℝ] HH :=
  toQ.comp ((qTwist (2 : ℤ) (-1) (gaugeU b)).comp ofQ)

lemma gaugeC_apply (b : Vk) (w : HH) :
    gaugeC b w = gaugeU b ^ (2 : ℤ) * w * gaugeU b ^ (-1 : ℤ) := by
  simp only [gaugeC, ContinuousLinearMap.comp_apply, qTwist_apply, toQ_ofQ]

lemma gaugeCinv_apply (b : Vk) (w : HH) :
    gaugeCinv b w = gaugeU b ^ (-2 : ℤ) * w * gaugeU b := by
  simp only [gaugeCinv, ContinuousLinearMap.comp_apply, qTwist_apply, toQ_ofQ, zpow_one]

lemma gaugeC_apply_pow (b : Vk) (w : HH) :
    gaugeC b w = gaugeU b ^ 2 * w * (gaugeU b)⁻¹ := by
  rw [gaugeC_apply,
    show gaugeU b ^ (2 : ℤ) = gaugeU b ^ 2 from by rw [zpow_ofNat],
    show gaugeU b ^ (-1 : ℤ) = (gaugeU b)⁻¹ from by rw [zpow_neg, zpow_one]]

lemma gaugeU_ne_zero (b : Vk) : gaugeU b ≠ 0 := by
  have h : gaugeU b ∈ Metric.sphere (0 : HH) 1 :=
    (Submission.Milnor.unitDir (gaugeX b)).2
  rw [Metric.mem_sphere, dist_zero_right] at h
  intro h0
  rw [h0, norm_zero] at h
  norm_num at h

/-- The off-diagonal part `[[0,0],[C⁻¹ B,0]]`. -/
def gaugeXOff (b : Vk) : E4 →L[ℝ] HH := (gaugeCinv b).comp (gaugeBOff b)

/-- **The gauge on the first chart**, in block form `[[η J, 0], [a C⁻¹B, 1]]`, where `a` is a
cutoff vanishing identically near `Z₀` (`‖gaugeX ·‖ ≤ 1`) and equal to `1` for
`‖gaugeX ·‖ ≥ 3/2`. -/
def gaugeH0 (b : Vk) : Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8 :=
  gaugeBlk ((etaCut ‖gaugeX b‖) • gaugeJ) ((aCut ‖gaugeX b‖) • gaugeXOff b) 1

/-- The inverse of `gaugeH0`, in block form `[[η⁻¹ J, 0], [-a η⁻¹ C⁻¹B J, 1]]`. -/
def gaugeH0inv (b : Vk) : Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8 :=
  gaugeBlk (((etaCut ‖gaugeX b‖)⁻¹) • gaugeJ)
    ((-(aCut ‖gaugeX b‖) * (etaCut ‖gaugeX b‖)⁻¹) • ((gaugeXOff b).comp gaugeJ)) 1

/-! ## The gauge `H₁` -/

variable (h : ∀ x : Vk, ∃ i : Fin 2,
    x ∈ (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk).baseSet (vkCover i))

/-- **The gauge on the second chart.**  On the "equator" `gaugeYNorm · = 0` (i.e. on `Z∞`, which
is *not* in the X-chart `gaugeUX`) it is the identity; this is what makes it continuous there, since
`H₀` inverts the discrepancy of the two transitions on `{0 < gaugeYNorm ≤ 2/3}` as well. -/
def gaugeH1 : Vk → Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8 := fun b =>
  if gaugeYNorm b = 0 then 1
  else (targetCore.coordChange (false, false) (true, true) b).comp
    ((gaugeH0 b).comp ((vkTangent h).coordChange 1 0 b))

/-- The inverse of `gaugeH1`. -/
def gaugeH1inv : Vk → Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8 := fun b =>
  if gaugeYNorm b = 0 then 1
  else ((vkTangent h).coordChange 0 1 b).comp
    ((gaugeH0inv b).comp (targetCore.coordChange (true, true) (false, false) b))

end

end Work.Agree
