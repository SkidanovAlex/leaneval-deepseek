import Mathlib
import Submission.Work.ThomBordism.ambientLocalDefs
import Submission.Work.ThomBordism.ambientLocalDefs2
import Submission.Work.Tubular.OnePointModel
import Submission.Work.PTGeometric.HOFDefs
import Submission.Work.Tubular.Gauss
import Submission.Work.ThomBordism.cappedChart_homotopic_translation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-!
# The convex interpolation between the identity and the blow-up coefficient

`Work.Tubular.normalBlowUp E ε = radialRescale E (ε * (ε - r)⁻¹)` is a positive fibrewise radial
rescaling only on the **open** `ε`-disc: `blowCoeff E ε p = ε * (ε - normalNorm E p)⁻¹` is `0` on the
norm-`ε` sphere (so `normalBlowUp` there collapses to the zero section), which is why
`normalBlowUp` is *not* a map of pairs `(ν, ν∖0) → (ν, ν∖0)`.

This file supplies the coefficient family

  `blowPsi ε t r = 1 + t * (ε * (ε - r)⁻¹ - 1)`

which is the affine interpolation `(1 - t) * 1 + t * blowCoeff` between the identity coefficient
(`t = 0`) and the blow-up coefficient (`t = 1`).  Because `blowCoeff r > 0` for `r < ε`, every
`blowPsi ε t r` is positive for `0 ≤ t ≤ 1`, `r < ε`; consequently the whole family
`radialRescale E (blowPsi ε t)` is a family of *positive* radial rescalings of the open `ε`-disc,
hence maps of pairs, and it joins `id` to `normalBlowUp E ε`.  This is the tool that makes the
correction in `NOTE_AMBIENTV2_PLAN5.md` (the "open tube" version of (F1)) stateable.
-/

open scoped Topology

namespace Work.ThomBordism

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The interpolation coefficient**: `1` at `t = 0`, the blow-up coefficient `ε * (ε - r)⁻¹` at
`t = 1`.  As a function of `r` it is the affine combination `(1 - t) * 1 + t * (ε * (ε - r)⁻¹)`. -/
noncomputable def blowPsi (ε t r : ℝ) : ℝ := 1 + t * (ε * (ε - r)⁻¹ - 1)

@[simp] theorem blowPsi_zero (ε r : ℝ) : blowPsi ε 0 r = 1 := by simp [blowPsi]

@[simp] theorem blowPsi_one (ε r : ℝ) : blowPsi ε 1 r = ε * (ε - r)⁻¹ := by simp [blowPsi]

/-- The affine form of the interpolation. -/
theorem blowPsi_eq (ε t r : ℝ) : blowPsi ε t r = (1 - t) + t * (ε * (ε - r)⁻¹) := by
  rw [blowPsi]; ring

/-- **The interpolation stays positive.**  For `ε > 0`, `r < ε` and `t ∈ [0,1]` the coefficient is a
convex combination of `1 > 0` and `ε * (ε - r)⁻¹ > 0`. -/
theorem blowPsi_pos {ε t r : ℝ} (hε : 0 < ε) (hr : r < ε) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < blowPsi ε t r := by
  rw [blowPsi_eq]
  have hb : 0 < ε * (ε - r)⁻¹ := mul_pos hε (inv_pos.mpr (by linarith))
  rcases eq_or_lt_of_le ht1 with h | h
  · subst h
    simpa using hb
  · have h2 : 0 ≤ t * (ε * (ε - r)⁻¹) := mul_nonneg ht0 hb.le
    linarith

/-! ## `normalBlowUp` is `radialRescale` with the blow-up coefficient -/

/-- **The blow-up is the radial rescaling with coefficient `ε * (ε - r)⁻¹`.** -/
theorem normalBlowUp_eq_radialRescale (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ε : ℝ) (p : Work.Tubular.NormalTotal E) :
    Work.Tubular.normalBlowUp E ε p
      = radialRescale E (fun r => ε * (ε - r)⁻¹) p := by
  apply Subtype.ext
  rw [radialRescale_coe]
  rfl

/-- **The `t = 1` stage of the interpolation is the blow-up.** -/
theorem radialRescale_blowPsi_one (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ε : ℝ) (p : Work.Tubular.NormalTotal E) :
    radialRescale E (blowPsi ε 1) p = Work.Tubular.normalBlowUp E ε p := by
  rw [normalBlowUp_eq_radialRescale]
  congr 1
  funext r
  simp

/-! ## The norm of the interpolated rescaling -/

/-- **The norm of the `t`-th stage.**  On the open `ε`-disc the interpolated rescaling is a *positive*
rescaling, so its norm is `blowPsi ε t (‖p‖) * ‖p‖`. -/
theorem normalNorm_radialRescale_blowPsi
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε t : ℝ} (hε : 0 < ε) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {p : Work.Tubular.NormalTotal E} (hp : Work.Tubular.normalNorm E p < ε) :
    Work.Tubular.normalNorm E (radialRescale E (blowPsi ε t) p)
      = blowPsi ε t (Work.Tubular.normalNorm E p) * Work.Tubular.normalNorm E p := by
  rw [normalNorm_radialRescale,
    abs_of_pos (blowPsi_pos hε hp ht0 ht1)]

/-- **The interpolated rescaling keeps the punctured set.**  On the open `ε`-disc with a nonzero
normal vector, every stage is again nonzero. -/
theorem mem_normalNonzero_radialRescale_blowPsi
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε t : ℝ} (hε : 0 < ε) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {p : Work.Tubular.NormalTotal E} (hp : Work.Tubular.normalNorm E p < ε)
    (hp0 : p ∈ Work.Tubular.normalNonzero E) :
    radialRescale E (blowPsi ε t) p ∈ Work.Tubular.normalNonzero E := by
  rw [Work.Tubular.mem_normalNonzero] at hp0 ⊢
  rw [normalNorm_radialRescale_blowPsi E hε ht0 ht1 hp]
  exact mul_ne_zero (ne_of_gt (blowPsi_pos hε hp ht0 ht1)) hp0

/-- **The `t`-th stage, capped**, lands in the closed `ε`-disc bundle. -/
theorem normalNorm_cap_radialRescale_blowPsi
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε t : ℝ} (hε : 0 < ε) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (p : Work.Tubular.NormalTotal E) :
    Work.Tubular.normalNorm E (cap E ε (radialRescale E (blowPsi ε t) p))
      = min (|blowPsi ε t (Work.Tubular.normalNorm E p)|
              * Work.Tubular.normalNorm E p) ε := by
  rw [normalNorm_cap E hε.le]
  rw [normalNorm_radialRescale]

/-- **The `t`-th stage, capped, is nonzero whenever the original point is**, on the open `ε`-disc. -/
theorem mem_normalNonzero_cap_radialRescale_blowPsi
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε t : ℝ} (hε : 0 < ε) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {p : Work.Tubular.NormalTotal E} (hp : Work.Tubular.normalNorm E p < ε)
    (hp0 : p ∈ Work.Tubular.normalNonzero E) :
    cap E ε (radialRescale E (blowPsi ε t) p) ∈ Work.Tubular.normalNonzero E := by
  rw [Work.Tubular.mem_normalNonzero] at hp0 ⊢
  rw [normalNorm_cap_radialRescale_blowPsi E hε ht0 ht1 p]
  have hpos : 0 < |blowPsi ε t (Work.Tubular.normalNorm E p)|
      * Work.Tubular.normalNorm E p :=
    mul_pos (abs_pos.mpr (ne_of_gt (blowPsi_pos hε hp ht0 ht1))) (lt_of_le_of_ne
      (Work.Tubular.normalNorm_nonneg E p) (Ne.symm (by simpa using hp0)))
  exact ne_of_gt (lt_min hpos hε)

/-! ## Every stage is a map of pairs on the open tube -/

/-- **Each stage is a map of pairs on the open tube.**  For `y ∈ C.openTube` we have
`normalNorm E (C.inv y) < ε` (`C.normalNorm_inv_lt`), so `blowPsi_pos` applies and the `t`-th capped
stage keeps the normal vector nonzero: it sends the punctured open tube into the punctured disc, as a
map of pairs must.  (The strict inequality `< ε` is essential here — this is why the homotopy has to
be built on `C.openTube` and not on the closed tube `C.U`, cf. `NOTE_AMBIENTV2_PLAN5.md`.) -/
theorem blowPsi_stage_mem (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {y : Work.Tubular.Euc (8 + k)} (hy : y ∈ C.openTube)
    (hy0 : C.inv y ∈ Work.Tubular.normalNonzero E) :
    cap E ε (radialRescale E (blowPsi ε t) (C.inv y)) ∈ Work.Tubular.normalNonzero E :=
  mem_normalNonzero_cap_radialRescale_blowPsi E C.eps_pos ht0 ht1
    (C.normalNorm_inv_lt hy) hy0

/-- **The `t = 1` stage on the open tube is exactly the collapse's local form**: the composite
`y ↦ normalBlowUp E ε (C.inv y)` that `hg2` pins down. -/
theorem blowPsi_stage_one_eq (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (y : Work.Tubular.Euc (8 + k)) :
    cap E ε (radialRescale E (blowPsi ε 1) (C.inv y))
      = cap E ε (Work.Tubular.normalBlowUp E ε (C.inv y)) := by
  rw [radialRescale_blowPsi_one]

/-! ## The endpoints of the interpolation -/

/-! ## The `t = 0` stage on the tube is the identity

For `y ∈ C.U` the tube inverse `C.inv y` lies in the closed `ε`-disc bundle (`C.inv_mem`), so the
`t = 0` stage is `tubeMap (C.inv y) = y` (`C.tubeMap_inv`).  Hence the `t = 0` end of the
interpolating family is the identity of the tube, with no further work. -/

/-- **The `t = 0` stage on the tube is the identity.** -/
theorem blowPsi_apply_zero (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (y : ↥C.U) :
    Work.Tubular.tubeMap E (cap E ε (radialRescale E (blowPsi ε 0) (C.inv y.1)))
      = (y.1 : Work.Tubular.Euc (8 + k)) := by
  rw [radialRescale_eq_self E _ (by simp)]
  rw [cap_eq_self_of_le E C.eps_pos.le (C.inv_mem y.1 y.2), C.tubeMap_inv y.1 y.2]

/-- **The `t = 1` stage on the tube is the (capped) blow-up composite.** -/
theorem blowPsi_apply_one (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (y : ↥C.U) :
    Work.Tubular.tubeMap E (cap E ε (radialRescale E (blowPsi ε 1) (C.inv y.1)))
      = Work.Tubular.tubeMap E (cap E ε (Work.Tubular.normalBlowUp E ε (C.inv y.1))) := by
  rw [radialRescale_blowPsi_one]

/-- **The `t = 0` stage is the identity** (on the closed `ε`-disc bundle). -/
theorem cap_radialRescale_blowPsi_zero
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (hε : 0 < ε) {p : Work.Tubular.NormalTotal E}
    (hp : Work.Tubular.normalNorm E p ≤ ε) :
    cap E ε (radialRescale E (blowPsi ε 0) p) = p := by
  rw [radialRescale_eq_self E _ (by simp)]
  exact cap_eq_self_of_le E hε.le hp

/-! ## Joint continuity of the family `t ↦ blowPsi ε t`

`blowPsi ε t r = 1 + t * (ε * (ε - r)⁻¹ - 1)` is **not** continuous on all of `ℝ × ℝ`: it is
unbounded as `r → ε` when `t ≠ 0`.  The honest statement — and the one the geometry needs — is
continuity on the region `r < ε`, which is where `C.inv` of the open tube lands
(`C.normalNorm_inv_lt`).  This is the local form of `continuous_transT_family` for this family. -/

/-- **The coefficient family is continuous on the good region `r < ε`.** -/
theorem continuousOn_blowPsi (ε : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => blowPsi ε q.1 q.2) {q | q.2 < ε} := by
  have hne : ∀ q ∈ ({q : ℝ × ℝ | q.2 < ε}), ε - q.2 ≠ 0 := by
    intro q hq
    exact ne_of_gt (by simpa using hq)
  have hsub : ContinuousOn (fun q : ℝ × ℝ => ε - q.2) {q | q.2 < ε} :=
    continuous_const.sub continuous_snd |>.continuousOn
  have hinv : ContinuousOn (fun q : ℝ × ℝ => (ε - q.2)⁻¹) {q | q.2 < ε} :=
    hsub.inv₀ hne
  have h1 : ContinuousOn (fun q : ℝ × ℝ => 1 + q.1 * (ε * (ε - q.2)⁻¹ - 1)) {q | q.2 < ε} :=
    continuous_const.continuousOn.add
      ((continuous_fst.continuousOn.mul
        ((continuous_const.continuousOn.mul hinv).sub continuous_const.continuousOn)))
  refine h1.congr ?_
  intro q _
  rfl

/-- The same, in terms of the normal norm of a point of `ν` (still on the good region). -/
theorem continuousOn_blowPsi_normalNorm
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (ε : ℝ) :
    ContinuousOn (fun q : ℝ × Work.Tubular.NormalTotal E =>
      blowPsi ε q.1 (Work.Tubular.normalNorm E q.2))
      {q | Work.Tubular.normalNorm E q.2 < ε} := by
  have hcont : Continuous fun q : ℝ × Work.Tubular.NormalTotal E =>
      ε - Work.Tubular.normalNorm E q.2 :=
    continuous_const.sub ((Work.Tubular.continuous_normalNorm E).comp continuous_snd)
  have hne : ∀ q ∈ ({q : ℝ × Work.Tubular.NormalTotal E |
      Work.Tubular.normalNorm E q.2 < ε}), ε - Work.Tubular.normalNorm E q.2 ≠ 0 := by
    intro q hq
    exact ne_of_gt (by simpa using hq)
  have hinv : ContinuousOn (fun q : ℝ × Work.Tubular.NormalTotal E =>
      (ε - Work.Tubular.normalNorm E q.2)⁻¹) {q | Work.Tubular.normalNorm E q.2 < ε} :=
    hcont.continuousOn.inv₀ hne
  have h1 : ContinuousOn (fun q : ℝ × Work.Tubular.NormalTotal E =>
      1 + q.1 * (ε * (ε - Work.Tubular.normalNorm E q.2)⁻¹ - 1))
      {q | Work.Tubular.normalNorm E q.2 < ε} :=
    continuous_const.continuousOn.add (continuous_fst.continuousOn.mul
      ((continuous_const.continuousOn.mul hinv).sub continuous_const.continuousOn))
  refine h1.congr ?_
  intro q _
  rfl

/-! ## `ContinuousOn` form of the radial rescaling on the good region -/

/-- **The family of radial rescalings is continuous on the region `normalNorm < ε`.**

This is `cmc_continuous_radialRescale` (`chartModelClass_span_top.lean`) with the global continuity of
`φ` replaced by `continuousOn_blowPsi_normalNorm`, which is all that is available — and all that is
needed, since `C.normalNorm_inv_lt` puts `C.inv` of the open tube inside this region.  The
`ContinuousOn` statement is proved by reducing to the restriction on the subtype, where the
`prodMk`/`subtype_mk` pattern applies verbatim. -/
theorem continuousOn_radialRescale_blowPsi
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (ε : ℝ) :
    ContinuousOn (fun q : ℝ × Work.Tubular.NormalTotal E =>
      radialRescale E (blowPsi ε q.1) q.2)
      {q | Work.Tubular.normalNorm E q.2 < ε} := by
  have hgood : Continuous fun q : ↥{q : ℝ × Work.Tubular.NormalTotal E |
      Work.Tubular.normalNorm E q.2 < ε} =>
      radialRescale E (blowPsi ε q.1.1) q.1.2 := by
    have hφ : Continuous fun q : ↥{q : ℝ × Work.Tubular.NormalTotal E |
        Work.Tubular.normalNorm E q.2 < ε} =>
        blowPsi ε q.1.1 (Work.Tubular.normalNorm E q.1.2) :=
      (continuousOn_blowPsi_normalNorm E ε).comp_continuous continuous_subtype_val
        (fun q => q.2)
    have hnv : Continuous fun q : ↥{q : ℝ × Work.Tubular.NormalTotal E |
        Work.Tubular.normalNorm E q.2 < ε} =>
        ((q.1.2 : Work.Tubular.NormalTotal E) : V.pt × Work.Tubular.Euc (8 + k)) :=
      continuous_subtype_val.comp continuous_subtype_val.snd
    have h1 : Continuous fun q : ↥{q : ℝ × Work.Tubular.NormalTotal E |
        Work.Tubular.normalNorm E q.2 < ε} =>
        (((q.1.2 : Work.Tubular.NormalTotal E) :
              V.pt × Work.Tubular.Euc (8 + k)).1,
          blowPsi ε q.1.1 (Work.Tubular.normalNorm E q.1.2)
            • ((q.1.2 : Work.Tubular.NormalTotal E) :
                V.pt × Work.Tubular.Euc (8 + k)).2) :=
      hnv.fst.prodMk (hφ.smul hnv.snd)
    have h2 : ∀ q : ↥{q : ℝ × Work.Tubular.NormalTotal E |
        Work.Tubular.normalNorm E q.2 < ε},
        (((q.1.2 : Work.Tubular.NormalTotal E) :
              V.pt × Work.Tubular.Euc (8 + k)).1,
          blowPsi ε q.1.1 (Work.Tubular.normalNorm E q.1.2)
            • ((q.1.2 : Work.Tubular.NormalTotal E) :
                V.pt × Work.Tubular.Euc (8 + k)).2) ∈
        {p : V.pt × Work.Tubular.Euc (8 + k) |
          p.2 ∈ Work.Tubular.normalSpace E p.1} :=
      fun q => Submodule.smul_mem (Work.Tubular.normalSpace E q.1.2.1.1) _ q.1.2.2
    exact h1.subtype_mk h2
  rw [continuousOn_iff_continuous_domRestrict]
  exact hgood

/-! ## Global continuity of a fibrewise radial rescaling, and of the capping -/

/-- **Global continuity of a fibrewise radial rescaling with a continuous coefficient** (the ambient
argument of `cmc_continuous_radialRescale`, repeated here so that `blowPsi.lean` stays independent of
the main file). -/
theorem continuous_radialRescale_of_continuous
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {φ : ℝ → ℝ}
    (hφ : Continuous φ) : Continuous (radialRescale E φ) := by
  have h1 : Continuous fun p : Work.Tubular.NormalTotal E =>
      (((p : V.pt × Work.Tubular.Euc (8 + k)).1,
        φ (Work.Tubular.normalNorm E p) •
          (p : V.pt × Work.Tubular.Euc (8 + k)).2)) :=
    (continuous_subtype_val.fst).prodMk
      ((hφ.comp (Work.Tubular.continuous_normalNorm E)).smul continuous_subtype_val.snd)
  have h2 : ∀ p : Work.Tubular.NormalTotal E,
      ((p : V.pt × Work.Tubular.Euc (8 + k)).1,
        φ (Work.Tubular.normalNorm E p) •
          (p : V.pt × Work.Tubular.Euc (8 + k)).2) ∈
      {q : V.pt × Work.Tubular.Euc (8 + k) | q.2 ∈ Work.Tubular.normalSpace E q.1} :=
    fun p => Submodule.smul_mem (Work.Tubular.normalSpace E p.1.1) _ p.2
  exact h1.subtype_mk h2

/-- **The capping is continuous.** -/
theorem continuous_cap (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (hε : 0 < ε) : Continuous (cap E ε) :=
  continuous_radialRescale_of_continuous E (continuous_capCoeff hε)

/-! ## Joint continuity of the `t`-th stage on the open tube -/

/-- **The `t`-th stage of the homotopy, as a function of `(t, y)` with `y` in the open tube, is
jointly continuous.**

The domain is `unitInterval × ↥C.openTube`: `C.inv` of the open tube lands in the good region
`{normalNorm < ε}` (`C.normalNorm_inv_lt`), which is exactly where `continuousOn_radialRescale_blowPsi`
applies; `cap` (`continuous_cap`) then returns the point to the closed tube and `tubeMap` reads it in
the ambient space.  Nothing is claimed on the *closed* tube: there `normalNorm (C.inv y) = ε` is
possible and `blowPsi` is discontinuous (see the header of this file). -/
theorem continuous_blowPsiStage
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) :
    Continuous fun q : unitInterval × ↥C.openTube =>
      Work.Tubular.tubeMap E (cap E ε (radialRescale E (blowPsi ε ((q.1 : unitInterval) : ℝ))
        (C.inv (q.2.1 : Work.Tubular.Euc (8 + k))))) := by
  have hinv : Continuous fun q : unitInterval × ↥C.openTube =>
      C.inv (q.2.1 : Work.Tubular.Euc (8 + k)) :=
    C.continuousOn_inv.comp_continuous (continuous_subtype_val.comp continuous_snd)
      (fun q => C.openTube_subset_U q.2.2)
  have hmap : Continuous fun q : unitInterval × ↥C.openTube =>
      (((q.1 : unitInterval) : ℝ), C.inv (q.2.1 : Work.Tubular.Euc (8 + k))) :=
    (continuous_subtype_val.comp continuous_fst).prodMk hinv
  have hgood : ∀ q : unitInterval × ↥C.openTube,
      (((q.1 : unitInterval) : ℝ), C.inv (q.2.1 : Work.Tubular.Euc (8 + k)))
        ∈ {p : ℝ × Work.Tubular.NormalTotal E | Work.Tubular.normalNorm E p.2 < ε} :=
    fun q => C.normalNorm_inv_lt q.2.2
  have hstg : Continuous fun q : unitInterval × ↥C.openTube =>
      radialRescale E (blowPsi ε ((q.1 : unitInterval) : ℝ))
        (C.inv (q.2.1 : Work.Tubular.Euc (8 + k))) :=
    (continuousOn_radialRescale_blowPsi E ε).comp_continuous hmap hgood
  exact (Work.Tubular.continuous_tubeMap E).comp ((continuous_cap E C.eps_pos).comp hstg)

/-! ## The homotopy itself: the identity on the open tube ⟶ the collapse's local form -/

/-- The inclusion of the open tube into the closed tube, as an element of the mapping space. -/
noncomputable def openTubeIncl
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) : C(↥C.openTube, ↥C.U) :=
  ⟨fun y => ⟨y.1, C.openTube_subset_U y.2⟩,
    Continuous.subtype_mk continuous_subtype_val (fun y => C.openTube_subset_U y.2)⟩

/-- The `t`-th stage of the homotopy, as a map from the open tube into the closed tube.  (The index
is a `unitInterval`, so that the stage is the composition of `continuous_blowPsiStage` with the
inclusion `y ↦ (t, y)`.) -/
noncomputable def blowPsiStage
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (t : unitInterval) : C(↥C.openTube, ↥C.U) :=
  ⟨fun y => ⟨Work.Tubular.tubeMap E
      (cap E ε (radialRescale E (blowPsi ε ((t : unitInterval) : ℝ)) (C.inv y.1))),
      C.mem_U _ (cap_mem_disc E C.eps_pos.le _)⟩,
    Continuous.subtype_mk
      ((continuous_blowPsiStage E C).comp (continuous_const.prodMk continuous_id)) _⟩

/-- **The homotopy: the identity of the open tube, through positive fibrewise radial rescalings of the
tube coordinates, to the collapse's local form `tubeMap ∘ cap ∘ normalBlowUp ∘ C.inv`.**

The codomain is the **closed** tube `C.U` and the domain the **open** tube: at `t = 1` the capped
blow-up may land on the norm-`ε` boundary, and on the closed tube `blowPsi` is discontinuous.  This is
the corrected, true form of (F1); the *global* form (a homotopy of self-maps of `C.U`) is false — see
`NOTE_AMBIENTV2_PLAN5.md`, "ADDENDUM part 2". -/
noncomputable def blowPsiHomotopy
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) :
    ContinuousMap.Homotopy (blowPsiStage E C 0) (blowPsiStage E C 1) where
  toContinuousMap :=
    ⟨fun q : unitInterval × ↥C.openTube =>
      ⟨Work.Tubular.tubeMap E (cap E ε (radialRescale E (blowPsi ε ((q.1 : unitInterval) : ℝ))
          (C.inv q.2.1))), C.mem_U _ (cap_mem_disc E C.eps_pos.le _)⟩,
      Continuous.subtype_mk (continuous_blowPsiStage E C) _⟩
  map_zero_left := fun _ => rfl
  map_one_left := fun _ => rfl

/-- **The `t = 0` end of the homotopy is the identity** (the inclusion of the open tube). -/
theorem blowPsiStage_zero
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) :
    blowPsiStage E C 0 = openTubeIncl E C := by
  apply ContinuousMap.ext
  intro y
  apply Subtype.ext
  exact blowPsi_apply_zero E C (⟨y.1, C.openTube_subset_U y.2⟩ : ↥C.U)

/-- **The `t = 1` end of the homotopy is the collapse's local form** `tubeMap ∘ cap ∘ normalBlowUp ∘
C.inv` on the open tube, with the strict inequality `normalNorm (C.inv y) < ε` available. -/
theorem blowPsiStage_one_apply
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (y : ↥C.openTube) :
    (blowPsiStage E C 1 y : ↥C.U).1
      = Work.Tubular.tubeMap E (cap E ε (Work.Tubular.normalBlowUp E ε (C.inv y.1))) := by
  show Work.Tubular.tubeMap E
      (cap E ε (radialRescale E (blowPsi ε ((1 : unitInterval) : ℝ)) (C.inv y.1))) = _
  rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]
  rw [radialRescale_blowPsi_one]

/-! ## The stages as maps of pairs -/

/-- **The tube inverse of a stage is the capped interpolated rescaling.** -/
theorem blowPsiStage_inv_eq
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (t : unitInterval) (y : ↥C.openTube) :
    C.inv (blowPsiStage E C t y).1
      = cap E ε (radialRescale E (blowPsi ε ((t : unitInterval) : ℝ)) (C.inv y.1)) := by
  show C.inv (Work.Tubular.tubeMap E
      (cap E ε (radialRescale E (blowPsi ε ((t : unitInterval) : ℝ)) (C.inv y.1)))) = _
  exact C.inv_tubeMap _ (cap_mem_disc E C.eps_pos.le _)

/-- **Every stage is a map of pairs** `(openTube, openTube∖E.e(V)) → (C.U, tubeInvPunct)`.

Both the domain's excluded set and the codomain's are described through `C.inv` (a point is excluded
iff its tube inverse is nonzero), and the membership is exactly
`mem_normalNonzero_cap_radialRescale_blowPsi`: each stage keeps the normal vector nonzero, which is
where the strict inequality `normalNorm (C.inv y) < ε` of the open tube is used. -/
theorem blowPsiStage_inv_mem
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (t : unitInterval) {y : ↥C.openTube}
    (hy : C.inv y.1 ∈ Work.Tubular.normalNonzero E) :
    C.inv (blowPsiStage E C t y).1 ∈ Work.Tubular.normalNonzero E := by
  rw [blowPsiStage_inv_eq]
  exact mem_normalNonzero_cap_radialRescale_blowPsi E C.eps_pos
    (unitInterval.nonneg t) (unitInterval.le_one t) (C.normalNorm_inv_lt y.2) hy

/-! ## The transport: all stages induce the same map on relative homology -/

/-- The punctured part of the open tube, described through the tube inverse (a point is excluded iff
its tube inverse is nonzero).  This is the source pair's excluded set for the transport. -/
def openTubePunct
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) : Set ↥C.openTube :=
  {y | C.inv y.1 ∈ Work.Tubular.normalNonzero E}

/-- **Homotopy invariance: the two ends of `blowPsiHomotopy` induce the same map on relative
homology** of the pair `(openTube, openTube∖E.e(V)) → (C.U, tubeInvPunct)`.

This is `Work.PTGeometric.HOF.relChainsMapOf_homologyMap_eq_of_homotopic` applied to the explicit
homotopy, exactly as `radialRescale_homologyMap_id` applies it on the `ν`-side; the pair condition
`hH` is `blowPsiStage_inv_mem`. -/
theorem blowPsi_relChainsMapOf_homologyMap_eq
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (n : ℕ) :
    HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf
        (TopCat.of ↥C.openTube) (TopCat.of ↥C.U) (openTubePunct E C)
        (Work.ThomBordism.tubeInvPunct E C)
        (TopCat.ofHom (blowPsiStage E C 0))
        (TopCat.ofHom ⟨fun y => ⟨blowPsiStage E C 0 y,
            blowPsiStage_inv_mem E C 0 y.2⟩,
          Continuous.subtype_mk ((blowPsiStage E C 0).continuous.comp continuous_subtype_val) _⟩)
        (by apply TopCat.ext; intro a; rfl)) n
      = HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf
        (TopCat.of ↥C.openTube) (TopCat.of ↥C.U) (openTubePunct E C)
        (Work.ThomBordism.tubeInvPunct E C)
        (TopCat.ofHom (blowPsiStage E C 1))
        (TopCat.ofHom ⟨fun y => ⟨blowPsiStage E C 1 y,
            blowPsiStage_inv_mem E C 1 y.2⟩,
          Continuous.subtype_mk ((blowPsiStage E C 1).continuous.comp continuous_subtype_val) _⟩)
        (by apply TopCat.ext; intro a; rfl)) n := by
  refine Work.PTGeometric.HOF.relChainsMapOf_homologyMap_eq_of_homotopic
    (X := TopCat.of ↥C.openTube) (Y := TopCat.of ↥C.U)
    (A := openTubePunct E C) (B := Work.ThomBordism.tubeInvPunct E C)
    (f₀ := TopCat.ofHom (blowPsiStage E C 0))
    (f₁ := TopCat.ofHom (blowPsiStage E C 1))
    (g₀ := TopCat.ofHom ⟨fun y => ⟨blowPsiStage E C 0 y,
        blowPsiStage_inv_mem E C 0 y.2⟩,
      Continuous.subtype_mk ((blowPsiStage E C 0).continuous.comp continuous_subtype_val) _⟩)
    (g₁ := TopCat.ofHom ⟨fun y => ⟨blowPsiStage E C 1 y,
        blowPsiStage_inv_mem E C 1 y.2⟩,
      Continuous.subtype_mk ((blowPsiStage E C 1).continuous.comp continuous_subtype_val) _⟩)
    ?_ ?_ (blowPsiHomotopy E C)
    (fun t x hx => blowPsiStage_inv_mem E C t hx) n

/-! ## The inclusion as a map of pairs, and the composed form of (F1) -/

/-- The inclusion `↥C.openTube → ↥C.U` is a map of pairs `(openTube, openTubePunct) → (C.U, tubeInvPunct)`
— on the open tube the two excluded sets are described by the *same* condition `C.inv y.1 ≠ 0`, so the
membership proof is `y.2` itself. -/
theorem openTubeIncl_inv_mem
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (y : ↥(openTubePunct E C)) :
    C.inv (openTubeIncl E C y).1 ∈ Work.Tubular.normalNonzero E :=
  y.2

/-! ## Named pair-conditions for the `RelHmapOf` form of (F1) -/

/-- The complement of the open tube's punctured set is the *included* set of the pair, so
`x ∉ (openTubePunct E C)ᶜ` is `x ∈ openTubePunct E C`.  Named so that the pair-conditions below can be
supplied to `RelHmapOf` as short terms (writing the `simp` inline in a `RelHmapOf` statement makes the
elaborator `whnf`-timeout). -/
theorem mem_openTubePunct_of_not_mem_compl
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) {x : ↥C.openTube} (hx : x ∉ (openTubePunct E C)ᶜ) :
    x ∈ openTubePunct E C := by
  simpa only [Set.mem_compl_iff, not_not] using hx

/-- **Every stage is a map of pairs**, in the `RelHmapOf` (complement) convention. -/
theorem blowPsi_stage_pair
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (t : unitInterval) :
    ∀ x : ↥C.openTube, x ∉ (openTubePunct E C)ᶜ →
      (TopCat.ofHom (blowPsiStage E C t)) x ∉ (Work.ThomBordism.tubeInvPunct E C)ᶜ :=
  fun x hx => by
    simp only [Set.mem_compl_iff, not_not] at hx ⊢
    exact blowPsiStage_inv_mem E C t hx

/-- The inclusion is a map of pairs, in the `RelHmapOf` (complement) convention. -/
theorem openTubeIncl_pair
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) :
    ∀ x : ↥C.openTube, x ∉ (openTubePunct E C)ᶜ →
      (TopCat.ofHom (openTubeIncl E C)) x ∉ (Work.ThomBordism.tubeInvPunct E C)ᶜ :=
  fun x hx => by
    simp only [Set.mem_compl_iff, not_not] at hx ⊢
    exact openTubeIncl_inv_mem E C ⟨x, hx⟩

/-- **(F1), the corrected form.**  On the relative homology of the pair
`(openTube, openTube∖E.e(V)) → (C.U, tubeInvPunct)`, the **collapse's local form**
`tubeMap ∘ cap ∘ normalBlowUp ∘ C.inv` (the `t = 1` end of `blowPsiHomotopy`) induces the **same** map
as the inclusion of the open tube (the `t = 0` end, by `blowPsiStage_zero`).

Stated at the `RelHmapOf` level so that no compatibility (`g`/`w`) data appear in the statement:
`blowPsiStage_zero` is a *proved* equality, not a definitional one, so rewriting it inside
`relChainsMapOf` produces `Eq.mp`-casts of Prop-valued fields, which `RelHmapOf_congr` absorbs.

The *global* form — a homotopy of self-maps of the closed tube `C.U` — is FALSE: `blowCoeff` vanishes
on the norm-`ε` sphere, so `normalBlowUp` collapses that sphere onto the zero section and `Φ̂` is not a
map of pairs there.  See `NOTE_AMBIENTV2_PLAN5.md`. -/
theorem blowPsiStage_one_RelHmapOf_eq_incl
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (n : ℕ) :
    Work.PTGeometric.HOF.RelHmapOf n (TopCat.ofHom (blowPsiStage E C 1))
        (openTubePunct E C)ᶜ (Work.ThomBordism.tubeInvPunct E C)ᶜ
        (blowPsi_stage_pair E C 1)
      = Work.PTGeometric.HOF.RelHmapOf n (TopCat.ofHom (openTubeIncl E C))
        (openTubePunct E C)ᶜ (Work.ThomBordism.tubeInvPunct E C)ᶜ
        (openTubeIncl_pair E C) := by
  have h1 : Work.PTGeometric.HOF.RelHmapOf n (TopCat.ofHom (blowPsiStage E C 0))
        (openTubePunct E C)ᶜ (Work.ThomBordism.tubeInvPunct E C)ᶜ
        (blowPsi_stage_pair E C 0)
      = Work.PTGeometric.HOF.RelHmapOf n (TopCat.ofHom (blowPsiStage E C 1))
        (openTubePunct E C)ᶜ (Work.ThomBordism.tubeInvPunct E C)ᶜ
        (blowPsi_stage_pair E C 1) :=
    Work.PTGeometric.HOF.RelHmapOf_homotopic
      (blowPsi_stage_pair E C 0) (blowPsi_stage_pair E C 1)
      (blowPsiHomotopy E C) (fun t x hx => blowPsi_stage_pair E C t x hx)
  have h2 : Work.PTGeometric.HOF.RelHmapOf n (TopCat.ofHom (blowPsiStage E C 0))
        (openTubePunct E C)ᶜ (Work.ThomBordism.tubeInvPunct E C)ᶜ
        (blowPsi_stage_pair E C 0)
      = Work.PTGeometric.HOF.RelHmapOf n (TopCat.ofHom (openTubeIncl E C))
        (openTubePunct E C)ᶜ (Work.ThomBordism.tubeInvPunct E C)ᶜ
        (openTubeIncl_pair E C) :=
    Work.PTGeometric.HOF.RelHmapOf_congr
      (congrArg TopCat.ofHom (blowPsiStage_zero E C))
      (blowPsi_stage_pair E C 0) (openTubeIncl_pair E C)
  exact h1.symm.trans h2

/-! ## (F2), the pullback half: the local form is indistinguishable from the inclusion -/

/-- **(F2), pullback half.**  As pullbacks on relative cohomology, the **collapse's local form**
`tubeMap ∘ cap ∘ normalBlowUp ∘ C.inv` (the `t = 1` stage) and the **inclusion** of the open tube
(the `t = 0` stage, cf. `blowPsiStage_zero`) induce the **same** map
`H^m(C.U, tubeInvPunct) → H^m(openTube, openTubePunct)`.

This is the cohomological twin of `blowPsiStage_one_RelHmapOf_eq_incl` (whose proof is the *homology*
statement, `relChainsMapOf_homologyMap_eq_of_homotopic`), and its proof is correspondingly direct:
`Work.Thom.relCohMap_homotopic` on the explicit homotopy `blowPsiHomotopy` — which *is* a homotopy
through maps of pairs by `blowPsi_stage_pair`/`blowPsiStage_inv_mem` — followed by `relCohMap_congrA`
for `blowPsiStage_zero`.

It is the statement the value's *class* side consumes: on the open tube the capped blow-up may be
replaced by the identity, which is what removes `normalBlowUp` from the collapse's local form without
ever mentioning the closed tube (where the corresponding claim is FALSE — see the module header and
`NOTE_AMBIENTV2_PLAN5.md`). -/
theorem blowPsiStage_one_relCohMap_eq_incl
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (m : ℕ) :
    Work.Thom.relCohMap (blowPsiStage E C 1) (openTubePunct E C)
        (Work.ThomBordism.tubeInvPunct E C)
        (fun y hy => blowPsiStage_inv_mem E C 1 hy) ℤ m
      = Work.Thom.relCohMap (openTubeIncl E C) (openTubePunct E C)
        (Work.ThomBordism.tubeInvPunct E C)
        (fun y hy => openTubeIncl_inv_mem E C ⟨y, hy⟩) ℤ m := by
  have h1 : Work.Thom.relCohMap (blowPsiStage E C 0) (openTubePunct E C)
        (Work.ThomBordism.tubeInvPunct E C)
        (fun y hy => blowPsiStage_inv_mem E C 0 hy) ℤ m
      = Work.Thom.relCohMap (blowPsiStage E C 1) (openTubePunct E C)
        (Work.ThomBordism.tubeInvPunct E C)
        (fun y hy => blowPsiStage_inv_mem E C 1 hy) ℤ m :=
    Work.Thom.relCohMap_homotopic (openTubePunct E C) (Work.ThomBordism.tubeInvPunct E C)
      (fun y hy => blowPsiStage_inv_mem E C 0 hy)
      (fun y hy => blowPsiStage_inv_mem E C 1 hy)
      (blowPsiHomotopy E C) (fun t x hx => blowPsiStage_inv_mem E C t hx) ℤ m
  have h2 : Work.Thom.relCohMap (openTubeIncl E C) (openTubePunct E C)
        (Work.ThomBordism.tubeInvPunct E C)
        (fun y hy => openTubeIncl_inv_mem E C ⟨y, hy⟩) ℤ m
      = Work.Thom.relCohMap (blowPsiStage E C 0) (openTubePunct E C)
        (Work.ThomBordism.tubeInvPunct E C)
        (fun y hy => blowPsiStage_inv_mem E C 0 hy) ℤ m :=
    Work.Thom.relCohMap_congrA (openTubePunct E C) (Work.ThomBordism.tubeInvPunct E C)
      (blowPsiStage_zero E C).symm
      (fun y hy => openTubeIncl_inv_mem E C ⟨y, hy⟩)
      (fun y hy => blowPsiStage_inv_mem E C 0 hy) ℤ m
  exact h1.symm.trans h2.symm

/-! ## (F2c), pointwise: the collapse read in the tube chart -/

/-- **(F2c), pointwise.**  On the cube points whose image lies in the *open* tube, the collapse loop
`tubeGenLoopOnePoint C g hg hR hbox` is `g` applied to the cube point, and `hg2` pins `g` there to be
the **pushforward along the tube chart** followed by the blow-up:

  `γ(t) = some (normalBlowUp E ε (C.inv (cubeToEuc R t)))`.

This is the identity whence `δ` is a push-forward along a map whose local form is the collapse's, i.e.
the input of (F2c); it is what makes `hg2` (and hence the *tube chart*, and hence all datum-dependence)
enter the value.  Note it is only available on `C.openTube` — exactly the region where
`blowPsiStage E C 1` and (F1)/(F2)-pullback live. -/
theorem tubeGenLoopOnePoint_apply_of_mem_openTube
    {V : Work.ThomBordism.Man8} {k : ℕ} {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    {t : Fin (8 + k) → unitInterval}
    (ht : Work.Tubular.cubeToEuc (8 + k) R t ∈ C.openTube) :
    (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox).1 t
      = OnePoint.some (Work.Tubular.normalBlowUp E ε
          (C.inv (Work.Tubular.cubeToEuc (8 + k) R t))) := by
  show g (OnePoint.some (Work.Tubular.cubeToEuc (8 + k) R t)) = _
  exact hg2 _ ht

/-! ## (F2c), the bridge: the `hg2` form and the `blowPsiStage` form agree where `cap` fixes -/

/-- **(F2c), the bridge.**  Where the capping is inert on `normalBlowUp E ε (C.inv y)` — which is the
case on the neighbourhood `{normalNorm E (C.inv y) ≤ ε/2}` of the zero section, see
`cap_normalBlowUp_eq_self_of_le_half` — the collapse's chart form read in the **ν**-coordinates and the
`t = 1` stage of `blowPsiHomotopy` read in the **tube**-coordinates agree, as elements of the ambient
space:

  `tubeMap E (normalBlowUp E ε (C.inv y)) = (blowPsiStage E C 1 ⟨y, hy⟩ : ↥C.U).1`.

This is the identity that lets (the PROVED) `blowPsiStage_one_relCohMap_eq_incl` / (F1) be applied to
the collapse: `hg2` presents the collapse as `some (normalBlowUp E ε (C.inv ·))`, and on this region
that is `some` of the tube-coordinate avatar of `blowPsiStage E C 1`.  The cap-fixing hypothesis is
kept explicit because it is exactly the arithmetic fact isolated in
`cap_normalBlowUp_eq_self_of_le_half`. -/
theorem tubeMap_normalBlowUp_eq_stage_of_cap_eq
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) {y : Work.Tubular.Euc (8 + k)} (hy : y ∈ C.openTube)
    (hcap : cap E ε (Work.Tubular.normalBlowUp E ε (C.inv y))
      = Work.Tubular.normalBlowUp E ε (C.inv y)) :
    Work.Tubular.tubeMap E (Work.Tubular.normalBlowUp E ε (C.inv y))
      = (blowPsiStage E C 1 ⟨y, hy⟩ : ↥C.U).1 := by
  rw [show (blowPsiStage E C 1 ⟨y, hy⟩ : ↥C.U).1 = Work.Tubular.tubeMap E
      (cap E ε (radialRescale E (blowPsi ε 1) (C.inv y))) from rfl,
    radialRescale_blowPsi_one, hcap]

/-- **(F2c), the bridge, complete.**  On the neighbourhood `{normalNorm E (C.inv y) ≤ ε/2}` of the zero
section — which contains the base point `E.e x` of the collapse — the collapse's chart form in the
**ν**-coordinates equals the `t = 1` stage of `blowPsiHomotopy` read in the **tube**-coordinates.  The
cap-fixing hypothesis of `tubeMap_normalBlowUp_eq_stage_of_cap_eq` is discharged here by the
**already-proved** `Work.ThomBordism.cap_normalBlowUp_eq_self` (in `cappedChart_homotopic_translation`),
so this is the usable form.

Together with `tubeGenLoopOnePoint_apply_of_mem_openTube` (the collapse in the chart) and the PROVED
`blowPsiStage_one_relCohMap_eq_incl`/(F1), this is what carries the collapse's local form into the tube
world where the blow-up can be cancelled.  The restriction to `≤ ε/2` is essential *and* harmless: the
two forms genuinely differ for `ε/2 < normalNorm < ε`, but the cycle that travels with them is localised
at the base point (see `NOTE_AMBIENTV2_PLAN5.md`, part 14). -/
theorem tubeMap_normalBlowUp_eq_stage_of_le_half
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) {y : Work.Tubular.Euc (8 + k)} (hy : y ∈ C.openTube)
    (h2 : Work.Tubular.normalNorm E (C.inv y) ≤ ε / 2) :
    Work.Tubular.tubeMap E (Work.Tubular.normalBlowUp E ε (C.inv y))
      = (blowPsiStage E C 1 ⟨y, hy⟩ : ↥C.U).1 :=
  tubeMap_normalBlowUp_eq_stage_of_cap_eq E C hy
    (Work.ThomBordism.cap_normalBlowUp_eq_self E C.eps_pos h2)

/-- **(F2c), function level.**  On the cube points whose image lies in the open tube **and** whose tube
inverse has norm `≤ ε/2`, the collapse loop factors through the tube world:

  `γ(t) = some (C.inv ((blowPsiStage E C 1 ⟨cubeToEuc R t, _⟩ : ↥C.U).1))`.

The right-hand side is `some ∘ C.inv` applied to the tube-coordinate avatar of the `t = 1` stage, i.e.
the collapse as seen through the tube chart; the left-hand side is the same point in ν-coordinates
(`tubeGenLoopOnePoint_apply_of_mem_openTube`).  This is the map-level input of (F2c): on this region
`blowPsiStage E C 1` may be replaced by the inclusion (PROVED `blowPsiStage_one_relCohMap_eq_incl`),
which removes `cap`/`normalBlowUp` from the collapse's local form. -/
theorem collapseLoop_eq_some_inv_stage
    {V : Work.ThomBordism.Man8} {k : ℕ} {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    {t : Fin (8 + k) → unitInterval}
    (ht : Work.Tubular.cubeToEuc (8 + k) R t ∈ C.openTube)
    (h2 : Work.Tubular.normalNorm E (C.inv (Work.Tubular.cubeToEuc (8 + k) R t)) ≤ ε / 2) :
    (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox).1 t
      = OnePoint.some (C.inv ((blowPsiStage E C 1
          ⟨Work.Tubular.cubeToEuc (8 + k) R t, ht⟩ : ↥C.U).1)) := by
  have hble : Work.Tubular.normalNorm E
      (Work.Tubular.normalBlowUp E ε (C.inv (Work.Tubular.cubeToEuc (8 + k) R t))) ≤ ε := by
    rw [← Work.ThomBordism.cap_normalBlowUp_eq_self E C.eps_pos h2]
    exact cap_mem_disc E C.eps_pos.le _
  rw [tubeGenLoopOnePoint_apply_of_mem_openTube C g hg hg2 hR hbox ht]
  congr 1
  rw [← tubeMap_normalBlowUp_eq_stage_of_le_half E C ht h2]
  exact (C.inv_tubeMap _ hble).symm


end

end Work.ThomBordism
