import Mathlib
import Submission.Work.Drive.geometricCount
import Submission.Work.Drive.refPlaneLevel
import Submission.Work.Drive.clampedSweepImage
import Submission.Work.Drive.cutClassImage
import Submission.Work.Drive.sqDisk_surjective
import Submission.Work.Drive.sqDisk_foldBox_existsUnique
import Submission.Work.Drive.linVecC_smul_surjective
import Submission.Work.Drive.linPlaneChartNormals
import Submission.Work.Drive.seamEssentiality
import Submission.Work.Drive.coreLoopClosed
import Submission.Work.Drive.injOn_coreLoop_Ico_of_isPlaneChart

/-!
# The reference factor `(F1)` of `hn2`: the loop-vs-sweep count is a *class* count

`Work.Drive.coreMeetPt Q c P` is the set of *points of the capping space* lying both on the core loop
of the chart `Q` and on the clamped radial sweep of the plane presentation `P`; its cardinality is the
parameterisation-free pairing `Work.Drive.coreSideCountPt`.  For the **reference plane**
`P = diskPlane (linPlaneChart φ lam hlampos)` — the square presentation of the linear projective plane
`projLine (linSub φ)` sitting at the single level `lam > c` — this file identifies that meet set with a
set of *loop parameters*:

> `coreMeetPt Q c P = coreLoop Q '' {t ∈ [0,1] | class (coreLoop Q t) ∈ projLine (linSub φ)}`,

and consequently its parity with the parity of the number of parameters at which the loop's class
meets the reference plane.  That reduces the factor `(F1)` of `HN2_REFERENCE_STATUS.md` §2 to the
elementary count of the zeros of `t ↦ ℓ (V t)` for a lift `V` of the class loop and the functional `ℓ`
of the plane — which is `Work.Drive.odd_ncard_zeros_of_anti_lift` once the essentiality
(`Work.Drive.exists_neg_parallelism_of_planeChart`) is fed in.

The three ingredients of the identification are all on disk:

* `Work.Drive.image_clampedSweep` (the exact image of a clamped sweep: class of a box point of the
  plane, level between the truncation level and the plane's level) — specialised here to a plane of
  *constant* level;
* `Work.Drive.classImage_diskPlane_linPlaneChart` (the square presentation of a linear plane covers
  the whole projective plane);
* the *level band* of a plane chart (`Work.Drive.exists_levelBand_of_isPlaneChart`), which makes the
  level condition of the sweep's image automatic on the core loop.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-! ## 1. The image of a clamped sweep of a plane of constant level -/

/-- **The image of a clamped radial sweep of a plane of constant level.**  This is
`Work.Drive.image_clampedSweep` with the plane's level held constant on the box, so that the second
level bound is `lam` instead of `levelOf (P y)`. -/
theorem image_clampedSweep_constLevel (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) {lam : ℝ}
    (hPlam : ∀ a ∈ Submission.Drive.unitBox 1, levelOf (P a) = lam)
    (hclam : c < lam) :
    clampedSweep c ψ P '' Submission.Drive.unitBox 2 =
      {y : CappingSpace | (cappingSpaceHomeoProj y).2 ∈ classImage P ∧
        c ≤ levelOf y ∧ levelOf y ≤ lam} := by
  have hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y) := by
    intro y hy
    rw [hPlam y hy]
    exact le_of_lt hclam
  rw [image_clampedSweep c hc ψ hψ0 hψ1 hψ01 hcont P hr]
  ext p
  constructor
  · rintro ⟨y, hy, hcls, hcle, hler⟩
    exact ⟨mem_classImage.mpr ⟨y, hy, hcls.symm⟩, hcle,
      le_trans hler (le_of_eq (hPlam y hy))⟩
  · rintro ⟨hcls, hcle, hler⟩
    obtain ⟨y, hy, hcls'⟩ := mem_classImage.mp hcls
    exact ⟨y, hy, hcls'.symm, hcle,
      le_trans hler (le_of_eq (hPlam y hy).symm)⟩

/-! ## 2. The square presentation of a linear plane covers the whole plane -/

/-- **The standard disk model of `ℝP²` covers it, with the disk parameter.**  This is
`Work.Drive.exists_mk_linVecC_eq` with the normalization `‖z‖ ≤ 1` kept, which is what the square
presentation `diskPlane = Q ∘ sqDisk ∘ foldBox` consumes. -/
theorem exists_mk_linVecC_eq_disk (q : Projectivization ℝ (Eucl 3)) (hq : q ∈ projLine linStd) :
    ∃ z : ℂ, ‖z‖ ≤ 1 ∧ Projectivization.mk ℝ (linVecC z) (linVecC_ne_zero z) = q := by
  obtain ⟨v, hv0, hvU, rfl⟩ := hq
  have hv3 : v 3 = 0 := by
    have h := hvU
    rw [linStd_eq_ker_coord] at h
    simpa [linStdCoord_apply] using h
  have hvrepr : v = ofComplex (c₁ v) (((v 2 : ℝ) : ℂ)) :=
    (ofComplex_c₁_c₂_of_apply_three_eq_zero hv3).symm
  have hw : c₁ v ≠ 0 ∨ (v 2 : ℝ) ≠ 0 := by
    rcases eq_or_ne (c₁ v) 0 with h | h
    · right
      intro h2
      refine hv0 ?_
      rw [hvrepr, h, h2]
      ext i
      fin_cases i <;> simp [ofComplex]
    · exact Or.inl h
  obtain ⟨z, a, ha0, hz, haeq⟩ := linVecC_smul_surjective hw
  refine ⟨z, hz, ?_⟩
  rw [Projectivization.mk_eq_mk_iff' ℝ (linVecC z) v (linVecC_ne_zero z) hv0]
  refine ⟨a⁻¹, ?_⟩
  rw [hvrepr, ← haeq, smul_smul, inv_mul_cancel₀ ha0, one_smul]

/-- **The linear plane chart covers its plane with disk parameters.**  This is
`Work.Drive.exists_linPlaneChart_class_eq` with the normalization `‖z‖ ≤ 1`. -/
theorem exists_linPlaneChart_class_eq_disk (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (q : Projectivization ℝ (Eucl 3)) (hq : q ∈ projLine (linSub φ)) :
    ∃ z : ℂ, ‖z‖ ≤ 1 ∧ (cappingSpaceHomeoProj (linPlaneChart φ c hc z)).2 = q := by
  obtain ⟨w, hw0, hwU, rfl⟩ := hq
  obtain ⟨v, hvU, hvφ⟩ := Submodule.mem_map.mp hwU
  have hv0 : v ≠ 0 := fun h => hw0 (by rw [← hvφ, h, map_zero])
  obtain ⟨z, hz, hzcls⟩ :=
    exists_mk_linVecC_eq_disk (Projectivization.mk ℝ v hv0) ⟨v, hv0, hvU, rfl⟩
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' ℝ (linVecC z) v (linVecC_ne_zero z) hv0).mp hzcls
  refine ⟨z, hz, ?_⟩
  rw [cappingSpaceHomeoProj_linPlaneChart]
  refine (Projectivization.mk_eq_mk_iff' ℝ (φ (linVecC z)) w
    (fun h => linVecC_ne_zero z (φ.injective (by simpa using h))) hw0).mpr ⟨a, ?_⟩
  · have h1 : φ (a • v) = a • φ v := by simp
    have h2 : a • w = a • φ v := congrArg (fun x : Eucl 3 => a • x) hvφ.symm
    have h3 : φ (linVecC z) = φ (a • v) := congrArg (fun x : Eucl 3 => φ x) ha.symm
    exact h2.trans (h1.symm.trans h3.symm)

/-- **The class image of the square presentation of a linear plane is that plane.** -/
theorem classImage_diskPlane_linPlaneChart (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c) :
    classImage (diskPlane (linPlaneChart φ c hc)) = projLine (linSub φ) := by
  ext q
  constructor
  · intro hq
    obtain ⟨y, hy, hyq⟩ := mem_classImage.mp hq
    rw [diskPlane_apply] at hyq
    rw [← hyq]
    exact linPlaneChart_mem_projLine φ c hc (sqDisk (foldBox y))
  · intro hq
    obtain ⟨z, hz, hzcls⟩ := exists_linPlaneChart_class_eq_disk φ c hc q hq
    obtain ⟨y, ⟨hy, hyz⟩, -⟩ := sqDisk_foldBox_existsUnique z hz
    refine mem_classImage.mpr ⟨y, hy, ?_⟩
    rw [diskPlane_apply, hyz]
    exact hzcls


/-! ## 3. The reference meet set is a set of loop parameters -/

/-- **The reference meet set is a set of loop parameters, for an arbitrary cutoff `ψ`.**

The `n`-independent form of the identification below: the intersection of the core loop with the image
of the clamped sweep of the reference plane (at an arbitrary cutoff `ψ` with `ψ '' [0,1] = [0,1]`) is
exactly the set of loop values whose class lies in the plane.  Stating it for a general `ψ` makes it
robust under the *design's* choice of cutoff (`GEOMETRIC_LOCALITY_STATUS.md` §3 records that the design
has to replace `t ↦ 1 - t` by a cutoff whose range is `[0,1]`, e.g. `cosCut`, for the locality engine's
`hbox` to hold). -/
theorem clampedSweep_image_reference (Q : ℂ → CappingSpace) (φ : Eucl 3 ≃L[ℝ] Eucl 3)
    (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    {β lam : ℝ} (hβlam : β < lam) (hlampos : 0 < lam)
    (hclow : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z))
    (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β) :
    (coreLoop Q '' Set.Icc (0 : ℝ) 1) ∩
        (clampedSweep c ψ (diskPlane (linPlaneChart φ lam hlampos)) '' Submission.Drive.unitBox 2)
      = coreLoop Q '' {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
          (cappingSpaceHomeoProj (coreLoop Q t)).2 ∈ projLine (linSub φ)} := by
  have hclam : c < lam := by
    have h0 : ‖(0 : ℂ)‖ ≤ 1 := by norm_num
    linarith [hclow 0 h0, hβ 0 h0, hβlam]
  have hPlam : ∀ a ∈ Submission.Drive.unitBox 1,
      levelOf (diskPlane (linPlaneChart φ lam hlampos) a) = lam := by
    intro a _
    rw [diskPlane_apply, levelOf, level_linPlaneChart]
  have himg := image_clampedSweep_constLevel c hc ψ hψ0 hψ1 hψ01 hcont
    (diskPlane (linPlaneChart φ lam hlampos)) hPlam hclam
  rw [classImage_diskPlane_linPlaneChart] at himg
  have hlevel : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      c ≤ levelOf (coreLoop Q t) ∧ levelOf (coreLoop Q t) ≤ lam := by
    intro t _
    have hz : ‖Complex.exp (↑Real.pi * (↑t : ℂ) * Complex.I)‖ = 1 := by
      rw [show (↑Real.pi * (↑t : ℂ) * Complex.I)
          = ((Real.pi * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    show c ≤ levelOf (Q _) ∧ levelOf (Q _) ≤ lam
    exact ⟨hclow _ hz.le, le_trans (hβ _ hz.le) (le_of_lt hβlam)⟩
  ext y
  rw [Set.mem_inter_iff, himg, Set.mem_setOf_eq, Set.mem_image, Set.mem_image]
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hcls, -, -⟩
    exact ⟨t, ⟨ht, hcls⟩, rfl⟩
  · rintro ⟨t, ⟨ht, hcls⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, hcls, (hlevel t ht).1, (hlevel t ht).2⟩

/-- **The geometric meet set of the core loop with the sweep of the reference plane is the set of loop
parameters whose class lies in the plane** (cutoff `t ↦ 1 - t`, i.e. the design's `coreMeetPt`). -/
theorem coreMeetPt_reference_eq (Q : ℂ → CappingSpace) (φ : Eucl 3 ≃L[ℝ] Eucl 3)
    {β c lam : ℝ} (hc : 0 < c) (hβlam : β < lam) (hlampos : 0 < lam)
    (hclow : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z))
    (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β) :
    coreMeetPt Q c (diskPlane (linPlaneChart φ lam hlampos))
      = coreLoop Q '' {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
          (cappingSpaceHomeoProj (coreLoop Q t)).2 ∈ projLine (linSub φ)} := by
  have hψ0 : (fun t : ℝ => 1 - t) 0 = 1 := by norm_num
  have hψ1 : (fun t : ℝ => 1 - t) 1 = 0 := by norm_num
  have hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, (fun t : ℝ => 1 - t) t ∈ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hcont : ContinuousOn (fun t : ℝ => 1 - t) (Set.Icc (0 : ℝ) 1) :=
    (continuous_const.sub continuous_id).continuousOn
  exact clampedSweep_image_reference Q φ c hc (fun t : ℝ => 1 - t) hψ0 hψ1 hψ01 hcont
    hβlam hlampos hclow hβ
/-! ## 4. The parity count of a class function with opposite endpoint signs -/

/-- **The class of a non-zero vector lies in the plane `linSub φ` exactly when its functional
vanishes.**  (`Work.Drive.ker_linFun` is `(linFun φ).ker = linSub φ`.) -/
theorem mk_mem_projLine_iff (φ : Eucl 3 ≃L[ℝ] Eucl 3) {w : Eucl 3} (hw : w ≠ 0) :
    (Projectivization.mk ℝ w hw ∈ projLine (linSub φ)) ↔ linFun φ w = 0 := by
  constructor
  · rintro ⟨v, hv, hvU, hq⟩
    have hk : linFun φ v = 0 := by
      have : v ∈ (linFun φ).ker := by rw [ker_linFun]; exact hvU
      simpa using this
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℝ v w hv hw).mp hq.symm
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ha
      exact hv ha.symm
    have : linFun φ (a • w) = 0 := by rw [ha]; exact hk
    rw [map_smul] at this
    exact (mul_eq_zero.mp this).resolve_left ha0
  · intro hw0
    refine ⟨w, hw, ?_, rfl⟩
    have : w ∈ (linFun φ).ker := by simpa using hw0
    rwa [ker_linFun] at this

/-- **Parity of the number of zeros of a differentiable function with opposite endpoint signs.**
This is `Work.Drive.odd_ncard_zeros_of_neg_pos` with the weaker hypothesis that the two endpoint values
merely have opposite signs (that is the form in which the essentiality of the class loop enters). -/
theorem odd_ncard_zeros_of_opposite_endpoints {f : ℝ → ℝ}
    (hder : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (deriv f x) x)
    (h0 : f 0 ≠ 0) (hopp : f 0 * f 1 < 0)
    (hfin : ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ f t = 0}).Finite)
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t = 0 → deriv f t ≠ 0) :
    Odd ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ f t = 0}).ncard := by
  have hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) :=
    fun x hx => (hder x hx).continuousAt.continuousWithinAt
  have hsc : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t = 0 → SignChangeAt f t :=
    fun t ht hft => Work.Surf.signChangeAt_of_hasDerivAt (hder t ht) (hreg t ht hft) hft
  have h1 : f 1 ≠ 0 := fun h => by
    rw [h, mul_zero] at hopp
    exact absurd hopp (lt_irrefl 0)
  have hsign : (f 0 < 0 ∧ 0 < f 1) ∨ (f 1 < 0 ∧ 0 < f 0) := by
    rcases lt_or_gt_of_ne h0 with h | h
    · refine Or.inl ⟨h, ?_⟩
      exact lt_of_not_ge fun hle =>
        absurd (mul_nonneg_of_nonpos_of_nonpos (le_of_lt h) hle) (not_le.mpr hopp)
    · refine Or.inr ⟨?_, h⟩
      exact lt_of_not_ge fun hle =>
        absurd (mul_nonneg (le_of_lt h) hle) (not_le.mpr hopp)
  have hodd : Odd ({t ∈ Set.Icc (0 : ℝ) 1 | f t = 0} : Set ℝ).ncard :=
    odd_ncard_zeros_of_opposite_signs zero_le_one hcont hfin hsc h0 h1 hsign
  simpa only [Set.mem_ofPred_eq] using hodd

/-! ## 5. `(F1)`: the reference factor of `hn2` is the equator crossing count of the class loop -/

/-- **`(F1)`: the reference factor of `hn2` is odd.**

Let `Q` be a chart of the configuration plane lying in the level band `[c, β]` with `β < lam`, let
`φ` be the linear equivalence whose plane `projLine (linSub φ)` is the reference plane placed at the
level `lam`, and let `V : ℝ → Eucl 3` be a nonzero lift of the class loop of `Q` on `[0,1]`
(`[V t] = class (coreLoop Q t)`).  If

* the class loop is **essential**: `V 1 = κ • V 0` with `κ < 0` (this is
  `Work.Drive.exists_neg_parallelism_of_planeChart`, i.e. the nontriviality of the core of the
  configuration Möbius band, which is where the hypothesis `UmlaufProp` of the wall enters), and
* the class function `t ↦ linFun φ (V t)` is differentiable on `[0,1]` with finitely many zeros, all
  regular, and nonzero at `t = 0` (a genericity condition on the *free* reference plane `φ`), and
* the core loop is injective on the parameters at which its class meets the plane,

then the parameterisation-free pairing of the core loop with the clamped sweep of the reference plane is
**odd** — `Work.Drive.coreSideCountPt Q c (diskPlane (linPlaneChart φ lam hlampos))` is odd.

This is the mixed factor `ε(R; chart P_u) = 1` of `HN2_REFERENCE_STATUS.md` §2, hence (with
`Work.Drive.not_odd_coreSideCount_reference` for the reference's own block) the input of the
antisymmetry `hn2` that is not already supplied by the transport. -/
theorem odd_coreSideCountPt_reference (Q : ℂ → CappingSpace) (φ : Eucl 3 ≃L[ℝ] Eucl 3)
    {β c lam : ℝ} (hc : 0 < c) (hβlam : β < lam) (hlampos : 0 < lam)
    (hclow : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z))
    (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β)
    (V : ℝ → Eucl 3) (hVne : ∀ t : ℝ, V t ≠ 0)
    (hVcls : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Projectivization.mk ℝ (V t) (hVne t) = (cappingSpaceHomeoProj (coreLoop Q t)).2)
    {κ : ℝ} (hκ : κ < 0) (hesse : V 1 = κ • V 0)
    (hV0 : linFun φ (V 0) ≠ 0)
    (hder : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => linFun φ (V t))
      (deriv (fun t : ℝ => linFun φ (V t)) x) x)
    (hfin : ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ linFun φ (V t) = 0}).Finite)
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1, linFun φ (V t) = 0 →
      deriv (fun t : ℝ => linFun φ (V t)) t ≠ 0)
    (hinj : Set.InjOn (coreLoop Q) {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
      (cappingSpaceHomeoProj (coreLoop Q t)).2 ∈ projLine (linSub φ)}) :
    Odd (coreSideCountPt Q c (diskPlane (linPlaneChart φ lam hlampos))) := by
  have hmeet := coreMeetPt_reference_eq Q φ hc hβlam hlampos hclow hβ
  -- the meet parameters, in the two descriptions
  have hS : {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
      (cappingSpaceHomeoProj (coreLoop Q t)).2 ∈ projLine (linSub φ)}
      = {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ linFun φ (V t) = 0} := by
    ext t
    constructor
    · rintro ⟨ht, hmem⟩
      exact ⟨ht, (mk_mem_projLine_iff φ (hVne t)).mp (by rw [hVcls t ht]; exact hmem)⟩
    · rintro ⟨ht, hzero⟩
      exact ⟨ht, by rw [← hVcls t ht]; exact (mk_mem_projLine_iff φ (hVne t)).mpr hzero⟩
  have hfinS : ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
      (cappingSpaceHomeoProj (coreLoop Q t)).2 ∈ projLine (linSub φ)}).Finite := by
    rw [hS]; exact hfin
  have hcount : coreSideCountPt Q c (diskPlane (linPlaneChart φ lam hlampos))
      = ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
          (cappingSpaceHomeoProj (coreLoop Q t)).2 ∈ projLine (linSub φ)}).ncard := by
    rw [coreSideCountPt, hmeet]
    exact (Set.ncard_image_iff hfinS).mpr hinj
  -- the sign change at the endpoints
  have hf1 : linFun φ (V 1) = κ * linFun φ (V 0) := by
    rw [hesse, map_smul, smul_eq_mul]
  have hf1nz : linFun φ (V 1) ≠ 0 := by
    rw [hf1]
    exact mul_ne_zero (ne_of_lt hκ) hV0
  have hopp : linFun φ (V 0) * linFun φ (V 1) < 0 := by
    rw [hf1]
    have h2 : linFun φ (V 0) * (κ * linFun φ (V 0))
        = κ * (linFun φ (V 0) * linFun φ (V 0)) := by ring
    rw [h2]
    exact mul_neg_of_neg_of_pos hκ (mul_self_pos.mpr hV0)
  rw [hcount, hS]
  exact odd_ncard_zeros_of_opposite_endpoints hder hV0 hopp hfin hreg


/-- **Injectivity of the core loop on the parameters at which its class meets the plane**, from the
loop's injectivity up to its period and the base point's class being off the plane.

For a plane chart the core loop is closed (`coreLoop Q 1 = coreLoop Q 0`), so `1` is a meet parameter
exactly when `0` is; excluding `0` (the base point condition, which in the lift language is
`linFun φ (V 0) ≠ 0`) makes the meet-parameter set a subset of `[0,1)`, where the loop's injectivity is
the only thing left to check. -/
theorem injOn_classMeetParams_of_injOn_Ico {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) (φ : Eucl 3 ≃L[ℝ] Eucl 3)
    (hnot0 : (cappingSpaceHomeoProj (coreLoop Q 0)).2 ∉ projLine (linSub φ))
    (hinjloop : Set.InjOn (coreLoop Q) (Set.Ico (0 : ℝ) 1)) :
    Set.InjOn (coreLoop Q) {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
      (cappingSpaceHomeoProj (coreLoop Q t)).2 ∈ projLine (linSub φ)} := by
  have hseam : coreLoop Q 0 = coreLoop Q 1 := coreLoop_zero_eq_one_of_isPlaneChart hQ
  intro t ht t' ht' heq
  have h1not : (1 : ℝ) ∉ {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
      (cappingSpaceHomeoProj (coreLoop Q t)).2 ∈ projLine (linSub φ)} := by
    rintro ⟨-, hmem⟩
    rw [← hseam] at hmem
    exact hnot0 hmem
  have htne : t ≠ 1 := fun h => h1not (h ▸ ht)
  have ht'ne : t' ≠ 1 := fun h => h1not (h ▸ ht')
  exact hinjloop ⟨ht.1.1, lt_of_le_of_ne ht.1.2 htne⟩
    ⟨ht'.1.1, lt_of_le_of_ne ht'.1.2 ht'ne⟩ heq


/-! ## 6. Discharging the essentiality: `(F1)` from the plane chart alone -/

/-- The parameter of the core loop, as a point of the unit circle: `Work.Drive.coreLoop Q t =
Q (coreLoopArg t)`. -/
def coreLoopArg (t : ℝ) : ℂ := Complex.exp (↑Real.pi * (↑t : ℂ) * Complex.I)

@[simp] lemma coreLoopArg_norm (t : ℝ) : ‖coreLoopArg t‖ = 1 := by
  rw [coreLoopArg, show (↑Real.pi * (↑t : ℂ) * Complex.I)
      = ((Real.pi * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

@[simp] lemma coreLoop_eq (Q : ℂ → CappingSpace) (t : ℝ) : coreLoop Q t = Q (coreLoopArg t) := rfl

@[simp] lemma coreLoopArg_one : coreLoopArg 1 = -1 := by
  rw [coreLoopArg,
    show (↑Real.pi * (↑(1 : ℝ) : ℂ) * Complex.I) = (↑Real.pi : ℂ) * Complex.I by
      push_cast; ring]
  exact Complex.exp_pi_mul_I

@[simp] lemma coreLoopArg_zero : coreLoopArg 0 = 1 := by
  rw [coreLoopArg]
  simp

/-- **The essentiality of the core loop of a plane chart.**  The class loop of the chart is the seam
loop of the plane, so a continuous nonvanishing lift of it is negated along the loop:
`Vc (coreLoopArg 1) = κ • Vc (coreLoopArg 0)` with `κ < 0`.  This is
`Work.Drive.exists_neg_parallelism_of_planeChart` (`IsPlaneChart` alone supplies it), i.e. the
nontriviality of the core of the configuration Möbius band. -/
theorem exists_neg_parallelism_of_coreLoop {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0)
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (Vc : ℂ → Eucl 3) (hVcne : ∀ z : ℂ, ‖z‖ = 1 → Vc z ≠ 0)
    (hVccont : ContinuousOn Vc {z : ℂ | ‖z‖ = 1})
    (hVccls : ∀ z (hz : ‖z‖ = 1),
      Projectivization.mk ℝ (Vc z) (hVcne z hz) = (cappingSpaceHomeoProj (Q z)).2) :
    ∃ κ : ℝ, κ < 0 ∧ Vc (coreLoopArg 1) = κ • Vc (coreLoopArg 0) := by
  obtain ⟨-, c, hc, hcneg⟩ := exists_neg_parallelism_of_planeChart hγ hγne hQ Vc hVcne hVccont hVccls
  exact ⟨c, hcneg, by rw [coreLoopArg_one, coreLoopArg_zero]; exact hc⟩

/-- **`(F1)`, with the essentiality discharged.**  This is `Work.Drive.odd_coreSideCountPt_reference`
with the two topological hypotheses replaced by their source `IsPlaneChart` (through
`Work.Drive.exists_neg_parallelism_of_coreLoop`): what remains is the *regularity* of the class
function of the loop (a genericity condition on the free reference plane `φ`, its functional being
`linFun φ`) and the injectivity of the core loop on the parameters at which its class meets the plane.

So the mixed factor `ε(R; chart P_u) = 1` of `hn2` is a theorem modulo genericity alone: **no additional
topological input** is needed beyond the chart and the (proved) essentiality of the core loop. -/
theorem odd_coreSideCountPt_reference_of_isPlaneChart {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0)
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (φ : Eucl 3 ≃L[ℝ] Eucl 3) {β c lam : ℝ} (hc : 0 < c) (hβlam : β < lam) (hlampos : 0 < lam)
    (hclow : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z))
    (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β)
    (Vc : ℂ → Eucl 3) (hVcne : ∀ z : ℂ, ‖z‖ = 1 → Vc z ≠ 0)
    (hVccont : ContinuousOn Vc {z : ℂ | ‖z‖ = 1})
    (hVccls : ∀ z (hz : ‖z‖ = 1),
      Projectivization.mk ℝ (Vc z) (hVcne z hz) = (cappingSpaceHomeoProj (Q z)).2)
    (hVc0 : linFun φ (Vc 1) ≠ 0)
    (hder : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => linFun φ (Vc (coreLoopArg t)))
      (deriv (fun t : ℝ => linFun φ (Vc (coreLoopArg t))) x) x)
    (hfin : ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ linFun φ (Vc (coreLoopArg t)) = 0}).Finite)
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1, linFun φ (Vc (coreLoopArg t)) = 0 →
      deriv (fun t : ℝ => linFun φ (Vc (coreLoopArg t))) t ≠ 0)
    (hinjloop : Set.InjOn (coreLoop Q) (Set.Ico (0 : ℝ) 1)) :
    Odd (coreSideCountPt Q c (diskPlane (linPlaneChart φ lam hlampos))) := by
  obtain ⟨κ, hκ, hesse⟩ :=
    exists_neg_parallelism_of_coreLoop hγ hγne hQ Vc hVcne hVccont hVccls
  -- the base point's class is off the plane (the lift form `hVc0`), hence the meet parameters lie in
  -- `[0, 1)` and the loop's injectivity up to its period suffices
  have hnot0 : (cappingSpaceHomeoProj (coreLoop Q 0)).2 ∉ projLine (linSub φ) := by
    intro hmem
    have h0 : (cappingSpaceHomeoProj (coreLoop Q 0)).2
        = Projectivization.mk ℝ (Vc 1) (hVcne 1 (by norm_num)) := by
      rw [coreLoop_eq, coreLoopArg_zero]
      exact (hVccls 1 (by norm_num)).symm
    rw [h0] at hmem
    exact hVc0 ((mk_mem_projLine_iff φ (hVcne 1 (by norm_num))).mp hmem)
  have hinj := injOn_classMeetParams_of_injOn_Ico hQ φ hnot0 hinjloop
  refine odd_coreSideCountPt_reference Q φ hc hβlam hlampos hclow hβ
    (fun t => Vc (coreLoopArg t)) (fun t => hVcne _ (coreLoopArg_norm t)) ?_ hκ hesse ?_ hder hfin hreg hinj
  · intro t ht
    rw [coreLoop_eq]
    exact hVccls _ (coreLoopArg_norm t)
  · rw [coreLoopArg_zero]
    exact hVc0


/-! ## 7. Transfer to the box count -/

/-- **The oddness transfers from the pairing count to the box count** at a configuration with
finitely many parameter meets and no seam meets (`Work.Drive.coreMeetPt_ncard_eq_iff`).  This is the
form in which the transport's multiplicativity `Work.Drive.odd_coreSideCount_mul_of_block` (which is
stated for the *box* counts `Work.Drive.coreSideCount`) consumes the reference factor `(F1)`. -/
theorem odd_coreSideCount_of_meetPt_ncard_eq (Q : ℂ → CappingSpace) (c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (hfin : (coreMeet Q c P).Finite)
    (hinj : Set.InjOn (fun p : ℝ × Work.Drive.Amb 2 => coreLoop Q p.1) (coreMeet Q c P))
    (h : Odd (coreSideCountPt Q c P)) : Odd (coreSideCount Q c P) :=
  ((coreMeetPt_ncard_eq_iff Q c P hfin).mpr hinj) ▸ h


/-- **`(F1)` with the loop's injectivity discharged.**  This is
`Work.Drive.odd_coreSideCountPt_reference_of_isPlaneChart` with the hypothesis
`Set.InjOn (coreLoop Q) (Set.Ico 0 1)` supplied by the proved
`Work.Drive.injOn_coreLoop_Ico_of_isPlaneChart` (the core loop of a plane chart is a simple closed
curve).

So the mixed factor `ε(R; chart P_u) = 1` of `hn2` holds **for every linear plane `φ` in general
position**: the only hypotheses left are the chart's level band, a continuous nonvanishing circle lift
of the chart's class map (with its base point off the plane) and the *regularity* of the class function
`t ↦ linFun φ (Vc (coreLoopArg t))` — a genericity condition on the free reference plane. -/
theorem odd_coreSideCountPt_reference_of_isPlaneChart' {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0)
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (φ : Eucl 3 ≃L[ℝ] Eucl 3) {β c lam : ℝ} (hc : 0 < c) (hβlam : β < lam) (hlampos : 0 < lam)
    (hclow : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z))
    (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β)
    (Vc : ℂ → Eucl 3) (hVcne : ∀ z : ℂ, ‖z‖ = 1 → Vc z ≠ 0)
    (hVccont : ContinuousOn Vc {z : ℂ | ‖z‖ = 1})
    (hVccls : ∀ z (hz : ‖z‖ = 1),
      Projectivization.mk ℝ (Vc z) (hVcne z hz) = (cappingSpaceHomeoProj (Q z)).2)
    (hVc0 : linFun φ (Vc 1) ≠ 0)
    (hder : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => linFun φ (Vc (coreLoopArg t)))
      (deriv (fun t : ℝ => linFun φ (Vc (coreLoopArg t))) x) x)
    (hfin : ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ linFun φ (Vc (coreLoopArg t)) = 0}).Finite)
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1, linFun φ (Vc (coreLoopArg t)) = 0 →
      deriv (fun t : ℝ => linFun φ (Vc (coreLoopArg t))) t ≠ 0) :
    Odd (coreSideCountPt Q c (diskPlane (linPlaneChart φ lam hlampos))) :=
  odd_coreSideCountPt_reference_of_isPlaneChart hγ hγne hQ φ hc hβlam hlampos hclow hβ Vc hVcne
    hVccont hVccls hVc0 hder hfin hreg (injOn_coreLoop_Ico_of_isPlaneChart hγ hγne hQ)


end

end Work.Drive
