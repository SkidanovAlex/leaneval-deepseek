import Mathlib
import Submission.Work.Drive.geometricLocality
import Submission.Work.Drive.coreLoopClosed
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.planeChain
import Submission.Work.Drive.coreLoop_injective_mod_one

/-!
# The three geometric side conditions of the locality engine `hn4`, for the design's loop and chain

`Work.Drive.meetPt_ncard_eq_of_regular_manifold` (`geometricLocality.lean`) needs, besides finiteness
and transversality of the base meets, three geometric facts about the design's (loop, chain) pair:

* **`hper`**, the loop is `1`-periodic: for the core loop `t ↦ Q (exp (iπt))` of a chart this is exactly
  the chart's seam clause (`Work.Drive.coreLoop_periodic`, from `exp (i(π(t+1))) = -exp (iπt)`);
* **`hbox`**, the parameter box of the chain covers the chain's image:
  `Work.Drive.clampedSweep_boxCover` reduces it to the two conditions
  `P '' unitBox 1 = range P` (for the plane presentation, proved for a disk presentation as
  `Work.Drive.diskPlane_boxCover`) and `ψ '' Icc 0 1 = range ψ` (for the radial cutoff);
* **`hinj`**, the loop is injective modulo its period (the one genuine new obligation: the chart's
  injectivity on the boundary circle modulo the antipodal identification).

## A design warning, recorded here because it is invisible in the statement of `hbox`

The design's `coreMeet` uses the cutoff `ψ = fun t => 1 - t`, whose range is all of `ℝ`.  With it
`hbox` is **false** (`x 2 = -5` gives a scale outside `ψ '' [0,1]`), so the *corrected* count
(`coreSideCountPt`) must be formed with a cutoff whose range lies in `[0,1]` and which is still
surjective on `[0,1]` — `Work.Drive.cosCut t = (1 + cos (πt))/2` below is such a cutoff: it is smooth,
it has `cosCut 0 = 1`, `cosCut 1 = 0` (the two face conditions of the radial sweep,
`clampedSweep_face_one`/`clampedSweep_face_zero`) and `cosCut '' ℝ = cosCut '' ([0,1])`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-! ## 1. The loop is periodic: `hper` -/

/-- **The core loop is `1`-periodic**, from the chart's seam clause. -/
theorem coreLoop_periodic {Q : ℂ → CappingSpace} (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (s : ℝ) : coreLoop Q (s + 1) = coreLoop Q s := by
  rw [coreLoop, coreLoop,
    show Real.pi * ((s + 1 : ℝ) : ℂ) * Complex.I
        = Real.pi * (s : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]
  exact hQseam _ (by rw [Complex.norm_exp]; simp)

/-- The core loop of a plane chart is `1`-periodic. -/
theorem coreLoop_periodic_of_isPlaneChart {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) (s : ℝ) :
    coreLoop Q (s + 1) = coreLoop Q s :=
  coreLoop_periodic hQ.2.2.1 s

/-- The core loop of the *perturbed* chart of the design: `linCapping A` commutes with the loop. -/
theorem coreLoop_linCapping {Q : ℂ → CappingSpace} (A : Eucl 3 ≃L[ℝ] Eucl 3) (s : ℝ) :
    coreLoop (fun z => linCapping A (Q z)) s = linCapping A (coreLoop Q s) := rfl

/-- Hence the perturbed loop is periodic too. -/
theorem coreLoop_periodic_linCapping {Q : ℂ → CappingSpace}
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z) (A : Eucl 3 ≃L[ℝ] Eucl 3) (s : ℝ) :
    coreLoop (fun z => linCapping A (Q z)) (s + 1) = coreLoop (fun z => linCapping A (Q z)) s := by
  rw [coreLoop_linCapping, coreLoop_linCapping, coreLoop_periodic hQseam s]

/-- **The loop half of the locality engine's `hinj`**: the core loop of a plane chart is injective
modulo its period (the proved `Work.Drive.coreLoop_injective_mod_one`, stated in the shape in which
`Work.Drive.meetPt_ncard_eq_of_regular_manifold` consumes it).  The other half of `hinj` — the
faithfulness of the *chain* parameterisation — is the injectivity of the sweep, which is a property of
the honest chart that the three clauses of `IsPlaneChart` do not imply (see
`GEOMETRIC_LOCALITY_STATUS.md` §2(ii)). -/
theorem coreLoop_hinj {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) (hγne : ∀ x : Circle, γ x ≠ 0)
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) :
    ∀ t t' : ℝ, coreLoop Q t = coreLoop Q t' → ∃ k : ℤ, t' = t + k :=
  fun _ _ h => coreLoop_injective_mod_one hγ hγne hQ h

/-! ## 2. The parameter box of the radial sweep covers its image: `hbox` -/

/-- The point `(y 0, y 1, t)` of `ℝ³`. -/
def mk3v (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![y 0, y 1, t]

@[simp] lemma mk3v_apply_zero (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : mk3v y t 0 = y 0 := rfl
@[simp] lemma mk3v_apply_one (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : mk3v y t 1 = y 1 := rfl
@[simp] lemma mk3v_apply_two (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : mk3v y t 2 = t := rfl

/-- The first two coordinates of `mk3v y t` are `y`. -/
lemma mk3v_proj (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    mk2 ((mk3v y t) 0) ((mk3v y t) 1) = y := by
  rw [mk3v_apply_zero, mk3v_apply_one, mk2_eta]

/-- **The radial sweep's box covers its image**, from the two cover conditions on the plane
presentation (`P '' unitBox 1 = range P`) and on the radial cutoff (`ψ '' Icc 0 1 = range ψ`). -/
theorem clampedSweep_boxCover {P : EuclideanSpace ℝ (Fin 2) → CappingSpace} (c : ℝ) (ψ : ℝ → ℝ)
    (hP : ∀ y : EuclideanSpace ℝ (Fin 2),
      ∃ y' ∈ Submission.Drive.unitBox 1, P y' = P y)
    (hψ : ∀ t : ℝ, ∃ t' ∈ Set.Icc (0 : ℝ) 1, ψ t' = ψ t)
    (x : EuclideanSpace ℝ (Fin 3)) :
    ∃ x' ∈ Submission.Drive.unitBox 2, clampedSweep c ψ P x' = clampedSweep c ψ P x := by
  obtain ⟨y', hy'mem, hy'⟩ := hP (mk2 (x 0) (x 1))
  obtain ⟨t', ht'mem, ht'⟩ := hψ (x 2)
  refine ⟨mk3v y' t', ?_, ?_⟩
  · rw [Submission.Drive.unitBox, Set.mem_ofPred_eq]
    intro i
    fin_cases i
    · simpa using hy'mem 0
    · simpa using hy'mem 1
    · simpa using ht'mem
  · have hsc : clampScale c ψ P (mk3v y' t') = clampScale c ψ P x := by
      rw [clampScale, clampScale, mk3v_apply_two, mk3v_proj, hy', ht']
    rw [clampedSweep_apply, clampedSweep_apply, mk3v_proj, hy',
      show pos (clampScale c ψ P (mk3v y' t')) (clampScale_pos c ψ P (mk3v y' t'))
        = pos (clampScale c ψ P x) (clampScale_pos c ψ P x) from Subtype.ext hsc]

/-- **A disk-presented plane covers its box**: `diskPlane Q '' unitBox 1 = range (diskPlane Q)`. -/
theorem diskPlane_boxCover {Q : ℂ → CappingSpace} (y : EuclideanSpace ℝ (Fin 2)) :
    ∃ y' ∈ Submission.Drive.unitBox 1, diskPlane Q y' = diskPlane Q y := by
  obtain ⟨w, hw, hwz⟩ := sqDisk_surjective (sqDisk (foldBox y))
    (norm_sqDisk_le_one _ (foldBox_mem_unitBox y))
  obtain ⟨a, ha, ha'⟩ := foldFun_surjOn_Icc (w 0) (hw 0)
  obtain ⟨b, hb, hb'⟩ := foldFun_surjOn_Icc (w 1) (hw 1)
  refine ⟨mk2 a b, ?_, ?_⟩
  · rw [Submission.Drive.unitBox, Set.mem_ofPred_eq]
    intro i
    fin_cases i
    · simpa using ha
    · simpa using hb
  · have hfold : foldBox (mk2 a b) = w := by
      rw [foldBox, mk2_apply_zero, mk2_apply_one, ha', hb', mk2_eta]
    rw [diskPlane_apply, diskPlane_apply, hfold, hwz]

/-! ## 3. A cutoff with `range ⊆ [0,1]` satisfying the two face conditions -/

/-- **A bounded cutoff for the radial sweep**: `cosCut t = (1 + cos (πt))/2`, so that
`cosCut 0 = 1` (the plane face) and `cosCut 1 = 0` (the level face), while its range is `[0,1]` and
its restriction to `[0,1]` is onto.  (The design's `ψ = 1 - ·` has full range and therefore fails the
cover condition `hbox` of the locality engine.) -/
def cosCut (t : ℝ) : ℝ := (1 + Real.cos (Real.pi * t)) / 2

@[simp] lemma cosCut_zero : cosCut 0 = 1 := by simp [cosCut]
@[simp] lemma cosCut_one : cosCut 1 = 0 := by simp [cosCut, Real.cos_pi]

lemma cosCut_mem_Icc (t : ℝ) : cosCut t ∈ Set.Icc (0 : ℝ) 1 := by
  have h := Real.neg_one_le_cos (Real.pi * t)
  have h2 := Real.cos_le_one (Real.pi * t)
  constructor <;> simp only [cosCut] <;> linarith

lemma cosCut_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cosCut := by
  unfold cosCut
  fun_prop

/-- **The restriction of `cosCut` to `[0,1]` is onto its range.** -/
lemma cosCut_surjOn (t : ℝ) : ∃ t' ∈ Set.Icc (0 : ℝ) 1, cosCut t' = cosCut t := by
  have ht : cosCut t ∈ Set.Icc (cosCut 1) (cosCut 0) := by
    rw [cosCut_one, cosCut_zero]
    exact cosCut_mem_Icc t
  obtain ⟨t', ht', ht''⟩ :=
    intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) cosCut_contDiff.continuous.continuousOn ht
  exact ⟨t', ht', ht''⟩


/-! ## 4. The engine's count *is* the design's count

`Work.Drive.coreSideCountPt Q c P` is defined as the cardinality of the *intersection of the images* of
the core loop and of the clamped sweep; the locality engine
`Work.Drive.meetPt_ncard_eq_of_regular_manifold` controls the number of distinct loop values on the
*parameter* meet set `Work.Drive.meetBox (coreLoop Q) (clampedSweep …)`.  The two agree by definition:
the loop's parameter domain `[0,1]` and the chain's box `unitBox 2` are the same two domains, so the
image of the parameter meet set under the loop is exactly the intersection of the two images.

Because the covering condition (`hbox`) of the engine fails for the design's cutoff `1 - ·` (§3 of
`GEOMETRIC_LOCALITY_STATUS.md`), the count is stated here with a *variable* cutoff, so that the cutoff
`cosCut` (or any bounded one) may be used. -/

/-- The geometric meet set with a *variable* cutoff. -/
def coreMeetPtCut (Q : ℂ → CappingSpace) (c : ℝ) (ψ : ℝ → ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) : Set CappingSpace :=
  coreLoop Q '' Set.Icc (0 : ℝ) 1 ∩ clampedSweep c ψ P '' Submission.Drive.unitBox 2

/-- The geometric count with a variable cutoff. -/
def coreSideCountPtCut (Q : ℂ → CappingSpace) (c : ℝ) (ψ : ℝ → ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) : ℕ :=
  (coreMeetPtCut Q c ψ P).ncard

/-- The design's `coreSideCountPt` is the case `ψ = 1 - ·` of the variable-cutoff count. -/
theorem coreSideCountPt_eq_cut (Q : ℂ → CappingSpace) (c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    coreSideCountPt Q c P = coreSideCountPtCut Q c (fun t => 1 - t) P := rfl

/-- **The engine's count is the design's count**: the image of `meetBox` under the loop is the
intersection of the loop's image with the chain's image. -/
theorem coreSideCountPtCut_eq_range_ncard (Q : ℂ → CappingSpace) (c : ℝ) (ψ : ℝ → ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    coreSideCountPtCut Q c ψ P =
      (Set.range (fun p : meetBox (coreLoop Q) (clampedSweep c ψ P) =>
        coreLoop Q p.1.1)).ncard := by
  have hset : coreMeetPtCut Q c ψ P =
      Set.range (fun p : meetBox (coreLoop Q) (clampedSweep c ψ P) => coreLoop Q p.1.1) := by
    ext y
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, ⟨x, hx, hxy⟩⟩
      exact ⟨⟨(t, x), ⟨ht, hx, hxy.symm⟩⟩, rfl⟩
    · rintro ⟨p, rfl⟩
      obtain ⟨ht, hx, he⟩ := mem_meetBox.mp p.2
      exact ⟨⟨p.1.1, ht, rfl⟩, ⟨p.1.2, hx, he.symm⟩⟩
  rw [coreSideCountPtCut, hset]

/-! ## 5. Smoothness of the loop as a manifold map -/

section DesignSmooth

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.halfLineProjectiveCharted Work.Drive.isManifold_halfLineProjectiveCharted
  Work.Drive.t2Space_cappingSpace

/-- **The core loop is smooth** when the chart is. -/
theorem contMDiff_coreLoop {Q : ℂ → CappingSpace}
    (hQ : ContMDiff (𝓘(ℝ,ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q) :
    ContMDiff (𝓘(ℝ,ℝ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (coreLoop Q) := by
  have hlin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => Complex.exp ((Real.pi : ℂ) * (t : ℂ) * Complex.I)) :=
    Complex.contDiff_exp.comp (ContDiff.mul
      (contDiff_const.mul Complex.ofRealCLM.contDiff) contDiff_const)
  have h1' : ContMDiff (𝓘(ℝ,ℝ)) (𝓘(ℝ,ℂ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => Complex.exp ((Real.pi : ℂ) * (t : ℂ) * Complex.I)) :=
    contMDiff_iff_contDiff.mpr hlin
  have h := hQ.comp h1'
  have hfun : (Q ∘ fun t : ℝ => Complex.exp ((Real.pi : ℂ) * (t : ℂ) * Complex.I)) =
      coreLoop Q := rfl
  rwa [hfun] at h

end DesignSmooth


/-! ## 6. The count does not depend on the cutoff: the bounded cutoff `cosCut` is admissible

The locality engine's cover condition `hbox` needs a *bounded* cutoff (see
`GEOMETRIC_LOCALITY_STATUS.md`), while the design's `coreMeet` uses `ψ = 1 - ·`.  The two give the same
count: the image of the clamped sweep depends only on the *range* of `ψ` on the parameter box, because
the radial coordinate enters only through `exp (ψ (x 2) · (log c − log (levelOf (P y))))`.  So the
design may keep `1 - ·` in the definition of its side value and use `cosCut` in the *locality* argument. -/

/-- The radial scale of the sweep at `mk3v y t`. -/
lemma clampScale_mk3v (c : ℝ) (ψ : ℝ → ℝ) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    clampScale c ψ P (mk3v y t)
      = Real.exp (ψ t * (Real.log c - Real.log (levelOf (P y)))) := by
  rw [clampScale, mk3v_apply_two, mk3v_proj]

/-- The sweep at `mk3v y t`. -/
lemma clampedSweep_mk3v (c : ℝ) (ψ : ℝ → ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    clampedSweep c ψ P (mk3v y t)
      = scaleCapping (pos (clampScale c ψ P (mk3v y t))
          (clampScale_pos c ψ P (mk3v y t))) (P y) := by
  rw [clampedSweep_apply, mk3v_proj]

/-- The box membership of `mk3v y t`. -/
lemma mk3v_mem_unitBox {y : EuclideanSpace ℝ (Fin 2)} {t : ℝ}
    (hy : y ∈ Submission.Drive.unitBox 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    mk3v y t ∈ Submission.Drive.unitBox 2 := by
  rw [Submission.Drive.unitBox, Set.mem_ofPred_eq]
  intro i
  fin_cases i
  · simpa using hy 0
  · simpa using hy 1
  · simpa using ht

/-- **One inclusion of the cutoff-independence**: if every value of `ψ` on the box is a value of `ψ'`
on the box, then the sweep's image for `ψ` is contained in the sweep's image for `ψ'`. -/
theorem clampedSweep_image_subset_of_cutoff {c : ℝ} {ψ ψ' : ℝ → ℝ}
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (h : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∃ s' ∈ Set.Icc (0 : ℝ) 1, ψ' s' = ψ s) :
    clampedSweep c ψ P '' Submission.Drive.unitBox 2 ⊆
      clampedSweep c ψ' P '' Submission.Drive.unitBox 2 := by
  rintro u ⟨x, hx, rfl⟩
  have hx' : ∀ i : Fin 3, x i ∈ Set.Icc (0 : ℝ) 1 := by
    rw [Submission.Drive.unitBox, Set.mem_ofPred_eq] at hx
    exact hx
  obtain ⟨s', hs'⟩ := h (x 2) (hx' 2)
  have hy : mk2 (x 0) (x 1) ∈ Submission.Drive.unitBox 1 := by
    rw [Submission.Drive.unitBox, Set.mem_ofPred_eq]
    intro i
    fin_cases i
    · simpa using hx' 0
    · simpa using hx' 1
  refine ⟨mk3v (mk2 (x 0) (x 1)) s', mk3v_mem_unitBox hy hs'.1, ?_⟩
  have hsc : clampScale c ψ' P (mk3v (mk2 (x 0) (x 1)) s') = clampScale c ψ P x := by
    rw [clampScale_mk3v, clampScale, hs'.2]
  rw [clampedSweep_apply, clampedSweep_apply, mk3v_proj,
    show pos (clampScale c ψ' P (mk3v (mk2 (x 0) (x 1)) s'))
        (clampScale_pos c ψ' P (mk3v (mk2 (x 0) (x 1)) s'))
      = pos (clampScale c ψ P x) (clampScale_pos c ψ P x) from Subtype.ext hsc]

/-- **The image of the clamped sweep depends only on the range of the cutoff on the box.** -/
theorem clampedSweep_image_eq_of_cutoff {c : ℝ} {ψ ψ' : ℝ → ℝ}
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (h : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∃ s' ∈ Set.Icc (0 : ℝ) 1, ψ' s' = ψ s)
    (h' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∃ s' ∈ Set.Icc (0 : ℝ) 1, ψ s' = ψ' s) :
    clampedSweep c ψ P '' Submission.Drive.unitBox 2
      = clampedSweep c ψ' P '' Submission.Drive.unitBox 2 :=
  Set.Subset.antisymm (clampedSweep_image_subset_of_cutoff P h)
    (clampedSweep_image_subset_of_cutoff P h')

/-- **The geometric count does not depend on the cutoff.** -/
theorem coreSideCountPtCut_eq_of_cutoff (Q : ℂ → CappingSpace) (c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) {ψ ψ' : ℝ → ℝ}
    (h : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∃ s' ∈ Set.Icc (0 : ℝ) 1, ψ' s' = ψ s)
    (h' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∃ s' ∈ Set.Icc (0 : ℝ) 1, ψ s' = ψ' s) :
    coreSideCountPtCut Q c ψ P = coreSideCountPtCut Q c ψ' P := by
  rw [coreSideCountPtCut, coreSideCountPtCut, coreMeetPtCut, coreMeetPtCut,
    clampedSweep_image_eq_of_cutoff P h h']

/-- **`cosCut` is onto `[0,1]` from `[0,1]`.** -/
lemma cosCut_surjOn_Icc :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ s ∈ Set.Icc (0 : ℝ) 1, cosCut s = t := by
  intro t ht
  have hcont : ContinuousOn cosCut (Set.Icc (0 : ℝ) 1) :=
    cosCut_contDiff.continuous.continuousOn
  have ht' : t ∈ Set.Icc (cosCut 1) (cosCut 0) := by
    rw [cosCut_one, cosCut_zero]; exact ht
  obtain ⟨s, hs, hst⟩ :=
    intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcont ht'
  exact ⟨s, hs, hst⟩

/-- **The bounded cutoff `cosCut` gives the design's count**: it has the same range as `1 - ·` on the
box, so the cover condition `hbox` of the locality engine may be discharged with `cosCut` without
changing the value of the side function. -/
theorem coreSideCountPtCut_eq_cosCut (Q : ℂ → CappingSpace) (c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    coreSideCountPtCut Q c cosCut P = coreSideCountPtCut Q c (fun t => 1 - t) P := by
  refine coreSideCountPtCut_eq_of_cutoff Q c P (fun s hs => ?_) (fun s hs => ?_)
  · refine ⟨1 - cosCut s, ⟨?_, ?_⟩, by ring⟩
    · have := cosCut_mem_Icc s; linarith [this.2]
    · have := cosCut_mem_Icc s; linarith [this.1]
  · obtain ⟨s', hs', hEq⟩ := cosCut_surjOn_Icc (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    exact ⟨s', hs', hEq⟩

end

end Work.Drive
