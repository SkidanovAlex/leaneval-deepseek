import Mathlib
import Submission.Work.Drive.planeChain
import Submission.Work.Drive.exists_perturbation_all_ne_zero
import Submission.Work.Drive.sqDisk_surjective
import Submission.Work.Drive.contMDiffAt_cappingVecPoint_general
import Submission.Work.Drive.contMDiff_interpSweep
import Submission.Work.Drive.classTripleRegular

/-!
# The homotopy half of the ends clause, in *disk* coordinates

`Work.Drive.HasClassLinearization` (`Submission/Work/Drive/classTripleOdd.lean`) bundles, for each of the
three planes of the design, a homotopy from the class map of the plane to the disk model of a *linear*
plane, together with the transversality data of the encoded chains.  The *homotopy* half is supplied by
`Work.Drive.exists_classMap_homotopy` (`Submission/Work/Drive/exists_classMap_homotopy.lean`) from

* two nonvanishing `C^∞` lifts `V`, `W` of the two *end* class maps, **anti-equivariant on the seam**
  (`V (seamInv2 y) = - V y`), and a weight `χ` with the same property;
* one perturbation vector `p` making the three families
  `(1-s) • V + s • W + χ • p`, `V + t • χ • p`, `W + t • χ • p` nonvanishing.

The producer of such a `p` (`Work.Drive.exists_perturbation_all_ne_zero`) is **box-local**: its
nonvanishing conclusion holds on `Submission.Drive.unitBox 1`, whereas the *chain* built from the
homotopy is a map of all of `ℝ³` (the seam invariance required by `Work.Drive.Meet3Hyp` is imposed on the
four whole *lines* `y 0 ∈ {0,1}`, `y 1 ∈ {0,1}`), so the naive assembly needs the nonvanishing on all of
`ℝ²`.

This file removes that mismatch by working in the **disk coordinates of the plane**, which is the form in
which the design's planes are presented anyway (`P k = rotPresentation Q (u k) = diskPlane D k` and
`planeClassMap (diskPlane (linPlaneChart φ c hc))`).  The point is that

> `diskPlane Q y = Q (sqDisk (foldBox y))`  and  `‖sqDisk (foldBox y)‖ ≤ 1` for **every** `y`,

so the folded square presentation never leaves the **compact** closed disk: the box-local nonvanishing of
the perturbation lemma (transported along the surjection `sqDisk : □ → D̄`,
`Work.Drive.sqDisk_surjective`) is all that is needed, and the homotopy

`H (t, y) := [ (1 - σ t) • V (θ y) + σ t • W (θ y) + (φ t · χ (θ y)) • p ]`,   `θ y = sqDisk (foldBox y)`,

is defined, continuous (indeed `C^∞` — the cutoffs `σ`, `φ` of this file are *smooth*, unlike the
`min`/`clamp` cutoffs of `exists_classMap_homotopy.lean`) and seam-invariant on all of `ℝ²`, with both
endpoint equalities holding as *function* equalities on all of `ℝ²` — which is exactly the shape of the
`HasClassLinearization` clauses.

The two remaining inputs are the design's: the **oddness** `V (-z) = - V z` of the two lifts on the
boundary circle (which is the essentiality of the two end class maps, see
`Submission/Work/Drive/ENDS_HOMOTOPY_NOTES.md` §2; for the linear end it is the proved
`Work.Drive.linVecC_neg`), and the `hgood` hypothesis of the perturbation lemma at the zeros of `χ`.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

/-! ## 1. Lifts of the class map of a disk chart -/

/-- **A vector lift of the class map of a disk chart.**  `V` is a nonvanishing vector field on the disk
whose projective class is the class of the capping point `D z` — the vector form of the chart's
presentation, in which the oddness on the boundary circle (i.e. the essentiality of the class map) can be
stated. -/
def IsClassLift (D : ℂ → CappingSpace) (V : ℂ → Eucl 3) (hV : ∀ z, V z ≠ 0) : Prop :=
  ∀ z, (cappingSpaceHomeoProj (D z)).2 = Projectivization.mk ℝ (V z) (hV z)

/-- **The class map of a folded disk presentation in terms of a lift**: the `y`-parameter is folded into
the square and then sent to the disk, so the class is that of the lift at `sqDisk (foldBox y)`. -/
theorem planeClassMap_diskPlane_of_lift {D : ℂ → CappingSpace} {V : ℂ → Eucl 3}
    {hV : ∀ z, V z ≠ 0} (h : IsClassLift D V hV) (y : EuclideanSpace ℝ (Fin 2)) :
    planeClassMap (diskPlane D) y
      = Projectivization.mk ℝ (V (sqDisk (foldBox y))) (hV _) := by
  have h1 : planeClassMap (diskPlane D) y
      = (cappingSpaceHomeoProj (D (sqDisk (foldBox y)))).2 := by
    simp only [planeClassMap, diskPlane_apply]
  rw [h1]
  exact h _

/-! ## 2. The perturbation data on the closed disk -/

/-- **The perturbation data on the closed disk.**  The three families of the homotopy are nonvanishing
at the perturbation vector `p`, on the whole closed disk (which is where the folded presentations take
their values). -/
def DiskGood (V W : ℂ → Eucl 3) (χ : ℂ → ℝ) (p : Eucl 3) : Prop :=
  (∀ z : ℂ, ‖z‖ ≤ 1 → ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      (1 - s) • V z + s • W z + (χ z) • p ≠ 0) ∧
  (∀ z : ℂ, ‖z‖ ≤ 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → V z + (t * χ z) • p ≠ 0) ∧
  (∀ z : ℂ, ‖z‖ ≤ 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → W z + (t * χ z) • p ≠ 0)

/-- **The perturbation lemma on the closed disk**: the box-local producer
`Work.Drive.exists_perturbation_all_ne_zero`, transported along the surjection
`Work.Drive.sqDisk_surjective : □ → D̄`. -/
theorem exists_perturbation_disk (V W : ℂ → Eucl 3) (χ : ℂ → ℝ)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hVne : ∀ z, V z ≠ 0) (hWne : ∀ z, W z ≠ 0)
    (hgood : ∀ z : ℂ, ‖z‖ ≤ 1 → χ z = 0 →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (1 - s) • V z + s • W z ≠ 0) :
    ∃ p : Eucl 3, DiskGood V W χ p := by
  have hV' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 2) => V (sqDisk y)) := hV.comp sqDisk_contDiff
  have hW' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 2) => W (sqDisk y)) := hW.comp sqDisk_contDiff
  have hχ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 2) => χ (sqDisk y)) := hχ.comp sqDisk_contDiff
  have hgood' : ∀ y ∈ Submission.Drive.unitBox 1, χ (sqDisk y) = 0 →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        (1 - s) • (V (sqDisk y)) + s • (W (sqDisk y)) ≠ 0 :=
    fun y hy h0 s hs => hgood (sqDisk y) (norm_sqDisk_le_one y hy) h0 s hs
  obtain ⟨p, h1, h2, h3⟩ := exists_perturbation_all_ne_zero
    (fun y : EuclideanSpace ℝ (Fin 2) => V (sqDisk y))
    (fun y : EuclideanSpace ℝ (Fin 2) => W (sqDisk y))
    (fun y : EuclideanSpace ℝ (Fin 2) => χ (sqDisk y)) hV' hW' hχ'
    (fun y => hVne _) (fun y => hWne _) hgood'
  refine ⟨p, ?_, ?_, ?_⟩
  · intro z hz s hs
    obtain ⟨y, hy, hzy⟩ := sqDisk_surjective z hz
    rw [← hzy]
    exact h1 s hs y hy
  · intro z hz t ht
    obtain ⟨y, hy, hzy⟩ := sqDisk_surjective z hz
    rw [← hzy]
    exact h2 t ht y hy
  · intro z hz t ht
    obtain ⟨y, hy, hzy⟩ := sqDisk_surjective z hz
    rw [← hzy]
    exact h3 t ht y hy

/-! ## 3. The smooth cutoffs

The two cutoffs of the concatenation are *smooth* (unlike the `min`/`clamp01` cutoffs of
`exists_classMap_homotopy.lean`), so that the assembled homotopy is `C^∞` and can be fed to the
`Meet3Hyp`-smoothness of the chain.

`σ t = smoothTransition (3t - 1)`: `0` for `t ≤ 1/3`, `1` for `t ≥ 2/3`;
`φ t = smoothTransition (12t - 3) · smoothTransition (9 - 12t)`: `1` on `[1/3, 2/3]`, `0` outside
`[1/4, 3/4]`. -/

/-- The interpolation parameter of the concatenation. -/
def smoothSigma (t : ℝ) : ℝ := Real.smoothTransition (3 * t - 1)

/-- The perturbation-dial of the concatenation. -/
def smoothPhi (t : ℝ) : ℝ :=
  Real.smoothTransition (12 * t - 3) * Real.smoothTransition (9 - 12 * t)

lemma contDiff_smoothSigma : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) smoothSigma :=
  Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)

lemma contDiff_smoothPhi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) smoothPhi :=
  (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp
      (contDiff_const.sub (contDiff_const.mul contDiff_id)))

lemma smoothSigma_mem (t : ℝ) : smoothSigma t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma smoothPhi_mem (t : ℝ) : smoothPhi t ∈ Set.Icc (0 : ℝ) 1 := by
  have hb : (0 : ℝ) ≤ Real.smoothTransition (9 - 12 * t) := Real.smoothTransition.nonneg _
  refine ⟨mul_nonneg (Real.smoothTransition.nonneg _) hb, ?_⟩
  calc Real.smoothTransition (12 * t - 3) * Real.smoothTransition (9 - 12 * t)
      ≤ 1 * Real.smoothTransition (9 - 12 * t) :=
        mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _) hb
    _ ≤ 1 := by rw [one_mul]; exact Real.smoothTransition.le_one _

lemma smoothSigma_eq_zero_of_le {t : ℝ} (h : t ≤ 1 / 3) : smoothSigma t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma smoothSigma_eq_one_of_le {t : ℝ} (h : 2 / 3 ≤ t) : smoothSigma t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma smoothPhi_eq_one_of_mem {t : ℝ} (h : t ∈ Set.Icc (1 / 3 : ℝ) (2 / 3)) : smoothPhi t = 1 := by
  have h1 : (1 : ℝ) ≤ 12 * t - 3 := by linarith [h.1]
  have h2 : (1 : ℝ) ≤ 9 - 12 * t := by linarith [h.2]
  rw [smoothPhi, Real.smoothTransition.one_of_one_le h1,
    Real.smoothTransition.one_of_one_le h2, mul_one]

lemma smoothPhi_eq_zero_of_lt {t : ℝ} (h : t < 1 / 4) : smoothPhi t = 0 := by
  have h1 : 12 * t - 3 ≤ 0 := by linarith
  rw [smoothPhi, Real.smoothTransition.zero_of_nonpos h1, zero_mul]

lemma smoothPhi_eq_zero_of_gt {t : ℝ} (h : 3 / 4 < t) : smoothPhi t = 0 := by
  have h1 : 9 - 12 * t ≤ 0 := by linarith
  rw [smoothPhi, Real.smoothTransition.zero_of_nonpos h1, mul_zero]

@[simp] lemma smoothSigma_zero : smoothSigma 0 = 0 := smoothSigma_eq_zero_of_le (by norm_num)
@[simp] lemma smoothSigma_one : smoothSigma 1 = 1 := smoothSigma_eq_one_of_le (by norm_num)
@[simp] lemma smoothPhi_zero : smoothPhi 0 = 0 := smoothPhi_eq_zero_of_lt (by norm_num)
@[simp] lemma smoothPhi_one : smoothPhi 1 = 0 := smoothPhi_eq_zero_of_gt (by norm_num)

/-! ## 4. The lifted homotopy and its nonvanishing -/

/-- **The lift of the homotopy**, in disk coordinates: `θ y = sqDisk (foldBox y)` never leaves the closed
disk, which is what makes the box-local perturbation data sufficient. -/
def diskHomotopyLift (V W : ℂ → Eucl 3) (χ : ℂ → ℝ) (p : Eucl 3)
    (q : ℝ × EuclideanSpace ℝ (Fin 2)) : Eucl 3 :=
  (1 - smoothSigma q.1) • V (sqDisk (foldBox q.2))
    + smoothSigma q.1 • W (sqDisk (foldBox q.2))
    + (smoothPhi q.1 * χ (sqDisk (foldBox q.2))) • p

/-- **The lifted homotopy never vanishes**: in each of the three ranges of `t` the formula reduces to one
of the three families of `DiskGood` (with the cutoff parameter in `[0,1]`). -/
lemma diskHomotopyLift_ne_zero (V W : ℂ → Eucl 3) (χ : ℂ → ℝ) (p : Eucl 3)
    (hnz : DiskGood V W χ p) (q : ℝ × EuclideanSpace ℝ (Fin 2)) :
    diskHomotopyLift V W χ p q ≠ 0 := by
  obtain ⟨t, y⟩ := q
  have hmem : ‖sqDisk (foldBox y)‖ ≤ 1 := norm_sqDisk_le_one _ (foldBox_mem_unitBox y)
  by_cases h0 : smoothSigma t = 0
  · have heq : diskHomotopyLift V W χ p (t, y)
        = V (sqDisk (foldBox y)) + (smoothPhi t * χ (sqDisk (foldBox y))) • p := by
      simp only [diskHomotopyLift, h0, sub_zero, one_smul, zero_smul, add_zero]
    rw [heq]
    exact hnz.2.1 _ hmem (smoothPhi t) (smoothPhi_mem t)
  · by_cases h1 : smoothSigma t = 1
    · have heq : diskHomotopyLift V W χ p (t, y)
          = W (sqDisk (foldBox y)) + (smoothPhi t * χ (sqDisk (foldBox y))) • p := by
        simp only [diskHomotopyLift, h1, sub_self, zero_smul, one_smul, zero_add]
      rw [heq]
      exact hnz.2.2 _ hmem (smoothPhi t) (smoothPhi_mem t)
    · have ht1 : 1 / 3 < t := by
        by_contra hc
        exact h0 (smoothSigma_eq_zero_of_le (not_lt.mp hc))
      have ht2 : t < 2 / 3 := by
        by_contra hc
        exact h1 (smoothSigma_eq_one_of_le (not_lt.mp hc))
      have hphi : smoothPhi t = 1 := smoothPhi_eq_one_of_mem ⟨le_of_lt ht1, le_of_lt ht2⟩
      have heq : diskHomotopyLift V W χ p (t, y)
          = (1 - smoothSigma t) • V (sqDisk (foldBox y))
            + smoothSigma t • W (sqDisk (foldBox y))
            + (χ (sqDisk (foldBox y))) • p := by
        simp only [diskHomotopyLift, hphi, one_mul]
      rw [heq]
      exact hnz.1 _ hmem (smoothSigma t) (smoothSigma_mem t)

/-- **The lift of the homotopy is smooth** (this is why the cutoffs of this file are the smooth
`smoothTransition`-based ones). -/
lemma contDiff_diskHomotopyLift (V W : ℂ → Eucl 3) (χ : ℂ → ℝ) (p : Eucl 3)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => diskHomotopyLift V W χ p q) := by
  have hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox q.2)) :=
    sqDisk_contDiff.comp (((contMDiff_iff_contDiff.mp foldBox_contMDiff).comp contDiff_snd))
  have hVθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => V (sqDisk (foldBox q.2))) := hV.comp hθ
  have hWθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => W (sqDisk (foldBox q.2))) := hW.comp hθ
  have hχθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => χ (sqDisk (foldBox q.2))) := hχ.comp hθ
  have hσ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => smoothSigma q.1) :=
    contDiff_smoothSigma.comp contDiff_fst
  have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => smoothPhi q.1) :=
    contDiff_smoothPhi.comp contDiff_fst
  unfold diskHomotopyLift
  exact (((contDiff_const.sub hσ).smul hVθ).add
    (hσ.smul hWθ)).add ((hφ.mul hχθ).smul contDiff_const)

/-! ## 5. The homotopy -/

/-- **The homotopy half of the ends clause, in disk coordinates.**  For two disk charts `D`, `E` with
nonvanishing lifts `V`, `W` that are **odd on the boundary circle** and a weight `χ` with the same
property, the box-local nonvanishing data `DiskGood V W χ p` produce a single homotopy `H` on all of
`ℝ × ℝ²`, with the two endpoints equal to the two class maps **as functions on all of `ℝ²`**, invariant
under the antipodal involution of the parameter square on the whole seam (so that the chain
`x ↦ H (x 2, ·)` satisfies `Work.Drive.Meet3Hyp`'s seam clause), continuous and — for the chain in the
third parameter — `C^∞` into `ℝP³`.

The two inputs beyond the perturbation data are the **oddness** on the boundary circle (the essentiality
of the two end class maps; for the linear end it is `Work.Drive.linVecC_neg`) and the `hgood` hypothesis
which `Work.Drive.exists_perturbation_disk` turns into `DiskGood`. -/
theorem exists_diskClassHomotopy
    (D E : ℂ → CappingSpace) (V W : ℂ → Eucl 3) (χ : ℂ → ℝ) (p : Eucl 3)
    (hVne : ∀ z, V z ≠ 0) (hWne : ∀ z, W z ≠ 0)
    (hVsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hWsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hχsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hVcls : IsClassLift D V hVne) (hWcls : IsClassLift E W hWne)
    (hVodd : ∀ z : ℂ, ‖z‖ = 1 → V (-z) = - V z)
    (hWodd : ∀ z : ℂ, ‖z‖ = 1 → W (-z) = - W z)
    (hχodd : ∀ z : ℂ, ‖z‖ = 1 → χ (-z) = - χ z)
    (hnz : DiskGood V W χ p) :
    ∃ H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3),
      (∀ y, H (0, y) = planeClassMap (diskPlane D) y) ∧
      (∀ y, H (1, y) = planeClassMap (diskPlane E) y) ∧
      (∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y → H (t, seamInv2 y) = H (t, y)) ∧
      Continuous H ∧
      ContMDiff (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1))) := by
  classical
  have hne : ∀ q : ℝ × EuclideanSpace ℝ (Fin 2), diskHomotopyLift V W χ p q ≠ 0 :=
    fun q => diskHomotopyLift_ne_zero V W χ p hnz q
  let H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3) :=
    fun q => Projectivization.mk ℝ (diskHomotopyLift V W χ p q) (hne q)
  have hH : ∀ q, H q = Projectivization.mk ℝ (diskHomotopyLift V W χ p q) (hne q) := fun _ => rfl
  -- the two endpoints
  have hl0 : ∀ y : EuclideanSpace ℝ (Fin 2),
      diskHomotopyLift V W χ p (0, y) = V (sqDisk (foldBox y)) := by
    intro y
    simp only [diskHomotopyLift, smoothSigma_zero, smoothPhi_zero, sub_zero, one_smul, zero_smul,
      zero_mul, add_zero]
  have hl1 : ∀ y : EuclideanSpace ℝ (Fin 2),
      diskHomotopyLift V W χ p (1, y) = W (sqDisk (foldBox y)) := by
    intro y
    simp only [diskHomotopyLift, smoothSigma_one, smoothPhi_one, sub_self, zero_smul, one_smul,
      zero_mul, add_zero, zero_add]
  -- the seam involution
  have hlseam : ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y →
      diskHomotopyLift V W χ p (t, seamInv2 y) = - diskHomotopyLift V W χ p (t, y) := by
    intro t y hy
    have hbox : foldBox y ∈ Submission.Drive.unitBox 1 := foldBox_mem_unitBox y
    have hnorm : ‖sqDisk (foldBox y)‖ = 1 :=
      (norm_sqDisk_eq_one_iff _ hbox).mpr (onSeam2_foldBox hy)
    have hθ : sqDisk (foldBox (seamInv2 y)) = - sqDisk (foldBox y) := by
      rw [foldBox_seamInv2, sqDisk_seamInv]
    simp only [diskHomotopyLift, hθ, hVodd _ hnorm, hWodd _ hnorm, hχodd _ hnorm]
    module
  refine ⟨H, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    rw [hH, planeClassMap_diskPlane_of_lift hVcls y, Projectivization.mk_eq_mk_iff]
    refine ⟨1, ?_⟩
    rw [hl0 y]
    simp
  · intro y
    rw [hH, planeClassMap_diskPlane_of_lift hWcls y, Projectivization.mk_eq_mk_iff]
    refine ⟨1, ?_⟩
    rw [hl1 y]
    simp
  · intro t y hy
    rw [hH, hH, Projectivization.mk_eq_mk_iff]
    refine ⟨(-1 : ℝˣ), ?_⟩
    rw [hlseam t y hy]
    simp
  · change Continuous (fun q => Projectivization.mk ℝ (diskHomotopyLift V W χ p q) (hne q))
    exact (continuous_projectivizationMk ℝ (Eucl 3)).comp
      (Continuous.subtype_mk
        (contDiff_diskHomotopyLift V W χ p hVsmooth hWsmooth hχsmooth).continuous hne)
  · intro x
    have hθ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) => sqDisk (foldBox (mk2 (x 0) (x 1)))) :=
      contDiff_comp_mk2 (sqDisk_contDiff.comp (contMDiff_iff_contDiff.mp foldBox_contMDiff))
    have hσ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) => smoothSigma (x 2)) :=
      contDiff_smoothSigma.comp coordCLM2.contDiff
    have hφ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) => smoothPhi (x 2)) :=
      contDiff_smoothPhi.comp coordCLM2.contDiff
    have hlift : ContMDiffAt (𝓡 3) (modelWithCornersSelf ℝ (Eucl 3))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) => diskHomotopyLift V W χ p (x 2, mk2 (x 0) (x 1))) x := by
      rw [contMDiffAt_iff_contDiffAt]
      have heq : (fun x : EuclideanSpace ℝ (Fin 3) =>
            diskHomotopyLift V W χ p (x 2, mk2 (x 0) (x 1)))
          = fun x => (1 - smoothSigma (x 2)) • V (sqDisk (foldBox (mk2 (x 0) (x 1))))
              + smoothSigma (x 2) • W (sqDisk (foldBox (mk2 (x 0) (x 1))))
              + (smoothPhi (x 2) * χ (sqDisk (foldBox (mk2 (x 0) (x 1))))) • p := rfl
      rw [heq]
      exact ((((contDiff_const.sub hσ').smul (hVsmooth.comp hθ')).add
        (hσ'.smul (hWsmooth.comp hθ'))).add
        ((hφ'.mul (hχsmooth.comp hθ')).smul contDiff_const)).contDiffAt
    exact contMDiffAt_projMk_general (𝓡 3)
      (fun x : EuclideanSpace ℝ (Fin 3) => diskHomotopyLift V W χ p (x 2, mk2 (x 0) (x 1)))
      (fun x => hne _) x hlift

/-! ## 6. The perturbation data is *dense* in the perturbation vector

The joint production of the two halves of `HasClassLinearization` (the homotopy of this file and the
transversality of the encoded chains, which is an *open dense* genericity statement in the same
parameter `p` by Sard) needs more than the existence of one good `p`: it needs the good set to be
**dense**, so that it meets the nonempty open set produced by the transversality argument.  This section
supplies that density, in the box form first (which is `Submission/Work/Drive/exists_perturbation_all_ne_zero.lean`'s
setting, whose closedness and empty-interior lemmas it reuses) and then in the disk form.
-/

/-- **The complement of a set of empty interior, inside an open dense set, is dense.**  This is the step
that combines the two kinds of avoidance: the *path* conditions avoid the closed cones `ℝ • V y` (open
dense good set), and the *interpolation* condition avoids a set of empty interior (dense, not open). -/
theorem Dense.sdiff_of_interior_eq_empty {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hs : Dense s) (hso : IsOpen s) (ht : interior t = ∅) : Dense (s \ t) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨p, hpU, hps⟩ := (dense_iff_inter_open.mp hs) U hU hUne
  by_contra hcon
  have hsub : U ∩ s ⊆ t := by
    intro q hq
    by_contra hqt
    exact hcon ⟨q, hq.1, hq.2, hqt⟩
  have hopen : IsOpen (U ∩ s) := hU.inter hso
  have hne : (U ∩ s).Nonempty := ⟨p, hpU, hps⟩
  have hsub' : U ∩ s ⊆ interior t := fun q hq =>
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hopen.mem_nhds hq) hsub)
  rw [ht] at hsub'
  exact hne.ne_empty (Set.eq_empty_iff_forall_notMem.mpr fun q hq => hsub' hq)

/-- The three nonvanishing conditions of the box-local perturbation lemma, as a set of perturbation
vectors. -/
def BoxNonzero (V W : EuclideanSpace ℝ (Fin 2) → Eucl 3) (χ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (p : Eucl 3) : Prop :=
  (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y ∈ Submission.Drive.unitBox 1,
      (1 - s) • V y + s • W y + (χ y) • p ≠ 0) ∧
  (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ y ∈ Submission.Drive.unitBox 1,
      V y + (t * χ y) • p ≠ 0) ∧
  (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ y ∈ Submission.Drive.unitBox 1,
      W y + (t * χ y) • p ≠ 0)

/-- **The box-local perturbation data is dense** in the perturbation vector: the union of the three bad
sets is contained in the union of a closed set of empty interior and a set of empty interior, so its
complement is dense. -/
theorem dense_boxNonzero (V W : EuclideanSpace ℝ (Fin 2) → Eucl 3)
    (χ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hVne : ∀ y, V y ≠ 0) (hWne : ∀ y, W y ≠ 0)
    (hgood : ∀ y ∈ Submission.Drive.unitBox 1, χ y = 0 →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (1 - s) • V y + s • W y ≠ 0) :
    Dense {p : Eucl 3 | BoxNonzero V W χ p} := by
  have hcV : IsClosed (rayCone V) := rayCone_isClosed V hV.continuous fun y _ => hVne y
  have hcW : IsClosed (rayCone W) := rayCone_isClosed W hW.continuous fun y _ => hWne y
  have hdV : Dense (rayCone V)ᶜ := by
    rw [dense_iff_closure_eq, closure_compl, rayCone_interior_eq_empty V hV, compl_empty]
  have hdW : Dense (rayCone W)ᶜ := by
    rw [dense_iff_closure_eq, closure_compl, rayCone_interior_eq_empty W hW, compl_empty]
  have hs : Dense ((rayCone V)ᶜ ∩ (rayCone W)ᶜ) :=
    hdV.inter_of_isOpen_left hdW hcV.isOpen_compl
  have hst : Dense (((rayCone V)ᶜ ∩ (rayCone W)ᶜ) \ interpBad V W χ) :=
    Dense.sdiff_of_interior_eq_empty hs (hcV.isOpen_compl.inter hcW.isOpen_compl)
      (interior_interpBad_eq_empty hV hW hχ)
  refine hst.mono ?_
  intro p hp
  obtain ⟨⟨hpV, hpW⟩, hpB⟩ := hp
  have hgood' : ∀ y ∈ Submission.Drive.unitBox 1, χ y = 0 →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, interpLiftP V W s y ≠ 0 := by
    intro y hy h0 s hs
    simpa only [interpLiftP] using hgood y hy h0 s hs
  exact ⟨fun s hs y hy =>
      interpLiftP_ne_zero_of_notMem_interpBad V W χ hgood' hpB s hs y hy,
    fun t ht y hy => path_ne_zero_of_notMem_rayCone V χ hVne hpV t ht y hy,
    fun t ht y hy => path_ne_zero_of_notMem_rayCone W χ hWne hpW t ht y hy⟩

/-- **The disk perturbation data is dense.**  The disk conditions and the box conditions are the same set
of perturbation vectors, because `Work.Drive.sqDisk` maps the box onto the closed disk. -/
theorem dense_diskGood (V W : ℂ → Eucl 3) (χ : ℂ → ℝ)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hVne : ∀ z, V z ≠ 0) (hWne : ∀ z, W z ≠ 0)
    (hgood : ∀ z : ℂ, ‖z‖ ≤ 1 → χ z = 0 →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (1 - s) • V z + s • W z ≠ 0) :
    Dense {p : Eucl 3 | DiskGood V W χ p} := by
  have hset : {p : Eucl 3 | DiskGood V W χ p}
      = {p : Eucl 3 | BoxNonzero (fun y : EuclideanSpace ℝ (Fin 2) => V (sqDisk y))
          (fun y : EuclideanSpace ℝ (Fin 2) => W (sqDisk y))
          (fun y : EuclideanSpace ℝ (Fin 2) => χ (sqDisk y)) p} := by
    ext p
    constructor
    · intro hp
      exact ⟨fun s hs y hy => hp.1 (sqDisk y) (norm_sqDisk_le_one y hy) s hs,
        fun t ht y hy => hp.2.1 (sqDisk y) (norm_sqDisk_le_one y hy) t ht,
        fun t ht y hy => hp.2.2 (sqDisk y) (norm_sqDisk_le_one y hy) t ht⟩
    · intro hp
      refine ⟨?_, ?_, ?_⟩
      · intro z hz s hs
        obtain ⟨y, hy, hzy⟩ := sqDisk_surjective z hz
        rw [← hzy]
        exact hp.1 s hs y hy
      · intro z hz t ht
        obtain ⟨y, hy, hzy⟩ := sqDisk_surjective z hz
        rw [← hzy]
        exact hp.2.1 t ht y hy
      · intro z hz t ht
        obtain ⟨y, hy, hzy⟩ := sqDisk_surjective z hz
        rw [← hzy]
        exact hp.2.2 t ht y hy
  rw [hset]
  refine (dense_boxNonzero (fun y : EuclideanSpace ℝ (Fin 2) => V (sqDisk y))
    (fun y : EuclideanSpace ℝ (Fin 2) => W (sqDisk y))
    (fun y : EuclideanSpace ℝ (Fin 2) => χ (sqDisk y))
    (hV.comp sqDisk_contDiff) (hW.comp sqDisk_contDiff) (hχ.comp sqDisk_contDiff)
    (fun y => hVne _) (fun y => hWne _) ?_).mono ?_
  · intro y hy h0 s hs
    exact hgood (sqDisk y) (norm_sqDisk_le_one y hy) h0 s hs
  · intro p hp
    exact hp

/-! ## 7. The two ends of the design: the chart and a linear plane -/

/-- **The linear plane chart's lift.**  The class of `linPlaneChart φ c hc z` is that of the vector
`φ (linVecC z)`, which is odd on the boundary circle (`Work.Drive.linVecC_neg`) and smooth. -/
theorem isClassLift_linPlaneChart (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c) :
    IsClassLift (linPlaneChart φ c hc) (fun z => φ (linVecC z))
      (fun z => phi_linVecC_ne_zero φ z) := by
  intro z
  rw [cappingSpaceHomeoProj_linPlaneChart]

/-- **The homotopy half of the ends clause for the design's two ends**: the chart's plane and the disk
model of a linear projective plane.  The chart contributes a smooth nonvanishing lift `V`, *odd on the
boundary circle* (the essentiality of the class map; see `Work.Drive.exists_odd_renormalization` for the
passage from "the parallelism factor is negative at one boundary point" to this form), a smooth weight
`χ` with the same parity, and the non-collision condition `hgood` at the zeros of `χ`; the linear plane
contributes the proved `Work.Drive.linVecC` (`Work.Drive.linVecC_neg` is its oddness).  The conclusion
is a single homotopy on all of `ℝ × ℝ²`, `C^∞` in the chain parameter, with both endpoints equal to the
two class maps *as functions on all of `ℝ²`* and invariant under the antipodal involution of the
parameter square on the whole seam — i.e. exactly the homotopy clauses of
`Work.Drive.HasClassLinearization`.

The perturbation vector `p` is produced existentially by the disk perturbation lemma; for the *joint*
production with the transversality half of `HasClassLinearization` use the density form
`Work.Drive.dense_diskGood` instead (the good set is dense, so it meets the nonempty open set that the
Sard argument produces). -/
theorem exists_diskClassHomotopy_linear (D : ℂ → CappingSpace) (V : ℂ → Eucl 3) (χ : ℂ → ℝ)
    (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (hVne : ∀ z, V z ≠ 0)
    (hVsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hχsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hVcls : IsClassLift D V hVne)
    (hVodd : ∀ z : ℂ, ‖z‖ = 1 → V (-z) = - V z)
    (hχodd : ∀ z : ℂ, ‖z‖ = 1 → χ (-z) = - χ z)
    (hgood : ∀ z : ℂ, ‖z‖ ≤ 1 → χ z = 0 →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (1 - s) • V z + s • (φ (linVecC z)) ≠ 0) :
    ∃ (p : Eucl 3) (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)),
      (∀ y, H (0, y) = planeClassMap (diskPlane D) y) ∧
      (∀ y, H (1, y) = planeClassMap (diskPlane (linPlaneChart φ c hc)) y) ∧
      (∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y → H (t, seamInv2 y) = H (t, y)) ∧
      Continuous H ∧
      ContMDiff (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1))) := by
  have hWsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => φ (linVecC z)) :=
    ((φ : Eucl 3 →L[ℝ] Eucl 3)).contDiff.comp linVecC_contDiff
  have hWne : ∀ z : ℂ, (fun z : ℂ => φ (linVecC z)) z ≠ 0 := fun z => phi_linVecC_ne_zero φ z
  have hWodd : ∀ z : ℂ, ‖z‖ = 1 → (fun z : ℂ => φ (linVecC z)) (-z)
      = - (fun z : ℂ => φ (linVecC z)) z := by
    intro z hz
    simp only
    rw [linVecC_neg hz, map_neg]
  obtain ⟨p, hp⟩ := exists_perturbation_disk V (fun z : ℂ => φ (linVecC z)) χ hVsmooth hWsmooth
    hχsmooth hVne hWne hgood
  exact ⟨p, exists_diskClassHomotopy D (linPlaneChart φ c hc) V (fun z : ℂ => φ (linVecC z)) χ p
    hVne hWne hVsmooth hWsmooth hχsmooth hVcls (isClassLift_linPlaneChart φ c hc) hVodd hWodd
    hχodd hp⟩

end

end Work.Drive
