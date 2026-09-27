import Mathlib
import Submission.Work.Drive.squareDisk
import Submission.Work.Drive.sqDisk_surjective
import Submission.Work.Drive.SeamSweep
import Submission.Work.Drive.CapSmooth.sweepChainSmooth
import Submission.Work.Drive.meet32_bordism_invariance
import Submission.Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet
import Submission.Work.Drive.ProjectiveTopology

/-!
# The plane as a chain: `C^∞` square presentations with a *global* seam identification

The counting engine (`Work.Drive.manifold_triple_inter_boundary_parity`,
`Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet`) consumes, for each of the three chains, a
`C^∞` map `D k : ℝ³ → Y` that is invariant under the antipodal involution `seamInv` of the parameter
cube **on the whole seam** `x k 0 ∈ {0,1} ∨ x k 1 ∈ {0,1}` (`Meet3Hyp.seam`), i.e. for *every* point of
those four lines, not only for the points of the unit cube.  For a sweep
`D k x = scaleCapping (sweepParam a x) (P (x 0, x 1))` this is exactly the requirement that the plane
presentation `P : ℝ² → Y` satisfy

> `P y = P (seamInv2 y)`  for **all** `y` with `onSeam2 y`

(`Work.Drive.sweepChain_seamInv`), and `P` must be `C^∞` on all of `ℝ²`.

This file makes that requirement *free* for the natural presentation of a plane: a `C^∞` map
`Q : ℂ → Y` of the closed disk whose boundary circle is antipodally identified — the disk model of
`ℝP²`, which is the form in which the concrete capped plane comes out of the strip/cap construction.
The device is the smooth fold

> `foldFun x = (1 - cos (π x)) / 2`,   `foldFun (1 - x) = 1 - foldFun x`,   `foldFun '' ℝ = [0,1]`,

applied to the two square coordinates:

* `Work.Drive.diskPlane Q y := Q (sqDisk (foldFun (y 0), foldFun (y 1)))` is `C^∞` on all of `ℝ²`
  (`contMDiff_diskPlane`) whenever `Q` is;
* it is seam-invariant on the *whole* of `onSeam2` (`diskPlane_seamInv2`), because the fold commutes
  with the antipodal involutions (`foldBox_seamInv2`) and sends the four seam lines into the square
  (`onSeam2_foldBox`, `foldBox_mem_unitBox`), where `sqDisk` lands on the unit circle
  (`norm_sqDisk_eq_one_iff`) and the disk presentation's antipodal invariance applies;
* its range is the same as that of `Q` on the closed disk (`range_diskPlane`, using
  `Work.Drive.sqDisk_surjective` and `foldFun`'s surjectivity).

Consequently the two fields of `Meet3Hyp` that are *not* genericity data are automatic for the sweeps
of such planes (`seam_sweepChain_of_disk`), and the only remaining input for the parity identity
`Σ_k top_k ≡ Σ_k bottom_k` on the concrete chains is the *genericity data*
(`Work.Drive.Meet3Generic`: transversality at the triple points + the face condition) — see the payoff
`Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet_sweeps`.  The file also supplies the missing
`T2Space` instance for the capping space (`t2Space_cappingSpace`), which the engine's `[T2Space M]`
requires.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold

noncomputable section

/-! ## 1. The smooth fold -/

/-- The smooth fold used to bring the four seam lines `y 0 ∈ {0,1}`, `y 1 ∈ {0,1}` of the parameter
plane into the unit square: it lies in `[0,1]`, maps onto `[0,1]`, and satisfies
`foldFun (1 - x) = 1 - foldFun x`. -/
def foldFun (x : ℝ) : ℝ := (1 - Real.cos (Real.pi * x)) / 2

@[simp] lemma foldFun_zero : foldFun 0 = 0 := by simp [foldFun]

@[simp] lemma foldFun_one : foldFun 1 = 1 := by
  simp [foldFun, Real.cos_pi]

/-- The fold is symmetric about the point `(1/2, 1/2)`. -/
lemma foldFun_symm (x : ℝ) : foldFun (1 - x) = 1 - foldFun x := by
  have h : Real.pi * (1 - x) = Real.pi - Real.pi * x := by ring
  rw [foldFun, foldFun, h, Real.cos_pi_sub]
  ring

lemma foldFun_mem_Icc (x : ℝ) : foldFun x ∈ Set.Icc (0 : ℝ) 1 := by
  have h1 : Real.cos (Real.pi * x) ≤ 1 := Real.cos_le_one _
  have h2 : -1 ≤ Real.cos (Real.pi * x) := Real.neg_one_le_cos _
  simp only [foldFun, Set.mem_Icc]
  constructor <;> linarith

lemma foldFun_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) foldFun := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => Real.cos (Real.pi * x)) :=
    Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)
  exact (contDiff_const.sub h).div_const 2

/-- The fold is onto `[0,1]`. -/
lemma foldFun_surjOn : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ x : ℝ, foldFun x = t := by
  intro t ht
  refine ⟨Real.arccos (1 - 2 * t) / Real.pi, ?_⟩
  have h1 : -1 ≤ 1 - 2 * t := by linarith [ht.2]
  have h2 : 1 - 2 * t ≤ 1 := by linarith [ht.1]
  rw [foldFun, show Real.pi * (Real.arccos (1 - 2 * t) / Real.pi)
      = Real.arccos (1 - 2 * t) by field_simp, Real.cos_arccos h1 h2]
  ring

/-! ## 2. The folded square coordinates -/

/-- The fold applied to both square coordinates. -/
def foldBox (y : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  mk2 (foldFun (y 0)) (foldFun (y 1))

@[simp] lemma foldBox_apply_zero (y : EuclideanSpace ℝ (Fin 2)) :
    foldBox y 0 = foldFun (y 0) := rfl

@[simp] lemma foldBox_apply_one (y : EuclideanSpace ℝ (Fin 2)) :
    foldBox y 1 = foldFun (y 1) := rfl

/-- The fold commutes with the antipodal involution of the parameter square. -/
lemma foldBox_seamInv2 (y : EuclideanSpace ℝ (Fin 2)) :
    foldBox (seamInv2 y) = seamInv2 (foldBox y) := by
  ext i
  fin_cases i <;> simp [foldBox, seamInv2, foldFun_symm]

/-- The fold sends the seam into the seam. -/
lemma onSeam2_foldBox {y : EuclideanSpace ℝ (Fin 2)} (hy : onSeam2 y) :
    onSeam2 (foldBox y) := by
  rcases hy with h | h | h | h
  · exact Or.inl (by rw [foldBox_apply_zero, h, foldFun_zero])
  · exact Or.inr (Or.inl (by rw [foldBox_apply_zero, h, foldFun_one]))
  · exact Or.inr (Or.inr (Or.inl (by rw [foldBox_apply_one, h, foldFun_zero])))
  · exact Or.inr (Or.inr (Or.inr (by rw [foldBox_apply_one, h, foldFun_one])))

/-- The fold lands in the unit square. -/
lemma foldBox_mem_unitBox (y : EuclideanSpace ℝ (Fin 2)) :
    foldBox y ∈ Submission.Drive.unitBox 1 :=
  fun i => by
    fin_cases i
    · simpa using foldFun_mem_Icc (y 0)
    · simpa using foldFun_mem_Icc (y 1)

lemma foldBox_contMDiff :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) foldBox := by
  intro y
  rw [contMDiffAt_iff_contDiffAt]
  have hf : foldBox = fun w : EuclideanSpace ℝ (Fin 2) =>
      WithLp.toLp 2 (![foldFun (w 0), foldFun (w 1)] : Fin 2 → ℝ) := by
    funext w
    rfl
  rw [hf, contDiffAt_piLp (p := 2) (E := fun _ : Fin 2 => ℝ)]
  intro i
  fin_cases i
  · exact ((foldFun_contDiff.comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff).contDiffAt)
  · exact ((foldFun_contDiff.comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).contDiff).contDiffAt)

lemma mk2_eta (y : EuclideanSpace ℝ (Fin 2)) : mk2 (y 0) (y 1) = y := by
  rw [mk2]
  have h : (![y 0, y 1] : Fin 2 → ℝ) = fun i : Fin 2 => y i := by
    funext i
    fin_cases i <;> simp
  rw [h]

/-- Every point of the unit square is a value of the fold: `foldBox` maps `ℝ²` onto `[0,1]²`. -/
lemma exists_foldBox_eq {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ Submission.Drive.unitBox 1) :
    ∃ w : EuclideanSpace ℝ (Fin 2), foldBox w = y := by
  obtain ⟨s, hs⟩ := foldFun_surjOn (y 0) (hy 0)
  obtain ⟨t, ht⟩ := foldFun_surjOn (y 1) (hy 1)
  refine ⟨mk2 s t, ?_⟩
  rw [foldBox, mk2_apply_zero, mk2_apply_one, hs, ht]
  exact mk2_eta y

/-! ## 3. The plane chain of a disk presentation -/

/-- **The plane chain presented by a map of the closed disk.**  The two square coordinates are folded
into `[0,1]` and then sent to the disk by the square-to-disk map `Work.Drive.sqDisk`.  This is a map
on all of `ℝ²`, so that `Work.Drive.sweepChain` of it is defined and smooth on all of `ℝ³`. -/
def diskPlane (Q : ℂ → CappingSpace) : EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  fun y => Q (sqDisk (foldBox y))

lemma diskPlane_apply (Q : ℂ → CappingSpace) (y : EuclideanSpace ℝ (Fin 2)) :
    diskPlane Q y = Q (sqDisk (foldBox y)) := rfl

/-- **The seam invariance of a disk-presented plane.**  If the disk presentation of the plane agrees
with itself at antipodal points of the boundary circle, then the folded square presentation agrees
with itself under the antipodal involution of the square on *every* point of the seam. -/
theorem diskPlane_seamInv2 {Q : ℂ → CappingSpace}
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z) {y : EuclideanSpace ℝ (Fin 2)}
    (hy : onSeam2 y) : diskPlane Q (seamInv2 y) = diskPlane Q y := by
  have hbox : foldBox y ∈ Submission.Drive.unitBox 1 := foldBox_mem_unitBox y
  have hseam : onSeam2 (foldBox y) := onSeam2_foldBox hy
  have hnorm : ‖sqDisk (foldBox y)‖ = 1 := (norm_sqDisk_eq_one_iff _ hbox).mpr hseam
  calc diskPlane Q (seamInv2 y)
      = Q (sqDisk (seamInv2 (foldBox y))) := by
        rw [diskPlane_apply, foldBox_seamInv2]
    _ = Q (- sqDisk (foldBox y)) := by rw [sqDisk_seamInv]
    _ = Q (sqDisk (foldBox y)) := hQseam _ hnorm
    _ = diskPlane Q y := rfl

/-- **The range of the folded presentation is the disk presentation's range on the closed disk.** -/
theorem range_diskPlane (Q : ℂ → CappingSpace) :
    Set.range (diskPlane Q) = Q '' {z : ℂ | ‖z‖ ≤ 1} := by
  ext w
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨sqDisk (foldBox y), norm_sqDisk_le_one _ (foldBox_mem_unitBox y), rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨y, hy, rfl⟩ := sqDisk_surjective z hz
    obtain ⟨w, hw⟩ := exists_foldBox_eq hy
    exact ⟨w, by rw [diskPlane_apply, hw]⟩

/-! ## 4. The genericity data of the engine, and the assembly of `Meet3Hyp` -/

/-- **The genericity data of the engine**: the two fields of `Work.Drive.Meet3Hyp` that are not
determined by the smoothness and the seam invariance of the three chains — transversality at every
triple point of the parameter cubes, and the face condition (at every boundary triple point exactly
one coordinate of exactly one parameter is on a face, crossed transversally). -/
structure Meet3Generic (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) : Prop where
  trans : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) →
      D 0 (x 0) = D 1 (x 1) → D 0 (x 0) = D 2 (x 2) →
      TripleTransverse
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 0) (x 0))
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 1) (x 1))
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 2) (x 2))
  face : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) →
      D 0 (x 0) = D 1 (x 1) → D 0 (x 0) = D 2 (x 2) →
      (∃ k, x k ∈ Submission.Drive.unitBoxBdry 2) →
      ∃ (k : Fin 3) (i : Fin 3), (x k i = 0 ∨ x k i = 1) ∧
        (∀ j : Fin 3, j ≠ i → x k j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ v : Fin 3 → EuclideanSpace ℝ (Fin 3),
          TripleCommonDir
            (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 0) (x 0))
            (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 1) (x 1))
            (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 2) (x 2)) v ∧
          v k i ≠ 0

/-- **The engine's hypotheses from smoothness, genericity and seam invariance.** -/
theorem meet3Hyp_of_generic {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hsm : ∀ k, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (D k))
    (hgen : Meet3Generic M D)
    (hseam : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)), onSeam x → D k x = D k (seamInv x)) :
    Meet3Hyp M D :=
  ⟨hsm, hgen.trans, hgen.face, hseam⟩

/-- The seam is disjoint from the two slices at the boundary triple intersections, from the face
condition alone.  This is the hypothesis `hdisj` of `Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet`
(which the reviewer of that lemma noted is redundant given the face condition). -/
lemma not_seam_and_slice_of_generic {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (hgen : Meet3Generic M D) (k : Fin 3) :
    ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3), x ∈ tripleBdryMeet M D k →
      ¬ (onSeam (x k) ∧ (x k 2 = 0 ∨ x k 2 = 1)) := by
  have huniq : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3), x ∈ tripleBdryMeet M D k →
      ∃ (k' : Fin 3) (i : Fin 3), (x k' i = 0 ∨ x k' i = 1) ∧
        (∀ j : Fin 3, j ≠ i → x k' j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ k'' : Fin 3, k'' ≠ k' → ∀ j : Fin 3, x k'' j ∈ Set.Ioo (0 : ℝ) 1) := by
    rintro x hx
    obtain ⟨k', i, h1, h2, h3, v, hv, hne⟩ := hgen.face x hx.1 hx.2.1 hx.2.2.1 ⟨k, hx.2.2.2⟩
    exact ⟨k', i, h1, h2, h3⟩
  obtain ⟨hdst, hdsb, -⟩ := disjoint_seam_top_bottom M D k huniq
  rintro x hx ⟨hs, hh⟩
  rcases hh with h | h
  · exact Set.disjoint_left.mp hdsb ⟨hx, hs⟩ ⟨hx, h⟩
  · exact Set.disjoint_left.mp hdst ⟨hx, hs⟩ ⟨hx, h⟩

/-! ## 5. The capping space case -/

section Capping

/-- **The capping space is Hausdorff**, transported from `(0,∞) × ℝP³` along the concrete
homeomorphism.  The counting engine requires `[T2Space M]`, and this instance is not in the library. -/
theorem t2Space_cappingSpace : T2Space Work.Drive.CappingSpace :=
  Work.Drive.cappingSpaceHomeoProj.symm.t2Space

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace

/-- **Smoothness of a disk-presented plane.** -/
theorem contMDiff_diskPlane {Q : ℂ → CappingSpace}
    (hQ : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) Q) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (diskPlane Q) := by
  have hsq : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) sqDisk :=
    contMDiff_iff_contDiff.mpr sqDisk_contDiff
  exact hQ.comp (hsq.comp foldBox_contMDiff)

/-- **The seam condition of `Meet3Hyp` for the sweep of a disk-presented plane.**  The `hP` hypothesis
of `Work.Drive.sweepChain_seamInv` is discharged by `Work.Drive.diskPlane_seamInv2`. -/
theorem seam_sweepChain_of_disk {Q : ℂ → CappingSpace}
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z) (a : ℝ) (ha : 0 < a)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : onSeam x) :
    sweepChain a ha (diskPlane Q) x = sweepChain a ha (diskPlane Q) (seamInv x) :=
  sweepChain_seamInv a ha (diskPlane Q)
    (fun y hy => (diskPlane_seamInv2 hQseam hy).symm) x hx

/-- **The three sweeps of disk-presented planes satisfy the engine's hypotheses.**  Smoothness is
`Work.Drive.CapSmooth.sweepChainSmooth`, the seam invariance is
`Work.Drive.seam_sweepChain_of_disk`, and the two remaining fields are the genericity data.  This is
the form in which the counting half consumes the concrete chains. -/
theorem meet3Hyp_sweeps
    (Q : Fin 3 → ℂ → CappingSpace) (a : Fin 3 → ℝ) (ha : ∀ k, 0 < a k)
    (hQ : ∀ k : Fin 3, ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (Q k))
    (hQseam : ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 → Q k (-z) = Q k z)
    (hgen : Meet3Generic CappingSpace
      (fun k => sweepChain (a k) (ha k) (diskPlane (Q k)))) :
    Meet3Hyp CappingSpace (fun k => sweepChain (a k) (ha k) (diskPlane (Q k))) :=
  meet3Hyp_of_generic _ (fun k => CapSmooth.sweepChainSmooth (a k) (ha k) (diskPlane (Q k))
    (contMDiff_diskPlane (hQ k))) hgen
    (fun k x hx => seam_sweepChain_of_disk (hQseam k) (a k) (ha k) x hx)

/-- **The parity identity `Σ_k top_k ≡ Σ_k bottom_k` for the sweeps of disk-presented planes.**  The
only inputs beyond the disk presentations and their antipodal boundary invariance are the *genericity
data* of the three sweeps; smoothness and the seam invariance of the three chains are automatic. -/
theorem even_sum_topBdryMeet_add_bottomBdryMeet_sweeps
    (Q : Fin 3 → ℂ → CappingSpace) (a : Fin 3 → ℝ) (ha : ∀ k, 0 < a k)
    (hQ : ∀ k : Fin 3, ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (Q k))
    (hQseam : ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 → Q k (-z) = Q k z)
    (hgen : Meet3Generic CappingSpace
      (fun k => sweepChain (a k) (ha k) (diskPlane (Q k)))) :
    Even (((topBdryMeet CappingSpace (fun k => sweepChain (a k) (ha k) (diskPlane (Q k))) 0).ncard
        + (bottomBdryMeet CappingSpace (fun k => sweepChain (a k) (ha k) (diskPlane (Q k))) 0).ncard)
      + ((topBdryMeet CappingSpace (fun k => sweepChain (a k) (ha k) (diskPlane (Q k))) 1).ncard
        + (bottomBdryMeet CappingSpace (fun k => sweepChain (a k) (ha k) (diskPlane (Q k))) 1).ncard)
      + ((topBdryMeet CappingSpace (fun k => sweepChain (a k) (ha k) (diskPlane (Q k))) 2).ncard
        + (bottomBdryMeet CappingSpace (fun k => sweepChain (a k) (ha k) (diskPlane (Q k))) 2).ncard)) := by
  exact even_sum_topBdryMeet_add_bottomBdryMeet CappingSpace _
    (meet3Hyp_sweeps Q a ha hQ hQseam hgen) (not_seam_and_slice_of_generic _ hgen)

end Capping

end

end Work.Drive
