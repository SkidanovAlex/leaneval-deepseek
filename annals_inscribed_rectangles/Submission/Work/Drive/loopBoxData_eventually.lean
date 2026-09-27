import Mathlib
import Submission.Work.Drive.boxThreeDefs
import Submission.Work.Drive.continuousAt_partial_fderiv
import Submission.Work.Drive.range_sup_eq_top_of_chartedDiff_surjective_real
import Submission.Work.Drive.geometricLocality
import Submission.Work.Sard.weak_interior_empty_open
import Submission.Work.Drive.chartDiffRangeBridge
import Submission.Work.Drive.exists_sigma_tau_of_faceSurjective

/-!
# `LoopBoxData` is an open property of the loop/chain family

`Work.Drive.loopBoxData_eventually`: if the two-clause regularity datum `Work.Drive.LoopBoxData`
holds for the pair `(A 0, D 0)` of a *jointly smooth* family of loops `A p : ℝ² → M` and chains
`D p : ℝ³ → M`, then it holds for all `p` near `0`.

The proof works in the `Amb 4 = ℝ⁵` model of the five-box (the charted difference system of the two
families), where all the clauses of `LoopBoxData` become *open* conditions on the charted derivative
`(p, y) ↦ fderiv ℝ (chartDiff c (A p) (D p)) y`:

* the transversality clause is the surjectivity of that derivative
  (`chartDiff_surjective_iff_range_sup_eq_top`);
* the face clause is the surjectivity of its restriction to a coordinate hyperplane
  (`exists_sigma_tau_of_faceSurjective` for the direction, `chartDiff_face_of_kernel` for the
  converse), and *that* is an open condition in the derivative.

The charted derivative is continuous in `(p, y)` (`continuousAt_partial_fderiv`), so both clauses hold
in a neighbourhood of every base meet; a compactness/contradiction argument on the box `unitBox 4`
(where the base meets live) finishes.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-! ## The charted difference system of a loop/chain family -/

/-- The chart `chr c` is `C^∞` on its source. -/
lemma loopBox_contMDiffOn_chr (c : M) :
    ContMDiffOn (𝓡 4) (𝓡 4) Ctop (chr c) (chr c).source := by
  have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := c) (n := Ctop)
  simpa [chr] using h

/-- The charted difference of a loop/chain family in the chart at `c`. -/
def loopBoxFamDiff (c : M) (A : P → EuclideanSpace ℝ (Fin 2) → M)
    (D : P → EuclideanSpace ℝ (Fin 3) → M) (q : P × Amb 4) : Tgt 4 :=
  chr c (A q.1 (sqPart q.2)) - chr c (D q.1 (cbPart q.2))

/-- The chart region of the loop/chain family: the parameters at which both values lie in the source
of the chart `chr c`. -/
def loopBoxFamRegion (c : M) (A : P → EuclideanSpace ℝ (Fin 2) → M)
    (D : P → EuclideanSpace ℝ (Fin 3) → M) : Set (P × Amb 4) :=
  {q | A q.1 (sqPart q.2) ∈ (chr c).source ∧ D q.1 (cbPart q.2) ∈ (chr c).source}

@[simp] lemma mem_loopBoxFamRegion {c : M} {A : P → EuclideanSpace ℝ (Fin 2) → M}
    {D : P → EuclideanSpace ℝ (Fin 3) → M} {q : P × Amb 4} :
    q ∈ loopBoxFamRegion c A D ↔
      A q.1 (sqPart q.2) ∈ (chr c).source ∧ D q.1 (cbPart q.2) ∈ (chr c).source := Iff.rfl

lemma contMDiff_sqPart :
    ContMDiff (𝓘(ℝ, Amb 4)) (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) Ctop
      (sqPart : Amb 4 → EuclideanSpace ℝ (Fin 2)) := by
  have h : (sqPart : Amb 4 → EuclideanSpace ℝ (Fin 2)) = ⇑sqPartCLM := by
    funext x; exact sqPartCLM_eq_sqPart x
  rw [h]
  exact sqPartCLM.contMDiff

lemma contMDiff_cbPart :
    ContMDiff (𝓘(ℝ, Amb 4)) (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) Ctop
      (cbPart : Amb 4 → EuclideanSpace ℝ (Fin 3)) := by
  have h : (cbPart : Amb 4 → EuclideanSpace ℝ (Fin 3)) = ⇑cbPartCLM := by
    funext x; exact cbPartCLM_eq_cbPart x
  rw [h]
  exact cbPartCLM.contMDiff

/-- The loop family pulled back to the five-box is jointly smooth. -/
lemma contMDiff_loopBoxSqFam (A : P → EuclideanSpace ℝ (Fin 2) → M)
    (hA : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2)) :
    ContMDiff (𝓘(ℝ, P × Amb 4)) (𝓡 4) Ctop (fun q : P × Amb 4 => A q.1 (sqPart q.2)) := by
  have hmid : ContMDiff (𝓘(ℝ, P × Amb 4)) (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) Ctop
      (fun q : P × Amb 4 => (q.1, sqPart q.2)) := by
    rw [contMDiff_iff_contDiff]
    have heq : (fun q : P × Amb 4 => (q.1, sqPart q.2))
        = fun q : P × Amb 4 => (q.1, sqPartCLM q.2) := by
      funext q; rw [sqPartCLM_eq_sqPart]
    rw [heq]
    fun_prop
  exact hA.comp hmid

/-- The chain family pulled back to the five-box is jointly smooth. -/
lemma contMDiff_loopBoxCbFam (D : P → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 3) => D q.1 q.2)) :
    ContMDiff (𝓘(ℝ, P × Amb 4)) (𝓡 4) Ctop (fun q : P × Amb 4 => D q.1 (cbPart q.2)) := by
  have hmid : ContMDiff (𝓘(ℝ, P × Amb 4)) (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) Ctop
      (fun q : P × Amb 4 => (q.1, cbPart q.2)) := by
    rw [contMDiff_iff_contDiff]
    have heq : (fun q : P × Amb 4 => (q.1, cbPart q.2))
        = fun q : P × Amb 4 => (q.1, cbPartCLM q.2) := by
      funext q; rw [cbPartCLM_eq_cbPart]
    rw [heq]
    fun_prop
  exact hD.comp hmid

/-- The chart region of the family is open. -/
lemma isOpen_loopBoxFamRegion (c : M) (A : P → EuclideanSpace ℝ (Fin 2) → M)
    (D : P → EuclideanSpace ℝ (Fin 3) → M)
    (hA : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2))
    (hD : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 3) => D q.1 q.2)) :
    IsOpen (loopBoxFamRegion c A D) := by
  have h1 := (contMDiff_loopBoxSqFam A hA).continuous
  have h2 := (contMDiff_loopBoxCbFam D hD).continuous
  exact (h1.isOpen_preimage _ (chr c).open_source).inter
    (h2.isOpen_preimage _ (chr c).open_source)

/-- The charted difference system of the family is smooth on the chart region. -/
lemma contDiffOn_loopBoxFamDiff (c : M) (A : P → EuclideanSpace ℝ (Fin 2) → M)
    (D : P → EuclideanSpace ℝ (Fin 3) → M)
    (hA : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2))
    (hD : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 3) => D q.1 q.2)) :
    ContDiffOn ℝ Ctop (loopBoxFamDiff c A D) (loopBoxFamRegion c A D) := by
  have hsq := contMDiff_loopBoxSqFam A hA
  have hcb := contMDiff_loopBoxCbFam D hD
  have h1 : ContMDiffOn (𝓘(ℝ, P × Amb 4)) (𝓡 4) Ctop
      (fun q : P × Amb 4 => chr c (A q.1 (sqPart q.2))) (loopBoxFamRegion c A D) :=
    (loopBox_contMDiffOn_chr c).comp hsq.contMDiffOn (fun q hq => hq.1)
  have h2 : ContMDiffOn (𝓘(ℝ, P × Amb 4)) (𝓡 4) Ctop
      (fun q : P × Amb 4 => chr c (D q.1 (cbPart q.2))) (loopBoxFamRegion c A D) :=
    (loopBox_contMDiffOn_chr c).comp hcb.contMDiffOn (fun q hq => hq.2)
  have h3 := h1.sub h2
  have h4 : ContMDiffOn (𝓘(ℝ, P × Amb 4)) (𝓡 4) Ctop (loopBoxFamDiff c A D)
      (loopBoxFamRegion c A D) := h3
  exact contMDiffOn_iff_contDiffOn.mp h4

/-- **The partial derivative of the charted difference system is continuous** in the parameter. -/
lemma continuousAt_loopBoxFamDiff_fderiv (c : M) (A : P → EuclideanSpace ℝ (Fin 2) → M)
    (D : P → EuclideanSpace ℝ (Fin 3) → M)
    (hA : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2))
    (hD : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 3) => D q.1 q.2))
    {q₀ : P × Amb 4} (hq₀ : q₀ ∈ loopBoxFamRegion c A D) :
    ContinuousAt (fun q : P × Amb 4 =>
      fderiv ℝ (fun y : Amb 4 => loopBoxFamDiff c A D (q.1, y)) q.2) q₀ :=
  continuousAt_partial_fderiv (isOpen_loopBoxFamRegion c A D hA hD)
    (loopBoxFamDiff c A D) (contDiffOn_loopBoxFamDiff c A D hA hD) hq₀

/-! ## The five-box form of `LoopBoxData` -/

/-- The intrinsic transversality clause, read at a five-box point. -/
def loopBoxTransAt (A : EuclideanSpace ℝ (Fin 2) → M) (D : EuclideanSpace ℝ (Fin 3) → M)
    (y : Amb 4) : Prop :=
  LinearMap.range (mfderiv (𝓡 2) (𝓡 4) A (sqPart y)).toLinearMap ⊔
    LinearMap.range (mfderiv (𝓡 3) (𝓡 4) D (cbPart y)).toLinearMap = ⊤

/-- The face clause, read at a five-box point: one coordinate is on a face, all the others are
strictly interior, and the two derivatives have a common direction whose block vector has non-zero
component in that coordinate. -/
def loopBoxFaceAt (A : EuclideanSpace ℝ (Fin 2) → M) (D : EuclideanSpace ℝ (Fin 3) → M)
    (y : Amb 4) : Prop :=
  ∃ i : Fin 5, (y i = 0 ∨ y i = 1) ∧ (∀ j : Fin 5, j ≠ i → y j ∈ Set.Ioo (0 : ℝ) 1) ∧
    ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
      mfderiv (𝓡 2) (𝓡 4) A (sqPart y) σ = mfderiv (𝓡 3) (𝓡 4) D (cbPart y) τ ∧
        mkPart σ τ i ≠ 0

/-- **`LoopBoxData` in the five-box form**: both clauses are attached to a point of the five-box. -/
def LoopBoxData5 (A : EuclideanSpace ℝ (Fin 2) → M) (D : EuclideanSpace ℝ (Fin 3) → M) : Prop :=
  ∀ y : Amb 4, y ∈ Submission.Drive.unitBox 4 → A (sqPart y) = D (cbPart y) →
    (loopBoxTransAt A D y ∧
      (y ∈ Submission.Drive.unitBoxBdry 4 → loopBoxFaceAt A D y))

/-- The single-point form of `LoopBoxData5` with the box membership as the only hypothesis: this is
the predicate whose *eventual* truth at a base meet is the content of the proof. -/
def loopBoxGood (A : EuclideanSpace ℝ (Fin 2) → M) (D : EuclideanSpace ℝ (Fin 3) → M)
    (y : Amb 4) : Prop :=
  y ∈ Submission.Drive.unitBox 4 →
    (loopBoxTransAt A D y ∧
      (y ∈ Submission.Drive.unitBoxBdry 4 → loopBoxFaceAt A D y))

lemma loopBoxData5_iff_forall_good (A : EuclideanSpace ℝ (Fin 2) → M)
    (D : EuclideanSpace ℝ (Fin 3) → M) :
    LoopBoxData5 A D ↔
      ∀ y : Amb 4, A (sqPart y) = D (cbPart y) → loopBoxGood A D y := by
  constructor
  · intro h y hmeet hy
    exact h y hy hmeet
  · intro h y hy hmeet
    exact h y hmeet hy

/-- The block coordinates of a five-box point `y` when all the remaining coordinates of the square
block are strictly interior. -/
lemma loopBox_five_of_sq {y : Amb 4} {i : Fin 2}
    (h2 : ∀ j : Fin 2, j ≠ i → (sqPart y) j ∈ Set.Ioo (0 : ℝ) 1)
    (h3 : ∀ j : Fin 3, (cbPart y) j ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ j : Fin 5, j ≠ Fin.castAdd 3 i → y j ∈ Set.Ioo (0 : ℝ) 1 := by
  intro j hj
  revert hj
  refine Fin.addCases (m := 2) (n := 3)
    (motive := fun j => j ≠ Fin.castAdd 3 i → y j ∈ Set.Ioo (0 : ℝ) 1) ?_ ?_ j
  · intro i' hi'
    have hne : i' ≠ i := fun h => hi' (by rw [h])
    have hmem := h2 i' hne
    simpa only [sqIdx, sqPart_apply] using hmem
  · intro j' _
    have hmem := h3 j'
    simpa only [cbIdx, cbPart_apply] using hmem

/-- The block analogue for the cube block. -/
lemma loopBox_five_of_cb {y : Amb 4} {j : Fin 3}
    (h1 : ∀ i : Fin 2, (sqPart y) i ∈ Set.Ioo (0 : ℝ) 1)
    (h2 : ∀ k : Fin 3, k ≠ j → (cbPart y) k ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ k : Fin 5, k ≠ Fin.natAdd 2 j → y k ∈ Set.Ioo (0 : ℝ) 1 := by
  intro k hk
  revert hk
  refine Fin.addCases (m := 2) (n := 3)
    (motive := fun k => k ≠ Fin.natAdd 2 j → y k ∈ Set.Ioo (0 : ℝ) 1) ?_ ?_ k
  · intro i' _
    have hmem := h1 i'
    simpa only [sqIdx, sqPart_apply] using hmem
  · intro j' hj'
    have hne : j' ≠ j := fun h => hj' (by rw [h])
    have hmem := h2 j' hne
    simpa only [cbIdx, cbPart_apply] using hmem

/-- The two blocks of the five-box are disjoint. -/
lemma loopBox_castAdd_ne_natAdd {i : Fin 2} {j : Fin 3} :
    Fin.castAdd 3 i ≠ Fin.natAdd 2 j := sqIdx_ne_cbIdx i j

/-- The two blocks of the five-box are disjoint. -/
lemma loopBox_natAdd_ne_castAdd {i : Fin 2} {j : Fin 3} :
    Fin.natAdd 2 j ≠ Fin.castAdd 3 i := (sqIdx_ne_cbIdx i j).symm

/-- The coordinates of `mkPart u x` in the `Fin.castAdd` form. -/
lemma loopBox_mkPart_castAdd (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3))
    (i : Fin 2) : (mkPart u x) (Fin.castAdd 3 i) = u i := mkPart_sqIdx u x i

/-- The coordinates of `mkPart u x` in the `Fin.natAdd` form. -/
lemma loopBox_mkPart_natAdd (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3))
    (j : Fin 3) : (mkPart u x) (Fin.natAdd 2 j) = x j := mkPart_cbIdx u x j

/-- **`LoopBoxData` is its five-box form.** -/
theorem loopBoxData_iff_five (A : EuclideanSpace ℝ (Fin 2) → M)
    (D : EuclideanSpace ℝ (Fin 3) → M) :
    LoopBoxData A D ↔ LoopBoxData5 A D := by
  constructor
  · rintro ⟨h1, h2⟩ y hy hmeet
    obtain ⟨hu, hx⟩ := (mem_unitBox_five_iff y).mp hy
    refine ⟨h1 (sqPart y) (cbPart y) hmeet hu hx, fun hybd => ?_⟩
    obtain ⟨-, hface⟩ := (mem_unitBoxBdry_five_iff y).mp hybd
    rcases hface with ⟨i, hi⟩ | ⟨j, hj⟩
    · have hbdu : sqPart y ∈ Submission.Drive.unitBoxBdry 1 :=
        (unitBoxBdry_iff 1 (sqPart y)).mpr ⟨hu, ⟨i, by simpa only [sqPart_apply] using hi⟩⟩
      rcases h2 (sqPart y) (cbPart y) hmeet hu hx (Or.inl hbdu) with
        ⟨i', hi', hrest, hxint, σ, τ, hστ, hσ⟩ | ⟨j', hj', hrest, huint, σ, τ, hστ, hτ⟩
      · refine ⟨sqIdx i', by simpa only [sqPart_apply] using hi',
          loopBox_five_of_sq hrest hxint, σ, τ, hστ, ?_⟩
        rw [mkPart_sqIdx]; exact hσ
      · refine ⟨cbIdx j', by simpa only [cbPart_apply] using hj',
          loopBox_five_of_cb huint hrest, σ, τ, hστ, ?_⟩
        rw [mkPart_cbIdx]; exact hτ
    · have hbdx : cbPart y ∈ Submission.Drive.unitBoxBdry 2 :=
        (unitBoxBdry_iff 2 (cbPart y)).mpr ⟨hx, ⟨j, by simpa only [cbPart_apply] using hj⟩⟩
      rcases h2 (sqPart y) (cbPart y) hmeet hu hx (Or.inr hbdx) with
        ⟨i', hi', hrest, hxint, σ, τ, hστ, hσ⟩ | ⟨j', hj', hrest, huint, σ, τ, hστ, hτ⟩
      · refine ⟨sqIdx i', by simpa only [sqPart_apply] using hi',
          loopBox_five_of_sq hrest hxint, σ, τ, hστ, ?_⟩
        rw [mkPart_sqIdx]; exact hσ
      · refine ⟨cbIdx j', by simpa only [cbPart_apply] using hj',
          loopBox_five_of_cb huint hrest, σ, τ, hστ, ?_⟩
        rw [mkPart_cbIdx]; exact hτ
  · intro h
    constructor
    · intro u x hmeet hu hx
      have hybox : mkPart u x ∈ Submission.Drive.unitBox 4 :=
        (mem_unitBox_five_iff _).mpr ⟨by rwa [sqPart_mkPart], by rwa [cbPart_mkPart]⟩
      have hmeet' : A (sqPart (mkPart u x)) = D (cbPart (mkPart u x)) := by
        rw [sqPart_mkPart, cbPart_mkPart]; exact hmeet
      have hres := (h (mkPart u x) hybox hmeet').1
      rw [loopBoxTransAt, sqPart_mkPart, cbPart_mkPart] at hres
      exact hres
    · intro u x hmeet hu hx hbd
      set y : Amb 4 := mkPart u x with hy
      have hybox : y ∈ Submission.Drive.unitBox 4 :=
        (mem_unitBox_five_iff _).mpr
          ⟨by rw [hy, sqPart_mkPart]; exact hu, by rw [hy, cbPart_mkPart]; exact hx⟩
      have hmeet' : A (sqPart y) = D (cbPart y) := by
        rw [hy, sqPart_mkPart, cbPart_mkPart]; exact hmeet
      have hybd : y ∈ Submission.Drive.unitBoxBdry 4 := by
        refine (unitBoxBdry_iff 4 y).mpr ⟨hybox, ?_⟩
        rcases hbd with hb | hb
        · obtain ⟨-, i, hi⟩ := (unitBoxBdry_iff 1 u).mp hb
          exact ⟨sqIdx i, by rw [hy, mkPart_sqIdx]; exact hi⟩
        · obtain ⟨-, j, hj⟩ := (unitBoxBdry_iff 2 x).mp hb
          exact ⟨cbIdx j, by rw [hy, mkPart_cbIdx]; exact hj⟩
      obtain ⟨i, hiface, hrest, σ, τ, hστ, hne⟩ := (h y hybox hmeet').2 hybd
      have hστ' : mfderiv (𝓡 2) (𝓡 4) A u σ = mfderiv (𝓡 3) (𝓡 4) D x τ := by
        have h2 : mfderiv (𝓡 2) (𝓡 4) A (sqPart (mkPart u x)) σ =
            mfderiv (𝓡 3) (𝓡 4) D (cbPart (mkPart u x)) τ := by
          rw [← hy]; exact hστ
        rwa [sqPart_mkPart, cbPart_mkPart] at h2
      clear hστ
      revert hiface hrest hne
      refine Fin.addCases (m := 2) (n := 3) (motive := fun i =>
        (y i = 0 ∨ y i = 1) → (∀ j : Fin 5, j ≠ i → y j ∈ Set.Ioo (0 : ℝ) 1) →
        (mkPart σ τ i ≠ 0) →
        ((∃ i : Fin 2, (u i = 0 ∨ u i = 1) ∧ (∀ j : Fin 2, j ≠ i → u j ∈ Set.Ioo (0 : ℝ) 1) ∧
            (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1) ∧
            ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
              mfderiv (𝓡 2) (𝓡 4) A u σ = mfderiv (𝓡 3) (𝓡 4) D x τ ∧ σ i ≠ 0)
          ∨ (∃ j : Fin 3, (x j = 0 ∨ x j = 1) ∧ (∀ k : Fin 3, k ≠ j → x k ∈ Set.Ioo (0 : ℝ) 1) ∧
            (∀ i : Fin 2, u i ∈ Set.Ioo (0 : ℝ) 1) ∧
            ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
              mfderiv (𝓡 2) (𝓡 4) A u σ = mfderiv (𝓡 3) (𝓡 4) D x τ ∧ τ j ≠ 0))) ?_ ?_ i
      · intro i' hi' hrest' hne'
        refine Or.inl ⟨i', ?_, ?_, ?_, σ, τ, hστ', ?_⟩
        · simpa only [hy, loopBox_mkPart_castAdd] using hi'
        · intro j hj
          have h5 := hrest' (Fin.castAdd 3 j) (fun hc => hj (Fin.castAdd_inj.mp hc))
          simpa only [hy, loopBox_mkPart_castAdd] using h5
        · intro j
          have h5 := hrest' (Fin.natAdd 2 j)
            (fun hc => loopBox_castAdd_ne_natAdd (i := i') (j := j) hc.symm)
          simpa only [hy, loopBox_mkPart_natAdd] using h5
        · simpa only [loopBox_mkPart_castAdd] using hne'
      · intro j' hj' hrest' hne'
        refine Or.inr ⟨j', ?_, ?_, ?_, σ, τ, hστ', ?_⟩
        · simpa only [hy, loopBox_mkPart_natAdd] using hj'
        · intro k hk
          have h5 := hrest' (Fin.natAdd 2 k) (fun hc => hk ((Fin.natAdd_inj 2).mp hc))
          simpa only [hy, loopBox_mkPart_natAdd] using h5
        · intro i
          have h5 := hrest' (Fin.castAdd 3 i)
            (fun hc => loopBox_castAdd_ne_natAdd (i := i) (j := j') hc)
          simpa only [hy, loopBox_mkPart_castAdd] using h5
        · simpa only [loopBox_mkPart_natAdd] using hne'

/-! ## The parameter is inserted as a constant -/

lemma loopBox_contMDiff_const (u : P) :
    ContMDiff (𝓡 2) (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) Ctop
      (fun q : EuclideanSpace ℝ (Fin 2) => (u, q)) := by
  rw [contMDiff_iff_contDiff]
  fun_prop

lemma loopBox_contMDiff_const3 (u : P) :
    ContMDiff (𝓡 3) (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) Ctop
      (fun q : EuclideanSpace ℝ (Fin 3) => (u, q)) := by
  rw [contMDiff_iff_contDiff]
  fun_prop

/-! ## The face-restricted surjectivity of a linear map is open -/

/-- The `i`-th component of the cofactor vector depends continuously on the linear map. -/
lemma loopBox_continuous_cofactorVec {m : ℕ} (i : Fin (m + 1)) :
    Continuous fun T : Amb m →L[ℝ] Tgt m => cofactorVec T i := by
  have hdet : Continuous fun T : Amb m →L[ℝ] Tgt m =>
      ((cofactorMatrix T).submatrix (Fin.succAbove i) id).det := by
    refine Continuous.matrix_det ?_
    refine continuous_pi fun a => continuous_pi fun b => ?_
    exact (by fun_prop : Continuous fun T : Amb m →L[ℝ] Tgt m =>
      T (EuclideanSpace.single (Fin.succAbove i a) 1) b)
  have h : Continuous fun T : Amb m →L[ℝ] Tgt m =>
      (-1 : ℝ) ^ (i : ℕ) * ((cofactorMatrix T).submatrix (Fin.succAbove i) id).det :=
    continuous_const.mul hdet
  simpa only [cofactorVec] using h

/-- The set of linear maps whose restriction to the coordinate hyperplane `{v | v i = 0}` is
surjective is open. -/
lemma loopBox_isOpen_surjective_domRestrict {m : ℕ} (i : Fin (m + 1)) :
    IsOpen {T : Amb m →L[ℝ] Tgt m |
      Function.Surjective (fun v : {v : Amb m // v i = 0} => T v.1)} := by
  have hset : ({T : Amb m →L[ℝ] Tgt m |
      Function.Surjective (fun v : {v : Amb m // v i = 0} => T v.1)})
      = {T : Amb m →L[ℝ] Tgt m | Function.Surjective T} ∩
        {T : Amb m →L[ℝ] Tgt m | cofactorVec T i ≠ 0} := by
    ext T
    constructor
    · intro h
      exact ⟨fun w => by obtain ⟨v, hv⟩ := h w; exact ⟨v.1, hv⟩,
        cofactorVec_apply_ne_zero T i h⟩
    · rintro ⟨hT, hc⟩
      exact (surjective_domRestrict_iff_cofactorVec_ne_zero T hT i).mpr hc
  rw [hset]
  exact (Work.Sard.isOpen_setOf_surjective_clm (E := Amb m) (F := Tgt m)).inter
    (isOpen_ne.preimage (loopBox_continuous_cofactorVec i))

/-! ## An abstract compactness reduction -/

/-- **The abstract openness argument.**  Let `meet : P → X → Prop` be a closed relation and `K` a
compact set.  If `Good p y` fails only on `K`, and at every base meet `y ∈ K` of `meet 0` the
predicate `Good` holds on a neighbourhood of `(0, y)`, then `Good` holds at every `meet p` for all
`p` near `0`. -/
theorem eventually_forall_meet_of_eventually {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace X] [FirstCountableTopology X]
    (meet : P → X → Prop) (hmeet : IsClosed {q : P × X | meet q.1 q.2})
    (K : Set X) (hK : IsCompact K) (Good : P → X → Prop)
    (hKg : ∀ p y, ¬ Good p y → y ∈ K)
    (hlocal : ∀ y ∈ K, meet 0 y → ∀ᶠ q in 𝓝 ((0 : P), y), meet q.1 q.2 → Good q.1 q.2) :
    ∀ᶠ p in 𝓝 (0 : P), ∀ y, meet p y → Good p y := by
  classical
  rw [Metric.eventually_nhds_iff]
  by_contra hcon
  push_neg at hcon
  choose p hp using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  choose y hy using fun n : ℕ => (hp n).2
  have hpt : Tendsto p atTop (𝓝 (0 : P)) := by
    have hsub : Tendsto (fun n : ℕ => p n - 0) atTop (𝓝 (0 : P)) := by
      refine squeeze_zero_norm' (a := fun n : ℕ => 1 / ((n : ℝ) + 1)) (Eventually.of_forall ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      intro n
      simpa only [dist_eq_norm, sub_zero] using le_of_lt (hp n).1
    simpa using hsub
  have hyK : ∀ n : ℕ, y n ∈ K := fun n => hKg _ _ (hy n).2
  obtain ⟨a, ha, φ, hφ, hya⟩ := hK.tendsto_subseq hyK
  have hpφ : Tendsto (fun k : ℕ => p (φ k)) atTop (𝓝 (0 : P)) := hpt.comp hφ.tendsto_atTop
  have hpair : Tendsto (fun k : ℕ => ((p (φ k), y (φ k)) : P × X)) atTop
      (𝓝 ((0 : P), a)) := Filter.Tendsto.prodMk_nhds hpφ hya
  have hmeet0 : meet 0 a :=
    hmeet.mem_of_tendsto hpair (Eventually.of_forall fun k => (hy (φ k)).1)
  have hev2 : ∀ᶠ k : ℕ in atTop, Good (p (φ k)) (y (φ k)) :=
    (hpair.eventually (hlocal a ha hmeet0)).mono fun k hk => hk (hy (φ k)).1
  obtain ⟨k, hk⟩ := hev2.exists
  exact (hy (φ k)).2 hk

/-! ## The local step: `Good` holds near a base meet -/

/-- **The local step.**  At a meet `y₀` of the base pair `(A 0, D 0)` satisfying `LoopBoxData`, the
single-point predicate `loopBoxGood` holds for all nearby parameters and points. -/
theorem loopBoxGood_eventually_at_meet (A : P → EuclideanSpace ℝ (Fin 2) → M)
    (D : P → EuclideanSpace ℝ (Fin 3) → M)
    (hA : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2))
    (hD : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 3) => D q.1 q.2))
    (h0 : LoopBoxData (A 0) (D 0))
    {y₀ : Amb 4} (hy₀ : y₀ ∈ Submission.Drive.unitBox 4)
    (hmeet₀ : A 0 (sqPart y₀) = D 0 (cbPart y₀)) :
    ∀ᶠ q : P × Amb 4 in 𝓝 ((0 : P), y₀),
      A q.1 (sqPart q.2) = D q.1 (cbPart q.2) → loopBoxGood (A q.1) (D q.1) q.2 := by
  classical
  have hbase := (loopBoxData_iff_five (A 0) (D 0)).mp h0
  obtain ⟨hTrans0, hFace0⟩ := hbase y₀ hy₀ hmeet₀
  set c : M := A 0 (sqPart y₀) with hc
  have hcx : c = D 0 (cbPart y₀) := by rw [hc]; exact hmeet₀
  have hreg0 : ((0 : P), y₀) ∈ loopBoxFamRegion c A D :=
    ⟨by simpa only [hc, chr] using mem_chart_source (EuclideanSpace ℝ (Fin 4)) (A 0 (sqPart y₀)),
      by rw [← hcx]
         simpa only [chr] using mem_chart_source (EuclideanSpace ℝ (Fin 4)) c⟩
  have hA0 : ContMDiff (𝓡 2) (𝓡 4) Ctop (A 0) := hA.comp (loopBox_contMDiff_const 0)
  have hD0 : ContMDiff (𝓡 3) (𝓡 4) Ctop (D 0) := hD.comp (loopBox_contMDiff_const3 0)
  -- the charted surjectivity at the base meet
  have hsurj0 : Function.Surjective
      (fderiv ℝ (fun y : Amb 4 => loopBoxFamDiff c A D ((0 : P), y)) y₀) := by
    have h := (chartDiff_surjective_iff_range_sup_eq_top c (A 0) (D 0) hA0 hD0
      (x := y₀) hreg0 hmeet₀).mpr hTrans0
    have heq : (fun y : Amb 4 => loopBoxFamDiff c A D ((0 : P), y)) = chartDiff c (A 0) (D 0) :=
      rfl
    rw [heq]
    exact h
  have hEvReg : ∀ᶠ q : P × Amb 4 in 𝓝 ((0 : P), y₀), q ∈ loopBoxFamRegion c A D :=
    (isOpen_loopBoxFamRegion c A D hA hD).mem_nhds hreg0
  have hcontG := continuousAt_loopBoxFamDiff_fderiv c A D hA hD hreg0
  have hEvSurj : ∀ᶠ q : P × Amb 4 in 𝓝 ((0 : P), y₀), Function.Surjective
      (fderiv ℝ (fun y : Amb 4 => loopBoxFamDiff c A D (q.1, y)) q.2) :=
    hcontG.preimage_mem_nhds
      ((Work.Sard.isOpen_setOf_surjective_clm (E := Amb 4) (F := Tgt 4)).mem_nhds hsurj0)
  -- clause 1 at a nearby parameter, from the charted surjectivity and the meet
  have clause1 : ∀ᶠ q : P × Amb 4 in 𝓝 ((0 : P), y₀),
      (A q.1 (sqPart q.2) = D q.1 (cbPart q.2) → q.2 ∈ Submission.Drive.unitBox 4 →
        loopBoxTransAt (A q.1) (D q.1) q.2) := by
    filter_upwards [hEvReg, hEvSurj] with q hreg hsurj hmeet _
    have hAq : ContMDiff (𝓡 2) (𝓡 4) Ctop (A q.1) := hA.comp (loopBox_contMDiff_const q.1)
    have hDq : ContMDiff (𝓡 3) (𝓡 4) Ctop (D q.1) := hD.comp (loopBox_contMDiff_const3 q.1)
    have hres := (chartDiff_surjective_iff_range_sup_eq_top c (A q.1) (D q.1) hAq hDq
      (x := q.2) hreg hmeet).mp hsurj
    simpa only [loopBoxTransAt] using hres
  by_cases hybd : y₀ ∈ Submission.Drive.unitBoxBdry 4
  · -- the base point is on the boundary: the face clause is inherited from the base witness
    obtain ⟨i, -, hrest0, σ0, τ0, hστ0, hne0⟩ := hFace0 hybd
    have hEvFace : ∀ᶠ q : P × Amb 4 in 𝓝 ((0 : P), y₀), Function.Surjective
        (fun v : {v : Amb 4 // v i = 0} =>
          fderiv ℝ (fun y : Amb 4 => loopBoxFamDiff c A D (q.1, y)) q.2 v.1) := by
      have hf0 := chartDiff_face_of_kernel c (A 0) (D 0) hA0 hD0 hreg0 hmeet₀ hsurj0 hστ0 hne0
      have hf0' : Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
          fderiv ℝ (fun y : Amb 4 => loopBoxFamDiff c A D ((0 : P), y)) y₀ v.1) := by
        have heq : (fun y : Amb 4 => loopBoxFamDiff c A D ((0 : P), y))
            = chartDiff c (A 0) (D 0) := rfl
        rw [heq]
        exact hf0
      exact hcontG.preimage_mem_nhds
        ((loopBox_isOpen_surjective_domRestrict (m := 4) i).mem_nhds hf0')
    have hEvCoord : ∀ᶠ q : P × Amb 4 in 𝓝 ((0 : P), y₀),
        ∀ j : Fin 5, j ≠ i → q.2 j ∈ Set.Ioo (0 : ℝ) 1 := by
      rw [Filter.eventually_all]
      intro j
      by_cases hj : j = i
      · rw [hj]
        exact Eventually.of_forall fun q h => absurd rfl h
      · filter_upwards [((isOpen_Ioo).preimage (by fun_prop : Continuous fun q : P × Amb 4 => q.2 j)).mem_nhds (hrest0 j hj)]
          with q hq
        exact fun _ => hq
    filter_upwards [clause1, hEvReg, hEvSurj, hEvFace, hEvCoord] with q hc1 hreg hsurj hface hcoord
    intro hmeet hbox
    refine ⟨hc1 hmeet hbox, fun hbd => ?_⟩
    have hqi : q.2 i = 0 ∨ q.2 i = 1 := by
      obtain ⟨-, k, hk⟩ := (unitBoxBdry_iff 4 q.2).mp hbd
      have hki : k = i := by
        by_contra hne
        have hk' := hcoord k hne
        rcases hk with hk | hk
        · rw [hk] at hk'
          exact absurd hk'.1 (lt_irrefl (0 : ℝ))
        · rw [hk] at hk'
          exact absurd hk'.2 (lt_irrefl (1 : ℝ))
      rwa [hki] at hk
    obtain ⟨σ, τ, hστ, hne⟩ := exists_sigma_tau_of_faceSurjective c (A q.1) (D q.1)
      (hA.comp (loopBox_contMDiff_const q.1)) (hD.comp (loopBox_contMDiff_const3 q.1))
      hreg hmeet hsurj hface
    exact ⟨i, hqi, hcoord, σ, τ, hστ, hne⟩
  · -- the base point is not on the boundary: the face clause is vacuous nearby
    have hEvNotBdry : ∀ᶠ q : P × Amb 4 in 𝓝 ((0 : P), y₀),
        ∀ k : Fin 5, q.2 k ≠ 0 ∧ q.2 k ≠ 1 := by
      rw [Filter.eventually_all]
      intro k
      have hk0 : y₀ k ≠ 0 := fun h => hybd ((unitBoxBdry_iff 4 y₀).mpr ⟨hy₀, ⟨k, Or.inl h⟩⟩)
      have hk1 : y₀ k ≠ 1 := fun h => hybd ((unitBoxBdry_iff 4 y₀).mpr ⟨hy₀, ⟨k, Or.inr h⟩⟩)
      have hc : Continuous fun q : P × Amb 4 => q.2 k := by fun_prop
      filter_upwards [((isOpen_ne (x := (0 : ℝ))).preimage hc).mem_nhds hk0,
        ((isOpen_ne (x := (1 : ℝ))).preimage hc).mem_nhds hk1] with q h1 h2
      exact ⟨h1, h2⟩
    filter_upwards [clause1, hEvNotBdry] with q hc1 hnb
    intro hmeet hbox
    refine ⟨hc1 hmeet hbox, fun hbq => ?_⟩
    exfalso
    obtain ⟨-, k, hk⟩ := (unitBoxBdry_iff 4 q.2).mp hbq
    rcases hk with hk | hk
    · exact (hnb k).1 hk
    · exact (hnb k).2 hk

/-! ## The target -/

theorem loopBoxData_eventually {P M : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (A : P → EuclideanSpace ℝ (Fin 2) → M) (D : P → EuclideanSpace ℝ (Fin 3) → M)
    (hA : ContMDiff (modelWithCornersSelf ℝ (P × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2))
    (hD : ContMDiff (modelWithCornersSelf ℝ (P × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 3) => D q.1 q.2))
    (h0 : Work.Drive.LoopBoxData (A 0) (D 0)) :
    Filter.Eventually (fun p : P => Work.Drive.LoopBoxData (A p) (D p)) (nhds (0 : P)) := by
  have hmeetcl : IsClosed
      {q : P × Amb 4 | A q.1 (sqPart q.2) = D q.1 (cbPart q.2)} :=
    isClosed_eq (contMDiff_loopBoxSqFam A hA).continuous
      (contMDiff_loopBoxCbFam D hD).continuous
  have hmain : ∀ᶠ p : P in 𝓝 (0 : P),
      ∀ y : Amb 4, A p (sqPart y) = D p (cbPart y) → loopBoxGood (A p) (D p) y :=
    eventually_forall_meet_of_eventually (P := P) (X := Amb 4)
      (fun p y => A p (sqPart y) = D p (cbPart y)) hmeetcl
      (Submission.Drive.unitBox 4) (isCompact_unitBox 4)
      (fun p y => loopBoxGood (A p) (D p) y)
      (fun p y hy => by
        by_contra hbox
        exact hy fun hbox' => absurd hbox' hbox)
      (fun y hy hyb => loopBoxGood_eventually_at_meet A D hA hD h0 hy hyb)
  filter_upwards [hmain] with p hp
  exact (loopBoxData_iff_five (A p) (D p)).mpr ((loopBoxData5_iff_forall_good (A p) (D p)).mpr hp)

end

end Work.Drive
