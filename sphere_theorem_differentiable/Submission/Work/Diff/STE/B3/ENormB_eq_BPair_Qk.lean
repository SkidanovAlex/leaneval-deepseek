import Mathlib
import Submission.Work.Diff.STE.B3.QkDef
import Submission.Work.Diff.STE.B3.BNorm_ENormB_equiv
import Submission.Work.Diff.STE.B3.pdVec_pair_eq_lambda
import Submission.Work.Diff.STE.B3.BPair_J_lin
import Submission.Work.Diff.STE.B3.integral_unitCube_eq_centreCube
import Submission.Work.Diff.STE.B3.mat_continuousOn_chi
import Submission.Work.Diff.STE.B3.contDiff_lamCoeff_seriesFun
import Submission.Work.Diff.STE.B3.BNorm_J_sub_le
import Submission.Work.Diff.STE.CSq_comp_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: the reduction `ENormB_pair k h h' = BPair (Qk D k h) h'`

`D.ENormB_pair k h h'` is the physical `Hᵏ` pairing of the periodised chart components
`D.Rper i h a b`, i.e. the sum over the `k`-fold multi-indices `l : Fin k → Fin n` of the `L²`
pairings of the iterated partial derivatives.  By the Parseval identity
`Work.Diff.STE.B3.pdVec_pair_eq_lambda` this is the *single* pairing against the `k`-th power of the
flat Laplacian `Λ` (the multiplier with symbol `λ(m) = Σ_j (2π m_j)²`), and the section `Qk D k h`
is precisely the reconstruction `Σ_i R_i^* (Λᵏ (R_i h))` of that multiplier.  The identity

`D.ENormB_pair k h h' = D.BPair (Qk D k h) h'`

is the content of this file.  The proof has three independent halves:

1. **The flat half** (`L2re_eq_integral_ccube`): for a continuous `A` whose *real part* is
   `1`-periodic, and a **real-valued** continuous `1`-periodic `Y` whose real part agrees with a
   function `rY` on the *open* centred cube,

     `L2re A Y = ∫_{(-1/2,1/2]^n} (A z).re * rY z dz`.

   The point is that `L2re` is an integral over the *positive* cube `(0,1]^n`, while the support of
   the localised components `R i h a b` lies in the open centred cube `(-1/2,1/2)^n`; the two cubes
   are both fundamental domains of the lattice `ℤ^n`
   (`Work.Diff.STE.B3.integral_unitCube_eq_centreCube`), and on the centred cube the periodisation
   `Rper` agrees with the component almost everywhere.

2. **The adjunction half** (`Work.Diff.STE.B3.BPair_J_lin`): `D.BPair` is additive in a finite sum of
   reconstructions `Σ_i R_i^* (u_i)`, and each summand is the component pairing
   `CPair_i (u_i) (R_i k)`.  Applied to `Qk D k h` this converts `D.BPair (Qk D k h) h'` into the
   sum `Σ_{i,a,b} ∫_{centreCube} u_i a b z * D.R i h' a b z`.

3. **The comparison**: the Parseval identity turns `D.ENormB_pair` into the sum of the pairings of
   part 1, and the two halves meet term by term.
-/

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE.B3

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## 1. Elementary facts about the flat torus -/

/-- A complex number fixed by conjugation is the coercion of its real part. -/
lemma ofReal_re_of_star_self' {w : ℂ} (hw : star w = w) : ((w.re : ℝ) : ℂ) = w := by
  have him : w.im = 0 := by
    have h := congrArg Complex.im hw
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  apply Complex.ext
  · simp
  · simp [him]

/-- The conjugate of a complex number fixed by conjugation is the coercion of its real part. -/
lemma star_eq_ofReal_re {w : ℂ} (hw : star w = w) : star w = ((w.re : ℝ) : ℂ) :=
  hw.trans (ofReal_re_of_star_self' hw).symm

/-- The real part of a `1`-periodic complex function is `1`-periodic. -/
lemma periodic1_of_re {ι : Type*} [Fintype ι] [DecidableEq ι] {F : (ι → ℝ) → ℂ}
    (h : Work.Diff.STE.Periodic1 F) :
    Work.Diff.STE.Periodic1 (fun z => (F z).re) := fun i x => by
  show (F (x + Pi.single i 1)).re = (F x).re
  rw [h i x]

/-- The pointwise product of two `1`-periodic real functions is `1`-periodic. -/
lemma periodic1_mul' {ι : Type*} [Fintype ι] [DecidableEq ι] {F G : (ι → ℝ) → ℝ}
    (hF : Work.Diff.STE.Periodic1 F) (hG : Work.Diff.STE.Periodic1 G) :
    Work.Diff.STE.Periodic1 (fun z => F z * G z) := fun i x => by
  show F (x + Pi.single i 1) * G (x + Pi.single i 1) = F x * G x
  rw [hF i x, hG i x]

/-- **The `1/2`-coordinate hyperplane is null.**  The boundary of the centred cube
`(-1/2, 1/2]^n` is contained in `{z | ∃ i, z i = 1/2}`, which is a finite union of coordinate
hyperplanes, hence null for the product of Lebesgue measures. -/
lemma volume_setOf_exists_coord_eq_half (n : ℕ) :
    (volume : Measure (Fin n → ℝ)) {z | ∃ i, z i = (1/2 : ℝ)} = 0 := by
  have hsingle : ∀ i : Fin n, (volume : Measure (Fin n → ℝ)) {z | z i = (1/2 : ℝ)} = 0 := by
    intro i
    rw [MeasureTheory.volume_pi]
    exact MeasureTheory.Measure.pi_hyperplane (fun _ : Fin n => (volume : Measure ℝ)) i (1/2)
  rw [show {z : Fin n → ℝ | ∃ i, z i = (1/2 : ℝ)}
      = ⋃ i, {z : Fin n → ℝ | z i = (1/2 : ℝ)} from by
    ext z
    simp]
  exact MeasureTheory.measure_iUnion_null hsingle

/-- The open centred cube `(-1/2, 1/2)^n`. -/
abbrev ocube (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1/2 : ℝ)) (1/2))

/-- The half-open centred cube `(-1/2, 1/2]^n` (the fundamental domain `B3Data.centreCube`). -/
abbrev ccube (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1/2 : ℝ)) (1/2))

lemma measurableSet_ocube (n : ℕ) : MeasurableSet (ocube n) :=
  MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)

lemma isCompact_Icc_cube (n : ℕ) (a b : ℝ) :
    IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc a b)) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

/-- A continuous function is integrable on any set contained in a closed cube. -/
lemma integrableOn_of_continuous_of_subset_Icc {n : ℕ} {γ : Type*} [NormedAddCommGroup γ]
    {F : (Fin n → ℝ) → γ} {s : Set (Fin n → ℝ)} {a b : ℝ}
    (hF : Continuous F) (hs : s ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Icc a b)) :
    IntegrableOn F s volume :=
  (hF.continuousOn.integrableOn_compact (isCompact_Icc_cube n a b)).mono_set hs

lemma integrableOn_unitCube_of_continuous {n : ℕ} {γ : Type*} [NormedAddCommGroup γ]
    {F : (Fin n → ℝ) → γ} (hF : Continuous F) :
    IntegrableOn F (Work.Diff.STE.unitCube (ι := Fin n)) volume :=
  integrableOn_of_continuous_of_subset_Icc hF (a := 0) (b := 1) (fun z hz => by
    rw [Work.Diff.STE.unitCube, Set.mem_pi] at hz
    rw [Set.mem_pi]
    intro i _
    exact ⟨le_of_lt (hz i (Set.mem_univ i)).1, (hz i (Set.mem_univ i)).2⟩)

lemma integrableOn_ccube_of_continuous {n : ℕ} {γ : Type*} [NormedAddCommGroup γ]
    {F : (Fin n → ℝ) → γ} (hF : Continuous F) :
    IntegrableOn F (ccube n) volume :=
  integrableOn_of_continuous_of_subset_Icc hF (a := -(1/2)) (b := 1/2) (fun z hz => by
    rw [ccube, Set.mem_pi] at hz
    rw [Set.mem_pi]
    intro i _
    exact ⟨le_of_lt (hz i (Set.mem_univ i)).1, (hz i (Set.mem_univ i)).2⟩)

/-- **The cube shift for real-valued functions**: the integral of a continuous `1`-periodic function
over the positive unit cube `(0,1]^n` equals its integral over the centred cube
`(-1/2,1/2]^n` (both are fundamental domains of the lattice `ℤ^n`). -/
lemma integral_unitCube_eq_ccube {n : ℕ} (G : (Fin n → ℝ) → ℝ)
    (hper : Work.Diff.STE.Periodic1 G) (hcont : Continuous G) :
    (∫ z in Work.Diff.STE.unitCube (ι := Fin n), G z) = ∫ z in ccube n, G z := by
  have hper' : Work.Diff.STE.Periodic1 (fun z => ((G z : ℝ) : ℂ)) := fun i x => by
    show ((G (x + Pi.single i 1) : ℝ) : ℂ) = ((G x : ℝ) : ℂ)
    rw [hper i x]
  have hcont' : Continuous (fun z => ((G z : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hcont
  have hmain := integral_unitCube_eq_centreCube (ι := Fin n)
    (F := fun z => ((G z : ℝ) : ℂ)) hper' hcont'
  have hU : (∫ z in Work.Diff.STE.unitCube (ι := Fin n), ((G z : ℝ) : ℂ)).re
      = ∫ z in Work.Diff.STE.unitCube (ι := Fin n), G z := by
    have hIntOn : IntegrableOn G (Work.Diff.STE.unitCube (ι := Fin n)) volume :=
      integrableOn_unitCube_of_continuous hcont
    have hInt : Integrable G (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
      hIntOn.integrable
    have h := Complex.ofRealCLM.integral_comp_comm (φ := G) hInt
    simpa using congrArg Complex.re h
  have hC : (∫ z in ccube n, ((G z : ℝ) : ℂ)).re = ∫ z in ccube n, G z := by
    have hIntOn : IntegrableOn G (ccube n) volume := integrableOn_ccube_of_continuous hcont
    have hInt : Integrable G (volume.restrict (ccube n)) := hIntOn.integrable
    have h := Complex.ofRealCLM.integral_comp_comm (φ := G) hInt
    simpa using congrArg Complex.re h
  have h := congrArg Complex.re hmain
  rw [hU, hC] at h
  simpa [ccube] using h

/-- The boundary of the centred cube is null, in the form used below: the centred cube and the open
centred cube differ by a null set. -/
lemma ae_mem_ocube {n : ℕ} :
    ∀ᵐ z ∂(volume.restrict (ccube n)), z ∈ ocube n := by
  rw [MeasureTheory.ae_iff]
  have hcomp : {z : Fin n → ℝ | ¬ z ∈ ocube n} = (ocube n)ᶜ := rfl
  rw [hcomp]
  rw [MeasureTheory.Measure.restrict_apply (measurableSet_ocube n).compl]
  refine MeasureTheory.measure_mono_null ?_ (volume_setOf_exists_coord_eq_half n)
  intro z hz
  obtain ⟨hznot, hzc⟩ := hz
  rw [Set.mem_compl_iff, ocube, Set.mem_pi] at hznot
  push Not at hznot
  obtain ⟨i, -, hi⟩ := hznot
  refine ⟨i, ?_⟩
  rw [ccube, Set.mem_pi] at hzc
  have h1 : z i ∈ Set.Ioc (-(1/2 : ℝ)) (1/2) := hzc i (Set.mem_univ i)
  have h2 : ¬ (z i < (1/2 : ℝ)) := fun hlt => hi ⟨h1.1, hlt⟩
  exact le_antisymm h1.2 (not_lt.mp h2)

/-! ## 2. The flat half: `L2re` against the centred cube -/

/-- **The bridge between the two pairings.**  For a continuous `A` whose real part is
`1`-periodic, a continuous `1`-periodic **real-valued** `Y` and a function `rY` agreeing with the
real part of `Y` on the open centred cube, the `L²` pairing over the positive unit cube is the
integral over the centred cube of `(A z).re * rY z`. -/
theorem L2re_eq_integral_ccube {n : ℕ}
    (A Y : (Fin n → ℝ) → ℂ) (rY : (Fin n → ℝ) → ℝ)
    (hAc : Continuous A) (hAper : Work.Diff.STE.Periodic1 (fun z => (A z).re))
    (hYc : Continuous Y) (hYper : Work.Diff.STE.Periodic1 Y)
    (hYreal : ∀ z, star (Y z) = Y z)
    (hYeq : ∀ z, z ∈ ocube n → Y z = ((rY z : ℝ) : ℂ)) :
    Work.Diff.STE.L2re A Y = ∫ z in ccube n, (A z).re * rY z := by
  have hstep1 : Work.Diff.STE.L2re A Y
      = ∫ z in Work.Diff.STE.unitCube (ι := Fin n), (A z).re * (Y z).re := by
    rw [Work.Diff.STE.L2re]
    change Complex.reCLM (∫ z in Work.Diff.STE.unitCube (ι := Fin n), A z * star (Y z))
      = ∫ z in Work.Diff.STE.unitCube (ι := Fin n), (A z).re * (Y z).re
    have hcont : Continuous (fun z => A z * star (Y z)) :=
      hAc.mul (Complex.continuous_conj.comp hYc)
    have hInt : Integrable (fun z => A z * star (Y z))
        (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
      (integrableOn_unitCube_of_continuous (F := fun z => A z * star (Y z)) hcont).integrable
    rw [← Complex.reCLM.integral_comp_comm hInt]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show (A z * star (Y z)).re = (A z).re * (Y z).re
    rw [star_eq_ofReal_re (hYreal z), Complex.re_mul_ofReal]
  have hstep2 : (∫ z in Work.Diff.STE.unitCube (ι := Fin n), (A z).re * (Y z).re)
      = ∫ z in ccube n, (A z).re * (Y z).re :=
    integral_unitCube_eq_ccube (fun z => (A z).re * (Y z).re)
      (periodic1_mul' hAper (periodic1_of_re hYper))
      ((Complex.continuous_re.comp hAc).mul (Complex.continuous_re.comp hYc))
  have hstep3 : (∫ z in ccube n, (A z).re * (Y z).re) = ∫ z in ccube n, (A z).re * rY z := by
    refine MeasureTheory.integral_congr_ae ?_
    refine ae_mem_ocube.mono fun z hz => ?_
    show (A z).re * (Y z).re = (A z).re * rY z
    rw [hYeq z hz, Complex.ofReal_re]
  rw [hstep1, hstep2, hstep3]

/-! ## 3. The coefficient family of `Λᵏ` and the section `Qk` -/

/-- The coefficient family of the `k`-th power of the flat Laplacian applied to the periodised
component `D.Rper i h a b`: `m ↦ λ(m)^k · ĉ(m)`. -/
noncomputable def lamCoeff (D : B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (h : Bil (I := I) (M := M)) (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    (Fin (Module.finrank ℝ E) → ℤ) → ℂ :=
  fun m => ((lamSym (E := E) m ^ k : ℝ) : ℂ) *
    Work.Diff.STE.fourierCoeff (D.Rper i h a b) m

/-- The component family of the section `Λᵏ (R_i h)`, i.e. the real part of the Fourier series with
coefficient family `lamCoeff`. -/
noncomputable def lamSection (D : B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (h : Bil (I := I) (M := M)) (i : ι₀) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
  fun a b z => (Work.Diff.STE.seriesFun (lamCoeff D k h i a b) z).re

/-- `Qk D k h` is the reconstruction of the component family `lamSection D k h`. -/
lemma Qk_eq_sum_Rstar (D : B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (h : Bil (I := I) (M := M)) :
    Qk D k h = ∑ i : ι₀, D.Rstar i (lamSection D k h i) := by
  unfold Qk lamSection lamCoeff
  rfl

/-- The Parseval half: `ENormB_pair` is the pairing against `Λᵏ`. -/
lemma ENormB_pair_eq_lambda (D : B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (h h' : Bil (I := I) (M := M))
    (hsm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b))
    (hsm' : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.R i h' a b)) :
    D.ENormB_pair k h h'
      = ∑ i, ∑ a, ∑ b, Work.Diff.STE.L2re
          (fun z => Work.Diff.STE.seriesFun (lamCoeff D k h i a b) z) (D.Rper i h' a b) := by
  rw [B3Data.ENormB_pair]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  obtain ⟨hd, hp⟩ := Rper_contDiff_periodic_of_R_contDiff D i h a b (hsm i a b)
  obtain ⟨hd', hp'⟩ := Rper_contDiff_periodic_of_R_contDiff D i h' a b (hsm' i a b)
  rw [pdVec_pair_eq_lambda k (D.Rper i h a b) (D.Rper i h' a b) hd hd' hp hp']
  congr 1

/-- The periodised component is real-valued (it is a lattice sum of complexified real numbers). -/
lemma Rper_star_self' (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (h : Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E))
    (z : Fin (Module.finrank ℝ E) → ℝ) :
    star (D.Rper i h a b z) = D.Rper i h a b z := by
  have hrepr : D.Rper i h a b z
      = ((∑' m : Fin (Module.finrank ℝ E) → ℤ,
          D.R i h a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ) := by
    show (∑' m : Fin (Module.finrank ℝ E) → ℤ,
      ((D.R i h a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ)) = _
    rw [Complex.ofReal_tsum]
  rw [hrepr]
  exact Complex.conj_ofReal _

/-! ## 4. The target -/

theorem ENormB_eq_BPair_Qk
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (h h' : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i h a b))
    (hh' : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i h' a b)) :
    D.ENormB_pair k h h' = D.BPair (Work.Diff.STE.B3.Qk D k h) h' := by
  classical
  -- the continuity of the component family of `Qk`
  have hu : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Continuous (lamSection D k h i a b) := fun i a b =>
    show Continuous (fun z => (Work.Diff.STE.seriesFun (lamCoeff D k h i a b) z).re) from
      Complex.continuous_re.comp
        (contDiff_lamCoeff_seriesFun (I := I) (M := M) D k h i a b (hh i a b)).continuous
  -- the continuity of the chart matrix of `h'` on the support of the cut-offs
  have hk : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContinuousOn (D.mat j h' a b) {z : Fin (Module.finrank ℝ E) → ℝ | D.χ j z ≠ 0} :=
    fun j a b => mat_continuousOn_chi (I := I) (M := M) D h' hh' j a b
  -- (1) the left-hand side is the pairing against `Λᵏ`
  have hL := ENormB_pair_eq_lambda (I := I) (M := M) D k h h'
    (fun i a b => hh i a b) (fun i a b => hh' i a b)
  -- (2) the right-hand side is the sum of the component pairings of `Λᵏ (R_i h)`
  have hR : D.BPair (Qk D k h) h'
      = ∑ i, ∑ a, ∑ b, ∫ z in B3Data.centreCube (E := E),
          (Work.Diff.STE.seriesFun (lamCoeff D k h i a b) z).re * D.R i h' a b z := by
    rw [Qk_eq_sum_Rstar D k h]
    rw [BPair_J_lin (I := I) (M := M) D h' (fun i => lamSection D k h i) hu hk]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [B3Data.CPair]
    rfl
  -- (3) the two halves agree component by component
  have hbridge : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.L2re (fun z => Work.Diff.STE.seriesFun (lamCoeff D k h i a b) z)
          (D.Rper i h' a b)
        = ∫ z in B3Data.centreCube (E := E),
            (Work.Diff.STE.seriesFun (lamCoeff D k h i a b) z).re * D.R i h' a b z := by
    intro i a b
    obtain ⟨hdY, hpY⟩ := Rper_contDiff_periodic_of_R_contDiff D i h' a b (hh' i a b)
    have hAc : Continuous (fun z => Work.Diff.STE.seriesFun (lamCoeff D k h i a b) z) :=
      (contDiff_lamCoeff_seriesFun (I := I) (M := M) D k h i a b (hh i a b)).continuous
    have hAper : Work.Diff.STE.Periodic1
        (fun z => (Work.Diff.STE.seriesFun (lamCoeff D k h i a b) z).re) :=
      periodic1_of_re (periodic_seriesFun (lamCoeff D k h i a b))
    have hYreal : ∀ z, star (D.Rper i h' a b z) = D.Rper i h' a b z :=
      fun z => Rper_star_self' D i h' a b z
    have hYeq : ∀ z, z ∈ ocube (Module.finrank ℝ E) →
        D.Rper i h' a b z = ((D.R i h' a b z : ℝ) : ℂ) := by
      intro z hz
      exact Rper_eq_of_mem_cube D h' i a b
        (fun k => (Set.mem_pi.mp hz) k (Set.mem_univ k))
    have hmain := L2re_eq_integral_ccube
      (A := fun z => Work.Diff.STE.seriesFun (lamCoeff D k h i a b) z)
      (Y := D.Rper i h' a b) (rY := D.R i h' a b) hAc hAper hdY.continuous hpY hYreal hYeq
    simpa only [ccube, B3Data.centreCube] using hmain
  rw [hL, hR]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => hbridge i a b

end Work.Diff.STE.B3
