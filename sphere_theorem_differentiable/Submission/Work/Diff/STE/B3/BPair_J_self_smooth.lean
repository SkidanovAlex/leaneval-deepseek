import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.BPair_J_self
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.B3.STruncC_contDiff_periodic
import Submission.Work.Diff.STE.B3.STruncR_CSq_le
import Submission.Work.Diff.STE.B3.integrableOn_Npair_term
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.integral_seriesFun_mul_conj
import Submission.Work.Diff.STE.B3.contDiff_integrableOn_Rpair
import Submission.Work.Diff.STE.B3.contDiff_integrableOn_Cpair
import Submission.Work.Diff.STE.B3.contDiff_phi_pt_continuous
import Submission.Work.Diff.STE.B3.periodicIntegralLeCube

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: the Friedrichs mollifier `J ρ ε` is self-adjoint for the composite pairing
(smooth version, no compactly supported multiplier)

The proved sibling `Work.Diff.STE.B3.BPair_J_self` establishes
`D.BPair (D.J ρ ε h) k = D.BPair h (D.J ρ ε k)` under the hypothesis that the Fourier multiplier
`ρ` is supported in a ball of radius `√2` (so that all Fourier series are finite sums) and that the
chart matrices of `h, k` are continuous on `{χ j ≠ 0}`.

This file proves the same identity under *smoothness* of the localised components
`D.R j h a b`, `D.R j k a b` and only the bound `‖ρ‖ ≤ 1` on the multiplier.  The point is that a
smooth cube-supported component has rapidly decaying Fourier coefficients, so the truncated series
converge absolutely and the self-adjointness argument goes through by Parseval instead of by a
finite sum.
-/

noncomputable section

open MeasureTheory BigOperators
open scoped ComplexConjugate

namespace Work.Diff.STE.B3

/-! ## The periodisation of a real cube-supported function -/

/-- The periodisation `∑' m, f (· + m)` of a real function, lifted to `ℂ`.  This is the function
whose Fourier coefficients are `Work.Diff.STE.B3.perCoeff f`. -/
def perF {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) : (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
  fun y => ∑' m : Fin (Module.finrank ℝ E) → ℤ,
    ((f (y + Work.Diff.STE.iVec m) : ℝ) : ℂ)

@[simp] lemma perF_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (y : Fin (Module.finrank ℝ E) → ℝ) :
    perF f y = ∑' m : Fin (Module.finrank ℝ E) → ℤ,
      ((f (y + Work.Diff.STE.iVec m) : ℝ) : ℂ) := rfl

lemma perCoeff_eq_fourierCoeff_perF {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) :
    B3.perCoeff f = Work.Diff.STE.fourierCoeff (perF f) := rfl

/-- The support of the complex lift of a real function is contained in the support. -/
lemma support_ofReal_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ}
    {s : Set (Fin (Module.finrank ℝ E) → ℝ)} (hs : Function.support f ⊆ s) :
    Function.support (fun y : Fin (Module.finrank ℝ E) → ℝ => ((f y : ℝ) : ℂ)) ⊆ s := by
  intro y hy
  refine hs ?_
  rw [Function.mem_support] at hy ⊢
  intro h0
  exact hy (by rw [h0, Complex.ofReal_zero])

/-- The periodisation of a smooth cube-supported function is smooth. -/
lemma perF_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfs : Function.support f ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2))) :
    ContDiff ℝ (⊤ : ℕ∞) (perF f) :=
  (Work.Diff.STE.periodization_contDiff_periodic (fun z => ((f z : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp hf) (support_ofReal_subset hfs)).1

/-- The periodisation of any function is `1`-periodic. -/
lemma perF_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) :
    Work.Diff.STE.Periodic1 (perF f) :=
  Work.Diff.STE.periodization_periodic (fun z => ((f z : ℝ) : ℂ))

/-- On the open cube the periodisation is the function itself. -/
lemma perF_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfs : Function.support f ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2))) :
    ∀ x : Fin (Module.finrank ℝ E) → ℝ,
      (∀ i, x i ∈ Set.Ioo (-(1/2:ℝ)) (1/2)) → perF f x = ((f x : ℝ) : ℂ) :=
  (Work.Diff.STE.periodization_contDiff_periodic (fun z => ((f z : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp hf) (support_ofReal_subset hfs)).2.2

/-- **Summability of the Fourier coefficients of the periodisation of a smooth cube-supported
function.** -/
lemma perF_summable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfs : Function.support f ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2))) :
    Summable (fun m : Fin (Module.finrank ℝ E) → ℤ =>
      ‖Work.Diff.STE.fourierCoeff (perF f) m‖) := by
  have hsum := Work.Diff.STE.summable_wt_pow_norm_fourierCoeff_of_contDiff (perF f)
    (perF_contDiff f hf hfs) (perF_periodic f) 0
  simpa only [pow_zero, one_mul] using hsum

/-- **The periodisation of a real cube-supported function is real-valued**, i.e. equal to its
complex conjugate. -/
lemma perF_star_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (g : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgs : Function.support g ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2))) :
    ∀ z : Fin (Module.finrank ℝ E) → ℝ, star (perF g z) = perF g z := by
  intro z
  have hsm := perF_contDiff g hg hgs
  have hper := perF_periodic g
  have hsum := perF_summable g hg hgs
  have hser : perF g
      = Work.Diff.STE.seriesFun (Work.Diff.STE.fourierCoeff (perF g)) :=
    funext fun y => (Work.Diff.STE.flat.seriesFun_fourierCoeff (perF g) hsm hper y).symm
  have hz : perF g z = Work.Diff.STE.seriesFun (Work.Diff.STE.fourierCoeff (perF g)) z :=
    congrFun hser z
  rw [hz, star_seriesFun _ hsum z]
  refine congrArg (fun D => Work.Diff.STE.seriesFun D z) ?_
  funext m
  have h4 := star_fourierCoeff_per g (-m)
  have h2 : star (Work.Diff.STE.fourierCoeff (perF g) (-m))
      = Work.Diff.STE.fourierCoeff (perF g) m := by
    have h5 : star (Work.Diff.STE.fourierCoeff (perF g) (-m))
        = Work.Diff.STE.fourierCoeff (perF g) (-(-m)) := h4
    simpa using h5
  simpa using h2

/-! ## Elementary facts about the cubes -/

/-- The open cube `(-1/2,1/2)^n` is a measurable set. -/
lemma measurableSet_openCube {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    MeasurableSet (Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2))) :=
  (measurableSet_pi Set.countable_univ).mpr (Or.inl (fun _ _ => measurableSet_Ioo))

/-- The unit cube `(0,1]^n` is a measurable set. -/
lemma measurableSet_unitCube' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    MeasurableSet (Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E))) :=
  (measurableSet_pi Set.countable_univ).mpr (Or.inl (fun _ _ => measurableSet_Ioc))

/-- The open cube is contained in the half-open cube of the same radius. -/
lemma openCube_subset_centreCube {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2))
      ⊆ B3Data.centreCube (E := E) := by
  intro z hz i _
  exact ⟨(Set.mem_Ioo.mp (Set.mem_pi.mp hz i (Set.mem_univ i))).1,
    le_of_lt (Set.mem_Ioo.mp (Set.mem_pi.mp hz i (Set.mem_univ i))).2⟩

/-- **The open cube and the half-open cube of the same side have the same measure.**  They are
`∏ᵢ (-1/2,1/2)` and `∏ᵢ (-1/2,1/2]`, which differ by the coordinate hyperplanes, a null set. -/
theorem setIntegral_openCube_eq_centreCube {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) :
    (∫ z in Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)), F z)
      = ∫ z in B3Data.centreCube (E := E), F z := by
  rw [MeasureTheory.volume_pi]
  exact MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Measure.pi_Ioo_ae_eq_pi_Ioc (s := Set.univ)
      (f := fun _ : Fin (Module.finrank ℝ E) => (-(1/2:ℝ)))
      (g := fun _ : Fin (Module.finrank ℝ E) => (1/2:ℝ)))

/-- An integral over the centred cube of a product which vanishes off the open cube equals the
integral over the open cube. -/
lemma setIntegral_centreCube_eq_openCube_of_forall_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (F G : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (h : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      z ∉ Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)) →
        F z * G z = 0) :
    (∫ z in B3Data.centreCube (E := E), F z * G z)
      = ∫ z in Set.pi Set.univ
          (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)), F z * G z :=
  MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (measurableSet_centreCube (E := E)) openCube_subset_centreCube (fun z hz => h z hz.2)

/-- If `w` is real (i.e. `star w = w`) then it is the coercion of its real part. -/
lemma ofReal_re_of_star_eq (w : ℂ) (h : star w = w) : ((w.re : ℝ) : ℂ) = w := by
  rw [ofReal_re_eq w, h]
  ring

/-- **Truncating a summable coefficient family keeps it summable.** -/
lemma summable_trunc_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1) (ε : ℝ)
    (c : (Fin (Module.finrank ℝ E) → ℤ) → ℂ) (hc : Summable (fun m => ‖c m‖)) :
    Summable (fun m => ‖trunc ρ ε c m‖) := by
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hc
  rw [trunc, norm_mul]
  have h2 : ‖((ρ (ε • fun i => (m i : ℝ))) : ℂ)‖ ≤ 1 := by
    simpa using hρ (ε • fun i => (m i : ℝ))
  calc ‖((ρ (ε • fun i => (m i : ℝ))) : ℂ)‖ * ‖c m‖ ≤ 1 * ‖c m‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = ‖c m‖ := one_mul _

/-- **Parseval for the Friedrichs truncation against a periodisation.**  For a summable coefficient
family `c` and a smooth cube-supported real function `g`,

  `∫_{unitCube} (seriesFun c).re · (perF g).re = (Σ_m c m · conj (ĝ m)).re`,

where `ĝ` are the Fourier coefficients of the periodisation of `g`. -/
theorem integral_seriesFun_re_mul_perF {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (g : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgs : Function.support g ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)))
    (c : (Fin (Module.finrank ℝ E) → ℤ) → ℂ) (hc : Summable (fun m => ‖c m‖)) :
    (∫ z in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
        (Work.Diff.STE.seriesFun c z).re * (perF g z).re)
      = (∑' m, c m * star (Work.Diff.STE.fourierCoeff (perF g) m)).re := by
  have hgsm := perF_contDiff g hg hgs
  have hgper := perF_periodic g
  have hgsum := perF_summable g hg hgs
  have hgreal := perF_star_eq g hg hgs
  have hser : ∀ z, perF g z
      = Work.Diff.STE.seriesFun (Work.Diff.STE.fourierCoeff (perF g)) z :=
    fun z => (Work.Diff.STE.flat.seriesFun_fourierCoeff (perF g) hgsm hgper z).symm
  have hcont : Continuous (fun z => Work.Diff.STE.seriesFun c z * star (perF g z)) :=
    (Work.Diff.STE.flat.continuous_seriesFun_of_summable c hc).mul
      (continuous_star.comp hgsm.continuous)
  have hint : IntegrableOn (fun z => Work.Diff.STE.seriesFun c z * star (perF g z))
      (Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E))) := by
    have hcompact : IsCompact (Set.pi Set.univ
        (fun _ : Fin (Module.finrank ℝ E) => Set.Icc (0:ℝ) 1)) := by
      rw [Set.pi_univ_Icc]
      exact isCompact_Icc
    refine (hcont.continuousOn.integrableOn_compact hcompact).mono_set ?_
    intro z hz i _
    exact ⟨le_of_lt (Set.mem_Ioc.mp (Set.mem_pi.mp hz i (Set.mem_univ i))).1,
      (Set.mem_Ioc.mp (Set.mem_pi.mp hz i (Set.mem_univ i))).2⟩
  calc (∫ z in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
        (Work.Diff.STE.seriesFun c z).re * (perF g z).re)
      = ∫ z in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
          (Work.Diff.STE.seriesFun c z * star (perF g z)).re := by
        refine setIntegral_congr_fun (measurableSet_unitCube' (E := E)) (fun z _ => ?_)
        have hB : ((perF g z).re : ℂ) = perF g z := ofReal_re_of_star_eq _ (hgreal z)
        have key : (Work.Diff.STE.seriesFun c z * star (perF g z)).re
            = (Work.Diff.STE.seriesFun c z).re * (perF g z).re := by
          rw [hgreal z, ← hB, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
            sub_zero]
        exact key.symm
    _ = (∫ z in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
          Work.Diff.STE.seriesFun c z * star (perF g z)).re := integral_re hint
    _ = (∑' m, c m * star (Work.Diff.STE.fourierCoeff (perF g) m)).re := by
        rw [show (∫ z in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
              Work.Diff.STE.seriesFun c z * star (perF g z))
            = ∫ z in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
              Work.Diff.STE.seriesFun c z
                * star (Work.Diff.STE.seriesFun
                    (Work.Diff.STE.fourierCoeff (perF g)) z) from
          setIntegral_congr_fun (measurableSet_unitCube' (E := E)) (fun z _ => by rw [hser z])]
        exact congrArg Complex.re
          (Work.Diff.STE.integral_seriesFun_mul_conj c _ hc hgsum)

/-! ## The self-adjointness of the Friedrichs truncation for smooth cube-supported functions -/

/-! ## The fundamental-domain identity for the unit cube

The integrals of a `1`-periodic function over `(0,1]^ι` and over `(-1/2,1/2]^ι` agree.  Each of the
two cubes is cut into its `2^(card ι)` half-open sub-boxes (at `1/2`, resp. at `0`); the `s`-th
sub-box of the centred cube is the translate of the `s`-th sub-box of the unit cube by the integer
vector `hshift s`, so the two integrals agree term by term by translation invariance and
periodicity. -/

section FundamentalDomain

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `s`-th half-open sub-box of the unit cube `(0,1]^ι` (cut at `1/2`). -/
private def hboxU (s : ι → Fin 2) : Set (ι → ℝ) :=
  Set.pi Set.univ fun i => if s i = 0 then Set.Ioc (0:ℝ) (1/2) else Set.Ioc (1/2:ℝ) 1

/-- The `s`-th half-open sub-box of the centred cube `(-1/2,1/2]^ι` (cut at `0`). -/
private def hboxC (s : ι → Fin 2) : Set (ι → ℝ) :=
  Set.pi Set.univ fun i => if s i = 0 then Set.Ioc (0:ℝ) (1/2) else Set.Ioc (-(1/2):ℝ) 0

/-- The integer vector carrying the `s`-th centred sub-box onto the `s`-th sub-box of the unit
cube. -/
private def hshift (s : ι → Fin 2) : ι → ℤ := fun i => if s i = 0 then 0 else 1

/-- The same vector, seen in `ι → ℝ`. -/
private def hshiftR (s : ι → Fin 2) : ι → ℝ := fun i => if s i = 0 then 0 else 1

private lemma iVec_hshift (s : ι → Fin 2) :
    Work.Diff.STE.iVec (hshift s) = hshiftR s := by
  funext i
  by_cases h : s i = 0 <;> simp [Work.Diff.STE.iVec_apply, hshift, hshiftR, h]

private lemma measurableSet_hboxU (s : ι → Fin 2) : MeasurableSet (hboxU s) := by
  refine (measurableSet_pi Set.countable_univ).mpr (Or.inl fun i _ => ?_)
  show MeasurableSet (if s i = 0 then Set.Ioc (0:ℝ) (1/2) else Set.Ioc (1/2:ℝ) 1)
  by_cases h : s i = 0 <;> simp [h]

private lemma measurableSet_hboxC (s : ι → Fin 2) : MeasurableSet (hboxC s) := by
  refine (measurableSet_pi Set.countable_univ).mpr (Or.inl fun i _ => ?_)
  show MeasurableSet (if s i = 0 then Set.Ioc (0:ℝ) (1/2) else Set.Ioc (-(1/2):ℝ) 0)
  by_cases h : s i = 0 <;> simp [h]

private lemma iUnion_hboxU :
    Set.iUnion (fun s : ι → Fin 2 => hboxU s) = Work.Diff.STE.unitCube (ι := ι) := by
  ext x
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨s, hs⟩ i _
    have h := hs i (Set.mem_univ i)
    by_cases hc : s i = 0
    · have h' : x i ∈ Set.Ioc (0:ℝ) (1/2) := by simpa [hc] using h
      exact ⟨h'.1, by linarith [h'.2]⟩
    · have h' : x i ∈ Set.Ioc (1/2:ℝ) 1 := by simpa [hc] using h
      exact ⟨by linarith [h'.1], h'.2⟩
  · intro hx
    refine ⟨fun i => if x i ≤ (1/2:ℝ) then 0 else 1, ?_⟩
    show ∀ i ∈ Set.univ, x i ∈ (if (if x i ≤ (1/2:ℝ) then (0 : Fin 2) else 1) = 0
      then Set.Ioc (0:ℝ) (1/2) else Set.Ioc (1/2:ℝ) 1)
    intro i _
    have hi : x i ∈ Set.Ioc (0:ℝ) 1 := hx i (Set.mem_univ i)
    rw [Set.mem_Ioc] at hi
    by_cases hc : x i ≤ (1/2:ℝ)
    · rw [if_pos hc, if_pos rfl]
      exact ⟨hi.1, hc⟩
    · rw [if_neg hc, if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
      exact ⟨lt_of_not_ge hc, hi.2⟩

private lemma iUnion_hboxC :
    Set.iUnion (fun s : ι → Fin 2 => hboxC s)
      = Set.pi Set.univ (fun _ : ι => Set.Ioc (-(1/2:ℝ)) (1/2)) := by
  ext x
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨s, hs⟩ i _
    have h := hs i (Set.mem_univ i)
    by_cases hc : s i = 0
    · have h' : x i ∈ Set.Ioc (0:ℝ) (1/2) := by simpa [hc] using h
      exact ⟨by linarith [h'.1], h'.2⟩
    · have h' : x i ∈ Set.Ioc (-(1/2):ℝ) 0 := by simpa [hc] using h
      exact ⟨h'.1, by linarith [h'.2]⟩
  · intro hx
    refine ⟨fun i => if (0:ℝ) < x i then 0 else 1, ?_⟩
    show ∀ i ∈ Set.univ, x i ∈ (if (if (0:ℝ) < x i then (0 : Fin 2) else 1) = 0
      then Set.Ioc (0:ℝ) (1/2) else Set.Ioc (-(1/2):ℝ) 0)
    intro i _
    have hi : x i ∈ Set.Ioc (-(1/2):ℝ) (1/2) := hx i (Set.mem_univ i)
    rw [Set.mem_Ioc] at hi
    by_cases hc : (0:ℝ) < x i
    · rw [if_pos hc, if_pos rfl]
      exact ⟨hc, hi.2⟩
    · rw [if_neg hc, if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
      exact ⟨hi.1, le_of_not_gt hc⟩

private lemma pairwiseDisjoint_hboxU :
    Pairwise (Function.onFun Disjoint (hboxU (ι := ι))) := by
  intro s t hst
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hy
  obtain ⟨i, hi⟩ : ∃ i, s i ≠ t i := by
    by_contra h
    push_neg at h
    exact hst (funext h)
  have hx' := hx i (Set.mem_univ i)
  have hy' := hy i (Set.mem_univ i)
  by_cases hs : s i = 0
  · have ht : t i ≠ 0 := fun h => hi (hs.trans h.symm)
    have hx'' : x i ∈ Set.Ioc (0:ℝ) (1/2) := by simpa [hs] using hx'
    have hy'' : x i ∈ Set.Ioc (1/2:ℝ) 1 := by simpa [ht] using hy'
    exact absurd hx''.2 (not_le.mpr (Set.mem_Ioc.mp hy'').1)
  · have ht : t i = 0 := by
      by_contra ht
      exact hi ((Fin.eq_one_of_ne_zero (s i) hs).trans
        (Fin.eq_one_of_ne_zero (t i) ht).symm)
    have hx'' : x i ∈ Set.Ioc (1/2:ℝ) 1 := by simpa [hs] using hx'
    have hy'' : x i ∈ Set.Ioc (0:ℝ) (1/2) := by simpa [ht] using hy'
    exact absurd hy''.2 (not_le.mpr (Set.mem_Ioc.mp hx'').1)

private lemma pairwiseDisjoint_hboxC :
    Pairwise (Function.onFun Disjoint (hboxC (ι := ι))) := by
  intro s t hst
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hy
  obtain ⟨i, hi⟩ : ∃ i, s i ≠ t i := by
    by_contra h
    push_neg at h
    exact hst (funext h)
  have hx' := hx i (Set.mem_univ i)
  have hy' := hy i (Set.mem_univ i)
  by_cases hs : s i = 0
  · have ht : t i ≠ 0 := fun h => hi (hs.trans h.symm)
    have hx'' : x i ∈ Set.Ioc (0:ℝ) (1/2) := by simpa [hs] using hx'
    have hy'' : x i ∈ Set.Ioc (-(1/2):ℝ) 0 := by simpa [ht] using hy'
    exact absurd (Set.mem_Ioc.mp hy'').2 (not_le.mpr hx''.1)
  · have ht : t i = 0 := by
      by_contra ht
      exact hi ((Fin.eq_one_of_ne_zero (s i) hs).trans
        (Fin.eq_one_of_ne_zero (t i) ht).symm)
    have hx'' : x i ∈ Set.Ioc (-(1/2):ℝ) 0 := by simpa [hs] using hx'
    have hy'' : x i ∈ Set.Ioc (0:ℝ) (1/2) := by simpa [ht] using hy'
    exact absurd (Set.mem_Ioc.mp hx'').2 (not_le.mpr hy''.1)

/-- Shift of a set integral by a constant vector (real-valued version). -/
private lemma setIntegral_comp_add_real (c : ι → ℝ) (s : Set (ι → ℝ))
    (G : (ι → ℝ) → ℝ) :
    ∫ y in s, G (y + c) = ∫ z in (fun y : ι → ℝ => y + c) '' s, G z := by
  have : (MeasureSpace.volume : Measure (ι → ℝ)).IsAddHaarMeasure :=
    isAddHaarMeasure_volume_pi ι
  exact ((measurePreserving_add_right (MeasureSpace.volume : Measure (ι → ℝ)) c).setIntegral_image_emb
    (MeasurableEquiv.addRight c).measurableEmbedding G s).symm

/-- The `s`-th box of the unit cube is the translate by the integer vector `hshift s` of the `s`-th
box of the centred cube. -/
private lemma image_hboxC_eq_hboxU (s : ι → Fin 2) :
    (fun y : ι → ℝ => y + hshiftR s) '' (hboxC s) = hboxU s := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩ i _
    have hyi := hy i (Set.mem_univ i)
    show y i + hshiftR s i ∈ (if s i = 0 then Set.Ioc (0:ℝ) (1/2) else Set.Ioc (1/2:ℝ) 1)
    by_cases hs : s i = 0
    · have hy' : y i ∈ Set.Ioc (0:ℝ) (1/2) := by simpa [hs] using hyi
      have hz : y i + hshiftR s i = y i := by simp [hshiftR, hs]
      rw [hz, if_pos hs]
      exact hy'
    · have hy' : y i ∈ Set.Ioc (-(1/2):ℝ) 0 := by simpa [hs] using hyi
      have hz : y i + hshiftR s i = y i + 1 := by simp [hshiftR, hs]
      rw [hz, if_neg hs]
      exact ⟨by linarith [hy'.1], by linarith [hy'.2]⟩
  · intro hz
    refine ⟨z - hshiftR s, ?_, ?_⟩
    · show ∀ i ∈ Set.univ, z i - hshiftR s i
        ∈ (if s i = 0 then Set.Ioc (0:ℝ) (1/2) else Set.Ioc (-(1/2):ℝ) 0)
      intro i _
      have hzi := hz i (Set.mem_univ i)
      by_cases hs : s i = 0
      · have hz' : z i ∈ Set.Ioc (0:ℝ) (1/2) := by simpa [hs] using hzi
        have hz2 : z i - hshiftR s i = z i := by simp [hshiftR, hs]
        rw [hz2, if_pos hs]
        exact hz'
      · have hz' : z i ∈ Set.Ioc (1/2:ℝ) 1 := by simpa [hs] using hzi
        have hz2 : z i - hshiftR s i = z i - 1 := by simp [hshiftR, hs]
        rw [hz2, if_neg hs]
        exact ⟨by linarith [hz'.1], by linarith [hz'.2]⟩
    · funext i
      simp only [Pi.sub_apply, Pi.add_apply]
      ring

/-- The integral of a periodic function over the `s`-th box of the unit cube equals the integral
over the `s`-th box of the centred cube. -/
private lemma setIntegral_hboxU_eq_hboxC (F : (ι → ℝ) → ℝ) (hper : Work.Diff.STE.Periodic1 F)
    (s : ι → Fin 2) :
    ∫ x in hboxU s, F x = ∫ x in hboxC s, F x := by
  calc ∫ x in hboxU s, F x
      = ∫ x in (fun y : ι → ℝ => y + hshiftR s) '' (hboxC s), F x := by
        rw [image_hboxC_eq_hboxU s]
    _ = ∫ y in hboxC s, F (y + hshiftR s) := (setIntegral_comp_add_real _ _ _).symm
    _ = ∫ y in hboxC s, F (y + Work.Diff.STE.iVec (hshift s)) := by
        refine setIntegral_congr_fun (measurableSet_hboxC s) (fun y _ => ?_)
        rw [iVec_hshift]
    _ = ∫ y in hboxC s, F y :=
        setIntegral_congr_fun (measurableSet_hboxC s)
          (fun y _ => Work.Diff.STE.B3.periodic1_add_iVec hper y (hshift s))

/-- **The fundamental-domain identity for the unit cube.**  The integral of a `1`-periodic
function over `(0,1]^ι` equals its integral over `(-1/2,1/2]^ι`. -/
theorem fd_unitCube_centreCube_periodic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → ℝ) → ℝ) (hper : Work.Diff.STE.Periodic1 F) (hcont : Continuous F) :
    (∫ z in Work.Diff.STE.unitCube (ι := ι), F z)
      = ∫ z in Set.pi Set.univ (fun _ : ι => Set.Ioc (-(1/2:ℝ)) (1/2)), F z := by
  have hbig : MeasureTheory.IntegrableOn F
      (Set.pi Set.univ (fun _ : ι => Set.Icc (-1:ℝ) 1)) :=
    hcont.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)
  have hsubU : Work.Diff.STE.unitCube (ι := ι) ⊆
      Set.pi Set.univ (fun _ : ι => Set.Icc (-1:ℝ) 1) := by
    intro x hx i _
    have h := hx i (Set.mem_univ i)
    rw [Set.mem_Ioc] at h
    exact ⟨by linarith [h.1], h.2⟩
  have hsubC : Set.pi Set.univ (fun _ : ι => Set.Ioc (-(1/2:ℝ)) (1/2)) ⊆
      Set.pi Set.univ (fun _ : ι => Set.Icc (-1:ℝ) 1) := by
    intro x hx i _
    have h := hx i (Set.mem_univ i)
    rw [Set.mem_Ioc] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hunionU : MeasureTheory.IntegrableOn F (⋃ s, hboxU s) := by
    rw [iUnion_hboxU]; exact hbig.mono_set hsubU
  have hunionC : MeasureTheory.IntegrableOn F (⋃ s, hboxC s) := by
    rw [iUnion_hboxC]; exact hbig.mono_set hsubC
  have hintU : ∀ s : ι → Fin 2, MeasureTheory.IntegrableOn F (hboxU s) :=
    fun s => hunionU.mono_set (Set.subset_iUnion hboxU s)
  have hintC : ∀ s : ι → Fin 2, MeasureTheory.IntegrableOn F (hboxC s) :=
    fun s => hunionC.mono_set (Set.subset_iUnion hboxC s)
  rw [← iUnion_hboxU, ← iUnion_hboxC,
    MeasureTheory.integral_iUnion (fun s => measurableSet_hboxU s) pairwiseDisjoint_hboxU hunionU,
    MeasureTheory.integral_iUnion (fun s => measurableSet_hboxC s) pairwiseDisjoint_hboxC hunionC,
    tsum_fintype, tsum_fintype]
  exact Finset.sum_congr rfl fun s _ => setIntegral_hboxU_eq_hboxC F hper s

end FundamentalDomain

/-- Real-valued form of the fundamental domain identity for the unit cube. -/
lemma fd_unitCube_centreCube_real {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → ℝ) → ℝ) (hper : Work.Diff.STE.Periodic1 F) (hcont : Continuous F) :
    (∫ z in Work.Diff.STE.unitCube (ι := ι), F z)
      = ∫ z in Set.pi Set.univ (fun _ : ι => Set.Ioc (-(1/2:ℝ)) (1/2)), F z :=
  fd_unitCube_centreCube_periodic F hper hcont

theorem STruncR_selfadjoint_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1) (ε : ℝ)
    (f g : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfs : Function.support f ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)))
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgs : Function.support g ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2))) :
    (∫ z in B3Data.centreCube (E := E), B3Data.STruncR ρ ε f z * g z)
      = ∫ z in B3Data.centreCube (E := E), f z * B3Data.STruncR ρ ε g z := by
  have hcf : Summable (fun m : Fin (Module.finrank ℝ E) → ℤ =>
      ‖Work.Diff.STE.fourierCoeff (perF f) m‖) := perF_summable f hf hfs
  have hcg : Summable (fun m : Fin (Module.finrank ℝ E) → ℤ =>
      ‖Work.Diff.STE.fourierCoeff (perF g) m‖) := perF_summable g hg hgs
  have hc : Summable (fun m => ‖trunc ρ ε (Work.Diff.STE.fourierCoeff (perF f)) m‖) :=
    summable_trunc_norm ρ hρ ε _ hcf
  have hd : Summable (fun m => ‖trunc ρ ε (Work.Diff.STE.fourierCoeff (perF g)) m‖) :=
    summable_trunc_norm ρ hρ ε _ hcg
  -- the pointwise periodicity of the real parts of Fourier series
  have hper_series : ∀ c : (Fin (Module.finrank ℝ E) → ℤ) → ℂ,
      Work.Diff.STE.Periodic1 (fun z => (Work.Diff.STE.seriesFun c z).re) :=
    fun c i z => congrArg Complex.re (Work.Diff.STE.flat.periodic1_seriesFun c i z)
  set c := trunc ρ ε (Work.Diff.STE.fourierCoeff (perF f)) with hcdef
  set d := trunc ρ ε (Work.Diff.STE.fourierCoeff (perF g)) with hddef
  -- #### the left-hand side
  have hL : (∫ z in B3Data.centreCube (E := E), B3Data.STruncR ρ ε f z * g z)
      = (∑' m, c m * star (Work.Diff.STE.fourierCoeff (perF g) m)).re := by
    have h1 : (∫ z in B3Data.centreCube (E := E),
          (Work.Diff.STE.seriesFun c z).re * g z)
        = ∫ z in Set.pi Set.univ
            (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)),
            (Work.Diff.STE.seriesFun c z).re * g z :=
      setIntegral_centreCube_eq_openCube_of_forall_eq_zero _ _ (fun z hz => by
        have hz0 : g z = 0 := by
          by_contra hne
          exact hz (hgs (Function.mem_support.mpr hne))
        rw [hz0, mul_zero])
    have h2 : (∫ z in Set.pi Set.univ
            (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)),
            (Work.Diff.STE.seriesFun c z).re * g z)
        = ∫ z in Set.pi Set.univ
            (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)),
            (Work.Diff.STE.seriesFun c z).re * (perF g z).re := by
      refine setIntegral_congr_fun (measurableSet_openCube (E := E)) (fun z hz => ?_)
      rw [perF_self g hg hgs z (fun i => Set.mem_pi.mp hz i (Set.mem_univ i))]
      simp
    have h3 : (∫ z in Set.pi Set.univ
            (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)),
            (Work.Diff.STE.seriesFun c z).re * (perF g z).re)
        = ∫ z in B3Data.centreCube (E := E),
            (Work.Diff.STE.seriesFun c z).re * (perF g z).re :=
      setIntegral_openCube_eq_centreCube (E := E)
        (fun z => (Work.Diff.STE.seriesFun c z).re * (perF g z).re)
    have hper4 : Work.Diff.STE.Periodic1
        (fun z => (Work.Diff.STE.seriesFun c z).re * (perF g z).re) := by
      intro i z
      show (Work.Diff.STE.seriesFun c (z + Pi.single i 1)).re * (perF g (z + Pi.single i 1)).re
        = (Work.Diff.STE.seriesFun c z).re * (perF g z).re
      rw [show (Work.Diff.STE.seriesFun c (z + Pi.single i 1)).re
            = (Work.Diff.STE.seriesFun c z).re from hper_series c i z,
        show perF g (z + Pi.single i 1) = perF g z from perF_periodic g i z]
    have hcont4 : Continuous
        (fun z => (Work.Diff.STE.seriesFun c z).re * (perF g z).re) :=
      (Complex.continuous_re.comp
          (Work.Diff.STE.flat.continuous_seriesFun_of_summable c hc)).mul
        (Complex.continuous_re.comp (perF_contDiff g hg hgs).continuous)
    have h4 : (∫ z in B3Data.centreCube (E := E),
            (Work.Diff.STE.seriesFun c z).re * (perF g z).re)
        = ∫ z in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
            (Work.Diff.STE.seriesFun c z).re * (perF g z).re :=
      (fd_unitCube_centreCube_real
        (fun z => (Work.Diff.STE.seriesFun c z).re * (perF g z).re) hper4 hcont4).symm
    have h5 : (∫ z in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
            (Work.Diff.STE.seriesFun c z).re * (perF g z).re)
        = (∑' m, c m * star (Work.Diff.STE.fourierCoeff (perF g) m)).re :=
      integral_seriesFun_re_mul_perF g hg hgs c hc
    have h0 : (∫ z in B3Data.centreCube (E := E), B3Data.STruncR ρ ε f z * g z)
        = ∫ z in B3Data.centreCube (E := E),
            (Work.Diff.STE.seriesFun c z).re * g z := rfl
    rw [h0, h1, h2, h3, h4, h5]
  -- #### the right-hand side
  have hR : (∫ z in B3Data.centreCube (E := E), f z * B3Data.STruncR ρ ε g z)
      = (∑' m, d m * star (Work.Diff.STE.fourierCoeff (perF f) m)).re := by
    have h1 : (∫ z in B3Data.centreCube (E := E),
          f z * (Work.Diff.STE.seriesFun d z).re)
        = ∫ z in Set.pi Set.univ
            (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)),
            f z * (Work.Diff.STE.seriesFun d z).re :=
      setIntegral_centreCube_eq_openCube_of_forall_eq_zero _ _ (fun z hz => by
        have hz0 : f z = 0 := by
          by_contra hne
          exact hz (hfs (Function.mem_support.mpr hne))
        rw [hz0, zero_mul])
    have h2 : (∫ z in Set.pi Set.univ
            (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)),
            f z * (Work.Diff.STE.seriesFun d z).re)
        = ∫ z in Set.pi Set.univ
            (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)),
            (perF f z).re * (Work.Diff.STE.seriesFun d z).re := by
      refine setIntegral_congr_fun (measurableSet_openCube (E := E)) (fun z hz => ?_)
      rw [perF_self f hf hfs z (fun i => Set.mem_pi.mp hz i (Set.mem_univ i))]
      simp
    have h3 : (∫ z in Set.pi Set.univ
            (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)),
            (perF f z).re * (Work.Diff.STE.seriesFun d z).re)
        = ∫ z in B3Data.centreCube (E := E),
            (perF f z).re * (Work.Diff.STE.seriesFun d z).re :=
      setIntegral_openCube_eq_centreCube (E := E)
        (fun z => (perF f z).re * (Work.Diff.STE.seriesFun d z).re)
    have hper4 : Work.Diff.STE.Periodic1
        (fun z => (perF f z).re * (Work.Diff.STE.seriesFun d z).re) := by
      intro i z
      show (perF f (z + Pi.single i 1)).re * (Work.Diff.STE.seriesFun d (z + Pi.single i 1)).re
        = (perF f z).re * (Work.Diff.STE.seriesFun d z).re
      rw [show perF f (z + Pi.single i 1) = perF f z from perF_periodic f i z,
        show (Work.Diff.STE.seriesFun d (z + Pi.single i 1)).re
            = (Work.Diff.STE.seriesFun d z).re from hper_series d i z]
    have hcont4 : Continuous
        (fun z => (perF f z).re * (Work.Diff.STE.seriesFun d z).re) :=
      (Complex.continuous_re.comp (perF_contDiff f hf hfs).continuous).mul
        (Complex.continuous_re.comp
          (Work.Diff.STE.flat.continuous_seriesFun_of_summable d hd))
    have h4 : (∫ z in B3Data.centreCube (E := E),
            (perF f z).re * (Work.Diff.STE.seriesFun d z).re)
        = ∫ z in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
            (perF f z).re * (Work.Diff.STE.seriesFun d z).re :=
      (fd_unitCube_centreCube_real
        (fun z => (perF f z).re * (Work.Diff.STE.seriesFun d z).re) hper4 hcont4).symm
    have h5 : (∫ z in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
            (perF f z).re * (Work.Diff.STE.seriesFun d z).re)
        = (∑' m, d m * star (Work.Diff.STE.fourierCoeff (perF f) m)).re := by
      rw [show (∫ z in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
            (perF f z).re * (Work.Diff.STE.seriesFun d z).re)
          = ∫ z in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
            (Work.Diff.STE.seriesFun d z).re * (perF f z).re from
        setIntegral_congr_fun (measurableSet_unitCube' (E := E)) (fun z _ => mul_comm _ _)]
      exact integral_seriesFun_re_mul_perF f hf hfs d hd
    have h0 : (∫ z in B3Data.centreCube (E := E), f z * B3Data.STruncR ρ ε g z)
        = ∫ z in B3Data.centreCube (E := E),
            f z * (Work.Diff.STE.seriesFun d z).re := rfl
    rw [h0, h1, h2, h3, h4, h5]
  -- #### symmetry of the coefficient pairing
  have hsym : (∑' m, c m * star (Work.Diff.STE.fourierCoeff (perF g) m)).re
      = (∑' m, d m * star (Work.Diff.STE.fourierCoeff (perF f) m)).re := by
    have hsumc : Summable (fun m => c m * star (Work.Diff.STE.fourierCoeff (perF g) m)) := by
      have hK : ∀ m, ‖Work.Diff.STE.fourierCoeff (perF g) m‖
          ≤ ∑' m, ‖Work.Diff.STE.fourierCoeff (perF g) m‖ :=
        fun m => hcg.le_tsum m (fun _ _ => norm_nonneg _)
      refine Summable.of_norm ?_
      have hnorm : (fun m => ‖c m * star (Work.Diff.STE.fourierCoeff (perF g) m)‖)
          = fun m => ‖c m‖ * ‖Work.Diff.STE.fourierCoeff (perF g) m‖ := by
        funext m
        rw [norm_mul, norm_star]
      rw [hnorm]
      refine Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (fun m => mul_le_mul_of_nonneg_left (hK m) (norm_nonneg _))
        (hc.mul_right _)
    have hsumd : Summable (fun m => d m * star (Work.Diff.STE.fourierCoeff (perF f) m)) := by
      have hK : ∀ m, ‖Work.Diff.STE.fourierCoeff (perF f) m‖
          ≤ ∑' m, ‖Work.Diff.STE.fourierCoeff (perF f) m‖ :=
        fun m => hcf.le_tsum m (fun _ _ => norm_nonneg _)
      refine Summable.of_norm ?_
      have hnorm : (fun m => ‖d m * star (Work.Diff.STE.fourierCoeff (perF f) m)‖)
          = fun m => ‖d m‖ * ‖Work.Diff.STE.fourierCoeff (perF f) m‖ := by
        funext m
        rw [norm_mul, norm_star]
      rw [hnorm]
      refine Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (fun m => mul_le_mul_of_nonneg_left (hK m) (norm_nonneg _))
        (hd.mul_right _)
    rw [Complex.re_tsum hsumc, Complex.re_tsum hsumd]
    refine tsum_congr fun m => ?_
    simp only [c, d, trunc]
    exact re_ofReal_mul_star_swap _ _ _
  rw [hL, hR, hsym]

/-! ## The smooth variants of the B3 adjunction and of `BPair_J_lin` -/

/-- **The `N`-pair integrability in the smooth setting** (the mat-continuity hypothesis of
`Work.Diff.STE.B3.integrableOn_Npair_term` is replaced by continuity of the localised component). -/
theorem contDiff_integrableOn_Npair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (k : Work.Diff.STE.Bil (I := I) (M := M))
    (hu : ∀ a b : Fin (Module.finrank ℝ E), Continuous (u a b))
    (hk : ∀ (a b : Fin (Module.finrank ℝ E)), Continuous (D.R i k a b))
    (j : ι₀) :
    MeasureTheory.IntegrableOn
      (fun y => (D.ζ j (D.pt i y)) ^ 2 * D.dens i y
        * Work.Diff.STE.B3.Phi D i u k (D.pt i y))
      (Work.Diff.STE.B3.sigmaBall D i) MeasureTheory.volume := by
  have hpt := continuousOn_pt_sigmaClosedBall' D i
  have hζ : ContinuousOn (fun y => D.ζ j (D.pt i y))
      (Work.Diff.STE.B3.sigmaClosedBall D i) :=
    (D.hζsm j).continuous.comp_continuousOn hpt
  have hdens : ContinuousOn (D.dens i) (Work.Diff.STE.B3.sigmaClosedBall D i) := by
    intro y hy
    have hy' : ‖y‖ ≤ D.σ i := hy
    have hy2 : ‖y‖ ≤ 2 * D.σ i := by have := D.hσ i; linarith
    exact (dens_continuousAt_of_mem_target D i (D.htarget i y hy2)).continuousWithinAt
  have hΦ := contDiff_phi_pt_continuous D i u k hu hk
  have hf : ContinuousOn (fun y => (D.ζ j (D.pt i y)) ^ 2 * D.dens i y
      * Work.Diff.STE.B3.Phi D i u k (D.pt i y))
      (Work.Diff.STE.B3.sigmaClosedBall D i) :=
    ((hζ.pow 2).mul hdens).mul hΦ
  refine (hf.integrableOn_compact (isCompact_sigmaClosedBall' D i)).mono_set ?_
  intro y hy
  exact le_of_lt (show ‖y‖ < D.σ i from hy)

/-- **The B3 adjunction in the smooth setting.** -/
theorem BPair_Rstar_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (k : Work.Diff.STE.Bil (I := I) (M := M))
    (hu : ∀ a b : Fin (Module.finrank ℝ E), Continuous (u a b))
    (hk : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)), Continuous (D.R j k a b)) :
    D.BPair (D.Rstar i u) k = Work.Diff.STE.B3Data.CPair i u (D.R i k) :=
  BPair_Rstar_of_integrable D i u k
    (fun j a b => contDiff_integrableOn_Rpair D i u k hu hk j a b)
    (fun a b => contDiff_integrableOn_Cpair D i u k hu hk a b)
    (fun j => contDiff_integrableOn_Npair D i u k hu (fun a b => hk i a b) j)

/-- The Friedrichs truncation of a smooth cube-supported function is smooth. -/
lemma contDiff_STruncR' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hρ : ∀ y, ‖ρ y‖ ≤ 1) (ε : ℝ) (f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfs : Function.support f ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => Work.Diff.STE.B3Data.STruncR ρ ε f z) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞)
      (⇑Complex.reCLM ∘ (Work.Diff.STE.STruncC ρ ε f :
        (Fin (Module.finrank ℝ E) → ℝ) → ℂ)) :=
    (Complex.reCLM.contDiff).comp
      ((Work.Diff.STE.B3.STruncC_contDiff_periodic ρ hρ ε f hf hfs).1)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun z => (Work.Diff.STE.STruncC ρ ε f z).re) := by
    convert h1 using 1
    funext z
    rfl
  simpa only [Work.Diff.STE.B3Data.STruncR, Work.Diff.STE.STruncC, Complex.ofReal_re] using h2

/-- **The additivity of `BPair` in a sum of reconstructions, in the smooth setting.** -/
theorem BPair_J_lin_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (k : Work.Diff.STE.Bil (I := I) (M := M))
    (u : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hu : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)), Continuous (u i a b))
    (hk : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)), Continuous (D.R j k a b)) :
    D.BPair (∑ i, D.Rstar i (u i)) k
      = ∑ i, Work.Diff.STE.B3Data.CPair i (u i) (D.R i k) := by
  classical
  have hRlin : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E))
      (z : Fin (Module.finrank ℝ E) → ℝ),
      D.R j (∑ i, D.Rstar i (u i)) a b z = ∑ i, D.R j (D.Rstar i (u i)) a b z := by
    intro j a b z
    simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat, Finset.sum_apply, sum_apply,
      Finset.mul_sum]
  have hint : ∀ (j i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      MeasureTheory.IntegrableOn
        (fun z => D.R j (D.Rstar i (u i)) a b z * D.R j k a b z)
        (Work.Diff.STE.B3Data.centreCube (E := E)) MeasureTheory.volume :=
    fun j i a b => contDiff_integrableOn_Rpair D i (u i) k (hu i) hk j a b
  have hlin : ∀ j : ι₀,
      Work.Diff.STE.B3Data.CPair j (D.R j (∑ i, D.Rstar i (u i))) (D.R j k)
        = ∑ i, Work.Diff.STE.B3Data.CPair j (D.R j (D.Rstar i (u i))) (D.R j k) := by
    intro j
    simp only [Work.Diff.STE.B3Data.CPair]
    have h1 : ∀ a b : Fin (Module.finrank ℝ E),
        ∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
            D.R j (∑ i, D.Rstar i (u i)) a b z * D.R j k a b z
          = ∑ i, ∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
              D.R j (D.Rstar i (u i)) a b z * D.R j k a b z := by
      intro a b
      rw [show (fun z => D.R j (∑ i, D.Rstar i (u i)) a b z * D.R j k a b z)
            = (fun z => ∑ i, D.R j (D.Rstar i (u i)) a b z * D.R j k a b z) from by
          funext z; rw [hRlin j a b z, Finset.sum_mul]]
      exact integral_finsetSum Finset.univ (fun i _ => hint j i a b)
    calc ∑ a, ∑ b, ∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
            D.R j (∑ i, D.Rstar i (u i)) a b z * D.R j k a b z
        = ∑ a, ∑ b, ∑ i, ∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
            D.R j (D.Rstar i (u i)) a b z * D.R j k a b z :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => h1 a b))
      _ = ∑ i, ∑ a, ∑ b, ∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
            D.R j (D.Rstar i (u i)) a b z * D.R j k a b z := by
          rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
          exact Finset.sum_comm
  calc D.BPair (∑ i, D.Rstar i (u i)) k
      = ∑ j, Work.Diff.STE.B3Data.CPair j (D.R j (∑ i, D.Rstar i (u i))) (D.R j k) := rfl
    _ = ∑ j, ∑ i, Work.Diff.STE.B3Data.CPair j (D.R j (D.Rstar i (u i))) (D.R j k) :=
          Finset.sum_congr rfl (fun j _ => hlin j)
    _ = ∑ i, ∑ j, Work.Diff.STE.B3Data.CPair j (D.R j (D.Rstar i (u i))) (D.R j k) :=
          Finset.sum_comm
    _ = ∑ i, D.BPair (D.Rstar i (u i)) k := rfl
    _ = ∑ i, Work.Diff.STE.B3Data.CPair i (u i) (D.R i k) :=
          Finset.sum_congr rfl (fun i _ => BPair_Rstar_smooth D i (u i) k (hu i) hk)

theorem BPair_J_self_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε)
    (h k : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R j h a b))
    (hk : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R j k a b)) :
    D.BPair (D.J ρ ε h) k = D.BPair h (D.J ρ ε k) := by
  have hhC : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)), Continuous (D.R j h a b) :=
    fun j a b => (hh j a b).continuous
  have hkC : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)), Continuous (D.R j k a b) :=
    fun j a b => (hk j a b).continuous
  have hu : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Continuous (fun z => Work.Diff.STE.B3Data.STruncR ρ ε (D.R i h a b) z) :=
    fun i a b => (contDiff_STruncR' ρ hρ ε (D.R i h a b) (hh i a b)
      (support_R_subset D i h a b)).continuous
  have hu' : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Continuous (fun z => Work.Diff.STE.B3Data.STruncR ρ ε (D.R i k a b) z) :=
    fun i a b => (contDiff_STruncR' ρ hρ ε (D.R i k a b) (hk i a b)
      (support_R_subset D i k a b)).continuous
  have hA : D.BPair (D.J ρ ε h) k
      = ∑ i, Work.Diff.STE.B3Data.CPair i
          (fun a b z => Work.Diff.STE.B3Data.STruncR ρ ε (D.R i h a b) z) (D.R i k) :=
    BPair_J_lin_smooth D k _ hu hkC
  have hB : D.BPair h (D.J ρ ε k)
      = ∑ i, Work.Diff.STE.B3Data.CPair i
          (fun a b z => Work.Diff.STE.B3Data.STruncR ρ ε (D.R i k a b) z) (D.R i h) := by
    rw [Work.Diff.STE.B3Data.BPair_comm]
    exact BPair_J_lin_smooth D h _ hu' hhC
  rw [hA, hB]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Work.Diff.STE.B3Data.CPair]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hself := STruncR_selfadjoint_smooth ρ hρ ε (D.R i h a b) (D.R i k a b)
    (hh i a b) (support_R_subset D i h a b) (hk i a b) (support_R_subset D i k a b)
  have hcomm : (∫ z in B3Data.centreCube (E := E),
        B3Data.STruncR ρ ε (D.R i k a b) z * D.R i h a b z)
      = ∫ z in B3Data.centreCube (E := E),
        D.R i h a b z * B3Data.STruncR ρ ε (D.R i k a b) z :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ _)
  exact hself.trans hcomm.symm

end Work.Diff.STE.B3