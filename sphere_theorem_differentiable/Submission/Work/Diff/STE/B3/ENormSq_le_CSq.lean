import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.Comp.summable_wt_fourierCoeff
import Submission.Work.Diff.STE.summable_norm_of_CSq
import Submission.Work.Diff.STE.periodization_contDiff_periodic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ENormSq_le_CSq`: the physical `Hᵏ` energy of a component is controlled by its weighted
Fourier mass

Layer B3 uses the physical-space energy `ENormSq k (D.Rper i h a b)` (the sum of the `L²` norms
squared of all `k`-fold partial derivatives of a periodised component) on the one hand, and the
weighted `ℓ²` mass `CSq k (fourierCoeff (D.Rper i h a b))` of its Fourier coefficients on the
other.  The two are equivalent norms on the same space, and this file records the direction

  `ENormSq k f ≤ C · CSq k (fourierCoeff f)`

for a `C^∞`, `1`-periodic `f` (the reverse direction, with the extra `ENormSq 0` term, is
`Work.Diff.STE.CSq_le_ENormSq`).

The proof is a three-step composition of results that are already in the workspace:

* `Work.Diff.STE.ENormSq_seriesFun_le`: for a rapidly decaying coefficient family `c`, the energy
  of the series `seriesFun c` is bounded by `C · CSq k c`;
* Fourier inversion `Work.Diff.STE.flat.seriesFun_fourierCoeff` identifies a smooth, `1`-periodic
  `f` with `seriesFun (fourierCoeff f)`;
* the rapid decay hypothesis is extracted from `summable_weighted_fourierCoeff_of_contDiff`
  (weighted `ℓ²` summability, from Bessel) together with `summable_norm_of_CSq` (weighted `ℓ²`
  summability implies weighted `ℓ¹` summability, after shifting the weight).

The last step is where the weight `⟨k⟩ = wt k` is shifted: `⟨k⟩^N ‖ĉ k‖ ≤ C_N ⟨k⟩^{s+2N} ‖ĉ k‖²`
is the AM–GM inequality against the summable dual weight `⟨k⟩^{-s}`.

For the Layer B3 application the only remaining input is that the periodised component
`D.Rper i h a b` is smooth and `1`-periodic, which is derived from the smoothness of the local
component `D.R i h a b` and the fact that its support lies in the open centred unit cube
(`B3Data.psi_supp`, a consequence of `B3Data.hχsupp`).
-/

noncomputable section

namespace Work.Diff.STE

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The norm of a real number seen in `ℂ` is its absolute value. -/
lemma norm_ofReal_cast (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by
  have h : ‖((x : ℝ) : ℂ)‖ ^ 2 = x ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  calc ‖((x : ℝ) : ℂ)‖ = Real.sqrt (‖((x : ℝ) : ℂ)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (x ^ 2) := by rw [h]
    _ = |x| := Real.sqrt_sq_eq_abs x

/-- `‖⟨k⟩^N · z‖ = ⟨k⟩^N ‖z‖` for the real weight `⟨k⟩ = wt k ≥ 1 > 0`. -/
lemma norm_wt_pow_mul (N : ℕ) (k : ι → ℤ) (z : ℂ) :
    ‖(wt k) ^ N * z‖ = (wt k) ^ N * ‖z‖ := by
  rw [norm_mul, norm_pow, norm_ofReal_cast, abs_of_nonneg (wt_pos k).le]

/-- The weight shift: multiplying the coefficient by `⟨k⟩^N` shifts the `CSq`-weight up by `2N`. -/
lemma wt_pow_mul_norm_sq (s N : ℕ) (k : ι → ℤ) (z : ℂ) :
    (wt k) ^ s * ‖(wt k) ^ N * z‖ ^ 2 = (wt k) ^ (s + 2 * N) * ‖z‖ ^ 2 := by
  have hexp : s + N * 2 = s + 2 * N := by omega
  rw [norm_wt_pow_mul, mul_pow, ← pow_mul, ← mul_assoc, ← pow_add, hexp]

/-- **Weighted `ℓ¹` summability of the Fourier coefficients of a smooth `1`-periodic
function.**  Every weight `⟨k⟩^N` times the modulus of the `k`-th Fourier coefficient is
summable: this is the rapid decay hypothesis needed by `ENormSq_seriesFun_le`. -/
lemma summable_wt_pow_norm_fourierCoeff_of_contDiff (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : Periodic1 f) (N : ℕ) :
    Summable (fun k : ι → ℤ => (wt k) ^ N * ‖fourierCoeff f k‖) := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ, Fintype.card ι < 2 * s := ⟨Fintype.card ι + 1, by omega⟩
  have hcsq : Summable (fun k : ι → ℤ => (wt k) ^ s * ‖(wt k) ^ N * fourierCoeff f k‖ ^ 2) := by
    refine (summable_weighted_fourierCoeff_of_contDiff f hf hper (s + 2 * N)).congr
      (fun k => ?_)
    exact (wt_pow_mul_norm_sq s N k (fourierCoeff f k)).symm
  have hnorm := summable_norm_of_CSq s hs (fun k : ι → ℤ => (wt k) ^ N * fourierCoeff f k) hcsq
  refine hnorm.congr (fun k => ?_)
  exact norm_wt_pow_mul N k (fourierCoeff f k)

/-- **The `Hᵏ` energy is controlled by the weighted Fourier mass**, for an arbitrary smooth
`1`-periodic function.  This is the general form of the target lemma, to which only the smoothness
and periodicity of the periodised component `D.Rper i h a b` have to be added. -/
theorem ENormSq_le_CSq_of_contDiff_periodic (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : (ι → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) f → Periodic1 f →
      ENormSq k f ≤ C * CSq k (fourierCoeff f) := by
  obtain ⟨C, hC, hbound⟩ := ENormSq_seriesFun_le (ι := ι) k
  refine ⟨C, hC, fun f hf hper => ?_⟩
  have hinv : f = seriesFun (fourierCoeff f) :=
    funext (fun x => (flat.seriesFun_fourierCoeff f hf hper x).symm)
  calc ENormSq k f = ENormSq k (seriesFun (fourierCoeff f)) :=
        congrArg (fun g => ENormSq k g) hinv
    _ ≤ C * CSq k (fourierCoeff f) :=
        hbound (fourierCoeff f) (fun N => summable_wt_pow_norm_fourierCoeff_of_contDiff f hf hper N)

end General

end Work.Diff.STE

namespace Work.Diff.STE.B3

section B3App

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I (⊤ : ℕ∞) M]
variable {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The periodised component `D.Rper i h a b` is smooth and `1`-periodic as soon as the local
component `D.R i h a b` is smooth: the support of the latter lies in the open centred unit cube
(`B3Data.psi_supp`, from `B3Data.hχsupp`), so the periodisation is a locally finite sum of
translates.  (No `[I.Boundaryless]` is needed, and the smoothness hypothesis is on `D.R`, not on
`D.Rper` as in `B3Data.Rper_contDiff_periodic`.) -/
lemma Rper_contDiff_periodic_of_R_contDiff
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (a b : Fin (Module.finrank ℝ E))
    (hsm : ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b)) :
    ContDiff ℝ (⊤ : ℕ∞) (D.Rper i h a b) ∧ Work.Diff.STE.Periodic1 (D.Rper i h a b) := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      ((D.R i h a b z : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hsm
  have hFsupp : Function.support (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      ((D.R i h a b z : ℝ) : ℂ)) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro z hz
    refine D.psi_supp i (Function.mem_support.mpr (fun hpsi => ?_))
    have hzR : D.R i h a b z = 0 := by
      simp only [B3Data.R, hpsi, zero_mul]
    refine hz ?_
    show ((D.R i h a b z : ℝ) : ℂ) = 0
    rw [hzR, Complex.ofReal_zero]
  have hEq : D.Rper i h a b = (fun x : Fin (Module.finrank ℝ E) → ℝ =>
      ∑' m : Fin (Module.finrank ℝ E) → ℤ,
        (fun z : Fin (Module.finrank ℝ E) → ℝ => ((D.R i h a b z : ℝ) : ℂ)) (x + iVec m)) :=
    rfl
  rw [hEq]
  have hres := periodization_contDiff_periodic _ hF hFsupp
  exact ⟨hres.1, hres.2.1⟩

end B3App

/-! ## The target -/

theorem ENormSq_le_CSq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.ENormSq k (D.Rper i h a b)
        ≤ C * Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b)) := by
  obtain ⟨C, hC, hmain⟩ :=
    Work.Diff.STE.ENormSq_le_CSq_of_contDiff_periodic (ι := Fin (Module.finrank ℝ E)) k
  refine ⟨C, hC, fun i a b => ?_⟩
  obtain ⟨hcd, hper⟩ := Rper_contDiff_periodic_of_R_contDiff D i h a b (hsmooth i a b)
  exact hmain (D.Rper i h a b) hcd hper

end Work.Diff.STE.B3
