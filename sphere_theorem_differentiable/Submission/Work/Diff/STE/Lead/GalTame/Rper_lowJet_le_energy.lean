import Mathlib
import Submission.Work.Diff.STE.Lead.Rper_contDiff
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.B3.CSq_le_ENormSq_of_periodization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Low-order jets of a periodised component, measured in `L²`

The tame (transport) estimates of the DeTurck operator that the `GalTame` layer feeds into the
Galerkin scheme need a bound for the `L²` norm of *one* low-order iterated derivative
`∂^{γ} (Rper i h a b)` of a periodised component by the *top-order* energy
`ENormSq m (Rper i h a b)`, with a constant that depends only on `D` and `m` — in particular
**uniform in the section `h`, the chart `i`, the frame indices `a b` and the multi-index**:

  `∫_{unitCube} ‖∂^{γ} (Rper i h a b)‖² ≤ C · ENormSq m (Rper i h a b)`,  `|γ| = j' ≤ m`.

This is exactly `Work.Diff.STE.Lead.GalTame.Rper_lowJet_le_energy`.

## Route

Everything is done on the Fourier side, where the loss of *differentiability order* is transparent.

* A single iterated derivative of a smooth `1`-periodic `f` is a Fourier multiplier:
  `∂^{γ} f = seriesFun (dmulV (ofFn γ) ĉ)` (`pdList_seriesFun`), and by Parseval
  (`ens_integral_normSq_seriesFun`) its `L²` norm squared is `Σ_μ ‖dmulV (ofFn γ) ĉ μ‖²`.
* Termwise, `‖dmulV (ofFn γ) ĉ μ‖² ≤ ((2π)² ⟨μ⟩)^{j'} ‖ĉ μ‖² ≤ ((2π)² ⟨μ⟩)^{m} ‖ĉ μ‖²`, because
  `j' ≤ m` and `(2π)² ⟨μ⟩ ≥ 1`; this is `norm_sq_dmulV_le`.  Summing,
  `∫ ‖∂^{γ} f‖² ≤ (2π)^{2m} · CSq m ĉ`.  **No cardinality factor** and no appeal to the order-`j'`
  energy appear: the weight `⟨μ⟩^{m}` of `CSq m` absorbs the `j'`-fold multiplier.
* The Sobolev comparison for a *periodisation*, `CSq_le_ENormSq_of_periodization m` (`m ≥ 1`),
  turns `CSq m ĉ` into `C · ENormSq m P`, using that the local component `R` is supported in the
  open centred cube (whence `P` vanishes on a half-integer hyperplane and its mean is controlled by
  its first derivative).  This is the only place where the extra `ENormSq 0` of the general
  (support-free) comparison `CSq_le_ENormSq` is removed.

The only inputs about the layer B3 data are the smoothness of the local component
(`R_contDiff_of_chartData`, from the chart data of `h`), its support (`B3Data.psi_supp`) and the
smoothness/periodicity of the periodisation (`Lead.Rper_contDiff_and_periodic`).
-/

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE.Lead.GalTame

/-- **A single iterated derivative of a smooth periodic function is controlled by the weighted
Fourier mass at any higher order.**  For `j ≤ m`, a multi-index `γ : Fin j → ι` and a `C^∞`,
`1`-periodic `f`,

  `∫_{unitCube} ‖∂^{γ} f‖² ≤ (2π)^{2m} · CSq m (fourierCoeff f)`.

The constant is explicit (`(2π)^{2m}`, no cardinality factor), and the proof is the Fourier
multiplier estimate `‖dmulV (ofFn γ) ĉ μ‖² ≤ ((2π)² ⟨μ⟩)^{j} ‖ĉ μ‖²` together with Parseval and the
monotonicity of `μ ↦ ((2π)² ⟨μ⟩)^{j}` in the order. -/
lemma lowJet_integral_pdVec_le_CSq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m j : ℕ) (hjm : j ≤ m) (γ : Fin j → ι) (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : Work.Diff.STE.Periodic1 f) :
    ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pdVec j γ f x‖ ^ 2
      ≤ (2 * Real.pi) ^ (2 * m) * Work.Diff.STE.CSq m (Work.Diff.STE.fourierCoeff f) := by
  classical
  set c : (ι → ℤ) → ℂ := Work.Diff.STE.fourierCoeff f with hc
  have hdecay : ∀ N : ℕ, Summable (fun k : ι → ℤ => Work.Diff.STE.wt k ^ N * ‖c k‖) :=
    fun N => Work.Diff.STE.summable_wt_pow_norm_fourierCoeff_of_contDiff f hf hper N
  have hinv : f = Work.Diff.STE.seriesFun c :=
    funext fun x => (Work.Diff.STE.flat.seriesFun_fourierCoeff f hf hper x).symm
  have hpd : Work.Diff.STE.pdVec j γ f
      = Work.Diff.STE.seriesFun (Work.Diff.STE.dmulV (List.ofFn γ) c) := by
    conv_lhs => rw [hinv]
    exact funext (Work.Diff.STE.pdList_seriesFun (List.ofFn γ) c hdecay)
  have hsumm : Summable (fun k : ι → ℤ => ‖Work.Diff.STE.dmulV (List.ofFn γ) c k‖) := by
    simpa using Work.Diff.STE.summable_dmulV (List.ofFn γ) c hdecay 0
  rw [hpd, Work.Diff.STE.ens_integral_normSq_seriesFun _ hsumm, Work.Diff.STE.CSq,
    ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k => ?_)
    (Work.Diff.STE.summable_sq_of_nonneg hsumm (fun k => norm_nonneg _))
    ((Work.Diff.STE.summable_wt_pow_mul_norm_sq c hdecay m).mul_left _)
  have hbase : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 * Work.Diff.STE.wt k := by
    have h1 : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
    have h3 : (0 : ℝ) ≤ Work.Diff.STE.wt k := le_of_lt (Work.Diff.STE.wt_pos k)
    nlinarith [Work.Diff.STE.wt_one_le k]
  calc ‖Work.Diff.STE.dmulV (List.ofFn γ) c k‖ ^ 2
      ≤ ((2 * Real.pi) ^ 2 * Work.Diff.STE.wt k) ^ (List.ofFn γ).length * ‖c k‖ ^ 2 :=
        Work.Diff.STE.norm_sq_dmulV_le _ _ _
    _ = ((2 * Real.pi) ^ 2 * Work.Diff.STE.wt k) ^ j * ‖c k‖ ^ 2 := by
        rw [List.length_ofFn]
    _ ≤ ((2 * Real.pi) ^ 2 * Work.Diff.STE.wt k) ^ m * ‖c k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hbase hjm) (sq_nonneg _)
    _ = (2 * Real.pi) ^ (2 * m) * (Work.Diff.STE.wt k ^ m * ‖c k‖ ^ 2) := by
        rw [mul_pow, ← pow_mul]; ring

theorem Rper_lowJet_le_energy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (m : ℕ)
    (hn : 0 < Module.finrank ℝ E) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (j' : ℕ)
        (γ : Fin j' → Fin (Module.finrank ℝ E)), j' ≤ m →
        ∫ x in Work.Diff.STE.unitCube,
            ‖Work.Diff.STE.pdVec j' γ (D.Rper i h a b) x‖ ^ 2
          ≤ C * Work.Diff.STE.ENormSq m (D.Rper i h a b) := by
  classical
  rcases m with _ | m'
  · -- `m = 0`: the only surviving multi-index is the empty one, and then both sides are `L²`.
    refine ⟨1, zero_le_one, ?_⟩
    intro h hsm i a b j' γ hj'
    have hj0 : j' = 0 := Nat.eq_zero_of_le_zero hj'
    subst hj0
    rw [one_mul, Work.Diff.STE.ENormSq_zero]
    have hzero : Work.Diff.STE.pdVec 0 γ (D.Rper i h a b) = D.Rper i h a b := by
      simp [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]
    rw [hzero]
  · -- `m ≥ 1`: Fourier interpolation down from the top order, then the periodisation Sobolev
    -- comparison at the top order.
    have hm : 1 ≤ m' + 1 := Nat.succ_le_succ (Nat.zero_le m')
    haveI : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, hn⟩⟩
    obtain ⟨C₂, hC₂nn, hC₂⟩ :=
      Work.Diff.STE.B3.CSq_le_ENormSq_of_periodization
        (ι := Fin (Module.finrank ℝ E)) (m' + 1) hm
    refine ⟨(2 * Real.pi) ^ (2 * (m' + 1)) * C₂,
      mul_nonneg (pow_nonneg (by positivity) _) hC₂nn, ?_⟩
    intro h hsm i a b j' γ hj'
    obtain ⟨hPsm, hPper⟩ :=
      Work.Diff.STE.Lead.Rper_contDiff_and_periodic D h hsm i a b
    have hRsm : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : Fin (Module.finrank ℝ E) → ℝ => ((D.R i h a b z : ℝ) : ℂ)) :=
      (Complex.ofRealCLM.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp
        (Work.Diff.STE.B3.R_contDiff_of_chartData D h hsm i a b)
    have hsupp : Function.support
        (fun z : Fin (Module.finrank ℝ E) → ℝ => ((D.R i h a b z : ℝ) : ℂ)) ⊆
        Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
      intro z hz
      refine D.psi_supp i ?_
      rw [Function.mem_support] at hz ⊢
      intro h0
      exact hz (by simp only [Work.Diff.STE.B3Data.R, h0, zero_mul, Complex.ofReal_zero])
    have hrepr : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
        D.Rper i h a b z = ∑' m : Fin (Module.finrank ℝ E) → ℤ,
          (fun w : Fin (Module.finrank ℝ E) → ℝ => ((D.R i h a b w : ℝ) : ℂ))
            (z + Work.Diff.STE.iVec m) := fun z => rfl
    calc ∫ x in Work.Diff.STE.unitCube,
            ‖Work.Diff.STE.pdVec j' γ (D.Rper i h a b) x‖ ^ 2
        ≤ (2 * Real.pi) ^ (2 * (m' + 1))
            * Work.Diff.STE.CSq (m' + 1) (Work.Diff.STE.fourierCoeff (D.Rper i h a b)) :=
          lowJet_integral_pdVec_le_CSq (m' + 1) j' hj' γ _ hPsm hPper
      _ ≤ (2 * Real.pi) ^ (2 * (m' + 1))
            * (C₂ * Work.Diff.STE.ENormSq (m' + 1) (D.Rper i h a b)) :=
          mul_le_mul_of_nonneg_left
            (hC₂ (fun z : Fin (Module.finrank ℝ E) → ℝ => ((D.R i h a b z : ℝ) : ℂ))
              (D.Rper i h a b) hRsm hsupp hPsm hPper hrepr)
            (by positivity)
      _ = ((2 * Real.pi) ^ (2 * (m' + 1)) * C₂)
            * Work.Diff.STE.ENormSq (m' + 1) (D.Rper i h a b) := by
          ring

end Work.Diff.STE.Lead.GalTame
