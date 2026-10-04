import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.B3.Pointwise
import Submission.Work.Diff.STE.B3.scoeff_add_of_support
import Submission.Work.Diff.STE.poincare_cube
import Submission.Work.Diff.STE.CSq_sub_tendsto

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `BNorm k (u m t - U t) → 0` from coordinatewise convergence of the Fourier coefficients

The composite `Hᵏ` norm `D.BNorm k h = Σ_i Σ_{ab} CSq k (fourierCoeff (D.Rper i h a b))` of
`B3Data` is additive in the section, and the additive pieces are read off from the Fourier
coefficients of the periodised components.  Hence, if for every chart `i`, every pair of frame
indices `(a,b)` and every frequency `μ` the coefficient of `Rper i (u m t) a b` converges to that
of `Rper i (U t) a b`, and if all coefficient families obey a uniform decay bound
`‖·‖ · ⟨μ⟩^M ≤ C` (uniform in `m`, in the frequency, and on the time interval), then
`D.BNorm k (u m t - U t) → 0` on `[0,τ₀]`, at every level `k`.

The proof decomposes this into:

* `perFun_sub`/`Rper_sub`/`fourierCoeff_Rper_sub` below: the periodised components are linear in
  the section (the lattice sum is finitely supported because `ψ i` is supported in the open unit
  cube) and `fourierCoeff` is additive for the resulting continuous functions;
* the analytic core `Work.Diff.STE.CSq_sub_tendsto`: a dominated-convergence statement for the
  weighted `ℓ²` sum `CSq` (Tannery's theorem);
* the finite sum over the charts and the frame indices.
-/

namespace Work.Diff.STE.B3

/-- **The periodisation is subtractive in the function** (for functions supported in the open unit
cube, so that all lattice sums are finitely supported). -/
lemma perFun_sub {n : ℕ} (f g : (Fin n → ℝ) → ℝ)
    (hfs : Function.support f ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)))
    (hgs : Function.support g ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)))
    (y : Fin n → ℝ) :
    perFun (f - g) y = perFun f y - perFun g y := by
  have h1 : ∀ k : Fin n → ℤ,
      (((f - g) (y + Work.Diff.STE.iVec k) : ℝ) : ℂ)
        = ((f (y + Work.Diff.STE.iVec k) : ℝ) : ℂ)
          - ((g (y + Work.Diff.STE.iVec k) : ℝ) : ℂ) := by
    intro k
    simp only [Pi.sub_apply, Complex.ofReal_sub]
  simp only [perFun]
  rw [tsum_congr h1]
  exact Summable.tsum_sub (summable_perFun hfs y) (summable_perFun hgs y)

end Work.Diff.STE.B3

namespace Work.Diff.STE

namespace B3Data

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

omit [CompleteSpace E] [I.Boundaryless] in
/-- The localised component of a difference of sections is the difference of the components. -/
lemma R_sub (D : B3Data (I := I) (M := M) ι₀ g₀) (X Y : Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    D.R i (X - Y) a b = D.R i X a b - D.R i Y a b := by
  funext z
  simp only [B3Data.R, B3Data.mat, Pi.sub_apply, sub_apply]
  ring

/-- The support of a localised component lies in the half-open unit cube. -/
lemma R_support_halfOpen (D : B3Data (I := I) (M := M) ι₀ g₀)
    (h : Bil (I := I) (M := M)) (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    Function.support (D.R i h a b) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) :=
  fun _ hz => Set.pi_mono (fun _ _ => Set.Ioo_subset_Ioc_self) (D.R_support i h a b hz)

/-- **The periodisation is subtractive in the section**, as an equality of functions. -/
lemma Rper_sub (D : B3Data (I := I) (M := M) ι₀ g₀) (X Y : Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    D.Rper i (X - Y) a b = D.Rper i X a b - D.Rper i Y a b := by
  have hR : D.R i (X - Y) a b = D.R i X a b - D.R i Y a b := R_sub D X Y i a b
  funext z
  show B3.perFun (D.R i (X - Y) a b) z
      = B3.perFun (D.R i X a b) z - B3.perFun (D.R i Y a b) z
  rw [hR]
  exact B3.perFun_sub _ _ (R_support_halfOpen D X i a b) (R_support_halfOpen D Y i a b) z

/-- **The Fourier coefficients are additive in the section**: the coefficient of the difference is
the difference of the coefficients.  This is `fourierCoeff_sub` (linearity of the integral) applied
to `Rper_sub`, the smoothness hypotheses providing the required continuity. -/
lemma fourierCoeff_Rper_sub (D : B3Data (I := I) (M := M) ι₀ g₀) (X Y : Bil (I := I) (M := M))
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ)
    (hX : ContDiff ℝ (⊤ : ℕ∞) (D.Rper i X a b))
    (hY : ContDiff ℝ (⊤ : ℕ∞) (D.Rper i Y a b)) :
    Work.Diff.STE.fourierCoeff (D.Rper i (X - Y) a b) μ
      = Work.Diff.STE.fourierCoeff (D.Rper i X a b) μ
        - Work.Diff.STE.fourierCoeff (D.Rper i Y a b) μ := by
  rw [show D.Rper i (X - Y) a b = fun z => D.Rper i X a b z - D.Rper i Y a b z from
    funext fun z => congrFun (Rper_sub D X Y i a b) z]
  exact Work.Diff.STE.fourierCoeff_sub _ _ hX.continuous hY.continuous μ

end B3Data

end Work.Diff.STE

namespace Work.Diff.STE.Lead

open Filter

-- the statement of the target lemma has two hypotheses (`hper`, `hperU`) that the proof does not
-- use (periodicity of the periodised components is automatic); keep them verbatim, silently.
set_option linter.unusedVariables false

theorem BNorm_tendsto_of_coeff_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (τ₀ : ℝ)
    (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (U : ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : ∀ (m : ℕ) (t : ℝ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i (u m t) a b))
    (hper : ∀ (m : ℕ) (t : ℝ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.Periodic1 (D.Rper i (u m t) a b))
    (hsmU : ∀ (t : ℝ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i (U t) a b))
    (hperU : ∀ (t : ℝ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.Periodic1 (D.Rper i (U t) a b))
    (hdecM : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (t : ℝ), t ∈ Set.Ico (0 : ℝ) τ₀ →
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ‖ * (Work.Diff.STE.wt μ) ^ M ≤ C)
    (hdecU : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ), t ∈ Set.Ico (0 : ℝ) τ₀ →
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ‖ * (Work.Diff.STE.wt μ) ^ M ≤ C)
    (hconv : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      TendstoUniformlyOn
        (fun (m : ℕ) (t : ℝ) => Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ)
        (fun (t : ℝ) => Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ)
        Filter.atTop (Set.Ico (0 : ℝ) τ₀)) :
    ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ k : ℕ,
      Filter.Tendsto (fun m : ℕ => D.BNorm k (u m t - U t)) Filter.atTop (nhds 0) := by
  intro t ht k
  -- the coefficient families of the two sections at the fixed time `t`, and the analytic core
  have key : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Filter.Tendsto (fun m : ℕ => Work.Diff.STE.CSq k
          (fun μ : Fin (Module.finrank ℝ E) → ℤ =>
            Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ
              - Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ))
        Filter.atTop (nhds 0) := by
    intro i a b
    refine Work.Diff.STE.CSq_sub_tendsto
      (fun m μ => Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ)
      (fun μ => Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ) ?_ ?_ k
    · intro M
      obtain ⟨C₁, hC₁, h₁⟩ := hdecM M
      obtain ⟨C₂, hC₂, h₂⟩ := hdecU M
      exact ⟨max C₁ C₂, le_max_of_le_left hC₁, fun m μ =>
        ⟨le_trans (h₁ m t ht i a b μ) (le_max_left C₁ C₂),
          le_trans (h₂ t ht i a b μ) (le_max_right C₁ C₂)⟩⟩
    · intro μ
      exact (hconv i a b μ).tendsto_at ht
  -- additivity of `BNorm` in the section
  have hBN : ∀ m : ℕ, D.BNorm k (u m t - U t)
      = ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          Work.Diff.STE.CSq k
            (fun μ : Fin (Module.finrank ℝ E) → ℤ =>
              Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ
                - Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ) := by
    intro m
    simp only [B3Data.BNorm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun a _ =>
      Finset.sum_congr rfl (fun b _ => ?_)))
    exact congrArg (Work.Diff.STE.CSq k) (funext fun μ =>
      B3Data.fourierCoeff_Rper_sub D (u m t) (U t) i a b μ (hsm m t i a b) (hsmU t i a b))
  rw [show (fun m : ℕ => D.BNorm k (u m t - U t)) = fun m : ℕ =>
      ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Work.Diff.STE.CSq k
          (fun μ : Fin (Module.finrank ℝ E) → ℤ =>
            Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ
              - Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ) from funext hBN]
  -- a finite sum of sequences tending to `0`
  have hsum := tendsto_finsetSum (Finset.univ : Finset ι₀) (fun i _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin (Module.finrank ℝ E))) (fun a _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun b _ => key i a b)))
  simpa using hsum

end Work.Diff.STE.Lead
