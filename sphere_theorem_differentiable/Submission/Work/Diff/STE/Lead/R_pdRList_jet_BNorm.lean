import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.Recon
import Submission.Work.Diff.STE.B3.pdList_le_sqrt_CSq
import Submission.Work.Diff.STE.commutator_core
import Submission.Work.Diff.STE.CSq_periodization_le_of_sup_bound
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The jet bound for the localised components of a section, against the composite `H^{k₀}` norm

This file proves `Work.Diff.STE.Lead.R_pdRList_jet_BNorm`: the iterated partial derivatives of the
localised chart components `D.R i h a b` of a section `h` (in the `g₀`-orthonormal frame of the
Layer B3 data `D`) are bounded, on the flat `2σ i`-ball, by a constant times the square root of the
composite Sobolev norm

`D.BNorm k₀ h = ∑_i ∑_a ∑_b CSq k₀ (fourierCoeff (D.Rper i h a b))`

of the *periodised* components, provided the number of derivatives `m` is below the critical
Sobolev order for `k₀` (`finrank ℝ E + 2m < 2k₀`).

Route (the standard Fourier/Sobolev argument, assembled from Layer A/B3):

* `Work.Diff.STE.B3.pdList_le_sqrt_CSq` bounds `‖pdList q f x‖ ≤ C √(CSq k₀ (fourierCoeff f))` for
  a smooth `1`-periodic `f` and `q.length ≤ m`;
* the function to which it is applied is the periodisation `D.Rper i h a b`, which is smooth and
  periodic (`Work.Diff.STE.B3.R_contDiff_of_chartData` +
  `Work.Diff.STE.periodization_contDiff_periodic`);
* on the open `1/2`-cube around `z` (`‖z‖ ≤ 2σ i ≤ 1/4`), the periodisation agrees with the
  complexified component `↑(D.R i h a b)` (`Work.Diff.STE.periodization_eq_self`), and since the
  iterated partial derivatives are a local operation (`pdList_eventuallyEq_of_eventuallyEq`) the
  jet of the component at `z` equals the jet of the periodisation there;
* the complexification dictionary `pdVec_ofReal_pdRList` identifies the mixed derivatives
  `∂^γ (↑∂^l (R i h a b))` with `↑(∂^{γ,l} (R i h a b))`;
* `CSq k₀ (fourierCoeff (D.Rper i h a b)) ≤ D.BNorm k₀ h` because all the summands of `BNorm` are
  nonnegative.
-/

namespace Work.Diff.STE.Lead

open scoped ContDiff

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-! ## Complexification of iterated partial derivatives

`pd i` (`Work.Diff.STE.pd`) is the `i`-th partial derivative of a complex valued function and
`pdR i` the same for real valued functions; the two commute with the inclusion `ℂ ← ℝ`, with no
differentiability hypothesis (a `fderiv` of a non differentiable function is `0`). -/

private lemma pd_ofReal_aux {n : ℕ} (i : Fin n) (g : (Fin n → ℝ) → ℝ) :
    Work.Diff.STE.pd i (fun y : Fin n → ℝ => ((g y : ℝ) : ℂ))
      = fun x : Fin n → ℝ => ((Work.Diff.STE.pdR i g x : ℝ) : ℂ) := by
  funext x
  show (fderiv ℝ (fun y : Fin n → ℝ => ((g y : ℝ) : ℂ)) x) (Pi.single i 1)
    = ((fderiv ℝ g x) (Pi.single i 1) : ℂ)
  have hcomp : (fun y : Fin n → ℝ => ((g y : ℝ) : ℂ)) = Complex.ofRealCLM ∘ g := by
    funext y; exact (Complex.ofRealCLM_apply (g y)).symm
  by_cases hg : DifferentiableAt ℝ g x
  · rw [hcomp]
    have h := (Complex.ofRealCLM.hasFDerivAt (x := g x)).comp x hg.hasFDerivAt
    rw [h.fderiv]
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  · have hg' : ¬ DifferentiableAt ℝ (fun y : Fin n → ℝ => ((g y : ℝ) : ℂ)) x := by
      intro h
      refine hg ?_
      have h2 := Complex.reCLM.differentiableAt.comp x h
      simpa [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using h2
    rw [fderiv_zero_of_not_differentiableAt hg, fderiv_zero_of_not_differentiableAt hg']
    simp

private lemma pdList_ofReal_aux {n : ℕ} (l : List (Fin n)) (f : (Fin n → ℝ) → ℝ) :
    Work.Diff.STE.pdList l (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ))
      = fun x : Fin n → ℝ => ((Work.Diff.STE.pdRList l f x : ℝ) : ℂ) := by
  induction l with
  | nil => rfl
  | cons i rest ih =>
    show Work.Diff.STE.pd i (Work.Diff.STE.pdList rest (fun y => ((f y : ℝ) : ℂ)))
      = fun x => ((Work.Diff.STE.pdR i (Work.Diff.STE.pdRList rest f) x : ℝ) : ℂ)
    rw [ih]
    exact pd_ofReal_aux i (Work.Diff.STE.pdRList rest f)

/-- The `List.foldr` recursion of `pdRList` is compatible with concatenation of lists. -/
private lemma pdRList_append {n : ℕ} (a b : List (Fin n)) (f : (Fin n → ℝ) → ℝ) :
    Work.Diff.STE.pdRList a (Work.Diff.STE.pdRList b f) = Work.Diff.STE.pdRList (a ++ b) f := by
  simp only [Work.Diff.STE.pdRList, List.foldr_append]

/-- **The complexification dictionary for the mixed jet.**  The `j` iterated partial derivatives
(along the tuple `γ`) of the complexification of `∂^l f` is the complexification of the iterated
partial derivative of `f` along `γ` followed by `l`. -/
private lemma pdVec_ofReal_pdRList {n j : ℕ} (γ : Fin j → Fin n) (l : List (Fin n))
    (f : (Fin n → ℝ) → ℝ) :
    Work.Diff.STE.pdVec j γ (fun y : Fin n → ℝ => ((Work.Diff.STE.pdRList l f y : ℝ) : ℂ))
      = fun x : Fin n → ℝ => ((Work.Diff.STE.pdRList (List.ofFn γ ++ l) f x : ℝ) : ℂ) := by
  rw [Work.Diff.STE.pdVec, pdList_ofReal_aux (List.ofFn γ) (Work.Diff.STE.pdRList l f)]
  funext x
  rw [pdRList_append]

/-- **Locality of the iterated partial derivatives.**  Eventually equal functions have the same
iterated `pdList`-derivative, in the eventual sense. -/
private lemma pdList_eventuallyEq_of_eventuallyEq {n : ℕ} {g₁ g₂ : (Fin n → ℝ) → ℂ}
    {x : Fin n → ℝ} (h : g₁ =ᶠ[nhds x] g₂) (l : List (Fin n)) :
    Work.Diff.STE.pdList l g₁ =ᶠ[nhds x] Work.Diff.STE.pdList l g₂ := by
  induction l with
  | nil => exact h
  | cons i rest ih =>
    have hfd : fderiv ℝ (Work.Diff.STE.pdList rest g₁) =ᶠ[nhds x]
        fderiv ℝ (Work.Diff.STE.pdList rest g₂) := ih.fderiv
    have hval : Work.Diff.STE.pd i (Work.Diff.STE.pdList rest g₁)
        =ᶠ[nhds x] Work.Diff.STE.pd i (Work.Diff.STE.pdList rest g₂) := by
      refine hfd.mono (fun y hy => ?_)
      show (fderiv ℝ (Work.Diff.STE.pdList rest g₁) y) (Pi.single i 1)
        = (fderiv ℝ (Work.Diff.STE.pdList rest g₂) y) (Pi.single i 1)
      rw [hy]
    simpa only [Work.Diff.STE.pdList, List.foldr_cons, Work.Diff.STE.pd] using hval

/-! ## The localised component and its periodisation -/

section Main

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **On the `2σ i`-ball the periodisation agrees with the complexified component.**  The support of
`D.R i h a b` lies in the open centred unit cube, so the periodisation, evaluated at a point `z`
with `‖z‖ ≤ 2σ i ≤ 1/4`, has a single contributing term, and locally around `z` (i.e. on the open
ball of radius `1/2 - ‖z‖ ≥ 1/4`) the periodisation *is* the complexified component. -/
private lemma Rper_eventuallyEq
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : ‖z‖ ≤ 2 * D.σ i) :
    D.Rper i h a b =ᶠ[nhds z] fun y : Fin (Module.finrank ℝ E) → ℝ =>
      ((D.R i h a b y : ℝ) : ℂ) := by
  have hsupp : Function.support (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      ((D.R i h a b y : ℝ) : ℂ)) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro y hy
    exact D.R_support i h a b
      (by simpa only [Function.mem_support, Complex.ofReal_ne_zero] using hy)
  have hr : 0 < 1 / 2 - ‖z‖ := by
    have h1 : 2 * D.σ i ≤ 1 / 4 := D.hσ2 i
    linarith
  have hball : z ∈ Metric.ball z (1 / 2 - ‖z‖) := Metric.mem_ball_self hr
  have ho : IsOpen (Metric.ball z (1 / 2 - ‖z‖)) := Metric.isOpen_ball
  refine Filter.eventually_of_mem (ho.mem_nhds hball) ?_
  intro y hy
  have hyz : ‖y - z‖ < 1 / 2 - ‖z‖ := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hy
  have hyn : ‖y‖ < 1 / 2 := by
    have h2 : ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
      have h3 : y - z + z = y := sub_add_cancel y z
      calc ‖y‖ = ‖y - z + z‖ := by rw [h3]
        _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
    linarith
  have hx : ∀ i : Fin (Module.finrank ℝ E), y i ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    intro i
    refine abs_lt.mp (lt_of_le_of_lt ?_ hyn)
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm y i
  have hpe := Work.Diff.STE.periodization_eq_self
    (f := fun y : Fin (Module.finrank ℝ E) → ℝ => ((D.R i h a b y : ℝ) : ℂ)) hsupp hx
  have hrepr : D.Rper i h a b y = ∑' m : Fin (Module.finrank ℝ E) → ℤ,
      ((D.R i h a b (y + Work.Diff.STE.iVec m) : ℝ) : ℂ) := rfl
  rw [hrepr]
  exact hpe

/-- **Smoothness and periodicity of the periodised components** of a section with smooth chart
data.  This is the regularity input of the Fourier sup bound
`Work.Diff.STE.B3.pdList_le_sqrt_CSq`. -/
private lemma Rper_contDiff_and_periodic_of_chartData
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (D.Rper i h a b) ∧ Work.Diff.STE.Periodic1 (D.Rper i h a b) := by
  set F : (Fin (Module.finrank ℝ E) → ℝ) → ℂ := fun z => ((D.R i h a b z : ℝ) : ℂ) with hFdef
  have hf : ContDiff ℝ (⊤ : ℕ∞) F := by
    have hR : ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b) :=
      Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hh i a b
    have hcomp := (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp hR
    have heq : (⇑Complex.ofRealCLM ∘ (D.R i h a b)) = F := by
      rw [hFdef]; funext z; exact Complex.ofRealCLM_apply _
    rwa [heq] at hcomp
  have hsupp : Function.support F ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro z hz
    exact D.R_support i h a b
      (by simpa only [hFdef, Function.mem_support, Complex.ofReal_ne_zero] using hz)
  obtain ⟨hcd, hper, -⟩ := Work.Diff.STE.periodization_contDiff_periodic F hf hsupp
  have hEq : D.Rper i h a b =
      (fun x : Fin (Module.finrank ℝ E) → ℝ =>
        ∑' m : Fin (Module.finrank ℝ E) → ℤ, F (x + Work.Diff.STE.iVec m)) := rfl
  rw [hEq]
  exact ⟨hcd, hper⟩

/-- **Each component of the composite norm is dominated by the composite norm**: the inner summands
of `D.BNorm k₀ h` are nonnegative. -/
private lemma CSq_fourierCoeff_Rper_le_BNorm
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (k₀ : ℕ) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.CSq k₀ (Work.Diff.STE.fourierCoeff (D.Rper i h a b)) ≤ D.BNorm k₀ h := by
  rw [Work.Diff.STE.B3Data.BNorm]
  refine le_trans (Finset.single_le_sum (s := Finset.univ)
      (f := fun b' : Fin (Module.finrank ℝ E) =>
        Work.Diff.STE.CSq k₀ (Work.Diff.STE.fourierCoeff (D.Rper i h a b')))
      (fun b' _ => Work.Diff.STE.CSq_nonneg _ _) (Finset.mem_univ b)) ?_
  refine le_trans (Finset.single_le_sum (s := Finset.univ)
      (f := fun a' : Fin (Module.finrank ℝ E) => ∑ b' : Fin (Module.finrank ℝ E),
        Work.Diff.STE.CSq k₀ (Work.Diff.STE.fourierCoeff (D.Rper i h a' b')))
      (fun a' _ => Finset.sum_nonneg (fun b' _ => Work.Diff.STE.CSq_nonneg _ _))
      (Finset.mem_univ a)) ?_
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun i' : ι₀ => ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
      Work.Diff.STE.CSq k₀ (Work.Diff.STE.fourierCoeff (D.Rper i' h a' b')))
    (fun i' _ => Finset.sum_nonneg
      (fun a' _ => Finset.sum_nonneg (fun b' _ => Work.Diff.STE.CSq_nonneg _ _)))
    (Finset.mem_univ i)

end Main

theorem R_pdRList_jet_BNorm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k₀ m : ℕ)
    (hm : Module.finrank ℝ E + 2 * m < 2 * k₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
      (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (l : List (Fin (Module.finrank ℝ E)))
      (j : ℕ) (γ : Fin j → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
      l.length + j ≤ m → ‖z‖ ≤ 2 * D.σ i →
      ‖Work.Diff.STE.pdVec j γ (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((Work.Diff.STE.pdRList l (D.R i h a b) y : ℝ) : ℂ)) z‖
        ≤ C * Real.sqrt (D.BNorm k₀ h) := by
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) + 2 * m < 2 * k₀ := by
    simpa only [Fintype.card_fin] using hm
  obtain ⟨C₀, hC₀, hC₀b⟩ :=
    Work.Diff.STE.B3.pdList_le_sqrt_CSq (ι := Fin (Module.finrank ℝ E)) k₀ m hcard
  refine ⟨C₀, hC₀, ?_⟩
  intro h hsm i a b l j γ z hl hz
  have hlen : (List.ofFn γ ++ l).length ≤ m := by
    rw [List.length_append, List.length_ofFn]
    omega
  -- The mixed jet is the complexification of the real iterated derivative of the component.
  have hL : Work.Diff.STE.pdVec j γ (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        ((Work.Diff.STE.pdRList l (D.R i h a b) y : ℝ) : ℂ)) z
      = ((Work.Diff.STE.pdRList (List.ofFn γ ++ l) (D.R i h a b) z : ℝ) : ℂ) := by
    rw [pdVec_ofReal_pdRList γ l (D.R i h a b)]
  -- The jet of the component at `z` is the jet of its periodisation there.
  have h3 : ((Work.Diff.STE.pdRList (List.ofFn γ ++ l) (D.R i h a b) z : ℝ) : ℂ)
      = Work.Diff.STE.pdList (List.ofFn γ ++ l)
          (fun y : Fin (Module.finrank ℝ E) → ℝ => ((D.R i h a b y : ℝ) : ℂ)) z := by
    rw [pdList_ofReal_aux (List.ofFn γ ++ l) (D.R i h a b)]
  have h2 : ((Work.Diff.STE.pdRList (List.ofFn γ ++ l) (D.R i h a b) z : ℝ) : ℂ)
      = Work.Diff.STE.pdList (List.ofFn γ ++ l) (D.Rper i h a b) z :=
    h3.trans ((pdList_eventuallyEq_of_eventuallyEq
      (Rper_eventuallyEq (I := I) (M := M) D h i a b hz).symm (List.ofFn γ ++ l)).eq_of_nhds)
  have hsmR := Rper_contDiff_and_periodic_of_chartData (I := I) (M := M) D h hsm i a b
  have hbound := hC₀b (D.Rper i h a b) hsmR.1 hsmR.2 (List.ofFn γ ++ l) hlen z
  calc ‖Work.Diff.STE.pdVec j γ (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        ((Work.Diff.STE.pdRList l (D.R i h a b) y : ℝ) : ℂ)) z‖
      = ‖((Work.Diff.STE.pdRList (List.ofFn γ ++ l) (D.R i h a b) z : ℝ) : ℂ)‖ := by rw [hL]
    _ = ‖Work.Diff.STE.pdList (List.ofFn γ ++ l) (D.Rper i h a b) z‖ := by rw [h2]
    _ ≤ C₀ * Real.sqrt (Work.Diff.STE.CSq k₀
          (Work.Diff.STE.fourierCoeff (D.Rper i h a b))) := hbound
    _ ≤ C₀ * Real.sqrt (D.BNorm k₀ h) :=
        mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (CSq_fourierCoeff_Rper_le_BNorm (I := I) (M := M) D h k₀ i a b)) hC₀

end Work.Diff.STE.Lead
