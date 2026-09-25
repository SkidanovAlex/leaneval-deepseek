import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.NN.Core.flat_dbar_twoForm_Ck
import Submission.Work.CR.Flat.Cauchy.bmPotential_iteratedFDeriv

namespace Work.NN.Final

open MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

/-! ### Auxiliary lemmas

The proof of the defect identity is the computation of
`Work.NN.Core.ck_bmPot_dbarCoord_sub` *without* the closedness hypothesis: the
`∂̄`-derivative of the row potential is taken under the integral sign
(`bmPot_dbarCoord`), and the surviving term `Σ_m ∫ bmKernel_m · ∂̄_m X_{jl}` is
evaluated with the Bochner–Martinelli formula.  The lemmas below supply that
formula in the translated form needed here, and the integrability facts needed
to split the integral of the sum.
-/

/-- A compactly supported function vanishes outside a ball of positive radius. -/
private lemma exists_radius_of_hasCompactSupport {n : ℕ} {g : (Fin n → ℂ) → ℂ}
    (hcs : HasCompactSupport g) : ∃ R : ℝ, 0 < R ∧ ∀ x, R ≤ ‖x‖ → g x = 0 := by
  have hb : Bornology.IsBounded (tsupport g) := IsCompact.isBounded hcs
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  refine ⟨max C 0 + 1, by positivity, fun x hx => ?_⟩
  by_contra hne
  have hxmem : x ∈ tsupport g := subset_tsupport g (Function.mem_support.mpr hne)
  have h1 := hC x hxmem
  have h2 : max C 0 + 1 ≤ ‖x‖ := hx
  have h3 : C ≤ max C 0 := le_max_left C 0
  linarith

/-- Integrability of `x ↦ bmKernel k x · ∂̄_i g (z + x)` for `g` of class `C¹` vanishing off the
ball of radius `R`. -/
private lemma integrable_bmKernel_mul_dbarCoord_comp_add {n : ℕ} (hn : 0 < n) (i k : Fin n)
    {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ 1 g) {R : ℝ}
    (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0) (z : Fin n → ℂ) :
    Integrable (fun x : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel k x
      * Work.CR.Flat.dbarCoord i g (z + x)) := by
  have hφ : ContDiff ℝ 1 (fun y : Fin n → ℂ => g (z + y)) :=
    hg.comp (contDiff_const.add contDiff_id)
  have hφs : ∀ x : Fin n → ℂ, R + ‖z‖ ≤ ‖x‖ → g (z + x) = 0 := by
    intro x hx
    refine hsupp (z + x) ?_
    have h1 : ‖x‖ ≤ ‖z + x‖ + ‖z‖ := by
      calc ‖x‖ = ‖(z + x) - z‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖z + x‖ + ‖z‖ := norm_sub_le _ _
    linarith
  refine (Work.CR.Flat.Cauchy.bmCz.integrable_bmKernel_mul_dbarCoord_gen hn i k
    (Work.CR.Flat.Cauchy.continuous_dbarCoord hφ i)
    (Work.CR.Flat.Cauchy.hasCompactSupport_dbarCoord hφs i)).congr
    (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [Work.CR.Flat.Cauchy.dbarCoord_comp_add (k := i) (f := g) (z := z) (x := x)
    ((hg.differentiable one_ne_zero).differentiableAt)]

/-- **The Bochner–Martinelli divergence formula, translated.**  For a `C¹` compactly supported
function `g` and any `z`, `Σ_m ∫ bmKernel_m x · ∂̄_m g (z+x) dx = bmGamma n · g z`. -/
private lemma bmKernel_divergence_comp_add {n : ℕ} (hn : 0 < n) {g : (Fin n → ℂ) → ℂ}
    (hg : ContDiff ℝ 1 g) (hcs : HasCompactSupport g) (z : Fin n → ℂ) :
    (∑ m : Fin n, ∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel m x
        * Work.CR.Flat.dbarCoord m g (z + x))
      = Work.CR.Flat.Cauchy.bmGamma n * g z := by
  obtain ⟨R, hR, hsupp⟩ := exists_radius_of_hasCompactSupport hcs
  have hφ : ContDiff ℝ 1 (fun y : Fin n → ℂ => g (z + y)) :=
    hg.comp (contDiff_const.add contDiff_id)
  have hφs : ∀ x : Fin n → ℂ, R + ‖z‖ ≤ ‖x‖ → g (z + x) = 0 := by
    intro x hx
    refine hsupp (z + x) ?_
    have h1 : ‖x‖ ≤ ‖z + x‖ + ‖z‖ := by
      calc ‖x‖ = ‖(z + x) - z‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖z + x‖ + ‖z‖ := norm_sub_le _ _
    linarith
  have hk := Work.CR.Flat.Cauchy.bmKernel_divergence_of_eps hn
    (by positivity : (0 : ℝ) < R + ‖z‖) hφ hφs
    (Work.CR.Flat.Cauchy.integrable_bmWeight hn).1
    (fun ε hε => Work.CR.Flat.Cauchy.bmKerEps_dbarCoord_integral (ε := ε) hn
      (by positivity : (0 : ℝ) < R + ‖z‖) hφ hφs hε)
  have hk' : (∑ m : Fin n, ∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel m x
        * Work.CR.Flat.dbarCoord m (fun y => g (z + y)) x)
      = Work.CR.Flat.Cauchy.bmGamma n * g z := by
    simpa using hk
  rw [← hk']
  refine Finset.sum_congr rfl fun m _ => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [Work.CR.Flat.Cauchy.dbarCoord_comp_add (k := m) (f := g) (z := z) (x := x)
    ((hg.differentiable one_ne_zero).differentiableAt)]

/-! ### The main theorem -/

/-- **Bochner–Martinelli defect identity for `(0,2)`-forms.**  Let `X` be a smooth `(0,2)`-form on `ℂⁿ` (all components of class `C¹`, compactly supported) and let `bmPot` be the Bochner–Martinelli row potential.  Then

  `∂̄_j (bmPot (X_{l·})) − ∂̄_l (bmPot (X_{j·})) = Σ_m ∫ bmKernel_m(x) · (∂̄_j X_{lm} − ∂̄_l X_{jm} + ∂̄_m X_{jl})(z+x) dx − γ · X_{jl}(z)`,

where `γ = bmGamma n`.  For *closed* `X` the integral term vanishes and this is the classical identity `∂̄_j (bmPot X_{l·}) − ∂̄_l (bmPot X_{j·}) = -γ X_{jl}`, proved privately inside `Submission/Work/NN/Core/flat_dbar_twoForm_Ck.lean` (`ck_bmPot_dbarCoord_sub`); the proof of the present statement is that computation *without* the closedness hypothesis, plus the observation that the resulting defect term is the stated integral of `∂̄X`. -/
theorem bmDefectTwo {n : ℕ} (hn : 0 < n) {X : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hX : ∀ j l, ContDiff ℝ 1 (X j l)) (hcs : ∀ j l, HasCompactSupport (X j l))
    (j l : Fin n) (z : Fin n → ℂ) :
    Work.CR.Flat.dbarCoord j (fun y => Work.CR.Flat.Cauchy.bmPot (fun m => X l m) y) z
      - Work.CR.Flat.dbarCoord l (fun y => Work.CR.Flat.Cauchy.bmPot (fun m => X j m) y) z
      = (∑ m : Fin n, ∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel m x *
            (Work.CR.Flat.dbarCoord j (X l m) (z + x) - Work.CR.Flat.dbarCoord l (X j m) (z + x)
              + Work.CR.Flat.dbarCoord m (X j l) (z + x)))
        - Work.CR.Flat.Cauchy.bmGamma n * X j l z := by
  -- a single radius outside which all the components `X_{ik}` vanish
  have hRex : ∀ i k : Fin n, ∃ R : ℝ, 0 < R ∧ ∀ x, R ≤ ‖x‖ → X i k x = 0 :=
    fun i k => exists_radius_of_hasCompactSupport (hcs i k)
  choose R hRpos hRsupp using hRex
  set r : ℝ := (∑ i : Fin n, ∑ k : Fin n, R i k) + 1 with hr
  have hrpos : 0 < r := by
    rw [hr]
    have h : 0 ≤ ∑ i : Fin n, ∑ k : Fin n, R i k :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => le_of_lt (hRpos i k)
    linarith
  have hRle : ∀ i k : Fin n, R i k ≤ r := by
    intro i k
    have h1 : R i k ≤ ∑ k' : Fin n, R i k' :=
      Finset.single_le_sum (fun b _ => le_of_lt (hRpos i b)) (Finset.mem_univ k)
    have h2 : (∑ k' : Fin n, R i k') ≤ ∑ i' : Fin n, ∑ k' : Fin n, R i' k' :=
      Finset.single_le_sum (fun b _ => Finset.sum_nonneg fun b' _ => le_of_lt (hRpos b b'))
        (Finset.mem_univ i)
    rw [hr]
    linarith
  have hsupp : ∀ i k : Fin n, ∀ x : Fin n → ℂ, r ≤ ‖x‖ → X i k x = 0 :=
    fun i k x hx => hRsupp i k x (le_trans (hRle i k) hx)
  -- the `∂̄`-derivatives of the two row potentials
  have hA := Work.CR.Flat.Cauchy.bmPot_dbarCoord hn (f := fun m => X l m)
    (fun m => hX l m) hrpos (fun m x hx => hsupp l m x hx) j z
  have hB := Work.CR.Flat.Cauchy.bmPot_dbarCoord hn (f := fun m => X j m)
    (fun m => hX j m) hrpos (fun m x hx => hsupp j m x hx) l z
  -- the Bochner–Martinelli formula for the remaining component `X_{jl}`
  have hD := bmKernel_divergence_comp_add hn (hX j l) (hcs j l) z
  -- integrability of the three pieces
  have hI1 : ∀ m : Fin n, Integrable (fun x : Fin n → ℂ =>
      Work.CR.Flat.Cauchy.bmKernel m x * Work.CR.Flat.dbarCoord j (X l m) (z + x)) :=
    fun m => integrable_bmKernel_mul_dbarCoord_comp_add hn j m (hX l m)
      (fun x hx => hsupp l m x hx) z
  have hI2 : ∀ m : Fin n, Integrable (fun x : Fin n → ℂ =>
      Work.CR.Flat.Cauchy.bmKernel m x * Work.CR.Flat.dbarCoord l (X j m) (z + x)) :=
    fun m => integrable_bmKernel_mul_dbarCoord_comp_add hn l m (hX j m)
      (fun x hx => hsupp j m x hx) z
  have hI3 : ∀ m : Fin n, Integrable (fun x : Fin n → ℂ =>
      Work.CR.Flat.Cauchy.bmKernel m x * Work.CR.Flat.dbarCoord m (X j l) (z + x)) :=
    fun m => integrable_bmKernel_mul_dbarCoord_comp_add hn m m (hX j l)
      (fun x hx => hsupp j l x hx) z
  rw [hA, hB, ← hD]
  have hsplit : ∀ m : Fin n,
      (∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel m x *
        (Work.CR.Flat.dbarCoord j (X l m) (z + x) - Work.CR.Flat.dbarCoord l (X j m) (z + x)
          + Work.CR.Flat.dbarCoord m (X j l) (z + x)))
      = (∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel m x
            * Work.CR.Flat.dbarCoord j (X l m) (z + x))
        - (∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel m x
            * Work.CR.Flat.dbarCoord l (X j m) (z + x))
        + (∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel m x
            * Work.CR.Flat.dbarCoord m (X j l) (z + x)) := by
    intro m
    have h1 : (∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel m x *
        (Work.CR.Flat.dbarCoord j (X l m) (z + x) - Work.CR.Flat.dbarCoord l (X j m) (z + x)
          + Work.CR.Flat.dbarCoord m (X j l) (z + x)))
        = ∫ x : Fin n → ℂ, (Work.CR.Flat.Cauchy.bmKernel m x
              * Work.CR.Flat.dbarCoord j (X l m) (z + x)
            - Work.CR.Flat.Cauchy.bmKernel m x * Work.CR.Flat.dbarCoord l (X j m) (z + x))
          + Work.CR.Flat.Cauchy.bmKernel m x * Work.CR.Flat.dbarCoord m (X j l) (z + x) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [h1, integral_add
        (f := fun x : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel m x
            * Work.CR.Flat.dbarCoord j (X l m) (z + x)
          - Work.CR.Flat.Cauchy.bmKernel m x * Work.CR.Flat.dbarCoord l (X j m) (z + x))
        (g := fun x : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel m x
            * Work.CR.Flat.dbarCoord m (X j l) (z + x))
        ((hI1 m).sub (hI2 m)) (hI3 m),
      integral_sub (hI1 m) (hI2 m)]
  rw [Finset.sum_congr rfl (fun m _ => hsplit m), Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

end

end Work.NN.Final
