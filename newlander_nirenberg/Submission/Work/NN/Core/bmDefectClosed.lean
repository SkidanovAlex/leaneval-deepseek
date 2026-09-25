import Mathlib
import Submission.Work.NN.Core.bmRow
import Submission.Work.CR.Flat.Cauchy.bmPot_dbarCoord
import Submission.Work.CR.Flat.Cauchy.bmKernel_divergence_of_eps
import Submission.Work.CR.Flat.Cauchy.integrable_bmWeight
import Submission.Work.CR.Flat.Cauchy.bmKerEps_dbarCoord_integral

namespace Work.NN.Core

open scoped NNReal ENNReal Convolution
open MeasureTheory Set Filter
open Work.CR.Flat

noncomputable section

variable {n : ℕ}

/-! ## Elementary `∂̄`-calculus lemmas -/

/-- `∂̄_j` of a constant function is zero. -/
private lemma dbarConst (j : Fin n) (c : ℂ) (z : Cn n) :
    Work.CR.Flat.dbarCoord j (fun _ : Cn n => c) z = 0 := by
  simp [Work.CR.Flat.dbarCoord]

/-- `∂̄_m χ` is differentiable wherever `χ` is twice differentiable. -/
private lemma dbarDiff {χ : Cn n → ℂ} {w : Cn n} (m : Fin n) (hχ : ContDiffAt ℝ 2 χ w) :
    DifferentiableAt ℝ (Work.CR.Flat.dbarCoord m χ) w := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ χ) w := hχ.fderiv_right (by norm_num)
  have h2 : ContDiffAt ℝ 1 (Work.CR.Flat.dbarCoord m χ) w := by
    rw [Work.CR.Flat.Polydisc.dbarCoord_eq_comp]
    exact (Work.CR.Flat.Polydisc.dbarCoordPhi m).contDiff.contDiffAt.comp w h1
  exact h2.differentiableAt (by norm_num)

/-- Additivity of `∂̄_j` for functions written as `w ↦ u w - v w`. -/
private lemma dbarSub (j : Fin n) (u v : Cn n → ℂ) (z : Cn n)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    Work.CR.Flat.dbarCoord j (fun w => u w - v w) z
      = Work.CR.Flat.dbarCoord j u z - Work.CR.Flat.dbarCoord j v z := by
  have hfd : fderiv ℝ (fun w => u w - v w) z = fderiv ℝ u z - fderiv ℝ v z := by
    rw [show (fun w => u w - v w) = u - v from rfl, fderiv_sub hu hv]
  simp only [Work.CR.Flat.dbarCoord, hfd, sub_apply]
  ring

/-- `∂̄_j` of a constant multiple: the Leibniz rule with a constant factor. -/
private lemma dbarConstMul (j : Fin n) (c : ℂ) (u : Cn n → ℂ) (z : Cn n)
    (hu : DifferentiableAt ℝ u z) :
    Work.CR.Flat.dbarCoord j (fun w => c * u w) z = c * Work.CR.Flat.dbarCoord j u z := by
  have h := Work.CR.Flat.Polydisc.dbarCoord_mul j (fun _ : Cn n => c) u z
    (differentiableAt_const c) hu
  simpa [dbarConst j c z] using h

/-- `∂̄_j` kills an additive constant. -/
private lemma dbarSubConst (j : Fin n) (u : Cn n → ℂ) (c : ℂ) (z : Cn n)
    (hu : DifferentiableAt ℝ u z) :
    Work.CR.Flat.dbarCoord j (fun w => u w - c) z = Work.CR.Flat.dbarCoord j u z := by
  rw [dbarSub j u (fun _ : Cn n => c) z hu (differentiableAt_const c), dbarConst j c z, sub_zero]

/-- `∂̄_x` of `w ↦ ∂̄_m χ w · ζ w`, with the two `∂̄`-derivatives commuted. -/
private lemma dbarDbarMul {χ ζ : Cn n → ℂ} {m x : Fin n} {w : Cn n}
    (hχ : ContDiffAt ℝ 2 χ w) (hζ : DifferentiableAt ℝ ζ w) :
    Work.CR.Flat.dbarCoord x (fun y => Work.CR.Flat.dbarCoord m χ y * ζ y) w
      = Work.CR.Flat.dbarCoord m (Work.CR.Flat.dbarCoord x χ) w * ζ w
        + Work.CR.Flat.dbarCoord m χ w * Work.CR.Flat.dbarCoord x ζ w := by
  rw [Work.CR.Flat.Polydisc.dbarCoord_mul x (Work.CR.Flat.dbarCoord m χ) ζ w
      (dbarDiff m hχ) hζ,
    Work.CR.Flat.Polydisc.dbarCoord_comm x m χ w hχ]

/-- `∂̄_m χ` is smooth when `χ` is. -/
private lemma contDiff_dbarCoord {χ : Cn n → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (m : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.CR.Flat.dbarCoord m χ) := by
  rw [Work.CR.Flat.Polydisc.dbarCoord_eq_comp]
  exact (Work.CR.Flat.Polydisc.dbarCoordPhi m).contDiff.comp (hχ.fderiv_right (by simp))

/-- `∂̄` of a translate of a function: differentiating `y ↦ f (z + y)` at `x` is the same as
differentiating `f` at `z + x`. -/
private lemma dbarCoord_comp_add' (k : Fin n) {f : (Fin n → ℂ) → ℂ} {z x : Fin n → ℂ}
    (hf : DifferentiableAt ℝ f (z + x)) :
    Work.CR.Flat.dbarCoord k (fun y => f (z + y)) x = Work.CR.Flat.dbarCoord k f (z + x) := by
  have hshift : HasFDerivAt (fun y : Fin n → ℂ => z + y)
      (ContinuousLinearMap.id ℝ (Fin n → ℂ)) x :=
    (hasFDerivAt_id x).const_add z
  have h := (hf.hasFDerivAt).comp x hshift
  simp only [Function.comp_def] at h
  rw [Work.CR.Flat.dbarCoord, Work.CR.Flat.dbarCoord, h.fderiv, ContinuousLinearMap.comp_id]

/-! ## Support lemmas -/

/-- A compactly supported function vanishes outside some closed ball of positive radius. -/
private lemma exists_radius_of_hasCompactSupport {g : (Fin n → ℂ) → ℂ}
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

/-- The Bochner–Martinelli potential of `C¹` data vanishing outside a ball is differentiable. -/
private lemma differentiableAt_bmPot (hn : 0 < n) {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiff ℝ 1 (f j)) {R : ℝ} (hsupp : ∀ j x, R ≤ ‖x‖ → f j x = 0)
    (z : Fin n → ℂ) : DifferentiableAt ℝ (Work.CR.Flat.Cauchy.bmPot f) z := by
  have hcs : ∀ j, HasCompactSupport (f j) :=
    fun j => Work.CR.Flat.Cauchy.bmPotDbar_hasCompactSupport_of_norm (hsupp j)
  have hbmPot : Work.CR.Flat.Cauchy.bmPot f =
      fun w => -∑ k, (Work.CR.Flat.Cauchy.bmKernel k ⋆[ContinuousLinearMap.mul ℝ ℂ, volume]
        f k) w := by
    funext w
    rw [← Work.CR.Flat.Cauchy.bmPotential_eq_bmPot f w]
    exact congrFun (Work.CR.Flat.Cauchy.bmPotential_eq_neg_conv f) w
  rw [hbmPot]
  have hsum : HasFDerivAt
      (fun w => ∑ k, (Work.CR.Flat.Cauchy.bmKernel k ⋆[ContinuousLinearMap.mul ℝ ℂ, volume]
        f k) w)
      (∑ k, (Work.CR.Flat.Cauchy.bmKernel k ⋆[ContinuousLinearMap.precompR (Fin n → ℂ)
        (ContinuousLinearMap.mul ℝ ℂ), volume] fderiv ℝ (f k)) z) z := by
    have h := HasFDerivAt.sum (u := Finset.univ) fun k _ =>
      HasCompactSupport.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
        (hcs k) (Work.CR.Flat.Cauchy.locallyIntegrable_bmKernel hn k) (hf k) z
    have hfun : (∑ k, (Work.CR.Flat.Cauchy.bmKernel k ⋆[ContinuousLinearMap.mul ℝ ℂ, volume]
        f k))
        = fun w => ∑ k, (Work.CR.Flat.Cauchy.bmKernel k ⋆[ContinuousLinearMap.mul ℝ ℂ, volume]
            f k) w := by
      funext w
      rw [Finset.sum_apply]
    rw [hfun] at h
    exact h
  exact hsum.neg.differentiableAt

/-- Integrability of `x ↦ bmKernel k x · ∂̄_i g (z + x)` for `g` of class `C¹` vanishing outside the
ball of radius `R` about the origin. -/
private lemma integrable_bmKernel_mul_dbarCoord_comp_add (hn : 0 < n) (i k : Fin n)
    {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ 1 g) {R : ℝ}
    (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0) (z : Fin n → ℂ) :
    Integrable (fun x : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel k x
      * Work.CR.Flat.dbarCoord i g (z + x)) := by
  have hcont : Continuous (fun x : Fin n → ℂ => Work.CR.Flat.dbarCoord i g (z + x)) :=
    (Work.CR.Flat.Cauchy.continuous_dbarCoord hg i).comp (continuous_const.add continuous_id)
  have hvan : ∀ x : Fin n → ℂ, R + ‖z‖ + 1 ≤ ‖x‖ →
      Work.CR.Flat.dbarCoord i g (z + x) = 0 := by
    intro x hx
    refine Work.CR.Flat.Cauchy.dbarCoord_eq_zero_of_lt_norm hsupp i ?_
    have h1 : ‖x‖ ≤ ‖z + x‖ + ‖z‖ := by
      calc ‖x‖ = ‖(z + x) - z‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖z + x‖ + ‖z‖ := norm_sub_le _ _
    linarith
  have hcs : HasCompactSupport (fun x : Fin n → ℂ => Work.CR.Flat.dbarCoord i g (z + x)) :=
    Work.CR.Flat.Cauchy.bmPotDbar_hasCompactSupport_of_norm hvan
  have h := (Work.CR.Flat.Cauchy.locallyIntegrable_bmKernel hn k)
    |>.integrable_smul_left_of_hasCompactSupport hcont hcs
  simpa only [smul_eq_mul, mul_comm] using h

/-! ## The pointwise algebra identity for the `(0,3)`-combination of `bmH` -/

/-- **Pointwise algebra identity behind `bmDefectClosed`.**  With
`bmH χ η j k l w = ∂̄_l χ w · η_{jk} w + ∂̄_j χ w · η_{kl} w - ∂̄_k χ w · η_{jl} w`, for `χ` of class
`C^∞` and `η` of class `C¹`, antisymmetric and `∂̄`-closed, the three-term `(0,3)`-combination of
`bmH` equals the `∂̄` of the three-term `(0,3)`-combination of `∂̄χ` against `η`. -/
private theorem bmHCombination {χ : Cn n → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {η : Fin n → Fin n → Cn n → ℂ} (hη : ∀ i l, ContDiff ℝ 1 (η i l))
    (_hanti : ∀ i l z, η i l z = -η l i z)
    (hclosed : ∀ i l m z, Work.CR.Flat.dbarCoord i (η l m) z
      - Work.CR.Flat.dbarCoord l (η i m) z + Work.CR.Flat.dbarCoord m (η i l) z = 0)
    (a b c l : Fin n) (w : Cn n) :
    Work.CR.Flat.dbarCoord a (bmH χ η b c l) w
        - Work.CR.Flat.dbarCoord b (bmH χ η a c l) w
        + Work.CR.Flat.dbarCoord c (bmH χ η a b l) w
      = Work.CR.Flat.dbarCoord l (fun y => Work.CR.Flat.dbarCoord a χ y * η b c y
          - Work.CR.Flat.dbarCoord b χ y * η a c y
          + Work.CR.Flat.dbarCoord c χ y * η a b y) w := by
  have hχ2 : ContDiffAt ℝ 2 χ w := hχ.contDiffAt.of_le (by simp)
  have hd : ∀ m : Fin n, DifferentiableAt ℝ (Work.CR.Flat.dbarCoord m χ) w :=
    fun m => dbarDiff m hχ2
  have hηd : ∀ i l : Fin n, DifferentiableAt ℝ (η i l) w :=
    fun i l => ((hη i l).differentiable one_ne_zero).differentiableAt
  have hcl : ∀ m x : Fin n,
      Work.CR.Flat.dbarCoord x (Work.CR.Flat.dbarCoord m χ) w
        = Work.CR.Flat.dbarCoord m (Work.CR.Flat.dbarCoord x χ) w :=
    fun m x => Work.CR.Flat.Polydisc.dbarCoord_comm m x χ w hχ2
  unfold bmH
  rw [dbarSub a (fun y => Work.CR.Flat.dbarCoord l χ y * η b c y
          + Work.CR.Flat.dbarCoord b χ y * η c l y)
        (fun y => Work.CR.Flat.dbarCoord c χ y * η b l y) w
        ((hd l).mul (hηd b c) |>.add ((hd b).mul (hηd c l))) ((hd c).mul (hηd b l)),
      Work.CR.Flat.Polydisc.dbarCoord_add a (fun y => Work.CR.Flat.dbarCoord l χ y * η b c y)
        (fun y => Work.CR.Flat.dbarCoord b χ y * η c l y) w
        ((hd l).mul (hηd b c)) ((hd b).mul (hηd c l)),
      dbarDbarMul hχ2 (hηd b c), dbarDbarMul hχ2 (hηd c l), dbarDbarMul hχ2 (hηd b l),
      dbarSub b (fun y => Work.CR.Flat.dbarCoord l χ y * η a c y
          + Work.CR.Flat.dbarCoord a χ y * η c l y)
        (fun y => Work.CR.Flat.dbarCoord c χ y * η a l y) w
        ((hd l).mul (hηd a c) |>.add ((hd a).mul (hηd c l))) ((hd c).mul (hηd a l)),
      Work.CR.Flat.Polydisc.dbarCoord_add b (fun y => Work.CR.Flat.dbarCoord l χ y * η a c y)
        (fun y => Work.CR.Flat.dbarCoord a χ y * η c l y) w
        ((hd l).mul (hηd a c)) ((hd a).mul (hηd c l)),
      dbarDbarMul hχ2 (hηd a c), dbarDbarMul hχ2 (hηd c l), dbarDbarMul hχ2 (hηd a l),
      dbarSub c (fun y => Work.CR.Flat.dbarCoord l χ y * η a b y
          + Work.CR.Flat.dbarCoord a χ y * η b l y)
        (fun y => Work.CR.Flat.dbarCoord b χ y * η a l y) w
        ((hd l).mul (hηd a b) |>.add ((hd a).mul (hηd b l))) ((hd b).mul (hηd a l)),
      Work.CR.Flat.Polydisc.dbarCoord_add c (fun y => Work.CR.Flat.dbarCoord l χ y * η a b y)
        (fun y => Work.CR.Flat.dbarCoord a χ y * η b l y) w
        ((hd l).mul (hηd a b)) ((hd a).mul (hηd b l)),
      dbarDbarMul hχ2 (hηd a b), dbarDbarMul hχ2 (hηd b l), dbarDbarMul hχ2 (hηd a l),
      Work.CR.Flat.Polydisc.dbarCoord_add l
        (fun y => Work.CR.Flat.dbarCoord a χ y * η b c y - Work.CR.Flat.dbarCoord b χ y * η a c y)
        (fun y => Work.CR.Flat.dbarCoord c χ y * η a b y) w
        (((hd a).mul (hηd b c)).sub ((hd b).mul (hηd a c))) ((hd c).mul (hηd a b)),
      dbarSub l (fun y => Work.CR.Flat.dbarCoord a χ y * η b c y)
        (fun y => Work.CR.Flat.dbarCoord b χ y * η a c y) w
        ((hd a).mul (hηd b c)) ((hd b).mul (hηd a c)),
      dbarDbarMul hχ2 (hηd b c), dbarDbarMul hχ2 (hηd a c), dbarDbarMul hχ2 (hηd a b)]
  linear_combination
    (η b c w) * hcl a l - (η a c w) * hcl b l + (η a b w) * hcl c l
    + (η c l w) * hcl a b - (η b l w) * hcl a c + (η a l w) * hcl b c
    + (Work.CR.Flat.dbarCoord l χ w) * hclosed a b c w
    + (Work.CR.Flat.dbarCoord b χ w) * hclosed a c l w
    - (Work.CR.Flat.dbarCoord c χ w) * hclosed a b l w
    - (Work.CR.Flat.dbarCoord a χ w) * hclosed b c l w

/-! ## The Bochner–Martinelli divergence formula for a translate -/

/-- **The Bochner–Martinelli divergence formula for a translate.**  For `n > 0`, a `C¹` function
`g` on `ℂⁿ` with compact support and any `z : ℂⁿ`,
`Σ_m ∫ x, bmKernel m x · ∂̄_m g (z + x) dx = bmGamma n · g z`. -/
private theorem bmDivergenceCompAdd (hn : 0 < n) {g : (Fin n → ℂ) → ℂ}
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
  have hk := Work.CR.Flat.Cauchy.bmKernel_divergence_of_eps (n := n) hn
    (R := R + ‖z‖) (by positivity) hφ hφs
    (Work.CR.Flat.Cauchy.integrable_bmWeight hn).1
    (fun ε hε => Work.CR.Flat.Cauchy.bmKerEps_dbarCoord_integral (ε := ε) hn (by positivity)
      hφ hφs hε)
  have hk' : (∑ m : Fin n, ∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel m x
        * Work.CR.Flat.dbarCoord m (fun y => g (z + y)) x)
      = Work.CR.Flat.Cauchy.bmGamma n * g z := by
    simpa using hk
  rw [← hk']
  refine Finset.sum_congr rfl fun m _ => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [dbarCoord_comp_add' m (f := g) (z := z) (x := x)
    ((hg.differentiable one_ne_zero).differentiableAt)]

/-! ## The main theorem -/

/-- The Bochner–Martinelli defect of a closed `(0,2)`-form is closed.  With
`bmDefect χ η j k = (χ-1)·η_{jk} - γ⁻¹ bmPot (bmH χ η j k ·)` (`Work.NN.Core.bmRow`,
`γ = Work.CR.Flat.Cauchy.bmGamma n`), for `χ` smooth with compact support and `η` antisymmetric,
globally `C¹` and globally `∂̄`-closed, one has
`∂̄_a (bmDefect χ η)_{bc} - ∂̄_b (bmDefect χ η)_{ac} + ∂̄_c (bmDefect χ η)_{ab} = 0`.
Proof: differentiate the potential under the integral sign (`Work.CR.Flat.Cauchy.bmPot_dbarCoord`),
expand the resulting `(0,3)`-combination of `bmH χ η` using commutation of the `∂̄`-derivatives of
the smooth `χ` and closedness/antisymmetry of `η`, obtaining `∂̄_l(∂̄χ ∧ η)_{abc}`, then apply the
Bochner–Martinelli divergence identity `Work.CR.Flat.Cauchy.bmKernel_divergence_of_eps`. -/
theorem bmDefectClosed {n : ℕ} (hn : 0 < n) {χ : Work.NN.Core.Cn n → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχcs : HasCompactSupport χ)
    {η : Fin n → Fin n → Work.NN.Core.Cn n → ℂ} (hη : ∀ i l, ContDiff ℝ 1 (η i l))
    (hanti : ∀ i l z, η i l z = -η l i z)
    (hclosed : ∀ i l m z, Work.CR.Flat.dbarCoord i (η l m) z
      - Work.CR.Flat.dbarCoord l (η i m) z + Work.CR.Flat.dbarCoord m (η i l) z = 0) :
    ∀ a b c (z : Work.NN.Core.Cn n),
      Work.CR.Flat.dbarCoord a (Work.NN.Core.bmDefect χ η b c) z
        - Work.CR.Flat.dbarCoord b (Work.NN.Core.bmDefect χ η a c) z
        + Work.CR.Flat.dbarCoord c (Work.NN.Core.bmDefect χ η a b) z = 0 := by
  intro a b c z
  obtain ⟨R, hRpos, hRχ⟩ := exists_radius_of_hasCompactSupport hχcs
  set R' : ℝ := R + 1 with hR'def
  have hR'pos : 0 < R' := by rw [hR'def]; linarith
  have hdbar0 : ∀ m : Fin n, ∀ x : Cn n, R' ≤ ‖x‖ → Work.CR.Flat.dbarCoord m χ x = 0 := by
    intro m x hx
    refine Work.CR.Flat.Cauchy.dbarCoord_eq_zero_of_lt_norm hRχ m ?_
    rw [hR'def] at hx
    linarith
  have hχdbar : ∀ m : Fin n, ContDiff ℝ (⊤ : ℕ∞) (Work.CR.Flat.dbarCoord m χ) :=
    fun m => contDiff_dbarCoord hχ m
  have hχd : DifferentiableAt ℝ χ z := (hχ.differentiable (by simp)).differentiableAt
  have hηd : ∀ i l : Fin n, DifferentiableAt ℝ (η i l) z :=
    fun i l => ((hη i l).differentiable one_ne_zero).differentiableAt
  have hHcd : ∀ (j k l : Fin n), ContDiff ℝ 1 (bmH χ η j k l) := by
    intro j k l
    unfold bmH
    exact ((((hχdbar l).of_le (by simp)).mul (hη j k)).add
      (((hχdbar j).of_le (by simp)).mul (hη k l))).sub
        (((hχdbar k).of_le (by simp)).mul (hη j l))
  have hHvan : ∀ (j k l : Fin n), ∀ x : Cn n, R' ≤ ‖x‖ → bmH χ η j k l x = 0 := by
    intro j k l x hx
    simp only [bmH]
    rw [hdbar0 l x hx, hdbar0 j x hx, hdbar0 k x hx]
    ring
  set K : Cn n → ℂ := fun y => Work.CR.Flat.dbarCoord a χ y * η b c y
      - Work.CR.Flat.dbarCoord b χ y * η a c y
      + Work.CR.Flat.dbarCoord c χ y * η a b y with hK
  have hKcd : ContDiff ℝ 1 K := by
    rw [hK]
    exact ((((hχdbar a).of_le (by simp)).mul (hη b c)).sub
      (((hχdbar b).of_le (by simp)).mul (hη a c))).add
        (((hχdbar c).of_le (by simp)).mul (hη a b))
  have hKvan : ∀ x : Cn n, R' ≤ ‖x‖ → K x = 0 := by
    intro x hx
    simp only [hK]
    rw [hdbar0 a x hx, hdbar0 b x hx, hdbar0 c x hx]
    ring
  have hKcs : HasCompactSupport K :=
    Work.CR.Flat.Cauchy.bmPotDbar_hasCompactSupport_of_norm hKvan
  -- the three terms of the potential part
  have hD : Work.CR.Flat.dbarCoord a (Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ η b c l)) z
      - Work.CR.Flat.dbarCoord b (Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ η a c l)) z
      + Work.CR.Flat.dbarCoord c (Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ η a b l)) z
      = Work.CR.Flat.Cauchy.bmGamma n * K z := by
    have hA := Work.CR.Flat.Cauchy.bmPot_dbarCoord (n := n) hn (f := fun l => bmH χ η b c l)
      (fun l => hHcd b c l) hR'pos (fun l x hx => hHvan b c l x hx) a z
    have hB := Work.CR.Flat.Cauchy.bmPot_dbarCoord (n := n) hn (f := fun l => bmH χ η a c l)
      (fun l => hHcd a c l) hR'pos (fun l x hx => hHvan a c l x hx) b z
    have hC := Work.CR.Flat.Cauchy.bmPot_dbarCoord (n := n) hn (f := fun l => bmH χ η a b l)
      (fun l => hHcd a b l) hR'pos (fun l x hx => hHvan a b l x hx) c z
    rw [hA, hB, hC, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    have hterm : ∀ l : Fin n,
        (∫ x, Work.CR.Flat.Cauchy.bmKernel l x
            * Work.CR.Flat.dbarCoord a (bmH χ η b c l) (z + x))
          - (∫ x, Work.CR.Flat.Cauchy.bmKernel l x
            * Work.CR.Flat.dbarCoord b (bmH χ η a c l) (z + x))
          + (∫ x, Work.CR.Flat.Cauchy.bmKernel l x
            * Work.CR.Flat.dbarCoord c (bmH χ η a b l) (z + x))
        = ∫ x, Work.CR.Flat.Cauchy.bmKernel l x * Work.CR.Flat.dbarCoord l K (z + x) := by
      intro l
      have h1 : Integrable (fun x : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel l x
          * Work.CR.Flat.dbarCoord a (bmH χ η b c l) (z + x)) :=
        integrable_bmKernel_mul_dbarCoord_comp_add hn a l (hHcd b c l) (hHvan b c l) z
      have h2 : Integrable (fun x : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel l x
          * Work.CR.Flat.dbarCoord b (bmH χ η a c l) (z + x)) :=
        integrable_bmKernel_mul_dbarCoord_comp_add hn b l (hHcd a c l) (hHvan a c l) z
      have h3 : Integrable (fun x : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel l x
          * Work.CR.Flat.dbarCoord c (bmH χ η a b l) (z + x)) :=
        integrable_bmKernel_mul_dbarCoord_comp_add hn c l (hHcd a b l) (hHvan a b l) z
      have h12 : Integrable (fun x : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel l x
          * Work.CR.Flat.dbarCoord a (bmH χ η b c l) (z + x)
          - Work.CR.Flat.Cauchy.bmKernel l x
            * Work.CR.Flat.dbarCoord b (bmH χ η a c l) (z + x)) := h1.sub h2
      rw [← integral_sub h1 h2, ← integral_add h12 h3]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      rw [hK]
      linear_combination (Work.CR.Flat.Cauchy.bmKernel l x)
        * bmHCombination hχ hη hanti hclosed a b c l (z + x)
    rw [Finset.sum_congr rfl (fun m _ => hterm m), bmDivergenceCompAdd hn hKcd hKcs z]
  -- the `(χ - 1)η` part
  have hP : Work.CR.Flat.dbarCoord a (fun y : Cn n => (χ y - 1) * η b c y) z
      - Work.CR.Flat.dbarCoord b (fun y : Cn n => (χ y - 1) * η a c y) z
      + Work.CR.Flat.dbarCoord c (fun y : Cn n => (χ y - 1) * η a b y) z = K z := by
    rw [Work.CR.Flat.Polydisc.dbarCoord_mul a (fun y : Cn n => χ y - 1) (η b c) z
          (hχd.sub (differentiableAt_const 1)) (hηd b c),
        Work.CR.Flat.Polydisc.dbarCoord_mul b (fun y : Cn n => χ y - 1) (η a c) z
          (hχd.sub (differentiableAt_const 1)) (hηd a c),
        Work.CR.Flat.Polydisc.dbarCoord_mul c (fun y : Cn n => χ y - 1) (η a b) z
          (hχd.sub (differentiableAt_const 1)) (hηd a b),
        dbarSubConst a χ 1 z hχd, dbarSubConst b χ 1 z hχd, dbarSubConst c χ 1 z hχd]
    rw [hK]
    linear_combination (χ z - 1) * hclosed a b c z
  -- expansion of the defect
  have hDef : ∀ (i j k : Fin n),
      Work.CR.Flat.dbarCoord i (bmDefect χ η j k) z
      = Work.CR.Flat.dbarCoord i (fun y : Cn n => (χ y - 1) * η j k y) z
        - ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
          * Work.CR.Flat.dbarCoord i
              (Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ η j k l)) z := by
    intro i j k
    have hP' : DifferentiableAt ℝ (fun y : Cn n => (χ y - 1) * η j k y) z :=
      (hχd.sub (differentiableAt_const 1)).mul (hηd j k)
    have hQ' : DifferentiableAt ℝ (fun y : Cn n =>
        ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
          * Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ η j k l) y) z :=
      (differentiableAt_const _).mul (differentiableAt_bmPot (R := R') hn (fun l => hHcd j k l)
        (fun l x hx => hHvan j k l x hx) z)
    have hbk : bmDefect χ η j k = fun y : Cn n => (χ y - 1) * η j k y
        - ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
          * Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ η j k l) y := by
      funext y
      simp only [Work.NN.Core.bmDefect]
    rw [hbk, dbarSub i _ _ z hP' hQ', dbarConstMul i _ _ z (differentiableAt_bmPot (R := R') hn
      (fun l => hHcd j k l) (fun l x hx => hHvan j k l x hx) z)]
  have hcomm : (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * Work.CR.Flat.Cauchy.bmGamma n = 1 :=
    inv_mul_cancel₀ (Work.CR.Flat.Cauchy.bmGamma_ne_zero_of
      (Work.CR.Flat.Cauchy.integrable_bmWeight hn).2)
  have hcomb : Work.CR.Flat.dbarCoord a (fun y : Cn n => (χ y - 1) * η b c y) z
      - Work.CR.Flat.dbarCoord b (fun y : Cn n => (χ y - 1) * η a c y) z
      + Work.CR.Flat.dbarCoord c (fun y : Cn n => (χ y - 1) * η a b y) z
      - ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
        * (Work.CR.Flat.dbarCoord a (Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ η b c l)) z
          - Work.CR.Flat.dbarCoord b (Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ η a c l)) z
          + Work.CR.Flat.dbarCoord c (Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ η a b l)) z)
      = 0 := by
    rw [hP, hD, ← mul_assoc, hcomm, one_mul, sub_self]
  rw [hDef a b c, hDef b a c, hDef c a b]
  linear_combination hcomb

end

end Work.NN.Core
