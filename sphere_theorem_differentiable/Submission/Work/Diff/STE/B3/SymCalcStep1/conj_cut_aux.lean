import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.SymCalc
import Submission.Work.Diff.STE.B3.pdVecMulCompExpansion
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.B3.integral_pd_comp_le
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.fourierCoeff_mul_seriesFun
import Submission.Work.Diff.STE.fourierCoeff_pd
import Submission.Work.Diff.STE.pd_seriesFun
import Submission.Work.Diff.STE.B3.SymCalcStep1.conv_CSq_le
import Submission.Work.Diff.STE.B3.SymCalcStep1.firstOrder_comm_le_cplx
import Submission.Work.Diff.STE.B3.SymCalcStep1.mul_pd_CSq_le
import Submission.Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_comp_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Work.Diff.STE.B3.SymCalcStep1

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The conjugation of the flat Laplacian along `T`

`conjCut ρ ε T T' g = comp_{T'} (S_ε (comp_T g))` with `S_ε = flatCut ρ ε`.  The exact
conjugation identity

`lapC ∘ conjCut = comp_{T'} ∘ P ∘ S_ε ∘ comp_T`,

with `P = comp_T ∘ lapC ∘ comp_{T'}` the flat Laplacian written in the `T`-coordinates, is the
starting point of the estimate: the commutator `[lapC, conjCut]` is `comp_{T'}([P,S_ε](comp_T g))`
and `[P,S_ε]` is one order lower than `P ∘ S_ε` because the top symbol of `P` is scalar.

The file below makes `P` explicit.  Writing `L = Σᵢ ∂ᵢ∂ᵢ` one has `P = Σᵢ Qᵢ ∘ Qᵢ` with

`Qᵢ = comp_T ∘ ∂ᵢ ∘ comp_{T'}`,  `(Qᵢ v)(y) = ∂ᵢ(v ∘ T')(T y) = Σ_p Mᵢₚ(y) · ∂_p v(y)`,

`Mᵢₚ` being the `p`-th component of `fderiv T' (T y) (eᵢ)` — a `1`-periodic `C^∞` function.  So
`P` is a second order operator with periodic coefficients and no zeroth order term, and
`[P,S_ε] = Σᵢ (Qᵢ [Qᵢ,S_ε] + [Qᵢ,S_ε] Qᵢ)`, a sum of terms each of which is bounded
`H^{s+1} → H^s` uniformly in `ε`: the commutator `[Qᵢ,S_ε]` is order `0` (PIECE 3 /
`firstOrder_comm_le_cplx`) and one factor `Qᵢ` costs exactly the one derivative that the target
allows. -/

/-- **Shift-equivariance of `T'`**, derived from `hTper` and the two inverse relations: `T'` is
`1`-periodic as a map in the sense `T' (y + eᵢ) = T' y + eᵢ`. -/
lemma shift_T' (T T' : (ι → ℝ) → (ι → ℝ))
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x)
    (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y) (i : ι) (y : ι → ℝ) :
    T' (y + Pi.single i 1) = T' y + Pi.single i 1 := by
  have h1 : T (T' (y + Pi.single i 1)) = y + Pi.single i 1 := hTinv2 _
  have h2 : T (T' y + Pi.single i 1) = y + Pi.single i 1 := by rw [hTper, hTinv2]
  have h3 : T' (T (T' (y + Pi.single i 1))) = T' (T (T' y + Pi.single i 1)) := by rw [h1, h2]
  rwa [hTinv1, hTinv1] at h3

/-- The derivative of a map that shifts by `e` in the argument is unchanged by the shift. -/
lemma fderiv_shift_eq {T' : (ι → ℝ) → (ι → ℝ)} (i : ι)
    (hshift : ∀ z : ι → ℝ, T' (z + Pi.single i 1) = T' z + Pi.single i 1) (z : ι → ℝ) :
    fderiv ℝ T' (z + Pi.single i 1) = fderiv ℝ T' z := by
  have hfun : (fun w : ι → ℝ => T' (w + Pi.single i 1))
      = fun w => T' w + Pi.single i 1 := funext hshift
  calc fderiv ℝ T' (z + Pi.single i 1)
      = fderiv ℝ (fun w : ι → ℝ => T' (w + Pi.single i 1)) z :=
        (fderiv_comp_add_right (𝕜 := ℝ) (f := T') (x := z) (Pi.single i 1)).symm
    _ = fderiv ℝ (fun w : ι → ℝ => T' w + Pi.single i 1) z := by rw [hfun]
    _ = fderiv ℝ T' z := fderiv_add_const (Pi.single i 1)

/-- The coefficients of the first-order operator `Qᵢ`: the `p`-th component of
`fderiv ℝ T' (T y) (eᵢ)`, a `1`-periodic `C^∞` function of `y`. -/
def Mcoef (T T' : (ι → ℝ) → (ι → ℝ)) (i p : ι) : (ι → ℝ) → ℂ :=
  fun y => (((fderiv ℝ T' (T y)) (Pi.single i 1)) p : ℂ)

/-- The first-order operator `Qᵢ = comp_T ∘ ∂ᵢ ∘ comp_{T'}`. -/
def Qop (T T' : (ι → ℝ) → (ι → ℝ)) (i : ι) (v : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  fun y => Work.Diff.STE.pd i (fun z => v (T' z)) (T y)

/-- The flat Laplacian transported to the `y = T x` coordinates. -/
def pullLap (T T' : (ι → ℝ) → (ι → ℝ)) (v : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  fun y => Work.Diff.STE.B3.SymCalc.lapC (fun x => v (T' x)) (T y)

lemma Mcoef_periodic (T T' : (ι → ℝ) → (ι → ℝ))
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x)
    (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y) (i p : ι) : Work.Diff.STE.Periodic1 (Mcoef T T' i p) := by
  intro m y
  have hshift : ∀ z : ι → ℝ, T' (z + Pi.single m 1) = T' z + Pi.single m 1 :=
    shift_T' T T' hTper hTinv1 hTinv2 m
  simp only [Mcoef]
  rw [hTper m y]
  rw [fderiv_shift_eq m hshift (T y)]

lemma Mcoef_contDiff (T T' : (ι → ℝ) → (ι → ℝ))
    (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T') (i p : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (Mcoef T T' i p) := by
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ T') := hT'.fderiv_right (by simp)
  have h1 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ι → ℝ => (fderiv ℝ T' z) (Pi.single i (1 : ℝ))) :=
    hfd.clm_apply (g := fun _ : ι → ℝ => (Pi.single i (1 : ℝ))) contDiff_const
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : ι → ℝ => ((fderiv ℝ T' (T y)) (Pi.single i (1 : ℝ))) p) := by
    have h3 : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : ι → ℝ => (fderiv ℝ T' (T y)) (Pi.single i (1 : ℝ))) := h1.comp hT
    exact ((ContinuousLinearMap.proj p : (ι → ℝ) →L[ℝ] ℝ).contDiff).comp h3
  exact Complex.ofRealCLM.contDiff.comp h2

/-- **The explicit form of `Qᵢ`** (chain rule), using `T' (T y) = y`. -/
lemma Qop_eq_sum (T T' : (ι → ℝ) → (ι → ℝ)) (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x)
    (hT' : Differentiable ℝ T') (i : ι) {v : (ι → ℝ) → ℂ} (hv : Differentiable ℝ v) (y : ι → ℝ) :
    Qop T T' i v y = ∑ p, Mcoef T T' i p y * Work.Diff.STE.pd p v y := by
  have h := congrFun (Work.Diff.STE.B3.pdMulComp_pd_comp_eq (T := T') hT' i hv) (T y)
  simpa only [Qop, Mcoef, hTinv1 y] using h

lemma Qop_sub (T T' : (ι → ℝ) → (ι → ℝ)) (hT' : Differentiable ℝ T') (i : ι)
    {v w : (ι → ℝ) → ℂ} (hv : Differentiable ℝ v) (hw : Differentiable ℝ w) :
    Qop T T' i (v - w) = Qop T T' i v - Qop T T' i w := by
  funext y
  simp only [Qop, Pi.sub_apply]
  have hfun : (fun z : ι → ℝ => v (T' z) - w (T' z))
      = (fun z => v (T' z)) - (fun z => w (T' z)) := rfl
  rw [hfun, Work.Diff.STE.pd,
    fderiv_sub (f := fun z : ι → ℝ => v (T' z)) (g := fun z : ι → ℝ => w (T' z))
      (x := T y) ((hv.comp hT').differentiableAt) ((hw.comp hT').differentiableAt)]
  simp only [ContinuousLinearMap.sub_apply, Work.Diff.STE.pd]

lemma Qop_add (T T' : (ι → ℝ) → (ι → ℝ)) (hT' : Differentiable ℝ T') (i : ι)
    {v w : (ι → ℝ) → ℂ} (hv : Differentiable ℝ v) (hw : Differentiable ℝ w) :
    Qop T T' i (v + w) = Qop T T' i v + Qop T T' i w := by
  funext y
  simp only [Qop, Pi.add_apply]
  have hfun : (fun z : ι → ℝ => v (T' z) + w (T' z))
      = (fun z => v (T' z)) + (fun z => w (T' z)) := rfl
  rw [hfun, Work.Diff.STE.pd,
    fderiv_add (f := fun z : ι → ℝ => v (T' z)) (g := fun z : ι → ℝ => w (T' z))
      (x := T y) ((hv.comp hT').differentiableAt) ((hw.comp hT').differentiableAt)]
  simp only [ContinuousLinearMap.add_apply, Work.Diff.STE.pd]


/-! ## `Periodic1` is stable under the pointwise operations -/

lemma Periodic1_mul' {f g : (ι → ℝ) → ℂ} (hf : Work.Diff.STE.Periodic1 f)
    (hg : Work.Diff.STE.Periodic1 g) : Work.Diff.STE.Periodic1 (f * g) :=
  fun m y => by simp only [Pi.mul_apply, hf m y, hg m y]

lemma Periodic1_sub' {f g : (ι → ℝ) → ℂ} (hf : Work.Diff.STE.Periodic1 f)
    (hg : Work.Diff.STE.Periodic1 g) : Work.Diff.STE.Periodic1 (f - g) :=
  fun m y => by simp only [Pi.sub_apply, hf m y, hg m y]

lemma Periodic1_add' {f g : (ι → ℝ) → ℂ} (hf : Work.Diff.STE.Periodic1 f)
    (hg : Work.Diff.STE.Periodic1 g) : Work.Diff.STE.Periodic1 (f + g) :=
  fun m y => by simp only [Pi.add_apply, hf m y, hg m y]

/-- The weighted `ℓ²` family of the Fourier coefficients is summable for a smooth `1`-periodic
function. -/
lemma summable_CSq_fourierCoeff (s : ℕ) {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hper : Work.Diff.STE.Periodic1 f) :
    Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖Work.Diff.STE.fourierCoeff f k‖ ^ 2) :=
  Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff f hf hper s

/-- **`P = Σᵢ Qᵢ ∘ Qᵢ`**: the conjugation identity `lapC ∘ comp_{T'} = comp_{T'} ∘ P` in the form
`P v = Σᵢ Qᵢ (Qᵢ v)`. -/
lemma pullLap_eq_sum_Qop (T T' : (ι → ℝ) → (ι → ℝ)) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (v : (ι → ℝ) → ℂ) :
    pullLap T T' v = fun y => ∑ i, Qop T T' i (Qop T T' i v) y := by
  funext y
  simp only [pullLap, Work.Diff.STE.B3.SymCalc.lapC, Qop]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  funext z
  rw [hTinv2]

/-! ## Elementary linearity of the Fourier transform and of `S_ε` -/

/-- **Linearity of `fourierCoeff` over a finite sum.** -/
lemma fourierCoeff_ftype_sum {α : Type*} [Fintype α] (F : α → (ι → ℝ) → ℂ) (k : ι → ℤ)
    (hF : ∀ i, Integrable (fun x => Work.Diff.STE.fourierExp (-k) x * F i x)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι)))) :
    Work.Diff.STE.fourierCoeff (fun x => ∑ i, F i x) k
      = ∑ i, Work.Diff.STE.fourierCoeff (F i) k := by
  simp only [Work.Diff.STE.fourierCoeff]
  have hpt : ∀ x : ι → ℝ, Work.Diff.STE.fourierExp (-k) x * (∑ i, F i x)
      = ∑ i, Work.Diff.STE.fourierExp (-k) x * F i x := fun x => Finset.mul_sum _ _ _
  rw [funext hpt, MeasureTheory.integral_finsetSum _ fun i _ => hF i]

/-- **Linearity of `fourierCoeff` over a finite sum**, for continuous summands. -/
lemma fourierCoeff_ftype_sum_of_continuous {α : Type*} [Fintype α]
    (F : α → (ι → ℝ) → ℂ) (hF : ∀ i, Continuous (F i)) (k : ι → ℤ) :
    Work.Diff.STE.fourierCoeff (fun x => ∑ i, F i x) k
      = ∑ i, Work.Diff.STE.fourierCoeff (F i) k :=
  fourierCoeff_ftype_sum F k fun i =>
    Work.Diff.STE.integrableOn_unitCube_of_continuous_cplx
      ((Work.Diff.STE.continuous_fourierExp (-k)).mul (hF i))

/-- **`seriesFun` is linear over finite sums.** -/
lemma seriesFun_fintype_sum {α : Type*} [Fintype α] (c : α → (ι → ℤ) → ℂ)
    (hc : ∀ p, Summable fun k : ι → ℤ => ‖c p k‖) (x : ι → ℝ) :
    Work.Diff.STE.seriesFun (fun k => ∑ p, c p k) x
      = ∑ p, Work.Diff.STE.seriesFun (c p) x := by
  simp only [Work.Diff.STE.seriesFun]
  have hpt : ∀ k : ι → ℤ, (∑ p, c p k) * Work.Diff.STE.fourierExp k x
      = ∑ p, c p k * Work.Diff.STE.fourierExp k x := fun k => Finset.sum_mul _ _ _
  rw [funext hpt]
  exact Summable.tsum_finsetSum
    (f := fun (p : α) (k : ι → ℤ) => c p k * Work.Diff.STE.fourierExp k x)
    (s := Finset.univ) fun p _ =>
    Summable.of_norm_bounded (hc p)
      (fun k => by rw [norm_mul, Work.Diff.STE.norm_fourierExp, mul_one])

/-- A moment of the truncated family `trunc ρ ε c` is summable whenever that moment of `c` is. -/
lemma summable_trunc_moment (ρ : (ι → ℝ) → ℝ) (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ)
    {c : (ι → ℤ) → ℂ} (N : ℕ)
    (hc : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖c k‖)) :
    Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖Work.Diff.STE.trunc ρ ε c k‖) := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) N) (norm_nonneg _))
    (fun k => ?_) hc
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) N)
  rw [Work.Diff.STE.trunc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hρb _)

/-- The truncated family is `ℓ¹` whenever the family is. -/
lemma summable_trunc_one (ρ : (ι → ℝ) → ℝ) (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ)
    {c : (ι → ℤ) → ℂ} (hc : Summable fun k : ι → ℤ => ‖c k‖) :
    Summable fun k : ι → ℤ => ‖Work.Diff.STE.trunc ρ ε c k‖ := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hc
  rw [Work.Diff.STE.trunc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hρb _)

/-- **`S_ε = flatCut ρ ε` is linear over finite sums** (of smooth `1`-periodic functions). -/
lemma flatCut_fintype_sum {α : Type*} [Fintype α] (ρ : (ι → ℝ) → ℝ)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ)
    (f : α → (ι → ℝ) → ℂ) (hf : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (f p))
    (hper : ∀ p, Work.Diff.STE.Periodic1 (f p)) :
    Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun x => ∑ p, f p x)
      = fun x => ∑ p, Work.Diff.STE.B3.SymCalc.flatCut ρ ε (f p) x := by
  have hcoeff : ∀ k : ι → ℤ,
      Work.Diff.STE.fourierCoeff (fun x => ∑ p, f p x) k
        = ∑ p, Work.Diff.STE.fourierCoeff (f p) k := fun k =>
    fourierCoeff_ftype_sum_of_continuous f (fun p => (hf p).continuous) k
  funext x
  show Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε
      (Work.Diff.STE.fourierCoeff (fun x => ∑ p, f p x))) x = _
  rw [show Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff (fun x => ∑ p, f p x))
      = Work.Diff.STE.trunc ρ ε (fun k => ∑ p, Work.Diff.STE.fourierCoeff (f p) k) from
        congrArg (Work.Diff.STE.trunc ρ ε) (funext hcoeff)]
  rw [show Work.Diff.STE.trunc ρ ε (fun k => ∑ p, Work.Diff.STE.fourierCoeff (f p) k)
      = fun k => ∑ p, Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff (f p)) k from by
        funext k
        simp only [Work.Diff.STE.trunc, Finset.mul_sum]]
  rw [seriesFun_fintype_sum _ (fun p => ?_)]
  · rfl
  · have h0 := Work.Diff.STE.summable_wt_pow_norm_fourierCoeff_of_contDiff (f p) (hf p) (hper p) 0
    simp only [pow_zero, one_mul] at h0
    exact summable_trunc_one ρ hρb ε h0

/-- **`CSq` of a finite sum of coefficient families.** -/
lemma CSq_fintype_sum_le {α : Type*} [Fintype α] (s : ℕ) (c : α → (ι → ℤ) → ℂ)
    (h : ∀ j, Summable fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ s * ‖c j m‖ ^ 2) :
    Work.Diff.STE.CSq s (fun m => ∑ j, c j m)
      ≤ (Fintype.card α : ℝ) * ∑ j, Work.Diff.STE.CSq s (c j) := by
  have hpt : ∀ m : ι → ℤ, (Work.Diff.STE.wt m) ^ s * ‖∑ j, c j m‖ ^ 2
      ≤ (Fintype.card α : ℝ) * ∑ j, (Work.Diff.STE.wt m) ^ s * ‖c j m‖ ^ 2 := by
    intro m
    have h0 : ‖∑ j, c j m‖ ≤ ∑ j, ‖c j m‖ := norm_sum_le _ _
    have h1 : (∑ j : α, ‖c j m‖) ^ 2
        ≤ (Finset.univ : Finset α).card * ∑ j, ‖c j m‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖c j m‖)
    rw [Finset.card_univ] at h1
    have h1' : ‖∑ j, c j m‖ ^ 2
        ≤ (Fintype.card α : ℝ) * ∑ j, ‖c j m‖ ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) h0 2).trans h1
    have h2 : (0 : ℝ) ≤ (Work.Diff.STE.wt m) ^ s :=
      pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) s
    have heq : (Work.Diff.STE.wt m) ^ s * ((Fintype.card α : ℝ) * ∑ j, ‖c j m‖ ^ 2)
        = (Fintype.card α : ℝ) * ∑ j, (Work.Diff.STE.wt m) ^ s * ‖c j m‖ ^ 2 := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    calc (Work.Diff.STE.wt m) ^ s * ‖∑ j, c j m‖ ^ 2
        ≤ (Work.Diff.STE.wt m) ^ s * ((Fintype.card α : ℝ) * ∑ j, ‖c j m‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1' h2
      _ = (Fintype.card α : ℝ) * ∑ j, (Work.Diff.STE.wt m) ^ s * ‖c j m‖ ^ 2 := heq
  have hsumRHS : Summable (fun m : ι → ℤ =>
      (Fintype.card α : ℝ) * ∑ j : α, (Work.Diff.STE.wt m) ^ s * ‖c j m‖ ^ 2) :=
    (summable_sum (f := fun (j : α) (m : ι → ℤ) =>
      (Work.Diff.STE.wt m) ^ s * ‖c j m‖ ^ 2) (s := (Finset.univ : Finset α))
      (fun j _ => h j)).mul_left _
  have hsumLHS : Summable (fun m : ι → ℤ =>
      (Work.Diff.STE.wt m) ^ s * ‖∑ j, c j m‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun m => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) s) (sq_nonneg _))
      hpt hsumRHS
  calc Work.Diff.STE.CSq s (fun m => ∑ j, c j m)
      = ∑' m, (Work.Diff.STE.wt m) ^ s * ‖∑ j, c j m‖ ^ 2 := rfl
    _ ≤ ∑' m, (Fintype.card α : ℝ) * ∑ j : α, (Work.Diff.STE.wt m) ^ s * ‖c j m‖ ^ 2 :=
        Summable.tsum_le_tsum hpt hsumLHS hsumRHS
    _ = (Fintype.card α : ℝ) * ∑' m, ∑ j : α, (Work.Diff.STE.wt m) ^ s * ‖c j m‖ ^ 2 :=
        tsum_mul_left
    _ = (Fintype.card α : ℝ) * ∑ j : α, ∑' m, (Work.Diff.STE.wt m) ^ s * ‖c j m‖ ^ 2 := by
        congr 1
        exact Summable.tsum_finsetSum (f := fun (j : α) (m : ι → ℤ) =>
          (Work.Diff.STE.wt m) ^ s * ‖c j m‖ ^ 2) (s := (Finset.univ : Finset α))
          (fun j _ => h j)

/-! ## `S_ε` and `Qᵢ` preserve smoothness and periodicity -/

lemma flatCut_periodic (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (g : (ι → ℝ) → ℂ) :
    Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) :=
  Work.Diff.STE.periodic_seriesFun _

lemma flatCut_contDiff (ρ : (ι → ℝ) → ℝ) (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ)
    {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hper : Work.Diff.STE.Periodic1 g) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) := by
  refine Work.Diff.STE.contDiff_seriesFun _ fun N => ?_
  exact summable_trunc_moment ρ hρb ε N
    (Work.Diff.STE.summable_wt_pow_norm_fourierCoeff_of_contDiff g hg hper N)

lemma fourierCoeff_flatCut (ρ : (ι → ℝ) → ℝ) (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ)
    {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hper : Work.Diff.STE.Periodic1 g)
    (k : ι → ℤ) :
    Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) k
      = (ρ (ε • (fun i => (k i : ℝ))) : ℂ) * Work.Diff.STE.fourierCoeff g k := by
  rw [Work.Diff.STE.B3.SymCalc.flatCut, Work.Diff.STE.flat.fourierCoeff_seriesFun _ _ k]
  · rfl
  · have h0 := Work.Diff.STE.summable_wt_pow_norm_fourierCoeff_of_contDiff g hg hper 0
    simp only [pow_zero, one_mul] at h0
    exact summable_trunc_one ρ hρb ε h0

lemma Qop_contDiff (T T' : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (hT' : ContDiff ℝ (⊤ : ℕ∞) T') (i : ι) {v : (ι → ℝ) → ℂ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) : ContDiff ℝ (⊤ : ℕ∞) (Qop T T' i v) :=
  (Work.Diff.STE.B3.pdMulComp_contDiff_pd i (hv.comp hT')).comp hT

lemma Qop_periodic (T T' : (ι → ℝ) → (ι → ℝ))
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x)
    (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (hT' : ContDiff ℝ (⊤ : ℕ∞) T') (i : ι) {v : (ι → ℝ) → ℂ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hper : Work.Diff.STE.Periodic1 v) :
    Work.Diff.STE.Periodic1 (Qop T T' i v) := by
  -- `v ∘ T'` is periodic
  have hcomp : Work.Diff.STE.Periodic1 (fun z : ι → ℝ => v (T' z)) := by
    intro m z
    show v (T' (z + Pi.single m 1)) = v (T' z)
    rw [shift_T' T T' hTper hTinv1 hTinv2 m z]
    exact hper m (T' z)
  have hdiff : Differentiable ℝ (fun z : ι → ℝ => v (T' z)) :=
    (hv.comp hT').differentiable (by simp)
  have hpd : Work.Diff.STE.Periodic1 (Work.Diff.STE.pd i (fun z : ι → ℝ => v (T' z))) :=
    Work.Diff.STE.B3.ipdcl_periodic_pd (w := fun z : ι → ℝ => v (T' z)) hcomp hdiff i
  intro m y
  show Work.Diff.STE.pd i (fun z : ι → ℝ => v (T' z)) (T (y + Pi.single m 1))
      = Work.Diff.STE.pd i (fun z : ι → ℝ => v (T' z)) (T y)
  rw [hTper m y]
  exact hpd m (T y)


/-- `CSq` of a sum of two families. -/
lemma CSq_add_le (s : ℕ) (a b : (ι → ℤ) → ℂ)
    (ha : Summable fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖a k‖ ^ 2)
    (hb : Summable fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖b k‖ ^ 2) :
    Work.Diff.STE.CSq s (fun k => a k + b k)
      ≤ 2 * (Work.Diff.STE.CSq s a + Work.Diff.STE.CSq s b) := by
  have hpt : ∀ k : ι → ℤ, (Work.Diff.STE.wt k) ^ s * ‖a k + b k‖ ^ 2
      ≤ 2 * ((Work.Diff.STE.wt k) ^ s * ‖a k‖ ^ 2 + (Work.Diff.STE.wt k) ^ s * ‖b k‖ ^ 2) := by
    intro k
    have h1 : ‖a k + b k‖ ^ 2 ≤ 2 * (‖a k‖ ^ 2 + ‖b k‖ ^ 2) := by
      have h3 : ‖a k + b k‖ ^ 2 ≤ (‖a k‖ + ‖b k‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (a k) (b k)) 2
      nlinarith [sq_nonneg (‖a k‖ - ‖b k‖), norm_nonneg (a k), norm_nonneg (b k)]
    have h2 : (0 : ℝ) ≤ (Work.Diff.STE.wt k) ^ s :=
      pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s
    calc (Work.Diff.STE.wt k) ^ s * ‖a k + b k‖ ^ 2
        ≤ (Work.Diff.STE.wt k) ^ s * (2 * (‖a k‖ ^ 2 + ‖b k‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = 2 * ((Work.Diff.STE.wt k) ^ s * ‖a k‖ ^ 2
            + (Work.Diff.STE.wt k) ^ s * ‖b k‖ ^ 2) := by ring
  have hsumR : Summable (fun k : ι → ℤ => 2 * ((Work.Diff.STE.wt k) ^ s * ‖a k‖ ^ 2
      + (Work.Diff.STE.wt k) ^ s * ‖b k‖ ^ 2)) := (ha.add hb).mul_left 2
  have hsumL : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖a k + b k‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s) (sq_nonneg _))
      hpt hsumR
  calc Work.Diff.STE.CSq s (fun k => a k + b k)
      = ∑' k, (Work.Diff.STE.wt k) ^ s * ‖a k + b k‖ ^ 2 := rfl
    _ ≤ ∑' k, 2 * ((Work.Diff.STE.wt k) ^ s * ‖a k‖ ^ 2
          + (Work.Diff.STE.wt k) ^ s * ‖b k‖ ^ 2) := Summable.tsum_le_tsum hpt hsumL hsumR
    _ = 2 * (Work.Diff.STE.CSq s a + Work.Diff.STE.CSq s b) := by
        rw [tsum_mul_left, Summable.tsum_add ha hb]
        rfl

/-- **`Qᵢ` costs one derivative** (it is a first-order operator with `1`-periodic `C^∞`
coefficients `Mᵢₚ = (fderiv T' (T ·) (eᵢ))ₚ`). -/
lemma Qop_CSq_le (T T' : (ι → ℝ) → (ι → ℝ))
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x)
    (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (i : ι) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) u →
      Work.Diff.STE.Periodic1 u →
      Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (Qop T T' i u))
        ≤ C * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff u) := by
  classical
  choose C hC using fun p : ι =>
    mul_pd_CSq_le (Mcoef T T' i p) (Mcoef_contDiff T T' hT hT' i p)
      (Mcoef_periodic T T' hTper hTinv1 hTinv2 i p) p s
  refine ⟨(Fintype.card ι : ℝ) * ∑ p, C p,
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun p _ => (hC p).1),
    fun u hu hpu => ?_⟩
  have hQ : Qop T T' i u = fun y => ∑ p, Mcoef T T' i p y * Work.Diff.STE.pd p u y :=
    funext fun y => Qop_eq_sum T T' hTinv1 (hT'.differentiable (by simp)) i (hu.differentiable (by simp)) y
  have hcoe : Work.Diff.STE.fourierCoeff (fun y => ∑ p, Mcoef T T' i p y * Work.Diff.STE.pd p u y)
      = fun k => ∑ p, Work.Diff.STE.fourierCoeff
          (fun y => Mcoef T T' i p y * Work.Diff.STE.pd p u y) k :=
    funext fun k => fourierCoeff_ftype_sum_of_continuous
      (fun p y => Mcoef T T' i p y * Work.Diff.STE.pd p u y)
      (fun p => (Mcoef_contDiff T T' hT hT' i p).continuous.mul
        (Work.Diff.STE.B3.pdMulComp_contDiff_pd p hu).continuous) k
  rw [hQ, hcoe]
  calc Work.Diff.STE.CSq s (fun k => ∑ p, Work.Diff.STE.fourierCoeff
          (fun y => Mcoef T T' i p y * Work.Diff.STE.pd p u y) k)
      ≤ (Fintype.card ι : ℝ) * ∑ p, Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
          (fun y => Mcoef T T' i p y * Work.Diff.STE.pd p u y)) :=
        CSq_fintype_sum_le s _ fun p => summable_CSq_fourierCoeff s
          ((Mcoef_contDiff T T' hT hT' i p).mul (Work.Diff.STE.B3.pdMulComp_contDiff_pd p hu))
          (Periodic1_mul' (Mcoef_periodic T T' hTper hTinv1 hTinv2 i p)
            (Work.Diff.STE.B3.ipdcl_periodic_pd (w := u) hpu (hu.differentiable (by simp)) p))
    _ ≤ (Fintype.card ι : ℝ) * ∑ p, C p
          * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff u) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => (hC p).2 u hu hpu) (by positivity)
    _ = ((Fintype.card ι : ℝ) * ∑ p, C p)
          * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff u) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ => by ring

/-- **The commutator `[Qᵢ, S_ε]` is of order `0`**, uniformly in `ε`: it is the sum over `p` of the
single-term commutators `[Mᵢₚ ∂ₚ, S_ε]`. -/
lemma Qop_comm_le (ρ : (ι → ℝ) → ℝ)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (T T' : (ι → ℝ) → (ι → ℝ))
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x)
    (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (i : ι) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ u : (ι → ℝ) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
      Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (Qop T T' i
          (Work.Diff.STE.B3.SymCalc.flatCut ρ ε u)
          - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Qop T T' i u)))
        ≤ C * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff u) := by
  classical
  choose C hC using fun p : ι =>
    firstOrder_comm_le_cplx ρ hρb hdiam L hL hρlip (Mcoef T T' i p)
      (Mcoef_contDiff T T' hT hT' i p) (Mcoef_periodic T T' hTper hTinv1 hTinv2 i p) p s
  have hMcont : ∀ p : ι, ContDiff ℝ (⊤ : ℕ∞) (Mcoef T T' i p) := fun p =>
    Mcoef_contDiff T T' hT hT' i p
  have hMper : ∀ p : ι, Work.Diff.STE.Periodic1 (Mcoef T T' i p) := fun p =>
    Mcoef_periodic T T' hTper hTinv1 hTinv2 i p
  refine ⟨(Fintype.card ι : ℝ) * ∑ p, C p,
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun p _ => (hC p).1),
    fun ε hε hε1 u hu hpu => ?_⟩
  have hper1 : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.flatCut ρ ε u) :=
    flatCut_periodic ρ ε u
  have hsm1 : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.flatCut ρ ε u) :=
    flatCut_contDiff ρ hρb ε hu hpu
  set Tp : ι → (ι → ℝ) → ℂ := fun p y =>
    Mcoef T T' i p y * Work.Diff.STE.pd p (Work.Diff.STE.B3.SymCalc.flatCut ρ ε u) y
    - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
        (fun y => Mcoef T T' i p y * Work.Diff.STE.pd p u y) y with hTpdef
  have hpt : ∀ p : ι, Tp p = fun y =>
      Mcoef T T' i p y * Work.Diff.STE.pd p (Work.Diff.STE.B3.SymCalc.flatCut ρ ε u) y
      - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
          (fun y => Mcoef T T' i p y * Work.Diff.STE.pd p u y) y := fun p =>
    congrFun hTpdef p
  have hfun : Qop T T' i (Work.Diff.STE.B3.SymCalc.flatCut ρ ε u)
      - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Qop T T' i u) = fun y => ∑ p, Tp p y := by
    have h1 : Qop T T' i (Work.Diff.STE.B3.SymCalc.flatCut ρ ε u)
        = fun y => ∑ p, (Mcoef T T' i p y
            * Work.Diff.STE.pd p (Work.Diff.STE.B3.SymCalc.flatCut ρ ε u) y) :=
      funext fun y => Qop_eq_sum T T' hTinv1 (hT'.differentiable (by simp)) i (hsm1.differentiable (by simp)) y
    have h2 : Qop T T' i u = fun y => ∑ p, Mcoef T T' i p y * Work.Diff.STE.pd p u y :=
      funext fun y => Qop_eq_sum T T' hTinv1 (hT'.differentiable (by simp)) i (hu.differentiable (by simp)) y
    have h3 : Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Qop T T' i u)
        = fun y => ∑ p, Work.Diff.STE.B3.SymCalc.flatCut ρ ε
            (fun y => Mcoef T T' i p y * Work.Diff.STE.pd p u y) y := by
      rw [h2]
      exact flatCut_fintype_sum ρ hρb ε _
        (fun p => (hMcont p).mul (Work.Diff.STE.B3.pdMulComp_contDiff_pd p hu))
        (fun p => Periodic1_mul' (hMper p)
          (Work.Diff.STE.B3.ipdcl_periodic_pd (w := u) hpu (hu.differentiable (by simp)) p))
    funext y
    rw [h1, h3]
    simp only [Pi.sub_apply, Finset.sum_apply]
    rw [← Finset.sum_sub_distrib]
  have hcontTp : ∀ p : ι, Continuous (Tp p) := fun p => by
    rw [hpt p]
    exact ((hMcont p).continuous.mul
        (Work.Diff.STE.B3.pdMulComp_contDiff_pd p hsm1).continuous).sub
      (flatCut_contDiff ρ hρb ε
        ((hMcont p).mul (Work.Diff.STE.B3.pdMulComp_contDiff_pd p hu))
        (Periodic1_mul' (hMper p)
          (Work.Diff.STE.B3.ipdcl_periodic_pd (w := u) hpu (hu.differentiable (by simp)) p))).continuous
  have hsmTp : ∀ p : ι, ContDiff ℝ (⊤ : ℕ∞) (Tp p) := fun p => by
    rw [hpt p]
    exact ((hMcont p).mul
        (Work.Diff.STE.B3.pdMulComp_contDiff_pd p hsm1)).sub
      (flatCut_contDiff ρ hρb ε
        ((hMcont p).mul (Work.Diff.STE.B3.pdMulComp_contDiff_pd p hu))
        (Periodic1_mul' (hMper p)
          (Work.Diff.STE.B3.ipdcl_periodic_pd (w := u) hpu (hu.differentiable (by simp)) p)))
  have hperTp : ∀ p : ι, Work.Diff.STE.Periodic1 (Tp p) := fun p => by
    rw [hpt p]
    exact Periodic1_sub'
      (Periodic1_mul' (hMper p)
        (Work.Diff.STE.B3.ipdcl_periodic_pd (w := Work.Diff.STE.B3.SymCalc.flatCut ρ ε u)
          hper1 (hsm1.differentiable (by simp)) p))
      (flatCut_periodic ρ ε _)
  have hcoe : Work.Diff.STE.fourierCoeff (fun y => ∑ p, Tp p y)
      = fun k => ∑ p, Work.Diff.STE.fourierCoeff (Tp p) k :=
    funext fun k => fourierCoeff_ftype_sum_of_continuous Tp hcontTp k
  rw [hfun, hcoe]
  calc Work.Diff.STE.CSq s (fun k => ∑ p, Work.Diff.STE.fourierCoeff (Tp p) k)
      ≤ (Fintype.card ι : ℝ) * ∑ p, Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (Tp p)) :=
        CSq_fintype_sum_le s _ fun p => summable_CSq_fourierCoeff s (hsmTp p) (hperTp p)
    _ ≤ (Fintype.card ι : ℝ) * ∑ p, C p * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff u) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => (hC p).2 ε hε hε1 u hu hpu)
          (by positivity)
    _ = ((Fintype.card ι : ℝ) * ∑ p, C p) * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff u) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ => by ring

end Work.Diff.STE.B3.SymCalcStep1
