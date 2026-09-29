import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17.lc_defs
import Submission.Work.C17I.xsOf_ge_eight_ninths
import Submission.Work.C17I.subst_eval_abs
import Submission.Work.C17I.hasSum_tsum_of_poly_growth
import Submission.Work.C17I.hasSum_tsum_of_coeff_growth
import Submission.Work.C17f.differentiableOn_of_hasSum_powSeries
import Submission.Work.C17f.deriv_hasSum_powSeries
import Submission.Work.C17g.segment_primitive
import Submission.Work.C17.Bsubst_poly_growth
import Submission.Work.C17I.DyIter_comp_yC

/-!
# Auxiliary material for `Work.C17.relation_to_LC`

Definitions and elementary lemmas used by the proof of `Work.C17.relation_to_LC`
(the analytic "log-coefficient" extraction `(LC)`).
-/

namespace Work.C17

open scoped BigOperators Topology
open Polynomial Filter

noncomputable section

/-! ## 1. Calculus plumbing -/

/-- The factor `(z-1)²/(z²-2z)` relating `∂_z` and `D_y`. -/
def wfac (z : ℂ) : ℂ := (z - 1) ^ 2 / (z ^ 2 - 2 * z)

/-- `(d/dz) (z²/(z-1))`, the derivative of `yC`. -/
def dyC (z : ℂ) : ℂ := (z ^ 2 - 2 * z) / (z - 1) ^ 2

lemma Dy_eq_mul_wfac (f : ℂ → ℂ) (z : ℂ) : Dy f z = deriv f z * wfac z := by
  rw [Dy, wfac, mul_div_assoc]

lemma dyC_mul_wfac (z : ℂ) (h1 : z ≠ 1) (h0 : z ≠ 0) (h2 : z ≠ 2) :
    dyC z * wfac z = 1 := by
  have hz : z ^ 2 - 2 * z ≠ 0 := by
    intro h
    have h' : z * (z - 2) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact h0 h''
    · exact h2 (sub_eq_zero.mp h'')
  have h1' : (z - 1) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr h1)
  rw [dyC, wfac]
  field_simp

lemma wfac_differentiableOn {Ω : Set ℂ} (hz0 : ∀ z ∈ Ω, z ≠ 0) (hz2 : ∀ z ∈ Ω, z ≠ 2) :
    DifferentiableOn ℂ wfac Ω := by
  have hnum : DifferentiableOn ℂ (fun z : ℂ => (z - 1) ^ 2) Ω :=
    (differentiableOn_id.sub (differentiableOn_const (1:ℂ))).pow 2
  have hden : DifferentiableOn ℂ (fun z : ℂ => z ^ 2 - 2 * z) Ω :=
    (differentiableOn_id.pow 2).sub (differentiableOn_id.const_mul 2)
  refine hnum.div hden (fun z hz => ?_)
  have h : z ^ 2 - 2 * z = z * (z - 2) := by ring
  rw [h]
  exact mul_ne_zero (hz0 z hz) (sub_ne_zero.mpr (hz2 z hz))

lemma Dy_differentiableOn {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (hz0 : ∀ z ∈ Ω, z ≠ 0) (hz2 : ∀ z ∈ Ω, z ≠ 2) : DifferentiableOn ℂ (Dy f) Ω := by
  have h1 : DifferentiableOn ℂ (deriv f) Ω := hf.deriv hΩ
  have h2 : DifferentiableOn ℂ (fun z => deriv f z * wfac z) Ω :=
    h1.mul (wfac_differentiableOn hz0 hz2)
  refine h2.congr (fun z hz => ?_)
  exact Dy_eq_mul_wfac f z

/-- `deriv` is local: eventual equality descends to the derivative, eventually. -/
lemma deriv_eventuallyEq {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    deriv f =ᶠ[𝓝 z] deriv g := by
  obtain ⟨s, hs, hsf⟩ := Filter.eventually_iff_exists_mem.mp h
  obtain ⟨t, hts, hto, hzt⟩ := mem_nhds_iff.mp hs
  filter_upwards [hto.mem_nhds hzt] with w hw
  exact Filter.EventuallyEq.deriv_eq
    (Filter.eventually_of_mem (hto.mem_nhds hw) (fun v hv => hsf v (hts hv)))

/-- `D_y^k` depends only on the germ. -/
lemma DyIter_eventuallyEq {z : ℂ} :
    ∀ k : ℕ, ∀ {f g : ℂ → ℂ}, f =ᶠ[𝓝 z] g → DyIter k f =ᶠ[𝓝 z] DyIter k g := by
  intro k
  induction k with
  | zero => intro f g h; exact h
  | succ k ih =>
      intro f g h
      show DyIter k (Dy (fun x => f x)) =ᶠ[𝓝 z] DyIter k (Dy (fun x => g x))
      refine ih ?_
      filter_upwards [deriv_eventuallyEq h] with w hw
      simp only [Dy, hw]

lemma DyIter_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) (k : ℕ) :
    DyIter k f z = DyIter k g z :=
  (DyIter_eventuallyEq k h).eq_of_nhds

/-- `D_y` commutes with the germ of a function agreeing on an open set. -/
lemma Dy_eq_of_eqOn {Ω : Set ℂ} (hΩ : IsOpen Ω) {f g : ℂ → ℂ} (h : Set.EqOn f g Ω)
    {z : ℂ} (hz : z ∈ Ω) : Dy f z = Dy g z :=
  DyIter_congr (Filter.eventually_of_mem (hΩ.mem_nhds hz) h) 1

/-- `D_y` commutes with multiplication by a scalar (no differentiability needed). -/
lemma Dy_const_mul (c : ℂ) (f : ℂ → ℂ) :
    Dy (fun z => c * f z) = fun z => c * Dy f z := by
  funext z
  rw [Dy_eq_mul_wfac, Dy_eq_mul_wfac, deriv_const_mul_field c]
  ring

lemma DyIter_differentiableOn {Ω : Set ℂ} (hΩ : IsOpen Ω) (hz0 : ∀ z ∈ Ω, z ≠ 0)
    (hz2 : ∀ z ∈ Ω, z ≠ 2) :
    ∀ k : ℕ, ∀ {f : ℂ → ℂ}, DifferentiableOn ℂ f Ω → DifferentiableOn ℂ (DyIter k f) Ω := by
  intro k
  induction k with
  | zero => intro f hf; simpa [DyIter] using hf
  | succ k ih =>
      intro f hf
      have hDf : DifferentiableOn ℂ (Dy f) Ω := Dy_differentiableOn hΩ hf hz0 hz2
      have h := ih hDf
      simpa [DyIter, Function.iterate_succ_apply] using h

/-- `D_y^k` of `κ·f` is `κ·D_y^k f`. -/
lemma DyIter_const_mul (c : ℂ) :
    ∀ k : ℕ, ∀ f : ℂ → ℂ, DyIter k (fun z => c * f z) = fun z => c * DyIter k f z := by
  intro k
  induction k with
  | zero => intro f; rfl
  | succ k ih =>
      intro f
      show DyIter k (Dy (fun z => c * f z)) = fun z => c * DyIter k (Dy f) z
      rw [Dy_const_mul]
      exact ih (Dy f)

/-! ## 2. Primitives on convex open sets -/

/-- On a convex open set, a holomorphic function has a primitive with any prescribed value at a
base point. -/
lemma exists_primitive_conv {Ω : Set ℂ} (hcvx : Convex ℝ Ω) (hopen : IsOpen Ω)
    {d : ℂ → ℂ} (hd : DifferentiableOn ℂ d Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (v : ℂ) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Ω ∧ F z₀ = v ∧ ∀ z ∈ Ω, HasDerivAt F (d z) z := by
  obtain ⟨hFd, hF'⟩ := Work.C17g.segment_primitive hcvx hopen hz₀ hd
  set G : ℂ → ℂ := fun z => (z - z₀) • ∫ t in (0:ℝ)..1, d (z₀ + t • (z - z₀)) with hG
  have hGd : DifferentiableOn ℂ G Ω := hFd
  have hG' : ∀ z ∈ Ω, HasDerivAt G (d z) z := hF'
  have hGz₀ : G z₀ = 0 := by
    rw [hG]
    simp
  exact ⟨fun z => G z + v, hGd.add_const v, by show G z₀ + v = v; rw [hGz₀, zero_add],
    fun z hz => (hG' z hz).add_const v⟩

/-! ## 3. Numerics for the cusp and the safe harbour -/

lemma xsOf_gt_five_sixths (m n : ℕ) (hm : 1 ≤ m) (hlt : m < n)
    (hgap : 10 ^ 6 * ((m : ℤ) - n).natAbs ≤ n) : (5 : ℝ) / 6 < xsOf m n := by
  have h := Work.C17I.xsOf_ge_eight_ninths m n hm hlt hgap
  linarith

lemma xsOf_nonneg (m n : ℕ) (hm : 1 ≤ m) (hlt : m < n) : (0:ℝ) ≤ xsOf m n :=
  le_of_lt (xsOf_pos m n hm hlt)

lemma norm_p0C_sub_one_gt : (41 : ℝ) / 100 < ‖p0C - 1‖ := by
  have h := norm_p0C_sub_one_sq
  nlinarith [norm_nonneg (p0C - 1), sq_nonneg (‖p0C - 1‖ - (41:ℝ)/100)]

lemma norm_yC_p0C_lt : ‖yC p0C‖ < (1 : ℝ) / 4 := by
  have h3 : 0 < ‖p0C - 1‖ := norm_p0C_sub_one_pos
  have h2 : ‖p0C‖ ^ 2 = (41 : ℝ) / 400 := norm_p0C_sq
  have h1 := norm_p0C_sub_one_gt
  have hy : yC p0C = p0C ^ 2 / (p0C - 1) := rfl
  rw [hy, norm_div, norm_pow, div_lt_iff₀ h3]
  nlinarith

lemma zero_notMem_ball_xs (m n : ℕ) (hm : 1 ≤ m) (hlt : m < n) {δ : ℝ}
    (hδ1 : 2 * δ ≤ xsOf m n) : (0 : ℂ) ∉ Metric.ball ((xsOf m n : ℂ)) δ := by
  intro h
  rw [Metric.mem_ball, Complex.dist_eq] at h
  rw [zero_sub, norm_neg] at h
  have hxn : ‖((xsOf m n : ℝ) : ℂ)‖ = xsOf m n := by
    rw [Complex.norm_real, Real.norm_of_nonneg (xsOf_nonneg m n hm hlt)]
  rw [hxn] at h
  have hp := xsOf_pos m n hm hlt
  linarith

lemma one_notMem_ball_xs (m n : ℕ) (hm : 1 ≤ m) (hlt : m < n) {δ : ℝ}
    (hδ2 : 2 * δ ≤ 1 - xsOf m n) : (1 : ℂ) ∉ Metric.ball ((xsOf m n : ℂ)) δ := by
  intro h
  rw [Metric.mem_ball, Complex.dist_eq] at h
  have hlt1 := xsOf_lt_one m n hm hlt
  have h1 : ‖(1:ℂ) - ((xsOf m n : ℝ) : ℂ)‖ = 1 - xsOf m n := by
    have hcast : (1:ℂ) - ((xsOf m n : ℝ) : ℂ) = (((1 - xsOf m n : ℝ)) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [h1] at h
  linarith

lemma two_notMem_ball_xs (m n : ℕ) (hm : 1 ≤ m) (hlt : m < n) {δ : ℝ}
    (hδ2 : 2 * δ ≤ 1 - xsOf m n) : (2 : ℂ) ∉ Metric.ball ((xsOf m n : ℂ)) δ := by
  intro h
  rw [Metric.mem_ball, Complex.dist_eq] at h
  have hlt1 := xsOf_lt_one m n hm hlt
  have h2 : ‖(2:ℂ) - ((xsOf m n : ℝ) : ℂ)‖ = 2 - xsOf m n := by
    have hcast : (2:ℂ) - ((xsOf m n : ℝ) : ℂ) = (((2 - xsOf m n : ℝ)) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [h2] at h
  linarith

/-! ## 4. Differentiability of the two kinds of power series that occur -/

/-- The value function of a power series whose coefficients grow at most like `r^n` is
holomorphic on the disc of radius `1/r`. -/
lemma differentiableOn_tsum_of_coeff_growth {c : ℕ → ℂ} {C r : ℝ} (hC : 0 ≤ C) (hr : 0 < r)
    (hc : ∀ n : ℕ, ‖c n‖ ≤ C * r ^ n) :
    DifferentiableOn ℂ (fun z : ℂ => ∑' n : ℕ, c n * z ^ n) (Metric.ball (0 : ℂ) (1 / r)) := by
  refine Work.C17f.differentiableOn_of_hasSum_powSeries (c := c) (r := 1 / r)
    (F := fun z : ℂ => ∑' n : ℕ, c n * z ^ n) (fun z hz => ?_)
  have hz' : ‖z‖ < 1 / r := by simpa [Metric.mem_ball, dist_zero_right] using hz
  exact Work.C17I.hasSum_tsum_of_coeff_growth hC hr hc z hz'

/-- The value function of a power series with polynomially growing coefficients is holomorphic on
the unit disc. -/
lemma differentiableOn_tsum_of_poly_growth {c : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C) {k : ℕ}
    (hc : ∀ n : ℕ, ‖c n‖ ≤ C * ((n : ℝ) + 1) ^ k) :
    DifferentiableOn ℂ (fun z : ℂ => ∑' n : ℕ, c n * z ^ n) (Metric.ball (0 : ℂ) 1) :=
  Work.C17f.differentiableOn_of_hasSum_powSeries
    (fun z hz => Work.C17I.hasSum_tsum_of_poly_growth hC hc z hz)

lemma norm_ratCast (q : ℚ) : ‖((q : ℚ) : ℂ)‖ = |(q : ℝ)| := by
  have hcast : ((q : ℚ) : ℂ) = ((q : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]

/-- The seven substituted pure series are holomorphic on the unit disc. -/
lemma Bsubst_differentiableOn (i : Fin 7) :
    DifferentiableOn ℂ
      (fun z : ℂ => ∑' k : ℕ,
        ((PowerSeries.coeff k ((Submission.CDTPlan.pureB i).subst Submission.CDT.sympY) : ℚ) : ℂ)
          * z ^ k)
      (Metric.ball (0 : ℂ) 1) := by
  obtain ⟨C, k, hCk⟩ := Work.C17.Bsubst_poly_growth i
  refine differentiableOn_tsum_of_poly_growth (c := fun N =>
    ((PowerSeries.coeff N ((Submission.CDTPlan.pureB i).subst Submission.CDT.sympY) : ℚ) : ℂ))
    (C := max C 0) (k := k) (le_max_right _ _) fun N => ?_
  rw [norm_ratCast]
  exact le_trans (hCk N) (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

/-! ## 5. Splitting a sum over `Fin 17` into its three blocks -/

/-- The index `5+k` (the four `G`-derivatives). -/
def gIdx (k : Fin 4) : Fin 17 := ⟨5 + (k : ℕ), by omega⟩

/-- The position of the `b`-th pure function in the ordered list of seventeen. -/
def bIdx (b : Fin 7) : Fin 17 :=
  if (b : ℕ) < 5 then ⟨(b : ℕ), by omega⟩ else ⟨(b : ℕ) + 4, by omega⟩

/-- The index `11+i` (the six integrals). -/
def iIdx (i : Fin 6) : Fin 17 := ⟨11 + (i : ℕ), by omega⟩

/-- The block decomposition of `Fin 17`: four `G`-derivatives, seven pure functions, six
integrals. -/
def j17 : ((Fin 4 ⊕ Fin 7) ⊕ Fin 6) → Fin 17
  | Sum.inl (Sum.inl k) => gIdx k
  | Sum.inl (Sum.inr b) => bIdx b
  | Sum.inr i => iIdx i

lemma j17_bijective : Function.Bijective j17 := by decide

lemma sum_fin17_split {M : Type*} [AddCommMonoid M] (g : Fin 17 → M) :
    (∑ i : Fin 17, g i)
      = (∑ k : Fin 4, g (gIdx k)) + (∑ b : Fin 7, g (bIdx b))
        + (∑ i : Fin 6, g (iIdx i)) := by
  rw [← Function.Bijective.sum_comp j17_bijective g]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  rfl


/-! ## 5. Formal series lemmas -/

/-- `d/dy` of the formal integral `intY` is the identity. -/
lemma dY_intY (W : PowerSeries ℚ) :
    PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.intY W) = W := by
  ext n
  rw [PowerSeries.coeff_derivative]
  have hcoeff : PowerSeries.coeff (n + 1) (Submission.CDTPlan.intY W)
      = PowerSeries.coeff n W / ((n : ℚ) + 1) := by
    rw [Submission.CDTPlan.intY, PowerSeries.coeff_mk]
    rw [if_neg (by omega : ¬ (n + 1 = 0))]
    rw [show n + 1 - 1 = n from by omega]
    push_cast
    ring
  rw [hcoeff]
  exact div_mul_cancel₀ (PowerSeries.coeff n W) (by positivity)

lemma PC_eq_aOf (m n : ℕ) (ra rb rab r0 : ℤ) :
    Submission.CDTPlan.PC m n ra rb rab r0
      = Submission.CDT.logP (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 := by
  simp only [Submission.CDTPlan.PC, Work.C17.aOf, Nat.cast_add, Nat.cast_mul, Nat.cast_one]

/-- `GC` is `Sym⁺(logP (aOf m) (aOf n) …)`. -/
lemma GC_eq_sympSym (m n : ℕ) (ra rb rab r0 : ℤ) :
    Submission.CDTPlan.GC m n ra rb rab r0
      = Submission.CDT.sympSym (Submission.CDT.logP (Work.C17.aOf m) (Work.C17.aOf n)
          ra rb rab r0) := by
  unfold Submission.CDTPlan.GC
  rw [PC_eq_aOf]

lemma yC_differentiableOn {s δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1 - s) :
    DifferentiableOn ℂ yC (Metric.ball ((s : ℂ)) δ) := by
  have hne : ∀ z ∈ Metric.ball ((s : ℂ)) δ, z ≠ 1 := by
    intro z hz hz1
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    rw [hz1] at hz
    have h2 : ‖(1:ℂ) - (s:ℂ)‖ = 1 - s := by
      have hc : (1:ℂ) - (s:ℂ) = (((1 - s : ℝ)) : ℂ) := by push_cast; ring
      rw [hc, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [h2] at hz
    linarith
  have h : yC = fun z : ℂ => z ^ 2 / (z - 1) := rfl
  rw [h]
  refine (differentiableOn_id.pow 2).div
    (differentiableOn_id.sub (differentiableOn_const (1:ℂ))) (fun z hz => ?_)
  exact sub_ne_zero.mpr (hne z hz)

lemma yC_ne_zero_of_mem {s δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1 - s) (hδs : δ < s) {z : ℂ}
    (hz : z ∈ Metric.ball ((s : ℂ)) δ) : yC z ≠ 0 := by
  have hdist : ‖z - ((s:ℝ):ℂ)‖ < δ := by
    have h2 := hz; rwa [Metric.mem_ball, Complex.dist_eq] at h2
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hdist
    rw [zero_sub, norm_neg] at hdist
    have h2 : ‖((s:ℝ):ℂ)‖ = s := by
      rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt (lt_trans hδ hδs))]
    rw [h2] at hdist
    linarith
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hdist
    have h2 : ‖(1:ℂ) - ((s:ℝ):ℂ)‖ = 1 - s := by
      have hc : (1:ℂ) - ((s:ℝ):ℂ) = (((1 - s : ℝ)) : ℂ) := by push_cast; ring
      rw [hc, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [h2] at hdist
    linarith
  have h1 : yC z = z ^ 2 / (z - 1) := rfl
  rw [h1]
  exact div_ne_zero (pow_ne_zero 2 hz0) (sub_ne_zero.mpr hz1)

lemma yC_differentiableOn_of_ne_one {U : Set ℂ} (h : ∀ z ∈ U, z ≠ 1) :
    DifferentiableOn ℂ yC U := by
  have h1 : yC = fun z : ℂ => z ^ 2 / (z - 1) := rfl
  rw [h1]
  refine (differentiableOn_id.pow 2).div
    (differentiableOn_id.sub (differentiableOn_const (1:ℂ))) (fun z hz => ?_)
  exact sub_ne_zero.mpr (h z hz)

lemma dyC_differentiableOn_of_ne_one {U : Set ℂ} (h : ∀ z ∈ U, z ≠ 1) :
    DifferentiableOn ℂ dyC U := by
  have h1 : dyC = fun z : ℂ => (z ^ 2 - 2 * z) / (z - 1) ^ 2 := rfl
  rw [h1]
  refine ((differentiableOn_id.pow 2).sub (differentiableOn_id.const_mul 2)).div
    ((differentiableOn_id.sub (differentiableOn_const (1:ℂ))).pow 2) (fun z hz => ?_)
  exact pow_ne_zero 2 (sub_ne_zero.mpr (h z hz))

lemma yC_ne_zero_iff (z : ℂ) (h0 : z ≠ 0) (h1 : z ≠ 1) : yC z ≠ 0 := by
  have h : yC z = z ^ 2 / (z - 1) := rfl
  rw [h]
  exact div_ne_zero (pow_ne_zero 2 h0) (sub_ne_zero.mpr h1)

lemma pAtY_differentiableOn_of_ne_one {U : Set ℂ} (h : ∀ z ∈ U, z ≠ 1) (p : Polynomial ℚ) :
    DifferentiableOn ℂ (Work.C17.pAtY p) U := by
  have hyC : DifferentiableOn ℂ yC U := yC_differentiableOn_of_ne_one h
  have hpoly : DifferentiableOn ℂ (fun y : ℂ => (p.map (algebraMap ℚ ℂ)).eval y) Set.univ :=
    Polynomial.differentiableOn (p := p.map (algebraMap ℚ ℂ)) (s := Set.univ)
  exact (hpoly.comp hyC (fun z _ => Set.mem_univ _)).congr (fun z hz => by
    simp only [Function.comp_apply, Work.C17.pAtY, Polynomial.eval_map])

lemma yC_ne_zero_of_ne_zero {U : Set ℂ} (h : ∀ z ∈ U, z ≠ 0) (h1 : ∀ z ∈ U, z ≠ 1) :
    ∀ z ∈ U, yC z ≠ 0 := by
  intro z hz
  have h2 : yC z = z ^ 2 / (z - 1) := rfl
  rw [h2]
  exact div_ne_zero (pow_ne_zero 2 (h z hz)) (sub_ne_zero.mpr (h1 z hz))

/-! ## 6. Index bookkeeping for the ordered list of seventeen functions -/

lemma seventeen_gIdx_eq (m n : ℕ) (ra rb rab r0 : ℤ) (k : Fin 4) :
    Submission.CDTPlan.seventeen m n ra rb rab r0 (gIdx k)
      = (PowerSeries.derivative (R := ℚ))^[(k : ℕ)] (Submission.CDTPlan.GC m n ra rb rab r0) := by
  fin_cases k <;>
    simp [gIdx, Submission.CDTPlan.seventeen, Submission.CDTPlan.dY,
      Function.iterate_succ_apply']

lemma seventeen_gIdx_eq' (m n : ℕ) (ra rb rab r0 : ℤ) (k : Fin 4) :
    Submission.CDTPlan.seventeen m n ra rb rab r0 (gIdx k)
      = (PowerSeries.derivative (R := ℚ))^[(k : ℕ)] (Submission.CDT.sympSym
          (Submission.CDT.logP (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0)) := by
  rw [seventeen_gIdx_eq, GC_eq_sympSym]

lemma seventeen_bIdx_eq (m n : ℕ) (ra rb rab r0 : ℤ) (b : Fin 7) :
    Submission.CDTPlan.seventeen m n ra rb rab r0 (bIdx b) = Submission.CDTPlan.pureB b := by
  have h := Work.C17.seventeen_pure_eq m n ra rb rab r0
  fin_cases b
  · simpa [bIdx] using h.1
  · simpa [bIdx] using h.2.1
  · simpa [bIdx] using h.2.2.1
  · simpa [bIdx] using h.2.2.2.1
  · simpa [bIdx] using h.2.2.2.2.1
  · simpa [bIdx] using h.2.2.2.2.2.1
  · simpa [bIdx] using h.2.2.2.2.2.2

/-- `tq 0 W = W`. -/
lemma tq_zero (W : PowerSeries ℚ) : Submission.CDTPlan.tq 0 W = W := by
  ext n
  simp [Submission.CDTPlan.tq]

/-- The first integral entry `11 = ∫yG`. -/
lemma seventeen_iIdx_zero (m n : ℕ) (ra rb rab r0 : ℤ) :
    Submission.CDTPlan.seventeen m n ra rb rab r0 (iIdx 0)
      = Submission.CDTPlan.intY (PowerSeries.X * Submission.CDTPlan.GC m n ra rb rab r0) := by
  simp [iIdx, Submission.CDTPlan.seventeen]

/-- For `i ≥ 1`, the integral entry `11+i = ∫(G - jet_{i-1})/y^i`. -/
lemma seventeen_iIdx_pos (m n : ℕ) (ra rb rab r0 : ℤ) (i : Fin 6) (hi : (i : ℕ) ≠ 0) :
    Submission.CDTPlan.seventeen m n ra rb rab r0 (iIdx i)
      = Submission.CDTPlan.intY (Submission.CDTPlan.tq ((i : ℕ) - 1)
          (Submission.CDTPlan.GC m n ra rb rab r0)) := by
  have h1 : (1 : ℕ) ≤ (i : ℕ) := Nat.one_le_iff_ne_zero.mpr hi
  fin_cases i
  · exact absurd rfl hi
  · simp [iIdx, Submission.CDTPlan.seventeen, tq_zero]
  · simp [iIdx, Submission.CDTPlan.seventeen]
  · simp [iIdx, Submission.CDTPlan.seventeen]
  · simp [iIdx, Submission.CDTPlan.seventeen]
  · simp [iIdx, Submission.CDTPlan.seventeen]

lemma seventeen_iIdx_zero' (m n : ℕ) (ra rb rab r0 : ℤ) :
    Submission.CDTPlan.seventeen m n ra rb rab r0 (iIdx 0)
      = Submission.CDTPlan.intY (PowerSeries.X * Submission.CDT.sympSym
          (Submission.CDT.logP (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0)) := by
  rw [seventeen_iIdx_zero, GC_eq_sympSym]

lemma seventeen_iIdx_pos' (m n : ℕ) (ra rb rab r0 : ℤ) (i : Fin 6) (hi : (i : ℕ) ≠ 0) :
    Submission.CDTPlan.seventeen m n ra rb rab r0 (iIdx i)
      = Submission.CDTPlan.intY (Submission.CDTPlan.tq ((i : ℕ) - 1)
          (Submission.CDT.sympSym
            (Submission.CDT.logP (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0))) := by
  rw [seventeen_iIdx_pos m n ra rb rab r0 i hi, GC_eq_sympSym]

/-! ## 7. The `y`-series of a coefficient sequence, evaluated at `yC z` -/

/-- `z ↦ Σ_k c_k (yC z)^k`: the `y`-series with coefficients `c`, evaluated at `yC z`. -/
def ySeriesFun (c : ℕ → ℂ) : ℂ → ℂ := fun z => ∑' k : ℕ, c k * yC z ^ k

lemma hasDerivAt_yC {z : ℂ} (hz1 : z ≠ 1) : HasDerivAt yC (dyC z) z := by
  have h1 : HasDerivAt (fun w : ℂ => w ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have h2 : HasDerivAt (fun w : ℂ => w - 1) 1 z := (hasDerivAt_id z).sub_const 1
  have h3 : HasDerivAt (fun w : ℂ => w ^ 2 / (w - 1))
      ((2 * z * (z - 1) - z ^ 2 * 1) / (z - 1) ^ 2) z :=
    h1.div h2 (by simpa using sub_ne_zero.mpr hz1)
  have heq : (2 * z * (z - 1) - z ^ 2 * 1) / (z - 1) ^ 2 = dyC z := by
    rw [dyC]; ring
  rw [heq] at h3
  exact h3

/-- Conversion between the two ways of writing a geometric coefficient bound. -/
lemma coeff_bound_conv {c : ℕ → ℂ} {C R : ℝ} (hR : 0 < R)
    (hc : ∀ k : ℕ, ‖c k‖ * R ^ k ≤ C) : ∀ k : ℕ, ‖c k‖ ≤ C * (1 / R) ^ k := by
  intro k
  have hRk : (0 : ℝ) < R ^ k := pow_pos hR k
  have h1 : ‖c k‖ ≤ C / R ^ k := (le_div_iff₀ hRk).mpr (hc k)
  have h2 : C / R ^ k = C * (1 / R) ^ k := by rw [div_eq_mul_inv, one_div, inv_pow]
  rwa [h2] at h1

lemma differentiableAt_tsum_of_coeff_growth {c : ℕ → ℂ} {C r : ℝ} (hC : 0 ≤ C) (hr : 0 < r)
    (hc : ∀ n : ℕ, ‖c n‖ ≤ C * r ^ n) {z : ℂ} (hz : ‖z‖ < 1 / r) :
    DifferentiableAt ℂ (fun w : ℂ => ∑' n : ℕ, c n * w ^ n) z :=
  (differentiableOn_tsum_of_coeff_growth hC hr hc).differentiableAt
    (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right] using hz))

lemma differentiableAt_ySeriesFun {c : ℕ → ℂ} {C R : ℝ} (hC : 0 < C) (hR : 0 < R)
    (hc : ∀ k : ℕ, ‖c k‖ * R ^ k ≤ C) {z : ℂ} (hz : ‖yC z‖ < R) (hz1 : z ≠ 1) :
    DifferentiableAt ℂ (ySeriesFun c) z := by
  have hH : DifferentiableAt ℂ (fun w : ℂ => ∑' k : ℕ, c k * w ^ k) (yC z) := by
    refine differentiableAt_tsum_of_coeff_growth hC.le (by positivity) (coeff_bound_conv hR hc) ?_
    rwa [one_div_one_div]
  exact hH.comp z (hasDerivAt_yC hz1).differentiableAt

lemma deriv_ySeriesFun {c : ℕ → ℂ} {C R : ℝ} (hC : 0 < C) (hR : 0 < R)
    (hc : ∀ k : ℕ, ‖c k‖ * R ^ k ≤ C) {z : ℂ} (hz : ‖yC z‖ < R) (hz1 : z ≠ 1) :
    deriv (ySeriesFun c) z
      = (∑' k : ℕ, ((k : ℂ) + 1) * c (k + 1) * yC z ^ k) * dyC z := by
  have hHdiff : DifferentiableAt ℂ (fun w : ℂ => ∑' k : ℕ, c k * w ^ k) (yC z) := by
    refine differentiableAt_tsum_of_coeff_growth hC.le (by positivity) (coeff_bound_conv hR hc) ?_
    rwa [one_div_one_div]
  have hHderiv : deriv (fun w : ℂ => ∑' k : ℕ, c k * w ^ k) (yC z)
      = ∑' k : ℕ, ((k : ℂ) + 1) * c (k + 1) * yC z ^ k := by
    have hsum : HasSum (fun k : ℕ => ((k : ℂ) + 1) * c (k + 1) * yC z ^ k)
        (deriv (fun w : ℂ => ∑' k : ℕ, c k * w ^ k) (yC z)) := by
      refine Work.C17f.deriv_hasSum_powSeries c R
        (fun w : ℂ => ∑' k : ℕ, c k * w ^ k) (fun w hw => ?_) (yC z) hz
      exact Work.C17I.hasSum_tsum_of_coeff_growth hC.le (by positivity)
        (coeff_bound_conv hR hc) w (by rwa [one_div_one_div])
    exact hsum.tsum_eq.symm
  have hHd : HasDerivAt (fun w : ℂ => ∑' k : ℕ, c k * w ^ k)
      (deriv (fun w : ℂ => ∑' k : ℕ, c k * w ^ k) (yC z)) (yC z) := hHdiff.hasDerivAt
  have hyC : HasDerivAt yC (dyC z) z := hasDerivAt_yC hz1
  have hcomp : HasDerivAt ((fun w : ℂ => ∑' k : ℕ, c k * w ^ k) ∘ yC)
      ((∑' k : ℕ, ((k : ℂ) + 1) * c (k + 1) * yC z ^ k) * dyC z) z := by
    have h1 := hHdiff.hasDerivAt.comp z hyC
    rw [hHderiv] at h1
    exact h1
  rw [show ySeriesFun c = (fun w : ℂ => ∑' k : ℕ, c k * w ^ k) ∘ yC from rfl, hcomp.deriv]

/-- Coefficient bound for `intY W` at the same rate, when `R ≤ 1`. -/
lemma intY_coeff_bound {W : PowerSeries ℚ} {C R : ℝ} (hC : 0 < C) (hR : 0 < R) (hR1 : R ≤ 1)
    (hW : ∀ k : ℕ, ‖((PowerSeries.coeff k W : ℚ) : ℂ)‖ * R ^ k ≤ C) :
    ∀ k : ℕ, ‖((PowerSeries.coeff k (Submission.CDTPlan.intY W) : ℚ) : ℂ)‖ * R ^ k ≤ C := by
  intro k
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have h0 : PowerSeries.coeff 0 (Submission.CDTPlan.intY W) = 0 := by
      rw [Submission.CDTPlan.intY, PowerSeries.coeff_mk, if_pos rfl]
    rw [h0]
    simpa using hC.le
  · have h1 : PowerSeries.coeff k (Submission.CDTPlan.intY W)
        = PowerSeries.coeff (k - 1) W / (k : ℚ) := by
      rw [Submission.CDTPlan.intY, PowerSeries.coeff_mk]
      rw [if_neg (by omega : ¬ (k = 0))]
    have h2 : ‖((PowerSeries.coeff k (Submission.CDTPlan.intY W) : ℚ) : ℂ)‖
        = ‖((PowerSeries.coeff (k - 1) W : ℚ) : ℂ)‖ / (k : ℝ) := by
      rw [h1]
      rw [show (((PowerSeries.coeff (k - 1) W / (k : ℚ) : ℚ)) : ℂ)
            = ((PowerSeries.coeff (k - 1) W : ℚ) : ℂ) / (((k : ℚ)) : ℂ) from by
          push_cast; ring]
      rw [norm_div, norm_ratCast,
        show ‖(((k : ℚ)) : ℂ)‖ = (k : ℝ) from by
          rw [norm_ratCast]
          have hc : (((k : ℚ)) : ℝ) = (k : ℝ) := by push_cast; ring
          rw [hc, abs_of_nonneg (by positivity)]]
    rw [h2]
    have hkn : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    have hle : ‖((PowerSeries.coeff (k - 1) W : ℚ) : ℂ)‖ / (k : ℝ)
        ≤ ‖((PowerSeries.coeff (k - 1) W : ℚ) : ℂ)‖ := by
      rw [div_le_iff₀ hkpos]
      nlinarith [norm_nonneg (((PowerSeries.coeff (k - 1) W : ℚ) : ℂ))]
    calc ‖((PowerSeries.coeff (k - 1) W : ℚ) : ℂ)‖ / (k : ℝ) * R ^ k
        ≤ ‖((PowerSeries.coeff (k - 1) W : ℚ) : ℂ)‖ * R ^ k :=
          mul_le_mul_of_nonneg_right hle (pow_nonneg hR.le k)
      _ = (‖((PowerSeries.coeff (k - 1) W : ℚ) : ℂ)‖ * R ^ (k - 1)) * R := by
          have hpow : R ^ k = R ^ (k - 1) * R := by
            conv_lhs => rw [show k = (k - 1) + 1 from by omega]
            rw [pow_succ]
          rw [hpow]; ring
      _ ≤ C * R := mul_le_mul_of_nonneg_right (hW (k - 1)) hR.le
      _ ≤ C := by nlinarith [hC.le, hR1]

/-- The derivative of the pullback of the formal integral `intY W`. -/
lemma hasDerivAt_ySeriesFun_intY {W : PowerSeries ℚ} {C R : ℝ} (hC : 0 < C) (hR : 0 < R)
    (hR1 : R ≤ 1) (hW : ∀ k : ℕ, ‖((PowerSeries.coeff k W : ℚ) : ℂ)‖ * R ^ k ≤ C)
    {z : ℂ} (hz : ‖yC z‖ < R) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hz2 : z ≠ 2) :
    HasDerivAt (ySeriesFun fun k => ((PowerSeries.coeff k (Submission.CDTPlan.intY W) : ℚ) : ℂ))
      (ySeriesFun (fun k => ((PowerSeries.coeff k W : ℚ) : ℂ)) z * dyC z) z := by
  have hd := Work.C17I.DyIter_comp_yC (Submission.CDTPlan.intY W) hC hR
    (intY_coeff_bound hC hR hR1 hW) z hz hz0 hz1 hz2 1
  have hDy : Work.C17.Dy (fun w : ℂ => ∑' k : ℕ,
      ((PowerSeries.coeff k (Submission.CDTPlan.intY W) : ℚ) : ℂ) * Work.C17.yC w ^ k) z
      = ∑' k : ℕ, ((PowerSeries.coeff k W : ℚ) : ℂ) * Work.C17.yC z ^ k := by
    simpa only [Work.C17.DyIter, Function.iterate_one, dY_intY] using hd
  have hw := Work.C17.Dy_eq_mul_wfac (fun w : ℂ => ∑' k : ℕ,
    ((PowerSeries.coeff k (Submission.CDTPlan.intY W) : ℚ) : ℂ) * Work.C17.yC w ^ k) z
  rw [hDy] at hw
  have hfac := Work.C17.dyC_mul_wfac z hz1 hz0 hz2
  have hdiff : DifferentiableAt ℂ (fun w : ℂ => ∑' k : ℕ,
      ((PowerSeries.coeff k (Submission.CDTPlan.intY W) : ℚ) : ℂ) * Work.C17.yC w ^ k) z :=
    differentiableAt_ySeriesFun hC hR (intY_coeff_bound hC hR hR1 hW) hz hz1
  have hderiv_eq : deriv (fun w : ℂ => ∑' k : ℕ,
      ((PowerSeries.coeff k (Submission.CDTPlan.intY W) : ℚ) : ℂ) * Work.C17.yC w ^ k) z
      = (∑' k : ℕ, ((PowerSeries.coeff k W : ℚ) : ℂ) * Work.C17.yC z ^ k) * Work.C17.dyC z := by
    have h3 : deriv (fun w : ℂ => ∑' k : ℕ,
        ((PowerSeries.coeff k (Submission.CDTPlan.intY W) : ℚ) : ℂ) * Work.C17.yC w ^ k) z
          * Work.C17.wfac z
        = ∑' k : ℕ, ((PowerSeries.coeff k W : ℚ) : ℂ) * Work.C17.yC z ^ k := hw.symm
    calc deriv (fun w : ℂ => ∑' k : ℕ,
          ((PowerSeries.coeff k (Submission.CDTPlan.intY W) : ℚ) : ℂ) * Work.C17.yC w ^ k) z
        = deriv (fun w : ℂ => ∑' k : ℕ,
            ((PowerSeries.coeff k (Submission.CDTPlan.intY W) : ℚ) : ℂ) * Work.C17.yC w ^ k) z
            * (Work.C17.dyC z * Work.C17.wfac z) := by rw [hfac, mul_one]
      _ = (deriv (fun w : ℂ => ∑' k : ℕ,
            ((PowerSeries.coeff k (Submission.CDTPlan.intY W) : ℚ) : ℂ) * Work.C17.yC w ^ k) z
            * Work.C17.wfac z) * Work.C17.dyC z := by ring
      _ = (∑' k : ℕ, ((PowerSeries.coeff k W : ℚ) : ℂ) * Work.C17.yC z ^ k)
            * Work.C17.dyC z := by rw [h3]
  have key : HasDerivAt (fun w : ℂ => ∑' k : ℕ,
      ((PowerSeries.coeff k (Submission.CDTPlan.intY W) : ℚ) : ℂ) * Work.C17.yC w ^ k)
      ((∑' k : ℕ, ((PowerSeries.coeff k W : ℚ) : ℂ) * Work.C17.yC z ^ k) * Work.C17.dyC z) z := by
    have h := hdiff.hasDerivAt
    rw [hderiv_eq] at h
    exact h
  have hrhs : ySeriesFun (fun k => ((PowerSeries.coeff k W : ℚ) : ℂ)) z
      = ∑' k : ℕ, ((PowerSeries.coeff k W : ℚ) : ℂ) * Work.C17.yC z ^ k := rfl
  rw [hrhs]
  exact key

end

end Work.C17
