import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmPot_dbarCoord
import Submission.Work.CR.Flat.Cauchy.bmKernel_divergence_of_eps
import Submission.Work.NN.Final.bmDefectTwo

namespace Work.NN.Final

open MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

/-! ### Auxiliary lemmas

These are the same auxiliary lemmas as those used in
`Submission/Work/NN/Final/bmDefectTwo.lean` (where they are `private`), restated here
with their own names: a radius outside which a compactly supported function vanishes,
integrability of the kernel against `∂̄` of a compactly supported `C¹` function, and the
translated Bochner–Martinelli divergence formula. -/

/-- A compactly supported function vanishes outside a ball of positive radius. -/
private lemma bm3_exists_radius {n : ℕ} {g : (Fin n → ℂ) → ℂ}
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
private lemma bm3_integrable {n : ℕ} (hn : 0 < n) (i k : Fin n)
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
private lemma bm3_divergence {n : ℕ} (hn : 0 < n) {g : (Fin n → ℂ) → ℂ}
    (hg : ContDiff ℝ 1 g) (hcs : HasCompactSupport g) (z : Fin n → ℂ) :
    (∑ m : Fin n, ∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel m x
        * Work.CR.Flat.dbarCoord m g (z + x))
      = Work.CR.Flat.Cauchy.bmGamma n * g z := by
  obtain ⟨R, hR, hsupp⟩ := bm3_exists_radius hcs
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

/-- **The `(0,3)`-level Bochner–Martinelli identity.**  The `(0,2)`-level identity is
`Work.NN.Final.bmDefectTwo` (`Submission/Work/NN/Final/bmDefectTwo.lean`, sorry-free):

`dbarCoord j (bmPot X_{l·}) - dbarCoord l (bmPot X_{j·})
   = ∑ m, ∫ x, bmKernel m x * (dbarCoord j X_{lm} - dbarCoord l X_{jm} + dbarCoord m X_{jl}) (z+x) - γ X_{jl} z`.

This is the same statement with one more index: for a `C¹` compactly supported family
`Y : Fin n → Fin n → Fin n → (ℂⁿ → ℂ)` (the first three indices are the form indices, the last
ingredient of `bmPot` is the fibre index),

`Δ₃ (bmPot Y) := dbarCoord j (bmPot (Y l m ·)) - dbarCoord l (bmPot (Y j m ·))
                + dbarCoord m (bmPot (Y j l ·))
   = γ · Y j l m z + ∑ i, ∫ x, bmKernel i x * (dbarCoord j (Y l m i) - dbarCoord l (Y j m i)
        + dbarCoord m (Y j l i) - dbarCoord i (Y j l m)) (z + x)`.

The proof should mirror `bmDefectTwo`: `bmPot_dbarCoord` turns `dbarCoord j (bmPot (Y l m ·)) z`
into `∑ i, ∫ x, bmKernel i x * dbarCoord j (Y l m i) (z+x)`, the four terms are regrouped as
`dbarCoord i (Y j l m) (z+x)` plus the alternating four-index sum, and the divergence formula
(`bmKernel_divergence_of_eps`, used as `∑ i, ∫ x, bmKernel i x * dbarCoord i (Y j l m) (z+x) = γ Y j l m z`,
with the same positive sign as the auxiliary lemma `bmKernel_divergence_comp_add` inside `bmDefectTwo`)
evaluates the first group.  This is the analytic input which makes the *error* of one
Bochner–Martinelli step on a polycylinder closed where the cutoff is 1, without ever
differentiating the potential twice. -/
theorem bmPot_dbarCoord_three {n : ℕ} (hn : 0 < n)
    {Y : Fin n → Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hY : ∀ j l m, ContDiff ℝ 1 (Y j l m))
    (hcs : ∀ j l m, HasCompactSupport (Y j l m)) :
    ∀ (j l m : Fin n) (z : Fin n → ℂ),
      Work.CR.Flat.dbarCoord j (Work.CR.Flat.Cauchy.bmPot (fun i => Y l m i)) z
        - Work.CR.Flat.dbarCoord l (Work.CR.Flat.Cauchy.bmPot (fun i => Y j m i)) z
        + Work.CR.Flat.dbarCoord m (Work.CR.Flat.Cauchy.bmPot (fun i => Y j l i)) z
      = Work.CR.Flat.Cauchy.bmGamma n * Y j l m z
        + ∑ i : Fin n, ∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel i x *
            (Work.CR.Flat.dbarCoord j (Y l m i) (z + x)
              - Work.CR.Flat.dbarCoord l (Y j m i) (z + x)
              + Work.CR.Flat.dbarCoord m (Y j l i) (z + x)
              - Work.CR.Flat.dbarCoord i (Y j l m) (z + x)) := by
  intro j l m z
  -- a single radius outside which all the components `Y_{ikp}` vanish
  have hRex : ∀ i k p : Fin n, ∃ R : ℝ, 0 < R ∧ ∀ x, R ≤ ‖x‖ → Y i k p x = 0 :=
    fun i k p => bm3_exists_radius (hcs i k p)
  choose R hRpos hRsupp using hRex
  set r : ℝ := (∑ i : Fin n, ∑ k : Fin n, ∑ p : Fin n, R i k p) + 1 with hr
  have hrpos : 0 < r := by
    rw [hr]
    have h : 0 ≤ ∑ i : Fin n, ∑ k : Fin n, ∑ p : Fin n, R i k p :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ =>
        Finset.sum_nonneg fun p _ => le_of_lt (hRpos i k p)
    linarith
  have hRle : ∀ i k p : Fin n, R i k p ≤ r := by
    intro i k p
    have h1 : R i k p ≤ ∑ p' : Fin n, R i k p' :=
      Finset.single_le_sum (fun b _ => le_of_lt (hRpos i k b)) (Finset.mem_univ p)
    have h2 : (∑ p' : Fin n, R i k p') ≤ ∑ k' : Fin n, ∑ p' : Fin n, R i k' p' :=
      Finset.single_le_sum (fun b _ => Finset.sum_nonneg fun b' _ => le_of_lt (hRpos i b b'))
        (Finset.mem_univ k)
    have h3 : (∑ k' : Fin n, ∑ p' : Fin n, R i k' p')
        ≤ ∑ i' : Fin n, ∑ k' : Fin n, ∑ p' : Fin n, R i' k' p' :=
      Finset.single_le_sum (fun b _ => Finset.sum_nonneg fun b' _ =>
        Finset.sum_nonneg fun b'' _ => le_of_lt (hRpos b b' b'')) (Finset.mem_univ i)
    rw [hr]
    linarith
  have hsupp : ∀ i k p : Fin n, ∀ x : Fin n → ℂ, r ≤ ‖x‖ → Y i k p x = 0 :=
    fun i k p x hx => hRsupp i k p x (le_trans (hRle i k p) hx)
  -- the `∂̄`-derivatives of the three row potentials
  have hA := Work.CR.Flat.Cauchy.bmPot_dbarCoord hn (f := fun i : Fin n => Y l m i)
    (fun i => hY l m i) hrpos (fun i x hx => hsupp l m i x hx) j z
  have hB := Work.CR.Flat.Cauchy.bmPot_dbarCoord hn (f := fun i : Fin n => Y j m i)
    (fun i => hY j m i) hrpos (fun i x hx => hsupp j m i x hx) l z
  have hC := Work.CR.Flat.Cauchy.bmPot_dbarCoord hn (f := fun i : Fin n => Y j l i)
    (fun i => hY j l i) hrpos (fun i x hx => hsupp j l i x hx) m z
  -- the Bochner–Martinelli formula for the remaining component `Y_{jlm}`
  have hD := bm3_divergence hn (hY j l m) (hcs j l m) z
  -- cleaned restatements, so that no beta-redexes appear when they are used below
  have hA' : Work.CR.Flat.dbarCoord j (Work.CR.Flat.Cauchy.bmPot (fun i => Y l m i)) z
      = ∑ k : Fin n, ∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel k x *
          Work.CR.Flat.dbarCoord j (Y l m k) (z + x) := hA
  have hB' : Work.CR.Flat.dbarCoord l (Work.CR.Flat.Cauchy.bmPot (fun i => Y j m i)) z
      = ∑ k : Fin n, ∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel k x *
          Work.CR.Flat.dbarCoord l (Y j m k) (z + x) := hB
  have hC' : Work.CR.Flat.dbarCoord m (Work.CR.Flat.Cauchy.bmPot (fun i => Y j l i)) z
      = ∑ k : Fin n, ∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel k x *
          Work.CR.Flat.dbarCoord m (Y j l k) (z + x) := hC
  have hD' : (∑ k : Fin n, ∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel k x *
        Work.CR.Flat.dbarCoord k (Y j l m) (z + x))
      = Work.CR.Flat.Cauchy.bmGamma n * Y j l m z := hD
  -- integrability of the four pieces
  have hI1 : ∀ i : Fin n, Integrable (fun x : Fin n → ℂ =>
      Work.CR.Flat.Cauchy.bmKernel i x * Work.CR.Flat.dbarCoord j (Y l m i) (z + x)) :=
    fun i => bm3_integrable hn j i (hY l m i) (fun x hx => hsupp l m i x hx) z
  have hI2 : ∀ i : Fin n, Integrable (fun x : Fin n → ℂ =>
      Work.CR.Flat.Cauchy.bmKernel i x * Work.CR.Flat.dbarCoord l (Y j m i) (z + x)) :=
    fun i => bm3_integrable hn l i (hY j m i) (fun x hx => hsupp j m i x hx) z
  have hI3 : ∀ i : Fin n, Integrable (fun x : Fin n → ℂ =>
      Work.CR.Flat.Cauchy.bmKernel i x * Work.CR.Flat.dbarCoord m (Y j l i) (z + x)) :=
    fun i => bm3_integrable hn m i (hY j l i) (fun x hx => hsupp j l i x hx) z
  have hI4 : ∀ i : Fin n, Integrable (fun x : Fin n → ℂ =>
      Work.CR.Flat.Cauchy.bmKernel i x * Work.CR.Flat.dbarCoord i (Y j l m) (z + x)) :=
    fun i => bm3_integrable hn i i (hY j l m) (fun x hx => hsupp j l m x hx) z
  -- splitting one integral into its four parts
  have key : ∀ i : Fin n,
      (∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel i x *
        (Work.CR.Flat.dbarCoord j (Y l m i) (z + x)
          - Work.CR.Flat.dbarCoord l (Y j m i) (z + x)
          + Work.CR.Flat.dbarCoord m (Y j l i) (z + x)
          - Work.CR.Flat.dbarCoord i (Y j l m) (z + x)))
      = (∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel i x *
            Work.CR.Flat.dbarCoord j (Y l m i) (z + x))
        - (∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel i x *
            Work.CR.Flat.dbarCoord l (Y j m i) (z + x))
        + (∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel i x *
            Work.CR.Flat.dbarCoord m (Y j l i) (z + x))
        - (∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel i x *
            Work.CR.Flat.dbarCoord i (Y j l m) (z + x)) := by
    intro i
    have h1 : (∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel i x *
        (Work.CR.Flat.dbarCoord j (Y l m i) (z + x)
          - Work.CR.Flat.dbarCoord l (Y j m i) (z + x)
          + Work.CR.Flat.dbarCoord m (Y j l i) (z + x)
          - Work.CR.Flat.dbarCoord i (Y j l m) (z + x)))
        = ∫ x : Fin n → ℂ,
            (Work.CR.Flat.Cauchy.bmKernel i x * Work.CR.Flat.dbarCoord j (Y l m i) (z + x)
              - Work.CR.Flat.Cauchy.bmKernel i x * Work.CR.Flat.dbarCoord l (Y j m i) (z + x))
            + (Work.CR.Flat.Cauchy.bmKernel i x * Work.CR.Flat.dbarCoord m (Y j l i) (z + x)
              - Work.CR.Flat.Cauchy.bmKernel i x
                  * Work.CR.Flat.dbarCoord i (Y j l m) (z + x)) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [h1, integral_add
      (f := fun x : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel i x
          * Work.CR.Flat.dbarCoord j (Y l m i) (z + x)
        - Work.CR.Flat.Cauchy.bmKernel i x * Work.CR.Flat.dbarCoord l (Y j m i) (z + x))
      (g := fun x : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel i x
          * Work.CR.Flat.dbarCoord m (Y j l i) (z + x)
        - Work.CR.Flat.Cauchy.bmKernel i x * Work.CR.Flat.dbarCoord i (Y j l m) (z + x))
      ((hI1 i).sub (hI2 i)) ((hI3 i).sub (hI4 i)),
      integral_sub (hI1 i) (hI2 i), integral_sub (hI3 i) (hI4 i)]
    ring
  rw [hA', hB', hC', ← hD']
  rw [Finset.sum_congr rfl fun i _ => key i]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

end

end Work.NN.Final
