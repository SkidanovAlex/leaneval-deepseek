import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.SmallBVocab
import Submission.Work.BoseFixB1B.cutFibreMass_facts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.PortSmallB.WinW` — the cube-window layer of the fibre port

The fibre bookkeeping of the difference state `slotDiffState L d u (γ δ) ψ` — the pointwise bound
on the derivative of the windowed slot fibre, together with the `χ`-generic helpers it rests on —
proved at the **cube** window `chiSmallB M L d u` (the window of the matched sliding word) rather
than at the ball window `chiB L d u`.

Everything here is a port of the PROVED ball-window material
(`Submission/Work/BoseFixB1B/B1Bfix2/{CutFibreBase,fibreDirI_diff_tendstoB}.lean`): the window
enters only through

* a **swap** `chiB L d u ↦ chiSmallB M L d u` (with the sup constant `chiSup ^ 2 ↦ kappaS M`),
* its **linear vanishing** `chiSmallB_abs_le_boxMargin` (`Winchk`),
* its **differentiability** `contDiff_three_chiSmallB` (needs `4 ≤ M`; `chiSmallB M` is `C^{M-1}`).

The two genuinely window-independent ingredients are factored out:

* `fderiv_window_fibreModelW` — the product rule for `χ * (fibreModel − b)`, for an **arbitrary**
  window `χ` differentiable at the point;
* `fderiv_window_Gfun_fibreW` — the resulting explicit derivative of the windowed slot fibre of
  `G δ`, again for an arbitrary differentiable window.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube.PortSmallB

open Submission.BoseGases
open Work.BoseFixB1B
open Work.BoseFixB1B.B1Bfix

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 0. The difference state at an inserted configuration -/

/-- The slot-`i` fibre of the difference state, in terms of the products of cutoffs. -/
theorem slotDiffState_kcInsN_eqW {n : ℕ} {L d : ℝ} (u : E3) (γ : E3 → ℝ)
    (ψ : X (n+1) → ℝ) (i : Fin (n+1)) (z : E3)
    (r : X n) :
    Work.BoseFixB1B.B1Bfix.slotDiffState L d u γ ψ (Submission.BoseGases.kcInsN n i (z, r))
      = (Work.BoseFixB1B.Fprod γ (Submission.BoseGases.kcInsN n i (z, r))
          - Work.BoseFixB1B.FprodB (Submission.BoseGases.dlBox L d u)
              (Submission.BoseGases.kcInsN n i (z, r)))
        * ψ (Submission.BoseGases.kcInsN n i (z, r)) := by
  rw [Work.BoseFixB1B.B1Bfix.slotDiffState_apply, Work.BoseFixB1B.cutProd_eq_Fprod,
    Work.BoseFixB1B.sharpBoxState_eq_FprodB]
  ring


/-! ## 1. Elementary product estimates (window-independent) -/
/-- A product of numbers each of which is `0` or `1` has modulus at most `1`. -/
lemma abs_prod_le_one_of_zero_or_oneW {ι : Type*} (s : Finset ι) (b : ι → ℝ)
    (hb : ∀ i ∈ s, b i = 0 ∨ b i = 1) : |∏ i ∈ s, b i| ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx]
    have hb' : ∀ i ∈ s, b i = 0 ∨ b i = 1 := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hbx := hb x (Finset.mem_insert_self x s)
    calc |b x * ∏ i ∈ s, b i| = |b x| * |∏ i ∈ s, b i| := abs_mul _ _
      _ ≤ 1 * 1 := by
          refine mul_le_mul ?_ (ih hb') (abs_nonneg _) zero_le_one
          rcases hbx with h | h <;> rw [h] <;> norm_num
      _ = 1 := one_mul 1

/-- **Telescoping bound for products**: a product of numbers in `[0,1]` differs from a product of
`0–1` numbers by at most the sum of the coordinatewise differences. -/
lemma abs_prod_sub_prod_le_sumW {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) (hb : ∀ i ∈ s, b i = 0 ∨ b i = 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have ha0' : ∀ i ∈ s, 0 ≤ a i := fun i hi => ha0 i (Finset.mem_insert_of_mem hi)
    have ha1' : ∀ i ∈ s, a i ≤ 1 := fun i hi => ha1 i (Finset.mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, b i = 0 ∨ b i = 1 := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have ih' := ih ha0' ha1' hb'
    rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.sum_insert hx]
    have hB : |∏ i ∈ s, b i| ≤ 1 := abs_prod_le_one_of_zero_or_oneW s b hb'
    have hax : 0 ≤ a x := ha0 x (Finset.mem_insert_self x s)
    have hax1 : a x ≤ 1 := ha1 x (Finset.mem_insert_self x s)
    have key : |a x * (∏ i ∈ s, a i) - b x * (∏ i ∈ s, b i)|
        ≤ |∏ i ∈ s, a i - ∏ i ∈ s, b i| + |a x - b x| := by
      have hsplit : a x * (∏ i ∈ s, a i) - b x * (∏ i ∈ s, b i)
          = a x * ((∏ i ∈ s, a i) - (∏ i ∈ s, b i))
            + (a x - b x) * (∏ i ∈ s, b i) := by ring
      rw [hsplit]
      have h1 : a x * |(∏ i ∈ s, a i) - (∏ i ∈ s, b i)|
          ≤ |(∏ i ∈ s, a i) - (∏ i ∈ s, b i)| :=
        mul_le_of_le_one_left (abs_nonneg _) hax1
      have h2 : |a x - b x| * |∏ i ∈ s, b i| ≤ |a x - b x| :=
        mul_le_of_le_one_right (abs_nonneg _) hB
      calc |a x * ((∏ i ∈ s, a i) - (∏ i ∈ s, b i))
              + (a x - b x) * (∏ i ∈ s, b i)|
          ≤ |a x * ((∏ i ∈ s, a i) - (∏ i ∈ s, b i))|
            + |(a x - b x) * (∏ i ∈ s, b i)| := abs_add_le _ _
        _ = a x * |(∏ i ∈ s, a i) - (∏ i ∈ s, b i)| + |a x - b x| * |∏ i ∈ s, b i| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hax]
        _ ≤ |(∏ i ∈ s, a i) - (∏ i ∈ s, b i)| + |a x - b x| := by linarith
    linarith [key, ih']


/-! ## 2. The generic derivative of the windowed local model -/
/-- The derivative of the windowed local model for an arbitrary window `χ`. -/
lemma fderiv_window_fibreModelW {n : ℕ}
    {g : E3 → ℝ} (hg : ContDiff ℝ (⊤ : ENat) g) {ψ : Submission.BoseGases.X (n + 1) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (i : Fin (n + 1)) (r : Submission.BoseGases.X n)
    (c b : ℝ) {χ : E3 → ℝ} {y : E3} (hχ : DifferentiableAt ℝ χ y) (k : Fin 3) :
    fderiv ℝ (χ * ((fibreModel g ψ i r c) - (fun _ : E3 => b))) y (kcStdBasis k)
      = χ y
          * ((Fprod g (kcInsN n i (y, r)) - c)
                * fderiv ℝ ψ (kcInsN n i (y, r)) (kcDir (n + 1) i k)
              + fderiv ℝ (Fprod g) (kcInsN n i (y, r)) (kcDir (n + 1) i k)
                * ψ (kcInsN n i (y, r)))
        + fderiv ℝ χ y (kcStdBasis k)
          * ((Fprod g (kcInsN n i (y, r)) - c) * ψ (kcInsN n i (y, r)) - b) := by
  have hm : ContDiff ℝ (⊤ : ENat) ((fibreModel g ψ i r c) - (fun _ : E3 => b)) :=
    (contDiff_fibreModel hg hψ i r c).sub contDiff_const
  have hmd : DifferentiableAt ℝ ((fibreModel g ψ i r c) - (fun _ : E3 => b)) y :=
    hm.differentiable (by simp) y
  have hmul := congrArg (fun (L' : E3 →L[ℝ] ℝ) => L' (kcStdBasis k))
    (fderiv_mul hχ hmd)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at hmul
  have h2 : fderiv ℝ ((fibreModel g ψ i r c) - (fun _ : E3 => b)) y (kcStdBasis k)
      = fderiv ℝ (fibreModel g ψ i r c) y (kcStdBasis k) := by
    rw [fderiv_sub ((contDiff_fibreModel hg hψ i r c).differentiable (by simp) y)
      (differentiableAt_const b)]
    simp
  rw [h2, fderiv_fibreModel hg hψ i r c y k] at hmul
  have hval : ((fibreModel g ψ i r c) - (fun _ : E3 => b)) y
      = (Fprod g (kcInsN n i (y, r)) - c) * ψ (kcInsN n i (y, r)) - b := rfl
  rw [hval] at hmul
  rw [hmul]
  try ring_nf

/-! ## 3. The generic derivative of the windowed slot fibre of `G δ` -/
/-- **The derivative of the windowed slot-`i` fibre of `G δ`.**  At every configuration whose
slot-`i` coordinate has nonzero box margin, the Leibniz rule and the local constancy of the
sharp part give an explicit expression for the derivative. -/
theorem fderiv_window_Gfun_fibreW {L d : ℝ} (hL : 0 < L) (hd : 0 < d) {K : ℝ} {γ : ℝ → E3 → ℝ}
    {u : E3} {hcut : IsCutFamily L d u K γ} {n : ℕ} {ψ : Submission.BoseGases.X (n + 1) → ℝ}
    {hψ : ContDiff ℝ (⊤ : ENat) ψ} {δ : ℝ} (hδ : 0 < δ) (i : Fin (n + 1)) (k : Fin 3)
    {χ : E3 → ℝ} {y : E3} {r : Submission.BoseGases.X n} (hy : boxMargin L d u y ≠ 0)
    (hχ : DifferentiableAt ℝ χ y) :
    fderiv ℝ (fun z : E3 => χ z * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i (Gfun (γ δ) ψ (Submission.BoseGases.dlBox L d u))
        (kcInsN n i (z, r))) y (kcStdBasis k)
      = χ y
          * ((Fprod (γ δ) (kcInsN n i (y, r))
                - FprodB (Submission.BoseGases.dlBox L d u) (kcInsN n i (y, r)))
              * fderiv ℝ ψ (kcInsN n i (y, r)) (kcDir (n + 1) i k)
            + fderiv ℝ (Fprod (γ δ)) (kcInsN n i (y, r)) (kcDir (n + 1) i k)
              * ψ (kcInsN n i (y, r)))
        + fderiv ℝ χ y (kcStdBasis k)
          * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.dlBox L d u) i
              (Gfun (γ δ) ψ (Submission.BoseGases.dlBox L d u)) (kcInsN n i (y, r))  := by
  have hcd : ContDiff ℝ (⊤ : ENat) (γ δ) := (hcut.2 δ hδ).1
  set b : ℝ := Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass L d u)
    (Submission.BoseGases.dlBox L d u) i (Gfun (γ δ) ψ (Submission.BoseGases.dlBox L d u))
    (kcInsN n i (y, r)) with hb
  have hP : ∀ z : E3, Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass L d u)
      (Submission.BoseGases.dlBox L d u) i (Gfun (γ δ) ψ (Submission.BoseGases.dlBox L d u))
      (kcInsN n i (z, r)) = b := by
    intro z
    rw [hb]
    exact boxP_kcInsN_eq _ i _ z y r
  have hG := Gfun_fibre_eventuallyEq (L := L) (d := d) (u := u) (n := n) (g := γ δ)
    (ψ := ψ) i r (y := y) hy
  have hmain : (fun z : E3 => χ z
        * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i (Gfun (γ δ) ψ (Submission.BoseGases.dlBox L d u))
          (kcInsN n i (z, r)))
      =ᶠ[𝓝 y] χ * ((fibreModel (γ δ) ψ i r
          (FprodB (Submission.BoseGases.dlBox L d u) (kcInsN n i (y, r))))
            - (fun _ : E3 => b)) := by
    filter_upwards [hG] with z hz
    rw [Work.SmallBoxTBWord.boxQ, hz, hP z]
    simp only [Pi.mul_apply, Pi.sub_apply]
  rw [Filter.EventuallyEq.fderiv_eq hmain]
  rw [fderiv_window_fibreModelW hcd hψ i r _ b hχ k]
  have hx₀ : Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i
        (Gfun (γ δ) ψ (Submission.BoseGases.dlBox L d u)) (kcInsN n i (y, r))
      = (Fprod (γ δ) (kcInsN n i (y, r))
          - FprodB (Submission.BoseGases.dlBox L d u) (kcInsN n i (y, r)))
          * ψ (kcInsN n i (y, r)) - b := by
    rw [hb, Work.SmallBoxTBWord.boxQ, Gfun_apply]
    try ring_nf
  rw [hx₀]
  try ring_nf

/-! ## 4. The product difference at an inserted configuration (window-independent) -/
/-! ## 4. The product difference at an inserted configuration -/

/-- **The two products differ only on the collar**: for the inserted configuration
`kcInsN n i (y,r)`, the product of the cutoffs and the product of the box indicators differ by at
most the sum of the collar indicators of the slot-`i` variable `y` and of the outside
coordinates `r`. -/
lemma abs_Fprod_sub_FprodB_kcInsN_leW {n : ℕ} {L d : ℝ} {K : ℝ} {γ : ℝ → E3 → ℝ}
    {u : E3} (hcut : IsCutFamily L d u K γ) {δ : ℝ} (hδ : 0 < δ) (i : Fin (n+1)) (y : E3)
    (r : Submission.BoseGases.X n) :
    |Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
        - FprodB (Submission.BoseGases.dlBox L d u) (Submission.BoseGases.kcInsN n i (y, r))|
      ≤ collarInd L d u δ y + ∑ j : Fin n, collarInd L d u δ (r j) := by
  classical
  have hbdd := (hcut.2 δ hδ).2.2.1
  have hP0 : 0 ≤ ∏ j : Fin n, γ δ (r j) := Finset.prod_nonneg (fun j _ => (hbdd (r j)).1)
  have hP1 : ∏ j : Fin n, γ δ (r j) ≤ 1 :=
    Finset.prod_le_one₀ (fun j _ => (hbdd (r j)).1) (fun j _ => (hbdd (r j)).2)
  have hdiff : |∏ j : Fin n, γ δ (r j) - FprodBr (Submission.BoseGases.dlBox L d u) r|
      ≤ ∑ j : Fin n, collarInd L d u δ (r j) := by
    have h := abs_prod_sub_prod_le_sumW (s := (Finset.univ : Finset (Fin n)))
      (a := fun j => γ δ (r j))
      (b := fun j => (Submission.BoseGases.dlBox L d u).indicator (fun _ => (1:ℝ)) (r j))
      (fun j _ => (hbdd (r j)).1) (fun j _ => (hbdd (r j)).2)
      (fun j _ => by
        by_cases hj : r j ∈ Submission.BoseGases.dlBox L d u
        · exact Or.inr (Set.indicator_of_mem hj _)
        · exact Or.inl (Set.indicator_of_notMem hj _))
    refine h.trans ?_
    exact Finset.sum_le_sum
      (fun j _ => abs_gamma_sub_indicator_le_collarInd (hcut := hcut) hδ (r j))
  have hmain : |γ δ y * (∏ j : Fin n, γ δ (r j))
        - (Submission.BoseGases.dlBox L d u).indicator (fun _ => (1:ℝ)) y
          * FprodBr (Submission.BoseGases.dlBox L d u) r|
      ≤ collarInd L d u δ y + ∑ j : Fin n, collarInd L d u δ (r j) := by
    have hrepr : γ δ y * (∏ j : Fin n, γ δ (r j))
          - (Submission.BoseGases.dlBox L d u).indicator (fun _ => (1:ℝ)) y
            * FprodBr (Submission.BoseGases.dlBox L d u) r
        = (γ δ y - (Submission.BoseGases.dlBox L d u).indicator (fun _ => (1:ℝ)) y)
            * (∏ j : Fin n, γ δ (r j))
          + (Submission.BoseGases.dlBox L d u).indicator (fun _ => (1:ℝ)) y
            * ((∏ j : Fin n, γ δ (r j)) - FprodBr (Submission.BoseGases.dlBox L d u) r) := by
      ring
    rw [hrepr]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have hInd : |(Submission.BoseGases.dlBox L d u).indicator (fun _ => (1:ℝ)) y| ≤ 1 := by
      by_cases h : y ∈ Submission.BoseGases.dlBox L d u
      · rw [Set.indicator_of_mem h]; norm_num
      · rw [Set.indicator_of_notMem h]; norm_num
    calc |γ δ y - (Submission.BoseGases.dlBox L d u).indicator (fun _ => (1:ℝ)) y|
            * |∏ j : Fin n, γ δ (r j)|
          + |(Submission.BoseGases.dlBox L d u).indicator (fun _ => (1:ℝ)) y|
            * |(∏ j : Fin n, γ δ (r j)) - FprodBr (Submission.BoseGases.dlBox L d u) r|
        ≤ collarInd L d u δ y * 1 + 1 * ∑ j : Fin n, collarInd L d u δ (r j) := by
          refine add_le_add ?_ ?_
          · refine mul_le_mul (abs_gamma_sub_indicator_le_collarInd (hcut := hcut) hδ y)
              (by rw [abs_of_nonneg hP0]; exact hP1) (abs_nonneg _) (collarInd_nonneg L d u δ y)
          · exact mul_le_mul hInd hdiff (abs_nonneg _) zero_le_one
      _ = collarInd L d u δ y + ∑ j : Fin n, collarInd L d u δ (r j) := by ring
  have h1 : Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
      = γ δ y * ∏ j : Fin n, γ δ (r j) := by
    rw [Fprod_eq_mul_FprodOther, FprodOther_kcInsN_eq, Submission.BoseGases.kc_insN_apply_same]
  have h2 : FprodB (Submission.BoseGases.dlBox L d u) (Submission.BoseGases.kcInsN n i (y, r))
      = (Submission.BoseGases.dlBox L d u).indicator (fun _ => (1:ℝ)) y
        * FprodBr (Submission.BoseGases.dlBox L d u) r := FprodB_kcInsN_eq i y r
  rw [h1, h2]
  exact hmain

/-! ## 5. The collar indicator integrated over the sliding box (window-independent) -/
/-! ## 5. The mean-free projection of the difference state at an inserted configuration -/

/-- The collar indicator is supported in the sliding box, so its integral over the box is its
integral over `ℝ³`. -/
lemma setIntegral_collarInd_dlBoxW {L d : ℝ} (u : E3) (δ : ℝ) :
    (∫ z in Submission.BoseGases.dlBox L d u, collarInd L d u δ z) = ∫ z : E3, collarInd L d u δ z := by
  refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (f := fun z : E3 => collarInd L d u δ z) (s := Submission.BoseGases.dlBox L d u)
    (fun z hz => ?_)
  rw [collarInd_eq_indicator]
  exact Set.indicator_of_notMem (fun hmem => hz hmem.1) _

/-! ## 6. The mean-free projection at an inserted configuration (window-independent) -/
/-- **The mean-free projection of `W_δ` at an inserted configuration is `O(δ)`-small**: both the
value and the box mean of `W_δ` are bounded by `Cb` times a sum of collar indicators (plus the
normalised collar volume, which is itself `O(δ)`). -/
lemma abs_boxQ_diff_kcInsN_leW {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3)
    {K : ℝ} {γ : ℝ → E3 → ℝ} {δ : ℝ} (hcut : IsCutFamily L d u K γ) (hδ : 0 < δ)
    {ψ : Submission.BoseGases.X (n+1) → ℝ} {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hψb : ∀ x ∈ Submission.BoseGases.abox (n+1) L, |ψ x| ≤ Cb)
    (i : Fin (n+1)) {y : E3} (hy : y ∈ Submission.BoseGases.acube L)
    {r : Submission.BoseGases.X n} (hr : r ∈ Submission.BoseGases.abox n L) :
    |Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
        (Submission.BoseGases.kcInsN n i (y, r))|
      ≤ Cb * (collarInd L d u δ y + ∑ j : Fin n, collarInd L d u δ (r j))
        + Cb * ((∫ z : E3, collarInd L d u δ z) / Work.SmallBoxSliding.boxMass L d u
            + ∑ j : Fin n, collarInd L d u δ (r j)) := by
  classical
  set A : Set E3 := Submission.BoseGases.dlBox L d u with hA
  set volA : ℝ := Work.SmallBoxSliding.boxMass L d u with hvolA
  set S : ℝ := ∑ j : Fin n, collarInd L d u δ (r j) with hS
  set V : ℝ := ∫ z : E3, collarInd L d u δ z with hV
  have hS0 : 0 ≤ S := by
    rw [hS]; exact Finset.sum_nonneg (fun j _ => collarInd_nonneg L d u δ (r j))
  have hV0 : 0 ≤ V := by
    rw [hV]; exact integral_nonneg (fun z => collarInd_nonneg L d u δ z)
  have hvol_eq : volA = (volume : Measure E3).real A := by
    rw [hvolA, hA]; exact Work.SmallBoxSliding.boxMass_eq_measureReal L d u
  have hvol0 : 0 ≤ volA := by rw [hvol_eq]; exact measureReal_nonneg
  have hfin : (volume : Measure E3) A < ⊤ := by
    rw [hA]; exact (Work.SmallBoxTBWord.isCompact_dlBox hL hd u).measure_lt_top
  have hAmeas : MeasurableSet A := by
    rw [hA]; exact Work.SmallBoxSliding.measurableSet_dlBox L d u
  have hAsub : A ⊆ Submission.BoseGases.acube L := by
    rw [hA]; exact Work.SmallBoxSliding.dlBox_subset_acube L d u
  have hW : ∀ z : E3, slotDiffState L d u (γ δ) ψ (Submission.BoseGases.kcInsN n i (z, r))
      = (Fprod (γ δ) (Submission.BoseGases.kcInsN n i (z, r))
          - FprodB A (Submission.BoseGases.kcInsN n i (z, r)))
        * ψ (Submission.BoseGases.kcInsN n i (z, r)) := by
    intro z
    rw [slotDiffState_apply, cutProd_eq_Fprod, sharpBoxState_eq_FprodB]
    ring
  have hcoef : ∀ z : E3, |Fprod (γ δ) (Submission.BoseGases.kcInsN n i (z, r))
        - FprodB A (Submission.BoseGases.kcInsN n i (z, r))|
      ≤ collarInd L d u δ z + S := by
    intro z
    simpa only [hA, hS] using abs_Fprod_sub_FprodB_kcInsN_leW (n := n) (L := L) (d := d)
      (K := K) (γ := γ) (u := u) hcut hδ i z r
  have hψmem : ∀ z : E3, z ∈ Submission.BoseGases.acube L →
      |ψ (Submission.BoseGases.kcInsN n i (z, r))| ≤ Cb := fun z hz =>
    hψb _ (kcInsN_mem_abox i hz ((mem_abox_iff n L r).mp hr))
  -- (a) the pointwise bound of the state
  have hpt : ∀ z : E3, z ∈ Submission.BoseGases.acube L → |slotDiffState L d u (γ δ) ψ
      (Submission.BoseGases.kcInsN n i (z, r))| ≤ Cb * (collarInd L d u δ z + S) := by
    intro z hz
    rw [hW z, abs_mul]
    calc |Fprod (γ δ) (Submission.BoseGases.kcInsN n i (z, r))
            - FprodB A (Submission.BoseGases.kcInsN n i (z, r))|
            * |ψ (Submission.BoseGases.kcInsN n i (z, r))|
        ≤ (collarInd L d u δ z + S) * Cb :=
          mul_le_mul (hcoef z) (hψmem z hz) (abs_nonneg _)
            (add_nonneg (collarInd_nonneg L d u δ z) hS0)
      _ = Cb * (collarInd L d u δ z + S) := by ring
  -- (b) the bound on the box mean
  have hcint : IntegrableOn (fun z : E3 => collarInd L d u δ z) A volume :=
    IntegrableOn.of_bound hfin (Work.BoseFixB1B.measurable_collarInd L d u δ).aestronglyMeasurable 1
      (by
        rw [ae_restrict_iff' hAmeas]
        refine ae_of_all _ (fun z _ => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (collarInd_nonneg L d u δ z)]
        exact collarInd_le_one L d u δ z)
  have hsint : IntegrableOn (fun _ : E3 => S) A volume :=
    integrableOn_const (μ := volume) (s := A) (ne_of_lt hfin) (by simp)
  have hmean : |(1 / volA) * ∫ z in A, slotDiffState L d u (γ δ) ψ
      (Submission.BoseGases.kcInsN n i (z, r))| ≤ Cb * (V / volA + S) := by
    have hβint : IntegrableOn (fun z : E3 => Cb * (collarInd L d u δ z + S)) A volume :=
      (hcint.add hsint).const_mul Cb
    have hle : (∫ z in A, |slotDiffState L d u (γ δ) ψ
          (Submission.BoseGases.kcInsN n i (z, r))|)
        ≤ ∫ z in A, Cb * (collarInd L d u δ z + S) :=
      setIntegral_le_of_le_ae hAmeas hβint
        (fun z _ => mul_nonneg hCb (add_nonneg (collarInd_nonneg L d u δ z) hS0))
        (fun z hz => hpt z (hAsub hz))
    have habs : |∫ z in A, slotDiffState L d u (γ δ) ψ
        (Submission.BoseGases.kcInsN n i (z, r))|
        ≤ ∫ z in A, |slotDiffState L d u (γ δ) ψ
            (Submission.BoseGases.kcInsN n i (z, r))| := by
      simpa only [Real.norm_eq_abs] using
        MeasureTheory.norm_integral_le_integral_norm
          (μ := (volume : Measure E3).restrict A)
          (f := fun z : E3 => slotDiffState L d u (γ δ) ψ
            (Submission.BoseGases.kcInsN n i (z, r)))
    have hvalue : (∫ z in A, Cb * (collarInd L d u δ z + S)) = Cb * (V + S * volA) := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hcint hsint,
        setIntegral_collarInd_dlBoxW u δ, setIntegral_const]
      rw [hV, hvol_eq, smul_eq_mul]
      ring
    have hstep : |∫ z in A, slotDiffState L d u (γ δ) ψ
        (Submission.BoseGases.kcInsN n i (z, r))| ≤ Cb * (V + S * volA) := by
      rw [hvalue] at hle
      exact habs.trans hle
    rw [abs_mul]
    have h1 : |(1 : ℝ) / volA| = 1 / volA := by
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / volA)]
    rw [h1]
    have hvv : (1 / volA) * (V + S * volA) ≤ V / volA + S := by
      have h2 : (1 / volA) * (S * volA) ≤ S := by
        rcases eq_or_ne volA 0 with hv0 | hv0
        · rw [hv0, div_zero, zero_mul]
          exact hS0
        · rw [one_div]
          exact le_of_eq (by rw [mul_comm S volA, ← mul_assoc, inv_mul_cancel₀ hv0, one_mul])
      have h1' : (1 / volA) * V = V / volA := by ring
      calc (1 / volA) * (V + S * volA)
          = (1 / volA) * V + (1 / volA) * (S * volA) := by ring
        _ ≤ V / volA + S := by
            rw [h1']
            exact add_le_add le_rfl h2
    calc (1 / volA) * |∫ z in A, slotDiffState L d u (γ δ) ψ
          (Submission.BoseGases.kcInsN n i (z, r))|
        ≤ (1 / volA) * (Cb * (V + S * volA)) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = Cb * ((1 / volA) * (V + S * volA)) := by ring
      _ ≤ Cb * (V / volA + S) := mul_le_mul_of_nonneg_left hvv hCb
  -- assembling the mean-free projection
  have hboxQ := boxQ_kcInsN_eq (n := n) i volA A (slotDiffState L d u (γ δ) ψ) y r
  rw [hboxQ]
  calc |slotDiffState L d u (γ δ) ψ (Submission.BoseGases.kcInsN n i (y, r))
        - 1 / volA * ∫ z in A, slotDiffState L d u (γ δ) ψ
            (Submission.BoseGases.kcInsN n i (z, r))|
      ≤ |slotDiffState L d u (γ δ) ψ (Submission.BoseGases.kcInsN n i (y, r))|
        + |1 / volA * ∫ z in A, slotDiffState L d u (γ δ) ψ
            (Submission.BoseGases.kcInsN n i (z, r))| := by
        rw [← Real.norm_eq_abs, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
        exact norm_sub_le _ _
    _ ≤ Cb * (collarInd L d u δ y + S) + Cb * (V / volA + S) :=
        add_le_add (hpt y hy) hmean
    _ = Cb * (collarInd L d u δ y + ∑ j : Fin n, collarInd L d u δ (r j))
        + Cb * ((∫ z : E3, collarInd L d u δ z) / Work.SmallBoxSliding.boxMass L d u
            + ∑ j : Fin n, collarInd L d u δ (r j)) := by
        rw [hS, hV, hvolA]


/-! ## 7. Monotonicity of the set integral from an a.e. hypothesis (window-independent) -/
/-- `∫_s f ≤ ∫_s β` from `f ≤ β` a.e. on `s`, with `β ≥ 0` integrable on `s`.  No integrability
of `f` is assumed (when `f` is not integrable both the integral is `0` and the claim reduces to the
nonnegativity of the right-hand side). -/
lemma setIntegral_le_of_le_aeW {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f β : α → ℝ} (hs : MeasurableSet s) (hβ : IntegrableOn β s μ) (hβ0 : ∀ x ∈ s, 0 ≤ β x)
    (h : ∀ᵐ x ∂(μ.restrict s), f x ≤ β x) : ∫ x in s, f x ∂μ ≤ ∫ x in s, β x ∂μ := by
  by_cases hf : IntegrableOn f s μ
  · exact integral_mono_ae hf hβ h
  · have hf' : ¬ Integrable f (μ.restrict s) := hf
    rw [integral_undef hf']
    exact integral_nonneg_of_ae (by
      filter_upwards [MeasureTheory.ae_restrict_mem hs] with x hx
      exact hβ0 x hx)

/-! ## 8. The `δ`-cancellation: the window kills the `K/δ` of the cutoff derivative -/
/-! ## 3. The `δ`-cancellation: the window kills the `K/δ` of the cutoff derivative -/

/-- On the collar the window vanishes at least linearly in the margin, so
`|χ y · ∂_k(γ δ) y| ≤ C1·K` there; off the collar the cutoff is locally constant and the
derivative vanishes.  Both cases are summarised by the collar indicator. -/
lemma abs_chiWindow_mul_fderiv_gamma_leW {L d : ℝ} (hL : 0 < L) (hd : 0 < d) {K : ℝ}
    {γ : ℝ → E3 → ℝ} {u : E3}
    {hcut : IsCutFamily L d u K γ} {C1 : ℝ} (hC10 : 0 ≤ C1)
    {χ : E3 → ℝ}
    (hC1 : ∀ x ∈ Submission.BoseGases.dlBox L d u,
      |χ x| ≤ C1 * boxMargin L d u x)
    {δ : ℝ} (hδ : 0 < δ) (y : E3) (k : Fin 3) :
    |χ y * fderiv ℝ (γ δ) y (Submission.BoseGases.kcStdBasis k)|
      ≤ C1 * K * collarInd L d u δ y := by
  have hK0 : 0 ≤ K := hcut.1
  by_cases hy : y ∈ Submission.BoseGases.dlBox L d u ∧ boxMargin L d u y ≤ δ
  · have hm0 : 0 ≤ boxMargin L d u y := boxMargin_nonneg_iff.mpr hy.1
    have h1 : |χ y| ≤ C1 * boxMargin L d u y := hC1 y hy.1
    have h2 : |fderiv ℝ (γ δ) y (Submission.BoseGases.kcStdBasis k)| ≤ K / δ := by
      have h := abs_fderiv_gamma_le_collarInd (L := L) (d := d) (hcut := hcut)
        (isClosed_dlBox' hL hd u) hδ y k
      rwa [collarInd_apply_of L d u hy, mul_one] at h
    rw [collarInd_apply_of L d u hy]
    rw [abs_mul]
    have hkey : boxMargin L d u y * (K / δ) ≤ K := by
      have hδne : δ ≠ 0 := ne_of_gt hδ
      have h := mul_le_mul_of_nonneg_right hy.2 (div_nonneg hK0 hδ.le)
      rw [mul_comm δ (K / δ), div_mul_cancel₀ K hδne] at h
      exact h
    calc |χ y| * |fderiv ℝ (γ δ) y (Submission.BoseGases.kcStdBasis k)|
        ≤ (C1 * boxMargin L d u y) * (K / δ) :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hC10 hm0)
      _ = C1 * (boxMargin L d u y * (K / δ)) := by ring
      _ ≤ C1 * K := mul_le_mul_of_nonneg_left hkey hC10
      _ = C1 * K * 1 := by ring
  · rw [collarInd_apply_of_not L d u hy]
    have hzero : fderiv ℝ (γ δ) y = 0 := by
      by_cases hyB : y ∈ Submission.BoseGases.dlBox L d u
      · have hm : δ < boxMargin L d u y := lt_of_not_ge (fun hle => hy ⟨hyB, hle⟩)
        exact fderiv_eq_zero_of_eventuallyEq_const
          (gamma_eventuallyEq_one (hcut := hcut) hδ hm)
      · exact fderiv_eq_zero_of_eventuallyEq_const
          (gamma_eventuallyEq_zero (K := K) (γ := γ) (hcut := hcut)
            (isClosed_dlBox' hL hd u) hδ hyB)
    rw [hzero]
    simp

/-! ## 9. The pointwise bound on the derivative of the windowed cube slot fibre -/
/-- **The pointwise bound on the derivative of the windowed slot fibre** of the difference state,
at a slot position of nonzero box margin.  All three terms of `Work.BoseFixB1B.fderiv_Gfun_fibre`
are bounded by the collar: the two products differ only on the collar, the cutoff derivative is
killed by the linear vanishing of the window, and the window derivative is bounded.

The constant is `27·Λ²` with `Λ = max (chiSup²·Cψ) (max (C1·K·Cb) (2·Cχ·Cb))`. -/
lemma fibre_deriv_sum_sq_leW {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3)
    {M : ℕ} (hM : 4 ≤ M)
    {K : ℝ} {γ : ℝ → E3 → ℝ} {δ : ℝ} (hcut : IsCutFamily L d u K γ) (hδ : 0 < δ)
    {ψ : Submission.BoseGases.X (n+1) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) {Cb : ℝ}
    (hCb : 0 ≤ Cb) (hψb : ∀ x ∈ Submission.BoseGases.abox (n+1) L, |ψ x| ≤ Cb)
    {C1 Cχ Cψ : ℝ} (hC10 : 0 ≤ C1)
    (hC1 : ∀ x ∈ Submission.BoseGases.dlBox L d u,
      |Submission.BoseGases.chiSmallB M L d u x| ≤ C1 * boxMargin L d u x)
    (hCχ : ∀ y : E3, ∀ k : Fin 3,
      |fderiv ℝ (Submission.BoseGases.chiSmallB M L d u) y (Submission.BoseGases.kcStdBasis k)| ≤ Cχ)
    (hCψ0 : 0 ≤ Cψ)
    (hCψ : ∀ x ∈ Submission.BoseGases.abox (n+1) L, ∀ i : Fin (n+1), ∀ k : Fin 3,
      |fderiv ℝ ψ x (Submission.BoseGases.kcDir (n+1) i k)| ≤ Cψ)
    (i : Fin (n+1)) {y : E3} (hy : y ∈ Submission.BoseGases.acube L)
    {r : Submission.BoseGases.X n} (hr : r ∈ Submission.BoseGases.abox n L)
    (hym : boxMargin L d u y ≠ 0) :
    ∑ k : Fin 3, (fderiv ℝ (slotFibreFun (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
        (slotDiffState L d u (γ δ) ψ) r) y (Submission.BoseGases.kcStdBasis k)) ^ 2
      ≤ 27 * (max (Work.BoseB1Cube.Winchk.kappaS M * Cψ)
            (max (C1 * K * Cb) (2 * Cχ * Cb))) ^ 2
        * (collarInd L d u δ y + ∑ j : Fin n, collarInd L d u δ (r j)
            + (∫ z : E3, collarInd L d u δ z) / Work.SmallBoxSliding.boxMass L d u) ^ 2 := by
  classical
  set S : ℝ := ∑ j : Fin n, collarInd L d u δ (r j) with hS
  set V : ℝ := ∫ z : E3, collarInd L d u δ z with hV
  set volA : ℝ := Work.SmallBoxSliding.boxMass L d u with hvolA
  set G : ℝ := collarInd L d u δ y + S + V / volA with hG
  set Lam : ℝ := max (Work.BoseB1Cube.Winchk.kappaS M * Cψ) (max (C1 * K * Cb) (2 * Cχ * Cb))
    with hLam
  have hS0 : 0 ≤ S := by
    rw [hS]; exact Finset.sum_nonneg (fun j _ => collarInd_nonneg L d u δ (r j))
  have hV0 : 0 ≤ V := by
    rw [hV]; exact integral_nonneg (fun z => collarInd_nonneg L d u δ z)
  have hvol0 : 0 ≤ volA := by
    rw [hvolA, Work.SmallBoxSliding.boxMass_eq_measureReal, Measure.real_def]
    positivity
  have hVdiv0 : 0 ≤ V / volA := div_nonneg hV0 hvol0
  have hcoll0 : 0 ≤ collarInd L d u δ y := collarInd_nonneg L d u δ y
  have hG0 : 0 ≤ G := by rw [hG]; exact add_nonneg (add_nonneg hcoll0 hS0) hVdiv0
  have hLam0 : 0 ≤ Lam := by
    rw [hLam]
    exact le_trans (mul_nonneg (Work.BoseB1Cube.Winchk.kappaS_nonneg M) hCψ0) (le_max_left _ _)
  have hK0 : 0 ≤ K := hcut.1
  have hcA : 0 ≤ Work.BoseB1Cube.Winchk.kappaS M * Cψ :=
    mul_nonneg (Work.BoseB1Cube.Winchk.kappaS_nonneg M) hCψ0
  have hcB : 0 ≤ C1 * K * Cb := mul_nonneg (mul_nonneg hC10 hK0) hCb
  have hCχ0 : 0 ≤ Cχ :=
    (abs_nonneg ((fderiv ℝ (Submission.BoseGases.chiSmallB M L d u) y)
      (Submission.BoseGases.kcStdBasis 0))).trans (hCχ y 0)
  have hcC : 0 ≤ 2 * Cχ * Cb := mul_nonneg (mul_nonneg (by norm_num) hCχ0) hCb
  have hχdiff : DifferentiableAt ℝ (Submission.BoseGases.chiSmallB M L d u) y :=
    ((Work.BoseFixB1S.win.contDiff_three_chiSmallB hM hL hd u).differentiable (by norm_num)) y
  -- the fibre derivative identity
  have hfib : ∀ k : Fin 3, fderiv ℝ (slotFibreFun (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
        (slotDiffState L d u (γ δ) ψ) r) y (Submission.BoseGases.kcStdBasis k)
      = Submission.BoseGases.chiSmallB M L d u y
          * ((Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
                - FprodB (Submission.BoseGases.dlBox L d u) (Submission.BoseGases.kcInsN n i (y, r)))
              * fderiv ℝ ψ (Submission.BoseGases.kcInsN n i (y, r))
                  (Submission.BoseGases.kcDir (n + 1) i k)
            + fderiv ℝ (Fprod (γ δ)) (Submission.BoseGases.kcInsN n i (y, r))
                (Submission.BoseGases.kcDir (n + 1) i k)
              * ψ (Submission.BoseGases.kcInsN n i (y, r)))
        + fderiv ℝ (Submission.BoseGases.chiSmallB M L d u) y (Submission.BoseGases.kcStdBasis k)
          * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
              (Submission.BoseGases.kcInsN n i (y, r)) := by
    intro k
    have heq : slotFibreFun (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiSmallB M L d u) i (slotDiffState L d u (γ δ) ψ) r
        = fun z : E3 => Submission.BoseGases.chiSmallB M L d u z
            * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i
              (Gfun (γ δ) ψ (Submission.BoseGases.dlBox L d u))
              (Submission.BoseGases.kcInsN n i (z, r)) := by
      funext z
      rfl
    rw [heq]
    exact fderiv_window_Gfun_fibreW (L := L) (d := d) hL hd (hcut := hcut) (n := n) (ψ := ψ)
      (hψ := hψ) (δ := δ) hδ i k (r := r) (y := y) hym hχdiff
  -- the auxiliary bounds
  have hψmem : ∀ z : E3, z ∈ Submission.BoseGases.acube L →
      |ψ (Submission.BoseGases.kcInsN n i (z, r))| ≤ Cb := fun z hz =>
    hψb _ (kcInsN_mem_abox i hz ((mem_abox_iff n L r).mp hr))
  have hPsplit : |Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
      - FprodB (Submission.BoseGases.dlBox L d u) (Submission.BoseGases.kcInsN n i (y, r))|
      ≤ collarInd L d u δ y + S := by
    simpa only [hS] using abs_Fprod_sub_FprodB_kcInsN_leW (n := n) (L := L) (d := d)
      (K := K) (γ := γ) (u := u) hcut hδ i y r
  have hx : |Submission.BoseGases.chiSmallB M L d u y| ≤ Work.BoseB1Cube.Winchk.kappaS M :=
    Work.BoseB1Cube.Winchk.abs_chiSmallB_le_kappaS (by omega) (ℓ := L) (d := d) u y
  have hPle : |∏ j : Fin n, γ δ (r j)| ≤ 1 := by
    have hbdd := (hcut.2 δ hδ).2.2.1
    rw [abs_of_nonneg (Finset.prod_nonneg (fun j _ => (hbdd (r j)).1))]
    exact Finset.prod_le_one₀ (fun j _ => (hbdd (r j)).1) (fun j _ => (hbdd (r j)).2)
  have hχγ : ∀ k : Fin 3, |Submission.BoseGases.chiSmallB M L d u y
      * fderiv ℝ (γ δ) y (Submission.BoseGases.kcStdBasis k)| ≤ C1 * K * collarInd L d u δ y :=
    fun k => abs_chiWindow_mul_fderiv_gamma_leW (L := L) (d := d) hL hd (hcut := hcut) (C1 := C1)
      hC10 hC1 hδ y k
  -- the first two terms of the fibre derivative
  have h12 : ∀ k : Fin 3, |Submission.BoseGases.chiSmallB M L d u y
        * ((Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
              - FprodB (Submission.BoseGases.dlBox L d u) (Submission.BoseGases.kcInsN n i (y, r)))
            * fderiv ℝ ψ (Submission.BoseGases.kcInsN n i (y, r))
                (Submission.BoseGases.kcDir (n + 1) i k)
          + fderiv ℝ (Fprod (γ δ)) (Submission.BoseGases.kcInsN n i (y, r))
              (Submission.BoseGases.kcDir (n + 1) i k)
            * ψ (Submission.BoseGases.kcInsN n i (y, r)))|
      ≤ (Work.BoseB1Cube.Winchk.kappaS M * Cψ + C1 * K * Cb) * G := by
    intro k
    have hψder : |fderiv ℝ ψ (Submission.BoseGases.kcInsN n i (y, r))
        (Submission.BoseGases.kcDir (n + 1) i k)| ≤ Cψ :=
      hCψ _ (kcInsN_mem_abox i hy ((mem_abox_iff n L r).mp hr)) i k
    have hψv : |ψ (Submission.BoseGases.kcInsN n i (y, r))| ≤ Cb := hψmem y hy
    have hFd' : |fderiv ℝ (Fprod (γ δ)) (Submission.BoseGases.kcInsN n i (y, r))
        (Submission.BoseGases.kcDir (n + 1) i k)|
        = |(∏ j : Fin n, γ δ (r j)) * fderiv ℝ (γ δ) y (Submission.BoseGases.kcStdBasis k)| := by
      rw [fderiv_Fprod_kcDir (hcut.2 δ hδ).1 i (Submission.BoseGases.kcInsN n i (y, r)) k,
        Submission.BoseGases.kc_insN_apply_same, FprodOther_kcInsN_eq]
    -- the first term
    have ht1 : |Submission.BoseGases.chiSmallB M L d u y
        * ((Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
              - FprodB (Submission.BoseGases.dlBox L d u) (Submission.BoseGases.kcInsN n i (y, r)))
            * fderiv ℝ ψ (Submission.BoseGases.kcInsN n i (y, r))
                (Submission.BoseGases.kcDir (n + 1) i k))|
        ≤ Work.BoseB1Cube.Winchk.kappaS M * Cψ * (collarInd L d u δ y + S) := by
      have hsh : |Submission.BoseGases.chiSmallB M L d u y
          * ((Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
                - FprodB (Submission.BoseGases.dlBox L d u)
                  (Submission.BoseGases.kcInsN n i (y, r)))
              * fderiv ℝ ψ (Submission.BoseGases.kcInsN n i (y, r))
                  (Submission.BoseGases.kcDir (n + 1) i k))|
          = |Submission.BoseGases.chiSmallB M L d u y|
            * (|Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
                - FprodB (Submission.BoseGases.dlBox L d u) (Submission.BoseGases.kcInsN n i (y, r))|
              * |fderiv ℝ ψ (Submission.BoseGases.kcInsN n i (y, r))
                  (Submission.BoseGases.kcDir (n + 1) i k)|) := by
        rw [abs_mul, abs_mul]
      rw [hsh]
      have hstep : |Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
            - FprodB (Submission.BoseGases.dlBox L d u) (Submission.BoseGases.kcInsN n i (y, r))|
            * |fderiv ℝ ψ (Submission.BoseGases.kcInsN n i (y, r))
                (Submission.BoseGases.kcDir (n + 1) i k)|
          ≤ (collarInd L d u δ y + S) * Cψ := by
        calc _ ≤ (collarInd L d u δ y + S)
              * |fderiv ℝ ψ (Submission.BoseGases.kcInsN n i (y, r))
                  (Submission.BoseGases.kcDir (n + 1) i k)| :=
              mul_le_mul_of_nonneg_right hPsplit (abs_nonneg _)
          _ ≤ (collarInd L d u δ y + S) * Cψ :=
              mul_le_mul_of_nonneg_left hψder (add_nonneg hcoll0 hS0)
      calc |Submission.BoseGases.chiSmallB M L d u y|
            * (|Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
                - FprodB (Submission.BoseGases.dlBox L d u) (Submission.BoseGases.kcInsN n i (y, r))|
              * |fderiv ℝ ψ (Submission.BoseGases.kcInsN n i (y, r))
                  (Submission.BoseGases.kcDir (n + 1) i k)|)
          ≤ Work.BoseB1Cube.Winchk.kappaS M
            * (|Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
                - FprodB (Submission.BoseGases.dlBox L d u) (Submission.BoseGases.kcInsN n i (y, r))|
              * |fderiv ℝ ψ (Submission.BoseGases.kcInsN n i (y, r))
                  (Submission.BoseGases.kcDir (n + 1) i k)|) :=
            mul_le_mul_of_nonneg_right hx (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ ≤ Work.BoseB1Cube.Winchk.kappaS M * ((collarInd L d u δ y + S) * Cψ) :=
            mul_le_mul_of_nonneg_left hstep (Work.BoseB1Cube.Winchk.kappaS_nonneg M)
        _ = Work.BoseB1Cube.Winchk.kappaS M * Cψ * (collarInd L d u δ y + S) := by ring
    -- the second term
    have ht2 : |Submission.BoseGases.chiSmallB M L d u y
        * (fderiv ℝ (Fprod (γ δ)) (Submission.BoseGases.kcInsN n i (y, r))
              (Submission.BoseGases.kcDir (n + 1) i k)
            * ψ (Submission.BoseGases.kcInsN n i (y, r)))|
        ≤ C1 * K * Cb * collarInd L d u δ y := by
      have hsh : |Submission.BoseGases.chiSmallB M L d u y
          * (fderiv ℝ (Fprod (γ δ)) (Submission.BoseGases.kcInsN n i (y, r))
                (Submission.BoseGases.kcDir (n + 1) i k)
              * ψ (Submission.BoseGases.kcInsN n i (y, r)))|
          = (|Submission.BoseGases.chiSmallB M L d u y|
              * |fderiv ℝ (γ δ) y (Submission.BoseGases.kcStdBasis k)|)
            * |∏ j : Fin n, γ δ (r j)|
            * |ψ (Submission.BoseGases.kcInsN n i (y, r))| := by
        simp only [abs_mul, hFd']
        ring
      rw [hsh]
      have hstep1 : |Submission.BoseGases.chiSmallB M L d u y|
            * |fderiv ℝ (γ δ) y (Submission.BoseGases.kcStdBasis k)|
          ≤ C1 * K * collarInd L d u δ y := by
        rw [← abs_mul]
        exact hχγ k
      have hstep2 : (|Submission.BoseGases.chiSmallB M L d u y|
              * |fderiv ℝ (γ δ) y (Submission.BoseGases.kcStdBasis k)|)
            * |∏ j : Fin n, γ δ (r j)| ≤ (C1 * K * collarInd L d u δ y) * 1 := by
        calc _ ≤ (C1 * K * collarInd L d u δ y) * |∏ j : Fin n, γ δ (r j)| :=
              mul_le_mul_of_nonneg_right hstep1 (abs_nonneg _)
          _ ≤ (C1 * K * collarInd L d u δ y) * 1 :=
              mul_le_mul_of_nonneg_left hPle (mul_nonneg (mul_nonneg hC10 hK0) hcoll0)
      calc (|Submission.BoseGases.chiSmallB M L d u y|
              * |fderiv ℝ (γ δ) y (Submission.BoseGases.kcStdBasis k)|)
            * |∏ j : Fin n, γ δ (r j)|
            * |ψ (Submission.BoseGases.kcInsN n i (y, r))|
          ≤ ((C1 * K * collarInd L d u δ y) * 1)
            * |ψ (Submission.BoseGases.kcInsN n i (y, r))| :=
            mul_le_mul_of_nonneg_right hstep2 (abs_nonneg _)
        _ ≤ ((C1 * K * collarInd L d u δ y) * 1) * Cb :=
            mul_le_mul_of_nonneg_left hψv (mul_nonneg (mul_nonneg (mul_nonneg hC10 hK0) hcoll0) zero_le_one)
        _ = C1 * K * Cb * collarInd L d u δ y := by ring
    have hsum : Work.BoseB1Cube.Winchk.kappaS M * Cψ * (collarInd L d u δ y + S)
        + C1 * K * Cb * collarInd L d u δ y
        ≤ (Work.BoseB1Cube.Winchk.kappaS M * Cψ + C1 * K * Cb) * G := by
      rw [hG]
      have h1' : collarInd L d u δ y + S ≤ collarInd L d u δ y + S + V / volA := by
        linarith [hVdiv0]
      have h2' : collarInd L d u δ y ≤ collarInd L d u δ y + S + V / volA := by
        linarith [hS0, hVdiv0]
      have hA' := mul_le_mul_of_nonneg_left h1' hcA
      have hB' := mul_le_mul_of_nonneg_left h2' hcB
      linarith
    calc |Submission.BoseGases.chiSmallB M L d u y
          * ((Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
                - FprodB (Submission.BoseGases.dlBox L d u)
                  (Submission.BoseGases.kcInsN n i (y, r)))
              * fderiv ℝ ψ (Submission.BoseGases.kcInsN n i (y, r))
                  (Submission.BoseGases.kcDir (n + 1) i k)
            + fderiv ℝ (Fprod (γ δ)) (Submission.BoseGases.kcInsN n i (y, r))
                (Submission.BoseGases.kcDir (n + 1) i k)
              * ψ (Submission.BoseGases.kcInsN n i (y, r)))|
        = |Submission.BoseGases.chiSmallB M L d u y
              * ((Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
                    - FprodB (Submission.BoseGases.dlBox L d u)
                      (Submission.BoseGases.kcInsN n i (y, r)))
                  * fderiv ℝ ψ (Submission.BoseGases.kcInsN n i (y, r))
                      (Submission.BoseGases.kcDir (n + 1) i k))
            + Submission.BoseGases.chiSmallB M L d u y
              * (fderiv ℝ (Fprod (γ δ)) (Submission.BoseGases.kcInsN n i (y, r))
                  (Submission.BoseGases.kcDir (n + 1) i k)
                * ψ (Submission.BoseGases.kcInsN n i (y, r)))| := by ring_nf
      _ ≤ Work.BoseB1Cube.Winchk.kappaS M * Cψ * (collarInd L d u δ y + S)
            + C1 * K * Cb * collarInd L d u δ y :=
          (abs_add_le _ _).trans (add_le_add ht1 ht2)
      _ ≤ (Work.BoseB1Cube.Winchk.kappaS M * Cψ + C1 * K * Cb) * G := hsum
  -- the third term
  have h3 : ∀ k : Fin 3, |fderiv ℝ (Submission.BoseGases.chiSmallB M L d u) y
        (Submission.BoseGases.kcStdBasis k)
        * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
          (Submission.BoseGases.kcInsN n i (y, r))| ≤ (2 * Cχ * Cb) * G := by
    intro k
    have hbq := abs_boxQ_diff_kcInsN_leW (n := n) (L := L) (d := d) hL hd u (hcut := hcut) hδ
      (ψ := ψ) hCb hψb i hy hr
    have hbq' : |Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
        (Submission.BoseGases.kcInsN n i (y, r))| ≤ 2 * (Cb * G) := by
      rw [hG, hS, hV, hvolA] at *
      nlinarith [hbq, hcoll0, hS0, hVdiv0, hCb]
    rw [abs_mul]
    calc |fderiv ℝ (Submission.BoseGases.chiSmallB M L d u) y (Submission.BoseGases.kcStdBasis k)|
          * |Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
              (Submission.BoseGases.kcInsN n i (y, r))|
        ≤ Cχ
          * |Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
              (Submission.BoseGases.kcInsN n i (y, r))| :=
          mul_le_mul_of_nonneg_right (hCχ y k) (abs_nonneg _)
      _ ≤ Cχ * (2 * (Cb * G)) := mul_le_mul_of_nonneg_left hbq' hCχ0
      _ = (2 * Cχ * Cb) * G := by ring
  -- putting the three terms together
  have hbound : ∀ k : Fin 3, |fderiv ℝ (slotFibreFun (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
        (slotDiffState L d u (γ δ) ψ) r) y (Submission.BoseGases.kcStdBasis k)| ≤ 3 * Lam * G := by
    intro k
    rw [hfib k]
    refine (abs_add_le _ _).trans ?_
    have hA := h12 k
    have hB := h3 k
    have hcoef : (Work.BoseB1Cube.Winchk.kappaS M * Cψ + C1 * K * Cb) + (2 * Cχ * Cb)
        ≤ 3 * Lam := by
      rw [hLam]
      have hb1 : C1 * K * Cb ≤ max (C1 * K * Cb) (2 * Cχ * Cb) := le_max_left _ _
      have hb2 : 2 * Cχ * Cb ≤ max (C1 * K * Cb) (2 * Cχ * Cb) := le_max_right _ _
      have hb3 : max (C1 * K * Cb) (2 * Cχ * Cb)
          ≤ max (Work.BoseB1Cube.Winchk.kappaS M * Cψ) (max (C1 * K * Cb) (2 * Cχ * Cb)) :=
        le_max_right _ _
      have ha : Work.BoseB1Cube.Winchk.kappaS M * Cψ
          ≤ max (Work.BoseB1Cube.Winchk.kappaS M * Cψ)
            (max (C1 * K * Cb) (2 * Cχ * Cb)) := le_max_left _ _
      linarith
    calc |Submission.BoseGases.chiSmallB M L d u y
            * ((Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
                  - FprodB (Submission.BoseGases.dlBox L d u)
                    (Submission.BoseGases.kcInsN n i (y, r)))
                * fderiv ℝ ψ (Submission.BoseGases.kcInsN n i (y, r))
                    (Submission.BoseGases.kcDir (n + 1) i k)
              + fderiv ℝ (Fprod (γ δ)) (Submission.BoseGases.kcInsN n i (y, r))
                  (Submission.BoseGases.kcDir (n + 1) i k)
                * ψ (Submission.BoseGases.kcInsN n i (y, r)))|
          + |fderiv ℝ (Submission.BoseGases.chiSmallB M L d u) y (Submission.BoseGases.kcStdBasis k)
            * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
                (Submission.BoseGases.kcInsN n i (y, r))|
        ≤ (Work.BoseB1Cube.Winchk.kappaS M * Cψ + C1 * K * Cb) * G + (2 * Cχ * Cb) * G :=
          add_le_add hA hB
      _ = ((Work.BoseB1Cube.Winchk.kappaS M * Cψ + C1 * K * Cb) + (2 * Cχ * Cb)) * G := by ring
      _ ≤ (3 * Lam) * G := mul_le_mul_of_nonneg_right hcoef hG0
  have hLam2 : Lam ^ 2 ≥ 0 := sq_nonneg Lam
  calc ∑ k : Fin 3, (fderiv ℝ (slotFibreFun (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
        (slotDiffState L d u (γ δ) ψ) r) y (Submission.BoseGases.kcStdBasis k)) ^ 2
      ≤ ∑ _k : Fin 3, (3 * Lam * G) ^ 2 := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbound k) 2
    _ = 3 * (3 * Lam * G) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
    _ = 27 * Lam ^ 2 * G ^ 2 := by ring
    _ = 27 * (max (Work.BoseB1Cube.Winchk.kappaS M * Cψ)
          (max (C1 * K * Cb) (2 * Cχ * Cb))) ^ 2
        * (collarInd L d u δ y + ∑ j : Fin n, collarInd L d u δ (r j)
            + (∫ z : E3, collarInd L d u δ z) / Work.SmallBoxSliding.boxMass L d u) ^ 2 := by
        rw [hLam, hG, hS, hV, hvolA]

/-! ## 10. Integrability on `acube`/`abox` of a function bounded a.e. (window-independent) -/
/-- Integrability on `acube L` of a function bounded a.e. -/
lemma integrableOn_acube_of_boundW {L : ℝ} {f : E3 → ℝ} {C : ℝ}
    (hL : 0 < L) (hf : AEStronglyMeasurable f (volume.restrict (acube L)))
    (hC : ∀ᵐ y ∂(volume.restrict (acube L)), ‖f y‖ ≤ C) : IntegrableOn f (acube L) volume :=
  IntegrableOn.of_bound (acube_lt_top L hL.le) hf C hC

/-- Integrability on `abox n L` of a function bounded a.e. -/
lemma integrableOn_abox_of_boundW {n : ℕ} {L : ℝ} {f : Submission.BoseGases.X n → ℝ}
    {C : ℝ} (hL : 0 < L) (hf : AEStronglyMeasurable f (volume.restrict (abox n L)))
    (hC : ∀ᵐ y ∂(volume.restrict (abox n L)), ‖f y‖ ≤ C) :
    IntegrableOn f (abox n L) volume :=
  IntegrableOn.of_bound (abox_lt_top n L hL.le) hf C hC

/-! ## 11. The coordinate derivative bound for the cube window -/

/-- The cube window is `C³` and compactly supported, so its **directional** derivatives along the
standard basis are globally bounded. -/
theorem exists_bound_fderiv_chiSmallB_coord {M : ℕ} (hM : 4 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : E3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : E3, ∀ k : Fin 3,
      |fderiv ℝ (Submission.BoseGases.chiSmallB M ℓ d u) y (Submission.BoseGases.kcStdBasis k)|
        ≤ C := by
  obtain ⟨C, hC0, hC⟩ := Work.BoseB1Cube.Winchk.exists_bound_fderiv_chiSmallB hM hℓ hd u
  have hnormk : ∀ k : Fin 3, ‖Submission.BoseGases.kcStdBasis k‖ = 1 := by
    intro k
    simp [Submission.BoseGases.kcStdBasis]
  refine ⟨C, hC0, fun y k => ?_⟩
  have h1 : ‖fderiv ℝ (Submission.BoseGases.chiSmallB M ℓ d u) y
      (Submission.BoseGases.kcStdBasis k)‖
      ≤ ‖fderiv ℝ (Submission.BoseGases.chiSmallB M ℓ d u) y‖ := by
    have hh := ContinuousLinearMap.le_opNorm
      (fderiv ℝ (Submission.BoseGases.chiSmallB M ℓ d u) y)
      (Submission.BoseGases.kcStdBasis k)
    rwa [hnormk k, mul_one] at hh
  rw [Real.norm_eq_abs] at h1
  exact h1.trans (hC y)

end Work.BoseB1Cube.PortSmallB

