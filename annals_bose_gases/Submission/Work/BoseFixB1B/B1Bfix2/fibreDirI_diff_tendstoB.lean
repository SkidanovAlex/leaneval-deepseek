import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.B1Bfix.DiffVocab
import Submission.Work.BoseFixB1B.B1Bfix2.CutFibreBase
import Submission.Work.BoseFixB1B.cutFibreMass_facts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.B1Bfix2.fibreDirI_diff_tendstoB`

The fibre Dirichlet energy of the difference state `W_δ = cutProd (γ δ) ψ − 1_{B(u)^{n+1}}ψ`
is `O(δ)`, hence tends to `0` as `δ → 0⁺` (the `FibreDirDiffConv` interface consumed by
`Work.BoseFixB1B.B1Bfix.ampDiff_form_tendsto`).

The whole estimate rests on the explicit derivative of the windowed slot fibre
(`Work.BoseFixB1B.fderiv_Gfun_fibre`) and on the `δ`-cancellation
`|chiB y| ≤ C1·boxMargin y ≤ C1·δ` on the collar, which converts the `K/δ` bound on
`fderiv (γ δ)` into the collar indicator.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B.B1Bfix

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. Elementary product estimates -/

/-- A product of numbers each of which is `0` or `1` has modulus at most `1`. -/
private lemma abs_prod_le_one_of_zero_or_one {ι : Type*} (s : Finset ι) (b : ι → ℝ)
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
private lemma abs_prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
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
    have hB : |∏ i ∈ s, b i| ≤ 1 := abs_prod_le_one_of_zero_or_one s b hb'
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

/-! ## 2. A global derivative bound for the window -/

/-- The window `chiB L d u` is smooth and compactly supported, so its Fréchet derivative is
globally bounded. -/
private theorem exists_bound_fderiv_chiB {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : E3, ‖fderiv ℝ (Submission.BoseGases.chiB L d u) y‖ ≤ C := by
  have hcont : Continuous (fderiv ℝ (Submission.BoseGases.chiB L d u)) :=
    (Work.SmallBoxTBWord.contDiff_chiB hL hd u).continuous_fderiv (by simp)
  have hcpt : HasCompactSupport (fderiv ℝ (Submission.BoseGases.chiB L d u)) :=
    (Work.SmallBoxTBWord.hasCompactSupport_chiB hL hd u).fderiv ℝ
  obtain ⟨C, hCpos, hCle⟩ := (hcpt.isCompact_range hcont).isBounded.subset_closedBall_lt 0 0
  exact ⟨C, le_of_lt hCpos, fun y => by
    have hy := hCle ⟨y, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    exact hy⟩

/-! ## 3. The `δ`-cancellation: `chiB` kills the `K/δ` of the cutoff derivative -/

/-- On the collar the window vanishes at least linearly in the margin, so
`|chiB y · ∂_k(γ δ) y| ≤ C1·K` there; off the collar the cutoff is locally constant and the
derivative vanishes.  Both cases are summarised by the collar indicator. -/
private lemma abs_chiB_mul_fderiv_gamma_le {L d : ℝ} (hL : 0 < L) (hd : 0 < d) {K : ℝ}
    {γ : ℝ → E3 → ℝ} {u : E3}
    {hcut : IsCutFamily L d u K γ} {C1 : ℝ} (hC10 : 0 ≤ C1)
    (hC1 : ∀ x ∈ Submission.BoseGases.dlBox L d u,
      |Submission.BoseGases.chiB L d u x| ≤ C1 * boxMargin L d u x)
    {δ : ℝ} (hδ : 0 < δ) (y : E3) (k : Fin 3) :
    |Submission.BoseGases.chiB L d u y * fderiv ℝ (γ δ) y (Submission.BoseGases.kcStdBasis k)|
      ≤ C1 * K * collarInd L d u δ y := by
  have hK0 : 0 ≤ K := hcut.1
  by_cases hy : y ∈ Submission.BoseGases.dlBox L d u ∧ boxMargin L d u y ≤ δ
  · have hm0 : 0 ≤ boxMargin L d u y := boxMargin_nonneg_iff.mpr hy.1
    have h1 : |Submission.BoseGases.chiB L d u y| ≤ C1 * boxMargin L d u y := hC1 y hy.1
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
    calc |Submission.BoseGases.chiB L d u y| * |fderiv ℝ (γ δ) y (Submission.BoseGases.kcStdBasis k)|
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

/-! ## 4. The product difference at an inserted configuration -/

/-- **The two products differ only on the collar**: for the inserted configuration
`kcInsN n i (y,r)`, the product of the cutoffs and the product of the box indicators differ by at
most the sum of the collar indicators of the slot-`i` variable `y` and of the outside
coordinates `r`. -/
private lemma abs_Fprod_sub_FprodB_kcInsN_le {n : ℕ} {L d : ℝ} {K : ℝ} {γ : ℝ → E3 → ℝ}
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
    have h := abs_prod_sub_prod_le_sum (s := (Finset.univ : Finset (Fin n)))
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

/-! ## 5. The mean-free projection of the difference state at an inserted configuration -/

/-- The collar indicator is supported in the sliding box, so its integral over the box is its
integral over `ℝ³`. -/
private lemma setIntegral_collarInd_dlBox {L d : ℝ} (u : E3) (δ : ℝ) :
    (∫ z in Submission.BoseGases.dlBox L d u, collarInd L d u δ z) = ∫ z : E3, collarInd L d u δ z := by
  refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (f := fun z : E3 => collarInd L d u δ z) (s := Submission.BoseGases.dlBox L d u)
    (fun z hz => ?_)
  rw [collarInd_eq_indicator]
  exact Set.indicator_of_notMem (fun hmem => hz hmem.1) _

/-- **The mean-free projection of `W_δ` at an inserted configuration is `O(δ)`-small**: both the
value and the box mean of `W_δ` are bounded by `Cb` times a sum of collar indicators (plus the
normalised collar volume, which is itself `O(δ)`). -/
private lemma abs_boxQ_diff_kcInsN_le {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3)
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
    simpa only [hA, hS] using abs_Fprod_sub_FprodB_kcInsN_le (n := n) (L := L) (d := d)
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
        setIntegral_collarInd_dlBox u δ, setIntegral_const]
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

/-! ## 6. The pointwise bound on the fibre derivative -/

/-! ## 6. Monotonicity of the set integral with an a.e. hypothesis -/

/-- `∫_s f ≤ ∫_s β` from `f ≤ β` a.e. on `s`, with `β ≥ 0` integrable on `s`.  No integrability
of `f` is assumed (when `f` is not integrable both the integral is `0` and the claim reduces to the
nonnegativity of the right-hand side). -/
private lemma setIntegral_le_of_le_ae' {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f β : α → ℝ} (hs : MeasurableSet s) (hβ : IntegrableOn β s μ) (hβ0 : ∀ x ∈ s, 0 ≤ β x)
    (h : ∀ᵐ x ∂(μ.restrict s), f x ≤ β x) : ∫ x in s, f x ∂μ ≤ ∫ x in s, β x ∂μ := by
  by_cases hf : IntegrableOn f s μ
  · exact integral_mono_ae hf hβ h
  · have hf' : ¬ Integrable f (μ.restrict s) := hf
    rw [integral_undef hf']
    exact integral_nonneg_of_ae (by
      filter_upwards [MeasureTheory.ae_restrict_mem hs] with x hx
      exact hβ0 x hx)

/-! ## 7. The pointwise bound on the fibre derivative -/

/-- **The pointwise bound on the derivative of the windowed slot fibre** of the difference state,
at a slot position of nonzero box margin.  All three terms of `Work.BoseFixB1B.fderiv_Gfun_fibre`
are bounded by the collar: the two products differ only on the collar, the cutoff derivative is
killed by the linear vanishing of the window, and the window derivative is bounded.

The constant is `27·Λ²` with `Λ = max (chiSup²·Cψ) (max (C1·K·Cb) (2·Cχ·Cb))`. -/
lemma fibre_deriv_sum_sq_le {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3)
    {K : ℝ} {γ : ℝ → E3 → ℝ} {δ : ℝ} (hcut : IsCutFamily L d u K γ) (hδ : 0 < δ)
    {ψ : Submission.BoseGases.X (n+1) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) {Cb : ℝ}
    (hCb : 0 ≤ Cb) (hψb : ∀ x ∈ Submission.BoseGases.abox (n+1) L, |ψ x| ≤ Cb)
    {C1 Cχ Cψ : ℝ} (hC10 : 0 ≤ C1)
    (hC1 : ∀ x ∈ Submission.BoseGases.dlBox L d u,
      |Submission.BoseGases.chiB L d u x| ≤ C1 * boxMargin L d u x)
    (hCχ : ∀ y : E3, ∀ k : Fin 3,
      |fderiv ℝ (Submission.BoseGases.chiB L d u) y (Submission.BoseGases.kcStdBasis k)| ≤ Cχ)
    (hCψ0 : 0 ≤ Cψ)
    (hCψ : ∀ x ∈ Submission.BoseGases.abox (n+1) L, ∀ i : Fin (n+1), ∀ k : Fin 3,
      |fderiv ℝ ψ x (Submission.BoseGases.kcDir (n+1) i k)| ≤ Cψ)
    (i : Fin (n+1)) {y : E3} (hy : y ∈ Submission.BoseGases.acube L)
    {r : Submission.BoseGases.X n} (hr : r ∈ Submission.BoseGases.abox n L)
    (hym : boxMargin L d u y ≠ 0) :
    ∑ k : Fin 3, (fderiv ℝ (slotFibreFun (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
        (slotDiffState L d u (γ δ) ψ) r) y (Submission.BoseGases.kcStdBasis k)) ^ 2
      ≤ 27 * (max (Submission.BoseGases.chiSup ^ 2 * Cψ)
            (max (C1 * K * Cb) (2 * Cχ * Cb))) ^ 2
        * (collarInd L d u δ y + ∑ j : Fin n, collarInd L d u δ (r j)
            + (∫ z : E3, collarInd L d u δ z) / Work.SmallBoxSliding.boxMass L d u) ^ 2 := by
  classical
  set S : ℝ := ∑ j : Fin n, collarInd L d u δ (r j) with hS
  set V : ℝ := ∫ z : E3, collarInd L d u δ z with hV
  set volA : ℝ := Work.SmallBoxSliding.boxMass L d u with hvolA
  set G : ℝ := collarInd L d u δ y + S + V / volA with hG
  set Lam : ℝ := max (Submission.BoseGases.chiSup ^ 2 * Cψ) (max (C1 * K * Cb) (2 * Cχ * Cb))
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
    exact le_trans (mul_nonneg (pow_nonneg chiSup_pos.le 2) hCψ0) (le_max_left _ _)
  have hK0 : 0 ≤ K := hcut.1
  have hcA : 0 ≤ Submission.BoseGases.chiSup ^ 2 * Cψ :=
    mul_nonneg (pow_nonneg chiSup_pos.le 2) hCψ0
  have hcB : 0 ≤ C1 * K * Cb := mul_nonneg (mul_nonneg hC10 hK0) hCb
  have hCχ0 : 0 ≤ Cχ :=
    (abs_nonneg ((fderiv ℝ (Submission.BoseGases.chiB L d u) y)
      (Submission.BoseGases.kcStdBasis 0))).trans (hCχ y 0)
  have hcC : 0 ≤ 2 * Cχ * Cb := mul_nonneg (mul_nonneg (by norm_num) hCχ0) hCb
  -- the fibre derivative identity
  have hfib : ∀ k : Fin 3, fderiv ℝ (slotFibreFun (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
        (slotDiffState L d u (γ δ) ψ) r) y (Submission.BoseGases.kcStdBasis k)
      = Submission.BoseGases.chiB L d u y
          * ((Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
                - FprodB (Submission.BoseGases.dlBox L d u) (Submission.BoseGases.kcInsN n i (y, r)))
              * fderiv ℝ ψ (Submission.BoseGases.kcInsN n i (y, r))
                  (Submission.BoseGases.kcDir (n + 1) i k)
            + fderiv ℝ (Fprod (γ δ)) (Submission.BoseGases.kcInsN n i (y, r))
                (Submission.BoseGases.kcDir (n + 1) i k)
              * ψ (Submission.BoseGases.kcInsN n i (y, r)))
        + fderiv ℝ (Submission.BoseGases.chiB L d u) y (Submission.BoseGases.kcStdBasis k)
          * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
              (Submission.BoseGases.kcInsN n i (y, r)) := by
    intro k
    have heq : slotFibreFun (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) i (slotDiffState L d u (γ δ) ψ) r
        = fun z : E3 => Submission.BoseGases.chiB L d u z
            * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i
              (Gfun (γ δ) ψ (Submission.BoseGases.dlBox L d u))
              (Submission.BoseGases.kcInsN n i (z, r)) := by
      funext z
      rfl
    rw [heq]
    exact fderiv_Gfun_fibre (L := L) (d := d) hL hd (hcut := hcut) (n := n) (ψ := ψ)
      (hψ := hψ) (δ := δ) hδ i k (r := r) (y := y) hym
  -- the auxiliary bounds
  have hψmem : ∀ z : E3, z ∈ Submission.BoseGases.acube L →
      |ψ (Submission.BoseGases.kcInsN n i (z, r))| ≤ Cb := fun z hz =>
    hψb _ (kcInsN_mem_abox i hz ((mem_abox_iff n L r).mp hr))
  have hPsplit : |Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
      - FprodB (Submission.BoseGases.dlBox L d u) (Submission.BoseGases.kcInsN n i (y, r))|
      ≤ collarInd L d u δ y + S := by
    simpa only [hS] using abs_Fprod_sub_FprodB_kcInsN_le (n := n) (L := L) (d := d)
      (K := K) (γ := γ) (u := u) hcut hδ i y r
  have hx : |Submission.BoseGases.chiB L d u y| ≤ Submission.BoseGases.chiSup ^ 2 :=
    Work.SmallBoxTBWord.abs_chiB_le_chiSup_sq u y
  have hPle : |∏ j : Fin n, γ δ (r j)| ≤ 1 := by
    have hbdd := (hcut.2 δ hδ).2.2.1
    rw [abs_of_nonneg (Finset.prod_nonneg (fun j _ => (hbdd (r j)).1))]
    exact Finset.prod_le_one₀ (fun j _ => (hbdd (r j)).1) (fun j _ => (hbdd (r j)).2)
  have hχγ : ∀ k : Fin 3, |Submission.BoseGases.chiB L d u y
      * fderiv ℝ (γ δ) y (Submission.BoseGases.kcStdBasis k)| ≤ C1 * K * collarInd L d u δ y :=
    fun k => abs_chiB_mul_fderiv_gamma_le (L := L) (d := d) hL hd (hcut := hcut) (C1 := C1)
      hC10 hC1 hδ y k
  -- the first two terms of the fibre derivative
  have h12 : ∀ k : Fin 3, |Submission.BoseGases.chiB L d u y
        * ((Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
              - FprodB (Submission.BoseGases.dlBox L d u) (Submission.BoseGases.kcInsN n i (y, r)))
            * fderiv ℝ ψ (Submission.BoseGases.kcInsN n i (y, r))
                (Submission.BoseGases.kcDir (n + 1) i k)
          + fderiv ℝ (Fprod (γ δ)) (Submission.BoseGases.kcInsN n i (y, r))
              (Submission.BoseGases.kcDir (n + 1) i k)
            * ψ (Submission.BoseGases.kcInsN n i (y, r)))|
      ≤ (Submission.BoseGases.chiSup ^ 2 * Cψ + C1 * K * Cb) * G := by
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
    have ht1 : |Submission.BoseGases.chiB L d u y
        * ((Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
              - FprodB (Submission.BoseGases.dlBox L d u) (Submission.BoseGases.kcInsN n i (y, r)))
            * fderiv ℝ ψ (Submission.BoseGases.kcInsN n i (y, r))
                (Submission.BoseGases.kcDir (n + 1) i k))|
        ≤ Submission.BoseGases.chiSup ^ 2 * Cψ * (collarInd L d u δ y + S) := by
      have hsh : |Submission.BoseGases.chiB L d u y
          * ((Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
                - FprodB (Submission.BoseGases.dlBox L d u)
                  (Submission.BoseGases.kcInsN n i (y, r)))
              * fderiv ℝ ψ (Submission.BoseGases.kcInsN n i (y, r))
                  (Submission.BoseGases.kcDir (n + 1) i k))|
          = |Submission.BoseGases.chiB L d u y|
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
      calc |Submission.BoseGases.chiB L d u y|
            * (|Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
                - FprodB (Submission.BoseGases.dlBox L d u) (Submission.BoseGases.kcInsN n i (y, r))|
              * |fderiv ℝ ψ (Submission.BoseGases.kcInsN n i (y, r))
                  (Submission.BoseGases.kcDir (n + 1) i k)|)
          ≤ Submission.BoseGases.chiSup ^ 2
            * (|Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
                - FprodB (Submission.BoseGases.dlBox L d u) (Submission.BoseGases.kcInsN n i (y, r))|
              * |fderiv ℝ ψ (Submission.BoseGases.kcInsN n i (y, r))
                  (Submission.BoseGases.kcDir (n + 1) i k)|) :=
            mul_le_mul_of_nonneg_right hx (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ ≤ Submission.BoseGases.chiSup ^ 2 * ((collarInd L d u δ y + S) * Cψ) :=
            mul_le_mul_of_nonneg_left hstep (pow_nonneg chiSup_pos.le 2)
        _ = Submission.BoseGases.chiSup ^ 2 * Cψ * (collarInd L d u δ y + S) := by ring
    -- the second term
    have ht2 : |Submission.BoseGases.chiB L d u y
        * (fderiv ℝ (Fprod (γ δ)) (Submission.BoseGases.kcInsN n i (y, r))
              (Submission.BoseGases.kcDir (n + 1) i k)
            * ψ (Submission.BoseGases.kcInsN n i (y, r)))|
        ≤ C1 * K * Cb * collarInd L d u δ y := by
      have hsh : |Submission.BoseGases.chiB L d u y
          * (fderiv ℝ (Fprod (γ δ)) (Submission.BoseGases.kcInsN n i (y, r))
                (Submission.BoseGases.kcDir (n + 1) i k)
              * ψ (Submission.BoseGases.kcInsN n i (y, r)))|
          = (|Submission.BoseGases.chiB L d u y|
              * |fderiv ℝ (γ δ) y (Submission.BoseGases.kcStdBasis k)|)
            * |∏ j : Fin n, γ δ (r j)|
            * |ψ (Submission.BoseGases.kcInsN n i (y, r))| := by
        simp only [abs_mul, hFd']
        ring
      rw [hsh]
      have hstep1 : |Submission.BoseGases.chiB L d u y|
            * |fderiv ℝ (γ δ) y (Submission.BoseGases.kcStdBasis k)|
          ≤ C1 * K * collarInd L d u δ y := by
        rw [← abs_mul]
        exact hχγ k
      have hstep2 : (|Submission.BoseGases.chiB L d u y|
              * |fderiv ℝ (γ δ) y (Submission.BoseGases.kcStdBasis k)|)
            * |∏ j : Fin n, γ δ (r j)| ≤ (C1 * K * collarInd L d u δ y) * 1 := by
        calc _ ≤ (C1 * K * collarInd L d u δ y) * |∏ j : Fin n, γ δ (r j)| :=
              mul_le_mul_of_nonneg_right hstep1 (abs_nonneg _)
          _ ≤ (C1 * K * collarInd L d u δ y) * 1 :=
              mul_le_mul_of_nonneg_left hPle (mul_nonneg (mul_nonneg hC10 hK0) hcoll0)
      calc (|Submission.BoseGases.chiB L d u y|
              * |fderiv ℝ (γ δ) y (Submission.BoseGases.kcStdBasis k)|)
            * |∏ j : Fin n, γ δ (r j)|
            * |ψ (Submission.BoseGases.kcInsN n i (y, r))|
          ≤ ((C1 * K * collarInd L d u δ y) * 1)
            * |ψ (Submission.BoseGases.kcInsN n i (y, r))| :=
            mul_le_mul_of_nonneg_right hstep2 (abs_nonneg _)
        _ ≤ ((C1 * K * collarInd L d u δ y) * 1) * Cb :=
            mul_le_mul_of_nonneg_left hψv (mul_nonneg (mul_nonneg (mul_nonneg hC10 hK0) hcoll0) zero_le_one)
        _ = C1 * K * Cb * collarInd L d u δ y := by ring
    have hsum : Submission.BoseGases.chiSup ^ 2 * Cψ * (collarInd L d u δ y + S)
        + C1 * K * Cb * collarInd L d u δ y
        ≤ (Submission.BoseGases.chiSup ^ 2 * Cψ + C1 * K * Cb) * G := by
      rw [hG]
      have h1' : collarInd L d u δ y + S ≤ collarInd L d u δ y + S + V / volA := by
        linarith [hVdiv0]
      have h2' : collarInd L d u δ y ≤ collarInd L d u δ y + S + V / volA := by
        linarith [hS0, hVdiv0]
      have hA' := mul_le_mul_of_nonneg_left h1' hcA
      have hB' := mul_le_mul_of_nonneg_left h2' hcB
      linarith
    calc |Submission.BoseGases.chiB L d u y
          * ((Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
                - FprodB (Submission.BoseGases.dlBox L d u)
                  (Submission.BoseGases.kcInsN n i (y, r)))
              * fderiv ℝ ψ (Submission.BoseGases.kcInsN n i (y, r))
                  (Submission.BoseGases.kcDir (n + 1) i k)
            + fderiv ℝ (Fprod (γ δ)) (Submission.BoseGases.kcInsN n i (y, r))
                (Submission.BoseGases.kcDir (n + 1) i k)
              * ψ (Submission.BoseGases.kcInsN n i (y, r)))|
        = |Submission.BoseGases.chiB L d u y
              * ((Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
                    - FprodB (Submission.BoseGases.dlBox L d u)
                      (Submission.BoseGases.kcInsN n i (y, r)))
                  * fderiv ℝ ψ (Submission.BoseGases.kcInsN n i (y, r))
                      (Submission.BoseGases.kcDir (n + 1) i k))
            + Submission.BoseGases.chiB L d u y
              * (fderiv ℝ (Fprod (γ δ)) (Submission.BoseGases.kcInsN n i (y, r))
                  (Submission.BoseGases.kcDir (n + 1) i k)
                * ψ (Submission.BoseGases.kcInsN n i (y, r)))| := by ring_nf
      _ ≤ Submission.BoseGases.chiSup ^ 2 * Cψ * (collarInd L d u δ y + S)
            + C1 * K * Cb * collarInd L d u δ y :=
          (abs_add_le _ _).trans (add_le_add ht1 ht2)
      _ ≤ (Submission.BoseGases.chiSup ^ 2 * Cψ + C1 * K * Cb) * G := hsum
  -- the third term
  have h3 : ∀ k : Fin 3, |fderiv ℝ (Submission.BoseGases.chiB L d u) y
        (Submission.BoseGases.kcStdBasis k)
        * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
          (Submission.BoseGases.kcInsN n i (y, r))| ≤ (2 * Cχ * Cb) * G := by
    intro k
    have hbq := abs_boxQ_diff_kcInsN_le (n := n) (L := L) (d := d) hL hd u (hcut := hcut) hδ
      (ψ := ψ) hCb hψb i hy hr
    have hbq' : |Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
        (Submission.BoseGases.kcInsN n i (y, r))| ≤ 2 * (Cb * G) := by
      rw [hG, hS, hV, hvolA] at *
      nlinarith [hbq, hcoll0, hS0, hVdiv0, hCb]
    rw [abs_mul]
    calc |fderiv ℝ (Submission.BoseGases.chiB L d u) y (Submission.BoseGases.kcStdBasis k)|
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
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
        (slotDiffState L d u (γ δ) ψ) r) y (Submission.BoseGases.kcStdBasis k)| ≤ 3 * Lam * G := by
    intro k
    rw [hfib k]
    refine (abs_add_le _ _).trans ?_
    have hA := h12 k
    have hB := h3 k
    have hcoef : (Submission.BoseGases.chiSup ^ 2 * Cψ + C1 * K * Cb) + (2 * Cχ * Cb)
        ≤ 3 * Lam := by
      rw [hLam]
      have hb1 : C1 * K * Cb ≤ max (C1 * K * Cb) (2 * Cχ * Cb) := le_max_left _ _
      have hb2 : 2 * Cχ * Cb ≤ max (C1 * K * Cb) (2 * Cχ * Cb) := le_max_right _ _
      have hb3 : max (C1 * K * Cb) (2 * Cχ * Cb)
          ≤ max (Submission.BoseGases.chiSup ^ 2 * Cψ) (max (C1 * K * Cb) (2 * Cχ * Cb)) :=
        le_max_right _ _
      have ha : Submission.BoseGases.chiSup ^ 2 * Cψ
          ≤ max (Submission.BoseGases.chiSup ^ 2 * Cψ)
            (max (C1 * K * Cb) (2 * Cχ * Cb)) := le_max_left _ _
      linarith
    calc |Submission.BoseGases.chiB L d u y
            * ((Fprod (γ δ) (Submission.BoseGases.kcInsN n i (y, r))
                  - FprodB (Submission.BoseGases.dlBox L d u)
                    (Submission.BoseGases.kcInsN n i (y, r)))
                * fderiv ℝ ψ (Submission.BoseGases.kcInsN n i (y, r))
                    (Submission.BoseGases.kcDir (n + 1) i k)
              + fderiv ℝ (Fprod (γ δ)) (Submission.BoseGases.kcInsN n i (y, r))
                  (Submission.BoseGases.kcDir (n + 1) i k)
                * ψ (Submission.BoseGases.kcInsN n i (y, r)))|
          + |fderiv ℝ (Submission.BoseGases.chiB L d u) y (Submission.BoseGases.kcStdBasis k)
            * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
                (Submission.BoseGases.kcInsN n i (y, r))|
        ≤ (Submission.BoseGases.chiSup ^ 2 * Cψ + C1 * K * Cb) * G + (2 * Cχ * Cb) * G :=
          add_le_add hA hB
      _ = ((Submission.BoseGases.chiSup ^ 2 * Cψ + C1 * K * Cb) + (2 * Cχ * Cb)) * G := by ring
      _ ≤ (3 * Lam) * G := mul_le_mul_of_nonneg_right hcoef hG0
  have hLam2 : Lam ^ 2 ≥ 0 := sq_nonneg Lam
  calc ∑ k : Fin 3, (fderiv ℝ (slotFibreFun (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
        (slotDiffState L d u (γ δ) ψ) r) y (Submission.BoseGases.kcStdBasis k)) ^ 2
      ≤ ∑ _k : Fin 3, (3 * Lam * G) ^ 2 := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbound k) 2
    _ = 3 * (3 * Lam * G) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
    _ = 27 * Lam ^ 2 * G ^ 2 := by ring
    _ = 27 * (max (Submission.BoseGases.chiSup ^ 2 * Cψ)
          (max (C1 * K * Cb) (2 * Cχ * Cb))) ^ 2
        * (collarInd L d u δ y + ∑ j : Fin n, collarInd L d u δ (r j)
            + (∫ z : E3, collarInd L d u δ z) / Work.SmallBoxSliding.boxMass L d u) ^ 2 := by
        rw [hLam, hG, hS, hV, hvolA]

/-! ## 8. The fibre Dirichlet energy of the difference state is `O(δ)` -/

/-- Integrability on `acube L` of a function bounded a.e. -/
private lemma integrableOn_acube_of_bound {L : ℝ} {f : E3 → ℝ} {C : ℝ}
    (hL : 0 < L) (hf : AEStronglyMeasurable f (volume.restrict (acube L)))
    (hC : ∀ᵐ y ∂(volume.restrict (acube L)), ‖f y‖ ≤ C) : IntegrableOn f (acube L) volume :=
  IntegrableOn.of_bound (acube_lt_top L hL.le) hf C hC

/-- Integrability on `abox n L` of a function bounded a.e. -/
private lemma integrableOn_abox_of_bound {n : ℕ} {L : ℝ} {f : Submission.BoseGases.X n → ℝ}
    {C : ℝ} (hL : 0 < L) (hf : AEStronglyMeasurable f (volume.restrict (abox n L)))
    (hC : ∀ᵐ y ∂(volume.restrict (abox n L)), ‖f y‖ ≤ C) :
    IntegrableOn f (abox n L) volume :=
  IntegrableOn.of_bound (abox_lt_top n L hL.le) hf C hC

theorem fibreDirI_diff_tendstoB {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {ψ : Submission.BoseGases.X (n+1) → ℝ} {K Cb : ℝ}
    {γ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hcut : Work.BoseFixB1B.IsCutFamily L d u K γ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hCb : 0 ≤ Cb)
    (hψb : ∀ x ∈ Submission.BoseGases.abox (n+1) L, |ψ x| ≤ Cb) :
    Work.BoseFixB1B.B1Bfix.FibreDirDiffConv L d u ψ K Cb γ := by
  classical
  obtain ⟨C1, hC10, hC1⟩ := chiB_abs_le_boxMargin hL hd u
  obtain ⟨Cχ, hCχ0, hCχ⟩ := exists_bound_fderiv_chiB hL hd u
  obtain ⟨Cψ, hCψ0, hCψ⟩ := exists_bound_fderiv_psi (L := L) hψ
  set Ca : ℝ := 12 * L ^ 2 * (1 + d ^ 2) with hCadef
  have hCa0 : 0 ≤ Ca := by rw [hCadef]; positivity
  have hCa : ∀ δ : ℝ, 0 < δ →
      (∫ y in acube L, collarInd L d u δ y) ≤ Ca * δ := by
    intro δ hδ
    rw [hCadef]
    exact integral_collarInd_acube_le hL hd u hδ
  choose Cj hCj0 hCj using fun j : Fin n => integral_collarInd_abox (L := L) (d := d) hL hd u n j
  have hnormk : ∀ k : Fin 3, ‖Submission.BoseGases.kcStdBasis k‖ = 1 := by
    intro k
    simp [Submission.BoseGases.kcStdBasis]
  have hCχcoord : ∀ y : E3, ∀ k : Fin 3,
      |fderiv ℝ (Submission.BoseGases.chiB L d u) y (Submission.BoseGases.kcStdBasis k)| ≤ Cχ := by
    intro y k
    have h1 : ‖fderiv ℝ (Submission.BoseGases.chiB L d u) y (Submission.BoseGases.kcStdBasis k)‖
        ≤ ‖fderiv ℝ (Submission.BoseGases.chiB L d u) y‖ := by
      have hh := ContinuousLinearMap.le_opNorm (fderiv ℝ (Submission.BoseGases.chiB L d u) y)
        (Submission.BoseGases.kcStdBasis k)
      rwa [hnormk k, mul_one] at hh
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (hCχ y)
  set Cab : ℝ := ∑ j : Fin n, Cj j with hCab
  have hCab0 : 0 ≤ Cab := by rw [hCab]; exact Finset.sum_nonneg (fun j _ => hCj0 j)
  set Cm : ℝ := max 1 (Work.SmallBoxSliding.boxMass L d u)⁻¹ with hCm
  have hCm0 : 0 ≤ Cm := by rw [hCm]; exact le_trans zero_le_one (le_max_left _ _)
  set A0 : ℝ := 27 * (max (Submission.BoseGases.chiSup ^ 2 * Cψ)
    (max (C1 * K * Cb) (2 * Cχ * Cb))) ^ 2 with hA0
  have hA00 : 0 ≤ A0 := by rw [hA0]; positivity
  have hvolc : (volume : Measure E3).real (acube L) = L ^ 3 := volume_real_acube hL.le
  have hvolb : (volume : Measure (Submission.BoseGases.X n)).real (Submission.BoseGases.abox n L)
      = (L ^ 3) ^ n := volume_real_abox n hL.le
  have hboxmass0 : 0 ≤ Work.SmallBoxSliding.boxMass L d u := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, Measure.real_def]
    positivity
  have hVac : ∀ δ : ℝ, (∫ z in acube L, collarInd L d u δ z) = ∫ z : E3, collarInd L d u δ z := by
    intro δ
    exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := fun z : E3 => collarInd L d u δ z) (s := acube L)
      (fun z hz => by
        rw [collarInd_eq_indicator]
        exact Set.indicator_of_notMem
          (fun hmem => hz (Work.SmallBoxSliding.dlBox_subset_acube L d u hmem.1)) _)
  have hVle : ∀ δ : ℝ, 0 < δ → (∫ z : E3, collarInd L d u δ z) ≤ Ca * δ := by
    intro δ hδ
    have h := hCa δ hδ
    rwa [hVac δ] at h
  have hSint : ∀ δ : ℝ, 0 < δ →
      (∫ r in Submission.BoseGases.abox n L, ∑ j : Fin n, collarInd L d u δ (r j))
        ≤ Cab * δ := by
    intro δ hδ
    have hsum_eq : (∫ r in Submission.BoseGases.abox n L, ∑ j : Fin n, collarInd L d u δ (r j))
        = ∑ j : Fin n, ∫ r in Submission.BoseGases.abox n L, collarInd L d u δ (r j) := by
      rw [MeasureTheory.integral_finset_sum]
      intro j _
      exact integrableOn_abox_of_bound (n := n) hL
        ((Work.BoseFixB1B.measurable_collarInd L d u δ).comp
          (measurable_pi_apply j)).aestronglyMeasurable
        (by
          rw [ae_restrict_iff' (abox_measurable n L)]
          refine ae_of_all _ (fun r _ => ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg (collarInd_nonneg L d u δ (r j))]
          exact collarInd_le_one L d u δ (r j))
    rw [hsum_eq]
    calc ∑ j : Fin n, ∫ r in Submission.BoseGases.abox n L, collarInd L d u δ (r j)
        ≤ ∑ j : Fin n, Cj j * δ := Finset.sum_le_sum (fun j _ => hCj j δ hδ)
      _ = Cab * δ := by rw [hCab, Finset.sum_mul]
  -- the per-slot estimate
  have hslot : ∀ (δ : ℝ), 0 < δ → δ ≤ 1 → ∀ i : Fin (n+1),
      fibreDirI L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) i (slotDiffState L d u (γ δ) ψ)
      ≤ (A0 * 3 * (Ca * (L ^ 3) ^ n + (L ^ 3) * ((n : ℝ) * Cab)
          + (L ^ 3) * (Ca * Cm) ^ 2 * (L ^ 3) ^ n)) * δ := by
    intro δ hδ hδ1 i
    set V : ℝ := ∫ z : E3, collarInd L d u δ z with hV
    set b : ℝ := V / Work.SmallBoxSliding.boxMass L d u with hb
    have hV0 : 0 ≤ V := by
      rw [hV]; exact integral_nonneg (fun z => collarInd_nonneg L d u δ z)
    have hb0 : 0 ≤ b := by rw [hb]; exact div_nonneg hV0 hboxmass0
    have hVle' : V ≤ Ca * δ := by rw [hV]; exact hVle δ hδ
    have hble : b ≤ Ca * Cm * δ := by
      rw [hb, div_eq_mul_inv]
      calc V * (Work.SmallBoxSliding.boxMass L d u)⁻¹
          ≤ (Ca * δ) * (Work.SmallBoxSliding.boxMass L d u)⁻¹ :=
            mul_le_mul_of_nonneg_right hVle' (inv_nonneg.mpr hboxmass0)
        _ ≤ (Ca * δ) * Cm :=
            mul_le_mul_of_nonneg_left (le_max_right (1:ℝ) _) (mul_nonneg hCa0 hδ.le)
        _ = Ca * Cm * δ := by ring
    have hS0' : ∀ r : Submission.BoseGases.X n, 0 ≤ ∑ j : Fin n, collarInd L d u δ (r j) :=
      fun r => Finset.sum_nonneg (fun j _ => collarInd_nonneg L d u δ (r j))
    have hSle : ∀ r : Submission.BoseGases.X n,
        (∑ j : Fin n, collarInd L d u δ (r j)) ≤ (n : ℝ) := by
      intro r
      calc ∑ j : Fin n, collarInd L d u δ (r j) ≤ ∑ _j : Fin n, (1 : ℝ) :=
            Finset.sum_le_sum (fun j _ => collarInd_le_one L d u δ (r j))
        _ = (n : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hSsq : ∀ r : Submission.BoseGases.X n,
        (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2
          ≤ (n : ℝ) * ∑ j : Fin n, collarInd L d u δ (r j) := by
      intro r
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith [hSle r, hS0' r, hn]
    -- the a.e. bound on the fibre derivative, integrated over the slot variable
    have hpp : ∀ r ∈ Submission.BoseGases.abox n L,
        (∫ y in acube L, ∑ k : Fin 3, (fderiv ℝ (slotFibreFun (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
            (slotDiffState L d u (γ δ) ψ) r) y (Submission.BoseGases.kcStdBasis k)) ^ 2)
        ≤ ∫ y in acube L, A0 * 3 * ((collarInd L d u δ y) ^ 2
            + (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2 + b ^ 2) := by
      intro r hr
      have hc : Measurable (fun y : E3 => collarInd L d u δ y) :=
        Work.BoseFixB1B.measurable_collarInd L d u δ
      have hsum : Measurable (fun y : E3 => (collarInd L d u δ y) ^ 2
          + (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2 + b ^ 2) :=
        ((hc.pow_const 2).add measurable_const).add measurable_const
      have hprod : Measurable (fun y : E3 => A0 * 3 * ((collarInd L d u δ y) ^ 2
          + (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2 + b ^ 2)) :=
        (measurable_const : Measurable (fun _ : E3 => A0 * 3)).mul hsum
      have hβint : IntegrableOn (fun y : E3 => A0 * 3 * ((collarInd L d u δ y) ^ 2
          + (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2 + b ^ 2)) (acube L) volume :=
        integrableOn_acube_of_bound (C := A0 * 3 * (1 + (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2 + b ^ 2))
          hL hprod.aestronglyMeasurable
          (by
            rw [ae_restrict_iff' (acube_measurable L)]
            refine ae_of_all _ (fun y _ => ?_)
            rw [Real.norm_of_nonneg (by positivity)]
            refine mul_le_mul_of_nonneg_left (a := A0 * 3) ?_ (mul_nonneg hA00 (by norm_num))
            have h1 : (collarInd L d u δ y) ^ 2 ≤ 1 := by
              have h2 := collarInd_le_one L d u δ y
              have h3 := collarInd_nonneg L d u δ y
              nlinarith
            linarith [h1, sq_nonneg (∑ j : Fin n, collarInd L d u δ (r j)), sq_nonneg b])
      refine setIntegral_le_of_le_ae' (acube_measurable L) hβint ?_ ?_
      · intro y _
        exact mul_nonneg (by positivity)
          (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))
      · have hae : ∀ᵐ y ∂(volume : Measure E3), boxMargin L d u y ≠ 0 := by
          rw [MeasureTheory.ae_iff]
          simpa only [not_ne_iff] using Work.BoseFixB1B.cutFibreMass_boxMargin_eq_zero_null L d u
        rw [MeasureTheory.ae_restrict_iff' (acube_measurable L)]
        filter_upwards [hae] with y hym hyac
        have hder := fibre_deriv_sum_sq_le (L := L) (d := d) hL hd u (hcut := hcut) hδ
          (ψ := ψ) hψ hCb hψb hC10 hC1 hCχcoord hCψ0 hCψ i hyac hr hym
        rw [← hA0, ← hV, ← hb] at hder
        refine hder.trans ?_
        have hmid : (collarInd L d u δ y + ∑ j : Fin n, collarInd L d u δ (r j) + b) ^ 2
            ≤ 3 * ((collarInd L d u δ y) ^ 2 + (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2 + b ^ 2) := by
          nlinarith [sq_nonneg (collarInd L d u δ y - ∑ j : Fin n, collarInd L d u δ (r j)),
            sq_nonneg (collarInd L d u δ y - b),
            sq_nonneg ((∑ j : Fin n, collarInd L d u δ (r j)) - b),
            collarInd_nonneg L d u δ y, hS0' r, hb0]
        refine (mul_le_mul_of_nonneg_left hmid hA00).trans ?_
        exact le_of_eq (by ring)
    -- the value of the slot integral
    have hyval : ∀ r ∈ Submission.BoseGases.abox n L,
        (∫ y in acube L, A0 * 3 * ((collarInd L d u δ y) ^ 2
            + (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2 + b ^ 2))
        = A0 * 3 * V + (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2
          + (A0 * 3 * (L ^ 3)) * b ^ 2 := by
      intro r _
      have h1 : (∫ y in acube L, (collarInd L d u δ y) ^ 2) = V := by
        rw [MeasureTheory.setIntegral_congr_fun (acube_measurable L)
          (fun y _ => collarInd_sq L d u δ y)]
        rw [hV]
        exact hVac δ
      have hI1 : IntegrableOn (fun y : E3 => A0 * 3 * (collarInd L d u δ y) ^ 2) (acube L) volume := by
        have hc : Measurable (fun y : E3 => A0 * 3 * (collarInd L d u δ y) ^ 2) :=
          (measurable_const : Measurable (fun _ : E3 => A0 * 3)).mul
            ((Work.BoseFixB1B.measurable_collarInd L d u δ).pow_const 2)
        refine integrableOn_acube_of_bound (C := A0 * 3) hL hc.aestronglyMeasurable ?_
        rw [ae_restrict_iff' (acube_measurable L)]
        refine ae_of_all _ (fun y _ => ?_)
        rw [Real.norm_of_nonneg (by positivity)]
        have hle : (collarInd L d u δ y) ^ 2 ≤ 1 := by
          have h3 := collarInd_le_one L d u δ y
          have h4 := collarInd_nonneg L d u δ y
          nlinarith
        calc A0 * 3 * (collarInd L d u δ y) ^ 2 ≤ A0 * 3 * 1 :=
              mul_le_mul_of_nonneg_left hle (mul_nonneg hA00 (by norm_num))
          _ = A0 * 3 := by ring
      have hI2 : IntegrableOn (fun _ : E3 => A0 * 3 * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
          (acube L) volume :=
        integrableOn_acube_of_bound (C := |A0 * 3 * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2|)
          hL (aestronglyMeasurable_const :
            AEStronglyMeasurable (fun _ : E3 => A0 * 3 * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
              (volume.restrict (acube L)))
          (ae_of_all _ (fun y => by rw [Real.norm_eq_abs]))
      have hI3 : IntegrableOn (fun _ : E3 => A0 * 3 * b ^ 2) (acube L) volume :=
        integrableOn_acube_of_bound (C := |A0 * 3 * b ^ 2|) hL
          (aestronglyMeasurable_const :
            AEStronglyMeasurable (fun _ : E3 => A0 * 3 * b ^ 2) (volume.restrict (acube L)))
          (ae_of_all _ (fun y => by rw [Real.norm_eq_abs]))
      calc (∫ y in acube L, A0 * 3 * ((collarInd L d u δ y) ^ 2
              + (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2 + b ^ 2))
          = ∫ y in acube L, (A0 * 3 * (collarInd L d u δ y) ^ 2
              + A0 * 3 * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2 + A0 * 3 * b ^ 2) := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
            ring
        _ = (∫ y in acube L, A0 * 3 * (collarInd L d u δ y) ^ 2)
            + (∫ y in acube L, A0 * 3 * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
            + (∫ y in acube L, A0 * 3 * b ^ 2) := by
            have hI12 : Integrable (fun y : E3 => A0 * 3 * (collarInd L d u δ y) ^ 2
                + A0 * 3 * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
                ((volume : Measure E3).restrict (acube L)) :=
              (hI1.add hI2).congr (Filter.Eventually.of_forall (fun y => by
                simp only [Pi.add_apply]))
            rw [MeasureTheory.integral_add (μ := (volume : Measure E3).restrict (acube L))
                (f := fun y : E3 => A0 * 3 * (collarInd L d u δ y) ^ 2
                  + A0 * 3 * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
                (g := fun _ : E3 => A0 * 3 * b ^ 2) hI12 hI3,
              MeasureTheory.integral_add (μ := (volume : Measure E3).restrict (acube L))
                (f := fun y : E3 => A0 * 3 * (collarInd L d u δ y) ^ 2)
                (g := fun _ : E3 => A0 * 3 * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
                hI1 hI2]
        _ = A0 * 3 * V + (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2
            + (A0 * 3 * (L ^ 3)) * b ^ 2 := by
            simp only [MeasureTheory.integral_const_mul, setIntegral_const, h1, hvolc, smul_eq_mul]
            ring
    -- the per-slot bound
    have hstep : fibreDirI L (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
        (slotDiffState L d u (γ δ) ψ)
        ≤ ∫ r in Submission.BoseGases.abox n L, (A0 * 3 * V
            + (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2
            + (A0 * 3 * (L ^ 3)) * b ^ 2) := by
      have hβ2int : IntegrableOn (fun r : Submission.BoseGases.X n => A0 * 3 * V
          + (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2
          + (A0 * 3 * (L ^ 3)) * b ^ 2) (Submission.BoseGases.abox n L) volume := by
        have hs : Measurable (fun r : Submission.BoseGases.X n =>
            (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2) :=
          (Finset.measurable_sum _ (fun j _ =>
            (Work.BoseFixB1B.measurable_collarInd L d u δ).comp
              (measurable_pi_apply j))).pow_const 2
        have hm : Measurable (fun r : Submission.BoseGases.X n => A0 * 3 * V
            + (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2
            + (A0 * 3 * (L ^ 3)) * b ^ 2) :=
          (measurable_const.add ((measurable_const : Measurable (fun _ : Submission.BoseGases.X n =>
            A0 * 3 * (L ^ 3))).mul hs)).add measurable_const
        refine integrableOn_abox_of_bound (n := n) (C := A0 * 3 * V
          + (A0 * 3 * (L ^ 3)) * ((n : ℝ) ^ 2) + (A0 * 3 * (L ^ 3)) * b ^ 2)
          hL hm.aestronglyMeasurable ?_
        rw [ae_restrict_iff' (abox_measurable n L)]
        refine ae_of_all _ (fun r _ => ?_)
        rw [Real.norm_of_nonneg (by positivity)]
        have hS2 : (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2 ≤ (n : ℝ) ^ 2 := by
          have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          nlinarith [hSle r, hS0' r, hn]
        have hA0L : 0 ≤ A0 * 3 * (L ^ 3) := by positivity
        nlinarith [hS2, hV0, sq_nonneg b, hA00, hA0L, hδ.le, hCa0, hCm0]
      rw [fibreDirI_eq]
      refine setIntegral_le_of_le_ae (abox_measurable n L) hβ2int ?_ ?_
      · intro r _
        positivity
      · intro r hr
        calc (∫ y in acube L, ∑ k : Fin 3, (fderiv ℝ (slotFibreFun (Submission.BoseGases.dlBox L d u)
              (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
              (slotDiffState L d u (γ δ) ψ) r) y (Submission.BoseGases.kcStdBasis k)) ^ 2)
            ≤ ∫ y in acube L, A0 * 3 * ((collarInd L d u δ y) ^ 2
              + (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2 + b ^ 2) := hpp r hr
          _ = _ := hyval r hr
    -- the value of the outer integral
    have hrval : (∫ r in Submission.BoseGases.abox n L, (A0 * 3 * V
          + (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2
          + (A0 * 3 * (L ^ 3)) * b ^ 2))
        = A0 * 3 * V * (L ^ 3) ^ n
          + (A0 * 3 * (L ^ 3))
            * (∫ r in Submission.BoseGases.abox n L, (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
          + (A0 * 3 * (L ^ 3)) * b ^ 2 * (L ^ 3) ^ n := by
      have hVint : IntegrableOn (fun _ : Submission.BoseGases.X n => A0 * 3 * V)
          (Submission.BoseGases.abox n L) volume :=
        integrableOn_abox_of_bound (n := n) (C := |A0 * 3 * V|) hL
          (aestronglyMeasurable_const :
            AEStronglyMeasurable (fun _ : Submission.BoseGases.X n => A0 * 3 * V)
              (volume.restrict (Submission.BoseGases.abox n L)))
          (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]))
      have hS2int : IntegrableOn (fun r : Submission.BoseGases.X n =>
          (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
          (Submission.BoseGases.abox n L) volume := by
        have hs : Measurable (fun r : Submission.BoseGases.X n =>
            (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2) :=
          (Finset.measurable_sum _ (fun j _ =>
            (Work.BoseFixB1B.measurable_collarInd L d u δ).comp
              (measurable_pi_apply j))).pow_const 2
        refine integrableOn_abox_of_bound (n := n) (C := (n : ℝ) ^ 2) hL
          hs.aestronglyMeasurable ?_
        rw [ae_restrict_iff' (abox_measurable n L)]
        refine ae_of_all _ (fun r _ => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith [hSle r, hS0' r, hn]
      have hb2int : IntegrableOn (fun _ : Submission.BoseGases.X n => b ^ 2)
          (Submission.BoseGases.abox n L) volume :=
        integrableOn_abox_of_bound (n := n) (C := |b ^ 2|) hL
          (aestronglyMeasurable_const :
            AEStronglyMeasurable (fun _ : Submission.BoseGases.X n => b ^ 2)
              (volume.restrict (Submission.BoseGases.abox n L)))
          (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]))
      calc (∫ r in Submission.BoseGases.abox n L, (A0 * 3 * V
              + (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2
              + (A0 * 3 * (L ^ 3)) * b ^ 2))
          = ∫ r in Submission.BoseGases.abox n L, (A0 * 3 * V
              + (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2
              + (A0 * 3 * (L ^ 3)) * (b ^ 2)) := by
            rfl
        _ = (∫ r in Submission.BoseGases.abox n L, A0 * 3 * V)
            + (∫ r in Submission.BoseGases.abox n L,
                (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
            + (∫ r in Submission.BoseGases.abox n L, (A0 * 3 * (L ^ 3)) * b ^ 2) := by
            have hb2c : IntegrableOn (fun _ : Submission.BoseGases.X n => (A0 * 3 * (L ^ 3)) * b ^ 2)
                (Submission.BoseGases.abox n L) volume := hb2int.const_mul (A0 * 3 * (L ^ 3))
            have hS2c : IntegrableOn (fun r : Submission.BoseGases.X n =>
                (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
                (Submission.BoseGases.abox n L) volume := hS2int.const_mul (A0 * 3 * (L ^ 3))
            have hV12 : IntegrableOn (fun r : Submission.BoseGases.X n => A0 * 3 * V
                + (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
                (Submission.BoseGases.abox n L) volume :=
              (hVint.add hS2c).congr (Filter.Eventually.of_forall (fun r => by
                simp only [Pi.add_apply]))
            rw [MeasureTheory.integral_add
                (μ := (volume : Measure (Submission.BoseGases.X n)).restrict
                  (Submission.BoseGases.abox n L))
                (f := fun r : Submission.BoseGases.X n => A0 * 3 * V
                  + (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
                (g := fun _ : Submission.BoseGases.X n => (A0 * 3 * (L ^ 3)) * b ^ 2)
                hV12 hb2c,
              MeasureTheory.integral_add
                (μ := (volume : Measure (Submission.BoseGases.X n)).restrict
                  (Submission.BoseGases.abox n L))
                (f := fun _ : Submission.BoseGases.X n => A0 * 3 * V)
                (g := fun r : Submission.BoseGases.X n =>
                  (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
                hVint hS2c]
        _ = A0 * 3 * V * (L ^ 3) ^ n
            + (A0 * 3 * (L ^ 3))
              * (∫ r in Submission.BoseGases.abox n L, (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
            + (A0 * 3 * (L ^ 3)) * b ^ 2 * (L ^ 3) ^ n := by
            simp only [MeasureTheory.integral_const_mul, setIntegral_const, hvolb, smul_eq_mul]
            ring
    -- the bound on the collar integral of the squared count
    have hS2b : (∫ r in Submission.BoseGases.abox n L,
          (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2) ≤ ((n : ℝ) * Cab) * δ := by
      have hmono : (∫ r in Submission.BoseGases.abox n L,
            (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
          ≤ ∫ r in Submission.BoseGases.abox n L,
              (n : ℝ) * ∑ j : Fin n, collarInd L d u δ (r j) := by
        have hint : IntegrableOn (fun r : Submission.BoseGases.X n =>
            (n : ℝ) * ∑ j : Fin n, collarInd L d u δ (r j))
            (Submission.BoseGases.abox n L) volume := by
          have hs : Measurable (fun r : Submission.BoseGases.X n =>
              ∑ j : Fin n, collarInd L d u δ (r j)) :=
            Finset.measurable_sum _ (fun j _ =>
              (Work.BoseFixB1B.measurable_collarInd L d u δ).comp (measurable_pi_apply j))
          refine integrableOn_abox_of_bound (n := n) (C := (n : ℝ) * (n : ℝ)) hL
            (measurable_const.mul hs).aestronglyMeasurable ?_
          rw [ae_restrict_iff' (abox_measurable n L)]
          refine ae_of_all _ (fun r _ => ?_)
          rw [Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (hS0' r))]
          exact mul_le_mul_of_nonneg_left (hSle r) (Nat.cast_nonneg n)
        refine setIntegral_le_of_le_ae (abox_measurable n L) hint ?_ ?_
        · intro r _
          exact mul_nonneg (Nat.cast_nonneg n) (hS0' r)
        · intro r _
          exact hSsq r
      calc (∫ r in Submission.BoseGases.abox n L,
            (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
          ≤ ∫ r in Submission.BoseGases.abox n L,
              (n : ℝ) * ∑ j : Fin n, collarInd L d u δ (r j) := hmono
        _ = (n : ℝ) * ∫ r in Submission.BoseGases.abox n L,
              ∑ j : Fin n, collarInd L d u δ (r j) := by
            rw [MeasureTheory.integral_const_mul]
        _ ≤ (n : ℝ) * (Cab * δ) :=
            mul_le_mul_of_nonneg_left (hSint δ hδ) (Nat.cast_nonneg n)
        _ = ((n : ℝ) * Cab) * δ := by ring
    -- the bound on the squared normalised collar volume
    have hb2 : b ^ 2 ≤ (Ca * Cm) ^ 2 * δ := by
      have h1 : b ^ 2 ≤ (Ca * Cm * δ) ^ 2 := by
        rw [sq_le_sq]
        refine abs_le.mpr ⟨by linarith [hb0, abs_nonneg (Ca * Cm * δ)], ?_⟩
        rwa [abs_of_nonneg (mul_nonneg (mul_nonneg hCa0 hCm0) hδ.le)]
      have h2 : (Ca * Cm * δ) ^ 2 ≤ (Ca * Cm) ^ 2 * δ := by
        have h3 : δ ^ 2 ≤ δ := by nlinarith [hδ.le, hδ1]
        nlinarith [h3, mul_nonneg (mul_nonneg hCa0 hCm0) hδ.le, sq_nonneg (Ca * Cm)]
      linarith
    -- assembling
    refine hstep.trans (hrval.le.trans ?_)
    have hY1 : A0 * 3 * V * (L ^ 3) ^ n ≤ A0 * 3 * (Ca * (L ^ 3) ^ n) * δ := by
      have h1 : V * (L ^ 3) ^ n ≤ Ca * (L ^ 3) ^ n * δ := by
        have h2 : V * (L ^ 3) ^ n ≤ Ca * δ * (L ^ 3) ^ n :=
          mul_le_mul_of_nonneg_right hVle' (pow_nonneg (pow_nonneg hL.le 3) n)
        calc V * (L ^ 3) ^ n ≤ Ca * δ * (L ^ 3) ^ n := h2
          _ = Ca * (L ^ 3) ^ n * δ := by ring
      calc A0 * 3 * V * (L ^ 3) ^ n = (A0 * 3) * (V * (L ^ 3) ^ n) := by ring
        _ ≤ (A0 * 3) * (Ca * (L ^ 3) ^ n * δ) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = A0 * 3 * (Ca * (L ^ 3) ^ n) * δ := by ring
    have hY2 : (A0 * 3 * (L ^ 3))
          * (∫ r in Submission.BoseGases.abox n L, (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
        ≤ (A0 * 3 * (L ^ 3)) * (((n : ℝ) * Cab) * δ) :=
      mul_le_mul_of_nonneg_left hS2b (by positivity)
    have hY3 : (A0 * 3 * (L ^ 3)) * b ^ 2 * (L ^ 3) ^ n
        ≤ (A0 * 3 * (L ^ 3)) * ((Ca * Cm) ^ 2 * (L ^ 3) ^ n) * δ := by
      have h1 : b ^ 2 * (L ^ 3) ^ n ≤ (Ca * Cm) ^ 2 * (L ^ 3) ^ n * δ := by
        have h2 : b ^ 2 * (L ^ 3) ^ n ≤ (Ca * Cm) ^ 2 * δ * (L ^ 3) ^ n :=
          mul_le_mul_of_nonneg_right hb2 (pow_nonneg (pow_nonneg hL.le 3) n)
        calc b ^ 2 * (L ^ 3) ^ n ≤ (Ca * Cm) ^ 2 * δ * (L ^ 3) ^ n := h2
          _ = (Ca * Cm) ^ 2 * (L ^ 3) ^ n * δ := by ring
      calc (A0 * 3 * (L ^ 3)) * b ^ 2 * (L ^ 3) ^ n
          = (A0 * 3 * (L ^ 3)) * (b ^ 2 * (L ^ 3) ^ n) := by ring
        _ ≤ (A0 * 3 * (L ^ 3)) * ((Ca * Cm) ^ 2 * (L ^ 3) ^ n * δ) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (A0 * 3 * (L ^ 3)) * ((Ca * Cm) ^ 2 * (L ^ 3) ^ n) * δ := by ring
    have hsumY : A0 * 3 * (Ca * (L ^ 3) ^ n) * δ
          + (A0 * 3 * (L ^ 3)) * (((n : ℝ) * Cab) * δ)
          + (A0 * 3 * (L ^ 3)) * ((Ca * Cm) ^ 2 * (L ^ 3) ^ n) * δ
        = (A0 * 3 * (Ca * (L ^ 3) ^ n + (L ^ 3) * ((n : ℝ) * Cab)
            + (L ^ 3) * (Ca * Cm) ^ 2 * (L ^ 3) ^ n)) * δ := by ring
    linarith [hY1, hY2, hY3, hsumY]
  -- the summed estimate
  have hsum : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → (∑ i : Fin (n+1), fibreDirI L
        (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) i (slotDiffState L d u (γ δ) ψ))
      ≤ ((↑(n+1) : ℝ) * (A0 * 3 * (Ca * (L ^ 3) ^ n + (L ^ 3) * ((n : ℝ) * Cab)
          + (L ^ 3) * (Ca * Cm) ^ 2 * (L ^ 3) ^ n))) * δ := by
    intro δ hδ hδ1
    calc ∑ i : Fin (n+1), fibreDirI L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
          (slotDiffState L d u (γ δ) ψ)
        ≤ ∑ _i : Fin (n+1), (A0 * 3 * (Ca * (L ^ 3) ^ n + (L ^ 3) * ((n : ℝ) * Cab)
            + (L ^ 3) * (Ca * Cm) ^ 2 * (L ^ 3) ^ n)) * δ :=
          Finset.sum_le_sum (fun i _ => hslot δ hδ hδ1 i)
      _ = ((↑(n+1) : ℝ) * (A0 * 3 * (Ca * (L ^ 3) ^ n + (L ^ 3) * ((n : ℝ) * Cab)
            + (L ^ 3) * (Ca * Cm) ^ 2 * (L ^ 3) ^ n))) * δ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hev1 : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), δ ≤ 1 :=
    nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hev : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < δ ∧ δ ≤ 1 :=
    Filter.Eventually.and self_mem_nhdsWithin hev1
  refine ⟨⟨(↑(n+1) : ℝ) * (A0 * 3 * (Ca * (L ^ 3) ^ n + (L ^ 3) * ((n : ℝ) * Cab)
      + (L ^ 3) * (Ca * Cm) ^ 2 * (L ^ 3) ^ n)), by positivity, ?_⟩, ?_⟩
  · filter_upwards [hev] with δ hδ
    exact hsum δ hδ.1 hδ.2
  · refine squeeze_zero'
      (f := fun δ : ℝ => ∑ i : Fin (n+1), fibreDirI L (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
        (slotDiffState L d u (γ δ) ψ))
      (g := fun δ : ℝ => ((↑(n+1) : ℝ) * (A0 * 3 * (Ca * (L ^ 3) ^ n + (L ^ 3) * ((n : ℝ) * Cab)
        + (L ^ 3) * (Ca * Cm) ^ 2 * (L ^ 3) ^ n))) * δ) ?_ ?_ ?_
    · filter_upwards with δ
      exact Finset.sum_nonneg (fun i _ => by
        rw [fibreDirI_eq]
        refine integral_nonneg (fun r => integral_nonneg (fun y => ?_))
        exact Finset.sum_nonneg (fun k _ => sq_nonneg _))
    · filter_upwards [hev] with δ hδ
      exact hsum δ hδ.1 hδ.2
    · have hcont : Filter.Tendsto (fun δ : ℝ =>
          ((↑(n+1) : ℝ) * (A0 * 3 * (Ca * (L ^ 3) ^ n + (L ^ 3) * ((n : ℝ) * Cab)
            + (L ^ 3) * (Ca * Cm) ^ 2 * (L ^ 3) ^ n))) * δ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        have h2 : Filter.Tendsto (fun δ : ℝ => δ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        simpa using h2.const_mul
          ((↑(n+1) : ℝ) * (A0 * 3 * (Ca * (L ^ 3) ^ n + (L ^ 3) * ((n : ℝ) * Cab)
            + (L ^ 3) * (Ca * Cm) ^ 2 * (L ^ 3) ^ n)))
      exact hcont

end Work.BoseFixB1B.B1Bfix
