import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseFixB1B.CutFibreForms
import Submission.Work.BoseFixB1B.chiB_abs_le_boxMargin
import Submission.Work.BoseFixB1B.collarCylinder
import Submission.Work.BoseFixB1B.integral_abox_indep_mul_coord
import Submission.Work.BoseFixB1B.volume_boxMargin_lt_support
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.B1Bfix2.CutFibreBase`

Self-contained base for the `B1Bfix2` fibre estimates: the collar indicator `collarInd` of the
sliding box, the explicit slot-fibre derivative `fderiv_Gfun_fibre` of the difference state
`Gfun g ψ B = cutProd g ψ − 1_{B^k}ψ`, the collar/integral estimates for `chiB`, and the
elementary supremum and moment bounds for the window.

This is the *frozen* part of `Submission.Work.BoseFixB1B.tendsto_cutFibreDir_sub` (everything
before the latter's still-open completion of the `O(δ)` estimate), kept here so that the
`B1Bfix2` development does not depend on that in-progress module.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The sharp box state as a product of slot indicators -/

/-- The sharp in-box state is the product of the slot indicators times `ψ`. -/
theorem sharpBoxState_eq_prod {k : ℕ} (B : Set E3) (ψ : Submission.BoseGases.X k → ℝ) :
    sharpBoxState B ψ
      = fun x : Submission.BoseGases.X k =>
          (∏ j : Fin k, B.indicator (fun _ => (1 : ℝ)) (x j)) * ψ x := by
  classical
  funext x
  show (Work.PerSector.slotBox (ι := Fin k) B).indicator ψ x = _
  rw [Work.PerSector.slotBox, Set.indicator_apply]
  change (if (∀ j : Fin k, x j ∈ B) then ψ x else 0)
      = (∏ j : Fin k, B.indicator (fun _ => (1 : ℝ)) (x j)) * ψ x
  by_cases h : ∀ j : Fin k, x j ∈ B
  · rw [if_pos h]
    have hone : (∏ j : Fin k, B.indicator (fun _ => (1 : ℝ)) (x j)) = (1 : ℝ) :=
      Finset.prod_eq_one (fun j _ => by rw [Set.indicator_of_mem (h j)])
    rw [hone, one_mul]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨j, hj⟩ := h
    have hz : B.indicator (fun _ => (1 : ℝ)) (x j) = 0 := Set.indicator_of_notMem hj _
    rw [Finset.prod_eq_zero (Finset.mem_univ j) hz]
    simp

/-- The ambient product of the cutoffs. -/
def Fprod {k : ℕ} (g : E3 → ℝ) (x : Submission.BoseGases.X k) : ℝ := ∏ j : Fin k, g (x j)

/-- The ambient product of the slot indicators of the box. -/
def FprodB {k : ℕ} (B : Set E3) (x : Submission.BoseGases.X k) : ℝ :=
  ∏ j : Fin k, B.indicator (fun _ => (1 : ℝ)) (x j)

@[simp] lemma Fprod_apply {k : ℕ} (g : E3 → ℝ) (x : Submission.BoseGases.X k) :
    Fprod g x = ∏ j : Fin k, g (x j) := rfl

@[simp] lemma FprodB_apply {k : ℕ} (B : Set E3) (x : Submission.BoseGases.X k) :
    FprodB B x = ∏ j : Fin k, B.indicator (fun _ => (1 : ℝ)) (x j) := rfl

lemma cutProd_eq_Fprod {k : ℕ} (g : E3 → ℝ) (ψ : Submission.BoseGases.X k → ℝ) :
    cutProd g ψ = fun x => Fprod g x * ψ x := rfl

lemma sharpBoxState_eq_FprodB {k : ℕ} (B : Set E3) (ψ : Submission.BoseGases.X k → ℝ) :
    sharpBoxState B ψ = fun x => FprodB B x * ψ x := sharpBoxState_eq_prod B ψ

/-! ## 2. The collar indicator and the pointwise cutoff facts -/

/-- The collar indicator of the cutoff family: `1` on the part of the sliding box on which the
box margin is `≤ δ`, `0` elsewhere. -/
def collarInd (L d : ℝ) (u : E3) (δ : ℝ) (x : E3) : ℝ :=
  (Submission.BoseGases.dlBox L d u ∩ {y : E3 | boxMargin L d u y ≤ δ}).indicator
    (fun _ => (1 : ℝ)) x

lemma collarInd_nonneg (L d : ℝ) (u : E3) (δ : ℝ) (x : E3) : 0 ≤ collarInd L d u δ x :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) x

lemma collarInd_le_one (L d : ℝ) (u : E3) (δ : ℝ) (x : E3) : collarInd L d u δ x ≤ 1 := by
  classical
  by_cases h : x ∈ Submission.BoseGases.dlBox L d u ∩ {y : E3 | boxMargin L d u y ≤ δ}
  · rw [collarInd, Set.indicator_of_mem h]
  · rw [collarInd, Set.indicator_of_notMem h]
    norm_num

lemma collarInd_eq_one_or_zero (L d : ℝ) (u : E3) (δ : ℝ) (x : E3) :
    collarInd L d u δ x = 1 ∨ collarInd L d u δ x = 0 := by
  classical
  by_cases h : x ∈ Submission.BoseGases.dlBox L d u ∩ {y : E3 | boxMargin L d u y ≤ δ}
  · exact Or.inl (Set.indicator_of_mem h _)
  · exact Or.inr (Set.indicator_of_notMem h _)

lemma collarInd_sq (L d : ℝ) (u : E3) (δ : ℝ) (x : E3) :
    collarInd L d u δ x ^ 2 = collarInd L d u δ x := by
  rcases collarInd_eq_one_or_zero L d u δ x with h | h <;> rw [h] <;> norm_num

lemma collarInd_apply_of (L d : ℝ) (u : E3) {δ : ℝ} {x : E3}
    (h : x ∈ Submission.BoseGases.dlBox L d u ∧ boxMargin L d u x ≤ δ) :
    collarInd L d u δ x = 1 := by
  rw [collarInd, Set.indicator_of_mem (show x ∈ Submission.BoseGases.dlBox L d u ∩
    {y : E3 | boxMargin L d u y ≤ δ} from h)]

lemma collarInd_apply_of_not (L d : ℝ) (u : E3) {δ : ℝ} {x : E3}
    (h : ¬ (x ∈ Submission.BoseGases.dlBox L d u ∧ boxMargin L d u x ≤ δ)) :
    collarInd L d u δ x = 0 := by
  rw [collarInd, Set.indicator_of_notMem (show x ∉ Submission.BoseGases.dlBox L d u ∩
    {y : E3 | boxMargin L d u y ≤ δ} from h)]

lemma collarInd_eq_indicator (L d : ℝ) (u : E3) (δ : ℝ) (x : E3) :
    collarInd L d u δ x
      = (Submission.BoseGases.dlBox L d u ∩ {y : E3 | boxMargin L d u y ≤ δ}).indicator
          (fun _ => (1 : ℝ)) x := rfl

/-- The sliding box is closed. -/
lemma isClosed_dlBox' {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3) :
    IsClosed (Submission.BoseGases.dlBox L d u) :=
  (Work.SmallBoxTBWord.isCompact_dlBox hL hd u).isClosed

/-- The cutoff vanishes off the sliding box. -/
lemma gamma_eq_zero_of_notMem {L d : ℝ} {K : ℝ} {γ : ℝ → E3 → ℝ} {u : E3}
    {hcut : IsCutFamily L d u K γ} {δ : ℝ} (hδ : 0 < δ)
    {x : E3} (hx : x ∉ Submission.BoseGases.dlBox L d u) : γ δ x = 0 := by
  by_contra hne
  exact hx ((hcut.2 δ hδ).2.1 (subset_tsupport (γ δ) (Function.mem_support.mpr hne)))

/-- The cutoff is locally `1` at points of the box of margin `> δ`. -/
lemma gamma_eventuallyEq_one {L d : ℝ} {K : ℝ} {γ : ℝ → E3 → ℝ} {u : E3}
    {hcut : IsCutFamily L d u K γ} {δ : ℝ} (hδ : 0 < δ) {x : E3}
    (hm : δ < boxMargin L d u x) :
    γ δ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
  have hopen : IsOpen {z : E3 | δ < boxMargin L d u z} :=
    isOpen_lt continuous_const (continuous_boxMargin_aux L d u)
  filter_upwards [hopen.mem_nhds hm] with z hz
  exact (hcut.2 δ hδ).2.2.2.1 z (le_of_lt hz)

/-- The cutoff is locally zero off the sliding box. -/
lemma gamma_eventuallyEq_zero {L d : ℝ} {K : ℝ} {γ : ℝ → E3 → ℝ} {u : E3}
    {hcut : IsCutFamily L d u K γ} (hclosed : IsClosed (Submission.BoseGases.dlBox L d u))
    {δ : ℝ} (hδ : 0 < δ) {x : E3} (hx : x ∉ Submission.BoseGases.dlBox L d u) :
    γ δ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
  obtain ⟨ε, hεpos, hεsub⟩ := (Metric.isOpen_iff.mp hclosed.isOpen_compl) x hx
  filter_upwards [Metric.ball_mem_nhds x hεpos] with z hz
  exact gamma_eq_zero_of_notMem (hcut := hcut) hδ
    (fun hmem => hεsub (Metric.mem_ball.mpr hz) hmem)

/-- The derivative of a function that is locally constant vanishes. -/
lemma fderiv_eq_zero_of_eventuallyEq_const {f : E3 → ℝ} {x : E3} {c : ℝ}
    (h : f =ᶠ[𝓝 x] fun _ => c) : fderiv ℝ f x = 0 := by
  rw [h.fderiv_eq]
  simp

/-- The cutoff differs from the box indicator only on the collar. -/
lemma abs_gamma_sub_indicator_le_collarInd {L d : ℝ} {K : ℝ} {γ : ℝ → E3 → ℝ} {u : E3}
    {hcut : IsCutFamily L d u K γ} {δ : ℝ} (hδ : 0 < δ) (x : E3) :
    |γ δ x - (Submission.BoseGases.dlBox L d u).indicator (fun _ => (1 : ℝ)) x|
      ≤ collarInd L d u δ x := by
  by_cases h : x ∈ Submission.BoseGases.dlBox L d u ∧ boxMargin L d u x ≤ δ
  · rw [collarInd_apply_of L d u h, Set.indicator_of_mem h.1]
    have hγ := (hcut.2 δ hδ).2.2.1 x
    rw [abs_le]
    exact ⟨by linarith [hγ.1], by linarith [hγ.2]⟩
  · rw [collarInd_apply_of_not L d u h]
    by_cases hxB : x ∈ Submission.BoseGases.dlBox L d u
    · have hm : δ < boxMargin L d u x := lt_of_not_ge (fun hle => h ⟨hxB, hle⟩)
      rw [Set.indicator_of_mem hxB, (hcut.2 δ hδ).2.2.2.1 x (le_of_lt hm), sub_self, abs_zero]
    · rw [Set.indicator_of_notMem hxB, gamma_eq_zero_of_notMem (hcut := hcut) hδ hxB, sub_zero,
        abs_zero]

/-- The directional derivative of the cutoff is dominated by the collar indicator. -/
lemma abs_fderiv_gamma_le_collarInd {L d : ℝ} {K : ℝ} {γ : ℝ → E3 → ℝ} {u : E3}
    {hcut : IsCutFamily L d u K γ} (hclosed : IsClosed (Submission.BoseGases.dlBox L d u))
    {δ : ℝ} (hδ : 0 < δ) (x : E3) (k : Fin 3) :
    |fderiv ℝ (γ δ) x (kcStdBasis k)| ≤ (K / δ) * collarInd L d u δ x := by
  by_cases h : x ∈ Submission.BoseGases.dlBox L d u ∧ boxMargin L d u x ≤ δ
  · rw [collarInd_apply_of L d u h, mul_one]
    have h1 := (hcut.2 δ hδ).2.2.2.2 x
    have h2 : ‖kcStdBasis k‖ = 1 := by
      simp [Submission.BoseGases.kcStdBasis, PiLp.norm_single]
    calc |fderiv ℝ (γ δ) x (kcStdBasis k)| = ‖fderiv ℝ (γ δ) x (kcStdBasis k)‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (γ δ) x‖ * ‖kcStdBasis k‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (γ δ) x‖ := by rw [h2, mul_one]
      _ ≤ K / δ := h1
  · rw [collarInd_apply_of_not L d u h, mul_zero]
    by_cases hxB : x ∈ Submission.BoseGases.dlBox L d u
    · have hm : δ < boxMargin L d u x := lt_of_not_ge (fun hle => h ⟨hxB, hle⟩)
      rw [fderiv_eq_zero_of_eventuallyEq_const (gamma_eventuallyEq_one (hcut := hcut) hδ hm)]
      simp
    · rw [fderiv_eq_zero_of_eventuallyEq_const
        (gamma_eventuallyEq_zero (K := K) (γ := γ) (hcut := hcut) hclosed hδ hxB)]
      simp

/-! ## 3. The state `G δ = cutProd (γ δ) ψ - sharpBoxState B ψ` and its fibre derivative -/

/-- The state whose peeled fibre Dirichlet form is estimated: the difference of the smooth
approximant and the sharp box state. -/
def Gfun {k : ℕ} (g : E3 → ℝ) (ψ : Submission.BoseGases.X k → ℝ) (B : Set E3) :
    Submission.BoseGases.X k → ℝ :=
  fun x => cutProd g ψ x - sharpBoxState B ψ x

lemma Gfun_apply {k : ℕ} (g : E3 → ℝ) (ψ : Submission.BoseGases.X k → ℝ) (B : Set E3)
    (x : Submission.BoseGases.X k) :
    Gfun g ψ B x = Fprod g x * ψ x - FprodB B x * ψ x := by
  rw [Gfun, cutProd_eq_Fprod, sharpBoxState_eq_FprodB]

/-- The product of the cutoffs over the slots other than `i`. -/
def FprodOther {n : ℕ} (g : E3 → ℝ) (i : Fin (n + 1))
    (x : Submission.BoseGases.X (n + 1)) : ℝ :=
  ∏ j : Fin n, g (x (i.succAbove j))

/-- The product of the slot indicators over the coordinates outside the slot `i`. -/
def FprodBr {n : ℕ} (B : Set E3) (r : Submission.BoseGases.X n) : ℝ :=
  ∏ j : Fin n, B.indicator (fun _ => (1 : ℝ)) (r j)

lemma Fprod_eq_mul_FprodOther {n : ℕ} (g : E3 → ℝ) (i : Fin (n + 1))
    (x : Submission.BoseGases.X (n + 1)) :
    Fprod g x = g (x i) * FprodOther g i x := by
  rw [Fprod, FprodOther, Fin.prod_univ_succAbove (fun j : Fin (n + 1) => g (x j)) i]

lemma FprodOther_kcInsN_eq {n : ℕ} (g : E3 → ℝ) (i : Fin (n + 1)) (z : E3)
    (r : Submission.BoseGases.X n) :
    FprodOther g i (kcInsN n i (z, r)) = ∏ j : Fin n, g (r j) :=
  Finset.prod_congr rfl (fun j _ => by rw [kc_insN_apply_succ])

lemma FprodOther_const_line {n : ℕ} (g : E3 → ℝ) (i : Fin (n + 1))
    (x : Submission.BoseGases.X (n + 1)) (k : Fin 3) (t : ℝ) :
    FprodOther g i (x + t • kcDir (n + 1) i k) = FprodOther g i x := by
  refine Finset.prod_congr rfl (fun j _ => ?_)
  congr 1
  have hk : (kcDir (n + 1) i k) (i.succAbove j) = 0 := by
    rw [kcDir, Function.update_of_ne (Fin.succAbove_ne i j)]
    rfl
  rw [Pi.add_apply, Pi.smul_apply, hk, smul_zero, add_zero]

lemma contDiff_FprodOther {n : ℕ} {g : E3 → ℝ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (i : Fin (n + 1)) : ContDiff ℝ (⊤ : ENat) (FprodOther g i) := by
  unfold FprodOther
  fun_prop

/-- The product of the cutoffs is smooth. -/
lemma contDiff_Fprod {n : ℕ} {g : E3 → ℝ} (hg : ContDiff ℝ (⊤ : ENat) g) :
    ContDiff ℝ (⊤ : ENat) (Fprod (k := n) g) := by
  unfold Fprod
  fun_prop

/-- **The chain rule for the product of the cutoffs** along the slot-`i` direction: only the
`i`-th factor contributes. -/
lemma fderiv_Fprod_kcDir {n : ℕ} {g : E3 → ℝ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (i : Fin (n + 1)) (x : Submission.BoseGases.X (n + 1)) (k : Fin 3) :
    fderiv ℝ (Fprod g) x (kcDir (n + 1) i k)
      = FprodOther g i x * fderiv ℝ g (x i) (kcStdBasis k) := by
  have hsplit : Fprod g
      = (fun y : Submission.BoseGases.X (n + 1) => g (y i)) * FprodOther g i := by
    funext y
    rw [Pi.mul_apply, Fprod_eq_mul_FprodOther]
  rw [hsplit]
  have h1 : DifferentiableAt ℝ (fun y : Submission.BoseGases.X (n + 1) => g (y i)) x :=
    (hg.comp (by fun_prop)).differentiable (by simp) x
  have h2 : DifferentiableAt ℝ (FprodOther g i) x :=
    (contDiff_FprodOther hg i).differentiable (by simp) x
  have hmul := congrArg (fun (L : Submission.BoseGases.X (n + 1) →L[ℝ] ℝ) =>
      L (kcDir (n + 1) i k)) (fderiv_mul h1 h2)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at hmul
  rw [hmul, Work.SmallBoxTBWord.fderiv_apply_eq_zero_of_const_line h2
      (FprodOther_const_line g i x k),
    Work.SmallBoxTBWord.fderiv_chi_apply_kcDir hg i x k]
  ring

/-- **The chain-rule bound**: the directional derivative of the product of the cutoffs is
dominated by the directional derivative of the single cutoff. -/
lemma abs_fderiv_Fprod_kcDir_le {L d : ℝ} (hL : 0 < L) (hd : 0 < d) {K : ℝ}
    {γ : ℝ → E3 → ℝ} {u : E3} {hcut : IsCutFamily L d u K γ} {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (i : Fin (n + 1)) (x : Submission.BoseGases.X (n + 1)) (k : Fin 3) :
    |fderiv ℝ (Fprod (γ δ)) x (kcDir (n + 1) i k)|
      ≤ (K / δ) * collarInd L d u δ (x i) := by
  have hcd : ContDiff ℝ (⊤ : ENat) (γ δ) := (hcut.2 δ hδ).1
  rw [fderiv_Fprod_kcDir hcd i x k, abs_mul]
  have h1 : |FprodOther (γ δ) i x| ≤ 1 := by
    rw [FprodOther, Finset.abs_prod]
    refine Finset.prod_le_one₀ (fun j _ => abs_nonneg _) (fun j _ => ?_)
    rw [abs_of_nonneg ((hcut.2 δ hδ).2.2.1 (x (i.succAbove j))).1]
    exact ((hcut.2 δ hδ).2.2.1 (x (i.succAbove j))).2
  have h2 := abs_fderiv_gamma_le_collarInd (L := L) (d := d) (K := K) (γ := γ) (u := u)
    (hcut := hcut) (isClosed_dlBox' (L := L) (d := d) hL hd u) hδ (x i) k
  calc |FprodOther (γ δ) i x| * |fderiv ℝ (γ δ) (x i) (kcStdBasis k)|
      ≤ 1 * ((K / δ) * collarInd L d u δ (x i)) :=
        mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = (K / δ) * collarInd L d u δ (x i) := one_mul _

/-! ## 4. The box mean over the sliding box is constant in the slot-`i` coordinate -/

lemma boxP_kcInsN_eq {L d : ℝ} {u : E3} {n : ℕ} (volA : ℝ) (i : Fin (n + 1))
    (G : Submission.BoseGases.X (n + 1) → ℝ) (y z : E3) (r : Submission.BoseGases.X n) :
    Work.SmallBoxTBWord.boxP volA (Submission.BoseGases.dlBox L d u) i G (kcInsN n i (y, r))
      = Work.SmallBoxTBWord.boxP volA (Submission.BoseGases.dlBox L d u) i G (kcInsN n i (z, r)) := by
  simp only [Work.SmallBoxTBWord.boxP]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  simp only [Work.SmallBoxBridge.Fourier.update_kcInsN]

/-! ## 5. Local constancy of the slot indicators along the fibre -/

/-- The box indicator is locally constant at a point of nonzero box margin. -/
lemma indicator_dlBox_eventuallyEq {L d : ℝ} {u : E3} {x : E3} (hx : boxMargin L d u x ≠ 0) :
    (fun z : E3 => (Submission.BoseGases.dlBox L d u).indicator (fun _ => (1 : ℝ)) z)
      =ᶠ[𝓝 x] fun _ => (Submission.BoseGases.dlBox L d u).indicator (fun _ => (1 : ℝ)) x := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hxnot : x ∉ Submission.BoseGases.dlBox L d u := fun hmem =>
      absurd (boxMargin_nonneg_iff.mpr hmem) (not_le.mpr hneg)
    have hopen : IsOpen {z : E3 | boxMargin L d u z < 0} :=
      isOpen_lt (continuous_boxMargin_aux L d u) continuous_const
    filter_upwards [hopen.mem_nhds hneg] with z hz
    have hznot : z ∉ Submission.BoseGases.dlBox L d u := fun hmem =>
      absurd (boxMargin_nonneg_iff.mpr hmem) (not_le.mpr hz)
    rw [Set.indicator_of_notMem hznot, Set.indicator_of_notMem hxnot]
  · have hxmem : x ∈ Submission.BoseGases.dlBox L d u := boxMargin_nonneg_iff.mp hpos.le
    have hopen : IsOpen {z : E3 | 0 < boxMargin L d u z} :=
      isOpen_lt continuous_const (continuous_boxMargin_aux L d u)
    filter_upwards [hopen.mem_nhds hpos] with z hz
    rw [Set.indicator_of_mem (boxMargin_nonneg_iff.mp hz.le), Set.indicator_of_mem hxmem]

/-- Splitting the product of the slot indicators of the fibre at the slot `i`. -/
lemma FprodB_kcInsN_eq {L d : ℝ} {u : E3} {n : ℕ} (i : Fin (n + 1)) (z : E3)
    (r : Submission.BoseGases.X n) :
    FprodB (Submission.BoseGases.dlBox L d u) (kcInsN n i (z, r))
      = (Submission.BoseGases.dlBox L d u).indicator (fun _ => (1 : ℝ)) z
        * FprodBr (Submission.BoseGases.dlBox L d u) r := by
  rw [FprodB, Fin.prod_univ_succAbove
      (fun j : Fin (n + 1) => (Submission.BoseGases.dlBox L d u).indicator (fun _ => (1 : ℝ))
        ((kcInsN n i (z, r)) j)) i, kc_insN_apply_same]
  congr 1
  rw [FprodBr]
  exact Finset.prod_congr rfl (fun j _ => by rw [kc_insN_apply_succ])

/-- The product of the slot indicators of the fibre is locally constant as a function of the
inserted slot-`i` coordinate. -/
lemma FprodB_fibre_eventuallyEq {L d : ℝ} {u : E3} {n : ℕ} (i : Fin (n + 1))
    (r : Submission.BoseGases.X n) {y : E3} (hy : boxMargin L d u y ≠ 0) :
    (fun z : E3 => FprodB (Submission.BoseGases.dlBox L d u) (kcInsN n i (z, r)))
      =ᶠ[𝓝 y] fun _ => FprodB (Submission.BoseGases.dlBox L d u) (kcInsN n i (y, r)) := by
  have hloc := indicator_dlBox_eventuallyEq (L := L) (d := d) (u := u) hy
  have hL : (fun z : E3 => FprodB (Submission.BoseGases.dlBox L d u) (kcInsN n i (z, r)))
      = (fun z : E3 => (Submission.BoseGases.dlBox L d u).indicator (fun _ => (1 : ℝ)) z)
        * fun _ : E3 => FprodBr (Submission.BoseGases.dlBox L d u) r := by
    funext z
    rw [Pi.mul_apply, FprodB_kcInsN_eq]
  have hR : (fun _ : E3 => FprodB (Submission.BoseGases.dlBox L d u) (kcInsN n i (y, r)))
      = (fun _ : E3 => (Submission.BoseGases.dlBox L d u).indicator (fun _ => (1 : ℝ)) y)
        * fun _ : E3 => FprodBr (Submission.BoseGases.dlBox L d u) r := by
    funext z
    rw [Pi.mul_apply, FprodB_kcInsN_eq]
  rw [hL, hR]
  exact hloc.mul (Filter.EventuallyEq.refl _ _)

/-- The local model of the fibre of `G δ` at a configuration with nonzero box margin. -/
def fibreModel {n : ℕ} (g : E3 → ℝ) (ψ : Submission.BoseGases.X (n + 1) → ℝ) (i : Fin (n + 1))
    (r : Submission.BoseGases.X n) (c : ℝ) : E3 → ℝ :=
  fun z => (Fprod g (kcInsN n i (z, r)) - c) * ψ (kcInsN n i (z, r))

/-- The fibre of `G δ` agrees near `y` (of nonzero box margin) with the local model. -/
lemma Gfun_fibre_eventuallyEq {L d : ℝ} {u : E3} {n : ℕ} {g : E3 → ℝ}
    {ψ : Submission.BoseGases.X (n + 1) → ℝ} (i : Fin (n + 1)) (r : Submission.BoseGases.X n)
    {y : E3} (hy : boxMargin L d u y ≠ 0) :
    (fun z : E3 => Gfun g ψ (Submission.BoseGases.dlBox L d u) (kcInsN n i (z, r)))
      =ᶠ[𝓝 y] fibreModel g ψ i r (FprodB (Submission.BoseGases.dlBox L d u)
        (kcInsN n i (y, r))) := by
  have hB := FprodB_fibre_eventuallyEq (L := L) (d := d) (u := u) i r hy
  filter_upwards [hB] with z hz
  rw [Gfun_apply, hz]
  simp only [fibreModel]
  ring

/-- Smoothness of the local model. -/
lemma contDiff_fibreModel {n : ℕ} {g : E3 → ℝ} (hg : ContDiff ℝ (⊤ : ENat) g)
    {ψ : Submission.BoseGases.X (n + 1) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (i : Fin (n + 1)) (r : Submission.BoseGases.X n) (c : ℝ) :
    ContDiff ℝ (⊤ : ENat) (fibreModel g ψ i r c) := by
  have hcomp : ContDiff ℝ (⊤ : ENat) (fun z : E3 => Fprod g (kcInsN n i (z, r))) := by
    have h1 : ContDiff ℝ (⊤ : ENat) (Fprod (k := n + 1) g) := contDiff_Fprod (n := n + 1) hg
    exact h1.comp (Work.SmallBoxBridge.Fourier.contDiff_kcInsN_right i r)
  have hψc : ContDiff ℝ (⊤ : ENat) (fun z : E3 => ψ (kcInsN n i (z, r))) :=
    hψ.comp (Work.SmallBoxBridge.Fourier.contDiff_kcInsN_right i r)
  rw [show fibreModel g ψ i r c
      = ((fun z : E3 => Fprod g (kcInsN n i (z, r))) - (fun _ : E3 => c))
        * (fun z : E3 => ψ (kcInsN n i (z, r))) from rfl]
  exact (hcomp.sub contDiff_const).mul hψc

/-- The derivative of the local model along the slot-`i` direction. -/
lemma fderiv_fibreModel {n : ℕ} {g : E3 → ℝ} (hg : ContDiff ℝ (⊤ : ENat) g)
    {ψ : Submission.BoseGases.X (n + 1) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (i : Fin (n + 1)) (r : Submission.BoseGases.X n) (c : ℝ) (y : E3) (k : Fin 3) :
    fderiv ℝ (fibreModel g ψ i r c) y (kcStdBasis k)
      = (Fprod g (kcInsN n i (y, r)) - c)
          * fderiv ℝ ψ (kcInsN n i (y, r)) (kcDir (n + 1) i k)
        + ψ (kcInsN n i (y, r)) * fderiv ℝ (Fprod g) (kcInsN n i (y, r)) (kcDir (n + 1) i k) := by
  rw [show fibreModel g ψ i r c
      = ((fun z : E3 => Fprod g (kcInsN n i (z, r))) - (fun _ : E3 => c))
        * (fun z : E3 => ψ (kcInsN n i (z, r))) from rfl]
  have hcomp : ContDiff ℝ (⊤ : ENat) (fun z : E3 => Fprod g (kcInsN n i (z, r))) := by
    have h1 : ContDiff ℝ (⊤ : ENat) (Fprod (k := n + 1) g) := contDiff_Fprod (n := n + 1) hg
    exact h1.comp (Work.SmallBoxBridge.Fourier.contDiff_kcInsN_right i r)
  have hA : DifferentiableAt ℝ
      ((fun z : E3 => Fprod g (kcInsN n i (z, r))) - (fun _ : E3 => c)) y :=
    (hcomp.sub contDiff_const).differentiable (by simp) y
  have hB : DifferentiableAt ℝ (fun z : E3 => ψ (kcInsN n i (z, r))) y :=
    (hψ.comp (Work.SmallBoxBridge.Fourier.contDiff_kcInsN_right i r)).differentiable (by simp) y
  have hmul := congrArg (fun (L : E3 →L[ℝ] ℝ) => L (kcStdBasis k)) (fderiv_mul hA hB)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at hmul
  have hdif : DifferentiableAt ℝ (fun z : E3 => Fprod g (kcInsN n i (z, r))) y :=
    hcomp.differentiable (by simp) y
  have hsub' : fderiv ℝ
        ((fun z : E3 => Fprod g (kcInsN n i (z, r))) - (fun _ : E3 => c)) y (kcStdBasis k)
      = fderiv ℝ (Fprod g) (kcInsN n i (y, r)) (kcDir (n + 1) i k) := by
    rw [fderiv_sub hdif (differentiableAt_const c)]
    simpa using
      (Submission.BoseGases.fiber_fderiv_kcDir i (contDiff_Fprod (n := n + 1) hg) r y k)
  have hB' : fderiv ℝ (fun z : E3 => ψ (kcInsN n i (z, r))) y (kcStdBasis k)
      = fderiv ℝ ψ (kcInsN n i (y, r)) (kcDir (n + 1) i k) :=
    Submission.BoseGases.fiber_fderiv_kcDir i hψ r y k
  rw [hsub', hB'] at hmul
  exact hmul

/-- The derivative of the windowed local model. -/
lemma fderiv_chi_fibreModel {L d : ℝ} (hL : 0 < L) (hd : 0 < d) {u : E3} {n : ℕ}
    {g : E3 → ℝ} (hg : ContDiff ℝ (⊤ : ENat) g) {ψ : Submission.BoseGases.X (n + 1) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (i : Fin (n + 1)) (r : Submission.BoseGases.X n)
    (c b : ℝ) (y : E3) (k : Fin 3) :
    fderiv ℝ ((chiB L d u) * ((fibreModel g ψ i r c) - (fun _ : E3 => b))) y (kcStdBasis k)
      = chiB L d u y
          * ((Fprod g (kcInsN n i (y, r)) - c)
                * fderiv ℝ ψ (kcInsN n i (y, r)) (kcDir (n + 1) i k)
              + fderiv ℝ (Fprod g) (kcInsN n i (y, r)) (kcDir (n + 1) i k)
                * ψ (kcInsN n i (y, r)))
        + fderiv ℝ (chiB L d u) y (kcStdBasis k)
          * ((Fprod g (kcInsN n i (y, r)) - c) * ψ (kcInsN n i (y, r)) - b) := by
  have hchi : ContDiff ℝ (⊤ : ENat) (chiB L d u) := Work.SmallBoxTBWord.contDiff_chiB hL hd u
  have hm : ContDiff ℝ (⊤ : ENat) ((fibreModel g ψ i r c) - (fun _ : E3 => b)) :=
    (contDiff_fibreModel hg hψ i r c).sub contDiff_const
  have hmd : DifferentiableAt ℝ ((fibreModel g ψ i r c) - (fun _ : E3 => b)) y :=
    hm.differentiable (by simp) y
  have hmul := congrArg (fun (L' : E3 →L[ℝ] ℝ) => L' (kcStdBasis k))
    (fderiv_mul (hchi.differentiable (by simp) y) hmd)
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

/-- **The derivative of the windowed slot-`i` fibre of `G δ`.**  At every configuration whose
slot-`i` coordinate has nonzero box margin, the Leibniz rule and the local constancy of the
sharp part give an explicit expression for the derivative. -/
theorem fderiv_Gfun_fibre {L d : ℝ} (hL : 0 < L) (hd : 0 < d) {K : ℝ} {γ : ℝ → E3 → ℝ}
    {u : E3} {hcut : IsCutFamily L d u K γ} {n : ℕ} {ψ : Submission.BoseGases.X (n + 1) → ℝ}
    {hψ : ContDiff ℝ (⊤ : ENat) ψ} {δ : ℝ} (hδ : 0 < δ) (i : Fin (n + 1)) (k : Fin 3)
    {y : E3} {r : Submission.BoseGases.X n} (hy : boxMargin L d u y ≠ 0) :
    fderiv ℝ (fun z : E3 => chiB L d u z * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i (Gfun (γ δ) ψ (Submission.BoseGases.dlBox L d u))
        (kcInsN n i (z, r))) y (kcStdBasis k)
      = chiB L d u y
          * ((Fprod (γ δ) (kcInsN n i (y, r))
                - FprodB (Submission.BoseGases.dlBox L d u) (kcInsN n i (y, r)))
              * fderiv ℝ ψ (kcInsN n i (y, r)) (kcDir (n + 1) i k)
            + fderiv ℝ (Fprod (γ δ)) (kcInsN n i (y, r)) (kcDir (n + 1) i k)
              * ψ (kcInsN n i (y, r)))
        + fderiv ℝ (chiB L d u) y (kcStdBasis k)
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
  have hmain : (fun z : E3 => chiB L d u z
        * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i (Gfun (γ δ) ψ (Submission.BoseGases.dlBox L d u))
          (kcInsN n i (z, r)))
      =ᶠ[𝓝 y] (chiB L d u) * ((fibreModel (γ δ) ψ i r
          (FprodB (Submission.BoseGases.dlBox L d u) (kcInsN n i (y, r))))
            - (fun _ : E3 => b)) := by
    filter_upwards [hG] with z hz
    rw [Work.SmallBoxTBWord.boxQ, hz, hP z]
    simp only [Pi.mul_apply, Pi.sub_apply]
  rw [Filter.EventuallyEq.fderiv_eq hmain]
  rw [fderiv_chi_fibreModel (L := L) (d := d) hL hd hcd hψ i r _ b y k]
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

/-- Telescoping product-difference bound: `|∏ a - ∏ b| ≤ Σ |a - b|` when `|a|, |b| ≤ 1`. -/
lemma abs_prod_sub_prod_le' {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  revert ha hb
  refine Finset.induction_on s ?_ ?_
  · intro ha hb; simp
  · intro i t hit ih ha hb
    rw [Finset.prod_insert hit, Finset.prod_insert hit, Finset.sum_insert hit]
    have ha_t : ∀ j ∈ t, |a j| ≤ 1 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hb_t : ∀ j ∈ t, |b j| ≤ 1 := fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have hih := ih ha_t hb_t
    have hai : |a i| ≤ 1 := ha i (Finset.mem_insert_self i t)
    have hprod_b : |∏ j ∈ t, b j| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun j hj => abs_nonneg _) (fun j hj => hb_t j hj)
    have key : a i * (∏ j ∈ t, a j) - b i * (∏ j ∈ t, b j)
        = a i * ((∏ j ∈ t, a j) - (∏ j ∈ t, b j)) + (a i - b i) * (∏ j ∈ t, b j) := by ring
    rw [key]
    calc |a i * ((∏ j ∈ t, a j) - (∏ j ∈ t, b j)) + (a i - b i) * (∏ j ∈ t, b j)|
        ≤ |a i * ((∏ j ∈ t, a j) - (∏ j ∈ t, b j))| + |(a i - b i) * (∏ j ∈ t, b j)| :=
          abs_add_le _ _
      _ = |a i| * |(∏ j ∈ t, a j) - (∏ j ∈ t, b j)| + |a i - b i| * |∏ j ∈ t, b j| := by
          rw [abs_mul, abs_mul]
      _ ≤ 1 * (∑ j ∈ t, |a j - b j|) + |a i - b i| * 1 := by
          apply add_le_add
          · exact mul_le_mul hai hih (abs_nonneg _) zero_le_one
          · exact mul_le_mul_of_nonneg_left hprod_b (abs_nonneg _)
      _ = |a i - b i| + ∑ j ∈ t, |a j - b j| := by ring

/-- The product of the cutoffs is close to the product of the sharp indicators. -/
lemma abs_Fprod_sub_FprodB_le' {L d : ℝ} {u : E3} {K : ℝ} {γ : ℝ → E3 → ℝ} {n : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hcut : IsCutFamily L d u K γ) (x : Submission.BoseGases.X (n + 1)) :
    |Fprod (γ δ) x - FprodB (Submission.BoseGases.dlBox L d u) x|
      ≤ ∑ j : Fin (n + 1), collarInd L d u δ (x j) := by
  rw [Fprod, FprodB]
  have hpt : ∀ j : Fin (n + 1),
      |γ δ (x j) - (Submission.BoseGases.dlBox L d u).indicator (fun _ => (1 : ℝ)) (x j)|
        ≤ collarInd L d u δ (x j) :=
    fun j => abs_gamma_sub_indicator_le_collarInd (hcut := hcut) hδ (x j)
  have ha : ∀ j ∈ (Finset.univ : Finset (Fin (n + 1))), |γ δ (x j)| ≤ 1 := by
    intro j _
    rw [abs_of_nonneg ((hcut.2 δ hδ).2.2.1 (x j)).1]
    exact ((hcut.2 δ hδ).2.2.1 (x j)).2
  have hb : ∀ j ∈ (Finset.univ : Finset (Fin (n + 1))),
      |(Submission.BoseGases.dlBox L d u).indicator (fun _ => (1 : ℝ)) (x j)| ≤ 1 := by
    intro j _
    by_cases h : x j ∈ Submission.BoseGases.dlBox L d u
    · rw [Set.indicator_of_mem h]; norm_num
    · rw [Set.indicator_of_notMem h]; norm_num
  calc |∏ j : Fin (n + 1), γ δ (x j)
          - ∏ j : Fin (n + 1),
              (Submission.BoseGases.dlBox L d u).indicator (fun _ => (1 : ℝ)) (x j)|
      ≤ ∑ j : Fin (n + 1),
          |γ δ (x j) - (Submission.BoseGases.dlBox L d u).indicator (fun _ => (1 : ℝ)) (x j)| :=
        abs_prod_sub_prod_le' Finset.univ _ _ ha hb
    _ ≤ ∑ j : Fin (n + 1), collarInd L d u δ (x j) := Finset.sum_le_sum (fun j _ => hpt j)

/-! ## 6. Sup and moment bounds for the window -/

/-- Sup bounds for the window `χ = chiB L d u` and for the square of its gradient. -/
lemma chiB_sup_bounds {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ y : E3, |Submission.BoseGases.chiB L d u y| ≤ C)
      ∧ (∀ y : E3, (∑ k : Fin 3, (fderiv ℝ (Submission.BoseGases.chiB L d u) y
          (Submission.BoseGases.kcStdBasis k)) ^ 2) ≤ C) := by
  have hcd : ContDiff ℝ (⊤ : ENat) (Submission.BoseGases.chiB L d u) :=
    Work.SmallBoxTBWord.contDiff_chiB hL hd u
  have hcs : HasCompactSupport (Submission.BoseGases.chiB L d u) :=
    Work.SmallBoxTBWord.hasCompactSupport_chiB hL hd u
  have hcontG : Continuous (fun y : E3 => ∑ k : Fin 3,
      (fderiv ℝ (Submission.BoseGases.chiB L d u) y (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
    have h1 : Continuous (fun y : E3 => fderiv ℝ (Submission.BoseGases.chiB L d u) y) :=
      hcd.continuous_fderiv (by simp)
    exact continuous_finsetSum _ (fun k _ => ((h1.clm_apply continuous_const).pow 2))
  obtain ⟨S, hS⟩ := hcs.exists_bound_of_continuousOn hcd.continuous.continuousOn
  obtain ⟨S', hS'⟩ := hcs.exists_bound_of_continuousOn hcontG.continuousOn
  have hvan : ∀ y ∉ tsupport (Submission.BoseGases.chiB L d u),
      Submission.BoseGases.chiB L d u y = 0 := by
    intro y hy
    by_contra hne
    exact hy (subset_tsupport _ (Function.mem_support.mpr hne))
  have hvanG : ∀ y ∉ tsupport (Submission.BoseGases.chiB L d u),
      (∑ k : Fin 3, (fderiv ℝ (Submission.BoseGases.chiB L d u) y
        (Submission.BoseGases.kcStdBasis k)) ^ 2) = 0 := by
    intro y hy
    have hzero : fderiv ℝ (Submission.BoseGases.chiB L d u) y = 0 := by
      obtain ⟨ε, hεpos, hεsub⟩ := (Metric.isOpen_iff.mp isClosed_closure.isOpen_compl) y hy
      have hev : (Submission.BoseGases.chiB L d u) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        filter_upwards [Metric.ball_mem_nhds y hεpos] with z hz
        exact hvan z (hεsub (Metric.mem_ball.mpr hz))
      rw [fderiv_eq_zero_of_eventuallyEq_const hev]
    simp [hzero]
  refine ⟨max (max S 0) (max S' 0), le_max_of_le_left (le_max_right _ _), ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ tsupport (Submission.BoseGases.chiB L d u)
    · have h := hS y hy
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_trans (le_max_left _ _) (le_max_left _ _))
    · rw [hvan y hy, abs_zero]
      exact le_max_of_le_left (le_max_right _ _)
  · intro y
    by_cases hy : y ∈ tsupport (Submission.BoseGases.chiB L d u)
    · have h := hS' y hy
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun k _ => sq_nonneg _))] at h
      exact le_trans h (le_max_of_le_right (le_max_left _ _))
    · rw [hvanG y hy]
      exact le_max_of_le_right (le_max_right _ _)

/-- The `L²`-mass of the window and the `L¹`-mass of the square of its gradient are bounded. -/
lemma chiB_moments {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3) :
    ∃ C : ℝ, 0 ≤ C ∧ (∫ y in Submission.BoseGases.acube L, (Submission.BoseGases.chiB L d u y) ^ 2 ≤ C)
      ∧ (∫ y in Submission.BoseGases.acube L, ∑ k : Fin 3,
          (fderiv ℝ (Submission.BoseGases.chiB L d u) y (Submission.BoseGases.kcStdBasis k)) ^ 2 ≤ C) := by
  obtain ⟨S, hS0, hS1, hS2⟩ := chiB_sup_bounds hL hd u
  have hfin : (volume : Measure E3) (Submission.BoseGases.acube L) < ⊤ := by
    rw [Submission.BoseGases.acube_volume L hL.le]
    exact ENNReal.ofReal_lt_top
  have hvol : ((volume : Measure E3) (Submission.BoseGases.acube L)).toReal = L ^ 3 := by
    rw [Submission.BoseGases.acube_volume L hL.le, ENNReal.toReal_ofReal (by positivity)]
  refine ⟨max (L ^ 3 * S ^ 2) (L ^ 3 * S), le_max_of_le_left (by positivity), ?_, ?_⟩
  · have hmono : (∫ y in Submission.BoseGases.acube L, (Submission.BoseGases.chiB L d u y) ^ 2)
        ≤ ∫ y in Submission.BoseGases.acube L, S ^ 2 :=
      MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => sq_nonneg _))
        (MeasureTheory.integrableOn_const (ne_of_lt hfin))
        (Filter.Eventually.of_forall (fun y => by
          have h := abs_le.mp (hS1 y)
          nlinarith [h.1, h.2, hS0, sq_nonneg (Submission.BoseGases.chiB L d u y)]))
    refine le_trans hmono ?_
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real, hvol]
    simp only [smul_eq_mul]
    exact le_max_left _ _
  · have hmono : (∫ y in Submission.BoseGases.acube L, ∑ k : Fin 3,
        (fderiv ℝ (Submission.BoseGases.chiB L d u) y (Submission.BoseGases.kcStdBasis k)) ^ 2)
        ≤ ∫ y in Submission.BoseGases.acube L, S :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun y => Finset.sum_nonneg (fun k _ => sq_nonneg _)))
        (MeasureTheory.integrableOn_const (ne_of_lt hfin)) (Filter.Eventually.of_forall hS2)
    refine le_trans hmono ?_
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real, hvol]
    simp only [smul_eq_mul]
    exact le_max_right _ _

/-! ## 7b. Copied collar and window estimates (proved in the sibling modules) -/




/-- The kinetic direction `kcDir N i k` is a unit vector: it is the `i`-th slot of the zero
configuration with the `k`-th standard basis vector inserted, and the norm on `Fin N → ℝ³` is
the sup-norm. -/
lemma norm_kcDir (N : ℕ) (i : Fin N) (k : Fin 3) :
    ‖Submission.BoseGases.kcDir N i k‖ = 1 := by
  rw [Submission.BoseGases.kcDir,
    show Function.update (0 : Submission.BoseGases.X N) i (Submission.BoseGases.kcStdBasis k)
      = Pi.single i (Submission.BoseGases.kcStdBasis k) from rfl,
    Pi.norm_single]
  simp [Submission.BoseGases.kcStdBasis]

/-- For negative side length the centred box `abox (n+1) L` is empty: every coordinate of every
particle would have to lie in `Icc (-L/2) (L/2)`, an interval of negative length. -/
lemma abox_eq_empty_of_neg (n : ℕ) {L : ℝ} (hL : L < 0) :
    Submission.BoseGases.abox (n + 1) L = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have hmem : x 0 0 ∈ Set.Icc (-L / 2) (L / 2) := hx 0 0
  linarith [hmem.1, hmem.2]

theorem exists_bound_fderiv_psi {n : ℕ} {L : ℝ} {ψ : Submission.BoseGases.X (n + 1) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) : ∃ Cψ : ℝ, 0 ≤ Cψ ∧ ∀ x ∈ Submission.BoseGases.abox (n + 1) L, ∀ (i : Fin (n + 1)) (k : Fin 3), |fderiv ℝ ψ x (Submission.BoseGases.kcDir (n + 1) i k)| ≤ Cψ := by
  by_cases hL : 0 ≤ L
  · -- the box is compact, the operator norm of the derivative is continuous, hence bounded on it
    have hK : IsCompact (abox (n + 1) L) :=
      (Metric.isCompact_iff_isClosed_bounded).mpr
        ⟨abox_isClosed (n + 1) L, abox_isBounded (n + 1) L hL⟩
    have hcont : Continuous (fun x : Submission.BoseGases.X (n + 1) => fderiv ℝ ψ x) :=
      hψ.continuous_fderiv (by simp)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun x hx i k => ?_⟩
    have h1 : ‖fderiv ℝ ψ x (Submission.BoseGases.kcDir (n + 1) i k)‖ ≤ C :=
      calc ‖fderiv ℝ ψ x (Submission.BoseGases.kcDir (n + 1) i k)‖
          ≤ ‖fderiv ℝ ψ x‖ * ‖Submission.BoseGases.kcDir (n + 1) i k‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ ψ x‖ := by rw [norm_kcDir, mul_one]
        _ ≤ C := hC x hx
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (le_max_left _ _)
  · -- the box is empty
    have hlt : L < 0 := lt_of_not_ge hL
    refine ⟨0, le_refl 0, fun x hx i k => ?_⟩
    rw [abox_eq_empty_of_neg n hlt] at hx
    exact absurd hx (Set.notMem_empty x)







/-! ## 1. Measurability of the collar -/

/-- The sublevel set `{boxMargin L d u ≤ δ}` of the box margin is the union of the six coordinate
slabs `{|x i| ≥ L/2 - δ}` and `{|(x - L d • u) i| ≥ L d/2 - δ}`; in particular it is
measurable. -/
lemma measurableSet_boxMargin_le (L d : ℝ) (u : E3) (δ : ℝ) :
    MeasurableSet {y : E3 | boxMargin L d u y ≤ δ} := by
  have hset : {y : E3 | boxMargin L d u y ≤ δ}
      = (⋃ i : Fin 3, {y : E3 | L / 2 - |y i| ≤ δ})
        ∪ (⋃ i : Fin 3, {y : E3 | L * d / 2 - |(y - (L * d) • u) i| ≤ δ}) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion]
    rw [boxMargin, min_le_iff, Finset.inf'_le_iff Finset.univ_nonempty,
      Finset.inf'_le_iff Finset.univ_nonempty]
    simp
  rw [hset]
  exact MeasurableSet.union
    (MeasurableSet.iUnion fun i : Fin 3 =>
      measurableSet_le (by fun_prop) measurable_const)
    (MeasurableSet.iUnion fun i : Fin 3 =>
      measurableSet_le (by fun_prop) measurable_const)

/-- The sliding box is measurable. -/
lemma measurableSet_dlBox (L d : ℝ) (u : E3) :
    MeasurableSet (Submission.BoseGases.dlBox L d u) := by
  rw [Submission.BoseGases.dlBox]
  exact MeasurableSet.inter (Submission.BoseGases.acube_measurable L)
    (MeasurableSet.preimage (Submission.BoseGases.acube_measurable (L * d)) (by fun_prop))

/-- The collar indicator is measurable. -/
lemma measurable_collarInd (L d : ℝ) (u : E3) (δ : ℝ) : Measurable (collarInd L d u δ) := by
  unfold collarInd
  exact Measurable.indicator measurable_const
    (MeasurableSet.inter (measurableSet_dlBox L d u) (measurableSet_boxMargin_le L d u δ))

/-! ## 2. The collar set is covered by the two `2δ`-collars of the two cubes -/

/-- **Geometric cover of the collar.**  A point `y` of the sliding box `dlBox L d u` whose margin
is `≤ δ` has some coordinate margin `≤ δ` for one of the two cubes defining the box; hence it lies
strictly inside the `2δ`-collar of that cube. -/
lemma collar_subset_twoCollar {L d δ : ℝ} (hδ : 0 < δ) (u : E3) :
    Submission.BoseGases.dlBox L d u ∩ {y : E3 | boxMargin L d u y ≤ δ}
      ⊆ (⋃ i : Fin 3, {x : E3 | (∀ m : Fin 3, |x m| ≤ L / 2) ∧ L / 2 - |x i| < 2 * δ})
        ∪ (⋃ i : Fin 3, {x : E3 | (∀ m : Fin 3, |(x - (L * d) • u) m| ≤ L * d / 2)
            ∧ L * d / 2 - |(x - (L * d) • u) i| < 2 * δ}) := by
  rintro y ⟨hybox, hm⟩
  simp only [Set.mem_ofPred_eq] at hm
  rw [Submission.BoseGases.mem_dlBox_iff] at hybox
  obtain ⟨h1, h2⟩ := hybox
  rw [Submission.BoseGases.mem_acube_iff] at h1 h2
  rw [boxMargin, min_le_iff] at hm
  rcases hm with hA | hB
  · rcases (Finset.inf'_le_iff Finset.univ_nonempty).mp hA with ⟨i, -, hi⟩
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact Or.inl ⟨i, (fun m => abs_le.mpr ⟨by linarith [(h1 m).1], by linarith [(h1 m).2]⟩),
      by linarith⟩
  · rcases (Finset.inf'_le_iff Finset.univ_nonempty).mp hB with ⟨i, -, hi⟩
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact Or.inr ⟨i, (fun m => abs_le.mpr ⟨by linarith [(h2 m).1], by linarith [(h2 m).2]⟩),
      by linarith⟩

/-- **Linear volume bound for the collar of the sliding box.**  The volume of the part of the
sliding box `B(u)` on which the margin is `≤ δ` is at most `12 L² (1 + d²) δ`. -/
lemma volume_dlBox_inter_boxMargin_le {L d δ : ℝ} (hL : 0 < L) (hd : 0 < d)
    (u : E3) (hδ : 0 < δ) :
    (volume : Measure E3) (Submission.BoseGases.dlBox L d u
        ∩ {y : E3 | boxMargin L d u y ≤ δ})
      ≤ ENNReal.ofReal (12 * L ^ 2 * (1 + d ^ 2) * δ) := by
  have hsub := collar_subset_twoCollar (L := L) (d := d) (δ := δ) hδ u
  have hV1 : (volume : Measure E3)
        (⋃ i : Fin 3, {x : E3 | (∀ m : Fin 3, |x m| ≤ L / 2) ∧ L / 2 - |x i| < 2 * δ})
      ≤ ENNReal.ofReal (24 * (L / 2) ^ 2 * (2 * δ)) := by
    simpa using volume_iUnion_collar_le (c := L / 2) (δ := 2 * δ)
      (by positivity) (by positivity) (0 : E3)
  have hV2 : (volume : Measure E3)
        (⋃ i : Fin 3, {x : E3 | (∀ m : Fin 3, |(x - (L * d) • u) m| ≤ L * d / 2)
            ∧ L * d / 2 - |(x - (L * d) • u) i| < 2 * δ})
      ≤ ENNReal.ofReal (24 * (L * d / 2) ^ 2 * (2 * δ)) :=
    volume_iUnion_collar_le (c := L * d / 2) (δ := 2 * δ)
      (by positivity) (by positivity) ((L * d) • u)
  calc (volume : Measure E3) (Submission.BoseGases.dlBox L d u
        ∩ {y : E3 | boxMargin L d u y ≤ δ})
      ≤ (volume : Measure E3)
          ((⋃ i : Fin 3, {x : E3 | (∀ m : Fin 3, |x m| ≤ L / 2) ∧ L / 2 - |x i| < 2 * δ})
          ∪ (⋃ i : Fin 3, {x : E3 | (∀ m : Fin 3, |(x - (L * d) • u) m| ≤ L * d / 2)
              ∧ L * d / 2 - |(x - (L * d) • u) i| < 2 * δ})) := measure_mono hsub
    _ ≤ (volume : Measure E3)
          (⋃ i : Fin 3, {x : E3 | (∀ m : Fin 3, |x m| ≤ L / 2) ∧ L / 2 - |x i| < 2 * δ})
        + (volume : Measure E3)
          (⋃ i : Fin 3, {x : E3 | (∀ m : Fin 3, |(x - (L * d) • u) m| ≤ L * d / 2)
              ∧ L * d / 2 - |(x - (L * d) • u) i| < 2 * δ}) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (24 * (L / 2) ^ 2 * (2 * δ))
        + ENNReal.ofReal (24 * (L * d / 2) ^ 2 * (2 * δ)) := add_le_add hV1 hV2
    _ = ENNReal.ofReal (12 * L ^ 2 * (1 + d ^ 2) * δ) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-! ## 3. The one-particle collar bound -/

/-- **One-particle collar bound.**  The integral of the collar indicator over the one-particle
cube `acube L` is at most `12 L² (1 + d²) δ`. -/
lemma integral_collarInd_acube_le {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3)
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ x in Submission.BoseGases.acube L, collarInd L d u δ x)
      ≤ 12 * L ^ 2 * (1 + d ^ 2) * δ := by
  have hmeas : MeasurableSet (Submission.BoseGases.dlBox L d u
      ∩ {y : E3 | boxMargin L d u y ≤ δ}) :=
    MeasurableSet.inter (isClosed_dlBox' hL hd u).measurableSet
      (measurableSet_boxMargin_le L d u δ)
  have hkey : (∫ x in Submission.BoseGases.acube L, collarInd L d u δ x)
      = ((volume : Measure E3).restrict (Submission.BoseGases.acube L)).real
          (Submission.BoseGases.dlBox L d u ∩ {y : E3 | boxMargin L d u y ≤ δ}) := by
    have hstep : (∫ x in Submission.BoseGases.acube L, collarInd L d u δ x)
        = ∫ x, (Submission.BoseGases.dlBox L d u
              ∩ {y : E3 | boxMargin L d u y ≤ δ}).indicator (fun _ : E3 => (1 : ℝ)) x
            ∂((volume : Measure E3).restrict (Submission.BoseGases.acube L)) := rfl
    rw [hstep, MeasureTheory.integral_indicator_const (1 : ℝ) hmeas, smul_eq_mul, mul_one]
  rw [hkey]
  have hsub_ac : (Submission.BoseGases.dlBox L d u ∩ {y : E3 | boxMargin L d u y ≤ δ})
      ⊆ Submission.BoseGases.acube L := fun x hx =>
    ((Submission.BoseGases.mem_dlBox_iff L d u x).mp hx.1).1
  have hrw : ((volume : Measure E3).restrict (Submission.BoseGases.acube L)).real
        (Submission.BoseGases.dlBox L d u ∩ {y : E3 | boxMargin L d u y ≤ δ})
      = (volume : Measure E3).real
          (Submission.BoseGases.dlBox L d u ∩ {y : E3 | boxMargin L d u y ≤ δ}) := by
    rw [Measure.real_def, Measure.real_def,
      Measure.restrict_apply' (Submission.BoseGases.acube_measurable L),
      Set.inter_eq_left.mpr hsub_ac]
  calc ((volume : Measure E3).restrict (Submission.BoseGases.acube L)).real
        (Submission.BoseGases.dlBox L d u ∩ {y : E3 | boxMargin L d u y ≤ δ})
      = (volume : Measure E3).real
          (Submission.BoseGases.dlBox L d u ∩ {y : E3 | boxMargin L d u y ≤ δ}) := hrw
    _ ≤ (ENNReal.ofReal (12 * L ^ 2 * (1 + d ^ 2) * δ)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (volume_dlBox_inter_boxMargin_le hL hd u hδ)
    _ = 12 * L ^ 2 * (1 + d ^ 2) * δ := ENNReal.toReal_ofReal (by positivity)

/-! ## 4. The many-particle bound -/

theorem integral_collarInd_abox {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : EuclideanSpace ℝ (Fin 3)) (n : ℕ) (j : Fin n) : ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → (∫ r in Submission.BoseGases.abox n L, Work.BoseFixB1B.collarInd L d u δ (r j)) ≤ C * δ := by
  rcases n with _ | m
  · exact Fin.elim0 j
  · refine ⟨(L ^ 3) ^ m * (12 * L ^ 2 * (1 + d ^ 2)), by positivity, fun δ hδ => ?_⟩
    have hmeas : Measurable (collarInd L d u δ) := measurable_collarInd L d u δ
    have hmeas_comp : Measurable
        (fun x : Submission.BoseGases.X (m + 1) => collarInd L d u δ (x j)) :=
      hmeas.comp (measurable_pi_apply j)
    have hmeas_c : Measurable
        (fun x : Submission.BoseGases.X (m + 1) => (1 : ℝ) * collarInd L d u δ (x j)) :=
      hmeas_comp.const_mul 1
    have hbnd : ∀ x : E3, ‖collarInd L d u δ x‖ ≤ 1 := fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (collarInd_nonneg L d u δ x)]
      exact collarInd_le_one L d u δ x
    have hfinB : (volume : Measure (Submission.BoseGases.X (m + 1)))
        (Submission.BoseGases.abox (m + 1) L) ≠ ∞ := by
      rw [Submission.BoseGases.abox_volume (m + 1) L hL.le]
      exact ENNReal.ofReal_ne_top
    have hfinA : (volume : Measure E3) (Submission.BoseGases.acube L) ≠ ∞ := by
      rw [Submission.BoseGases.acube_volume L hL.le]
      exact ENNReal.ofReal_ne_top
    have hInt : MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X (m + 1) =>
          (fun _ : Submission.BoseGases.X (m + 1) => (1 : ℝ)) x * collarInd L d u δ (x j))
        (Submission.BoseGases.abox (m + 1) L) := by
      refine Measure.integrableOn_of_bounded (M := 1) hfinB ?_ ?_
      · exact hmeas_c.aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun x => ?_
        have h0 : 0 ≤ collarInd L d u δ (x j) := collarInd_nonneg L d u δ (x j)
        have h1 : collarInd L d u δ (x j) ≤ 1 := collarInd_le_one L d u δ (x j)
        show ‖(1 : ℝ) * collarInd L d u δ (x j)‖ ≤ 1
        rw [Real.norm_eq_abs, abs_mul, abs_one, one_mul, abs_of_nonneg h0]
        exact h1
    have hIntg : MeasureTheory.IntegrableOn
        (fun _ : Submission.BoseGases.X (m + 1) => (1 : ℝ))
        (Submission.BoseGases.abox (m + 1) L) := by
      refine Measure.integrableOn_of_bounded (M := 1) hfinB aestronglyMeasurable_const ?_
      exact Filter.Eventually.of_forall fun x => by simp
    have hInth : MeasureTheory.IntegrableOn (collarInd L d u δ)
        (Submission.BoseGases.acube L) :=
      Measure.integrableOn_of_bounded (M := 1) hfinA hmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall hbnd)
    have hindep : ∀ (x : Submission.BoseGases.X (m + 1)) (a : E3),
        (fun _ : Submission.BoseGases.X (m + 1) => (1 : ℝ)) (Function.update x j a)
          = (fun _ : Submission.BoseGases.X (m + 1) => (1 : ℝ)) x := fun _ _ => rfl
    have hpeel := integral_abox_indep_mul_coord (n := m + 1) (ℓ := L) hL j
      (g := fun _ : Submission.BoseGases.X (m + 1) => (1 : ℝ))
      (h := collarInd L d u δ) hindep hInt hIntg hInth
    have hvol1 : (∫ x in Submission.BoseGases.abox (m + 1) L, (1 : ℝ))
        = (volume : Measure (Submission.BoseGases.X (m + 1))).real
            (Submission.BoseGases.abox (m + 1) L) := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    have haboxreal : (volume : Measure (Submission.BoseGases.X (m + 1))).real
          (Submission.BoseGases.abox (m + 1) L) = (L ^ 3) ^ (m + 1) := by
      rw [Measure.real_def, Submission.BoseGases.abox_volume (m + 1) L hL.le,
        ENNReal.toReal_ofReal (by positivity)]
    have hmain : (∫ r in Submission.BoseGases.abox (m + 1) L, collarInd L d u δ (r j))
        = ((∫ x in Submission.BoseGases.abox (m + 1) L, (1 : ℝ)) / L ^ 3)
            * (∫ x in Submission.BoseGases.acube L, collarInd L d u δ x) := by
      simpa only [one_mul] using hpeel
    calc (∫ r in Submission.BoseGases.abox (m + 1) L, collarInd L d u δ (r j))
        = (L ^ 3) ^ m * (∫ x in Submission.BoseGases.acube L, collarInd L d u δ x) := by
          rw [hmain, hvol1, haboxreal, pow_succ,
            mul_div_cancel_right₀ ((L ^ 3) ^ m) (pow_ne_zero 3 (ne_of_gt hL))]
      _ ≤ (L ^ 3) ^ m * (12 * L ^ 2 * (1 + d ^ 2) * δ) :=
          mul_le_mul_of_nonneg_left (integral_collarInd_acube_le hL hd u hδ) (by positivity)
      _ = ((L ^ 3) ^ m * (12 * L ^ 2 * (1 + d ^ 2))) * δ := by ring







/-- **Global bound on the sliding-box window.**  The squared window is dominated by the constant
`((√chiNormSq)⁻¹)^4`. -/
lemma chiB_sq_le_supConst {L d : ℝ} (u x : E3) :
    (Submission.BoseGases.chiB L d u x) ^ 2 ≤ ((Real.sqrt chiNormSq)⁻¹) ^ 4 := by
  have hs : 0 ≤ (Real.sqrt chiNormSq)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have h1 : (chiScale L x) ^ 2 ≤ ((Real.sqrt chiNormSq)⁻¹) ^ 2 := by
    calc (chiScale L x) ^ 2 = |chiScale L x| ^ 2 := (sq_abs _).symm
      _ ≤ ((Real.sqrt chiNormSq)⁻¹) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_chiScale_le L x) 2
  have h2 : (chiScale (L * d) (x - (L * d) • u)) ^ 2 ≤ ((Real.sqrt chiNormSq)⁻¹) ^ 2 := by
    calc (chiScale (L * d) (x - (L * d) • u)) ^ 2 = |chiScale (L * d) (x - (L * d) • u)| ^ 2 :=
          (sq_abs _).symm
      _ ≤ ((Real.sqrt chiNormSq)⁻¹) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_chiScale_le (L * d) (x - (L * d) • u)) 2
  have hprod : (Submission.BoseGases.chiB L d u x) ^ 2
      = (chiScale L x) ^ 2 * (chiScale (L * d) (x - (L * d) • u)) ^ 2 := by
    rw [Submission.BoseGases.chiB, mul_pow]
  rw [hprod]
  calc (chiScale L x) ^ 2 * (chiScale (L * d) (x - (L * d) • u)) ^ 2
      ≤ ((Real.sqrt chiNormSq)⁻¹) ^ 2 * ((Real.sqrt chiNormSq)⁻¹) ^ 2 :=
        mul_le_mul h1 h2 (sq_nonneg _) (pow_nonneg hs 2)
    _ = ((Real.sqrt chiNormSq)⁻¹) ^ 4 := by ring

/-- **The window-weighted collar integral is linear in `δ`.** -/
theorem integral_chiB_sq_collarInd_le {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ →
      (∫ y in Submission.BoseGases.acube L,
        (Submission.BoseGases.chiB L d u y) ^ 2 * Work.BoseFixB1B.collarInd L d u δ y) ≤ C * δ := by
  obtain ⟨Cc, hCc0, hCc⟩ := collarBox_le (L := L) (d := d) hL hd u
  set M : ℝ := ((Real.sqrt chiNormSq)⁻¹) ^ 4 with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  refine ⟨M * Cc * 2, mul_nonneg (mul_nonneg hM0 hCc0) (by norm_num), fun δ hδ => ?_⟩
  have h2δ : (0 : ℝ) < 2 * δ := by linarith
  set T : Set E3 := collarBoxSet L d (2 * δ) u with hTdef
  have hTmeas : MeasurableSet T := by
    rw [hTdef]; exact measurableSet_collarBoxSet L d (2 * δ) u
  have hTfin : (volume : Measure E3) T ≠ ⊤ := by
    intro htop
    have hle := hCc (2 * δ) h2δ
    rw [htop] at hle
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hle)
  -- the set where `collarInd` does not vanish lies in `T`
  have hsupp : ∀ y : E3, collarInd L d u δ y ≠ 0 → y ∈ T := by
    intro y hy
    have hmem : y ∈ Submission.BoseGases.dlBox L d u ∩ {z : E3 | boxMargin L d u z ≤ δ} := by
      by_contra h
      exact hy (Set.indicator_of_notMem h (fun _ : E3 => (1 : ℝ)))
    rw [hTdef, collarBoxSet]
    exact ⟨hmem.1, lt_of_le_of_lt hmem.2 (by linarith : δ < 2 * δ)⟩
  -- pointwise domination of the integrand by the majorant
  have hbd : ∀ y : E3, (Submission.BoseGases.acube L).indicator
        (fun z : E3 => (Submission.BoseGases.chiB L d u z) ^ 2 * collarInd L d u δ z) y
      ≤ M * T.indicator (1 : E3 → ℝ) y := by
    intro y
    by_cases hy : y ∈ Submission.BoseGases.acube L
    · rw [Set.indicator_of_mem hy]
      rcases collarInd_eq_one_or_zero L d u δ y with h1 | h0
      · have hyT : y ∈ T := hsupp y (by rw [h1]; norm_num)
        rw [h1, mul_one, Set.indicator_of_mem hyT]
        have hb : (Submission.BoseGases.chiB L d u y) ^ 2 ≤ M := by
          rw [hMdef]; exact chiB_sq_le_supConst (L := L) (d := d) u y
        simpa using hb
      · rw [h0, mul_zero]
        exact mul_nonneg hM0 (Set.indicator_nonneg (fun _ _ => zero_le_one) y)
    · rw [Set.indicator_of_notMem hy]
      exact mul_nonneg hM0 (Set.indicator_nonneg (fun _ _ => zero_le_one) y)
  -- the majorant is integrable
  have hgi : Integrable (fun y : E3 => M * T.indicator (1 : E3 → ℝ) y) volume := by
    have hind : Integrable (T.indicator (1 : E3 → ℝ)) (volume : Measure E3) :=
      (integrable_indicator_iff hTmeas).mpr (integrableOn_const (C := (1 : ℝ)) hTfin (by simp))
    exact hind.const_mul M
  -- the monotonicity step
  have hmono : (∫ y : E3, (Submission.BoseGases.acube L).indicator
        (fun z : E3 => (Submission.BoseGases.chiB L d u z) ^ 2 * collarInd L d u δ z) y)
      ≤ ∫ y : E3, M * T.indicator (1 : E3 → ℝ) y := by
    refine integral_mono_of_nonneg (μ := volume) (Filter.Eventually.of_forall (fun y => ?_)) hgi
      (Filter.Eventually.of_forall hbd)
    by_cases hy : y ∈ Submission.BoseGases.acube L
    · rw [Set.indicator_of_mem hy]
      exact mul_nonneg (sq_nonneg _) (collarInd_nonneg L d u δ y)
    · rw [Set.indicator_of_notMem hy]; exact le_refl 0
  have hLHS : (∫ y in Submission.BoseGases.acube L,
        (Submission.BoseGases.chiB L d u y) ^ 2 * collarInd L d u δ y)
      = ∫ y : E3, (Submission.BoseGases.acube L).indicator
          (fun z : E3 => (Submission.BoseGases.chiB L d u z) ^ 2 * collarInd L d u δ z) y :=
    (integral_indicator (Submission.BoseGases.acube_measurable L)).symm
  have hRHS : (∫ y : E3, M * T.indicator (1 : E3 → ℝ) y) = M * (volume T).toReal := by
    rw [MeasureTheory.integral_const_mul, integral_indicator_one hTmeas,
      MeasureTheory.Measure.real_def]
  calc (∫ y in Submission.BoseGases.acube L,
        (Submission.BoseGases.chiB L d u y) ^ 2 * collarInd L d u δ y)
      = ∫ y : E3, (Submission.BoseGases.acube L).indicator
          (fun z : E3 => (Submission.BoseGases.chiB L d u z) ^ 2 * collarInd L d u δ z) y := hLHS
    _ ≤ ∫ y : E3, M * T.indicator (1 : E3 → ℝ) y := hmono
    _ = M * (volume T).toReal := hRHS
    _ ≤ M * (Cc * (2 * δ)) :=
        mul_le_mul_of_nonneg_left
          (ENNReal.toReal_le_of_le_ofReal (by positivity) (hCc (2 * δ) h2δ)) hM0
    _ = M * Cc * 2 * δ := by ring


/-! ## 7. The collar count and the bound on the box mean -/

/-- The number of coordinates of the configuration `r` lying in the `δ`-collar. -/
def collSum (L d : ℝ) (u : E3) (δ : ℝ) {n : ℕ} (r : Submission.BoseGases.X n) : ℝ :=
  ∑ j : Fin n, collarInd L d u δ (r j)

lemma collSum_nonneg {L d : ℝ} {u : E3} {δ : ℝ} {n : ℕ} (r : Submission.BoseGases.X n) :
    0 ≤ collSum L d u δ r :=
  Finset.sum_nonneg (fun j _ => collarInd_nonneg L d u δ (r j))

/-- The integral of the collar count over the `n`-particle box is `O(δ)`. -/
lemma integral_collSum_le {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ →
      (∫ r in Submission.BoseGases.abox n L, collSum L d u δ r) ≤ C * δ := by
  classical
  rcases n with _ | m
  · refine ⟨0, le_refl 0, fun δ hδ => ?_⟩
    have hfun : (fun r : Submission.BoseGases.X 0 => collSum L d u δ r)
        = fun _ : Submission.BoseGases.X 0 => (0 : ℝ) := by
      funext r
      simp [collSum]
    rw [hfun]
    simp
  · choose Cj hCj0 hCj using fun j : Fin (m + 1) =>
      integral_collarInd_abox (L := L) (d := d) hL hd u (m + 1) j
    refine ⟨∑ j : Fin (m + 1), Cj j, Finset.sum_nonneg (fun j _ => hCj0 j), fun δ hδ => ?_⟩
    have hfinB : (volume : Measure (Submission.BoseGases.X (m + 1)))
        (Submission.BoseGases.abox (m + 1) L) ≠ ∞ := by
      rw [Submission.BoseGases.abox_volume (m + 1) L hL.le]
      exact ENNReal.ofReal_ne_top
    have hInt : ∀ j : Fin (m + 1), Integrable
        (fun r : Submission.BoseGases.X (m + 1) => collarInd L d u δ (r j))
        ((volume : Measure (Submission.BoseGases.X (m + 1))).restrict
          (Submission.BoseGases.abox (m + 1) L)) := by
      intro j
      refine Measure.integrableOn_of_bounded (M := 1) hfinB ?_ ?_
      · exact ((measurable_collarInd L d u δ).comp (measurable_pi_apply j)).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun r => by
          rw [Real.norm_eq_abs, abs_of_nonneg (collarInd_nonneg L d u δ (r j))]
          exact collarInd_le_one L d u δ (r j)
    have hsum : (∫ r in Submission.BoseGases.abox (m + 1) L, collSum L d u δ r)
        = ∑ j : Fin (m + 1), ∫ r in Submission.BoseGases.abox (m + 1) L,
            collarInd L d u δ (r j) := by
      have h1 : (fun r : Submission.BoseGases.X (m + 1) => collSum L d u δ r)
          = fun r => ∑ j : Fin (m + 1), collarInd L d u δ (r j) := rfl
      rw [h1]
      exact MeasureTheory.integral_finset_sum Finset.univ (fun j _ => hInt j)
    rw [hsum]
    calc ∑ j : Fin (m + 1), ∫ r in Submission.BoseGases.abox (m + 1) L,
            collarInd L d u δ (r j)
        ≤ ∑ j : Fin (m + 1), Cj j * δ := Finset.sum_le_sum (fun j _ => hCj j δ hδ)
      _ = (∑ j : Fin (m + 1), Cj j) * δ := by rw [Finset.sum_mul]

/-! ## 8. The pointwise bound on the squared fibre derivative -/

/-- The `r`-independent part of the pointwise bound. -/
def A1Bound (L d : ℝ) (u : E3) (g : E3 → ℝ) (K Cb Cψ C4 δ : ℝ) (n : ℕ) (y : E3) : ℝ :=
  12 * Cb ^ 2 * ((Submission.BoseGases.chiB L d u y) ^ 2
      * (∑ k : Fin 3, (fderiv ℝ g y (Submission.BoseGases.kcStdBasis k)) ^ 2))
    + 12 * ((n : ℝ) + 1) * Cψ ^ 2 * ((Submission.BoseGases.chiB L d u y) ^ 2
        * collarInd L d u δ y)
    + 6 * Cb ^ 2 * ((∑ k : Fin 3, (fderiv ℝ (Submission.BoseGases.chiB L d u) y
        (Submission.BoseGases.kcStdBasis k)) ^ 2) * collarInd L d u δ y)
    + 6 * Cb ^ 2 * ((C4 * δ) ^ 2 * (∑ k : Fin 3,
        (fderiv ℝ (Submission.BoseGases.chiB L d u) y (Submission.BoseGases.kcStdBasis k)) ^ 2))

/-- The part of the pointwise bound carrying the collar count of `r`. -/
def A2Bound (L d : ℝ) (u : E3) (Cb Cψ : ℝ) (n : ℕ) (y : E3) : ℝ :=
  12 * ((n : ℝ) + 1) * Cψ ^ 2 * ((Submission.BoseGases.chiB L d u y) ^ 2)
    + 24 * (n : ℝ) * Cb ^ 2 * (∑ k : Fin 3,
        (fderiv ℝ (Submission.BoseGases.chiB L d u) y (Submission.BoseGases.kcStdBasis k)) ^ 2)

/-! ## 9. Null sets of the sliding-box geometry and the majorant integrals -/

/-- A coordinate hyperplane of `E3` is Lebesgue-null. -/
lemma volume_coord_hyperplane_eq_zero' (i : Fin 3) (c : ℝ) :
    (volume : Measure E3) {y : E3 | y i = c} = 0 := by
  have hqmp : Measure.QuasiMeasurePreserving (fun y : E3 => y i)
      (volume : Measure E3) (volume : Measure ℝ) :=
    (Measure.quasiMeasurePreserving_eval (fun _ : Fin 3 => (volume : Measure ℝ)) i).comp
      (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving
  have h := hqmp.preimage_null (Real.volume_singleton (a := c))
  have heq : (fun y : E3 => y i) ⁻¹' ({c} : Set ℝ) = {y : E3 | y i = c} := by
    ext y; simp
  rwa [heq] at h

/-- The zero level set of the box margin is Lebesgue-null. -/
lemma volume_boxMargin_eq_zero' {L d : ℝ} (u : E3) :
    (volume : Measure E3) {y : E3 | boxMargin L d u y = 0} = 0 := by
  classical
  have hSnull : ∀ i : Fin 3,
      (volume : Measure E3) ({y : E3 | y i = L / 2} ∪ {y : E3 | y i = -(L / 2)}
        ∪ {y : E3 | y i = (L * d) * u i + L * d / 2}
        ∪ {y : E3 | y i = (L * d) * u i - L * d / 2}) = 0 := by
    intro i
    refine measure_union_null (measure_union_null (measure_union_null ?_ ?_) ?_) ?_
    · exact volume_coord_hyperplane_eq_zero' i (L / 2)
    · exact volume_coord_hyperplane_eq_zero' i (-(L / 2))
    · exact volume_coord_hyperplane_eq_zero' i ((L * d) * u i + L * d / 2)
    · exact volume_coord_hyperplane_eq_zero' i ((L * d) * u i - L * d / 2)
  have hcover : {y : E3 | boxMargin L d u y = 0} ⊆
      ⋃ i : Fin 3, ({y : E3 | y i = L / 2} ∪ {y : E3 | y i = -(L / 2)}
        ∪ {y : E3 | y i = (L * d) * u i + L * d / 2}
        ∪ {y : E3 | y i = (L * d) * u i - L * d / 2}) := by
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    unfold boxMargin at hy
    rw [min_eq_iff] at hy
    rcases hy with ⟨hA, -⟩ | ⟨hB, -⟩
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (H := Finset.univ_nonempty)
        (f := fun i : Fin 3 => L / 2 - |y i|)
      have hzero : |y i| = L / 2 := by linarith
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      simp only [Set.mem_union, Set.mem_setOf_eq]
      rcases abs_cases (y i) with hh | hh
      · have : y i = L / 2 := by linarith
        tauto
      · have : y i = -(L / 2) := by linarith
        tauto
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (H := Finset.univ_nonempty)
          (f := fun i : Fin 3 => L * d / 2 - |(y - (L * d) • u) i|)
      have hzero : |(y - (L * d) • u) i| = L * d / 2 := by linarith
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      simp only [Set.mem_union, Set.mem_setOf_eq]
      rcases abs_cases ((y - (L * d) • u) i) with ⟨habs, -⟩ | ⟨habs, -⟩
      · have hsub : y i - (L * d) * u i = L * d / 2 := by
          have h1 := hzero
          have h2 := habs
          simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h1 h2
          linarith
        have : y i = (L * d) * u i + L * d / 2 := by linarith
        tauto
      · have hsub : y i - (L * d) * u i = -(L * d / 2) := by
          have h1 := hzero
          have h2 := habs
          simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h1 h2
          linarith
        have : y i = (L * d) * u i - L * d / 2 := by linarith
        tauto
  refine measure_mono_null hcover ?_
  exact measure_iUnion_null_iff.mpr hSnull

/-- The configurations whose slot-`i` coordinate lies on the boundary of the box are null. -/
lemma ae_boxMargin_ne_zero' {L d : ℝ} (u : E3) {n : ℕ} :
    ∀ᵐ r ∂(volume : Measure (Submission.BoseGases.X n)),
      ∀ j : Fin n, boxMargin L d u (r j) ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  have hcoord : ∀ j : Fin n, (volume : Measure (Submission.BoseGases.X n))
      {r : Submission.BoseGases.X n | boxMargin L d u (r j) = 0} = 0 := by
    intro j
    have hqmp : Measure.QuasiMeasurePreserving (fun r : Submission.BoseGases.X n => r j)
        (volume : Measure (Submission.BoseGases.X n)) (volume : Measure E3) :=
      Measure.quasiMeasurePreserving_eval (fun _ : Fin n => (volume : Measure E3)) j
    exact hqmp.preimage_null (volume_boxMargin_eq_zero' (L := L) (d := d) u)
  have hunion : {r : Submission.BoseGases.X n | ¬ (∀ j : Fin n, boxMargin L d u (r j) ≠ 0)}
      = ⋃ j : Fin n, {r : Submission.BoseGases.X n | boxMargin L d u (r j) = 0} := by
    ext r; simp [not_forall]
  rw [hunion]
  exact measure_iUnion_null_iff.mpr hcoord
