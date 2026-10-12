import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1B.tendsto_cutProd_mass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.tendsto_cutProd_nCountB`

The **weighted mass convergence** along the smooth approximants of the sharp box state: for the
cutoff family `γ_δ` of the sliding box `B(u) = dlBox L d u` (`Work.BoseFixB1B.IsCutFamily`) and a
continuous fibre `ψ`,

    ∫_{abox k L} (∏ᵢγ_δ(xᵢ)·ψ(x))² · nCountB M L d u x
        ⟶  ∫_{abox k L} (1_{B(u)^k}·ψ(x))² · nCountB M L d u x     (δ → 0⁺),

where `nCountB M L d u x = Σᵢ χ_{B(u)}(xᵢ)²` is the smooth count of `Work.BoseFixB1.Defs`
(the per-configuration particle count of the smooth small box `chiSmallB`).

This is the *weighted* companion of `Work.BoseFixB1B.tendsto_cutProd_mass`: the weight
`nCountB M L d u` is a finite sum of squares of the continuous small-box cutoff, hence
continuous on the ambient space (for every `M`, `L`, `d`, `u` — no positivity hypothesis is
needed, since `chiSmall M` is continuous for every `M` by
`Work.SmallBoxSliding.chiSmall_continuous_all`), and therefore bounded on the compact box
`abox k L`.  The convergence is then exactly the unweighted one, multiplied pointwise by the
fixed bounded factor `nCountB M L d u x`: dominated convergence with the constant bound
`Cb²·Cg` where `Cb` bounds `ψ` and `Cg` bounds the count on the box.

The proof is a verbatim adaptation of `Work.BoseFixB1B.tendsto_cutProd_mass`, with the extra
factor carried through the pointwise-convergence, measurability and domination steps.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge Work.PerSector Work.SlotWord

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The count weight is continuous and nonnegative -/

/-- **The small-box cutoff is continuous at fixed `u`**, for every `M` (in particular for `M = 0`,
where the bump may degenerate).  This is the fixed-`u` slice of the joint continuity result; it is
proved directly from `chiSmallB = chiScale ℓ · chiSmall M ((ℓd)⁻¹ • x − u)`. -/
private lemma chiSmallB_continuous_fixed (M : ℕ) (L d : ℝ) (u : E3) :
    Continuous (fun x : E3 => Submission.BoseGases.chiSmallB M L d u x) := by
  unfold Submission.BoseGases.chiSmallB
  exact (Submission.BoseGases.chiScale_continuous L).mul
    ((Work.SmallBoxSliding.chiSmall_continuous_all M).comp
      ((continuous_id.const_smul ((L * d)⁻¹)).sub continuous_const))

/-- **The per-configuration count `nCountB` is continuous** on the ambient configuration space,
for every `M`, `L`, `d`, `u`: it is a finite sum of squares of continuous functions of the
coordinates. -/
private lemma nCountB_continuous (M : ℕ) (L d : ℝ) (u : E3) {k : ℕ} :
    Continuous (fun x : Submission.BoseGases.X k => Work.BoseFixB1.nCountB M L d u x) := by
  rw [show (fun x : Submission.BoseGases.X k => Work.BoseFixB1.nCountB M L d u x)
      = (fun x : Submission.BoseGases.X k => ∑ i : Fin k,
          (Submission.BoseGases.chiSmallB M L d u (x i)) ^ 2) from by
    funext x; rw [Work.BoseFixB1.nCountB]]
  exact continuous_finsetSum _ fun i _ =>
    ((chiSmallB_continuous_fixed M L d u).comp (continuous_apply i)).pow 2

/-- `nCountB ≥ 0`: it is a sum of squares. -/
private lemma nCountB_nonneg (M : ℕ) (L d : ℝ) (u : E3) {k : ℕ}
    (x : Submission.BoseGases.X k) : 0 ≤ Work.BoseFixB1.nCountB M L d u x := by
  rw [Work.BoseFixB1.nCountB]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-! ## 2. The weighted mass convergence -/

theorem tendsto_cutProd_nCountB {k : ℕ} {L d : ℝ} {u : EuclideanSpace ℝ (Fin 3)} {M : ℕ}
    {ψ : Submission.BoseGases.X k → ℝ} {K : ℝ} {γ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hL : 0 < L) (hd : 0 < d) (hcut : Work.BoseFixB1B.IsCutFamily L d u K γ)
    (hψ : Continuous ψ) :
    Filter.Tendsto
      (fun δ : ℝ => ∫ x in Submission.BoseGases.abox k L,
        (Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2 * Work.BoseFixB1.nCountB M L d u x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ x in Submission.BoseGases.abox k L,
        (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ x) ^ 2
          * Work.BoseFixB1.nCountB M L d u x)) := by
  classical
  obtain ⟨hK0, hcutδ⟩ := hcut
  -- a bound for the fibre `ψ` on the compact box
  obtain ⟨Cb, hCb⟩ := (abox_compact k hL).exists_bound_of_continuousOn hψ.continuousOn
  set Cb' : ℝ := max Cb 0 with hCb'def
  have hCb'0 : 0 ≤ Cb' := le_max_right _ _
  have hψb : ∀ x ∈ abox k L, |ψ x| ≤ Cb' := by
    intro x hx
    rw [← Real.norm_eq_abs]
    exact le_trans (hCb x hx) (le_max_left _ _)
  -- a bound for the count weight on the compact box
  have hgcont : Continuous (fun x : Submission.BoseGases.X k =>
      Work.BoseFixB1.nCountB M L d u x) := nCountB_continuous M L d u
  obtain ⟨Cg, hCg⟩ := (abox_compact k hL).exists_bound_of_continuousOn hgcont.continuousOn
  set Cg' : ℝ := max Cg 0 with hCg'def
  have hCg'0 : 0 ≤ Cg' := le_max_right _ _
  have hgb : ∀ x ∈ abox k L, |Work.BoseFixB1.nCountB M L d u x| ≤ Cg' := by
    intro x hx
    rw [← Real.norm_eq_abs]
    exact le_trans (hCg x hx) (le_max_left _ _)
  have haboxm : MeasurableSet (abox k L) := (abox_isClosed k L).measurableSet
  haveI hfin : IsFiniteMeasure
      ((volume : Measure (Submission.BoseGases.X k)).restrict (abox k L)) :=
    isFiniteMeasure_restrict.mpr (ne_of_lt (abox_compact k hL).measure_lt_top)
  have hγsupp : ∀ δ : ℝ, 0 < δ → ∀ y, γ δ y ≠ 0 → y ∈ dlBox L d u := fun δ hδ y hy =>
    (hcutδ δ hδ).2.1 (subset_tsupport _ (Function.mem_support.mpr hy))
  have hγone : ∀ δ : ℝ, 0 < δ → ∀ y, boxMargin L d u y ≥ δ → γ δ y = 1 :=
    fun δ hδ => (hcutδ δ hδ).2.2.2.1
  have hnull : (volume : Measure (Submission.BoseGases.X k))
      {x : Submission.BoseGases.X k | ¬ GoodCollar L d u x} = 0 :=
    volume_goodCollar_compl (k := k) (L := L) (d := d) u
  have hae : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X k)).restrict (abox k L)),
      GoodCollar L d u x := by
    rw [MeasureTheory.ae_iff]
    exact le_antisymm (le_trans (Measure.restrict_apply_le _ _) hnull.le) bot_le
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (Submission.BoseGases.X k)).restrict (abox k L))
    (l := nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (F := fun δ x => (cutProd (γ δ) ψ x) ^ 2 * Work.BoseFixB1.nCountB M L d u x)
    (f := fun x => (sharpBoxState (dlBox L d u) ψ x) ^ 2 * Work.BoseFixB1.nCountB M L d u x)
    (bound := fun _ => Cb' ^ 2 * Cg') ?_ ?_ ?_ ?_
  · -- measurability: the integrand is continuous
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hprod : Continuous (fun x : Submission.BoseGases.X k => ∏ i : Fin k, γ δ (x i)) :=
      continuous_finsetProd (Finset.univ : Finset (Fin k))
        (fun i _ => (hcutδ δ hδ).1.continuous.comp (continuous_apply i))
    have hF : Continuous (fun x : Submission.BoseGases.X k =>
        (cutProd (γ δ) ψ x) ^ 2 * Work.BoseFixB1.nCountB M L d u x) :=
      ((hprod.mul hψ).pow 2).mul hgcont
    exact hF.aestronglyMeasurable
  · -- domination by the constant `Cb'² · Cg'` on the box
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [ae_restrict_mem haboxm] with x hx
    have h01 : ∀ y, 0 ≤ γ δ y ∧ γ δ y ≤ 1 := (hcutδ δ hδ).2.2.1
    have hgn : 0 ≤ Work.BoseFixB1.nCountB M L d u x := nCountB_nonneg M L d u x
    have hcutb : |cutProd (γ δ) ψ x| ≤ Cb' := by
      rw [cutProd_apply, abs_mul,
        abs_of_nonneg (Finset.prod_nonneg (fun i _ => (h01 (x i)).1))]
      calc (∏ i : Fin k, γ δ (x i)) * |ψ x| ≤ 1 * Cb' :=
            mul_le_mul
              (Finset.prod_le_one₀ (fun i _ => (h01 (x i)).1) (fun i _ => (h01 (x i)).2))
              (hψb x hx) (abs_nonneg _) zero_le_one
        _ = Cb' := one_mul Cb'
    have hsq : (cutProd (γ δ) ψ x) ^ 2 ≤ Cb' ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (cutProd (γ δ) ψ x)) hcutb 2
      rwa [sq_abs] at h
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (sq_nonneg (cutProd (γ δ) ψ x)), abs_of_nonneg hgn]
    exact mul_le_mul hsq (abs_le.mp (hgb x hx)).2 hgn (sq_nonneg Cb')
  · exact integrable_const _
  · -- pointwise convergence off the null set
    filter_upwards [hae] with x hx
    exact (tendsto_cutProd_sq_pointwise hγsupp hγone hx).mul_const _

end Work.BoseFixB1B
