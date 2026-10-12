import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.dict13Aux6
import Submission.Work.BoseBoxFock.dict13Aux8
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.dict13Aux9` — from the bounded dictionary to the `L¹` dictionary

`lhsGen_eq_of_bounded` is the transfer step of `dict13_L1`: given the (proved) identity *for
bounded measurable symmetric pair kernels*, it holds for every a.e.-strongly-measurable, integrable
and pointwise symmetric pair kernel.  The proof replaces the kernel by its (symmetrised) measurable
hull — the two sides are invariant under a.e. changes — and then by the value truncations
`trunc N H`, whose `L¹` norms converge; both sides are `L¹`-Lipschitz (`lhsGen_abs_le`,
`rhsGen_abs_le`) and linear in the kernel (`lhsGen_linear`, `rhsGen_linear`).

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X
local notation "abx" => Submission.BoseGases.abox
local notation "acb" => Submission.BoseGases.acube

set_option autoImplicit false

/-- `‖trunc N H a b‖ ≤ ‖H a b‖`. -/
theorem trunc_enorm_le (N : ℕ) (H : E3 → E3 → ℝ) (a b : E3) : ‖trunc N H a b‖ ≤ ‖H a b‖ := by
  rw [trunc_apply]
  split_ifs with h
  · exact le_refl _
  · rw [norm_zero]; exact norm_nonneg _

/-- `boxL1 ℓ e` is bounded by the full-space `∫⁻ ‖uncurry e‖ₑ`. -/
theorem boxL1_le_lintegral_full {ℓ : ℝ} {e : E3 → E3 → ℝ}
    (he : AEStronglyMeasurable (Function.uncurry e)
      ((volume : Measure E3).prod (volume : Measure E3))) :
    boxL1 ℓ e ≤ ∫⁻ p, ‖Function.uncurry e p‖ₑ
      ∂((volume : Measure E3).prod (volume : Measure E3)) := by
  have h1 : boxL1 ℓ e = ∫⁻ p, ‖Function.uncurry e p‖ₑ
      ∂(((volume : Measure E3).restrict (acb ℓ)).prod
        ((volume : Measure E3).restrict (acb ℓ))) := by
    rw [boxL1]
    exact (lintegral_prod _ ((he.mono_measure (prod_restrict_acube_le ℓ)).aemeasurable.enorm)).symm
  rw [h1, Measure.prod_restrict]
  simpa using lintegral_mono_set (μ := (volume : Measure E3).prod (volume : Measure E3))
    (s := acb ℓ ×ˢ acb ℓ) (t := Set.univ) (Set.subset_univ _)

/-- **The transfer step.**  If the block-I identity holds at every bounded measurable symmetric
pair kernel (with a fixed weight `G` bounded by `Bc` on the box), then it holds at every integrable,
a.e.-strongly-measurable, pointwise symmetric pair kernel. -/
theorem lhsGen_eq_of_bounded {n : ℕ} {ℓ : ℝ} {Θ : Xn n → ℂ} {A B : E3 → ℂ} {p : Fin n × Fin n}
    (D : RowData n ℓ Θ A B p) {G : Xn n → ℝ} {Bc : ℝ} (hBc : 0 ≤ Bc)
    (hGc : Continuous G) (hGb : ∀ x ∈ abx n ℓ, ‖G x‖ ≤ Bc)
    (hbound : ∀ h : E3 → E3 → ℝ, Measurable (Function.uncurry h) →
      (∃ C : ℝ, ∀ a b, ‖h a b‖ ≤ C) → (∀ a b, h a b = h b a) →
      lhsGen ℓ Θ A B p h = ∫ x in abx n ℓ, G x * h (x p.1) (x p.2))
    {k : E3 → E3 → ℝ}
    (hkm : AEStronglyMeasurable (Function.uncurry k)
      ((volume : Measure E3).prod (volume : Measure E3)))
    (hkI : Integrable (Function.uncurry k)
      ((volume : Measure E3).prod (volume : Measure E3)))
    (hksym : ∀ a b, k a b = k b a) :
    lhsGen ℓ Θ A B p k = ∫ x in abx n ℓ, G x * k (x p.1) (x p.2) := by
  obtain ⟨K, hK0, hK⟩ := lhsGen_abs_le D
  -- the measurable hull of `k`
  set g : E3 × E3 → ℝ := AEMeasurable.mk (Function.uncurry k) hkI.aemeasurable with hgdef
  have hgm : Measurable g := hkI.aemeasurable.measurable_mk
  have hga : Function.uncurry k =ᵐ[(volume : Measure E3).prod (volume : Measure E3)] g :=
    hkI.aemeasurable.ae_eq_mk
  -- its symmetrisation
  set H : E3 → E3 → ℝ := fun a b => (g (a, b) + g (b, a)) / 2 with hHdef
  have hHm : Measurable (Function.uncurry H) := by
    rw [show Function.uncurry H = fun q : E3 × E3 => (g q + g (q.2, q.1)) / 2 from rfl]
    exact (hgm.add (hgm.comp measurable_swap)).div_const 2
  have hHsym : ∀ a b, H a b = H b a := by
    intro a b
    simp only [hHdef, Prod.fst_swap, Prod.snd_swap]
    ring
  have hswapmp : Measure.QuasiMeasurePreserving (Prod.swap : E3 × E3 → E3 × E3)
      ((volume : Measure E3).prod (volume : Measure E3))
      ((volume : Measure E3).prod (volume : Measure E3)) :=
    ⟨measurable_swap, Measure.absolutelyContinuous_of_eq (by
      simpa using (MeasureTheory.Measure.prod_swap (μ := (volume : Measure E3))
        (ν := (volume : Measure E3))))⟩
  have hgswap : (fun q : E3 × E3 => g (q.2, q.1))
      =ᵐ[(volume : Measure E3).prod (volume : Measure E3)] Function.uncurry k := by
    have h1 := hswapmp.ae_eq hga.symm
    have h2 : (fun q : E3 × E3 => Function.uncurry k (q.2, q.1))
        =ᵐ[(volume : Measure E3).prod (volume : Measure E3)] Function.uncurry k :=
      Filter.Eventually.of_forall fun q => hksym q.2 q.1
    exact h1.trans h2
  have hHa : Function.uncurry H
      =ᵐ[(volume : Measure E3).prod (volume : Measure E3)] Function.uncurry k := by
    rw [show Function.uncurry H = fun q : E3 × E3 => (g q + g (q.2, q.1)) / 2 from rfl]
    refine (hga.and hgswap).mono fun q hq => ?_
    obtain ⟨hq1, hq2⟩ := hq
    simp only [Function.uncurry] at hq1 hq2 ⊢
    rw [← hq1, hq2]
    ring
  -- the box `L¹` norms are finite
  have hHbox : boxL1 ℓ H < ⊤ := by
    refine lt_of_le_of_lt (boxL1_le_lintegral_full hHm.aestronglyMeasurable) ?_
    have hEq : (fun q : E3 × E3 => ‖Function.uncurry H q‖ₑ)
        =ᵐ[(volume : Measure E3).prod (volume : Measure E3)]
        (fun q => ‖Function.uncurry k q‖ₑ) :=
      hHa.mono fun q hq => by
        show ‖Function.uncurry H q‖ₑ = ‖Function.uncurry k q‖ₑ
        rw [hq]
    rw [lintegral_congr_ae hEq]
    exact hkI.hasFiniteIntegral
  have hHNbox : ∀ N : ℕ, boxL1 ℓ (trunc N H) < ⊤ := fun N =>
    lt_of_le_of_lt (boxL1_mono fun a b => trunc_enorm_le N H a b) hHbox
  have hidbox : ∀ N : ℕ, boxL1 ℓ (fun a b => H a b - trunc N H a b) < ⊤ := fun N =>
    lt_of_le_of_lt (boxL1_mono fun a b => by
      rw [trunc_sub_abs]
      split_ifs with h
      · exact norm_nonneg _
      · exact le_refl _) hHbox
  -- the two sides agree at `k` and at `H`
  have hLHS1 : lhsGen ℓ Θ A B p k = lhsGen ℓ Θ A B p H := by
    simp only [lhsGen]
    rw [dict13RowShapeCongrAe hHa]
  have hRHS1 : (∫ x in abx n ℓ, G x * k (x p.1) (x p.2))
      = ∫ x in abx n ℓ, G x * H (x p.1) (x p.2) := rhsGen_congr_ae D.hp hHa.symm
  -- the bounded dictionary at the truncations
  have htrunc : ∀ N : ℕ, lhsGen ℓ Θ A B p (trunc N H)
      = ∫ x in abx n ℓ, G x * trunc N H (x p.1) (x p.2) := fun N =>
    hbound (trunc N H) (measurable_trunc hHm N)
      ⟨(N : ℝ), fun a b => trunc_abs_le N H a b⟩ fun a b => trunc_symm hHsym N a b
  -- the left-hand side converges
  have hLtend : Filter.Tendsto (fun N : ℕ => lhsGen ℓ Θ A B p (trunc N H))
      Filter.atTop (nhds (lhsGen ℓ Θ A B p H)) := by
    have hlin : ∀ N : ℕ, lhsGen ℓ Θ A B p H - lhsGen ℓ Θ A B p (trunc N H)
        = lhsGen ℓ Θ A B p (fun a b => H a b - trunc N H a b) := fun N =>
      lhsGen_linear D hHm (measurable_trunc hHm N) (measurable_trunc_sub hHm N)
        hHbox (hHNbox N) (hidbox N)
    have habs : ∀ N : ℕ, |lhsGen ℓ Θ A B p (fun a b => H a b - trunc N H a b)|
        ≤ K * (boxL1 ℓ (fun a b => H a b - trunc N H a b)).toReal := fun N =>
      hK _ (measurable_trunc_sub hHm N) (hidbox N)
    have hlim0 : Filter.Tendsto
        (fun N : ℕ => |lhsGen ℓ Θ A B p (fun a b => H a b - trunc N H a b)|)
        Filter.atTop (nhds 0) :=
      squeeze_zero (fun N => abs_nonneg _) habs
        (by simpa using (boxL1_trunc_tendsto hHm hHbox).const_mul K)
    have hlim1 : Filter.Tendsto
        (fun N : ℕ => lhsGen ℓ Θ A B p (fun a b => H a b - trunc N H a b))
        Filter.atTop (nhds 0) := by
      exact (tendsto_zero_iff_abs_tendsto_zero _).mpr hlim0
    have hlim2 : Filter.Tendsto
        (fun N : ℕ => lhsGen ℓ Θ A B p H - lhsGen ℓ Θ A B p (trunc N H))
        Filter.atTop (nhds 0) :=
      Filter.Tendsto.congr (fun N => (hlin N).symm) hlim1
    have h3 := (tendsto_const_nhds (x := lhsGen ℓ Θ A B p H)).sub hlim2
    simpa using h3.congr fun N => sub_sub_self _ _
  -- the right-hand side converges
  have hRtend : Filter.Tendsto
      (fun N : ℕ => ∫ x in abx n ℓ, G x * trunc N H (x p.1) (x p.2))
      Filter.atTop (nhds (∫ x in abx n ℓ, G x * H (x p.1) (x p.2))) := by
    have hlin : ∀ N : ℕ,
        (∫ x in abx n ℓ, G x * H (x p.1) (x p.2))
          - (∫ x in abx n ℓ, G x * trunc N H (x p.1) (x p.2))
        = ∫ x in abx n ℓ, G x * (H (x p.1) (x p.2) - trunc N H (x p.1) (x p.2)) := fun N =>
      rhsGen_linear D.hℓ hGc D.hp hHm.aestronglyMeasurable
        (measurable_trunc hHm N).aestronglyMeasurable hHbox (hHNbox N)
    have habs : ∀ N : ℕ,
        |∫ x in abx n ℓ, G x * (H (x p.1) (x p.2) - trunc N H (x p.1) (x p.2))|
        ≤ Bc * (ℓ ^ 3) ^ (n - 2)
            * (boxL1 ℓ (fun a b => H a b - trunc N H a b)).toReal := fun N =>
      rhsGen_abs_le D.hℓ hBc hGb D.hp (measurable_trunc_sub hHm N).aestronglyMeasurable
        (hidbox N)
    have hlim0 : Filter.Tendsto
        (fun N : ℕ => |∫ x in abx n ℓ, G x * (H (x p.1) (x p.2) - trunc N H (x p.1) (x p.2))|)
        Filter.atTop (nhds 0) :=
      squeeze_zero (fun N => abs_nonneg _) habs
        (by simpa using ((boxL1_trunc_tendsto hHm hHbox).const_mul
          (Bc * (ℓ ^ 3) ^ (n - 2))))
    have hlim1 : Filter.Tendsto
        (fun N : ℕ => ∫ x in abx n ℓ, G x * (H (x p.1) (x p.2) - trunc N H (x p.1) (x p.2)))
        Filter.atTop (nhds 0) := by
      exact (tendsto_zero_iff_abs_tendsto_zero _).mpr hlim0
    have hlim2 : Filter.Tendsto
        (fun N : ℕ => (∫ x in abx n ℓ, G x * H (x p.1) (x p.2))
          - (∫ x in abx n ℓ, G x * trunc N H (x p.1) (x p.2)))
        Filter.atTop (nhds 0) :=
      Filter.Tendsto.congr (fun N => (hlin N).symm) hlim1
    have h3 := (tendsto_const_nhds
      (x := ∫ x in abx n ℓ, G x * H (x p.1) (x p.2))).sub hlim2
    simpa using h3.congr fun N => sub_sub_self _ _
  -- conclude
  have hfinal : lhsGen ℓ Θ A B p H - (∫ x in abx n ℓ, G x * H (x p.1) (x p.2)) = 0 := by
    have h1 := hLtend.sub hRtend
    have h3 : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop
        (nhds (lhsGen ℓ Θ A B p H - (∫ x in abx n ℓ, G x * H (x p.1) (x p.2)))) :=
      h1.congr' (Filter.Eventually.of_forall fun N => htrunc N ▸ sub_self _)
    exact tendsto_nhds_unique h3 tendsto_const_nhds
  rw [hLHS1, hRHS1]
  exact sub_eq_zero.mp hfinal

end Work.BoseBoxFock
