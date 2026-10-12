import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.exists_fibre_le_of_integral_ae_hq0_restrict`

The fibre-selection lemma of the `touchingSum` / BF3c assembly, in the form in which the
"a fibre of vanishing weight carries no charge" condition `ν = 0 → q = 0` is only assumed
`μ`-almost everywhere (the pointwise-hypothesis version is
`Work.BoseBoxFock.exists_fibre_le_of_integral_ae`).

If `G` is measurable, `ν ≥ 0` everywhere, `∫_{y ∈ G} ν > 0` and `∫_{y ∈ G} (q − c ν) ≤ 0`, then some
`y ∈ G` satisfies `ν y > 0` and `q y ≤ c ν y`.

Proof.  Put `f := q − c ν`.  Under the negation of the conclusion, `f` is nonnegative a.e. on `G`
(at a point of `G` with `ν = 0`, the a.e. hypothesis `hq0` gives `f = 0`; at a point of `G` with
`ν > 0`, the negation gives `f > 0`), while `∫_G f ≤ 0`.  Hence `f = 0` a.e. on `G`.  On the other
hand `∫_G ν > 0` with `ν ≥ 0` says that `μ.restrict G` gives positive measure to the support of
`ν`, so that support contains a point of the full-`μ.restrict G`-measure set
`{y ∈ G | f y = 0}`; at such a point `ν > 0`, so the negation forces `f > 0`.  Contradiction.
-/

namespace Work.BoseBoxFock

theorem exists_fibre_le_of_integral_ae_hq0_restrict {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} (q ν : α → ℝ) (c : ℝ) (G : Set α)
    (hGm : MeasurableSet G)
    (hνnn : ∀ y, 0 ≤ ν y) (hq0 : ∀ᵐ y ∂μ, ν y = 0 → q y = 0)
    (hqi : MeasureTheory.Integrable q μ) (hνi : MeasureTheory.Integrable ν μ)
    (hint : ∫ y in G, (q y - c * ν y) ∂μ ≤ 0)
    (hpos : 0 < ∫ y in G, ν y ∂μ) :
    ∃ y ∈ G, 0 < ν y ∧ q y ≤ c * ν y := by
  classical
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ y, y ∈ G → 0 < ν y → c * ν y < q y`
  -- the a.e. hypothesis `hq0`, read as: at a.e. point, `ν = 0` and `q ≠ 0` do not both hold
  have hbad : ∀ᵐ y ∂μ, ¬(ν y = 0 ∧ q y ≠ 0) :=
    hq0.mono fun y hy => fun h => h.2 (hy h.1)
  -- `f := q − c ν` is nonnegative on `G`, almost everywhere
  have hGnn : ∀ᵐ y ∂μ, y ∈ G → 0 ≤ q y - c * ν y :=
    hbad.mono fun y hy hyG => by
      by_cases h0 : ν y = 0
      · have hqz : q y = 0 := by
          by_contra hq
          exact hy ⟨h0, hq⟩
        rw [h0, hqz, mul_zero, sub_zero]
      · have hνp : 0 < ν y := lt_of_le_of_ne (hνnn y) (Ne.symm h0)
        have hlt : c * ν y < q y := hcon y hyG hνp
        linarith
  have hfi : MeasureTheory.Integrable (fun y => q y - c * ν y) μ := hqi.sub (hνi.const_mul c)
  -- the integral of `f` over `G` is both `≤ 0` and `≥ 0`
  have hf0 : ∫ y in G, (q y - c * ν y) ∂μ = 0 :=
    le_antisymm hint (MeasureTheory.setIntegral_nonneg_ae hGm hGnn)
  have hfae : 0 ≤ᵐ[μ.restrict G] (fun y => q y - c * ν y) := by
    rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' hGm]
    exact hGnn
  have hzero_ae : (fun y => q y - c * ν y) =ᵐ[μ.restrict G] 0 :=
    (MeasureTheory.setIntegral_eq_zero_iff_of_nonneg_ae hfae hfi.restrict).mp hf0
  have hGae : ∀ᵐ y ∂(μ.restrict G), y ∈ G :=
    (MeasureTheory.ae_restrict_iff' hGm).mpr (Filter.Eventually.of_forall fun y hy => hy)
  have hνae : 0 ≤ᵐ[μ.restrict G] ν := by
    rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' hGm]
    exact Filter.Eventually.of_forall fun y _ => hνnn y
  -- the support of `ν` has positive measure for the restricted measure
  have hνsup : 0 < (μ.restrict G) (Function.support ν) :=
    (MeasureTheory.integral_pos_iff_support_of_nonneg_ae hνae hνi.restrict).mp hpos
  -- pick a point of that support where `f = 0` and which lies in `G`
  have hcomb : ∀ᵐ y ∂(μ.restrict G), q y - c * ν y = 0 ∧ y ∈ G :=
    (show ∀ᵐ y ∂(μ.restrict G), q y - c * ν y = 0 from hzero_ae).and hGae
  obtain ⟨y, hy, hyf, hyG⟩ :=
    MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae (μ := μ.restrict G)
      (s := Function.support ν) hνsup.ne' (p := fun y => q y - c * ν y = 0 ∧ y ∈ G)
      (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self hcomb)
  have hyν : ν y ≠ 0 := hy
  have hyνp : 0 < ν y := lt_of_le_of_ne (hνnn y) (Ne.symm hyν)
  have hlt : c * ν y < q y := hcon y hyG hyνp
  linarith [hyf]

end Work.BoseBoxFock
