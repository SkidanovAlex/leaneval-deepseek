import Mathlib
import Submission.Work.EKLComp.Entropy
import Submission.Work.EKLComp.tendsto_hPart

/-!
# Monotonicity of `hPart` under a "shifted" entropy comparison of the joins

If the entropy of the `N`-fold join of `Q` is bounded by the entropy of the
`(N+K)`-fold join of `P`, uniformly in `N` and for a fixed shift `K`, then
`h_μ(T,Q) ≤ h_μ(T,P)`: the extra `K` iterates only contribute a `o(N)` term to
`H_μ(⋁_{k<N+K}T^{-k}P)`, which disappears after dividing by `N` and passing to the
limit given by Fekete's lemma (`Work.EKLComp.tendsto_hPart`).

Precisely, for `M ≥ 1`,
`H(Q,M)/M ≤ H(P,M+K)/M = (H(P,M+K)/(M+K)) · ((M+K)/M)`,
where `H(P,M+K)/(M+K) → h_μ(T,P)` and `(M+K)/M → 1`; letting `M → ∞` and using that
`H(Q,M)/M → h_μ(T,Q)` gives the claim.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

namespace Work.EKLComp.prop92win

theorem hPart_le_of_joinSets_le {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] {T : X → X} (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (P Q : Work.EKLContract.FinPart X) (K : ℕ)
    (h : ∀ N, Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T Q N)
              ≤ Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T P (N + K))) :
    Work.EKLContract.hPart μ T Q ≤ Work.EKLContract.hPart μ T P := by
  -- Fekete: both averages converge to the corresponding `hPart`
  have hQ := Work.EKLComp.tendsto_hPart μ hmp Q
  have hP := Work.EKLComp.tendsto_hPart μ hmp P
  have hPshift : Tendsto
      (fun M : ℕ => Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T P (M + K))
        / (((M + K : ℕ)) : ℝ)) atTop (nhds (Work.EKLContract.hPart μ T P)) :=
    hP.comp (tendsto_add_atTop_nat K)
  -- the renormalisation factor `(M+K)/M` tends to `1`
  have hratio : Tendsto (fun M : ℕ => (((M + K : ℕ)) : ℝ) / (M : ℝ)) atTop (nhds 1) := by
    have h2 : Tendsto (fun M : ℕ => (1 : ℝ) + (K : ℝ) / (M : ℝ)) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (K : ℝ))
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with M hM
    have hMne : (M : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have hprod := hPshift.mul hratio
  rw [mul_one] at hprod
  -- compare the two convergent sequences
  refine le_of_tendsto_of_tendsto hQ hprod ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hMne : (M : ℝ) ≠ 0 := by positivity
  have h1 : Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T Q M) / (M : ℝ)
      ≤ Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T P (M + K)) / (M : ℝ) :=
    div_le_div_of_nonneg_right (h M) (by positivity)
  have h3 : Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T P (M + K)) / (M : ℝ) =
      (Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T P (M + K))
        / (((M + K : ℕ)) : ℝ)) * ((((M + K : ℕ)) : ℝ) / (M : ℝ)) := by
    push_cast
    field_simp
  rw [h3] at h1
  exact h1

end Work.EKLComp.prop92win
