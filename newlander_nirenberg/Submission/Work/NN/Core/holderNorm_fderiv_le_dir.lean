import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder.comp_linear_le
import Submission.Work.CR.Flat.Holder.Bilinear

/-!
Copyright: none.  Part of the `Newlander–Nirenberg` formalisation project.

# Directional derivative lowers the Hölder order

For an open set `Ω ⊆ ℂⁿ` and `u : ℂⁿ → ℂ` of class `C^{k+1,α}` on `Ω`, the directional
derivative `z ↦ du_z v` is of class `C^{k,α}` on `Ω`, with

  `holderNorm k α (fun z => fderiv ℝ u z v) Ω ≤ ‖v‖ * holderNorm (k+1) α u Ω`.

The proof is the same mechanism as for the Wirtinger derivatives
(`Work.NN.Core.holderNorm_comp_fderiv_le`): the map `z ↦ du_z v` is the composition of the
fixed continuous linear map `Φ = (L ↦ L v)` on `(ℂⁿ →L[ℝ] ℂ)` with `fderiv ℝ u`, so
`comp_linear_le` bounds each `C^{i,α}` term by `‖Φ‖` times the same term of `fderiv ℝ u`;
the iterated derivatives of `fderiv ℝ u` are those of `u` shifted by one
(`iDN_fderivWithin`/`hSN_fderivWithin`), and on the open set `Ω` we may replace
`fderiv ℝ u` by `fderivWithin ℝ u Ω`.  Since `‖Φ‖ = ‖v‖`, the stated bound follows.
-/

noncomputable section

open scoped NNReal ENNReal Topology
open Set

namespace Work.NN.Core

open Work.CR.Flat (holderNorm iterDerivNorm holderSeminorm)
open Work.CR.Flat.Holder (iDN hSN iDN_congr hSN_congr iDN_fderivWithin hSN_fderivWithin
  comp_linear_le iDN_complex_eq hSN_complex_eq)

/-! ### `holderNorm` depends only on the values on the domain -/

lemma holderNorm_congr_eqOn {n : ℕ} {k : ℕ} {α : ℝ} {f g : Cn n → ℂ} {Ω : Set (Cn n)}
    (h : ∀ x ∈ Ω, f x = g x) : holderNorm k α f Ω = holderNorm k α g Ω := by
  unfold Work.CR.Flat.holderNorm
  exact Finset.sum_congr rfl fun i _ => by
    have h1 : iterDerivNorm i f Ω = iterDerivNorm i g Ω := iDN_congr h
    have h2 : holderSeminorm i α f Ω = holderSeminorm i α g Ω := hSN_congr h
    rw [h1, h2]

/-! ### The main estimate -/

/-- Composing `fderiv ℝ u` with a fixed continuous linear functional `Φ` on the space of
real-linear maps `ℂⁿ → ℂ` multiplies the `C^{k,α}` norm by at most `‖Φ‖`: for `u` of class
`C^{k+1}` on an open `Ω`,

  `holderNorm k α (Φ ∘ fderiv ℝ u) Ω ≤ ‖Φ‖ * holderNorm (k+1) α u Ω`.

This is `Work.NN.Core.holderNorm_comp_fderiv_le` with the normalisation `‖Φ‖ ≤ 1` replaced by
the exact factor `‖Φ‖`. -/
lemma holderNorm_comp_fderiv_le_mul {n : ℕ} (k : ℕ) (α : ℝ) {Ω : Set (Cn n)} (hΩ : IsOpen Ω)
    {u : Cn n → ℂ} (hu : ContDiffOn ℝ ((k+1 : ℕ) : WithTop ℕ∞) u Ω)
    (Φ : (Cn n →L[ℝ] ℂ) →L[ℝ] ℂ) :
    holderNorm k α (Φ ∘ fderiv ℝ u) Ω ≤ ENNReal.ofReal ‖Φ‖ * holderNorm (k+1) α u Ω := by
  have hΩu : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  have hm : ((k:ℕ):WithTop ℕ∞) + 1 ≤ (((k+1:ℕ)):WithTop ℕ∞) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
  have hfdiff : ContDiffOn ℝ (k:ℕ∞) (fun z => fderiv ℝ u z) Ω :=
    hu.fderiv_of_isOpen hΩ hm
  have hterm : ∀ i ∈ Finset.range (k+1),
      iterDerivNorm i (Φ ∘ fderiv ℝ u) Ω + holderSeminorm i α (Φ ∘ fderiv ℝ u) Ω
        ≤ ENNReal.ofReal ‖Φ‖ * (iterDerivNorm (i+1) u Ω + holderSeminorm (i+1) α u Ω) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hik : i ≤ k := by omega
    have hφi : ContDiffOn ℝ (i:ℕ∞) (fun z => fderiv ℝ u z) Ω :=
      hfdiff.of_le (WithTop.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hik))
    have hcomp := comp_linear_le Φ i α hφi hΩu
    have hIdn : iterDerivNorm i (Φ ∘ fderiv ℝ u) Ω
        ≤ ENNReal.ofReal ‖Φ‖ * iterDerivNorm (i+1) u Ω := by
      calc iterDerivNorm i (Φ ∘ fderiv ℝ u) Ω
          = iDN i (Φ ∘ fderiv ℝ u) Ω := (iDN_complex_eq i _ Ω).symm
        _ ≤ ENNReal.ofReal ‖Φ‖ * iDN i (fun z => fderiv ℝ u z) Ω := hcomp.1
        _ = ENNReal.ofReal ‖Φ‖ * iDN i (fun z => fderivWithin ℝ u Ω z) Ω := by
              rw [iDN_congr (fun z hz => (fderivWithin_of_isOpen hΩ hz).symm)]
        _ = ENNReal.ofReal ‖Φ‖ * iDN (i+1) u Ω := by rw [iDN_fderivWithin i u Ω hΩu]
        _ = ENNReal.ofReal ‖Φ‖ * iterDerivNorm (i+1) u Ω := by rw [iDN_complex_eq]
    have hHsn : holderSeminorm i α (Φ ∘ fderiv ℝ u) Ω
        ≤ ENNReal.ofReal ‖Φ‖ * holderSeminorm (i+1) α u Ω := by
      calc holderSeminorm i α (Φ ∘ fderiv ℝ u) Ω
          = hSN i α (Φ ∘ fderiv ℝ u) Ω := (hSN_complex_eq i α _ Ω).symm
        _ ≤ ENNReal.ofReal ‖Φ‖ * hSN i α (fun z => fderiv ℝ u z) Ω := hcomp.2
        _ = ENNReal.ofReal ‖Φ‖ * hSN i α (fun z => fderivWithin ℝ u Ω z) Ω := by
              rw [hSN_congr (fun z hz => (fderivWithin_of_isOpen hΩ hz).symm)]
        _ = ENNReal.ofReal ‖Φ‖ * hSN (i+1) α u Ω := by rw [hSN_fderivWithin i α u Ω hΩu]
        _ = ENNReal.ofReal ‖Φ‖ * holderSeminorm (i+1) α u Ω := by rw [hSN_complex_eq]
    calc iterDerivNorm i (Φ ∘ fderiv ℝ u) Ω + holderSeminorm i α (Φ ∘ fderiv ℝ u) Ω
        ≤ ENNReal.ofReal ‖Φ‖ * iterDerivNorm (i+1) u Ω
            + ENNReal.ofReal ‖Φ‖ * holderSeminorm (i+1) α u Ω := add_le_add hIdn hHsn
      _ = ENNReal.ofReal ‖Φ‖ * (iterDerivNorm (i+1) u Ω + holderSeminorm (i+1) α u Ω) := by
            rw [mul_add]
  calc holderNorm k α (Φ ∘ fderiv ℝ u) Ω
      = ∑ i ∈ Finset.range (k+1), (iterDerivNorm i (Φ ∘ fderiv ℝ u) Ω
          + holderSeminorm i α (Φ ∘ fderiv ℝ u) Ω) := rfl
    _ ≤ ∑ i ∈ Finset.range (k+1), ENNReal.ofReal ‖Φ‖ * (iterDerivNorm (i+1) u Ω
          + holderSeminorm (i+1) α u Ω) := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal ‖Φ‖ * ∑ i ∈ Finset.range (k+1), (iterDerivNorm (i+1) u Ω
          + holderSeminorm (i+1) α u Ω) := by rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal ‖Φ‖ * holderNorm (k+1) α u Ω := by
        refine mul_le_mul_right ?_ _
        rw [Work.CR.Flat.holderNorm]
        conv_rhs => rw [Finset.sum_range_succ']
        exact le_add_right le_rfl

lemma holderNorm_fderiv_le_dir {n : ℕ} {α : ℝ} {Ω : Set (Work.NN.Core.Cn n)} (hΩ : IsOpen Ω)
    (k : ℕ) {u : Work.NN.Core.Cn n → ℂ} (hu : ContDiffOn ℝ ((k+1 : ℕ) : WithTop ℕ∞) u Ω) (v : Work.NN.Core.Cn n) :
    Work.CR.Flat.holderNorm k α (fun z => fderiv ℝ u z v) Ω
      ≤ ENNReal.ofReal ‖v‖ * Work.CR.Flat.holderNorm (k+1) α u Ω := by
  have hnorm : ‖(ContinuousLinearMap.apply ℝ ℂ v : (Cn n →L[ℝ] ℂ) →L[ℝ] ℂ)‖ ≤ ‖v‖ := by
    rw [ContinuousLinearMap.opNorm_le_iff (norm_nonneg v)]
    intro D
    rw [ContinuousLinearMap.apply_apply]
    calc ‖D v‖ ≤ ‖D‖ * ‖v‖ := D.le_opNorm v
      _ = ‖v‖ * ‖D‖ := mul_comm _ _
  have hfun : (fun z => fderiv ℝ u z v)
      = (ContinuousLinearMap.apply ℝ ℂ v : (Cn n →L[ℝ] ℂ) →L[ℝ] ℂ) ∘ (fderiv ℝ u) := by
    funext z
    rw [Function.comp_apply, ContinuousLinearMap.apply_apply]
  rw [hfun]
  calc holderNorm k α
        ((ContinuousLinearMap.apply ℝ ℂ v : (Cn n →L[ℝ] ℂ) →L[ℝ] ℂ) ∘ fderiv ℝ u) Ω
      ≤ ENNReal.ofReal ‖(ContinuousLinearMap.apply ℝ ℂ v : (Cn n →L[ℝ] ℂ) →L[ℝ] ℂ)‖
          * holderNorm (k+1) α u Ω := holderNorm_comp_fderiv_le_mul k α hΩ hu _
    _ ≤ ENNReal.ofReal ‖v‖ * holderNorm (k+1) α u Ω :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal hnorm) _

end Work.NN.Core
