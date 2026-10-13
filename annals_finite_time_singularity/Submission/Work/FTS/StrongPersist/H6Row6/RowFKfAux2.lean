/-
# `H6Row6/RowFKfAux2` — helper lemmas for the `(f,K)`-rows `rowFKf` (assembly layer)

The assembly of `Work.FTS.StrongPersist.H6Row6.rowFKf` (the two conjuncts `u = -(1/2)·FK f·D_θf`
and `u = -sin²θ·FK f·f`) needs, on top of the already-proved prices of `RowFKfAux`,
`FkRowPrices`, `FkRowSummandCS`/`fkPairCS` and `FkTileAux`:

* the linearity of `D_θ`-, `D_z`- and mixed iterates in a *constant* factor, so that the
  Leibniz expansion `RowFKfC1.fkRow_expand1` (proved for `FK f·D_θf`) transfers to
  `-(1/2)·FK f·D_θf` (the first conjunct) and to `FK f·(sin²θ·f)`;
* the pointwise domination of a leaf-weighted slot by the `ℋ^m`-integrand at an arbitrary
  `m ≥ i + j` (used at level `7` for the single exceptional summand `b₁ = 0`, `a + b = 6`);
* the elementary arithmetic `M·S ≤ (1+M)²(1+S)` and `1 ≤ α^{-3}` on `Ioc 0 1`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Row6.RowFKfAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T4bSlotAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-! ## Linearity of the iterates in a constant factor -/

/-- `D_θ^n (c · g) = c · D_θ^n g`. -/
theorem DthIter_const_mul_row (c : ℝ) (g : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.DthIter n (fun z θ => c * g z θ)
      = fun z θ => c * Work.Spaces.DthIter n g z θ := by
  funext z θ
  induction n generalizing z θ with
  | zero => rfl
  | succ k ih =>
      show Real.sin (2 * θ)
          * deriv (fun θ' => Work.Spaces.DthIter k (fun z θ => c * g z θ) z θ') θ
        = c * (Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter k g z θ') θ)
      rw [funext (fun θ' => ih z θ'), deriv_const_mul_field]
      ring

/-- `D_z^n (c · g) = c · D_z^n g`. -/
theorem DzIter_const_mul_row (c : ℝ) (g : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.DzIter n (fun z θ => c * g z θ)
      = fun z θ => c * Work.Spaces.DzIter n g z θ := by
  funext z θ
  induction n generalizing z θ with
  | zero => rfl
  | succ k ih =>
      show z * deriv (fun z' => Work.Spaces.DzIter k (fun z θ => c * g z θ) z' θ) z
        = c * (z * deriv (fun z' => Work.Spaces.DzIter k g z' θ) z)
      rw [funext (fun z' => ih z' θ), deriv_const_mul_field]
      ring

/-- `D_z^jD_θ^i (c · g) = c · D_z^jD_θ^i g`. -/
theorem mixed_const_mul_row (c : ℝ) (g : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => c * g z θ)
      = fun z θ => c * Work.Spaces.mixed j i g z θ := by
  rw [Work.Spaces.mixed, DthIter_const_mul_row, Work.Spaces.mixed, DzIter_const_mul_row]

/-! ## A leaf-weighted slot against the `ℋ^m`-integrand -/

/-- Every leaf weight vanishes at `z = 0` (the radial factor `w 0` is `0`). -/
theorem leafW_zero_row {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) (θ : ℝ) : ρ 0 θ = 0 := by
  rcases hρ with h | h | h
  · rw [h, Work.FTS.TransportS.leafEta, Work.Spaces.w]; norm_num
  · rw [h, Work.FTS.TransportS.leafOne, Work.Spaces.w]; norm_num
  · rw [h.2, Work.FTS.TransportS.leafGam, Work.Spaces.w]; norm_num

/-- `HkIntegrand` vanishes at `z = 0` (both weights carry a factor `w 0 = 0`). -/
theorem HkIntegrand_zero_row (α : ℝ) (m : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α m f 0 θ = 0 := by
  unfold Work.Spaces.HkIntegrand
  have hw : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
  have hWt : Work.Spaces.Wt α 0 θ = 0 := by rw [Work.Spaces.Wt, hw, zero_mul]
  simp only [hw, zero_div, hWt, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Finset.sum_const_zero, add_zero, ite_self]

/-- **The pointwise domination of a leaf-weighted slot by `HkIntegrand α m f`**, for any
`m ≥ i + j` and any leaf weight `ρ` of a slot `a ≤ i` (so that `ρ ≤ slotW α i`). -/
theorem domLeaf_le_row {α : ℝ} (hα : 0 < α) {a i j m : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) (hai : a ≤ i) (hij : i + j ≤ m)
    {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ρ z θ * (Work.Spaces.mixed j i f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α m f z θ := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · rw [← hz0, leafW_zero_row hρ θ, zero_mul, HkIntegrand_zero_row]
  · have h1 : ρ z θ ≤ Work.FTS.TransportS.slotW α i z θ :=
      Work.FTS.StrongPersist.H6Pair6Aux.leaf_le_slotW_of_le hα hρ hai z θ hzpos hθ
    have h2 : Work.FTS.TransportS.slotW α i z θ * (Work.Spaces.mixed j i f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α m f z θ :=
      Work.FTS.StrongPersist.H6Pair6Aux.slotW_slot_le hα hθ hij
    exact le_trans (mul_le_mul_of_nonneg_right h1 (sq_nonneg _)) h2

/-! ## Integrability of a leaf-weighted slot, at an arbitrary level -/

/-- The leaf-weighted slot integrand is continuous on the open quadrant. -/
theorem leafSlot_continuousOn_row {α : ℝ} {a i j : ℕ} {ρ : ℝ → ℝ → ℝ}
    {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2 * (Work.Spaces.mixed j i f p.1 p.2) ^ 2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_leaf hρ).mul
    ((hsm.mixed j i).continuousOn.pow 2)

/-- **The angular slice of a leaf-weighted slot is integrable**, and so is its `z`-marginal,
for an `ℋ^m`-datum and a slot with `a ≤ a'`, `a' + j ≤ m`. -/
theorem slotIntegrable_row {α : ℝ} (hα0 : 0 < α) {f : ℝ → ℝ → ℝ} {m : ℕ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α m f)
    {a a' j : ℕ} {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    (hai : a ≤ a') (haj : a' + j ≤ m) :
    MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed j a' f z θ) ^ 2)
        Work.Spaces.Iz ∧
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => ρ z θ * (Work.Spaces.mixed j a' f z θ) ^ 2) Work.Spaces.Iθ) := by
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ
  have hslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => ρ z θ * (Work.Spaces.mixed j a' f z θ) ^ 2) Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · have hzero : (fun θ : ℝ => ρ z θ * (Work.Spaces.mixed j a' f z θ) ^ 2)
          = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        rw [← hz0, leafW_zero_row hρ θ, zero_mul]
      rw [hzero]
      exact integrableOn_zero
    · refine MeasureTheory.Integrable.mono' (hm.1 z hz)
        (Work.Spaces.aesm_slice_of_continuousOn_Qd _
          (leafSlot_continuousOn_row hsm hρ) hzpos) ?_
      filter_upwards [haeθ] with θ hθ
      rw [Real.norm_of_nonneg (mul_nonneg
        (Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hρ z
          ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) (sq_nonneg _))]
      exact domLeaf_le_row hα0 hρ hai haj hz hθ
  refine ⟨?_, hslice⟩
  have hX : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => ρ p.1 p.2 * (Work.Spaces.mixed j a' f p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (leafSlot_continuousOn_row hsm hρ)
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed j a' f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := hX.integral_prod_right' (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    simpa using h
  refine MeasureTheory.Integrable.mono' hm.2 haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
  have h1 : ‖∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed j a' f z θ) ^ 2‖
      ≤ ∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed j a' f z θ) ^ 2 := by
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [haeθ] with θ hθ
    exact Real.norm_of_nonneg (mul_nonneg
      (Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hρ z
        ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) (sq_nonneg _))
  have h2 : (∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed j a' f z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f z θ := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hm.1 z hz) ?_
    · filter_upwards [haeθ] with θ hθ
      exact mul_nonneg (Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hρ z
        ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) (sq_nonneg _)
    · filter_upwards [haeθ] with θ hθ
      exact domLeaf_le_row hα0 hρ hai haj hz hθ
  linarith

/-! ## The arithmetic of the target shape -/

/-- `M·S ≤ (1+M)²(1+S)` for `M, S ≥ 0`: the target shape absorbs the product of the two
`ℋ`-prices. -/
theorem mul_le_target_row {M S : ℝ} (hM : 0 ≤ M) (hS : 0 ≤ S) :
    M * S ≤ (1 + M) ^ 2 * (1 + S) := by
  have h1 : M ≤ (1 + M) ^ 2 := by nlinarith
  have h2 : S ≤ 1 + S := by linarith
  exact mul_le_mul h1 h2 hS (by positivity)

/-- `1 ≤ α^{-3}` on `Ioc 0 1`. -/
theorem one_le_rpow_neg_three_row {α : ℝ} (hα : α ∈ Set.Ioc 0 1) :
    (1 : ℝ) ≤ α ^ (-(3 : ℝ)) := by
  have h0 : 0 < α := hα.1
  have h3 : α ^ (3 : ℝ) ≤ 1 := by
    calc α ^ (3 : ℝ) ≤ 1 ^ (3 : ℝ) := Real.rpow_le_rpow h0.le hα.2 (by norm_num)
      _ = 1 := Real.one_rpow 3
  calc (1 : ℝ) ≤ (α ^ (3 : ℝ))⁻¹ := (one_le_inv₀ (Real.rpow_pos_of_pos h0 3)).mpr h3
    _ = α ^ (-(3 : ℝ)) := (Real.rpow_neg h0.le 3).symm

end

end Work.FTS.StrongPersist.H6Row6
