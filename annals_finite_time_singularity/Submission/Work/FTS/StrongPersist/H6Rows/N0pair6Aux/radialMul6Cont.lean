import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.OpenPkg.radialMul_field
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Ip6DzAux
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.FkJets
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.FkSlots
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.RadialMul6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The radial multiplier at level six

For a *radial* factor `X` (`z ↦ X z`, smooth on `(0,∞)`, with all its `D_z`-jets up to order
six bounded by `M`) and any datum `ψ` which is `C^∞` on the open quadrant and honest in `ℋ⁶`,
the product `(z,θ) ↦ X z * ψ z θ` is again in `ℋ⁶`.

This is the level-six instance of the naive Leibniz bound: the level-six slots of the product
are dominated by `C·M²·HkIntegrand α 6 ψ`, because *every* radial derivative `D_z^b X`, `b ≤ 6`,
is bounded (the sibling `Work.FTS.StrongPersist.hkIntegrand_prod_le_rad_uniform6` needs a
radial Hardy bound for the single top slot `b = 6` instead, which is only available for data
with decay; here the bound on `D_z^6 X` comes for free from `L12Sup6` for `X = L₁₂ f`).
-/

/-- Every binomial coefficient occurring in the level-six Leibniz expansions is at most
`2⁶ = 64`, hence its square is at most `4096`. -/
theorem choose_sq_le_4096 {i b : ℕ} (hi : i ≤ 6) :
    (((i.choose b : ℕ) : ℝ)) ^ 2 ≤ 4096 := by
  have h1 : i.choose b ≤ 2 ^ i := Nat.choose_le_two_pow i b
  have h2 : 2 ^ i ≤ 64 := by
    calc 2 ^ i ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hi
      _ = 64 := by norm_num
  have h3 : ((i.choose b : ℕ) : ℝ) ≤ 64 := by exact_mod_cast le_trans h1 h2
  have h0 : (0 : ℝ) ≤ ((i.choose b : ℕ) : ℝ) := by positivity
  nlinarith [h3, h0]




end Work.FTS.StrongPersist.H6Pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T3RowAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Small `θ`-slice facts -/

/-- A single slot of `f` is dominated by the level-six integrand. -/
theorem slotW_slot_le6 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {a b : ℕ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hab : a + b ≤ 6) :
    Work.FTS.TransportS.slotW α a z θ * (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  rcases eq_or_ne a 0 with ha | ha
  · subst ha
    rw [Work.FTS.TransportS.slotW_zero_eq α hθ]
    have h := sq_le_HkIntegrand_pure6 (f := f) (z := z) (θ := θ) α
      (show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) b (by omega)
    simpa only [Work.Spaces.mixed_zero_right] using h
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    rw [Work.FTS.TransportS.slotW_of_pos_eq α ha1 hθ]
    exact sq_le_HkIntegrand_mixed6 α hα ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩ b a ha1 hab

/-- The `ρ`-weighted product of two slots of `f` is dominated by the level-six integrand. -/
theorem leaf_slice_le6 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {a b k : ℕ}
    {ρ : ℝ → ℝ → ℝ} (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (hab : a + b ≤ 6)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|
      ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  obtain ⟨hρnn, hρle⟩ := Work.FTS.TransportS.IsLeafW_le α hα hleaf
  have hρ0 : 0 ≤ ρ z θ := hρnn z θ hz hθ.1 hθ.2
  have h1 : ρ z θ * (Work.Spaces.mixed (b - k) a f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    (mul_le_mul_of_nonneg_right (hρle z θ hz hθ.1 hθ.2) (sq_nonneg _)).trans
      (slotW_slot_le6 hα hθ (by omega))
  have h2 : ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    (mul_le_mul_of_nonneg_right (hρle z θ hz hθ.1 hθ.2) (sq_nonneg _)).trans
      (slotW_slot_le6 hα hθ hab)
  have h3 : |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|
      ≤ (1 / 2) * (Work.Spaces.mixed (b - k) a f z θ) ^ 2
        + (1 / 2) * (Work.Spaces.mixed b a f z θ) ^ 2 := by
    rw [← abs_mul]
    exact abs_mul_le_half _ _
  calc ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|
      = ρ z θ * (|Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|) := by
        ring
    _ ≤ ρ z θ * ((1 / 2) * (Work.Spaces.mixed (b - k) a f z θ) ^ 2
          + (1 / 2) * (Work.Spaces.mixed b a f z θ) ^ 2) :=
        mul_le_mul_of_nonneg_left h3 hρ0
    _ = (1 / 2) * (ρ z θ * (Work.Spaces.mixed (b - k) a f z θ) ^ 2)
          + (1 / 2) * (ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) := by ring
    _ ≤ Work.Spaces.HkIntegrand α 6 f z θ := by linarith

/-- The three leaf weights are continuous on the open quadrant. -/
theorem continuousOn_leaf {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) :
    ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  rcases hleaf with rfl | rfl | ⟨-, rfl⟩
  · exact (continuousOn_w_sq_Q0.mul (continuousOn_sin_rpow_Q0 Work.Spaces.eta)).congr
      (fun p _ => rfl)
  · exact continuousOn_w_sq_Q0.congr (fun p _ => rfl)
  · exact (continuousOn_w_sq_Q0.mul (continuousOn_sin_rpow_Q0 (Work.Spaces.gam α))).congr
      (fun p _ => rfl)

/-- A `θ`-slice sum of `ρ`-weighted slot products, with coefficients bounded by `64`, is
dominated by `448` times the level-six integrand. -/
theorem group_sum_le {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (hab : a + b ≤ 6) (P : ℕ → Prop)
    [DecidablePred P] {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (∑ k ∈ Finset.range (b + 1), (if P k then (b.choose k : ℝ)
        * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|)
        else 0))
      ≤ 448 * Work.Spaces.HkIntegrand α 6 f z θ := by
  have hchoose : ∀ k ∈ Finset.range (b + 1), (b.choose k : ℝ) ≤ 64 := by
    intro k hk
    have h1 : b.choose k ≤ 2 ^ b := Nat.choose_le_two_pow b k
    have h2 : 2 ^ b ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast (le_trans h1 h2 : b.choose k ≤ 64)
  have hstep : ∀ k ∈ Finset.range (b + 1),
      (if P k then (b.choose k : ℝ)
        * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|)
        else 0)
        ≤ 64 * Work.Spaces.HkIntegrand α 6 f z θ := by
    intro k hk
    by_cases hP : P k
    · rw [if_pos hP]
      have hle := leaf_slice_le6 (f := f) (k := k) (ρ := ρ) hα hleaf hab hz hθ
      have hc := hchoose k hk
      have hρnn : 0 ≤ ρ z θ := (Work.FTS.TransportS.IsLeafW_le α hα hleaf).1 z θ hz hθ.1 hθ.2
      exact mul_le_mul hc hle
        (mul_nonneg (mul_nonneg hρnn (abs_nonneg _)) (abs_nonneg _)) (by norm_num)
    · rw [if_neg hP]
      exact mul_nonneg (by norm_num) (Work.Spaces.HkIntegrand_nonneg α 6 f z θ)
  have hcard : (Finset.range (b + 1)).card = b + 1 := Finset.card_range _
  have hle7 : ((b + 1 : ℕ) : ℝ) ≤ 7 := by
    have hb : b ≤ 6 := by omega
    exact_mod_cast (by omega : b + 1 ≤ 7)
  have hnn := Work.Spaces.HkIntegrand_nonneg α 6 f z θ
  calc (∑ k ∈ Finset.range (b + 1), (if P k then (b.choose k : ℝ)
        * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|)
        else 0))
      ≤ ∑ _k ∈ Finset.range (b + 1), 64 * Work.Spaces.HkIntegrand α 6 f z θ :=
        Finset.sum_le_sum hstep
    _ = 64 * ((b + 1 : ℕ) : ℝ) * Work.Spaces.HkIntegrand α 6 f z θ := by
        rw [Finset.sum_const, hcard]
        simp only [nsmul_eq_mul]
        ring
    _ ≤ 448 * Work.Spaces.HkIntegrand α 6 f z θ := by
        have : (64 : ℝ) * ((b + 1 : ℕ) : ℝ) ≤ 448 := by nlinarith [hle7]
        exact mul_le_mul_of_nonneg_right this hnn

/-- A property holding for every `z > 0` holds a.e. for the measure restricted to `Iz`. -/
theorem ae_restrict_Iz_of_pos {p : ℝ → Prop} (h : ∀ z : ℝ, 0 < z → p z) :
    ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), p z := by
  rw [Work.Spaces.Iz]
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => h z hz)

/-- The first group of slots (those with at most four derivatives on the coefficient). -/
def B1f (a b : ℕ) (ρ : ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (b + 1), (if k ≤ 4 then (b.choose k : ℝ)
    * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|) else 0)

/-- The second group of slots (those with at least five derivatives on the coefficient). -/
def B2f (a b : ℕ) (ρ : ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (b + 1), (if 5 ≤ k then (b.choose k : ℝ)
    * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|) else 0)

theorem B2f_continuousOn {α : ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) :
    ContinuousOn (fun p : ℝ × ℝ => B2f a b ρ f p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  simp only [B2f]
  refine continuousOn_finsetSum _ fun k _ => ?_
  by_cases h5 : 5 ≤ k
  · simp only [if_pos h5]
    exact continuousOn_const.mul
      (((continuousOn_leaf hleaf).mul ((hso.mixed (b - k) a).continuousOn).abs).mul
        ((hso.mixed b a).continuousOn).abs)
  · simp only [if_neg h5]; exact continuousOn_const

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.radialMul6Cont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Continuity of the order-`6` `ℋ`-integrand of a radial multiple

For a radial factor `X` which is only `C^6` on `(0,∞)` (it is *not* smooth on a neighbourhood of
the closed quadrant, so none of the `C^∞`-machinery of `Work.Spaces` applies to the product) and
a datum `f` smooth on the open quadrant `Q0 = (0,∞) × (0,π/2)`, the weighted integrand

`HkIntegrand α 6 (fun z θ => X z * f z θ)`

is continuous on the open quadrant.  Every one of the finitely many derivatives occurring in
`HkIntegrand` is a `z`-only combination of the `z`-only iterates of `D_z = z ∂_z`, so the
Leibniz expansion `H6Pair6Aux.leibniz_radial_mul` (which needs only `X` of class `C^6` on
`(0,∞)`) exhibits it as a finite sum of products of continuous functions.

The two weights `w z / sin(2θ)^{η/2}` and `W α z θ = w z / sin(2θ)^{γ/2}` are continuous on the
open quadrant since `sin(2θ) > 0` there.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

open scoped Real Topology
open Set Filter

set_option maxHeartbeats 1600000

/-! ## The weights on the open quadrant -/

/-- `sin (2θ) > 0` for `θ ∈ (0, π/2)`. -/
private lemma sin_two_pos_Q0 {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The radial weight `w z = (1+z)²/z²` is continuous on the open quadrant. -/
private lemma continuousOn_w_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

/-- The angular weight `sin(2θ)^c` is continuous on the open quadrant. -/
private lemma continuousOn_sinpow_Q0 (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Work.FTS.EllipticEst.Q0 :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun _p hp => Or.inl (ne_of_gt (sin_two_pos_Q0 (Work.FTS.EllipticEst.mem_Q0.mp hp).2)))

/-- The product weight `W = w · sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
private lemma continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  exact continuousOn_w_Q0.mul (continuousOn_sinpow_Q0 _)

/-! ## The mixed derivatives of a radial multiple -/

/-- **Continuity of the mixed derivatives of a radial multiple.**  For `X` of class `C^6` on
`(0,∞)`, `f` smooth on the open quadrant and `j ≤ 6`, the function
`(z,θ) ↦ D_z^j D_θ^i (X · f) z θ` is continuous on `Q0` (with no restriction on `i`).

The key point is that the derivative in `z` may be transferred to the radial factor by
`H6Pair6Aux.leibniz_radial_mul`, which is available for a merely `C^6` factor `X`. -/
private lemma continuousOn_mixed_radial_mul {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hX : ContDiffOn ℝ 6 X (Set.Ioi 0)) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {j i : ℕ} (hj : j ≤ 6) :
    ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i (fun z θ => X z * f z θ) p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  -- the Leibniz sum, which is manifestly continuous
  have hS : ContinuousOn (fun p : ℝ × ℝ =>
      ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) *
        (Work.Elliptic.DzdIter k X p.1 * Work.Spaces.mixed (j - k) i f p.1 p.2))
      Work.FTS.EllipticEst.Q0 := by
    refine continuousOn_finsetSum _ (fun k hk => ?_)
    have hk6 : k ≤ 6 := by
      have := Finset.mem_range.mp hk
      omega
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul ?_ ?_)
    · exact (Work.FTS.StrongPersist.L3Rhs.NfkAux.continuousOn_DzdIter_of_radial
        (r := X) (n := 6) (fun m hm => hX.of_le (by exact_mod_cast hm)) (a := k) hk6).comp
        continuousOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
    · exact (hf.mixed (j - k) i).continuousOn
  refine hS.congr (fun p hp => ?_)
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul hX hf j i hj p.1 p.2 hz hθ0 hθ1

/-! ## The requested continuity -/

theorem radialMul6Cont (α : ℝ) (X : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hX : ContDiffOn ℝ 6 X (Set.Ioi 0)) (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6 (fun z θ => X z * f z θ) p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  -- the `D_z`-slots
  have hDz : ∀ i : ℕ, i ≤ 6 → ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.DzIter i (fun z θ => X z * f z θ) p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    fun i hi => continuousOn_mixed_radial_mul (X := X) (f := f) hX hf (j := i) (i := 0) hi
  -- the mixed slots
  have hMx : ∀ j i : ℕ, i + j ≤ 6 → ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.mixed j i (fun z θ => X z * f z θ) p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    fun j i hij => continuousOn_mixed_radial_mul (X := X) (f := f) hX hf (j := j) (i := i)
      (by omega)
  -- the weighted `D_z`-slot
  have hwdiv : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1
      / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Work.FTS.EllipticEst.Q0 :=
    continuousOn_w_Q0.div (continuousOn_sinpow_Q0 _) (fun p hp =>
      ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_Q0 (Work.FTS.EllipticEst.mem_Q0.mp hp).2) _))
  have hHk : (fun p : ℝ × ℝ =>
        Work.Spaces.HkIntegrand α 6 (fun z θ => X z * f z θ) p.1 p.2)
      = fun p : ℝ × ℝ =>
          (∑ i ∈ Finset.range (6 + 1),
              (Work.Spaces.DzIter i (fun z θ => X z * f z θ) p.1 p.2
                * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
                if 1 ≤ i ∧ i + j ≤ 6
                then (Work.Spaces.mixed j i (fun z θ => X z * f z θ) p.1 p.2
                  * Work.Spaces.Wt α p.1 p.2) ^ 2
                else 0 := by
    funext p; rfl
  rw [hHk]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum (Finset.range (6 + 1)) (fun i hi => ?_)
    exact ((hDz i (by have := Finset.mem_range.mp hi; omega)).mul hwdiv).pow 2
  · refine continuousOn_finsetSum (Finset.range (6 + 1)) (fun i _ =>
      continuousOn_finsetSum (Finset.range (6 + 1)) (fun j _ => ?_))
    split_ifs with hic
    · exact (((hMx j i hic.2).mul (continuousOn_Wt_Q0 α))).pow 2
    · exact continuousOn_const

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
end
