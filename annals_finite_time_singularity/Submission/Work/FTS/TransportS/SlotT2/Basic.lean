import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.TransportS.SupDzWeighted.supDz_weighted_avg_le
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.WProductRule
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `mixed_le_WlInf6`

Pointwise control of every mixed derivative `D_z^b D_θ^a f` inside the open quadrant by the
`𝒲^{6,∞}`-norm, for `f` of class `SmoothOpen` (`C^∞` on the open quadrant only) — the order-6
companion of `Work.FTS.OpenPkg.Mixed_le_WlInf_open` (which is the order-4 statement, constant
`100`).

The angular summands of the `𝒲^{6,∞}`-norm control
`(z+1)^k ∂_z^k D_θ^j f · sin(2θ)^{-α/5}/(α + sin 2θ)`; `Work.Spaces.pz_Dth_sup_bound` turns this
into the unweighted pointwise bound

`|z^k ∂_z^k D_θ^j f| ≤ |f|_𝒲 · (z+1)^{-k} (α + sin 2θ) sin(2θ)^{α/5}`   (`1 ≤ j`, `k + j ≤ 6`).

Combining this with the Stirling expansion of `D_z^b` in the genuine smooth order on the open
half-line (`Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open`) and
`Work.Spaces.abs_sum_scoef_mul_le` (the total coefficient mass is the Bell number
`bell b ≤ 203 ≤ 1000` for `b ≤ 6`) gives the stated bound with constant `1000`.
-/

open scoped Real

namespace Work.FTS.StrongPersist.N6Trans.L6FBound

/-- The Bell numbers of the rows `0 ≤ n ≤ 6` are `1, 1, 2, 5, 15, 52, 203`, all of them
well below `1000`. -/
theorem bell_le_six (n : ℕ) (hn : n ≤ 6) : Work.Spaces.bell n ≤ 1000 := by
  interval_cases n <;> decide

/-- `|f|_{𝒲^{6,∞}} ≥ 0`. -/
theorem WlInf6_nonneg {α : ℝ} {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.WlInfMem α 6 f) :
    0 ≤ Work.Spaces.WlInf α 6 f := by
  rw [Work.Spaces.WlInf]
  exact add_nonneg (Work.Spaces.wlZSum_nonneg α 6 f hmem)
    (Work.Spaces.wlThSum_nonneg α 6 f hmem)

/-- `|z^j ∂_z^j (D_θ^a f)| ≤ |f|_𝒲 · sin(2θ)^{α/5}(α+sin 2θ)` for `1 ≤ a`, `j + a ≤ 6`. -/
theorem zpz_Dth_le_WlInf6 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.WlInfMem α 6 f) {a : ℕ} (ha : 1 ≤ a) {j : ℕ} (hja : j + a ≤ 6)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |z ^ j * Work.Spaces.pzIter j (Work.Spaces.DthIter a f) z θ| ≤
      Work.Spaces.WlInf α 6 f * ((α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5)) := by
  have hz0 : (0:ℝ) ≤ z := hz
  have hz1 : (0:ℝ) < z + 1 := by linarith
  have h := Work.Spaces.pz_Dth_sup_bound α hα 6 f hmem a j ha hja z θ hz hθ
  have hW := WlInf6_nonneg hmem
  have hnn : 0 ≤ (α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5) :=
    mul_nonneg (by linarith [Work.Spaces.sin_two_nonneg' hθ])
      (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg' hθ) _)
  rw [abs_mul, abs_of_nonneg (pow_nonneg hz0 j)]
  have hle1 : (z/(z+1))^j ≤ 1 :=
    pow_le_one₀ (div_nonneg hz0 (by linarith)) (by rw [div_le_one hz1]; linarith)
  calc z ^ j * |Work.Spaces.pzIter j (Work.Spaces.DthIter a f) z θ|
      ≤ z ^ j * (Work.Spaces.WlInf α 6 f / (z+1)^j
          * ((α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5))) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hz0 j)
    _ = Work.Spaces.WlInf α 6 f
          * ((z/(z+1))^j * ((α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5))) := by
        rw [div_pow]; ring
    _ ≤ Work.Spaces.WlInf α 6 f
          * (1 * ((α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle1 hnn) hW
    _ = Work.Spaces.WlInf α 6 f
          * ((α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5)) := by ring

theorem mixed_le_WlInf6 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.WlInfMem α 6 f)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a + b ≤ 6) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.mixed b a f z θ| ≤ 1000 * (Work.Spaces.WlInf α 6 f
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hb6 : b ≤ 6 := by omega
  -- the angular factor is nonnegative, and so is the whole bound
  have hsin0 : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg' hθI
  have hY : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hsin0 _)
  have hM : 0 ≤ Work.Spaces.WlInf α 6 f
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
    mul_nonneg (WlInf6_nonneg hfm) hY
  -- the pointwise bound for the individual `z^k ∂_z^k (D_θ^a f)`-terms
  have hbound : ∀ k ≤ b, |z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter a f) z θ|
      ≤ Work.Spaces.WlInf α 6 f
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
    fun k hk => zpz_Dth_le_WlInf6 hα hfm ha (by omega) hzI hθI
  -- the Stirling expansion of `D_z^b` in the genuine smooth order on `(0,∞)`
  have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z' => Work.Spaces.DthIter a f z' θ) (Set.Ioi 0) :=
    Work.FTS.OpenPkg.smoothOpen_DthIter_slice_z hf a hθ
  rw [Work.Spaces.mixed,
    Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open (h := Work.Spaces.DthIter a f) hsmooth b z hz]
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b
    (Work.Spaces.WlInf α 6 f
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
    (fun k => z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter a f) z θ) hbound
  refine le_trans hsum ?_
  calc (Work.Spaces.bell b : ℝ)
        * (Work.Spaces.WlInf α 6 f
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
      ≤ 1000 * (Work.Spaces.WlInf α 6 f
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast bell_le_six b hb6) hM

end Work.FTS.StrongPersist.N6Trans.L6FBound
end
-- ===== merged: Submission.Work.FTS.TransportS.IPFixDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The slot sum of level `n`**: the sum of the absolute values of the slot pairings with the
leaf weights of `H1IP`, over the slots `(a,b)` with `a + b ≤ n`.  The `a ≥ 1` guard on the
`γ`-weight is the one of `leafSum`/`IsLeafW` (the `10^21`-term of `H1IP` acts on a `D_θ` and
therefore always sits at a slot with `a ≥ 1`).

This is the quantity that the unfolding of `IPn α n` is bounded by at level `n + 1`: each
`HkIPStep` raises the order of the slot by one, and each `H1IP` adds at most one more. -/
def SlotSum (α : ℝ) (n : ℕ) (u v : Fn) : ℝ :=
  ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
    (|slotPairing leafEta a b u v| + |slotPairing leafOne a b u v|
      + (if 1 ≤ a then |slotPairing (leafGam α) a b u v| else 0))

/-- **The summand of `SlotSum`**: the sum of the absolute values of the three leaf weightings of
the slot `(a,b)`, with the `a ≥ 1` guard on the `γ`-weight. -/
def SlotTerm (α : ℝ) (a b : ℕ) (u v : Fn) : ℝ :=
  |slotPairing leafEta a b u v| + |slotPairing leafOne a b u v|
    + (if 1 ≤ a then |slotPairing (leafGam α) a b u v| else 0)

/-- `SlotSum` is the sum of the summands `SlotTerm`. -/
theorem SlotSum_eq_sum_SlotTerm (α : ℝ) (n : ℕ) (u v : Fn) :
    SlotSum α n u v
      = ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          SlotTerm α a b u v := rfl

/-- The summand of the slot sum is nonnegative. -/
theorem SlotTerm_nonneg (α : ℝ) (a b : ℕ) (u v : Fn) : 0 ≤ SlotTerm α a b u v := by
  unfold SlotTerm
  refine add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) ?_
  by_cases h : 1 ≤ a
  · rw [if_pos h]; exact abs_nonneg _
  · rw [if_neg h]

/-- **The coercive recursion iterated `n` times.**  `IPn α 0 = H1IP α` and
`IPn α (n+1) = HkIPStep 1 1 (IPn α n)`, so `IPn α 3` is exactly the `IP4 α` of
`Work.FTS.CoercivityStep.Assembly`, the inner product of the `ℋ⁴` coercivity. -/
def IPn (α : ℝ) : ℕ → Fn → Fn → ℝ
  | 0 => Work.Coercivity.H1IP α
  | (n + 1) => Work.Coercivity.HkIPStep 1 1 (IPn α n)


/-- The slot sum of level `n` is nonnegative (it is a sum of absolute values). -/
theorem SlotSum_nonneg (α : ℝ) (n : ℕ) (u v : Fn) : 0 ≤ SlotSum α n u v := by
  unfold SlotSum
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  refine add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) ?_
  by_cases h : 1 ≤ a
  · rw [if_pos h]; exact abs_nonneg _
  · rw [if_neg h]

end Work.FTS.TransportS
end
end
-- ===== merged: Submission.Work.FTS.TransportS.SlotT2.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.SlotT2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The canonical slot weight -/

/-- The canonical weight of a slot of the flat pairing: `w(z)² sin(2θ)^{-q}`. -/
def canonW (q : ℝ) (z θ : ℝ) : ℝ := (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)

theorem canonW_nonneg {q z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ canonW q z θ :=
  mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)

/-- At `z = 0` the radial weight vanishes, hence so does `canonW`. -/
theorem canonW_zero_z (q θ : ℝ) : canonW q 0 θ = 0 := by
  simp [canonW, Work.Spaces.w]

/-- `canonW η z θ = Whz z θ ^ 2` on `Iθ`. -/
theorem canonW_eta_eq (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    canonW Work.Spaces.eta z θ = (Work.FTS.H2.Whz z θ) ^ 2 :=
  (Work.FTS.H2.hbi_Whz_sq z θ (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ)).symm

/-- `canonW (gam α) z θ = Wt α z θ ^ 2` on `Iθ`. -/
theorem canonW_gam_eq (α z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    canonW (Work.Spaces.gam α) z θ = (Work.Spaces.Wt α z θ) ^ 2 :=
  (Work.FTS.H2.hbi_Wm_sq α z θ (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ)).symm

/-- For `σ ∈ [0,1]` and `0 < q ≤ q'` the decreasing-exponent estimate `σ^{-q} ≤ σ^{-q'}`. -/
theorem rpow_neg_mono {σ q q' : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hq : 0 < q) (hqq : q ≤ q') :
    σ ^ (-q) ≤ σ ^ (-q') := by
  rcases eq_or_lt_of_le hσ0 with h0 | h0
  · subst h0
    have h1 : (-q : ℝ) ≠ 0 := by linarith
    have h2 : (-q' : ℝ) ≠ 0 := by linarith
    rw [Real.zero_rpow h1, Real.zero_rpow h2]
  · exact Real.rpow_le_rpow_of_exponent_ge h0 hσ1 (by linarith)

/-- `canonW` is monotone in the exponent. -/
theorem canonW_mono {q q' : ℝ} (hq : 0 < q) (hqq : q ≤ q') {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : canonW q z θ ≤ canonW q' z θ :=
  mul_le_mul_of_nonneg_left
    (rpow_neg_mono (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) (Real.sin_le_one _) hq hqq)
    (sq_nonneg _)

/-! ## Pointwise domination of the canonical slot weights by the summands of `HkIntegrand` -/

/-- For `0 < q ≤ η` the pure-`D_z` slot weight `canonW q` is dominated by the `j`-th summand
weight of `HkIntegrand α 4`. -/
theorem canonW_mul_z_le (α : ℝ) (g : ℝ → ℝ → ℝ) {q : ℝ} (hq0 : 0 < q)
    (hq : q ≤ Work.Spaces.eta) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ)
    (j : ℕ) (hj : j ≤ 4) :
    canonW q z θ * (Work.Spaces.DzIter j g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hw : canonW q z θ ≤ (Work.FTS.H2.Whz z θ) ^ 2 := by
    rw [← canonW_eta_eq z θ hθ]
    exact canonW_mono hq0 hq hθ
  calc canonW q z θ * (Work.Spaces.DzIter j g z θ) ^ 2
      ≤ (Work.FTS.H2.Whz z θ) ^ 2 * (Work.Spaces.DzIter j g z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = (Work.Spaces.DzIter j g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [Work.FTS.H2.Whz]; ring
    _ ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ j hj

/-- For `0 < q ≤ γ` the mixed slot weight `canonW q` is dominated by the `(i,j)` summand
weight of `HkIntegrand α 4`. -/
theorem canonW_mul_mixed_le (α : ℝ) (g : ℝ → ℝ → ℝ) {q : ℝ} (hq : 0 < q)
    (hqγ : q ≤ Work.Spaces.gam α) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hw : canonW q z θ ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
    rw [← canonW_gam_eq α z θ hθ]
    exact canonW_mono hq hqγ hθ
  calc canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2
      ≤ (Work.Spaces.Wt α z θ) ^ 2 * (Work.Spaces.mixed j i g z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i j hi hij

/-! ## Monotonicity lemmas for the two iterated integrals -/

theorem integral_Iθ_mono {f g : ℝ → ℝ} (h : ∀ θ ∈ Work.Spaces.Iθ, f θ ≤ g θ)
    (h0 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ f θ) (hg : IntegrableOn g Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, f θ) ≤ ∫ θ in Work.Spaces.Iθ, g θ :=
  MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc h0) hg
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc h)

theorem integral_Iz_mono {f g : ℝ → ℝ} (h : ∀ z ∈ Work.Spaces.Iz, f z ≤ g z)
    (h0 : ∀ z ∈ Work.Spaces.Iz, 0 ≤ f z) (hg : IntegrableOn g Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz, f z) ≤ ∫ z in Work.Spaces.Iz, g z :=
  MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici h0) hg
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici h)

/-! ## Continuity / measurability of the canonical slot integrands -/

theorem continuousOn_canonW (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => canonW q p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    simp only [Work.Spaces.w]
    exact (ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))).pow 2
  have h2 : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-q))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const ?_
    intro p hp
    refine Or.inl (ne_of_gt ?_)
    apply Real.sin_pos_of_pos_of_lt_pi
    · show (0 : ℝ) < 2 * p.2; linarith [hp.2.1]
    · show 2 * p.2 < Real.pi; linarith [hp.2.2, Real.pi_pos]
  exact h1.mul h2


/-- Joint a.e. strong measurability of the mixed canonical slot integrand. -/
theorem mslot_joint_aesm {q : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (j i : ℕ) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => canonW q p.1 p.2 * (Work.Spaces.mixed j i g p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    ((continuousOn_canonW q).mul ((hg.mixed j i).continuousOn.pow 2))


/-- A.e. strong measurability of the mixed canonical slot integrand on a `θ`-slice. -/
theorem mslot_slice_aesm {q : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (j i : ℕ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _
    ((continuousOn_canonW q).mul ((hg.mixed j i).continuousOn.pow 2)) hz

/-! ## Slot integrability -/


theorem mslot_slice_integrable {α q : ℝ} {g : ℝ → ℝ → ℝ} (hq : 0 < q)
    (hqγ : q ≤ Work.Spaces.gam α) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 4 g) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    IntegrableOn (fun θ => canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2)
      Work.Spaces.Iθ := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · subst h0
    rw [show (fun θ => canonW q 0 θ * (Work.Spaces.mixed j i g 0 θ) ^ 2) = fun _ => (0 : ℝ) from by
      funext θ; rw [canonW_zero_z, zero_mul]]
    exact integrableOn_zero
  · refine Integrable.mono' (hmem.1 z hz) (mslot_slice_aesm hg j i hz0) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (canonW_nonneg hθ) (sq_nonneg _))]
    exact canonW_mul_mixed_le α g hq hqγ hz0 hθ j i hi hij

/-! ## The iterated `ℋ⁴`-bounds -/


/-- **The mixed slot energy.**  For `0 < q ≤ γ`, `1 ≤ i`, `i + j ≤ 4` and `g ∈ ℋ⁴`,
`∫_z∫_θ w² sin(2θ)^{-q} (D_z^j D_θ^i g)² ≤ HkSq α 4 g`. -/
theorem canonW_mixed_iterated_le (α : ℝ) {q : ℝ} (hq : 0 < q) (hqγ : q ≤ Work.Spaces.gam α)
    {g : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 g) (j i : ℕ) (hi : 1 ≤ i)
    (hij : i + j ≤ 4) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2)
      ≤ Work.Spaces.HkSq α 4 g := by
  rw [Work.Spaces.HkSq]
  refine integral_Iz_mono (fun z hz => ?_) (fun z hz => ?_) hmem.2
  · rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      rw [show (fun θ => canonW q 0 θ * (Work.Spaces.mixed j i g 0 θ) ^ 2) = fun _ => (0 : ℝ) from by
        funext θ; rw [canonW_zero_z, zero_mul]]
      rw [MeasureTheory.integral_zero]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 g 0 θ)
    · exact integral_Iθ_mono (fun θ hθ => canonW_mul_mixed_le α g hq hqγ hz0 hθ j i hi hij)
        (fun θ hθ => mul_nonneg (canonW_nonneg hθ) (sq_nonneg _)) (hmem.1 z hz)
  · exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (canonW_nonneg hθ) (sq_nonneg _))


/-- The marginal of the mixed slot is a.e. strongly measurable. -/
theorem mslot_marginal_aesm {q : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (j i : ℕ) :
    AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2) (volume.restrict Work.Spaces.Iz) :=
  MeasureTheory.AEStronglyMeasurable.integral_prod_right' (mslot_joint_aesm hg j i)


/-- The marginal of the mixed slot is integrable. -/
theorem mslot_marginal_integrable {α q : ℝ} {g : ℝ → ℝ → ℝ} (hq : 0 < q)
    (hqγ : q ≤ Work.Spaces.gam α) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 4 g) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2) Work.Spaces.Iz := by
  refine Integrable.mono' hmem.2 (mslot_marginal_aesm hg j i) ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (canonW_nonneg hθ) (sq_nonneg _))
  rw [Real.norm_of_nonneg hnn]
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · subst h0
    rw [show (fun θ => canonW q 0 θ * (Work.Spaces.mixed j i g 0 θ) ^ 2) = fun _ => (0 : ℝ) from by
      funext θ; rw [canonW_zero_z, zero_mul]]
    rw [MeasureTheory.integral_zero]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 g 0 θ)
  · exact integral_Iθ_mono (fun θ hθ => canonW_mul_mixed_le α g hq hqγ hz0 hθ j i hi hij)
      (fun θ hθ => mul_nonneg (canonW_nonneg hθ) (sq_nonneg _)) (hmem.1 z hz)

end Work.FTS.TransportS.SlotT2
end
end
