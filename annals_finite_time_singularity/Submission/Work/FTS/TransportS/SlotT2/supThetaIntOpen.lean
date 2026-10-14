import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (RegQ)

set_option autoImplicit false

/-! ## The level package -/

/-- **The level-`n` data of the corrected induction.**  `cs` is the Cauchy–Schwarz bound
consumed at level `n`; `coer` is the coercivity of the clean operator `Lhat` at level `n`,
stated on `RegQ α (n+1)` because the pairing `IP (Lhat f) f` sees the slots of `Lhat f`,
one order deeper than those of `f`. -/
structure CoerData2 (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) (cc CC : ℝ) : Prop where
  /-- the coercivity constant is positive -/
  hcc : 0 < cc
  /-- the Cauchy–Schwarz constant is positive -/
  hCC : 0 < CC
  /-- Cauchy–Schwarz against the honest `ℋⁿ`-norm, on the level-`n` class -/
  cs : ∀ f g : Fn, RegQ α n f → RegQ α n g →
    |IP f g| ≤ CC * Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g
  /-- coercivity of `Lhat` at level `n` -/
  coer : ∀ f : Fn, RegQ α (n + 1) f →
    cc * Work.Spaces.HkSq α n f ≤ IP (Work.FTS.CoercivityFix.Lhat f) f

/-- **The regularity ports the step needs.**  Every field says how `RegQ`-membership
descends when a derivative is taken, or that a slot of the operator/defect is at level `n`
when the argument is at level `n+1` or `n+2`; the last field records the one-sided
comparison of the `ℋⁿ`-norm with the `ℋ^{n+1}`-norm. -/
structure StepReg2 (α : ℝ) (n : ℕ) : Prop where
  /-- `RegQ α (n+2) f → RegQ α n f` -/
  mono1 : ∀ f : Fn, RegQ α (n + 2) f → RegQ α n f
  /-- `RegQ α (n+2) f → RegQ α (n+1) f` -/
  mono2 : ∀ f : Fn, RegQ α (n + 2) f → RegQ α (n + 1) f
  /-- `D_θ` drops the level by one -/
  dth1 : ∀ f : Fn, RegQ α (n + 2) f → RegQ α (n + 1) (Work.Spaces.Dth f)
  /-- `D_z` drops the level by one -/
  dz1 : ∀ f : Fn, RegQ α (n + 2) f → RegQ α (n + 1) (Work.Spaces.Dz f)
  /-- `D_θ` drops the level by two -/
  dth2 : ∀ f : Fn, RegQ α (n + 2) f → RegQ α n (Work.Spaces.Dth f)
  /-- `D_z` drops the level by two -/
  dz2 : ∀ f : Fn, RegQ α (n + 2) f → RegQ α n (Work.Spaces.Dz f)
  /-- `Lhat (D_z f)` is at level `n` when `f` is at level `n+2` -/
  ldz : ∀ f : Fn, RegQ α (n + 2) f →
    RegQ α n (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f))
  /-- the defect `Ê₂ f` is at level `n` when `f` is at level `n+1` -/
  e2r : ∀ f : Fn, RegQ α (n + 1) f → RegQ α n (Work.FTS.CoercivityFix.E2hat f)
  /-- one-sided comparison of the `ℋⁿ`-norms of the three slots with `|f|_{n+1}` -/
  normSub : ∀ f : Fn, RegQ α (n + 2) f →
    Work.Spaces.HkSq α n f ≤ Work.Spaces.HkSq α (n + 1) f
      ∧ Work.Spaces.HkSq α n (Work.Spaces.Dth f) ≤ Work.Spaces.HkSq α (n + 1) f
      ∧ Work.Spaces.HkSq α n (Work.Spaces.Dz f) ≤ Work.Spaces.HkSq α (n + 1) f

/-- **The algebraic inputs of the step, membership-free for the congruence.**  The
congruence of the concrete inner product in its *first* argument on the open quadrant needs
**no** regularity hypothesis (derivatives are local and the quadrant is co-null: see
`StepAssembly/H1IP_congr_qd`), and the two commutator identities are pointwise statements
on the open quadrant. -/
structure Comm2 (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) : Prop where
  /-- congruence in the first argument on the open quadrant, with no membership -/
  congr : ∀ f f' g : Fn,
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP f g = IP f' g
  /-- additivity in the first argument, on the level-`n` class -/
  add : ∀ f₁ f₂ g : Fn, RegQ α n f₁ → RegQ α n f₂ → RegQ α n g →
    IP (f₁ + f₂) g = IP f₁ g + IP f₂ g
  /-- `D_θ` commutes with `Lhat` exactly -/
  dthC : ∀ f : Fn, Work.FTS.LocData.SmoothQuad f → ∀ z θ : ℝ,
    (z, θ) ∈ Work.Construction.Qd →
    Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ
  /-- the `D_z` commutator of `Lhat` is the explicit defect `Ê₂` -/
  dzC : ∀ f : Fn, Work.FTS.LocData.SmoothQuad f → ∀ z θ : ℝ,
    (z, θ) ∈ Work.Construction.Qd →
    Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
        + Work.FTS.CoercivityFix.E2hat f z θ

/-! ## The concrete inner product of `ℋ⁴` -/

/-- **The paper's recursion with explicit step coefficients**: `IP4` in the vocabulary of
`Submission/Work/FTS/CoercivityStep` is `HkIPStep 1 1 (HkIPStep 1 1 (HkIPStep 1 1 (H1IP α)))`;
here the three coefficient pairs are *free*, because the corrected step absorbs the defect
by taking them small (`StepSmall`) instead of by a balance hypothesis on the constants. -/
def IP4 (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) (α : ℝ) : Fn → Fn → ℝ :=
  Work.Coercivity.HkIPStep c₁'' c₂''
    (Work.Coercivity.HkIPStep c₁' c₂' (Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α)))

/-- The recursion with the coefficients of the *first* step only (the level-`2` inner
product attached to the level-`1` base). -/
def IP2 (c₁ c₂ : ℝ) (α : ℝ) : Fn → Fn → ℝ :=
  Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α)

/-- The recursion iterated twice (the level-`3` inner product). -/
def IP3 (c₁ c₂ c₁' c₂' : ℝ) (α : ℝ) : Fn → Fn → ℝ :=
  Work.Coercivity.HkIPStep c₁' c₂' (IP2 c₁ c₂ α)




end Work.FTS.CoercivityFix.Assembly
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.wtoHQ_of_pointwise_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The `D_z`-bound from pointwise `z^k ∂_z^k`-bounds on the open half-line

The class-dependent input of the port: `Work.FTS.H2.Q.abs_w_DzIter_le_sm` requires smoothness
of the `z`-slice on `(-1,∞)`, which `SmoothOpen` does not provide (it gives `(0,∞)` only); the
open-half-line Stirling expansion `Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open` does. -/

private theorem abs_w_DzIter_le_open {h : ℝ → ℝ → ℝ} {z θ M : ℝ} {i : ℕ}
    (hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi 0))
    (hz : z ∈ Set.Ioi 0) (hM : 0 ≤ M) (hi : i ≤ 4)
    (hbound : ∀ k ≤ i, |Work.Spaces.w z * (z ^ k * Work.Spaces.pzIter k h z θ)| ≤ M) :
    |Work.Spaces.w z * Work.Spaces.DzIter i h z θ| ≤ 100 * M := by
  have h1 : Work.Spaces.w z * Work.Spaces.DzIter i h z θ
      = ∑ k ∈ Finset.range (i + 1),
          (Work.Spaces.scoef i k : ℝ)
            * (Work.Spaces.w z * (z ^ k * Work.Spaces.pzIter k h z θ)) := by
    rw [Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open hsmooth i z hz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [h1]
  calc |∑ k ∈ Finset.range (i + 1),
        (Work.Spaces.scoef i k : ℝ)
          * (Work.Spaces.w z * (z ^ k * Work.Spaces.pzIter k h z θ))|
      ≤ (Work.Spaces.bell i : ℝ) * M :=
        Work.Spaces.abs_sum_scoef_mul_le i M _ (fun k hk => hbound k hk)
    _ ≤ 100 * M :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Work.Spaces.bell_le i hi) hM

/-! ## The pointwise bound for `HkIntegrand` in the open-quadrant class

Verbatim port of `Work.FTS.H2.Q.hkIntegrand_le_Q` from `SmoothQuad` to `SmoothOpen`: the only
class-dependent steps (`hsmoothf`, `hsmoothD` and the two applications of
`abs_w_DzIter_le_sm`) are replaced by their open-half-line counterparts. -/

theorem hkIntegrand_le_QO {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) {Wl : ℝ} (hWl : 0 ≤ Wl)
    (hA : ∀ (m : ℕ), m ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ), θ ∈ Set.Ioo 0 (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ m * Work.Spaces.pzIter m f z θ| ≤ 200000 * Wl)
    (hB : ∀ (i l : ℕ), 1 ≤ i → l + i ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ),
      θ ∈ Set.Ioo 0 (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ l * Work.Spaces.pzIter l (Work.Spaces.DthIter i f) z θ|
        ≤ 200000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) :
    ∀ (z : ℝ), z ∈ Work.Spaces.Iz → ∀ (θ : ℝ), θ ∈ Set.Ioo 0 (π / 2) →
      Work.Spaces.HkIntegrand α 4 f z θ
        ≤ Wl ^ 2 * (1 / (1 + z) ^ 2)
          * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by
  intro z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsin : 0 ≤ Real.sin (2 * θ) := by
    refine Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], ?_⟩
    linarith [hθ.2, Real.pi_pos]
  by_cases hz0 : z = 0
  · subst hz0
    rw [Work.FTS.LocData.HkIntegrand_zero_fst]
    have h1 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hsin _
    have h2 : 0 ≤ (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) :=
      Real.rpow_nonneg hsin _
    have h3 : 0 ≤ (α + Real.sin (2 * θ)) ^ 2 := sq_nonneg _
    have h4 : (0 : ℝ) ≤ 1 / (1 + 0) ^ 2 := by norm_num
    have h5 : (0 : ℝ) ≤ 2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) :=
      add_nonneg (mul_nonneg (by norm_num) h1)
        (mul_nonneg (by norm_num) (mul_nonneg h3 h2))
    exact mul_nonneg (mul_nonneg (sq_nonneg _) h4) h5
  · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    have hz1 : (0 : ℝ) < 1 + z := by linarith
    have hzIoi : z ∈ Set.Ioi (0 : ℝ) := hzpos
    have hwnn : 0 ≤ Work.Spaces.w z :=
      div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hsmoothf : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => f z θ) (Set.Ioi 0) :=
      Work.FTS.EllipticEst.SmoothOpen.curry_z hsm hθ
    have hsmoothD : ∀ (i : ℕ), ContDiffOn ℝ Work.Stability.smoothOrder
        (fun z => Work.Spaces.DthIter i f z θ) (Set.Ioi 0) :=
      fun i => Work.FTS.EllipticEst.SmoothOpen.curry_z
        (Work.FTS.EllipticEst.SmoothOpen.DthIter hsm i) hθ
    -- per-term bound: pure `D_z`-family
    have hZ : ∀ i ≤ 4,
        (Work.Spaces.DzIter i f z θ * (Work.Spaces.w z
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ (20000000 * Wl / (1 + z)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      intro i hi
      have hb : ∀ k ≤ i,
          |Work.Spaces.w z * (z ^ k * Work.Spaces.pzIter k f z θ)| ≤ 200000 * Wl / (1 + z) := by
        intro k hk
        have h1 := hA k (le_trans hk hi) z hzpos θ hθ
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hz1, abs_of_nonneg hwnn,
          abs_of_nonneg (pow_nonneg hzpos.le k)] at h1
        rw [abs_mul, abs_of_nonneg hwnn, abs_mul, abs_of_nonneg (pow_nonneg hzpos.le k),
          le_div_iff₀ hz1]
        linarith [h1]
      have hsq : (Work.Spaces.w z * Work.Spaces.DzIter i f z θ) ^ 2
          ≤ (20000000 * Wl / (1 + z)) ^ 2 := by
        have h2 : |Work.Spaces.w z * Work.Spaces.DzIter i f z θ|
            ≤ 100 * (200000 * Wl / (1 + z)) :=
          abs_w_DzIter_le_open hsmoothf hzIoi (by positivity) hi hb
        have h3 : |Work.Spaces.w z * Work.Spaces.DzIter i f z θ|
            ≤ 20000000 * Wl / (1 + z) := by
          convert h2 using 1; ring
        rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 20000000 * Wl / (1 + z))]
        exact h3
      rw [Work.Elliptic.sq_mul_div_sin hθI]
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hsin _)
    -- angular bookkeeping for the mixed family
    have hsq5 : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
      have hne : α / 5 + α / 5 ≠ 0 := by intro h; have := hα; linarith
      rw [pow_two, Work.Elliptic.sin_two_rpow_mul' hθI hne,
        show α / 5 + α / 5 = 2 * α / 5 by ring]
    have hcomb : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by
      have hne : 2 * α / 5 + -(Work.Spaces.gam α) ≠ 0 := by
        rw [Work.Spaces.gam]; intro h; linarith
      rw [hsq5, Work.Elliptic.sin_two_rpow_mul' hθI hne]
      ring_nf
    -- per-term bound: mixed family
    have hM : ∀ (i j : ℕ), 1 ≤ i → i + j ≤ 4 →
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ (20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              / (1 + z)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      intro i j hi hij
      have hb : ∀ l ≤ j,
          |Work.Spaces.w z * (z ^ l * Work.Spaces.pzIter l (Work.Spaces.DthIter i f) z θ)|
            ≤ 200000 * (Wl * ((α + Real.sin (2 * θ))
                * (Real.sin (2 * θ)) ^ (α / 5))) / (1 + z) := by
        intro l hl
        have h1 := hB i l hi (by omega) z hzpos θ hθ
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hz1, abs_of_nonneg hwnn,
          abs_of_nonneg (pow_nonneg hzpos.le l)] at h1
        rw [abs_mul, abs_of_nonneg hwnn, abs_mul, abs_of_nonneg (pow_nonneg hzpos.le l),
          le_div_iff₀ hz1]
        linarith [h1]
      have hsq : (Work.Spaces.w z * Work.Spaces.mixed j i f z θ) ^ 2
          ≤ (20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              / (1 + z)) ^ 2 := by
        have h2 : |Work.Spaces.w z * Work.Spaces.DzIter j (Work.Spaces.DthIter i f) z θ|
            ≤ 100 * (200000 * (Wl * ((α + Real.sin (2 * θ))
                * (Real.sin (2 * θ)) ^ (α / 5))) / (1 + z)) :=
          abs_w_DzIter_le_open (hsmoothD i) hzIoi (by positivity) (by omega) hb
        have h3 : |Work.Spaces.w z * Work.Spaces.mixed j i f z θ|
            ≤ 20000000 * (Wl * ((α + Real.sin (2 * θ))
                * (Real.sin (2 * θ)) ^ (α / 5))) / (1 + z) := by
          rw [show Work.Spaces.mixed j i f = Work.Spaces.DzIter j (Work.Spaces.DthIter i f)
            from rfl]
          convert h2 using 1; ring
        rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ)
            ≤ 20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                / (1 + z))]
        exact h3
      have hWt : (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
          = (Work.Spaces.w z * Work.Spaces.mixed j i f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        rw [mul_pow, Work.Spaces.bt_Wt_sq α z θ hα hθI]
        ring
      rw [hWt]
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hsin _)
    -- assemble the two sums
    rw [Work.Spaces.HkIntegrand]
    have hZsum : ∑ i ∈ Finset.range (4 + 1),
        (Work.Spaces.DzIter i f z θ * (Work.Spaces.w z
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ (2 * 10 ^ 15) * (Wl ^ 2 * (1 / (1 + z) ^ 2)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      calc ∑ i ∈ Finset.range (4 + 1),
            (Work.Spaces.DzIter i f z θ * (Work.Spaces.w z
              / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ ∑ _i ∈ Finset.range (4 + 1),
              (20000000 * Wl / (1 + z)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
            Finset.sum_le_sum fun i hi => hZ i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        _ = 5 * ((20000000 * Wl / (1 + z)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
        _ = (2 * 10 ^ 15) * (Wl ^ 2 * (1 / (1 + z) ^ 2)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
            rw [div_pow]; ring
    have hMsum : ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
        (if 1 ≤ i ∧ i + j ≤ 4
          then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ (10 ^ 16) * (Wl ^ 2 * (1 / (1 + z) ^ 2)
            * ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by
      set Yv : ℝ := (20000000 * (Wl * ((α + Real.sin (2 * θ))
              * (Real.sin (2 * θ)) ^ (α / 5))) / (1 + z)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) with hYv
      have hYvnn : 0 ≤ Yv := by rw [hYv]; positivity
      calc ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
            (if 1 ≤ i ∧ i + j ≤ 4
              then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ ∑ _i ∈ Finset.range (4 + 1), ∑ _j ∈ Finset.range (4 + 1), Yv := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            by_cases h : 1 ≤ i ∧ i + j ≤ 4
            · rw [if_pos h]; exact hM i j h.1 h.2
            · rw [if_neg h]; exact hYvnn
        _ = 25 * Yv := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
        _ = (10 ^ 16) * (Wl ^ 2 * (1 / (1 + z) ^ 2)
            * ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by
            rw [hYv]
            have hexp :
                (20000000 * (Wl * ((α + Real.sin (2 * θ))
                    * (Real.sin (2 * θ)) ^ (α / 5))) / (1 + z)) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  = (20000000 : ℝ) ^ 2 * Wl ^ 2 * (α + Real.sin (2 * θ)) ^ 2 / (1 + z) ^ 2
                    * (((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
                        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
              rw [div_pow, mul_pow, mul_pow, mul_pow]
              ring
            rw [hexp, hcomb]
            ring
    calc ∑ i ∈ Finset.range (4 + 1),
            (Work.Spaces.DzIter i f z θ * (Work.Spaces.w z
              / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          + ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4
                then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ (2 * 10 ^ 15) * (Wl ^ 2 * (1 / (1 + z) ^ 2)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + (10 ^ 16) * (Wl ^ 2 * (1 / (1 + z) ^ 2)
              * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) :=
          add_le_add hZsum hMsum
      _ = Wl ^ 2 * (1 / (1 + z) ^ 2)
            * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by ring

/-! ## The angular majorant and its vanishing at the endpoints -/

/-- The angular majorant of the `WtoH` estimates. -/
private def angMaj (α θ : ℝ) : ℝ :=
  2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))

/-- The pointwise majorant of the `ℋ⁴`-integrand. -/
private def majr (α W z θ : ℝ) : ℝ := W ^ 2 * (1 / (1 + z) ^ 2) * angMaj α θ

/-- The angular majorant vanishes at the two endpoints `θ = 0`, `θ = π/2`. -/
private theorem angMaj_eq_zero {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hsin : Real.sin (2 * θ) = 0) : angMaj α θ = 0 := by
  have h1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) = 0 := by
    rw [hsin, Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
  have h2 : (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) = 0 := by
    rw [hsin, Real.zero_rpow]
    intro h
    rw [Work.Spaces.gam] at h
    linarith
  simp only [angMaj]
  rw [h1, h2]
  ring

/-- The `ℋ⁴`-integrand vanishes where `sin(2θ) = 0` (both weights degenerate). -/
private theorem HkIntegrand_eq_zero_of_sin_eq_zero {α : ℝ} (hα : 0 < α) (k : ℕ)
    (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hsin : Real.sin (2 * θ) = 0) :
    Work.Spaces.HkIntegrand α k f z θ = 0 := by
  have h1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [hsin, Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
  have h2 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) = 0 := by
    rw [hsin, Real.zero_rpow]
    intro h
    rw [Work.Spaces.gam] at h
    have := hα
    linarith
  have hWt : Work.Spaces.Wt α z θ = 0 := by
    simp only [Work.Spaces.Wt, Work.Spaces.wTheta, h2, mul_zero]
  have hw : ∀ i : ℕ, (Work.Spaces.DzIter i f z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 = 0 := by
    intro i
    rw [h1, div_zero, mul_zero]
    ring
  have hm : ∀ i j : ℕ, (if 1 ≤ i ∧ i + j ≤ k
      then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) = 0 := by
    intro i j
    by_cases hp : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hp, hWt, mul_zero]; ring
    · rw [if_neg hp]
  have hA : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 :=
    Finset.sum_eq_zero fun i _ => hw i
  have hB : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => hm i j
  rw [Work.Spaces.HkIntegrand, hA, hB, add_zero]

/- Port of `Work.FTS.Nonlinear.Pieces.RNP.wtoHQ_of_pointwise` from `SmoothQuad` to the
open-quadrant class `Work.FTS.EllipticEst.SmoothOpen` (the class of the primed interfaces), with
the `ℋ⁴`-honesty (`HkMem α 4 f`) added to the conclusion — that conjunct is what the primed
`N4Extra'` clauses and the `PiecesHk` table consume, and it is exactly what the primed rows
10/11/15/19 (`Submission/Work/FTS/NonlinRows/`) must produce.  The pointwise hypotheses `hA`,
`hB` are verbatim those of the existing (proved) SmoothQuad version. -/
theorem wtoHQ_of_pointwise_open : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (W : ℝ),
    0 < α → α ≤ 1 → 0 ≤ W → Work.FTS.EllipticEst.SmoothOpen f →
    (∀ m : ℕ, m ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |(1 + z) * Work.Spaces.w z * z ^ m * Work.Spaces.pzIter m f z θ| ≤ 200000 * W) →
    (∀ i l : ℕ, 1 ≤ i → l + i ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |(1 + z) * Work.Spaces.w z * z ^ l * Work.Spaces.pzIter l
          (Work.Spaces.DthIter i f) z θ|
        ≤ 200000 * (W * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) →
    Work.Spaces.HkMem α 4 f ∧ Work.FTS.Nonlin.Xn α f ≤ C * W := by
  refine ⟨10 ^ 10, by norm_num, ?_⟩
  intro α f W hα hα1 hW hsm hA hB
  -- the pointwise bound of the `ℋ⁴`-integrand
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.HkIntegrand α 4 f z θ ≤ majr α W z θ :=
    fun z hz θ hθ => by
      have h := hkIntegrand_le_QO (f := f) hα hα1 hsm hW hA hB z hz θ hθ
      simpa only [majr, angMaj, Pi.add_apply] using h
  -- the `ℋ⁴`-membership, by domination
  have hmem : Work.Spaces.HkMem α 4 f := by
    refine Work.FTS.LocData.HkMem_of_majorant α 4
      (M := majr α W) ?_ ?_ ?_ ?_
    · simpa only [Work.FTS.EllipticEst.Q0] using hsm.continuousOn_HkIntegrand α 4
    · -- integrable `θ`-slices of the majorant
      intro z hz
      have hS1 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          Work.Spaces.Iθ :=
        (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
          (by rw [Work.Spaces.eta]; norm_num)
          (by rw [Work.Spaces.eta]; norm_num)).1
      have hS2 : IntegrableOn (fun θ : ℝ => (α + Real.sin (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
        Work.Spaces.integrableOn_angular_weight' hα hα1
      have h := ((hS1.const_mul (2 * 10 ^ 15)).add (hS2.const_mul (10 ^ 16))).const_mul
        (W ^ 2 * (1 / (1 + z) ^ 2))
      simpa only [majr, angMaj, Pi.add_apply, IntegrableOn] using h
    · -- integrability of the `z`-integral of the slices
      have hKval : IntegrableOn (fun z : ℝ => W ^ 2 * (1 / (1 + z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, angMaj α θ)) Work.Spaces.Iz := by
        refine (Work.Elliptic.WtoH_IntZ.1.mul_const (W ^ 2 * (∫ θ in Work.Spaces.Iθ,
          angMaj α θ))).congr ?_
        filter_upwards with z
        ring
      have heq : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, majr α W z θ)
          = fun z : ℝ => W ^ 2 * (1 / (1 + z) ^ 2)
              * (∫ θ in Work.Spaces.Iθ, angMaj α θ) := by
        funext z
        simp only [majr]
        rw [MeasureTheory.integral_const_mul]
      rw [heq]
      exact hKval
    · -- the domination on the *closed* interval
      intro z hz θ hθ
      rcases eq_or_lt_of_le hθ.1 with h0 | hθ0
      · subst h0
        have hsin : Real.sin (2 * (0 : ℝ)) = 0 := by simp
        refine le_of_eq ?_
        rw [HkIntegrand_eq_zero_of_sin_eq_zero hα 4 f hsin, majr,
          angMaj_eq_zero hα hα1 hsin]
        simp only [mul_zero]
      · rcases eq_or_lt_of_le hθ.2 with h2 | hθ2
        · subst h2
          have hsin : Real.sin (2 * (π / 2)) = 0 := by
            rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
          refine le_of_eq ?_
          rw [HkIntegrand_eq_zero_of_sin_eq_zero hα 4 f hsin, majr,
            angMaj_eq_zero hα hα1 hsin]
          simp only [mul_zero]
        · exact hpt z hz θ ⟨hθ0, hθ2⟩
  refine ⟨hmem, ?_⟩
  -- the angular integral
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ W ^ 2 * (1 / (1 + z) ^ 2) * (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) := by
    intro z hz
    have hS1 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ :=
      (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
        (by rw [Work.Spaces.eta]; norm_num)
        (by rw [Work.Spaces.eta]; norm_num)).1
    have hS2 : IntegrableOn (fun θ : ℝ => (α + Real.sin (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
      Work.Spaces.integrableOn_angular_weight' hα hα1
    have hmaj : Integrable (fun θ : ℝ => majr α W z θ)
        (volume.restrict Work.Spaces.Iθ) := by
      have h := ((hS1.const_mul (2 * 10 ^ 15)).add (hS2.const_mul (10 ^ 16))).const_mul
        (W ^ 2 * (1 / (1 + z) ^ 2))
      simpa only [majr, angMaj, Pi.add_apply] using h
    have hIoo : volume.restrict Work.Spaces.Iθ
        = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
      have haeeq : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ :=
        MeasureTheory.Ioo_ae_eq_Icc
      exact Measure.restrict_congr_set haeeq.symm
    have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α 4 f z θ ≤ majr α W z θ := by
      rw [hIoo]
      exact ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hpt z hz θ hθ)
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, majr α W z θ :=
          integral_mono_of_nonneg
            (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ) hmaj hae
      _ = W ^ 2 * (1 / (1 + z) ^ 2) * (∫ θ in Work.Spaces.Iθ, angMaj α θ) := by
          simp only [majr]
          rw [MeasureTheory.integral_const_mul]
      _ ≤ W ^ 2 * (1 / (1 + z) ^ 2) * (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (sq_nonneg _) (div_nonneg (by norm_num) (sq_nonneg _)))
          simpa only [angMaj] using
            Work.Elliptic.WtoH_Angular (α := α) (A := 2 * 10 ^ 15) (B := 10 ^ 16)
              hα hα1 (by norm_num) (by norm_num)
  -- the radial integral
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 f z θ)
      ≤ (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) * 2 * W ^ 2 := by
    set K : ℝ := 2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700 with hK
    have hI : IntegrableOn (fun z : ℝ => W ^ 2 * (1 / (1 + z) ^ 2) * K) Work.Spaces.Iz := by
      refine (Work.Elliptic.WtoH_IntZ.1.mul_const (W ^ 2 * K)).congr ?_
      filter_upwards with z
      ring
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ ∫ z in Work.Spaces.Iz, W ^ 2 * (1 / (1 + z) ^ 2) * K :=
          integral_mono_of_nonneg
            (Eventually.of_forall fun z =>
              integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
            hI (ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hinner z hz))
      _ = (∫ z in Work.Spaces.Iz, 1 / (1 + z) ^ 2) * (W ^ 2 * K) := by
          rw [show (fun z : ℝ => W ^ 2 * (1 / (1 + z) ^ 2) * K)
              = fun z : ℝ => (1 / (1 + z) ^ 2) * (W ^ 2 * K) from by funext z; ring]
          rw [MeasureTheory.integral_mul_const]
      _ ≤ 2 * (W ^ 2 * K) :=
          mul_le_mul_of_nonneg_right Work.Elliptic.WtoH_IntZ.2
            (mul_nonneg (sq_nonneg _) (by rw [hK]; norm_num))
      _ = K * 2 * W ^ 2 := by rw [hK]; ring
  have hSq : Work.Spaces.HkSq α 4 f ≤ 10 ^ 20 * W ^ 2 := by
    rw [Work.Spaces.HkSq]
    have hK2 : (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) * 2 * W ^ 2 ≤ 10 ^ 20 * W ^ 2 := by
      nlinarith [sq_nonneg W]
    linarith [houter]
  have hmain : Real.sqrt (Work.Spaces.HkSq α 4 f) ≤ 10 ^ 10 * W := by
    calc Real.sqrt (Work.Spaces.HkSq α 4 f) ≤ Real.sqrt (10 ^ 20 * W ^ 2) :=
          Real.sqrt_le_sqrt hSq
      _ = 10 ^ 10 * W := by
          rw [show (10 : ℝ) ^ 20 * W ^ 2 = (10 ^ 10 * W) ^ 2 by ring]
          exact Real.sqrt_sq (mul_nonneg (by norm_num) hW)
  simpa only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm] using hmain

end Work.FTS.NonlinRows
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.FstarPkg.DzFstar_W =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.FstarPkg

set_option autoImplicit false

/-! ## The factorization of `D_z F_*` -/

/-- `D_z F_*` separates into the angular factor `α Γ(θ)/c` and the radial factor `Hz` of
`DzHzDefs`: for `z > -1`,

  `D_z F_*(z,θ) = (α/c) · Γ(θ) · H(z)`.

This is `Work.Construction.Dz_Fstar_eq` with the radial factor collected into `Hz`. -/
theorem Dz_Fstar_eq_Hz {α z θ : ℝ} (hα : 0 < α) (hz : -1 < z) :
    Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      = (α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * Hz z) := by
  rw [Work.Construction.Dz_Fstar_eq hα hz, Hz]
  ring

/-! ## The universal constant -/

/-- The universal (α-independent) constant multiplying `α` in the bound of `DzFstar_W`: the
sum over the slots of `𝒲^{4,∞}` of the radial bound `HB` times the angular coefficient
`tBound (j-1) 0`. -/
noncomputable def KBdz : ℝ :=
  (∑ k ∈ Finset.range 5, HB k)
    + ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
        (if 1 ≤ j ∧ k + j ≤ 4 then HB k * Work.Spaces.tBound (j - 1) 0 else 0)

lemma KBdz_nonneg : 0 ≤ KBdz := by
  rw [KBdz]
  refine add_nonneg (Finset.sum_nonneg fun k _ => HB_nonneg k)
    (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_)
  split_ifs with h
  · exact mul_nonneg (HB_nonneg k) (Work.Spaces.tBound_nonneg _ _)
  · norm_num

/-! ## The estimate -/

theorem DzFstar_W :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.WlInfMem α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
      Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ C * α := by
  refine ⟨10 * KBdz + 1, by linarith [KBdz_nonneg], fun α hα hα1 => ?_⟩
  -- `c(α) ≥ 1/10`, hence `|α/c| ≤ 10α`.
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hcoef : |α / Work.Spaces.c α| ≤ 10 * α := by
    rw [abs_of_nonneg (div_nonneg hα.le hcpos.le), div_le_iff₀ hcpos]
    nlinarith
  -- `WlInf` (and `WlInfMem`) only see `z > -1`, where `D_z F_*` is the product
  -- `(α/c) · Γ ⊗ Hz`.
  have hcongr := WlInf_congr (f := Work.Spaces.Dz (Work.Construction.Fstar α))
    (g := fun z θ => (α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * Hz z))
    (fun z hz θ => Dz_Fstar_eq_Hz hα hz) α 4
  -- the `Γ ⊗ Hz` estimate, with `B = HB` from the radial bound
  obtain ⟨hmem, hbound⟩ := WlInf_Gamma_radial (l := 4) (H := Hz) (B := HB)
    (D := α / Work.Spaces.c α) (α := α) hα hα1 (fun k _ z hz => Hz_deriv_bound k z hz)
  refine ⟨hcongr.2.mpr hmem, ?_⟩
  rw [hcongr.1]
  calc Work.Spaces.WlInf α 4 (fun z θ => (α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * Hz z))
      ≤ |α / Work.Spaces.c α| * KBdz := hbound
    _ ≤ 10 * α * KBdz := mul_le_mul_of_nonneg_right hcoef KBdz_nonneg
    _ = 10 * KBdz * α := by ring
    _ ≤ (10 * KBdz + 1) * α := by nlinarith [hα, KBdz_nonneg]

end Work.FTS.Nonlinear.FstarPkg
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.PvecMeas =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

open Work.FTS.Nonlin Work.Construction Work.Spaces

/-! ## Closure of a.e. strong measurability under the operations occurring in `pv` -/

theorem aesm_congr {F G : ℝ → ℝ → ℝ}
    (hF : AEStronglyMeasurable (Function.uncurry F) QdMeas)
    (hFG : ∀ z θ, F z θ = G z θ) :
    AEStronglyMeasurable (Function.uncurry G) QdMeas :=
  hF.congr (Filter.Eventually.of_forall fun p => hFG p.1 p.2)

theorem aesm_mul {f h : ℝ → ℝ → ℝ}
    (hf : AEStronglyMeasurable (Function.uncurry f) QdMeas)
    (hh : AEStronglyMeasurable (Function.uncurry h) QdMeas) :
    AEStronglyMeasurable (Function.uncurry (fun z θ => f z θ * h z θ)) QdMeas :=
  continuous_mul.comp_aestronglyMeasurable₂ hf hh

theorem aesm_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : AEStronglyMeasurable (Function.uncurry f) QdMeas) :
    AEStronglyMeasurable (Function.uncurry (fun z θ => c * f z θ)) QdMeas :=
  (continuous_const.mul continuous_id).comp_aestronglyMeasurable hf

theorem aesm_neg {f : ℝ → ℝ → ℝ}
    (hf : AEStronglyMeasurable (Function.uncurry f) QdMeas) :
    AEStronglyMeasurable (Function.uncurry (fun z θ => -f z θ)) QdMeas :=
  continuous_neg.comp_aestronglyMeasurable hf

theorem continuous_s2_snd : Continuous fun p : ℝ × ℝ => Work.Construction.s2 p.2 := by
  simp only [Work.Construction.s2]; fun_prop

theorem continuous_sinsq_snd : Continuous fun p : ℝ × ℝ => (Real.sin p.2) ^ 2 := by
  fun_prop

theorem aesm_s2_mul {f : ℝ → ℝ → ℝ}
    (hf : AEStronglyMeasurable (Function.uncurry f) QdMeas) :
    AEStronglyMeasurable (Function.uncurry (fun z θ => Work.Construction.s2 θ * f z θ)) QdMeas :=
  continuous_mul.comp_aestronglyMeasurable₂ continuous_s2_snd.aestronglyMeasurable hf

theorem aesm_sinsq_mul {f : ℝ → ℝ → ℝ}
    (hf : AEStronglyMeasurable (Function.uncurry f) QdMeas) :
    AEStronglyMeasurable (Function.uncurry (fun z θ => (Real.sin θ) ^ 2 * f z θ)) QdMeas :=
  continuous_mul.comp_aestronglyMeasurable₂ continuous_sinsq_snd.aestronglyMeasurable hf

/-! ## The profile `F_*` in terms of `c α = ∫_θ Γ K`

All the facts about `F_*` that the measurability argument needs are elementary *given*
`c α ≠ 0`; when `c α = 0` the profile `F_* = α (Γ/c) (2z/(1+z)²)` collapses to `0`, and
`L₁₂` and `(·,K)` of the zero function vanish.  Splitting on `c α = 0` avoids the extra
hypotheses `0 < α`, `α ≤ 1` of the library lemmas `L12_Fstar_eq`/`FK_Fstar` (which are only
used there to produce `c α ≠ 0`). -/

theorem Fstar_eq_zero_of_c_eq_zero {α : ℝ} (h : Work.Spaces.c α = 0) :
    ∀ z θ, Work.Construction.Fstar α z θ = 0 := by
  intro z θ
  simp [Work.Construction.Fstar, h]

theorem L12dens_Fstar_of_c_ne {α : ℝ} (hc : Work.Spaces.c α ≠ 0) (s : ℝ) :
    Work.Construction.L12dens (Work.Construction.Fstar α) s = α * (Work.FM.Fstar s / s) := by
  rw [Work.Construction.L12dens, Work.FM.L12dens]
  have hpoint : ∀ θ : ℝ, Work.Spaces.K θ * Work.Construction.Fstar α s θ / s
      = (α * (Work.Spaces.Gam α θ * Work.Spaces.K θ) / Work.Spaces.c α)
          * (Work.FM.Fstar s / s) := by
    intro θ
    simp only [Work.Construction.Fstar]
    ring
  rw [MeasureTheory.setIntegral_congr_fun (s := Set.Icc 0 (Real.pi / 2)) measurableSet_Icc
        (fun θ _ => hpoint θ)]
  rw [MeasureTheory.integral_mul_const]
  have hcint : (∫ θ in Set.Icc 0 (Real.pi / 2),
        α * (Work.Spaces.Gam α θ * Work.Spaces.K θ) / Work.Spaces.c α) = α := by
    rw [MeasureTheory.integral_div, MeasureTheory.integral_const_mul]
    have hval : (∫ θ in Set.Icc 0 (Real.pi / 2),
        Work.Spaces.Gam α θ * Work.Spaces.K θ) = Work.Spaces.c α := rfl
    rw [hval, mul_div_assoc, div_self hc, mul_one]
  rw [hcint]

theorem L12_zero (z : ℝ) : Work.Construction.L12 (fun _ _ => (0 : ℝ)) z = 0 := by
  rw [Work.Construction.L12, Work.FM.L12]
  have h0 : ∀ s : ℝ, Work.FM.L12dens Work.Spaces.K (fun _ _ => (0 : ℝ)) s = 0 := by
    intro s
    simp [Work.FM.L12dens]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s _ => h0 s)]
  simp

theorem L12_Fstar_eq_of_c_ne {α : ℝ} (hc : Work.Spaces.c α ≠ 0) {z : ℝ} (hz : -1 < z) :
    Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) := by
  rw [Work.Construction.L12, Work.FM.L12]
  rw [MeasureTheory.setIntegral_congr_fun (s := Set.Ioi z) measurableSet_Ioi
        (fun s _ => show Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α) s
            = α * (Work.FM.Fstar s / s) from L12dens_Fstar_of_c_ne hc s)]
  rw [MeasureTheory.integral_const_mul,
    Work.FTS.Nonlinear.FstarPkg.integral_Ioi_Fstar_div_of_gt_neg_one z hz]
  ring


/-! ## `Θ α (F_*)` is `C^∞` on the open quadrant, for every `α` -/

theorem smoothQuad_Theta_Fstar_all (α : ℝ) :
    Work.FTS.LocData.SmoothQuad (Work.Construction.Theta α (Work.Construction.Fstar α)) := by
  by_cases hα : α = 0
  · have hfun : Work.Construction.Theta α (Work.Construction.Fstar α) = fun _ _ => (0 : ℝ) := by
      funext z θ
      simp [Work.Construction.Theta, hα]
    rw [hfun]
    exact contDiffOn_const
  · by_cases hc : Work.Spaces.c α = 0
    · have hF : Work.Construction.Fstar α = fun _ _ => (0 : ℝ) := by
        funext z θ
        exact Fstar_eq_zero_of_c_eq_zero hc z θ
      have hfun : Work.Construction.Theta α (Work.Construction.Fstar α) = fun _ _ => (0 : ℝ) := by
        funext z θ
        simp only [Work.Construction.Theta, hF, Work.Construction.s2]
        rw [L12_zero z]
        ring
      rw [hfun]
      exact contDiffOn_const
    · have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun p : ℝ × ℝ => Real.sin (2 * p.2) / (2 * (1 + p.1))) Work.Spaces.quadU := by
        have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
            (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.Spaces.quadU :=
          (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
        have hden : ContDiffOn ℝ Work.Stability.smoothOrder
            (fun p : ℝ × ℝ => 2 * (1 + p.1)) Work.Spaces.quadU :=
          contDiffOn_const.mul (contDiffOn_const.add contDiffOn_fst)
        have hne : ∀ p ∈ Work.Spaces.quadU, 2 * (1 + p.1) ≠ 0 := by
          intro p hp
          have hp1 : (0 : ℝ) < 1 + p.1 := by
            have := Set.mem_Ioi.mp hp.1; linarith
          positivity
        exact hnum.div hden hne
      refine hsmooth.congr ?_
      intro p hp
      obtain ⟨z, θ⟩ := p
      have hz : -1 < z := Set.mem_Ioi.mp hp.1
      simp only [Function.uncurry, Work.Construction.Theta, Work.Construction.s2]
      rw [L12_Fstar_eq_of_c_ne hc hz]
      field_simp
      ring

/-! ## The measurability of the atoms -/

theorem aesm_g_ops {α : ℝ} {g : ℝ → ℝ → ℝ} (hgal : Work.FTS.Nonlin.GalClass α g) :
    AEStronglyMeasurable (Function.uncurry g) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry (Work.Spaces.pth g)) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry (Work.Spaces.Dz g)) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry (Work.Spaces.Dth g)) QdMeas := by
  have hsm : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hio := Work.Spaces.isOpen_quadU
  exact ⟨aesm_of_smoothQuad hsm,
    aesm_of_smoothQuad (Work.FTS.LocData.contDiffOn_pth hio hsm),
    aesm_of_smoothQuad (Work.FTS.LocData.contDiffOn_Dz hio hsm),
    aesm_of_smoothQuad (Work.FTS.LocData.contDiffOn_Dth hio hsm)⟩

theorem aesm_F_ops (α : ℝ) :
    AEStronglyMeasurable (Function.uncurry (Work.Construction.Fstar α)) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry (Work.Spaces.pth (Work.Construction.Fstar α)))
      QdMeas ∧
    AEStronglyMeasurable (Function.uncurry (Work.Spaces.Dz (Work.Construction.Fstar α)))
      QdMeas := by
  have hsm : Work.FTS.LocData.SmoothQuad (Work.Construction.Fstar α) :=
    Work.FTS.LocData.SmoothQuad_Fstar α
  have hio := Work.Spaces.isOpen_quadU
  exact ⟨aesm_of_smoothQuad hsm,
    aesm_of_smoothQuad (Work.FTS.LocData.contDiffOn_pth hio hsm),
    aesm_of_smoothQuad (Work.FTS.LocData.contDiffOn_Dz hio hsm)⟩

theorem aesm_Tg_ops {α Ce : ℝ} {g Φg : Work.FTS.Galerkin.Fn}
    (hell : Work.FTS.Nonlin.EllPkgG α Ce g Φg) :
    AEStronglyMeasurable (Function.uncurry (Work.Construction.Rop α
        (Work.FTS.Nonlin.PhiTg α g Φg))) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry (Work.Construction.Uop α
        (Work.FTS.Nonlin.PhiTg α g Φg))) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry (Work.Construction.Vop
        (Work.FTS.Nonlin.PhiTg α g Φg))) QdMeas :=
  ⟨aesm_of_smoothQuad hell.R.1.1,
    aesm_Uop_of_div (aesm_of_smoothQuad hell.U.1.1),
    aesm_of_smoothQuad hell.V.1.1⟩

theorem aesm_FK_ops {α : ℝ} {g : ℝ → ℝ → ℝ} (hgal : Work.FTS.Nonlin.GalClass α g) :
    AEStronglyMeasurable (Function.uncurry (fun z θ => Work.Construction.FK g z)) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry (fun z θ =>
      Work.Construction.FK (Work.Construction.Fstar α) z)) QdMeas :=
  ⟨aesm_FK (aesm_of_smoothQuad hgal.reg.1),
    aesm_FK (aesm_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α))⟩

theorem PvecMeas {α Ce Cs : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn}
    (hgal : Work.FTS.Nonlin.GalClass α g) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (hell : Work.FTS.Nonlin.EllPkgG α Ce g Φg) :
    (∀ k : Fin 20, AEMeasurable (Function.uncurry (fun r θ =>
        Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k r θ))
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) ∧
    (∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), ∀ k : Fin 20, AEMeasurable
        (fun θ : ℝ => ENNReal.ofReal |Work.Spaces.K θ
          * Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k r θ|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    (∀ k : Fin 20, AEMeasurable
        (fun r : ℝ => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ
          * Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k r θ|)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) := by
  obtain ⟨hg, hpthg, hDzg, hDthg⟩ := aesm_g_ops hgal
  obtain ⟨hF, hpthF, hDzF⟩ := aesm_F_ops α
  obtain ⟨hRopTg, hUopTg, hVopTg⟩ := aesm_Tg_ops hell
  obtain ⟨hFKg, hFKF⟩ := aesm_FK_ops hgal
  obtain ⟨hRopTs, hUopTs, hVopTs⟩ := aesm_star_ops hs.smooth (smoothQuad_Theta_Fstar_all α)
  -- the twenty pieces of `pv`
  have hpiece : ∀ k : Fin 20, AEStronglyMeasurable (Function.uncurry (fun r θ =>
      Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k r θ)) QdMeas := by
    intro k
    fin_cases k
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTg α g Φg) z θ * g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTg hg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTg α g Φg) z θ * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTg hF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTs α Φs) z θ * g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTs hg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTs α Φs) z θ * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTs hF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTg α g Φg) z θ * pth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTg hpthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTg α g Φg) z θ * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTg hpthF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTs α Φs) z θ * pth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTs hpthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTs α Φs) z θ * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTs hpthF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTg α g Φg) z θ * Dz g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTg hDzg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTg α g Φg) z θ * Dz (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTg hDzF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTs α Φs) z θ * Dz g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTs hDzg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTs α Φs) z θ * Dz (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTs hDzF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * FK g z * Dth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_mul hFKg hDthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * s2 θ * FK g z * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_s2_mul (aesm_mul hFKg hpthF)))
        (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * FK (Fstar α) z * Dth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_mul hFKF hDthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * s2 θ * FK (Fstar α) z * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_s2_mul (aesm_mul hFKF hpthF)))
        (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK g z * g z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKg hg))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK g z * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKg hF))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK (Fstar α) z * g z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKF hg))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK (Fstar α) z * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKF hF))) (fun z θ => ?_)
      ring
  -- the `ENNReal`-valued versions, with the angular weight `K`
  have hENN : ∀ k : Fin 20, AEStronglyMeasurable (Function.uncurry (fun r θ =>
      ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlinear.Pieces.rl1Tools.pv
        α g Φs Φg k r θ|)) QdMeas := by
    intro k
    have hKcont : Continuous fun p : ℝ × ℝ => Work.Spaces.K p.2 := by
      simp only [Work.Spaces.K]; fun_prop
    have hK : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.K p.2) QdMeas :=
      hKcont.aestronglyMeasurable
    have hpair : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (Work.Spaces.K p.2, Function.uncurry (fun r θ =>
          Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k r θ) p)) QdMeas :=
      hK.prodMk (hpiece k)
    have hcomp : Continuous (fun q : ℝ × ℝ => ENNReal.ofReal |q.1 * q.2|) :=
      ENNReal.continuous_ofReal.comp
        (continuous_abs.comp (continuous_fst.mul continuous_snd))
    exact hcomp.comp_aestronglyMeasurable hpair
  refine ⟨fun k => (hpiece k).aemeasurable, ?_, ?_⟩
  · filter_upwards [eventually_all.2 fun k => (hENN k).prodMk_left] with r hr
    intro k
    exact (hr k).aemeasurable
  · intro k
    exact (hENN k).aemeasurable.lintegral_prod_right

end Work.FTS.Nonlinear.Pieces.rl1Tools
end
end
-- ===== merged: Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.TransportS.SlotT2

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Elementary facts about the weights and the intervals -/

theorem supOpen_w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem supOpen_one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith

theorem supOpen_w_sq_ne_zero {z : ℝ} (hz : 0 < z) : (Work.Spaces.w z) ^ 2 ≠ 0 := by
  have h : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith : (1 : ℝ) + z ≠ 0))
      (pow_ne_zero 2 (ne_of_gt hz))
  exact pow_ne_zero 2 h

/-- `Iθ = [0,π/2]` differs from the open interval by the null set `{0, π/2}`. -/
theorem supOpen_Iθ_ae_eq :
    (Work.Spaces.Iθ : Set ℝ) =ᵐ[MeasureTheory.volume] Set.Ioo 0 (Real.pi / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
    (b := Real.pi / 2)).symm

theorem supOpen_restrict_Iθ : MeasureTheory.volume.restrict Work.Spaces.Iθ
    = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  MeasureTheory.Measure.restrict_congr_set supOpen_Iθ_ae_eq

/-- `Iz = [0,∞)` differs from the open half-line by the null set `{0}`. -/
theorem supOpen_Iz_ae_eq : (Work.Spaces.Iz : Set ℝ) =ᵐ[MeasureTheory.volume] Set.Ioi 0 :=
  (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ))).symm

theorem supOpen_restrict_Iz : MeasureTheory.volume.restrict Work.Spaces.Iz
    = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
  MeasureTheory.Measure.restrict_congr_set supOpen_Iz_ae_eq

/-! ## The open-quadrant commutation, and the weight identity of the `θ`-slot -/

/-- On the open quadrant, `D_z^bD_θf = sin(2θ)·∂_θ(D_z^b f)`: the `D_θ`-iterate of a
`D_z`-iterate commutes across, for `C^∞` data on the open quadrant. -/
theorem supOpen_mixed_eq_sin_pth {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (b : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.mixed b 1 f z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter b f) z θ := by
  have hy : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have h1 : Work.Spaces.mixed b 1 f z θ
      = Work.Spaces.DthIter 1 (Work.Spaces.DzIter b f) z θ :=
    ((Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hF) b 1) hy).symm
  rw [h1]
  rfl

/-- The weight identity behind the angular Hardy inequality, on the open quadrant:
`(∂_θD_z^b f)² w² sin(2θ)^{2-γ} = (D_z^bD_θf · W)²`. -/
theorem supOpen_pth_weight {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hα : 0 < α) (hα1 : α ≤ 1) (b : ℕ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      = (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 :=
  Work.Spaces.bt_mixed_weight_gen α z θ hα hα1 ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) (Work.Spaces.mixed b 1 f z θ)
    (supOpen_mixed_eq_sin_pth hF b hz hθ)

/-! ## Integrability of the angular slices -/

/-- The pointwise domination of `(D_z^b f)²` by the `ℋ⁴`-integrand on the open quadrant,
using that the light weight `w/σ^{η/2}` exceeds `1` there. -/
theorem supOpen_sq_le_Hk {α : ℝ} {f : ℝ → ℝ → ℝ} {b : ℕ} (hb4 : b ≤ 4) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.DzIter b f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hspos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsin _
  have hsle : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hsin) (Real.sin_le_one _) (by norm_num [Work.Spaces.eta])
  have hw1 : 1 ≤ Work.Spaces.w z := supOpen_one_le_w hz
  have hL : 1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
    rw [le_div_iff₀ hspos]
    linarith
  calc (Work.Spaces.DzIter b f z θ) ^ 2
      ≤ (Work.Spaces.DzIter b f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [mul_pow]
        exact le_mul_of_one_le_right (sq_nonneg _) (by nlinarith)
    _ ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ b hb4

/-- For `z > 0` the angular slice `θ ↦ (D_z^bf z θ)²` is integrable on `Iθ`, by domination
by the `ℋ⁴`-integrand. -/
theorem supOpen_integrableOn_sq {α : ℝ} {f : ℝ → ℝ → ℝ} {b : ℕ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) (hb4 : b ≤ 4)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter b f z θ) ^ 2) Work.Spaces.Iθ := by
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith
  have hkey : MeasureTheory.Integrable (fun θ => (Work.Spaces.DzIter b f z θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    refine MeasureTheory.Integrable.mono'
      ((hmem.1 z hzIz).mono_set Set.Ioo_subset_Icc_self)
      ((((hF.DzIter b).curry_θ hz).continuousOn.aestronglyMeasurable
        measurableSet_Ioo).pow 2) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact supOpen_sq_le_Hk hb4 hz hθ
  show MeasureTheory.Integrable (fun θ => (Work.Spaces.DzIter b f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  rw [supOpen_restrict_Iθ]
  exact hkey

/-- For `z > 0` the weighted angular slice `(∂_θD_z^bf z ·)² σ^{2-γ}` is integrable on
`Iθ`: after multiplying by `(w z)²` it is the mixed slot `(mixed b 1 f · W)²`, which is
dominated by the `ℋ⁴`-integrand. -/
theorem supOpen_integrableOn_pth_weight {α : ℝ} {f : ℝ → ℝ → ℝ} {b : ℕ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hα : 0 < α) (hα1 : α ≤ 1) (hb3 : b ≤ 3) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith
  have hw2 : (Work.Spaces.w z) ^ 2 ≠ 0 := supOpen_w_sq_ne_zero hz
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hderiv_cont : ContinuousOn
      (fun θ => deriv (fun θ' => Work.Spaces.DzIter b f z θ') θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (((hF.DzIter b).curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])).continuousOn_deriv_of_isOpen
      isOpen_Ioo le_rfl
  have hsincont : ContinuousOn (fun θ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (hsinpos θ hθ)))
  have hkey : MeasureTheory.Integrable
      (fun θ => (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    refine MeasureTheory.Integrable.mono'
      (((hmem.1 z hzIz).mono_set Set.Ioo_subset_Icc_self).const_mul
        ((Work.Spaces.w z) ^ 2)⁻¹) ?_ ?_
    · have hcont : ContinuousOn
          (fun θ => (deriv (fun θ' => Work.Spaces.DzIter b f z θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        (hderiv_cont.pow 2).mul hsincont
      exact hcont.aestronglyMeasurable measurableSet_Ioo
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_of_nonneg
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (hsinpos θ hθ)) _))]
      calc (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          = ((Work.Spaces.w z) ^ 2)⁻¹
              * (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
            rw [← supOpen_pth_weight hF hα hα1 b hz hθ]
            rw [show ((Work.Spaces.w z) ^ 2)⁻¹
                  * ((Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
                      * (Work.Spaces.w z) ^ 2
                      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
                = ((Work.Spaces.w z) ^ 2)⁻¹ * ((Work.Spaces.w z) ^ 2)
                    * ((Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
                        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) from by ring]
            rw [inv_mul_cancel₀ hw2, one_mul]
        _ ≤ ((Work.Spaces.w z) ^ 2)⁻¹ * Work.Spaces.HkIntegrand α 4 f z θ :=
            mul_le_mul_of_nonneg_left
              (Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ 1 b le_rfl (by omega))
              (inv_nonneg.mpr (sq_nonneg _))
  show MeasureTheory.Integrable
      (fun θ => (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  rw [supOpen_restrict_Iθ]
  exact hkey

/-! ## The slicewise bound and the a.e. sup bound -/

/-- The two-term majorant of the angular slice estimate at the fixed radius `z`. -/
def supOpenBfun (α : ℝ) (f : ℝ → ℝ → ℝ) (b : ℕ) (z : ℝ) : ℝ :=
  (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
    + (200 / (Work.Spaces.gam α - 1))
        * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)

/-- The open-interval Agmon inequality `Work.H2.T1Q.SliceSupOpen` at the slice
`θ ↦ D_z^b f z θ`. -/
theorem supOpen_slice_bound {α : ℝ} {f : ℝ → ℝ → ℝ} {b : ℕ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hα : 0 < α) (hα1 : α ≤ 1) (hb3 : b ≤ 3) {z : ℝ} (hz : 0 < z) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.DzIter b f z θ) ^ 2 ≤ supOpenBfun α f b z := by
  have hb4 : b ≤ 4 := by omega
  have hslice : ContDiffOn ℝ 1 (fun θ => Work.Spaces.DzIter b f z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    ((hF.DzIter b).curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])
  have hint2 := supOpen_integrableOn_sq hF hmem hb4 hz
  have hintp := supOpen_integrableOn_pth_weight hF hmem hα hα1 hb3 hz
  intro θ hθ
  exact Work.H2.T1Q.SliceSupOpen α (fun θ' => Work.Spaces.DzIter b f z θ') hα hα1 hslice
    hint2 hintp θ hθ

/-- The angular slice of `D_z^bf` is bounded above, the input of the countability argument
for the measurability of the interior supremum. -/
theorem supOpen_slice_bddAbove {α : ℝ} {f : ℝ → ℝ → ℝ} {b : ℕ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hα : 0 < α) (hα1 : α ≤ 1) (hb3 : b ≤ 3) {z : ℝ} (hz : 0 < z) :
    BddAbove {y : ℝ | ∃ θ ∈ Set.Ioo 0 (Real.pi / 2), y = |Work.Spaces.DzIter b f z θ|} :=
  ⟨Real.sqrt (supOpenBfun α f b z), fun y hy => by
    obtain ⟨θ, hθ, rfl⟩ := hy
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (supOpen_slice_bound hF hmem hα hα1 hb3 hz θ hθ)⟩

/-- The `D_z`-slot: multiplying the angular slice integral of `(D_z^bf)²` by `w(z)²` costs
only the light weight, hence is dominated by the `ℋ⁴`-integrand. -/
theorem supOpen_block_z {α : ℝ} {f : ℝ → ℝ → ℝ} {b : ℕ}
    (hmem : Work.Spaces.HkMem α 4 f) (hb4 : b ≤ 4) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2) * (Work.Spaces.w z) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ := by
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith
  have hwz_nn : 0 ≤ Work.Spaces.w z := supOpen_w_nonneg z
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have e1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2) * (Work.Spaces.w z) ^ 2
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ * Work.Spaces.w z) ^ 2 := by
    rw [mul_comm, ← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  rw [e1]
  refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun θ => sq_nonneg _))
    (hmem.1 z hzIz) ?_
  rw [supOpen_restrict_Iθ]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  have hsinθ : 0 < Real.sin (2 * θ) := hsinpos θ hθ
  have hspos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsinθ _
  have hsle : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hsinθ) (Real.sin_le_one _) (by norm_num [Work.Spaces.eta])
  have hL : Work.Spaces.w z ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
    rw [le_div_iff₀ hspos]
    nlinarith [hwz_nn, hsle]
  have hstep : (Work.Spaces.DzIter b f z θ * Work.Spaces.w z) ^ 2
      ≤ (Work.Spaces.DzIter b f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [sq_le_sq, abs_mul, abs_mul, abs_of_nonneg hwz_nn,
      abs_of_nonneg (div_nonneg hwz_nn (le_of_lt hspos))]
    exact mul_le_mul_of_nonneg_left hL (abs_nonneg _)
  exact hstep.trans (Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ b hb4)

/-- The mixed block: `∫_θ (∂_θD_z^bf)² σ^{2-γ} · w(z)²` is exactly the angular integral of
the `(D_z^bD_θf · W)²` slot, dominated by the `ℋ⁴`-integrand. -/
theorem supOpen_block_mixed {α : ℝ} {f : ℝ → ℝ → ℝ} {b : ℕ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hα : 0 < α) (hα1 : α ≤ 1) (hb3 : b ≤ 3) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w z) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ := by
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith
  have e2 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w z) ^ 2
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    rw [mul_comm, ← MeasureTheory.integral_const_mul]
    have h1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
        * ((Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))
        = ∫ θ in Set.Ioo 0 (Real.pi / 2), (Work.Spaces.w z) ^ 2
            * ((Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) :=
      MeasureTheory.setIntegral_congr_set supOpen_Iθ_ae_eq
    have h2 : (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        = ∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 :=
      MeasureTheory.setIntegral_congr_set supOpen_Iθ_ae_eq
    rw [h1, h2]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
    rw [← supOpen_pth_weight hF hα hα1 b hz hθ]
    ring
  rw [e2]
  refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun θ => sq_nonneg _))
    (hmem.1 z hzIz) (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ _ => Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ 1 b le_rfl (by omega)))

/-- **The a.e. pointwise bound.**  For almost every `z ∈ (0,∞)` the squared weighted angular
supremum of `D_z^bf` is dominated by `(4/π + 200/(γ-1))·∫_θ HkIntegrand α 4 f z θ`. -/
theorem supOpen_ae_sup_bound {α : ℝ} {f : ℝ → ℝ → ℝ} {b : ℕ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hα : 0 < α) (hα1 : α ≤ 1) (hb3 : b ≤ 3) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
        ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
            * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ := by
  have hb4 : b ≤ 4 := by omega
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hzpos
  have hzIz : z ∈ Work.Spaces.Iz := by
    rw [Work.Spaces.Iz, Set.mem_Ici]; exact le_of_lt hzpos
  have hwz_nn : 0 ≤ Work.Spaces.w z := supOpen_w_nonneg z
  have hγpos : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hsinθ_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) :=
    fun θ hθ => Work.Spaces.bt_sin_nonneg hθ
  have hBnn : 0 ≤ supOpenBfun α f b z := by
    rw [supOpenBfun]
    refine add_nonneg (mul_nonneg (div_nonneg (by norm_num) Real.pi_pos.le)
      (MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _))) ?_
    refine mul_nonneg (div_nonneg (by norm_num) (le_of_lt hγpos))
      (MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsinθ_nn θ hθ) _)))
  have hsup_nn : 0 ≤ Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z :=
    le_trans (abs_nonneg _)
      (le_csSup (supOpen_slice_bddAbove hF hmem hα hα1 hb3 hzpos)
        ⟨π / 4, ⟨by positivity, by linarith [Real.pi_pos]⟩, rfl⟩)
  have hsup_le : Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z
      ≤ Real.sqrt (supOpenBfun α f b z) :=
    Work.FTS.H2.supAbsThO_le (fun θ hθ => by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (supOpen_slice_bound hF hmem hα hα1 hb3 hzpos θ hθ))
  have hstep1 : (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
      ≤ supOpenBfun α f b z * (Work.Spaces.w z) ^ 2 := by
    have h1 : Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z
        ≤ Real.sqrt (supOpenBfun α f b z) * Work.Spaces.w z :=
      mul_le_mul_of_nonneg_right hsup_le hwz_nn
    have h0 : 0 ≤ Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z :=
      mul_nonneg hsup_nn hwz_nn
    calc (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
        ≤ (Real.sqrt (supOpenBfun α f b z) * Work.Spaces.w z) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = supOpenBfun α f b z * (Work.Spaces.w z) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hBnn]
  calc (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
      ≤ supOpenBfun α f b z * (Work.Spaces.w z) ^ 2 := hstep1
    _ = (4 / Real.pi) * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
            * (Work.Spaces.w z) ^ 2)
          + (200 / (Work.Spaces.gam α - 1)) * ((∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w z) ^ 2) := by
        rw [supOpenBfun]; ring
    _ ≤ (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
          + (200 / (Work.Spaces.gam α - 1))
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (supOpen_block_z hmem hb4 hzpos) (by positivity))
          (mul_le_mul_of_nonneg_left
            (supOpen_block_mixed hF hmem hα hα1 hb3 hzpos) (by positivity))
    _ = (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) := by ring

/-- A version of `Work.H2.T1Q.SupAbsThOAesm` whose continuity hypothesis is only required
almost everywhere in `z` (the argument is pointwise a.e. in any case). -/
theorem supOpen_supAbsThO_aemeasurable {u : ℝ → ℝ → ℝ}
    (hcont : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ContinuousOn (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)))
    (hmeas : ∀ q : ℚ, ((q : ℝ) ∈ Set.Ioo 0 (Real.pi / 2)) →
      AEMeasurable (fun z => u z (q : ℝ)) (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hbdd : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      BddAbove {y : ℝ | ∃ θ ∈ Set.Ioo 0 (Real.pi / 2), y = |u z θ|}) :
    AEMeasurable (fun z => Work.FTS.H2.supAbsThO u z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  refine (Work.H2.T1Q.supRatAbs_aemeasurable hmeas).congr ?_
  filter_upwards [hcont, hbdd] with z hz hbddz
  exact (Work.H2.T1Q.supAbsThO_eq_supRatAbs hz hbddz).symm

/-- **Angular sup bound of Elgindi's Lemma `infinity_separated`, integrated in the radial
variable, in the open class.**  For `f` of class `C^∞` on the *open* quadrant with
`HkMem α 4 f` and `b ≤ 3`,

  `∫_z (sup_{θ ∈ (0,π/2)} |D_z^b f(z,θ)| · w(z))² dz ≤ C/(γ-1) · HkSq α 4 f`,

with `C` a universal constant.  The sup is taken over the **open** angular interval (for
`SmoothOpen` data the values at `θ = 0, π/2` are not controlled), and it is this function
which has to be proved integrable.

Route (adapt the *proved* closed-quadrant `Work.FTS.H2.SupThetaInt`, and the proved
`Work.H2.T1Q.SupThetaIntQ` which does exactly this for the *stronger* class `SmoothQuad` with
`supAbsThO`, defined in `Transport1Aux`/`H2.Defs`):
* at each fixed `z`, the angular Agmon inequality with a mean-value base point — for the
  open class this is `Work.FTS.H2.slice_sup_sq_le` **generalised to `ContDiffOn ℝ 1 u
  (Ioo 0 (π/2))` with the base point chosen in `(0,π/2)`** (`exists_le_setAverage` over the
  open interval) — gives
  `sup_θ|D_z^b f(z,θ)|² ≤ (4/π)∫_{Ioo}(D_z^b f(z,·))² + (200/(γ-1))∫_θ(∂_θD_z^b f)²σ^{2-γ}`;
* uniformly in `z`, the two right-hand integrals are bounded by `C·HkSq α 4 f`
  (`D_z^b f = z^b ∂_z^b f + …` is a finite combination, and the summand
  `(D_z^j f · w/σ^{η/2})²` resp. `(mixed b 1 f · Wt)²` is a summand of `HkIntegrand α 4 f`
  for `j ≤ 4` resp. `b + 1 ≤ 4`: use `Work.Spaces.sq_le_HkIntegrand_z`,
  `Work.Spaces.sq_le_HkIntegrand_mixed`, `Work.Spaces.DzIter_eq_sum_scoef`-type expansions,
  and the angular slice integrability `Work.FTS.EllipticEst.integrableOn_zSummand`,
  `...SliceDecompDefs.integrableOn_mixedSummand`);
* measurability of `z ↦ supAbsThO (DzIter b f) z` (the sup over the open interval) and a.e.
  strong measurability of the slice integrals, exactly as in `SupThetaIntQ.lean`
  (`SupAbsThOAesm.lean`); then integrate the a.e. inequality in `z`.
The factor `1/(γ-1)` is essential and cannot be replaced by a universal constant (see
`SlotT2/NOTES_sliceSupEtaGam_FALSE.md`). -/
theorem supThetaIntOpen : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b : ℕ),
    0 < α → α ≤ 1 → b ≤ 3 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    MeasureTheory.IntegrableOn
        (fun z => (sSup {y : ℝ | ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
            y = |Work.Spaces.DzIter b f z θ|}) ^ 2 * (Work.Spaces.w z) ^ 2)
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz,
          (sSup {y : ℝ | ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
            y = |Work.Spaces.DzIter b f z θ|}) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ C / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f := by
  refine ⟨1000, by norm_num, ?_⟩
  intro α f b hα hα1 hb3 hF hmem
  have hγpos : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- the a.e. pointwise bound, transported to `volume.restrict Iz`
  have hstep : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
        ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
            * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ := by
    rw [supOpen_restrict_Iz]
    exact supOpen_ae_sup_bound hF hmem hα hα1 hb3
  -- a.e. strong measurability of the interior angular supremum
  have hmeas_sup : AEMeasurable (fun z => Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine supOpen_supAbsThO_aemeasurable ?_ ?_ ?_
    · rw [supOpen_restrict_Iz]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hzpos
      exact ((hF.DzIter b).curry_θ hzpos).continuousOn
    · intro q hq
      rw [supOpen_restrict_Iz]
      exact (((hF.DzIter b).curry_z hq).continuousOn).aemeasurable measurableSet_Ioi
    · rw [supOpen_restrict_Iz]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hzpos
      exact supOpen_slice_bddAbove hF hmem hα hα1 hb3 hzpos
  have hw_meas : AEMeasurable (fun z : ℝ => Work.Spaces.w z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [supOpen_restrict_Iz]
    change AEMeasurable (fun z : ℝ => (1 + z) ^ 2 / z ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0))
    exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).aemeasurable
        measurableSet_Ioi
  have hf_aesm : AEStronglyMeasurable
      (fun z => (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ((hmeas_sup.mul hw_meas).pow_const 2).aestronglyMeasurable
  -- domination and integrability
  have hdom_nn : ∀ z, 0 ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
      * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) := fun z =>
    mul_nonneg (by positivity)
      (MeasureTheory.setIntegral_nonneg hIθ_meas
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ))
  have hdom_int : MeasureTheory.Integrable (fun z =>
      (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmem.2.const_mul _
  have hf_int : MeasureTheory.IntegrableOn
      (fun z => (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' hdom_int hf_aesm ?_
    filter_upwards [hstep] with z hz
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hz
  have hmain : ∫ z in Work.Spaces.Iz,
        (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
      ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := by
    calc ∫ z in Work.Spaces.Iz,
          (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
        ≤ ∫ z in Work.Spaces.Iz, (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun z => sq_nonneg _)) hdom_int hstep
      _ = (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
            * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 4 f z θ) :=
          MeasureTheory.integral_const_mul _ _
      _ = (4 / Real.pi + 200 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := rfl
  have hcoef : (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
      ≤ 1000 / (Work.Spaces.gam α - 1) := by
    have heq : (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
        = (4 / Real.pi * (Work.Spaces.gam α - 1) + 200) / (Work.Spaces.gam α - 1) := by
      field_simp
    rw [heq]
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hγpos)
    have h1 : (4 / Real.pi) * (Work.Spaces.gam α - 1) ≤ (4 / Real.pi) * 1 :=
      mul_le_mul_of_nonneg_left (by rw [Work.Spaces.gam]; linarith) (by positivity)
    have h2 : (4 : ℝ) / Real.pi ≤ 4 := by
      rw [div_le_iff₀ Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    linarith
  have hfun : (fun z : ℝ => (sSup {y : ℝ | ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        y = |Work.Spaces.DzIter b f z θ|}) ^ 2 * (Work.Spaces.w z) ^ 2)
      = fun z : ℝ =>
          (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2 := by
    funext z
    rw [mul_pow]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hf_int
  · rw [hfun]
    calc ∫ z in Work.Spaces.Iz,
          (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
        ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := hmain
      _ ≤ 1000 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f :=
          mul_le_mul_of_nonneg_right hcoef (Work.Spaces.HkSq_nonneg α 4 f)

end

end Work.FTS.TransportS.SlotT2
end
