import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsRLX.Defs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsMemOfClassCJeps
import Submission.Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_le_HkSq_ClassC
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_Pz_sub_le
import Submission.Work.FTS.StrongEps.EpsRLX.ProfileSlotCompare
import Submission.Work.FTS.StrongEps.EpsRLX.ProfileMixedSlot.EpsSq_mixed_le_HkSq
import Submission.Work.FTS.StrongEps.EpsRLX.ProfileDzSlot.EpsSq_dzIter_le_HkSq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongEps.EpsRLX.ProfileFacts`

**The profile facts of one admissible datum of the projected `ε`-scheme.**

Given the datum `ProfileData α C₀ B ε ρ u` (open-quadrant smoothness of `u`, honest `ℋ⁶`-membership
with size `≤ B`, and `ClassC` plus the small-ball bound `Xn ≤ C₀α²` for the projected-mollified
profile `Wp ρ ε u = Pz (Jeps ρ ε u)`), the datum and its projected-mollified profile satisfy the
eight boundedness facts needed downstream, with one constant `C` — independent of `α ∈ (0,1]`,
of `ε ∈ (0,1]`, of `C₀`, `B`, `u` and of the kernel `ρ` (it only depends on `ρ` through the two
constants of `EpsMemOfClassCJeps` and `HkSq_JepsPz_le`).

The four ingredients are, in order of appearance,

* `EpsLocalPStar.EpsMemOfClassCJeps` — the datum itself is in the weighted space `X`, with the
  sharp `1/(γ-1)²`-degradation (`γ = 1 + α/10`), using the vanishing of the endpoint traces forced
  by `ClassC α (Pz (Jeps ρ ε u))` (conjuncts 1, 2);
* `EpsSqTools.HkSq_JepsPz_le` at `k = 6` — the mollified-projected profile is in `ℋ⁶`, at the cost
  of one factor `C/ε` per derivative (conjunct 3);
* `EpsSqTools.EpsSq_le_HkSq_ClassC` — the `X`-norm of a class element is bounded by its `ℋ⁴`-norm
  times `C/(γ-1)⁸`, and `ℋ⁴ ≤ ℋ⁶` (conjuncts 4, 5);
* the class fields `tr`, `mem` (conjuncts 6, 7), and the mixed slots (conjunct 8), which are the
  `KMath` content of this file's siblings:
  * for `1 ≤ a`, `EpsSq α (mixed b a Wp) ≤ HkSq α 6 Wp` because `(mixed b a Wp · W)²` is literally
    one summand of `HkIntegrand α 6 Wp` (`EpsRLX.ProfileMixedSlot.EpsSq_mixed_le_HkSq`);
  * for `a = 0` (so `mixed b 0 Wp = D_z^b Wp`, `b ≤ 4`), the weighted angular Hardy inequality
    (`EpsLocalPStar.EpsSliceLe`, constant `1/(γ-1)²`) applied to the `θ`-slice of `D_z^b Wp` turns
    `sin^{-γ}(D_z^b Wp)²` into the `(b,1)`-slot `(mixed b 1 Wp · W)²` of `ℋ⁶`
    (`EpsRLX.ProfileDzSlot.EpsSq_dzIter_le_HkSq`); the traces required by the Hardy inequality are
    exactly the `(a,b) = (0,b)` clause of the class's `BdryTraces α 6 Wp`.

Since `(γ-1)² ≥ (γ-1)⁸` for `γ - 1 = α/10 ≤ 1/10`, all the exponents `2` above are absorbed into
the exponent `8`, and since `1 ≤ C/(γ-1)⁸` the slot bounds may be inflated freely.
-/

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

theorem ProfileFacts (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ ε ∈ Set.Ioc 0 1, ∀ {C₀ B : ℝ}, ∀ {u : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.EpsRLX.ProfileData α C₀ B ε ρ u →
      Work.FTS.StrongEps.EpsMem α u ∧
      Work.FTS.StrongEps.EpsSq α u ≤ C / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 1 u ∧
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
        ≤ C * (C / ε) ^ 12 * Work.FTS.StrongEps.EpsSq α u ∧
      Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ∧
      Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
        ≤ C / (Work.Spaces.gam α - 1) ^ 8
            * Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ∧
      Work.FTS.Nonlin.BdryTraces α 6 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ∧
      Work.Spaces.HkMem α 7 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ∧
      (∀ b a : ℕ, a + b ≤ 4 →
        Work.FTS.StrongEps.EpsMem α (Work.Spaces.mixed b a (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)) ∧
        Work.FTS.StrongEps.EpsSq α (Work.Spaces.mixed b a (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u))
          ≤ C / (Work.Spaces.gam α - 1) ^ 8
              * Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongEps.EpsLocalPStar.EpsMemOfClassCJeps ρ hρ
  obtain ⟨C₃, hC₃pos, hC₃⟩ := Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le ρ hρ
  obtain ⟨C₅, hC₅pos, hC₅⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSq_le_HkSq_ClassC
  obtain ⟨C₈, hC₈pos, hC₈⟩ := Work.FTS.StrongEps.EpsRLX.ProfileDzSlot.EpsSq_dzIter_le_HkSq
  refine ⟨max 1 (C₁ + C₃ + C₅ + C₈), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro α hα ε hε C₀ B u hd
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hε0 : 0 < ε := hε.1
  have hε1 : ε ≤ 1 := hε.2
  set C : ℝ := max 1 (C₁ + C₃ + C₅ + C₈) with hCdef
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hCnn : 0 ≤ C := hCpos.le
  have hs : C₁ + C₃ + C₅ + C₈ ≤ C := le_max_right _ _
  have hC₁le : C₁ ≤ C := by linarith [hs, hC₃pos, hC₅pos, hC₈pos]
  have hC₃le : C₃ ≤ C := by linarith [hs, hC₁pos, hC₅pos, hC₈pos]
  have hC₅le : C₅ ≤ C := by linarith [hs, hC₁pos, hC₃pos, hC₈pos]
  have hC₈le : C₈ ≤ C := by linarith [hs, hC₁pos, hC₃pos, hC₅pos]
  have hγpos : 0 < Work.Spaces.gam α - 1 := by
    have := Work.Spaces.one_lt_gam hα0
    linarith
  have hγle : Work.Spaces.gam α - 1 ≤ 1 := by rw [Work.Spaces.gam]; linarith
  -- (1) and (2): the datum `u` itself
  obtain ⟨hmem_u, hsq_u⟩ := hC₁ α hα ε hε0 hε1 u hd.smo hd.hkmem hd.cls
  have hB : Work.FTS.StrongEps.EpsSq α u
      ≤ C / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 1 u := by
    have hcoef : C₁ / (Work.Spaces.gam α - 1) ^ 2 ≤ C / (Work.Spaces.gam α - 1) ^ 2 :=
      div_le_div_of_nonneg_right hC₁le (pow_pos hγpos 2).le
    exact le_trans hsq_u (mul_le_mul_of_nonneg_right hcoef (Work.Spaces.HkSq_nonneg α 1 u))
  -- (3): the `ℋ⁶`-size of the projected-mollified profile
  have h3 : Work.Spaces.HkSq α 6 (Wp ρ ε u)
      ≤ C * (C / ε) ^ 12 * Work.FTS.StrongEps.EpsSq α u := by
    have h := hC₃ α hα ε hε0 hε1 6 (by norm_num) u hd.smo hmem_u
    have hE : 0 ≤ Work.FTS.StrongEps.EpsSq α u := Work.FTS.StrongEps.EpsSq_nonneg α u
    have hbase : C₃ / ε ≤ C / ε := div_le_div_of_nonneg_right hC₃le hε0.le
    have hpow : (C₃ / ε) ^ 12 ≤ (C / ε) ^ 12 :=
      pow_le_pow_left₀ (div_nonneg hC₃pos.le hε0.le) hbase 12
    have hCY : C₃ * (C₃ / ε) ^ 12 ≤ C * (C / ε) ^ 12 :=
      mul_le_mul hC₃le hpow (pow_nonneg (div_nonneg hC₃pos.le hε0.le) 12) hCnn
    refine le_trans h ?_
    simpa only [show 2 * 6 = 12 by norm_num] using mul_le_mul_of_nonneg_right hCY hE
  -- (4) and (5): the projected-mollified profile
  obtain ⟨hmem_W, hsq_W⟩ := hC₅ α hα (Wp ρ ε u) hd.cls
  have hmem6W : Work.Spaces.HkMem α 6 (Wp ρ ε u) :=
    Work.FTS.OpenPkg.HkMem_mono_open hd.cls.reg 6 (by norm_num) hd.cls.mem8
  have hE5 : Work.FTS.StrongEps.EpsSq α (Wp ρ ε u)
      ≤ C / (Work.Spaces.gam α - 1) ^ 8 * Work.Spaces.HkSq α 6 (Wp ρ ε u) := by
    have hmono : Work.Spaces.HkSq α 4 (Wp ρ ε u) ≤ Work.Spaces.HkSq α 6 (Wp ρ ε u) :=
      Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hmem6W
    have hcoef : C₅ / (Work.Spaces.gam α - 1) ^ 8 ≤ C / (Work.Spaces.gam α - 1) ^ 8 :=
      div_le_div_of_nonneg_right hC₅le (pow_pos hγpos 8).le
    exact le_trans hsq_W
      (mul_le_mul hcoef hmono (Work.Spaces.HkSq_nonneg α 4 (Wp ρ ε u))
        (div_nonneg hCnn (pow_pos hγpos 8).le))
  -- (8): the mixed slots of the projected-mollified profile
  have h8 : ∀ b a : ℕ, a + b ≤ 4 →
      Work.FTS.StrongEps.EpsMem α (Work.Spaces.mixed b a (Wp ρ ε u)) ∧
      Work.FTS.StrongEps.EpsSq α (Work.Spaces.mixed b a (Wp ρ ε u))
        ≤ C / (Work.Spaces.gam α - 1) ^ 8 * Work.Spaces.HkSq α 6 (Wp ρ ε u) := by
    intro b a hab
    have hbig : (1 : ℝ) ≤ C / (Work.Spaces.gam α - 1) ^ 8 := by
      have hx : (Work.Spaces.gam α - 1) ^ 8 ≤ 1 := pow_le_one₀ hγpos.le hγle
      have hinv : (1 : ℝ) ≤ ((Work.Spaces.gam α - 1) ^ 8)⁻¹ :=
        (one_le_inv₀ (pow_pos hγpos 8)).mpr hx
      rw [div_eq_mul_inv]
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ C * ((Work.Spaces.gam α - 1) ^ 8)⁻¹ := mul_le_mul hC1 hinv zero_le_one hCnn
    by_cases ha : a = 0
    · subst ha
      obtain ⟨hmem8, hsq8⟩ := hC₈ α hα (f := Wp ρ ε u) hd.cls.reg hmem6W hd.cls.tr b (by omega)
      have hcoef : C₈ / (Work.Spaces.gam α - 1) ^ 2 ≤ C / (Work.Spaces.gam α - 1) ^ 8 :=
        div_le_div₀ hCnn hC₈le (pow_pos hγpos 8)
          (pow_le_pow_of_le_one hγpos.le hγle (by norm_num))
      refine ⟨?_, ?_⟩
      · simpa only [Work.Spaces.mixed_zero_right] using hmem8
      · calc Work.FTS.StrongEps.EpsSq α (Work.Spaces.mixed b 0 (Wp ρ ε u))
            = Work.FTS.StrongEps.EpsSq α (Work.Spaces.DzIter b (Wp ρ ε u)) := by
              rw [Work.Spaces.mixed_zero_right]
          _ ≤ C₈ / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 6 (Wp ρ ε u) := hsq8
          _ ≤ C / (Work.Spaces.gam α - 1) ^ 8 * Work.Spaces.HkSq α 6 (Wp ρ ε u) :=
              mul_le_mul_of_nonneg_right hcoef (Work.Spaces.HkSq_nonneg α 6 (Wp ρ ε u))
    · have ha1 : 1 ≤ a := by omega
      obtain ⟨hmemM, hsqM⟩ :=
        Work.FTS.StrongEps.EpsRLX.ProfileMixedSlot.EpsSq_mixed_le_HkSq hd.cls.reg hmem6W
          (j := b) (i := a) ha1 (by omega)
      exact ⟨hmemM, le_trans hsqM (by
        calc Work.Spaces.HkSq α 6 (Wp ρ ε u)
            = 1 * Work.Spaces.HkSq α 6 (Wp ρ ε u) := by ring
          _ ≤ C / (Work.Spaces.gam α - 1) ^ 8 * Work.Spaces.HkSq α 6 (Wp ρ ε u) :=
              mul_le_mul_of_nonneg_right hbig (Work.Spaces.HkSq_nonneg α 6 (Wp ρ ε u)))⟩
  exact ⟨hmem_u, hB, h3, hmem_W, hE5, hd.cls.tr, hd.cls.mem, h8⟩

end Work.FTS.StrongEps.EpsRLX
