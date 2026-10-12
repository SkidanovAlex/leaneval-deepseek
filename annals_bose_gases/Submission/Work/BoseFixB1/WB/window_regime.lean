import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.WB.banddecay_window
import Submission.Work.BoseFixB1.WB.convdev_window
import Submission.Work.BoseFixB1.WB.eps_window
import Submission.Work.BoseFixB1.WB.kb_window
import Submission.Work.BoseFixB1.fsRegimeAt
import Submission.Work.BoseFixB1.regime_sideAt_ge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WB.window_regime` — the dilute window regime of the particle window

FS `thm:aprioriHLambda` (step 4) is proved for `μ` in the dilute regime, and every
input of the argument holds for **all sufficiently dilute** `μ` — i.e. the
threshold `ε₀` can be chosen uniformly in `μ`:

* the support-radius conditions `R ≤ ℓ·χ_{R₀}` and `R ≤ ℓd/16`
  (`Work.BoseFixB1.regime_sideAt_ge`);
* FS's localisation regularity `M = 48 ≥ 3` (`M_eq_mValue`);
* the diluteness itself, `μa³ ≤ ε₀ ≤ 1`;
* the smallness `ε = K_B^{3/2}K_ℓ(μa³)^{1/4} ≤ 1/2` of the final `ε`-split
  (`eps_window`);
* FS's parameter condition `K_B³(μa³)^{1/2} ≤ π/(3C_A)` (`kb_window`);
* the quadratic-deviation error `convDevC M·(R/ℓ)² ≤ 1/4` of the total-mass
  identity (`convdev_window`);
* the discarded `χ_{B(u)}`-mass on the complement of the interior `I₋` of the
  sliding localisation (`interior_compl_mass_window` below).

The last conjunct is the only non-elementary one.  The interior of the sliding
localisation is the box `{|((ℓd)•u)_j| ≤ A - 2μ^{-1/3}}` (`A = ½ℓ(1+d)`), so its
complement is covered by the far set (where `χ_{B(u)} ≡ 0`) and the bad band, on
which the (g2)-integral law
(`ChiSmallBand.chiSmallB_badband_integral_law`, packaged as
`interior_compl_mass_le`) gives the `χ_{B(u)}²`-mass

  `∫_{I₋ᶜ} χ_{B(u)}² ≤ 12(1+d)²·chiSmallBandDecay M d·C₁·(μa³)^{M/3}·ℓ³`.

On the bad band the cutoff vanishes to order `2M` in `μ^{-1/3}/ℓ`, and
`μ^{-1/3}/ℓ = (μa³)^{166/969}`, so `(μ^{-1/3}/ℓ)^{2M+1} = (μa³)^{16102/969}` beats
`(μa³)^{M/3} = (μa³)^{16}`: with the law's constant `C₁ = 2^{2M}` the hypothesis
`hEst` of the law holds for every `μa³ ≤ 1` (`hest_window`).  What is left is the
decay of `chiSmallBandDecay M d·(μa³)^{M/3} ∝ (μa³)^{4592/323} → 0`
(`banddecay_window`), which is what makes the discarded mass a fixed multiple of
`ℓ³`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.WB

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. `I₋ᶜ ⊆ bandSet ∪ farSet`

The interior of the sliding localisation is the box
`{|((ℓd)•u)_j| ≤ A - 2μ^{-1/3}}` (`A = ½ℓ(1+d)`).  Its complement therefore has a
coordinate exceeding `A - 2μ^{-1/3}`; either that coordinate also exceeds `A` (so
`u` is in the far set, where the cutoff vanishes identically), or all coordinates
are `≤ A` and `u` lies in the bad band. -/
lemma interiorSet_compl_subset_bandSet_union_farSet {ℓ d μ : ℝ} :
    (Work.SmallBoxSliding.interiorSet ℓ d μ)ᶜ ⊆
      Work.SmallBoxSliding.bandSet ℓ d μ ∪ Work.SmallBoxSliding.farSet ℓ d μ := by
  intro u hu
  rw [Set.mem_compl_iff, Work.SmallBoxSliding.interiorSet, Set.mem_ofPred_eq,
    not_forall] at hu
  obtain ⟨j, hj⟩ := hu
  rw [not_le] at hj
  by_cases hfar : ∃ j' : Fin 3,
      (1 / 2) * ℓ * (1 + d) < |((ℓ * d) • u).ofLp j'|
  · exact Or.inr hfar
  · push Not at hfar
    exact Or.inl ⟨⟨j, le_of_lt hj⟩, hfar⟩

/-! ## 2. The discarded mass on `I₋ᶜ`

The (g2)-integral law of the sliding localisation
(`ChiSmallBand.chiSmallB_badband_integral_law`) bounds the `χ_{B(u)}²`-mass over
the bad band; the far set contributes nothing.  Hence the discarded mass over the
complement of the interior is bounded by the same law. -/
lemma interior_compl_mass_le {M : ℕ} (hM : 1 ≤ M) {ℓ d μ a C₁ : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (hμ : 0 < μ) (ha : 0 ≤ a) (hC₁ : 0 ≤ C₁)
    (hAδ : 0 ≤ (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ))
    (hEst : (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M) * μ ^ (-1 / 3 : ℝ) * ℓ ^ 2
        ≤ C₁ * (μ * a ^ 3) ^ ((M : ℝ) / 3) * ℓ ^ 3) :
    (∫ u in (Work.SmallBoxSliding.interiorSet ℓ d μ)ᶜ,
        Work.SmallBoxSliding.chiMass M ℓ d u)
      ≤ 12 * (1 + d) ^ 2 * Submission.BoseGases.chiSmallBandDecay M d * C₁
          * (μ * a ^ 3) ^ ((M : ℝ) / 3) * ℓ ^ 3 := by
  set F : ℝ³ → ℝ := fun u => ∫ x : ℝ³, (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2
    with hFdef
  have hchi : ∀ u : ℝ³, Work.SmallBoxSliding.chiMass M ℓ d u = F u := fun u => rfl
  have hFint : Integrable F := by
    rw [hFdef]
    exact Work.SmallBoxSliding.integrable_chiSmallB_mass hM hℓ hd
  have hF0 : ∀ u : ℝ³, 0 ≤ F u := by
    intro u
    rw [hFdef]
    exact integral_nonneg_of_ae (ae_of_all _ (fun x => sq_nonneg _))
  have hsub := interiorSet_compl_subset_bandSet_union_farSet (ℓ := ℓ) (d := d) (μ := μ)
  have hunion : (∫ u in Work.SmallBoxSliding.bandSet ℓ d μ ∪ Work.SmallBoxSliding.farSet ℓ d μ,
        F u)
      = (∫ u in Work.SmallBoxSliding.bandSet ℓ d μ, F u)
        + ∫ u in Work.SmallBoxSliding.farSet ℓ d μ, F u :=
    setIntegral_union (Work.SmallBoxSliding.disjoint_bandSet_farSet ℓ d μ)
      (Work.SmallBoxSliding.measurableSet_farSet ℓ d μ) hFint.integrableOn hFint.integrableOn
  have hfar : (∫ u in Work.SmallBoxSliding.farSet ℓ d μ, F u) = 0 := by
    have hpt : ∀ u ∈ Work.SmallBoxSliding.farSet ℓ d μ, F u = 0 := by
      intro u hu
      rw [hFdef]
      have hz : (fun x : ℝ³ => (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2)
          = fun _ => (0 : ℝ) := by
        funext x
        rw [Work.SmallBoxSliding.farSet_chiSmallB_zero hℓ hd hu x]
        ring
      simp only [hz]
      exact integral_zero _ _
    rw [setIntegral_congr_fun (Work.SmallBoxSliding.measurableSet_farSet ℓ d μ) hpt]
    simp
  calc (∫ u in (Work.SmallBoxSliding.interiorSet ℓ d μ)ᶜ,
        Work.SmallBoxSliding.chiMass M ℓ d u)
      = (∫ u in (Work.SmallBoxSliding.interiorSet ℓ d μ)ᶜ, F u) :=
        setIntegral_congr_fun (Work.SmallBoxSliding.measurableSet_interiorSet ℓ d μ).compl
          (fun u _ => hchi u)
    _ ≤ (∫ u in Work.SmallBoxSliding.bandSet ℓ d μ ∪ Work.SmallBoxSliding.farSet ℓ d μ, F u) :=
        setIntegral_mono_set hFint.integrableOn (Eventually.of_forall hF0)
          (Eventually.of_forall (fun u hu => hsub hu))
    _ = (∫ u in Work.SmallBoxSliding.bandSet ℓ d μ, F u)
        + ∫ u in Work.SmallBoxSliding.farSet ℓ d μ, F u := hunion
    _ = (∫ u in Work.SmallBoxSliding.bandSet ℓ d μ, F u) := by rw [hfar]; ring
    _ ≤ 12 * (1 + d) ^ 2 * Submission.BoseGases.chiSmallBandDecay M d * C₁
          * (μ * a ^ 3) ^ ((M : ℝ) / 3) * ℓ ^ 3 := by
        rw [hFdef, Work.SmallBoxSliding.bandSet_eq_chiSmallBadBand]
        exact Submission.BoseGases.chiSmallB_badband_integral_law hM hℓ hd hμ ha hAδ hC₁ hEst

/-! ## 3. The two closed forms of the regime

`μ^{-1/3} = a·(μa³)^{-1/3}` and `(μ^{-1/3}/ℓ)^{2M+1} ≤ (μa³)^{M/3}`, the latter
being the hypothesis `hEst` of the (g2)-law at the constant `C₁ = 2^{2M}`. -/

/-- `μ^{-1/3} = (a v)·(μ(a v)³)^{-1/3}`. -/
lemma mu_inv_third_eq_rpow {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v)
    {μ : ℝ} (hμ : 0 < μ) :
    μ ^ (-(1 / 3) : ℝ)
      = (_root_.BoseGases.a v) * (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(1 / 3) : ℝ) := by
  have ht0 : (0 : ℝ) < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  have hA3 : (0 : ℝ) < (_root_.BoseGases.a v) ^ 3 := by positivity
  have h2 : (((_root_.BoseGases.a v) ^ 3 : ℝ)) ^ (-(1 / 3) : ℝ) = (_root_.BoseGases.a v)⁻¹ := by
    rw [show (((_root_.BoseGases.a v) : ℝ) ^ 3) = (_root_.BoseGases.a v) ^ ((3 : ℕ) : ℝ) by
      exact (Real.rpow_natCast (_root_.BoseGases.a v) 3).symm]
    rw [← Real.rpow_mul hav.le]
    norm_num
    rw [Real.rpow_neg hav.le 1, Real.rpow_one]
  calc μ ^ (-(1 / 3) : ℝ)
      = ((μ * (_root_.BoseGases.a v) ^ 3) / (_root_.BoseGases.a v) ^ 3) ^ (-(1 / 3) : ℝ) := by
        rw [show (μ * (_root_.BoseGases.a v) ^ 3) / (_root_.BoseGases.a v) ^ 3 = μ by
          field_simp]
    _ = (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(1 / 3) : ℝ) * (_root_.BoseGases.a v) := by
        rw [Real.div_rpow ht0.le hA3.le, h2, div_inv_eq_mul]
    _ = (_root_.BoseGases.a v) * (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(1 / 3) : ℝ) := by ring

/-- `μ ↦ μ^{-1/3}` in the `-1/3` spelling of the (g2)-law. -/
lemma rpow_neg_third_congr (x : ℝ) : x ^ (-(1 / 3) : ℝ) = x ^ (-1 / 3 : ℝ) := by
  congr 1
  norm_num

/-- **The `hEst` hypothesis of the (g2)-law at `C₁ = 2^{2M}`**, for every
`μa³ ≤ 1`.  With `r := μ^{-1/3}/ℓ = (μa³)^{166/969}` (`μ^{-1/3} = a_μ(μa³)^{-1/3}`
and `ℓ = a(μa³)^{-163/323}`), both sides are `2^{2M}·r^{2M+1}·ℓ³` and
`2^{2M}·(μa³)^{M/3}·ℓ³`, and `(2M+1)·166/969 ≥ M/3 = 16`. -/
lemma hest_window {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v)
    {μ : ℝ} (hμ : 0 < μ) (ht : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1) :
    (2 * μ ^ (-(1 / 3) : ℝ) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        ^ (2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
      * μ ^ (-(1 / 3) : ℝ) * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2
    ≤ 2 ^ (2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
      * (μ * (_root_.BoseGases.a v) ^ 3)
          ^ (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M : ℝ) / 3)
      * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := by
  have ht0 : (0 : ℝ) < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  have hℓ : Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      = (_root_.BoseGases.a v) * (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(163 / 323) : ℝ) :=
    Work.BoseBox.sideAt_eq_rpow hav hμ
  have hℓpos : (0 : ℝ) < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
    rw [hℓ]; positivity
  have hmu : μ ^ (-(1 / 3) : ℝ)
      = (_root_.BoseGases.a v) * (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(1 / 3) : ℝ) :=
    mu_inv_third_eq_rpow hav hμ
  rw [mul_div_assoc]
  rw [Work.BoseFixB1.M_eq_mValue,
    show (2 * Work.BoseBox.mValue : ℕ) = 96 by norm_num [Work.BoseBox.mValue],
    show ((Work.BoseBox.mValue : ℝ) / 3) = 16 by norm_num [Work.BoseBox.mValue]]
  rw [mul_pow]
  set r : ℝ := μ ^ (-(1 / 3) : ℝ) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) with hrdef
  have hr : r = (μ * (_root_.BoseGases.a v) ^ 3) ^ (166 / 969 : ℝ) := by
    rw [hrdef, hmu, hℓ, mul_div_mul_left _ _ (ne_of_gt hav), ← Real.rpow_sub ht0]
    congr 1
    norm_num
  have hpow : r ^ (97 : ℝ) ≤ (μ * (_root_.BoseGases.a v) ^ 3) ^ (16 : ℝ) := by
    rw [hr, ← Real.rpow_mul ht0.le]
    exact Real.rpow_le_rpow_of_exponent_ge ht0 ht (by norm_num)
  have hkey : r * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) = μ ^ (-(1 / 3) : ℝ) := by
    rw [hrdef]
    exact div_mul_cancel₀ _ (ne_of_gt hℓpos)
  have hstep : 2 ^ 96 * r ^ 96 * μ ^ (-(1 / 3) : ℝ)
        * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 2
      = 2 ^ 96 * r ^ 97 * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := by
    rw [show (97 : ℕ) = 96 + 1 by norm_num, pow_succ, ← hkey]
    ring
  rw [hstep]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by simpa using hpow) (by positivity)) (by positivity)

/-! ## 4. The discarded mass in the regime -/

/-- **The discarded mass on `I₋ᶜ` is a fixed multiple of `ℓ³` on the dilute
window**, given the decay of the bad-band constant
(`banddecay_window`, which supplies `∃ε, 12(1+d)²·chiSmallBandDecay M d·2^{2M}(μa³)^{M/3}
≤ 2π/C₁` for `μa³ ≤ ε`). -/
lemma interior_compl_mass_of_band {v : EuclideanSpace ℝ (Fin 3) → ℝ} {C₁ : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hC₁ : 0 < C₁)
    (hband : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ →
      12 * (1 + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
          * Submission.BoseGases.chiSmallBandDecay (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          * 2 ^ 96 * (μ * (_root_.BoseGases.a v) ^ 3) ^ (16 : ℝ)
        ≤ 2 * Real.pi / C₁) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ →
      (∫ u in (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ,
          Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        ≤ (2 * Real.pi / C₁) * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := by
  obtain ⟨εb, hεb, hb⟩ := hband
  have hθpos : (0 : ℝ) < (1 / 4 : ℝ) ^ (969 / 166 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨min εb (min ((1 / 4 : ℝ) ^ (969 / 166 : ℝ)) 1),
    lt_min hεb (lt_min hθpos one_pos), ?_⟩
  intro μ hμ ht
  have htb : μ * (_root_.BoseGases.a v) ^ 3 ≤ εb := le_trans ht (min_le_left _ _)
  have htθ : μ * (_root_.BoseGases.a v) ^ 3 ≤ (1 / 4 : ℝ) ^ (969 / 166 : ℝ) :=
    le_trans ht (le_trans (min_le_right _ _) (min_le_left _ _))
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
    le_trans ht (le_trans (min_le_right _ _) (min_le_right _ _))
  have ht0 : (0 : ℝ) < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  have hℓpos : (0 : ℝ) < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
    rw [Work.BoseBox.sideAt_eq_rpow hav hμ]; positivity
  have hdpos : (0 : ℝ) < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := by
    rw [Work.BoseFixB1.d_eq_fsXp]; exact Work.BoseBox.fsXp_pos ht0
  have hM1 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M :=
    Work.BoseFixB1.M_ge_one μ (_root_.BoseGases.a v)
  have hAδ : 0 ≤ (1 / 2) * Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (1 + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
      - 2 * μ ^ (-(1 / 3) : ℝ) :=
    Work.BoseFixB1.ell_residual_nonneg_fb hav hμ htθ
  have hest := hest_window (v := v) hav hμ ht1
  rw [rpow_neg_third_congr] at hAδ hest
  have hlaw := interior_compl_mass_le (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    hM1 hℓpos hdpos hμ hav.le (by norm_num) hAδ hest
  have hM3 : (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M : ℝ) / 3) = 16 := by
    rw [Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  have hbd := hb μ hμ htb
  rw [hM3] at hlaw
  calc (∫ u in (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ,
          Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      ≤ 12 * (1 + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
          * Submission.BoseGases.chiSmallBandDecay (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          * 2 ^ 96 * (μ * (_root_.BoseGases.a v) ^ 3) ^ (16 : ℝ)
          * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := hlaw
    _ = (12 * (1 + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
          * Submission.BoseGases.chiSmallBandDecay (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          * 2 ^ 96 * (μ * (_root_.BoseGases.a v) ^ 3) ^ (16 : ℝ))
          * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := by ring
    _ ≤ (2 * Real.pi / C₁) * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 :=
        mul_le_mul_of_nonneg_right hbd (by positivity)

/-- The discarded mass on `I₋ᶜ` at FS's parameters, from the bad-band decay. -/
lemma interior_compl_mass_window {v : EuclideanSpace ℝ (Fin 3) → ℝ} {C₁ : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hC₁ : 0 < C₁) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ →
      (∫ u in (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ,
          Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        ≤ (2 * Real.pi / C₁) * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 :=
  interior_compl_mass_of_band (v := v) hav hC₁ (banddecay_window (v := v) hav hC₁)

/-! ## 5. The regime bundle -/

theorem window_regime {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R C₁ C_A : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hR : 0 < R) (hC₁ : 0 < C₁) (hCA : 0 < C_A) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      (R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
      ∧ (R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
      ∧ (3 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
      ∧ (μ * (_root_.BoseGases.a v) ^ 3 ≤ 1)
      ∧ (Work.BoseFixB1.wbEps v μ ≤ 1 / 2)
      ∧ ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) ≤ Real.pi / (3 * C_A))
      ∧ (Submission.BoseGases.convDevC (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            * (R / Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2 ≤ 1 / 4)
      ∧ ((∫ u in (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ,
            Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          ≤ (2 * Real.pi / C₁) * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) := by
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge hav hR
  obtain ⟨εe, hεe, heps⟩ := eps_window (v := v) hav
  obtain ⟨εk, hεk, hkb⟩ := kb_window (v := v) hav hCA
  obtain ⟨εc, hεc, hcv⟩ := convdev_window (v := v) hav hR
  obtain ⟨εi, hεi, hic⟩ := interior_compl_mass_window (v := v) hav hC₁
  refine ⟨min εr (min εe (min εk (min εc (min εi 1)))),
    lt_min hεr (lt_min hεe (lt_min hεk (lt_min hεc (lt_min hεi one_pos)))), ?_⟩
  intro μ hAdm
  obtain ⟨hμ, hdil, _hOK⟩ := hAdm
  have hr : μ * (_root_.BoseGases.a v) ^ 3 ≤ εr := le_trans hdil (min_le_left _ _)
  have hrest : μ * (_root_.BoseGases.a v) ^ 3 ≤ min εe (min εk (min εc (min εi 1))) :=
    le_trans hdil (min_le_right _ _)
  have he : μ * (_root_.BoseGases.a v) ^ 3 ≤ εe := le_trans hrest (min_le_left _ _)
  have hrest2 : μ * (_root_.BoseGases.a v) ^ 3 ≤ min εk (min εc (min εi 1)) :=
    le_trans hrest (min_le_right _ _)
  have hk : μ * (_root_.BoseGases.a v) ^ 3 ≤ εk := le_trans hrest2 (min_le_left _ _)
  have hrest3 : μ * (_root_.BoseGases.a v) ^ 3 ≤ min εc (min εi 1) :=
    le_trans hrest2 (min_le_right _ _)
  have hc : μ * (_root_.BoseGases.a v) ^ 3 ≤ εc := le_trans hrest3 (min_le_left _ _)
  have hrest4 : μ * (_root_.BoseGases.a v) ^ 3 ≤ min εi 1 :=
    le_trans hrest3 (min_le_right _ _)
  have hi : μ * (_root_.BoseGases.a v) ^ 3 ≤ εi := le_trans hrest4 (min_le_left _ _)
  have hone : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := le_trans hrest4 (min_le_right _ _)
  obtain ⟨hA, hB⟩ := hreg μ hμ hr
  have hM3 : 3 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  exact ⟨hB, hA, hM3, hone, heps μ hμ he, hkb μ hμ hk, hcv μ hμ hc, hic μ hμ hi⟩

end Work.BoseFixB1.WB
