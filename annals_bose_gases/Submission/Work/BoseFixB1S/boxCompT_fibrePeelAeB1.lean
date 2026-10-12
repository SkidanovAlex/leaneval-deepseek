import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.HopDefs
import Submission.Work.BoseFixB1S.boxPQw_mass_le
import Submission.Work.BoseFixB1S.fibreSandwichB1
import Submission.Work.BoseFixB1S.peelSlotIndicator
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxCompT_fibrePeelAeB1`

The (PEEL) identity at the box projections with the fibre hypotheses the corpus actually
supplies (a.e. strong measurability plus a bound, instead of measurability).

The proof has three ingredients.

* **The fibre is integrable over `A`.**  `fib` is a.e. strongly measurable on the cube and
  bounded there by `Cf`; since `A ⊆ acube ℓ` has finite measure, `1_A · fib` is integrable on
  the cube (`integrable_Aind_mul_of_bound`), which supplies the `hg` hypothesis of the peel.
* **The component is `P_{A,i}`-fixed.**  `boxPInd_boxCompT` says that for `i ∈ S` the component
  `G = boxCompT V A S T Φ` is fixed by `P_{A,i}`:
  `P_{A,i}G = G` on the box.  Unfolding `P_{A,i}` (`boxPInd_eq`) this gives, for
  `x` in the box, `G x = 1_A(x i) · (1/V)·∫_A G(x|i↦z) dz`; hence `G` vanishes for `x i ∉ A`
  (`hzero`) and, on the peeled configuration `x = kcInsN n i (t,r)`, the value
  `G (kcInsN n i (t,r)) = (1/V)·∫_A G (kcInsN n i (z,r)) dz` is *independent of `t ∈ A`*
  (`hconst`).
* **The peel.**  `peelSlotIndicator` (with `g = fib` and `K = G²`) turns the box integral
  `∫ 1_A(x i)·fib(x i)·G²` into the iterated integral `∫_{t∈A} fib t · ∫_{abox n ℓ} G(kcInsN(t,r))²`;
  by `hzero` the left side is `∫ G²·fib(x i)`, and by `hconst` the inner integral is the constant
  `K2 = ∫_{abox n ℓ} G(kcInsN(a₀,r))²`, so the whole thing is `M1 · K2`.  The *same* peel with
  `g = 1` gives the flat identity `∫ G² = V · K2`.  Dividing by `V` finishes.
-/

namespace Work.BoseFixB1S

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **Integrability of a bounded a.e.-strongly-measurable fibre against the indicator of `A`.**
For `A ⊆ acube ℓ` with `A` measurable (so `A` has finite volume) and `f` a.e. strongly
measurable on the cube and bounded there by `C`, the function `1_A · f` is integrable for the
restricted cube measure.  This is exactly the `hg` hypothesis of
`Work.BoseFixB1S.peelSlotIndicator`. -/
private theorem integrable_Aind_mul_of_bound {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hA : MeasurableSet A)
    {f : E3 → ℝ} (hfm : AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {C : ℝ} (hb : ∀ z ∈ Submission.BoseGases.acube ℓ, |f z| ≤ C) :
    Integrable (fun z => Work.BoseFixB1S.Aind A z * f z)
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)) := by
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le]
        exact ENNReal.ofReal_lt_top⟩
  refine Integrable.of_bound ?_ (max C 0) ?_
  · exact (measurable_const.indicator hA).aestronglyMeasurable.mul hfm
  · rw [ae_restrict_iff' (Submission.BoseGases.acube_measurable ℓ)]
    apply Filter.Eventually.of_forall
    intro z hz
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hzA : z ∈ A
    · rw [Work.BoseFixB1S.Aind, Set.indicator_of_mem hzA, abs_one, one_mul]
      exact le_trans (hb z hz) (le_max_left _ _)
    · rw [Work.BoseFixB1S.Aind, Set.indicator_of_notMem hzA, abs_zero, zero_mul]
      exact le_max_right _ _

/-- **The (PEEL) identity at the box projections, with the fibre hypotheses the corpus
actually supplies.**  For a fibre `fib` that is only *a.e. strongly measurable* on the cube
(this is all that is available for the localised fibre `w1Fibre ℓ (wSmall1Pair …)`, since `g₀` is
only a.e. measurable) and bounded there, a joint component `ψ = boxCompT V A S T Φ` whose slot `i`
lies in the `P`-part `S` is `P_{A,i}`-fixed, hence `fib(xᵢ)` acts on it as its box average
`M1/V = (∫_A fib)/volA`:

  `∫_{abox} ψ²·fib(xᵢ) = (M1/V)·∫_{abox} ψ²` .

This is `Work.BoseFixB1S.boxCompT_fibrePeelB1` with `Measurable fib` replaced by
a.e.-strong measurability plus a bound (needed to get `IntegrableOn fib A`; without it both
sides are junk and the identity can genuinely fail).  Both replacement hypotheses are exactly what
`Work.BoseFixB1.q1Fib_aem_bound` returns for `fib = w1Fibre ℓ (wSmall1Pair h M ℓ d u)`. -/
theorem boxCompT_fibrePeelAeB1 {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hfibm : MeasureTheory.AEStronglyMeasurable fib
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {Cf : ℝ} (hfibb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ Cf)
    {M1 : ℝ} (hM1 : M1 = ∫ z in A, fib z)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {S T : Finset (Fin N)} (i : Fin N) (hi : i ∈ S) (hST : Disjoint S T) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.boxCompT V A S T Φ x) ^ 2 * fib (x i))
      = (M1 / V) * ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.boxCompT V A S T Φ x) ^ 2 := by
  -- `N ≠ 0` and `N = n + 1`, so that the peel `peelSlotIndicator` applies
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  -- `A` is nonempty, since it has positive volume `V`
  have hAne : A.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, MeasureTheory.measure_empty, ENNReal.toReal_zero] at hVeq
    linarith
  obtain ⟨a₀, ha₀⟩ := hAne
  -- the joint component, as `G`
  set G : Submission.BoseGases.X (n + 1) → ℝ := Work.BoseFixB1S.boxCompT V A S T Φ with hG
  obtain ⟨hGm, CG, hGb⟩ :=
    Work.BoseFixB1S.goodState_boxCompT hℓ hV hA hVeq hAc S T
      (Work.BoseFixB1S.goodState_of_continuous hℓ hΦc)
  -- the bound `G² ≤ (max CG 0)²` on the box, and measurability of `G²`
  have hCnn : 0 ≤ (max CG 0) ^ 2 := sq_nonneg _
  have hKb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ,
      |(fun x => G x ^ 2) x| ≤ (max CG 0) ^ 2 := by
    intro x hx
    have h1 : |G x| ≤ max CG 0 := le_trans (hGb x hx) (le_max_left _ _)
    show |G x ^ 2| ≤ (max CG 0) ^ 2
    rw [abs_of_nonneg (sq_nonneg (G x)), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hKm : AEStronglyMeasurable (fun x => G x ^ 2)
      (volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)) :=
    (hGm.pow_const 2).aestronglyMeasurable
  -- the fibre is integrable on `A ⊆ acube ℓ`
  have hg1 : Integrable (fun z => Work.BoseFixB1S.Aind A z * fib z)
      (volume.restrict (Submission.BoseGases.acube ℓ)) :=
    integrable_Aind_mul_of_bound hℓ hA hfibm hfibb
  have hg2 : Integrable (fun z => Work.BoseFixB1S.Aind A z * (1 : ℝ))
      (volume.restrict (Submission.BoseGases.acube ℓ)) :=
    integrable_Aind_mul_of_bound (C := 1) (f := fun _ : E3 => (1 : ℝ)) hℓ hA
      aestronglyMeasurable_const (fun z hz => by simp)
  -- the two peels: against the fibre, and against the constant `1`
  have hpeel1 := Work.BoseFixB1S.peelSlotIndicator (n := n) hℓ hA hAc i
    (g := fib) (K := fun x => G x ^ 2) hg1 hCnn hKm hKb
  have hpeel2 := Work.BoseFixB1S.peelSlotIndicator (n := n) hℓ hA hAc i
    (g := fun _ : E3 => (1 : ℝ)) (K := fun x => G x ^ 2) hg2 hCnn hKm hKb
  -- `G` vanishes where the slot `i` lies outside `A`
  have hzero : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ, x i ∉ A → G x = 0 := by
    intro x hx hxi
    have hfix := Work.BoseFixB1S.boxPInd_boxCompT hℓ hV hA hVeq hAc S T hΦc i x hx
    rw [if_pos hi] at hfix
    rw [Work.BoseFixB1S.boxPInd_eq V A i G x, Work.BoseFixB1S.Aind,
      Set.indicator_of_notMem hxi, zero_mul] at hfix
    exact hfix.symm
  -- on the peeled configuration the value of `G` is independent of the slot-`i` variable in `A`
  have hconst : ∀ (t : E3), t ∈ A → ∀ r ∈ Submission.BoseGases.abox n ℓ,
      G (Submission.BoseGases.kcInsN n i (t, r))
        = G (Submission.BoseGases.kcInsN n i (a₀, r)) := by
    intro t ht r hr
    have key : ∀ u ∈ A, G (Submission.BoseGases.kcInsN n i (u, r))
        = (1 / V) * ∫ z in A, G (Submission.BoseGases.kcInsN n i (z, r)) := by
      intro u hu
      have hx := Work.BoseFixB1S.kcInsN_mem_abox hAc i hu hr
      have hfix := Work.BoseFixB1S.boxPInd_boxCompT hℓ hV hA hVeq hAc S T hΦc i _ hx
      rw [if_pos hi] at hfix
      rw [Work.BoseFixB1S.boxPInd_eq V A i G _,
        Submission.BoseGases.kc_insN_apply_same, Work.BoseFixB1S.Aind,
        Set.indicator_of_mem hu, one_mul, Work.BoseFixB1S.oneMean] at hfix
      have hcongr : (∫ z in A, G (Function.update (Submission.BoseGases.kcInsN n i (u, r)) i z))
          = ∫ z in A, G (Submission.BoseGases.kcInsN n i (z, r)) := by
        apply setIntegral_congr_fun hA
        intro z hz
        simp only [Submission.BoseGases.update_kcInsN]
      rw [hcongr] at hfix
      exact hfix.symm
    rw [key t ht, key a₀ ha₀]
  -- the slotted mass `K2`
  set K2 : ℝ := ∫ r in Submission.BoseGases.abox n ℓ,
    G (Submission.BoseGases.kcInsN n i (a₀, r)) ^ 2 with hK2
  have hK2eq : ∀ t ∈ A, (∫ r in Submission.BoseGases.abox n ℓ,
      G (Submission.BoseGases.kcInsN n i (t, r)) ^ 2) = K2 := by
    intro t ht
    rw [hK2]
    apply setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
    intro r hr
    simp only [hconst t ht r hr]
  -- the fibre peel, evaluated
  have hfibre : (∫ t in A, fib t * (∫ r in Submission.BoseGases.abox n ℓ,
        G (Submission.BoseGases.kcInsN n i (t, r)) ^ 2)) = M1 * K2 := by
    calc (∫ t in A, fib t * (∫ r in Submission.BoseGases.abox n ℓ,
          G (Submission.BoseGases.kcInsN n i (t, r)) ^ 2))
        = ∫ t in A, fib t * K2 := by
          apply setIntegral_congr_fun hA
          intro t ht
          simp only [hK2eq t ht]
      _ = (∫ t in A, fib t) * K2 := MeasureTheory.integral_mul_const K2 _
      _ = M1 * K2 := by rw [← hM1]
  -- the flat identity
  have hflat : (∫ x in Submission.BoseGases.abox (n + 1) ℓ, G x ^ 2) = V * K2 := by
    have hL : (∫ x in Submission.BoseGases.abox (n + 1) ℓ, G x ^ 2)
        = ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            A.indicator (fun _ => (1 : ℝ)) (x i) * (1 : ℝ) * G x ^ 2 := by
      apply setIntegral_congr_fun (Submission.BoseGases.abox_measurable (n + 1) ℓ)
      intro x hx
      by_cases hxi : x i ∈ A
      · show G x ^ 2 = A.indicator (fun _ => (1 : ℝ)) (x i) * (1 : ℝ) * G x ^ 2
        rw [Set.indicator_of_mem hxi]; ring
      · show G x ^ 2 = A.indicator (fun _ => (1 : ℝ)) (x i) * (1 : ℝ) * G x ^ 2
        rw [Set.indicator_of_notMem hxi, hzero x hx hxi]; ring
    rw [hL, hpeel2]
    have h2 : (∫ t in A, (1 : ℝ) * (∫ r in Submission.BoseGases.abox n ℓ,
          G (Submission.BoseGases.kcInsN n i (t, r)) ^ 2)) = ∫ t in A, K2 := by
      apply setIntegral_congr_fun hA
      intro t ht
      show (1 : ℝ) * (∫ r in Submission.BoseGases.abox n ℓ,
        G (Submission.BoseGases.kcInsN n i (t, r)) ^ 2) = K2
      rw [one_mul, hK2eq t ht]
    rw [h2, MeasureTheory.setIntegral_const, smul_eq_mul, hVeq]
    rfl
  -- rewrite the left-hand side as the peel's left-hand side
  have hLHS : (∫ x in Submission.BoseGases.abox (n + 1) ℓ, G x ^ 2 * fib (x i))
      = ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          A.indicator (fun _ => (1 : ℝ)) (x i) * fib (x i) * G x ^ 2 := by
    apply setIntegral_congr_fun (Submission.BoseGases.abox_measurable (n + 1) ℓ)
    intro x hx
    by_cases hxi : x i ∈ A
    · show G x ^ 2 * fib (x i)
          = A.indicator (fun _ => (1 : ℝ)) (x i) * fib (x i) * G x ^ 2
      rw [Set.indicator_of_mem hxi]; ring
    · show G x ^ 2 * fib (x i)
          = A.indicator (fun _ => (1 : ℝ)) (x i) * fib (x i) * G x ^ 2
      rw [Set.indicator_of_notMem hxi, hzero x hx hxi]; ring
  rw [hLHS, hpeel1, hfibre, hflat]
  rw [← mul_assoc, div_mul_cancel₀ M1 (ne_of_gt hV)]

end Work.BoseFixB1S
