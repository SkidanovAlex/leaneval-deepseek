import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLComp.BirkhoffDefs
import Submission.Work.EKLComp.Hopf_inequality
import Submission.Work.EKLComp.preimage_badSet
import Submission.Work.EKLComp.measurableSet_badSet
import Submission.Work.EKLComp.condExp_invariants_apply_eq
import Submission.Work.EKLComp.setIntegral_sub_condExp_eq_zero
import Submission.Work.EKLComp.posSumSet_indicator_eq_badSet
import Submission.Work.EKLComp.tendsto_zero_of_forall_rat
import Submission.Work.EKLComp.setIntegral_indicator_sub_const

/-!
# C11c: the Birkhoff pointwise ergodic theorem

Proof strategy (all from scratch; Mathlib has `birkhoffSum` but no pointwise ergodic theorem):

* write `h = E(f | invariants T)` and `g = f - h`; `h ∘ T = h` (child lemma
  `condExp_invariants_apply_eq`), so the Birkhoff averages of `h` are constantly `h`;
* `∫_U g = 0` for every invariant measurable `U` (`setIntegral_sub_condExp_eq_zero`);
* for `ε > 0` let `U_ε = badSet T g ε = {x | ∃ q ∈ ℚ, ε < q ∧ ∃ᶠ n, q < birkA T g n x}`;
  this set is exactly `T`-invariant (`preimage_badSet`), measurable (`measurableSet_badSet`),
  and Hopf's maximal inequality (`Hopf_inequality`) applied to `g̃ = U_ε.indicator (g - ε)`
  gives `0 ≤ ∫_{U_ε} g̃ = ∫_{U_ε} g - ε·μ(U_ε) = -ε·μ(U_ε)`, hence `μ(U_ε) = 0`
  (`posSumSet_indicator_eq_badSet`, `setIntegral_indicator_sub_const`);
* applying this to `g` and to `-g` gives, a.e., `∀ q ∈ ℚ_{>0}`, eventually `-q ≤ birkA T g n x ≤ q`,
  so `birkA T g n x → 0` a.e. (`tendsto_zero_of_forall_rat`);
* finally `birkA T f n x = birkA T g n x + h x` for `n ≥ 1`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped MeasureTheory BigOperators

namespace Work.EKLComp

open Work.EKLComp.Birkhoff


variable {X : Type*}

theorem birkA_sub (T : X → X) (f h : X → ℝ) (n : ℕ) (x : X) :
    birkA T (fun y => f y - h y) n x = birkA T f n x - birkA T h n x := by
  simp only [birkA, birkhoffSum, Finset.sum_sub_distrib, mul_sub]

theorem birkA_of_invariant (T : X → X) (h : X → ℝ) (hh : ∀ y, h (T y) = h y) (n : ℕ)
    (hn : n ≠ 0) (x : X) : birkA T h n x = h x := by
  have hk : ∀ k : ℕ, h (T^[k] x) = h x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', hh, ih]
  have hsum : (∑ k ∈ Finset.range n, h (T^[k] x)) = n • h x := by
    rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_const, Finset.card_range]
  simp only [birkA, birkhoffSum]
  rw [hsum, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_mul]

theorem birkA_neg (T : X → X) (f : X → ℝ) (n : ℕ) (x : X) :
    birkA T (fun y => -f y) n x = -birkA T f n x := by
  simp only [birkA, birkhoffSum, Finset.sum_neg_distrib, mul_neg]

theorem birkhoff_of_aux [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ) (f h : X → ℝ) (hfm : Measurable f) (hhm : Measurable h)
    (hfint : Integrable f μ) (hhint : Integrable h μ) (hhinv : ∀ x, h (T x) = h x)
    (hzero : ∀ U : Set X, MeasurableSet U → T ⁻¹' U = U → ∫ x in U, (f x - h x) ∂μ = 0) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkA T f n x) atTop (𝓝 (h x)) := by
  have hg_meas : Measurable (fun x => f x - h x) := hfm.sub hhm
  have hg_int : Integrable (fun x => f x - h x) μ := hfint.sub hhint
  have hbad_of : ∀ (φ : X → ℝ), Measurable φ → Integrable φ μ →
      (∀ U : Set X, MeasurableSet U → T ⁻¹' U = U → ∫ x in U, φ x ∂μ = 0) →
      ∀ ε : ℝ, 0 < ε → μ (badSet T φ ε) = 0 := by
    intro φ hφm hφi hφ0 ε hε
    have hUmeas : MeasurableSet (badSet T φ ε) := measurableSet_badSet T hT.measurable φ hφm ε
    have hinv : T ⁻¹' badSet T φ ε = badSet T φ ε := preimage_badSet T φ ε
    have hzero' : ∫ x in badSet T φ ε, φ x ∂μ = 0 := hφ0 _ hUmeas hinv
    have hφt_int : Integrable ((badSet T φ ε).indicator (fun y => φ y - ε)) μ :=
      (hφi.sub (integrable_const ε)).indicator hUmeas
    have h1 : 0 ≤ ∫ x in {x | ∃ n : ℕ, 0 < birkhoffSum T
        ((badSet T φ ε).indicator (fun y => φ y - ε)) n x},
        ((badSet T φ ε).indicator (fun y => φ y - ε)) x ∂μ :=
      Hopf_inequality μ T hT _ hφt_int
    rw [posSumSet_indicator_eq_badSet T φ ε hinv] at h1
    rw [setIntegral_indicator_sub_const μ (badSet T φ ε) hUmeas (measure_ne_top μ _) φ hφi ε, hzero'] at h1
    have hz : (μ (badSet T φ ε)).toReal = 0 :=
      le_antisymm (by nlinarith [h1, hε]) ENNReal.toReal_nonneg
    rcases (ENNReal.toReal_eq_zero_iff (μ (badSet T φ ε))).mp hz with hh | hh
    · exact hh
    · exact absurd hh (measure_ne_top μ _)
  have hupper : ∀ᵐ x ∂μ, ∀ q : ℚ, 0 < q →
      ∀ᶠ n in atTop, birkA T (fun x => f x - h x) n x ≤ (q : ℝ) := by
    rw [ae_all_iff]
    intro q
    by_cases hq : 0 < q
    · have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
      have hnull : μ (badSet T (fun x => f x - h x) ((q : ℝ) / 2)) = 0 :=
        hbad_of _ hg_meas hg_int hzero _ (by linarith [hqr])
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
      intro _
      by_contra hcon
      rw [not_eventually] at hcon
      simp only [not_le] at hcon
      exact hx ⟨q, by linarith [hqr], hcon⟩
    · exact Filter.Eventually.of_forall fun x h => absurd h hq
  have hlower : ∀ᵐ x ∂μ, ∀ q : ℚ, 0 < q →
      ∀ᶠ n in atTop, -(q : ℝ) ≤ birkA T (fun x => f x - h x) n x := by
    rw [ae_all_iff]
    intro q
    by_cases hq : 0 < q
    · have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
      have hneg0 : ∀ U : Set X, MeasurableSet U → T ⁻¹' U = U →
          ∫ x in U, -(f x - h x) ∂μ = 0 := by
        intro U hU hUT
        rw [integral_neg, hzero U hU hUT, neg_zero]
      have hnull : μ (badSet T (fun x => -(f x - h x)) ((q : ℝ) / 2)) = 0 :=
        hbad_of _ hg_meas.neg hg_int.neg hneg0 _ (by linarith [hqr])
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
      intro _
      have h1 : ∀ᶠ n in atTop, birkA T (fun y => -(f y - h y)) n x ≤ (q : ℝ) := by
        by_contra hc
        rw [not_eventually] at hc
        simp only [not_le] at hc
        exact hx ⟨q, by linarith [hqr], hc⟩
      refine h1.mono (fun n hn => ?_)
      have hb : birkA T (fun y => -(f y - h y)) n x = -birkA T (fun y => f y - h y) n x :=
        birkA_neg T _ n x
      rw [hb] at hn
      linarith
    · exact Filter.Eventually.of_forall fun x h => absurd h hq
  have hconv : ∀ᵐ x ∂μ,
      Tendsto (fun n => birkA T (fun x => f x - h x) n x) atTop (𝓝 0) :=
    (hupper.and hlower).mono fun x hx => tendsto_zero_of_forall_rat _ hx.1 hx.2
  filter_upwards [hconv] with x hx
  have hsplit : (fun n : ℕ => birkA T f n x) =ᶠ[atTop]
      (fun n : ℕ => birkA T (fun x => f x - h x) n x + h x) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
    have h1 := birkA_sub T f h n x
    rw [h1, birkA_of_invariant T h hhinv n hn' x]
    ring
  have h2 : Tendsto (fun n : ℕ => birkA T (fun x => f x - h x) n x + h x) atTop (𝓝 (0 + h x)) :=
    hx.add tendsto_const_nhds
  have h3 := h2.congr' hsplit.symm
  simpa using h3

theorem birkhoff_measurable [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ) (f : X → ℝ) (hfint : Integrable f μ) (hfm : Measurable f) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkA T f n x) atTop
      (𝓝 (condExp (MeasurableSpace.invariants T) μ f x)) := by
  refine birkhoff_of_aux μ T hT f (condExp (MeasurableSpace.invariants T) μ f) hfm ?_ hfint ?_ ?_ ?_
  · have hsm : StronglyMeasurable[MeasurableSpace.invariants T]
        (condExp (MeasurableSpace.invariants T) μ f) := stronglyMeasurable_condExp
    exact hsm.measurable.mono (MeasurableSpace.invariants_le T) le_rfl
  · exact integrable_condExp
  · intro x
    exact condExp_invariants_apply_eq μ T f x
  · intro U hU hUT
    exact setIntegral_sub_condExp_eq_zero μ T f hfint U hU hUT

theorem birkhoff_all [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ) (f : X → ℝ) (hfint : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkA T f n x) atTop
      (𝓝 (condExp (MeasurableSpace.invariants T) μ f x)) := by
  obtain ⟨f', hf'm, hf'e⟩ := hfint.aestronglyMeasurable.aemeasurable
  have hf'int : Integrable f' μ := hfint.congr hf'e
  have hmain := birkhoff_measurable μ T hT f' hf'int hf'm
  have hk : ∀ᵐ x ∂μ, ∀ k : ℕ, f (T^[k] x) = f' (T^[k] x) := by
    rw [ae_all_iff]
    intro k
    have hqmp : Measure.QuasiMeasurePreserving (T^[k]) μ μ := (hT.iterate k).quasiMeasurePreserving
    exact hqmp.ae_eq_comp hf'e
  have hae : ∀ᵐ x ∂μ, ∀ n : ℕ, birkA T f n x = birkA T f' n x := by
    filter_upwards [hk] with x hx n
    simp only [birkA, birkhoffSum]
    rw [Finset.sum_congr rfl (fun k _ => hx k)]
  have hcond : condExp (MeasurableSpace.invariants T) μ f =ᵐ[μ]
      condExp (MeasurableSpace.invariants T) μ f' := condExp_congr_ae hf'e
  filter_upwards [hmain, hae, hcond] with x hx1 hx2 hx3
  rw [hx3]
  exact hx1.congr' (Filter.Eventually.of_forall fun n => (hx2 n).symm)

theorem prove_Birkhoff : Work.EKLContract.P_Birkhoff := by
  intro X mX μ hμ T hT f hfint
  exact birkhoff_all μ T hT f hfint

end Work.EKLComp
