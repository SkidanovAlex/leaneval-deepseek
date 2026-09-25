import Mathlib
import Submission.Work.BourgainPlan.Maximal.poly_block_defs
import Submission.Work.BourgainPlan.Maximal.poly_block_cap
import Submission.Work.BourgainPlan.Maximal.poly_weight_cap_block
import Submission.Work.BourgainPlan.Maximal.polyErrNorm_tsum_le
import Submission.Work.BourgainPlan.Maximal.poly_sharp_core_periodic
import Submission.Work.BourgainPlan.Maximal.polyBlockCore_eq_weighted
import Submission.Work.BourgainPlan.Maximal.polyBlockT_sep
import Submission.Work.BourgainPlan.Maximal.polyActIdx_card_le_one
import Submission.Work.BourgainPlan.Maximal.norm_polyBlockErr_le_actIdx
import Submission.Work.BourgainPlan.Maximal.poly_profile_replace_sharp

/-!
# The per-block `ℓ²` maximal estimate for the general-polynomial model

This is the analytic core of the model maximal inequality (Bourgain 1989, §6, (6.19)–(6.30)).
The block model is split into the *sharp core* (a weighted periodised-neighbourhood sum, controlled
by Bourgain's multi-frequency lemma via `weighted_core_maximal`) and the *profile error* (controlled
by the `ℓ¹`-in-scale summability of the profile-replacement error), plus a finite crude part below
the cutoff scale.
-/

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Commons.Analysis.ExponentialSums
open Commons.Analysis.Fourier (maximal_l2_of_fixed_multiplier)

/-! ## The error multiplier and its two bounds -/

/-- The profile-replacement error multiplier of the `m`-th block, switched on only from the cutoff
scale `K₀`. -/
noncomputable def polyErrMultCut (P : Polynomial ℤ) (m K₀ K : ℕ) (θ : ℝ) : ℂ :=
  if K₀ ≤ K then polyErrMult P m K θ else 0

lemma measurable_polyErrMultCut (P : Polynomial ℤ) (m K₀ K : ℕ) :
    Measurable (polyErrMultCut P m K₀ K) := by
  unfold polyErrMultCut
  exact Measurable.ite (by measurability) (measurable_polyErrMult P m K) measurable_const

lemma norm_polyErrMultCut_le (P : Polynomial ℤ) {m K₀ K : ℕ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ θ, ‖polyBlockErr P m K θ‖ ≤ B) (θ : ℝ) :
    ‖polyErrMultCut P m K₀ K θ‖ ≤ B := by
  unfold polyErrMultCut
  split_ifs with h
  · unfold polyErrMult
    split_ifs with hθ
    · exact hB θ
    · rw [norm_zero]; exact hB0
  · rw [norm_zero]; exact hB0

/-- **The block error is square-summable in the scale, uniformly in `θ`.** -/
theorem poly_blockErr_tsum_sq_le (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff)
    (hd : 2 ≤ P.natDegree) {A Cf : ℝ} (hA : 0 < A) (hCf : 0 < Cf)
    (hAcap : ∀ (m q a : ℕ) (l : ℤ), 2^m ≤ q → q < 2^(m+1) → Nat.gcd a q = 1 →
      l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff →
      ‖polyWeight P (q * P.leadingCoeff.toNat) (a + l * q)‖
        ≤ A * (2:ℝ)^(-(m:ℝ) * polySig P))
    (hCf' : ∀ (q a : ℕ) (l : ℤ) (θ : ℝ),
      (∑' K : ℕ, polyErrNorm P q a l K θ) ≤ ENNReal.ofReal Cf)
    {K₁ : ℕ} (hK₁ : 4 ≤ K₁) (hcont : ∀ m k : ℕ, K₁ + 4*m ≤ k →
      (P.leadingCoeff : ℝ) * (polyDil P k)⁻¹ ≤ polyArcRad P k)
    (m : ℕ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∑' K : ℕ, ‖polyErrMultCut P m (K₁ + 4*m) K θ‖ₑ ^ 2)
      ≤ ENNReal.ofReal ((A * (Cf + 1) * (2:ℝ)^(-(m:ℝ) * polySig P)) ^ 2) := by
  set K₀ : ℕ := K₁ + 4*m with hK₀
  set cap : ℝ := A * (2:ℝ)^(-(m:ℝ) * polySig P) with hcap
  have hcap0 : 0 ≤ cap := by rw [hcap]; positivity
  have hcardone : (polyActIdx P m K₀ θ).card ≤ 1 := by
    refine polyActIdx_card_le_one P hd ?_ θ
    omega
  -- the pointwise bound of the error by the active profile errors
  have hpoint : ∀ K : ℕ, K₀ ≤ K →
      ‖polyBlockErr P m K θ‖
        ≤ ∑ p ∈ polyActIdx P m K₀ θ,
            cap * polyErrVal P
              (θ - (((p.1.2:ℝ)/(p.1.1:ℝ) + (p.2:ℝ)) / (P.leadingCoeff:ℝ))) K := by
    intro K hK
    have h1 := norm_polyBlockErr_le_actIdx P hc hd (k := K) (hcont m K (by omega))
      (m := m) (by omega) θ hθ0 hθ1
    have h2 : ∑ p ∈ polyActIdx P m K θ,
          ‖polyWeight P (p.1.1 * P.leadingCoeff.toNat) (p.1.2 + p.2 * p.1.1)‖ *
            polyErrVal P (θ - (((p.1.2:ℝ)/(p.1.1:ℝ) + (p.2:ℝ)) / (P.leadingCoeff:ℝ))) K
        ≤ ∑ p ∈ polyActIdx P m K₀ θ,
            cap * polyErrVal P
              (θ - (((p.1.2:ℝ)/(p.1.1:ℝ) + (p.2:ℝ)) / (P.leadingCoeff:ℝ))) K := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (polyActIdx_subset hd hK) ?_) ?_
      · intro p hp hnp
        exact mul_nonneg (norm_nonneg _) (by unfold polyErrVal; positivity)
      · refine Finset.sum_le_sum (fun p hp => ?_)
        refine mul_le_mul_of_nonneg_right ?_ (by unfold polyErrVal; positivity)
        rw [mem_polyActIdx, mem_polyAllIdx] at hp
        obtain ⟨⟨hpb, hpl⟩, _⟩ := hp
        obtain ⟨hm1, hm2, ha, hgcd⟩ := mem_blockPair.mp hpb
        exact hAcap m p.1.1 p.1.2 p.2 hm1 hm2 hgcd hpl
    exact le_trans h1 h2
  -- the ENNReal form
  have hpointE : ∀ K : ℕ, K₀ ≤ K →
      ‖polyBlockErr P m K θ‖ₑ ≤ ∑ p ∈ polyActIdx P m K₀ θ,
          ENNReal.ofReal cap * polyErrNorm P p.1.1 p.1.2 p.2 K θ := by
    intro K hK
    rw [enorm_eq_ofReal_norm''']
    refine le_trans (ENNReal.ofReal_le_ofReal (hpoint K hK)) ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun p _ =>
      mul_nonneg hcap0 (by unfold polyErrVal; positivity))]
    refine Finset.sum_le_sum (fun p hp => ?_)
    rw [polyErrNorm, ENNReal.ofReal_mul hcap0]
  -- the sum over the scales
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le (fun s => ?_)
  have hsplit : ∑ K ∈ s, ‖polyErrMultCut P m K₀ K θ‖ₑ ^ 2
      = ∑ K ∈ s.filter (fun K => K₀ ≤ K), ‖polyBlockErr P m K θ‖ₑ ^ 2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun K _ => ?_)
    by_cases hK : K₀ ≤ K
    · rw [if_pos hK]
      unfold polyErrMultCut
      rw [if_pos hK]
      unfold polyErrMult
      rw [if_pos ⟨hθ0, hθ1⟩]
    · rw [if_neg hK]
      unfold polyErrMultCut
      rw [if_neg hK]
      simp
  rw [hsplit]
  have hstep : ∀ K ∈ s.filter (fun K => K₀ ≤ K),
      ‖polyBlockErr P m K θ‖ₑ ^ 2
        ≤ (∑ p ∈ polyActIdx P m K₀ θ,
            ENNReal.ofReal cap * polyErrNorm P p.1.1 p.1.2 p.2 K θ) ^ 2 := by
    intro K hK
    rw [Finset.mem_filter] at hK
    exact pow_le_pow_left₀ (by positivity) (hpointE K hK.2) 2
  calc ∑ K ∈ s.filter (fun K => K₀ ≤ K), ‖polyBlockErr P m K θ‖ₑ ^ 2
      ≤ ∑ K ∈ s.filter (fun K => K₀ ≤ K),
          (∑ p ∈ polyActIdx P m K₀ θ,
            ENNReal.ofReal cap * polyErrNorm P p.1.1 p.1.2 p.2 K θ) ^ 2 :=
        Finset.sum_le_sum hstep
    _ ≤ ∑' K : ℕ, (∑ p ∈ polyActIdx P m K₀ θ,
            ENNReal.ofReal cap * polyErrNorm P p.1.1 p.1.2 p.2 K θ) ^ 2 :=
        ENNReal.sum_le_tsum _
    _ = ∑' K : ℕ, ∑ p ∈ polyActIdx P m K₀ θ,
            (ENNReal.ofReal cap * polyErrNorm P p.1.1 p.1.2 p.2 K θ) ^ 2 := by
        refine tsum_congr (fun K => ?_)
        rw [sq_sum_eq_of_card_le_one hcardone]
    _ = ∑ p ∈ polyActIdx P m K₀ θ, ∑' K : ℕ,
            (ENNReal.ofReal cap * polyErrNorm P p.1.1 p.1.2 p.2 K θ) ^ 2 :=
        ennreal_tsum_finsetSum _ _
    _ = ∑ p ∈ polyActIdx P m K₀ θ, (ENNReal.ofReal cap)^2 *
            ∑' K : ℕ, (polyErrNorm P p.1.1 p.1.2 p.2 K θ) ^ 2 := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr (fun K => by rw [mul_pow])
    _ ≤ ∑ p ∈ polyActIdx P m K₀ θ, (ENNReal.ofReal cap)^2 *
            (∑' K : ℕ, polyErrNorm P p.1.1 p.1.2 p.2 K θ) ^ 2 := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        exact mul_le_mul_right sq_le_tsum_sq _
    _ ≤ (ENNReal.ofReal cap)^2 * (ENNReal.ofReal Cf)^2 := by
        calc ∑ p ∈ polyActIdx P m K₀ θ, (ENNReal.ofReal cap)^2 *
              (∑' K : ℕ, polyErrNorm P p.1.1 p.1.2 p.2 K θ) ^ 2
            ≤ ∑ _p ∈ polyActIdx P m K₀ θ,
                (ENNReal.ofReal cap)^2 * (ENNReal.ofReal Cf)^2 := by
              refine Finset.sum_le_sum (fun p hp => ?_)
              exact mul_le_mul_right (pow_le_pow_left₀ (by positivity)
                (hCf' p.1.1 p.1.2 p.2 θ) 2) _
          _ = ((polyActIdx P m K₀ θ).card : ℝ≥0∞) *
                ((ENNReal.ofReal cap)^2 * (ENNReal.ofReal Cf)^2) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ 1 * ((ENNReal.ofReal cap)^2 * (ENNReal.ofReal Cf)^2) := by
              gcongr
              exact_mod_cast hcardone
          _ = (ENNReal.ofReal cap)^2 * (ENNReal.ofReal Cf)^2 := one_mul _
    _ ≤ ENNReal.ofReal ((A * (Cf + 1) * (2:ℝ)^(-(m:ℝ) * polySig P)) ^ 2) := by
        have hd0 : (0:ℝ) < (2:ℝ)^(-(m:ℝ) * polySig P) := Real.rpow_pos_of_pos (by norm_num) _
        have hreal : cap ^ 2 * Cf ^ 2 ≤ (A * (Cf + 1) * (2:ℝ)^(-(m:ℝ) * polySig P)) ^ 2 := by
          rw [hcap]
          nlinarith [hA, hCf, hd0, sq_nonneg (Cf * (2:ℝ)^(-(m:ℝ) * polySig P)),
            sq_nonneg (A * (2:ℝ)^(-(m:ℝ) * polySig P))]
        calc (ENNReal.ofReal cap)^2 * (ENNReal.ofReal Cf)^2
            = ENNReal.ofReal (cap^2 * Cf^2) := by
              rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (by positivity),
                ← ENNReal.ofReal_mul (by positivity)]
          _ ≤ ENNReal.ofReal ((A * (Cf + 1) * (2:ℝ)^(-(m:ℝ) * polySig P)) ^ 2) :=
              ENNReal.ofReal_le_ofReal hreal

/-- **The real-valued square-summability of the cut error family.** -/
lemma polyErrMultCut_hsum (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff)
    (hd : 2 ≤ P.natDegree) {A Cf : ℝ} (hA : 0 < A) (hCf : 0 < Cf)
    (hAcap : ∀ (m q a : ℕ) (l : ℤ), 2^m ≤ q → q < 2^(m+1) → Nat.gcd a q = 1 →
      l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff →
      ‖polyWeight P (q * P.leadingCoeff.toNat) (a + l * q)‖
        ≤ A * (2:ℝ)^(-(m:ℝ) * polySig P))
    (hCf' : ∀ (q a : ℕ) (l : ℤ) (θ : ℝ),
      (∑' K : ℕ, polyErrNorm P q a l K θ) ≤ ENNReal.ofReal Cf)
    {K₁ : ℕ} (hK₁ : 4 ≤ K₁) (hcont : ∀ m k : ℕ, K₁ + 4*m ≤ k →
      (P.leadingCoeff : ℝ) * (polyDil P k)⁻¹ ≤ polyArcRad P k)
    (m : ℕ) (θ : ℝ) :
    Summable (fun K : ℕ => ‖polyErrMultCut P m (K₁ + 4*m) K θ‖ ^ 2) ∧
      (∑' K : ℕ, ‖polyErrMultCut P m (K₁ + 4*m) K θ‖ ^ 2)
        ≤ (A * (Cf + 1) * (2:ℝ)^(-(m:ℝ) * polySig P)) ^ 2 := by
  set E : ℝ := A * (Cf + 1) * (2:ℝ)^(-(m:ℝ) * polySig P) with hE
  have hE0 : (0:ℝ) ≤ E ^ 2 := sq_nonneg E
  by_cases hθ : 0 < θ ∧ θ < 1
  · have hmain := poly_blockErr_tsum_sq_le P hc hd hA hCf hAcap hCf' hK₁ hcont m θ hθ.1 hθ.2
    have hfin : ∀ t : Finset ℕ,
        ∑ K ∈ t, ‖polyErrMultCut P m (K₁ + 4*m) K θ‖ ^ 2 ≤ E ^ 2 := by
      intro t
      have hmain' : (∑' K : ℕ, ‖polyErrMultCut P m (K₁ + 4*m) K θ‖ₑ ^ (2:ℝ))
          ≤ ENNReal.ofReal (E ^ 2) := by
        rw [hE]
        rw [tsum_congr (fun K => ENNReal.rpow_two _)]
        exact hmain
      have h1 : ∑ K ∈ t, ‖polyErrMultCut P m (K₁ + 4*m) K θ‖ₑ ^ (2:ℝ)
          ≤ ENNReal.ofReal (E ^ 2) := le_trans (ENNReal.sum_le_tsum t) hmain'
      rw [Finset.sum_congr rfl
        (fun K _ => Commons.Analysis.Fourier.enorm_complex_pow_two _)] at h1
      rw [← ENNReal.ofReal_sum_of_nonneg (fun K _ => sq_nonneg _)] at h1
      exact (ENNReal.ofReal_le_ofReal_iff hE0).mp h1
    constructor
    · exact summable_of_sum_range_le (fun K => sq_nonneg _)
        (fun n => by simpa using hfin (Finset.range n))
    · exact Real.tsum_le_of_sum_range_le (fun K => sq_nonneg _)
        (fun n => by simpa using hfin (Finset.range n))
  · have hz : ∀ K : ℕ, polyErrMultCut P m (K₁ + 4*m) K θ = 0 := by
      intro K
      rw [polyErrMultCut]
      split_ifs with hK
      · rw [polyErrMult, if_neg hθ]
      · rfl
    constructor
    · simpa [hz] using (summable_zero : Summable (fun _ : ℕ => (0:ℝ)))
    · have hz' : (∑' K : ℕ, ‖polyErrMultCut P m (K₁ + 4*m) K θ‖ ^ 2) = 0 := by
        rw [show (fun K : ℕ => ‖polyErrMultCut P m (K₁ + 4*m) K θ‖ ^ 2)
            = fun _ : ℕ => (0:ℝ) from funext (fun K => by rw [hz K]; norm_num)]
        rw [tsum_zero]
      rw [hz']
      exact hE0

/-- **The error maximal function of a block.** -/
theorem polyErrMultCut_maximal_le (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff)
    (hd : 2 ≤ P.natDegree) {A Cf : ℝ} (hA : 0 < A) (hCf : 0 < Cf)
    (hAcap : ∀ (m q a : ℕ) (l : ℤ), 2^m ≤ q → q < 2^(m+1) → Nat.gcd a q = 1 →
      l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff →
      ‖polyWeight P (q * P.leadingCoeff.toNat) (a + l * q)‖
        ≤ A * (2:ℝ)^(-(m:ℝ) * polySig P))
    (hCf' : ∀ (q a : ℕ) (l : ℤ) (θ : ℝ),
      (∑' K : ℕ, polyErrNorm P q a l K θ) ≤ ENNReal.ofReal Cf)
    {K₁ : ℕ} (hK₁ : 4 ≤ K₁) (hcont : ∀ m k : ℕ, K₁ + 4*m ≤ k →
      (P.leadingCoeff : ℝ) * (polyDil P k)⁻¹ ≤ polyArcRad P k)
    (m : ℕ) (g : ℤ → ℂ) (s : Finset ℤ) (hgs : ∀ n, n ∉ s → g n = 0) :
    ∫⁻ x : ℤ, (⨆ K : ℕ, ‖∫ θ in (0:ℝ)..1, polyErrMultCut P m (K₁ + 4*m) K θ *
        (∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))
        * Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ)))‖ₑ) ^ (2:ℝ)
      ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (2 * (A * (Cf + 1) * (2:ℝ)^(-(m:ℝ) * polySig P)) ^ 2) *
        ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  set E : ℝ := A * (Cf + 1) * (2:ℝ)^(-(m:ℝ) * polySig P) with hE
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hcap0 : (0:ℝ) ≤ A * (2:ℝ)^(-(m:ℝ) * polySig P) := by positivity
  have hcardone : ∀ θ : ℝ, (polyActIdx P m (K₁ + 4*m) θ).card ≤ 1 := fun θ =>
    polyActIdx_card_le_one P hd (by omega) θ
  have hbound : ∀ K : ℕ, ∃ C : ℝ, ∀ θ : ℝ, ‖polyErrMultCut P m (K₁ + 4*m) K θ‖ ≤ C := by
    intro K
    by_cases hK : K₁ + 4*m ≤ K
    · refine ⟨2 * (A * (2:ℝ)^(-(m:ℝ) * polySig P)), fun θ => ?_⟩
      by_cases hθ : 0 < θ ∧ θ < 1
      · rw [polyErrMultCut, if_pos hK, polyErrMult, if_pos hθ]
        have h1 := norm_polyBlockErr_le_actIdx P hc hd (k := K) (hcont m K hK)
          (m := m) (by omega) θ hθ.1 hθ.2
        have h2 : ∑ p ∈ polyActIdx P m K θ,
              ‖polyWeight P (p.1.1 * P.leadingCoeff.toNat) (p.1.2 + p.2 * p.1.1)‖ *
                polyErrVal P (θ - (((p.1.2:ℝ)/(p.1.1:ℝ) + (p.2:ℝ)) / (P.leadingCoeff:ℝ))) K
            ≤ 2 * (A * (2:ℝ)^(-(m:ℝ) * polySig P)) := by
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (polyActIdx_subset hd hK) ?_) ?_
          · intro p hp hnp
            exact mul_nonneg (norm_nonneg _) (by unfold polyErrVal; positivity)
          · calc ∑ p ∈ polyActIdx P m (K₁ + 4*m) θ,
                ‖polyWeight P (p.1.1 * P.leadingCoeff.toNat) (p.1.2 + p.2 * p.1.1)‖ *
                  polyErrVal P (θ - (((p.1.2:ℝ)/(p.1.1:ℝ) + (p.2:ℝ)) / (P.leadingCoeff:ℝ))) K
                ≤ ∑ _p ∈ polyActIdx P m (K₁ + 4*m) θ,
                    (A * (2:ℝ)^(-(m:ℝ) * polySig P)) * 2 := by
                  refine Finset.sum_le_sum (fun p hp => ?_)
                  refine mul_le_mul ?_ ?_ (by unfold polyErrVal; positivity) hcap0
                  · rw [mem_polyActIdx, mem_polyAllIdx] at hp
                    obtain ⟨⟨hpb, hpl⟩, _⟩ := hp
                    obtain ⟨hm1, hm2, ha, hgcd⟩ := mem_blockPair.mp hpb
                    exact hAcap m p.1.1 p.1.2 p.2 hm1 hm2 hgcd hpl
                  · unfold polyErrVal
                    exact le_trans (norm_sub_le _ _) (by
                      have h3 : ‖(if |polyDil P K *
                          (θ - (((p.1.2:ℝ)/(p.1.1:ℝ) + (p.2:ℝ)) / (P.leadingCoeff:ℝ)))| ≤ 1
                          then (1:ℂ) else 0)‖ ≤ 1 := by split_ifs <;> simp
                      linarith [norm_polyProfile_le_one P (2^K)
                        (θ - (((p.1.2:ℝ)/(p.1.1:ℝ) + (p.2:ℝ)) / (P.leadingCoeff:ℝ)))])
              _ = ((polyActIdx P m (K₁ + 4*m) θ).card : ℝ) * ((A * (2:ℝ)^(-(m:ℝ) * polySig P)) * 2) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ 1 * ((A * (2:ℝ)^(-(m:ℝ) * polySig P)) * 2) := by
                  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                  exact_mod_cast hcardone θ
              _ = 2 * (A * (2:ℝ)^(-(m:ℝ) * polySig P)) := by ring
        linarith
      · rw [polyErrMultCut, if_pos hK, polyErrMult, if_neg hθ, norm_zero]; positivity
    · refine ⟨1, fun θ => ?_⟩
      rw [polyErrMultCut, if_neg hK, norm_zero]; norm_num
  have hsum : ∀ θ, Summable (fun K : ℕ => ‖polyErrMultCut P m (K₁ + 4*m) K θ‖ ^ 2) ∧
      ∑' K : ℕ, ‖polyErrMultCut P m (K₁ + 4*m) K θ‖ ^ 2 ≤ E ^ 2 := by
    intro θ
    rw [hE]
    exact polyErrMultCut_hsum P hc hd hA hCf hAcap hCf' hK₁ hcont m θ
  have hsquare := multiplier_square_function_l2'
    (fun K => polyErrMultCut P m (K₁ + 4*m) K) E
    (fun K => measurable_polyErrMultCut P m (K₁ + 4*m) K) hbound hsum g s hgs
  calc ∫⁻ x : ℤ, (⨆ K : ℕ, ‖∫ θ in (0:ℝ)..1, polyErrMultCut P m (K₁ + 4*m) K θ *
        (∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))
        * Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ)))‖ₑ) ^ (2:ℝ)
      ∂MeasureTheory.Measure.count
      ≤ ∫⁻ x : ℤ, 2 * ∑' K : ℕ, ‖∫ θ in (0:ℝ)..1, polyErrMultCut P m (K₁ + 4*m) K θ *
        (∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))
        * Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ)))‖ₑ ^ (2:ℝ)
        ∂MeasureTheory.Measure.count :=
        lintegral_mono (fun x => by
          simp only [ENNReal.rpow_two]
          exact sq_iSup_le_two_tsum_sq)
    _ = 2 * ∫⁻ x : ℤ, ∑' K : ℕ, ‖∫ θ in (0:ℝ)..1, polyErrMultCut P m (K₁ + 4*m) K θ *
        (∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))
        * Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ)))‖ₑ ^ (2:ℝ)
        ∂MeasureTheory.Measure.count :=
        lintegral_const_mul' 2 _ (by norm_num)
    _ ≤ 2 * (ENNReal.ofReal (E ^ 2) *
          ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) :=
        mul_le_mul_right hsquare 2
    _ = ENNReal.ofReal (2 * E ^ 2) *
          ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
        have h2 : (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) := by norm_num
        rw [h2, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    _ = ENNReal.ofReal (2 * (A * (Cf + 1) * (2:ℝ)^(-(m:ℝ) * polySig P)) ^ 2) *
          ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by rw [hE]

lemma polyTkBlockMax_eq_zero_of_lt (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ) {m k : ℕ}
    (hk : k < 4*m) (x : ℤ) : polyTkBlockMax P g s m k x = 0 := by
  unfold polyTkBlockMax
  simp only [polyModelQBlock_eq_zero_of_lt P hk]
  simp

lemma polyBlockT_card_le (P : Polynomial ℤ) (m : ℕ) :
    (polyBlockT P m).card ≤ P.leadingCoeff.toNat * 2^(2*m+1) := by
  rw [polyBlockT]
  calc (Finset.image _ (blockPair m ×ˢ Finset.range P.leadingCoeff.toNat)).card
      ≤ (blockPair m ×ˢ Finset.range P.leadingCoeff.toNat).card := Finset.card_image_le
    _ = (blockPair m).card * P.leadingCoeff.toNat := by
        rw [Finset.card_product, Finset.card_range]
    _ ≤ 2^(2*m+1) * P.leadingCoeff.toNat := Nat.mul_le_mul_right _ (blockPair_card_le m)
    _ = P.leadingCoeff.toNat * 2^(2*m+1) := Nat.mul_comm _ _

lemma log_polyBlockT_le (P : Polynomial ℤ) (hc : 0 ≤ P.leadingCoeff) (m : ℕ) :
    Real.log (((polyBlockT P m).card : ℝ) + 2)
      ≤ ((P.leadingCoeff.toNat : ℝ) + 5) * ((m : ℝ) + 2) := by
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have h1 : ((polyBlockT P m).card : ℝ) + 2
      ≤ (((P.leadingCoeff.toNat : ℝ) + 2) * (2:ℝ)^(2*m+1)) := by
    have h2 : ((polyBlockT P m).card : ℝ) ≤ (P.leadingCoeff.toNat : ℝ) * (2:ℝ)^(2*m+1) := by
      have := polyBlockT_card_le P m
      calc ((polyBlockT P m).card : ℝ) ≤ ((P.leadingCoeff.toNat * 2^(2*m+1) : ℕ) : ℝ) := by
            exact_mod_cast this
        _ = (P.leadingCoeff.toNat : ℝ) * (2:ℝ)^(2*m+1) := by push_cast; ring
    have h3 : (1:ℝ) ≤ (2:ℝ)^(2*m+1) := one_le_pow₀ (by norm_num)
    have h4 : (0:ℝ) ≤ (P.leadingCoeff.toNat : ℝ) := Nat.cast_nonneg _
    nlinarith [h2, h3, h4]
  have h5 : (0:ℝ) < ((P.leadingCoeff.toNat : ℝ) + 2) * (2:ℝ)^(2*m+1) := by positivity
  calc Real.log (((polyBlockT P m).card : ℝ) + 2)
      ≤ Real.log (((P.leadingCoeff.toNat : ℝ) + 2) * (2:ℝ)^(2*m+1)) :=
        Real.log_le_log (by positivity) h1
    _ = Real.log (((P.leadingCoeff.toNat : ℝ) + 2)) + Real.log ((2:ℝ)^(2*m+1)) := by
        rw [Real.log_mul (by positivity) (by positivity)]
    _ ≤ ((P.leadingCoeff.toNat : ℝ) + 2) + ((2*m+1 : ℕ) : ℝ) * Real.log 2 := by
        gcongr
        · have := Real.log_le_sub_one_of_pos
            (show (0:ℝ) < (P.leadingCoeff.toNat : ℝ) + 2 by positivity)
          linarith
        · rw [Real.log_pow]
    _ ≤ ((P.leadingCoeff.toNat : ℝ) + 5) * ((m : ℝ) + 2) := by
        have h6 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
          linarith
        have h7 : (0:ℝ) ≤ ((2*m+1 : ℕ) : ℝ) := Nat.cast_nonneg _
        have h8 : (0:ℝ) ≤ (P.leadingCoeff.toNat : ℝ) := Nat.cast_nonneg _
        push_cast
        nlinarith [h6, h7, h8, hm0]

lemma lintegral_polyTkBlock_sq_le (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ)
    (hgs : ∀ n, n ∉ s → g n = 0) (m k : ℕ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ θ : ℝ, ‖polyModelQBlock P m (2^k) θ‖ ≤ B) :
    ∫⁻ x : ℤ, ‖polyTkBlockMax P g s m k x‖ₑ ^ (2:ℝ)
        ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (B ^ 2) * ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ)
        ∂MeasureTheory.Measure.count := by
  set mf : ℕ → ℝ → ℂ := fun j θ =>
    if j = 0 then (starRingEnd ℂ (polyModelQBlock P m (2^k) θ)) else 0 with hmf
  have hmfm : ∀ j : ℕ, Measurable (mf j) := by
    intro j
    by_cases hj : j = 0
    · rw [hmf]
      simp only [hj, if_true]
      exact Complex.continuous_conj.measurable.comp (measurable_polyModelQBlock P m (2^k))
    · rw [hmf]
      simp only [hj, if_false]
      exact measurable_const
  have hb : ∀ j : ℕ, ∃ C : ℝ, ∀ θ : ℝ, ‖mf j θ‖ ≤ C := by
    intro j
    by_cases hj : j = 0
    · refine ⟨B, fun θ => ?_⟩
      rw [hmf]
      simp only [hj, if_true, Complex.norm_conj]
      exact hB θ
    · refine ⟨1, fun θ => ?_⟩
      rw [hmf]
      simp only [hj, if_false, norm_zero]
      norm_num
  have hsum : ∀ θ : ℝ, Summable (fun j : ℕ => ‖mf j θ‖ ^ 2) ∧
      ∑' j : ℕ, ‖mf j θ‖ ^ 2 ≤ B ^ 2 := by
    intro θ
    constructor
    · refine summable_of_ne_finset_zero (s := {0}) (fun j hj => ?_)
      rw [Finset.mem_singleton] at hj
      rw [hmf]
      simp only [hj, if_false, norm_zero]
      norm_num
    · rw [tsum_eq_single 0 (fun j hj => by
        rw [hmf]
        simp only [hj, if_false, norm_zero]
        norm_num)]
      rw [hmf]
      simp only [if_true, Complex.norm_conj]
      exact pow_le_pow_left₀ (norm_nonneg _) (hB θ) 2
  have hmain := multiplier_square_function_l2' mf B hmfm hb hsum g s hgs
  have hcongr : ∀ x : ℤ, (∑' j : ℕ, ‖∫ θ in (0:ℝ)..1, mf j θ *
        (∑ n ∈ s, g n * Complex.exp (2 * Real.pi * Complex.I * ((n:ℤ):ℂ) * (θ:ℂ))) *
        Complex.exp (-(2 * Real.pi * Complex.I * (x:ℂ) * (θ:ℂ)))‖ₑ ^ (2:ℝ))
      = ‖polyTkBlockMax P g s m k x‖ₑ ^ (2:ℝ) := by
    intro x
    rw [tsum_eq_single 0 (fun j hj => by
      rw [hmf]
      simp only [hj, if_false]
      simp)]
    rw [hmf]
    simp only [if_true]
    rw [polyTkBlockMax]
    simp only [mul_assoc]
  calc ∫⁻ x : ℤ, ‖polyTkBlockMax P g s m k x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count
      = ∫⁻ x : ℤ, (∑' j : ℕ, ‖∫ θ in (0:ℝ)..1, mf j θ *
          (∑ n ∈ s, g n * Complex.exp (2 * Real.pi * Complex.I * ((n:ℤ):ℂ) * (θ:ℂ))) *
          Complex.exp (-(2 * Real.pi * Complex.I * (x:ℂ) * (θ:ℂ)))‖ₑ ^ (2:ℝ))
          ∂MeasureTheory.Measure.count := by
        refine lintegral_congr (fun x => ?_)
        exact (hcongr x).symm
    _ ≤ ENNReal.ofReal (B ^ 2) * ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := hmain


end Work.BourgainPlan.Maximal
