import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.coeff_eq_zero_of_invariant
import Submission.Work.EQ.finsum_pow_eq_eq_sum_range

/-! Guidance from the project lead (the requester):

ROUTE: read cftquad-src design copy at Submission/Work/EQ/DESIGN_CCM.md (lead's design, trace route for rational_of_compact_cycle). Siblings run in parallel.

# meromorphicAt_rootSum: summing a meromorphic germ over k-th roots (1–2.5k, pure analysis)

**Claim.** Let `g` be meromorphic at `0`. Then `R(u) := ∑ g ζ`, summed over the `k` roots
`ζ ≠ 0` of `u₁ + κζᵏ = u`, is meromorphic at `u₁`.

Proof (implemented below). Choose `M ≥ 0` divisible by `k` with `φ(ζ) = ζᴹ g ζ` analytic at `0`,
and a primitive `k`-th root of unity `η`. Put `Φ(t) = ∑_{j<k} φ(ηʲ t)`, analytic at `0` and
invariant under `t ↦ η t`, and `H(t) = κᴹ t^{M(k-1)} Φ(t)`, also analytic at `0` and invariant.
`Work.EQ.coeff_eq_zero_of_invariant` shows that the power-series coefficients of `H` vanish off
the multiples of `k`, whence (`exists_analyticAt_comp_pow_aux`) `H t = Ψ(tᵏ)` for `Ψ` analytic at
`0`. For `u ≠ u₁` and any `k`-th root `t` of `(u-u₁)/κ`, the root set is `{ηʲ t}` and
`(u-u₁)ᴹ R(u) = H(t) = Ψ((u-u₁)/κ)`; the right-hand side is analytic at `u₁`, so
`R = Ψ((u-u₁)/κ)/(u-u₁)ᴹ` near `u₁` and `R` is meromorphic there.
-/

set_option maxHeartbeats 4000000

namespace Work.EQ

open Filter _root_.Topology
open scoped Topology


/-- Shift of a sum over `range k` when the summand is `k`-periodic. -/
lemma sum_range_shift_one {M : Type*} [AddCommMonoid M] {k : ℕ} (hk : 0 < k) (f : ℕ → M)
    (hf : f k = f 0) : ∑ j ∈ Finset.range k, f (j + 1) = ∑ j ∈ Finset.range k, f j := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [Finset.sum_range_succ (fun j => f (j + 1)) m, Finset.sum_range_succ' f m, hf]

/-- `M * (k-1) + M = k * M` for `k > 0`. -/
lemma mul_pred_add (M k : ℕ) (hk : 0 < k) : M * (k - 1) + M = k * M := by
  rw [Nat.mul_sub_left_distrib, Nat.mul_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right M hk),
    Nat.mul_comm]

/-- Auxiliary descent lemma: coefficient vanishing is taken as a hypothesis. -/
theorem exists_analyticAt_comp_pow_aux {H : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt H p 0) {k : ℕ} (hk : 0 < k)
    (hcoeff : ∀ n, ¬ k ∣ n → p.coeff n = 0) :
    ∃ Ψ : ℂ → ℂ, AnalyticAt ℂ Ψ 0 ∧ ∀ᶠ z in 𝓝 (0 : ℂ), H z = Ψ (z ^ k) := by
  obtain ⟨r, hr⟩ := hp
  set c : ℕ → ℂ := fun l => p.coeff (k * l) with hc
  set q : FormalMultilinearSeries ℂ ℂ ℂ :=
    fun l => ContinuousMultilinearMap.mkPiRing ℂ (Fin l) (c l) with hq
  obtain ⟨R, hRposE, hRlt⟩ : ∃ R : NNReal, 0 < (R : ENNReal) ∧ (R : ENNReal) < r :=
    ENNReal.lt_iff_exists_nnreal_btwn.mp hr.r_pos
  have hRpos : 0 < R := ENNReal.coe_pos.mp hRposE
  obtain ⟨C, hCpos, hC⟩ := p.norm_mul_pow_le_of_lt_radius (r := R) (lt_of_lt_of_le hRlt hr.r_le)
  have hqcoeff : ∀ l, q.coeff l = c l := by
    intro l
    simp only [FormalMultilinearSeries.coeff, hq, ContinuousMultilinearMap.mkPiRing_apply]
    simp
  have hqnorm : ∀ l, ‖q l‖ = ‖c l‖ := by
    intro l
    rw [FormalMultilinearSeries.norm_apply_eq_norm_coef, hqcoeff l]
  have hqbound : ∀ l, ‖q l‖ * ((R ^ k : NNReal) : ℝ) ^ l ≤ C := by
    intro l
    rw [hqnorm]
    have h2 : ((R ^ k : NNReal) : ℝ) = (R : ℝ) ^ k := by push_cast; ring
    rw [h2, ← pow_mul]
    have h3 : ‖c l‖ = ‖p (k * l)‖ := by
      rw [hc]
      simp only
      rw [FormalMultilinearSeries.norm_apply_eq_norm_coef]
    rw [h3]
    exact hC (k * l)
  have hqrad : ((R ^ k : NNReal) : ENNReal) ≤ q.radius :=
    FormalMultilinearSeries.le_radius_of_bound q C hqbound
  have hqpos : (0 : ENNReal) < q.radius := by
    refine lt_of_lt_of_le ?_ hqrad
    rw [ENNReal.coe_pos]
    exact pow_pos hRpos k
  have hqsum : ∀ s : ℂ, q.sum s = ∑' l, s ^ l * c l := by
    intro s
    rw [FormalMultilinearSeries.sum]
    refine tsum_congr (fun l => ?_)
    simp only [hq, ContinuousMultilinearMap.mkPiRing_apply, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rw [smul_eq_mul]
  refine ⟨q.sum, (q.hasFPowerSeriesOnBall hqpos).analyticAt, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by exact_mod_cast hRpos : (0:ℝ) < (R:ℝ))]
    with z hz
  have hzR : ‖z‖ < (R : ℝ) := by simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzr : z ∈ Metric.eball (0 : ℂ) r := by
    rw [mem_eball_zero_iff, enorm_eq_nnnorm]
    refine lt_trans ?_ hRlt
    rw [ENNReal.coe_lt_coe]
    exact_mod_cast hzR
  have h1 : H z = ∑' n, z ^ n * p.coeff n := by
    have hh : HasSum (fun n => z ^ n * p.coeff n) (H z) := by
      simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, zero_add]
        using hr.hasSum hzr
    exact hh.tsum_eq.symm
  rw [h1, hqsum]
  refine tsum_eq_tsum_of_ne_zero_bij (g := fun l => (z ^ k) ^ l * c l)
    (fun x => k * (x : ℕ)) ?_ ?_ ?_
  · intro x y hxy
    exact Subtype.ext (Nat.mul_left_cancel hk hxy)
  · intro n hn
    rw [Function.mem_support] at hn
    have hpn : p.coeff n ≠ 0 := by
      intro h0; exact hn (by rw [h0, mul_zero])
    have hzn : z ^ n ≠ 0 := by
      intro h0; exact hn (by rw [h0, zero_mul])
    have hkdvd : k ∣ n := by
      by_contra h
      exact hpn (hcoeff n h)
    have hpow : z ^ n = (z ^ k) ^ (n / k) := by
      rw [← pow_mul, Nat.mul_div_cancel' hkdvd]
    refine ⟨⟨n / k, ?_⟩, ?_⟩
    · rw [Function.mem_support, hc]
      simp only [Nat.mul_div_cancel' hkdvd]
      refine mul_ne_zero ?_ hpn
      rw [← hpow]
      exact hzn
    · exact Nat.mul_div_cancel' hkdvd
  · intro x
    simp only [hc, pow_mul]

/-- The analytic descent lemma. -/
theorem exists_analyticAt_comp_pow {H : ℂ → ℂ} (hH : AnalyticAt ℂ H 0) {k : ℕ} (hk : 0 < k)
    {η : ℂ} (hη : IsPrimitiveRoot η k) (hinv : ∀ᶠ z in 𝓝 (0 : ℂ), H (η * z) = H z) :
    ∃ Ψ : ℂ → ℂ, AnalyticAt ℂ Ψ 0 ∧ ∀ᶠ z in 𝓝 (0 : ℂ), H z = Ψ (z ^ k) := by
  obtain ⟨p, hp⟩ := hH
  exact exists_analyticAt_comp_pow_aux hp hk (fun n hn => coeff_eq_zero_of_invariant hp hk hη hinv hn)

/-- **Summing a meromorphic germ over the `k`-th roots.** If `g` is meromorphic at `0`, then
`u ↦ ∑ g ζ` over the `k` solutions `ζ ≠ 0` of `u₁ + κ ζᵏ = u` is meromorphic at `u₁`: only the
Laurent terms of degree divisible by `k` survive, and they form a Laurent series in
`(u - u₁)/κ`. -/
theorem meromorphicAt_rootSum {g : ℂ → ℂ} (hg : MeromorphicAt g 0) {k : ℕ} (hk : 0 < k)
    {κ : ℂ} (hκ : κ ≠ 0) (u₁ : ℂ) :
    MeromorphicAt (fun u => ∑ᶠ ζ ∈ {ζ : ℂ | ζ ≠ 0 ∧ u₁ + κ * ζ ^ k = u}, g ζ) u₁ := by
  classical
  obtain ⟨m, hm⟩ := hg
  have hm' : AnalyticAt ℂ (fun z => z ^ m * g z) 0 := by simpa [smul_eq_mul] using hm
  have hE : m * (k - 1) + m = k * m := mul_pred_add m k hk
  have hE2 : (k * m) * (k - 1) + k * m = k * (k * m) := mul_pred_add (k * m) k hk
  set φ : ℂ → ℂ := fun z => z ^ (k * m) * g z with hφdef
  have hφan : AnalyticAt ℂ φ 0 := by
    rw [hφdef]
    have heq : (fun z : ℂ => z ^ (k * m) * g z)
        = fun z => z ^ (m * (k - 1)) * (z ^ m * g z) := by
      funext z
      rw [← hE, pow_add, mul_assoc]
    rw [heq]
    exact (analyticAt_id.pow _).mul hm'
  obtain ⟨η, hη⟩ : ∃ η : ℂ, IsPrimitiveRoot η k :=
    ⟨Complex.exp (2 * ↑Real.pi * Complex.I / k), Complex.isPrimitiveRoot_exp k hk.ne'⟩
  set Φ : ℂ → ℂ := fun t => ∑ j ∈ Finset.range k, φ (η ^ j * t) with hΦdef
  have hΦan : AnalyticAt ℂ Φ 0 := by
    rw [hΦdef]
    have hfun : ∀ j ∈ Finset.range k, AnalyticAt ℂ (fun t : ℂ => φ (η ^ j * t)) 0 := by
      intro j hj
      have h1 : AnalyticAt ℂ (fun t : ℂ => η ^ j * t) 0 :=
        (analyticAt_const (v := η ^ j) (x := (0 : ℂ))).mul (analyticAt_id (z := (0 : ℂ)))
      have h2 : AnalyticAt ℂ φ ((fun t : ℂ => η ^ j * t) 0) := by simpa using hφan
      exact h2.comp h1
    have hsum : (fun t : ℂ => ∑ j ∈ Finset.range k, φ (η ^ j * t))
        = ∑ j ∈ Finset.range k, (fun t : ℂ => φ (η ^ j * t)) := by
      ext t
      simp [Finset.sum_apply]
    rw [hsum]
    exact Finset.analyticAt_sum (Finset.range k) hfun
  have hinvΦ : ∀ t, Φ (η * t) = Φ t := by
    intro t
    rw [hΦdef]
    simp only []
    have hfj : ∀ j, φ (η ^ j * (η * t)) = φ (η ^ (j + 1) * t) := by
      intro j
      congr 1
      rw [← mul_assoc, ← pow_succ]
    rw [Finset.sum_congr rfl (fun j hj => hfj j)]
    refine sum_range_shift_one hk (fun j => φ (η ^ j * t)) ?_
    simp [hη.pow_eq_one]
  set H : ℂ → ℂ := fun t => κ ^ (k * m) * t ^ ((k * m) * (k - 1)) * Φ t with hHdef
  have hHan : AnalyticAt ℂ H 0 := by
    rw [hHdef]
    have h1 : AnalyticAt ℂ (fun t : ℂ => κ ^ (k * m) * t ^ ((k * m) * (k - 1))) 0 :=
      (analyticAt_const (v := κ ^ (k * m)) (x := (0 : ℂ))).mul
        ((analyticAt_id (z := (0 : ℂ))).pow _)
    exact h1.mul hΦan
  have hHinv : ∀ᶠ t in 𝓝 (0 : ℂ), H (η * t) = H t := by
    refine Eventually.of_forall (fun t => ?_)
    have hηM : η ^ ((k * m) * (k - 1)) = 1 := by
      rw [show (k * m) * (k - 1) = k * (m * (k - 1)) from by ring, pow_mul, hη.pow_eq_one,
        one_pow]
    rw [hHdef]
    simp only
    rw [mul_pow, hηM, one_mul, hinvΦ t]
  obtain ⟨Ψ, hΨan, hΨeq⟩ := exists_analyticAt_comp_pow hHan hk hη hHinv
  let R : ℂ → ℂ := fun u => ∑ᶠ ζ ∈ {ζ : ℂ | ζ ≠ 0 ∧ u₁ + κ * ζ ^ k = u}, g ζ
  let rt : ℂ → ℂ := fun u => Classical.choose (IsAlgClosed.exists_pow_nat_eq ((u - u₁) / κ) hk)
  have hrt : ∀ u, (rt u) ^ k = (u - u₁) / κ := fun u =>
    Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq ((u - u₁) / κ) hk)
  have key : ∀ u, u ≠ u₁ → (u - u₁) ^ (k * m) * R u = H (rt u) := by
    intro u hu
    have hc : (u - u₁) / κ ≠ 0 := div_ne_zero (sub_ne_zero.mpr hu) hκ
    have ht0 : rt u ≠ 0 := by
      have h1 : (rt u) ^ k ≠ 0 := by rw [hrt u]; exact hc
      exact fun h0 => h1 (by rw [h0, zero_pow hk.ne'])
    have hS : {ζ : ℂ | ζ ≠ 0 ∧ u₁ + κ * ζ ^ k = u} = {ζ : ℂ | ζ ^ k = (u - u₁) / κ} := by
      ext ζ
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h0, h1⟩
        rw [eq_div_iff hκ, mul_comm]
        linear_combination h1
      · intro h
        refine ⟨?_, ?_⟩
        · intro h0; rw [h0, zero_pow hk.ne'] at h; exact hc h.symm
        · rw [h, ← mul_div_assoc, mul_div_cancel_left₀ (u - u₁) hκ]
          ring
    rw [show R u = ∑ᶠ ζ ∈ {ζ : ℂ | ζ ≠ 0 ∧ u₁ + κ * ζ ^ k = u}, g ζ from rfl, hS,
      finsum_pow_eq_eq_sum_range hk hη hc (hrt u) g]
    have hsum1 : ∑ j ∈ Finset.range k, g (η ^ j * rt u) = ((rt u) ^ (k * m))⁻¹ * Φ (rt u) := by
      have h1 : ∀ j ∈ Finset.range k,
          g (η ^ j * rt u) = ((η ^ j * rt u) ^ (k * m))⁻¹ * φ (η ^ j * rt u) := by
        intro j hj
        have hz : η ^ j * rt u ≠ 0 := mul_ne_zero (pow_ne_zero _ (hη.ne_zero hk.ne')) ht0
        rw [hφdef]
        simp only
        rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hz), one_mul]
      rw [Finset.sum_congr rfl h1]
      have h2 : ∀ j, (η ^ j) ^ (k * m) = 1 := by
        intro j
        have h3 : (η ^ j) ^ k = 1 := by
          rw [← pow_mul, Nat.mul_comm j k, pow_mul, hη.pow_eq_one, one_pow]
        rw [pow_mul, h3, one_pow]
      have h4 : ∀ j ∈ Finset.range k, ((η ^ j * rt u) ^ (k * m))⁻¹ * φ (η ^ j * rt u)
          = ((rt u) ^ (k * m))⁻¹ * φ (η ^ j * rt u) := by
        intro j hj
        rw [mul_pow, h2 j, one_mul]
      rw [Finset.sum_congr rfl h4, hΦdef]
      simp only
      rw [← Finset.mul_sum]
    rw [hsum1, hHdef]
    simp only
    have hfin : (u - u₁) ^ (k * m) * (((rt u) ^ (k * m))⁻¹ * Φ (rt u))
        = κ ^ (k * m) * (rt u) ^ ((k * m) * (k - 1)) * Φ (rt u) := by
      have hu1 : u - u₁ = κ * (rt u) ^ k := by
        rw [hrt u, ← mul_div_assoc, mul_div_cancel_left₀ (u - u₁) hκ]
      have hB : (rt u) ^ (k * (k * m)) * ((rt u) ^ (k * m))⁻¹
          = (rt u) ^ ((k * m) * (k - 1)) := by
        rw [← hE2, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht0), mul_one]
      rw [hu1, mul_pow, ← pow_mul, ← hB]
      ring
    exact hfin
  have htrend : Tendsto rt (𝓝 u₁) (𝓝 0) := by
    have h1 : Tendsto (fun u : ℂ => (u - u₁) / κ) (𝓝 u₁) (𝓝 ((u₁ - u₁) / κ)) :=
      (continuousAt_id.sub continuousAt_const).div_const κ |>.tendsto
    have h1' : Tendsto (fun u : ℂ => (u - u₁) / κ) (𝓝 u₁) (𝓝 0) := by
      simpa using h1
    have hpow : Tendsto (fun u => (rt u) ^ k) (𝓝 u₁) (𝓝 0) := by
      simpa only [hrt] using h1'
    rw [Metric.tendsto_nhds] at hpow ⊢
    intro ε hε
    filter_upwards [hpow (ε ^ k) (pow_pos hε k)] with u hu
    have hu' : ‖rt u‖ ^ k < ε ^ k := by
      simpa [dist_eq_norm, norm_pow] using hu
    simpa [dist_eq_norm] using
      (pow_lt_pow_iff_left₀ (norm_nonneg (rt u)) hε.le hk.ne').mp hu'
  set W : ℂ → ℂ := fun u => Ψ ((u - u₁) / κ) with hWdef
  have hWan : AnalyticAt ℂ W u₁ := by
    rw [hWdef]
    have h1 : AnalyticAt ℂ (fun u : ℂ => (u - u₁) / κ) u₁ := by
      have ha : AnalyticAt ℂ (fun u : ℂ => u - u₁) u₁ := by
        apply AnalyticAt.sub analyticAt_id analyticAt_const
      exact ha.div_const (c := κ)
    have h0 : AnalyticAt ℂ Ψ ((fun u : ℂ => (u - u₁) / κ) u₁) := by simpa using hΨan
    exact AnalyticAt.comp (f := fun u : ℂ => (u - u₁) / κ) (x := u₁) h0 h1
  refine MeromorphicAt.congr (f := fun u => W u / (u - u₁) ^ (k * m)) ?_ ?_
  · refine (hWan.meromorphicAt).div ?_
    have h1 : AnalyticAt ℂ (fun u : ℂ => (u - u₁) ^ (k * m)) u₁ := by
      have ha : AnalyticAt ℂ (fun u : ℂ => u - u₁) u₁ := by
        apply AnalyticAt.sub analyticAt_id analyticAt_const
      exact ha.pow _
    exact h1.meromorphicAt
  · have hev : ∀ᶠ u in 𝓝[≠] u₁, H (rt u) = Ψ ((rt u) ^ k) :=
      (htrend.mono_left nhdsWithin_le_nhds).eventually hΨeq
    filter_upwards [self_mem_nhdsWithin, hev] with u hmem hHu
    have hu : u ≠ u₁ := hmem
    change Ψ ((u - u₁) / κ) / (u - u₁) ^ (k * m) = R u
    rw [div_eq_iff (pow_ne_zero _ (sub_ne_zero.mpr hu)), mul_comm, key u hu, hHu, hrt u]

end Work.EQ
