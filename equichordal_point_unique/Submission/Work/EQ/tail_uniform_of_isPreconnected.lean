import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.H0_tail_bounded
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.HeteroGerm
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.StableTailDefs
import Submission.Work.EQ.fan_base
import Submission.Work.EQ.germCHelpers

/-! # Uniform tails on a preconnected piece of `H0`

The main result `Work.EQ.tail_uniform_of_isPreconnected`: on a preconnected `T ⊆ H0` on which
both linearising parameters are bounded by `B`, the forward tail is the principal stable leaf
and the backward tail the principal unstable leaf from one common index on. -/

namespace Work.EQ

open Filter _root_.Topology
open scoped Topology

noncomputable section

set_option maxHeartbeats 3200000

/-- The backward tail condition: from the index `N` on, the chain follows the principal unstable
leaf, `q.1 (-n) = ugermC a h (λⁿ ψ₂ q)`. -/
def TailB (a : ℝ) (h : ℂ → ℂ) (q : ChainData) (N : ℕ) : Prop :=
  ∀ n : ℕ, N ≤ n → q.1 (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ n * q.2.2)

lemma TailB_mono {a : ℝ} {h : ℂ → ℂ} {q : ChainData} {N N' : ℕ} (hN : TailB a h q N)
    (hNN : N ≤ N') : TailB a h q N' := fun n hn => hN n (le_trans hNN hn)

section Helpers

variable {a : ℝ} {h : ℂ → ℂ} {ρ : ℝ}

/-- `eqMirror` is continuous. -/
lemma continuous_eqMirror : Continuous eqMirror := by
  unfold eqMirror; fun_prop

/-- Norm of `λ` as a complex number. -/
lemma norm_eqLamC (ha0 : 0 < a) (ha1 : a < 1) : ‖(eqLam a : ℂ)‖ = eqLam a := by
  rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (eqLam_pos' ha0 ha1).le]

private lemma norm_eqLam_pow_mul (ha0 : 0 < a) (ha1 : a < 1) (m : ℕ) (z : ℂ) :
    ‖(eqLam a : ℂ) ^ m * z‖ = (eqLam a) ^ m * ‖z‖ := by
  rw [norm_mul, norm_pow, norm_eqLamC ha0 ha1]

/-- The principal forward branch acts on the unstable germ by scaling the parameter down:
`fwdC a (ugermC a h (λu)) = ugermC a h u`. -/
lemma fwdC_ugermC_lam
    (hRP : ∀ u ∈ Metric.ball (0 : ℂ) ρ,
      RegPair a (germC a h u) (germC a h ((eqLam a : ℂ) * u)) ∧
        invBranch a true (germC a h ((eqLam a : ℂ) * u)) = germC a h u) :
    ∀ u ∈ Metric.ball (0 : ℂ) ρ,
      fwdC a (ugermC a h ((eqLam a : ℂ) * u)) = ugermC a h u := by
  intro u hu
  show fwdC a (eqMirror (germC a h ((eqLam a : ℂ) * u))) = eqMirror (germC a h u)
  rw [fwdC_mirror, (hRP u hu).2]

/-- One step of the descent on the stable (forward) side: if the successor point sits on the
principal leaf and the current point is within `1/2` of the principal branch, it *is* the
principal branch. -/
lemma step_fwd (hRP : ∀ u ∈ Metric.ball (0 : ℂ) ρ,
      RegPair a (germC a h u) (germC a h ((eqLam a : ℂ) * u)) ∧
        invBranch a true (germC a h ((eqLam a : ℂ) * u)) = germC a h u)
    {m : ℕ} {q : ChainData} (hchain : IsChain a h q)
    (htail : q.1 ((m + 1 : ℕ) : ℤ) = germC a h ((eqLam a : ℂ) ^ (m + 1) * q.2.1))
    (hclose : ‖q.1 (m : ℤ) - germC a h ((eqLam a : ℂ) ^ m * q.2.1)‖ < 1 / 2)
    (hball : (eqLam a : ℂ) ^ m * q.2.1 ∈ Metric.ball (0 : ℂ) ρ) :
    q.1 (m : ℤ) = germC a h ((eqLam a : ℂ) ^ m * q.2.1) := by
  have hcast : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
  have hreg : RegPair a (q.1 (m : ℤ)) (q.1 ((m + 1 : ℕ) : ℤ)) := by
    have := hchain.1 (m : ℤ)
    rwa [hcast] at this
  have hpow : (eqLam a : ℂ) ^ (m + 1) * q.2.1
      = (eqLam a : ℂ) * ((eqLam a : ℂ) ^ m * q.2.1) := by
    rw [pow_succ']; ring
  have hbtrue : invBranch a true (q.1 ((m + 1 : ℕ) : ℤ))
      = germC a h ((eqLam a : ℂ) ^ m * q.2.1) := by
    rw [htail, hpow]
    exact (hRP _ hball).2
  rcases H0_invParam_ge_exists_invBranch hreg.1 hreg.2.2 with hh | hh
  · rw [hh, hbtrue]
  · exfalso
    have hQnd : bsq (subO1 a (q.1 ((m + 1 : ℕ) : ℤ))) ≠ 0 := by
      simpa [bsq, subO1] using hreg.2.2
    have hsep : 1 ≤ ‖invBranch a true (q.1 ((m + 1 : ℕ) : ℤ))
        - invBranch a false (q.1 ((m + 1 : ℕ) : ℤ))‖ := invBranch_separation hQnd
    have hdist : ‖q.1 (m : ℤ) - germC a h ((eqLam a : ℂ) ^ m * q.2.1)‖
        = ‖invBranch a true (q.1 ((m + 1 : ℕ) : ℤ))
            - invBranch a false (q.1 ((m + 1 : ℕ) : ℤ))‖ := by
      rw [hh, ← hbtrue, norm_sub_rev]
    linarith [hsep, hclose, hdist]

/-- One step of the descent on the unstable (backward) side, with the forward branches. -/
lemma step_bwd (hRP : ∀ u ∈ Metric.ball (0 : ℂ) ρ,
      RegPair a (germC a h u) (germC a h ((eqLam a : ℂ) * u)) ∧
        invBranch a true (germC a h ((eqLam a : ℂ) * u)) = germC a h u)
    {m : ℕ} {q : ChainData} (hchain : IsChain a h q)
    (htail : q.1 (-((m + 1 : ℕ) : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ (m + 1) * q.2.2))
    (hclose : ‖q.1 (-(m : ℤ)) - ugermC a h ((eqLam a : ℂ) ^ m * q.2.2)‖ < 1 / 2)
    (hball : (eqLam a : ℂ) ^ m * q.2.2 ∈ Metric.ball (0 : ℂ) ρ) :
    q.1 (-(m : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ m * q.2.2) := by
  have hcast : ((-((m + 1 : ℕ) : ℤ)) + 1) = -(m : ℤ) := by push_cast; ring
  have hreg : RegPair a (q.1 (-((m + 1 : ℕ) : ℤ))) (q.1 (-(m : ℤ))) := by
    have := hchain.1 (-((m + 1 : ℕ) : ℤ))
    rwa [hcast] at this
  have hPnd : bsq (subO2 a (q.1 (-((m + 1 : ℕ) : ℤ)))) ≠ 0 := by
    simpa [bsq, subO2] using hreg.2.1
  have hpow : (eqLam a : ℂ) ^ (m + 1) * q.2.2
      = (eqLam a : ℂ) * ((eqLam a : ℂ) ^ m * q.2.2) := by
    rw [pow_succ']; ring
  have hfwdCid : fwdC a (q.1 (-((m + 1 : ℕ) : ℤ)))
      = ugermC a h ((eqLam a : ℂ) ^ m * q.2.2) := by
    rw [htail, hpow]
    exact fwdC_ugermC_lam hRP _ hball
  rcases fwd_pair_dichotomy hreg.1 hPnd with hh | hh
  · rw [hh, hfwdCid]
  · exfalso
    have hsep := fwd_branch_separation a (q.1 (-((m + 1 : ℕ) : ℤ))) hPnd
    have hdist : ‖q.1 (-(m : ℤ)) - ugermC a h ((eqLam a : ℂ) ^ m * q.2.2)‖
        = ‖fwdC a (q.1 (-((m + 1 : ℕ) : ℤ)))
            - fwdAlt a (q.1 (-((m + 1 : ℕ) : ℤ)))‖ := by
      rw [hh, ← hfwdCid, norm_sub_rev]
    linarith [hsep, hclose, hdist]

/-- `germC a h (c ·)` is continuous at `q` whenever the value lies in the analyticity ball. -/
lemma continuousAt_germC_psi1
    (hAnC : AnalyticOnNhd ℂ (germC a h) (Metric.ball (0 : ℂ) ρ))
    {q : ChainData} {c : ℂ} (hc : c * q.2.1 ∈ Metric.ball (0 : ℂ) ρ) :
    ContinuousAt (fun q' : ChainData => germC a h (c * q'.2.1)) q := by
  have hinner : ContinuousAt (fun q' : ChainData => c * q'.2.1) q := by fun_prop
  exact ContinuousAt.comp (f := fun q' : ChainData => c * q'.2.1) (g := germC a h)
    ((hAnC _ hc).continuousAt) hinner

/-- `ugermC a h (c ·)` is continuous at `q`. -/
lemma continuousAt_ugermC_psi2
    (hAnC : AnalyticOnNhd ℂ (germC a h) (Metric.ball (0 : ℂ) ρ))
    {q : ChainData} {c : ℂ} (hc : c * q.2.2 ∈ Metric.ball (0 : ℂ) ρ) :
    ContinuousAt (fun q' : ChainData => ugermC a h (c * q'.2.2)) q := by
  show ContinuousAt (fun q' : ChainData => eqMirror (germC a h (c * q'.2.2))) q
  have h1 : ContinuousAt (fun q' : ChainData => germC a h (c * q'.2.2)) q :=
    ContinuousAt.comp (f := fun q' : ChainData => c * q'.2.2) (g := germC a h)
      ((hAnC _ hc).continuousAt) (by fun_prop)
  exact ContinuousAt.comp (f := fun q' : ChainData => germC a h (c * q'.2.2)) (g := eqMirror)
    continuous_eqMirror.continuousAt h1

/-- `‖f x - f a‖ < ε` eventually near `a`, for `f` continuous at `a`. -/
lemma ev_norm_sub_self_lt {α E : Type*} [TopologicalSpace α] [NormedAddCommGroup E]
    {f : α → E} {a : α} {ε : ℝ} (hf : ContinuousAt f a) (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 a, ‖f x - f a‖ < ε := by
  have h : ∀ᶠ y in 𝓝 (f a), dist y (f a) < ε := by
    filter_upwards [Metric.ball_mem_nhds (f a) hε] with y hy
    rwa [Metric.mem_ball] at hy
  have h2 := hf.eventually h
  filter_upwards [h2] with x hx
  rwa [dist_eq_norm] at hx

/-- Variant vanishing at `a`. -/
lemma ev_norm_lt_of_eq_zero {α E : Type*} [TopologicalSpace α] [NormedAddCommGroup E]
    {f : α → E} {a : α} {ε : ℝ} (hf : ContinuousAt f a) (h0 : f a = 0) (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 a, ‖f x‖ < ε := by
  have h := ev_norm_sub_self_lt hf hε
  filter_upwards [h] with x hx
  rwa [h0, sub_zero] at hx

end Helpers

/-- **Uniform tails on a preconnected piece of `H0`.** On a preconnected set `T ⊆ H0` on which
both linearising parameters are bounded, the forward tail is the principal stable leaf and the
backward tail the principal unstable leaf from one common index `N` on. Openness of
`{q ∈ T | tails from n}` is `H0_tail_bounded` plus the separation of the two branches; closedness
is continuity. -/
theorem tail_uniform_of_isPreconnected {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {T : Set ChainData} (hT : IsPreconnected T) (hTH : T ⊆ H0 a h)
    {B : ℝ} (hB₁ : ∀ q ∈ T, ‖q.2.1‖ ≤ B) (hB₂ : ∀ q ∈ T, ‖q.2.2‖ ≤ B) :
    ∃ N : ℕ, ∀ q ∈ T, ∀ n : ℕ, N ≤ n →
      q.1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ n * q.2.1) ∧
      q.1 (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ n * q.2.2) := by
  rcases T.eq_empty_or_nonempty with hT0 | ⟨q₀, hq₀⟩
  · refine ⟨0, ?_⟩
    intro q hq
    exact absurd (hT0 ▸ hq) (Set.notMem_empty q)
  obtain ⟨ρ, hρ0, hAnC, hC0, hRP, hInjY, hderivY⟩ := germC_facts ha0 ha1 hh
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hlam1le : eqLam a ≤ 1 := le_of_lt hlam1
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB₁ q₀ hq₀)
  -- a floor `n₀` with `λ^{n₀} B < ρ/4`
  obtain ⟨n₀, hn₀⟩ : ∃ n : ℕ, (eqLam a) ^ n * B < ρ / 4 := by
    rcases eq_or_lt_of_le hB0 with hB | hB
    · exact ⟨0, by rw [← hB, mul_zero]; positivity⟩
    · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hρ0 (by linarith : (0:ℝ) < 4 * B)) hlam1
      refine ⟨n, ?_⟩
      have h2 : (eqLam a) ^ n * B < (ρ / (4 * B)) * B := mul_lt_mul_of_pos_right hn hB
      have h3 : (ρ / (4 * B)) * B = ρ / 4 := by field_simp
      rwa [h3] at h2
  -- a slightly larger bound `B'` that still keeps `λ^{n₀} B' < ρ`
  set δ : ℝ := ρ / (4 * (eqLam a) ^ n₀) with hδdef
  have hlamn0 : (eqLam a) ^ n₀ ≠ 0 := pow_ne_zero _ (ne_of_gt hlam0)
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos hρ0 (by positivity)
  have hlamδ : (eqLam a) ^ n₀ * δ = ρ / 4 := by
    rw [hδdef, ← mul_div_assoc, mul_comm (eqLam a ^ n₀) ρ]
    exact mul_div_mul_right _ _ hlamn0
  set B' : ℝ := B + δ with hB'def
  have hBB' : B < B' := by rw [hB'def]; linarith
  have hlamB' : (eqLam a) ^ n₀ * B' < ρ := by
    rw [hB'def, mul_add, hlamδ]; linarith
  have hmapgen : ∀ m : ℕ, n₀ ≤ m → ∀ z : ℂ, ‖z‖ < B' →
      (eqLam a : ℂ) ^ m * z ∈ Metric.ball (0 : ℂ) ρ := by
    intro m hm z hz
    rw [Metric.mem_ball, dist_zero_right, norm_eqLam_pow_mul ha0 ha1 m]
    have h1 : (eqLam a) ^ m ≤ (eqLam a) ^ n₀ := pow_le_pow_of_le_one hlam0.le hlam1le hm
    have h2 : (eqLam a) ^ m * ‖z‖ ≤ (eqLam a) ^ n₀ * B' :=
      mul_le_mul h1 hz.le (norm_nonneg _) (pow_nonneg hlam0.le _)
    exact lt_of_le_of_lt h2 hlamB'
  -- tails at the base point, and the common index `N`
  obtain ⟨N₁₀, M₁₀, K₀, ε₀, hε₀, hN₁₀K₀, hM₁₀K₀, htail₀⟩ :=
    H0_tail_bounded ha0 ha1 hh q₀ (hTH hq₀)
  set N : ℕ := max n₀ (max N₁₀ M₁₀) with hNdef
  have hNn₀ : n₀ ≤ N := by rw [hNdef]; exact le_max_left _ _
  have hNN₁₀ : N₁₀ ≤ N := by
    rw [hNdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hNM₁₀ : M₁₀ ≤ N := by
    rw [hNdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hq₀box : (∀ k : ℤ, |k| ≤ (K₀ : ℤ) → ‖q₀.1 k - q₀.1 k‖ < ε₀) ∧
      ‖q₀.2.1 - q₀.2.1‖ < ε₀ ∧ ‖q₀.2.2 - q₀.2.2‖ < ε₀ := by
    refine ⟨fun k hk => ?_, ?_, ?_⟩ <;> rw [sub_self, norm_zero] <;> linarith
  have hq₀A : TailP a h q₀ N ∧ TailB a h q₀ N :=
    ⟨TailP_mono (htail₀ q₀ (hTH hq₀) hq₀box.1 hq₀box.2.1 hq₀box.2.2).1 hNN₁₀,
     TailB_mono (htail₀ q₀ (hTH hq₀) hq₀box.1 hq₀box.2.1 hq₀box.2.2).2 hNM₁₀⟩
  set A : Set ChainData := {q' | TailP a h q' N ∧ TailB a h q' N} with hAdef
  -- ## `A` is closed at points of `T`
  have hclosed : ∀ q ∈ T, q ∈ closure A → q ∈ A := by
    intro q hqT hqcl
    by_contra hqA
    rw [hAdef] at hqA
    simp only [Set.mem_setOf_eq, not_and_or] at hqA
    rcases hqA with hqA | hqA
    · rw [TailP] at hqA
      push_neg at hqA
      obtain ⟨n, hnN, hnneq⟩ := hqA
      have hball : (eqLam a : ℂ) ^ n * q.2.1 ∈ Metric.ball (0 : ℂ) ρ :=
        hmapgen n (le_trans hNn₀ hnN) q.2.1 (lt_of_le_of_lt (hB₁ q hqT) hBB')
      have hcont : ContinuousAt (fun q' : ChainData =>
          q'.1 (n : ℤ) - germC a h ((eqLam a : ℂ) ^ n * q'.2.1)) q :=
        (by fun_prop : ContinuousAt (fun q' : ChainData => q'.1 (n : ℤ)) q).sub
          (continuousAt_germC_psi1 hAnC hball)
      have hS : {q' : ChainData | q'.1 (n : ℤ) - germC a h ((eqLam a : ℂ) ^ n * q'.2.1) ≠ 0}
          ∈ 𝓝 q := hcont.eventually_ne (sub_ne_zero.mpr hnneq)
      obtain ⟨x, hxS, hxA⟩ := mem_closure_iff_nhds.mp hqcl _ hS
      exact hxS (by rw [hxA.1 n hnN, sub_self])
    · rw [TailB] at hqA
      push_neg at hqA
      obtain ⟨n, hnN, hnneq⟩ := hqA
      have hball : (eqLam a : ℂ) ^ n * q.2.2 ∈ Metric.ball (0 : ℂ) ρ :=
        hmapgen n (le_trans hNn₀ hnN) q.2.2 (lt_of_le_of_lt (hB₂ q hqT) hBB')
      have hcont : ContinuousAt (fun q' : ChainData =>
          q'.1 (-(n : ℤ)) - ugermC a h ((eqLam a : ℂ) ^ n * q'.2.2)) q :=
        (by fun_prop : ContinuousAt (fun q' : ChainData => q'.1 (-(n : ℤ))) q).sub
          (continuousAt_ugermC_psi2 hAnC hball)
      have hS : {q' : ChainData | q'.1 (-(n : ℤ)) - ugermC a h ((eqLam a : ℂ) ^ n * q'.2.2) ≠ 0}
          ∈ 𝓝 q := hcont.eventually_ne (sub_ne_zero.mpr hnneq)
      obtain ⟨x, hxS, hxA⟩ := mem_closure_iff_nhds.mp hqcl _ hS
      exact hxS (by rw [hxA.2 n hnN, sub_self])
  -- ## `A` is open at points of `T`
  have hopen : ∀ q : ChainData, q ∈ T ∩ A →
      ∃ W : Set ChainData, IsOpen W ∧ q ∈ W ∧ W ∩ T ⊆ A := by
    intro q hq
    obtain ⟨hqT, hTP, hTB⟩ := hq
    obtain ⟨N₁, M₁, K, ε, hε, hN₁K, hM₁K, htail⟩ := H0_tail_bounded ha0 ha1 hh q (hTH hqT)
    -- the neighbourhood box of `H0_tail_bounded`, as an `Eventually`
    have hbox : ∀ᶠ q' in 𝓝 q,
        (∀ k : ℤ, |k| ≤ (K : ℤ) → ‖q'.1 k - q.1 k‖ < ε) ∧ ‖q'.2.1 - q.2.1‖ < ε
          ∧ ‖q'.2.2 - q.2.2‖ < ε := by
      have h1 : ∀ᶠ q' in 𝓝 q, ∀ k ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)),
          ‖q'.1 k - q.1 k‖ < ε := by
        rw [Finset.eventually_all]
        intro k hk
        exact ev_norm_sub_self_lt (f := fun q' : ChainData => q'.1 k) (by fun_prop) hε
      filter_upwards [h1,
        ev_norm_sub_self_lt (f := fun q' : ChainData => q'.2.1) (by fun_prop) hε,
        ev_norm_sub_self_lt (f := fun q' : ChainData => q'.2.2) (by fun_prop) hε]
        with q' h1' h2' h3'
      refine ⟨?_, h2', h3'⟩
      intro k hk
      exact h1' k (by rw [Finset.mem_Icc]; exact abs_le.mp hk)
    have htails : ∀ᶠ q' in 𝓝 q, q' ∈ T → (TailP a h q' N₁ ∧ TailB a h q' M₁) := by
      filter_upwards [hbox] with q' hq' hq'T
      exact htail q' (hTH hq'T) hq'.1 hq'.2.1 hq'.2.2
    -- the separation conditions at the finitely many intermediate levels
    have hclF : ∀ᶠ q' in 𝓝 q, ∀ m ∈ Finset.Icc N N₁,
        ‖q'.1 (m : ℤ) - germC a h ((eqLam a : ℂ) ^ m * q'.2.1)‖ < 1 / 2 := by
      rw [Finset.eventually_all]
      intro m hm
      have hmN : N ≤ m := (Finset.mem_Icc.mp hm).1
      have hball : (eqLam a : ℂ) ^ m * q.2.1 ∈ Metric.ball (0 : ℂ) ρ :=
        hmapgen m (le_trans hNn₀ hmN) q.2.1 (lt_of_le_of_lt (hB₁ q hqT) hBB')
      exact ev_norm_lt_of_eq_zero (f := fun q' : ChainData =>
          q'.1 (m : ℤ) - germC a h ((eqLam a : ℂ) ^ m * q'.2.1))
        ((by fun_prop : ContinuousAt (fun q' : ChainData => q'.1 (m : ℤ)) q).sub
          (continuousAt_germC_psi1 hAnC hball))
        (sub_eq_zero.mpr (hTP m hmN)) (by norm_num)
    have hclB : ∀ᶠ q' in 𝓝 q, ∀ m ∈ Finset.Icc N M₁,
        ‖q'.1 (-(m : ℤ)) - ugermC a h ((eqLam a : ℂ) ^ m * q'.2.2)‖ < 1 / 2 := by
      rw [Finset.eventually_all]
      intro m hm
      have hmN : N ≤ m := (Finset.mem_Icc.mp hm).1
      have hball : (eqLam a : ℂ) ^ m * q.2.2 ∈ Metric.ball (0 : ℂ) ρ :=
        hmapgen m (le_trans hNn₀ hmN) q.2.2 (lt_of_le_of_lt (hB₂ q hqT) hBB')
      exact ev_norm_lt_of_eq_zero (f := fun q' : ChainData =>
          q'.1 (-(m : ℤ)) - ugermC a h ((eqLam a : ℂ) ^ m * q'.2.2))
        ((by fun_prop : ContinuousAt (fun q' : ChainData => q'.1 (-(m : ℤ))) q).sub
          (continuousAt_ugermC_psi2 hAnC hball))
        (sub_eq_zero.mpr (hTB m hmN)) (by norm_num)
    have hDb1 : ∀ᶠ q' in 𝓝 q, ‖q'.2.1‖ < B' := by
      filter_upwards [ev_norm_sub_self_lt (f := fun q' : ChainData => q'.2.1) (by fun_prop)
        (show (0:ℝ) < B' - B by linarith)] with q' hq'
      have h1 : ‖q'.2.1‖ ≤ ‖q'.2.1 - q.2.1‖ + ‖q.2.1‖ := by
        have := norm_add_le (q'.2.1 - q.2.1) q.2.1
        rwa [sub_add_cancel] at this
      linarith [hq', hB₁ q hqT]
    have hDb2 : ∀ᶠ q' in 𝓝 q, ‖q'.2.2‖ < B' := by
      filter_upwards [ev_norm_sub_self_lt (f := fun q' : ChainData => q'.2.2) (by fun_prop)
        (show (0:ℝ) < B' - B by linarith)] with q' hq'
      have h1 : ‖q'.2.2‖ ≤ ‖q'.2.2 - q.2.2‖ + ‖q.2.2‖ := by
        have := norm_add_le (q'.2.2 - q.2.2) q.2.2
        rwa [sub_add_cancel] at this
      linarith [hq', hB₂ q hqT]
    have hgood : ∀ᶠ q' in 𝓝[T] q, TailP a h q' N ∧ TailB a h q' N := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [htails, hclF, hclB, hDb1, hDb2] with q' htl hclF' hclB' hb1 hb2
      intro hq'T
      obtain ⟨hTP', hTB'⟩ := htl hq'T
      have hchain : IsChain a h q' := isChain_of_mem_H0 (hTH hq'T)
      have hdescF : ∀ n : ℕ, N ≤ n → n ≤ N₁ →
          q'.1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ n * q'.2.1) := by
        intro n hnN hnN₁
        refine Nat.decreasingInduction (motive := fun j _ => N ≤ j →
            q'.1 (j : ℤ) = germC a h ((eqLam a : ℂ) ^ j * q'.2.1)) ?_ ?_ hnN₁ hnN
        · intro k hk ih hNk
          have hk₁ : k ≤ N₁ := le_of_lt hk
          have hnext : q'.1 ((k + 1 : ℕ) : ℤ)
              = germC a h ((eqLam a : ℂ) ^ (k + 1) * q'.2.1) := ih (Nat.le_succ_of_le hNk)
          have hcl : ‖q'.1 (k : ℤ) - germC a h ((eqLam a : ℂ) ^ k * q'.2.1)‖ < 1 / 2 :=
            hclF' k (Finset.mem_Icc.mpr ⟨hNk, hk₁⟩)
          have hball : (eqLam a : ℂ) ^ k * q'.2.1 ∈ Metric.ball (0 : ℂ) ρ :=
            hmapgen k (le_trans hNn₀ hNk) q'.2.1 hb1
          exact step_fwd hRP hchain hnext hcl hball
        · intro _
          exact hTP' N₁ le_rfl
      have hdescB : ∀ n : ℕ, N ≤ n → n ≤ M₁ →
          q'.1 (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ n * q'.2.2) := by
        intro n hnN hnM₁
        refine Nat.decreasingInduction (motive := fun j _ => N ≤ j →
            q'.1 (-(j : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ j * q'.2.2)) ?_ ?_ hnM₁ hnN
        · intro k hk ih hNk
          have hk₁ : k ≤ M₁ := le_of_lt hk
          have hnext : q'.1 (-((k + 1 : ℕ) : ℤ))
              = ugermC a h ((eqLam a : ℂ) ^ (k + 1) * q'.2.2) := ih (Nat.le_succ_of_le hNk)
          have hcl : ‖q'.1 (-(k : ℤ)) - ugermC a h ((eqLam a : ℂ) ^ k * q'.2.2)‖ < 1 / 2 :=
            hclB' k (Finset.mem_Icc.mpr ⟨hNk, hk₁⟩)
          have hball : (eqLam a : ℂ) ^ k * q'.2.2 ∈ Metric.ball (0 : ℂ) ρ :=
            hmapgen k (le_trans hNn₀ hNk) q'.2.2 hb2
          exact step_bwd hRP hchain hnext hcl hball
        · intro _
          exact hTB' M₁ le_rfl
      refine ⟨?_, ?_⟩
      · intro n hn
        by_cases h : n ≤ N₁
        · exact hdescF n hn h
        · exact hTP' n (le_of_lt (lt_of_not_ge h))
      · intro n hn
        by_cases h : n ≤ M₁
        · exact hdescB n hn h
        · exact hTB' n (le_of_lt (lt_of_not_ge h))
    have hS : {q' : ChainData | TailP a h q' N ∧ TailB a h q' N} ∈ 𝓝 q ⊓ 𝓟 T := hgood
    have hS' := Filter.mem_inf_principal.mp hS
    obtain ⟨W, hWsub, hWopen, hqW⟩ := mem_nhds_iff.mp hS'
    exact ⟨W, hWopen, hqW, fun q' hq' => hWsub hq'.1 hq'.2⟩
  choose W hW using hopen
  have huopen : IsOpen (⋃ (q : ChainData) (hq : q ∈ T ∩ A), W q hq) :=
    isOpen_iUnion fun q => isOpen_iUnion fun hq => (hW q hq).1
  have hq₀u : q₀ ∈ (⋃ (q : ChainData) (hq : q ∈ T ∩ A), W q hq) :=
    Set.mem_iUnion.mpr ⟨q₀, Set.mem_iUnion.mpr ⟨⟨hq₀, hq₀A⟩, (hW q₀ ⟨hq₀, hq₀A⟩).2.1⟩⟩
  -- ## Preconnectedness: `T ⊆ A`
  have hTsubA : T ⊆ A := by
    intro q hq
    by_contra hqA
    have hqcl : q ∉ closure A := fun hc => hqA (hclosed q hq hc)
    have hsu : T ⊆ (⋃ (q : ChainData) (hq : q ∈ T ∩ A), W q hq) ∪ (closure A)ᶜ := by
      intro x hx
      by_cases hxA : x ∈ A
      · exact Or.inl (Set.mem_iUnion.mpr
          ⟨x, Set.mem_iUnion.mpr ⟨⟨hx, hxA⟩, (hW x ⟨hx, hxA⟩).2.1⟩⟩)
      · exact Or.inr (fun hc => hxA (hclosed x hx hc))
    have hne : (T ∩ (⋃ (q : ChainData) (hq : q ∈ T ∩ A), W q hq)).Nonempty :=
      ⟨q₀, hq₀, hq₀u⟩
    have hnev : (T ∩ (closure A)ᶜ).Nonempty := ⟨q, hq, hqcl⟩
    obtain ⟨x, hxT, hxu, hxv⟩ := hT _ _ huopen isClosed_closure.isOpen_compl hsu hne hnev
    obtain ⟨q', hxu2⟩ := Set.mem_iUnion.mp hxu
    obtain ⟨hq', hxq'⟩ := Set.mem_iUnion.mp hxu2
    exact hxv (subset_closure ((hW q' hq').2.2 ⟨hxq', hxT⟩))
  refine ⟨N, ?_⟩
  intro q hq n hn
  have hAq := hTsubA hq
  exact ⟨hAq.1 n hn, hAq.2 n hn⟩

end

end Work.EQ
