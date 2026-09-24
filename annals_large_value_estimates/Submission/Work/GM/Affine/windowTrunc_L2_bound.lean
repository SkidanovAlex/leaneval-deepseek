import Mathlib
import Submission.Work.GM.Affine.farHprof_helpers
import Submission.Work.GM.Affine.window_part_defs
import Submission.Work.GM.Affine.resonant_count_good
import Submission.Work.GM.Affine.far_part_defs
import Submission.Work.GM.Affine.tail_part_bound
import Submission.Work.GM.Affine.card_mul_pairs_le
import Submission.Work.GM.Affine.card_int_in_interval_le
import Submission.Work.GM.Affine.region_I_bound
import Submission.Work.GM.Affine.divisor_bound

/-!
# The window-truncated `L²` bound (GM §9, region II, window part)

`windowTrunc_L2_bound` is the truncated (`2B ≤ T^η`) form of the window part of the far weight.
The proof follows the plan of `NOTES_windowTrunc_L2_bound.md`:

* the pointwise expansion `∑_{m₁} |m₁|⁻¹ Bsum(ξ/m₁) Wwin(ξ/m₁) = ∑_{p ∈ Pwin} aTerm p`
  (`Wwin_sum_eq_pairs`) and a dyadic layer decomposition of `Pwin` into the finsets `Pj`;
* a Cauchy–Schwarz over the layers (weights `2^{-j}`) and over the pairs of a layer;
* the resonance count `card_mul_pairs_le_nonzero` on each layer
  (`r_j = 2^{j+2} M₁/M₃`, so `#Pj ⪅ T^{3ε}(1 + 2^j M₁/M₃)`);
* the fast decay of `ψ̂₁` on layer `j` together with the elementary bound
  `#{ℓ : 2^j ≤ |M₃(ℓ-y)| < 2^{j+1}} ≤ 2^{j+2}/M₃ + 1` and Plancherel in `ξ`;
* geometric summation in `j`.

The hypothesis `2B ≤ T^η` is used only to rule out the pairs with `ℓ = 0`
(equivalently: to make every product `m₁ℓ` of a window pair non-zero, so that the
divisor-bound count applies with the *non-vanishing* variant recorded below).
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.GM.Affine

noncomputable section

/-! ### The resonance count without the hypothesis `r < |ξ|` -/

/-- `card_mul_pairs_le` needs `r < |ξ|` only to know that all the products `p.1 * p.2` occurring
in `P` are non-zero.  In the window estimate the products are non-zero for a geometric reason, so
we record the version with the non-vanishing hypothesis stated directly. -/
theorem card_mul_pairs_le_nonzero {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M₁ r X : ℝ), 0 < M₁ → 0 ≤ r → 1 ≤ X →
      ∀ ξ : ℝ, |ξ| ≤ X → ∀ P : Finset (ℤ × ℤ),
        (∀ p ∈ P, M₁ ≤ |(p.1 : ℝ)|) →
        (∀ p ∈ P, |((p.1 : ℝ) * (p.2 : ℝ)) - ξ| ≤ r) →
        (∀ p ∈ P, p.1 * p.2 ≠ 0) →
        (P.card : ℝ) ≤ C * (X + r + 2) ^ ε * (2 * r + 1) := by
  obtain ⟨Cd, hCdpos, hCd⟩ := card_divisors_le_const_mul_rpow hε
  refine ⟨2 * Cd, by positivity, ?_⟩
  intro M₁ r X hM₁ hr hX ξ hξX P hP1 hP2 hPnz
  let Q : Finset ℤ := P.image (fun p : ℤ × ℤ => p.1 * p.2)
  have hmap : Set.MapsTo (fun p : ℤ × ℤ => p.1 * p.2) ↑P ↑Q :=
    fun p hp => Finset.mem_image_of_mem _ hp
  have hsum : P.card = ∑ n ∈ Q, (P.filter (fun p => p.1 * p.2 = n)).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  have hQnz : ∀ n ∈ Q, n ≠ 0 := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨p, hp, rfl⟩ := hn
    exact hPnz p hp
  have hQabs : ∀ n ∈ Q, |(n : ℝ) - ξ| ≤ r := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨p, hp, rfl⟩ := hn
    have h := hP2 p hp
    rwa [← Int.cast_mul] at h
  have hQcard : (Q.card : ℝ) ≤ 2 * r + 1 := card_int_in_interval_le hr Q hQabs
  have hnat : ∀ n ∈ Q, ((n.natAbs : ℕ) : ℝ) ≤ X + r + 2 := by
    intro n hn
    have h := hQabs n hn
    have hn_abs : |(n : ℝ)| ≤ |ξ| + r := by
      calc |(n : ℝ)| = |((n : ℝ) - ξ) + ξ| := by rw [sub_add_cancel]
        _ ≤ |(n : ℝ) - ξ| + |ξ| := abs_add_le _ _
        _ ≤ |ξ| + r := by linarith [h]
    have hcast : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [hcast]
    linarith [hξX, hn_abs]
  have hterm : ∀ n ∈ Q, ((P.filter (fun p => p.1 * p.2 = n)).card : ℝ)
      ≤ 2 * Cd * (X + r + 2) ^ ε := by
    intro n hn
    have hfib : ((P.filter (fun p => p.1 * p.2 = n)).card : ℝ)
        ≤ 2 * ((n.natAbs.divisors.card : ℕ) : ℝ) := by
      have := fiber_card_le_card_divisors hM₁ P hP1 n (hQnz n hn)
      exact_mod_cast this
    have hdiv := hCd n.natAbs
    have hrpow : ((n.natAbs : ℕ) : ℝ) ^ ε ≤ (X + r + 2) ^ ε :=
      Real.rpow_le_rpow (by positivity) (hnat n hn) hε.le
    calc ((P.filter (fun p => p.1 * p.2 = n)).card : ℝ)
        ≤ 2 * ((n.natAbs.divisors.card : ℕ) : ℝ) := hfib
      _ ≤ 2 * (Cd * ((n.natAbs : ℕ) : ℝ) ^ ε) :=
          mul_le_mul_of_nonneg_left hdiv (by norm_num)
      _ ≤ 2 * (Cd * (X + r + 2) ^ ε) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrpow hCdpos.le) (by norm_num)
      _ = 2 * Cd * (X + r + 2) ^ ε := by ring
  have hPcard : (P.card : ℝ) = ∑ n ∈ Q, ((P.filter (fun p => p.1 * p.2 = n)).card : ℝ) := by
    rw [hsum]; push_cast; rfl
  calc (P.card : ℝ)
      = ∑ n ∈ Q, ((P.filter (fun p => p.1 * p.2 = n)).card : ℝ) := hPcard
    _ ≤ ∑ n ∈ Q, 2 * Cd * (X + r + 2) ^ ε := Finset.sum_le_sum hterm
    _ = (Q.card : ℝ) * (2 * Cd * (X + r + 2) ^ ε) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * r + 1) * (2 * Cd * (X + r + 2) ^ ε) :=
        mul_le_mul_of_nonneg_right hQcard (by positivity)
    _ = 2 * Cd * (X + r + 2) ^ ε * (2 * r + 1) := by ring

/-! ### Elementary layer arithmetic -/

/-- Uniqueness of the dyadic layer index. -/
lemma layer_index_unique {v : ℝ} {j k : ℕ} (h1 : (2:ℝ)^j ≤ v) (h2 : v < (2:ℝ)^(j+1))
    (h3 : (2:ℝ)^k ≤ v) (h4 : v < (2:ℝ)^(k+1)) : j = k := by
  rcases lt_trichotomy j k with h | h | h
  · have h5 : (2:ℝ)^(j+1) ≤ (2:ℝ)^k := by
      apply pow_le_pow_right₀ (by norm_num); omega
    linarith
  · exact h
  · have h5 : (2:ℝ)^(k+1) ≤ (2:ℝ)^j := by
      apply pow_le_pow_right₀ (by norm_num); omega
    linarith

/-- Existence of the dyadic layer index. -/
lemma layer_index_exists {v : ℝ} (hv : 1 ≤ v) :
    ∃ j : ℕ, (2:ℝ)^j ≤ v ∧ v < (2:ℝ)^(j+1) := by
  have hv0 : (0:ℝ) < v := by linarith
  have hfl : (1:ℤ) ≤ ⌊v⌋ := Int.le_floor.mpr (by exact_mod_cast hv)
  set n : ℕ := (⌊v⌋).toNat with hn
  have hnne : n ≠ 0 := by rw [hn]; omega
  have hcastn : (n : ℝ) = (⌊v⌋ : ℝ) := by
    rw [hn]; exact_mod_cast (Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ ⌊v⌋))
  refine ⟨Nat.log 2 n, ?_, ?_⟩
  · have h1 := Nat.pow_log_le_self 2 hnne
    have h2 : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    rw [hcastn] at h2
    have := Int.floor_le v
    push_cast at h2 ⊢
    linarith
  · have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    have h3 : ((n : ℕ) : ℝ) + 1 ≤ ((2 ^ (Nat.log 2 n).succ : ℕ) : ℝ) := by
      have : n + 1 ≤ 2 ^ (Nat.log 2 n).succ := h2
      exact_mod_cast this
    rw [hcastn] at h3
    have h4 := Int.lt_floor_add_one v
    have h5 : (2:ℝ) ^ ((Nat.log 2 n) + 1) = ((2 ^ (Nat.log 2 n).succ : ℕ) : ℝ) := by
      push_cast [Nat.succ_eq_add_one]; norm_num
    rw [h5]
    linarith

/-- The dyadic layer indicators of a value `v ∈ [1,B]` sum to `1` over `j ≤ ⌈B⌉`. -/
lemma sum_layer_indicator {B v : ℝ} (hv : 1 ≤ v) (hvB : v ≤ B) :
    ∑ j ∈ Finset.range ((⌈B⌉).toNat + 1),
      (if (2:ℝ)^j ≤ v ∧ v < (2:ℝ)^(j+1) then (1:ℂ) else 0) = 1 := by
  obtain ⟨j0, h1, h2⟩ := layer_index_exists hv
  have hBpos : (0:ℝ) < B := by linarith
  have hJ : B ≤ ((⌈B⌉).toNat : ℝ) := by
    have h := Int.le_ceil B
    have h0 : (0:ℤ) ≤ ⌈B⌉ := by
      have : (0:ℝ) ≤ (⌈B⌉ : ℤ) := by push_cast; linarith
      exact_mod_cast this
    rw [← Int.toNat_of_nonneg h0] at h
    exact_mod_cast h
  have hj0 : j0 ≤ (⌈B⌉).toNat := by
    have h3 : (j0:ℝ) ≤ (2:ℝ)^j0 := by exact_mod_cast (Nat.lt_two_pow_self (n := j0)).le
    have h4 : (2:ℝ)^j0 ≤ B := le_trans h1 hvB
    have : (j0:ℝ) ≤ ((⌈B⌉).toNat : ℝ) := by linarith
    exact_mod_cast this
  rw [Finset.sum_eq_single j0]
  · simp [h1, h2]
  · intro j hj hjne
    rw [if_neg]
    rintro ⟨h1', h2'⟩
    exact hjne (layer_index_unique h1' h2' h1 h2)
  · intro hnot
    exact absurd (Finset.mem_range.mpr (by omega)) hnot

/-- The number of integers `ℓ` with `2^j ≤ |M₃(ℓ-y)| < 2^{j+1}` is at most `2^{j+2}/M₃ + 1`. -/
lemma card_layer_annulus_le {M₃ y : ℝ} (hM₃ : 0 < M₃) (j : ℕ) (L : ℤ) :
    (((Finset.Icc (-L) L).filter (fun ℓ : ℤ =>
        (2:ℝ)^j ≤ |M₃ * ((ℓ:ℝ) - y)| ∧ |M₃ * ((ℓ:ℝ) - y)| < (2:ℝ)^(j+1))).card : ℝ)
      ≤ (2:ℝ)^(j+2)/M₃ + 1 := by
  set q : ℤ → Prop := (fun ℓ : ℤ =>
        (2:ℝ)^j ≤ |M₃ * ((ℓ:ℝ) - y)| ∧ |M₃ * ((ℓ:ℝ) - y)| < (2:ℝ)^(j+1)) with hq
  have hQmem : ∀ ℓ ∈ (Finset.Icc (-L) L).filter q, |(ℓ:ℝ) - y| ≤ (2:ℝ)^(j+1)/M₃ := by
    intro ℓ hℓ
    rw [Finset.mem_filter] at hℓ
    have h2 : M₃ * |(ℓ:ℝ) - y| ≤ (2:ℝ)^(j+1) := by
      have h := hℓ.2.2.le
      rwa [abs_mul, abs_of_pos hM₃] at h
    rw [le_div_iff₀ hM₃, mul_comm]
    exact h2
  have hcard := card_int_in_interval_le (r := (2:ℝ)^(j+1)/M₃) (ξ := y) (by positivity)
    ((Finset.Icc (-L) L).filter q) hQmem
  have htwo : 2 * ((2:ℝ)^(j+1)/M₃) + 1 = (2:ℝ)^(j+2)/M₃ + 1 := by
    have hpow : (2:ℝ)^(j+2) = 2 * (2:ℝ)^(j+1) := by
      rw [show j+2 = (j+1)+1 by ring, pow_succ]; ring
    rw [hpow, mul_div_assoc]
  rw [← htwo]
  exact hcard

/-! ### Region membership, compact support -/
/-! ### Elementary helpers -/

lemma pow_two_mul (j k : ℕ) : ((2:ℝ)^j)^k = (2:ℝ)^(k*j) := by
  rw [← pow_mul, Nat.mul_comm j k]

lemma mem_wtrRegion {T η M₁ M₃ ξ : ℝ}
    (hξ : ξ ∈ Set.Icc (-(T ^ 6)) (T ^ 6) \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃)) :
    |ξ| ≤ T ^ 6 ∧ T ^ η * M₁ / M₃ < |ξ| := by
  obtain ⟨h1, h2⟩ := hξ
  rw [Set.mem_Icc] at h1
  rw [Set.mem_Icc, not_and_or] at h2
  refine ⟨abs_le.mpr h1, ?_⟩
  rcases h2 with h | h
  · rw [not_le] at h
    have : T ^ η * M₁ / M₃ < -ξ := by linarith
    linarith [neg_le_abs ξ]
  · rw [not_le] at h
    linarith [le_abs_self ξ]

lemma hasCompactSupport_of_SuppHyp {C₀ : ℝ} {f : ℝ → ℝ} (hsup : SuppHyp C₀ f) :
    HasCompactSupport f := by
  rw [hasCompactSupport_def]
  refine IsCompact.of_isClosed_subset (s := Set.Icc (1 / C₀) C₀) isCompact_Icc
    isClosed_closure ?_
  refine closure_minimal ?_ isClosed_Icc
  intro u hu
  rw [Function.mem_support] at hu
  exact hsup u hu

lemma continuous_Fhat_of_continuous_compact {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) : Continuous (Fhat f) := by
  rw [show Fhat f = VectorFourier.fourierIntegral Real.fourierChar (volume : Measure ℝ)
      (innerₗ ℝ) (fun u : ℝ => (f u : ℂ)) from rfl]
  exact VectorFourier.fourierIntegral_continuous (μ := (volume : Measure ℝ)) (L := innerₗ ℝ)
    (f := fun u : ℝ => (f u : ℂ)) Real.continuous_fourierChar (by fun_prop)
    ((hf.integrable_of_hasCompactSupport hcs).ofReal)

lemma continuous_Bsum {M₂ : ℝ} {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Continuous (fun u : ℝ => Bsum f M₂ u) := by
  have hfhat := continuous_Fhat_of_continuous_compact hf hcs
  simp only [Bsum]
  exact continuous_finsetSum _ (fun m₂ _ =>
    Continuous.mul continuous_const (hfhat.comp (continuous_const.mul continuous_id)))

lemma continuous_psi1hat (K : ℝ) : Continuous (psi1hat K) := by
  rw [show psi1hat K = Fhat (psi1 K) from rfl]
  exact continuous_Fhat_of_continuous_compact (psi1_contDiff K).continuous (psi1_hasCompactSupport K)

/-! ### A finite-`ℓ`-sum form of `Wwin` -/

lemma Wwin_eq_finsum_gen {K T M₁ M₃ B y : ℝ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    (hy : |y| ≤ T ^ 6 / M₁) :
    Wwin K M₃ B y =
      (M₃ : ℂ) * ∑ ℓ ∈ Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B),
        (if 2 / M₃ < |(ℓ : ℝ) - y| ∧ |(ℓ : ℝ) - y| ≤ B / M₃ then
          psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0) := by
  have hceil : ((⌈T ^ 6 / M₁ + B / M₃⌉ : ℤ) : ℝ) ≥ T ^ 6 / M₁ + B / M₃ := by
    have := Int.le_ceil (T ^ 6 / M₁ + B / M₃); push_cast; linarith
  have hLbound : ((Lwin T M₁ M₃ B : ℤ) : ℝ) ≥ T ^ 6 / M₁ + B / M₃ + 1 := by
    rw [Lwin]; push_cast; linarith [hceil]
  rw [Wwin]
  congr 1
  refine tsum_eq_sum (fun ℓ hℓ => ?_)
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hℓ
  have hfar : B / M₃ < |(ℓ : ℝ) - y| := by
    rcases hℓ with h | h
    · have h1 : ℓ ≤ -(Lwin T M₁ M₃ B) - 1 := by omega
      have h2 : ((ℓ:ℤ) : ℝ) ≤ -((Lwin T M₁ M₃ B : ℤ) : ℝ) - 1 := by exact_mod_cast h1
      have h3 : -((ℓ:ℤ) : ℝ) - |y| ≤ |(ℓ : ℝ) - y| := by
        have h6 : |((ℓ:ℤ) : ℝ)| ≤ |((ℓ:ℤ) : ℝ) - y| + |y| := by
          have h7 := abs_add_le (((ℓ:ℤ) : ℝ) - y) y
          rwa [sub_add_cancel] at h7
        have h8 : -((ℓ:ℤ) : ℝ) ≤ |((ℓ:ℤ) : ℝ)| := neg_le_abs _
        linarith
      linarith
    · have h1 : (Lwin T M₁ M₃ B) + 1 ≤ ℓ := by omega
      have h2 : ((Lwin T M₁ M₃ B : ℤ) : ℝ) + 1 ≤ ((ℓ:ℤ) : ℝ) := by exact_mod_cast h1
      have h3 : ((ℓ:ℤ) : ℝ) - |y| ≤ |(ℓ : ℝ) - y| := by
        have h6 : |((ℓ:ℤ) : ℝ)| ≤ |((ℓ:ℤ) : ℝ) - y| + |y| := by
          have h7 := abs_add_le (((ℓ:ℤ) : ℝ) - y) y
          rwa [sub_add_cancel] at h7
        have h8 : ((ℓ:ℤ) : ℝ) ≤ |((ℓ:ℤ) : ℝ)| := le_abs_self _
        linarith
      linarith
  rw [if_neg (fun hh => absurd hh.2 (not_le.mpr hfar))]

/-! ### The finite-`ℓ`-sum version of the window sum -/

def wtrS (K T M₁ M₂ M₃ B : ℝ) (f : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
    ((M₃ : ℂ) * ∑ ℓ ∈ Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B),
      (if 2 / M₃ < |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ∧ |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ≤ B / M₃ then
        psi1hat K (M₃ * ((ℓ : ℝ) - ξ / (m₁ : ℝ))) else 0))

lemma wtrS_eq {K T η B M₁ M₂ M₃ : ℝ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃) {f : ℝ → ℝ} {ξ : ℝ}
    (hξ : ξ ∈ Set.Icc (-(T ^ 6)) (T ^ 6) \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃)) :
    wtrS K T M₁ M₂ M₃ B f ξ =
      ∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
        Wwin K M₃ B (ξ / (m₁ : ℝ)) := by
  obtain ⟨hξle, -⟩ := mem_wtrRegion hξ
  refine Finset.sum_congr rfl (fun m₁ hm₁ => ?_)
  have hm₁pos : (0:ℝ) < |(m₁ : ℝ)| := by
    have h := (Finset.mem_filter.mp hm₁).2
    exact lt_trans hM₁ h
  have hm₁abs : M₁ ≤ |(m₁ : ℝ)| := le_of_lt (Finset.mem_filter.mp hm₁).2
  have hy : |ξ / (m₁ : ℝ)| ≤ T ^ 6 / M₁ := by
    rw [abs_div, div_le_div_iff₀ hm₁pos hM₁]
    exact mul_le_mul hξle hm₁abs hM₁.le (by positivity : (0:ℝ) ≤ T^6)
  rw [Wwin_eq_finsum_gen hM₁ hM₃ hy]

lemma measurable_wtrS {K T M₁ M₂ M₃ B : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) : Measurable (fun ξ => wtrS K T M₁ M₂ M₃ B f ξ) := by
  have hB : Continuous (fun u : ℝ => Bsum f M₂ u) := continuous_Bsum hf hcs
  have hpsi : Continuous (psi1hat K) := continuous_psi1hat K
  unfold wtrS
  refine Finset.measurable_sum _ (fun m₁ hm₁ => ?_)
  refine Measurable.mul ?_ ?_
  · refine Measurable.mul measurable_const ?_
    exact (hB.measurable.comp (measurable_id.div_const _))
  · refine Measurable.mul measurable_const ?_
    refine Finset.measurable_sum _ (fun ℓ hℓ => ?_)
    refine Measurable.ite ?_ ?_ measurable_const
    · rw [show {ξ : ℝ | 2 / M₃ < |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ∧
            |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ≤ B / M₃}
          = (fun ξ : ℝ => |(ℓ : ℝ) - ξ / (m₁ : ℝ)|) ⁻¹' Set.Ioc (2 / M₃) (B / M₃) from by
          ext ξ; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioc]]
      exact (by fun_prop : Continuous fun ξ : ℝ => |(ℓ : ℝ) - ξ / (m₁ : ℝ)|).measurable
        measurableSet_Ioc
    · exact (hpsi.comp (by fun_prop)).measurable

/-! ### Two Cauchy–Schwarz lemmas -/

lemma norm_sum_sq_le_weighted {ι : Type*} (s : Finset ι) (z : ι → ℂ) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ (∑ i ∈ s, w i) * (∑ i ∈ s, ‖z i‖ ^ 2 / w i) := by
  have h3 : ‖∑ i ∈ s, z i‖ ^ 2 ≤ (∑ i ∈ s, ‖z i‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
  refine h3.trans ?_
  have h4 := Finset.sum_mul_sq_le_sq_mul_sq (s := s)
    (f := fun i => Real.sqrt (w i)) (g := fun i => ‖z i‖ / Real.sqrt (w i))
  have h5 : ∑ i ∈ s, Real.sqrt (w i) * (‖z i‖ / Real.sqrt (w i)) = ∑ i ∈ s, ‖z i‖ := by
    apply Finset.sum_congr rfl
    intro i hi
    have hw0 : 0 < w i := hw i hi
    have hs : Real.sqrt (w i) ≠ 0 := by positivity
    field_simp
  have h6 : ∑ i ∈ s, (Real.sqrt (w i)) ^ 2 = ∑ i ∈ s, w i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Real.sq_sqrt (le_of_lt (hw i hi))
  have h7 : ∑ i ∈ s, (‖z i‖ / Real.sqrt (w i)) ^ 2 = ∑ i ∈ s, ‖z i‖ ^ 2 / w i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [div_pow, Real.sq_sqrt (le_of_lt (hw i hi))]
  rw [h5, h6, h7] at h4
  exact h4

lemma norm_sum_sq_le_card_mul_sum_norm_sq {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖z i‖ ^ 2 := by
  have h := norm_sum_sq_le_weighted s z (fun _ => (1:ℝ)) (fun i hi => by norm_num)
  simpa using h

lemma sum_inv_two_pow_le (N : ℕ) : ∑ j ∈ Finset.range N, ((2:ℝ)^j)⁻¹ ≤ 2 := by
  have hgeom : Summable (fun j : ℕ => ((1:ℝ)/2)^j) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have htsum : (∑' j : ℕ, ((1:ℝ)/2)^j) = 2 := by
    rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖((1:ℝ)/2)‖ < 1)]
    norm_num
  have h1 : ∑ j ∈ Finset.range N, ((1:ℝ)/2)^j ≤ ∑' j : ℕ, ((1:ℝ)/2)^j :=
    hgeom.sum_le_tsum (Finset.range N) (fun j _ => by positivity)
  rw [htsum] at h1
  refine le_trans (le_of_eq ?_) h1
  apply Finset.sum_congr rfl
  intro j hj
  rw [one_div, inv_pow]

lemma sum_inv_two_pow_mul_le (k N : ℕ) (hk : 1 ≤ k) :
    ∑ j ∈ Finset.range N, ((2:ℝ)^(k*j))⁻¹ ≤ 2 := by
  refine le_trans (Finset.sum_le_sum (fun j hj => ?_)) (sum_inv_two_pow_le N)
  have hjk : j ≤ k*j := Nat.le_mul_of_pos_left j (by omega)
  have hle : (2:ℝ)^j ≤ (2:ℝ)^(k*j) := pow_le_pow_right₀ (by norm_num) hjk
  simpa only [one_div] using one_div_le_one_div_of_le (by positivity : (0:ℝ) < (2:ℝ)^j) hle

/-! ### The squared norm of `aTerm` -/

lemma norm_aTerm_sq (K M₂ M₃ : ℝ) (f : ℝ → ℝ) (ξ : ℝ) (x y : ℤ) :
    ‖aTerm K M₂ M₃ f ξ (x, y)‖ ^ 2
      = (1/(x:ℝ)^2) * ‖Bsum f M₂ (ξ/(x:ℝ))‖^2 * M₃^2 *
          ‖psi1hat K (M₃ * ((y:ℝ) - ξ/(x:ℝ)))‖^2 := by
  have hcx : ‖((( |(x:ℝ)| : ℝ) : ℂ))⁻¹‖ = 1/|(x:ℝ)| := by
    rw [norm_inv]
    have h1 : ‖((( |(x:ℝ)| : ℝ) : ℂ))‖ = |(x:ℝ)| :=
      (Complex.norm_real _).trans ((Real.norm_eq_abs _).trans (abs_abs _))
    rw [h1, one_div]
  have hM₃c : ‖((M₃:ℝ):ℂ)‖ = |M₃| := (Complex.norm_real M₃).trans (Real.norm_eq_abs M₃)
  simp only [aTerm]
  rw [show ‖((( |(x:ℝ)| : ℝ) : ℂ))⁻¹ * Bsum f M₂ (ξ / (x:ℝ)) *
        ((M₃:ℂ) * psi1hat K (M₃ * ((y:ℝ) - ξ / (x:ℝ))))‖
      = ‖((( |(x:ℝ)| : ℝ) : ℂ))⁻¹‖ * ‖Bsum f M₂ (ξ / (x:ℝ))‖ *
        (‖((M₃:ℝ):ℂ)‖ * ‖psi1hat K (M₃ * ((y:ℝ) - ξ / (x:ℝ)))‖) from by
      rw [norm_mul, norm_mul, norm_mul]]
  simp only [mul_pow, hcx, hM₃c]
  rw [show (1/|(x:ℝ)|)^2 = 1/(x:ℝ)^2 from by rw [div_pow, one_pow, sq_abs],
      show |M₃|^2 = M₃^2 from sq_abs M₃]
  ring

/-! ### The layer count -/

lemma wtr_layer_count {T η B M₁ M₃ ξ : ℝ} {εc Ccnt : ℝ}
    (hT : 1 ≤ T) (hη : 0 < η) (hB : 2 ≤ B) (h2B : 2 * B ≤ T ^ η) (hM₁ : 0 < M₁)
    (hM₃ : 1 ≤ M₃) (hεc : 0 < εc) (hCcntpos : 0 < Ccnt)
    (hCcnt : ∀ (M₁' r X : ℝ), 0 < M₁' → 0 ≤ r → 1 ≤ X → ∀ ξ' : ℝ, |ξ'| ≤ X →
      ∀ P : Finset (ℤ × ℤ), (∀ p ∈ P, M₁' ≤ |(p.1 : ℝ)|) →
        (∀ p ∈ P, |((p.1 : ℝ) * (p.2 : ℝ)) - ξ'| ≤ r) →
        (∀ p ∈ P, p.1 * p.2 ≠ 0) →
        (P.card : ℝ) ≤ Ccnt * (X + r + 2) ^ εc * (2 * r + 1))
    (hξ : ξ ∈ Set.Icc (-(T ^ 6)) (T ^ 6)
        \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃))
    {j : ℕ} (hj : j ∈ Finset.range (Nat.log 2 (⌊B⌋).toNat + 1)) :
    ((Pj T M₁ M₃ B ξ j).card : ℝ)
      ≤ Ccnt * (5 : ℝ) ^ εc * T ^ (6 * εc) * 9 * (1 + (2 : ℝ) ^ j * M₁ / M₃) := by
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  have hT1 : (0:ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  obtain ⟨hξle, hξgt⟩ := mem_wtrRegion hξ
  have hT6 : (1:ℝ) ≤ T^6 := one_le_pow₀ hT
  have hjle : j ≤ Nat.log 2 (⌊B⌋).toNat := by
    have := Finset.mem_range.mp hj; omega
  have hn2 : 2 ≤ (⌊B⌋).toNat := by
    have h : (2:ℤ) ≤ ⌊B⌋ := Int.le_floor.mpr (by exact_mod_cast hB)
    omega
  have hpowJ : (2:ℕ) ^ Nat.log 2 (⌊B⌋).toNat ≤ (⌊B⌋).toNat :=
    Nat.pow_log_le_self 2 (by omega)
  have h2jB : (2:ℝ)^j ≤ B := by
    have h1 : (2:ℕ)^j ≤ (2:ℕ)^(Nat.log 2 (⌊B⌋).toNat) :=
      Nat.pow_le_pow_right (by norm_num) hjle
    have h2 : ((2:ℕ)^j : ℝ) ≤ ((⌊B⌋).toNat : ℝ) := by exact_mod_cast (le_trans h1 hpowJ)
    have h3 : ((⌊B⌋).toNat : ℝ) ≤ B := by
      have h4 : (((⌊B⌋).toNat : ℤ) : ℝ) ≤ ((⌊B⌋ : ℤ) : ℝ) := by
        exact_mod_cast (le_of_eq (Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ ⌊B⌋)))
      push_cast at h4
      exact le_trans h4 (Int.floor_le B)
    push_cast at h2
    linarith
  set r : ℝ := (2:ℝ)^(j+2) * M₁ / M₃ with hr
  have hrnn : 0 ≤ r := by rw [hr]; positivity
  have hrlt : r < 2 * T^6 := by
    have h1 : (2:ℝ)^(j+2) = 4 * (2:ℝ)^j := by rw [pow_add]; ring
    have h2 : 4 * (2:ℝ)^j * M₁ / M₃ ≤ 4 * B * M₁ / M₃ := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hM₃pos)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2jB (by norm_num)) hM₁.le
    have h3 : 4 * B * M₁ / M₃ ≤ 2 * T^η * M₁ / M₃ := by
      rw [show (4:ℝ) * B * M₁ / M₃ = 2 * (2*B) * M₁ / M₃ by ring]
      apply div_le_div_of_nonneg_right _ (le_of_lt hM₃pos)
      nlinarith [h2B, hM₁.le]
    have h4 : 2 * T^η * M₁ / M₃ < 2 * T^6 := by
      have hh : T^η * M₁ / M₃ < T^6 := lt_of_lt_of_le hξgt hξle
      have hh2 : 2 * (T^η * M₁ / M₃) < 2 * T^6 := by linarith
      calc 2 * T^η * M₁ / M₃ = 2 * (T^η * M₁ / M₃) := by ring
        _ < 2 * T^6 := hh2
    rw [hr, h1]
    linarith
  have hP1 : ∀ p ∈ Pj T M₁ M₃ B ξ j, M₁ ≤ |(p.1 : ℝ)| := by
    intro p hp
    have hpwin : p ∈ Pwin T M₁ M₃ B ξ := (Finset.mem_filter.mp hp).1
    have hpm : p ∈ (R1 M₁).product
        (Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B)) :=
      (Finset.mem_filter.mp hpwin).1
    exact R1_le_abs (Finset.mem_product.mp hpm).1
  have hP1mem : ∀ p ∈ Pj T M₁ M₃ B ξ j, p.1 ∈ R1 M₁ := by
    intro p hp
    have hpwin : p ∈ Pwin T M₁ M₃ B ξ := (Finset.mem_filter.mp hp).1
    have hpm : p ∈ (R1 M₁).product
        (Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B)) :=
      (Finset.mem_filter.mp hpwin).1
    exact (Finset.mem_product.mp hpm).1
  have hP2 : ∀ p ∈ Pj T M₁ M₃ B ξ j, |((p.1 : ℝ) * (p.2 : ℝ)) - ξ| ≤ r := by
    intro p hp
    have hlay : (2:ℝ)^j ≤ |M₃ * ((p.2 : ℝ) - ξ / (p.1 : ℝ))| ∧
        |M₃ * ((p.2 : ℝ) - ξ / (p.1 : ℝ))| < (2:ℝ)^(j+1) := (Finset.mem_filter.mp hp).2
    have hmem := hP1mem p hp
    have h1 : (p.1 : ℝ) ≠ 0 := by
      have h2 : M₁ < |(p.1 : ℝ)| := (Finset.mem_filter.mp hmem).2
      intro h; rw [h] at h2; simp only [Int.cast_zero, abs_zero] at h2; linarith
    have h2 : |(p.1 : ℝ)| ≤ 2 * M₁ := abs_le_two_mul_of_mem_R1 hmem
    have h3 : |(p.2 : ℝ) - ξ / (p.1 : ℝ)| < (2:ℝ)^(j+1) / M₃ := by
      have h4 : M₃ * |(p.2 : ℝ) - ξ / (p.1 : ℝ)| < (2:ℝ)^(j+1) := by
        have h5 := hlay.2
        rwa [abs_mul, abs_of_pos hM₃pos] at h5
      rw [lt_div_iff₀ hM₃pos, mul_comm]
      exact h4
    have hmul : |((p.1 : ℝ) * (p.2 : ℝ)) - ξ|
        = |(p.1 : ℝ)| * |(p.2 : ℝ) - ξ / (p.1 : ℝ)| := by
      rw [← abs_mul]; congr 1; field_simp
    rw [hmul]
    calc |(p.1 : ℝ)| * |(p.2 : ℝ) - ξ / (p.1 : ℝ)|
        ≤ (2 * M₁) * ((2:ℝ)^(j+1) / M₃) :=
          mul_le_mul h2 h3.le (abs_nonneg _) (by positivity)
      _ = r := by rw [hr]; ring
  have hP3 : ∀ p ∈ Pj T M₁ M₃ B ξ j, p.1 * p.2 ≠ 0 := by
    intro p hp h0
    have hmem := hP1mem p hp
    have hp1 : (p.1 : ℝ) ≠ 0 := by
      have h2 : M₁ < |(p.1 : ℝ)| := (Finset.mem_filter.mp hmem).2
      intro h; rw [h] at h2; simp only [Int.cast_zero, abs_zero] at h2; linarith
    have hp2 : p.2 = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · rw [h] at hp1; simp only [Int.cast_zero] at hp1; exact absurd rfl hp1
      · exact h
    have hpwin : p ∈ Pwin T M₁ M₃ B ξ := (Finset.mem_filter.mp hp).1
    have habs : |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ B / M₃ := (Finset.mem_filter.mp hpwin).2.2
    rw [hp2] at habs
    simp only [Int.cast_zero, zero_sub, abs_neg] at habs
    rw [abs_div, div_le_div_iff₀ (abs_pos.mpr hp1) hM₃pos] at habs
    have hpl : |(p.1 : ℝ)| ≤ 2 * M₁ := abs_le_two_mul_of_mem_R1 hmem
    have hbm : B * |(p.1 : ℝ)| ≤ B * (2 * M₁) := mul_le_mul_of_nonneg_left hpl (by linarith : (0:ℝ) ≤ B)
    have hstep : |ξ| * M₃ ≤ T^η * M₁ := by
      have h2' : (2:ℝ)*B*M₁ ≤ T^η*M₁ := by nlinarith [h2B, hM₁.le]
      linarith
    have : |ξ| ≤ T^η * M₁ / M₃ := by rw [le_div_iff₀ hM₃pos]; linarith
    linarith
  have hmain := hCcnt M₁ r (T^6) hM₁ hrnn (one_le_pow₀ hT) ξ hξle
    (Pj T M₁ M₃ B ξ j) hP1 hP2 hP3
  have hXr : T^6 + r + 2 ≤ 5 * T^6 := by linarith [hrlt, hT6]
  have hrpow : (T^6 + r + 2)^εc ≤ (5:ℝ)^εc * T^(6*εc) := by
    have h1 : (5*T^6)^εc = (5:ℝ)^εc * T^(6*εc) := by
      rw [Real.mul_rpow (by norm_num) (by positivity),
        show (T:ℝ)^6 = (T:ℝ)^((6:ℕ):ℝ) from (Real.rpow_natCast T 6).symm,
        ← Real.rpow_mul hT1.le]
      norm_num
    rw [← h1]
    exact Real.rpow_le_rpow (by positivity) hXr hεc.le
  have hr2 : 2*r + 1 ≤ 9 * (1 + (2:ℝ)^j * M₁/M₃) := by
    rw [hr]
    have h1 : (2:ℝ)^(j+2) = 4*(2:ℝ)^j := by rw [pow_add]; ring
    rw [h1]
    have hkey : (2:ℝ)*(4*(2:ℝ)^j*M₁/M₃) + 1 = 8*((2:ℝ)^j*M₁/M₃) + 1 := by ring
    rw [hkey]
    have hu : (0:ℝ) ≤ (2:ℝ)^j*M₁/M₃ := by positivity
    linarith
  calc ((Pj T M₁ M₃ B ξ j).card : ℝ)
      ≤ Ccnt * (T^6 + r + 2)^εc * (2*r+1) := hmain
    _ ≤ Ccnt * ((5:ℝ)^εc * T^(6*εc)) * (9*(1 + (2:ℝ)^j*M₁/M₃)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hrpow hCcntpos.le) hr2 ?_ ?_
        · positivity
        · positivity
    _ = Ccnt * (5 : ℝ)^εc * T ^ (6 * εc) * 9 * (1 + (2 : ℝ)^j * M₁ / M₃) := by ring

/-! ### The layer majorant -/

lemma psi1hat_sq_le_layer {K : ℝ} {Cpsi : ℝ} (hCpsinn : 0 ≤ Cpsi)
    (hCpsi : ∀ y : ℝ, ‖psi1hat K y‖ ≤ Cpsi / (1 + |y|)^3)
    {j : ℕ} {t : ℝ} (ht : (2:ℝ)^j ≤ |t|) :
    ‖psi1hat K t‖^2 ≤ Cpsi^2 / (2:ℝ)^(6*j) := by
  have h2 : (2:ℝ)^j ≤ 1 + |t| := by linarith [abs_nonneg t]
  have h3 : (2:ℝ)^(3*j) ≤ (1 + |t|)^3 := by
    have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (2:ℝ)^j) h2 3
    rwa [pow_two_mul j 3] at h
  have h1 : ‖psi1hat K t‖ ≤ Cpsi / (2:ℝ)^(3*j) :=
    (hCpsi t).trans (div_le_div_of_nonneg_left hCpsinn (by positivity) h3)
  have h5 : ((2:ℝ)^(3*j))^2 = (2:ℝ)^(6*j) := by
    rw [pow_two_mul, show 2*(3*j) = 6*j by ring]
  calc ‖psi1hat K t‖^2 ≤ (Cpsi / (2:ℝ)^(3*j))^2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = Cpsi^2 / (2:ℝ)^(6*j) := by rw [div_pow, h5]

lemma wtr_layer_majorant {K T B M₁ M₂ M₃ ξ : ℝ} (hM₃ : 0 < M₃) {Cpsi : ℝ}
    (hCpsinn : 0 ≤ Cpsi) (hCpsi : ∀ y : ℝ, ‖psi1hat K y‖ ≤ Cpsi / (1 + |y|)^3)
    (f : ℝ → ℝ) (j : ℕ) :
    ∑ p ∈ Pj T M₁ M₃ B ξ j, ‖aTerm K M₂ M₃ f ξ p‖^2
      ≤ M₃^2 * Cpsi^2 / (2:ℝ)^(6*j) * ((2:ℝ)^(j+2)/M₃ + 1) *
          ∑ m₁ ∈ R1 M₁, (1/(m₁:ℝ)^2) * ‖Bsum f M₂ (ξ/(m₁:ℝ))‖^2 := by
  rw [Pj, Pwin, Finset.filter_filter, Finset.sum_filter, Finset.product_eq_sprod,
    Finset.sum_product]
  have hterm : ∀ x ∈ R1 M₁,
      ∑ y ∈ Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B),
          (if (2 / M₃ < |(y:ℝ) - ξ / (x:ℝ)| ∧ |(y:ℝ) - ξ / (x:ℝ)| ≤ B / M₃) ∧
              ((2:ℝ)^j ≤ |M₃ * ((y:ℝ) - ξ / (x:ℝ))| ∧
              |M₃ * ((y:ℝ) - ξ / (x:ℝ))| < (2:ℝ)^(j+1))
            then ‖aTerm K M₂ M₃ f ξ (x, y)‖^2 else 0)
        ≤ (1/(x:ℝ)^2) * ‖Bsum f M₂ (ξ/(x:ℝ))‖^2 *
            (M₃^2 * Cpsi^2 / (2:ℝ)^(6*j) * ((2:ℝ)^(j+2)/M₃ + 1)) := by
    intro x hx
    have hstep1 : ∑ y ∈ Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B),
          (if (2 / M₃ < |(y:ℝ) - ξ / (x:ℝ)| ∧ |(y:ℝ) - ξ / (x:ℝ)| ≤ B / M₃) ∧
              ((2:ℝ)^j ≤ |M₃ * ((y:ℝ) - ξ / (x:ℝ))| ∧
              |M₃ * ((y:ℝ) - ξ / (x:ℝ))| < (2:ℝ)^(j+1))
            then ‖aTerm K M₂ M₃ f ξ (x, y)‖^2 else 0)
        ≤ ∑ y ∈ Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B),
          (if (2:ℝ)^j ≤ |M₃ * ((y:ℝ) - ξ / (x:ℝ))| ∧
              |M₃ * ((y:ℝ) - ξ / (x:ℝ))| < (2:ℝ)^(j+1)
            then ‖aTerm K M₂ M₃ f ξ (x, y)‖^2 else 0) := by
      apply Finset.sum_le_sum
      intro y hy
      by_cases h : (2 / M₃ < |(y:ℝ) - ξ / (x:ℝ)| ∧ |(y:ℝ) - ξ / (x:ℝ)| ≤ B / M₃) ∧
              ((2:ℝ)^j ≤ |M₃ * ((y:ℝ) - ξ / (x:ℝ))| ∧
              |M₃ * ((y:ℝ) - ξ / (x:ℝ))| < (2:ℝ)^(j+1))
      · rw [if_pos h, if_pos h.2]
      · rw [if_neg h]
        by_cases h2 : (2:ℝ)^j ≤ |M₃ * ((y:ℝ) - ξ / (x:ℝ))| ∧
              |M₃ * ((y:ℝ) - ξ / (x:ℝ))| < (2:ℝ)^(j+1)
        · rw [if_pos h2]; positivity
        · rw [if_neg h2]
    refine hstep1.trans ?_
    have hstep2 : ∑ y ∈ Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B),
          (if (2:ℝ)^j ≤ |M₃ * ((y:ℝ) - ξ / (x:ℝ))| ∧
              |M₃ * ((y:ℝ) - ξ / (x:ℝ))| < (2:ℝ)^(j+1)
            then ‖aTerm K M₂ M₃ f ξ (x, y)‖^2 else 0)
        = ∑ y ∈ Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B),
          (if (2:ℝ)^j ≤ |M₃ * ((y:ℝ) - ξ / (x:ℝ))| ∧
              |M₃ * ((y:ℝ) - ξ / (x:ℝ))| < (2:ℝ)^(j+1)
            then (1/(x:ℝ)^2) * ‖Bsum f M₂ (ξ/(x:ℝ))‖^2 * M₃^2 *
              ‖psi1hat K (M₃ * ((y:ℝ) - ξ / (x:ℝ)))‖^2 else 0) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [norm_aTerm_sq]
    rw [hstep2]
    have hker : ∀ y : ℤ, ((2:ℝ)^j ≤ |M₃ * ((y:ℝ) - ξ / (x:ℝ))| ∧
              |M₃ * ((y:ℝ) - ξ / (x:ℝ))| < (2:ℝ)^(j+1)) →
        ‖psi1hat K (M₃ * ((y:ℝ) - ξ / (x:ℝ)))‖^2 ≤ Cpsi^2 / (2:ℝ)^(6*j) :=
      fun y hy => psi1hat_sq_le_layer hCpsinn hCpsi hy.1
    calc ∑ y ∈ Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B),
          (if (2:ℝ)^j ≤ |M₃ * ((y:ℝ) - ξ / (x:ℝ))| ∧
              |M₃ * ((y:ℝ) - ξ / (x:ℝ))| < (2:ℝ)^(j+1)
            then (1/(x:ℝ)^2) * ‖Bsum f M₂ (ξ/(x:ℝ))‖^2 * M₃^2 *
              ‖psi1hat K (M₃ * ((y:ℝ) - ξ / (x:ℝ)))‖^2 else 0)
        ≤ ∑ y ∈ Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B),
          (if (2:ℝ)^j ≤ |M₃ * ((y:ℝ) - ξ / (x:ℝ))| ∧
              |M₃ * ((y:ℝ) - ξ / (x:ℝ))| < (2:ℝ)^(j+1)
            then (1/(x:ℝ)^2) * ‖Bsum f M₂ (ξ/(x:ℝ))‖^2 * M₃^2 *
              (Cpsi^2 / (2:ℝ)^(6*j)) else 0) := by
          apply Finset.sum_le_sum
          intro y hy
          by_cases h : (2:ℝ)^j ≤ |M₃ * ((y:ℝ) - ξ / (x:ℝ))| ∧
              |M₃ * ((y:ℝ) - ξ / (x:ℝ))| < (2:ℝ)^(j+1)
          · rw [if_pos h, if_pos h]
            exact mul_le_mul_of_nonneg_left (hker y h) (by positivity)
          · rw [if_neg h, if_neg h]
      _ = (1/(x:ℝ)^2) * ‖Bsum f M₂ (ξ/(x:ℝ))‖^2 * M₃^2 * (Cpsi^2 / (2:ℝ)^(6*j)) *
            (((Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B)).filter
              (fun y : ℤ => (2:ℝ)^j ≤ |M₃ * ((y:ℝ) - ξ / (x:ℝ))| ∧
                |M₃ * ((y:ℝ) - ξ / (x:ℝ))| < (2:ℝ)^(j+1))).card : ℝ) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ (1/(x:ℝ)^2) * ‖Bsum f M₂ (ξ/(x:ℝ))‖^2 * M₃^2 * (Cpsi^2 / (2:ℝ)^(6*j)) *
            ((2:ℝ)^(j+2)/M₃ + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact card_layer_annulus_le hM₃ j (Lwin T M₁ M₃ B)
      _ = (1/(x:ℝ)^2) * ‖Bsum f M₂ (ξ/(x:ℝ))‖^2 *
            (M₃^2 * Cpsi^2 / (2:ℝ)^(6*j) * ((2:ℝ)^(j+2)/M₃ + 1)) := by ring
  calc ∑ x ∈ R1 M₁, ∑ y ∈ Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B),
        (if (2 / M₃ < |(y:ℝ) - ξ / (x:ℝ)| ∧ |(y:ℝ) - ξ / (x:ℝ)| ≤ B / M₃) ∧
            ((2:ℝ)^j ≤ |M₃ * ((y:ℝ) - ξ / (x:ℝ))| ∧
            |M₃ * ((y:ℝ) - ξ / (x:ℝ))| < (2:ℝ)^(j+1))
          then ‖aTerm K M₂ M₃ f ξ (x, y)‖^2 else 0)
      ≤ ∑ x ∈ R1 M₁, (1/(x:ℝ)^2) * ‖Bsum f M₂ (ξ/(x:ℝ))‖^2 *
            (M₃^2 * Cpsi^2 / (2:ℝ)^(6*j) * ((2:ℝ)^(j+2)/M₃ + 1)) :=
        Finset.sum_le_sum hterm
    _ = M₃^2 * Cpsi^2 / (2:ℝ)^(6*j) * ((2:ℝ)^(j+2)/M₃ + 1) *
          ∑ m₁ ∈ R1 M₁, (1/(m₁:ℝ)^2) * ‖Bsum f M₂ (ξ/(m₁:ℝ))‖^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring

/-! ### The layer decomposition -/

lemma wtr_layer_decomp {K T η B M₁ M₂ M₃ : ℝ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃) {f : ℝ → ℝ}
    {ξ : ℝ} (hξ : ξ ∈ Set.Icc (-(T ^ 6)) (T ^ 6)
        \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃)) :
    (∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
        Wwin K M₃ B (ξ / (m₁ : ℝ)))
      = ∑ j ∈ Finset.range (Nat.log 2 (⌊B⌋).toNat + 1),
          ∑ p ∈ Pj T M₁ M₃ B ξ j, aTerm K M₂ M₃ f ξ p := by
  obtain ⟨hξle, -⟩ := mem_wtrRegion hξ
  have hS := Wwin_sum_eq_pairs K T M₁ M₂ M₃ B hM₁ hM₃ (f := f) hξle
  rw [hS]
  have hPJ : ∀ p ∈ Pwin T M₁ M₃ B ξ,
      (∑ j ∈ Finset.range (Nat.log 2 (⌊B⌋).toNat + 1),
          (if p ∈ Pj T M₁ M₃ B ξ j then (1:ℂ) else 0)) = 1 := by
    intro p hp
    have hpwin : p ∈ Pwin T M₁ M₃ B ξ := hp
    rw [Pwin, Finset.mem_filter] at hp
    obtain ⟨hpm, hwin⟩ := hp
    have hpm' : p.1 ∈ R1 M₁ ∧ p.2 ∈ Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B) :=
      Finset.mem_product.mp hpm
    obtain ⟨hm₁, hℓ⟩ := hpm'

    set v : ℝ := |M₃ * (((p.2 : ℝ)) - ξ / (p.1 : ℝ))| with hv
    have hv1 : 1 ≤ v := by
      rw [hv, abs_mul, abs_of_pos hM₃]
      have h2 : (2:ℝ)/M₃ ≤ |(p.2 : ℝ) - ξ / (p.1 : ℝ)| := hwin.1.le
      have h3 : M₃ * (2/M₃) ≤ M₃ * |(p.2 : ℝ) - ξ / (p.1 : ℝ)| :=
        mul_le_mul_of_nonneg_left h2 hM₃.le
      rw [mul_div_cancel₀] at h3
      · linarith
      · exact ne_of_gt hM₃
    obtain ⟨j0, hj1, hj2⟩ := layer_index_exists hv1
    have hvB : v ≤ B := by
      rw [hv, abs_mul, abs_of_pos hM₃]
      have h3 : M₃ * |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ M₃ * (B/M₃) :=
        mul_le_mul_of_nonneg_left hwin.2 hM₃.le
      rwa [mul_div_cancel₀ _ (ne_of_gt hM₃)] at h3
    have h2jB : (2:ℕ)^j0 ≤ (⌊B⌋).toNat := by
      have h4 : (((2:ℕ)^j0 : ℤ) : ℝ) ≤ B := by
        push_cast
        exact le_trans hj1 hvB
      have h5 : ((2:ℕ)^j0 : ℤ) ≤ ⌊B⌋ := Int.le_floor.mpr h4
      have h6 : (0:ℤ) ≤ ⌊B⌋ := le_trans (by positivity : (0:ℤ) ≤ ((2:ℕ)^j0 : ℤ)) h5
      have h8 : ((⌊B⌋).toNat : ℤ) = ⌊B⌋ := Int.toNat_of_nonneg h6
      omega
    have hj0lt : j0 < Nat.log 2 (⌊B⌋).toNat + 1 := by
      have h := Nat.le_log_of_pow_le (b:=2) (by norm_num) h2jB
      omega
    have hpj : p ∈ Pj T M₁ M₃ B ξ j0 := by
      rw [Pj, Finset.mem_filter]
      exact ⟨hpwin, by rw [hv] at hj1 hj2; exact ⟨hj1, hj2⟩⟩
    rw [Finset.sum_eq_single j0]
    · simp [hpj]
    · intro j hj hjne
      rw [if_neg]
      intro hpj'
      have hlay : (2:ℝ)^j ≤ v ∧ v < (2:ℝ)^(j+1) := by
        have h := (Finset.mem_filter.mp hpj').2
        rw [hv]
        exact h
      exact hjne (layer_index_unique hlay.1 hlay.2 hj1 hj2)
    · intro hnot
      exact absurd (Finset.mem_range.mpr hj0lt) hnot
  calc ∑ p ∈ Pwin T M₁ M₃ B ξ, aTerm K M₂ M₃ f ξ p
      = ∑ p ∈ Pwin T M₁ M₃ B ξ,
          (∑ j ∈ Finset.range (Nat.log 2 (⌊B⌋).toNat + 1),
            (if p ∈ Pj T M₁ M₃ B ξ j then (1:ℂ) else 0)) * aTerm K M₂ M₃ f ξ p := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [hPJ p hp, one_mul]
    _ = ∑ p ∈ Pwin T M₁ M₃ B ξ,
          ∑ j ∈ Finset.range (Nat.log 2 (⌊B⌋).toNat + 1),
            (if p ∈ Pj T M₁ M₃ B ξ j then aTerm K M₂ M₃ f ξ p else 0) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h : p ∈ Pj T M₁ M₃ B ξ j
        · rw [if_pos h, if_pos h, one_mul]
        · rw [if_neg h, if_neg h, zero_mul]
    _ = ∑ j ∈ Finset.range (Nat.log 2 (⌊B⌋).toNat + 1),
          ∑ p ∈ Pwin T M₁ M₃ B ξ,
            (if p ∈ Pj T M₁ M₃ B ξ j then aTerm K M₂ M₃ f ξ p else 0) :=
        Finset.sum_comm
    _ = ∑ j ∈ Finset.range (Nat.log 2 (⌊B⌋).toNat + 1),
          ∑ p ∈ Pj T M₁ M₃ B ξ j, aTerm K M₂ M₃ f ξ p := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Finset.sum_filter (s := Pwin T M₁ M₃ B ξ)
          (p := fun p => p ∈ Pj T M₁ M₃ B ξ j)]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext p
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_filter.mp h).1, h⟩⟩

/-! ### The integral of the elementary majorant -/

lemma wtr_majorant_integral {T η B M₁ M₂ M₃ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6))
        \ (Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃)),
        ∑ m₁ ∈ R1 M₁, (1 / (m₁ : ℝ) ^ 2) * ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2)
      ≤ 8 * ∫ s, (Hsum M₂ f s) ^ 2 := by
  set R : Set ℝ := Set.Icc (-(T ^ 6)) (T ^ 6)
      \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃) with hR
  have hzene : ∀ m₁ ∈ R1 M₁, m₁ ≠ 0 := by
    intro m₁ hm₁ h0
    have h1 : M₁ < |((m₁ : ℝ))| := (Finset.mem_filter.mp hm₁).2
    rw [h0] at h1; simp only [Int.cast_zero, abs_zero] at h1; linarith
  have hI : 0 ≤ ∫ s, (Hsum M₂ f s) ^ 2 := integral_nonneg (fun s => sq_nonneg _)
  have hInt : ∀ m₁ ∈ R1 M₁, Integrable
      (fun ξ : ℝ => (1 / (m₁ : ℝ) ^ 2) * ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2) :=
    fun m₁ hm₁ => ((bsum_hsum_plancherel f M₂ hM₂ hf hcs (hzene m₁ hm₁)).1).const_mul _
  have hterm : ∀ m₁ ∈ R1 M₁,
      (∫ ξ in R, (1 / (m₁ : ℝ) ^ 2) * ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2)
        ≤ (1 / |(m₁ : ℝ)|) * ∫ s, (Hsum M₂ f s) ^ 2 := by
    intro m₁ hm₁
    have hne : (|((m₁ : ℝ))|) ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast hzene m₁ hm₁)
    have hb : (∫ ξ : ℝ, (1 / (m₁ : ℝ) ^ 2) * ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2)
        = (1 / |(m₁ : ℝ)|) * ∫ s, (Hsum M₂ f s) ^ 2 := by
      rw [MeasureTheory.integral_const_mul,
        (bsum_hsum_plancherel f M₂ hM₂ hf hcs (hzene m₁ hm₁)).2]
      have hcoe : (1 / (m₁ : ℝ) ^ 2) * |(m₁ : ℝ)| = 1 / |(m₁ : ℝ)| := by
        rw [← sq_abs (m₁ : ℝ), one_div, one_div]
        have hsq : (|(m₁ : ℝ)|)^2 = |(m₁ : ℝ)| * |(m₁ : ℝ)| := by ring
        rw [hsq, mul_inv, mul_assoc, inv_mul_cancel₀ hne, mul_one]
      calc (1 / (m₁ : ℝ) ^ 2) * (|(m₁ : ℝ)| * ∫ s, (Hsum M₂ f s) ^ 2)
          = ((1 / (m₁ : ℝ) ^ 2) * |(m₁ : ℝ)|) * ∫ s, (Hsum M₂ f s) ^ 2 := by ring
        _ = (1 / |(m₁ : ℝ)|) * ∫ s, (Hsum M₂ f s) ^ 2 := by rw [hcoe]
    calc (∫ ξ in R, (1 / (m₁ : ℝ) ^ 2) * ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2)
        ≤ ∫ ξ : ℝ, (1 / (m₁ : ℝ) ^ 2) * ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2 :=
          setIntegral_le_integral (hInt m₁ hm₁) (Filter.Eventually.of_forall (fun ξ => by positivity))
      _ = (1 / |(m₁ : ℝ)|) * ∫ s, (Hsum M₂ f s) ^ 2 := hb
  calc (∫ ξ in R, ∑ m₁ ∈ R1 M₁, (1 / (m₁ : ℝ) ^ 2) * ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2)
      = ∑ m₁ ∈ R1 M₁, ∫ ξ in R, (1 / (m₁ : ℝ) ^ 2) * ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2 := by
        rw [MeasureTheory.integral_finsetSum (R1 M₁)]
        intro m₁ hm₁
        exact (hInt m₁ hm₁).integrableOn
    _ ≤ ∑ m₁ ∈ R1 M₁, (1 / |(m₁ : ℝ)|) * ∫ s, (Hsum M₂ f s) ^ 2 := Finset.sum_le_sum hterm
    _ = (∑ m₁ ∈ R1 M₁, 1 / |(m₁ : ℝ)|) * ∫ s, (Hsum M₂ f s) ^ 2 := by rw [Finset.sum_mul]
    _ ≤ 8 * ∫ s, (Hsum M₂ f s) ^ 2 :=
        mul_le_mul_of_nonneg_right (sum_inv_abs_R1_le M₁ hM₁) hI

/-! ### Geometric summation -/

lemma wtr_geom_sum_le (A C : ℝ) (hA : 0 ≤ A) (hC : 1 ≤ C) (N : ℕ) :
    (∑ j ∈ Finset.range N,
        (2:ℝ)^j * (1 + (2:ℝ)^j * A) * (C * ((2:ℝ)^(j+2) + C)) / (2:ℝ)^(6*j))
      ≤ 8*C + 2*C^2 + 8*(A*C) + 2*(A*C^2) := by
  have hpt : ∀ j : ℕ,
      (2:ℝ)^j * (1 + (2:ℝ)^j * A) * (C * ((2:ℝ)^(j+2) + C)) / (2:ℝ)^(6*j)
        = 4*C*((2:ℝ)^(4*j))⁻¹ + C^2*((2:ℝ)^(5*j))⁻¹
          + 4*(A*C)*((2:ℝ)^(3*j))⁻¹ + (A*C^2)*((2:ℝ)^(4*j))⁻¹ := by
    intro j
    have h6 : (2:ℝ)^(6*j) = ((2:ℝ)^j)^6 := (pow_two_mul j 6).symm
    have h4 : (2:ℝ)^(4*j) = ((2:ℝ)^j)^4 := (pow_two_mul j 4).symm
    have h5 : (2:ℝ)^(5*j) = ((2:ℝ)^j)^5 := (pow_two_mul j 5).symm
    have h3 : (2:ℝ)^(3*j) = ((2:ℝ)^j)^3 := (pow_two_mul j 3).symm
    have hj2 : (2:ℝ)^(j+2) = 4*(2:ℝ)^j := by rw [pow_add]; ring
    rw [h6, h4, h5, h3, hj2]
    field_simp
    ring_nf
  have h4b := sum_inv_two_pow_mul_le 4 N (by norm_num)
  have h5b := sum_inv_two_pow_mul_le 5 N (by norm_num)
  have h3b := sum_inv_two_pow_mul_le 3 N (by norm_num)
  have hsum1 : (∑ j ∈ Finset.range N,
        (2:ℝ)^j * (1 + (2:ℝ)^j * A) * (C * ((2:ℝ)^(j+2) + C)) / (2:ℝ)^(6*j))
      = ∑ j ∈ Finset.range N, (4*C*((2:ℝ)^(4*j))⁻¹ + C^2*((2:ℝ)^(5*j))⁻¹
          + 4*(A*C)*((2:ℝ)^(3*j))⁻¹ + (A*C^2)*((2:ℝ)^(4*j))⁻¹) :=
    Finset.sum_congr rfl (fun j _ => hpt j)
  rw [hsum1, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  have h1 : 4*C*(∑ j ∈ Finset.range N, ((2:ℝ)^(4*j))⁻¹) ≤ 4*C*2 :=
    mul_le_mul_of_nonneg_left h4b (by positivity)
  have h2 : C^2*(∑ j ∈ Finset.range N, ((2:ℝ)^(5*j))⁻¹) ≤ C^2*2 :=
    mul_le_mul_of_nonneg_left h5b (by positivity)
  have h3' : 4*(A*C)*(∑ j ∈ Finset.range N, ((2:ℝ)^(3*j))⁻¹) ≤ 4*(A*C)*2 :=
    mul_le_mul_of_nonneg_left h3b (by positivity)
  have h3'' : (A*C^2)*(∑ j ∈ Finset.range N, ((2:ℝ)^(4*j))⁻¹) ≤ (A*C^2)*2 :=
    mul_le_mul_of_nonneg_left h4b (by positivity)
  linarith

/-! ### The main statement -/

theorem windowTrunc_L2_bound {C₀ K : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (T η B : ℝ) (M₁ M₂ M₃ : ℝ),
      1 ≤ T → 0 < η → 2 ≤ B → 2 * B ≤ T ^ η → 0 < M₁ → 0 < M₂ → 1 ≤ M₃ →
      ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
      (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6))
          \ (Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃)),
        ‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
            Wwin K M₃ B (ξ / (m₁ : ℝ))‖ ^ 2) ≤
        C * T ^ (6 * ε) * (M₁ + M₁ * M₃ + M₃ + M₃ ^ 2) * ∫ s, (Hsum M₂ f s) ^ 2 := by
  intro ε hε
  set εc : ℝ := ε / 2 with hεcdef
  have hεcpos : 0 < εc := by rw [hεcdef]; linarith
  obtain ⟨Ccnt, hCcntpos, hCcnt⟩ := card_mul_pairs_le_nonzero hεcpos
  obtain ⟨Cpsi, hCpsipos, hCpsi⟩ := psi1hat_decay K hK 3
  have hCpsinn : 0 ≤ Cpsi := hCpsipos.le
  refine ⟨1440 * Ccnt * (5:ℝ)^εc * Cpsi^2 + 1, by positivity, ?_⟩
  intro T η B M₁ M₂ M₃ hT hη hB h2B hM₁ hM₂ hM₃ f hf hfnn hsup
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  have hT1 : (0:ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hcs : HasCompactSupport f := hasCompactSupport_of_SuppHyp hsup
  set R : Set ℝ := Set.Icc (-(T ^ 6)) (T ^ 6)
      \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃) with hRdef
  set D : ℝ := ∫ s, (Hsum M₂ f s) ^ 2 with hDdef
  have hDnn : 0 ≤ D := by rw [hDdef]; exact integral_nonneg (fun s => sq_nonneg _)
  set Bm : ℝ → ℝ := fun ξ => ∑ m₁ ∈ R1 M₁, (1/(m₁:ℝ)^2) * ‖Bsum f M₂ (ξ/(m₁:ℝ))‖^2
    with hBmdef
  have hBmnn : ∀ ξ, 0 ≤ Bm ξ := by
    intro ξ; rw [hBmdef]; exact Finset.sum_nonneg (fun m₁ _ => by positivity)
  have hBmcont : Continuous Bm := by
    rw [hBmdef]
    refine continuous_finsetSum _ (fun m₁ _ => ?_)
    exact (((continuous_Bsum hf hcs).comp (continuous_id.div_const _)).norm.pow 2).const_mul _
  have hRmeas : MeasurableSet R := by
    rw [hRdef]; exact measurableSet_Icc.diff measurableSet_Icc
  have hBmint : IntegrableOn Bm R :=
    (hBmcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      (by rw [hRdef]; exact Set.diff_subset)
  have hBmbound : (∫ ξ in R, Bm ξ) ≤ 8 * D := by
    rw [hRdef, hBmdef, hDdef]
    exact wtr_majorant_integral (T:=T) (η:=η) (B:=B) hM₁ hM₂ hf hcs
  set Wt : ℝ := ∑ j ∈ Finset.range (Nat.log 2 (⌊B⌋).toNat + 1), (2:ℝ)^j *
      (Ccnt * (5:ℝ)^εc * T^(6*εc) * 9 * (1 + (2:ℝ)^j * M₁/M₃)) *
      (M₃^2 * Cpsi^2 / (2:ℝ)^(6*j) * ((2:ℝ)^(j+2)/M₃ + 1)) with hWtdef
  have hWtnn : 0 ≤ Wt := by
    rw [hWtdef]
    exact Finset.sum_nonneg (fun j _ => by positivity)
  have hpoint : ∀ ξ ∈ R,
      ‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
            Wwin K M₃ B (ξ / (m₁ : ℝ))‖ ^ 2 ≤ 2 * Wt * Bm ξ := by
    intro ξ hξ
    rw [wtr_layer_decomp (K:=K) (T:=T) (η:=η) (B:=B) (M₁:=M₁) (M₂:=M₂) (M₃:=M₃)
      hM₁ hM₃pos hξ]
    have hcs1 : ‖∑ j ∈ Finset.range (Nat.log 2 (⌊B⌋).toNat + 1),
          ∑ p ∈ Pj T M₁ M₃ B ξ j, aTerm K M₂ M₃ f ξ p‖^2
        ≤ (∑ j ∈ Finset.range (Nat.log 2 (⌊B⌋).toNat + 1), ((2:ℝ)^j)⁻¹) *
          (∑ j ∈ Finset.range (Nat.log 2 (⌊B⌋).toNat + 1),
            ‖∑ p ∈ Pj T M₁ M₃ B ξ j, aTerm K M₂ M₃ f ξ p‖^2 / ((2:ℝ)^j)⁻¹) :=
      norm_sum_sq_le_weighted _ _ _ (fun j hj => by positivity)
    have hgeo : (∑ j ∈ Finset.range (Nat.log 2 (⌊B⌋).toNat + 1), ((2:ℝ)^j)⁻¹) ≤ 2 :=
      sum_inv_two_pow_le _
    have hj_bound : ∀ j ∈ Finset.range (Nat.log 2 (⌊B⌋).toNat + 1),
        ‖∑ p ∈ Pj T M₁ M₃ B ξ j, aTerm K M₂ M₃ f ξ p‖^2 / ((2:ℝ)^j)⁻¹
          ≤ (2:ℝ)^j * (Ccnt * (5:ℝ)^εc * T^(6*εc) * 9 * (1 + (2:ℝ)^j * M₁/M₃)) *
            (M₃^2 * Cpsi^2 / (2:ℝ)^(6*j) * ((2:ℝ)^(j+2)/M₃ + 1)) * Bm ξ := by
      intro j hj
      rw [div_inv_eq_mul]
      have hY : ‖∑ p ∈ Pj T M₁ M₃ B ξ j, aTerm K M₂ M₃ f ξ p‖^2
          ≤ (Ccnt * (5:ℝ)^εc * T^(6*εc) * 9 * (1 + (2:ℝ)^j * M₁/M₃)) *
            (M₃^2 * Cpsi^2 / (2:ℝ)^(6*j) * ((2:ℝ)^(j+2)/M₃ + 1) * Bm ξ) := by
        calc ‖∑ p ∈ Pj T M₁ M₃ B ξ j, aTerm K M₂ M₃ f ξ p‖^2
            ≤ ((Pj T M₁ M₃ B ξ j).card : ℝ) *
                ∑ p ∈ Pj T M₁ M₃ B ξ j, ‖aTerm K M₂ M₃ f ξ p‖^2 :=
              norm_sum_sq_le_card_mul_sum_norm_sq _ _
          _ ≤ (Ccnt * (5:ℝ)^εc * T^(6*εc) * 9 * (1 + (2:ℝ)^j * M₁/M₃)) *
                ∑ p ∈ Pj T M₁ M₃ B ξ j, ‖aTerm K M₂ M₃ f ξ p‖^2 := by
              apply mul_le_mul_of_nonneg_right
                (wtr_layer_count hT hη hB h2B hM₁ hM₃ hεcpos hCcntpos hCcnt hξ hj)
              positivity
          _ ≤ (Ccnt * (5:ℝ)^εc * T^(6*εc) * 9 * (1 + (2:ℝ)^j * M₁/M₃)) *
                (M₃^2 * Cpsi^2 / (2:ℝ)^(6*j) * ((2:ℝ)^(j+2)/M₃ + 1) * Bm ξ) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              rw [hBmdef]
              exact wtr_layer_majorant hM₃pos hCpsinn hCpsi f j
      calc ‖∑ p ∈ Pj T M₁ M₃ B ξ j, aTerm K M₂ M₃ f ξ p‖^2 * (2:ℝ)^j
          ≤ ((Ccnt * (5:ℝ)^εc * T^(6*εc) * 9 * (1 + (2:ℝ)^j * M₁/M₃)) *
              (M₃^2 * Cpsi^2 / (2:ℝ)^(6*j) * ((2:ℝ)^(j+2)/M₃ + 1) * Bm ξ)) * (2:ℝ)^j :=
            mul_le_mul_of_nonneg_right hY (by positivity)
        _ = (2:ℝ)^j * (Ccnt * (5:ℝ)^εc * T^(6*εc) * 9 * (1 + (2:ℝ)^j * M₁/M₃)) *
              (M₃^2 * Cpsi^2 / (2:ℝ)^(6*j) * ((2:ℝ)^(j+2)/M₃ + 1)) * Bm ξ := by ring
    have hsum2 : (∑ j ∈ Finset.range (Nat.log 2 (⌊B⌋).toNat + 1),
          ‖∑ p ∈ Pj T M₁ M₃ B ξ j, aTerm K M₂ M₃ f ξ p‖^2 / ((2:ℝ)^j)⁻¹)
        ≤ Wt * Bm ξ := by
      calc (∑ j ∈ Finset.range (Nat.log 2 (⌊B⌋).toNat + 1),
            ‖∑ p ∈ Pj T M₁ M₃ B ξ j, aTerm K M₂ M₃ f ξ p‖^2 / ((2:ℝ)^j)⁻¹)
          ≤ ∑ j ∈ Finset.range (Nat.log 2 (⌊B⌋).toNat + 1), (2:ℝ)^j *
              (Ccnt * (5:ℝ)^εc * T^(6*εc) * 9 * (1 + (2:ℝ)^j * M₁/M₃)) *
              (M₃^2 * Cpsi^2 / (2:ℝ)^(6*j) * ((2:ℝ)^(j+2)/M₃ + 1)) * Bm ξ :=
            Finset.sum_le_sum hj_bound
        _ = Wt * Bm ξ := by rw [hWtdef, Finset.sum_mul]
    have hBmξ : 0 ≤ Bm ξ := hBmnn ξ
    calc ‖∑ j ∈ Finset.range (Nat.log 2 (⌊B⌋).toNat + 1),
          ∑ p ∈ Pj T M₁ M₃ B ξ j, aTerm K M₂ M₃ f ξ p‖^2
        ≤ (∑ j ∈ Finset.range (Nat.log 2 (⌊B⌋).toNat + 1), ((2:ℝ)^j)⁻¹) *
            (∑ j ∈ Finset.range (Nat.log 2 (⌊B⌋).toNat + 1),
              ‖∑ p ∈ Pj T M₁ M₃ B ξ j, aTerm K M₂ M₃ f ξ p‖^2 / ((2:ℝ)^j)⁻¹) := hcs1
      _ ≤ 2 * (Wt * Bm ξ) := by
          refine mul_le_mul hgeo hsum2 ?_ ?_
          · positivity
          · norm_num
      _ = 2 * Wt * Bm ξ := by ring
  have hmeas : AEStronglyMeasurable (fun ξ => ‖∑ m₁ ∈ R1 M₁,
        ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
            Wwin K M₃ B (ξ / (m₁ : ℝ))‖^2) (volume.restrict R) := by
    have h2 : AEStronglyMeasurable (fun ξ => ‖wtrS K T M₁ M₂ M₃ B f ξ‖^2)
        (volume.restrict R) :=
      ((measurable_wtrS (K:=K) (T:=T) (M₁:=M₁) (M₂:=M₂) (M₃:=M₃) (B:=B) hf hcs).norm.pow_const 2).aestronglyMeasurable
    refine h2.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hRmeas] with ξ hξ
    rw [wtrS_eq hM₁ hM₃pos hξ]
  have hnn : ∀ ξ, (0:ℝ) ≤ ‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ *
      Bsum f M₂ (ξ / (m₁ : ℝ)) * Wwin K M₃ B (ξ / (m₁ : ℝ))‖^2 := fun ξ => sq_nonneg _
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn) hmeas]
  have hchain : ∫⁻ ξ in R, ENNReal.ofReal (‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ *
        Bsum f M₂ (ξ / (m₁ : ℝ)) * Wwin K M₃ B (ξ / (m₁ : ℝ))‖^2)
      ≤ ENNReal.ofReal (2 * Wt * (8 * D)) := by
    have h1 : ∫⁻ ξ in R, ENNReal.ofReal (‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ *
          Bsum f M₂ (ξ / (m₁ : ℝ)) * Wwin K M₃ B (ξ / (m₁ : ℝ))‖^2)
        ≤ ∫⁻ ξ in R, ENNReal.ofReal (2 * Wt * Bm ξ) := by
      refine lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hRmeas] with ξ hξ
      exact ENNReal.ofReal_le_ofReal (hpoint ξ hξ)
    have h2 : ∫⁻ ξ in R, ENNReal.ofReal (2 * Wt * Bm ξ)
        = ENNReal.ofReal (∫ ξ in R, 2 * Wt * Bm ξ) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (hBmint.const_mul (2*Wt))
        (Filter.Eventually.of_forall (fun ξ => mul_nonneg (by positivity) (hBmnn ξ)))).symm
    have h3 : (∫ ξ in R, 2 * Wt * Bm ξ) = 2 * Wt * (∫ ξ in R, Bm ξ) :=
      MeasureTheory.integral_const_mul _ _
    have h4 : 2 * Wt * (∫ ξ in R, Bm ξ) ≤ 2 * Wt * (8 * D) :=
      mul_le_mul_of_nonneg_left hBmbound (by positivity)
    calc ∫⁻ ξ in R, ENNReal.ofReal (‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ *
          Bsum f M₂ (ξ / (m₁ : ℝ)) * Wwin K M₃ B (ξ / (m₁ : ℝ))‖^2)
        ≤ ∫⁻ ξ in R, ENNReal.ofReal (2 * Wt * Bm ξ) := h1
      _ = ENNReal.ofReal (∫ ξ in R, 2 * Wt * Bm ξ) := h2
      _ = ENNReal.ofReal (2 * Wt * (∫ ξ in R, Bm ξ)) := by rw [h3]
      _ ≤ ENNReal.ofReal (2 * Wt * (8 * D)) := by
          exact ENNReal.ofReal_le_ofReal h4
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hchain).trans ?_
  rw [ENNReal.toReal_ofReal (by positivity)]
  have hWtbound : Wt ≤ 90 * Ccnt * (5:ℝ)^εc * T^(6*εc) * Cpsi^2 *
      (M₁ + M₁*M₃ + M₃ + M₃^2) := by
    rw [hWtdef]
    have hkey : ∀ j : ℕ, (2:ℝ)^j *
          (Ccnt * (5:ℝ)^εc * T^(6*εc) * 9 * (1 + (2:ℝ)^j * M₁/M₃)) *
          (M₃^2 * Cpsi^2 / (2:ℝ)^(6*j) * ((2:ℝ)^(j+2)/M₃ + 1))
        = (9*Ccnt*(5:ℝ)^εc*T^(6*εc)*Cpsi^2) *
          ((2:ℝ)^j * (1 + (2:ℝ)^j * (M₁/M₃)) *
            (M₃ * ((2:ℝ)^(j+2) + M₃)) / (2:ℝ)^(6*j)) := by
      intro j
      have hM₃ne : M₃ ≠ 0 := ne_of_gt hM₃pos
      have h2ne : (2:ℝ)^(6*j) ≠ 0 := by positivity
      field_simp
      try ring
    have hstep : (∑ j ∈ Finset.range (Nat.log 2 (⌊B⌋).toNat + 1), (2:ℝ)^j *
        (Ccnt * (5:ℝ)^εc * T^(6*εc) * 9 * (1 + (2:ℝ)^j * M₁/M₃)) *
        (M₃^2 * Cpsi^2 / (2:ℝ)^(6*j) * ((2:ℝ)^(j+2)/M₃ + 1)))
        = (9*Ccnt*(5:ℝ)^εc*T^(6*εc)*Cpsi^2) *
          (∑ j ∈ Finset.range (Nat.log 2 (⌊B⌋).toNat + 1),
            (2:ℝ)^j * (1 + (2:ℝ)^j * (M₁/M₃)) *
              (M₃ * ((2:ℝ)^(j+2) + M₃)) / (2:ℝ)^(6*j)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => hkey j)
    rw [hstep]
    have hgeo := wtr_geom_sum_le (M₁/M₃) M₃ (by positivity) hM₃
      (Nat.log 2 (⌊B⌋).toNat + 1)
    have hcoef : (0:ℝ) ≤ 9*Ccnt*(5:ℝ)^εc*T^(6*εc)*Cpsi^2 := by positivity
    have hAC1 : M₁/M₃*M₃ = M₁ := by field_simp
    have hAC2 : M₁/M₃*M₃^2 = M₁*M₃ := by
      rw [show M₃^2 = M₃*M₃ by ring, ← mul_assoc, hAC1]
    have hS : 8*M₃ + 2*M₃^2 + 8*M₁ + 2*(M₁*M₃) ≤ 10*(M₁ + M₁*M₃ + M₃ + M₃^2) := by
      have h1 : 8*M₃ ≤ 8*M₃^2 := by nlinarith [hM₃]
      have h2 : 8*M₁ ≤ 10*M₁ := by nlinarith [hM₁]
      have h3 : 2*(M₁*M₃) ≤ 10*(M₁*M₃) :=
        by nlinarith [mul_nonneg hM₁.le (by linarith : (0:ℝ) ≤ M₃)]
      linarith
    have hfin : 8*M₃ + 2*M₃^2 + 8*(M₁/M₃*M₃) + 2*(M₁/M₃*M₃^2)
        ≤ 10*(M₁ + M₁*M₃ + M₃ + M₃^2) := by
      rw [hAC1, hAC2]; exact hS
    calc (9*Ccnt*(5:ℝ)^εc*T^(6*εc)*Cpsi^2) *
          (∑ j ∈ Finset.range (Nat.log 2 (⌊B⌋).toNat + 1),
            (2:ℝ)^j * (1 + (2:ℝ)^j * (M₁/M₃)) *
              (M₃ * ((2:ℝ)^(j+2) + M₃)) / (2:ℝ)^(6*j))
        ≤ (9*Ccnt*(5:ℝ)^εc*T^(6*εc)*Cpsi^2) * (10*(M₁ + M₁*M₃ + M₃ + M₃^2)) :=
          mul_le_mul_of_nonneg_left (le_trans hgeo hfin) hcoef
      _ = 90 * Ccnt * (5:ℝ)^εc * T^(6*εc) * Cpsi^2 * (M₁ + M₁*M₃ + M₃ + M₃^2) := by ring
  have harith : 2 * Wt * (8 * D)
      ≤ (1440 * Ccnt * (5:ℝ)^εc * Cpsi^2 + 1) * T^(6*ε) *
        (M₁ + M₁*M₃ + M₃ + M₃^2) * D := by
    have hA : 2 * Wt * (8 * D) ≤ 2 * (90 * Ccnt * (5:ℝ)^εc * T^(6*εc) * Cpsi^2 *
        (M₁ + M₁*M₃ + M₃ + M₃^2)) * (8 * D) := by
      have h2 : Wt * (8 * D) ≤ (90 * Ccnt * (5:ℝ)^εc * T^(6*εc) * Cpsi^2 *
          (M₁ + M₁*M₃ + M₃ + M₃^2)) * (8 * D) :=
        mul_le_mul_of_nonneg_right hWtbound (by positivity)
      calc 2 * Wt * (8 * D) = 2 * (Wt * (8 * D)) := by ring
        _ ≤ 2 * ((90 * Ccnt * (5:ℝ)^εc * T^(6*εc) * Cpsi^2 *
              (M₁ + M₁*M₃ + M₃ + M₃^2)) * (8 * D)) := by linarith
        _ = 2 * (90 * Ccnt * (5:ℝ)^εc * T^(6*εc) * Cpsi^2 *
              (M₁ + M₁*M₃ + M₃ + M₃^2)) * (8 * D) := by ring
    have h5 : T^(6*εc) ≤ T^(6*ε) := by
      apply Real.rpow_le_rpow_of_exponent_le hT
      rw [hεcdef]; linarith
    calc 2 * Wt * (8 * D)
        ≤ 2 * (90 * Ccnt * (5:ℝ)^εc * T^(6*εc) * Cpsi^2 *
            (M₁ + M₁*M₃ + M₃ + M₃^2)) * (8 * D) := hA
      _ = 1440 * Ccnt * (5:ℝ)^εc * Cpsi^2 * (M₁ + M₁*M₃ + M₃ + M₃^2) *
            T^(6*εc) * D := by ring
      _ ≤ 1440 * Ccnt * (5:ℝ)^εc * Cpsi^2 * (M₁ + M₁*M₃ + M₃ + M₃^2) *
            T^(6*ε) * D := by
          apply mul_le_mul_of_nonneg_right _ hDnn
          apply mul_le_mul_of_nonneg_left h5
          positivity
      _ ≤ (1440 * Ccnt * (5:ℝ)^εc * Cpsi^2 + 1) * T^(6*ε) *
            (M₁ + M₁*M₃ + M₃ + M₃^2) * D := by
          have hvar : (0:ℝ) ≤ T^(6*ε) * ((M₁ + M₁*M₃ + M₃ + M₃^2) * D) := by positivity
          calc 1440 * Ccnt * (5:ℝ)^εc * Cpsi^2 * (M₁ + M₁*M₃ + M₃ + M₃^2) *
                T^(6*ε) * D
              = (1440 * Ccnt * (5:ℝ)^εc * Cpsi^2) *
                (T^(6*ε) * ((M₁ + M₁*M₃ + M₃ + M₃^2) * D)) := by ring
            _ ≤ (1440 * Ccnt * (5:ℝ)^εc * Cpsi^2 + 1) *
                (T^(6*ε) * ((M₁ + M₁*M₃ + M₃ + M₃^2) * D)) :=
                mul_le_mul_of_nonneg_right (by linarith) hvar
            _ = (1440 * Ccnt * (5:ℝ)^εc * Cpsi^2 + 1) * T^(6*ε) *
                (M₁ + M₁*M₃ + M₃ + M₃^2) * D := by ring
  exact harith

end

end Work.GM.Affine
