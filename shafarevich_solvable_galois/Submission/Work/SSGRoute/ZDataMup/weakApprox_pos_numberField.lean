import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.NK.CFTLib.HR.TransferAux.localLevelMap_injective_vanishing
import Submission.NK.CFTLib.HRdescent.localConditionCyclotomicPrime
import Submission.NK.CFTLib.exists_congruenceSubgroup_le_normImage
import Submission.NK.HassePrinciple.ideleInclusion_smul_of_restrict
import Submission.NK.NUV2.ARL.HR.locUnits_inflation_eq_zero_iff
import Submission.NK.NUV2.ArtinBridge.kummerE_le_normImage_of_isGalois_exp
import Submission.NK.NUV2.ChebAux.Transfer.cycClassOf_translation
import Submission.NK.NUV2.ChebAux.Transfer.locUnits_res_inflation_eq_zero
import Submission.NK.NUV2.LC.localNormFinite_range_iff_val_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Weak approximation of algebraic integers with positivity at the real places

For a number field `K`, a finite set `S` of finite primes, prescribed precisions `n 𝔭` and elements
`a 𝔭` of the unit balls of the completions `K_𝔭`, there is `t ∈ 𝓞 K`, `t ≠ 0`, with

* `|t - a 𝔭|_𝔭 ≤ exp (-(n 𝔭))` for every `𝔭 ∈ S`, and
* `t` positive at every real infinite place of `K`.

The proof has three ingredients, each isolated below.

* `singlePlace_approx`: an element of the ring of integers `𝔭.adicCompletionIntegers K` of the
  completion is congruent modulo `𝔭 ^ n` to the image of an algebraic integer.  This is the
  density of `𝓞 K` in `𝔭.adicCompletionIntegers K`.
* `crt_ringOfIntegers`: the Chinese remainder property for `𝓞 K`, gluing finitely many
  congruence conditions modulo `𝔭 ^ (n 𝔭)`.
* `posAdjust_ringOfIntegers`: given `b` and a nonzero `c`, one can add a large multiple of `c * c`
  without destroying positivity at the real places; all congruences are preserved because `c` may
  be taken to lie in every `𝔭 ^ (n 𝔭)` (`exists_ne_zero_mem_ideal_pow`).
-/

namespace Work.SSGRoute.ZDataMup

open IsDedekindDomain
open scoped NumberField WithZero Topology

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

variable {K : Type} [Field K] [NumberField K]

/-! ### Approximation at a single finite prime -/

/-- Every element of the unit ball of a completion is congruent modulo `𝔭 ^ n` to the image of an
algebraic integer. -/
theorem singlePlace_approx (𝔭 : HeightOneSpectrum (𝓞 K)) (n : ℕ) (a : 𝔭.adicCompletion K)
    (ha : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) a ≤ 1) :
    ∃ r : 𝓞 K,
      Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap K (𝔭.adicCompletion K) (r : K) - a)
        ≤ (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := by
  have hmem : a ∈ 𝔭.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact ha
  have hdense := Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers
    K 𝔭 ⟨a, hmem⟩
  have hball : {y : 𝔭.adicCompletion K | Valued.v (y - a) < WithZero.exp (-(n : ℤ))} ∈ 𝓝 a :=
    Commons.NumberTheory.NumberField.Completion.exp_ball_nhds 𝔭 a (-(n : ℤ))
  obtain ⟨y, hy, hyS⟩ := (mem_closure_iff_nhds.mp hdense)
    {y : 𝔭.adicCompletion K | Valued.v (y - a) < WithZero.exp (-(n : ℤ))} hball
  obtain ⟨r, rfl⟩ := hyS
  exact ⟨r, le_of_lt hy⟩

/-! ### Chinese remainder theorem for `𝓞 K` -/

/-- The Chinese remainder property for the ring of integers. -/
theorem crt_ringOfIntegers (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : HeightOneSpectrum (𝓞 K) → ℕ) (r : HeightOneSpectrum (𝓞 K) → 𝓞 K) :
    ∃ b : 𝓞 K, ∀ 𝔭 ∈ S, b - r 𝔭 ∈ 𝔭.asIdeal ^ (n 𝔭) := by
  classical
  have hcop : Pairwise (Function.onFun IsCoprime
      (fun 𝔭 : ↥S => 𝔭.1.asIdeal ^ (n 𝔭.1))) :=
    fun 𝔭 𝔮 hpq =>
      HeightOneSpectrum.isCoprime_pow_of_ne 𝔭.1 𝔮.1 (fun h => hpq (Subtype.ext h)) _ _
  obtain ⟨b, hb⟩ := Ideal.exists_forall_sub_mem_ideal hcop (fun 𝔭 : ↥S => r 𝔭.1)
  exact ⟨b, fun 𝔭 h𝔭 => hb ⟨𝔭, h𝔭⟩⟩

/-! ### A nonzero algebraic integer in all the prescribed powers -/

/-- There is a nonzero algebraic integer lying in `𝔭 ^ (n 𝔭)` for every `𝔭` in a finite set. -/
theorem exists_ne_zero_mem_ideal_pow (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : HeightOneSpectrum (𝓞 K) → ℕ) :
    ∃ C : 𝓞 K, C ≠ 0 ∧ ∀ 𝔭 ∈ S, C ∈ 𝔭.asIdeal ^ (n 𝔭) := by
  classical
  have hone : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭.asIdeal ^ (n 𝔭) ≠ ⊥ := by
    intro 𝔭
    obtain ⟨x, hxmem, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot 𝔭.ne_bot
    refine fun hbot => pow_ne_zero (n 𝔭) hxne ?_
    simpa [hbot] using Ideal.pow_mem_pow hxmem (n 𝔭)
  choose c hcmem hcne using fun 𝔭 : ↥S =>
    Submodule.exists_mem_ne_zero_of_ne_bot (hone 𝔭.1)
  refine ⟨(∏ 𝔭 : ↥S, c 𝔭), ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    exact fun 𝔭 _ => hcne 𝔭
  · intro 𝔭 h𝔭
    rw [← Finset.prod_erase_mul (s := (Finset.univ : Finset ↥S)) (f := c) (a := ⟨𝔭, h𝔭⟩)
      (Finset.mem_univ _)]
    exact (𝔭.asIdeal ^ (n 𝔭)).mul_mem_left
      (∏ q ∈ (Finset.univ : Finset ↥S).erase ⟨𝔭, h𝔭⟩, c q) (hcmem ⟨𝔭, h𝔭⟩)

/-! ### Positivity adjustment at the real places -/

/-- Given `b c : 𝓞 K` with `c ≠ 0`, some `b + k * (c * c)` is nonzero and positive at every real
infinite place. -/
theorem posAdjust_ringOfIntegers (b c : 𝓞 K) (hc : c ≠ 0) :
    ∃ t : 𝓞 K, t ≠ 0 ∧ (∃ k : ℕ, t = b + k * (c * c)) ∧
      (∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
        0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
              (algebraMap K w.Completion ((t : K)))) := by
  classical
  let φ : (w : NumberField.InfinitePlace K) → w.IsReal → K →+* ℝ := fun w hw =>
    (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom.comp
      (algebraMap K w.Completion)
  have hφc : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal), φ w hw (c : K) ≠ 0 := by
    intro w hw h
    have h2 : (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        (algebraMap K w.Completion ((c : 𝓞 K) : K)) = 0 := h
    have h1 : algebraMap K w.Completion ((c : 𝓞 K) : K) = 0 :=
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).injective
        (by rw [h2, map_zero])
    have h0 : ((c : 𝓞 K) : K) = 0 := by
      have h1' : algebraMap K w.Completion ((c : 𝓞 K) : K)
          = algebraMap K w.Completion (0 : K) := by rw [h1, map_zero]
      exact RingHom.injective (algebraMap K w.Completion) h1'
    exact hc (by simpa using h0)
  have hsqpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < φ w hw ((c : K) * (c : K)) := by
    intro w hw
    rw [map_mul]
    exact mul_self_pos.mpr (hφc w hw)
  set N : ℕ := (Finset.univ : Finset {w : NumberField.InfinitePlace K // w.IsReal}).sup
      (fun w => Nat.ceil
        (max 0 (-(φ w.1 w.2 (b : K)) / φ w.1 w.2 ((c : K) * (c : K))))) + 1 with hNdef
  have key : ∀ w : {w : NumberField.InfinitePlace K // w.IsReal},
      -(φ w.1 w.2 (b : K)) < (N : ℝ) * φ w.1 w.2 ((c : K) * (c : K)) := by
    intro w
    have hcc : 0 < φ w.1 w.2 ((c : K) * (c : K)) := hsqpos w.1 w.2
    have hsup : Nat.ceil (max 0 (-(φ w.1 w.2 (b : K))
        / φ w.1 w.2 ((c : K) * (c : K)))) ≤ N - 1 := by
      rw [hNdef]
      have hle := Finset.le_sup
        (s := (Finset.univ : Finset {w : NumberField.InfinitePlace K // w.IsReal}))
        (f := fun w : {w : NumberField.InfinitePlace K // w.IsReal} => Nat.ceil
          (max 0 (-(φ w.1 w.2 (b : K)) / φ w.1 w.2 ((c : K) * (c : K)))))
        (Finset.mem_univ w)
      omega
    have hlt : max 0 (-(φ w.1 w.2 (b : K)) / φ w.1 w.2 ((c : K) * (c : K))) < (N : ℝ) := by
      have h2 := Nat.le_ceil (max 0 (-(φ w.1 w.2 (b : K))
        / φ w.1 w.2 ((c : K) * (c : K))))
      have h3 : ((Nat.ceil (max 0 (-(φ w.1 w.2 (b : K))
          / φ w.1 w.2 ((c : K) * (c : K)))) : ℕ) : ℝ) < (N : ℝ) := by
        have h4 : 1 ≤ N := by omega
        have h5 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
          rw [Nat.cast_sub h4, Nat.cast_one]
        have h6 : ((Nat.ceil (max 0 (-(φ w.1 w.2 (b : K))
            / φ w.1 w.2 ((c : K) * (c : K)))) : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
          exact_mod_cast hsup
        linarith
      linarith
    have h7 : -(φ w.1 w.2 (b : K)) / φ w.1 w.2 ((c : K) * (c : K)) < (N : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hlt
    rwa [div_lt_iff₀ hcc] at h7
  by_cases h : b + (N : 𝓞 K) * (c * c) ≠ 0
  · refine ⟨b + (N : 𝓞 K) * (c * c), h, ⟨N, rfl⟩, ?_⟩
    intro w hw
    have hk := key ⟨w, hw⟩
    have hcc : 0 < φ w hw ((c : K) * (c : K)) := hsqpos w hw
    have hcoe : (((b + (N : 𝓞 K) * (c * c) : 𝓞 K) : K))
        = (b : K) + (N : K) * ((c : K) * (c : K)) := by
      push_cast
      ring
    have hNK : φ w hw (N : K) = (N : ℝ) := map_natCast (φ w hw) N
    change 0 < φ w hw (((b + (N : 𝓞 K) * (c * c) : 𝓞 K) : K))
    rw [hcoe, map_add, map_mul, hNK]
    linarith
  · have h0 : b + (N : 𝓞 K) * (c * c) = 0 := by
      by_contra hne
      exact h hne
    have hb : b = -((N : 𝓞 K) * (c * c)) := eq_neg_of_add_eq_zero_left h0
    have hzero : b + (((N + 1 : ℕ)) : 𝓞 K) * (c * c) = c * c := by
      rw [hb]
      push_cast
      ring
    refine ⟨b + (((N + 1 : ℕ)) : 𝓞 K) * (c * c), ?_, ⟨N + 1, rfl⟩, ?_⟩
    · rw [hzero]
      exact mul_ne_zero hc hc
    · intro w hw
      have hk := key ⟨w, hw⟩
      have hcc : 0 < φ w hw ((c : K) * (c : K)) := hsqpos w hw
      have hcoe : (((b + (((N + 1 : ℕ)) : 𝓞 K) * (c * c) : 𝓞 K) : K))
          = (b : K) + ((N + 1 : ℕ) : K) * ((c : K) * (c : K)) := by
        push_cast
        ring
      have hNK : φ w hw (((N + 1 : ℕ) : K)) = ((N + 1 : ℕ) : ℝ) :=
        map_natCast (φ w hw) (N + 1)
      have hN1 : (((N + 1 : ℕ)) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      change 0 < φ w hw (((b + (((N + 1 : ℕ)) : 𝓞 K) * (c * c) : 𝓞 K) : K))
      rw [hcoe, map_add, map_mul, hNK, hN1]
      linarith

/-! ### Weak approximation with positivity -/

theorem weakApprox_pos_numberField {K : Type} [Field K] [NumberField K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (n : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℕ)
    (hn : ∀ 𝔭 ∈ S, 0 < n 𝔭)
    (a : (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
      𝔭.adicCompletion K)
    (hint : ∀ 𝔭 ∈ S,
      Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (a 𝔭) ≤ 1) :
    ∃ t : NumberField.RingOfIntegers K, t ≠ 0 ∧
      (∀ 𝔭 ∈ S,
        Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (algebraMap K (𝔭.adicCompletion K) ((t : K)) - a 𝔭)
          ≤ (WithZero.exp (-(n 𝔭 : ℤ)) : WithZero (Multiplicative ℤ))) ∧
      (∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
        0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
              (algebraMap K w.Completion ((t : K)))) := by
  classical
  choose r hr using fun 𝔭 : ↥S =>
    singlePlace_approx (K := K) 𝔭.1 (n 𝔭.1) (a 𝔭.1) (hint 𝔭.1 𝔭.2)
  obtain ⟨b, hb⟩ := crt_ringOfIntegers (K := K) S n
    (fun 𝔭 => if h : 𝔭 ∈ S then r ⟨𝔭, h⟩ else 0)
  obtain ⟨C, hCne, hCmem⟩ := exists_ne_zero_mem_ideal_pow (K := K) S n
  obtain ⟨t, htne, htk, htpos⟩ := posAdjust_ringOfIntegers (K := K) b C hCne
  obtain ⟨k, htk'⟩ := htk
  refine ⟨t, htne, ?_, htpos⟩
  intro 𝔭 h𝔭
  have hres : b - r ⟨𝔭, h𝔭⟩ ∈ 𝔭.asIdeal ^ n 𝔭 := by
    have h0 := hb 𝔭 h𝔭
    rwa [dif_pos h𝔭] at h0
  have hC2 : C * C ∈ 𝔭.asIdeal ^ n 𝔭 :=
    (𝔭.asIdeal ^ n 𝔭).mul_mem_left C (hCmem 𝔭 h𝔭)
  have hkc : (k : 𝓞 K) * (C * C) ∈ 𝔭.asIdeal ^ n 𝔭 :=
    (𝔭.asIdeal ^ n 𝔭).mul_mem_left (k : 𝓞 K) hC2
  have htm : t - r ⟨𝔭, h𝔭⟩ ∈ 𝔭.asIdeal ^ n 𝔭 := by
    have h1 : t - r ⟨𝔭, h𝔭⟩ = (b - r ⟨𝔭, h𝔭⟩) + (k : 𝓞 K) * (C * C) := by
      rw [htk']
      ring
    rw [h1]
    exact (𝔭.asIdeal ^ n 𝔭).add_mem hres hkc
  have hvK : 𝔭.intValuation (t - r ⟨𝔭, h𝔭⟩)
      ≤ (WithZero.exp (-(n 𝔭 : ℤ)) : WithZero (Multiplicative ℤ)) :=
    (HeightOneSpectrum.intValuation_le_pow_iff_mem 𝔭 (t - r ⟨𝔭, h𝔭⟩) (n 𝔭)).mpr htm
  have hv : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap K (𝔭.adicCompletion K) (((t - r ⟨𝔭, h𝔭⟩ : 𝓞 K) : K)))
      ≤ (WithZero.exp (-(n 𝔭 : ℤ)) : WithZero (Multiplicative ℤ)) := by
    rw [Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact hvK
  have h1 : algebraMap K (𝔭.adicCompletion K) (((t - r ⟨𝔭, h𝔭⟩ : 𝓞 K) : K))
      = algebraMap K (𝔭.adicCompletion K) ((t : K))
        - algebraMap K (𝔭.adicCompletion K) (((r ⟨𝔭, h𝔭⟩ : 𝓞 K) : K)) := by
    rw [show (((t - r ⟨𝔭, h𝔭⟩ : 𝓞 K) : K))
        = (t : K) - (((r ⟨𝔭, h𝔭⟩ : 𝓞 K) : K)) by push_cast; ring]
    rw [map_sub]
  have hsplit : algebraMap K (𝔭.adicCompletion K) ((t : K)) - a 𝔭
      = algebraMap K (𝔭.adicCompletion K) (((t - r ⟨𝔭, h𝔭⟩ : 𝓞 K) : K))
        + (algebraMap K (𝔭.adicCompletion K) (((r ⟨𝔭, h𝔭⟩ : 𝓞 K) : K)) - a 𝔭) := by
    rw [h1]
    ring
  rw [hsplit]
  refine le_trans (Commons.NumberTheory.NumberField.Completion.val_add_le_max 𝔭 _ _)
    (max_le hv ?_)
  exact hr ⟨𝔭, h𝔭⟩

end

end Work.SSGRoute.ZDataMup
