import Mathlib
import Submission.NK.NUV2.RouteB.RayModulus.Defs
import Submission.NK.NUV2.RouteB.Sharp.exists_mem_fractionalIdeal_congr
import Submission.NK.CFTLib.Arl.exists_integral_sign_adjust
import Submission.Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Elements of a fractional ideal congruent to `1` modulo a modulus, and positive

Given a modulus `𝔪` and a nonzero fractional ideal `𝔡` which is coprime to `𝔪` (all
`FractionalIdeal.count` are zero on the support of `𝔪`), there is `δ ∈ 𝔡` which is `≡ 1 (𝔪)` at
all finite places of the modulus and positive at all real places in `𝔪.pos`.

The proof combines two ingredients.

* The Chinese-remainder theorem for fractional ideals
  (`NK.NUV2.RouteB.Sharp.exists_mem_fractionalIdeal_congr`) produces an element `γ ∈ 𝔡`
  congruent to `1` modulo `𝔪`.
* `NK.CFTLib.Arl.exists_integral_sign_adjust` produces, for the *integer*
  `m = Ideal.absNorm 𝔪.ideal` (which lies in the ideal `𝔪.ideal`), an algebraic integer `u` such
  that `1 + m·u` has a prescribed sign at every real place.  Then `δ := γ·(1 + m·u)` lies in `𝔡`
  (as `1 + m·u ∈ 𝓞 K`), is congruent to `1` modulo `𝔪` (because `m ∈ 𝔪.ideal`), and is positive at
  every real place in `𝔪.pos` (the sign of `1 + m·u` being chosen to match that of `γ`).
-/

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

namespace NK.NUV2.RouteB.RayModulus

variable {K : Type} [Field K] [NumberField K]

/-- Membership in the support of a modulus, in terms of the exponent function. -/
lemma modulus_mem_supportFinset_iff (𝔪 : NK.NUV2.RouteB.Modulus K)
    {q : HeightOneSpectrum (𝓞 K)} : q ∈ 𝔪.supportFinset ↔ 𝔪.exps q ≠ 0 := by
  rw [NK.NUV2.RouteB.Modulus.supportFinset, Set.Finite.mem_toFinset]
  rfl

/-- An algebraic integer has valuation at most `1` at every finite place. -/
lemma val_algebraMap_le_one_of_ringOfIntegers (q : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    Valued.v (algebraMap K (q.adicCompletion K) (a : K)) ≤ 1 := by
  rw [Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one q a

/-- At a real infinite place, the real identification of the completion agrees with the first
coordinate of the mixed embedding. -/
lemma ringEquivReal_algebraMap_eq_of_isReal (w : InfinitePlace K) (hw : w.IsReal) (y : K) :
    (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (algebraMap K w.Completion y)
      = (NumberField.mixedEmbedding K y).1 ⟨w, hw⟩ := by
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
  simp [NumberField.mixedEmbedding.mixedEmbedding_apply_isReal]

/-- There is a nonzero element `γ ∈ 𝔡` congruent to `1` modulo `𝔪` (at the finite places
of `𝔪`), which is moreover integral at those places.  When the support of `𝔪` is empty any
nonzero element of `𝔡` will do. -/
lemma exists_ne_zero_mem_fractionalIdeal_cong_one (𝔪 : NK.NUV2.RouteB.Modulus K)
    (𝔡 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) (h𝔡 : 𝔡 ≠ 0)
    (hcop : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      𝔪.exps q ≠ 0 → FractionalIdeal.count K q 𝔡 = 0) :
    ∃ γ : K, γ ∈ (𝔡 : Set K) ∧ γ ≠ 0 ∧
      (∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 →
        Valued.v (algebraMap K (q.adicCompletion K) (γ - 1))
          ≤ WithZero.exp (-(𝔪.exps q : ℤ))) ∧
      (∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 →
        Valued.v (algebraMap K (q.adicCompletion K) γ) ≤ 1) := by
  classical
  by_cases hsupp : 𝔪.supportFinset = ∅
  · -- the modulus is trivial: any nonzero element of `𝔡` works
    have hzero : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q = 0 := by
      intro q
      by_contra hq
      have hmem : q ∈ 𝔪.supportFinset := 𝔪.mem_supportFinset hq
      rw [hsupp] at hmem
      exact Finset.notMem_empty q hmem
    obtain ⟨γ, hγmem, hγne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (FractionalIdeal.coeToSubmodule_ne_bot.mpr h𝔡)
    exact ⟨γ, hγmem, hγne, fun q hq => absurd (hzero q) hq, fun q hq => absurd (hzero q) hq⟩
  · obtain ⟨q₀, hq₀⟩ := Finset.nonempty_iff_ne_empty.mpr hsupp
    have hq₀' : 𝔪.exps q₀ ≠ 0 := (modulus_mem_supportFinset_iff 𝔪).mp hq₀
    obtain ⟨γ, hγmem, hγcong⟩ :=
      NK.NUV2.RouteB.Sharp.exists_mem_fractionalIdeal_congr K 𝔪.exps 𝔪.finite_support 𝔡 h𝔡 hcop 1
    have hγcong' : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 →
        Valued.v (algebraMap K (q.adicCompletion K) (γ - 1))
          ≤ WithZero.exp (-(𝔪.exps q : ℤ)) := by
      intro q hq
      have h := hγcong q hq
      simpa using h
    have hγne : γ ≠ 0 := by
      intro h0
      have h1 := hγcong' q₀ hq₀'
      have h2 : Valued.v (algebraMap K (q₀.adicCompletion K) (γ - 1)) = 1 := by
        rw [h0, zero_sub]; simp
      rw [h2] at h1
      have h3 : WithZero.exp (-(𝔪.exps q₀ : ℤ)) < 1 := by
        rw [← WithZero.exp_zero]
        refine WithZero.exp_lt_exp.mpr ?_
        have : 1 ≤ 𝔪.exps q₀ := Nat.one_le_iff_ne_zero.mpr hq₀'
        omega
      exact absurd h1 (not_le.mpr h3)
    refine ⟨γ, hγmem, hγne, hγcong', ?_⟩
    intro q hq
    have hsplit : algebraMap K (q.adicCompletion K) γ
        = algebraMap K (q.adicCompletion K) (γ - 1) + 1 := by
      rw [map_sub, map_one]; ring
    rw [hsplit]
    refine le_trans (Valuation.map_add _ _ _) (max_le (le_trans (hγcong' q hq) ?_)
      (le_of_eq (Valuation.map_one _)))
    rw [← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by
      have : 1 ≤ 𝔪.exps q := Nat.one_le_iff_ne_zero.mpr hq
      omega)

theorem exists_mem_fractionalIdeal_cong_pos (K : Type) [Field K] [NumberField K]
    (𝔪 : NK.NUV2.RouteB.Modulus K)
    (𝔡 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) (h𝔡 : 𝔡 ≠ 0)
    (hcop : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      𝔪.exps q ≠ 0 → FractionalIdeal.count K q 𝔡 = 0) :
    ∃ δ : K, δ ∈ (𝔡 : Set K) ∧ δ ≠ 0 ∧
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), 𝔪.exps q ≠ 0 →
        Valued.v (algebraMap K (q.adicCompletion K) (δ - 1))
          ≤ WithZero.exp (-(𝔪.exps q : ℤ))) ∧
      (∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal), w ∈ 𝔪.pos →
        0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
          (algebraMap K w.Completion δ)) := by
  classical
  obtain ⟨γ, hγmem, hγne, hγcong, hγint⟩ :=
    exists_ne_zero_mem_fractionalIdeal_cong_one 𝔪 𝔡 h𝔡 hcop
  by_cases hreal : ∃ w : InfinitePlace K, w.IsReal
  · -- there is a real place: adjust the archimedean signs
    obtain ⟨w₀, hw₀⟩ := hreal
    have hmpos : 0 < Ideal.absNorm 𝔪.ideal :=
      Nat.pos_iff_ne_zero.mpr
        (Ideal.absNorm_ne_zero_of_nonZeroDivisors
          (⟨𝔪.ideal, mem_nonZeroDivisors_iff_ne_zero.mpr 𝔪.ideal_ne_zero⟩ : (Ideal (𝓞 K))⁰))
    -- the integer `m = N(𝔪.ideal)` lies in `𝔪.ideal`
    have hmloc : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 →
        Valued.v (algebraMap K (q.adicCompletion K) (Ideal.absNorm 𝔪.ideal : K))
          ≤ WithZero.exp (-(𝔪.exps q : ℤ)) := by
      intro q hq
      have hmem : (Ideal.absNorm 𝔪.ideal : 𝓞 K) ∈ q.asIdeal ^ (𝔪.exps q) := by
        refine NK.NUV2.RouteB.Sharp.finset_prod_le_pow_of_mem 𝔪.exps 𝔪.supportFinset
          (𝔪.mem_supportFinset hq) ?_
        rw [← NK.NUV2.RouteB.Modulus.ideal]
        exact Ideal.absNorm_mem 𝔪.ideal
      rw [show (Ideal.absNorm 𝔪.ideal : K)
            = algebraMap (𝓞 K) K (Ideal.absNorm 𝔪.ideal : 𝓞 K) by simp,
        Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq,
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem q _ (𝔪.exps q)).mpr hmem
    -- the sign to be imposed on `1 + m·u` at each real place
    set r : InfinitePlace K → ℝ := (fun w =>
      if h : w.IsReal then (if (mixedEmbedding K γ).1 ⟨w, h⟩ < 0 then (-1 : ℝ) else 1) else 1)
      with hrdef
    have hrw : ∀ (w : InfinitePlace K) (hw : w.IsReal),
        r w = if (mixedEmbedding K γ).1 ⟨w, hw⟩ < 0 then (-1 : ℝ) else 1 := by
      intro w hw
      rw [hrdef]
      exact dif_pos hw
    have hr : ∀ w : InfinitePlace K, w.IsReal → r w ≠ 0 := by
      intro w hw
      rw [hrw w hw]
      split_ifs <;> norm_num
    obtain ⟨u, hu⟩ :=
      NK.CFTLib.Arl.exists_integral_sign_adjust K (Ideal.absNorm 𝔪.ideal) hmpos r hr
    set a : 𝓞 K := 1 + (Ideal.absNorm 𝔪.ideal) • u with hadef
    have haK : (a : K) = 1 + (Ideal.absNorm 𝔪.ideal : K) * (u : K) := by
      rw [hadef]; push_cast; ring
    -- `γ·a` is positive at every real place
    have hpos_all : ∀ (w : InfinitePlace K) (hw : w.IsReal),
        0 < (mixedEmbedding K (γ * (a : K))).1 ⟨w, hw⟩ := by
      intro w hw
      have hφγne : (mixedEmbedding K γ).1 ⟨w, hw⟩ ≠ 0 := by
        have h1 : (mixedEmbedding K γ).1 ⟨w, hw⟩ = (InfinitePlace.embedding_of_isReal hw) γ := by
          rw [NumberField.mixedEmbedding.mixedEmbedding_apply_isReal]
        rw [h1]
        intro h
        exact hγne (RingHom.injective (InfinitePlace.embedding_of_isReal hw) (by simpa using h))
      have hγsgn : 0 < r w * (mixedEmbedding K γ).1 ⟨w, hw⟩ := by
        rw [hrw w hw]
        split_ifs with hlt
        · rw [neg_one_mul]; exact neg_pos.mpr hlt
        · rw [one_mul]; simp only [not_lt] at hlt
          exact lt_of_le_of_ne hlt (Ne.symm hφγne)
      have hasgn : 0 < r w * (mixedEmbedding K (a : K)).1 ⟨w, hw⟩ := by
        have h := hu w hw
        rw [ringEquivReal_algebraMap_eq_of_isReal, ← haK] at h
        exact h
      have hrsq : r w * r w = 1 := by
        rw [hrw w hw]; split_ifs <;> norm_num
      have hkey : (mixedEmbedding K (γ * (a : K))).1 ⟨w, hw⟩
          = (r w * (mixedEmbedding K γ).1 ⟨w, hw⟩)
            * (r w * (mixedEmbedding K (a : K)).1 ⟨w, hw⟩) := by
        rw [map_mul, Prod.fst_mul, mul_mul_mul_comm, hrsq, one_mul]
        rfl
      rw [hkey]
      exact mul_pos hγsgn hasgn
    refine ⟨γ * (a : K), ?_, ?_, ?_, ?_⟩
    · -- membership in `𝔡`
      have hsm := Submodule.smul_mem 𝔡.1 a hγmem
      have hEq : a • γ = γ * (a : K) := by
        rw [Algebra.smul_def, RingOfIntegers.coe_eq_algebraMap, mul_comm]
      rwa [hEq] at hsm
    · -- nonvanishing
      intro hzero
      have h := hpos_all w₀ hw₀
      rw [hzero] at h
      simp at h
    · -- the congruence modulo `𝔪`
      intro q hq
      have h1 : γ * (a : K) - 1
          = (γ - 1) + γ * ((Ideal.absNorm 𝔪.ideal : K) * (u : K)) := by
        rw [haK]; ring
      have hsplit : algebraMap K (q.adicCompletion K) (γ * (a : K) - 1)
          = algebraMap K (q.adicCompletion K) (γ - 1)
            + algebraMap K (q.adicCompletion K) γ
              * algebraMap K (q.adicCompletion K) ((Ideal.absNorm 𝔪.ideal : K) * (u : K)) := by
        calc algebraMap K (q.adicCompletion K) (γ * (a : K) - 1)
            = algebraMap K (q.adicCompletion K)
                ((γ - 1) + γ * ((Ideal.absNorm 𝔪.ideal : K) * (u : K))) := by rw [h1]
          _ = algebraMap K (q.adicCompletion K) (γ - 1)
                + algebraMap K (q.adicCompletion K)
                  (γ * ((Ideal.absNorm 𝔪.ideal : K) * (u : K))) := map_add _ _ _
          _ = algebraMap K (q.adicCompletion K) (γ - 1)
                + algebraMap K (q.adicCompletion K) γ
                  * algebraMap K (q.adicCompletion K)
                    ((Ideal.absNorm 𝔪.ideal : K) * (u : K)) := by rw [map_mul]
      rw [hsplit]
      refine le_trans (Valuation.map_add _ _ _) (max_le (hγcong q hq) ?_)
      simp only [map_mul]
      refine le_trans (mul_le_mul' (hγint q hq)
        (mul_le_mul' (hmloc q hq) (val_algebraMap_le_one_of_ringOfIntegers q u))) ?_
      rw [one_mul, mul_one]
    · -- positivity at the real places in `𝔪.pos`
      intro w hw _
      rw [ringEquivReal_algebraMap_eq_of_isReal]
      exact hpos_all w hw
  · -- no real place: the positivity condition is vacuous
    exact ⟨γ, hγmem, hγne, hγcong, fun w hw _ => absurd ⟨w, hw⟩ hreal⟩

end NK.NUV2.RouteB.RayModulus
