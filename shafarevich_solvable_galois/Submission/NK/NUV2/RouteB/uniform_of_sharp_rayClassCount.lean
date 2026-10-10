import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Submission.NK.NUV2.RouteB.Unif.card_supported_le
import Submission.NK.NUV2.RouteB.Unif.primeFactorsFinset
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Classical BigOperators

namespace NK.NUV2.RouteB

variable {K : Type*} [Field K] [NumberField K]

/-- **The Euler-factor decomposition of the ray-class count.**  For `S ⊆ S'`, the ideals of
`𝓞 K` which are coprime to `S`, of norm `≤ N` and in the ray class `c` are exactly the products
`𝔟 · 𝔞` with `𝔟` supported on `S'∖S`, `𝔞` coprime to `S'`, `classOfIdeal 𝔞 = (classOfIdeal 𝔟)⁻¹·c`
and `N𝔟 · N𝔞 ≤ N`. -/
theorem rayCnt_eq_sum_fibers (U : Subgroup (NK.GlobalCFT.Idele K))
    {S S' : Finset (NK.HeckeL.PrimeIdeal K)} (hsub : S ⊆ S')
    (c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U) (N : ℕ) :
    rayCnt U S c N = ∑ 𝔟 ∈ extraSupports S' S N,
      rayCnt U S' ((NK.HeckeL.classOfIdeal K U 𝔟)⁻¹ * c) (N / Ideal.absNorm 𝔟) := by
  classical
  rw [rayCnt, Finset.card_eq_sum_card_fiberwise (t := extraSupports S' S N)
    (f := fun 𝔞 : Ideal (𝓞 K) => partAt (S' \ S) 𝔞) ?_]
  · refine Finset.sum_congr rfl fun 𝔟 h𝔟 => ?_
    rw [rayCnt]
    refine Finset.card_nbij' (fun 𝔞 => partAway S' 𝔞) (fun 𝔞' => 𝔟 * 𝔞')
      (s := (rayFinset U S c N).filter (fun 𝔞 => partAt (S' \ S) 𝔞 = 𝔟))
      (t := rayFinset U S' ((NK.HeckeL.classOfIdeal K U 𝔟)⁻¹ * c) (N / Ideal.absNorm 𝔟))
      ?_ ?_ ?_ ?_
    · intro 𝔞 h𝔞
      rw [Finset.mem_coe] at h𝔞
      obtain ⟨h𝔞s, h𝔞f⟩ := Finset.mem_filter.mp h𝔞
      obtain ⟨h𝔞ne, h𝔞cop, h𝔞cl, h𝔞N⟩ := (mem_rayFinset U S c N 𝔞).mp h𝔞s
      obtain ⟨h𝔟ne, -, -⟩ := (mem_extraSupports S' S N 𝔟).mp h𝔟
      rw [Finset.mem_coe]
      refine (mem_rayFinset U S' ((NK.HeckeL.classOfIdeal K U 𝔟)⁻¹ * c) (N / Ideal.absNorm 𝔟)
        (partAway S' 𝔞)).mpr
        ⟨partAway_ne_zero S' 𝔞, fun 𝔭 h𝔭 => partAway_coprime S' 𝔞 h𝔭, ?_, ?_⟩
      · have hsplit := partAt_mul_partAway hsub h𝔞ne h𝔞cop
        have hmul : NK.HeckeL.classOfIdeal K U (partAt (S' \ S) 𝔞) *
            NK.HeckeL.classOfIdeal K U (partAway S' 𝔞) = c := by
          rw [← NK.HeckeL.Basic.classOfIdeal_mul U _ _
            (partAt_ne_zero _ _) (partAway_ne_zero _ _), hsplit, h𝔞cl]
        rw [h𝔞f] at hmul
        exact eq_inv_mul_of_mul_eq hmul
      · have h2 : Ideal.absNorm (partAt (S' \ S) 𝔞) * Ideal.absNorm (partAway S' 𝔞)
            = Ideal.absNorm 𝔞 := by
          rw [← map_mul, partAt_mul_partAway hsub h𝔞ne h𝔞cop]
        rw [h𝔞f] at h2
        have hmul : Ideal.absNorm (partAway S' 𝔞) * Ideal.absNorm 𝔟 ≤ N := by
          rw [mul_comm, h2]; exact h𝔞N
        exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero fun h0 =>
          h𝔟ne (Ideal.absNorm_eq_zero_iff.mp h0))).mpr hmul
    · intro 𝔞' h𝔞'
      rw [Finset.mem_coe] at h𝔞'
      obtain ⟨hane, hacop, hacl, haN⟩ := (mem_rayFinset U S'
        ((NK.HeckeL.classOfIdeal K U 𝔟)⁻¹ * c) (N / Ideal.absNorm 𝔟) 𝔞').mp h𝔞'
      obtain ⟨h𝔟ne, h𝔟supp, -⟩ := (mem_extraSupports S' S N 𝔟).mp h𝔟
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨(mem_rayFinset U S c N (𝔟 * 𝔞')).mpr
        ⟨mul_ne_zero h𝔟ne hane, ?_, ?_, ?_⟩, ?_⟩
      · intro 𝔭 h𝔭
        exact not_dvd_mul h𝔟ne hane
          (fun h => (Finset.mem_sdiff.mp (h𝔟supp 𝔭 h)).2 h𝔭)
          (fun h => hacop 𝔭 (hsub h𝔭) h)
      · rw [NK.HeckeL.Basic.classOfIdeal_mul U _ _ h𝔟ne hane, hacl, mul_inv_cancel_left]
      · rw [map_mul]
        refine le_trans (Nat.mul_le_mul_left _ haN) ?_
        rw [mul_comm]
        exact Nat.div_mul_le_self N (Ideal.absNorm 𝔟)
      · exact partAt_mul_eq h𝔟ne h𝔟supp hane hacop
    · intro 𝔞 h𝔞
      rw [Finset.mem_coe] at h𝔞
      obtain ⟨h𝔞s, h𝔞f⟩ := Finset.mem_filter.mp h𝔞
      obtain ⟨h𝔞ne, h𝔞cop, -, -⟩ := (mem_rayFinset U S c N 𝔞).mp h𝔞s
      rw [← h𝔞f]
      exact partAt_mul_partAway hsub h𝔞ne h𝔞cop
    · intro 𝔞' h𝔞'
      rw [Finset.mem_coe] at h𝔞'
      obtain ⟨hane, hacop, -, -⟩ := (mem_rayFinset U S'
        ((NK.HeckeL.classOfIdeal K U 𝔟)⁻¹ * c) (N / Ideal.absNorm 𝔟) 𝔞').mp h𝔞'
      obtain ⟨h𝔟ne, h𝔟supp, -⟩ := (mem_extraSupports S' S N 𝔟).mp h𝔟
      exact partAway_mul_eq h𝔟ne h𝔟supp hane hacop
  · intro 𝔞 h𝔞
    rw [Finset.mem_coe] at h𝔞 ⊢
    obtain ⟨h𝔞ne, h𝔞cop, -, h𝔞N⟩ := (mem_rayFinset U S c N 𝔞).mp h𝔞
    refine (mem_extraSupports S' S N (partAt (S' \ S) 𝔞)).mpr
      ⟨partAt_ne_zero _ _, fun 𝔭 h𝔭 => partAt_supported _ _ h𝔭, ?_⟩
    have h2 : Ideal.absNorm (partAt (S' \ S) 𝔞) * Ideal.absNorm (partAway S' 𝔞)
        = Ideal.absNorm 𝔞 := by
      rw [← map_mul, partAt_mul_partAway hsub h𝔞ne h𝔞cop]
    refine le_trans ?_ h𝔞N
    rw [← h2]
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero fun h0 =>
      partAway_ne_zero S' 𝔞 (Ideal.absNorm_eq_zero_iff.mp h0))

/-- **The uniform power-saving bound, given the sharp bound for `S' ⊇ S` and the count of the
ideals supported on `S'∖S`.**  The sum over the extra factors costs a factor `N^ε` (any `ε > 0`),
which is absorbed by lowering the exponent. -/
theorem uniform_of_sharp_aux (U : Subgroup (NK.GlobalCFT.Idele K))
    (S S' : Finset (NK.HeckeL.PrimeIdeal K)) (hsub : S ⊆ S')
    (hsharp' : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      ∀ c₁ c₂ : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
        |((Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S', ¬ 𝔭.asIdeal ∣ 𝔞) ∧
              NK.HeckeL.classOfIdeal K U 𝔞 = c₁ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ X} : ℝ)
          - (Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S', ¬ 𝔭.asIdeal ∣ 𝔞) ∧
              NK.HeckeL.classOfIdeal K U 𝔞 = c₂ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ X} : ℝ))|
        ≤ C * X ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)))
    (hcard : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      (Nat.card {𝔟 : Ideal (𝓞 K) // 𝔟 ≠ 0 ∧
          (∀ 𝔭 : NK.HeckeL.PrimeIdeal K, 𝔭.asIdeal ∣ 𝔟 → 𝔭 ∈ S' \ S) ∧
          Ideal.absNorm 𝔟 ≤ N} : ℝ) ≤ C * (N : ℝ) ^ ε) :
    ∃ (C θ : ℝ), 0 < C ∧ θ < 1 ∧ ∀ X : ℝ, 1 ≤ X →
      ∀ c₁ c₂ : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
        |((Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧
              NK.HeckeL.classOfIdeal K U 𝔞 = c₁ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ X} : ℝ)
          - (Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧
              NK.HeckeL.classOfIdeal K U 𝔞 = c₂ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ X} : ℝ))|
        ≤ C * X ^ θ := by
  classical
  obtain ⟨C', hC'pos, hC'sharp⟩ := hsharp'
  have hmR : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  have hf1 : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Module.finrank_pos (R := ℚ) (M := K)).ne'
  set ε : ℝ := 1 / (2 * (Module.finrank ℚ K : ℝ)) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  obtain ⟨C₀, hC₀pos, hC₀le⟩ := hcard (1 / (2 * (Module.finrank ℚ K : ℝ))) (by positivity)
  rw [← hεdef] at hC₀le
  set θ₀ : ℝ := 1 - 1 / (Module.finrank ℚ K : ℝ) with hθ₀def
  have hθ₀nonneg : 0 ≤ θ₀ := by
    rw [hθ₀def]
    have h1 : 1 / (Module.finrank ℚ K : ℝ) ≤ 1 := by
      rw [div_le_one hmR]
      exact hf1
    linarith
  set θ : ℝ := 1 - 1 / (2 * (Module.finrank ℚ K : ℝ)) with hθdef
  have hθlt : θ < 1 := by rw [hθdef]; linarith [hεpos, hεdef]
  have hθnonneg : 0 ≤ θ := by
    rw [hθdef]
    have h1 : 1 / (2 * (Module.finrank ℚ K : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [hmR]
    linarith
  refine ⟨C' * C₀, θ, by positivity, hθlt, ?_⟩
  intro X hX c₁ c₂
  have hX0 : 0 ≤ X := le_trans zero_le_one hX
  set N : ℕ := ⌊X⌋₊ with hNdef
  have hN1 : 1 ≤ N := by
    rw [hNdef]
    exact Nat.le_floor (by simpa using hX)
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
  rw [← rayCnt_eq_natCard_le U S c₁ X hX0, ← rayCnt_eq_natCard_le U S c₂ X hX0, ← hNdef]
  rw [rayCnt_eq_sum_fibers U hsub c₁ N, rayCnt_eq_sum_fibers U hsub c₂ N]
  rw [Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ 𝔟 ∈ extraSupports S' S N,
      |(((rayCnt U S' ((NK.HeckeL.classOfIdeal K U 𝔟)⁻¹ * c₁)
              (N / Ideal.absNorm 𝔟) : ℕ) : ℝ)
          - ((rayCnt U S' ((NK.HeckeL.classOfIdeal K U 𝔟)⁻¹ * c₂)
              (N / Ideal.absNorm 𝔟) : ℕ) : ℝ))|
        ≤ C' * (((N / Ideal.absNorm 𝔟 : ℕ) : ℝ) ^ θ₀) := by
    intro 𝔟 h𝔟
    obtain ⟨h𝔟ne, -, h𝔟N⟩ := (mem_extraSupports S' S N 𝔟).mp h𝔟
    have hpos : 0 < Ideal.absNorm 𝔟 := Nat.pos_of_ne_zero fun h0 =>
      h𝔟ne (Ideal.absNorm_eq_zero_iff.mp h0)
    have hone : 1 ≤ N / Ideal.absNorm 𝔟 := (Nat.one_le_div_iff hpos).mpr h𝔟N
    have hX1 : (1 : ℝ) ≤ ((N / Ideal.absNorm 𝔟 : ℕ) : ℝ) := by exact_mod_cast hone
    have hb := hC'sharp ((N / Ideal.absNorm 𝔟 : ℕ) : ℝ) hX1
      ((NK.HeckeL.classOfIdeal K U 𝔟)⁻¹ * c₁) ((NK.HeckeL.classOfIdeal K U 𝔟)⁻¹ * c₂)
    rw [← rayCnt_eq_natCard_real, ← rayCnt_eq_natCard_real] at hb
    exact hb
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hden : ∀ 𝔟 : Ideal (𝓞 K), 𝔟 ∈ extraSupports S' S N →
      (0 : ℝ) < (Ideal.absNorm 𝔟 : ℝ) := by
    intro 𝔟 h𝔟
    obtain ⟨h𝔟ne, -, -⟩ := (mem_extraSupports S' S N 𝔟).mp h𝔟
    exact_mod_cast Nat.pos_of_ne_zero fun h0 => h𝔟ne (Ideal.absNorm_eq_zero_iff.mp h0)
  have hsumle : ∑ 𝔟 ∈ extraSupports S' S N, (((N / Ideal.absNorm 𝔟 : ℕ) : ℝ) ^ θ₀)
      ≤ C₀ * (N : ℝ) ^ θ := by
    have step1 : ∑ 𝔟 ∈ extraSupports S' S N, (((N / Ideal.absNorm 𝔟 : ℕ) : ℝ) ^ θ₀)
        ≤ ∑ 𝔟 ∈ extraSupports S' S N, ((N : ℝ) / (Ideal.absNorm 𝔟 : ℝ)) ^ θ₀ :=
      Finset.sum_le_sum fun 𝔟 _ => Real.rpow_le_rpow (by positivity) Nat.cast_div_le hθ₀nonneg
    have step2 : ∑ 𝔟 ∈ extraSupports S' S N, ((N : ℝ) / (Ideal.absNorm 𝔟 : ℝ)) ^ θ₀
        = ∑ 𝔟 ∈ extraSupports S' S N, (N : ℝ) ^ θ₀ * ((Ideal.absNorm 𝔟 : ℝ) ^ θ₀)⁻¹ :=
      Finset.sum_congr rfl fun 𝔟 h𝔟 => by
        rw [Real.div_rpow (by positivity) (hden 𝔟 h𝔟).le, div_eq_mul_inv]
    have step3 : ∑ 𝔟 ∈ extraSupports S' S N,
          (N : ℝ) ^ θ₀ * ((Ideal.absNorm 𝔟 : ℝ) ^ θ₀)⁻¹
        ≤ ∑ 𝔟 ∈ extraSupports S' S N, (N : ℝ) ^ θ₀ := by
      refine Finset.sum_le_sum fun 𝔟 h𝔟 => ?_
      have h1 : (1 : ℝ) ≤ (Ideal.absNorm 𝔟 : ℝ) := by
        obtain ⟨h𝔟ne, -, -⟩ := (mem_extraSupports S' S N 𝔟).mp h𝔟
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr fun h0 =>
          h𝔟ne (Ideal.absNorm_eq_zero_iff.mp h0)
      exact mul_le_of_le_one_right (Real.rpow_nonneg (by positivity) _)
        (inv_le_one_of_one_le₀ (Real.one_le_rpow h1 hθ₀nonneg))
    have step4 : ∑ 𝔟 ∈ extraSupports S' S N, (N : ℝ) ^ θ₀
        = ((extraSupports S' S N).card : ℝ) * (N : ℝ) ^ θ₀ := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have heq : (extraSupports S' S N).card = Nat.card {𝔟 : Ideal (𝓞 K) //
        𝔟 ≠ 0 ∧ (∀ 𝔭 : NK.HeckeL.PrimeIdeal K, 𝔭.asIdeal ∣ 𝔟 → 𝔭 ∈ S' \ S) ∧
        Ideal.absNorm 𝔟 ≤ N} := by
      rw [extraSupports]
      exact (natCard_subtype_eq_filter_card
        (s := (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) N).toFinset)
        (P := fun 𝔟 => 𝔟 ≠ 0 ∧
          (∀ 𝔭 : NK.HeckeL.PrimeIdeal K, 𝔭.asIdeal ∣ 𝔟 → 𝔭 ∈ S' \ S) ∧
          Ideal.absNorm 𝔟 ≤ N)
        (fun x hx => by rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]; exact hx.2.2)).symm
    have hcardN : (((extraSupports S' S N).card : ℕ) : ℝ) ≤ C₀ * (N : ℝ) ^ ε := by
      rw [heq]
      exact hC₀le N
    have step5 : ((extraSupports S' S N).card : ℝ) * (N : ℝ) ^ θ₀
        ≤ (C₀ * (N : ℝ) ^ ε) * (N : ℝ) ^ θ₀ :=
      mul_le_mul_of_nonneg_right hcardN (Real.rpow_nonneg (by positivity) _)
    have hexp : ε + θ₀ = θ := by
      rw [hεdef, hθ₀def, hθdef]
      have h1f : 1 / (Module.finrank ℚ K : ℝ)
          = 2 * (1 / (2 * (Module.finrank ℚ K : ℝ))) := by
        field_simp
        try ring
      rw [h1f]
      ring
    have step6 : (C₀ * (N : ℝ) ^ ε) * (N : ℝ) ^ θ₀ = C₀ * (N : ℝ) ^ θ := by
      rw [mul_assoc, ← Real.rpow_add hNpos ε θ₀, hexp]
    calc ∑ 𝔟 ∈ extraSupports S' S N, (((N / Ideal.absNorm 𝔟 : ℕ) : ℝ) ^ θ₀)
        ≤ ∑ 𝔟 ∈ extraSupports S' S N, ((N : ℝ) / (Ideal.absNorm 𝔟 : ℝ)) ^ θ₀ := step1
      _ = ∑ 𝔟 ∈ extraSupports S' S N, (N : ℝ) ^ θ₀ * ((Ideal.absNorm 𝔟 : ℝ) ^ θ₀)⁻¹ := step2
      _ ≤ ∑ 𝔟 ∈ extraSupports S' S N, (N : ℝ) ^ θ₀ := step3
      _ = ((extraSupports S' S N).card : ℝ) * (N : ℝ) ^ θ₀ := step4
      _ ≤ (C₀ * (N : ℝ) ^ ε) * (N : ℝ) ^ θ₀ := step5
      _ = C₀ * (N : ℝ) ^ θ := step6
  calc C' * (∑ 𝔟 ∈ extraSupports S' S N, (((N / Ideal.absNorm 𝔟 : ℕ) : ℝ) ^ θ₀))
      ≤ C' * (C₀ * (N : ℝ) ^ θ) := mul_le_mul_of_nonneg_left hsumle hC'pos.le
    _ = (C' * C₀) * (N : ℝ) ^ θ := by ring
    _ ≤ (C' * C₀) * X ^ θ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Real.rpow_le_rpow (by positivity) (by rw [hNdef]; exact Nat.floor_le hX0) hθnonneg

theorem uniform_of_sharp_rayClassCount
    (K : Type) [Field K] [NumberField K]
    (U : Subgroup (NK.GlobalCFT.Idele K)) (hU : IsOpen (U : Set (NK.GlobalCFT.Idele K)))
    (hfin : Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U))
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (h𝔪 : 𝔪 ≠ 0)
    (hsharp : ∀ S : Finset (NK.HeckeL.PrimeIdeal K),
      (∀ 𝔭 : NK.HeckeL.PrimeIdeal K, 𝔭.asIdeal ∣ 𝔪 → 𝔭 ∈ S) →
      ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
        ∀ c₁ c₂ : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
          |((Nat.card {𝔞 : Ideal (NumberField.RingOfIntegers K) //
                𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧
                NK.HeckeL.classOfIdeal K U 𝔞 = c₁ ∧ Ideal.absNorm 𝔞 ≤ X} : ℝ)
          - (Nat.card {𝔞 : Ideal (NumberField.RingOfIntegers K) //
                𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧
                NK.HeckeL.classOfIdeal K U 𝔞 = c₂ ∧ Ideal.absNorm 𝔞 ≤ X} : ℝ))|
        ≤ C * X ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)))
    (S : Finset (NK.HeckeL.PrimeIdeal K)) :
    ∃ (C θ : ℝ), 0 < C ∧ θ < 1 ∧ ∀ X : ℝ, 1 ≤ X →
      ∀ c₁ c₂ : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
        |((Nat.card {𝔞 : Ideal (NumberField.RingOfIntegers K) //
              𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧
              NK.HeckeL.classOfIdeal K U 𝔞 = c₁ ∧ Ideal.absNorm 𝔞 ≤ X} : ℝ)
        - (Nat.card {𝔞 : Ideal (NumberField.RingOfIntegers K) //
              𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧
              NK.HeckeL.classOfIdeal K U 𝔞 = c₂ ∧ Ideal.absNorm 𝔞 ≤ X} : ℝ))|
      ≤ C * X ^ θ := by
  classical
  -- enlarge `S` by the primes dividing `𝔪`, for which the sharp bound is available
  obtain ⟨T, hT⟩ := Unif.primeFactorsFinset K 𝔪 h𝔪
  set S' : Finset (NK.HeckeL.PrimeIdeal K) := S ∪ T with hS'def
  refine uniform_of_sharp_aux U S S' Finset.subset_union_left ?_ ?_
  · exact hsharp S' fun 𝔭 hp => Finset.mem_union_right S ((hT 𝔭).mpr hp)
  · intro ε hε
    exact Unif.card_supported_le K (S' \ S) ε hε

end NK.NUV2.RouteB
