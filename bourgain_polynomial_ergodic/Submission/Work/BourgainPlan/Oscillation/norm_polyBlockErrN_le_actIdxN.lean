import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Maximal.norm_polyBlockErr_le_actIdx

namespace Work.BourgainPlan.Oscillation

open Finset MeasureTheory
open scoped BigOperators ENNReal
open Work.BourgainPlan.Maximal
open Commons.Analysis.ExponentialSums

noncomputable section

/-!
# The profile-replacement error of the `m`-th block at an arbitrary scale

This file is the *arbitrary-scale* (non-dyadic) counterpart of
`Work.BourgainPlan.Maximal.norm_polyBlockErr_le_actIdx`: Bourgain's oscillation inequality runs
along the lacunary scales `⌊ρ^i⌋`, which are not powers of two, so the identification of the
profile-replacement error of the `m`-th denominator block with the sum of the *active* profile
errors has to be redone at an arbitrary scale `N`.

The dyadic proof (`polyBlockErr_eq_sum`, `norm_polyModelTermArc_sub_sharp_le`, ...) is replayed
verbatim with `2^k` replaced by `N`, `polyDil P k` by `polyDilN P N`, `polyArcRad P k` by
`polyArcRadN P N` and `polyErrVal P · k` by `polyErrValN P · N`.  The only genuinely new
arithmetic input is the *cutoff* `2^{4m+4} ≤ N` (the arbitrary-scale form of `4m+4 ≤ k`), which
makes the `q`-filter of the model block equal to `Ico (2^m) (2^{m+1})`, and the scale threshold
`K ≤ N` which makes the sharp window `|N^d β| ≤ 1` lie inside the major arcs.

All the auxiliary declarations live in the namespace `BlockErrN` so that they cannot collide with
the other (dyadic) bookkeeping lemmas.
-/

namespace BlockErrN

/-! ## The arc-restricted model term at an arbitrary scale -/

open Classical in
/-- A single arc term of the `m`-th block of the model at an arbitrary scale `N`, restricted to
its arc `|c θ − a/q − l| ≤ N^{−(d−1/4)}` (the arbitrary-scale version of `polyModelTermArc`). -/
noncomputable def polyModelTermArcN (P : Polynomial ℤ) (q a : ℕ) (l : ℤ) (N : ℕ) (θ : ℝ) : ℂ :=
  if |(P.leadingCoeff : ℝ) * θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRadN P N
    then polyModelTermPre P N q a l θ else 0

/-! ## The `q`-block of the model at an arbitrary scale -/

/-- **The `q`-filter of the `m`-th block at an arbitrary scale.**  If `2^{4m+4} ≤ N` then the
denominators of the `m`-th dyadic block are exactly `2^m ≤ q < 2^{m+1}` (the arbitrary-scale
form of `blockQ_eq`). -/
lemma blockQN_eq (m N : ℕ) (hN : 2 ^ (4 * m + 4) ≤ N) :
    (Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)))).filter (fun q => Nat.log 2 q = m)
      = Finset.Ico (2^m) (2^(m+1)) := by
  rw [filter_log_eq_filter_pow]
  ext q
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
  have hQ : 2^(m+1) - 1 ≤ Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) := by
    refine Nat.le_floor ?_
    have h2 : (2:ℝ)^(m+1) ≤ (N : ℝ) ^ ((1:ℝ)/4) := by
      have hb : (2:ℝ)^(4*m+4) ≤ (N : ℝ) := by
        exact_mod_cast hN
      have h4 := Real.rpow_le_rpow (by positivity) hb (by norm_num : (0:ℝ) ≤ ((1:ℝ)/4))
      have h5 : ((2:ℝ)^(4*m+4))^((1:ℝ)/4) = (2:ℝ)^(m+1) := by
        rw [← Real.rpow_natCast (2:ℝ) (4*m+4), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
          ← Real.rpow_natCast (2:ℝ) (m+1)]
        congr 1
        push_cast
        ring
      linarith [h5]
    have h3 : ((2^(m+1) - 1 : ℕ) : ℝ) < (2:ℝ)^(m+1) := by
      have h4 := Nat.sub_lt (Nat.two_pow_pos (m+1)) (by norm_num : 0 < 1)
      push_cast
      exact_mod_cast h4
    linarith
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h3⟩
  · rintro ⟨h2, h3⟩
    exact ⟨by omega, h2, h3⟩

/-- The `q`-th block of the model at an arbitrary scale, as a sum of arc-restricted terms (the
arbitrary-scale form of `poly_majorArcBlock_two_pow_eq_sum`). -/
lemma poly_majorArcBlockN_eq_sum (P : Polynomial ℤ) (q N : ℕ) (θ : ℝ) :
    polyMajorArcBlockPre P ((1:ℝ)/4) N θ q
      = ∑ a ∈ Finset.range q, ∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
          (if Nat.gcd a q = 1 then polyModelTermArcN P q a l N θ else 0) := by
  have hmb : polyMajorArcBlockPre P ((1:ℝ)/4) N θ q
      = ∑ a ∈ Finset.range q, (if Nat.gcd a q = 1 then
          (∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
            (if |(P.leadingCoeff : ℝ) * θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRadN P N
              then polyModelTermPre P N q a l θ else 0)) else 0) := by
    unfold polyMajorArcBlockPre
    rfl
  rw [hmb]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases hg : Nat.gcd a q = 1
  · simp only [hg, if_true]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    unfold polyModelTermArcN
    rfl
  · simp only [hg, if_false, Finset.sum_const_zero]

/-- **The model block at an arbitrary scale is a sum over the index pairs of the block** (the
arbitrary-scale form of `poly_modelQBlock_two_pow_eq_blockPair`). -/
lemma poly_modelQBlockN_eq_blockPair (P : Polynomial ℤ) {m N : ℕ} (hN : 2 ^ (4*m+4) ≤ N)
    (θ : ℝ) :
    starRingEnd ℂ (polyModelQBlock P m N θ)
      = ∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
          starRingEnd ℂ (polyModelTermArcN P i.1 i.2 l N θ) := by
  have h1 : starRingEnd ℂ (polyModelQBlock P m N θ)
      = ∑ q ∈ Finset.Ico (2^m) (2^(m+1)),
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
            ∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
              starRingEnd ℂ (polyModelTermArcN P q a l N θ) := by
    unfold polyModelQBlock
    rw [blockQN_eq m N hN, map_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [poly_majorArcBlockN_eq_sum, map_sum]
    have hstep : ∀ a : ℕ,
        starRingEnd ℂ (∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
            (if Nat.gcd a q = 1 then polyModelTermArcN P q a l N θ else 0))
          = (if Nat.gcd a q = 1 then ∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
              starRingEnd ℂ (polyModelTermArcN P q a l N θ) else 0) := by
      intro a
      rw [map_sum]
      rw [Finset.sum_congr rfl (fun l _ => conj_ite_zero _ (polyModelTermArcN P q a l N θ))]
      exact sum_ite_gcd_eq' a q _ (fun l => starRingEnd ℂ (polyModelTermArcN P q a l N θ))
    rw [Finset.sum_congr rfl (fun a _ => hstep a), ← Finset.sum_filter]
  rw [h1, sum_blockPair m]

/-- The sharp core at an arbitrary scale is the sum over the index pairs of the sharp terms (the
arbitrary-scale form of `polyBlockCore_eq_sum_sharpTerm`). -/
lemma polyBlockCoreN_eq_sum_sharpTermN (P : Polynomial ℤ) (m N : ℕ) (θ : ℝ) :
    polyBlockCoreN P m N θ
      = ∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
          starRingEnd ℂ (polySharpTermN P i.1 i.2 l N θ) := rfl

/-- **The error of the `m`-th block at an arbitrary scale is the sum of the arc errors** (the
arbitrary-scale form of `polyBlockErr_eq_sum`). -/
lemma polyBlockErrN_eq_sum (P : Polynomial ℤ) {m N : ℕ} (hN : 2 ^ (4*m+4) ≤ N) (θ : ℝ) :
    polyBlockErrN P m N N θ
      = ∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
          starRingEnd ℂ (polyModelTermArcN P i.1 i.2 l N θ - polySharpTermN P i.1 i.2 l N θ) := by
  unfold polyBlockErrN
  rw [if_pos le_rfl, poly_modelQBlockN_eq_blockPair P hN θ, polyBlockCoreN_eq_sum_sharpTermN]
  simp_rw [← Finset.sum_sub_distrib, ← map_sub]

/-! ## The two vanishing lemmas -/

lemma polyModelTermArcN_eq_zero_of_not_act (P : Polynomial ℤ) (q a : ℕ) (l : ℤ) (N : ℕ)
    (θ : ℝ) (h : ¬ |(P.leadingCoeff : ℝ) * θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRadN P N) :
    polyModelTermArcN P q a l N θ = 0 := by
  unfold polyModelTermArcN; rw [if_neg h]

/-- If the sharp window at scale `N` is contained in the major arcs then the sharp term of an arc
vanishes off that arc (the arbitrary-scale form of `polySharpTerm_eq_zero_of_not_act`). -/
lemma polySharpTermN_eq_zero_of_not_act (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) {N : ℕ}
    (hN1 : 1 ≤ N) (hcont : (P.leadingCoeff : ℝ) * (polyDilN P N)⁻¹ ≤ polyArcRadN P N)
    (q a : ℕ) (l : ℤ) (θ : ℝ)
    (h : ¬ |(P.leadingCoeff : ℝ) * θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRadN P N) :
    polySharpTermN P q a l N θ = 0 := by
  have hc0 : (0 : ℝ) < (P.leadingCoeff : ℝ) := by exact_mod_cast hc
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (1:ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    linarith
  have hpos : 0 < polyDilN P N := by
    rw [polyDilN, ← Real.rpow_natCast (N:ℝ) P.natDegree]
    exact Real.rpow_pos_of_pos hNpos _
  have key : ¬ |polyDilN P N * (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ)))| ≤ 1 := by
    intro hc'
    apply h
    have h1 : |θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))| ≤ (polyDilN P N)⁻¹ := by
      rw [abs_mul, abs_of_pos hpos] at hc'
      rw [inv_eq_one_div, le_div_iff₀ hpos]
      linarith
    have halg : ((P.leadingCoeff : ℝ) * θ - (a:ℝ)/(q:ℝ) - (l:ℝ))
        = (P.leadingCoeff : ℝ) * (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))) := by
      field_simp
      ring
    rw [halg, abs_mul, abs_of_pos hc0]
    calc (P.leadingCoeff : ℝ) * |θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))|
        ≤ (P.leadingCoeff : ℝ) * (polyDilN P N)⁻¹ :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt hc0)
      _ ≤ polyArcRadN P N := hcont
  unfold polySharpTermN
  rw [if_neg key, mul_zero]

/-! ## The per-term profile error bound -/

/-- **Per-term profile error bound at an arbitrary scale** (the arbitrary-scale form of
`norm_polyModelTermArc_sub_sharp_le`). -/
lemma norm_polyModelTermArcN_sub_sharpN_le (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) {N : ℕ}
    (hN1 : 1 ≤ N) (hcont : (P.leadingCoeff : ℝ) * (polyDilN P N)⁻¹ ≤ polyArcRadN P N)
    (q a : ℕ) (l : ℤ) (θ : ℝ) :
    ‖polyModelTermArcN P q a l N θ - polySharpTermN P q a l N θ‖
      ≤ ‖polyWeight P (q * P.leadingCoeff.toNat) (a + l * q)‖ *
          polyErrValN P (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))) N := by
  by_cases harc : |(P.leadingCoeff : ℝ) * θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRadN P N
  · have h1 : polyModelTermArcN P q a l N θ = polyModelTermPre P N q a l θ := by
      unfold polyModelTermArcN; rw [if_pos harc]
    have h2 : polyModelTermPre P N q a l θ
        = polyWeight P (q * P.leadingCoeff.toNat) (a + l * q) *
            polyProfile P N (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))) := rfl
    have h3 : polySharpTermN P q a l N θ
        = polyWeight P (q * P.leadingCoeff.toNat) (a + l * q) *
            (if |polyDilN P N * (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ)))| ≤ 1
              then (1:ℂ) else 0) := rfl
    rw [h1, h2, h3, ← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_left le_rfl (norm_nonneg _)
  · rw [polyModelTermArcN_eq_zero_of_not_act P q a l N θ harc,
      polySharpTermN_eq_zero_of_not_act P hc hN1 hcont q a l θ harc, sub_zero, norm_zero]
    unfold polyErrValN
    positivity

/-! ## The cutoff: the sharp window is inside the major arcs -/

/-- **The scale cutoff.**  For `N ≥ c^4 + 1` (`c = P.leadingCoeff.toNat`) the sharp window
`|N^d β| ≤ 1` is contained in the major arc of radius `N^{−(d−1/4)}`: the edge of the sharp window
is `c·N^{−d} ≤ N^{−(d−1/4)}`, i.e. `c ≤ N^{1/4}`. -/
lemma le_arcRadN_of_le (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) {N : ℕ}
    (hK : P.leadingCoeff.toNat ^ 4 + 1 ≤ N) :
    (P.leadingCoeff : ℝ) * (polyDilN P N)⁻¹ ≤ polyArcRadN P N := by
  set c : ℕ := P.leadingCoeff.toNat with hcdef
  have hcZ : (c : ℤ) = P.leadingCoeff := Int.toNat_of_nonneg (le_of_lt hc)
  have hcR : (c : ℝ) = (P.leadingCoeff : ℝ) := by rw [← hcZ]; push_cast; ring
  have hN1 : 1 ≤ N := by omega
  have hNpos : 0 < (N : ℝ) := by
    have : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
    linarith
  have hcroot : (c : ℝ) ≤ (N : ℝ) ^ ((1:ℝ)/4) := by
    have hpow : (c:ℝ)^4 + 1 ≤ (N:ℝ) := by
      have h := hK
      have h2 : ((c^4 + 1 : ℕ) : ℝ) ≤ (N:ℝ) := by exact_mod_cast h
      push_cast at h2
      exact h2
    have hc0 : (0:ℝ) ≤ (c:ℝ) := by positivity
    have hlt : ((c:ℝ)^4) < ((c:ℝ)^4 + 1) := by linarith
    have h3 : (((c:ℝ)^4))^((1:ℝ)/4) < (((c:ℝ)^4+1))^((1:ℝ)/4) :=
      Real.rpow_lt_rpow (by positivity) hlt (by norm_num)
    have h4 : (((c:ℝ)^4+1))^((1:ℝ)/4) ≤ (N:ℝ)^((1:ℝ)/4) :=
      Real.rpow_le_rpow (by positivity) hpow (by norm_num)
    have h1 : (((c:ℝ)^4))^((1:ℝ)/4) = (c:ℝ) := by
      rw [← Real.rpow_natCast (c:ℝ) 4, ← Real.rpow_mul hc0,
        show (((4:ℕ):ℝ) * (1/4)) = 1 by norm_num, Real.rpow_one]
    linarith
  have hDilpos : 0 < polyDilN P N := by
    rw [polyDilN, ← Real.rpow_natCast (N:ℝ) P.natDegree]
    exact Real.rpow_pos_of_pos hNpos _
  have hA : polyArcRadN P N * polyDilN P N = (N:ℝ)^((1:ℝ)/4) := by
    rw [polyArcRadN, polyDilN, ← Real.rpow_natCast (N:ℝ) P.natDegree, ← Real.rpow_add hNpos]
    congr 1
    ring
  calc (P.leadingCoeff : ℝ) * (polyDilN P N)⁻¹
      = (c : ℝ) * (polyDilN P N)⁻¹ := by rw [hcR]
    _ ≤ polyArcRadN P N := by
        rw [inv_eq_one_div, mul_one_div, div_le_iff₀ hDilpos, hA]
        exact hcroot

end BlockErrN

open BlockErrN in
/-- **The error of the `m`-th denominator block of the model at an arbitrary scale is bounded by
the sum of the profile errors of the active arcs.**  This is the arbitrary-scale form of
`Work.BourgainPlan.Maximal.norm_polyBlockErr_le_actIdx`, needed because Bourgain's oscillation
inequality runs along the lacunary scales `⌊ρ^i⌋`. -/
theorem norm_polyBlockErrN_le_actIdxN (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff)
    (hd : 2 ≤ P.natDegree) :
    ∃ K : ℕ, ∀ (m N : ℕ), K ≤ N → 2 ^ (4 * m + 4) ≤ N → ∀ θ : ℝ, 0 < θ → θ < 1 →
      ‖Work.BourgainPlan.Oscillation.polyBlockErrN P m N N θ‖
        ≤ ∑ p ∈ Work.BourgainPlan.Oscillation.polyActIdxN P m N θ,
            ‖Work.BourgainPlan.Maximal.polyWeight P (p.1.1 * P.leadingCoeff.toNat)
                (p.1.2 + p.2 * p.1.1)‖ *
              Work.BourgainPlan.Oscillation.polyErrValN P
                (θ - (((p.1.2:ℝ)/(p.1.1:ℝ) + (p.2:ℝ)) / (P.leadingCoeff:ℝ))) N := by
  refine ⟨P.leadingCoeff.toNat ^ 4 + 1, fun m N hK hmN θ hθ0 hθ1 => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hcont : (P.leadingCoeff : ℝ) * (polyDilN P N)⁻¹ ≤ polyArcRadN P N :=
    BlockErrN.le_arcRadN_of_le P hc hK
  set g : (ℕ × ℕ) × ℤ → ℝ := fun p =>
    ‖polyWeight P (p.1.1 * P.leadingCoeff.toNat) (p.1.2 + p.2 * p.1.1)‖ *
      polyErrValN P (θ - (((p.1.2:ℝ)/(p.1.1:ℝ) + (p.2:ℝ)) / (P.leadingCoeff:ℝ))) N with hg
  rw [BlockErrN.polyBlockErrN_eq_sum P hmN θ]
  rw [← Finset.sum_product (blockPair m) (Finset.Icc (-1:ℤ) P.leadingCoeff)
    (fun p : (ℕ × ℕ) × ℤ =>
      starRingEnd ℂ (BlockErrN.polyModelTermArcN P p.1.1 p.1.2 p.2 N θ -
        polySharpTermN P p.1.1 p.1.2 p.2 N θ))]
  calc ‖∑ p ∈ blockPair m ×ˢ Finset.Icc (-1:ℤ) P.leadingCoeff,
          starRingEnd ℂ (BlockErrN.polyModelTermArcN P p.1.1 p.1.2 p.2 N θ -
            polySharpTermN P p.1.1 p.1.2 p.2 N θ)‖
      ≤ ∑ p ∈ blockPair m ×ˢ Finset.Icc (-1:ℤ) P.leadingCoeff,
          (if |(P.leadingCoeff : ℝ) * θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)| ≤ polyArcRadN P N
            then g p else 0) := by
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun p hp => ?_))
        by_cases harc : |(P.leadingCoeff : ℝ) * θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)|
            ≤ polyArcRadN P N
        · rw [if_pos harc, Complex.norm_conj]
          simpa only [hg] using
            BlockErrN.norm_polyModelTermArcN_sub_sharpN_le P hc hN1 hcont
              (N := N) p.1.1 p.1.2 p.2 θ
        · rw [if_neg harc]
          have h1 := BlockErrN.polyModelTermArcN_eq_zero_of_not_act P p.1.1 p.1.2 p.2 N θ harc
          have h2 := BlockErrN.polySharpTermN_eq_zero_of_not_act P hc hN1 hcont
            p.1.1 p.1.2 p.2 θ harc
          rw [h1, h2, sub_zero, map_zero, norm_zero]
    _ = ∑ p ∈ polyActIdxN P m N θ, g p := by
        rw [polyActIdxN, polyAllIdx, ← Finset.sum_filter]

end

end Work.BourgainPlan.Oscillation
