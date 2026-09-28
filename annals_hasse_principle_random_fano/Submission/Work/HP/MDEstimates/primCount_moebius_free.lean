import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.MDEstimates.PrimDecomp
import Submission.Work.HP.MDEstimates.moebius_multiples_sum

/-!
# Möbius inversion for the primitive points of a saturated lattice

For a saturated (= primitive / pure) integral lattice `L ⊆ ℤ^ι` and `T ≥ 0`, the number of
primitive points of `L` of Euclidean norm at most `T` equals
`∑_{l ≥ 1} μ(l) · (#{a ∈ L : ‖a‖ ≤ T/l} - 1)`.

The identity is the Möbius expansion of `1_{IsPrim a} = ∑_{l | gcd a} μ(l)` against the
decomposition of a nonzero lattice point as `a = k • b` with `k ≥ 1` and `b` primitive, i.e.
`k = pFac a`, `b = pDir a` (see `Submission.Work.HP.MDEstimates.PrimDecomp`).  Saturation is used
exactly here: `k • b ∈ L` implies `b ∈ L`.  The resulting sum over `l` is truncated at
`K = ⌈T⌉ + 1`, because for `l > K` the ball `{a ∈ L : ‖a‖ ≤ T/l}` consists of the origin alone
(its radius is `< 1`), so the corresponding summand `μ(l)·(1 - 1)` vanishes.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset

namespace Work.HP.MDEstimates

section Aux

variable {ι : Type*} [Fintype ι]

/-- A primitive vector is nonzero. -/
private lemma isPrim_ne_zero {v : ι → ℤ} (hv : IsPrim v) : v ≠ 0 := by
  intro h
  have h0 : Finset.univ.gcd v = 0 := by
    rw [Finset.gcd_eq_zero_iff]
    intro i _
    rw [h]
    rfl
  rw [IsPrim] at hv
  rw [hv] at h0
  exact one_ne_zero h0

/-- An integer vector of Euclidean norm `< 1` is zero. -/
private lemma eq_zero_of_eNorm_le_of_lt_one {a : ι → ℤ} {r : ℝ} (h : eNorm a ≤ r) (hr : r < 1) :
    a = 0 := by
  by_contra ha
  have h1 : (1 : ℝ) ≤ eNorm a := one_le_eNorm_of_ne_zero ha
  linarith

/-- For `0 ≤ r < 1`, the points of `L` of norm at most `r` are exactly the origin. -/
private lemma ncard_ball_of_lt_one (L : Submodule ℤ (ι → ℤ)) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) : ({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ r}.ncard) = 1 := by
  have hset : {a : ι → ℤ | a ∈ L ∧ eNorm a ≤ r} = ({0} : Set (ι → ℤ)) := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, ha⟩
      exact eq_zero_of_eNorm_le_of_lt_one ha hr1
    · rintro rfl
      exact ⟨L.zero_mem, by simpa [eNorm] using hr0⟩
  rw [hset, Set.ncard_singleton]

/-- Splitting off the origin: for `r ≥ 0` the points of `L` of norm at most `r` are the origin
together with the nonzero ones. -/
private lemma ncard_ball_eq_succ (L : Submodule ℤ (ι → ℤ)) {r : ℝ} (hr0 : 0 ≤ r) :
    ({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ r}.ncard) =
      ({a : ι → ℤ | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ r}.ncard) + 1 := by
  have hfin : {a : ι → ℤ | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ r}.Finite :=
    (MDBasic.finite_eNorm_le r).subset (fun a ha => ha.2.2)
  have hnot : (0 : ι → ℤ) ∉ {a : ι → ℤ | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ r} := by
    simp
  have hset : {a : ι → ℤ | a ∈ L ∧ eNorm a ≤ r}
      = insert (0 : ι → ℤ) {a : ι → ℤ | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ r} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
    constructor
    · rintro ⟨haL, ha⟩
      by_cases h : a = 0
      · exact Or.inl h
      · exact Or.inr ⟨haL, h, ha⟩
    · rintro (rfl | ⟨haL, -, ha⟩)
      · exact ⟨L.zero_mem, by simpa [eNorm] using hr0⟩
      · exact ⟨haL, ha⟩
  rw [hset, Set.ncard_insert_of_notMem hnot hfin]

/-- A nonzero scalar multiple of a nonzero vector is nonzero. -/
private lemma scale_ne_zero {k : ℕ} (hk : 1 ≤ k) {b : ι → ℤ} (hb : b ≠ 0) : scale k b ≠ 0 := by
  intro h
  refine hb (scale_injective k hk ?_)
  rw [h]
  funext i
  simp [scale]

end Aux

section Census

variable {ι : Type*} [Fintype ι]

/-- Counting the pairs `(k, b)` with `k ∈ t` and `b ∈ U k`: the set of pairs fibres over the
first coordinate. -/
private lemma ncard_sigma_set (t : Finset ℕ) (U : ℕ → Set (ι → ℤ))
    (hfin : ∀ k, (U k).Finite) :
    {p : ℕ × (ι → ℤ) | p.1 ∈ t ∧ p.2 ∈ U p.1}.ncard = ∑ k ∈ t, (U k).ncard := by
  classical
  have hfun : ∀ k, ((fun b : ι → ℤ => (k, b)) '' U k).Finite := fun k => (hfin k).image _
  have hdisj : ((t : Set ℕ)).PairwiseDisjoint (fun k => (fun b : ι → ℤ => (k, b)) '' U k) := by
    intro k _ k' _ hne
    show Disjoint ((fun b : ι → ℤ => (k, b)) '' U k) ((fun b : ι → ℤ => (k', b)) '' U k')
    rw [Set.disjoint_left]
    rintro p ⟨b, _, rfl⟩ ⟨b', _, h'⟩
    exact hne ((Prod.mk.injEq k' b' k b).mp h').1.symm
  have hunion : {p : ℕ × (ι → ℤ) | p.1 ∈ t ∧ p.2 ∈ U p.1}
      = ⋃ k ∈ (t : Set ℕ), (fun b : ι → ℤ => (k, b)) '' U k := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨hkt, hb⟩
      exact ⟨p.1, hkt, p.2, hb, rfl⟩
    · rintro ⟨k, hkt, b, hb, hkb⟩
      rw [← hkb]
      exact ⟨hkt, hb⟩
  rw [hunion, Set.Finite.ncard_biUnion (Finset.finite_toSet t) (fun k _ => hfun k) hdisj,
    finsum_mem_eq_finite_toFinset_sum _ (Finset.finite_toSet t), Finset.finite_toSet_toFinset]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact Set.ncard_image_of_injective (U k) (fun b b' h => (Prod.mk.injEq k b k b').mp h |>.2)

/-- Counting the nonzero points of a saturated lattice by primitive direction: every nonzero
`a ∈ L` is uniquely `k • b` with `k ≥ 1` and `b ∈ L` primitive, and `‖k • b‖ = k·‖b‖`.  The sum
may be truncated at `K` because a primitive vector has norm `≥ 1`, so the scale factors occurring
satisfy `k ≤ r ≤ K`.  (The hypothesis `0 ≤ r` is not needed.) -/
private lemma census_ncard (L : Submodule ℤ (ι → ℤ))
    (hL : IsPrimLat L) {r : ℝ} (_hr : 0 ≤ r) (K : ℕ) (hK : r ≤ (K : ℝ)) :
    {a : ι → ℤ | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ r}.ncard =
      ∑ k ∈ Finset.Icc 1 K,
        {b : ι → ℤ | b ∈ L ∧ IsPrim b ∧ eNorm b ≤ r / (k : ℝ)}.ncard := by
  classical
  have h1 : {a : ι → ℤ | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ r}.ncard
      = ({p : ℕ × (ι → ℤ) | p.1 ∈ Finset.Icc 1 K ∧ p.2 ∈ L ∧ IsPrim p.2 ∧
          eNorm p.2 ≤ r / (p.1 : ℝ)}).ncard := by
    refine Set.ncard_congr (fun a _ => (pFac a, pDir a)) ?_ ?_ ?_
    · intro a ha
      simp only [Set.mem_ofPred_eq] at ha
      obtain ⟨haL, ha0, han⟩ := ha
      have hfac1 : 1 ≤ pFac a := one_le_pFac ha0
      have hdirL : pDir a ∈ L := by
        have h1 : ((pFac a : ℕ) : ℤ) • pDir a ∈ L := by
          rw [← scale_eq_smul, scale_pFac_pDir ha0]
          exact haL
        exact hL (pDir a) ((pFac a : ℕ) : ℤ) (by
          have h2 : (1 : ℤ) ≤ ((pFac a : ℕ) : ℤ) := by exact_mod_cast hfac1
          omega) h1
      have hdirprim : IsPrim (pDir a) := isPrim_pDir ha0
      have hdirne : pDir a ≠ 0 := isPrim_ne_zero hdirprim
      have hfpos : (0 : ℝ) < (pFac a : ℝ) := by exact_mod_cast hfac1
      have hnorm : eNorm a = (pFac a : ℝ) * eNorm (pDir a) := by
        rw [← eNorm_scale, scale_pFac_pDir ha0]
      have hbound : eNorm (pDir a) ≤ r / (pFac a : ℝ) := by
        rw [le_div_iff₀ hfpos, mul_comm, ← hnorm]
        exact han
      have hfacK : pFac a ≤ K := by
        have h2 : (1 : ℝ) ≤ eNorm (pDir a) := one_le_eNorm_of_ne_zero hdirne
        have h3 : (pFac a : ℝ) ≤ eNorm a := by
          rw [hnorm]
          nlinarith [hfpos, h2]
        exact_mod_cast (le_trans h3 (le_trans han hK))
      simp only [Set.mem_ofPred_eq]
      exact ⟨Finset.mem_Icc.mpr ⟨hfac1, hfacK⟩, hdirL, hdirprim, hbound⟩
    · intro a b ha hb hab
      simp only [Set.mem_ofPred_eq] at ha hb
      obtain ⟨haL, ha0, han⟩ := ha
      obtain ⟨hbL, hb0, hbn⟩ := hb
      have hpair := (Prod.mk.injEq (pFac a) (pDir a) (pFac b) (pDir b)).mp hab
      calc a = scale (pFac a) (pDir a) := (scale_pFac_pDir ha0).symm
        _ = scale (pFac b) (pDir b) := by rw [hpair.1, hpair.2]
        _ = b := scale_pFac_pDir hb0
    · rintro ⟨k, b⟩ hp
      simp only [Set.mem_ofPred_eq] at hp
      obtain ⟨hk, hbL, hbprim, hbn⟩ := hp
      obtain ⟨hk1, _hkK⟩ := Finset.mem_Icc.mp hk
      refine ⟨scale k b, ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq]
        refine ⟨?_, ?_, ?_⟩
        · rw [scale_eq_smul]
          exact L.smul_mem (k : ℤ) hbL
        · exact scale_ne_zero hk1 (isPrim_ne_zero hbprim)
        · have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
          rw [eNorm_scale]
          have hkr : (k : ℝ) * (r / (k : ℝ)) = r := by field_simp
          rw [← hkr]
          exact mul_le_mul_of_nonneg_left hbn hkpos.le
      · show (pFac (scale k b), pDir (scale k b)) = (k, b)
        rw [pFac_scale_of_isPrim k hbprim, pDir_scale_of_isPrim k hbprim hk1]
  rw [h1]
  exact ncard_sigma_set (Finset.Icc 1 K)
    (fun k => {b : ι → ℤ | b ∈ L ∧ IsPrim b ∧ eNorm b ≤ r / (k : ℝ)})
    (fun k => (MDBasic.finite_eNorm_le (r / (k : ℝ))).subset
      (fun b hb => by simpa only [Set.mem_ofPred_eq] using hb.2.2))

end Census

/-- Möbius inversion for the primitive points of a saturated lattice. -/
theorem primCount_moebius_free {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℤ))
    (hL : IsPrimLat L) {T : ℝ} (hT : 0 ≤ T) :
    (({a : ι → ℤ | a ∈ L ∧ IsPrim a ∧ eNorm a ≤ T}.ncard : ℝ)) =
      ∑' l : ℕ, (ArithmeticFunction.moebius l : ℝ) *
        ((({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T / l}.ncard : ℕ) : ℝ) - 1) := by
  classical
  set K : ℕ := ⌈T⌉₊ + 1 with hKdef
  have hTK : T < (K : ℝ) := by
    have h1 : T ≤ (⌈T⌉₊ : ℝ) := Nat.le_ceil T
    have h2 : ((⌈T⌉₊ : ℕ) : ℝ) < ((⌈T⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
    rw [hKdef]
    push_cast
    linarith
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    have h : (0 : ℕ) < K := by simp [hKdef]
    exact_mod_cast h
  set F : ℕ → ℝ := fun n =>
    (({b : ι → ℤ | b ∈ L ∧ IsPrim b ∧ eNorm b ≤ T / (n : ℝ)}.ncard : ℕ) : ℝ) with hFdef
  -- the summand vanishes for all `n > K`
  have hFsupp : ∀ n : ℕ, K < n → F n = 0 := by
    intro n hn
    have hKg : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_lt hn)
    have hle : T / (n : ℝ) ≤ T / (K : ℝ) := by
      have h1 : (1 : ℝ) / (n : ℝ) ≤ 1 / (K : ℝ) := one_div_le_one_div_of_le hKpos hKg
      rw [div_eq_mul_one_div T (n : ℝ), div_eq_mul_one_div T (K : ℝ)]
      exact mul_le_mul_of_nonneg_left h1 hT
    have hltK : T / (K : ℝ) < 1 := by
      rw [div_lt_one hKpos]
      exact hTK
    have hlt : T / (n : ℝ) < 1 := lt_of_le_of_lt hle hltK
    have hempty : {b : ι → ℤ | b ∈ L ∧ IsPrim b ∧ eNorm b ≤ T / (n : ℝ)}
        = (∅ : Set (ι → ℤ)) := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro b ⟨-, hbp, hbn⟩
      have h1 : (1 : ℝ) ≤ eNorm b := one_le_eNorm_of_ne_zero (isPrim_ne_zero hbp)
      linarith
    rw [hFdef]
    simp [hempty]
  -- reduce the `tsum` to the finite sum over `Icc 1 K`
  have hstep1 : (∑' l : ℕ, (ArithmeticFunction.moebius l : ℝ) *
        ((({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T / l}.ncard : ℕ) : ℝ) - 1))
      = ∑ l ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius l : ℝ) *
        ((({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T / l}.ncard : ℕ) : ℝ) - 1) := by
    refine tsum_eq_sum (s := Finset.Icc 1 K) ?_
    intro l hl
    have hcases : l < 1 ∨ K < l := by
      by_cases h1 : 1 ≤ l
      · right
        by_contra h
        push Not at h
        exact hl (Finset.mem_Icc.mpr ⟨h1, h⟩)
      · left; omega
    obtain h0 | hKl := hcases
    · have hl0 : l = 0 := by omega
      rw [hl0]
      have hn := ncard_ball_of_lt_one L (r := T / ((0 : ℕ) : ℝ)) (by simp) (by simp)
      rw [hn]
      ring
    · have hlpos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (by omega : 1 ≤ l)
      have hKg : (K : ℝ) ≤ (l : ℝ) := by exact_mod_cast (le_of_lt hKl)
      have hr : (0 : ℝ) ≤ T / (l : ℝ) := div_nonneg hT hlpos.le
      have hlt : T / (l : ℝ) < 1 := by
        have hle : T / (l : ℝ) ≤ T / (K : ℝ) := by
          have h1 : (1 : ℝ) / (l : ℝ) ≤ 1 / (K : ℝ) := one_div_le_one_div_of_le hKpos hKg
          rw [div_eq_mul_one_div T (l : ℝ), div_eq_mul_one_div T (K : ℝ)]
          exact mul_le_mul_of_nonneg_left h1 hT
        have hltK : T / (K : ℝ) < 1 := by
          rw [div_lt_one hKpos]
          exact hTK
        linarith
      have hn := ncard_ball_of_lt_one L hr hlt
      rw [hn]
      ring
  rw [hstep1]
  -- each summand, rewritten as a sum over the scale factor
  have hterm : ∀ l ∈ Finset.Icc 1 K,
      (ArithmeticFunction.moebius l : ℝ) *
        ((({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T / l}.ncard : ℕ) : ℝ) - 1)
      = (ArithmeticFunction.moebius l : ℝ) * (∑ k ∈ Finset.Icc 1 K, F (l * k)) := by
    intro l hl
    obtain ⟨hl1, _hlK⟩ := Finset.mem_Icc.mp hl
    have hlpos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl1
    have hr : (0 : ℝ) ≤ T / (l : ℝ) := div_nonneg hT hlpos.le
    have hrK : T / (l : ℝ) ≤ (K : ℝ) := by
      rw [div_le_iff₀ hlpos]
      have hKl : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl1
      have hmul : (K : ℝ) * 1 ≤ (K : ℝ) * (l : ℝ) := mul_le_mul_of_nonneg_left hKl hKpos.le
      nlinarith [hT, le_of_lt hTK]
    have hinner : (∑ k ∈ Finset.Icc 1 K, F (l * k))
        = ∑ k ∈ Finset.Icc 1 K,
            (({b : ι → ℤ | b ∈ L ∧ IsPrim b ∧ eNorm b ≤ (T / (l : ℝ)) / (k : ℝ)}.ncard : ℕ)
              : ℝ) := by
      rw [hFdef]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      show (({b : ι → ℤ | b ∈ L ∧ IsPrim b ∧ eNorm b ≤ T / ((l * k : ℕ) : ℝ)}.ncard : ℕ) : ℝ)
        = (({b : ι → ℤ | b ∈ L ∧ IsPrim b ∧ eNorm b ≤ (T / (l : ℝ)) / (k : ℝ)}.ncard : ℕ) : ℝ)
      have hthr : (T / (l : ℝ)) / (k : ℝ) = T / ((l * k : ℕ) : ℝ) := by
        rw [div_div]
        push_cast
        ring
      rw [hthr]
    rw [hinner]
    congr 1
    have hsplit := ncard_ball_eq_succ L hr
    have h1 : ((({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T / (l : ℝ)}.ncard : ℕ) : ℝ) - 1)
        = (({a : ι → ℤ | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ T / (l : ℝ)}.ncard : ℕ) : ℝ) := by
      rw [hsplit]; push_cast; ring
    rw [h1]
    rw [census_ncard L hL hr K hrK, Nat.cast_sum]
  rw [Finset.sum_congr rfl hterm, moebius_multiples_sum K F hFsupp]
  have hlast : F 1 = (({a : ι → ℤ | a ∈ L ∧ IsPrim a ∧ eNorm a ≤ T}.ncard : ℕ) : ℝ) := by
    rw [hFdef]
    simp
  rw [hlast]

end Work.HP.MDEstimates
