import Mathlib
import Submission.Commons.NumberTheory.Counting.ncard_prod_max_one_abs_le_factorial
import Submission.Commons.NumberTheory.NumberField.ncard_mahler_le
import Submission.Commons.NumberTheory.NumberField.units_rank_eq_nrRealPlaces_add_nrComplexPlaces_sub_one
import Submission.Commons.Analysis.SpecialFunctions.mahler_arith_small_lam
import Submission.Commons.Analysis.SpecialFunctions.mahler_arith_large_lam
import Submission.Commons.NumberTheory.NumberField.exists_two_stdBasis_coord_intCast
import Submission.Commons.Analysis.SpecialFunctions.mahler_except_le

set_option maxHeartbeats 1000000

open NumberField NumberField.mixedEmbedding
open scoped Classical BigOperators

namespace Commons.NumberTheory.NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- The real coordinates of an element of `K` (the coordinates on the `stdBasis` of the mixed
space): one coordinate per real place, two (real and imaginary part) per complex place. -/
abbrev mahlerCoord (l : NumberField.mixedEmbedding.index K) (a : K) : ℝ :=
  (NumberField.mixedEmbedding.stdBasis K).repr (NumberField.mixedEmbedding K a) l

lemma mahlerCoord_add (l : NumberField.mixedEmbedding.index K) (a b : K) :
    mahlerCoord l (a + b) = mahlerCoord l a + mahlerCoord l b := by simp [mahlerCoord]

lemma mahlerCoord_sub (l : NumberField.mixedEmbedding.index K) (a b : K) :
    mahlerCoord l (a - b) = mahlerCoord l a - mahlerCoord l b := by simp [mahlerCoord]

lemma mahlerCoord_neg (l : NumberField.mixedEmbedding.index K) (a : K) :
    mahlerCoord l (-a) = -mahlerCoord l a := by simp [mahlerCoord]

lemma card_mixedEmbedding_index : Fintype.card (NumberField.mixedEmbedding.index K) = Module.finrank ℚ K := by
  rw [← NumberField.mixedEmbedding.finrank (K := K)]
  exact (Module.finrank_eq_card_basis (stdBasis K)).symm

/-- The product over all real coordinates of `max 1 |·|` is at most the product over the infinite
places of `(max 1 |·|_w) ^ w.mult`. -/
lemma prod_max_one_mahlerCoord_le (a : K) :
    (∏ l : NumberField.mixedEmbedding.index K, max 1 |mahlerCoord l a|) ≤
      ∏ w : NumberField.InfinitePlace K,
        (max 1 (NumberField.mixedEmbedding.normAtPlace w
          (NumberField.mixedEmbedding K a))) ^ w.mult := by
  classical
  simp_rw [NumberField.mixedEmbedding.normAtPlace_apply]
  have hL : (∏ l : NumberField.mixedEmbedding.index K, max 1 |mahlerCoord l a|)
      = (∏ w : {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w},
            max 1 |mahlerCoord (Sum.inl w) a|)
        * ∏ w : {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex w},
            ∏ j : Fin 2, max 1 |mahlerCoord (Sum.inr (w, j)) a| := by
    rw [Fintype.prod_sum_type]
    congr 1
    rw [Fintype.prod_prod_type]
  have hR : (∏ w : NumberField.InfinitePlace K, (max 1 (w a)) ^ w.mult)
      = (∏ w : {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w},
            max 1 (w.1 a))
        * ∏ w : {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex w},
            (max 1 (w.1 a)) ^ 2 := by
    rw [NumberField.InfinitePlace.prod_eq_prod_mul_prod]
    congr 1
    · exact Finset.prod_congr rfl (fun w _ => by
        rw [NumberField.InfinitePlace.mult_isReal, pow_one])
    · apply Finset.prod_congr rfl
      intro w _
      rw [NumberField.InfinitePlace.mult_isComplex]
  rw [hL, hR]
  have h1 : (∏ w : {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w},
        max 1 |mahlerCoord (Sum.inl w) a|)
      ≤ ∏ w : {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w},
            max 1 (w.1 a) := by
    apply Finset.prod_le_prod
    · intro w _
      exact le_trans zero_le_one (le_max_left _ _)
    · intro w _
      simp only [mahlerCoord, NumberField.mixedEmbedding.stdBasis_apply_isReal,
        NumberField.mixedEmbedding.mixedEmbedding_apply_isReal]
      rw [← NumberField.InfinitePlace.norm_embedding_of_isReal w.prop a, Real.norm_eq_abs]
  have h2 : (∏ w : {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex w},
        ∏ j : Fin 2, max 1 |mahlerCoord (Sum.inr (w, j)) a|)
      ≤ ∏ w : {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex w},
            (max 1 (w.1 a)) ^ 2 := by
    apply Finset.prod_le_prod
    · intro w _
      exact Finset.prod_nonneg (fun j _ => le_trans zero_le_one (le_max_left _ _))
    · intro w _
      rw [Fin.prod_univ_two]
      simp only [mahlerCoord, NumberField.mixedEmbedding.stdBasis_apply_isComplex_fst,
        NumberField.mixedEmbedding.stdBasis_apply_isComplex_snd,
        NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]
      set z : ℂ := (w.1 : NumberField.InfinitePlace K).embedding a with hz
      have hnorm : (w.1 : NumberField.InfinitePlace K) a = ‖z‖ := by
        rw [← NumberField.InfinitePlace.mk_embedding (w.1), hz]
        exact NumberField.InfinitePlace.apply _ _
      rw [hnorm]
      rcases le_or_gt (1 : ℝ) ‖z‖ with hlt | hlt
      · have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
        have him : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
        rw [max_eq_right hlt]
        calc max 1 |z.re| * max 1 |z.im| ≤ ‖z‖ * ‖z‖ := by
              apply mul_le_mul
              · exact max_le hlt hre
              · exact max_le hlt him
              · exact le_trans zero_le_one (le_max_left _ _)
              · exact norm_nonneg z
          _ = ‖z‖ ^ 2 := by ring
      · have hzle : ‖z‖ < 1 := hlt
        have hre : |z.re| < 1 := lt_of_le_of_lt (Complex.abs_re_le_norm z) hzle
        have him : |z.im| < 1 := lt_of_le_of_lt (Complex.abs_im_le_norm z) hzle
        rw [max_eq_left (le_of_lt hlt), max_eq_left (le_of_lt hre), max_eq_left (le_of_lt him)]
        norm_num
  have h2n : 0 ≤ (∏ w : {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex w},
        ∏ j : Fin 2, max 1 |mahlerCoord (Sum.inr (w, j)) a|) :=
    Finset.prod_nonneg (fun w _ =>
      Finset.prod_nonneg (fun j _ => le_trans zero_le_one (le_max_left _ _)))
  have h1n : 0 ≤ (∏ w : {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w},
        max 1 (w.1 a)) :=
    Finset.prod_nonneg (fun w _ => le_trans zero_le_one (le_max_left _ _))
  exact mul_le_mul h1 h2 h2n h1n

/-- Some real coordinate of `a` is at least half of its house. -/
lemma exists_mahlerCoord_ge_half_house (a : K) :
    ∃ l : NumberField.mixedEmbedding.index K, NumberField.house a ≤ 2 * |mahlerCoord l a| := by
  classical
  obtain ⟨w₀, -, hw₀⟩ := Finset.exists_max_image Finset.univ
    (fun w : NumberField.InfinitePlace K => w a) Finset.univ_nonempty
  have hle : NumberField.house a ≤ w₀ a := by
    have h : ∀ φ : K →+* ℂ, ‖φ a‖ ≤ w₀ a := by
      intro φ
      rw [← NumberField.InfinitePlace.apply]
      exact hw₀ _ (Finset.mem_univ _)
    rw [NumberField.house, NumberField.canonicalEmbedding.norm_le_iff]
    exact h
  rcases w₀.isReal_or_isComplex with hreal | hcompl
  · refine ⟨Sum.inl ⟨w₀, hreal⟩, ?_⟩
    have hcoord : mahlerCoord (Sum.inl ⟨w₀, hreal⟩) a =
        (NumberField.InfinitePlace.embedding_of_isReal hreal) a := by
      simp only [mahlerCoord, NumberField.mixedEmbedding.stdBasis_apply_isReal,
        NumberField.mixedEmbedding.mixedEmbedding_apply_isReal]
    refine hle.trans ?_
    rw [hcoord, ← NumberField.InfinitePlace.norm_embedding_of_isReal hreal a, Real.norm_eq_abs]
    linarith [abs_nonneg (NumberField.InfinitePlace.embedding_of_isReal hreal a)]
  · have hcompl' : ¬ NumberField.InfinitePlace.IsReal w₀ :=
      fun h => NumberField.InfinitePlace.ne_of_isReal_isComplex h hcompl rfl
    have hnorm : w₀ a = ‖w₀.embedding a‖ := by
      conv_lhs => rw [← NumberField.InfinitePlace.mk_embedding w₀]
      exact NumberField.InfinitePlace.apply w₀.embedding a
    have hcoord : ∀ j : Fin 2, mahlerCoord (Sum.inr (⟨w₀, hcompl⟩, j)) a =
        (if j = 0 then (w₀.embedding a).re else (w₀.embedding a).im) := by
      intro j
      fin_cases j <;>
      simp [mahlerCoord, NumberField.mixedEmbedding.stdBasis_apply_isComplex_fst,
        NumberField.mixedEmbedding.stdBasis_apply_isComplex_snd,
        NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]
    rw [hnorm] at hle
    rcases le_or_gt |(w₀.embedding a).re| |(w₀.embedding a).im| with h | h
    · refine ⟨Sum.inr (⟨w₀, hcompl⟩, 1), ?_⟩
      rw [hcoord 1]
      have h1 : ‖w₀.embedding a‖ ≤ |(w₀.embedding a).re| + |(w₀.embedding a).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      rw [if_neg (by decide : ¬ (1 : Fin 2) = 0)] at *
      linarith
    · refine ⟨Sum.inr (⟨w₀, hcompl⟩, 0), ?_⟩
      rw [hcoord 0]
      have h1 : ‖w₀.embedding a‖ ≤ |(w₀.embedding a).re| + |(w₀.embedding a).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      rw [if_pos rfl] at *
      linarith

/-- The coordinates of an integer: a coordinate is either the integer itself or zero. -/
lemma mahlerCoord_intCast (l : NumberField.mixedEmbedding.index K) (k : ℤ) :
    mahlerCoord l ((k : K)) = (k : ℝ) ∨ mahlerCoord l ((k : K)) = 0 := by
  rcases l with w | wj
  · left
    simp [mahlerCoord, NumberField.mixedEmbedding.stdBasis_apply_isReal,
      NumberField.mixedEmbedding.mixedEmbedding_apply_isReal,
      NumberField.InfinitePlace.embedding_of_isReal_apply]
  · rcases wj with ⟨w, j⟩
    fin_cases j
    · left
      simp [mahlerCoord, NumberField.mixedEmbedding.stdBasis_apply_isComplex_fst,
        NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]
    · right
      simp [mahlerCoord, NumberField.mixedEmbedding.stdBasis_apply_isComplex_snd,
        NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]

/-- Some coordinate of an integer equals the integer itself. -/
lemma exists_mahlerCoord_intCast (k : ℤ) :
    ∃ l : NumberField.mixedEmbedding.index K, mahlerCoord l ((k : K)) = (k : ℝ) := by
  classical
  by_cases h : ∃ w : NumberField.InfinitePlace K, NumberField.InfinitePlace.IsReal w
  · obtain ⟨w, hw⟩ := h
    exact ⟨Sum.inl ⟨w, hw⟩, by
      simp [mahlerCoord, NumberField.mixedEmbedding.stdBasis_apply_isReal,
        NumberField.mixedEmbedding.mixedEmbedding_apply_isReal,
        NumberField.InfinitePlace.embedding_of_isReal_apply]⟩
  · push_neg at h
    obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace K))
    exact ⟨Sum.inr ⟨⟨w, NumberField.InfinitePlace.not_isReal_iff_isComplex.mp (h w)⟩, 0⟩, by
      simp [mahlerCoord, NumberField.mixedEmbedding.stdBasis_apply_isComplex_fst,
        NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]⟩


/-- A "real type" coordinate: one for which the coordinate of a rational integer is the integer
itself (as opposed to the imaginary-part coordinates, where an integer has coordinate `0`). -/
lemma exists_realType_index (K : Type*) [Field K] [NumberField K] :
    ∃ l : NumberField.mixedEmbedding.index K, ∀ k : ℤ, mahlerCoord l ((k : K)) = (k : ℝ) := by
  classical
  by_cases h : ∃ w : NumberField.InfinitePlace K, NumberField.InfinitePlace.IsReal w
  · obtain ⟨w, hw⟩ := h
    refine ⟨Sum.inl ⟨w, hw⟩, fun k => ?_⟩
    simp [mahlerCoord, NumberField.mixedEmbedding.stdBasis_apply_isReal,
      NumberField.mixedEmbedding.mixedEmbedding_apply_isReal,
      NumberField.InfinitePlace.embedding_of_isReal_apply]
  · push Not at h
    obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace K))
    refine ⟨Sum.inr (⟨⟨w, NumberField.InfinitePlace.not_isReal_iff_isComplex.mp (h w)⟩, 0⟩),
      fun k => ?_⟩
    simp [mahlerCoord, NumberField.mixedEmbedding.stdBasis_apply_isComplex_fst,
      NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]

/-- **Injectivity of the grid.**  Fix a "real type" coordinate `l₀` and a scale `δ`.  Suppose
`a b` are two elements of the ring of integers whose coordinates differ by less than `1` in the
`l₀`-coordinate and by less than `max 1 δ` in every coordinate.  If `2 * max 1 δ ≤ lam` and every
non-rational element of the ring of integers has house `≥ lam`, then `a = b`.

Indeed, if `c := a - b` were non-rational then `lam ≤ house c ≤ 2 * max l |coord l c| <
2 * max 1 δ ≤ lam`, a contradiction; hence `c` is a rational integer `k`, and `k` is detected by
the `l₀`-coordinate: `|k| = |coord l₀ c| < 1`, so `k = 0`, i.e. `c = 0` and `a = b`. -/
lemma grid_injective {lam δ : ℝ} {l₀ : NumberField.mixedEmbedding.index K}
    (hrealType : ∀ k : ℤ, mahlerCoord l₀ ((k : K)) = (k : ℝ))
    (hδlam : 2 * max 1 δ ≤ lam)
    (hsep : ∀ α : NumberField.RingOfIntegers K, ((α : K)) ∉ Set.range (algebraMap ℤ K) →
      lam ≤ NumberField.house ((α : K)))
    {a b : NumberField.RingOfIntegers K}
    (hcoord₀ : |mahlerCoord l₀ ((a : K)) - mahlerCoord l₀ ((b : K))| < 1)
    (hcoord : ∀ l : NumberField.mixedEmbedding.index K,
      |mahlerCoord l ((a : K)) - mahlerCoord l ((b : K))| < max 1 δ) :
    a = b := by
  classical
  by_contra hne
  set c : NumberField.RingOfIntegers K := a - b with hc
  have hcK : ((c : K)) = ((a : K)) - ((b : K)) := by
    rw [hc]; push_cast; ring
  have hcabs : ∀ l, |mahlerCoord l ((c : K))| < max 1 δ := by
    intro l
    rw [hcK, mahlerCoord_sub]
    exact hcoord l
  by_cases hrat : ((c : K)) ∈ Set.range (algebraMap ℤ K)
  · obtain ⟨k, hk⟩ := hrat
    have hk' : ((c : K)) = (k : K) := hk.symm
    have h1 : mahlerCoord l₀ ((c : K)) = (k : ℝ) := by rw [hk']; exact hrealType k
    have h2 : |(k : ℝ)| < 1 := by
      rw [← h1]
      rw [hcK, mahlerCoord_sub]
      exact hcoord₀
    have hk0 : k = 0 := by
      obtain ⟨h3, h4⟩ := abs_lt.mp h2
      have h5 : (-1 : ℤ) < k := by exact_mod_cast h3
      have h6 : k < (1 : ℤ) := by exact_mod_cast h4
      omega
    have hcz : ((c : K)) = 0 := by rw [hk', hk0]; simp
    have hcz' : c = 0 := by
      rw [← NumberField.RingOfIntegers.coe_eq_zero_iff]
      exact hcz
    rw [hc] at hcz'
    exact hne (sub_eq_zero.mp hcz')
  · have h3 : lam ≤ NumberField.house ((c : K)) := hsep c hrat
    obtain ⟨l, hl⟩ := exists_mahlerCoord_ge_half_house ((c : K))
    have h4 : |mahlerCoord l ((c : K))| < max 1 δ := hcabs l
    have h5 : max 1 δ ≤ lam / 2 := by linarith
    have : NumberField.house ((c : K)) < 2 * max 1 δ := by
      calc NumberField.house ((c : K)) ≤ 2 * |mahlerCoord l ((c : K))| := hl
        _ < 2 * max 1 δ := by linarith
    linarith



/-! ### Rounding lemmas -/

lemma abs_intCast_floor_le_add_one (x : ℝ) : |(((⌊x⌋ : ℤ) : ℝ))| ≤ |x| + 1 := by
  have h1 : ((⌊x⌋ : ℤ) : ℝ) ≤ x := Int.floor_le x
  have h2 : x < ((⌊x⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one x
  rw [abs_le]
  constructor <;> linarith [neg_abs_le x, le_abs_self x]

lemma max_one_abs_intCast_floor_le (x : ℝ) : max 1 |(((⌊x⌋ : ℤ) : ℝ))| ≤ 2 * max 1 |x| := by
  have h := abs_intCast_floor_le_add_one x
  rcases le_or_gt |x| 1 with hx | hx
  · rw [max_eq_left hx]
    rw [max_le_iff]
    exact ⟨by norm_num, by linarith⟩
  · calc max 1 |(((⌊x⌋ : ℤ) : ℝ))| ≤ max 1 (|x| + 1) := max_le_max le_rfl h
      _ = |x| + 1 := max_eq_right (by linarith)
      _ ≤ 2 * max 1 |x| := by rw [max_eq_right (le_of_lt hx)]; linarith

lemma max_one_abs_intCast_floor_div_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (x : ℝ) :
    max 1 |(((⌊x / ε⌋ : ℤ) : ℝ))| ≤ 2 * max 1 |x| / ε := by
  have h : max 1 |(((⌊x / ε⌋ : ℤ) : ℝ))| ≤ 2 * max 1 |x / ε| := max_one_abs_intCast_floor_le _
  rw [abs_div, abs_of_pos hε0] at h
  have h2 : max 1 (|x| / ε) ≤ max 1 |x| / ε := by
    rcases le_or_gt (1:ℝ) |x| with hx | hx
    · have hxε : 1 ≤ |x| / ε := by rw [le_div_iff₀ hε0]; nlinarith
      rw [max_eq_right hxε, max_eq_right hx]
    · have hx1 : |x| / ε ≤ 1 / ε := div_le_div_of_nonneg_right (le_of_lt hx) hε0.le
      have h1ε : (1:ℝ) ≤ 1 / ε := by rw [le_div_iff₀ hε0]; linarith
      have hmax : max 1 |x| / ε = 1 / ε := by rw [max_eq_left (le_of_lt hx)]
      rw [hmax]
      exact max_le h1ε hx1
  calc max 1 |(((⌊x / ε⌋ : ℤ) : ℝ))| ≤ 2 * max 1 (|x| / ε) := h
    _ ≤ 2 * (max 1 |x| / ε) := by linarith
    _ = 2 * max 1 |x| / ε := by ring

lemma abs_sub_lt_one_of_floor_eq {x y : ℝ} (h : ⌊x⌋ = ⌊y⌋) : |x - y| < 1 := by
  have h1 : ((⌊x⌋ : ℤ) : ℝ) ≤ x := Int.floor_le x
  have h2 : x < ((⌊x⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one x
  have h3 : ((⌊x⌋ : ℤ) : ℝ) ≤ y := by rw [h]; exact Int.floor_le y
  have h4 : y < ((⌊x⌋ : ℤ) : ℝ) + 1 := by rw [h]; exact Int.lt_floor_add_one y
  rw [abs_sub_lt_iff]
  exact ⟨by linarith, by linarith⟩

lemma abs_sub_lt_of_floor_div_eq {ε : ℝ} (hε : 0 < ε) {x y : ℝ}
    (h : ⌊x / ε⌋ = ⌊y / ε⌋) : |x - y| < ε := by
  have h1 : |x / ε - y / ε| < 1 := abs_sub_lt_one_of_floor_eq h
  have h2 : x / ε - y / ε = (x - y) / ε := by ring
  rw [h2, abs_div, abs_of_pos hε, div_lt_one hε] at h1
  exact h1

lemma max_one_abs_intCast_floor_div_le_of_le {δ : ℝ} (hδ1 : 1 ≤ δ) {x : ℝ} (hx : δ ≤ |x|) :
    max 1 |(((⌊x / δ⌋ : ℤ) : ℝ))| ≤ 2 * max 1 |x| / δ := by
  have hδ0 : 0 < δ := lt_of_lt_of_le one_pos hδ1
  have h1 : |(((⌊x / δ⌋ : ℤ) : ℝ))| ≤ |x| / δ + 1 := by
    have h := abs_intCast_floor_le_add_one (x / δ)
    rwa [abs_div, abs_of_pos hδ0] at h
  have h2 : 1 ≤ |x| / δ := (le_div_iff₀ hδ0).mpr (by linarith)
  have h3 : max 1 |x| = |x| := max_eq_right (by linarith)
  calc max 1 |(((⌊x / δ⌋ : ℤ) : ℝ))| ≤ max 1 (|x| / δ + 1) := max_le_max le_rfl h1
    _ = |x| / δ + 1 := max_eq_right (by linarith)
    _ ≤ 2 * (|x| / δ) := by linarith
    _ = 2 * max 1 |x| / δ := by rw [h3]; ring

lemma max_one_abs_intCast_floor_div_le' {δ : ℝ} (hδ1 : 1 ≤ δ) (x : ℝ) :
    max 1 |(((⌊x / δ⌋ : ℤ) : ℝ))| ≤ max 1 (2 / δ) * max 1 |x| := by
  have hδ0 : 0 < δ := lt_of_lt_of_le one_pos hδ1
  rcases lt_or_ge |x| δ with hx | hx
  · have h2 : |(((⌊x / δ⌋ : ℤ) : ℝ))| ≤ 1 := by
      have h3 : |(((⌊x / δ⌋ : ℤ) : ℝ))| < 2 := by
        have h := abs_intCast_floor_le_add_one (x / δ)
        rw [abs_div, abs_of_pos hδ0] at h
        have hxa : |x| < δ := hx
        have h5 : |x| / δ < 1 := (div_lt_one hδ0).mpr hxa
        linarith
      have h4 : ((|⌊x / δ⌋| : ℤ) : ℝ) < 2 := by
        rw [Int.cast_abs]
        exact h3
      have h4' : |⌊x / δ⌋| < (2 : ℤ) := by exact_mod_cast h4
      have h5 : |⌊x / δ⌋| ≤ 1 := by omega
      exact_mod_cast h5
    rw [max_eq_left h2]
    nlinarith [le_max_left (1:ℝ) (2/δ), le_max_left (1:ℝ) |x|]
  · have h1 : |(((⌊x / δ⌋ : ℤ) : ℝ))| ≤ |x| / δ + 1 := by
      have h := abs_intCast_floor_le_add_one (x / δ)
      rwa [abs_div, abs_of_pos hδ0] at h
    have h2 : |x| / δ + 1 ≤ 2 * (|x| / δ) := by
      have : 1 ≤ |x| / δ := (le_div_iff₀ hδ0).mpr (by linarith)
      linarith
    have h3 : max 1 |x| = |x| := max_eq_right (by linarith)
    calc max 1 |(((⌊x / δ⌋ : ℤ) : ℝ))| ≤ max 1 (|x| / δ + 1) := max_le_max le_rfl h1
      _ = |x| / δ + 1 := max_eq_right (by linarith)
      _ ≤ 2 * (|x| / δ) := h2
      _ = (2 / δ) * |x| := by ring
      _ ≤ max 1 (2 / δ) * max 1 |x| := by
          rw [h3]
          exact mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) (2/δ)) (abs_nonneg x)

/-- **Injectivity of a fine uniform grid**: if all coordinates of `a - b` differ by less than
`ε ≤ 1` with `2ε ≤ lam`, then `a = b`. -/
lemma grid_injective_uniform {lam ε : ℝ} (hε1 : ε ≤ 1) (h2ε : 2 * ε ≤ lam)
    {l₀ : NumberField.mixedEmbedding.index K}
    (hl₀ : ∀ k : ℤ, mahlerCoord l₀ ((k : K)) = (k : ℝ))
    (hsep : ∀ α : NumberField.RingOfIntegers K,
      ((α : K)) ∉ Set.range (algebraMap ℤ K) → lam ≤ NumberField.house ((α : K)))
    {a b : NumberField.RingOfIntegers K}
    (h : ∀ l, |mahlerCoord l ((a : K)) - mahlerCoord l ((b : K))| < ε) : a = b := by
  classical
  by_contra hne
  set c : NumberField.RingOfIntegers K := a - b with hc
  have hcK : ((c : K)) = ((a : K)) - ((b : K)) := by rw [hc]; push_cast; ring
  have hcabs : ∀ l, |mahlerCoord l ((c : K))| < ε := by
    intro l; rw [hcK, mahlerCoord_sub]; exact h l
  by_cases hrat : ((c : K)) ∈ Set.range (algebraMap ℤ K)
  · obtain ⟨k, hk⟩ := Set.mem_range.mp hrat
    have h1 : mahlerCoord l₀ ((c : K)) = (k : ℝ) := by rw [← hk]; exact hl₀ k
    have h2 : |(k : ℝ)| < 1 := by
      rw [← h1, hcK, mahlerCoord_sub]
      exact lt_of_lt_of_le (h l₀) hε1
    have hk0 : k = 0 := by
      obtain ⟨h3, h4⟩ := abs_lt.mp h2
      have h5 : (-1 : ℤ) < k := by exact_mod_cast h3
      have h6 : k < (1 : ℤ) := by exact_mod_cast h4
      omega
    have hcz : ((c : K)) = 0 := by rw [← hk, hk0]; simp
    have hcz' : c = 0 := by
      rw [← NumberField.RingOfIntegers.coe_eq_zero_iff]; exact hcz
    rw [hc] at hcz'
    exact hne (sub_eq_zero.mp hcz')
  · have h3 : lam ≤ NumberField.house ((c : K)) := hsep c hrat
    obtain ⟨l, hl⟩ := exists_mahlerCoord_ge_half_house ((c : K))
    have h4 : |mahlerCoord l ((c : K))| < ε := hcabs l
    have : NumberField.house ((c : K)) < 2 * ε := by linarith
    linarith

/-! ### Finiteness and counting for an arbitrary finite index type -/

lemma finite_setOf_prod_max_one_abs_le {ι : Type*} [Fintype ι] (M : ℝ) :
    ({z : ι → ℤ | (∏ l, max 1 |(((z l : ℤ) : ℝ))|) ≤ M}).Finite := by
  classical
  refine Set.Finite.subset
    (Set.Finite.pi (fun _ : ι => Set.finite_Icc (-(⌈M⌉₊ : ℤ)) (⌈M⌉₊ : ℤ))) ?_
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz
  simp only [Set.mem_univ, Set.mem_pi, true_implies]
  intro l
  have h1 : max 1 |(((z l : ℤ) : ℝ))| ≤ M := by
    have hsub : ({l} : Finset ι) ⊆ Finset.univ := Finset.subset_univ _
    have h2 := Finset.prod_le_prod_of_subset_of_one_le
      (f := fun j : ι => max 1 |(((z j : ℤ) : ℝ))|) hsub
      (fun j _ => by positivity) (fun j _ _ => le_max_left _ _)
    simpa using le_trans h2 hz
  have h3 : |(((z l : ℤ) : ℝ))| ≤ (⌈M⌉₊ : ℝ) :=
    le_trans (le_trans (le_max_right _ _) h1) (Nat.le_ceil M)
  have h4 : |z l| ≤ (⌈M⌉₊ : ℤ) := by
    rw [← Int.cast_le (R := ℝ), Int.cast_abs, Int.cast_natCast]
    exact h3
  rw [Set.mem_Icc]
  exact abs_le.mp h4

lemma ncard_prod_max_one_abs_le_factorial_index {ι : Type*} [Fintype ι] (M : ℝ) (hM : 1 ≤ M) :
    (Nat.card {z : ι → ℤ // (∏ l, max 1 |(((z l : ℤ) : ℝ))|) ≤ M} : ℝ) ≤
      (5:ℝ)^(Fintype.card ι) + (100:ℝ)^(Fintype.card ι) * M *
        (1 + Real.log M)^(Fintype.card ι - 1) /
          (((Fintype.card ι - 1).factorial : ℕ) : ℝ) := by
  classical
  have hmain := Commons.NumberTheory.Counting.ncard_prod_max_one_abs_le_factorial
    (Fintype.card ι) M hM
  set e := Fintype.equivFin ι with he
  have hcard : Nat.card {z : ι → ℤ // (∏ l, max 1 |(((z l : ℤ) : ℝ))|) ≤ M}
      = Nat.card {x : Fin (Fintype.card ι) → ℤ //
          (∏ i, max 1 |(((x i : ℤ) : ℝ))|) ≤ M} := by
    refine Nat.card_congr
      (Equiv.subtypeEquiv (Equiv.arrowCongr e (Equiv.refl ℤ)) ?_)
    intro z
    have hprod : (∏ i : Fin (Fintype.card ι), max 1 |(((z (e.symm i) : ℤ) : ℝ))|)
        = ∏ l : ι, max 1 |(((z l : ℤ) : ℝ))| := by
      rw [Fintype.prod_equiv e.symm
        (fun i : Fin (Fintype.card ι) => max 1 |(((z (e.symm i) : ℤ) : ℝ))|)
        (fun l : ι => max 1 |(((z l : ℤ) : ℝ))|)]
      intro i
      rfl
    show ((∏ l : ι, max 1 |(((z l : ℤ) : ℝ))|) ≤ M) ↔
      ((∏ i : Fin (Fintype.card ι), max 1 |(((z (e.symm i) : ℤ) : ℝ))|) ≤ M)
    rw [hprod]
  rw [hcard]
  exact hmain

/-- The house of an element is at most the product of the place norms appearing in the Mahler
measure. -/
lemma house_le_prod_max_normAtPlace (a : K) :
    NumberField.house a ≤ ∏ w : NumberField.InfinitePlace K,
      (max 1 (NumberField.mixedEmbedding.normAtPlace w
        (NumberField.mixedEmbedding K a))) ^ w.mult := by
  obtain ⟨w₀, -, hw₀⟩ := Finset.exists_max_image Finset.univ
    (fun w : NumberField.InfinitePlace K => w a) Finset.univ_nonempty
  have hhouse : NumberField.house a ≤ w₀ a := by
    have h : ∀ φ : K →+* ℂ, ‖φ a‖ ≤ w₀ a := by
      intro φ
      rw [← NumberField.InfinitePlace.apply]
      exact hw₀ _ (Finset.mem_univ _)
    rw [NumberField.house, NumberField.canonicalEmbedding.norm_le_iff]
    exact h
  have h1 : w₀ a = NumberField.mixedEmbedding.normAtPlace w₀ (NumberField.mixedEmbedding K a) := by
    rw [NumberField.mixedEmbedding.normAtPlace_apply]
  calc NumberField.house a ≤ w₀ a := hhouse
    _ = NumberField.mixedEmbedding.normAtPlace w₀ (NumberField.mixedEmbedding K a) := h1
    _ ≤ max 1 (NumberField.mixedEmbedding.normAtPlace w₀
          (NumberField.mixedEmbedding K a)) := le_max_right _ _
    _ = (max 1 (NumberField.mixedEmbedding.normAtPlace w₀
          (NumberField.mixedEmbedding K a)))^(1:ℕ) := (pow_one _).symm
    _ ≤ (max 1 (NumberField.mixedEmbedding.normAtPlace w₀
          (NumberField.mixedEmbedding K a)))^w₀.mult :=
        pow_le_pow_right₀ (le_max_left _ _)
          (by have := NumberField.InfinitePlace.mult_pos (w := w₀); omega)
    _ ≤ ∏ w : NumberField.InfinitePlace K, (max 1 (NumberField.mixedEmbedding.normAtPlace w
          (NumberField.mixedEmbedding K a)))^w.mult :=
        (by
          have hsub := Finset.prod_le_prod_of_subset_of_one_le
            (s := ({w₀} : Finset (NumberField.InfinitePlace K))) (t := Finset.univ)
            (f := fun w : NumberField.InfinitePlace K =>
              (max 1 (NumberField.mixedEmbedding.normAtPlace w
                (NumberField.mixedEmbedding K a)))^w.mult)
            (Finset.subset_univ _) (fun w _ => by positivity)
            (fun w _ _ => one_le_pow₀ (le_max_left _ _))
          simpa using hsub)

/-- Numerical input for the mixed-grid bound. -/
lemma mahler_coeff_bound (n : ℕ) (hn : 2 ≤ n) {lam : ℝ} (hlam : 4 ≤ lam) :
    2 * (2 / (lam / 4)) * (max 1 (2 / (lam / 4))) ^ (n - 2) ≤ 8 ^ n / lam := by
  have hlam0 : 0 < lam := by linarith
  have hn2 : 1 ≤ n := by omega
  rcases le_or_gt (2 / (lam / 4)) 1 with h | h
  · rw [max_eq_left h, one_pow, mul_one]
    rw [show (2:ℝ) * (2 / (lam / 4)) = 16 / lam from by ring]
    rw [div_le_div_iff₀ hlam0 hlam0]
    have h8 : (16:ℝ) ≤ 8^n := by
      calc (16:ℝ) ≤ 64 := by norm_num
        _ = 8^2 := by norm_num
        _ ≤ 8^n := pow_le_pow_right₀ (by norm_num) hn
    nlinarith [h8, hlam0]
  · rw [max_eq_right (le_of_lt h)]
    have hlt : lam < 8 := by
      have := (one_lt_div (by linarith : (0:ℝ) < lam / 4)).mp h
      linarith
    have h2δ : 2 / (lam / 4) ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    have hpow : (2 / (lam / 4)) ^ (n - 2) ≤ (2:ℝ) ^ (n - 2) :=
      pow_le_pow_left₀ (by positivity) h2δ (n - 2)
    have hstep : 2 * (2 / (lam / 4)) * (2 / (lam / 4)) ^ (n - 2) ≤ 2 * 2 * 2 ^ (n - 2) := by
      calc 2 * (2 / (lam / 4)) * (2 / (lam / 4)) ^ (n - 2)
          ≤ 2 * (2 / (lam / 4)) * 2 ^ (n - 2) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ ≤ 2 * 2 * 2 ^ (n - 2) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            linarith [h2δ]
    have heq : 2 * 2 * (2:ℝ) ^ (n - 2) = 2 ^ n := by
      have : n = (n - 2) + 2 := by omega
      rw [this, pow_add]; norm_num; ring
    have hlam_le : lam ≤ (4:ℝ)^n := by
      have h16 : (16:ℝ) ≤ 4^n := by
        calc (16:ℝ) = 4^2 := by norm_num
          _ ≤ 4^n := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    rw [le_div_iff₀ hlam0]
    calc 2 * (2 / (lam / 4)) * (2 / (lam / 4)) ^ (n - 2) * lam
        ≤ (2 * 2 * 2 ^ (n - 2)) * lam := mul_le_mul_of_nonneg_right hstep (by linarith)
      _ = 2 ^ n * lam := by rw [heq]
      _ ≤ 2 ^ n * 4 ^ n := by exact mul_le_mul_of_nonneg_left hlam_le (by positivity)
      _ = 8 ^ n := by rw [← mul_pow]; norm_num

lemma two_realType_index_tmp (K : Type*) [Field K] [NumberField K]
    (h : NumberField.Units.rank K ≠ 0) :
    ∃ l₀ l₁ : NumberField.mixedEmbedding.index K, l₀ ≠ l₁ ∧
      (∀ k : ℤ, mahlerCoord l₀ ((k : K)) = (k : ℝ)) ∧
      (∀ k : ℤ, mahlerCoord l₁ ((k : K)) = (k : ℝ)) := by
  obtain ⟨l₀, l₁, hne, h0, h1⟩ :=
    Commons.NumberTheory.NumberField.exists_two_stdBasis_coord_intCast (K := K) h
  exact ⟨l₀, l₁, hne, fun k => h0 k, fun k => h1 k⟩

/-- **Counting elements of bounded Mahler measure in a number field.**

Let `K` be a number field with `2 ≤ [K : ℚ] = n`, let `Y ≥ 1`, and let `lam ≥ 1` be such that
every non-rational element of the ring of integers of `K` has house at least `lam` (this holds
e.g. for `lam` the minimum of the houses of the non-rational integral elements).  Then the number
of non-rational algebraic integers `α` whose "Mahler measure"
`∏_w (max 1 |α|_w) ^ w.mult` is at most `Y` is at most
`100000 ^ n * Y * (1 + log Y) ^ (n - 1) / lam`.

This is (a version of) Theorem 2.1 of Lemke Oliver--Thorne, *Upper bounds on polynomials with
small Galois group*, Mathematika 66 (2020), 1054--1059, and is the key counting input in
Bhargava's proof of van der Waerden's Conjecture.

# Proof plan (for whoever finishes this)

Write `n = finrank ℚ K`, `δ = lam / 4`, and let `T` be the set being counted.  Fix a "real type"
coordinate `l₀` of the mixed space (`exists_realType_index`), i.e. a coordinate for which the
coordinate of the rational integer `k` is `k` itself (as opposed to the imaginary-part
coordinates, where an integer has coordinate `0`).

* `prod_max_one_mahlerCoord_le`: the product of `max 1 |coord l ·|` over all coordinates is at most
  the Mahler measure `∏_w (max 1 |·|_w) ^ w.mult`; combined with `house_le_two_mahlerCoord`
  (`exists_mahlerCoord_ge_half_house`) this relates the coordinate box to the house.
* `grid_injective`: if all coordinates of `a - b` are `< max 1 δ` and the `l₀`-coordinate is
  `< 1`, then `a = b`.

**Case `lam ≤ 2`.**  Grid every coordinate at scale `δ ≤ 1/2`:
`z_l = ⌊coord l α / δ⌋`.  The map `α ↦ z` is injective by `grid_injective`, and
`∏_l max 1 |z_l| ≤ δ^{-n} * M(α) ≤ 4^n Y / lam` (because `max 1 (x/δ) ≤ max 1 x / δ` for
`δ ≤ 1`).  Apply `ncard_prod_max_one_abs_le_factorial` (after reindexing `index K ≃ Fin n`) to
conclude.

**Case `lam > 2`.**  Decompose `T` by the set `S(α) = {l | 1 ≤ |coord l α|}`; there are `2^n`
classes.  Within a class use the grid `z_{l₀} = ⌊coord l₀ α⌋` (scale `1`) and, for `l ≠ l₀`,
`z_l = ⌊coord l α / δ⌋` if `l ∈ S(α)`, `z_l = ⌊coord l α⌋` otherwise.
`grid_injective` gives injectivity of `α ↦ z` (differences are `< 1` at `l₀` and
`< max 1 δ` elsewhere, and `2 max 1 δ ≤ lam`).  For `l ∈ S(α) \ {l₀}` one has
`max 1 |z_l| ≤ max 1 |coord l α| / δ`, for `l ∉ S(α)` one has `max 1 |z_l| ≤ max 1 |coord l α|`,
so `∏_l max 1 |z_l| ≤ δ^{-|S(α) \ {l₀}|} * M(α)`, giving the gain `4/lam` as long as
`S(α) ≠ {l₀}`; then apply the counting lemma again (here `M ≤ max 4^{n-1} Y / lam`).

The remaining class `S(α) = {l₀}` is handled by a *separation* argument: such `α` have all
coordinates but the `l₀` one in `[0,1)`, hence two of them are congruent modulo `ℤ` only if
equal, and any two distinct ones have house `≥ lam`, which forces their `l₀`-coordinates to differ
by at least `lam/2`; since those coordinates lie in `[-Y,Y]` the class has at most `4Y/lam + 1`
elements.

Finally sum the `2^n` classes and estimate the resulting expression, using
`Real.log (max 1 (4/lam) ^ n * Y) ≤ Real.log Y + n * Real.log 4` and
`lam ≤ 100000 ^ n * (1 + Real.log Y) ^ (n - 1)` (the latter because a nonempty `T` gives
`lam ≤ Y`, and `(1 + log Y) ≥ 1`). -/
theorem ncard_max_normAtPlace_le {K : Type*} [Field K] [NumberField K]
    (hn : 2 ≤ Module.finrank ℚ K) (Y lam : ℝ) (hY : 1 ≤ Y) (hlam : 1 ≤ lam)
    (hsep : ∀ α : NumberField.RingOfIntegers K, ((α : K)) ∉ Set.range (algebraMap ℤ K) →
      lam ≤ NumberField.house ((α : K))) :
    (Nat.card {α : NumberField.RingOfIntegers K // ((α : K)) ∉ Set.range (algebraMap ℤ K) ∧
        (∏ w : NumberField.InfinitePlace K,
            (max 1 (NumberField.mixedEmbedding.normAtPlace w
              (NumberField.mixedEmbedding K ((α : K))))) ^ w.mult) ≤ Y} : ℝ) ≤
      (100000 : ℝ) ^ Module.finrank ℚ K * Y *
        (1 + Real.log Y) ^ (Module.finrank ℚ K - 1) / lam := by
  classical
  set n := Module.finrank ℚ K with hn_def
  set F : NumberField.RingOfIntegers K → ℝ := fun α => ∏ w : NumberField.InfinitePlace K,
      (max 1 (NumberField.mixedEmbedding.normAtPlace w
        (NumberField.mixedEmbedding K ((α : K))))) ^ w.mult with hF
  have hn1 : 1 ≤ n := by rw [hn_def]; exact le_trans (by norm_num) hn
  let T := {α : NumberField.RingOfIntegers K // ((α : K)) ∈ (Set.range (algebraMap ℤ K))ᶜ ∧ F α ≤ Y}
  change (Nat.card T : ℝ) ≤ (100000 : ℝ) ^ n * Y * (1 + Real.log Y) ^ (n - 1) / lam
  by_cases hsmall : lam ≤ 4
  · -- CASE A: `lam ≤ 4`
    set ε : ℝ := lam / 4 with hεdef
    have hε0 : 0 < ε := by rw [hεdef]; linarith
    have hε1 : ε ≤ 1 := by rw [hεdef]; linarith
    have h2ε : 2 * ε ≤ lam := by rw [hεdef]; linarith
    obtain ⟨l₀, hl₀⟩ := exists_realType_index K
    obtain ⟨e, -⟩ : ∃ e : NumberField.mixedEmbedding.index K ≃ Fin n, True :=
      ⟨Fintype.equivFinOfCardEq (by rw [card_mixedEmbedding_index, hn_def]), trivial⟩
    let Φ : T → (Fin n → ℤ) := fun α i => ⌊mahlerCoord (e.symm i) ((α.1 : K)) / ε⌋
    have hΦ_inj : Function.Injective Φ := by
      intro a b hab
      refine Subtype.ext ?_
      refine grid_injective_uniform hε1 h2ε hl₀ hsep ?_
      intro l
      have h := congrFun hab (e l)
      simp only [Φ, Equiv.symm_apply_apply] at h
      exact abs_sub_lt_of_floor_div_eq hε0 h
    have hΦ_bound : ∀ α : T, (∏ i : Fin n, max 1 |(((Φ α i : ℤ) : ℝ))|) ≤ (8:ℝ)^n * Y / lam := by
      intro α
      have hreindex : (∏ i : Fin n, max 1 |(((Φ α i : ℤ) : ℝ))|)
          = ∏ l : NumberField.mixedEmbedding.index K,
              max 1 |(((⌊mahlerCoord l ((α.1 : K)) / ε⌋ : ℤ) : ℝ))| := by
        rw [Fintype.prod_equiv e.symm (fun i : Fin n => max 1 |(((Φ α i : ℤ) : ℝ))|)
          (fun l : NumberField.mixedEmbedding.index K =>
            max 1 |(((⌊mahlerCoord l ((α.1 : K)) / ε⌋ : ℤ) : ℝ))|)]
        intro i
        simp only [Φ, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
      rw [hreindex]
      have hY' : (∏ l : NumberField.mixedEmbedding.index K, max 1 |mahlerCoord l ((α.1 : K))|) ≤ Y :=
        (prod_max_one_mahlerCoord_le _).trans α.2.2
      calc (∏ l : NumberField.mixedEmbedding.index K,
              max 1 |(((⌊mahlerCoord l ((α.1 : K)) / ε⌋ : ℤ) : ℝ))|)
          ≤ ∏ l : NumberField.mixedEmbedding.index K,
              ((2 / ε) * max 1 |mahlerCoord l ((α.1 : K))|) := by
            apply Finset.prod_le_prod
            · intro l _; positivity
            · intro l _
              have h := max_one_abs_intCast_floor_div_le hε0 hε1 (mahlerCoord l ((α.1 : K)))
              have h2 : 2 * max 1 |mahlerCoord l ((α.1 : K))| / ε
                  = (2/ε) * max 1 |mahlerCoord l ((α.1 : K))| := by ring
              linarith
        _ = (2/ε) ^ (Fintype.card (NumberField.mixedEmbedding.index K)) *
              (∏ l, max 1 |mahlerCoord l ((α.1 : K))|) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
        _ ≤ (2/ε) ^ n * Y := by
            rw [card_mixedEmbedding_index, hn_def]
            gcongr
        _ = (8/lam)^n * Y := by
            rw [hεdef]
            congr 1
            ring
        _ ≤ 8^n * Y / lam := by
            rw [div_pow, div_mul_eq_mul_div]
            exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by
              calc lam = lam^1 := (pow_one lam).symm
                _ ≤ lam^n := pow_le_pow_right₀ hlam hn1)
    have hM1 : (1:ℝ) ≤ (8:ℝ)^n * Y / lam := by
      rw [le_div_iff₀ (by linarith)]
      have h8 : (8:ℝ) ≤ 8^n := by
        calc (8:ℝ) = 8^1 := (pow_one 8).symm
          _ ≤ 8^n := pow_le_pow_right₀ (by norm_num) hn1
      nlinarith [hY, hsmall]
    haveI : Finite {z : Fin n → ℤ // (∏ i, max 1 |(((z i : ℤ) : ℝ))|) ≤ (8:ℝ)^n * Y / lam} :=
      (finite_setOf_prod_max_one_abs_le ((8:ℝ)^n * Y / lam)).to_subtype
    have hcard : Nat.card T ≤
        Nat.card {z : Fin n → ℤ // (∏ i, max 1 |(((z i : ℤ) : ℝ))|) ≤ (8:ℝ)^n * Y / lam} :=
      Nat.card_le_card_of_injective (fun α : T => ⟨Φ α, hΦ_bound α⟩)
        (fun a b h => hΦ_inj (Subtype.ext_iff.mp h))
    have hcount := ncard_prod_max_one_abs_le_factorial_index (ι := Fin n) ((8:ℝ)^n * Y / lam) hM1
    have hcount' : (Nat.card {z : Fin n → ℤ //
          (∏ i, max 1 |(((z i : ℤ) : ℝ))|) ≤ (8:ℝ)^n * Y / lam} : ℝ) ≤
        (5:ℝ)^n + (100:ℝ)^n * ((8:ℝ)^n * Y / lam) *
          (1 + Real.log ((8:ℝ)^n * Y / lam))^(n-1) / (((n-1).factorial : ℕ) : ℝ) := by
      simpa using hcount
    calc (Nat.card T : ℝ)
        ≤ (Nat.card {z : Fin n → ℤ //
            (∏ i, max 1 |(((z i : ℤ) : ℝ))|) ≤ (8:ℝ)^n * Y / lam} : ℝ) := by
          exact_mod_cast hcard
      _ ≤ (5:ℝ)^n + (100:ℝ)^n * ((8:ℝ)^n * Y / lam) *
          (1 + Real.log ((8:ℝ)^n * Y / lam))^(n-1) / (((n-1).factorial : ℕ) : ℝ) := hcount'
      _ ≤ (100000:ℝ)^n * Y * (1 + Real.log Y)^(n-1) / lam :=
          Commons.Analysis.SpecialFunctions.mahler_arith_small_lam n hn Y lam hY hlam hsmall
  · push_neg at hsmall
    have h4lam : 4 ≤ lam := le_of_lt hsmall
    by_cases hrank : NumberField.Units.rank K = 0
    · -- CASE B1: `lam ≥ 4` and the unit rank is `0` (imaginary quadratic)
      have hcard_places : Fintype.card (NumberField.InfinitePlace K) = 1 := by
        have h1 : NumberField.InfinitePlace.nrRealPlaces K +
            NumberField.InfinitePlace.nrComplexPlaces K - 1 = NumberField.Units.rank K :=
          units_rank_eq_nrRealPlaces_add_nrComplexPlaces_sub_one K
        have h3 : NumberField.InfinitePlace.nrRealPlaces K +
            2 * NumberField.InfinitePlace.nrComplexPlaces K = Module.finrank ℚ K :=
          NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
        have h4 : NumberField.InfinitePlace.nrRealPlaces K +
            NumberField.InfinitePlace.nrComplexPlaces K = 1 := by omega
        rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, h4]
      have huniq : ∀ w w' : NumberField.InfinitePlace K, w = w' :=
        Fintype.card_le_one_iff.mp (le_of_eq hcard_places)
      have hpred : ∀ α : NumberField.RingOfIntegers K, (F α ≤ Y) ↔
          ((∏ w : NumberField.InfinitePlace K,
            (NumberField.mixedEmbedding.normAtPlace w
              (NumberField.mixedEmbedding K ((α : K)))) ^ w.mult) ≤ Y) := by
        intro α
        obtain ⟨w₀⟩ : Nonempty (NumberField.InfinitePlace K) := inferInstance
        set x := NumberField.mixedEmbedding.normAtPlace w₀
          (NumberField.mixedEmbedding K ((α : K))) with hx
        have hx0 : 0 ≤ x := by
          rw [hx]
          exact NumberField.mixedEmbedding.normAtPlace_nonneg w₀ _
        have h1 : F α = (max 1 x) ^ w₀.mult := by
          rw [hF]
          exact Fintype.prod_eq_single w₀ (fun w hw => absurd (huniq w w₀) hw)
        have h2 : (∏ w : NumberField.InfinitePlace K,
            (NumberField.mixedEmbedding.normAtPlace w
              (NumberField.mixedEmbedding K ((α : K)))) ^ w.mult) = x ^ w₀.mult := by
          exact Fintype.prod_eq_single w₀ (fun w hw => absurd (huniq w w₀) hw)
        rw [h1, h2]
        constructor
        · intro h
          calc x ^ w₀.mult ≤ (max 1 x) ^ w₀.mult :=
                pow_le_pow_left₀ hx0 (le_max_right (1:ℝ) x) w₀.mult
            _ ≤ Y := h
        · intro h
          rcases le_or_gt x 1 with hx1 | hx1
          · rw [max_eq_left hx1, one_pow]; exact hY
          · rw [max_eq_right (le_of_lt hx1)]; exact h
      refine le_trans ?_ (ncard_mahler_le hn Y lam hY hlam hsep)
      have hsame : Nat.card T = Nat.card {α : NumberField.RingOfIntegers K //
          ((α : K)) ∉ Set.range (algebraMap ℤ K) ∧
          (∏ w : NumberField.InfinitePlace K,
            (NumberField.mixedEmbedding.normAtPlace w
              (NumberField.mixedEmbedding K ((α : K)))) ^ w.mult) ≤ Y} := by
        apply Nat.card_congr
        exact Equiv.subtypeEquivRight (fun α => and_congr_right (fun _ => hpred α))
      rw [hsame]
    · -- CASE B2: `lam ≥ 4` and the unit rank is positive
      obtain ⟨l₀, l₁, hl₀₁, hl₀, hl₁⟩ := two_realType_index_tmp K hrank
      set δ : ℝ := lam / 4 with hδdef
      have hδ0 : 0 < δ := by rw [hδdef]; linarith
      have hδ1 : 1 ≤ δ := by rw [hδdef]; linarith
      have hδ2 : 2 * max 1 δ ≤ lam := by
        rw [hδdef]
        have h1 : (1:ℝ) ≤ lam / 2 := by linarith
        have h2 : lam / 4 ≤ lam / 2 := by linarith
        have h3 : max 1 (lam / 4) ≤ lam / 2 := max_le h1 h2
        linarith
      by_cases hT : Nonempty T
      · obtain ⟨α₀⟩ := hT
        have hlamY : lam ≤ Y := by
          have h1 : NumberField.house ((α₀.1 : K)) ≤ F α₀ :=
            house_le_prod_max_normAtPlace (α₀.1 : K)
          have h2 := hsep α₀.1 α₀.2.1
          linarith [h1, α₀.2.2]
        obtain ⟨e, -⟩ : ∃ e : NumberField.mixedEmbedding.index K ≃ Fin n, True :=
          ⟨Fintype.equivFinOfCardEq (by rw [card_mixedEmbedding_index, hn_def]), trivial⟩
        let Φ : T → (Fin n → ℤ) := fun α i =>
          ⌊mahlerCoord (e.symm i) ((α.1 : K)) / (if e.symm i = l₀ then 1 else δ)⌋
        let p : T → Prop := fun α => ∃ l ∈ Finset.univ.erase l₀, δ ≤ |mahlerCoord l ((α.1 : K))|
        let pair : T → (Fin 2 → ℤ) := fun α =>
          ![⌊mahlerCoord l₀ ((α.1 : K)) / δ⌋, ⌊mahlerCoord l₁ ((α.1 : K))⌋]
        have hΦ_inj : Function.Injective Φ := by
          intro a b hab
          refine Subtype.ext ?_
          refine grid_injective hl₀ hδ2 hsep ?_ ?_
          · have h := congrFun hab (e l₀)
            have h' : ⌊mahlerCoord l₀ ((a.1 : K)) / (if l₀ = l₀ then (1:ℝ) else δ)⌋ =
                ⌊mahlerCoord l₀ ((b.1 : K)) / (if l₀ = l₀ then (1:ℝ) else δ)⌋ := by
              simpa only [Φ, Equiv.symm_apply_apply] using h
            rw [if_pos rfl] at h'
            exact abs_sub_lt_of_floor_div_eq one_pos h'
          · intro l
            rw [max_eq_right hδ1]
            by_cases hl : l = l₀
            · subst hl
              have h := congrFun hab (e l)
              have h' : ⌊mahlerCoord l ((a.1 : K)) / (if l = l then (1:ℝ) else δ)⌋ =
                  ⌊mahlerCoord l ((b.1 : K)) / (if l = l then (1:ℝ) else δ)⌋ := by
                simpa only [Φ, Equiv.symm_apply_apply] using h
              rw [if_pos rfl] at h'
              have := abs_sub_lt_of_floor_div_eq one_pos h'
              linarith
            · have h := congrFun hab (e l)
              have h' : ⌊mahlerCoord l ((a.1 : K)) / (if l = l₀ then (1:ℝ) else δ)⌋ =
                  ⌊mahlerCoord l ((b.1 : K)) / (if l = l₀ then (1:ℝ) else δ)⌋ := by
                simpa only [Φ, Equiv.symm_apply_apply] using h
              rw [if_neg hl] at h'
              exact abs_sub_lt_of_floor_div_eq hδ0 h'
        have hΦ_bound : ∀ α : T, p α →
            (∏ i : Fin n, max 1 |(((Φ α i : ℤ) : ℝ))|) ≤ (8:ℝ)^n * Y / lam := by
          intro α hp
          obtain ⟨lstar, hlstarmem, hlstarδ⟩ := hp
          have hlstarne : lstar ≠ l₀ := (Finset.mem_erase.mp hlstarmem).1
          have hreindex : (∏ i : Fin n, max 1 |(((Φ α i : ℤ) : ℝ))|)
              = ∏ l : NumberField.mixedEmbedding.index K,
                  max 1 |(((⌊mahlerCoord l ((α.1 : K)) /
                    (if l = l₀ then (1:ℝ) else δ)⌋ : ℤ) : ℝ))| := by
            rw [Fintype.prod_equiv e.symm (fun i : Fin n => max 1 |(((Φ α i : ℤ) : ℝ))|)
              (fun l : NumberField.mixedEmbedding.index K =>
                max 1 |(((⌊mahlerCoord l ((α.1 : K)) /
                  (if l = l₀ then (1:ℝ) else δ)⌋ : ℤ) : ℝ))|)]
            intro i
            simp only [Φ, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
          rw [hreindex]
          have hY' : (∏ l : NumberField.mixedEmbedding.index K,
              max 1 |mahlerCoord l ((α.1 : K))|) ≤ Y :=
            (prod_max_one_mahlerCoord_le _).trans α.2.2
          have hpt : ∀ l : NumberField.mixedEmbedding.index K,
              max 1 |(((⌊mahlerCoord l ((α.1 : K)) / (if l = l₀ then (1:ℝ) else δ)⌋ : ℤ) : ℝ))|
              ≤ (if l = l₀ then (2:ℝ) else (if l = lstar then 2 / δ else max 1 (2 / δ))) *
                max 1 |mahlerCoord l ((α.1 : K))| := by
            intro l
            by_cases h0 : l = l₀
            · subst h0
              rw [if_pos rfl, if_pos rfl]
              simpa using max_one_abs_intCast_floor_le (mahlerCoord l ((α.1 : K)))
            · rw [if_neg h0, if_neg h0]
              by_cases h1 : l = lstar
              · subst h1
                rw [if_pos rfl]
                have h := max_one_abs_intCast_floor_div_le_of_le hδ1 hlstarδ
                have h2 : 2 * max 1 |mahlerCoord l ((α.1 : K))| / δ
                    = (2 / δ) * max 1 |mahlerCoord l ((α.1 : K))| := by ring
                linarith [h]
              · rw [if_neg h1]
                exact max_one_abs_intCast_floor_div_le' hδ1 _
          have hcoef : (∏ l : NumberField.mixedEmbedding.index K,
              (if l = l₀ then (2:ℝ) else (if l = lstar then 2 / δ else max 1 (2 / δ))))
              = 2 * (2 / δ) * (max 1 (2 / δ)) ^ (((Finset.univ.erase l₀).erase lstar).card) := by
            rw [← Finset.mul_prod_erase Finset.univ
              (fun l : NumberField.mixedEmbedding.index K =>
                if l = l₀ then (2:ℝ) else (if l = lstar then 2 / δ else max 1 (2 / δ)))
              (Finset.mem_univ l₀), if_pos rfl]
            have h2 : (∏ x ∈ Finset.univ.erase l₀,
                (if x = l₀ then (2:ℝ) else (if x = lstar then 2 / δ else max 1 (2 / δ))))
                = (2 / δ) * (max 1 (2 / δ)) ^ ((Finset.univ.erase l₀).erase lstar).card := by
              rw [← Finset.mul_prod_erase (Finset.univ.erase l₀)
                (fun x : NumberField.mixedEmbedding.index K =>
                  if x = l₀ then (2:ℝ) else (if x = lstar then 2 / δ else max 1 (2 / δ)))
                (Finset.mem_erase.mpr ⟨hlstarne, Finset.mem_univ lstar⟩),
                if_neg hlstarne, if_pos rfl]
              congr 1
              rw [Finset.prod_congr rfl (fun x hx => ?_), Finset.prod_const]
              rw [if_neg (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1,
                if_neg (Finset.mem_erase.mp hx).1]
            rw [h2]
            ring
          have hcard2 : ((Finset.univ.erase l₀).erase lstar).card = n - 2 := by
            rw [Finset.card_erase_of_mem (a := lstar)
              (Finset.mem_erase.mpr ⟨hlstarne, Finset.mem_univ lstar⟩)]
            rw [Finset.card_erase_of_mem (a := l₀) (Finset.mem_univ l₀), Finset.card_univ,
              card_mixedEmbedding_index, hn_def]
            omega
          calc (∏ l : NumberField.mixedEmbedding.index K,
                  max 1 |(((⌊mahlerCoord l ((α.1 : K)) / (if l = l₀ then (1:ℝ) else δ)⌋ : ℤ) : ℝ))|)
              ≤ ∏ l : NumberField.mixedEmbedding.index K,
                  ((if l = l₀ then (2:ℝ) else (if l = lstar then 2 / δ else max 1 (2 / δ))) *
                    max 1 |mahlerCoord l ((α.1 : K))|) :=
                Finset.prod_le_prod (fun l _ => by positivity) (fun l _ => hpt l)
            _ = (∏ l : NumberField.mixedEmbedding.index K,
                  (if l = l₀ then (2:ℝ) else (if l = lstar then 2 / δ else max 1 (2 / δ)))) *
                  (∏ l, max 1 |mahlerCoord l ((α.1 : K))|) := by
                rw [Finset.prod_mul_distrib]
            _ = (2 * (2 / δ) * (max 1 (2 / δ)) ^ (n - 2)) *
                  (∏ l, max 1 |mahlerCoord l ((α.1 : K))|) := by rw [hcoef, hcard2]
            _ ≤ (2 * (2 / δ) * (max 1 (2 / δ)) ^ (n - 2)) * Y :=
                mul_le_mul_of_nonneg_left hY' (by positivity)
            _ ≤ 8^n * Y / lam := by
                have hc := mahler_coeff_bound n hn h4lam
                rw [hδdef]
                calc (2 * (2 / (lam / 4)) * (max 1 (2 / (lam / 4))) ^ (n - 2)) * Y
                    ≤ (8^n / lam) * Y := mul_le_mul_of_nonneg_right hc (by linarith)
                  _ = 8^n * Y / lam := by ring
        have hsmall : ∀ α : T, ¬ p α → ∀ l ≠ l₀, |mahlerCoord l ((α.1 : K))| < δ := by
          intro α hα l hl
          by_contra hcon
          exact hα ⟨l, Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩, not_lt.mp hcon⟩
        have hpair_inj : ∀ a b : T, ¬ p a → ¬ p b → pair a = pair b → a = b := by
          intro a b hpa hpb hab
          refine Subtype.ext ?_
          by_contra hne
          set c : NumberField.RingOfIntegers K := a.1 - b.1 with hc
          have hcK : ((c : K)) = ((a.1 : K)) - ((b.1 : K)) := by rw [hc]; push_cast; ring
          have h0 : |mahlerCoord l₀ ((a.1 : K)) - mahlerCoord l₀ ((b.1 : K))| < δ := by
            have h := congrFun hab (0 : Fin 2)
            simp only [pair] at h
            exact abs_sub_lt_of_floor_div_eq hδ0 h
          have h1 : |mahlerCoord l₁ ((a.1 : K)) - mahlerCoord l₁ ((b.1 : K))| < 1 := by
            have h := congrFun hab (1 : Fin 2)
            simp only [pair] at h
            exact abs_sub_lt_one_of_floor_eq h
          have hcoord : ∀ l, |mahlerCoord l ((c : K))| < 2 * δ := by
            intro l
            rw [hcK, mahlerCoord_sub]
            rcases eq_or_ne l l₀ with rfl | hl
            · linarith [h0, hδ0]
            · have ha := hsmall a hpa l hl
              have hb := hsmall b hpb l hl
              have hle : |mahlerCoord l ((a.1 : K)) - mahlerCoord l ((b.1 : K))| ≤
                  |mahlerCoord l ((a.1 : K))| + |mahlerCoord l ((b.1 : K))| := by
                refine abs_le.mpr ⟨?_, ?_⟩ <;>
                  linarith [neg_abs_le (mahlerCoord l ((a.1 : K))),
                    neg_abs_le (mahlerCoord l ((b.1 : K))),
                    le_abs_self (mahlerCoord l ((a.1 : K))),
                    le_abs_self (mahlerCoord l ((b.1 : K)))]
              linarith
          have hhouse : NumberField.house ((c : K)) < lam := by
            obtain ⟨l, hl⟩ := exists_mahlerCoord_ge_half_house ((c : K))
            have := hcoord l
            linarith [hδdef]
          have hrat : ((c : K)) ∈ Set.range (algebraMap ℤ K) := by
            by_contra hcon
            exact absurd (hsep c hcon) (not_le.mpr hhouse)
          obtain ⟨k, hk⟩ := Set.mem_range.mp hrat
          have hk' : ((c : K)) = (k : K) := hk.symm
          have hkk : ((k : ℝ)) = mahlerCoord l₁ ((c : K)) := by rw [hk']; exact (hl₁ k).symm
          have hklt : |(k : ℝ)| < 1 := by
            rw [hkk, hcK, mahlerCoord_sub]
            exact h1
          have hk0 : k = 0 := by
            obtain ⟨h3, h4⟩ := abs_lt.mp hklt
            have h5 : (-1 : ℤ) < k := by exact_mod_cast h3
            have h6 : k < (1 : ℤ) := by exact_mod_cast h4
            omega
          have hcz : ((c : K)) = 0 := by rw [hk', hk0]; simp
          have hcz' : c = 0 := by
            rw [← NumberField.RingOfIntegers.coe_eq_zero_iff]
            exact hcz
          rw [hc] at hcz'
          exact hne (sub_eq_zero.mp hcz')
        have hpair_bound : ∀ α : T, ¬ p α →
            (∏ i : Fin 2, max 1 |(((pair α i : ℤ) : ℝ))|) ≤ 16 * Y / lam := by
          intro α hpa
          have hge : 2 * δ ≤ |mahlerCoord l₀ ((α.1 : K))| := by
            obtain ⟨l, hl⟩ := exists_mahlerCoord_ge_half_house ((α.1 : K))
            have hlam := hsep α.1 α.2.1
            have h2d : (2:ℝ) * δ = lam / 2 := by rw [hδdef]; ring
            have hl0 : l = l₀ := by
              by_contra hl'
              have hlt := hsmall α hpa l hl'
              linarith
            subst hl0
            linarith [hl, h2d]
          have hM : max 1 |mahlerCoord l₀ ((α.1 : K))| * max 1 |mahlerCoord l₁ ((α.1 : K))| ≤ Y := by
            have hprod := prod_max_one_mahlerCoord_le ((α.1 : K))
            have hsub := Finset.prod_le_prod_of_subset_of_one_le
              (s := ({l₀, l₁} : Finset (NumberField.mixedEmbedding.index K))) (t := Finset.univ)
              (f := fun l => max 1 |mahlerCoord l ((α.1 : K))|)
              (Finset.subset_univ _) (fun l _ => by positivity)
              (fun l _ _ => le_max_left _ _)
            have h2 : (∏ l ∈ ({l₀, l₁} : Finset (NumberField.mixedEmbedding.index K)),
                max 1 |mahlerCoord l ((α.1 : K))|)
                = max 1 |mahlerCoord l₀ ((α.1 : K))| * max 1 |mahlerCoord l₁ ((α.1 : K))| := by
              rw [Finset.prod_insert (by simp [hl₀₁]), Finset.prod_singleton]
            rw [h2] at hsub
            linarith [hsub, hprod, α.2.2]
          have hx1 : (1:ℝ) ≤ |mahlerCoord l₀ ((α.1 : K))| := by linarith [hge, hδ1]
          have hm0 : max 1 |mahlerCoord l₀ ((α.1 : K))| = |mahlerCoord l₀ ((α.1 : K))| := max_eq_right hx1
          have hle₁ : max 1 |mahlerCoord l₁ ((α.1 : K))| ≤ Y / |mahlerCoord l₀ ((α.1 : K))| := by
            rw [hm0] at hM
            rw [le_div_iff₀ (by linarith)]
            linarith [hM]
          rw [Fin.prod_univ_two]
          simp only [pair]
          have hb0 := max_one_abs_intCast_floor_div_le_of_le hδ1 (le_trans (by linarith : δ ≤ 2 * δ) hge)
          have hb1 := max_one_abs_intCast_floor_le (mahlerCoord l₁ ((α.1 : K)))
          have hxne : |mahlerCoord l₀ ((α.1 : K))| ≠ 0 := by linarith [hge, hδ0]
          have hlne : lam ≠ 0 := by linarith
          calc max 1 |(((⌊mahlerCoord l₀ ((α.1 : K)) / δ⌋ : ℤ) : ℝ))| *
                max 1 |(((⌊mahlerCoord l₁ ((α.1 : K))⌋ : ℤ) : ℝ))|
              ≤ (2 * max 1 |mahlerCoord l₀ ((α.1 : K))| / δ) *
                (2 * max 1 |mahlerCoord l₁ ((α.1 : K))|) :=
                mul_le_mul hb0 hb1 (by positivity) (by positivity)
            _ ≤ (2 * max 1 |mahlerCoord l₀ ((α.1 : K))| / δ) *
                (2 * (Y / |mahlerCoord l₀ ((α.1 : K))|)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                linarith [hle₁]
            _ = 16 * Y / lam := by
                rw [hm0, hδdef]
                field_simp
                ring
        have hfinA : Finite {z : Fin n → ℤ //
            (∏ i, max 1 |(((z i : ℤ) : ℝ))|) ≤ (8:ℝ)^n * Y / lam} :=
          (finite_setOf_prod_max_one_abs_le ((8:ℝ)^n * Y / lam)).to_subtype
        have hfinB : Finite {z : Fin 2 → ℤ //
            (∏ i, max 1 |(((z i : ℤ) : ℝ))|) ≤ 16 * Y / lam} :=
          (finite_setOf_prod_max_one_abs_le (16 * Y / lam)).to_subtype
        haveI := hfinA
        haveI := hfinB
        let Ψ : T → ({z : Fin n → ℤ //
              (∏ i, max 1 |(((z i : ℤ) : ℝ))|) ≤ (8:ℝ)^n * Y / lam}) ⊕
            ({z : Fin 2 → ℤ // (∏ i, max 1 |(((z i : ℤ) : ℝ))|) ≤ 16 * Y / lam}) :=
          fun α => if hp : p α then Sum.inl ⟨Φ α, hΦ_bound α hp⟩
            else Sum.inr ⟨pair α, hpair_bound α hp⟩
        have hΨ_inj : Function.Injective Ψ := by
          intro a b hab
          by_cases ha : p a
          · by_cases hb : p b
            · have h : Φ a = Φ b := by
                have hh := hab
                simp only [Ψ, dif_pos ha, dif_pos hb] at hh
                exact Subtype.ext_iff.mp (Sum.inl.inj hh)
              exact hΦ_inj h
            · have hh := hab
              simp only [Ψ, dif_pos ha, dif_neg hb] at hh
              exact absurd hh (fun hcon => by cases hcon)
          · by_cases hb : p b
            · have hh := hab
              simp only [Ψ, dif_neg ha, dif_pos hb] at hh
              exact absurd hh (fun hcon => by cases hcon)
            · have h : pair a = pair b := by
                have hh := hab
                simp only [Ψ, dif_neg ha, dif_neg hb] at hh
                exact Subtype.ext_iff.mp (Sum.inr.inj hh)
              exact hpair_inj a b ha hb h
        have hsplit : Nat.card T ≤ Nat.card {z : Fin n → ℤ //
              (∏ i, max 1 |(((z i : ℤ) : ℝ))|) ≤ (8:ℝ)^n * Y / lam} +
            Nat.card {z : Fin 2 → ℤ //
              (∏ i, max 1 |(((z i : ℤ) : ℝ))|) ≤ 16 * Y / lam} := by
          have h := Nat.card_le_card_of_injective Ψ hΨ_inj
          rwa [Nat.card_sum] at h
        have hMA : (1:ℝ) ≤ (8:ℝ)^n * Y / lam := by
          rw [le_div_iff₀ (by linarith)]
          have h8 : (8:ℝ) ≤ 8^n := by
            calc (8:ℝ) = 8^1 := (pow_one 8).symm
              _ ≤ 8^n := pow_le_pow_right₀ (by norm_num) hn1
          nlinarith [hlamY]
        have hMB : (1:ℝ) ≤ 16 * Y / lam := by
          rw [le_div_iff₀ (by linarith)]
          linarith [hlamY, h4lam]
        have hcotA := ncard_prod_max_one_abs_le_factorial_index (ι := Fin n)
          ((8:ℝ)^n * Y / lam) hMA
        have hcotB := ncard_prod_max_one_abs_le_factorial_index (ι := Fin 2)
          (16 * Y / lam) hMB
        have hcotA' : (Nat.card {z : Fin n → ℤ //
              (∏ i, max 1 |(((z i : ℤ) : ℝ))|) ≤ (8:ℝ)^n * Y / lam} : ℝ) ≤
            (5:ℝ)^n + (100:ℝ)^n * ((8:ℝ)^n * Y / lam) *
              (1 + Real.log ((8:ℝ)^n * Y / lam))^(n-1) / (((n-1).factorial : ℕ) : ℝ) := by
          simpa using hcotA
        have hcotB' : (Nat.card {z : Fin 2 → ℤ //
              (∏ i, max 1 |(((z i : ℤ) : ℝ))|) ≤ 16 * Y / lam} : ℝ) ≤
            (5:ℝ)^2 + (100:ℝ)^2 * (16 * Y / lam) *
              (1 + Real.log (16 * Y / lam))^(2-1) / (((2-1).factorial : ℕ) : ℝ) := by
          simpa using hcotB
        have hBA := Commons.Analysis.SpecialFunctions.mahler_except_le n hn Y lam hY h4lam hlamY
        have h2n : (2:ℝ) ≤ 2^n := by
          calc (2:ℝ) = 2^1 := (pow_one 2).symm
            _ ≤ 2^n := pow_le_pow_right₀ (by norm_num) hn1
        have hA0 : (0:ℝ) ≤ (5:ℝ)^n + (100:ℝ)^n * ((8:ℝ)^n * Y / lam) *
            (1 + Real.log ((8:ℝ)^n * Y / lam))^(n-1) / (((n-1).factorial : ℕ) : ℝ) := by
          apply add_nonneg (by positivity)
          apply div_nonneg
          · exact mul_nonneg (by positivity)
              (pow_nonneg (by
                have h1 : (1:ℝ) ≤ (8:ℝ)^n * Y / lam := hMA
                have := Real.log_nonneg h1
                linarith) _)
          · positivity
        have hX : (0:ℝ) ≤ (16 * Y / lam) * (1 + Real.log (4 * Y / lam)) := by
          apply mul_nonneg (by positivity)
          have h1 : (1:ℝ) ≤ 4 * Y / lam := by
            rw [le_div_iff₀ (by linarith)]
            nlinarith [hlamY]
          have := Real.log_nonneg h1
          linarith
        calc (Nat.card T : ℝ) ≤ ((Nat.card {z : Fin n → ℤ //
                (∏ i, max 1 |(((z i : ℤ) : ℝ))|) ≤ (8:ℝ)^n * Y / lam} : ℝ) +
              (Nat.card {z : Fin 2 → ℤ //
                (∏ i, max 1 |(((z i : ℤ) : ℝ))|) ≤ 16 * Y / lam} : ℝ)) := by
              exact_mod_cast hsplit
          _ ≤ ((5:ℝ)^n + (100:ℝ)^n * ((8:ℝ)^n * Y / lam) *
                (1 + Real.log ((8:ℝ)^n * Y / lam))^(n-1) / (((n-1).factorial : ℕ) : ℝ)) +
              ((5:ℝ)^2 + (100:ℝ)^2 * (16 * Y / lam) *
                (1 + Real.log (16 * Y / lam))^(2-1) / (((2-1).factorial : ℕ) : ℝ)) := by
              linarith [hcotA', hcotB']
          _ ≤ 2^n * ((5:ℝ)^n + (100:ℝ)^n * ((8:ℝ)^n * Y / lam) *
                (1 + Real.log ((8:ℝ)^n * Y / lam))^(n-1) / (((n-1).factorial : ℕ) : ℝ)) := by
              nlinarith [hBA, h2n, hA0]
          _ ≤ 2^n * ((5:ℝ)^n + (100:ℝ)^n * ((8:ℝ)^n * Y / lam) *
                (1 + Real.log ((8:ℝ)^n * Y / lam))^(n-1) / (((n-1).factorial : ℕ) : ℝ)) +
              ((16 * Y / lam) * (1 + Real.log (4 * Y / lam)) + 8 * Y / lam) :=
              le_add_of_nonneg_right (add_nonneg hX (by positivity))
          _ ≤ (100000:ℝ)^n * Y * (1 + Real.log Y)^(n-1) / lam := by
              have h := Commons.Analysis.SpecialFunctions.mahler_arith_large_lam n hn Y lam hY hlam h4lam hlamY
              linarith [h]
      · have hempty : Nat.card T = 0 := Nat.card_eq_zero.mpr (Or.inl (not_nonempty_iff.mp hT))
        rw [hempty]
        have hlog : (0:ℝ) < 1 + Real.log Y := by
          have := Real.log_nonneg hY
          linarith
        have hpos : (0:ℝ) ≤ (100000:ℝ)^n * Y * (1 + Real.log Y)^(n-1) / lam := by
          apply div_nonneg
          · exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (pow_nonneg hlog.le _)
          · linarith
        simpa using hpos


end

end Commons.NumberTheory.NumberField
