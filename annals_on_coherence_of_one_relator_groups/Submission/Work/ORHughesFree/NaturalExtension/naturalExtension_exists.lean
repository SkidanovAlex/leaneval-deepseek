/-
# The natural extension of a Sylvester rank function

This file constructs, for a ring `U` with a `τ`-compatible Sylvester rank function `rk`, a Sylvester
rank function on the skew Laurent polynomial ring `U[t^{±1};τ] = SkewL U` extending `rk` and
sending `I + At` to `n` for every `n × n` matrix `A` over `U`; that is, the natural extension of
`rk` in the sense of [JZLA20, Proposition 3.5].

The construction is the usual one: the truncations `trunc i A` of `A` (see `Defs.lean`) give, for
every `i`, a matrix over `U`, and these are Sylvester rank functions up to an error of rank
`O(1)`; the ultralimit `blim ω` of `rk (trunc i A) / i` along a fixed ultrafilter containing all
cofinite sets (see `Defs.lean`) is therefore a Sylvester rank function on `U[t^{±1};τ]`, and the
identities `trunc i (skewLaurentConst n m A) = i · rk A` and `trunc i (onePlusAt n A) = i · n`
show that it is the natural extension.

-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension.blim_mono
import Submission.Work.ORHughesFree.NaturalExtension.blim_congr
import Submission.Work.ORHughesFree.NaturalExtension.blim_of_tendsto
import Submission.Work.ORHughesFree.NaturalExtension.rk_trunc_blockDiagFin2
import Submission.Work.ORHughesFree.NaturalExtension.rk_trunc_blockUpperFin2
import Submission.Work.ORHughesFree.NaturalExtension.blim_add
import Submission.Work.ORHughesFree.NaturalExtension.rk_trunc_onePlusAt
import Submission.Work.ORHughesFree.NaturalExtension.rk_trunc_skewLaurentConst
import Submission.Work.ORHughesFree.NaturalExtension.rk_trunc_mul_sub_le
import Submission.Work.ORHughesFree.RankAPI.rk_le_left
import Submission.Work.ORHughesFree.RankAPI.rk_le_right
import Submission.Work.ORHughesFree.RankAPI.rk_add_le

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORHughesFree.NaturalExtension

open Matrix Filter

/-! ## Elementary properties of the ultralimit -/

theorem blim_const (ω : Ultrafilter ℕ) (c : ℝ) : blim ω (fun _ => c) = c := by
  have hset : {r : ℝ | {i : ℕ | r ≤ (fun _ => c) i} ∈ ω} = Set.Iic c := by
    ext r
    change ({i : ℕ | r ≤ (fun _ => c) i} ∈ ω) ↔ r ∈ Set.Iic c
    constructor
    · intro hr
      by_contra hc
      rw [Set.mem_Iic, not_le] at hc
      have h0 : {i : ℕ | r ≤ (fun _ => c) i} = ∅ := by
        ext i
        simp [show ¬ (r ≤ c) from not_le.mpr hc]
      rw [h0] at hr
      have hmem : (∅ : Set ℕ) ∈ (ω : Filter ℕ) := hr
      exact Filter.empty_notMem (ω : Filter ℕ) hmem
    · intro hr
      rw [Set.mem_Iic] at hr
      have h0 : {i : ℕ | r ≤ (fun _ => c) i} = Set.univ := by
        ext i
        simp [hr]
      rw [h0]
      exact Filter.univ_mem
  rw [blim, hset]
  exact isLUB_Iic.csSup_eq Set.nonempty_Iic

theorem bddAbove_blimSet (ω : Ultrafilter ℕ) {f : ℕ → ℝ} {M : ℝ}
    (hf : ∀ i, f i ≤ M) : BddAbove {r : ℝ | {i | r ≤ f i} ∈ ω} := by
  refine ⟨M, fun r hr => ?_⟩
  change {i : ℕ | r ≤ f i} ∈ ω at hr
  by_contra hlt
  rw [not_le] at hlt
  have h0 : {i : ℕ | r ≤ f i} = ∅ := by
    ext i
    simp [show ¬ (r ≤ f i) from not_le.mpr (lt_of_le_of_lt (hf i) hlt)]
  rw [h0] at hr
  have hmem : (∅ : Set ℕ) ∈ (ω : Filter ℕ) := hr
  exact Filter.empty_notMem (ω : Filter ℕ) hmem

theorem nonempty_blimSet (ω : Ultrafilter ℕ) {f : ℕ → ℝ} {m : ℝ}
    (hf : ∀ i, m ≤ f i) : {r : ℝ | {i | r ≤ f i} ∈ ω}.Nonempty := by
  refine ⟨m, ?_⟩
  show {i : ℕ | m ≤ f i} ∈ ω
  have h0 : {i : ℕ | m ≤ f i} = Set.univ := by
    ext i
    simp [hf i]
  rw [h0]
  exact Filter.univ_mem

theorem blim_nonneg (ω : Ultrafilter ℕ) {f : ℕ → ℝ} {M : ℝ} (hf : ∀ i, |f i| ≤ M)
    (h : ∀ i, 0 ≤ f i) : 0 ≤ blim ω f := by
  have hM : ∀ i, f i ≤ M := fun i => le_trans (le_abs_self _) (hf i)
  refine le_csSup (bddAbove_blimSet ω hM) ?_
  show {i : ℕ | (0 : ℝ) ≤ f i} ∈ ω
  have h0 : {i : ℕ | (0 : ℝ) ≤ f i} = Set.univ := by
    ext i
    simp [h i]
  rw [h0]
  exact Filter.univ_mem

theorem blim_le_of_forall_le (ω : Ultrafilter ℕ) {f : ℕ → ℝ} {M M' : ℝ}
    (hf : ∀ i, |f i| ≤ M) (h : ∀ i, f i ≤ M') : blim ω f ≤ M' := by
  have hm : ∀ i, -M ≤ f i := fun i => neg_le_of_abs_le (hf i)
  refine csSup_le (nonempty_blimSet ω hm) ?_
  intro r hr
  obtain ⟨i, hi⟩ := Filter.nonempty_of_mem hr
  exact le_trans hi (h i)

/-! ## The sequence of truncated ranks -/

variable {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]

/-- The rank of the `i`-th truncation of `A`, normalized by `i`. -/
noncomputable def rankSeq (rk : SylvesterRank U) (ω : Ultrafilter ℕ) (n m : ℕ)
    (A : Matrix (Fin n) (Fin m) (SkewL U)) : ℕ → ℝ :=
  fun i => rk.rk (n * i) (m * i) (trunc i A) / (i : ℝ)

theorem rankSeq_nonneg (rk : SylvesterRank U) (ω : Ultrafilter ℕ) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (SkewL U)) (i : ℕ) : 0 ≤ rankSeq rk ω n m A i :=
  div_nonneg (rk.rk_nonneg _ _ _) (Nat.cast_nonneg i)

theorem abs_rankSeq_le (rk : SylvesterRank U) (ω : Ultrafilter ℕ) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (SkewL U)) :
    ∀ i, |rankSeq rk ω n m A i| ≤ max (n : ℝ) (m : ℝ) := by
  intro i
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    simp [rankSeq]
  · rw [abs_of_nonneg (rankSeq_nonneg rk ω A i)]
    have hpos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
    have hA : rk.rk (n * i) (m * i) (trunc i A) ≤ (n : ℝ) * (i : ℝ) := by
      have hle := RankAPI.rk_le_left rk (trunc i A)
      rw [Nat.cast_mul] at hle
      exact hle
    have hmax : (n : ℝ) * (i : ℝ) ≤ max (n : ℝ) (m : ℝ) * (i : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg i)
    rw [rankSeq, div_le_iff₀ hpos]
    exact le_trans hA hmax

theorem abs_rankSeq_le_of_le (rk : SylvesterRank U) (ω : Ultrafilter ℕ) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (SkewL U)) {N M : ℕ} (hn : n ≤ N) (hm : m ≤ M) :
    ∀ i, |rankSeq rk ω n m A i| ≤ max (N : ℝ) (M : ℝ) :=
  fun i => le_trans (abs_rankSeq_le rk ω A i)
    (max_le_max (Nat.cast_le.mpr hn) (Nat.cast_le.mpr hm))

theorem rankSeq_zero (rk : SylvesterRank U) (ω : Ultrafilter ℕ) (n m : ℕ) :
    rankSeq rk ω n m (0 : Matrix (Fin n) (Fin m) (SkewL U)) = fun _ => 0 := by
  funext i
  simp [rankSeq, trunc_zero, rk.rk_zero]

/-! ## The main theorem -/

theorem naturalExtension_exists {U : Type} [Ring U] [VonNeumannRegularRing U]
    [MulSemiringAction (Multiplicative ℤ) U] (rk : SylvesterRank U)
    (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) U),
      rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A) :
    ∃ rkE : SylvesterRank (SkewMonoidAlgebra U (Multiplicative ℤ)),
      IsNaturalExtension rk rkE := by
  classical
  obtain ⟨ω, hω⟩ := exists_ultrafilter_le_atTop
  have hbdd : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (SkewL U)) (i : ℕ),
      |rankSeq rk ω n m A i| ≤ max (n : ℝ) (m : ℝ) :=
    fun n m A => abs_rankSeq_le rk ω A
  refine ⟨{ rk := fun n m A => blim ω (rankSeq rk ω n m A),
            rk_nonneg := ?_,
            rk_zero := ?_,
            rk_one := ?_,
            rk_mul_le_left := ?_,
            rk_mul_le_right := ?_,
            rk_blockDiag := ?_,
            rk_blockUpper := ?_ }, ?_⟩
  · intro n m A
    exact blim_nonneg ω (hbdd n m A) (fun i => rankSeq_nonneg rk ω A i)
  · intro n m
    rw [rankSeq_zero rk ω n m]
    exact blim_const ω 0
  · have hmat : (1 : Matrix (Fin 1) (Fin 1) (SkewL U)) =
        onePlusAt 1 (0 : Matrix (Fin 1) (Fin 1) U) := by
      simp [onePlusAt]
    rw [hmat]
    have hev : ∀ᶠ i in Filter.atTop,
        rankSeq rk ω 1 1 (onePlusAt 1 (0 : Matrix (Fin 1) (Fin 1) U)) i = 1 := by
      filter_upwards [eventually_ge_atTop 1] with i hi
      rw [rankSeq, rk_trunc_onePlusAt rk 0 i, Nat.cast_one, mul_one]
      have hi' : (i : ℝ) ≠ 0 := by positivity
      exact div_self hi'
    rw [blim_congr ω hω hev, blim_const ω 1]
  · intro n m k A B
    let C : ℝ := (k : ℝ) * (lowerDeg B : ℝ) + (n : ℝ) * (lowerDeg A : ℝ)
    have hCnn : 0 ≤ C := by
      show 0 ≤ (k : ℝ) * (lowerDeg B : ℝ) + (n : ℝ) * (lowerDeg A : ℝ)
      positivity
    have hpt : ∀ i : ℕ, rankSeq rk ω n k (A * B) i ≤ rankSeq rk ω n m A i + C / (i : ℝ) := by
      intro i
      have hsplit : trunc i (A * B) =
          trunc i A * trunc i B + (trunc i (A * B) - trunc i A * trunc i B) := by
        abel
      have h4 : rk.rk (n * i) (k * i) (trunc i (A * B)) ≤
          rk.rk (n * i) (m * i) (trunc i A) + C := by
        have h1 : rk.rk (n * i) (k * i) (trunc i (A * B)) ≤
            rk.rk (n * i) (k * i) (trunc i A * trunc i B) +
              rk.rk (n * i) (k * i) (trunc i (A * B) - trunc i A * trunc i B) := by
          have hraw := RankAPI.rk_add_le rk (trunc i A * trunc i B)
            (trunc i (A * B) - trunc i A * trunc i B)
          have hsum : trunc i A * trunc i B +
              (trunc i (A * B) - trunc i A * trunc i B) = trunc i (A * B) := by abel
          rw [hsum] at hraw
          exact hraw
        have h2 : rk.rk (n * i) (k * i) (trunc i A * trunc i B) ≤
            rk.rk (n * i) (m * i) (trunc i A) :=
          rk.rk_mul_le_left (trunc i A) (trunc i B)
        have h3 : rk.rk (n * i) (k * i) (trunc i (A * B) - trunc i A * trunc i B) ≤ C :=
          rk_trunc_mul_sub_le rk A B i
        linarith
      calc rankSeq rk ω n k (A * B) i
          = rk.rk (n * i) (k * i) (trunc i (A * B)) / (i : ℝ) := rfl
        _ ≤ (rk.rk (n * i) (m * i) (trunc i A) + C) / (i : ℝ) :=
            div_le_div_of_nonneg_right h4 (Nat.cast_nonneg i)
        _ = rk.rk (n * i) (m * i) (trunc i A) / (i : ℝ) + C / (i : ℝ) := add_div _ _ _
        _ = rankSeq rk ω n m A i + C / (i : ℝ) := rfl
    have hbndC : ∀ i : ℕ, |C / (i : ℝ)| ≤ C := by
      intro i
      rw [abs_of_nonneg (div_nonneg hCnn (Nat.cast_nonneg i))]
      rcases Nat.eq_zero_or_pos i with hi | hi
      · subst hi; simpa using hCnn
      · rw [div_le_iff₀ (by exact_mod_cast hi)]
        have h1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
        nlinarith
    have hbndC' : ∀ i : ℕ, |C / (i : ℝ)| ≤ max (n : ℝ) (m : ℝ) + C :=
      fun i => le_trans (hbndC i)
        (le_add_of_nonneg_left (by positivity : (0 : ℝ) ≤ max (n : ℝ) (m : ℝ)))
    have hbndA' : ∀ i : ℕ, |rankSeq rk ω n m A i| ≤ max (n : ℝ) (m : ℝ) + C :=
      fun i => le_trans (hbdd n m A i) (le_add_of_nonneg_right hCnn)
    have hsum : blim ω (fun i => rankSeq rk ω n m A i + C / (i : ℝ)) =
        blim ω (rankSeq rk ω n m A) + blim ω (fun i => C / (i : ℝ)) :=
      blim_add ω hbndA' hbndC'
    have htend : blim ω (fun i => C / (i : ℝ)) = 0 :=
      blim_of_tendsto ω hω hbndC (tendsto_const_div_atTop_nhds_zero_nat C)
    have hmono : blim ω (rankSeq rk ω n k (A * B)) ≤
        blim ω (fun i => rankSeq rk ω n m A i + C / (i : ℝ)) := by
      refine blim_mono ω (hbdd n k (A * B))
        (M' := max (n : ℝ) (m : ℝ) + C) (fun i => ?_) hpt
      calc |rankSeq rk ω n m A i + C / (i : ℝ)|
          ≤ |rankSeq rk ω n m A i| + |C / (i : ℝ)| := abs_add_le _ _
        _ ≤ max (n : ℝ) (m : ℝ) + C := add_le_add (hbdd n m A i) (hbndC i)
    calc blim ω (rankSeq rk ω n k (A * B)) ≤
          blim ω (fun i => rankSeq rk ω n m A i + C / (i : ℝ)) := hmono
      _ = blim ω (rankSeq rk ω n m A) + blim ω (fun i => C / (i : ℝ)) := hsum
      _ = blim ω (rankSeq rk ω n m A) := by rw [htend, add_zero]
  · intro n m k A B
    let C : ℝ := (k : ℝ) * (lowerDeg B : ℝ) + (n : ℝ) * (lowerDeg A : ℝ)
    have hCnn : 0 ≤ C := by
      show 0 ≤ (k : ℝ) * (lowerDeg B : ℝ) + (n : ℝ) * (lowerDeg A : ℝ)
      positivity
    have hpt : ∀ i : ℕ, rankSeq rk ω n k (A * B) i ≤ rankSeq rk ω m k B i + C / (i : ℝ) := by
      intro i
      have hsplit : trunc i (A * B) =
          trunc i A * trunc i B + (trunc i (A * B) - trunc i A * trunc i B) := by
        abel
      have h4 : rk.rk (n * i) (k * i) (trunc i (A * B)) ≤
          rk.rk (m * i) (k * i) (trunc i B) + C := by
        have h1 : rk.rk (n * i) (k * i) (trunc i (A * B)) ≤
            rk.rk (n * i) (k * i) (trunc i A * trunc i B) +
              rk.rk (n * i) (k * i) (trunc i (A * B) - trunc i A * trunc i B) := by
          have hraw := RankAPI.rk_add_le rk (trunc i A * trunc i B)
            (trunc i (A * B) - trunc i A * trunc i B)
          have hsum : trunc i A * trunc i B +
              (trunc i (A * B) - trunc i A * trunc i B) = trunc i (A * B) := by abel
          rw [hsum] at hraw
          exact hraw
        have h2 : rk.rk (n * i) (k * i) (trunc i A * trunc i B) ≤
            rk.rk (m * i) (k * i) (trunc i B) :=
          rk.rk_mul_le_right (trunc i A) (trunc i B)
        have h3 : rk.rk (n * i) (k * i) (trunc i (A * B) - trunc i A * trunc i B) ≤ C :=
          rk_trunc_mul_sub_le rk A B i
        linarith
      calc rankSeq rk ω n k (A * B) i
          = rk.rk (n * i) (k * i) (trunc i (A * B)) / (i : ℝ) := rfl
        _ ≤ (rk.rk (m * i) (k * i) (trunc i B) + C) / (i : ℝ) :=
            div_le_div_of_nonneg_right h4 (Nat.cast_nonneg i)
        _ = rk.rk (m * i) (k * i) (trunc i B) / (i : ℝ) + C / (i : ℝ) := add_div _ _ _
        _ = rankSeq rk ω m k B i + C / (i : ℝ) := rfl
    have hbndC : ∀ i : ℕ, |C / (i : ℝ)| ≤ C := by
      intro i
      rw [abs_of_nonneg (div_nonneg hCnn (Nat.cast_nonneg i))]
      rcases Nat.eq_zero_or_pos i with hi | hi
      · subst hi; simpa using hCnn
      · rw [div_le_iff₀ (by exact_mod_cast hi)]
        have h1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
        nlinarith
    have hbndC' : ∀ i : ℕ, |C / (i : ℝ)| ≤ max (m : ℝ) (k : ℝ) + C :=
      fun i => le_trans (hbndC i)
        (le_add_of_nonneg_left (by positivity : (0 : ℝ) ≤ max (m : ℝ) (k : ℝ)))
    have hbndB' : ∀ i : ℕ, |rankSeq rk ω m k B i| ≤ max (m : ℝ) (k : ℝ) + C :=
      fun i => le_trans (hbdd m k B i) (le_add_of_nonneg_right hCnn)
    have hsum : blim ω (fun i => rankSeq rk ω m k B i + C / (i : ℝ)) =
        blim ω (rankSeq rk ω m k B) + blim ω (fun i => C / (i : ℝ)) :=
      blim_add ω hbndB' hbndC'
    have htend : blim ω (fun i => C / (i : ℝ)) = 0 :=
      blim_of_tendsto ω hω hbndC (tendsto_const_div_atTop_nhds_zero_nat C)
    have hmono : blim ω (rankSeq rk ω n k (A * B)) ≤
        blim ω (fun i => rankSeq rk ω m k B i + C / (i : ℝ)) := by
      refine blim_mono ω (hbdd n k (A * B))
        (M' := max (m : ℝ) (k : ℝ) + C) (fun i => ?_) hpt
      calc |rankSeq rk ω m k B i + C / (i : ℝ)|
          ≤ |rankSeq rk ω m k B i| + |C / (i : ℝ)| := abs_add_le _ _
        _ ≤ max (m : ℝ) (k : ℝ) + C := add_le_add (hbdd m k B i) (hbndC i)
    calc blim ω (rankSeq rk ω n k (A * B)) ≤
          blim ω (fun i => rankSeq rk ω m k B i + C / (i : ℝ)) := hmono
      _ = blim ω (rankSeq rk ω m k B) + blim ω (fun i => C / (i : ℝ)) := hsum
      _ = blim ω (rankSeq rk ω m k B) := by rw [htend, add_zero]
  · intro n m p q A B
    have hpt : ∀ i : ℕ, rankSeq rk ω (n + p) (m + q) (blockDiagFin A B) i =
        rankSeq rk ω n m A i + rankSeq rk ω p q B i := by
      intro i
      simp only [rankSeq]
      rw [rk_trunc_blockDiagFin2 rk i A B, add_div]
    rw [funext hpt]
    exact blim_add ω (abs_rankSeq_le_of_le rk ω A (Nat.le_add_right n p) (Nat.le_add_right m q))
      (abs_rankSeq_le_of_le rk ω B (Nat.le_add_left p n) (Nat.le_add_left q m))
  · intro n m p q A B C
    have hpt : ∀ i : ℕ, rankSeq rk ω n m A i + rankSeq rk ω p q B i ≤
        rankSeq rk ω (n + p) (m + q) (blockUpperFin A B C) i := by
      intro i
      have h := rk_trunc_blockUpperFin2 rk i A B C
      simp only [rankSeq]
      rw [← add_div]
      exact div_le_div_of_nonneg_right h (Nat.cast_nonneg i)
    calc blim ω (rankSeq rk ω n m A) + blim ω (rankSeq rk ω p q B)
        = blim ω (rankSeq rk ω n m A + rankSeq rk ω p q B) :=
          (blim_add ω (abs_rankSeq_le_of_le rk ω A (Nat.le_add_right n p) (Nat.le_add_right m q))
            (abs_rankSeq_le_of_le rk ω B (Nat.le_add_left p n) (Nat.le_add_left q m))).symm
      _ ≤ blim ω (rankSeq rk ω (n + p) (m + q) (blockUpperFin A B C)) :=
          blim_mono ω (M' := max (n : ℝ) (m : ℝ) + max (p : ℝ) (q : ℝ)) (fun i => by
              calc |rankSeq rk ω n m A i + rankSeq rk ω p q B i|
                  ≤ |rankSeq rk ω n m A i| + |rankSeq rk ω p q B i| := abs_add_le _ _
                _ ≤ max (n : ℝ) (m : ℝ) + max (p : ℝ) (q : ℝ) :=
                    add_le_add (hbdd n m A i) (hbdd p q B i))
            (fun i => by
              refine le_trans (abs_rankSeq_le rk ω (blockUpperFin A B C) i) ?_
              push_cast
              exact max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
                (add_le_add (le_max_right _ _) (le_max_right _ _))) hpt
  · constructor
    · intro n m A
      change blim ω (rankSeq rk ω n m (skewLaurentConst n m A)) = rk.rk n m A
      have hev : ∀ᶠ i in Filter.atTop,
          rankSeq rk ω n m (skewLaurentConst n m A) i = rk.rk n m A := by
        filter_upwards [eventually_ge_atTop 1] with i hi
        rw [rankSeq, rk_trunc_skewLaurentConst rk hτ A i]
        have hi' : (i : ℝ) ≠ 0 := by positivity
        exact mul_div_cancel_left₀ (rk.rk n m A) hi'
      rw [blim_congr ω hω hev, blim_const ω (rk.rk n m A)]
    · intro n A
      change blim ω (rankSeq rk ω n n (onePlusAt n A)) = (n : ℝ)
      have hev : ∀ᶠ i in Filter.atTop, rankSeq rk ω n n (onePlusAt n A) i = (n : ℝ) := by
        filter_upwards [eventually_ge_atTop 1] with i hi
        rw [rankSeq, rk_trunc_onePlusAt rk A i]
        have hi' : (i : ℝ) ≠ 0 := by positivity
        exact mul_div_cancel_left₀ (n : ℝ) hi'
      rw [blim_congr ω hω hev, blim_const ω (n : ℝ)]

end Work.ORHughesFree.NaturalExtension
