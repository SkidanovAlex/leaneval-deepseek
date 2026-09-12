import Mathlib
import Submission.L2Norm
import Submission.Ell2Update
import Submission.Commons.Analysis.Interval.aux_averaging_count

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Prop ell-2 update: deterministic greedy-interval core

Tikhomirov 2020, Section 3, `Prop ell-2 update` (paper lines ~1013–1223).
This file develops the deterministic interval-construction used in its proof:

Given a nonnegative `g : ℤ → ℝ` with multiplicative log-Lipschitzness
(`ratioLip`), a "small" threshold `a` and a small-fraction `δ`, each "large"
point `l` (`g l ≥ rw·a`) in an interval `I₀ = Icc lo (lo+N−1)` spawns a greedy
integer interval `[l, r] ⊆ Ĩ := Icc lo (lo+2N−1)` with
  (i) `r` is the maximal point `t ≥ l` (within `Ĩ`) such that the number of
      "small" points (`g ≤ a`) in `[l,t]` is at most `δ·(t−l+1)`;
  (ii) hence `|[l,r] ∩ {g ≤ a}| ≤ δ·|I'|` and (via maximality) `≥ δ|I'|/2`;
  (iii) the length `|I'|` is at most `N` (by the N-interval mass bound) and at
      least `~1/μ²` (by the log-Lipschitz ratio, which keeps a long prefix of
      `[l,r]` above `a`).

All statements are self-contained (Mathlib + the two sibling modules for
`ratioLip` and `norm₂sq`); nothing here depends on randomness.
-/

namespace Submission.Ell2Greedy

attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- The `N`-point integer interval `I₀ := [lo, lo+N−1]`. -/
def I0 (lo : ℤ) (N : ℕ) : Finset ℤ := Finset.Icc lo (lo + (N : ℤ) - 1)

/-- The doubled interval `Ĩ := [lo, lo+2N−1]` ("I₀ + {0,…,N}"). -/
def It (lo : ℤ) (N : ℕ) : Finset ℤ := Finset.Icc lo (lo + (2 : ℤ) * (N : ℤ) - 1)

/-- Number of points of `[l, r]` on which `g ≤ a`. -/
def smallCnt (g : ℤ → ℝ) (a : ℝ) (l r : ℤ) : ℕ :=
  ((Finset.Icc l r).filter (fun t : ℤ => g t ≤ a)).card

/-- Length (in points) of `[l,t]` as a real: `t−l+1`. -/
def clen (l t : ℤ) : ℝ := ((t - l + 1 : ℤ) : ℝ)

/-- Candidates for the right endpoint of the greedy interval from `l`:
`t ∈ [l, hi]` with `(small count on [l,t]) ≤ δ·(t−l+1)`. -/
def cand (g : ℤ → ℝ) (a δ : ℝ) (hi l : ℤ) : Finset ℤ :=
  (Finset.Icc l hi).filter (fun t : ℤ => (smallCnt g a l t : ℝ) ≤ δ * clen l t)

/-- The right endpoint: the maximal candidate (defaults to `l` if there is none;
all uses supply a nonemptiness proof). -/
noncomputable def rEnd (g : ℤ → ℝ) (a δ : ℝ) (hi l : ℤ) : ℤ :=
  if h : (cand g a δ hi l).Nonempty then (cand g a δ hi l).max' h else l

/-- Interval length of `[l, r]` (number of integer points). -/
def ilen (l r : ℤ) : ℕ := (Finset.Icc l r).card

/-- Cardinality of a ℤ interval of length `N` starting at `lo`. -/
lemma card_Icc_len (lo : ℤ) (N : ℕ) : (Finset.Icc lo (lo + (N : ℤ) - 1)).card = N := by
  rw [Int.card_Icc]
  have h : (N : ℤ) = (N : ℤ) + 1 - 1 := by omega
  rw [← Int.toNat_of_nonneg (Int.ofNat_nonneg N)]
  congr
  omega

/-- `I₀` has cardinality `N`. -/
lemma card_I0 (lo : ℤ) (N : ℕ) : (I0 lo N).card = N := card_Icc_len lo N

/-- `Ĩ` has cardinality `2N`. -/
lemma card_It (lo : ℤ) (N : ℕ) : (It lo N).card = 2 * N := by
  dsimp [It]
  rw [Int.card_Icc]
  have h : (2 * (N : ℤ)) = (2 * (N : ℤ)) + 1 - 1 := by omega
  rw [← Int.toNat_of_nonneg (by positivity : 0 ≤ (2 * (N : ℤ)))]
  congr
  omega

/-- membership in `I0`. -/
lemma mem_I0 {lo : ℤ} {N : ℕ} {t : ℤ} : t ∈ I0 lo N ↔ lo ≤ t ∧ t ≤ lo + (N : ℤ) - 1 := by
  dsimp [I0]
  rw [Finset.mem_Icc]

/-- membership in `It`. -/
lemma mem_It {lo : ℤ} {N : ℕ} {t : ℤ} :
    t ∈ It lo N ↔ lo ≤ t ∧ t ≤ lo + (2 : ℤ) * (N : ℤ) - 1 := by
  dsimp [It]
  rw [Finset.mem_Icc]

/-- splitting of `Ĩ` into `I₀` and its translate by `N`. -/
lemma mem_It_split {lo : ℤ} {N : ℕ} {t : ℤ} :
    t ∈ It lo N ↔ t ∈ I0 lo N ∨ t ∈ Finset.Icc (lo + (N : ℤ)) (lo + (2 : ℤ) * (N : ℤ) - 1) := by
  rw [mem_It, mem_I0, Finset.mem_Icc]
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩
    by_cases ht : t ≤ lo + (N : ℤ) - 1
    · left; exact ⟨h1, ht⟩
    · right; constructor <;> omega
  · intro h
    rcases h with h | h
    · rcases h with ⟨h1, h2⟩; constructor <;> omega
    · rcases h with ⟨h1, h2⟩; constructor <;> omega

/-- interval `I0` is contained in `It`. -/
lemma I0_subset_It (lo : ℤ) (N : ℕ) : I0 lo N ⊆ It lo N := by
  intro t ht
  rw [mem_It_split]
  left
  exact ht

/-- right half of `Ĩ` is contained in `It`. -/
lemma right_It_subset (lo : ℤ) (N : ℕ) :
    Finset.Icc (lo + (N : ℤ)) (lo + (2 : ℤ) * (N : ℤ) - 1) ⊆ It lo N := by
  intro t ht
  rw [mem_It_split]
  right
  exact ht

/-- membership in a ℤ interval: pure inequalities. -/
lemma mem_Icc_int {a b x : ℤ} : x ∈ Finset.Icc a b ↔ a ≤ x ∧ x ≤ b := Finset.mem_Icc

/-- membership in `cand` unfolds to interval membership + small-count condition. -/
lemma mem_cand_iff {g : ℤ → ℝ} {a δ : ℝ} {hi l t : ℤ} :
    t ∈ cand g a δ hi l ↔
      t ∈ Finset.Icc l hi ∧ (smallCnt g a l t : ℝ) ≤ δ * clen l t := by
  unfold cand
  exact Finset.mem_filter

/-- monotonicity of the small count in the right endpoint. -/
lemma smallCnt_le_of_le {g : ℤ → ℝ} {a : ℝ} {l t u : ℤ} (htu : t ≤ u) :
    smallCnt g a l t ≤ smallCnt g a l u := by
  dsimp [smallCnt]
  have hsub' : Finset.Icc l t ⊆ Finset.Icc l u := Finset.Icc_subset_Icc (le_refl l) htu
  have hsub : (Finset.Icc l t).filter (fun t : ℤ => g t ≤ a) ⊆
      (Finset.Icc l u).filter (fun t : ℤ => g t ≤ a) :=
    Finset.filter_subset_filter _ hsub'
  exact Finset.card_le_card hsub

/-- the singleton `[l,l]` has no small point when `g l > a`. -/
lemma smallCnt_self_zero {g : ℤ → ℝ} {a : ℝ} {l : ℤ} (ha : a < g l) : smallCnt g a l l = 0 := by
  dsimp [smallCnt]
  rw [Finset.card_eq_zero]
  rw [Finset.filter_eq_empty_iff]
  intro t ht hg
  have ht' : t = l := by
    have h1' := Finset.mem_Icc.mp ht
    omega
  subst t
  exact (not_le_of_gt ha) hg

/-- a large point is a candidate. -/
lemma cand_mem_self {g : ℤ → ℝ} {a δ : ℝ} {hi l : ℤ} (hδ0 : 0 ≤ δ) (ha : a < g l) (hlhi : l ≤ hi) :
    l ∈ cand g a δ hi l := by
  rw [mem_cand_iff]
  constructor
  · rw [Finset.mem_Icc]
    exact ⟨le_rfl, hlhi⟩
  · have h1 : ((l - l + 1 : ℤ) : ℝ) = (1 : ℝ) := by
      have hz : (l - l + 1 : ℤ) = (1 : ℤ) := by omega
      rw [hz]
      norm_num
    rw [smallCnt_self_zero ha]
    dsimp [clen]
    rw [h1]
    simpa using hδ0

/-- every candidate is at most the right end. -/
lemma le_rEnd {g : ℤ → ℝ} {a δ : ℝ} {hi l t : ℤ} (hcand : (cand g a δ hi l).Nonempty)
    (ht : t ∈ cand g a δ hi l) : t ≤ rEnd g a δ hi l := by
  unfold rEnd
  rw [dif_pos hcand]
  exact Finset.le_max' _ _ ht

/-- the right end is itself a candidate (membership). -/
lemma rEnd_mem_cand {g : ℤ → ℝ} {a δ : ℝ} {hi l : ℤ} (hcand : (cand g a δ hi l).Nonempty) :
    rEnd g a δ hi l ∈ cand g a δ hi l := by
  unfold rEnd
  rw [dif_pos hcand]
  exact Finset.max'_mem _ _

/-- the right end lies in `[l,hi]`. -/
lemma rEnd_mem_Icc {g : ℤ → ℝ} {a δ : ℝ} {hi l : ℤ} (hcand : (cand g a δ hi l).Nonempty) :
    l ≤ rEnd g a δ hi l ∧ rEnd g a δ hi l ≤ hi := by
  have hm := rEnd_mem_cand (g := g) (a := a) (δ := δ) (hi := hi) (l := l) hcand
  rw [mem_cand_iff] at hm
  exact Finset.mem_Icc.mp hm.1

/-- the right end satisfies the small-count condition. -/
lemma rEnd_smallCnt {g : ℤ → ℝ} {a δ : ℝ} {hi l : ℤ} (hcand : (cand g a δ hi l).Nonempty) :
    (smallCnt g a l (rEnd g a δ hi l) : ℝ) ≤ δ * clen l (rEnd g a δ hi l) := by
  have hm := rEnd_mem_cand (g := g) (a := a) (δ := δ) (hi := hi) (l := l) hcand
  rw [mem_cand_iff] at hm
  exact hm.2

/-- maximality: the successor of the right end is not a candidate. -/
lemma rEnd_succ_not_cand {g : ℤ → ℝ} {a δ : ℝ} {hi l : ℤ} (hcand : (cand g a δ hi l).Nonempty)
    (hlts : rEnd g a δ hi l < hi) :
    ¬ (rEnd g a δ hi l + 1 ∈ cand g a δ hi l) := by
  intro h
  have hle := le_rEnd (g := g) (a := a) (δ := δ) (hi := hi) (l := l) hcand h
  omega

/-- the point after the right end (when inside `[l,hi]`) violates the small-count
condition. -/
lemma rEnd_succ_violates {g : ℤ → ℝ} {a δ : ℝ} {hi l : ℤ} (hcand : (cand g a δ hi l).Nonempty)
    (hlts : rEnd g a δ hi l < hi) :
    δ * clen l (rEnd g a δ hi l + 1) < (smallCnt g a l (rEnd g a δ hi l + 1) : ℝ) := by
  have hn : ¬ (rEnd g a δ hi l + 1 ∈ cand g a δ hi l) := rEnd_succ_not_cand hcand hlts
  have hle1 : l ≤ rEnd g a δ hi l + 1 := by
    have hle := (rEnd_mem_Icc hcand).1
    omega
  have hle2 : rEnd g a δ hi l + 1 ≤ hi := by omega
  rw [mem_cand_iff] at hn
  have hn' : ¬ (smallCnt g a l (rEnd g a δ hi l + 1) : ℝ) ≤ δ * clen l (rEnd g a δ hi l + 1) := by
    intro hc
    exact hn ⟨(Finset.mem_Icc.mpr ⟨hle1, hle2⟩), hc⟩
  exact lt_of_not_ge hn'

/-- adding one point on the right increases the small count by at most one. -/
lemma smallCnt_succ_le {g : ℤ → ℝ} {a : ℝ} {l t : ℤ} :
    smallCnt g a l (t + 1) ≤ smallCnt g a l t + 1 := by
  dsimp [smallCnt]
  by_cases hl : l ≤ t + 1
  · have hdec : Finset.Icc l (t + 1) = insert (t + 1) (Finset.Icc l t) := by
      ext x
      rw [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Icc]
      constructor
      · intro hx
        rcases hx with ⟨h1, h2⟩
        by_cases hxt : x ≤ t
        · right; exact ⟨h1, hxt⟩
        · left; omega
      · intro hx
        rcases hx with hx | hx
        · rw [hx]; constructor <;> omega
        · rcases hx with ⟨h1, h2⟩; constructor <;> omega
    rw [hdec, Finset.filter_insert]
    by_cases hg : g (t + 1) ≤ a
    · rw [if_pos hg]
      have hnot : t + 1 ∉ (Finset.Icc l t).filter (fun x : ℤ => g x ≤ a) := by
        intro hm
        rcases Finset.mem_filter.mp hm with ⟨hmI, _⟩
        have : t + 1 ≤ t := (Finset.mem_Icc.mp hmI).2
        omega
      rw [Finset.card_insert_of_notMem hnot]
    · rw [if_neg hg]
      omega
  · have e1 : (Finset.Icc l (t + 1)).filter (fun x : ℤ => g x ≤ a) = ∅ := by
      ext x
      simp [mem_Icc_int]
      omega
    have e2 : (Finset.Icc l t).filter (fun x : ℤ => g x ≤ a) = ∅ := by
      ext x
      simp [mem_Icc_int]
      omega
    rw [e1, e2]
    simp

/-- (prefix bound) With a `μ⁴`-ratioLip function and a `2^{μ²}a`-large point `l`,
all points `l+j` with `j ≤ q ≤ 1/(2μ²)` still exceed `a·2^{μ²/2}` (hence `a`). -/
lemma prefix_above {g : ℤ → ℝ} {a μ : ℝ} {l : ℤ} {j q : ℕ}
    (hμ0 : 0 < μ) (ha0 : 0 < a) (hlip : Ell2Update.ratioLip (μ ^ 4) g)
    (hlarge : (2 : ℝ) ^ (μ ^ 2) * a ≤ g l) (hj : j ≤ q) (hq : (q : ℝ) ≤ 1 / (2 * μ ^ 2)) :
    a * (2 : ℝ) ^ (μ ^ 2 / 2) ≤ g (l + (j : ℤ)) := by
  let B : ℝ := (2 : ℝ) ^ (μ ^ 2) * a
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hε0 : 0 ≤ μ ^ 4 := by positivity
  have hdist : |((l : ℤ) : ℝ) - ((l + (j : ℤ)) : ℝ)| ≤ (j : ℝ) := by
    have hz : ((l : ℤ) : ℝ) - ((l + (j : ℤ)) : ℝ) = -((j : ℤ) : ℝ) := by
      norm_num [Int.cast_add]
    rw [hz]
    rw [abs_neg]
    rw [abs_of_nonneg]
    · norm_num
    · exact_mod_cast Nat.zero_le j
  have hdec : a * (2 : ℝ) ^ (μ ^ 2 / 2) ≤ (2 : ℝ) ^ (-(μ ^ 4) * (j : ℝ)) * B := by
    have hjreal : (j : ℝ) ≤ 1 / (2 * μ ^ 2) := le_trans (by exact_mod_cast hj) hq
    have hμsq : 0 < μ ^ 2 := by positivity
    have hjmu : (j : ℝ) * μ ^ 2 ≤ 1 / 2 := by
      have hmul := mul_le_mul_of_nonneg_right hjreal (le_of_lt hμsq)
      have hcancel : (1 / (2 * μ ^ 2)) * μ ^ 2 = 1 / 2 := by
        field_simp [hμsq.ne']
      rwa [hcancel] at hmul
    have hμ4j : (μ ^ 4) * (j : ℝ) ≤ μ ^ 2 / 2 := by
      have hprod : (μ ^ 4) * (j : ℝ) = μ ^ 2 * ((j : ℝ) * μ ^ 2) := by ring
      rw [hprod]
      have hle := mul_le_mul_of_nonneg_left hjmu (le_of_lt hμsq)
      have h12 : μ ^ 2 * (1 / 2) = μ ^ 2 / 2 := by ring
      rwa [h12] at hle
    have hexp : μ ^ 2 / 2 ≤ μ ^ 2 - (μ ^ 4) * (j : ℝ) := by nlinarith
    have hmono : (2 : ℝ) ^ (μ ^ 2 / 2) ≤ (2 : ℝ) ^ (μ ^ 2 - (μ ^ 4) * (j : ℝ)) :=
      Ell2Update.rpow_two_mono hexp
    have hdec0 : a * (2 : ℝ) ^ (μ ^ 2 / 2) ≤ a * (2 : ℝ) ^ (μ ^ 2 - (μ ^ 4) * (j : ℝ)) :=
      mul_le_mul_of_nonneg_left hmono (le_of_lt ha0)
    have hprod : (2 : ℝ) ^ (-(μ ^ 4) * (j : ℝ)) * (2 : ℝ) ^ (μ ^ 2) =
        (2 : ℝ) ^ (μ ^ 2 - (μ ^ 4) * (j : ℝ)) := by
      rw [Ell2Update.rpow_two_add]
      congr 1
      ring
    have hrew : a * (2 : ℝ) ^ (μ ^ 2 - (μ ^ 4) * (j : ℝ)) =
        (2 : ℝ) ^ (-(μ ^ 4) * (j : ℝ)) * ((2 : ℝ) ^ (μ ^ 2) * a) := by
      rw [← hprod]
      ring
    rwa [hrew] at hdec0
  exact Ell2Update.ratioLip_spike (ε := μ ^ 4) (g := g) hlip
    (B := B) (a := a * (2 : ℝ) ^ (μ ^ 2 / 2)) (D := (j : ℝ)) (x := l + (j : ℤ)) (y := l)
    hlarge hB0 (by simpa [Int.cast_add] using hdist) hε0 hdec

/-- strict version of the prefix bound: prefix points are not "small". -/
lemma prefix_not_small {g : ℤ → ℝ} {a μ : ℝ} {l : ℤ} {j q : ℕ}
    (hμ0 : 0 < μ) (ha0 : 0 < a) (hlip : Ell2Update.ratioLip (μ ^ 4) g)
    (hlarge : (2 : ℝ) ^ (μ ^ 2) * a ≤ g l) (hj : j ≤ q) (hq : (q : ℝ) ≤ 1 / (2 * μ ^ 2)) :
    a < g (l + (j : ℤ)) := by
  have hb := prefix_above (g := g) (a := a) (μ := μ) (l := l) (j := j) (q := q)
    hμ0 ha0 hlip hlarge hj hq
  have hg : (1 : ℝ) < (2 : ℝ) ^ (μ ^ 2 / 2) := by
    exact Ell2Update.two_pow_gt_one (μ ^ 2 / 2) (by positivity)
  have hmul : a < a * (2 : ℝ) ^ (μ ^ 2 / 2) := by
    simpa using (mul_lt_mul_of_pos_left hg ha0)
  linarith



/-- sum over a subset is at most the sum over the superset (nonnegative terms). -/
lemma sum_subset_le {g : ℤ → ℝ} (hg : ∀ t : ℤ, 0 ≤ g t) {s t : Finset ℤ} (hst : s ⊆ t) :
    (∑ x ∈ s, g x) ≤ (∑ x ∈ t, g x) := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun x hx hx' => hg x)

/-- (lower bound on an interval sum) an interval with only `smallCnt` points
below/at `a` carries mass at least `a·(|I| − smallCnt)`. -/
lemma sum_ge_a_mul_nonsmall {g : ℤ → ℝ} {a : ℝ} {l r : ℤ} (hg : ∀ t : ℤ, 0 ≤ g t) :
    a * (((Finset.Icc l r).card : ℝ) - (smallCnt g a l r : ℝ)) ≤
      ∑ t ∈ Finset.Icc l r, g t := by
  have hNcard : ((Finset.Icc l r).filter (fun t : ℤ => a < g t)).card =
      (Finset.Icc l r).card - ((Finset.Icc l r).filter (fun t : ℤ => g t ≤ a)).card := by
    have hEq : (Finset.Icc l r).filter (fun t : ℤ => a < g t) =
        (Finset.Icc l r) \ (Finset.Icc l r).filter (fun t : ℤ => g t ≤ a) := by
      have h1 : (Finset.Icc l r).filter (fun t : ℤ => a < g t) =
          (Finset.Icc l r).filter (fun t : ℤ => ¬ g t ≤ a) := by
        ext t
        rw [Finset.mem_filter, Finset.mem_filter]
        constructor
        · intro h; exact ⟨h.1, not_le_of_gt h.2⟩
        · intro h; exact ⟨h.1, lt_of_not_ge h.2⟩
      rw [h1]
      exact Finset.filter_not (fun t : ℤ => g t ≤ a) (Finset.Icc l r)
    rw [hEq]
    rw [Finset.card_sdiff]
    have hsub : (Finset.Icc l r).filter (fun t : ℤ => g t ≤ a) ⊆ Finset.Icc l r :=
      Finset.filter_subset _ _
    rw [Finset.inter_eq_left.mpr hsub]
  have hNge : ((Finset.Icc l r).filter (fun t : ℤ => a < g t)).card * a ≤
      (∑ t ∈ (Finset.Icc l r).filter (fun t : ℤ => a < g t), g t) := by
    have hterm : ∀ t ∈ (Finset.Icc l r).filter (fun t : ℤ => a < g t), a ≤ g t := by
      intro t ht
      exact le_of_lt (Finset.mem_filter.mp ht).2
    have hsum := Finset.sum_le_sum hterm
    rwa [Finset.sum_const, nsmul_eq_mul] at hsum
  have hsum_nonneg : (0 : ℝ) ≤ ∑ t ∈ (Finset.Icc l r).filter (fun t : ℤ => ¬ a < g t), g t := by
    exact Finset.sum_nonneg (fun t ht => hg t)
  have hsub' : ((Finset.Icc l r).filter (fun t : ℤ => g t ≤ a)).card ≤ (Finset.Icc l r).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hsm : (((Finset.Icc l r).filter (fun t : ℤ => g t ≤ a)).card : ℝ) =
      (smallCnt g a l r : ℝ) := by
    rfl
  have hcast : ((Finset.Icc l r).filter (fun t : ℤ => a < g t)).card =
      ((Finset.Icc l r).card : ℝ) - (smallCnt g a l r : ℝ) := by
    have h0 := congrArg (fun x : ℕ => (x : ℝ)) hNcard
    rw [Nat.cast_sub hsub'] at h0
    rwa [hsm] at h0
  calc
    a * (((Finset.Icc l r).card : ℝ) - (smallCnt g a l r : ℝ)) =
        a * ((Finset.Icc l r).filter (fun t : ℤ => a < g t)).card := by rw [hcast]
    _ ≤ (∑ t ∈ (Finset.Icc l r).filter (fun t : ℤ => a < g t), g t) := by
      rwa [mul_comm]
    _ ≤ (∑ t ∈ (Finset.Icc l r).filter (fun t : ℤ => a < g t), g t) +
          (∑ t ∈ (Finset.Icc l r).filter (fun t : ℤ => ¬ a < g t), g t) := by linarith
    _ = ∑ t ∈ Finset.Icc l r, g t :=
      Finset.sum_filter_add_sum_filter_not (Finset.Icc l r) (fun t : ℤ => a < g t) (fun t => g t)


/-- `ilen` as a real equals `clen` when the interval is nonempty to the right. -/
lemma ilen_clen_real {l r : ℤ} (hl : l ≤ r) : (ilen l r : ℝ) = clen l r := by
  dsimp [ilen, clen]
  rw [Int.card_Icc]
  have hnon : (0 : ℤ) ≤ r - l + 1 := by omega
  have hz0 : ((r - l + 1 : ℤ).toNat : ℤ) = (r - l + 1 : ℤ) := Int.toNat_of_nonneg hnon
  have hcast : (((r - l + 1 : ℤ).toNat : ℕ) : ℝ) = ((r - l + 1 : ℤ) : ℝ) := by
    exact_mod_cast hz0
  have hE : ((r + 1 - l : ℤ).toNat : ℕ) = ((r - l + 1 : ℤ).toNat : ℕ) := by
    congr 1
    ring
  rw [hE]
  exact hcast

/-- The greedy right endpoint for the concrete parameters of Prop ell-2 update:
small fraction `δ = 8μ` and upper bound `hi2 := lo + 2N − 1`. -/
noncomputable def rEnd8 (g : ℤ → ℝ) (a μ : ℝ) (lo : ℤ) (N : ℕ) (l : ℤ) : ℤ :=
  rEnd g a (8 * μ) (lo + (2 : ℤ) * (N : ℤ) - 1) l

/-- a block with left endpoint `l` (a `2^{μ²}a`-large point in `I₀`) exists:
bounds, small-count upper bound and length bound. -/
theorem block_part1 {g : ℤ → ℝ} {a R μ : ℝ} {lo : ℤ} {N : ℕ} {l : ℤ}
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 64)
    (hR0 : 0 < R) (ha0 : 0 < a) (ha4R : 4 * R ≤ a)
    (hN1 : 1 ≤ N) (hg0 : ∀ t : ℤ, 0 ≤ g t)
    (hlip : Ell2Update.ratioLip (μ ^ 4) g)
    (hmass : (∑ t ∈ It lo N, g t) ≤ 2 * R * (N : ℝ))
    (hl : l ∈ I0 lo N)
    (hlarge : (2 : ℝ) ^ (μ ^ 2) * a ≤ g l) :
    l ≤ rEnd8 g a μ lo N l ∧
      rEnd8 g a μ lo N l ≤ lo + (2 : ℤ) * (N : ℤ) - 1 ∧
      (smallCnt g a l (rEnd8 g a μ lo N l) : ℝ) ≤ (8 * μ) * (ilen l (rEnd8 g a μ lo N l) : ℝ) ∧
      (ilen l (rEnd8 g a μ lo N l) : ℝ) ≤ (N : ℝ) := by
  let δ : ℝ := 8 * μ
  let hi2 : ℤ := lo + (2 : ℤ) * (N : ℤ) - 1
  let r : ℤ := rEnd8 g a μ lo N l
  have hδ0 : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ1 : δ ≤ 1 / 2 := by
    dsimp [δ]
    nlinarith [hμ1]
  have hl' : lo ≤ l ∧ l ≤ lo + (N : ℤ) - 1 := (mem_I0.mp hl)
  have ha_gl : a < g l := by
    have hg1 : (1 : ℝ) < (2 : ℝ) ^ (μ ^ 2) := Ell2Update.two_pow_gt_one (μ ^ 2) (by positivity)
    have hm : a < a * (2 : ℝ) ^ (μ ^ 2) := by
      simpa using (mul_lt_mul_of_pos_left hg1 ha0)
    have hle : a * (2 : ℝ) ^ (μ ^ 2) ≤ g l := by
      rw [mul_comm]
      exact hlarge
    linarith
  have h_l_hi2 : l ≤ hi2 := by
    dsimp [hi2]
    have hlo : l ≤ lo + (N : ℤ) - 1 := hl'.2
    have hNpos : (0 : ℤ) ≤ (N : ℤ) := by exact_mod_cast Nat.zero_le N
    omega
  have hr_eq : r = rEnd g a δ hi2 l := by
    dsimp [r, rEnd8, δ, hi2]
  have hcand : (cand g a δ hi2 l).Nonempty := by
    exact ⟨l, cand_mem_self hδ0.le ha_gl h_l_hi2⟩
  have hmem := rEnd_mem_Icc (g := g) (a := a) (δ := δ) (hi := hi2) (l := l) hcand
  have hl_r : l ≤ r := by
    rw [hr_eq]
    exact hmem.1
  have hr_hi2 : r ≤ hi2 := by
    rw [hr_eq]
    exact hmem.2
  have hsmall := rEnd_smallCnt (g := g) (a := a) (δ := δ) (hi := hi2) (l := l) hcand
  have hlenreal : (ilen l r : ℝ) = clen l r := ilen_clen_real hl_r
  have hsmall2 : (smallCnt g a l r : ℝ) ≤ δ * (ilen l r : ℝ) := by
    rw [hr_eq]
    calc
      (smallCnt g a l (rEnd g a δ hi2 l) : ℝ) ≤ δ * clen l (rEnd g a δ hi2 l) := hsmall
      _ = δ * (ilen l (rEnd g a δ hi2 l) : ℝ) := by
        rw [ilen_clen_real (rEnd_mem_Icc (g := g) (a := a) (δ := δ) (hi := hi2) (l := l) hcand).1]
  have hIcc_sub : Finset.Icc l r ⊆ It lo N := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    rw [mem_It]
    constructor
    · exact le_trans hl'.1 hx.1
    · exact le_trans hx.2 (by dsimp [hi2] at hr_hi2; exact hr_hi2)
  have hsum_le : (∑ t ∈ Finset.Icc l r, g t) ≤ ∑ t ∈ It lo N, g t :=
    sum_subset_le hg0 hIcc_sub
  have hsum_le2 : (∑ t ∈ Finset.Icc l r, g t) ≤ 2 * R * (N : ℝ) :=
    le_trans hsum_le hmass
  have hlower := sum_ge_a_mul_nonsmall (g := g) (a := a) (l := l) (r := r) hg0
  have hbig : ((Finset.Icc l r).card : ℝ) - (smallCnt g a l r : ℝ) ≥ (1 - δ) * (ilen l r : ℝ) := by
    have hI : (Finset.Icc l r).card = ilen l r := rfl
    rw [hI]
    nlinarith [hsmall2]
  have hfirst : a * ((1 - δ) * (ilen l r : ℝ)) ≤ 2 * R * (N : ℝ) := by
    have hmon : a * ((1 - δ) * (ilen l r : ℝ)) ≤ a * (((Finset.Icc l r).card : ℝ) - (smallCnt g a l r : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · exact hbig
      · exact le_of_lt ha0
    calc
      a * ((1 - δ) * (ilen l r : ℝ)) ≤ a * (((Finset.Icc l r).card : ℝ) - (smallCnt g a l r : ℝ)) := hmon
      _ ≤ ∑ t ∈ Finset.Icc l r, g t := hlower
      _ ≤ 2 * R * (N : ℝ) := hsum_le2
  have hlen0 : 0 ≤ (ilen l r : ℝ) := by exact_mod_cast Nat.zero_le _
  have hcoef : 2 * R * (ilen l r : ℝ) ≤ a * ((1 - δ) * (ilen l r : ℝ)) := by
    have hm2 : 2 * R * (ilen l r : ℝ) ≤ a * ((1 / 2) * (ilen l r : ℝ)) := by
      have hmain : 2 * R ≤ a * (1 / 2) := by
        have : a * (1 / 2) = a / 2 := by ring
        rw [this]
        nlinarith [ha4R, hR0]
      calc
        2 * R * (ilen l r : ℝ) ≤ (a * (1 / 2)) * (ilen l r : ℝ) :=
          mul_le_mul_of_nonneg_right hmain hlen0
        _ = a * ((1 / 2) * (ilen l r : ℝ)) := by ring
    have hδge : (1 : ℝ) / 2 ≤ 1 - δ := by linarith
    have hmul : a * ((1 / 2) * (ilen l r : ℝ)) ≤ a * ((1 - δ) * (ilen l r : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (by nlinarith) (le_of_lt ha0)
    linarith
  have hlen_le : (ilen l r : ℝ) ≤ (N : ℝ) := by
    have htot : 2 * R * (ilen l r : ℝ) ≤ 2 * R * (N : ℝ) := by
      calc
        2 * R * (ilen l r : ℝ) ≤ a * ((1 - δ) * (ilen l r : ℝ)) := hcoef
        _ ≤ 2 * R * (N : ℝ) := hfirst
    have hR : 0 < 2 * R := by positivity
    nlinarith
  have hsmall3 : (smallCnt g a l r : ℝ) ≤ (8 * μ) * (ilen l r : ℝ) := by
    simpa [δ] using hsmall2
  have hr_hi2' : r ≤ lo + (2 : ℤ) * (N : ℤ) - 1 := by
    simpa [hi2] using hr_hi2
  exact ⟨hl_r, hr_hi2', hsmall3, hlen_le⟩


/-- integer-argument version of `prefix_not_small`: every `t ∈ [l, l+q]` is not
small. -/
lemma prefix_not_small_int {g : ℤ → ℝ} {a μ : ℝ} {l : ℤ} {q : ℕ} {t : ℤ}
    (hμ0 : 0 < μ) (ha0 : 0 < a) (hlip : Ell2Update.ratioLip (μ ^ 4) g)
    (hlarge : (2 : ℝ) ^ (μ ^ 2) * a ≤ g l) (hq : (q : ℝ) ≤ 1 / (2 * μ ^ 2))
    (htl : l ≤ t) (htq : t ≤ l + (q : ℤ)) : a < g t := by
  let j : ℕ := Int.toNat (t - l)
  have hd0 : (0 : ℤ) ≤ t - l := by omega
  have hjd : (j : ℤ) = t - l := by
    dsimp [j]
    exact Int.toNat_of_nonneg hd0
  have hjq : j ≤ q := by
    have hjq' : (j : ℤ) ≤ (q : ℤ) := by
      calc
        (j : ℤ) = t - l := hjd
        _ ≤ (q : ℤ) := by omega
    exact_mod_cast hjq'
  have hg := prefix_not_small (g := g) (a := a) (μ := μ) (l := l) (j := j) (q := q)
    hμ0 ha0 hlip hlarge hjq hq
  have ht' : l + (j : ℤ) = t := by
    rw [hjd]
    omega
  rwa [ht'] at hg

/-- `clen` at `r+1` is `clen` at `r` plus one. -/
lemma clen_succ (l r : ℤ) : clen l (r + 1) = clen l r + 1 := by
  dsimp [clen]
  have hz : (r + 1 - l + 1 : ℤ) = (r - l + 1 : ℤ) + 1 := by omega
  rw [hz]
  norm_num
/-- integer version of `ilen`: `(ilen l r : ℤ) = r − l + 1` when `l ≤ r+1`. -/
lemma ilen_eq_int {l r : ℤ} (hl : l ≤ r + 1) : (ilen l r : ℤ) = r - l + 1 := by
  dsimp [ilen]
  rw [Int.card_Icc]
  have hnon : (0 : ℤ) ≤ r + 1 - l := by omega
  rw [Int.toNat_of_nonneg hnon]
  omega
/-- The full single-block property bundle for `rEnd8` (Prop ell-2 update):
`r` lies strictly inside `Ĩ`; the small-point count is within
`[δ|I'|/2, δ|I'|]` (`δ = 8μ`); and the length satisfies `N ≥ |I'| ≥ ⌊1/(2μ²)⌋+1`. -/
theorem block_core {g : ℤ → ℝ} {a R μ : ℝ} {lo : ℤ} {N : ℕ} {l : ℤ}
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 64)
    (hR0 : 0 < R) (ha0 : 0 < a) (ha4R : 4 * R ≤ a)
    (hN1 : 1 ≤ N) (hg0 : ∀ t : ℤ, 0 ≤ g t)
    (hlip : Ell2Update.ratioLip (μ ^ 4) g)
    (hmass : (∑ t ∈ It lo N, g t) ≤ 2 * R * (N : ℝ))
    (hl : l ∈ I0 lo N)
    (hlarge : (2 : ℝ) ^ (μ ^ 2) * a ≤ g l) :
    l ≤ rEnd8 g a μ lo N l ∧
      rEnd8 g a μ lo N l < lo + (2 : ℤ) * (N : ℤ) - 1 ∧
      (smallCnt g a l (rEnd8 g a μ lo N l) : ℝ) ≤ (8 * μ) * (ilen l (rEnd8 g a μ lo N l) : ℝ) ∧
      (8 * μ) * (ilen l (rEnd8 g a μ lo N l) : ℝ) / 2 ≤
        (smallCnt g a l (rEnd8 g a μ lo N l) : ℝ) ∧
      (ilen l (rEnd8 g a μ lo N l) : ℝ) ≤ (N : ℝ) ∧
      (Nat.floor (1 / (2 * μ ^ 2)) + 1 ≤ ilen l (rEnd8 g a μ lo N l)) := by
  let E : ℤ := rEnd8 g a μ lo N l
  let hi2 : ℤ := lo + (2 : ℤ) * (N : ℤ) - 1
  let δ : ℝ := 8 * μ
  have hδ0 : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ1 : δ ≤ 1 / 2 := by
    dsimp [δ]
    nlinarith [hμ1]
  have hμ2 : μ ≤ 2 := by linarith
  have hl' : lo ≤ l ∧ l ≤ lo + (N : ℤ) - 1 := (mem_I0.mp hl)
  have ha_gl : a < g l := by
    have hg1 : (1 : ℝ) < (2 : ℝ) ^ (μ ^ 2) := Ell2Update.two_pow_gt_one (μ ^ 2) (by positivity)
    have hm : a < a * (2 : ℝ) ^ (μ ^ 2) := by
      simpa using (mul_lt_mul_of_pos_left hg1 ha0)
    have hle : a * (2 : ℝ) ^ (μ ^ 2) ≤ g l := by
      rw [mul_comm]
      exact hlarge
    linarith
  have h_l_hi2 : l ≤ hi2 := by
    dsimp [hi2]
    have hlo : l ≤ lo + (N : ℤ) - 1 := hl'.2
    have hNpos : (0 : ℤ) ≤ (N : ℤ) := by exact_mod_cast Nat.zero_le N
    omega
  have hcand : (cand g a δ hi2 l).Nonempty := by
    exact ⟨l, cand_mem_self hδ0.le ha_gl h_l_hi2⟩
  have hb := block_part1 (g := g) (a := a) (R := R) (μ := μ) (lo := lo) (N := N) (l := l)
    hμ0 hμ1 hR0 ha0 ha4R hN1 hg0 hlip hmass hl hlarge
  rcases hb with ⟨hl_E, hE_hi2, hsmallE, hlenE⟩
  -- (i) strict containment: E < hi2
  have hrlt : E < hi2 := by
    by_contra h
    have hge : hi2 ≤ E := le_of_not_gt h
    have hEeq : E = hi2 := le_antisymm (by simpa [E, hi2] using hE_hi2) hge
    have hIbig : (N : ℝ) + 1 ≤ (ilen l hi2 : ℝ) := by
      have hIeq : (ilen l hi2 : ℤ) = hi2 - l + 1 := by
        exact ilen_eq_int (l := l) (r := hi2) (by omega)
      have hz : (N : ℤ) + 1 ≤ hi2 - l + 1 := by
        dsimp [hi2]
        omega
      have hzI : (N : ℤ) + 1 ≤ (ilen l hi2 : ℤ) := by
        rwa [hIeq]
      exact_mod_cast hzI
    have hle2 : (ilen l hi2 : ℝ) ≤ (N : ℝ) := by
      change (ilen l E : ℝ) ≤ (N : ℝ) at hlenE
      rwa [hEeq] at hlenE
    linarith
  have hEend : rEnd g a δ hi2 l = E := by
    dsimp [E, rEnd8, δ, hi2]
  -- (ii) small-count upper bound
  have hsmallE2 : (smallCnt g a l E : ℝ) ≤ δ * (ilen l E : ℝ) := by
    change (smallCnt g a l E : ℝ) ≤ (8 * μ) * (ilen l E : ℝ) at hsmallE
    simpa [δ] using hsmallE
  -- (iii) length lower bound ⌊1/(2μ²)⌋+1 ≤ |I'|
  let q : ℕ := Nat.floor (1 / (2 * μ ^ 2))
  have hq : (q : ℝ) ≤ 1 / (2 * μ ^ 2) := Nat.floor_le (by positivity)
  have hlen_ge : q + 1 ≤ ilen l E := by
    by_contra h
    have hleq : ilen l E ≤ q := by omega
    have hsmall_r1 : smallCnt g a l (E + 1) = 0 := by
      dsimp [smallCnt]
      rw [Finset.card_eq_zero]
      rw [Finset.filter_eq_empty_iff]
      intro x hx hgx
      have hx1 : l ≤ x := (Finset.mem_Icc.mp hx).1
      have hx2 : x ≤ E + 1 := (Finset.mem_Icc.mp hx).2
      have hxq : x ≤ l + (q : ℤ) := by
        have hIeq : (ilen l E : ℤ) = E - l + 1 := by
          exact ilen_eq_int (l := l) (r := E) (by omega)
        have hxq' : x - l ≤ (q : ℤ) := by
          calc
            x - l ≤ E + 1 - l := by omega
            _ = (ilen l E : ℤ) := by
              rw [hIeq]
              ring
            _ ≤ (q : ℤ) := by exact_mod_cast hleq
        omega
      exact (not_le_of_gt (prefix_not_small_int (g := g) (a := a) (μ := μ) (l := l) (q := q)
        hμ0 ha0 hlip hlarge hq hx1 hxq)) hgx
    have hviol := rEnd_succ_violates (g := g) (a := a) (δ := δ) (hi := hi2) (l := l) hcand
      (by simpa [E, hi2, rEnd8, δ] using hrlt)
    have hsmall_r1r : (smallCnt g a l (E + 1) : ℝ) = 0 := by
      rw [hsmall_r1]
      norm_num
    rw [hEend, clen_succ] at hviol
    have hclen_pos : 0 < clen l E := by
      have hcl : (ilen l E : ℝ) = clen l E := ilen_clen_real (by simpa [E] using hl_E)
      have hpos : 0 < (ilen l E : ℝ) := by
        have hne : ilen l E ≠ 0 := by
          intro hz
          have hI := ilen_eq_int (l := l) (r := E) (by omega)
          rw [hz] at hI
          norm_num at hI
          omega
        exact_mod_cast Nat.pos_of_ne_zero hne
      linarith
    nlinarith [hclen_pos]
  -- (iv) small-count lower bound δ·|I'|/2 ≤ smallCnt
  have hδlen : 2 ≤ δ * (ilen l E : ℝ) := by
    have hq1 : (q : ℝ) + 1 ≤ (ilen l E : ℝ) := by exact_mod_cast hlen_ge
    have hδq1 : δ * ((q : ℝ) + 1) ≤ δ * (ilen l E : ℝ) := by
      exact mul_le_mul_of_nonneg_left hq1 hδ0.le
    have hq2 : (1 : ℝ) / (2 * μ ^ 2) < (q : ℝ) + 1 := Nat.lt_floor_add_one (1 / (2 * μ ^ 2))
    have hδq : 2 < δ * ((q : ℝ) + 1) := by
      have hm := mul_lt_mul_of_pos_left hq2 hδ0
      have h4 : 2 ≤ 4 / μ := by
        exact (le_div_iff₀ hμ0).2 (by nlinarith [hμ2])
      have hred : δ * (1 / (2 * μ ^ 2)) = 4 / μ := by
        dsimp [δ]
        field_simp [hμ0.ne']
        ring
      have hδx : δ * (1 / (2 * μ ^ 2)) < δ * ((q : ℝ) + 1) := hm
      nlinarith
    nlinarith
  have hsucc := smallCnt_succ_le (g := g) (a := a) (l := l) (t := E)
  have hviol2 := rEnd_succ_violates (g := g) (a := a) (δ := δ) (hi := hi2) (l := l) hcand
    (by simpa [E, hi2, rEnd8, δ] using hrlt)
  have hsmall_lower : δ * (ilen l E : ℝ) / 2 ≤ (smallCnt g a l E : ℝ) := by
    rw [hEend, clen_succ] at hviol2
    have hsuccR : (smallCnt g a l (E + 1) : ℝ) ≤ (smallCnt g a l E : ℝ) + 1 := by
      exact_mod_cast hsucc
    have hclenE : clen l E = (ilen l E : ℝ) := (ilen_clen_real (by simpa [E] using hl_E)).symm
    have hδ1' : δ ≤ 1 / 2 := hδ1
    nlinarith
  -- assemble
  change l ≤ E ∧ E < hi2 ∧
      (smallCnt g a l E : ℝ) ≤ (8 * μ) * (ilen l E : ℝ) ∧
      (8 * μ) * (ilen l E : ℝ) / 2 ≤ (smallCnt g a l E : ℝ) ∧
      (ilen l E : ℝ) ≤ (N : ℝ) ∧ (Nat.floor (1 / (2 * μ ^ 2)) + 1 ≤ ilen l E)
  have hsmall_hi3 : (smallCnt g a l E : ℝ) ≤ (8 * μ) * (ilen l E : ℝ) := by
    simpa [δ] using hsmallE2
  have hsmall_lo3 : (8 * μ) * (ilen l E : ℝ) / 2 ≤ (smallCnt g a l E : ℝ) := by
    simpa [δ] using hsmall_lower
  exact ⟨by simpa [E] using hl_E, hrlt, hsmall_hi3, hsmall_lo3, (by simpa [E] using hlenE), hlen_ge⟩



/-- Greedy covering of a sorted list of "large" points of `I₀`: each block
`(x, r)` starts at a large point `x` and ends at `rEnd8 … x`; the remaining
points (strictly beyond `r`) are covered recursively.  Pairwise-disjoint,
ordered blocks; the union covers every element of the input list. -/
noncomputable def coverBlocks (g : ℤ → ℝ) (a μ : ℝ) (lo : ℤ) (N : ℕ) :
    List ℤ → List (ℤ × ℤ)
  | [] => []
  | x :: xs =>
      let r := rEnd8 g a μ lo N x
      (x, r) :: coverBlocks g a μ lo N (xs.filter (fun y : ℤ => decide (r < y)))
termination_by l => l.length
decreasing_by
  simp_wf
  have h := List.length_filter_le (fun x : {x : ℤ // x ∈ xs} =>
    decide (r < (x : ℤ))) xs.attach
  simpa using h

/-- unfolding at the empty list. -/
lemma coverBlocks_nil (g : ℤ → ℝ) (a μ : ℝ) (lo : ℤ) (N : ℕ) :
    coverBlocks g a μ lo N [] = [] := by
  simp [coverBlocks]

/-- unfolding at a nonempty list. -/
lemma coverBlocks_cons (g : ℤ → ℝ) (a μ : ℝ) (lo : ℤ) (N : ℕ) (x : ℤ) (xs : List ℤ) :
    coverBlocks g a μ lo N (x :: xs) =
      (x, rEnd8 g a μ lo N x) ::
        coverBlocks g a μ lo N (xs.filter (fun y : ℤ => decide (rEnd8 g a μ lo N x < y))) := by
  simp [coverBlocks]

/-- a valid start for a greedy block: a large point of `I₀`. -/
def goodStart (g : ℤ → ℝ) (a μ : ℝ) (lo : ℤ) (N : ℕ) (x : ℤ) : Prop :=
  x ∈ I0 lo N ∧ (2 : ℝ) ^ (μ ^ 2) * a ≤ g x

/-- the left point of every block is an element of the input list and the right
point is the canonical `rEnd8` of the left point. -/
lemma coverBlocks_pair {g : ℤ → ℝ} {a μ : ℝ} {lo : ℤ} {N : ℕ} :
    ∀ L : List ℤ, ∀ b ∈ coverBlocks g a μ lo N L,
      b.1 ∈ L ∧ b.2 = rEnd8 g a μ lo N b.1 := by
  have hrec : ∀ n : ℕ, ∀ L : List ℤ, L.length ≤ n →
      ∀ b ∈ coverBlocks g a μ lo N L, b.1 ∈ L ∧ b.2 = rEnd8 g a μ lo N b.1 := by
    intro n
    induction n with
    | zero =>
        intro L hL b hb
        have hL' : L = [] := by
          cases L with
          | nil => rfl
          | cons y ys =>
              exfalso
              simp at hL
        subst L
        simp [coverBlocks] at hb
    | succ n ih =>
        intro L hL b hb
        cases L with
        | nil => simp [coverBlocks] at hb
        | cons x xs =>
            rw [coverBlocks_cons] at hb
            rw [List.mem_cons] at hb
            rcases hb with hb | hb
            · subst b
              exact ⟨by simp, rfl⟩
            · have hlen : (xs.filter (fun y : ℤ => decide (rEnd8 g a μ lo N x < y))).length ≤ n := by
                have h1 : (xs.filter (fun y : ℤ => decide (rEnd8 g a μ lo N x < y))).length ≤ xs.length :=
                  List.length_filter_le _ _
                have h2 : xs.length ≤ n := by
                  have hx : (x :: xs).length = xs.length + 1 := by simp
                  rw [hx] at hL
                  omega
                omega
              have hm := ih (xs.filter (fun y : ℤ => decide (rEnd8 g a μ lo N x < y))) hlen b hb
              exact ⟨List.mem_cons_of_mem x (List.mem_of_mem_filter hm.1), hm.2⟩
  intro L b hb
  exact hrec L.length L (le_rfl) b hb

/-- the left point of every block is an element of the input list. -/
lemma coverBlocks_left_mem {g : ℤ → ℝ} {a μ : ℝ} {lo : ℤ} {N : ℕ} {L : List ℤ} :
    ∀ b ∈ coverBlocks g a μ lo N L, b.1 ∈ L := by
  intro b hb
  exact (coverBlocks_pair L b hb).1

/-- the right point of every block is the canonical `rEnd8` of its left point. -/
lemma coverBlocks_right_eq {g : ℤ → ℝ} {a μ : ℝ} {lo : ℤ} {N : ℕ} {L : List ℤ} :
    ∀ b ∈ coverBlocks g a μ lo N L, b.2 = rEnd8 g a μ lo N b.1 := by
  intro b hb
  exact (coverBlocks_pair L b hb).2

/-- all blocks start from good starts when the input list does. -/
lemma coverBlocks_good {g : ℤ → ℝ} {a μ : ℝ} {lo : ℤ} {N : ℕ} {L : List ℤ}
    (hgood : ∀ x ∈ L, goodStart g a μ lo N x) :
    ∀ b ∈ coverBlocks g a μ lo N L, goodStart g a μ lo N b.1 := by
  intro b hb
  exact hgood b.1 (coverBlocks_left_mem b hb)

/-- the full `block_core` bundle for every block of the covering, given the
ambient hypotheses and that every input element is a good start. -/
theorem coverBlocks_block_core {g : ℤ → ℝ} {a R μ : ℝ} {lo : ℤ} {N : ℕ} {L : List ℤ}
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 64)
    (hR0 : 0 < R) (ha0 : 0 < a) (ha4R : 4 * R ≤ a)
    (hN1 : 1 ≤ N) (hg0 : ∀ t : ℤ, 0 ≤ g t)
    (hlip : Ell2Update.ratioLip (μ ^ 4) g)
    (hmass : (∑ t ∈ It lo N, g t) ≤ 2 * R * (N : ℝ))
    (hgood : ∀ x ∈ L, goodStart g a μ lo N x) :
    ∀ b ∈ coverBlocks g a μ lo N L,
      let x := b.1
      let r := b.2
      x ≤ r ∧ r < lo + (2 : ℤ) * (N : ℤ) - 1 ∧
        (smallCnt g a x r : ℝ) ≤ (8 * μ) * (ilen x r : ℝ) ∧
        (8 * μ) * (ilen x r : ℝ) / 2 ≤ (smallCnt g a x r : ℝ) ∧
        (ilen x r : ℝ) ≤ (N : ℝ) ∧
        (Nat.floor (1 / (2 * μ ^ 2)) + 1 ≤ ilen x r) := by
  intro b hb
  have hr : b.2 = rEnd8 g a μ lo N b.1 := coverBlocks_right_eq b hb
  rcases (coverBlocks_good (L := L) hgood) b hb with ⟨hl0, hlarge⟩
  have hcore := block_core (g := g) (a := a) (R := R) (μ := μ) (lo := lo) (N := N)
    (l := b.1) hμ0 hμ1 hR0 ha0 ha4R hN1 hg0 hlip hmass hl0 hlarge
  change b.1 ≤ rEnd8 g a μ lo N b.1 ∧
      rEnd8 g a μ lo N b.1 < lo + (2 : ℤ) * (N : ℤ) - 1 ∧
      (smallCnt g a b.1 (rEnd8 g a μ lo N b.1) : ℝ) ≤ (8 * μ) * (ilen b.1 (rEnd8 g a μ lo N b.1) : ℝ) ∧
      (8 * μ) * (ilen b.1 (rEnd8 g a μ lo N b.1) : ℝ) / 2 ≤
        (smallCnt g a b.1 (rEnd8 g a μ lo N b.1) : ℝ) ∧
      (ilen b.1 (rEnd8 g a μ lo N b.1) : ℝ) ≤ (N : ℝ) ∧
      (Nat.floor (1 / (2 * μ ^ 2)) + 1 ≤ ilen b.1 (rEnd8 g a μ lo N b.1)) at hcore
  rwa [← hr] at hcore



/-- every point is at most its own greedy right endpoint (even degenerate). -/
lemma le_rEnd8_self (g : ℤ → ℝ) (a μ : ℝ) (lo : ℤ) (N : ℕ) (x : ℤ) :
    x ≤ rEnd8 g a μ lo N x := by
  dsimp [rEnd8]
  unfold rEnd
  by_cases h : (cand g a (8 * μ) (lo + (2 : ℤ) * (N : ℤ) - 1) x).Nonempty
  · rw [dif_pos h]
    have hm := Finset.max'_mem (cand g a (8 * μ) (lo + (2 : ℤ) * (N : ℤ) - 1) x) h
    rw [mem_cand_iff] at hm
    exact (Finset.mem_Icc.mp hm.1).1
  · rw [dif_neg h]

/-- coverage: every element of an ascending input list lies in the interval of
some block of the greedy covering. -/
lemma coverBlocks_coverage {g : ℤ → ℝ} {a μ : ℝ} {lo : ℤ} {N : ℕ} :
    ∀ L : List ℤ, List.Pairwise (fun a b : ℤ => a ≤ b) L →
      ∀ x : ℤ, x ∈ L → ∃ b ∈ coverBlocks g a μ lo N L, x ∈ Finset.Icc b.1 b.2 := by
  have hrec : ∀ n : ℕ, ∀ L : List ℤ, L.length ≤ n →
      List.Pairwise (fun a b : ℤ => a ≤ b) L →
      ∀ x : ℤ, x ∈ L → ∃ b ∈ coverBlocks g a μ lo N L, x ∈ Finset.Icc b.1 b.2 := by
    intro n
    induction n with
    | zero =>
        intro L hL hs x hx
        have hL' : L = [] := by
          cases L with
          | nil => rfl
          | cons y ys => exfalso; simp at hL
        subst L
        simp at hx
    | succ n ih =>
        intro L hL hs x hx
        cases L with
        | nil => simp [coverBlocks] at hx
        | cons y ys =>
            by_cases hxy : x = y
            · subst x
              rw [coverBlocks_cons]
              refine ⟨(y, rEnd8 g a μ lo N y), ?_, ?_⟩
              · simp
              · rw [Finset.mem_Icc]
                exact ⟨le_rfl, le_rEnd8_self g a μ lo N y⟩
            · have hxys : x ∈ ys := by
                rw [List.mem_cons] at hx
                exact hx.resolve_left hxy
              by_cases hxr : x ≤ rEnd8 g a μ lo N y
              · rw [coverBlocks_cons]
                refine ⟨(y, rEnd8 g a μ lo N y), ?_, ?_⟩
                · simp
                · rw [Finset.mem_Icc]
                  constructor
                  · have hp := (List.pairwise_cons.mp hs).1
                    exact hp x hxys
                  · exact hxr
              · have hrx : rEnd8 g a μ lo N y < x := lt_of_not_ge hxr
                have hxfil : x ∈ ys.filter (fun z : ℤ => decide (rEnd8 g a μ lo N y < z)) := by
                  rw [List.mem_filter]
                  exact ⟨hxys, decide_eq_true hrx⟩
                have hlen : (ys.filter (fun z : ℤ => decide (rEnd8 g a μ lo N y < z))).length ≤ n := by
                  have h1 : (ys.filter (fun z : ℤ => decide (rEnd8 g a μ lo N y < z))).length ≤ ys.length :=
                    List.length_filter_le _ _
                  have h2 : ys.length ≤ n := by
                    have hyy : (y :: ys).length = ys.length + 1 := by simp
                    rw [hyy] at hL
                    omega
                  omega
                have hsf : List.Pairwise (fun a b : ℤ => a ≤ b)
                    (ys.filter (fun z : ℤ => decide (rEnd8 g a μ lo N y < z))) :=
                  List.Pairwise.filter (fun z : ℤ => decide (rEnd8 g a μ lo N y < z))
                    (List.pairwise_cons.mp hs).2
                have hrec' := ih (ys.filter (fun z : ℤ => decide (rEnd8 g a μ lo N y < z))) hlen hsf x hxfil
                rcases hrec' with ⟨b, hb, hxb⟩
                rw [coverBlocks_cons]
                exact ⟨b, by simp [hb], hxb⟩
  intro L hs x hx
  exact hrec L.length L (le_rfl) hs x hx



/-- blocks of the covering are separated: an earlier block's right end is
strictly below the left point of every later block. -/
lemma coverBlocks_pairwise_sep {g : ℤ → ℝ} {a μ : ℝ} {lo : ℤ} {N : ℕ} :
    ∀ L : List ℤ, List.Pairwise (fun b₁ b₂ : ℤ × ℤ => b₁.2 < b₂.1)
      (coverBlocks g a μ lo N L) := by
  have hrec : ∀ n : ℕ, ∀ L : List ℤ, L.length ≤ n →
      List.Pairwise (fun b₁ b₂ : ℤ × ℤ => b₁.2 < b₂.1) (coverBlocks g a μ lo N L) := by
    intro n
    induction n with
    | zero =>
        intro L hL
        have hL' : L = [] := by
          cases L with
          | nil => rfl
          | cons y ys => exfalso; simp at hL
        subst L
        rw [coverBlocks_nil]
        exact List.Pairwise.nil
    | succ n ih =>
        intro L hL
        cases L with
        | nil => rw [coverBlocks_nil]; exact List.Pairwise.nil
        | cons y ys =>
            rw [coverBlocks_cons]
            rw [List.pairwise_cons]
            constructor
            · intro b hb
              rcases coverBlocks_pair (L := ys.filter (fun z : ℤ => decide (rEnd8 g a μ lo N y < z))) b hb with ⟨hmem, _⟩
              rw [List.mem_filter] at hmem
              have hd0 : decide (rEnd8 g a μ lo N y < b.1) = true := hmem.2
              have hd : rEnd8 g a μ lo N y < b.1 := by
                rwa [decide_eq_true_iff] at hd0
              exact hd
            · have hlen : (ys.filter (fun z : ℤ => decide (rEnd8 g a μ lo N y < z))).length ≤ n := by
                have h1 : (ys.filter (fun z : ℤ => decide (rEnd8 g a μ lo N y < z))).length ≤ ys.length :=
                  List.length_filter_le _ _
                have h2 : ys.length ≤ n := by
                  have hyy : (y :: ys).length = ys.length + 1 := by simp
                  rw [hyy] at hL
                  omega
                omega
              exact ih (ys.filter (fun z : ℤ => decide (rEnd8 g a μ lo N y < z))) hlen
  intro L
  exact hrec L.length L (le_rfl)

/-- the finset of "large" points of `I₀` (value ≥ `2^{μ²}a`). -/
noncomputable def largeFinset (g : ℤ → ℝ) (a μ : ℝ) (lo : ℤ) (N : ℕ) : Finset ℤ :=
  (I0 lo N).filter (fun t : ℤ => decide ((2 : ℝ) ^ (μ ^ 2) * a ≤ g t))

/-- the sorted ascending list of the large points of `I₀`. -/
noncomputable def largeSorted (g : ℤ → ℝ) (a μ : ℝ) (lo : ℤ) (N : ℕ) : List ℤ :=
  (largeFinset g a μ lo N).sort (fun x y : ℤ => x ≤ y)

/-- membership in `largeSorted`. -/
lemma mem_largeSorted {g : ℤ → ℝ} {a μ : ℝ} {lo : ℤ} {N : ℕ} {x : ℤ} :
    x ∈ largeSorted g a μ lo N ↔ x ∈ I0 lo N ∧ (2 : ℝ) ^ (μ ^ 2) * a ≤ g x := by
  dsimp [largeSorted, largeFinset]
  rw [Finset.mem_sort (fun x y : ℤ => x ≤ y)]
  rw [Finset.mem_filter]
  simp only [decide_eq_true_eq]

/-- `largeSorted` is ascending. -/
lemma sorted_largeSorted (g : ℤ → ℝ) (a μ : ℝ) (lo : ℤ) (N : ℕ) :
    List.Pairwise (fun x y : ℤ => x ≤ y) (largeSorted g a μ lo N) := by
  dsimp [largeSorted, largeFinset]
  exact Finset.pairwise_sort (largeFinset g a μ lo N) (fun x y : ℤ => x ≤ y)

/-- no duplicates in `largeSorted`. -/
lemma nodup_largeSorted (g : ℤ → ℝ) (a μ : ℝ) (lo : ℤ) (N : ℕ) :
    (largeSorted g a μ lo N).Nodup := by
  dsimp [largeSorted, largeFinset]
  exact Finset.sort_nodup (largeFinset g a μ lo N) (fun x y : ℤ => x ≤ y)

/-- length of `largeSorted` is the number of large points. -/
lemma length_largeSorted (g : ℤ → ℝ) (a μ : ℝ) (lo : ℤ) (N : ℕ) :
    (largeSorted g a μ lo N).length = (largeFinset g a μ lo N).card := by
  dsimp [largeSorted, largeFinset]
  exact Finset.length_sort (fun x y : ℤ => x ≤ y)



/-- every large point lies in `largeSorted`. -/
lemma mem_largeSorted_of_mem {g : ℤ → ℝ} {a μ : ℝ} {lo : ℤ} {N : ℕ} {x : ℤ}
    (hx : x ∈ largeFinset g a μ lo N) : x ∈ largeSorted g a μ lo N := by
  rw [mem_largeSorted]
  dsimp [largeFinset] at hx
  rw [Finset.mem_filter] at hx
  exact ⟨hx.1, decide_eq_true_iff.mp hx.2⟩

/-- (counting export of the family construction) the total length of all blocks
of the greedy covering of the large points is at least the number of large
points. -/
theorem blocks_total_len_ge_large {g : ℤ → ℝ} {a μ : ℝ} {lo : ℤ} {N : ℕ} :
    (largeFinset g a μ lo N).card ≤
      ∑ b ∈ (coverBlocks g a μ lo N (largeSorted g a μ lo N)).toFinset,
        ilen b.1 b.2 := by
  let L : List ℤ := largeSorted g a μ lo N
  let B : List (ℤ × ℤ) := coverBlocks g a μ lo N L
  have hcov : ∀ x : ℤ, x ∈ largeFinset g a μ lo N →
      ∃ b ∈ B, x ∈ Finset.Icc b.1 b.2 := by
    intro x hx
    have hxL : x ∈ L := by
      dsimp [L]
      exact mem_largeSorted_of_mem hx
    rcases coverBlocks_coverage (L := L) (sorted_largeSorted g a μ lo N) x hxL with ⟨b, hb, hxb⟩
    exact ⟨b, by simpa [B] using hb, hxb⟩
  have hsub : largeFinset g a μ lo N ⊆
      B.toFinset.biUnion (fun b : ℤ × ℤ => Finset.Icc b.1 b.2) := by
    intro x hx
    rcases hcov x hx with ⟨b, hb, hxb⟩
    rw [Finset.mem_biUnion]
    exact ⟨b, by simpa [B] using (List.mem_toFinset.mpr hb), hxb⟩
  have hcard1 : (largeFinset g a μ lo N).card ≤
      (B.toFinset.biUnion (fun b : ℤ × ℤ => Finset.Icc b.1 b.2)).card :=
    Finset.card_le_card hsub
  have hcard2 : (B.toFinset.biUnion (fun b : ℤ × ℤ => Finset.Icc b.1 b.2)).card ≤
      ∑ b ∈ B.toFinset, (Finset.Icc b.1 b.2).card := by
    exact Finset.card_biUnion_le (s := B.toFinset) (t := fun b : ℤ × ℤ => Finset.Icc b.1 b.2)
  have hcard3 : (∑ b ∈ B.toFinset, (Finset.Icc b.1 b.2).card) =
      ∑ b ∈ B.toFinset, ilen b.1 b.2 := by
    apply Finset.sum_congr rfl
    intro b hb
    rfl
  calc
    (largeFinset g a μ lo N).card ≤
        (B.toFinset.biUnion (fun b : ℤ × ℤ => Finset.Icc b.1 b.2)).card := hcard1
    _ ≤ ∑ b ∈ B.toFinset, (Finset.Icc b.1 b.2).card := hcard2
    _ = ∑ b ∈ B.toFinset, ilen b.1 b.2 := hcard3



/-- the `j`-th shell lower value `4R·2^{jμ²}`. -/
def shellVal (R μ : ℝ) (j : ℕ) : ℝ := 4 * R * (2 : ℝ) ^ ((j : ℝ) * μ ^ 2)

/-- the `j`-th shell: points of `Ĩ` whose value lies in `(a_j, 2^{μ²}·a_j]`. -/
def shell (g : ℤ → ℝ) (R μ : ℝ) (lo : ℤ) (N : ℕ) (j : ℕ) : Finset ℤ :=
  (It lo N).filter (fun t : ℤ =>
    shellVal R μ j < g t ∧ g t ≤ (2 : ℝ) ^ (μ ^ 2) * shellVal R μ j)

/-- membership in a shell. -/
lemma mem_shell_iff {g : ℤ → ℝ} {R μ : ℝ} {lo : ℤ} {N : ℕ} {j : ℕ} {t : ℤ} :
    t ∈ shell g R μ lo N j ↔
      t ∈ It lo N ∧ shellVal R μ j < g t ∧ g t ≤ (2 : ℝ) ^ (μ ^ 2) * shellVal R μ j := by
  dsimp [shell]
  rw [Finset.mem_filter]

/-- shells are contained in `Ĩ`. -/
lemma shell_subset_It {g : ℤ → ℝ} {R μ : ℝ} {lo : ℤ} {N : ℕ} (j : ℕ) :
    shell g R μ lo N j ⊆ It lo N := by
  intro t ht
  exact (mem_shell_iff.mp ht).1

/-- next shell lower value is `2^{μ²}` times the current one. -/
lemma shellVal_succ (R μ : ℝ) (j : ℕ) :
    shellVal R μ (j + 1) = (2 : ℝ) ^ (μ ^ 2) * shellVal R μ j := by
  dsimp [shellVal]
  have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by
    norm_num [Nat.cast_add]
  rw [hcast]
  have hpow : (2 : ℝ) ^ (((j : ℝ) + 1) * μ ^ 2) = (2 : ℝ) ^ ((j : ℝ) * μ ^ 2) * (2 : ℝ) ^ (μ ^ 2) := by
    rw [Ell2Update.rpow_two_add]
    congr 1
    ring
  rw [hpow]
  ring

/-- shell values are monotone in the index (for nonnegative `R`). -/
lemma shellVal_mono {R μ : ℝ} (hR : 0 ≤ R) {j₁ j₂ : ℕ} (hj : j₁ ≤ j₂) :
    shellVal R μ j₁ ≤ shellVal R μ j₂ := by
  dsimp [shellVal]
  have he : (j₁ : ℝ) * μ ^ 2 ≤ (j₂ : ℝ) * μ ^ 2 := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (by positivity)
  have hpow : (2 : ℝ) ^ ((j₁ : ℝ) * μ ^ 2) ≤ (2 : ℝ) ^ ((j₂ : ℝ) * μ ^ 2) :=
    Ell2Update.rpow_two_mono he
  have h40 : 0 ≤ 4 * R := by positivity
  exact mul_le_mul_of_nonneg_left hpow h40

/-- shells with distinct indices are disjoint. -/
lemma shell_disjoint {g : ℤ → ℝ} {R μ : ℝ} {lo : ℤ} {N : ℕ} (hR : 0 < R)
    {j₁ j₂ : ℕ} (hj : j₁ < j₂) : Disjoint (shell g R μ lo N j₁) (shell g R μ lo N j₂) := by
  rw [Finset.disjoint_left]
  intro t ht1 ht2
  have ht1' := mem_shell_iff.mp ht1
  have ht2' := mem_shell_iff.mp ht2
  have hsucc : (2 : ℝ) ^ (μ ^ 2) * shellVal R μ j₁ = shellVal R μ (j₁ + 1) :=
    (shellVal_succ R μ j₁).symm
  have hj12 : j₁ + 1 ≤ j₂ := by omega
  have hmono : shellVal R μ (j₁ + 1) ≤ shellVal R μ j₂ :=
    shellVal_mono (le_of_lt hR) hj12
  have hsep : (2 : ℝ) ^ (μ ^ 2) * shellVal R μ j₁ ≤ shellVal R μ j₂ := by
    rwa [hsucc]
  linarith [ht1'.2.2, ht2'.2.1, hsep]

/-- total number of shell points (first `K` shells) is at most `|Ĩ|`. -/
lemma sum_shell_card_le_It {g : ℤ → ℝ} {R μ : ℝ} {lo : ℤ} {N : ℕ} (hR : 0 < R) (K : ℕ) :
    (∑ j ∈ Finset.range K, ((shell g R μ lo N j).card : ℝ)) ≤ (2 * (N : ℝ)) := by
  have hdisj : (↑(Finset.range K) : Set ℕ).PairwiseDisjoint (shell g R μ lo N) := by
    intro j hj k hk hne
    by_cases hjk : j < k
    · exact shell_disjoint hR hjk
    · have hkj : k < j := by omega
      exact (shell_disjoint hR hkj).symm
  have hcard := Finset.card_biUnion (s := Finset.range K) (t := shell g R μ lo N) hdisj
  -- Σ_{j<K} |shell j| = |⋃_{j<K} shell j| ≤ |It lo N| = 2N
  have hsub : (Finset.range K).biUnion (shell g R μ lo N) ⊆ It lo N := by
    rw [Finset.biUnion_subset]
    intro j hj
    exact shell_subset_It (g := g) (R := R) (μ := μ) (lo := lo) (N := N) j
  have hle1 : (∑ j ∈ Finset.range K, (shell g R μ lo N j).card) ≤ (It lo N).card := by
    rw [← hcard]
    exact Finset.card_le_card hsub
  have hle2 : ((∑ j ∈ Finset.range K, (shell g R μ lo N j).card) : ℝ) ≤ ((It lo N).card : ℝ) := by
    exact_mod_cast hle1
  have hIt : ((It lo N).card : ℝ) = 2 * (N : ℝ) := by
    rw [card_It]
    norm_num
  rwa [hIt] at hle2

/-- pigeonhole: some shell among the first `K` has at most `2|Ĩ|/K` points. -/
lemma exists_shell_small {g : ℤ → ℝ} {R μ : ℝ} {lo : ℤ} {N : ℕ} (hR : 0 < R)
    (K : ℕ) (hK : 0 < K) : ∃ j < K, ((shell g R μ lo N j).card : ℝ) ≤ 2 * (N : ℝ) / (K : ℝ) := by
  by_contra h
  have hall : ∀ j < K, 2 * (N : ℝ) / (K : ℝ) < (shell g R μ lo N j).card := by
    intro j hj
    have hnot : ¬ ((shell g R μ lo N j).card : ℝ) ≤ 2 * (N : ℝ) / (K : ℝ) := by
      intro hc
      exact h ⟨j, hj, hc⟩
    exact lt_of_not_ge hnot
  have hlt : (∑ j ∈ Finset.range K, (2 * (N : ℝ) / (K : ℝ))) <
      ∑ j ∈ Finset.range K, ((shell g R μ lo N j).card : ℝ) := by
    apply Finset.sum_lt_sum
    · intro j hj
      exact (hall j (Finset.mem_range.mp hj)).le
    · refine ⟨0, ?_, ?_⟩
      · exact Finset.mem_range.mpr hK
      · exact hall 0 hK
  have hsum : (∑ j ∈ Finset.range K, (2 * (N : ℝ) / (K : ℝ))) = 2 * (N : ℝ) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hKn : (K : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hK)
    field_simp [hKn]
  have hle2 : (∑ j ∈ Finset.range K, ((shell g R μ lo N j).card : ℝ)) ≤ 2 * (N : ℝ) :=
    sum_shell_card_le_It (g := g) (R := R) (μ := μ) (lo := lo) (N := N) hR K
  linarith


/-- shell choice for Prop ell-2 update: some shell `j` (among the first
`K := ⌈1/(2μ²)⌉`) has at most `4μ²N` points, and its value `a := 4R·2^{jμ²}`
satisfies `4R ≤ a` and `2^{μ²}a ≤ 8R` (so spikes `{g ≥ 8R}` are `≥ 2^{μ²}a`,
i.e. large). -/
theorem exists_shell_choice {g : ℤ → ℝ} {R μ : ℝ} {lo : ℤ} {N : ℕ}
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 64) (hR0 : 0 < R) :
    ∃ j : ℕ, j < Nat.ceil (1 / (2 * μ ^ 2)) ∧
      (((shell g R μ lo N j).card : ℝ) ≤ 4 * μ ^ 2 * (N : ℝ)) ∧
      (4 * R ≤ shellVal R μ j) ∧
      ((2 : ℝ) ^ (μ ^ 2) * shellVal R μ j ≤ 8 * R) := by
  let K : ℕ := Nat.ceil (1 / (2 * μ ^ 2))
  have hμsq12 : μ ^ 2 ≤ 1 / 2 := by
    have h1 : μ ^ 2 ≤ μ * (1 / 64) := by
      simpa [pow_two] using (mul_le_mul_of_nonneg_left hμ1 hμ0.le)
    have h2 : μ * (1 / 64) ≤ (1 / 64) * (1 / 64) := mul_le_mul_of_nonneg_right hμ1 (by norm_num)
    have h3 : (1 / 64) * (1 / 64) ≤ 1 / 2 := by norm_num
    linarith
  have hxge1 : (1 : ℝ) ≤ 1 / (2 * μ ^ 2) := by
    have hden : 2 * μ ^ 2 ≤ 1 := by nlinarith [hμsq12]
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * μ ^ 2)).2 (by simpa using hden)
  have hK1 : 1 ≤ K := by
    have hle := Nat.le_ceil (1 / (2 * μ ^ 2))
    have hKge1R : (1 : ℝ) ≤ (K : ℝ) := le_trans hxge1 hle
    exact_mod_cast hKge1R
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK1
  rcases exists_shell_small (g := g) (R := R) (μ := μ) (lo := lo) (N := N) hR0 K hKpos with ⟨j, hjK, hmed⟩
  have hmed2 : ((shell g R μ lo N j).card : ℝ) ≤ 4 * μ ^ 2 * (N : ℝ) := by
    have hle := Nat.le_ceil (1 / (2 * μ ^ 2))
    have h1 : 1 ≤ 2 * μ ^ 2 * (K : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 2 * μ ^ 2)
      have hc : (2 * μ ^ 2) * (1 / (2 * μ ^ 2)) = 1 := by
        have h2m : (0 : ℝ) < 2 * μ ^ 2 := by positivity
        field_simp [h2m.ne']
      rwa [hc] at hmul
    have hq : (1 : ℝ) / (K : ℝ) ≤ 2 * μ ^ 2 := by
      exact (div_le_iff₀ (by exact_mod_cast hKpos : (0 : ℝ) < (K : ℝ))).2 h1
    have h3 : (2 * (N : ℝ)) / (K : ℝ) ≤ (2 * (N : ℝ)) * (2 * μ ^ 2) := by
      have h2N0 : 0 ≤ 2 * (N : ℝ) := by positivity
      calc
        (2 * (N : ℝ)) / (K : ℝ) = (2 * (N : ℝ)) * ((1 : ℝ) / (K : ℝ)) := by rw [div_eq_mul_one_div]
        _ ≤ (2 * (N : ℝ)) * (2 * μ ^ 2) := mul_le_mul_of_nonneg_left hq h2N0
    have h3' : (2 * (N : ℝ)) * (2 * μ ^ 2) = 4 * μ ^ 2 * (N : ℝ) := by ring
    linarith
  -- 4R ≤ a
  have ha_ge : 4 * R ≤ shellVal R μ j := by
    have he0 : 0 ≤ (j : ℝ) * μ ^ 2 := by positivity
    have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((j : ℝ) * μ ^ 2) :=
      Ell2Update.rpow_two_ge_one ((j : ℝ) * μ ^ 2) he0
    have h4R0 : 0 ≤ 4 * R := by positivity
    calc
      4 * R = (4 * R) * 1 := by ring
      _ ≤ (4 * R) * (2 : ℝ) ^ ((j : ℝ) * μ ^ 2) := mul_le_mul_of_nonneg_left hpow1 h4R0
      _ = shellVal R μ j := by rfl
  -- 2^{μ²}·a ≤ 8R
  have ha_le : (2 : ℝ) ^ (μ ^ 2) * shellVal R μ j ≤ 8 * R := by
    have hj1 : j + 1 ≤ K := by omega
    have hmono : shellVal R μ (j + 1) ≤ shellVal R μ K := shellVal_mono (le_of_lt hR0) hj1
    have hsucc : (2 : ℝ) ^ (μ ^ 2) * shellVal R μ j = shellVal R μ (j + 1) :=
      (shellVal_succ R μ j).symm
    have htop : shellVal R μ K ≤ 8 * R := by
      dsimp [shellVal]
      have hKm1 : 0 ≤ (K : ℝ) * μ ^ 2 := by positivity
      have hKm : (K : ℝ) * μ ^ 2 ≤ 1 := by
        have hKlt := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 1 / (2 * μ ^ 2))
        have hmul := mul_lt_mul_of_pos_left hKlt (by positivity : (0 : ℝ) < μ ^ 2)
        have hred : μ ^ 2 * (1 / (2 * μ ^ 2) + 1) = 1 / 2 + μ ^ 2 := by
          have h2m : (0 : ℝ) < 2 * μ ^ 2 := by positivity
          field_simp [h2m.ne']
        have hb : μ ^ 2 * (K : ℝ) < 1 / 2 + μ ^ 2 := by
          rwa [hred] at hmul
        have hkb : (K : ℝ) * μ ^ 2 = μ ^ 2 * (K : ℝ) := by ring
        rw [← hkb] at hb
        nlinarith [hμsq12]
      have hpowK : (2 : ℝ) ^ ((K : ℝ) * μ ^ 2) ≤ 2 := Ell2Update.two_pow_le_two ((K : ℝ) * μ ^ 2) hKm1 hKm
      have h40 : 0 ≤ 4 * R := by positivity
      calc
        4 * R * (2 : ℝ) ^ ((K : ℝ) * μ ^ 2) ≤ (4 * R) * 2 := by
          rw [show 4 * R * (2 : ℝ) ^ ((K : ℝ) * μ ^ 2) = (4 * R) * (2 : ℝ) ^ ((K : ℝ) * μ ^ 2) by ring]
          exact mul_le_mul_of_nonneg_left hpowK h40
        _ = 8 * R := by ring
    calc
      (2 : ℝ) ^ (μ ^ 2) * shellVal R μ j ≤ shellVal R μ K := by
        rw [hsucc]
        exact hmono
      _ ≤ 8 * R := htop
  exact ⟨j, hjK, hmed2, ha_ge, ha_le⟩



/-- positional form of `List.Pairwise`: earlier elements relate to later ones. -/
lemma pairwise_get {α : Type} {R : α → α → Prop} {l : List α}
    (h : List.Pairwise R l) : ∀ i j : Fin l.length, i < j → R (l.get i) (l.get j) := by
  intro i j hij
  exact List.Pairwise.rel_get_of_lt h hij

/-- separation of distinct members of a pairwise-separated list, without
positions. -/
lemma sep_of_mem {B : List (ℤ × ℤ)}
    (hsep : List.Pairwise (fun b₁ b₂ : ℤ × ℤ => b₁.2 < b₂.1) B)
    {b₁ b₂ : ℤ × ℤ} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (hne : b₁ ≠ b₂) :
    b₁.2 < b₂.1 ∨ b₂.2 < b₁.1 := by
  classical
  rcases List.get_of_mem hb₁ with ⟨i, hi₁⟩
  rcases List.get_of_mem hb₂ with ⟨j, hj₂⟩
  have hneij : i ≠ j := by
    intro hij
    apply hne
    rw [← hi₁, ← hj₂, hij]
  rcases lt_or_gt_of_ne hneij with hlt | hlt
  · left
    rw [← hi₁, ← hj₂]
    exact pairwise_get hsep i j hlt
  · right
    rw [← hj₂, ← hi₁]
    exact pairwise_get hsep j i hlt

/-- intervals of distinct separated blocks are disjoint. -/
lemma block_intervals_disjoint_of_mem {B : List (ℤ × ℤ)}
    (hsep : List.Pairwise (fun b₁ b₂ : ℤ × ℤ => b₁.2 < b₂.1) B)
    {b₁ b₂ : ℤ × ℤ} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (hne : b₁ ≠ b₂) :
    Disjoint (Finset.Icc b₁.1 b₁.2) (Finset.Icc b₂.1 b₂.2) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  have hx₁' := Finset.mem_Icc.mp hx₁
  have hx₂' := Finset.mem_Icc.mp hx₂
  rcases sep_of_mem hsep hb₁ hb₂ hne with hlt | hlt
  · linarith
  · linarith


/-- the medium points of `Ĩ` for the threshold pair `(a, 2^{μ²}a)`. -/
def mediumFinset (g : ℤ → ℝ) (a μ : ℝ) (lo : ℤ) (N : ℕ) : Finset ℤ :=
  (It lo N).filter (fun t : ℤ => a < g t ∧ g t ≤ (2 : ℝ) ^ (μ ^ 2) * a)

/-- the medium points inside a block `[b.1, b.2]`. -/
def mediumBlock (g : ℤ → ℝ) (a μ : ℝ) (b : ℤ × ℤ) : Finset ℤ :=
  (Finset.Icc b.1 b.2).filter (fun t : ℤ => a < g t ∧ g t ≤ (2 : ℝ) ^ (μ ^ 2) * a)

/-- membership in `mediumFinset`. -/
lemma mem_mediumFinset_iff {g : ℤ → ℝ} {a μ : ℝ} {lo : ℤ} {N : ℕ} {t : ℤ} :
    t ∈ mediumFinset g a μ lo N ↔
      t ∈ It lo N ∧ a < g t ∧ g t ≤ (2 : ℝ) ^ (μ ^ 2) * a := by
  dsimp [mediumFinset]
  rw [Finset.mem_filter]

/-- membership in `mediumBlock`. -/
lemma mem_mediumBlock_iff {g : ℤ → ℝ} {a μ : ℝ} {b : ℤ × ℤ} {t : ℤ} :
    t ∈ mediumBlock g a μ b ↔
      t ∈ Finset.Icc b.1 b.2 ∧ a < g t ∧ g t ≤ (2 : ℝ) ^ (μ ^ 2) * a := by
  dsimp [mediumBlock]
  rw [Finset.mem_filter]

/-- every block of the greedy covering is contained in `Ĩ`. -/
theorem block_subset_It_of_mem {g : ℤ → ℝ} {a R μ : ℝ} {lo : ℤ} {N : ℕ} {b : ℤ × ℤ}
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 64)
    (hR0 : 0 < R) (ha0 : 0 < a) (ha4R : 4 * R ≤ a)
    (hN1 : 1 ≤ N) (hg0 : ∀ t : ℤ, 0 ≤ g t)
    (hlip : Ell2Update.ratioLip (μ ^ 4) g)
    (hmass : (∑ t ∈ It lo N, g t) ≤ 2 * R * (N : ℝ))
    (hb : b ∈ coverBlocks g a μ lo N (largeSorted g a μ lo N)) :
    Finset.Icc b.1 b.2 ⊆ It lo N := by
  have hcore := coverBlocks_block_core (g := g) (a := a) (R := R) (μ := μ) (lo := lo) (N := N)
    (L := largeSorted g a μ lo N)
    hμ0 hμ1 hR0 ha0 ha4R hN1 hg0 hlip hmass
    (fun x hx => mem_largeSorted.mp hx) b hb
  dsimp at hcore
  rcases hcore with ⟨hlx, hrlt, hsc1, hsc2, hlen, hlenq⟩
  have hgood := coverBlocks_good (L := largeSorted g a μ lo N)
    (fun x hx => mem_largeSorted.mp hx) b hb
  rcases hgood with ⟨hI0, hlarge⟩
  have hlo1 : lo ≤ b.1 := (mem_I0.mp hI0).1
  intro x hx
  have hx' := Finset.mem_Icc.mp hx
  rw [mem_It]
  constructor
  · exact le_trans hlo1 hx'.1
  · have hx2 : x ≤ b.2 := hx'.2
    have hb2 : b.2 < lo + (2 : ℤ) * (N : ℤ) - 1 := hrlt
    omega

/-- containment: the medium points of any block lie in the medium points of `Ĩ`. -/
lemma mediumBlock_subset_mediumFinset {g : ℤ → ℝ} {a R μ : ℝ} {lo : ℤ} {N : ℕ} {b : ℤ × ℤ}
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 64)
    (hR0 : 0 < R) (ha0 : 0 < a) (ha4R : 4 * R ≤ a)
    (hN1 : 1 ≤ N) (hg0 : ∀ t : ℤ, 0 ≤ g t)
    (hlip : Ell2Update.ratioLip (μ ^ 4) g)
    (hmass : (∑ t ∈ It lo N, g t) ≤ 2 * R * (N : ℝ))
    (hb : b ∈ coverBlocks g a μ lo N (largeSorted g a μ lo N)) :
    mediumBlock g a μ b ⊆ mediumFinset g a μ lo N := by
  intro t ht
  rw [mem_mediumBlock_iff] at ht
  rw [mem_mediumFinset_iff]
  constructor
  · exact block_subset_It_of_mem (g := g) (a := a) (R := R) (μ := μ) (lo := lo) (N := N)
      hμ0 hμ1 hR0 ha0 ha4R hN1 hg0 hlip hmass hb ht.1
  · exact ht.2



/-- medium-point sets of distinct blocks of the covering are disjoint. -/
lemma mediumBlock_disjoint_of_mem {g : ℤ → ℝ} {a μ : ℝ} {lo : ℤ} {N : ℕ} {b₁ b₂ : ℤ × ℤ}
    (hb₁ : b₁ ∈ coverBlocks g a μ lo N (largeSorted g a μ lo N))
    (hb₂ : b₂ ∈ coverBlocks g a μ lo N (largeSorted g a μ lo N))
    (hne : b₁ ≠ b₂) :
    Disjoint (mediumBlock g a μ b₁) (mediumBlock g a μ b₂) := by
  have hsep := coverBlocks_pairwise_sep (g := g) (a := a) (μ := μ) (lo := lo) (N := N)
    (largeSorted g a μ lo N)
  have hI := block_intervals_disjoint_of_mem hsep hb₁ hb₂ hne
  exact Finset.disjoint_filter_filter (p := fun t : ℤ => a < g t ∧ g t ≤ (2 : ℝ) ^ (μ ^ 2) * a)
    (q := fun t : ℤ => a < g t ∧ g t ≤ (2 : ℝ) ^ (μ ^ 2) * a) hI

/-- (good-index bound) with small-fraction `δ = 8μ`, the total length of the
"good" blocks (those whose medium part is at most `δ|I'|`) is at least `μN/2`,
given that there are `≥ μN` large points and at most `4μ²N` medium points. -/
theorem good_index_bound {g : ℤ → ℝ} {a R μ : ℝ} {lo : ℤ} {N : ℕ}
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 64)
    (hR0 : 0 < R) (ha0 : 0 < a) (ha4R : 4 * R ≤ a)
    (hN1 : 1 ≤ N) (hg0 : ∀ t : ℤ, 0 ≤ g t)
    (hlip : Ell2Update.ratioLip (μ ^ 4) g)
    (hmass : (∑ t ∈ It lo N, g t) ≤ 2 * R * (N : ℝ))
    (hL : μ * (N : ℝ) ≤ ((largeFinset g a μ lo N).card : ℝ))
    (hmed : ((mediumFinset g a μ lo N).card : ℝ) ≤ 4 * μ ^ 2 * (N : ℝ)) :
    μ * (N : ℝ) / 2 ≤
      ∑ b ∈ (coverBlocks g a μ lo N (largeSorted g a μ lo N)).toFinset,
        if ((mediumBlock g a μ b).card : ℝ) ≤ (8 * μ) * (ilen b.1 b.2 : ℝ)
          then (ilen b.1 b.2 : ℝ) else 0 := by
  classical
  let B : List (ℤ × ℤ) := coverBlocks g a μ lo N (largeSorted g a μ lo N)
  let δ : ℝ := 8 * μ
  let good : ℤ × ℤ → Prop := fun b => ((mediumBlock g a μ b).card : ℝ) ≤ δ * (ilen b.1 b.2 : ℝ)
  let G : Finset (ℤ × ℤ) := B.toFinset.filter good
  let H : Finset (ℤ × ℤ) := B.toFinset.filter (fun b => ¬ good b)
  have hδ0 : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ1 : δ ≤ 1 / 2 := by
    dsimp [δ]
    nlinarith [hμ1]
  have hμ2 : μ ≤ 2 := by linarith
  -- total length ≥ μN
  have htotN : ((largeFinset g a μ lo N).card : ℝ) ≤
      (∑ b ∈ B.toFinset, (ilen b.1 b.2 : ℝ)) := by
    have htot := blocks_total_len_ge_large (g := g) (a := a) (μ := μ) (lo := lo) (N := N)
    exact_mod_cast htot
  have htot : μ * (N : ℝ) ≤ ∑ b ∈ B.toFinset, (ilen b.1 b.2 : ℝ) := by
    exact le_trans hL htotN
  -- decomposition: Σ_all = Σ_G + Σ_H
  have hsplit : (∑ b ∈ B.toFinset, (ilen b.1 b.2 : ℝ)) =
      (∑ b ∈ G, (ilen b.1 b.2 : ℝ)) + (∑ b ∈ H, (ilen b.1 b.2 : ℝ)) := by
    have hs := Finset.sum_filter_add_sum_filter_not B.toFinset good (fun b : ℤ × ℤ => (ilen b.1 b.2 : ℝ))
    simpa [G, H, good, δ] using hs.symm
  -- per bad block: ilen ≤ med/δ
  have hper : ∀ b ∈ H, (ilen b.1 b.2 : ℝ) ≤ ((mediumBlock g a μ b).card : ℝ) / δ := by
    intro b hb
    have hnot : ¬ good b := (Finset.mem_filter.mp hb).2
    have hbnd : δ * (ilen b.1 b.2 : ℝ) < ((mediumBlock g a μ b).card : ℝ) := by
      dsimp [good] at hnot
      exact lt_of_not_ge hnot
    have hbndle : δ * (ilen b.1 b.2 : ℝ) ≤ ((mediumBlock g a μ b).card : ℝ) := hbnd.le
    have hle : (ilen b.1 b.2 : ℝ) * δ ≤ ((mediumBlock g a μ b).card : ℝ) := by
      rwa [mul_comm] at hbndle
    exact (le_div_iff₀ hδ0).mpr hle
  have hdiv : (∑ b ∈ H, ((mediumBlock g a μ b).card : ℝ) / δ) =
      (∑ b ∈ H, ((mediumBlock g a μ b).card : ℝ)) / δ := by
    rw [Finset.sum_div]
  have hbad : (∑ b ∈ H, (ilen b.1 b.2 : ℝ)) ≤
      (∑ b ∈ H, ((mediumBlock g a μ b).card : ℝ)) / δ := by
    calc
      (∑ b ∈ H, (ilen b.1 b.2 : ℝ)) ≤ ∑ b ∈ H, ((mediumBlock g a μ b).card : ℝ) / δ :=
        Finset.sum_le_sum hper
      _ = (∑ b ∈ H, ((mediumBlock g a μ b).card : ℝ)) / δ := hdiv
  -- Σ_H med ≤ mediumTotal (disjointness)
  have hHmed : (∑ b ∈ H, ((mediumBlock g a μ b).card : ℝ)) ≤
      ((mediumFinset g a μ lo N).card : ℝ) := by
    have hdisj : (↑H : Set (ℤ × ℤ)).PairwiseDisjoint (mediumBlock g a μ) := by
      intro b1 hb1 b2 hb2 hne
      exact mediumBlock_disjoint_of_mem (g := g) (a := a) (μ := μ) (lo := lo) (N := N)
        (by exact List.mem_toFinset.mp (Finset.mem_filter.mp hb1).1)
        (by exact List.mem_toFinset.mp (Finset.mem_filter.mp hb2).1) hne
    have hcard := Finset.card_biUnion (s := H) (t := mediumBlock g a μ) hdisj
    have hsubU : H.biUnion (mediumBlock g a μ) ⊆ mediumFinset g a μ lo N := by
      rw [Finset.biUnion_subset]
      intro b hb
      exact mediumBlock_subset_mediumFinset (g := g) (a := a) (R := R) (μ := μ) (lo := lo) (N := N)
        hμ0 hμ1 hR0 ha0 ha4R hN1 hg0 hlip hmass
        (List.mem_toFinset.mp (Finset.mem_filter.mp hb).1)
    have hle1 : (∑ b ∈ H, ((mediumBlock g a μ b).card : ℕ)) ≤ (mediumFinset g a μ lo N).card := by
      calc
        (∑ b ∈ H, ((mediumBlock g a μ b).card : ℕ)) = (H.biUnion (mediumBlock g a μ)).card := by
          rw [hcard]
        _ ≤ (mediumFinset g a μ lo N).card := Finset.card_le_card hsubU
    exact_mod_cast hle1
  -- mediumTotal ≤ 4μ²N, so Σ_H med / δ ≤ μN/2
  have hx2 : (4 * μ ^ 2 * (N : ℝ)) / (8 * μ) = μ * (N : ℝ) / 2 := by
    field_simp [hμ0.ne']
    ring
  have hmedDiv : ((mediumFinset g a μ lo N).card : ℝ) / δ ≤ μ * (N : ℝ) / 2 := by
    have hdiv1 : ((mediumFinset g a μ lo N).card : ℝ) / δ ≤
        (4 * μ ^ 2 * (N : ℝ)) / δ := by
      exact div_le_div_of_nonneg_right hmed (le_of_lt hδ0)
    have hδx : (4 * μ ^ 2 * (N : ℝ)) / δ = (4 * μ ^ 2 * (N : ℝ)) / (8 * μ) := by
      dsimp [δ]
    rwa [hδx, hx2] at hdiv1
  have hbad2 : (∑ b ∈ H, (ilen b.1 b.2 : ℝ)) ≤ μ * (N : ℝ) / 2 := by
    have h1 : (∑ b ∈ H, ((mediumBlock g a μ b).card : ℝ)) / δ ≤ μ * (N : ℝ) / 2 := by
      calc
        (∑ b ∈ H, ((mediumBlock g a μ b).card : ℝ)) / δ ≤
            ((mediumFinset g a μ lo N).card : ℝ) / δ := by
          exact div_le_div_of_nonneg_right hHmed (le_of_lt hδ0)
        _ ≤ μ * (N : ℝ) / 2 := hmedDiv
    linarith
  -- assemble
  have hG : μ * (N : ℝ) / 2 ≤ (∑ b ∈ G, (ilen b.1 b.2 : ℝ)) := by
    have hsplit : (∑ b ∈ B.toFinset, (ilen b.1 b.2 : ℝ)) =
        (∑ b ∈ G, (ilen b.1 b.2 : ℝ)) + (∑ b ∈ H, (ilen b.1 b.2 : ℝ)) := by
      have hs := Finset.sum_filter_add_sum_filter_not B.toFinset good (fun b : ℤ × ℤ => (ilen b.1 b.2 : ℝ))
      simpa [G, H] using hs.symm
    nlinarith [htot, hsplit, hbad2]
  -- convert to the if-then-else form
  have hif : (∑ b ∈ B.toFinset,
      if ((mediumBlock g a μ b).card : ℝ) ≤ (8 * μ) * (ilen b.1 b.2 : ℝ)
        then (ilen b.1 b.2 : ℝ) else 0) = ∑ b ∈ G, (ilen b.1 b.2 : ℝ) := by
    rw [← Finset.sum_filter]
  rw [hif]
  exact hG


/-- the separation `κ = (2^{μ²}−1)·4R` between the large and small thresholds. -/
def kappa (μ R : ℝ) : ℝ := ((2 : ℝ) ^ (μ ^ 2) - 1) * (4 * R)

/-- `κ` is positive. -/
lemma kappa_pos {μ R : ℝ} (hμ0 : 0 < μ) (hR0 : 0 < R) : 0 < kappa μ R := by
  dsimp [kappa]
  have h1 : (0 : ℝ) < (2 : ℝ) ^ (μ ^ 2) - 1 := by
    have hg := Ell2Update.two_pow_gt_one (μ ^ 2) (by positivity)
    linarith
  positivity

/-- `κ ≤ (2^{μ²}−1)·a` when `a ≥ 4R`. -/
lemma kappa_le_mul {μ R a : ℝ} (ha4R : 4 * R ≤ a) (hκnon : 0 ≤ (2 : ℝ) ^ (μ ^ 2) - 1) :
    kappa μ R ≤ ((2 : ℝ) ^ (μ ^ 2) - 1) * a := by
  dsimp [kappa]
  exact mul_le_mul_of_nonneg_left ha4R hκnon



/-- the `I₁` part of a block: points with value at least `2^{μ²}a`. -/
def blockI1 (g : ℤ → ℝ) (a μ : ℝ) (b : ℤ × ℤ) : Finset ℤ :=
  (Finset.Icc b.1 b.2).filter (fun t : ℤ => (2 : ℝ) ^ (μ ^ 2) * a ≤ g t)

/-- the `I₂` part of a block: medium points (strictly between the thresholds). -/
def blockI2 (g : ℤ → ℝ) (a μ : ℝ) (b : ℤ × ℤ) : Finset ℤ :=
  (Finset.Icc b.1 b.2).filter (fun t : ℤ => a < g t ∧ g t < (2 : ℝ) ^ (μ ^ 2) * a)

/-- the `I₃` part of a block: small points (value at most `a`). -/
def blockI3 (g : ℤ → ℝ) (a : ℝ) (b : ℤ × ℤ) : Finset ℤ :=
  (Finset.Icc b.1 b.2).filter (fun t : ℤ => g t ≤ a)

/-- membership in `blockI1`. -/
lemma mem_blockI1_iff {g : ℤ → ℝ} {a μ : ℝ} {b : ℤ × ℤ} {t : ℤ} :
    t ∈ blockI1 g a μ b ↔ t ∈ Finset.Icc b.1 b.2 ∧ (2 : ℝ) ^ (μ ^ 2) * a ≤ g t := by
  dsimp [blockI1]
  rw [Finset.mem_filter]

/-- membership in `blockI2`. -/
lemma mem_blockI2_iff {g : ℤ → ℝ} {a μ : ℝ} {b : ℤ × ℤ} {t : ℤ} :
    t ∈ blockI2 g a μ b ↔
      t ∈ Finset.Icc b.1 b.2 ∧ a < g t ∧ g t < (2 : ℝ) ^ (μ ^ 2) * a := by
  dsimp [blockI2]
  rw [Finset.mem_filter]

/-- membership in `blockI3`. -/
lemma mem_blockI3_iff {g : ℤ → ℝ} {a : ℝ} {b : ℤ × ℤ} {t : ℤ} :
    t ∈ blockI3 g a b ↔ t ∈ Finset.Icc b.1 b.2 ∧ g t ≤ a := by
  dsimp [blockI3]
  rw [Finset.mem_filter]

/-- (single good block) for a good block `b` of the covering, the number of
shifts `y` in an interval `J` of length at least `|b|` whose bad count over
`b` is below `δ|b|/4` is at most `64δ|J|` (Lemma l: aux averaging applied). -/
theorem block_aux_count {g1 g2 : ℤ → ℝ} {a R μ : ℝ} {lo : ℤ} {N : ℕ} {c d : ℤ} {b : ℤ × ℤ}
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 64)
    (hR0 : 0 < R) (ha0 : 0 < a) (ha4R : 4 * R ≤ a)
    (hN1 : 1 ≤ N) (hg10 : ∀ t : ℤ, 0 ≤ g1 t)
    (hlip : Ell2Update.ratioLip (μ ^ 4) g1)
    (hmass : (∑ t ∈ It lo N, g1 t) ≤ 2 * R * (N : ℝ))
    (hb : b ∈ coverBlocks g1 a μ lo N (largeSorted g1 a μ lo N))
    (hgood : ((mediumBlock g1 a μ b).card : ℝ) ≤ (8 * μ) * (ilen b.1 b.2 : ℝ))
    (hJlen : ((Finset.Icc b.1 b.2).card : ℝ) ≤ ((Finset.Icc c d).card : ℝ)) :
    (((Finset.Icc c d).filter (fun y : ℤ =>
      (((Finset.Icc b.1 b.2).filter (fun t : ℤ => |g1 t - g2 (t + y)| ≥ kappa μ R / 2)).card : ℝ) <
        (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4)).card : ℝ)
      ≤ 64 * (8 * μ) * ((Finset.Icc c d).card : ℝ) := by
  classical
  have hcore := coverBlocks_block_core (g := g1) (a := a) (R := R) (μ := μ) (lo := lo) (N := N)
    (L := largeSorted g1 a μ lo N)
    hμ0 hμ1 hR0 ha0 ha4R hN1 hg10 hlip hmass
    (fun x hx => mem_largeSorted.mp hx) b hb
  dsimp at hcore
  rcases hcore with ⟨hlx, hrlt, hsc1, hsc2, hlen, hlenq⟩
  have hκ0 : 0 < kappa μ R := kappa_pos hμ0 hR0
  have hδ0 : 0 < 8 * μ := by positivity
  -- I₃ bounds
  have hI3lo : (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 2 ≤ (blockI3 g1 a b).card := by
    simpa [blockI3, smallCnt, ilen] using hsc2
  have hI3hi : (blockI3 g1 a b).card ≤ (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) := by
    simpa [blockI3, smallCnt, ilen] using hsc1
  -- I₂ bound via the good condition
  have hsub2 : blockI2 g1 a μ b ⊆ mediumBlock g1 a μ b := by
    intro t ht
    rw [mem_mediumBlock_iff]
    rw [mem_blockI2_iff] at ht
    exact ⟨ht.1, ht.2.1, le_of_lt ht.2.2⟩
  have hI2 : (blockI2 g1 a μ b).card ≤ (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) := by
    have hle1 : (blockI2 g1 a μ b).card ≤ (mediumBlock g1 a μ b).card :=
      Finset.card_le_card hsub2
    have hleR : ((blockI2 g1 a μ b).card : ℝ) ≤ ((mediumBlock g1 a μ b).card : ℝ) := by
      exact_mod_cast hle1
    have hle2 : ((mediumBlock g1 a μ b).card : ℝ) ≤ (8 * μ) * (ilen b.1 b.2 : ℝ) := hgood
    have hle3 : ((blockI2 g1 a μ b).card : ℝ) ≤ (8 * μ) * (ilen b.1 b.2 : ℝ) :=
      le_trans hleR hle2
    simpa [ilen] using hle3
  -- partition
  have hpart : ∀ t : ℤ, t ∈ Finset.Icc b.1 b.2 ↔
      t ∈ blockI1 g1 a μ b ∨ t ∈ blockI2 g1 a μ b ∨ t ∈ blockI3 g1 a b := by
    intro t
    constructor
    · intro ht
      by_cases h1 : (2 : ℝ) ^ (μ ^ 2) * a ≤ g1 t
      · left
        rw [mem_blockI1_iff]
        exact ⟨ht, h1⟩
      · by_cases h3 : g1 t ≤ a
        · right
          right
          rw [mem_blockI3_iff]
          exact ⟨ht, h3⟩
        · right
          left
          rw [mem_blockI2_iff]
          exact ⟨ht, ⟨lt_of_not_ge h3, lt_of_not_ge h1⟩⟩
    · intro h
      rcases h with h | h | h
      · exact (mem_blockI1_iff.mp h).1
      · exact (mem_blockI2_iff.mp h).1
      · exact (mem_blockI3_iff.mp h).1
  -- separation
  have hsep : ∀ t₁ : ℤ, t₁ ∈ blockI1 g1 a μ b → ∀ t₃ : ℤ, t₃ ∈ blockI3 g1 a b →
      g1 t₃ + kappa μ R ≤ g1 t₁ := by
    intro t₁ ht₁ t₃ ht₃
    have ht₁' := mem_blockI1_iff.mp ht₁
    have ht₃' := mem_blockI3_iff.mp ht₃
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (μ ^ 2) := Ell2Update.rpow_two_ge_one (μ ^ 2) (by positivity)
    have hκnon : 0 ≤ (2 : ℝ) ^ (μ ^ 2) - 1 := by linarith
    have hkle := kappa_le_mul (μ := μ) (R := R) (a := a) ha4R hκnon
    calc
      g1 t₃ + kappa μ R ≤ a + ((2 : ℝ) ^ (μ ^ 2) - 1) * a := by linarith
      _ = (2 : ℝ) ^ (μ ^ 2) * a := by ring
      _ ≤ g1 t₁ := ht₁'.2
  exact Commons.Analysis.Interval.aux_averaging_count (f := g1) (g := g2)
    (κ := kappa μ R) (δ := (8 * μ)) (a := b.1) (b := b.2)
    (I₁ := blockI1 g1 a μ b) (I₂ := blockI2 g1 a μ b) (I₃ := blockI3 g1 a b)
    (c := c) (d := d) hκ0 hδ0 hpart hI3lo hI3hi hI2 hsep hJlen



/-- (Markov in counting form) over a finite index set with nonnegative values,
the number of indices where `T y` exceeds `B` is at most `(Σ T) / B`. -/
lemma real_markov {J : Finset ℤ} {T : ℤ → ℝ} {B : ℝ} (hB : 0 < B)
    (hT : ∀ y ∈ J, 0 ≤ T y) :
    (((J.filter (fun y : ℤ => B < T y)).card : ℝ)) ≤ (∑ y ∈ J, T y) / B := by
  classical
  -- per filtered element: B ≤ T y
  have hle : (∑ y ∈ J.filter (fun y : ℤ => B < T y), B) ≤ ∑ y ∈ J, T y := by
    have hsub : J.filter (fun y : ℤ => B < T y) ⊆ J := Finset.filter_subset _ _
    calc
      (∑ y ∈ J.filter (fun y : ℤ => B < T y), B)
          ≤ (∑ y ∈ J.filter (fun y : ℤ => B < T y), T y) := by
            exact Finset.sum_le_sum (fun y hy => le_of_lt (Finset.mem_filter.mp hy).2)
      _ ≤ ∑ y ∈ J, T y := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y hy hy' => hT y hy)
  have hcard : (∑ y ∈ J.filter (fun y : ℤ => B < T y), B) = B * ((J.filter (fun y : ℤ => B < T y)).card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  have hB' : B * ((J.filter (fun y : ℤ => B < T y)).card : ℝ) ≤ (∑ y ∈ J, T y) := by
    rwa [hcard] at hle
  exact (le_div_iff₀ hB).2 (by rwa [mul_comm] at hB')



/-- number of "bad" points of a block for a shift `y`: those `t` with
`|g1 t − g2(t+y)| ≥ κ/2`. -/
def badInBlock (g1 g2 : ℤ → ℝ) (κ : ℝ) (y : ℤ) (b : ℤ × ℤ) : ℕ :=
  ((Finset.Icc b.1 b.2).filter (fun t : ℤ => κ / 2 ≤ |g1 t - g2 (t + y)|)).card


/-- the indicator summand identity: exactly one of `A < X` and `X ≤ A` holds, so
the two indicator-weighted copies of `c` sum to `c`. -/
lemma summand_indicator_compl (A X c : ℝ) :
    (if A < X then c else 0) + (if X ≤ A then c else 0) = c := by
  by_cases h : A < X
  · simp [h, not_le_of_gt h]
  · have hX : X ≤ A := le_of_not_gt h
    simp [h, hX]

/-- pointwise: the two indicator decompositions of a per-block length sum are
complementary: `F y + S y = total length of B₀`. -/
lemma ind_sum_compl {g1 g2 : ℤ → ℝ} {μ κ : ℝ} {B₀ : Finset (ℤ × ℤ)}
    (S F : ℤ → ℝ) (hdef : ∀ y : ℤ,
      (S y = ∑ b ∈ B₀, (ilen b.1 b.2 : ℝ) *
        if (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4 ≤ (badInBlock g1 g2 κ y b : ℝ) then 1 else 0) ∧
      (F y = ∑ b ∈ B₀, (ilen b.1 b.2 : ℝ) *
        if (badInBlock g1 g2 κ y b : ℝ) < (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4 then 1 else 0)) :
    ∀ y : ℤ, F y + S y = ∑ b ∈ B₀, (ilen b.1 b.2 : ℝ) := by
  intro y
  rcases hdef y with ⟨hS, hF⟩
  rw [hF, hS]
  calc
    (∑ b ∈ B₀, (ilen b.1 b.2 : ℝ) *
        if (badInBlock g1 g2 κ y b : ℝ) < (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4 then 1 else 0) +
        (∑ b ∈ B₀, (ilen b.1 b.2 : ℝ) *
        if (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4 ≤ (badInBlock g1 g2 κ y b : ℝ) then 1 else 0)
        = ∑ b ∈ B₀, (ilen b.1 b.2 : ℝ) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      simpa using (summand_indicator_compl (badInBlock g1 g2 κ y b : ℝ)
        ((8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4) (ilen b.1 b.2 : ℝ))


/-- `y` is "very good": the total bad mass over the good blocks `B₀` (weighted
by block lengths) is at least `μN/4`. -/
def manyBad (g1 g2 : ℤ → ℝ) (μ : ℝ) (κ : ℝ) (N : ℕ) (B₀ : Finset (ℤ × ℤ)) (y : ℤ) : Prop :=
  μ * (N : ℝ) / 4 ≤ ∑ b ∈ B₀, (ilen b.1 b.2 : ℝ) *
    if (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4 ≤ (badInBlock g1 g2 κ y b : ℝ) then 1 else 0

/-- (union over good blocks + Markov) with good blocks `B₀` of total length at
least `μN/2` and a per-good-block aux bound, all but `128δ|J|` shifts `y` are
"very good". -/
theorem union_good_y_count {g1 g2 : ℤ → ℝ} {μ κ : ℝ} {N : ℕ} {J : Finset ℤ}
    {B₀ : Finset (ℤ × ℤ)} (hμ0 : 0 < μ) (hκ0 : 0 < κ) (hN : 0 < N)
    (hLtot : μ * (N : ℝ) / 2 ≤ ∑ b ∈ B₀, (ilen b.1 b.2 : ℝ))
    (hbnd : ∀ b ∈ B₀,
      (((J.filter (fun y : ℤ =>
        ((badInBlock g1 g2 κ y b : ℝ)) <
          (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4)).card : ℝ))
        ≤ 64 * (8 * μ) * (J.card : ℝ)) :
    (((J.filter (fun y : ℤ => ¬ manyBad g1 g2 μ κ N B₀ y)).card : ℝ)
      ≤ 128 * (8 * μ) * (J.card : ℝ)) := by
  classical
  let S : ℤ → ℝ := fun y => ∑ b ∈ B₀, (ilen b.1 b.2 : ℝ) *
    if (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4 ≤ (badInBlock g1 g2 κ y b : ℝ) then 1 else 0
  let F : ℤ → ℝ := fun y => ∑ b ∈ B₀, (ilen b.1 b.2 : ℝ) *
    if (badInBlock g1 g2 κ y b : ℝ) < (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4 then 1 else 0
  let T : ℝ := ∑ b ∈ B₀, (ilen b.1 b.2 : ℝ)
  have hFS : ∀ y : ℤ, F y + S y = T := by
    intro y
    dsimp [S, F, T]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    simpa using (summand_indicator_compl (badInBlock g1 g2 κ y b : ℝ)
      ((8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4) (ilen b.1 b.2 : ℝ))
  have hF0 : ∀ y : ℤ, 0 ≤ F y := by
    intro y
    dsimp [F]
    apply Finset.sum_nonneg
    intro b hb
    by_cases h : (badInBlock g1 g2 κ y b : ℝ) < (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4
    · simp [h]
      exact_mod_cast Nat.zero_le _
    · simp [h]
      exact_mod_cast Nat.zero_le _
  have hE : (∑ y ∈ J, F y) ≤ 64 * (8 * μ) * T * (J.card : ℝ) := by
    have hswap : (∑ y ∈ J, F y) = ∑ b ∈ B₀, (ilen b.1 b.2 : ℝ) *
        ((J.filter (fun y : ℤ =>
          (badInBlock g1 g2 κ y b : ℝ) < (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4)).card : ℝ) := by
      calc
        (∑ y ∈ J, F y) = ∑ y ∈ J, ∑ b ∈ B₀, (ilen b.1 b.2 : ℝ) *
            (if (badInBlock g1 g2 κ y b : ℝ) < (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4 then 1 else 0) := by
              simp [F]
        _ = ∑ b ∈ B₀, ∑ y ∈ J, (ilen b.1 b.2 : ℝ) *
            (if (badInBlock g1 g2 κ y b : ℝ) < (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4 then 1 else 0) := by
              rw [Finset.sum_comm]
        _ = ∑ b ∈ B₀, (ilen b.1 b.2 : ℝ) *
            (∑ y ∈ J, if (badInBlock g1 g2 κ y b : ℝ) < (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4 then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro b hb
              rw [Finset.mul_sum]
        _ = ∑ b ∈ B₀, (ilen b.1 b.2 : ℝ) *
            ((J.filter (fun y : ℤ =>
              (badInBlock g1 g2 κ y b : ℝ) < (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4)).card : ℝ) := by
              apply Finset.sum_congr rfl
              intro b hb
              congr 1
              calc
                (∑ y ∈ J, (if (badInBlock g1 g2 κ y b : ℝ) <
                      (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4 then (1 : ℝ) else 0))
                    = ∑ y ∈ J.filter (fun y : ℤ =>
                        (badInBlock g1 g2 κ y b : ℝ) < (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4), (1 : ℝ) := by
                      rw [Finset.sum_filter]
                _ = ((J.filter (fun y : ℤ =>
                      (badInBlock g1 g2 κ y b : ℝ) < (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4)).card : ℝ) := by
                      rw [Finset.sum_const, nsmul_eq_mul]
                      norm_num
    have hper : ∀ b ∈ B₀, (ilen b.1 b.2 : ℝ) *
        ((J.filter (fun y : ℤ =>
          (badInBlock g1 g2 κ y b : ℝ) < (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4)).card : ℝ)
        ≤ (ilen b.1 b.2 : ℝ) * (64 * (8 * μ) * (J.card : ℝ)) := by
      intro b hb
      exact mul_le_mul_of_nonneg_left (hbnd b hb) (by exact_mod_cast Nat.zero_le _)
    have hsumle : (∑ b ∈ B₀, (ilen b.1 b.2 : ℝ) *
        ((J.filter (fun y : ℤ =>
          (badInBlock g1 g2 κ y b : ℝ) < (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4)).card : ℝ))
        ≤ (∑ b ∈ B₀, (ilen b.1 b.2 : ℝ) * (64 * (8 * μ) * (J.card : ℝ))) :=
      Finset.sum_le_sum hper
    have hfac : (∑ b ∈ B₀, (ilen b.1 b.2 : ℝ) * (64 * (8 * μ) * (J.card : ℝ))) =
        64 * (8 * μ) * T * (J.card : ℝ) := by
      rw [show (∑ b ∈ B₀, (ilen b.1 b.2 : ℝ) * (64 * (8 * μ) * (J.card : ℝ))) =
          (∑ b ∈ B₀, (64 * (8 * μ) * (J.card : ℝ)) * (ilen b.1 b.2 : ℝ)) by
            apply Finset.sum_congr rfl
            intro b hb
            ring]
      rw [← Finset.mul_sum]
      dsimp [T]
      ring
    calc
      (∑ y ∈ J, F y) = ∑ b ∈ B₀, (ilen b.1 b.2 : ℝ) *
          ((J.filter (fun y : ℤ =>
            (badInBlock g1 g2 κ y b : ℝ) < (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4)).card : ℝ) := hswap
      _ ≤ (∑ b ∈ B₀, (ilen b.1 b.2 : ℝ) * (64 * (8 * μ) * (J.card : ℝ))) := hsumle
      _ = 64 * (8 * μ) * T * (J.card : ℝ) := hfac
  -- Markov: F ≥ 0 on J, threshold B := T − μN/4
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hB0 : 0 < T - μ * (N : ℝ) / 4 := by
    have hT2 : 0 < T / 2 := by
      have : 0 < μ * (N : ℝ) / 2 := by positivity
      have h12 : μ * (N : ℝ) / 2 ≤ T := hLtot
      linarith
    linarith
  have hmk := real_markov (J := J) (T := F) (B := T - μ * (N : ℝ) / 4) hB0 (fun y hy => hF0 y)
  have hnum : 64 * (8 * μ) * T * (J.card : ℝ) ≤
      128 * (8 * μ) * (J.card : ℝ) * (T - μ * (N : ℝ) / 4) := by
    have hmain : 64 * T ≤ 128 * (T - μ * (N : ℝ) / 4) := by nlinarith [hLtot]
    have hc : 0 ≤ (8 * μ) * (J.card : ℝ) := by positivity
    have hm := mul_le_mul_of_nonneg_left hmain hc
    have hL : 64 * (8 * μ) * T * (J.card : ℝ) = (8 * μ) * (J.card : ℝ) * (64 * T) := by ring
    have hR : 128 * (8 * μ) * (J.card : ℝ) * (T - μ * (N : ℝ) / 4) =
        (8 * μ) * (J.card : ℝ) * (128 * (T - μ * (N : ℝ) / 4)) := by ring
    rwa [← hL, ← hR] at hm
  have hratio : (64 * (8 * μ) * T * (J.card : ℝ)) / (T - μ * (N : ℝ) / 4) ≤
      128 * (8 * μ) * (J.card : ℝ) := by
    exact (div_le_iff₀ hB0).2 hnum
  have hmk2 : (((J.filter (fun y : ℤ => (T - μ * (N : ℝ) / 4) < F y)).card : ℝ)) ≤
      128 * (8 * μ) * (J.card : ℝ) := by
    calc
      (((J.filter (fun y : ℤ => (T - μ * (N : ℝ) / 4) < F y)).card : ℝ))
          ≤ (∑ y ∈ J, F y) / (T - μ * (N : ℝ) / 4) := hmk
      _ ≤ (64 * (8 * μ) * T * (J.card : ℝ)) / (T - μ * (N : ℝ) / 4) := by
            exact div_le_div_of_nonneg_right hE (le_of_lt hB0)
      _ ≤ 128 * (8 * μ) * (J.card : ℝ) := hratio
  -- counted filter equals the complement of the many-bad condition
  have hcond : ∀ y : ℤ, (T - μ * (N : ℝ) / 4 < F y) ↔ ¬ (μ * (N : ℝ) / 4 ≤ S y) := by
    intro y
    have hFSy : F y + S y = T := hFS y
    constructor
    · intro hF
      intro hS
      nlinarith
    · intro hnotS
      have hSlt : S y < μ * (N : ℝ) / 4 := lt_of_not_ge hnotS
      nlinarith
  have hfil : J.filter (fun y : ℤ => (T - μ * (N : ℝ) / 4) < F y) =
      J.filter (fun y : ℤ => ¬ (μ * (N : ℝ) / 4 ≤ S y)) := by
    ext y
    by_cases hy : y ∈ J
    · simp [hy, hcond y]
    · simp [hy]
  have hmk3 : (((J.filter (fun y : ℤ => ¬ (μ * (N : ℝ) / 4 ≤ S y))).card : ℝ)) ≤
      128 * (8 * μ) * (J.card : ℝ) := by
    rwa [hfil] at hmk2
  -- statement's condition is `manyBad`, whose body is exactly `μN/4 ≤ S y`
  have hSdef : ∀ y : ℤ, manyBad g1 g2 μ κ N B₀ y ↔ μ * (N : ℝ) / 4 ≤ S y := by
    intro y
    rfl
  have hEqF : J.filter (fun y : ℤ => ¬ manyBad g1 g2 μ κ N B₀ y) =
      J.filter (fun y : ℤ => ¬ (μ * (N : ℝ) / 4 ≤ S y)) := by
    ext y
    by_cases hy : y ∈ J
    · simp [hy, hSdef y]
    · simp [hy]
  have hmk4 : (((J.filter (fun y : ℤ => ¬ manyBad g1 g2 μ κ N B₀ y)).card : ℝ)) ≤
      128 * (8 * μ) * (J.card : ℝ) := by
    rwa [← hEqF] at hmk3
  exact hmk4


/-- a filtered sum equals the corresponding indicator-weighted sum over the
whole set. -/
lemma sum_filter_eq_sum_if {α : Type} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] (f : α → ℝ) :
    (∑ x ∈ s.filter p, f x) = ∑ x ∈ s, if p x then f x else 0 := by
  rw [Finset.sum_filter]



/-- (shell data for the counting form) from the spike hypothesis on `I₀`, the
shell choice yields a threshold `a` with: `0 < a`, `4R ≤ a`,
`2^{μ²}a ≤ 8R` (spikes are large), medium points over `Ĩ` at most `4μ²N`,
and at least `μN` large points. -/
theorem exists_shell_data {g : ℤ → ℝ} {R μ : ℝ} {lo : ℤ} {N : ℕ}
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 64) (hR0 : 0 < R) (hN1 : 1 ≤ N)
    (hsp : μ * (N : ℝ) ≤ (((Finset.Icc lo (lo + (N : ℤ) - 1)).filter (fun t : ℤ => 8 * R ≤ g t)).card : ℝ)) :
    ∃ a : ℝ, 0 < a ∧ 4 * R ≤ a ∧
      ((2 : ℝ) ^ (μ ^ 2) * a ≤ 8 * R) ∧
      (((mediumFinset g a μ lo N).card : ℝ) ≤ 4 * μ ^ 2 * (N : ℝ)) ∧
      (μ * (N : ℝ) ≤ ((largeFinset g a μ lo N).card : ℝ)) := by
  classical
  rcases exists_shell_choice (g := g) (R := R) (μ := μ) (lo := lo) (N := N)
    hμ0 hμ1 hR0 with ⟨j, hjK, hmed, ha_ge, htop⟩
  let a : ℝ := shellVal R μ j
  refine ⟨a, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [a]
    dsimp [shellVal]
    positivity
  · dsimp [a]
    exact ha_ge
  · dsimp [a]
    exact htop
  · dsimp [a]
    have hEq : mediumFinset g (shellVal R μ j) μ lo N = shell g R μ lo N j := by
      rfl
    rw [hEq]
    exact hmed
  · dsimp [a]
    have hsub : (Finset.Icc lo (lo + (N : ℤ) - 1)).filter (fun t : ℤ => 8 * R ≤ g t)
        ⊆ largeFinset g (shellVal R μ j) μ lo N := by
      intro t ht
      rw [Finset.mem_filter] at ht
      rw [show largeFinset g (shellVal R μ j) μ lo N =
          (I0 lo N).filter (fun t : ℤ => decide ((2 : ℝ) ^ (μ ^ 2) * shellVal R μ j ≤ g t)) by rfl]
      rw [Finset.mem_filter]
      constructor
      · simpa [I0] using ht.1
      · rw [decide_eq_true_eq]
        linarith [ht.2, htop]
    have hle1 : (((Finset.Icc lo (lo + (N : ℤ) - 1)).filter (fun t : ℤ => 8 * R ≤ g t)).card : ℝ) ≤
        ((largeFinset g (shellVal R μ j) μ lo N).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    linarith


end Submission.Ell2Greedy
