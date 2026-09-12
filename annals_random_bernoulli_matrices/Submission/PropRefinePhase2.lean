import Mathlib
import Submission.PropRefineExport
import Submission.Commons.Analysis.Interval.window_spike_cover
import Submission.Commons.Analysis.Interval.translate_filter_card
import Submission.Commons.Data.Finset.product_filter_fst_card
import Submission.Commons.Data.Finset.zeroOneSeq_card
import Submission.ProdCount

open Submission.Sec3
open Submission.Sec3Tower
open Submission.ProdCount
open Submission.L2Norm
open Submission.Ell2Update
open Submission.PropRefineExport

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Prop refinement, phase 2: backward-walk step bounds (counting form)

Tikhomirov 2020, Section 3, `prop: refinement` phase 2 (paper lines ~1440–1470).

The phase-1 export guarantees (with high probability) a flat level `≤ m`; on
that event `aux095_spikes` bounds the `√2H`-spikes of every level `≥ m+1` by
`3μN` per `N`-window.  This module converts that window bound into per-step
counting bounds for the backward walk over the tail coordinates (each `X_i`
uniform on an integer interval of cardinality `≥ N`):

- `lvl_step_spike_count`: for one shifted point, at most `6μ|J|` of the
  values `X ∈ J = Icc a b` (with `|J| ≥ N`) make `g_i(s + X) ≥ √2H`;
- `lvl_step_spike_count_two`: the two-sided union (both `s + X` and `s − X`)
  is `≤ 12μ|J|`.

**Walk induction:** `goodAll` (all `m` steps good), the prefix bridges
`pre_restrict_same`/`restrict_coord_same`/`pre_restrict_full`/`last_coord_same`,
`goodAll_succ` (all-good of an extension splits into all-good of its
`restrict` plus the last-step condition), `card_image_filter`, and
**`chain_good_count`** — the fiber/product induction: if at every prefix at
most a `c`-fraction of the next values is good, then the number of full
tuples with ALL steps good is at most `c^m · ∏|J_j|` (proved by induction on
`m` over `ProdCount.prodFinset`, double-counting through the
`biUnion`/`extendFin` decomposition).  The phase-2 walk instantiates
`good k u a` with the step-`k` survival event and `c := 12μ`, giving the
`(12μ)^m · ∏|S_i|` bound on surviving tail tuples; the outer union bound over
the `2^m` `{0,1}`-sequences and the `≤ (√2H)⁻¹` starting points then closes
the proof of the refinement proposition.
-/

namespace Submission.PropRefinePhase2

attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- translating an interval by `s` keeps its cardinality. -/
lemma translate_Icc_card {a b s : ℤ} :
    ((Finset.Icc (s + a) (s + b)).card : ℝ) = ((Finset.Icc a b).card : ℝ) := by
  have h := Commons.Analysis.Interval.translate_filter_card (Q := fun _ : ℤ => True)
    (c := a) (d := b) (s := s)
  simpa using h.symm

/-- reflecting through the origin preserves filter cardinalities (up to the
mirrored interval). -/
lemma neg_filter_card {Q : ℤ → Prop} [DecidablePred Q] {c d : ℤ} :
    (((Finset.Icc c d).filter (fun x : ℤ => Q (-x))).card) =
      ((Finset.Icc (-d) (-c)).filter (fun y : ℤ => Q y)).card := by
  classical
  apply Finset.card_bij (fun x hx => -x)
  · intro x hx
    rw [Finset.mem_filter] at hx
    rcases hx with ⟨hxin, hq⟩
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_Icc] at hxin ⊢
      omega
    · exact hq
  · intro x hx y hy hxy
    omega
  · intro y hy
    rw [Finset.mem_filter] at hy
    rcases hy with ⟨hyin, hq⟩
    refine ⟨-y, ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_Icc] at hyin ⊢
        omega
      · simpa using hq
    · simp

/-- one-sided per-step count: at most `6μ|J|` of the values `x` of a
coordinate uniform on `J = Icc a b` (with `|J| ≥ N`) make
`g_i(s + x) ≥ √2H`, given the `3μN` window spike bound on `g_i`. -/
lemma lvl_step_spike_count {f : ℤ → ℝ} {p : unitInterval} {H μ : ℝ} {N nn : ℕ}
    {i : ℕ} (hi : i ≤ nn) (x : Fin nn → ℤ) {a b : ℤ} (s : ℤ)
    (hH0 : 0 < H) (hN1 : 1 ≤ N) (hμ0 : 0 ≤ μ)
    (hNw : ∀ lo : ℤ,
      (Refine.spikeCnt (lvl f p i (pre x i hi)) (Real.sqrt 2 * H) lo N : ℝ) ≤
        3 * μ * (N : ℝ))
    (hS : (N : ℝ) ≤ ((Finset.Icc a b).card : ℝ)) :
    ((((Finset.Icc a b).filter (fun u : ℤ =>
        Real.sqrt 2 * H ≤ lvl f p i (pre x i hi) (s + u))).card : ℝ) ≤
      6 * μ * ((Finset.Icc a b).card : ℝ)) := by
  classical
  let g : ℤ → ℝ := lvl f p i (pre x i hi)
  let m : ℕ := (Finset.Icc a b).card
  have htr : (((Finset.Icc a b).filter (fun u : ℤ =>
        Real.sqrt 2 * H ≤ g (s + u))).card) =
      ((Finset.Icc (s + a) (s + b)).filter (fun y : ℤ => Real.sqrt 2 * H ≤ g y)).card := by
    exact Commons.Analysis.Interval.translate_filter_card
      (Q := fun y : ℤ => Real.sqrt 2 * H ≤ g y) (c := a) (d := b) (s := s)
  have hC : ∀ lo : ℤ,
      (((Finset.Icc lo (lo + (N : ℤ) - 1)).filter (fun t : ℤ => Real.sqrt 2 * H ≤ g t)).card : ℝ) ≤
        3 * μ * (N : ℝ) := by
    intro lo
    simpa [g, Refine.spikeCnt, Ell2Greedy.I0] using hNw lo
  have hS' : (N : ℝ) ≤ (((Finset.Icc (s + a) (s + b)).card : ℕ) : ℝ) := by
    rw [translate_Icc_card]
    exact hS
  have hcv := Commons.Analysis.Interval.window_spike_cover (F := g) (η := Real.sqrt 2 * H)
    (N := N) (c := s + a) (d := s + b) (C := 3 * μ * (N : ℝ)) hN1 hC hS'
  have hcv0 := hcv
  rw [translate_Icc_card] at hcv0
  have hcv' : ((((Finset.Icc (s + a) (s + b)).filter (fun y : ℤ =>
        Real.sqrt 2 * H ≤ g y)).card : ℕ) : ℝ) ≤
      (3 * μ * (N : ℝ)) * (((m : ℝ) / (N : ℝ)) + 1) := by
    simpa [m] using hcv0
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hpos : 0 ≤ 3 * μ * (N : ℝ) := by
    exact mul_nonneg (mul_nonneg (by norm_num) hμ0) (by exact_mod_cast (Nat.zero_le N))
  have hq : 1 ≤ ((m : ℝ) / (N : ℝ)) := by
    exact (le_div_iff₀ hNpos).mpr (by simpa [m] using hS)
  have hqf : ((m : ℝ) / (N : ℝ)) + 1 ≤ 2 * ((m : ℝ) / (N : ℝ)) := by
    nlinarith
  have htail : (3 * μ * (N : ℝ)) * (((m : ℝ) / (N : ℝ)) + 1) ≤ 6 * μ * (m : ℝ) := by
    calc
      (3 * μ * (N : ℝ)) * (((m : ℝ) / (N : ℝ)) + 1)
          ≤ (3 * μ * (N : ℝ)) * (2 * ((m : ℝ) / (N : ℝ))) :=
            mul_le_mul_of_nonneg_left hqf hpos
      _ = 6 * μ * (m : ℝ) := by
            field_simp [hNne]
            ring
  calc
    ((((Finset.Icc a b).filter (fun u : ℤ =>
        Real.sqrt 2 * H ≤ lvl f p i (pre x i hi) (s + u))).card : ℕ) : ℝ)
        = ((((Finset.Icc a b).filter (fun u : ℤ =>
            Real.sqrt 2 * H ≤ g (s + u))).card : ℕ) : ℝ) := by simp [g]
    _ = ((((Finset.Icc (s + a) (s + b)).filter (fun y : ℤ =>
            Real.sqrt 2 * H ≤ g y)).card : ℕ) : ℝ) := by rw [htr]
    _ ≤ (3 * μ * (N : ℝ)) * (((m : ℝ) / (N : ℝ)) + 1) := hcv'
    _ ≤ 6 * μ * (m : ℝ) := htail
    _ = 6 * μ * (((Finset.Icc a b).card : ℕ) : ℝ) := by simp [m]


/-- reflecting the interval keeps its cardinality. -/
lemma neg_Icc_card {a b : ℤ} :
    ((Finset.Icc (-b) (-a)).card : ℝ) = ((Finset.Icc a b).card : ℝ) := by
  have h := neg_filter_card (Q := fun _ : ℤ => True) (c := a) (d := b)
  simpa using h.symm

/-- two-sided per-step count: both prevalue events (at `s + X` and `s − X`)
hold for at most `12μ|J|` of the values `X ∈ J = Icc a b`. -/
lemma lvl_step_spike_count_two {f : ℤ → ℝ} {p : unitInterval} {H μ : ℝ} {N nn : ℕ}
    {i : ℕ} (hi : i ≤ nn) (x : Fin nn → ℤ) {a b : ℤ} (s : ℤ)
    (hH0 : 0 < H) (hN1 : 1 ≤ N) (hμ0 : 0 ≤ μ)
    (hNw : ∀ lo : ℤ,
      (Refine.spikeCnt (lvl f p i (pre x i hi)) (Real.sqrt 2 * H) lo N : ℝ) ≤
        3 * μ * (N : ℝ))
    (hS : (N : ℝ) ≤ ((Finset.Icc a b).card : ℝ)) :
    ((((Finset.Icc a b).filter (fun u : ℤ =>
        Real.sqrt 2 * H ≤ lvl f p i (pre x i hi) (s + u) ∨
        Real.sqrt 2 * H ≤ lvl f p i (pre x i hi) (s - u))).card : ℝ) ≤
      12 * μ * ((Finset.Icc a b).card : ℝ)) := by
  classical
  let g : ℤ → ℝ := lvl f p i (pre x i hi)
  have h1 : ((((Finset.Icc a b).filter (fun u : ℤ =>
        Real.sqrt 2 * H ≤ g (s + u))).card : ℕ) : ℝ) ≤ 6 * μ * ((Finset.Icc a b).card : ℝ) := by
    simpa [g] using (lvl_step_spike_count (f := f) (p := p) (H := H) (μ := μ) (N := N)
      (nn := nn) (i := i) hi x (a := a) (b := b) s hH0 hN1 hμ0 hNw hS)
  have hminus : ((((Finset.Icc a b).filter (fun u : ℤ =>
        Real.sqrt 2 * H ≤ g (s - u))).card : ℕ) : ℝ) ≤ 6 * μ * ((Finset.Icc a b).card : ℝ) := by
    have hSneg : (N : ℝ) ≤ (((Finset.Icc (-b) (-a)).card : ℕ) : ℝ) := by
      rw [neg_Icc_card]
      exact hS
    have h2 : ((((Finset.Icc (-b) (-a)).filter (fun v : ℤ =>
          Real.sqrt 2 * H ≤ g (s + v))).card : ℕ) : ℝ) ≤ 6 * μ * (((Finset.Icc (-b) (-a)).card : ℕ) : ℝ) := by
      simpa [g] using (lvl_step_spike_count (f := f) (p := p) (H := H) (μ := μ) (N := N)
        (nn := nn) (i := i) hi x (a := -b) (b := -a) s hH0 hN1 hμ0 hNw hSneg)
    have hfL : (Finset.Icc a b).filter (fun u : ℤ => Real.sqrt 2 * H ≤ g (s - u)) =
        (Finset.Icc a b).filter (fun u : ℤ => Real.sqrt 2 * H ≤ g (s + -u)) := by
      ext u
      by_cases hu : u ∈ Finset.Icc a b <;> simp [hu]
      have harg : s - u = s + -u := by ring
      rw [harg]
    have hnf := neg_filter_card (Q := fun v : ℤ => Real.sqrt 2 * H ≤ g (s + v)) (c := a) (d := b)
    calc
      ((((Finset.Icc a b).filter (fun u : ℤ =>
          Real.sqrt 2 * H ≤ g (s - u))).card : ℕ) : ℝ)
          = ((((Finset.Icc a b).filter (fun u : ℤ =>
              Real.sqrt 2 * H ≤ g (s + -u))).card : ℕ) : ℝ) := by
            rw [hfL]
      _ = ((((Finset.Icc (-b) (-a)).filter (fun v : ℤ =>
              Real.sqrt 2 * H ≤ g (s + v))).card : ℕ) : ℝ) := by
            rw [hnf]
      _ ≤ 6 * μ * (((Finset.Icc (-b) (-a)).card : ℕ) : ℝ) := h2
      _ = 6 * μ * (((Finset.Icc a b).card : ℕ) : ℝ) := by
            rw [neg_Icc_card]
  have hsub : (Finset.Icc a b).filter (fun u : ℤ =>
        Real.sqrt 2 * H ≤ g (s + u) ∨ Real.sqrt 2 * H ≤ g (s - u)) ⊆
      (Finset.Icc a b).filter (fun u : ℤ => Real.sqrt 2 * H ≤ g (s + u)) ∪
        (Finset.Icc a b).filter (fun u : ℤ => Real.sqrt 2 * H ≤ g (s - u)) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    rcases hu with ⟨huin, hpq⟩
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases hpq with hp | hq
    · exact Or.inl ⟨huin, hp⟩
    · exact Or.inr ⟨huin, hq⟩
  have hNat : ((Finset.Icc a b).filter (fun u : ℤ =>
        Real.sqrt 2 * H ≤ g (s + u) ∨ Real.sqrt 2 * H ≤ g (s - u))).card ≤
      ((Finset.Icc a b).filter (fun u : ℤ => Real.sqrt 2 * H ≤ g (s + u))).card +
      ((Finset.Icc a b).filter (fun u : ℤ => Real.sqrt 2 * H ≤ g (s - u))).card := by
    have hcard := Finset.card_le_card hsub
    have hcu := Finset.card_union_le
      ((Finset.Icc a b).filter (fun u : ℤ => Real.sqrt 2 * H ≤ g (s + u)))
      ((Finset.Icc a b).filter (fun u : ℤ => Real.sqrt 2 * H ≤ g (s - u)))
    exact le_trans hcard hcu
  have hunion : ((((Finset.Icc a b).filter (fun u : ℤ =>
        Real.sqrt 2 * H ≤ g (s + u) ∨ Real.sqrt 2 * H ≤ g (s - u))).card : ℕ) : ℝ) ≤
      ((((Finset.Icc a b).filter (fun u : ℤ => Real.sqrt 2 * H ≤ g (s + u))).card : ℕ) : ℝ) +
      ((((Finset.Icc a b).filter (fun u : ℤ => Real.sqrt 2 * H ≤ g (s - u))).card : ℕ) : ℝ) := by
    exact_mod_cast hNat
  calc
    ((((Finset.Icc a b).filter (fun u : ℤ =>
        Real.sqrt 2 * H ≤ lvl f p i (pre x i hi) (s + u) ∨
        Real.sqrt 2 * H ≤ lvl f p i (pre x i hi) (s - u))).card : ℕ) : ℝ)
        = ((((Finset.Icc a b).filter (fun u : ℤ =>
            Real.sqrt 2 * H ≤ g (s + u) ∨ Real.sqrt 2 * H ≤ g (s - u))).card : ℕ) : ℝ) := by simp [g]
    _ ≤ ((((Finset.Icc a b).filter (fun u : ℤ => Real.sqrt 2 * H ≤ g (s + u))).card : ℕ) : ℝ) +
        ((((Finset.Icc a b).filter (fun u : ℤ => Real.sqrt 2 * H ≤ g (s - u))).card : ℕ) : ℝ) := hunion
    _ ≤ 6 * μ * (((Finset.Icc a b).card : ℕ) : ℝ) + 6 * μ * (((Finset.Icc a b).card : ℕ) : ℝ) := by
          exact add_le_add h1 hminus
    _ = 12 * μ * (((Finset.Icc a b).card : ℕ) : ℝ) := by ring


attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- all `m` steps of a length-`m` tuple are good (`good k u a` : adding value
`a` to prefix `u` at step `k` is good). -/
def goodAll {m : ℕ} (good : (k : ℕ) → (Fin k → ℤ) → ℤ → Prop)
    (x : Fin m → ℤ) : Prop :=
  ∀ (k : ℕ) (hk : k < m), good k (pre x k (Nat.le_of_lt hk)) (x ⟨k, hk⟩)

/-- `pre (restrict x) k` equals `pre x k` (same content, different lengths). -/
lemma pre_restrict_same {m : ℕ} (x : Fin (m + 1) → ℤ) {k : ℕ} (hk : k < m) :
    pre (restrict x) k (Nat.le_of_lt hk) = pre x k (Nat.le_of_lt (Nat.lt_trans hk (Nat.lt_succ_self m))) := by
  funext j
  dsimp [restrict, pre]

/-- coordinates of `restrict x` are coordinates of `x`. -/
lemma restrict_coord_same {m : ℕ} (x : Fin (m + 1) → ℤ) {k : ℕ} (hk : k < m) :
    (restrict x) ⟨k, hk⟩ = x ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m)⟩ := by
  dsimp [restrict]

/-- `pre x m` (with `m < m+1`) is `restrict x`. -/
lemma pre_restrict_full {m : ℕ} (x : Fin (m + 1) → ℤ) :
    pre x m (Nat.le_of_lt (Nat.lt_succ_self m)) = restrict x := by
  funext j
  dsimp [restrict, pre]
  congr 1

/-- `x ⟨m, m < m+1⟩ = x (Fin.last m)`. -/
lemma last_coord_same {m : ℕ} (x : Fin (m + 1) → ℤ) :
    x ⟨m, Nat.lt_succ_self m⟩ = x (Fin.last m) := by
  rfl

/-- all-good of an extension splits into all-good of the restriction plus the
last-step condition. -/
lemma goodAll_succ {m : ℕ} {good : (k : ℕ) → (Fin k → ℤ) → ℤ → Prop}
    (x : Fin (m + 1) → ℤ) :
    goodAll good x ↔ goodAll good (restrict x) ∧ good m (restrict x) (x (Fin.last m)) := by
  classical
  constructor
  · intro hx
    constructor
    · dsimp [goodAll]
      intro k hk
      have h := hx k (Nat.lt_trans hk (Nat.lt_succ_self m))
      rwa [pre_restrict_same x hk, restrict_coord_same x hk]
    · have h := hx m (Nat.lt_succ_self m)
      rwa [← pre_restrict_full x, ← last_coord_same x]
  · intro hx
    dsimp [goodAll]
    intro k hk'
    by_cases hkm : k < m
    · have h := (hx.1) k hkm
      have hpre : pre x k (Nat.le_of_lt hk') = pre (restrict x) k (Nat.le_of_lt hkm) := by
        calc
          pre x k (Nat.le_of_lt hk') = pre x k (Nat.le_of_lt (Nat.lt_trans hkm (Nat.lt_succ_self m))) := by
            exact pre_irrel (x := x)
          _ = pre (restrict x) k (Nat.le_of_lt hkm) := by
            exact (pre_restrict_same x hkm).symm
      have hcoord : x ⟨k, hk'⟩ = (restrict x) ⟨k, hkm⟩ := by
        calc
          x ⟨k, hk'⟩ = x ⟨k, Nat.lt_trans hkm (Nat.lt_succ_self m)⟩ := by congr 1
          _ = (restrict x) ⟨k, hkm⟩ := by
            exact (restrict_coord_same x hkm).symm
      rw [hpre, hcoord]
      exact h
    · have heq : k = m := by omega
      subst k
      have hpre : pre x m (Nat.le_of_lt hk') = restrict x := by
        calc
          pre x m (Nat.le_of_lt hk') = pre x m (Nat.le_of_lt (Nat.lt_succ_self m)) := by
            exact pre_irrel (x := x)
          _ = restrict x := pre_restrict_full x
      have hcoord : x ⟨m, hk'⟩ = x (Fin.last m) := by
        congr 1
      rw [hpre, hcoord]
      exact hx.2

/-- `extendFin y` is injective in its value argument. -/
lemma extend_injective {k : ℕ} (y : Fin k → ℤ) : Function.Injective (fun a : ℤ => extendFin y a) := by
  intro a₁ a₂ h
  have hlast := congrFun h (Fin.last k)
  simpa [extendFin] using hlast

/-- cardinality of a filtered image equals the filtered cardinality for an
injective map. -/
lemma card_image_filter {α β : Type} [DecidableEq β] {Y : Finset α} {f : α → β}
    (hinj : Function.Injective f) (P : β → Prop) [DecidablePred P] :
    (((Y.image f).filter P).card) = ((Y.filter (fun a : α => P (f a))).card) := by
  classical
  symm
  apply Finset.card_bij (fun a ha => f a)
  · intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_filter, Finset.mem_image]
    exact ⟨⟨a, ha.1, rfl⟩, ha.2⟩
  · intro a₁ ha₁ a₂ ha₂ h
    exact hinj h
  · intro b hb
    rw [Finset.mem_filter] at hb
    rcases hb with ⟨hbi, hP⟩
    rcases Finset.mem_image.mp hbi with ⟨a, ha, hfab⟩
    refine ⟨a, ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · exact ha
      · rw [hfab]
        exact hP
    · exact hfab

/-- multi-step fiber/product count: if at every prefix at most a `c`-fraction
of the next values is good, then the number of full tuples with ALL steps good
is at most `c^m · ∏|J_j|`. -/
lemma chain_good_count (m : ℕ) {J : Fin m → Finset ℤ} {c : ℝ} (hc0 : 0 ≤ c)
    {good : (k : ℕ) → (Fin k → ℤ) → ℤ → Prop}
    [∀ (k : ℕ) (u : Fin k → ℤ) (a : ℤ), Decidable (good k u a)]
    (hstep : ∀ (k : ℕ) (hk : k < m) (u : Fin k → ℤ),
      u ∈ prodFinset k (fun j : Fin k => J (Fin.castLE (Nat.le_of_lt hk) j)) →
      ((((J ⟨k, hk⟩).filter (fun a : ℤ => good k u a)).card : ℕ) : ℝ) ≤
        c * ((J ⟨k, hk⟩).card : ℝ)) :
    ((((prodFinset m J).filter (fun x : Fin m → ℤ => goodAll good x)).card : ℕ) : ℝ) ≤
      c ^ m * (∏ j : Fin m, ((J j).card : ℝ)) := by
  classical
  induction m with
  | zero =>
      have hg0 : ∀ x : Fin 0 → ℤ, goodAll good x := by
        intro x
        dsimp [goodAll]
        intro k hk
        exact False.elim (Nat.not_lt_zero k hk)
      have hpf : (prodFinset 0 J).filter (fun x : Fin 0 → ℤ => goodAll good x) =
          prodFinset 0 J := by
        have hcong := Finset.filter_congr (s := prodFinset 0 J)
          (p := fun x : Fin 0 → ℤ => goodAll good x) (q := fun _ : Fin 0 → ℤ => True)
          (by intro x hx; exact ⟨fun h => trivial, fun _ => hg0 x⟩)
        simpa using hcong
      calc
        ((((prodFinset 0 J).filter (fun x : Fin 0 → ℤ => goodAll good x)).card : ℕ) : ℝ)
            = (((prodFinset 0 J).card : ℕ) : ℝ) := by rw [hpf]
        _ = (1 : ℝ) := by simp [ProdCount.prodFinset]
        _ ≤ (c ^ 0) * (∏ j : Fin 0, ((J j).card : ℝ)) := by simp
  | succ m ih =>
      let J' : Fin m → Finset ℤ := fun j => J (Fin.castSucc j)
      let s : Finset (Fin m → ℤ) := prodFinset m (fun j : Fin m => J (Fin.castSucc j))
      have hdisj : (↑s : Set (Fin m → ℤ)).PairwiseDisjoint
          (fun y : Fin m → ℤ => ((J (Fin.last m)).image (fun a : ℤ => extendFin y a))) := by
        intro y₁ hy₁ y₂ hy₂ hne
        exact disjoint_extend_image (Y := J (Fin.last m)) (y₁ := y₁) (y₂ := y₂) hne
      have hfbeq : (prodFinset (m + 1) J).filter (fun x : Fin (m + 1) → ℤ => goodAll good x) =
          s.biUnion (fun y : Fin m → ℤ =>
            ((J (Fin.last m)).image (fun a : ℤ => extendFin y a)).filter
              (fun x : Fin (m + 1) → ℤ => goodAll good x)) := by
        ext z
        constructor
        · intro hz
          rw [Finset.mem_filter] at hz
          rcases hz with ⟨hzmem, hgood⟩
          rcases (ProdCount.mem_prodFinset_succ J z).1 hzmem with ⟨hy, ha⟩
          rw [Finset.mem_biUnion]
          refine ⟨restrict z, hy, ?_⟩
          rw [Finset.mem_filter]
          constructor
          · rw [Finset.mem_image]
            refine ⟨z (Fin.last m), ha, ?_⟩
            exact extend_restrict z
          · exact hgood
        · intro hz
          rw [Finset.mem_biUnion] at hz
          rcases hz with ⟨y, hy, hf⟩
          rw [Finset.mem_filter] at hf
          rcases hf with ⟨hzimg, hgood⟩
          rw [Finset.mem_image] at hzimg
          rcases hzimg with ⟨a', ha', hz'⟩
          rw [Finset.mem_filter]
          constructor
          · rw [ProdCount.mem_prodFinset_succ]
            constructor
            · rw [← hz', restrict_extend]
              exact hy
            · rw [← hz', extendFin_last]
              exact ha'
          · exact hgood
      have hcbeq : (((s.biUnion (fun y : Fin m → ℤ =>
            ((J (Fin.last m)).image (fun a : ℤ => extendFin y a)).filter
              (fun x : Fin (m + 1) → ℤ => goodAll good x))).card : ℕ) : ℝ) =
          (∑ y ∈ s,
            (((((J (Fin.last m)).image (fun a : ℤ => extendFin y a)).filter
              (fun x : Fin (m + 1) → ℤ => goodAll good x)).card : ℕ) : ℝ)) := by
        have hdisjf : (↑s : Set (Fin m → ℤ)).PairwiseDisjoint
            (fun y : Fin m → ℤ => ((J (Fin.last m)).image (fun a : ℤ => extendFin y a)).filter
              (fun x : Fin (m + 1) → ℤ => goodAll good x)) := by
          intro y₁ hy₁ y₂ hy₂ hne
          change Disjoint
            (((J (Fin.last m)).image (fun a : ℤ => extendFin y₁ a)).filter
              (fun x : Fin (m + 1) → ℤ => goodAll good x))
            (((J (Fin.last m)).image (fun a : ℤ => extendFin y₂ a)).filter
              (fun x : Fin (m + 1) → ℤ => goodAll good x))
          rw [Finset.disjoint_left]
          intro z hz₁ hz₂
          rw [Finset.mem_filter] at hz₁ hz₂
          have hd := hdisj (x := y₁) (y := y₂) hy₁ hy₂ hne
          change Disjoint
            ((J (Fin.last m)).image (fun a : ℤ => extendFin y₁ a))
            ((J (Fin.last m)).image (fun a : ℤ => extendFin y₂ a)) at hd
          rw [Finset.disjoint_left] at hd
          exact hd hz₁.1 hz₂.1
        have hb := Finset.card_biUnion hdisjf
        rw [hb]
        simp
      have hper_fiber : ∀ y ∈ s,
          (((J (Fin.last m)).image (fun a : ℤ => extendFin y a)).filter
              (fun x : Fin (m + 1) → ℤ => goodAll good x)).card =
            ((J (Fin.last m)).filter (fun a : ℤ => goodAll good y ∧ good m y a)).card := by
        intro y hy
        have hif := card_image_filter (Y := J (Fin.last m)) (f := fun a : ℤ => extendFin y a)
          (extend_injective y) (P := fun x : Fin (m + 1) → ℤ => goodAll good x)
        have hsplit0 : ∀ a : ℤ, goodAll good (extendFin y a) ↔ goodAll good y ∧ good m y a := by
          intro a
          have hsplit := goodAll_succ (good := good) (x := extendFin y a)
          rw [restrict_extend] at hsplit
          rw [extendFin_last] at hsplit
          exact hsplit
        have hfiber : (J (Fin.last m)).filter (fun a : ℤ => goodAll good (extendFin y a)) =
            (J (Fin.last m)).filter (fun a : ℤ => goodAll good y ∧ good m y a) := by
          ext a
          by_cases ha : a ∈ J (Fin.last m) <;> simp [ha, hsplit0 a]
        calc
          (((J (Fin.last m)).image (fun a : ℤ => extendFin y a)).filter
              (fun x : Fin (m + 1) → ℤ => goodAll good x)).card
              = ((J (Fin.last m)).filter (fun a : ℤ => goodAll good (extendFin y a))).card := hif
          _ = ((J (Fin.last m)).filter (fun a : ℤ => goodAll good y ∧ good m y a)).card := by
                rw [hfiber]
      have hg_all : ∀ y ∈ s,
          (if goodAll good y then
              (((J (Fin.last m)).filter (fun a : ℤ => good m y a)).card : ℝ) else 0) ≤
            (if goodAll good y then (1 : ℝ) else 0) * (c * ((J (Fin.last m)).card : ℝ)) := by
        intro y hy
        by_cases hg : goodAll good y
        · simp [hg]
          have hmem : y ∈ prodFinset m (fun j : Fin m => J (Fin.castLE (Nat.le_of_lt (Nat.lt_succ_self m)) j)) := by
            rw [ProdCount.mem_prodFinset]
            intro j
            rw [ProdCount.mem_prodFinset] at hy
            have hyj : y j ∈ J (Fin.castSucc j) := hy j
            have hcast : Fin.castSucc j = Fin.castLE (Nat.le_of_lt (Nat.lt_succ_self m)) j := by
              apply Fin.ext
              rfl
            rwa [← hcast]
          exact hstep m (Nat.lt_succ_self m) y hmem
        · simp [hg]
      have hsum1 :
          (∑ y ∈ s, ((((J (Fin.last m)).image (fun a : ℤ => extendFin y a)).filter
              (fun x : Fin (m + 1) → ℤ => goodAll good x)).card : ℕ) : ℝ)
            = (∑ y ∈ s, (if goodAll good y then
                (((J (Fin.last m)).filter (fun a : ℤ => good m y a)).card : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [hper_fiber y hy]
        by_cases hg : goodAll good y <;> simp [hg]
      have hsum2 :
          (∑ y ∈ s, (if goodAll good y then
                (((J (Fin.last m)).filter (fun a : ℤ => good m y a)).card : ℝ) else 0))
            ≤ (∑ y ∈ s, (if goodAll good y then (1 : ℝ) else 0)) * (c * ((J (Fin.last m)).card : ℝ)) := by
        calc
          (∑ y ∈ s, (if goodAll good y then
                (((J (Fin.last m)).filter (fun a : ℤ => good m y a)).card : ℝ) else 0))
              ≤ ∑ y ∈ s, ((if goodAll good y then (1 : ℝ) else 0) * (c * ((J (Fin.last m)).card : ℝ))) := by
                exact Finset.sum_le_sum (s := s) (fun y hy => hg_all y hy)
          _ = (∑ y ∈ s, (if goodAll good y then (1 : ℝ) else 0)) * (c * ((J (Fin.last m)).card : ℝ)) := by
                rw [Finset.sum_mul]
      have hsum3 : (∑ y ∈ s, (if goodAll good y then (1 : ℝ) else 0)) =
          (((s.filter (fun u : Fin m → ℤ => goodAll good u)).card : ℕ) : ℝ) := by
        rw [← Finset.sum_filter]
        rw [Finset.sum_const, nsmul_eq_mul]
        simp
      have hfcard :
          ((((prodFinset (m + 1) J).filter (fun x : Fin (m + 1) → ℤ => goodAll good x)).card : ℕ) : ℝ)
            = (∑ y ∈ s, ((((J (Fin.last m)).image (fun a : ℤ => extendFin y a)).filter
                (fun x : Fin (m + 1) → ℤ => goodAll good x)).card : ℕ) : ℝ) := by
        rw [hfbeq]
        exact hcbeq
      have hih : ((((prodFinset m J').filter (fun u : Fin m → ℤ => goodAll good u)).card : ℕ) : ℝ) ≤
          c ^ m * (∏ j : Fin m, ((J' j).card : ℝ)) := by
        have hstep' : ∀ (k : ℕ) (hk : k < m) (u : Fin k → ℤ),
            u ∈ prodFinset k (fun j : Fin k => J' (Fin.castLE (Nat.le_of_lt hk) j)) →
            ((((J' ⟨k, hk⟩).filter (fun a : ℤ => good k u a)).card : ℕ) : ℝ) ≤
              c * ((J' ⟨k, hk⟩).card : ℝ) := by
          intro k hk u hu
          have hmem : u ∈ prodFinset k (fun j : Fin k => J (Fin.castLE (Nat.le_of_lt (Nat.lt_trans hk (Nat.lt_succ_self m))) j)) := by
            rw [ProdCount.mem_prodFinset] at hu ⊢
            intro j
            have hj := hu j
            dsimp [J'] at hj
            have hcast : Fin.castSucc (Fin.castLE (Nat.le_of_lt hk) j) =
                Fin.castLE (Nat.le_of_lt (Nat.lt_trans hk (Nat.lt_succ_self m))) j := by
              apply Fin.ext
              simp
            rwa [← hcast] at hj
          have hst := hstep k (Nat.lt_trans hk (Nat.lt_succ_self m)) u hmem
          have hset : J ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m)⟩ = J' ⟨k, hk⟩ := by
            dsimp [J']
          rwa [← hset]
        exact ih (J := J') hstep'
      calc
        ((((prodFinset (m + 1) J).filter (fun x : Fin (m + 1) → ℤ => goodAll good x)).card : ℕ) : ℝ)
            = (∑ y ∈ s, ((((J (Fin.last m)).image (fun a : ℤ => extendFin y a)).filter
                (fun x : Fin (m + 1) → ℤ => goodAll good x)).card : ℕ) : ℝ) := hfcard
        _ = (∑ y ∈ s, (if goodAll good y then
                (((J (Fin.last m)).filter (fun a : ℤ => good m y a)).card : ℝ) else 0)) := hsum1
        _ ≤ (∑ y ∈ s, (if goodAll good y then (1 : ℝ) else 0)) * (c * ((J (Fin.last m)).card : ℝ)) := hsum2
        _ = (((s.filter (fun u : Fin m → ℤ => goodAll good u)).card : ℕ) : ℝ) * (c * ((J (Fin.last m)).card : ℝ)) := by
              rw [hsum3]
        _ = ((((prodFinset m J').filter (fun u : Fin m → ℤ => goodAll good u)).card : ℕ) : ℝ) * (c * ((J (Fin.last m)).card : ℝ)) := by
              dsimp [s]
        _ ≤ (c ^ m * (∏ j : Fin m, ((J' j).card : ℝ))) * (c * ((J (Fin.last m)).card : ℝ)) := by
              exact mul_le_mul_of_nonneg_right hih (mul_nonneg hc0 (by exact_mod_cast (Nat.zero_le (J (Fin.last m)).card)))
        _ = c ^ (m + 1) * ((J (Fin.last m)).card : ℝ) * (∏ j : Fin m, ((J' j).card : ℝ)) := by ring
        _ = c ^ (m + 1) * (∏ j : Fin (m + 1), ((J j).card : ℝ)) := by
              have hprod2 : (∏ j : Fin (m + 1), ((J j).card : ℝ)) =
                  ((J (Fin.last m)).card : ℝ) * (∏ j : Fin m, ((J' j).card : ℝ)) := by
                rw [Fin.prod_univ_castSucc]
                simp [J', mul_comm, mul_left_comm, mul_assoc]
              rw [hprod2]
              ring


attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- concatenation of the length-`m` prefix with a length-`k` tail of values. -/
def partialVec {m : ℕ} (pref : Fin m → ℤ) {k : ℕ} (u : Fin k → ℤ) : Fin (m + k) → ℤ :=
  fun q => if hq : q.val < m then pref ⟨q.val, hq⟩ else u ⟨q.val - m, by omega⟩

/-- the first `i₀ ≤ m` coordinates of `partialVec pref u` are those of `pref`. -/
lemma pre_partial_pref {m : ℕ} (pref : Fin m → ℤ) {k : ℕ} (u : Fin k → ℤ)
    {i₀ : ℕ} (hi₀m : i₀ ≤ m) :
    pre (partialVec pref u) i₀ (Nat.le_trans hi₀m (Nat.le_add_right m k)) =
      pre pref i₀ hi₀m := by
  funext j
  dsimp [partialVec, pre]
  have hj : j.val < m := lt_of_lt_of_le j.isLt hi₀m
  rw [dif_pos hj]
  congr 1

/-- the walk point at level `m+k` after the first `k` tail steps. -/
def walkPt {m : ℕ} (v : Fin m → ℤ) (p0 : ℤ) {k : ℕ} (u : Fin k → ℤ) : ℤ :=
  p0 - ∑ i : Fin k, (if hi : i.val < m then v ⟨i.val, hi⟩ * u i else 0)

/-- step-`k` survival event: adding value `a` at step `k` (prevalue level
`m+k`, `v_k := v ⟨k, hk⟩` the `{0,1}`-choice) keeps both prevalues `≥ √2H`. -/
def goodStep {f : ℤ → ℝ} {p : unitInterval} {H : ℝ} {m : ℕ} (pref : Fin m → ℤ)
    (v : Fin m → ℤ) (p0 : ℤ) {k : ℕ} (hk : k < m) (u : Fin k → ℤ) (a : ℤ) : Prop :=
  let L : ℤ → ℝ := lvl f p (m + k) (partialVec pref u)
  let pt : ℤ := walkPt v p0 u
  Real.sqrt 2 * H ≤ L (pt - v ⟨k, hk⟩ * a) ∧ Real.sqrt 2 * H ≤ L (pt + (1 - v ⟨k, hk⟩) * a)

/-- `goodStep`'s two conjuncts live among `pt ± a` and `pt`, so a failing
conjunct is covered by the two-sided set `{pt + a} ∪ {pt − a}`. -/
lemma goodStep_subset_two {f : ℤ → ℝ} {p : unitInterval} {H : ℝ} {m : ℕ}
    (pref : Fin m → ℤ) (v : Fin m → ℤ) (p0 : ℤ) {k : ℕ} (hk : k < m) (u : Fin k → ℤ)
    (a : ℤ) (hv : v ⟨k, hk⟩ = 0 ∨ v ⟨k, hk⟩ = 1) :
    goodStep (f := f) (p := p) (H := H) (m := m) pref v p0 hk u a →
      Real.sqrt 2 * H ≤ lvl f p (m + k) (partialVec pref u) (walkPt v p0 u + a) ∨
      Real.sqrt 2 * H ≤ lvl f p (m + k) (partialVec pref u) (walkPt v p0 u - a) := by
  classical
  intro hg
  dsimp [goodStep] at hg
  rcases hv with hv0 | hv1
  · left
    rw [hv0] at hg
    simpa using hg.2
  · right
    rw [hv1] at hg
    simpa using hg.1


attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- `good`-family for the walk: step `k` (guarded for `k ≥ m`; only used at
`k < m`) adds value `a` to tail-prefix `u`.  Carrying `(hk : k < m)` inside
`good`'s type would bake the tuple length into the family and break the
restrict step of `goodAll_succ` (length `m+1` vs length `m`), so the step
index `v ⟨k⟩` is guarded instead. -/
def goodStepFam {f : ℤ → ℝ} {p : unitInterval} {H : ℝ} {m : ℕ} (pref v : Fin m → ℤ)
    (p0 : ℤ) (k : ℕ) (u : Fin k → ℤ) (a : ℤ) : Prop :=
  let vk : ℤ := if h : k < m then v ⟨k, h⟩ else 0
  let L : ℤ → ℝ := lvl f p (m + k) (partialVec pref u)
  let pt : ℤ := walkPt v p0 u
  Real.sqrt 2 * H ≤ L (pt - vk * a) ∧ Real.sqrt 2 * H ≤ L (pt + (1 - vk) * a)

/-- window bound for the level-`(m+k)` function of the partial vector, from
the flat-level Event on the prefix. -/
lemma aux095_partial {f : ℤ → ℝ} {p : unitInterval} {H μ : ℝ} {N m : ℕ}
    (pref : Fin m → ℤ)
    (hH0 : 0 < H) (hN1 : 1 ≤ N) (hμ0 : 0 ≤ μ)
    (hsup0 : ∀ t : ℤ, f t ≤ 2 * H)
    (hflat : ∃ (i₀ : ℕ) (hi₀m : i₀ ≤ m),
      ∀ lo : ℤ, (Refine.spikeCnt (lvl f p i₀ (pre pref i₀ hi₀m)) H lo N : ℝ) ≤ μ * (N : ℝ)) :
    ∀ (k : ℕ) (u : Fin k → ℤ) (lo : ℤ),
      (Refine.spikeCnt (lvl f p (m + k) (partialVec pref u)) (Real.sqrt 2 * H) lo N : ℝ) ≤
        3 * μ * (N : ℝ) := by
  classical
  rcases hflat with ⟨i₀, hi₀m, hfi₀⟩
  intro k u lo
  have hmn : m ≤ m + k := by omega
  have hflat' : ∃ (j : ℕ) (hjm : j ≤ m),
      ∀ lo : ℤ, (Refine.spikeCnt (lvl f p j (pre (partialVec pref u) j (Nat.le_trans hjm hmn))) H lo N : ℝ) ≤
        μ * (N : ℝ) := by
    refine ⟨i₀, hi₀m, ?_⟩
    intro lo'
    have hpre : pre (partialVec pref u) i₀ (Nat.le_trans hi₀m hmn) = pre pref i₀ hi₀m := by
      -- pre_partial_pref: pre (partialVec pref u) i₀ (le_trans hi₀m (le_add_right m k)) = pre pref i₀ hi₀m
      have hp := pre_partial_pref (pref := pref) (u := u) hi₀m
      -- hp has proof arg (le_trans hi₀m (le_add_right m k)); ours (le_trans hi₀m hmn): equal by proof irrelevance
      simpa using hp
    rw [hpre]
    exact hfi₀ lo'
  have hb := aux095_ge_m (f := f) (p := p) (H := H) (μ := μ) (N := N) (m := m)
    (x := partialVec pref u) (nn := m + k) hmn hH0 hN1 hμ0 hsup0 hflat' (m + k)
    (le_refl (m + k)) (by omega) lo
  simpa [pre_self] using hb


attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- `goodStepFam`'s event is inside the two-sided set at the walk point
(`v⟨k,hk⟩ ∈ {0,1}`). -/
lemma goodStepFam_subset_two {f : ℤ → ℝ} {p : unitInterval} {H : ℝ} {m : ℕ}
    (pref v : Fin m → ℤ) (s₀ : ℤ) {k : ℕ} (hk : k < m) (u : Fin k → ℤ) (a : ℤ)
    (hv : v ⟨k, hk⟩ = 0 ∨ v ⟨k, hk⟩ = 1) :
    goodStepFam (f := f) (p := p) (H := H) (m := m) pref v s₀ k u a →
      Real.sqrt 2 * H ≤ lvl f p (m + k) (partialVec pref u) (walkPt v s₀ u + a) ∨
      Real.sqrt 2 * H ≤ lvl f p (m + k) (partialVec pref u) (walkPt v s₀ u - a) := by
  classical
  intro hg
  have hg' : goodStep (f := f) (p := p) (H := H) (m := m) pref v s₀ hk u a := by
    dsimp [goodStepFam] at hg
    rw [dif_pos hk] at hg
    exact hg
  exact goodStep_subset_two pref v s₀ hk u a hv hg'

/-- per-step fiber bound: at most a `12μ`-fraction of the next values keeps
the step good, from the flat-Event window bound and the two-sided count. -/
lemma step_fiber_bound {f : ℤ → ℝ} {p : unitInterval} {H μ : ℝ} {N m : ℕ}
    (pref v : Fin m → ℤ) (s₀ : ℤ) {k : ℕ} (hk : k < m) (u : Fin k → ℤ)
    {a b : ℤ}
    (hH0 : 0 < H) (hN1 : 1 ≤ N) (hμ0 : 0 ≤ μ)
    (hsup0 : ∀ t : ℤ, f t ≤ 2 * H)
    (hv : v ⟨k, hk⟩ = 0 ∨ v ⟨k, hk⟩ = 1)
    (hflat : ∃ (i₀ : ℕ) (hi₀m : i₀ ≤ m),
      ∀ lo : ℤ, (Refine.spikeCnt (lvl f p i₀ (pre pref i₀ hi₀m)) H lo N : ℝ) ≤ μ * (N : ℝ))
    (hS : (N : ℝ) ≤ ((Finset.Icc a b).card : ℝ)) :
    ((((Finset.Icc a b).filter (fun x : ℤ => goodStepFam (f := f) (p := p) (H := H)
        (m := m) pref v s₀ k u x)).card : ℕ) : ℝ) ≤
      12 * μ * ((Finset.Icc a b).card : ℝ) := by
  classical
  let g : ℤ → ℝ := lvl f p (m + k) (partialVec pref u)
  have hwin : ∀ lo : ℤ,
      (Refine.spikeCnt g (Real.sqrt 2 * H) lo N : ℝ) ≤ 3 * μ * (N : ℝ) := by
    intro lo
    have hb := aux095_partial (f := f) (p := p) (H := H) (μ := μ) (N := N) (m := m)
      pref hH0 hN1 hμ0 hsup0 hflat k u lo
    simpa [g] using hb
  have hps : pre (partialVec pref u) (m + k) (le_refl (m + k)) = partialVec pref u := by
    exact pre_self (ℓ := m + k) (x := partialVec pref u)
  have hwin' : ∀ lo : ℤ,
      (Refine.spikeCnt (lvl f p (m + k) (pre (partialVec pref u) (m + k) (le_refl (m + k)))) (Real.sqrt 2 * H) lo N : ℝ) ≤
        3 * μ * (N : ℝ) := by
    intro lo
    have heq : lvl f p (m + k) (pre (partialVec pref u) (m + k) (le_refl (m + k))) = lvl f p (m + k) (partialVec pref u) := by
      rw [hps]
    rw [heq]
    exact hwin lo
  have htw := lvl_step_spike_count_two (f := f) (p := p) (H := H) (μ := μ) (N := N)
    (nn := m + k) (i := m + k) (le_refl (m + k)) (partialVec pref u) (a := a) (b := b)
    (walkPt v s₀ u) hH0 hN1 hμ0 hwin' hS
  have htw' : ((((Finset.Icc a b).filter (fun x : ℤ =>
        Real.sqrt 2 * H ≤ g (walkPt v s₀ u + x) ∨
        Real.sqrt 2 * H ≤ g (walkPt v s₀ u - x))).card : ℕ) : ℝ) ≤
      12 * μ * ((Finset.Icc a b).card : ℝ) := by
    simpa [g, pre_self] using htw
  have hsub : (Finset.Icc a b).filter (fun x : ℤ =>
        goodStepFam (f := f) (p := p) (H := H) (m := m) pref v s₀ k u x) ⊆
      (Finset.Icc a b).filter (fun x : ℤ =>
        Real.sqrt 2 * H ≤ g (walkPt v s₀ u + x) ∨
        Real.sqrt 2 * H ≤ g (walkPt v s₀ u - x)) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, by
      have hgo := goodStepFam_subset_two (f := f) (p := p) (H := H) (m := m) pref v s₀ hk u x hv hx.2
      simpa [g] using hgo⟩
  have hcard := Finset.card_le_card hsub
  calc
    ((((Finset.Icc a b).filter (fun x : ℤ => goodStepFam (f := f) (p := p) (H := H)
        (m := m) pref v s₀ k u x)).card : ℕ) : ℝ)
        ≤ ((((Finset.Icc a b).filter (fun x : ℤ =>
            Real.sqrt 2 * H ≤ g (walkPt v s₀ u + x) ∨
            Real.sqrt 2 * H ≤ g (walkPt v s₀ u - x))).card : ℕ) : ℝ) := by
          exact_mod_cast hcard
    _ ≤ 12 * μ * ((Finset.Icc a b).card : ℝ) := htw'

/-- fixed-`v` surviving-tail-tuple bound: with the flat prefix Event, at most
`(12μ)^m · ∏|S_i|` tail tuples make ALL `m` backward steps survive. -/
theorem walk_tail_bound (m : ℕ) {f : ℤ → ℝ} {p : unitInterval} {H μ : ℝ} {N : ℕ}
    (pref v : Fin m → ℤ) (s₀ : ℤ) {lo hi : Fin m → ℤ}
    (hH0 : 0 < H) (hN1 : 1 ≤ N) (hμ0 : 0 ≤ μ)
    (hsup0 : ∀ t : ℤ, f t ≤ 2 * H)
    (hv : ∀ i : Fin m, v i = 0 ∨ v i = 1)
    (hflat : ∃ (i₀ : ℕ) (hi₀m : i₀ ≤ m),
      ∀ lo : ℤ, (Refine.spikeCnt (lvl f p i₀ (pre pref i₀ hi₀m)) H lo N : ℝ) ≤ μ * (N : ℝ))
    (hS : ∀ i : Fin m, (N : ℝ) ≤ ((Finset.Icc (lo i) (hi i)).card : ℝ)) :
    ((((prodFinset m (fun i : Fin m => Finset.Icc (lo i) (hi i))).filter
        (fun z : Fin m → ℤ => goodAll (goodStepFam (f := f) (p := p) (H := H) (m := m) pref v s₀) z)).card : ℕ) : ℝ) ≤
      (12 * μ) ^ m * (∏ i : Fin m, (((Finset.Icc (lo i) (hi i)).card : ℕ) : ℝ)) := by
  classical
  have hc0 : 0 ≤ 12 * μ := by positivity
  have hstep : ∀ (k : ℕ) (hk : k < m) (u : Fin k → ℤ),
      u ∈ prodFinset k (fun j : Fin k => (Finset.Icc (lo (Fin.castLE (Nat.le_of_lt hk) j)) (hi (Fin.castLE (Nat.le_of_lt hk) j)))) →
      (((((Finset.Icc (lo ⟨k, hk⟩) (hi ⟨k, hk⟩))).filter
          (fun a : ℤ => goodStepFam (f := f) (p := p) (H := H) (m := m) pref v s₀ k u a)).card : ℕ) : ℝ) ≤
        (12 * μ) * (((Finset.Icc (lo ⟨k, hk⟩) (hi ⟨k, hk⟩)).card : ℕ) : ℝ) := by
    intro k hk u hu
    have hvk : v ⟨k, hk⟩ = 0 ∨ v ⟨k, hk⟩ = 1 := hv ⟨k, hk⟩
    exact step_fiber_bound (f := f) (p := p) (H := H) (μ := μ) (N := N) (m := m)
      pref v s₀ hk u (a := lo ⟨k, hk⟩) (b := hi ⟨k, hk⟩) hH0 hN1 hμ0 hsup0 hvk hflat (hS ⟨k, hk⟩)
  have hc := chain_good_count m (J := fun i : Fin m => Finset.Icc (lo i) (hi i))
    (c := 12 * μ) hc0 (good := goodStepFam (f := f) (p := p) (H := H) (m := m) pref v s₀) hstep
  simpa using hc


attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- parity step: a level-`(2m+1)` value reaching `T` (in esup) implies the
level-`2m` one does too (odd `⌊εn⌋ = 2m+1` reduction). -/
lemma esup_parity_event {f : ℤ → ℝ} {p : unitInterval} {m : ℕ}
    (x : Fin (2 * m + 1) → ℤ) (hfpos : ∀ t : ℤ, 0 ≤ f t) (hf : Summable f) {T : ℝ}
    (hbig : T ≤ Sec3Tower.esup (lvl f p (2 * m + 1) (pre x (2 * m + 1) (le_refl (2 * m + 1))))) :
    T ≤ Sec3Tower.esup (lvl f p (2 * m) (pre x (2 * m) (by omega : 2 * m ≤ 2 * m + 1))) := by
  exact le_trans hbig (esup_parity (f := f) (p := p) (m := m) x hfpos hf)


attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- (assembly ingredient 2) count of (prefix, tail) pairs whose prefix has NO
flat level `≤ m` is at most `exp(−2Mn)·∏J·∏S` (prefix no-flat bound of
`phase1_no_flat_count`, tail counted independently). -/
theorem prefix_noflat_pair_count {M ε : ℝ} (hM : 1 ≤ M) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ∃ n₀ : ℕ, ∀ (n : ℕ), n₀ ≤ n →
    ∀ (m : ℕ), m = Nat.floor (ε * (n : ℝ) / 2) →
    ∀ {p : unitInterval} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) ≤ 1 / 2),
    ∀ {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t)
      (hf2 : Summable (fun t : ℤ => (f t) ^ 2)),
    ∀ {Rt L : ℝ} (hR0 : 0 < Rt) (hL16 : 16 * Rt ≤ L),
    ∀ {N : ℕ} (hN1 : 1 ≤ N), ∀ (hn1 : 1 ≤ n),
    ∀ {μ : ℝ} (hμeq : μ = PropRefine3.mu0 M ε) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 64),
    ∀ {H Cdrop : ℝ}
      (hH : H = L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ))))
      (hCdrop : Cdrop = (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * Rt ^ 2 /
        ((N : ℝ) * (n : ℝ))),
    ∀ (hlip : Ell2Update.ratioLip (μ ^ 4) f)
      (hmass : ∀ lo : ℤ, (∑ t ∈ Ell2Greedy.I0 lo N, f t) ≤ Rt / Real.sqrt (n : ℝ)),
    ∀ (hCdrop0 : 0 ≤ Cdrop)
      (hsmall : norm₂sq f < Cdrop * ((m / 2 + 1 : ℕ) : ℝ)),
    ∀ {c d : Fin m → ℤ},
      (∀ k : Fin m, (N : ℝ) ≤ ((Finset.Icc (c k) (d k)).card : ℝ)) →
    ∀ (loS hiS : Fin m → ℤ),
      (((((prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))).product
            (prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j)))).filter
          (fun pz : (Fin m → ℤ) × (Fin m → ℤ) =>
            ¬ (∃ (j : ℕ) (hj : j ≤ m), flatLvl f p H μ N j (pre pz.1 j hj)))).card : ℕ) : ℝ) ≤
        Real.exp (-2 * M * (n : ℝ)) *
          (∏ j : Fin m, (((Finset.Icc (c j) (d j)).card : ℕ) : ℝ)) *
          (∏ j : Fin m, (((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ)) := by
  classical
  rcases phase1_no_flat_count (M := M) (ε := ε) hM hε0 hε1 with ⟨n₀, hpf⟩
  refine ⟨n₀, ?_⟩
  intro n hn m hm p hp0 hp1 f hfpos hf2 Rt L hR0 hL16 N hN1 hn1 μ hμeq hμ0 hμ1 H Cdrop hH hCdrop
    hlip hmass hCdrop0 hsmall c d hJlen loS hiS
  let J : Fin m → Finset ℤ := fun j => Finset.Icc (c j) (d j)
  let S : Fin m → Finset ℤ := fun j => Finset.Icc (loS j) (hiS j)
  let noFlat : (Fin m → ℤ) → Prop := fun u =>
    ¬ (∃ (j : ℕ) (hj : j ≤ m), flatLvl f p H μ N j (pre u j hj))
  have hpref := hpf n hn (m := m) hm (p := p) hp0 hp1 (f := f) hfpos hf2 (Rt := Rt) (L := L)
    hR0 hL16 (N := N) hN1 hn1 (μ := μ) hμeq hμ0 hμ1 (H := H) (Cdrop := Cdrop) hH hCdrop
    hlip hmass hCdrop0 hsmall (c := c) (d := d) hJlen
  have hP : ((((prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))).filter noFlat).card : ℕ) : ℝ) ≤
      Real.exp (-2 * M * (n : ℝ)) * (∏ j : Fin m, (((Finset.Icc (c j) (d j)).card : ℕ) : ℝ)) := by
    simpa [noFlat, J] using hpref
  have hQ : ((((prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j))).card : ℕ) : ℝ) =
      (∏ j : Fin m, (((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ))) := by
    exact_mod_cast (ProdCount.prodFinset_card (fun j : Fin m => Finset.Icc (loS j) (hiS j)))
  have hprod := Commons.Data.Finset.product_filter_fst_card
    (prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j)))
    (prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j))) noFlat
  calc
    (((((prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))).product
        (prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j)))).filter
        (fun pz : (Fin m → ℤ) × (Fin m → ℤ) => noFlat pz.1)).card : ℕ) : ℝ)
        = ((((prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))).filter noFlat).card : ℕ) : ℝ) *
          ((((prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j))).card : ℕ) : ℝ)) := by
          rw [hprod]
          norm_num
    _ ≤ Real.exp (-2 * M * (n : ℝ)) *
          (∏ j : Fin m, (((Finset.Icc (c j) (d j)).card : ℕ) : ℝ)) *
          (∏ j : Fin m, (((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ)) := by
          rw [hQ]
          have hS0 : 0 ≤ (∏ j : Fin m, (((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ)) := by positivity
          nlinarith


attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- (assembly ingredient 3, start-set part) the number of start points
`s₀` with `g_m(s₀) ≥ √2H` is at most `1/(√2H)`, for a mass-`≤ 1` base
kernel. -/
lemma startSet_ncard_le {f : ℤ → ℝ} {p : unitInterval} {H : ℝ} {m : ℕ}
    (pref : Fin m → ℤ) (hH0 : 0 < H)
    (hfpos : ∀ t : ℤ, 0 ≤ f t) (hf : Summable f)
    (hmass : IntFun.norm₁ f ≤ 1) :
    (({t : ℤ | Real.sqrt 2 * H ≤ lvl f p m pref t}).ncard : ℝ) ≤
      1 / (Real.sqrt 2 * H) := by
  have hη : 0 < Real.sqrt 2 * H := by
    exact mul_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)) hH0
  exact lvl_spike_ncard_le_one (p := p) (η := Real.sqrt 2 * H) m pref hfpos hf hmass hη


attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- the `2^m` `{0,1}`-valued step-choice sequences over the `m` tail steps. -/
def SeqSet (m : ℕ) : Finset (Fin m → ℤ) :=
  (Finset.univ : Finset (Fin m → Fin 2)).image
    (fun b : Fin m → Fin 2 => fun i : Fin m => ((b i).val : ℤ))

/-- membership in `SeqSet`: exactly the `{0,1}`-valued sequences. -/
lemma mem_SeqSet {m : ℕ} (v : Fin m → ℤ) :
    v ∈ SeqSet m ↔ ∀ i : Fin m, v i = 0 ∨ v i = 1 := by
  classical
  dsimp [SeqSet]
  rw [Finset.mem_image]
  constructor
  · intro h
    rcases h with ⟨b, hb, hbv⟩
    intro i
    have hval := congrFun hbv i
    by_cases hz : (b i).val = 0
    · left
      calc
        v i = ((b i).val : ℤ) := hval.symm
        _ = (0 : ℤ) := by exact_mod_cast hz
    · right
      have hv2 : (b i).val < 2 := (b i).isLt
      have h1 : (b i).val = 1 := by omega
      calc
        v i = ((b i).val : ℤ) := hval.symm
        _ = (1 : ℤ) := by exact_mod_cast h1
  · intro h
    refine ⟨fun i => if v i = 0 then (⟨0, by norm_num⟩ : Fin 2) else (⟨1, by norm_num⟩ : Fin 2), ?_, ?_⟩
    · simp
    · funext i
      by_cases hz : v i = 0
      · simp [hz]
      · have h01 := h i
        have h1 : v i = 1 := by
          rcases h01 with h0 | h1
          · exact False.elim (hz h0)
          · exact h1
        simp [hz, h1]

/-- `|SeqSet m| = 2^m` (reals). -/
lemma SeqSet_card_real (m : ℕ) : ((SeqSet m).card : ℝ) = (2 : ℝ) ^ m := by
  have hc := Commons.Data.Finset.zeroOneSeq_card m
  dsimp [SeqSet]
  rw [hc]
  exact_mod_cast (by norm_num : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m)


attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- the (finite) set of start points of a prefix: `g_m(pref) ≥ √2H`. -/
def StartSet {f : ℤ → ℝ} {p : unitInterval} {H : ℝ} {m : ℕ}
    (pref : Fin m → ℤ) : Set ℤ :=
  {t : ℤ | Real.sqrt 2 * H ≤ lvl f p m pref t}

/-- `StartSet pref` is finite for a nonnegative summable base kernel. -/
lemma StartSet_finite {f : ℤ → ℝ} {p : unitInterval} {H : ℝ} {m : ℕ}
    (pref : Fin m → ℤ) (hH0 : 0 < H)
    (hfpos : ∀ t : ℤ, 0 ≤ f t) (hf : Summable f) :
    (StartSet (f := f) (p := p) (H := H) (m := m) pref).Finite := by
  have hpos : ∀ t : ℤ, 0 ≤ lvl f p m pref t := lvl_nonneg m pref hfpos
  have hsum : Summable (lvl f p m pref) := lvl_summable (p := p) m pref hf
  have hη : 0 < Real.sqrt 2 * H :=
    mul_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)) hH0
  dsimp [StartSet]
  exact finite_ge hpos hsum hη

/-- `StartSet pref` membership is `g_m(pref)(t) ≥ √2H`. -/
lemma mem_StartSet {f : ℤ → ℝ} {p : unitInterval} {H : ℝ} {m : ℕ}
    (pref : Fin m → ℤ) (t : ℤ) :
    t ∈ StartSet (f := f) (p := p) (H := H) (m := m) pref ↔
      Real.sqrt 2 * H ≤ lvl f p m pref t := by
  rfl
/-- (assembly ingredient 3, per prefix) on a flat prefix, the number of tail
tuples admitting SOME start point `s₀ ∈ StartSet pref` and SOME `{0,1}`-choice
`v` for which all `m` backward steps survive is at most
`(√2H)⁻¹ · 2^m · (12μ)^m · ∏|S|`. -/
theorem survive_union_bound {f : ℤ → ℝ} {p : unitInterval} {H μ : ℝ} {N m : ℕ}
    (pref : Fin m → ℤ) {loS hiS : Fin m → ℤ}
    (hH0 : 0 < H) (hN1 : 1 ≤ N) (hμ0 : 0 ≤ μ)
    (hsup0 : ∀ t : ℤ, f t ≤ 2 * H)
    (hfpos : ∀ t : ℤ, 0 ≤ f t) (hf : Summable f)
    (hmass : IntFun.norm₁ f ≤ 1)
    (hflat : ∃ (i₀ : ℕ) (hi₀m : i₀ ≤ m),
      ∀ lo : ℤ, (Refine.spikeCnt (lvl f p i₀ (pre pref i₀ hi₀m)) H lo N : ℝ) ≤ μ * (N : ℝ))
    (hS : ∀ i : Fin m, (N : ℝ) ≤ ((Finset.Icc (loS i) (hiS i)).card : ℝ)) :
    ((((prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j))).filter
        (fun z : Fin m → ℤ =>
          ∃ s₀ ∈ StartSet (f := f) (p := p) (H := H) (m := m) pref,
          ∃ v ∈ SeqSet m, goodAll (goodStepFam (f := f) (p := p) (H := H) (m := m) pref v s₀) z)).card : ℕ) : ℝ) ≤
      (1 / (Real.sqrt 2 * H)) * (2 : ℝ) ^ m * (12 * μ) ^ m *
        (∏ j : Fin m, (((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ)) := by
  classical
  have hAfin : (StartSet (f := f) (p := p) (H := H) (m := m) pref).Finite :=
    StartSet_finite pref hH0 hfpos hf
  let Q : Finset (Fin m → ℤ) := prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j))
  let A : Finset ℤ := hAfin.toFinset
  let B : Finset (Fin m → ℤ) := SeqSet m
  let X : ℝ := (12 * μ) ^ m * (∏ j : Fin m, (((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ))
  let E : ℤ → (Fin m → ℤ) → (Fin m → ℤ) → Prop :=
    fun s₀ v z => goodAll (goodStepFam (f := f) (p := p) (H := H) (m := m) pref v s₀) z
  let fc (S : Finset (Fin m → ℤ)) : ℝ := (S.card : ℝ)
  have hQ : Q = prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j)) := rfl
  -- per (a,b): fiber count ≤ X via walk_tail_bound
  have hfib : ∀ a ∈ A, ∀ b ∈ B, (fc (Q.filter (fun z : Fin m → ℤ => E a b z)) ≤ X) := by
    intro a ha b hb
    have hst := walk_tail_bound m (f := f) (p := p) (H := H) (μ := μ) (N := N)
      pref b a (lo := loS) (hi := hiS) hH0 hN1 hμ0 hsup0
      (by exact (mem_SeqSet b).mp hb) hflat hS
    have hgoal : (fc (Q.filter (fun z : Fin m → ℤ => E a b z)) ≤
        (12 * μ) ^ m * (∏ j : Fin m, (((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ))) := by
      dsimp [fc, E]
      simpa using hst
    simpa [X] using hgoal
  -- filter with ∃ a∈A ∃ b∈B ⊆ biUnion of fibers
  have hF0 : (Q.filter (fun z : Fin m → ℤ =>
        ∃ a ∈ A, ∃ b ∈ B, E a b z)) ⊆
      (A.product B).biUnion (fun q : ℤ × (Fin m → ℤ) => Q.filter (fun z : Fin m → ℤ => E q.1 q.2 z)) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    rw [Finset.mem_biUnion]
    rcases hz with ⟨hzQ, hzE⟩
    rcases hzE with ⟨a, ha, b, hb, habz⟩
    refine ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨hzQ, habz⟩
  have hcard0 := Finset.card_le_card hF0
  have hcard1 : (fc (Q.filter (fun z : Fin m → ℤ =>
        ∃ a ∈ A, ∃ b ∈ B, E a b z)) ≤
      ∑ q ∈ (A.product B), (fc (Q.filter (fun z : Fin m → ℤ => E q.1 q.2 z)))) := by
    have hcb : ((A.product B).biUnion
        (fun q : ℤ × (Fin m → ℤ) => Q.filter (fun z : Fin m → ℤ => E q.1 q.2 z))).card ≤
        ∑ q ∈ (A.product B), ((Q.filter (fun z : Fin m → ℤ => E q.1 q.2 z)).card) := by
      exact Finset.card_biUnion_le (s := A.product B)
        (t := fun q : ℤ × (Fin m → ℤ) => Q.filter (fun z : Fin m → ℤ => E q.1 q.2 z))
    have hℕ : (Q.filter (fun z => ∃ a ∈ A, ∃ b ∈ B, E a b z)).card ≤
        ∑ q ∈ (A.product B), ((Q.filter (fun z : Fin m → ℤ => E q.1 q.2 z)).card) := by
      exact le_trans hcard0 hcb
    have hsum : ((∑ q ∈ (A.product B), ((Q.filter (fun z : Fin m → ℤ => E q.1 q.2 z)).card) : ℕ) : ℝ) =
        ∑ q ∈ (A.product B), (((Q.filter (fun z : Fin m → ℤ => E q.1 q.2 z)).card : ℕ) : ℝ) := by
      exact map_sum (Nat.castAddMonoidHom ℝ) (fun q : ℤ × (Fin m → ℤ) =>
        (Q.filter (fun z : Fin m → ℤ => E q.1 q.2 z)).card) (A.product B)
    dsimp [fc]
    calc
      ((Q.filter (fun z => ∃ a ∈ A, ∃ b ∈ B, E a b z)).card : ℝ)
          ≤ ((∑ q ∈ (A.product B), ((Q.filter (fun z : Fin m → ℤ => E q.1 q.2 z)).card) : ℕ) : ℝ) := by
            exact_mod_cast hℕ
      _ = ∑ q ∈ (A.product B), (((Q.filter (fun z : Fin m → ℤ => E q.1 q.2 z)).card : ℕ) : ℝ) := by
            exact hsum
  have hsum_le : (∑ q ∈ (A.product B), (fc (Q.filter (fun z : Fin m → ℤ => E q.1 q.2 z)))) ≤
      ((A.card : ℝ) * (B.card : ℝ)) * X := by
    have hpt : ∀ q ∈ (A.product B), (fc (Q.filter (fun z : Fin m → ℤ => E q.1 q.2 z)) ≤ X) := by
      intro q hq
      have hq1 : q.1 ∈ A := (Finset.mem_product.mp hq).1
      have hq2 : q.2 ∈ B := (Finset.mem_product.mp hq).2
      exact hfib q.1 hq1 q.2 hq2
    have hle : (∑ q ∈ (A.product B), (fc (Q.filter (fun z : Fin m → ℤ => E q.1 q.2 z)))) ≤
        ∑ q ∈ (A.product B), X := by
      exact Finset.sum_le_sum (s := A.product B) (fun q hq => hpt q hq)
    calc
      (∑ q ∈ (A.product B), (fc (Q.filter (fun z : Fin m → ℤ => E q.1 q.2 z))))
          ≤ ∑ q ∈ (A.product B), X := hle
      _ = ((A.product B).card : ℝ) * X := by
            rw [Finset.sum_const]
            rw [nsmul_eq_mul]
      _ = ((A.card : ℝ) * (B.card : ℝ)) * X := by
            have hcp : ((((A.product B).card : ℕ) : ℝ) = (A.card : ℝ) * (B.card : ℝ)) := by
              exact_mod_cast Finset.card_product A B
            rw [hcp]
  have hA_le : ((A.card : ℝ) ≤ 1 / (Real.sqrt 2 * H)) := by
    have hsq := startSet_ncard_le (f := f) (p := p) (H := H) (m := m) pref hH0 hfpos hf hmass
    have hcard : A.card = (StartSet (f := f) (p := p) (H := H) (m := m) pref).ncard := by
      dsimp [A]
      exact (Set.ncard_eq_toFinset_card (s := StartSet (f := f) (p := p) (H := H) (m := m) pref) hAfin).symm
    rw [hcard]
    exact hsq
  have hB_eq : ((B.card : ℝ) = (2 : ℝ) ^ m) := by
    dsimp [B]
    exact SeqSet_card_real m
  have hX0 : 0 ≤ X := by
    dsimp [X]
    exact mul_nonneg (pow_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) hμ0) m)
      (Finset.prod_nonneg (fun j hj => by
        exact_mod_cast (Nat.zero_le ((Finset.Icc (loS j) (hiS j)).card)))
      )
  have hprod : ((A.card : ℝ) * (B.card : ℝ)) * X ≤
      (1 / (Real.sqrt 2 * H)) * (2 : ℝ) ^ m * X := by
    have hB0 : 0 ≤ (B.card : ℝ) := by exact_mod_cast (Nat.zero_le B.card)
    have hC0 : 0 ≤ 1 / (Real.sqrt 2 * H) := by
      exact div_nonneg (by norm_num) (mul_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)) hH0).le
    have hb1 : (A.card : ℝ) * (B.card : ℝ) ≤ (1 / (Real.sqrt 2 * H)) * (B.card : ℝ) := by
      exact mul_le_mul_of_nonneg_right hA_le hB0
    have hb2 : (1 / (Real.sqrt 2 * H)) * (B.card : ℝ) ≤ (1 / (Real.sqrt 2 * H)) * (2 : ℝ) ^ m := by
      exact mul_le_mul_of_nonneg_left (le_of_eq hB_eq) hC0
    exact mul_le_mul_of_nonneg_right (le_trans hb1 hb2) hX0
  -- convert the set-∃ filter to the A/B filter form (StartSet.toFinset mem)
  have hseteq : (Q.filter (fun z : Fin m → ℤ =>
        ∃ s₀ ∈ StartSet (f := f) (p := p) (H := H) (m := m) pref,
        ∃ v ∈ SeqSet m, goodAll (goodStepFam (f := f) (p := p) (H := H) (m := m) pref v s₀) z)) =
      (Q.filter (fun z : Fin m → ℤ => ∃ a ∈ A, ∃ b ∈ B, E a b z)) := by
    apply Finset.Subset.antisymm
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      rcases hz with ⟨hzQ, hzP1⟩
      refine ⟨hzQ, ?_⟩
      rcases hzP1 with ⟨s₀, hs₀, v, hv, hz'⟩
      refine ⟨s₀, ?_, v, ?_, hz'⟩
      · dsimp [A]
        exact (Set.Finite.mem_toFinset hAfin).2 hs₀
      · dsimp [B]
        exact hv
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      rcases hz with ⟨hzQ, hzP2⟩
      refine ⟨hzQ, ?_⟩
      rcases hzP2 with ⟨a, ha, b, hb, hz'⟩
      refine ⟨a, ?_, b, ?_, ?_⟩
      · exact (Set.Finite.mem_toFinset hAfin).1 ha
      · exact hb
      · simpa [E] using hz'
  calc
    ((((prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j))).filter
        (fun z : Fin m → ℤ =>
          ∃ s₀ ∈ StartSet (f := f) (p := p) (H := H) (m := m) pref,
          ∃ v ∈ SeqSet m, goodAll (goodStepFam (f := f) (p := p) (H := H) (m := m) pref v s₀) z)).card : ℕ) : ℝ)
        = (fc (Q.filter (fun z : Fin m → ℤ =>
            ∃ s₀ ∈ StartSet (f := f) (p := p) (H := H) (m := m) pref,
            ∃ v ∈ SeqSet m, goodAll (goodStepFam (f := f) (p := p) (H := H) (m := m) pref v s₀) z))) := by
          dsimp [fc, Q]
    _ = (fc (Q.filter (fun z : Fin m → ℤ => ∃ a ∈ A, ∃ b ∈ B, E a b z))) := by rw [hseteq]
    _ ≤ ∑ q ∈ (A.product B), (fc (Q.filter (fun z : Fin m → ℤ => E q.1 q.2 z))) := hcard1
    _ ≤ ((A.card : ℝ) * (B.card : ℝ)) * X := hsum_le
    _ ≤ (1 / (Real.sqrt 2 * H)) * (2 : ℝ) ^ m * X := hprod
    _ = (1 / (Real.sqrt 2 * H)) * (2 : ℝ) ^ m * (12 * μ) ^ m *
        (∏ j : Fin m, (((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ)) := by
          dsimp [X]
          ring
/-- (assembly ingredient 3, prefix sum) summing `survive_union_bound` over the
flat prefixes: the number of (flat-prefix, start, choice, surviving-tail)
quadruples is at most `|∏J|·(√2H)⁻¹·2^m·(12μ)^m·∏|S|`. -/
theorem flat_survive_pair_count {f : ℤ → ℝ} {p : unitInterval} {H μ : ℝ} {N m : ℕ}
    (J : Fin m → Finset ℤ) {loS hiS : Fin m → ℤ}
    (hH0 : 0 < H) (hN1 : 1 ≤ N) (hμ0 : 0 ≤ μ)
    (hsup0 : ∀ t : ℤ, f t ≤ 2 * H)
    (hfpos : ∀ t : ℤ, 0 ≤ f t) (hf : Summable f)
    (hmass : IntFun.norm₁ f ≤ 1)
    (hS : ∀ i : Fin m, (N : ℝ) ≤ ((Finset.Icc (loS i) (hiS i)).card : ℝ)) :
    (∑ pref ∈ (prodFinset m J).filter (fun pref : Fin m → ℤ =>
        ∃ (i₀ : ℕ) (hi₀m : i₀ ≤ m),
          ∀ lo : ℤ, (Refine.spikeCnt (lvl f p i₀ (pre pref i₀ hi₀m)) H lo N : ℝ) ≤ μ * (N : ℝ)),
      ((((prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j))).filter
        (fun z : Fin m → ℤ =>
          ∃ s₀ ∈ StartSet (f := f) (p := p) (H := H) (m := m) pref,
          ∃ v ∈ SeqSet m, goodAll (goodStepFam (f := f) (p := p) (H := H) (m := m) pref v s₀) z)).card : ℕ) : ℝ)) ≤
      ((prodFinset m J).card : ℝ) *
        (1 / (Real.sqrt 2 * H)) * (2 : ℝ) ^ m * (12 * μ) ^ m *
        (∏ j : Fin m, (((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ)) := by
  classical
  let rightPart : ℝ := (1 / (Real.sqrt 2 * H)) * (2 : ℝ) ^ m * (12 * μ) ^ m *
      (∏ j : Fin m, (((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ))
  have hsummand : ∀ pref ∈ (prodFinset m J).filter (fun pref : Fin m → ℤ =>
        ∃ (i₀ : ℕ) (hi₀m : i₀ ≤ m),
          ∀ lo : ℤ, (Refine.spikeCnt (lvl f p i₀ (pre pref i₀ hi₀m)) H lo N : ℝ) ≤ μ * (N : ℝ)),
      ((((prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j))).filter
        (fun z : Fin m → ℤ =>
          ∃ s₀ ∈ StartSet (f := f) (p := p) (H := H) (m := m) pref,
          ∃ v ∈ SeqSet m, goodAll (goodStepFam (f := f) (p := p) (H := H) (m := m) pref v s₀) z)).card : ℕ) : ℝ) ≤
        rightPart := by
    intro pref hpref
    have hflat : ∃ (i₀ : ℕ) (hi₀m : i₀ ≤ m),
          ∀ lo : ℤ, (Refine.spikeCnt (lvl f p i₀ (pre pref i₀ hi₀m)) H lo N : ℝ) ≤ μ * (N : ℝ) :=
      (Finset.mem_filter.mp hpref).2
    have hb := survive_union_bound (f := f) (p := p) (H := H) (μ := μ) (N := N) (m := m)
      pref (loS := loS) (hiS := hiS) hH0 hN1 hμ0 hsup0 hfpos hf hmass hflat hS
    dsimp [rightPart] at hb ⊢
    exact hb
  have hright0 : 0 ≤ rightPart := by
    dsimp [rightPart]
    have hc1 : 0 ≤ 1 / (Real.sqrt 2 * H) := by
      exact div_nonneg (by norm_num) (mul_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)) hH0).le
    have hc2 : 0 ≤ (12 * μ) ^ m := by
      exact pow_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) hμ0) m
    have hc3 : 0 ≤ ∏ j : Fin m, (((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ) := by
      exact Finset.prod_nonneg (fun j hj => by
        exact_mod_cast (Nat.zero_le ((Finset.Icc (loS j) (hiS j)).card)))
    have hpow2 : 0 ≤ (2 : ℝ) ^ m := by positivity
    have hab : 0 ≤ (1 / (Real.sqrt 2 * H)) * (2 : ℝ) ^ m := mul_nonneg hc1 hpow2
    have habc : 0 ≤ ((1 / (Real.sqrt 2 * H)) * (2 : ℝ) ^ m) * (12 * μ) ^ m := mul_nonneg hab hc2
    exact mul_nonneg habc hc3
  have hcard : ((prodFinset m J).filter (fun pref : Fin m → ℤ =>
        ∃ (i₀ : ℕ) (hi₀m : i₀ ≤ m),
          ∀ lo : ℤ, (Refine.spikeCnt (lvl f p i₀ (pre pref i₀ hi₀m)) H lo N : ℝ) ≤ μ * (N : ℝ))).card ≤
      (prodFinset m J).card := by
    exact Finset.card_le_card (Finset.filter_subset
      (p := fun pref : Fin m → ℤ => ∃ (i₀ : ℕ) (hi₀m : i₀ ≤ m),
          ∀ lo : ℤ, (Refine.spikeCnt (lvl f p i₀ (pre pref i₀ hi₀m)) H lo N : ℝ) ≤ μ * (N : ℝ))
      (s := prodFinset m J))
  have hcardR : (((prodFinset m J).filter (fun pref : Fin m → ℤ =>
        ∃ (i₀ : ℕ) (hi₀m : i₀ ≤ m),
          ∀ lo : ℤ, (Refine.spikeCnt (lvl f p i₀ (pre pref i₀ hi₀m)) H lo N : ℝ) ≤ μ * (N : ℝ))).card : ℝ) ≤
      ((prodFinset m J).card : ℝ) := by
    exact_mod_cast hcard
  calc
    (∑ pref ∈ (prodFinset m J).filter (fun pref : Fin m → ℤ =>
        ∃ (i₀ : ℕ) (hi₀m : i₀ ≤ m),
          ∀ lo : ℤ, (Refine.spikeCnt (lvl f p i₀ (pre pref i₀ hi₀m)) H lo N : ℝ) ≤ μ * (N : ℝ)),
      ((((prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j))).filter
        (fun z : Fin m → ℤ =>
          ∃ s₀ ∈ StartSet (f := f) (p := p) (H := H) (m := m) pref,
          ∃ v ∈ SeqSet m, goodAll (goodStepFam (f := f) (p := p) (H := H) (m := m) pref v s₀) z)).card : ℕ) : ℝ))
        ≤ ∑ pref ∈ (prodFinset m J).filter (fun pref : Fin m → ℤ =>
        ∃ (i₀ : ℕ) (hi₀m : i₀ ≤ m),
          ∀ lo : ℤ, (Refine.spikeCnt (lvl f p i₀ (pre pref i₀ hi₀m)) H lo N : ℝ) ≤ μ * (N : ℝ)), rightPart := by
          exact Finset.sum_le_sum (s := (prodFinset m J).filter (fun pref : Fin m → ℤ =>
            ∃ (i₀ : ℕ) (hi₀m : i₀ ≤ m),
              ∀ lo : ℤ, (Refine.spikeCnt (lvl f p i₀ (pre pref i₀ hi₀m)) H lo N : ℝ) ≤ μ * (N : ℝ)))
            (fun pref hpref => hsummand pref hpref)
    _ = (((prodFinset m J).filter (fun pref : Fin m → ℤ =>
        ∃ (i₀ : ℕ) (hi₀m : i₀ ≤ m),
          ∀ lo : ℤ, (Refine.spikeCnt (lvl f p i₀ (pre pref i₀ hi₀m)) H lo N : ℝ) ≤ μ * (N : ℝ))).card : ℝ) * rightPart := by
          rw [Finset.sum_const]
          rw [nsmul_eq_mul]
    _ ≤ ((prodFinset m J).card : ℝ) * rightPart := by
          exact mul_le_mul_of_nonneg_right hcardR hright0
    _ = ((prodFinset m J).card : ℝ) *
          (1 / (Real.sqrt 2 * H)) * (2 : ℝ) ^ m * (12 * μ) ^ m *
          (∏ j : Fin m, (((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ)) := by
          dsimp [rightPart]
          ring
/-- the first `m` coordinates of `pref`-then-`u` concatenation equal `pref`. -/
lemma partialVec_pre_eq {m k : ℕ} (w : Fin (m + k) → ℤ) :
    partialVec (pre w m (Nat.le_add_right m k)) (fun j : Fin k => w ⟨m + j.val, by omega⟩) = w := by
  funext q
  dsimp [partialVec, pre]
  by_cases hqm : q.val < m
  · simp [hqm]
  · simp [hqm]
    congr 1
    apply Fin.ext
    dsimp
    omega
end Submission.PropRefinePhase2
