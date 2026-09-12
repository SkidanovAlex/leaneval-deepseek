import Mathlib
import Submission.Sec3Tower
import Submission.Refine3
import Submission.L2Norm
import Submission.Ell2Update
import Submission.PropRefine3

/-!
# Prop refinement: level-function export (phase 1 complete, phase 2 deterministic core)

Tikhomirov 2020, Section 3, `prop: refinement` phase 1 (paper lines ~1330–1400),
in deterministic counting form over level functions `lvl f p k u := avgF f p k u`
(the paper's `g_k = f_{A,p,k}`).

Layers proved here (all machine-checked):

* **Layer B (per-prefix inheritance):** `lvl_zero`; `lvl_nonneg`; `lvl_le_sup`;
  `lvl_mass`; `lvl_ratioLip` (ratioLip is preserved by every mixing step via
  `Ell2Update.ratioLip_avg`); `lvl_sq_summable` (ℓ₂-square-summability via the
  one-step `summable_sq_one_step`); `norm₂sq_lvl_step_le` / `norm₂sq_lvl_le`
  (the level norms never increase); the telescoping `levelNorm_telescope`
  (`‖lvl m x‖₂² ≤ ‖f‖₂² − Cdrop·#dropping steps`, recursion-based `dropCnt`).

* **Layer C (per-prefix dichotomy):** `lvl_step_bad_count` — instantiation of
  `Refine3.step_bad_count` with `g := lvl f p k u` (if the current level is
  NOT flat, all but `1024μ|J|` next values drop by `Cdrop`); and the combined
  `badLvl_step_bound` (flat ⇒ no bad extensions, non-flat ⇒ the above).

* **Layer D (phase-1 export):** `mu0_pos`, `mu0_le_64`;
  `phase1_lvl_count` (tuples with `≥ ⌈m/2⌉` bad steps are `≤ exp(−2Mn)·∏|J|`);
  `dropCnt_eq_step`/`nBad_eq_stepBad`/`card_filter_succ`/`few_bad_implies_flat`/
  `not_flat_counted` (the deterministic (a)-or-(b) export: fewer than `⌈m/2⌉`
  bad steps forces a flat level `≤ m` under `‖f‖₂² < Cdrop·(⌊m/2⌋+1)`); and
  `phase1_no_flat_count` — the phase-1 Event-failure bound: the number of
  tuples with NO flat level is `≤ exp(−2Mn)·∏|J_j|`.

**Phase-2 deterministic core (paper lines ~1400–1420):** `tailVec` (tail
coordinates), `pre_cat_tail` (`pre x (i₀+s) = cat (pre x i₀) (tailVec x i₀ s)`),
`lvl_split` — THE bridge identity `lvl f p (i₀+s) (pre x (i₀+s)) =
avgF (lvl f p i₀ (pre x i₀)) p s tail` (via `Refine2.avgF_cat`);
`sqrt2_sub_one_ge_third`, `lvl_index` (level-index/proof renaming);
`spikeCnt_lvl_le_of_flat` — a single `Refine.avgF_spike_shrink` application per
level above the flat base (`√2H`-spikes of level `i₀+s` ≤ `μN/(√2−1)` per
`N`-interval), and `spikeCnt_lvl_le_of_flat_three` (the `3μN` form); and
`aux095_spikes` — eq. aux 09502875605824: if some level `i₀ ≤ m` is flat at
height `H`, then EVERY level `i ≥ m+1` has at most `3μN` points `≥ √2H` on
every `N`-interval.

**Level mass and spike counting (phase-2 tools):** `lvl_summable` (each level
is summable when the base is); `norm₁_lvl` — mass preservation
`‖lvl f p k u‖₁ = ‖f‖₁` (one-step via `IntFun.norm₁_add`/`norm₁_const_mul`/
`norm₁_add_right` + the convex-combination structure), with `norm₁_lvl_eq_one`
and `norm₁_lvl_le_one`; `finite_ge`/`ncard_ge_le` (the set `{t : θ ≤ f t}` of a
nonnegative summable `f` is finite with `ncard ≤ ‖f‖₁/θ`), and
`lvl_spike_ncard_le_one` — `|{t : η ≤ g_k(t)}| ≤ 1/η` for every level `g_k` of
a mass-`≤ 1` base kernel (`η > 0`), the `s_m`-counting bound of the phase-2
union bound.

**Phase-2 walk monotonicity:** `level_walk_exists` — `Sec3Tower.backward_chain`
(`BWalk`) restated with the `lvl`-level functions: from any top point `t_top`
at level `ℓ` of a coordinate vector `y : Fin ℓ → ℤ` there is a backward walk
`t i (hi : i ≤ ℓ)` (proof-independent, `t ℓ (le_refl ℓ) = t_top`) whose level
values are non-increasing (`lvl`-value at level `i+1` ≤ `lvl`-value at level
`i` for every step), each step adding `0` or the coordinate `y ⟨i,·⟩` — the
paper's sequence `(g_i(t_i))` of Prop refinement phase 2.

**Phase-2 two-prevalue claim:** `two_prevalues` — if the level-`(m+1)` value
at `t` reaches `(√2p + 2(1−p))H` while the level-`m` function is pointwise
`≤ 2H`, then BOTH level-`m` prevalues (at `t` and at `t + yₘ`) are `≥ √2H`
(via `Sec3Tower.flvl_rec` + `Refine.two_sides_of_high`): the deterministic
content of the paper's claim that `Ẽ` forces `g_{i−1}(t_i ± X_i) ≥ √2H` at
every backward step.

`flatLvl` = every `N`-interval has `≤ μN` points `≥ H`; `dropLvl` = the
one-step ℓ₂-drop `‖lvl(k+1) w‖₂² ≤ ‖lvl k (restrict w)‖₂² − Cdrop`;
`badLvl` = non-flat current level and no drop.  `m := ⌊εn/2⌋`,
`μ := mu0 M ε := exp(−16M/ε)/(24·1024²)`, `H := L/(2N√n)`,
`Cdrop := (1/2)p(1−p)μ⁶Rt²/(Nn)`, `f` = a nonnegative, ℓ₂-square-summable,
`ratioLip(μ⁴)`, `N`-window-mass-bounded kernel (the rough-decay output).
-/

open Submission.Sec3
open Submission.Sec3Tower
open Submission.ProdCount
open Submission.L2Norm
open Submission.Ell2Update

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

namespace Submission.PropRefineExport

attribute [local instance] Classical.propDecidable

open scoped BigOperators

def lvl (f : ℤ → ℝ) (p : unitInterval) (k : ℕ) (u : Fin k → ℤ) : ℤ → ℝ :=
  avgF f p k u

/-- `lvl` at level `k+1` on an extension equals the one-step average of `lvl`
at level `k` by the new coordinate (pointwise at `t`). -/
lemma lvl_extend_pt {f : ℤ → ℝ} {p : unitInterval} (k : ℕ) (u : Fin k → ℤ)
    (a : ℤ) (t : ℤ) :
    lvl f p (k + 1) (extendFin u a) t =
      (1 - (p : ℝ)) * lvl f p k u t + (p : ℝ) * lvl f p k u (t + a) := by
  have hrec := avgF_rec (f := f) (p := p) k (extendFin u a) t
  have hpre : pre (extendFin u a) k (Nat.le_succ k) = u := by
    funext j
    dsimp [pre, extendFin]
    have hlt : (↑j : ℕ) < k := by simpa using j.isLt
    simp [hlt]
  have hlst : (extendFin u a) last = a := by
    dsimp [last, extendFin]
    simp
  dsimp [lvl] at hrec ⊢
  rw [hpre] at hrec
  rw [hlst] at hrec
  exact hrec

/-- the same one-step identity as a pointwise function equality. -/
lemma lvl_extend_eq {f : ℤ → ℝ} {p : unitInterval} (k : ℕ) (u : Fin k → ℤ)
    (a : ℤ) :
    lvl f p (k + 1) (extendFin u a) =
      (fun t : ℤ => (1 - (p : ℝ)) * lvl f p k u t + (p : ℝ) * lvl f p k u (t + a)) := by
  funext t
  exact lvl_extend_pt k u a t

/-- `lvl` of a prefix of a full vector agrees with `flvl`. -/
lemma lvl_eq_flvl {ℓ : ℕ} (f : ℤ → ℝ) (p : unitInterval) (x : Fin ℓ → ℤ)
    {k : ℕ} (hk : k ≤ ℓ) : lvl f p k (pre x k hk) = flvl f p x k hk := by
  rfl



lemma lvl_zero {f : ℤ → ℝ} {p : unitInterval} (u : Fin 0 → ℤ) : lvl f p 0 u = f := by
  funext t
  dsimp [lvl, avgF]
  have hu : u = (fun _ : Fin 0 => (0 : ℤ)) := by
    funext j
    exact Fin.elim0 j
  rw [hu]
  dsimp [avgF, wB, subSum]
  simp

-- nonneg inheritance
lemma lvl_nonneg {f : ℤ → ℝ} {p : unitInterval} (k : ℕ) (u : Fin k → ℤ)
    (hfpos : ∀ t : ℤ, 0 ≤ f t) : ∀ t : ℤ, 0 ≤ lvl f p k u t := by
  intro t
  dsimp [lvl]
  exact avgF_nonneg (f := f) (p := p) (ℓ := k) (x := u) hfpos t

-- sup inheritance
lemma lvl_le_sup {f : ℤ → ℝ} {p : unitInterval} {M : ℝ} (k : ℕ) (u : Fin k → ℤ)
    (hfsup : ∀ t : ℤ, f t ≤ M) : ∀ t : ℤ, lvl f p k u t ≤ M := by
  intro t
  dsimp [lvl]
  exact Submission.Refine.avgF_le_sup (f := f) (p := p) (M := M) (ℓ := k) (x := u) hfsup t

-- mass inheritance
lemma lvl_mass {f : ℤ → ℝ} {p : unitInterval} {M₀ : ℝ} {N : ℕ} (k : ℕ) (u : Fin k → ℤ)
    (hmass : ∀ a : ℤ, (∑ t ∈ Submission.Ell2Greedy.I0 a N, f t) ≤ M₀) :
    ∀ a : ℤ, (∑ t ∈ Submission.Ell2Greedy.I0 a N, lvl f p k u t) ≤ M₀ := by
  intro a
  dsimp [lvl]
  exact Submission.Refine.avgF_mass_plain (f := f) (p := p) (M₀ := M₀) (ℓ := k) (x := u) (N := N) hmass a



-- ratioLip inheritance: one-step preservation is Ell2Update.ratioLip_avg
lemma lvl_ratioLip {ε : ℝ} {f : ℤ → ℝ} {p : unitInterval} (k : ℕ)
    (hlip : Ell2Update.ratioLip ε f) : ∀ (u : Fin k → ℤ), Ell2Update.ratioLip ε (lvl f p k u) := by
  induction k with
  | zero =>
      intro u
      have hz := lvl_zero (f := f) (p := p) u
      simpa [hz] using hlip
  | succ k ih =>
      intro u
      let v : Fin k → ℤ := restrict u
      let a : ℤ := u (Fin.last k)
      have hw : u = extendFin v a := by
        exact (extend_restrict u).symm
      have hmain : Ell2Update.ratioLip ε
          (fun t : ℤ => (1 - (p : ℝ)) * lvl f p k v t + (p : ℝ) * lvl f p k v (t + a)) := by
        exact Ell2Update.ratioLip_avg (ε := ε) (g := lvl f p k v) (p := (p : ℝ))
          (hlip := ih v) (hp0 := p.property.1) (hp1 := p.property.2) (y := a)
      have hEq : lvl f p (k + 1) u =
          (fun t : ℤ => (1 - (p : ℝ)) * lvl f p k v t + (p : ℝ) * lvl f p k v (t + a)) := by
        rw [hw]
        dsimp [v, a]
        exact lvl_extend_eq k (restrict u) (u (Fin.last k))
      simpa [hEq] using hmain

-- (x+y)² ≤ 2x²+2y² helper
lemma sq_add_le_two (x y : ℝ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  have hE : 2 * x ^ 2 + 2 * y ^ 2 - (x + y) ^ 2 = (x - y) ^ 2 := by ring
  nlinarith [sq_nonneg (x - y)]

-- single-step summability preservation: mix of g and its translate is ℓ₂-sq summable
lemma summable_sq_one_step {g : ℤ → ℝ} {p : unitInterval} (a : ℤ)
    (hg2 : Summable (fun t : ℤ => (g t) ^ 2)) :
    Summable (fun t : ℤ => (((1 - (p : ℝ)) * g t + (p : ℝ) * g (t + a)) : ℝ) ^ 2) := by
  have hpt : ∀ t : ℤ,
      (((1 - (p : ℝ)) * g t + (p : ℝ) * g (t + a)) : ℝ) ^ 2 ≤
        2 * (1 - (p : ℝ)) ^ 2 * (g t) ^ 2 + 2 * (p : ℝ) ^ 2 * (g (t + a)) ^ 2 := by
    intro t
    have h1 := sq_add_le_two ((1 - (p : ℝ)) * g t) ((p : ℝ) * g (t + a))
    have hterm1 : ((1 - (p : ℝ)) * g t) ^ 2 = (1 - (p : ℝ)) ^ 2 * (g t) ^ 2 := by ring
    have hterm2 : ((p : ℝ) * g (t + a)) ^ 2 = (p : ℝ) ^ 2 * (g (t + a)) ^ 2 := by ring
    rw [hterm1, hterm2] at h1
    nlinarith
  have hsum2 : Summable (fun t : ℤ =>
      2 * (1 - (p : ℝ)) ^ 2 * (g t) ^ 2 + 2 * (p : ℝ) ^ 2 * (g (t + a)) ^ 2) := by
    have hA : Summable (fun t : ℤ => 2 * (1 - (p : ℝ)) ^ 2 * (g t) ^ 2) := by
      exact summable_const_mul (2 * (1 - (p : ℝ)) ^ 2) hg2
    have hB : Summable (fun t : ℤ => 2 * (p : ℝ) ^ 2 * (g (t + a)) ^ 2) := by
      exact summable_const_mul (2 * (p : ℝ) ^ 2) (summable_sq_translate_add a hg2)
    exact hA.add hB
  exact Summable.of_nonneg_of_le (fun t => sq_nonneg _) hpt hsum2

-- ℓ₂-sq summability inheritance by induction
lemma lvl_sq_summable {f : ℤ → ℝ} {p : unitInterval} (k : ℕ)
    (hf2 : Summable (fun t : ℤ => (f t) ^ 2)) :
    ∀ (u : Fin k → ℤ), Summable (fun t : ℤ => (lvl f p k u t) ^ 2) := by
  induction k with
  | zero =>
      intro u
      have hz := lvl_zero (f := f) (p := p) u
      rw [hz]
      exact hf2
  | succ k ih =>
      intro u
      let v : Fin k → ℤ := restrict u
      let a : ℤ := u (Fin.last k)
      have hw : u = extendFin v a := by
        exact (extend_restrict u).symm
      have hEq : lvl f p (k + 1) u =
          (fun t : ℤ => (1 - (p : ℝ)) * lvl f p k v t + (p : ℝ) * lvl f p k v (t + a)) := by
        rw [hw]
        dsimp [v, a]
        exact lvl_extend_eq k (restrict u) (u (Fin.last k))
      have hsq := summable_sq_one_step (p := p) (g := lvl f p k v) a (ih v)
      simpa [hEq] using hsq


/-- the flatness (Event) predicate at level `k` of a prefix `u`: every
`N`-interval has at most `μN` points where `lvl ≥ H`. -/
def flatLvl (f : ℤ → ℝ) (p : unitInterval) (H : ℝ) (μ : ℝ) (N : ℕ)
    (k : ℕ) (u : Fin k → ℤ) : Prop :=
  ∀ lo : ℤ, (Refine.spikeCnt (lvl f p k u) H lo N : ℝ) ≤ μ * (N : ℝ)

/-- flatness of the level-`k` function of the length-`k` prefix of a full tuple
(in `flvl` terms, for readability at the export boundary). -/
def flatLvlFlvl {ℓ : ℕ} (f : ℤ → ℝ) (p : unitInterval) (H : ℝ) (μ : ℝ) (N : ℕ)
    (x : Fin ℓ → ℤ) (k : ℕ) (hk : k ≤ ℓ) : Prop :=
  ∀ lo : ℤ, (Refine.spikeCnt (flvl f p x k hk) H lo N : ℝ) ≤ μ * (N : ℝ)


/-- the single-step ℓ₂-drop predicate at step `k`. -/
def dropLvl (f : ℤ → ℝ) (p : unitInterval) (Cdrop : ℝ) (k : ℕ)
    (w : Fin (k + 1) → ℤ) : Prop :=
  norm₂sq (lvl f p (k + 1) w) ≤ norm₂sq (lvl f p k (restrict w)) - Cdrop

/-- the drop predicate, applied to an extension. -/
lemma dropLvl_extend_iff {f : ℤ → ℝ} {p : unitInterval} {Cdrop : ℝ} (k : ℕ)
    (u : Fin k → ℤ) (a : ℤ) :
    dropLvl f p Cdrop k (extendFin u a) ↔
      norm₂sq (lvl f p (k + 1) (extendFin u a)) ≤ norm₂sq (lvl f p k u) - Cdrop := by
  dsimp [dropLvl]
  rw [restrict_extend]

-- norm₂sq of the one-step extension never increases
lemma norm₂sq_lvl_step_le {f : ℤ → ℝ} {p : unitInterval} (k : ℕ) (u : Fin k → ℤ)
    (a : ℤ) (hf2 : Summable (fun t : ℤ => (f t) ^ 2)) :
    norm₂sq (lvl f p (k + 1) (extendFin u a)) ≤ norm₂sq (lvl f p k u) := by
  let g : ℤ → ℝ := lvl f p k u
  have hEq : lvl f p (k + 1) (extendFin u a) =
      (fun t : ℤ => (1 - (p : ℝ)) * g t + (p : ℝ) * g (t + a)) := by
    simpa [g] using lvl_extend_eq k u a
  rw [hEq]
  have hg2 : Summable (fun t : ℤ => (g t) ^ 2) := by
    simpa [g] using lvl_sq_summable k hf2 u
  have hG2 : Summable (fun t : ℤ => (g (t + a)) ^ 2) := summable_sq_translate_add a hg2
  have hmix := norm₂sq_mix_sub (p := (p : ℝ)) (f := g) (g := fun t : ℤ => g (t + a)) hg2 hG2
  have hdrop_nonneg : 0 ≤ (p : ℝ) * (1 - (p : ℝ)) * norm₂sq (fun t : ℤ => g t - g (t + a)) := by
    exact mul_nonneg (mul_nonneg p.property.1 (by linarith [p.property.2])) (norm₂sq_nonneg _)
  calc
    norm₂sq (fun t : ℤ => (1 - (p : ℝ)) * g t + (p : ℝ) * g (t + a))
        = (1 - (p : ℝ)) * norm₂sq g + (p : ℝ) * norm₂sq (fun t : ℤ => g (t + a)) -
            (p : ℝ) * (1 - (p : ℝ)) * norm₂sq (fun t : ℤ => g t - g (t + a)) := by
          simpa using hmix
    _ = norm₂sq g - (p : ℝ) * (1 - (p : ℝ)) * norm₂sq (fun t : ℤ => g t - g (t + a)) := by
          rw [norm₂sq_translate_add a]
          ring
    _ ≤ norm₂sq g := by
          linarith

-- arbitrary (k+1)-vector version (via extend_restrict)
lemma norm₂sq_lvl_le {f : ℤ → ℝ} {p : unitInterval} (k : ℕ) (w : Fin (k + 1) → ℤ)
    (hf2 : Summable (fun t : ℤ => (f t) ^ 2)) :
    norm₂sq (lvl f p (k + 1) w) ≤ norm₂sq (lvl f p k (restrict w)) := by
  have hw : w = extendFin (restrict w) (w (Fin.last k)) := (extend_restrict w).symm
  have hEq := norm₂sq_lvl_step_le (f := f) (p := p) k (restrict w) (w (Fin.last k)) hf2
  nth_rewrite 1 [hw]
  exact hEq

-- recursive drop-count of a length-m vector (steps 0..m-1)
noncomputable def dropCnt (f : ℤ → ℝ) (p : unitInterval) (Cdrop : ℝ) :
    (m : ℕ) → (Fin m → ℤ) → ℕ
  | 0, _ => 0
  | m + 1, x => dropCnt f p Cdrop m (restrict x) + if dropLvl f p Cdrop m x then 1 else 0

-- telescoping: ‖lvl m x‖₂² ≤ ‖f‖₂² − Cdrop·(#dropping steps)
lemma levelNorm_telescope {f : ℤ → ℝ} {p : unitInterval} (Cdrop : ℝ)
    (hf2 : Summable (fun t : ℤ => (f t) ^ 2)) (m : ℕ) (x : Fin m → ℤ) :
    norm₂sq (lvl f p m x) ≤ norm₂sq f - Cdrop * (dropCnt f p Cdrop m x : ℝ) := by
  induction m with
  | zero =>
      have hz : lvl f p 0 x = f := lvl_zero (f := f) (p := p) x
      rw [hz]
      dsimp [dropCnt]
      simp
  | succ m ih =>
      let y : Fin m → ℤ := restrict x
      have hstep : norm₂sq (lvl f p (m + 1) x) ≤
          norm₂sq (lvl f p m y) - (if dropLvl f p Cdrop m x then Cdrop else 0) := by
        by_cases hd : dropLvl f p Cdrop m x
        · rw [if_pos hd]
          simpa [y, dropLvl] using hd
        · rw [if_neg hd]
          have hle := norm₂sq_lvl_le (f := f) (p := p) (k := m) (w := x) hf2
          simpa [y, dropLvl] using hle
      have hdcN : dropCnt f p Cdrop (m + 1) x = dropCnt f p Cdrop m y +
          (if dropLvl f p Cdrop m x then 1 else 0) := by
        dsimp [dropCnt, y]
      have hdc : (dropCnt f p Cdrop (m + 1) x : ℝ) = (dropCnt f p Cdrop m y : ℝ) +
          (if dropLvl f p Cdrop m x then (1 : ℝ) else 0) := by
        rw [hdcN]
        by_cases d : dropLvl f p Cdrop m x <;> simp [d]
      have h2 := ih y
      by_cases d : dropLvl f p Cdrop m x
      · rw [if_pos d] at hstep
        rw [hdc]
        rw [if_pos d]
        nlinarith
      · rw [if_neg d] at hstep
        rw [hdc]
        rw [if_neg d]
        nlinarith


/-- bad level-step predicate (matches PropRefine3.badPred instantiation). -/
def badLvl (f : ℤ → ℝ) (p : unitInterval) (H μ Cdrop : ℝ) (N : ℕ)
    (k : ℕ) (w : Fin (k + 1) → ℤ) : Prop :=
  ¬ flatLvl f p H μ N k (restrict w) ∧ ¬ dropLvl f p Cdrop k w

/-- badness of an extension in terms of the flat/drop predicates on `u`. -/
lemma badLvl_extend {f : ℤ → ℝ} {p : unitInterval} {H μ Cdrop : ℝ} {N : ℕ}
    (k : ℕ) (u : Fin k → ℤ) (a : ℤ) :
    badLvl f p H μ Cdrop N k (extendFin u a) ↔
      (¬ flatLvl f p H μ N k u ∧ ¬ dropLvl f p Cdrop k (extendFin u a)) := by
  dsimp [badLvl]
  rw [restrict_extend]

/-- per-prefix phase-1 counting (instantiation of `Refine3.step_bad_count` with
`g := lvl f p k u`): if the level-`k` function of `u` is NOT flat, then all but
`1024μ|J|` of the next values `a ∈ J` make the extension drop by `Cdrop`. -/
theorem lvl_step_bad_count {f : ℤ → ℝ} {p : unitInterval} {Rt μ L : ℝ} {N n : ℕ}
    {k : ℕ} {u : Fin k → ℤ} {c d : ℤ} {Cdrop H : ℝ}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) ≤ 1 / 2)
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 64)
    (hR0 : 0 < Rt) (hN1 : 1 ≤ N) (hn1 : 1 ≤ n)
    (hL16 : 16 * Rt ≤ L)
    (hCdrop : Cdrop = (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * Rt ^ 2 /
      ((N : ℝ) * (n : ℝ)))
    (hH : H = L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ))))
    (hfpos : ∀ t : ℤ, 0 ≤ f t)
    (hf2 : Summable (fun t : ℤ => (f t) ^ 2))
    (hlip : Ell2Update.ratioLip (μ ^ 4) f)
    (hmass : ∀ lo : ℤ, (∑ t ∈ Ell2Greedy.I0 lo N, f t) ≤ Rt / Real.sqrt (n : ℝ))
    (hJlen : (N : ℝ) ≤ ((Finset.Icc c d).card : ℝ))
    (hnf : ¬ flatLvl f p H μ N k u) :
    ((((Finset.Icc c d).filter (fun a : ℤ => ¬ dropLvl f p Cdrop k (extendFin u a))).card : ℕ) : ℝ) ≤
      1024 * μ * ((Finset.Icc c d).card : ℝ) := by
  classical
  let g : ℤ → ℝ := lvl f p k u
  have hg0 : ∀ t : ℤ, 0 ≤ g t := by
    intro t
    dsimp [g]
    exact lvl_nonneg k u hfpos t
  have hg2 : Summable (fun t : ℤ => (g t) ^ 2) := by
    dsimp [g]
    exact lvl_sq_summable k hf2 u
  have hglip : Ell2Update.ratioLip (μ ^ 4) g := by
    dsimp [g]
    exact lvl_ratioLip k hlip u
  have hgmass : ∀ lo : ℤ, (∑ t ∈ Ell2Greedy.I0 lo N, g t) ≤ Rt / Real.sqrt (n : ℝ) := by
    intro lo
    dsimp [g]
    exact lvl_mass k u hmass lo
  have hnf' : ¬ (∀ lo : ℤ,
      (Refine.spikeCnt (lvl f p k u) (L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ)))) lo N : ℝ) ≤
        μ * (N : ℝ)) := by
    intro h
    apply hnf
    intro lo
    have hlo := h lo
    rwa [hH]
  have hsb := Refine3.step_bad_count (g := lvl f p k u) hp0 hp1 hμ0 hμ1 hR0 hN1 hn1 hL16
    hg0 hg2 hglip hgmass hJlen hnf'
  -- per-value equivalence of the drop predicates
  have hlev : ∀ a : ℤ,
      lvl f p (k + 1) (extendFin u a) =
        (fun t : ℤ => (1 - (p : ℝ)) * g t + (p : ℝ) * g (t + a)) := by
    intro a
    simpa [g] using lvl_extend_eq k u a
  have hif : ∀ a : ℤ, dropLvl f p Cdrop k (extendFin u a) ↔
      (norm₂sq (fun t : ℤ => (1 - (p : ℝ)) * g t + (p : ℝ) * g (t + a)) ≤
        norm₂sq g - (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * Rt ^ 2 /
          ((N : ℝ) * (n : ℝ))) := by
    intro a
    calc
      dropLvl f p Cdrop k (extendFin u a)
          ↔ norm₂sq (lvl f p (k + 1) (extendFin u a)) ≤ norm₂sq (lvl f p k u) - Cdrop :=
            dropLvl_extend_iff k u a
      _ ↔ norm₂sq (lvl f p (k + 1) (extendFin u a)) ≤ norm₂sq g - Cdrop := by
            simp [g]
      _ ↔ norm₂sq (fun t : ℤ => (1 - (p : ℝ)) * g t + (p : ℝ) * g (t + a)) ≤
            norm₂sq g - Cdrop := by
            rw [hlev a]
      _ ↔ norm₂sq (fun t : ℤ => (1 - (p : ℝ)) * g t + (p : ℝ) * g (t + a)) ≤
            norm₂sq g - (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * Rt ^ 2 /
              ((N : ℝ) * (n : ℝ)) := by
            rw [hCdrop]
  have hfilters : (Finset.Icc c d).filter (fun a : ℤ => ¬ dropLvl f p Cdrop k (extendFin u a)) =
      (Finset.Icc c d).filter (fun y : ℤ =>
        ¬ (norm₂sq (fun t : ℤ => (1 - (p : ℝ)) * g t + (p : ℝ) * g (t + y)) ≤
            norm₂sq g - (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * Rt ^ 2 /
              ((N : ℝ) * (n : ℝ)))) := by
    ext a
    rw [Finset.mem_filter, Finset.mem_filter]
    by_cases ha : a ∈ Finset.Icc c d <;> simp [ha, hif a]
  rwa [hfilters]


/-- combined per-prefix bound: whether the level-`k` function is flat or not,
at most `1024μ|J|` next values `a ∈ J` make the extension `(u,a)` bad
(= non-flat current level and no drop). -/
theorem badLvl_step_bound {f : ℤ → ℝ} {p : unitInterval} {Rt μ L : ℝ} {N n : ℕ}
    {k : ℕ} {u : Fin k → ℤ} {c d : ℤ} {Cdrop H : ℝ}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) ≤ 1 / 2)
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 64)
    (hR0 : 0 < Rt) (hN1 : 1 ≤ N) (hn1 : 1 ≤ n)
    (hL16 : 16 * Rt ≤ L)
    (hCdrop : Cdrop = (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * Rt ^ 2 /
      ((N : ℝ) * (n : ℝ)))
    (hH : H = L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ))))
    (hfpos : ∀ t : ℤ, 0 ≤ f t)
    (hf2 : Summable (fun t : ℤ => (f t) ^ 2))
    (hlip : Ell2Update.ratioLip (μ ^ 4) f)
    (hmass : ∀ lo : ℤ, (∑ t ∈ Ell2Greedy.I0 lo N, f t) ≤ Rt / Real.sqrt (n : ℝ))
    (hJlen : (N : ℝ) ≤ ((Finset.Icc c d).card : ℝ)) :
    ((((Finset.Icc c d).filter (fun a : ℤ => badLvl f p H μ Cdrop N k (extendFin u a))).card : ℕ) : ℝ) ≤
      1024 * μ * ((Finset.Icc c d).card : ℝ) := by
  classical
  by_cases hflat : flatLvl f p H μ N k u
  · have hempty : (Finset.Icc c d).filter
        (fun a : ℤ => badLvl f p H μ Cdrop N k (extendFin u a)) = ∅ := by
      ext a
      rw [Finset.mem_filter]
      have hb : badLvl f p H μ Cdrop N k (extendFin u a) ↔ False := by
        rw [badLvl_extend]
        constructor
        · intro h
          exact (h.1 hflat).elim
        · intro h
          exact False.elim h
      simp [hb]
    rw [hempty]
    simp
    positivity
  · have hnf : ¬ flatLvl f p H μ N k u := hflat
    have hmain := lvl_step_bad_count (f := f) (p := p) (Rt := Rt) (μ := μ) (L := L)
      (N := N) (n := n) (k := k) (u := u) (c := c) (d := d) (Cdrop := Cdrop) (H := H)
      hp0 hp1 hμ0 hμ1 hR0 hN1 hn1 hL16 hCdrop hH hfpos hf2 hlip hmass hJlen hnf
    -- on the non-flat branch, badLvl = ¬dropLvl
    have hfilters : (Finset.Icc c d).filter
          (fun a : ℤ => badLvl f p H μ Cdrop N k (extendFin u a)) =
        (Finset.Icc c d).filter (fun a : ℤ => ¬ dropLvl f p Cdrop k (extendFin u a)) := by
      ext a
      rw [Finset.mem_filter, Finset.mem_filter]
      by_cases ha : a ∈ Finset.Icc c d <;> simp [ha, badLvl_extend k u a, hflat]
    rwa [hfilters]


/-- `mu0 := exp(−16M/ε)/(24·1024²)` is positive. -/
lemma mu0_pos (M ε : ℝ) : 0 < PropRefine3.mu0 M ε := by
  dsimp [PropRefine3.mu0]
  exact div_pos (Real.exp_pos _) (by norm_num)

/-- `mu0 := exp(−16M/ε)/(24·1024²) ≤ 1/64` for `1 ≤ M`, `0 < ε`, `ε ≤ 1/2`. -/
lemma mu0_le_64 {M ε : ℝ} (hM : 1 ≤ M) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    PropRefine3.mu0 M ε ≤ 1 / 64 := by
  dsimp [PropRefine3.mu0]
  -- exp(-16M/ε) ≤ 1 (since -16M/ε ≤ 0)
  have hM0 : 0 ≤ M := by linarith
  have hq : 0 ≤ 16 * M / ε := by
    exact div_nonneg (mul_nonneg (by norm_num) hM0) (le_of_lt hε0)
  have hneg : -16 * M / ε ≤ 0 := by
    rw [div_le_iff₀ hε0]
    have h : -16 * M ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-16 : ℝ) ≤ 0) hM0
    simpa using h
  have he1 : Real.exp (-16 * M / ε) ≤ 1 := by
    have hle := (Real.exp_le_exp).2 hneg
    simpa using hle
  have hden : (0 : ℝ) < 24 * 1024 ^ 2 := by norm_num
  have hle1 : Real.exp (-16 * M / ε) / (24 * 1024 ^ 2) ≤ 1 / (24 * 1024 ^ 2) := by
    exact div_le_div_of_nonneg_right he1 (le_of_lt hden)
  have hle2 : 1 / (24 * 1024 ^ 2) ≤ 1 / 64 := by
    norm_num
  linarith

/-- (phase-1 counting, level-function form) with the per-prefix bad-value
fraction `1024·μ` where `μ := mu0 M ε`, the number of full tuples with at
least `⌈m/2⌉` bad level steps is at most `exp(−2Mn)·∏|J_j|`.  Here the level
functions are `lvl f p k u := avgF f p k u` (the paper's `f_{A,p,k}`), `J_j`
are the coordinate intervals, `H := L/(2N√n)` is the flatness height and
`Cdrop` the per-step ℓ₂-drop.  `f` must be a nonnegative, ℓ₂-square-summable,
`ratioLip(μ⁴)`, `N`-window-mass-bounded kernel. -/
theorem phase1_lvl_count {M ε : ℝ} (hM : 1 ≤ M) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
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
    ∀ {c d : Fin m → ℤ},
      (∀ k : Fin m, (N : ℝ) ≤ ((Finset.Icc (c k) (d k)).card : ℝ)) →
      ((((prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))).filter
          (fun x : Fin m → ℤ =>
            (m + 1) / 2 ≤ PropRefine3.nBad
              (fun k : ℕ => fun u : Fin k → ℤ => flatLvl f p H μ N k u)
              (fun k : ℕ => fun w : Fin (k + 1) → ℤ => dropLvl f p Cdrop k w) x)).card : ℕ) : ℝ) ≤
        Real.exp (-2 * M * (n : ℝ)) *
          (∏ j : Fin m, (((Finset.Icc (c j) (d j)).card : ℕ) : ℝ)) := by
  classical
  rcases PropRefine3.phase1_tail (M := M) (ε := ε) hM hε0 hε1 with ⟨n₀, hpt⟩
  refine ⟨n₀, ?_⟩
  intro n hn m hm p hp0 hp1 f hfpos hf2 Rt L hR0 hL16 N hN1 hn1 μ hμeq hμ0 hμ1 H Cdrop hH hCdrop
    hlip hmass c d hJlen
  let J : Fin m → Finset ℤ := fun j => Finset.Icc (c j) (d j)
  have hc0 : 0 ≤ PropRefine3.cPhase1 M ε := by
    dsimp [PropRefine3.cPhase1, PropRefine3.mu0]
    positivity
  have hc : PropRefine3.cPhase1 M ε = 1024 * μ := by
    dsimp [PropRefine3.cPhase1]
    rw [← hμeq]
  have hstep : ∀ (k : ℕ) (hk : k < m) (u : Fin k → ℤ),
      u ∈ prodFinset k (fun j : Fin k => J (Fin.castLE (Nat.le_of_lt hk) j)) →
      ((((J ⟨k, hk⟩).filter (fun a : ℤ =>
          PropRefine3.badPred
            (fun kk : ℕ => fun uu : Fin kk → ℤ => flatLvl f p H μ N kk uu)
            (fun kk : ℕ => fun ww : Fin (kk + 1) → ℤ => dropLvl f p Cdrop kk ww)
            k (extendFin u a))).card : ℕ) : ℝ) ≤
        PropRefine3.cPhase1 M ε * ((J ⟨k, hk⟩).card : ℝ) := by
    intro k hk u hu
    have hb := badLvl_step_bound (f := f) (p := p) (Rt := Rt) (μ := μ) (L := L) (N := N) (n := n)
      (k := k) (u := u) (c := c ⟨k, hk⟩) (d := d ⟨k, hk⟩) (Cdrop := Cdrop) (H := H)
      hp0 hp1 hμ0 hμ1 hR0 hN1 hn1 hL16 hCdrop hH hfpos hf2 hlip hmass ?hJlen
    · have hbad : ∀ a : ℤ,
        PropRefine3.badPred
            (fun kk : ℕ => fun uu : Fin kk → ℤ => flatLvl f p H μ N kk uu)
            (fun kk : ℕ => fun ww : Fin (kk + 1) → ℤ => dropLvl f p Cdrop kk ww)
            k (extendFin u a) ↔
          badLvl f p H μ Cdrop N k (extendFin u a) := by
        intro a
        dsimp [PropRefine3.badPred]
        rw [restrict_extend]
        exact (badLvl_extend k u a).symm
      have hset : (J ⟨k, hk⟩).filter (fun a : ℤ =>
            PropRefine3.badPred
              (fun kk : ℕ => fun uu : Fin kk → ℤ => flatLvl f p H μ N kk uu)
              (fun kk : ℕ => fun ww : Fin (kk + 1) → ℤ => dropLvl f p Cdrop kk ww)
              k (extendFin u a)) =
          (Finset.Icc (c ⟨k, hk⟩) (d ⟨k, hk⟩)).filter (fun a : ℤ =>
            badLvl f p H μ Cdrop N k (extendFin u a)) := by
        ext a
        rw [Finset.mem_filter, Finset.mem_filter]
        by_cases ha : a ∈ Finset.Icc (c ⟨k, hk⟩) (d ⟨k, hk⟩) <;> simp [J, ha, hbad a]
      rw [hc, hset]
      simpa [J] using hb
    · have hJk : (N : ℝ) ≤ (((Finset.Icc (c ⟨k, hk⟩) (d ⟨k, hk⟩)).card : ℕ) : ℝ) := by
        simpa [J] using (hJlen ⟨k, hk⟩)
      exact hJk
  have hfinal := hpt n hn (m := m) hm (J := J)
    (hflat := fun kk : ℕ => fun uu : Fin kk → ℤ => flatLvl f p H μ N kk uu)
    (hdrop := fun kk : ℕ => fun ww : Fin (kk + 1) → ℤ => dropLvl f p Cdrop kk ww)
    hstep
  simpa [J] using hfinal



attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- step-wise drop predicate of a full length-m vector at step i. -/
def stepDrop {f : ℤ → ℝ} {p : unitInterval} (Cdrop : ℝ) {m : ℕ} (x : Fin m → ℤ)
    (i : ℕ) (hi : i < m) : Prop :=
  dropLvl f p Cdrop i (pre x (i + 1) (Nat.succ_le_of_lt hi))

/-- step-wise flatness of the level-i prefix. -/
def stepFlat {f : ℤ → ℝ} {p : unitInterval} (H μ : ℝ) (N : ℕ) {m : ℕ} (x : Fin m → ℤ)
    (i : ℕ) (hi : i < m) : Prop :=
  flatLvl f p H μ N i (pre x i (Nat.le_of_lt hi))

-- restrict of a prefix is the shorter prefix
lemma restrict_pre_eq {ℓ : ℕ} (x : Fin ℓ → ℤ) (i : ℕ) (hi : i < ℓ) :
    restrict (pre x (i + 1) (Nat.succ_le_of_lt hi)) = pre x i (Nat.le_of_lt hi) := by
  funext j
  dsimp [restrict, pre]

-- pre at the full length is the vector
lemma pre_self {ℓ : ℕ} (x : Fin ℓ → ℤ) : pre x ℓ (le_refl ℓ) = x := by
  funext j
  dsimp [pre]

-- pre does not depend on the ≤-proof
lemma pre_irrel {ℓ : ℕ} (x : Fin ℓ → ℤ) {j : ℕ} {p₁ p₂ : j ≤ ℓ} :
    pre x j p₁ = pre x j p₂ := by
  funext q
  dsimp [pre]

/-- cardinality of a filter over `Fin (m+1)` splits into the `castSucc` part
and the last element. -/
lemma card_filter_succ {m : ℕ} (Q : Fin (m + 1) → Prop) [DecidablePred Q] :
    ((Finset.univ : Finset (Fin (m + 1))).filter Q).card =
      ((Finset.univ : Finset (Fin m)).filter (fun j : Fin m => Q (Fin.castSucc j))).card +
        (if Q (Fin.last m) then 1 else 0) := by
  classical
  calc
    ((Finset.univ : Finset (Fin (m + 1))).filter Q).card
        = (∑ i : Fin (m + 1), if Q i then (1 : ℕ) else 0) := by
          rw [Finset.card_filter]
    _ = (∑ i : Fin m, if Q (Fin.castSucc i) then (1 : ℕ) else 0) +
          (if Q (Fin.last m) then (1 : ℕ) else 0) := by
          rw [Fin.sum_univ_castSucc]
    _ = ((Finset.univ : Finset (Fin m)).filter (fun j : Fin m => Q (Fin.castSucc j))).card +
          (if Q (Fin.last m) then 1 else 0) := by
          rw [Finset.card_filter]

-- nBad (with level flat/drop predicates) counts the non-flat non-drop steps.
lemma nBad_eq_stepBad {f : ℤ → ℝ} {p : unitInterval} {H μ Cdrop : ℝ} {N : ℕ}
    {m : ℕ} (x : Fin m → ℤ) :
    PropRefine3.nBad (fun k : ℕ => fun u : Fin k → ℤ => flatLvl f p H μ N k u)
        (fun k : ℕ => fun w : Fin (k + 1) → ℤ => dropLvl f p Cdrop k w) x =
      (((Finset.univ : Finset (Fin m)).filter (fun i : Fin m =>
        ¬ flatLvl f p H μ N i.val (pre x i.val (Nat.le_of_lt i.isLt)) ∧
        ¬ dropLvl f p Cdrop i.val (pre x (i.val + 1) (Nat.succ_le_of_lt i.isLt)))).card) := by
  classical
  let hflat : (k : ℕ) → (Fin k → ℤ) → Prop := fun k u => flatLvl f p H μ N k u
  let hdrop : (k : ℕ) → (Fin (k + 1) → ℤ) → Prop := fun k w => dropLvl f p Cdrop k w
  have hper : ∀ i : Fin m,
      PropRefine3.badPred hflat hdrop i.val (pre x (i.val + 1) (Nat.succ_le_of_lt i.isLt)) ↔
        (¬ flatLvl f p H μ N i.val (pre x i.val (Nat.le_of_lt i.isLt)) ∧
         ¬ dropLvl f p Cdrop i.val (pre x (i.val + 1) (Nat.succ_le_of_lt i.isLt))) := by
    intro i
    dsimp [PropRefine3.badPred, hflat, hdrop]
    rw [restrict_pre_eq x i.val i.isLt]
  have hfilters :
      ((Finset.univ : Finset (Fin m)).filter (fun i : Fin m =>
        PropRefine3.badPred hflat hdrop i.val (pre x (i.val + 1) (Nat.succ_le_of_lt i.isLt)))) =
      ((Finset.univ : Finset (Fin m)).filter (fun i : Fin m =>
        ¬ flatLvl f p H μ N i.val (pre x i.val (Nat.le_of_lt i.isLt)) ∧
        ¬ dropLvl f p Cdrop i.val (pre x (i.val + 1) (Nat.succ_le_of_lt i.isLt)))) := by
    ext i
    by_cases hi : i ∈ (Finset.univ : Finset (Fin m)) <;> simp [hi, hper i]
  calc
    PropRefine3.nBad (fun k : ℕ => fun u : Fin k → ℤ => flatLvl f p H μ N k u)
        (fun k : ℕ => fun w : Fin (k + 1) → ℤ => dropLvl f p Cdrop k w) x
        = (((Finset.univ : Finset (Fin m)).filter (fun i : Fin m =>
            PropRefine3.badPred hflat hdrop i.val (pre x (i.val + 1) (Nat.succ_le_of_lt i.isLt)))).card) := by
          simpa [hflat, hdrop] using (PropRefine3.nBad_eq
            (fun k : ℕ => fun u : Fin k → ℤ => flatLvl f p H μ N k u)
            (fun k : ℕ => fun w : Fin (k + 1) → ℤ => dropLvl f p Cdrop k w) x)
    _ = (((Finset.univ : Finset (Fin m)).filter (fun i : Fin m =>
        ¬ flatLvl f p H μ N i.val (pre x i.val (Nat.le_of_lt i.isLt)) ∧
        ¬ dropLvl f p Cdrop i.val (pre x (i.val + 1) (Nat.succ_le_of_lt i.isLt)))).card) := by
          rw [hfilters]


-- recursive drop-count equals the filter-count over steps
lemma dropCnt_eq_step {f : ℤ → ℝ} {p : unitInterval} (Cdrop : ℝ) {m : ℕ} (x : Fin m → ℤ) :
    dropCnt f p Cdrop m x =
      (((Finset.univ : Finset (Fin m)).filter (fun i : Fin m =>
        dropLvl f p Cdrop i.val (pre x (i.val + 1) (Nat.succ_le_of_lt i.isLt)))).card) := by
  induction m with
  | zero =>
      dsimp [dropCnt]
      simp
  | succ m ih =>
      -- relate the (m+1)-filter to the restrict-x filter and the last step
      have hlast : pre x (m + 1) (Nat.succ_le_of_lt (Fin.last m).isLt) = x := by
        calc
          pre x (m + 1) (Nat.succ_le_of_lt (Fin.last m).isLt) = pre x (m + 1) (le_refl (m + 1)) := by
            apply pre_irrel
          _ = x := by
            exact pre_self (ℓ := m + 1) x
      have hper : ∀ i : Fin m,
          dropLvl f p Cdrop i.val (pre x (i.val + 1) (Nat.succ_le_of_lt (Fin.castSucc i).isLt)) ↔
          dropLvl f p Cdrop i.val (pre (restrict x) (i.val + 1) (Nat.succ_le_of_lt i.isLt)) := by
        intro i
        have hpr : pre (restrict x) (i.val + 1) (Nat.succ_le_of_lt i.isLt) =
            pre x (i.val + 1) (Nat.succ_le_of_lt (Fin.castSucc i).isLt) := by
          calc
            pre (restrict x) (i.val + 1) (Nat.succ_le_of_lt i.isLt)
                = pre x (i.val + 1) (Nat.le_trans (Nat.succ_le_of_lt i.isLt) (Nat.le_succ m)) := by
                  exact (Submission.PropRefine2.pre_restrict_eq (k := m) (v := x) (j := i.val)
                    (hj := Nat.succ_le_of_lt i.isLt)).symm
            _ = pre x (i.val + 1) (Nat.succ_le_of_lt (Fin.castSucc i).isLt) := by
                  apply pre_irrel
        rw [hpr]
      have hfc : ((Finset.univ : Finset (Fin m)).filter (fun i : Fin m =>
            dropLvl f p Cdrop i.val (pre x (i.val + 1) (Nat.succ_le_of_lt (Fin.castSucc i).isLt)))) =
          ((Finset.univ : Finset (Fin m)).filter (fun i : Fin m =>
            dropLvl f p Cdrop i.val (pre (restrict x) (i.val + 1) (Nat.succ_le_of_lt i.isLt)))) := by
        ext i
        by_cases hi : i ∈ (Finset.univ : Finset (Fin m)) <;> simp [hi, hper i]
      have hsc := card_filter_succ (m := m) (Q := fun j : Fin (m + 1) =>
        dropLvl f p Cdrop j.val (pre x (j.val + 1) (Nat.succ_le_of_lt j.isLt)))
      have hsplit : (((Finset.univ : Finset (Fin (m + 1))).filter (fun j : Fin (m + 1) =>
            dropLvl f p Cdrop j.val (pre x (j.val + 1) (Nat.succ_le_of_lt j.isLt)))).card) =
          (((Finset.univ : Finset (Fin m)).filter (fun i : Fin m =>
            dropLvl f p Cdrop i.val (pre (restrict x) (i.val + 1) (Nat.succ_le_of_lt i.isLt)))).card) +
            (if dropLvl f p Cdrop m x then 1 else 0) := by
        calc
          (((Finset.univ : Finset (Fin (m + 1))).filter (fun j : Fin (m + 1) =>
              dropLvl f p Cdrop j.val (pre x (j.val + 1) (Nat.succ_le_of_lt j.isLt)))).card)
              = (((Finset.univ : Finset (Fin m)).filter (fun i : Fin m =>
                  dropLvl f p Cdrop i.val (pre x (i.val + 1) (Nat.succ_le_of_lt (Fin.castSucc i).isLt)))).card) +
                  (if dropLvl f p Cdrop (Fin.last m).val (pre x ((Fin.last m).val + 1) (Nat.succ_le_of_lt (Fin.last m).isLt)) then 1 else 0) := hsc
          _ = (((Finset.univ : Finset (Fin m)).filter (fun i : Fin m =>
                  dropLvl f p Cdrop i.val (pre (restrict x) (i.val + 1) (Nat.succ_le_of_lt i.isLt)))).card) +
                  (if dropLvl f p Cdrop m x then 1 else 0) := by
                rw [hfc]
                congr 1
      calc
        dropCnt f p Cdrop (m + 1) x
            = dropCnt f p Cdrop m (restrict x) + (if dropLvl f p Cdrop m x then 1 else 0) := by
              dsimp [dropCnt]
        _ = (((Finset.univ : Finset (Fin m)).filter (fun i : Fin m =>
                dropLvl f p Cdrop i.val (pre (restrict x) (i.val + 1) (Nat.succ_le_of_lt i.isLt)))).card) +
              (if dropLvl f p Cdrop m x then 1 else 0) := by
              rw [ih (restrict x)]
        _ = (((Finset.univ : Finset (Fin (m + 1))).filter (fun j : Fin (m + 1) =>
                dropLvl f p Cdrop j.val (pre x (j.val + 1) (Nat.succ_le_of_lt j.isLt)))).card) := by
              rw [← hsplit]


/-- deterministic dichotomy of phase 1: a tuple with fewer than `⌈m/2⌉` bad
level-steps (bad = not-flat and no-drop) must have a flat level `≤ m`, provided
the total available ℓ₂² mass `‖f‖₂²` is below `Cdrop·(⌊m/2⌋+1)`. -/
theorem few_bad_implies_flat {f : ℤ → ℝ} {p : unitInterval} {H μ Cdrop : ℝ} {N : ℕ}
    {m : ℕ} (x : Fin m → ℤ)
    (hCdrop0 : 0 ≤ Cdrop)
    (hf2 : Summable (fun t : ℤ => (f t) ^ 2))
    (hfew : PropRefine3.nBad (fun k : ℕ => fun u : Fin k → ℤ => flatLvl f p H μ N k u)
        (fun k : ℕ => fun w : Fin (k + 1) → ℤ => dropLvl f p Cdrop k w) x < (m + 1) / 2)
    (hsmall : norm₂sq f < Cdrop * ((m / 2 + 1 : ℕ) : ℝ)) :
    ∃ (j : ℕ) (hj : j ≤ m), flatLvl f p H μ N j (pre x j hj) := by
  classical
  by_contra hno
  have hnof : ∀ i : Fin m, ¬ flatLvl f p H μ N i.val (pre x i.val (Nat.le_of_lt i.isLt)) := by
    intro i hflat
    exact hno ⟨i.val, Nat.le_of_lt i.isLt, hflat⟩
  have hbad := nBad_eq_stepBad (f := f) (p := p) (H := H) (μ := μ) (Cdrop := Cdrop) (N := N) (x := x)
  have hfc : ((Finset.univ : Finset (Fin m)).filter (fun i : Fin m =>
        ¬ flatLvl f p H μ N i.val (pre x i.val (Nat.le_of_lt i.isLt)) ∧
        ¬ dropLvl f p Cdrop i.val (pre x (i.val + 1) (Nat.succ_le_of_lt i.isLt)))) =
      ((Finset.univ : Finset (Fin m)).filter (fun i : Fin m =>
        ¬ dropLvl f p Cdrop i.val (pre x (i.val + 1) (Nat.succ_le_of_lt i.isLt)))) := by
    ext i
    by_cases hi : i ∈ (Finset.univ : Finset (Fin m)) <;> simp [hi, hnof i]
  have hbad' : PropRefine3.nBad (fun k : ℕ => fun u : Fin k → ℤ => flatLvl f p H μ N k u)
        (fun k : ℕ => fun w : Fin (k + 1) → ℤ => dropLvl f p Cdrop k w) x =
      (((Finset.univ : Finset (Fin m)).filter (fun i : Fin m =>
        ¬ dropLvl f p Cdrop i.val (pre x (i.val + 1) (Nat.succ_le_of_lt i.isLt)))).card) := by
    rw [hbad, hfc]
  have hdc := dropCnt_eq_step (f := f) (p := p) Cdrop (x := x)
  have hsum : PropRefine3.nBad (fun k : ℕ => fun u : Fin k → ℤ => flatLvl f p H μ N k u)
        (fun k : ℕ => fun w : Fin (k + 1) → ℤ => dropLvl f p Cdrop k w) x +
      dropCnt f p Cdrop m x = m := by
    rw [hbad', hdc]
    have hcp := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
      (fun i : Fin m => dropLvl f p Cdrop i.val (pre x (i.val + 1) (Nat.succ_le_of_lt i.isLt)))
    rw [add_comm]
    simpa [Finset.card_univ] using hcp
  have hdropge : ((m / 2 + 1 : ℕ) : ℝ) ≤ (dropCnt f p Cdrop m x : ℝ) := by
    have hnat : (m / 2 + 1 : ℕ) ≤ dropCnt f p Cdrop m x := by
      omega
    exact_mod_cast hnat
  have ht := levelNorm_telescope (f := f) (p := p) Cdrop hf2 m x
  have h0 : 0 ≤ norm₂sq (lvl f p m x) := norm₂sq_nonneg _
  have hCdc : Cdrop * (dropCnt f p Cdrop m x : ℝ) ≤ norm₂sq f := by
    linarith [ht, h0]
  have hmul : Cdrop * ((m / 2 + 1 : ℕ) : ℝ) ≤ Cdrop * (dropCnt f p Cdrop m x : ℝ) :=
    mul_le_mul_of_nonneg_left hdropge hCdrop0
  nlinarith [hsmall, hmul, hCdc]

/-- contrapositive counting form: a tuple with NO flat level `≤ m` must have at
least `⌈m/2⌉` bad steps (hence is counted in the phase-1 export). -/
theorem not_flat_counted {f : ℤ → ℝ} {p : unitInterval} {H μ Cdrop : ℝ} {N : ℕ}
    {m : ℕ} (x : Fin m → ℤ)
    (hCdrop0 : 0 ≤ Cdrop)
    (hf2 : Summable (fun t : ℤ => (f t) ^ 2))
    (hsmall : norm₂sq f < Cdrop * ((m / 2 + 1 : ℕ) : ℝ)) :
    ¬ (∃ (j : ℕ) (hj : j ≤ m), flatLvl f p H μ N j (pre x j hj)) →
      (m + 1) / 2 ≤ PropRefine3.nBad (fun k : ℕ => fun u : Fin k → ℤ => flatLvl f p H μ N k u)
        (fun k : ℕ => fun w : Fin (k + 1) → ℤ => dropLvl f p Cdrop k w) x := by
  intro hno
  by_contra hcnt
  have hfew : PropRefine3.nBad (fun k : ℕ => fun u : Fin k → ℤ => flatLvl f p H μ N k u)
      (fun k : ℕ => fun w : Fin (k + 1) → ℤ => dropLvl f p Cdrop k w) x < (m + 1) / 2 := by
    omega
  exact hno (few_bad_implies_flat (f := f) (p := p) (H := H) (μ := μ) (Cdrop := Cdrop) (N := N)
    (m := m) x hCdrop0 hf2 hfew hsmall)


/-- (phase-1 export, level-function form) the number of tuples whose level
functions have NO flat level `≤ m` is at most `exp(−2Mn)·∏|J_j|`. -/
theorem phase1_no_flat_count {M ε : ℝ} (hM : 1 ≤ M) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
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
      ((((prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))).filter
          (fun x : Fin m → ℤ =>
            ¬ (∃ (j : ℕ) (hj : j ≤ m), flatLvl f p H μ N j (pre x j hj)))).card : ℕ) : ℝ) ≤
        Real.exp (-2 * M * (n : ℝ)) *
          (∏ j : Fin m, (((Finset.Icc (c j) (d j)).card : ℕ) : ℝ)) := by
  classical
  rcases phase1_lvl_count (M := M) (ε := ε) hM hε0 hε1 with ⟨n₀, hpc⟩
  refine ⟨n₀, ?_⟩
  intro n hn m hm p hp0 hp1 f hfpos hf2 Rt L hR0 hL16 N hN1 hn1 μ hμeq hμ0 hμ1 H Cdrop hH hCdrop
    hlip hmass hCdrop0 hsmall c d hJlen
  let J : Fin m → Finset ℤ := fun j => Finset.Icc (c j) (d j)
  have hb := hpc n hn (m := m) hm (p := p) hp0 hp1 (f := f) hfpos hf2 (Rt := Rt) (L := L)
    hR0 hL16 (N := N) hN1 hn1 (μ := μ) hμeq hμ0 hμ1 (H := H) (Cdrop := Cdrop) hH hCdrop
    hlip hmass (c := c) (d := d) hJlen
  let P : Finset (Fin m → ℤ) := prodFinset m J
  let noflatP : (Fin m → ℤ) → Prop := fun x =>
    ¬ (∃ (j : ℕ) (hj : j ≤ m), flatLvl f p H μ N j (pre x j hj))
  let badP : (Fin m → ℤ) → Prop := fun x =>
    (m + 1) / 2 ≤ PropRefine3.nBad
      (fun k : ℕ => fun u : Fin k → ℤ => flatLvl f p H μ N k u)
      (fun k : ℕ => fun w : Fin (k + 1) → ℤ => dropLvl f p Cdrop k w) x
  have hsub : (P.filter noflatP) ⊆ (P.filter badP) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    have hnf := not_flat_counted (f := f) (p := p) (H := H) (μ := μ) (Cdrop := Cdrop) (N := N)
      (m := m) x hCdrop0 hf2 hsmall hx.2
    exact ⟨hx.1, hnf⟩
  have hcard := Finset.card_le_card hsub
  have h1 : (((P.filter noflatP).card : ℕ) : ℝ) ≤ (((P.filter badP).card : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have h2 : (((P.filter badP).card : ℕ) : ℝ) ≤
      Real.exp (-2 * M * (n : ℝ)) * (∏ j : Fin m, (((Finset.Icc (c j) (d j)).card : ℕ) : ℝ)) := by
    simpa [P, J, noflatP, badP] using hb
  simpa [P, J, noflatP, badP] using (le_trans h1 h2)


attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- tail coordinates `i₀, …, i₀+s−1` of a vector `x : Fin ℓ → ℤ` (requires
`i₀+s ≤ ℓ`). -/
def tailVec {ℓ : ℕ} (x : Fin ℓ → ℤ) (i₀ s : ℕ) (hs : i₀ + s ≤ ℓ) : Fin s → ℤ :=
  fun q => x ⟨i₀ + q.val, by have hq := q.isLt; omega⟩

-- pre x (i₀+s) = cat (pre x i₀) (tailVec x i₀ s)
lemma pre_cat_tail {ℓ : ℕ} (x : Fin ℓ → ℤ) {i₀ s : ℕ} (hs : i₀ + s ≤ ℓ) :
    pre x (i₀ + s) hs = Refine2.cat (pre x i₀ (Nat.le_trans (Nat.le_add_right i₀ s) hs))
      (tailVec x i₀ s hs) := by
  funext q
  dsimp [pre, Refine2.cat, tailVec]
  by_cases hq : q.val < i₀
  · simp [hq]
    congr 1
  · simp [hq]
    congr 1
    apply Fin.ext
    simp [Fin.castLE]
    omega

-- the level (i₀+s) function = s-fold average of the level-i₀ function over the tail
lemma lvl_split {f : ℤ → ℝ} {p : unitInterval} {ℓ : ℕ} (x : Fin ℓ → ℤ) {i₀ s : ℕ}
    (hs : i₀ + s ≤ ℓ) :
    lvl f p (i₀ + s) (pre x (i₀ + s) hs) =
      avgF (lvl f p i₀ (pre x i₀ (Nat.le_trans (Nat.le_add_right i₀ s) hs))) p s
        (tailVec x i₀ s hs) := by
  have hcat := Refine2.avgF_cat (f := f) (p := p) (j := i₀) (m := s)
    (v := pre x i₀ (Nat.le_trans (Nat.le_add_right i₀ s) hs)) (w := tailVec x i₀ s hs)
  have hpre := pre_cat_tail (x := x) (hs := hs)
  calc
    lvl f p (i₀ + s) (pre x (i₀ + s) hs)
        = avgF f p (i₀ + s) (pre x (i₀ + s) hs) := rfl
    _ = avgF f p (i₀ + s) (Refine2.cat (pre x i₀ (Nat.le_trans (Nat.le_add_right i₀ s) hs))
          (tailVec x i₀ s hs)) := by rw [hpre]
    _ = avgF (avgF f p i₀ (pre x i₀ (Nat.le_trans (Nat.le_add_right i₀ s) hs))) p s
          (tailVec x i₀ s hs) := by rw [← hcat]
    _ = avgF (lvl f p i₀ (pre x i₀ (Nat.le_trans (Nat.le_add_right i₀ s) hs))) p s
          (tailVec x i₀ s hs) := rfl

/-- `√2 − 1 ≥ 1/3`. -/
lemma sqrt2_sub_one_ge_third : (1 : ℝ) / 3 ≤ Real.sqrt 2 - 1 := by
  have hsq : ((4 : ℝ) / 3) ^ 2 < 2 := by norm_num
  have hs : (4 : ℝ) / 3 < Real.sqrt 2 := by
    have h : ((4 : ℝ) / 3) ^ 2 < (Real.sqrt 2) ^ 2 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      exact hsq
    have habs := (sq_lt_sq.mp h)
    have h1 : 0 ≤ (4 : ℝ) / 3 := by norm_num
    have h2 : 0 ≤ Real.sqrt 2 := by exact Real.sqrt_nonneg 2
    rwa [abs_of_nonneg h1, abs_of_nonneg h2] at habs
  linarith

/-- spike-shrink from a flat level: if level-`i₀` has at most `μN` points `≥ H`
on every `N`-interval (and is bounded by `2H`), then every later level
`i₀+s` has at most `μN/(√2−1)` points `≥ √2H` on every `N`-interval. -/
lemma spikeCnt_lvl_le_of_flat {f : ℤ → ℝ} {p : unitInterval} {H μ : ℝ} {N ℓ : ℕ}
    (x : Fin ℓ → ℤ) {i₀ : ℕ} (hi₀ : i₀ ≤ ℓ)
    (hH0 : 0 < H) (hN1 : 1 ≤ N)
    (hfsup : ∀ t : ℤ, lvl f p i₀ (pre x i₀ hi₀) t ≤ 2 * H)
    (hflat : ∀ lo : ℤ, (Refine.spikeCnt (lvl f p i₀ (pre x i₀ hi₀)) H lo N : ℝ) ≤ μ * (N : ℝ))
    {s : ℕ} (hs : i₀ + s ≤ ℓ) :
    ∀ lo : ℤ,
      (Refine.spikeCnt (lvl f p (i₀ + s) (pre x (i₀ + s) hs)) (Real.sqrt 2 * H) lo N : ℝ) ≤
        μ * (N : ℝ) / (Real.sqrt 2 - 1) := by
  classical
  intro lo
  have hmain := Refine.avgF_spike_shrink (f := lvl f p i₀ (pre x i₀ hi₀)) (p := p)
    (H := H) (μ := μ) (N := N) (ℓ := s) (x := tailVec x i₀ s hs) hH0 hN1 hfsup hflat lo
  have hsplit := lvl_split (f := f) (p := p) (x := x) (i₀ := i₀) (s := s) hs
  have hpre : pre x i₀ (Nat.le_trans (Nat.le_add_right i₀ s) hs) = pre x i₀ hi₀ := by
    exact pre_irrel (x := x)
  rw [hsplit]
  rw [hpre]
  exact hmain

/-- the `3μN` form of the spike bound. -/
lemma spikeCnt_lvl_le_of_flat_three {f : ℤ → ℝ} {p : unitInterval} {H μ : ℝ} {N ℓ : ℕ}
    (x : Fin ℓ → ℤ) {i₀ : ℕ} (hi₀ : i₀ ≤ ℓ)
    (hH0 : 0 < H) (hN1 : 1 ≤ N) (hμ0 : 0 ≤ μ)
    (hfsup : ∀ t : ℤ, lvl f p i₀ (pre x i₀ hi₀) t ≤ 2 * H)
    (hflat : ∀ lo : ℤ, (Refine.spikeCnt (lvl f p i₀ (pre x i₀ hi₀)) H lo N : ℝ) ≤ μ * (N : ℝ))
    {s : ℕ} (hs : i₀ + s ≤ ℓ) :
    ∀ lo : ℤ,
      (Refine.spikeCnt (lvl f p (i₀ + s) (pre x (i₀ + s) hs)) (Real.sqrt 2 * H) lo N : ℝ) ≤
        3 * μ * (N : ℝ) := by
  intro lo
  have hb := spikeCnt_lvl_le_of_flat (f := f) (p := p) (H := H) (μ := μ) (N := N) (x := x)
    hi₀ hH0 hN1 hfsup hflat hs lo
  have hpos : 0 ≤ μ * (N : ℝ) :=
    mul_nonneg hμ0 (by exact_mod_cast (Nat.zero_le N))
  have h31 : (1 : ℝ) ≤ 3 * (Real.sqrt 2 - 1) := by nlinarith [sqrt2_sub_one_ge_third]
  have hle : μ * (N : ℝ) ≤ (3 * μ * (N : ℝ)) * (Real.sqrt 2 - 1) := by
    have hm : μ * (N : ℝ) * 1 ≤ μ * (N : ℝ) * (3 * (Real.sqrt 2 - 1)) :=
      mul_le_mul_of_nonneg_left h31 hpos
    nlinarith
  have hdiv : μ * (N : ℝ) / (Real.sqrt 2 - 1) ≤ 3 * μ * (N : ℝ) :=
    (div_le_iff₀ Refine.sqrt2_sub_one_pos).mpr hle
  exact le_trans hb hdiv


attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- the level index is proof-irrelevant: renaming `k₁` to an equal `k₂` (and
the `≤ ℓ`-proofs) does not change the level function. -/
lemma lvl_index {f : ℤ → ℝ} {p : unitInterval} {ℓ : ℕ} (x : Fin ℓ → ℤ)
    {k₁ k₂ : ℕ} (h : k₁ = k₂) (p₁ : k₁ ≤ ℓ) (p₂ : k₂ ≤ ℓ) :
    lvl f p k₁ (pre x k₁ p₁) = lvl f p k₂ (pre x k₂ p₂) := by
  subst k₂
  congr 1

/-- `Lemma l:aux 07395875092835` iterated (eq. aux 09502875605824): if some
level `i₀ ≤ m` is flat at height `H`, then every level `i ≥ m+1` has at most
`3μN` points `≥ √2H` on every `N`-interval. -/
theorem aux095_spikes {f : ℤ → ℝ} {p : unitInterval} {H μ : ℝ} {N m nn : ℕ}
    (x : Fin nn → ℤ) (hmn : m ≤ nn)
    (hH0 : 0 < H) (hN1 : 1 ≤ N) (hμ0 : 0 ≤ μ)
    (hsup0 : ∀ t : ℤ, f t ≤ 2 * H)
    (hflat : ∃ (i₀ : ℕ) (hi₀m : i₀ ≤ m),
      ∀ lo : ℤ, (Refine.spikeCnt (lvl f p i₀ (pre x i₀ (Nat.le_trans hi₀m hmn))) H lo N : ℝ) ≤
        μ * (N : ℝ)) :
    ∀ (i : ℕ) (hi : i ≤ nn), m + 1 ≤ i →
      ∀ lo : ℤ,
        (Refine.spikeCnt (lvl f p i (pre x i hi)) (Real.sqrt 2 * H) lo N : ℝ) ≤ 3 * μ * (N : ℝ) := by
  classical
  rcases hflat with ⟨i₀, hi₀m, hfi₀⟩
  intro i hi hmi lo
  have hsup_i₀ : ∀ t : ℤ, lvl f p i₀ (pre x i₀ (Nat.le_trans hi₀m hmn)) t ≤ 2 * H := by
    intro t
    exact lvl_le_sup i₀ (pre x i₀ (Nat.le_trans hi₀m hmn)) hsup0 t
  have hi₀i : i₀ ≤ i := by omega
  have hs : i₀ + (i - i₀) ≤ nn := by
    have hsub : i₀ + (i - i₀) = i := Nat.add_sub_of_le hi₀i
    omega
  have hb := spikeCnt_lvl_le_of_flat_three (f := f) (p := p) (H := H) (μ := μ) (N := N)
    (x := x) (i₀ := i₀) (hi₀ := Nat.le_trans hi₀m hmn) hH0 hN1 hμ0 hsup_i₀ hfi₀
    (s := i - i₀) (hs := hs) lo
  have hlvl : lvl f p (i₀ + (i - i₀)) (pre x (i₀ + (i - i₀)) hs) = lvl f p i (pre x i hi) := by
    exact lvl_index (x := x) (Nat.add_sub_of_le hi₀i) hs hi
  rw [hlvl] at hb
  exact hb


attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- every level function is summable whenever the base kernel is summable. -/
lemma lvl_summable {f : ℤ → ℝ} {p : unitInterval} (k : ℕ) (u : Fin k → ℤ)
    (hf : Summable f) : Summable (lvl f p k u) := by
  induction k with
  | zero =>
      have hz : lvl f p 0 u = f := lvl_zero (f := f) (p := p) u
      rw [hz]
      exact hf
  | succ k ih =>
      let v : Fin k → ℤ := restrict u
      let a : ℤ := u (Fin.last k)
      have hEq : lvl f p (k + 1) u =
          (fun t : ℤ => (1 - (p : ℝ)) * lvl f p k v t + (p : ℝ) * lvl f p k v (t + a)) := by
        rw [show u = extendFin v a by exact (extend_restrict u).symm]
        dsimp [v, a]
        exact lvl_extend_eq k (restrict u) (u (Fin.last k))
      rw [hEq]
      have hG : Summable (lvl f p k v) := ih v
      have hA : Summable (fun t : ℤ => (1 - (p : ℝ)) * lvl f p k v t) :=
        summable_const_mul (1 - (p : ℝ)) hG
      have hB : Summable (fun t : ℤ => (p : ℝ) * lvl f p k v (t + a)) := by
        exact summable_const_mul (p : ℝ) (IntFun.summable_translate a hG)
      exact hA.add hB

/-- total mass is preserved by the averaging steps: `‖lvl f p k u‖₁ = ‖f‖₁`. -/
lemma norm₁_lvl {f : ℤ → ℝ} {p : unitInterval} (k : ℕ) (u : Fin k → ℤ)
    (hf : Summable f) : IntFun.norm₁ (lvl f p k u) = IntFun.norm₁ f := by
  induction k with
  | zero =>
      have hz : lvl f p 0 u = f := lvl_zero (f := f) (p := p) u
      rw [hz]
  | succ k ih =>
      let v : Fin k → ℤ := restrict u
      let a : ℤ := u (Fin.last k)
      have hEq : lvl f p (k + 1) u =
          (fun t : ℤ => (1 - (p : ℝ)) * lvl f p k v t + (p : ℝ) * lvl f p k v (t + a)) := by
        rw [show u = extendFin v a by exact (extend_restrict u).symm]
        dsimp [v, a]
        exact lvl_extend_eq k (restrict u) (u (Fin.last k))
      have hG : Summable (lvl f p k v) := lvl_summable k v hf
      have hG2 : Summable (fun t : ℤ => lvl f p k v (t + a)) := IntFun.summable_translate a hG
      calc
        IntFun.norm₁ (lvl f p (k + 1) u)
            = IntFun.norm₁ (fun t : ℤ => (1 - (p : ℝ)) * lvl f p k v t + (p : ℝ) * lvl f p k v (t + a)) := by
              rw [hEq]
        _ = IntFun.norm₁ (fun t : ℤ => (1 - (p : ℝ)) * lvl f p k v t) +
              IntFun.norm₁ (fun t : ℤ => (p : ℝ) * lvl f p k v (t + a)) := by
              exact IntFun.norm₁_add (summable_const_mul (1 - (p : ℝ)) hG)
                (summable_const_mul (p : ℝ) hG2)
        _ = (1 - (p : ℝ)) * IntFun.norm₁ (lvl f p k v) + (p : ℝ) * IntFun.norm₁ (lvl f p k v) := by
              rw [IntFun.norm₁_const_mul (1 - (p : ℝ)) hG]
              rw [IntFun.norm₁_const_mul (p : ℝ) hG2]
              rw [IntFun.norm₁_add_right a hG]
        _ = IntFun.norm₁ (lvl f p k v) := by ring
        _ = IntFun.norm₁ f := ih v

/-- mass-one base kernels keep mass-one level functions. -/
lemma norm₁_lvl_eq_one {f : ℤ → ℝ} {p : unitInterval} (k : ℕ) (u : Fin k → ℤ)
    (hf : Summable f) (hmass : IntFun.norm₁ f = 1) :
    IntFun.norm₁ (lvl f p k u) = 1 := by
  rw [norm₁_lvl k u hf, hmass]

/-- mass-≤-one base kernels keep mass-≤-one level functions. -/
lemma norm₁_lvl_le_one {f : ℤ → ℝ} {p : unitInterval} (k : ℕ) (u : Fin k → ℤ)
    (hf : Summable f) (hmass : IntFun.norm₁ f ≤ 1) :
    IntFun.norm₁ (lvl f p k u) ≤ 1 := by
  rw [norm₁_lvl k u hf]
  exact hmass


/-- the set of points where a nonnegative summable function is `≥ θ > 0` is
finite. -/
lemma finite_ge {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hf : Summable f) {θ : ℝ}
    (hθ : 0 < θ) : Set.Finite {t : ℤ | θ ≤ f t} := by
  classical
  by_contra hnot
  let s : Set ℤ := {t : ℤ | θ ≤ f t}
  have hinf : s.Infinite := hnot
  rcases Set.Infinite.exists_subset_card_eq hinf (⌊IntFun.norm₁ f / θ⌋₊ + 1) with ⟨F, hFs, hFcard⟩
  have hbig : θ * (F.card : ℝ) > IntFun.norm₁ f := by
    have hFc : (F.card : ℝ) = (⌊IntFun.norm₁ f / θ⌋₊ : ℝ) + 1 := by
      rw [hFcard]
      norm_num
    rw [hFc]
    have hlt : IntFun.norm₁ f / θ < (⌊IntFun.norm₁ f / θ⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one (a := IntFun.norm₁ f / θ)
    have hθnz : θ ≠ 0 := ne_of_gt hθ
    have hmul : IntFun.norm₁ f < θ * ((⌊IntFun.norm₁ f / θ⌋₊ : ℝ) + 1) := by
      calc
        IntFun.norm₁ f = θ * (IntFun.norm₁ f / θ) := by field_simp [hθnz]
        _ < θ * ((⌊IntFun.norm₁ f / θ⌋₊ : ℝ) + 1) := mul_lt_mul_of_pos_left hlt hθ
    linarith
  have hsum_ge : θ * (F.card : ℝ) ≤ (∑ t ∈ F, f t) := by
    have hc : (∑ t ∈ F, θ) = θ * (F.card : ℝ) := by
      rw [Finset.sum_const]
      rw [nsmul_eq_mul]
      ring
    rw [← hc]
    apply Finset.sum_le_sum
    intro t ht
    have htm : t ∈ s := by exact (hFs ht)
    dsimp [s] at htm
    exact htm
  have hsum_le : (∑ t ∈ F, f t) ≤ IntFun.norm₁ f := IntFun.Finset_sum_le_norm₁ hfpos hf F
  nlinarith

/-- the number of points with `f ≥ θ` is at most `‖f‖₁/θ`. -/
lemma ncard_ge_le {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hf : Summable f) {θ : ℝ}
    (hθ : 0 < θ) : ((({t : ℤ | θ ≤ f t}).ncard : ℝ) ≤ IntFun.norm₁ f / θ) := by
  classical
  let s : Set ℤ := {t : ℤ | θ ≤ f t}
  have hfin : s.Finite := finite_ge hfpos hf hθ
  let F : Finset ℤ := hfin.toFinset
  have hmem : ∀ t : ℤ, t ∈ F ↔ t ∈ s := by
    intro t
    exact Set.Finite.mem_toFinset hfin
  have hcard : (s.ncard : ℝ) = (F.card : ℝ) := by
    rw [Set.ncard_eq_toFinset_card s hfin]
  have hsum_ge : θ * (F.card : ℝ) ≤ (∑ t ∈ F, f t) := by
    have hc : (∑ t ∈ F, θ) = θ * (F.card : ℝ) := by
      rw [Finset.sum_const]
      rw [nsmul_eq_mul]
      ring
    rw [← hc]
    apply Finset.sum_le_sum
    intro t ht
    have htm : t ∈ s := (hmem t).1 ht
    dsimp [s] at htm
    exact htm
  have hsum_le : (∑ t ∈ F, f t) ≤ IntFun.norm₁ f := IntFun.Finset_sum_le_norm₁ hfpos hf F
  calc
    (s.ncard : ℝ) = (F.card : ℝ) := hcard
    _ ≤ IntFun.norm₁ f / θ := by
      have hstep : (F.card : ℝ) * θ ≤ (∑ t ∈ F, f t) := by simpa [mul_comm] using hsum_ge
      calc
        (F.card : ℝ) ≤ ((∑ t ∈ F, f t) / θ) := (le_div_iff₀ hθ).2 hstep
        _ ≤ IntFun.norm₁ f / θ := div_le_div_of_nonneg_right hsum_le hθ.le

/-- spike count of a level function with mass-≤-1 base: at most `1/η` points
are `≥ η`. -/
lemma lvl_spike_ncard_le_one {f : ℤ → ℝ} {p : unitInterval} {η : ℝ} (k : ℕ)
    (u : Fin k → ℤ) (hfpos : ∀ t : ℤ, 0 ≤ f t) (hf : Summable f)
    (hmass : IntFun.norm₁ f ≤ 1) (hη : 0 < η) :
    ((({t : ℤ | η ≤ lvl f p k u t}).ncard : ℝ) ≤ 1 / η) := by
  have hpos : ∀ t : ℤ, 0 ≤ lvl f p k u t := lvl_nonneg k u hfpos
  have hsum := lvl_summable (p := p) k u hf
  have hb := ncard_ge_le hpos hsum hη
  have hm : IntFun.norm₁ (lvl f p k u) ≤ 1 := norm₁_lvl_le_one (p := p) k u hf hmass
  calc
    (({t : ℤ | η ≤ lvl f p k u t}).ncard : ℝ) ≤ IntFun.norm₁ (lvl f p k u) / η := hb
    _ ≤ 1 / η := div_le_div_of_nonneg_right hm hη.le


attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- (monotone backward walk, level-function form) `Sec3Tower.backward_chain`
restated with the `lvl`-level functions: from any top point `t_top` at level
`ℓ` there is a backward walk `t i (hi : i ≤ ℓ)` whose level values never
increase going up (`lvl`-value at level `i+1` ≤ `lvl`-value at level `i`),
each step adds `0` or the coordinate `y ⟨i,·⟩`, the walk point is independent
of the `≤ ℓ`-proof, and `t ℓ (le_refl ℓ) = t_top`. -/
theorem level_walk_exists {f : ℤ → ℝ} {p : unitInterval} {ℓ : ℕ} (y : Fin ℓ → ℤ)
    (t_top : ℤ) :
    ∃ t : (i : ℕ) → i ≤ ℓ → ℤ,
      (∀ (i : ℕ) {p₁ p₂ : i ≤ ℓ}, t i p₁ = t i p₂) ∧
      t ℓ (le_refl ℓ) = t_top ∧
      (∀ (i : ℕ) (hm1 : i + 1 ≤ ℓ),
          lvl f p (i + 1) (pre y (i + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hm1)))
            (t (i + 1) hm1) ≤
          lvl f p i (pre y i (Nat.le_trans (Nat.le_succ i) hm1))
            (t i (Nat.le_trans (Nat.le_succ i) hm1))) ∧
      (∀ (i : ℕ) (hm1 : i + 1 ≤ ℓ),
          t i (Nat.le_trans (Nat.le_succ i) hm1) =
              t (i + 1) hm1 + y ⟨i, Nat.lt_of_succ_le hm1⟩ ∨
          t i (Nat.le_trans (Nat.le_succ i) hm1) = t (i + 1) hm1) := by
  classical
  let W : BWalk f p y t_top := backward_chain f p y t_top
  refine ⟨W.t, ?_, ?_, ?_, ?_⟩
  · intro i p₁ p₂
    exact W.t_irrel
  · exact W.htop
  · intro i hm1
    simpa [lvl_eq_flvl] using (W.hmono i hm1)
  · intro i hm1
    exact W.hrel i hm1


attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- two-prevalue claim (Prop refinement phase 2): if the level-`(m+1)` value
at `t` reaches `(√2p + 2(1−p))H` while the level-`m` function is bounded by
`2H`, then both level-`m` prevalues (at `t` and at `t + yₘ`) are `≥ √2H`. -/
theorem two_prevalues {f : ℤ → ℝ} {p : unitInterval} {H : ℝ} {ℓ : ℕ} (y : Fin ℓ → ℤ)
    {m : ℕ} (hm : m < ℓ)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) ≤ 1 / 2)
    (hsup : ∀ t : ℤ, lvl f p m (pre y m (Nat.le_of_lt hm)) t ≤ 2 * H)
    (t : ℤ)
    (hbig : (Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ))) * H ≤
      lvl f p (m + 1) (pre y (m + 1) (Nat.succ_le_of_lt hm)) t) :
    Real.sqrt 2 * H ≤ lvl f p m (pre y m (Nat.le_of_lt hm)) t ∧
    Real.sqrt 2 * H ≤ lvl f p m (pre y m (Nat.le_of_lt hm)) (t + y ⟨m, hm⟩) := by
  classical
  have hconv : lvl f p (m + 1) (pre y (m + 1) (Nat.succ_le_of_lt hm)) t =
      (1 - (p : ℝ)) * lvl f p m (pre y m (Nat.le_of_lt hm)) t +
        (p : ℝ) * lvl f p m (pre y m (Nat.le_of_lt hm)) (t + y ⟨m, hm⟩) := by
    calc
      lvl f p (m + 1) (pre y (m + 1) (Nat.succ_le_of_lt hm)) t
          = flvl f p y (m + 1) (Nat.succ_le_of_lt hm) t := by rw [lvl_eq_flvl]
      _ = (1 - (p : ℝ)) * flvl f p y m (Nat.le_of_lt hm) t +
            (p : ℝ) * flvl f p y m (Nat.le_of_lt hm) (t + y ⟨m, hm⟩) := flvl_rec hm t
      _ = (1 - (p : ℝ)) * lvl f p m (pre y m (Nat.le_of_lt hm)) t +
            (p : ℝ) * lvl f p m (pre y m (Nat.le_of_lt hm)) (t + y ⟨m, hm⟩) := by
            rw [lvl_eq_flvl]
  rw [hconv] at hbig
  exact Refine.two_sides_of_high
    (A := lvl f p m (pre y m (Nat.le_of_lt hm)) t)
    (B := lvl f p m (pre y m (Nat.le_of_lt hm)) (t + y ⟨m, hm⟩))
    (H := H) (p := (p : ℝ)) (hsup t) (hsup (t + y ⟨m, hm⟩)) hp0 hp1 hbig


attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- aux095 for every level at or above the flat level: with a flat level `i₀`
at height `H` (`f ≤ 2H` pointwise), every level `i ≥ i₀` has at most `3μN`
points `≥ √2H` on every `N`-interval.  (Includes level `i₀` itself: its
`√2H`-spikes are a subset of its `H`-spikes, `≤ μN ≤ 3μN`.) -/
theorem aux095_all {f : ℤ → ℝ} {p : unitInterval} {H μ : ℝ} {N nn : ℕ}
    (x : Fin nn → ℤ) {i₀ : ℕ} (hi₀ : i₀ ≤ nn)
    (hH0 : 0 < H) (hN1 : 1 ≤ N) (hμ0 : 0 ≤ μ)
    (hsup0 : ∀ t : ℤ, f t ≤ 2 * H)
    (hflat : ∀ lo : ℤ, (Refine.spikeCnt (lvl f p i₀ (pre x i₀ hi₀)) H lo N : ℝ) ≤ μ * (N : ℝ)) :
    ∀ (i : ℕ) (hi : i ≤ nn), i₀ ≤ i →
      ∀ lo : ℤ,
        (Refine.spikeCnt (lvl f p i (pre x i hi)) (Real.sqrt 2 * H) lo N : ℝ) ≤ 3 * μ * (N : ℝ) := by
  classical
  intro i hi hi0i lo
  have hsup_i₀ : ∀ t : ℤ, lvl f p i₀ (pre x i₀ hi₀) t ≤ 2 * H := by
    intro t
    exact lvl_le_sup i₀ (pre x i₀ hi₀) hsup0 t
  by_cases hsub : i₀ < i
  · have hi0ile : i₀ ≤ i := le_of_lt hsub
    let s : ℕ := i - i₀
    have hs : i₀ + s ≤ nn := by
      dsimp [s]
      have hsubadd : i₀ + (i - i₀) = i := Nat.add_sub_of_le hi0ile
      omega
    have hb := spikeCnt_lvl_le_of_flat_three (f := f) (p := p) (H := H) (μ := μ) (N := N)
      (x := x) (i₀ := i₀) (hi₀ := hi₀) hH0 hN1 hμ0 hsup_i₀ hflat (s := s) (hs := hs) lo
    have hlvl : lvl f p (i₀ + (i - i₀)) (pre x (i₀ + (i - i₀)) hs) = lvl f p i (pre x i hi) := by
      exact lvl_index (x := x) (Nat.add_sub_of_le hi0ile) hs hi
    rw [hlvl] at hb
    exact hb
  · have heq : i = i₀ := le_antisymm (le_of_not_gt hsub) hi0i
    have hlvl : lvl f p i (pre x i hi) = lvl f p i₀ (pre x i₀ hi₀) := by
      exact lvl_index (x := x) heq hi hi₀
    have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
      have hs : 1 < Real.sqrt 2 := by
        have hpos := Refine.sqrt2_sub_one_pos
        linarith
      exact le_of_lt hs
    have hge : H ≤ Real.sqrt 2 * H := by
      calc
        H = 1 * H := by ring
        _ ≤ Real.sqrt 2 * H := mul_le_mul_of_nonneg_right hsqrt hH0.le
    have hsubs : ((Ell2Greedy.I0 lo N).filter (fun t : ℤ => Real.sqrt 2 * H ≤ lvl f p i₀ (pre x i₀ hi₀) t)) ⊆
        ((Ell2Greedy.I0 lo N).filter (fun t : ℤ => H ≤ lvl f p i₀ (pre x i₀ hi₀) t)) := by
      intro t ht
      rw [Finset.mem_filter] at ht ⊢
      exact ⟨ht.1, le_trans hge ht.2⟩
    have hcard := Finset.card_le_card hsubs
    have h3 : μ * (N : ℝ) ≤ 3 * μ * (N : ℝ) := by
      have hN0 : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
      have hμN0 : 0 ≤ μ * (N : ℝ) := mul_nonneg hμ0 hN0
      nlinarith
    have hb : (Refine.spikeCnt (lvl f p i₀ (pre x i₀ hi₀)) (Real.sqrt 2 * H) lo N : ℝ) ≤
        3 * μ * (N : ℝ) := by
      calc
        (Refine.spikeCnt (lvl f p i₀ (pre x i₀ hi₀)) (Real.sqrt 2 * H) lo N : ℝ)
            ≤ (Refine.spikeCnt (lvl f p i₀ (pre x i₀ hi₀)) H lo N : ℝ) := by
              exact_mod_cast hcard
        _ ≤ μ * (N : ℝ) := hflat lo
        _ ≤ 3 * μ * (N : ℝ) := h3
    rw [hlvl]
    exact hb

/-- aux095 in the `∃ i₀ ≤ m` Event form, for EVERY level `i ≥ m` (not just
`i ≥ m+1`): the prevalue level `m` of the first walk step is covered. -/
theorem aux095_ge_m {f : ℤ → ℝ} {p : unitInterval} {H μ : ℝ} {N m nn : ℕ}
    (x : Fin nn → ℤ) (hmn : m ≤ nn)
    (hH0 : 0 < H) (hN1 : 1 ≤ N) (hμ0 : 0 ≤ μ)
    (hsup0 : ∀ t : ℤ, f t ≤ 2 * H)
    (hflat : ∃ (i₀ : ℕ) (hi₀m : i₀ ≤ m),
      ∀ lo : ℤ, (Refine.spikeCnt (lvl f p i₀ (pre x i₀ (Nat.le_trans hi₀m hmn))) H lo N : ℝ) ≤
        μ * (N : ℝ)) :
    ∀ (i : ℕ) (hi : i ≤ nn), m ≤ i →
      ∀ lo : ℤ,
        (Refine.spikeCnt (lvl f p i (pre x i hi)) (Real.sqrt 2 * H) lo N : ℝ) ≤ 3 * μ * (N : ℝ) := by
  classical
  rcases hflat with ⟨i₀, hi₀m, hfi₀⟩
  intro i hi hmi lo
  have hi0i : i₀ ≤ i := by omega
  exact aux095_all (x := x) (i₀ := i₀) (hi₀ := Nat.le_trans hi₀m hmn) hH0 hN1 hμ0 hsup0 hfi₀
    i hi hi0i lo


attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- (esup parity core) adding one averaging step never increases the supremum:
`esup g_{ℓ+1} ≤ esup g_ℓ` for the prefix level functions of a length-`(ℓ+1)`
vector. -/
lemma esup_lvl_step_le {f : ℤ → ℝ} {p : unitInterval} {ℓ : ℕ}
    (x : Fin (ℓ + 1) → ℤ) (hfpos : ∀ t : ℤ, 0 ≤ f t) (hf : Summable f) :
    Sec3Tower.esup (lvl f p (ℓ + 1) (pre x (ℓ + 1) (Nat.succ_le_of_lt (Nat.lt_succ_self ℓ)))) ≤
    Sec3Tower.esup (lvl f p ℓ (pre x ℓ (Nat.le_of_lt (Nat.lt_succ_self ℓ)))) := by
  classical
  let A : ℤ → ℝ := lvl f p (ℓ + 1) (pre x (ℓ + 1) (Nat.succ_le_of_lt (Nat.lt_succ_self ℓ)))
  let B : ℤ → ℝ := lvl f p ℓ (pre x ℓ (Nat.le_of_lt (Nat.lt_succ_self ℓ)))
  have hposB : ∀ t : ℤ, 0 ≤ B t := by
    intro t
    dsimp [B]
    exact lvl_nonneg ℓ (pre x ℓ (Nat.le_of_lt (Nat.lt_succ_self ℓ))) hfpos t
  have hsumB : Summable B := by
    dsimp [B]
    exact lvl_summable ℓ (pre x ℓ (Nat.le_of_lt (Nat.lt_succ_self ℓ))) hf
  -- per-point: A t ≤ esup B
  have hpt : ∀ t : ℤ, A t ≤ Sec3Tower.esup B := by
    intro t
    have hrec := flvl_rec (f := f) (p := p) (x := x) (m := ℓ) (Nat.lt_succ_self ℓ) t
    -- convert flvl to lvl
    have hA : A t = (1 - (p : ℝ)) * B t + (p : ℝ) * B (t + x ⟨ℓ, Nat.lt_succ_self ℓ⟩) := by
      dsimp [A, B]
      simpa [lvl_eq_flvl] using hrec
    have hmax : (1 - (p : ℝ)) * B t + (p : ℝ) * B (t + x ⟨ℓ, Nat.lt_succ_self ℓ⟩) ≤
        max (B t) (B (t + x ⟨ℓ, Nat.lt_succ_self ℓ⟩)) := by
      have hp0 : 0 ≤ (p : ℝ) := p.property.1
      have hp1m : 0 ≤ 1 - (p : ℝ) := by linarith [p.property.2]
      calc
        (1 - (p : ℝ)) * B t + (p : ℝ) * B (t + x ⟨ℓ, Nat.lt_succ_self ℓ⟩)
            ≤ (1 - (p : ℝ)) * max (B t) (B (t + x ⟨ℓ, Nat.lt_succ_self ℓ⟩)) +
                (p : ℝ) * max (B t) (B (t + x ⟨ℓ, Nat.lt_succ_self ℓ⟩)) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left (le_max_left _ _) hp1m)
                (mul_le_mul_of_nonneg_left (le_max_right _ _) hp0)
        _ = max (B t) (B (t + x ⟨ℓ, Nat.lt_succ_self ℓ⟩)) := by ring
    have hle1 : B t ≤ Sec3Tower.esup B := Sec3Tower.le_esup hposB hsumB t
    have hle2 : B (t + x ⟨ℓ, Nat.lt_succ_self ℓ⟩) ≤ Sec3Tower.esup B :=
      Sec3Tower.le_esup hposB hsumB (t + x ⟨ℓ, Nat.lt_succ_self ℓ⟩)
    calc
      A t = (1 - (p : ℝ)) * B t + (p : ℝ) * B (t + x ⟨ℓ, Nat.lt_succ_self ℓ⟩) := hA
      _ ≤ max (B t) (B (t + x ⟨ℓ, Nat.lt_succ_self ℓ⟩)) := hmax
      _ ≤ Sec3Tower.esup B := max_le hle1 hle2
  -- esup A ≤ esup B via csSup_le over range A
  dsimp [Sec3Tower.esup, A, B]
  apply csSup_le
  · exact ⟨A 0, ⟨0, rfl⟩⟩
  · intro b hb
    rcases hb with ⟨t, rfl⟩
    exact hpt t

/-- (esup parity) `esup g_{2m+1} ≤ esup g_{2m}`: the level-`(2m+1)` function
never exceeds the level-`2m` one in supremum. -/
lemma esup_parity {f : ℤ → ℝ} {p : unitInterval} {m : ℕ}
    (x : Fin (2 * m + 1) → ℤ) (hfpos : ∀ t : ℤ, 0 ≤ f t) (hf : Summable f) :
    Sec3Tower.esup (lvl f p (2 * m + 1) (pre x (2 * m + 1) (le_refl (2 * m + 1)))) ≤
    Sec3Tower.esup (lvl f p (2 * m) (pre x (2 * m) (by omega : 2 * m ≤ 2 * m + 1))) := by
  have hm : 2 * m < 2 * m + 1 := by omega
  have h := esup_lvl_step_le (f := f) (p := p) (ℓ := 2 * m) x hfpos hf
  -- h: esup (lvl f p (2m+1) (pre x (2m+1) (succ_le_of_lt (lt_succ_self (2m))))) ≤ esup (lvl f p (2m) (pre x (2m) (le_of_lt (lt_succ_self (2m)))))
  simpa [pre_hm_irrel x] using h


end Submission.PropRefineExport
