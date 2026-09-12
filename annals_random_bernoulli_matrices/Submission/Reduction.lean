import Mathlib
import Submission.PropRefinePhase2
import Submission.PropRefineExport
import Submission.Sec3Tower
import Submission.Commons.Data.Finset.fiber_filter_product_card_real
import Submission.Commons.Analysis.Real.phase2_tail_N

open Submission.PropRefinePhase2
open Submission.PropRefineExport
open Submission.Sec3Tower
open Submission.ProdCount
open Submission.L2Norm
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

namespace Submission.Reduction

attribute [local instance] Classical.propDecidable

/-!
# Deterministic reduction for Prop. refinement, phase 2 (ingredient 4)

On a tuple `x : Fin (2*m) → ℤ` whose level-`2m` function reaches
`T := (√2 p + 2(1−p))H` in supremum, the backward walk (from the top level
down to level `m`) provides a start point `s₀` at level `m` with value `≥ √2H`
and a `{0,1}`-choice sequence `v` such that EVERY tail step survives: at each
step `k < m`, both level-`(m+k)` prevalues of the partial tail stay `≥ √2H`
(`goodAll (goodStepFam pref v s₀) (tailOf x)`).
-/

/-- the last `m` coordinates of a `2m`-vector (`X_{m+1}, …, X_{2m}`). -/
def tailOf {m : ℕ} (x : Fin (2 * m) → ℤ) : Fin m → ℤ :=
  fun j => x ⟨m + j.val, by omega⟩

/-- `pre z (k+1)` is `pre z k` extended by the value `z ⟨k⟩`. -/
lemma pre_succ_extend {ℓ : ℕ} (z : Fin ℓ → ℤ) {k : ℕ} (hk : k < ℓ) :
    pre z (k + 1) (Nat.succ_le_of_lt hk) =
      extendFin (pre z k (Nat.le_of_lt hk)) (z ⟨k, hk⟩) := by
  have h := extend_restrict (x := pre z (k + 1) (Nat.succ_le_of_lt hk))
  have hrest : restrict (pre z (k + 1) (Nat.succ_le_of_lt hk)) = pre z k (Nat.le_of_lt hk) := by
    funext j
    rfl
  have hlast : (pre z (k + 1) (Nat.succ_le_of_lt hk)) (Fin.last k) = z ⟨k, hk⟩ := by
    rfl
  rw [hrest, hlast] at h
  exact h.symm

/-- coordinates of `pre (tailOf x) k` are the corresponding tail coordinates of `x`. -/
lemma pre_tail_coord {m : ℕ} (x : Fin (2 * m) → ℤ) {k : ℕ} (hk : k ≤ m) (j : Fin k) :
    pre (tailOf x) k hk j = x ⟨m + j.val, by omega⟩ := by
  rfl

/-- the `(m+k)`-prefix of `x` equals the first `m` coordinates followed by the
first `k` tail coordinates (vector-bridge for the level functions). -/
lemma partialVec_tail {m : ℕ} (x : Fin (2 * m) → ℤ) {k : ℕ} (hk : k < m) :
    partialVec (pre x m (by omega : m ≤ 2 * m)) (pre (tailOf x) k (Nat.le_of_lt hk)) =
      pre x (m + k) (by omega : m + k ≤ 2 * m) := by
  let w : Fin (m + k) → ℤ := pre x (m + k) (by omega : m + k ≤ 2 * m)
  have hp := partialVec_pre_eq (m := m) (k := k) (w := w)
  have h1 : pre w m (Nat.le_add_right m k) = pre x m (by omega : m ≤ 2 * m) := by
    funext j
    rfl
  have h2 : (fun j : Fin k => w ⟨m + j.val, by omega⟩) = pre (tailOf x) k (Nat.le_of_lt hk) := by
    funext j
    rfl
  calc
    partialVec (pre x m (by omega : m ≤ 2 * m)) (pre (tailOf x) k (Nat.le_of_lt hk))
        = partialVec (pre w m (Nat.le_add_right m k)) (fun j : Fin k => w ⟨m + j.val, by omega⟩) := by
          rw [h1.symm, h2.symm]
    _ = w := hp
    _ = pre x (m + k) (by omega : m + k ≤ 2 * m) := by rfl

/-- `walkPt` of a one-step-extended tail subtracts `v⟨k⟩·a`. -/
lemma walkPt_extend {m : ℕ} (v : Fin m → ℤ) (p0 : ℤ) {k : ℕ} (hk : k < m)
    (u : Fin k → ℤ) (a : ℤ) :
    walkPt v p0 (extendFin u a) = walkPt v p0 u - v ⟨k, hk⟩ * a := by
  dsimp [walkPt]
  rw [Fin.sum_univ_castSucc]
  have hsum : (∑ q : Fin k,
        (if hq : (Fin.castSucc q).val < m then
            v ⟨(Fin.castSucc q).val, hq⟩ * (extendFin u a) (Fin.castSucc q) else 0)) =
      (∑ q : Fin k, (if hq : q.val < m then v ⟨q.val, hq⟩ * u q else 0)) := by
    apply Finset.sum_congr rfl
    intro q hq'
    have hqlt : q.val < m := lt_trans q.isLt hk
    rw [dif_pos hqlt]
    rw [extendFin_of_lt]
    simp [hqlt]
  have hlast : (if hq : (Fin.last k).val < m then
        v ⟨(Fin.last k).val, hq⟩ * (extendFin u a) (Fin.last k) else 0) =
      v ⟨k, hk⟩ * a := by
    have hkl : (Fin.last k).val < m := by
      dsimp [Fin.last]
      omega
    rw [dif_pos hkl]
    rw [extendFin_last]
    congr 2
  calc
    p0 - ((∑ q : Fin k,
        (if hq : (Fin.castSucc q).val < m then
            v ⟨(Fin.castSucc q).val, hq⟩ * (extendFin u a) (Fin.castSucc q) else 0)) +
      (if hq : (Fin.last k).val < m then
        v ⟨(Fin.last k).val, hq⟩ * (extendFin u a) (Fin.last k) else 0))
        = p0 - ((∑ q : Fin k, (if hq : q.val < m then v ⟨q.val, hq⟩ * u q else 0)) +
            v ⟨k, hk⟩ * a) := by
          rw [hsum, hlast]
    _ = (p0 - (∑ q : Fin k, (if hq : q.val < m then v ⟨q.val, hq⟩ * u q else 0))) -
        v ⟨k, hk⟩ * a := by
          ring

/-- `goodStep` rewritten with the level-`(m+k)` values at the NEXT walk point
`walkPt v s₀ (extendFin u a)` and that point plus `a`. -/
lemma goodStep_iff_two {f : ℤ → ℝ} {p : unitInterval} {H : ℝ} {m : ℕ}
    (pref : Fin m → ℤ) (v : Fin m → ℤ) (s₀ : ℤ) {k : ℕ} (hk : k < m)
    (u : Fin k → ℤ) (a : ℤ) :
    goodStep (f := f) (p := p) (H := H) (m := m) pref v s₀ hk u a ↔
      Real.sqrt 2 * H ≤ lvl f p (m + k) (partialVec pref u)
          (walkPt v s₀ (extendFin u a)) ∧
      Real.sqrt 2 * H ≤ lvl f p (m + k) (partialVec pref u)
          (walkPt v s₀ (extendFin u a) + a) := by
  classical
  have hpn : walkPt v s₀ (extendFin u a) =
      walkPt v s₀ u - v ⟨k, hk⟩ * a := walkPt_extend v s₀ hk u a
  have hp1 : walkPt v s₀ u - v ⟨k, hk⟩ * a = walkPt v s₀ (extendFin u a) := hpn.symm
  have hp2 : walkPt v s₀ u + (1 - v ⟨k, hk⟩) * a =
      walkPt v s₀ (extendFin u a) + a := by
    calc
      walkPt v s₀ u + (1 - v ⟨k, hk⟩) * a
          = (walkPt v s₀ u - v ⟨k, hk⟩ * a) + a := by ring
      _ = walkPt v s₀ (extendFin u a) + a := by rw [hpn.symm]
  constructor
  · intro hg
    dsimp [goodStep] at hg
    rw [hp1, hp2] at hg
    exact hg
  · intro hg
    dsimp [goodStep]
    rw [hp1, hp2]
    exact hg


/-! ## walk-choice sequence -/

/-- the first `hrel` disjunct at tail-step `i` (the walk point at level `m+i`
moves down by adding coordinate `m+i`). -/
def firstRel {m : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin (2 * m) → ℤ} {t_top : ℤ}
    (W : BWalk f p x t_top) (i : Fin m) : Prop :=
  W.t (m + i.val) (by omega : m + i.val ≤ 2 * m) =
    W.t (m + i.val + 1) (by omega : m + i.val + 1 ≤ 2 * m) + x ⟨m + i.val, by omega⟩

/-- `{0,1}`-choice sequence induced by the walk's `hrel` disjunctions. -/
noncomputable def walkV {m : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin (2 * m) → ℤ} {t_top : ℤ}
    (W : BWalk f p x t_top) : Fin m → ℤ :=
  fun i => if firstRel W i then 1 else 0

/-- membership of the induced sequence in `SeqSet`. -/
lemma walkV_mem {m : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin (2 * m) → ℤ} {t_top : ℤ}
    (W : BWalk f p x t_top) : walkV W ∈ SeqSet m := by
  rw [mem_SeqSet]
  intro i
  by_cases h : firstRel W i
  · right
    simp [walkV, h]
  · left
    simp [walkV, h]

/-- `walkV` takes the value `1` exactly at the `firstRel` steps. -/
lemma walkV_eq_one {m : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin (2 * m) → ℤ} {t_top : ℤ}
    (W : BWalk f p x t_top) {k : ℕ} (hk : k < m) :
    walkV W ⟨k, hk⟩ = 1 ↔ firstRel W ⟨k, hk⟩ := by
  by_cases h : firstRel W ⟨k, hk⟩
  · simp [walkV, h]
  · simp [walkV, h]

/-- `hrel` at level `m+k` is exactly the disjunction used by `firstRel`. -/
lemma hrel_first_iff {m : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin (2 * m) → ℤ} {t_top : ℤ}
    (W : BWalk f p x t_top) {k : ℕ} (hk : k < m) (hm1 : m + k + 1 ≤ 2 * m) :
    firstRel W ⟨k, hk⟩ ↔
      W.t (m + k) (Nat.le_trans (Nat.le_succ (m + k)) hm1) =
        W.t (m + k + 1) hm1 + x ⟨m + k, Nat.lt_of_succ_le hm1⟩ := by
  dsimp [firstRel]
  constructor
  · intro h
    rwa [show W.t (m + k) (by omega : m + k ≤ 2 * m) =
        W.t (m + k) (Nat.le_trans (Nat.le_succ (m + k)) hm1) by
          exact W.t_irrel,
      show W.t (m + k + 1) (by omega : m + k + 1 ≤ 2 * m) =
        W.t (m + k + 1) hm1 by
          exact W.t_irrel,
      show x ⟨m + k, by omega⟩ = x ⟨m + k, Nat.lt_of_succ_le hm1⟩ by rfl]
  · intro h
    rwa [show W.t (m + k) (Nat.le_trans (Nat.le_succ (m + k)) hm1) =
        W.t (m + k) (by omega : m + k ≤ 2 * m) by
          exact (W.t_irrel).symm,
      show W.t (m + k + 1) hm1 =
        W.t (m + k + 1) (by omega : m + k + 1 ≤ 2 * m) by
          exact (W.t_irrel).symm,
      show x ⟨m + k, Nat.lt_of_succ_le hm1⟩ = x ⟨m + k, by omega⟩ by rfl]

/-- the `walkPt` of the induced choices along the `(k+1)`-tail-prefix reaches
the walk point at level `m+k+1` (walk/tail consistency). -/
lemma walkPt_prez_succ {m : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin (2 * m) → ℤ} {t_top : ℤ}
    (W : BWalk f p x t_top) {s₀ : ℤ} {k : ℕ} (hk : k < m)
    (hstep : walkPt (walkV W) s₀ (pre (tailOf x) k (Nat.le_of_lt hk)) =
      W.t (m + k) (by omega : m + k ≤ 2 * m)) :
    walkPt (walkV W) s₀ (pre (tailOf x) (k + 1) (Nat.succ_le_of_lt hk)) =
      W.t (m + k + 1) (by omega : m + k + 1 ≤ 2 * m) := by
  classical
  have hsx := pre_succ_extend (z := tailOf x) (k := k) hk
  rw [hsx]
  have hext := walkPt_extend (v := walkV W) s₀ hk (pre (tailOf x) k (Nat.le_of_lt hk))
    (tailOf x ⟨k, hk⟩)
  rw [hext]
  rw [hstep]
  have hxcoord : tailOf x ⟨k, hk⟩ = x ⟨m + k, by omega⟩ := by rfl
  rw [hxcoord]
  have hm1 : m + k + 1 ≤ 2 * m := by omega
  have hrel := W.hrel (m + k) hm1
  have hfirst := hrel_first_iff (W := W) hk hm1
  by_cases hfirstA : firstRel W ⟨k, hk⟩
  · have hA : W.t (m + k) (Nat.le_trans (Nat.le_succ (m + k)) hm1) =
        W.t (m + k + 1) hm1 + x ⟨m + k, Nat.lt_of_succ_le hm1⟩ := (hfirst.mp hfirstA)
    have hv : walkV W ⟨k, hk⟩ = 1 := (walkV_eq_one W hk).mpr hfirstA
    rw [hv]
    -- target now: W.t (m+k) (by omega) - x⟨m+k, by omega⟩ = W.t (m+k+1) (by omega)
    rw [show W.t (m + k) (by omega : m + k ≤ 2 * m) =
        W.t (m + k) (Nat.le_trans (Nat.le_succ (m + k)) hm1) by
          exact W.t_irrel] 
    -- hmm: still W.t(m+k) minus x = W.t(m+k+1) by omega; use hA (with the other index proofs)
    rw [show x ⟨m + k, by omega⟩ = x ⟨m + k, Nat.lt_of_succ_le hm1⟩ by rfl]
    rw [hA]
    rw [show W.t (m + k + 1) (by omega : m + k + 1 ≤ 2 * m) =
        W.t (m + k + 1) hm1 by
          exact W.t_irrel.symm]
    ring
  · have hv : walkV W ⟨k, hk⟩ = 0 := by
      simp [walkV, hfirstA]
    rw [hv]
    simp
    rcases hrel with hA | hB
    · exfalso
      exact hfirstA ((hrel_first_iff (W := W) hk hm1).mpr hA)
    · rw [show W.t (m + k) (by omega : m + k ≤ 2 * m) =
          W.t (m + k) (Nat.le_trans (Nat.le_succ (m + k)) hm1) by
            exact W.t_irrel,
        show W.t (m + k + 1) hm1 =
          W.t (m + k + 1) (by omega : m + k + 1 ≤ 2 * m) by
            exact W.t_irrel]
      exact hB

/-- `walkPt` of the induced choices along the first `k` tail coordinates
equals the walk point at level `m+k`. -/
lemma walkPt_prez_eq {m : ℕ} {f : ℤ → ℝ} {p : unitInterval} {x : Fin (2 * m) → ℤ} {t_top : ℤ}
    (W : BWalk f p x t_top) (s₀ : ℤ) :
    s₀ = W.t m (by omega : m ≤ 2 * m) →
    ∀ (k : ℕ) (hk : k ≤ m),
      walkPt (walkV W) s₀ (pre (tailOf x) k hk) = W.t (m + k) (by omega : m + k ≤ 2 * m) := by
  intro hs₀
  intro k
  induction k with
  | zero =>
      intro hk
      dsimp [walkPt]
      simp [hs₀]
  | succ k ih =>
      intro hk1
      have hklt : k < m := Nat.lt_of_succ_le hk1
      have ih' := ih (Nat.le_of_lt hklt)
      rw [show pre (tailOf x) (k + 1) hk1 =
          pre (tailOf x) (k + 1) (Nat.succ_le_of_lt hklt) by
            exact pre_hm_irrel (tailOf x)]
      exact walkPt_prez_succ W hklt ih'

/-- the prevalue threshold `√2H` does not exceed `T`. -/
lemma sqrt2H_le_T {p : unitInterval} {H : ℝ} (hH0 : 0 < H) (hp1 : (p : ℝ) ≤ 1 / 2) :
    Real.sqrt 2 * H ≤ (Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ))) * H := by
  have hle : Real.sqrt 2 ≤ 2 := by
    have hsq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
      rw [Real.sq_sqrt]
      norm_num
    nlinarith [sq_nonneg (Real.sqrt 2)]
  have hT' : Real.sqrt 2 ≤ Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ)) := by
    have hp : 0 ≤ 1 - (p : ℝ) := by linarith [hp1]
    have hprod : 0 ≤ (2 - Real.sqrt 2) * (1 - (p : ℝ)) := mul_nonneg (sub_nonneg.mpr hle) hp
    nlinarith
  exact mul_le_mul_of_nonneg_right hT' hH0.le

/-- per-step survival (deterministic core of the reduction): if the
level-`(m+k+1)` value at the walk point `W.t (m+k+1)` reaches `T`, then the
`k`-th tail step of the induced `(walkV, s₀)` walk survives. -/
theorem step_survive {f : ℤ → ℝ} {p : unitInterval} {H : ℝ} {m : ℕ} {x : Fin (2 * m) → ℤ}
    {t_top : ℤ} (W : BWalk f p x t_top)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) ≤ 1 / 2)
    (hfsup : ∀ t : ℤ, f t ≤ 2 * H)
    {T : ℝ} (hT : T = (Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ))) * H)
    {k : ℕ} (hk : k < m)
    (hbigT : T ≤ lvl f p (m + k + 1) (pre x (m + k + 1) (by omega : m + k + 1 ≤ 2 * m))
        (W.t (m + k + 1) (by omega : m + k + 1 ≤ 2 * m))) :
    goodStep (f := f) (p := p) (H := H) (m := m) (pre x m (by omega : m ≤ 2 * m))
      (walkV W) (W.t m (by omega : m ≤ 2 * m)) hk
      (pre (tailOf x) k (Nat.le_of_lt hk)) (tailOf x ⟨k, hk⟩) := by
  classical
  let pref : Fin m → ℤ := pre x m (by omega : m ≤ 2 * m)
  let z : Fin m → ℤ := tailOf x
  let v : Fin m → ℤ := walkV W
  let s₀ : ℤ := W.t m (by omega : m ≤ 2 * m)
  let u : Fin k → ℤ := pre z k (Nat.le_of_lt hk)
  let a : ℤ := z ⟨k, hk⟩
  have hm : m + k < 2 * m := by omega
  have hm1 : m + k + 1 ≤ 2 * m := by omega
  have hbig : (Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ))) * H ≤
      lvl f p (m + k + 1) (pre x (m + k + 1) (Nat.succ_le_of_lt hm)) (W.t (m + k + 1) hm1) := by
    have heq : pre x (m + k + 1) (by omega : m + k + 1 ≤ 2 * m) =
        pre x (m + k + 1) (Nat.succ_le_of_lt hm) := pre_hm_irrel x
    have heq2 : W.t (m + k + 1) (by omega : m + k + 1 ≤ 2 * m) = W.t (m + k + 1) hm1 := W.t_irrel
    rw [hT.symm, heq, heq2]
    exact hbigT
  have hsupk : ∀ t : ℤ, lvl f p (m + k) (pre x (m + k) (Nat.le_of_lt hm)) t ≤ 2 * H := by
    intro t
    exact lvl_le_sup (k := m + k) (u := pre x (m + k) (Nat.le_of_lt hm)) hfsup t
  have htwo := two_prevalues (f := f) (p := p) (H := H) (ℓ := 2 * m) x (m := m + k) hm
    hp0 hp1 hsupk (W.t (m + k + 1) hm1) hbig
  -- level-function bridge
  have heqL : lvl f p (m + k) (partialVec pref u) =
      lvl f p (m + k) (pre x (m + k) (Nat.le_of_lt hm)) := by
    have hb := partialVec_tail (x := x) (hk := hk)
    have hb' : partialVec pref u = pre x (m + k) (Nat.le_of_lt hm) := by
      calc
        partialVec pref u
            = partialVec (pre x m (by omega : m ≤ 2 * m)) (pre (tailOf x) k (Nat.le_of_lt hk)) := by rfl
        _ = pre x (m + k) (by omega : m + k ≤ 2 * m) := hb
        _ = pre x (m + k) (Nat.le_of_lt hm) := pre_hm_irrel x
    rw [hb']
  -- walk point consistency
  have hs₀ : s₀ = W.t m (by omega : m ≤ 2 * m) := rfl
  have hpz := walkPt_prez_eq (W := W) s₀ hs₀ (k + 1) (Nat.succ_le_of_lt hk)
  have hpre1 : pre z (k + 1) (Nat.succ_le_of_lt hk) = extendFin u a := by
    dsimp [u, a]
    exact pre_succ_extend (z := z) (k := k) hk
  have hpn : walkPt v s₀ (extendFin u a) = W.t (m + k + 1) hm1 := by
    dsimp [v, s₀]
    calc
      walkPt (walkV W) (W.t m (by omega : m ≤ 2 * m)) (extendFin u a)
          = walkPt (walkV W) (W.t m (by omega : m ≤ 2 * m)) (pre z (k + 1) (Nat.succ_le_of_lt hk)) := by
            rw [hpre1]
      _ = W.t (m + (k + 1)) (by omega : m + (k + 1) ≤ 2 * m) := hpz
      _ = W.t (m + k + 1) hm1 := by
            rw [show W.t (m + (k + 1)) (by omega : m + (k + 1) ≤ 2 * m) =
                W.t (m + k + 1) hm1 by
                  exact W.t_irrel]
  have hxcoord : z ⟨k, hk⟩ = x ⟨m + k, hm⟩ := by rfl
  have hc1 : Real.sqrt 2 * H ≤ lvl f p (m + k) (partialVec pref u)
      (walkPt v s₀ (extendFin u a)) := by
    dsimp [v, s₀]
    rw [heqL]
    rw [hpn]
    exact htwo.1
  have hc2 : Real.sqrt 2 * H ≤ lvl f p (m + k) (partialVec pref u)
      (walkPt v s₀ (extendFin u a) + a) := by
    dsimp [v, s₀, a]
    rw [heqL]
    rw [hpn]
    rw [hxcoord]
    exact htwo.2
  exact (goodStep_iff_two (f := f) (p := p) (H := H) (m := m) pref v s₀ hk u a).mpr
    ⟨hc1, hc2⟩

/-- (deterministic reduction, ingredient 4) if the level-`2m` function of the
full tuple `x` reaches `T := (√2p+2(1−p))H` in supremum, then there is a start
point `s₀` at level `m` with value `≥ √2H` and a `{0,1}`-choice `v` for which
every tail step survives. -/
theorem esup_gt_reduction {f : ℤ → ℝ} {p : unitInterval} {H : ℝ} {m : ℕ}
    (x : Fin (2 * m) → ℤ)
    (hH0 : 0 < H) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) ≤ 1 / 2)
    (hfsup : ∀ t : ℤ, f t ≤ 2 * H)
    (hfpos : ∀ t : ℤ, 0 ≤ f t) (hf : Summable f)
    (hbig : (Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ))) * H <
      Sec3Tower.esup (lvl f p (2 * m) (pre x (2 * m) (le_refl (2 * m))))) :
    ∃ s₀ : ℤ, s₀ ∈ StartSet (f := f) (p := p) (H := H) (m := m)
        (pre x m (by omega : m ≤ 2 * m)) ∧
      ∃ v : Fin m → ℤ,
        v ∈ SeqSet m ∧
        goodAll (goodStepFam (f := f) (p := p) (H := H) (m := m)
          (pre x m (by omega : m ≤ 2 * m)) v s₀) (tailOf x) := by
  classical
  let T : ℝ := (Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ))) * H
  let g : ℤ → ℝ := lvl f p (2 * m) (pre x (2 * m) (le_refl (2 * m)))
  have hne : (Set.range g).Nonempty := Set.range_nonempty g
  rcases exists_lt_of_lt_csSup (s := Set.range g) (b := T) hne hbig with ⟨a, ha, hgt⟩
  rcases ha with ⟨tt, rfl⟩
  let W : BWalk f p x tt := backward_chain f p x tt
  let s₀ : ℤ := W.t m (by omega : m ≤ 2 * m)
  have htop : T < flvl f p x (2 * m) (le_refl (2 * m)) (W.t (2 * m) (le_refl (2 * m))) := by
    have h1 : T < flvl f p x (2 * m) (le_refl (2 * m)) tt := by
      simpa [g, lvl_eq_flvl] using hgt
    simpa [W.htop] using h1
  refine ⟨s₀, ?_, walkV W, walkV_mem W, ?_⟩
  · dsimp [s₀]
    rw [mem_StartSet]
    have hge := level_ge_top (W := W) m (by omega : m ≤ 2 * m)
    have hsq := sqrt2H_le_T (p := p) (H := H) hH0 hp1
    have hv : flvl f p x m (by omega : m ≤ 2 * m) (W.t m (by omega : m ≤ 2 * m)) =
        lvl f p m (pre x m (by omega : m ≤ 2 * m)) (W.t m (by omega : m ≤ 2 * m)) := by
      simpa [lvl_eq_flvl]
    rw [← hv]
    linarith [hsq, htop, hge]
  · dsimp [goodAll]
    intro k hk
    dsimp [s₀]
    dsimp [goodStepFam]
    rw [dif_pos hk]
    apply step_survive (W := W) (k := k) hp0 hp1 hfsup rfl hk
    have hge := level_ge_top (W := W) (m + k + 1) (by omega : m + k + 1 ≤ 2 * m)
    have hbigL : T < lvl f p (m + k + 1) (pre x (m + k + 1) (by omega : m + k + 1 ≤ 2 * m))
        (W.t (m + k + 1) (by omega : m + k + 1 ≤ 2 * m)) := by
      simpa [lvl_eq_flvl] using lt_of_lt_of_le htop hge
    exact le_of_lt hbigL



/-- concatenation of a length-`m` prefix tuple and a length-`m` tail tuple into
a `Fin (2*m)` vector (coordinates `< m` from the prefix, the rest from the
tail). -/
def catTwo {m : ℕ} (pz : (Fin m → ℤ) × (Fin m → ℤ)) : Fin (2 * m) → ℤ :=
  fun q => if hq : q.val < m then pz.1 ⟨q.val, hq⟩ else pz.2 ⟨q.val - m, by omega⟩

/-- the first `m` coordinates of `catTwo pz` are `pz.1`. -/
lemma pre_catTwo_fst {m : ℕ} (pz : (Fin m → ℤ) × (Fin m → ℤ)) :
    pre (catTwo pz) m (by omega : m ≤ 2 * m) = pz.1 := by
  funext j
  dsimp [catTwo, pre]
  have hq : j.val < m := j.isLt
  rw [dif_pos hq]

/-- the last `m` coordinates of `catTwo pz` are `pz.2`. -/
lemma tailOf_catTwo {m : ℕ} (pz : (Fin m → ℤ) × (Fin m → ℤ)) :
    tailOf (catTwo pz) = pz.2 := by
  funext j
  dsimp [catTwo, tailOf]
  have hq : ¬ (m + j.val) < m := by omega
  rw [dif_neg hq]
  have harg : (⟨m + j.val - m, by omega⟩ : Fin m) = j := by
    apply Fin.ext
    dsimp
    omega
  exact congrArg pz.2 harg

/-- (phase-2 counting export, even case, counting form) the number of
`(pref, tail)`-pairs whose `2m`-level function reaches
`T := (√2 p + 2(1−p))H` in supremum is at most the product of the coordinate
cardinalities times `exp(−2Mn) + (√2H)⁻¹·2^m·(12μ)^m`. -/
theorem phase2_count_even {M ε : ℝ} (hM : 1 ≤ M) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ∃ n₀ : ℕ, ∀ (n : ℕ), n₀ ≤ n →
    ∀ (m : ℕ), m = Nat.floor (ε * (n : ℝ) / 2) →
    ∀ {p : unitInterval} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) ≤ 1 / 2),
    ∀ {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t)
      (hf2 : Summable (fun t : ℤ => (f t) ^ 2))
      (hfsum : Summable f),
    ∀ {Rt L : ℝ} (hR0 : 0 < Rt) (hL16 : 16 * Rt ≤ L),
    ∀ {N : ℕ} (hN1 : 1 ≤ N), ∀ (hn1 : 1 ≤ n),
    ∀ {μ : ℝ} (hμeq : μ = PropRefine3.mu0 M ε) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 64),
    ∀ {H Cdrop : ℝ}
      (hH : H = L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ))))
      (hCdrop : Cdrop = (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * Rt ^ 2 /
        ((N : ℝ) * (n : ℝ))),
    ∀ (hlip : Ell2Update.ratioLip (μ ^ 4) f)
      (hmass : ∀ lo : ℤ, (∑ t ∈ Submission.Ell2Greedy.I0 lo N, f t) ≤ Rt / Real.sqrt (n : ℝ)),
    ∀ (hCdrop0 : 0 ≤ Cdrop)
      (hsmall : norm₂sq f < Cdrop * ((m / 2 + 1 : ℕ) : ℝ))
      (hnorm1 : IntFun.norm₁ f ≤ 1)
      (hfsup : ∀ t : ℤ, f t ≤ 2 * H)
      (hH0 : 0 < H),
    ∀ {c d loS hiS : Fin m → ℤ}
      (hJlen : ∀ k : Fin m, (N : ℝ) ≤ ((Finset.Icc (c k) (d k)).card : ℝ))
      (hSlen : ∀ k : Fin m, (N : ℝ) ≤ ((Finset.Icc (loS k) (hiS k)).card : ℝ)),
      (((((prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))).product
            (prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j)))).filter
          (fun pz : (Fin m → ℤ) × (Fin m → ℤ) =>
            (Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ))) * H <
              Sec3Tower.esup (lvl f p (2 * m) (pre (catTwo pz) (2 * m) (le_refl (2 * m)))))).card : ℕ) : ℝ) ≤
        ((∏ j : Fin m, (((Finset.Icc (c j) (d j)).card : ℕ) : ℝ)) *
          (∏ j : Fin m, (((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ))) *
          (Real.exp (-2 * M * (n : ℝ)) +
            (1 / (Real.sqrt 2 * H)) * (2 : ℝ) ^ m * (12 * μ) ^ m) := by
  classical
  rcases prefix_noflat_pair_count (M := M) (ε := ε) hM hε0 hε1 with ⟨n₀, hnf⟩
  refine ⟨n₀, ?_⟩
  intro n hn m hm p hp0 hp1 f hfpos hf2 hfsum Rt L hR0 hL16 N hN1 hn1 μ hμeq hμ0 hμ1 H Cdrop hH hCdrop
    hlip hmass hCdrop0 hsmall hnorm1 hfsup hH0 c d loS hiS hJlen hSlen

  let Ac : ℝ := ∏ j : Fin m, (((Finset.Icc (c j) (d j)).card : ℕ) : ℝ)
  let Bc : ℝ := ∏ j : Fin m, (((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ)
  let A : Finset (Fin m → ℤ) := prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))
  let B : Finset (Fin m → ℤ) := prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j))
  let P : Finset ((Fin m → ℤ) × (Fin m → ℤ)) := A.product B
  let flatPref (pref : Fin m → ℤ) : Prop :=
    ∃ (j : ℕ) (hj : j ≤ m), flatLvl f p H μ N j (pre pref j hj)
  let surv (pref : Fin m → ℤ) (z : Fin m → ℤ) : Prop :=
    ∃ s₀ : ℤ, s₀ ∈ StartSet (f := f) (p := p) (H := H) (m := m) pref ∧
      ∃ v : Fin m → ℤ, v ∈ SeqSet m ∧
        goodAll (goodStepFam (f := f) (p := p) (H := H) (m := m) pref v s₀) z
  let E (pz : (Fin m → ℤ) × (Fin m → ℤ)) : Prop :=
    (Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ))) * H <
      Sec3Tower.esup (lvl f p (2 * m) (pre (catTwo pz) (2 * m) (le_refl (2 * m))))
  let Eset : Finset ((Fin m → ℤ) × (Fin m → ℤ)) := P.filter E
  let noflat : Finset ((Fin m → ℤ) × (Fin m → ℤ)) := P.filter (fun pz => ¬ flatPref pz.1)
  let survset : Finset ((Fin m → ℤ) × (Fin m → ℤ)) :=
    P.filter (fun pz => flatPref pz.1 ∧ surv pz.1 pz.2)
  -- deterministic containment: E ⟹ ¬flat ∨ (flat ∧ surv)
  have hcont : ∀ pz : (Fin m → ℤ) × (Fin m → ℤ), E pz →
      (¬ flatPref pz.1 ∨ (flatPref pz.1 ∧ surv pz.1 pz.2)) := by
    intro pz hE
    by_cases hflat : flatPref pz.1
    · right
      refine ⟨hflat, ?_⟩
      have hred := esup_gt_reduction (f := f) (p := p) (H := H) (m := m) (x := catTwo pz)
        hH0 hp0 hp1 hfsup hfpos hfsum hE
      rcases hred with ⟨s₀, hs0, v, hv, hg⟩
      have hpre := pre_catTwo_fst pz
      have htail := tailOf_catTwo pz
      refine ⟨s₀, ?_, v, hv, ?_⟩
      · rwa [hpre] at hs0
      · rwa [hpre, htail] at hg
    · left
      exact hflat
  have hsub : Eset ⊆ noflat ∪ survset := by
    intro pz hpz
    rw [Finset.mem_filter] at hpz
    rw [Finset.mem_union]
    rcases hcont pz hpz.2 with hnf | hflat
    · left
      rw [Finset.mem_filter]
      exact ⟨hpz.1, hnf⟩
    · right
      rw [Finset.mem_filter]
      exact ⟨hpz.1, hflat⟩
  have hcard : ((Eset.card : ℕ) : ℝ) ≤
      ((noflat.card : ℕ) : ℝ) + ((survset.card : ℕ) : ℝ) := by
    calc
      ((Eset.card : ℕ) : ℝ) ≤ (((noflat ∪ survset).card : ℕ) : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub)
      _ ≤ (((noflat.card + survset.card : ℕ) : ℝ)) := by
        exact_mod_cast (Finset.card_union_le noflat survset)
      _ = ((noflat.card : ℕ) : ℝ) + ((survset.card : ℕ) : ℝ) := by simp
  -- no-flat-prefix pairs
  have hno := hnf n hn (m := m) hm (p := p) hp0 hp1 (f := f) hfpos hf2 (Rt := Rt) (L := L)
    hR0 hL16 (N := N) hN1 hn1 (μ := μ) hμeq hμ0 hμ1 (H := H) (Cdrop := Cdrop) hH hCdrop
    hlip hmass hCdrop0 hsmall (c := c) (d := d) hJlen (loS := loS) (hiS := hiS)
  have hno' : ((noflat.card : ℕ) : ℝ) ≤ Real.exp (-2 * M * (n : ℝ)) * Ac * Bc := by
    dsimp [noflat, flatPref, Ac, Bc]
    exact hno
  -- flat-prefix survive pairs
  have hsurv := flat_survive_pair_count (f := f) (p := p) (H := H) (μ := μ) (N := N) (m := m)
    (J := fun j : Fin m => Finset.Icc (c j) (d j)) (loS := loS) (hiS := hiS)
    hH0 hN1 hμ0.le hfsup hfpos hfsum hnorm1 hSlen
  have hfib := Commons.Data.Finset.fiber_filter_product_card_real (s := A) (t := B)
    (P := flatPref) (Q := surv)
  have hfib' : ((survset.card : ℕ) : ℝ) =
      (∑ pref ∈ A.filter flatPref,
        (((B.filter (fun z : Fin m → ℤ => surv pref z)).card : ℕ) : ℝ)) := by
    dsimp [survset, P]
    exact hfib
  have hcq : ((prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))).card : ℝ) = Ac := by
    dsimp [Ac]
    exact_mod_cast (ProdCount.prodFinset_card (fun j : Fin m => Finset.Icc (c j) (d j)))
  have hsurv' : ((survset.card : ℕ) : ℝ) ≤
      Ac * (1 / (Real.sqrt 2 * H)) * (2 : ℝ) ^ m * (12 * μ) ^ m * Bc := by
    rw [hfib']
    have hmain : (∑ pref ∈ A.filter flatPref,
        (((B.filter (fun z : Fin m → ℤ => surv pref z)).card : ℕ) : ℝ)) ≤
        ((prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))).card : ℝ) *
          (1 / (Real.sqrt 2 * H)) * (2 : ℝ) ^ m * (12 * μ) ^ m * Bc := by
      dsimp [A, B, flatPref, surv, Ac, Bc]
      exact hsurv
    rwa [hcq] at hmain
  have hsum : ((noflat.card : ℕ) : ℝ) + ((survset.card : ℕ) : ℝ) ≤
      Ac * Bc * (Real.exp (-2 * M * (n : ℝ)) +
        (1 / (Real.sqrt 2 * H)) * (2 : ℝ) ^ m * (12 * μ) ^ m) := by
    have h1 := hno'
    have h2 := hsurv'
    nlinarith
  have hfinal : ((Eset.card : ℕ) : ℝ) ≤
      Ac * Bc * (Real.exp (-2 * M * (n : ℝ)) +
        (1 / (Real.sqrt 2 * H)) * (2 : ℝ) ^ m * (12 * μ) ^ m) :=
    le_trans hcard hsum
  simpa [Ac, Bc, Eset, P, E, A, B] using hfinal

/-- (phase-2 export, even case) same counting conclusion with the asymptotic
`≤ exp(−Mn)·∏|coords|` bound (absorbing the layer-0 terms for large `n`). -/
theorem phase2_export_even {M ε : ℝ} (hM : 1 ≤ M) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ∃ n₀ : ℕ, ∀ (n : ℕ), n₀ ≤ n →
    ∀ (m : ℕ), m = Nat.floor (ε * (n : ℝ) / 2) →
    ∀ {p : unitInterval} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) ≤ 1 / 2),
    ∀ {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t)
      (hf2 : Summable (fun t : ℤ => (f t) ^ 2))
      (hfsum : Summable f),
    ∀ {Rt L : ℝ} (hR0 : 0 < Rt) (hL16 : 16 * Rt ≤ L) (hL1 : 1 ≤ L),
    ∀ {N : ℕ} (hN1 : 1 ≤ N), ∀ (hn1 : 1 ≤ n),
    ∀ {μ : ℝ} (hμeq : μ = PropRefine3.mu0 M ε) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 64),
    ∀ {H Cdrop : ℝ}
      (hH : H = L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ))))
      (hCdrop : Cdrop = (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * Rt ^ 2 /
        ((N : ℝ) * (n : ℝ))),
    ∀ (hlip : Ell2Update.ratioLip (μ ^ 4) f)
      (hmass : ∀ lo : ℤ, (∑ t ∈ Submission.Ell2Greedy.I0 lo N, f t) ≤ Rt / Real.sqrt (n : ℝ)),
    ∀ (hCdrop0 : 0 ≤ Cdrop)
      (hsmall : norm₂sq f < Cdrop * ((m / 2 + 1 : ℕ) : ℝ))
      (hnorm1 : IntFun.norm₁ f ≤ 1)
      (hfsup : ∀ t : ℤ, f t ≤ 2 * H)
      (hH0 : 0 < H),
    ∀ {c d loS hiS : Fin m → ℤ}
      (hJlen : ∀ k : Fin m, (N : ℝ) ≤ ((Finset.Icc (c k) (d k)).card : ℝ))
      (hSlen : ∀ k : Fin m, (N : ℝ) ≤ ((Finset.Icc (loS k) (hiS k)).card : ℝ)),
    (N : ℝ) ≤ (2 : ℝ) ^ n →
      (((((prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))).product
            (prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j)))).filter
          (fun pz : (Fin m → ℤ) × (Fin m → ℤ) =>
            (Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ))) * H <
              Sec3Tower.esup (lvl f p (2 * m) (pre (catTwo pz) (2 * m) (le_refl (2 * m)))))).card : ℕ) : ℝ) ≤
        Real.exp (-M * (n : ℝ)) *
          (∏ j : Fin m, (((Finset.Icc (c j) (d j)).card : ℕ) : ℝ)) *
          (∏ j : Fin m, (((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ)) := by
  classical
  rcases phase2_count_even (M := M) (ε := ε) hM hε0 hε1 with ⟨n₁, hc⟩
  rcases Commons.Analysis.Real.phase2_tail_N (M := M) (ε := ε) hM hε0 hε1 with ⟨n₂, hl⟩
  refine ⟨max (max n₁ n₂) (Nat.ceil (4 / ε)), ?_⟩
  intro n hn m hm p hp0 hp1 f hfpos hf2 hfsum Rt L hR0 hL16 hL1 N hN1 hn1 μ hμeq hμ0 hμ1
    H Cdrop hH hCdrop hlip hmass hCdrop0 hsmall hnorm1 hfsup hH0 c d loS hiS hJlen hSlen hNpow
  let PJ : ℝ := ∏ j : Fin m, (((Finset.Icc (c j) (d j)).card : ℕ) : ℝ)
  let PS : ℝ := ∏ j : Fin m, (((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ)
  have hn₁ : n₁ ≤ n := by
    exact le_trans (le_max_left n₁ n₂) (le_trans (le_max_left _ _) hn)
  have hn₂ : n₂ ≤ n := by
    exact le_trans (le_max_right n₁ n₂) (le_trans (le_max_left _ _) hn)
  have hcnt := hc n hn₁ (m := m) hm (p := p) hp0 hp1 (f := f) hfpos hf2 hfsum (Rt := Rt) (L := L)
    hR0 hL16 (N := N) hN1 hn1 (μ := μ) hμeq hμ0 hμ1 (H := H) (Cdrop := Cdrop) hH hCdrop
    hlip hmass hCdrop0 hsmall hnorm1 hfsup hH0 (c := c) (d := d) hJlen (loS := loS)
    (hiS := hiS) hSlen
  have hcnt' : (((((prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))).product
            (prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j)))).filter
          (fun pz : (Fin m → ℤ) × (Fin m → ℤ) =>
            (Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ))) * H <
              Sec3Tower.esup (lvl f p (2 * m) (pre (catTwo pz) (2 * m) (le_refl (2 * m)))))).card : ℕ) : ℝ) ≤
      PJ * PS * (Real.exp (-2 * M * (n : ℝ)) +
        (1 / (Real.sqrt 2 * H)) * (2 : ℝ) ^ m * (12 * μ) ^ m) := by
    simpa [PJ, PS] using hcnt
  have hmbig : (ε * (n : ℝ) / 4) ≤ (m : ℝ) := by
    have hεn : (4 : ℝ) ≤ ε * (n : ℝ) := by
      have h1 : (4 : ℝ) ≤ ε * (Nat.ceil (4 / ε) : ℝ) := by
        have hεnz : ε ≠ 0 := ne_of_gt hε0
        calc
          (4 : ℝ) = ε * (4 / ε) := by field_simp [hεnz]
          _ ≤ ε * (Nat.ceil (4 / ε) : ℝ) := by
            exact mul_le_mul_of_nonneg_left (Nat.le_ceil (4 / ε)) hε0.le
      have hnn : ((Nat.ceil (4 / ε) : ℕ) : ℝ) ≤ (n : ℝ) := by
        have hnat : Nat.ceil (4 / ε) ≤ n := le_trans (le_max_right (max n₁ n₂) _) hn
        exact_mod_cast hnat
      exact le_trans h1 (mul_le_mul_of_nonneg_left hnn hε0.le)
    have hff := (Nat.floor_eq_iff (a := ε * (n : ℝ) / 2) (n := m)
      (ha := (show 0 ≤ ε * (n : ℝ) / 2 by positivity))).mp hm.symm
    have hfl2 : ε * (n : ℝ) / 2 - 1 < (m : ℝ) := by
      have h2 : ε * (n : ℝ) / 2 < (m : ℝ) + 1 := hff.2
      linarith
    have hq : ε * (n : ℝ) / 4 ≤ ε * (n : ℝ) / 2 - 1 := by
      nlinarith
    exact le_of_lt (lt_of_le_of_lt hq hfl2)
  have hla2 : Real.exp (-2 * M * (n : ℝ)) +
      (Real.sqrt 2 * (N : ℝ) * Real.sqrt (n : ℝ)) * (2 : ℝ) ^ m * (12 * μ) ^ m ≤
      Real.exp (-M * (n : ℝ)) := by
    have hlay := hl n hn₂ (m := m) hmbig (N := N) hN1 hNpow
    rw [hμeq]
    dsimp [PropRefine3.mu0]
    have hC : (12 * (Real.exp (-16 * M / ε) / (24 * 1024 ^ 2))) =
        (12 * Real.exp (-16 * M / ε) / (24 * 1024 ^ 2)) := by ring
    rw [hC]
    exact hlay
  have hHv : 1 / (Real.sqrt 2 * H) ≤ Real.sqrt 2 * (N : ℝ) * Real.sqrt (n : ℝ) := by
    have hpos2 : 0 < Real.sqrt 2 * (L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ)))) := by
      positivity
    rw [hH]
    rw [div_le_iff₀ hpos2]
    have hNnz : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hN1))
    have hnnz : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hn1))
    have hsqrt2 : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
    have hsqrtn : Real.sqrt (n : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn1)))
    have heq : (Real.sqrt 2 * (L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ))))) *
        (Real.sqrt 2 * (N : ℝ) * Real.sqrt (n : ℝ)) = L := by
      field_simp [hNnz, hnnz, hsqrt2, hsqrtn, Real.sq_sqrt]
      norm_num
    calc
      1 ≤ L := hL1
      _ = (Real.sqrt 2 * (N : ℝ) * Real.sqrt (n : ℝ)) *
          (Real.sqrt 2 * (L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ))))) := by
            rw [mul_comm]
            exact heq.symm
  have hterm : Real.exp (-2 * M * (n : ℝ)) +
      (1 / (Real.sqrt 2 * H)) * (2 : ℝ) ^ m * (12 * μ) ^ m ≤ Real.exp (-M * (n : ℝ)) := by
    have hp2 : 0 ≤ (2 : ℝ) ^ m * (12 * μ) ^ m := by positivity
    have hpart : (1 / (Real.sqrt 2 * H)) * (2 : ℝ) ^ m * (12 * μ) ^ m ≤
        (Real.sqrt 2 * (N : ℝ) * Real.sqrt (n : ℝ)) * (2 : ℝ) ^ m * (12 * μ) ^ m := by
      calc
        (1 / (Real.sqrt 2 * H)) * (2 : ℝ) ^ m * (12 * μ) ^ m
            = (1 / (Real.sqrt 2 * H)) * ((2 : ℝ) ^ m * (12 * μ) ^ m) := by ring
        _ ≤ (Real.sqrt 2 * (N : ℝ) * Real.sqrt (n : ℝ)) * ((2 : ℝ) ^ m * (12 * μ) ^ m) := by
              exact mul_le_mul_of_nonneg_right hHv hp2
        _ = (Real.sqrt 2 * (N : ℝ) * Real.sqrt (n : ℝ)) * (2 : ℝ) ^ m * (12 * μ) ^ m := by ring
    nlinarith [hla2, hpart]
  have hPJ : 0 ≤ PJ := by
    dsimp [PJ]
    exact Finset.prod_nonneg (fun j hj => by exact_mod_cast (Nat.zero_le _))
  have hPS : 0 ≤ PS := by
    dsimp [PS]
    exact Finset.prod_nonneg (fun j hj => by exact_mod_cast (Nat.zero_le _))
  have hmid : PJ * PS * (Real.exp (-2 * M * (n : ℝ)) +
      (1 / (Real.sqrt 2 * H)) * (2 : ℝ) ^ m * (12 * μ) ^ m) ≤
      Real.exp (-M * (n : ℝ)) * PJ * PS := by
    calc
      PJ * PS * (Real.exp (-2 * M * (n : ℝ)) +
          (1 / (Real.sqrt 2 * H)) * (2 : ℝ) ^ m * (12 * μ) ^ m)
          ≤ PJ * PS * Real.exp (-M * (n : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hterm (mul_nonneg hPJ hPS)
      _ = Real.exp (-M * (n : ℝ)) * PJ * PS := by ring
  exact le_trans hcnt' hmid


-- the (2m+1)-vector whose first 2m coordinates are w and top coordinate is a
def oddVec {m : ℕ} (w : Fin (2 * m) → ℤ) (a : ℤ) : Fin (2 * m + 1) → ℤ :=
  fun q => if hq : q.val < 2 * m then w ⟨q.val, hq⟩ else a

-- pre of the odd vector at 2m = w
lemma pre_oddVec {m : ℕ} (w : Fin (2 * m) → ℤ) (a : ℤ) :
    pre (oddVec w a) (2 * m) (by omega : 2 * m ≤ 2 * m + 1) = w := by
  funext j
  dsimp [pre, oddVec]
  have hlt : (j : ℕ) < 2 * m := j.isLt
  simp [hlt]

-- esup at level 2m+1 ≤ esup at level 2m (of the 2m-prefix)
lemma esup_odd_le_even {f : ℤ → ℝ} {p : unitInterval} {m : ℕ}
    (hfpos : ∀ t : ℤ, 0 ≤ f t) (hf : Summable f)
    (w : Fin (2 * m) → ℤ) (a : ℤ) :
    Submission.Sec3Tower.esup (lvl f p (2 * m + 1) (pre (oddVec w a) (2 * m + 1) (le_refl (2 * m + 1)))) ≤
    Submission.Sec3Tower.esup (lvl f p (2 * m) (pre w (2 * m) (le_refl (2 * m)))) := by
  have hpar := Submission.PropRefineExport.esup_parity (f := f) (p := p) (m := m)
    (x := oddVec w a) hfpos hf
  have hpre := pre_oddVec w a
  rw [pre_self] at hpar
  rwa [hpre] at hpar

-- ============ draft phase2_export_odd ============

theorem phase2_export_odd {M ε : ℝ} (hM : 1 ≤ M) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ∃ n₀ : ℕ, ∀ (n : ℕ), n₀ ≤ n →
    ∀ (m : ℕ), m = Nat.floor (ε * (n : ℝ) / 2) →
    ∀ {p : unitInterval} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) ≤ 1 / 2),
    ∀ {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t)
      (hf2 : Summable (fun t : ℤ => (f t) ^ 2))
      (hfsum : Summable f),
    ∀ {Rt L : ℝ} (hR0 : 0 < Rt) (hL16 : 16 * Rt ≤ L) (hL1 : 1 ≤ L),
    ∀ {N : ℕ} (hN1 : 1 ≤ N), ∀ (hn1 : 1 ≤ n),
    ∀ {μ : ℝ} (hμeq : μ = PropRefine3.mu0 M ε) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 64),
    ∀ {H Cdrop : ℝ}
      (hH : H = L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ))))
      (hCdrop : Cdrop = (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * Rt ^ 2 /
        ((N : ℝ) * (n : ℝ))),
    ∀ (hlip : Ell2Update.ratioLip (μ ^ 4) f)
      (hmass : ∀ lo : ℤ, (∑ t ∈ Submission.Ell2Greedy.I0 lo N, f t) ≤ Rt / Real.sqrt (n : ℝ)),
    ∀ (hCdrop0 : 0 ≤ Cdrop)
      (hsmall : norm₂sq f < Cdrop * ((m / 2 + 1 : ℕ) : ℝ))
      (hnorm1 : IntFun.norm₁ f ≤ 1)
      (hfsup : ∀ t : ℤ, f t ≤ 2 * H)
      (hH0 : 0 < H),
    ∀ {c d loS hiS : Fin m → ℤ}
      (hJlen : ∀ k : Fin m, (N : ℝ) ≤ ((Finset.Icc (c k) (d k)).card : ℝ))
      (hSlen : ∀ k : Fin m, (N : ℝ) ≤ ((Finset.Icc (loS k) (hiS k)).card : ℝ)),
    (N : ℝ) ≤ (2 : ℝ) ^ n →
    ∀ (cl dl : ℤ),
      ((((((prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))).product
            (prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j)))).product
            (Finset.Icc cl dl)).filter
          (fun pza : ((Fin m → ℤ) × (Fin m → ℤ)) × ℤ =>
            (Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ))) * H <
              Submission.Sec3Tower.esup (lvl f p (2 * m + 1)
                (pre (oddVec (catTwo pza.1) pza.2) (2 * m + 1) (le_refl (2 * m + 1)))))).card : ℕ) : ℝ) ≤
        Real.exp (-M * (n : ℝ)) *
          (∏ j : Fin m, (((Finset.Icc (c j) (d j)).card : ℕ) : ℝ)) *
          (∏ j : Fin m, (((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ)) *
          (((Finset.Icc cl dl).card : ℕ) : ℝ) := by
  classical
  rcases phase2_export_even (M := M) (ε := ε) hM hε0 hε1 with ⟨n₀, hE⟩
  refine ⟨n₀, ?_⟩
  intro n hn m hm p hp0 hp1 f hfpos hf2 hfsum Rt L hR0 hL16 hL1 N hN1 hn1 μ hμeq hμ0 hμ1
    H Cdrop hH hCdrop hlip hmass hCdrop0 hsmall hnorm1 hfsup hH0 c d loS hiS hJlen hSlen hNpow cl dl
  let Ac : ℝ := ∏ j : Fin m, (((Finset.Icc (c j) (d j)).card : ℕ) : ℝ)
  let Bc : ℝ := ∏ j : Fin m, (((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ)
  let Cc : ℝ := (((Finset.Icc cl dl).card : ℕ) : ℝ)
  let A : Finset (Fin m → ℤ) := prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))
  let B : Finset (Fin m → ℤ) := prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j))
  let F2 : Finset ((Fin m → ℤ) × (Fin m → ℤ)) := A.product B
  let FI : Finset ℤ := Finset.Icc cl dl
  let evPred (pz : (Fin m → ℤ) × (Fin m → ℤ)) : Prop :=
    (Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ))) * H <
      Submission.Sec3Tower.esup (lvl f p (2 * m) (pre (catTwo pz) (2 * m) (le_refl (2 * m))))
  let odPred (pza : ((Fin m → ℤ) × (Fin m → ℤ)) × ℤ) : Prop :=
    (Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ))) * H <
      Submission.Sec3Tower.esup (lvl f p (2 * m + 1)
        (pre (oddVec (catTwo pza.1) pza.2) (2 * m + 1) (le_refl (2 * m + 1))))
  let E3 : Finset (((Fin m → ℤ) × (Fin m → ℤ)) × ℤ) := (F2.product FI).filter odPred
  let E2 : Finset ((Fin m → ℤ) × (Fin m → ℤ)) := F2.filter evPred
  have hodd_ev : ∀ (pz : (Fin m → ℤ) × (Fin m → ℤ)) (a : ℤ), odPred (pz, a) → evPred pz := by
    intro pz a hod
    dsimp [odPred, evPred] at hod ⊢
    have hpar := esup_odd_le_even (f := f) (p := p) hfpos hfsum (w := catTwo pz) (a := a)
    exact lt_of_lt_of_le hod hpar
  have hsub : E3 ⊆ E2.product FI := by
    intro q hq
    rw [Finset.mem_filter] at hq
    have hq12 : q.1 ∈ F2 ∧ q.2 ∈ FI := Finset.mem_product.mp hq.1
    have hqprod : q.1 ∈ E2 ∧ q.2 ∈ FI := by
      constructor
      · rw [Finset.mem_filter]
        constructor
        · exact hq12.1
        · exact hodd_ev q.1 q.2 hq.2
      · exact hq12.2
    exact Finset.mem_product.mpr hqprod
  have hcard : ((E3.card : ℕ) : ℝ) ≤ ((E2.card : ℕ) : ℝ) * Cc := by
    have hc3 : E3.card ≤ (E2.product FI).card := Finset.card_le_card hsub
    have hc4 : (E2.product FI).card = E2.card * FI.card := by
      simpa using (Finset.card_product (s := E2) (t := FI))
    calc
      ((E3.card : ℕ) : ℝ) ≤ (((E2.product FI).card : ℕ) : ℝ) := by exact_mod_cast hc3
      _ = (((E2.card * FI.card : ℕ) : ℝ)) := by rw [hc4]
      _ = ((E2.card : ℕ) : ℝ) * (((FI.card : ℕ) : ℝ)) := by rw [Nat.cast_mul]
      _ = ((E2.card : ℕ) : ℝ) * Cc := by simp [FI, Cc]
  have hE2 := hE n hn (m := m) hm (p := p) hp0 hp1 (f := f) hfpos hf2 hfsum (Rt := Rt) (L := L)
    hR0 hL16 hL1 (N := N) hN1 hn1 (μ := μ) hμeq hμ0 hμ1 (H := H) (Cdrop := Cdrop) hH hCdrop
    hlip hmass hCdrop0 hsmall hnorm1 hfsup hH0 (c := c) (d := d) hJlen (loS := loS)
    (hiS := hiS) hSlen hNpow
  have hE2' : ((E2.card : ℕ) : ℝ) ≤ Real.exp (-M * (n : ℝ)) * Ac * Bc := by
    simpa [E2, evPred, A, B, F2, Ac, Bc] using hE2
  have hC0 : 0 ≤ Cc := by
    dsimp [Cc]
    exact_mod_cast (Nat.zero_le _)
  have hfinal' : ((E3.card : ℕ) : ℝ) ≤ Real.exp (-M * (n : ℝ)) * Ac * Bc * Cc := by
    calc
      ((E3.card : ℕ) : ℝ) ≤ ((E2.card : ℕ) : ℝ) * Cc := hcard
      _ ≤ (Real.exp (-M * (n : ℝ)) * Ac * Bc) * Cc := by
        exact mul_le_mul_of_nonneg_right hE2' hC0
  simpa [Ac, Bc, Cc, A, B, F2, FI, E3, E2, evPred, odPred] using hfinal'

