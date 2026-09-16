import Submission.ZagierHoffmanProof.StepK16
import Submission.ZagierHoffmanProof.StepK2
import Submission.ZagierHoffmanProof.StepB8
import Submission.ZagierHoffmanProof.StepB5
import Submission.ZagierHoffmanProof.StepL2
import Submission.ZagierHoffmanProof.StepE

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L3: CW(R1) in pure-output form (paper Lemma 2.9, expansion half)

Lemma 2.9 of the paper states that for a tuple `W = (w1, …, wm)` (depth `m ≥ 1`) the
product identity `CW(R1) = S_<d+1(W)·R1(d) = 0` can be written with *pure* power sums:
```
S_d(q+w1, W⁻)  + Σ_i a_i·S_d(s_i)  +  Σ_j b_j·S_{d+1}(1, t_j)  = 0
```
with `s_i ≤ (q)+W`, `(s_i)₁ < q+w1`, `t_j ≤ (q−1)+W`.  This file proves the
**expansion half** — the concrete level-`d` identity in which every product has been
expanded to pure `S`-values:

- `p1_a_side` (m ≥ 2) / `p1_a_side_m1` (m = 1): `S_d(q)·S_<d+1(W) = S_d(q+w1,W⁻) +
  S_d(q,w1,…,wm) + (Δ-outputs)` — the `(q,w1,…,wm)` term comes from `S_prepend`, the
  `S_d(q+w1,W⁻)` term is the merge output of `S_mul_P_first` (m ≥ 2; `thakur_prod_one`
  for m = 1), and each Δ-term is expanded to pure outputs via the Part-2 data
  (`p2Wp`, `S_prepend`).
- `d1_b_side`: `D1·S_{d+1}(1)·(S_<d+1(q−1)·S_<d+1(W)) = Σ_j D1·g_j·S_{d+1}(1, t_j)`
  via the Part-2 data `p2Wb` and `S_prepend` at level `d+1`.
- `cw_r1_pure_ge2` (m ≥ 2, d ≥ 1) / `cw_r1_pure_m1` (m = 1, d ≥ 1): the assembled
  `CW(R1) = 0` in pure-output form.
- `cw_r1_pure_ge2_all` (m ≥ 2) / `cw_r1_pure_m1_all` (m = 1): the same identity at
  **every** level `d ≥ 0` (the `d = 0` case uses the level-zero vanishing of all
  depth-≥-2 blocks and the telescoping `b`-side `S_<1(q−1)·S_<1(W)`).

Remaining (next milestones, see PLAN.md): the shape bounds (`LePad`/first-entry
`< q+w1`) for every output, and the Lemma-2.9 ∃-statement (index families + bounds)
that §2.3/§3 consumes.
-/

namespace ZagierHoffmanPositiveChar

attribute [instance] P2Data.fin

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Part-2 data witness for the level-`d` product `S_<d(i)·S_<d(W⁻)` (a = singleton
`i`, b = tail of `W`), used to expand the Δ-outputs of the depth-1 × depth-`m` merge
(only meaningful for `m ≥ 2`). -/
noncomputable def p2Wp (v : ℕ+) {m : ℕ} (_hm2 : 1 < m) (_hm : 0 < m) (W : Fin m → ℕ+) :
    P2Data F 1 (m - 1) (by omega : 0 < 1) (by omega : 0 < m - 1) (single v) (expTail W) := by
  classical
  have hfull := p1p2_full_all F (m - 1) (by omega : 0 < m - 1) 1 (by omega : 0 < 1)
  exact Classical.choice ((hfull.2) (by omega : 0 < 1) (by omega : 0 < m - 1) (single v) (expTail W))

/-- Part-2 data witness for the level-`d+1` product `S_<d+1(q−1)·S_<d+1(W)` (a =
singleton `q−1`, b = `W`), used for the `D1`-side of `CW(R1)`. -/
noncomputable def p2Wb {m : ℕ} (hm : 0 < m) (W : Fin m → ℕ+) :
    P2Data F 1 m (by omega : 0 < 1) hm (single (qMinusExp F)) W := by
  classical
  have hfull := p1p2_full_all F m hm 1 (by omega : 0 < 1)
  exact Classical.choice ((hfull.2) (by omega : 0 < 1) hm (single (qMinusExp F)) W)

/-- Level split: `S_d(q)·S_<d+1(W) = S_d(q,W) + S_d(q)·S_d(W)` (recursion
`S_<d+1 = S_<d + S_d` and `S_prepend` for the `< d` part). -/
lemma cw_first_split {m : ℕ} (hm : 0 < m) (W : Fin m → ℕ+) (d : ℕ) :
    P F d (qExp F) * S_lt F m hm W (d + 1) =
      S F (m + 1) (by omega : 0 < m + 1) (consVec (qExp F) W) d +
        P F d (qExp F) * S F m hm W d := by
  rw [S_lt_succ F m hm W d]
  rw [mul_add]
  rw [S_prepend F d (qExp F) hm W]

/-- The merge output at depth 1: `headAdd v (0 < 1) (single w1) = single (v+w1)`. -/
lemma headAdd_single (v w1 : ℕ+) :
    headAdd v (by omega : 0 < 1) (single w1) =
      single ⟨(v : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos v) (w1 : ℕ)⟩ := by
  funext j
  fin_cases j
  dsimp [headAdd, single]

/-- `m ≥ 2` merge: `S_d(q)·S_d(W) = S_d(q+w1,W⁻) + Σ_i Δ^i·P_d(q+w1−i)·S_<d(i)·S_<d(W⁻)`
(paper (2.2) for a depth-1 × depth-`m` product; from `S_mul_P_first`). -/
lemma pdq_mul_SdW_ge2 {m : ℕ} (hm2 : 1 < m) (hm : 0 < m) (W : Fin m → ℕ+)
    (d : ℕ) (hd : 1 ≤ d) :
    P F d (qExp F) * S F m hm W d =
      S F m hm (headAdd (qExp F) hm W) d +
      ∑ i : dIdx (qExp F) (W ⟨0, hm⟩),
        (ChenDeltaZ F (qExp F : ℕ) (W ⟨0, hm⟩ : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
        (P F d (dHead (qExp F) (W ⟨0, hm⟩) i) *
          S_lt F 1 (by omega : 0 < 1) (single (dPn (qExp F) (W ⟨0, hm⟩) i)) d *
          S_lt F (m - 1) (by omega : 0 < m - 1) (expTail W) d) := by
  classical
  calc
    P F d (qExp F) * S F m hm W d
        = S F m hm (headAdd (qExp F) hm W) d +
          ∑ i : dIdx (qExp F) (W ⟨0, hm⟩),
            (ChenDeltaZ F (qExp F : ℕ) (W ⟨0, hm⟩ : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
            (P F d (dHead (qExp F) (W ⟨0, hm⟩) i) *
              S_lt F 1 (by omega : 0 < 1) (fun _ : Fin 1 => ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩) d *
              S_lt F (m - 1) (by omega : 0 < m - 1) (fun j : Fin (m - 1) => W ⟨j.1 + 1, by omega⟩) d) := by
          simpa [dIdx, dPn, dHead, single] using
            (S_mul_P_first F d hd (k := m) (hk := hm2) hm (qExp F) W)
    _ = S F m hm (headAdd (qExp F) hm W) d +
          ∑ i : dIdx (qExp F) (W ⟨0, hm⟩),
            (ChenDeltaZ F (qExp F : ℕ) (W ⟨0, hm⟩ : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
            (P F d (dHead (qExp F) (W ⟨0, hm⟩) i) *
              S_lt F 1 (by omega : 0 < 1) (single (dPn (qExp F) (W ⟨0, hm⟩) i)) d *
              S_lt F (m - 1) (by omega : 0 < m - 1) (expTail W) d) := by
          apply congrArg (fun t : RatFunc.CompletionAtInfty F =>
            S F m hm (headAdd (qExp F) hm W) d + t)
          apply Finset.sum_congr rfl
          intro i hi
          dsimp [single, dPn, expTail]
          rfl

/-- Per-`i` pure expansion of a Δ-term (`m ≥ 2`): `Δ^i·P_d(q+w1−i)·(S_<d(i)·S_<d(W⁻))`
becomes the `S_d`-outputs `Σ_e Δ^i·g_e·S_d((q+w1−i) :: c_e)` of the Part-2 expansion of
`S_<d(i)·S_<d(W⁻)`. -/
lemma delta_term_pure {m : ℕ} (hm2 : 1 < m) (hm : 0 < m) (W : Fin m → ℕ+) (d : ℕ)
    (i : dIdx (qExp F) (W ⟨0, hm⟩)) :
    (ChenDeltaZ F (qExp F : ℕ) (W ⟨0, hm⟩ : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
        (P F d (dHead (qExp F) (W ⟨0, hm⟩) i) *
          S_lt F 1 (by omega : 0 < 1) (single (dPn (qExp F) (W ⟨0, hm⟩) i)) d *
          S_lt F (m - 1) (by omega : 0 < m - 1) (expTail W) d) =
      ∑ e : (p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).ι,
        ((ChenDeltaZ F (qExp F : ℕ) (W ⟨0, hm⟩ : ℕ) i.1 * (p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).f e : ℤ) :
          RatFunc.CompletionAtInfty F) *
        S F ((p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).dep e + 1)
          (by omega : 0 < (p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).dep e + 1)
          (consVec (dHead (qExp F) (W ⟨0, hm⟩) i)
            ((p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).c e)) d := by
  classical
  let D := p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W
  let Δ : RatFunc.CompletionAtInfty F :=
    (ChenDeltaZ F (qExp F : ℕ) (W ⟨0, hm⟩ : ℕ) i.1 : RatFunc.CompletionAtInfty F)
  change Δ * (P F d (dHead (qExp F) (W ⟨0, hm⟩) i) *
          S_lt F 1 (by omega : 0 < 1) (single (dPn (qExp F) (W ⟨0, hm⟩) i)) d *
          S_lt F (m - 1) (by omega : 0 < m - 1) (expTail W) d) =
      ∑ e : D.ι, ((ChenDeltaZ F (qExp F : ℕ) (W ⟨0, hm⟩ : ℕ) i.1 * D.f e : ℤ) :
          RatFunc.CompletionAtInfty F) *
        S F (D.dep e + 1) (by omega : 0 < D.dep e + 1)
          (consVec (dHead (qExp F) (W ⟨0, hm⟩) i) (D.c e)) d
  calc
    Δ * (P F d (dHead (qExp F) (W ⟨0, hm⟩) i) *
          S_lt F 1 (by omega : 0 < 1) (single (dPn (qExp F) (W ⟨0, hm⟩) i)) d *
          S_lt F (m - 1) (by omega : 0 < m - 1) (expTail W) d)
        = Δ * (P F d (dHead (qExp F) (W ⟨0, hm⟩) i) *
            (S_lt F 1 (by omega : 0 < 1) (single (dPn (qExp F) (W ⟨0, hm⟩) i)) d *
              S_lt F (m - 1) (by omega : 0 < m - 1) (expTail W) d)) := by ring
    _ = Δ * (P F d (dHead (qExp F) (W ⟨0, hm⟩) i) *
            (∑ e : D.ι, ((D.f e : ℤ) : RatFunc.CompletionAtInfty F) *
              S_lt F (D.dep e) (D.hdep e) (D.c e) d)) := by
          rw [D.hid d]
    _ = Δ * (∑ e : D.ι, (P F d (dHead (qExp F) (W ⟨0, hm⟩) i)) *
            (((D.f e : ℤ) : RatFunc.CompletionAtInfty F) *
              S_lt F (D.dep e) (D.hdep e) (D.c e) d)) := by
          rw [Finset.mul_sum]
    _ = ∑ e : D.ι, Δ * ((P F d (dHead (qExp F) (W ⟨0, hm⟩) i)) *
            (((D.f e : ℤ) : RatFunc.CompletionAtInfty F) *
              S_lt F (D.dep e) (D.hdep e) (D.c e) d)) := by
          rw [Finset.mul_sum]
    _ = ∑ e : D.ι, ((ChenDeltaZ F (qExp F : ℕ) (W ⟨0, hm⟩ : ℕ) i.1 * D.f e : ℤ) :
            RatFunc.CompletionAtInfty F) *
            (P F d (dHead (qExp F) (W ⟨0, hm⟩) i) *
              S_lt F (D.dep e) (D.hdep e) (D.c e) d) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [Int.cast_mul]
          ring
    _ = ∑ e : D.ι, ((ChenDeltaZ F (qExp F : ℕ) (W ⟨0, hm⟩ : ℕ) i.1 * D.f e : ℤ) :
            RatFunc.CompletionAtInfty F) *
            S F (D.dep e + 1) (by omega : 0 < D.dep e + 1)
              (consVec (dHead (qExp F) (W ⟨0, hm⟩) i) (D.c e)) d := by
          apply Finset.sum_congr rfl
          intro e he
          rw [S_prepend F d (dHead (qExp F) (W ⟨0, hm⟩) i) (D.hdep e) (D.c e)]

/-- P1 side of `CW(R1)` for `m ≥ 2`, `d ≥ 1`: `S_d(q)·S_<d+1(W)` is the `S_d`-sum of the
merge output `S_d(q+w1,W⁻)`, the depth-(m+1) tuple `S_d(q,w1,…,wm)`, and the
Δ-outputs. -/
lemma p1_a_side {m : ℕ} (hm2 : 1 < m) (hm : 0 < m) (W : Fin m → ℕ+) (d : ℕ) (hd : 1 ≤ d) :
    P F d (qExp F) * S_lt F m hm W (d + 1) =
      S F m hm (headAdd (qExp F) hm W) d +
      S F (m + 1) (by omega : 0 < m + 1) (consVec (qExp F) W) d +
      ∑ i : dIdx (qExp F) (W ⟨0, hm⟩),
        ∑ e : (p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).ι,
          ((ChenDeltaZ F (qExp F : ℕ) (W ⟨0, hm⟩ : ℕ) i.1 *
              (p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).f e : ℤ) :
            RatFunc.CompletionAtInfty F) *
          S F ((p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).dep e + 1)
            (by omega : 0 < (p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).dep e + 1)
            (consVec (dHead (qExp F) (W ⟨0, hm⟩) i)
              ((p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).c e)) d := by
  classical
  calc
    P F d (qExp F) * S_lt F m hm W (d + 1)
        = S F (m + 1) (by omega : 0 < m + 1) (consVec (qExp F) W) d +
            P F d (qExp F) * S F m hm W d := by
          rw [cw_first_split F hm W d]
    _ = S F (m + 1) (by omega : 0 < m + 1) (consVec (qExp F) W) d +
            (S F m hm (headAdd (qExp F) hm W) d +
            ∑ i : dIdx (qExp F) (W ⟨0, hm⟩),
              (ChenDeltaZ F (qExp F : ℕ) (W ⟨0, hm⟩ : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
              (P F d (dHead (qExp F) (W ⟨0, hm⟩) i) *
                S_lt F 1 (by omega : 0 < 1) (single (dPn (qExp F) (W ⟨0, hm⟩) i)) d *
                S_lt F (m - 1) (by omega : 0 < m - 1) (expTail W) d)) := by
          rw [pdq_mul_SdW_ge2 F hm2 hm W d hd]
    _ = S F m hm (headAdd (qExp F) hm W) d +
          S F (m + 1) (by omega : 0 < m + 1) (consVec (qExp F) W) d +
          ∑ i : dIdx (qExp F) (W ⟨0, hm⟩),
            (ChenDeltaZ F (qExp F : ℕ) (W ⟨0, hm⟩ : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
            (P F d (dHead (qExp F) (W ⟨0, hm⟩) i) *
              S_lt F 1 (by omega : 0 < 1) (single (dPn (qExp F) (W ⟨0, hm⟩) i)) d *
              S_lt F (m - 1) (by omega : 0 < m - 1) (expTail W) d) := by ring
    _ = S F m hm (headAdd (qExp F) hm W) d +
          S F (m + 1) (by omega : 0 < m + 1) (consVec (qExp F) W) d +
          ∑ i : dIdx (qExp F) (W ⟨0, hm⟩),
            ∑ e : (p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).ι,
              ((ChenDeltaZ F (qExp F : ℕ) (W ⟨0, hm⟩ : ℕ) i.1 *
                  (p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).f e : ℤ) :
                RatFunc.CompletionAtInfty F) *
              S F ((p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).dep e + 1)
                (by omega : 0 < (p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).dep e + 1)
                (consVec (dHead (qExp F) (W ⟨0, hm⟩) i)
                  ((p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).c e)) d := by
          apply congrArg (fun t : RatFunc.CompletionAtInfty F =>
            S F m hm (headAdd (qExp F) hm W) d +
              S F (m + 1) (by omega : 0 < m + 1) (consVec (qExp F) W) d + t)
          apply Finset.sum_congr rfl
          intro i hi
          exact delta_term_pure F hm2 hm W d i

/-- `m = 1` P1 side (explicit singleton `w1`): `S_d(q)·S_<d+1(w1) = S_d(q+w1) +
S_d(q,w1) + Σ_i Δ^i·S_d(q+w1−i, i)` (from `thakur_prod_one`). -/
lemma p1_a_side_m1 (w1 : ℕ+) (d : ℕ) (hd : 1 ≤ d) :
    P F d (qExp F) * S_lt F 1 (by omega : 0 < 1) (single w1) (d + 1) =
      S F 1 (by omega : 0 < 1) (single ⟨(qExp F : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩) d +
      S F 2 (by omega : 0 < 2) (consVec (qExp F) (single w1)) d +
      ∑ i : dIdx (qExp F) w1,
        (ChenDeltaZ F (qExp F : ℕ) (w1 : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
          S F 2 (by omega : 0 < 2) (thakurExp (qExp F : ℕ) (w1 : ℕ) i) d := by
  classical
  let q : ℕ+ := qExp F
  let qw1 : ℕ+ := ⟨(q : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos q) (w1 : ℕ)⟩
  have hS1 : S F 1 (by omega : 0 < 1) (single w1) d = P F d w1 := by
    rw [S_one_eq_P F d (by omega : 0 < 1) (single w1)]
    simp [single]
  have hS1' : S F 1 (by omega : 0 < 1) (single qw1) d = P F d qw1 := by
    rw [S_one_eq_P F d (by omega : 0 < 1) (single qw1)]
    simp [single]
  have ht := thakur_prod_one F d hd q w1
  calc
    P F d (qExp F) * S_lt F 1 (by omega : 0 < 1) (single w1) (d + 1)
        = S F 2 (by omega : 0 < 2) (consVec (qExp F) (single w1)) d + P F d (qExp F) * P F d w1 := by
          rw [cw_first_split F (by omega : 0 < 1) (single w1) d]
          rw [hS1]
    _ = S F 2 (by omega : 0 < 2) (consVec (qExp F) (single w1)) d + P F d q * P F d w1 := by rfl
    _ = S F 2 (by omega : 0 < 2) (consVec (qExp F) (single w1)) d +
          (P F d qw1 +
          ∑ i : dIdx q w1,
            (ChenDeltaZ F (q : ℕ) (w1 : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
              S F 2 (by omega : 0 < 2) (thakurExp (q : ℕ) (w1 : ℕ) i) d) := by
          rw [ht]
    _ = S F 2 (by omega : 0 < 2) (consVec (qExp F) (single w1)) d +
          (S F 1 (by omega : 0 < 1) (single qw1) d +
          ∑ i : dIdx q w1,
            (ChenDeltaZ F (q : ℕ) (w1 : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
              S F 2 (by omega : 0 < 2) (thakurExp (q : ℕ) (w1 : ℕ) i) d) := by
          rw [← hS1']
    _ = S F 1 (by omega : 0 < 1) (single qw1) d + S F 2 (by omega : 0 < 2) (consVec (qExp F) (single w1)) d +
          ∑ i : dIdx (qExp F) w1,
            (ChenDeltaZ F (qExp F : ℕ) (w1 : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
              S F 2 (by omega : 0 < 2) (thakurExp (qExp F : ℕ) (w1 : ℕ) i) d := by
          dsimp [q, qw1]
          ac_rfl

/-- `D1` side of `CW(R1)`: `D1·S_{d+1}(1)·(S_<d+1(q−1)·S_<d+1(W)) = Σ_j
(D1·g_j)·S_{d+1}(1 :: t_j)` for the Part-2 outputs `t_j ≤ (q−1)+W`. -/
lemma d1_b_side {m : ℕ} (hm : 0 < m) (W : Fin m → ℕ+) (d : ℕ) :
    D1c F * ((P F (d + 1) oneExp) *
        (S_lt F 1 (by omega : 0 < 1) (single (qMinusExp F)) (d + 1) *
          S_lt F m hm W (d + 1))) =
      ∑ e' : (p2Wb F hm W).ι,
        (D1c F * (((p2Wb F hm W).f e' : ℤ) : RatFunc.CompletionAtInfty F)) *
          S F ((p2Wb F hm W).dep e' + 1)
            (by omega : 0 < (p2Wb F hm W).dep e' + 1)
            (consVec oneExp ((p2Wb F hm W).c e')) (d + 1) := by
  classical
  let D := p2Wb F hm W
  change D1c F * ((P F (d + 1) oneExp) *
        (S_lt F 1 (by omega : 0 < 1) (single (qMinusExp F)) (d + 1) *
          S_lt F m hm W (d + 1))) =
      ∑ e' : D.ι, (D1c F * (((D.f e' : ℤ) : RatFunc.CompletionAtInfty F))) *
        S F (D.dep e' + 1) (by omega : 0 < D.dep e' + 1) (consVec oneExp (D.c e')) (d + 1)
  calc
    D1c F * ((P F (d + 1) oneExp) *
        (S_lt F 1 (by omega : 0 < 1) (single (qMinusExp F)) (d + 1) *
          S_lt F m hm W (d + 1)))
        = D1c F * ((P F (d + 1) oneExp) *
            (∑ e' : D.ι, (((D.f e' : ℤ) : RatFunc.CompletionAtInfty F)) *
              S_lt F (D.dep e') (D.hdep e') (D.c e') (d + 1))) := by
          rw [D.hid (d + 1)]
    _ = D1c F * (∑ e' : D.ι, (P F (d + 1) oneExp) *
            (((D.f e' : ℤ) : RatFunc.CompletionAtInfty F) *
              S_lt F (D.dep e') (D.hdep e') (D.c e') (d + 1))) := by
          rw [Finset.mul_sum]
    _ = ∑ e' : D.ι, D1c F * ((P F (d + 1) oneExp) *
            (((D.f e' : ℤ) : RatFunc.CompletionAtInfty F) *
              S_lt F (D.dep e') (D.hdep e') (D.c e') (d + 1))) := by
          rw [Finset.mul_sum]
    _ = ∑ e' : D.ι, (D1c F * (((D.f e' : ℤ) : RatFunc.CompletionAtInfty F))) *
            (P F (d + 1) oneExp *
              S_lt F (D.dep e') (D.hdep e') (D.c e') (d + 1)) := by
          apply Finset.sum_congr rfl
          intro e' he'
          ring
    _ = ∑ e' : D.ι, (D1c F * (((D.f e' : ℤ) : RatFunc.CompletionAtInfty F))) *
            S F (D.dep e' + 1) (by omega : 0 < D.dep e' + 1) (consVec oneExp (D.c e')) (d + 1) := by
          apply Finset.sum_congr rfl
          intro e' he'
          rw [S_prepend F (d + 1) oneExp (D.hdep e') (D.c e')]

/-- ★ `CW(R1) = 0` in pure-output form for `m ≥ 2`, `d ≥ 1`:
`S_d(q+w1,W⁻) + S_d(q,w1,…,wm) + (Δ-outputs) + (D1-outputs at level d+1) = 0`. -/
theorem cw_r1_pure_ge2 {m : ℕ} (hm2 : 1 < m) (hm : 0 < m) (W : Fin m → ℕ+) :
    ∀ d : ℕ, 1 ≤ d →
      S F m hm (headAdd (qExp F) hm W) d +
      S F (m + 1) (by omega : 0 < m + 1) (consVec (qExp F) W) d +
      ∑ i : dIdx (qExp F) (W ⟨0, hm⟩),
        ∑ e : (p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).ι,
          ((ChenDeltaZ F (qExp F : ℕ) (W ⟨0, hm⟩ : ℕ) i.1 *
              (p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).f e : ℤ) :
            RatFunc.CompletionAtInfty F) *
          S F ((p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).dep e + 1)
            (by omega : 0 < (p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).dep e + 1)
            (consVec (dHead (qExp F) (W ⟨0, hm⟩) i)
              ((p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).c e)) d +
      ∑ e' : (p2Wb F hm W).ι,
        (D1c F * (((p2Wb F hm W).f e' : ℤ) : RatFunc.CompletionAtInfty F)) *
          S F ((p2Wb F hm W).dep e' + 1)
            (by omega : 0 < (p2Wb F hm W).dep e' + 1)
            (consVec oneExp ((p2Wb F hm W).c e')) (d + 1)
      = 0 := by
  classical
  intro d hd
  have hD := cw_r1_display F hm W d
  rw [p1_a_side F hm2 hm W d hd] at hD
  rw [d1_b_side F hm W d] at hD
  simpa [add_assoc] using hD

/-- ★ `CW(R1) = 0` in pure-output form for `m = 1`, `d ≥ 1`. -/
theorem cw_r1_pure_m1 (w1 : ℕ+) : ∀ d : ℕ, 1 ≤ d →
    S F 1 (by omega : 0 < 1)
        (single ⟨(qExp F : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩) d +
      S F 2 (by omega : 0 < 2) (consVec (qExp F) (single w1)) d +
      ∑ i : dIdx (qExp F) w1,
        (ChenDeltaZ F (qExp F : ℕ) (w1 : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
          S F 2 (by omega : 0 < 2) (thakurExp (qExp F : ℕ) (w1 : ℕ) i) d +
      ∑ e' : (p2Wb F (by omega : 0 < 1) (single w1)).ι,
        (D1c F * (((p2Wb F (by omega : 0 < 1) (single w1)).f e' : ℤ) : RatFunc.CompletionAtInfty F)) *
          S F ((p2Wb F (by omega : 0 < 1) (single w1)).dep e' + 1)
            (by omega : 0 < (p2Wb F (by omega : 0 < 1) (single w1)).dep e' + 1)
            (consVec oneExp ((p2Wb F (by omega : 0 < 1) (single w1)).c e')) (d + 1)
      = 0 := by
  classical
  intro d hd
  have hD := cw_r1_display F (by omega : 0 < 1) (single w1) d
  rw [p1_a_side_m1 F w1 d hd] at hD
  rw [d1_b_side F (by omega : 0 < 1) (single w1) d] at hD
  simpa [add_assoc] using hD


/-- `S_<d` at level `0` is the empty sum. -/
lemma S_lt_zero {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) : S_lt F r hr 𝔰 0 = 0 := by
  rw [S_lt_eq_sum_levels F r hr 𝔰 0]
  simp

/-- `S_<1(W) = S_0(W) = 0` for depth `m ≥ 2`. -/
lemma S_lt_one_eq_zero_ge2 {m : ℕ} (hm2 : 1 < m) (hm : 0 < m) (W : Fin m → ℕ+) :
    S_lt F m hm W 1 = 0 := by
  rw [S_lt_succ F m hm W 0]
  rw [S_lt_zero]
  rw [S_zero_of_depth_ge_two F hm (by omega : 1 < m) W]
  simp

/-- `S_<1(w1) = P_0(w1) = 1` for a depth-one tuple. -/
lemma S_lt_one_single_one (w1 : ℕ+) : S_lt F 1 (by omega : 0 < 1) (single w1) 1 = 1 := by
  rw [S_lt_succ F 1 (by omega : 0 < 1) (single w1) 0]
  rw [S_lt_eq_sum_levels F 1 (by omega : 0 < 1) (single w1) 0]
  simp
  rw [S_one_eq_P F 0 (by omega : 0 < 1) (single w1)]
  simp [single]
  rw [P_zero_eq_one F w1]

/-- Level-zero block of a depth-`m+1` prepend (depth ≥ 2) vanishes. -/
lemma S_cons_zero {m : ℕ} (hm : 0 < m) (x : ℕ+) (W : Fin m → ℕ+) :
    S F (m + 1) (by omega : 0 < m + 1) (consVec x W) 0 = 0 := by
  exact S_zero_of_depth_ge_two F (by omega : 0 < m + 1) (by omega : 1 < m + 1) (consVec x W)

/-- ★ `CW(R1) = 0` in pure-output form for `m ≥ 2`, **every** level `d ≥ 0`
(`cw_r1_pure_ge2` plus the `d = 0` case, where every depth-≥-2 block vanishes). -/
theorem cw_r1_pure_ge2_all {m : ℕ} (hm2 : 1 < m) (hm : 0 < m) (W : Fin m → ℕ+) :
    ∀ d : ℕ,
      S F m hm (headAdd (qExp F) hm W) d +
      S F (m + 1) (by omega : 0 < m + 1) (consVec (qExp F) W) d +
      ∑ i : dIdx (qExp F) (W ⟨0, hm⟩),
        ∑ e : (p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).ι,
          ((ChenDeltaZ F (qExp F : ℕ) (W ⟨0, hm⟩ : ℕ) i.1 *
              (p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).f e : ℤ) :
            RatFunc.CompletionAtInfty F) *
          S F ((p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).dep e + 1)
            (by omega : 0 < (p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).dep e + 1)
            (consVec (dHead (qExp F) (W ⟨0, hm⟩) i)
              ((p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).c e)) d +
      ∑ e' : (p2Wb F hm W).ι,
        (D1c F * (((p2Wb F hm W).f e' : ℤ) : RatFunc.CompletionAtInfty F)) *
          S F ((p2Wb F hm W).dep e' + 1)
            (by omega : 0 < (p2Wb F hm W).dep e' + 1)
            (consVec oneExp ((p2Wb F hm W).c e')) (d + 1)
      = 0 := by
  classical
  intro d
  by_cases hd0 : d = 0
  · subst d
    have hA : S F m hm (headAdd (qExp F) hm W) 0 = 0 :=
      S_zero_of_depth_ge_two F hm (by omega : 1 < m) (headAdd (qExp F) hm W)
    have hB : S F (m + 1) (by omega : 0 < m + 1) (consVec (qExp F) W) 0 = 0 :=
      S_cons_zero F hm (qExp F) W
    have hC : (∑ i : dIdx (qExp F) (W ⟨0, hm⟩),
        ∑ e : (p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).ι,
          ((ChenDeltaZ F (qExp F : ℕ) (W ⟨0, hm⟩ : ℕ) i.1 *
              (p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).f e : ℤ) :
            RatFunc.CompletionAtInfty F) *
          S F ((p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).dep e + 1)
            (by omega : 0 < (p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).dep e + 1)
            (consVec (dHead (qExp F) (W ⟨0, hm⟩) i)
              ((p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).c e)) 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro e he
      have hge : 1 < (p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).dep e + 1 := by
        have hpos : 0 < (p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).dep e :=
          (p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).hdep e
        omega
      rw [S_zero_of_depth_ge_two F
        (by omega : 0 < (p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).dep e + 1)
        hge (consVec (dHead (qExp F) (W ⟨0, hm⟩) i)
              ((p2Wp F (dPn (qExp F) (W ⟨0, hm⟩) i) hm2 hm W).c e))]
      simp
    have hD : (∑ e' : (p2Wb F hm W).ι,
        (D1c F * (((p2Wb F hm W).f e' : ℤ) : RatFunc.CompletionAtInfty F)) *
          S F ((p2Wb F hm W).dep e' + 1)
            (by omega : 0 < (p2Wb F hm W).dep e' + 1)
            (consVec oneExp ((p2Wb F hm W).c e')) 1) = 0 := by
      rw [← d1_b_side F hm W 0]
      rw [S_lt_one_eq_zero_ge2 F hm2 hm W]
      simp
    rw [hA, hB, hC, hD]
    simp
  · exact cw_r1_pure_ge2 F hm2 hm W d (by omega)

/-- ★ `CW(R1) = 0` in pure-output form for `m = 1`, **every** level `d ≥ 0`. -/
theorem cw_r1_pure_m1_all (w1 : ℕ+) : ∀ d : ℕ,
    S F 1 (by omega : 0 < 1)
        (single ⟨(qExp F : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩) d +
      S F 2 (by omega : 0 < 2) (consVec (qExp F) (single w1)) d +
      ∑ i : dIdx (qExp F) w1,
        (ChenDeltaZ F (qExp F : ℕ) (w1 : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
          S F 2 (by omega : 0 < 2) (thakurExp (qExp F : ℕ) (w1 : ℕ) i) d +
      ∑ e' : (p2Wb F (by omega : 0 < 1) (single w1)).ι,
        (D1c F * (((p2Wb F (by omega : 0 < 1) (single w1)).f e' : ℤ) : RatFunc.CompletionAtInfty F)) *
          S F ((p2Wb F (by omega : 0 < 1) (single w1)).dep e' + 1)
            (by omega : 0 < (p2Wb F (by omega : 0 < 1) (single w1)).dep e' + 1)
            (consVec oneExp ((p2Wb F (by omega : 0 < 1) (single w1)).c e')) (d + 1)
      = 0 := by
  classical
  intro d
  by_cases hd0 : d = 0
  · subst d
    let q : ℕ+ := qExp F
    let qw1 : ℕ+ := ⟨(q : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos q) (w1 : ℕ)⟩
    have hA : S F 1 (by omega : 0 < 1) (single qw1) 0 = 1 := by
      rw [S_one_eq_P F 0 (by omega : 0 < 1) (single qw1)]
      simp [single]
      rw [P_zero_eq_one F qw1]
    have hB : S F 2 (by omega : 0 < 2) (consVec (qExp F) (single w1)) 0 = 0 := by
      exact S_zero_of_depth_ge_two F (by omega : 0 < 2) (by omega : 1 < 2)
        (consVec (qExp F) (single w1))
    have hC : (∑ i : dIdx (qExp F) w1,
        (ChenDeltaZ F (qExp F : ℕ) (w1 : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
          S F 2 (by omega : 0 < 2) (thakurExp (qExp F : ℕ) (w1 : ℕ) i) 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [S_zero_of_depth_ge_two F (by omega : 0 < 2) (by omega : 1 < 2)
        (thakurExp (qExp F : ℕ) (w1 : ℕ) i)]
      simp
    have hD : (∑ e' : (p2Wb F (by omega : 0 < 1) (single w1)).ι,
        (D1c F * (((p2Wb F (by omega : 0 < 1) (single w1)).f e' : ℤ) : RatFunc.CompletionAtInfty F)) *
          S F ((p2Wb F (by omega : 0 < 1) (single w1)).dep e' + 1)
            (by omega : 0 < (p2Wb F (by omega : 0 < 1) (single w1)).dep e' + 1)
            (consVec oneExp ((p2Wb F (by omega : 0 < 1) (single w1)).c e')) 1)
        = D1c F * P F 1 oneExp := by
      rw [← d1_b_side F (by omega : 0 < 1) (single w1) 0]
      rw [S_lt_one_single_one F (qMinusExp F)]
      rw [S_lt_one_single_one F w1]
      ring
    change S F 1 (by omega : 0 < 1) (single qw1) 0 +
      S F 2 (by omega : 0 < 2) (consVec (qExp F) (single w1)) 0 +
      (∑ i : dIdx (qExp F) w1,
        (ChenDeltaZ F (qExp F : ℕ) (w1 : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
          S F 2 (by omega : 0 < 2) (thakurExp (qExp F : ℕ) (w1 : ℕ) i) 0) +
      (∑ e' : (p2Wb F (by omega : 0 < 1) (single w1)).ι,
        (D1c F * (((p2Wb F (by omega : 0 < 1) (single w1)).f e' : ℤ) : RatFunc.CompletionAtInfty F)) *
          S F ((p2Wb F (by omega : 0 < 1) (single w1)).dep e' + 1)
            (by omega : 0 < (p2Wb F (by omega : 0 < 1) (single w1)).dep e' + 1)
            (consVec oneExp ((p2Wb F (by omega : 0 < 1) (single w1)).c e')) 1) = 0
    rw [hA, hB, hC, hD]
    have hR1 := R1_all_unc F 0
    simp [R1Prop] at hR1
    rw [P_zero_eq_one F (qExp F)] at hR1
    have hS2 := S2_recursion F 1
    rw [hS2] at hR1
    rw [S_lt_one_single_one F (qMinusExp F)] at hR1
    simp [mul_one] at hR1
    simpa using hR1
  · exact cw_r1_pure_m1 F w1 d (by omega)



/-- Prefix sums of a prepend stay ≤ the sum of the two prefix sums
(`psum (x::W) n ≤ psum (x) n + psum W n`). -/
lemma psum_consVec_le {m : ℕ} (x : ℕ+) (W : Fin m → ℕ+) :
    ∀ n : ℕ, psum (consVec x W) n ≤ psum (single x) n + psum W n := by
  intro n
  cases n with
  | zero => simp [psum_zero]
  | succ n' =>
    rw [psum_consVec]
    rw [psum_single_of_pos x (by omega : 0 < n' + 1)]
    have h := psum_mono W (Nat.le_succ n')
    exact Nat.add_le_add_left h (x : ℕ)

/-- The `(q,W)` output of the P1 side is ≤ `(q) + W`: `LePad (q :: W) (q) W`. -/
lemma LePad_cons_q {m : ℕ} (W : Fin m → ℕ+) :
    LePad (consVec (qExp F) W) (single (qExp F)) W := by
  classical
  constructor
  · rw [weight_consVec, weight_single]
  · intro n
    rw [psumSeq_tupPadSum (single (qExp F)) W n]
    exact psum_consVec_le (qExp F) W n

/-- First entry of the `(q,W)` output: `q < q + w1`. -/
lemma cons_q_head_lt {m : ℕ} (hm : 0 < m) (W : Fin m → ℕ+) :
    ((consVec (qExp F) W) ⟨0, (by omega : 0 < m + 1)⟩ : ℕ) <
      (qExp F : ℕ) + (W ⟨0, hm⟩ : ℕ) := by
  have h0 : (consVec (qExp F) W) ⟨0, (by omega : 0 < m + 1)⟩ = qExp F := by
    simpa using (consVec_zero (qExp F) W)
  rw [h0]
  have hpos : 0 < (W ⟨0, hm⟩ : ℕ) := (W ⟨0, hm⟩).pos
  omega

/-- The general Δ-output bound: from `u ≤ (i) + B` and `hd + i = q + w1` we get
`hd :: u ≤ (q) + (w1 :: B)`.  (Here `hd = q+w1−i` is a Chen-Δ head.) -/
lemma LePad_cons_dHead {k L : ℕ} (hd i q w1 : ℕ+) (u : Fin L → ℕ+) (B : Fin k → ℕ+)
    (hsum : (hd : ℕ) + (i : ℕ) = (q : ℕ) + (w1 : ℕ))
    (hle : LePad u (single i) B) :
    LePad (consVec hd u) (single q) (consVec w1 B) := by
  classical
  constructor
  · rw [weight_consVec, weight_consVec, weight_single]
    rcases hle with ⟨hw, _⟩
    rw [hw]
    rw [weight_single]
    omega
  · intro n
    rw [psumSeq_tupPadSum (single q) (consVec w1 B) n]
    cases n with
    | zero => simp [psum_zero]
    | succ n' =>
      rw [psum_consVec]
      rw [psum_consVec]
      rw [psum_single_of_pos q (by omega : 0 < n' + 1)]
      by_cases hn' : n' = 0
      · subst n'
        rw [psum_zero, psum_zero]
        have hi : 1 ≤ (i : ℕ) := (i : ℕ+).pos
        omega
      · have hnpos : 0 < n' := Nat.pos_of_ne_zero hn'
        have hp := hle.2 n'
        rw [psumSeq_tupPadSum (single i) B n'] at hp
        rw [psum_single_of_pos i hnpos] at hp
        calc
          (hd : ℕ) + psum u n' ≤ (hd : ℕ) + ((i : ℕ) + psum B n') := by
            exact Nat.add_le_add_left hp (hd : ℕ)
          _ = ((hd : ℕ) + (i : ℕ)) + psum B n' := by omega
          _ = ((q : ℕ) + (w1 : ℕ)) + psum B n' := by rw [hsum]
          _ = (q : ℕ) + ((w1 : ℕ) + psum B n') := by omega



/-
# consVec-normal forms of the CW(R1) pure decomposition

The lemmas below restate `cw_r1_pure_ge2_all`/`p1_a_side` with the tuple given in
cons-normal form `W := w1 :: B` (`B : Fin k → ℕ+`, depth `k+1`), so that all index
types and witnesses are expressed directly in the head `w1` and the tail `B`
(no `W⟨0,·⟩`/`expTail W` type dependencies).  These are the lemmas the
Lemma-2.9 ∃-statement is assembled from.  -/

noncomputable def p2WpT (v : ℕ+) {k : ℕ} (_hk : 0 < k) (B : Fin k → ℕ+) :
    P2Data F 1 k (by omega : 0 < 1) (by omega : 0 < k) (single v) B := by
  classical
  have hfull := p1p2_full_all F k (by omega : 0 < k) 1 (by omega : 0 < 1)
  exact Classical.choice ((hfull.2) (by omega : 0 < 1) (by omega : 0 < k) (single v) B)

lemma S_recursion_cons {k : ℕ} (hk : 0 < k) (w1 : ℕ+) (B : Fin k → ℕ+) (d : ℕ) :
    S F (k + 1) (by omega : 0 < k + 1) (consVec w1 B) d =
      P F d w1 * S_lt F k hk B d := by
  classical
  have hrec := S_d_recursion F (k + 1) (by omega : 1 < k + 1) (by omega : 0 < k + 1) hk
    (consVec w1 B) d
  calc
    S F (k + 1) (by omega : 0 < k + 1) (consVec w1 B) d
        = P F d ((consVec w1 B) ⟨0, (by omega : 0 < k + 1)⟩) *
            S_lt F k hk (fun j : Fin k => (consVec w1 B) ⟨j.1 + 1, by omega⟩) d := by
          exact hrec
    _ = P F d w1 * S_lt F k hk B d := by
          have h0 : (consVec w1 B) ⟨0, (by omega : 0 < k + 1)⟩ = w1 := by
            simpa using (consVec_zero w1 B)
          rw [h0]
          have htail : (fun j : Fin k => (consVec w1 B) ⟨j.1 + 1, by omega⟩) = B := by
            funext j
            exact (consVec_succ w1 B j)
          rw [htail]

lemma delta_term_pure_cons {k : ℕ} (hk : 0 < k) (w1 : ℕ+) (B : Fin k → ℕ+) (d : ℕ)
    (j : dIdx (qExp F) w1) :
    (ChenDeltaZ F (qExp F : ℕ) (w1 : ℕ) j.1 : RatFunc.CompletionAtInfty F) *
        (P F d (dHead (qExp F) w1 j) *
          S_lt F 1 (by omega : 0 < 1) (single (dPn (qExp F) w1 j)) d *
          S_lt F k hk B d) =
      ∑ e : (p2WpT F (dPn (qExp F) w1 j) hk B).ι,
        ((ChenDeltaZ F (qExp F : ℕ) (w1 : ℕ) j.1 * (p2WpT F (dPn (qExp F) w1 j) hk B).f e : ℤ) :
          RatFunc.CompletionAtInfty F) *
        S F ((p2WpT F (dPn (qExp F) w1 j) hk B).dep e + 1)
          (by omega : 0 < (p2WpT F (dPn (qExp F) w1 j) hk B).dep e + 1)
          (consVec (dHead (qExp F) w1 j) ((p2WpT F (dPn (qExp F) w1 j) hk B).c e)) d := by
  classical
  let D := p2WpT F (dPn (qExp F) w1 j) hk B
  let Δ : RatFunc.CompletionAtInfty F :=
    (ChenDeltaZ F (qExp F : ℕ) (w1 : ℕ) j.1 : RatFunc.CompletionAtInfty F)
  change Δ * (P F d (dHead (qExp F) w1 j) *
          S_lt F 1 (by omega : 0 < 1) (single (dPn (qExp F) w1 j)) d *
          S_lt F k hk B d) =
      ∑ e : D.ι, ((ChenDeltaZ F (qExp F : ℕ) (w1 : ℕ) j.1 * D.f e : ℤ) :
          RatFunc.CompletionAtInfty F) *
        S F (D.dep e + 1) (by omega : 0 < D.dep e + 1)
          (consVec (dHead (qExp F) w1 j) (D.c e)) d
  calc
    Δ * (P F d (dHead (qExp F) w1 j) *
          S_lt F 1 (by omega : 0 < 1) (single (dPn (qExp F) w1 j)) d *
          S_lt F k hk B d)
        = Δ * (P F d (dHead (qExp F) w1 j) *
            (S_lt F 1 (by omega : 0 < 1) (single (dPn (qExp F) w1 j)) d *
              S_lt F k hk B d)) := by ring
    _ = Δ * (P F d (dHead (qExp F) w1 j) *
            (∑ e : D.ι, ((D.f e : ℤ) : RatFunc.CompletionAtInfty F) *
              S_lt F (D.dep e) (D.hdep e) (D.c e) d)) := by
          rw [D.hid d]
    _ = Δ * (∑ e : D.ι, (P F d (dHead (qExp F) w1 j)) *
            (((D.f e : ℤ) : RatFunc.CompletionAtInfty F) *
              S_lt F (D.dep e) (D.hdep e) (D.c e) d)) := by
          rw [Finset.mul_sum]
    _ = ∑ e : D.ι, Δ * ((P F d (dHead (qExp F) w1 j)) *
            (((D.f e : ℤ) : RatFunc.CompletionAtInfty F) *
              S_lt F (D.dep e) (D.hdep e) (D.c e) d)) := by
          rw [Finset.mul_sum]
    _ = ∑ e : D.ι, ((ChenDeltaZ F (qExp F : ℕ) (w1 : ℕ) j.1 * D.f e : ℤ) :
            RatFunc.CompletionAtInfty F) *
            (P F d (dHead (qExp F) w1 j) *
              S_lt F (D.dep e) (D.hdep e) (D.c e) d) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [Int.cast_mul]
          ring
    _ = ∑ e : D.ι, ((ChenDeltaZ F (qExp F : ℕ) (w1 : ℕ) j.1 * D.f e : ℤ) :
            RatFunc.CompletionAtInfty F) *
            S F (D.dep e + 1) (by omega : 0 < D.dep e + 1)
              (consVec (dHead (qExp F) w1 j) (D.c e)) d := by
          apply Finset.sum_congr rfl
          intro e he
          rw [S_prepend F d (dHead (qExp F) w1 j) (D.hdep e) (D.c e)]

-- import needed bits from StepL3 already there (p1_a_side_cons added below in scratch-free full form)
lemma p1_a_side_cons {k : ℕ} (hk : 0 < k) (w1 : ℕ+) (B : Fin k → ℕ+) (d : ℕ) (hd : 1 ≤ d) :
    P F d (qExp F) * S_lt F (k + 1) (by omega : 0 < k + 1) (consVec w1 B) (d + 1) =
      S F (k + 1) (by omega : 0 < k + 1)
          (consVec ⟨(qExp F : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩ B) d +
      S F (k + 2) (by omega : 0 < k + 2) (consVec (qExp F) (consVec w1 B)) d +
      ∑ j : dIdx (qExp F) w1,
        ∑ e : (p2WpT F (dPn (qExp F) w1 j) hk B).ι,
          ((ChenDeltaZ F (qExp F : ℕ) (w1 : ℕ) j.1 *
              (p2WpT F (dPn (qExp F) w1 j) hk B).f e : ℤ) :
            RatFunc.CompletionAtInfty F) *
          S F ((p2WpT F (dPn (qExp F) w1 j) hk B).dep e + 1)
            (by omega : 0 < (p2WpT F (dPn (qExp F) w1 j) hk B).dep e + 1)
            (consVec (dHead (qExp F) w1 j) ((p2WpT F (dPn (qExp F) w1 j) hk B).c e)) d := by
  classical
  let q : ℕ+ := qExp F
  let qw1 : ℕ+ := ⟨(q : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos q) (w1 : ℕ)⟩
  have ht := thakur_prod_one F d hd q w1
  calc
    P F d (qExp F) * S_lt F (k + 1) (by omega : 0 < k + 1) (consVec w1 B) (d + 1)
        = S F (k + 2) (by omega : 0 < k + 2) (consVec (qExp F) (consVec w1 B)) d +
            P F d (qExp F) * S F (k + 1) (by omega : 0 < k + 1) (consVec w1 B) d := by
          rw [cw_first_split F (by omega : 0 < k + 1) (consVec w1 B) d]
    _ = S F (k + 2) (by omega : 0 < k + 2) (consVec (qExp F) (consVec w1 B)) d +
            P F d (qExp F) * (P F d w1 * S_lt F k hk B d) := by
          rw [S_recursion_cons F hk w1 B d]
    _ = S F (k + 2) (by omega : 0 < k + 2) (consVec (qExp F) (consVec w1 B)) d +
            (P F d q * P F d w1) * S_lt F k hk B d := by
          dsimp [q]
          ring
    _ = S F (k + 2) (by omega : 0 < k + 2) (consVec (qExp F) (consVec w1 B)) d +
            (P F d qw1 +
            ∑ j : dIdx q w1,
              (ChenDeltaZ F (q : ℕ) (w1 : ℕ) j.1 : RatFunc.CompletionAtInfty F) *
                S F 2 (by omega : 0 < 2) (thakurExp (q : ℕ) (w1 : ℕ) j) d) * S_lt F k hk B d := by
          rw [ht]
    _ = S F (k + 2) (by omega : 0 < k + 2) (consVec (qExp F) (consVec w1 B)) d +
            (P F d qw1 * S_lt F k hk B d +
              (∑ j : dIdx q w1,
                (ChenDeltaZ F (q : ℕ) (w1 : ℕ) j.1 : RatFunc.CompletionAtInfty F) *
                  S F 2 (by omega : 0 < 2) (thakurExp (q : ℕ) (w1 : ℕ) j) d) * S_lt F k hk B d) := by
          rw [add_mul]
    _ = S F (k + 2) (by omega : 0 < k + 2) (consVec (qExp F) (consVec w1 B)) d +
            (S F (k + 1) (by omega : 0 < k + 1) (consVec qw1 B) d +
              (∑ j : dIdx q w1,
                (ChenDeltaZ F (q : ℕ) (w1 : ℕ) j.1 : RatFunc.CompletionAtInfty F) *
                  S F 2 (by omega : 0 < 2) (thakurExp (q : ℕ) (w1 : ℕ) j) d) * S_lt F k hk B d) := by
          rw [S_prepend F d qw1 hk B]
    _ = S F (k + 2) (by omega : 0 < k + 2) (consVec (qExp F) (consVec w1 B)) d +
            (S F (k + 1) (by omega : 0 < k + 1) (consVec qw1 B) d +
              ∑ j : dIdx q w1,
                (ChenDeltaZ F (q : ℕ) (w1 : ℕ) j.1 : RatFunc.CompletionAtInfty F) *
                  S F 2 (by omega : 0 < 2) (thakurExp (q : ℕ) (w1 : ℕ) j) d * S_lt F k hk B d) := by
          rw [Finset.sum_mul]
    _ = S F (k + 1) (by omega : 0 < k + 1) (consVec qw1 B) d +
          S F (k + 2) (by omega : 0 < k + 2) (consVec (qExp F) (consVec w1 B)) d +
          ∑ j : dIdx q w1,
            (ChenDeltaZ F (q : ℕ) (w1 : ℕ) j.1 : RatFunc.CompletionAtInfty F) *
              S F 2 (by omega : 0 < 2) (thakurExp (q : ℕ) (w1 : ℕ) j) d * S_lt F k hk B d := by
          ac_rfl
    _ = S F (k + 1) (by omega : 0 < k + 1)
            (consVec ⟨(qExp F : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩ B) d +
          S F (k + 2) (by omega : 0 < k + 2) (consVec (qExp F) (consVec w1 B)) d +
          ∑ j : dIdx (qExp F) w1,
            (ChenDeltaZ F (qExp F : ℕ) (w1 : ℕ) j.1 : RatFunc.CompletionAtInfty F) *
              (P F d (dHead (qExp F) w1 j) *
                S_lt F 1 (by omega : 0 < 1) (single (dPn (qExp F) w1 j)) d *
                S_lt F k hk B d) := by
          apply congrArg (fun t : RatFunc.CompletionAtInfty F =>
            S F (k + 1) (by omega : 0 < k + 1)
              (consVec ⟨(qExp F : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩ B) d +
              S F (k + 2) (by omega : 0 < k + 2) (consVec (qExp F) (consVec w1 B)) d + t)
          apply Finset.sum_congr rfl
          intro j hj
          rw [thakur_S_two_eq F d (qExp F : ℕ) (w1 : ℕ) j]
          dsimp [q, dHead, dPn, single]
          ac_rfl
    _ = S F (k + 1) (by omega : 0 < k + 1)
            (consVec ⟨(qExp F : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩ B) d +
          S F (k + 2) (by omega : 0 < k + 2) (consVec (qExp F) (consVec w1 B)) d +
          ∑ j : dIdx (qExp F) w1,
            ∑ e : (p2WpT F (dPn (qExp F) w1 j) hk B).ι,
              ((ChenDeltaZ F (qExp F : ℕ) (w1 : ℕ) j.1 *
                  (p2WpT F (dPn (qExp F) w1 j) hk B).f e : ℤ) :
                RatFunc.CompletionAtInfty F) *
              S F ((p2WpT F (dPn (qExp F) w1 j) hk B).dep e + 1)
                (by omega : 0 < (p2WpT F (dPn (qExp F) w1 j) hk B).dep e + 1)
                (consVec (dHead (qExp F) w1 j) ((p2WpT F (dPn (qExp F) w1 j) hk B).c e)) d := by
          apply congrArg (fun t : RatFunc.CompletionAtInfty F =>
            S F (k + 1) (by omega : 0 < k + 1)
              (consVec ⟨(qExp F : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩ B) d +
              S F (k + 2) (by omega : 0 < k + 2) (consVec (qExp F) (consVec w1 B)) d + t)
          apply Finset.sum_congr rfl
          intro j hj
          exact delta_term_pure_cons F hk w1 B d j

-- CW pure cons form (k>=1), all d
theorem cw_r1_pure_cons {k : ℕ} (hk : 0 < k) (w1 : ℕ+) (B : Fin k → ℕ+) :
    ∀ d : ℕ,
      S F (k + 1) (by omega : 0 < k + 1)
          (consVec ⟨(qExp F : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩ B) d +
      S F (k + 2) (by omega : 0 < k + 2) (consVec (qExp F) (consVec w1 B)) d +
      ∑ j : dIdx (qExp F) w1,
        ∑ e : (p2WpT F (dPn (qExp F) w1 j) hk B).ι,
          ((ChenDeltaZ F (qExp F : ℕ) (w1 : ℕ) j.1 *
              (p2WpT F (dPn (qExp F) w1 j) hk B).f e : ℤ) :
            RatFunc.CompletionAtInfty F) *
          S F ((p2WpT F (dPn (qExp F) w1 j) hk B).dep e + 1)
            (by omega : 0 < (p2WpT F (dPn (qExp F) w1 j) hk B).dep e + 1)
            (consVec (dHead (qExp F) w1 j) ((p2WpT F (dPn (qExp F) w1 j) hk B).c e)) d +
      ∑ e' : (p2Wb F (by omega : 0 < k + 1) (consVec w1 B)).ι,
        (D1c F * (((p2Wb F (by omega : 0 < k + 1) (consVec w1 B)).f e' : ℤ) :
            RatFunc.CompletionAtInfty F)) *
          S F ((p2Wb F (by omega : 0 < k + 1) (consVec w1 B)).dep e' + 1)
            (by omega : 0 < (p2Wb F (by omega : 0 < k + 1) (consVec w1 B)).dep e' + 1)
            (consVec oneExp ((p2Wb F (by omega : 0 < k + 1) (consVec w1 B)).c e')) (d + 1)
      = 0 := by
  classical
  intro d
  by_cases hd0 : d = 0
  · subst d
    have hA : S F (k + 1) (by omega : 0 < k + 1)
        (consVec ⟨(qExp F : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩ B) 0 = 0 := by
      exact S_zero_of_depth_ge_two F (by omega : 0 < k + 1) (by omega : 1 < k + 1)
        (consVec ⟨(qExp F : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩ B)
    have hB : S F (k + 2) (by omega : 0 < k + 2) (consVec (qExp F) (consVec w1 B)) 0 = 0 := by
      exact S_zero_of_depth_ge_two F (by omega : 0 < k + 2) (by omega : 1 < k + 2)
        (consVec (qExp F) (consVec w1 B))
    have hC : (∑ j : dIdx (qExp F) w1,
        ∑ e : (p2WpT F (dPn (qExp F) w1 j) hk B).ι,
          ((ChenDeltaZ F (qExp F : ℕ) (w1 : ℕ) j.1 *
              (p2WpT F (dPn (qExp F) w1 j) hk B).f e : ℤ) :
            RatFunc.CompletionAtInfty F) *
          S F ((p2WpT F (dPn (qExp F) w1 j) hk B).dep e + 1)
            (by omega : 0 < (p2WpT F (dPn (qExp F) w1 j) hk B).dep e + 1)
            (consVec (dHead (qExp F) w1 j) ((p2WpT F (dPn (qExp F) w1 j) hk B).c e)) 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      apply Finset.sum_eq_zero
      intro e he
      have hge : 1 < (p2WpT F (dPn (qExp F) w1 j) hk B).dep e + 1 := by
        have hpos : 0 < (p2WpT F (dPn (qExp F) w1 j) hk B).dep e :=
          (p2WpT F (dPn (qExp F) w1 j) hk B).hdep e
        omega
      rw [S_zero_of_depth_ge_two F
        (by omega : 0 < (p2WpT F (dPn (qExp F) w1 j) hk B).dep e + 1) hge
        (consVec (dHead (qExp F) w1 j) ((p2WpT F (dPn (qExp F) w1 j) hk B).c e))]
      simp
    have hD : (∑ e' : (p2Wb F (by omega : 0 < k + 1) (consVec w1 B)).ι,
        (D1c F * (((p2Wb F (by omega : 0 < k + 1) (consVec w1 B)).f e' : ℤ) :
            RatFunc.CompletionAtInfty F)) *
          S F ((p2Wb F (by omega : 0 < k + 1) (consVec w1 B)).dep e' + 1)
            (by omega : 0 < (p2Wb F (by omega : 0 < k + 1) (consVec w1 B)).dep e' + 1)
            (consVec oneExp ((p2Wb F (by omega : 0 < k + 1) (consVec w1 B)).c e')) 1) = 0 := by
      rw [← d1_b_side F (by omega : 0 < k + 1) (consVec w1 B) 0]
      rw [S_lt_one_eq_zero_ge2 F (by omega : 1 < k + 1) (by omega : 0 < k + 1) (consVec w1 B)]
      simp
    rw [hA, hB, hC, hD]
    simp
  · have hD := cw_r1_display F (by omega : 0 < k + 1) (consVec w1 B) d
    rw [p1_a_side_cons F hk w1 B d (by omega)] at hD
    rw [d1_b_side F (by omega : 0 < k + 1) (consVec w1 B) d] at hD
    simpa [add_assoc] using hD



/-- Empty-tail prepend is the singleton: `x :: B = (x)` for `B : Fin 0`. -/
lemma consVec_empty' (x : ℕ+) (B : Fin 0 → ℕ+) : consVec x B = single x := by
  funext j
  fin_cases j
  simp [consVec, single]

/-- `CW(R1) = 0` in consVec-normal form, depth-one tuple (k = 0, m = 1), every level. -/
theorem cw_r1_pure_cons0 (w1 : ℕ+) : ∀ (B : Fin 0 → ℕ+) (d : ℕ),
    S F 1 (by omega : 0 < 1)
        (consVec ⟨(qExp F : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩ B) d +
      S F 2 (by omega : 0 < 2) (consVec (qExp F) (consVec w1 B)) d +
      ∑ j : dIdx (qExp F) w1,
        (ChenDeltaZ F (qExp F : ℕ) (w1 : ℕ) j.1 : RatFunc.CompletionAtInfty F) *
          S F 2 (by omega : 0 < 2) (thakurExp (qExp F : ℕ) (w1 : ℕ) j) d +
      ∑ e' : (p2Wb F (by omega : 0 < 1) (single w1)).ι,
        (D1c F * (((p2Wb F (by omega : 0 < 1) (single w1)).f e' : ℤ) : RatFunc.CompletionAtInfty F)) *
          S F ((p2Wb F (by omega : 0 < 1) (single w1)).dep e' + 1)
            (by omega : 0 < (p2Wb F (by omega : 0 < 1) (single w1)).dep e' + 1)
            (consVec oneExp ((p2Wb F (by omega : 0 < 1) (single w1)).c e')) (d + 1)
      = 0 := by
  classical
  intro B d
  have h := cw_r1_pure_m1_all F w1 d
  rw [consVec_empty' ⟨(qExp F : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩ B]
  rw [consVec_empty' w1 B]
  exact h




/-!
# Step L3 (finish): Lemma 2.9 in consVec-normal ∃-form

The statements `lemma29Stmt`/`lemma_2_9` below are paper Lemma 2.9 (=(2.10)): for the
tuple `W = (w1 :: B)` of depth `k+1`, the level-`d` power sum of the merged head
`(q+w1) :: B` equals `0` up to an `a`-family (level `d`, `≤ (q)+W`, first entry
`< q+w1`) and a `b`-family of tuples `(1 :: t)` (`t ≤ (q−1)+W`) at level `d+1` — with
explicit witness families (depths, exponents, ℤ / `RatFunc F` coefficients) and the
`LePad` shape bounds.  `lemma_2_9_ge2` covers depth `≥ 2` (k ≥ 1, via `cw_r1_pure_cons`),
`lemma_2_9_m1` the depth-one case (k = 0, via `cw_r1_pure_cons0`).
-/

lemma intCast_ratFunc_completion (n : ℤ) :
    (((n : ℤ) : RatFunc F) : RatFunc.CompletionAtInfty F) = ((n : ℤ) : RatFunc.CompletionAtInfty F) := by
  change (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) ((n : ℤ) : RatFunc F)) =
    ((n : ℤ) : RatFunc.CompletionAtInfty F)
  exact map_intCast (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) n

lemma ratFunc_coe_mul (x y : RatFunc F) :
    ((x * y : RatFunc F) : RatFunc.CompletionAtInfty F) =
      (x : RatFunc.CompletionAtInfty F) * (y : RatFunc.CompletionAtInfty F) := by
  change (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (x * y)) =
    (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) x) *
      (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) y)
  exact map_mul (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) x y

lemma d1_b_coeff {m : ℕ} (hm : 0 < m) (W : Fin m → ℕ+) (e' : (p2Wb F hm W).ι) :
    ((D1rat F * (((p2Wb F hm W).f e' : ℤ) : RatFunc F) : RatFunc F) :
        RatFunc.CompletionAtInfty F) =
      D1c F * (((p2Wb F hm W).f e' : ℤ) : RatFunc.CompletionAtInfty F) := by
  calc
    ((D1rat F * (((p2Wb F hm W).f e' : ℤ) : RatFunc F) : RatFunc F) :
        RatFunc.CompletionAtInfty F)
        = (D1rat F : RatFunc.CompletionAtInfty F) *
            ((((p2Wb F hm W).f e' : ℤ) : RatFunc F) : RatFunc.CompletionAtInfty F) := by
          rw [ratFunc_coe_mul F (D1rat F) (((p2Wb F hm W).f e' : ℤ) : RatFunc F)]
    _ = D1c F * (((p2Wb F hm W).f e' : ℤ) : RatFunc.CompletionAtInfty F) := by
          rw [D1c_eq_D1rat F]
          rw [intCast_ratFunc_completion F ((p2Wb F hm W).f e')]




/-- The Lemma-2.9 statement (paper (2.10)) in consVec-normal ∃-form for the tuple
`W = (w1 :: B)` of depth `k+1 ≥ 1`: `S_d(q+w1, B)` plus an `a`-family (level `d`,
bounded by `(q)+W`, first entry `< q+w1`) and a `b`-family (level `d+1`, tuples
`(1 :: t)`, `t ≤ (q−1)+W`) sums to `0` at every level. -/
def lemma29Stmt (k : ℕ) (w1 : ℕ+) (B : Fin k → ℕ+) : Prop :=
  ∃ (ιa : Type) (_ : Fintype ιa) (depa : ιa → ℕ) (hdepa : ∀ i, 0 < depa i)
      (ca : ∀ i, Fin (depa i) → ℕ+) (aa : ιa → ℤ)
      (ιb : Type) (_ : Fintype ιb) (depb : ιb → ℕ) (hdepb : ∀ j, 0 < depb j)
      (cb : ∀ j, Fin (depb j) → ℕ+) (bb : ιb → RatFunc F),
    (∀ i, LePad (ca i) (single (qExp F)) (consVec w1 B) ∧
          ((ca i) ⟨0, hdepa i⟩ : ℕ) < (qExp F : ℕ) + (w1 : ℕ)) ∧
    (∀ j, LePad (cb j) (single (qMinusExp F)) (consVec w1 B)) ∧
    (∀ d : ℕ,
      S F (k + 1) (by omega : 0 < k + 1)
          (consVec ⟨(qExp F : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩ B) d +
      (∑ i : ιa, (((aa i : ℤ) : RatFunc.CompletionAtInfty F) *
          S F (depa i) (hdepa i) (ca i) d)) +
      (∑ j : ιb, (((bb j : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depb j + 1) (by omega : 0 < depb j + 1) (consVec oneExp (cb j)) (d + 1))) = 0)


-- Lemma 2.9 in consVec-normal ∃-form, depth k+1 >= 2 (k >= 1)
theorem lemma_2_9_ge2 {k : ℕ} (hk : 0 < k) (w1 : ℕ+) (B : Fin k → ℕ+) :
    lemma29Stmt F k w1 B := by
  classical
  let ιa : Type := PUnit.{1} ⊕ (Σ j : dIdx (qExp F) w1, (p2WpT F (dPn (qExp F) w1 j) hk B).ι)
  letI : Fintype ιa := by
    dsimp [ιa]
    infer_instance
  let depa : ιa → ℕ := fun i => match i with
    | Sum.inl _ => k + 2
    | Sum.inr p => (p2WpT F (dPn (qExp F) w1 p.1) hk B).dep p.2 + 1
  have hdepa : ∀ i, 0 < depa i := by
    intro i
    cases i with
    | inl u => dsimp [depa]; omega
    | inr p =>
        dsimp [depa]
        have hpos : 0 < (p2WpT F (dPn (qExp F) w1 p.1) hk B).dep p.2 :=
          (p2WpT F (dPn (qExp F) w1 p.1) hk B).hdep p.2
        omega
  let ca : ∀ i, Fin (depa i) → ℕ+ := fun i => match i with
    | Sum.inl _ => consVec (qExp F) (consVec w1 B)
    | Sum.inr p => consVec (dHead (qExp F) w1 p.1) ((p2WpT F (dPn (qExp F) w1 p.1) hk B).c p.2)
  let aa : ιa → ℤ := fun i => match i with
    | Sum.inl _ => 1
    | Sum.inr p => ChenDeltaZ F (qExp F : ℕ) (w1 : ℕ) p.1.1 * (p2WpT F (dPn (qExp F) w1 p.1) hk B).f p.2
  let ιb : Type := (p2Wb F (by omega : 0 < k + 1) (consVec w1 B)).ι
  letI : Fintype ιb := by dsimp [ιb]; infer_instance
  let depb : ιb → ℕ := fun j => (p2Wb F (by omega : 0 < k + 1) (consVec w1 B)).dep j
  have hdepb : ∀ j, 0 < depb j := by
    intro j
    exact (p2Wb F (by omega : 0 < k + 1) (consVec w1 B)).hdep j
  let cb : ∀ j, Fin (depb j) → ℕ+ := fun j => (p2Wb F (by omega : 0 < k + 1) (consVec w1 B)).c j
  let bb : ιb → RatFunc F := fun j =>
    D1rat F * (((p2Wb F (by omega : 0 < k + 1) (consVec w1 B)).f j : ℤ) : RatFunc F)
  refine ⟨ιa, inferInstance, depa, hdepa, ca, aa, ιb, inferInstance, depb, hdepb, cb, bb,
    ?_, ?_, ?_⟩
  · intro i
    cases i with
    | inl u =>
        constructor
        · dsimp [ca, depa]
          exact LePad_cons_q F (consVec w1 B)
        · dsimp [ca, depa]
          change (qExp F : ℕ) < (qExp F : ℕ) + (w1 : ℕ)
          have hpos : 0 < (w1 : ℕ) := w1.pos
          omega
    | inr p =>
        constructor
        · dsimp [ca, depa]
          exact LePad_cons_dHead (dHead (qExp F) w1 p.1) (dPn (qExp F) w1 p.1) (qExp F) w1
            ((p2WpT F (dPn (qExp F) w1 p.1) hk B).c p.2) B
            (by
              dsimp [dHead, dPn]
              have hi1 : 1 ≤ p.1.1 := (Finset.mem_Icc.mp p.1.2).1
              have hin : p.1.1 ≤ (qExp F : ℕ) + (w1 : ℕ) - 1 := (Finset.mem_Icc.mp p.1.2).2
              omega)
            ((p2WpT F (dPn (qExp F) w1 p.1) hk B).hle p.2)
        · dsimp [ca, depa]
          change (dHead (qExp F) w1 p.1 : ℕ) < (qExp F : ℕ) + (w1 : ℕ)
          dsimp [dHead]
          have hi1 : 1 ≤ p.1.1 := (Finset.mem_Icc.mp p.1.2).1
          have hq : 0 < (qExp F : ℕ) := (qExp F).pos
          omega
  · intro j
    dsimp [cb, depb]
    exact (p2Wb F (by omega : 0 < k + 1) (consVec w1 B)).hle j
  · intro d
    classical
    have hcw := cw_r1_pure_cons F hk w1 B d
    simp [ιa, ιb, depa, ca, aa, depb, cb, bb, d1_b_coeff,
      Fintype.sum_sum_type, Fintype.sum_sigma, Int.cast_one, one_mul] at hcw ⊢
    simpa [add_assoc] using hcw


-- k = 0 case: depth-one tuple (single w1), thakurExp Δ-outputs
theorem lemma_2_9_m1 (w1 : ℕ+) (B : Fin 0 → ℕ+) : lemma29Stmt F 0 w1 B := by
  classical
  let q : ℕ+ := qExp F
  let ιa : Type := PUnit.{1} ⊕ dIdx (qExp F) w1
  letI : Fintype ιa := by dsimp [ιa]; infer_instance
  let depa : ιa → ℕ := fun i => match i with
    | Sum.inl _ => 2
    | Sum.inr _ => 2
  have hdepa : ∀ i, 0 < depa i := by intro i; cases i <;> dsimp [depa] <;> omega
  let ca : ∀ i, Fin (depa i) → ℕ+ := fun i => match i with
    | Sum.inl _ => consVec (qExp F) (consVec w1 B)
    | Sum.inr j => thakurExp (qExp F : ℕ) (w1 : ℕ) j
  let aa : ιa → ℤ := fun i => match i with
    | Sum.inl _ => 1
    | Sum.inr j => ChenDeltaZ F (qExp F : ℕ) (w1 : ℕ) j.1
  let ιb : Type := (p2Wb F (by omega : 0 < 1) (single w1)).ι
  letI : Fintype ιb := by dsimp [ιb]; infer_instance
  let depb : ιb → ℕ := fun j => (p2Wb F (by omega : 0 < 1) (single w1)).dep j
  have hdepb : ∀ j, 0 < depb j := by
    intro j
    exact (p2Wb F (by omega : 0 < 1) (single w1)).hdep j
  let cb : ∀ j, Fin (depb j) → ℕ+ := fun j => (p2Wb F (by omega : 0 < 1) (single w1)).c j
  let bb : ιb → RatFunc F := fun j =>
    D1rat F * (((p2Wb F (by omega : 0 < 1) (single w1)).f j : ℤ) : RatFunc F)
  change ∃ (ιa : Type) (_ : Fintype ιa) (depa : ιa → ℕ) (hdepa : ∀ i, 0 < depa i)
      (ca : ∀ i, Fin (depa i) → ℕ+) (aa : ιa → ℤ)
      (ιb : Type) (_ : Fintype ιb) (depb : ιb → ℕ) (hdepb : ∀ j, 0 < depb j)
      (cb : ∀ j, Fin (depb j) → ℕ+) (bb : ιb → RatFunc F),
    (∀ i, LePad (ca i) (single (qExp F)) (consVec w1 B) ∧
          ((ca i) ⟨0, hdepa i⟩ : ℕ) < (qExp F : ℕ) + (w1 : ℕ)) ∧
    (∀ j, LePad (cb j) (single (qMinusExp F)) (consVec w1 B)) ∧
    (∀ d : ℕ,
      S F 1 (by omega : 0 < 1)
          (consVec ⟨(qExp F : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩ B) d +
      (∑ i : ιa, (((aa i : ℤ) : RatFunc.CompletionAtInfty F) *
          S F (depa i) (hdepa i) (ca i) d)) +
      (∑ j : ιb, (((bb j : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depb j + 1) (by omega : 0 < depb j + 1) (consVec oneExp (cb j)) (d + 1))) = 0)
  refine ⟨ιa, inferInstance, depa, hdepa, ca, aa, ιb, inferInstance, depb, hdepb, cb, bb,
    ?_, ?_, ?_⟩
  · intro i
    cases i with
    | inl u =>
        constructor
        · dsimp [ca, depa]
          exact LePad_cons_q F (consVec w1 B)
        · dsimp [ca, depa]
          change (qExp F : ℕ) < (qExp F : ℕ) + (w1 : ℕ)
          have hpos : 0 < (w1 : ℕ) := w1.pos
          omega
    | inr j =>
        constructor
        · dsimp [ca, depa]
          have hL := LePad_thakurExp_of_sum (qExp F) w1 j
          rw [← consVec_empty' w1 B] at hL
          exact hL
        · dsimp [ca, depa]
          change (qExp F : ℕ) + (w1 : ℕ) - j.1 < (qExp F : ℕ) + (w1 : ℕ)
          have hi1 : 1 ≤ j.1 := (Finset.mem_Icc.mp j.2).1
          have hq : 0 < (qExp F : ℕ) := (qExp F).pos
          omega
  · intro j
    dsimp [cb, depb]
    have hL := (p2Wb F (by omega : 0 < 1) (single w1)).hle j
    convert hL using 1
    exact consVec_empty' w1 B
  · intro d
    classical
    have hcw := cw_r1_pure_cons0 F w1 B d
    simp [ιa, ιb, depa, ca, aa, depb, cb, bb, d1_b_coeff, q,
      Fintype.sum_sum_type, Int.cast_one, one_mul] at hcw ⊢
    simpa [add_assoc] using hcw

/-- ★ Lemma 2.9 (paper (2.10)) in consVec-normal ∃-form, every depth `k+1 ≥ 1`. -/
theorem lemma_2_9 (k : ℕ) (w1 : ℕ+) (B : Fin k → ℕ+) : lemma29Stmt F k w1 B := by
  by_cases hk : k = 0
  · subst k
    exact lemma_2_9_m1 F w1 B
  · exact lemma_2_9_ge2 F (Nat.pos_of_ne_zero hk) w1 B




/-- ★ Lemma 2.9 at the ζ level (paper Remark 2.4 over (2.10)): the MZV of the merged
head `(q+w1) :: B` is a K-combination of the `a`-values (bounded by `(q)+W`, first
entry `< q+w1`) and the `(1 :: t)`-values (`t ≤ (q−1)+W`). -/
theorem lemma_2_9_zeta (k : ℕ) (w1 : ℕ+) (B : Fin k → ℕ+) :
  ∃ (ιa : Type) (_ : Fintype ιa) (depa : ιa → ℕ) (hdepa : ∀ i, 0 < depa i)
      (ca : ∀ i, Fin (depa i) → ℕ+) (aA : ιa → RatFunc F)
      (ιb : Type) (_ : Fintype ιb) (depb : ιb → ℕ) (hdepb : ∀ j, 0 < depb j)
      (cb : ∀ j, Fin (depb j) → ℕ+) (bB : ιb → RatFunc F),
    (∀ i, LePad (ca i) (single (qExp F)) (consVec w1 B) ∧
          ((ca i) ⟨0, hdepa i⟩ : ℕ) < (qExp F : ℕ) + (w1 : ℕ)) ∧
    (∀ j, LePad (cb j) (single (qMinusExp F)) (consVec w1 B)) ∧
    ζ_A F (consVec ⟨(qExp F : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩ B)
      + (∑ i : ιa, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (ca i)))
      + (∑ j : ιb, (((bB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (consVec oneExp (cb j)))) = 0 := by
  classical
  rcases lemma_2_9 F k w1 B with ⟨ιa, fina, depa, hdepa, ca, aa, ιb, finb, depb, hdepb, cb, bb, hleA, hleB, hid⟩
  let aA0 : ιa → RatFunc F := fun i => ((aa i : ℤ) : RatFunc F)
  let leading : Fin (k + 1) → ℕ+ :=
    consVec ⟨(qExp F : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩ B
  -- family A with the leading term prepended (internal, for the mixed bridge)
  let ιa' : Type := PUnit.{1} ⊕ ιa
  letI : Fintype ιa' := by dsimp [ιa']; infer_instance
  let depa' : ιa' → ℕ := fun i => match i with | Sum.inl _ => k + 1 | Sum.inr x => depa x
  have hdepa' : ∀ i, 0 < depa' i := by
    intro i
    cases i with
    | inl u => dsimp [depa']; exact Nat.succ_pos k
    | inr x => dsimp [depa']; exact hdepa x
  let ca' : ∀ i, Fin (depa' i) → ℕ+ := fun i => match i with
    | Sum.inl _ => leading
    | Sum.inr x => ca x
  let aA' : ιa' → RatFunc F := fun i => match i with
    | Sum.inl _ => 1
    | Sum.inr x => aA0 x
  let depB : ιb → ℕ := fun j => depb j + 1
  have hdepB : ∀ j, 0 < depB j := by intro j; dsimp [depB]; exact Nat.succ_pos (depb j)
  let cB : ∀ j, Fin (depB j) → ℕ+ := fun j => consVec oneExp (cb j)
  have hrel : ∀ d : ℕ,
      (∑ i : ιa', (((aA' i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depa' i) (hdepa' i) (ca' i) d)) +
      (∑ j : ιb, (((bb j : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depB j) (hdepB j) (cB j) (d + 1))) = 0 := by
    intro d
    have hh := hid d
    rw [Fintype.sum_sum_type]
    simp [depa', ca', aA', aA0, leading, depB, cB, intCast_ratFunc_completion F,
      completion_coe_one, Int.cast_one, one_mul]
    simpa [add_assoc] using hh
  have hbr := zeta_mixed_bridge F
      (depA := depa') (hdepA := hdepa') (cA := ca') (aA := aA')
      (depB := depB) (hdepB := hdepB) (cB := cB) (aB := bb)
      (h0B := fun j => by
        dsimp [depB, cB]
        have hd : 0 < depb j := hdepb j
        exact S_zero_of_depth_ge_two F (by omega : 0 < depb j + 1) (by omega : 1 < depb j + 1)
          (consVec oneExp (cb j)))
      hrel
  refine ⟨ιa, inferInstance, depa, hdepa, ca, aA0, ιb, inferInstance, depb, hdepb, cb, bb, ?hleA2, ?hleB2, ?hzeta⟩
  · intro i
    exact hleA i
  · intro j
    exact hleB j
  · -- hzeta : ζ(leading) + Σ (aA0:K∞)·ζ(ca) + Σ (bb:K∞)·ζ(1::cb) = 0
    -- hbr : Σ_{ιa'} (aA':K∞) ζ(ca') + Σ_{ιb}(bb:K∞) ζ(cB) = 0
    rw [Fintype.sum_sum_type] at hbr
    simp [depa', ca', aA', aA0, leading, depB, cB, intCast_ratFunc_completion F,
      completion_coe_one, Int.cast_one, one_mul] at hbr ⊢
    simpa [add_assoc] using hbr

end ZagierHoffmanPositiveChar
