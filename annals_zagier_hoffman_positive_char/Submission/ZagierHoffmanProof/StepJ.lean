import Submission.ZagierHoffmanProof.StepI

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Step J: Data cons steps and the mutual induction for the depth-1-left families

Proves P1cD / P2cD (the cons steps of `P1oneD`/`P2oneD` at arbitrary depth k) and the
mutual induction giving `P1oneD`/`P2oneD` at every positive depth.  `P1oneD k`/`P2oneD k`
are the Part-1 (paper (2.5)) and Part-2 (paper (2.6)) statements for products of a
depth-one tuple with a depth-`k` tuple, in data-witness form (StepI).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Δ-index of the depth-(1,k+1) cons step: `1 ≤ i ≤ v+w1−1`. -/
abbrev dIdx (v w1 : ℕ+) := {i : ℕ // i ∈ Finset.Icc 1 ((v : ℕ) + (w1 : ℕ) - 1)}

/-- The Δ-value `⟨i.1, 1 ≤ i.1⟩` (a depth-one tuple value). -/
noncomputable def dPn (v w1 : ℕ+) (i : dIdx v w1) : ℕ+ :=
  ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩

/-- The Δ-output head `v+w1−i`. -/
noncomputable def dHead (v w1 : ℕ+) (i : dIdx v w1) : ℕ+ :=
  ⟨(v : ℕ) + (w1 : ℕ) - i.1, by
    have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
    have hin : i.1 ≤ (v : ℕ) + (w1 : ℕ) - 1 := (Finset.mem_Icc.mp i.2).2
    omega⟩

/-- The pure merged head `v+w1`. -/
noncomputable def dMerge (v w1 : ℕ+) : ℕ+ :=
  ⟨(v : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos v) (w1 : ℕ)⟩

/-- Extract the Part-2 data witness for `(v, W)` from the family hypothesis. -/
noncomputable def p2w {k : ℕ} (hk : 0 < k) (hP2 : P2oneD F k hk) (v : ℕ+) (W : Fin k → ℕ+) :
    P2Data F 1 k (by omega : 0 < 1) hk (single v) W :=
  Classical.choice (hP2 v W)

/-- Prefix sums of the zero-padded pointwise sum split as sums of the parts. -/
lemma psumSeq_tupPadSum {r k : ℕ} (a : Fin r → ℕ+) (b : Fin k → ℕ+) (m : ℕ) :
    psumSeq (tupPadSum a b) m = psum a m + psum b m := by
  classical
  induction m with
  | zero => simp [psumSeq, psum]
  | succ m ih =>
    rw [psumSeq_range_succ]
    rw [ih]
    rw [psum_succ a m, psum_succ b m]
    have ht : tupPadSum a b m = pad0 a m + pad0 b m := rfl
    rw [ht]
    omega

/-- Prepend the same head to a LePad pair: `x::c2 ≤ a + (x::b)` from `c2 ≤ a + b`. -/
lemma LePad_cons_cons {L r k : ℕ} (x : ℕ+) (c2 : Fin L → ℕ+) (a : Fin r → ℕ+) (b : Fin k → ℕ+)
    (h : LePad c2 a b) : LePad (consVec x c2) a (consVec x b) := by
  classical
  constructor
  · rw [weight_consVec, weight_consVec, h.1]
    omega
  · intro m
    by_cases hm0 : m = 0
    · subst m
      rw [psum_zero]
      simp [psumSeq]
    · rcases m with _ | n
      · omega
      · rw [psum_consVec]
        have hpre := h.2 n
        have hpre' := psumSeq_tupPadSum a b n
        rw [hpre'] at hpre
        have hmono : psum a n ≤ psum a (n + 1) := psum_mono a (Nat.le_succ n)
        have htg := psumSeq_tupPadSum a (consVec x b) (n + 1)
        rw [htg]
        rw [psum_consVec x b n]
        omega

/-- The pure merged term `(⟨v+w1⟩ :: W) ≤ (v) + (w1 :: W)` (Data-cons pure output). -/
lemma LePad_merge_cons {k : ℕ} (v w1 : ℕ+) (W : Fin k → ℕ+) :
    LePad (consVec ⟨(v : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos v) (w1 : ℕ)⟩ W)
      (single v) (consVec w1 W) := by
  classical
  let m : ℕ+ := ⟨(v : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos v) (w1 : ℕ)⟩
  change LePad (consVec m W) (single v) (consVec w1 W)
  constructor
  · rw [weight_consVec, weight_single, weight_consVec]
    dsimp [m]
    omega
  · intro n0
    by_cases hm0 : n0 = 0
    · subst n0
      rw [psum_zero]
      simp [psumSeq]
    · rcases n0 with _ | n
      · omega
      · rw [psum_consVec]
        have ht : psumSeq (tupPadSum (single v) (consVec w1 W)) (n + 1) =
            (v : ℕ) + (w1 : ℕ) + psumSeq (pad0 W) n := by
          rw [psumSeq_single_cons]
          simp
        rw [ht]
        dsimp [m]
        change (v : ℕ) + (w1 : ℕ) + psum W n ≤
          (v : ℕ) + (w1 : ℕ) + psumSeq (pad0 W) n
        have hc : psum W n = psumSeq (pad0 W) n := rfl
        omega

/-- The prefix-sum order is symmetric in the two argument tuples. -/
lemma LePad_swap {L r k : ℕ} (c : Fin L → ℕ+) (a : Fin r → ℕ+) (b : Fin k → ℕ+) :
    LePad c a b ↔ LePad c b a := by
  constructor <;> intro h
  · constructor
    · rw [h.1]
      omega
    · intro m
      have hpre := h.2 m
      have htg := psumSeq_tupPadSum a b m
      have htg2 := psumSeq_tupPadSum b a m
      rw [htg] at hpre
      rw [htg2]
      omega
  · constructor
    · rw [h.1]
      omega
    · intro m
      have hpre := h.2 m
      have htg := psumSeq_tupPadSum a b m
      have htg2 := psumSeq_tupPadSum b a m
      rw [htg2] at hpre
      rw [htg]
      omega

/-- `(x :: y :: C) ≤ (x) + (y :: C)` (pure merge of the cons level identity). -/
lemma LePad_double_cons {k : ℕ} (x y : ℕ+) (C : Fin k → ℕ+) :
    LePad (consVec x (consVec y C)) (single x) (consVec y C) := by
  classical
  constructor
  · rw [weight_consVec, weight_consVec, weight_single]
  · intro m
    by_cases hm0 : m = 0
    · subst m
      rw [psum_zero]
      simp [psumSeq]
    · rcases m with _ | n
      · omega
      · rw [psum_consVec]
        have htg := psumSeq_tupPadSum (single x) (consVec y C) (n + 1)
        rw [htg]
        rw [psum_single_of_pos x (by omega : 0 < n + 1)]
        have hmono : psum (consVec y C) n ≤ psum (consVec y C) (n + 1) :=
          psum_mono (consVec y C) (Nat.le_succ n)
        omega

/-- ★ Part-1 cons step at depth k: `P1oneD(k)` gives `P1oneD(k+1)` (paper (2.2) family). -/
theorem p1cD {k : ℕ} (hk : 0 < k) (hP2 : P2oneD F k hk) (v w1 : ℕ+) (W : Fin k → ℕ+) :
    Nonempty (P1Data F 1 (k + 1) (by omega : 0 < 1) (by omega : 0 < k + 1)
      (single v) (consVec w1 W)) := by
  classical
  let w2 : ∀ i : dIdx v w1, P2Data F 1 k (by omega : 0 < 1) hk (single (dPn v w1 i)) W :=
    fun i => p2w F hk hP2 (dPn v w1 i) W
  letI : ∀ i : dIdx v w1, Fintype ((w2 i).ι) := fun i => (w2 i).fin
  let ι0 : Type := PUnit.{1} ⊕ (Σ i : dIdx v w1, (w2 i).ι)
  let dep0 : ι0 → ℕ := fun a => match a with
    | Sum.inl _ => k + 1
    | Sum.inr p => (w2 p.1).dep p.2 + 1
  let hdep0 : ∀ a : ι0, 0 < dep0 a := by
    intro a
    cases a with
    | inl u => dsimp [dep0]; omega
    | inr p => dsimp [dep0]; have hp := (w2 p.1).hdep p.2; omega
  let f0 : ι0 → ℤ := fun a => match a with
    | Sum.inl _ => (1 : ℤ)
    | Sum.inr p => ChenDeltaZ F (v : ℕ) (w1 : ℕ) p.1.1 * (w2 p.1).f p.2
  let c0 : ∀ a : ι0, Fin (dep0 a) → ℕ+ := fun a => match a with
    | Sum.inl _ => consVec (dMerge v w1) W
    | Sum.inr p => consVec (dHead v w1 p.1) ((w2 p.1).c p.2)
  have hid0 : ∀ d : ℕ,
      S F 1 (by omega : 0 < 1) (single v) d * S F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) d =
      ∑ a : ι0, ((f0 a : ℤ) : RatFunc.CompletionAtInfty F) * S F (dep0 a) (hdep0 a) (c0 a) d := by
    intro d
    let K := RatFunc.CompletionAtInfty F
    let G : ι0 → K := fun a => ((f0 a : ℤ) : K) * S F (dep0 a) (hdep0 a) (c0 a) d
    have hG1 : ∀ i : dIdx v w1,
        (ChenDeltaZ F (v : ℕ) (w1 : ℕ) i.1 : K) *
          (P F d (dHead v w1 i) *
            (S_lt F 1 (by omega : 0 < 1) (single (dPn v w1 i)) d * S_lt F k hk W d)) =
        ∑ e : (w2 i).ι, G (Sum.inr ⟨i, e⟩) := by
      intro i
      have hper' : (ChenDeltaZ F (v : ℕ) (w1 : ℕ) i.1 : K) *
            (P F d (dHead v w1 i) *
              (S_lt F 1 (by omega : 0 < 1) (single (dPn v w1 i)) d * S_lt F k hk W d)) =
          ∑ e : (w2 i).ι,
            ((ChenDeltaZ F (v : ℕ) (w1 : ℕ) i.1 * (w2 i).f e : ℤ) : K) *
            S F ((w2 i).dep e + 1) (by omega) (consVec (dHead v w1 i) ((w2 i).c e)) d := by
        let Δ : ℤ := ChenDeltaZ F (v : ℕ) (w1 : ℕ) i.1
        calc
          (Δ : K) * (P F d (dHead v w1 i) *
              (S_lt F 1 (by omega : 0 < 1) (single (dPn v w1 i)) d * S_lt F k hk W d))
              = (Δ : K) * (P F d (dHead v w1 i) * (∑ e : (w2 i).ι,
                  (((w2 i).f e : ℤ) : K) * S_lt F ((w2 i).dep e) ((w2 i).hdep e) ((w2 i).c e) d)) := by
                exact congrArg (fun q : K => (Δ : K) * (P F d (dHead v w1 i) * q)) ((w2 i).hid d)
          _ = (Δ : K) * (∑ e : (w2 i).ι,
                (((w2 i).f e : ℤ) : K) *
                  (P F d (dHead v w1 i) * S_lt F ((w2 i).dep e) ((w2 i).hdep e) ((w2 i).c e) d)) := by
                have hd1 : P F d (dHead v w1 i) * (∑ e : (w2 i).ι,
                    (((w2 i).f e : ℤ) : K) * S_lt F ((w2 i).dep e) ((w2 i).hdep e) ((w2 i).c e) d) =
                    ∑ e : (w2 i).ι,
                    (((w2 i).f e : ℤ) : K) *
                      (P F d (dHead v w1 i) * S_lt F ((w2 i).dep e) ((w2 i).hdep e) ((w2 i).c e) d) := by
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro e he
                      ring
                exact congrArg (fun q : K => (Δ : K) * q) hd1
          _ = ∑ e : (w2 i).ι,
                ((Δ * (w2 i).f e : ℤ) : K) *
                  (P F d (dHead v w1 i) * S_lt F ((w2 i).dep e) ((w2 i).hdep e) ((w2 i).c e) d) := by
                have hd2 : (Δ : K) * (∑ e : (w2 i).ι,
                    (((w2 i).f e : ℤ) : K) *
                      (P F d (dHead v w1 i) * S_lt F ((w2 i).dep e) ((w2 i).hdep e) ((w2 i).c e) d)) =
                    ∑ e : (w2 i).ι,
                    ((Δ * (w2 i).f e : ℤ) : K) *
                      (P F d (dHead v w1 i) * S_lt F ((w2 i).dep e) ((w2 i).hdep e) ((w2 i).c e) d) := by
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro e he
                      rw [Int.cast_mul]
                      ring
                exact hd2
          _ = ∑ e : (w2 i).ι,
                ((Δ * (w2 i).f e : ℤ) : K) *
                  S F ((w2 i).dep e + 1) (by omega) (consVec (dHead v w1 i) ((w2 i).c e)) d := by
                apply Finset.sum_congr rfl
                intro e he
                rw [S_prepend F d (dHead v w1 i) ((w2 i).hdep e) ((w2 i).c e)]
      simpa [G, f0, dep0, c0, hdep0] using hper'
    change S F 1 (by omega : 0 < 1) (single v) d * S F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) d =
      ∑ a : ι0, G a
    rw [show S F 1 (by omega : 0 < 1) (single v) d * S F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) d =
        S F (k + 1) (by omega : 0 < k + 1) (consVec (dMerge v w1) W) d +
        ∑ i : dIdx v w1,
          (ChenDeltaZ F (v : ℕ) (w1 : ℕ) i.1 : K) *
          (P F d (dHead v w1 i) *
            (S_lt F 1 (by omega : 0 < 1) (single (dPn v w1 i)) d * S_lt F k hk W d))
        by simpa [dHead, dPn, dMerge] using p1cons_level F hk v w1 W d]
    have hGsplit : (∑ a : ι0, G a) =
        G (Sum.inl PUnit.unit) + ∑ p : Σ i : dIdx v w1, (w2 i).ι, G (Sum.inr p) := by
      have hsum := Fintype.sum_sum_type (f := G)
      rw [hsum]
      simp
    rw [hGsplit]
    rw [Fintype.sum_sigma]
    congr 1
    · dsimp [G, f0, dep0, c0, hdep0]
      simp
    · apply Finset.sum_congr rfl
      intro i hi
      exact hG1 i
  have hle0 : ∀ a : ι0, LePad (c0 a) (single v) (consVec w1 W) := by
    intro a
    cases a with
    | inl u =>
      simpa [c0, dMerge] using LePad_merge_cons v w1 W
    | inr p =>
      refine LePad_cons_k v w1 (dHead v w1 p.1) (dPn v w1 p.1) W ((w2 p.1).c p.2) ?_ ?_ ?_ ?_
      · have hw := ((w2 p.1).hle p.2).1
        have hws := weight_single (dPn v w1 p.1)
        rw [hws] at hw
        exact hw
      · exact ((w2 p.1).hle p.2).2
      · have hval : (dHead v w1 p.1 : ℕ) = (v : ℕ) + (w1 : ℕ) - p.1.1 := rfl
        rw [hval]
        omega
      · have hval : (dHead v w1 p.1 : ℕ) = (v : ℕ) + (w1 : ℕ) - p.1.1 := rfl
        have hvp : (dPn v w1 p.1 : ℕ) = p.1.1 := rfl
        rw [hval, hvp]
        have hle : p.1.1 ≤ (v : ℕ) + (w1 : ℕ) := by
          have hin : p.1.1 ≤ (v : ℕ) + (w1 : ℕ) - 1 := (Finset.mem_Icc.mp p.1.2).2
          have hy : 1 ≤ (v : ℕ) := PNat.pos v
          omega
        exact Nat.sub_add_cancel hle
  have hbd0 : ∀ a : ι0, dep0 a ≤ 1 + (k + 1) := by
    intro a
    cases a with
    | inl u =>
      dsimp [dep0]
      omega
    | inr p =>
      dsimp [dep0]
      have hb := (w2 p.1).hbd p.2
      omega
  let D : P1Data F 1 (k + 1) (by omega : 0 < 1) (by omega : 0 < k + 1) (single v) (consVec w1 W) := {
    ι := ι0
    fin := inferInstance
    dep := dep0
    hdep := hdep0
    f := f0
    c := c0
    hid := hid0
    hle := hle0
    hbd := hbd0 }
  exact ⟨D⟩


theorem p2cD {k : ℕ} (hk : 0 < k) (hP2 : P2oneD F k hk) (v w1 : ℕ+) (W : Fin k → ℕ+) :
    Nonempty (P2Data F 1 (k + 1) (by omega : 0 < 1) (by omega : 0 < k + 1)
      (single v) (consVec w1 W)) := by
  classical
  let wv : P2Data F 1 k (by omega : 0 < 1) hk (single v) W := p2w F hk hP2 v W
  let D1 : P1Data F 1 (k + 1) (by omega : 0 < 1) (by omega : 0 < k + 1) (single v) (consVec w1 W) :=
    Classical.choice (p1cD F hk hP2 v w1 W)
  letI : Fintype wv.ι := wv.fin
  letI : Fintype D1.ι := D1.fin
  let ι0 : Type := PUnit.{1} ⊕ wv.ι ⊕ D1.ι
  let dep0 : ι0 → ℕ := fun a => match a with
    | Sum.inl _ => k + 2
    | Sum.inr (Sum.inl e) => wv.dep e + 1
    | Sum.inr (Sum.inr a) => D1.dep a
  let hdep0 : ∀ a : ι0, 0 < dep0 a := by
    intro a
    cases a with
    | inl u => dsimp [dep0]; omega
    | inr p => cases p with
      | inl e => dsimp [dep0]; have hp := wv.hdep e; omega
      | inr x => dsimp [dep0]; have hp := D1.hdep x; omega
  let f0 : ι0 → ℤ := fun a => match a with
    | Sum.inl _ => (1 : ℤ)
    | Sum.inr (Sum.inl e) => wv.f e
    | Sum.inr (Sum.inr x) => D1.f x
  let c0 : ∀ a : ι0, Fin (dep0 a) → ℕ+ := fun a => match a with
    | Sum.inl _ => consVec v (consVec w1 W)
    | Sum.inr (Sum.inl e) => consVec w1 (wv.c e)
    | Sum.inr (Sum.inr x) => D1.c x
  have hid0 : ∀ d : ℕ,
      S_lt F 1 (by omega : 0 < 1) (single v) d * S_lt F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) d =
      ∑ a : ι0, ((f0 a : ℤ) : RatFunc.CompletionAtInfty F) * S_lt F (dep0 a) (hdep0 a) (c0 a) d := by
    intro d
    let K := RatFunc.CompletionAtInfty F
    let G : ι0 → K := fun a => ((f0 a : ℤ) : K) * S_lt F (dep0 a) (hdep0 a) (c0 a) d
    -- B group:
    have hB : (∑ i ∈ Finset.range d,
        S F 1 (by omega : 0 < 1) (single w1) i *
          (S_lt F 1 (by omega : 0 < 1) (single v) i * S_lt F k hk W i)) =
        ∑ e : wv.ι,
          ((wv.f e : ℤ) : K) *
          S_lt F (wv.dep e + 1) (by omega) (consVec w1 (wv.c e)) d := by
      calc
        (∑ i ∈ Finset.range d,
            S F 1 (by omega : 0 < 1) (single w1) i *
              (S_lt F 1 (by omega : 0 < 1) (single v) i * S_lt F k hk W i))
            = ∑ i ∈ Finset.range d,
                P F i w1 * (S_lt F 1 (by omega : 0 < 1) (single v) i * S_lt F k hk W i) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [S_one_eq_P F i (by omega) (single w1)]
                  simp [single]
        _ = ∑ i ∈ Finset.range d,
              P F i w1 * (∑ e : wv.ι,
                ((wv.f e : ℤ) : K) * S_lt F (wv.dep e) (wv.hdep e) (wv.c e) i) := by
              apply Finset.sum_congr rfl
              intro i hi
              congr 1
              exact (wv.hid i)
        _ = ∑ i ∈ Finset.range d, ∑ e : wv.ι,
              ((wv.f e : ℤ) : K) *
                (P F i w1 * S_lt F (wv.dep e) (wv.hdep e) (wv.c e) i) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro e he
              ring
        _ = ∑ e : wv.ι,
              ((wv.f e : ℤ) : K) *
                (∑ i ∈ Finset.range d,
                  S F (wv.dep e + 1) (by omega) (consVec w1 (wv.c e)) i) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro e he
              calc
                (∑ i ∈ Finset.range d,
                    ((wv.f e : ℤ) : K) *
                      (P F i w1 * S_lt F (wv.dep e) (wv.hdep e) (wv.c e) i))
                    = ((wv.f e : ℤ) : K) *
                        (∑ i ∈ Finset.range d,
                          P F i w1 * S_lt F (wv.dep e) (wv.hdep e) (wv.c e) i) := by
                      exact (Finset.mul_sum (s := Finset.range d)
                        (a := ((wv.f e : ℤ) : K))
                        (f := fun i : ℕ => P F i w1 * S_lt F (wv.dep e) (wv.hdep e) (wv.c e) i)).symm
                _ = ((wv.f e : ℤ) : K) *
                      (∑ i ∈ Finset.range d,
                        S F (wv.dep e + 1) (by omega) (consVec w1 (wv.c e)) i) := by
                      congr 1
                      apply Finset.sum_congr rfl
                      intro i hi
                      rw [S_prepend F i w1 (wv.hdep e) (wv.c e)]
        _ = ∑ e : wv.ι,
              ((wv.f e : ℤ) : K) * S_lt F (wv.dep e + 1) (by omega) (consVec w1 (wv.c e)) d := by
              apply Finset.sum_congr rfl
              intro e he
              rw [← S_lt_eq_sum_levels F (wv.dep e + 1) (by omega) (consVec w1 (wv.c e)) d]
    -- C group:
    have hC : (∑ i ∈ Finset.range d,
        S F 1 (by omega : 0 < 1) (single v) i * S F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) i) =
        ∑ x : D1.ι,
          ((D1.f x : ℤ) : K) * S_lt F (D1.dep x) (D1.hdep x) (D1.c x) d := by
      calc
        (∑ i ∈ Finset.range d,
            S F 1 (by omega : 0 < 1) (single v) i * S F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) i)
            = ∑ i ∈ Finset.range d,
                ∑ x : D1.ι,
                  ((D1.f x : ℤ) : K) * S F (D1.dep x) (D1.hdep x) (D1.c x) i := by
                apply Finset.sum_congr rfl
                intro i hi
                exact (D1.hid i)
        _ = ∑ x : D1.ι,
              ((D1.f x : ℤ) : K) *
                (∑ i ∈ Finset.range d, S F (D1.dep x) (D1.hdep x) (D1.c x) i) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro x hx
              exact (Finset.mul_sum (s := Finset.range d)
                (a := ((D1.f x : ℤ) : K))
                (f := fun i : ℕ => S F (D1.dep x) (D1.hdep x) (D1.c x) i)).symm
        _ = ∑ x : D1.ι,
              ((D1.f x : ℤ) : K) * S_lt F (D1.dep x) (D1.hdep x) (D1.c x) d := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [← S_lt_eq_sum_levels F (D1.dep x) (D1.hdep x) (D1.c x) d]
    change S_lt F 1 (by omega : 0 < 1) (single v) d * S_lt F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) d =
      ∑ a : ι0, G a
    rw [show S_lt F 1 (by omega : 0 < 1) (single v) d * S_lt F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) d =
        S_lt F (k + 2) (by omega : 0 < k + 2) (consVec v (consVec w1 W)) d +
        (∑ i ∈ Finset.range d,
          S F 1 (by omega : 0 < 1) (single w1) i *
            (S_lt F 1 (by omega : 0 < 1) (single v) i * S_lt F k hk W i)) +
        (∑ i ∈ Finset.range d,
          S F 1 (by omega : 0 < 1) (single v) i * S F (k + 1) (by omega : 0 < k + 1) (consVec w1 W) i)
        by exact p2cons_level F hk v w1 W d]
    rw [hB, hC]
    -- now split the carrier sum
    have hGsplit : (∑ a : ι0, G a) =
        G (Sum.inl PUnit.unit) + ∑ p : wv.ι ⊕ D1.ι, G (Sum.inr p) := by
      have hsum := Fintype.sum_sum_type (f := G)
      rw [hsum]
      simp
    have hGsplit2 : (∑ p : wv.ι ⊕ D1.ι, G (Sum.inr p)) =
        (∑ e : wv.ι, G (Sum.inr (Sum.inl e))) +
          ∑ x : D1.ι, G (Sum.inr (Sum.inr x)) := by
      have hsum := Fintype.sum_sum_type
        (f := fun p : wv.ι ⊕ D1.ι => G (Sum.inr p))
      rw [hsum]
    rw [hGsplit, hGsplit2]
    -- goal: A + Bcar + Ccar = G(inl) + (Bcar' + Ccar') where G(inl)=A, etc.
    simp [G, f0, dep0, c0]
    ac_rfl
  have hle0 : ∀ a : ι0, LePad (c0 a) (single v) (consVec w1 W) := by
    intro a
    cases a with
    | inl u =>
      simpa [c0] using LePad_double_cons v w1 W
    | inr p => cases p with
      | inl e =>
        simpa [c0, dep0, hdep0] using LePad_cons_cons w1 (wv.c e) (single v) W (wv.hle e)
      | inr x =>
        simpa [c0, dep0, hdep0] using D1.hle x
  have hbd0 : ∀ a : ι0, dep0 a ≤ 1 + (k + 1) := by
    intro a
    cases a with
    | inl u =>
      dsimp [dep0]
      omega
    | inr p => cases p with
      | inl e =>
        dsimp [dep0]
        have hb := wv.hbd e
        omega
      | inr x =>
        dsimp [dep0]
        have hb := D1.hbd x
        omega
  let D : P2Data F 1 (k + 1) (by omega : 0 < 1) (by omega : 0 < k + 1) (single v) (consVec w1 W) := {
    ι := ι0
    fin := inferInstance
    dep := dep0
    hdep := hdep0
    f := f0
    c := c0
    hid := hid0
    hle := hle0
    hbd := hbd0 }
  exact ⟨D⟩


/-- ★ Mutual induction of the data families: both hold at every positive depth. -/
theorem p1p2D_all : ∀ (k : ℕ) (hk : 0 < k), P1oneD F k hk ∧ P2oneD F k hk := by
  classical
  intro k
  induction k with
  | zero => intro hk; omega
  | succ n ih =>
    intro hk
    by_cases hn : n = 0
    · subst n
      exact ⟨p1oneD_one F, p2oneD_one F⟩
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hP1n := (ih hnpos).1
      have hP2n := (ih hnpos).2
      constructor
      · intro v W'
        have hdec := fin_succ_eq_consVec (m := n) W'
        rw [hdec]
        exact p1cD F hnpos hP2n v (W' ⟨0, by omega⟩) (fun j : Fin n => W' ⟨j.1 + 1, by omega⟩)
      · intro v W'
        have hdec := fin_succ_eq_consVec (m := n) W'
        rw [hdec]
        exact p2cD F hnpos hP2n v (W' ⟨0, by omega⟩) (fun j : Fin n => W' ⟨j.1 + 1, by omega⟩)

/-- Forget the data witness: Part 1 of Prop 2.1 (depth-1-left) from `P1oneD`. -/
theorem p1oneD_imp (k : ℕ) (hk : 0 < k) : P1oneD F k hk → P1one F k hk := by
  intro h v W
  rcases h v W with ⟨D⟩
  exact p1w_of_data F (by omega : 0 < 1) hk (single v) W D

/-- Forget the data witness: Part 2 of Prop 2.1 (depth-1-left) from `P2oneD`. -/
theorem p2oneD_imp (k : ℕ) (hk : 0 < k) : P2oneD F k hk → P2one F k hk := by
  intro h v W
  rcases h v W with ⟨D⟩
  exact p2w_of_data F (by omega : 0 < 1) hk (single v) W D

/-- ★ Both depth-1-left families of Prop 2.1 hold at every positive depth. -/
theorem p1p2_one_all : ∀ (k : ℕ) (hk : 0 < k), P1one F k hk ∧ P2one F k hk := by
  intro k hk
  have h := p1p2D_all F k hk
  exact ⟨p1oneD_imp F k hk h.1, p2oneD_imp F k hk h.2⟩



/-- Symmetric depth-1-right Part-1 family from the depth-1-left one. -/
theorem p1one_sym {k : ℕ} (hk : 0 < k) (h : P1one F k hk) :
    ∀ (W : Fin k → ℕ+) (v : ℕ+), P1W F k 1 hk (by omega : 0 < 1) W (single v) := by
  classical
  intro W v
  rcases h v W with ⟨ι, fin, dep, hdep, f, c, hid, hle, hbd⟩
  refine ⟨ι, fin, dep, hdep, f, c, ?hid, ?hle, ?hbd⟩
  · intro d
    calc
      S F k hk W d * S F 1 (by omega : 0 < 1) (single v) d
          = S F 1 (by omega : 0 < 1) (single v) d * S F k hk W d := by rw [mul_comm]
      _ = ∑ i, ((f i : ℤ) : RatFunc.CompletionAtInfty F) *
            S F (dep i) (hdep i) (c i) d := hid d
  · intro i
    exact (LePad_swap (c i) (single v) W).mp (hle i)
  · intro i
    have hb := hbd i
    omega

/-- Symmetric depth-1-right Part-2 family from the depth-1-left one. -/
theorem p2one_sym {k : ℕ} (hk : 0 < k) (h : P2one F k hk) :
    ∀ (W : Fin k → ℕ+) (v : ℕ+), P2W F k 1 hk (by omega : 0 < 1) W (single v) := by
  classical
  intro W v
  rcases h v W with ⟨ι, fin, dep, hdep, f, c, hid, hle, hbd⟩
  refine ⟨ι, fin, dep, hdep, f, c, ?hid, ?hle, ?hbd⟩
  · intro d
    calc
      S_lt F k hk W d * S_lt F 1 (by omega : 0 < 1) (single v) d
          = S_lt F 1 (by omega : 0 < 1) (single v) d * S_lt F k hk W d := by rw [mul_comm]
      _ = ∑ i, ((f i : ℤ) : RatFunc.CompletionAtInfty F) *
            S_lt F (dep i) (hdep i) (c i) d := hid d
  · intro i
    exact (LePad_swap (c i) (single v) W).mp (hle i)
  · intro i
    have hb := hbd i
    omega



/-- Prop 2.1(1): depth-`k` by depth-1 products (both orders), every positive depth. -/
theorem p1_any_one {k : ℕ} (hk : 0 < k) (W : Fin k → ℕ+) (v : ℕ+) :
    P1W F k 1 hk (by omega : 0 < 1) W (single v) :=
  p1one_sym F hk (p1p2_one_all F k hk).1 W v

/-- Prop 2.1(2): depth-`k` by depth-1 `S_<d` products (both orders), every depth. -/
theorem p2_any_one {k : ℕ} (hk : 0 < k) (W : Fin k → ℕ+) (v : ℕ+) :
    P2W F k 1 hk (by omega : 0 < 1) W (single v) :=
  p2one_sym F hk (p1p2_one_all F k hk).2 W v

end ZagierHoffmanPositiveChar
