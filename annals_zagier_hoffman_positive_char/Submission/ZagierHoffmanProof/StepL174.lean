import Submission.ZagierHoffmanProof.StepL173
import Submission.ZagierHoffmanProof.StepL44
import Submission.ZagierHoffmanProof.StepL43
import Submission.ZagierHoffmanProof.StepL29

set_option autoImplicit false
set_option maxHeartbeats 40000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L174: ★★ the CASE-2 (Prop 2.13) AMBIENT STEPS + the fiber TEMPLATE PROFILE

Route (C) needs, for every member family of the CASE-2 chain `maink_case2_j`
(StepL147, `prop213_step1`) and of the all-`q` leaf `maink_case2_qqq` (StepL148), the
ambient measure descent `ambNu Λ m < ambNu Λ s` at every ambient level `Λ ≥ k`.

The CASE-2 members (all of weight `w = weight k s`, `s` of depth `k`) split as:
  • type-2 (StepL44): a STRICT prefix-`k` drop ⇒ (as in StepL165's type-2) the member
    has `depth > k`, so the DEPTH component of `ambNu` decides;
  • the all-`q` leaf (StepL148): the same, via its `hdrop`;
  • type-3 (StepL44): only `psum m k ≤ psum s k` and `InitLt q s m` — the ambient step
    needs the paper's Prop-2.13 conclusion `depth(u) ≥ depth(s) = k`.  That depth bound
    is PROVED here: the paper's route is
    "fiber ≤ (q^{k−j−1}, q−1) + Remark (equal weights + prefix dominance ⇒ depth ≥)",
    and the missing sharpened prefix bound is the TEMPLATE PROFILE
      `psum (fiber_n) m ≤ psum ((q,…,q,q−1)) m`
    (the committed `BCq_fiber_prefix_X` bounds the fiber by the CONSTANT `(k−j)q−1`,
    which is saturated by the fiber's own weight and hence useless for the depth).
    ★ `BCqIter_fiber_profile` proves the profile by induction on the iterate count
    (`p2_fiber_prefix'` + the head-`1` split, exactly as `BCqIterO_cB_psum_le`), and
    ★★ `BCqIter_fiber_dep_ge` converts profile + weight equality into
    `depth (fiber_n) ≥ n+1` (if `depth < n+1`, then
    `weight = psum (fiber) depth ≤ psum (template) depth < psum (template) (n+1) = weight`).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## Arithmetic helpers (nonlinear, so `omega` alone is not enough) -/

lemma fiberArith1 (q m : ℕ) (hq : 1 ≤ q) (hm : 1 ≤ m) :
    (q - 1) + (1 + (m - 1) * q) = m * q := by
  have h1 : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hm' : m = (m - 1) + 1 := (Nat.succ_pred_eq_of_pos hm).symm
  calc
    (q - 1) + (1 + (m - 1) * q) = ((q - 1) + 1) + (m - 1) * q := by omega
    _ = q + (m - 1) * q := by rw [h1]
    _ = (m - 1) * q + q := by omega
    _ = m * q := by
          conv_rhs => rw [hm']
          rw [Nat.succ_mul]

lemma fiberArith2 (q n : ℕ) (hq : 1 ≤ q) :
    (q - 1) + (1 + (n * q + (q - 1))) = (n + 1) * q + (q - 1) := by
  have h1 : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have h2 : (n + 1) * q = n * q + q := Nat.succ_mul n q
  omega

/-! ## The template `(q, …, q, q−1)` and its prefix profile -/

/-- The reference template `(q, …, q, q−1)` of depth `n+1` (the paper's
`(q^{n}, q−1)`). -/
noncomputable def fiberTmpl (n : ℕ) : Fin (n + 1) → ℕ+ :=
  fun i => if (i : ℕ) < n then qExp F else qMinusExp F

/-- The prefix profile of the template `(q^{n}, q−1)`, for `m ≤ n+1`. -/
lemma fiberTmpl_psum_le (n m : ℕ) (hm : m ≤ n + 1) :
    psum (fiberTmpl F n) m =
      min m n * Nat.card F + (if n < m then (qMinusExp F : ℕ) else 0) := by
  classical
  have hterm : ∀ j ∈ Finset.range m, pad0 (fiberTmpl F n) j =
      (if j < n then (qExp F : ℕ) else (qMinusExp F : ℕ)) := by
    intro j hj
    have hj' : j < n + 1 := by have := Finset.mem_range.mp hj; omega
    rw [pad0_of_lt (fiberTmpl F n) hj']
    by_cases hjn : j < n
    · simp [fiberTmpl, hjn]
    · simp [fiberTmpl, hjn]
  rw [psum, Finset.sum_congr rfl hterm]
  rcases Nat.lt_or_ge n m with hnm | hnm
  · have hm1 : m = n + 1 := by omega
    have h1 : (∑ j ∈ Finset.range n,
        (if j < n then (qExp F : ℕ) else (qMinusExp F : ℕ))) = n * Nat.card F := by
      rw [Finset.sum_congr rfl (fun j hj => if_pos (Finset.mem_range.mp hj))]
      simp [qExp]
    have h2 : (if n < n then (qExp F : ℕ) else (qMinusExp F : ℕ)) = (qMinusExp F : ℕ) :=
      if_neg (by omega)
    rw [hm1, Finset.sum_range_succ, h1, h2]
    rw [if_pos (by omega : n < n + 1), show min (n + 1) n = n from Nat.min_eq_right (by omega)]
  · rw [show min m n = m from Nat.min_eq_left hnm, if_neg (by omega : ¬ n < m), Nat.add_zero]
    rw [Finset.sum_congr rfl (fun j hj => if_pos (by have := Finset.mem_range.mp hj; omega))]
    simp [qExp]

/-- The prefix profile of the template `(q^{n}, q−1)`, for ALL `m`. -/
lemma fiberTmpl_psum (n m : ℕ) :
    psum (fiberTmpl F n) m =
      min m n * Nat.card F + (if n < m then (qMinusExp F : ℕ) else 0) := by
  rcases Nat.lt_or_ge m (n + 1) with hm | hm
  · exact fiberTmpl_psum_le F n m (by omega)
  · have h1 : psum (fiberTmpl F n) m = weight (n + 1) (fiberTmpl F n) :=
      psum_ge_depth (fiberTmpl F n) (by omega)
    have h2 : psum (fiberTmpl F n) (n + 1) = weight (n + 1) (fiberTmpl F n) :=
      psum_ge_depth (fiberTmpl F n) (le_refl (n + 1))
    rw [h1, ← h2, fiberTmpl_psum_le F n (n + 1) (le_refl (n + 1)),
      show min (n + 1) n = n from Nat.min_eq_right (by omega), if_pos (by omega),
      show min m n = n from Nat.min_eq_right (by omega), if_pos (by omega)]

/-- The template's weight. -/
lemma fiberTmpl_weight (n : ℕ) :
    weight (n + 1) (fiberTmpl F n) = n * Nat.card F + (qMinusExp F : ℕ) := by
  have hp := psum_ge_depth (fiberTmpl F n) (le_refl (n + 1))
  rw [← hp, fiberTmpl_psum F n (n + 1),
    show min (n + 1) n = n from Nat.min_eq_right (by omega), if_pos (by omega)]

/-! ## The template profile of the `BC_q`-iterate fibers -/

/-- ★ The `BC_q`-iterate fiber TEMPLATE PROFILE: after `n` steps every b-fiber's prefix
sums are dominated by the profile of `(q^{n}, q−1)`. -/
lemma BCqIter_fiber_profile (n : ℕ) (R0 : BinaryRel F)
    (hbhd : ∀ j : R0.ιB, ((R0.cB j) ⟨0, R0.hdepB j⟩ : ℕ) = 1)
    (hX : ∀ j : R0.ιB, ∀ m : ℕ, psum (expTail (R0.cB j)) m ≤ (qMinusExp F : ℕ)) :
    ∀ i : (RelData.BCqIter F n (toData F R0)).ιB,
      ∀ m : ℕ, psum (expTail ((RelData.BCqIter F n (toData F R0)).cB i)) m ≤
        psum (fiberTmpl F n) m := by
  classical
  induction n with
  | zero =>
      intro i m
      change psum (expTail ((toData F R0).cB i)) m ≤ psum (fiberTmpl F 0) m
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        rw [psum_zero, psum_zero]
      · have h0 : psum (fiberTmpl F 0) m =
            min m 0 * Nat.card F + (if 0 < m then (qMinusExp F : ℕ) else 0) :=
          fiberTmpl_psum F 0 m
        rw [h0, show min m 0 = 0 from Nat.min_eq_right (Nat.zero_le m), if_pos hm,
          Nat.zero_mul, Nat.zero_add]
        exact hX i m
  | succ n ih =>
      rw [BCqIter_append]
      intro i m
      change RelData.BCqIdx F (RelData.BCqIter F n (toData F R0)) at i
      rcases i with ⟨j, e⟩
      let Dn := RelData.BCqIter F n (toData F R0)
      have hhead : ((Dn.cB j) ⟨0, Dn.hdepB j⟩ : ℕ) = 1 :=
        BCqIter_head_one_data F n R0 hbhd j
      have htail : expTail ((RelData.BCq F Dn).cB ⟨j, e⟩) =
          (p2WpT F (qMinusExp F) (Dn.hdepB j) (Dn.cB j)).c e := by
        dsimp only [RelData.BCq, Dn]
        rfl
      have hstep : psum (expTail ((RelData.BCq F Dn).cB ⟨j, e⟩)) m ≤
          psum (single (qMinusExp F)) m + psum (Dn.cB j) m := by
        rw [htail]
        exact p2_fiber_prefix' F Dn j e m
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        rw [psum_zero, psum_zero]
      · have hIH : psum (expTail (Dn.cB j)) (m - 1) ≤ psum (fiberTmpl F n) (m - 1) :=
          ih j (m - 1)
        have hsplit : psum (Dn.cB j) m = 1 + psum (expTail (Dn.cB j)) (m - 1) := by
          have h := psum_head_expTail (Dn.hdepB j) (Dn.cB j) (m - 1)
          rw [show (m - 1) + 1 = m from Nat.sub_add_cancel hm] at h
          rw [h, hhead]
        have hsingle : psum (single (qMinusExp F)) m = (qMinusExp F : ℕ) :=
          psum_single_of_pos (qMinusExp F) hm
        have hq2 : 2 ≤ Nat.card F := card_ge_two F
        have hqm : (qMinusExp F : ℕ) = Nat.card F - 1 := rfl
        rcases Nat.lt_or_ge (n + 1) m with hlt | hle
        · -- n+1 < m
          have hb2 : n + 1 ≤ m := by omega
          have hb1 : n + 1 ≤ m - 1 :=
            (Nat.le_sub_iff_add_le (by omega : 1 ≤ m)).mpr (by omega)
          have hgoal : psum (fiberTmpl F (n + 1)) m =
              min m (n + 1) * Nat.card F + (if n + 1 < m then (qMinusExp F : ℕ) else 0) :=
            fiberTmpl_psum F (n + 1) m
          have hmn : min m (n + 1) = n + 1 := Nat.min_eq_right hb2
          have htop : psum (fiberTmpl F n) (n + 1) = n * Nat.card F + (qMinusExp F : ℕ) := by
            rw [fiberTmpl_psum F n (n + 1),
              show min (n + 1) n = n from Nat.min_eq_right (Nat.le_succ n),
              if_pos (Nat.lt_succ_self n)]
          have hmono : psum (fiberTmpl F n) (m - 1) ≤ psum (fiberTmpl F n) (n + 1) := by
            rw [psum_ge_depth (fiberTmpl F n) hb1,
              psum_ge_depth (fiberTmpl F n) (le_refl (n + 1))]
          rw [hgoal, if_pos hlt, hmn]
          calc
            psum (expTail ((RelData.BCq F Dn).cB ⟨j, e⟩)) m
                ≤ psum (single (qMinusExp F)) m + psum (Dn.cB j) m := hstep
            _ = (qMinusExp F : ℕ) + (1 + psum (expTail (Dn.cB j)) (m - 1)) := by
                  rw [hsingle, hsplit]
            _ ≤ (qMinusExp F : ℕ) + (1 + (n * Nat.card F + (qMinusExp F : ℕ))) := by
                  have h2 := le_trans hIH (le_trans hmono (le_of_eq htop))
                  exact Nat.add_le_add_left (Nat.add_le_add_left h2 1) _
            _ = (n + 1) * Nat.card F + (qMinusExp F : ℕ) :=
                  fiberArith2 (Nat.card F) n (by omega)
        · -- m ≤ n+1: (q−1) + 1 + (m−1)·q = m·q
          have hb3 : m - 1 ≤ n := (Nat.sub_le_iff_le_add).mpr (by omega)
          have hgoal : psum (fiberTmpl F (n + 1)) m =
              min m (n + 1) * Nat.card F + (if n + 1 < m then (qMinusExp F : ℕ) else 0) :=
            fiberTmpl_psum F (n + 1) m
          have hmn : min m (n + 1) = m := Nat.min_eq_left hle
          have h0 : psum (fiberTmpl F n) (m - 1) = (m - 1) * Nat.card F := by
            rw [fiberTmpl_psum F n (m - 1),
              show min (m - 1) n = m - 1 from Nat.min_eq_left hb3,
              if_neg (not_lt.mpr hb3), Nat.add_zero]
          rw [hgoal, if_neg (not_lt.mpr hle), hmn]
          rw [h0] at hIH
          calc
            psum (expTail ((RelData.BCq F Dn).cB ⟨j, e⟩)) m
                ≤ psum (single (qMinusExp F)) m + psum (Dn.cB j) m := hstep
            _ = (qMinusExp F : ℕ) + (1 + psum (expTail (Dn.cB j)) (m - 1)) := by
                  rw [hsingle, hsplit]
            _ ≤ (qMinusExp F : ℕ) + (1 + (m - 1) * Nat.card F) :=
                  Nat.add_le_add_left (Nat.add_le_add_left hIH 1) _
            _ = m * Nat.card F := fiberArith1 (Nat.card F) m (by omega) hm

/-- ★★ The iterate fiber DEPTH bound: after `n` `BC_q` steps every b-fiber has depth at
least `n+1` (paper: Prop 2.13's `depth(u) ≥ depth(s)`), i.e. the b-tuple depth is at
least `n+2`. -/
theorem BCqIter_fiber_dep_ge (n : ℕ) :
    ∀ i : (RelData.BCqIter F n (toData F (r1Rel F))).ιB,
      n + 2 ≤ (RelData.BCqIter F n (toData F (r1Rel F))).depB i := by
  classical
  intro i
  have hprof := BCqIter_fiber_profile F n (r1Rel F) (r1Rel_hbhd F) (r1Rel_tail_psum F) i
  have hwt := BCq_fiber_weight_X F n (r1Rel F) (r1Rel_hbhd F) (qMinusExp F)
    (r1Rel_tail_weight F) i
  by_contra hcon
  push Not at hcon
  have hsub : (RelData.BCqIter F n (toData F (r1Rel F))).depB i - 1 ≤ n :=
    (Nat.sub_le_iff_le_add).mpr (by omega)
  have hd : (RelData.BCqIter F n (toData F (r1Rel F))).depB i - 1 < n + 1 :=
    Nat.lt_succ_of_le hsub
  have hw1 : psum (expTail ((RelData.BCqIter F n (toData F (r1Rel F))).cB i))
        ((RelData.BCqIter F n (toData F (r1Rel F))).depB i - 1) =
      n * Nat.card F + (qMinusExp F : ℕ) := by
    rw [psum_ge_depth (expTail ((RelData.BCqIter F n (toData F (r1Rel F))).cB i))
      (le_refl ((RelData.BCqIter F n (toData F (r1Rel F))).depB i - 1))]
    exact hwt
  have hle := hprof ((RelData.BCqIter F n (toData F (r1Rel F))).depB i - 1)
  have hlt : psum (fiberTmpl F n) ((RelData.BCqIter F n (toData F (r1Rel F))).depB i - 1)
      < psum (fiberTmpl F n) (n + 1) :=
    psum_lt_psum_of_lt (fiberTmpl F n) hd (le_refl (n + 1))
  have htop : psum (fiberTmpl F n) (n + 1) = n * Nat.card F + (qMinusExp F : ℕ) := by
    rw [fiberTmpl_psum F n (n + 1),
      show min (n + 1) n = n from Nat.min_eq_right (Nat.le_succ n),
      if_pos (Nat.lt_succ_self n)]
  have hle2 : n * Nat.card F + (qMinusExp F : ℕ) ≤
      psum (fiberTmpl F n) ((RelData.BCqIter F n (toData F (r1Rel F))).depB i - 1) := by
    rw [← hw1]
    exact hle
  have hbad : n * Nat.card F + (qMinusExp F : ℕ) < n * Nat.card F + (qMinusExp F : ℕ) :=
    lt_of_le_of_lt hle2 (lt_of_lt_of_le hlt (le_of_eq htop))
  exact absurd hbad (lt_irrefl _)

end ZagierHoffmanPositiveChar
