
import Mathlib
import Submission.Work.WilE9.Sharp.Vocab
import Submission.Work.WilE9.Sharp.ExConsts
import Submission.Work.WilE9.Sharp.clearNumDen_totalDegree_le
import Submission.Work.WilE9.Deg.iftP_totalDegree_le

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-!
## The degree bookkeeping for the extended system (self-contained)

Everything the assembly below needs about `totalDegree` is proved here from the imported
component bounds `Deg.jQ_totalDegree_le` (`pbQ`), `Deg.iftP_totalDegree_le` (`pbP`) and
`clearNumDen_totalDegree_le` (`clearPb`, whence `exQ`, `exP`).  The constants are the raw
`ℕ`-expressions of `ExConsts.lean`, so the final polynomial is *literally*
`A3 n a₀ * (1+X₀)² * (1+X₁)`, evaluated to `A3 n a₀ * (D+1)² * (|L|+1)`.

The lemmas are kept in the namespace `ExDegDev` so that they do not clash with the
same-shaped development elsewhere in the area.
-/
namespace ExDegDev
/-! ## 1. Renaming does not raise the degree -/

theorem exRaise_totalDegree_le {n m r : ℕ} (P : EAPoly (n + (1 + m)) r) :
    (exRaise (n := n) (m := m) P).totalDegree ≤ P.totalDegree := by
  unfold exRaise
  exact MvPolynomial.totalDegree_rename_le _ P

theorem pbRaise_totalDegree_le {n m r : ℕ} (P : EAPoly (n + (1 + m)) r) :
    (pbRaise (n := n) (m := m) P).totalDegree ≤ P.totalDegree := by
  unfold pbRaise
  exact MvPolynomial.totalDegree_rename_le _ P

theorem atomDeg_exRaise_le {n m r : ℕ} (P : EAPoly (n + (1 + m)) r) :
    atomDeg (exRaise (n := n) (m := m) P) ≤ atomDeg P := by
  unfold atomDeg
  exact Nat.add_le_add_right (exRaise_totalDegree_le P) 1

/-! ## 2. The atoms of the extended system -/

theorem totalDegree_X_sub_mul_le {k r : ℕ} (A B C : Fin k) :
    ((MvPolynomial.X (Sum.inl A) - MvPolynomial.X (Sum.inl B) * MvPolynomial.X (Sum.inl C) :
      EAPoly k r)).totalDegree ≤ 2 := by
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · rw [MvPolynomial.totalDegree_X] <;> omega
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X] <;> omega

theorem totalDegree_sq_add_sq_sub_one_le {k r : ℕ} (A B : Fin k) :
    ((MvPolynomial.X (Sum.inl A) ^ 2 + MvPolynomial.X (Sum.inl B) ^ 2 - 1 :
      EAPoly k r)).totalDegree ≤ 2 := by
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · rw [MvPolynomial.totalDegree_X_pow]
    · rw [MvPolynomial.totalDegree_X_pow]
  · rw [MvPolynomial.totalDegree_one] <;> omega

/-- A single coordinate has atom degree `2`. -/
theorem atomDeg_X_le {k r : ℕ} (A : Fin k) :
    atomDeg (MvPolynomial.X (Sum.inl A) : EAPoly k r) ≤ 2 := by
  unfold atomDeg
  rw [MvPolynomial.totalDegree_X] <;> omega

/-- The algebraic relation `y² + w² - 1` has atom degree `3`. -/
theorem atomDeg_sq_le {k r : ℕ} (A B : Fin k) :
    atomDeg (MvPolynomial.X (Sum.inl A) ^ 2 + MvPolynomial.X (Sum.inl B) ^ 2 - 1 :
      EAPoly k r) ≤ 3 := by
  unfold atomDeg
  have := totalDegree_sq_add_sq_sub_one_le (k := k) (r := r) A B
  omega

/-! ## 3. The pulled-back system -/

/-- Each equation of the pulled-back system has total degree at most `E.deg + 2`. -/
theorem pbF_totalDegree_le (n m : ℕ) (E : EffStratum n m) (j : Fin (qpb n m)) :
    (pbF n m E.X.r E.h j).totalDegree ≤ E.deg + 2 := by
  have hA : ∀ a : Fin (1 + m), (E.h a).totalDegree ≤ E.deg := by
    intro a
    have h2 : atomDeg (E.h a) ≤ ∑ a, atomDeg (E.h a) :=
      Finset.single_le_sum (f := fun a => atomDeg (E.h a)) (fun b _ => Nat.zero_le _)
        (Finset.mem_univ a)
    have h3 : (∑ a, atomDeg (E.h a)) ≤ E.deg := by rw [EffStratum.deg]; omega
    have h4 : (E.h a).totalDegree + 1 ≤ E.deg := le_trans h2 h3
    omega
  rw [pbF]
  split_ifs with h0 h1 h2 h3
  · exact (totalDegree_X_sub_mul_le _ _ _).trans (by omega)
  · exact (totalDegree_X_sub_mul_le _ _ _).trans (by omega)
  · exact (totalDegree_sq_add_sq_sub_one_le _ _).trans (by omega)
  · exact (totalDegree_sq_add_sq_sub_one_le _ _).trans (by omega)
  · exact le_trans (pbRaise_totalDegree_le _) (le_trans (hA _) (by omega))

/-- The sum of the total degrees of the pulled-back equations, bounded by `qpb n m * (E.deg+2)`. -/
theorem pbF_sum_totalDegree_le (n m : ℕ) (E : EffStratum n m) :
    (∑ j : Fin (qpb n m), (pbF n m E.X.r E.h j).totalDegree) ≤ qpb n m * (E.deg + 2) := by
  refine (Finset.sum_le_sum (fun j _ => pbF_totalDegree_le n m E j)).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- `clearPb` raises the total degree by at most `K * (n+1)`. -/
theorem clearPb_totalDegree_le (n m : ℕ) {r : ℕ} (K : ℕ) (P : EAPoly (Npb n m) r) :
    (clearPb n m K P).totalDegree ≤ K * (n + 1) + P.totalDegree := by
  unfold clearPb
  refine (clearNumDen_totalDegree_le _ _ _ K _).trans ?_
  rw [Fintype.card_fin]
  exact Nat.add_le_add_left (MvPolynomial.totalDegree_rename_le _ _) _

/-! ## 4. Summing atom degrees over the lists of the extended system -/

/-- The sum of the atoms of a `List.finRange n` mapped through a function bounded by `c`. -/
theorem finRange_map_sum_le {n : ℕ} {f : Fin n → ℕ} {c : ℕ} (h : ∀ i, f i ≤ c) :
    ((List.finRange n).map f).sum ≤ c * n := by
  refine (List.sum_le_length_nsmul ((List.finRange n).map f) c ?_).trans ?_
  · rintro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    exact h i
  · rw [List.length_map, List.length_finRange, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]

/-- `(l.map (fun x => c + f x)).sum = l.length * c + (l.map f).sum`. -/
theorem sum_map_add_const {α : Type*} (l : List α) (c : ℕ) (f : α → ℕ) :
    (l.map (fun x => c + f x)).sum = l.length * c + (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]; ring

/-- The atom degree of the list of equations of the extended system. -/
theorem atomDeg_exEqList_sum_le {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n)) (S : ℕ)
    (hS : (∑ a : Fin (1 + m), atomDeg (h a)) ≤ S) :
    ((exEqList c h L).map atomDeg).sum ≤ 3 * n + 6 + S + atomDeg (exEq6 c h L) := by
  simp only [exEqList, List.map_append, List.sum_append]
  have hA : (List.map atomDeg ((List.finRange n).map (fun i : Fin n =>
      (MvPolynomial.X (Sum.inl (exY n m i)) ^ 2 + MvPolynomial.X (Sum.inl (exW n m i)) ^ 2 - 1 :
        EAPoly (Next n m) r)))).sum ≤ 3 * n := by
    rw [List.map_map]
    exact finRange_map_sum_le (fun i => atomDeg_sq_le (exY n m i) (exW n m i))
  have hB : (List.map atomDeg
      [(MvPolynomial.X (Sum.inl (exT n m)) ^ 2 + MvPolynomial.X (Sum.inl (exU n m)) ^ 2 - 1 :
        EAPoly (Next n m) r)]).sum ≤ 3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact atomDeg_sq_le (exT n m) (exU n m)
  have hC : (List.map atomDeg ((List.finRange (1 + m)).map (fun a =>
      exRaise (n := n) (m := m) (h a)))).sum ≤ S := by
    have h1 : (List.map atomDeg ((List.finRange (1 + m)).map (fun a =>
        exRaise (n := n) (m := m) (h a)))).sum
        ≤ ((List.finRange (1 + m)).map (fun a => atomDeg (h a))).sum := by
      rw [List.map_map]
      exact List.sum_le_sum (fun a _ => atomDeg_exRaise_le (h a))
    refine h1.trans ?_
    rw [← List.ofFn_eq_map, List.sum_ofFn]
    exact hS
  have hD : (List.map atomDeg
      [(MvPolynomial.X (Sum.inl (exSig n m)) ^ 2 + MvPolynomial.X (Sum.inl (exV n m)) ^ 2 - 1 :
        EAPoly (Next n m) r)]).sum ≤ 3 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact atomDeg_sq_le (exSig n m) (exV n m)
  have hE : (List.map atomDeg [exEq6 c h L]).sum = atomDeg (exEq6 c h L) := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  omega

/-- The atom degree of the list of strict inequalities of the extended system. -/
theorem atomDeg_exPosList_sum_le {n m r : ℕ} (B : Basic (n + (1 + m)) r) :
    ((exPosList (n := n) (m := m) (r := r) B).map atomDeg).sum
      ≤ 2 * n + 4 + (B.pos.map atomDeg).sum := by
  simp only [exPosList, List.map_append, List.sum_append]
  have hA : (List.map atomDeg ((List.finRange n).map (fun i : Fin n =>
      (MvPolynomial.X (Sum.inl (exW n m i)) : EAPoly (Next n m) r)))).sum ≤ 2 * n := by
    rw [List.map_map]
    exact finRange_map_sum_le (fun i => atomDeg_X_le (exW n m i))
  have hB : (List.map atomDeg
      [(MvPolynomial.X (Sum.inl (exU n m)) : EAPoly (Next n m) r),
       (MvPolynomial.X (Sum.inl (exV n m)) : EAPoly (Next n m) r)]).sum ≤ 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have h1 := atomDeg_X_le (k := Next n m) (r := r) (exU n m)
    have h2 := atomDeg_X_le (k := Next n m) (r := r) (exV n m)
    omega
  have hC : (List.map atomDeg (B.pos.map exRaise)).sum ≤ (B.pos.map atomDeg).sum := by
    rw [List.map_map]
    exact List.sum_le_sum (fun p _ => atomDeg_exRaise_le p)
  omega

/-- The degree of one basic condition of the extended system. -/
theorem exBasic_deg_le {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n))
    (B : Basic (n + (1 + m)) r) (S : ℕ)
    (hS : (∑ a : Fin (1 + m), atomDeg (h a)) ≤ S) :
    (exBasic c h L B).deg ≤ 5 * n + 10 + S + atomDeg (exEq6 c h L) + B.deg := by
  simp only [exBasic, Basic.deg, List.map_append, List.sum_append]
  have h1 := atomDeg_exEqList_sum_le c h L S hS
  have h2 : (List.map atomDeg (B.eqs.map exRaise)).sum ≤ (List.map atomDeg B.eqs).sum := by
    rw [List.map_map]
    exact List.sum_le_sum (fun p _ => atomDeg_exRaise_le p)
  have h3 := atomDeg_exPosList_sum_le (n := n) (m := m) (r := r) B
  omega

/-! ## 5. The cleared equation `exEq6` -/

/-- **The degree of the cleared equation.**  The whole content of the sharp degree bound: the
fibre dimension only enters through `m ≤ a₀`, so the estimate is *simultaneously* uniform in `m`. -/
theorem atomDeg_exEq6_le (n m a₀ : ℕ) (E : EffStratum n m) (L : List (Fin n)) (hm : m ≤ a₀) :
    atomDeg (exEq6 E.X.c E.h L) ≤ A2 n a₀ * (E.deg + 2) * (L.length + 1) := by
  have hq : qpb n m ≤ qm n a₀ := by simp only [qpb, qm]; omega
  have hq' : qpb n m ≤ 2 * n + a₀ + 3 := hq
  -- (a) the sum of the degrees of the pulled-back equations
  have hdF_le :
      (∑ j : Fin (qpb n m), (pbF n m E.X.r E.h j).totalDegree) ≤ qm n a₀ * (E.deg + 2) :=
    (pbF_sum_totalDegree_le n m E).trans (Nat.mul_le_mul_right _ hq)
  have hsumSd :
      (∑ j : Fin (qpb n m), (pbF n m E.X.r E.h j).totalDegree)
        ≤ (qm n a₀ + 1) * (E.deg + 2) := by
    refine hdF_le.trans ?_
    rw [Nat.add_mul, one_mul]
    exact Nat.le_add_right _ _
  have hsd1 :
      (∑ j : Fin (qpb n m), (pbF n m E.X.r E.h j).totalDegree) + 1
        ≤ (qm n a₀ + 1) * (E.deg + 2) := by
    calc (∑ j : Fin (qpb n m), (pbF n m E.X.r E.h j).totalDegree) + 1
        ≤ qm n a₀ * (E.deg + 2) + 1 := Nat.add_le_add_right hdF_le 1
      _ ≤ qm n a₀ * (E.deg + 2) + (E.deg + 2) := by omega
      _ = (qm n a₀ + 1) * (E.deg + 2) := by ring
  -- (b) numerical facts about `bm`
  have hbm : 2 ≤ bm n a₀ := by
    rw [show bm n a₀ = 4 * (qm n a₀ ^ 3 + qm n a₀ ^ 2 + qm n a₀ + 1) from rfl]
    have h1 : 1 ≤ qm n a₀ ^ 3 + qm n a₀ ^ 2 + qm n a₀ + 1 := by omega
    omega
  have hl2 : 2 * L.length ≤ 1 + L.length * bm n a₀ := by
    have h : L.length * 2 ≤ L.length * bm n a₀ := Nat.mul_le_mul_left _ hbm
    omega
  have hbmq :
      4 * (qpb n m * qpb n m * qpb n m + qpb n m * qpb n m + qpb n m + 1) ≤ bm n a₀ := by
    rw [show bm n a₀
        = 4 * ((2 * n + a₀ + 3) * (2 * n + a₀ + 3) * (2 * n + a₀ + 3)
            + (2 * n + a₀ + 3) * (2 * n + a₀ + 3) + (2 * n + a₀ + 3) + 1) from by
      simp only [bm, qm]; ring]
    refine Nat.mul_le_mul_left 4 ?_
    have h3 : qpb n m * qpb n m * qpb n m
        ≤ (2 * n + a₀ + 3) * (2 * n + a₀ + 3) * (2 * n + a₀ + 3) :=
      Nat.mul_le_mul (Nat.mul_le_mul hq' hq') hq'
    have h2 : qpb n m * qpb n m ≤ (2 * n + a₀ + 3) * (2 * n + a₀ + 3) :=
      Nat.mul_le_mul hq' hq'
    omega
  -- (c) the degree of `Q ^ (2 * |L|)`
  have hQ : (pbQ E.X.c E.h).totalDegree
      ≤ (∑ j : Fin (qpb n m), (pbF n m E.X.r E.h j).totalDegree) := by
    rw [pbQ]
    exact Work.WilE9.Deg.jQ_totalDegree_le (pbChain E.X.c) (pbF n m E.X.r E.h)
  have hpow : (pbQ E.X.c E.h ^ (2 * L.length)).totalDegree
      ≤ ((qm n a₀ + 1) * (E.deg + 2)) * (1 + L.length * bm n a₀) := by
    refine (MvPolynomial.totalDegree_pow _ _).trans ?_
    calc (2 * L.length) * (pbQ E.X.c E.h).totalDegree
        ≤ (2 * L.length) * ((qm n a₀ + 1) * (E.deg + 2)) :=
          Nat.mul_le_mul_left _ (hQ.trans hsumSd)
      _ ≤ (1 + L.length * bm n a₀) * ((qm n a₀ + 1) * (E.deg + 2)) :=
          Nat.mul_le_mul_right _ hl2
      _ = ((qm n a₀ + 1) * (E.deg + 2)) * (1 + L.length * bm n a₀) := Nat.mul_comm _ _
  -- (d) the degree of `P_L`
  have hPbound : (pbP E.X.c E.h L).totalDegree
      ≤ ((qm n a₀ + 1) * (E.deg + 2)) * (1 + L.length * bm n a₀) := by
    rw [pbP]
    refine (Work.WilE9.Deg.iftP_totalDegree_le (pbChain E.X.c) (pbF n m E.X.r E.h)
      (fS n m) L).trans ?_
    calc ((∑ j : Fin (qpb n m), (pbF n m E.X.r E.h j).totalDegree) + 1)
            + L.length * (4 * (qpb n m * qpb n m * qpb n m + qpb n m * qpb n m
                + qpb n m + 1)
              * ((∑ j : Fin (qpb n m), (pbF n m E.X.r E.h j).totalDegree) + 1))
        = ((∑ j : Fin (qpb n m), (pbF n m E.X.r E.h j).totalDegree) + 1)
            * (1 + L.length * (4 * (qpb n m * qpb n m * qpb n m + qpb n m * qpb n m
                + qpb n m + 1))) := by ring
      _ ≤ ((qm n a₀ + 1) * (E.deg + 2)) * (1 + L.length * bm n a₀) := by
          apply Nat.mul_le_mul hsd1
          exact Nat.add_le_add_left (Nat.mul_le_mul_left L.length hbmq) 1
  -- (e) `exK`
  have exK_le : exK E.X.c E.h L
      ≤ ((qm n a₀ + 1) * (E.deg + 2)) * (1 + L.length * bm n a₀) + 1 := by
    rw [exK]
    exact Nat.add_le_add_right (max_le hpow hPbound) 1
  -- (f) the two factors of `exEq6`
  have hQbound : (exQ E.X.c E.h L).totalDegree
      ≤ ((qm n a₀ + 1) * (E.deg + 2)) * (1 + L.length * bm n a₀) * (n + 2) + (n + 1) := by
    rw [exQ]
    refine (clearPb_totalDegree_le n m (exK E.X.c E.h L) _).trans ?_
    calc (exK E.X.c E.h L) * (n + 1) + (pbQ E.X.c E.h ^ (2 * L.length)).totalDegree
        ≤ (((qm n a₀ + 1) * (E.deg + 2)) * (1 + L.length * bm n a₀) + 1) * (n + 1)
            + ((qm n a₀ + 1) * (E.deg + 2)) * (1 + L.length * bm n a₀) :=
          Nat.add_le_add (Nat.mul_le_mul_right _ exK_le) hpow
      _ = ((qm n a₀ + 1) * (E.deg + 2)) * (1 + L.length * bm n a₀) * (n + 2) + (n + 1) := by
          ring
  have hPbound2 : (exP E.X.c E.h L).totalDegree
      ≤ ((qm n a₀ + 1) * (E.deg + 2)) * (1 + L.length * bm n a₀) * (n + 2) + (n + 1) := by
    rw [exP]
    refine (clearPb_totalDegree_le n m (exK E.X.c E.h L) _).trans ?_
    calc (exK E.X.c E.h L) * (n + 1) + (pbP E.X.c E.h L).totalDegree
        ≤ (((qm n a₀ + 1) * (E.deg + 2)) * (1 + L.length * bm n a₀) + 1) * (n + 1)
            + ((qm n a₀ + 1) * (E.deg + 2)) * (1 + L.length * bm n a₀) :=
          Nat.add_le_add (Nat.mul_le_mul_right _ exK_le) hPbound
      _ = ((qm n a₀ + 1) * (E.deg + 2)) * (1 + L.length * bm n a₀) * (n + 2) + (n + 1) := by
          ring
  -- (g) the equation itself
  have htd : (exEq6 E.X.c E.h L).totalDegree
      ≤ ((qm n a₀ + 1) * (E.deg + 2)) * (1 + L.length * bm n a₀) * (n + 2) + (n + 2) := by
    rw [exEq6]
    refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_X]
      have h := hQbound
      omega
    · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_X]
      have h := hPbound2
      omega
  have hatom : atomDeg (exEq6 E.X.c E.h L)
      ≤ ((qm n a₀ + 1) * (E.deg + 2)) * (1 + L.length * bm n a₀) * (n + 2) + (n + 3) := by
    unfold atomDeg
    have := htd
    omega
  -- (h) scaling to `A2`
  have hGc : 1 + L.length * bm n a₀ ≤ (L.length + 1) * Gc n a₀ := by
    rw [show Gc n a₀ = 1 + bm n a₀ from rfl]
    have : (L.length + 1) * (1 + bm n a₀)
        = (1 + L.length * bm n a₀) + (bm n a₀ + L.length) := by ring
    rw [this]; exact Nat.le_add_right _ _
  have hscale : ((qm n a₀ + 1) * (E.deg + 2)) * (1 + L.length * bm n a₀) * (n + 2)
      ≤ A1 n a₀ * (E.deg + 2) * (L.length + 1) := by
    calc ((qm n a₀ + 1) * (E.deg + 2)) * (1 + L.length * bm n a₀) * (n + 2)
        ≤ ((qm n a₀ + 1) * (E.deg + 2)) * ((L.length + 1) * Gc n a₀) * (n + 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hGc) (le_refl _)
      _ = A1 n a₀ * (E.deg + 2) * (L.length + 1) := by
          rw [show A1 n a₀ = (qm n a₀ + 1) * Gc n a₀ * (n + 2) from rfl]; ring
  have hA2 : A1 n a₀ * (E.deg + 2) * (L.length + 1) + (n + 3)
      ≤ A2 n a₀ * (E.deg + 2) * (L.length + 1) := by
    have hpos : 0 < (E.deg + 2) * (L.length + 1) := Nat.mul_pos (by omega) (by omega)
    have h1 : 1 ≤ (E.deg + 2) * (L.length + 1) := by omega
    have hge : (n + 3) ≤ (n + 3) * ((E.deg + 2) * (L.length + 1)) := by
      calc (n + 3) = (n + 3) * 1 := (Nat.mul_one _).symm
        _ ≤ (n + 3) * ((E.deg + 2) * (L.length + 1)) := Nat.mul_le_mul_left _ h1
    have hsplit : A2 n a₀ * (E.deg + 2) * (L.length + 1)
        = A1 n a₀ * (E.deg + 2) * (L.length + 1)
            + (n + 3) * ((E.deg + 2) * (L.length + 1)) := by
      rw [show A2 n a₀ = A1 n a₀ + n + 3 from rfl]; ring
    rw [hsplit]
    exact Nat.add_le_add_left hge _
  calc atomDeg (exEq6 E.X.c E.h L)
      ≤ ((qm n a₀ + 1) * (E.deg + 2)) * (1 + L.length * bm n a₀) * (n + 2) + (n + 3) := hatom
    _ ≤ A1 n a₀ * (E.deg + 2) * (L.length + 1) + (n + 3) := Nat.add_le_add_right hscale _
    _ ≤ A2 n a₀ * (E.deg + 2) * (L.length + 1) := hA2

/-! ## 6. The arithmetic of the final bound -/

theorem arith_bound (n a₀ D l : ℕ) :
    (D + 1) * (5 * n + 10 + D + A2 n a₀ * (D + 2) * (l + 1)) + D
      ≤ A3 n a₀ * (D + 1) ^ 2 * (l + 1) := by
  have hl1 : 1 ≤ l + 1 := by omega
  have hD2 : D + 2 ≤ 2 * (D + 1) := by omega
  have hA : A2 n a₀ * (D + 2) * (l + 1) ≤ 2 * A2 n a₀ * (D + 1) * (l + 1) := by
    calc A2 n a₀ * (D + 2) * (l + 1)
        ≤ A2 n a₀ * (2 * (D + 1)) * (l + 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hD2)
      _ = 2 * A2 n a₀ * (D + 1) * (l + 1) := by ring
  have hB : 5 * n + 10 + D ≤ (5 * n + 11) * (D + 1) := by nlinarith
  have h3 : 5 * n + 10 + D + A2 n a₀ * (D + 2) * (l + 1)
      ≤ (5 * n + 11 + 2 * A2 n a₀) * (D + 1) * (l + 1) := by
    have h1 : (5 * n + 11) * (D + 1) ≤ (5 * n + 11) * (D + 1) * (l + 1) := by
      calc (5 * n + 11) * (D + 1) = (5 * n + 11) * (D + 1) * 1 := (Nat.mul_one _).symm
        _ ≤ (5 * n + 11) * (D + 1) * (l + 1) := Nat.mul_le_mul_left _ hl1
    calc 5 * n + 10 + D + A2 n a₀ * (D + 2) * (l + 1)
        ≤ (5 * n + 11) * (D + 1) + 2 * A2 n a₀ * (D + 1) * (l + 1) := Nat.add_le_add hB hA
      _ ≤ (5 * n + 11) * (D + 1) * (l + 1) + 2 * A2 n a₀ * (D + 1) * (l + 1) :=
          Nat.add_le_add_right h1 _
      _ = (5 * n + 11 + 2 * A2 n a₀) * (D + 1) * (l + 1) := by ring
  have hDle : D ≤ (D + 1) * (D + 1) * (l + 1) := by
    have h1 : D ≤ (D + 1) * (D + 1) := by nlinarith
    calc D ≤ (D + 1) * (D + 1) := h1
      _ = (D + 1) * (D + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ (D + 1) * (D + 1) * (l + 1) := Nat.mul_le_mul_left _ hl1
  calc (D + 1) * (5 * n + 10 + D + A2 n a₀ * (D + 2) * (l + 1)) + D
      ≤ (D + 1) * ((5 * n + 11 + 2 * A2 n a₀) * (D + 1) * (l + 1)) + D :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ h3) _
    _ = (5 * n + 11 + 2 * A2 n a₀) * ((D + 1) * (D + 1)) * (l + 1) + D := by ring
    _ ≤ (5 * n + 11 + 2 * A2 n a₀) * ((D + 1) * (D + 1)) * (l + 1)
          + (D + 1) * (D + 1) * (l + 1) := Nat.add_le_add_left hDle _
    _ = (5 * n + 12 + 2 * A2 n a₀) * ((D + 1) * (D + 1)) * (l + 1) := by ring
    _ = A3 n a₀ * (D + 1) ^ 2 * (l + 1) := by
        rw [show A3 n a₀ = 5 * n + 12 + 2 * A2 n a₀ from rfl, pow_two]
end ExDegDev

/-! ## The target -/

/-- **Degree bound for the extended system of the E9 assembly.**

`(exSemiPf n m E L).deg` is the sum, over the disjuncts `B` of the stratum's semi-Pfaffian set,
of the degrees of the extended disjuncts `exBasic E.X.c E.h L B`, which contain the fixed
quadratic equations `y²+w²-1`, `τ²+u²-1`, `σ²+υ²-1`, the reindexed equations `h a` and the
single cleared equation `exEq6 E.X.c E.h L`.  Every ingredient is a polynomial in
`(E.deg, |L|, m, ∑ a, atomDeg (h a))` with coefficients depending only on `n`, and the
hypotheses below bound each of those by `(D, |L|, a₀)`.  The constants realizing the advertised
shape `A3 n a₀ * (|L|+1) * (D+1)^2` are collected in `Submission.Work.WilE9.Sharp.ExConsts`;
the degree bounds of the components are `clearNumDen_totalDegree_le` (for `exQ`, `exP`),
`Deg.jQ_totalDegree_le` (for `pbQ`) and `Deg.iftP_totalDegree_le` (for `pbP`).

NOTE: the proof is self-contained.  The degree bookkeeping is carried out in `ExDegDev` above,
directly from the three component bounds named in the previous paragraph; the hypotheses of the
bound are `E.deg ≤ D` together with `E.X.basics.length ≤ D + 1`, the latter being what bounds
the number of disjuncts (a bound on `E.deg` alone would not: an empty disjunct has degree zero).
The final polynomial is `A3 n a₀ * (1+X₀)² * (1+X₁)`, i.e. exactly the advertised
`A3 n a₀ * (D+1)² * (|L|+1)`. -/
theorem exSemiPf_deg_le (n a₀ : ℕ) : ∃ b₀ : MvPolynomial (Fin 3) ℕ,
    ∀ (m : ℕ) (E : Work.WilE9.Sharp.EffStratum n m) (L : List (Fin n)) (D : ℕ),
      m ≤ a₀ → E.X.fmt ≤ a₀ → E.deg ≤ D → E.X.basics.length ≤ D + 1 →
      (Work.WilE9.Sharp.exSemiPf n m E L).deg ≤ b₀.eval ![D, L.length, a₀] := by
  refine ⟨MvPolynomial.C (A3 n a₀) * (1 + MvPolynomial.X (0 : Fin 3)) ^ 2
    * (1 + MvPolynomial.X (1 : Fin 3)), ?_⟩
  intro m E L D hm hfmt hdeg hlen
  -- the value of the advertised polynomial
  have hEval : MvPolynomial.eval ![D, L.length, a₀]
      (MvPolynomial.C (A3 n a₀) * (1 + MvPolynomial.X (0 : Fin 3)) ^ 2
        * (1 + MvPolynomial.X (1 : Fin 3)))
      = A3 n a₀ * (D + 1) ^ 2 * (L.length + 1) := by
    simp [MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_add,
      MvPolynomial.eval_X] <;> ring
  rw [hEval]
  set S0 : ℕ := ∑ a : Fin (1 + m), atomDeg (E.h a) with hS0def
  set U : ℕ := atomDeg (exEq6 E.X.c E.h L) with hUdef
  have hXd : E.X.deg ≤ D := by
    have h : E.X.deg ≤ E.deg := by rw [EffStratum.deg]; omega
    omega
  have hS0_le : S0 ≤ D := by
    have h : S0 ≤ E.deg := by rw [hS0def, EffStratum.deg]; exact Nat.le_add_left _ _
    omega
  have hU_le : U ≤ A2 n a₀ * (D + 2) * (L.length + 1) := by
    rw [hUdef]
    refine (ExDegDev.atomDeg_exEq6_le n m a₀ E L hm).trans ?_
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  -- the degree of the extended system, disjunct by disjunct
  have hdeg_eq : (exSemiPf n m E L).deg
      = (E.X.basics.map (fun B => (exBasic E.X.c E.h L B).deg)).sum := by
    rw [SemiPf.deg, exSemiPf, List.map_map]; rfl
  have hsum : (E.X.basics.map (fun B => (exBasic E.X.c E.h L B).deg)).sum
      ≤ (E.X.basics.map (fun B => 5 * n + 10 + S0 + U + B.deg)).sum :=
    List.sum_le_sum (fun B _ => ExDegDev.exBasic_deg_le E.X.c E.h L B S0 (le_of_eq hS0def.symm))
  have hsum2 : (E.X.basics.map (fun B => 5 * n + 10 + S0 + U + B.deg)).sum
      = E.X.basics.length * (5 * n + 10 + S0 + U) + E.X.deg := by
    rw [ExDegDev.sum_map_add_const]
    rw [show (E.X.basics.map (fun B => B.deg)).sum = E.X.deg from rfl]
  rw [hdeg_eq]
  calc (E.X.basics.map (fun B => (exBasic E.X.c E.h L B).deg)).sum
      ≤ (E.X.basics.map (fun B => 5 * n + 10 + S0 + U + B.deg)).sum := hsum
    _ = E.X.basics.length * (5 * n + 10 + S0 + U) + E.X.deg := hsum2
    _ ≤ (D + 1) * (5 * n + 10 + D + U) + D :=
        Nat.add_le_add (Nat.mul_le_mul hlen (by omega)) hXd
    _ ≤ (D + 1) * (5 * n + 10 + D + A2 n a₀ * (D + 2) * (L.length + 1)) + D :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
    _ ≤ A3 n a₀ * (D + 1) ^ 2 * (L.length + 1) := ExDegDev.arith_bound n a₀ D (L.length)

end Work.WilE9.Sharp
