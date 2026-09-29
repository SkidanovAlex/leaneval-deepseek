import Mathlib
import Submission.Work.Layout.MergeDefs
import Submission.Work.Layout.mergeShadow

set_option autoImplicit false

/-!
# `mrgCost` is bounded by `MRC` times the total size of the merged runs

`Work.Layout.merge_mrgCost_le` is the cost bound for the comparison phase of `Sk.mergePair`.  The
per-step charge of `mrgCost` splits into four summands (`Work.Layout.mergeShadow`): a comparison
term, the size of the moved record, the size of the record exposed by the move, and a constant.
The four are estimated separately:

* `mmc_mrgCmp_eq_cmpCost`: the total comparison term is exactly `cmpCost` of the key lists, so the
  caller's hypothesis `hcmp` (proved from `Work.Layout.merge_cmpCost`) applies;
* `mmc_mrgMov_le`: every record is moved at most once;
* `mmc_mrgExp_le`: the record exposed by a move is its successor in the same run, so each record is
  charged for exposure at most once -- this is where the "head reserve" `vszHead` is needed, since
  the exposure of a long record may happen while a short one is moved;
* `mmc_mrgTs_le`: the merge makes at most `|P| + |Q|` comparison steps.
-/

namespace Work.Layout

open HvdH Work.Layout

theorem mmc_cost_cons (KLt KSz : ℕ) (p : Val) (ps : List Val) (q : Val) (qs : List Val) :
    mrgCost KLt KSz (p :: ps) (q :: qs) =
      mrgStep KLt KSz p ps q qs +
        (if keyOf q < keyOf p then mrgCost KLt KSz (p :: ps) qs
          else mrgCost KLt KSz ps (q :: qs)) := by
  rw [mrgCost.eq_def]

theorem mmc_cost_nil_left (KLt KSz : ℕ) (Q : List Val) : mrgCost KLt KSz [] Q = 0 := by
  cases Q <;> rw [mrgCost.eq_def]

theorem mmc_cost_nil_right (KLt KSz : ℕ) (P : List Val) : mrgCost KLt KSz P [] = 0 := by
  cases P <;> rw [mrgCost.eq_def]

theorem mmc_cmpCost_cons (k : ℕ) (ks : List ℕ) (l : ℕ) (ls : List ℕ) :
    cmpCost (k :: ks) (l :: ls) =
      (k.size).size + (l.size).size + 4 +
        (if l < k then cmpCost (k :: ks) ls else cmpCost ks (l :: ls)) := by
  rw [cmpCost.eq_def]

theorem mmc_cmpCost_nil_left (ls : List ℕ) : cmpCost [] ls = 0 := by
  cases ls <;> rw [cmpCost.eq_def]

theorem mmc_cmpCost_nil_right (ks : List ℕ) : cmpCost ks [] = 0 := by
  cases ks <;> rw [cmpCost.eq_def]

theorem vszHead_eq_ite (L : List Val) :
    vszHead L = vsz (if L = [] then Val.nil else L.headD Val.nil) := by
  cases L with
  | nil => simp [vszHead]
  | cons v vs => simp [vszHead]

theorem mmc_mrgCmp_eq_cmpCost (P Q : List Val) :
    mrgCmp P Q = cmpCost (P.map keyOf) (Q.map keyOf) := by
  induction P, Q using mrgCmp.induct with
  | case1 p ps q qs ih1 ih2 =>
      simp only [List.map_cons] at ih1 ih2 ⊢
      by_cases h : keyOf q < keyOf p
      · simp only [mrgCmp_cons, mmc_cmpCost_cons, if_pos h, ih1]
      · simp only [mrgCmp_cons, mmc_cmpCost_cons, if_neg h, ih2]
  | case2 P Q h =>
      rcases P with _ | ⟨p, ps⟩ <;> rcases Q with _ | ⟨q, qs⟩
      · simp [mmc_cmpCost_nil_left]
      · simp [mmc_cmpCost_nil_left]
      · simp [mmc_cmpCost_nil_right]
      · exact False.elim (h p ps q qs rfl rfl)

theorem mmc_mrgTs_le (P Q : List Val) : mrgTs P Q ≤ P.length + Q.length := by
  induction P, Q using mrgTs.induct with
  | case1 p ps q qs ih1 ih2 =>
      simp only [List.length_cons] at ih1 ih2 ⊢
      by_cases h : keyOf q < keyOf p
      · simp only [mrgTs_cons, if_pos h]
        omega
      · simp only [mrgTs_cons, if_neg h]
        omega
  | case2 P Q h =>
      rcases P with _ | ⟨p, ps⟩ <;> rcases Q with _ | ⟨q, qs⟩
      · simp
      · simp
      · simp
      · exact False.elim (h p ps q qs rfl rfl)

theorem mmc_mrgMov_le (P Q : List Val) :
    mrgMov P Q ≤ (P.map vsz).sum + (Q.map vsz).sum + (P.length + Q.length) := by
  induction P, Q using mrgMov.induct with
  | case1 p ps q qs ih1 ih2 =>
      simp only [List.map_cons, List.sum_cons, List.length_cons] at ih1 ih2 ⊢
      by_cases h : keyOf q < keyOf p
      · simp only [mrgMov_cons, if_pos h]
        omega
      · simp only [mrgMov_cons, if_neg h]
        omega
  | case2 P Q h =>
      rcases P with _ | ⟨p, ps⟩ <;> rcases Q with _ | ⟨q, qs⟩
      · simp
      · simp
      · simp
      · exact False.elim (h p ps q qs rfl rfl)

theorem mmc_mrgExp_le (P Q : List Val) :
    mrgExp P Q + (vszHead P + vszHead Q) ≤
      (P.map vsz).sum + (Q.map vsz).sum + 2 * (P.length + Q.length) + 4 := by
  induction P, Q using mrgExp.induct with
  | case1 p ps q qs ih1 ih2 =>
      simp only [vszHead_cons, List.map_cons, List.sum_cons, List.length_cons] at ih1 ih2 ⊢
      by_cases h : keyOf q < keyOf p
      · simp only [mrgExp_cons, if_pos h]
        omega
      · simp only [mrgExp_cons, if_neg h]
        omega
  | case2 P Q h =>
      rcases P with _ | ⟨p, ps⟩ <;> rcases Q with _ | ⟨q, qs⟩
      · simp only [mrgExp_nil_left, vszHead_nil, vsz_nil, List.map_nil, List.sum_nil,
          List.length_nil]
        omega
      · simp only [mrgExp_nil_left, vszHead_nil, vsz_nil, List.map_nil, List.sum_nil,
          List.length_nil, vszHead_cons, List.map_cons, List.sum_cons, List.length_cons]
        omega
      · simp only [mrgExp_nil_right, vszHead_nil, vsz_nil, List.map_nil, List.sum_nil,
          List.length_nil, vszHead_cons, List.map_cons, List.sum_cons, List.length_cons]
        omega
      · exact False.elim (h p ps q qs rfl rfl)

theorem mmc_mrgCost_decomp (KLt KSz : ℕ) (P Q : List Val) :
    mrgCost KLt KSz P Q = cCmp KLt * mrgCmp P Q + cMov KLt * mrgMov P Q +
      cExp KSz * mrgExp P Q + cK * mrgTs P Q := by
  induction P, Q using mrgCost.induct with
  | case1 p ps q qs ih1 ih2 =>
      by_cases h : keyOf q < keyOf p
      · simp only [mmc_cost_cons, mrgCmp_cons, mrgMov_cons, mrgExp_cons, mrgTs_cons, if_pos h,
          ih1, mrgStep, vszHead_eq_ite] <;> ring
      · simp only [mmc_cost_cons, mrgCmp_cons, mrgMov_cons, mrgExp_cons, mrgTs_cons, if_neg h,
          ih2, mrgStep, vszHead_eq_ite] <;> ring
  | case2 P Q h =>
      rcases P with _ | ⟨p, ps⟩ <;> rcases Q with _ | ⟨q, qs⟩
      · simp [mmc_cost_nil_left]
      · simp [mmc_cost_nil_left]
      · simp [mmc_cost_nil_right]
      · exact False.elim (h p ps q qs rfl rfl)

theorem merge_mrgCost_le (KLt KSz : ℕ) (P Q : List Val) (hcmp : ∀ ks ls : List ℕ, (ks ++ ls).Nodup → cmpCost ks ls ≤ 20 * (((ks ++ ls).map (fun k => k.size + 2)).sum + ks.length + ls.length + 2)) (hrec : ∀ v ∈ P ++ Q, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v') (hnd : ((P ++ Q).map keyOf).Nodup) : mrgCost KLt KSz P Q ≤ MRC KLt KSz * (((P ++ Q).map vsz).sum + (P ++ Q).length + 2) := by
  set T : ℕ := (P.map vsz).sum + (Q.map vsz).sum + (P.length + Q.length) + 2 with hT
  have hgoal : ((P ++ Q).map vsz).sum + (P ++ Q).length + 2 = T := by
    simp only [hT, List.map_append, List.sum_append, List.length_append]
  have hkey : ∀ v ∈ P ++ Q, (keyOf v).size + 2 ≤ vsz v := by
    intro v hv
    obtain ⟨k, v', rfl⟩ := hrec v hv
    rw [keyOf_record, vsz_record]
    omega
  have hsumkey : ((P ++ Q).map (fun v => (keyOf v).size + 2)).sum ≤
      (P.map vsz).sum + (Q.map vsz).sum := by
    have h1 : ((P ++ Q).map (fun v => (keyOf v).size + 2)).sum ≤ ((P ++ Q).map vsz).sum :=
      List.sum_le_sum (fun i hi => hkey i hi)
    calc ((P ++ Q).map (fun v => (keyOf v).size + 2)).sum
        ≤ ((P ++ Q).map vsz).sum := h1
      _ = (P.map vsz).sum + (Q.map vsz).sum := by rw [List.map_append, List.sum_append]
  have hlen : (P.map keyOf).length + (Q.map keyOf).length = (P ++ Q).length := by simp
  have hcmpP : cmpCost (P.map keyOf) (Q.map keyOf) ≤
      20 * (((P ++ Q).map (fun v => (keyOf v).size + 2)).sum + (P ++ Q).length + 2) := by
    have h := hcmp (P.map keyOf) (Q.map keyOf) (by simpa only [List.map_append] using hnd)
    have hS : (List.map (fun k => k.size + 2) (P.map keyOf ++ Q.map keyOf)).sum =
        ((P ++ Q).map (fun v => (keyOf v).size + 2)).sum := by
      rw [List.map_append, List.sum_append, List.map_append, List.sum_append]
      congr 1
      · rw [List.map_map]; rfl
      · rw [List.map_map]; rfl
    simpa only [hS, hlen, Nat.add_assoc] using h
  have hT2 : ((P ++ Q).map (fun v => (keyOf v).size + 2)).sum + (P ++ Q).length + 2 ≤ T := by
    rw [hT, List.length_append]
    omega
  have hcmpT : cmpCost (P.map keyOf) (Q.map keyOf) ≤ 20 * T := by
    linarith
  have hA : cCmp KLt * mrgCmp P Q ≤ 20 * cCmp KLt * T := by
    rw [mmc_mrgCmp_eq_cmpCost]
    calc cCmp KLt * cmpCost (P.map keyOf) (Q.map keyOf)
        ≤ cCmp KLt * (20 * T) := Nat.mul_le_mul_left (cCmp KLt) hcmpT
      _ = 20 * cCmp KLt * T := by ring
  have hB : cMov KLt * mrgMov P Q ≤ cMov KLt * T := by
    apply Nat.mul_le_mul_left
    have h := mmc_mrgMov_le P Q
    rw [hT]
    omega
  have hC : cExp KSz * mrgExp P Q ≤ 6 * cExp KSz * T := by
    have h := mmc_mrgExp_le P Q
    have h2 : mrgExp P Q ≤ 6 * T := by rw [hT]; omega
    calc cExp KSz * mrgExp P Q ≤ cExp KSz * (6 * T) := Nat.mul_le_mul_left (cExp KSz) h2
      _ = 6 * cExp KSz * T := by ring
  have hD : cK * mrgTs P Q ≤ cK * T := by
    apply Nat.mul_le_mul_left
    have h := mmc_mrgTs_le P Q
    rw [hT]
    omega
  rw [hgoal, mmc_mrgCost_decomp]
  have hstep : cCmp KLt * mrgCmp P Q + cMov KLt * mrgMov P Q + cExp KSz * mrgExp P Q +
      cK * mrgTs P Q ≤ (20 * cCmp KLt + cMov KLt + 6 * cExp KSz + cK) * T := by
    have hexp : (20 * cCmp KLt + cMov KLt + 6 * cExp KSz + cK) * T =
        20 * cCmp KLt * T + cMov KLt * T + 6 * cExp KSz * T + cK * T := by ring
    rw [hexp]
    linarith
  have hMRC : (20 * cCmp KLt + cMov KLt + 6 * cExp KSz + cK) * T ≤ MRC KLt KSz * T := by
    apply Nat.mul_le_mul_right
    simp only [MRC, cCmp, cMov, cExp, cK]
    omega
  linarith
end Work.Layout
