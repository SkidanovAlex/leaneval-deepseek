import Mathlib.Combinatorics.HalesJewett
import Mathlib.Data.Fintype.BigOperators

open Combinatorics

namespace Commons.Combinatorics.Ramsey

abbrev HasVar {k n : ℕ} (y : Fin n → Option (Fin (k+1))) : Prop := ∃ i, y i = none

def wsubst {k m n : ℕ} (S : Subspace (Fin m) (Fin (k+1)) (Fin n))
    (x : Fin m → Option (Fin (k+1))) : Fin n → Option (Fin (k+1)) :=
  fun i => (S.idxFun i).elim some x

@[simp] lemma wsubst_apply {k m n : ℕ} (S : Subspace (Fin m) (Fin (k+1)) (Fin n))
    (x : Fin m → Option (Fin (k+1))) (i : Fin n) :
    wsubst S x i = (S.idxFun i).elim some x := rfl

lemma hasVar_wsubst {k m n : ℕ} (S : Subspace (Fin m) (Fin (k+1)) (Fin n))
    (x : Fin m → Option (Fin (k+1))) : HasVar (wsubst S x) ↔ HasVar x := by
  constructor
  · rintro ⟨i, hi⟩
    cases h : S.idxFun i with
    | inl a => simp [wsubst, h] at hi
    | inr e => exact ⟨e, by simpa [wsubst, h] using hi⟩
  · rintro ⟨e, he⟩
    obtain ⟨i, hi⟩ := S.proper e
    exact ⟨i, by simp [wsubst, hi, he]⟩

def lineOf {k m n : ℕ} (S : Subspace (Fin m) (Fin (k+1)) (Fin n))
    (x : Fin m → Option (Fin (k+1))) (hx : HasVar x) : Line (Fin (k+1)) (Fin n) :=
  ⟨wsubst S x, (hasVar_wsubst S x).mpr hx⟩

@[simp] lemma lineOf_proof_irrel {k m n : ℕ} (S : Subspace (Fin m) (Fin (k+1)) (Fin n))
    (x : Fin m → Option (Fin (k+1))) (h1 h2 : HasVar x) : lineOf S x h1 = lineOf S x h2 :=
  Line.ext rfl

def scomp {k m m' n : ℕ} (S : Subspace (Fin m) (Fin (k+1)) (Fin n))
    (T : Subspace (Fin m') (Fin (k+1)) (Fin m)) : Subspace (Fin m') (Fin (k+1)) (Fin n) :=
  ⟨fun i => (S.idxFun i).elim (fun a => Sum.inl a) (fun e => T.idxFun e), by
    intro e
    obtain ⟨i, hi⟩ := T.proper e
    obtain ⟨j, hj⟩ := S.proper i
    exact ⟨j, by rw [hj]; exact hi⟩⟩

lemma wsubst_scomp {k m m' n : ℕ} (S : Subspace (Fin m) (Fin (k+1)) (Fin n))
    (T : Subspace (Fin m') (Fin (k+1)) (Fin m)) (x : Fin m' → Option (Fin (k+1))) :
    wsubst (scomp S T) x = wsubst S (wsubst T x) := by
  funext i
  cases h : S.idxFun i <;> simp [wsubst, scomp, h]

def eSeq (k M r : ℕ) : ℕ → ℕ
  | 0 => M
  | (i+1) => eSeq k M r i - 1 + r ^ ((k+2) ^ (eSeq k M r i - 1))

def qseq (k M r : ℕ) (j : ℕ) : ℕ := eSeq k M r (M - j)

lemma eSeq_succ (k M r i : ℕ) :
    eSeq k M r (i+1) = eSeq k M r i - 1 + r ^ ((k+2) ^ (eSeq k M r i - 1)) := rfl

lemma qseq_pred (k M r : ℕ) {j : ℕ} (hj : 1 ≤ j) (hjM : j ≤ M) :
    qseq k M r (j-1) = qseq k M r j - 1 + r ^ ((k+2) ^ (qseq k M r j - 1)) := by
  have h : M - (j-1) = (M - j) + 1 := by omega
  rw [qseq, qseq, h]
  exact eSeq_succ k M r (M-j)

lemma eSeq_ge (k M r : ℕ) (hr : 1 ≤ r) : ∀ i, M ≤ eSeq k M r i := by
  intro i
  induction i with
  | zero => exact le_refl M
  | succ i ih =>
    rw [eSeq_succ]
    have : 1 ≤ r ^ ((k+2) ^ (eSeq k M r i - 1)) := Nat.one_le_pow _ _ hr
    omega

lemma qseq_ge_M (k M r : ℕ) (hr : 1 ≤ r) (j : ℕ) : M ≤ qseq k M r j :=
  eSeq_ge k M r hr (M - j)

/-- The block of `d` letters `a...ab...b` with `t` copies of `a`. -/
def blk (k d : ℕ) (hk : 1 ≤ k) (t : ℕ) : Fin d → Option (Fin (k+1)) :=
  fun s => if (s:ℕ) < t then some (Fin.last k) else some ⟨k-1, by omega⟩

/-- Insert the block `blk t` at position `j-1` of the word `z`. -/
def Qword (k d j qj1 qj : ℕ) (hk : 1 ≤ k) (hjqj : j ≤ qj) (h3 : qj1 = qj - 1 + d)
    (t : ℕ) (z : Fin (qj - 1) → Option (Fin (k+1))) : Fin qj1 → Option (Fin (k+1)) :=
  fun p => if hp1 : (p:ℕ) < j-1 then z ⟨p, by omega⟩
    else if hp2 : (p:ℕ) < j-1 + d then blk k d hk t ⟨(p:ℕ) - (j-1), by omega⟩
    else z ⟨(p:ℕ) - d, by omega⟩

end Commons.Combinatorics.Ramsey

namespace Commons.Combinatorics.Ramsey

/-- The `j`-th step word `w'`: identity on the first `j-1` positions, then a block of `t1`
copies of `♯k`, `t2-t1` copies of variable `j-1`, then `d-t2` copies of `k-1`, then variables. -/
def Wword (k j d qj1 qj t1 t2 : ℕ) (hk : 1 ≤ k) (hj1 : 1 ≤ j) (hjqj : j ≤ qj)
    (h3 : qj1 = qj - 1 + d) (ht12 : t1 < t2) (ht2d : t2 ≤ d) :
    Subspace (Fin qj) (Fin (k+1)) (Fin qj1) :=
  ⟨fun p => if hp1 : (p:ℕ) < j-1 then Sum.inr (⟨p, by omega⟩ : Fin qj)
    else if hp2 : (p:ℕ) < j-1 + t1 then Sum.inl (Fin.last k)
    else if hp3 : (p:ℕ) < j-1 + t2 then Sum.inr (⟨j-1, by omega⟩ : Fin qj)
    else if hp4 : (p:ℕ) < j-1 + d then Sum.inl (⟨k-1, by omega⟩ : Fin (k+1))
    else Sum.inr (⟨(p:ℕ) - d + 1, by omega⟩ : Fin qj),
   by
    intro e
    rcases lt_trichotomy (e:ℕ) (j-1) with hlt | heq | hgt
    · refine ⟨⟨(e:ℕ), by omega⟩, ?_⟩
      simp only [dif_pos (show ((⟨(e:ℕ), by omega⟩ : Fin qj1):ℕ) < j-1 from by
        simp only [Fin.val_mk]; omega)]
    · refine ⟨⟨j-1+t1, by omega⟩, ?_⟩
      simp only [dif_neg (show ¬ ((⟨j-1+t1, by omega⟩ : Fin qj1):ℕ) < j-1 from by
                   simp only [Fin.val_mk]; omega),
                 dif_neg (show ¬ ((⟨j-1+t1, by omega⟩ : Fin qj1):ℕ) < j-1+t1 from by
                   simp only [Fin.val_mk]; omega),
                 dif_pos (show ((⟨j-1+t1, by omega⟩ : Fin qj1):ℕ) < j-1+t2 from by
                   simp only [Fin.val_mk]; omega)]
      exact congrArg Sum.inr (Fin.ext (by simp only [Fin.val_mk]; omega))
    · refine ⟨⟨(e:ℕ)+d-1, by omega⟩, ?_⟩
      simp only [dif_neg (show ¬ ((⟨(e:ℕ)+d-1, by omega⟩ : Fin qj1):ℕ) < j-1 from by
                   simp only [Fin.val_mk]; omega),
                 dif_neg (show ¬ ((⟨(e:ℕ)+d-1, by omega⟩ : Fin qj1):ℕ) < j-1+t1 from by
                   simp only [Fin.val_mk]; omega),
                 dif_neg (show ¬ ((⟨(e:ℕ)+d-1, by omega⟩ : Fin qj1):ℕ) < j-1+t2 from by
                   simp only [Fin.val_mk]; omega),
                 dif_neg (show ¬ ((⟨(e:ℕ)+d-1, by omega⟩ : Fin qj1):ℕ) < j-1+d from by
                   simp only [Fin.val_mk]; omega)]
      exact congrArg Sum.inr (Fin.ext (by simp only [Fin.val_mk]; omega))⟩


/-- `Qword t z` is a variable word whenever `z` is. -/
lemma Qword_hasVar {k d j qj1 qj : ℕ} (hk : 1 ≤ k) (hjqj : j ≤ qj) (h3 : qj1 = qj - 1 + d)
    (t : ℕ) (z : Fin (qj - 1) → Option (Fin (k+1))) (hz : HasVar z) :
    HasVar (Qword k d j qj1 qj hk hjqj h3 t z) := by
  obtain ⟨s, hs⟩ := hz
  rcases lt_or_ge (s:ℕ) (j-1) with hlt | hge
  · refine ⟨⟨(s:ℕ), by omega⟩, ?_⟩
    rw [Qword]
    simp only [dif_pos (show (((⟨(s:ℕ), by omega⟩ : Fin qj1):ℕ)) < j-1 from by simp only [Fin.val_mk]; omega)]
    exact (show z (⟨(s:ℕ), by omega⟩ : Fin (qj-1)) = none from by rw [show (⟨(s:ℕ), by omega⟩ : Fin (qj-1)) = s from Fin.ext rfl]; exact hs)
  · refine ⟨⟨(s:ℕ)+d, by omega⟩, ?_⟩
    rw [Qword]
    simp only [dif_neg (show ¬ (((⟨(s:ℕ)+d, by omega⟩ : Fin qj1):ℕ)) < j-1 from by simp only [Fin.val_mk]; omega),
               dif_neg (show ¬ (((⟨(s:ℕ)+d, by omega⟩ : Fin qj1):ℕ)) < j-1 + d from by simp only [Fin.val_mk]; omega)]
    exact (show z (⟨(s:ℕ)+d-d, by omega⟩ : Fin (qj-1)) = none from by
      rw [show (⟨(s:ℕ)+d-d, by omega⟩ : Fin (qj-1)) = s from Fin.ext (by simp only [Fin.val_mk]; omega)]
      exact hs)

/-- Numeric: position `j-1` is a valid position of a `qseq`-dimensional word. -/
lemma step_jj_lt (k M r : ℕ) (hr : 1 ≤ r) (j : ℕ) (hj1 : 1 ≤ j) (hjM : j ≤ M) : j-1 < qseq k M r j := by
  have := qseq_ge_M k M r hr j; omega

/-- `wsubst (Wword ...) x` equals the corresponding `Qword t2` insertion. -/
lemma wsubst_Wword_eq_Qword_t2 {k j d qj1 qj t1 t2 : ℕ} (hk : 1 ≤ k) (hj1 : 1 ≤ j)
    (hjqj : j ≤ qj) (h3 : qj1 = qj - 1 + d) (ht12 : t1 < t2) (ht2d : t2 ≤ d)
    (x : Fin qj → Option (Fin (k+1))) (hxA : x ⟨j-1, by omega⟩ = some (Fin.last k)) :
    wsubst (Wword k j d qj1 qj t1 t2 hk hj1 hjqj h3 ht12 ht2d) x
      = Qword k d j qj1 qj hk hjqj h3 t2
          (fun s => if (s:ℕ) < j-1 then x ⟨s, by omega⟩ else x ⟨(s:ℕ)+1, by omega⟩) := by
  funext p
  simp only [wsubst_apply, Wword, Qword, blk, Fin.val_mk]
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  all_goals try (exfalso; omega)
  all_goals simp only [Sum.elim_inr, Sum.elim_inl]
  all_goals first
    | rfl
    | (congr 1; exact Fin.ext rfl)
    | (congr 1; rfl)
    | (exact hxA)

/-- `wsubst (Wword ...) y` equals the corresponding `Qword t1` insertion (with `b` at pos `j-1`). -/
lemma wsubst_Wword_eq_Qword_t1 {k j d qj1 qj t1 t2 : ℕ} (hk : 1 ≤ k) (hj1 : 1 ≤ j)
    (hjqj : j ≤ qj) (h3 : qj1 = qj - 1 + d) (ht12 : t1 < t2) (ht2d : t2 ≤ d)
    (y : Fin qj → Option (Fin (k+1))) (hyB : y ⟨j-1, by omega⟩ = some ⟨k-1, by omega⟩) :
    wsubst (Wword k j d qj1 qj t1 t2 hk hj1 hjqj h3 ht12 ht2d) y
      = Qword k d j qj1 qj hk hjqj h3 t1
          (fun s => if (s:ℕ) < j-1 then y ⟨s, by omega⟩ else y ⟨(s:ℕ)+1, by omega⟩) := by
  funext p
  simp only [wsubst_apply, Wword, Qword, blk, Fin.val_mk]
  split_ifs with h1 h2 h3' h4 h5 h6 h7
  all_goals try (exfalso; omega)
  all_goals simp only [Sum.elim_inr, Sum.elim_inl]
  all_goals first
    | rfl
    | (congr 1; exact Fin.ext rfl)
    | (congr 1; rfl)
    | (exact hyB)

/-- Transfer of colours through equal `wsubst`. -/
lemma C_lineOf_congr {k m m' n r : ℕ} (C : Line (Fin (k+1)) (Fin n) → Fin r)
    {S : Subspace (Fin m) (Fin (k+1)) (Fin n)} {S' : Subspace (Fin m') (Fin (k+1)) (Fin n)}
    {x : Fin m → Option (Fin (k+1))} {x' : Fin m' → Option (Fin (k+1))}
    (h : wsubst S x = wsubst S' x') (hx : HasVar x) (hx' : HasVar x') :
    C (lineOf S x hx) = C (lineOf S' x' hx') := by
  have hh : lineOf S x hx = lineOf S' x' hx' := Line.ext h
  rw [hh]

/-- The key pigeonhole argument. -/
lemma step_key {k N r : ℕ} (hk : 1 ≤ k) (hr : 0 < r) (j d qj qj1 : ℕ) (hj1 : 1 ≤ j) (hjqj : j ≤ qj)
    (h3 : qj1 = qj - 1 + d) {t1 t2 : Fin (d+1)} (ht12 : t1.val < t2.val)
    (w : Subspace (Fin qj1) (Fin (k+1)) (Fin N))
    (C : Line (Fin (k+1)) (Fin N) → Fin r)
    (T : Fin (d+1) → (Fin (qj-1) → Option (Fin (k+1))) → Fin r)
    (hT : ∀ (t : Fin (d+1)) (z : Fin (qj-1) → Option (Fin (k+1))),
      T t z = if hz : HasVar z then
        C (lineOf w (Qword k d j qj1 qj hk hjqj h3 t.val z) (Qword_hasVar hk hjqj h3 t.val z hz))
      else ⟨0, hr⟩)
    (heq : T t1 = T t2)
    (x y : Fin qj → Option (Fin (k+1))) (hx : HasVar x) (hy : HasVar y)
    (hxA : x ⟨j-1, by omega⟩ = some (Fin.last k))
    (hyB : y ⟨j-1, by omega⟩ = some ⟨k-1, by omega⟩)
    (hxy : ∀ i, i ≠ ⟨j-1, by omega⟩ → x i = y i) :
    C (lineOf (scomp w (Wword k j d qj1 qj t1.val t2.val hk hj1 hjqj h3 ht12 (by omega))) x hx)
      = C (lineOf (scomp w (Wword k j d qj1 qj t1.val t2.val hk hj1 hjqj h3 ht12 (by omega))) y hy) := by
  classical
  let z : Fin (qj-1) → Option (Fin (k+1)) :=
    fun s => if (s:ℕ) < j-1 then x ⟨s, by omega⟩ else x ⟨(s:ℕ)+1, by omega⟩
  have hz : HasVar z := by
    obtain ⟨p, hp⟩ := hx
    rcases lt_trichotomy (p:ℕ) (j-1) with h | h | h
    · refine ⟨⟨(p:ℕ), by omega⟩, ?_⟩
      show (if ((⟨(p:ℕ), by omega⟩ : Fin (qj-1)):ℕ) < j-1 then x ⟨_,_⟩ else x ⟨_,_⟩) = none
      rw [if_pos (by simp only [Fin.val_mk]; omega)]
      rw [show (⟨(p:ℕ), by omega⟩ : Fin qj) = p from Fin.ext (by simp only [Fin.val_mk])]
      exact hp
    · exfalso
      have hp' : x p = some (Fin.last k) := by
        rw [show p = (⟨j-1, by omega⟩ : Fin qj) from Fin.ext (by simp only [Fin.val_mk]; omega)]
        exact hxA
      rw [hp] at hp'
      cases hp'
    · refine ⟨⟨(p:ℕ)-1, by omega⟩, ?_⟩
      show (if ((⟨(p:ℕ)-1, by omega⟩ : Fin (qj-1)):ℕ) < j-1 then x ⟨_,_⟩ else x ⟨_,_⟩) = none
      rw [if_neg (by simp only [Fin.val_mk]; omega)]
      convert hp using 2
      exact Fin.ext (by simp only [Fin.val_mk]; omega)
  have hQ2 : wsubst (Wword k j d qj1 qj t1.val t2.val hk hj1 hjqj h3 ht12 (by omega)) x
      = Qword k d j qj1 qj hk hjqj h3 t2.val z :=
    wsubst_Wword_eq_Qword_t2 hk hj1 hjqj h3 ht12 (by omega) x hxA
  have hQ1 : wsubst (Wword k j d qj1 qj t1.val t2.val hk hj1 hjqj h3 ht12 (by omega)) y
      = Qword k d j qj1 qj hk hjqj h3 t1.val z := by
    rw [wsubst_Wword_eq_Qword_t1 hk hj1 hjqj h3 ht12 (by omega) y hyB]
    congr 1
    funext s
    show (if (s:ℕ) < j-1 then y ⟨_,_⟩ else y ⟨_,_⟩) = (if (s:ℕ) < j-1 then x ⟨_,_⟩ else x ⟨_,_⟩)
    by_cases h : (s:ℕ) < j-1
    · rw [if_pos h, if_pos h]
      exact (hxy ⟨(s:ℕ), by omega⟩ (by intro hh; have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega)).symm
    · rw [if_neg h, if_neg h]
      exact (hxy ⟨(s:ℕ)+1, by omega⟩ (by intro hh; have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega)).symm
  calc C (lineOf (scomp w (Wword k j d qj1 qj t1.val t2.val hk hj1 hjqj h3 ht12 (by omega))) x hx)
      = C (lineOf w (Qword k d j qj1 qj hk hjqj h3 t2.val z) (Qword_hasVar hk hjqj h3 t2.val z hz)) :=
          C_lineOf_congr C (by rw [wsubst_scomp, hQ2]) hx _
    _ = T t2 z := ((hT t2 z).trans (dif_pos hz)).symm
    _ = T t1 z := congrFun heq.symm z
    _ = C (lineOf w (Qword k d j qj1 qj hk hjqj h3 t1.val z) (Qword_hasVar hk hjqj h3 t1.val z hz)) :=
          (hT t1 z).trans (dif_pos hz)
    _ = C (lineOf (scomp w (Wword k j d qj1 qj t1.val t2.val hk hj1 hjqj h3 ht12 (by omega))) y hy) :=
          C_lineOf_congr C (by rw [wsubst_scomp, hQ1]) _ hy


/-- The block length at step `j`. -/
abbrev dd (k M r j : ℕ) : ℕ := r ^ ((k+2) ^ (qseq k M r j - 1))

/-- The concrete step word built from a pair `(t1,t2)`. -/
noncomputable def WwordOf (k M r j : ℕ) (hk : 1 ≤ k) (hr : 0 < r) (hj1 : 1 ≤ j) (hjM : j ≤ M)
    (t1 t2 : ℕ) (ht12 : t1 < t2) (ht2d : t2 ≤ dd k M r j) :
    Subspace (Fin (qseq k M r j)) (Fin (k+1)) (Fin (qseq k M r (j-1))) :=
  Wword k j (dd k M r j) (qseq k M r (j-1)) (qseq k M r j) t1 t2
    hk hj1 (by have := qseq_ge_M k M r hr j; omega) (qseq_pred k M r hj1 hjM) ht12 ht2d

/-- The `j`-th step of the inductive construction (existence of a suitable subspace). -/
theorem steppair_exists {k M r N : ℕ} (hk : 1 ≤ k) (hr : 0 < r) (hM : 1 ≤ M)
    (j : ℕ) (hj1 : 1 ≤ j) (hjM : j ≤ M)
    (w : Subspace (Fin (qseq k M r (j-1))) (Fin (k+1)) (Fin N))
    (C : Line (Fin (k+1)) (Fin N) → Fin r) :
    ∃ S : Subspace (Fin (qseq k M r j)) (Fin (k+1)) (Fin (qseq k M r (j-1))),
      (∃ (t1 t2 : Fin (dd k M r j + 1)) (ht12 : t1.val < t2.val),
        S = WwordOf k M r j hk hr hj1 hjM t1.val t2.val ht12 (by omega)) ∧
      (∀ x y (hx : HasVar x) (hy : HasVar y),
        x ⟨j-1, step_jj_lt k M r hr j hj1 hjM⟩ = some (Fin.last k) →
        y ⟨j-1, step_jj_lt k M r hr j hj1 hjM⟩ = some ⟨k-1, by omega⟩ →
        (∀ i, i ≠ ⟨j-1, step_jj_lt k M r hr j hj1 hjM⟩ → x i = y i) →
        C (lineOf (scomp w S) x hx) = C (lineOf (scomp w S) y hy)) := by
  have hr1 : 1 ≤ r := hr
  let qj := qseq k M r j
  let qj1 := qseq k M r (j-1)
  let d := r ^ ((k+2) ^ (qj - 1))
  have h3 : qj1 = qj - 1 + d := qseq_pred k M r hj1 hjM
  have hjqj : j ≤ qj := le_trans hjM (qseq_ge_M k M r hr1 j)
  have hcard1 : Fintype.card (Fin (qj-1) → Option (Fin (k+1))) = (k+2)^(qj-1) := by
    rw [Fintype.card_fun, Fintype.card_option, Fintype.card_fin, Fintype.card_fin]
  let T : Fin (d+1) → (Fin (qj-1) → Option (Fin (k+1))) → Fin r := fun t z =>
    if hz : HasVar z then
      C (lineOf w (Qword k d j qj1 qj hk hjqj h3 t.val z) (Qword_hasVar hk hjqj h3 t.val z hz))
    else ⟨0, hr⟩
  have hT : ∀ (t : Fin (d+1)) (z : Fin (qj-1) → Option (Fin (k+1))),
      T t z = if hz : HasVar z then
        C (lineOf w (Qword k d j qj1 qj hk hjqj h3 t.val z) (Qword_hasVar hk hjqj h3 t.val z hz))
      else ⟨0, hr⟩ := fun t z => rfl
  have hcard2 : Fintype.card ((Fin (qj-1) → Option (Fin (k+1))) → Fin r) = d := by
    rw [Fintype.card_fun, hcard1, Fintype.card_fin]
  have hnotinj : ¬ Function.Injective T := by
    intro hinj
    have hle := Fintype.card_le_of_injective T hinj
    rw [Fintype.card_fin, hcard2] at hle
    omega
  obtain ⟨t1, t2, heq, hne⟩ := Function.not_injective_iff.mp hnotinj
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨WwordOf k M r j hk hr hj1 hjM t1.val t2.val hlt (Nat.le_of_lt_succ t2.isLt), ?_, ?_⟩
    · exact ⟨t1, t2, hlt, rfl⟩
    · intro x y hx hy hxA hyB hxy
      exact step_key hk hr j d qj qj1 hj1 hjqj h3 hlt w C T hT heq x y hx hy hxA hyB hxy
  · refine ⟨WwordOf k M r j hk hr hj1 hjM t2.val t1.val hgt (Nat.le_of_lt_succ t1.isLt), ?_, ?_⟩
    · exact ⟨t2, t1, hgt, rfl⟩
    · intro x y hx hy hxA hyB hxy
      exact step_key hk hr j d qj qj1 hj1 hjqj h3 hgt w C T hT heq.symm x y hx hy hxA hyB hxy

/-- The `j`-th step subspace. -/
noncomputable def stepSub {k M r N : ℕ} (hk : 1 ≤ k) (hr : 0 < r) (hM : 1 ≤ M)
    (j : ℕ) (hj1 : 1 ≤ j) (hjM : j ≤ M)
    (w : Subspace (Fin (qseq k M r (j-1))) (Fin (k+1)) (Fin N))
    (C : Line (Fin (k+1)) (Fin N) → Fin r) :
    Subspace (Fin (qseq k M r j)) (Fin (k+1)) (Fin (qseq k M r (j-1))) :=
  Classical.choose (steppair_exists hk hr hM j hj1 hjM w C)

lemma stepSub_isWword {k M r N : ℕ} (hk : 1 ≤ k) (hr : 0 < r) (hM : 1 ≤ M)
    (j : ℕ) (hj1 : 1 ≤ j) (hjM : j ≤ M)
    (w : Subspace (Fin (qseq k M r (j-1))) (Fin (k+1)) (Fin N))
    (C : Line (Fin (k+1)) (Fin N) → Fin r) :
    ∃ (t1 t2 : Fin (dd k M r j + 1)) (ht12 : t1.val < t2.val),
      stepSub hk hr hM j hj1 hjM w C = WwordOf k M r j hk hr hj1 hjM t1.val t2.val ht12 (Nat.le_of_lt_succ t2.isLt) :=
  (Classical.choose_spec (steppair_exists hk hr hM j hj1 hjM w C)).1

lemma stepSub_prop {k M r N : ℕ} (hk : 1 ≤ k) (hr : 0 < r) (hM : 1 ≤ M)
    (j : ℕ) (hj1 : 1 ≤ j) (hjM : j ≤ M)
    (w : Subspace (Fin (qseq k M r (j-1))) (Fin (k+1)) (Fin N))
    (C : Line (Fin (k+1)) (Fin N) → Fin r) :
    ∀ x y (hx : HasVar x) (hy : HasVar y),
      x ⟨j-1, step_jj_lt k M r hr j hj1 hjM⟩ = some (Fin.last k) →
      y ⟨j-1, step_jj_lt k M r hr j hj1 hjM⟩ = some ⟨k-1, by omega⟩ →
      (∀ i, i ≠ ⟨j-1, step_jj_lt k M r hr j hj1 hjM⟩ → x i = y i) →
      C (lineOf (scomp w (stepSub hk hr hM j hj1 hjM w C)) x hx)
        = C (lineOf (scomp w (stepSub hk hr hM j hj1 hjM w C)) y hy) :=
  (Classical.choose_spec (steppair_exists hk hr hM j hj1 hjM w C)).2


lemma WwordOf_idx_lt {k M r j : ℕ} (hk : 1 ≤ k) (hr : 0 < r) (hj1 : 1 ≤ j) (hjM : j ≤ M)
    (t1 t2 : ℕ) (ht12 : t1 < t2) (ht2d : t2 ≤ dd k M r j)
    (p : Fin (qseq k M r (j-1))) (hp : (p:ℕ) < j-1) :
    (WwordOf k M r j hk hr hj1 hjM t1 t2 ht12 ht2d).idxFun p
      = Sum.inr (⟨p, by have := qseq_ge_M k M r hr j; omega⟩ : Fin (qseq k M r j)) := by
  simp only [WwordOf, Wword, dif_pos hp]

lemma WwordOf_idx_ge {k M r j : ℕ} (hk : 1 ≤ k) (hr : 0 < r) (hj1 : 1 ≤ j) (hjM : j ≤ M)
    (t1 t2 : ℕ) (ht12 : t1 < t2) (ht2d : t2 ≤ dd k M r j)
    (p : Fin (qseq k M r (j-1))) (hp : j-1 ≤ (p:ℕ)) :
    (∃ c : Fin (k+1), (WwordOf k M r j hk hr hj1 hjM t1 t2 ht12 ht2d).idxFun p = Sum.inl c) ∨
      (∃ e : Fin (qseq k M r j),
        (WwordOf k M r j hk hr hj1 hjM t1 t2 ht12 ht2d).idxFun p = Sum.inr e ∧ j-1 ≤ (e:ℕ)) := by
  have hjqj : j ≤ qseq k M r j := by have := qseq_ge_M k M r hr j; omega
  have h3 : qseq k M r (j-1) = qseq k M r j - 1 + dd k M r j := qseq_pred k M r hj1 hjM
  simp only [WwordOf, Wword]
  by_cases h1 : (p:ℕ) < j-1 + t1
  · left
    rw [dif_neg (by omega), dif_pos h1]
    exact ⟨Fin.last k, rfl⟩
  · by_cases h2 : (p:ℕ) < j-1 + t2
    · right
      rw [dif_neg (by omega), dif_neg h1, dif_pos h2]
      exact ⟨⟨j-1, by omega⟩, rfl, by simp only [Fin.val_mk]; omega⟩
    · by_cases h4 : (p:ℕ) < j-1 + dd k M r j
      · left
        rw [dif_neg (by omega), dif_neg h1, dif_neg h2, dif_pos h4]
        exact ⟨⟨k-1, by omega⟩, rfl⟩
      · right
        rw [dif_neg (by omega), dif_neg h1, dif_neg h2, dif_neg h4]
        refine ⟨⟨(p:ℕ)-dd k M r j+1, by omega⟩, rfl, ?_⟩
        simp only [Fin.val_mk]; omega



/-- The "identity-like" subspace using `m` of the `n` available directions. -/
def identLike {k m n : ℕ} (h : m ≤ n) : Subspace (Fin m) (Fin (k+1)) (Fin n) :=
  ⟨fun i => if h' : (i : ℕ) < m then Sum.inr ⟨i, h'⟩ else Sum.inl ⟨0, Nat.succ_pos k⟩, by
    intro e
    refine ⟨⟨e, lt_of_lt_of_le e.isLt h⟩, ?_⟩
    rw [dif_pos e.isLt]⟩

/-- The recursive construction of the subspace. -/
noncomputable def buildW {k M r N : ℕ} (hk : 1 ≤ k) (hr : 0 < r) (hM : 1 ≤ M)
    (hN : qseq k M r 0 ≤ N) (C : Line (Fin (k+1)) (Fin N) → Fin r) :
    (j : ℕ) → j ≤ M → Subspace (Fin (qseq k M r j)) (Fin (k+1)) (Fin N)
  | 0, _ => identLike hN
  | (j+1), h =>
      scomp (buildW hk hr hM hN C j (Nat.le_of_succ_le h))
            (stepSub hk hr hM (j+1) (by omega) h (buildW hk hr hM hN C j (Nat.le_of_succ_le h)) C)

/-- `Subspace.reindex` acts on substitutions by precomposition. -/
lemma reindex_wsubst {k m m' n : ℕ} (S : Subspace (Fin m) (Fin (k+1)) (Fin n))
    (e : Fin m ≃ Fin m') (x : Fin m' → Option (Fin (k+1))) :
    wsubst (S.reindex e (Equiv.refl (Fin (k+1))) (Equiv.refl (Fin n))) x = wsubst S (x ∘ e) := by
  funext i
  rw [wsubst_apply, wsubst_apply]
  cases h : S.idxFun i with
  | inl a => simp [Subspace.reindex, h]
  | inr d => simp [Subspace.reindex, h]

lemma eSeq_mono (k M r : ℕ) (hr : 1 ≤ r) : ∀ i i' : ℕ, i ≤ i' → eSeq k M r i ≤ eSeq k M r i' := by
  intro i i' h
  induction i', h using Nat.le_induction with
  | base => exact le_rfl
  | succ i' hi ih =>
      refine le_trans ih ?_
      rw [eSeq_succ]
      have : 1 ≤ r ^ ((k+2) ^ (eSeq k M r i' - 1)) := Nat.one_le_pow _ _ hr
      omega

lemma qseq_anti (k M r : ℕ) (hr : 1 ≤ r) {j i : ℕ} (h : j ≤ i) :
    qseq k M r i ≤ qseq k M r j := by
  simp only [qseq]
  exact eSeq_mono k M r hr (M - i) (M - j) (by omega)

lemma qseq_self (k M r : ℕ) : qseq k M r M = M := by
  rw [qseq, Nat.sub_self]; rfl

/-- Unfolding of one `buildW` step. -/
lemma buildW_succ {k M r N : ℕ} (hk : 1 ≤ k) (hr : 0 < r) (hM : 1 ≤ M)
    (hN : qseq k M r 0 ≤ N) (C : Line (Fin (k+1)) (Fin N) → Fin r)
    (j : ℕ) (hj : j+1 ≤ M) :
    buildW hk hr hM hN C (j+1) hj
      = scomp (buildW hk hr hM hN C j (Nat.le_of_succ_le hj))
              (stepSub hk hr hM (j+1) (by omega) hj (buildW hk hr hM hN C j (Nat.le_of_succ_le hj)) C) := rfl


/-- The main induction: `buildW j` is insensitive to a single `(a,b)`-swap at any position `< j`. -/
theorem buildW_prop {k M r N : ℕ} (hk : 1 ≤ k) (hr : 0 < r) (hM : 1 ≤ M)
    (hN : qseq k M r 0 ≤ N) (C : Line (Fin (k+1)) (Fin N) → Fin r) :
    ∀ (j : ℕ) (hjM : j ≤ M)
      (σ σ' : Fin (qseq k M r j) → Option (Fin (k+1))) (hσ : HasVar σ) (hσ' : HasVar σ')
      (p : Fin (qseq k M r j)), (p:ℕ) < j →
      σ p = some (Fin.last k) → σ' p = some ⟨k-1, by omega⟩ →
      (∀ i, i ≠ p → σ i = σ' i) →
      C (lineOf (buildW hk hr hM hN C j hjM) σ hσ)
        = C (lineOf (buildW hk hr hM hN C j hjM) σ' hσ') := by
  intro j
  induction j with
  | zero =>
      intro hjM σ σ' hσ hσ' p hp
      omega
  | succ j ih =>
      intro hjM σ σ' hσ hσ' p hp hσA hσ'B hagree
      obtain ⟨t1, t2, ht12, hSw⟩ := stepSub_isWword hk hr hM (j+1) (by omega) hjM
        (buildW hk hr hM hN C j (Nat.le_of_succ_le hjM)) C
      rw [buildW_succ hk hr hM hN C j hjM, hSw]
      set u := WwordOf k M r (j+1) hk hr (by omega) hjM t1.val t2.val ht12 (Nat.le_of_lt_succ t2.isLt) with hu
      set wj := buildW hk hr hM hN C j (Nat.le_of_succ_le hjM) with hwj
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hp) with hpj | hpj
      · -- p.val < j : transfer to wj
        have hle : qseq k M r (j+1) ≤ qseq k M r j := qseq_anti k M r hr (Nat.le_succ j)
        let p' : Fin (qseq k M r j) := Fin.castLE hle p
        have hp' : (p':ℕ) < j := by simp only [p', Fin.val_castLE]; exact hpj
        have hσ0 : HasVar (wsubst u σ) := (hasVar_wsubst u σ).mpr hσ
        have hσ0' : HasVar (wsubst u σ') := (hasVar_wsubst u σ').mpr hσ'
        have hA0 : wsubst u σ p' = some (Fin.last k) := by
          rw [wsubst_apply, hu, WwordOf_idx_lt hk hr (by omega) hjM t1.val t2.val ht12
            (Nat.le_of_lt_succ t2.isLt) p' hp', Sum.elim_inr]
          exact hσA
        have hB0 : wsubst u σ' p' = some ⟨k-1, by omega⟩ := by
          rw [wsubst_apply, hu, WwordOf_idx_lt hk hr (by omega) hjM t1.val t2.val ht12
            (Nat.le_of_lt_succ t2.isLt) p' hp', Sum.elim_inr]
          exact hσ'B
        have hagree0 : ∀ q, q ≠ p' → wsubst u σ q = wsubst u σ' q := by
          intro q hq
          rw [wsubst_apply, wsubst_apply]
          rw [hu]
          by_cases hqj : (q:ℕ) < j
          · rw [WwordOf_idx_lt hk hr (by omega) hjM t1.val t2.val ht12 (Nat.le_of_lt_succ t2.isLt) q hqj,
                Sum.elim_inr]
            apply hagree
            intro hh
            apply hq
            apply Fin.ext
            have hh' : (q:ℕ) = (p:ℕ) := congrArg Fin.val hh
            have hpv : (p':ℕ) = (p:ℕ) := Fin.val_castLE hle p
            omega
          · have hge : j ≤ (q:ℕ) := by omega
            obtain hc | hc := WwordOf_idx_ge hk hr (by omega) hjM t1.val t2.val ht12 (Nat.le_of_lt_succ t2.isLt) q hge
            · obtain ⟨c, hc⟩ := hc; rw [hc]; simp only [Sum.elim_inl]
            · obtain ⟨e, he, hej⟩ := hc
              rw [he]
              apply hagree
              intro hh
              have : (e:ℕ) = p.val := congrArg Fin.val hh
              omega
        have ihj := ih (Nat.le_of_succ_le hjM) (wsubst u σ) (wsubst u σ') hσ0 hσ0' p' hp' hA0 hB0 hagree0
        trans C (lineOf wj (wsubst u σ) hσ0)
        · exact C_lineOf_congr C (by rw [wsubst_scomp]) hσ hσ0
        · rw [ihj]
          exact (C_lineOf_congr C (by rw [wsubst_scomp]) hσ' hσ0').symm
      · -- p.val = j : use stepSub_prop
        have hp_eq : p = (⟨j, by have := qseq_ge_M k M r hr (j+1); omega⟩ : Fin (qseq k M r (j+1))) := Fin.ext hpj
        rw [hp_eq] at hσA hσ'B hagree
        have hprop := stepSub_prop hk hr hM (j+1) (by omega) hjM
          (buildW hk hr hM hN C j (Nat.le_of_succ_le hjM)) C σ σ' hσ hσ' hσA hσ'B hagree
        rw [hSw] at hprop
        exact hprop


/-- Reducing a coordinate-wise swap to a chain of single swaps. -/
lemma insens_chain {k M r N : ℕ} (hk : 1 ≤ k) (hr : 0 < r) (hM : 1 ≤ M)
    (hN : qseq k M r 0 ≤ N) (C : Line (Fin (k+1)) (Fin N) → Fin r)
    (σ σ' : Fin (qseq k M r M) → Option (Fin (k+1))) (hσ : HasVar σ) (hσ' : HasVar σ')
    (hKnn : ∀ i, σ i = none ↔ σ' i = none)
    (hK : ∀ i, σ i = σ' i ∨ (σ i = some (Fin.last k) ∧ σ' i = some ⟨k-1, by omega⟩) ∨
        (σ' i = some (Fin.last k) ∧ σ i = some ⟨k-1, by omega⟩)) :
    C (lineOf (buildW hk hr hM hN C M le_rfl) σ hσ)
      = C (lineOf (buildW hk hr hM hN C M le_rfl) σ' hσ') := by
  classical
  suffices h : ∀ (n : ℕ) (σ σ' : Fin (qseq k M r M) → Option (Fin (k+1))) (hσ : HasVar σ) (hσ' : HasVar σ'),
      (∀ i, σ i = none ↔ σ' i = none) →
      (∀ i, σ i = σ' i ∨ (σ i = some (Fin.last k) ∧ σ' i = some ⟨k-1, by omega⟩) ∨
        (σ' i = some (Fin.last k) ∧ σ i = some ⟨k-1, by omega⟩)) →
      (Finset.univ.filter (fun i => σ i ≠ σ' i)).card = n →
      C (lineOf (buildW hk hr hM hN C M le_rfl) σ hσ)
        = C (lineOf (buildW hk hr hM hN C M le_rfl) σ' hσ') from
    h _ σ σ' hσ hσ' hKnn hK rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro σ σ' hσ hσ' hKnn hK hcard
    by_cases hD : (Finset.univ.filter (fun i => σ i ≠ σ' i)).Nonempty
    · obtain ⟨i₀, hi₀mem⟩ := hD
      have hi₀ : σ i₀ ≠ σ' i₀ := (Finset.mem_filter.mp hi₀mem).2
      have hi₀M : (i₀:ℕ) < M := lt_of_lt_of_eq i₀.isLt (qseq_self k M r)
      let σ'' : Fin (qseq k M r M) → Option (Fin (k+1)) := fun i => if i = i₀ then σ' i₀ else σ i
      have hσ''i : σ'' i₀ = σ' i₀ := by
        show (if i₀ = i₀ then σ' i₀ else σ i₀) = σ' i₀
        rw [if_pos rfl]
      have hσ''ne : ∀ i, i ≠ i₀ → σ'' i = σ i := by
        intro i hi
        show (if i = i₀ then σ' i₀ else σ i) = σ i
        rw [if_neg hi]
      have hσ'' : HasVar σ'' := by
        obtain ⟨j, hj⟩ := hσ
        by_cases hji : j = i₀
        · exfalso
          have h1 : σ i₀ = none := by rw [← hji]; exact hj
          exact hi₀ (by rw [h1, (hKnn i₀).mp h1])
        · exact ⟨j, by rw [hσ''ne j hji]; exact hj⟩
      have hKnn'' : ∀ i, σ'' i = none ↔ σ' i = none := by
        intro i
        by_cases hi : i = i₀
        · subst hi; rw [hσ''i]
        · rw [hσ''ne i hi]; exact hKnn i
      have hK'' : ∀ i, σ'' i = σ' i ∨ (σ'' i = some (Fin.last k) ∧ σ' i = some ⟨k-1, by omega⟩) ∨
          (σ' i = some (Fin.last k) ∧ σ'' i = some ⟨k-1, by omega⟩) := by
        intro i
        by_cases hi : i = i₀
        · subst hi; exact Or.inl (by rw [hσ''i])
        · rw [hσ''ne i hi]; exact hK i
      have hD'' : Finset.univ.filter (fun i => σ'' i ≠ σ' i)
          = (Finset.univ.filter (fun i => σ i ≠ σ' i)).erase i₀ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
        by_cases hi : i = i₀
        · subst hi; rw [hσ''i]; simp
        · rw [hσ''ne i hi]; tauto
      have hcard'' : (Finset.univ.filter (fun i => σ'' i ≠ σ' i)).card < n := by
        rw [hD'']
        exact lt_of_lt_of_eq (Finset.card_erase_lt_of_mem hi₀mem) hcard
      have hrec := ih _ hcard'' σ'' σ' hσ'' hσ' hKnn'' hK'' rfl
      rcases hK i₀ with hEq | ⟨hA, hB⟩ | ⟨hA, hB⟩
      · exact absurd hEq hi₀
      · have hswap := buildW_prop hk hr hM hN C M le_rfl σ σ'' hσ hσ'' i₀ hi₀M hA
            (by rw [hσ''i]; exact hB) (by intro i hi; rw [hσ''ne i hi])
        exact hswap.trans hrec
      · have hswap := (buildW_prop hk hr hM hN C M le_rfl σ'' σ hσ'' hσ i₀ hi₀M
            (by rw [hσ''i]; exact hA) hB (by intro i hi; rw [hσ''ne i hi])).symm
        exact hswap.trans hrec
    · have hσeq : σ = σ' := by
        funext i
        by_contra h
        exact hD ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩⟩
      subst hσeq
      rfl

/-- **Insensitivity lemma** (Shelah type): a colouring of the combinatorial lines is insensitive
to interchanging the two largest letters on the lines of some subspace. -/
theorem insens_lemma (k M r : ℕ) (hk : 1 ≤ k) (hr : 0 < r) :
    ∃ n : ℕ, ∀ N : ℕ, n ≤ N → ∀ C : Combinatorics.Line (Fin (k+1)) (Fin N) → Fin r,
    ∃ S : Combinatorics.Subspace (Fin M) (Fin (k+1)) (Fin N),
      ∀ σ σ' : Fin M → Option (Fin (k+1)), (hσ : ∃ e, σ e = none) → (hσ' : ∃ e, σ' e = none) →
        ((∀ i, σ i = none ↔ σ' i = none) ∧
          ∀ i, σ i = σ' i ∨
            (σ i = some (Fin.last k) ∧ σ' i = some ⟨k-1, by omega⟩) ∨
            (σ' i = some (Fin.last k) ∧ σ i = some ⟨k-1, by omega⟩)) →
        C ⟨fun i => Sum.elim (fun a => some a) σ (S.idxFun i), by
            obtain ⟨e, he⟩ := hσ; obtain ⟨i, hi⟩ := S.proper e
            exact ⟨i, by simp [hi, he]⟩⟩
        = C ⟨fun i => Sum.elim (fun a => some a) σ' (S.idxFun i), by
            obtain ⟨e, he⟩ := hσ'; obtain ⟨i, hi⟩ := S.proper e
            exact ⟨i, by simp [hi, he]⟩⟩ := by
  rcases Nat.eq_zero_or_pos M with hM0 | hM
  · subst hM0
    refine ⟨0, fun N _ C => ⟨⟨fun _ => Sum.inl ⟨0, Nat.succ_pos k⟩, fun e => Fin.elim0 e⟩, ?_⟩⟩
    intro σ σ' hσ
    exact absurd hσ (by rintro ⟨e, _⟩; exact Fin.elim0 e)
  · refine ⟨qseq k M r 0, fun N hN C => ?_⟩
    let wM : Subspace (Fin (qseq k M r M)) (Fin (k+1)) (Fin N) := buildW hk hr hM hN C M le_rfl
    let e : Fin (qseq k M r M) ≃ Fin M := finCongr (qseq_self k M r)
    refine ⟨wM.reindex e (Equiv.refl (Fin (k+1))) (Equiv.refl (Fin N)), ?_⟩
    intro σ σ' hσ hσ' hK
    change C (lineOf (wM.reindex e (Equiv.refl (Fin (k+1))) (Equiv.refl (Fin N))) σ hσ)
      = C (lineOf (wM.reindex e (Equiv.refl (Fin (k+1))) (Equiv.refl (Fin N))) σ' hσ')
    have hσ0 : HasVar (σ ∘ e) := by
      obtain ⟨i, hi⟩ := hσ; exact ⟨e.symm i, by simp only [Function.comp_apply, Equiv.apply_symm_apply]; exact hi⟩
    have hσ0' : HasVar (σ' ∘ e) := by
      obtain ⟨i, hi⟩ := hσ'; exact ⟨e.symm i, by simp only [Function.comp_apply, Equiv.apply_symm_apply]; exact hi⟩
    rw [show lineOf (wM.reindex e (Equiv.refl (Fin (k+1))) (Equiv.refl (Fin N))) σ hσ
          = lineOf wM (σ ∘ e) hσ0 from Line.ext (reindex_wsubst wM e σ),
        show lineOf (wM.reindex e (Equiv.refl (Fin (k+1))) (Equiv.refl (Fin N))) σ' hσ'
          = lineOf wM (σ' ∘ e) hσ0' from Line.ext (reindex_wsubst wM e σ')]
    exact insens_chain hk hr hM hN C (σ ∘ e) (σ' ∘ e) hσ0 hσ0'
      (by intro i; exact hK.1 (e i)) (by intro i; exact hK.2 (e i))

end Commons.Combinatorics.Ramsey