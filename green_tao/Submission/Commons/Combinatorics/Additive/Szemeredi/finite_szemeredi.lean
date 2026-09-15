/-
# `Commons.Combinatorics.Additive.Szemeredi.finite_szemeredi`

**Target.**  Finitary Szemerédi: for every `k` and `δ > 0` there is `N₀` such that every
`δ`-dense `B ⊆ {0, …, N-1}` with `N ≥ N₀` contains a `k`-term arithmetic progression
`a, a+b, …, a+(k-1)b` with `b ≥ 1`.

**Route.**  Via the density Hales–Jewett theorem: the commons lemma
`finite_szemeredi_of_density_hales_jewett` reduces the target to `DHJ k` for all `k ≥ 2`.
`DHJ 2` is Sperner's theorem (commons `dhj_two`); the step `DHJ k ⟹ DHJ (k+1)` is the
density-increment dichotomy of Dodos–Kanellopoulos–Tyros (Int. Math. Res. Not. 2014),
which uses Graham–Rothschild for colourings of combinatorial lines at the alphabet `k`.
-/
import Mathlib
import Mathlib.Combinatorics.Hindman
import Mathlib.Data.Set.Card
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.NoetherianSpace
import Submission.Commons.Combinatorics.Additive.Szemeredi.dhj_two
import Submission.Commons.Combinatorics.Additive.Szemeredi.finite_szemeredi_of_density_hales_jewett
import Submission.Commons.Combinatorics.Ramsey.dkt_density_increment_unif
import Submission.Commons.Combinatorics.Ramsey.dkt_dhj_of_increment_unif

namespace Commons.Combinatorics.Additive.Szemeredi

open Finset
open scoped Classical

/-! ### Local copies of the Graham–Rothschild chain

`Submission.Commons.Combinatorics.Ramsey.finite_hindman` and
`Submission.Commons.Combinatorics.Ramsey.mdhj_of_dhj` both define a top-level
`Commons.Combinatorics.Ramsey.res`, so no module can import both; the density-increment
chain needs `mdhj_of_dhj`, so the Graham–Rothschild chain (finite Hindman + Shelah's
insensitivity + Tyros's induction) is reproduced below inside the private namespace `Aux`.
Nothing new here: it is the team's commons development, relocated verbatim. -/
namespace Aux

open _root_.Combinatorics





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



open Filter



structure FU (X : Type*) where
  val : Finset X
deriving DecidableEq

@[ext] theorem FU.ext {X} {a b : FU X} (h : a.val = b.val) : a = b := by cases a; cases b; simp_all

namespace FU
instance (X) [DecidableEq X] : CommMonoid (FU X) where
  mul a b := ⟨a.val ∪ b.val⟩
  one := ⟨∅⟩
  mul_assoc a b c := FU.ext (Finset.union_assoc _ _ _)
  one_mul a := FU.ext (Finset.empty_union _)
  mul_one a := FU.ext (Finset.union_empty _)
  mul_comm a b := FU.ext (Finset.union_comm _ _)
instance (X) : Inhabited (FU X) := ⟨⟨∅⟩⟩
@[simp] theorem mul_val {X} [DecidableEq X] (a b : FU X) : (a * b).val = a.val ∪ b.val := rfl
@[simp] theorem one_val {X} [DecidableEq X] : (1 : FU X).val = ∅ := rfl
end FU
open FU

attribute [local instance] Ultrafilter.semigroup

variable {X : Type*} [DecidableEq X]

def DF (F : Finset X) : Set (FU X) := {S | Disjoint S.val F}
def NE : Set (FU X) := {S | S.val.Nonempty}

def delta (X : Type*) [DecidableEq X] : Set (Ultrafilter (FU X)) :=
  (⋂ F : Finset X, {U | DF F ∈ U}) ∩ {U | NE ∈ U}

theorem mem_delta {U : Ultrafilter (FU X)} :
    U ∈ delta X ↔ (∀ F : Finset X, DF F ∈ U) ∧ NE ∈ U := by simp [delta]

theorem delta_closed : IsClosed (delta X) := by
  have : delta X = (⋂ F : Finset X, {U : Ultrafilter (FU X) | DF F ∈ U}) ∩ {U : Ultrafilter (FU X) | NE ∈ U} := rfl
  rw [this]
  exact (isClosed_iInter (fun F => ultrafilter_isClosed_basic (DF F))).inter (ultrafilter_isClosed_basic NE)

theorem mem_umul {M : Type*} [Semigroup M] (U V : Ultrafilter M) (A : Set M) :
    A ∈ U * V ↔ ∀ᶠ m in U, ∀ᶠ m' in V, m * m' ∈ A :=
  (Iff.rfl : (A ∈ U * V) ↔ ∀ᶠ m in ↑(U * V), m ∈ A).trans (Ultrafilter.eventually_mul U V A)

theorem delta_mul {U V : Ultrafilter (FU X)} (hU : U ∈ delta X) (hV : V ∈ delta X) : U * V ∈ delta X := by
  rw [mem_delta] at hU hV ⊢
  constructor
  · intro F
    rw [mem_umul]
    filter_upwards [hU.1 F] with m hm
    filter_upwards [hV.1 F] with m' hm'
    change Disjoint (m * m').val F
    rw [FU.mul_val]
    exact disjoint_sup_left.mpr ⟨hm, hm'⟩
  · rw [mem_umul]
    filter_upwards [hU.2] with m hm
    filter_upwards [hV.2] with m' hm'
    change (m * m').val.Nonempty
    rw [FU.mul_val]
    exact Finset.union_nonempty.mpr (Or.inl hm)

theorem delta_nonempty [Infinite X] : (delta X).Nonempty := by
  classical
  set S : Set (Set (FU X)) := {t | ∃ F : Finset X, t = DF F} ∪ {NE} with hS
  have hcond : ∀ T : Finset (Set (FU X)), (↑T : Set (Set (FU X))) ⊆ S → (⋂₀ (↑T : Set (Set (FU X)))).Nonempty := by
    intro T hT
    have hmem : ∀ t ∈ T, t = NE ∨ ∃ F, t = DF F := by
      intro t ht
      have := hT ht
      simp only [S, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff] at this
      rcases this with ⟨F, hF⟩ | h
      · exact Or.inr ⟨F, hF⟩
      · exact Or.inl h
    let getF : Set (FU X) → Finset X := fun t => if h : ∃ F, t = DF F then h.choose else ∅
    have hgetF : ∀ t ∈ T, t = DF (getF t) ∨ t = NE := by
      intro t ht
      rcases hmem t ht with h | ⟨F, hF⟩
      · exact Or.inr h
      · left
        simp only [getF]
        rw [dif_pos (⟨F, hF⟩ : ∃ G, t = DF G)]
        exact (⟨F, hF⟩ : ∃ G, t = DF G).choose_spec
    obtain ⟨x, hx⟩ : ∃ x, x ∉ T.biUnion getF := by
      have hcard : (T.biUnion getF).card < ENat.card X := by
        rw [ENat.card_eq_top_of_infinite]
        exact ENat.natCast_lt_top _
      exact Finset.exists_not_mem_of_card_lt_enatCard hcard
    refine ⟨(⟨({x} : Finset X)⟩ : FU X), ?_⟩
    rw [Set.mem_sInter]
    intro t ht
    rcases hgetF t ht with h | h
    · rw [h]; simp only [DF, Set.mem_setOf_eq]
      rw [Finset.disjoint_left]; intro y hy
      simp only [Finset.mem_singleton] at hy; subst hy
      intro hyF
      exact hx (Finset.mem_biUnion.mpr ⟨t, ht, hyF⟩)
    · rw [h]; simp [NE]
  obtain ⟨F, hF⟩ := Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty S hcond
  refine ⟨F, ?_⟩
  rw [mem_delta]
  refine ⟨fun G => hF ?_, hF ?_⟩
  · exact Set.mem_union_left _ ⟨G, rfl⟩
  · exact Set.mem_union_right _ (Set.mem_singleton NE)

theorem exists_idem_delta [Infinite X] : ∃ U ∈ delta X, U * U = U :=
  exists_idempotent_in_compact_subsemigroup (fun r => Ultrafilter.continuous_mul_left r)
    (delta X) delta_nonempty delta_closed.isCompact (fun U hU V hV => delta_mul hU hV)

def res (A : Set (FU X)) (s : FU X) : Set (FU X) := {t | s * t ∈ A}

theorem eventually_res (U : Ultrafilter (FU X)) (hidem : U * U = U)
    (A : Set (FU X)) (hA : A ∈ U) : {s : FU X | res A s ∈ U} ∈ U := by
  have h : A ∈ U * U := by rw [hidem]; exact hA
  rw [mem_umul] at h
  rw [show {s : FU X | res A s ∈ U} ∈ U ↔ ∀ᶠ s in U, res A s ∈ U from Iff.rfl]
  filter_upwards [h] with m hm
  rw [show res A m ∈ U ↔ ∀ᶠ t in U, t ∈ res A m from Iff.rfl]
  exact hm

def unL (L : Finset (FU X)) : FU X := ⟨L.biUnion (fun s => s.val)⟩

theorem unL_val (L : Finset (FU X)) : (unL L).val = L.biUnion (fun s => s.val) := rfl

theorem unL_insert (s : FU X) (L : Finset (FU X)) : unL (insert s L) = s * unL L := by
  apply FU.ext
  rw [FU.mul_val, unL_val, unL_val, Finset.biUnion_insert]

theorem unL_empty : unL (∅ : Finset (FU X)) = 1 := by
  apply FU.ext
  rw [unL_val, FU.one_val]
  simp

theorem unL_mono {J L : Finset (FU X)} (h : J ⊆ L) : (unL J).val ⊆ (unL L).val := by
  rw [unL_val, unL_val]
  intro x hx
  obtain ⟨t, htJ, hxt⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨t, h htJ, hxt⟩

theorem unL_mem_subset {L : Finset (FU X)} {s : FU X} (h : s ∈ L) : s.val ⊆ (unL L).val := by
  rw [unL_val]; exact Finset.subset_biUnion_of_mem (fun t => t.val) h

def Inv (U : Ultrafilter (FU X)) (C : Set (FU X)) (L : Finset (FU X)) (A : Set (FU X)) : Prop :=
  A ∈ U ∧ A ⊆ C ∧ A ⊆ {S : FU X | Disjoint S.val (unL L).val} ∧
  (∀ J : Finset (FU X), J ⊆ L → J.Nonempty → unL J ∈ C) ∧
  (∀ J : Finset (FU X), J ⊆ L → J.Nonempty → ∀ S ∈ A, unL J * S ∈ C)

noncomputable def step (U : Ultrafilter (FU X)) (C : Set (FU X))
    (p : Finset (FU X) × Set (FU X)) : FU X × (Finset (FU X) × Set (FU X)) := by
  classical
  exact (let s : FU X := if h : (p.2 ∩ {s : FU X | res p.2 s ∈ U}).Nonempty then h.choose else 1
    (s, (insert s p.1, p.2 ∩ res p.2 s ∩ C ∩ {S : FU X | Disjoint S.val (unL (insert s p.1)).val})))

theorem step_fst_mem {U : Ultrafilter (FU X)} {C : Set (FU X)} {L A}
    (hL : Inv U C L A) (hidem : U * U = U) :
    (step U C (L, A)).1 ∈ A ∩ {s : FU X | res A s ∈ U} := by
  classical
  have hB : (A ∩ {s : FU X | res A s ∈ U}).Nonempty :=
    Ultrafilter.nonempty_of_mem (inter_mem hL.1 (eventually_res U hidem A hL.1))
  have hdef : (step U C (L, A)).1 = (if h : (A ∩ {s : FU X | res A s ∈ U}).Nonempty then h.choose else 1) := rfl
  rw [hdef, dif_pos hB]
  exact hB.choose_spec

theorem step_snd {U : Ultrafilter (FU X)} {C : Set (FU X)} {L A} :
    (step U C (L, A)).2 = (insert (step U C (L, A)).1 L,
      A ∩ res A (step U C (L, A)).1 ∩ C ∩ {S : FU X | Disjoint S.val (unL (insert (step U C (L, A)).1 L)).val}) := rfl

theorem inv_base {U : Ultrafilter (FU X)} {C : Set (FU X)} (hC : C ∈ U) : Inv U C ∅ C := by
  refine ⟨hC, subset_rfl, ?_, ?_, ?_⟩
  · intro S hS
    rw [unL_empty, FU.one_val]; exact disjoint_bot_right
  · intro J hJ hJne
    rw [Finset.subset_empty] at hJ; rw [hJ] at hJne
    exact absurd hJne Finset.not_nonempty_empty
  · intro J hJ hJne
    rw [Finset.subset_empty] at hJ; rw [hJ] at hJne
    exact absurd hJne Finset.not_nonempty_empty

theorem step_inv {U : Ultrafilter (FU X)} {C : Set (FU X)} (hC : C ∈ U) (hUdelta : U ∈ delta X)
    (hidem : U * U = U) {L A} (hL : Inv U C L A) :
    Inv U C (step U C (L, A)).2.1 (step U C (L, A)).2.2 := by
  obtain ⟨hsA, hsres⟩ := step_fst_mem hL hidem
  obtain ⟨hA, hAC, hAdisj, hv, hvi⟩ := hL
  rw [mem_delta] at hUdelta
  set s : FU X := (step U C (L, A)).1 with hs
  set L' : Finset (FU X) := insert s L with hLs
  set A' : Set (FU X) := A ∩ res A s ∩ C ∩ {S : FU X | Disjoint S.val (unL L').val} with hAs
  have h1 : (step U C (L, A)).2.1 = L' := rfl
  have h2 : (step U C (L, A)).2.2 = A' := rfl
  rw [h1, h2]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hAs]
    exact inter_mem (inter_mem (inter_mem hA hsres) hC) (hUdelta.1 (unL L').val)
  · intro S hS; rw [hAs] at hS; exact hS.1.2
  · intro S hS; rw [hAs] at hS; exact hS.2
  · intro J hJL hJne
    rw [hLs] at hJL
    by_cases hmem : s ∈ J
    · have hJerase : J.erase s ⊆ L := fun x hx => by
        have hxJ : x ∈ J := Finset.mem_of_mem_erase hx
        have hxs : x ≠ s := (Finset.mem_erase.mp hx).1
        have hx' := hJL hxJ
        rw [Finset.mem_insert] at hx'
        rcases hx' with h | h
        · exact absurd h hxs
        · exact h
      have hJeq : J = insert s (J.erase s) := (Finset.insert_erase hmem).symm
      rw [hJeq, unL_insert]
      by_cases hJ'e : (J.erase s).Nonempty
      · rw [mul_comm]
        exact hvi (J.erase s) hJerase hJ'e s hsA
      · rw [Finset.not_nonempty_iff_eq_empty] at hJ'e
        rw [hJ'e, unL_empty, mul_one]
        exact hAC hsA
    · have hJL' : J ⊆ L := fun x hxJ => by
        have hx := hJL hxJ
        rw [Finset.mem_insert] at hx
        rcases hx with h | h
        · exact absurd (h ▸ hxJ) hmem
        · exact h
      exact hv J hJL' hJne
  · intro J hJL hJne S hSA
    rw [hLs] at hJL
    rw [hAs] at hSA
    obtain ⟨⟨⟨hSA', hSres⟩, _⟩, _⟩ := hSA
    by_cases hmem : s ∈ J
    · have hJerase : J.erase s ⊆ L := fun x hx => by
        have hxJ : x ∈ J := Finset.mem_of_mem_erase hx
        have hxs : x ≠ s := (Finset.mem_erase.mp hx).1
        have hx' := hJL hxJ
        rw [Finset.mem_insert] at hx'
        rcases hx' with h | h
        · exact absurd h hxs
        · exact h
      have hJeq : J = insert s (J.erase s) := (Finset.insert_erase hmem).symm
      rw [hJeq, unL_insert]
      have hkey : unL (J.erase s) * (s * S) ∈ C := by
        by_cases hJ'e : (J.erase s).Nonempty
        · exact hvi (J.erase s) hJerase hJ'e (s * S) hSres
        · rw [Finset.not_nonempty_iff_eq_empty] at hJ'e
          rw [hJ'e, unL_empty, one_mul]
          exact hAC hSres
      have heq : (s * unL (J.erase s)) * S = unL (J.erase s) * (s * S) := by ac_rfl
      rw [heq]; exact hkey
    · have hJL' : J ⊆ L := fun x hxJ => by
        have hx := hJL hxJ
        rw [Finset.mem_insert] at hx
        rcases hx with h | h
        · exact absurd (h ▸ hxJ) hmem
        · exact h
      exact hvi J hJL' hJne S hSA'

theorem fut_infinite_aux [Infinite X] (m r : ℕ) (hr : 0 < r)
    (χ : (S : Finset X) → S.Nonempty → Fin r) :
    ∃ s : Fin m → Finset X, (∀ j, (s j).Nonempty) ∧
      (∀ j j', j ≠ j' → Disjoint (s j) (s j')) ∧
      ∃ c : Fin r, ∀ (t : Finset (Fin m)) (ht : t.Nonempty) (hU : (t.biUnion s).Nonempty),
        χ (t.biUnion s) hU = c := by
  classical
  obtain ⟨U, hUdelta, hUidem⟩ := exists_idem_delta (X := X)
  let f : FU X → Fin r := fun S => if h : S.val.Nonempty then χ S.val h else ⟨0, hr⟩
  have hcolor : ∃ c : Fin r, {S : FU X | f S = c} ∈ U := by
    have hcover : (⋃ c : Fin r, {S : FU X | f S = c}) ∈ U := by
      rw [show (⋃ c : Fin r, {S : FU X | f S = c}) = (Set.univ : Set (FU X)) from by
        ext S
        exact ⟨fun _ => trivial, fun _ => Set.mem_iUnion.mpr ⟨f S, rfl⟩⟩]
      exact Filter.univ_mem
    have hb : (⋃ c ∈ (Set.univ : Set (Fin r)), {S : FU X | f S = c}) ∈ U := by
      rwa [Set.biUnion_univ]
    obtain ⟨c, -, hc⟩ := (Ultrafilter.finite_biUnion_mem_iff (Set.finite_univ)
      (s := fun c : Fin r => {S : FU X | f S = c})).mp hb
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := hcolor
  let C : Set (FU X) := {S : FU X | f S = c} ∩ NE
  have hC : C ∈ U := inter_mem hc hUdelta.2
  have hCf : ∀ S ∈ C, f S = c := fun S hS => hS.1
  have hCne : ∀ S ∈ C, S.val.Nonempty := fun S hS => hS.2
  let st : ℕ → Finset (FU X) × Set (FU X) := Nat.rec (∅, C) (fun _ p => (step U C p).2)
  have st_succ : ∀ n, st (n+1) = (step U C (st n)).2 := fun n => rfl
  have hInv : ∀ n, Inv U C (st n).1 (st n).2 := by
    intro n
    induction n with
    | zero => exact inv_base hC
    | succ n ih =>
      have h := step_inv hC hUdelta hUidem ih
      exact h
  have seq_mem_st : ∀ n j, j < n → (step U C (st j)).1 ∈ (st n).1 := by
    intro n
    induction n with
    | zero => intro j hj; exact absurd hj (Nat.not_lt_zero j)
    | succ n ih =>
      intro j hj
      rw [st_succ n, show (step U C (st n)).2.1 = insert (step U C (st n)).1 (st n).1 from rfl]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact Finset.mem_insert_of_mem (ih j h)
      · subst h; exact Finset.mem_insert_self _ _
  refine ⟨fun j : Fin m => ((step U C (st j.val)).1).val, ?_, ?_, ?_⟩
  · intro j
    have h1 : (step U C (st j.val)).1 ∈ (st j.val).2 := (step_fst_mem (hInv j.val) hUidem).1
    exact hCne _ ((hInv j.val).2.1 h1)
  · intro j j' hjj
    have hv : j.val ≠ j'.val := fun h => hjj (Fin.ext h)
    rcases lt_or_gt_of_ne hv with h | h
    · have h1 : (step U C (st j'.val)).1 ∈ (st j'.val).2 := (step_fst_mem (hInv j'.val) hUidem).1
      have h2 : (st j'.val).2 ⊆ {S : FU X | Disjoint S.val (unL (st j'.val).1).val} := (hInv j'.val).2.2.1
      have h3 : Disjoint ((step U C (st j'.val)).1).val (unL (st j'.val).1).val := h2 h1
      have h4 : ((step U C (st j.val)).1).val ⊆ (unL (st j'.val).1).val :=
        unL_mem_subset (seq_mem_st j'.val j.val h)
      exact (Disjoint.mono_right h4 h3).symm
    · have h1 : (step U C (st j.val)).1 ∈ (st j.val).2 := (step_fst_mem (hInv j.val) hUidem).1
      have h2 : (st j.val).2 ⊆ {S : FU X | Disjoint S.val (unL (st j.val).1).val} := (hInv j.val).2.2.1
      have h3 : Disjoint ((step U C (st j.val)).1).val (unL (st j.val).1).val := h2 h1
      have h4 : ((step U C (st j'.val)).1).val ⊆ (unL (st j.val).1).val :=
        unL_mem_subset (seq_mem_st j.val j'.val h)
      exact (Disjoint.mono_right h4 h3)
  · refine ⟨c, ?_⟩
    intro t ht htne
    set seq' : Fin m → FU X := fun j => (step U C (st j.val)).1 with hseq'
    have himage_sub : t.image seq' ⊆ (st m).1 := by
      intro S hS
      obtain ⟨j, hjt, rfl⟩ := Finset.mem_image.mp hS
      exact seq_mem_st m j.val j.isLt
    have himage_ne : (t.image seq').Nonempty := by
      obtain ⟨j, hj⟩ := ht
      exact ⟨seq' j, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
    have hC' : unL (t.image seq') ∈ C := (hInv m).2.2.2.1 _ himage_sub himage_ne
    have hf : f (unL (t.image seq')) = c := hCf _ hC'
    have hfeq : f (⟨t.biUnion fun j : Fin m => (step U C (st j.val)).1.val⟩ : FU X) = f (unL (t.image seq')) := by
      congr 1
      exact FU.ext (by rw [unL_val, Finset.image_biUnion])
    rw [hf] at hfeq
    simp only [f] at hfeq
    rw [dif_pos htne] at hfeq
    exact hfeq


theorem chi_eq_of_eq {N r : ℕ} (χ : (S : Finset (Fin N)) → S.Nonempty → Fin r)
    {A B : Finset (Fin N)} (h : A = B) (hA : A.Nonempty) (hB : B.Nonempty) : χ A hA = χ B hB := by
  cases h; rfl

section Compact
variable (m r : ℕ)

theorem map_biUnion' {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (e : β ↪ γ) (s : Finset α) (f : α → Finset β) :
    (s.biUnion f).map e = s.biUnion (fun a => (f a).map e) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp only [Finset.biUnion_insert, Finset.map_union, ih]

def CfgFin (n : ℕ) (σ : Finset (Fin n) → Fin r) : Prop :=
  ∃ s : Fin m → Finset (Fin n), (∀ j, (s j).Nonempty) ∧
    (∀ j j', j ≠ j' → Disjoint (s j) (s j')) ∧
    ∃ c : Fin r, ∀ (t : Finset (Fin m)) (ht : t.Nonempty), σ (t.biUnion s) = c

def rN (n : ℕ) (χ : Finset ℕ → Fin r) : Finset (Fin n) → Fin r := fun T => χ (T.map Fin.valEmbedding)

def HasCfgN (n : ℕ) (χ : Finset ℕ → Fin r) : Prop := CfgFin m r n (rN r n χ)

theorem csve (n : ℕ) :
    (Fin.castSuccEmb.trans (Fin.valEmbedding (n := n+1))) = (Fin.valEmbedding (n := n)) := by
  ext i; rfl

theorem HasCfgN_mono {n : ℕ} {χ : Finset ℕ → Fin r} (h : HasCfgN m r n χ) : HasCfgN m r (n+1) χ := by
  obtain ⟨s, h1, h2, c, hc⟩ := h
  refine ⟨fun j => (s j).map Fin.castSuccEmb, ?_, ?_, c, ?_⟩
  · intro j; rw [Finset.map_nonempty]; exact h1 j
  · intro j j' hjj; rw [Finset.disjoint_map]; exact h2 j j' hjj
  · intro t ht
    have key : (t.biUnion (fun j => (s j).map Fin.castSuccEmb)).map (Fin.valEmbedding (n := n+1))
        = (t.biUnion s).map (Fin.valEmbedding (n := n)) := by
      rw [map_biUnion']
      conv_rhs => rw [map_biUnion']
      congr 1
      funext j
      rw [Finset.map_map, csve]
    show χ ((t.biUnion (fun j => (s j).map Fin.castSuccEmb)).map (Fin.valEmbedding (n := n+1))) = c
    rw [key]
    exact hc t ht

theorem rN_continuous (n : ℕ) : Continuous (rN r n) := by
  rw [continuous_pi_iff]
  intro T
  exact continuous_apply (T.map Fin.valEmbedding)

theorem badFin_closed (n : ℕ) : IsClosed {σ : Finset (Fin n) → Fin r | ¬ CfgFin m r n σ} :=
  (Set.toFinite _).isClosed

theorem KN_closed (n : ℕ) : IsClosed {χ : Finset ℕ → Fin r | ¬ HasCfgN m r n χ} := by
  have h : {χ : Finset ℕ → Fin r | ¬ HasCfgN m r n χ}
      = rN r n ⁻¹' {σ : Finset (Fin n) → Fin r | ¬ CfgFin m r n σ} := rfl
  rw [h]
  exact (badFin_closed m r n).preimage (rN_continuous r n)

theorem transfer_eq (n : ℕ) (σ : Finset (Fin n) → Fin r) :
    rN r n (fun S => σ ((Finset.univ : Finset (Fin n)).filter (fun i => (i : ℕ) ∈ S))) = σ := by
  funext T
  show σ ((Finset.univ : Finset (Fin n)).filter (fun i => (i : ℕ) ∈ T.map (Fin.valEmbedding))) = σ T
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    obtain ⟨a, ha, hav⟩ := Finset.mem_map.mp h
    rwa [Fin.val_injective hav] at ha
  · intro h; exact Finset.mem_map.mpr ⟨i, h, rfl⟩

theorem KN_nonempty (n : ℕ) (hbad : ∃ σ : Finset (Fin n) → Fin r, ¬ CfgFin m r n σ) :
    {χ : Finset ℕ → Fin r | ¬ HasCfgN m r n χ}.Nonempty := by
  obtain ⟨σ, hσ⟩ := hbad
  refine ⟨fun S => σ ((Finset.univ : Finset (Fin n)).filter (fun i => (i : ℕ) ∈ S)), ?_⟩
  simp only [Set.mem_setOf_eq, HasCfgN, transfer_eq]
  exact hσ

theorem finite_bound (hr : 0 < r) : ∃ n, ∀ σ : Finset (Fin n) → Fin r, CfgFin m r n σ := by
  by_contra h
  push_neg at h
  have hK : ∀ n, ({χ : Finset ℕ → Fin r | ¬ HasCfgN m r n χ}).Nonempty := fun n => KN_nonempty m r n (h n)
  have hmono : ∀ n, {χ : Finset ℕ → Fin r | ¬ HasCfgN m r (n+1) χ} ⊆ {χ : Finset ℕ → Fin r | ¬ HasCfgN m r n χ} := by
    intro n χ hχ hc; exact hχ (HasCfgN_mono m r hc)
  have hcl : ∀ n, IsClosed {χ : Finset ℕ → Fin r | ¬ HasCfgN m r n χ} := fun n => KN_closed m r n
  obtain ⟨χ, hχ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => {χ : Finset ℕ → Fin r | ¬ HasCfgN m r n χ}) hmono hK (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hχ
  -- infinite FUT gives a config
  obtain ⟨s, hs1, hs2, c, hc⟩ := fut_infinite_aux (X := ℕ) m r hr (fun S _ => χ S)
  have hsub : ∀ j, s j ⊆ Finset.range (1 + (Finset.univ : Finset (Fin m)).sup (fun j => (s j).sup id)) := by
    intro j x hx
    rw [Finset.mem_range]
    have h1 : x ≤ (s j).sup id := Finset.le_sup (f := id) hx
    have h2 : (s j).sup id ≤ (Finset.univ : Finset (Fin m)).sup (fun j => (s j).sup id) :=
      Finset.le_sup (f := fun j => (s j).sup id) (Finset.mem_univ j)
    omega
  set N := 1 + (Finset.univ : Finset (Fin m)).sup (fun j => (s j).sup id) with hN
  have huniv : (Finset.univ : Finset (Fin N)).map Fin.valEmbedding = Finset.range N := by
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_range]
    exact ⟨fun ⟨i, h⟩ => h ▸ i.isLt, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  choose T hT using fun j => (Finset.subset_map_iff.mp (by rw [huniv]; exact hsub j) : ∃ u ⊆ (Finset.univ : Finset (Fin N)), s j = u.map Fin.valEmbedding)
  have key : HasCfgN m r N χ := by
    refine ⟨fun j => T j, ?_, ?_, c, ?_⟩
    · intro j
      rw [← Finset.map_nonempty, ← (hT j).2]
      exact hs1 j
    · intro j j' hjj
      rw [← Finset.disjoint_map (Fin.valEmbedding), ← (hT j).2, ← (hT j').2]
      exact hs2 j j' hjj
    · intro t ht
      show χ ((t.biUnion fun j => T j).map Fin.valEmbedding) = c
      rw [map_biUnion']
      have : (t.biUnion fun j => (T j).map Fin.valEmbedding) = t.biUnion s := by
        congr 1; funext j; exact (hT j).2.symm
      rw [this]
      have hne : (t.biUnion s).Nonempty := by
        obtain ⟨j, hj⟩ := ht
        obtain ⟨x, hx⟩ := hs1 j
        exact ⟨x, Finset.mem_biUnion.mpr ⟨j, hj, hx⟩⟩
      exact hc t ht hne
  exact hχ N key

theorem finite_hindman (m r : ℕ) (hr : 0 < r) :
    ∃ n : ℕ, ∀ N : ℕ, n ≤ N → ∀ χ : (S : Finset (Fin N)) → S.Nonempty → Fin r,
      ∃ s : Fin m → Finset (Fin N), (∀ j, (s j).Nonempty) ∧
        (∀ j j', j ≠ j' → Disjoint (s j) (s j')) ∧
        ∃ c : Fin r, ∀ (t : Finset (Fin m)) (ht : t.Nonempty) (hU : (t.biUnion s).Nonempty),
          χ (t.biUnion s) hU = c := by
  obtain ⟨n, hn⟩ := finite_bound m r hr
  refine ⟨n, fun N hN χ => ?_⟩
  let e : Fin n ↪ Fin N := Fin.castLEEmb hN
  let σ : Finset (Fin n) → Fin r := fun T => if h : (T.map e).Nonempty then χ (T.map e) h else ⟨0, hr⟩
  obtain ⟨s, hs1, hs2, c, hc⟩ := hn σ
  refine ⟨fun j => (s j).map e, ?_, ?_, c, ?_⟩
  · intro j; rw [Finset.map_nonempty]; exact hs1 j
  · intro j j' hjj; rw [Finset.disjoint_map]; exact hs2 j j' hjj
  · intro t ht hU
    have key : t.biUnion (fun j => (s j).map e) = (t.biUnion s).map e :=
      (map_biUnion' e t s).symm
    have hne : ((t.biUnion s).map e).Nonempty := by
      rw [Finset.map_nonempty]
      obtain ⟨j, hj⟩ := ht
      obtain ⟨x, hx⟩ := hs1 j
      exact ⟨x, Finset.mem_biUnion.mpr ⟨j, hj, hx⟩⟩
    have h1 : χ ((t.biUnion s).map e) hne = c := by
      have h2 := hc t ht
      rw [show σ (t.biUnion s) = χ ((t.biUnion s).map e) hne from by
            simp only [σ]; rw [dif_pos hne]] at h2
      exact h2
    rw [chi_eq_of_eq χ key hU hne]
    exact h1

end Compact





/-! ## Base case `k = 1` -/

/-- The combinatorial line over `Fin 1` whose wildcard positions are exactly `T`. -/
def lineOfSet {N : ℕ} (T : Finset (Fin N)) (hT : T.Nonempty) : Line (Fin 1) (Fin N) :=
  ⟨fun i => if i ∈ T then none else some 0, by
    obtain ⟨i, hi⟩ := hT; exact ⟨i, by rw [if_pos hi]⟩⟩

/-- Base case of the Graham-Rothschild theorem: colourings of the lines over a one-letter
alphabet.  This is exactly Folkman's finite union theorem. -/
theorem grlines_base (M r : ℕ) (hr : 0 < r) :
    ∃ n : ℕ, ∀ N : ℕ, n ≤ N → ∀ C : Line (Fin 1) (Fin N) → Fin r,
    ∃ S : Subspace (Fin M) (Fin 1) (Fin N), ∃ c : Fin r,
      ∀ σ : Fin M → Option (Fin 1), (hσ : ∃ e, σ e = none) →
        C ⟨fun i => Sum.elim (fun a => some a) σ (S.idxFun i), by
            obtain ⟨e, he⟩ := hσ; obtain ⟨i, hi⟩ := S.proper e
            exact ⟨i, by simp [hi, he]⟩⟩ = c := by
  obtain ⟨n0, hn0⟩ := finite_hindman M r hr
  refine ⟨n0, fun N hN C => ?_⟩
  let chi : (S : Finset (Fin N)) → S.Nonempty → Fin r := fun S hS => C (lineOfSet S hS)
  obtain ⟨s, hsne, hsdisj, c, hc⟩ := hn0 N hN chi
  let g : Fin N → Fin 1 ⊕ Fin M := fun i =>
    if h : ∃ j, i ∈ s j then Sum.inr h.choose else Sum.inl 0
  have hg : ∀ i j, g i = Sum.inr j ↔ i ∈ s j := by
    intro i j
    by_cases h : ∃ j', i ∈ s j'
    · have hgi : g i = Sum.inr h.choose := dif_pos h
      rw [hgi]
      constructor
      · intro heq
        rw [Sum.inr.injEq] at heq
        rw [← heq]; exact h.choose_spec
      · intro hij
        congr 1
        by_contra hne
        exact (Finset.disjoint_left.mp (hsdisj h.choose j hne)) h.choose_spec hij
    · have hgi : g i = Sum.inl 0 := dif_neg h
      rw [hgi]
      constructor
      · intro heq; exact absurd heq (by simp)
      · intro hij; exact absurd ⟨j, hij⟩ h
  have hgne : ∀ j, ∃ i, g i = Sum.inr j := by
    intro j; obtain ⟨i, hi⟩ := hsne j; exact ⟨i, (hg i j).mpr hi⟩
  refine ⟨⟨g, hgne⟩, c, ?_⟩
  intro σ hσ
  set T : Finset (Fin M) := Finset.univ.filter (fun j => σ j = none) with hTdef
  have hTne : T.Nonempty := by
    obtain ⟨e, he⟩ := hσ
    exact ⟨e, by simp [hTdef, he]⟩
  have hUne : (T.biUnion s).Nonempty := by
    obtain ⟨e, he⟩ := hTne
    obtain ⟨i, hi⟩ := hsne e
    exact ⟨i, Finset.mem_biUnion.mpr ⟨e, he, hi⟩⟩
  have hword : (fun i => Sum.elim (fun a => some a) σ (g i))
      = (lineOfSet (T.biUnion s) hUne).idxFun := by
    funext i
    change Sum.elim (fun a => some a) σ (g i) = if i ∈ T.biUnion s then none else some 0
    by_cases h : i ∈ T.biUnion s
    · rw [if_pos h]
      obtain ⟨j, hjT, hij⟩ := Finset.mem_biUnion.mp h
      have hj : σ j = none := by simpa [hTdef] using hjT
      rw [show g i = Sum.inr j from (hg i j).mpr hij, Sum.elim_inr, hj]
    · rw [if_neg h]
      have hh : ∀ j, i ∈ s j → σ j ≠ none := fun j hij hj =>
        h (Finset.mem_biUnion.mpr ⟨j, by simp [hTdef, hj], hij⟩)
      cases hg' : g i with
      | inl a => rw [Sum.elim_inl]; exact congrArg some (Subsingleton.elim a 0)
      | inr j =>
        rw [Sum.elim_inr]
        have : σ j ≠ none := hh j ((hg i j).mp hg')
        cases hσj : σ j with
        | none => exact absurd hσj this
        | some a => exact congrArg some (Subsingleton.elim a 0)
  have hline : (⟨fun i => Sum.elim (fun a => some a) σ (g i), by
        obtain ⟨e, he⟩ := hσ; obtain ⟨i, hi⟩ := hgne e
        exact ⟨i, by simp [hi, he]⟩⟩ : Line (Fin 1) (Fin N))
      = lineOfSet (T.biUnion s) hUne := Line.ext hword
  rw [hline]
  exact hc T hTne hUne

/-! ## Inductive step -/

/-- Embed a word over `Fin k` into a word over `Fin (k+1)`. -/
def embWord {k n : ℕ} (x : Fin n → Option (Fin k)) : Fin n → Option (Fin (k+1)) :=
  fun i => (x i).map Fin.castSucc

/-- Embed a subspace over `Fin k` into a subspace over `Fin (k+1)`. -/
def embSub {k m n : ℕ} (T : Subspace (Fin m) (Fin k) (Fin n)) :
    Subspace (Fin m) (Fin (k+1)) (Fin n) :=
  ⟨fun i => Sum.map (Fin.castSucc (n := k)) (id : Fin m → Fin m) (T.idxFun i), by
    intro e; obtain ⟨i, hi⟩ := T.proper e; exact ⟨i, by rw [hi]; rfl⟩⟩

/-- Substitution of a word into a subspace, over a general alphabet `Fin K`. -/
def wsubstG {K m n : ℕ} (S : Subspace (Fin m) (Fin K) (Fin n)) (x : Fin m → Option (Fin K)) :
    Fin n → Option (Fin K) :=
  fun i => Sum.elim (fun a => some a) x (S.idxFun i)

lemma hasVarG {K m n : ℕ} (S : Subspace (Fin m) (Fin K) (Fin n)) (x : Fin m → Option (Fin K)) :
    (∃ i, wsubstG S x i = none) ↔ ∃ i, x i = none := by
  constructor
  · rintro ⟨i, hi⟩; cases h : S.idxFun i with
    | inl a => rw [wsubstG, h, Sum.elim_inl] at hi; simp at hi
    | inr e => exact ⟨e, by simpa [wsubstG, h] using hi⟩
  · rintro ⟨e, he⟩; obtain ⟨i, hi⟩ := S.proper e
    exact ⟨i, by simp only [wsubstG, hi, Sum.elim_inr, he]⟩

/-- The combinatorial line of `S` corresponding to the word `x`. -/
def lineOf' {K m n : ℕ} (S : Subspace (Fin m) (Fin K) (Fin n)) (x : Fin m → Option (Fin K))
    (hx : ∃ i, x i = none) : Line (Fin K) (Fin n) :=
  ⟨wsubstG S x, (hasVarG S x).mpr hx⟩

lemma hasVar_embWord {k n : ℕ} (x : Fin n → Option (Fin k)) :
    (∃ i, embWord x i = none) ↔ ∃ i, x i = none := by
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i, by simpa [embWord] using hi⟩
  · rintro ⟨i, hi⟩; exact ⟨i, by simp [embWord, hi]⟩

/-- Collapse the top letter `Fin.last k` of `Fin (k+1)` onto `⟨k-1⟩` in `Fin k`. -/
def collapseTop {k : ℕ} (hk : 1 ≤ k) : Fin (k+1) → Fin k := Fin.predAbove (⟨k-1, by omega⟩ : Fin k)

lemma castSucc_phi {k : ℕ} (hk : 1 ≤ k) (b : Fin (k+1)) :
    Fin.castSucc (collapseTop hk b) = if b = Fin.last k then ⟨k-1, by omega⟩ else b := by
  by_cases h : b = Fin.last k
  · subst h
    rw [if_pos rfl, collapseTop, Fin.predAbove_of_castSucc_lt]
    · rfl
    · exact Fin.castSucc_lt_last _
  · rw [if_neg h]
    have hb : (b : ℕ) < k := by
      simp only [Fin.last, Fin.val_mk] at h
      rcases Nat.lt_or_ge (b : ℕ) k with hlt | hge
      · exact hlt
      · exact absurd (Fin.ext (by omega : (b:ℕ) = k)) h
    have hb' : b = Fin.castSucc (⟨b, hb⟩ : Fin k) := by ext; simp [Fin.castSucc]
    have hle : (⟨b, hb⟩ : Fin k) ≤ (⟨k-1, by omega⟩ : Fin k) := by
      rw [Fin.le_def]; simp only [Fin.val_mk]; omega
    rw [hb', collapseTop, Fin.predAbove_castSucc_of_le _ _ hle]

/-- Replace the top letter `Fin.last k` of a word over `Fin (k+1)` by `⟨k-1⟩`. -/
def topSwap {k n : ℕ} (hk : 1 ≤ k) (x : Fin n → Option (Fin (k+1))) :
    Fin n → Option (Fin (k+1)) :=
  fun i => (x i).map (fun b => if b = Fin.last k then ⟨k-1, by omega⟩ else b)

lemma topSwap_none_iff {k n : ℕ} (hk : 1 ≤ k) (x : Fin n → Option (Fin (k+1))) (i : Fin n) :
    topSwap hk x i = none ↔ x i = none := by
  rw [topSwap]; cases x i <;> simp

lemma topSwap_rel {k n : ℕ} (hk : 1 ≤ k) (x : Fin n → Option (Fin (k+1))) (i : Fin n) :
    topSwap hk x i = x i ∨
      (x i = some (Fin.last k) ∧ topSwap hk x i = some ⟨k-1, by omega⟩) ∨
      (topSwap hk x i = some (Fin.last k) ∧ x i = some ⟨k-1, by omega⟩) := by
  rw [topSwap]
  cases hx : x i with
  | none => exact Or.inl rfl
  | some b =>
    by_cases hb : b = Fin.last k
    · exact Or.inr (Or.inl ⟨by rw [hb], by simp [hb]⟩)
    · exact Or.inl (by simp [hb])

lemma wsubst_embSub_topSwap {k m n : ℕ} (hk : 1 ≤ k) (T : Subspace (Fin m) (Fin k) (Fin n))
    (σ : Fin m → Option (Fin (k+1))) :
    embWord (wsubstG T (fun j => (σ j).map (collapseTop hk))) = topSwap hk (wsubstG (embSub T) σ) := by
  funext e
  cases h : T.idxFun e with
  | inl a =>
    simp only [wsubstG, h, embSub, Sum.map_inl, Sum.elim_inl, embWord, topSwap,
      Option.map_some, Fin.castSucc_ne_last, if_false]
  | inr e' =>
    simp only [wsubstG, h, embSub, Sum.map_inr, Sum.elim_inr, embWord, topSwap, Option.map_map]
    congr 1
    funext b
    exact castSucc_phi hk b

/-- Inductive step of the Graham-Rothschild theorem, using the insensitivity lemma. -/
theorem grlines_succ (k M r : ℕ) (hk : 1 ≤ k) (hr : 0 < r)
    (IH : ∃ n : ℕ, ∀ N : ℕ, n ≤ N → ∀ C : Line (Fin k) (Fin N) → Fin r,
      ∃ S : Subspace (Fin M) (Fin k) (Fin N), ∃ c : Fin r,
        ∀ σ : Fin M → Option (Fin k), (hσ : ∃ e, σ e = none) →
          C ⟨fun i => Sum.elim (fun a => some a) σ (S.idxFun i), by
              obtain ⟨e, he⟩ := hσ; obtain ⟨i, hi⟩ := S.proper e
              exact ⟨i, by simp [hi, he]⟩⟩ = c) :
    ∃ n : ℕ, ∀ N : ℕ, n ≤ N → ∀ C : Line (Fin (k+1)) (Fin N) → Fin r,
      ∃ S : Subspace (Fin M) (Fin (k+1)) (Fin N), ∃ c : Fin r,
        ∀ σ : Fin M → Option (Fin (k+1)), (hσ : ∃ e, σ e = none) →
          C ⟨fun i => Sum.elim (fun a => some a) σ (S.idxFun i), by
              obtain ⟨e, he⟩ := hσ; obtain ⟨i, hi⟩ := S.proper e
              exact ⟨i, by simp [hi, he]⟩⟩ = c := by
  obtain ⟨nn, hnn⟩ := IH
  obtain ⟨ni, hni⟩ := insens_lemma k nn r hk hr
  refine ⟨ni, fun N hN C => ?_⟩
  obtain ⟨S', hS'⟩ := hni N hN C
  let c' : Line (Fin k) (Fin nn) → Fin r := fun y =>
    C (lineOf' S' (embWord y.idxFun) ((hasVar_embWord y.idxFun).mpr y.proper))
  obtain ⟨S'', c, hS''⟩ := hnn nn le_rfl c'
  refine ⟨scomp S' (embSub S''), c, ?_⟩
  intro σ hσ
  set τ : Fin nn → Option (Fin (k+1)) := wsubstG (embSub S'') σ with hτdef
  set σk : Fin M → Option (Fin k) := fun j => (σ j).map (collapseTop hk) with hσkdef
  have hσk : ∃ e, σk e = none := by
    obtain ⟨e, he⟩ := hσ; exact ⟨e, by simp [hσkdef, he]⟩
  have hτhole : ∃ e, τ e = none := by
    rw [hτdef]; exact (hasVarG (embSub S'') σ).mpr hσ
  have hτ'hole : ∃ e, topSwap hk τ e = none := by
    obtain ⟨e, he⟩ := hτhole; exact ⟨e, (topSwap_none_iff hk τ e).mpr he⟩
  have hrel : (∀ i, τ i = none ↔ topSwap hk τ i = none) ∧
      ∀ i, τ i = topSwap hk τ i ∨
        (τ i = some (Fin.last k) ∧ topSwap hk τ i = some ⟨k-1, by omega⟩) ∨
        (topSwap hk τ i = some (Fin.last k) ∧ τ i = some ⟨k-1, by omega⟩) := by
    refine ⟨fun i => (topSwap_none_iff hk τ i).symm, fun i => ?_⟩
    rcases topSwap_rel hk τ i with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hins : C (lineOf' S' τ hτhole) = C (lineOf' S' (topSwap hk τ) hτ'hole) :=
    hS' τ (topSwap hk τ) hτhole hτ'hole hrel
  have hxid : embWord (wsubstG S'' σk) = topSwap hk τ := by
    rw [hτdef]
    show embWord (wsubstG S'' (fun j => (σ j).map (collapseTop hk)))
      = topSwap hk (wsubstG (embSub S'') σ)
    exact wsubst_embSub_topSwap hk S'' σ
  have hcx : c' (lineOf' S'' σk hσk) = c := hS'' σk hσk
  have hcxt : C (lineOf' S' (topSwap hk τ) hτ'hole) = c := by
    rw [← hcx]
    congr 1
    apply Line.ext
    show wsubstG S' (topSwap hk τ) = wsubstG S' (embWord ((lineOf' S'' σk hσk).idxFun))
    rw [show (lineOf' S'' σk hσk).idxFun = wsubstG S'' σk from rfl, hxid]
  have hgoal : C (⟨fun i => Sum.elim (fun a => some a) σ ((scomp S' (embSub S'')).idxFun i), by
        obtain ⟨e, he⟩ := hσ; obtain ⟨i, hi⟩ := (scomp S' (embSub S'')).proper e
        exact ⟨i, by simp [hi, he]⟩⟩ : Line (Fin (k+1)) (Fin N)) = C (lineOf' S' τ hτhole) := by
    congr 1
    apply Line.ext
    funext i
    show Sum.elim (fun a => some a) σ ((scomp S' (embSub S'')).idxFun i)
      = Sum.elim (fun a => some a) τ (S'.idxFun i)
    rw [hτdef]
    cases h : S'.idxFun i <;> simp only [scomp, wsubstG, h, Sum.elim_inl, Sum.elim_inr]
  rw [hgoal]
  exact hins.trans hcxt

/-- **Graham–Rothschild theorem** (colourings of the combinatorial lines, see e.g. Dodos,
Kanellopoulos, Tyros).  For every `k, M, r` there is `n` such that every `r`-colouring of the
combinatorial lines of `[k]^N` (`N ≥ n`) has an `M`-dimensional subspace all of whose lines have
the same colour. -/
theorem grlines (k M r : ℕ) (hk : 1 ≤ k) (hr : 0 < r) :
    ∃ n : ℕ, ∀ N : ℕ, n ≤ N → ∀ C : Combinatorics.Line (Fin k) (Fin N) → Fin r,
    ∃ S : Combinatorics.Subspace (Fin M) (Fin k) (Fin N), ∃ c : Fin r,
      ∀ σ : Fin M → Option (Fin k), (hσ : ∃ e, σ e = none) →
        C ⟨fun i => Sum.elim (fun a => some a) σ (S.idxFun i), by
            obtain ⟨e, he⟩ := hσ; obtain ⟨i, hi⟩ := S.proper e
            exact ⟨i, by simp [hi, he]⟩⟩ = c := by
  revert hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    rcases eq_or_lt_of_le hk with hk1 | hk2
    · rw [← hk1]; exact grlines_base M r hr
    · have hkm1 : 1 ≤ k - 1 := by omega
      have hk_eq : k = (k - 1) + 1 := by omega
      rw [hk_eq]
      exact grlines_succ (k - 1) M r hkm1 hr (ih (k - 1) (by omega) hkm1)




end Aux

/-! ### The density Hales–Jewett assembly -/

/-- The combinatorial line of `Fin k → Fin n` determined by the pattern `σ`. -/
def lineOf {k M N : ℕ} (S : Combinatorics.Subspace (Fin M) (Fin k) (Fin N))
    (σ : Fin M → Option (Fin k)) (hσ : ∃ e, σ e = none) : Combinatorics.Line (Fin k) (Fin N) :=
  ⟨fun i => Sum.elim (fun a => some a) σ (S.idxFun i), by
    obtain ⟨e, he⟩ := hσ; obtain ⟨i, hi⟩ := S.proper e
    exact ⟨i, by simp [hi, he]⟩⟩

/-- `DHJ k`: the density Hales–Jewett property for the alphabet `Fin k` (Mathlib `Line` form). -/
def DHJ (k : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ T : Finset (Fin n → Fin k),
    δ * (k : ℝ) ^ n ≤ (T.card : ℝ) →
      ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ x : Fin k, l x ∈ T

/-- `DHJw k`: the same, in the `w, P` formulation used by
`finite_szemeredi_of_density_hales_jewett`. -/
def DHJw (k : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ T : Finset (Fin n → Fin k),
    δ * (k : ℝ) ^ n ≤ (T.card : ℝ) →
      ∃ w : Fin n → Fin k, ∃ P : Finset (Fin n), P.Nonempty ∧
        ∀ v : Fin k, (fun i => if i ∈ P then v else w i) ∈ T

/-- Graham–Rothschild for colourings of combinatorial lines. -/
def GRLines (k M r : ℕ) : Prop :=
  ∃ n : ℕ, ∀ N : ℕ, n ≤ N → ∀ C : Combinatorics.Line (Fin k) (Fin N) → Fin r,
    ∃ S : Combinatorics.Subspace (Fin M) (Fin k) (Fin N), ∃ c : Fin r,
      ∀ σ : Fin M → Option (Fin k), (hσ : ∃ e, σ e = none) → C (lineOf S σ hσ) = c

/-- The line of `[k]^n` determined by `(w,P)`. -/
def lineOfWP {n k : ℕ} (w : Fin n → Fin k) (P : Finset (Fin n)) (hP : P.Nonempty) :
    Combinatorics.Line (Fin k) (Fin n) :=
  ⟨fun i => if i ∈ P then none else some (w i), by
    obtain ⟨i, hi⟩ := hP; exact ⟨i, by simp [hi]⟩⟩

lemma lineOfWP_apply {n k : ℕ} (w : Fin n → Fin k) (P : Finset (Fin n)) (hP : P.Nonempty)
    (v : Fin k) : lineOfWP w P hP v = fun i => if i ∈ P then v else w i := by
  funext i; by_cases hi : i ∈ P <;> simp [Combinatorics.Line.toFun, lineOfWP, hi]

lemma DHJw_of_DHJ {k : ℕ} (hk : 0 < k) (h : DHJ k) : DHJw k := by
  intro δ hδ
  obtain ⟨n₀, hn⟩ := h δ hδ
  refine ⟨n₀, fun n hn' T hT => ?_⟩
  obtain ⟨l, hl⟩ := hn n hn' T hT
  refine ⟨fun i => (l.idxFun i).getD ⟨0, hk⟩,
    Finset.univ.filter (fun i => l.idxFun i = none), ?_, ?_⟩
  · obtain ⟨i, hi⟩ := l.proper; exact ⟨i, by simp [hi]⟩
  · intro v
    have hval : l v = fun i => if i ∈ Finset.univ.filter (fun i => l.idxFun i = none) then v
        else (l.idxFun i).getD ⟨0, hk⟩ := by
      funext i
      by_cases hi : l.idxFun i = none
      · have : i ∈ Finset.univ.filter (fun i => l.idxFun i = none) := by simp [hi]
        simp [Combinatorics.Line.toFun, hi, this]
      · have hne : ¬ (i ∈ Finset.univ.filter (fun i => l.idxFun i = none)) := by simp [hi]
        obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hi
        simp [Combinatorics.Line.toFun, ha, hne]
    rw [← hval]; exact hl v

lemma DHJ_of_DHJw {k : ℕ} (hk : 0 < k) (h : DHJw k) : DHJ k := by
  intro δ hδ
  obtain ⟨n₀, hn⟩ := h δ hδ
  exact ⟨n₀, fun n hn' T hT => by
    obtain ⟨w, P, hP, hw⟩ := hn n hn' T hT
    exact ⟨lineOfWP w P hP, fun v => by
      rw [lineOfWP_apply]; exact hw v⟩⟩

/-- `DHJ 2`, from the commons lemma `dhj_two` (Sperner's theorem). -/
theorem DHJ_two : DHJ 2 :=
  DHJ_of_DHJw (by norm_num) (by
    intro δ hδ
    obtain ⟨n₀, hn⟩ := dhj_two δ hδ
    exact ⟨n₀, fun n hn' T hT => hn n hn' T hT⟩)

theorem grlines_two (k M : ℕ) (hk : 1 ≤ k) : GRLines k M 2 := by
  obtain ⟨n, hn⟩ := Aux.grlines k M 2 hk (by norm_num)
  exact ⟨n, fun N hN C => hn N hN C⟩

theorem DHJ_succ (k : ℕ) (hk : 1 ≤ k) (h : DHJ k) (hgr : ∀ M : ℕ, GRLines k M 2) : DHJ (k+1) := by
  have hinc := Commons.Combinatorics.Ramsey.dkt_density_increment_unif k hk h (fun M => hgr M)
  exact Commons.Combinatorics.Ramsey.dkt_dhj_of_increment_unif (k+1) (by omega) hinc

/-- `DHJ k` for every `k ≥ 2`. -/
theorem DHJ_all : ∀ k : ℕ, 2 ≤ k → DHJ k := by
  intro k hk
  induction k with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_or_ge j 2 with hj | hj
    · have : j = 1 := by omega
      subst this; exact DHJ_two
    · exact DHJ_succ j (by omega) (ih hj) (fun M => grlines_two j M (by omega))

/-- The requested lemma. -/
theorem finite_szemeredi (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ B : Finset ℕ, B ⊆ Finset.range N →
      δ * (N : ℝ) ≤ (B.card : ℝ) →
        ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ (B : Set ℕ) :=
  finite_szemeredi_of_density_hales_jewett
    (fun k hk => DHJw_of_DHJ (by omega) (DHJ_all k hk)) k δ hδ

end Commons.Combinatorics.Additive.Szemeredi
