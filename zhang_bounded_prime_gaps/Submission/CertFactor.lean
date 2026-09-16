import Mathlib
import Submission.CertXside
import Submission.SlabDP
import Submission.CertIndex
import Submission.Commons.Algebra.Multinomial.mulBin_comm
import Submission.Commons.Data.Nat.multinomial_factor_rec

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

open scoped BigOperators
open Finset

namespace Commons.NumberTheory.MaynardSieve

abbrev XVec := MV → ℕ

def mulA (Q : XVec) : XVec :=
  fun m => Q m + ∑ v : Fin 12, if 1 ≤ m v then Nat.factorial (2 * ((v : ℕ) + 1)) * Q (m - evec v) else 0

def mulH (w : Fin 12) (Q : XVec) : XVec :=
  fun m => Nat.factorial (2 * ((w : ℕ) + 1)) * Q m
    + ∑ v : Fin 12,
        if 1 ≤ m v then Nat.factorial (2 * ((v : ℕ) + 1) + 2 * ((w : ℕ) + 1)) * Q (m - evec v)
        else 0

def mulBin (c : ℕ) (d : Fin 12 → ℕ) (Q : XVec) : XVec :=
  fun m => c * Q m + ∑ v : Fin 12, if 1 ≤ m v then d v * Q (m - evec v) else 0

/-- Commutativity of the two "binomial" coefficient operators (from the commons). -/
theorem mulBin_comm' (c c' : ℕ) (d d' : Fin 12 → ℕ) (Q : XVec) :
    mulBin c d (mulBin c' d' Q) = mulBin c' d' (mulBin c d Q) :=
  funext (fun m => Commons.Algebra.Multinomial.mulBin_comm c c' d d' Q m)

/-- The Pascal-type recursion for the scalar factor `mc` (from the commons). -/
theorem multinomial_factor_rec' (k : ℕ) (n : MV) :
    Nat.choose (k + 1) (∑ i, n i) * Nat.multinomial Finset.univ n
      = Nat.choose k (∑ i, n i) * Nat.multinomial Finset.univ n
        + ∑ q : Fin 12, if 1 ≤ n q then
            Nat.choose k (∑ i, n i - 1)
              * Nat.multinomial Finset.univ (n - (Pi.single q (1:ℕ) : Fin 12 → ℕ))
          else 0 :=
  Commons.Data.Nat.multinomial_factor_rec k n

theorem xslots_cons_A_eq (t : List CertSlot) : xslots (CertSlot.A :: t) = mulA (xslots t) := rfl

theorem xslots_cons_H_eq (w : Fin 12) (t : List CertSlot) :
    xslots (CertSlot.H w :: t) = mulH w (xslots t) := rfl

theorem mulA_eq_mulBin : mulA = mulBin 1 (fun v : Fin 12 => Nat.factorial (2 * ((v : ℕ) + 1))) := by
  funext Q m; simp only [mulA, mulBin, one_mul]

theorem mulH_eq_mulBin (w : Fin 12) :
    mulH w = mulBin (Nat.factorial (2 * ((w : ℕ) + 1)))
      (fun v : Fin 12 => Nat.factorial (2 * ((v : ℕ) + 1) + 2 * ((w : ℕ) + 1))) := by
  funext Q m; simp only [mulH, mulBin]

def opSlot : CertSlot → XVec → XVec
  | CertSlot.A => mulA
  | CertSlot.H w => mulH w

def xops : List CertSlot → XVec → XVec
  | [], Q => Q
  | CertSlot.A :: t, Q => mulA (xops t Q)
  | CertSlot.H w :: t, Q => mulH w (xops t Q)

theorem xops_cons (s : CertSlot) (t : List CertSlot) (Q : XVec) :
    xops (s :: t) Q = opSlot s (xops t Q) := by cases s <;> rfl

theorem xslots_eq_xops (L : List CertSlot) : xslots L = xops L (xslots []) := by
  induction L with
  | nil => rfl
  | cons s t ih =>
      cases s with
      | A => rw [xslots_cons_A_eq, xops_cons, ih]; rfl
      | H w => rw [xslots_cons_H_eq, xops_cons, ih]; rfl

theorem xops_append (L M : List CertSlot) (Q : XVec) :
    xops (L ++ M) Q = xops L (xops M Q) := by
  induction L with
  | nil => rfl
  | cons s t ih => rw [List.cons_append, xops_cons, xops_cons, ih]

theorem opSlot_comm (s s' : CertSlot) (R : XVec) :
    opSlot s (opSlot s' R) = opSlot s' (opSlot s R) := by
  cases s with
  | A =>
      cases s' with
      | A => rfl
      | H w' =>
          simp only [opSlot]
          rw [mulA_eq_mulBin, mulH_eq_mulBin]
          exact mulBin_comm' _ _ _ _ _
  | H w =>
      cases s' with
      | A =>
          simp only [opSlot]
          rw [mulA_eq_mulBin, mulH_eq_mulBin]
          exact (mulBin_comm' _ _ _ _ _).symm
      | H w' =>
          simp only [opSlot]
          rw [mulH_eq_mulBin, mulH_eq_mulBin]
          exact mulBin_comm' _ _ _ _ _

theorem xops_perm : ∀ {L L' : List CertSlot}, L.Perm L' → ∀ Q, xops L Q = xops L' Q
  | _, _, .nil, Q => rfl
  | _, _, .cons a h, Q => by rw [xops_cons, xops_cons, xops_perm h]
  | _, _, .swap a b l, Q => by
      rw [xops_cons, xops_cons, xops_cons, xops_cons, opSlot_comm]
  | _, _, .trans h1 h2, Q => by rw [xops_perm h1, xops_perm h2]

theorem xslots_perm {L L' : List CertSlot} (h : L.Perm L') : xslots L = xslots L' := by
  rw [xslots_eq_xops L, xslots_eq_xops L']
  exact xops_perm h _

def hpartL (l : List (Fin 12)) (n : MV) : List CertSlot :=
  (l.map (fun i => List.replicate (n i) (CertSlot.H i))).flatten

theorem Hpart_eq_hpartL (n : MV) :
    (List.ofFn (fun i : Fin 12 => List.replicate (n i) (CertSlot.H i))).flatten
      = hpartL (List.finRange 12) n := by
  simp only [hpartL, List.ofFn_eq_map]

theorem hpartL_cons (i : Fin 12) (t : List (Fin 12)) (n : MV) :
    hpartL (i :: t) n = List.replicate (n i) (CertSlot.H i) ++ hpartL t n := by
  simp only [hpartL, List.map_cons, List.flatten_cons]

theorem hpartL_eq_of_notMem (t : List (Fin 12)) (q : Fin 12) (n : MV) (h : q ∉ t) :
    hpartL t (n - evec q) = hpartL t n := by
  induction t with
  | nil => rfl
  | cons i t ih =>
      have hq : q ≠ i := fun hc => h (by simp [hc])
      have ht : q ∉ t := fun hc => h (by simp [hc])
      rw [hpartL_cons, hpartL_cons, ih ht]
      have h1 : (evec q : Fin 12 → ℕ) i = 0 := by
        rw [evec]; exact Pi.single_eq_of_ne (Ne.symm hq) 1
      have hthis : (n - evec q) i = n i := by rw [Pi.sub_apply, h1, tsub_zero]
      exact congrArg (fun x => List.replicate x (CertSlot.H i) ++ hpartL t n) hthis

theorem replicate_append_perm (m : ℕ) (a b : CertSlot) (M : List CertSlot) :
    (List.replicate m b ++ (a :: M)).Perm (a :: (List.replicate m b ++ M)) := by
  induction m with
  | zero => exact List.Perm.refl _
  | succ k ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact (List.Perm.cons b ih).trans (List.Perm.swap a b (List.replicate k b ++ M))

theorem hpartL_insert (l : List (Fin 12)) (hl : l.Nodup) (q : Fin 12) (n : MV)
    (hmem : q ∈ l) (hq : 1 ≤ n q) :
    (hpartL l n).Perm (CertSlot.H q :: hpartL l (n - evec q)) := by
  induction l with
  | nil => exact absurd hmem (by simp)
  | cons i t ih =>
      have hnod : t.Nodup := hl.of_cons
      have hinot : i ∉ t := (List.nodup_cons.mp hl).1
      rcases List.mem_cons.mp hmem with h | hmemt
      · rw [h]
        have hqi1 : 1 ≤ n i := h ▸ hq
        rw [hpartL_cons, hpartL_cons, hpartL_eq_of_notMem t i n hinot]
        have hni : (n - evec i) i = n i - 1 := by
          rw [Pi.sub_apply, evec, Pi.single_eq_same]
        rw [hni]
        have hrep : List.replicate (n i) (CertSlot.H i)
            = CertSlot.H i :: List.replicate (n i - 1) (CertSlot.H i) := by
          conv_lhs => rw [show n i = (n i - 1) + 1 from by omega]
          rw [List.replicate_succ]
        rw [hrep, List.cons_append]
      · have hqi : i ≠ q := fun hc => hinot (hc ▸ hmemt)
        rw [hpartL_cons, hpartL_cons]
        have h1 : (evec q : Fin 12 → ℕ) i = 0 := by
          rw [evec]; exact Pi.single_eq_of_ne hqi 1
        have hneq : (n - evec q) i = n i := by rw [Pi.sub_apply, h1, tsub_zero]
        rw [hneq]
        exact (List.Perm.append_left _ (ih hnod hmemt)).trans
          (replicate_append_perm (n i) (CertSlot.H q) (CertSlot.H i) (hpartL t (n - evec q)))

theorem sum_sub_evec_add_one (n : MV) (q : Fin 12) (hq : 1 ≤ n q) :
    ∑ i, (n - evec q) i + 1 = ∑ i, n i := by
  have h1 : ∀ i, i ≠ q → (n - evec q) i = n i := by
    intro i hi
    rw [Pi.sub_apply, evec, Pi.single_eq_of_ne hi 1, tsub_zero]
  have h2 : (n - evec q) q = n q - 1 := by
    rw [Pi.sub_apply, evec, Pi.single_eq_same]
  have hA : ∑ i, (n - evec q) i
      = ∑ i ∈ (Finset.univ.erase q), (n - evec q) i + (n q - 1) := by
    rw [← Finset.sum_erase_add _ (n - evec q) (Finset.mem_univ q), h2]
  have hB : ∑ i, n i = ∑ i ∈ (Finset.univ.erase q), n i + n q := by
    rw [← Finset.sum_erase_add _ n (Finset.mem_univ q)]
  have hC : ∑ i ∈ (Finset.univ.erase q), (n - evec q) i
      = ∑ i ∈ (Finset.univ.erase q), n i :=
    Finset.sum_congr rfl (fun i hi => h1 i (Finset.mem_erase.mp hi).1)
  rw [hA, hB, hC]
  omega

theorem sum_sub_evec (n : MV) (q : Fin 12) (hq : 1 ≤ n q) :
    ∑ i, (n - evec q) i = ∑ i, n i - 1 := by
  have h := sum_sub_evec_add_one n q hq
  omega

theorem finRange_nodup : (List.finRange 12).Nodup := List.nodup_finRange 12

/-- **The H-insertion lemma for the slot list of the certificate's x-side.** -/
theorem slotList_insert (k : ℕ) (q : Fin 12) (n : MV) (hq : 1 ≤ n q) :
    (CertSlot.H q :: slotList k (n - evec q)).Perm (slotList (k + 1) n) := by
  have hsum := sum_sub_evec n q hq
  have hle : n q ≤ ∑ i, n i := Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ q)
  have hpart := hpartL_insert (List.finRange 12) finRange_nodup q n (List.mem_finRange q) hq
  simp only [slotList, Hpart_eq_hpartL]
  rw [hsum]
  rw [show k - (∑ i, n i - 1) = k + 1 - ∑ i, n i from by omega]
  exact ((List.Perm.append_left (List.replicate (k + 1 - ∑ i, n i) CertSlot.A) hpart).trans
      (replicate_append_perm (k + 1 - ∑ i, n i) (CertSlot.H q) CertSlot.A
        (hpartL (List.finRange 12) (n - evec q)))).symm

def mc (k : ℕ) (n : MV) : ℕ := Nat.choose k (∑ i, n i) * Nat.multinomial Finset.univ n

def Phi (k : ℕ) (n : MV) : XVec := xslots (slotList k n)

theorem mc_succ (k : ℕ) (n : MV) :
    mc (k + 1) n = mc k n + ∑ q : Fin 12, if 1 ≤ n q then mc k (n - evec q) else 0 := by
  have h := multinomial_factor_rec' k n
  have hsum2 : (∑ q : Fin 12, if 1 ≤ n q then
        Nat.choose k (∑ i, n i - 1)
          * Nat.multinomial Finset.univ (n - (Pi.single q (1:ℕ) : Fin 12 → ℕ)) else 0)
      = ∑ q : Fin 12, if 1 ≤ n q then mc k (n - evec q) else 0 := by
    refine Finset.sum_congr rfl (fun q _ => ?_)
    by_cases hq : 1 ≤ n q
    · rw [if_pos hq, if_pos hq]
      simp only [mc]
      rw [sum_sub_evec n q hq]
      simp only [evec]
    · rw [if_neg hq, if_neg hq]
  rw [hsum2] at h
  simpa only [mc] using h

theorem mc_eq_zero (k : ℕ) (n : MV) (h : k < ∑ i, n i) : mc k n = 0 := by
  simp only [mc]
  rw [Nat.choose_eq_zero_of_lt h, zero_mul]

theorem mulA_Phi (k : ℕ) (n : MV) (h : ∑ w, n w ≤ k) : mulA (Phi k n) = Phi (k + 1) n := by
  unfold Phi
  rw [← xslots_cons_A_eq]
  congr 1
  simp only [slotList]
  rw [← List.cons_append, ← List.replicate_succ,
    show (k - ∑ w, n w) + 1 = k + 1 - ∑ w, n w from by omega]

theorem mulH_Phi (k : ℕ) (q : Fin 12) (n : MV) (hq : 1 ≤ n q) :
    mulH q (Phi k (n - evec q)) = Phi (k + 1) n := by
  unfold Phi
  rw [← xslots_cons_H_eq q (slotList k (n - evec q))]
  exact xslots_perm (slotList_insert k q n hq)

theorem indPart_eq_evec (p : Fin 12) : indPart p = evec p := by
  funext i
  simp only [indPart, evec]
  by_cases h : i = p
  · subst h; rw [if_pos rfl, Pi.single_eq_same]
  · rw [if_neg h, Pi.single_eq_of_ne h]

theorem slabStep_mcPhi (k : ℕ) (m n : MV) :
    slabStep (fun m n => mc k n * Phi k n m) m n = mc (k + 1) n * Phi (k + 1) n m := by
  rw [slabStep_eq]
  simp only [indPart_eq_evec]
  have h12 : mc k n * Phi k n m
      + (∑ p : Fin 12, if 0 < m p then
          Nat.factorial (2 * ((p : ℕ) + 1)) * (mc k n * Phi k n (m - evec p)) else 0)
      = mc k n * (mulA (Phi k n)) m := by
    simp only [mulA]
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h : 0 < m p
    · rw [if_pos h, if_pos (show 1 ≤ m p by omega)]
      ring
    · rw [if_neg h, if_neg (show ¬ 1 ≤ m p by omega), mul_zero]
  have h34 : (∑ q : Fin 12, if 0 < n q then
        Nat.factorial (2 * ((q : ℕ) + 1)) * (mc k (n - evec q) * Phi k (n - evec q) m)
      else 0)
      + (∑ p : Fin 12, ∑ q : Fin 12, if 0 < m p ∧ 0 < n q then
          Nat.factorial (2 * ((p : ℕ) + 1) + 2 * ((q : ℕ) + 1))
            * (mc k (n - evec q) * Phi k (n - evec q) (m - evec p)) else 0)
      = ∑ q : Fin 12, if 1 ≤ n q then mc k (n - evec q) * (mulH q (Phi k (n - evec q))) m
        else 0 := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    by_cases hq : 1 ≤ n q
    · rw [if_pos (show 0 < n q by omega), if_pos hq]
      simp only [mulH]
      simp only [mul_add, Finset.mul_sum]
      congr 1
      · ring
      · refine Finset.sum_congr rfl (fun p _ => ?_)
        by_cases hp : 0 < m p
        · rw [if_pos ⟨hp, show 0 < n q by omega⟩, if_pos (show 1 ≤ m p by omega)]
          ring
        · rw [if_neg (by intro hc; exact hp hc.1), if_neg (show ¬ 1 ≤ m p by omega),
              mul_zero]
    · rw [if_neg (show ¬ 0 < n q by omega), if_neg hq]
      rw [Finset.sum_eq_zero]
      · rfl
      · intro p _
        exact if_neg (by intro hc; omega)
  rw [add_assoc, h12, h34]
  have hsum : (∑ q : Fin 12, if 1 ≤ n q then mc k (n - evec q) * (mulH q (Phi k (n - evec q))) m
        else 0)
      = (∑ q : Fin 12, if 1 ≤ n q then mc k (n - evec q) else 0) * Phi (k + 1) n m := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    by_cases hq : 1 ≤ n q
    · rw [if_pos hq, if_pos hq, congrFun (mulH_Phi k q n hq) m]
    · rw [if_neg hq, if_neg hq, zero_mul]
  by_cases hk : ∑ w, n w ≤ k
  · rw [congrFun (mulA_Phi k n hk) m, hsum, ← add_mul, ← mc_succ]
  · have hzero : mc k n = 0 := mc_eq_zero k n (by omega)
    have hms : (∑ q : Fin 12, if 1 ≤ n q then mc k (n - evec q) else 0) = mc (k + 1) n := by
      rw [mc_succ, hzero, zero_add]
    rw [hzero, zero_mul, zero_add, hsum, hms]

theorem slabLevel_eq_mc (k : ℕ) (m n : MV) : slabLevel k m n = mc k n * Phi k n m := by
  induction k generalizing m n with
  | zero =>
      rw [slabLevel_zero]
      simp only [slabBase]
      by_cases hn : n = 0
      · subst hn
        have hmc : mc 0 0 = 1 := by
          simp [mc, Nat.multinomial]
        have hphi : Phi 0 0 m = if m = 0 then 1 else 0 := by
          unfold Phi
          have hsl : slotList 0 (0 : MV) = [] := by
            simp [slotList]
          rw [hsl, xslots_nil]
        rw [hmc, hphi]
        by_cases hm : m = 0 <;> simp [hm]
      · have hne : 0 < ∑ i, n i := by
          rcases Nat.eq_zero_or_pos (∑ i, n i) with h0 | hpos
          · exact absurd (funext (fun i => by
              have hz := (Finset.sum_eq_zero_iff.mp h0) i (Finset.mem_univ i)
              simpa using hz)) hn
          · exact hpos
        rw [if_neg (fun hc => hn hc.2)]
        have hmc : mc 0 n = 0 := by
          simp only [mc]
          rw [Nat.choose_eq_zero_of_lt hne, zero_mul]
        rw [hmc, zero_mul]
  | succ k ih =>
      have hfun : slabLevel k = (fun m n => mc k n * Phi k n m) :=
        funext (fun m' => funext (fun n' => ih m' n'))
      show slabStep (slabLevel k) m n = mc (k + 1) n * Phi (k + 1) n m
      rw [hfun]
      exact slabStep_mcPhi k m n

theorem slabLevel_eq_xcoe (k : ℕ) (m n : MV) : slabLevel k m n = xcoe k n m := by
  rw [slabLevel_eq_mc]
  simp only [mc, Phi, xcoe]
  rw [show Nat.multinomial Finset.univ n
      = Nat.factorial (∑ i, n i) / ∏ i, Nat.factorial (n i) from rfl]

/-- **THE FACTORISATION.**  `Ssum` factorises into a one-sided computation: for signatures over
the twelve even parts `2,…,24`, the y-side contributes only the multinomial factor
`C(k,|β|)·|β|!/∏σ!` and the x-side is the coefficient of `A^{k-|β|}·∏_w h_w^{σ_w}`. -/
theorem Ssum_eq_xcoe (β β' : List ℕ) (k : ℕ)
    (hβ : ∀ a ∈ β, ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1))
    (hβ' : ∀ a ∈ β', ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1)) :
    Ssum β β' k = xcoe k (mult β') (mult β) := by
  rw [Ssum_eq_slabLevel β β' k hβ hβ', slabLevel_eq_xcoe]

end Commons.NumberTheory.MaynardSieve
