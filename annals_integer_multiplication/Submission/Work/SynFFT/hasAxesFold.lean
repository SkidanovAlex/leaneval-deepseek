import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.fft1.stepKit
import Submission.Work.Params.listSizesBig
import Submission.Work.SynFFT.axFoldVBounds
import Submission.Work.SynFFT.axFoldCost

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Work.SynFFT

open HvdH

/-! ## Plumbing: the missing `WordR` step lemmas and elementary stack moves -/

namespace AxKit

open Work.SynFFT.MrgKit

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-- `LayoutLib.length` on a concrete list. -/
theorem lengthStep {main : Cmd} {lenP : Cmd} {Kl : ℕ}
    (h : ∀ (xs : List Val), WordR main lenP
      (fun vs => ∃ rest, vs = ofList xs :: rest)
      (fun vs out => ∃ rest, vs = ofList xs :: rest ∧
        out = .int (xs.length : ℤ) :: ofList xs :: rest)
      (fun _ => Kl * (vsz (ofList xs) + 1)))
    (xs t : List Val) (D : ℕ) (hD : Kl * (vsz (ofList xs) + 1) ≤ D) :
    WordR main lenP (fun vs => vs = ofList xs :: t)
      (fun _ out => out = .int (xs.length : ℤ) :: ofList xs :: t) (fun _ => D) := by
  refine WordR_conseqC (h xs) ⟨t, rfl⟩ ?_ hD
  intro out hout
  obtain ⟨r, h1, h2⟩ := hout
  simp only [List.cons.injEq] at h1
  obtain ⟨-, rfl⟩ := h1
  exact h2

/-- `LayoutLib.reverse` on a concrete list. -/
theorem reverseStep {main : Cmd} {revP : Cmd} {Kr : ℕ}
    (h : ∀ (xs : List Val), WordR main revP
      (fun vs => ∃ rest, vs = ofList xs :: rest)
      (fun vs out => ∃ rest, vs = ofList xs :: rest ∧ out = ofList xs.reverse :: rest)
      (fun _ => Kr * (vsz (ofList xs) + 1)))
    (xs t : List Val) (D : ℕ) (hD : Kr * (vsz (ofList xs) + 1) ≤ D) :
    WordR main revP (fun vs => vs = ofList xs :: t)
      (fun _ out => out = ofList xs.reverse :: t) (fun _ => D) := by
  refine WordR_conseqC (h xs) ⟨t, rfl⟩ ?_ hD
  intro out hout
  obtain ⟨r, h1, h2⟩ := hout
  simp only [List.cons.injEq] at h1
  obtain ⟨-, rfl⟩ := h1
  exact h2

/-- `IntLib.tdiv` on two concrete integers. -/
theorem tdivStep {main : Cmd} {tdP : Cmd} {Kt : ℕ}
    (h : BinOp main tdP (fun _ b => b ≠ 0) Int.tdiv (fun a b => Kt * isz a * isz b))
    (a b : ℤ) (t : List Val) (hb : b ≠ 0) (D : ℕ) (hD : Kt * isz a * isz b ≤ D) :
    WordR main tdP (fun vs => vs = .int a :: .int b :: t)
      (fun _ out => out = .int (a.tdiv b) :: t) (fun _ => D) := by
  unfold BinOp at h
  refine WordR_conseqC h ⟨a, b, t, rfl, hb⟩ ?_ hD
  intro out hout
  obtain ⟨a', b', t', h1, hout'⟩ := hout
  simp only [List.cons.injEq, Val.int.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  exact hout'

/-- `roll k` followed by `drop`: delete the element at index `k`. -/
theorem rollDropStep {main : Cmd} {rollP : ℕ → Cmd} {kdrP : Cmd} {Kr Kdr : ℕ}
    (hroll : ∀ k, WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k+1) * (((vs.take (k+1)).map vsz).sum + 1)))
    (hdr : WordR main kdrP (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => Kdr * (vsz (vs.headD .nil) + 1)))
    (k : ℕ) (A : List Val) (hk : k < A.length) (D1 D2 : ℕ)
    (h1 : Kr * (k+1) * (((A.take (k+1)).map vsz).sum + 1) ≤ D1)
    (h2 : Kdr * (vsz (A.getD k .nil) + 1) ≤ D2) :
    WordR main (rollP k ;;; kdrP) (fun vs => vs = A)
      (fun _ out => out = A.eraseIdx k) (fun _ => D1 + D2) := by
  refine WordR_seqC (rollStep hroll k A hk D1 h1) ?_
  refine kdropStep hdr (A.getD k .nil :: A.eraseIdx k) (by simp) D2 ?_
  simpa using h2

end AxKit

/-! ## Pure facts: products of lists, `Nat.clog`, and value sizes -/

namespace AxPure

open HvdH
open Work.SynFFT.MrgKit

lemma prod_take_length (l : List ℕ) : (l.take l.length).prod = l.prod := by
  rw [List.take_length]

lemma prod_drop_length (l : List ℕ) : (l.drop l.length).prod = 1 := by
  rw [List.drop_length]; rfl

lemma prod_take_mul_drop (l : List ℕ) (j : ℕ) (h : j ≤ l.length) :
    (l.take j).prod * (l.drop j).prod = l.prod := by
  conv_rhs => rw [← List.take_append_drop j l]
  rw [List.prod_append]

lemma one_le_prod_of (l : List ℕ) (h : ∀ t ∈ l, 1 ≤ t) : 1 ≤ l.prod :=
  List.one_le_prod h

lemma le_prod_of_mem (l : List ℕ) (t : ℕ) (h : ∀ s ∈ l, 0 < s) (hm : t ∈ l) : t ≤ l.prod := by
  obtain ⟨a, b, rfl⟩ := List.mem_iff_append.mp hm
  rw [List.prod_append, List.prod_cons]
  have h1 : 1 ≤ a.prod := one_le_prod_of a (fun s hs => by have := h s (by simp [hs]); omega)
  have h2 : 1 ≤ b.prod := one_le_prod_of b (fun s hs => by have := h s (by simp [hs]); omega)
  have ht : 1 ≤ t := by have := h t (by simp); omega
  calc t = 1 * (t * 1) := by ring
    _ ≤ a.prod * (t * b.prod) := Nat.mul_le_mul h1 (Nat.mul_le_mul_left t h2)

lemma prod_take_succ (l : List ℕ) (j : ℕ) (h : j < l.length) :
    (l.take (j+1)).prod = (l.take j).prod * l.getD j 1 := by
  rw [← List.take_concat_get' l j h, List.prod_append, List.getD_eq_getElem l 1 h]
  simp

lemma prod_drop_eq (l : List ℕ) (j : ℕ) (h : j < l.length) :
    (l.drop j).prod = l.getD j 1 * (l.drop (j+1)).prod := by
  rw [List.drop_eq_getElem_cons h, List.prod_cons, List.getD_eq_getElem l 1 h]

lemma drop_len_sub (l : List ℕ) (i : ℕ) (h : i < l.length) :
    l.drop (l.length - i - 1) = l.getD (l.length - 1 - i) 0 :: l.drop (l.length - i) := by
  have h2 : l.length - 1 - i < l.length := by omega
  conv_lhs => rw [show l.length - i - 1 = l.length - 1 - i by omega]
  rw [List.drop_eq_getElem_cons h2, List.getD_eq_getElem l 0 h2,
    show l.length - 1 - i + 1 = l.length - i by omega]

lemma length_drop_len_sub (l : List ℕ) (i : ℕ) (h : i ≤ l.length) :
    (l.drop (l.length - i)).length = i := by
  rw [List.length_drop]; omega

lemma getD_mem' (l : List ℕ) (i : ℕ) (h : i < l.length) :
    l.getD (l.length - 1 - i) 0 ∈ l := by
  have h2 : l.length - 1 - i < l.length := by omega
  rw [List.getD_eq_getElem l 0 h2]
  exact List.getElem_mem ..

lemma rev_map_getD (l : List ℕ) (i : ℕ) (h : i < l.length) :
    ((l.map (fun t : ℕ => Val.int (t : ℤ))).reverse).getD i .nil
      = .int (((l.getD (l.length - 1 - i) 0 : ℕ) : ℤ)) := by
  have h2 : l.length - 1 - i < l.length := by omega
  rw [List.getD_eq_getElem _ _ (by simpa [List.length_reverse, List.length_map] using h),
    List.getElem_reverse, List.getElem_map, List.getD_eq_getElem l 0 h2]
  simp

lemma pow_length_le_prod (l : List ℕ) (h : ∀ t ∈ l, 2 ≤ t) : 2 ^ l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, List.prod_cons]
    have ha : 2 ≤ a := h a (by simp)
    have ht : ∀ s ∈ t, 2 ≤ s := fun s hs => h s (by simp [hs])
    have hrec : 2 ^ t.length ≤ t.prod := ih ht
    calc 2 ^ (t.length + 1) = 2 * 2 ^ t.length := by rw [pow_succ]; ring
      _ ≤ a * t.prod := Nat.mul_le_mul ha hrec

lemma clog_pow_two (m : ℕ) (hm : 1 ≤ m) : Nat.clog 2 (2 ^ m) = m :=
  Nat.clog_pow 2 m (by norm_num)

lemma pow_clog_of_isPow2 (t : ℕ) (h : IsPow2 t) : t = 2 ^ Nat.clog 2 t := by
  obtain ⟨k, -, rfl⟩ := h
  rw [Nat.clog_pow 2 k (by norm_num)]

lemma two_le_of_isPow2 (t : ℕ) (h : IsPow2 t) : 2 ≤ t := by
  obtain ⟨k, hk, rfl⟩ := h
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

lemma log_eq_clog_of_isPow2 (t : ℕ) (h : IsPow2 t) : Nat.log 2 t = Nat.clog 2 t := by
  obtain ⟨k, -, rfl⟩ := h
  rw [Nat.log_pow (by norm_num), Nat.clog_pow 2 k (by norm_num)]

lemma one_le_clog (t : ℕ) (h : 2 ≤ t) : 1 ≤ Nat.clog 2 t :=
  Nat.clog_pos (by norm_num) (by omega)

lemma clog_le_size (t M : ℕ) (h : IsPow2 t) (h2 : t ≤ M) : Nat.clog 2 t ≤ M.size := by
  rw [Nat.clog_le_iff_le_pow (by norm_num)]
  exact le_of_lt (lt_of_le_of_lt h2 (Nat.lt_size_self M))

lemma size_le_self (M : ℕ) : M.size ≤ M :=
  Nat.size_le.mpr (Nat.lt_two_pow_self (n := M))

lemma isz_le_size (t M : ℕ) (h : t ≤ M) : isz (t : ℤ) ≤ M.size + 2 := by
  have h1 : ((t : ℤ)).natAbs = t := Int.natAbs_natCast t
  simp only [isz, h1]
  have := Nat.size_le_size h
  omega

lemma vsz_ofList_cvecs_le (p r M : ℕ) (ws : List (List (ℤ × ℤ))) (hp : 1 ≤ p) (hM : 1 ≤ M)
    (hlen : ws.length = M) (hdisc : ∀ w ∈ ws, InDiscVec p r w) :
    vsz (ofList (cvecs ws)) ≤ 14 * (M * (r + 1) * (p + 1)) := by
  have h1 : ∀ v ∈ cvecs ws, vsz v ≤ 13 * (r + 1) * (p + 1) := by
    intro v hv
    rw [cvecs, List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact vsz_cvecVal_le p r w (hdisc w hw).1 (hdisc w hw).2
  have h2 : vsz (ofList (cvecs ws)) ≤ M * (13 * (r + 1) * (p + 1) + 1) + 1 :=
    vsz_ofList_le_of_bound (cvecs ws) (13 * (r + 1) * (p + 1)) M h1
      (by rw [cvecs, List.length_map]; exact le_of_eq hlen)
  set N : ℕ := M * (r + 1) * (p + 1) with hN
  have h4 : M + 1 ≤ N := by
    have h6 : 2 ≤ (r + 1) * (p + 1) := by
      have h8 : 1 ≤ r + 1 := by omega
      have h9 : 2 ≤ p + 1 := by omega
      calc 2 = 1 * 2 := by ring
        _ ≤ (r + 1) * (p + 1) := Nat.mul_le_mul h8 h9
    have h7 : 2 * M ≤ M * ((r + 1) * (p + 1)) := by
      calc 2 * M = M * 2 := by ring
        _ ≤ M * ((r + 1) * (p + 1)) := Nat.mul_le_mul_left M h6
    rw [hN]
    calc M + 1 ≤ 2 * M := by omega
      _ ≤ M * ((r + 1) * (p + 1)) := h7
      _ = M * (r + 1) * (p + 1) := by ring
  have h5 : M * (13 * (r + 1) * (p + 1) + 1) + 1 ≤ 14 * N := by
    have : M * (13 * (r + 1) * (p + 1) + 1) = 13 * N + M := by
      rw [hN]; ring
    rw [this]
    have : 13 * N + M + 1 ≤ 13 * N + N := by omega
    linarith [hN] 
  calc vsz (ofList (cvecs ws)) ≤ M * (13 * (r + 1) * (p + 1) + 1) + 1 := h2
    _ ≤ 14 * N := h5
    _ = 14 * (M * (r + 1) * (p + 1)) := by rw [hN]

/-- `vsz (intList l)` is small when `l` is a list of numbers `≥ 2` with product `M`. -/
lemma vsz_intList_le (l : List ℕ) (M : ℕ) (h : ∀ t ∈ l, 2 ≤ t) (hM : l.prod = M) :
    vsz (intList l) ≤ 18 * (M + 1) := by
  have hle : ∀ t ∈ l, t ≤ M := by
    intro t ht
    rw [← hM]
    exact le_prod_of_mem l t (fun s hs => by have := h s hs; omega) ht
  have hB : ∀ m ∈ l, m.size ≤ M.size := fun m hm => Nat.size_le_size (hle m hm)
  have h1 := Work.Params.vsz_intList_le l M.size hB
  have hlen : l.length ≤ M.size := by
    have h2 : 2 ^ l.length ≤ M := by rw [← hM]; exact pow_length_le_prod l h
    have h3 : l.length ≤ Nat.log 2 M := by
      have := Nat.log_mono_right (b := 2) h2
      rwa [Nat.log_pow (by norm_num)] at this
    have h4 : Nat.log 2 M ≤ M.size := by
      have := Nat.log_mono_right (b := 2) (le_of_lt (Nat.lt_size_self M))
      rwa [Nat.log_pow (by norm_num)] at this
    omega
  have hsq := size_sq_le M
  nlinarith [h1, hlen, hsq]

end AxPure

namespace AxFold

open Work.SynFFT.MrgKit
open AxPure

local infixl:68 " ;;; " => HvdH.Cmd.seq
def drv (ts : List ℕ) : List Val := (ts.map (fun t : ℕ => Val.int t)).reverse

lemma sum_reverse (l : List ℕ) : l.reverse.sum = l.sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.reverse_cons, List.sum_append, List.sum_cons, List.sum_nil, ih]
    omega

lemma vsz_ofList_reverse (l : List Val) : vsz (ofList l.reverse) = vsz (ofList l) := by
  rw [vsz_ofList, vsz_ofList, List.length_reverse, List.map_reverse, sum_reverse]

def iList (ts : List ℕ) : Val := ofList (ts.map (fun t : ℕ => Val.int t))

lemma intList_eq_iList (ts : List ℕ) : intList ts = iList ts := by
  induction ts with
  | nil => rfl
  | cons a t ih =>
    rw [show intList (a :: t) = Val.cons (Val.int a) (intList t) from rfl, ih,
      show iList (a :: t) = Val.cons (Val.int a) (iList t) from rfl]

lemma vsz_ofList_drv (ts : List ℕ) : vsz (ofList (drv ts)) = vsz (iList ts) := by
  rw [drv, vsz_ofList_reverse]
  rfl

/-- The cost of a `roll j` when all entries of the window are `V`-small. -/
lemma rollCost_le {Krl j V : ℕ} {A : List Val} (hV : 1 ≤ V)
    (h : ∀ i < j + 1, vsz (A.getD i .nil) ≤ V) :
    Krl * (j + 1) * (((A.take (j + 1)).map vsz).sum + 1) ≤ 2 * Krl * (j + 1) * (j + 1) * V := by
  have h1 : ((A.take (j + 1)).map vsz).sum ≤ (j + 1) * V := vsz_take_sum_le_getD A (j+1) V h
  have h2 : ((A.take (j + 1)).map vsz).sum + 1 ≤ (j + 2) * V := by
    have h2a : (j + 1) * V + V = (j + 2) * V := by ring_nf
    have h2b := Nat.add_le_add h1 hV
    omega
  have h3 : (j + 2) ≤ 2 * (j + 1) := by omega
  have ha : Krl * (j + 1) * (((A.take (j + 1)).map vsz).sum + 1) ≤
      Krl * (j + 1) * ((j + 2) * V) := Nat.mul_le_mul_left (Krl * (j+1)) h2
  have hb : Krl * (j + 1) * ((j + 2) * V) ≤ Krl * (j + 1) * (2 * (j + 1) * V) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_right V h3)
  have hc : Krl * (j + 1) * (2 * (j + 1) * V) = 2 * Krl * (j + 1) * (j + 1) * V := by ring_nf
  linarith [ha, hb, hc]

/-- `roll k` with the uniform budget `KB * V`. -/
lemma rollU {main : Cmd} {rollP : ℕ → Cmd} {Krl KB V k : ℕ} {A : List Val}
    (hroll : ∀ k, WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Krl * (k+1) * (((vs.take (k+1)).map vsz).sum + 1)))
    (hKB : 2 * Krl * (k+1) * (k+1) ≤ KB) (hV : 1 ≤ V) (hkA : k < A.length)
    (hA : ∀ i < k+1, vsz (A.getD i .nil) ≤ V) :
    WordR main (rollP k) (fun vs => vs = A) (fun _ out => out = A.getD k .nil :: A.eraseIdx k)
      (fun _ => KB * V) := by
  refine rollStep hroll k A hkA (KB * V) ?_
  have h1 := rollCost_le (Krl := Krl) (j := k) (A := A) hV hA
  have h2 : 2 * Krl * (k+1) * (k+1) * V ≤ KB * V := Nat.mul_le_mul_right V hKB
  exact le_trans h1 h2

/-- `dup` with the uniform budget `KB * V`. -/
lemma dupU {main : Cmd} {dupP : Cmd} {Kd KB V : ℕ} {v : Val} {t : List Val}
    (hdup : WordR main dupP (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => Kd * (vsz (vs.headD .nil) + 1)))
    (hKB : 2 * Kd ≤ KB) (hV : 1 ≤ V) (hv : vsz v ≤ V) :
    WordR main dupP (fun vs => vs = v :: t) (fun _ out => out = v :: v :: t) (fun _ => KB * V) := by
  refine dupStep hdup v t (KB * V) ?_
  nlinarith [hKB, hv, hV]

/-- `swap` with the uniform budget `KB * V`. -/
lemma swapU {main : Cmd} {swapP : Cmd} {Ksw KB V : ℕ} {A : List Val}
    (hswap : WordR main swapP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Ksw * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (hKB : 3 * Ksw ≤ KB) (hV : 1 ≤ V) (hA : 2 ≤ A.length)
    (h0 : vsz (A.getD 0 .nil) ≤ V) (h1 : vsz (A.getD 1 .nil) ≤ V) :
    WordR main swapP (fun vs => vs = A) (fun _ out => out = A.getD 1 .nil :: A.getD 0 .nil :: A.drop 2)
      (fun _ => KB * V) := by
  refine swapStep hswap A hA (KB * V) ?_
  nlinarith [hKB, h0, h1, hV]

/-- `drop` with the uniform budget `KB * V`. -/
lemma drU {main : Cmd} {kdrP : Cmd} {Kdr KB V : ℕ} {A : List Val}
    (hkdr : WordR main kdrP (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => Kdr * (vsz (vs.headD .nil) + 1)))
    (hKB : 2 * Kdr ≤ KB) (hV : 1 ≤ V) (hA : 1 ≤ A.length) (h0 : vsz (A.headD .nil) ≤ V) :
    WordR main kdrP (fun vs => vs = A) (fun _ out => out = A.drop 1) (fun _ => KB * V) := by
  refine kdropStep hkdr A hA (KB * V) ?_
  nlinarith [hKB, h0, hV]

/-- `push` with the uniform budget `KB * V`. -/
lemma pushU {main : Cmd} {pushP : Val → Cmd} {Kpv KB V : ℕ} {v : Val} {A : List Val}
    (hpush : ∀ v, WordR main (pushP v) (fun _ => True) (fun vs out => out = v :: vs)
      (fun _ => Kpv * (vsz v + 1)))
    (hKB : 2 * Kpv ≤ KB) (hV : 1 ≤ V) (hv : vsz v ≤ V) :
    WordR main (pushP v) (fun vs => vs = A) (fun _ out => out = v :: A) (fun _ => KB * V) := by
  refine pushStep hpush v A (KB * V) ?_
  nlinarith [hKB, hv, hV]

lemma lenU {main : Cmd} {lenP : Cmd} {Kl KB V : ℕ} {xs : List Val} {t : List Val}
    (hlen : ∀ (xs : List Val), WordR main lenP (fun vs => ∃ rest, vs = ofList xs :: rest)
      (fun vs out => ∃ rest, vs = ofList xs :: rest ∧
        out = .int (xs.length : ℤ) :: ofList xs :: rest)
      (fun _ => Kl * (vsz (ofList xs) + 1)))
    (hKB : 2 * Kl ≤ KB) (hV : 1 ≤ V) (hv : vsz (ofList xs) ≤ V) :
    WordR main lenP (fun vs => vs = ofList xs :: t)
      (fun _ out => out = .int (xs.length : ℤ) :: ofList xs :: t) (fun _ => KB * V) := by
  refine AxKit.lengthStep hlen xs t (KB * V) ?_
  nlinarith [hKB, hv, hV]

lemma revU {main : Cmd} {revP : Cmd} {Krev KB V : ℕ} {xs : List Val} {t : List Val}
    (hrev : ∀ (xs : List Val), WordR main revP (fun vs => ∃ rest, vs = ofList xs :: rest)
      (fun vs out => ∃ rest, vs = ofList xs :: rest ∧ out = ofList xs.reverse :: rest)
      (fun _ => Krev * (vsz (ofList xs) + 1)))
    (hKB : 2 * Krev ≤ KB) (hV : 1 ≤ V) (hv : vsz (ofList xs) ≤ V) :
    WordR main revP (fun vs => vs = ofList xs :: t) (fun _ out => out = ofList xs.reverse :: t)
      (fun _ => KB * V) := by
  refine AxKit.reverseStep hrev xs t (KB * V) ?_
  nlinarith [hKB, hv, hV]

/-- The loop invariant: the array approximates the partially transformed state, the two products
`X = ∏ (ts.take (n-i))` and `Y = ∏ (ts.drop (n-i))` are on the stack, and a copy `tL` of
`intList ts` is kept below the parameters. -/
def AxInv (p r : ℕ) (ts : List ℕ) (sgn : ℤ) (u0 : Arr r) (e : ℝ) (tL : Val) (rest : List Val)
    (i : ℕ) (acc : List Val) : Prop :=
  ∃ (ws : List (List (ℤ × ℤ))) (X Y : ℕ),
    acc = ofList (cvecs ws) :: .int (X : ℤ) :: .int (Y : ℤ) :: .int sgn :: .int (r : ℤ) ::
      .int (p : ℤ) :: tL :: rest ∧
    ws.length = ts.prod ∧ (∀ w ∈ ws, InDiscVec p r w) ∧
    ApproxSL p r ts.prod ws (axisIterN r sgn (ts.drop (ts.length - i)) u0)
      (e + ((ts.drop (ts.length - i)).map (fun t => (Nat.log 2 t : ℝ))).sum) ∧
    X = (ts.take (ts.length - i)).prod ∧ Y = (ts.drop (ts.length - i)).prod

/-! ### The prelude: build the driver list, the total product `M` and the initial products -/

def preludeProg (dupP lenP revP kdrP swapP : Cmd) (pushP : Val → Cmd) (rollP : ℕ → Cmd) : Cmd :=
  rollP 1 ;;; dupP ;;; revP ;;; rollP 1 ;;; rollP 5 ;;; rollP 5 ;;; rollP 5 ;;; rollP 5 ;;; rollP 5 ;;;
  rollP 1 ;;; dupP ;;; lenP ;;; swapP ;;; kdrP ;;; pushP (.int 1) ;;; swapP ;;; rollP 2 ;;; rollP 3

theorem preludeWord (hk : Work.SynFFT.KLib) (hl : HvdH.LayoutLib) :
    ∃ (prog : Cmd) (KC : ℕ), ∀ (main : Cmd) (ws : List (List (ℤ × ℤ))) (ts : List ℕ) (sgn : ℤ)
      (p r : ℕ) (rest : List Val) (V : ℕ),
    ws.length = ts.prod → 1 ≤ V →
    vsz (ofList (cvecs ws)) ≤ V → vsz (iList ts) ≤ V → vsz (ofList (drv ts)) ≤ V →
    isz sgn ≤ V → isz (r : ℤ) ≤ V → isz (p : ℤ) ≤ V → isz ((ts.prod : ℕ) : ℤ) ≤ V →
    isz (1 : ℤ) ≤ V →
    WordR main prog
      (fun vs => vs = ofList (cvecs ws) :: iList ts :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = ofList (drv ts) :: ofList (cvecs ws) :: .int ((ts.prod : ℕ) : ℤ) ::
        .int (1 : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: iList ts :: rest)
      (fun _ => KC * V) := by
  obtain ⟨dupP, Kd, hdup⟩ := hk.dup
  obtain ⟨lenP, Kl, hlen⟩ := hl.length
  obtain ⟨revP, Krev, hrev⟩ := hl.reverse
  obtain ⟨kdrP, Kdr, hkdr⟩ := hk.drop
  obtain ⟨swapP, Ksw, hswap⟩ := hk.swap
  obtain ⟨pushP, Kpv, hpush⟩ := hk.pushVal
  obtain ⟨rollP, Krl, hroll⟩ := hk.roll
  refine ⟨preludeProg dupP lenP revP kdrP swapP pushP rollP,
    18 * (1000 * Kd + 1000 * Kl + 1000 * Krev + 1000 * Kdr + 1000 * Ksw + 1000 * Kpv +
      1000 * Krl + 1000), ?_⟩
  intro main ws ts sgn p r rest V hwl hV1 hWv hTv hDv hSv hRv hPv hMv h1v
  simp only [iList] at hTv
  set W : Val := ofList (cvecs ws) with hWdef
  set T : Val := ofList (ts.map (fun t : ℕ => Val.int t)) with hTdef
  set S : Val := .int sgn with hSdef
  set Rv : Val := .int (r : ℤ) with hRdef
  set Pv : Val := .int (p : ℤ) with hPdef
  set Mv : Val := .int ((ts.prod : ℕ) : ℤ) with hMdef
  set Dv : Val := ofList (drv ts) with hDdef
  set KB : ℕ := 1000 * Kd + 1000 * Kl + 1000 * Krev + 1000 * Kdr + 1000 * Ksw + 1000 * Kpv +
    1000 * Krl + 1000 with hKBdef
  have hWV : vsz W ≤ V := by rw [hWdef]; exact hWv
  have hTV : vsz T ≤ V := by rw [hTdef]; exact hTv
  have hDV : vsz Dv ≤ V := by rw [hDdef]; exact hDv
  have hSV : vsz S ≤ V := by rw [hSdef, vsz_int']; exact hSv
  have hRV : vsz Rv ≤ V := by rw [hRdef, vsz_int']; exact hRv
  have hPV : vsz Pv ≤ V := by rw [hPdef, vsz_int']; exact hPv
  have hMV : vsz Mv ≤ V := by rw [hMdef, vsz_int']; exact hMv
  have h1V : vsz (.int (1 : ℤ)) ≤ V := h1v
  have e1 : WordR main (rollP 1) (fun vs => vs = W :: T :: S :: Rv :: Pv :: rest)
      (fun _ out => out = T :: W :: S :: Rv :: Pv :: rest) (fun _ => KB * V) :=
    rollU (hroll main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
      (by intro i hi; interval_cases i <;>
          simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
  have e2 : WordR main dupP (fun vs => vs = T :: W :: S :: Rv :: Pv :: rest)
      (fun _ out => out = T :: T :: W :: S :: Rv :: Pv :: rest) (fun _ => KB * V) :=
    dupU (hdup main) (by rw [hKBdef]; omega) hV1 hTV
  have e3 : WordR main revP (fun vs => vs = T :: T :: W :: S :: Rv :: Pv :: rest)
      (fun _ out => out = Dv :: T :: W :: S :: Rv :: Pv :: rest) (fun _ => KB * V) := by
    have h := revU (hrev main) (Krev := Krev) (KB := KB) (V := V)
      (xs := ts.map (fun t : ℕ => Val.int t)) (t := T :: W :: S :: Rv :: Pv :: rest)
      (by rw [hKBdef]; omega) hV1 (by rw [hTdef] at hTV; exact hTV)
    refine WordR_weaken h (fun vs hvs => hvs) ?_ (fun _ _ => le_rfl)
    intro vs out hvs hout
    rw [hout]
    rfl
  have e4 : WordR main (rollP 1) (fun vs => vs = Dv :: T :: W :: S :: Rv :: Pv :: rest)
      (fun _ out => out = T :: Dv :: W :: S :: Rv :: Pv :: rest) (fun _ => KB * V) :=
    rollU (hroll main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
      (by intro i hi; interval_cases i <;>
          simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
  have e5 : WordR main (rollP 5) (fun vs => vs = T :: Dv :: W :: S :: Rv :: Pv :: rest)
      (fun _ out => out = Pv :: T :: Dv :: W :: S :: Rv :: rest) (fun _ => KB * V) :=
    rollU (hroll main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
      (by intro i hi; interval_cases i <;>
          simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
  have e6 : WordR main (rollP 5) (fun vs => vs = Pv :: T :: Dv :: W :: S :: Rv :: rest)
      (fun _ out => out = Rv :: Pv :: T :: Dv :: W :: S :: rest) (fun _ => KB * V) :=
    rollU (hroll main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
      (by intro i hi; interval_cases i <;>
          simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
  have e7 : WordR main (rollP 5) (fun vs => vs = Rv :: Pv :: T :: Dv :: W :: S :: rest)
      (fun _ out => out = S :: Rv :: Pv :: T :: Dv :: W :: rest) (fun _ => KB * V) :=
    rollU (hroll main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
      (by intro i hi; interval_cases i <;>
          simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
  have e8 : WordR main (rollP 5) (fun vs => vs = S :: Rv :: Pv :: T :: Dv :: W :: rest)
      (fun _ out => out = W :: S :: Rv :: Pv :: T :: Dv :: rest) (fun _ => KB * V) :=
    rollU (hroll main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
      (by intro i hi; interval_cases i <;>
          simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
  have e9 : WordR main (rollP 5) (fun vs => vs = W :: S :: Rv :: Pv :: T :: Dv :: rest)
      (fun _ out => out = Dv :: W :: S :: Rv :: Pv :: T :: rest) (fun _ => KB * V) :=
    rollU (hroll main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
      (by intro i hi; interval_cases i <;>
          simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
  have e10 : WordR main (rollP 1) (fun vs => vs = Dv :: W :: S :: Rv :: Pv :: T :: rest)
      (fun _ out => out = W :: Dv :: S :: Rv :: Pv :: T :: rest) (fun _ => KB * V) :=
    rollU (hroll main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
      (by intro i hi; interval_cases i <;>
          simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
  have e11 : WordR main dupP (fun vs => vs = W :: Dv :: S :: Rv :: Pv :: T :: rest)
      (fun _ out => out = W :: W :: Dv :: S :: Rv :: Pv :: T :: rest) (fun _ => KB * V) :=
    dupU (hdup main) (by rw [hKBdef]; omega) hV1 hWV
  have e12 : WordR main lenP (fun vs => vs = W :: W :: Dv :: S :: Rv :: Pv :: T :: rest)
      (fun _ out => out = Mv :: W :: W :: Dv :: S :: Rv :: Pv :: T :: rest) (fun _ => KB * V) := by
    have hD : Kl * (vsz (ofList (cvecs ws)) + 1) ≤ KB * V := by
      rw [hKBdef]
      have hW' : vsz (ofList (cvecs ws)) ≤ V := by rw [← hWdef]; exact hWV
      nlinarith [hW', hV1]
    have h := AxKit.lengthStep (hlen main) (Kl := Kl) (xs := cvecs ws)
      (t := W :: Dv :: S :: Rv :: Pv :: T :: rest) (KB * V) hD
    refine WordR_weaken h (fun vs hvs => hvs) ?_ (fun _ _ => le_rfl)
    intro vs out hvs hout
    rw [hout, show (cvecs ws).length = ts.prod by rw [cvecs, List.length_map]; exact hwl, hMdef]
  have e13 : WordR main swapP (fun vs => vs = Mv :: W :: W :: Dv :: S :: Rv :: Pv :: T :: rest)
      (fun _ out => out = W :: Mv :: W :: Dv :: S :: Rv :: Pv :: T :: rest) (fun _ => KB * V) :=
    swapU (hswap main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
      (by simp only [List.getD_cons_zero]; exact hMV)
      (by simp only [List.getD_cons_zero, List.getD_cons_succ]; exact hWV)
  have e14 : WordR main kdrP (fun vs => vs = W :: Mv :: W :: Dv :: S :: Rv :: Pv :: T :: rest)
      (fun _ out => out = Mv :: W :: Dv :: S :: Rv :: Pv :: T :: rest) (fun _ => KB * V) :=
    drU (hkdr main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
      (by simp only [List.headD_cons]; exact hWV)
  have e15 : WordR main (pushP (.int (1 : ℤ)))
      (fun vs => vs = Mv :: W :: Dv :: S :: Rv :: Pv :: T :: rest)
      (fun _ out => out = .int (1 : ℤ) :: Mv :: W :: Dv :: S :: Rv :: Pv :: T :: rest)
      (fun _ => KB * V) :=
    pushU (hpush main) (by rw [hKBdef]; omega) hV1 h1V
  have e16 : WordR main swapP
      (fun vs => vs = .int (1 : ℤ) :: Mv :: W :: Dv :: S :: Rv :: Pv :: T :: rest)
      (fun _ out => out = Mv :: .int (1 : ℤ) :: W :: Dv :: S :: Rv :: Pv :: T :: rest)
      (fun _ => KB * V) :=
    swapU (hswap main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
      (by simp only [List.getD_cons_zero]; exact h1V)
      (by simp only [List.getD_cons_zero, List.getD_cons_succ]; exact hMV)
  have e17 : WordR main (rollP 2)
      (fun vs => vs = Mv :: .int (1 : ℤ) :: W :: Dv :: S :: Rv :: Pv :: T :: rest)
      (fun _ out => out = W :: Mv :: .int (1 : ℤ) :: Dv :: S :: Rv :: Pv :: T :: rest)
      (fun _ => KB * V) :=
    rollU (hroll main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
      (by intro i hi; interval_cases i <;>
          simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
  have e18 : WordR main (rollP 3)
      (fun vs => vs = W :: Mv :: .int (1 : ℤ) :: Dv :: S :: Rv :: Pv :: T :: rest)
      (fun _ out => out = Dv :: W :: Mv :: .int (1 : ℤ) :: S :: Rv :: Pv :: T :: rest)
      (fun _ => KB * V) :=
    rollU (hroll main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
      (by intro i hi; interval_cases i <;>
          simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
  have c2 := WordR_seqC e1 e2
  have c3 := WordR_seqC c2 e3
  have c4 := WordR_seqC c3 e4
  have c5 := WordR_seqC c4 e5
  have c6 := WordR_seqC c5 e6
  have c7 := WordR_seqC c6 e7
  have c8 := WordR_seqC c7 e8
  have c9 := WordR_seqC c8 e9
  have c10 := WordR_seqC c9 e10
  have c11 := WordR_seqC c10 e11
  have c12 := WordR_seqC c11 e12
  have c13 := WordR_seqC c12 e13
  have c14 := WordR_seqC c13 e14
  have c15 := WordR_seqC c14 e15
  have c16 := WordR_seqC c15 e16
  have c17 := WordR_seqC c16 e17
  have c18 := WordR_seqC c17 e18
  refine WordR_weaken c18 (fun vs h => h) (fun vs out h h' => h') (fun vs => ?_)
  rw [Nat.mul_assoc]
  omega

lemma getD_default_eq {α : Type} (l : List α) (d₁ d₂ : α) {n : ℕ} (h : n < l.length) :
    l.getD n d₁ = l.getD n d₂ := by
  rw [List.getD_eq_getElem l d₁ h, List.getD_eq_getElem l d₂ h]

lemma drv_getD (ts : List ℕ) (i : ℕ) (h : i < ts.length) :
    (drv ts).getD i .nil = .int ((ts.getD (ts.length - 1 - i) 0 : ℕ) : ℤ) := by
  have h2 : i < (ts.map (fun t : ℕ => Val.int t)).length := by simpa [List.length_map] using h
  have h4 : (ts.map (fun t : ℕ => Val.int t)).length - 1 - i <
      (ts.map (fun t : ℕ => Val.int t)).length := by rw [List.length_map]; omega
  rw [drv, List.getD_reverse i h2,
    getD_default_eq _ .nil ((fun t : ℕ => Val.int t) 0) h4,
    List.getD_map ts (0 : ℕ) (fun t : ℕ => Val.int t), List.length_map]

lemma clogU {main : Cmd} {clP : Cmd} {Kc KB V : ℕ} {a : ℤ} {t : List Val}
    (hcl : UnOp main clP (fun a => 0 ≤ a) (fun a => (Nat.clog 2 a.toNat : ℤ)) (fun a => Kc * isz a))
    (hKB : Kc ≤ KB) (ha : 0 ≤ a) (hv : isz a ≤ V) (hV : 1 ≤ V) :
    WordR main clP (fun vs => vs = .int a :: t)
      (fun _ out => out = .int ((Nat.clog 2 a.toNat : ℕ) : ℤ) :: t) (fun _ => KB * V) := by
  refine Work.SynFFT.Fft1Kit.clog2Step hcl a t ha (KB * V) ?_
  calc Kc * isz a ≤ Kc * V := Nat.mul_le_mul_left Kc hv
    _ ≤ KB * V := Nat.mul_le_mul_right V hKB

lemma mulU {main : Cmd} {mulP : Cmd} {Km KB V : ℕ} {a b : ℤ} {t : List Val}
    (hmul : BinOp main mulP (fun _ _ => True) (· * ·) (fun a b => Km * isz a * isz b))
    (hKB : 1 ≤ KB) (h : Km * isz a * isz b ≤ V) :
    WordR main mulP (fun vs => vs = .int a :: .int b :: t) (fun _ out => out = .int (a * b) :: t)
      (fun _ => KB * V) := by
  refine mulStep hmul a b t (KB * V) ?_
  calc Km * isz a * isz b ≤ V := h
    _ ≤ KB * V := by simpa using Nat.mul_le_mul_right V hKB

lemma tdivU {main : Cmd} {tdP : Cmd} {Kt KB V : ℕ} {a b : ℤ} {t : List Val}
    (htd : BinOp main tdP (fun _ b => b ≠ 0) Int.tdiv (fun a b => Kt * isz a * isz b))
    (hKB : 1 ≤ KB) (hb : b ≠ 0) (h : Kt * isz a * isz b ≤ V) :
    WordR main tdP (fun vs => vs = .int a :: .int b :: t) (fun _ out => out = .int (a.tdiv b) :: t)
      (fun _ => KB * V) := by
  refine AxKit.tdivStep htd a b t hb (KB * V) ?_
  calc Kt * isz a * isz b ≤ V := h
    _ ≤ KB * V := by simpa using Nat.mul_le_mul_right V hKB

def stepProg (dupP clogP tdivP mulP kdrP swapP axisP : Cmd) (rollP : ℕ → Cmd) : Cmd :=
  (dupP ;;; dupP ;;; clogP ;;; rollP 5 ;;; rollP 5 ;;; rollP 3 ;;; swapP ;;; tdivP ;;; rollP 4 ;;;
    rollP 4 ;;; rollP 2 ;;; rollP 2 ;;; axisP) ;;;
  (rollP 3 ;;; rollP 3 ;;; swapP ;;; mulP ;;; rollP 3 ;;; kdrP ;;; rollP 2 ;;; rollP 2)

def AxSpec (axisP : Cmd) (Ka : ℕ) : Prop :=
  ∀ (main : Cmd) (p r A t B k : ℕ) (sgn : ℤ) (ws : List (List (ℤ × ℤ))) (u : Arr r)
    (e : ℝ) (rest : List Val),
    HvdH.IsPow2 r → t = 2 ^ k → t ∣ 2 * r → 2 * r < 2 ^ p → (sgn = 1 ∨ sgn = -1) →
    0 < A → 0 < B → ws.length = A * t * B → (∀ w ∈ ws, InDiscVec p r w) →
    ApproxSL p r (A * t * B) ws u e →
    WordR main axisP
      (fun vs => vs = ofList (cvecs ws) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) ::
        .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => ∃ ws' : List (List (ℤ × ℤ)),
        out = ofList (cvecs ws') :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) ::
          .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest ∧
        ws'.length = A * t * B ∧ (∀ w ∈ ws', InDiscVec p r w) ∧
        ApproxSL p r (A * t * B) ws' (axisT r t B sgn u) (e + k))
      (fun _ => Ka * (A * t * B) * (r + 1) * (p + 1) * (k + 1) +
        Ka * (A * t * B) * (r + 1) * (p + 1) * ((A * t * B).size + 2) + Ka)

theorem axSpec_of (ha : Work.SynFFT.HasAxis) : ∃ (axisP : Cmd) (Ka : ℕ), AxSpec axisP Ka := by
  obtain ⟨P, K, h⟩ := ha
  exact ⟨P, K, fun main p r A t B k sgn ws u e rest h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    h main p r A t B k sgn ws u e rest h1 h2 h3 h4 h5 h6 h7 h8 h9 h10⟩


/-- The axis word's `WordR` triple with its existential output, composed with a following
parameterised program: the standard `seq` law for a `∃`-post. -/
theorem WordR_seqQ {main p q : Cmd} {A : List Val} {Q : List Val → Prop}
    {R : List Val → Prop} {c1 c2 : ℕ}
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => Q out) (fun _ => c1))
    (h2 : ∀ B, Q B → WordR main q (fun vs => vs = B) (fun _ out => R out) (fun _ => c2)) :
    WordR main (p ;;; q) (fun vs => vs = A) (fun _ out => R out) (fun _ => c1 + c2) := by
  intro vs hvs st Rg hR
  rw [hvs] at hR
  obtain ⟨mid, st2, n1, hQ, he1, hn1, hstk, hoth⟩ := h1 A rfl st Rg hR
  obtain ⟨out, st3, n2, hR', he2, hn2, hstk2, hoth2⟩ := h2 mid hQ mid rfl st2 Rg hstk
  exact ⟨out, st3, n1 + n2, hR', Eval.seq he1 he2, Nat.add_le_add hn1 hn2, hstk2,
    fun k hk => by rw [hoth2 k hk, hoth k hk]⟩

/-- The axis loop step: read the current axis, update the two products, run the axis word. -/
theorem stepWord
    (dupP clP tdP mulP kdrP swapP axisP : Cmd) (rollP : ℕ → Cmd)
    {Kd Kc Kt Km Kdr Ksw Krl Ka : ℕ}
    (hdup : ∀ main : Cmd, WordR main dupP (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => Kd * (vsz (vs.headD .nil) + 1)))
    (hcl : ∀ main : Cmd, UnOp main clP (fun a => 0 ≤ a)
      (fun a => (Nat.clog 2 a.toNat : ℤ)) (fun a => Kc * isz a))
    (htd : ∀ main : Cmd, BinOp main tdP (fun _ b => b ≠ 0) Int.tdiv
      (fun a b => Kt * isz a * isz b))
    (hmul : ∀ main : Cmd, BinOp main mulP (fun _ _ => True) (· * ·)
      (fun a b => Km * isz a * isz b))
    (hkdr : ∀ main : Cmd, WordR main kdrP (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => Kdr * (vsz (vs.headD .nil) + 1)))
    (hswap : ∀ main : Cmd, WordR main swapP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Ksw * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (hroll : ∀ main : Cmd, ∀ k, WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Krl * (k+1) * (((vs.take (k+1)).map vsz).sum + 1)))
    (hax : AxSpec axisP Ka) :
    ∃ (prog : Cmd) (KC : ℕ), ∀ (main : Cmd) (p r : ℕ) (ts : List ℕ) (sgn : ℤ) (u0 : Arr r)
      (e : ℝ) (tL : Val) (rest : List Val) (V : ℕ) (i : ℕ) (acc : List Val),
    HvdH.IsPow2 r → (∀ t ∈ ts, HvdH.IsPow2 t) → (∀ t ∈ ts, t ∣ 2 * r) →
    (∀ t ∈ ts, 2 ≤ t) → 2 * r < 2 ^ p → (sgn = 1 ∨ sgn = -1) →
    14 * (ts.prod * (r + 1) * (p + 1)) ≤ V → ts.prod.size + 2 ≤ V → p + 2 ≤ V →
    r.size + 2 ≤ V → 3 ≤ V → 1 ≤ ts.prod →
    Km * ((ts.prod.size + 2) * (ts.prod.size + 2)) ≤ V →
    Kt * ((ts.prod.size + 2) * (ts.prod.size + 2)) ≤ V →
    Ka * (ts.prod * (r + 1) * (p + 1) * (ts.prod.size + 2)) * 2 + Ka ≤ V →
    i < ts.length →
    AxInv p r ts sgn u0 e tL rest i acc →
    WordR main prog (fun vs => vs = (drv ts).getD i .nil :: acc)
      (fun _ out => AxInv p r ts sgn u0 e tL rest (i + 1) out) (fun _ => KC * V) := by
  refine ⟨stepProg dupP clP tdP mulP kdrP swapP axisP rollP,
    25 * (1000 * Kd + 1000 * Kc + 1000 * Kt + 1000 * Km + 1000 * Kdr + 1000 * Ksw +
      1000 * Krl + 1000 * Ka + 1000), ?_⟩
  intro main p r ts sgn u0 e tL rest V i acc hrp hpow hdiv h2t hr2 hsg hV1 hV2 hV3 hV4 hV5
    hM1 hKm hKt hKa hi hInv
  obtain ⟨ws, X, Y, hacc, hwl, hdisc, happ, hX, hY⟩ := hInv
  set W : Val := ofList (cvecs ws) with hWdef
  set iu : Val := .int (ts.getD (ts.length - 1 - i) 0) with hiudef
  set iX : Val := .int (X : ℤ) with hiXdef
  set iY : Val := .int (Y : ℤ) with hiYdef
  set iS : Val := .int sgn with hiSdef
  set iR : Val := .int (r : ℤ) with hiRdef
  set iP : Val := .int (p : ℤ) with hiPdef
  set KB : ℕ := 1000 * Kd + 1000 * Kc + 1000 * Kt + 1000 * Km + 1000 * Kdr + 1000 * Ksw +
    1000 * Krl + 1000 * Ka + 1000 with hKBdef
  have hKB1 : 1 ≤ KB := by rw [hKBdef]; omega
  -- facts about the current axis
  have hr2' : 2 ≤ r := AxPure.two_le_of_isPow2 r hrp
  have hp1 : 1 ≤ p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h; simp at hr2; omega
    · exact h
  have hu_mem : ts.getD (ts.length - 1 - i) 0 ∈ ts := AxPure.getD_mem' ts i hi
  have hu_pow : HvdH.IsPow2 (ts.getD (ts.length - 1 - i) 0) := hpow _ hu_mem
  have hu2 : 2 ≤ ts.getD (ts.length - 1 - i) 0 := h2t _ hu_mem
  have hu_div : ts.getD (ts.length - 1 - i) 0 ∣ 2 * r := hdiv _ hu_mem
  have hu_pos : 0 < ts.getD (ts.length - 1 - i) 0 := by omega
  have hu_le : ts.getD (ts.length - 1 - i) 0 ≤ ts.prod :=
    AxPure.le_prod_of_mem ts _ (fun s hs => by have := h2t s hs; omega) hu_mem
  have hu_pow2 : ts.getD (ts.length - 1 - i) 0 =
      2 ^ Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) := AxPure.pow_clog_of_isPow2 _ hu_pow
  have hk_le : Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) ≤ ts.prod.size :=
    AxPure.clog_le_size _ _ hu_pow hu_le
  -- facts about the two products
  have hXY : X * Y = ts.prod := by
    rw [hX, hY]
    exact AxPure.prod_take_mul_drop ts (ts.length - i) (by omega)
  have h1X : 1 ≤ X := by
    rw [hX]
    exact AxPure.one_le_prod_of _ (fun t ht => by
      have := h2t t (List.mem_of_mem_take ht); omega)
  have h1Y : 1 ≤ Y := by
    rw [hY]
    exact AxPure.one_le_prod_of _ (fun t ht => by
      have := h2t t (List.mem_of_mem_drop ht); omega)
  have hA1 : 1 ≤ (ts.take (ts.length - i - 1)).prod :=
    AxPure.one_le_prod_of _ (fun t ht => by
      have := h2t t (List.mem_of_mem_take ht); omega)
  have hXle : X ≤ ts.prod := by nlinarith [hXY, h1Y]
  have hYle : Y ≤ ts.prod := by nlinarith [hXY, h1X]
  have hXsplit : X = (ts.take (ts.length - i - 1)).prod * ts.getD (ts.length - 1 - i) 0 := by
    have h1 : (ts.take (ts.length - i)).prod =
        (ts.take (ts.length - i - 1)).prod * ts.getD (ts.length - 1 - i) 0 := by
      have h2 : ts.length - i = ts.length - i - 1 + 1 := by omega
      have h6 : ts.length - 1 - i < ts.length := by omega
      have h3 : ts.getD (ts.length - i - 1) 1 = ts.getD (ts.length - 1 - i) 0 := by
        have h7 : ts.length - i - 1 = ts.length - 1 - i := by omega
        rw [h7, List.getD_eq_getElem ts 1 h6, List.getD_eq_getElem ts 0 h6]
      conv_lhs => rw [h2]
      rw [AxPure.prod_take_succ ts (ts.length - i - 1) (by omega), h3]
    rw [hX, h1]
  have hXdiv : X / ts.getD (ts.length - 1 - i) 0 = (ts.take (ts.length - i - 1)).prod := by
    rw [hXsplit]
    exact Nat.mul_div_left _ hu_pos
  have hdrop : ts.drop (ts.length - i - 1) =
      ts.getD (ts.length - 1 - i) 0 :: ts.drop (ts.length - i) := AxPure.drop_len_sub ts i hi
  have hYcons : (ts.drop (ts.length - i - 1)).prod = ts.getD (ts.length - 1 - i) 0 * Y := by
    rw [AxPure.drop_len_sub ts i hi, List.prod_cons, hY]
  -- value bounds
  have hWV : vsz W ≤ V := by
    rw [hWdef]
    refine le_trans (AxPure.vsz_ofList_cvecs_le p r (ts.prod) ws hp1 hM1 hwl hdisc) hV1
  have huV : vsz iu ≤ V := by
    rw [hiudef, MrgKit.vsz_int']
    exact le_trans (AxPure.isz_le_size _ _ hu_le) hV2
  have hXV : vsz iX ≤ V := by
    rw [hiXdef, MrgKit.vsz_int']
    exact le_trans (AxPure.isz_le_size _ _ hXle) hV2
  have hYV : vsz iY ≤ V := by
    rw [hiYdef, MrgKit.vsz_int']
    exact le_trans (AxPure.isz_le_size _ _ hYle) hV2
  have hS3 : isz ((1 : ℤ)) ≤ 3 := by simp [isz]
  have hS3' : isz ((-1 : ℤ)) ≤ 3 := by simp [isz]
  have hSV : vsz iS ≤ V := by
    rw [hiSdef, MrgKit.vsz_int']
    rcases hsg with h | h <;> rw [h] <;> omega
  have hRV : vsz iR ≤ V := by
    rw [hiRdef, MrgKit.vsz_int']
    have := AxPure.isz_le_size r r (le_refl r)
    omega
  have hPV : vsz iP ≤ V := by
    rw [hiPdef, MrgKit.vsz_int']
    have h1 := AxPure.isz_le_size p p (le_refl p)
    have h2 := AxPure.size_le_self p
    omega
  have hkV : vsz (.int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ)) ≤ V := by
    have h1 : Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) ≤ ts.prod := by
      have := AxPure.size_le_self ts.prod
      omega
    have h2 : isz (((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ)) ≤ ts.prod.size + 2 :=
      AxPure.isz_le_size _ _ h1
    rw [show vsz (.int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ)) =
      isz (((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ)) from MrgKit.vsz_int' _]
    omega
  have hXcV : vsz (.int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ)) ≤ V := by
    have hcon : ((X : ℤ).tdiv ((ts.getD (ts.length - 1 - i) 0 : ℕ) : ℤ)) =
        (((X / ts.getD (ts.length - 1 - i) 0 : ℕ)) : ℤ) :=
      (Int.ofNat_tdiv X (ts.getD (ts.length - 1 - i) 0)).symm
    have h2 : isz (((X / ts.getD (ts.length - 1 - i) 0 : ℕ)) : ℤ) ≤ ts.prod.size + 2 :=
      AxPure.isz_le_size _ _ (le_trans (Nat.div_le_self _ _) hXle)
    rw [show vsz (.int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ)) =
      isz ((X : ℤ).tdiv ((ts.getD (ts.length - 1 - i) 0 : ℕ) : ℤ)) from MrgKit.vsz_int' _, hcon]
    omega
  have hYmV : vsz (.int ((Y : ℤ) * ((ts.getD (ts.length - 1 - i) 0 : ℕ) : ℤ))) ≤ V := by
    have hcon : ((Y : ℤ) * ((ts.getD (ts.length - 1 - i) 0 : ℕ) : ℤ)) =
        (((Y * ts.getD (ts.length - 1 - i) 0 : ℕ)) : ℤ) :=
      (Int.natCast_mul Y (ts.getD (ts.length - 1 - i) 0)).symm
    have hu_le_X : ts.getD (ts.length - 1 - i) 0 ≤ X := by
      rw [hXsplit]; nlinarith [hA1]
    have h2 : isz (((Y * ts.getD (ts.length - 1 - i) 0 : ℕ)) : ℤ) ≤ ts.prod.size + 2 :=
      AxPure.isz_le_size _ _ (by nlinarith [hXY, hu_le_X])
    rw [show vsz (.int ((Y : ℤ) * ((ts.getD (ts.length - 1 - i) 0 : ℕ) : ℤ))) =
      isz ((Y : ℤ) * ((ts.getD (ts.length - 1 - i) 0 : ℕ) : ℤ)) from MrgKit.vsz_int' _, hcon]
    omega
  -- the operations, part 1
  have e1 : WordR main dupP (fun vs => vs = iu :: W :: iX :: iY :: iS :: iR :: iP :: tL :: rest)
      (fun _ out => out = iu :: iu :: W :: iX :: iY :: iS :: iR :: iP :: tL :: rest)
      (fun _ => KB * V) :=
    dupU (hdup main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) huV
  have e2 : WordR main dupP
      (fun vs => vs = iu :: iu :: W :: iX :: iY :: iS :: iR :: iP :: tL :: rest)
      (fun _ out => out = iu :: iu :: iu :: W :: iX :: iY :: iS :: iR :: iP :: tL :: rest)
      (fun _ => KB * V) :=
    dupU (hdup main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) huV
  have huV' : isz ((ts.getD (ts.length - 1 - i) 0 : ℕ) : ℤ) ≤ V := by
    have h := huV
    rw [hiudef, MrgKit.vsz_int'] at h
    exact h
  have e3 : WordR main clP
      (fun vs => vs = iu :: iu :: iu :: W :: iX :: iY :: iS :: iR :: iP :: tL :: rest)
      (fun _ out => out = .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iu :: iu :: W :: iX :: iY :: iS :: iR :: iP :: tL :: rest)
      (fun _ => KB * V) :=
    clogU (hcl main) (by rw [hKBdef]; omega) (by simp) huV' (by omega : 1 ≤ V)
  have e4 : WordR main (rollP 5)
      (fun vs => vs = .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iu :: iu :: W :: iX :: iY :: iS :: iR :: iP :: tL :: rest)
      (fun _ out => out = iY :: .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iu :: iu :: W :: iX :: iS :: iR :: iP :: tL :: rest)
      (fun _ => KB * V) :=
    rollU (hroll main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
      (by intro j hj; interval_cases j <;>
          simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
  have e5 : WordR main (rollP 5)
      (fun vs => vs = iY :: .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iu :: iu :: W :: iX :: iS :: iR :: iP :: tL :: rest)
      (fun _ out => out = iX :: iY :: .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iu :: iu :: W :: iS :: iR :: iP :: tL :: rest)
      (fun _ => KB * V) :=
    rollU (hroll main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
      (by intro j hj; interval_cases j <;>
          simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
  have e6 : WordR main (rollP 3)
      (fun vs => vs = iX :: iY :: .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iu :: iu :: W :: iS :: iR :: iP :: tL :: rest)
      (fun _ out => out = iu :: iX :: iY ::
        .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iu :: W :: iS :: iR :: iP :: tL :: rest)
      (fun _ => KB * V) :=
    rollU (hroll main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
      (by intro j hj; interval_cases j <;>
          simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
  have e7 : WordR main swapP
      (fun vs => vs = iu :: iX :: iY ::
        .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iu :: W :: iS :: iR :: iP :: tL :: rest)
      (fun _ out => out = iX :: iu :: iY ::
        .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iu :: W :: iS :: iR :: iP :: tL :: rest)
      (fun _ => KB * V) :=
    swapU (hswap main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
      (by simp only [List.getD_cons_zero]; exact huV)
      (by simp only [List.getD_cons_zero, List.getD_cons_succ]; exact hXV)
  have e8 : WordR main tdP
      (fun vs => vs = iX :: iu :: iY ::
        .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iu :: W :: iS :: iR :: iP :: tL :: rest)
      (fun _ out => out = .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) :: iY ::
        .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iu :: W :: iS :: iR :: iP :: tL :: rest)
      (fun _ => KB * V) := by
    refine WordR_weaken (tdivU (htd main) hKB1 (by have h := hu_pos; omega) (by
      have h1 : isz (X : ℤ) ≤ ts.prod.size + 2 := AxPure.isz_le_size _ _ hXle
      have h2 : isz ((ts.getD (ts.length - 1 - i) 0 : ℕ) : ℤ) ≤ ts.prod.size + 2 :=
        AxPure.isz_le_size _ _ hu_le
      have h3 : Kt * isz (X : ℤ) * isz ((ts.getD (ts.length - 1 - i) 0 : ℕ) : ℤ) ≤
          Kt * (ts.prod.size + 2) * (ts.prod.size + 2) := by
        calc Kt * isz (X : ℤ) * isz ((ts.getD (ts.length - 1 - i) 0 : ℕ) : ℤ)
            ≤ Kt * (ts.prod.size + 2) * isz ((ts.getD (ts.length - 1 - i) 0 : ℕ) : ℤ) :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left Kt h1)
          _ ≤ Kt * (ts.prod.size + 2) * (ts.prod.size + 2) :=
              Nat.mul_le_mul_left _ h2
      have h4 : Kt * (ts.prod.size + 2) * (ts.prod.size + 2) ≤ V := by
        have h := hKt
        have he : Kt * (ts.prod.size + 2) * (ts.prod.size + 2) =
            Kt * ((ts.prod.size + 2) * (ts.prod.size + 2)) := by ring
        rw [he]; exact h
      exact le_trans h3 h4))
      (fun vs hvs => hvs) ?_ (fun _ _ => le_rfl)
    intro vs out hvs hout
    rw [hout]
    show .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) :: iY ::
        .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iu :: W :: iS :: iR :: iP :: tL :: rest =
      .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) :: iY ::
        .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iu :: W :: iS :: iR :: iP :: tL :: rest
    rw [Int.ofNat_tdiv]
  have e9 : WordR main (rollP 4)
      (fun vs => vs = .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) :: iY ::
        .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iu :: W :: iS :: iR :: iP :: tL :: rest)
      (fun _ out => out = W :: .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) :: iY ::
        .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iu :: iS :: iR :: iP :: tL :: rest)
      (fun _ => KB * V) :=
    rollU (hroll main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
      (by intro j hj; interval_cases j <;>
          simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
  have e10 : WordR main (rollP 4)
      (fun vs => vs = W :: .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) :: iY ::
        .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iu :: iS :: iR :: iP :: tL :: rest)
      (fun _ out => out = iu :: W :: .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) :: iY ::
        .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iS :: iR :: iP :: tL :: rest)
      (fun _ => KB * V) :=
    rollU (hroll main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
      (by intro j hj; interval_cases j <;>
          simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
  have e11 : WordR main (rollP 2)
      (fun vs => vs = iu :: W :: .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) :: iY ::
        .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iS :: iR :: iP :: tL :: rest)
      (fun _ out => out = .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) :: iu :: W :: iY ::
        .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iS :: iR :: iP :: tL :: rest)
      (fun _ => KB * V) :=
    rollU (hroll main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
      (by intro j hj; interval_cases j <;>
          simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
  have e12 : WordR main (rollP 2)
      (fun vs => vs = .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) :: iu :: W :: iY ::
        .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iS :: iR :: iP :: tL :: rest)
      (fun _ out => out = W :: .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) :: iu :: iY ::
        .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iS :: iR :: iP :: tL :: rest)
      (fun _ => KB * V) :=
    rollU (hroll main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
      (by intro j hj; interval_cases j <;>
          simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
  -- the axis word
  have hprod : (X / ts.getD (ts.length - 1 - i) 0) * ts.getD (ts.length - 1 - i) 0 = X := by
    rw [hXdiv]
    exact hXsplit.symm
  have hAB : (X / ts.getD (ts.length - 1 - i) 0) * ts.getD (ts.length - 1 - i) 0 * Y = ts.prod := by
    rw [hprod, hXY]
  have hApos : 0 < X / ts.getD (ts.length - 1 - i) 0 := by rw [hXdiv]; exact hA1
  have hBpos : 0 < Y := by omega
  have hlen_ax : ws.length =
      (X / ts.getD (ts.length - 1 - i) 0) * ts.getD (ts.length - 1 - i) 0 * Y := by
    rw [hAB, hwl]
  have happ_ax : ApproxSL p r
      ((X / ts.getD (ts.length - 1 - i) 0) * ts.getD (ts.length - 1 - i) 0 * Y) ws
      (axisIterN r sgn (ts.drop (ts.length - i)) u0)
      (e + ((ts.drop (ts.length - i)).map (fun t => (Nat.log 2 t : ℝ))).sum) := by
    rw [hAB]; exact happ
  have haxis := hax main p r (X / ts.getD (ts.length - 1 - i) 0) (ts.getD (ts.length - 1 - i) 0) Y
    (Nat.clog 2 (ts.getD (ts.length - 1 - i) 0)) sgn ws
    (axisIterN r sgn (ts.drop (ts.length - i)) u0)
    (e + ((ts.drop (ts.length - i)).map (fun t => (Nat.log 2 t : ℝ))).sum) (tL :: rest)
    hrp hu_pow2 hu_div hr2 hsg hApos hBpos hlen_ax hdisc happ_ax
  have haxc : Ka * ((X / ts.getD (ts.length - 1 - i) 0) * ts.getD (ts.length - 1 - i) 0 * Y) *
        (r + 1) * (p + 1) * (Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) + 1) +
      Ka * ((X / ts.getD (ts.length - 1 - i) 0) * ts.getD (ts.length - 1 - i) 0 * Y) *
        (r + 1) * (p + 1) *
        ((((X / ts.getD (ts.length - 1 - i) 0) * ts.getD (ts.length - 1 - i) 0 * Y)).size + 2) +
      Ka ≤ KB * V := by
    rw [hAB]
    have hk1 : Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) + 1 ≤ ts.prod.size + 2 := by omega
    have h5 : Ka * ts.prod * (r + 1) * (p + 1) * (Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) + 1) ≤
        Ka * ts.prod * (r + 1) * (p + 1) * (ts.prod.size + 2) :=
      Nat.mul_le_mul_left (Ka * ts.prod * (r + 1) * (p + 1)) hk1
    have h6 : Ka * ts.prod * (r + 1) * (p + 1) * (ts.prod.size + 2) +
        Ka * ts.prod * (r + 1) * (p + 1) * (ts.prod.size + 2) + Ka ≤ V := by
      have h := hKa
      have he : Ka * ts.prod * (r + 1) * (p + 1) * (ts.prod.size + 2) +
          Ka * ts.prod * (r + 1) * (p + 1) * (ts.prod.size + 2) + Ka =
          Ka * (ts.prod * (r + 1) * (p + 1) * (ts.prod.size + 2)) * 2 + Ka := by ring
      rw [he]; exact h
    have h7 : Ka * ts.prod * (r + 1) * (p + 1) * (Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) + 1) +
        Ka * ts.prod * (r + 1) * (p + 1) * (ts.prod.size + 2) + Ka ≤
        Ka * ts.prod * (r + 1) * (p + 1) * (ts.prod.size + 2) +
        Ka * ts.prod * (r + 1) * (p + 1) * (ts.prod.size + 2) + Ka := by
      omega
    have h8 := le_trans h7 h6
    have h9 : Ka * ts.prod * (r + 1) * (p + 1) * (Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) + 1) +
        Ka * ts.prod * (r + 1) * (p + 1) * (ts.prod.size + 2) + Ka ≤ KB * V := by
      have hK := hKB1
      calc Ka * ts.prod * (r + 1) * (p + 1) * (Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) + 1) +
          Ka * ts.prod * (r + 1) * (p + 1) * (ts.prod.size + 2) + Ka ≤ V := h8
        _ ≤ KB * V := by simpa using Nat.mul_le_mul_right V hK
    nlinarith [h9]
  have haxis' : WordR main axisP
      (fun vs => vs = W :: .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) :: iu :: iY ::
        .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iS :: iR :: iP :: tL :: rest)
      (fun _ out => ∃ w : List (List (ℤ × ℤ)),
        out = ofList (cvecs w) :: .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) :: iu :: iY ::
          .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          iS :: iR :: iP :: tL :: rest ∧
        w.length = ts.prod ∧ (∀ x ∈ w, InDiscVec p r x) ∧
        ApproxSL p r ts.prod w (axisIterN r sgn (ts.drop (ts.length - i - 1)) u0)
          (e + ((ts.drop (ts.length - i - 1)).map (fun t => (Nat.log 2 t : ℝ))).sum))
      (fun _ => KB * V) := by
    refine WordR_weaken haxis (fun vs hvs => hvs) ?_ ?_
    · intro vs out hvs hout
      obtain ⟨w, hout', hw1, hw2, hw3⟩ := hout
      refine ⟨w, ?_, ?_, hw2, ?_⟩
      · rw [hout']
      · rw [hw1]; exact hAB
      · have hdrop2 : ts.drop (ts.length - i - 1) =
            ts.getD (ts.length - 1 - i) 0 :: ts.drop (ts.length - i) := hdrop
        have harr : axisT r (ts.getD (ts.length - 1 - i) 0) Y sgn
            (axisIterN r sgn (ts.drop (ts.length - i)) u0) =
            axisIterN r sgn (ts.drop (ts.length - i - 1)) u0 := by
          rw [hdrop2]
          simp only [axisIterN]
          rw [← hY]
        have herr : (e + ((ts.drop (ts.length - i)).map (fun t => (Nat.log 2 t : ℝ))).sum) +
              (Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℝ) =
            e + ((ts.drop (ts.length - i - 1)).map (fun t => (Nat.log 2 t : ℝ))).sum := by
          rw [hdrop2, List.map_cons, List.sum_cons]
          have h1 : ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℝ) =
              (Nat.log 2 (ts.getD (ts.length - 1 - i) 0) : ℝ) := by
            rw [AxPure.log_eq_clog_of_isPow2 _ hu_pow]
          rw [h1]; ring
        rw [hAB, harr, herr] at hw3
        exact hw3
    · intro vs hvs
      exact haxc
  -- the composition of part 1 with the axis word
  have c12 : WordR main (dupP ;;; dupP ;;; clP ;;; rollP 5 ;;; rollP 5 ;;; rollP 3 ;;; swapP ;;; tdP ;;;
      rollP 4 ;;; rollP 4 ;;; rollP 2 ;;; rollP 2)
      (fun vs => vs = iu :: W :: iX :: iY :: iS :: iR :: iP :: tL :: rest)
      (fun _ out => out = W :: .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) :: iu :: iY ::
        .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
        iS :: iR :: iP :: tL :: rest) (fun _ => 12 * (KB * V)) := by
    have h := WordR_seqC (WordR_seqC (WordR_seqC (WordR_seqC (WordR_seqC (WordR_seqC
      (WordR_seqC (WordR_seqC (WordR_seqC (WordR_seqC (WordR_seqC e1 e2) e3) e4) e5) e6) e7)
      e8) e9) e10) e11) e12
    refine WordR_weaken h (fun vs hvs => hvs) (fun vs out hvs hout => hout) (fun vs => ?_)
    omega
  have hmid : WordR main (dupP ;;; dupP ;;; clP ;;; rollP 5 ;;; rollP 5 ;;; rollP 3 ;;; swapP ;;; tdP ;;;
      rollP 4 ;;; rollP 4 ;;; rollP 2 ;;; rollP 2 ;;; axisP)
      (fun vs => vs = iu :: W :: iX :: iY :: iS :: iR :: iP :: tL :: rest)
      (fun _ out => ∃ w : List (List (ℤ × ℤ)),
        out = ofList (cvecs w) :: .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) :: iu :: iY ::
          .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          iS :: iR :: iP :: tL :: rest ∧
        w.length = ts.prod ∧ (∀ x ∈ w, InDiscVec p r x) ∧
        ApproxSL p r ts.prod w (axisIterN r sgn (ts.drop (ts.length - i - 1)) u0)
          (e + ((ts.drop (ts.length - i - 1)).map (fun t => (Nat.log 2 t : ℝ))).sum))
      (fun _ => 12 * (KB * V) + KB * V) :=
    WordR_seqQ c12 (fun B hB => by rw [hB]; exact haxis')
  -- part 2: the last eight operations
  have hpart2 : ∀ (w : List (List (ℤ × ℤ))), w.length = ts.prod →
      (∀ x ∈ w, InDiscVec p r x) →
      ApproxSL p r ts.prod w (axisIterN r sgn (ts.drop (ts.length - i - 1)) u0)
        (e + ((ts.drop (ts.length - i - 1)).map (fun t => (Nat.log 2 t : ℝ))).sum) →
      WordR main (rollP 3 ;;; rollP 3 ;;; swapP ;;; mulP ;;; rollP 3 ;;; kdrP ;;; rollP 2 ;;; rollP 2)
        (fun vs => vs = ofList (cvecs w) :: .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          iu :: iY :: .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          iS :: iR :: iP :: tL :: rest)
        (fun _ out => out = ofList (cvecs w) :: .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          .int (((Y * ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) :: iS :: iR :: iP :: tL :: rest)
        (fun _ => 8 * (KB * V)) := by
    intro w hwl' hdisc' happ'
    have hwV : vsz (ofList (cvecs w)) ≤ V := by
      refine le_trans (AxPure.vsz_ofList_cvecs_le p r (ts.prod) w hp1 hM1 hwl' hdisc') hV1
    have huV2' : isz ((ts.getD (ts.length - 1 - i) 0 : ℕ) : ℤ) ≤ V := huV'
    have hYm : vsz (.int ((Y : ℤ) * ((ts.getD (ts.length - 1 - i) 0 : ℕ) : ℤ))) ≤ V := hYmV
    have hYm' : vsz (.int (((Y * ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ)) ≤ V := by
      rw [show (.int (((Y * ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) : Val) =
        .int ((Y : ℤ) * ((ts.getD (ts.length - 1 - i) 0 : ℕ) : ℤ)) from by
          rw [Int.natCast_mul]]
      exact hYm
    have f1 : WordR main (rollP 3)
        (fun vs => vs = ofList (cvecs w) :: .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          iu :: iY :: .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          iS :: iR :: iP :: tL :: rest)
        (fun _ out => out = iY :: ofList (cvecs w) ::
          .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) :: iu ::
          .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          iS :: iR :: iP :: tL :: rest) (fun _ => KB * V) :=
      rollU (hroll main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
        (by intro j hj; interval_cases j <;>
            simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
    have f2 : WordR main (rollP 3)
        (fun vs => vs = iY :: ofList (cvecs w) ::
          .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) :: iu ::
          .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          iS :: iR :: iP :: tL :: rest)
        (fun _ out => out = iu :: iY :: ofList (cvecs w) ::
          .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          iS :: iR :: iP :: tL :: rest) (fun _ => KB * V) :=
      rollU (hroll main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
        (by intro j hj; interval_cases j <;>
            simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
    have f3 : WordR main swapP
        (fun vs => vs = iu :: iY :: ofList (cvecs w) ::
          .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          iS :: iR :: iP :: tL :: rest)
        (fun _ out => out = iY :: iu :: ofList (cvecs w) ::
          .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          iS :: iR :: iP :: tL :: rest) (fun _ => KB * V) :=
      swapU (hswap main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
        (by simp only [List.getD_cons_zero]; exact huV)
        (by simp only [List.getD_cons_zero, List.getD_cons_succ]; exact hYV)
    have f4 : WordR main mulP
        (fun vs => vs = iY :: iu :: ofList (cvecs w) ::
          .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          iS :: iR :: iP :: tL :: rest)
        (fun _ out => out = .int (((Y * ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          ofList (cvecs w) :: .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          iS :: iR :: iP :: tL :: rest) (fun _ => KB * V) := by
      refine WordR_weaken (mulU (hmul main) hKB1 (by
        have h1 : isz (Y : ℤ) ≤ ts.prod.size + 2 := AxPure.isz_le_size _ _ hYle
        have h2 : isz ((ts.getD (ts.length - 1 - i) 0 : ℕ) : ℤ) ≤ ts.prod.size + 2 :=
          AxPure.isz_le_size _ _ hu_le
        have h3 : Km * isz (Y : ℤ) * isz ((ts.getD (ts.length - 1 - i) 0 : ℕ) : ℤ) ≤
            Km * (ts.prod.size + 2) * (ts.prod.size + 2) := by
          calc Km * isz (Y : ℤ) * isz ((ts.getD (ts.length - 1 - i) 0 : ℕ) : ℤ)
              ≤ Km * (ts.prod.size + 2) * isz ((ts.getD (ts.length - 1 - i) 0 : ℕ) : ℤ) :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul_left Km h1)
            _ ≤ Km * (ts.prod.size + 2) * (ts.prod.size + 2) := Nat.mul_le_mul_left _ h2
        have h4 : Km * (ts.prod.size + 2) * (ts.prod.size + 2) ≤ V := by
          have h := hKm
          have he : Km * (ts.prod.size + 2) * (ts.prod.size + 2) =
              Km * ((ts.prod.size + 2) * (ts.prod.size + 2)) := by ring
          rw [he]; exact h
        exact le_trans h3 h4))
        (fun vs hvs => hvs) ?_ (fun _ _ => le_rfl)
      intro vs out hvs hout
      rw [hout]
      exact congrArg (fun z : ℤ => .int z :: ofList (cvecs w) ::
        (Val.int ((X / ts.getD (ts.length - 1 - i) 0 : ℕ) : ℤ)) ::
        (Val.int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ)) ::
        iS :: iR :: iP :: tL :: rest)
        (Int.natCast_mul Y (ts.getD (ts.length - 1 - i) 0)).symm
    have f5 : WordR main (rollP 3)
        (fun vs => vs = .int (((Y * ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          ofList (cvecs w) :: .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          iS :: iR :: iP :: tL :: rest)
        (fun _ out => out = .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          .int (((Y * ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          ofList (cvecs w) :: .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          iS :: iR :: iP :: tL :: rest) (fun _ => KB * V) :=
      rollU (hroll main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
        (by intro j hj; interval_cases j <;>
            simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
    have f6 : WordR main kdrP
        (fun vs => vs = .int ((Nat.clog 2 (ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          .int (((Y * ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          ofList (cvecs w) :: .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          iS :: iR :: iP :: tL :: rest)
        (fun _ out => out = .int (((Y * ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          ofList (cvecs w) :: .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          iS :: iR :: iP :: tL :: rest) (fun _ => KB * V) :=
      drU (hkdr main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
        (by simp only [List.headD_cons]; exact hkV)
    have f7 : WordR main (rollP 2)
        (fun vs => vs = .int (((Y * ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          ofList (cvecs w) :: .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          iS :: iR :: iP :: tL :: rest)
        (fun _ out => out = .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          .int (((Y * ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          ofList (cvecs w) :: iS :: iR :: iP :: tL :: rest) (fun _ => KB * V) :=
      rollU (hroll main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
        (by intro j hj; interval_cases j <;>
            simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
    have f8 : WordR main (rollP 2)
        (fun vs => vs = .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          .int (((Y * ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          ofList (cvecs w) :: iS :: iR :: iP :: tL :: rest)
        (fun _ out => out = ofList (cvecs w) ::
          .int (((X / ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          .int (((Y * ts.getD (ts.length - 1 - i) 0) : ℕ) : ℤ) ::
          iS :: iR :: iP :: tL :: rest) (fun _ => KB * V) :=
      rollU (hroll main) (by rw [hKBdef]; omega) (by omega : 1 ≤ V) (by simp)
        (by intro j hj; interval_cases j <;>
            simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
    have h := WordR_seqC (WordR_seqC (WordR_seqC (WordR_seqC (WordR_seqC (WordR_seqC
      (WordR_seqC f1 f2) f3) f4) f5) f6) f7) f8
    refine WordR_weaken h (fun vs hvs => hvs) (fun vs out hvs hout => hout) (fun vs => ?_)
    omega
  -- the final assembly
  have hfull : WordR main (stepProg dupP clP tdP mulP kdrP swapP axisP rollP)
      (fun vs => vs = iu :: W :: iX :: iY :: iS :: iR :: iP :: tL :: rest)
      (fun _ out => AxInv p r ts sgn u0 e tL rest (i + 1) out)
      (fun _ => (12 * (KB * V) + KB * V) + 8 * (KB * V)) :=
    WordR_seqQ hmid (fun B hB => by
      obtain ⟨w, hout, hwl', hdisc', happ'⟩ := hB
      refine WordR_weaken (hpart2 w hwl' hdisc' happ') (fun vs hvs => ?_)
        (fun vs out hvs hout' => ?_) (fun _ _ => le_rfl)
      · rw [hvs, hout]
      · rw [hout']
        exact ⟨w, X / ts.getD (ts.length - 1 - i) 0, Y * ts.getD (ts.length - 1 - i) 0,
          rfl, hwl', hdisc', happ',
          by rw [show ts.length - (i + 1) = ts.length - i - 1 by omega]; exact hXdiv,
          by rw [show ts.length - (i + 1) = ts.length - i - 1 by omega]
             rw [hYcons]; ring⟩)
  refine WordR_weaken hfull (fun vs hvs => ?_) (fun vs out hvs hout => hout) (fun vs => ?_)
  · rw [hvs, hacc, drv_getD ts i hi]
  · intro vs
    rw [hKBdef]
    have hR : (25 * (1000 * Kd + 1000 * Kc + 1000 * Kt + 1000 * Km + 1000 * Kdr + 1000 * Ksw +
          1000 * Krl + 1000 * Ka + 1000)) * V =
        25 * ((1000 * Kd + 1000 * Kc + 1000 * Kt + 1000 * Km + 1000 * Kdr + 1000 * Ksw +
          1000 * Krl + 1000 * Ka + 1000) * V) := by ring
    rw [hR]
    omega

/-! ### The postlude: hand back `intList ts` and drop the bookkeeping values -/

def postProg (swapP kdrP : Cmd) (rollP : ℕ → Cmd) : Cmd :=
  rollP 6 ;;; rollP 3 ;;; kdrP ;;; rollP 2 ;;; kdrP ;;; swapP

theorem postWord (hk : Work.SynFFT.KLib) :
    ∃ (prog : Cmd) (KC : ℕ), ∀ (main : Cmd) (p r : ℕ) (ts : List ℕ) (sgn : ℤ) (u0 : Arr r)
      (e : ℝ) (rest : List Val) (V : ℕ),
    1 ≤ V → 3 ≤ V → vsz (iList ts) ≤ V → isz ((ts.prod : ℕ) : ℤ) ≤ V → isz sgn ≤ V →
    isz (r : ℤ) ≤ V → isz (p : ℤ) ≤ V →
    (∀ (ws' : List (List (ℤ × ℤ))), ws'.length = ts.prod → (∀ w ∈ ws', InDiscVec p r w) →
      vsz (ofList (cvecs ws')) ≤ V) →
    ∀ (acc : List Val), AxInv p r ts sgn u0 e (iList ts) rest ts.length acc →
    WordR main prog (fun vs => vs = acc)
      (fun _ out => ∃ ws' : List (List (ℤ × ℤ)),
        out = ofList (cvecs ws') :: iList ts :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest ∧
        ws'.length = ts.prod ∧ (∀ w ∈ ws', InDiscVec p r w) ∧
        ApproxSL p r ts.prod ws' (axisIterN r sgn ts u0)
          (e + (ts.map (fun t => (Nat.log 2 t : ℝ))).sum))
      (fun _ => KC * V) := by
  obtain ⟨swapP, Ksw, hswap⟩ := hk.swap
  obtain ⟨kdrP, Kdr, hkdr⟩ := hk.drop
  obtain ⟨rollP, Krl, hroll⟩ := hk.roll
  refine ⟨postProg swapP kdrP rollP,
    6 * (1000 * Ksw + 1000 * Kdr + 1000 * Krl + 1000), ?_⟩
  intro main p r ts sgn u0 e rest V hV1 hV3 hTV hMv hSv hRv hPv hwsb acc hInv
  set KB : ℕ := 1000 * Ksw + 1000 * Kdr + 1000 * Krl + 1000 with hKBdef
  obtain ⟨ws', X, Y, hacc, hwl, hdisc, happ, hX, hY⟩ := hInv
  have hzero : ts.length - ts.length = 0 := by omega
  have hX1 : X = 1 := by
    rw [hX, hzero, List.take_zero]
    rfl
  have hYM : Y = ts.prod := by
    rw [hY, hzero, List.drop_zero]
  have happ' : ApproxSL p r ts.prod ws' (axisIterN r sgn ts u0)
      (e + (ts.map (fun t => (Nat.log 2 t : ℝ))).sum) := by
    rw [hzero, List.drop_zero] at happ
    exact happ
  have hwV : vsz (ofList (cvecs ws')) ≤ V := hwsb ws' hwl hdisc
  have h1b : vsz (.int (1 : ℤ)) ≤ V := by
    rw [show vsz (.int (1 : ℤ)) = 3 by simp [MrgKit.vsz_int', isz]]
    exact hV3
  have hMb : vsz (.int ((ts.prod : ℕ) : ℤ)) ≤ V := by
    rw [MrgKit.vsz_int']
    exact hMv
  have hSv' : vsz (.int sgn) ≤ V := by rw [MrgKit.vsz_int']; exact hSv
  have hRv' : vsz (.int (r : ℤ)) ≤ V := by rw [MrgKit.vsz_int']; exact hRv
  have hPv' : vsz (.int (p : ℤ)) ≤ V := by rw [MrgKit.vsz_int']; exact hPv
  -- the six operations
  have g1 : WordR main (rollP 6)
      (fun vs => vs = ofList (cvecs ws') :: .int (1 : ℤ) :: .int ((ts.prod : ℕ) : ℤ) ::
        .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: iList ts :: rest)
      (fun _ out => out = iList ts :: ofList (cvecs ws') :: .int (1 : ℤ) ::
        .int ((ts.prod : ℕ) : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ => KB * V) :=
    rollU (hroll main) (by rw [hKBdef]; omega) hV1 (by simp)
      (by intro j hj
          interval_cases j
          · simp only [List.getD_cons_zero]; exact hwV
          · simp only [List.getD_cons_zero, List.getD_cons_succ]; exact h1b
          · simp only [List.getD_cons_zero, List.getD_cons_succ]; exact hMb
          · simp only [List.getD_cons_zero, List.getD_cons_succ]; exact hSv'
          · simp only [List.getD_cons_zero, List.getD_cons_succ]; exact hRv'
          · simp only [List.getD_cons_zero, List.getD_cons_succ]; exact hPv'
          · simp only [List.getD_cons_zero, List.getD_cons_succ]; exact hTV)
  have g2 : WordR main (rollP 3)
      (fun vs => vs = iList ts :: ofList (cvecs ws') :: .int (1 : ℤ) ::
        .int ((ts.prod : ℕ) : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = .int ((ts.prod : ℕ) : ℤ) :: iList ts :: ofList (cvecs ws') ::
        .int (1 : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ => KB * V) :=
    rollU (hroll main) (by rw [hKBdef]; omega) hV1 (by simp)
      (by intro j hj; interval_cases j <;>
          simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
  have g3 : WordR main kdrP
      (fun vs => vs = .int ((ts.prod : ℕ) : ℤ) :: iList ts :: ofList (cvecs ws') ::
        .int (1 : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = iList ts :: ofList (cvecs ws') ::
        .int (1 : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ => KB * V) :=
    drU (hkdr main) (by rw [hKBdef]; omega) hV1 (by simp)
      (by simp only [List.headD_cons]; exact hMb)
  have g4 : WordR main (rollP 2)
      (fun vs => vs = iList ts :: ofList (cvecs ws') ::
        .int (1 : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = .int (1 : ℤ) :: iList ts :: ofList (cvecs ws') ::
        .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ => KB * V) :=
    rollU (hroll main) (by rw [hKBdef]; omega) hV1 (by simp)
      (by intro j hj; interval_cases j <;>
          simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega)
  have g5 : WordR main kdrP
      (fun vs => vs = .int (1 : ℤ) :: iList ts :: ofList (cvecs ws') ::
        .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = iList ts :: ofList (cvecs ws') ::
        .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ => KB * V) :=
    drU (hkdr main) (by rw [hKBdef]; omega) hV1 (by simp)
      (by simp only [List.headD_cons]; exact h1b)
  have g6 : WordR main swapP
      (fun vs => vs = iList ts :: ofList (cvecs ws') ::
        .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = ofList (cvecs ws') :: iList ts ::
        .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ => KB * V) :=
    swapU (hswap main) (by rw [hKBdef]; omega) hV1 (by simp)
      (by simp only [List.getD_cons_zero]; exact hTV)
      (by simp only [List.getD_cons_zero, List.getD_cons_succ]; exact hwV)
  have h := WordR_seqC (WordR_seqC (WordR_seqC (WordR_seqC (WordR_seqC g1 g2) g3) g4) g5) g6
  refine WordR_weaken h (fun vs hvs => ?_) (fun _ out _ hout => ⟨ws', hout, hwl, hdisc, happ'⟩)
    (fun vs => ?_)
  · rw [hvs, hacc, hX1, hYM]
    norm_num
  · rw [hKBdef]
    have hR : (6 * (1000 * Ksw + 1000 * Kdr + 1000 * Krl + 1000)) * V =
        6 * ((1000 * Ksw + 1000 * Kdr + 1000 * Krl + 1000) * V) := by ring
    rw [hR]
    omega


/-! ### The assembly -/

theorem axesFoldMain (hk : Work.SynFFT.KLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib)
    (ha : Work.SynFFT.HasAxis) :
    ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p r : ℕ) (ts : List ℕ) (sgn : ℤ)
      (ws : List (List (ℤ × ℤ))) (u : Arr r) (e : ℝ) (rest : List Val),
    HvdH.IsPow2 r → (∀ t ∈ ts, HvdH.IsPow2 t) → (∀ t ∈ ts, t ∣ 2 * r) →
    (∀ t ∈ ts, 2 ≤ t) → 2 * r < 2 ^ p → (sgn = 1 ∨ sgn = -1) → ws.length = ts.prod →
    (∀ w ∈ ws, InDiscVec p r w) → ApproxSL p r ts.prod ws u e →
    WordR main prog
      (fun vs => vs = ofList (cvecs ws) :: iList ts :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => ∃ ws' : List (List (ℤ × ℤ)),
        out = ofList (cvecs ws') :: iList ts :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest ∧
        ws'.length = ts.prod ∧ (∀ w ∈ ws', InDiscVec p r w) ∧
        ApproxSL p r ts.prod ws' (axisIterN r sgn ts u)
          (e + (ts.map (fun t => (Nat.log 2 t : ℝ))).sum))
      (fun _ => K * ((ts.length + 1) * (ts.prod * (r + 1) * (p + 1) * (ts.prod.size + 2))) + K) := by
  obtain ⟨axisP, Ka, hax⟩ := axSpec_of ha
  obtain ⟨mulP, Km, hmul⟩ := hi.mulS
  obtain ⟨tdP, Kt, htd⟩ := hi.tdiv
  obtain ⟨dupP, Kd, hdup⟩ := hk.dup
  obtain ⟨swapP, Ksw, hswap⟩ := hk.swap
  obtain ⟨kdrP, Kdr, hkdr⟩ := hk.drop
  obtain ⟨rollP, Krl, hroll⟩ := hk.roll
  obtain ⟨clP, Kc, hcl⟩ := hi.clog2
  obtain ⟨foldComb, Kfold, hfold⟩ := hk.foldList
  obtain ⟨preP, KCpre, hpre⟩ := preludeWord hk hl
  obtain ⟨stepP, KCstep, hstep⟩ :=
    stepWord dupP clP tdP mulP kdrP swapP axisP rollP hdup hcl htd hmul hkdr hswap hroll hax
  obtain ⟨postP, KCpost, hpost⟩ := postWord hk
  refine ⟨preP ;;; foldComb stepP ;;; postP,
    1000 * (Km + Kt + Ka + 1) * (KCpre + KCstep + 3 * Kfold + KCpost), ?_⟩
  intro main p r ts sgn ws u e rest hrp hpow hdiv h2t hr2 hsg hwl hdisc happ
  set X : ℕ := ts.prod * (r + 1) * (p + 1) * (ts.prod.size + 2) with hXdef
  set V : ℕ := 1000 * (Km + Kt + Ka + 1) * X with hVdef
  have hr2' : 2 ≤ r := AxPure.two_le_of_isPow2 r hrp
  have hp1 : 1 ≤ p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h; simp at hr2; omega
    · exact h
  have hM1 : 1 ≤ ts.prod := AxPure.one_le_prod_of ts (fun t ht => by have := h2t t ht; omega)
  -- The budget `V` and all the size bounds it has to dominate.
  have hpr : r < 2 ^ p := by omega
  obtain ⟨hV1', hV2', hV3', hV4', hV5', hKm', hKt', hKa', h18⟩ :=
    axFoldVBounds p r Km Kt Ka ts.prod V hM1 hr2' hp1 hpr (by rw [hVdef, hXdef])
  have hV0 : 1 ≤ V := le_trans (by norm_num : (1 : ℕ) ≤ 3) hV5'
  -- Value bounds for the prelude.
  have hTV : vsz (iList ts) ≤ V := by
    have h1 : vsz (iList ts) ≤ 18 * (ts.prod + 1) := by
      rw [show iList ts = intList ts from (intList_eq_iList ts).symm]
      exact AxPure.vsz_intList_le ts ts.prod h2t rfl
    exact le_trans h1 h18
  have hWv : vsz (ofList (cvecs ws)) ≤ V :=
    le_trans (AxPure.vsz_ofList_cvecs_le p r ts.prod ws hp1 hM1 hwl hdisc) hV1'
  have hDv : vsz (ofList (drv ts)) ≤ V := by rw [vsz_ofList_drv]; exact hTV
  have hSv : isz sgn ≤ V := by
    rcases hsg with h | h
    · rw [h]; rw [show isz (1 : ℤ) = 3 by simp [isz]]; exact hV5'
    · rw [h]; rw [show isz (-1 : ℤ) = 3 by simp [isz]]; exact hV5'
  have hRv : isz (r : ℤ) ≤ V := le_trans (AxPure.isz_le_size r r (le_refl r)) hV4'
  have hPv : isz (p : ℤ) ≤ V := by
    have h := AxPure.isz_le_size p p (le_refl p)
    have hs := AxPure.size_le_self p
    omega
  have hMv : isz ((ts.prod : ℕ) : ℤ) ≤ V :=
    le_trans (AxPure.isz_le_size ts.prod ts.prod (le_refl ts.prod)) hV2'
  have h1v : isz (1 : ℤ) ≤ V := by rw [show isz (1 : ℤ) = 3 by simp [isz]]; exact hV5'
  -- The prelude.
  have hpre' := hpre main ws ts sgn p r rest V hwl hV0 hWv hTV hDv hSv hRv hPv hMv h1v
  -- The fold: one `stepP` per axis, innermost first.
  have hL : ∀ x ∈ drv ts, vsz x ≤ ts.prod.size + 2 := by
    intro x hx
    rw [drv, List.mem_reverse, List.mem_map] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    rw [MrgKit.vsz_int', isz, Int.natAbs_natCast]
    have h1 : t ≤ ts.prod :=
      AxPure.le_prod_of_mem ts t (fun s hs => by have := h2t s hs; omega) ht
    have h2 : t.size ≤ ts.prod.size := Nat.size_le_size h1
    omega
  have hstep'' : ∀ (i : ℕ) (acc : List Val), i < (drv ts).length →
      AxInv p r ts sgn u e (iList ts) rest i acc →
      WordR main stepP (fun vs => vs = (drv ts).getD i .nil :: acc)
        (fun _ out => AxInv p r ts sgn u e (iList ts) rest (i + 1) out)
        (fun _ => KCstep * V) := by
    intro i acc hi' hInv
    have hi'' : i < ts.length := by
      simpa only [drv, List.length_reverse, List.length_map] using hi'
    exact hstep main p r ts sgn u e (iList ts) rest V i acc hrp hpow hdiv h2t hr2 hsg
      hV1' hV2' hV3' hV4' hV5' hM1 hKm' hKt' hKa' hi'' hInv
  have hfold' := hfold main stepP (drv ts) (AxInv p r ts sgn u e (iList ts) rest)
    (KCstep * V) (ts.prod.size + 2) hL hstep''
  -- The invariant at the beginning of the fold.
  have hinit : AxInv p r ts sgn u e (iList ts) rest 0
      (ofList (cvecs ws) :: .int ((ts.prod : ℕ) : ℤ) :: .int ((1 : ℕ) : ℤ) :: .int sgn ::
        .int (r : ℤ) :: .int (p : ℤ) :: iList ts :: rest) := by
    refine ⟨ws, ts.prod, 1, rfl, hwl, hdisc, ?_, ?_, ?_⟩
    · rw [Nat.sub_zero, List.drop_eq_nil_of_le (le_refl ts.length)]
      simp only [axisIterN, List.map_nil, List.sum_nil, add_zero]
      exact happ
    · rw [Nat.sub_zero, List.take_length]
    · rw [Nat.sub_zero, List.drop_length, List.prod_nil]
  -- Prelude followed by the fold.
  have hc1raw := hk.seq main preP (foldComb stepP)
      (fun vs => vs = ofList (cvecs ws) :: iList ts :: .int sgn :: .int (r : ℤ) ::
        .int (p : ℤ) :: rest)
      (fun _ out => out = ofList (drv ts) :: ofList (cvecs ws) :: .int ((ts.prod : ℕ) : ℤ) ::
        .int ((1 : ℕ) : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: iList ts :: rest)
      (fun _ => KCpre * V)
      (fun mid => ∃ acc, mid = ofList (drv ts) :: acc ∧
        AxInv p r ts sgn u e (iList ts) rest 0 acc)
      (fun _ out => AxInv p r ts sgn u e (iList ts) rest (drv ts).length out)
      (fun _ => (drv ts).length * (KCstep * V + Kfold * ((ts.prod.size + 2) + 1)) + Kfold)
      (fun _ => (drv ts).length * (KCstep * V + Kfold * ((ts.prod.size + 2) + 1)) + Kfold)
      hpre' hfold'
      (fun vs mid hvs hmid => by
        have hmid' : mid = ofList (drv ts) :: (ofList (cvecs ws) :: .int ((ts.prod : ℕ) : ℤ) ::
            .int ((1 : ℕ) : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) ::
            iList ts :: rest) := hmid
        refine ⟨⟨ofList (cvecs ws) :: .int ((ts.prod : ℕ) : ℤ) :: .int ((1 : ℕ) : ℤ) ::
          .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: iList ts :: rest, ?_, hinit⟩, le_rfl⟩
        rw [hmid'])
  have hc1 : WordR main (preP ;;; foldComb stepP)
      (fun vs => vs = ofList (cvecs ws) :: iList ts :: .int sgn :: .int (r : ℤ) ::
        .int (p : ℤ) :: rest)
      (fun _ out => AxInv p r ts sgn u e (iList ts) rest ts.length out)
      (fun _ => KCpre * V +
        ((drv ts).length * (KCstep * V + Kfold * ((ts.prod.size + 2) + 1)) + Kfold)) :=
    WordR_weaken hc1raw (fun vs hvs => hvs)
      (fun vs out hvs hout => by
        obtain ⟨mid, _, h2⟩ := hout
        have hlen : (drv ts).length = ts.length := by simp [drv]
        exact hlen ▸ h2)
      (fun vs _ => le_rfl)
  -- The postlude.
  have hpost2 : WordR main postP
      (fun vs => AxInv p r ts sgn u e (iList ts) rest ts.length vs)
      (fun _ out => ∃ ws' : List (List (ℤ × ℤ)),
        out = ofList (cvecs ws') :: iList ts :: .int sgn :: .int (r : ℤ) ::
          .int (p : ℤ) :: rest ∧
        ws'.length = ts.prod ∧ (∀ w ∈ ws', InDiscVec p r w) ∧
        ApproxSL p r ts.prod ws' (axisIterN r sgn ts u)
          (e + (ts.map (fun t => (Nat.log 2 t : ℝ))).sum))
      (fun _ => KCpost * V) := by
    intro vs hvs s R hR
    have h := hpost main p r ts sgn u e rest V hV0 hV5' hTV hMv hSv hRv hPv
      (fun ws' h1 h2 =>
        le_trans (AxPure.vsz_ofList_cvecs_le p r ts.prod ws' hp1 hM1 h1 h2) hV1')
      vs hvs
    exact h vs rfl s R hR
  have hfin := hk.seq main (preP ;;; foldComb stepP) postP
      (fun vs => vs = ofList (cvecs ws) :: iList ts :: .int sgn :: .int (r : ℤ) ::
        .int (p : ℤ) :: rest)
      (fun _ out => AxInv p r ts sgn u e (iList ts) rest ts.length out)
      (fun _ => KCpre * V +
        ((drv ts).length * (KCstep * V + Kfold * ((ts.prod.size + 2) + 1)) + Kfold))
      (fun vs => AxInv p r ts sgn u e (iList ts) rest ts.length vs)
      (fun _ out => ∃ ws' : List (List (ℤ × ℤ)),
        out = ofList (cvecs ws') :: iList ts :: .int sgn :: .int (r : ℤ) ::
          .int (p : ℤ) :: rest ∧
        ws'.length = ts.prod ∧ (∀ w ∈ ws', InDiscVec p r w) ∧
        ApproxSL p r ts.prod ws' (axisIterN r sgn ts u)
          (e + (ts.map (fun t => (Nat.log 2 t : ℝ))).sum))
      (fun _ => KCpost * V)
      (fun _ => KCpost * V)
      hc1 hpost2
      (fun vs mid hvs hmid => ⟨hmid, le_rfl⟩)
  refine WordR_weaken hfin (fun vs hvs => hvs)
    (fun vs out hvs hout => by
      obtain ⟨mid, _, h2⟩ := hout
      exact h2)
    (fun vs _ => ?_)
  rw [show (drv ts).length = ts.length by simp [drv]]
  have hS : (ts.prod.size + 2) + 1 ≤ 2 * V := by omega
  exact axFoldCost KCpre KCstep KCpost Kfold Km Kt Ka ts.length (ts.prod.size + 2) V X hVdef hS
end AxFold

/-! ### The requested lemma -/

/-- The `HasAxesFold` statement, from `axesFoldMain` by rewriting `iList` to `intList`
and re-associating the cost. -/
theorem hasAxesFold (hk : Work.SynFFT.KLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib)
    (hf : HvdH.FxLib) (ha : Work.SynFFT.HasAxis) : Work.SynFFT.HasAxesFold := by
  obtain ⟨prog, K, h⟩ := AxFold.axesFoldMain hk hi hl ha
  refine ⟨prog, K, ?_⟩
  intro main p r ts sgn ws u e rest hrp hpow hdiv h2t hr2 hsg hwl hdisc happ
  refine MrgKit.WordR_weaken (h main p r ts sgn ws u e rest hrp hpow hdiv h2t hr2 hsg hwl hdisc happ)
    (fun vs hvs => by simpa [AxFold.intList_eq_iList] using hvs)
    (fun vs out _ hout => by
      obtain ⟨ws', h1, h2, h3, h4⟩ := hout
      exact ⟨ws', by simpa [AxFold.intList_eq_iList] using h1, h2, h3, h4⟩)
    (fun vs _ => by
      show K * ((ts.length + 1) * (ts.prod * (r + 1) * (p + 1) * (ts.prod.size + 2))) + K ≤
        K * (ts.length + 1) * ts.prod * (r + 1) * (p + 1) * (ts.prod.size + 2) + K
      have hEq : K * ((ts.length + 1) * (ts.prod * (r + 1) * (p + 1) * (ts.prod.size + 2))) + K =
          K * (ts.length + 1) * ts.prod * (r + 1) * (p + 1) * (ts.prod.size + 2) + K := by ring
      rw [hEq])
end Work.SynFFT
