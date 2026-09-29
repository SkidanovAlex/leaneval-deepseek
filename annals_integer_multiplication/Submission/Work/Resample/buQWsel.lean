import Mathlib
import Submission.Work.Resample.buQWdefs
import Submission.Work.Resample.buQWkey
import Submission.Work.Resample.buQWsort
import Submission.Work.Resample.buQWSelDefs
import Submission.Work.Resample.auKit
import Submission.Work.Resample.auInnerElem
import Submission.Work.Resample.auPrepDefs
import Submission.Work.Resample.auPreKit
import Submission.Work.Fx.FxCommon
import Submission.Work.Kernel.Raw
import Submission.Work.Resample.buHalveIn
import Submission.Work.Resample.buSelLInV
import Submission.Work.Resample.buKeysSpec
import Submission.Work.Resample.buSelElemWord
import Submission.Work.Resample.buSelSorted
import Submission.Work.Resample.buSelRecsSpec
import Submission.Work.Resample.buSelOutEq
import Submission.Work.Resample.buZipConsWord

/-!
# `Work.Resample.buQWsel`: the selection stage of the one-dimensional `B̃` word

Given the input vector `u` (length `t`) together with the static key list `buKeysT s t` and the
parameter `s`, the stage produces `buSelL s t u` (the fused `C̃ ∘ P̃_t` selection followed by the
halving, paper Prop. 4.7(ii)), in cost `Kc (t+1) (p+1)^2`.

The word is `zipWith` (`KL.consV`) of the key list with the vector, then `LL.sortByKey`, then
`LL.take s`, then `KL.mapList` with the element word that drops the key and halves the pair.  The
mathematics is `buQWsort` (the sorted records with keys `0…s-1`) plus the index facts of
`buQWkey`; the size invariant is `buInV`.

-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace Work.Resample

open HvdH
open Work.Fx

/-! ## window specifications -/

/-- `WS main p A B c`: the word `p` transforms the window `A` (sitting on top of an arbitrary list
of values) into some window satisfying `B`, at cost `≤ c`, leaving everything below untouched. -/
def WS (main p : HvdH.Cmd) (A : List HvdH.Val) (B : List HvdH.Val → Prop) (c : ℕ) : Prop :=
  ∀ rest : List HvdH.Val, HvdH.WordR main p (fun vs => vs = A ++ rest)
    (fun _ out => ∃ Bv : List HvdH.Val, B Bv ∧ out = Bv ++ rest) (fun _ => c)

theorem WS.ofPipe (KL : HvdH.KernelLib) {main p : HvdH.Cmd} {A B : List HvdH.Val} {c : ℕ}
    (h : Pipe main p A B c) : WS main p A (fun Bv => Bv = B) c := by
  intro rest
  refine KL.conseq (main := main) (p := p)
    (P := fun vs => vs = A ++ rest) (P' := fun vs => vs = A ++ rest)
    (Q := fun _ out => out = B ++ rest)
    (Q' := fun _ out => ∃ Bv : List HvdH.Val, Bv = B ∧ out = Bv ++ rest)
    (C := fun _ => c) (C' := fun _ => c)
    (h rest) (fun vs hvs => hvs) ?_ (fun vs hvs => le_rfl)
  intro vs out hvs hout
  exact ⟨B, rfl, hout⟩

theorem WS.mono (KL : HvdH.KernelLib) {main p : HvdH.Cmd} {A : List HvdH.Val}
    {B C : List HvdH.Val → Prop} {c : ℕ} (h : WS main p A B c) (hBC : ∀ Bv, B Bv → C Bv) :
    WS main p A C c := by
  intro rest
  refine KL.conseq (main := main) (p := p)
    (P := fun vs => vs = A ++ rest) (P' := fun vs => vs = A ++ rest)
    (Q := fun _ out => ∃ Bv : List HvdH.Val, B Bv ∧ out = Bv ++ rest)
    (Q' := fun _ out => ∃ Cv : List HvdH.Val, C Cv ∧ out = Cv ++ rest)
    (C := fun _ => c) (C' := fun _ => c)
    (h rest) (fun vs hvs => hvs) ?_ (fun vs hvs => le_rfl)
  intro vs out hvs hout
  obtain ⟨Bv, hB, hout⟩ := hout
  exact ⟨Bv, hBC Bv hB, hout⟩

theorem WS.cost (KL : HvdH.KernelLib) {main p : HvdH.Cmd} {A : List HvdH.Val}
    {B : List HvdH.Val → Prop} {c c' : ℕ} (h : WS main p A B c) (hcc : c ≤ c') :
    WS main p A B c' := by
  intro rest
  refine KL.conseq (main := main) (p := p)
    (P := fun vs => vs = A ++ rest) (P' := fun vs => vs = A ++ rest)
    (Q := fun _ out => ∃ Bv : List HvdH.Val, B Bv ∧ out = Bv ++ rest)
    (Q' := fun _ out => ∃ Bv : List HvdH.Val, B Bv ∧ out = Bv ++ rest)
    (C := fun _ => c) (C' := fun _ => c')
    (h rest) (fun vs hvs => hvs) (fun vs out hvs hout => hout) (fun vs hvs => hcc)

theorem WS.comp (KL : HvdH.KernelLib) {main p q : HvdH.Cmd} {A : List HvdH.Val}
    {B C : List HvdH.Val → Prop} {c d : ℕ} (h1 : WS main p A B c)
    (h2 : ∀ Bv, B Bv → WS main q Bv C d) : WS main (.seq p q) A C (c + d) := by
  intro rest
  have h2' : HvdH.WordR main q (fun vs => ∃ Bv : List HvdH.Val, B Bv ∧ vs = Bv ++ rest)
      (fun _ out => ∃ Cv : List HvdH.Val, C Cv ∧ out = Cv ++ rest) (fun _ => d) := by
    intro mid hmid st Rh hRh
    obtain ⟨Bv, hB, hmid'⟩ := hmid
    subst hmid'
    exact h2 Bv hB rest (Bv ++ rest) rfl st Rh hRh
  have hcost : ∀ vs mid, vs = A ++ rest →
      (∃ Bv : List HvdH.Val, B Bv ∧ mid = Bv ++ rest) →
      (∃ Bv : List HvdH.Val, B Bv ∧ mid = Bv ++ rest) ∧ d ≤ d :=
    fun vs mid _ hmid => ⟨hmid, le_rfl⟩
  have hseq := KL.seq (main := main) (p := p) (q := q)
    (P := fun vs : List HvdH.Val => vs = A ++ rest)
    (Q := fun _ out => ∃ Bv : List HvdH.Val, B Bv ∧ out = Bv ++ rest)
    (C := fun _ => c)
    (P' := fun mid => ∃ Bv : List HvdH.Val, B Bv ∧ mid = Bv ++ rest)
    (Q' := fun _ out => ∃ Cv : List HvdH.Val, C Cv ∧ out = Cv ++ rest)
    (C' := fun _ => d) (B := fun _ => d) (h1 rest) h2' hcost
  refine KL.conseq (main := main) (p := .seq p q)
    (P := fun vs => vs = A ++ rest) (P' := fun vs => vs = A ++ rest)
    (Q := fun _ out => ∃ mid, (∃ Bv : List HvdH.Val, B Bv ∧ mid = Bv ++ rest) ∧
      (∃ Cv : List HvdH.Val, C Cv ∧ out = Cv ++ rest))
    (Q' := fun _ out => ∃ Cv : List HvdH.Val, C Cv ∧ out = Cv ++ rest)
    (C := fun _ => c + d) (C' := fun _ => c + d)
    hseq (fun vs hvs => hvs) ?_ (fun vs hvs => le_rfl)
  intro vs out hvs h
  obtain ⟨mid, ⟨Bv, hB, hm⟩, Cv, hC, ho⟩ := h
  exact ⟨Cv, hC, ho⟩

/-! ## sizes -/

/-- The element size bound of the selection stage. -/
def buSL (p : ℕ) : ℕ := 3 * p + 12

lemma isz_fst_le {p : ℕ} {z : ℤ × ℤ} (hz : buIn (2 ^ p) z) : HvdH.isz z.1 ≤ p + 3 := by
  have h1 : z.1.natAbs ≤ 2 ^ p := (buIn_coord hz).1
  have h2 : z.1.natAbs.size ≤ p + 1 := Nat.size_le.mpr (by
    calc z.1.natAbs ≤ 2 ^ p := h1
      _ < 2 ^ (p + 1) := Nat.pow_lt_pow_succ (by norm_num : 1 < 2))
  simp only [HvdH.isz]
  omega

lemma isz_snd_le {p : ℕ} {z : ℤ × ℤ} (hz : buIn (2 ^ p) z) : HvdH.isz z.2 ≤ p + 3 := by
  have h1 : z.2.natAbs ≤ 2 ^ p := (buIn_coord hz).2
  have h2 : z.2.natAbs.size ≤ p + 1 := Nat.size_le.mpr (by
    calc z.2.natAbs ≤ 2 ^ p := h1
      _ < 2 ^ (p + 1) := Nat.pow_lt_pow_succ (by norm_num : 1 < 2))
  simp only [HvdH.isz]
  omega

lemma egLam_le (s t i : ℕ) : egLam s t i ≤ s + i := by
  unfold egLam
  split
  · rename_i h
    have h1 : ((Classical.choose h : Fin s) : ℕ) < s := (Classical.choose h).2
    omega
  · exact le_rfl

lemma isz_egLam_le {s t p : ℕ} (hst : s < t) (htp : t < 2 ^ p) {i : ℕ} (hi : i < t) :
    HvdH.isz (((egLam s t i : ℕ) : ℤ)) ≤ p + 3 := by
  have h1 : egLam s t i ≤ s + i := egLam_le s t i
  have h2 : s + i < 2 ^ (p + 1) := by
    have h3 : s + i ≤ s + t := Nat.add_le_add_left (le_of_lt hi) s
    have h4 : s + t < 2 ^ p + 2 ^ p := by omega
    have h5 : 2 ^ p + 2 ^ p = 2 ^ (p + 1) := by ring
    omega
  have h6 : (egLam s t i : ℤ).natAbs < 2 ^ (p + 1) := by
    rw [Int.natAbs_natCast]
    exact lt_of_le_of_lt h1 h2
  have h7 : (egLam s t i : ℤ).natAbs.size ≤ p + 1 := Nat.size_le.mpr h6
  simp only [HvdH.isz]
  omega

lemma vsz_cfxVal_le_sel {p : ℕ} {z : ℤ × ℤ} (hz : buIn (2 ^ p) z) : HvdH.vsz (cfxVal z) ≤ buSL p := by
  rw [Work.Fx.vsz_cfxVal]
  have h1 := isz_fst_le hz
  have h2 := isz_snd_le hz
  simp only [buSL]
  omega

lemma vsz_key_le {s t p : ℕ} (hst : s < t) (htp : t < 2 ^ p) {i : ℕ} (hi : i < t) :
    HvdH.vsz (Val.int (((egLam s t i : ℕ) : ℤ))) ≤ buSL p := by
  rw [Work.Fx.vsz_int]
  have h1 := isz_egLam_le hst htp hi
  simp only [buSL]
  omega

lemma mem_buSelKeys {s t : ℕ} {x : Val} (hx : x ∈ buSelKeys s t) :
    ∃ i : Fin t, x = Val.int (((egLam s t (i : ℕ) : ℕ) : ℤ)) := by
  rw [buSelKeys, List.mem_map] at hx
  obtain ⟨k, hk, hkx⟩ := hx
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hk
  exact ⟨i, by rw [← hkx, ← hi]⟩

lemma mem_u_getD {u : List (ℤ × ℤ)} {x : Val} (hx : x ∈ u.map cfxVal) :
    ∃ i, i < u.length ∧ x = cfxVal (u.getD i (0, 0)) := by
  obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hx
  obtain ⟨i, hi, hiz⟩ := List.mem_iff_getElem.mp hz
  exact ⟨i, hi, by rw [← hzx, ← hiz, List.getD_eq_getElem u (0, 0) hi]⟩

lemma mem_buSelRecs {s t : ℕ} {u : List (ℤ × ℤ)} (hu : u.length = t) {x : Val}
    (hx : x ∈ buSelRecs s t u) :
    ∃ i, i < t ∧ x = Val.cons (Val.int (((egLam s t i : ℕ) : ℤ))) (cfxVal (u.getD i (0, 0))) := by
  have h1 : buSelRecs s t u = buSelRecs' s t u := (buSelRecsSpec s t u hu).1
  rw [h1, buSelRecs', List.mem_ofFn] at hx
  obtain ⟨i, hi⟩ := hx
  exact ⟨i, i.isLt, hi.symm⟩

lemma vsz_mem_buSelRecs {s t p : ℕ} {u : List (ℤ × ℤ)} (hu : u.length = t) (hst : s < t)
    (htp : t < 2 ^ p) (hV : buInV (2 ^ p) u) {x : Val} (hx : x ∈ buSelRecs s t u) :
    HvdH.vsz x ≤ buSL p := by
  obtain ⟨i, hi, rfl⟩ := mem_buSelRecs hu hx
  have hk := isz_egLam_le hst htp hi
  have hzu : u.getD i (0, 0) ∈ u := by
    rw [List.getD_eq_getElem u (0, 0) (by omega : i < u.length)]
    exact List.mem_iff_getElem.mpr ⟨i, by omega, rfl⟩
  have hz := hV _ hzu
  have hz1 := isz_fst_le hz
  have hz2 := isz_snd_le hz
  have hc : HvdH.vsz (cfxVal (u.getD i (0, 0))) ≤ 2 * p + 7 := by
    rw [Work.Fx.vsz_cfxVal]; omega
  rw [Work.Fx.vsz_cons, Work.Fx.vsz_int]
  simp only [buSL] at *
  omega

lemma vsz_buKeysT_le {s t p : ℕ} (hst : s < t) (htp : t < 2 ^ p) :
    HvdH.vsz (buKeysT s t) ≤ (t + 1) * (buSL p + 1) := by
  rw [buKeysT_eq]
  have h := Work.Resample.vsz_ofList_le (l := buSelKeys s t) (B := buSL p)
    (fun x hx => by
      obtain ⟨i, rfl⟩ := mem_buSelKeys hx
      exact vsz_key_le hst htp i.isLt)
  rwa [buSelKeys, List.length_map, List.length_ofFn] at h

lemma vsz_cvecVal_le {p : ℕ} {u : List (ℤ × ℤ)} (hV : buInV (2 ^ p) u) :
    HvdH.vsz (cvecVal u) ≤ (u.length + 1) * (buSL p + 1) := by
  have h := Work.Resample.vsz_ofList_le (l := u.map cfxVal) (B := buSL p) (fun x hx => by
    obtain ⟨i, hi, rfl⟩ := mem_u_getD hx
    refine vsz_cfxVal_le_sel (hV _ ?_)
    rw [List.getD_eq_getElem u (0, 0) hi]
    exact List.mem_iff_getElem.mpr ⟨i, hi, rfl⟩)
  simpa [HvdH.cvecVal, List.length_map] using h

lemma vsz_buSelRecs_le {s t p : ℕ} {u : List (ℤ × ℤ)} (hu : u.length = t) (hst : s < t)
    (htp : t < 2 ^ p) (hV : buInV (2 ^ p) u) :
    HvdH.vsz (ofList (buSelRecs s t u)) ≤ (t + 1) * (buSL p + 1) := by
  have h := Work.Resample.vsz_ofList_le (l := buSelRecs s t u) (B := buSL p)
    (fun x hx => vsz_mem_buSelRecs hu hst htp hV hx)
  rwa [(buSelRecsSpec s t u hu).2.2.2] at h

lemma vsz_ofList_ys_le {s t p : ℕ} {u : List (ℤ × ℤ)} (hu : u.length = t) (hst : s < t)
    (htp : t < 2 ^ p) (hV : buInV (2 ^ p) u) {ys : List Val}
    (hperm : ys.Perm (buSelRecs s t u)) :
    HvdH.vsz (ofList ys) ≤ (t + 1) * (buSL p + 1) := by
  have h := Work.Resample.vsz_ofList_le (l := ys) (B := buSL p) (fun x hx =>
    vsz_mem_buSelRecs hu hst htp hV ((hperm.mem_iff).mp hx))
  have hlen : ys.length = t := by
    rw [List.Perm.length_eq hperm, (buSelRecsSpec s t u hu).2.2.2]
  rwa [hlen] at h

/-! ## cost arithmetic -/

theorem stageLe {S p t X : ℕ} (hX : X ≤ 400 * S * ((t + 1) * (buSL p + 1) * (p + 1))) :
    X ≤ 2 ^ 20 * S * (t + 1) * (p + 1) * (p + 1) := by
  have hL : buSL p + 1 ≤ 13 * (p + 1) := by simp only [buSL]; omega
  have h1 : (t + 1) * (buSL p + 1) * (p + 1) ≤ (t + 1) * (13 * (p + 1)) * (p + 1) := by
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hL)
  have h2 : 400 * S * ((t + 1) * (13 * (p + 1)) * (p + 1))
      = 5200 * S * (t + 1) * (p + 1) * (p + 1) := by ring
  have h3 : 5200 * S * (t + 1) * (p + 1) * (p + 1)
      ≤ 2 ^ 20 * S * (t + 1) * (p + 1) * (p + 1) := by
    refine Nat.mul_le_mul_right _ ?_
    refine Nat.mul_le_mul_right _ ?_
    refine Nat.mul_le_mul_right _ ?_
    exact Nat.mul_le_mul_right _ (by norm_num : (5200 : ℕ) ≤ 2 ^ 20)
  calc X ≤ 400 * S * ((t + 1) * (buSL p + 1) * (p + 1)) := hX
    _ ≤ 400 * S * ((t + 1) * (13 * (p + 1)) * (p + 1)) := Nat.mul_le_mul_left _ h1
    _ = 5200 * S * (t + 1) * (p + 1) * (p + 1) := h2
    _ ≤ 2 ^ 20 * S * (t + 1) * (p + 1) * (p + 1) := h3

theorem add23_le_two_pow {n : ℕ} (hn : 40 ≤ n) : n + 23 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have h24 : 24 ≤ 2 ^ n := by
        have h1 : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        norm_num at h1
        omega
      calc n + 1 + 23 = n + 24 := by omega
        _ ≤ 2 ^ n + 2 ^ n := by omega
        _ = 2 ^ (n + 1) := by ring

theorem finalLe {S p t : ℕ} (hS : 40 ≤ S) :
    7 * (2 ^ 20 * S * (t + 1) * (p + 1) * (p + 1))
      ≤ 2 ^ (2 ^ S + 80) * (t + 1) * (p + 1) * (p + 1) := by
  have hpow : 7 * 2 ^ 20 * S ≤ 2 ^ (2 ^ S + 80) := by
    have h1 : 7 * 2 ^ 20 * S ≤ 2 ^ 23 * S := Nat.mul_le_mul_right _ (by norm_num : (7 * 2 ^ 20 : ℕ) ≤ 2 ^ 23)
    have h2 : 2 ^ 23 * S ≤ 2 ^ 23 * 2 ^ S := Nat.mul_le_mul_left _ (le_of_lt (Nat.lt_two_pow_self))
    have h3 : 2 ^ 23 * 2 ^ S = 2 ^ (S + 23) := by rw [← pow_add]; ring_nf
    have h4 : 2 ^ (S + 23) ≤ 2 ^ (2 ^ S + 80) := by
      apply Nat.pow_le_pow_right (by norm_num)
      have h5 := add23_le_two_pow hS
      omega
    exact le_trans h1 (le_trans h2 (le_trans (le_of_eq h3) h4))
  calc 7 * (2 ^ 20 * S * (t + 1) * (p + 1) * (p + 1))
      = 7 * 2 ^ 20 * S * ((t + 1) * (p + 1) * (p + 1)) := by ring
    _ ≤ 2 ^ (2 ^ S + 80) * ((t + 1) * (p + 1) * (p + 1)) := Nat.mul_le_mul_right _ hpow
    _ = 2 ^ (2 ^ S + 80) * (t + 1) * (p + 1) * (p + 1) := by ring

theorem le_mul_of_one_le_nat (a b : ℕ) (h : 1 ≤ b) : a ≤ a * b := by
  calc a = a * 1 := by ring
    _ ≤ a * b := Nat.mul_le_mul_left _ h

theorem le_mul_assoc_nat (a b c : ℕ) (h : 1 ≤ c) : a * b ≤ a * (b * c) := by
  rw [← Nat.mul_assoc]
  exact le_mul_of_one_le_nat (a * b) c h

theorem coef_le {S Y c : ℕ} (h : c * S ≤ 400 * S) : c * S * Y ≤ 400 * S * Y :=
  Nat.mul_le_mul_right Y h

theorem one_le_mul_tl (t p : ℕ) : 1 ≤ (t + 1) * (buSL p + 1) :=
  Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos t) (Nat.succ_pos (buSL p)))

theorem buQWsel (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) (FL : HvdH.FxLib) :
    ∃ (q : HvdH.Cmd) (Kc : ℕ),
    ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) (htp : t < 2 ^ p)
      (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → Kc * p < N →
    HvdH.WordR main q
      (fun vs => ∃ (u : List (ℤ × ℤ)) (rest : List HvdH.Val),
        vs = HvdH.cvecVal u :: Work.Resample.buKeysT s t :: HvdH.Val.int (s : ℤ) :: rest ∧
        u.length = t ∧ Work.Resample.buInV (2 ^ p) u)
      (fun vs out => ∃ (u : List (ℤ × ℤ)) (rest : List HvdH.Val) (v : List (ℤ × ℤ)),
        vs = HvdH.cvecVal u :: Work.Resample.buKeysT s t :: HvdH.Val.int (s : ℤ) :: rest ∧
        out = HvdH.cvecVal v :: rest ∧ v = Work.Resample.buSelL s t u ∧ v.length = s ∧
        Work.Resample.buInV (2 ^ (p - 1) + 2) v)
      (fun _ => Kc * (t + 1) * (p + 1) * (p + 1)) := by
  obtain ⟨swapprog, Ksw, hsw⟩ := KL.swap
  obtain ⟨zipprog, Kz, hzip⟩ := buZipConsWord KL
  obtain ⟨sortprog, Ksrt, hsortW⟩ := LL.sortByKey
  obtain ⟨rollprog, Krl, hroll⟩ := KL.roll
  obtain ⟨takeprog, Ktk, htake⟩ := LL.take
  obtain ⟨mlcomb, Kml, hml⟩ := KL.mapList
  obtain ⟨elemprog, Kel, hele⟩ := buSelElemWord KL IL
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ, S = Ksw + Kz + Ksrt + Krl + Ktk + Kml + Kel + 50 := ⟨_, rfl⟩
  refine ⟨.seq swapprog (.seq zipprog (.seq sortprog (.seq (rollprog 1) (.seq takeprog (mlcomb elemprog))))),
    2 ^ (2 ^ S + 80), ?_⟩
  intro p α s t hs hst hcop htp main N Cm hmon hmul hN
  intro vs hPre s0 R hR
  obtain ⟨u, rest, hvs, hulen, hV⟩ := hPre
  subst hvs
  have hKswS : Ksw ≤ S := by omega
  have hKzS : Kz ≤ S := by omega
  have hKsrtS : Ksrt ≤ S := by omega
  have hKrlS : Krl ≤ S := by omega
  have hKtkS : Ktk ≤ S := by omega
  have hKmlS : Kml ≤ S := by omega
  have hKelS : Kel ≤ S := by omega
  -- sizes
  have hsz_cvec : HvdH.vsz (cvecVal u) ≤ (t + 1) * (buSL p + 1) := by
    have h := vsz_cvecVal_le (p := p) hV
    rwa [hulen] at h
  have hsz_keys : HvdH.vsz (buKeysT s t) ≤ (t + 1) * (buSL p + 1) := vsz_buKeysT_le hst htp
  have hsz_recs : HvdH.vsz (ofList (buSelRecs s t u)) ≤ (t + 1) * (buSL p + 1) :=
    vsz_buSelRecs_le hulen hst htp hV
  -- stage 1 : swap
  have h1 : WS main swapprog [cvecVal u, buKeysT s t, .int (s:ℤ)]
      (fun Bv => Bv = [buKeysT s t, cvecVal u, .int (s:ℤ)])
      (Ksw * (HvdH.vsz (cvecVal u) + HvdH.vsz (buKeysT s t) + 1)) :=
    WS.ofPipe KL (by
      have h := Pipe.appendTail [HvdH.Val.int (s:ℤ)] (Pipe.swap main hsw (cvecVal u) (buKeysT s t))
      simpa only [List.cons_append, List.nil_append] using h)
  have hc1 : Ksw * (HvdH.vsz (cvecVal u) + HvdH.vsz (buKeysT s t) + 1)
      ≤ 400 * S * ((t + 1) * (buSL p + 1) * (p + 1)) := by
    have hX : HvdH.vsz (cvecVal u) + HvdH.vsz (buKeysT s t) + 1 ≤ 3 * ((t + 1) * (buSL p + 1)) := by
      have hpos : 1 ≤ (t + 1) * (buSL p + 1) := one_le_mul_tl t p
      omega
    calc Ksw * (HvdH.vsz (cvecVal u) + HvdH.vsz (buKeysT s t) + 1)
        ≤ Ksw * (3 * ((t + 1) * (buSL p + 1))) := Nat.mul_le_mul_left _ hX
      _ = 3 * Ksw * ((t + 1) * (buSL p + 1)) := by ring
      _ ≤ 3 * S * ((t + 1) * (buSL p + 1)) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 hKswS)
      _ ≤ 3 * S * ((t + 1) * (buSL p + 1) * (p + 1)) :=
          le_mul_assoc_nat (3 * S) ((t + 1) * (buSL p + 1)) (p + 1) (by omega)
      _ ≤ 400 * S * ((t + 1) * (buSL p + 1) * (p + 1)) := by
          exact coef_le (S := S) (Y := (t + 1) * (buSL p + 1) * (p + 1)) (by omega : 3 * S ≤ 400 * S)
  -- stage 2 : zip
  have hlenZ : (buSelKeys s t).length = (u.map cfxVal).length := by
    simp [buSelKeys, List.length_map, List.length_ofFn, hulen]
  have hszZ : ∀ x ∈ buSelKeys s t ++ u.map cfxVal, HvdH.vsz x ≤ buSL p := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨i, rfl⟩ := mem_buSelKeys hx
      exact vsz_key_le hst htp i.isLt
    · obtain ⟨i, hi, rfl⟩ := mem_u_getD hx
      refine vsz_cfxVal_le_sel (hV _ ?_)
      rw [List.getD_eq_getElem u (0, 0) hi]
      exact List.mem_iff_getElem.mpr ⟨i, hi, rfl⟩
  have h2 : WS main zipprog [buKeysT s t, cvecVal u, .int (s:ℤ)]
      (fun Bv => Bv = [ofList (buSelRecs s t u), .int (s:ℤ)])
      (Kz * (t + 1) * (buSL p + 1)) := by
    have hpipe : Pipe main zipprog [ofList (buSelKeys s t), ofList (u.map cfxVal)]
        [ofList (buSelRecs s t u)] (Kz * (t + 1) * (buSL p + 1)) := by
      have hzw := hzip main (buSL p) (buSelKeys s t) (u.map cfxVal) hlenZ hszZ
      have hlen2 : (buSelKeys s t).length = t := by simp [buSelKeys, List.length_map, List.length_ofFn]
      rw [hlen2] at hzw
      exact Pipe.ofWordR_auInnerElem (main := main) (prog := zipprog)
        (A := [ofList (buSelKeys s t), ofList (u.map cfxVal)]) (B := [ofList (buSelRecs s t u)])
        (c := Kz * (t + 1) * (buSL p + 1)) hzw
    refine WS.ofPipe KL ?_
    have h := Pipe.appendTail [HvdH.Val.int (s:ℤ)] hpipe
    simpa only [buKeysT_eq, HvdH.cvecVal, List.cons_append, List.nil_append] using h
  have hc2 : Kz * (t + 1) * (buSL p + 1) ≤ 400 * S * ((t + 1) * (buSL p + 1) * (p + 1)) := by
    calc Kz * (t + 1) * (buSL p + 1) ≤ S * (t + 1) * (buSL p + 1) :=
          Nat.mul_le_mul_right (buSL p + 1) (Nat.mul_le_mul_right (t + 1) hKzS)
      _ = S * ((t + 1) * (buSL p + 1)) := by ring
      _ ≤ S * ((t + 1) * (buSL p + 1) * (p + 1)) :=
          le_mul_assoc_nat S ((t + 1) * (buSL p + 1)) (p + 1) (by omega)
      _ ≤ 400 * S * ((t + 1) * (buSL p + 1) * (p + 1)) :=
          Nat.mul_le_mul_right ((t + 1) * (buSL p + 1) * (p + 1)) (by omega : S ≤ 400 * S)
  -- stage 3 : sort
  have hnodup : ((buSelRecs s t u).map HvdH.pairKey).Nodup := by
    rw [(buSelRecsSpec s t u hulen).2.2.1]
    exact (buKeysSpec s t hs hst hcop).2.2
  have hshape : ∀ x ∈ buSelRecs s t u, ∃ (k : ℕ) (v : HvdH.Val), x = .cons (.int k) v := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_buSelRecs hulen hx
    exact ⟨egLam s t i, cfxVal (u.getD i (0, 0)), rfl⟩
  have h3 : WS main sortprog [ofList (buSelRecs s t u), .int (s:ℤ)]
      (fun Bv => ∃ ys : List HvdH.Val, ys.Perm (buSelRecs s t u) ∧
        ys.Pairwise (fun a b => HvdH.pairKey a < HvdH.pairKey b) ∧ Bv = [ofList ys, .int (s:ℤ)])
      (Ksrt * (HvdH.vsz (ofList (buSelRecs s t u)) + 1) * ((buSelRecs s t u).length.size + 1)) := by
    intro r vs hvs st Rh hRh
    have hv : vs = ofList (buSelRecs s t u) :: ([.int (s:ℤ)] ++ r) := by rw [hvs]; rfl
    obtain ⟨out, st', n, ⟨rest', ys, hvs', hout', hperm, hsort'⟩, hev, hn, hstk, hoth⟩ :=
      hsortW main (buSelRecs s t u) hshape hnodup vs ⟨[.int (s:ℤ)] ++ r, hv⟩ st Rh hRh
    have hrest : rest' = [.int (s:ℤ)] ++ r := (List.cons.inj (hvs'.symm.trans hv)).2
    have hout1 : out = [ofList ys, .int (s:ℤ)] ++ r := by
      rw [hout', hrest]; rfl
    exact ⟨out, st', n, ⟨[ofList ys, .int (s:ℤ)], ⟨ys, hperm, hsort', rfl⟩, hout1⟩, hev, hn, hstk, hoth⟩
  have hc3 : Ksrt * (HvdH.vsz (ofList (buSelRecs s t u)) + 1) * ((buSelRecs s t u).length.size + 1)
      ≤ 400 * S * ((t + 1) * (buSL p + 1) * (p + 1)) := by
    have h1 : HvdH.vsz (ofList (buSelRecs s t u)) + 1 ≤ 2 * ((t + 1) * (buSL p + 1)) := by
      have hpos : 1 ≤ (t + 1) * (buSL p + 1) := one_le_mul_tl t p
      omega
    have h2 : (buSelRecs s t u).length.size + 1 ≤ p + 1 := by
      rw [(buSelRecsSpec s t u hulen).2.2.2]
      have h3 := Nat.size_le.mpr htp
      omega
    calc Ksrt * (HvdH.vsz (ofList (buSelRecs s t u)) + 1) * ((buSelRecs s t u).length.size + 1)
        ≤ Ksrt * (2 * ((t + 1) * (buSL p + 1))) * (p + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left Ksrt h1) h2
      _ = 2 * Ksrt * ((t + 1) * (buSL p + 1)) * (p + 1) := by ring
      _ ≤ 2 * S * ((t + 1) * (buSL p + 1)) * (p + 1) :=
          Nat.mul_le_mul_right (p + 1) (Nat.mul_le_mul_right ((t + 1) * (buSL p + 1))
            (Nat.mul_le_mul_left 2 hKsrtS))
      _ = 2 * S * ((t + 1) * (buSL p + 1) * (p + 1)) := by ring
      _ ≤ 400 * S * ((t + 1) * (buSL p + 1) * (p + 1)) :=
          coef_le (S := S) (Y := (t + 1) * (buSL p + 1) * (p + 1)) (by omega : 2 * S ≤ 400 * S)
  -- stage 4 : roll + take + mapList, for every sorted list `ys`
  have h4 : ∀ Bv, (∃ ys : List HvdH.Val, ys.Perm (buSelRecs s t u) ∧
        ys.Pairwise (fun a b => HvdH.pairKey a < HvdH.pairKey b) ∧ Bv = [ofList ys, .int (s:ℤ)]) →
      WS main (.seq (rollprog 1) (.seq takeprog (mlcomb elemprog))) Bv
        (fun Dv => ∃ ys : List HvdH.Val, ys.Perm (buSelRecs s t u) ∧
          ys.Pairwise (fun a b => HvdH.pairKey a < HvdH.pairKey b) ∧
          Dv = [ofList ((ys.take s).map buSelElem)])
        (4 * (2 ^ 20 * S * (t + 1) * (p + 1) * (p + 1))) := by
    intro Bv hBv
    obtain ⟨ys, hperm, hsortp, rfl⟩ := hBv
    have hsz_ys : HvdH.vsz (ofList ys) ≤ (t + 1) * (buSL p + 1) :=
      vsz_ofList_ys_le hulen hst htp hV hperm
    -- the roll
    have hrl : WS main (rollprog 1) [ofList ys, .int (s:ℤ)] (fun Bv => Bv = [.int (s:ℤ), ofList ys])
        (Krl * 2 * (HvdH.vsz (ofList ys) + HvdH.isz (s:ℤ) + 1)) := by
      intro r vs hvs st Rh hRh
      obtain ⟨out, st', n, hout, hev, hn, hstk, hoth⟩ :=
        hroll main 1 vs (by rw [hvs]; simp) st Rh hRh
      have hgde := getD_eraseIdx_append (l := [ofList ys, .int (s:ℤ)]) (rest := r) (k := 1) (by simp)
      have hout1 : out = [.int (s:ℤ), ofList ys] ++ r := by
        rw [hout, hvs, hgde]; simp
      have hn' : n ≤ Krl * 2 * (HvdH.vsz (ofList ys) + HvdH.isz (s:ℤ) + 1) := by
        rw [hvs] at hn
        dsimp only at hn
        have hcalc : (List.map HvdH.vsz (List.take (1 + 1) ([ofList ys, .int (s:ℤ)] ++ r))).sum + 1
            = HvdH.vsz (ofList ys) + HvdH.isz (s:ℤ) + 1 := by
          have htake : List.take (1 + 1) ([ofList ys, .int (s:ℤ)] ++ r) = [ofList ys, .int (s:ℤ)] := rfl
          rw [htake, List.map_cons, List.map_cons, List.map_nil, List.sum_cons, List.sum_cons,
            List.sum_nil, Work.Fx.vsz_int]
          ring
        rw [hcalc] at hn
        exact hn
      exact ⟨out, st', n, ⟨[.int (s:ℤ), ofList ys], rfl, hout1⟩, hev, hn', hstk, hoth⟩
    -- the take
    have htk : WS main takeprog [.int (s:ℤ), ofList ys] (fun Bv => Bv = [ofList (ys.take s)])
        (Ktk * (HvdH.vsz (ofList ys) + HvdH.isz (s:ℤ) + 1)) := by
      intro r vs hvs st Rh hRh
      obtain ⟨out, st', n, ⟨rest', hvs', hout'⟩, hev, hn, hstk, hoth⟩ :=
        htake main s ys vs ⟨r, by rw [hvs]; rfl⟩ st Rh hRh
      have hrest : rest' = r := by
        have h1 : HvdH.Val.int (s:ℤ) :: ofList ys :: rest'
            = HvdH.Val.int (s:ℤ) :: ofList ys :: r := by
          rw [← hvs', hvs]; rfl
        exact (List.cons.inj (List.cons.inj h1).2).2
      have hout1 : out = [ofList (ys.take s)] ++ r := by
        rw [hout', hrest]; rfl
      exact ⟨out, st', n, ⟨[ofList (ys.take s)], rfl, hout1⟩, hev, hn, hstk, hoth⟩
    -- the per-element word
    have hElem : ∀ x ∈ ys.take s, Pipe main elemprog [x] [buSelElem x] (Kel * buSL p) := by
      intro x hx
      obtain ⟨i, hi, hxeq⟩ := mem_buSelRecs hulen ((hperm.mem_iff).mp (List.mem_of_mem_take hx))
      intro r vs hvs st Rh hRh
      have hvs' : vs = HvdH.Val.cons (HvdH.Val.int ((egLam s t i : ℕ) : ℤ))
          (cfxVal (u.getD i (0, 0))) :: r := by
        rw [hvs, hxeq]; rfl
      obtain ⟨out, st', n, ⟨_, hout⟩, hev, hn, hstk, hoth⟩ :=
        hele main (((egLam s t i : ℕ) : ℤ)) (u.getD i (0, 0)) r vs hvs' st Rh hRh
      have hzu : u.getD i (0, 0) ∈ u := by
        rw [List.getD_eq_getElem u (0, 0) (by omega : i < u.length)]
        exact List.mem_iff_getElem.mpr ⟨i, by omega, rfl⟩
      have hk := isz_egLam_le hst htp hi
      have hz := hV _ hzu
      have hz1 := isz_fst_le hz
      have hz2 := isz_snd_le hz
      have hn' : n ≤ Kel * buSL p := by
        have hinner : HvdH.isz (((egLam s t i : ℕ) : ℤ)) + HvdH.isz (u.getD i (0, 0)).1
            + HvdH.isz (u.getD i (0, 0)).2 + 2 ≤ buSL p := by
          simp only [buSL]; omega
        exact le_trans hn (Nat.mul_le_mul_left _ hinner)
      have hP : out = [buSelElem x] ++ r := by
        rw [hout, hxeq, buSelElem_apply]
        rfl
      exact ⟨out, st', n, hP, hev, hn', hstk, hoth⟩
    have hxL : ∀ x ∈ ys.take s, HvdH.vsz x ≤ buSL p := fun x hx =>
      vsz_mem_buSelRecs hulen hst htp hV ((hperm.mem_iff).mp (List.mem_of_mem_take hx))
    have hfL : ∀ x ∈ ys.take s, HvdH.vsz (buSelElem x) ≤ buSL p := by
      intro x hx
      obtain ⟨i, hi, hxeq⟩ := mem_buSelRecs hulen ((hperm.mem_iff).mp (List.mem_of_mem_take hx))
      subst hxeq
      have hzu : u.getD i (0, 0) ∈ u := by
        rw [List.getD_eq_getElem u (0, 0) (by omega : i < u.length)]
        exact List.mem_iff_getElem.mpr ⟨i, by omega, rfl⟩
      have hz := hV _ hzu
      have hz1 := isz_fst_le hz
      have hz2 := isz_snd_le hz
      rw [buSelElem_apply, Work.Fx.vsz_cfxVal]
      show HvdH.isz (Int.tdiv (u.getD i (0, 0)).1 2)
          + HvdH.isz (Int.tdiv (u.getD i (0, 0)).2 2) + 1 ≤ buSL p
      have e1 := Work.Fx.isz_tdiv_le (u.getD i (0, 0)).1 2
      have e2 := Work.Fx.isz_tdiv_le (u.getD i (0, 0)).2 2
      simp only [buSL]
      omega
    have hmap : WS main (mlcomb elemprog) [ofList (ys.take s)]
        (fun Bv => Bv = [ofList ((ys.take s).map buSelElem)])
        ((ys.take s).length * (Kel * buSL p + Kml * (buSL p + 1)) + Kml) := by
      refine WS.ofPipe KL ?_
      have h := Pipe.mapListFun (rest := []) (xs := ys.take s) (F := buSelElem)
        (c := Kel * buSL p) (L := buSL p) hml hElem hxL hfL
      simpa using h
    have hc4 : (ys.take s).length * (Kel * buSL p + Kml * (buSL p + 1)) + Kml
        ≤ 400 * S * ((t + 1) * (buSL p + 1) * (p + 1)) := by
      have hlen : (ys.take s).length ≤ t + 1 := by
        have h1 := List.length_take_le s ys
        omega
      have hpos1 : 1 ≤ (t + 1) * (buSL p + 1) := one_le_mul_tl t p
      have hmid : Kel * buSL p + Kml * (buSL p + 1) ≤ 2 * S * (buSL p + 1) := by
        have ha : Kel * buSL p ≤ S * (buSL p + 1) := by
          calc Kel * buSL p ≤ S * buSL p := Nat.mul_le_mul_right _ hKelS
            _ ≤ S * (buSL p + 1) := Nat.mul_le_mul_left _ (by omega)
        have hb : Kml * (buSL p + 1) ≤ S * (buSL p + 1) := Nat.mul_le_mul_right _ hKmlS
        calc Kel * buSL p + Kml * (buSL p + 1)
            ≤ S * (buSL p + 1) + S * (buSL p + 1) := add_le_add ha hb
          _ = 2 * S * (buSL p + 1) := by ring
      have h1 : (ys.take s).length * (Kel * buSL p + Kml * (buSL p + 1))
          ≤ (t + 1) * (2 * S * (buSL p + 1)) := Nat.mul_le_mul hlen hmid
      have h2 : (t + 1) * (2 * S * (buSL p + 1)) + Kml ≤ 3 * S * ((t + 1) * (buSL p + 1)) := by
        have hh : Kml ≤ S * ((t + 1) * (buSL p + 1)) := by
          calc Kml ≤ S := hKmlS
            _ = S * 1 := by ring
            _ ≤ S * ((t + 1) * (buSL p + 1)) := Nat.mul_le_mul_left _ hpos1
        calc (t + 1) * (2 * S * (buSL p + 1)) + Kml
            ≤ 2 * S * ((t + 1) * (buSL p + 1)) + S * ((t + 1) * (buSL p + 1)) :=
              add_le_add (le_of_eq (by ring)) hh
          _ = 3 * S * ((t + 1) * (buSL p + 1)) := by ring
      calc (ys.take s).length * (Kel * buSL p + Kml * (buSL p + 1)) + Kml
          ≤ (t + 1) * (2 * S * (buSL p + 1)) + Kml := Nat.add_le_add_right h1 Kml
        _ ≤ 3 * S * ((t + 1) * (buSL p + 1)) := h2
        _ ≤ 3 * S * ((t + 1) * (buSL p + 1) * (p + 1)) :=
            Nat.mul_le_mul_left _ (le_mul_of_one_le_nat _ _ (by omega : 1 ≤ p + 1))
        _ ≤ 400 * S * ((t + 1) * (buSL p + 1) * (p + 1)) :=
            coef_le (S := S) (Y := (t + 1) * (buSL p + 1) * (p + 1)) (by omega : 3 * S ≤ 400 * S)
    have hcrl : Krl * 2 * (HvdH.vsz (ofList ys) + HvdH.isz (s:ℤ) + 1)
        ≤ 400 * S * ((t + 1) * (buSL p + 1) * (p + 1)) := by
      have h1 : HvdH.vsz (ofList ys) + HvdH.isz (s:ℤ) + 1 ≤ 3 * ((t + 1) * (buSL p + 1)) := by
        have hpos : 1 ≤ (t + 1) * (buSL p + 1) := one_le_mul_tl t p
        have hisz : HvdH.isz (s:ℤ) ≤ (t + 1) * (buSL p + 1) := by
          have hsz1 : (s:ℤ).natAbs ≤ 2 ^ p := by rw [Int.natAbs_natCast]; omega
          have hsz2 : (s:ℤ).natAbs.size ≤ p + 1 := Nat.size_le.mpr (by
            calc (s:ℤ).natAbs ≤ 2 ^ p := hsz1
              _ < 2 ^ (p + 1) := Nat.pow_lt_pow_succ (by norm_num : 1 < 2))
          have hsz3 : HvdH.isz (s:ℤ) ≤ buSL p := by simp only [HvdH.isz, buSL]; omega
          have hsz4 : buSL p ≤ (t + 1) * (buSL p + 1) := by
            calc buSL p = 1 * buSL p := by ring
              _ ≤ (t + 1) * (buSL p + 1) :=
                  Nat.mul_le_mul (by omega : 1 ≤ t + 1) (by omega : buSL p ≤ buSL p + 1)
          exact le_trans hsz3 hsz4
        omega
      calc Krl * 2 * (HvdH.vsz (ofList ys) + HvdH.isz (s:ℤ) + 1)
          ≤ Krl * 2 * (3 * ((t + 1) * (buSL p + 1))) := Nat.mul_le_mul_left _ h1
        _ = 6 * Krl * ((t + 1) * (buSL p + 1)) := by ring
        _ ≤ 6 * S * ((t + 1) * (buSL p + 1)) :=
            Nat.mul_le_mul_right ((t + 1) * (buSL p + 1)) (Nat.mul_le_mul_left 6 hKrlS)
        _ ≤ 6 * S * ((t + 1) * (buSL p + 1) * (p + 1)) :=
            le_mul_assoc_nat (6 * S) ((t + 1) * (buSL p + 1)) (p + 1) (by omega)
        _ ≤ 400 * S * ((t + 1) * (buSL p + 1) * (p + 1)) :=
            coef_le (S := S) (Y := (t + 1) * (buSL p + 1) * (p + 1)) (by omega : 6 * S ≤ 400 * S)
    have hctk : Ktk * (HvdH.vsz (ofList ys) + HvdH.isz (s:ℤ) + 1)
        ≤ 400 * S * ((t + 1) * (buSL p + 1) * (p + 1)) := by
      have h1 : HvdH.vsz (ofList ys) + HvdH.isz (s:ℤ) + 1 ≤ 3 * ((t + 1) * (buSL p + 1)) := by
        have hpos : 1 ≤ (t + 1) * (buSL p + 1) := one_le_mul_tl t p
        have hisz : HvdH.isz (s:ℤ) ≤ (t + 1) * (buSL p + 1) := by
          have hsz1 : (s:ℤ).natAbs ≤ 2 ^ p := by rw [Int.natAbs_natCast]; omega
          have hsz2 : (s:ℤ).natAbs.size ≤ p + 1 := Nat.size_le.mpr (by
            calc (s:ℤ).natAbs ≤ 2 ^ p := hsz1
              _ < 2 ^ (p + 1) := Nat.pow_lt_pow_succ (by norm_num : 1 < 2))
          have hsz3 : HvdH.isz (s:ℤ) ≤ buSL p := by simp only [HvdH.isz, buSL]; omega
          have hsz4 : buSL p ≤ (t + 1) * (buSL p + 1) := by
            calc buSL p = 1 * buSL p := by ring
              _ ≤ (t + 1) * (buSL p + 1) :=
                  Nat.mul_le_mul (by omega : 1 ≤ t + 1) (by omega : buSL p ≤ buSL p + 1)
          exact le_trans hsz3 hsz4
        omega
      calc Ktk * (HvdH.vsz (ofList ys) + HvdH.isz (s:ℤ) + 1)
          ≤ Ktk * (3 * ((t + 1) * (buSL p + 1))) := Nat.mul_le_mul_left _ h1
        _ = 3 * Ktk * ((t + 1) * (buSL p + 1)) := by ring
        _ ≤ 3 * S * ((t + 1) * (buSL p + 1)) :=
            Nat.mul_le_mul_right ((t + 1) * (buSL p + 1)) (Nat.mul_le_mul_left 3 hKtkS)
        _ ≤ 3 * S * ((t + 1) * (buSL p + 1) * (p + 1)) :=
            le_mul_assoc_nat (3 * S) ((t + 1) * (buSL p + 1)) (p + 1) (by omega)
        _ ≤ 400 * S * ((t + 1) * (buSL p + 1) * (p + 1)) :=
            coef_le (S := S) (Y := (t + 1) * (buSL p + 1) * (p + 1)) (by omega : 3 * S ≤ 400 * S)
    have hinner : WS main (.seq takeprog (mlcomb elemprog)) [.int (s:ℤ), ofList ys]
        (fun Bv => Bv = [ofList ((ys.take s).map buSelElem)])
        ((Ktk * (HvdH.vsz (ofList ys) + HvdH.isz (s:ℤ) + 1))
          + ((ys.take s).length * (Kel * buSL p + Kml * (buSL p + 1)) + Kml)) :=
      WS.comp KL htk (fun Bv hB => by rw [hB]; exact hmap)
    have hchain : WS main (.seq (rollprog 1) (.seq takeprog (mlcomb elemprog))) [ofList ys, .int (s:ℤ)]
        (fun Bv => Bv = [ofList ((ys.take s).map buSelElem)])
        ((Krl * 2 * (HvdH.vsz (ofList ys) + HvdH.isz (s:ℤ) + 1))
          + ((Ktk * (HvdH.vsz (ofList ys) + HvdH.isz (s:ℤ) + 1))
            + ((ys.take s).length * (Kel * buSL p + Kml * (buSL p + 1)) + Kml))) :=
      WS.comp KL hrl (fun Bv hB => by rw [hB]; exact hinner)
    refine WS.mono KL (WS.cost KL hchain ?_) ?_
    · have h3 : (Krl * 2 * (HvdH.vsz (ofList ys) + HvdH.isz (s:ℤ) + 1))
            + ((Ktk * (HvdH.vsz (ofList ys) + HvdH.isz (s:ℤ) + 1))
              + ((ys.take s).length * (Kel * buSL p + Kml * (buSL p + 1)) + Kml))
          ≤ 1200 * S * ((t + 1) * (buSL p + 1) * (p + 1)) := by
        have hsum3 := add_le_add hcrl (add_le_add hctk hc4)
        calc (Krl * 2 * (HvdH.vsz (ofList ys) + HvdH.isz (s:ℤ) + 1))
              + ((Ktk * (HvdH.vsz (ofList ys) + HvdH.isz (s:ℤ) + 1))
                + ((ys.take s).length * (Kel * buSL p + Kml * (buSL p + 1)) + Kml))
            ≤ 400 * S * ((t + 1) * (buSL p + 1) * (p + 1))
              + (400 * S * ((t + 1) * (buSL p + 1) * (p + 1))
                + 400 * S * ((t + 1) * (buSL p + 1) * (p + 1))) := hsum3
          _ = 1200 * S * ((t + 1) * (buSL p + 1) * (p + 1)) := by ring
      have h4 : 1200 * S * ((t + 1) * (buSL p + 1) * (p + 1))
          ≤ 1200 * S * (13 * ((t + 1) * (p + 1) * (p + 1))) := by
        refine Nat.mul_le_mul_left (1200 * S) ?_
        calc (t + 1) * (buSL p + 1) * (p + 1)
            ≤ (t + 1) * (13 * (p + 1)) * (p + 1) :=
              Nat.mul_le_mul_right (p + 1) (Nat.mul_le_mul_left (t + 1)
                (by simp only [buSL]; omega))
          _ = 13 * ((t + 1) * (p + 1) * (p + 1)) := by ring
      have h5 : 1200 * S * (13 * ((t + 1) * (p + 1) * (p + 1)))
          = 15600 * S * (t + 1) * (p + 1) * (p + 1) := by ring
      have h6 : 15600 * S * (t + 1) * (p + 1) * (p + 1)
          ≤ 2 ^ 22 * S * (t + 1) * (p + 1) * (p + 1) := by
        have h6' : 15600 * S * (t + 1) * (p + 1) * (p + 1)
            = (15600 * S) * ((t + 1) * (p + 1) * (p + 1)) := by ring
        have h6'' : 2 ^ 22 * S * (t + 1) * (p + 1) * (p + 1)
            = (2 ^ 22 * S) * ((t + 1) * (p + 1) * (p + 1)) := by ring
        rw [h6', h6'']
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right S (by norm_num : (15600 : ℕ) ≤ 2 ^ 22))
      have h7 : 2 ^ 22 * S * (t + 1) * (p + 1) * (p + 1)
          = 4 * (2 ^ 20 * S * (t + 1) * (p + 1) * (p + 1)) := by ring
      calc (Krl * 2 * (HvdH.vsz (ofList ys) + HvdH.isz (s:ℤ) + 1))
            + ((Ktk * (HvdH.vsz (ofList ys) + HvdH.isz (s:ℤ) + 1))
              + ((ys.take s).length * (Kel * buSL p + Kml * (buSL p + 1)) + Kml))
          ≤ 1200 * S * ((t + 1) * (buSL p + 1) * (p + 1)) := h3
        _ ≤ 1200 * S * (13 * ((t + 1) * (p + 1) * (p + 1))) := h4
        _ = 15600 * S * (t + 1) * (p + 1) * (p + 1) := h5
        _ ≤ 2 ^ 22 * S * (t + 1) * (p + 1) * (p + 1) := h6
        _ = 4 * (2 ^ 20 * S * (t + 1) * (p + 1) * (p + 1)) := h7
    · intro Dv hDv
      exact ⟨ys, hperm, hsortp, hDv⟩
  -- assembly
  have hCf : WS main (.seq zipprog (.seq sortprog (.seq (rollprog 1) (.seq takeprog (mlcomb elemprog)))))
      [buKeysT s t, cvecVal u, .int (s:ℤ)]
      (fun Dv => ∃ ys : List HvdH.Val, ys.Perm (buSelRecs s t u) ∧
        ys.Pairwise (fun a b => HvdH.pairKey a < HvdH.pairKey b) ∧
        Dv = [ofList ((ys.take s).map buSelElem)])
      (2 ^ 20 * S * (t + 1) * (p + 1) * (p + 1) + (2 ^ 20 * S * (t + 1) * (p + 1) * (p + 1)
        + 4 * (2 ^ 20 * S * (t + 1) * (p + 1) * (p + 1)))) :=
    WS.comp KL (WS.cost KL h2 (stageLe hc2)) (fun Bv hB => by
      rw [hB]
      exact WS.comp KL (WS.cost KL h3 (stageLe hc3)) h4)
  have hAll : WS main (.seq swapprog (.seq zipprog (.seq sortprog
        (.seq (rollprog 1) (.seq takeprog (mlcomb elemprog))))))
      [cvecVal u, buKeysT s t, .int (s:ℤ)]
      (fun Dv => ∃ ys : List HvdH.Val, ys.Perm (buSelRecs s t u) ∧
        ys.Pairwise (fun a b => HvdH.pairKey a < HvdH.pairKey b) ∧
        Dv = [ofList ((ys.take s).map buSelElem)])
      (2 ^ 20 * S * (t + 1) * (p + 1) * (p + 1)
        + (2 ^ 20 * S * (t + 1) * (p + 1) * (p + 1)
          + (2 ^ 20 * S * (t + 1) * (p + 1) * (p + 1)
            + 4 * (2 ^ 20 * S * (t + 1) * (p + 1) * (p + 1))))) :=
    WS.comp KL (WS.cost KL h1 (stageLe hc1)) (fun Bv hB => by rw [hB]; exact hCf)
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hoth⟩ :=
    hAll rest (cvecVal u :: buKeysT s t :: HvdH.Val.int (s:ℤ) :: rest) rfl s0 R hR
  obtain ⟨Dv, ⟨ys, hperm, hsortp, hDv⟩, hout⟩ := hpost
  have hylen : ys.length = t := by
    rw [List.Perm.length_eq hperm, (buSelRecsSpec s t u hulen).2.2.2]
  have hget : ∀ ℓ < s, ys.getD ℓ HvdH.Val.nil
      = HvdH.Val.cons (HvdH.Val.int (ℓ : ℤ)) (cfxVal (u.getD (egNu s t ℓ) (0, 0))) :=
    buSelSorted s t hs hst hcop u hulen ys hperm hsortp
  have heq : (ys.take s).map buSelElem = (buSelL s t u).map cfxVal :=
    buSelOutEq s t hst u hulen ys hylen hget
  have hDvv : Dv = [cvecVal (buSelL s t u)] := by
    rw [hDv, heq]
    rfl
  refine ⟨out, s', n, ?_, hev, ?_, ?_, hoth⟩
  · refine ⟨u, rest, buSelL s t u, rfl, ?_, rfl, List.length_ofFn, buSelLInV p s t u hulen hV⟩
    rw [hout, hDvv]
    rfl
  · refine le_trans hn ?_
    have hsum : (2 ^ 20 * S * (t + 1) * (p + 1) * (p + 1)
        + (2 ^ 20 * S * (t + 1) * (p + 1) * (p + 1)
          + (2 ^ 20 * S * (t + 1) * (p + 1) * (p + 1)
            + 4 * (2 ^ 20 * S * (t + 1) * (p + 1) * (p + 1)))))
        = 7 * (2 ^ 20 * S * (t + 1) * (p + 1) * (p + 1)) := by ring
    rw [hsum]
    exact finalLe (S := S) (by omega : 40 ≤ S)
  · rw [hstk]
