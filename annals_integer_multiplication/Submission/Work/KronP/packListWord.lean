import Mathlib
import Submission.Work.KronP.defs
import Submission.Work.ConvR.sizes
import Submission.Work.KronP.packElemPos
import Submission.Work.KronP.packElemNeg
import Submission.Work.KronP.packMapLiftC
import Submission.Work.KronP.packChunkSize
import Submission.Work.KronP.packEvalSub

/-!
# `Work.KronP.packListWord`: the packing of one signed coefficient list

`packListWord` is the last piece of the Kronecker word (paper Lemma 2.5) that was still
missing: given the signed coefficient list `zsVal xs` and a base `b` (`b = 3p` in the
caller), it produces `pack xs b = Σ_j xs[j]·2^{b j}`.

Route (validated by the cost bound `K * (vsz (zsVal xs) + xs.length * (b + 1) + isz b + 2)`):

* duplicate the list (`KernelLib.dup`);
* `KernelLib.mapList` (through `Work.KronP.packMapLiftC`) with the per-element words
  `packElemPos` / `packElemNeg` turns the copy into `intList` of the nonnegative, resp.
  the negative parts `(max x 0).toNat`, `(max (-x) 0).toNat`;
* `KernelLib.pick` puts a copy of the base under the second list (the first `evalPoly`
  consumes the other copy), so two `IntLib.evalPoly` calls consume both lists and the
  base, and `IntLib.sub` finishes;
* `Work.KronP.packEvalSub` identifies the result with `pack xs b`.

All costs are linear: `mapList` costs `O(n·(b+1))`, `evalPoly` costs
`O(Σ isz + n·(b+1) + isz b)`, and the moves cost `O(vsz)`.
-/

set_option autoImplicit false
set_option maxErrors 2000
set_option maxHeartbeats 4000000

namespace Work.KronP

open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-! ## plumbing -/

theorem plwConseq {main p : Cmd} {P P' : List Val → Prop} {Q Q' : List Val → List Val → Prop}
    {C C' : List Val → ℕ} (h : WordR main p P Q C) (hP : ∀ vs, P' vs → P vs)
    (hQ : ∀ vs out, P' vs → Q vs out → Q' vs out) (hC : ∀ vs, P' vs → C vs ≤ C' vs) :
    WordR main p P' Q' C' := by
  intro vs hP' s R hR
  obtain ⟨out, s', n, hQh, he, hn, hstk, hoth⟩ := h vs (hP vs hP') s R hR
  exact ⟨out, s', n, hQ vs out hP' hQh, he, le_trans hn (hC vs hP'), hstk, hoth⟩

theorem plwSeq {main : Cmd} {p q : Cmd} {A B C : List Val} {c d : ℕ}
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c))
    (h2 : WordR main q (fun vs => vs = B) (fun _ out => out = C) (fun _ => d)) :
    WordR main (.seq p q) (fun vs => vs = A) (fun _ out => out = C) (fun _ => c + d) := by
  intro vs hv s R hR
  rw [hv] at hR
  obtain ⟨mid, s₂, n₁, hQ, he₁, hn₁, hstk₁, hoth₁⟩ := h1 A rfl s R hR
  rw [hQ] at hstk₁
  obtain ⟨out, s₃, n₂, hQ', he₂, hn₂, hstk₂, hoth₂⟩ := h2 B rfl s₂ R hstk₁
  exact ⟨out, s₃, n₁ + n₂, hQ', Eval.seq he₁ he₂, Nat.add_le_add hn₁ hn₂, hstk₂,
    fun k hk => by rw [hoth₂ k hk, hoth₁ k hk]⟩

/-! ## list / arithmetic helpers -/

theorem plwOfList_int_fun (xs : List ℤ) (g : ℤ → ℕ) :
    HvdH.ofList (xs.map (fun z => HvdH.Val.int ((g z : ℤ)))) = HvdH.intList (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons, List.map_cons]
    change HvdH.Val.cons (HvdH.Val.int ((g a : ℤ)))
      (HvdH.ofList (t.map (fun z => HvdH.Val.int ((g z : ℤ))))) = HvdH.intList (g a :: t.map g)
    rw [ih]
    rfl

theorem plwIsz_le_add_of_natAbs_le {a b c : ℤ} (h : a.natAbs ≤ b.natAbs + c.natAbs) :
    HvdH.isz a ≤ HvdH.isz b + HvdH.isz c := by
  set M := max b.natAbs.size c.natAbs.size with hM
  have hb : b.natAbs < 2 ^ M :=
    lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
  have hc : c.natAbs < 2 ^ M :=
    lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  have h2 : a.natAbs < 2 ^ (M + 1) := by
    calc a.natAbs ≤ b.natAbs + c.natAbs := h
      _ < 2 ^ M + 2 ^ M := Nat.add_lt_add hb hc
      _ = 2 ^ (M + 1) := by rw [pow_succ]; ring
  have h3 : a.natAbs.size ≤ M + 1 := (Nat.size_le).mpr h2
  have h4 : M ≤ b.natAbs.size + c.natAbs.size := by rw [hM]; omega
  simp only [HvdH.isz]
  omega

theorem plwIsz_sub_le (a b : ℤ) : HvdH.isz (a - b) ≤ HvdH.isz a + HvdH.isz b :=
  plwIsz_le_add_of_natAbs_le (Int.natAbs_sub_le a b)

theorem plwToNat_max_neg_le (y : ℤ) : (max (-y) 0).toNat ≤ y.natAbs := by
  by_cases hy0 : 0 ≤ y
  · have hmm : max (-y) 0 = (0 : ℤ) := max_eq_right (by omega)
    rw [hmm]
    exact Nat.zero_le _
  · have hy1 : y ≤ 0 := by omega
    have hmm : max (-y) 0 = -y := max_eq_left (by omega)
    rw [hmm]
    have hnat : ((y.natAbs : ℕ) : ℤ) = -y := by
      rw [← Int.natAbs_neg y]
      exact Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ -y)
    have h : (((-y).toNat : ℕ) : ℤ) ≤ ((y.natAbs : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -y), hnat]
    exact_mod_cast h

theorem plwToNat_max_pos_le (y : ℤ) : (max y 0).toNat ≤ y.natAbs := by
  by_cases hy0 : 0 ≤ y
  · have hmm : max y 0 = y := max_eq_left hy0
    rw [hmm]
    have h : y.toNat = y.natAbs := by
      apply Nat.cast_injective (R := ℤ)
      rw [Int.toNat_of_nonneg hy0, Int.natAbs_of_nonneg hy0]
    rw [h]
  · have hy1 : y ≤ 0 := by omega
    have hmm : max y 0 = (0 : ℤ) := max_eq_right hy1
    rw [hmm]
    exact Nat.zero_le _

theorem plwTake2_vsz_sum (a b : Val) (l : List Val) :
    (((a :: b :: l).take 2).map vsz).sum = vsz a + vsz b := by
  simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  ring

theorem plwTake3_vsz_sum (a b c : Val) (l : List Val) :
    (((a :: b :: c :: l).take 3).map vsz).sum = vsz a + vsz b + vsz c := by
  simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  ring

theorem plwGetD1_erase1 (a b : Val) (l : List Val) :
    (a :: b :: l).getD 1 .nil :: (a :: b :: l).eraseIdx 1 = b :: a :: l := by simp

theorem plwGetD1_erase1_4 (a b c : Val) (l : List Val) :
    (a :: b :: c :: l).getD 1 .nil :: (a :: b :: c :: l).eraseIdx 1 = b :: a :: c :: l := by simp

theorem plwGetD1_erase1_5 (a b c d : Val) (l : List Val) :
    (a :: b :: c :: d :: l).getD 1 .nil :: (a :: b :: c :: d :: l).eraseIdx 1 = b :: a :: c :: d :: l := by
  simp

theorem plwGetD2_erase2_4 (a b c : Val) (l : List Val) :
    (a :: b :: c :: l).getD 2 .nil :: (a :: b :: c :: l).eraseIdx 2 = c :: a :: b :: l := by
  simp

theorem plwGetD2_pick4 (a b c : Val) (l : List Val) :
    (a :: b :: c :: l).getD 2 .nil :: (a :: b :: c :: l) = c :: a :: b :: c :: l := by simp

theorem plwSum_mul_bud (l : List ℕ) (Bud : ℕ) :
    (l.map (fun c => c * Bud)).sum = l.sum * Bud := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]


/-! ## the size facts used by the cost bounds -/

theorem plwIszLeIszOfNatAbsLe {a b : ℤ} (h : a.natAbs ≤ b.natAbs) :
    HvdH.isz a ≤ HvdH.isz b := by
  have h1 : a.natAbs < 2 ^ b.natAbs.size := lt_of_le_of_lt h (Nat.lt_size_self _)
  have h2 : a.natAbs.size ≤ b.natAbs.size := (Nat.size_le).mpr h1
  simp only [HvdH.isz]
  omega

theorem plwIszToNatMaxPos (z : ℤ) : HvdH.isz (((max z 0).toNat : ℤ)) ≤ HvdH.isz z := by
  apply plwIszLeIszOfNatAbsLe
  rw [Int.natAbs_natCast]
  exact plwToNat_max_pos_le z

theorem plwIszToNatMaxNeg (z : ℤ) : HvdH.isz (((max (-z) 0).toNat : ℤ)) ≤ HvdH.isz z := by
  apply plwIszLeIszOfNatAbsLe
  rw [Int.natAbs_natCast]
  exact plwToNat_max_neg_le z

theorem plwIszLeOfNatAbsLt {z : ℤ} {b : ℕ} (h : z.natAbs < 2 ^ (3 * b)) :
    HvdH.isz z ≤ 3 * b + 2 := by
  have h1 : z.natAbs.size ≤ 3 * b := (Nat.size_le).mpr h
  simp only [HvdH.isz]
  omega

theorem plwVszIntListPos : ∀ xs : List ℤ,
    HvdH.vsz (HvdH.intList (xs.map fun x => (max x 0).toNat)) ≤ HvdH.vsz (Work.KronP.zsVal xs)
  | [] => by simp [Work.KronP.zsVal, HvdH.intList, HvdH.ofList, HvdH.vsz, HvdH.Val.enc]
  | a :: t => by
      have ih := plwVszIntListPos t
      have hL : HvdH.vsz (HvdH.intList ((a :: t).map fun x => (max x 0).toNat)) =
          HvdH.isz ((max a 0).toNat : ℤ)
            + HvdH.vsz (HvdH.intList (t.map fun x => (max x 0).toNat)) + 1 := by
        rw [List.map_cons,
          show HvdH.intList ((max a 0).toNat :: (t.map fun x => (max x 0).toNat)) =
            HvdH.Val.cons (HvdH.Val.int (((max a 0).toNat : ℤ)))
              (HvdH.intList (t.map fun x => (max x 0).toNat)) from rfl,
          Work.ConvR.vsz_cons, Work.ConvR.vsz_int]
      have hR : HvdH.vsz (Work.KronP.zsVal (a :: t)) =
          HvdH.isz a + HvdH.vsz (Work.KronP.zsVal t) + 1 := by
        rw [show Work.KronP.zsVal (a :: t) =
            HvdH.Val.cons (HvdH.Val.int a) (Work.KronP.zsVal t) from rfl,
          Work.ConvR.vsz_cons, Work.ConvR.vsz_int]
      rw [hL, hR]
      have := plwIszToNatMaxPos a
      omega

theorem plwVszIntListNeg : ∀ xs : List ℤ,
    HvdH.vsz (HvdH.intList (xs.map fun x => (max (-x) 0).toNat)) ≤ HvdH.vsz (Work.KronP.zsVal xs)
  | [] => by simp [Work.KronP.zsVal, HvdH.intList, HvdH.ofList, HvdH.vsz, HvdH.Val.enc]
  | a :: t => by
      have ih := plwVszIntListNeg t
      have hL : HvdH.vsz (HvdH.intList ((a :: t).map fun x => (max (-x) 0).toNat)) =
          HvdH.isz ((max (-a) 0).toNat : ℤ)
            + HvdH.vsz (HvdH.intList (t.map fun x => (max (-x) 0).toNat)) + 1 := by
        rw [List.map_cons,
          show HvdH.intList ((max (-a) 0).toNat :: (t.map fun x => (max (-x) 0).toNat)) =
            HvdH.Val.cons (HvdH.Val.int (((max (-a) 0).toNat : ℤ)))
              (HvdH.intList (t.map fun x => (max (-x) 0).toNat)) from rfl,
          Work.ConvR.vsz_cons, Work.ConvR.vsz_int]
      have hR : HvdH.vsz (Work.KronP.zsVal (a :: t)) =
          HvdH.isz a + HvdH.vsz (Work.KronP.zsVal t) + 1 := by
        rw [show Work.KronP.zsVal (a :: t) =
            HvdH.Val.cons (HvdH.Val.int a) (Work.KronP.zsVal t) from rfl,
          Work.ConvR.vsz_cons, Work.ConvR.vsz_int]
      rw [hL, hR]
      have := plwIszToNatMaxNeg a
      omega

theorem plwVszZsVal (xs : List ℤ) :
    HvdH.vsz (Work.KronP.zsVal xs) = (xs.map HvdH.isz).sum + xs.length + 1 := by
  rw [show Work.KronP.zsVal xs = HvdH.ofList (xs.map HvdH.Val.int) from rfl,
    Work.ConvR.vsz_ofList, List.length_map, List.map_map]
  simp only [Function.comp_def, Work.ConvR.vsz_int]

theorem plwValSizes (b : ℕ) (xs : List ℤ) (hx : ∀ x ∈ xs, x.natAbs < 2 ^ (3 * b)) :
    (∀ z : ℤ, HvdH.isz (((max z 0).toNat : ℤ)) ≤ HvdH.isz z) ∧
    (∀ z : ℤ, HvdH.isz (((max (-z) 0).toNat : ℤ)) ≤ HvdH.isz z) ∧
    (∀ x ∈ xs, HvdH.isz x ≤ 3 * b + 2) ∧
    HvdH.vsz (Work.KronP.zsVal xs) = (xs.map HvdH.isz).sum + xs.length + 1 ∧
    HvdH.vsz (HvdH.intList (xs.map fun x => (max x 0).toNat)) ≤ HvdH.vsz (Work.KronP.zsVal xs) ∧
    HvdH.vsz (HvdH.intList (xs.map fun x => (max (-x) 0).toNat)) ≤ HvdH.vsz (Work.KronP.zsVal xs) := by
  refine ⟨plwIszToNatMaxPos, plwIszToNatMaxNeg, ?_, plwVszZsVal xs, plwVszIntListPos xs,
    plwVszIntListNeg xs⟩
  intro x hx'
  exact plwIszLeOfNatAbsLt (hx x hx')

/-! ## the main theorem -/

theorem packListWord (hK : HvdH.KernelLib) (hI : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ),
      ∀ (main : HvdH.Cmd) (xs : List ℤ) (b : ℕ) (tl : List HvdH.Val),
        1 ≤ b → (∀ x ∈ xs, x.natAbs < 2 ^ (3 * b)) →
        HvdH.WordR main prog
          (fun vs => vs = Work.KronP.zsVal xs :: HvdH.Val.int (b : ℤ) :: tl)
          (fun _ out => out = HvdH.Val.int (Work.KronP.pack xs b) :: tl)
          (fun _ => K * (HvdH.vsz (Work.KronP.zsVal xs) + xs.length * (b + 1) +
            HvdH.isz (b : ℤ) + 2)) := by
  obtain ⟨dupP, Kdup, hdup⟩ := hK.dup
  obtain ⟨dropP, Kdrop, hdrop⟩ := hK.drop
  obtain ⟨rollP, Kroll, hroll⟩ := hK.roll
  obtain ⟨pickP, Kpick, hpick⟩ := hK.pick
  obtain ⟨evP, Kev, hev⟩ := hI.evalPoly
  obtain ⟨subP, Ksub, hsub⟩ := hI.sub
  obtain ⟨elP, cPos, hPos⟩ := packElemPos hK hI
  obtain ⟨elN, cNeg, hNeg⟩ := packElemNeg hK hI
  obtain ⟨mComb, Kml, hMapLift⟩ := packMapLiftC hK
  set C1 : ℕ := 4 * Kdup + 1 with hC1
  set C2 : ℕ := 40 * (cPos + 1) * Kml + 1 with hC2
  set C3 : ℕ := 16 * Kroll + 1 with hC3
  set C4 : ℕ := 40 * (cNeg + 1) * Kml + 1 with hC4
  set C5 : ℕ := 20 * Kpick + 1 with hC5
  set C7 : ℕ := 8 * Kev + 1 with hC7
  set C8 : ℕ := 40 * Kroll + 1 with hC8
  set C10 : ℕ := 60 * Ksub + 1 with hC10
  set C9 : ℕ := 50 * Kroll + 1 with hC9
  set C11 : ℕ := 40 * Kroll + 1 with hC11
  set Kk : ℕ := [C1, C2, C3, C4, C5, C3, C7, C8, C9, C11, C7, C10].sum with hKk
  refine ⟨dupP ;;; mComb elP ;;; rollP 1 ;;; mComb elN ;;; pickP 2 ;;; rollP 1 ;;; evP ;;;
      rollP 1 ;;; rollP 2 ;;; rollP 1 ;;; evP ;;; subP, Kk, ?_⟩
  intro main xs b tl hb hx
  obtain ⟨hszt1, hszt2, hElem, _hvszE, hPvle, hNvle⟩ := plwValSizes b xs hx
  set Lv : Val := Work.KronP.zsVal xs with hLv
  set Bv : Val := HvdH.Val.int (b : ℤ) with hBv
  set L : ℕ := 3 * b + 2 with hL
  set hs1 : List ℕ := xs.map (fun x => (max x 0).toNat) with hhs1
  set hs2 : List ℕ := xs.map (fun x => (max (-x) 0).toNat) with hhs2
  set Pv : Val := HvdH.intList hs1 with hPv
  set Nv : Val := HvdH.intList hs2 with hNv
  set h1 : ℕ := HvdH.evalChunks hs1 b with hh1
  set h2 : ℕ := HvdH.evalChunks hs2 b with hh2
  set Bud : ℕ := HvdH.vsz (Work.KronP.zsVal xs) + xs.length * (b + 1) +
    HvdH.isz (b : ℤ) + 2 with hBud
  set A0 : List Val := Lv :: Bv :: tl with hA0
  set A1 : List Val := Lv :: Lv :: Bv :: tl with hA1
  set A2 : List Val := Pv :: Lv :: Bv :: tl with hA2
  set A3 : List Val := Lv :: Pv :: Bv :: tl with hA3
  set A4 : List Val := Nv :: Pv :: Bv :: tl with hA4
  set A5 : List Val := Bv :: Nv :: Pv :: Bv :: tl with hA5
  set A6 : List Val := Nv :: Bv :: Pv :: Bv :: tl with hA6
  set A7 : List Val := Val.int (h2 : ℤ) :: Pv :: Bv :: tl with hA7
  set A8 : List Val := Pv :: Val.int (h2 : ℤ) :: Bv :: tl with hA8
  set A9 : List Val := Bv :: Pv :: Val.int (h2 : ℤ) :: tl with hA9
  set A10 : List Val := Pv :: Bv :: Val.int (h2 : ℤ) :: tl with hA10
  set A11 : List Val := Val.int (h1 : ℤ) :: Val.int (h2 : ℤ) :: tl with hA11
  set A12 : List Val := Val.int ((h1 : ℤ) - (h2 : ℤ)) :: tl with hA12
  have hB1 : 1 ≤ Bud := by
    have h := Work.ConvR.vsz_one_le (Work.KronP.zsVal xs)
    rw [hBud]; omega
  have hVL : HvdH.vsz Lv ≤ Bud := by rw [hBud, hLv]; omega
  have hVP : HvdH.vsz Pv ≤ Bud := by
    have h := hPvle
    rw [hPv, hLv] at h
    rw [hBud]; omega
  have hVN : HvdH.vsz Nv ≤ Bud := by
    have h := hNvle
    rw [hNv, hLv] at h
    rw [hBud]; omega
  have hVB : HvdH.vsz Bv ≤ Bud := by rw [hBv, Work.ConvR.vsz_int, hBud]; omega
  have hIszB : HvdH.isz (b : ℤ) ≤ Bud := by rw [hBud]; omega
  have hiszb' : HvdH.isz (b : ℤ) ≤ Bud := hIszB
  have hS1 : (hs1.map fun h => HvdH.isz (h : ℤ)).sum ≤ Bud := by
    have h : (hs1.map fun h => HvdH.isz (h : ℤ)).sum + hs1.length + 1 ≤ Bud := by
      rw [← Work.ConvR.vsz_intList hs1]
      have h2 := hVP
      rw [hPv] at h2
      exact h2
    omega
  have hS2 : (hs2.map fun h => HvdH.isz (h : ℤ)).sum ≤ Bud := by
    have h : (hs2.map fun h => HvdH.isz (h : ℤ)).sum + hs2.length + 1 ≤ Bud := by
      rw [← Work.ConvR.vsz_intList hs2]
      have h2 := hVN
      rw [hNv] at h2
      exact h2
    omega
  have hnb : xs.length * (b + 1) ≤ Bud := by rw [hBud]; omega
  have hLp : L + 1 = 3 * (b + 1) := by rw [hL]; omega
  have hxL : ∀ x ∈ xs, HvdH.isz x ≤ L := by intro x hx'; rw [hL]; exact hElem x hx'
  have hL1 : HvdH.isz ((h1 : ℕ) : ℤ) ≤ 12 * Bud := by
    have hbnd : ∀ h ∈ hs1, h < 2 ^ (3 * b) := by
      intro h hh
      rw [hhs1] at hh
      obtain ⟨y, hy, hyeq⟩ := List.mem_map.mp hh
      rw [← hyeq]
      exact lt_of_le_of_lt (plwToNat_max_pos_le y) (hx y hy)
    have hc := packChunkSize hb hbnd
    rw [← hh1] at hc
    have hl : hs1.length = xs.length := by rw [hhs1, List.length_map]
    rw [hl] at hc
    omega
  have hL2 : HvdH.isz ((h2 : ℕ) : ℤ) ≤ 12 * Bud := by
    have hbnd : ∀ h ∈ hs2, h < 2 ^ (3 * b) := by
      intro h hh
      rw [hhs2] at hh
      obtain ⟨y, hy, hyeq⟩ := List.mem_map.mp hh
      rw [← hyeq]
      exact lt_of_le_of_lt (plwToNat_max_neg_le y) (hx y hy)
    have hc := packChunkSize hb hbnd
    rw [← hh2] at hc
    have hl : hs2.length = xs.length := by rw [hhs2, List.length_map]
    rw [hl] at hc
    omega
  -- STEP 1: duplicate the value list
  have e1 : WordR main dupP (fun vs => vs = A0) (fun _ out => out = A1)
      (fun _ => C1 * Bud) := by
    refine plwConseq (hdup main) ?_ ?_ ?_
    · intro vs hv; rw [hv, hA0]; exact List.cons_ne_nil _ _
    · intro vs out hv hq
      subst hv
      obtain ⟨v, rest, hvs, hout⟩ := hq
      rw [hA0] at hvs
      simp only [List.cons.injEq] at hvs
      obtain ⟨ha, hb'⟩ := hvs
      rw [hout, ← ha, ← hb', hA1]
    · intro vs hv
      subst hv
      rw [hA0, List.headD_cons, hC1]
      have hKV : Kdup * HvdH.vsz Lv ≤ Kdup * Bud := Nat.mul_le_mul_left _ hVL
      have hK1 : Kdup ≤ Kdup * Bud := by
        calc Kdup = Kdup * 1 := (Nat.mul_one _).symm
          _ ≤ Kdup * Bud := Nat.mul_le_mul_left _ hB1
      nlinarith [hKV, hK1]
  -- STEP 2: map the positive parts over the copy
  have e2 : WordR main (mComb elP) (fun vs => vs = A1) (fun _ out => out = A2)
      (fun _ => C2 * Bud) := by
    have hbody : ∀ z : ℤ, HvdH.isz z ≤ L → WordR main elP
        (fun vs => vs = HvdH.Val.int z :: (Lv :: Bv :: tl))
        (fun _ out => out = HvdH.Val.int (((max z 0).toNat : ℤ)) :: (Lv :: Bv :: tl))
        (fun _ => cPos * (L + 1)) :=
      fun z hz => hPos main (Lv :: Bv :: tl) L z hz
    have hsz : ∀ z : ℤ, HvdH.isz z ≤ L →
        HvdH.vsz (HvdH.Val.int (((max z 0).toNat : ℤ))) ≤ L := by
      intro z hz
      rw [Work.ConvR.vsz_int]
      exact le_trans (hszt1 z) hz
    have hmain := hMapLift main elP (Lv :: Bv :: tl)
      (fun z => HvdH.Val.int (((max z 0).toNat : ℤ))) (cPos * (L + 1)) L hbody hsz xs hxL
    refine plwConseq hmain ?_ ?_ ?_
    · intro vs hv; subst hv; rw [hA1, hLv]
    · intro vs out hv hq
      subst hv
      rw [hq, plwOfList_int_fun xs (fun x => (max x 0).toNat), ← hhs1, ← hPv, hA2]
    · intro vs hv
      have hLp2 : cPos * (L + 1) + L + 1 = (cPos + 1) * (3 * (b + 1)) := by rw [hL]; ring
      rw [hLp2, hC2]
      have hA2' : Kml * (xs.length * (b + 1)) ≤ Kml * Bud := Nat.mul_le_mul_left _ hnb
      have hA3' : Kml * (cPos + 1) * (xs.length * (b + 1)) ≤ Kml * (cPos + 1) * Bud :=
        Nat.mul_le_mul_left _ hnb
      have hK1 : Kml ≤ Kml * Bud := by
        calc Kml = Kml * 1 := (Nat.mul_one _).symm
          _ ≤ Kml * Bud := Nat.mul_le_mul_left _ hB1
      nlinarith [hA2', hA3', hK1]
  -- STEP 3: bring the original list to the top
  have e3 : WordR main (rollP 1) (fun vs => vs = A2) (fun _ out => out = A3)
      (fun _ => C3 * Bud) := by
    refine plwConseq (hroll main 1) ?_ ?_ ?_
    · intro vs hv; subst hv; rw [hA2]; simp
    · intro vs out hv hq
      subst hv
      rw [hq, hA2, hA3, plwGetD1_erase1_4]
    · intro vs hv
      subst hv
      rw [hA2, plwTake2_vsz_sum, hC3]
      have h1 : Kroll * HvdH.vsz Pv ≤ Kroll * Bud := Nat.mul_le_mul_left _ hVP
      have h2 : Kroll * HvdH.vsz Lv ≤ Kroll * Bud := Nat.mul_le_mul_left _ hVL
      have h3 : Kroll ≤ Kroll * Bud := by
        calc Kroll = Kroll * 1 := (Nat.mul_one _).symm
          _ ≤ Kroll * Bud := Nat.mul_le_mul_left _ hB1
      nlinarith [h1, h2, h3]
  -- STEP 4: map the negative parts over the original list
  have e4 : WordR main (mComb elN) (fun vs => vs = A3) (fun _ out => out = A4)
      (fun _ => C4 * Bud) := by
    have hbody : ∀ z : ℤ, HvdH.isz z ≤ L → WordR main elN
        (fun vs => vs = HvdH.Val.int z :: (Pv :: Bv :: tl))
        (fun _ out => out = HvdH.Val.int (((max (-z) 0).toNat : ℤ)) :: (Pv :: Bv :: tl))
        (fun _ => cNeg * (L + 1)) :=
      fun z hz => hNeg main (Pv :: Bv :: tl) L z hz
    have hsz : ∀ z : ℤ, HvdH.isz z ≤ L →
        HvdH.vsz (HvdH.Val.int (((max (-z) 0).toNat : ℤ))) ≤ L := by
      intro z hz
      rw [Work.ConvR.vsz_int]
      exact le_trans (hszt2 z) hz
    have hmain := hMapLift main elN (Pv :: Bv :: tl)
      (fun z => HvdH.Val.int (((max (-z) 0).toNat : ℤ))) (cNeg * (L + 1)) L hbody hsz xs hxL
    refine plwConseq hmain ?_ ?_ ?_
    · intro vs hv; subst hv; rw [hA3, hLv]
    · intro vs out hv hq
      subst hv
      rw [hq, plwOfList_int_fun xs (fun x => (max (-x) 0).toNat), ← hhs2, ← hNv, hA4]
    · intro vs hv
      have hLp2 : cNeg * (L + 1) + L + 1 = (cNeg + 1) * (3 * (b + 1)) := by rw [hL]; ring
      rw [hLp2, hC4]
      have hA2' : Kml * (xs.length * (b + 1)) ≤ Kml * Bud := Nat.mul_le_mul_left _ hnb
      have hA3' : Kml * (cNeg + 1) * (xs.length * (b + 1)) ≤ Kml * (cNeg + 1) * Bud :=
        Nat.mul_le_mul_left _ hnb
      have hK1 : Kml ≤ Kml * Bud := by
        calc Kml = Kml * 1 := (Nat.mul_one _).symm
          _ ≤ Kml * Bud := Nat.mul_le_mul_left _ hB1
      nlinarith [hA2', hA3', hK1]
  -- STEP 5: copy the base to the top
  have e5 : WordR main (pickP 2) (fun vs => vs = A4) (fun _ out => out = A5)
      (fun _ => C5 * Bud) := by
    refine plwConseq (hpick main 2) ?_ ?_ ?_
    · intro vs hv; subst hv; rw [hA4]; simp
    · intro vs out hv hq
      subst hv
      rw [hq, hA4, hA5, plwGetD2_pick4]
    · intro vs hv
      subst hv
      rw [hA4, plwTake3_vsz_sum, hC5]
      have h1 : Kpick * HvdH.vsz Nv ≤ Kpick * Bud := Nat.mul_le_mul_left _ hVN
      have h2 : Kpick * HvdH.vsz Pv ≤ Kpick * Bud := Nat.mul_le_mul_left _ hVP
      have h3 : Kpick * HvdH.isz (b : ℤ) ≤ Kpick * Bud := by
        have h := hVB
        rw [hBv, Work.ConvR.vsz_int] at h
        exact Nat.mul_le_mul_left _ h
      have h4 : Kpick ≤ Kpick * Bud := by
        calc Kpick = Kpick * 1 := (Nat.mul_one _).symm
          _ ≤ Kpick * Bud := Nat.mul_le_mul_left _ hB1
      nlinarith [h1, h2, h3, h4]
  -- STEP 6: the negative list to the top
  have e6 : WordR main (rollP 1) (fun vs => vs = A5) (fun _ out => out = A6)
      (fun _ => C3 * Bud) := by
    refine plwConseq (hroll main 1) ?_ ?_ ?_
    · intro vs hv; subst hv; rw [hA5]; simp
    · intro vs out hv hq
      subst hv
      rw [hq, hA5, hA6, plwGetD1_erase1_4]
    · intro vs hv
      subst hv
      rw [hA5, plwTake2_vsz_sum, hC3]
      have h1 : Kroll * HvdH.vsz Bv ≤ Kroll * Bud := Nat.mul_le_mul_left _ hVB
      have h2 : Kroll * HvdH.vsz Nv ≤ Kroll * Bud := Nat.mul_le_mul_left _ hVN
      have h3 : Kroll ≤ Kroll * Bud := by
        calc Kroll = Kroll * 1 := (Nat.mul_one _).symm
          _ ≤ Kroll * Bud := Nat.mul_le_mul_left _ hB1
      nlinarith [h1, h2, h3]
  -- STEP 7: evaluate the negative digit list
  have e7 : WordR main evP (fun vs => vs = A6) (fun _ out => out = A7)
      (fun _ => C7 * Bud) := by
    have hbnd2 : ∀ h ∈ hs2, h < 2 ^ (3 * b) := by
      intro h hh
      rw [hhs2] at hh
      obtain ⟨y, hy, hyeq⟩ := List.mem_map.mp hh
      rw [← hyeq]
      exact lt_of_le_of_lt (plwToNat_max_neg_le y) (hx y hy)
    have hev2 := hev main hs2 b hb hbnd2
    refine plwConseq hev2 ?_ ?_ ?_
    · intro vs hv
      subst hv
      exact ⟨Pv :: Bv :: tl, by rw [hA6, hNv, hBv]⟩
    · intro vs out hv hq
      subst hv
      obtain ⟨r, hr, hout⟩ := hq
      rw [hA6, hNv, hBv] at hr
      simp only [List.cons.injEq] at hr
      obtain ⟨-, -, hrr⟩ := hr
      rw [hout, hA7, ← hh2, hBv, ← hrr]
    · intro vs hv
      rw [hC7]
      have hl : hs2.length * (b + 1) = xs.length * (b + 1) := by
        congr 1; rw [hhs2, List.length_map]
      have h3' : HvdH.isz (b : ℤ) + 1 ≤ Bud := by rw [hBud]; omega
      have hA1' : Kev * (hs2.map fun h => HvdH.isz (h : ℤ)).sum ≤ Kev * Bud :=
        Nat.mul_le_mul_left _ hS2
      have hA2' : Kev * (hs2.length * (b + 1)) ≤ Kev * Bud := by
        rw [hl]; exact Nat.mul_le_mul_left _ hnb
      have hA3' : Kev * (HvdH.isz (b : ℤ) + 1) ≤ Kev * Bud := Nat.mul_le_mul_left _ h3'
      nlinarith [hA1', hA2', hA3']
  -- STEP 8: the positive list to the top
  have e8 : WordR main (rollP 1) (fun vs => vs = A7) (fun _ out => out = A8)
      (fun _ => C8 * Bud) := by
    refine plwConseq (hroll main 1) ?_ ?_ ?_
    · intro vs hv; subst hv; rw [hA7]; simp
    · intro vs out hv hq
      subst hv
      rw [hq, hA7, hA8, plwGetD1_erase1_4]
    · intro vs hv
      subst hv
      rw [hA7, plwTake2_vsz_sum, Work.ConvR.vsz_int, hC8]
      have h1 : Kroll * HvdH.isz (h2 : ℤ) ≤ Kroll * (12 * Bud) := Nat.mul_le_mul_left _ hL2
      have h2 : Kroll * HvdH.vsz Pv ≤ Kroll * Bud := Nat.mul_le_mul_left _ hVP
      have h3 : Kroll ≤ Kroll * Bud := by
        calc Kroll = Kroll * 1 := (Nat.mul_one _).symm
          _ ≤ Kroll * Bud := Nat.mul_le_mul_left _ hB1
      nlinarith [h1, h2, h3]
  -- STEP 9: bury the first result below the base
  have e9 : WordR main (rollP 2) (fun vs => vs = A8) (fun _ out => out = A9)
      (fun _ => C9 * Bud) := by
    refine plwConseq (hroll main 2) ?_ ?_ ?_
    · intro vs hv; subst hv; rw [hA8]; simp
    · intro vs out hv hq
      subst hv
      rw [hq, hA8, hA9, plwGetD2_erase2_4]
    · intro vs hv
      subst hv
      rw [hA8, plwTake3_vsz_sum, hBv, Work.ConvR.vsz_int, hC9]
      have h1 : Kroll * HvdH.isz (h2 : ℤ) ≤ Kroll * (12 * Bud) := Nat.mul_le_mul_left _ hL2
      have h2 : Kroll * HvdH.vsz Pv ≤ Kroll * Bud := Nat.mul_le_mul_left _ hVP
      have h3 : Kroll * HvdH.isz (b : ℤ) ≤ Kroll * Bud := Nat.mul_le_mul_left _ hIszB
      have h4 : Kroll ≤ Kroll * Bud := by
        calc Kroll = Kroll * 1 := (Nat.mul_one _).symm
          _ ≤ Kroll * Bud := Nat.mul_le_mul_left _ hB1
      nlinarith [h1, h2, h3, h4]
  -- STEP 10: the base to the top
  have e10 : WordR main (rollP 1) (fun vs => vs = A9) (fun _ out => out = A10)
      (fun _ => C11 * Bud) := by
    refine plwConseq (hroll main 1) ?_ ?_ ?_
    · intro vs hv; subst hv; rw [hA9]; simp
    · intro vs out hv hq
      subst hv
      rw [hq, hA9, hA10, plwGetD1_erase1_4]
    · intro vs hv
      subst hv
      rw [hA9, plwTake2_vsz_sum, hBv, Work.ConvR.vsz_int, hC11]
      have h1 : Kroll * HvdH.isz (b : ℤ) ≤ Kroll * Bud := Nat.mul_le_mul_left _ hIszB
      have h2 : Kroll * HvdH.vsz Pv ≤ Kroll * Bud := Nat.mul_le_mul_left _ hVP
      have h3 : Kroll ≤ Kroll * Bud := by
        calc Kroll = Kroll * 1 := (Nat.mul_one _).symm
          _ ≤ Kroll * Bud := Nat.mul_le_mul_left _ hB1
      nlinarith [h1, h2, h3]
  -- STEP 11: evaluate the positive digit list (consumes the base)
  have e11 : WordR main evP (fun vs => vs = A10) (fun _ out => out = A11)
      (fun _ => C7 * Bud) := by
    have hbnd1 : ∀ h ∈ hs1, h < 2 ^ (3 * b) := by
      intro h hh
      rw [hhs1] at hh
      obtain ⟨y, hy, hyeq⟩ := List.mem_map.mp hh
      rw [← hyeq]
      exact lt_of_le_of_lt (plwToNat_max_pos_le y) (hx y hy)
    have hev1 := hev main hs1 b hb hbnd1
    refine plwConseq hev1 ?_ ?_ ?_
    · intro vs hv
      subst hv
      exact ⟨Val.int (h2 : ℤ) :: tl, by rw [hA10, hPv, hBv]⟩
    · intro vs out hv hq
      subst hv
      obtain ⟨r, hr, hout⟩ := hq
      rw [hA10, hPv, hBv] at hr
      simp only [List.cons.injEq] at hr
      obtain ⟨-, -, hrr⟩ := hr
      rw [hout, hA11, ← hh1, ← hrr]
    · intro vs hv
      rw [hC7]
      have hl : hs1.length * (b + 1) = xs.length * (b + 1) := by
        congr 1; rw [hhs1, List.length_map]
      have h3' : HvdH.isz (b : ℤ) + 1 ≤ Bud := by rw [hBud]; omega
      have hA1' : Kev * (hs1.map fun h => HvdH.isz (h : ℤ)).sum ≤ Kev * Bud :=
        Nat.mul_le_mul_left _ hS1
      have hA2' : Kev * (hs1.length * (b + 1)) ≤ Kev * Bud := by
        rw [hl]; exact Nat.mul_le_mul_left _ hnb
      have hA3' : Kev * (HvdH.isz (b : ℤ) + 1) ≤ Kev * Bud := Nat.mul_le_mul_left _ h3'
      nlinarith [hA1', hA2', hA3']
  -- STEP 12: subtract
  have e12 : WordR main subP (fun vs => vs = A11) (fun _ out => out = A12)
      (fun _ => C10 * Bud) := by
    refine plwConseq (hsub main) ?_ ?_ ?_
    · intro vs hv
      subst hv
      exact ⟨h1, h2, tl, by rw [hA11], trivial⟩
    · intro vs out hv hq
      subst hv
      obtain ⟨a, b, r, hvs, hout⟩ := hq
      rw [hA11] at hvs
      simp only [List.cons.injEq, HvdH.Val.int.injEq] at hvs
      obtain ⟨ha, hb', hr⟩ := hvs
      rw [hout, ← ha, ← hb', ← hr, hA12]
    · intro vs hv
      subst hv
      rw [hA11, hC10]
      show Ksub * (HvdH.isz (h1 : ℤ) + HvdH.isz (h2 : ℤ)) ≤ (60 * Ksub + 1) * Bud
      have hA1' : Ksub * HvdH.isz (h1 : ℤ) ≤ Ksub * (12 * Bud) := Nat.mul_le_mul_left _ hL1
      have hA2' : Ksub * HvdH.isz (h2 : ℤ) ≤ Ksub * (12 * Bud) := Nat.mul_le_mul_left _ hL2
      nlinarith [hA1', hA2']
  -- assemble
  have e1211 := plwSeq e11 e12
  have e121110 := plwSeq e10 e1211
  have e1211109 := plwSeq e9 e121110
  have e12111098 := plwSeq e8 e1211109
  have e121110987 := plwSeq e7 e12111098
  have e1211109876 := plwSeq e6 e121110987
  have e12111098765 := plwSeq e5 e1211109876
  have e121110987654 := plwSeq e4 e12111098765
  have e1211109876543 := plwSeq e3 e121110987654
  have e12111098765432 := plwSeq e2 e1211109876543
  have eall := plwSeq e1 e12111098765432
  refine plwConseq eall ?_ ?_ ?_
  · intro vs hv
    rw [hv, hA0, hLv, hBv]
  · intro vs out hv hq
    rw [hq, hA12]
    have hpk : ((h1 : ℤ) - (h2 : ℤ)) = Work.KronP.pack xs b := by
      rw [packEvalSub]
    rw [hpk]
  · intro vs hv
    beta_reduce
    show (List.map (fun c => c * Bud) [C1, C2, C3, C4, C5, C3, C7, C8, C9, C11, C7, C10]).sum ≤
      Kk * Bud
    rw [plwSum_mul_bud, hKk]

end Work.KronP
