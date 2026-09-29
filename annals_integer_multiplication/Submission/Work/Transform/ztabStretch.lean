import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.Kernel.Raw
import Submission.Work.ConvR.basic

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.Transform

open HvdH

/-! ## List facts about `(replicate k xs).flatten` -/

/-- Sum of a constant list. -/
theorem ztsSumReplicate (k c : ℕ) : (List.replicate k c).sum = k * c := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.sum_cons, ih]; ring

/-- Length of a replicated-and-flattened list. -/
theorem ztsLengthReplicateFlatten {α : Type*} (k : ℕ) (xs : List α) :
    (List.replicate k xs).flatten.length = k * xs.length := by
  rw [List.length_flatten, List.map_replicate, ztsSumReplicate]

/-- `map` distributes over a replicated-and-flattened list. -/
theorem ztsMapReplicateFlatten {α β : Type*} (f : α → β) (k : ℕ) (xs : List α) :
    (List.replicate k (xs.map f)).flatten = ((List.replicate k xs).flatten).map f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.replicate_succ, List.flatten_cons, List.flatten_cons,
      List.map_append, ih]

/-- Indexing a replicated-and-flattened list: the `i`-th entry is the `(i % xs.length)`-th entry
of `xs` (for `i` in range). -/
theorem ztsGetDReplicateFlatten {α : Type*} (k : ℕ) (xs : List α) (d : α) :
    ∀ i, i < k * xs.length →
      ((List.replicate k xs).flatten).getD i d = xs.getD (i % xs.length) d := by
  induction k with
  | zero => intro i hi; simp at hi
  | succ k ih =>
    intro i hi
    rcases xs with _ | ⟨a, t⟩
    · simp
    · have hi' : i < t.length + 1 + k * (t.length + 1) := by
        rw [Nat.succ_mul, List.length_cons] at hi
        omega
      rw [List.replicate_succ, List.flatten_cons]
      by_cases hlt : i < t.length + 1
      · have hlt' : i < (a :: t).length := hlt
        rw [List.getD_append _ _ _ _ hlt', Nat.mod_eq_of_lt hlt']
      · have hle : t.length + 1 ≤ i := Nat.le_of_not_lt hlt
        have hle' : (a :: t).length ≤ i := hle
        rw [List.getD_append_right _ _ _ _ hle']
        have hik' : i - (a :: t).length < k * (a :: t).length := by
          simp only [List.length_cons]
          omega
        rw [ih (i - (a :: t).length) hik']
        rw [Nat.mod_eq_sub_mod hle']

/-- Size of an `ofList` of a replicated value. -/
theorem ztsVszOfListReplicate (k : ℕ) (v : Val) :
    vsz (ofList (List.replicate k v)) = k * (vsz v + 1) + 1 := by
  rw [Work.ConvR.vsz_ofList, List.map_replicate, ztsSumReplicate, List.length_replicate]
  ring

/-- `isz` of a positive natural number is at most three times it. -/
theorem ztsIszLe (k : ℕ) (hk : 1 ≤ k) : isz (k : ℤ) ≤ 3 * k := by
  simp only [isz, Int.natAbs_natCast]
  have h : k.size ≤ k := Nat.size_le.mpr Nat.lt_two_pow_self
  omega

/-- The arithmetic of the stretch cost bound. -/
theorem ztsCostArith (Kr Kf k A : ℕ) (hk : 1 ≤ k) (hA : 1 ≤ A) :
    Kr * ((k + 1) * A + isz (k : ℤ) + 1) + Kf * (k * A + 2)
      ≤ (6 * Kr + 3 * Kf) * (k * A + 1) := by
  have hisz : isz (k : ℤ) ≤ 3 * k := ztsIszLe k hk
  have hAle : A ≤ k * A := by
    calc A = 1 * A := by ring
      _ ≤ k * A := Nat.mul_le_mul_right A hk
  have hkle : k ≤ k * A := by
    calc k = k * 1 := by ring
      _ ≤ k * A := Nat.mul_le_mul_left k hA
  have hisz' : isz (k : ℤ) ≤ 3 * (k * A) :=
    le_trans hisz (Nat.mul_le_mul_left 3 hkle)
  have h1 : (k + 1) * A + isz (k : ℤ) + 1 ≤ 6 * (k * A + 1) := by
    rw [Nat.succ_mul]
    have e : 6 * (k * A + 1) = 6 * (k * A) + 6 := by ring
    rw [e]
    omega
  have h2 : k * A + 2 ≤ 3 * (k * A + 1) := by omega
  calc Kr * ((k + 1) * A + isz (k : ℤ) + 1) + Kf * (k * A + 2)
      ≤ Kr * (6 * (k * A + 1)) + Kf * (3 * (k * A + 1)) :=
        Nat.add_le_add (Nat.mul_le_mul_left Kr h1) (Nat.mul_le_mul_left Kf h2)
    _ = (6 * Kr + 3 * Kf) * (k * A + 1) := by ring

/-- **The stretch: replicate `k` copies of a length-`r` vector and flatten.**

From `int k :: cvecVal bs` (with `1 ≤ k`), produce `cvecVal bs'` where `bs'` is the concatenation
of `k` copies of `bs` — so `bs'.length = k * bs.length` and, for `i < k * bs.length`,
`bs'[i] = bs[i % bs.length]`.  Intended implementation: `LayoutLib.replicate k (cvecVal bs)`
(giving `ofList (List.replicate k (cvecVal bs))`) followed by `LayoutLib.flatten` (whose pre is
`ofList (xss.map ofList)` with `xss = List.replicate k (bs.map cfxVal)`, using
`cvecVal bs = ofList (bs.map cfxVal)`), composed with `KernelLib.seq`.

Cost: `replicate` costs `K_rep * ((k+1)*(vsz v + 1) + isz k + 1)` with `v = cvecVal bs`, and
`flatten` costs `K_fl * (vsz (ofList (List.replicate k (cvecVal bs))) + 1)`
`= K_fl * (k * (vsz v + 1) + 1)`.  Since `vsz v ≥ 1` and `1 ≤ k`, both `isz k ≤ 3k ≤ 3k*(vsz v + 1)`
and the `+1`s are absorbed into `K * (k * (vsz (cvecVal bs) + 1) + 1)`.

The list-index equality follows from `(List.replicate k xs).flatten = xs ++ ... ++ xs` and
`List.getD_append` (`i % xs.length` is the offset inside the copy `i / xs.length`); when `bs = []`
the range `i < k * 0 = 0` is empty. -/
theorem ztabStretch : HvdH.KernelLib → HvdH.LayoutLib →
    ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (k : ℕ) (bs : List (ℤ × ℤ)) (rest : List HvdH.Val),
      1 ≤ k →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.int ((k : ℤ)) :: HvdH.cvecVal bs :: rest)
        (fun _ out => ∃ bs', out = HvdH.cvecVal bs' :: rest ∧
          bs'.length = k * bs.length ∧
          ∀ i < k * bs.length, bs'.getD i (0, 0) = bs.getD (i % bs.length) (0, 0))
        (fun _ => K * (k * (HvdH.vsz (HvdH.cvecVal bs) + 1) + 1)) := by
  intro hK hL
  obtain ⟨repP, Kr, hrep⟩ := hL.replicate
  obtain ⟨flaP, Kf, hfla⟩ := hL.flatten
  refine ⟨Cmd.seq repP flaP, 6 * Kr + 3 * Kf, ?_⟩
  intro main k bs rest hk
  -- step 1: replicate the value `cvecVal bs` `k` times
  have h1 : WordR main repP
      (fun vs => vs = Val.int (k : ℤ) :: cvecVal bs :: rest)
      (fun _ out => out = ofList (List.replicate k (cvecVal bs)) :: rest)
      (fun _ => Kr * ((k + 1) * (vsz (cvecVal bs) + 1) + isz (k : ℤ) + 1)) := by
    refine Work.Kernel.WordR_conseq (hrep main k (cvecVal bs)) ?_ ?_ ?_
    · intro vs hvs
      exact ⟨rest, hvs⟩
    · intro vs out hvs hout
      obtain ⟨r, hvr, houtr⟩ := hout
      have hr : r = rest := by
        rw [hvs] at hvr
        exact ((List.cons.inj (List.cons.inj hvr).2).2).symm
      rw [houtr, hr]
    · intro vs _
      exact le_rfl
  -- step 2: flatten the replicated list
  have h2 : WordR main flaP
      (fun vs => vs = ofList (List.replicate k (cvecVal bs)) :: rest)
      (fun _ out => ∃ bs', out = cvecVal bs' :: rest ∧
        bs'.length = k * bs.length ∧
        ∀ i < k * bs.length, bs'.getD i (0, 0) = bs.getD (i % bs.length) (0, 0))
      (fun _ => Kf * (k * (vsz (cvecVal bs) + 1) + 2)) := by
    refine Work.Kernel.WordR_conseq
      (hfla main (List.replicate k (bs.map cfxVal))) ?_ ?_ ?_
    · intro vs hvs
      refine ⟨rest, ?_⟩
      rw [hvs, List.map_replicate]
      rfl
    · intro vs out hvs hout
      obtain ⟨r, hvr, houtr⟩ := hout
      have hmap : (List.replicate k (bs.map cfxVal)).map ofList
          = List.replicate k (cvecVal bs) := by
        rw [List.map_replicate]; rfl
      have hr : r = rest := by
        rw [hvs, hmap] at hvr
        exact ((List.cons.inj hvr).2).symm
      refine ⟨(List.replicate k bs).flatten, ?_, ?_, ?_⟩
      · rw [houtr, hr, ztsMapReplicateFlatten]
        rfl
      · exact ztsLengthReplicateFlatten k bs
      · intro i hi
        exact ztsGetDReplicateFlatten k bs (0, 0) i hi
    · intro vs _
      rw [List.map_replicate]
      rw [ztsVszOfListReplicate]
      exact le_rfl
  -- compose
  have hseq := hK.seq main repP flaP
    (fun vs => vs = Val.int (k : ℤ) :: cvecVal bs :: rest)
    (fun _ out => out = ofList (List.replicate k (cvecVal bs)) :: rest)
    (fun _ => Kr * ((k + 1) * (vsz (cvecVal bs) + 1) + isz (k : ℤ) + 1))
    (fun vs => vs = ofList (List.replicate k (cvecVal bs)) :: rest)
    (fun _ out => ∃ bs', out = cvecVal bs' :: rest ∧
      bs'.length = k * bs.length ∧
      ∀ i < k * bs.length, bs'.getD i (0, 0) = bs.getD (i % bs.length) (0, 0))
    (fun _ => Kf * (k * (vsz (cvecVal bs) + 1) + 2))
    (fun _ => Kf * (k * (vsz (cvecVal bs) + 1) + 2))
    h1 h2 (by intro vs mid _ hmid; exact ⟨hmid, le_rfl⟩)
  refine Work.Kernel.WordR_conseq (p := Cmd.seq repP flaP) hseq ?_ ?_ ?_
  · intro vs hvs; exact hvs
  · intro vs out _ hpost
    obtain ⟨mid, -, hpost'⟩ := hpost
    exact hpost'
  · intro vs _
    exact ztsCostArith Kr Kf k (vsz (cvecVal bs) + 1) hk (by omega)

end Work.Transform
