import Mathlib
import Submission.Work.Resample.auPrepDefs
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.Resample.auMapListTail
import Submission.Work.Resample.auWtLCostArith

namespace Work.Resample

open HvdH

/-!
# `Work.Resample.auWtLWord`: the weight-list word of one resampling record

Given an element word (`hElem`, the conclusion of `Work.Resample.auInnerElem`) turning the window

`[cons (int i) (int (auPi p)), int C, int t, int p, int α]`

into

`[int (auWt p α t ((C + t·i)²)), int C, int t, int p, int α]`,

this file builds the word that maps it over the `auL p α` labels of one output `k`, turning

`[int (auL p α), int (auPi p), int (auC p α s t k), int t, int p, int α]`

into

`[ofList (auWtL p α s t k), int (auC p α s t k), int t, int p, int α]`.

The construction is `replicate` (`auL p α` copies of the payload `int (auPi p)`), then `enumerate`
(label them `cons (int i) (int (auPi p))`, giving `auKs p (auL p α)`), then `KernelLib.mapList`
with the given element word (`auMapListTail`).  The cost is `K * (p+1)^K`, absorbed by
`auWtLCostArith`.
-/

/-! ## Size bookkeeping -/

/-- `vsz` of an integer value is `isz`. -/
theorem auVsz_int (z : ℤ) : vsz (Val.int z) = isz z := by
  show (Val.int z).enc.length = isz z
  exact Work.IntLib.vsz_int z

/-- `vsz` of a `cons` value. -/
theorem auVsz_cons (a b : Val) : vsz (Val.cons a b) = 1 + vsz a + vsz b := by
  simp only [vsz, Val.enc, List.length_cons, List.length_append]
  omega

/-- `vsz` of a list value. -/
theorem auVsz_ofList (l : List Val) : vsz (ofList l) = l.length + 1 + (l.map vsz).sum := by
  induction l with
  | nil => simp [ofList, vsz, Val.enc]
  | cons v vs ih =>
    have h : ofList (v :: vs) = Val.cons v (ofList vs) := rfl
    rw [h, auVsz_cons, ih]
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    ring

/-! ## The element function on labels -/

/-- Read the index `i` out of a label `cons (int i) _` and return the corresponding weight value. -/
def auWtLOf (p α s t k : ℕ) : Val → Val
  | .cons (.int i) _ => .int (auWt p α t (auNsq p α s t k i.toNat))
  | _ => .nil

theorem auWtLOf_cons (p α s t k : ℕ) (i : ℤ) (v : Val) :
    auWtLOf p α s t k (.cons (.int i) v) = .int (auWt p α t (auNsq p α s t k i.toNat)) := rfl

/-- Membership in the label list. -/
theorem mem_auKs_iff {p t : ℕ} {x : Val} :
    x ∈ auKs p t ↔ ∃ k < t, x = Val.cons (.int (k : ℤ)) (.int (auPi p)) := by
  constructor
  · intro hx
    rw [auKs, List.mem_map] at hx
    obtain ⟨k, hk, hk'⟩ := hx
    exact ⟨k, List.mem_range.mp hk, hk'.symm⟩
  · rintro ⟨k, hk, rfl⟩
    rw [auKs, List.mem_map]
    exact ⟨k, List.mem_range.mpr hk, rfl⟩

/-- Mapping the element function over the labels gives the weight list. -/
theorem map_auWtLOf (p α s t k : ℕ) :
    (auKs p (auL p α)).map (auWtLOf p α s t k) = auWtL p α s t k := by
  simp only [auKs, auWtL, List.map_map]
  apply List.map_congr_left
  intro i _
  show auWtLOf p α s t k (.cons (.int (i : ℤ)) (.int (auPi p)))
    = .int (auWt p α t (auNsq p α s t k i))
  rw [auWtLOf_cons, Int.toNat_natCast]

/-! ## The main theorem -/

theorem auWtLWord (hk : HvdH.KernelLib) (hl : HvdH.LayoutLib)
    (hElem : ∃ (progE : HvdH.Cmd) (KE : ℕ), ∀ (main : HvdH.Cmd) (p α t : ℕ) (C : ℤ) (i : ℕ),
      HvdH.isz C ≤ Work.Resample.auSZ p → HvdH.isz ((i : ℕ) : ℤ) ≤ Work.Resample.auSZ p →
      (1 ≤ t) → (t < 2 ^ p) → (α ≤ 2 ^ p) →
      (C + (t : ℤ) * (i : ℤ)) ^ 2 ≤ (2 : ℤ) ^ (4 * p + 8) →
      Work.Resample.Pipe main progE
        [HvdH.Val.cons (HvdH.Val.int (i : ℤ)) (HvdH.Val.int (Work.Resample.auPi p)),
          HvdH.Val.int C, HvdH.Val.int (t : ℤ), HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ)]
        [HvdH.Val.int (Work.Resample.auWt p α t ((C + (t : ℤ) * (i : ℤ)) ^ 2)),
          HvdH.Val.int C, HvdH.Val.int (t : ℤ), HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ)]
        (KE * (p + 1) ^ KE)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t k : ℕ) (hs : 2 ≤ s) (hst : s < t)
      (htp : t < 2 ^ p) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p) (hklt : k < t)
      (hLle : Work.Resample.auL p α ≤ 4 * p + 1)
      (hLsz : HvdH.isz ((Work.Resample.auL p α : ℕ) : ℤ) ≤ Work.Resample.auSZ p)
      (hCsz : HvdH.isz (Work.Resample.auC p α s t k) ≤ Work.Resample.auSZ p)
      (hI : ∀ i, i < Work.Resample.auL p α → HvdH.isz ((i : ℕ) : ℤ) ≤ Work.Resample.auSZ p)
      (hN : ∀ i < Work.Resample.auL p α, 0 ≤ Work.Resample.auNsq p α s t k i ∧
        Work.Resample.auNsq p α s t k i ≤ (2 : ℤ) ^ (4 * p + 8))
      (hWtsz : ∀ N : ℤ, 0 ≤ N → HvdH.isz (Work.Resample.auWt p α t N) ≤ Work.Resample.auSZ p),
      Work.Resample.Pipe main prog
        [HvdH.Val.int ((Work.Resample.auL p α : ℕ) : ℤ), HvdH.Val.int (Work.Resample.auPi p),
          HvdH.Val.int (Work.Resample.auC p α s t k), HvdH.Val.int (t : ℤ),
          HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ)]
        [HvdH.ofList (Work.Resample.auWtL p α s t k), HvdH.Val.int (Work.Resample.auC p α s t k),
          HvdH.Val.int (t : ℤ), HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ)]
        (K * (p + 1) ^ K) := by
  obtain ⟨repProg, Krep, hRep⟩ := hl.replicate
  obtain ⟨enProg, Kenum, hEnum⟩ := hl.enumerate
  obtain ⟨comb, Kml, hML⟩ := MapListField.of_kernel hk
  obtain ⟨elemProg, KE, hElemP⟩ := hElem
  refine ⟨Cmd.seq (Cmd.seq repProg enProg) (comb elemProg), 2 ^ (Krep + Kenum + Kml + KE + 40), ?_⟩
  intro main p α s t k hs hst htp hα hp hαp hklt hLle hLsz hCsz hI hN hWtsz
  -- the size bounds consumed by the cost estimate
  have hpi : isz (auPi p) ≤ auSZ p := isz_auPi_le p
  have hV1 : vsz (.int (auPi p)) ≤ auSZ p := by rw [auVsz_int]; exact hpi
  have hV3 : vsz (ofList (List.replicate (auL p α) (.int (auPi p))))
      ≤ auL p α * (auSZ p + 1) + 1 := by
    rw [auVsz_ofList, List.length_replicate, List.map_replicate]
    have hsum : (List.replicate (auL p α) (vsz (.int (auPi p)))).sum
        = auL p α * vsz (.int (auPi p)) := by
      rw [List.sum_replicate, smul_eq_mul]
    rw [hsum]
    have hmul : auL p α * vsz (.int (auPi p)) ≤ auL p α * auSZ p :=
      Nat.mul_le_mul_left _ hV1
    have hdist : auL p α * (auSZ p + 1) = auL p α * auSZ p + auL p α := by ring
    omega
  -- the sizes of the label list and of the produced weight list
  have hx : ∀ x ∈ auKs p (auL p α), vsz x ≤ 1 + 2 * auSZ p := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_auKs_iff.mp hx
    rw [auVsz_cons, auVsz_int, auVsz_int]
    have h1 := hI i hi
    have h2 := hpi
    omega
  have hy : ∀ x ∈ auKs p (auL p α), vsz (auWtLOf p α s t k x) ≤ 1 + 2 * auSZ p := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_auKs_iff.mp hx
    rw [auWtLOf_cons, Int.toNat_natCast, auVsz_int]
    have hN0 : 0 ≤ auNsq p α s t k i := (hN i hi).1
    have h1 := hWtsz (auNsq p α s t k i) hN0
    omega
  -- the element word, stated on the window `x :: T`
  have helemW : ∀ x ∈ auKs p (auL p α),
      Pipe main elemProg
        (x :: [.int (auC p α s t k), .int (t : ℤ), .int (p : ℤ), .int (α : ℤ)])
        (auWtLOf p α s t k x :: [.int (auC p α s t k), .int (t : ℤ), .int (p : ℤ), .int (α : ℤ)])
        (KE * (p + 1) ^ KE) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_auKs_iff.mp hx
    have hsq : (auC p α s t k + (t : ℤ) * (i : ℤ)) ^ 2 ≤ (2 : ℤ) ^ (4 * p + 8) := by
      rw [← auNsq_eq_C]
      exact (hN i hi).2
    have hαp' : α ≤ 2 ^ p := by
      have h1 : α * α < p := by simpa [pow_two] using hαp
      have h2 : α ≤ α * α := Nat.le_mul_self α
      have h3 : α < p := by omega
      exact le_trans (le_of_lt h3) (le_of_lt Nat.lt_two_pow_self)
    have h := hElemP main p α t (auC p α s t k) i hCsz (hI i hi) (by omega) htp hαp' hsq
    refine Pipe.rw h ?_
    rw [auWtLOf_cons, Int.toNat_natCast, auNsq_eq_C]
  -- the three phases
  have h1 : Pipe main repProg
      [.int ((auL p α : ℕ) : ℤ), .int (auPi p)]
      [ofList (List.replicate (auL p α) (.int (auPi p)))]
      (Krep * (((auL p α) + 1) * (vsz (.int (auPi p)) + 1)
        + isz (((auL p α : ℕ) : ℤ)) + 1)) :=
    Pipe.replicate main hRep
  have h2 : Pipe main enProg
      [ofList (List.replicate (auL p α) (.int (auPi p)))]
      [ofList (auKs p (auL p α))]
      (Kenum * (vsz (ofList (List.replicate (auL p α) (.int (auPi p))))
        + (auL p α) * ((auL p α).size + 1) + 1)) := by
    refine Pipe.rw (Pipe.le (Pipe.enumerate (main := main) (prog := enProg) (K := Kenum) hEnum
      (xs := List.replicate (auL p α) (.int (auPi p)))) ?_) ?_
    · rw [List.length_replicate]
    · rw [auKs, enumerate_replicate]
  have h3 : Pipe main (comb elemProg)
      (ofList (auKs p (auL p α))
        :: [.int (auC p α s t k), .int (t : ℤ), .int (p : ℤ), .int (α : ℤ)])
      (ofList (auWtL p α s t k)
        :: [.int (auC p α s t k), .int (t : ℤ), .int (p : ℤ), .int (α : ℤ)])
      (auL p α * (KE * (p + 1) ^ KE + Kml * ((1 + 2 * auSZ p) + 1)) + Kml) := by
    have hml := auMapListTail (comb := comb) (Kml := Kml) hML helemW hx hy
    have hlen : (auKs p (auL p α)).length = auL p α := by simp [auKs]
    rw [hlen] at hml
    refine Pipe.rw hml ?_
    rw [map_auWtLOf]
  have h12 : Pipe main (.seq repProg enProg)
      ([.int ((auL p α : ℕ) : ℤ), .int (auPi p)]
        ++ [.int (auC p α s t k), .int (t : ℤ), .int (p : ℤ), .int (α : ℤ)])
      ([ofList (auKs p (auL p α))]
        ++ [.int (auC p α s t k), .int (t : ℤ), .int (p : ℤ), .int (α : ℤ)])
      ((Krep * (((auL p α) + 1) * (vsz (.int (auPi p)) + 1)
          + isz (((auL p α : ℕ) : ℤ)) + 1))
        + (Kenum * (vsz (ofList (List.replicate (auL p α) (.int (auPi p))))
          + (auL p α) * ((auL p α).size + 1) + 1))) :=
    Pipe.comp (Pipe.appendTail _ h1) (Pipe.appendTail _ h2)
  have hall : Pipe main (Cmd.seq (Cmd.seq repProg enProg) (comb elemProg))
      ([.int ((auL p α : ℕ) : ℤ), .int (auPi p)]
        ++ [.int (auC p α s t k), .int (t : ℤ), .int (p : ℤ), .int (α : ℤ)])
      ([ofList (auWtL p α s t k)]
        ++ [.int (auC p α s t k), .int (t : ℤ), .int (p : ℤ), .int (α : ℤ)])
      (((Krep * (((auL p α) + 1) * (vsz (.int (auPi p)) + 1)
          + isz (((auL p α : ℕ) : ℤ)) + 1))
        + (Kenum * (vsz (ofList (List.replicate (auL p α) (.int (auPi p))))
          + (auL p α) * ((auL p α).size + 1) + 1)))
        + (auL p α * (KE * (p + 1) ^ KE + Kml * ((1 + 2 * auSZ p) + 1)) + Kml)) :=
    Pipe.comp h12 h3
  refine Pipe.le hall ?_
  exact auWtLCostArith hp hLle hV1 hLsz hV3 (by omega)

end Work.Resample
