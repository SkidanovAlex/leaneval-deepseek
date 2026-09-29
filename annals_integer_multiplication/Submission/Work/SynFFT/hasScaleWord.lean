import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.yMulProg

/-!
# `Work.SynFFT.hasScaleWord`

The word that multiplies every coefficient of every element of a fixed-point vector by a scalar
`m = ±1`:

`cvecVal w :: int m :: rest  ↦  cvecVal (w.map (fun z => (m*z.1, m*z.2))) :: int m :: rest`

at cost `O(|w| (p+1))`.  Here `cvecVal w` is the `StackLang` representation of a vector of
fixed-point complex numbers `2^{-p}(x + iy)` with `x² + y² ≤ 2^{2p}` (`inDisc`), so every
coordinate is `≤ 2^p` in absolute value and costs `O(p+1)` glyphs to copy or multiply.

The word is an instance of the kernel's `mapList` over the coefficient list `w`, with the
per-element word (`qScale`, see its docstring)

`cfxVal (a,b) :: int m :: rest ↦ cfxVal (m*a, m*b) :: int m :: rest`

built from `unconsV` (unpack the pair), `pick` (copy the scalar to the top — twice, once for
each coefficient, so that the parameter sitting in `rest` is *kept*), `roll` (bring the second
coefficient up), two `mulS` (schoolbook products by the `±1` scalar, so no size can grow),
`swap` and `consV` (re-pack in the right order).

The `WordR` plumbing (`WordR_seqC`, `uncStep`, ..., `mapStep`) is taken from
`Submission.Work.SynFFT.mrgBlkDefs` (namespace `Work.SynFFT.MrgKit`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Work.SynFFT

open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-! ## Small helpers -/

/-- Scale a fixed-point complex number by `m`, as a function on `Val`. -/
def scaleVal (m : ℤ) : Val → Val
  | .cons (.int a) (.int b) => .cons (.int (m * a)) (.int (m * b))
  | v => v

lemma scaleVal_cfxVal (m : ℤ) (z : ℤ × ℤ) :
    scaleVal m (cfxVal z) = cfxVal (m * z.1, m * z.2) := by
  rcases z with ⟨a, b⟩
  rfl

lemma sum_take2 (x y : Val) (t : List Val) :
    (((x :: y :: t).take 2).map vsz).sum = vsz x + vsz y := rfl

lemma sum_take3 (x y z : Val) (t : List Val) :
    (((x :: y :: z :: t).take 3).map vsz).sum = vsz x + (vsz y + vsz z) := rfl

/-- `isz (m * a) ≤ isz a` when `|m| ≤ 1` (multiplying by a sign cannot increase the bit-size). -/
lemma isz_mul_le (m a : ℤ) (hm : m.natAbs ≤ 1) : isz (m * a) ≤ isz a := by
  have hnat : (m * a).natAbs ≤ a.natAbs := by
    rw [Int.natAbs_mul]
    calc m.natAbs * a.natAbs ≤ 1 * a.natAbs := Nat.mul_le_mul_right _ hm
      _ = a.natAbs := one_mul _
  have hsz : (m * a).natAbs.size ≤ a.natAbs.size := Nat.size_le_size hnat
  simp only [isz]; omega

lemma natAbs_le_one_of_isz (m : ℤ) (hm : isz m ≤ 3) : m.natAbs ≤ 1 := by
  have h : m.natAbs.size ≤ 1 := by simp only [isz] at hm; omega
  have h2 : m.natAbs < 2 := (Nat.size_le (m := m.natAbs) (n := 1)).mp h
  omega

lemma isz_sign (m : ℤ) (hm : m = 1 ∨ m = -1) : isz m ≤ 3 := by
  rcases hm with rfl | rfl <;> decide

/-- A `Forall₂` whose relation is `y = scaleVal m x` determines the second list. -/
lemma forall₂_scaleVal (m : ℤ) {xs ys : List Val}
    (h : List.Forall₂ (fun x y => y = scaleVal m x) xs ys) : ys = xs.map (scaleVal m) := by
  induction h with
  | nil => rfl
  | cons hab _ ih => rw [hab, ih]; rfl

/-! ## The element word -/

/-- The per-element word of `hasScaleWord`: unpack `cfxVal (a,b)`, multiply both coefficients
by the scalar `m` sitting at index `0` of the tail, and re-pack (the scalar itself is left
untouched in the tail, so a `mapList` over the vector can use it for every element). -/
def qScale (uncP : Cmd) (pickP : ℕ → Cmd) (mulP : Cmd) (rollP : ℕ → Cmd)
    (swapP consP : Cmd) : Cmd :=
  ((((((uncP ;;; pickP 2) ;;; mulP) ;;; rollP 1) ;;; pickP 2) ;;; mulP) ;;; swapP) ;;; consP

/-- The specification of `qScale` with an explicit constant cost. -/
theorem qScale_wordR {main : Cmd} {uncP : Cmd} {pickP : ℕ → Cmd} {mulP : Cmd}
    {rollP : ℕ → Cmd} {swapP consP : Cmd} {Kuc Kp Km Kr Ksw Kcv : ℕ}
    (hunc : WordR main uncP (fun vs => ∃ a b rest, vs = .cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest) (fun _ => Kuc))
    (hpick : ∀ k, WordR main (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => Kp * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hmul : BinOp main mulP (fun _ _ => True) (· * ·) (fun a b => Km * isz a * isz b))
    (hroll : ∀ k, WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hswap : WordR main swapP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Ksw * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (hcons : WordR main consP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => Kcv))
    (p : ℕ) (z : ℤ × ℤ) (m : ℤ) (rest : List Val) (hm0 : rest.getD 0 .nil = .int m)
    (hz1 : isz z.1 ≤ p + 3) (hz2 : isz z.2 ≤ p + 3) (hm3 : isz m ≤ 3)
    (D : ℕ) (hD : 8 * (100 * (Kuc + Kp + Km + Kr + Ksw + Kcv + 1) * (p + 1)) ≤ D) :
    WordR main (qScale uncP pickP mulP rollP swapP consP)
      (fun vs => vs = cfxVal z :: rest)
      (fun _ out => out = cfxVal (m * z.1, m * z.2) :: rest) (fun _ => D) := by
  obtain ⟨rest', rfl⟩ : ∃ rest', rest = .int m :: rest' := by
    cases rest with
    | nil => exact absurd hm0 (by simp)
    | cons x xs =>
      have hx : x = .int m := by simpa using hm0
      exact ⟨xs, by rw [hx]⟩
  set Ksum : ℕ := Kuc + Kp + Km + Kr + Ksw + Kcv + 1 with hKsum
  set Ds : ℕ := 100 * Ksum * (p + 1) with hDs
  have hKu : Kuc ≤ Ksum := by omega
  have hKp : Kp ≤ Ksum := by omega
  have hKm : Km ≤ Ksum := by omega
  have hKr : Kr ≤ Ksum := by omega
  have hKsw : Ksw ≤ Ksum := by omega
  have hKcv : Kcv ≤ Ksum := by omega
  have bd : ∀ (Ki x : ℕ), Ki ≤ Ksum → x ≤ 100 * (p + 1) → Ki * x ≤ Ds := by
    intro Ki x h1 h2
    calc Ki * x ≤ Ksum * (100 * (p + 1)) := Nat.mul_le_mul h1 h2
      _ = Ds := by rw [hDs]; ring
  have hmabs : m.natAbs ≤ 1 := natAbs_le_one_of_isz m hm3
  have hma : isz (m * z.1) ≤ p + 3 := le_trans (isz_mul_le m z.1 hmabs) hz1
  have hmb : isz (m * z.2) ≤ p + 3 := le_trans (isz_mul_le m z.2 hmabs) hz2
  have hmp : isz m ≤ p + 3 := by omega
  -- step 1: unpack the pair
  have s1 : WordR main uncP (fun vs => vs = .cons (.int z.1) (.int z.2) :: .int m :: rest')
      (fun _ out => out = .int z.1 :: .int z.2 :: .int m :: rest') (fun _ => Ds) := by
    refine MrgKit.uncStep hunc (.int z.1) (.int z.2) (.int m :: rest') Ds ?_
    have h := bd Kuc 1 hKu (by omega)
    simpa using h
  -- step 2: copy the scalar to the top
  have s2 : WordR main (pickP 2) (fun vs => vs = .int z.1 :: .int z.2 :: .int m :: rest')
      (fun _ out => out = .int m :: .int z.1 :: .int z.2 :: .int m :: rest') (fun _ => Ds) := by
    refine MrgKit.pickStep hpick 2 (.int z.1 :: .int z.2 :: .int m :: rest') (by simp) Ds ?_
    rw [sum_take3, MrgKit.vsz_int', MrgKit.vsz_int', MrgKit.vsz_int']
    rw [Nat.mul_assoc]
    refine bd Kp ((2 + 1) * (isz z.1 + (isz z.2 + isz m) + 1)) hKp ?_
    omega
  -- step 3: first coordinate times the scalar
  have s3 : WordR main mulP (fun vs => vs = .int m :: .int z.1 :: .int z.2 :: .int m :: rest')
      (fun _ out => out = .int (m * z.1) :: .int z.2 :: .int m :: rest') (fun _ => Ds) := by
    refine MrgKit.mulStep hmul m z.1 (.int z.2 :: .int m :: rest') Ds ?_
    rw [Nat.mul_assoc]
    refine bd Km (isz m * isz z.1) hKm ?_
    have h : isz m * isz z.1 ≤ 3 * (p + 3) := Nat.mul_le_mul hm3 hz1
    omega
  -- step 4: bring the second coordinate to the top
  have s4 : WordR main (rollP 1) (fun vs => vs = .int (m * z.1) :: .int z.2 :: .int m :: rest')
      (fun _ out => out = .int z.2 :: .int (m * z.1) :: .int m :: rest') (fun _ => Ds) := by
    refine MrgKit.rollStep hroll 1 (.int (m * z.1) :: .int z.2 :: .int m :: rest') (by simp) Ds ?_
    rw [sum_take2, MrgKit.vsz_int', MrgKit.vsz_int']
    rw [Nat.mul_assoc]
    refine bd Kr ((1 + 1) * (isz (m * z.1) + isz z.2 + 1)) hKr ?_
    omega
  -- step 5: copy the scalar above the second coordinate (the parameter below is kept)
  have s5 : WordR main (pickP 2)
      (fun vs => vs = .int z.2 :: .int (m * z.1) :: .int m :: rest')
      (fun _ out => out = .int m :: .int z.2 :: .int (m * z.1) :: .int m :: rest') (fun _ => Ds) := by
    refine MrgKit.pickStep hpick 2 (.int z.2 :: .int (m * z.1) :: .int m :: rest') (by simp) Ds ?_
    rw [sum_take3, MrgKit.vsz_int', MrgKit.vsz_int', MrgKit.vsz_int']
    rw [Nat.mul_assoc]
    refine bd Kp ((2 + 1) * (isz z.2 + (isz (m * z.1) + isz m) + 1)) hKp ?_
    omega
  -- step 6: second coordinate times the scalar
  have s6 : WordR main mulP
      (fun vs => vs = .int m :: .int z.2 :: .int (m * z.1) :: .int m :: rest')
      (fun _ out => out = .int (m * z.2) :: .int (m * z.1) :: .int m :: rest') (fun _ => Ds) := by
    refine MrgKit.mulStep hmul m z.2 (.int (m * z.1) :: .int m :: rest') Ds ?_
    rw [Nat.mul_assoc]
    refine bd Km (isz m * isz z.2) hKm ?_
    have h : isz m * isz z.2 ≤ 3 * (p + 3) := Nat.mul_le_mul hm3 hz2
    omega
  -- step 7: restore the order of the coordinates
  have s7 : WordR main swapP
      (fun vs => vs = .int (m * z.2) :: .int (m * z.1) :: .int m :: rest')
      (fun _ out => out = .int (m * z.1) :: .int (m * z.2) :: .int m :: rest') (fun _ => Ds) := by
    refine MrgKit.swapStep hswap (.int (m * z.2) :: .int (m * z.1) :: .int m :: rest')
      (by simp) Ds ?_
    have e0 : ((.int (m * z.2) :: .int (m * z.1) :: .int m :: rest').getD 0 .nil) =
      .int (m * z.2) := rfl
    have e1 : ((.int (m * z.2) :: .int (m * z.1) :: .int m :: rest').getD 1 .nil) =
      .int (m * z.1) := rfl
    rw [e0, e1]
    refine bd Ksw (vsz (.int (m * z.2)) + vsz (.int (m * z.1)) + 1) hKsw ?_
    rw [MrgKit.vsz_int', MrgKit.vsz_int']
    omega
  -- step 8: re-pack the pair
  have s8 : WordR main consP
      (fun vs => vs = .int (m * z.1) :: .int (m * z.2) :: .int m :: rest')
      (fun _ out => out = .cons (.int (m * z.1)) (.int (m * z.2)) :: .int m :: rest')
      (fun _ => Ds) := by
    refine MrgKit.consStep hcons (.int (m * z.1)) (.int (m * z.2)) (.int m :: rest') Ds ?_
    have h := bd Kcv 1 hKcv (by omega)
    simpa using h
  have u1 := MrgKit.WordR_seqC s1 s2
  have u2 := MrgKit.WordR_seqC u1 s3
  have u3 := MrgKit.WordR_seqC u2 s4
  have u4 := MrgKit.WordR_seqC u3 s5
  have u5 := MrgKit.WordR_seqC u4 s6
  have u6 := MrgKit.WordR_seqC u5 s7
  have u7 := MrgKit.WordR_seqC u6 s8
  unfold qScale
  refine MrgKit.WordR_weaken u7 (fun vs hvs => hvs) ?_ ?_
  · intro vs out _ hout
    rw [hout]
    rfl
  · intro vs _
    clear u1 u2 u3 u4 u5 u6 u7 hunc hpick hmul hroll hswap hcons bd
      hz1 hz2 hm3 hma hmb hmp hmabs hKu hKp hKm hKr hKsw hKcv hKsum
    rw [hDs]
    exact le_trans (le_of_eq (by ring)) hD

/-! ## The vector word -/

/-- The same word applied to every element of a vector, via the kernel's `mapList`. -/
theorem scaleVec_wordR {main : Cmd} {uncP : Cmd} {pickP : ℕ → Cmd} {mulP : Cmd}
    {rollP : ℕ → Cmd} {swapP consP : Cmd} {mapP : Cmd → Cmd} {Kuc Kp Km Kr Ksw Kcv Kml : ℕ}
    (hunc : WordR main uncP (fun vs => ∃ a b rest, vs = .cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest) (fun _ => Kuc))
    (hpick : ∀ k, WordR main (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => Kp * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hmul : BinOp main mulP (fun _ _ => True) (· * ·) (fun a b => Km * isz a * isz b))
    (hroll : ∀ k, WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hswap : WordR main swapP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Ksw * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (hcons : WordR main consP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => Kcv))
    (hmap : ∀ (q : Cmd) (rest : List Val) (P : Val → Prop) (Q : Val → Val → Prop) (c L : ℕ),
      (∀ x, P x → WordR main q (fun vs => vs = x :: rest)
        (fun _ out => ∃ y, out = y :: rest ∧ Q x y ∧ vsz y ≤ L) (fun _ => c)) →
      ∀ xs : List Val, (∀ x ∈ xs, P x ∧ vsz x ≤ L) →
      WordR main (mapP q) (fun vs => vs = ofList xs :: rest)
        (fun _ out => ∃ ys, out = ofList ys :: rest ∧ List.Forall₂ Q xs ys)
        (fun _ => xs.length * (c + Kml * (L + 1)) + Kml))
    (p : ℕ) (m : ℤ) (w : List (ℤ × ℤ)) (rest : List Val)
    (hin : ∀ z ∈ w, inDisc p z) (hm1 : m = 1 ∨ m = -1) (hm0 : rest.getD 0 .nil = .int m) :
    WordR main (mapP (qScale uncP pickP mulP rollP swapP consP))
      (fun vs => vs = cvecVal w :: rest)
      (fun _ out => out = cvecVal (w.map fun z => (m * z.1, m * z.2)) :: rest)
      (fun _ => (1000 * (Kuc + Kp + Km + Kr + Ksw + Kcv + 1) + 9 * Kml) * (w.length + 1)
        * (p + 1)) := by
  set Ksum : ℕ := Kuc + Kp + Km + Kr + Ksw + Kcv + 1 with hKsum
  set D : ℕ := 1000 * Ksum * (p + 1) with hDdef
  have hm3 : isz m ≤ 3 := isz_sign m hm1
  have hDq : 8 * (100 * Ksum * (p + 1)) ≤ D := by
    rw [hDdef]
    calc 8 * (100 * Ksum * (p + 1)) = 800 * (Ksum * (p + 1)) := by ring
      _ ≤ 1000 * (Ksum * (p + 1)) := Nat.mul_le_mul_right (Ksum * (p + 1)) (by norm_num)
      _ = 1000 * Ksum * (p + 1) := by ring
  have hmem : ∀ z ∈ w, inDisc p z := hin
  refine MrgKit.mapStep hmap (qScale uncP pickP mulP rollP swapP consP) rest
    (fun x => ∃ z : ℤ × ℤ, x = cfxVal z ∧ inDisc p z) (fun x y => y = scaleVal m x)
    D (2 * p + 7) ?_ (w.map cfxVal) ?_ (cvecVal (w.map fun z => (m * z.1, m * z.2))) ?_
    ((1000 * Ksum + 9 * Kml) * (w.length + 1) * (p + 1)) ?_
  · intro x hx
    rcases hx with ⟨z, rfl, hz⟩
    refine MrgKit.WordR_weaken
      (qScale_wordR (main := main) hunc hpick hmul hroll hswap hcons p z m rest hm0
        (MrgKit.isz_le_of_inDisc p z hz) (MrgKit.isz_le_of_inDisc' p z hz) hm3 D hDq)
      (fun vs hvs => hvs) ?_ (fun vs _ => le_rfl)
    intro vs out _ hout
    exact ⟨cfxVal (m * z.1, m * z.2), hout, (scaleVal_cfxVal m z).symm,
      MrgKit.vsz_cfxVal_le p _ (MrgKit.inDisc_sign p z m hm1 hz)⟩
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact ⟨⟨z, rfl, hmem z hz⟩, MrgKit.vsz_cfxVal_le p z (hmem z hz)⟩
  · intro ys hys
    have h1 : ys = (w.map cfxVal).map (scaleVal m) := forall₂_scaleVal m hys
    rw [h1]
    have h2 : (w.map cfxVal).map (scaleVal m) = w.map (fun z => cfxVal (m * z.1, m * z.2)) := by
      rw [List.map_map]
      rfl
    rw [h2]
    show ofList ((w.map fun z => (m * z.1, m * z.2)).map cfxVal) =
      ofList (w.map fun z => cfxVal (m * z.1, m * z.2))
    rw [List.map_map]
    rfl
  · have hL : 2 * p + 7 + 1 ≤ 8 * (p + 1) := by omega
    rw [hDdef, List.length_map]
    nlinarith [Nat.mul_le_mul_left Kml hL]

/-! ## The requested lemma -/

theorem hasScaleWord (hk : Work.SynFFT.KLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (m : ℤ) (w : List (ℤ × ℤ)) (rest : List HvdH.Val),
      (∀ z ∈ w, HvdH.inDisc p z) → (m = 1 ∨ m = -1) → rest.getD 0 HvdH.Val.nil = HvdH.Val.int m →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.cvecVal w :: rest)
        (fun vs out => out = HvdH.cvecVal (w.map (fun z => (m * z.1, m * z.2))) :: rest)
        (fun _ => K * (w.length + 1) * (p + 1)) := by
  obtain ⟨pickP, Kp, hpick⟩ := hk.pick
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨swapP, Ksw, hswap⟩ := hk.swap
  obtain ⟨consP, Kcv, hcons⟩ := hk.consV
  obtain ⟨uncP, Kuc, hunc⟩ := hk.unconsV
  obtain ⟨mapP, Kml, hmap⟩ := hk.mapList
  obtain ⟨mulP, Km, hmul⟩ := hi.mulS
  refine ⟨mapP (qScale uncP pickP mulP rollP swapP consP),
    1000 * (Kuc + Kp + Km + Kr + Ksw + Kcv + 1) + 9 * Kml, ?_⟩
  intro main p m w rest hin hm1 hm0
  exact scaleVec_wordR (main := main) (hunc main) (hpick main) (hmul main) (hroll main)
    (hswap main) (hcons main) (hmap main) p m w rest hin hm1 hm0

end Work.SynFFT
