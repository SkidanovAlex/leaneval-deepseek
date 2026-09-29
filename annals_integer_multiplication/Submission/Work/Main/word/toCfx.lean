import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Main.word.toCfxElem

/-!
# `Work.Main.word.toCfx`: the chunk vector as a fixed-point complex vector

`Work.Main.word.toCfx` converts the list `xs` of base-`2^b` chunks of an integer (each `x < 2^b`,
with `b ≤ p`) into the fixed-point complex vector `ws` with `ws[j] = (x_j · 2^{p-b}, 0)`, i.e. the
vector of *scaled* chunks at precision `p`.  The list is transformed elementwise with
`KernelLib.mapList`, each element by `Work.Main.word.toCfxElem` (copy `b`, copy `p`, subtract,
shift left by `p - b`, pair with `0`), so the whole conversion costs `O((r+1)(p+1))` steps.

The file is deliberately independent of `Submission.Work.Main.defs`: it uses only the lead-owned
interfaces `Submission.HvdH.Interfaces` and the elementwise word `toCfxElem`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Main.word

open HvdH

/-! ## Encoding sizes (`Val.int`, and the `intList` unfolding) -/

private theorem cp_encodePosNum_length (q : PosNum) :
    (Computability.encodePosNum q).length = q.natSize := by
  induction q with
  | one => rfl
  | bit0 q ih => simp [Computability.encodePosNum, PosNum.natSize, ih]
  | bit1 q ih => simp [Computability.encodePosNum, PosNum.natSize, ih]

private theorem cp_encodeNum_length (x : Num) :
    (Computability.encodeNum x).length = x.natSize := by
  cases x with
  | zero => rfl
  | pos q => exact cp_encodePosNum_length q

private theorem cp_encodeNat_length (n : ℕ) :
    (Computability.encodeNat n).length = n.size := by
  change (Computability.encodeNum (Num.ofNat' n)).length = n.size
  rw [cp_encodeNum_length, Num.natSize_to_nat]
  simp

private theorem cp_vsz_int (z : ℤ) : vsz (Val.int z) = isz z := by
  show ((if z < 0 then Glyph.neg else Glyph.pos) ::
    ((Computability.encodeNat z.natAbs).map Glyph.bit ++ [Glyph.iend])).length = isz z
  rw [List.length_cons, List.length_append, List.length_map, List.length_singleton,
    cp_encodeNat_length, isz]

private theorem cp_vsz_cons (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  show (Glyph.cons :: (a.enc ++ b.enc)).length = a.enc.length + b.enc.length + 1
  rw [List.length_cons, List.length_append]

/-- `intList` is `ofList` of the list of integer values (definitional unfolding). -/
private theorem cp_intList_cons (a : ℕ) (t : List ℕ) :
    HvdH.intList (a :: t) = HvdH.Val.cons (HvdH.Val.int (a : ℤ)) (HvdH.intList t) := rfl

private theorem cp_intList_eq (xs : List ℕ) :
    HvdH.intList xs = HvdH.ofList (xs.map (fun n : ℕ => HvdH.Val.int (n : ℤ))) := by
  induction xs with
  | nil => rfl
  | cons a t ih =>
    rw [show HvdH.intList (a :: t) = HvdH.Val.cons (HvdH.Val.int (a : ℤ)) (HvdH.intList t) from rfl, ih]
    rfl

/-! ## Size and disc bounds for one chunk -/

/-- The fixed-point value attached to the chunk `n`: `(n · 2^{p-b}, 0)`. -/
private def cfxOf (p b n : ℕ) : ℤ × ℤ := (((n : ℤ) * 2 ^ (p - b)), 0)

/-- The shifted integer `n · 2^{p-b}` is `< 2^p`. -/
private theorem cp_shift_lt {p b n : ℕ} (hb : b ≤ p) (hn : n < 2 ^ b) :
    n * 2 ^ (p - b) < 2 ^ p := by
  calc n * 2 ^ (p - b) < 2 ^ b * 2 ^ (p - b) :=
        Nat.mul_lt_mul_of_pos_right hn (Nat.pow_pos (by norm_num))
    _ = 2 ^ (b + (p - b)) := (pow_add 2 b (p - b)).symm
    _ = 2 ^ p := by rw [show b + (p - b) = p by omega]

/-- `isz (n · 2^{p-b}) ≤ p + 2` for a chunk. -/
private theorem cp_shift_size {p b n : ℕ} (hb : b ≤ p) (hn : n < 2 ^ b) :
    isz (((n : ℤ) * 2 ^ (p - b))) ≤ p + 2 := by
  have hlt := cp_shift_lt hb hn
  have hm : (((n : ℤ) * 2 ^ (p - b)).natAbs) = n * 2 ^ (p - b) := by
    rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pow]; norm_num
  have := Nat.size_le.mpr hlt
  simp only [isz]
  rw [hm]
  omega

/-- `n < 2^b` and `b ≤ p` put `n · 2^{p-b}` in the disc `C̃◦`. -/
private theorem cfxOf_inDisc {p b : ℕ} (hb : b ≤ p) {n : ℕ} (hn : n < 2 ^ b) :
    inDisc p (cfxOf p b n) := by
  simp only [inDisc, cfxOf]
  have hn' : (n : ℤ) ≤ (2 : ℤ) ^ b := by
    have h : n ≤ 2 ^ b := le_of_lt hn
    calc (n : ℤ) ≤ ((2 ^ b : ℕ) : ℤ) := by exact_mod_cast h
      _ = (2 : ℤ) ^ b := by push_cast; ring
  have h1 : (n : ℤ) * (2 : ℤ) ^ (p - b) ≤ (2 : ℤ) ^ p := by
    calc (n : ℤ) * (2 : ℤ) ^ (p - b) ≤ (2 : ℤ) ^ b * (2 : ℤ) ^ (p - b) :=
          mul_le_mul_of_nonneg_right hn' (by positivity)
      _ = (2 : ℤ) ^ (b + (p - b)) := by rw [pow_add]
      _ = (2 : ℤ) ^ p := by rw [Nat.add_sub_of_le hb]
  have h0 : 0 ≤ (n : ℤ) * (2 : ℤ) ^ (p - b) := by positivity
  have hsq : ((n : ℤ) * (2 : ℤ) ^ (p - b)) ^ 2 ≤ ((2 : ℤ) ^ p) ^ 2 := by
    simpa [pow_two] using mul_le_mul h1 h1 h0 (le_trans h0 h1)
  have h4 : (4 : ℤ) ^ p = ((2 : ℤ) ^ p) ^ 2 := by
    rw [show (4 : ℤ) = (2 : ℤ) ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm 2 p]
  rw [h4]
  simpa using hsq

/-- Sizes and disc condition for the converted chunk. -/
private theorem cp_sizes {p b n : ℕ} (hb : b ≤ p) (hn : n < 2 ^ b) :
    vsz (Val.int (n : ℤ)) ≤ p + 5 ∧
      vsz (cfxVal (((n : ℤ) * 2 ^ (p - b)), 0)) ≤ p + 5 ∧
      inDisc p (((n : ℤ) * 2 ^ (p - b)), 0) := by
  have hnp : n < 2 ^ p := lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) hb)
  have hnsize : n.size ≤ p := Nat.size_le.mpr hnp
  refine ⟨?_, ?_, ?_⟩
  · rw [cp_vsz_int]
    simp only [isz, Int.natAbs_natCast]
    omega
  · rw [show cfxVal (((n : ℤ) * 2 ^ (p - b)), 0) =
        Val.cons (Val.int (((n : ℤ) * 2 ^ (p - b)))) (Val.int 0) from rfl,
      cp_vsz_cons, cp_vsz_int, cp_vsz_int]
    have h1 := cp_shift_size hb hn
    have h0 : isz (0 : ℤ) = 2 := by simp [isz]
    rw [h0]
    omega
  · exact cfxOf_inDisc hb hn

/-! ## Extracting the coefficient vector from the mapped list -/

/-- Reading a `List.Forall₂` between `xs.map (Val.int ·)` and a list of converted values: the
second list is the `cfxOf`-image of `xs`, and every chunk is `< 2^b` (`Val.int` is injective, so
the relation determines the integer). -/
private theorem cp_forall₂_cfxOf {p b : ℕ} :
    ∀ (xs : List ℕ) {ys : List Val},
      List.Forall₂ (fun x y => ∃ n : ℕ, x = Val.int (n : ℤ) ∧ n < 2 ^ b ∧
        y = cfxVal (cfxOf p b n))
      (xs.map (fun n : ℕ => Val.int (n : ℤ))) ys →
      ys = xs.map (fun n => cfxVal (cfxOf p b n)) ∧ ∀ n ∈ xs, n < 2 ^ b := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases h with
    | nil => exact ⟨rfl, by simp⟩
  | cons a xs ih =>
    intro ys h
    rw [List.map_cons] at h
    cases h with
    | cons hrel hrest =>
      obtain ⟨n, hx, hn, hy⟩ := hrel
      obtain ⟨hys, hbnd⟩ := ih hrest
      have han : a = n := by
        have h2 : (a : ℤ) = (n : ℤ) := (Val.int.injEq _ _).mp hx
        exact Int.ofNat.inj h2
      refine ⟨?_, ?_⟩
      · simp only [List.map_cons]
        rw [hys, hy, han]
      · intro m hm
        simp only [List.mem_cons] at hm
        rcases hm with rfl | hm
        · rwa [han]
        · exact hbnd m hm

/-- **Extraction.** Given the pointwise relation provided by `mapList` on the converted list, the
output list is the encoding of a coefficient vector `ws` of the same length as `xs`, in the disc,
whose `j`-th coefficient is exactly `(xs[j] · 2^{p-b}, 0)`. -/
private theorem cp_extract {p b : ℕ} (hb : b ≤ p) (xs : List ℕ) {ys : List Val}
    (h : List.Forall₂ (fun x y => ∃ n : ℕ, x = Val.int (n : ℤ) ∧ n < 2 ^ b ∧
        y = cfxVal (((n : ℤ) * 2 ^ (p - b)), 0))
      (xs.map (fun n : ℕ => Val.int (n : ℤ))) ys) :
    ∃ ws : List (ℤ × ℤ), ys = ws.map cfxVal ∧ ws.length = xs.length ∧
      InDiscVec p xs.length ws ∧
      ∀ j < xs.length, ws.getD j (0, 0) = (((xs.getD j 0 : ℕ) : ℤ) * 2 ^ (p - b), 0) := by
  obtain ⟨hys, hbnd⟩ := cp_forall₂_cfxOf (p := p) (b := b) xs h
  refine ⟨xs.map (fun n => cfxOf p b n), ?_, ?_, ?_, ?_⟩
  · rw [hys, List.map_map]; rfl
  · simp
  · refine ⟨by simp, ?_⟩
    intro z hz
    obtain ⟨n, hn, hFn⟩ := List.mem_map.mp hz
    rw [← hFn]
    exact cfxOf_inDisc hb (hbnd n hn)
  · intro j hj
    have h1 : (xs.map (fun n => cfxOf p b n)).getD j (0, 0) = cfxOf p b (xs.getD j 0) := by
      rw [List.getD_eq_getElem (hn := by simpa using hj), List.getElem_map,
        ← List.getD_eq_getElem (l := xs) (d := 0) (hn := hj)]
    rw [h1]
    rfl

/-! ## The list word -/

theorem toCfx (hKer : HvdH.KernelLib) (hInt : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p b : ℕ) (xs : List ℕ) (rest : List HvdH.Val),
      b ≤ p → (∀ j ∈ xs, j < 2 ^ b) →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.intList xs :: HvdH.Val.int p :: HvdH.Val.int b :: rest)
        (fun vs out => (∃ (ws : List (ℤ × ℤ)), vs = HvdH.intList xs :: HvdH.Val.int p :: HvdH.Val.int b :: rest ∧
          out = HvdH.cvecVal ws :: HvdH.Val.int p :: HvdH.Val.int b :: rest ∧ ws.length = xs.length ∧
          HvdH.InDiscVec p xs.length ws ∧
          ∀ j < xs.length, ws.getD j (0,0) = (((xs.getD j 0 : ℕ) : ℤ) * 2 ^ (p - b), 0)))
        (fun _ => K * (xs.length + 1) * (p + 1) + K) := by
  obtain ⟨bodyP, Kb, hbody⟩ := toCfxElem hKer hInt
  obtain ⟨mapP, Km, hmap⟩ := hKer.mapList
  refine ⟨mapP bodyP, 2 * Kb + 7 * Km + 1, ?_⟩
  intro main p b xs rest hb hxs
  have hmain := hmap main bodyP (HvdH.Val.int (p : ℤ) :: HvdH.Val.int (b : ℤ) :: rest)
      (fun x : HvdH.Val => ∃ n : ℕ, x = HvdH.Val.int (n : ℤ) ∧ n < 2 ^ b)
      (fun x y : HvdH.Val => ∃ n : ℕ, x = HvdH.Val.int (n : ℤ) ∧ n < 2 ^ b ∧
        y = HvdH.cfxVal (((n : ℤ) * 2 ^ (p - b)), 0))
      (Kb * (p + 1) + Kb) (p + 5)
      (fun x hx => by
        obtain ⟨n, rfl, hn⟩ := hx
        refine hKer.conseq main bodyP _ _ _ _ _ _
          (hbody main p b n rest hb hn) ?_ ?_ ?_
        · intro vs hvs; exact hvs
        · intro vs out hvs hout
          exact ⟨HvdH.cfxVal (((n : ℤ) * 2 ^ (p - b)), 0), hout, ⟨n, rfl, hn, rfl⟩,
            (cp_sizes hb hn).2.1⟩
        · intro vs hvs; exact le_rfl)
      (xs.map (fun n : ℕ => HvdH.Val.int (n : ℤ)))
      (fun x hx => by
        obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
        exact ⟨⟨n, rfl, hxs n hn⟩, (cp_sizes hb (hxs n hn)).1⟩)
  refine hKer.conseq main (mapP bodyP) _ _ _ _ _ _ hmain ?_ ?_ ?_
  · intro vs hvs
    rw [hvs, cp_intList_eq]
  · intro vs out hvs hq
    obtain ⟨ys, hout, hF2⟩ := hq
    obtain ⟨ws, hys, hlen, hdisc, hgetD⟩ := cp_extract hb xs hF2
    exact ⟨ws, hvs, by rw [hout, hys]; rfl, hlen, hdisc, hgetD⟩
  · intro vs hvs
    simp only [List.length_map]
    have hKb : Kb ≤ Kb * (p + 1) := Nat.le_mul_of_pos_right Kb (by omega)
    have hKm : Km * (p + 5 + 1) ≤ Km * (7 * (p + 1)) := Nat.mul_le_mul_left Km (by omega)
    nlinarith [hKb, hKm]

end Work.Main.word
