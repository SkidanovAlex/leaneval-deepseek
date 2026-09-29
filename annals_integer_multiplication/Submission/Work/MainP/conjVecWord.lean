import Mathlib
import Submission.Work.Kernel.Raw
import Submission.Work.ConvR.basic
import Submission.Work.Transform.conjElemWord

set_option autoImplicit false

namespace Work.MainP

open HvdH

/-! ## Auxiliary lemmas for the conjugation word -/

/-- `cfxVal` is injective (a `cons` of two integer values determines its two components). -/
theorem cfxVal_inj' {a b : ℤ × ℤ} (h : cfxVal a = cfxVal b) : a = b := by
  have h' : a.1 = b.1 ∧ a.2 = b.2 := by
    simpa [HvdH.cfxVal, HvdH.Val.cons.injEq, HvdH.Val.int.injEq] using h
  exact Prod.ext h'.1 h'.2

/-- `ofList` of the conjugated values is the encoding of the conjugated coefficient vector. -/
theorem ofList_map_cfxVal_conj (zs : List (ℤ × ℤ)) :
    HvdH.ofList (zs.map (fun z => cfxVal (z.1, -z.2))) =
      HvdH.cvecVal (zs.map fun z => (z.1, -z.2)) := by
  induction zs with
  | nil => rfl
  | cons a zs ih =>
    show Val.cons (cfxVal (a.1, -a.2))
        (HvdH.ofList (zs.map (fun z => cfxVal (z.1, -z.2)))) =
      Val.cons (cfxVal (a.1, -a.2))
        (HvdH.cvecVal (zs.map fun z => (z.1, -z.2)))
    rw [ih]

/-- The pointwise relation: a value `cfxVal z` is paired with the conjugated value
`cfxVal (z.1, -z.2)`. -/
def conjRel (x y : Val) : Prop := ∃ z : ℤ × ℤ, x = cfxVal z ∧ y = cfxVal (z.1, -z.2)

/-- **Extraction.**  If the list `ys` of values is pointwise paired by `conjRel` with the encoding
`zs.map cfxVal` of a coefficient vector, then `ys` is *literally* the list of conjugated
coefficients: `ys = zs.map (fun z => cfxVal (z.1, -z.2))`.  (`cfxVal` is injective, so `conjRel`
determines its second argument.) -/
theorem conjRel_extract (zs : List (ℤ × ℤ)) :
    ∀ {ys : List Val}, List.Forall₂ conjRel (zs.map cfxVal) ys →
      ys = zs.map (fun z => cfxVal (z.1, -z.2)) := by
  induction zs with
  | nil =>
    intro ys h
    rw [List.map_nil] at h
    exact List.forall₂_nil_left_iff.mp h
  | cons a zs ih =>
    intro ys h
    rw [List.map_cons] at h
    cases h with
    | cons hhead htail =>
      obtain ⟨z, hz, hy⟩ := hhead
      have hza : z = a := cfxVal_inj' hz.symm
      subst hza
      rw [hy, ih htail]
      rfl

/-- Conjugation preserves the disc condition `C̃◦` (`x² + (-y)² = x² + y²`). -/
theorem inDisc_conj {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : inDisc p (z.1, -z.2) := by
  simp only [inDisc] at h ⊢
  nlinarith [h]

/-- Cost arithmetic for `conjVecWord`: `n` iterations of a per-element cost `O(p+1)`, plus the
`mapList` bookkeeping, fit into `(Kc + 9 Km) (n+1)(p+1) + (Kc + 9 Km)`. -/
theorem conjVecCost (Kc Km r p : ℕ) :
    r * (Kc * (p + 1) + Km * (Work.ConvR.cfxSz p + 1)) + Km ≤
      (Kc + 9 * Km) * (r + 1) * (p + 1) + (Kc + 9 * Km) := by
  have hsz : Work.ConvR.cfxSz p = 2 * p + 8 := rfl
  rw [hsz]
  have hA : Kc * (p + 1) + Km * (2 * p + 8 + 1) ≤ (Kc + 9 * Km) * (p + 1) := by
    have h : 2 * p + 8 + 1 ≤ 9 * (p + 1) := by omega
    have h2 : Km * (2 * p + 8 + 1) ≤ Km * (9 * (p + 1)) := Nat.mul_le_mul_left Km h
    calc Kc * (p + 1) + Km * (2 * p + 8 + 1)
        ≤ Kc * (p + 1) + Km * (9 * (p + 1)) := Nat.add_le_add_left h2 _
      _ = (Kc + 9 * Km) * (p + 1) := by ring
  have hKm : Km ≤ (Kc + 9 * Km) * (p + 1) + (Kc + 9 * Km) := by
    have h1 : Km ≤ Km * (p + 1) := by
      simpa using Nat.mul_le_mul_left Km (show 1 ≤ p + 1 by omega)
    have h2 : Km * (p + 1) ≤ (Kc + 9 * Km) * (p + 1) :=
      Nat.mul_le_mul_right (p + 1) (by omega)
    omega
  calc r * (Kc * (p + 1) + Km * (2 * p + 8 + 1)) + Km
      ≤ r * ((Kc + 9 * Km) * (p + 1)) + Km := Nat.add_le_add_right (Nat.mul_le_mul_left r hA) _
    _ = (Kc + 9 * Km) * (r * (p + 1)) + Km := by ring
    _ ≤ (Kc + 9 * Km) * (r * (p + 1)) +
          ((Kc + 9 * Km) * (p + 1) + (Kc + 9 * Km)) := Nat.add_le_add_left hKm _
    _ = (Kc + 9 * Km) * (r + 1) * (p + 1) + (Kc + 9 * Km) := by ring

/-! ## The conjugation word -/

/-- Paper Prop 5.2, auxiliary word: conjugate a vector of fixed-point complex numbers.
Each element of `cvecVal zs` is the value `cfxVal z = cons (int z.1) (int z.2)`; conjugating the
vector means negating every *second* component, which is exact (no rounding) and preserves the
disc condition `C̃◦`.

Program: `KernelLib.mapList` applied to the per-element word
`[cons (int a) (int b), rest] → [cons (int a) (int (-b)), rest]`, which is
`unconsV` (gives `int a :: int b :: rest`), `roll 1`, `IntLib.neg`, `roll 1`, `consV`.
Cost `O(n p)`: `mapList` cost `n * (c + K2*(L+1)) + K2` with per-element cost `O(p)` and the
per-element size bound `L = 2p+8` (`Work.ConvR.vsz_cfxVal_le`, from `InDiscVec`). -/
theorem conjVecWord (hKer : HvdH.KernelLib) (hInt : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (zs : List (ℤ × ℤ))
      (rest : List HvdH.Val),
      HvdH.InDiscVec p zs.length zs →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.cvecVal zs :: rest)
        (fun vs out => vs = HvdH.cvecVal zs :: rest ∧
          out = HvdH.cvecVal (zs.map fun z => (z.1, -z.2)) :: rest)
        (fun _ => K * (zs.length + 1) * (p + 1) + K) := by
  -- the per-element conjugating word (negate the second component of `cfxVal z`)
  obtain ⟨celP, Kc, hcel⟩ := Work.Transform.conjElemWord hKer hInt
  -- the generic list-map loop
  obtain ⟨mapP, Km, hmap⟩ := hKer.mapList
  refine ⟨mapP celP, Kc + 9 * Km, ?_⟩
  intro main p zs rest hzs
  -- every element of the encoded vector is a disc coefficient of encoding size `≤ cfxSz p`
  have hxs : ∀ x ∈ zs.map cfxVal,
      (∃ z : ℤ × ℤ, x = cfxVal z ∧ inDisc p z) ∧ vsz x ≤ Work.ConvR.cfxSz p := by
    intro x hx
    obtain ⟨z, hzx, rfl⟩ := List.mem_map.mp hx
    exact ⟨⟨z, rfl, hzs.2 z hzx⟩, Work.ConvR.vsz_cfxVal_le (hzs.2 z hzx)⟩
  -- the per-element word, with the pointwise conjugation relation as its specification
  have hper : ∀ x, (∃ z : ℤ × ℤ, x = cfxVal z ∧ inDisc p z) →
      HvdH.WordR main celP (fun vs => vs = x :: rest)
        (fun _ out => ∃ y, out = y :: rest ∧ conjRel x y ∧ vsz y ≤ Work.ConvR.cfxSz p)
        (fun _ => Kc * (p + 1)) := by
    rintro x ⟨z, rfl, hz⟩
    refine hKer.conseq main celP _ _ _ _ _ _ (hcel main p z rest hz) (fun _ h => h) ?_ ?_
    · intro vs out _ hout
      exact ⟨cfxVal (z.1, -z.2), hout, ⟨z, rfl, rfl⟩,
        Work.ConvR.vsz_cfxVal_le (inDisc_conj hz)⟩
    · intro vs _; exact le_rfl
  have hmain := hmap main celP rest
      (fun x => ∃ z : ℤ × ℤ, x = cfxVal z ∧ inDisc p z)
      conjRel (Kc * (p + 1)) (Work.ConvR.cfxSz p) hper (zs.map cfxVal) hxs
  refine hKer.conseq main (mapP celP) _ _ _ _ _ _ hmain (fun _ h => h) ?_ ?_
  · -- read the resulting list of values back as the conjugated coefficient vector
    rintro vs out hvs ⟨ys, hout, hF2⟩
    have hys := conjRel_extract zs hF2
    refine ⟨hvs, ?_⟩
    rw [hout, hys, ofList_map_cfxVal_conj]
  · -- the cost bound
    intro vs _
    have hlen : (zs.map cfxVal).length = zs.length := List.length_map ..
    show (zs.map cfxVal).length * (Kc * (p + 1) + Km * (Work.ConvR.cfxSz p + 1)) + Km ≤
      (Kc + 9 * Km) * (zs.length + 1) * (p + 1) + (Kc + 9 * Km)
    rw [hlen]
    exact conjVecCost Kc Km zs.length p

end Work.MainP
