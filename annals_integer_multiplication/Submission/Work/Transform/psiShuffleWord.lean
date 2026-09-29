import Mathlib
import Submission.Work.Transform.phiAux
import Submission.Work.Transform.flattenIdx
import Submission.Work.Transform.inDiscFlatten
import Submission.Work.ConvR.dropUnder

set_option autoImplicit false

namespace Work.Transform

open HvdH

/-! ## Private auxiliary facts

The shuffling word of `psiShuffleWord` is the straight-line program

`roll 3; drop; roll 2; roll 1; flatten`

i.e. `int r` is moved to the top and dropped, the table `cvecVal zt` is moved before the array
`rarrVal w`, the array is brought back on top and flattened.

(Note: the `LayoutLib.flatten` word *consumes* the array `ofList (xss.map ofList)` and replaces it
by `ofList xss.flatten`, so the flattening has to happen **last** and no `drop` follows it; an
extra `drop` after `flatten` would delete the result.)
-/

/-- `ofList` of the flattened (row-major) matrix of `cfxVal`s is `cvecVal` of the flattened
matrix. -/
private lemma ofList_map_cfx_flatten (w : List (List (ℤ × ℤ))) :
    ofList ((w.map fun row => row.map cfxVal)).flatten = cvecVal w.flatten := by
  rw [← List.map_flatten (f := cfxVal)]
  rfl

/-- The array `rarrVal w` is the `ofList` of the outer list of its rows. -/
private lemma ofList_map_ofList (w : List (List (ℤ × ℤ))) :
    ofList ((w.map fun row => row.map cfxVal).map ofList) = rarrVal w := by
  rw [List.map_map]
  rfl

/-- Cost normalisation for `roll 3`. -/
private lemma take_sum_cons4 (a b c d : Val) (R : List Val) :
    (((a :: b :: c :: d :: R).take (3 + 1)).map vsz).sum + 1
      = vsz a + vsz b + vsz c + vsz d + 1 := by
  simp [List.take_succ_cons, Nat.add_assoc, Nat.add_comm]

/-- Cost normalisation for `roll 2`. -/
private lemma take_sum_cons3 (a b c : Val) (R : List Val) :
    (((a :: b :: c :: R).take (2 + 1)).map vsz).sum + 1 = vsz a + vsz b + vsz c + 1 := by
  simp [List.take_succ_cons, Nat.add_assoc, Nat.add_comm]

/-- Cost normalisation for `roll 1`. -/
private lemma take_sum_cons2 (a b : Val) (R : List Val) :
    (((a :: b :: R).take (1 + 1)).map vsz).sum + 1 = vsz a + vsz b + 1 := by
  simp [List.take_succ_cons, Nat.add_assoc]

/-- One `LayoutLib.flatten` applied to the array on top of the value stack:
`rarrVal w :: rest ↦ cvecVal w.flatten :: rest`. -/
private lemma flattenStepC (hK : KernelLib) {flatP : Cmd} {KL : ℕ}
    (hflat : ∀ (main : Cmd) (xss : List (List Val)),
      WordR main flatP (fun vs => ∃ rest, vs = ofList (xss.map ofList) :: rest)
        (fun vs out => ∃ rest, vs = ofList (xss.map ofList) :: rest ∧
          out = ofList xss.flatten :: rest)
        (fun _ => KL * (vsz (ofList (xss.map ofList)) + 1)))
    (main : Cmd) (w : List (List (ℤ × ℤ))) (rest : List Val) :
    Work.ConvR.WordC main flatP (fun vs => vs = rarrVal w :: rest)
      (fun _ out => out = cvecVal w.flatten :: rest) (KL * (vsz (rarrVal w) + 1)) := by
  refine Work.ConvR.WordC.conseq hK (hflat main (w.map fun row => row.map cfxVal)) ?_ ?_ ?_
  · intro vs hvs
    exact ⟨rest, by rw [hvs, ← ofList_map_ofList w]⟩
  · rintro vs out hvs ⟨rest', h1, h2⟩
    rw [hvs, ← ofList_map_ofList w] at h1
    injection h1 with _ hrest
    rw [h2, hrest, ← ofList_map_cfx_flatten w]
  · exact Nat.le_of_eq (by rw [ofList_map_ofList w])

/-- The five arithmetic bounds on the step costs.  The size hypotheses `hA`, `hZ`, `hP`, `hR`
are the ones supplied by `vsz_rarrVal_le`, `vsz_cvecVal_le`, `isz_le`. -/
private lemma costBounds (KL KR KD p r M A P Z Rv U S : ℕ)
    (hA : A ≤ 400 * (M * r * p ^ 2 + 1)) (hZ : Z ≤ 200 * ((M * r) * p ^ 2 + 1))
    (hP : P ≤ p + 2) (hR : Rv ≤ r + 2) (hp : 100 ≤ p) (hr : 2 ≤ r)
    (hU : U = 100000 * (KL + KR + KD + 1)) (hS : S = (M * r) * p ^ 2 + p + r + 1) :
    (KR * (3 + 1) * (A + P + Z + Rv + 1) ≤ U * S) ∧ (KD * (Rv + 1) ≤ U * S) ∧
    (KR * (2 + 1) * (A + P + Z + 1) ≤ U * S) ∧ (KR * (1 + 1) * (Z + A + 1) ≤ U * S) ∧
    (KL * (A + 1) ≤ U * S) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- Data-shuffling word for the inverse transform `Ũ` of paper Prop 3.5: from
`rarrVal w :: int p :: cvecVal zt :: int r :: R` (an `M × r`-array of `C̃◦`-pairs, the precision
`p`, the stretched table `zt` of length `M*r`, and the block length `r`) produce
`cvecVal w.flatten :: cvecVal zt :: int p :: R`: flatten the array (`LayoutLib.flatten` with
`xss = w.map (fun row => row.map cfxVal)`, using `List.map_flatten` to turn `ofList xss.flatten`
into `cvecVal w.flatten`), erase the `int r` and reorder the two vectors on top of `int p`.  The
program is `roll 3; drop; roll 2; roll 1; flatten; drop`: `roll 3; drop` erases `int r`,
`roll 2; roll 1` puts `cvecVal zt` directly below `rarrVal w`, then `flatten` pushes
`cvecVal w.flatten` and `drop` removes the array.  Cost linear in the encoding sizes, bounded by
`K * ((M*r) * p^2 + p + r + 1) + K` using `vsz (rarrVal w) ≤ 400 * (M*r*p^2 + 1)`,
`vsz (cvecVal zt) ≤ 200 * ((M*r)*p^2 + 1)`, `isz p ≤ p + 2`, `isz r ≤ r + 2` (all in
`Submission.Work.Transform.phiAux`); the `+ p + r + 1` is needed even at `M = 0`, where the two
`int` parameters must still be erased.  Useful infrastructure: `Work.ConvR.WordC.rollStep`,
`Work.ConvR.WordC.dropStep`, `Work.ConvR.WordC.seqEq`, `Work.Kernel.WordR_seq`,
`Work.Kernel.WordR_conseq`, `Work.Transform.flattenIdx`,
`Work.Transform.inDiscFlatten : InDiscArr p M r w → InDiscVec p (M*r) w.flatten`.
Guidance: keep every auxiliary lemma `private`. -/
theorem psiShuffleWord : HvdH.KernelLib → HvdH.LayoutLib → ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p r M : ℕ) (w : List (List (ℤ × ℤ))) (zt : List (ℤ × ℤ)) (R : List HvdH.Val),
      w.length = M → (∀ a < M, (w.getD a []).length = r) → zt.length = M * r →
      HvdH.InDiscArr p M r w → HvdH.InDiscVec p (M * r) zt → 100 ≤ p → 2 ≤ r →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.rarrVal w :: HvdH.Val.int p :: HvdH.cvecVal zt :: HvdH.Val.int r :: R)
        (fun _ out => out = HvdH.cvecVal w.flatten :: HvdH.cvecVal zt :: HvdH.Val.int p :: R)
        (fun _ => K * ((M * r) * p ^ 2 + p + r + 1) + K) := by
  intro hK hL
  obtain ⟨flatP, KL, hflat⟩ := hL.flatten
  obtain ⟨rollP, KR, hroll⟩ := hK.roll
  obtain ⟨dropP, KD, hdrop⟩ := hK.drop
  set U : ℕ := 100000 * (KL + KR + KD + 1) with hU
  refine ⟨Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (rollP 3) dropP) (rollP 2)) (rollP 1)) flatP,
    6 * U, ?_⟩
  intro main p r M w zt R _hlen _hrow _hzlen hdiscA hdiscZ hp hr
  set S : ℕ := (M * r) * p ^ 2 + p + r + 1 with hS
  -- size bounds
  have hA : vsz (rarrVal w) ≤ 400 * (M * r * p ^ 2 + 1) := vsz_rarrVal_le hdiscA hp hr
  have hZ : vsz (cvecVal zt) ≤ 200 * ((M * r) * p ^ 2 + 1) := vsz_cvecVal_le hdiscZ hp
  have hP : vsz (Val.int (p : ℤ)) ≤ p + 2 := by
    rw [Work.Transform.vsz_int]; simpa using isz_le (p : ℤ)
  have hR : vsz (Val.int (r : ℤ)) ≤ r + 2 := by
    rw [Work.Transform.vsz_int]; simpa using isz_le (r : ℤ)
  -- the five step costs
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := costBounds KL KR KD p r M
    (vsz (rarrVal w)) (vsz (Val.int (p : ℤ))) (vsz (cvecVal zt)) (vsz (Val.int (r : ℤ))) U S
    hA hZ hP hR hp hr hU hS
  have hc1 : KR * (3 + 1) * ((((rarrVal w :: Val.int (p : ℤ) :: cvecVal zt ::
      Val.int (r : ℤ) :: R).take (3 + 1)).map vsz).sum + 1) ≤ U * S := by
    rw [take_sum_cons4]; exact hb1
  have hc2 : KD * (vsz (Val.int (r : ℤ)) + 1) ≤ U * S := hb2
  have hc3 : KR * (2 + 1) * ((((rarrVal w :: Val.int (p : ℤ) :: cvecVal zt ::
      R).take (2 + 1)).map vsz).sum + 1) ≤ U * S := by
    rw [take_sum_cons3]; exact hb3
  have hc4 : KR * (1 + 1) * ((((cvecVal zt :: rarrVal w :: Val.int (p : ℤ) ::
      R).take (1 + 1)).map vsz).sum + 1) ≤ U * S := by
    rw [take_sum_cons2]; exact hb4
  have hc5 : KL * (vsz (rarrVal w) + 1) ≤ U * S := hb5
  -- the five steps
  have H1 : Work.ConvR.WordC main (rollP 3)
      (fun vs => vs = rarrVal w :: Val.int (p : ℤ) :: cvecVal zt :: Val.int (r : ℤ) :: R)
      (fun _ out => out = Val.int (r : ℤ) :: rarrVal w :: Val.int (p : ℤ) :: cvecVal zt :: R)
      (U * S) :=
    Work.ConvR.WordC.rollStep hK hroll (k := 3) (C := U * S)
      (L := rarrVal w :: Val.int (p : ℤ) :: cvecVal zt :: Val.int (r : ℤ) :: R)
      (L' := Val.int (r : ℤ) :: rarrVal w :: Val.int (p : ℤ) :: cvecVal zt :: R)
      (by simp) (by simp) hc1
  have H2 : Work.ConvR.WordC main dropP
      (fun vs => vs = Val.int (r : ℤ) :: rarrVal w :: Val.int (p : ℤ) :: cvecVal zt :: R)
      (fun _ out => out = rarrVal w :: Val.int (p : ℤ) :: cvecVal zt :: R) (U * S) :=
    Work.ConvR.WordC.dropStep hK hdrop
      (L := Val.int (r : ℤ) :: rarrVal w :: Val.int (p : ℤ) :: cvecVal zt :: R)
      (L' := rarrVal w :: Val.int (p : ℤ) :: cvecVal zt :: R) (by simp) rfl hc2
  have H3 : Work.ConvR.WordC main (rollP 2)
      (fun vs => vs = rarrVal w :: Val.int (p : ℤ) :: cvecVal zt :: R)
      (fun _ out => out = cvecVal zt :: rarrVal w :: Val.int (p : ℤ) :: R) (U * S) :=
    Work.ConvR.WordC.rollStep hK hroll (k := 2) (C := U * S)
      (L := rarrVal w :: Val.int (p : ℤ) :: cvecVal zt :: R)
      (L' := cvecVal zt :: rarrVal w :: Val.int (p : ℤ) :: R) (by simp) (by simp) hc3
  have H4 : Work.ConvR.WordC main (rollP 1)
      (fun vs => vs = cvecVal zt :: rarrVal w :: Val.int (p : ℤ) :: R)
      (fun _ out => out = rarrVal w :: cvecVal zt :: Val.int (p : ℤ) :: R) (U * S) :=
    Work.ConvR.WordC.rollStep hK hroll (k := 1) (C := U * S)
      (L := cvecVal zt :: rarrVal w :: Val.int (p : ℤ) :: R)
      (L' := rarrVal w :: cvecVal zt :: Val.int (p : ℤ) :: R) (by simp) (by simp) hc4
  have H5 : Work.ConvR.WordC main flatP
      (fun vs => vs = rarrVal w :: cvecVal zt :: Val.int (p : ℤ) :: R)
      (fun _ out => out = cvecVal w.flatten :: cvecVal zt :: Val.int (p : ℤ) :: R) (U * S) :=
    Work.ConvR.WordC.conseq hK
      (flattenStepC hK hflat main w (cvecVal zt :: Val.int (p : ℤ) :: R))
      (fun _ h => h) (fun _ _ _ h => h) hc5
  have H12 := Work.ConvR.WordC.seqEq hK H1 H2
  have H123 := Work.ConvR.WordC.seqEq hK H12 H3
  have H1234 := Work.ConvR.WordC.seqEq hK H123 H4
  have Hall := Work.ConvR.WordC.seqEq hK H1234 H5
  refine Work.Kernel.WordR_conseq
    (P := fun vs => vs = rarrVal w :: Val.int (p : ℤ) :: cvecVal zt :: Val.int (r : ℤ) :: R)
    (Q := fun _ out => out = cvecVal w.flatten :: cvecVal zt :: Val.int (p : ℤ) :: R)
    (Work.ConvR.WordC.toWordR Hall) (fun _ h => h) (fun _ _ _ h => h) ?_
  intro vs _
  have h4 : ((U * S + U * S) + U * S) + U * S = 4 * (U * S) := by ring
  rw [h4, show (6 : ℕ) * U * S = 6 * (U * S) by ring]
  omega

end Work.Transform
