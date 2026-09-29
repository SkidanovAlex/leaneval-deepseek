import Mathlib
import Submission.Work.ConvR.basic
import Submission.Work.Kernel.Raw
import Submission.Work.Transform.phiAux

namespace Work.Transform

open HvdH

/-! ## Private helpers for the pointwise-product word

`blendPwWord` is `KernelLib.zipWith` applied to the one-element product word `pwMulS_aux`
(copy the precision with `pick 2`, then `FxLib.mulS`); the sizes of the elements are bounded
by `2p + 8` because they are `cfxVal` of disc points.  Everything below is `private` so that
sibling modules of the `Work.Transform` namespace stay importable together. -/

/-- Per-element precondition: both values are `cfxVal` of disc points. -/
private def pwP (p : ℕ) (x y : Val) : Prop :=
  ∃ z1 z2 : ℤ × ℤ, x = cfxVal z1 ∧ y = cfxVal z2 ∧ inDisc p z1 ∧ inDisc p z2

/-- Per-element postcondition: the product is a `cfxVal` of a disc point, with error `< 2`. -/
private def pwQ (p : ℕ) (x y z : Val) : Prop :=
  ∃ z1 z2 w : ℤ × ℤ, x = cfxVal z1 ∧ y = cfxVal z2 ∧ z = cfxVal w ∧
    inDisc p w ∧ (2 : ℝ) ^ p * ‖fxC p w - fxC p z1 * fxC p z2‖ < 2

/-- One-element product word (no hypothesis `100 ≤ p`): on `cfxVal z1 :: cfxVal z2 :: int p :: rest`
it produces `cfxVal w :: int p :: rest` with `z w ≈ z1 * z2`.  `pick 2` copies the precision `int p`
that sits below the two values to the top of the stack and `FxLib.mulS` consumes that copy. -/
private theorem pwMulS_aux (hK : KernelLib) (hF : FxLib) :
    ∃ (q : Cmd) (C : ℕ),
      ∀ (main : Cmd) (p : ℕ) (rest : List Val) (z1 z2 : ℤ × ℤ),
        inDisc p z1 → inDisc p z2 →
        WordR main q
          (fun vs => vs = cfxVal z1 :: cfxVal z2 :: Val.int p :: rest)
          (fun _ out => ∃ w : ℤ × ℤ, out = cfxVal w :: Val.int p :: rest ∧ inDisc p w ∧
            (2 : ℝ) ^ p * ‖fxC p w - fxC p z1 * fxC p z2‖ < 2)
          (fun _ => C * (p + 1) ^ 2) := by
  obtain ⟨pick, K₁, hpick⟩ := hK.pick
  obtain ⟨mulS, K₂, hmulS⟩ := hF.mulS
  refine ⟨Cmd.seq (pick 2) mulS, 60 * K₁ + K₂ + 1, ?_⟩
  intro main p rest z1 z2 hd1 hd2
  have hcu : vsz (cfxVal z1) ≤ 2 * p + 8 := vsz_cfxVal_le hd1
  have hcv : vsz (cfxVal z2) ≤ 2 * p + 8 := vsz_cfxVal_le hd2
  have hcp : isz ((p : ℤ)) ≤ p + 2 := isz_le _
  have hkey : 3 * (5 * p + 18 + 1) ≤ 60 * ((p + 1) ^ 2) := by nlinarith
  have hpick' : WordR main (pick 2)
      (fun vs => vs = cfxVal z1 :: cfxVal z2 :: Val.int (p : ℤ) :: rest)
      (fun _ out => out = Val.int (p : ℤ) :: cfxVal z1 :: cfxVal z2 :: Val.int (p : ℤ) :: rest)
      (fun _ => 60 * K₁ * ((p + 1) ^ 2)) := by
    refine Work.Kernel.WordR_conseq (hpick main 2) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      simp only [List.length_cons]
      omega
    · intro vs out hvs hout
      rw [hvs] at hout
      have hlen2 : 2 < (cfxVal z1 :: cfxVal z2 :: Val.int (p : ℤ) :: rest).length := by
        simp only [List.length_cons]
        omega
      have hget : (cfxVal z1 :: cfxVal z2 :: Val.int (p : ℤ) :: rest).getD 2 Val.nil
          = Val.int (p : ℤ) := by
        rw [List.getD_eq_getElem
          (l := cfxVal z1 :: cfxVal z2 :: Val.int (p : ℤ) :: rest) (d := Val.nil) hlen2]
        rfl
      rw [hget] at hout
      rw [hout]
    · intro vs hvs
      rw [hvs]
      have hsum : (((cfxVal z1 :: cfxVal z2 :: Val.int (p : ℤ) :: rest).take
          (2 + 1)).map vsz).sum ≤ 5 * p + 18 := by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, vsz_int]
        omega
      calc K₁ * (2 + 1) * ((((cfxVal z1 :: cfxVal z2 :: Val.int (p : ℤ) :: rest).take
              (2 + 1)).map vsz).sum + 1)
          = K₁ * 3 * ((((cfxVal z1 :: cfxVal z2 :: Val.int (p : ℤ) :: rest).take
              (2 + 1)).map vsz).sum + 1) := by norm_num
        _ ≤ K₁ * 3 * (5 * p + 18 + 1) := by
              apply Nat.mul_le_mul_left
              omega
        _ ≤ 60 * K₁ * ((p + 1) ^ 2) := by nlinarith [hkey]
  refine Work.Kernel.WordR_conseq (p := Cmd.seq (pick 2) mulS)
    (Work.Kernel.WordR_seq (B := fun _ => K₂ * ((p + 1) ^ 2)) hpick' (hmulS main p) ?_) ?_ ?_ ?_
  · intro vs mid hvs hmid
    subst mid
    refine ⟨⟨z1, z2, Val.int (p : ℤ) :: rest, rfl, hd1, hd2⟩, ?_⟩
    show K₂ * ((p + 1) ^ 2) ≤ K₂ * ((p + 1) ^ 2)
    exact le_rfl
  · intro vs hvs
    exact hvs
  · intro vs out hvs hout
    obtain ⟨mid, hmid, u', v', rest', w, hmid', hout', hdisc, herr⟩ := hout
    subst mid
    have hB := (List.cons.inj hmid').2
    have hu' : z1 = u' := cfxVal_injective (List.cons.inj hB).1
    have hC := (List.cons.inj hB).2
    have hv' : z2 = v' := cfxVal_injective (List.cons.inj hC).1
    have hrest : rest' = Val.int (p : ℤ) :: rest := ((List.cons.inj hC).2).symm
    refine ⟨w, ?_, hdisc, ?_⟩
    · rw [hout', hrest]
    · rw [hu', hv']
      exact herr
  · intro vs hvs
    have h : 60 * K₁ * (p + 1) ^ 2 + K₂ * (p + 1) ^ 2 = (60 * K₁ + K₂) * (p + 1) ^ 2 := by
      ring
    rw [h]
    exact Nat.mul_le_mul_right _ (by omega)

/-- Entries of `xs` and `ys` (which are `cfxVal` of disc points, indexwise) have encoding size
`≤ 2p + 8`. -/
private theorem pwPairSizes_aux {p : ℕ} {xs ys : List Val} (hlen : xs.length = ys.length)
    (h : ∀ i < xs.length, ∃ z1 z2 : ℤ × ℤ, xs.getD i Val.nil = cfxVal z1 ∧
      ys.getD i Val.nil = cfxVal z2 ∧ inDisc p z1 ∧ inDisc p z2) :
    ∀ x ∈ xs ++ ys, vsz x ≤ 2 * p + 8 := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    obtain ⟨z1, _, h1, _, hd, _⟩ := h i hi
    have hz : xs[i] = cfxVal z1 := by
      rw [← List.getD_eq_getElem (l := xs) (d := Val.nil) hi]
      exact h1
    rw [hz]
    exact vsz_cfxVal_le hd
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hi' : i < xs.length := by rw [hlen]; exact hi
    obtain ⟨_, z2, _, h2, _, hd⟩ := h i hi'
    have hz : ys[i] = cfxVal z2 := by
      rw [← List.getD_eq_getElem (l := ys) (d := Val.nil) hi]
      exact h2
    rw [hz]
    exact vsz_cfxVal_le hd

/-- Arithmetic bookkeeping for the final cost bound. -/
private theorem pwCostIneq (C Kzw p n : ℕ) :
    n * (C * (p + 1) ^ 2 + Kzw * (2 * p + 8 + 1)) + Kzw ≤
      (C + 12 * Kzw + 1) * (n * (p + 1) ^ 2) + (C + 12 * Kzw + 1) := by
  have h9 : 2 * p + 8 + 1 ≤ 11 * (p + 1) ^ 2 := by nlinarith
  have hstep : n * (C * (p + 1) ^ 2 + Kzw * (2 * p + 8 + 1)) ≤
      n * (C * (p + 1) ^ 2 + Kzw * (11 * (p + 1) ^ 2)) := by
    apply Nat.mul_le_mul_left
    exact Nat.add_le_add_left (Nat.mul_le_mul_left Kzw h9) _
  have hA : n * (p + 1) ^ 2 * (C + 11 * Kzw) ≤ n * (p + 1) ^ 2 * (C + 12 * Kzw + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hK' : Kzw ≤ C + 12 * Kzw + 1 := by omega
  have h2 : n * (C * (p + 1) ^ 2 + Kzw * (11 * (p + 1) ^ 2)) + Kzw ≤
      (C + 12 * Kzw + 1) * (n * (p + 1) ^ 2) + (C + 12 * Kzw + 1) :=
    calc n * (C * (p + 1) ^ 2 + Kzw * (11 * (p + 1) ^ 2)) + Kzw
        = n * (p + 1) ^ 2 * (C + 11 * Kzw) + Kzw := by ring
      _ ≤ n * (p + 1) ^ 2 * (C + 12 * Kzw + 1) + (C + 12 * Kzw + 1) :=
            Nat.add_le_add hA hK'
      _ = (C + 12 * Kzw + 1) * (n * (p + 1) ^ 2) + (C + 12 * Kzw + 1) := by ring
  exact le_trans (Nat.add_le_add_right hstep Kzw) h2

theorem blendPwWord (hK : HvdH.KernelLib) (hF : HvdH.FxLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p : ℕ) (xs ys : List HvdH.Val) (rest : List HvdH.Val),
      xs.length = ys.length →
      (∀ i < xs.length, ∃ z1 z2 : ℤ × ℤ, xs.getD i HvdH.Val.nil = HvdH.cfxVal z1 ∧
        ys.getD i HvdH.Val.nil = HvdH.cfxVal z2 ∧ HvdH.inDisc p z1 ∧ HvdH.inDisc p z2) →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.ofList xs :: HvdH.ofList ys :: HvdH.Val.int p :: rest)
        (fun vs out => ∃ zs : List HvdH.Val, out = HvdH.ofList zs :: HvdH.Val.int p :: rest ∧
          zs.length = xs.length ∧
          ∀ i < xs.length, ∃ z1 z2 w : ℤ × ℤ, xs.getD i HvdH.Val.nil = HvdH.cfxVal z1 ∧
            ys.getD i HvdH.Val.nil = HvdH.cfxVal z2 ∧ zs.getD i HvdH.Val.nil = HvdH.cfxVal w ∧
            HvdH.inDisc p w ∧
            (2 : ℝ) ^ p * ‖HvdH.fxC p w - HvdH.fxC p z1 * HvdH.fxC p z2‖ < 2)
        (fun _ => K * (xs.length * (p + 1) ^ 2) + K) := by
  obtain ⟨q, C, hq⟩ := pwMulS_aux hK hF
  obtain ⟨comb, Kzw, hzw⟩ := hK.zipWith
  refine ⟨comb q, C + 12 * Kzw + 1, ?_⟩
  intro main p xs ys rest hlen hpair
  have hsub : ∀ x y : Val, pwP p x y →
      WordR main q (fun vs => vs = x :: y :: Val.int p :: rest)
        (fun _ out => ∃ z : Val, out = z :: Val.int p :: rest ∧ pwQ p x y z ∧
          vsz z ≤ 2 * p + 8)
        (fun _ => C * (p + 1) ^ 2) := by
    intro x y hxy
    obtain ⟨z1, z2, hx, hy, hd1, hd2⟩ := hxy
    subst hx
    subst hy
    refine Work.Kernel.WordR_conseq (hq main p rest z1 z2 hd1 hd2) (fun vs h => h) ?_
      (fun vs _ => le_rfl)
    intro vs out _ hout
    obtain ⟨w, hout', hdisc, herr⟩ := hout
    exact ⟨cfxVal w, hout', ⟨z1, z2, w, rfl, rfl, rfl, hdisc, herr⟩, vsz_cfxVal_le hdisc⟩
  have hL : ∀ x ∈ xs ++ ys, vsz x ≤ 2 * p + 8 := pwPairSizes_aux hlen hpair
  have hmain := hzw main q (Val.int p :: rest) (pwP p) (pwQ p) (C * (p + 1) ^ 2) (2 * p + 8)
    hsub xs ys hlen hpair hL
  refine Work.Kernel.WordR_conseq hmain (fun vs h => h) ?_ ?_
  · intro vs out _ hout
    obtain ⟨zs, h1, h2, h3⟩ := hout
    exact ⟨zs, h1, h2, fun i hi => h3 i hi⟩
  · intro vs _
    exact pwCostIneq C Kzw p xs.length

end Work.Transform
