import Mathlib
import Submission.Work.Fx.scaleSteps

set_option autoImplicit false

namespace Work.Fx

open HvdH

/-!
# Dropping everything below the top value of the window

`roll 1` moves the second value of the window to the top, `drop` removes it; iterating this
`js.length` times leaves `[t0]` out of the window `t0 :: js`, at cost `O((js.length + 1) · (szl · + 1))`.
-/

/-- `m`-fold iteration of "roll the second value of the window to the top, then drop it". -/
def dropIter (rp : ℕ → Cmd) (dp : Cmd) : ℕ → Cmd
  | 0 => .skip
  | n + 1 => .seq (.seq (rp 1) dp) (dropIter rp dp n)

/-- `roll 1` on the first two values of a window `a :: b :: E`: the window becomes `b :: a :: E`. -/
theorem roll1Spec (hk : KernelLib) {main : Cmd} {rp : ℕ → Cmd} {Kr : ℕ}
    (hr : ∀ k, WordR main (rp k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (a b : Val) (E : List Val) :
    Spec main (rp 1) (2 + E.length) (fun t => t = a :: b :: E) (fun _ o => o = b :: a :: E)
      (fun _ => 2 * Kr * (szl (a :: b :: E) + 1)) := by
  have hcost : Kr * (1 + 1) * (szl ([a, b] : List Val) + 1) ≤ 2 * Kr * (szl (a :: b :: E) + 1) := by
    have h1 : szl ([a, b] : List Val) ≤ szl (a :: b :: E) := by
      simp only [szl_cons, szl_nil]
      omega
    have h2 := Nat.mul_le_mul_left (2 * Kr) (Nat.add_le_add_right h1 1)
    calc Kr * (1 + 1) * (szl ([a, b] : List Val) + 1)
        = 2 * Kr * (szl ([a, b] : List Val) + 1) := by ring
      _ ≤ 2 * Kr * (szl (a :: b :: E) + 1) := h2
  have h := Spec.rollStep (hk := hk) (h := hr 1) (A := [a, b]) (k := 1) (by simp) (E := E)
    (Bc := 2 * Kr * (szl (a :: b :: E) + 1)) hcost
  refine Spec.mono (hk := hk) h ?_ ?_ ?_
  · intro t _ hP; rw [hP]; rfl
  · intro t o _ _ hQ
    rw [hQ]
    simp
  · intro t _ _; exact le_rfl

/-- `drop` on a nonempty window `a :: E`: the window becomes `E`. -/
theorem dropHeadSpec (hk : KernelLib) {main : Cmd} {dp : Cmd} {Kd : ℕ}
    (hd : WordR main dp (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => Kd * (vsz (vs.headD .nil) + 1)))
    (a : Val) (E : List Val) :
    Spec main dp (1 + E.length) (fun t => t = a :: E) (fun _ o => o = E)
      (fun _ => Kd * (szl (a :: E) + 1)) := by
  have hcost : Kd * (vsz a + 1) ≤ Kd * (szl (a :: E) + 1) := by
    have h1 := szl_cons a E
    exact Nat.mul_le_mul_left _ (by omega)
  have h := Spec.dropStep (hk := hk) (h := hd) (a := a) (E := E)
    (Bc := Kd * (szl (a :: E) + 1)) hcost
  refine Spec.mono (hk := hk) h ?_ ?_ ?_
  · intro t _ hP; rw [hP]; rfl
  · intro t o _ _ hQ; exact hQ
  · intro t _ _; exact le_rfl

/-- Drop everything strictly below the top value of the current window, keeping only the top value:
`Spec` with window `t0 :: js` (length `js.length+1`) and result `[t0]`, at cost
`K * (js.length+1) * (szl t + 1)` (only the size of the window is charged, the values below it are
never touched).  Program: repeatedly `roll 1` then `drop` (`js.length` times); `roll 1` moves the
second value to the top, `drop` removes it. -/
theorem dropBelow (hk : HvdH.KernelLib) :
    ∃ (prog : ℕ → HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (t0 : HvdH.Val) (js : List HvdH.Val),
      Work.Fx.Spec main (prog js.length) (js.length + 1) (fun t => t = t0 :: js) (fun _ o => o = [t0])
        (fun t => K * (js.length + 1) * (Work.Fx.szl t + 1)) := by
  obtain ⟨rp, Kr, hr⟩ := hk.roll
  obtain ⟨dp, Kd, hd⟩ := hk.drop
  refine ⟨fun m => dropIter rp dp m, 2 * Kr + Kd + 1, ?_⟩
  intro main t0 js
  induction js with
  | nil =>
    show Spec main .skip 1 (fun t => t = t0 :: ([] : List Val)) (fun _ o => o = [t0])
      (fun t => (2 * Kr + Kd + 1) * 1 * (szl t + 1))
    have hskip : Spec main .skip 1 (fun t => t = ([t0] : List Val)) (fun _ o => o = [t0])
        (fun _ => 1) := by
      intro top rest ht hP
      rw [hP]
      refine hk.conseq (main := main) (p := .skip)
        (P := fun _ => True) (P' := fun vs => vs = ([t0] : List Val) ++ rest)
        (Q := fun vs out => out = vs)
        (Q' := fun _ out => ∃ o, out = o ++ rest ∧ o = [t0])
        (C := fun _ => 1) (C' := fun _ => 1)
        (hk.skip main) (fun vs _ => trivial) ?_ (fun vs _ => le_rfl)
      intro vs out hv hQ
      exact ⟨[t0], by rw [hQ, hv], rfl⟩
    refine Spec.mono (hk := hk) hskip (fun t ht hP => hP) (fun t o ht hP hQ => hQ) ?_
    intro t ht hP
    rw [hP]
    have h1 : 1 ≤ vsz t0 := one_le_vsz t0
    simp only [szl_singleton]
    calc (1:ℕ) = 1 * 1 := by ring
      _ ≤ (2 * Kr + Kd + 1) * (vsz t0 + 1) := Nat.mul_le_mul (by omega) (by omega)
      _ = (2 * Kr + Kd + 1) * 1 * (vsz t0 + 1) := by ring
  | cons j js' ih =>
    rw [show (j :: js').length + 1 = 2 + js'.length from by simp only [List.length_cons]; omega]
    have hroll := roll1Spec (hk := hk) (hr := hr main) t0 j js'
    have hdr := dropHeadSpec (hk := hk) (hd := hd main) j (t0 :: js')
    have hpair0 := Spec.seq_det_quad (hk := hk) (p := rp 1) (q := dp) hroll hdr
      (by simp only [List.length_cons]; omega : (j :: t0 :: js').length = 1 + (t0 :: js').length)
    have hpair : Spec main (.seq (rp 1) dp) (2 + js'.length) (fun t => t = t0 :: j :: js')
        (fun _ o => o = t0 :: js') (fun _ => (2 * Kr + Kd) * (szl (t0 :: j :: js') + 1)) := by
      refine Spec.mono (hk := hk) hpair0 (fun t ht hP => hP) (fun t o ht hP hQ => hQ) ?_
      intro t ht hP
      have hs : szl (j :: t0 :: js') = szl (t0 :: j :: js') := by
        simp only [szl_cons]; ring
      rw [hs]
      exact le_of_eq (by ring)
    have hcomp : Spec main (.seq (.seq (rp 1) dp) (dropIter rp dp js'.length)) (2 + js'.length)
        (fun t => t = t0 :: j :: js') (fun t out => ∃ o, o = t0 :: js' ∧ out = [t0])
        (fun t => (2 * Kr + Kd) * (szl (t0 :: j :: js') + 1) +
          (2 * Kr + Kd + 1) * (js'.length + 1) * (szl t + 1)) :=
      Spec.seq (hk := hk) (p := .seq (rp 1) dp) (q := dropIter rp dp js'.length)
        (n := 2 + js'.length) (m := js'.length + 1)
        (P := fun t => t = t0 :: j :: js') (Q := fun _ o => o = t0 :: js')
        (C := fun _ => (2 * Kr + Kd) * (szl (t0 :: j :: js') + 1))
        (P' := fun t => t = t0 :: js') (Q' := fun _ o => o = [t0])
        (C' := fun t => (2 * Kr + Kd + 1) * (js'.length + 1) * (szl t + 1))
        (B := fun t => (2 * Kr + Kd + 1) * (js'.length + 1) * (szl t + 1))
        hpair ih
        (fun t o ht h1 h2 => by rw [h2]; simp only [List.length_cons])
        (fun t o ht h1 h2 => h2)
        (fun t o ht h1 h2 => by
          rw [h1, h2]
          exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (by simp only [szl_cons]; omega) 1))
    refine Spec.mono (hk := hk) hcomp (fun t ht hP => hP) ?_ ?_
    · intro t o ht hP hQ
      rcases hQ with ⟨o', ho', hout⟩
      exact hout
    · intro t ht hP
      rw [hP]
      have h2 : 2 + js'.length = (js'.length + 1) + 1 := by omega
      rw [h2]
      have hstep : (2 * Kr + Kd) * (szl (t0 :: j :: js') + 1)
          ≤ (2 * Kr + Kd + 1) * (szl (t0 :: j :: js') + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      calc (2 * Kr + Kd) * (szl (t0 :: j :: js') + 1)
            + (2 * Kr + Kd + 1) * (js'.length + 1) * (szl (t0 :: j :: js') + 1)
          ≤ (2 * Kr + Kd + 1) * (szl (t0 :: j :: js') + 1)
            + (2 * Kr + Kd + 1) * (js'.length + 1) * (szl (t0 :: j :: js') + 1) :=
            Nat.add_le_add_right hstep _
        _ = (2 * Kr + Kd + 1) * ((js'.length + 1) + 1) * (szl (t0 :: j :: js') + 1) := by ring

end Work.Fx
