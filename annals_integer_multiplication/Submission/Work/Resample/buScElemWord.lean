import Mathlib
import Submission.Work.Resample.buQWscalDefs
import Submission.Work.Resample.buQWelemLin
import Submission.Work.Resample.buQWelemKit

/-!
# `Work.Resample.buScElemWord`: the element word of the scaling `zipWith`

A program `q` which, given the window `[int W, cons (int a) (int b), int D]` on top of the value
stack, produces `[cons (int (tdiv (W*a) D)) (int (tdiv (W*b) D)), int D]`: it multiplies the two
coordinates by `W` and truncates-divides by `D`, keeping the divisor `int D` in place.  The cost is
quadratic in the total bit-size `isz W + isz a + isz b + isz D`, which is what one pays for the two
schoolbook products `W*a`, `W*b` and the two truncating divisions.

The chain of library words (all acting on a fixed window of at most five values, `A = cons a b`,
`X = tdiv (W*a) D`, `Y = tdiv (W*b) D`):

```
[W, A, D] →ᵈᵘᵖ [W, W, A, D] →ʳᵒˡˡ² [A, W, W, D] →ᵘⁿᶜ [a, b, W, W, D] →ʳᵒˡˡ² [W, a, b, W, D]
   →ᵐᵘˡˢ [W·a, b, W, D] →ʳᵒˡˡ³ [D, W·a, b, W] →ᵈᵘᵖ [D, D, W·a, b, W] →ʳᵒˡˡ² [W·a, D, D, b, W]
   →ᵗᵈⁱᵛ [X, D, b, W] →ʳᵒˡˡ² [b, X, D, W] →ʳᵒˡˡ³ [W, b, X, D] →ᵐᵘˡˢ [W·b, X, D]
   →ʳᵒˡˡ² [D, W·b, X] →ᵈᵘᵖ [D, D, W·b, X] →ʳᵒˡˡ² [W·b, D, D, X] →ᵗᵈⁱᵛ [Y, D, X]
   →ʳᵒˡˡ² [X, Y, D] →ᶜᵒⁿˢ [cons X Y, D]
```

(`roll n` moves the value at index `n` to the top.)  Every value occurring in the windows has
`vsz ≤ 4P+4` where `P = isz W + isz a + isz b + isz D`, so the uniform roll bound `105·KR·(P+1)`
applies; `mulS` costs `Kmul·isz _·isz _` and `tdiv` costs `Kt·isz _·isz D`, both `≤ K·(P+1)²`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample
open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-! ## size lemmas -/

theorem buSc_vsz_int (z : ℤ) : vsz (Val.int z) = isz z := Work.Main.word.vsz_int z

theorem buSc_vsz_cons (u v : Val) : vsz (Val.cons u v) = vsz u + vsz v + 1 :=
  Work.Main.word.vsz_cons u v

/-- Truncating division never increases `isz`. -/
theorem buSc_isz_tdiv_le (x y : ℤ) : isz (Int.tdiv x y) ≤ isz x := by
  have h : (Int.tdiv x y).natAbs ≤ x.natAbs := by
    rw [Int.natAbs_tdiv]; exact Nat.div_le_self _ _
  have h2 := Nat.size_le_size h
  simp only [isz]
  omega

theorem buSc_four_int {P : ℕ} {z : ℤ} (h : isz z ≤ P) : vsz (Val.int z) ≤ 4 * P + 4 := by
  rw [buSc_vsz_int]; omega

theorem buSc_four_cons {P : ℕ} {x y : ℤ} (hx : isz x ≤ P) (hy : isz y ≤ P) :
    vsz (Val.cons (Val.int x) (Val.int y)) ≤ 4 * P + 4 := by
  rw [buSc_vsz_cons, buSc_vsz_int, buSc_vsz_int]; omega

/-- Membership bounds for windows, built one entry at a time. -/
theorem buSc_bound_nil {M : ℕ} : ∀ w ∈ ([] : List Val), vsz w ≤ M :=
  fun w hw => absurd hw (List.not_mem_nil (a := w))

theorem buSc_bound_cons {M : ℕ} {v0 : Val} {T : List Val} (hv : vsz v0 ≤ M)
    (hT : ∀ w ∈ T, vsz w ≤ M) : ∀ w ∈ (v0 :: T), vsz w ≤ M := by
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  exacts [hv, hT w hw]

/-! ## cost arithmetic in the normal form `c·(P+1)²` -/

theorem buSc_const_le (c P : ℕ) : c ≤ c * (P + 1) * (P + 1) := by
  have h : (1 : ℕ) ≤ (P + 1) * (P + 1) := Nat.mul_pos (Nat.succ_pos P) (Nat.succ_pos P)
  calc c = c * 1 := by ring
    _ ≤ c * ((P + 1) * (P + 1)) := Nat.mul_le_mul_left c h
    _ = c * (P + 1) * (P + 1) := by ring

theorem buSc_lin_le (c P : ℕ) : c * (P + 1) ≤ c * (P + 1) * (P + 1) := by
  calc c * (P + 1) = c * (P + 1) * 1 := (Nat.mul_one _).symm
    _ ≤ c * (P + 1) * (P + 1) :=
        Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.zero_le P))

theorem buSc_succ_le {K v P : ℕ} (h : v ≤ P) : K * (v + 1) ≤ K * (P + 1) * (P + 1) :=
  le_trans (Nat.mul_le_mul_left K (Nat.succ_le_succ h)) (buSc_lin_le K P)

theorem buSc_mul_le {K u v P : ℕ} (hu : u ≤ P) (hv : v ≤ P) :
    K * u * v ≤ K * (P + 1) * (P + 1) := by
  have h1 : u * v ≤ P * P := Nat.mul_le_mul hu hv
  have h2 : P * P ≤ (P + 1) * (P + 1) := Nat.mul_le_mul (Nat.le_succ P) (Nat.le_succ P)
  calc K * u * v = K * (u * v) := by ring
    _ ≤ K * (P * P) := Nat.mul_le_mul_left K h1
    _ ≤ K * ((P + 1) * (P + 1)) := Nat.mul_le_mul_left K h2
    _ = K * (P + 1) * (P + 1) := by ring

/-- Composition of two `Pipe`s, keeping the cost in the normal form `c·(P+1)²`. -/
theorem Pipe.comp2 {main p q : Cmd} {A B D : List Val} {P c c' : ℕ}
    (h1 : Pipe main p A B (c * (P + 1) * (P + 1)))
    (h2 : Pipe main q B D (c' * (P + 1) * (P + 1))) :
    Pipe main (p ;;; q) A D ((c + c') * (P + 1) * (P + 1)) :=
  Pipe.le (Pipe.comp h1 h2) (le_of_eq (by ring))

/-! ## the element word -/

/-- The element word of the scaling `zipWith`: from the window
`[int W, cons (int a) (int b), int D, T]` it produces
`[cons (int (tdiv (W*a) D)) (int (tdiv (W*b) D)), int D, T]`, i.e. it multiplies the two
coordinates by `W` and truncates-divides by `D`, keeping the divisor `int D` in place.  A working
program: `dup, roll 2, unconsV, roll 2, mulS, roll 3, dup, roll 2, tdiv, roll 2, roll 3, mulS,
roll 2, dup, roll 2, tdiv, roll 2, consV` (see `b1ScaleBody.lean`/`buQWelemShr` for the same proof
style). -/
theorem buScElemWord (KL : KernelLib) (IL : IntLib) :
    ∃ (q : Cmd) (K : ℕ),
    ∀ (main : Cmd) (W a b D : ℤ) (T : List Val), D ≠ 0 →
      WordR main q
        (fun vs => vs = Val.int W :: Val.cons (Val.int a) (Val.int b) :: Val.int D :: T)
        (fun _ out => out = Val.cons (Val.int (Int.tdiv (W * a) D))
          (Val.int (Int.tdiv (W * b) D)) :: Val.int D :: T)
        (fun _ => K * (isz W + isz a + isz b + isz D + 1) *
          (isz W + isz a + isz b + isz D + 1)) := by
  obtain ⟨dupP, Kdup, hdup⟩ := KL.dup
  obtain ⟨rollP, KR, hroll⟩ := KL.roll
  obtain ⟨unconsP, Kuc, huc⟩ := KL.unconsV
  obtain ⟨consP, Kcs, hcons⟩ := KL.consV
  obtain ⟨mulP, Kmul, hmul⟩ := IL.mulS
  obtain ⟨tdivP, Kt, htdiv⟩ := IL.tdiv
  let Kcoef : ℕ := Kdup + (105 * KR + (Kuc + (105 * KR + (Kmul + (105 * KR + (Kdup + (105 * KR + (Kt + (105 * KR + (105 * KR + (Kmul + (105 * KR + (Kdup + (105 * KR + (Kt + (105 * KR + (Kcs)))))))))))))))))
  let prog : Cmd := dupP ;;; rollP 2 ;;; unconsP ;;; rollP 2 ;;; mulP ;;; rollP 3 ;;; dupP
    ;;; rollP 2 ;;; tdivP ;;; rollP 2 ;;; rollP 3 ;;; mulP ;;; rollP 2 ;;; dupP ;;; rollP 2
    ;;; tdivP ;;; rollP 2 ;;; consP
  refine ⟨prog, Kcoef, ?_⟩
  intro main W a b D T hD
  generalize hP : isz W + isz a + isz b + isz D = P
  have hW : isz W ≤ P := by rw [← hP]; omega
  have ha : isz a ≤ P := by rw [← hP]; omega
  have hb : isz b ≤ P := by rw [← hP]; omega
  have hDsz : isz D ≤ P := by rw [← hP]; omega
  have hWa : isz (W * a) ≤ P := by
    rw [← hP]; have := Work.Fx.isz_mul_le W a; omega
  have hWb : isz (W * b) ≤ P := by
    rw [← hP]; have := Work.Fx.isz_mul_le W b; omega
  have hX : isz (Int.tdiv (W * a) D) ≤ P := le_trans (buSc_isz_tdiv_le _ _) hWa
  have hY : isz (Int.tdiv (W * b) D) ≤ P := le_trans (buSc_isz_tdiv_le _ _) hWb
  -- ### step 1: duplicate the weight
  have H1 : Pipe main dupP [Val.int W, Val.cons (Val.int a) (Val.int b), Val.int D]
      [Val.int W, Val.int W, Val.cons (Val.int a) (Val.int b), Val.int D]
      (Kdup * (P + 1) * (P + 1)) :=
    Work.Resample.Pipe.le
      (Work.Resample.Pipe.appendTail [Val.cons (Val.int a) (Val.int b), Val.int D]
        (Work.Resample.Pipe.dup main hdup (Val.int W)))
      (by rw [buSc_vsz_int]; exact buSc_succ_le hW)
  -- ### step 2: bring the complex value to the front
  have hm2 : ∀ v ∈ ([Val.int W, Val.int W, Val.cons (Val.int a) (Val.int b),
      Val.int D] : List Val), vsz v ≤ 4 * P + 4 :=
    buSc_bound_cons (buSc_four_int hW)
      (buSc_bound_cons (buSc_four_int hW)
        (buSc_bound_cons (buSc_four_cons ha hb)
          (buSc_bound_cons (buSc_four_int hDsz) buSc_bound_nil)))
  have H2 : Pipe main (rollP 2)
      [Val.int W, Val.int W, Val.cons (Val.int a) (Val.int b), Val.int D]
      [Val.cons (Val.int a) (Val.int b), Val.int W, Val.int W, Val.int D]
      (105 * KR * (P + 1) * (P + 1)) :=
    Work.Resample.Pipe.le
      (Work.Resample.Pipe.rw
        (bu_rollK4 main hroll
          (A := [Val.int W, Val.int W, Val.cons (Val.int a) (Val.int b), Val.int D])
          (k := 2) (P := P) (by simp) (by norm_num) hm2)
        (by simp))
      (buSc_lin_le (105 * KR) P)
  -- ### step 3: split the complex value
  have H3 : Pipe main unconsP
      [Val.cons (Val.int a) (Val.int b), Val.int W, Val.int W, Val.int D]
      [Val.int a, Val.int b, Val.int W, Val.int W, Val.int D] (Kuc * (P + 1) * (P + 1)) :=
    Work.Resample.Pipe.le
      (bu_unconsTail main huc (Val.int a) (Val.int b) [Val.int W, Val.int W, Val.int D])
      (buSc_const_le Kuc P)
  -- ### step 4: bring the weight up again
  have hm4 : ∀ v ∈ ([Val.int a, Val.int b, Val.int W, Val.int W, Val.int D] : List Val),
      vsz v ≤ 4 * P + 4 :=
    buSc_bound_cons (buSc_four_int ha)
      (buSc_bound_cons (buSc_four_int hb)
        (buSc_bound_cons (buSc_four_int hW)
          (buSc_bound_cons (buSc_four_int hW)
            (buSc_bound_cons (buSc_four_int hDsz) buSc_bound_nil))))
  have H4 : Pipe main (rollP 2)
      [Val.int a, Val.int b, Val.int W, Val.int W, Val.int D]
      [Val.int W, Val.int a, Val.int b, Val.int W, Val.int D]
      (105 * KR * (P + 1) * (P + 1)) :=
    Work.Resample.Pipe.le
      (Work.Resample.Pipe.rw
        (bu_rollK4 main hroll (A := [Val.int a, Val.int b, Val.int W, Val.int W, Val.int D])
          (k := 2) (P := P) (by simp) (by norm_num) hm4)
        (by simp))
      (buSc_lin_le (105 * KR) P)
  -- ### step 5: `W·a`
  have H5 : Pipe main mulP [Val.int W, Val.int a, Val.int b, Val.int W, Val.int D]
      [Val.int (W * a), Val.int b, Val.int W, Val.int D] (Kmul * (P + 1) * (P + 1)) :=
    Work.Resample.Pipe.le
      (bu_binOpTail main (hmul main) (a := W) (b := a) trivial (le_refl _)
        (T := [Val.int b, Val.int W, Val.int D]))
      (buSc_mul_le hW ha)
  -- ### step 6: bring the divisor to the front
  have hm6 : ∀ v ∈ ([Val.int (W * a), Val.int b, Val.int W, Val.int D] : List Val),
      vsz v ≤ 4 * P + 4 :=
    buSc_bound_cons (buSc_four_int hWa)
      (buSc_bound_cons (buSc_four_int hb)
        (buSc_bound_cons (buSc_four_int hW)
          (buSc_bound_cons (buSc_four_int hDsz) buSc_bound_nil)))
  have H6 : Pipe main (rollP 3)
      [Val.int (W * a), Val.int b, Val.int W, Val.int D]
      [Val.int D, Val.int (W * a), Val.int b, Val.int W]
      (105 * KR * (P + 1) * (P + 1)) :=
    Work.Resample.Pipe.le
      (Work.Resample.Pipe.rw
        (bu_rollK4 main hroll (A := [Val.int (W * a), Val.int b, Val.int W, Val.int D])
          (k := 3) (P := P) (by simp) (by norm_num) hm6)
        (by simp))
      (buSc_lin_le (105 * KR) P)
  -- ### step 7: copy the divisor
  have H7 : Pipe main dupP [Val.int D, Val.int (W * a), Val.int b, Val.int W]
      [Val.int D, Val.int D, Val.int (W * a), Val.int b, Val.int W]
      (Kdup * (P + 1) * (P + 1)) :=
    Work.Resample.Pipe.le
      (Work.Resample.Pipe.appendTail [Val.int (W * a), Val.int b, Val.int W]
        (Work.Resample.Pipe.dup main hdup (Val.int D)))
      (by rw [buSc_vsz_int]; exact buSc_succ_le hDsz)
  -- ### step 8: bring `W·a` back
  have hm8 : ∀ v ∈ ([Val.int D, Val.int D, Val.int (W * a), Val.int b,
      Val.int W] : List Val), vsz v ≤ 4 * P + 4 :=
    buSc_bound_cons (buSc_four_int hDsz)
      (buSc_bound_cons (buSc_four_int hDsz)
        (buSc_bound_cons (buSc_four_int hWa)
          (buSc_bound_cons (buSc_four_int hb)
            (buSc_bound_cons (buSc_four_int hW) buSc_bound_nil))))
  have H8 : Pipe main (rollP 2)
      [Val.int D, Val.int D, Val.int (W * a), Val.int b, Val.int W]
      [Val.int (W * a), Val.int D, Val.int D, Val.int b, Val.int W]
      (105 * KR * (P + 1) * (P + 1)) :=
    Work.Resample.Pipe.le
      (Work.Resample.Pipe.rw
        (bu_rollK4 main hroll
          (A := [Val.int D, Val.int D, Val.int (W * a), Val.int b, Val.int W])
          (k := 2) (P := P) (by simp) (by norm_num) hm8)
        (by simp))
      (buSc_lin_le (105 * KR) P)
  -- ### step 9: `X = tdiv (W·a) D`
  have H9 : Pipe main tdivP
      [Val.int (W * a), Val.int D, Val.int D, Val.int b, Val.int W]
      [Val.int (Int.tdiv (W * a) D), Val.int D, Val.int b, Val.int W]
      (Kt * (P + 1) * (P + 1)) :=
    Work.Resample.Pipe.le
      (bu_binOpTail main (htdiv main) (a := W * a) (b := D) hD (le_refl _)
        (T := [Val.int D, Val.int b, Val.int W]))
      (buSc_mul_le hWa hDsz)
  -- ### step 10: bring `b` up
  have hm10 : ∀ v ∈ ([Val.int (Int.tdiv (W * a) D), Val.int D, Val.int b,
      Val.int W] : List Val), vsz v ≤ 4 * P + 4 :=
    buSc_bound_cons (buSc_four_int hX)
      (buSc_bound_cons (buSc_four_int hDsz)
        (buSc_bound_cons (buSc_four_int hb)
          (buSc_bound_cons (buSc_four_int hW) buSc_bound_nil)))
  have H10 : Pipe main (rollP 2)
      [Val.int (Int.tdiv (W * a) D), Val.int D, Val.int b, Val.int W]
      [Val.int b, Val.int (Int.tdiv (W * a) D), Val.int D, Val.int W]
      (105 * KR * (P + 1) * (P + 1)) :=
    Work.Resample.Pipe.le
      (Work.Resample.Pipe.rw
        (bu_rollK4 main hroll
          (A := [Val.int (Int.tdiv (W * a) D), Val.int D, Val.int b, Val.int W])
          (k := 2) (P := P) (by simp) (by norm_num) hm10)
        (by simp))
      (buSc_lin_le (105 * KR) P)
  -- ### step 11: bring the weight up
  have hm11 : ∀ v ∈ ([Val.int b, Val.int (Int.tdiv (W * a) D), Val.int D,
      Val.int W] : List Val), vsz v ≤ 4 * P + 4 :=
    buSc_bound_cons (buSc_four_int hb)
      (buSc_bound_cons (buSc_four_int hX)
        (buSc_bound_cons (buSc_four_int hDsz)
          (buSc_bound_cons (buSc_four_int hW) buSc_bound_nil)))
  have H11 : Pipe main (rollP 3)
      [Val.int b, Val.int (Int.tdiv (W * a) D), Val.int D, Val.int W]
      [Val.int W, Val.int b, Val.int (Int.tdiv (W * a) D), Val.int D]
      (105 * KR * (P + 1) * (P + 1)) :=
    Work.Resample.Pipe.le
      (Work.Resample.Pipe.rw
        (bu_rollK4 main hroll
          (A := [Val.int b, Val.int (Int.tdiv (W * a) D), Val.int D, Val.int W])
          (k := 3) (P := P) (by simp) (by norm_num) hm11)
        (by simp))
      (buSc_lin_le (105 * KR) P)
  -- ### step 12: `W·b`
  have H12 : Pipe main mulP
      [Val.int W, Val.int b, Val.int (Int.tdiv (W * a) D), Val.int D]
      [Val.int (W * b), Val.int (Int.tdiv (W * a) D), Val.int D]
      (Kmul * (P + 1) * (P + 1)) :=
    Work.Resample.Pipe.le
      (bu_binOpTail main (hmul main) (a := W) (b := b) trivial (le_refl _)
        (T := [Val.int (Int.tdiv (W * a) D), Val.int D]))
      (buSc_mul_le hW hb)
  -- ### step 13: the divisor again
  have hm13 : ∀ v ∈ ([Val.int (W * b), Val.int (Int.tdiv (W * a) D),
      Val.int D] : List Val), vsz v ≤ 4 * P + 4 :=
    buSc_bound_cons (buSc_four_int hWb)
      (buSc_bound_cons (buSc_four_int hX)
        (buSc_bound_cons (buSc_four_int hDsz) buSc_bound_nil))
  have H13 : Pipe main (rollP 2)
      [Val.int (W * b), Val.int (Int.tdiv (W * a) D), Val.int D]
      [Val.int D, Val.int (W * b), Val.int (Int.tdiv (W * a) D)]
      (105 * KR * (P + 1) * (P + 1)) :=
    Work.Resample.Pipe.le
      (Work.Resample.Pipe.rw
        (bu_rollK4 main hroll
          (A := [Val.int (W * b), Val.int (Int.tdiv (W * a) D), Val.int D])
          (k := 2) (P := P) (by simp) (by norm_num) hm13)
        (by simp))
      (buSc_lin_le (105 * KR) P)
  -- ### step 14: copy the divisor
  have H14 : Pipe main dupP [Val.int D, Val.int (W * b), Val.int (Int.tdiv (W * a) D)]
      [Val.int D, Val.int D, Val.int (W * b), Val.int (Int.tdiv (W * a) D)]
      (Kdup * (P + 1) * (P + 1)) :=
    Work.Resample.Pipe.le
      (Work.Resample.Pipe.appendTail [Val.int (W * b), Val.int (Int.tdiv (W * a) D)]
        (Work.Resample.Pipe.dup main hdup (Val.int D)))
      (by rw [buSc_vsz_int]; exact buSc_succ_le hDsz)
  -- ### step 15: bring `W·b` back
  have hm15 : ∀ v ∈ ([Val.int D, Val.int D, Val.int (W * b),
      Val.int (Int.tdiv (W * a) D)] : List Val), vsz v ≤ 4 * P + 4 :=
    buSc_bound_cons (buSc_four_int hDsz)
      (buSc_bound_cons (buSc_four_int hDsz)
        (buSc_bound_cons (buSc_four_int hWb)
          (buSc_bound_cons (buSc_four_int hX) buSc_bound_nil)))
  have H15 : Pipe main (rollP 2)
      [Val.int D, Val.int D, Val.int (W * b), Val.int (Int.tdiv (W * a) D)]
      [Val.int (W * b), Val.int D, Val.int D, Val.int (Int.tdiv (W * a) D)]
      (105 * KR * (P + 1) * (P + 1)) :=
    Work.Resample.Pipe.le
      (Work.Resample.Pipe.rw
        (bu_rollK4 main hroll
          (A := [Val.int D, Val.int D, Val.int (W * b), Val.int (Int.tdiv (W * a) D)])
          (k := 2) (P := P) (by simp) (by norm_num) hm15)
        (by simp))
      (buSc_lin_le (105 * KR) P)
  -- ### step 16: `Y = tdiv (W·b) D`
  have H16 : Pipe main tdivP
      [Val.int (W * b), Val.int D, Val.int D, Val.int (Int.tdiv (W * a) D)]
      [Val.int (Int.tdiv (W * b) D), Val.int D, Val.int (Int.tdiv (W * a) D)]
      (Kt * (P + 1) * (P + 1)) :=
    Work.Resample.Pipe.le
      (bu_binOpTail main (htdiv main) (a := W * b) (b := D) hD (le_refl _)
        (T := [Val.int D, Val.int (Int.tdiv (W * a) D)]))
      (buSc_mul_le hWb hDsz)
  -- ### step 17: order the two coordinates
  have hm17 : ∀ v ∈ ([Val.int (Int.tdiv (W * b) D), Val.int D,
      Val.int (Int.tdiv (W * a) D)] : List Val), vsz v ≤ 4 * P + 4 :=
    buSc_bound_cons (buSc_four_int hY)
      (buSc_bound_cons (buSc_four_int hDsz)
        (buSc_bound_cons (buSc_four_int hX) buSc_bound_nil))
  have H17 : Pipe main (rollP 2)
      [Val.int (Int.tdiv (W * b) D), Val.int D, Val.int (Int.tdiv (W * a) D)]
      [Val.int (Int.tdiv (W * a) D), Val.int (Int.tdiv (W * b) D), Val.int D]
      (105 * KR * (P + 1) * (P + 1)) :=
    Work.Resample.Pipe.le
      (Work.Resample.Pipe.rw
        (bu_rollK4 main hroll
          (A := [Val.int (Int.tdiv (W * b) D), Val.int D, Val.int (Int.tdiv (W * a) D)])
          (k := 2) (P := P) (by simp) (by norm_num) hm17)
        (by simp))
      (buSc_lin_le (105 * KR) P)
  -- ### step 18: build the result value
  have H18 : Pipe main consP
      [Val.int (Int.tdiv (W * a) D), Val.int (Int.tdiv (W * b) D), Val.int D]
      [Val.cons (Val.int (Int.tdiv (W * a) D)) (Val.int (Int.tdiv (W * b) D)), Val.int D]
      (Kcs * (P + 1) * (P + 1)) :=
    Work.Resample.Pipe.le
      (bu_consTail main hcons (Val.int (Int.tdiv (W * a) D))
        (Val.int (Int.tdiv (W * b) D)) [Val.int D])
      (buSc_const_le Kcs P)
  -- ### the chain
  have hchain : Pipe main prog
      [Val.int W, Val.cons (Val.int a) (Val.int b), Val.int D]
      [Val.cons (Val.int (Int.tdiv (W * a) D)) (Val.int (Int.tdiv (W * b) D)), Val.int D]
      (Kcoef * (P + 1) * (P + 1)) :=
    Pipe.comp2 H1 (Pipe.comp2 H2 (Pipe.comp2 H3 (Pipe.comp2 H4 (Pipe.comp2 H5
      (Pipe.comp2 H6 (Pipe.comp2 H7 (Pipe.comp2 H8 (Pipe.comp2 H9 (Pipe.comp2 H10
      (Pipe.comp2 H11 (Pipe.comp2 H12 (Pipe.comp2 H13 (Pipe.comp2 H14 (Pipe.comp2 H15
      (Pipe.comp2 H16 (Pipe.comp2 H17 H18))))))))))))))))
  exact hchain T

end Work.Resample

namespace Work.Resample
namespace Work.Resample

/-- The same statement under the (doubly nested) name of the original request template. -/
theorem buScElemWord (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (q : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (W a b D : ℤ) (T : List HvdH.Val), D ≠ 0 →
      HvdH.WordR main q
        (fun vs => vs = HvdH.Val.int W :: HvdH.Val.cons (HvdH.Val.int a) (HvdH.Val.int b) ::
          HvdH.Val.int D :: T)
        (fun _ out => out = HvdH.Val.cons (HvdH.Val.int (Int.tdiv (W * a) D))
          (HvdH.Val.int (Int.tdiv (W * b) D)) :: HvdH.Val.int D :: T)
        (fun _ => K * (HvdH.isz W + HvdH.isz a + HvdH.isz b + HvdH.isz D + 1) *
          (HvdH.isz W + HvdH.isz a + HvdH.isz b + HvdH.isz D + 1)) :=
  _root_.Work.Resample.buScElemWord KL IL

end Work.Resample
end Work.Resample
