import Mathlib
import Submission.Work.Resample.buQWelemKit

/-!
# `Work.Resample.buQWelemLin`

The per-element linear-combination word: from `cfxVal a :: cfxVal b :: int σ` (with `σ = ±1`)
produce `cfxVal (a + σ·b)`, at cost `≤ Kc·(P+1)` when the integer components have `isz ≤ P`.

The chain of library words (all acting on a fixed window of at most 6 values) is the one described
in `Submission/Work/Resample/buQWelemKit.lean`:

```
[A,B,σ] →ᵘⁿᶜ [a₁,a₂,B,σ] →ʳᵒˡˡ² [B,a₁,a₂,σ] →ᵘⁿᶜ [b₁,b₂,a₁,a₂,σ] →ᵖⁱᶜᵏ⁴ [σ,b₁,b₂,a₁,a₂,σ]
        →ʳᵒˡˡ¹ [b₁,σ,b₂,a₁,a₂,σ] →ᵐᵘˡˢ [b₁σ,b₂,a₁,a₂,σ] →ᵖⁱᶜᵏ⁴ [σ,b₁σ,b₂,a₁,a₂,σ]
        →ʳᵒˡˡ² [b₂,σ,b₁σ,a₁,a₂,σ] →ᵐᵘˡˢ [b₂σ,b₁σ,a₁,a₂,σ] →ʳᵒˡˡ³ [a₂,b₂σ,b₁σ,a₁,σ]
        →ᵃᵈᵈ [a₂+b₂σ,b₁σ,a₁,σ] →ʳᵒˡˡ² [a₁,a₂+b₂σ,b₁σ,σ] →ʳᵒˡˡ² [b₁σ,a₁,a₂+b₂σ,σ]
        →ᵃᵈᵈ [a₁+b₁σ,a₂+b₂σ,σ] →ʳᵒˡˡ² [σ,a₁+b₁σ,a₂+b₂σ] →ᵈʳᵒᵖ [a₁+b₁σ,a₂+b₂σ]
        →ᶜᵒⁿˢ [cfxVal (a₁+σb₁, a₂+σb₂)]
```

All window values have `vsz ≤ 4P+4` (the components have `isz ≤ P`, the products `bᵢσ` have
`isz (bᵢσ) ≤ isz bᵢ ≤ P`, the sums `aᵢ + bᵢσ` have `isz ≤ 3P+4`, and `isz σ ≤ 3`), so the
uniform roll/pick bound of `105·K·(P+1)` applies to each of the nine roll/pick steps.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH
open Work.Main.word

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-! ## Size facts -/

theorem isz_mul_pm_le_self {x : ℤ} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) : isz (x * σ) ≤ isz x := by
  rcases hσ with rfl | rfl
  · rw [mul_one]
  · rw [mul_neg_one]; simp only [isz, Int.natAbs_neg]; omega

theorem good_int {P : ℕ} {z : ℤ} (h : isz z ≤ P) : vsz (Val.int z) ≤ 4 * P + 4 := by
  rw [vsz_int]; omega

theorem good_pm {P : ℕ} {σ : ℤ} (h : isz σ ≤ 3) : vsz (Val.int σ) ≤ 4 * P + 4 := by
  rw [vsz_int]; omega

theorem good_cfx {P : ℕ} {x y : ℤ} (hx : isz x ≤ P) (hy : isz y ≤ P) :
    vsz (Val.cons (Val.int x) (Val.int y)) ≤ 4 * P + 4 := by
  rw [vsz_cons, vsz_int, vsz_int]; omega

theorem good_mul {P : ℕ} {x σ : ℤ} (hx : isz x ≤ P) (hσ : σ = 1 ∨ σ = -1) :
    vsz (Val.int (x * σ)) ≤ 4 * P + 4 := by
  rw [vsz_int]; have := isz_mul_pm_le_self (x := x) hσ; omega

theorem good_add {P : ℕ} {x y : ℤ} (hx : isz x ≤ P) (hy : isz y ≤ P) :
    vsz (Val.int (x + y)) ≤ 4 * P + 4 := by
  rw [vsz_int]; have := isz_add_le hx hy; omega

/-! ## Uniform roll/pick cost bound on a window of size `≤ 4P+4` -/

theorem bu_rollK4 {rollP : ℕ → Cmd} {KR : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => KR * (k + 1) * (szl (vs.take (k + 1)) + 1)))
    {A : List Val} {k P : ℕ} (hk : k < A.length) (hk5 : k + 1 ≤ 5)
    (hM : ∀ v ∈ A, vsz v ≤ 4 * P + 4) :
    Pipe main (rollP k) A (A.getD k .nil :: A.eraseIdx k) (105 * KR * (P + 1)) := by
  refine Pipe.le (Pipe.roll main h hk) ?_
  have hS : szl (A.take (k + 1)) ≤ 5 * (4 * P + 4) := by
    calc szl (A.take (k + 1)) ≤ (k + 1) * (4 * P + 4) := szlTake_le A (k + 1) (4 * P + 4) hM
      _ ≤ 5 * (4 * P + 4) := Nat.mul_le_mul_right _ hk5
  have hS1 : szl (A.take (k + 1)) + 1 ≤ 21 * (P + 1) := by
    have : (5 : ℕ) * (4 * P + 4) + 1 ≤ 21 * (P + 1) := by nlinarith
    omega
  calc KR * (k + 1) * (szl (A.take (k + 1)) + 1)
      ≤ KR * 5 * (21 * (P + 1)) := Nat.mul_le_mul (Nat.mul_le_mul_left KR hk5) hS1
    _ = 105 * KR * (P + 1) := by ring

theorem bu_pickK4 {pickP : ℕ → Cmd} {KP : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => KP * (k + 1) * (szl (vs.take (k + 1)) + 1)))
    {A : List Val} {k P : ℕ} (hk : k < A.length) (hk5 : k + 1 ≤ 5)
    (hM : ∀ v ∈ A, vsz v ≤ 4 * P + 4) :
    Pipe main (pickP k) A (A.getD k .nil :: A) (105 * KP * (P + 1)) := by
  refine Pipe.le (Pipe.pick main h hk) ?_
  have hS : szl (A.take (k + 1)) ≤ 5 * (4 * P + 4) := by
    calc szl (A.take (k + 1)) ≤ (k + 1) * (4 * P + 4) := szlTake_le A (k + 1) (4 * P + 4) hM
      _ ≤ 5 * (4 * P + 4) := Nat.mul_le_mul_right _ hk5
  have hS1 : szl (A.take (k + 1)) + 1 ≤ 21 * (P + 1) := by
    have : (5 : ℕ) * (4 * P + 4) + 1 ≤ 21 * (P + 1) := by nlinarith
    omega
  calc KP * (k + 1) * (szl (A.take (k + 1)) + 1)
      ≤ KP * 5 * (21 * (P + 1)) := Nat.mul_le_mul (Nat.mul_le_mul_left KP hk5) hS1
    _ = 105 * KP * (P + 1) := by ring

/-! ## Composition that keeps the cost in the normal form `c·(P+1)` -/

theorem Pipe.comp' {main p q : Cmd} {A B D : List Val} {P c c' : ℕ}
    (h1 : Pipe main p A B (c * (P + 1))) (h2 : Pipe main q B D (c' * (P + 1))) :
    Pipe main (p ;;; q) A D ((c + c') * (P + 1)) :=
  Pipe.le (Pipe.comp h1 h2) (le_of_eq (by rw [Nat.add_mul]))

/-! ## The word -/

theorem buQWelemLin (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (q : HvdH.Cmd) (Kc : ℕ),
      ∀ (main : HvdH.Cmd) (P : ℕ) (σ : ℤ) (a b : ℤ × ℤ),
        (σ = 1 ∨ σ = -1) → HvdH.isz a.1 ≤ P → HvdH.isz a.2 ≤ P →
        HvdH.isz b.1 ≤ P → HvdH.isz b.2 ≤ P →
        HvdH.WordR main q
          (fun vs => ∃ rest, vs = HvdH.cfxVal a :: HvdH.cfxVal b :: HvdH.Val.int σ :: rest)
          (fun vs out => ∃ rest, vs = HvdH.cfxVal a :: HvdH.cfxVal b :: HvdH.Val.int σ :: rest ∧
            out = HvdH.cfxVal (a.1 + σ * b.1, a.2 + σ * b.2) :: rest)
          (fun _ => Kc * (P + 1)) := by
  obtain ⟨unconsP, Kuc, huc⟩ := KL.unconsV
  obtain ⟨rollP, KR, hroll⟩ := KL.roll
  obtain ⟨pickP, KP, hpick⟩ := KL.pick
  obtain ⟨consP, Kcs, hcons⟩ := KL.consV
  obtain ⟨dropP, Kd, hdrop⟩ := KL.drop
  obtain ⟨addP, Kad, hadd⟩ := IL.add
  obtain ⟨mulP, Kmul, hmul⟩ := IL.mulS
  let Kc : ℕ := Kuc + (105 * KR + (Kuc + (105 * KP + (105 * KR + (3 * Kmul + (105 * KP + (105 * KR + (3 * Kmul + (105 * KR + (2 * Kad + (105 * KR + (105 * KR + (2 * Kad + (105 * KR + (4 * Kd + (Kcs))))))))))))))))
  refine ⟨unconsP ;;; rollP 2 ;;; unconsP ;;; pickP 4 ;;; rollP 1 ;;; mulP ;;; pickP 4
    ;;; rollP 2 ;;; mulP ;;; rollP 3 ;;; addP ;;; rollP 2 ;;; rollP 2 ;;; addP ;;; rollP 2
    ;;; dropP ;;; consP, Kc, ?_⟩
  intro main P σ a b hσ ha1 ha2 hb1 hb2
  have hsig : isz σ ≤ 3 := isz_pm_one hσ
  have hb1σ : isz (b.1 * σ) ≤ P := le_trans (isz_mul_pm_le_self hσ) hb1
  have hb2σ : isz (b.2 * σ) ≤ P := le_trans (isz_mul_pm_le_self hσ) hb2
  -- ### step 1: uncons `a`
  have H1 : Pipe main unconsP [HvdH.cfxVal a, HvdH.cfxVal b, Val.int σ]
      [Val.int a.1, Val.int a.2, HvdH.cfxVal b, Val.int σ] (Kuc * (P + 1)) :=
    Pipe.le (bu_unconsTail main huc (Val.int a.1) (Val.int a.2) [HvdH.cfxVal b, Val.int σ])
      (bu_const_bound Kuc P)
  -- ### step 2: roll `b` to the front
  have hM2 : ∀ v ∈ ([Val.int a.1, Val.int a.2, HvdH.cfxVal b, Val.int σ] : List Val),
      vsz v ≤ 4 * P + 4 := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact good_int ha1
    · exact good_int ha2
    · exact good_cfx hb1 hb2
    · exact good_pm hsig
  have H2 : Pipe main (rollP 2) [Val.int a.1, Val.int a.2, HvdH.cfxVal b, Val.int σ]
      [HvdH.cfxVal b, Val.int a.1, Val.int a.2, Val.int σ] (105 * KR * (P + 1)) :=
    Pipe.rw (bu_rollK4 main hroll (A := [Val.int a.1, Val.int a.2, HvdH.cfxVal b, Val.int σ])
      (k := 2) (P := P) (by simp) (by norm_num) hM2) (by simp)
  -- ### step 3: uncons `b`
  have H3 : Pipe main unconsP [HvdH.cfxVal b, Val.int a.1, Val.int a.2, Val.int σ]
      [Val.int b.1, Val.int b.2, Val.int a.1, Val.int a.2, Val.int σ] (Kuc * (P + 1)) :=
    Pipe.le (bu_unconsTail main huc (Val.int b.1) (Val.int b.2)
      [Val.int a.1, Val.int a.2, Val.int σ]) (bu_const_bound Kuc P)
  -- ### step 4: bring `σ` up
  have hM4 : ∀ v ∈ ([Val.int b.1, Val.int b.2, Val.int a.1, Val.int a.2, Val.int σ] : List Val),
      vsz v ≤ 4 * P + 4 := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact good_int hb1
    · exact good_int hb2
    · exact good_int ha1
    · exact good_int ha2
    · exact good_pm hsig
  have H4 : Pipe main (pickP 4) [Val.int b.1, Val.int b.2, Val.int a.1, Val.int a.2, Val.int σ]
      [Val.int σ, Val.int b.1, Val.int b.2, Val.int a.1, Val.int a.2, Val.int σ]
      (105 * KP * (P + 1)) :=
    Pipe.rw (bu_pickK4 main hpick (A := [Val.int b.1, Val.int b.2, Val.int a.1, Val.int a.2,
      Val.int σ]) (k := 4) (P := P) (by simp) (by norm_num) hM4) (by simp)
  -- ### step 5: `b₁` to the front
  have hM5 : ∀ v ∈ ([Val.int σ, Val.int b.1, Val.int b.2, Val.int a.1, Val.int a.2,
      Val.int σ] : List Val), vsz v ≤ 4 * P + 4 := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact good_pm hsig
    · exact good_int hb1
    · exact good_int hb2
    · exact good_int ha1
    · exact good_int ha2
    · exact good_pm hsig
  have H5 : Pipe main (rollP 1) [Val.int σ, Val.int b.1, Val.int b.2, Val.int a.1, Val.int a.2,
        Val.int σ] [Val.int b.1, Val.int σ, Val.int b.2, Val.int a.1, Val.int a.2, Val.int σ]
      (105 * KR * (P + 1)) :=
    Pipe.rw (bu_rollK4 main hroll (A := [Val.int σ, Val.int b.1, Val.int b.2, Val.int a.1,
      Val.int a.2, Val.int σ]) (k := 1) (P := P) (by simp) (by norm_num) hM5) (by simp)
  -- ### step 6: `b₁·σ`
  have H6 : Pipe main mulP [Val.int b.1, Val.int σ, Val.int b.2, Val.int a.1, Val.int a.2,
        Val.int σ]
      [Val.int (b.1 * σ), Val.int b.2, Val.int a.1, Val.int a.2, Val.int σ]
      (3 * Kmul * (P + 1)) :=
    Pipe.le (bu_binOpTail main (hmul main) (a := b.1) (b := σ) trivial
      (bu_mul_bound hb1 hsig) (T := [Val.int b.2, Val.int a.1, Val.int a.2, Val.int σ]))
      (le_refl _)
  -- ### step 7: bring `σ` up again
  have hM7 : ∀ v ∈ ([Val.int (b.1 * σ), Val.int b.2, Val.int a.1, Val.int a.2,
      Val.int σ] : List Val), vsz v ≤ 4 * P + 4 := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact good_mul hb1 hσ
    · exact good_int hb2
    · exact good_int ha1
    · exact good_int ha2
    · exact good_pm hsig
  have H7 : Pipe main (pickP 4) [Val.int (b.1 * σ), Val.int b.2, Val.int a.1, Val.int a.2,
        Val.int σ]
      [Val.int σ, Val.int (b.1 * σ), Val.int b.2, Val.int a.1, Val.int a.2, Val.int σ]
      (105 * KP * (P + 1)) :=
    Pipe.rw (bu_pickK4 main hpick (A := [Val.int (b.1 * σ), Val.int b.2, Val.int a.1,
      Val.int a.2, Val.int σ]) (k := 4) (P := P) (by simp) (by norm_num) hM7) (by simp)
  -- ### step 8: `b₂` to the front
  have hM8 : ∀ v ∈ ([Val.int σ, Val.int (b.1 * σ), Val.int b.2, Val.int a.1, Val.int a.2,
      Val.int σ] : List Val), vsz v ≤ 4 * P + 4 := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact good_pm hsig
    · exact good_mul hb1 hσ
    · exact good_int hb2
    · exact good_int ha1
    · exact good_int ha2
    · exact good_pm hsig
  have H8 : Pipe main (rollP 2) [Val.int σ, Val.int (b.1 * σ), Val.int b.2, Val.int a.1,
        Val.int a.2, Val.int σ]
      [Val.int b.2, Val.int σ, Val.int (b.1 * σ), Val.int a.1, Val.int a.2, Val.int σ]
      (105 * KR * (P + 1)) :=
    Pipe.rw (bu_rollK4 main hroll (A := [Val.int σ, Val.int (b.1 * σ), Val.int b.2,
      Val.int a.1, Val.int a.2, Val.int σ]) (k := 2) (P := P) (by simp) (by norm_num) hM8)
      (by simp)
  -- ### step 9: `b₂·σ`
  have H9 : Pipe main mulP [Val.int b.2, Val.int σ, Val.int (b.1 * σ), Val.int a.1, Val.int a.2,
        Val.int σ]
      [Val.int (b.2 * σ), Val.int (b.1 * σ), Val.int a.1, Val.int a.2, Val.int σ]
      (3 * Kmul * (P + 1)) :=
    Pipe.le (bu_binOpTail main (hmul main) (a := b.2) (b := σ) trivial
      (bu_mul_bound hb2 hsig) (T := [Val.int (b.1 * σ), Val.int a.1, Val.int a.2, Val.int σ]))
      (le_refl _)
  -- ### step 10: `a₂` to the front
  have hM10 : ∀ v ∈ ([Val.int (b.2 * σ), Val.int (b.1 * σ), Val.int a.1, Val.int a.2,
      Val.int σ] : List Val), vsz v ≤ 4 * P + 4 := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact good_mul hb2 hσ
    · exact good_mul hb1 hσ
    · exact good_int ha1
    · exact good_int ha2
    · exact good_pm hsig
  have H10 : Pipe main (rollP 3) [Val.int (b.2 * σ), Val.int (b.1 * σ), Val.int a.1,
        Val.int a.2, Val.int σ]
      [Val.int a.2, Val.int (b.2 * σ), Val.int (b.1 * σ), Val.int a.1, Val.int σ]
      (105 * KR * (P + 1)) :=
    Pipe.rw (bu_rollK4 main hroll (A := [Val.int (b.2 * σ), Val.int (b.1 * σ), Val.int a.1,
      Val.int a.2, Val.int σ]) (k := 3) (P := P) (by simp) (by norm_num) hM10) (by simp)
  -- ### step 11: `a₂ + b₂·σ`
  have H11 : Pipe main addP [Val.int a.2, Val.int (b.2 * σ), Val.int (b.1 * σ), Val.int a.1,
        Val.int σ]
      [Val.int (a.2 + b.2 * σ), Val.int (b.1 * σ), Val.int a.1, Val.int σ]
      (2 * Kad * (P + 1)) :=
    Pipe.le (bu_binOpTail main (hadd main) (a := a.2) (b := b.2 * σ) trivial
      (bu_add_bound ha2 hb2σ) (T := [Val.int (b.1 * σ), Val.int a.1, Val.int σ])) (le_refl _)
  -- ### step 12: `a₁` to the front
  have hM12 : ∀ v ∈ ([Val.int (a.2 + b.2 * σ), Val.int (b.1 * σ), Val.int a.1,
      Val.int σ] : List Val), vsz v ≤ 4 * P + 4 := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact good_add ha2 hb2σ
    · exact good_mul hb1 hσ
    · exact good_int ha1
    · exact good_pm hsig
  have H12 : Pipe main (rollP 2) [Val.int (a.2 + b.2 * σ), Val.int (b.1 * σ), Val.int a.1,
        Val.int σ]
      [Val.int a.1, Val.int (a.2 + b.2 * σ), Val.int (b.1 * σ), Val.int σ] (105 * KR * (P + 1)) :=
    Pipe.rw (bu_rollK4 main hroll (A := [Val.int (a.2 + b.2 * σ), Val.int (b.1 * σ),
      Val.int a.1, Val.int σ]) (k := 2) (P := P) (by simp) (by norm_num) hM12) (by simp)
  -- ### step 13: `b₁·σ` to the front
  have hM13 : ∀ v ∈ ([Val.int a.1, Val.int (a.2 + b.2 * σ), Val.int (b.1 * σ),
      Val.int σ] : List Val), vsz v ≤ 4 * P + 4 := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact good_int ha1
    · exact good_add ha2 hb2σ
    · exact good_mul hb1 hσ
    · exact good_pm hsig
  have H13 : Pipe main (rollP 2) [Val.int a.1, Val.int (a.2 + b.2 * σ), Val.int (b.1 * σ),
        Val.int σ]
      [Val.int (b.1 * σ), Val.int a.1, Val.int (a.2 + b.2 * σ), Val.int σ] (105 * KR * (P + 1)) :=
    Pipe.rw (bu_rollK4 main hroll (A := [Val.int a.1, Val.int (a.2 + b.2 * σ),
      Val.int (b.1 * σ), Val.int σ]) (k := 2) (P := P) (by simp) (by norm_num) hM13) (by simp)
  -- ### step 14: `b₁·σ + a₁`
  have H14 : Pipe main addP [Val.int (b.1 * σ), Val.int a.1, Val.int (a.2 + b.2 * σ),
        Val.int σ]
      [Val.int (b.1 * σ + a.1), Val.int (a.2 + b.2 * σ), Val.int σ] (2 * Kad * (P + 1)) :=
    Pipe.le (bu_binOpTail main (hadd main) (a := b.1 * σ) (b := a.1) trivial
      (bu_add_bound hb1σ ha1) (T := [Val.int (a.2 + b.2 * σ), Val.int σ])) (le_refl _)
  -- ### step 15: `σ` back on top
  have hM15 : ∀ v ∈ ([Val.int (b.1 * σ + a.1), Val.int (a.2 + b.2 * σ),
      Val.int σ] : List Val), vsz v ≤ 4 * P + 4 := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact good_add hb1σ ha1
    · exact good_add ha2 hb2σ
    · exact good_pm hsig
  have H15 : Pipe main (rollP 2) [Val.int (b.1 * σ + a.1), Val.int (a.2 + b.2 * σ), Val.int σ]
      [Val.int σ, Val.int (b.1 * σ + a.1), Val.int (a.2 + b.2 * σ)] (105 * KR * (P + 1)) :=
    Pipe.rw (bu_rollK4 main hroll (A := [Val.int (b.1 * σ + a.1), Val.int (a.2 + b.2 * σ),
      Val.int σ]) (k := 2) (P := P) (by simp) (by norm_num) hM15) (by simp)
  -- ### step 16: drop `σ`
  have H16 : Pipe main dropP [Val.int σ, Val.int (b.1 * σ + a.1), Val.int (a.2 + b.2 * σ)]
      [Val.int (b.1 * σ + a.1), Val.int (a.2 + b.2 * σ)] (4 * Kd * (P + 1)) := by
    refine Pipe.le (bu_dropTail main hdrop (Val.int σ) [Val.int (b.1 * σ + a.1),
      Val.int (a.2 + b.2 * σ)]) ?_
    have h3 : vsz (Val.int σ) + 1 ≤ 4 * (P + 1) := by rw [vsz_int]; omega
    calc Kd * (vsz (Val.int σ) + 1) ≤ Kd * (4 * (P + 1)) := Nat.mul_le_mul_left Kd h3
      _ = 4 * Kd * (P + 1) := by ring
  -- ### step 17: build the result value
  have e1 : b.1 * σ + a.1 = a.1 + σ * b.1 := by rw [Int.mul_comm b.1 σ, Int.add_comm]
  have e2 : a.2 + b.2 * σ = a.2 + σ * b.2 := by rw [Int.mul_comm b.2 σ]
  have hcfx : Val.cons (Val.int (b.1 * σ + a.1)) (Val.int (a.2 + b.2 * σ))
      = HvdH.cfxVal (a.1 + σ * b.1, a.2 + σ * b.2) := by
    rw [e1, e2]
    rfl
  have H17 : Pipe main consP [Val.int (b.1 * σ + a.1), Val.int (a.2 + b.2 * σ)]
      [HvdH.cfxVal (a.1 + σ * b.1, a.2 + σ * b.2)] (Kcs * (P + 1)) :=
    Pipe.rw (Pipe.le (bu_consTail main hcons (Val.int (b.1 * σ + a.1))
      (Val.int (a.2 + b.2 * σ)) []) (bu_const_bound Kcs P)) (by rw [hcfx])
  -- ### assemble the chain
  have hAll : Pipe main (unconsP ;;; rollP 2 ;;; unconsP ;;; pickP 4 ;;; rollP 1 ;;; mulP
      ;;; pickP 4 ;;; rollP 2 ;;; mulP ;;; rollP 3 ;;; addP ;;; rollP 2 ;;; rollP 2 ;;; addP
      ;;; rollP 2 ;;; dropP ;;; consP)
      [HvdH.cfxVal a, HvdH.cfxVal b, Val.int σ]
      [HvdH.cfxVal (a.1 + σ * b.1, a.2 + σ * b.2)]
      (Kc * (P + 1)) :=
    Pipe.comp' H1 (Pipe.comp' H2 (Pipe.comp' H3 (Pipe.comp' H4 (Pipe.comp' H5 (Pipe.comp' H6
      (Pipe.comp' H7 (Pipe.comp' H8 (Pipe.comp' H9 (Pipe.comp' H10 (Pipe.comp' H11
      (Pipe.comp' H12 (Pipe.comp' H13 (Pipe.comp' H14 (Pipe.comp' H15 (Pipe.comp' H16 H17)))))))))))))))
  -- ### read off the `WordR`
  intro vs ⟨rest, hvs⟩ s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ :=
    hAll rest (HvdH.cfxVal a :: HvdH.cfxVal b :: Val.int σ :: rest) (by simp) s R
      (by rw [← hvs]; exact hR)
  exact ⟨out, s', n, ⟨rest, hvs, by simpa using hout⟩, hev, hn, hstk, hoth⟩

end Work.Resample
