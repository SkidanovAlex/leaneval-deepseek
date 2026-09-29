import Mathlib
import Submission.Work.Resample.buQWelemKit
import Submission.Work.Resample.buQWelemShr
import Submission.Work.Resample.buQWelemLin

/-!
# `Work.Resample.buQWelemWord`: the three per-element `B̃` words

`buQWelemWord` requests, for each of the three elementary operations on fixed-point complex
numbers (`a+b`, `a/2^pp`, `a+σb` with `σ = ±1`), a fixed `StackLang` program and a cost linear in
the size bound `P` of the inputs.  The first conjunct (`buQWelemAdd`) is proved here; the second
and third are proved in `Submission/Work/Resample/buQWelemShr.lean` and
`Submission/Work/Resample/buQWelemLin.lean`, using the toolkit `buQWelemKit.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH
open Work.Main.word

local infixl:68 " ;;; " => HvdH.Cmd.seq

/-! ## membership helpers for the window-size obligations -/

theorem buAddW_mem2 {v1 v2 : Val} {M : ℕ} (h1 : vsz v1 ≤ M) (h2 : vsz v2 ≤ M) :
    ∀ v ∈ ([v1, v2] : List Val), vsz v ≤ M := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;> assumption

theorem buAddW_mem3 {v1 v2 v3 : Val} {M : ℕ} (h1 : vsz v1 ≤ M) (h2 : vsz v2 ≤ M)
    (h3 : vsz v3 ≤ M) : ∀ v ∈ ([v1, v2, v3] : List Val), vsz v ≤ M := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl <;> assumption

theorem buAddW_mem4 {v1 v2 v3 v4 : Val} {M : ℕ} (h1 : vsz v1 ≤ M) (h2 : vsz v2 ≤ M)
    (h3 : vsz v3 ≤ M) (h4 : vsz v4 ≤ M) :
    ∀ v ∈ ([v1, v2, v3, v4] : List Val), vsz v ≤ M := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> assumption

/-! ## the complex addition word -/

/-- **First conjunct**: `cfxVal a :: cfxVal b :: rest ↦ cfxVal (a + b) :: rest`, cost `≤ Kc·(P+1)`
when `isz (a.1), isz (a.2), isz (b.1), isz (b.2) ≤ P`. -/
theorem buQWelemAdd (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (q : HvdH.Cmd) (Kc : ℕ),
      ∀ (main : HvdH.Cmd) (P : ℕ) (a b : ℤ × ℤ),
        HvdH.isz a.1 ≤ P → HvdH.isz a.2 ≤ P → HvdH.isz b.1 ≤ P → HvdH.isz b.2 ≤ P →
        HvdH.WordR main q
          (fun vs => ∃ rest, vs = HvdH.cfxVal a :: HvdH.cfxVal b :: rest)
          (fun vs out => ∃ rest, vs = HvdH.cfxVal a :: HvdH.cfxVal b :: rest ∧
            out = HvdH.cfxVal (a.1 + b.1, a.2 + b.2) :: rest)
          (fun _ => Kc * (P + 1)) := by
  obtain ⟨uncP, Ku, hunc⟩ := KL.unconsV
  obtain ⟨rollP, KR, hroll⟩ := KL.roll
  obtain ⟨consP, Kcs, hcons⟩ := KL.consV
  obtain ⟨addP, Kad, hadd⟩ := IL.add
  refine ⟨uncP ;;; rollP 2 ;;; uncP ;;; rollP 2 ;;; rollP 2 ;;; rollP 3 ;;; addP ;;; rollP 2 ;;; rollP 2
      ;;; addP ;;; consP, 2 * Ku + 720 * KR + 4 * Kad + Kcs, ?_⟩
  intro main P a b ha1 ha2 hb1 hb2
  have e_a1 : vsz (Val.int a.1) ≤ 3 * P + 4 := by rw [vsz_int]; omega
  have e_a2 : vsz (Val.int a.2) ≤ 3 * P + 4 := by rw [vsz_int]; omega
  have e_b1 : vsz (Val.int b.1) ≤ 3 * P + 4 := by rw [vsz_int]; omega
  have e_b2 : vsz (Val.int b.2) ≤ 3 * P + 4 := by rw [vsz_int]; omega
  have e_a : vsz (Val.cons (Val.int a.1) (Val.int a.2)) ≤ 3 * P + 4 := vsz_cfxVal_le ha1 ha2
  have e_b : vsz (Val.cons (Val.int b.1) (Val.int b.2)) ≤ 3 * P + 4 := vsz_cfxVal_le hb1 hb2
  have e_ab1 : vsz (Val.int (a.1 + b.1)) ≤ 3 * P + 4 := vsz_int_le (isz_add_le ha1 hb1)
  have e_ab2 : vsz (Val.int (a.2 + b.2)) ≤ 3 * P + 4 := vsz_int_le (isz_add_le ha2 hb2)
  -- step 1: split the first pair
  have H1 : Pipe main uncP
      [Val.cons (Val.int a.1) (Val.int a.2), Val.cons (Val.int b.1) (Val.int b.2)]
      [Val.int a.1, Val.int a.2, Val.cons (Val.int b.1) (Val.int b.2)] (Ku * (P + 1)) :=
    Pipe.le (bu_unconsTail main hunc (Val.int a.1) (Val.int a.2)
      [Val.cons (Val.int b.1) (Val.int b.2)]) (bu_const_bound Ku P)
  -- step 2: bring the second pair to the top
  have H2 : Pipe main (rollP 2) [Val.int a.1, Val.int a.2, Val.cons (Val.int b.1) (Val.int b.2)]
      [Val.cons (Val.int b.1) (Val.int b.2), Val.int a.1, Val.int a.2] (120 * KR * (P + 1)) :=
    bu_rollK main hroll (A := [Val.int a.1, Val.int a.2, Val.cons (Val.int b.1) (Val.int b.2)])
      (k := 2) (P := P) (by simp) (by omega) (buAddW_mem3 e_a1 e_a2 e_b)
  -- step 3: split it
  have H3 : Pipe main uncP [Val.cons (Val.int b.1) (Val.int b.2), Val.int a.1, Val.int a.2]
      [Val.int b.1, Val.int b.2, Val.int a.1, Val.int a.2] (Ku * (P + 1)) :=
    Pipe.le (bu_unconsTail main hunc (Val.int b.1) (Val.int b.2) [Val.int a.1, Val.int a.2])
      (bu_const_bound Ku P)
  -- step 4
  have H4 : Pipe main (rollP 2) [Val.int b.1, Val.int b.2, Val.int a.1, Val.int a.2]
      [Val.int a.1, Val.int b.1, Val.int b.2, Val.int a.2] (120 * KR * (P + 1)) :=
    bu_rollK main hroll (A := [Val.int b.1, Val.int b.2, Val.int a.1, Val.int a.2]) (k := 2)
      (P := P) (by simp) (by omega) (buAddW_mem4 e_b1 e_b2 e_a1 e_a2)
  -- step 5
  have H5 : Pipe main (rollP 2) [Val.int a.1, Val.int b.1, Val.int b.2, Val.int a.2]
      [Val.int b.2, Val.int a.1, Val.int b.1, Val.int a.2] (120 * KR * (P + 1)) :=
    bu_rollK main hroll (A := [Val.int a.1, Val.int b.1, Val.int b.2, Val.int a.2]) (k := 2)
      (P := P) (by simp) (by omega) (buAddW_mem4 e_a1 e_b1 e_b2 e_a2)
  -- step 6
  have H6 : Pipe main (rollP 3) [Val.int b.2, Val.int a.1, Val.int b.1, Val.int a.2]
      [Val.int a.2, Val.int b.2, Val.int a.1, Val.int b.1] (120 * KR * (P + 1)) :=
    bu_rollK main hroll (A := [Val.int b.2, Val.int a.1, Val.int b.1, Val.int a.2]) (k := 3)
      (P := P) (by simp) (by omega) (buAddW_mem4 e_b2 e_a1 e_b1 e_a2)
  -- step 7: a₂ + b₂
  have H7 : Pipe main addP [Val.int a.2, Val.int b.2, Val.int a.1, Val.int b.1]
      [Val.int (a.2 + b.2), Val.int a.1, Val.int b.1] (2 * Kad * (P + 1)) :=
    bu_binOpTail main (hadd main) (a := a.2) (b := b.2) (c := 2 * Kad * (P + 1)) trivial
      (bu_add_bound ha2 hb2) [Val.int a.1, Val.int b.1]
  -- step 8
  have H8 : Pipe main (rollP 2) [Val.int (a.2 + b.2), Val.int a.1, Val.int b.1]
      [Val.int b.1, Val.int (a.2 + b.2), Val.int a.1] (120 * KR * (P + 1)) :=
    bu_rollK main hroll (A := [Val.int (a.2 + b.2), Val.int a.1, Val.int b.1]) (k := 2)
      (P := P) (by simp) (by omega) (buAddW_mem3 e_ab2 e_a1 e_b1)
  -- step 9
  have H9 : Pipe main (rollP 2) [Val.int b.1, Val.int (a.2 + b.2), Val.int a.1]
      [Val.int a.1, Val.int b.1, Val.int (a.2 + b.2)] (120 * KR * (P + 1)) :=
    bu_rollK main hroll (A := [Val.int b.1, Val.int (a.2 + b.2), Val.int a.1]) (k := 2)
      (P := P) (by simp) (by omega) (buAddW_mem3 e_b1 e_ab2 e_a1)
  -- step 10: a₁ + b₁
  have H10 : Pipe main addP [Val.int a.1, Val.int b.1, Val.int (a.2 + b.2)]
      [Val.int (a.1 + b.1), Val.int (a.2 + b.2)] (2 * Kad * (P + 1)) :=
    bu_binOpTail main (hadd main) (a := a.1) (b := b.1) (c := 2 * Kad * (P + 1)) trivial
      (bu_add_bound ha1 hb1) [Val.int (a.2 + b.2)]
  -- step 11: repack
  have H11 : Pipe main consP [Val.int (a.1 + b.1), Val.int (a.2 + b.2)]
      [HvdH.cfxVal (a.1 + b.1, a.2 + b.2)] (Kcs * (P + 1)) :=
    Pipe.le (bu_consTail main hcons (Val.int (a.1 + b.1)) (Val.int (a.2 + b.2)) [])
      (bu_const_bound Kcs P)
  -- the chain
  have hchain : Pipe main
      (uncP ;;; rollP 2 ;;; uncP ;;; rollP 2 ;;; rollP 2 ;;; rollP 3 ;;; addP ;;; rollP 2 ;;; rollP 2
        ;;; addP ;;; consP)
      [Val.cons (Val.int a.1) (Val.int a.2), Val.cons (Val.int b.1) (Val.int b.2)]
      [HvdH.cfxVal (a.1 + b.1, a.2 + b.2)]
      (Ku * (P + 1) + 120 * KR * (P + 1) + Ku * (P + 1) + 120 * KR * (P + 1)
        + 120 * KR * (P + 1) + 120 * KR * (P + 1) + 2 * Kad * (P + 1) + 120 * KR * (P + 1)
        + 120 * KR * (P + 1) + 2 * Kad * (P + 1) + Kcs * (P + 1)) :=
    Pipe.comp (Pipe.comp (Pipe.comp (Pipe.comp (Pipe.comp (Pipe.comp (Pipe.comp (Pipe.comp
      (Pipe.comp (Pipe.comp H1 H2) H3) H4) H5) H6) H7) H8) H9) H10) H11
  have hsum : Ku * (P + 1) + 120 * KR * (P + 1) + Ku * (P + 1) + 120 * KR * (P + 1)
      + 120 * KR * (P + 1) + 120 * KR * (P + 1) + 2 * Kad * (P + 1) + 120 * KR * (P + 1)
      + 120 * KR * (P + 1) + 2 * Kad * (P + 1) + Kcs * (P + 1)
      = (2 * Ku + 720 * KR + 4 * Kad + Kcs) * (P + 1) := by ring
  have hfin : Pipe main
      (uncP ;;; rollP 2 ;;; uncP ;;; rollP 2 ;;; rollP 2 ;;; rollP 3 ;;; addP ;;; rollP 2 ;;; rollP 2
        ;;; addP ;;; consP)
      [Val.cons (Val.int a.1) (Val.int a.2), Val.cons (Val.int b.1) (Val.int b.2)]
      [HvdH.cfxVal (a.1 + b.1, a.2 + b.2)] ((2 * Ku + 720 * KR + 4 * Kad + Kcs) * (P + 1)) :=
    Pipe.le hchain (le_of_eq hsum)
  intro vs hpre s R hR
  obtain ⟨rest, hvs⟩ := hpre
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := hfin rest vs hvs s R hR
  exact ⟨out, s', n, ⟨rest, hvs, hout⟩, hev, hn, hstk, hoth⟩

/-! ## the target -/

theorem buQWelemWord (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    (∃ (q : HvdH.Cmd) (Kc : ℕ),
      ∀ (main : HvdH.Cmd) (P : ℕ) (a b : ℤ × ℤ),
        HvdH.isz a.1 ≤ P → HvdH.isz a.2 ≤ P → HvdH.isz b.1 ≤ P → HvdH.isz b.2 ≤ P →
        HvdH.WordR main q
          (fun vs => ∃ rest, vs = HvdH.cfxVal a :: HvdH.cfxVal b :: rest)
          (fun vs out => ∃ rest, vs = HvdH.cfxVal a :: HvdH.cfxVal b :: rest ∧
            out = HvdH.cfxVal (a.1 + b.1, a.2 + b.2) :: rest)
          (fun _ => Kc * (P + 1))) ∧
    (∃ (q : HvdH.Cmd) (Kc : ℕ),
      ∀ (main : HvdH.Cmd) (P : ℕ) (pp : ℕ) (a : ℤ × ℤ),
        HvdH.isz a.1 ≤ P → HvdH.isz a.2 ≤ P → HvdH.isz (pp : ℤ) ≤ P →
        HvdH.WordR main q
          (fun vs => ∃ rest, vs = HvdH.cfxVal a :: HvdH.Val.int (pp : ℤ) :: rest)
          (fun vs out => ∃ rest, vs = HvdH.cfxVal a :: HvdH.Val.int (pp : ℤ) :: rest ∧
            out = HvdH.cfxVal (Int.tdiv a.1 ((2 : ℤ) ^ pp), Int.tdiv a.2 ((2 : ℤ) ^ pp)) :: rest)
          (fun _ => Kc * (P + 1))) ∧
    (∃ (q : HvdH.Cmd) (Kc : ℕ),
      ∀ (main : HvdH.Cmd) (P : ℕ) (σ : ℤ) (a b : ℤ × ℤ),
        (σ = 1 ∨ σ = -1) → HvdH.isz a.1 ≤ P → HvdH.isz a.2 ≤ P →
        HvdH.isz b.1 ≤ P → HvdH.isz b.2 ≤ P →
        HvdH.WordR main q
          (fun vs => ∃ rest, vs = HvdH.cfxVal a :: HvdH.cfxVal b :: HvdH.Val.int σ :: rest)
          (fun vs out => ∃ rest, vs = HvdH.cfxVal a :: HvdH.cfxVal b :: HvdH.Val.int σ :: rest ∧
            out = HvdH.cfxVal (a.1 + σ * b.1, a.2 + σ * b.2) :: rest)
          (fun _ => Kc * (P + 1))) := by
  obtain ⟨q1, Kc1, h1⟩ := buQWelemAdd KL IL
  obtain ⟨q2, Kc2, h2⟩ := buQWelemShr KL IL
  obtain ⟨q3, Kc3, h3⟩ := buQWelemLin KL IL
  exact ⟨⟨q1, Kc1, h1⟩, ⟨q2, Kc2, h2⟩, ⟨q3, Kc3, h3⟩⟩

end Work.Resample
