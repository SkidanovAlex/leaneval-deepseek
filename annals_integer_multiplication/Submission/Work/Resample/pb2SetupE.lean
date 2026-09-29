import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.pb2Defs
import Submission.Work.Resample.paWords
import Submission.Work.Resample.paProofs1
import Submission.Work.MainP.ss_prod_le_ts_prod

/-!
# Prologue of the `B̃` program (mirror of `paSetupE`)

From the raw precondition of the Resample area (stack 0 holds
`int p, int α, intList ss, intList ts, cvecVal zs0`, all other stacks empty) move the four control
values to stacks 5, 4, 3, 2 (in this order: `p ↦ 5`, `α ↦ 4`, `ss ↦ 3`, `ts ↦ 2`), park the array
on stack 1, insert the boundary marker `paMark`, push `int 1` and put it on stack 6, finally bring
the array back on top of the marker.

Compared with `paSetupE` the only change is that the *input* dimensions `ts` go to stack 2 and the
*output* dimensions `ss` to stack 3, so that the invariant `PB2Inv` (which reads the remaining input
dims on stack 2 and the remaining output dims on stack 3) is satisfied at axis `0`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- The encoding size of `Val.int (n : ℤ)` is `n.size + 2`. -/
theorem pb2Vsz_int_nat (n : ℕ) : vsz (Val.int (n : ℤ)) = n.size + 2 := by
  rw [HvdH.vsz, Work.IntLib.vsz_int, HvdH.isz, Int.natAbs_natCast]

/-- `n.size ≤ n` for every natural number. -/
theorem pb2_size_le_self (n : ℕ) : n.size ≤ n := by
  rw [Nat.size_le]; exact Nat.lt_two_pow_self (n := n)

/-- Mirror of paSetupE for the B half: prologue from the ResampleProp stack to PB2Inv at axis 0. -/
theorem pb2SetupE :
    ∃ (setup : HvdH.Cmd) (Kc : ℕ),
      ∀ (main : HvdH.Cmd) (p α : ℕ) (ss ts : List ℕ)
        (Φ : (i : ℕ) → (Fin (ts.getD i 0) → ℤ × ℤ) → (Fin (ss.getD i 0) → ℤ × ℤ))
        (zs0 : List (ℤ × ℤ)) (rest : List HvdH.Val),
      HvdH.ResParams p α ss ts → zs0.length = ts.prod → (∀ z ∈ zs0, HvdH.inDisc p z) →
      Work.Resample.WordPI main setup
        (fun vs a => vs = [HvdH.Val.int p, HvdH.Val.int α, HvdH.intList ss, HvdH.intList ts,
            HvdH.cvecVal zs0] ++ rest ∧ (∀ k : HvdH.Stk, k ≠ 0 → a k = []))
        (fun vs a out rout b => rout = rest ∧ Work.Resample.PB2Inv p α ss ts Φ zs0 0 out rout b)
        (fun _ _ => Kc * Work.Resample.PASetupBr p ss ts) := by
  obtain ⟨c5, K5, h5⟩ := paW2 5 (by decide)
  obtain ⟨c4, K4, h4⟩ := paW2 4 (by decide)
  obtain ⟨c3, K3, h3⟩ := paW2 3 (by decide)
  obtain ⟨c2, K2, h2⟩ := paW2 2 (by decide)
  obtain ⟨c1, K1, h1⟩ := paW2 1 (by decide)
  obtain ⟨c6, K6, h6⟩ := paW2 6 (by decide)
  obtain ⟨c1b, K1b, h1b⟩ := paW1 1 (by decide)
  obtain ⟨pushP, Kpv, hpush⟩ := Work.Kernel.kernelLib_pushVal
  refine ⟨Cmd.seq c5 (Cmd.seq c4 (Cmd.seq c3 (Cmd.seq c2 (Cmd.seq c1
      (Cmd.seq (Cmd.seq (Cmd.set 0 paMark) (Cmd.push 0 0))
        (Cmd.seq (pushP (Val.int 1)) (Cmd.seq c6 c1b))))))),
    5 * (2 * (K5 + K4 + K3 + K2 + K1 + K6 + K1b + Kpv + 1)), ?_⟩
  intro main p α ss ts Φ zs0 rest hpar hlen0 hdisc
  refine WordPI.ofEv main _ _ _ _ ?_
  intro vs a hpre s R Bg h0 hk
  obtain ⟨hvs, ha0⟩ := hpre
  -- the five moves off the value stack: `p ↦ 5`, `α ↦ 4`, `ss ↦ 3`, `ts ↦ 2`, array ↦ 1
  obtain ⟨o1, b1, s1, n1, ⟨ho1, hb1⟩, he1, hc1, h0₁, hk₁⟩ :=
    h5 main (Val.int p) ([Val.int α, intList ss, intList ts, cvecVal zs0] ++ rest) (a 5) vs a
      ⟨hvs, rfl⟩ s R Bg h0 hk
  obtain ⟨o2, b2, s2, n2, ⟨ho2, hb2⟩, he2, hc2, h0₂, hk₂⟩ :=
    h4 main (Val.int α) ([intList ss, intList ts, cvecVal zs0] ++ rest) (b1 4) o1 b1
      ⟨ho1, rfl⟩ s1 R Bg h0₁ hk₁
  obtain ⟨o3, b3, s3, n3, ⟨ho3, hb3⟩, he3, hc3, h0₃, hk₃⟩ :=
    h3 main (intList ss) ([intList ts, cvecVal zs0] ++ rest) (b2 3) o2 b2
      ⟨ho2, rfl⟩ s2 R Bg h0₂ hk₂
  obtain ⟨o4, b4, s4, n4, ⟨ho4, hb4⟩, he4, hc4, h0₄, hk₄⟩ :=
    h2 main (intList ts) ([cvecVal zs0] ++ rest) (b3 2) o3 b3
      ⟨ho3, rfl⟩ s3 R Bg h0₃ hk₃
  obtain ⟨o5, b5, s5, n5, ⟨ho5, hb5⟩, he5, hc5, h0₅, hk₅⟩ :=
    h1 main (cvecVal zs0) rest (b4 1) o4 b4 ⟨ho4, rfl⟩ s4 R Bg h0₄ hk₄
  -- insert the boundary marker
  obtain ⟨s6, n6, he6, hn6, h6stk, h6fr⟩ := paPushMark_ev main 0 s5
  -- push `int 1` on top of the marker, move it to stack 6
  obtain ⟨o7, s7, n7, ho7, he7, hc7, h0₇, hk₇⟩ :=
    hpush main (Val.int 1) [] trivial s6 (paMark :: (encs rest ++ R))
      (by rw [h6stk, h0₅, ho5]; rfl)
  obtain ⟨o8, b8, s8, n8, ⟨ho8, hb8⟩, he8, hc8, h0₈, hk₈⟩ :=
    h6 main (Val.int 1) [] (b5 6) o7 b5 ⟨ho7, rfl⟩ s7 (paMark :: (encs rest ++ R)) Bg h0₇
      (fun k hk0 => by rw [hk₇ k hk0, h6fr k hk0, hk₅ k hk0])
  -- bring the array back on top of the marker
  obtain ⟨o9, b9, s9, n9, ⟨ho9, hb9⟩, he9, hc9, h0₉, hk₉⟩ :=
    h1b main (cvecVal zs0) [] o8 b8 ⟨ho8, by
      rw [hb8, hb5, hb4, hb3, hb2, hb1]
      simp [ha0]⟩ s8 (paMark :: (encs rest ++ R)) Bg h0₈ hk₈
  -- the resulting state is the invariant at `j = 0`
  have hPB : PB2Inv p α ss ts Φ zs0 0 [cvecVal zs0] rest b9 := by
    refine ⟨cvecVal zs0, ⟨rfl, ?_, ?_, ?_⟩, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show zs0.length = (ss.take 0).prod * (ts.drop 0).prod
      rw [hlen0]; simp
    · exact hdisc
    · have h1 := pa_vsz_cvec_le (p := p) (zs := zs0) hdisc
      rw [hlen0] at h1
      exact h1
    · rw [hb9, Function.update_self]
    · rw [hb9, hb8, hb5, hb4, hb3, hb2, hb1]; simp [ha0, List.drop_zero]
    · rw [hb9, hb8, hb5, hb4, hb3, hb2, hb1]; simp [ha0, List.drop_zero]
    · rw [hb9, hb8, hb5, hb4, hb3, hb2, hb1]; simp [ha0]
    · rw [hb9, hb8, hb5, hb4, hb3, hb2, hb1]; simp [ha0]
    · rw [hb9, hb8, hb5, hb4, hb3, hb2, hb1]; simp [ha0, List.take_zero]
    · intro k hk0 hk6
      by_cases h1 : k = 1
      · subst h1; rw [hb9, Function.update_self]
      · have hk2 : k ≠ 2 := fun h => hk6 (by rw [h]; decide)
        have hk3 : k ≠ 3 := fun h => hk6 (by rw [h]; decide)
        have hk4 : k ≠ 4 := fun h => hk6 (by rw [h]; decide)
        have hk5 : k ≠ 5 := fun h => hk6 (by rw [h]; decide)
        have hk7 : k ≠ 6 := fun h => hk6 (by rw [h]; decide)
        rw [hb9, hb8, hb5, hb4, hb3, hb2, hb1]
        simp [ha0, h1, hk0, hk2, hk3, hk4, hk5, hk7]
  -- the cost bound
  have hp100 : 100 ≤ p := hpar.2.2.1
  have hα2 : 2 ≤ α := hpar.2.2.2.1
  have hαp2 : α ^ 2 < p := hpar.2.2.2.2.1
  have hαp : α ≤ p := by
    have h1 : α ≤ α ^ 2 := by nlinarith
    omega
  set Z : ℕ := p + 1 with hZ
  set Y : ℕ := vsz (intList ss) + vsz (intList ts) + 1 with hY
  set X1 : ℕ := ts.prod * (2 * p + 8) + ts.prod + 2 with hX1
  set M : ℕ := 2 * (K5 + K4 + K3 + K2 + K1 + K6 + K1b + Kpv + 1) with hM
  have hsX : vsz (cvecVal zs0) + 1 ≤ X1 := by
    have h := pa_vsz_cvec_le (p := p) (zs := zs0) hdisc
    rw [hlen0] at h
    rw [hX1]; omega
  have hAp : vsz (Val.int (p:ℤ)) + 1 ≤ 2 * Z := by
    rw [hZ, pb2Vsz_int_nat]
    have h := pb2_size_le_self p
    omega
  have hAα : vsz (Val.int (α:ℤ)) + 1 ≤ 2 * Z := by
    rw [hZ, pb2Vsz_int_nat]
    have h := pb2_size_le_self α
    omega
  have hK5M : 2 * K5 ≤ M := by rw [hM]; omega
  have hK4M : 2 * K4 ≤ M := by rw [hM]; omega
  have hK3M : K3 ≤ M := by rw [hM]; omega
  have hK2M : K2 ≤ M := by rw [hM]; omega
  have hK1M : K1 ≤ M := by rw [hM]; omega
  have hK6M : 2 * K6 ≤ M := by rw [hM]; omega
  have hK1bM : K1b ≤ M := by rw [hM]; omega
  have hKpvM : 2 * Kpv ≤ M := by rw [hM]; omega
  have hYb : vsz (intList ss) + 1 ≤ Y := by rw [hY]; omega
  have hYb' : vsz (intList ts) + 1 ≤ Y := by rw [hY]; omega
  have hM2 : 2 ≤ M := by rw [hM]; omega
  have hZ2 : 2 ≤ Z := by rw [hZ]; omega
  have h4one : vsz (Val.int (1:ℤ)) + 1 = 4 := by decide
  have hb1 : n1 ≤ M * Z :=
    le_trans hc1 (calc K5 * (vsz (Val.int (p:ℤ)) + 1) ≤ K5 * (2 * Z) := Nat.mul_le_mul_left K5 hAp
      _ = 2 * K5 * Z := by ring
      _ ≤ M * Z := Nat.mul_le_mul_right Z hK5M)
  have hb2 : n2 ≤ M * Z :=
    le_trans hc2 (calc K4 * (vsz (Val.int (α:ℤ)) + 1) ≤ K4 * (2 * Z) := Nat.mul_le_mul_left K4 hAα
      _ = 2 * K4 * Z := by ring
      _ ≤ M * Z := Nat.mul_le_mul_right Z hK4M)
  have hb3 : n3 ≤ M * Y :=
    le_trans hc3 (le_trans (Nat.mul_le_mul_left K3 hYb) (Nat.mul_le_mul_right Y hK3M))
  have hb4 : n4 ≤ M * Y :=
    le_trans hc4 (le_trans (Nat.mul_le_mul_left K2 hYb') (Nat.mul_le_mul_right Y hK2M))
  have hb5 : n5 ≤ M * X1 :=
    le_trans hc5 (le_trans (Nat.mul_le_mul_left K1 hsX) (Nat.mul_le_mul_right X1 hK1M))
  have hb6 : n6 ≤ M * Z := by
    have h2 : 2 ≤ M * Z := le_trans (by norm_num) (Nat.mul_le_mul hM2 hZ2)
    omega
  have hb7 : n7 ≤ M * Z := by
    rw [h4one] at hc7
    refine le_trans hc7 (le_trans (le_of_eq (by ring : Kpv * 4 = 2 * Kpv * 2)) ?_)
    exact Nat.mul_le_mul hKpvM hZ2
  have hb8 : n8 ≤ M * Z := by
    rw [h4one] at hc8
    refine le_trans hc8 (le_trans (le_of_eq (by ring : K6 * 4 = 2 * K6 * 2)) ?_)
    exact Nat.mul_le_mul hK6M hZ2
  have hb9 : n9 ≤ M * X1 :=
    le_trans hc9 (le_trans (Nat.mul_le_mul_left K1b hsX) (Nat.mul_le_mul_right X1 hK1bM))
  have hS : n1 + (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + n9)))))))
      ≤ M * (5 * Z + 2 * Y + 2 * X1) := by
    have h := add_le_add hb1 (add_le_add hb2 (add_le_add hb3 (add_le_add hb4
      (add_le_add hb5 (add_le_add hb6 (add_le_add hb7 (add_le_add hb8 hb9)))))))
    have hsum : M * Z + (M * Z + (M * Y + (M * Y + (M * X1 + (M * Z + (M * Z +
        (M * Z + M * X1))))))) = M * (5 * Z + 2 * Y + 2 * X1) := by ring
    exact le_trans h (le_of_eq hsum)
  have hPAS : Z + Y + X1 ≤ PASetupBr p ss ts := by
    rw [hZ, hY, hX1]
    simp only [PASetupBr]
    omega
  have hcost : n1 + (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + n9)))))))
      ≤ 5 * (2 * (K5 + K4 + K3 + K2 + K1 + K6 + K1b + Kpv + 1)) * PASetupBr p ss ts := by
    have hKc : 5 * (2 * (K5 + K4 + K3 + K2 + K1 + K6 + K1b + Kpv + 1)) = 5 * M := by rw [hM]
    rw [hKc]
    calc n1 + (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + n9)))))))
        ≤ M * (5 * Z + 2 * Y + 2 * X1) := hS
      _ ≤ M * (5 * (Z + Y + X1)) := Nat.mul_le_mul_left M (by omega)
      _ = 5 * M * (Z + Y + X1) := by ring
      _ ≤ 5 * M * PASetupBr p ss ts := Nat.mul_le_mul_left (5 * M) hPAS
  refine ⟨[cvecVal zs0], rest, b9, s9,
    n1 + (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + n9))))))),
    ⟨rfl, hPB⟩, ?_, hcost, ?_, hk₉⟩
  · exact Eval.seq he1 (Eval.seq he2 (Eval.seq he3 (Eval.seq he4 (Eval.seq he5
      (Eval.seq he6 (Eval.seq he7 (Eval.seq he8 he9)))))))
  · rw [h0₉, ho9, ho8]

end Work.Resample
