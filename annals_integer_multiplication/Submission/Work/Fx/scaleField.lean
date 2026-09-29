import Mathlib
import Submission.Work.Fx.scaleSteps
import Submission.Work.Fx.sqrtMaxFacts
import Submission.Work.Fx.dropBelow
import Submission.Work.Fx.scaleMathB

set_option autoImplicit false
set_option maxHeartbeats 40000000

namespace Work.Fx

open HvdH

/-! ## Cost estimates (every step costs at most `4000*KK*(p+1)^2`) -/

theorem le_sq1_x1 (K p : ℕ) : K * (p + 1) ≤ K * (p + 1) ^ 2 := by
  apply Nat.mul_le_mul_left
  rw [pow_two]
  calc (p + 1) = (p + 1) * 1 := (Nat.mul_one _).symm
    _ ≤ (p + 1) * (p + 1) := Nat.mul_le_mul_left _ (by omega)

theorem pickroll_cost_x1 {K KK p k s : ℕ} (hK : K ≤ KK) (hk : k + 1 ≤ 10) (hs : s ≤ 130 * (p + 1)) :
    K * (k + 1) * (s + 1) ≤ 4000 * KK * (p + 1) ^ 2 := by
  have hs1 : s + 1 ≤ 131 * (p + 1) := by omega
  have h1 : K * (k + 1) * (s + 1) ≤ K * 10 * (131 * (p + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left K hk) hs1
  have h2 : K * 10 * (131 * (p + 1)) ≤ 4000 * KK * (p + 1) ^ 2 := by
    have hK' : 1310 * K ≤ 4000 * KK := by omega
    calc K * 10 * (131 * (p + 1)) = (1310 * K) * (p + 1) := by ring
      _ ≤ (4000 * KK) * (p + 1) := Nat.mul_le_mul_right _ hK'
      _ ≤ (4000 * KK) * (p + 1) ^ 2 := le_sq1_x1 _ _
  exact le_trans h1 h2

theorem val_cost {K KK p : ℕ} {v : Val} (hK : K ≤ KK) (hv : vsz v ≤ 9 * (p + 1)) :
    K * (vsz v + 1) ≤ 4000 * KK * (p + 1) ^ 2 := by
  have h1 : K * (vsz v + 1) ≤ K * (10 * (p + 1)) := Nat.mul_le_mul_left K (by omega)
  have h2 : K * (10 * (p + 1)) ≤ 4000 * KK * (p + 1) ^ 2 := by
    have hK' : 10 * K ≤ 4000 * KK := by omega
    calc K * (10 * (p + 1)) = (10 * K) * (p + 1) := by ring
      _ ≤ (4000 * KK) * (p + 1) := Nat.mul_le_mul_right _ hK'
      _ ≤ (4000 * KK) * (p + 1) ^ 2 := le_sq1_x1 _ _
  exact le_trans h1 h2

theorem swap_cost {K KK p : ℕ} {v w : Val} (hK : K ≤ KK) (hv : vsz v ≤ 9 * (p + 1))
    (hw : vsz w ≤ 9 * (p + 1)) : K * (vsz v + vsz w + 1) ≤ 4000 * KK * (p + 1) ^ 2 := by
  have h1 : K * (vsz v + vsz w + 1) ≤ K * (19 * (p + 1)) := Nat.mul_le_mul_left K (by omega)
  have h2 : K * (19 * (p + 1)) ≤ 4000 * KK * (p + 1) ^ 2 := by
    have hK' : 19 * K ≤ 4000 * KK := by omega
    calc K * (19 * (p + 1)) = (19 * K) * (p + 1) := by ring
      _ ≤ (4000 * KK) * (p + 1) := Nat.mul_le_mul_right _ hK'
      _ ≤ (4000 * KK) * (p + 1) ^ 2 := le_sq1_x1 _ _
  exact le_trans h1 h2

theorem mul2_cost {K KK p : ℕ} {a b : ℤ} (hK : K ≤ KK) (ha : isz a ≤ 9 * (p + 1))
    (hb : isz b ≤ 9 * (p + 1)) : K * isz a * isz b ≤ 4000 * KK * (p + 1) ^ 2 := by
  have h1 : K * isz a * isz b ≤ K * (9 * (p + 1)) * (9 * (p + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left K ha) hb
  have h2 : K * (9 * (p + 1)) * (9 * (p + 1)) ≤ 4000 * KK * (p + 1) ^ 2 := by
    have hK' : 81 * K ≤ 4000 * KK := by omega
    calc K * (9 * (p + 1)) * (9 * (p + 1)) = (81 * K) * (p + 1) * (p + 1) := by ring
      _ ≤ (4000 * KK) * (p + 1) * (p + 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hK')
      _ = 4000 * KK * (p + 1) ^ 2 := by ring
  exact le_trans h1 h2

theorem addsub_cost_x1 {K KK p : ℕ} {a b : ℤ} (hK : K ≤ KK) (ha : isz a ≤ 9 * (p + 1))
    (hb : isz b ≤ 9 * (p + 1)) : K * (isz a + isz b) ≤ 4000 * KK * (p + 1) ^ 2 := by
  have h1 : K * (isz a + isz b) ≤ K * (18 * (p + 1)) := Nat.mul_le_mul_left K (by omega)
  have h2 : K * (18 * (p + 1)) ≤ 4000 * KK * (p + 1) ^ 2 := by
    have hK' : 18 * K ≤ 4000 * KK := by omega
    calc K * (18 * (p + 1)) = (18 * K) * (p + 1) := by ring
      _ ≤ (4000 * KK) * (p + 1) := Nat.mul_le_mul_right _ hK'
      _ ≤ (4000 * KK) * (p + 1) ^ 2 := le_sq1_x1 _ _
  exact le_trans h1 h2

theorem sq_cost {K KK p : ℕ} {a : ℤ} (hK : K ≤ KK) (ha : isz a ≤ 9 * (p + 1)) :
    K * isz a ^ 2 ≤ 4000 * KK * (p + 1) ^ 2 := by
  have h1 : K * isz a ^ 2 ≤ K * (9 * (p + 1)) * (9 * (p + 1)) := by
    have h : isz a ^ 2 ≤ (9 * (p + 1)) * (9 * (p + 1)) := by
      rw [pow_two]; exact Nat.mul_le_mul ha ha
    calc K * isz a ^ 2 = K * (isz a ^ 2) := by ring
      _ ≤ K * ((9 * (p + 1)) * (9 * (p + 1))) := Nat.mul_le_mul_left K h
      _ = K * (9 * (p + 1)) * (9 * (p + 1)) := by ring
  have h2 : K * (9 * (p + 1)) * (9 * (p + 1)) ≤ 4000 * KK * (p + 1) ^ 2 := by
    have hK' : 81 * K ≤ 4000 * KK := by omega
    calc K * (9 * (p + 1)) * (9 * (p + 1)) = (81 * K) * (p + 1) * (p + 1) := by ring
      _ ≤ (4000 * KK) * (p + 1) * (p + 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hK')
      _ = 4000 * KK * (p + 1) ^ 2 := by ring
  exact le_trans h1 h2

theorem pow2c_cost {K KK p : ℕ} (hK : K ≤ KK) :
    K * (p + isz (p : ℤ)) ≤ 4000 * KK * (p + 1) ^ 2 := by
  have hp3 : p + isz (p : ℤ) ≤ 3 * (p + 1) := by
    have hna : ((p : ℤ)).natAbs = p := Int.natAbs_natCast p
    have hsz : p.size ≤ p := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p))
    have : isz ((p : ℤ)) = p.size + 2 := by simp only [isz, hna]
    omega
  have h1 : K * (p + isz (p : ℤ)) ≤ K * (3 * (p + 1)) := Nat.mul_le_mul_left K hp3
  have h2 : K * (3 * (p + 1)) ≤ 4000 * KK * (p + 1) ^ 2 := by
    have hK' : 3 * K ≤ 4000 * KK := by omega
    calc K * (3 * (p + 1)) = (3 * K) * (p + 1) := by ring
      _ ≤ (4000 * KK) * (p + 1) := Nat.mul_le_mul_right _ hK'
      _ ≤ (4000 * KK) * (p + 1) ^ 2 := le_sq1_x1 _ _
  exact le_trans h1 h2

theorem shl_cost {K KK p : ℕ} {a : ℤ} (hK : K ≤ KK) (ha : isz a ≤ 9 * (p + 1)) :
    K * (isz a + p + isz (p : ℤ)) ≤ 4000 * KK * (p + 1) ^ 2 := by
  have hp : isz ((p : ℤ)) ≤ 9 * (p + 1) := by
    have hna : ((p : ℤ)).natAbs = p := Int.natAbs_natCast p
    have hsz : p.size ≤ p := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p))
    have : isz ((p : ℤ)) = p.size + 2 := by simp only [isz, hna]
    omega
  have h1 : K * (isz a + p + isz (p : ℤ)) ≤ K * (19 * (p + 1)) := Nat.mul_le_mul_left K (by omega)
  have h2 : K * (19 * (p + 1)) ≤ 4000 * KK * (p + 1) ^ 2 := by
    have hK' : 19 * K ≤ 4000 * KK := by omega
    calc K * (19 * (p + 1)) = (19 * K) * (p + 1) := by ring
      _ ≤ (4000 * KK) * (p + 1) := Nat.mul_le_mul_right _ hK'
      _ ≤ (4000 * KK) * (p + 1) ^ 2 := le_sq1_x1 _ _
  exact le_trans h1 h2

theorem small_cost {K KK p m : ℕ} (hK : K ≤ KK) (hm : m ≤ 9 * (p + 1)) :
    K * m ≤ 4000 * KK * (p + 1) ^ 2 := by
  have h1 : K * m ≤ K * (9 * (p + 1)) := Nat.mul_le_mul_left K hm
  have h2 : K * (9 * (p + 1)) ≤ 4000 * KK * (p + 1) ^ 2 := by
    have hK' : 9 * K ≤ 4000 * KK := by omega
    calc K * (9 * (p + 1)) = (9 * K) * (p + 1) := by ring
      _ ≤ (4000 * KK) * (p + 1) := Nat.mul_le_mul_right _ hK'
      _ ≤ (4000 * KK) * (p + 1) ^ 2 := le_sq1_x1 _ _
  exact le_trans h1 h2

/-- The right-nested sum of `n` copies of `S` (the shape of the accumulated cost of the chain). -/
def costN (S : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => S + costN S n

theorem costN_eq (S n : ℕ) : costN S n = n * S := by
  induction n with
  | zero => rw [costN, Nat.zero_mul]
  | succ n ih => rw [costN, ih]; ring

theorem one_le_pow2 (p : ℕ) : (1 : ℤ) ≤ 2 ^ p := by
  have : (0 : ℤ) < 2 ^ p := by positivity
  omega

theorem uncon_cost_x1 {K KK p : ℕ} (hK : K ≤ KK) : K ≤ 4000 * KK * (p + 1) ^ 2 := by
  have hp1 : 1 ≤ (p + 1) ^ 2 := by nlinarith [Nat.zero_le p]
  calc K ≤ KK := hK
    _ = KK * 1 := (Nat.mul_one KK).symm
    _ ≤ KK * ((p + 1) ^ 2) := Nat.mul_le_mul_left KK hp1
    _ ≤ 4000 * KK * (p + 1) ^ 2 := by
        exact Nat.mul_le_mul_right _ (by omega)

/-- Cost of one `dropBelow` cleanup step. -/
theorem cleanse_cost {K KK p m s : ℕ} (hK : K ≤ KK) (hm : m + 1 ≤ 10) (hs : s ≤ 130 * (p + 1)) :
    K * (m + 1) * (s + 1) ≤ 4000 * KK * (p + 1) ^ 2 :=
  pickroll_cost_x1 hK hm hs

end Work.Fx

namespace Work.Fx

open HvdH

/-- The scaling program of paper Lemma 2.2 (the paper's proof, with the branch `a ≤ 4^p`
absorbed into the `max`, so that no test is needed). -/
def scaleProg (rollP : ℕ → Cmd) (unconsP dupP swP dropP : Cmd) (pickP : ℕ → Cmd)
    (pushP : Val → Cmd) (consP mulP addP maxP shlP tdivP sqP powP : Cmd)
    (dropbP : ℕ → Cmd) : Cmd :=
  .seq (rollP 2) (.seq unconsP (.seq (pickP 3) (.seq mulP (.seq (pickP 3) (.seq (rollP 2) (.seq swP (.seq mulP (.seq (pickP 0) (.seq (pickP 0) (.seq mulP (.seq (pickP 2) (.seq (pickP 0) (.seq mulP (.seq addP (.seq dupP (.seq sqP (.seq (pushP (.int 1)) (.seq addP (.seq (pickP 4) (.seq powP (.seq maxP (.seq (pickP 3) (.seq (pickP 5) (.seq (pickP 1) (.seq shlP (.seq (pickP 2) (.seq (rollP 1) (.seq tdivP (.seq (pickP 6) (.seq (pickP 5) (.seq shlP (.seq (pickP 3) (.seq (rollP 1) (.seq tdivP (.seq (rollP 1) (.seq consP ((dropbP 7))))))))))))))))))))))))))))))))))))))

theorem scaleField (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p c : ℕ), 1 ≤ c → c ≤ 2 ^ p → HvdH.WordR main prog
      (fun vs => ∃ (u : ℤ × ℤ) (rest : List HvdH.Val),
        vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (c : ℤ) :: HvdH.cfxVal u :: rest ∧ HvdH.inDisc p u)
      (fun vs out => ∃ (u : ℤ × ℤ) (rest : List HvdH.Val) (w : ℤ × ℤ),
        vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (c : ℤ) :: HvdH.cfxVal u :: rest ∧
        out = HvdH.cfxVal w :: rest ∧ HvdH.inDisc p w ∧ ∀ x : ℂ, (c : ℝ) * ‖x‖ ≤ 1 →
          (2 : ℝ) ^ p * ‖HvdH.fxC p w - (c : ℂ) * x‖ <
            2 * c * ((2 : ℝ) ^ p * ‖HvdH.fxC p u - x‖) + 3)
      (fun _ => K * (p + 1) ^ 2) := by
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨pickP, Kp, hpick⟩ := hk.pick
  obtain ⟨dupP, Kdup, hdup⟩ := hk.dup
  obtain ⟨swP, Ksw, hsw⟩ := hk.swap
  obtain ⟨dropP, Kdr, hdrop⟩ := hk.drop
  obtain ⟨pushP, Kpu, hpush⟩ := hk.pushVal
  obtain ⟨consP, Kco, hcons⟩ := hk.consV
  obtain ⟨unconsP, Kun, huncons⟩ := hk.unconsV
  obtain ⟨mulP, Kmul, hmul⟩ := hi.mulS
  obtain ⟨addP, Kadd, hadd⟩ := hi.add
  obtain ⟨maxP, Kmax, hmax⟩ := hi.max
  obtain ⟨shlP, Kshl, hshl⟩ := hi.shl
  obtain ⟨tdivP, Ktd, htd⟩ := hi.tdiv
  obtain ⟨sqP, Ksq, hsq⟩ := hi.sqrt
  obtain ⟨powP, Kpw, hpow⟩ := hi.pow2
  obtain ⟨dropbP, Kdb, hdropb⟩ := dropBelow hk
  set Kc : ℕ := Kr + (Kp + (Kdup + (Ksw + (Kdr + (Kpu + (Kco + (Kun +
    (Kmul + (Kadd + (Kmax + (Kshl + (Ktd + (Ksq + (Kpw + Kdb)))))))))))))) with hKc
  have hKr : Kr ≤ Kc := by rw [hKc]; omega
  have hKp : Kp ≤ Kc := by rw [hKc]; omega
  have hKdup : Kdup ≤ Kc := by rw [hKc]; omega
  have hKsw : Ksw ≤ Kc := by rw [hKc]; omega
  have hKpu : Kpu ≤ Kc := by rw [hKc]; omega
  have hKco : Kco ≤ Kc := by rw [hKc]; omega
  have hKun : Kun ≤ Kc := by rw [hKc]; omega
  have hKmul : Kmul ≤ Kc := by rw [hKc]; omega
  have hKadd : Kadd ≤ Kc := by rw [hKc]; omega
  have hKmax : Kmax ≤ Kc := by rw [hKc]; omega
  have hKshl : Kshl ≤ Kc := by rw [hKc]; omega
  have hKtd : Ktd ≤ Kc := by rw [hKc]; omega
  have hKsq : Ksq ≤ Kc := by rw [hKc]; omega
  have hKpw : Kpw ≤ Kc := by rw [hKc]; omega
  have hKdb : Kdb ≤ Kc := by rw [hKc]; omega
  have hmain : ∀ (main : Cmd) (p c : ℕ), 1 ≤ c → c ≤ 2 ^ p → WordR main (scaleProg rollP unconsP dupP swP dropP pickP pushP consP mulP addP maxP shlP tdivP sqP powP dropbP)
      (fun vs => ∃ (u : ℤ × ℤ) (rest : List Val),
        vs = .int (p : ℤ) :: .int (c : ℤ) :: cfxVal u :: rest ∧ inDisc p u)
      (fun vs out => ∃ (u : ℤ × ℤ) (rest : List Val) (w : ℤ × ℤ),
        vs = .int (p : ℤ) :: .int (c : ℤ) :: cfxVal u :: rest ∧
        out = cfxVal w :: rest ∧ inDisc p w ∧ ∀ x : ℂ, (c : ℝ) * ‖x‖ ≤ 1 →
          (2 : ℝ) ^ p * ‖fxC p w - (c : ℂ) * x‖ <
            2 * c * ((2 : ℝ) ^ p * ‖fxC p u - x‖) + 3)
      (fun _ => 152000 * Kc * (p + 1) ^ 2) := by

    intro main p c h1c h2c
    set Cstep : ℕ := 4000 * Kc * (p + 1) ^ 2 with hCstep
    let Wof : ℤ → ℤ → ℤ × ℤ := fun x0 y0 =>
      let X : ℤ := (c : ℤ) * x0
      let Y : ℤ := (c : ℤ) * y0
      let a : ℤ := X * X + Y * Y
      let s : ℤ := (Nat.sqrt a.toNat : ℤ)
      let b : ℤ := max ((2 : ℤ) ^ p) (1 + s)
      (Int.tdiv (X * (2 : ℤ) ^ p) b, Int.tdiv (Y * (2 : ℤ) ^ p) b)
    have key : ∀ (x0 y0 : ℤ), inDisc p (x0, y0) →
        Spec main (scaleProg rollP unconsP dupP swP dropP pickP pushP consP mulP addP maxP shlP tdivP sqP powP dropbP) 3 (fun t => t = [.int (p:ℤ), .int (c:ℤ), cfxVal (x0, y0)])
          (fun _ o => o = [cfxVal (Wof x0 y0)] ∧ inDisc p (Wof x0 y0) ∧
            ∀ x : ℂ, (c:ℝ) * ‖x‖ ≤ 1 →
              (2:ℝ)^p * ‖fxC p (Wof x0 y0) - (c:ℂ) * x‖ <
                2 * c * ((2:ℝ)^p * ‖fxC p (x0, y0) - x‖) + 3)
          (fun _ => 152000 * Kc * (p + 1) ^ 2) := by
      intro x0 y0 hd
      let X : ℤ := (c : ℤ) * x0
      let Y : ℤ := (c : ℤ) * y0
      let a : ℤ := X * X + Y * Y
      let s : ℤ := (Nat.sqrt a.toNat : ℤ)
      let Pw : ℤ := (2 : ℤ) ^ p
      let b : ℤ := max Pw (1 + s)
      let powX : ℤ := X * Pw
      let powY : ℤ := Y * Pw
      let X' : ℤ := Int.tdiv powX b
      let Y' : ℤ := Int.tdiv powY b
      let A0 : List Val := [.int (p:ℤ), .int (c:ℤ), cfxVal (x0, y0)]
      let A1 : List Val := [cfxVal (x0, y0), .int (p:ℤ), .int (c:ℤ)]
      let A2 : List Val := [.int x0, .int y0, .int (p:ℤ), .int (c:ℤ)]
      let A3 : List Val := [.int (c:ℤ), .int x0, .int y0, .int (p:ℤ), .int (c:ℤ)]
      let A4 : List Val := [.int X, .int y0, .int (p:ℤ), .int (c:ℤ)]
      let A5 : List Val := [.int (c:ℤ), .int X, .int y0, .int (p:ℤ), .int (c:ℤ)]
      let A6 : List Val := [.int y0, .int (c:ℤ), .int X, .int (p:ℤ), .int (c:ℤ)]
      let A7 : List Val := [.int (c:ℤ), .int y0, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A8 : List Val := [.int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A9 : List Val := [.int Y, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A10 : List Val := [.int Y, .int Y, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A11 : List Val := [.int (Y*Y), .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A12 : List Val := [.int X, .int (Y*Y), .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A13 : List Val := [.int X, .int X, .int (Y*Y), .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A14 : List Val := [.int (X*X), .int (Y*Y), .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A15 : List Val := [.int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A16 : List Val := [.int a, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A17 : List Val := [.int s, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A18 : List Val := [.int 1, .int s, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A19 : List Val := [.int (1 + s), .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A20 : List Val := [.int (p:ℤ), .int (1 + s), .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A21 : List Val := [.int Pw, .int (1 + s), .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A22 : List Val := [.int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A23 : List Val := [.int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A24 : List Val := [.int (p:ℤ), .int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A25 : List Val := [.int X, .int (p:ℤ), .int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A26 : List Val := [.int powX, .int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A27 : List Val := [.int b, .int powX, .int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A28 : List Val := [.int powX, .int b, .int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A29 : List Val := [.int X', .int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A30 : List Val := [.int (p:ℤ), .int X', .int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A31 : List Val := [.int Y, .int (p:ℤ), .int X', .int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A32 : List Val := [.int powY, .int X', .int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A33 : List Val := [.int b, .int powY, .int X', .int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A34 : List Val := [.int powY, .int b, .int X', .int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A35 : List Val := [.int Y', .int X', .int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A36 : List Val := [.int X', .int Y', .int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A37 : List Val := [cfxVal (X', Y'), .int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
      let A38 : List Val := [cfxVal (X', Y')]
      let js : List Val := [.int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]
        -- size bounds
      have hx0le : x0.natAbs ≤ 2^p := (natAbs_le_of_inDisc hd).1
      have hy0le : y0.natAbs ≤ 2^p := (natAbs_le_of_inDisc hd).2
      have hp2 : ∀ j : ℕ, (2:ℕ)^(2*j) = 4^j := by
        intro j
        induction j with
        | zero => norm_num
        | succ j ih =>
          calc (2:ℕ)^(2*(j+1)) = (2:ℕ)^(2*j + 2) := by rw [show 2*(j+1) = 2*j + 2 by ring]
            _ = (2:ℕ)^(2*j) * 2^2 := by rw [pow_add]
            _ = 4^j * 4 := by rw [ih]; norm_num
            _ = 4^(j+1) := by rw [pow_succ]
      have hp4 : ∀ j : ℕ, (2:ℕ)^(4*j) = 4^j * 4^j := by
        intro j
        rw [show (4:ℕ)*j = 2*j + 2*j by ring, pow_add, hp2]
      have hXle : X.natAbs ≤ 4^p := by
        simp only [X, Int.natAbs_mul, Int.natAbs_natCast]
        calc c * x0.natAbs ≤ 2^p * 2^p := Nat.mul_le_mul h2c hx0le
          _ = 4^p := by rw [← pow_add, show p + p = 2*p by ring]; exact hp2 p
      have hYle : Y.natAbs ≤ 4^p := by
        simp only [Y, Int.natAbs_mul, Int.natAbs_natCast]
        calc c * y0.natAbs ≤ 2^p * 2^p := Nat.mul_le_mul h2c hy0le
          _ = 4^p := by rw [← pow_add, show p + p = 2*p by ring]; exact hp2 p
      have hXXle : (X*X).natAbs ≤ 4^p * 4^p := by
        rw [Int.natAbs_mul]; exact Nat.mul_le_mul hXle hXle
      have hYYle : (Y*Y).natAbs ≤ 4^p * 4^p := by
        rw [Int.natAbs_mul]; exact Nat.mul_le_mul hYle hYle
      have ha0 : (0:ℤ) ≤ a := by
        have hae : a = X*X + Y*Y := rfl
        rw [hae]; nlinarith [sq_nonneg X, sq_nonneg Y]
      have hale : a.natAbs ≤ 2 * (4^p * 4^p) := by
        have hae : a = X*X + Y*Y := rfl
        rw [hae]
        calc (X*X + Y*Y).natAbs ≤ (X*X).natAbs + (Y*Y).natAbs := Int.natAbs_add_le _ _
          _ ≤ 4^p * 4^p + 4^p * 4^p := Nat.add_le_add hXXle hYYle
          _ = 2 * (4^p * 4^p) := by ring
      have htoNat : a.toNat ≤ 2 * (4^p * 4^p) := by
        have h1 : a.toNat = a.natAbs := by
          have h2 : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha0
          have h3 : ((a.natAbs : ℕ) : ℤ) = a := Int.natAbs_of_nonneg ha0
          omega
        rw [h1]; exact hale
      have hp9 : isz ((p:ℤ)) ≤ 9 * (p+1) := by
        have hna : ((p:ℤ)).natAbs = p := Int.natAbs_natCast p
        have h1 : isz ((p:ℤ)) = p.size + 2 := by simp only [isz, hna]
        have h2 : p.size ≤ p := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p))
        omega
      have hc9 : isz ((c:ℤ)) ≤ 9 * (p+1) := by
        have hna : ((c:ℤ)).natAbs = c := Int.natAbs_natCast c
        have h : isz ((c:ℤ)) ≤ p + 3 := by
          apply isz_le_of_natAbs_le
          rw [hna]; exact h2c
        omega
      have hx09 : isz x0 ≤ 9 * (p+1) := by
        have h : isz x0 ≤ p + 3 := isz_le_of_natAbs_le hx0le; omega
      have hy09 : isz y0 ≤ 9 * (p+1) := by
        have h : isz y0 ≤ p + 3 := isz_le_of_natAbs_le hy0le; omega
      have hX9 : isz X ≤ 9 * (p+1) := by
        have h : isz X ≤ 2*p + 3 := by
          apply isz_le_of_natAbs_le (k := 2*p)
          rw [hp2 p]; exact hXle
        omega
      have hY9 : isz Y ≤ 9 * (p+1) := by
        have h : isz Y ≤ 2*p + 3 := by
          apply isz_le_of_natAbs_le (k := 2*p)
          rw [hp2 p]; exact hYle
        omega
      have hXX9 : isz (X*X) ≤ 9 * (p+1) := by
        have h : isz (X*X) ≤ 4*p + 3 := by
          apply isz_le_of_natAbs_le (k := 4*p)
          rw [hp4 p]; exact hXXle
        omega
      have hYY9 : isz (Y*Y) ≤ 9 * (p+1) := by
        have h : isz (Y*Y) ≤ 4*p + 3 := by
          apply isz_le_of_natAbs_le (k := 4*p)
          rw [hp4 p]; exact hYYle
        omega
      have ha9 : isz a ≤ 9 * (p+1) := by
        have h : isz a ≤ 4*p + 4 := by
          apply isz_le_of_natAbs_le (k := 4*p+1)
          rw [pow_succ, hp4 p]
          calc a.natAbs ≤ 2 * (4^p * 4^p) := hale
            _ = 4^p * 4^p * 2 := by ring
        omega
      have hs_pow : s.natAbs ≤ 2^(4*p+1) := by
        have h2 : s.natAbs = Nat.sqrt a.toNat := by simp only [s, Int.natAbs_natCast]
        rw [h2]
        calc Nat.sqrt a.toNat ≤ a.toNat := Nat.sqrt_le_self _
          _ ≤ 2 * (4^p * 4^p) := htoNat
          _ = 2^(4*p+1) := by rw [pow_succ, hp4 p]; ring
      have hs9 : isz s ≤ 9 * (p+1) := by
        have h : isz s ≤ 4*p + 4 := by
          apply isz_le_of_natAbs_le (k := 4*p+1)
          exact hs_pow
        omega
      have h19 : isz (1:ℤ) ≤ 9 * (p+1) := by
        have h : isz (1:ℤ) ≤ 3 := by
          have h1 : (1:ℤ).natAbs ≤ 2^0 := by norm_num
          simpa using isz_le_of_natAbs_le (z := (1:ℤ)) (k := 0) h1
        omega
      have hs1_nat : (1 + s).natAbs ≤ 1 + s.natAbs := by
        have h := Int.natAbs_add_le (1:ℤ) s
        simpa using h
      have h1s9 : isz (1 + s) ≤ 9 * (p+1) := by
        have h : isz (1 + s) ≤ 4*p + 5 := by
          apply isz_le_of_natAbs_le (k := 4*p+2)
          rw [pow_succ]
          calc (1 + s).natAbs ≤ 1 + s.natAbs := hs1_nat
            _ ≤ 1 + 2^(4*p+1) := Nat.add_le_add_left hs_pow 1
            _ ≤ 2^(4*p+1) + 2^(4*p+1) := by
                have h2 : (1:ℕ) ≤ 2^(4*p+1) := Nat.one_le_two_pow
                omega
            _ = 2^(4*p+1) * 2 := by ring
        omega
      have hPw_nat : Pw.natAbs ≤ 2^(4*p+2) := by
        have h1 : Pw.natAbs = 2^p := by simp only [Pw, Int.natAbs_pow]; norm_num
        rw [h1]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hPw9 : isz Pw ≤ 9 * (p+1) := by
        have h : isz Pw ≤ p + 3 := by
          apply isz_le_of_natAbs_le
          simp only [Pw, Int.natAbs_pow]; norm_num
        omega
      have hbne : b ≠ 0 := by
        have h1 : (1:ℤ) ≤ b := le_trans (one_le_pow2 p) (le_max_left _ _)
        omega
      have h1s_pow : (1 + s).natAbs ≤ 2^(4*p+2) := by
        rw [pow_succ]
        calc (1 + s).natAbs ≤ 1 + s.natAbs := hs1_nat
          _ ≤ 1 + 2^(4*p+1) := Nat.add_le_add_left hs_pow 1
          _ ≤ 2^(4*p+1) + 2^(4*p+1) := by
              have h2 : (1:ℕ) ≤ 2^(4*p+1) := Nat.one_le_two_pow
              omega
          _ = 2^(4*p+1) * 2 := by ring
      have hb_nat : b.natAbs ≤ 2^(4*p+2) := by
        have hbm : b = max Pw (1 + s) := rfl
        rw [hbm]
        rcases le_total Pw (1 + s) with hle | hle
        · rw [max_eq_right hle]; exact h1s_pow
        · rw [max_eq_left hle]; exact hPw_nat
      have hb9 : isz b ≤ 9 * (p+1) := by
        have h : isz b ≤ 4*p + 5 := by
          apply isz_le_of_natAbs_le (k := 4*p+2)
          exact hb_nat
        omega
      have hpowX_nat : powX.natAbs ≤ 2^(3*p) := by
        have h1 : powX.natAbs = X.natAbs * Pw.natAbs := by simp only [powX, Int.natAbs_mul]
        have h2 : Pw.natAbs = 2^p := by simp only [Pw, Int.natAbs_pow]; norm_num
        rw [h1, h2]
        calc X.natAbs * 2^p ≤ 4^p * 2^p := Nat.mul_le_mul_right _ hXle
          _ = 2^(2*p) * 2^p := by rw [hp2 p]
          _ = 2^(2*p + p) := by rw [pow_add]
          _ = 2^(3*p) := by congr 1; ring
      have hpowY_nat : powY.natAbs ≤ 2^(3*p) := by
        have h1 : powY.natAbs = Y.natAbs * Pw.natAbs := by simp only [powY, Int.natAbs_mul]
        have h2 : Pw.natAbs = 2^p := by simp only [Pw, Int.natAbs_pow]; norm_num
        rw [h1, h2]
        calc Y.natAbs * 2^p ≤ 4^p * 2^p := Nat.mul_le_mul_right _ hYle
          _ = 2^(2*p) * 2^p := by rw [hp2 p]
          _ = 2^(2*p + p) := by rw [pow_add]
          _ = 2^(3*p) := by congr 1; ring
      have hpowX9 : isz powX ≤ 9 * (p+1) := by
        have h : isz powX ≤ 3*p + 3 := by
          apply isz_le_of_natAbs_le (k := 3*p)
          exact hpowX_nat
        omega
      have hpowY9 : isz powY ≤ 9 * (p+1) := by
        have h : isz powY ≤ 3*p + 3 := by
          apply isz_le_of_natAbs_le (k := 3*p)
          exact hpowY_nat
        omega
      have hX'9 : isz X' ≤ 9 * (p+1) := by
        have h : isz X' ≤ isz powX := by
          have h2 : X' = Int.tdiv powX b := rfl
          rw [h2]; exact isz_tdiv_le powX b
        omega
      have hY'9 : isz Y' ≤ 9 * (p+1) := by
        have h : isz Y' ≤ isz powY := by
          have h2 : Y' = Int.tdiv powY b := rfl
          rw [h2]; exact isz_tdiv_le powY b
        omega

      let Pk6 : List Val := [.int (c:ℤ), .int X, .int y0]

      let Pk9 : List Val := [.int Y]

      let Pk10 : List Val := [.int Y]

      let Pk12 : List Val := [.int (Y*Y), .int Y, .int X]

      let Pk13 : List Val := [.int X]

      let Pk20 : List Val := [.int (1 + s), .int a, .int Y, .int X, .int (p:ℤ)]

      let Pk23 : List Val := [.int b, .int a, .int Y, .int X]

      let Pk24 : List Val := [.int X, .int b, .int a, .int Y, .int X, .int (p:ℤ)]

      let Pk25 : List Val := [.int (p:ℤ), .int X]

      let Pk27 : List Val := [.int powX, .int X, .int b]

      let Pk28 : List Val := [.int b, .int powX]

      let Pk30 : List Val := [.int X', .int X, .int b, .int a, .int Y, .int X, .int (p:ℤ)]

      let Pk31 : List Val := [.int (p:ℤ), .int X', .int X, .int b, .int a, .int Y]

      let Pk33 : List Val := [.int powY, .int X', .int X, .int b]

      let Pk34 : List Val := [.int b, .int powY]

      let Pk36 : List Val := [.int Y', .int X']


      -- bounds on `szl` of the windows used by `pick`/`roll`

      have hsz1 : szl A0 ≤ 130 * (p + 1) := by
        simp only [A0, cfxVal, szl, vsz_int, vsz_cons, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        omega

      have hsz3 : szl A2 ≤ 130 * (p + 1) := by
        simp only [A2, cfxVal, szl, vsz_int, vsz_cons, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        omega

      have hsz5 : szl A4 ≤ 130 * (p + 1) := by
        simp only [A4, cfxVal, szl, vsz_int, vsz_cons, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        omega

      have hsz6 : szl Pk6 ≤ 130 * (p + 1) := by
        simp only [Pk6, cfxVal, szl, vsz_int, vsz_cons, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        omega

      have hsz9 : szl Pk9 ≤ 130 * (p + 1) := by
        simp only [Pk9, cfxVal, szl, vsz_int, vsz_cons, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        omega

      have hsz10 : szl Pk10 ≤ 130 * (p + 1) := by
        simp only [Pk10, cfxVal, szl, vsz_int, vsz_cons, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        omega

      have hsz12 : szl Pk12 ≤ 130 * (p + 1) := by
        simp only [Pk12, cfxVal, szl, vsz_int, vsz_cons, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        omega

      have hsz13 : szl Pk13 ≤ 130 * (p + 1) := by
        simp only [Pk13, cfxVal, szl, vsz_int, vsz_cons, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        omega

      have hsz20 : szl Pk20 ≤ 130 * (p + 1) := by
        simp only [Pk20, cfxVal, szl, vsz_int, vsz_cons, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        omega

      have hsz23 : szl Pk23 ≤ 130 * (p + 1) := by
        simp only [Pk23, cfxVal, szl, vsz_int, vsz_cons, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        omega

      have hsz24 : szl Pk24 ≤ 130 * (p + 1) := by
        simp only [Pk24, cfxVal, szl, vsz_int, vsz_cons, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        omega

      have hsz25 : szl Pk25 ≤ 130 * (p + 1) := by
        simp only [Pk25, cfxVal, szl, vsz_int, vsz_cons, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        omega

      have hsz27 : szl Pk27 ≤ 130 * (p + 1) := by
        simp only [Pk27, cfxVal, szl, vsz_int, vsz_cons, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        omega

      have hsz28 : szl Pk28 ≤ 130 * (p + 1) := by
        simp only [Pk28, cfxVal, szl, vsz_int, vsz_cons, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        omega

      have hsz30 : szl Pk30 ≤ 130 * (p + 1) := by
        simp only [Pk30, cfxVal, szl, vsz_int, vsz_cons, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        omega

      have hsz31 : szl Pk31 ≤ 130 * (p + 1) := by
        simp only [Pk31, cfxVal, szl, vsz_int, vsz_cons, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        omega

      have hsz33 : szl Pk33 ≤ 130 * (p + 1) := by
        simp only [Pk33, cfxVal, szl, vsz_int, vsz_cons, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        omega

      have hsz34 : szl Pk34 ≤ 130 * (p + 1) := by
        simp only [Pk34, cfxVal, szl, vsz_int, vsz_cons, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        omega

      have hsz36 : szl Pk36 ≤ 130 * (p + 1) := by
        simp only [Pk36, cfxVal, szl, vsz_int, vsz_cons, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        omega

      have hsz37 : szl A37 ≤ 130 * (p + 1) := by
        simp only [A37, cfxVal, szl, vsz_int, vsz_cons, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        omega


      -- the 38 steps

      have h1 : Spec main (rollP 2) 3 (fun t => t = A0) (fun _ o => o = A1) (fun _ => Cstep) := by

        have h := Spec.rollStep hk (hroll main 2) (A := A0) (E := []) (Bc := Cstep)
          (by simp [A0]) (by rw [hCstep]; exact pickroll_cost_x1 hKr (by norm_num) hsz1)
        simpa only [A0, A1, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h2 : Spec main unconsP 3 (fun t => t = A1) (fun _ o => o = A2) (fun _ => Cstep) := by

        have h := Spec.unconsStep hk (huncons main) (a := .int x0) (b := .int y0)
          (E := [.int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep) (by rw [hCstep]; exact uncon_cost_x1 hKun)
        simpa only [A1, A2, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h3 : Spec main (pickP 3) 4 (fun t => t = A2) (fun _ o => o = A3) (fun _ => Cstep) := by

        have h := Spec.pickStep hk (hpick main 3) (A := A2) (E := []) (Bc := Cstep)
          (by simp [A2]) (by rw [hCstep]; exact pickroll_cost_x1 hKp (by norm_num) hsz3)
        simpa only [A2, A3, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h4 : Spec main mulP 5 (fun t => t = A3) (fun _ o => o = A4) (fun _ => Cstep) := by

        have h := Spec.binStep hk (hmul main) (a := (c:ℤ)) (b := x0) (hab := trivial)
          (E := [.int y0, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep) (by rw [hCstep]; exact mul2_cost hKmul hc9 hx09)
        simpa only [A3, A4, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h5 : Spec main (pickP 3) 4 (fun t => t = A4) (fun _ o => o = A5) (fun _ => Cstep) := by

        have h := Spec.pickStep hk (hpick main 3) (A := A4) (E := []) (Bc := Cstep)
          (by simp [A4]) (by rw [hCstep]; exact pickroll_cost_x1 hKp (by norm_num) hsz5)
        simpa only [A4, A5, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h6 : Spec main (rollP 2) 5 (fun t => t = A5) (fun _ o => o = A6) (fun _ => Cstep) := by

        have h := Spec.rollStep hk (hroll main 2) (A := Pk6) (E := [.int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep)
          (by simp [Pk6]) (by rw [hCstep]; exact pickroll_cost_x1 hKr (by norm_num) hsz6)
        simpa only [Pk6, A5, A6, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h7 : Spec main swP 5 (fun t => t = A6) (fun _ o => o = A7) (fun _ => Cstep) := by

        have h := Spec.swapStep hk (hsw main) (a := .int y0) (b := .int (c:ℤ))
          (E := [.int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep)
          (by rw [hCstep]; exact swap_cost hKsw (by rw [vsz_int]; exact hy09) (by rw [vsz_int]; exact hc9))
        simpa only [A6, A7, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h8 : Spec main mulP 5 (fun t => t = A7) (fun _ o => o = A8) (fun _ => Cstep) := by

        have h := Spec.binStep hk (hmul main) (a := (c:ℤ)) (b := y0) (hab := trivial)
          (E := [.int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep) (by rw [hCstep]; exact mul2_cost hKmul hc9 hy09)
        simpa only [A7, A8, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h9 : Spec main (pickP 0) 4 (fun t => t = A8) (fun _ o => o = A9) (fun _ => Cstep) := by

        have h := Spec.pickStep hk (hpick main 0) (A := Pk9) (E := [.int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep)
          (by simp [Pk9]) (by rw [hCstep]; exact pickroll_cost_x1 hKp (by norm_num) hsz9)
        simpa only [Pk9, A8, A9, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h10 : Spec main (pickP 0) 5 (fun t => t = A9) (fun _ o => o = A10) (fun _ => Cstep) := by

        have h := Spec.pickStep hk (hpick main 0) (A := Pk10) (E := [.int Y, .int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep)
          (by simp [Pk10]) (by rw [hCstep]; exact pickroll_cost_x1 hKp (by norm_num) hsz10)
        simpa only [Pk10, A9, A10, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h11 : Spec main mulP 6 (fun t => t = A10) (fun _ o => o = A11) (fun _ => Cstep) := by

        have h := Spec.binStep hk (hmul main) (a := Y) (b := Y) (hab := trivial)
          (E := [.int Y, .int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep) (by rw [hCstep]; exact mul2_cost hKmul hY9 hY9)
        simpa only [A10, A11, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h12 : Spec main (pickP 2) 5 (fun t => t = A11) (fun _ o => o = A12) (fun _ => Cstep) := by

        have h := Spec.pickStep hk (hpick main 2) (A := Pk12) (E := [.int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep)
          (by simp [Pk12]) (by rw [hCstep]; exact pickroll_cost_x1 hKp (by norm_num) hsz12)
        simpa only [Pk12, A11, A12, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h13 : Spec main (pickP 0) 6 (fun t => t = A12) (fun _ o => o = A13) (fun _ => Cstep) := by

        have h := Spec.pickStep hk (hpick main 0) (A := Pk13) (E := [.int (Y*Y), .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep)
          (by simp [Pk13]) (by rw [hCstep]; exact pickroll_cost_x1 hKp (by norm_num) hsz13)
        simpa only [Pk13, A12, A13, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h14 : Spec main mulP 7 (fun t => t = A13) (fun _ o => o = A14) (fun _ => Cstep) := by

        have h := Spec.binStep hk (hmul main) (a := X) (b := X) (hab := trivial)
          (E := [.int (Y*Y), .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep) (by rw [hCstep]; exact mul2_cost hKmul hX9 hX9)
        simpa only [A13, A14, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h15 : Spec main addP 6 (fun t => t = A14) (fun _ o => o = A15) (fun _ => Cstep) := by

        have h := Spec.binStep hk (hadd main) (a := X*X) (b := Y*Y) (hab := trivial)
          (E := [.int Y, .int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep) (by rw [hCstep]; exact addsub_cost_x1 hKadd hXX9 hYY9)
        simpa only [A14, A15, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h16 : Spec main dupP 5 (fun t => t = A15) (fun _ o => o = A16) (fun _ => Cstep) := by

        have h := Spec.dupStep hk (hdup main) (a := .int a) (E := [.int Y, .int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep)
          (by rw [hCstep]; exact val_cost hKdup (by rw [vsz_int]; exact ha9))
        simpa only [A15, A16, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h17 : Spec main sqP 6 (fun t => t = A16) (fun _ o => o = A17) (fun _ => Cstep) := by

        have h := Spec.unStep hk (hsq main) (a := a) (ha := ha0)
          (E := [.int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep) (by rw [hCstep]; exact sq_cost hKsq ha9)
        simpa only [A16, A17, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h18 : Spec main (pushP (.int 1)) 6 (fun t => t = A17) (fun _ o => o = A18) (fun _ => Cstep) := by

        have h := Spec.pushStep hk (hpush main (.int 1)) (v := .int 1) (E := A17) (Bc := Cstep)
          (by rw [hCstep]; exact val_cost hKpu (by rw [vsz_int]; exact h19))
        simpa only [A17, A18, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h19 : Spec main addP 7 (fun t => t = A18) (fun _ o => o = A19) (fun _ => Cstep) := by

        have h := Spec.binStep hk (hadd main) (a := 1) (b := s) (hab := trivial)
          (E := [.int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep) (by rw [hCstep]; exact addsub_cost_x1 hKadd h19 hs9)
        simpa only [A18, A19, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h20 : Spec main (pickP 4) 6 (fun t => t = A19) (fun _ o => o = A20) (fun _ => Cstep) := by

        have h := Spec.pickStep hk (hpick main 4) (A := Pk20) (E := [.int (c:ℤ)]) (Bc := Cstep)
          (by simp [Pk20]) (by rw [hCstep]; exact pickroll_cost_x1 hKp (by norm_num) hsz20)
        simpa only [Pk20, A19, A20, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h21 : Spec main powP 7 (fun t => t = A20) (fun _ o => o = A21) (fun _ => Cstep) := by

        have h := Spec.unStep hk (hpow main) (a := (p:ℤ)) (ha := by exact_mod_cast Nat.zero_le p)
          (E := [.int (1 + s), .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep) (by rw [hCstep]; exact pow2c_cost hKpw)
        simpa [A20, A21, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h22 : Spec main maxP 7 (fun t => t = A21) (fun _ o => o = A22) (fun _ => Cstep) := by

        have h := Spec.binStep hk (hmax main) (a := Pw) (b := 1 + s) (hab := trivial)
          (E := [.int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep) (by rw [hCstep]; exact addsub_cost_x1 hKmax hPw9 h1s9)
        simpa only [A21, A22, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h23 : Spec main (pickP 3) 6 (fun t => t = A22) (fun _ o => o = A23) (fun _ => Cstep) := by

        have h := Spec.pickStep hk (hpick main 3) (A := Pk23) (E := [.int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep)
          (by simp [Pk23]) (by rw [hCstep]; exact pickroll_cost_x1 hKp (by norm_num) hsz23)
        simpa only [Pk23, A22, A23, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h24 : Spec main (pickP 5) 7 (fun t => t = A23) (fun _ o => o = A24) (fun _ => Cstep) := by

        have h := Spec.pickStep hk (hpick main 5) (A := Pk24) (E := [.int (c:ℤ)]) (Bc := Cstep)
          (by simp [Pk24]) (by rw [hCstep]; exact pickroll_cost_x1 hKp (by norm_num) hsz24)
        simpa only [Pk24, A23, A24, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h25 : Spec main (pickP 1) 8 (fun t => t = A24) (fun _ o => o = A25) (fun _ => Cstep) := by

        have h := Spec.pickStep hk (hpick main 1) (A := Pk25) (E := [.int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep)
          (by simp [Pk25]) (by rw [hCstep]; exact pickroll_cost_x1 hKp (by norm_num) hsz25)
        simpa only [Pk25, A24, A25, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h26 : Spec main shlP 9 (fun t => t = A25) (fun _ o => o = A26) (fun _ => Cstep) := by

        have h := Spec.binStep hk (hshl main) (a := X) (b := (p:ℤ)) (hab := by exact_mod_cast Nat.zero_le p)
          (E := [.int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep) (by rw [hCstep]; exact shl_cost hKshl hX9)
        simpa [A25, A26, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h27 : Spec main (pickP 2) 8 (fun t => t = A26) (fun _ o => o = A27) (fun _ => Cstep) := by

        have h := Spec.pickStep hk (hpick main 2) (A := Pk27) (E := [.int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep)
          (by simp [Pk27]) (by rw [hCstep]; exact pickroll_cost_x1 hKp (by norm_num) hsz27)
        simpa only [Pk27, A26, A27, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h28 : Spec main (rollP 1) 9 (fun t => t = A27) (fun _ o => o = A28) (fun _ => Cstep) := by

        have h := Spec.rollStep hk (hroll main 1) (A := Pk28) (E := [.int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep)
          (by simp [Pk28]) (by rw [hCstep]; exact pickroll_cost_x1 hKr (by norm_num) hsz28)
        simpa only [Pk28, A27, A28, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h29 : Spec main tdivP 9 (fun t => t = A28) (fun _ o => o = A29) (fun _ => Cstep) := by

        have h := Spec.binStep hk (htd main) (a := powX) (b := b) (hab := hbne)
          (E := [.int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep) (by rw [hCstep]; exact mul2_cost hKtd hpowX9 hb9)
        simpa only [A28, A29, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h30 : Spec main (pickP 6) 8 (fun t => t = A29) (fun _ o => o = A30) (fun _ => Cstep) := by

        have h := Spec.pickStep hk (hpick main 6) (A := Pk30) (E := [.int (c:ℤ)]) (Bc := Cstep)
          (by simp [Pk30]) (by rw [hCstep]; exact pickroll_cost_x1 hKp (by norm_num) hsz30)
        simpa only [Pk30, A29, A30, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h31 : Spec main (pickP 5) 9 (fun t => t = A30) (fun _ o => o = A31) (fun _ => Cstep) := by

        have h := Spec.pickStep hk (hpick main 5) (A := Pk31) (E := [.int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep)
          (by simp [Pk31]) (by rw [hCstep]; exact pickroll_cost_x1 hKp (by norm_num) hsz31)
        simpa only [Pk31, A30, A31, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h32 : Spec main shlP 10 (fun t => t = A31) (fun _ o => o = A32) (fun _ => Cstep) := by

        have h := Spec.binStep hk (hshl main) (a := Y) (b := (p:ℤ)) (hab := by exact_mod_cast Nat.zero_le p)
          (E := [.int X', .int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep) (by rw [hCstep]; exact shl_cost hKshl hY9)
        simpa [A31, A32, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h33 : Spec main (pickP 3) 9 (fun t => t = A32) (fun _ o => o = A33) (fun _ => Cstep) := by

        have h := Spec.pickStep hk (hpick main 3) (A := Pk33) (E := [.int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep)
          (by simp [Pk33]) (by rw [hCstep]; exact pickroll_cost_x1 hKp (by norm_num) hsz33)
        simpa only [Pk33, A32, A33, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h34 : Spec main (rollP 1) 10 (fun t => t = A33) (fun _ o => o = A34) (fun _ => Cstep) := by

        have h := Spec.rollStep hk (hroll main 1) (A := Pk34) (E := [.int X', .int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep)
          (by simp [Pk34]) (by rw [hCstep]; exact pickroll_cost_x1 hKr (by norm_num) hsz34)
        simpa only [Pk34, A33, A34, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h35 : Spec main tdivP 10 (fun t => t = A34) (fun _ o => o = A35) (fun _ => Cstep) := by

        have h := Spec.binStep hk (htd main) (a := powY) (b := b) (hab := hbne)
          (E := [.int X', .int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep) (by rw [hCstep]; exact mul2_cost hKtd hpowY9 hb9)
        simpa only [A34, A35, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h36 : Spec main (rollP 1) 9 (fun t => t = A35) (fun _ o => o = A36) (fun _ => Cstep) := by

        have h := Spec.rollStep hk (hroll main 1) (A := Pk36) (E := [.int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep)
          (by simp [Pk36]) (by rw [hCstep]; exact pickroll_cost_x1 hKr (by norm_num) hsz36)
        simpa only [Pk36, A35, A36, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h37 : Spec main consP 9 (fun t => t = A36) (fun _ o => o = A37) (fun _ => Cstep) := by

        have h := Spec.consStep hk (hcons main) (a := .int X') (b := .int Y')
          (E := [.int X, .int b, .int a, .int Y, .int X, .int (p:ℤ), .int (c:ℤ)]) (Bc := Cstep) (by rw [hCstep]; exact uncon_cost_x1 hKco)
        simpa only [A36, A37, cfxVal, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h

      have h38 : Spec main (dropbP 7) 8 (fun t => t = A37) (fun _ o => o = A38) (fun _ => Cstep) := by

        have h := hdropb main (cfxVal (X', Y')) js
        refine Spec.mono hk h (fun t _ ht => ?_) (fun t o _ _ hQ => hQ) (fun t _ ht => ?_)
        · rw [ht]
        · rw [ht]
          have hjs : js.length = 7 := by simp [js]
          rw [hjs, hCstep]
          exact cleanse_cost (K := Kdb) (KK := Kc) (p := p) (m := 7) (s := szl A37) hKdb (by omega) hsz37


      -- compose the steps (right-nested: `S i` is the program of steps `i..38`)

      have S37 := Spec.seq_det_quad hk h37 h38 (by rfl)

      have S36 := Spec.seq_det_quad hk h36 S37 (by rfl)

      have S35 := Spec.seq_det_quad hk h35 S36 (by rfl)

      have S34 := Spec.seq_det_quad hk h34 S35 (by rfl)

      have S33 := Spec.seq_det_quad hk h33 S34 (by rfl)

      have S32 := Spec.seq_det_quad hk h32 S33 (by rfl)

      have S31 := Spec.seq_det_quad hk h31 S32 (by rfl)

      have S30 := Spec.seq_det_quad hk h30 S31 (by rfl)

      have S29 := Spec.seq_det_quad hk h29 S30 (by rfl)

      have S28 := Spec.seq_det_quad hk h28 S29 (by rfl)

      have S27 := Spec.seq_det_quad hk h27 S28 (by rfl)

      have S26 := Spec.seq_det_quad hk h26 S27 (by rfl)

      have S25 := Spec.seq_det_quad hk h25 S26 (by rfl)

      have S24 := Spec.seq_det_quad hk h24 S25 (by rfl)

      have S23 := Spec.seq_det_quad hk h23 S24 (by rfl)

      have S22 := Spec.seq_det_quad hk h22 S23 (by rfl)

      have S21 := Spec.seq_det_quad hk h21 S22 (by rfl)

      have S20 := Spec.seq_det_quad hk h20 S21 (by rfl)

      have S19 := Spec.seq_det_quad hk h19 S20 (by rfl)

      have S18 := Spec.seq_det_quad hk h18 S19 (by rfl)

      have S17 := Spec.seq_det_quad hk h17 S18 (by rfl)

      have S16 := Spec.seq_det_quad hk h16 S17 (by rfl)

      have S15 := Spec.seq_det_quad hk h15 S16 (by rfl)

      have S14 := Spec.seq_det_quad hk h14 S15 (by rfl)

      have S13 := Spec.seq_det_quad hk h13 S14 (by rfl)

      have S12 := Spec.seq_det_quad hk h12 S13 (by rfl)

      have S11 := Spec.seq_det_quad hk h11 S12 (by rfl)

      have S10 := Spec.seq_det_quad hk h10 S11 (by rfl)

      have S9 := Spec.seq_det_quad hk h9 S10 (by rfl)

      have S8 := Spec.seq_det_quad hk h8 S9 (by rfl)

      have S7 := Spec.seq_det_quad hk h7 S8 (by rfl)

      have S6 := Spec.seq_det_quad hk h6 S7 (by rfl)

      have S5 := Spec.seq_det_quad hk h5 S6 (by rfl)

      have S4 := Spec.seq_det_quad hk h4 S5 (by rfl)

      have S3 := Spec.seq_det_quad hk h3 S4 (by rfl)

      have S2 := Spec.seq_det_quad hk h2 S3 (by rfl)

      have S1 := Spec.seq_det_quad hk h1 S2 (by rfl)

      -- the rounded pair is the one used by the mathematical estimate
      have hb1 : Pw ≤ b := le_max_left _ _
      have hb0 : (0:ℤ) ≤ b := le_trans (by positivity : (0:ℤ) ≤ Pw) hb1
      have hbto : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg hb0
      have hbR : ((b.toNat : ℕ) : ℝ) = (b : ℝ) := by exact_mod_cast hbto
      have hW : Wof x0 y0 = (X', Y') := rfl
      have hX'e : X' = Int.tdiv ((2:ℤ)^p * ((c:ℤ)*x0)) b.toNat := by
        simp only [X', powX, X, Pw, hbto, mul_comm]
      have hY'e : Y' = Int.tdiv ((2:ℤ)^p * ((c:ℤ)*y0)) b.toNat := by
        simp only [Y', powY, Y, Pw, hbto, mul_comm]
      have hWe : Wof x0 y0 = (Int.tdiv ((2:ℤ)^p * ((c:ℤ)*x0)) b.toNat,
          Int.tdiv ((2:ℤ)^p * ((c:ℤ)*y0)) b.toNat) := by rw [hW, hX'e, hY'e]
      have hWb : (X', Y') = Wof x0 y0 := by rw [hWe, hX'e, hY'e]
      have hbb : b = max ((2:ℤ)^p) ((Nat.sqrt (X*X + Y*Y).toNat : ℤ) + 1) := by
        simp only [b, Pw, s, a, add_comm]
      have hb2 : ((b : ℝ)) ^ 2 > (((c : ℤ) * x0 : ℤ) : ℝ) ^ 2 + (((c : ℤ) * y0 : ℤ) : ℝ) ^ 2 := by
        have h := (sqrtMaxFacts p X Y).2
        rw [hbb]
        have hXr : (X : ℝ) = (((c : ℤ) * x0 : ℤ) : ℝ) := by simp only [X]
        have hYr : (Y : ℝ) = (((c : ℤ) * y0 : ℤ) : ℝ) := by simp only [Y]
        rw [← hXr, ← hYr]
        exact h
      have hsle : (s : ℝ) ≤ Real.sqrt ((X:ℝ)^2 + (Y:ℝ)^2) := by
        have haeq : ((a:ℤ):ℝ) = (X:ℝ)^2 + (Y:ℝ)^2 := by simp only [a]; push_cast; ring
        have hs2 : (s:ℝ)^2 ≤ ((a:ℤ):ℝ) := by
          have h1 : (Nat.sqrt a.toNat : ℕ) ^ 2 ≤ a.toNat := Nat.sqrt_le' _
          have h2 : ((Nat.sqrt a.toNat : ℕ) : ℝ) ^ 2 ≤ (a.toNat : ℝ) := by exact_mod_cast h1
          have h3 : ((a.toNat : ℕ) : ℝ) = ((a:ℤ):ℝ) := by
            exact_mod_cast (Int.toNat_of_nonneg ha0)
          rw [h3] at h2
          simp only [s]
          exact_mod_cast h2
        rw [← haeq]
        exact (Real.le_sqrt (by positivity) (by positivity)).mpr hs2
      have hb3 : (b : ℝ) ≤ max ((2:ℝ)^p) (Real.sqrt ((X:ℝ)^2 + (Y:ℝ)^2) + 1) := by
        rw [show b = max Pw (1 + s) from rfl, show Pw = (2:ℤ)^p from rfl]
        push_cast
        apply max_le
        · exact le_max_left _ _
        · exact le_trans (by linarith) (le_max_right _ _)
      have hmath : ∀ x : ℂ, (c:ℝ) * ‖x‖ ≤ 1 →
          inDisc p (Int.tdiv ((2:ℤ)^p * ((c:ℤ)*x0)) b.toNat,
            Int.tdiv ((2:ℤ)^p * ((c:ℤ)*y0)) b.toNat) ∧
          (2:ℝ)^p * ‖fxC p (Int.tdiv ((2:ℤ)^p * ((c:ℤ)*x0)) b.toNat,
              Int.tdiv ((2:ℤ)^p * ((c:ℤ)*y0)) b.toNat) - (c:ℂ) * x‖ <
            2 * c * ((2:ℝ)^p * ‖fxC p (x0, y0) - x‖) + 3 := by
        intro x hx
        exact scaleMathB h1c hx
          (by
            have h : (2:ℤ)^p ≤ (b.toNat : ℤ) := by rw [hbto]; exact hb1
            exact_mod_cast h)
          (by rw [hbR]; exact hb2) (by rw [hbR]; exact hb3)
      have hdisc : inDisc p (Wof x0 y0) := by
        rw [hWe]
        exact (hmath 0 (by simp)).1
      have herr : ∀ x : ℂ, (c:ℝ) * ‖x‖ ≤ 1 →
          (2:ℝ)^p * ‖fxC p (Wof x0 y0) - (c:ℂ) * x‖ <
            2 * c * ((2:ℝ)^p * ‖fxC p (x0, y0) - x‖) + 3 := by
        intro x hx
        have h2 := (hmath x hx).2
        simpa only [hWe, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, X, Y, a, s, Pw, b, powX, powY, X', Y'] using h2
      have hfin : Spec main (scaleProg rollP unconsP dupP swP dropP pickP pushP consP mulP addP maxP shlP tdivP sqP powP dropbP) 3 (fun t => t = A0)
          (fun _ o => o = [cfxVal (Wof x0 y0)] ∧ inDisc p (Wof x0 y0) ∧
            ∀ x : ℂ, (c:ℝ) * ‖x‖ ≤ 1 →
              (2:ℝ)^p * ‖fxC p (Wof x0 y0) - (c:ℂ) * x‖ <
                2 * c * ((2:ℝ)^p * ‖fxC p (x0, y0) - x‖) + 3)
          (fun _ => 152000 * Kc * (p + 1) ^ 2) := by
        have hP' : ∀ t, t.length = 3 → t = A0 → t = A0 := fun t _ h => h
        have hQ' : ∀ t o, t.length = 3 → t = A0 → o = A38 →
            o = [cfxVal (Wof x0 y0)] ∧ inDisc p (Wof x0 y0) ∧
              ∀ x : ℂ, (c:ℝ) * ‖x‖ ≤ 1 →
                (2:ℝ)^p * ‖fxC p (Wof x0 y0) - (c:ℂ) * x‖ <
                  2 * c * ((2:ℝ)^p * ‖fxC p (x0, y0) - x‖) + 3 := by
          intro t o _ ht hQ
          exact ⟨by rw [hQ], hdisc, herr⟩
        have hC' : ∀ t, t.length = 3 → t = A0 → costN Cstep 38 ≤ 152000 * Kc * (p + 1) ^ 2 := by
          intro t _ _
          change costN Cstep 38 ≤ 152000 * Kc * (p + 1) ^ 2
          rw [costN_eq, hCstep]
          exact Nat.le_of_eq (by ring)
        exact Spec.mono hk S1 hP' hQ' hC'
      exact hfin
    -- assemble the `WordR` statement from the `Spec` for the whole program
    intro vs hpre s R hs
    rcases hpre with ⟨⟨x0, y0⟩, rest, hvs, hd⟩
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ :=
      (Spec.use (key x0 y0 hd) (top := [.int (p:ℤ), .int (c:ℤ), cfxVal (x0, y0)])
        (rest := rest) (by simp) rfl) vs hvs s R (by simpa only [hvs, List.length_nil, List.length_cons, List.append_nil, List.nil_append, List.cons_append, Nat.reduceAdd, Nat.add_zero, Nat.zero_add] using hs)
    rcases hpost with ⟨o, hout, hO, hdisc, herr⟩
    exact ⟨out, s', n, ⟨(x0, y0), rest, Wof x0 y0, hvs, by rw [hout, hO]; rfl, hdisc, herr⟩,
      hev, hn, hstk, hfr⟩
  exact ⟨scaleProg rollP unconsP dupP swP dropP pickP pushP consP mulP addP maxP shlP tdivP sqP powP dropbP, 152000 * Kc, hmain⟩
