import Mathlib
import Submission.Work.Resample.interfacesShim
import Submission.Work.Resample.auKit
import Submission.Work.Fx.FxCommon
import Submission.Work.Resample.buQWsignWord
import Submission.Work.Resample.buQWmagWord

namespace Work.Resample
open HvdH

/-- `+1` when `a` and `b` have the same negativity status, `-1` otherwise. -/
def buQWsgn (a b : ℤ) : ℤ :=
  2 * (if (if a < 0 then (1 : ℤ) else 0) = (if b < 0 then (1 : ℤ) else 0) then 1 else 0) - 1

theorem buQWsgn_eq (a b : ℤ) : buQWsgn a b = 1 ∨ buQWsgn a b = -1 := by
  unfold buQWsgn
  by_cases h : (if a < 0 then (1 : ℤ) else 0) = (if b < 0 then (1 : ℤ) else 0)
  · left; rw [if_pos h]; norm_num
  · right; rw [if_neg h]; norm_num

theorem isz_buQWsgn_le (a b : ℤ) : isz (buQWsgn a b) ≤ 3 := by
  rcases buQWsgn_eq a b with h | h <;> rw [h] <;> decide

theorem size_mul_le (m n : ℕ) : (m * n).size ≤ m.size + n.size := by
  rw [Nat.size_le]
  have hm : m < 2 ^ m.size := Nat.size_le.mp le_rfl
  have hn : n < 2 ^ n.size := Nat.size_le.mp le_rfl
  have h2 : (2:ℕ) ^ m.size * 2 ^ n.size = 2 ^ (m.size + n.size) := by rw [Nat.pow_add]
  have h3 : m * n < (2:ℕ) ^ m.size * 2 ^ n.size := Nat.mul_lt_mul'' hm hn
  rwa [h2] at h3

theorem mul_buQWsgn (a b : ℤ) : ((a.natAbs * b.natAbs : ℕ) : ℤ) * buQWsgn a b = a * b := by
  unfold buQWsgn
  rw [Nat.cast_mul]
  by_cases ha : a < 0 <;> by_cases hb : b < 0 <;>
    simp only [ha, hb, if_true, if_false] <;>
    (try rw [Int.ofNat_natAbs_of_nonpos (show a ≤ 0 by omega)]) <;>
    (try rw [Int.natAbs_of_nonneg (show (0:ℤ) ≤ a by omega)]) <;>
    (try rw [Int.ofNat_natAbs_of_nonpos (show b ≤ 0 by omega)]) <;>
    (try rw [Int.natAbs_of_nonneg (show (0:ℤ) ≤ b by omega)]) <;>
    norm_num <;> ring

theorem mulSize_int_natAbs (a b : ℤ) (r : List Val) :
    mulSize (Val.int (a.natAbs : ℤ) :: Val.int (b.natAbs : ℤ) :: r) =
      max a.natAbs.size b.natAbs.size := by
  simp only [mulSize, Int.natAbs_natCast]

theorem pipe_int2 {main prog : Cmd} {a b f : ℤ} {c : ℕ}
    (h : WordR main prog (fun vs => ∃ rest, vs = .int a :: .int b :: rest)
      (fun vs out => ∃ rest, vs = .int a :: .int b :: rest ∧ out = .int f :: rest)
      (fun _ => c)) : Pipe main prog [.int a, .int b] [.int f] c := by
  intro rest vs hvs s R hR
  have hv2 : vs = .int a :: .int b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨r', hvs', hout⟩, hev, hn, hstk, hoth⟩ := h vs ⟨rest, hv2⟩ s R hR
  obtain ⟨h1, h2, h3⟩ := Work.Fx.int_cons_inj3 (hvs'.symm.trans hv2)
  refine ⟨out, s', n, ?_, hev, hn, hstk, hoth⟩
  show out = .int f :: rest
  rw [hout, h3]

theorem buQWmulWord (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (q : HvdH.Cmd) (Kc : ℕ),
    ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ) (P : ℕ) (a b : ℤ),
      Monotone Cm → HvdH.MulBelow main N Cm → P < N →
      a.natAbs.size ≤ P → b.natAbs.size ≤ P →
      HvdH.WordR main q
        (fun vs => ∃ rest, vs = HvdH.Val.int a :: HvdH.Val.int b :: rest)
        (fun vs out => ∃ rest, vs = HvdH.Val.int a :: HvdH.Val.int b :: rest ∧
          out = HvdH.Val.int (a * b) :: rest)
        (fun _ => Kc * (Cm (Kc * P) + P + 1)) := by
  obtain ⟨signP, Ksign, hsign⟩ := buQWsignWord KL IL
  obtain ⟨magP, Kmag, hmag⟩ := buQWmagWord KL IL
  obtain ⟨mulSP, Kms, hms⟩ := IL.mulS
  let KS : ℕ := Ksign + Kmag + Kms + 1
  have hKsign : Ksign ≤ KS := by dsimp only [KS]; omega
  have hKmag : Kmag ≤ KS := by dsimp only [KS]; omega
  have hKms : Kms ≤ KS := by dsimp only [KS]; omega
  let Kc : ℕ := 3000 * KS + 1
  have hKc1 : 1 ≤ Kc := by dsimp only [Kc]; omega
  refine ⟨.seq signP (.seq magP (.seq .self mulSP)), Kc, ?_⟩
  intro main N Cm P a b hmono hmb hPN hsa hsb
  intro vs hpre st Rg hRg
  obtain ⟨rest, rfl⟩ := hpre
  let s : ℤ := buQWsgn a b
  have signPipe : Pipe main signP [.int a, .int b] [.int a, .int b, .int s]
      (KS * (1000 * (P + 1))) :=
    Pipe.le (c := Ksign * (a.natAbs.size + b.natAbs.size + 1))
      (fun r => hsign main a b r) (by
        have h1 : a.natAbs.size + b.natAbs.size + 1 ≤ 1000 * (P + 1) := by omega
        exact Nat.mul_le_mul hKsign h1)
  have magPipe : Pipe main magP [.int a, .int b, .int s]
      [.int (a.natAbs : ℤ), .int (b.natAbs : ℤ), .int s] (KS * (1000 * (P + 1))) :=
    Pipe.le (c := Kmag * (a.natAbs.size + b.natAbs.size + 1))
      (fun r => hmag main a b (.int s :: r)) (by
        have h1 : a.natAbs.size + b.natAbs.size + 1 ≤ 1000 * (P + 1) := by omega
        exact Nat.mul_le_mul hKmag h1)
  have hselfW : WordR main .self
      (fun vs => ∃ r, vs = .int (a.natAbs : ℤ) :: .int (b.natAbs : ℤ) :: r)
      (fun vs out => ∃ r, vs = .int (a.natAbs : ℤ) :: .int (b.natAbs : ℤ) :: r ∧
        out = .int ((a.natAbs * b.natAbs : ℕ) : ℤ) :: r)
      (fun _ => Cm (Kc * P)) := by
    refine Work.Kernel.WordR_conseq hmb ?_ ?_ ?_
    · intro vs hvs
      obtain ⟨r, rfl⟩ := hvs
      exact ⟨a.natAbs, b.natAbs, r, rfl, by omega, by omega⟩
    · intro vs out hvs hpost
      obtain ⟨r, rfl⟩ := hvs
      obtain ⟨x, y, r', hvs', hout'⟩ := hpost
      obtain ⟨h1, h2, h3⟩ := Work.Fx.int_cons_inj3 hvs'
      have hx : x = a.natAbs := (Int.natCast_inj.mp h1).symm
      have hy : y = b.natAbs := (Int.natCast_inj.mp h2).symm
      exact ⟨r, rfl, by rw [hout', hx, hy, ← h3]⟩
    · intro vs hvs
      obtain ⟨r, rfl⟩ := hvs
      refine hmono ?_
      rw [mulSize_int_natAbs]
      calc max a.natAbs.size b.natAbs.size ≤ P := by omega
        _ = 1 * P := (one_mul P).symm
        _ ≤ Kc * P := Nat.mul_le_mul_right P hKc1
  have selfPipe : Pipe main .self [.int (a.natAbs : ℤ), .int (b.natAbs : ℤ), .int s]
      [.int ((a.natAbs * b.natAbs : ℕ) : ℤ), .int s] (Cm (Kc * P)) :=
    Pipe.appendTail [.int s] (pipe_int2 hselfW)
  have mulPipe0 : Pipe main mulSP [.int ((a.natAbs * b.natAbs : ℕ) : ℤ), .int s]
      [.int (((a.natAbs * b.natAbs : ℕ) : ℤ) * s)]
      (Kms * isz ((a.natAbs * b.natAbs : ℕ) : ℤ) * isz s) :=
    Pipe.binOp (hms main) trivial
  have mulPipe : Pipe main mulSP [.int ((a.natAbs * b.natAbs : ℕ) : ℤ), .int s] [.int (a * b)]
      (KS * (1000 * (P + 1))) := by
    refine Pipe.le (c := Kms * isz ((a.natAbs * b.natAbs : ℕ) : ℤ) * isz s) ?_ ?_
    · refine Pipe.rw (c := Kms * isz ((a.natAbs * b.natAbs : ℕ) : ℤ) * isz s) mulPipe0 ?_
      refine congrArg (fun t : ℤ => [Val.int t]) ?_
      exact mul_buQWsgn a b
    · have h1 : isz ((a.natAbs * b.natAbs : ℕ) : ℤ) ≤ 2 * P + 2 := by
        have h := size_mul_le a.natAbs b.natAbs
        simp only [isz, Int.natAbs_natCast]
        omega
      have h2 : isz s ≤ 3 := isz_buQWsgn_le a b
      calc Kms * isz ((a.natAbs * b.natAbs : ℕ) : ℤ) * isz s
          ≤ Kms * (2 * P + 2) * 3 := Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
        _ ≤ KS * (1000 * (P + 1)) := by
            have h3 : (2 * P + 2) * 3 ≤ 1000 * (P + 1) := by omega
            calc Kms * (2 * P + 2) * 3 = Kms * ((2 * P + 2) * 3) := by ring
              _ ≤ KS * ((2 * P + 2) * 3) := Nat.mul_le_mul_right _ hKms
              _ ≤ KS * (1000 * (P + 1)) := Nat.mul_le_mul_left _ h3
  have hchain : Pipe main (.seq signP (.seq magP (.seq .self mulSP))) [.int a, .int b]
      [.int (a * b)]
      (KS * (1000 * (P + 1)) +
        (KS * (1000 * (P + 1)) + (Cm (Kc * P) + KS * (1000 * (P + 1))))) :=
    Pipe.comp signPipe (Pipe.comp magPipe (Pipe.comp selfPipe mulPipe))
  have hbound : KS * (1000 * (P + 1)) +
        (KS * (1000 * (P + 1)) + (Cm (Kc * P) + KS * (1000 * (P + 1))))
      ≤ Kc * (Cm (Kc * P) + P + 1) := by
    have h3 : 3 * (KS * (1000 * (P + 1))) ≤ Kc * (P + 1) := by
      have h3000 : 3000 * KS ≤ Kc := by dsimp only [Kc]; omega
      calc 3 * (KS * (1000 * (P + 1))) = (3000 * KS) * (P + 1) := by ring
        _ ≤ Kc * (P + 1) := Nat.mul_le_mul_right _ h3000
    have hCm : Cm (Kc * P) ≤ Kc * Cm (Kc * P) := by
      calc Cm (Kc * P) = 1 * Cm (Kc * P) := (one_mul _).symm
        _ ≤ Kc * Cm (Kc * P) := Nat.mul_le_mul_right _ hKc1
    have e : KS * (1000 * (P + 1)) +
        (KS * (1000 * (P + 1)) + (Cm (Kc * P) + KS * (1000 * (P + 1))))
        = 3 * (KS * (1000 * (P + 1))) + Cm (Kc * P) := by ring
    rw [e]
    calc 3 * (KS * (1000 * (P + 1))) + Cm (Kc * P)
        ≤ Kc * (P + 1) + Kc * Cm (Kc * P) := add_le_add h3 hCm
      _ = Kc * (Cm (Kc * P) + P + 1) := by ring
  have hpipe : Pipe main (.seq signP (.seq magP (.seq .self mulSP))) [.int a, .int b]
      [.int (a * b)] (Kc * (Cm (Kc * P) + P + 1)) := Pipe.le hchain hbound
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ :=
    hpipe rest (Val.int a :: Val.int b :: rest) rfl st Rg hRg
  exact ⟨out, s', n, ⟨rest, rfl, hout⟩, hev, hn, hstk, hoth⟩

end Work.Resample
