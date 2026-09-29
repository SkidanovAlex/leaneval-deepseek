import Mathlib
import Submission.Work.Main.defs

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! Self-contained backup of the per-coefficient rounding word (`Work.Main.word.recoverElemB`). -/

namespace Work.Main.word

open HvdH

local infixl:68 " ;;; " => HvdH.Cmd.seq

theorem r2_wordR_mono {main pr : Cmd} {P P' : List Val → Prop} {Q Q' : List Val → List Val → Prop}
    {C C' : List Val → ℕ} (h : WordR main pr P Q C) (h1 : ∀ vs, P' vs → P vs)
    (h2 : ∀ vs out, P' vs → Q vs out → Q' vs out) (h3 : ∀ vs, P' vs → C vs ≤ C' vs) :
    WordR main pr P' Q' C' := by
  intro vs hp s R hs
  obtain ⟨o, s', n, hQ, hev, hn, hl, hk⟩ := h vs (h1 vs hp) s R hs
  exact ⟨o, s', n, h2 vs o hp hQ, hev, le_trans hn (h3 vs hp), hl, hk⟩

theorem r2_seqDetSum {main : Cmd} {q₁ q₂ : Cmd} {A B C' : List Val} {a b P2 : ℕ}
    (h₁ : WordR main q₁ (fun vs => vs = A) (fun _ o => o = B) (fun _ => a * P2))
    (h₂ : WordR main q₂ (fun vs => vs = B) (fun _ o => o = C') (fun _ => b * P2)) :
    WordR main (.seq q₁ q₂) (fun vs => vs = A) (fun _ o => o = C') (fun _ => (a + b) * P2) := by
  intro vs hvs s R hs
  rw [hvs] at hs
  obtain ⟨o₁, s₁, n₁, ho₁, he₁, hn₁, hl₁, hk₁⟩ := h₁ A rfl s R hs
  rw [ho₁] at hl₁
  obtain ⟨o₂, s₂, n₂, ho₂, he₂, hn₂, hl₂, hk₂⟩ := h₂ B rfl s₁ R hl₁
  exact ⟨o₂, s₂, n₁ + n₂, ho₂, Eval.seq he₁ he₂,
    le_trans (Nat.add_le_add hn₁ hn₂) (by rw [Nat.add_mul]), hl₂,
    fun k hk => by rw [hk₂ k hk, hk₁ k hk]⟩

theorem r2_natAbs_le_two_pow {p : ℕ} {z : ℤ} (h : z ^ 2 ≤ (4 : ℤ) ^ p) : z.natAbs ≤ 2 ^ p := by
  have h3 : ((z.natAbs : ℤ)) ^ 2 ≤ (((2 ^ p : ℕ)) : ℤ) ^ 2 := by
    have e : ((z.natAbs : ℤ)) ^ 2 = z ^ 2 := by
      rw [← Int.natCast_pow, ← Int.natAbs_pow, Int.natAbs_of_nonneg (sq_nonneg z)]
    have e2 : (((2 ^ p : ℕ) : ℤ)) ^ 2 = (4 : ℤ) ^ p := by
      have h1 : (((2 ^ p : ℕ) : ℤ)) = (2 : ℤ) ^ p := Int.natCast_pow 2 p
      rw [h1, ← pow_mul, mul_comm, pow_mul, show (4 : ℤ) = (2 : ℤ) ^ 2 by norm_num]
    rw [e, e2]
    exact h
  exact (Nat.pow_le_pow_iff_left (n := 2) (show (2 : ℕ) ≠ 0 by norm_num)).mp (by exact_mod_cast h3)

theorem r2_isz_le_of_natAbs_le {z : ℤ} {p : ℕ} (h : z.natAbs ≤ 2 ^ p) : isz z ≤ p + 3 := by
  have h1 : z.natAbs.size ≤ p + 1 := by
    rw [Nat.size_le]
    exact lt_of_le_of_lt h (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self p))
  simp only [isz]
  omega

theorem r2_inDisc_fst_natAbs_le {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : z.1.natAbs ≤ 2 ^ p := by
  apply r2_natAbs_le_two_pow
  simp only [inDisc] at h
  nlinarith [sq_nonneg z.2]

theorem r2_inDisc_snd_natAbs_le {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : z.2.natAbs ≤ 2 ^ p := by
  apply r2_natAbs_le_two_pow
  simp only [inDisc] at h
  nlinarith [sq_nonneg z.1]

theorem r2_isz_fst_le {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : isz z.1 ≤ p + 3 :=
  r2_isz_le_of_natAbs_le (r2_inDisc_fst_natAbs_le h)

theorem r2_isz_snd_le {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : isz z.2 ≤ p + 3 :=
  r2_isz_le_of_natAbs_le (r2_inDisc_snd_natAbs_le h)

theorem r2_isz_le_of_le_two_pow {p c : ℕ} (h : c ≤ 2 ^ p) : isz ((c : ℤ)) ≤ p + 3 := by
  apply r2_isz_le_of_natAbs_le
  rw [Int.natAbs_natCast]; exact h

theorem r2_isz_int_le (p : ℕ) : isz ((p : ℤ)) ≤ p + 2 := by
  rw [isz, Int.natAbs_natCast]
  have h : p.size ≤ p := by
    rw [Nat.size_le]
    exact Nat.lt_two_pow_self
  omega







theorem recoverElemB (hKer : HvdH.KernelLib) (hInt : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ),
      ∀ (main : HvdH.Cmd) (S p b : ℕ) (z : ℤ × ℤ) (rest : List HvdH.Val),
        2 * b < p → S ≤ 2 ^ p → HvdH.inDisc p z →
        HvdH.WordR main prog
          (fun vs => vs = HvdH.cfxVal z :: HvdH.Val.int S :: HvdH.Val.int p :: HvdH.Val.int b :: rest)
          (fun _ out => out = HvdH.Val.int (Work.Main.recov S p b z) :: HvdH.Val.int S :: HvdH.Val.int p :: HvdH.Val.int b :: rest)
          (fun _ => K * (p + 1) * (p + 1)) := by
  obtain ⟨uP, Ku, huP⟩ := hKer.unconsV
  obtain ⟨sP, Ks, hsP⟩ := hKer.swap
  obtain ⟨dP, Kd, hdP⟩ := hKer.drop
  obtain ⟨pP, Kp, hpP⟩ := hKer.pick
  obtain ⟨mP, Km, hmP⟩ := hInt.mulS
  obtain ⟨aP, Ka, haP⟩ := hInt.add
  obtain ⟨bP, Kb, hbP⟩ := hInt.sub
  obtain ⟨wP, Kw, hwP⟩ := hInt.pow2
  obtain ⟨vP, Kv, hvP⟩ := hKer.pushVal
  obtain ⟨fP, Kf, hfP⟩ := hInt.fdiv
  refine ⟨uP ;;; sP ;;; dP ;;; pP 1 ;;; mP ;;; pP 3 ;;; pP 4 ;;; aP ;;; pP 3 ;;; bP ;;; vP (Val.int 1) ;;; sP ;;; bP ;;; wP ;;; aP ;;; pP 3 ;;; pP 4 ;;; aP ;;; pP 3 ;;; bP ;;; wP ;;; sP ;;; fP, Ku + 9 * Ks + 9 * Kd + 100 * Kp + 16 * Km + 200 * Kp + 250 * Kp + 20 * Ka + 200 * Kp + 20 * Kb + 20 * Kv + 20 * Ks + 20 * Kb + 20 * Kw + 20 * Ka + 200 * Kp + 250 * Kp + 20 * Ka + 200 * Kp + 20 * Kb + 20 * Kw + 20 * Ks + 16 * Kf, ?_⟩
  intro main S p b z rest h2b hS hz
  have hpX : p + 1 ≤ (p + 1) * (p + 1) := by
    have h : (p + 1) * 1 ≤ (p + 1) * (p + 1) := Nat.mul_le_mul_left _ (by omega)
    rwa [Nat.mul_one] at h
  have hz1 : isz z.1 ≤ p + 3 := r2_isz_fst_le hz
  have hz2 : isz z.2 ≤ p + 3 := r2_isz_snd_le hz
  have hS1 : isz (S : ℤ) ≤ p + 3 := r2_isz_le_of_le_two_pow hS
  have hp1 : isz (p : ℤ) ≤ p + 2 := r2_isz_int_le p
  have hb1 : isz (b : ℤ) ≤ p + 2 := by
    rw [isz, Int.natAbs_natCast]
    have hbs : b.size ≤ p := by
      rw [Nat.size_le]
      exact lt_of_lt_of_le (by omega : b < p) (le_of_lt Nat.lt_two_pow_self)
    omega
  have hone1 : isz (1 : ℤ) ≤ p + 3 := by
    apply r2_isz_le_of_natAbs_le
    have h3 : ((1 : ℤ)).natAbs = 1 := by norm_num
    rw [h3]; exact Nat.one_le_two_pow
  have hA1 : isz ((S : ℤ) * z.1) ≤ 2 * p + 4 := by
    apply r2_isz_le_of_natAbs_le
    have h : ((S : ℤ) * z.1).natAbs ≤ 2 ^ (2 * p) := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      have hh : 2 ^ (2 * p) = 2 ^ p * 2 ^ p := by
        rw [show 2 * p = p + p by omega, pow_add]
      rw [hh]
      exact Nat.mul_le_mul hS (r2_inDisc_fst_natAbs_le hz)
    calc ((S : ℤ) * z.1).natAbs ≤ 2 ^ (2 * p) := h
      _ ≤ 2 ^ (2 * p + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hB21 : isz ((b : ℤ) + (b : ℤ)) ≤ p + 2 := by
    have hh : ((b : ℤ) + (b : ℤ)).natAbs = 2 * b := by
      rw [show ((b : ℤ) + (b : ℤ)) = ((2 * b : ℕ) : ℤ) by rw [← Nat.cast_add, two_mul],
        Int.natAbs_natCast]
    rw [isz, hh]
    have hbs : (2 * b).size ≤ p := by
      rw [Nat.size_le]
      exact lt_of_lt_of_le (by omega : 2 * b < p) (le_of_lt Nat.lt_two_pow_self)
    omega
  have hPE : ((p : ℤ) - ((b : ℤ) + (b : ℤ))) = ((p - 2 * b : ℕ) : ℤ) := by
    have h2b : ((b : ℤ) + (b : ℤ)) = ((2 * b : ℕ) : ℤ) := by
      rw [← Nat.cast_add, two_mul]
    rw [h2b, ← Nat.cast_sub (show 2 * b ≤ p by omega)]
  have hKE : (((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1) = ((p - 2 * b - 1 : ℕ) : ℤ) := by
    rw [hPE]
    have hm1 : 1 ≤ p - 2 * b := by omega
    have hc := Int.natCast_sub hm1
    omega
  have htoNatPE : (((p : ℤ) - ((b : ℤ) + (b : ℤ)))).toNat = p - 2 * b := by
    rw [hPE, Int.toNat_natCast]
  have htoNatKE : ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat = p - 2 * b - 1 := by
    rw [hKE, Int.toNat_natCast]
  have hPE1 : isz ((p : ℤ) - ((b : ℤ) + (b : ℤ))) ≤ p + 2 := by
    have hh : ((p : ℤ) - ((b : ℤ) + (b : ℤ))).natAbs = p - 2 * b := by
      rw [hPE, Int.natAbs_natCast]
    rw [isz, hh]
    have hbs : (p - 2 * b).size ≤ p := by
      rw [Nat.size_le]
      exact lt_of_le_of_lt (by omega : p - 2 * b ≤ p) Nat.lt_two_pow_self
    omega
  have hKE1 : isz (((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1) ≤ p + 2 := by
    have hh : (((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1).natAbs = p - 2 * b - 1 := by
      rw [hKE, Int.natAbs_natCast]
    rw [isz, hh]
    have hbs : (p - 2 * b - 1).size ≤ p := by
      rw [Nat.size_le]
      exact lt_of_le_of_lt (by omega : p - 2 * b - 1 ≤ p) Nat.lt_two_pow_self
    omega
  have hD11 : isz (2 ^ (((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1).toNat : ℤ) ≤ p + 3 := by
    apply r2_isz_le_of_natAbs_le
    rw [Int.natAbs_pow, htoNatKE]
    have h2 : ((2 : ℤ)).natAbs = 2 := by norm_num
    rw [h2]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hN21 : isz (2 ^ (((p : ℤ) - ((b : ℤ) + (b : ℤ)))).toNat : ℤ) ≤ p + 3 := by
    apply r2_isz_le_of_natAbs_le
    rw [Int.natAbs_pow, htoNatPE]
    have h2 : ((2 : ℤ)).natAbs = 2 := by norm_num
    rw [h2]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hN1b : isz ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) ≤ 2 * p + 4 := by
    apply r2_isz_le_of_natAbs_le
    have h1 : ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat).natAbs ≤ 2 ^ p := by
      rw [Int.natAbs_pow, htoNatKE]
      have h2 : ((2 : ℤ)).natAbs = 2 := by norm_num
      rw [h2]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : ((S : ℤ) * z.1).natAbs ≤ 2 ^ (2 * p) := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      have hh : 2 ^ (2 * p) = 2 ^ p * 2 ^ p := by
        rw [show 2 * p = p + p by omega, pow_add]
      rw [hh]
      exact Nat.mul_le_mul hS (r2_inDisc_fst_natAbs_le hz)
    have h3 : ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1).natAbs ≤ 2 ^ p + 2 ^ (2 * p) :=
      le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add h1 h2)
    have h4 : 2 ^ p ≤ 2 ^ (2 * p) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 : 2 ^ (2 * p) + 2 ^ (2 * p) = 2 ^ (2 * p + 1) := by rw [pow_succ]; ring
    calc ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1).natAbs ≤ 2 ^ p + 2 ^ (2 * p) := h3
      _ ≤ 2 ^ (2 * p) + 2 ^ (2 * p) := Nat.add_le_add_right h4 _
      _ = 2 ^ (2 * p + 1) := h5







  have S1 : WordR main (uP) (fun vs => vs = cfxVal z :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int (z.1) :: Val.int (z.2) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => Ku * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (huP main) ?_ ?_ ?_
    · exact fun vs hvs => ⟨Val.int z.1, Val.int z.2, Val.int S :: Val.int p :: Val.int b :: rest, by rw [hvs]; rfl⟩
    · rintro vs out hvs hout
      obtain ⟨a, b', r, hv, ho⟩ := hout
      rw [hvs] at hv
      cases hv
      exact ho
    · intro vs hvs
      exact Nat.le_mul_of_pos_right _ (by positivity)
  have S2 : WordR main (sP) (fun vs => vs = Val.int (z.1) :: Val.int (z.2) :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int (z.2) :: Val.int (z.1) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => 9 * Ks * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (hsP main) ?_ ?_ ?_
    · exact fun vs hvs => by rw [hvs]; simp
    · rintro vs out hvs hout
      obtain ⟨a, b', r, hv, ho⟩ := hout
      rw [hvs] at hv
      cases hv
      exact ho
    · intro vs hvs
      have hlin : vsz (vs.getD 0 Val.nil) + vsz (vs.getD 1 Val.nil) + 1 ≤ 9 * ((p + 1) * (p + 1)) := by
        rw [hvs]
        simp only [List.getD_cons_zero, List.getD_cons_succ, Work.Main.vsz_int]
        omega
      have h := Nat.mul_le_mul_left Ks hlin
      have he : Ks * (9 * ((p + 1) * (p + 1))) = 9 * Ks * ((p + 1) * (p + 1)) := by ring
      rwa [he] at h
  have S3 : WordR main (dP) (fun vs => vs = Val.int (z.2) :: Val.int (z.1) :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int (z.1) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => 9 * Kd * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (hdP main) ?_ ?_ ?_
    · exact fun vs hvs => by rw [hvs]; simp
    · rintro vs out hvs hout
      obtain ⟨v, r, hv, ho⟩ := hout
      rw [hvs] at hv
      cases hv
      exact ho
    · intro vs hvs
      have hlin : vsz (vs.headD Val.nil) + 1 ≤ 9 * ((p + 1) * (p + 1)) := by
        rw [hvs]
        simp only [List.headD_cons, Work.Main.vsz_int]
        omega
      have h := Nat.mul_le_mul_left Kd hlin
      have he : Kd * (9 * ((p + 1) * (p + 1))) = 9 * Kd * ((p + 1) * (p + 1)) := by ring
      rwa [he] at h
  have S4 : WordR main (pP 1) (fun vs => vs = Val.int (z.1) :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int (S) :: Val.int (z.1) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => 100 * Kp * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (hpP main 1) ?_ ?_ ?_
    · exact fun vs hvs => by rw [hvs]; simp
    · rintro vs out hvs hout
      rw [hvs] at hout
      rw [hout]
      simp
    · intro vs hvs
      have hlin : (((vs.take (1+1)).map vsz).sum + 1) ≤ 50 * ((p + 1) * (p + 1)) := by
        rw [hvs]
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Work.Main.vsz_int]
        omega
      have h := Nat.mul_le_mul_left (Kp * (1+1)) hlin
      have he : (Kp * (1+1)) * (50 * ((p + 1) * (p + 1))) = 100 * Kp * ((p + 1) * (p + 1)) := by ring
      rwa [he] at h
  have S5 : WordR main (mP) (fun vs => vs = Val.int (S) :: Val.int (z.1) :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => 16 * Km * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (hmP main) ?_ ?_ ?_
    · exact fun vs hvs => ⟨(S : ℤ), z.1, Val.int S :: Val.int p :: Val.int b :: rest, by rw [hvs], trivial⟩
    · rintro vs out hvs hout
      obtain ⟨a, b', r, hv, ho⟩ := hout
      rw [hvs] at hv
      cases hv
      exact ho
    · intro vs hvs
      rw [hvs]
      show Km * isz (S : ℤ) * isz z.1 ≤ 16 * Km * ((p + 1) * (p + 1))
      rw [Nat.mul_assoc]
      have hlin : isz (S : ℤ) * isz z.1 ≤ 16 * ((p + 1) * (p + 1)) := by
        have h4 : isz (S : ℤ) ≤ 4 * (p + 1) := by omega
        have h5 : isz z.1 ≤ 4 * (p + 1) := by omega
        have h6 : isz (S : ℤ) * isz z.1 ≤ (4 * (p + 1)) * (4 * (p + 1)) := Nat.mul_le_mul h4 h5
        have h7 : (4 * (p + 1)) * (4 * (p + 1)) = 16 * ((p + 1) * (p + 1)) := by ring
        rw [h7] at h6; exact h6
      calc Km * (isz (S : ℤ) * isz z.1) ≤ Km * (16 * ((p + 1) * (p + 1))) := Nat.mul_le_mul_left _ hlin
        _ = 16 * Km * ((p + 1) * (p + 1)) := by ring
  have S6 : WordR main (pP 3) (fun vs => vs = Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int (b) :: Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => 200 * Kp * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (hpP main 3) ?_ ?_ ?_
    · exact fun vs hvs => by rw [hvs]; simp
    · rintro vs out hvs hout
      rw [hvs] at hout
      rw [hout]
      simp
    · intro vs hvs
      have hlin : (((vs.take (3+1)).map vsz).sum + 1) ≤ 50 * ((p + 1) * (p + 1)) := by
        rw [hvs]
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Work.Main.vsz_int]
        omega
      have h := Nat.mul_le_mul_left (Kp * (3+1)) hlin
      have he : (Kp * (3+1)) * (50 * ((p + 1) * (p + 1))) = 200 * Kp * ((p + 1) * (p + 1)) := by ring
      rwa [he] at h
  have S7 : WordR main (pP 4) (fun vs => vs = Val.int (b) :: Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int (b) :: Val.int (b) :: Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => 250 * Kp * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (hpP main 4) ?_ ?_ ?_
    · exact fun vs hvs => by rw [hvs]; simp
    · rintro vs out hvs hout
      rw [hvs] at hout
      rw [hout]
      simp
    · intro vs hvs
      have hlin : (((vs.take (4+1)).map vsz).sum + 1) ≤ 50 * ((p + 1) * (p + 1)) := by
        rw [hvs]
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Work.Main.vsz_int]
        omega
      have h := Nat.mul_le_mul_left (Kp * (4+1)) hlin
      have he : (Kp * (4+1)) * (50 * ((p + 1) * (p + 1))) = 250 * Kp * ((p + 1) * (p + 1)) := by ring
      rwa [he] at h
  have S8 : WordR main (aP) (fun vs => vs = Val.int (b) :: Val.int (b) :: Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int ((b : ℤ) + (b : ℤ)) :: Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => 20 * Ka * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (haP main) ?_ ?_ ?_
    · exact fun vs hvs => ⟨(b : ℤ), (b : ℤ), Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest, by rw [hvs], trivial⟩
    · rintro vs out hvs hout
      obtain ⟨a, b', r, hv, ho⟩ := hout
      rw [hvs] at hv
      cases hv
      exact ho
    · intro vs hvs
      rw [hvs]
      show Ka * (isz (b : ℤ) + isz (b : ℤ)) ≤ 20 * Ka * ((p + 1) * (p + 1))
      have hlin : isz (b : ℤ) + isz (b : ℤ) ≤ 20 * ((p + 1) * (p + 1)) := by omega
      calc Ka * (isz (b : ℤ) + isz (b : ℤ)) ≤ Ka * (20 * ((p + 1) * (p + 1))) := Nat.mul_le_mul_left _ hlin
        _ = 20 * Ka * ((p + 1) * (p + 1)) := by ring
  have S9 : WordR main (pP 3) (fun vs => vs = Val.int ((b : ℤ) + (b : ℤ)) :: Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int (p) :: Val.int ((b : ℤ) + (b : ℤ)) :: Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => 200 * Kp * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (hpP main 3) ?_ ?_ ?_
    · exact fun vs hvs => by rw [hvs]; simp
    · rintro vs out hvs hout
      rw [hvs] at hout
      rw [hout]
      simp
    · intro vs hvs
      have hlin : (((vs.take (3+1)).map vsz).sum + 1) ≤ 50 * ((p + 1) * (p + 1)) := by
        rw [hvs]
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Work.Main.vsz_int]
        omega
      have h := Nat.mul_le_mul_left (Kp * (3+1)) hlin
      have he : (Kp * (3+1)) * (50 * ((p + 1) * (p + 1))) = 200 * Kp * ((p + 1) * (p + 1)) := by ring
      rwa [he] at h
  have S10 : WordR main (bP) (fun vs => vs = Val.int (p) :: Val.int ((b : ℤ) + (b : ℤ)) :: Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int ((p : ℤ) - ((b : ℤ) + (b : ℤ))) :: Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => 20 * Kb * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (hbP main) ?_ ?_ ?_
    · exact fun vs hvs => ⟨(p : ℤ), (b : ℤ) + (b : ℤ), Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest, by rw [hvs], trivial⟩
    · rintro vs out hvs hout
      obtain ⟨a, b', r, hv, ho⟩ := hout
      rw [hvs] at hv
      cases hv
      exact ho
    · intro vs hvs
      rw [hvs]
      show Kb * (isz (p : ℤ) + isz ((b : ℤ) + (b : ℤ))) ≤ 20 * Kb * ((p + 1) * (p + 1))
      have hlin : isz (p : ℤ) + isz ((b : ℤ) + (b : ℤ)) ≤ 20 * ((p + 1) * (p + 1)) := by omega
      calc Kb * (isz (p : ℤ) + isz ((b : ℤ) + (b : ℤ))) ≤ Kb * (20 * ((p + 1) * (p + 1))) := Nat.mul_le_mul_left _ hlin
        _ = 20 * Kb * ((p + 1) * (p + 1)) := by ring
  have S11 : WordR main (vP (Val.int 1)) (fun vs => vs = Val.int ((p : ℤ) - ((b : ℤ) + (b : ℤ))) :: Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int (1) :: Val.int ((p : ℤ) - ((b : ℤ) + (b : ℤ))) :: Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => 20 * Kv * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (hvP main (Val.int (1 : ℤ))) ?_ ?_ ?_
    · exact fun _ _ => trivial
    · rintro vs out hvs hout
      rw [hvs] at hout
      exact hout
    · intro vs hvs
      have hlin : vsz (Val.int (1 : ℤ)) + 1 ≤ 20 * ((p + 1) * (p + 1)) := by
        rw [Work.Main.vsz_int]; omega
      calc Kv * (vsz (Val.int (1 : ℤ)) + 1) ≤ Kv * (20 * ((p + 1) * (p + 1))) := Nat.mul_le_mul_left _ hlin
        _ = 20 * Kv * ((p + 1) * (p + 1)) := by ring
  have S12 : WordR main (sP) (fun vs => vs = Val.int (1) :: Val.int ((p : ℤ) - ((b : ℤ) + (b : ℤ))) :: Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int ((p : ℤ) - ((b : ℤ) + (b : ℤ))) :: Val.int (1) :: Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => 20 * Ks * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (hsP main) ?_ ?_ ?_
    · exact fun vs hvs => by rw [hvs]; simp
    · rintro vs out hvs hout
      obtain ⟨a, b', r, hv, ho⟩ := hout
      rw [hvs] at hv
      cases hv
      exact ho
    · intro vs hvs
      have hlin : vsz (vs.getD 0 Val.nil) + vsz (vs.getD 1 Val.nil) + 1 ≤ 20 * ((p + 1) * (p + 1)) := by
        rw [hvs]
        simp only [List.getD_cons_zero, List.getD_cons_succ, Work.Main.vsz_int]
        omega
      have h := Nat.mul_le_mul_left Ks hlin
      have he : Ks * (20 * ((p + 1) * (p + 1))) = 20 * Ks * ((p + 1) * (p + 1)) := by ring
      rwa [he] at h
  have S13 : WordR main (bP) (fun vs => vs = Val.int ((p : ℤ) - ((b : ℤ) + (b : ℤ))) :: Val.int (1) :: Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int (((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1) :: Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => 20 * Kb * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (hbP main) ?_ ?_ ?_
    · exact fun vs hvs => ⟨(p : ℤ) - ((b : ℤ) + (b : ℤ)), (1 : ℤ), Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest, by rw [hvs], trivial⟩
    · rintro vs out hvs hout
      obtain ⟨a, b', r, hv, ho⟩ := hout
      rw [hvs] at hv
      cases hv
      exact ho
    · intro vs hvs
      rw [hvs]
      show Kb * (isz ((p : ℤ) - ((b : ℤ) + (b : ℤ))) + isz (1 : ℤ)) ≤ 20 * Kb * ((p + 1) * (p + 1))
      have hlin : isz ((p : ℤ) - ((b : ℤ) + (b : ℤ))) + isz (1 : ℤ) ≤ 20 * ((p + 1) * (p + 1)) := by omega
      calc Kb * (isz ((p : ℤ) - ((b : ℤ) + (b : ℤ))) + isz (1 : ℤ)) ≤ Kb * (20 * ((p + 1) * (p + 1))) := Nat.mul_le_mul_left _ hlin
        _ = 20 * Kb * ((p + 1) * (p + 1)) := by ring
  have S14 : WordR main (wP) (fun vs => vs = Val.int (((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1) :: Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat) :: Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => 20 * Kw * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (hwP main) ?_ ?_ ?_
    · exact fun vs hvs => ⟨((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1, Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest, by rw [hvs], by omega⟩
    · rintro vs out hvs hout
      obtain ⟨a, r, hv, ho⟩ := hout
      rw [hvs] at hv
      cases hv
      exact ho
    · intro vs hvs
      rw [hvs]
      show Kw * ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1).toNat + isz (((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)) ≤ 20 * Kw * ((p + 1) * (p + 1))
      rw [htoNatKE]
      have hlin : (p - 2 * b - 1) + isz (((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1) ≤ 20 * ((p + 1) * (p + 1)) := by omega
      calc Kw * ((p - 2 * b - 1) + isz (((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)) ≤ Kw * (20 * ((p + 1) * (p + 1))) := Nat.mul_le_mul_left _ hlin
        _ = 20 * Kw * ((p + 1) * (p + 1)) := by ring
  have S15 : WordR main (aP) (fun vs => vs = Val.int ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat) :: Val.int ((S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => 20 * Ka * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (haP main) ?_ ?_ ?_
    · exact fun vs hvs => ⟨(2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat, (S : ℤ) * z.1, Val.int S :: Val.int p :: Val.int b :: rest, by rw [hvs], trivial⟩
    · rintro vs out hvs hout
      obtain ⟨a, b', r, hv, ho⟩ := hout
      rw [hvs] at hv
      cases hv
      exact ho
    · intro vs hvs
      rw [hvs]
      show Ka * (isz ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat) + isz ((S : ℤ) * z.1)) ≤ 20 * Ka * ((p + 1) * (p + 1))
      have hlin : isz ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat) + isz ((S : ℤ) * z.1) ≤ 20 * ((p + 1) * (p + 1)) := by omega
      calc Ka * (isz ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat) + isz ((S : ℤ) * z.1)) ≤ Ka * (20 * ((p + 1) * (p + 1))) := Nat.mul_le_mul_left _ hlin
        _ = 20 * Ka * ((p + 1) * (p + 1)) := by ring
  have S16 : WordR main (pP 3) (fun vs => vs = Val.int ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int (b) :: Val.int ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => 200 * Kp * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (hpP main 3) ?_ ?_ ?_
    · exact fun vs hvs => by rw [hvs]; simp
    · rintro vs out hvs hout
      rw [hvs] at hout
      rw [hout]
      simp
    · intro vs hvs
      have hlin : (((vs.take (3+1)).map vsz).sum + 1) ≤ 50 * ((p + 1) * (p + 1)) := by
        rw [hvs]
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Work.Main.vsz_int]
        omega
      have h := Nat.mul_le_mul_left (Kp * (3+1)) hlin
      have he : (Kp * (3+1)) * (50 * ((p + 1) * (p + 1))) = 200 * Kp * ((p + 1) * (p + 1)) := by ring
      rwa [he] at h
  have S17 : WordR main (pP 4) (fun vs => vs = Val.int (b) :: Val.int ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int (b) :: Val.int (b) :: Val.int ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => 250 * Kp * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (hpP main 4) ?_ ?_ ?_
    · exact fun vs hvs => by rw [hvs]; simp
    · rintro vs out hvs hout
      rw [hvs] at hout
      rw [hout]
      simp
    · intro vs hvs
      have hlin : (((vs.take (4+1)).map vsz).sum + 1) ≤ 50 * ((p + 1) * (p + 1)) := by
        rw [hvs]
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Work.Main.vsz_int]
        omega
      have h := Nat.mul_le_mul_left (Kp * (4+1)) hlin
      have he : (Kp * (4+1)) * (50 * ((p + 1) * (p + 1))) = 250 * Kp * ((p + 1) * (p + 1)) := by ring
      rwa [he] at h
  have S18 : WordR main (aP) (fun vs => vs = Val.int (b) :: Val.int (b) :: Val.int ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int ((b : ℤ) + (b : ℤ)) :: Val.int ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => 20 * Ka * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (haP main) ?_ ?_ ?_
    · exact fun vs hvs => ⟨(b : ℤ), (b : ℤ), Val.int ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest, by rw [hvs], trivial⟩
    · rintro vs out hvs hout
      obtain ⟨a, b', r, hv, ho⟩ := hout
      rw [hvs] at hv
      cases hv
      exact ho
    · intro vs hvs
      rw [hvs]
      show Ka * (isz (b : ℤ) + isz (b : ℤ)) ≤ 20 * Ka * ((p + 1) * (p + 1))
      have hlin : isz (b : ℤ) + isz (b : ℤ) ≤ 20 * ((p + 1) * (p + 1)) := by omega
      calc Ka * (isz (b : ℤ) + isz (b : ℤ)) ≤ Ka * (20 * ((p + 1) * (p + 1))) := Nat.mul_le_mul_left _ hlin
        _ = 20 * Ka * ((p + 1) * (p + 1)) := by ring
  have S19 : WordR main (pP 3) (fun vs => vs = Val.int ((b : ℤ) + (b : ℤ)) :: Val.int ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int (p) :: Val.int ((b : ℤ) + (b : ℤ)) :: Val.int ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => 200 * Kp * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (hpP main 3) ?_ ?_ ?_
    · exact fun vs hvs => by rw [hvs]; simp
    · rintro vs out hvs hout
      rw [hvs] at hout
      rw [hout]
      simp
    · intro vs hvs
      have hlin : (((vs.take (3+1)).map vsz).sum + 1) ≤ 50 * ((p + 1) * (p + 1)) := by
        rw [hvs]
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Work.Main.vsz_int]
        omega
      have h := Nat.mul_le_mul_left (Kp * (3+1)) hlin
      have he : (Kp * (3+1)) * (50 * ((p + 1) * (p + 1))) = 200 * Kp * ((p + 1) * (p + 1)) := by ring
      rwa [he] at h
  have S20 : WordR main (bP) (fun vs => vs = Val.int (p) :: Val.int ((b : ℤ) + (b : ℤ)) :: Val.int ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int ((p : ℤ) - ((b : ℤ) + (b : ℤ))) :: Val.int ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => 20 * Kb * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (hbP main) ?_ ?_ ?_
    · exact fun vs hvs => ⟨(p : ℤ), (b : ℤ) + (b : ℤ), Val.int ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest, by rw [hvs], trivial⟩
    · rintro vs out hvs hout
      obtain ⟨a, b', r, hv, ho⟩ := hout
      rw [hvs] at hv
      cases hv
      exact ho
    · intro vs hvs
      rw [hvs]
      show Kb * (isz (p : ℤ) + isz ((b : ℤ) + (b : ℤ))) ≤ 20 * Kb * ((p + 1) * (p + 1))
      have hlin : isz (p : ℤ) + isz ((b : ℤ) + (b : ℤ)) ≤ 20 * ((p + 1) * (p + 1)) := by omega
      calc Kb * (isz (p : ℤ) + isz ((b : ℤ) + (b : ℤ))) ≤ Kb * (20 * ((p + 1) * (p + 1))) := Nat.mul_le_mul_left _ hlin
        _ = 20 * Kb * ((p + 1) * (p + 1)) := by ring
  have S21 : WordR main (wP) (fun vs => vs = Val.int ((p : ℤ) - ((b : ℤ) + (b : ℤ))) :: Val.int ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int ((2 : ℤ) ^ (((p : ℤ) - ((b : ℤ) + (b : ℤ)))).toNat) :: Val.int ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => 20 * Kw * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (hwP main) ?_ ?_ ?_
    · exact fun vs hvs => ⟨(p : ℤ) - ((b : ℤ) + (b : ℤ)), Val.int ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest, by rw [hvs], by omega⟩
    · rintro vs out hvs hout
      obtain ⟨a, r, hv, ho⟩ := hout
      rw [hvs] at hv
      cases hv
      exact ho
    · intro vs hvs
      rw [hvs]
      show Kw * (((p : ℤ) - ((b : ℤ) + (b : ℤ))).toNat + isz ((p : ℤ) - ((b : ℤ) + (b : ℤ)))) ≤ 20 * Kw * ((p + 1) * (p + 1))
      rw [htoNatPE]
      have hlin : (p - 2 * b) + isz ((p : ℤ) - ((b : ℤ) + (b : ℤ))) ≤ 20 * ((p + 1) * (p + 1)) := by omega
      calc Kw * ((p - 2 * b) + isz ((p : ℤ) - ((b : ℤ) + (b : ℤ)))) ≤ Kw * (20 * ((p + 1) * (p + 1))) := Nat.mul_le_mul_left _ hlin
        _ = 20 * Kw * ((p + 1) * (p + 1)) := by ring
  have S22 : WordR main (sP) (fun vs => vs = Val.int ((2 : ℤ) ^ (((p : ℤ) - ((b : ℤ) + (b : ℤ)))).toNat) :: Val.int ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) :: Val.int ((2 : ℤ) ^ (((p : ℤ) - ((b : ℤ) + (b : ℤ)))).toNat) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => 20 * Ks * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (hsP main) ?_ ?_ ?_
    · exact fun vs hvs => by rw [hvs]; simp
    · rintro vs out hvs hout
      obtain ⟨a, b', r, hv, ho⟩ := hout
      rw [hvs] at hv
      cases hv
      exact ho
    · intro vs hvs
      have hlin : vsz (vs.getD 0 Val.nil) + vsz (vs.getD 1 Val.nil) + 1 ≤ 20 * ((p + 1) * (p + 1)) := by
        rw [hvs]
        simp only [List.getD_cons_zero, List.getD_cons_succ, Work.Main.vsz_int]
        omega
      have h := Nat.mul_le_mul_left Ks hlin
      have he : Ks * (20 * ((p + 1) * (p + 1))) = 20 * Ks * ((p + 1) * (p + 1)) := by ring
      rwa [he] at h
  have S23 : WordR main (fP) (fun vs => vs = Val.int ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) :: Val.int ((2 : ℤ) ^ (((p : ℤ) - ((b : ℤ) + (b : ℤ)))).toNat) :: Val.int S :: Val.int p :: Val.int b :: rest)
      (fun _ out => out = Val.int (((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1).fdiv ((2 : ℤ) ^ (((p : ℤ) - ((b : ℤ) + (b : ℤ)))).toNat)) :: Val.int S :: Val.int p :: Val.int b :: rest) (fun _ => 16 * Kf * ((p + 1) * (p + 1))) := by
    refine r2_wordR_mono (hfP main) ?_ ?_ ?_
    · exact fun vs hvs => ⟨(2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1, (2 : ℤ) ^ (((p : ℤ) - ((b : ℤ) + (b : ℤ)))).toNat, Val.int S :: Val.int p :: Val.int b :: rest, by rw [hvs], by positivity⟩
    · rintro vs out hvs hout
      obtain ⟨a, b', r, hv, ho⟩ := hout
      rw [hvs] at hv
      cases hv
      exact ho
    · intro vs hvs
      rw [hvs]
      show Kf * isz ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) * isz ((2 : ℤ) ^ (((p : ℤ) - ((b : ℤ) + (b : ℤ)))).toNat) ≤ 16 * Kf * ((p + 1) * (p + 1))
      rw [Nat.mul_assoc]
      have hlin : isz ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) * isz ((2 : ℤ) ^ (((p : ℤ) - ((b : ℤ) + (b : ℤ)))).toNat) ≤ 16 * ((p + 1) * (p + 1)) := by
        have h4 : isz ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) ≤ 4 * (p + 1) := by omega
        have h5 : isz ((2 : ℤ) ^ (((p : ℤ) - ((b : ℤ) + (b : ℤ)))).toNat) ≤ 4 * (p + 1) := by omega
        have h6 : isz ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) * isz ((2 : ℤ) ^ (((p : ℤ) - ((b : ℤ) + (b : ℤ)))).toNat) ≤ (4 * (p + 1)) * (4 * (p + 1)) := Nat.mul_le_mul h4 h5
        have h7 : (4 * (p + 1)) * (4 * (p + 1)) = 16 * ((p + 1) * (p + 1)) := by ring
        rw [h7] at h6; exact h6
      calc Kf * (isz ((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1) * isz ((2 : ℤ) ^ (((p : ℤ) - ((b : ℤ) + (b : ℤ)))).toNat)) ≤ Kf * (16 * ((p + 1) * (p + 1))) := Nat.mul_le_mul_left _ hlin
        _ = 16 * Kf * ((p + 1) * (p + 1)) := by ring
  have J2 := r2_seqDetSum S1 S2
  have J3 := r2_seqDetSum J2 S3
  have J4 := r2_seqDetSum J3 S4
  have J5 := r2_seqDetSum J4 S5
  have J6 := r2_seqDetSum J5 S6
  have J7 := r2_seqDetSum J6 S7
  have J8 := r2_seqDetSum J7 S8
  have J9 := r2_seqDetSum J8 S9
  have J10 := r2_seqDetSum J9 S10
  have J11 := r2_seqDetSum J10 S11
  have J12 := r2_seqDetSum J11 S12
  have J13 := r2_seqDetSum J12 S13
  have J14 := r2_seqDetSum J13 S14
  have J15 := r2_seqDetSum J14 S15
  have J16 := r2_seqDetSum J15 S16
  have J17 := r2_seqDetSum J16 S17
  have J18 := r2_seqDetSum J17 S18
  have J19 := r2_seqDetSum J18 S19
  have J20 := r2_seqDetSum J19 S20
  have J21 := r2_seqDetSum J20 S21
  have J22 := r2_seqDetSum J21 S22
  have J23 := r2_seqDetSum J22 S23
  have hdiv : (((2 : ℤ) ^ ((((p : ℤ) - ((b : ℤ) + (b : ℤ))) - 1)).toNat + (S : ℤ) * z.1).fdiv ((2 : ℤ) ^ (((p : ℤ) - ((b : ℤ) + (b : ℤ)))).toNat)) = Work.Main.recov S p b z := by
    rw [htoNatKE, htoNatPE, Work.Main.recov]
    congr 1
    ring
  refine r2_wordR_mono J23 (fun _ h => h) ?_ ?_
  · rintro vs out hvs hout
    rw [hout, hdiv]
  · intro vs hvs
    rw [← Nat.mul_assoc]

end Work.Main.word
