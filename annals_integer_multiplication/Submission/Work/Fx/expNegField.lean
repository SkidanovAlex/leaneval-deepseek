import Mathlib
import Submission.Work.Fx.FxExpCore
import Submission.Work.Fx.mulSField
import Submission.Work.Fx.expStepErr
import Submission.Work.Fx.expNegXtau
import Submission.Work.Fx.expNegZ
import Submission.Work.Fx.expNegFinalB
import Submission.Work.Fx.expNegZero

set_option autoImplicit false
set_option maxHeartbeats 10000000

namespace Work.Fx

open HvdH

/-! ## Adapters for exact-window chaining with existential postconditions -/

/-- `WordR` with an exact input window and an arbitrary postcondition. -/
theorem wrd_rel {main prog : Cmd} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {C : List Val → ℕ} {A : List Val} {B : List Val → List Val → Prop} {c : ℕ}
    (h : WordR main prog P Q C) (hA : P A) (hB : ∀ out, Q A out → B A out) (hc : C A ≤ c) :
    WordR main prog (fun vs => vs = A) B (fun _ => c) := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, hPost, hev, hn, hstk, hfr⟩ := h vs (hvs ▸ hA) s R hR
  have hb : B vs out := by
    have h1 : Q A out := by rwa [hvs] at hPost
    have h2 : B A out := hB out h1
    rwa [← hvs] at h2
  refine ⟨out, s', n, hb, hev, ?_, hstk, hfr⟩
  show n ≤ c
  exact le_trans hn (by rwa [← hvs] at hc)

/-- Sequential composition where the first step's postcondition may be existential. -/
theorem wrd_seq_exi {main p q : Cmd} {A : List Val} {Q : List Val → List Val → Prop}
    {S : List Val → Prop} {c1 c2 : ℕ}
    (h1 : WordR main p (fun vs => vs = A) Q (fun _ => c1))
    (h2 : ∀ mid, Q A mid → WordR main q (fun vs => vs = mid) (fun _ out => S out) (fun _ => c2)) :
    WordR main (.seq p q) (fun vs => vs = A) (fun _ out => S out) (fun _ => c1 + c2) := by
  intro vs hvs s R0 hR
  obtain ⟨mid, s1, n1, hmid, hev1, hn1, hstk1, hfr1⟩ := h1 vs hvs s R0 hR
  have hm2 : Q A mid := by rwa [hvs] at hmid
  obtain ⟨out, s2, n2, hS, hev2, hn2, hstk2, hfr2⟩ := h2 mid hm2 mid rfl s1 R0 hstk1
  have hn1' : n1 ≤ c1 := hn1
  have hn2' : n2 ≤ c2 := hn2
  refine ⟨out, s2, n1 + n2, hS, Eval.seq hev1 hev2, ?_, hstk2,
    fun k hk => by rw [hfr2 k hk, hfr1 k hk]⟩
  show n1 + n2 ≤ c1 + c2
  omega

/-- The `π` word on an exact window. -/
theorem wrd_piW {main : Cmd} {prog : Cmd} {K : ℕ}
    (h : ∀ (m : Cmd) (p : ℕ), 100 ≤ p → WordR m prog
      (fun vs => ∃ rest, vs = .int (p : ℤ) :: rest)
      (fun vs out => ∃ rest u, vs = .int (p : ℤ) :: rest ∧ out = .int u :: rest ∧
        |(u : ℝ) - 2 ^ p * Real.pi| ≤ 1) (fun _ => K * (p + 1) ^ K))
    (P : ℕ) (hP : 100 ≤ P) (A : List Val) (tail : List Val) (hA : A = .int ((P : ℕ) : ℤ) :: tail) :
    WordR main prog (fun vs => vs = A)
      (fun _ out => ∃ u : ℤ, |(u : ℝ) - 2 ^ P * Real.pi| ≤ 1 ∧ out = .int u :: tail)
      (fun _ => K * (P + 1) ^ K) := by
  refine wrd_rel (h main P hP) ?_ ?_ le_rfl
  · rw [hA]; exact ⟨tail, rfl⟩
  · intro out hQ
    rcases hQ with ⟨rest', u, hvs, hout, hu⟩
    have hvs' : (HvdH.Val.int ((P : ℕ) : ℤ) :: tail : List Val) = .int (P : ℤ) :: rest' := by
      rw [← hA]; exact hvs
    have hr : rest' = tail := ((List.cons.inj hvs').2).symm
    exact ⟨u, hu, by rw [hout, hr]⟩

/-- The `log 2` word on an exact window. -/
theorem wrd_logW {main : Cmd} {prog : Cmd} {K : ℕ}
    (h : ∀ (m : Cmd) (p : ℕ), 100 ≤ p → WordR m prog
      (fun vs => ∃ rest, vs = .int (p : ℤ) :: rest)
      (fun vs out => ∃ rest u, vs = .int (p : ℤ) :: rest ∧ out = .int u :: rest ∧
        |(u : ℝ) - 2 ^ p * Real.log 2| ≤ 1) (fun _ => K * (p + 1) ^ K))
    (P : ℕ) (hP : 100 ≤ P) (A : List Val) (tail : List Val) (hA : A = .int ((P : ℕ) : ℤ) :: tail) :
    WordR main prog (fun vs => vs = A)
      (fun _ out => ∃ L : ℤ, |(L : ℝ) - 2 ^ P * Real.log 2| ≤ 1 ∧ out = .int L :: tail)
      (fun _ => K * (P + 1) ^ K) := by
  refine wrd_rel (h main P hP) ?_ ?_ le_rfl
  · rw [hA]; exact ⟨tail, rfl⟩
  · intro out hQ
    rcases hQ with ⟨rest', u, hvs, hout, hu⟩
    have hvs' : (HvdH.Val.int ((P : ℕ) : ℤ) :: tail : List Val) = .int (P : ℤ) :: rest' := by
      rw [← hA]; exact hvs
    have hr : rest' = tail := ((List.cons.inj hvs').2).symm
    exact ⟨u, hu, by rw [hout, hr]⟩

/-- The imaginary part of the `expc` output is small. -/
theorem isz_V_le {P : ℕ} {U V : ℤ} {z : ℝ}
    (h : ‖((U : ℂ) + (V : ℂ) * Complex.I) / 2 ^ P - Complex.exp ((z : ℝ) : ℂ)‖ ≤ 4 / 2 ^ P) :
    V.natAbs ≤ 4 := by
  have him : ((((U : ℂ) + (V : ℂ) * Complex.I) / 2 ^ P) - Complex.exp ((z : ℝ) : ℂ)).im
      = (V : ℝ) / 2 ^ P := by
    rw [Complex.sub_im, Complex.exp_ofReal_im, sub_zero]
    rw [show (2 : ℂ) ^ P = (((2 : ℝ) ^ P : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.div_ofReal]
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  have h2 := Complex.abs_im_le_norm ((((U : ℂ) + (V : ℂ) * Complex.I) / 2 ^ P) -
    Complex.exp ((z : ℝ) : ℂ))
  rw [him] at h2
  rw [abs_div, abs_of_pos (pow_pos (two_pos : (0:ℝ) < 2) P)] at h2
  have h3 : |(V : ℝ)| / 2 ^ P ≤ 4 / 2 ^ P := le_trans h2 h
  have h4 : |(V : ℝ)| ≤ 4 := by
    have h5 := (div_le_div_iff_of_pos_right (pow_pos (two_pos : (0:ℝ) < 2) P)).mp h3
    linarith
  have h6 : ((V.natAbs : ℕ) : ℝ) = |(V : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have h7 : ((V.natAbs : ℕ) : ℝ) ≤ 4 := by rw [h6]; linarith
  exact_mod_cast h7


/-- The complex exponential word on the exact window `[int P, int Z, int 0] ++ tail`. -/
theorem wrd_expW {main : Cmd} {prog : Cmd} {K : ℕ}
    (h : ∀ (m : Cmd) (p : ℕ) (X Y : ℤ), 100 ≤ p →
      ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2 ≤ (32 * 2 ^ p) ^ 2) → WordR m prog
      (fun vs => ∃ rest, vs = .int (p : ℤ) :: .int X :: .int Y :: rest)
      (fun vs out => ∃ rest U V, vs = .int (p : ℤ) :: .int X :: .int Y :: rest ∧
        out = .int U :: .int V :: rest ∧
        ‖((U : ℂ) + (V : ℂ) * Complex.I) / 2 ^ p -
          Complex.exp (((X : ℂ) + (Y : ℂ) * Complex.I) / 2 ^ p)‖ ≤ 4 / (2 : ℝ) ^ p)
      (fun _ => K * (p + 1) ^ K))
    (P : ℕ) (hP : 100 ≤ P) (Z : ℤ) (hZ : (Z : ℝ) ^ 2 ≤ (32 * 2 ^ P) ^ 2)
    (A : List Val) (tail : List Val)
    (hA : A = .int ((P : ℕ) : ℤ) :: .int Z :: .int (0 : ℤ) :: tail) :
    WordR main prog (fun vs => vs = A)
      (fun _ out => ∃ U V : ℤ, out = .int U :: .int V :: tail ∧
        |(U : ℝ) / 2 ^ P - Real.exp ((Z : ℝ) / 2 ^ P)| ≤ 4 / (2 : ℝ) ^ P ∧
        V.natAbs ≤ 4)
      (fun _ => K * (P + 1) ^ K) := by
  have hZ' : ((Z : ℝ) ^ 2 + ((0 : ℤ) : ℝ) ^ 2 ≤ (32 * 2 ^ P) ^ 2) := by
    simpa using hZ
  refine wrd_rel (h main P Z 0 hP hZ') ?_ ?_ le_rfl
  · rw [hA]; exact ⟨tail, rfl⟩
  · intro out hQ
    rcases hQ with ⟨rest', U, V, hvs, hout, hnorm⟩
    have hvs' : (HvdH.Val.int ((P : ℕ) : ℤ) :: .int Z :: .int (0 : ℤ) :: tail : List Val)
        = .int (P : ℤ) :: .int Z :: .int (0 : ℤ) :: rest' := by
      rw [← hA]; exact hvs
    have h1 := (List.cons.inj hvs').2
    have h2 := (List.cons.inj h1).2
    have h3 := (List.cons.inj h2).2
    have hr : rest' = tail := h3.symm
    have hcplx : Complex.exp (((Z : ℂ) + ((0 : ℤ) : ℂ) * Complex.I) / 2 ^ (P : ℕ))
        = ((Real.exp ((Z : ℝ) / 2 ^ P) : ℝ) : ℂ) := by
      have harg : ((Z : ℂ) + ((0 : ℤ) : ℂ) * Complex.I) / 2 ^ (P : ℕ)
          = (((Z : ℝ) / 2 ^ P : ℝ) : ℂ) := by
        push_cast
        ring
      rw [harg, ← Complex.ofReal_exp]
    rw [hcplx] at hnorm
    have h4 := Complex.abs_re_le_norm ((((U : ℂ) + (V : ℂ) * Complex.I) / 2 ^ (P : ℕ)) -
      ((Real.exp ((Z : ℝ) / 2 ^ P) : ℝ) : ℂ))
    have h5 : ((((U : ℂ) + (V : ℂ) * Complex.I) / 2 ^ (P : ℕ)) -
        ((Real.exp ((Z : ℝ) / 2 ^ P) : ℝ) : ℂ)).re
        = (U : ℝ) / 2 ^ P - Real.exp ((Z : ℝ) / 2 ^ P) := by
      rw [Complex.sub_re, Complex.ofReal_re]
      congr 1
      rw [show (2 : ℂ) ^ (P : ℕ) = (((2 : ℝ) ^ P : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.div_ofReal]
      simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [h5] at h4
    have hV4 : V.natAbs ≤ 4 := isz_V_le (z := (Z : ℝ) / 2 ^ P) (by
      have hc := hnorm
      rw [Complex.ofReal_exp ((Z : ℝ) / 2 ^ P)] at hc
      exact hc)
    exact ⟨U, V, by rw [hout, hr], h4.trans hnorm, hV4⟩

/-- Binary operation on an exact window, with an explicit result name. -/
theorem wrd_bin {main prog : Cmd} {P : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ} {C : ℤ → ℤ → ℕ}
    (h : BinOp main prog P f C) (pre post : List Val) (a b Bv : ℤ) (tail : List Val)
    (hpre : pre = .int a :: .int b :: tail) (hpost : post = .int Bv :: tail)
    (hP : P a b) (hBv : f a b = Bv)
    {c : ℕ} (hc : C a b ≤ c) :
    WordR main prog (fun vs => vs = pre) (fun _ out => out = post) (fun _ => c) := by
  subst hpre hpost
  refine wrd_rel h ⟨a, b, tail, rfl, hP⟩ ?_ hc
  intro out hQ
  rcases hQ with ⟨a', b', r', hvs, hout⟩
  obtain ⟨h1, h2⟩ := List.cons.inj hvs
  obtain ⟨ha, hr⟩ := List.cons.inj h2
  rw [hout, ← Val.int.inj h1, ← Val.int.inj ha, ← hr, hBv]

/-- Unary operation on an exact window, with an explicit result name. -/
theorem wrd_un {main prog : Cmd} {P : ℤ → Prop} {f : ℤ → ℤ} {C : ℤ → ℕ}
    (h : UnOp main prog P f C) (pre post : List Val) (a Bv : ℤ) (tail : List Val)
    (hpre : pre = .int a :: tail) (hpost : post = .int Bv :: tail)
    (hP : P a) (hBv : f a = Bv)
    {c : ℕ} (hc : C a ≤ c) :
    WordR main prog (fun vs => vs = pre) (fun _ out => out = post) (fun _ => c) := by
  subst hpre hpost
  refine wrd_rel h ⟨a, tail, rfl, hP⟩ ?_ hc
  intro out hQ
  rcases hQ with ⟨a', r', hvs, hout⟩
  obtain ⟨h1, h2⟩ := List.cons.inj hvs
  rw [hout, ← Val.int.inj h1, ← h2, hBv]

/-! ## Cost bounds (every step of the word costs at most `Cstep`) -/

theorem le_pow (B D : ℕ) (hB : 1 ≤ B) (hD : 1 ≤ D) : B ≤ B ^ D := by
  calc B = B ^ 1 := (pow_one B).symm
    _ ≤ B ^ D := Nat.pow_le_pow_right hB hD

theorem cost_pickroll (KK B D K k S : ℕ) (hB : 100 ≤ B) (hD : 2 ≤ D) (hK : K ≤ KK)
    (hk : k + 1 ≤ 9) (hS : S ≤ 9 * (100 * B + 1000)) :
    K * (k + 1) * (S + 1) ≤ 100000 * KK * B ^ D := by
  have hBD : B ≤ B ^ D := le_pow B D (by omega) (by omega)
  have h1 : K * (k + 1) * (S + 1) ≤ KK * 9 * (9 * (100 * B + 1000) + 1) :=
    calc K * (k + 1) * (S + 1) ≤ KK * 9 * (S + 1) := Nat.mul_le_mul (Nat.mul_le_mul hK hk) le_rfl
      _ ≤ KK * 9 * (9 * (100 * B + 1000) + 1) :=
          Nat.mul_le_mul_left _ (by omega)
  have h2 : 9 * (100 * B + 1000) + 1 ≤ 1000 * B := by omega
  have h3 : KK * 9 * (9 * (100 * B + 1000) + 1) ≤ KK * 9 * (1000 * B) :=
    Nat.mul_le_mul_left _ h2
  have h4 : KK * 9 * (1000 * B) = 9000 * KK * B := by ring
  have h5 : 9000 * KK * B ≤ 100000 * KK * B ^ D := by
    have h6 : 9000 * KK ≤ 100000 * KK := Nat.mul_le_mul_right KK (by norm_num)
    calc 9000 * KK * B = (9000 * KK) * B := by ring
      _ ≤ (100000 * KK) * B := Nat.mul_le_mul_right B h6
      _ ≤ (100000 * KK) * B ^ D := Nat.mul_le_mul_left _ hBD
  linarith [h1, h3, h4, h5]

theorem cost_bin (KK B D K a b : ℕ) (hB : 100 ≤ B) (hD : 2 ≤ D) (hK : K ≤ KK)
    (ha : a ≤ 100 * B + 1000) (hb : b ≤ 100 * B + 1000) :
    K * (a + b) ≤ 100000 * KK * B ^ D := by
  have hBD : B ≤ B ^ D := le_pow B D (by omega) (by omega)
  have h1 : K * (a + b) ≤ KK * (2 * (100 * B + 1000)) :=
    Nat.mul_le_mul hK (by omega)
  have h2 : KK * (2 * (100 * B + 1000)) ≤ KK * (300 * B) :=
    Nat.mul_le_mul_left KK (by omega)
  have h3 : KK * (300 * B) = 300 * KK * B := by ring
  have h5 : 300 * KK * B ≤ 100000 * KK * B ^ D := by
    have h6 : 300 * KK ≤ 100000 * KK := Nat.mul_le_mul_right KK (by norm_num)
    calc 300 * KK * B = (300 * KK) * B := by ring
      _ ≤ (100000 * KK) * B := Nat.mul_le_mul_right B h6
      _ ≤ (100000 * KK) * B ^ D := Nat.mul_le_mul_left _ hBD
  linarith [h1, h2, h3, h5]

theorem cost_bin1 (KK B D K a b : ℕ) (hB : 100 ≤ B) (hD : 2 ≤ D) (hK : K ≤ KK)
    (ha : a ≤ 100 * B + 1000) (hb : b ≤ 100 * B + 1000) :
    K * (a + b + 1) ≤ 100000 * KK * B ^ D := by
  have hBD : B ≤ B ^ D := le_pow B D (by omega) (by omega)
  have h1 : K * (a + b + 1) ≤ KK * (2 * (100 * B + 1000) + 1) :=
    Nat.mul_le_mul hK (by omega)
  have h2 : KK * (2 * (100 * B + 1000) + 1) ≤ KK * (300 * B) :=
    Nat.mul_le_mul_left KK (by omega)
  have h3 : KK * (300 * B) = 300 * KK * B := by ring
  have h5 : 300 * KK * B ≤ 100000 * KK * B ^ D := by
    have h6 : 300 * KK ≤ 100000 * KK := Nat.mul_le_mul_right KK (by norm_num)
    calc 300 * KK * B = (300 * KK) * B := by ring
      _ ≤ (100000 * KK) * B := Nat.mul_le_mul_right B h6
      _ ≤ (100000 * KK) * B ^ D := Nat.mul_le_mul_left _ hBD
  linarith [h1, h2, h3, h5]

theorem cost_mul (KK B D K a b : ℕ) (hB : 100 ≤ B) (hD : 2 ≤ D) (hK : K ≤ KK)
    (ha : a ≤ 100 * B + 1000) (hb : b ≤ 100 * B + 1000) :
    K * a * b ≤ 100000 * KK * B ^ D := by
  have hBB : B * B ≤ B ^ D := by
    calc B * B = B ^ 2 := (pow_two B).symm
      _ ≤ B ^ D := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : K * a * b ≤ KK * (100 * B + 1000) * (100 * B + 1000) :=
    Nat.mul_le_mul (Nat.mul_le_mul hK ha) hb
  have h2 : 100 * B + 1000 ≤ 110 * B := by omega
  have h3 : KK * (100 * B + 1000) * (100 * B + 1000) ≤ KK * (110 * B) * (110 * B) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) h2
  have h4 : KK * (110 * B) * (110 * B) = 12100 * KK * (B * B) := by ring
  have h5 : 12100 * KK * (B * B) ≤ 12100 * KK * B ^ D := Nat.mul_le_mul_left _ hBB
  have h6 : 12100 * KK ≤ 100000 * KK := Nat.mul_le_mul_right KK (by norm_num)
  have h7 : 12100 * KK * B ^ D ≤ 100000 * KK * B ^ D := Nat.mul_le_mul_right _ h6
  linarith [h1, h3, h4, h5, h7]

theorem cost_drop (KK B D K v : ℕ) (hB : 100 ≤ B) (hD : 2 ≤ D) (hK : K ≤ KK)
    (hv : v ≤ 100 * B + 1000) : K * (v + 1) ≤ 100000 * KK * B ^ D := by
  exact cost_bin KK B D K v 1 hB hD hK hv (by omega)

theorem cost_swap (KK B D K a b : ℕ) (hB : 100 ≤ B) (hD : 2 ≤ D) (hK : K ≤ KK)
    (ha : a ≤ 100 * B + 1000) (hb : b ≤ 100 * B + 1000) :
    K * (a + b + 1) ≤ 100000 * KK * B ^ D :=
  cost_bin1 KK B D K a b hB hD hK ha hb

theorem cost_const (KK B D K : ℕ) (hB : 100 ≤ B) (hD : 2 ≤ D) (hK : K ≤ KK) :
    K ≤ 100000 * KK * B ^ D := by
  have h1 : K ≤ 100000 * KK :=
    calc K ≤ KK := hK
      _ ≤ 100000 * KK := Nat.le_mul_of_pos_left KK (by norm_num)
  calc K ≤ 100000 * KK := h1
    _ ≤ 100000 * KK * B ^ D := Nat.le_mul_of_pos_right _ (pow_pos (by omega) D)

theorem cost_word (KK B D Kx P : ℕ) (hB : 100 ≤ B) (hD : 2 ≤ D) (hP : P + 1 ≤ 53 * B)
    (hKx : Kx ≤ D) (hKK : Kx * 53 ^ D ≤ KK) :
    Kx * (P + 1) ^ Kx ≤ 100000 * KK * B ^ D := by
  have hBD : B ^ Kx ≤ B ^ D := Nat.pow_le_pow_right (by omega) hKx
  have h1 : (P + 1) ^ Kx ≤ 53 ^ D * B ^ Kx := by
    calc (P + 1) ^ Kx ≤ (53 * B) ^ Kx := Nat.pow_le_pow_left hP Kx
      _ = 53 ^ Kx * B ^ Kx := Nat.mul_pow 53 B Kx
      _ ≤ 53 ^ D * B ^ Kx := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hKx)
  have h2 : Kx * (P + 1) ^ Kx ≤ Kx * (53 ^ D * B ^ Kx) := Nat.mul_le_mul_left _ h1
  have h3 : Kx * (53 ^ D * B ^ Kx) = (Kx * 53 ^ D) * B ^ Kx := by ring
  have h4 : (Kx * 53 ^ D) * B ^ Kx ≤ KK * B ^ Kx := Nat.mul_le_mul_right _ hKK
  have h5 : KK * B ^ Kx ≤ KK * B ^ D := Nat.mul_le_mul_left KK hBD
  have h6 : KK * B ^ D ≤ 100000 * KK * B ^ D := by
    have h7 : KK * B ^ D ≤ KK * B ^ D * 100000 := Nat.le_mul_of_pos_right _ (by norm_num)
    linarith [h7]
  linarith [h2, h3, h4, h5, h6]

/-- The final assembly of the cost bound. -/
theorem cost_final (KK B D : ℕ) (hB : 1 ≤ B) (hD : 2 ≤ D) :
    50 * (100000 * KK * B ^ D) + 4 * KK ≤
      (10 ^ 8 * (KK + 1) + D + 1) * B ^ (10 ^ 8 * (KK + 1) + D + 1) := by
  have hBD : 1 ≤ B ^ D := one_le_pow₀ hB
  have hBD' : B ^ D ≤ B ^ (10 ^ 8 * (KK + 1) + D + 1) :=
    Nat.pow_le_pow_right hB (by omega)
  have h1 : 50 * (100000 * KK * B ^ D) + 4 * KK
      ≤ (5 * 10 ^ 6 * (KK + 1) + 4 * (KK + 1)) * B ^ D := by
    have e1 : 50 * (100000 * KK * B ^ D) = 5 * 10 ^ 6 * KK * B ^ D := by ring
    rw [e1]
    have h2 : 5 * 10 ^ 6 * KK * B ^ D ≤ 5 * 10 ^ 6 * (KK + 1) * B ^ D :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    have h3 : 4 * KK ≤ 4 * (KK + 1) * B ^ D := by
      calc 4 * KK ≤ 4 * (KK + 1) := Nat.mul_le_mul_left 4 (by omega)
        _ ≤ 4 * (KK + 1) * B ^ D := Nat.le_mul_of_pos_right _ hBD
    linarith [h2, h3]
  have h2 : (5 * 10 ^ 6 * (KK + 1) + 4 * (KK + 1)) * B ^ D
      ≤ (10 ^ 8 * (KK + 1) + D + 1) * B ^ (10 ^ 8 * (KK + 1) + D + 1) := by
    have h3 : 5 * 10 ^ 6 * (KK + 1) + 4 * (KK + 1) ≤ 10 ^ 8 * (KK + 1) + D + 1 := by
      have h4 : 5 * 10 ^ 6 * (KK + 1) + 4 * (KK + 1) ≤ 10 ^ 8 * (KK + 1) := by
        nlinarith
      omega
    exact Nat.mul_le_mul h3 hBD'
  linarith [h1, h2]

/-! ## Auxiliary definitions -/

/-- Sequential composition of a list of programs. -/
def seqs : List Cmd → Cmd
  | [] => .skip
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-- If `|X| ≤ 2^P` then the bit size of `|X|` is at most `P + 1`. -/
theorem natAbsSize_le_of_abs_le_pow (X : ℤ) (P : ℕ) (h : |(X : ℝ)| ≤ (2 : ℝ) ^ P) :
    X.natAbs.size ≤ P + 1 := by
  have h1 : (X.natAbs : ℝ) ≤ (2 : ℝ) ^ P := by
    rw [Nat.cast_natAbs, Int.cast_abs]; exact h
  have h2 : X.natAbs ≤ 2 ^ P := by exact_mod_cast h1
  exact Nat.size_le.mpr (lt_of_le_of_lt h2 (Nat.pow_lt_pow_right (by norm_num) (by omega)))

/-- `(w,0)` lies in the disc when `|w| ≤ 2^p`. -/
theorem inDisc_of_abs_le (p : ℕ) (w : ℤ) (h : |(w : ℝ)| ≤ (2 : ℝ) ^ p) : inDisc p (w, 0) := by
  rw [inDisc]
  have h2 : ((w : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ p) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg (pow_nonneg (zero_le_two : (0:ℝ) ≤ 2) p)]
    exact h
  have h9' : (4 : ℝ) ^ p = ((2 : ℝ) ^ p) ^ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, pow_two]
  have h4 : ((w : ℝ)) ^ 2 ≤ (4 : ℝ) ^ p := by
    calc ((w : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ p) ^ 2 := h2
      _ = (4 : ℝ) ^ p := (h9'.symm)
  have h5 : ((w ^ 2 : ℤ) : ℝ) ≤ ((4 ^ p : ℤ) : ℝ) := by
    push_cast
    exact h4
  have h6 : w ^ 2 ≤ 4 ^ p := by exact_mod_cast h5
  simpa using h6

/-- `2^p ‖fxC p (w,0) - x‖ = |w - 2^p x|`. -/
theorem final_conv (p : ℕ) (w : ℤ) (x : ℝ) :
    (2 : ℝ) ^ p * ‖fxC p (w, 0) - ((x : ℝ) : ℂ)‖ = |(w : ℝ) - (2 : ℝ) ^ p * x| := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ p := pow_pos (two_pos : (0:ℝ) < 2) p
  have h1 : fxC p (w, 0) - ((x : ℝ) : ℂ) = ((((w : ℝ) - (2 : ℝ) ^ p * x) / (2 : ℝ) ^ p : ℝ) : ℂ) := by
    simp only [fxC]
    push_cast
    field_simp
    ring
  rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hpos]
  rw [mul_div_cancel₀ _ (ne_of_gt hpos)]

/-- `isz 0 = 2`. -/
theorem isz_zero : isz ((0 : ℤ)) = 2 := by
  have h1 : ((0:ℤ)).natAbs = 0 := by norm_num
  have h2 : (0:ℕ).size = 0 := by
    apply le_antisymm _ (Nat.zero_le _)
    exact Nat.size_le.mpr (by norm_num)
  simp only [isz, h1, h2]

/-- `vsz (cfxVal (0,0)) = 5`. -/
theorem vsz_cfxVal_zero : vsz (cfxVal ((0:ℤ), (0:ℤ))) = 5 := by
  rw [vsz_cfxVal]
  show isz ((0:ℤ)) + isz ((0:ℤ)) + 1 = 5
  rw [isz_zero]

/-- `vsz (cfxVal (w,0)) = isz w + 3`. -/
theorem vsz_cfxVal_snd_zero (w : ℤ) : vsz (cfxVal (w, (0:ℤ))) = isz w + 3 := by
  rw [vsz_cfxVal]
  show isz w + isz ((0:ℤ)) + 1 = isz w + 3
  rw [isz_zero]

/-- Truncated division of a nonnegative integer by a positive one is nonnegative. -/
theorem tdv_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a.tdiv b := by
  by_contra h
  have h1 : a.tdiv b ≤ -1 := by omega
  have h2 : b * (a.tdiv b) ≤ b * (-1) := mul_le_mul_of_nonneg_left h1 (le_of_lt hb)
  have h3 : a.tmod b ≤ b - 1 := by
    have h4 := Int.tmod_lt_of_pos a hb
    omega
  have h6 : a = a.tmod b + b * (a.tdiv b) := (Int.tmod_add_mul_tdiv a b).symm
  nlinarith [h2, h3, h6, ha]

/-- Size bound for `X = tdiv (u*j) k` when `|u| ≤ 2^M` and `j < k(p+2)`. -/
theorem isz_tdiv_of_bounds (u : ℤ) (j k p M : ℕ) (hk : 1 ≤ k) (hj : j < k * (p + 2))
    (hu : |(u : ℝ)| ≤ (2 : ℝ) ^ M) :
    isz (Int.tdiv (u * (j : ℤ)) (k : ℤ)) ≤ M + p + 8 := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have hjR : (j : ℝ) ≤ (k : ℝ) * ((p : ℝ) + 2) := by
    have h2 : ((j : ℝ)) < ((k * (p + 2) : ℕ) : ℝ) := by exact_mod_cast hj
    have h3 : ((k * (p + 2) : ℕ) : ℝ) = (k : ℝ) * ((p : ℝ) + 2) := by push_cast; ring
    rw [h3] at h2; linarith
  have h1 : |((Int.tdiv (u * (j : ℤ)) (k : ℤ) : ℤ) : ℝ) - (u : ℝ) * (j : ℝ) / (k : ℝ)| ≤ 1 := by
    have h := tdiv_abs_le_one (u * (j : ℤ)) (k : ℤ) hk0
    convert h using 3 <;> push_cast <;> ring
  have h2 : |(u : ℝ) * (j : ℝ) / (k : ℝ)| ≤ (2 : ℝ) ^ M * ((p : ℝ) + 2) := by
    have hjnn : (0 : ℝ) ≤ (j : ℝ) := by positivity
    rw [abs_div, abs_mul, abs_of_nonneg hjnn, abs_of_pos hkR, div_le_iff₀ hkR]
    calc |(u : ℝ)| * (j : ℝ) ≤ (2 : ℝ) ^ M * (j : ℝ) :=
          mul_le_mul_of_nonneg_right hu hjnn
      _ ≤ (2 : ℝ) ^ M * ((k : ℝ) * ((p : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left hjR (pow_nonneg (zero_le_two : (0:ℝ) ≤ 2) M)
      _ = (2 : ℝ) ^ M * ((p : ℝ) + 2) * (k : ℝ) := by ring
  have h3 : |((Int.tdiv (u * (j : ℤ)) (k : ℤ) : ℤ) : ℝ)| ≤ (2 : ℝ) ^ M * ((p : ℝ) + 2) + 1 := by
    have h4 : ((Int.tdiv (u * (j : ℤ)) (k : ℤ) : ℤ) : ℝ)
        = (((Int.tdiv (u * (j : ℤ)) (k : ℤ) : ℤ) : ℝ) - (u : ℝ) * (j : ℝ) / (k : ℝ))
          + (u : ℝ) * (j : ℝ) / (k : ℝ) := by ring
    rw [h4]
    linarith [abs_add_le (((Int.tdiv (u * (j : ℤ)) (k : ℤ) : ℤ) : ℝ) - (u : ℝ) * (j : ℝ) / (k : ℝ))
      ((u : ℝ) * (j : ℝ) / (k : ℝ)), h1, h2]
  have h4 : ((Int.tdiv (u * (j : ℤ)) (k : ℤ)).natAbs : ℝ) ≤ (2 : ℝ) ^ M * ((p : ℝ) + 2) + 1 := by
    rw [Nat.cast_natAbs, Int.cast_abs]; exact h3
  have h5 : (Int.tdiv (u * (j : ℤ)) (k : ℤ)).natAbs ≤ 2 ^ (M + p + 3) := by
    have h6 : ((Int.tdiv (u * (j : ℤ)) (k : ℤ)).natAbs : ℝ) ≤ ((2 ^ (M + p + 3) : ℕ) : ℝ) := by
      push_cast
      have h7 : (1 : ℝ) ≤ (2 : ℝ) ^ M := one_le_pow₀ (by norm_num)
      have h8 : ((p : ℝ) + 3) ≤ (2 : ℝ) ^ (p + 3) := by
        have h9 : (p + 3 : ℕ) < 2 ^ (p + 3) := Nat.lt_two_pow_self
        exact_mod_cast le_of_lt h9
      have h10 : (0 : ℝ) < (2 : ℝ) ^ M := pow_pos (two_pos : (0:ℝ) < 2) M
      have h11 : (2 : ℝ) ^ (M + p + 3) = (2 : ℝ) ^ M * (2 : ℝ) ^ (p + 3) := by
        rw [show M + p + 3 = M + (p + 3) by omega]
        exact pow_add 2 M (p + 3)
      rw [h11]
      nlinarith [h7, h8, h10]
    exact_mod_cast h6
  have h6 : (Int.tdiv (u * (j : ℤ)) (k : ℤ)).natAbs < 2 ^ (M + p + 6) :=
    lt_of_le_of_lt h5 (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have h7 : (Int.tdiv (u * (j : ℤ)) (k : ℤ)).natAbs.size ≤ M + p + 6 := Nat.size_le.mpr h6
  simp only [isz]; omega


/-- `1 / 2^p ≤ 1` in `ℝ`. -/
theorem one_div_two_pow_le_one (p : ℕ) : 1 / (2:ℝ) ^ p ≤ 1 := by
  have hpos : (0:ℝ) < 2 ^ p := pow_pos (two_pos : (0:ℝ) < 2) p
  rw [div_le_iff₀ hpos, one_mul]
  exact one_le_pow₀ (one_le_two : (1:ℝ) ≤ 2)

/-- `|Z|/2^(2p+60) ≤ 3` when `Z/2^(2p+60)` approximates `τ log 2 - πj/k` and the latter is `≤ 2`. -/
theorem abs_div_two_pow_le_three (p j k : ℕ) (Z : ℤ) (τ : ℕ)
    (hz : |(Z : ℝ) / 2 ^ (2 * p + 60) - ((τ : ℝ) * Real.log 2 - Real.pi * j / k)| ≤ 1 / 2 ^ (p + 50))
    (hy : |(τ : ℝ) * Real.log 2 - Real.pi * j / k| ≤ 2) :
    |(Z : ℝ) / 2 ^ (2 * p + 60)| ≤ 3 := by
  have h1 : |(Z : ℝ) / 2 ^ (2 * p + 60)|
      ≤ |(Z : ℝ) / 2 ^ (2 * p + 60) - ((τ : ℝ) * Real.log 2 - Real.pi * j / k)|
        + |(τ : ℝ) * Real.log 2 - Real.pi * j / k| := by
    have h2 : (Z : ℝ) / 2 ^ (2 * p + 60)
        = ((Z : ℝ) / 2 ^ (2 * p + 60) - ((τ : ℝ) * Real.log 2 - Real.pi * j / k))
          + ((τ : ℝ) * Real.log 2 - Real.pi * j / k) := by ring
    calc |(Z : ℝ) / 2 ^ (2 * p + 60)|
        = |((Z : ℝ) / 2 ^ (2 * p + 60) - ((τ : ℝ) * Real.log 2 - Real.pi * j / k))
          + ((τ : ℝ) * Real.log 2 - Real.pi * j / k)| := congrArg abs h2
      _ ≤ |(Z : ℝ) / 2 ^ (2 * p + 60) - ((τ : ℝ) * Real.log 2 - Real.pi * j / k)|
          + |(τ : ℝ) * Real.log 2 - Real.pi * j / k| := abs_add_le _ _
  have h3 : 1 / (2:ℝ) ^ (p + 50) ≤ 1 := one_div_two_pow_le_one (p + 50)
  linarith [h1, hz, hy, h3]

/-- `exp (Z/2^(2p+60)) ≤ 32` when `|Z|/2^(2p+60) ≤ 3`. -/
theorem exp_le_thirtytwo (p : ℕ) (Z : ℤ) (hz : |(Z : ℝ) / 2 ^ (2 * p + 60)| ≤ 3) :
    Real.exp ((Z : ℝ) / 2 ^ (2 * p + 60)) ≤ 32 := by
  have h3 : (Z : ℝ) / 2 ^ (2 * p + 60) ≤ 3 := le_trans (le_abs_self _) hz
  have h4 : Real.exp ((Z : ℝ) / 2 ^ (2 * p + 60)) ≤ Real.exp 3 := Real.exp_le_exp.mpr h3
  have h5 : Real.exp (3:ℝ) ≤ 32 := by
    have h6 : Real.exp (3:ℝ) = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h6]
    calc Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
      _ ≤ 32 := by norm_num
  linarith

/-- Size bound for the real part of the `expc` output: if `U/2^(2p+60)` is within `4/2^(2p+60)` of
`exp (Z/2^(2p+60))` and the latter is `≤ 32`, then `|U| ≤ 2^(2p+66)`. -/
theorem abs_U_le (p : ℕ) (Z U : ℤ)
    (hz : |(Z : ℝ) / 2 ^ (2 * p + 60)| ≤ 3)
    (he32 : Real.exp ((Z : ℝ) / 2 ^ (2 * p + 60)) ≤ 32)
    (hUV : |(U : ℝ) / 2 ^ (2 * p + 60) - Real.exp ((Z : ℝ) / 2 ^ (2 * p + 60))| ≤ 4 / 2 ^ (2 * p + 60)) :
    |(U : ℝ)| ≤ (2 : ℝ) ^ (2 * p + 60 + 6) := by
  have hpos : (0:ℝ) < (2:ℝ) ^ (2 * p + 60) := pow_pos (two_pos : (0:ℝ) < 2) _
  have h3 : |(U : ℝ)| / 2 ^ (2 * p + 60) ≤ 32 + 4 / 2 ^ (2 * p + 60) := by
    have hL : |Real.exp ((Z : ℝ) / 2 ^ (2 * p + 60))| ≤ 32 := by
      rw [abs_of_pos (Real.exp_pos _)]; exact he32
    have h4 : |(U : ℝ) / 2 ^ (2 * p + 60)| ≤
        |(U : ℝ) / 2 ^ (2 * p + 60) - Real.exp ((Z : ℝ) / 2 ^ (2 * p + 60))|
          + |Real.exp ((Z : ℝ) / 2 ^ (2 * p + 60))| := by
      have h5 : (U : ℝ) / 2 ^ (2 * p + 60)
          = ((U : ℝ) / 2 ^ (2 * p + 60) - Real.exp ((Z : ℝ) / 2 ^ (2 * p + 60)))
            + Real.exp ((Z : ℝ) / 2 ^ (2 * p + 60)) := by ring
      calc |(U : ℝ) / 2 ^ (2 * p + 60)|
          = |((U : ℝ) / 2 ^ (2 * p + 60) - Real.exp ((Z : ℝ) / 2 ^ (2 * p + 60)))
            + Real.exp ((Z : ℝ) / 2 ^ (2 * p + 60))| := congrArg abs h5
        _ ≤ |(U : ℝ) / 2 ^ (2 * p + 60) - Real.exp ((Z : ℝ) / 2 ^ (2 * p + 60))|
            + |Real.exp ((Z : ℝ) / 2 ^ (2 * p + 60))| := abs_add_le _ _
    rw [abs_div, abs_of_pos hpos] at h4
    linarith [h4, hUV, hL]
  have h6 : |(U : ℝ)| ≤ 2 ^ (2 * p + 60) * (32 + 4 / 2 ^ (2 * p + 60)) := by
    rw [mul_comm (2 ^ (2 * p + 60)) (32 + 4 / 2 ^ (2 * p + 60))]
    rw [div_le_iff₀ hpos] at h3
    exact h3
  have h9a : (2:ℝ) ^ (2 * p + 60) * (4 / (2:ℝ) ^ (2 * p + 60)) = 4 := by
    have hb : (2:ℝ) ^ (2 * p + 60) ≠ 0 := ne_of_gt hpos
    have h7 : (2:ℝ) ^ (2 * p + 60) * ((2:ℝ) ^ (2 * p + 60))⁻¹ = 1 := mul_inv_cancel₀ hb
    have h8 : 4 / (2:ℝ) ^ (2 * p + 60) = 4 * ((2:ℝ) ^ (2 * p + 60))⁻¹ := div_eq_mul_inv 4 _
    calc (2:ℝ) ^ (2 * p + 60) * (4 / (2:ℝ) ^ (2 * p + 60))
        = (2:ℝ) ^ (2 * p + 60) * (4 * ((2:ℝ) ^ (2 * p + 60))⁻¹) := by rw [h8]
      _ = 4 * ((2:ℝ) ^ (2 * p + 60) * ((2:ℝ) ^ (2 * p + 60))⁻¹) := by ring
      _ = 4 := by rw [h7]; ring
  have h9 : (2:ℝ) ^ (2 * p + 60) * (32 + 4 / (2:ℝ) ^ (2 * p + 60)) = 32 * (2:ℝ) ^ (2 * p + 60) + 4 := by
    rw [mul_add, h9a]
    ring
  have h10 : (1:ℝ) ≤ 2 ^ (2 * p + 60) := one_le_pow₀ (one_le_two : (1:ℝ) ≤ 2)
  have h11 : (2:ℝ) ^ (2 * p + 60 + 6) = (2:ℝ) ^ (2 * p + 60) * 64 := by rw [pow_add]; norm_num
  have h12 : (32:ℝ) * 2 ^ (2 * p + 60) + 4 ≤ (2:ℝ) ^ (2 * p + 60 + 6) := by
    rw [h11]; nlinarith [h10, hpos]
  linarith [h6, h9, h12]

theorem expNegField (hk : HvdH.KernelLib) (hi : HvdH.IntLib) (h : Work.Fx.NumWords hk hi) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p j k : ℕ), 100 ≤ p → 1 ≤ k →
      HvdH.WordR main prog (fun vs => ∃ (rest : List HvdH.Val),
          vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (j : ℤ) :: HvdH.Val.int (k : ℤ) :: rest)
      (fun vs out => ∃ (rest : List HvdH.Val) (w : ℤ × ℤ),
        vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (j : ℤ) :: HvdH.Val.int (k : ℤ) :: rest ∧
        out = HvdH.cfxVal w :: rest ∧ HvdH.inDisc p w ∧
        (2 : ℝ) ^ p * ‖HvdH.fxC p w - ((Real.exp (-(Real.pi * j / k)) : ℝ) : ℂ)‖ < 2)
      (fun _ => K * (p + HvdH.isz j + HvdH.isz k) ^ K) := by
  obtain ⟨piP, Kpi, hpi⟩ := h.pi
  obtain ⟨lgP, Klog, hlg⟩ := h.log2
  obtain ⟨exP, Kexp, hexp⟩ := h.expc
  obtain ⟨addP, Kadd, hadd⟩ := hi.add
  obtain ⟨subP, Ksub, hsub⟩ := hi.sub
  obtain ⟨mulP, Kmul, hmul⟩ := hi.mulS
  obtain ⟨tdivP, Ktdiv, htdiv⟩ := hi.tdiv
  obtain ⟨ltP, Klt, hlt⟩ := hi.lt
  obtain ⟨powP, Kpow, hpow⟩ := hi.pow2
  obtain ⟨pickP, Kpick, hpick⟩ := hk.pick
  obtain ⟨rollP, Kroll, hroll⟩ := hk.roll
  obtain ⟨swP, Ksw, hsw⟩ := hk.swap
  obtain ⟨dropP, Kdrop, hdrop⟩ := hk.drop
  obtain ⟨consP, Kcons, hcons⟩ := hk.consV
  obtain ⟨pushP, Kpush, hpush⟩ := hk.pushVal
  obtain ⟨izC, Kiz, hiz⟩ := hk.ifZero
  set SS : ℕ := Kpi + Klog + Kexp + Kpick + Kroll + Ksw + Kdrop + Kcons + Kpush + Kiz +
    Kadd + Ksub + Kmul + Ktdiv + Klt + Kpow with hSS
  set Dg : ℕ := max Kpi (max Klog (max Kexp 2)) with hDg
  set KK : ℕ := 53 ^ (Dg + 1) * SS with hKK
  have hDg2 : 2 ≤ Dg := by simp only [hDg]; omega
  have hDgKpi : Kpi ≤ Dg := by simp only [hDg]; omega
  have hDgKlog : Klog ≤ Dg := by simp only [hDg]; omega
  have hDgKexp : Kexp ≤ Dg := by simp only [hDg]; omega
  have leKK : ∀ {x : ℕ}, x ≤ SS → x ≤ KK := by
    intro x hx
    have h2 : SS ≤ 53 ^ (Dg + 1) * SS := Nat.le_mul_of_pos_left SS (pow_pos (by norm_num : (0:ℕ) < 53) _)
    rw [hKK]; exact le_trans hx h2
  have leKK53 : ∀ {x : ℕ}, x ≤ SS → x * 53 ^ Dg ≤ KK := by
    intro x hx
    have h2 : 53 ^ Dg ≤ 53 ^ (Dg + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc x * 53 ^ Dg ≤ SS * 53 ^ (Dg + 1) := Nat.mul_le_mul hx h2
      _ = 53 ^ (Dg + 1) * SS := by ring
      _ = KK := hKK.symm
  have hKpi : Kpi ≤ KK := leKK (by simp only [hSS]; omega)
  have hKlog : Klog ≤ KK := leKK (by simp only [hSS]; omega)
  have hKexp : Kexp ≤ KK := leKK (by simp only [hSS]; omega)
  have hKpick : Kpick ≤ KK := leKK (by simp only [hSS]; omega)
  have hKroll : Kroll ≤ KK := leKK (by simp only [hSS]; omega)
  have hKsw : Ksw ≤ KK := leKK (by simp only [hSS]; omega)
  have hKdrop : Kdrop ≤ KK := leKK (by simp only [hSS]; omega)
  have hKcons : Kcons ≤ KK := leKK (by simp only [hSS]; omega)
  have hKpush : Kpush ≤ KK := leKK (by simp only [hSS]; omega)
  have hKiz : Kiz ≤ KK := leKK (by simp only [hSS]; omega)
  have hKadd : Kadd ≤ KK := leKK (by simp only [hSS]; omega)
  have hKsub : Ksub ≤ KK := leKK (by simp only [hSS]; omega)
  have hKmul : Kmul ≤ KK := leKK (by simp only [hSS]; omega)
  have hKtdiv : Ktdiv ≤ KK := leKK (by simp only [hSS]; omega)
  have hKlt : Klt ≤ KK := leKK (by simp only [hSS]; omega)
  have hKpow : Kpow ≤ KK := leKK (by simp only [hSS]; omega)
  have hKpi53 : Kpi * 53 ^ Dg ≤ KK := leKK53 (by simp only [hSS]; omega)
  have hKlog53 : Klog * 53 ^ Dg ≤ KK := leKK53 (by simp only [hSS]; omega)
  have hKexp53 : Kexp * 53 ^ Dg ≤ KK := leKK53 (by simp only [hSS]; omega)
  let flagQ : Cmd := seqs [pickP 0, pushP (HvdH.Val.int (2 : ℤ)), addP, pickP 3, mulP, pickP 2, ltP]
  let zeroQ : Cmd := seqs [dropP, dropP, dropP, pushP (cfxVal ((0 : ℤ), (0 : ℤ)))]
  let segA : Cmd := seqs [pickP 0, pickP 0, addP, pushP (HvdH.Val.int (60 : ℤ)), addP, pickP 0, pickP 0]
  let segB : Cmd := seqs [rollP 4, rollP 1, mulP, rollP 4, swP, tdivP, pickP 0, rollP 3]
  let segC : Cmd := seqs [pickP 0, rollP 2, tdivP, pickP 0, rollP 2, mulP, rollP 2, swP, subP,
    pushP (HvdH.Val.int (0 : ℤ)), swP, rollP 3]
  let segD : Cmd := seqs [rollP 2, pushP (HvdH.Val.int (60 : ℤ)), addP, rollP 3, addP, powP, swP, tdivP,
    pushP (HvdH.Val.int (0 : ℤ)), swP, consP, rollP 1, dropP]
  let p1 : Cmd := .seq segA piP
  let p2 : Cmd := .seq segB lgP
  let p3 : Cmd := .seq segC exP
  let mainQ : Cmd := .seq p1 (.seq p2 (.seq p3 segD))
  let q1 : Cmd := .seq p2 (.seq p3 segD)
  let q2 : Cmd := .seq p3 segD
  let prog : Cmd := .seq flagQ (izC zeroQ mainQ)
  refine ⟨prog, 10 ^ 8 * (KK + 1) + Dg + 1, ?_⟩
  intro main p j k hp hk1
  set B : ℕ := p + isz (j : ℤ) + isz (k : ℤ) with hBdef
  have hjB : isz ((j:ℤ)) ≤ B := by simp only [hBdef]; omega
  have hkB : isz ((k:ℤ)) ≤ B := by simp only [hBdef]; omega
  have hB100 : 100 ≤ B := by
    have h1 : 2 ≤ isz ((j:ℤ)) := by simp only [isz]; omega
    have h2 : 2 ≤ isz ((k:ℤ)) := by simp only [isz]; omega
    simp only [hBdef]; omega
  have hsz2 : (2:ℕ).size = 2 := by
    have h1 : (2:ℕ).size ≤ 2 := Nat.size_le.mpr (by norm_num)
    have h2 : ¬ (2:ℕ).size ≤ 1 := by
      intro hh; exact absurd (Nat.size_le.mp hh) (by norm_num)
    omega
  have hpB : p ≤ B := by simp only [hBdef]; omega
  set Cstep : ℕ := 100000 * KK * B ^ Dg with hCstep
  intro vs hpre s R0 hR
  rcases hpre with ⟨rest, hvs⟩
  have hisz0 : isz ((0:ℤ)) = 2 := by
    have h1 : ((0:ℤ)).natAbs = 0 := by norm_num
    have h2 : (0:ℕ).size = 0 := by
      apply le_antisymm _ (Nat.zero_le _)
      exact Nat.size_le.mpr (by norm_num)
    simp only [isz, h1, h2]
  have hisz2 : isz ((2:ℤ)) = 4 := by
    have h : ((2:ℤ)).natAbs = 2 := by norm_num
    simp only [isz, h, hsz2]
  have hisz60 : isz ((60:ℤ)) ≤ 8 := by
    have h : ((60:ℤ)).natAbs = 60 := by norm_num
    have h2 : (60:ℕ).size ≤ 6 := Nat.size_le.mpr (by norm_num)
    simp only [isz, h]; omega
  have hMp : isz ((p:ℤ)) ≤ p + 2 := by
    have hp : ((p:ℤ)).natAbs = p := Int.natAbs_natCast p
    have h2 : p.size ≤ p := Nat.size_le.mpr (Nat.lt_two_pow_self)
    simp only [isz, hp]; omega
  have hMj : isz ((j:ℤ)) ≤ B := by simp only [hBdef]; omega
  have hMk : isz ((k:ℤ)) ≤ B := by simp only [hBdef]; omega
  have hM2p : isz ((2:ℤ) + (p:ℤ)) ≤ p + 5 := by
    have h := isz_add_le (2:ℤ) (p:ℤ)
    have h4 : max (isz (2:ℤ)) (isz (p:ℤ)) ≤ max 4 (p + 2) :=
      max_le_max (le_of_eq hisz2) hMp
    have h5 : max 4 (p + 2) = p + 2 := max_eq_right (by omega)
    omega
  have hMPp : isz ((p:ℤ) + (p:ℤ)) ≤ p + 3 := by
    have h := isz_add_le (p:ℤ) (p:ℤ)
    rw [max_self] at h
    omega
  have hMPv : isz ((60:ℤ) + ((p:ℤ) + (p:ℤ))) ≤ p + 10 := by
    have h := isz_add_le (60:ℤ) ((p:ℤ) + (p:ℤ))
    have h4 : max (isz (60:ℤ)) (isz ((p:ℤ) + (p:ℤ))) ≤ max 8 (p + 3) :=
      max_le_max hisz60 hMPp
    have h5 : max 8 (p + 3) = p + 3 := max_eq_right (by omega)
    omega
  have hMcfx : vsz (cfxVal ((0:ℤ), (0:ℤ))) ≤ 8 := by
    rw [vsz_cfxVal, hisz0]; norm_num

  -- flag segment
  let F0 : List Val := .int ((p : ℤ)) :: .int ((j : ℤ)) :: .int ((k : ℤ)) :: rest
  let F1 : List Val := .int ((p : ℤ)) :: .int ((p : ℤ)) :: .int ((j : ℤ)) :: .int ((k : ℤ)) :: rest
  let F2 : List Val := .int ((2 : ℤ)) :: .int ((p : ℤ)) :: .int ((p : ℤ)) :: .int ((j : ℤ)) :: .int ((k : ℤ)) :: rest
  let F3 : List Val := .int (((2 : ℤ) + (p : ℤ))) :: .int ((p : ℤ)) :: .int ((j : ℤ)) :: .int ((k : ℤ)) :: rest
  let F4 : List Val := .int ((k : ℤ)) :: .int (((2 : ℤ) + (p : ℤ))) :: .int ((p : ℤ)) :: .int ((j : ℤ)) :: .int ((k : ℤ)) :: rest
  let F5 : List Val := .int (((k : ℤ) * ((2 : ℤ) + (p : ℤ)))) :: .int ((p : ℤ)) :: .int ((j : ℤ)) :: .int ((k : ℤ)) :: rest
  let F6 : List Val := .int ((j : ℤ)) :: .int (((k : ℤ) * ((2 : ℤ) + (p : ℤ)))) :: .int ((p : ℤ)) :: .int ((j : ℤ)) :: .int ((k : ℤ)) :: rest
  let fv : ℤ := if (j : ℤ) < (k : ℤ) * ((2 : ℤ) + (p : ℤ)) then 1 else 0
  let F7 : List Val := .int (fv) :: .int ((p : ℤ)) :: .int ((j : ℤ)) :: .int ((k : ℤ)) :: rest
  have hfvsmall : isz fv ≤ 100 * B + 1000 := by
    simp only [fv]; split <;> norm_num [isz]
  have hFk2 : isz ((k : ℤ) * ((2 : ℤ) + (p : ℤ))) ≤ 100 * B + 1000 := by
    have h := isz_mul_le (k : ℤ) ((2 : ℤ) + (p : ℤ)); omega
  have t0 : WordR main (pickP 0) (fun vs => vs = F0) (fun _ out => out = F1) (fun _ => Cstep) := by
    refine wrd_pick (hpick main) 0 F0 (HvdH.Val.int (p : ℤ)) rfl (by simp only [F0]; simp) ?_
    exact cost_pickroll KK B Dg Kpick 0 _ hB100 hDg2 hKpick (by norm_num) (by simp only [F0, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int] <;> omega)
  have t1 : WordR main (pushP (HvdH.Val.int (2 : ℤ))) (fun vs => vs = F1) (fun _ out => out = F2) (fun _ => Cstep) := by
    refine wrd_rel (hpush main (HvdH.Val.int (2:ℤ))) trivial (fun out h => h) ?_
    exact cost_drop KK B Dg Kpush (vsz (HvdH.Val.int (2:ℤ))) hB100 hDg2 hKpush (by rw [vsz_int]; omega)
  have t2 : WordR main addP (fun vs => vs = F2) (fun _ out => out = F3) (fun _ => Cstep) :=
    wrd_bin (hadd main) F2 F3 ((2 : ℤ)) ((p : ℤ)) (((2 : ℤ) + (p : ℤ))) (.int ((p : ℤ)) :: .int ((j : ℤ)) :: .int ((k : ℤ))  :: rest) rfl rfl trivial rfl (cost_bin KK B Dg Kadd (isz (2:ℤ)) (isz (p:ℤ)) hB100 hDg2 hKadd (by omega) (by omega))
  have t3 : WordR main (pickP 3) (fun vs => vs = F3) (fun _ out => out = F4) (fun _ => Cstep) :=
    wrd_pick (hpick main) 3 F3 (F3.getD 3 .nil) rfl (by simp only [F3]; simp)
      (cost_pickroll KK B Dg Kpick 3 _ hB100 hDg2 hKpick (by norm_num) (by simp only [F3, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int] <;> omega))
  have t5 : WordR main (pickP 2) (fun vs => vs = F5) (fun _ out => out = F6) (fun _ => Cstep) :=
    wrd_pick (hpick main) 2 F5 (F5.getD 2 .nil) rfl (by simp only [F5]; simp)
      (cost_pickroll KK B Dg Kpick 2 _ hB100 hDg2 hKpick (by norm_num) (by simp only [F5, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int] <;> omega))
  have t6 : WordR main ltP (fun vs => vs = F6) (fun _ out => out = F7) (fun _ => Cstep) :=
    wrd_bin (hlt main) F6 F7 ((j:ℤ)) (((k:ℤ) * ((2:ℤ) + (p:ℤ)))) (fv) (.int ((p : ℤ)) :: .int ((j : ℤ)) :: .int ((k : ℤ)) :: rest) rfl rfl trivial rfl
      (cost_bin KK B Dg Klt (isz (j:ℤ)) (isz ((k:ℤ) * ((2:ℤ) + (p:ℤ)))) hB100 hDg2 hKlt (by omega) (by omega))
  have t4 : WordR main mulP (fun vs => vs = F4) (fun _ out => out = F5) (fun _ => Cstep) :=
    wrd_bin (hmul main) F4 F5 ((k:ℤ)) (((2:ℤ) + (p:ℤ))) (((k:ℤ) * ((2:ℤ) + (p:ℤ)))) (.int ((p : ℤ)) :: .int ((j : ℤ)) :: .int ((k : ℤ)) :: rest) rfl rfl trivial rfl
      (cost_mul KK B Dg Kmul (isz (k:ℤ)) (isz ((2:ℤ) + (p:ℤ))) hB100 hDg2 hKmul (by omega) (by omega))
  have hflag : WordR main flagQ (fun vs => vs = F0) (fun _ out => out = F7) (fun _ => 7 * Cstep) := by
    have c5 := wrd_seq2 t5 t6
    have c4 := wrd_seq2 t4 c5
    have c3 := wrd_seq2 t3 c4
    have c2 := wrd_seq2 t2 c3
    have c1 := wrd_seq2 t1 c2
    have c0 := wrd_seq2 t0 c1
    exact wrd_conseq hk c0 (fun _ h => h) (fun _ _ _ h => h) (fun _ _ => by beta_reduce; omega)
  -- zero branch
  have hzero : fv = 0 → WordR main zeroQ (fun vs => vs = F0) (fun _ out => out = cfxVal ((0:ℤ),(0:ℤ)) :: rest) (fun _ => 4 * Cstep) := by
    intro _
    have z0 : WordR main dropP (fun vs => vs = F0) (fun _ out => out = .int (j:ℤ) :: .int (k:ℤ) :: rest) (fun _ => Cstep) :=
      wrd_drop (hdrop main) (HvdH.Val.int (p:ℤ)) (HvdH.Val.int (j:ℤ) :: .int (k:ℤ) :: rest) (cost_drop KK B Dg Kdrop (vsz (HvdH.Val.int (p:ℤ))) hB100 hDg2 hKdrop (by rw [vsz_int]; omega))
    have z1 : WordR main dropP (fun vs => vs = .int (j:ℤ) :: .int (k:ℤ) :: rest) (fun _ out => out = .int (k:ℤ) :: rest) (fun _ => Cstep) :=
      wrd_drop (hdrop main) (HvdH.Val.int (j:ℤ)) (HvdH.Val.int (k:ℤ) :: rest) (cost_drop KK B Dg Kdrop (vsz (HvdH.Val.int (j:ℤ))) hB100 hDg2 hKdrop (by rw [vsz_int]; omega))
    have z2 : WordR main dropP (fun vs => vs = .int (k:ℤ) :: rest) (fun _ out => out = rest) (fun _ => Cstep) :=
      wrd_drop (hdrop main) (HvdH.Val.int (k:ℤ)) rest (cost_drop KK B Dg Kdrop (vsz (HvdH.Val.int (k:ℤ))) hB100 hDg2 hKdrop (by rw [vsz_int]; omega))
    have z3 : WordR main (pushP (cfxVal ((0:ℤ),(0:ℤ)))) (fun vs => vs = rest) (fun _ out => out = cfxVal ((0:ℤ),(0:ℤ)) :: rest) (fun _ => Cstep) := by
      refine wrd_rel (hpush main (cfxVal ((0:ℤ),(0:ℤ)))) trivial (fun out h => h) ?_
      exact cost_drop KK B Dg Kpush (vsz (cfxVal ((0:ℤ),(0:ℤ)))) hB100 hDg2 hKpush (by rw [vsz_cfxVal_zero]; omega)
    have cz2 := wrd_seq2 z2 z3
    have cz1 := wrd_seq2 z1 cz2
    have cz0 := wrd_seq2 z0 cz1
    exact wrd_conseq hk cz0 (fun _ h => h) (fun _ _ _ h => h) (fun _ _ => by beta_reduce; omega)

  -- main branch
  have hmain : fv ≠ 0 → WordR main mainQ (fun vs => vs = F0)
      (fun _ out => ∃ (w : ℤ × ℤ), out = cfxVal w :: rest ∧ inDisc p w ∧
        (2 : ℝ) ^ p * ‖fxC p w - ((Real.exp (-(Real.pi * j / k)) : ℝ) : ℂ)‖ < 2)
      (fun _ => 43 * Cstep) := by
    intro hf0
    have hjlt : j < k * (p + 2) := by
      by_contra hcon
      have h2 : k * (p + 2) ≤ j := by omega
      have h3 : ((k * (p + 2) : ℕ) : ℤ) = (k : ℤ) * ((2 : ℤ) + (p : ℤ)) := by push_cast; ring
      have h1 : (j : ℤ) ≥ (k : ℤ) * ((2 : ℤ) + (p : ℤ)) := by rw [← h3]; exact_mod_cast h2
      have h4 : fv = 0 := by simp only [fv, if_neg (not_lt.mpr h1)]
      exact hf0 h4
    let Pn : ℕ := 2 * p + 60
    have hPn : 100 ≤ Pn := by simp only [Pn]; omega
    let base : ℤ := (60 : ℤ) + ((p : ℤ) + (p : ℤ))
    have hbase : base = ((Pn : ℕ) : ℤ) := by simp only [base, Pn]; push_cast; ring
    let A0 : List Val := .int ((p : ℤ)) :: .int ((j : ℤ)) :: .int ((k : ℤ)) :: rest
    let A1 : List Val := .int ((p : ℤ)) :: .int ((p : ℤ)) :: .int ((j : ℤ)) :: .int ((k : ℤ)) :: rest
    let A2 : List Val := .int ((p : ℤ)) :: .int ((p : ℤ)) :: .int ((p : ℤ)) :: .int ((j : ℤ)) :: .int ((k : ℤ)) :: rest
    let A3 : List Val := .int (((p : ℤ) + (p : ℤ))) :: .int ((p : ℤ)) :: .int ((j : ℤ)) :: .int ((k : ℤ)) :: rest
    let A4 : List Val := .int ((60 : ℤ)) :: .int (((p : ℤ) + (p : ℤ))) :: .int ((p : ℤ)) :: .int ((j : ℤ)) :: .int ((k : ℤ)) :: rest
    let A5 : List Val := .int (base) :: .int ((p : ℤ)) :: .int ((j : ℤ)) :: .int ((k : ℤ)) :: rest
    let A6 : List Val := .int (base) :: .int (base) :: .int ((p : ℤ)) :: .int ((j : ℤ)) :: .int ((k : ℤ)) :: rest
    let A7 : List Val := .int (base) :: .int (base) :: .int (base) :: .int ((p : ℤ)) :: .int ((j : ℤ)) :: .int ((k : ℤ)) :: rest
    have s0 : WordR main (pickP 0) (fun vs => vs = A0) (fun _ out => out = A1) (fun _ => Cstep) := by
      refine wrd_pick (hpick main) 0 A0 (A0.getD 0 .nil) rfl (by simp only [A0]; simp) ?_
      exact cost_pickroll KK B Dg Kpick 0 _ hB100 hDg2 hKpick (by norm_num) (by simp only [A0, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int, base] <;> omega)
    have s1 : WordR main (pickP 0) (fun vs => vs = A1) (fun _ out => out = A2) (fun _ => Cstep) := by
      refine wrd_pick (hpick main) 0 A1 (A1.getD 0 .nil) rfl (by simp only [A1]; simp) ?_
      exact cost_pickroll KK B Dg Kpick 0 _ hB100 hDg2 hKpick (by norm_num) (by simp only [A1, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int, base] <;> omega)
    have s2 : WordR main addP (fun vs => vs = A2) (fun _ out => out = A3) (fun _ => Cstep) :=
      wrd_bin (hadd main) A2 A3 ((p : ℤ)) ((p : ℤ)) (((p : ℤ) + (p : ℤ))) (.int ((p : ℤ)) :: .int ((j : ℤ)) :: .int ((k : ℤ))  :: rest) rfl rfl trivial rfl (cost_bin KK B Dg Kadd (isz (p : ℤ)) (isz (p : ℤ)) hB100 hDg2 hKadd (by omega) (by omega))
    have s3 : WordR main (pushP (HvdH.Val.int ((60 : ℤ)))) (fun vs => vs = A3) (fun _ out => out = A4) (fun _ => Cstep) := by
      refine wrd_rel (hpush main (HvdH.Val.int ((60 : ℤ)))) trivial (fun out h => h) ?_
      exact cost_drop KK B Dg Kpush (vsz (HvdH.Val.int ((60 : ℤ)))) hB100 hDg2 hKpush (by rw [vsz_int]; omega)
    have s4 : WordR main addP (fun vs => vs = A4) (fun _ out => out = A5) (fun _ => Cstep) :=
      wrd_bin (hadd main) A4 A5 ((60 : ℤ)) (((p : ℤ) + (p : ℤ))) (base) (.int ((p : ℤ)) :: .int ((j : ℤ)) :: .int ((k : ℤ))  :: rest) rfl rfl trivial rfl (cost_bin KK B Dg Kadd (isz (60 : ℤ)) (isz ((p : ℤ) + (p : ℤ))) hB100 hDg2 hKadd (by omega) (by omega))
    have s5 : WordR main (pickP 0) (fun vs => vs = A5) (fun _ out => out = A6) (fun _ => Cstep) := by
      refine wrd_pick (hpick main) 0 A5 (A5.getD 0 .nil) rfl (by simp only [A5]; simp) ?_
      exact cost_pickroll KK B Dg Kpick 0 _ hB100 hDg2 hKpick (by norm_num) (by simp only [A5, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int, base] <;> omega)
    have s6 : WordR main (pickP 0) (fun vs => vs = A6) (fun _ out => out = A7) (fun _ => Cstep) := by
      refine wrd_pick (hpick main) 0 A6 (A6.getD 0 .nil) rfl (by simp only [A6]; simp) ?_
      exact cost_pickroll KK B Dg Kpick 0 _ hB100 hDg2 hKpick (by norm_num) (by simp only [A6, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int, base] <;> omega)
    have hsegA : WordR main segA (fun vs => vs = A0) (fun _ out => out = A7) (fun _ => 7 * Cstep) := by
      have c6 := s6
      have c5 := wrd_seq2 s5 c6
      have c4 := wrd_seq2 s4 c5
      have c3 := wrd_seq2 s3 c4
      have c2 := wrd_seq2 s2 c3
      have c1 := wrd_seq2 s1 c2
      have c0 := wrd_seq2 s0 c1
      exact wrd_conseq hk c0 (fun _ h => h) (fun _ _ _ h => h) (fun _ _ => by beta_reduce; omega)
    have hpiFun : ∀ mid, mid = A7 → WordR main piP (fun vs => vs = mid)
        (fun _ out => ∃ u : ℤ, |(u : ℝ) - 2 ^ Pn * Real.pi| ≤ 1 ∧ out = .int u :: A6)
        (fun _ => Cstep) := by
      intro mid hmid
      rw [hmid]
      have hw : WordR main piP (fun vs => vs = A7)
          (fun _ out => ∃ u : ℤ, |(u : ℝ) - 2 ^ Pn * Real.pi| ≤ 1 ∧ out = .int u :: A6)
          (fun _ => Kpi * (Pn + 1) ^ Kpi) :=
        wrd_piW hpi Pn hPn A7 A6 (by simp only [A7, A6]; rw [hbase])
      have hc : Kpi * (Pn + 1) ^ Kpi ≤ Cstep := by
        have hP : Pn + 1 ≤ 53 * B := by simp only [Pn]; omega
        exact cost_word KK B Dg Kpi Pn hB100 hDg2 hP hDgKpi hKpi53
      exact wrd_conseq hk hw (fun _ h => h) (fun _ _ _ h => h) (fun _ _ => hc)
    have H1 : WordR main p1 (fun vs => vs = A0)
        (fun _ out => ∃ u : ℤ, |(u : ℝ) - 2 ^ Pn * Real.pi| ≤ 1 ∧ out = .int u :: A6)
        (fun _ => 8 * Cstep) := by
      have h := wrd_seq_exi hsegA hpiFun
      exact wrd_conseq hk h (fun _ hh => hh) (fun _ _ _ hh => hh) (fun _ _ => by beta_reduce; omega)

    have cont1 : ∀ mid, (∃ u : ℤ, |(u : ℝ) - 2 ^ Pn * Real.pi| ≤ 1 ∧ mid = .int u :: A6) →
        WordR main q1 (fun vs => vs = mid)
          (fun _ out => ∃ (w : ℤ × ℤ), out = cfxVal w :: rest ∧ inDisc p w ∧
            (2 : ℝ) ^ p * ‖fxC p w - ((Real.exp (-(Real.pi * j / k)) : ℝ) : ℂ)‖ < 2)
          (fun _ => 35 * Cstep) := by
      intro mid hmid
      rcases hmid with ⟨u, hu, hm⟩
      rw [hm] at *
      have hu3 : |(u : ℝ)| ≤ (2 : ℝ) ^ (Pn + 3) := by
        have h4 := abs_le.mp hu
        have hR : (2:ℝ)^(Pn+3) = (2:ℝ)^Pn * 8 := by rw [pow_add]; norm_num
        have h1 : (1:ℝ) ≤ (2:ℝ) ^ Pn := one_le_pow₀ (by norm_num)
        have hpos : (0:ℝ) < (2:ℝ) ^ Pn := pow_pos (two_pos : (0:ℝ) < 2) Pn
        have hpi : (3:ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
        rw [abs_le, hR]
        constructor
        · nlinarith [h4.1, hpi, h1, hpos]
        · nlinarith [h4.2, Real.pi_lt_d6, h1, hpos]
      have huN : u.natAbs ≤ 2 ^ (Pn + 3) := by
        have h6 : ((u.natAbs : ℕ) : ℝ) = |(u : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
        have h7 : ((u.natAbs : ℕ) : ℝ) ≤ ((2 ^ (Pn+3) : ℕ) : ℝ) := by
          rw [h6]; push_cast; linarith
        exact_mod_cast h7
      have hMu6 : isz u ≤ Pn + 6 := by
        have h9 : u.natAbs.size ≤ Pn + 4 :=
          Nat.size_le.mpr (lt_of_le_of_lt huN (Nat.pow_lt_pow_right (by norm_num) (by omega)))
        simp only [isz]; omega
      have hMu : isz u ≤ 100 * B + 1000 := by
        have h10 : Pn + 6 ≤ 100 * B + 1000 := by simp only [Pn]; omega
        omega
      let X : ℤ := Int.tdiv (u * (j : ℤ)) (k : ℤ)
      have hMXt : isz X ≤ Pn + p + 12 := by
        have h := isz_tdiv_of_bounds u j k p (Pn+3) hk1 hjlt hu3
        have h2 : (Pn + 3) + p + 8 ≤ Pn + p + 12 := by omega
        exact le_trans h h2
      have hMX : isz X ≤ 100 * B + 1000 := by
        have h2 : Pn + p + 12 ≤ 100 * B + 1000 := by simp only [Pn]; omega
        omega
      have hMutj : isz (u * (j : ℤ)) ≤ 100 * B + 1000 := by
        have h := isz_mul_le u (j : ℤ)
        have h2 : Pn + 6 + B ≤ 100 * B + 1000 := by simp only [Pn]; omega
        omega
      let A8 : List Val := .int (u) :: .int (base) :: .int (base) :: .int ((p : ℤ)) :: .int ((j : ℤ)) :: .int ((k : ℤ)) :: rest
      let A9 : List Val := .int ((j : ℤ)) :: .int (u) :: .int (base) :: .int (base) :: .int ((p : ℤ)) :: .int ((k : ℤ)) :: rest
      let A10 : List Val := .int (u) :: .int ((j : ℤ)) :: .int (base) :: .int (base) :: .int ((p : ℤ)) :: .int ((k : ℤ)) :: rest
      let A11 : List Val := .int ((u * (j : ℤ))) :: .int (base) :: .int (base) :: .int ((p : ℤ)) :: .int ((k : ℤ)) :: rest
      let A12 : List Val := .int ((k : ℤ)) :: .int ((u * (j : ℤ))) :: .int (base) :: .int (base) :: .int ((p : ℤ)) :: rest
      let A13 : List Val := .int ((u * (j : ℤ))) :: .int ((k : ℤ)) :: .int (base) :: .int (base) :: .int ((p : ℤ)) :: rest
      let A14 : List Val := .int (X) :: .int (base) :: .int (base) :: .int ((p : ℤ)) :: rest
      let A15 : List Val := .int (X) :: .int (X) :: .int (base) :: .int (base) :: .int ((p : ℤ)) :: rest
      let A16 : List Val := .int (base) :: .int (X) :: .int (X) :: .int (base) :: .int ((p : ℤ)) :: rest
      have s7 : WordR main (rollP 4) (fun vs => vs = A8) (fun _ out => out = A9) (fun _ => Cstep) := by
        refine wrd_roll (hroll main) 4 A8 (A8.getD 4 .nil) rfl (by simp only [A8]; simp) ?_
        exact cost_pickroll KK B Dg Kroll 4 _ hB100 hDg2 hKroll (by norm_num) (by simp only [A8, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int, base] <;> omega)
      have s8 : WordR main (rollP 1) (fun vs => vs = A9) (fun _ out => out = A10) (fun _ => Cstep) := by
        refine wrd_roll (hroll main) 1 A9 (A9.getD 1 .nil) rfl (by simp only [A9]; simp) ?_
        exact cost_pickroll KK B Dg Kroll 1 _ hB100 hDg2 hKroll (by norm_num) (by simp only [A9, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int, base] <;> omega)
      have s9 : WordR main mulP (fun vs => vs = A10) (fun _ out => out = A11) (fun _ => Cstep) :=
        wrd_bin (hmul main) A10 A11 (u) ((j : ℤ)) ((u * (j : ℤ))) (.int (base) :: .int (base) :: .int ((p : ℤ)) :: .int ((k : ℤ))  :: rest) rfl rfl trivial rfl (cost_mul KK B Dg Kmul (isz u) (isz (j : ℤ)) hB100 hDg2 hKmul (by omega) (by omega))
      have s10 : WordR main (rollP 4) (fun vs => vs = A11) (fun _ out => out = A12) (fun _ => Cstep) := by
        refine wrd_roll (hroll main) 4 A11 (A11.getD 4 .nil) rfl (by simp only [A11]; simp) ?_
        exact cost_pickroll KK B Dg Kroll 4 _ hB100 hDg2 hKroll (by norm_num) (by simp only [A11, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int, base] <;> omega)
      have s11 : WordR main swP (fun vs => vs = A12) (fun _ out => out = A13) (fun _ => Cstep) :=
        wrd_swap (hsw main) (HvdH.Val.int (k : ℤ)) (HvdH.Val.int (u * (j : ℤ)))
          (HvdH.Val.int (base) :: .int (base) :: .int ((p : ℤ)) :: rest)
          (cost_swap KK B Dg Ksw (vsz (HvdH.Val.int (k : ℤ))) (vsz (HvdH.Val.int (u * (j : ℤ)))) hB100 hDg2 hKsw (by rw [vsz_int]; omega) (by rw [vsz_int]; omega))
      have s12 : WordR main tdivP (fun vs => vs = A13) (fun _ out => out = A14) (fun _ => Cstep) :=
        wrd_bin (htdiv main) A13 A14 ((u * (j : ℤ))) ((k : ℤ)) (X) (.int (base) :: .int (base) :: .int ((p : ℤ))  :: rest) rfl rfl (by omega) rfl (cost_mul KK B Dg Ktdiv (isz (u * (j : ℤ))) (isz (k : ℤ)) hB100 hDg2 hKtdiv (by omega) (by omega))
      have s13 : WordR main (pickP 0) (fun vs => vs = A14) (fun _ out => out = A15) (fun _ => Cstep) := by
        refine wrd_pick (hpick main) 0 A14 (A14.getD 0 .nil) rfl (by simp only [A14]; simp) ?_
        exact cost_pickroll KK B Dg Kpick 0 _ hB100 hDg2 hKpick (by norm_num) (by simp only [A14, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int, base] <;> omega)
      have s14 : WordR main (rollP 3) (fun vs => vs = A15) (fun _ out => out = A16) (fun _ => Cstep) := by
        refine wrd_roll (hroll main) 3 A15 (A15.getD 3 .nil) rfl (by simp only [A15]; simp) ?_
        exact cost_pickroll KK B Dg Kroll 3 _ hB100 hDg2 hKroll (by norm_num) (by simp only [A15, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int, base] <;> omega)
      have hsegB : WordR main segB (fun vs => vs = A8) (fun _ out => out = A16) (fun _ => 8 * Cstep) := by
        have c14 := s14
        have c13 := wrd_seq2 s13 c14
        have c12 := wrd_seq2 s12 c13
        have c11 := wrd_seq2 s11 c12
        have c10 := wrd_seq2 s10 c11
        have c9 := wrd_seq2 s9 c10
        have c8 := wrd_seq2 s8 c9
        have c7 := wrd_seq2 s7 c8
        exact wrd_conseq hk c7 (fun _ h => h) (fun _ _ _ h => h) (fun _ _ => by beta_reduce; omega)
      have hlgFun : ∀ mid, mid = A16 → WordR main lgP (fun vs => vs = mid)
          (fun _ out => ∃ L : ℤ, |(L : ℝ) - 2 ^ Pn * Real.log 2| ≤ 1 ∧
            out = .int L :: (HvdH.Val.int (X) :: .int (X) :: .int (base) :: .int ((p : ℤ)) :: rest))
          (fun _ => Cstep) := by
        intro mid hmid
        rw [hmid]
        have hw : WordR main lgP (fun vs => vs = A16)
            (fun _ out => ∃ L : ℤ, |(L : ℝ) - 2 ^ Pn * Real.log 2| ≤ 1 ∧
              out = .int L :: (HvdH.Val.int (X) :: .int (X) :: .int (base) :: .int ((p : ℤ)) :: rest))
            (fun _ => Klog * (Pn + 1) ^ Klog) :=
          wrd_logW hlg Pn hPn A16 (HvdH.Val.int (X) :: .int (X) :: .int (base) :: .int ((p : ℤ)) :: rest) (by simp only [A16]; rw [hbase])
        have hc : Klog * (Pn + 1) ^ Klog ≤ Cstep := by
          have hP : Pn + 1 ≤ 53 * B := by simp only [Pn]; omega
          exact cost_word KK B Dg Klog Pn hB100 hDg2 hP hDgKlog hKlog53
        exact wrd_conseq hk hw (fun _ h => h) (fun _ _ _ h => h) (fun _ _ => hc)
      have H2 : WordR main p2 (fun vs => vs = A8)
          (fun _ out => ∃ L : ℤ, |(L : ℝ) - 2 ^ Pn * Real.log 2| ≤ 1 ∧
            out = .int L :: (HvdH.Val.int (X) :: .int (X) :: .int (base) :: .int ((p : ℤ)) :: rest))
          (fun _ => 9 * Cstep) := by
        have h := wrd_seq_exi hsegB hlgFun
        exact wrd_conseq hk h (fun _ hh => hh) (fun _ _ _ hh => hh) (fun _ _ => by beta_reduce; omega)
      
      have cont2 : ∀ mid, (∃ L : ℤ, |(L : ℝ) - 2 ^ Pn * Real.log 2| ≤ 1 ∧
            mid = .int L :: (HvdH.Val.int (X) :: .int (X) :: .int (base) :: .int ((p : ℤ)) :: rest)) →
          WordR main q2 (fun vs => vs = mid)
            (fun _ out => ∃ (w : ℤ × ℤ), out = cfxVal w :: rest ∧ inDisc p w ∧
              (2 : ℝ) ^ p * ‖fxC p w - ((Real.exp (-(Real.pi * j / k)) : ℝ) : ℂ)‖ < 2)
            (fun _ => 26 * Cstep) := by
        intro mid hmid
        rcases hmid with ⟨L, hL, hm⟩
        rw [hm] at *
        have hMLt : isz L ≤ 2 * p + 72 := by
          have h4 := abs_le.mp hL
          have hlog : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
          have hlogpos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
          have hR : (2:ℝ)^(Pn+2) = (2:ℝ)^Pn * 4 := by rw [pow_add]; norm_num
          have h1 : (1:ℝ) ≤ (2:ℝ) ^ Pn := one_le_pow₀ (by norm_num)
          have hpos : (0:ℝ) < (2:ℝ) ^ Pn := pow_pos (two_pos : (0:ℝ) < 2) Pn
          have h3 : |(L : ℝ)| ≤ (2 : ℝ) ^ (Pn + 2) := by
            rw [abs_le, hR]
            constructor
            · nlinarith [h4.1, hlogpos, h1, hpos]
            · nlinarith [h4.2, hlog, h1, hpos]
          have h9 : L.natAbs.size ≤ Pn + 3 := natAbsSize_le_of_abs_le_pow L (Pn + 2) h3
          have h10 : Pn + 5 ≤ 2 * p + 72 := by simp only [Pn]; omega
          simp only [isz]; omega
        have hML : isz L ≤ 100 * B + 1000 := by
          have h10 : 2 * p + 72 ≤ 100 * B + 1000 := by omega
          omega
        have hLpos : 0 < L := by
          have h1 := (abs_le.mp hL).1
          have hlog : (1:ℝ)/2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
          have h2 : (1:ℝ) < (2:ℝ)^Pn * Real.log 2 := by
            have h3 : (2:ℝ) ≤ (2:ℝ)^Pn := by
              have h4 : (1:ℕ) ≤ Pn := by simp only [Pn]; omega
              calc (2:ℝ) = (2:ℝ)^1 := by norm_num
                _ ≤ (2:ℝ)^Pn := pow_le_pow_right₀ (by norm_num) h4
            nlinarith [h3, hlog]
          have h5 : (0:ℝ) < (L:ℝ) := by linarith
          exact_mod_cast h5
        let ti : ℤ := Int.tdiv X L
        have hA := expNegXtau p j k u L X ti.toNat hp hk1 hjlt hu hL rfl rfl
        have hti0 : 0 ≤ ti := by simp only [ti]; exact tdv_nonneg hA.1 hLpos
        have htin : ti = ((ti.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hti0).symm
        have hMtt : isz ti ≤ Pn + p + 12 := by
          have h := natAbs_tdiv_size_le X L
          have h' : ti.natAbs.size ≤ X.natAbs.size := h
          have h2 : isz ti ≤ isz X := by simp only [isz]; omega
          omega
        have hMt : isz ti ≤ 100 * B + 1000 := by
          have h2 : Pn + p + 12 ≤ 100 * B + 1000 := by simp only [Pn]; omega
          omega
        let tiN : ℤ := ((ti.toNat : ℕ) : ℤ)
        have htiN : tiN = ti := htin.symm
        let Z : ℤ := tiN * L - X
        have hZdef : Z = (ti.toNat : ℤ) * L - X := by simp only [Z, tiN]
        have hMtL : isz (tiN * L) ≤ 100 * B + 1000 := by
          have h := isz_mul_le tiN L
          have h2 : isz tiN ≤ Pn + p + 12 := by rw [htiN]; exact hMtt
          have h3 : Pn + p + 12 + (2 * p + 72) ≤ 100 * B + 1000 := by simp only [Pn]; omega
          omega
        have hB := expNegZ p j k X L ti.toNat hp hk1 hjlt hL hA.2.1 hA.2.2.2.1 hA.2.2.2.2.1
        have hzy : |(Z : ℝ) / 2 ^ Pn - ((ti.toNat : ℝ) * Real.log 2 - Real.pi * j / k)| ≤ 1 / 2 ^ (p + 50) := by
          have h := hB.1
          simpa only [hZdef, Pn] using h
        have hz32 : |(Z : ℝ) / 2 ^ Pn| ≤ 32 := by
          have h := hB.2.1
          simpa only [hZdef, Pn] using h
        have hMZ : isz Z ≤ 100 * B + 1000 := by
          have h' : Z.natAbs.size ≤ 3 * p + 80 := by
            have h := hB.2.2
            simpa only [hZdef] using h
          simp only [isz]
          omega
        let A17 : List Val := .int (L) :: .int (X) :: .int (X) :: .int (base) :: .int ((p : ℤ)) :: rest
        let A18 : List Val := .int (L) :: .int (L) :: .int (X) :: .int (X) :: .int (base) :: .int ((p : ℤ)) :: rest
        let A19 : List Val := .int (X) :: .int (L) :: .int (L) :: .int (X) :: .int (base) :: .int ((p : ℤ)) :: rest
        let A20 : List Val := .int (ti) :: .int (L) :: .int (X) :: .int (base) :: .int ((p : ℤ)) :: rest
        let A21 : List Val := .int (ti) :: .int (ti) :: .int (L) :: .int (X) :: .int (base) :: .int ((p : ℤ)) :: rest
        let A22 : List Val := .int (L) :: .int (ti) :: .int (ti) :: .int (X) :: .int (base) :: .int ((p : ℤ)) :: rest
        let A23 : List Val := .int ((tiN * L)) :: .int (ti) :: .int (X) :: .int (base) :: .int ((p : ℤ)) :: rest
        let A24 : List Val := .int (X) :: .int ((tiN * L)) :: .int (ti) :: .int (base) :: .int ((p : ℤ)) :: rest
        let A25 : List Val := .int ((tiN * L)) :: .int (X) :: .int (ti) :: .int (base) :: .int ((p : ℤ)) :: rest
        let A26 : List Val := .int (Z) :: .int (ti) :: .int (base) :: .int ((p : ℤ)) :: rest
        let A27 : List Val := .int ((0 : ℤ)) :: .int (Z) :: .int (ti) :: .int (base) :: .int ((p : ℤ)) :: rest
        let A28 : List Val := .int (Z) :: .int ((0 : ℤ)) :: .int (ti) :: .int (base) :: .int ((p : ℤ)) :: rest
        let A29 : List Val := .int (base) :: .int (Z) :: .int ((0 : ℤ)) :: .int (ti) :: .int ((p : ℤ)) :: rest
        have s15 : WordR main (pickP 0) (fun vs => vs = A17) (fun _ out => out = A18) (fun _ => Cstep) := by
          refine wrd_pick (hpick main) 0 A17 (A17.getD 0 .nil) rfl (by simp only [A17]; simp) ?_
          exact cost_pickroll KK B Dg Kpick 0 _ hB100 hDg2 hKpick (by norm_num) (by simp only [A17, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int, base] <;> omega)
        have s16 : WordR main (rollP 2) (fun vs => vs = A18) (fun _ out => out = A19) (fun _ => Cstep) := by
          refine wrd_roll (hroll main) 2 A18 (A18.getD 2 .nil) rfl (by simp only [A18]; simp) ?_
          exact cost_pickroll KK B Dg Kroll 2 _ hB100 hDg2 hKroll (by norm_num) (by simp only [A18, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int, base] <;> omega)
        have s17 : WordR main tdivP (fun vs => vs = A19) (fun _ out => out = A20) (fun _ => Cstep) :=
          wrd_bin (htdiv main) A19 A20 (X) (L) (ti) (.int (L) :: .int (X) :: .int (base) :: .int ((p : ℤ))  :: rest) rfl rfl (by omega) rfl (cost_mul KK B Dg Ktdiv (isz X) (isz L) hB100 hDg2 hKtdiv (by omega) (by omega))
        have s18 : WordR main (pickP 0) (fun vs => vs = A20) (fun _ out => out = A21) (fun _ => Cstep) := by
          refine wrd_pick (hpick main) 0 A20 (A20.getD 0 .nil) rfl (by simp only [A20]; simp) ?_
          exact cost_pickroll KK B Dg Kpick 0 _ hB100 hDg2 hKpick (by norm_num) (by simp only [A20, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int, base] <;> omega)
        have s19 : WordR main (rollP 2) (fun vs => vs = A21) (fun _ out => out = A22) (fun _ => Cstep) := by
          refine wrd_roll (hroll main) 2 A21 (A21.getD 2 .nil) rfl (by simp only [A21]; simp) ?_
          exact cost_pickroll KK B Dg Kroll 2 _ hB100 hDg2 hKroll (by norm_num) (by simp only [A21, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int, base] <;> omega)
        have s20 : WordR main mulP (fun vs => vs = A22) (fun _ out => out = A23) (fun _ => Cstep) :=
          wrd_bin (hmul main) A22 A23 (L) (ti) ((tiN * L)) (.int (ti) :: .int (X) :: .int (base) :: .int ((p : ℤ))  :: rest) rfl rfl trivial (by rw [← htiN]; ring) (cost_mul KK B Dg Kmul (isz L) (isz ti) hB100 hDg2 hKmul (by omega) (by omega))
        have s21 : WordR main (rollP 2) (fun vs => vs = A23) (fun _ out => out = A24) (fun _ => Cstep) := by
          refine wrd_roll (hroll main) 2 A23 (A23.getD 2 .nil) rfl (by simp only [A23]; simp) ?_
          exact cost_pickroll KK B Dg Kroll 2 _ hB100 hDg2 hKroll (by norm_num) (by simp only [A23, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int, base] <;> omega)
        have s22 : WordR main swP (fun vs => vs = A24) (fun _ out => out = A25) (fun _ => Cstep) :=
          wrd_swap (hsw main) (HvdH.Val.int X) (HvdH.Val.int (tiN * L))
            (HvdH.Val.int (ti) :: .int (base) :: .int ((p : ℤ)) :: rest)
            (cost_swap KK B Dg Ksw (vsz (HvdH.Val.int X)) (vsz (HvdH.Val.int (tiN * L))) hB100 hDg2 hKsw (by rw [vsz_int]; omega) (by rw [vsz_int]; omega))
        have s23 : WordR main subP (fun vs => vs = A25) (fun _ out => out = A26) (fun _ => Cstep) :=
          wrd_bin (hsub main) A25 A26 ((tiN * L)) (X) (Z) (.int (ti) :: .int (base) :: .int ((p : ℤ))  :: rest) rfl rfl trivial rfl (cost_bin KK B Dg Ksub (isz (tiN * L)) (isz X) hB100 hDg2 hKsub (by omega) (by omega))
        have s24 : WordR main (pushP (HvdH.Val.int ((0 : ℤ)))) (fun vs => vs = A26) (fun _ out => out = A27) (fun _ => Cstep) := by
          refine wrd_rel (hpush main (HvdH.Val.int ((0 : ℤ)))) trivial (fun out h => h) ?_
          exact cost_drop KK B Dg Kpush (vsz (HvdH.Val.int ((0 : ℤ)))) hB100 hDg2 hKpush (by rw [vsz_int]; omega)
        have s25 : WordR main swP (fun vs => vs = A27) (fun _ out => out = A28) (fun _ => Cstep) :=
          wrd_swap (hsw main) (HvdH.Val.int (0 : ℤ)) (HvdH.Val.int Z)
            (HvdH.Val.int (ti) :: .int (base) :: .int ((p : ℤ)) :: rest)
            (cost_swap KK B Dg Ksw (vsz (HvdH.Val.int (0 : ℤ))) (vsz (HvdH.Val.int Z)) hB100 hDg2 hKsw (by rw [vsz_int]; omega) (by rw [vsz_int]; omega))
        have s26 : WordR main (rollP 3) (fun vs => vs = A28) (fun _ out => out = A29) (fun _ => Cstep) := by
          refine wrd_roll (hroll main) 3 A28 (A28.getD 3 .nil) rfl (by simp only [A28]; simp) ?_
          exact cost_pickroll KK B Dg Kroll 3 _ hB100 hDg2 hKroll (by norm_num) (by simp only [A28, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int, base] <;> omega)
        have hsegC : WordR main segC (fun vs => vs = A17) (fun _ out => out = A29) (fun _ => 12 * Cstep) := by
          have c26 := s26
          have c25 := wrd_seq2 s25 c26
          have c24 := wrd_seq2 s24 c25
          have c23 := wrd_seq2 s23 c24
          have c22 := wrd_seq2 s22 c23
          have c21 := wrd_seq2 s21 c22
          have c20 := wrd_seq2 s20 c21
          have c19 := wrd_seq2 s19 c20
          have c18 := wrd_seq2 s18 c19
          have c17 := wrd_seq2 s17 c18
          have c16 := wrd_seq2 s16 c17
          have c15 := wrd_seq2 s15 c16
          exact wrd_conseq hk c15 (fun _ h => h) (fun _ _ _ h => h) (fun _ _ => by beta_reduce; omega)
          
        have hZbound : (Z : ℝ) ^ 2 ≤ (32 * 2 ^ Pn) ^ 2 := by
          have h := hz32
          have hpos : (0:ℝ) < 2 ^ Pn := pow_pos (two_pos : (0:ℝ) < 2) Pn
          rw [abs_div, abs_of_pos hpos] at h
          have h2 : |(Z : ℝ)| ≤ 32 * 2 ^ Pn := by
            rw [div_le_iff₀ hpos] at h; linarith
          have h3 := abs_le.mp h2
          nlinarith [h3.1, h3.2]
        have hexpFun : ∀ mid, mid = A29 → WordR main exP (fun vs => vs = mid)
            (fun _ out => ∃ U V : ℤ, out = .int U :: .int V :: (HvdH.Val.int (ti) :: .int ((p : ℤ)) :: rest) ∧
              |(U : ℝ) / 2 ^ Pn - Real.exp ((Z : ℝ) / 2 ^ Pn)| ≤ 4 / (2 : ℝ) ^ Pn ∧
              V.natAbs ≤ 4)
            (fun _ => Cstep) := by
          intro mid hmid
          rw [hmid]
          have hw : WordR main exP (fun vs => vs = A29)
            (fun _ out => ∃ U V : ℤ, out = .int U :: .int V :: (HvdH.Val.int (ti) :: .int ((p : ℤ)) :: rest) ∧
              |(U : ℝ) / 2 ^ Pn - Real.exp ((Z : ℝ) / 2 ^ Pn)| ≤ 4 / (2 : ℝ) ^ Pn ∧
              V.natAbs ≤ 4)
            (fun _ => Kexp * (Pn + 1) ^ Kexp) :=
            wrd_expW hexp Pn hPn Z hZbound A29 (HvdH.Val.int (ti) :: .int ((p : ℤ)) :: rest)
              (by simp only [A29]; rw [hbase])
          have hc : Kexp * (Pn + 1) ^ Kexp ≤ Cstep := by
            have hP : Pn + 1 ≤ 53 * B := by simp only [Pn]; omega
            exact cost_word KK B Dg Kexp Pn hB100 hDg2 hP hDgKexp hKexp53
          exact wrd_conseq hk hw (fun _ h => h) (fun _ _ _ h => h) (fun _ _ => hc)
        have H3 : WordR main p3 (fun vs => vs = A17)
            (fun _ out => ∃ U V : ℤ, out = .int U :: .int V :: (HvdH.Val.int (ti) :: .int ((p : ℤ)) :: rest) ∧
              |(U : ℝ) / 2 ^ Pn - Real.exp ((Z : ℝ) / 2 ^ Pn)| ≤ 4 / (2 : ℝ) ^ Pn ∧
              V.natAbs ≤ 4)
            (fun _ => 13 * Cstep) := by
          have h := wrd_seq_exi hsegC hexpFun
          exact wrd_conseq hk h (fun _ hh => hh) (fun _ _ _ hh => hh) (fun _ _ => by beta_reduce; omega)
        have cont3 : ∀ mid, (∃ U V : ℤ, mid = .int U :: .int V :: (HvdH.Val.int (ti) :: .int ((p : ℤ)) :: rest) ∧
              |(U : ℝ) / 2 ^ Pn - Real.exp ((Z : ℝ) / 2 ^ Pn)| ≤ 4 / (2 : ℝ) ^ Pn ∧
              V.natAbs ≤ 4) →
            WordR main segD (fun vs => vs = mid)
              (fun _ out => ∃ (w : ℤ × ℤ), out = cfxVal w :: rest ∧ inDisc p w ∧
                (2 : ℝ) ^ p * ‖fxC p w - ((Real.exp (-(Real.pi * j / k)) : ℝ) : ℂ)‖ < 2)
              (fun _ => 13 * Cstep) := by
          intro mid hmid
          rcases hmid with ⟨U, V, hm, hUV, hV4⟩
          rw [hm] at *
          have hy2 : |((ti.toNat : ℝ) * Real.log 2 - Real.pi * j / k)| ≤ 2 := by
            have h := hA.2.2.2.1
            have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
            have hlog1 : Real.log 2 ≤ 1 := le_of_lt (Real.log_two_lt_d9.trans (by norm_num))
            have heq : (ti.toNat : ℝ) * Real.log 2 - Real.pi * j / k
                = ((ti.toNat : ℝ) - (Real.pi * j / k) / Real.log 2) * Real.log 2 := by
              field_simp
            rw [heq, abs_mul, abs_of_pos hlog]
            nlinarith [abs_nonneg ((ti.toNat : ℝ) - (Real.pi * j / k) / Real.log 2), h, hlog, hlog1]
          have hz3 : |(Z : ℝ) / 2 ^ Pn| ≤ 3 := abs_div_two_pow_le_three p j k Z ti.toNat hzy hy2
          have he32 : Real.exp ((Z : ℝ) / 2 ^ Pn) ≤ 32 := exp_le_thirtytwo p Z hz3
          have hUbound : |(U : ℝ)| ≤ (2 : ℝ) ^ (Pn + 6) := abs_U_le p Z U hz3 he32 hUV
          have hMU6 : isz U ≤ Pn + 11 := by
            have h := natAbsSize_le_of_abs_le_pow U (Pn + 6) hUbound
            simp only [isz]; omega
          have hMU : isz U ≤ 100 * B + 1000 := by
            have h2 : Pn + 11 ≤ 100 * B + 1000 := by simp only [Pn]; omega
            omega
          have hMV : isz V ≤ 100 * B + 1000 := by
            have h1 : V.natAbs ≤ 4 := hV4
            have h2 : V.natAbs.size ≤ 4 := Nat.size_le.mpr (by omega)
            simp only [isz]; omega
          let sn : ℤ := (p : ℤ) + ((60:ℤ) + ti)
          let W2 : ℤ := (2:ℤ) ^ sn.toNat
          let w : ℤ := Int.tdiv U W2
          have hsn : sn.toNat = ti.toNat + p + 60 := by
            have h1 : sn = ((ti.toNat + p + 60 : ℕ) : ℤ) := by
              have h2 : ((ti.toNat + p + 60 : ℕ) : ℤ) = (p : ℤ) + ((60 : ℤ) + ti) := by
                push_cast
                rw [← htin]
                ring
              rw [h2]
            rw [h1, Int.toNat_natCast]
          have hMsn1 : sn.toNat ≤ 7 * p + 80 := by
            rw [hsn]
            have h := hA.2.2.2.2.1
            omega
          have hMsn2 : isz sn ≤ 100 * B + 1000 := by
            have h3 : 0 ≤ sn := by
              have h := hti0
              simp only [sn]
              omega
            have h5 : (sn.natAbs : ℤ) ≤ ((7 * p + 80 : ℕ) : ℤ) := by
              rw [Int.natAbs_of_nonneg h3]
              have h6 : sn = ((sn.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg h3).symm
              rw [h6]
              exact_mod_cast hMsn1
            have h6 : sn.natAbs ≤ 7 * p + 80 := by exact_mod_cast h5
            have h7 : sn.natAbs.size ≤ 7 * p + 80 :=
              le_trans (Nat.size_le_size h6) (Nat.size_le.mpr (Nat.lt_two_pow_self (n := 7 * p + 80)))
            simp only [isz]
            omega
          have hMW2 : isz W2 ≤ 100 * B + 1000 := by
            have h2 : W2.natAbs.size ≤ sn.toNat + 1 := by
              have h3 : W2.natAbs = 2 ^ sn.toNat := by
                simp only [W2]
                rw [Int.natAbs_pow]
                norm_num
              rw [h3]
              exact Nat.size_le.mpr (Nat.pow_lt_pow_right (by norm_num) (by omega))
            simp only [isz]
            omega
          have hMw : isz w ≤ 100 * B + 1000 := by
            have h := natAbs_tdiv_le U W2
            have h' : w.natAbs ≤ U.natAbs := h
            have h2 : w.natAbs.size ≤ U.natAbs.size := Nat.size_le_size h'
            have h3 : isz w ≤ isz U := by simp only [isz]; omega
            omega
          have hMt60 : isz ((60:ℤ) + ti) ≤ 100 * B + 1000 := by
            have h := isz_add_le (60:ℤ) ti
            have h3 : isz ti ≤ Pn + p + 12 := hMtt
            have h4 : max (isz (60:ℤ)) (isz ti) + 1 ≤ 100 * B + 1000 := by
              have h5 : 8 ≤ 100 * B + 1000 := by omega
              have h6 : Pn + p + 13 ≤ 100 * B + 1000 := by simp only [Pn]; omega
              omega
            omega
          let A30 : List Val := .int (U) :: .int (V) :: .int (ti) :: .int ((p : ℤ)) :: rest
          let A31 : List Val := .int (ti) :: .int (U) :: .int (V) :: .int ((p : ℤ)) :: rest
          let A32 : List Val := .int ((60 : ℤ)) :: .int (ti) :: .int (U) :: .int (V) :: .int ((p : ℤ)) :: rest
          let A33 : List Val := .int (((60 : ℤ) + ti)) :: .int (U) :: .int (V) :: .int ((p : ℤ)) :: rest
          let A34 : List Val := .int ((p : ℤ)) :: .int (((60 : ℤ) + ti)) :: .int (U) :: .int (V) :: rest
          let A35 : List Val := .int (sn) :: .int (U) :: .int (V) :: rest
          let A36 : List Val := .int (W2) :: .int (U) :: .int (V) :: rest
          let A37 : List Val := .int (U) :: .int (W2) :: .int (V) :: rest
          let A38 : List Val := .int (w) :: .int (V) :: rest
          let A39 : List Val := .int ((0 : ℤ)) :: .int (w) :: .int (V) :: rest
          let A40 : List Val := .int (w) :: .int ((0 : ℤ)) :: .int (V) :: rest
          let A41 : List Val := cfxVal (w, (0 : ℤ)) :: .int (V) :: rest
          let A42 : List Val := .int (V) :: cfxVal (w, (0 : ℤ)) :: rest
          let A43 : List Val := cfxVal (w, (0 : ℤ)) :: rest
          have s27 : WordR main (rollP 2) (fun vs => vs = A30) (fun _ out => out = A31) (fun _ => Cstep) := by
            refine wrd_roll (hroll main) 2 A30 (A30.getD 2 .nil) rfl (by simp only [A30]; simp) ?_
            exact cost_pickroll KK B Dg Kroll 2 _ hB100 hDg2 hKroll (by norm_num) (by simp only [A30, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int, base] <;> omega)
          have s28 : WordR main (pushP (HvdH.Val.int ((60 : ℤ)))) (fun vs => vs = A31) (fun _ out => out = A32) (fun _ => Cstep) := by
            refine wrd_rel (hpush main (HvdH.Val.int ((60 : ℤ)))) trivial (fun out h => h) ?_
            exact cost_drop KK B Dg Kpush (vsz (HvdH.Val.int ((60 : ℤ)))) hB100 hDg2 hKpush (by rw [vsz_int]; omega)
          have s29 : WordR main addP (fun vs => vs = A32) (fun _ out => out = A33) (fun _ => Cstep) :=
            wrd_bin (hadd main) A32 A33 ((60 : ℤ)) (ti) (((60 : ℤ) + ti)) (.int (U) :: .int (V) :: .int ((p : ℤ))  :: rest) rfl rfl trivial rfl (cost_bin KK B Dg Kadd (isz (60 : ℤ)) (isz ti) hB100 hDg2 hKadd (by omega) (by omega))
          have s30 : WordR main (rollP 3) (fun vs => vs = A33) (fun _ out => out = A34) (fun _ => Cstep) := by
            refine wrd_roll (hroll main) 3 A33 (A33.getD 3 .nil) rfl (by simp only [A33]; simp) ?_
            exact cost_pickroll KK B Dg Kroll 3 _ hB100 hDg2 hKroll (by norm_num) (by simp only [A33, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int, base] <;> omega)
          have s31 : WordR main addP (fun vs => vs = A34) (fun _ out => out = A35) (fun _ => Cstep) :=
            wrd_bin (hadd main) A34 A35 ((p : ℤ)) (((60 : ℤ) + ti)) (sn) (.int (U) :: .int (V)  :: rest) rfl rfl trivial rfl (cost_bin KK B Dg Kadd (isz (p : ℤ)) (isz ((60 : ℤ) + ti)) hB100 hDg2 hKadd (by omega) (by omega))
          have s32 : WordR main powP (fun vs => vs = A35) (fun _ out => out = A36) (fun _ => Cstep) :=
            wrd_un (hpow main) A35 A36 (sn) (W2) (.int (U) :: .int (V)  :: rest) rfl rfl (by simp only [sn]; have := hti0; omega) rfl (cost_bin KK B Dg Kpow sn.toNat (isz sn) hB100 hDg2 hKpow (by omega) (by omega))
          have s33 : WordR main swP (fun vs => vs = A36) (fun _ out => out = A37) (fun _ => Cstep) :=
            wrd_swap (hsw main) (HvdH.Val.int W2) (HvdH.Val.int U) (HvdH.Val.int (V) :: rest)
              (cost_swap KK B Dg Ksw (vsz (HvdH.Val.int W2)) (vsz (HvdH.Val.int U)) hB100 hDg2 hKsw (by rw [vsz_int]; omega) (by rw [vsz_int]; omega))
          have s34 : WordR main tdivP (fun vs => vs = A37) (fun _ out => out = A38) (fun _ => Cstep) :=
            wrd_bin (htdiv main) A37 A38 (U) (W2) (w) (.int (V)  :: rest) rfl rfl (pow_ne_zero _ (two_ne_zero : (2:ℤ) ≠ 0)) rfl (cost_mul KK B Dg Ktdiv (isz U) (isz W2) hB100 hDg2 hKtdiv (by omega) (by omega))
          have s35 : WordR main (pushP (HvdH.Val.int ((0 : ℤ)))) (fun vs => vs = A38) (fun _ out => out = A39) (fun _ => Cstep) := by
            refine wrd_rel (hpush main (HvdH.Val.int ((0 : ℤ)))) trivial (fun out h => h) ?_
            exact cost_drop KK B Dg Kpush (vsz (HvdH.Val.int ((0 : ℤ)))) hB100 hDg2 hKpush (by rw [vsz_int]; omega)
          have s36 : WordR main swP (fun vs => vs = A39) (fun _ out => out = A40) (fun _ => Cstep) :=
            wrd_swap (hsw main) (HvdH.Val.int (0 : ℤ)) (HvdH.Val.int w) (HvdH.Val.int (V) :: rest)
              (cost_swap KK B Dg Ksw (vsz (HvdH.Val.int (0 : ℤ))) (vsz (HvdH.Val.int w)) hB100 hDg2 hKsw (by rw [vsz_int]; omega) (by rw [vsz_int]; omega))
          have s37 : WordR main consP (fun vs => vs = A40) (fun _ out => out = A41) (fun _ => Cstep) :=
            wrd_cons (hcons main) (Val.int (w)) (Val.int (0 : ℤ)) (HvdH.Val.int (V) :: rest) (cost_const KK B Dg Kcons hB100 hDg2 hKcons)
          have s38 : WordR main (rollP 1) (fun vs => vs = A41) (fun _ out => out = A42) (fun _ => Cstep) := by
            refine wrd_roll (hroll main) 1 A41 (A41.getD 1 .nil) rfl (by simp only [A41]; simp) ?_
            exact cost_pickroll KK B Dg Kroll 1 _ hB100 hDg2 hKroll (by norm_num) (by simp only [A41, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_cfxVal_snd_zero, vsz_int] <;> omega)
          have s39 : WordR main dropP (fun vs => vs = A42) (fun _ out => out = A43) (fun _ => Cstep) :=
            wrd_drop (hdrop main) (HvdH.Val.int (V)) (cfxVal (w, (0 : ℤ)) :: rest) (cost_drop KK B Dg Kdrop (vsz (HvdH.Val.int (V))) hB100 hDg2 hKdrop (by rw [vsz_int]; omega))
          have hsegD : WordR main segD (fun vs => vs = A30) (fun _ out => out = A43) (fun _ => 13 * Cstep) := by
            have c39 := s39
            have c38 := wrd_seq2 s38 c39
            have c37 := wrd_seq2 s37 c38
            have c36 := wrd_seq2 s36 c37
            have c35 := wrd_seq2 s35 c36
            have c34 := wrd_seq2 s34 c35
            have c33 := wrd_seq2 s33 c34
            have c32 := wrd_seq2 s32 c33
            have c31 := wrd_seq2 s31 c32
            have c30 := wrd_seq2 s30 c31
            have c29 := wrd_seq2 s29 c30
            have c28 := wrd_seq2 s28 c29
            have c27 := wrd_seq2 s27 c28
            exact wrd_conseq hk c27 (fun _ h => h) (fun _ _ _ h => h) (fun _ _ => by beta_reduce; omega)
          have hx0 : 0 ≤ (Real.pi * j / k : ℝ) := div_nonneg (mul_nonneg (le_of_lt Real.pi_pos) (Nat.cast_nonneg j)) (Nat.cast_nonneg k)
          have hC := expNegFinalB p (Real.pi * j / k) ((ti.toNat : ℝ) * Real.log 2 - Real.pi * j / k)
            ((Z : ℝ) / 2 ^ Pn) ti.toNat U w hp hx0 rfl hA.2.2.2.1 hzy hUV (by simp only [w, W2, hsn])
          refine wrd_conseq hk hsegD (fun _ h => h) ?_ (fun _ _ => le_rfl)
          intro vs' out hpre hpost
          rw [hpost]
          refine ⟨(w, (0:ℤ)), ?_, ?_, ?_⟩
          · rfl
          · exact inDisc_of_abs_le p w hC.2.1
          · rw [final_conv]
            exact hC.1
        exact wrd_conseq hk (wrd_seq_exi H3 cont3) (fun _ h => h) (fun _ _ _ h => h) (fun _ _ => by beta_reduce; omega)
      exact wrd_conseq hk (wrd_seq_exi H2 cont2) (fun _ h => h) (fun _ _ _ h => h) (fun _ _ => by beta_reduce; omega)
    exact wrd_conseq hk (wrd_seq_exi H1 cont1) (fun _ h => h) (fun _ _ _ h => h) (fun _ _ => by beta_reduce; omega)
  have hif : WordR main (izC zeroQ mainQ) (fun vs => vs = .int fv :: F0)
      (fun _ out => (fv = 0 → out = cfxVal ((0:ℤ),(0:ℤ)) :: rest) ∧
        (fv ≠ 0 → ∃ (w : ℤ × ℤ), out = cfxVal w :: rest ∧ inDisc p w ∧
          (2 : ℝ) ^ p * ‖fxC p w - ((Real.exp (-(Real.pi * j / k)) : ℝ) : ℂ)‖ < 2))
      (fun _ => Kiz * (isz fv + 1) + max (4*Cstep) (43*Cstep)) :=
    hiz main zeroQ mainQ fv F0 (fun out => out = cfxVal ((0:ℤ),(0:ℤ)) :: rest)
      (fun out => ∃ (w : ℤ × ℤ), out = cfxVal w :: rest ∧ inDisc p w ∧
        (2 : ℝ) ^ p * ‖fxC p w - ((Real.exp (-(Real.pi * j / k)) : ℝ) : ℂ)‖ < 2)
      (4*Cstep) (43*Cstep) hzero hmain
  have hwhole : WordR main prog (fun vs => vs = F0)
      (fun _ out => (fv = 0 → out = cfxVal ((0:ℤ),(0:ℤ)) :: rest) ∧
        (fv ≠ 0 → ∃ (w : ℤ × ℤ), out = cfxVal w :: rest ∧ inDisc p w ∧
          (2 : ℝ) ^ p * ‖fxC p w - ((Real.exp (-(Real.pi * j / k)) : ℝ) : ℂ)‖ < 2))
      (fun _ => 7*Cstep + (Kiz * (isz fv + 1) + max (4*Cstep) (43*Cstep))) := by
    refine wrd_seq_exi hflag (fun mid hmid => ?_)
    rw [hmid]
    exact hif
  have hvsF : vs = F0 := by rw [hvs]
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := hwhole vs hvsF s R0 hR
  have hcost : 7 * Cstep + (Kiz * (isz fv + 1) + max (4 * Cstep) (43 * Cstep)) ≤
      (10 ^ 8 * (KK + 1) + Dg + 1) * B ^ (10 ^ 8 * (KK + 1) + Dg + 1) := by
    have h1 : isz fv ≤ 3 := by simp only [fv]; split <;> norm_num [isz]
    have h2 : Kiz * (isz fv + 1) ≤ 4 * KK := by
      have h3 : isz fv + 1 ≤ 4 := by omega
      calc Kiz * (isz fv + 1) ≤ KK * 4 := Nat.mul_le_mul hKiz h3
        _ = 4 * KK := by ring
    have h4 : max (4 * Cstep) (43 * Cstep) = 43 * Cstep := max_eq_right (by omega)
    rw [h4]
    have h5 : 7 * Cstep + (Kiz * (isz fv + 1) + 43 * Cstep) = 50 * Cstep + Kiz * (isz fv + 1) := by ring
    have h6 : Kiz * (isz fv + 1) ≤ 4 * KK := h2
    have h7 : 50 * Cstep = 50 * (100000 * KK * B ^ Dg) := by simp only [Cstep]
    have h8 := cost_final KK B Dg (by omega) hDg2
    linarith [h5, h6, h7, h8]
  rcases hpost with ⟨hp0, hp1⟩
  by_cases hlt : j < k * (p + 2)
  · have hfvn : fv ≠ 0 := by
      have h1 : ((j:ℤ)) < ((k:ℤ) * ((2:ℤ) + (p:ℤ))) := by
        have h2 : ((k*(p+2):ℕ):ℤ) = (k:ℤ)*((2:ℤ)+(p:ℤ)) := by push_cast; ring
        rw [← h2]; exact_mod_cast hlt
      simp only [fv, if_pos h1]
      norm_num
    rcases hp1 hfvn with ⟨w, hout, hdisc, herr⟩
    exact ⟨out, s', n, ⟨rest, w, hvsF, hout, hdisc, herr⟩, hev, le_trans hn hcost, hstk, hfr⟩
  · have hfv0 : fv = 0 := by
      have h1 : ¬ ((j:ℤ) < ((k:ℤ) * ((2:ℤ) + (p:ℤ)))) := by
        intro h2
        have h3 : ((k*(p+2):ℕ):ℤ) = (k:ℤ)*((2:ℤ)+(p:ℤ)) := by push_cast; ring
        have h4 : (j:ℤ) < ((k*(p+2):ℕ):ℤ) := by rw [h3]; exact_mod_cast h2
        exact hlt (by exact_mod_cast h4)
      simp only [fv, if_neg h1]
    have hout := hp0 hfv0
    have hnorm : ‖fxC p ((0:ℤ),(0:ℤ)) - ((Real.exp (-(Real.pi*j/k)) : ℝ) : ℂ)‖
        = Real.exp (-(Real.pi * j / k)) := by
      have h1 : fxC p ((0:ℤ),(0:ℤ)) = 0 := by simp [fxC]
      rw [h1, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt (Real.exp_pos _))]
    refine ⟨out, s', n, ⟨rest, ((0:ℤ),(0:ℤ)), hvsF, ?_, ?_, ?_⟩, hev, le_trans hn hcost, hstk, hfr⟩
    · rw [hout]
    · simp only [inDisc]; simpa using pow_nonneg (by norm_num : (0:ℤ) ≤ 4) p
    · rw [hnorm]
      exact expNegZero p j k hp hk1 (by omega)

end Work.Fx
