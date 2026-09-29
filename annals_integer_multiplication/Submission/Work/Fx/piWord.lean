import Mathlib
import Submission.Work.Fx.FxCommon
import Submission.Work.Fx.piDefs
import Submission.Work.Fx.piIter
import Submission.Work.Fx.piUBound

/-!
# The π word: assembly layer

`Pipe main prog A B c` is a `WordR` spec for a word that transforms the top `|A|` values of the
value stack from the *fixed* window `A` into the *fixed* window `B`, leaving everything below
untouched.  This is the shape needed to chain library words by hand inside a `KernelLib.loop`.
-/

set_option autoImplicit false
set_option maxHeartbeats 10000000

namespace Work.Fx

open HvdH

/-! ## `Pipe` -/

/-- `Pipe main prog A B c`: `prog` maps the window `A` (on top of any fixed list of values) to the
window `B`, at cost at most `c`. -/
def Pipe (main prog : Cmd) (A B : List Val) (c : ℕ) : Prop :=
  ∀ rest : List Val,
    WordR main prog (fun vs => vs = A ++ rest) (fun _ out => out = B ++ rest) (fun _ => c)

theorem Pipe.le {main prog : Cmd} {A B : List Val} {c c' : ℕ} (h : Pipe main prog A B c)
    (hc : c ≤ c') : Pipe main prog A B c' := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h rest vs hvs s R hR
  exact ⟨out, s', n, hout, hev, le_trans hn hc, hstk, hoth⟩

theorem Pipe.rw {main prog : Cmd} {A B B' : List Val} {c : ℕ} (h : Pipe main prog A B c)
    (hB : B = B') : Pipe main prog A B' c := hB ▸ h

theorem Pipe.comp {main p q : Cmd} {A B D : List Val} {c d : ℕ} (h1 : Pipe main p A B c)
    (h2 : Pipe main q B D d) : Pipe main (.seq p q) A D (c + d) := by
  intro rest vs hvs s R hR
  obtain ⟨mid, s', n1, hmid, hev1, hn1, hstk1, hoth1⟩ := h1 rest vs hvs s R hR
  obtain ⟨out, s'', n2, hout, hev2, hn2, hstk2, hoth2⟩ := h2 rest mid hmid s' R hstk1
  exact ⟨out, s'', n1 + n2, hout, Eval.seq hev1 hev2, Nat.add_le_add hn1 hn2, hstk2,
    fun k hk => by rw [hoth2 k hk, hoth1 k hk]⟩

theorem Pipe.appendTail {main prog : Cmd} {A B : List Val} {c : ℕ} (T : List Val)
    (h : Pipe main prog A B c) : Pipe main prog (A ++ T) (B ++ T) c := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ :=
    h (T ++ rest) vs (by rw [hvs, List.append_assoc]) s R
      (by simpa only [hvs, List.append_assoc] using hR)
  exact ⟨out, s', n, by rw [hout, List.append_assoc], hev, hn, hstk, hoth⟩

/-! ## Adapters for the library words -/

theorem Pipe.pushVal {main : Cmd} {prog : Val → Cmd} {K : ℕ}
    (h : ∀ (m : Cmd) (v : Val), WordR m (prog v) (fun _ => True)
      (fun vs out => out = v :: vs) (fun _ => K * (vsz v + 1))) (v : Val) :
    Pipe main (prog v) [] [v] (K * (vsz v + 1)) := by
  intro rest vs hvs s R hR
  have hrs : vs = rest := by rw [hvs, List.nil_append]
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h main v vs trivial s R hR
  exact ⟨out, s', n, by rw [hout, hrs]; rfl, hev, hn, hstk, hoth⟩

theorem Pipe.binOp {main prog : Cmd} {P : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ} {C : ℤ → ℤ → ℕ}
    (h : BinOp main prog P f C) {a b : ℤ} (hab : P a b) :
    Pipe main prog [.int a, .int b] [.int (f a b)] (C a b) := by
  intro rest vs hvs s R hR
  have hv2 : vs = .int a :: .int b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h vs ⟨a, b, rest, hv2, hab⟩ s R hR
  obtain ⟨h1, h2, h3⟩ := int_cons_inj3 (hvs'.symm.trans hv2)
  have hn' : n ≤ C a b := by rw [hv2] at hn; exact hn
  exact ⟨out, s', n, by rw [hout, h1, h2, h3]; rfl, hev, hn', hstk, hoth⟩

theorem Pipe.unOp {main prog : Cmd} {P : ℤ → Prop} {f : ℤ → ℤ} {C : ℤ → ℕ}
    (h : UnOp main prog P f C) {a : ℤ} (ha : P a) :
    Pipe main prog [.int a] [.int (f a)] (C a) := by
  intro rest vs hvs s R hR
  have hv2 : vs = .int a :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h vs ⟨a, rest, hv2, ha⟩ s R hR
  have h1 := List.cons.inj (hvs'.symm.trans hv2)
  have ha' : a' = a := Val.int.inj h1.1
  have hn' : n ≤ C a := by rw [hv2] at hn; exact hn
  exact ⟨out, s', n, by rw [hout, ha', h1.2]; rfl, hev, hn', hstk, hoth⟩

theorem Pipe.swap {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (a b : Val) : Pipe main prog [a, b] [b, a] (K * (vsz a + vsz b + 1)) := by
  intro rest vs hvs s R hR
  have hv2 : vs = a :: b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv2]; simp) s R hR
  obtain ⟨h1, h2, h3⟩ := cons_inj3 (hvs'.symm.trans hv2)
  have hn' : n ≤ K * (vsz a + vsz b + 1) := by
    rw [hv2] at hn
    simpa only [List.getD_cons_zero, List.getD_cons_succ] using hn
  exact ⟨out, s', n, by rw [hout, h1, h2, h3]; rfl, hev, hn', hstk, hoth⟩

theorem Pipe.drop {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1)))
    (a : Val) : Pipe main prog [a] [] (K * (vsz a + 1)) := by
  intro rest vs hvs s R hR
  have hv2 : vs = a :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨v, rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv2]; simp) s R hR
  have h1 := List.cons.inj (hvs'.symm.trans hv2)
  have hn' : n ≤ K * (vsz a + 1) := by
    rw [hv2] at hn; simpa only [List.headD_cons] using hn
  exact ⟨out, s', n, by rw [hout, h1.2]; rfl, hev, hn', hstk, hoth⟩

theorem Pipe.dup {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1)))
    (a : Val) : Pipe main prog [a] [a, a] (K * (vsz a + 1)) := by
  intro rest vs hvs s R hR
  have hv2 : vs = a :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨v, rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv2]; simp) s R hR
  have h1 := List.cons.inj (hvs'.symm.trans hv2)
  have hn' : n ≤ K * (vsz a + 1) := by
    rw [hv2] at hn; simpa only [List.headD_cons] using hn
  exact ⟨out, s', n, by rw [hout, h1.1, h1.2]; rfl, hev, hn', hstk, hoth⟩

theorem szl_take_le_x2 (A : List Val) (m : ℕ) : szl (A.take m) ≤ szl A := by
  have h := szl_append (A.take m) (A.drop m)
  rw [List.take_append_drop] at h
  omega

theorem szl_le_len_mul {A : List Val} {n : ℕ} (h : ∀ v ∈ A, vsz v ≤ n) :
    szl A ≤ A.length * n := by
  induction A with
  | nil => simp [szl]
  | cons a t ih =>
    have ha : vsz a ≤ n := h a (by simp)
    have ht : ∀ v ∈ t, vsz v ≤ n := fun v hv => h v (by simp [hv])
    have := ih ht
    rw [szl_cons, List.length_cons]
    nlinarith [Nat.zero_le (vsz a), Nat.zero_le (szl t)]

theorem Pipe.pick {prog : ℕ → Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A : List Val} {k : ℕ} (hk : k < A.length) :
    Pipe main (prog k) A (A.getD k .nil :: A) (K * (k + 1) * (szl (A.take (k + 1)) + 1)) := by
  intro rest vs hvs s R hR
  have hlt : k < vs.length := by rw [hvs]; simp only [List.length_append]; omega
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h main k vs hlt s R hR
  have hn' : n ≤ K * (k + 1) * (szl (A.take (k + 1)) + 1) := by
    have h : n ≤ K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1) := hn
    rw [hvs, List.take_append_of_le_length (by omega)] at h
    simpa [szl] using h
  refine ⟨out, s', n, ?_, hev, hn', hstk, hoth⟩
  rw [hout, hvs, getD_append_of_lt hk]
  rfl

theorem Pipe.roll {prog : ℕ → Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A : List Val} {k : ℕ} (hk : k < A.length) :
    Pipe main (prog k) A (A.getD k .nil :: A.eraseIdx k)
      (K * (k + 1) * (szl (A.take (k + 1)) + 1)) := by
  intro rest vs hvs s R hR
  have hlt : k < vs.length := by rw [hvs]; simp only [List.length_append]; omega
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h main k vs hlt s R hR
  have hn' : n ≤ K * (k + 1) * (szl (A.take (k + 1)) + 1) := by
    have h : n ≤ K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1) := hn
    rw [hvs, List.take_append_of_le_length (by omega)] at h
    simpa [szl] using h
  refine ⟨out, s', n, ?_, hev, hn', hstk, hoth⟩
  rw [hout, hvs, getD_append_of_lt hk, eraseIdx_append_of_lt hk, List.cons_append]

/-! ## Cost helpers -/

/-- The uniform per-step cost bound. -/
def SB (p KS : ℕ) : ℕ := KS * (SZ p + 8) ^ 2

theorem le_SB_one {K KS p : ℕ} (hK : K ≤ KS) {v : ℕ} (hv : v ≤ SZ p) :
    K * (v + 1) ≤ SB p KS := by
  rw [SB]
  calc K * (v + 1) ≤ KS * (SZ p + 1) := Nat.mul_le_mul hK (by omega)
    _ ≤ KS * (SZ p + 8) ^ 2 := Nat.mul_le_mul_left _ (by
        nlinarith [Nat.zero_le (SZ p), sq_nonneg (SZ p)])

theorem le_SB_two {K KS p : ℕ} (hK : K ≤ KS) {u v : ℕ} (hu : u ≤ SZ p)
    (hv : v ≤ SZ p) : K * (u + v) ≤ SB p KS := by
  rw [SB]
  calc K * (u + v) ≤ KS * (2 * (SZ p)) := Nat.mul_le_mul hK (by omega)
    _ ≤ KS * (SZ p + 8) ^ 2 := Nat.mul_le_mul_left _ (by
        nlinarith [Nat.zero_le (SZ p), sq_nonneg (SZ p)])

theorem le_SB_three {K KS p : ℕ} (hK : K ≤ KS) {u v w : ℕ} (hu : u ≤ SZ p)
    (hv : v ≤ SZ p) (hw : w ≤ SZ p) : K * (u + v + w) ≤ SB p KS := by
  rw [SB]
  calc K * (u + v + w) ≤ KS * (3 * (SZ p)) := Nat.mul_le_mul hK (by omega)
    _ ≤ KS * (SZ p + 8) ^ 2 := Nat.mul_le_mul_left _ (by
        nlinarith [Nat.zero_le (SZ p), sq_nonneg (SZ p)])

theorem le_SB_sq {K KS p : ℕ} (hK : K ≤ KS) {u : ℕ} (hu : u ≤ SZ p) :
    K * u ^ 2 ≤ SB p KS := by
  rw [SB]
  calc K * u ^ 2 ≤ KS * (SZ p) ^ 2 := Nat.mul_le_mul hK (Nat.pow_le_pow_left hu 2)
    _ ≤ KS * (SZ p + 8) ^ 2 := Nat.mul_le_mul_left _ (by
        nlinarith [Nat.zero_le (SZ p), sq_nonneg (SZ p)])

theorem one_le_SZ (p : ℕ) : 1 ≤ SZ p := by simp only [SZ]; omega

theorem le_SB_roll {K KS p : ℕ} (hK : K ≤ KS) (h100 : 100 ≤ p) {A : List Val} {k : ℕ}
    (hk : k ≤ 7) (hAlen : A.length ≤ 8) (hA : ∀ v ∈ A, vsz v ≤ SZ p) :
    K * (k + 1) * (szl (A.take (k + 1)) + 1) ≤ SB p KS := by
  have hsum : szl (A.take (k + 1)) ≤ 8 * SZ p :=
    le_trans (szl_take_le_x2 A (k + 1))
      (le_trans (szl_le_len_mul hA) (Nat.mul_le_mul_right _ hAlen))
  have hle : 8 * (8 * SZ p + 1) ≤ (SZ p + 8) ^ 2 := by
    have h1 : 48 ≤ SZ p := by rw [SZ]; omega
    have h2 : (8 * (8 * (SZ p : ℤ) + 1)) ≤ ((SZ p : ℤ) + 8) ^ 2 := by
      nlinarith [h1, Nat.zero_le (SZ p)]
    exact_mod_cast h2
  rw [SB]
  calc K * (k + 1) * (szl (A.take (k + 1)) + 1) ≤ KS * 8 * (8 * SZ p + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul hK (by omega)) (by omega)
    _ = KS * (8 * (8 * SZ p + 1)) := by ring
    _ ≤ KS * (SZ p + 8) ^ 2 := Nat.mul_le_mul_left _ hle

/-! ## Elementary bounds used by the cost accounting -/

theorem toNat_le_natAbs (z : ℤ) : z.toNat ≤ z.natAbs := by
  rw [Int.toNat_le]
  exact Int.le_natAbs


theorem isz_le_SZ {p : ℕ} {z : ℤ} (h : z.natAbs < 2 ^ (8 * p + 6)) : isz z ≤ SZ p := by
  have h1 : z.natAbs.size ≤ 8 * p + 6 := Nat.size_le.mpr h
  simp only [isz, SZ]; omega

theorem natSqrt_lt_of_lt_sq {m B : ℕ} (h : m < B ^ 2) : Nat.sqrt m < B := by
  by_contra hc
  have h1 : B ≤ Nat.sqrt m := by omega
  have h2 : B * B ≤ Nat.sqrt m * Nat.sqrt m := Nat.mul_le_mul h1 h1
  have h3 := Nat.sqrt_le' m
  nlinarith [h2, h3]

theorem pow2_lt {a b : ℕ} (h : a < b) : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right one_lt_two h

theorem pow2_le {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

theorem isz_natCast_le_x2 {p n : ℕ} (h : n ≤ 8 * p + 6) : isz ((n : ℤ)) ≤ SZ p := by
  apply isz_le_SZ
  rw [Int.natAbs_natCast]
  exact lt_of_le_of_lt h (Nat.lt_two_pow_self (n := 8 * p + 6))

theorem isz_pow2_le {p k : ℕ} (h : k ≤ 8 * p + 5) : isz ((2 : ℤ) ^ k) ≤ SZ p := by
  apply isz_le_SZ
  have h2 : ((2 : ℤ) ^ k).natAbs = 2 ^ k := by
    rw [Int.natAbs_pow]
    norm_num
  rw [h2]
  exact lt_of_le_of_lt (pow2_le h) (pow2_lt (by omega))

theorem C0c_eq (p : ℕ) : C0c p = (2 : ℤ) ^ (8 * p + 1) := by
  simp only [C0c, qq]
  congr 1
  ring

theorem natAbs_C0c (p : ℕ) : (C0c p).natAbs = 2 ^ (8 * p + 1) := by
  rw [C0c_eq]
  simp only [Int.natAbs_pow]
  norm_num

theorem isz_C0c_le (p : ℕ) : isz (C0c p) ≤ SZ p := by
  apply isz_le_SZ
  rw [natAbs_C0c]
  exact pow2_lt (by omega)

theorem aval_natAbs_lt (p k : ℕ) : (aval p k).natAbs < 2 ^ (8 * p + 3) := by
  have h := (piIter p).1 k
  have hA : Aseq k < 2 := by simpa [Aseq] using Real.sqrtTwoAddSeries_lt_two k
  have h1 : (aval p k : ℝ) ≤ (2 : ℝ) ^ (2 * qq p) * Aseq k + 4 * (2 : ℝ) ^ (qq p) := by
    have h2 := abs_le.mp h
    linarith [h2.1]
  have hQ : (2 : ℝ) ^ (2 * qq p) = (2 : ℝ) ^ (8 * p) := by
    rw [show 2 * qq p = 8 * p by simp only [qq]; ring]
  have hr : (2 : ℝ) ^ (qq p) = (2 : ℝ) ^ (4 * p) := by
    rw [show qq p = 4 * p by simp only [qq]]
  have hbound : (aval p k : ℝ) < (2 : ℝ) ^ (8 * p + 3) := by
    have h3 : (2 : ℝ) ^ (2 * qq p) * Aseq k < (2 : ℝ) ^ (8 * p) * 2 := by
      rw [hQ]; exact mul_lt_mul_of_pos_left hA (by positivity)
    have h4 : 4 * (2 : ℝ) ^ (qq p) ≤ (2 : ℝ) ^ (8 * p + 2) := by
      rw [hr, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]
      apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      show 2 + 4 * p ≤ 8 * p + 2
      omega
    calc (aval p k : ℝ) ≤ (2 : ℝ) ^ (2 * qq p) * Aseq k + 4 * (2 : ℝ) ^ (qq p) := h1
      _ < (2 : ℝ) ^ (8 * p) * 2 + (2 : ℝ) ^ (8 * p + 2) := by linarith
      _ = (2 : ℝ) ^ (8 * p) * 6 := by
          rw [show (2 : ℝ) ^ (8 * p + 2) = 2 ^ (8 * p) * 4 by rw [pow_add]; norm_num]
          ring
      _ < (2 : ℝ) ^ (8 * p) * 8 := by
          exact mul_lt_mul_of_pos_left (by norm_num) (by positivity)
      _ = (2 : ℝ) ^ (8 * p + 3) := by rw [pow_add]; norm_num
  have hcast : (((aval p k).natAbs : ℕ) : ℝ) = (aval p k : ℝ) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg (sq_nonneg' p k)]
  have : (((aval p k).natAbs : ℕ) : ℝ) < (2 : ℝ) ^ (8 * p + 3) := by rw [hcast]; exact hbound
  exact_mod_cast this

theorem isz_aval_le (p k : ℕ) : isz (aval p k) ≤ SZ p := by
  apply isz_le_SZ
  exact lt_of_lt_of_le (aval_natAbs_lt p k) (pow2_le (by omega))

theorem sum_pow_lt {p : ℕ} : 2 ^ (8 * p + 1) + 2 ^ (8 * p + 3) < 2 ^ (8 * p + 4) := by
  have h1 : 2 ^ (8 * p + 1) < 2 ^ (8 * p + 3) := pow2_lt (by omega)
  have h2 : 2 ^ (8 * p + 3) + 2 ^ (8 * p + 3) = 2 ^ (8 * p + 4) := by
    rw [← two_mul, mul_comm, ← pow_succ]
  omega

theorem natAbs_add_lt {a b : ℤ} {p : ℕ} (ha : a.natAbs ≤ 2 ^ (8 * p + 1))
    (hb : b.natAbs ≤ 2 ^ (8 * p + 3)) : (a + b).natAbs < 2 ^ (8 * p + 4) := by
  have h1 : (a + b).natAbs ≤ a.natAbs + b.natAbs := Int.natAbs_add_le _ _
  have h2 : a.natAbs + b.natAbs ≤ 2 ^ (8 * p + 1) + 2 ^ (8 * p + 3) :=
    Nat.add_le_add ha hb
  exact lt_of_le_of_lt (le_trans h1 h2) sum_pow_lt

theorem isz_C0c_add_aval_le (p k : ℕ) : isz (C0c p + aval p k) ≤ SZ p := by
  apply isz_le_SZ
  exact lt_of_lt_of_le
    (natAbs_add_lt (le_of_eq (natAbs_C0c p)) (le_of_lt (aval_natAbs_lt p k)))
    (pow2_le (by omega))

theorem sqrt_lt_two_pow {m p : ℕ} (hm : m < 2 ^ (8 * p + 4)) : Nat.sqrt m ≤ 2 ^ (4 * p + 2) := by
  have h4 : (2 ^ (4 * p + 2)) ^ 2 = 2 ^ (8 * p + 4) := by
    rw [← pow_mul]; congr 1; ring
  exact le_of_lt (natSqrt_lt_of_lt_sq (by rw [h4]; exact hm))

theorem isz_sqrt_C0c_aval_le (p k : ℕ) :
    isz ((Nat.sqrt ((C0c p + aval p k).toNat) : ℤ)) ≤ SZ p := by
  apply isz_le_SZ
  have h1 : (C0c p + aval p k).toNat ≤ (C0c p + aval p k).natAbs := toNat_le_natAbs _
  have h2 : (C0c p + aval p k).natAbs < 2 ^ (8 * p + 4) :=
    natAbs_add_lt (le_of_eq (natAbs_C0c p)) (le_of_lt (aval_natAbs_lt p k))
  have h3 : Nat.sqrt ((C0c p + aval p k).toNat) ≤ 2 ^ (4 * p + 2) :=
    sqrt_lt_two_pow (lt_of_le_of_lt h1 h2)
  calc ((Nat.sqrt ((C0c p + aval p k).toNat) : ℤ)).natAbs
      = Nat.sqrt ((C0c p + aval p k).toNat) := Int.natAbs_natCast _
    _ ≤ 2 ^ (4 * p + 2) := h3
    _ < 2 ^ (8 * p + 6) := pow2_lt (by omega)

theorem isz_mul_pow2_le (p : ℕ) {d : ℤ} (hd : d.natAbs ≤ 2 ^ (4 * p + 2)) :
    isz (d * 2 ^ (qq p)) ≤ SZ p := by
  apply isz_le_SZ
  have h1 : (d * 2 ^ (qq p)).natAbs = d.natAbs * 2 ^ qq p := by
    rw [Int.natAbs_mul]
    simp only [Int.natAbs_pow]
    norm_num
  rw [h1]
  have h3 : (2 : ℕ) ^ qq p = 2 ^ (4 * p) := by
    rw [show qq p = 4 * p by simp only [qq]]
  rw [h3]
  calc d.natAbs * 2 ^ (4 * p) ≤ 2 ^ (4 * p + 2) * 2 ^ (4 * p) := Nat.mul_le_mul_right _ hd
    _ = 2 ^ (8 * p + 2) := by rw [← pow_add]; congr 1; ring
    _ < 2 ^ (8 * p + 6) := pow2_lt (by omega)

theorem natAbs_Dval_le (p : ℕ) : (Dval p).natAbs ≤ 2 ^ (4 * p + 2) := by
  have h1 : (C0c p - aval p p).toNat ≤ (C0c p - aval p p).natAbs := toNat_le_natAbs _
  have h2 : (C0c p - aval p p).natAbs ≤ (C0c p).natAbs + (aval p p).natAbs :=
    Int.natAbs_sub_le _ _
  have h3 : (C0c p).natAbs + (aval p p).natAbs < 2 ^ (8 * p + 4) := by
    rw [natAbs_C0c]
    exact lt_of_lt_of_le (Nat.add_lt_add_left (aval_natAbs_lt p p) _) (le_of_lt sum_pow_lt)
  calc (Dval p).natAbs = Nat.sqrt ((C0c p - aval p p).toNat) := Int.natAbs_natCast _
    _ ≤ 2 ^ (4 * p + 2) := sqrt_lt_two_pow (lt_of_le_of_lt (le_trans h1 h2) h3)

theorem isz_Dval_le (p : ℕ) : isz (Dval p) ≤ SZ p := by
  apply isz_le_SZ
  exact lt_of_le_of_lt (natAbs_Dval_le p) (pow2_lt (by omega))

theorem isz_Dval_mul_le (p : ℕ) : isz (Dval p * 2 ^ (2 * p + 1)) ≤ SZ p := by
  apply isz_le_SZ
  have h1 : (Dval p * 2 ^ (2 * p + 1)).natAbs = (Dval p).natAbs * 2 ^ (2 * p + 1) := by
    rw [Int.natAbs_mul]
    simp only [Int.natAbs_pow]
    norm_num
  rw [h1]
  calc (Dval p).natAbs * 2 ^ (2 * p + 1) ≤ 2 ^ (4 * p + 2) * 2 ^ (2 * p + 1) :=
        Nat.mul_le_mul_right _ (natAbs_Dval_le p)
    _ = 2 ^ (6 * p + 3) := by rw [← pow_add]; congr 1; ring
    _ < 2 ^ (8 * p + 6) := pow2_lt (by omega)

theorem natAbs_pow_qq_le (p : ℕ) : (((2 : ℤ) ^ (qq p - 1)).natAbs) ≤ 2 ^ (6 * p + 3) := by
  have h4 : ((2 : ℤ) ^ (qq p - 1)).natAbs = 2 ^ (qq p - 1) := by
    simp only [Int.natAbs_pow]
    norm_num
  rw [h4]
  apply pow2_le
  simp only [qq]
  omega

theorem isz_Nval_le (p : ℕ) : isz (Nval p) ≤ SZ p := by
  apply isz_le_SZ
  have h1 : (Dval p * 2 ^ (2 * p + 1)).natAbs ≤ 2 ^ (6 * p + 3) := by
    rw [Int.natAbs_mul]
    simp only [Int.natAbs_pow]
    norm_num
    calc (Dval p).natAbs * 2 ^ (2 * p + 1) ≤ 2 ^ (4 * p + 2) * 2 ^ (2 * p + 1) :=
          Nat.mul_le_mul_right _ (natAbs_Dval_le p)
      _ = 2 ^ (6 * p + 3) := by rw [← pow_add]; congr 1; ring
  have h4 : ((2 : ℤ) ^ (qq p - 1)).natAbs ≤ 2 ^ (6 * p + 3) := natAbs_pow_qq_le p
  rw [Nval]
  calc (Dval p * 2 ^ (2 * p + 1) + 2 ^ (qq p - 1)).natAbs
      ≤ (Dval p * 2 ^ (2 * p + 1)).natAbs + ((2 : ℤ) ^ (qq p - 1)).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ 2 ^ (6 * p + 3) + 2 ^ (6 * p + 3) := Nat.add_le_add h1 h4
    _ = 2 * 2 ^ (6 * p + 3) := by ring
    _ = 2 ^ (6 * p + 4) := by rw [pow_succ]; ring
    _ < 2 ^ (8 * p + 6) := pow2_lt (by omega)

theorem SB_le (p KS : ℕ) (h100 : 100 ≤ p) : SB p KS ≤ 256 * KS * (p + 1) ^ 2 := by
  rw [SB, SZ]
  have h1 : 8 * p + 8 + 8 = 8 * (p + 2) := by ring
  rw [h1]
  have h2 : (8 * (p + 2)) ^ 2 ≤ 256 * (p + 1) ^ 2 := by nlinarith
  calc KS * (8 * (p + 2)) ^ 2 ≤ KS * (256 * (p + 1) ^ 2) := Nat.mul_le_mul_left _ h2
    _ = 256 * KS * (p + 1) ^ 2 := by ring

theorem pow_bound (M p : ℕ) (hM : 1 ≤ M) (hp : 2 ≤ p + 1) :
    M * (p + 1) ^ 3 ≤ (4 * M + 1) * (p + 1) ^ (4 * M + 1) := by
  have h1 : (p + 1) ^ (4 * M + 1) = (p + 1) ^ 3 * (p + 1) ^ (4 * M - 2) := by
    rw [← pow_add]; congr 1; omega
  rw [h1]
  have h2 : M ≤ (p + 1) ^ (4 * M - 2) := by
    have h3 : (2 : ℕ) ^ (4 * M - 2) ≤ (p + 1) ^ (4 * M - 2) := Nat.pow_le_pow_left hp _
    have h4 : M ≤ 2 ^ (4 * M - 2) := by
      have h5 := Nat.lt_two_pow_self (n := 4 * M - 2)
      omega
    exact le_trans h4 h3
  calc M * (p + 1) ^ 3 ≤ (p + 1) ^ (4 * M - 2) * (p + 1) ^ 3 := Nat.mul_le_mul_right _ h2
    _ = (p + 1) ^ 3 * (p + 1) ^ (4 * M - 2) := by ring
    _ ≤ (4 * M + 1) * ((p + 1) ^ 3 * (p + 1) ^ (4 * M - 2)) :=
        Nat.le_mul_of_pos_left _ (by omega)

/-- The sandwich `2^{2p}(2 - Aseq p) ≥ 1`. -/
theorem two_sub_Aseq_ge (p : ℕ) (hp : 1 ≤ p) : 1 ≤ (2 : ℝ) ^ (2 * p) * (2 - Aseq p) := by
  have hlt : Real.pi < 2 ^ (p + 1) * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 p) + 1 / 4 ^ p :=
    Real.pi_lt_sqrtTwoAddSeries p
  have hA : Aseq p = Real.sqrtTwoAddSeries 0 p := rfl
  have h4 : (1 : ℝ) / 4 ^ p ≤ 1 / 4 := by
    have h5 : (4 : ℝ) ^ 1 ≤ 4 ^ p := pow_le_pow_right₀ (by norm_num) hp
    rw [pow_one] at h5
    exact one_div_le_one_div_of_le (by norm_num) h5
  have h6 : 1 ≤ (2 : ℝ) ^ p * Real.sqrt (2 - Aseq p) := by
    rw [← hA] at hlt
    have h7 : 2 ^ (p + 1) * Real.sqrt (2 - Aseq p) > 11 / 4 := by
      have hp3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
      linarith
    have h8 : (2 : ℝ) ^ p * Real.sqrt (2 - Aseq p)
        = 2 ^ (p + 1) * Real.sqrt (2 - Aseq p) / 2 := by
      rw [pow_succ]; ring
    rw [h8]
    linarith
  have h10 : (2 : ℝ) ^ (2 * p) * (2 - Aseq p)
      = ((2 : ℝ) ^ p * Real.sqrt (2 - Aseq p)) ^ 2 := by
    have hx : 0 ≤ 2 - Aseq p := by
      have hh := Real.sqrtTwoAddSeries_lt_two p
      simp only [Aseq]; linarith
    calc (2 : ℝ) ^ (2 * p) * (2 - Aseq p)
        = (2 : ℝ) ^ (p * 2) * (2 - Aseq p) := by congr 1; ring
      _ = ((2 : ℝ) ^ p) ^ 2 * (2 - Aseq p) := by rw [pow_mul]
      _ = ((2 : ℝ) ^ p) ^ 2 * (Real.sqrt (2 - Aseq p)) ^ 2 := by rw [Real.sq_sqrt hx]
      _ = ((2 : ℝ) ^ p * Real.sqrt (2 - Aseq p)) ^ 2 := by rw [mul_pow]
  rw [h10]
  nlinarith [h6]

/-- `C0c p - aval p p ≥ 0`: the final square root is well defined. -/
theorem C0c_sub_aval_nonneg (p : ℕ) (h100 : 100 ≤ p) : 0 ≤ C0c p - aval p p := by
  have herr := (piIter p).1 p
  have hge := two_sub_Aseq_ge p (by omega)
  have h1 : (aval p p : ℝ) ≤ (2 : ℝ) ^ (2 * qq p) * Aseq p + 4 * (2 : ℝ) ^ (qq p) := by
    have h2 := abs_le.mp herr
    linarith [h2.1]
  have hQ : (2 : ℝ) ^ (2 * qq p) = (2 : ℝ) ^ (8 * p) := by
    rw [show 2 * qq p = 8 * p by simp only [qq]; ring]
  have hr : (2 : ℝ) ^ (qq p) = (2 : ℝ) ^ (4 * p) := by
    rw [show qq p = 4 * p by simp only [qq]]
  have h7 : 1 / (2 : ℝ) ^ (2 * p) ≤ 2 - Aseq p := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (2 * p))]
    calc (1 : ℝ) ≤ (2 : ℝ) ^ (2 * p) * (2 - Aseq p) := hge
      _ = (2 - Aseq p) * (2 : ℝ) ^ (2 * p) := by ring
  have h10 : (2 : ℝ) ^ (8 * p) * Aseq p ≤ (2 : ℝ) ^ (8 * p) * (2 - 1 / (2 : ℝ) ^ (2 * p)) := by
    have h11 : Aseq p ≤ 2 - 1 / (2 : ℝ) ^ (2 * p) := by linarith
    exact mul_le_mul_of_nonneg_left h11 (by positivity)
  have h12 : (2 : ℝ) ^ (8 * p) * (1 / (2 : ℝ) ^ (2 * p)) = (2 : ℝ) ^ (6 * p) := by
    have hpow : (2 : ℝ) ^ (8 * p) = (2 : ℝ) ^ (6 * p) * (2 : ℝ) ^ (2 * p) := by
      rw [← pow_add]; congr 1; ring
    rw [hpow, one_div, mul_assoc, mul_inv_cancel₀ (by positivity : (2 : ℝ) ^ (2 * p) ≠ 0),
      mul_one]
  have h13 : (2 : ℝ) ^ (6 * p) > 4 * (2 : ℝ) ^ (qq p) := by
    rw [hr, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  have h14 : (aval p p : ℝ) < (2 : ℝ) ^ (8 * p + 1) := by
    rw [hQ] at h1
    have h15 : (2 : ℝ) ^ (8 * p) * (2 - 1 / (2 : ℝ) ^ (2 * p))
        = (2 : ℝ) ^ (8 * p + 1) - (2 : ℝ) ^ (6 * p) := by
      rw [mul_sub, h12, ← pow_succ]
    linarith [h1, h10, h15, h13]
  have h16 : aval p p < C0c p := by
    rw [C0c_eq]
    exact_mod_cast h14
  omega

theorem Pipe.pushOnAny {main prog : Cmd} {v : Val} {c : ℕ} {T : List Val}
    (h : WordR main prog (fun _ => True) (fun vs out => out = v :: vs) (fun _ => c)) :
    Pipe main prog T (v :: T) c := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h vs trivial s R hR
  exact ⟨out, s', n, by rw [hout, hvs]; rfl, hev, hn, hstk, hoth⟩

theorem vsz_mem_le3 {p : ℕ} {a b c : ℤ} (ha : vsz (HvdH.Val.int a) ≤ SZ p) (hb : vsz (HvdH.Val.int b) ≤ SZ p)
    (hc : vsz (HvdH.Val.int c) ≤ SZ p) : ∀ v ∈ ([.int a, .int b, .int c] : List Val), vsz v ≤ SZ p := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with h | h | h
  · rw [h]; exact ha
  · rw [h]; exact hb
  · rw [h]; exact hc

theorem vsz_mem_le4 {p : ℕ} {a b c d : ℤ} (ha : vsz (HvdH.Val.int a) ≤ SZ p) (hb : vsz (HvdH.Val.int b) ≤ SZ p)
    (hc : vsz (HvdH.Val.int c) ≤ SZ p) (hd : vsz (HvdH.Val.int d) ≤ SZ p) :
    ∀ v ∈ ([.int a, .int b, .int c, .int d] : List Val), vsz v ≤ SZ p := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with h | h | h | h
  · rw [h]; exact ha
  · rw [h]; exact hb
  · rw [h]; exact hc
  · rw [h]; exact hd

theorem vsz_mem_le5 {p : ℕ} {a b c d e : ℤ} (ha : vsz (HvdH.Val.int a) ≤ SZ p) (hb : vsz (HvdH.Val.int b) ≤ SZ p)
    (hc : vsz (HvdH.Val.int c) ≤ SZ p) (hd : vsz (HvdH.Val.int d) ≤ SZ p) (he : vsz (HvdH.Val.int e) ≤ SZ p) :
    ∀ v ∈ ([.int a, .int b, .int c, .int d, .int e] : List Val), vsz v ≤ SZ p := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with h | h | h | h | h
  · rw [h]; exact ha
  · rw [h]; exact hb
  · rw [h]; exact hc
  · rw [h]; exact hd
  · rw [h]; exact he

theorem vsz_mem_le_append {p : ℕ} {A B : List Val} (hA : ∀ v ∈ A, vsz v ≤ SZ p)
    (hB : ∀ v ∈ B, vsz v ≤ SZ p) : ∀ v ∈ A ++ B, vsz v ≤ SZ p := by
  intro v hv
  rcases List.mem_append.mp hv with h | h
  · exact hA v h
  · exact hB v h

theorem natAbs_sqrt_C0c_aval_le (p k : ℕ) :
    ((Nat.sqrt ((C0c p + aval p k).toNat) : ℤ)).natAbs ≤ 2 ^ (4 * p + 2) := by
  have h1 : (C0c p + aval p k).toNat ≤ (C0c p + aval p k).natAbs := toNat_le_natAbs _
  have h2 : (C0c p + aval p k).natAbs < 2 ^ (8 * p + 4) :=
    natAbs_add_lt (le_of_eq (natAbs_C0c p)) (le_of_lt (aval_natAbs_lt p k))
  have h3 : Nat.sqrt ((C0c p + aval p k).toNat) ≤ 2 ^ (4 * p + 2) :=
    sqrt_lt_two_pow (lt_of_le_of_lt h1 h2)
  rw [Int.natAbs_natCast]
  exact h3

theorem natAbs_q_sub_one (p : ℕ) : ((((qq p : ℕ) : ℤ) - 1)).natAbs ≤ 2 ^ (6 * p + 3) := by
  have h1 : (((qq p : ℕ) : ℤ) - 1).natAbs ≤ ((qq p : ℕ) : ℤ).natAbs + (1 : ℤ).natAbs :=
    Int.natAbs_sub_le _ _
  have h2 : ((qq p : ℕ) : ℤ).natAbs = qq p := Int.natAbs_natCast _
  rw [h2] at h1
  simp only [Int.natAbs_one] at h1
  refine le_trans h1 ?_
  have h3 : qq p + 1 ≤ 6 * p + 3 := by simp only [qq]; omega
  exact le_trans h3 (le_of_lt (Nat.lt_two_pow_self (n := 6 * p + 3)))

theorem isz_q_sub_one (p : ℕ) : isz (((qq p : ℕ) : ℤ) - 1) ≤ SZ p := by
  apply isz_le_SZ
  have h1 := natAbs_q_sub_one p
  rw [show 6 * p + 3 = 6 * p + 3 by rfl] at h1
  exact lt_of_le_of_lt h1 (pow2_lt (by omega))


theorem toNat_eq_of_eq {a : ℤ} {n : ℕ} (h : a = (n : ℤ)) : a.toNat = n := by
  rw [h]
  have h3 : ((((n : ℕ) : ℤ)).toNat : ℤ) = ((n : ℕ) : ℤ) := Int.toNat_of_nonneg (by simp)
  exact_mod_cast h3

/-- The value computed by the body's square-root step. -/
def dd (p i : ℕ) : ℤ :=
  (Nat.sqrt ((C0c p + aval p i).toNat) : ℤ) * 2 ^ (((qq p : ℕ) : ℤ)).toNat

theorem dd_eq (p i : ℕ) : dd p i = astep p (aval p i) := by
  have h : (((qq p : ℕ) : ℤ)).toNat = qq p := toNat_eq_of_eq rfl
  rw [dd, h, astep]
  ring

/-- `q = 4p` as computed by the pre-loop from a copy of `p`. -/
def xv (p : ℕ) : ℤ := (p : ℤ) * 2 ^ ((2 : ℤ).toNat)

theorem xv_eq (p : ℕ) : xv p = ((qq p : ℕ) : ℤ) := by
  have h : ((2 : ℤ)).toNat = 2 := toNat_eq_of_eq (by norm_num)
  rw [xv, h, qq]
  push_cast
  ring

/-- `2^(8p+1)` as computed by the pre-loop. -/
def Cv (p : ℕ) : ℤ := (2 : ℤ) ^ ((1 + (xv p + xv p)).toNat)

theorem xv2_eq (p : ℕ) : xv p + xv p = ((2 * qq p : ℕ) : ℤ) := by
  rw [xv_eq]
  push_cast [qq]
  ring

theorem Cv_eq (p : ℕ) : Cv p = C0c p := by
  have h : ((1 + (xv p + xv p))).toNat = 8 * p + 1 := by
    apply toNat_eq_of_eq
    rw [xv2_eq]
    push_cast [qq]
    ring
  rw [Cv, h, C0c_eq]

/-- The value computed by the final part of the program. -/
def ucomp (p : ℕ) : ℤ :=
  ((2 : ℤ) ^ ((((qq p : ℕ) : ℤ) - 1)).toNat
    + (Nat.sqrt ((C0c p - aval p p).toNat) : ℤ) * 2 ^ ((1 + ((p : ℤ) + (p : ℤ))).toNat)).fdiv
    (2 ^ (((qq p : ℕ) : ℤ)).toNat)

theorem ucomp_eq (p : ℕ) (hp : 1 ≤ p) : ucomp p = uval p := by
  have h1 : ((((qq p : ℕ) : ℤ) - 1)).toNat = qq p - 1 := by
    apply toNat_eq_of_eq
    have h2 : (1 : ℕ) ≤ qq p := by simp only [qq]; omega
    push_cast
    rw [Nat.cast_sub h2]
    ring
  have h4 : ((1 + ((p : ℤ) + (p : ℤ))).toNat) = 2 * p + 1 := by
    apply toNat_eq_of_eq
    push_cast
    ring
  have h6 : ((((qq p : ℕ) : ℤ)).toNat) = qq p := toNat_eq_of_eq rfl
  rw [ucomp, uval, Nval, Dval, h1, h4, h6]
  rw [add_comm]

theorem isz_dd_le (p i : ℕ) : isz (dd p i) ≤ SZ p := by
  have h : (((qq p : ℕ) : ℤ)).toNat = qq p := toNat_eq_of_eq rfl
  rw [dd, h]
  exact isz_mul_pow2_le p (natAbs_sqrt_C0c_aval_le p i)

theorem isz_xv_le (p : ℕ) : isz (xv p) ≤ SZ p := by
  rw [xv_eq]
  exact isz_natCast_le_x2 (by simp only [qq]; omega)

theorem isz_Cv_le (p : ℕ) : isz (Cv p) ≤ SZ p := by
  rw [Cv_eq]
  exact isz_C0c_le p

theorem isz_xv2_le (p : ℕ) : isz (xv p + xv p) ≤ SZ p := by
  rw [xv2_eq]
  exact isz_natCast_le_x2 (by simp only [qq]; omega)

theorem isz_xv3_le (p : ℕ) : isz (1 + (xv p + xv p)) ≤ SZ p := by
  have h : 1 + (xv p + xv p) = ((2 * qq p + 1 : ℕ) : ℤ) := by
    rw [xv2_eq]
    push_cast
    ring
  rw [h]
  exact isz_natCast_le_x2 (by simp only [qq]; omega)

theorem C0c_add_aval_nonneg (p i : ℕ) : (0 : ℤ) ≤ C0c p + aval p i := by
  have h1 : (0 : ℤ) ≤ C0c p := by rw [C0c]; positivity
  have h2 := sq_nonneg' p i
  linarith

theorem Pipe.pickAt {prog : ℕ → Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A : List Val} {k : ℕ} (hk : k < A.length) {v : Val} (hv : A.getD k .nil = v) :
    Pipe main (prog k) A (v :: A) (K * (k + 1) * (szl (A.take (k + 1)) + 1)) := by
  refine Pipe.rw (Pipe.pick main h hk) ?_
  rw [hv]

theorem two_le_SZ (p : ℕ) : 2 ≤ SZ p := by simp only [SZ]; omega

theorem toNat_two_le (p : ℕ) : ((2 : ℤ)).toNat ≤ SZ p := by
  rw [toNat_eq_of_eq (n := 2) (by norm_num)]; exact two_le_SZ p

theorem vsz_int_le {p : ℕ} {z : ℤ} (h : isz z ≤ SZ p) : vsz (HvdH.Val.int z) ≤ SZ p := by
  simpa [vsz_int] using h

theorem vsz_mem_le1 {p : ℕ} {a : ℤ} (ha : vsz (HvdH.Val.int a) ≤ SZ p) :
    ∀ v ∈ ([.int a] : List Val), vsz v ≤ SZ p := by
  intro v hv
  simp only [List.mem_singleton] at hv
  rw [hv]; simpa [vsz_int] using ha

theorem vsz_mem_le2 {p : ℕ} {a b : ℤ} (ha : vsz (HvdH.Val.int a) ≤ SZ p) (hb : vsz (HvdH.Val.int b) ≤ SZ p) :
    ∀ v ∈ ([.int a, .int b] : List Val), vsz v ≤ SZ p := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with h | h
  · rw [h]; exact ha
  · rw [h]; exact hb

theorem natAbs_fdiv_le {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) : (a.fdiv b).natAbs ≤ a.natAbs := by
  have h1 : a.fdiv b = a / b := by
    rw [Int.fdiv_eq_ediv, if_pos (Or.inl (le_of_lt hb)), sub_zero]
  have h2 : 0 ≤ a / b := Int.ediv_nonneg ha (le_of_lt hb)
  have h3 : a / b ≤ a := Int.ediv_le_self b ha
  have h4 : ((a / b).natAbs : ℤ) ≤ (a.natAbs : ℤ) := by
    rw [Int.natAbs_of_nonneg h2, Int.natAbs_of_nonneg ha]
    exact h3
  rw [h1]
  exact_mod_cast h4

theorem toNat_q (p : ℕ) : (((qq p : ℕ) : ℤ)).toNat = qq p := toNat_eq_of_eq rfl

theorem toNat_q_sub_one (p : ℕ) (hp : 1 ≤ p) : ((((qq p : ℕ) : ℤ) - 1)).toNat = qq p - 1 := by
  apply toNat_eq_of_eq
  have h2 : (1 : ℕ) ≤ qq p := by simp only [qq]; omega
  push_cast
  rw [Nat.cast_sub h2]
  ring

theorem toNat_two_p_one (p : ℕ) : ((1 + ((p : ℤ) + (p : ℤ))).toNat) = 2 * p + 1 := by
  apply toNat_eq_of_eq
  push_cast
  ring

/-- The `2^(qq p - 1) + Dval·2^(2p+1)` term as computed by the program. -/
def Nt (p : ℕ) : ℤ := (2 : ℤ) ^ ((((qq p : ℕ) : ℤ) - 1)).toNat
  + (Nat.sqrt ((C0c p - aval p p).toNat) : ℤ) * 2 ^ ((1 + ((p : ℤ) + (p : ℤ))).toNat)

theorem Nt_eq (p : ℕ) (hp : 1 ≤ p) : Nt p = Nval p := by
  simp only [Nt, Dval, Nval, toNat_q_sub_one p hp, toNat_two_p_one p]
  ring

theorem Dm_eq (p : ℕ) : (Nat.sqrt ((C0c p - aval p p).toNat) : ℤ)
    * 2 ^ ((1 + ((p : ℤ) + (p : ℤ))).toNat) = Dval p * 2 ^ (2 * p + 1) := by
  rw [toNat_two_p_one p, Dval]

theorem isz_Dm_le (p : ℕ) : isz ((Nat.sqrt ((C0c p - aval p p).toNat) : ℤ)
    * 2 ^ ((1 + ((p : ℤ) + (p : ℤ))).toNat)) ≤ SZ p := by
  rw [Dm_eq]
  exact isz_Dval_mul_le p

theorem isz_Dv_le (p : ℕ) : isz ((Nat.sqrt ((C0c p - aval p p).toNat) : ℤ)) ≤ SZ p :=
  isz_Dval_le p

theorem natAbs_Nval_le (p : ℕ) : (Nval p).natAbs ≤ 2 ^ (6 * p + 4) := by
  have h1 : (Dval p * 2 ^ (2 * p + 1)).natAbs ≤ 2 ^ (6 * p + 3) := by
    rw [Int.natAbs_mul]
    simp only [Int.natAbs_pow]
    norm_num
    calc (Dval p).natAbs * 2 ^ (2 * p + 1) ≤ 2 ^ (4 * p + 2) * 2 ^ (2 * p + 1) :=
          Nat.mul_le_mul_right _ (natAbs_Dval_le p)
      _ = 2 ^ (6 * p + 3) := by rw [← pow_add]; congr 1; ring
  have h4 : ((2 : ℤ) ^ (qq p - 1)).natAbs ≤ 2 ^ (6 * p + 3) := natAbs_pow_qq_le p
  rw [Nval]
  calc (Dval p * 2 ^ (2 * p + 1) + 2 ^ (qq p - 1)).natAbs
      ≤ (Dval p * 2 ^ (2 * p + 1)).natAbs + ((2 : ℤ) ^ (qq p - 1)).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ 2 ^ (6 * p + 3) + 2 ^ (6 * p + 3) := Nat.add_le_add h1 h4
    _ = 2 * 2 ^ (6 * p + 3) := by ring
    _ = 2 ^ (6 * p + 4) := by rw [pow_succ]; ring

theorem natAbs_Nval_lt (p : ℕ) : (Nval p).natAbs < 2 ^ (8 * p + 6) :=
  lt_of_le_of_lt (natAbs_Nval_le p) (pow2_lt (by omega))

theorem isz_C0c_sub_aval_le (p : ℕ) : isz (C0c p - aval p p) ≤ SZ p := by
  apply isz_le_SZ
  have h1 : (C0c p - aval p p).natAbs ≤ (C0c p).natAbs + (aval p p).natAbs :=
    Int.natAbs_sub_le _ _
  have h2 : (C0c p).natAbs + (aval p p).natAbs < 2 ^ (8 * p + 4) := by
    rw [natAbs_C0c]
    exact lt_of_lt_of_le (Nat.add_lt_add_left (aval_natAbs_lt p p) _) (le_of_lt sum_pow_lt)
  exact lt_of_le_of_lt h1 (lt_trans h2 (pow2_lt (by omega)))

theorem Nval_pos (p : ℕ) : 0 < Nval p := by
  rw [Nval]
  have h1 : (0 : ℤ) < (2 : ℤ) ^ (qq p - 1) := pow_pos (by norm_num) _
  have h2 : (0 : ℤ) ≤ Dval p * 2 ^ (2 * p + 1) := by
    rw [Dval]; positivity
  linarith

theorem isz_Nt_le (p : ℕ) (hp : 1 ≤ p) : isz (Nt p) ≤ SZ p := by
  rw [Nt_eq p hp]
  exact isz_Nval_le p

theorem isz_u_le (p : ℕ) (hp : 1 ≤ p) :
    isz (Int.fdiv (Nt p) (2 ^ (((qq p : ℕ) : ℤ)).toNat)) ≤ SZ p := by
  apply isz_le_SZ
  have hb : (0 : ℤ) < 2 ^ (((qq p : ℕ) : ℤ)).toNat := pow_pos (by norm_num) _
  have h1 : (Int.fdiv (Nt p) (2 ^ (((qq p : ℕ) : ℤ)).toNat)).natAbs ≤ (Nt p).natAbs :=
    natAbs_fdiv_le (le_of_lt (by rw [Nt_eq p hp]; exact Nval_pos p)) hb
  have h2 : (Nt p).natAbs < 2 ^ (8 * p + 6) := by
    rw [Nt_eq p hp]
    exact natAbs_Nval_lt p
  exact lt_of_le_of_lt h1 h2


/-- Fixed-point computation of `π` (paper §2.8): given the precision `p ≥ 100`, produce an integer
`u` with `|u - 2^p π| ≤ 1`, i.e. `u/2^p` approximates `π` within one unit in the last place.
Cost polynomial in `p`. Suggested route: Machin's formula or the nested-square-root sequence
`a_{n+1} = sqrt(2+a_n)` (`Real.pi_gt_sqrtTwoAddSeries`/`Real.pi_lt_sqrtTwoAddSeries` sandwich
`π` between `2^{n+1} sqrt(2-a_n)` and that plus `4^-n`), evaluated in fixed point with `hi.sqrt`,
`hi.mulS`, `hi.tdiv`, `hi.shl`, `hi.add`, `hi.sub` and the generic words of `hk`; the helper
framework in `FxCommon` (`Spec`, `Spec.seq`, `Spec.binOp`, ...) composes `WordR` words. -/
theorem piWord (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ), 100 ≤ p →
      HvdH.WordR main prog (fun vs => ∃ (rest : List HvdH.Val), vs = HvdH.Val.int (p : ℤ) :: rest)
        (fun vs out => ∃ (rest : List HvdH.Val) (u : ℤ), vs = HvdH.Val.int (p : ℤ) :: rest ∧
          out = HvdH.Val.int u :: rest ∧ |(u : ℝ) - 2 ^ p * Real.pi| ≤ 1)
        (fun _ => K * (p + 1) ^ K) := by
  obtain ⟨pushProg, Kpush, hPush⟩ := hk.pushVal
  obtain ⟨swapProg, Kswap, hSwap⟩ := hk.swap
  obtain ⟨dropProg, Kdrop, hDrop⟩ := hk.drop
  obtain ⟨pickProg, Kpick, hPick⟩ := hk.pick
  obtain ⟨comb, Kloop, hLoop⟩ := hk.loop
  obtain ⟨addProg, Kadd, hAdd⟩ := hi.add
  obtain ⟨subProg, Ksub, hSub⟩ := hi.sub
  obtain ⟨sqrtProg, Ksqrt, hSqrt⟩ := hi.sqrt
  obtain ⟨shlProg, Kshl, hShl⟩ := hi.shl
  obtain ⟨shrFProg, KshrF, hShrF⟩ := hi.shrF
  obtain ⟨ltProg, Klt, hLt⟩ := hi.lt
  obtain ⟨pow2Prog, Kpow2, hPow2⟩ := hi.pow2
  set KS : ℕ := Kpush + Kswap + Kdrop + Kpick + Kloop + Kadd + Ksub + Ksqrt + Kshl + KshrF + Klt
    + Kpow2 + 1 with hKSdef
  have hKpush : Kpush ≤ KS := by omega
  have hKswap : Kswap ≤ KS := by omega
  have hKdrop : Kdrop ≤ KS := by omega
  have hKpick : Kpick ≤ KS := by omega
  have hKloop : Kloop ≤ KS := by omega
  have hKadd : Kadd ≤ KS := by omega
  have hKsub : Ksub ≤ KS := by omega
  have hKsqrt : Ksqrt ≤ KS := by omega
  have hKshl : Kshl ≤ KS := by omega
  have hKshrF : KshrF ≤ KS := by omega
  have hKlt : Klt ≤ KS := by omega
  have hKpow2 : Kpow2 ≤ KS := by omega
  have hKS1 : 1 ≤ KS := by omega
  let body : Cmd :=
    .seq (pickProg 2) (.seq addProg (.seq sqrtProg (.seq (pickProg 3) (.seq swapProg
      (.seq shlProg (.seq swapProg (.seq (pushProg (Val.int 1)) (.seq swapProg
      (.seq subProg (.seq swapProg (.seq (pickProg 1) (.seq (pushProg (Val.int 0))
      ltProg))))))))))))
  let pre : Cmd :=
    .seq (pickProg 0) (.seq (pushProg (Val.int 2)) (.seq swapProg (.seq shlProg
      (.seq (pickProg 0) (.seq (pickProg 0) (.seq addProg (.seq (pushProg (Val.int 1))
      (.seq addProg (.seq pow2Prog (.seq (pickProg 2) (pushProg (Val.int 0))))))))))))
  let fin1 : Cmd :=
    .seq swapProg (.seq dropProg (.seq (pickProg 1) (.seq subProg (.seq sqrtProg
      (.seq (pickProg 3) (.seq (pickProg 4) (.seq addProg (pushProg (Val.int 1)))))))))
  let fin2 : Cmd :=
    .seq addProg (.seq swapProg (.seq shlProg (.seq (pickProg 2) (.seq (pushProg (Val.int 1))
      (.seq swapProg (.seq subProg (.seq pow2Prog addProg)))))))
  let fin3 : Cmd :=
    .seq (pickProg 2) (.seq swapProg (.seq shrFProg (.seq swapProg (.seq dropProg
      (.seq swapProg (.seq dropProg (.seq swapProg dropProg)))))))
  let fin : Cmd := .seq fin1 (.seq fin2 fin3)
  refine ⟨Cmd.seq pre (Cmd.seq (comb body) fin), 4 * (20000 * KS) + 1, ?_⟩
  intro main p h100
  have hp1 : 1 ≤ p := by omega
  have hsz0 : isz (0 : ℤ) ≤ SZ p := isz_natCast_le_x2 (p := p) (n := 0) (by omega)
  have hsz1 : isz (1 : ℤ) ≤ SZ p := isz_natCast_le_x2 (p := p) (n := 1) (by omega)
  have hsz2 : isz (2 : ℤ) ≤ SZ p := isz_natCast_le_x2 (p := p) (n := 2) (by omega)
  have hszp : isz ((p : ℤ)) ≤ SZ p := isz_natCast_le_x2 (by omega)
  have hszq : isz (((qq p : ℕ) : ℤ)) ≤ SZ p := isz_natCast_le_x2 (by simp only [qq]; omega)
  have hszC0 : isz (C0c p) ≤ SZ p := isz_C0c_le p
  have htdq : (((qq p : ℕ) : ℤ)).toNat ≤ SZ p := by
    rw [toNat_q p]; simp only [SZ, qq]; omega
  -- (A) the pre-loop chain
  have hpre : Pipe main pre [.int (p : ℤ)]
      [.int 0, .int (p : ℤ), .int (C0c p), .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]
      (12 * SB p KS) := by
    have hchain : Pipe main pre [.int (p : ℤ)]
        [.int 0, .int (p : ℤ), .int (Cv p), .int (xv p), .int (p : ℤ)] (12 * SB p KS) := by
      have s1 := Pipe.le (Pipe.pickAt main hPick (A := [.int (p : ℤ)]) (k := 0) (by simp)
          (v := .int (p : ℤ)) (rfl))
        (le_SB_roll hKpick h100 (k := 0) (by simp) (by simp) (vsz_mem_le1 (vsz_int_le hszp)))
      have s2 := Pipe.le (Pipe.pushOnAny (T := [.int (p : ℤ), .int (p : ℤ)])
          (hPush main (Val.int 2))) (le_SB_one hKpush (vsz_int_le hsz2))
      have s3 := Pipe.le (Pipe.appendTail [.int (p : ℤ)]
          (Pipe.swap main hSwap (.int 2) (.int (p : ℤ))))
        (le_SB_three hKswap (vsz_int_le hsz2) (vsz_int_le hszp) (one_le_SZ p))
      have s4 := Pipe.le (Pipe.appendTail [.int (p : ℤ)]
          (Pipe.binOp (hShl main) (a := (p : ℤ)) (b := (2 : ℤ)) (by norm_num)))
        (le_SB_three hKshl hszp (toNat_two_le p) hsz2)
      have s5 := Pipe.le (Pipe.pickAt main hPick (A := [.int (xv p), .int (p : ℤ)]) (k := 0)
          (by simp) (v := .int (xv p)) (rfl))
        (le_SB_roll hKpick h100 (k := 0) (by simp) (by simp)
          (vsz_mem_le2 (vsz_int_le (isz_xv_le p)) (vsz_int_le hszp)))
      have s6 := Pipe.le (Pipe.pickAt main hPick (A := [.int (xv p), .int (xv p), .int (p : ℤ)])
          (k := 0) (by simp) (v := .int (xv p)) (rfl))
        (le_SB_roll hKpick h100 (k := 0) (by simp) (by simp)
          (vsz_mem_le3 (vsz_int_le (isz_xv_le p)) (vsz_int_le (isz_xv_le p)) (vsz_int_le hszp)))
      have s7 := Pipe.le (Pipe.appendTail [.int (xv p), .int (p : ℤ)]
          (Pipe.binOp (hAdd main) (a := xv p) (b := xv p) trivial))
        (le_SB_two hKadd (isz_xv_le p) (isz_xv_le p))
      have s8 := Pipe.le (Pipe.pushOnAny (T := [.int (xv p + xv p), .int (xv p), .int (p : ℤ)])
          (hPush main (Val.int 1))) (le_SB_one hKpush (vsz_int_le hsz1))
      have s9 := Pipe.le (Pipe.appendTail [.int (xv p), .int (p : ℤ)]
          (Pipe.binOp (hAdd main) (a := (1 : ℤ)) (b := xv p + xv p) trivial))
        (le_SB_two hKadd hsz1 (isz_xv2_le p))
      have htd3 : ((1 + (xv p + xv p))).toNat ≤ SZ p := by
        rw [toNat_eq_of_eq (n := 2 * qq p + 1) (by rw [xv2_eq]; push_cast; ring)]
        simp only [SZ, qq]; omega
      have s10 := Pipe.le (Pipe.appendTail [.int (xv p), .int (p : ℤ)]
          (Pipe.unOp (hPow2 main) (a := 1 + (xv p + xv p))
            (by rw [xv]; positivity)))
        (le_SB_two hKpow2 htd3 (isz_xv3_le p))
      have s11 := Pipe.le (Pipe.pickAt main hPick (A := [.int (Cv p), .int (xv p), .int (p : ℤ)])
          (k := 2) (by simp) (v := .int (p : ℤ)) (rfl))
        (le_SB_roll hKpick h100 (k := 2) (by simp) (by simp)
          (vsz_mem_le3 (vsz_int_le (isz_Cv_le p)) (vsz_int_le (isz_xv_le p)) (vsz_int_le hszp)))
      have s12 := Pipe.le (Pipe.pushOnAny
          (T := [.int (p : ℤ), .int (Cv p), .int (xv p), .int (p : ℤ)]) (hPush main (Val.int 0)))
        (le_SB_one hKpush (vsz_int_le hsz0))
      exact Pipe.le (Pipe.comp s1 (Pipe.comp s2 (Pipe.comp s3 (Pipe.comp s4 (Pipe.comp s5 (Pipe.comp s6 (Pipe.comp s7 (Pipe.comp s8 (Pipe.comp s9 (Pipe.comp s10 (Pipe.comp s11 s12))))))))))) (by omega)
    refine Pipe.rw hchain ?_
    simp only [Cv_eq p, xv_eq p]
  -- (B) the loop
  have hmid : Pipe main (comb body)
      [.int 0, .int (p : ℤ), .int (C0c p), .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]
      [.int (aval p p), .int 0, .int (C0c p), .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]
      ((p + 1) * (14 * SB p KS + Kloop) + Kloop) := by
    intro rest vs hvs s R hR
    let I : ℕ → List Val → Prop := fun i vs => ∃ c : ℤ, i < p ∧
      vs = [.int c, .int ((p - i : ℕ) : ℤ), .int (C0c p), .int ((qq p : ℕ) : ℤ),
        .int (p : ℤ)] ++ rest ∧ c = aval p i
    let F : List Val → Prop := fun out => ∃ c : ℤ,
      out = [.int c, .int 0, .int (C0c p), .int ((qq p : ℕ) : ℤ), .int (p : ℤ)] ++ rest
        ∧ c = aval p p
    have hbody : ∀ i vs, I i vs → WordR main body (fun w => w = vs)
        (fun _ out => ∃ vs', (out = .int 0 :: vs' ∧ F vs')
          ∨ (out = .int 1 :: vs' ∧ I (i + 1) vs' ∧ i + 1 < p)) (fun _ => 14 * SB p KS) := by
      intro i vs hI
      obtain ⟨c, hilt, hvsI, hcI⟩ := hI
      rw [hvsI, hcI]
      have hsz_c : isz (aval p i) ≤ SZ p := isz_aval_le p i
      have hsz_r : isz (((p - i : ℕ) : ℤ)) ≤ SZ p := isz_natCast_le_x2 (by omega)
      have hsz_sum : isz (C0c p + aval p i) ≤ SZ p := isz_C0c_add_aval_le p i
      have hsz_d : isz ((Nat.sqrt ((C0c p + aval p i).toNat) : ℤ)) ≤ SZ p :=
        isz_sqrt_C0c_aval_le p i
      have hsz_d2 : isz (dd p i) ≤ SZ p := isz_dd_le p i
      have hsz_rm : isz (((p - i : ℕ) : ℤ) - 1) ≤ SZ p := by
        apply isz_le_SZ
        have h1 : ((((p - i : ℕ) : ℤ) - 1)).natAbs ≤ p + 1 := by
          have h2 := Int.natAbs_sub_le (((p - i : ℕ) : ℤ)) (1 : ℤ)
          rw [Int.natAbs_natCast, Int.natAbs_one] at h2
          have h3 : p - i ≤ p := Nat.sub_le _ _
          omega
        calc ((((p - i : ℕ) : ℤ) - 1)).natAbs ≤ p + 1 := h1
          _ < 2 ^ (8 * p + 6) := lt_of_le_of_lt (by omega) (Nat.lt_two_pow_self)
      have s1 := Pipe.le (Pipe.pickAt main hPick
          (A := [.int (aval p i), .int ((p - i : ℕ) : ℤ), .int (C0c p), .int ((qq p : ℕ) : ℤ)])
          (k := 2) (by simp) (v := .int (C0c p)) (rfl))
        (le_SB_roll hKpick h100 (k := 2) (by simp) (by simp)
          (vsz_mem_le4 (vsz_int_le hsz_c) (vsz_int_le hsz_r) (vsz_int_le hszC0) (vsz_int_le hszq)))
      have s2 := Pipe.le (Pipe.appendTail [.int ((p - i : ℕ) : ℤ), .int (C0c p),
          .int ((qq p : ℕ) : ℤ)] (Pipe.binOp (hAdd main) (a := C0c p) (b := aval p i) trivial))
        (le_SB_two hKadd hszC0 hsz_c)
      have s3 := Pipe.le (Pipe.appendTail [.int ((p - i : ℕ) : ℤ), .int (C0c p),
          .int ((qq p : ℕ) : ℤ)] (Pipe.unOp (hSqrt main) (a := C0c p + aval p i)
            (C0c_add_aval_nonneg p i)))
        (le_SB_sq hKsqrt hsz_sum)
      have s4 := Pipe.le (Pipe.pickAt main hPick
          (A := [.int ((Nat.sqrt ((C0c p + aval p i).toNat) : ℤ)),
            .int ((p - i : ℕ) : ℤ), .int (C0c p), .int ((qq p : ℕ) : ℤ)]) (k := 3) (by simp)
          (v := .int ((qq p : ℕ) : ℤ)) (rfl))
        (le_SB_roll hKpick h100 (k := 3) (by simp) (by simp)
          (vsz_mem_le4 (vsz_int_le hsz_d) (vsz_int_le hsz_r) (vsz_int_le hszC0) (vsz_int_le hszq)))
      have s5 := Pipe.le (Pipe.appendTail [.int ((p - i : ℕ) : ℤ), .int (C0c p),
          .int ((qq p : ℕ) : ℤ)]
          (Pipe.swap main hSwap (.int ((qq p : ℕ) : ℤ))
            (.int ((Nat.sqrt ((C0c p + aval p i).toNat) : ℤ)))))
        (le_SB_three hKswap (vsz_int_le hszq) (vsz_int_le hsz_d) (one_le_SZ p))
      have s6 := Pipe.le (Pipe.appendTail [.int ((p - i : ℕ) : ℤ), .int (C0c p),
          .int ((qq p : ℕ) : ℤ)]
          (Pipe.binOp (hShl main) (a := (Nat.sqrt ((C0c p + aval p i).toNat) : ℤ))
            (b := ((qq p : ℕ) : ℤ)) (by positivity)))
        (le_SB_three hKshl hsz_d htdq hszq)
      have s7 := Pipe.le (Pipe.appendTail [.int (C0c p), .int ((qq p : ℕ) : ℤ)]
          (Pipe.swap main hSwap (.int (dd p i)) (.int (((p - i : ℕ) : ℤ)))))
        (le_SB_three hKswap (vsz_int_le hsz_d2) (vsz_int_le hsz_r) (one_le_SZ p))
      have s8 := Pipe.le (Pipe.pushOnAny (T := [.int (((p - i : ℕ) : ℤ)), .int (dd p i),
          .int (C0c p), .int ((qq p : ℕ) : ℤ)]) (hPush main (Val.int 1)))
        (le_SB_one hKpush (vsz_int_le hsz1))
      have s9 := Pipe.le (Pipe.appendTail [.int (dd p i), .int (C0c p), .int ((qq p : ℕ) : ℤ)]
          (Pipe.swap main hSwap (.int 1) (.int (((p - i : ℕ) : ℤ)))))
        (le_SB_three hKswap (vsz_int_le hsz1) (vsz_int_le hsz_r) (one_le_SZ p))
      have s10 := Pipe.le (Pipe.appendTail [.int (dd p i), .int (C0c p), .int ((qq p : ℕ) : ℤ)]
          (Pipe.binOp (hSub main) (a := ((p - i : ℕ) : ℤ)) (b := (1 : ℤ)) trivial))
        (le_SB_two hKsub hsz_r hsz1)
      have s11 := Pipe.le (Pipe.appendTail [.int (C0c p), .int ((qq p : ℕ) : ℤ)]
          (Pipe.swap main hSwap (.int (((p - i : ℕ) : ℤ) - 1)) (.int (dd p i))))
        (le_SB_three hKswap (vsz_int_le hsz_rm) (vsz_int_le hsz_d2) (one_le_SZ p))
      have s12 := Pipe.le (Pipe.pickAt main hPick
          (A := [.int (dd p i), .int (((p - i : ℕ) : ℤ) - 1), .int (C0c p),
            .int ((qq p : ℕ) : ℤ)]) (k := 1) (by simp)
          (v := .int (((p - i : ℕ) : ℤ) - 1)) (rfl))
        (le_SB_roll hKpick h100 (k := 1) (by simp) (by simp)
          (vsz_mem_le4 (vsz_int_le hsz_d2) (vsz_int_le hsz_rm) (vsz_int_le hszC0)
            (vsz_int_le hszq)))
      have s13 := Pipe.le (Pipe.pushOnAny (T := [.int (((p - i : ℕ) : ℤ) - 1), .int (dd p i),
          .int (((p - i : ℕ) : ℤ) - 1), .int (C0c p), .int ((qq p : ℕ) : ℤ)])
          (hPush main (Val.int 0)))
        (le_SB_one hKpush (vsz_int_le hsz0))
      have s14 := Pipe.le (Pipe.appendTail [.int (dd p i), .int (((p - i : ℕ) : ℤ) - 1),
          .int (C0c p), .int ((qq p : ℕ) : ℤ)]
          (Pipe.binOp (hLt main) (a := (0 : ℤ)) (b := ((p - i : ℕ) : ℤ) - 1) trivial))
        (le_SB_two hKlt hsz0 hsz_rm)
      have hpipe : Pipe main body
          [.int (aval p i), .int ((p - i : ℕ) : ℤ), .int (C0c p), .int ((qq p : ℕ) : ℤ)]
          [.int (if (0 : ℤ) < ((p - i : ℕ) : ℤ) - 1 then 1 else 0), .int (dd p i),
            .int (((p - i : ℕ) : ℤ) - 1), .int (C0c p), .int ((qq p : ℕ) : ℤ)]
          (14 * SB p KS) :=
        Pipe.le (Pipe.comp s1 (Pipe.comp s2 (Pipe.comp s3 (Pipe.comp s4 (Pipe.comp s5 (Pipe.comp s6 (Pipe.comp s7 (Pipe.comp s8 (Pipe.comp s9 (Pipe.comp s10 (Pipe.comp s11 (Pipe.comp s12 (Pipe.comp s13 s14))))))))))))) (by omega)
      intro w hw s' R hR
      obtain ⟨out, s'', n, hout, hev, hn, hstk, hoth⟩ :=
        hpipe ([.int (p : ℤ)] ++ rest) w hw s' R hR
      have hpi1 : 1 ≤ p - i := by omega
      rcases lt_or_eq_of_le hpi1 with hgt | heq
      · refine ⟨out, s'', n, ?_, hev, hn, hstk, hoth⟩
        refine ⟨[.int (aval p (i + 1)), .int ((p - (i + 1) : ℕ) : ℤ), .int (C0c p),
            .int ((qq p : ℕ) : ℤ), .int (p : ℤ)] ++ rest, Or.inr ⟨?_, ?_, ?_⟩⟩
        · have hfl : (if (0 : ℤ) < ((p - i : ℕ) : ℤ) - 1 then (1 : ℤ) else 0) = 1 := by
            rw [if_pos (by omega)]
          have hd2 : dd p i = aval p (i + 1) := by rw [dd_eq, aval_succ]
          have hrv : ((p - i : ℕ) : ℤ) - 1 = ((p - (i + 1) : ℕ) : ℤ) := by omega
          rw [hout, hfl, hd2, hrv]
          rfl
        · exact ⟨aval p (i + 1), by omega, rfl, rfl⟩
        · omega
      · refine ⟨out, s'', n, ?_, hev, hn, hstk, hoth⟩
        refine ⟨[.int (aval p p), .int 0, .int (C0c p), .int ((qq p : ℕ) : ℤ),
            .int (p : ℤ)] ++ rest, Or.inl ⟨?_, ?_⟩⟩
        · have hfl : (if (0 : ℤ) < ((p - i : ℕ) : ℤ) - 1 then (1 : ℤ) else 0) = 0 := by
            rw [← heq]; norm_num
          have hd2 : dd p i = aval p p := by
            rw [dd_eq, ← aval_succ, show i + 1 = p by omega]
          have hrv : ((p - i : ℕ) : ℤ) - 1 = 0 := by rw [← heq]; norm_num
          rw [hout, hfl, hd2, hrv]
          rfl
        · exact ⟨aval p p, rfl, rfl⟩
    have hI0 : I 0 vs := ⟨0, by omega, by simpa using hvs, rfl⟩
    obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ :=
      hLoop main body I F (14 * SB p KS) p hbody vs hI0 s R hR
    obtain ⟨c, hc1, hc2⟩ := hout
    exact ⟨out, s', n, by rw [hc1, hc2], hev, hn, hstk, hoth⟩
  -- (C) the final chain
  have hfin : Pipe main fin
      [.int (aval p p), .int 0, .int (C0c p), .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]
      [.int (uval p)] (27 * SB p KS) := by
    have hsz_D : isz ((Nat.sqrt ((C0c p - aval p p).toNat) : ℤ)) ≤ SZ p := isz_Dv_le p
    have hsz_cp : isz (aval p p) ≤ SZ p := isz_aval_le p p
    have hsz_c2p1 : isz ((p : ℤ) + (p : ℤ)) ≤ SZ p := by
      rw [show (p : ℤ) + (p : ℤ) = ((2 * p : ℕ) : ℤ) by push_cast; ring]
      exact isz_natCast_le_x2 (by omega)
    have hsz_2p1 : isz (1 + ((p : ℤ) + (p : ℤ))) ≤ SZ p := by
      rw [show 1 + ((p : ℤ) + (p : ℤ)) = ((2 * p + 1 : ℕ) : ℤ) by push_cast; ring]
      exact isz_natCast_le_x2 (by omega)
    have htd2p1 : ((1 + ((p : ℤ) + (p : ℤ))).toNat) ≤ SZ p := by
      rw [toNat_two_p_one p]; simp only [SZ]; omega
    have htdq1 : ((((qq p : ℕ) : ℤ) - 1).toNat) ≤ SZ p := by
      rw [toNat_q_sub_one p hp1]; simp only [SZ, qq]; omega
    have hsz_powq : isz ((2 : ℤ) ^ ((((qq p : ℕ) : ℤ) - 1)).toNat) ≤ SZ p :=
      isz_pow2_le (by rw [toNat_q_sub_one p hp1]; simp only [qq]; omega)
    have g1 : Pipe main fin1
          [.int (aval p p), .int 0, .int (C0c p), .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]
          [.int 1, .int ((p : ℤ) + (p : ℤ)), .int ((Nat.sqrt ((C0c p - aval p p).toNat) : ℤ)), .int (C0c p), .int ((qq p : ℕ) : ℤ), .int (p : ℤ)] (9 * SB p KS) := by
      have f1 := Pipe.le (Pipe.appendTail [.int (C0c p), .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]
          (Pipe.swap main hSwap (.int (aval p p)) (.int 0)))
        (le_SB_three hKswap (vsz_int_le hsz_cp) (vsz_int_le hsz0) (one_le_SZ p))
      have f2 := Pipe.le (Pipe.appendTail [.int (aval p p), .int (C0c p),
          .int ((qq p : ℕ) : ℤ), .int (p : ℤ)] (Pipe.drop main hDrop (.int 0)))
        (le_SB_one hKdrop (vsz_int_le hsz0))
      have f3 := Pipe.le (Pipe.pickAt main hPick (A := [.int (aval p p), .int (C0c p),
          .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]) (k := 1) (by simp) (v := .int (C0c p)) (rfl))
        (le_SB_roll hKpick h100 (k := 1) (by simp) (by simp) (vsz_mem_le4 (vsz_int_le hsz_cp) (vsz_int_le hszC0) (vsz_int_le hszq) (vsz_int_le hszp)))
      have f4 := Pipe.le (Pipe.appendTail [.int (C0c p), .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]
          (Pipe.binOp (hSub main) (a := C0c p) (b := aval p p) trivial))
        (le_SB_two hKsub hszC0 hsz_cp)
      have f5 := Pipe.le (Pipe.appendTail [.int (C0c p), .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]
          (Pipe.unOp (hSqrt main) (a := C0c p - aval p p) (C0c_sub_aval_nonneg p h100)))
        (le_SB_sq hKsqrt (isz_C0c_sub_aval_le p))
      have f6 := Pipe.le (Pipe.pickAt main hPick
          (A := [.int ((Nat.sqrt ((C0c p - aval p p).toNat) : ℤ)), .int (C0c p),
          .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]) (k := 3) (by simp) (v := .int (p : ℤ)) (rfl))
        (le_SB_roll hKpick h100 (k := 3) (by simp) (by simp) (vsz_mem_le4 (vsz_int_le hsz_D) (vsz_int_le hszC0) (vsz_int_le hszq) (vsz_int_le hszp)))
      have f7 := Pipe.le (Pipe.pickAt main hPick (A := [.int (p : ℤ),
          .int ((Nat.sqrt ((C0c p - aval p p).toNat) : ℤ)), .int (C0c p),
          .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]) (k := 4) (by simp) (v := .int (p : ℤ)) (rfl))
        (le_SB_roll hKpick h100 (k := 4) (by simp) (by simp) (vsz_mem_le5 (vsz_int_le hszp) (vsz_int_le hsz_D) (vsz_int_le hszC0) (vsz_int_le hszq) (vsz_int_le hszp)))
      have f8 := Pipe.le (Pipe.appendTail [.int ((Nat.sqrt ((C0c p - aval p p).toNat) : ℤ)),
          .int (C0c p), .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]
          (Pipe.binOp (hAdd main) (a := (p : ℤ)) (b := (p : ℤ)) trivial))
        (le_SB_two hKadd hszp hszp)
      have f9 := Pipe.le (Pipe.pushOnAny (T := [.int ((p : ℤ) + (p : ℤ)),
          .int ((Nat.sqrt ((C0c p - aval p p).toNat) : ℤ)), .int (C0c p),
          .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]) (hPush main (Val.int 1)))
        (le_SB_one hKpush (vsz_int_le hsz1))
      exact Pipe.le (Pipe.comp f1 (Pipe.comp f2 (Pipe.comp f3 (Pipe.comp f4 (Pipe.comp f5 (Pipe.comp f6 (Pipe.comp f7 (Pipe.comp f8 f9)))))))) (by omega)
    have g2 : Pipe main fin2
          [.int 1, .int ((p : ℤ) + (p : ℤ)), .int ((Nat.sqrt ((C0c p - aval p p).toNat) : ℤ)), .int (C0c p), .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]
          [.int (Nt p), .int (C0c p), .int ((qq p : ℕ) : ℤ), .int (p : ℤ)] (9 * SB p KS) := by
      have f10 := Pipe.le (Pipe.appendTail [.int ((Nat.sqrt ((C0c p - aval p p).toNat) : ℤ)),
          .int (C0c p), .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]
          (Pipe.binOp (hAdd main) (a := (1 : ℤ)) (b := (p : ℤ) + (p : ℤ)) trivial))
        (le_SB_two hKadd hsz1 hsz_c2p1)
      have f11 := Pipe.le (Pipe.appendTail [.int (C0c p), .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]
          (Pipe.swap main hSwap (.int (1 + ((p : ℤ) + (p : ℤ))))
          (.int ((Nat.sqrt ((C0c p - aval p p).toNat) : ℤ)))))
        (le_SB_three hKswap (vsz_int_le hsz_2p1) (vsz_int_le hsz_D) (one_le_SZ p))
      have f12 := Pipe.le (Pipe.appendTail [.int (C0c p), .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]
          (Pipe.binOp (hShl main) (a := (Nat.sqrt ((C0c p - aval p p).toNat) : ℤ))
          (b := 1 + ((p : ℤ) + (p : ℤ))) (by positivity)))
        (le_SB_three hKshl hsz_D htd2p1 hsz_2p1)
      have f13 := Pipe.le (Pipe.pickAt main hPick
          (A := [.int ((Nat.sqrt ((C0c p - aval p p).toNat) : ℤ)
          * 2 ^ ((1 + ((p : ℤ) + (p : ℤ))).toNat)), .int (C0c p),
          .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]) (k := 2) (by simp)
          (v := .int ((qq p : ℕ) : ℤ)) (rfl))
        (le_SB_roll hKpick h100 (k := 2) (by simp) (by simp) (vsz_mem_le4 (vsz_int_le (isz_Dm_le p)) (vsz_int_le hszC0) (vsz_int_le hszq) (vsz_int_le hszp)))
      have f14 := Pipe.le (Pipe.pushOnAny (T := [.int (((qq p : ℕ) : ℤ)),
          .int ((Nat.sqrt ((C0c p - aval p p).toNat) : ℤ)
          * 2 ^ ((1 + ((p : ℤ) + (p : ℤ))).toNat)), .int (C0c p),
          .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]) (hPush main (Val.int 1)))
        (le_SB_one hKpush (vsz_int_le hsz1))
      have f15 := Pipe.le (Pipe.appendTail
          [.int ((Nat.sqrt ((C0c p - aval p p).toNat) : ℤ)
          * 2 ^ ((1 + ((p : ℤ) + (p : ℤ))).toNat)), .int (C0c p),
          .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]
          (Pipe.swap main hSwap (.int 1) (.int (((qq p : ℕ) : ℤ)))))
        (le_SB_three hKswap (vsz_int_le hsz1) (vsz_int_le hszq) (one_le_SZ p))
      have f16 := Pipe.le (Pipe.appendTail
          [.int ((Nat.sqrt ((C0c p - aval p p).toNat) : ℤ)
          * 2 ^ ((1 + ((p : ℤ) + (p : ℤ))).toNat)), .int (C0c p),
          .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]
          (Pipe.binOp (hSub main) (a := ((qq p : ℕ) : ℤ)) (b := (1 : ℤ)) trivial))
        (le_SB_two hKsub hszq hsz1)
      have f17 := Pipe.le (Pipe.appendTail
          [.int ((Nat.sqrt ((C0c p - aval p p).toNat) : ℤ)
          * 2 ^ ((1 + ((p : ℤ) + (p : ℤ))).toNat)), .int (C0c p),
          .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]
          (Pipe.unOp (hPow2 main) (a := ((qq p : ℕ) : ℤ) - 1) (by push_cast [qq]; omega)))
        (le_SB_two hKpow2 htdq1 (isz_q_sub_one p))
      have f18 := Pipe.le (Pipe.appendTail [.int (C0c p), .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]
          (Pipe.binOp (hAdd main) (a := (2 : ℤ) ^ ((((qq p : ℕ) : ℤ) - 1)).toNat)
          (b := (Nat.sqrt ((C0c p - aval p p).toNat) : ℤ)
          * 2 ^ ((1 + ((p : ℤ) + (p : ℤ))).toNat)) trivial))
        (le_SB_two hKadd hsz_powq (isz_Dm_le p))
      exact Pipe.le (Pipe.comp f10 (Pipe.comp f11 (Pipe.comp f12 (Pipe.comp f13 (Pipe.comp f14 (Pipe.comp f15 (Pipe.comp f16 (Pipe.comp f17 f18)))))))) (by omega)
    have g3 : Pipe main fin3
          [.int (Nt p), .int (C0c p), .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]
          [.int (Int.fdiv (Nt p) (2 ^ (((qq p : ℕ) : ℤ)).toNat))] (9 * SB p KS) := by
      have f19 := Pipe.le (Pipe.pickAt main hPick (A := [.int (Nt p), .int (C0c p),
          .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]) (k := 2) (by simp)
          (v := .int ((qq p : ℕ) : ℤ)) (rfl))
        (le_SB_roll hKpick h100 (k := 2) (by simp) (by simp) (vsz_mem_le4 (vsz_int_le (isz_Nt_le p hp1)) (vsz_int_le hszC0) (vsz_int_le hszq) (vsz_int_le hszp)))
      have f20 := Pipe.le (Pipe.appendTail [.int (C0c p), .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]
          (Pipe.swap main hSwap (.int (((qq p : ℕ) : ℤ))) (.int (Nt p))))
        (le_SB_three hKswap (vsz_int_le hszq) (vsz_int_le (isz_Nt_le p hp1)) (one_le_SZ p))
      have f21 := Pipe.le (Pipe.appendTail [.int (C0c p), .int ((qq p : ℕ) : ℤ), .int (p : ℤ)]
          (Pipe.binOp (hShrF main) (a := Nt p) (b := ((qq p : ℕ) : ℤ)) (by positivity)))
        (le_SB_two hKshrF (isz_Nt_le p hp1) hszq)
      have f22 := Pipe.le (Pipe.appendTail [.int ((qq p : ℕ) : ℤ), .int (p : ℤ)]
          (Pipe.swap main hSwap (.int (Int.fdiv (Nt p) (2 ^ (((qq p : ℕ) : ℤ)).toNat)))
          (.int (C0c p))))
        (le_SB_three hKswap (vsz_int_le (isz_u_le p hp1)) (vsz_int_le hszC0) (one_le_SZ p))
      have f23 := Pipe.le (Pipe.appendTail
          [.int (Int.fdiv (Nt p) (2 ^ (((qq p : ℕ) : ℤ)).toNat)), .int ((qq p : ℕ) : ℤ),
          .int (p : ℤ)] (Pipe.drop main hDrop (.int (C0c p))))
        (le_SB_one hKdrop (vsz_int_le hszC0))
      have f24 := Pipe.le (Pipe.appendTail [.int (p : ℤ)]
          (Pipe.swap main hSwap (.int (Int.fdiv (Nt p) (2 ^ (((qq p : ℕ) : ℤ)).toNat)))
          (.int (((qq p : ℕ) : ℤ)))))
        (le_SB_three hKswap (vsz_int_le (isz_u_le p hp1)) (vsz_int_le hszq) (one_le_SZ p))
      have f25 := Pipe.le (Pipe.appendTail
          [.int (Int.fdiv (Nt p) (2 ^ (((qq p : ℕ) : ℤ)).toNat)), .int (p : ℤ)]
          (Pipe.drop main hDrop (.int (((qq p : ℕ) : ℤ)))))
        (le_SB_one hKdrop (vsz_int_le hszq))
      have f26 := Pipe.le (Pipe.swap main hSwap
          (.int (Int.fdiv (Nt p) (2 ^ (((qq p : ℕ) : ℤ)).toNat))) (.int (p : ℤ)))
        (le_SB_three hKswap (vsz_int_le (isz_u_le p hp1)) (vsz_int_le hszp) (one_le_SZ p))
      have f27 := Pipe.le (Pipe.appendTail [.int (Int.fdiv (Nt p) (2 ^ (((qq p : ℕ) : ℤ)).toNat))]
          (Pipe.drop main hDrop (.int (p : ℤ))))
        (le_SB_one hKdrop (vsz_int_le hszp))
      exact Pipe.le (Pipe.comp f19 (Pipe.comp f20 (Pipe.comp f21 (Pipe.comp f22 (Pipe.comp f23 (Pipe.comp f24 (Pipe.comp f25 (Pipe.comp f26 f27)))))))) (by omega)
    refine Pipe.rw (Pipe.le (Pipe.comp g1 (Pipe.comp g2 g3)) (by omega)) ?_
    have hfin_eq : Int.fdiv (Nt p) (2 ^ (((qq p : ℕ) : ℤ)).toNat) = uval p := by
      rw [← ucomp_eq p hp1]
      rfl
    rw [show Int.fdiv (Nt p) (2 ^ (((qq p : ℕ) : ℤ)).toNat) = uval p from hfin_eq]
  -- (D) assembly
  intro vs hvs s R hR
  obtain ⟨rest0, hvs0⟩ := hvs
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ :=
    (Pipe.comp hpre (Pipe.comp hmid hfin)) rest0 vs (by rw [hvs0]; rfl) s R hR
  refine ⟨out, s', n, ?_, hev, ?_, hstk, hoth⟩
  · have hpost : out = HvdH.Val.int (uval p) :: rest0 := by rw [hout]; rfl
    exact ⟨rest0, uval p, hvs0, hpost, piUBound p h100 ((piIter p).1 p)⟩
  · have hcost : n ≤ 12 * SB p KS + ((p + 1) * (14 * SB p KS + Kloop) + Kloop + 27 * SB p KS) := hn
    have hSBb : SB p KS ≤ 256 * KS * (p + 1) ^ 2 := SB_le p KS h100
    have h1 : 12 * SB p KS + ((p + 1) * (14 * SB p KS + Kloop) + Kloop + 27 * SB p KS)
        ≤ 12 * (256 * KS * (p + 1) ^ 2)
          + ((p + 1) * (14 * (256 * KS * (p + 1) ^ 2) + KS) + KS
            + 27 * (256 * KS * (p + 1) ^ 2)) := by
      nlinarith [hSBb, hKloop]
    have h2 : 12 * (256 * KS * (p + 1) ^ 2)
          + ((p + 1) * (14 * (256 * KS * (p + 1) ^ 2) + KS) + KS
            + 27 * (256 * KS * (p + 1) ^ 2)) ≤ 20000 * KS * (p + 1) ^ 3 := by
      nlinarith [hKS1, Nat.zero_le p, Nat.zero_le KS, sq_nonneg ((p : ℤ) + 1)]
    have h3 : 20000 * KS * (p + 1) ^ 3
        ≤ (4 * (20000 * KS) + 1) * (p + 1) ^ (4 * (20000 * KS) + 1) :=
      pow_bound (20000 * KS) p (by omega) (by omega)
    exact le_trans (le_trans hcost h1) (le_trans h2 h3)

end Work.Fx
