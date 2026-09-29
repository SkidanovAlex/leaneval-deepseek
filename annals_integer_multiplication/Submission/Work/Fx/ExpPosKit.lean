import Mathlib
import Submission.Work.Fx.FxAdapt
import Submission.Work.Fx.expStepB
import Submission.Work.Fx.ExpPosDefs

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Fx
open HvdH

/-- `szl` of a prefix. -/
theorem szl_take_le (A : List Val) (m : ℕ) : szl (A.take m) ≤ szl A := by
  have h := szl_append (A.take m) (A.drop m)
  rw [List.take_append_drop] at h
  omega

/-!
# Window-step adapters for the positive exponential field

Each lemma turns a `KernelLib`/`IntLib` word into a `Spec` on an *explicit* window of
arbitrary length, at a caller-supplied constant cost.
-/

/-- `pick k` on a window `A` of arbitrary length. -/
theorem Spec.pickStep_x1 {main : Cmd} {prog : ℕ → Cmd} {K : ℕ}
    (h : ∀ k, WordR main (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A B : List Val} {k : ℕ} (hk : k < A.length) (hB : A.getD k .nil :: A = B) {c : ℕ}
    (hc : K * (k + 1) * (szl A + 1) ≤ c) :
    Spec main (prog k) A.length (fun t => t = A) (fun _ o => o = B) (fun _ => c) := by
  intro top rest ht hP vs hvs s R hR
  rw [hP] at hvs
  rw [hvs] at hR
  have hk' : k < (A ++ rest).length := by rw [List.length_append]; omega
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := h k (A ++ rest) hk' s R hR
  have hout : out = B ++ rest := by
    rw [hpost, getD_append_of_lt (rest := rest) hk, ← List.cons_append, hB]
  refine ⟨out, s', n, ⟨B, hout, rfl⟩, hev, ?_, hstk, hfr⟩
  simp only at hn
  refine le_trans hn ?_
  have htake : (A ++ rest).take (k + 1) = A.take (k + 1) :=
    List.take_append_of_le_length (by omega)
  rw [htake]
  have hsum : ((A.take (k + 1)).map vsz).sum ≤ szl A := by
    simpa [szl] using szl_take_le A (k + 1)
  exact le_trans (Nat.mul_le_mul_left (K * (k + 1)) (Nat.add_le_add_right hsum 1)) hc

/-- `roll k` on a window `A` of arbitrary length. -/
theorem Spec.rollStep_x1 {main : Cmd} {prog : ℕ → Cmd} {K : ℕ}
    (h : ∀ k, WordR main (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A B : List Val} {k : ℕ} (hk : k < A.length) (hB : A.getD k .nil :: A.eraseIdx k = B) {c : ℕ}
    (hc : K * (k + 1) * (szl A + 1) ≤ c) :
    Spec main (prog k) A.length (fun t => t = A) (fun _ o => o = B) (fun _ => c) := by
  intro top rest ht hP vs hvs s R hR
  rw [hP] at hvs
  rw [hvs] at hR
  have hk' : k < (A ++ rest).length := by rw [List.length_append]; omega
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := h k (A ++ rest) hk' s R hR
  have hout : out = B ++ rest := by
    rw [hpost, getD_append_of_lt (rest := rest) hk, eraseIdx_append_of_lt (rest := rest) hk]
    rw [← hB]
    rfl
  refine ⟨out, s', n, ⟨B, hout, rfl⟩, hev, ?_, hstk, hfr⟩
  simp only at hn
  refine le_trans hn ?_
  have htake : (A ++ rest).take (k + 1) = A.take (k + 1) :=
    List.take_append_of_le_length (by omega)
  rw [htake]
  have hsum : ((A.take (k + 1)).map vsz).sum ≤ szl A := by
    simpa [szl] using szl_take_le A (k + 1)
  exact le_trans (Nat.mul_le_mul_left (K * (k + 1)) (Nat.add_le_add_right hsum 1)) hc

/-- `dup` on a nonempty window: the head is copied to the front. -/
theorem Spec.dupStep_x1 {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1)))
    (a : Val) (A' : List Val) {B : List Val} (hB : a :: a :: A' = B) {c : ℕ}
    (hc : K * (vsz a + 1) ≤ c) :
    Spec main prog (1 + A'.length) (fun t => t = a :: A') (fun _ o => o = B)
      (fun _ => c) := by
  intro top rest ht hP vs hvs s R hR
  rw [hP] at hvs
  rw [hvs] at hR
  have hne : a :: (A' ++ rest) ≠ [] := List.cons_ne_nil _ _
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := h (a :: (A' ++ rest)) hne s R hR
  obtain ⟨v, r, hv, hout0⟩ := hpost
  have h1 := List.cons.inj hv
  have hout : out = B ++ rest := by
    rw [hout0, ← h1.2, ← h1.1]
    rw [← hB]
    rfl
  refine ⟨out, s', n, ⟨B, hout, rfl⟩, hev, ?_, hstk, hfr⟩
  simp only at hn
  rw [List.headD_cons] at hn
  exact le_trans hn hc

/-- `drop` on a nonempty window: the head is removed. -/
theorem Spec.dropStep_x1 {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1)))
    (a : Val) (A' : List Val) {B : List Val} (hB : A' = B) {c : ℕ}
    (hc : K * (vsz a + 1) ≤ c) :
    Spec main prog (1 + A'.length) (fun t => t = a :: A') (fun _ o => o = B)
      (fun _ => c) := by
  intro top rest ht hP vs hvs s R hR
  rw [hP] at hvs
  rw [hvs] at hR
  have hne : a :: (A' ++ rest) ≠ [] := List.cons_ne_nil _ _
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := h (a :: (A' ++ rest)) hne s R hR
  obtain ⟨v, r, hv, hout0⟩ := hpost
  have h1 := List.cons.inj hv
  have hout : out = B ++ rest := by
    rw [hout0, ← h1.2]
    rw [← hB]
  refine ⟨out, s', n, ⟨B, hout, rfl⟩, hev, ?_, hstk, hfr⟩
  simp only at hn
  rw [List.headD_cons] at hn
  exact le_trans hn hc

/-- A binary integer operation on the top two values of a window. -/
theorem Spec.binOpStep (hk : KernelLib) {main prog : Cmd} {P : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ}
    {C : ℤ → ℤ → ℕ} (h : BinOp main prog P f C) {a b : ℤ} (hP : P a b) {E B : List Val}
    (hB : Val.int (f a b) :: E = B) {c : ℕ} (hc : C a b ≤ c) :
    Spec main prog (2 + E.length) (fun t => t = [Val.int a, Val.int b] ++ E)
      (fun _ o => o = B) (fun _ => c) := by
  have h1 : Spec main prog 2 (fun t => t = [Val.int a, Val.int b])
      (fun _ o => o = [Val.int (f a b)]) (binCost C) := by
    refine Spec.mono hk (Spec.binOp hk h) ?_ ?_ ?_
    · intro t ht hq
      rw [hq]
      exact ⟨a, b, rfl, hP⟩
    · intro t o ht hq hQ
      rcases hQ with ⟨a', b', hab, ho⟩
      have e1 : ([Val.int a', Val.int b'] : List Val) = [Val.int a, Val.int b] := by
        rw [← hab, hq]
      obtain ⟨e2, e3⟩ := List.cons.inj e1
      have e4 := List.cons.inj e3
      rw [ho, Val.int.inj e2, Val.int.inj e4.1]
    · intro t ht hq
      rw [hq]
  refine Spec.mono hk (Spec.extend_exact hk h1 (E := E) rfl) ?_ ?_ ?_
  · intro t ht hq
    rw [hq]
  · intro t o ht hq hQ
    rw [hQ]
    rw [← hB]
    rfl
  · intro t ht hq
    show C a b ≤ c
    exact hc

/-- Pushing a constant value on top of a window. -/
theorem Spec.pushValStep {main : Cmd} {prog : Val → Cmd} {K : ℕ}
    (h : ∀ v, WordR main (prog v) (fun _ => True) (fun vs out => out = v :: vs)
      (fun _ => K * (vsz v + 1)))
    {A B : List Val} (v : Val) (hB : v :: A = B) {c : ℕ} (hc : K * (vsz v + 1) ≤ c) :
    Spec main (prog v) A.length (fun t => t = A) (fun _ o => o = B) (fun _ => c) := by
  intro top rest ht hP vs hvs s R hR
  rw [hP] at hvs
  rw [hvs] at hR
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := h v (A ++ rest) trivial s R hR
  have hout : out = B ++ rest := by rw [hpost, ← List.cons_append, hB]
  exact ⟨out, s', n, ⟨B, hout, rfl⟩, hev, le_trans hn hc, hstk, hfr⟩

/-- `consV` on the top two values of a window. -/
theorem Spec.consVStep {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest)
      (fun _ => K))
    {a b : Val} {E B : List Val} (hB : Val.cons a b :: E = B) {c : ℕ} (hc : K ≤ c) :
    Spec main prog (2 + E.length) (fun t => t = [a, b] ++ E) (fun _ o => o = B)
      (fun _ => c) := by
  intro top rest ht hP vs hvs s R hR
  rw [hP] at hvs
  rw [hvs] at hR
  rw [List.append_assoc] at hR
  have h2 : 2 ≤ ([a, b] ++ (E ++ rest)).length := by simp
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := h ([a, b] ++ (E ++ rest)) h2 s R hR
  obtain ⟨a', b', r', hv, hout0⟩ := hpost
  have h0 : a :: b :: (E ++ rest) = a' :: b' :: r' := by rw [← hv]; rfl
  obtain ⟨ha, hb, hr⟩ := cons_inj3 h0
  have hout : out = B ++ rest := by
    rw [hout0, ← ha, ← hb, ← hr]
    rw [← hB]
    rfl
  exact ⟨out, s', n, ⟨B, hout, rfl⟩, hev, le_trans hn hc, hstk, hfr⟩

/-- A one-input, one-output sub-word (precision `Q`, property `φ` on the result). -/
theorem Spec.wordStep {main prog : Cmd} {Kc Q : ℕ} {φ : ℤ → Prop}
    (h : WordR main prog (fun vs => ∃ rest, vs = Val.int (Q : ℤ) :: rest)
      (fun vs out => ∃ rest u, vs = Val.int (Q : ℤ) :: rest ∧ out = Val.int u :: rest ∧ φ u)
      (fun _ => Kc * (Q + 1) ^ Kc))
    {E : List Val} {c : ℕ} (hc : Kc * (Q + 1) ^ Kc ≤ c) :
    Spec main prog (1 + E.length) (fun t => t = [Val.int (Q : ℤ)] ++ E)
      (fun _ o => ∃ u : ℤ, φ u ∧ o = [Val.int u] ++ E) (fun _ => c) := by
  intro top rest ht hP vs hvs s R hR
  rw [hP] at hvs
  rw [hvs] at hR
  have hR' : s.stk 0 = encs (Val.int (Q : ℤ) :: (E ++ rest)) ++ R := by
    rw [hR]
    simp only [List.singleton_append, List.cons_append, List.nil_append, List.append_assoc]
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ :=
    h (Val.int (Q : ℤ) :: (E ++ rest)) ⟨E ++ rest, rfl⟩ s R hR'
  obtain ⟨r, u, hv, hout, hφ⟩ := hpost
  have hr : r = E ++ rest := ((List.cons.inj hv).2).symm
  refine ⟨out, s', n, ⟨[Val.int u] ++ E, ?_, u, hφ, rfl⟩, hev, le_trans hn hc, hstk, hfr⟩
  simp only [hout, hr, List.nil_append, List.cons_append, List.singleton_append]

/-- A three-input, two-output sub-word (precision `Q`, property `φ` on the result pair). -/
theorem Spec.expWordStep {main prog : Cmd} {Kc Q : ℕ} {Z Y : ℤ} {φ : ℤ → ℤ → Prop}
    (h : WordR main prog (fun vs => ∃ rest, vs = Val.int (Q : ℤ) :: Val.int Z :: Val.int Y :: rest)
      (fun vs out => ∃ rest U V, vs = Val.int (Q : ℤ) :: Val.int Z :: Val.int Y :: rest ∧
        out = Val.int U :: Val.int V :: rest ∧ φ U V)
      (fun _ => Kc * (Q + 1) ^ Kc))
    {E : List Val} {c : ℕ} (hc : Kc * (Q + 1) ^ Kc ≤ c) :
    Spec main prog (3 + E.length)
      (fun t => t = [Val.int (Q : ℤ), Val.int Z, Val.int Y] ++ E)
      (fun _ o => ∃ U V : ℤ, φ U V ∧ o = [Val.int U, Val.int V] ++ E) (fun _ => c) := by
  intro top rest ht hP vs hvs s R hR
  rw [hP] at hvs
  rw [hvs] at hR
  have hR' : s.stk 0 = encs (Val.int (Q : ℤ) :: Val.int Z :: Val.int Y :: (E ++ rest)) ++ R := by
    rw [hR]
    simp only [List.singleton_append, List.cons_append, List.nil_append, List.append_assoc]
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ :=
    h (Val.int (Q : ℤ) :: Val.int Z :: Val.int Y :: (E ++ rest)) ⟨E ++ rest, rfl⟩ s R hR'
  obtain ⟨r, U, V, hv, hout, hφ⟩ := hpost
  have h1 := List.cons.inj hv
  have h2 := List.cons.inj h1.2
  have h3 := List.cons.inj h2.2
  have hr : r = E ++ rest := h3.2.symm
  refine ⟨out, s', n, ⟨[Val.int U, Val.int V] ++ E, ?_, U, V, hφ, rfl⟩, hev,
    le_trans hn hc, hstk, hfr⟩
  simp only [hout, hr, List.nil_append, List.cons_append, List.singleton_append]

/-- If `P` approximates `2^q π` within `1`, then `isz P ≤ q + 5`. -/
theorem isz_le_of_pi_approx {P : ℤ} {q : ℕ} (h : |(P : ℝ) - (2 : ℝ) ^ q * Real.pi| ≤ 1) :
    isz P ≤ q + 5 := by
  have hpi0 : (0:ℝ) < Real.pi := Real.pi_pos
  have hW0 : (0:ℝ) < (2:ℝ)^q := by positivity
  have hWpi : (0:ℝ) < (2:ℝ)^q * Real.pi := mul_pos hW0 hpi0
  have hbounds := abs_le.mp h
  have habs : |(P : ℝ)| ≤ (2:ℝ)^q * Real.pi + 1 := by
    rw [abs_le]
    exact ⟨by linarith [hbounds.1, hWpi], by linarith [hbounds.2]⟩
  have hhalf : |(P : ℝ)| ≤ (2:ℝ)^q * 4 + 1 := by
    have : (2:ℝ)^q * Real.pi < (2:ℝ)^q * 4 := by
      exact mul_lt_mul_of_pos_left Real.pi_lt_four hW0
    linarith
  have hnat : P.natAbs ≤ 4 * 2^q + 1 := by
    have h2 : ((P.natAbs : ℕ) : ℝ) ≤ ((4 * 2^q + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      push_cast
      linarith [hhalf]
    exact_mod_cast h2
  have hlt : P.natAbs < 2 ^ (q + 3) := by
    have h4 : 4 * 2 ^ q = 2 ^ (q + 2) := by ring
    rw [h4] at hnat
    have : 2 ^ (q + 2) + 1 < 2 ^ (q + 3) := by
      have h5 : (2:ℕ) ^ (q + 3) = 2 ^ (q + 2) * 2 := by ring
      rw [h5]
      have h6 : 1 ≤ 2 ^ (q + 2) := Nat.one_le_two_pow
      omega
    omega
  have hsize : P.natAbs.size ≤ q + 3 := Nat.size_le.mpr hlt
  simp only [isz]
  omega

/-- If `P` approximates `2^q log 2` within `1`, then `isz P ≤ q + 5`. -/
theorem isz_le_of_log_approx {P : ℤ} {q : ℕ} (h : |(P : ℝ) - (2 : ℝ) ^ q * Real.log 2| ≤ 1) :
    isz P ≤ q + 5 := by
  have hlog0 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : Real.log 2 < 4 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hW0 : (0:ℝ) < (2:ℝ)^q := by positivity
  have hWpi : (0:ℝ) < (2:ℝ)^q * Real.log 2 := mul_pos hW0 hlog0
  have hbounds := abs_le.mp h
  have habs : |(P : ℝ)| ≤ (2:ℝ)^q * Real.log 2 + 1 := by
    rw [abs_le]
    exact ⟨by linarith [hbounds.1, hWpi], by linarith [hbounds.2]⟩
  have hhalf : |(P : ℝ)| ≤ (2:ℝ)^q * 4 + 1 := by
    have : (2:ℝ)^q * Real.log 2 < (2:ℝ)^q * 4 := mul_lt_mul_of_pos_left hlog4 hW0
    linarith
  have hnat : P.natAbs ≤ 4 * 2^q + 1 := by
    have h2 : ((P.natAbs : ℕ) : ℝ) ≤ ((4 * 2^q + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      push_cast
      linarith [hhalf]
    exact_mod_cast h2
  have hlt : P.natAbs < 2 ^ (q + 3) := by
    have h4 : 4 * 2 ^ q = 2 ^ (q + 2) := by ring
    rw [h4] at hnat
    have : 2 ^ (q + 2) + 1 < 2 ^ (q + 3) := by
      have h5 : (2:ℕ) ^ (q + 3) = 2 ^ (q + 2) * 2 := by ring
      rw [h5]
      have h6 : 1 ≤ 2 ^ (q + 2) := Nat.one_le_two_pow
      omega
    omega
  have hsize : P.natAbs.size ≤ q + 3 := Nat.size_le.mpr hlt
  simp only [isz]
  omega

/-- `isz` of a `max` with zero. -/
theorem isz_max_zero_le (T : ℤ) : isz (max 0 T) ≤ isz T := by
  have h : (max 0 T).natAbs ≤ T.natAbs := by
    have h2 : max 0 T ≤ |T| := max_le (abs_nonneg T) (le_abs_self T)
    have h3 : 0 ≤ max 0 T := le_max_left _ _
    have h4 : ((max 0 T).natAbs : ℤ) ≤ (T.natAbs : ℤ) := by
      rw [Nat.cast_natAbs, Nat.cast_natAbs, abs_of_nonneg h3]
      exact h2
    exact_mod_cast h4
  have hsize : (max 0 T).natAbs.size ≤ T.natAbs.size := Nat.size_mono' h
  simp only [isz]
  omega

/-- `exp 32 ≤ 2^52`. -/
theorem exp32_le : Real.exp 32 ≤ (2 : ℝ) ^ 52 := by
  have h1 : Real.exp 32 = (Real.exp 1) ^ 32 := by
    have := Real.exp_nat_mul 1 32
    simpa using this
  have h2 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have h3 : (3 : ℝ) ^ 32 ≤ (2 : ℝ) ^ 52 := by norm_num
  calc Real.exp 32 = (Real.exp 1) ^ 32 := h1
    _ ≤ 3 ^ 32 := by gcongr
    _ ≤ (2 : ℝ) ^ 52 := h3

/-- The coordinate bound for the output of the complex exponential word. -/
theorem abs_le_of_exp_approx {U V Z : ℤ} {q : ℕ}
    (h : ‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ q - Complex.exp ((Z : ℂ) / (2 : ℂ) ^ q)‖
      ≤ 4 / (2 : ℝ) ^ q)
    (hZ : |(Z : ℝ)| ≤ 32 * (2 : ℝ) ^ q) :
    |(U : ℝ)| ≤ (2 : ℝ) ^ (q + 53) ∧ |(V : ℝ)| ≤ (2 : ℝ) ^ (q + 53) := by
  have hq0 : (0:ℝ) < (2:ℝ)^q := by positivity
  set n : ℕ := 2^q with hn
  have hnpos : 0 < n := by simp [hn]
  have hnr : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
  have hpc : (2:ℂ)^q = (n:ℂ) := by rw [hn, Nat.cast_pow]; norm_num
  have hpr : (2:ℝ)^q = (n:ℝ) := by rw [hn, Nat.cast_pow]; norm_num
  rw [hpc] at h
  rw [hpr] at h hZ
  let z : ℂ := (U:ℂ) + (V:ℂ)*Complex.I
  have hzre : z.re = (U:ℝ) := by simp [z]
  have hzim : z.im = (V:ℝ) := by simp [z]
  have h'h : ‖z / (n:ℂ) - Complex.exp ((Z:ℂ)/(n:ℂ))‖ ≤ 4 / (n:ℝ) := by simpa [z] using h
  have hzn : ‖z / (n:ℂ)‖ ≤ Real.exp 32 + 4/(n:ℝ) := by
    have h3 : ‖z / (n:ℂ)‖ ≤ ‖z / (n:ℂ) - Complex.exp ((Z:ℂ)/(n:ℂ))‖ + ‖Complex.exp ((Z:ℂ)/(n:ℂ))‖ := by
      have := norm_add_le (z / (n:ℂ) - Complex.exp ((Z:ℂ)/(n:ℂ))) (Complex.exp ((Z:ℂ)/(n:ℂ)))
      simpa only [sub_add_cancel] using this
    have hzn2 : ‖Complex.exp ((Z:ℂ)/(n:ℂ))‖ ≤ Real.exp 32 := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have h4 : ((Z:ℂ)/(n:ℂ)).re = (Z:ℝ)/(n:ℝ) := by
        rw [Complex.div_re]
        simp [Complex.normSq]
        field_simp
      rw [h4, div_le_iff₀ hnr]
      exact (abs_le.mp hZ).2
    calc ‖z / (n:ℂ)‖ ≤ ‖z / (n:ℂ) - Complex.exp ((Z:ℂ)/(n:ℂ))‖ + ‖Complex.exp ((Z:ℂ)/(n:ℂ))‖ := h3
      _ ≤ 4/(n:ℝ) + Real.exp 32 := add_le_add h'h hzn2
      _ = Real.exp 32 + 4/(n:ℝ) := by ring
  have hnorm : ‖z‖ ≤ n * (Real.exp 32 + 4/(n:ℝ)) := by
    have h5 : ‖z / (n:ℂ)‖ = ‖z‖ / (n:ℝ) := by
      rw [norm_div]
      simp
    have h6 : ‖z‖ / (n:ℝ) ≤ Real.exp 32 + 4/(n:ℝ) := by
      rw [← h5]; exact hzn
    rw [div_le_iff₀ hnr] at h6
    calc ‖z‖ ≤ (Real.exp 32 + 4/(n:ℝ)) * (n:ℝ) := h6
      _ = n * (Real.exp 32 + 4/(n:ℝ)) := by push_cast; ring
  have hU : |(U:ℝ)| ≤ n * (Real.exp 32 + 4/(n:ℝ)) := by
    have h6 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    rw [hzre] at h6
    exact le_trans h6 hnorm
  have hV : |(V:ℝ)| ≤ n * (Real.exp 32 + 4/(n:ℝ)) := by
    have h6 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    rw [hzim] at h6
    exact le_trans h6 hnorm
  have h7 : n * (Real.exp 32 + 4/(n:ℝ)) = n * Real.exp 32 + 4 := by
    field_simp
  have hx4 : (4:ℝ) ≤ (2:ℝ)^(q+52) := by
    have h1 : (1:ℝ) ≤ 2^q := one_le_pow₀ (by norm_num)
    have h2 : (4:ℝ) ≤ 2^52 := by norm_num
    have h3 : (2:ℝ)^(q+52) = 2^q * 2^52 := by rw [pow_add]
    rw [h3]; nlinarith
  have hrhs : n * (Real.exp 32 + 4/(n:ℝ)) ≤ (2:ℝ)^(q+53) := by
    rw [h7, ← hpr]
    have h14 : (2:ℝ)^q * Real.exp 32 ≤ (2:ℝ)^q * 2^52 :=
      mul_le_mul_of_nonneg_left exp32_le (by positivity)
    have h15 : (2:ℝ)^q * 2^52 = (2:ℝ)^(q+52) := by rw [pow_add]
    have h16 : (2:ℝ)^(q+53) = (2:ℝ)^(q+52) * 2 := by ring
    rw [h15] at h14
    rw [h16]
    linarith
  exact ⟨le_trans hU hrhs, le_trans hV hrhs⟩

/-- Size bound for the output of the complex exponential word. -/
theorem isz_le_of_exp_approx {U V Z : ℤ} {q : ℕ}
    (h : ‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ q - Complex.exp ((Z : ℂ) / (2 : ℂ) ^ q)‖
      ≤ 4 / (2 : ℝ) ^ q)
    (hZ : |(Z : ℝ)| ≤ 32 * (2 : ℝ) ^ q) : isz U ≤ q + 65 ∧ isz V ≤ q + 65 := by
  obtain ⟨hU, hV⟩ := abs_le_of_exp_approx h hZ
  have key : ∀ x : ℤ, |(x:ℝ)| ≤ (2:ℝ)^(q+53) → isz x ≤ q + 65 := by
    intro x hx
    have h13 : |(x:ℝ)| ≤ (2:ℝ)^(q+58) := by
      refine le_trans hx ?_
      exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
    have h14 : ((x.natAbs : ℕ) : ℝ) ≤ ((2^(q+58) : ℕ) : ℝ) := by
      have h14a : ((x.natAbs : ℕ) : ℝ) = |(x:ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      have h14b : ((2^(q+58) : ℕ) : ℝ) = (2:ℝ)^(q+58) := by push_cast; ring
      rw [h14a, h14b]
      exact h13
    have h15 : x.natAbs ≤ 2^(q+58) := by exact_mod_cast h14
    have h16 : x.natAbs < 2^(q+59) := by
      rw [pow_succ]
      have h18 : (0:ℕ) < 2^(q+58) := by positivity
      omega
    have h19 : x.natAbs.size ≤ q + 59 := Nat.size_le.mpr h16
    simp only [isz]
    omega
  exact ⟨key U hU, key V hV⟩

/-- `isz (n : ℤ) ≤ n + 2`. -/
theorem isz_natCast_le (n : ℕ) : isz (n : ℤ) ≤ n + 2 := by
  have h : (n : ℤ).natAbs = n := Int.natAbs_natCast n
  have hn : n.size ≤ n := Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))
  simp only [isz, h]
  omega

/-! ## Composable size bounds (no `omega` on the coefficient arithmetic) -/

theorem isz_le_add_of {a b : ℤ} {A B : ℕ} (ha : isz a ≤ A) (hb : isz b ≤ B) :
    isz (a + b) ≤ A + B := le_trans (isz_add_lin a b) (Nat.add_le_add ha hb)

theorem isz_le_sub_of {a b : ℤ} {A B : ℕ} (ha : isz a ≤ A) (hb : isz b ≤ B) :
    isz (a - b) ≤ A + B := le_trans (isz_sub_lin a b) (Nat.add_le_add ha hb)

theorem isz_le_mul_of {a b : ℤ} {A B : ℕ} (ha : isz a ≤ A) (hb : isz b ≤ B) :
    isz (a * b) ≤ A + B := le_trans (isz_mul_le a b) (Nat.add_le_add ha hb)

theorem isz_le_tdiv_of {a b : ℤ} {A : ℕ} (ha : isz a ≤ A) : isz (a.tdiv b) ≤ A :=
  le_trans (isz_tdiv_le a b) ha

theorem isz_le_max0_of {a : ℤ} {A : ℕ} (ha : isz a ≤ A) : isz (max 0 a) ≤ A :=
  le_trans (isz_max_zero_le a) ha

theorem isz_le_one_of {a : ℤ} {A : ℕ} (ha : isz a ≤ A) : isz a ≤ A := ha

/-- `a * N + b * N ≤ c * N` from `a + b ≤ c`. -/
theorem coeff_add_le {a b c N : ℕ} (h : a + b ≤ c) : a * N + b * N ≤ c * N := by
  rw [← Nat.add_mul]
  exact Nat.mul_le_mul_right N h

theorem coeff_le_mono {a c N : ℕ} (h : a ≤ c) : a * N ≤ c * N := Nat.mul_le_mul_right N h

/-- `szl` of a list bounded elementwise. -/
theorem szl_le_of_forall {W : List Val} {C : ℕ} (h : ∀ v ∈ W, vsz v ≤ C) :
    szl W ≤ W.length * C := by
  induction W with
  | nil => simp [szl]
  | cons a t ih =>
    have ha : vsz a ≤ C := h a (by simp)
    have ht : szl t ≤ t.length * C := ih (fun v hv => h v (by simp [hv]))
    rw [szl_cons, List.length_cons]
    calc vsz a + szl t ≤ C + t.length * C := Nat.add_le_add ha ht
      _ = (t.length + 1) * C := by ring

/-- Size of the output pair of the exponential word (stated outside deep tactic contexts). -/
theorem vsz_cons_w1w2_le (p σ j k : ℕ) (P L U V : ℤ) {N : ℕ} (hN1 : 1 ≤ N)
    (h1 : isz (epW1w p σ j k P L U) ≤ 300 * N) (h2 : isz (epW1w p σ j k P L V) ≤ 300 * N) :
    vsz (.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V))) ≤ 1000 * N := by
  rw [vsz_cons, vsz_int, vsz_int]
  have hone : (1 : ℕ) ≤ 200 * N :=
    le_trans hN1 (Nat.le_mul_of_pos_left N (by norm_num))
  have hsum : (isz (epW1w p σ j k P L U) + isz (epW1w p σ j k P L V)) + 1 ≤
      (300 * N + 300 * N) + 200 * N := Nat.add_le_add (Nat.add_le_add h1 h2) hone
  have hfin : (300 * N + 300 * N) + 200 * N ≤ 1000 * N := by
    have h0 : (300 * N + 300 * N) + 200 * N = 800 * N := by ring
    rw [h0]
    exact Nat.mul_le_mul_right N (by norm_num)
  exact le_trans hsum hfin

/-- Size of the truncated coordinate (stated in a clean context). -/
theorem isz_epW1w_le {p σ j k : ℕ} {P L U : ℤ} {N : ℕ} (hU : isz U ≤ 300 * N) :
    isz (epW1w p σ j k P L U) ≤ 300 * N := by
  change isz (Int.tdiv U (2 ^ (epSw p σ j k P L).toNat)) ≤ 300 * N
  exact isz_le_tdiv_of (a := U) hU

/-- Bundle of the endgame size facts (stated in a clean context to avoid deep
elaboration inside the main proof). -/
theorem segG_sizes (p σ j k : ℕ) (P L U V : ℤ) {N : ℕ} (hN1 : 1 ≤ N)
    (hU : isz U ≤ 300 * N) (hV : isz V ≤ 300 * N) :
    isz (epW1w p σ j k P L U) ≤ 300 * N ∧ isz (epW1w p σ j k P L V) ≤ 300 * N ∧
    vsz (.cons (.int (epW1w p σ j k P L U)) (.int (epW1w p σ j k P L V))) ≤ 1000 * N :=
  ⟨isz_epW1w_le (p := p) (σ := σ) hU, isz_epW1w_le (p := p) (σ := σ) hV,
   vsz_cons_w1w2_le p σ j k P L U V hN1 (isz_epW1w_le (p := p) (σ := σ) hU)
     (isz_epW1w_le (p := p) (σ := σ) hV)⟩

/-- Bump a size bound to the uniform `4000 * N`. -/
theorem le_4000N_of {a C N : ℕ} (h : a ≤ C * N) (hC : C ≤ 4000) : a ≤ 4000 * N :=
  le_trans h (coeff_le_mono hC)

/-- Compose two deterministic one-step specs, adding their constant costs. -/
theorem Spec.seqStep (hk : KernelLib) {main p q : Cmd} {n m : ℕ} {A B D : List Val} {k l : ℕ}
    (h1 : Spec main p n (fun t => t = A) (fun _ o => o = B) (fun _ => k))
    (h2 : Spec main q m (fun t => t = B) (fun _ o => o = D) (fun _ => l)) (hB : B.length = m) :
    Spec main (.seq p q) n (fun t => t = A) (fun _ o => o = D) (fun _ => k + l) := by
  refine Spec.mono hk (Spec.seq_det hk h1 h2 hB) (fun t _ h => h) (fun t o _ _ h => h)
    (fun t ht h => ?_)
  exact le_rfl

/-- If `L` approximates `2^q log 2` with `q ≥ 1`, then `L ≠ 0`. -/
theorem ne_zero_of_log_approx {L : ℤ} {q : ℕ} (hq : 1 ≤ q)
    (h : |(L : ℝ) - (2 : ℝ) ^ q * Real.log 2| ≤ 1) : L ≠ 0 := by
  have hlog4 : (1 : ℝ) < Real.log 4 := by
    have h4pos : (0:ℝ) < 4 := by norm_num
    have he : Real.exp 1 < Real.exp (Real.log 4) := by
      rw [Real.exp_log h4pos]; linarith [Real.exp_one_lt_three]
    exact (Real.exp_lt_exp).mp he
  have hlog : (1 : ℝ) / 2 < Real.log 2 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      have h : Real.log ((2:ℝ) ^ 2) = (2:ℕ) * Real.log 2 := Real.log_pow 2 2
      norm_num at h ⊢
      rw [← h]
    linarith
  have h2q : (2 : ℝ) ≤ (2 : ℝ) ^ q := by
    have h : (2 : ℝ) ^ (1 : ℕ) ≤ (2 : ℝ) ^ q := pow_le_pow_right₀ (by norm_num) hq
    simpa using h
  have hprod : (1 : ℝ) < (2 : ℝ) ^ q * Real.log 2 := by nlinarith
  have hb := abs_le.mp h
  have hpos : (0 : ℝ) < (L : ℝ) := by linarith [hb.1, hprod]
  intro h0
  rw [h0] at hpos
  norm_num at hpos

/-- Compose two specs whose costs are `k*M` and `l*M`, adding the multipliers. -/
theorem Spec.seqAdd (hk : KernelLib) {main p q : Cmd} {n m : ℕ} {A B D : List Val} {M k l : ℕ}
    (h1 : Spec main p n (fun t => t = A) (fun _ o => o = B) (fun _ => k * M))
    (h2 : Spec main q m (fun t => t = B) (fun _ o => o = D) (fun _ => l * M)) (hB : B.length = m) :
    Spec main (.seq p q) n (fun t => t = A) (fun _ o => o = D) (fun _ => (k + l) * M) := by
  have h := Spec.seq_det hk h1 h2 hB
  refine Spec.mono hk h (fun t _ h => h) (fun t o _ _ h => h) (fun t ht h => ?_)
  show k * M + l * M ≤ (k + l) * M
  rw [Nat.add_mul]

/-- `a ≤ c` gives `a ≤ 1 * c`. -/
theorem le_one_mul {a c : ℕ} (h : a ≤ c) : a ≤ 1 * c := by simpa using h

end Work.Fx
