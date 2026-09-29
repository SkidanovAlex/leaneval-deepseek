import Mathlib
import Submission.Work.Fx.FxLin
import Submission.Work.Fx.mulF_approx

set_option maxHeartbeats 40000000

namespace Work.Fx

open HvdH

/-! ## Basic integer facts used by the fast fixed-point multiplication -/

/-- The "sign" computed by the StackLang program equals `Int.sign`. -/
theorem int_sign_eq (a : ℤ) :
    Int.sign a = (if (0 : ℤ) < a then 1 else 0) - (if a < 0 then 1 else 0) := by
  rcases a with n | n
  · rcases n with _ | m
    · norm_num [Int.sign]
    · rw [show Int.sign (Int.ofNat (m+1)) = 1 from rfl]
      rw [show Int.ofNat (m+1) = ((m:ℤ) + 1) from by simp]
      have h1 : (0:ℤ) < (m:ℤ) + 1 := by have := Int.natCast_nonneg m; linarith
      have h2 : ¬ ((m:ℤ) + 1 < 0) := by have := Int.natCast_nonneg m; linarith
      rw [ite_eq_left h1, ite_eq_right h2]; norm_num
  · rw [show Int.sign (Int.negSucc n) = -1 from rfl]
    rw [show Int.negSucc n = -((n:ℤ) + 1) from by
      rw [show Int.negSucc n = -(((n+1 : ℕ)) : ℤ) from rfl]; push_cast; ring]
    have h1 : ¬ ((0:ℤ) < -((n:ℤ) + 1)) := by have := Int.natCast_nonneg n; linarith
    have h2 : -((n:ℤ) + 1) < 0 := by have := Int.natCast_nonneg n; linarith
    rw [ite_eq_right h1, ite_eq_left h2]; norm_num

/-- `max (-a) a = |a|` as an integer. -/
theorem int_max_neg_eq_natAbs (a : ℤ) : max (-a) a = (a.natAbs : ℤ) := by
  rw [max_comm]; rcases lt_or_ge 0 a with h | h
  · rw [max_eq_left (by linarith)]; exact (Int.ofNat_natAbs_of_nonneg (le_of_lt h)).symm
  · rw [max_eq_right (by linarith)]
    have : (a.natAbs : ℤ) = -a := by
      rw [← Int.natAbs_neg a]; exact Int.ofNat_natAbs_of_nonneg (by linarith)
    rw [this]

/-- `a = sign a * |a|`. -/
theorem sign_mul_natAbs (a : ℤ) : Int.sign a * (a.natAbs : ℤ) = a := Int.sign_mul_natAbs a

/-! ## `TopSpec`: replace a prefix of the value stack -/

/-- `TopSpec main p X Y c`: running `p` on any value stack of the form `X ++ rest` produces
`Y ++ rest`, at cost `c` (uniform in `rest`). -/
def TopSpec (main : HvdH.Cmd) (p : HvdH.Cmd) (X Y : List HvdH.Val) (c : ℕ) : Prop :=
  ∀ rest : List HvdH.Val,
    HvdH.WordR main p (fun vs => vs = X ++ rest) (fun _ out => out = Y ++ rest) (fun _ => c)

theorem TopSpec.seq (hk : HvdH.KernelLib) {main p q : HvdH.Cmd} {X Y Z : List HvdH.Val} {c1 c2 : ℕ}
    (h1 : TopSpec main p X Y c1) (h2 : TopSpec main q Y Z c2) :
    TopSpec main (.seq p q) X Z (c1 + c2) := by
  intro rest
  refine hk.conseq (main := main) (p := (.seq p q))
    (P := fun vs => vs = X ++ rest) (P' := fun vs => vs = X ++ rest)
    (Q := fun _ out => ∃ mid, mid = Y ++ rest ∧ out = Z ++ rest) (Q' := fun _ out => out = Z ++ rest)
    (C := fun _ => c1 + c2) (C' := fun _ => c1 + c2) ?_ (fun _ hv => hv) ?_ (fun _ _ => le_rfl)
  · refine hk.seq (main := main) (p := p) (q := q)
      (P := fun vs => vs = X ++ rest) (Q := fun _ out => out = Y ++ rest) (C := fun _ => c1)
      (P' := fun vs => vs = Y ++ rest) (Q' := fun _ out => out = Z ++ rest)
      (C' := fun _ => c2) (B := fun _ => c2) (h1 rest) (h2 rest) ?_
    intro vs mid hP hQ
    exact ⟨hQ, le_rfl⟩
  · intro vs out hv hq
    rcases hq with ⟨mid, hm, ho⟩
    exact ho

theorem TopSpec.extend {main p : HvdH.Cmd} {X Y : List HvdH.Val} {c : ℕ}
    (h : TopSpec main p X Y c) (E : List HvdH.Val) :
    TopSpec main p (X ++ E) (Y ++ E) c := by
  intro rest
  simp only [List.append_assoc]
  exact h (E ++ rest)

theorem TopSpec.mono {main p : HvdH.Cmd} {X Y X' Y' : List HvdH.Val} {c c' : ℕ}
    (hk : HvdH.KernelLib) (h : TopSpec main p X Y c) (hX : X' = X) (hY : Y' = Y) (hc : c ≤ c') :
    TopSpec main p X' Y' c' := by
  intro rest
  have h1 : HvdH.WordR main p (fun vs => vs = X' ++ rest)
      (fun _ out => out = Y' ++ rest) (fun _ => c) := by
    rw [hX, hY]; exact h rest
  exact hk.conseq (main := main) (p := p)
    (P := fun vs => vs = X' ++ rest) (P' := fun vs => vs = X' ++ rest)
    (Q := fun _ out => out = Y' ++ rest) (Q' := fun _ out => out = Y' ++ rest)
    (C := fun _ => c) (C' := fun _ => c') h1
    (fun _ hv => hv) (fun _ _ _ hq => hq) (fun _ _ => hc)



open HvdH

/-! ## `TopSpec` op adapters -/

theorem TopSpec.binOp (hk : HvdH.KernelLib) {main p : HvdH.Cmd} {P : ℤ → ℤ → Prop}
    {f : ℤ → ℤ → ℤ} {C : ℤ → ℤ → ℕ} (h : BinOp main p P f C) {a b : ℤ} (hab : P a b) :
    TopSpec main p [.int a, .int b] [.int (f a b)] (C a b) := by
  intro rest
  refine hk.conseq (main := main) (p := p)
    (P := fun vs => ∃ a b rest, vs = .int a :: .int b :: rest ∧ P a b)
    (Q := fun vs out => ∃ a b rest, vs = .int a :: .int b :: rest ∧ out = .int (f a b) :: rest)
    (C := binCost C)
    (P' := fun vs => vs = [.int a, .int b] ++ rest)
    (Q' := fun _ out => out = [.int (f a b)] ++ rest)
    (C' := fun _ => C a b) h ?_ ?_ ?_
  · intro vs hv
    exact ⟨a, b, rest, hv, hab⟩
  · intro vs out hv hQ
    rcases hQ with ⟨a', b', rest', hvs, hout⟩
    rw [hvs, List.cons_append, List.cons_append] at hv
    obtain ⟨h1, h2, h3⟩ := int_cons_inj3 hv
    rw [hout, h1, h2, h3]
    rfl
  · intro vs hv
    rw [hv, List.cons_append, List.cons_append]
    rfl

theorem TopSpec.unOp (hk : HvdH.KernelLib) {main p : HvdH.Cmd} {P : ℤ → Prop}
    {f : ℤ → ℤ} {C : ℤ → ℕ} (h : UnOp main p P f C) {a : ℤ} (ha : P a) :
    TopSpec main p [.int a] [.int (f a)] (C a) := by
  intro rest
  refine hk.conseq (main := main) (p := p)
    (P := fun vs => ∃ a rest, vs = .int a :: rest ∧ P a)
    (Q := fun vs out => ∃ a rest, vs = .int a :: rest ∧ out = .int (f a) :: rest)
    (C := unCost C)
    (P' := fun vs => vs = [.int a] ++ rest)
    (Q' := fun _ out => out = [.int (f a)] ++ rest)
    (C' := fun _ => C a) h ?_ ?_ ?_
  · intro vs hv
    exact ⟨a, rest, hv, ha⟩
  · intro vs out hv hQ
    rcases hQ with ⟨a', rest', hvs, hout⟩
    rw [hvs, List.cons_append] at hv
    have h1 := List.cons.inj hv
    rw [hout, Val.int.inj h1.1, h1.2]
    rfl
  · intro vs hv
    rw [hv, List.cons_append]
    rfl

theorem TopSpec.dup (hk : HvdH.KernelLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (v : HvdH.Val),
      TopSpec main prog [v] [v, v] (K * (vsz v + 1)) := by
  obtain ⟨prog, K, h⟩ := hk.dup
  refine ⟨prog, K, fun main v => ?_⟩
  intro rest
  refine hk.conseq (main := main) (p := prog)
    (P := fun vs => vs ≠ [])
    (Q := fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
    (C := fun vs => K * (vsz (vs.headD .nil) + 1))
    (P' := fun vs => vs = [v] ++ rest)
    (Q' := fun _ out => out = [v, v] ++ rest)
    (C' := fun _ => K * (vsz v + 1)) (h main) ?_ ?_ ?_
  · intro vs hv; rw [hv]; exact List.cons_ne_nil v rest
  · intro vs out hv hq
    rcases hq with ⟨w, rest', hvs, hout⟩
    rw [hvs] at hv
    have h1 := List.cons.inj hv
    rw [hout, h1.1, h1.2]
    rfl
  · intro vs hv; rw [hv]; rfl

theorem TopSpec.swap (hk : HvdH.KernelLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (a b : HvdH.Val),
      TopSpec main prog [a, b] [b, a] (K * (vsz a + vsz b + 1)) := by
  obtain ⟨prog, K, h⟩ := hk.swap
  refine ⟨prog, K, fun main a b => ?_⟩
  intro rest
  refine hk.conseq (main := main) (p := prog)
    (P := fun vs => 2 ≤ vs.length)
    (Q := fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
    (C := fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1))
    (P' := fun vs => vs = [a, b] ++ rest)
    (Q' := fun _ out => out = [b, a] ++ rest)
    (C' := fun _ => K * (vsz a + vsz b + 1)) (h main) ?_ ?_ ?_
  · intro vs hv; rw [hv]; simp
  · intro vs out hv hq
    rcases hq with ⟨a', b', rest', hvs, hout⟩
    rw [hvs] at hv
    obtain ⟨h1, h2, h3⟩ := cons_inj3 hv
    rw [hout, h1, h2, h3]
    rfl
  · intro vs hv; rw [hv]; simp

theorem TopSpec.roll (hk : HvdH.KernelLib) :
    ∃ (prog : ℕ → HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (k : ℕ) (W : List HvdH.Val),
      k < W.length →
      TopSpec main (prog k) W (W.getD k .nil :: W.eraseIdx k)
        (K * (k + 1) * (((W.take (k + 1)).map vsz).sum + 1)) := by
  obtain ⟨prog, K, h⟩ := hk.roll
  refine ⟨prog, K, fun main k W hklt => ?_⟩
  intro rest
  have hlen : k < (W ++ rest).length := by
    rw [List.length_append]; omega
  have htake : (W ++ rest).take (k + 1) = W.take (k + 1) :=
    List.take_append_of_le_length (by omega)
  refine hk.conseq (main := main) (p := prog k)
    (P := fun vs => k < vs.length)
    (Q := fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
    (C := fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1))
    (P' := fun vs => vs = W ++ rest)
    (Q' := fun _ out => out = (W.getD k .nil :: W.eraseIdx k) ++ rest)
    (C' := fun _ => K * (k + 1) * (((W.take (k + 1)).map vsz).sum + 1)) (h main k) ?_ ?_ ?_
  · intro vs hv; rw [hv]; exact hlen
  · intro vs out hv hq
    rw [hv] at hq
    rw [hq]
    exact getD_eraseIdx_append hklt
  · intro vs hv; rw [hv, htake]

theorem TopSpec.pushVal (hk : HvdH.KernelLib) :
    ∃ (prog : HvdH.Val → HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (v : HvdH.Val),
      TopSpec main (prog v) [] [v] (K * (vsz v + 1)) := by
  obtain ⟨prog, K, h⟩ := hk.pushVal
  refine ⟨prog, K, fun main v => ?_⟩
  intro rest
  refine hk.conseq (main := main) (p := prog v)
    (P := fun _ => True) (Q := fun vs out => out = v :: vs)
    (C := fun _ => K * (vsz v + 1))
    (P' := fun vs => vs = ([] : List HvdH.Val) ++ rest)
    (Q' := fun _ out => out = [v] ++ rest)
    (C' := fun _ => K * (vsz v + 1)) (h main v) ?_ ?_ ?_
  · intro vs hv; exact trivial
  · intro vs out hv hq
    rw [hq, hv]; rfl
  · intro vs hv; exact le_rfl

theorem TopSpec.unconsV (hk : HvdH.KernelLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (a b : HvdH.Val),
      TopSpec main prog [HvdH.Val.cons a b] [a, b] K := by
  obtain ⟨prog, K, h⟩ := hk.unconsV
  refine ⟨prog, K, fun main a b => ?_⟩
  intro rest
  refine hk.conseq (main := main) (p := prog)
    (P := fun vs => ∃ a b rest, vs = .cons a b :: rest)
    (Q := fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest)
    (C := fun _ => K)
    (P' := fun vs => vs = [HvdH.Val.cons a b] ++ rest)
    (Q' := fun _ out => out = [a, b] ++ rest)
    (C' := fun _ => K) (h main) ?_ ?_ ?_
  · intro vs hv; exact ⟨a, b, rest, hv⟩
  · intro vs out hv hq
    rcases hq with ⟨a', b', rest', hvs, hout⟩
    rw [hvs] at hv
    obtain ⟨h1, h2, h3⟩ := val_cons_inj3 hv
    rw [hout, h1, h2, h3]
    rfl
  · intro vs hv; exact le_rfl

theorem TopSpec.consV (hk : HvdH.KernelLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (a b : HvdH.Val),
      TopSpec main prog [a, b] [HvdH.Val.cons a b] K := by
  obtain ⟨prog, K, h⟩ := hk.consV
  refine ⟨prog, K, fun main a b => ?_⟩
  intro rest
  refine hk.conseq (main := main) (p := prog)
    (P := fun vs => 2 ≤ vs.length)
    (Q := fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest)
    (C := fun _ => K)
    (P' := fun vs => vs = [a, b] ++ rest)
    (Q' := fun _ out => out = [HvdH.Val.cons a b] ++ rest)
    (C' := fun _ => K) (h main) ?_ ?_ ?_
  · intro vs hv; rw [hv]; simp
  · intro vs out hv hq
    rcases hq with ⟨a', b', rest', hvs, hout⟩
    rw [hvs] at hv
    obtain ⟨h1, h2, h3⟩ := cons_inj3 hv
    rw [hout, h1, h2, h3]
    rfl
  · intro vs hv; exact le_rfl

theorem TopSpec.selfMul (hk : HvdH.KernelLib) {main : HvdH.Cmd} {N : ℕ} {Cm : ℕ → ℕ}
    (h : MulBelow main N Cm) {x y : ℕ} (hx : x.size < N) (hy : y.size < N) :
    TopSpec main .self [.int (x : ℤ), .int (y : ℤ)] [.int ((x * y : ℕ) : ℤ)]
      (Cm (max x.size y.size)) := by
  intro rest
  refine hk.conseq (main := main) (p := .self)
    (P := mulPre N) (Q := mulPost) (C := fun vs => Cm (mulSize vs))
    (P' := fun vs => vs = [.int (x : ℤ), .int (y : ℤ)] ++ rest)
    (Q' := fun _ out => out = [.int ((x * y : ℕ) : ℤ)] ++ rest)
    (C' := fun _ => Cm (max x.size y.size)) h ?_ ?_ ?_
  · intro vs hv
    exact ⟨x, y, rest, hv, hx, hy⟩
  · intro vs out hv hq
    rcases hq with ⟨x', y', rest', hvs, hout⟩
    rw [hvs, List.cons_append, List.cons_append] at hv
    obtain ⟨h1, h2, h3⟩ := int_cons_inj3 hv
    have hx' : x' = x := Int.ofNat.inj h1
    have hy' : y' = y := Int.ofNat.inj h2
    rw [hout, hx', hy', h3]
    simp
  · intro vs hv
    rw [hv, List.cons_append, List.cons_append]
    simp [mulSize, Int.natAbs_natCast]




open HvdH

/-! ## Size lemmas -/

theorem natAbs_le_two_pow {p : ℕ} {x y : ℤ} (h : x ^ 2 + y ^ 2 ≤ 4 ^ p) : x.natAbs ≤ 2 ^ p := by
  have h4 : (4 : ℤ) ^ p = ((2 : ℤ) ^ p) ^ 2 := by
    rw [show (4 : ℤ) = 2 * 2 from rfl, mul_pow]; ring
  have hsq : ((x.natAbs : ℤ)) ^ 2 ≤ ((2 : ℤ) ^ p) ^ 2 := by
    rw [h4] at h
    have hy : (0:ℤ) ≤ y^2 := sq_nonneg y
    have : x ^ 2 ≤ ((2 : ℤ) ^ p) ^ 2 := by linarith
    rwa [Int.natAbs_sq]
  have h2p : ((2 : ℤ) ^ p) = ((2 ^ p : ℕ) : ℤ) := by push_cast; ring
  have hle : (x.natAbs : ℤ) ≤ ((2 ^ p : ℕ) : ℤ) := by
    have ha : |(x.natAbs : ℤ)| ≤ |((2 : ℤ) ^ p)| := (sq_le_sq.mp hsq)
    rw [h2p] at ha
    simpa using ha
  exact_mod_cast hle

theorem size_le_of_le_two_pow {n p : ℕ} (h : n ≤ 2 ^ p) : n.size ≤ p + 1 :=
  Nat.size_le.mpr (lt_of_le_of_lt h (Nat.pow_lt_pow_succ (by norm_num : 1 < 2)))

theorem szl_le_mul {M : ℕ} {W : List HvdH.Val} (h : ∀ v ∈ W, vsz v ≤ M) :
    szl W ≤ M * W.length := by
  induction W with
  | nil => simp [szl]
  | cons a t ih =>
    rw [szl_cons, List.length_cons]
    have ha : vsz a ≤ M := h a (by simp)
    have ht : ∀ v ∈ t, vsz v ≤ M := fun v hv => h v (by simp [hv])
    have := ih ht
    nlinarith

/-- `isz` of a value with `natAbs ≤ 2^p`. -/
theorem isz_le_of_natAbs_le_x1 {z : ℤ} {p : ℕ} (h : z.natAbs ≤ 2 ^ p) : isz z ≤ p + 3 := by
  have : z.natAbs.size ≤ p + 1 := Nat.size_le.mpr (lt_of_le_of_lt h (Nat.pow_lt_pow_succ (by norm_num)))
  simp only [isz]; omega

theorem isz_le_M {z : ℤ} {p : ℕ} (h : z.natAbs ≤ 2 ^ p) : isz z ≤ 1000 * (p + 1) := by
  have := isz_le_of_natAbs_le_x1 h
  have hp : (0:ℕ) ≤ p := Nat.zero_le p
  omega

theorem vsz_int_le_M {z : ℤ} {p : ℕ} (h : z.natAbs ≤ 2 ^ p) : vsz (.int z) ≤ 1000 * (p + 1) := by
  rw [vsz_int]; exact isz_le_M h

/-- Bound on `szl` of an explicit window of at most 13 values. -/
theorem szl_bnd_of (p : ℕ) (W : List HvdH.Val) (hl : W.length ≤ 13)
    (h : ∀ v ∈ W, vsz v ≤ 3000 * (p + 1)) : szl W + 1 ≤ 40000 * (p + 1) := by
  have h1 := szl_le_mul (M := 3000 * (p + 1)) h
  have h2 : 3000 * (p + 1) * W.length ≤ 3000 * (p + 1) * 13 := Nat.mul_le_mul_left _ hl
  omega

/-! ## Cost bound helpers -/

theorem cost_roll {K KB p k sz : ℕ} (hK : K * 1000000 ≤ KB) (hk : k + 1 ≤ 13)
    (hsz : sz + 1 ≤ 40000 * (p + 1)) : K * (k + 1) * (sz + 1) ≤ KB * (p + 1) := by
  have h2 : (k + 1) * (sz + 1) ≤ 1000000 * (p + 1) := by nlinarith
  calc K * (k + 1) * (sz + 1) = K * ((k + 1) * (sz + 1)) := by ring
    _ ≤ K * (1000000 * (p + 1)) := Nat.mul_le_mul_left K h2
    _ = (K * 1000000) * (p + 1) := by ring
    _ ≤ KB * (p + 1) := Nat.mul_le_mul_right (p + 1) hK

theorem cost_binL {K KB p a b : ℕ} (hK : K * 1000000 ≤ KB) (ha : a ≤ 3000 * (p + 1))
    (hb : b ≤ 3000 * (p + 1)) : K * (a + b) ≤ KB * (p + 1) := by
  have h2 : a + b ≤ 1000000 * (p + 1) := by nlinarith
  calc K * (a + b) ≤ K * (1000000 * (p + 1)) := Nat.mul_le_mul_left K h2
    _ = (K * 1000000) * (p + 1) := by ring
    _ ≤ KB * (p + 1) := Nat.mul_le_mul_right (p + 1) hK

theorem cost_one_x1 {K KB p a : ℕ} (hK : K * 1000000 ≤ KB) (ha : a ≤ 1000000 * (p + 1)) :
    K * a ≤ KB * (p + 1) := by
  calc K * a ≤ K * (1000000 * (p + 1)) := Nat.mul_le_mul_left K ha
    _ = (K * 1000000) * (p + 1) := by ring
    _ ≤ KB * (p + 1) := Nat.mul_le_mul_right (p + 1) hK

theorem cost_smallmul {K KB p a b : ℕ} (hK : K * 1000000 ≤ KB) (ha : a ≤ 3)
    (hb : b ≤ 3000 * (p + 1)) : K * a * b ≤ KB * (p + 1) := by
  have h2 : a * b ≤ 1000000 * (p + 1) := by nlinarith
  calc K * a * b = K * (a * b) := by ring
    _ ≤ K * (1000000 * (p + 1)) := Nat.mul_le_mul_left K h2
    _ = (K * 1000000) * (p + 1) := by ring
    _ ≤ KB * (p + 1) := Nat.mul_le_mul_right (p + 1) hK

theorem coeffK {Ksum K : ℕ} (h : K ≤ Ksum) : K * 1000000 ≤ 1000000 * Ksum := by nlinarith

theorem szl_bnd2 (p : ℕ) (a1 : Val) (a2 : Val) (h1 : vsz a1 ≤ 3000 * (p+1)) (h2 : vsz a2 ≤ 3000 * (p+1)) :
    szl [a1, a2] + 1 ≤ 40000 * (p + 1) := by
  have h := szl_le_mul (M := 3000 * (p+1)) (W := [a1, a2]) (by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> assumption)
  simp only [List.length_cons, List.length_nil] at h
  omega

theorem szl_bnd3 (p : ℕ) (a1 : Val) (a2 : Val) (a3 : Val) (h1 : vsz a1 ≤ 3000 * (p+1)) (h2 : vsz a2 ≤ 3000 * (p+1)) (h3 : vsz a3 ≤ 3000 * (p+1)) :
    szl [a1, a2, a3] + 1 ≤ 40000 * (p + 1) := by
  have h := szl_le_mul (M := 3000 * (p+1)) (W := [a1, a2, a3]) (by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> assumption)
  simp only [List.length_cons, List.length_nil] at h
  omega

theorem szl_bnd4 (p : ℕ) (a1 : Val) (a2 : Val) (a3 : Val) (a4 : Val) (h1 : vsz a1 ≤ 3000 * (p+1)) (h2 : vsz a2 ≤ 3000 * (p+1)) (h3 : vsz a3 ≤ 3000 * (p+1)) (h4 : vsz a4 ≤ 3000 * (p+1)) :
    szl [a1, a2, a3, a4] + 1 ≤ 40000 * (p + 1) := by
  have h := szl_le_mul (M := 3000 * (p+1)) (W := [a1, a2, a3, a4]) (by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> assumption)
  simp only [List.length_cons, List.length_nil] at h
  omega

theorem szl_bnd5 (p : ℕ) (a1 : Val) (a2 : Val) (a3 : Val) (a4 : Val) (a5 : Val) (h1 : vsz a1 ≤ 3000 * (p+1)) (h2 : vsz a2 ≤ 3000 * (p+1)) (h3 : vsz a3 ≤ 3000 * (p+1)) (h4 : vsz a4 ≤ 3000 * (p+1)) (h5 : vsz a5 ≤ 3000 * (p+1)) :
    szl [a1, a2, a3, a4, a5] + 1 ≤ 40000 * (p + 1) := by
  have h := szl_le_mul (M := 3000 * (p+1)) (W := [a1, a2, a3, a4, a5]) (by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption)
  simp only [List.length_cons, List.length_nil] at h
  omega

theorem szl_bnd6 (p : ℕ) (a1 : Val) (a2 : Val) (a3 : Val) (a4 : Val) (a5 : Val) (a6 : Val) (h1 : vsz a1 ≤ 3000 * (p+1)) (h2 : vsz a2 ≤ 3000 * (p+1)) (h3 : vsz a3 ≤ 3000 * (p+1)) (h4 : vsz a4 ≤ 3000 * (p+1)) (h5 : vsz a5 ≤ 3000 * (p+1)) (h6 : vsz a6 ≤ 3000 * (p+1)) :
    szl [a1, a2, a3, a4, a5, a6] + 1 ≤ 40000 * (p + 1) := by
  have h := szl_le_mul (M := 3000 * (p+1)) (W := [a1, a2, a3, a4, a5, a6]) (by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
  simp only [List.length_cons, List.length_nil] at h
  omega

theorem szl_bnd7 (p : ℕ) (a1 : Val) (a2 : Val) (a3 : Val) (a4 : Val) (a5 : Val) (a6 : Val) (a7 : Val) (h1 : vsz a1 ≤ 3000 * (p+1)) (h2 : vsz a2 ≤ 3000 * (p+1)) (h3 : vsz a3 ≤ 3000 * (p+1)) (h4 : vsz a4 ≤ 3000 * (p+1)) (h5 : vsz a5 ≤ 3000 * (p+1)) (h6 : vsz a6 ≤ 3000 * (p+1)) (h7 : vsz a7 ≤ 3000 * (p+1)) :
    szl [a1, a2, a3, a4, a5, a6, a7] + 1 ≤ 40000 * (p + 1) := by
  have h := szl_le_mul (M := 3000 * (p+1)) (W := [a1, a2, a3, a4, a5, a6, a7]) (by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
  simp only [List.length_cons, List.length_nil] at h
  omega

theorem szl_bnd8 (p : ℕ) (a1 : Val) (a2 : Val) (a3 : Val) (a4 : Val) (a5 : Val) (a6 : Val) (a7 : Val) (a8 : Val) (h1 : vsz a1 ≤ 3000 * (p+1)) (h2 : vsz a2 ≤ 3000 * (p+1)) (h3 : vsz a3 ≤ 3000 * (p+1)) (h4 : vsz a4 ≤ 3000 * (p+1)) (h5 : vsz a5 ≤ 3000 * (p+1)) (h6 : vsz a6 ≤ 3000 * (p+1)) (h7 : vsz a7 ≤ 3000 * (p+1)) (h8 : vsz a8 ≤ 3000 * (p+1)) :
    szl [a1, a2, a3, a4, a5, a6, a7, a8] + 1 ≤ 40000 * (p + 1) := by
  have h := szl_le_mul (M := 3000 * (p+1)) (W := [a1, a2, a3, a4, a5, a6, a7, a8]) (by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
  simp only [List.length_cons, List.length_nil] at h
  omega

theorem szl_bnd9 (p : ℕ) (a1 : Val) (a2 : Val) (a3 : Val) (a4 : Val) (a5 : Val) (a6 : Val) (a7 : Val) (a8 : Val) (a9 : Val) (h1 : vsz a1 ≤ 3000 * (p+1)) (h2 : vsz a2 ≤ 3000 * (p+1)) (h3 : vsz a3 ≤ 3000 * (p+1)) (h4 : vsz a4 ≤ 3000 * (p+1)) (h5 : vsz a5 ≤ 3000 * (p+1)) (h6 : vsz a6 ≤ 3000 * (p+1)) (h7 : vsz a7 ≤ 3000 * (p+1)) (h8 : vsz a8 ≤ 3000 * (p+1)) (h9 : vsz a9 ≤ 3000 * (p+1)) :
    szl [a1, a2, a3, a4, a5, a6, a7, a8, a9] + 1 ≤ 40000 * (p + 1) := by
  have h := szl_le_mul (M := 3000 * (p+1)) (W := [a1, a2, a3, a4, a5, a6, a7, a8, a9]) (by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
  simp only [List.length_cons, List.length_nil] at h
  omega

theorem szl_bnd10 (p : ℕ) (a1 : Val) (a2 : Val) (a3 : Val) (a4 : Val) (a5 : Val) (a6 : Val) (a7 : Val) (a8 : Val) (a9 : Val) (a10 : Val) (h1 : vsz a1 ≤ 3000 * (p+1)) (h2 : vsz a2 ≤ 3000 * (p+1)) (h3 : vsz a3 ≤ 3000 * (p+1)) (h4 : vsz a4 ≤ 3000 * (p+1)) (h5 : vsz a5 ≤ 3000 * (p+1)) (h6 : vsz a6 ≤ 3000 * (p+1)) (h7 : vsz a7 ≤ 3000 * (p+1)) (h8 : vsz a8 ≤ 3000 * (p+1)) (h9 : vsz a9 ≤ 3000 * (p+1)) (h10 : vsz a10 ≤ 3000 * (p+1)) :
    szl [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10] + 1 ≤ 40000 * (p + 1) := by
  have h := szl_le_mul (M := 3000 * (p+1)) (W := [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]) (by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
  simp only [List.length_cons, List.length_nil] at h
  omega

theorem szl_bnd11 (p : ℕ) (a1 : Val) (a2 : Val) (a3 : Val) (a4 : Val) (a5 : Val) (a6 : Val) (a7 : Val) (a8 : Val) (a9 : Val) (a10 : Val) (a11 : Val) (h1 : vsz a1 ≤ 3000 * (p+1)) (h2 : vsz a2 ≤ 3000 * (p+1)) (h3 : vsz a3 ≤ 3000 * (p+1)) (h4 : vsz a4 ≤ 3000 * (p+1)) (h5 : vsz a5 ≤ 3000 * (p+1)) (h6 : vsz a6 ≤ 3000 * (p+1)) (h7 : vsz a7 ≤ 3000 * (p+1)) (h8 : vsz a8 ≤ 3000 * (p+1)) (h9 : vsz a9 ≤ 3000 * (p+1)) (h10 : vsz a10 ≤ 3000 * (p+1)) (h11 : vsz a11 ≤ 3000 * (p+1)) :
    szl [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] + 1 ≤ 40000 * (p + 1) := by
  have h := szl_le_mul (M := 3000 * (p+1)) (W := [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]) (by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
  simp only [List.length_cons, List.length_nil] at h
  omega

theorem szl_bnd12 (p : ℕ) (a1 : Val) (a2 : Val) (a3 : Val) (a4 : Val) (a5 : Val) (a6 : Val) (a7 : Val) (a8 : Val) (a9 : Val) (a10 : Val) (a11 : Val) (a12 : Val) (h1 : vsz a1 ≤ 3000 * (p+1)) (h2 : vsz a2 ≤ 3000 * (p+1)) (h3 : vsz a3 ≤ 3000 * (p+1)) (h4 : vsz a4 ≤ 3000 * (p+1)) (h5 : vsz a5 ≤ 3000 * (p+1)) (h6 : vsz a6 ≤ 3000 * (p+1)) (h7 : vsz a7 ≤ 3000 * (p+1)) (h8 : vsz a8 ≤ 3000 * (p+1)) (h9 : vsz a9 ≤ 3000 * (p+1)) (h10 : vsz a10 ≤ 3000 * (p+1)) (h11 : vsz a11 ≤ 3000 * (p+1)) (h12 : vsz a12 ≤ 3000 * (p+1)) :
    szl [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12] + 1 ≤ 40000 * (p + 1) := by
  have h := szl_le_mul (M := 3000 * (p+1)) (W := [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12]) (by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
  simp only [List.length_cons, List.length_nil] at h
  omega

theorem szl_bnd13 (p : ℕ) (a1 : Val) (a2 : Val) (a3 : Val) (a4 : Val) (a5 : Val) (a6 : Val) (a7 : Val) (a8 : Val) (a9 : Val) (a10 : Val) (a11 : Val) (a12 : Val) (a13 : Val) (h1 : vsz a1 ≤ 3000 * (p+1)) (h2 : vsz a2 ≤ 3000 * (p+1)) (h3 : vsz a3 ≤ 3000 * (p+1)) (h4 : vsz a4 ≤ 3000 * (p+1)) (h5 : vsz a5 ≤ 3000 * (p+1)) (h6 : vsz a6 ≤ 3000 * (p+1)) (h7 : vsz a7 ≤ 3000 * (p+1)) (h8 : vsz a8 ≤ 3000 * (p+1)) (h9 : vsz a9 ≤ 3000 * (p+1)) (h10 : vsz a10 ≤ 3000 * (p+1)) (h11 : vsz a11 ≤ 3000 * (p+1)) (h12 : vsz a12 ≤ 3000 * (p+1)) (h13 : vsz a13 ≤ 3000 * (p+1)) :
    szl [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13] + 1 ≤ 40000 * (p + 1) := by
  have h := szl_le_mul (M := 3000 * (p+1)) (W := [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13]) (by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
  simp only [List.length_cons, List.length_nil] at h
  omega

theorem isz_ite_le (a : ℤ) : isz (if (0:ℤ) < a then 1 else 0) ≤ 3 := by
  split <;> simp [isz]
theorem isz_ite_le' (a : ℤ) : isz (if a < 0 then 1 else 0) ≤ 3 := by
  split <;> simp [isz]




open HvdH

/-- The `n`-step sign subroutine: `int a ↦ int (Int.sign a)`. -/
theorem TopSpec.sgn (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (a : ℤ),
      TopSpec main prog [.int a] [.int (Int.sign a)] (K * (isz a + 1)) := by
  obtain ⟨Dp, Kdu, hDp⟩ := TopSpec.dup hk
  obtain ⟨Pv, Kpv, hPv⟩ := TopSpec.pushVal hk
  obtain ⟨Sw, Ksw, hSw⟩ := TopSpec.swap hk
  obtain ⟨ltP, Klt, hlt⟩ := hi.lt
  obtain ⟨subP, Ksb, hsub⟩ := hi.sub
  refine ⟨.seq (.seq (.seq (.seq (.seq (.seq (.seq Dp (Pv (.int 0))) Sw) ltP) Sw) (Pv (.int 0))) ltP) subP,
    Kdu + 3 * Kpv + 3 * Ksw + 3 * Klt + 5 * Ksw + 3 * Kpv + 3 * Klt + 6 * Ksb, ?_⟩
  intro main a
  have h0 : isz (0:ℤ) = 2 := by simp [isz]
  have h1 : TopSpec main Dp [.int a] [.int a, .int a] (Kdu * (isz a + 1)) := by
    simpa [vsz_int] using hDp main (.int a)
  have h2 : TopSpec main (Pv (.int 0)) [.int a, .int a] [.int 0, .int a, .int a]
      (3 * Kpv * (isz a + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (hPv main (.int 0)) [.int a, .int a]) rfl rfl ?_
    rw [vsz_int]; have := Nat.zero_le (isz a); nlinarith
  have h3 : TopSpec main Sw [.int 0, .int a, .int a] [.int a, .int 0, .int a]
      (3 * Ksw * (isz a + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (hSw main (.int 0) (.int a)) [.int a]) rfl rfl ?_
    rw [vsz_int, vsz_int, h0]; have := Nat.zero_le (isz a); nlinarith
  have h4 : TopSpec main ltP [.int a, .int 0, .int a]
      [.int (if a < 0 then 1 else 0), .int a] (3 * Klt * (isz a + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (TopSpec.binOp hk (hlt main) (a := a) (b := 0) trivial)
      [.int a]) rfl rfl ?_
    rw [h0]; have := Nat.zero_le (isz a); nlinarith
  have h5 : TopSpec main Sw [.int (if a < 0 then 1 else 0), .int a]
      [.int a, .int (if a < 0 then 1 else 0)] (5 * Ksw * (isz a + 1)) := by
    refine TopSpec.mono hk (hSw main (.int (if a < 0 then 1 else 0)) (.int a)) rfl rfl ?_
    rw [vsz_int, vsz_int]
    have h3 := isz_ite_le' a
    have := Nat.zero_le (isz a); nlinarith
  have h6 : TopSpec main (Pv (.int 0)) [.int a, .int (if a < 0 then 1 else 0)]
      [.int 0, .int a, .int (if a < 0 then 1 else 0)] (3 * Kpv * (isz a + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (hPv main (.int 0))
      [.int a, .int (if a < 0 then 1 else 0)]) rfl rfl ?_
    rw [vsz_int]; have := Nat.zero_le (isz a); nlinarith
  have h7 : TopSpec main ltP [.int 0, .int a, .int (if a < 0 then 1 else 0)]
      [.int (if (0:ℤ) < a then 1 else 0), .int (if a < 0 then 1 else 0)]
      (3 * Klt * (isz a + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (TopSpec.binOp hk (hlt main) (a := 0) (b := a) trivial)
      [.int (if a < 0 then 1 else 0)]) rfl rfl ?_
    rw [h0]; have := Nat.zero_le (isz a); nlinarith
  have h8 : TopSpec main subP
      [.int (if (0:ℤ) < a then 1 else 0), .int (if a < 0 then 1 else 0)]
      [.int ((if (0:ℤ) < a then 1 else 0) - (if a < 0 then 1 else 0))] (6 * Ksb * (isz a + 1)) := by
    refine TopSpec.mono hk (TopSpec.binOp hk (hsub main)
      (a := (if (0:ℤ) < a then 1 else 0)) (b := (if a < 0 then 1 else 0)) trivial) rfl rfl ?_
    have h2' := isz_ite_le a
    have h3' := isz_ite_le' a
    have := Nat.zero_le (isz a); nlinarith
  have h123 := TopSpec.seq hk h1 h2
  have h1234 := TopSpec.seq hk h123 h3
  have h12345 := TopSpec.seq hk h1234 h4
  have h123456 := TopSpec.seq hk h12345 h5
  have h1234567 := TopSpec.seq hk h123456 h6
  have h12345678 := TopSpec.seq hk h1234567 h7
  have hAll := TopSpec.seq hk h12345678 h8
  refine TopSpec.mono hk hAll rfl ?_ ?_
  · rw [int_sign_eq]
  · exact le_of_eq (by ring)



open HvdH

theorem isz_sign_le (a : ℤ) : isz (Int.sign a) ≤ 3 := by
  rw [isz, Int.natAbs_sign]; split <;> simp

/-- The abs+sign subroutine: `int a ↦ int |a| :: int (sign a)`. -/
theorem TopSpec.absSgn (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (a : ℤ),
      TopSpec main prog [.int a] [.int (a.natAbs : ℤ), .int (Int.sign a)] (K * (isz a + 1)) := by
  obtain ⟨Dp, Kdu, hDp⟩ := TopSpec.dup hk
  obtain ⟨Sg, Ksg, hSg⟩ := TopSpec.sgn hk hi
  obtain ⟨Sw, Ksw, hSw⟩ := TopSpec.swap hk
  obtain ⟨negP, Kng, hng⟩ := hi.neg
  obtain ⟨maxP, Kmx, hmx⟩ := hi.max
  refine ⟨.seq (.seq (.seq (.seq (.seq Dp Sg) Sw) Dp) negP) maxP,
    Kdu + Ksg + 5 * Ksw + Kdu + Kng + 2 * Kmx, ?_⟩
  intro main a
  have h1 : TopSpec main Dp [.int a] [.int a, .int a] (Kdu * (isz a + 1)) := by
    simpa [vsz_int] using hDp main (.int a)
  have h2 : TopSpec main Sg [.int a, .int a] [.int (Int.sign a), .int a] (Ksg * (isz a + 1)) :=
    TopSpec.extend (hSg main a) [.int a]
  have h3 : TopSpec main Sw [.int (Int.sign a), .int a] [.int a, .int (Int.sign a)]
      (5 * Ksw * (isz a + 1)) := by
    refine TopSpec.mono hk (hSw main (.int (Int.sign a)) (.int a)) rfl rfl ?_
    rw [vsz_int, vsz_int]
    have h3' := isz_sign_le a
    have := Nat.zero_le (isz a); nlinarith
  have h4 : TopSpec main Dp [.int a, .int (Int.sign a)] [.int a, .int a, .int (Int.sign a)]
      (Kdu * (isz a + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (hDp main (.int a)) [.int (Int.sign a)]) rfl rfl ?_
    rw [vsz_int]
  have h5 : TopSpec main negP [.int a, .int a, .int (Int.sign a)]
      [.int (-a), .int a, .int (Int.sign a)] (Kng * (isz a + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (TopSpec.unOp hk (hng main) (a := a) trivial)
      [.int a, .int (Int.sign a)]) rfl rfl ?_
    have := Nat.zero_le (isz a); nlinarith
  have h6 : TopSpec main maxP [.int (-a), .int a, .int (Int.sign a)]
      [.int (a.natAbs : ℤ), .int (Int.sign a)] (2 * Kmx * (isz a + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (TopSpec.binOp hk (hmx main) (a := -a) (b := a) trivial)
      [.int (Int.sign a)]) rfl ?_ ?_
    · simp [int_max_neg_eq_natAbs]
    · rw [isz_neg]; have := Nat.zero_le (isz a); nlinarith
  have h12 := TopSpec.seq hk h1 h2
  have h123 := TopSpec.seq hk h12 h3
  have h1234 := TopSpec.seq hk h123 h4
  have h12345 := TopSpec.seq hk h1234 h5
  have hAll := TopSpec.seq hk h12345 h6
  refine TopSpec.mono hk hAll rfl rfl ?_
  exact le_of_eq (by ring)


theorem szl_take_le_x1 (W : List HvdH.Val) (n : ℕ) : szl (W.take n) ≤ szl W := by
  have h := szl_append (W.take n) (W.drop n)
  rw [List.take_append_drop] at h
  omega

theorem TopSpec.rollS (hk : HvdH.KernelLib) :
    ∃ (prog : ℕ → HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (k : ℕ) (W : List HvdH.Val),
      k < W.length →
      TopSpec main (prog k) W (W.getD k .nil :: W.eraseIdx k) (K * (k + 1) * (szl W + 1)) := by
  obtain ⟨prog, K, h⟩ := TopSpec.roll hk
  refine ⟨prog, K, fun main k W hklt => ?_⟩
  refine TopSpec.mono hk (h main k W hklt) rfl rfl ?_
  exact Nat.mul_le_mul_left (K * (k + 1)) (Nat.succ_le_succ (szl_take_le_x1 W (k + 1)))



open HvdH

/-- Fixed-point complex multiplication with the four real products done by the recursive `self`
(paper Lemma 2.4, fast variant). Input `int p :: cfxVal u :: cfxVal v`, output `cfxVal w` with
`inDisc p w` and `2^p ‖fxC p w - fxC p u * fxC p v‖ < 2`, cost `4 * Cm (p+2) + K * (p+1)`.
Route: take absolute values of the four coordinates (naturals, with `natAbs.size ≤ p+1 < p+2 < N`),
call `self` (`MulBelow main N Cm`) four times on the products of magnitudes `x*x'`, `y*y'`, `x*y'`,
`y*x'`, fix the signs with `hi.neg`, and round with `hi.tdiv` exactly as in `mulSField`
(`w = (Int.tdiv (x*x' - y*y') (2^p), Int.tdiv (x*y' + y*x') (2^p))`). `Monotone Cm` turns the
`mulSize` cost bound into `Cm (p+2)` per call. The helper framework `FxCommon`/`FxLin` composes
`WordR` words (`Spec`, `Spec.seq_det_lin`, `Spec.extend_exact`, `Spec.binOp`, `Spec.unOp`, ...). -/
theorem mulFField (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ) (p : ℕ), Monotone Cm →
      HvdH.MulBelow main N Cm → p + 2 < N → HvdH.WordR main prog
      (fun vs => ∃ (u v : ℤ × ℤ) (rest : List HvdH.Val),
        vs = HvdH.Val.int (p : ℤ) :: HvdH.cfxVal u :: HvdH.cfxVal v :: rest ∧
        HvdH.inDisc p u ∧ HvdH.inDisc p v)
      (fun vs out => ∃ (u v : ℤ × ℤ) (rest : List HvdH.Val) (w : ℤ × ℤ),
        vs = HvdH.Val.int (p : ℤ) :: HvdH.cfxVal u :: HvdH.cfxVal v :: rest ∧
        out = HvdH.cfxVal w :: rest ∧ HvdH.inDisc p w ∧
        (2 : ℝ) ^ p * ‖HvdH.fxC p w - HvdH.fxC p u * HvdH.fxC p v‖ < 2)
      (fun _ => 4 * Cm (p + 2) + K * (p + 1)) := by
  obtain ⟨Dp, Kdu, hDp⟩ := TopSpec.dup hk
  obtain ⟨Sw, Ksw, hSw⟩ := TopSpec.swap hk
  obtain ⟨Rl, Kro, hRl⟩ := TopSpec.rollS hk
  obtain ⟨Uc, Kuc, hUc⟩ := TopSpec.unconsV hk
  obtain ⟨Cv, Kcv, hCv⟩ := TopSpec.consV hk
  obtain ⟨AS, Kas, hAS⟩ := TopSpec.absSgn hk hi
  obtain ⟨mulSP, Kms, hms⟩ := hi.mulS
  obtain ⟨addP, Kad, had⟩ := hi.add
  obtain ⟨subP, Ksb, hsb⟩ := hi.sub
  obtain ⟨shrTP, Ksh, hsh⟩ := hi.shrT
  set Ksum : ℕ := Kdu + Ksw + Kro + Kuc + Kcv + Kas + Kms + Kad + Ksb + Ksh + 1 with hKsum
  set KB : ℕ := 1000000 * Ksum with hKB
  refine ⟨Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq ((Rl 2)) (Uc)) ((Rl 3))) (Uc)) (AS)) ((Rl 2))) (AS)) ((Rl 4))) (AS)) ((Rl 6))) (AS)) ((Rl 6))) (Dp)) ((Rl 6))) (Dp)) ((Rl 4))) (Dp)) ((Rl 7))) (Dp)) ((Rl 6))) ((Rl 1))) (.self)) ((Rl 4))) ((Rl 3))) (.self)) ((Rl 5))) ((Rl 4))) (.self)) ((Rl 4))) ((Rl 4))) (.self)) ((Rl 4))) (Dp)) ((Rl 6))) (Dp)) ((Rl 8))) (Dp)) ((Rl 10))) (Dp)) ((Rl 11))) ((Rl 5))) (mulSP)) ((Rl 1))) (mulSP)) ((Rl 9))) ((Rl 6))) (mulSP)) ((Rl 3))) (mulSP)) ((Rl 7))) ((Rl 6))) (mulSP)) ((Rl 3))) (mulSP)) ((Rl 5))) ((Rl 5))) (mulSP)) ((Rl 4))) (mulSP)) (addP)) (Sw)) ((Rl 2))) (subP)) ((Rl 2))) (Dp)) ((Rl 2))) (shrTP)) ((Rl 1))) ((Rl 2))) (shrTP)) (Sw)) (Cv), 100 * KB, ?_⟩
  intro main N Cm p hmono hmul hpN
  have hKdu : Kdu * 1000000 ≤ KB := by rw [hKB]; exact coeffK (by rw [hKsum]; omega)
  have hKsw : Ksw * 1000000 ≤ KB := by rw [hKB]; exact coeffK (by rw [hKsum]; omega)
  have hKro : Kro * 1000000 ≤ KB := by rw [hKB]; exact coeffK (by rw [hKsum]; omega)
  have hKas : Kas * 1000000 ≤ KB := by rw [hKB]; exact coeffK (by rw [hKsum]; omega)
  have hKms : Kms * 1000000 ≤ KB := by rw [hKB]; exact coeffK (by rw [hKsum]; omega)
  have hKad : Kad * 1000000 ≤ KB := by rw [hKB]; exact coeffK (by rw [hKsum]; omega)
  have hKsb : Ksb * 1000000 ≤ KB := by rw [hKB]; exact coeffK (by rw [hKsum]; omega)
  have hKsh : Ksh * 1000000 ≤ KB := by rw [hKB]; exact coeffK (by rw [hKsum]; omega)
  have hKucKB : Kuc ≤ KB * (p + 1) := by
    have h1 : Kuc ≤ KB := by rw [hKB]; nlinarith [show Kuc ≤ Ksum by rw [hKsum]; omega]
    nlinarith
  have hKcvKB : Kcv ≤ KB * (p + 1) := by
    have h1 : Kcv ≤ KB := by rw [hKB]; nlinarith [show Kcv ≤ Ksum by rw [hKsum]; omega]
    nlinarith
  intro vs hP s R hR
  rcases hP with ⟨u, v, rest, hvs, hU, hV⟩
  rcases u with ⟨x, y⟩
  rcases v with ⟨x', y'⟩
  have hU' : x ^ 2 + y ^ 2 ≤ 4 ^ p := hU
  have hV' : x' ^ 2 + y' ^ 2 ≤ 4 ^ p := hV
  set sx : ℤ := Int.sign x with hsx
  set sy : ℤ := Int.sign y with hsy
  set tx : ℤ := Int.sign x' with htx
  set ty : ℤ := Int.sign y' with hty
  set p1 : ℕ := x.natAbs * x'.natAbs with hp1
  set p2 : ℕ := y.natAbs * y'.natAbs with hp2
  set p3 : ℕ := x.natAbs * y'.natAbs with hp3
  set p4 : ℕ := y.natAbs * x'.natAbs with hp4
  set t1 : ℤ := sx * (tx * (p1 : ℤ)) with ht1
  set t2 : ℤ := sy * (ty * (p2 : ℤ)) with ht2
  set t3 : ℤ := sx * (ty * (p3 : ℤ)) with ht3
  set t4 : ℤ := sy * (tx * (p4 : ℤ)) with ht4
  set zA : ℤ := t1 - t2 with hA
  set zB : ℤ := t4 + t3 with hB
  set wr : ℤ := zA.tdiv ((2 : ℤ) ^ p) with hwr
  set wi : ℤ := zB.tdiv ((2 : ℤ) ^ p) with hwi
  have hxn : x.natAbs ≤ 2 ^ p := natAbs_le_two_pow (x := x) (y := y) hU'
  have hyn : y.natAbs ≤ 2 ^ p := natAbs_le_two_pow (x := y) (y := x) (by linarith)
  have hxqn : x'.natAbs ≤ 2 ^ p := natAbs_le_two_pow (x := x') (y := y') hV'
  have hyqn : y'.natAbs ≤ 2 ^ p := natAbs_le_two_pow (x := y') (y := x') (by linarith)
  have hsx1 : (x.natAbs).size ≤ p + 1 := size_le_of_le_two_pow hxn
  have hsy1 : (y.natAbs).size ≤ p + 1 := size_le_of_le_two_pow hyn
  have hsx1' : (x'.natAbs).size ≤ p + 1 := size_le_of_le_two_pow hxqn
  have hsy1' : (y'.natAbs).size ≤ p + 1 := size_le_of_le_two_pow hyqn
  have hsxx : sx * (x.natAbs : ℤ) = x := by rw [hsx]; exact Int.sign_mul_natAbs x
  have hsyy : sy * (y.natAbs : ℤ) = y := by rw [hsy]; exact Int.sign_mul_natAbs y
  have htxx : tx * (x'.natAbs : ℤ) = x' := by rw [htx]; exact Int.sign_mul_natAbs x'
  have htyy : ty * (y'.natAbs : ℤ) = y' := by rw [hty]; exact Int.sign_mul_natAbs y'
  have hp1b : p1 ≤ 2 ^ (2 * p) := by
    rw [hp1]
    calc x.natAbs * x'.natAbs ≤ 2^p * 2^p := Nat.mul_le_mul hxn hxqn
      _ = 2 ^ (2 * p) := by rw [← pow_add]; congr 1; omega
  have hp2b : p2 ≤ 2 ^ (2 * p) := by
    rw [hp2]
    calc y.natAbs * y'.natAbs ≤ 2^p * 2^p := Nat.mul_le_mul hyn hyqn
      _ = 2 ^ (2 * p) := by rw [← pow_add]; congr 1; omega
  have hp3b : p3 ≤ 2 ^ (2 * p) := by
    rw [hp3]
    calc x.natAbs * y'.natAbs ≤ 2^p * 2^p := Nat.mul_le_mul hxn hyqn
      _ = 2 ^ (2 * p) := by rw [← pow_add]; congr 1; omega
  have hp4b : p4 ≤ 2 ^ (2 * p) := by
    rw [hp4]
    calc y.natAbs * x'.natAbs ≤ 2^p * 2^p := Nat.mul_le_mul hyn hxqn
      _ = 2 ^ (2 * p) := by rw [← pow_add]; congr 1; omega
  have hsign (a : ℤ) : (Int.sign a).natAbs ≤ 1 := by rw [Int.natAbs_sign]; split <;> omega
  have ht1b : t1.natAbs ≤ 2 ^ (2 * p) := by
    rw [ht1, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, hp1]
    calc sx.natAbs * (tx.natAbs * (x.natAbs * x'.natAbs))
        ≤ 1 * (1 * (2^p * 2^p)) :=
          Nat.mul_le_mul (hsign x) (Nat.mul_le_mul (hsign x') (Nat.mul_le_mul hxn hxqn))
      _ = 2 ^ (2 * p) := by rw [one_mul, one_mul, ← pow_add]; congr 1; omega
  have ht2b : t2.natAbs ≤ 2 ^ (2 * p) := by
    rw [ht2, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast]
    rw [hp2]
    calc sy.natAbs * (ty.natAbs * (y.natAbs * y'.natAbs))
        ≤ 1 * (1 * (2^p * 2^p)) :=
          Nat.mul_le_mul (hsign y) (Nat.mul_le_mul (hsign y') (Nat.mul_le_mul hyn hyqn))
      _ = 2 ^ (2 * p) := by rw [one_mul, one_mul, ← pow_add]; congr 1; omega
  have ht3b : t3.natAbs ≤ 2 ^ (2 * p) := by
    rw [ht3, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast]
    rw [hp3]
    calc sx.natAbs * (ty.natAbs * (x.natAbs * y'.natAbs))
        ≤ 1 * (1 * (2^p * 2^p)) :=
          Nat.mul_le_mul (hsign x) (Nat.mul_le_mul (hsign y') (Nat.mul_le_mul hxn hyqn))
      _ = 2 ^ (2 * p) := by rw [one_mul, one_mul, ← pow_add]; congr 1; omega
  have ht4b : t4.natAbs ≤ 2 ^ (2 * p) := by
    rw [ht4, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast]
    rw [hp4]
    calc sy.natAbs * (tx.natAbs * (y.natAbs * x'.natAbs))
        ≤ 1 * (1 * (2^p * 2^p)) :=
          Nat.mul_le_mul (hsign y) (Nat.mul_le_mul (hsign x') (Nat.mul_le_mul hyn hxqn))
      _ = 2 ^ (2 * p) := by rw [one_mul, one_mul, ← pow_add]; congr 1; omega
  have hAb : zA.natAbs ≤ 2 ^ (2 * p + 1) := by
    rw [hA]
    calc (t1 - t2).natAbs ≤ t1.natAbs + t2.natAbs := Int.natAbs_sub_le t1 t2
      _ ≤ 2^(2*p) + 2^(2*p) := Nat.add_le_add ht1b ht2b
      _ = 2 ^ (2 * p + 1) := by rw [pow_succ]; ring
  have hBb : zB.natAbs ≤ 2 ^ (2 * p + 1) := by
    rw [hB]
    calc (t4 + t3).natAbs ≤ t4.natAbs + t3.natAbs := Int.natAbs_add_le t4 t3
      _ ≤ 2^(2*p) + 2^(2*p) := Nat.add_le_add ht4b ht3b
      _ = 2 ^ (2 * p + 1) := by rw [pow_succ]; ring
  have hwrb : wr.natAbs ≤ 2 ^ (2 * p + 1) := by
    rw [hwr, Int.natAbs_tdiv]
    calc zA.natAbs / ((2:ℤ)^p).natAbs ≤ zA.natAbs := Nat.div_le_self _ _
      _ ≤ 2 ^ (2 * p + 1) := hAb
  have hwib : wi.natAbs ≤ 2 ^ (2 * p + 1) := by
    rw [hwi, Int.natAbs_tdiv]
    calc zB.natAbs / ((2:ℤ)^p).natAbs ≤ zB.natAbs := Nat.div_le_self _ _
      _ ≤ 2 ^ (2 * p + 1) := hBb
  have ht1x : t1 = x * x' := by
    have h1 : (p1 : ℤ) = (x.natAbs : ℤ) * (x'.natAbs : ℤ) := by rw [hp1, Nat.cast_mul]
    have h2 : t1 = (sx * (x.natAbs : ℤ)) * (tx * (x'.natAbs : ℤ)) := by rw [ht1, h1]; ring
    rw [h2, hsxx, htxx]
  have ht2y : t2 = y * y' := by
    have h1 : (p2 : ℤ) = (y.natAbs : ℤ) * (y'.natAbs : ℤ) := by rw [hp2, Nat.cast_mul]
    have h2 : t2 = (sy * (y.natAbs : ℤ)) * (ty * (y'.natAbs : ℤ)) := by rw [ht2, h1]; ring
    rw [h2, hsyy, htyy]
  have ht3x : t3 = x * y' := by
    have h1 : (p3 : ℤ) = (x.natAbs : ℤ) * (y'.natAbs : ℤ) := by rw [hp3, Nat.cast_mul]
    have h2 : t3 = (sx * (x.natAbs : ℤ)) * (ty * (y'.natAbs : ℤ)) := by rw [ht3, h1]; ring
    rw [h2, hsxx, htyy]
  have ht4x : t4 = y * x' := by
    have h1 : (p4 : ℤ) = (y.natAbs : ℤ) * (x'.natAbs : ℤ) := by rw [hp4, Nat.cast_mul]
    have h2 : t4 = (sy * (y.natAbs : ℤ)) * (tx * (x'.natAbs : ℤ)) := by rw [ht4, h1]; ring
    rw [h2, hsyy, htxx]
  have hAx : zA = x * x' - y * y' := by rw [hA, ht1x, ht2y]
  have hBx : zB = x * y' + y * x' := by rw [hB, ht4x, ht3x]; ring
  have hwr' : wr = (x * x' - y * y').tdiv ((2 : ℤ) ^ p) := by rw [hwr, hAx]
  have hwi' : wi = (x * y' + y * x').tdiv ((2 : ℤ) ^ p) := by rw [hwi, hBx]
  have hiP : isz ((p : ℤ)) ≤ 1000 * (p + 1) := by rw [isz, Int.natAbs_natCast]; have := size_le_of_le_two_pow (Nat.le_of_lt (Nat.lt_two_pow_self (n := p))); omega
  have hiX : isz (x) ≤ 1000 * (p + 1) := isz_le_M hxn
  have hiY : isz (y) ≤ 1000 * (p + 1) := isz_le_M hyn
  have hiXq : isz (x') ≤ 1000 * (p + 1) := isz_le_M hxqn
  have hiYq : isz (y') ≤ 1000 * (p + 1) := isz_le_M hyqn
  
  have hiAX : isz ((x.natAbs : ℤ)) ≤ 1000 * (p + 1) := by
    have h : isz ((x.natAbs : ℤ)) = isz x := by rw [isz, isz, Int.natAbs_natCast]
    rw [h]; exact hiX
  have hiAY : isz ((y.natAbs : ℤ)) ≤ 1000 * (p + 1) := by
    have h : isz ((y.natAbs : ℤ)) = isz y := by rw [isz, isz, Int.natAbs_natCast]
    rw [h]; exact hiY
  have hiBX : isz ((x'.natAbs : ℤ)) ≤ 1000 * (p + 1) := by
    have h : isz ((x'.natAbs : ℤ)) = isz x' := by rw [isz, isz, Int.natAbs_natCast]
    rw [h]; exact hiXq
  have hiBY : isz ((y'.natAbs : ℤ)) ≤ 1000 * (p + 1) := by
    have h : isz ((y'.natAbs : ℤ)) = isz y' := by rw [isz, isz, Int.natAbs_natCast]
    rw [h]; exact hiYq
  have hiSX : isz (sx) ≤ 1000 * (p + 1) := by rw [hsx]; have := isz_sign_le x; omega
  have hiSY : isz (sy) ≤ 1000 * (p + 1) := by rw [hsy]; have := isz_sign_le y; omega
  have hiTX : isz (tx) ≤ 1000 * (p + 1) := by rw [htx]; have := isz_sign_le x'; omega
  have hiTY : isz (ty) ≤ 1000 * (p + 1) := by rw [hty]; have := isz_sign_le y'; omega
  have hiP1 : isz ((p1 : ℤ)) ≤ 1000 * (p + 1) := by have h := isz_le_of_natAbs_le_x1 (z := (p1 : ℤ)) (p := 2*p) (by rw [Int.natAbs_natCast]; exact hp1b); omega
  have hiP2 : isz ((p2 : ℤ)) ≤ 1000 * (p + 1) := by have h := isz_le_of_natAbs_le_x1 (z := (p2 : ℤ)) (p := 2*p) (by rw [Int.natAbs_natCast]; exact hp2b); omega
  have hiP3 : isz ((p3 : ℤ)) ≤ 1000 * (p + 1) := by have h := isz_le_of_natAbs_le_x1 (z := (p3 : ℤ)) (p := 2*p) (by rw [Int.natAbs_natCast]; exact hp3b); omega
  have hiP4 : isz ((p4 : ℤ)) ≤ 1000 * (p + 1) := by have h := isz_le_of_natAbs_le_x1 (z := (p4 : ℤ)) (p := 2*p) (by rw [Int.natAbs_natCast]; exact hp4b); omega
  have hiT1 : isz (t1) ≤ 1000 * (p + 1) := by have h := isz_le_of_natAbs_le_x1 (z := t1) (p := 2*p) ht1b; omega
  have hiT2 : isz (t2) ≤ 1000 * (p + 1) := by have h := isz_le_of_natAbs_le_x1 (z := t2) (p := 2*p) ht2b; omega
  have hiT3 : isz (t3) ≤ 1000 * (p + 1) := by have h := isz_le_of_natAbs_le_x1 (z := t3) (p := 2*p) ht3b; omega
  have hiT4 : isz (t4) ≤ 1000 * (p + 1) := by have h := isz_le_of_natAbs_le_x1 (z := t4) (p := 2*p) ht4b; omega
  have hiTXP1 : isz (tx * (p1 : ℤ)) ≤ 1000 * (p + 1) := by
    have hs : tx.natAbs ≤ 1 := by rw [htx, Int.natAbs_sign]; split <;> omega
    have hnat : (tx * (p1 : ℤ)).natAbs ≤ 2 ^ (2 * p) := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      calc tx.natAbs * p1 ≤ 1 * p1 := Nat.mul_le_mul hs le_rfl
        _ = p1 := by ring
        _ ≤ 2 ^ (2 * p) := hp1b
    have h := isz_le_of_natAbs_le_x1 (z := tx * (p1 : ℤ)) (p := 2 * p) hnat
    omega
  have hiTYP2 : isz (ty * (p2 : ℤ)) ≤ 1000 * (p + 1) := by
    have hs : ty.natAbs ≤ 1 := by rw [hty, Int.natAbs_sign]; split <;> omega
    have hnat : (ty * (p2 : ℤ)).natAbs ≤ 2 ^ (2 * p) := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      calc ty.natAbs * p2 ≤ 1 * p2 := Nat.mul_le_mul hs le_rfl
        _ = p2 := by ring
        _ ≤ 2 ^ (2 * p) := hp2b
    have h := isz_le_of_natAbs_le_x1 (z := ty * (p2 : ℤ)) (p := 2 * p) hnat
    omega
  have hiTYP3 : isz (ty * (p3 : ℤ)) ≤ 1000 * (p + 1) := by
    have hs : ty.natAbs ≤ 1 := by rw [hty, Int.natAbs_sign]; split <;> omega
    have hnat : (ty * (p3 : ℤ)).natAbs ≤ 2 ^ (2 * p) := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      calc ty.natAbs * p3 ≤ 1 * p3 := Nat.mul_le_mul hs le_rfl
        _ = p3 := by ring
        _ ≤ 2 ^ (2 * p) := hp3b
    have h := isz_le_of_natAbs_le_x1 (z := ty * (p3 : ℤ)) (p := 2 * p) hnat
    omega
  have hiTXP4 : isz (tx * (p4 : ℤ)) ≤ 1000 * (p + 1) := by
    have hs : tx.natAbs ≤ 1 := by rw [htx, Int.natAbs_sign]; split <;> omega
    have hnat : (tx * (p4 : ℤ)).natAbs ≤ 2 ^ (2 * p) := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      calc tx.natAbs * p4 ≤ 1 * p4 := Nat.mul_le_mul hs le_rfl
        _ = p4 := by ring
        _ ≤ 2 ^ (2 * p) := hp4b
    have h := isz_le_of_natAbs_le_x1 (z := tx * (p4 : ℤ)) (p := 2 * p) hnat
    omega
  have hiA : isz (zA) ≤ 1000 * (p + 1) := by have h := isz_le_of_natAbs_le_x1 (z := zA) (p := 2*p+1) hAb; omega
  have hiB : isz (zB) ≤ 1000 * (p + 1) := by have h := isz_le_of_natAbs_le_x1 (z := zB) (p := 2*p+1) hBb; omega
  have hiWR : isz (wr) ≤ 1000 * (p + 1) := by have h := isz_le_of_natAbs_le_x1 (z := wr) (p := 2*p+1) hwrb; omega
  have hiWI : isz (wi) ≤ 1000 * (p + 1) := by have h := isz_le_of_natAbs_le_x1 (z := wi) (p := 2*p+1) hwib; omega
  have hsx3 : isz sx ≤ 3 := by rw [hsx]; exact isz_sign_le x
  have hsy3 : isz sy ≤ 3 := by rw [hsy]; exact isz_sign_le y
  have htx3 : isz tx ≤ 3 := by rw [htx]; exact isz_sign_le x'
  have hty3 : isz ty ≤ 3 := by rw [hty]; exact isz_sign_le y'
  have hvP : vsz (.int (p : ℤ)) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiP; omega
  have hvU : vsz (cfxVal (x, y)) ≤ 3000 * (p + 1) := by
    rw [show cfxVal (x, y) = .cons (.int x) (.int y) from rfl, vsz_cons, vsz_int, vsz_int]
    have := hiX; have := hiY; omega
  have hvV : vsz (cfxVal (x', y')) ≤ 3000 * (p + 1) := by
    rw [show cfxVal (x', y') = .cons (.int x') (.int y') from rfl, vsz_cons, vsz_int, vsz_int]
    have := hiXq; have := hiYq; omega
  have hvX : vsz (.int x) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiX; omega
  have hvY : vsz (.int y) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiY; omega
  have hvXq : vsz (.int x') ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiXq; omega
  have hvYq : vsz (.int y') ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiYq; omega
  have hvAX : vsz (.int (x.natAbs : ℤ)) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiAX; omega
  have hvAY : vsz (.int (y.natAbs : ℤ)) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiAY; omega
  have hvBX : vsz (.int (x'.natAbs : ℤ)) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiBX; omega
  have hvBY : vsz (.int (y'.natAbs : ℤ)) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiBY; omega
  have hvSX : vsz (.int sx) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiSX; omega
  have hvSY : vsz (.int sy) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiSY; omega
  have hvTX : vsz (.int tx) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiTX; omega
  have hvTY : vsz (.int ty) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiTY; omega
  have hvP1 : vsz (.int (p1 : ℤ)) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiP1; omega
  have hvP2 : vsz (.int (p2 : ℤ)) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiP2; omega
  have hvP3 : vsz (.int (p3 : ℤ)) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiP3; omega
  have hvP4 : vsz (.int (p4 : ℤ)) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiP4; omega
  have hvT1 : vsz (.int t1) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiT1; omega
  have hvT2 : vsz (.int t2) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiT2; omega
  have hvT3 : vsz (.int t3) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiT3; omega
  have hvT4 : vsz (.int t4) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiT4; omega
  have hvTXP1 : vsz (.int (tx * (p1 : ℤ))) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiTXP1; omega
  have hvTYP2 : vsz (.int (ty * (p2 : ℤ))) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiTYP2; omega
  have hvTYP3 : vsz (.int (ty * (p3 : ℤ))) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiTYP3; omega
  have hvTXP4 : vsz (.int (tx * (p4 : ℤ))) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiTXP4; omega
  have hvAA : vsz (.int zA) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiA; omega
  have hvBB : vsz (.int zB) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiB; omega
  have hvWR : vsz (.int wr) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiWR; omega
  have hvWI : vsz (.int wi) ≤ 3000 * (p + 1) := by rw [vsz_int]; have := hiWI; omega
  have sr1 : TopSpec main (Rl 2) [.int (p : ℤ), cfxVal (x, y), cfxVal (x', y')] [cfxVal (x', y'), .int (p : ℤ), cfxVal (x, y)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 2 [.int (p : ℤ), cfxVal (x, y), cfxVal (x', y')] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd3 p (.int (p : ℤ)) (cfxVal (x, y)) (cfxVal (x', y')) hvP hvU hvV)
  have su2 : TopSpec main Uc [cfxVal (x', y'), .int (p : ℤ), cfxVal (x, y)] [.int x', .int y', .int (p : ℤ), cfxVal (x, y)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (hUc main (.int x') (.int y')) [.int (p : ℤ), cfxVal (x, y)]) rfl rfl ?_
    exact hKucKB
  have sr3 : TopSpec main (Rl 3) [.int x', .int y', .int (p : ℤ), cfxVal (x, y)] [cfxVal (x, y), .int x', .int y', .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 3 [.int x', .int y', .int (p : ℤ), cfxVal (x, y)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd4 p (.int x') (.int y') (.int (p : ℤ)) (cfxVal (x, y)) hvXq hvYq hvP hvU)
  have su4 : TopSpec main Uc [cfxVal (x, y), .int x', .int y', .int (p : ℤ)] [.int x, .int y, .int x', .int y', .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (hUc main (.int x) (.int y)) [.int x', .int y', .int (p : ℤ)]) rfl rfl ?_
    exact hKucKB
  have sa5 : TopSpec main AS [.int x, .int y, .int x', .int y', .int (p : ℤ)] [.int (x.natAbs), .int sx, .int y, .int x', .int y', .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (hAS main x) [.int y, .int x', .int y', .int (p : ℤ)]) rfl (by simp [← hsx]) ?_
    exact cost_one_x1 hKas (by have hh := hiX; omega)
  have sr6 : TopSpec main (Rl 2) [.int (x.natAbs), .int sx, .int y, .int x', .int y', .int (p : ℤ)] [.int y, .int (x.natAbs), .int sx, .int x', .int y', .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 2 [.int (x.natAbs), .int sx, .int y, .int x', .int y', .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd6 p (.int (x.natAbs)) (.int sx) (.int y) (.int x') (.int y') (.int (p : ℤ)) hvAX hvSX hvY hvXq hvYq hvP)
  have sa7 : TopSpec main AS [.int y, .int (x.natAbs), .int sx, .int x', .int y', .int (p : ℤ)] [.int (y.natAbs), .int sy, .int (x.natAbs), .int sx, .int x', .int y', .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (hAS main y) [.int (x.natAbs), .int sx, .int x', .int y', .int (p : ℤ)]) rfl (by simp [← hsy]) ?_
    exact cost_one_x1 hKas (by have hh := hiY; omega)
  have sr8 : TopSpec main (Rl 4) [.int (y.natAbs), .int sy, .int (x.natAbs), .int sx, .int x', .int y', .int (p : ℤ)] [.int x', .int (y.natAbs), .int sy, .int (x.natAbs), .int sx, .int y', .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 4 [.int (y.natAbs), .int sy, .int (x.natAbs), .int sx, .int x', .int y', .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd7 p (.int (y.natAbs)) (.int sy) (.int (x.natAbs)) (.int sx) (.int x') (.int y') (.int (p : ℤ)) hvAY hvSY hvAX hvSX hvXq hvYq hvP)
  have sa9 : TopSpec main AS [.int x', .int (y.natAbs), .int sy, .int (x.natAbs), .int sx, .int y', .int (p : ℤ)] [.int (x'.natAbs), .int tx, .int (y.natAbs), .int sy, .int (x.natAbs), .int sx, .int y', .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (hAS main x') [.int (y.natAbs), .int sy, .int (x.natAbs), .int sx, .int y', .int (p : ℤ)]) rfl (by simp [← htx]) ?_
    exact cost_one_x1 hKas (by have hh := hiXq; omega)
  have sr10 : TopSpec main (Rl 6) [.int (x'.natAbs), .int tx, .int (y.natAbs), .int sy, .int (x.natAbs), .int sx, .int y', .int (p : ℤ)] [.int y', .int (x'.natAbs), .int tx, .int (y.natAbs), .int sy, .int (x.natAbs), .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 6 [.int (x'.natAbs), .int tx, .int (y.natAbs), .int sy, .int (x.natAbs), .int sx, .int y', .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd8 p (.int (x'.natAbs)) (.int tx) (.int (y.natAbs)) (.int sy) (.int (x.natAbs)) (.int sx) (.int y') (.int (p : ℤ)) hvBX hvTX hvAY hvSY hvAX hvSX hvYq hvP)
  have sa11 : TopSpec main AS [.int y', .int (x'.natAbs), .int tx, .int (y.natAbs), .int sy, .int (x.natAbs), .int sx, .int (p : ℤ)] [.int (y'.natAbs), .int ty, .int (x'.natAbs), .int tx, .int (y.natAbs), .int sy, .int (x.natAbs), .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (hAS main y') [.int (x'.natAbs), .int tx, .int (y.natAbs), .int sy, .int (x.natAbs), .int sx, .int (p : ℤ)]) rfl (by simp [← hty]) ?_
    exact cost_one_x1 hKas (by have hh := hiYq; omega)
  have sr12 : TopSpec main (Rl 6) [.int (y'.natAbs), .int ty, .int (x'.natAbs), .int tx, .int (y.natAbs), .int sy, .int (x.natAbs), .int sx, .int (p : ℤ)] [.int (x.natAbs), .int (y'.natAbs), .int ty, .int (x'.natAbs), .int tx, .int (y.natAbs), .int sy, .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 6 [.int (y'.natAbs), .int ty, .int (x'.natAbs), .int tx, .int (y.natAbs), .int sy, .int (x.natAbs), .int sx, .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd9 p (.int (y'.natAbs)) (.int ty) (.int (x'.natAbs)) (.int tx) (.int (y.natAbs)) (.int sy) (.int (x.natAbs)) (.int sx) (.int (p : ℤ)) hvBY hvTY hvBX hvTX hvAY hvSY hvAX hvSX hvP)
  have sd13 : TopSpec main Dp [.int (x.natAbs), .int (y'.natAbs), .int ty, .int (x'.natAbs), .int tx, .int (y.natAbs), .int sy, .int sx, .int (p : ℤ)] [.int (x.natAbs), .int (x.natAbs), .int (y'.natAbs), .int ty, .int (x'.natAbs), .int tx, .int (y.natAbs), .int sy, .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (hDp main (.int (x.natAbs))) [.int (y'.natAbs), .int ty, .int (x'.natAbs), .int tx, .int (y.natAbs), .int sy, .int sx, .int (p : ℤ)]) rfl rfl ?_
    exact cost_one_x1 hKdu (by have := hvAX; omega)
  have sr14 : TopSpec main (Rl 6) [.int (x.natAbs), .int (x.natAbs), .int (y'.natAbs), .int ty, .int (x'.natAbs), .int tx, .int (y.natAbs), .int sy, .int sx, .int (p : ℤ)] [.int (y.natAbs), .int (x.natAbs), .int (x.natAbs), .int (y'.natAbs), .int ty, .int (x'.natAbs), .int tx, .int sy, .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 6 [.int (x.natAbs), .int (x.natAbs), .int (y'.natAbs), .int ty, .int (x'.natAbs), .int tx, .int (y.natAbs), .int sy, .int sx, .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd10 p (.int (x.natAbs)) (.int (x.natAbs)) (.int (y'.natAbs)) (.int ty) (.int (x'.natAbs)) (.int tx) (.int (y.natAbs)) (.int sy) (.int sx) (.int (p : ℤ)) hvAX hvAX hvBY hvTY hvBX hvTX hvAY hvSY hvSX hvP)
  have sd15 : TopSpec main Dp [.int (y.natAbs), .int (x.natAbs), .int (x.natAbs), .int (y'.natAbs), .int ty, .int (x'.natAbs), .int tx, .int sy, .int sx, .int (p : ℤ)] [.int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int (x.natAbs), .int (y'.natAbs), .int ty, .int (x'.natAbs), .int tx, .int sy, .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (hDp main (.int (y.natAbs))) [.int (x.natAbs), .int (x.natAbs), .int (y'.natAbs), .int ty, .int (x'.natAbs), .int tx, .int sy, .int sx, .int (p : ℤ)]) rfl rfl ?_
    exact cost_one_x1 hKdu (by have := hvAY; omega)
  have sr16 : TopSpec main (Rl 4) [.int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int (x.natAbs), .int (y'.natAbs), .int ty, .int (x'.natAbs), .int tx, .int sy, .int sx, .int (p : ℤ)] [.int (y'.natAbs), .int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int (x.natAbs), .int ty, .int (x'.natAbs), .int tx, .int sy, .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 4 [.int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int (x.natAbs), .int (y'.natAbs), .int ty, .int (x'.natAbs), .int tx, .int sy, .int sx, .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd11 p (.int (y.natAbs)) (.int (y.natAbs)) (.int (x.natAbs)) (.int (x.natAbs)) (.int (y'.natAbs)) (.int ty) (.int (x'.natAbs)) (.int tx) (.int sy) (.int sx) (.int (p : ℤ)) hvAY hvAY hvAX hvAX hvBY hvTY hvBX hvTX hvSY hvSX hvP)
  have sd17 : TopSpec main Dp [.int (y'.natAbs), .int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int (x.natAbs), .int ty, .int (x'.natAbs), .int tx, .int sy, .int sx, .int (p : ℤ)] [.int (y'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int (x.natAbs), .int ty, .int (x'.natAbs), .int tx, .int sy, .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (hDp main (.int (y'.natAbs))) [.int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int (x.natAbs), .int ty, .int (x'.natAbs), .int tx, .int sy, .int sx, .int (p : ℤ)]) rfl rfl ?_
    exact cost_one_x1 hKdu (by have := hvBY; omega)
  have sr18 : TopSpec main (Rl 7) [.int (y'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int (x.natAbs), .int ty, .int (x'.natAbs), .int tx, .int sy, .int sx, .int (p : ℤ)] [.int (x'.natAbs), .int (y'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 7 [.int (y'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int (x.natAbs), .int ty, .int (x'.natAbs), .int tx, .int sy, .int sx, .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd12 p (.int (y'.natAbs)) (.int (y'.natAbs)) (.int (y.natAbs)) (.int (y.natAbs)) (.int (x.natAbs)) (.int (x.natAbs)) (.int ty) (.int (x'.natAbs)) (.int tx) (.int sy) (.int sx) (.int (p : ℤ)) hvBY hvBY hvAY hvAY hvAX hvAX hvTY hvBX hvTX hvSY hvSX hvP)
  have sd19 : TopSpec main Dp [.int (x'.natAbs), .int (y'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] [.int (x'.natAbs), .int (x'.natAbs), .int (y'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (hDp main (.int (x'.natAbs))) [.int (y'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)]) rfl rfl ?_
    exact cost_one_x1 hKdu (by have := hvBX; omega)
  have sr20 : TopSpec main (Rl 6) [.int (x'.natAbs), .int (x'.natAbs), .int (y'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] [.int (x.natAbs), .int (x'.natAbs), .int (x'.natAbs), .int (y'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 6 [.int (x'.natAbs), .int (x'.natAbs), .int (y'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd13 p (.int (x'.natAbs)) (.int (x'.natAbs)) (.int (y'.natAbs)) (.int (y'.natAbs)) (.int (y.natAbs)) (.int (y.natAbs)) (.int (x.natAbs)) (.int (x.natAbs)) (.int ty) (.int tx) (.int sy) (.int sx) (.int (p : ℤ)) hvBX hvBX hvBY hvBY hvAY hvAY hvAX hvAX hvTY hvTX hvSY hvSX hvP)
  have sr21 : TopSpec main (Rl 1) [.int (x.natAbs), .int (x'.natAbs), .int (x'.natAbs), .int (y'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] [.int (x'.natAbs), .int (x.natAbs), .int (x'.natAbs), .int (y'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 1 [.int (x.natAbs), .int (x'.natAbs), .int (x'.natAbs), .int (y'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd13 p (.int (x.natAbs)) (.int (x'.natAbs)) (.int (x'.natAbs)) (.int (y'.natAbs)) (.int (y'.natAbs)) (.int (y.natAbs)) (.int (y.natAbs)) (.int (x.natAbs)) (.int ty) (.int tx) (.int sy) (.int sx) (.int (p : ℤ)) hvAX hvBX hvBX hvBY hvBY hvAY hvAY hvAX hvTY hvTX hvSY hvSX hvP)
  have sm22 : TopSpec main .self [.int (x'.natAbs), .int (x.natAbs), .int (x'.natAbs), .int (y'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] [.int (p1 : ℤ), .int (x'.natAbs), .int (y'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (Cm (p + 2)) := by
    refine TopSpec.mono hk (TopSpec.extend (TopSpec.selfMul hk hmul (x := x'.natAbs) (y := x.natAbs) (by omega) (by omega)) [.int (x'.natAbs), .int (y'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)]) rfl (by rw [hp1, Nat.mul_comm x.natAbs x'.natAbs]; simp) ?_
    exact hmono (by omega)
  have sr23 : TopSpec main (Rl 4) [.int (p1 : ℤ), .int (x'.natAbs), .int (y'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] [.int (y.natAbs), .int (p1 : ℤ), .int (x'.natAbs), .int (y'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 4 [.int (p1 : ℤ), .int (x'.natAbs), .int (y'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (y.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd12 p (.int (p1 : ℤ)) (.int (x'.natAbs)) (.int (y'.natAbs)) (.int (y'.natAbs)) (.int (y.natAbs)) (.int (y.natAbs)) (.int (x.natAbs)) (.int ty) (.int tx) (.int sy) (.int sx) (.int (p : ℤ)) hvP1 hvBX hvBY hvBY hvAY hvAY hvAX hvTY hvTX hvSY hvSX hvP)
  have sr24 : TopSpec main (Rl 3) [.int (y.natAbs), .int (p1 : ℤ), .int (x'.natAbs), .int (y'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] [.int (y'.natAbs), .int (y.natAbs), .int (p1 : ℤ), .int (x'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 3 [.int (y.natAbs), .int (p1 : ℤ), .int (x'.natAbs), .int (y'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd12 p (.int (y.natAbs)) (.int (p1 : ℤ)) (.int (x'.natAbs)) (.int (y'.natAbs)) (.int (y'.natAbs)) (.int (y.natAbs)) (.int (x.natAbs)) (.int ty) (.int tx) (.int sy) (.int sx) (.int (p : ℤ)) hvAY hvP1 hvBX hvBY hvBY hvAY hvAX hvTY hvTX hvSY hvSX hvP)
  have sm25 : TopSpec main .self [.int (y'.natAbs), .int (y.natAbs), .int (p1 : ℤ), .int (x'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] [.int (p2 : ℤ), .int (p1 : ℤ), .int (x'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (Cm (p + 2)) := by
    refine TopSpec.mono hk (TopSpec.extend (TopSpec.selfMul hk hmul (x := y'.natAbs) (y := y.natAbs) (by omega) (by omega)) [.int (p1 : ℤ), .int (x'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)]) rfl (by rw [hp2, Nat.mul_comm y.natAbs y'.natAbs]; simp) ?_
    exact hmono (by omega)
  have sr26 : TopSpec main (Rl 5) [.int (p2 : ℤ), .int (p1 : ℤ), .int (x'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] [.int (x.natAbs), .int (p2 : ℤ), .int (p1 : ℤ), .int (x'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 5 [.int (p2 : ℤ), .int (p1 : ℤ), .int (x'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int (x.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd11 p (.int (p2 : ℤ)) (.int (p1 : ℤ)) (.int (x'.natAbs)) (.int (y'.natAbs)) (.int (y.natAbs)) (.int (x.natAbs)) (.int ty) (.int tx) (.int sy) (.int sx) (.int (p : ℤ)) hvP2 hvP1 hvBX hvBY hvAY hvAX hvTY hvTX hvSY hvSX hvP)
  have sr27 : TopSpec main (Rl 4) [.int (x.natAbs), .int (p2 : ℤ), .int (p1 : ℤ), .int (x'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] [.int (y'.natAbs), .int (x.natAbs), .int (p2 : ℤ), .int (p1 : ℤ), .int (x'.natAbs), .int (y.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 4 [.int (x.natAbs), .int (p2 : ℤ), .int (p1 : ℤ), .int (x'.natAbs), .int (y'.natAbs), .int (y.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd11 p (.int (x.natAbs)) (.int (p2 : ℤ)) (.int (p1 : ℤ)) (.int (x'.natAbs)) (.int (y'.natAbs)) (.int (y.natAbs)) (.int ty) (.int tx) (.int sy) (.int sx) (.int (p : ℤ)) hvAX hvP2 hvP1 hvBX hvBY hvAY hvTY hvTX hvSY hvSX hvP)
  have sm28 : TopSpec main .self [.int (y'.natAbs), .int (x.natAbs), .int (p2 : ℤ), .int (p1 : ℤ), .int (x'.natAbs), .int (y.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] [.int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int (x'.natAbs), .int (y.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (Cm (p + 2)) := by
    refine TopSpec.mono hk (TopSpec.extend (TopSpec.selfMul hk hmul (x := y'.natAbs) (y := x.natAbs) (by omega) (by omega)) [.int (p2 : ℤ), .int (p1 : ℤ), .int (x'.natAbs), .int (y.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)]) rfl (by rw [hp3, Nat.mul_comm x.natAbs y'.natAbs]; simp) ?_
    exact hmono (by omega)
  have sr29 : TopSpec main (Rl 4) [.int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int (x'.natAbs), .int (y.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] [.int (y.natAbs), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int (x'.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 4 [.int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int (x'.natAbs), .int (y.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd10 p (.int (p3 : ℤ)) (.int (p2 : ℤ)) (.int (p1 : ℤ)) (.int (x'.natAbs)) (.int (y.natAbs)) (.int ty) (.int tx) (.int sy) (.int sx) (.int (p : ℤ)) hvP3 hvP2 hvP1 hvBX hvAY hvTY hvTX hvSY hvSX hvP)
  have sr30 : TopSpec main (Rl 4) [.int (y.natAbs), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int (x'.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] [.int (x'.natAbs), .int (y.natAbs), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 4 [.int (y.natAbs), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int (x'.natAbs), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd10 p (.int (y.natAbs)) (.int (p3 : ℤ)) (.int (p2 : ℤ)) (.int (p1 : ℤ)) (.int (x'.natAbs)) (.int ty) (.int tx) (.int sy) (.int sx) (.int (p : ℤ)) hvAY hvP3 hvP2 hvP1 hvBX hvTY hvTX hvSY hvSX hvP)
  have sm31 : TopSpec main .self [.int (x'.natAbs), .int (y.natAbs), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] [.int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (Cm (p + 2)) := by
    refine TopSpec.mono hk (TopSpec.extend (TopSpec.selfMul hk hmul (x := x'.natAbs) (y := y.natAbs) (by omega) (by omega)) [.int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)]) rfl (by rw [hp4, Nat.mul_comm y.natAbs x'.natAbs]; simp) ?_
    exact hmono (by omega)
  have sr32 : TopSpec main (Rl 4) [.int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] [.int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int tx, .int sy, .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 4 [.int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int ty, .int tx, .int sy, .int sx, .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd9 p (.int (p4 : ℤ)) (.int (p3 : ℤ)) (.int (p2 : ℤ)) (.int (p1 : ℤ)) (.int ty) (.int tx) (.int sy) (.int sx) (.int (p : ℤ)) hvP4 hvP3 hvP2 hvP1 hvTY hvTX hvSY hvSX hvP)
  have sd33 : TopSpec main Dp [.int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int tx, .int sy, .int sx, .int (p : ℤ)] [.int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int tx, .int sy, .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (hDp main (.int ty)) [.int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int tx, .int sy, .int sx, .int (p : ℤ)]) rfl rfl ?_
    exact cost_one_x1 hKdu (by have := hvTY; omega)
  have sr34 : TopSpec main (Rl 6) [.int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int tx, .int sy, .int sx, .int (p : ℤ)] [.int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int sy, .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 6 [.int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int tx, .int sy, .int sx, .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd10 p (.int ty) (.int ty) (.int (p4 : ℤ)) (.int (p3 : ℤ)) (.int (p2 : ℤ)) (.int (p1 : ℤ)) (.int tx) (.int sy) (.int sx) (.int (p : ℤ)) hvTY hvTY hvP4 hvP3 hvP2 hvP1 hvTX hvSY hvSX hvP)
  have sd35 : TopSpec main Dp [.int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int sy, .int sx, .int (p : ℤ)] [.int tx, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int sy, .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (hDp main (.int tx)) [.int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int sy, .int sx, .int (p : ℤ)]) rfl rfl ?_
    exact cost_one_x1 hKdu (by have := hvTX; omega)
  have sr36 : TopSpec main (Rl 8) [.int tx, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int sy, .int sx, .int (p : ℤ)] [.int sy, .int tx, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 8 [.int tx, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int sy, .int sx, .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd11 p (.int tx) (.int tx) (.int ty) (.int ty) (.int (p4 : ℤ)) (.int (p3 : ℤ)) (.int (p2 : ℤ)) (.int (p1 : ℤ)) (.int sy) (.int sx) (.int (p : ℤ)) hvTX hvTX hvTY hvTY hvP4 hvP3 hvP2 hvP1 hvSY hvSX hvP)
  have sd37 : TopSpec main Dp [.int sy, .int tx, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int sx, .int (p : ℤ)] [.int sy, .int sy, .int tx, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int sx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (hDp main (.int sy)) [.int tx, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int sx, .int (p : ℤ)]) rfl rfl ?_
    exact cost_one_x1 hKdu (by have := hvSY; omega)
  have sr38 : TopSpec main (Rl 10) [.int sy, .int sy, .int tx, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int sx, .int (p : ℤ)] [.int sx, .int sy, .int sy, .int tx, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 10 [.int sy, .int sy, .int tx, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int sx, .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd12 p (.int sy) (.int sy) (.int tx) (.int tx) (.int ty) (.int ty) (.int (p4 : ℤ)) (.int (p3 : ℤ)) (.int (p2 : ℤ)) (.int (p1 : ℤ)) (.int sx) (.int (p : ℤ)) hvSY hvSY hvTX hvTX hvTY hvTY hvP4 hvP3 hvP2 hvP1 hvSX hvP)
  have sd39 : TopSpec main Dp [.int sx, .int sy, .int sy, .int tx, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int (p : ℤ)] [.int sx, .int sx, .int sy, .int sy, .int tx, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (hDp main (.int sx)) [.int sy, .int sy, .int tx, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int (p : ℤ)]) rfl rfl ?_
    exact cost_one_x1 hKdu (by have := hvSX; omega)
  have sr40 : TopSpec main (Rl 11) [.int sx, .int sx, .int sy, .int sy, .int tx, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int (p : ℤ)] [.int (p1 : ℤ), .int sx, .int sx, .int sy, .int sy, .int tx, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 11 [.int sx, .int sx, .int sy, .int sy, .int tx, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p1 : ℤ), .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd13 p (.int sx) (.int sx) (.int sy) (.int sy) (.int tx) (.int tx) (.int ty) (.int ty) (.int (p4 : ℤ)) (.int (p3 : ℤ)) (.int (p2 : ℤ)) (.int (p1 : ℤ)) (.int (p : ℤ)) hvSX hvSX hvSY hvSY hvTX hvTX hvTY hvTY hvP4 hvP3 hvP2 hvP1 hvP)
  have sr41 : TopSpec main (Rl 5) [.int (p1 : ℤ), .int sx, .int sx, .int sy, .int sy, .int tx, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p : ℤ)] [.int tx, .int (p1 : ℤ), .int sx, .int sx, .int sy, .int sy, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 5 [.int (p1 : ℤ), .int sx, .int sx, .int sy, .int sy, .int tx, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd13 p (.int (p1 : ℤ)) (.int sx) (.int sx) (.int sy) (.int sy) (.int tx) (.int tx) (.int ty) (.int ty) (.int (p4 : ℤ)) (.int (p3 : ℤ)) (.int (p2 : ℤ)) (.int (p : ℤ)) hvP1 hvSX hvSX hvSY hvSY hvTX hvTX hvTY hvTY hvP4 hvP3 hvP2 hvP)
  have sm42 : TopSpec main mulSP [.int tx, .int (p1 : ℤ), .int sx, .int sx, .int sy, .int sy, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p : ℤ)] [.int (tx * (p1 : ℤ)), .int sx, .int sx, .int sy, .int sy, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (TopSpec.binOp hk (hms main) trivial) [.int sx, .int sx, .int sy, .int sy, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p : ℤ)]) rfl rfl ?_
    exact cost_smallmul hKms (by have := htx3; omega) (by have := hiP1; omega)
  have sr43 : TopSpec main (Rl 1) [.int (tx * (p1 : ℤ)), .int sx, .int sx, .int sy, .int sy, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p : ℤ)] [.int sx, .int (tx * (p1 : ℤ)), .int sx, .int sy, .int sy, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 1 [.int (tx * (p1 : ℤ)), .int sx, .int sx, .int sy, .int sy, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd12 p (.int (tx * (p1 : ℤ))) (.int sx) (.int sx) (.int sy) (.int sy) (.int tx) (.int ty) (.int ty) (.int (p4 : ℤ)) (.int (p3 : ℤ)) (.int (p2 : ℤ)) (.int (p : ℤ)) hvTXP1 hvSX hvSX hvSY hvSY hvTX hvTY hvTY hvP4 hvP3 hvP2 hvP)
  have sm44 : TopSpec main mulSP [.int sx, .int (tx * (p1 : ℤ)), .int sx, .int sy, .int sy, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p : ℤ)] [.int t1, .int sx, .int sy, .int sy, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (TopSpec.binOp hk (hms main) trivial) [.int sx, .int sy, .int sy, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p : ℤ)]) rfl (by simp [ht1]) ?_
    exact cost_smallmul hKms (by have := hsx3; omega) (by have := hiTXP1; omega)
  have sr45 : TopSpec main (Rl 9) [.int t1, .int sx, .int sy, .int sy, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p : ℤ)] [.int (p2 : ℤ), .int t1, .int sx, .int sy, .int sy, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 9 [.int t1, .int sx, .int sy, .int sy, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p2 : ℤ), .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd11 p (.int t1) (.int sx) (.int sy) (.int sy) (.int tx) (.int ty) (.int ty) (.int (p4 : ℤ)) (.int (p3 : ℤ)) (.int (p2 : ℤ)) (.int (p : ℤ)) hvT1 hvSX hvSY hvSY hvTX hvTY hvTY hvP4 hvP3 hvP2 hvP)
  have sr46 : TopSpec main (Rl 6) [.int (p2 : ℤ), .int t1, .int sx, .int sy, .int sy, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p : ℤ)] [.int ty, .int (p2 : ℤ), .int t1, .int sx, .int sy, .int sy, .int tx, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 6 [.int (p2 : ℤ), .int t1, .int sx, .int sy, .int sy, .int tx, .int ty, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd11 p (.int (p2 : ℤ)) (.int t1) (.int sx) (.int sy) (.int sy) (.int tx) (.int ty) (.int ty) (.int (p4 : ℤ)) (.int (p3 : ℤ)) (.int (p : ℤ)) hvP2 hvT1 hvSX hvSY hvSY hvTX hvTY hvTY hvP4 hvP3 hvP)
  have sm47 : TopSpec main mulSP [.int ty, .int (p2 : ℤ), .int t1, .int sx, .int sy, .int sy, .int tx, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p : ℤ)] [.int (ty * (p2 : ℤ)), .int t1, .int sx, .int sy, .int sy, .int tx, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (TopSpec.binOp hk (hms main) trivial) [.int t1, .int sx, .int sy, .int sy, .int tx, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p : ℤ)]) rfl rfl ?_
    exact cost_smallmul hKms (by have := hty3; omega) (by have := hiP2; omega)
  have sr48 : TopSpec main (Rl 3) [.int (ty * (p2 : ℤ)), .int t1, .int sx, .int sy, .int sy, .int tx, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p : ℤ)] [.int sy, .int (ty * (p2 : ℤ)), .int t1, .int sx, .int sy, .int tx, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 3 [.int (ty * (p2 : ℤ)), .int t1, .int sx, .int sy, .int sy, .int tx, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd10 p (.int (ty * (p2 : ℤ))) (.int t1) (.int sx) (.int sy) (.int sy) (.int tx) (.int ty) (.int (p4 : ℤ)) (.int (p3 : ℤ)) (.int (p : ℤ)) hvTYP2 hvT1 hvSX hvSY hvSY hvTX hvTY hvP4 hvP3 hvP)
  have sm49 : TopSpec main mulSP [.int sy, .int (ty * (p2 : ℤ)), .int t1, .int sx, .int sy, .int tx, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p : ℤ)] [.int t2, .int t1, .int sx, .int sy, .int tx, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (TopSpec.binOp hk (hms main) trivial) [.int t1, .int sx, .int sy, .int tx, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p : ℤ)]) rfl (by simp [ht2]) ?_
    exact cost_smallmul hKms (by have := hsy3; omega) (by have := hiTYP2; omega)
  have sr50 : TopSpec main (Rl 7) [.int t2, .int t1, .int sx, .int sy, .int tx, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p : ℤ)] [.int (p3 : ℤ), .int t2, .int t1, .int sx, .int sy, .int tx, .int ty, .int (p4 : ℤ), .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 7 [.int t2, .int t1, .int sx, .int sy, .int tx, .int ty, .int (p4 : ℤ), .int (p3 : ℤ), .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd9 p (.int t2) (.int t1) (.int sx) (.int sy) (.int tx) (.int ty) (.int (p4 : ℤ)) (.int (p3 : ℤ)) (.int (p : ℤ)) hvT2 hvT1 hvSX hvSY hvTX hvTY hvP4 hvP3 hvP)
  have sr51 : TopSpec main (Rl 6) [.int (p3 : ℤ), .int t2, .int t1, .int sx, .int sy, .int tx, .int ty, .int (p4 : ℤ), .int (p : ℤ)] [.int ty, .int (p3 : ℤ), .int t2, .int t1, .int sx, .int sy, .int tx, .int (p4 : ℤ), .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 6 [.int (p3 : ℤ), .int t2, .int t1, .int sx, .int sy, .int tx, .int ty, .int (p4 : ℤ), .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd9 p (.int (p3 : ℤ)) (.int t2) (.int t1) (.int sx) (.int sy) (.int tx) (.int ty) (.int (p4 : ℤ)) (.int (p : ℤ)) hvP3 hvT2 hvT1 hvSX hvSY hvTX hvTY hvP4 hvP)
  have sm52 : TopSpec main mulSP [.int ty, .int (p3 : ℤ), .int t2, .int t1, .int sx, .int sy, .int tx, .int (p4 : ℤ), .int (p : ℤ)] [.int (ty * (p3 : ℤ)), .int t2, .int t1, .int sx, .int sy, .int tx, .int (p4 : ℤ), .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (TopSpec.binOp hk (hms main) trivial) [.int t2, .int t1, .int sx, .int sy, .int tx, .int (p4 : ℤ), .int (p : ℤ)]) rfl rfl ?_
    exact cost_smallmul hKms (by have := hty3; omega) (by have := hiP3; omega)
  have sr53 : TopSpec main (Rl 3) [.int (ty * (p3 : ℤ)), .int t2, .int t1, .int sx, .int sy, .int tx, .int (p4 : ℤ), .int (p : ℤ)] [.int sx, .int (ty * (p3 : ℤ)), .int t2, .int t1, .int sy, .int tx, .int (p4 : ℤ), .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 3 [.int (ty * (p3 : ℤ)), .int t2, .int t1, .int sx, .int sy, .int tx, .int (p4 : ℤ), .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd8 p (.int (ty * (p3 : ℤ))) (.int t2) (.int t1) (.int sx) (.int sy) (.int tx) (.int (p4 : ℤ)) (.int (p : ℤ)) hvTYP3 hvT2 hvT1 hvSX hvSY hvTX hvP4 hvP)
  have sm54 : TopSpec main mulSP [.int sx, .int (ty * (p3 : ℤ)), .int t2, .int t1, .int sy, .int tx, .int (p4 : ℤ), .int (p : ℤ)] [.int t3, .int t2, .int t1, .int sy, .int tx, .int (p4 : ℤ), .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (TopSpec.binOp hk (hms main) trivial) [.int t2, .int t1, .int sy, .int tx, .int (p4 : ℤ), .int (p : ℤ)]) rfl (by simp [ht3]) ?_
    exact cost_smallmul hKms (by have := hsx3; omega) (by have := hiTYP3; omega)
  have sr55 : TopSpec main (Rl 5) [.int t3, .int t2, .int t1, .int sy, .int tx, .int (p4 : ℤ), .int (p : ℤ)] [.int (p4 : ℤ), .int t3, .int t2, .int t1, .int sy, .int tx, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 5 [.int t3, .int t2, .int t1, .int sy, .int tx, .int (p4 : ℤ), .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd7 p (.int t3) (.int t2) (.int t1) (.int sy) (.int tx) (.int (p4 : ℤ)) (.int (p : ℤ)) hvT3 hvT2 hvT1 hvSY hvTX hvP4 hvP)
  have sr56 : TopSpec main (Rl 5) [.int (p4 : ℤ), .int t3, .int t2, .int t1, .int sy, .int tx, .int (p : ℤ)] [.int tx, .int (p4 : ℤ), .int t3, .int t2, .int t1, .int sy, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 5 [.int (p4 : ℤ), .int t3, .int t2, .int t1, .int sy, .int tx, .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd7 p (.int (p4 : ℤ)) (.int t3) (.int t2) (.int t1) (.int sy) (.int tx) (.int (p : ℤ)) hvP4 hvT3 hvT2 hvT1 hvSY hvTX hvP)
  have sm57 : TopSpec main mulSP [.int tx, .int (p4 : ℤ), .int t3, .int t2, .int t1, .int sy, .int (p : ℤ)] [.int (tx * (p4 : ℤ)), .int t3, .int t2, .int t1, .int sy, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (TopSpec.binOp hk (hms main) trivial) [.int t3, .int t2, .int t1, .int sy, .int (p : ℤ)]) rfl rfl ?_
    exact cost_smallmul hKms (by have := htx3; omega) (by have := hiP4; omega)
  have sr58 : TopSpec main (Rl 4) [.int (tx * (p4 : ℤ)), .int t3, .int t2, .int t1, .int sy, .int (p : ℤ)] [.int sy, .int (tx * (p4 : ℤ)), .int t3, .int t2, .int t1, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 4 [.int (tx * (p4 : ℤ)), .int t3, .int t2, .int t1, .int sy, .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd6 p (.int (tx * (p4 : ℤ))) (.int t3) (.int t2) (.int t1) (.int sy) (.int (p : ℤ)) hvTXP4 hvT3 hvT2 hvT1 hvSY hvP)
  have sm59 : TopSpec main mulSP [.int sy, .int (tx * (p4 : ℤ)), .int t3, .int t2, .int t1, .int (p : ℤ)] [.int t4, .int t3, .int t2, .int t1, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (TopSpec.binOp hk (hms main) trivial) [.int t3, .int t2, .int t1, .int (p : ℤ)]) rfl (by simp [ht4]) ?_
    exact cost_smallmul hKms (by have := hsy3; omega) (by have := hiTXP4; omega)
  have sa60 : TopSpec main addP [.int t4, .int t3, .int t2, .int t1, .int (p : ℤ)] [.int zB, .int t2, .int t1, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (TopSpec.binOp hk (had main) trivial) [.int t2, .int t1, .int (p : ℤ)]) rfl rfl ?_
    exact cost_binL hKad (by have := hiT4; omega) (by have := hiT3; omega)
  have ss61 : TopSpec main Sw [.int zB, .int t2, .int t1, .int (p : ℤ)] [.int t2, .int zB, .int t1, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (hSw main (.int zB) (.int t2)) [.int t1, .int (p : ℤ)]) rfl rfl ?_
    exact cost_one_x1 hKsw (by have := hvBB; have := hvT2; omega)
  have sr62 : TopSpec main (Rl 2) [.int t2, .int zB, .int t1, .int (p : ℤ)] [.int t1, .int t2, .int zB, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 2 [.int t2, .int zB, .int t1, .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd4 p (.int t2) (.int zB) (.int t1) (.int (p : ℤ)) hvT2 hvBB hvT1 hvP)
  have ss63 : TopSpec main subP [.int t1, .int t2, .int zB, .int (p : ℤ)] [.int zA, .int zB, .int (p : ℤ)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (TopSpec.binOp hk (hsb main) trivial) [.int zB, .int (p : ℤ)]) rfl (by simp [hA]) ?_
    exact cost_binL hKsb (by have := hiT1; omega) (by have := hiT2; omega)
  have sr64 : TopSpec main (Rl 2) [.int zA, .int zB, .int (p : ℤ)] [.int (p : ℤ), .int zA, .int zB] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 2 [.int zA, .int zB, .int (p : ℤ)] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd3 p (.int zA) (.int zB) (.int (p : ℤ)) hvAA hvBB hvP)
  have sd65 : TopSpec main Dp [.int (p : ℤ), .int zA, .int zB] [.int (p : ℤ), .int (p : ℤ), .int zA, .int zB] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (hDp main (.int (p : ℤ))) [.int zA, .int zB]) rfl rfl ?_
    exact cost_one_x1 hKdu (by have := hvP; omega)
  have sr66 : TopSpec main (Rl 2) [.int (p : ℤ), .int (p : ℤ), .int zA, .int zB] [.int zA, .int (p : ℤ), .int (p : ℤ), .int zB] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 2 [.int (p : ℤ), .int (p : ℤ), .int zA, .int zB] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd4 p (.int (p : ℤ)) (.int (p : ℤ)) (.int zA) (.int zB) hvP hvP hvAA hvBB)
  have sh67 : TopSpec main shrTP [.int zA, .int (p : ℤ), .int (p : ℤ), .int zB] [.int wr, .int (p : ℤ), .int zB] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (TopSpec.binOp hk (hsh main) (by exact Int.natCast_nonneg p)) [.int (p : ℤ), .int zB]) rfl (by simp [hwr, Int.toNat_natCast]) ?_
    exact cost_binL hKsh (by have := hiA; omega) (by have := hiP; omega)
  have sr68 : TopSpec main (Rl 1) [.int wr, .int (p : ℤ), .int zB] [.int (p : ℤ), .int wr, .int zB] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 1 [.int wr, .int (p : ℤ), .int zB] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd3 p (.int wr) (.int (p : ℤ)) (.int zB) hvWR hvP hvBB)
  have sr69 : TopSpec main (Rl 2) [.int (p : ℤ), .int wr, .int zB] [.int zB, .int (p : ℤ), .int wr] (KB * (p + 1)) := by
    refine TopSpec.mono hk (hRl main 2 [.int (p : ℤ), .int wr, .int zB] (by simp)) rfl (by simp) ?_
    exact cost_roll hKro (by norm_num) (szl_bnd3 p (.int (p : ℤ)) (.int wr) (.int zB) hvP hvWR hvBB)
  have sh70 : TopSpec main shrTP [.int zB, .int (p : ℤ), .int wr] [.int wi, .int wr] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (TopSpec.binOp hk (hsh main) (by exact Int.natCast_nonneg p)) [.int wr]) rfl (by simp [hwi, Int.toNat_natCast]) ?_
    exact cost_binL hKsh (by have := hiB; omega) (by have := hiP; omega)
  have ss71 : TopSpec main Sw [.int wi, .int wr] [.int wr, .int wi] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (hSw main (.int wi) (.int wr)) []) rfl rfl ?_
    exact cost_one_x1 hKsw (by have := hvWR; have := hvWI; omega)
  have sc72 : TopSpec main Cv [.int wr, .int wi] [cfxVal (wr, wi)] (KB * (p + 1)) := by
    refine TopSpec.mono hk (TopSpec.extend (hCv main (.int wr) (.int wi)) []) rfl rfl ?_
    exact hKcvKB
  have c1 := TopSpec.seq hk sr1 su2
  have c2 := TopSpec.seq hk c1 sr3
  have c3 := TopSpec.seq hk c2 su4
  have c4 := TopSpec.seq hk c3 sa5
  have c5 := TopSpec.seq hk c4 sr6
  have c6 := TopSpec.seq hk c5 sa7
  have c7 := TopSpec.seq hk c6 sr8
  have c8 := TopSpec.seq hk c7 sa9
  have c9 := TopSpec.seq hk c8 sr10
  have c10 := TopSpec.seq hk c9 sa11
  have c11 := TopSpec.seq hk c10 sr12
  have c12 := TopSpec.seq hk c11 sd13
  have c13 := TopSpec.seq hk c12 sr14
  have c14 := TopSpec.seq hk c13 sd15
  have c15 := TopSpec.seq hk c14 sr16
  have c16 := TopSpec.seq hk c15 sd17
  have c17 := TopSpec.seq hk c16 sr18
  have c18 := TopSpec.seq hk c17 sd19
  have c19 := TopSpec.seq hk c18 sr20
  have c20 := TopSpec.seq hk c19 sr21
  have c21 := TopSpec.seq hk c20 sm22
  have c22 := TopSpec.seq hk c21 sr23
  have c23 := TopSpec.seq hk c22 sr24
  have c24 := TopSpec.seq hk c23 sm25
  have c25 := TopSpec.seq hk c24 sr26
  have c26 := TopSpec.seq hk c25 sr27
  have c27 := TopSpec.seq hk c26 sm28
  have c28 := TopSpec.seq hk c27 sr29
  have c29 := TopSpec.seq hk c28 sr30
  have c30 := TopSpec.seq hk c29 sm31
  have c31 := TopSpec.seq hk c30 sr32
  have c32 := TopSpec.seq hk c31 sd33
  have c33 := TopSpec.seq hk c32 sr34
  have c34 := TopSpec.seq hk c33 sd35
  have c35 := TopSpec.seq hk c34 sr36
  have c36 := TopSpec.seq hk c35 sd37
  have c37 := TopSpec.seq hk c36 sr38
  have c38 := TopSpec.seq hk c37 sd39
  have c39 := TopSpec.seq hk c38 sr40
  have c40 := TopSpec.seq hk c39 sr41
  have c41 := TopSpec.seq hk c40 sm42
  have c42 := TopSpec.seq hk c41 sr43
  have c43 := TopSpec.seq hk c42 sm44
  have c44 := TopSpec.seq hk c43 sr45
  have c45 := TopSpec.seq hk c44 sr46
  have c46 := TopSpec.seq hk c45 sm47
  have c47 := TopSpec.seq hk c46 sr48
  have c48 := TopSpec.seq hk c47 sm49
  have c49 := TopSpec.seq hk c48 sr50
  have c50 := TopSpec.seq hk c49 sr51
  have c51 := TopSpec.seq hk c50 sm52
  have c52 := TopSpec.seq hk c51 sr53
  have c53 := TopSpec.seq hk c52 sm54
  have c54 := TopSpec.seq hk c53 sr55
  have c55 := TopSpec.seq hk c54 sr56
  have c56 := TopSpec.seq hk c55 sm57
  have c57 := TopSpec.seq hk c56 sr58
  have c58 := TopSpec.seq hk c57 sm59
  have c59 := TopSpec.seq hk c58 sa60
  have c60 := TopSpec.seq hk c59 ss61
  have c61 := TopSpec.seq hk c60 sr62
  have c62 := TopSpec.seq hk c61 ss63
  have c63 := TopSpec.seq hk c62 sr64
  have c64 := TopSpec.seq hk c63 sd65
  have c65 := TopSpec.seq hk c64 sr66
  have c66 := TopSpec.seq hk c65 sh67
  have c67 := TopSpec.seq hk c66 sr68
  have c68 := TopSpec.seq hk c67 sr69
  have c69 := TopSpec.seq hk c68 sh70
  have c70 := TopSpec.seq hk c69 ss71
  have c71 := TopSpec.seq hk c70 sc72
  have cfin : TopSpec main (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq ((Rl 2)) (Uc)) ((Rl 3))) (Uc)) (AS)) ((Rl 2))) (AS)) ((Rl 4))) (AS)) ((Rl 6))) (AS)) ((Rl 6))) (Dp)) ((Rl 6))) (Dp)) ((Rl 4))) (Dp)) ((Rl 7))) (Dp)) ((Rl 6))) ((Rl 1))) (.self)) ((Rl 4))) ((Rl 3))) (.self)) ((Rl 5))) ((Rl 4))) (.self)) ((Rl 4))) ((Rl 4))) (.self)) ((Rl 4))) (Dp)) ((Rl 6))) (Dp)) ((Rl 8))) (Dp)) ((Rl 10))) (Dp)) ((Rl 11))) ((Rl 5))) (mulSP)) ((Rl 1))) (mulSP)) ((Rl 9))) ((Rl 6))) (mulSP)) ((Rl 3))) (mulSP)) ((Rl 7))) ((Rl 6))) (mulSP)) ((Rl 3))) (mulSP)) ((Rl 5))) ((Rl 5))) (mulSP)) ((Rl 4))) (mulSP)) (addP)) (Sw)) ((Rl 2))) (subP)) ((Rl 2))) (Dp)) ((Rl 2))) (shrTP)) ((Rl 1))) ((Rl 2))) (shrTP)) (Sw)) (Cv)) [.int (p : ℤ), cfxVal (x, y), cfxVal (x', y')] [cfxVal (wr, wi)] (4 * Cm (p + 2) + 100 * KB * (p + 1)) :=
    TopSpec.mono hk c71 rfl rfl (by nlinarith [Nat.zero_le (Cm (p + 2)), Nat.zero_le KB, Nat.zero_le p])
  have hmain := cfin rest
  obtain ⟨out, s', n, hout, hev, hcost, hstk, hoth⟩ := hmain vs hvs s R hR
  refine ⟨out, s', n, ?_, hev, hcost, hstk, hoth⟩
  refine ⟨(x, y), (x', y'), rest, (wr, wi), hvs, ?_, ?_, ?_⟩
  · rw [hout]; rfl
  · rw [hwr', hwi']; exact (mulF_approx p x y x' y' hU hV).1
  · rw [hwr', hwi']; exact (mulF_approx p x y x' y' hU hV).2

end Work.Fx
