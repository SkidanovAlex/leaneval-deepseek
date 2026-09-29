import Mathlib
import Submission.Work.Params.basic
import Submission.Work.Params.defs

/-!
# A small "stack machine" toolkit for the `Params` program.

Every command of `KernelLib`/`IntLib` is turned into a step lemma of the shape
`WordR main p (fun vs => vs = L) (fun _ out => out = M) (fun _ => c)` with `c` an explicit
cost bound, i.e. it turns the *exact* stack `L` into the *exact* stack `M`.  `seqC` composes
two such steps, so a long straight-line program is proved by a chain of `seqC` applications.
-/

set_option autoImplicit false

namespace Work.Params

open HvdH

variable {main : Cmd}

/-- Compose two steps whose intermediate stack is *exactly* `M`. -/
theorem seqC (hK : KernelLib) {p q : Cmd} {L M N : List Val} {c c' : ℕ}
    (hp : WordR main p (fun vs => vs = L) (fun _ out => out = M) (fun _ => c))
    (hq : WordR main q (fun vs => vs = M) (fun _ out => out = N) (fun _ => c')) :
    WordR main (.seq p q) (fun vs => vs = L) (fun _ out => out = N) (fun _ => c + c') := by
  have h := hK.seq main p q (fun vs => vs = L) (fun _ out => out = M) (fun _ => c)
    (fun vs => vs = M) (fun _ out => out = N) (fun _ => c') (fun _ => c') hp hq
    (fun vs mid _ hM => ⟨hM, le_refl _⟩)
  refine hK.conseq main (.seq p q) (fun vs => vs = L) (fun vs => vs = L)
    (fun vs out => ∃ mid, mid = M ∧ out = N) (fun _ out => out = N) (fun _ => c + c') (fun _ => c + c')
    h (fun _ hh => hh) ?_ (fun _ _ => le_refl _)
  intro vs out _ hq
  obtain ⟨mid, -, hout⟩ := hq
  exact hout

/-- Turn a `WordR` with "structural" pre/post into one with exact states. -/
theorem lift (hK : KernelLib) {p : Cmd} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {C : List Val → ℕ} (h : WordR main p P Q C) {L M : List Val} {c : ℕ}
    (hP : P L) (hQ : ∀ out, Q L out → out = M) (hC : C L ≤ c) :
    WordR main p (fun vs => vs = L) (fun _ out => out = M) (fun _ => c) := by
  refine hK.conseq main p P (fun vs => vs = L) Q (fun _ out => out = M) C (fun _ => c) h ?_ ?_ ?_
  · intro vs hvs; rw [hvs]; exact hP
  · intro vs out hvs hq; rw [hvs] at hq; exact hQ out hq
  · intro vs hvs; rw [hvs]; exact hC

/-- Re-bound the cost of a step. -/
theorem conseqC (hK : KernelLib) {p : Cmd} {L M : List Val} {c c' : ℕ}
    (h : WordR main p (fun vs => vs = L) (fun _ out => out = M) (fun _ => c)) (hc : c ≤ c') :
    WordR main p (fun vs => vs = L) (fun _ out => out = M) (fun _ => c') := by
  refine hK.conseq main p (fun vs => vs = L) (fun vs => vs = L) (fun _ out => out = M)
    (fun _ out => out = M) (fun _ => c) (fun _ => c') h (fun _ hh => hh) (fun _ _ _ hq => hq)
    (fun _ _ => hc)

/-! ## `IntLib` operations -/

theorem unStep {p : Cmd} {f : ℤ → ℤ} {P : ℤ → Prop} {C : ℤ → ℕ}
    (hK : KernelLib) (h : UnOp main p P f C) (a : ℤ) (tl : List Val) (hPa : P a) (c : ℕ) (hc : C a ≤ c) :
    WordR main p (fun vs => vs = .int a :: tl) (fun _ out => out = .int (f a) :: tl) (fun _ => c) := by
  refine lift hK h ⟨a, tl, rfl, hPa⟩ ?_ hc
  intro out hq
  obtain ⟨a', rest, hv, hout⟩ := hq
  cases hv
  exact hout

theorem binStep {p : Cmd} {f : ℤ → ℤ → ℤ} {P : ℤ → ℤ → Prop} {C : ℤ → ℤ → ℕ}
    (hK : KernelLib) (h : BinOp main p P f C) (a b : ℤ) (tl : List Val) (hP : P a b)
    (c : ℕ) (hc : C a b ≤ c) :
    WordR main p (fun vs => vs = .int a :: .int b :: tl) (fun _ out => out = .int (f a b) :: tl)
      (fun _ => c) := by
  refine lift hK h ⟨a, b, tl, rfl, hP⟩ ?_ hc
  intro out hq
  obtain ⟨a', b', rest, hv, hout⟩ := hq
  cases hv
  exact hout

/-! ## `KernelLib` operations -/

theorem dupStep (hK : KernelLib) {p : Cmd} {K0 : ℕ}
    (h : WordR main p (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => K0 * (vsz (vs.headD .nil) + 1)))
    (a : Val) (tl : List Val) (c : ℕ) (hc : K0 * (vsz a + 1) ≤ c) :
    WordR main p (fun vs => vs = a :: tl) (fun _ out => out = a :: a :: tl) (fun _ => c) := by
  refine lift hK h (by simp) ?_ ?_
  · intro out hq
    obtain ⟨v, rest, hv, hout⟩ := hq
    cases hv
    exact hout
  · simpa using hc

theorem dropStep (hK : KernelLib) {p : Cmd} {K0 : ℕ}
    (h : WordR main p (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => K0 * (vsz (vs.headD .nil) + 1)))
    (a : Val) (tl : List Val) (c : ℕ) (hc : K0 * (vsz a + 1) ≤ c) :
    WordR main p (fun vs => vs = a :: tl) (fun _ out => out = tl) (fun _ => c) := by
  refine lift hK h (by simp) ?_ ?_
  · intro out hq
    obtain ⟨v, rest, hv, hout⟩ := hq
    cases hv
    exact hout
  · simpa using hc

theorem swapStep (hK : KernelLib) {p : Cmd} {K0 : ℕ}
    (h : WordR main p (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => K0 * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (a b : Val) (tl : List Val) (c : ℕ) (hc : K0 * (vsz a + vsz b + 1) ≤ c) :
    WordR main p (fun vs => vs = a :: b :: tl) (fun _ out => out = b :: a :: tl) (fun _ => c) := by
  refine lift hK h (by simp) ?_ ?_
  · intro out hq
    obtain ⟨a', b', rest, hv, hout⟩ := hq
    cases hv
    exact hout
  · simpa using hc

/-- The cost-relevant `sum` of the sizes of the top `j` values, written as a *recursive
function* peeling the head of the list, so that all statements about it are matched
*syntactically*: the kernel never has to reduce `List.take` / `List.map` / `List.sum` on a
concrete list (which used to make the kernel check of the `mapList` blocks blow up). -/
def vsh : ℕ → List Val → ℕ
  | 0, _ => 0
  | _ + 1, [] => 0
  | n + 1, a :: L => vsz a + vsh n L

@[simp] theorem vsh_zero (L : List Val) : vsh 0 L = 0 := rfl

@[simp] theorem vsh_nil : ∀ n : ℕ, vsh (n + 1) [] = 0 := fun _ => rfl

@[simp] theorem vsh_cons (n : ℕ) (a : Val) (L : List Val) :
    vsh (n + 1) (a :: L) = vsz a + vsh n L := rfl

/-- Bridge to the form used by the `KernelLib` cost functions. -/
theorem vsh_eq : ∀ (n : ℕ) (L : List Val), vsh n L = ((L.take n).map vsz).sum
  | 0, L => rfl
  | _ + 1, [] => by simp [vsh, List.take]
  | n + 1, a :: L => by
      rw [vsh_cons, vsh_eq n L, List.take, List.map_cons, List.sum_cons]

theorem pickStep (hK : KernelLib) {prog : ℕ → Cmd} {K0 : ℕ}
    (h : ∀ k : ℕ, WordR main (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => K0 * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (k : ℕ) (L : List Val) (hk : k < L.length) (c : ℕ)
    (hc : K0 * (k + 1) * (vsh (k + 1) L + 1) ≤ c) :
    WordR main (prog k) (fun vs => vs = L) (fun _ out => out = L.getD k .nil :: L) (fun _ => c) := by
  refine lift hK (h k) hk ?_ (show K0 * (k + 1) * (((L.take (k + 1)).map vsz).sum + 1) ≤ c from by
    rw [← vsh_eq]; exact hc)
  intro out hq
  exact hq

theorem rollStep (hK : KernelLib) {prog : ℕ → Cmd} {K0 : ℕ}
    (h : ∀ k : ℕ, WordR main (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K0 * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (k : ℕ) (L : List Val) (hk : k < L.length) (c : ℕ)
    (hc : K0 * (k + 1) * (vsh (k + 1) L + 1) ≤ c) :
    WordR main (prog k) (fun vs => vs = L) (fun _ out => out = L.getD k .nil :: L.eraseIdx k)
      (fun _ => c) := by
  refine lift hK (h k) hk ?_ (show K0 * (k + 1) * (((L.take (k + 1)).map vsz).sum + 1) ≤ c from by
    rw [← vsh_eq]; exact hc)
  intro out hq
  exact hq

theorem pushValStep (hK : KernelLib) {prog : Val → Cmd} {K0 : ℕ}
    (h : ∀ v : Val, WordR main (prog v) (fun _ => True) (fun vs out => out = v :: vs)
      (fun _ => K0 * (vsz v + 1)))
    (v : Val) (L : List Val) (c : ℕ) (hc : K0 * (vsz v + 1) ≤ c) :
    WordR main (prog v) (fun vs => vs = L) (fun _ out => out = v :: L) (fun _ => c) := by
  refine lift hK (h v) trivial ?_ hc
  intro out hq
  exact hq

theorem consVStep (hK : KernelLib) {p : Cmd} {K0 : ℕ}
    (h : WordR main p (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => K0))
    (a b : Val) (tl : List Val) (c : ℕ) (hc : K0 ≤ c) :
    WordR main p (fun vs => vs = a :: b :: tl) (fun _ out => out = .cons a b :: tl) (fun _ => c) := by
  refine lift hK h (by simp) ?_ hc
  intro out hq
  obtain ⟨a', b', rest, hv, hout⟩ := hq
  cases hv
  exact hout

theorem unconsVStep (hK : KernelLib) {p : Cmd} {K0 : ℕ}
    (h : WordR main p (fun vs => ∃ a b rest, vs = .cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest) (fun _ => K0))
    (a b : Val) (tl : List Val) (c : ℕ) (hc : K0 ≤ c) :
    WordR main p (fun vs => vs = .cons a b :: tl) (fun _ out => out = a :: b :: tl) (fun _ => c) := by
  refine lift hK h ⟨a, b, tl, rfl⟩ ?_ hc
  intro out hq
  obtain ⟨a', b', rest, hv, hout⟩ := hq
  cases hv
  exact hout

/-! ## Crude power bounds for costs -/

theorem pow_le_pow {B : ℕ} (hB : 0 < B) {m k : ℕ} (h : m ≤ k) : B ^ m ≤ B ^ k :=
  Nat.pow_le_pow_right hB h

theorem mul2_le_pow {B : ℕ} (hB : 0 < B) {a b : ℕ} (ha : a ≤ B) (hb : b ≤ B) {k : ℕ} (hk : 2 ≤ k) :
    a * b ≤ B ^ k :=
  le_trans (by
    calc a * b ≤ B * B := Nat.mul_le_mul ha hb
      _ = B ^ 2 := by ring) (pow_le_pow hB hk)

theorem mul3_le_pow {B : ℕ} (hB : 0 < B) {a b c : ℕ} (ha : a ≤ B) (hb : b ≤ B) (hc : c ≤ B)
    {k : ℕ} (hk : 3 ≤ k) : a * b * c ≤ B ^ k :=
  le_trans (by
    calc a * b * c ≤ B * B * B := Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc
      _ = B ^ 3 := by ring) (pow_le_pow hB hk)

theorem mul3sq_le_pow {B : ℕ} (hB : 0 < B) {a b c : ℕ} (ha : a ≤ B) (hb : b ≤ B) (hc : c ≤ B ^ 2)
    {k : ℕ} (hk : 4 ≤ k) : a * b * c ≤ B ^ k :=
  le_trans (by
    calc a * b * c ≤ B * B * (B ^ 2) := Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc
      _ = B ^ 4 := by ring) (pow_le_pow hB hk)

theorem le_pow_of_le {B : ℕ} (hB : 0 < B) {a : ℕ} (ha : a ≤ B) {k : ℕ} (hk : 1 ≤ k) :
    a ≤ B ^ k :=
  le_trans ha (Nat.le_self_pow (n := k) (by omega : k ≠ 0) B)


theorem mul_add_one_le_pow {B : ℕ} (hB : 2 ≤ B) {a b : ℕ} (ha : a ≤ B) (hb : b ≤ B) {k : ℕ}
    (hk : 3 ≤ k) : a * (b + 1) ≤ B ^ k :=
  le_trans (by
    calc a * (b + 1) ≤ B * (B + 1) := Nat.mul_le_mul ha (by omega)
      _ ≤ B * B * B := by nlinarith [hB]
      _ = B ^ 3 := by ring) (pow_le_pow (by omega) hk)

theorem mul_two_add_le_pow {B : ℕ} (hB : 3 ≤ B) {a b c : ℕ} (ha : a ≤ B) (hb : b ≤ B) (hc : c ≤ B)
    {k : ℕ} (hk : 3 ≤ k) : a * (b + c + 1) ≤ B ^ k :=
  le_trans (by
    calc a * (b + c + 1) ≤ B * (B + B + 1) := Nat.mul_le_mul ha (by omega)
      _ ≤ B * B * B := by nlinarith [hB]
      _ = B ^ 3 := by ring) (pow_le_pow (by omega) hk)

theorem mul_add_add_le_pow {B : ℕ} (hB : 2 ≤ B) {a b c : ℕ} (ha : a ≤ B) (hb : b ≤ B) (hc : c ≤ B)
    {k : ℕ} (hk : 3 ≤ k) : a * (b + c) ≤ B ^ k :=
  le_trans (by
    calc a * (b + c) ≤ B * (B + B) := Nat.mul_le_mul ha (by omega)
      _ ≤ B * B * B := by nlinarith [hB]
      _ = B ^ 3 := by ring) (pow_le_pow (by omega) hk)

theorem mul2sqq_le_pow {B : ℕ} (hB : 0 < B) {a b : ℕ} (ha : a ≤ B) (hb : b ≤ B ^ 2) {k : ℕ}
    (hk : 3 ≤ k) : a * b ≤ B ^ k :=
  le_trans (by
    calc a * b ≤ B * (B ^ 2) := Nat.mul_le_mul ha hb
      _ = B ^ 3 := by ring) (pow_le_pow hB hk)

theorem mul_sq_le_pow {B : ℕ} (hB : 0 < B) {a b : ℕ} (ha : a ≤ B) (hb : b ≤ B) {k : ℕ}
    (hk : 3 ≤ k) : a * b ^ 2 ≤ B ^ k :=
  le_trans (by
    calc a * b ^ 2 ≤ B * (B ^ 2) := Nat.mul_le_mul ha (by nlinarith [hb, hB])
      _ = B ^ 3 := by ring) (pow_le_pow hB hk)

/-!
## Exact-value wrappers: state the result value explicitly

`unStepP`/`binStepP` take the intended *result value* `X` and an equation proof, so that a long
straight-line program can be written with the mathematically meaningful values on the stack.

`ifZeroStep` turns the disjunctive post of `ifZero` into a single (conditional) state.
-/

theorem unStepP (hK : KernelLib) {p : Cmd} {f : ℤ → ℤ} {P : ℤ → Prop} {C : ℤ → ℕ}
    (h : UnOp main p P f C) (a : ℤ) (tl : List Val) (hPa : P a) (X : ℤ) (heq : f a = X)
    (c : ℕ) (hc : C a ≤ c) :
    WordR main p (fun vs => vs = .int a :: tl) (fun _ out => out = .int X :: tl) (fun _ => c) := by
  refine lift hK h ⟨a, tl, rfl, hPa⟩ ?_ hc
  intro out hq
  obtain ⟨a', rest, hv, hout⟩ := hq
  cases hv
  rw [hout, heq]

theorem binStepP (hK : KernelLib) {p : Cmd} {f : ℤ → ℤ → ℤ} {P : ℤ → ℤ → Prop} {C : ℤ → ℤ → ℕ}
    (h : BinOp main p P f C) (a b : ℤ) (tl : List Val) (hP : P a b) (X : ℤ) (heq : f a b = X)
    (c : ℕ) (hc : C a b ≤ c) :
    WordR main p (fun vs => vs = .int a :: .int b :: tl) (fun _ out => out = .int X :: tl) (fun _ => c) := by
  refine lift hK h ⟨a, b, tl, rfl, hP⟩ ?_ hc
  intro out hq
  obtain ⟨a', b', rest, hv, hout⟩ := hq
  cases hv
  rw [hout, heq]

theorem ifZeroStep (hK : KernelLib) {p : Cmd} {z : ℤ} {rest M₁ M₂ : List Val} {c : ℕ}
    (h : WordR main p (fun vs => vs = .int z :: rest)
      (fun _ out => (z = 0 → out = M₁) ∧ (z ≠ 0 → out = M₂)) (fun _ => c)) :
    WordR main p (fun vs => vs = .int z :: rest)
      (fun _ out => out = if z = 0 then M₁ else M₂) (fun _ => c) := by
  refine hK.conseq main p _ _ _ _ _ _ h (fun _ hh => hh) ?_ (fun _ _ => le_refl _)
  intro vs out _ hq
  by_cases hz : z = 0
  · rw [if_pos hz]; exact hq.1 hz
  · rw [if_neg hz]; exact hq.2 hz

/-! ## Cost bounds: every primitive step costs at most `SB` -/

theorem cost1 {W SB K a V : ℕ} (hW : 2 ≤ W) (hSB : W ^ 20 ≤ SB) (hK : K ≤ W) (ha : a ≤ V)
    (hV : V + 1 ≤ W) : K * (a + 1) ≤ SB := by
  have h1 : a + 1 ≤ W := by omega
  calc K * (a + 1) ≤ W * W := Nat.mul_le_mul hK h1
    _ = W ^ 2 := by ring
    _ ≤ W ^ 20 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ ≤ SB := hSB

theorem cost2 {W SB K a b V : ℕ} (hW : 2 ≤ W) (hSB : W ^ 20 ≤ SB) (hK : K ≤ W) (ha : a ≤ V)
    (hb : b ≤ V) (hV : V + 1 ≤ W) : K * (a + b + 1) ≤ SB := by
  have h1 : a + b + 1 ≤ 2 * W := by omega
  calc K * (a + b + 1) ≤ W * (2 * W) := Nat.mul_le_mul hK h1
    _ = 2 * W ^ 2 := by ring
    _ ≤ W * W ^ 2 := Nat.mul_le_mul_right _ hW
    _ = W ^ 3 := by ring
    _ ≤ W ^ 20 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ ≤ SB := hSB

theorem cost3 {W SB K k s : ℕ} (hW : 2 ≤ W) (hSB : W ^ 20 ≤ SB) (hK : K ≤ W) (hk : k + 1 ≤ W)
    (hs : s + 1 ≤ W ^ 3) : K * (k + 1) * (s + 1) ≤ SB := by
  calc K * (k + 1) * (s + 1) ≤ W * W * W ^ 3 :=
        Nat.mul_le_mul (Nat.mul_le_mul hK hk) hs
    _ = W ^ 5 := by ring
    _ ≤ W ^ 20 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ ≤ SB := hSB

theorem cost4 {W SB K a b : ℕ} (hW : 2 ≤ W) (hSB : W ^ 20 ≤ SB) (hK : K ≤ W) (ha : a ≤ W)
    (hb : b ≤ W) : K * a * b ≤ SB := by
  calc K * a * b ≤ W * W * W := Nat.mul_le_mul (Nat.mul_le_mul hK ha) hb
    _ = W ^ 3 := by ring
    _ ≤ W ^ 20 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ ≤ SB := hSB

theorem cost5 {W SB K a : ℕ} (hW : 2 ≤ W) (hSB : W ^ 20 ≤ SB) (hK : K ≤ W) (ha : a ≤ W) :
    K * a ^ 2 ≤ SB := by
  calc K * a ^ 2 ≤ W * W ^ 2 := Nat.mul_le_mul hK (Nat.pow_le_pow_left ha 2)
    _ = W ^ 3 := by ring
    _ ≤ W ^ 20 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ ≤ SB := hSB

theorem cost6 {W SB K a b : ℕ} (hW : 2 ≤ W) (hSB : W ^ 20 ≤ SB) (hK : K ≤ W) (ha : a ≤ W)
    (hb : b ≤ W) : K * (a + b) ≤ SB := by
  have h1 : a + b ≤ 2 * W := by omega
  calc K * (a + b) ≤ W * (2 * W) := Nat.mul_le_mul hK h1
    _ = 2 * W ^ 2 := by ring
    _ ≤ W * W ^ 2 := Nat.mul_le_mul_right _ hW
    _ = W ^ 3 := by ring
    _ ≤ W ^ 20 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ ≤ SB := hSB

theorem cost9 {W SB K a : ℕ} (hW : 2 ≤ W) (hSB : W ^ 20 ≤ SB) (hK : K ≤ W) (ha : a ≤ W) :
    K * a ≤ SB := by
  calc K * a ≤ W * W := Nat.mul_le_mul hK ha
    _ = W ^ 2 := by ring
    _ ≤ W ^ 20 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ ≤ SB := hSB

theorem cost7 {W SB K a M V : ℕ} (hW : 2 ≤ W) (hSB : W ^ 20 ≤ SB) (hK : K ≤ W) (ha : a ≤ V)
    (hV : V + 1 ≤ W) (hM : M ≤ W ^ 19) : K * (a + 1) + M ≤ SB := by
  have h1 : a + 1 ≤ W := by omega
  have h2 : K * (a + 1) ≤ W ^ 2 := by
    calc K * (a + 1) ≤ W * W := Nat.mul_le_mul hK h1
      _ = W ^ 2 := by ring
  have h4 : W ^ 2 ≤ W ^ 19 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h5 : 2 * W ^ 19 ≤ W ^ 20 := by
    calc 2 * W ^ 19 ≤ W * W ^ 19 := Nat.mul_le_mul_right _ hW
      _ = W ^ 20 := by ring
  calc K * (a + 1) + M ≤ W ^ 2 + W ^ 19 := Nat.add_le_add h2 hM
    _ ≤ W ^ 19 + W ^ 19 := Nat.add_le_add_right h4 _
    _ = 2 * W ^ 19 := by ring
    _ ≤ W ^ 20 := h5
    _ ≤ SB := hSB

theorem cost7c {W SB K a M V : ℕ} (hW : 2 ≤ W) (hSB : W ^ 34 ≤ SB) (hK : K ≤ W) (ha : a ≤ V)
    (hV : V + 1 ≤ W) (hM : M ≤ W ^ 32) : K * (a + 1) + M ≤ SB := by
  have h1 : a + 1 ≤ W := by omega
  have h2 : K * (a + 1) ≤ W ^ 2 := by
    calc K * (a + 1) ≤ W * W := Nat.mul_le_mul hK h1
      _ = W ^ 2 := by ring
  have h4 : 2 * W ^ 32 ≤ W ^ 33 := by
    calc 2 * W ^ 32 ≤ W * W ^ 32 := Nat.mul_le_mul_right _ hW
      _ = W ^ 33 := by ring
  have h5 : W ^ 33 ≤ W ^ 34 := Nat.pow_le_pow_right (by omega) (by norm_num)
  calc K * (a + 1) + M ≤ W ^ 2 + W ^ 32 := Nat.add_le_add h2 hM
    _ ≤ 2 * W ^ 32 := by
        have : W ^ 2 ≤ W ^ 32 := Nat.pow_le_pow_right (by omega) (by norm_num)
        omega
    _ ≤ W ^ 33 := h4
    _ ≤ W ^ 34 := h5
    _ ≤ SB := hSB

theorem cost8 {W SB D c K L : ℕ} (hW : 4 ≤ W) (hSB : W ^ 37 ≤ SB) (hD : D ≤ W) (hc : c ≤ W ^ 35)
    (hK : K ≤ W) (hL : L + 1 ≤ W) : D * (c + K * (L + 1)) + K ≤ SB := by
  have hmul : K * (L + 1) ≤ W * W := Nat.mul_le_mul hK hL
  have hsum : c + K * (L + 1) ≤ W ^ 35 + W * W := Nat.add_le_add hc hmul
  have hstep : D * (c + K * (L + 1)) + K ≤ W * (W ^ 35 + W * W) + W :=
    Nat.add_le_add (Nat.mul_le_mul hD hsum) hK
  have h1 : W * (W ^ 35 + W * W) = W ^ 36 + W ^ 3 := by ring
  have h31 : W ^ 3 + W ≤ W ^ 4 := by
    have h4 : W ≤ W ^ 3 := Nat.le_self_pow (by omega) W
    have h5 : 2 * W ^ 3 ≤ W ^ 4 := by
      calc 2 * W ^ 3 ≤ W * W ^ 3 := Nat.mul_le_mul_right _ (by omega : 2 ≤ W)
        _ = W ^ 4 := by ring
    omega
  have h7 : W ^ 36 + W ^ 3 + W ≤ W ^ 37 := by
    have h6 : W ^ 4 ≤ W ^ 36 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h8 : 2 * W ^ 36 ≤ W ^ 37 := by
      calc 2 * W ^ 36 ≤ W * W ^ 36 := Nat.mul_le_mul_right _ (by omega)
        _ = W ^ 37 := by ring
    omega
  rw [h1] at hstep
  calc D * (c + K * (L + 1)) + K ≤ W ^ 36 + W ^ 3 + W := hstep
    _ ≤ W ^ 37 := h7
    _ ≤ SB := hSB

/-- Bound for a `pick`/`roll` prefix sum: `k + 1 ≤ W`, each `vsz ≤ V ≤ W`. -/
theorem pick_sum_le {W V s j : ℕ} (hW : 4 ≤ W) (hV : V + 1 ≤ W) (hs : s ≤ j * V) (hj : j ≤ W) :
    s + 1 ≤ W ^ 3 := by
  have h1 : s ≤ W * W := by
    have h2 : V ≤ W := by omega
    calc s ≤ j * V := hs
      _ ≤ W * W := Nat.mul_le_mul hj h2
  have h3 : W * W + 1 ≤ W ^ 3 := by
    have h4 : W * W = W ^ 2 := by ring
    rw [h4]
    have h5 : 2 ≤ W ^ 2 := by nlinarith
    have h6 : W ^ 2 + 1 ≤ 2 * W ^ 2 := by omega
    have h7 : 2 * W ^ 2 ≤ W ^ 3 := by
      calc 2 * W ^ 2 ≤ W * W ^ 2 := Nat.mul_le_mul_right _ (by omega : 2 ≤ W)
        _ = W ^ 3 := by ring
    omega
  omega

/-- The cost of `c` branch steps plus the `ifZero` test. -/
theorem sum_branch {W S : ℕ} (hW : 100 ≤ W) (hS : S = 15 * W ^ 30) : S ≤ W ^ 32 := by
  rw [hS]
  calc 15 * W ^ 30 ≤ W * W ^ 30 := Nat.mul_le_mul_right _ (by omega)
    _ = W ^ 31 := by ring
    _ ≤ W ^ 32 := Nat.pow_le_pow_right (by omega) (by norm_num)

/-- The cost of the body chain: four primitive steps and the `ifZero` step. -/
theorem sum_body {W S : ℕ} (hW : 100 ≤ W) (hS : S = 4 * W ^ 30 + W ^ 34) : S ≤ W ^ 35 := by
  rw [hS]
  have h2 : 5 * W ^ 34 ≤ W ^ 35 := by
    calc 5 * W ^ 34 ≤ W * W ^ 34 := Nat.mul_le_mul_right _ (by omega)
      _ = W ^ 35 := by ring
  have h1 : W ^ 30 ≤ W ^ 34 := Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

/-- Rewrite the post-state of a step with an explicit equation. -/
theorem step_rw (hK : KernelLib) {p : Cmd} {L M M' : List Val} {c : ℕ}
    (h : WordR main p (fun vs => vs = L) (fun _ out => out = M) (fun _ => c)) (hM : M = M') :
    WordR main p (fun vs => vs = L) (fun _ out => out = M') (fun _ => c) := hM ▸ h

end Work.Params


/-- A branch chain of `n` primitive steps (each bounded by `W^30`) costs at most `W^32`. -/
theorem sum_branchN {W S n : ℕ} (hW : 100 ≤ W) (hn : n ≤ 20) (hS : S ≤ n * W ^ 30) : S ≤ W ^ 32 := by
  calc S ≤ n * W ^ 30 := hS
    _ ≤ 20 * W ^ 30 := Nat.mul_le_mul_right _ hn
    _ ≤ W * W ^ 30 := Nat.mul_le_mul_right _ (by omega)
    _ = W ^ 31 := by ring
    _ ≤ W ^ 32 := Nat.pow_le_pow_right (by omega) (by norm_num)
