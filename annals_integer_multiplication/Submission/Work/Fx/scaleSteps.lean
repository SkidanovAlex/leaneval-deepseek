import Mathlib
import Submission.Work.Fx.ScaleCommonImport

/-!
# Composable `Spec` steps for fixed-point programs

Adapters giving each library word as a `Spec` whose window is a *prefix* of the current window
(the rest of the window is carried along unchanged), with a constant cost bound.
-/

set_option autoImplicit false

namespace Work.Fx

open HvdH

/-- Generic "instantiate the top part `A`, lift with context `E`, constant cost" step. -/
theorem Spec.step2 (hk : KernelLib) {main prog : Cmd} {n : ℕ} {P : List Val → Prop}
    {Q : List Val → List Val → Prop} {C : List Val → ℕ} {A : List Val}
    (_hAn : A.length = n) (h : Spec main prog n P Q C) (hP : P A) {E : List Val} {Bc : ℕ}
    (hcost : C A ≤ Bc) {O : List Val} (hQ : ∀ o, Q A o → o = O) :
    Spec main prog (n + E.length) (fun t => t = A ++ E) (fun _ o => o = O ++ E)
      (fun _ => Bc) := by
  have h' : Spec main prog n (fun t => t = A) (fun _ o => o = O) (fun _ => Bc) := by
    refine Spec.mono hk h ?_ ?_ ?_
    · intro t _ ht; rw [ht]; exact hP
    · intro t o _ ht hQo; rw [ht] at hQo; exact hQ o hQo
    · intro t _ ht; rw [ht]; exact hcost
  exact Spec.extend_exact hk h' rfl

/-- A binary integer operation on the top two values of the window. -/
theorem Spec.binStep (hk : KernelLib) {main prog : Cmd} {P : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ}
    {C : ℤ → ℤ → ℕ} (h : BinOp main prog P f C) {a b : ℤ} (hab : P a b) {E : List Val} {Bc : ℕ}
    (hcost : C a b ≤ Bc) :
    Spec main prog (2 + E.length) (fun t => t = [.int a, .int b] ++ E)
      (fun _ o => o = [.int (f a b)] ++ E) (fun _ => Bc) := by
  refine Spec.step2 hk (A := [.int a, .int b]) (n := 2) (by simp) (Spec.binOp hk h)
    ⟨a, b, rfl, hab⟩ hcost ?_
  intro o ho
  rcases ho with ⟨a', b', he, ho'⟩
  obtain ⟨ha, hb, -⟩ := int_cons_inj3 he
  rw [ho', ← ha, ← hb]

/-- A unary integer operation on the top value of the window. -/
theorem Spec.unStep (hk : KernelLib) {main prog : Cmd} {P : ℤ → Prop} {f : ℤ → ℤ} {C : ℤ → ℕ}
    (h : UnOp main prog P f C) {a : ℤ} (ha : P a) {E : List Val} {Bc : ℕ} (hcost : C a ≤ Bc) :
    Spec main prog (1 + E.length) (fun t => t = [.int a] ++ E) (fun _ o => o = [.int (f a)] ++ E)
      (fun _ => Bc) := by
  refine Spec.step2 hk (A := [.int a]) (n := 1) (by simp) (Spec.unOp hk h)
    ⟨a, rfl, ha⟩ hcost ?_
  intro o ho
  rcases ho with ⟨a', he, ho'⟩
  have ha' : a' = a := (Val.int.inj (List.cons.inj he).1).symm
  rw [ho', ha']

/-- `pick` the `k`-th value of the window to the top. -/
theorem Spec.pickStep (hk : KernelLib) {main prog : Cmd} {K k : ℕ}
    (h : WordR main prog (fun vs => k < vs.length) (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A : List Val} (hA : A.length = k + 1) {E : List Val} {Bc : ℕ}
    (hcost : K * (k + 1) * (szl A + 1) ≤ Bc) :
    Spec main prog (k + 1 + E.length) (fun t => t = A ++ E)
      (fun _ o => o = (A.getD k .nil :: A) ++ E) (fun _ => Bc) := by
  refine Spec.step2 hk (A := A) (n := k + 1) hA (Spec.pickK hk h) trivial hcost ?_
  intro o ho; exact ho

/-- `roll` the `k`-th value of the window to the top. -/
theorem Spec.rollStep (hk : KernelLib) {main prog : Cmd} {K k : ℕ}
    (h : WordR main prog (fun vs => k < vs.length) (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A : List Val} (hA : A.length = k + 1) {E : List Val} {Bc : ℕ}
    (hcost : K * (k + 1) * (szl A + 1) ≤ Bc) :
    Spec main prog (k + 1 + E.length) (fun t => t = A ++ E)
      (fun _ o => o = (A.getD k .nil :: A.eraseIdx k) ++ E) (fun _ => Bc) := by
  refine Spec.step2 hk (A := A) (n := k + 1) hA (Spec.rollK hk h) trivial hcost ?_
  intro o ho; exact ho

/-- `dup` the top value of the window. -/
theorem Spec.dupStep (hk : KernelLib) {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1))) {a : Val} {E : List Val} {Bc : ℕ}
    (hcost : K * (vsz a + 1) ≤ Bc) :
    Spec main prog (1 + E.length) (fun t => t = [a] ++ E) (fun _ o => o = [a, a] ++ E)
      (fun _ => Bc) := by
  refine Spec.step2 hk (A := [a]) (n := 1) (by simp) (Spec.dupK hk h) trivial ?_ ?_
  · exact hcost
  · intro o ho
    rcases ho with ⟨v, hv, ho'⟩
    have hv' : v = a := (List.cons.inj hv).1.symm
    rw [ho', hv']

/-- `drop` the top value of the window. -/
theorem Spec.dropStep (hk : KernelLib) {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1))) {a : Val} {E : List Val} {Bc : ℕ}
    (hcost : K * (vsz a + 1) ≤ Bc) :
    Spec main prog (1 + E.length) (fun t => t = [a] ++ E) (fun _ o => o = E) (fun _ => Bc) := by
  refine Spec.step2 hk (A := [a]) (n := 1) (by simp) (Spec.dropK hk h) trivial ?_ (O := []) ?_
  · exact hcost
  · intro o ho; exact ho

/-- push a constant value. -/
theorem Spec.pushStep (hk : KernelLib) {main prog : Cmd} {K : ℕ} {v : Val}
    (h : WordR main prog (fun _ => True) (fun vs out => out = v :: vs) (fun _ => K * (vsz v + 1)))
    {E : List Val} {Bc : ℕ} (hcost : K * (vsz v + 1) ≤ Bc) :
    Spec main prog (0 + E.length) (fun t => t = E) (fun _ o => o = [v] ++ E) (fun _ => Bc) := by
  refine Spec.step2 hk (A := []) (n := 0) (by simp) (Spec.pushValK hk h) trivial ?_ (O := [v]) ?_
  · exact hcost
  · intro o ho; exact ho

/-- combine the top two values into a `cons`. -/
theorem Spec.consStep (hk : KernelLib) {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => K))
    {a b : Val} {E : List Val} {Bc : ℕ} (hcost : K ≤ Bc) :
    Spec main prog (2 + E.length) (fun t => t = [a, b] ++ E) (fun _ o => o = [.cons a b] ++ E)
      (fun _ => Bc) := by
  refine Spec.step2 hk (A := [a, b]) (n := 2) (by simp) (Spec.consVK hk h) trivial hcost ?_
  intro o ho
  rcases ho with ⟨a', b', he, ho'⟩
  obtain ⟨h1, h2, -⟩ := cons_inj3 he
  rw [ho', ← h1, ← h2]

/-- split a `cons` value into its two components. -/
theorem Spec.unconsStep (hk : KernelLib) {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => ∃ a b rest, vs = .cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest) (fun _ => K))
    {a b : Val} {E : List Val} {Bc : ℕ} (hcost : K ≤ Bc) :
    Spec main prog (1 + E.length) (fun t => t = [.cons a b] ++ E)
      (fun _ o => o = [a, b] ++ E) (fun _ => Bc) := by
  refine Spec.step2 hk (A := [.cons a b]) (n := 1) (by simp) (Spec.unconsVK hk h) ⟨a, b, rfl⟩ hcost ?_
  intro o ho
  rcases ho with ⟨a', b', he, ho'⟩
  obtain ⟨h1, h2, -⟩ := val_cons_inj3 he
  rw [ho', ← h1, ← h2]

/-- `swap` the top two values of the window. -/
theorem Spec.swapStep (hk : KernelLib) {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    {a b : Val} {E : List Val} {Bc : ℕ} (hcost : K * (vsz a + vsz b + 1) ≤ Bc) :
    Spec main prog (2 + E.length) (fun t => t = [a, b] ++ E) (fun _ o => o = [b, a] ++ E)
      (fun _ => Bc) := by
  refine Spec.step2 hk (A := [a, b]) (n := 2) (by simp) (Spec.swapK hk h) trivial ?_ ?_
  · simpa using hcost
  · intro o ho
    rcases ho with ⟨a', b', he, ho'⟩
    obtain ⟨h1, h2, -⟩ := cons_inj3 he
    rw [ho', ← h1, ← h2]

/-- Sequential composition of two constant-cost deterministic window steps. -/
theorem Spec.seq_det_quad (hk : KernelLib) {main p q : Cmd} {n m : ℕ} {A B D : List Val} {c1 c2 : ℕ}
    (h1 : Spec main p n (fun t => t = A) (fun _ o => o = B) (fun _ => c1))
    (h2 : Spec main q m (fun t => t = B) (fun _ o => o = D) (fun _ => c2)) (hB : B.length = m) :
    Spec main (.seq p q) n (fun t => t = A) (fun _ o => o = D) (fun _ => c1 + c2) :=
  Spec.seq_det hk h1 h2 hB

end Work.Fx
