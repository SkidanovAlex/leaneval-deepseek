import Submission.Work.Fx.FxMath

/-!
# Exact-window adapters with linear cost
-/

set_option autoImplicit false

namespace Work.Fx

open HvdH

/-- Extend an exact-window `Spec` with a carried block, keeping the (linear) cost. -/
theorem Spec.extendLin (hk : KernelLib) {main p : Cmd} {n k : ℕ} {A B : List Val} {K : ℕ}
    (h : Spec main p n (fun t => t = A) (fun _ o => o = B) (linCost K)) {E : List Val}
    (hE : E.length = k) :
    Spec main p (n + k) (fun t => t = A ++ E) (fun _ o => o = B ++ E) (linCost K) := by
  refine Spec.mono hk (Spec.extend_exact hk h hE) (fun t _ h => h) (fun t o _ _ h => h) ?_
  intro t _ hAt
  rw [hAt]
  show K * (szl A + 1) ≤ K * (szl (A ++ E) + 1)
  rw [szl_append]
  exact Nat.mul_le_mul_left K (by omega)

/-- Exact-window, linear-cost form of a `BinOp`. -/
theorem Spec.binOpEx (hk : KernelLib) {main p : Cmd} {P : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ}
    {C : ℤ → ℤ → ℕ} (h : BinOp main p P f C) {A0 B0 : ℤ} (hP : P A0 B0) {KK : ℕ}
    (hC : C A0 B0 ≤ KK) :
    Spec main p 2 (fun t => t = [.int A0, .int B0]) (fun _ o => o = [.int (f A0 B0)])
      (linCost KK) := by
  refine Spec.mono hk (Spec.binOp hk h) ?_ ?_ ?_
  · intro t ht hq
    rw [hq]
    exact ⟨A0, B0, rfl, hP⟩
  · intro t o ht hq hQ
    rcases hQ with ⟨a, b, hab, ho⟩
    have e1 : ([.int a, .int b] : List Val) = [.int A0, .int B0] := Eq.trans (Eq.symm hab) hq
    have e2 := List.cons.inj e1
    have e3 := List.cons.inj e2.2
    rw [ho, Val.int.inj e2.1, Val.int.inj e3.1]
  · intro t ht hq
    rw [hq]
    have hone : 1 ≤ szl [.int A0, .int B0] + 1 := by
      simp only [szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int]
      omega
    show C A0 B0 ≤ KK * (szl [.int A0, .int B0] + 1)
    calc C A0 B0 ≤ KK := hC
      _ = KK * 1 := (Nat.mul_one KK).symm
      _ ≤ KK * (szl [.int A0, .int B0] + 1) := Nat.mul_le_mul_left KK hone

/-- Exact-window, linear-cost form of a `UnOp`. -/
theorem Spec.unOpEx (hk : KernelLib) {main p : Cmd} {P : ℤ → Prop} {f : ℤ → ℤ} {C : ℤ → ℕ}
    (h : UnOp main p P f C) {A0 : ℤ} (hP : P A0) {KK : ℕ} (hC : C A0 ≤ KK) :
    Spec main p 1 (fun t => t = [.int A0]) (fun _ o => o = [.int (f A0)]) (linCost KK) := by
  refine Spec.mono hk (Spec.unOp hk h) ?_ ?_ ?_
  · intro t ht hq
    rw [hq]
    exact ⟨A0, rfl, hP⟩
  · intro t o ht hq hQ
    rcases hQ with ⟨a, ha, ho⟩
    have e1 : ([.int a] : List Val) = [.int A0] := Eq.trans (Eq.symm ha) hq
    rw [ho, Val.int.inj (List.cons.inj e1).1]
  · intro t ht hq
    rw [hq]
    have hone : 1 ≤ szl [.int A0] + 1 := by
      simp only [szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int]
      omega
    show C A0 ≤ KK * (szl [.int A0] + 1)
    calc C A0 ≤ KK := hC
      _ = KK * 1 := (Nat.mul_one KK).symm
      _ ≤ KK * (szl [.int A0] + 1) := Nat.mul_le_mul_left KK hone

/-- `unconsV` on a fixed window `[Val.cons A B]`. -/
theorem Spec.unconsVEx (hk : KernelLib) {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => ∃ a b rest, vs = .cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest) (fun _ => K))
    (A B : Val) :
    Spec main prog 1 (fun t => t = [.cons A B]) (fun _ o => o = [A, B]) (linCost K) := by
  refine Spec.mono hk (Spec.unconsVK hk h) ?_ ?_ ?_
  · intro t ht hq
    rw [hq]
    exact ⟨A, B, rfl⟩
  · intro t o ht hq hQ
    rcases hQ with ⟨a, b, hab, ho⟩
    have e1 : ([.cons a b] : List Val) = [.cons A B] := Eq.trans (Eq.symm hab) hq
    have e2 := Val.cons.inj (List.cons.inj e1).1
    rw [ho, e2.1, e2.2]
  · intro t ht hq
    rw [hq]
    show K ≤ K * (szl [.cons A B] + 1)
    calc K = K * 1 := (Nat.mul_one K).symm
      _ ≤ K * (szl [.cons A B] + 1) := Nat.mul_le_mul_left K (by simp)

/-- `consV` on a fixed window `[A, B]`. -/
theorem Spec.consVEx (hk : KernelLib) {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest)
      (fun _ => K)) (A B : Val) :
    Spec main prog 2 (fun t => t = [A, B]) (fun _ o => o = [.cons A B]) (linCost K) := by
  refine Spec.mono hk (Spec.consVK hk h) (fun t _ _ => trivial) ?_ ?_
  · intro t o ht hq hQ
    rcases hQ with ⟨a, b, hab, ho⟩
    have e1 : ([a, b] : List Val) = [A, B] := Eq.trans (Eq.symm hab) hq
    have e2 := List.cons.inj e1
    have e3 := List.cons.inj e2.2
    rw [ho, e2.1, e3.1]
  · intro t ht hq
    rw [hq]
    show K ≤ K * (szl [A, B] + 1)
    calc K = K * 1 := (Nat.mul_one K).symm
      _ ≤ K * (szl [A, B] + 1) := Nat.mul_le_mul_left K (by simp)

/-- `swap` on a fixed window `[A, B]`. -/
theorem Spec.swapEx (hk : KernelLib) {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1))) (A B : Val) :
    Spec main prog 2 (fun t => t = [A, B]) (fun _ o => o = [B, A]) (linCost (3 * K)) := by
  refine Spec.mono hk (Spec.swapK hk h) (fun t _ _ => trivial) ?_ ?_
  · intro t o ht hq hQ
    rcases hQ with ⟨a, b, hab, ho⟩
    have e1 : ([a, b] : List Val) = [A, B] := Eq.trans (Eq.symm hab) hq
    have e2 := List.cons.inj e1
    have e3 := List.cons.inj e2.2
    rw [ho, e2.1, e3.1]
  · intro t ht hq
    rw [hq]
    have h1 : vsz A ≤ szl [A, B] := le_szl (by simp)
    have h2 : vsz B ≤ szl [A, B] := le_szl (by simp)
    show K * (vsz A + vsz B + 1) ≤ 3 * K * (szl [A, B] + 1)
    nlinarith

/-- `pushVal` of a constant. -/
theorem Spec.pushValEx (hk : KernelLib) {main prog : Cmd} {K : ℕ} {v : Val}
    (h : WordR main prog (fun _ => True) (fun vs out => out = v :: vs) (fun _ => K * (vsz v + 1))) :
    Spec main prog 0 (fun _ => True) (fun _ o => o = [v]) (linCost (K * (vsz v + 1))) := by
  refine Spec.mono hk (Spec.pushValK hk h) (fun t _ _ => trivial) (fun t o ht hq hQ => hQ) ?_
  intro t ht hq
  cases t with
  | nil => simp [linCost]
  | cons a l => simp at ht

/-- `pushVal` of a constant, in exact-window form (empty window). -/
theorem Spec.pushValEx' (hk : KernelLib) {main prog : Cmd} {K : ℕ} {v : Val}
    (h : WordR main prog (fun _ => True) (fun vs out => out = v :: vs) (fun _ => K * (vsz v + 1))) :
    Spec main prog 0 (fun t => t = ([] : List Val)) (fun _ o => o = [v])
      (linCost (K * (vsz v + 1))) :=
  Spec.mono hk (Spec.pushValEx hk h) (fun t _ _ => trivial) (fun t o ht hq hQ => hQ)
    (fun t _ _ => le_rfl)

/-- `roll k` on a fixed window of length `k+1`. -/
theorem Spec.rollEx (hk : KernelLib) {main prog : Cmd} {K k : ℕ}
    (h : WordR main prog (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {W B : List Val} (hW : W.length = k + 1) (hB : B = W.getD k .nil :: W.eraseIdx k) :
    Spec main prog (k + 1) (fun t => t = W) (fun _ o => o = B) (linCost (K * (k + 1))) := by
  refine Spec.mono hk (Spec.rollK hk h) (fun t _ _ => trivial) ?_ ?_
  · intro t o ht htW hQ
    rw [hQ, htW]
    exact hB.symm
  · intro t _ _
    rfl

theorem Nat.size_two : (2 : ℕ).size = 2 := by
  have h1 : (2 : ℕ).size ≤ 2 := Nat.size_le.mpr (by norm_num)
  have h2 : ¬ (2 : ℕ).size ≤ 1 := by
    intro h
    exact absurd (Nat.size_le.mp h) (by norm_num)
  omega

theorem isz_two : isz (2 : ℤ) = 4 := by
  have h : (2 : ℤ).natAbs = 2 := rfl
  simp only [isz, h, Nat.size_two]

/-- `szl` of an integer pair followed by a carried block. -/
theorem szl_int_pair_append (A0 B0 : ℤ) (E : List Val) :
    szl ([.int A0, .int B0] ++ E) = isz A0 + isz B0 + szl E := by
  simp only [List.cons_append, List.nil_append, szl_cons, szl_nil, vsz_int]
  omega

theorem linCost_int_pair (K : ℕ) (A0 B0 : ℤ) (E : List Val) :
    linCost K ([.int A0, .int B0] ++ E) = K * (isz A0 + isz B0 + szl E + 1) := by
  rw [linCost, szl_int_pair_append]

end Work.Fx
