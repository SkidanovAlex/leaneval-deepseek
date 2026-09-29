import Mathlib
import Submission.Work.Fx.ExpDefs

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace Work.Fx
open HvdH

/-!
# `Work.Fx.expStepA`

One step of the fixed-point Horner loop for the complex exponential: from the window

`[1, Qre, Qim, dd, Zs, Zt, Pow, d0]`

compute `Nre = Zs*Qre - Zt*Qim` and `Nim = Zs*Qim + Zt*Qre` (the two coordinates of
`(Zs + i Zt) * (Qre + i Qim)`) and leave

`[Nre, Nim, dd, Zs, Zt, Pow, d0]`.

Only `IntLib`'s `mulS`, `add`, `sub` and `KernelLib`'s `pick`, `roll`, `drop` are used, so the
program needs no `self`; it composes 16 elementary steps and its total cost is linear in the size
of the window.

The proof uses a small local toolkit: a window is described as `ints L` for a list `L` of integer
*terms*, and each elementary step is a `WordR` word transforming `ints L ++ rest` into
`ints L' ++ rest`.
-/

/-! ## Windows over lists of integer terms -/

/-- The value window attached to a list of integer terms. -/
def ints (l : List ℤ) : List Val := l.map Val.int

theorem ints_cons (a : ℤ) (l : List ℤ) : ints (a :: l) = Val.int a :: ints l := rfl

theorem length_ints (l : List ℤ) : (ints l).length = l.length := by
  simp only [ints, List.length_map]

theorem getD_ints : ∀ (l : List ℤ) (k : ℕ), k < l.length →
    (ints l).getD k Val.nil = Val.int (l.getD k 0)
  | [], k, hk => by simp at hk
  | a :: t, 0, _ => rfl
  | a :: t, k + 1, hk => by
      rw [ints_cons, List.getD_cons_succ, List.getD_cons_succ]
      exact getD_ints t k (by simpa using hk)

theorem eraseIdx_ints : ∀ (l : List ℤ) (k : ℕ), (ints l).eraseIdx k = ints (l.eraseIdx k)
  | [], k => by cases k <;> rfl
  | a :: t, 0 => rfl
  | a :: t, k + 1 => by
      rw [ints_cons, List.eraseIdx_cons_succ, eraseIdx_ints t k, List.eraseIdx_cons_succ, ints_cons]

theorem vsz_ints {l : List ℤ} {M : ℕ} (h : ∀ z ∈ l, isz z ≤ M) :
    ∀ v ∈ ints l, vsz v ≤ M := by
  intro v hv
  rw [ints, List.mem_map] at hv
  obtain ⟨z, hz, rfl⟩ := hv
  rw [vsz_int]
  exact h z hz

theorem sum_take_vsz_le {M : ℕ} {A : List Val} (h : ∀ v ∈ A, vsz v ≤ M) (k : ℕ) :
    ((A.take (k + 1)).map vsz).sum ≤ (k + 1) * M := by
  have h1 : ((A.take (k + 1)).map vsz).sum ≤ ((A.take (k + 1)).map (fun _ => M)).sum :=
    List.sum_le_sum fun v hv => h v (List.mem_of_mem_take hv)
  have h2 : ∀ (L : List Val), ((L.map fun _ => M).sum) = L.length * M := by
    intro L
    induction L with
    | nil => simp
    | cons a t ih => simp [Nat.succ_mul, Nat.add_comm]
  rw [h2] at h1
  have h3 : (A.take (k + 1)).length ≤ k + 1 := by rw [List.length_take]; exact Nat.min_le_left _ _
  calc ((A.take (k + 1)).map vsz).sum ≤ (A.take (k + 1)).length * M := h1
    _ ≤ (k + 1) * M := Nat.mul_le_mul_right _ h3

/-! ## `WordR` adapters -/

/-- Exact-window consequence rule. -/
theorem wrd_exact {main p : Cmd} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {C : List Val → ℕ} {A B : List Val} {c : ℕ}
    (h : WordR main p P Q C) (hA : P A) (hB : ∀ out, Q A out → out = B) (hc : C A ≤ c) :
    WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c) := by
  intro vs hvs s R hs
  subst vs
  obtain ⟨out, s', n, hPost, hev, hn, hstk, hfr⟩ := h A hA s R hs
  exact ⟨out, s', n, hB out hPost, hev, le_trans hn hc, hstk, hfr⟩

/-- Sequential composition of two exact-window words. -/
theorem wrd_seq2_x1 {main p q : Cmd} {A mid B : List Val} {c1 c2 : ℕ}
    (hp : WordR main p (fun vs => vs = A) (fun _ out => out = mid) (fun _ => c1))
    (hq : WordR main q (fun vs => vs = mid) (fun _ out => out = B) (fun _ => c2)) :
    WordR main (p.seq q) (fun vs => vs = A) (fun _ out => out = B) (fun _ => c1 + c2) := by
  intro vs hvs s R hs
  subst vs
  obtain ⟨m, s1, n1, hm, hev1, hn1, hstk1, hfr1⟩ := hp A rfl s R hs
  obtain ⟨out, s2, n2, hB, hev2, hn2, hstk2, hfr2⟩ := hq m hm s1 R hstk1
  have hn1' : n1 ≤ c1 := hn1
  have hn2' : n2 ≤ c2 := hn2
  refine ⟨out, s2, n1 + n2, hB, Eval.seq hev1 hev2, ?_, hstk2, fun k hk => ?_⟩
  · show n1 + n2 ≤ c1 + c2
    omega
  · rw [hfr2 k hk, hfr1 k hk]

/-- Sequential composition of two exact-window words, with the total cost named `z`. -/
theorem wrd_seq2z (hk : KernelLib) {main p q : Cmd} {A mid B : List Val} {c1 c2 z : ℕ}
    (hp : WordR main p (fun vs => vs = A) (fun _ out => out = mid) (fun _ => c1))
    (hq : WordR main q (fun vs => vs = mid) (fun _ out => out = B) (fun _ => c2))
    (hz : c1 + c2 = z) :
    WordR main (p.seq q) (fun vs => vs = A) (fun _ out => out = B) (fun _ => z) := by
  refine hk.conseq (main := main) (p := p.seq q) (P := fun vs => vs = A)
    (P' := fun vs => vs = A) (Q := fun _ out => out = B) (Q' := fun _ out => out = B)
    (C := fun _ => c1 + c2) (C' := fun _ => z) (wrd_seq2_x1 hp hq)
    (fun vs h => h) (fun vs out _ hq => hq) ?_
  intro vs _
  first | (simp only []; exact hz.le) | exact hz.le

/-- `pick k` on an integer window. -/
theorem wrd_pickI {main : Cmd} {prog : ℕ → Cmd} {K : ℕ}
    (h : ∀ k, WordR main (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (k : ℕ) (L L' : List ℤ) (rest : List Val) (hL' : L.getD k 0 :: L = L') (hk : k < L.length)
    {c : ℕ} (hc : K * (k + 1) * ((((ints L).take (k + 1)).map vsz).sum + 1) ≤ c) :
    WordR main (prog k) (fun vs => vs = ints L ++ rest)
      (fun _ out => out = ints L' ++ rest) (fun _ => c) := by
  have hkl : k < (ints L).length := by rwa [length_ints]
  have hk' : k < (ints L ++ rest).length := by
    rw [List.length_append]; omega
  have h' : WordR main (prog k) (fun vs => vs = ints L ++ rest)
      (fun _ out => out = .int (L.getD k 0) :: (ints L ++ rest)) (fun _ => c) := by
    refine wrd_exact (h k) hk' ?_ ?_
    · intro out hout
      rw [hout, List.getD_append (ints L) rest .nil k hkl, getD_ints L k hk]
    · have htake : (ints L ++ rest).take (k + 1) = (ints L).take (k + 1) := by
        apply List.take_append_of_le_length
        rw [length_ints]; omega
      simpa [htake] using hc
  refine wrd_exact h' ?_ ?_ (le_refl c)
  · rfl
  · intro out hout
    rw [hout, ← hL', ints_cons] <;> rfl

/-- `roll k` on an integer window. -/
theorem wrd_rollI {main : Cmd} {prog : ℕ → Cmd} {K : ℕ}
    (h : ∀ k, WordR main (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (k : ℕ) (L L' : List ℤ) (rest : List Val) (hL' : L.getD k 0 :: L.eraseIdx k = L')
    (hk : k < L.length) {c : ℕ}
    (hc : K * (k + 1) * ((((ints L).take (k + 1)).map vsz).sum + 1) ≤ c) :
    WordR main (prog k) (fun vs => vs = ints L ++ rest)
      (fun _ out => out = ints L' ++ rest) (fun _ => c) := by
  have hkl : k < (ints L).length := by rwa [length_ints]
  have hk' : k < (ints L ++ rest).length := by
    rw [List.length_append]; omega
  have h' : WordR main (prog k) (fun vs => vs = ints L ++ rest)
      (fun _ out => out = .int (L.getD k 0) :: ints (L.eraseIdx k) ++ rest) (fun _ => c) := by
    refine wrd_exact (h k) hk' ?_ ?_
    · intro out hout
      rw [hout, getD_eraseIdx_append hkl, getD_ints L k hk, eraseIdx_ints]
    · have htake : (ints L ++ rest).take (k + 1) = (ints L).take (k + 1) := by
        apply List.take_append_of_le_length
        rw [length_ints]; omega
      simpa [htake] using hc
  refine wrd_exact h' ?_ ?_ (le_refl c)
  · rfl
  · intro out hout
    rw [hout, ← hL', ints_cons] <;> rfl

/-- A binary integer operation on the two top values of an integer window. -/
theorem wrd_binOpI {main prog : Cmd} {P : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ} {C : ℤ → ℤ → ℕ}
    (h : BinOp main prog P f C) (a b : ℤ) (l L L' : List ℤ) (rest : List Val)
    (hL : L = a :: b :: l) (hL' : f a b :: l = L') (hP : P a b) {c : ℕ} (hc : C a b ≤ c) :
    WordR main prog (fun vs => vs = ints L ++ rest)
      (fun _ out => out = ints L' ++ rest) (fun _ => c) := by
  have h' : WordR main prog (fun vs => vs = .int a :: .int b :: (ints l ++ rest))
      (fun _ out => out = .int (f a b) :: (ints l ++ rest)) (fun _ => c) := by
    refine wrd_exact h ⟨a, b, ints l ++ rest, rfl, hP⟩ ?_ ?_
    · intro out hQ
      rcases hQ with ⟨a', b', rest', hvs, hout⟩
      obtain ⟨h1, h2⟩ := List.cons.inj hvs
      obtain ⟨ha, hr⟩ := List.cons.inj h2
      rw [hout, ← Val.int.inj h1, ← Val.int.inj ha, ← hr]
    · simpa only [binCost] using hc
  refine wrd_exact h' ?_ ?_ (le_refl c)
  · rw [hL]; rfl
  · intro out hout
    rw [hout, ← hL', ints_cons] <;> rfl

/-- `drop` on an integer window. -/
theorem wrd_dropI {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v r, vs = v :: r ∧ out = r)
      (fun vs => K * (vsz (vs.headD .nil) + 1)))
    (a : ℤ) (l L L' : List ℤ) (rest : List Val) (hL : L = a :: l) (hL' : l = L')
    {c : ℕ} (hc : K * (isz a + 1) ≤ c) :
    WordR main prog (fun vs => vs = ints L ++ rest)
      (fun _ out => out = ints L' ++ rest) (fun _ => c) := by
  have h' : WordR main prog (fun vs => vs = .int a :: (ints l ++ rest))
      (fun _ out => out = ints l ++ rest) (fun _ => c) := by
    refine wrd_exact h (List.cons_ne_nil _ _) ?_ ?_
    · intro out hQ
      rcases hQ with ⟨v, r, hvs, hout⟩
      obtain ⟨h1, h2⟩ := List.cons.inj hvs
      rw [hout, ← h2]
    · have hh : (Val.int a :: (ints l ++ rest)).headD .nil = Val.int a := rfl
      rw [hh, vsz_int]
      exact hc
  refine wrd_exact h' ?_ ?_ (le_refl c)
  · rw [hL]; rfl
  · intro out hout
    rw [hout, hL']

/-! ## Cost bounds -/

/-- Cost of a `pick`/`roll` step. -/
theorem cost_pickroll_x1 {K KK S k m : ℕ} (hK : K ≤ KK) (hk : k + 1 ≤ 12) (hm : m ≤ 36 * S)
    (hS : 1 ≤ S) : K * (k + 1) * (m + 1) ≤ 1000 * KK * S ^ 2 := by
  have hm' : m + 1 ≤ 37 * S := by omega
  have h1 : K * (k + 1) * (m + 1) ≤ KK * 12 * (37 * S) :=
    Nat.mul_le_mul (Nat.mul_le_mul hK hk) hm'
  have h2 : KK * 12 * (37 * S) = (444 * KK) * S := by ring
  rw [h2] at h1
  refine le_trans h1 ?_
  calc (444 * KK) * S ≤ (1000 * KK) * S := Nat.mul_le_mul_right S (by omega)
    _ ≤ (1000 * KK) * S ^ 2 := by
        apply Nat.mul_le_mul_left
        calc S = S * 1 := (Nat.mul_one S).symm
          _ ≤ S * S := Nat.mul_le_mul_left S hS
          _ = S ^ 2 := by ring

/-- Cost of a multiplication step; the two factors have size at most `S`. -/
theorem cost_mul_x1 {K KK S a b : ℕ} (hK : K ≤ KK) (ha : a ≤ S) (hb : b ≤ S) (hS : 1 ≤ S) :
    K * a * b ≤ 1000 * KK * S ^ 2 := by
  have h1 : K * a * b ≤ KK * S * S := Nat.mul_le_mul (Nat.mul_le_mul hK ha) hb
  have h2 : KK * S * S = KK * S ^ 2 := by ring
  rw [h2] at h1
  exact le_trans h1 (Nat.mul_le_mul_right _ (by omega))

/-- Cost of an addition/subtraction step; the two summands have size at most `2*S`. -/
theorem cost_addsub {K KK S a b : ℕ} (hK : K ≤ KK) (ha : a ≤ 2 * S) (hb : b ≤ 2 * S)
    (hS : 1 ≤ S) : K * (a + b) ≤ 1000 * KK * S ^ 2 := by
  have h1 : K * (a + b) ≤ KK * (4 * S) := Nat.mul_le_mul hK (by omega)
  have h2 : KK * (4 * S) = (4 * KK) * S := by ring
  rw [h2] at h1
  refine le_trans h1 ?_
  calc (4 * KK) * S ≤ (1000 * KK) * S := Nat.mul_le_mul_right S (by omega)
    _ ≤ (1000 * KK) * S ^ 2 := by
        apply Nat.mul_le_mul_left
        calc S = S * 1 := (Nat.mul_one S).symm
          _ ≤ S * S := Nat.mul_le_mul_left S hS
          _ = S ^ 2 := by ring

/-- Cost of a `drop` step; the dropped value has size at most `S`. -/
theorem cost_drop_x1 {K KK S a : ℕ} (hK : K ≤ KK) (ha : a ≤ S) (hS : 1 ≤ S) :
    K * (a + 1) ≤ 1000 * KK * S ^ 2 := by
  have h1 : K * (a + 1) ≤ KK * (2 * S) := Nat.mul_le_mul hK (by omega)
  have h2 : KK * (2 * S) = (2 * KK) * S := by ring
  rw [h2] at h1
  refine le_trans h1 ?_
  calc (2 * KK) * S ≤ (1000 * KK) * S := Nat.mul_le_mul_right S (by omega)
    _ ≤ (1000 * KK) * S ^ 2 := by
        apply Nat.mul_le_mul_left
        calc S = S * 1 := (Nat.mul_one S).symm
          _ ≤ S * S := Nat.mul_le_mul_left S hS
          _ = S ^ 2 := by ring

/-- The size of the first `k+1` values of a window whose terms all have `isz ≤ 3*S`. -/
theorem pickroll_sum_le {S : ℕ} {L : List ℤ} (h : ∀ z ∈ L, isz z ≤ 3 * S) {k : ℕ}
    (hk : k + 1 ≤ 12) : (((ints L).take (k + 1)).map vsz).sum ≤ 36 * S := by
  have h1 : ∀ v ∈ ints L, vsz v ≤ 3 * S := vsz_ints h
  have h2 := sum_take_vsz_le h1 k
  have hk' : (k + 1) * 3 ≤ 36 := by omega
  calc (((ints L).take (k + 1)).map vsz).sum ≤ (k + 1) * (3 * S) := h2
    _ = ((k + 1) * 3) * S := by ring
    _ ≤ 36 * S := Nat.mul_le_mul_right S hk'

/-! ## The program -/

/-- The 16 elementary steps of the `expStepA` word. -/
def expStepProg (mulP addP subP dropP : Cmd) (pickP rollP : ℕ → Cmd) : Cmd :=
  List.foldr Cmd.seq dropP
    [pickP 1, pickP 6, mulP, pickP 3, pickP 6, mulP, addP, rollP 3, pickP 6, mulP, rollP 3,
     pickP 5, mulP, subP, rollP 2]

theorem expStepA (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (Qre Qim dd Zs Zt Pow d0 : ℤ),
      Spec main prog 8
        (fun t => t = [HvdH.Val.int 1, HvdH.Val.int Qre, HvdH.Val.int Qim, HvdH.Val.int dd,
          HvdH.Val.int Zs, HvdH.Val.int Zt, HvdH.Val.int Pow, HvdH.Val.int d0])
        (fun t o => o = [HvdH.Val.int (Zs * Qre - Zt * Qim), HvdH.Val.int (Zs * Qim + Zt * Qre),
          HvdH.Val.int dd, HvdH.Val.int Zs, HvdH.Val.int Zt, HvdH.Val.int Pow, HvdH.Val.int d0])
        (fun t => K * (szl t + 1) ^ K) := by
  obtain ⟨mulP, Kmul, hmul⟩ := hi.mulS
  obtain ⟨addP, Kadd, hadd⟩ := hi.add
  obtain ⟨subP, Ksub, hsub⟩ := hi.sub
  obtain ⟨pickP, Kp, hpick⟩ := hk.pick
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨dropP, Kd, hdrop⟩ := hk.drop
  let KK : ℕ := Kp + Kr + Kd + Kmul + Ksub + Kadd + 1
  refine ⟨expStepProg mulP addP subP dropP pickP rollP, 16000 * KK + 2, ?_⟩
  intro main Qre Qim dd Zs Zt Pow d0
  -- the integer terms of the computation
  let p1 : ℤ := Zs * Qre
  let p2 : ℤ := Zt * Qim
  let p3 : ℤ := Zs * Qim
  let p4 : ℤ := Zt * Qre
  let Nim : ℤ := p3 + p4
  let Nre : ℤ := p1 - p2
  -- the windows
  let l0 : List ℤ := [1, Qre, Qim, dd, Zs, Zt, Pow, d0]
  let l1 : List ℤ := [Qre, 1, Qre, Qim, dd, Zs, Zt, Pow, d0]
  let l2 : List ℤ := [Zt, Qre, 1, Qre, Qim, dd, Zs, Zt, Pow, d0]
  let l3 : List ℤ := [p4, 1, Qre, Qim, dd, Zs, Zt, Pow, d0]
  let l4 : List ℤ := [Qim, p4, 1, Qre, Qim, dd, Zs, Zt, Pow, d0]
  let l5 : List ℤ := [Zs, Qim, p4, 1, Qre, Qim, dd, Zs, Zt, Pow, d0]
  let l6 : List ℤ := [p3, p4, 1, Qre, Qim, dd, Zs, Zt, Pow, d0]
  let l7 : List ℤ := [Nim, 1, Qre, Qim, dd, Zs, Zt, Pow, d0]
  let l8 : List ℤ := [Qim, Nim, 1, Qre, dd, Zs, Zt, Pow, d0]
  let l9 : List ℤ := [Zt, Qim, Nim, 1, Qre, dd, Zs, Zt, Pow, d0]
  let l10 : List ℤ := [p2, Nim, 1, Qre, dd, Zs, Zt, Pow, d0]
  let l11 : List ℤ := [Qre, p2, Nim, 1, dd, Zs, Zt, Pow, d0]
  let l12 : List ℤ := [Zs, Qre, p2, Nim, 1, dd, Zs, Zt, Pow, d0]
  let l13 : List ℤ := [p1, p2, Nim, 1, dd, Zs, Zt, Pow, d0]
  let l14 : List ℤ := [Nre, Nim, 1, dd, Zs, Zt, Pow, d0]
  let l15 : List ℤ := [1, Nre, Nim, dd, Zs, Zt, Pow, d0]
  let l16 : List ℤ := [Nre, Nim, dd, Zs, Zt, Pow, d0]
  let S : ℕ := szl (ints l0) + 1
  let Cstep : ℕ := 1000 * KK * S ^ 2
  have hKp : Kp ≤ KK := by simp only [KK]; omega
  have hKr : Kr ≤ KK := by simp only [KK]; omega
  have hKd : Kd ≤ KK := by simp only [KK]; omega
  have hKmul : Kmul ≤ KK := by simp only [KK]; omega
  have hKsub : Ksub ≤ KK := by simp only [KK]; omega
  have hKadd : Kadd ≤ KK := by simp only [KK]; omega
  have hS : 1 ≤ S := by simp only [S]; omega
  -- size bounds for the terms
  have hterm : ∀ z ∈ l0, isz z ≤ szl (ints l0) := by
    intro z hz
    have h : Val.int z ∈ ints l0 := List.mem_map_of_mem hz
    have h2 := le_szl h
    rwa [vsz_int] at h2
  have hpar : ∀ z ∈ l0, isz z ≤ S := by
    intro z hz
    have h := hterm z hz
    simp only [S]
    omega
  have hQre : isz Qre ≤ S := hpar Qre (by simp [l0])
  have hQim : isz Qim ≤ S := hpar Qim (by simp [l0])
  have hdd : isz dd ≤ S := hpar dd (by simp [l0])
  have hZs : isz Zs ≤ S := hpar Zs (by simp [l0])
  have hZt : isz Zt ≤ S := hpar Zt (by simp [l0])
  have hPow : isz Pow ≤ S := hpar Pow (by simp [l0])
  have hd0 : isz d0 ≤ S := hpar d0 (by simp [l0])
  have hone : isz (1 : ℤ) ≤ S := hpar 1 (by simp [l0])
  have hp1 : isz p1 ≤ 2 * S := by
    have h := isz_mul_le Zs Qre
    change isz (Zs * Qre) ≤ 2 * S
    omega
  have hp2 : isz p2 ≤ 2 * S := by
    have h := isz_mul_le Zt Qim
    change isz (Zt * Qim) ≤ 2 * S
    omega
  have hp3 : isz p3 ≤ 2 * S := by
    have h := isz_mul_le Zs Qim
    change isz (Zs * Qim) ≤ 2 * S
    omega
  have hp4 : isz p4 ≤ 2 * S := by
    have h := isz_mul_le Zt Qre
    change isz (Zt * Qre) ≤ 2 * S
    omega
  have hNim : isz Nim ≤ 3 * S := by
    have h := isz_add_le p3 p4
    change isz (p3 + p4) ≤ 3 * S
    rcases le_total (isz p3) (isz p4) with hle | hle
    · rw [max_eq_right hle] at h; omega
    · rw [max_eq_left hle] at h; omega
  have hNre : isz Nre ≤ 3 * S := by
    have h := isz_sub_le p1 p2
    change isz (p1 - p2) ≤ 3 * S
    rcases le_total (isz p1) (isz p2) with hle | hle
    · rw [max_eq_right hle] at h; omega
    · rw [max_eq_left hle] at h; omega
  -- size bounds for every window
  have hl0 : ∀ z ∈ l0, isz z ≤ 3 * S := by
    intro z hz
    simp only [l0, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega
  have hl1 : ∀ z ∈ l1, isz z ≤ 3 * S := by
    intro z hz
    simp only [l1, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega
  have hl2 : ∀ z ∈ l2, isz z ≤ 3 * S := by
    intro z hz
    simp only [l2, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega
  have hl3 : ∀ z ∈ l3, isz z ≤ 3 * S := by
    intro z hz
    simp only [l3, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega
  have hl4 : ∀ z ∈ l4, isz z ≤ 3 * S := by
    intro z hz
    simp only [l4, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega
  have hl5 : ∀ z ∈ l5, isz z ≤ 3 * S := by
    intro z hz
    simp only [l5, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega
  have hl6 : ∀ z ∈ l6, isz z ≤ 3 * S := by
    intro z hz
    simp only [l6, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega
  have hl7 : ∀ z ∈ l7, isz z ≤ 3 * S := by
    intro z hz
    simp only [l7, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega
  have hl8 : ∀ z ∈ l8, isz z ≤ 3 * S := by
    intro z hz
    simp only [l8, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega
  have hl9 : ∀ z ∈ l9, isz z ≤ 3 * S := by
    intro z hz
    simp only [l9, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega
  have hl10 : ∀ z ∈ l10, isz z ≤ 3 * S := by
    intro z hz
    simp only [l10, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega
  have hl11 : ∀ z ∈ l11, isz z ≤ 3 * S := by
    intro z hz
    simp only [l11, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega
  have hl12 : ∀ z ∈ l12, isz z ≤ 3 * S := by
    intro z hz
    simp only [l12, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega
  have hl13 : ∀ z ∈ l13, isz z ≤ 3 * S := by
    intro z hz
    simp only [l13, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega
  have hl14 : ∀ z ∈ l14, isz z ≤ 3 * S := by
    intro z hz
    simp only [l14, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega
  have hl15 : ∀ z ∈ l15, isz z ≤ 3 * S := by
    intro z hz
    simp only [l15, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega
  have hl16 : ∀ z ∈ l16, isz z ≤ 3 * S := by
    intro z hz
    simp only [l16, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega
  -- the sixteen steps
  intro top rest hlen htop
  have step1 : WordR main (pickP 1) (fun vs => vs = ints l0 ++ rest)
      (fun _ out => out = ints l1 ++ rest) (fun _ => Cstep) :=
    wrd_pickI (hpick main) 1 l0 l1 rest (by simp [l1, l0, List.getD]) (by simp [l0])
      (cost_pickroll_x1 hKp (by norm_num) (pickroll_sum_le hl0 (by norm_num)) hS)
  have step2 : WordR main (pickP 6) (fun vs => vs = ints l1 ++ rest)
      (fun _ out => out = ints l2 ++ rest) (fun _ => Cstep) :=
    wrd_pickI (hpick main) 6 l1 l2 rest (by simp [l2, l1, l0, List.getD]) (by simp [l1, l0])
      (cost_pickroll_x1 hKp (by norm_num) (pickroll_sum_le hl1 (by norm_num)) hS)
  have step3 : WordR main mulP (fun vs => vs = ints l2 ++ rest)
      (fun _ out => out = ints l3 ++ rest) (fun _ => Cstep) :=
    wrd_binOpI (hmul main) Zt Qre l0 l2 l3 rest (by rfl) (by rfl) trivial
      (cost_mul_x1 hKmul hZt hQre hS)
  have step4 : WordR main (pickP 3) (fun vs => vs = ints l3 ++ rest)
      (fun _ out => out = ints l4 ++ rest) (fun _ => Cstep) :=
    wrd_pickI (hpick main) 3 l3 l4 rest (by simp [l4, l3, l0, p4, List.getD]) (by simp [l3, l0])
      (cost_pickroll_x1 hKp (by norm_num) (pickroll_sum_le hl3 (by norm_num)) hS)
  have step5 : WordR main (pickP 6) (fun vs => vs = ints l4 ++ rest)
      (fun _ out => out = ints l5 ++ rest) (fun _ => Cstep) :=
    wrd_pickI (hpick main) 6 l4 l5 rest (by simp [l5, l4, l3, l0, p4, List.getD])
      (by simp [l4, l3, l0])
      (cost_pickroll_x1 hKp (by norm_num) (pickroll_sum_le hl4 (by norm_num)) hS)
  have step6 : WordR main mulP (fun vs => vs = ints l5 ++ rest)
      (fun _ out => out = ints l6 ++ rest) (fun _ => Cstep) :=
    wrd_binOpI (hmul main) Zs Qim l3 l5 l6 rest (by rfl) (by rfl) trivial
      (cost_mul_x1 hKmul hZs hQim hS)
  have step7 : WordR main addP (fun vs => vs = ints l6 ++ rest)
      (fun _ out => out = ints l7 ++ rest) (fun _ => Cstep) :=
    wrd_binOpI (hadd main) p3 p4 l0 l6 l7 rest (by rfl) (by rfl) trivial
      (cost_addsub hKadd hp3 hp4 hS)
  have step8 : WordR main (rollP 3) (fun vs => vs = ints l7 ++ rest)
      (fun _ out => out = ints l8 ++ rest) (fun _ => Cstep) :=
    wrd_rollI (hroll main) 3 l7 l8 rest (by simp [l8, l7, l0, List.getD, List.eraseIdx])
      (by simp [l7, l0])
      (cost_pickroll_x1 hKr (by norm_num) (pickroll_sum_le hl7 (by norm_num)) hS)
  have step9 : WordR main (pickP 6) (fun vs => vs = ints l8 ++ rest)
      (fun _ out => out = ints l9 ++ rest) (fun _ => Cstep) :=
    wrd_pickI (hpick main) 6 l8 l9 rest (by simp [l9, l8, l7, l0, List.getD, List.eraseIdx])
      (by simp [l8, l7, l0])
      (cost_pickroll_x1 hKp (by norm_num) (pickroll_sum_le hl8 (by norm_num)) hS)
  have step10 : WordR main mulP (fun vs => vs = ints l9 ++ rest)
      (fun _ out => out = ints l10 ++ rest) (fun _ => Cstep) :=
    wrd_binOpI (hmul main) Zt Qim (l7.eraseIdx 3) l9 l10 rest (by rfl) (by rfl) trivial
      (cost_mul_x1 hKmul hZt hQim hS)
  have step11 : WordR main (rollP 3) (fun vs => vs = ints l10 ++ rest)
      (fun _ out => out = ints l11 ++ rest) (fun _ => Cstep) :=
    wrd_rollI (hroll main) 3 l10 l11 rest
      (by simp [l11, l10, l7, l0, List.getD, List.eraseIdx]) (by simp [l10, l7, l0])
      (cost_pickroll_x1 hKr (by norm_num) (pickroll_sum_le hl10 (by norm_num)) hS)
  have step12 : WordR main (pickP 5) (fun vs => vs = ints l11 ++ rest)
      (fun _ out => out = ints l12 ++ rest) (fun _ => Cstep) :=
    wrd_pickI (hpick main) 5 l11 l12 rest
      (by simp [l12, l11, l10, l7, l0, List.getD, List.eraseIdx]) (by simp [l11, l10, l7, l0])
      (cost_pickroll_x1 hKp (by norm_num) (pickroll_sum_le hl11 (by norm_num)) hS)
  have step13 : WordR main mulP (fun vs => vs = ints l12 ++ rest)
      (fun _ out => out = ints l13 ++ rest) (fun _ => Cstep) :=
    wrd_binOpI (hmul main) Zs Qre (l10.eraseIdx 3) l12 l13 rest (by rfl) (by rfl) trivial
      (cost_mul_x1 hKmul hZs hQre hS)
  have step14 : WordR main subP (fun vs => vs = ints l13 ++ rest)
      (fun _ out => out = ints l14 ++ rest) (fun _ => Cstep) :=
    wrd_binOpI (hsub main) p1 p2 ((l10.eraseIdx 3).eraseIdx 0) l13 l14 rest (by rfl) (by rfl) trivial
      (cost_addsub hKsub hp1 hp2 hS)
  have step15 : WordR main (rollP 2) (fun vs => vs = ints l14 ++ rest)
      (fun _ out => out = ints l15 ++ rest) (fun _ => Cstep) :=
    wrd_rollI (hroll main) 2 l14 l15 rest
      (by simp [l15, l14, l10, l7, l0, List.getD, List.eraseIdx]) (by simp [l14, l10, l7, l0])
      (cost_pickroll_x1 hKr (by norm_num) (pickroll_sum_le hl14 (by norm_num)) hS)
  have step16 : WordR main dropP (fun vs => vs = ints l15 ++ rest)
      (fun _ out => out = ints l16 ++ rest) (fun _ => Cstep) :=
    wrd_dropI (hdrop main) 1 (l14.eraseIdx 2) l15 l16 rest
      (by simp [l15, l14, l10, l7, l0, List.eraseIdx])
      (by simp [l16, l14, l10, l7, l0, List.eraseIdx]) (cost_drop_x1 hKd hone hS)
  have H15 : WordR main _ (fun vs => vs = ints l14 ++ rest)
      (fun _ out => out = ints l16 ++ rest) (fun _ => 2 * Cstep) :=
    wrd_seq2z hk step15 step16 (by ring)
  have H14 : WordR main _ (fun vs => vs = ints l13 ++ rest)
      (fun _ out => out = ints l16 ++ rest) (fun _ => 3 * Cstep) :=
    wrd_seq2z hk step14 H15 (by ring)
  have H13 : WordR main _ (fun vs => vs = ints l12 ++ rest)
      (fun _ out => out = ints l16 ++ rest) (fun _ => 4 * Cstep) :=
    wrd_seq2z hk step13 H14 (by ring)
  have H12 : WordR main _ (fun vs => vs = ints l11 ++ rest)
      (fun _ out => out = ints l16 ++ rest) (fun _ => 5 * Cstep) :=
    wrd_seq2z hk step12 H13 (by ring)
  have H11 : WordR main _ (fun vs => vs = ints l10 ++ rest)
      (fun _ out => out = ints l16 ++ rest) (fun _ => 6 * Cstep) :=
    wrd_seq2z hk step11 H12 (by ring)
  have H10 : WordR main _ (fun vs => vs = ints l9 ++ rest)
      (fun _ out => out = ints l16 ++ rest) (fun _ => 7 * Cstep) :=
    wrd_seq2z hk step10 H11 (by ring)
  have H9 : WordR main _ (fun vs => vs = ints l8 ++ rest)
      (fun _ out => out = ints l16 ++ rest) (fun _ => 8 * Cstep) :=
    wrd_seq2z hk step9 H10 (by ring)
  have H8 : WordR main _ (fun vs => vs = ints l7 ++ rest)
      (fun _ out => out = ints l16 ++ rest) (fun _ => 9 * Cstep) :=
    wrd_seq2z hk step8 H9 (by ring)
  have H7 : WordR main _ (fun vs => vs = ints l6 ++ rest)
      (fun _ out => out = ints l16 ++ rest) (fun _ => 10 * Cstep) :=
    wrd_seq2z hk step7 H8 (by ring)
  have H6 : WordR main _ (fun vs => vs = ints l5 ++ rest)
      (fun _ out => out = ints l16 ++ rest) (fun _ => 11 * Cstep) :=
    wrd_seq2z hk step6 H7 (by ring)
  have H5 : WordR main _ (fun vs => vs = ints l4 ++ rest)
      (fun _ out => out = ints l16 ++ rest) (fun _ => 12 * Cstep) :=
    wrd_seq2z hk step5 H6 (by ring)
  have H4 : WordR main _ (fun vs => vs = ints l3 ++ rest)
      (fun _ out => out = ints l16 ++ rest) (fun _ => 13 * Cstep) :=
    wrd_seq2z hk step4 H5 (by ring)
  have H3 : WordR main _ (fun vs => vs = ints l2 ++ rest)
      (fun _ out => out = ints l16 ++ rest) (fun _ => 14 * Cstep) :=
    wrd_seq2z hk step3 H4 (by ring)
  have H2 : WordR main _ (fun vs => vs = ints l1 ++ rest)
      (fun _ out => out = ints l16 ++ rest) (fun _ => 15 * Cstep) :=
    wrd_seq2z hk step2 H3 (by ring)
  have H1 : WordR main _ (fun vs => vs = ints l0 ++ rest)
      (fun _ out => out = ints l16 ++ rest) (fun _ => 16 * Cstep) :=
    wrd_seq2z hk step1 H2 (by ring)
  have htop' : top = ints l0 := by rw [htop]; rfl
  refine hk.conseq (main := main) (p := expStepProg mulP addP subP dropP pickP rollP)
    (P := fun vs => vs = ints l0 ++ rest) (P' := fun vs => vs = top ++ rest)
    (Q := fun _ out => out = ints l16 ++ rest)
    (Q' := fun _ out => ∃ o, out = o ++ rest ∧
      o = [Val.int (Zs * Qre - Zt * Qim), Val.int (Zs * Qim + Zt * Qre),
        Val.int dd, Val.int Zs, Val.int Zt, Val.int Pow, Val.int d0])
    (C := fun _ => 16 * Cstep) (C' := fun _ => (16000 * KK + 2) * (szl top + 1) ^ (16000 * KK + 2))
    H1 ?_ ?_ ?_
  · intro vs hv
    rw [hv, htop']
  · intro vs out _ hq
    exact ⟨ints l16, hq, by rfl⟩
  · intro vs _
    rw [htop']
    have hpow : S ^ 2 ≤ S ^ (16000 * KK + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    have hC : 16 * Cstep = 16000 * KK * S ^ 2 := by simp only [Cstep]; ring
    rw [hC]
    calc 16000 * KK * S ^ 2 ≤ (16000 * KK + 2) * S ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (16000 * KK + 2) * S ^ (16000 * KK + 2) := Nat.mul_le_mul_left _ hpow

end Work.Fx
