import Mathlib
import Submission.Work.Kernel.Raw

/-!
# `crtLabSetup`: the `WordR` toolkit of exact-stack steps

Ingredients of `Work.MainP.crtLabSetup` (the *setup* phase of the CRT label-and-sort word:
from `int S :: intList ss` produce the driver list `drv S` together with the initial accumulator
`acc ss 0`).  Nothing here refers to the CRT definitions, so the file only needs the interface.

* `wordR_lift` / `wordR_seqC`: the two glue rules of `HvdH.WordR` for *exact* value stacks;
* `step_*`: the `KernelLib`/`LayoutLib` fields turned into steps of the shape
  `WordR main p (fun vs => vs = L) (fun _ out => out = M) (fun _ => c)`;
* `wordR_exists_tail`: from a family of `WordR`s indexed by the (unknown) tail of stack 0 to a
  single `WordR` whose pre/post-condition existentially quantifies that tail.

Everything is `sorry`-free.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

/-! ## Glue rules for `WordR` on exact value stacks -/

/-- Turn a `WordR` with a structural pre/post-condition into one with exact value stacks. -/
theorem wordR_lift {main p : Cmd} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {C : List Val → ℕ} (h : WordR main p P Q C) {L M : List Val} {c : ℕ}
    (hP : P L) (hQ : ∀ out, Q L out → out = M) (hC : C L ≤ c) :
    WordR main p (fun vs => vs = L) (fun _ out => out = M) (fun _ => c) := by
  intro vs hvs s R hR
  cases hvs
  obtain ⟨out, s', n, hq, hev, hn, hstk, hfr⟩ := h L hP s R hR
  exact ⟨out, s', n, hQ out hq, hev, le_trans hn hC, hstk, hfr⟩

/-- Compose two exact-stack `WordR`s (both with constant cost). -/
theorem wordR_seqC (hK : KernelLib) {main p q : Cmd} {L M N : List Val} {c c' : ℕ}
    (hp : WordR main p (fun vs => vs = L) (fun _ out => out = M) (fun _ => c))
    (hq : WordR main q (fun vs => vs = M) (fun _ out => out = N) (fun _ => c')) :
    WordR main (.seq p q) (fun vs => vs = L) (fun _ out => out = N) (fun _ => c + c') := by
  have h := hK.seq main p q (fun vs => vs = L) (fun _ out => out = M) (fun _ => c)
    (fun vs => vs = M) (fun _ out => out = N) (fun _ => c') (fun _ => c') hp hq
    (fun vs mid _ hM => ⟨hM, le_refl _⟩)
  refine hK.conseq main (.seq p q) (fun vs => vs = L) (fun vs => vs = L)
    (fun vs out => ∃ mid, mid = M ∧ out = N) (fun _ out => out = N) (fun _ => c + c')
    (fun _ => c + c') h (fun _ hh => hh) ?_ (fun _ _ => le_refl _)
  intro vs out _ hq
  obtain ⟨-, -, hout⟩ := hq
  exact hout

/-- From a family of `WordR`s indexed by the tail of stack 0 to one `WordR` with an
existentially quantified tail. -/
theorem wordR_exists_tail {main p : Cmd} (F G : List Val → List Val) (C : ℕ)
    (h : ∀ tl : List Val, WordR main p (fun vs => vs = F tl) (fun _ out => out = G tl)
      (fun _ => C)) :
    WordR main p (fun vs => ∃ tl, vs = F tl) (fun vs out => ∃ tl, vs = F tl ∧ out = G tl)
      (fun _ => C) := by
  intro vs hvs s R hR
  obtain ⟨tl, rfl⟩ := hvs
  obtain ⟨out, s', n, hq, hev, hn, hstk, hfr⟩ := h tl (F tl) rfl s R hR
  exact ⟨out, s', n, ⟨tl, rfl, hq⟩, hev, hn, hstk, hfr⟩

/-! ## The fields of the libraries as exact-stack steps -/

/-- `KernelLib.pushVal` as a step. -/
theorem step_pushVal {main p : Cmd} {K0 : ℕ}
    (h : ∀ v : Val, WordR main p (fun _ => True) (fun vs out => out = v :: vs)
      (fun _ => K0 * (vsz v + 1)))
    (v : Val) (L : List Val) (c : ℕ) (hc : K0 * (vsz v + 1) ≤ c) :
    WordR main p (fun vs => vs = L) (fun _ out => out = v :: L) (fun _ => c) :=
  wordR_lift (h v) trivial (fun _ hq => hq) hc

/-- `KernelLib.consV` as a step. -/
theorem step_consV {main p : Cmd} {K0 : ℕ}
    (h : WordR main p (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = Val.cons a b :: rest) (fun _ => K0))
    (a b : Val) (tl : List Val) (c : ℕ) (hc : K0 ≤ c) :
    WordR main p (fun vs => vs = a :: b :: tl) (fun _ out => out = Val.cons a b :: tl)
      (fun _ => c) := by
  refine wordR_lift h (by simp) ?_ hc
  intro out hq
  obtain ⟨a', b', rest, hv, hout⟩ := hq
  simp only [List.cons.injEq] at hv
  obtain ⟨rfl, rfl, rfl⟩ := hv
  exact hout

/-- `KernelLib.swap` as a step. -/
theorem step_swap {main p : Cmd} {K0 : ℕ}
    (h : WordR main p (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => K0 * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (a b : Val) (tl : List Val) (c : ℕ) (hc : K0 * (vsz a + vsz b + 1) ≤ c) :
    WordR main p (fun vs => vs = a :: b :: tl) (fun _ out => out = b :: a :: tl) (fun _ => c) := by
  refine wordR_lift h (by simp) ?_ ?_
  · intro out hq
    obtain ⟨a', b', rest, hv, hout⟩ := hq
    simp only [List.cons.injEq] at hv
    obtain ⟨rfl, rfl, rfl⟩ := hv
    exact hout
  · simpa using hc

/-- `KernelLib.drop` as a step. -/
theorem step_drop {main p : Cmd} {K0 : ℕ}
    (h : WordR main p (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => K0 * (vsz (vs.headD .nil) + 1)))
    (a : Val) (tl : List Val) (c : ℕ) (hc : K0 * (vsz a + 1) ≤ c) :
    WordR main p (fun vs => vs = a :: tl) (fun _ out => out = tl) (fun _ => c) := by
  refine wordR_lift h (by simp) ?_ ?_
  · intro out hq
    obtain ⟨v, rest, hv, hout⟩ := hq
    simp only [List.cons.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact hout
  · simpa using hc

/-- `KernelLib.roll` as a step. -/
theorem step_roll {main : Cmd} {p : ℕ → Cmd} {K0 : ℕ}
    (h : ∀ k : ℕ, WordR main (p k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K0 * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (k : ℕ) (L : List Val) (hk : k < L.length) (c : ℕ)
    (hc : K0 * (k + 1) * (((L.take (k + 1)).map vsz).sum + 1) ≤ c) :
    WordR main (p k) (fun vs => vs = L) (fun _ out => out = L.getD k .nil :: L.eraseIdx k)
      (fun _ => c) :=
  wordR_lift (h k) hk (fun _ hq => hq) hc

/-- `LayoutLib.replicate` as a step. -/
theorem step_replicate {main p : Cmd} {K0 : ℕ}
    (h : ∀ (k : ℕ) (v : Val), WordR main p (fun vs => ∃ rest, vs = Val.int (k : ℤ) :: v :: rest)
      (fun vs out => ∃ rest, vs = Val.int (k : ℤ) :: v :: rest ∧
        out = ofList (List.replicate k v) :: rest)
      (fun _ => K0 * ((k + 1) * (vsz v + 1) + isz (k : ℤ) + 1)))
    (k : ℕ) (v : Val) (tl : List Val) (c : ℕ)
    (hc : K0 * ((k + 1) * (vsz v + 1) + isz (k : ℤ) + 1) ≤ c) :
    WordR main p (fun vs => vs = Val.int (k : ℤ) :: v :: tl)
      (fun _ out => out = ofList (List.replicate k v) :: tl) (fun _ => c) := by
  refine wordR_lift (h k v) ⟨tl, rfl⟩ ?_ hc
  intro out hq
  obtain ⟨r, hr, hout⟩ := hq
  have hr' : r = tl := by simpa using hr.symm
  rw [hr'] at hout
  exact hout

end Work.MainP
