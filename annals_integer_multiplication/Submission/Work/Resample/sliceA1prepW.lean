import Mathlib
import Submission.Work.Resample.sliceA1prep
import Submission.Work.Kernel.Raw

/-!
# `Work.Resample.sliceA1prepW`: the static-data word `prep` of the `Ã₁` slice

In the *non-uniform* statement `Work.Resample.sliceA1` the parameters `p, α, s, t` are fixed
before the existential, so the static data block `P = [slT p α s t]` of the resampling word
(paper Lemma 4.9) is a *constant*: `prep` only has to drop the four parameter values and push
the table.  Accordingly the cost of `prep` involves no `Cm` (no multiplication is performed):
it is bounded by `K*(t+1)*(p+1)^K` for a constant `K` that may depend on `p, α, s, t`.

The program is `KernelLib.drop` iterated four times, followed by `KernelLib.pushVal` of the
table value.  The file proves

* `prepWDropHead` / `prepWDropAll`: dropping a whole list of values off the value stack, with a
  cost linear in the total size of the dropped values (`Kd` is the constant of `KernelLib.drop`);
* `prepWExistsRest`: the bookkeeping that lifts a word stated for a *fixed* suffix `rest` to the
  existential precondition `∃ rest, vs = xs ++ rest` used by the interface;
* the arithmetic facts controlling the final constant.

The main theorem then exhibits the program and a suitable constant `K = C₀ + 1`, where `C₀` is
the concrete cost of the run.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ## Dropping a whole list of values -/

/-- `dropAllProg progD xs` runs `progD` once per element of `xs`. -/
def dropAllProg (progD : Cmd) : List Val → Cmd
  | [] => .skip
  | _ :: tl => .seq progD (dropAllProg progD tl)

/-- One `KernelLib.drop` step, with the head of the value stack fixed by the precondition. -/
theorem prepWDropHead {main : Cmd} {progD : Cmd} {Kd : ℕ}
    (hD : WordR main progD (fun vs => vs ≠ [])
      (fun vs out => ∃ v r, vs = v :: r ∧ out = r)
      (fun vs => Kd * (vsz (vs.headD .nil) + 1))) (a : Val) (rest : List Val) :
    WordR main progD (fun vs => vs = a :: rest) (fun _ out => out = rest)
      (fun _ => Kd * (vsz a + 1)) := by
  refine Work.Kernel.WordR_conseq hD ?_ ?_ ?_
  · intro vs hvs; rw [hvs]; simp
  · intro vs out hvs hq
    obtain ⟨v, r, hv, hout⟩ := hq
    rw [hvs] at hv
    simp only [List.cons.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact hout
  · intro vs hvs
    rw [hvs]
    simp

/-- The cost arithmetic of the induction step of `prepWDropAll`. -/
theorem prepWCostArith (Kd V S L : ℕ) :
    Kd * (V + 1) + (Kd + 1) * (S + L + 1) ≤ (Kd + 1) * (V + S + (L + 1) + 1) := by
  have h : Kd * (V + 1) ≤ (Kd + 1) * (V + 1) := Nat.mul_le_mul_right _ (Nat.le_succ Kd)
  have e : (Kd + 1) * (V + 1) + (Kd + 1) * (S + L + 1)
      = (Kd + 1) * (V + S + (L + 1) + 1) := by
    ring
  calc Kd * (V + 1) + (Kd + 1) * (S + L + 1)
      ≤ (Kd + 1) * (V + 1) + (Kd + 1) * (S + L + 1) := Nat.add_le_add_right h _
    _ = (Kd + 1) * (V + S + (L + 1) + 1) := e

/-- Dropping *all* the values of `xs` (deterministic statement, with the suffix `rest` fixed).
Cost: `(Kd+1) * (Σ vsz xs + length xs + 1)`. -/
theorem prepWDropAll {main : Cmd} {progD : Cmd} {Kd : ℕ}
    (hD : WordR main progD (fun vs => vs ≠ [])
      (fun vs out => ∃ v r, vs = v :: r ∧ out = r)
      (fun vs => Kd * (vsz (vs.headD .nil) + 1))) :
    ∀ (xs : List Val) (rest : List Val),
      WordR main (dropAllProg progD xs) (fun vs => vs = xs ++ rest) (fun _ out => out = rest)
        (fun _ => (Kd + 1) * ((xs.map vsz).sum + xs.length + 1)) := by
  intro xs
  induction xs with
  | nil =>
    intro rest
    refine Work.Kernel.WordR_conseq (Work.Kernel.WordR_skip main) ?_ ?_ ?_
    · intro vs _; trivial
    · intro vs out hvs hq; rw [hq]; exact hvs
    · intro vs _; simp
  | cons a tl ih =>
    intro rest
    have h1 : WordR main progD (fun vs => vs = a :: (tl ++ rest)) (fun _ out => out = tl ++ rest)
        (fun _ => Kd * (vsz a + 1)) := prepWDropHead hD a (tl ++ rest)
    have h2 : WordR main (dropAllProg progD tl) (fun vs => vs = tl ++ rest)
        (fun _ out => out = rest)
        (fun _ => (Kd + 1) * ((tl.map vsz).sum + tl.length + 1)) := ih rest
    have h3 := Work.Kernel.WordR_seq h1 h2
      (B := fun _ => (Kd + 1) * ((tl.map vsz).sum + tl.length + 1))
      (fun vs mid _ hmid => ⟨hmid, le_rfl⟩)
    refine Work.Kernel.WordR_conseq h3 ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out _ hq
      obtain ⟨mid, _, hout⟩ := hq
      exact hout
    · intro vs _
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      exact prepWCostArith Kd (vsz a) ((tl.map vsz).sum) tl.length

/-- Lifting a word stated for every *fixed* suffix `rest` to the existential precondition
`∃ rest, vs = xs ++ rest` (the form used by the interface). -/
theorem prepWExistsRest {main p : Cmd} {xs : List Val} {Post : List Val → List Val → Prop}
    {C : ℕ} (h : ∀ rest : List Val, WordR main p (fun vs => vs = xs ++ rest)
      (fun _ out => Post rest out) (fun _ => C)) :
    WordR main p (fun vs => ∃ rest, vs = xs ++ rest)
      (fun vs out => ∃ rest, vs = xs ++ rest ∧ Post rest out) (fun _ => C) := by
  intro vs ⟨rest, hvs⟩ s R hR
  obtain ⟨out, s', n, hpost, he, hn, hstk, hoth⟩ := h rest vs hvs s R hR
  exact ⟨out, s', n, ⟨rest, hvs, hpost⟩, he, hn, hstk, hoth⟩

/-- The final arithmetic: the chosen constant dominates the actual cost. -/
theorem prepWLeMulPow (C t p : ℕ) : C ≤ (C + 1) * (t + 1) * (p + 1) ^ (C + 1) := by
  have h2 : 1 ≤ (t + 1) * (p + 1) ^ (C + 1) := by
    have hp1 : 0 < (p + 1) ^ (C + 1) := pow_pos (by omega) _
    have ht1 : 0 < t + 1 := by omega
    exact Nat.succ_le_iff.mpr (Nat.mul_pos ht1 hp1)
  calc C ≤ C + 1 := Nat.le_succ C
    _ = (C + 1) * 1 := (Nat.mul_one _).symm
    _ ≤ (C + 1) * ((t + 1) * (p + 1) ^ (C + 1)) := Nat.mul_le_mul_left _ h2
    _ = (C + 1) * (t + 1) * (p + 1) ^ (C + 1) := by ring

/-! ## The main theorem -/

theorem sliceA1prepW (KL : HvdH.KernelLib) (p α s t : ℕ) (hs : 2 ≤ s) (hα : 2 ≤ α) (ht : 0 < t)
    (hst : s ≤ t) :
    ∃ (prep : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ),
      Monotone Cm → HvdH.MulBelow main N Cm → K * p < N →
      HvdH.WordR main prep
        (fun vs => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest)
        (fun vs out => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest ∧
          out = [Work.Resample.slT p α s t] ++ rest)
        (fun _ => K * (t + 1) * (p + 1) ^ K) := by
  obtain ⟨progD, Kd, hD⟩ := KL.drop
  obtain ⟨progP, Kp, hP⟩ := KL.pushVal
  -- the four parameter values (as a list), the constant table value, and the cost constant
  set vT : Val := Work.Resample.slT p α s t with hvT
  set xs : List Val := [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ)] with hxs
  set C₀ : ℕ := (Kd + 1) * ((xs.map vsz).sum + xs.length + 1) + Kp * (vsz vT + 1) with hC₀
  refine ⟨Cmd.seq (dropAllProg progD xs) (progP vT), C₀ + 1, ?_⟩
  intro main N Cm hmon hmb hN
  -- for a fixed suffix `rest`, drop the four parameters and push the table
  have hFixed : ∀ rest : List Val, WordR main (Cmd.seq (dropAllProg progD xs) (progP vT))
      (fun vs => vs = xs ++ rest) (fun _ out => out = vT :: rest) (fun _ => C₀) := by
    intro rest
    have h1 : WordR main (dropAllProg progD xs) (fun vs => vs = xs ++ rest)
        (fun _ out => out = rest)
        (fun _ => (Kd + 1) * ((xs.map vsz).sum + xs.length + 1)) :=
      prepWDropAll (hD main) xs rest
    have h2 : WordR main (progP vT) (fun _ => True) (fun vs out => out = vT :: vs)
        (fun _ => Kp * (vsz vT + 1)) := hP main vT
    have h3 := Work.Kernel.WordR_seq h1 h2 (B := fun _ => Kp * (vsz vT + 1))
      (fun vs mid _ hmid => ⟨trivial, le_rfl⟩)
    refine Work.Kernel.WordR_conseq h3 ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out _ hq
      obtain ⟨mid, hm, ho⟩ := hq
      rw [hm] at ho
      exact ho
    · intro vs _
      exact le_of_eq hC₀.symm
  -- pass to the existential precondition/postcondition of the interface
  refine Work.Kernel.WordR_conseq (prepWExistsRest hFixed) ?_ ?_ ?_
  · intro vs h; simpa [hxs] using h
  · intro vs out _ hpost
    obtain ⟨rest, hvs, hout⟩ := hpost
    exact ⟨rest, by simpa [hxs] using hvs, by rw [hout]; simp [hvT]⟩
  · intro vs _
    exact prepWLeMulPow C₀ t p

end Work.Resample
