import Mathlib
import Submission.Work.Resample.auParkDefs

/-!
# The five "parking" step adapters for `Work.Resample.auCWPark`

Each lemma lifts one word of `KernelLib` / one value mover of `Work.Resample.auRoundAux` from
the `WordR`/`WordM` interface into the `PreD`/`PostD` state description of
`Submission/Work/Resample/auParkDefs.lean` (value stack and parking stack `1`), with the uniform
cost shape `KB * (S + 1)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH

/-- `auRoundPush 1`: move the top value of stack `0` to the front of the parking stack. -/
theorem auParkStepPush {main p : Cmd} {Kc KB S : ℕ}
    (h : ∀ (m : Cmd) (v : Val) (rest L : List Val),
      WordM m p (fun vs a => vs = v :: rest ∧ a 1 = L)
        (fun vs a out b => out = rest ∧ b 1 = v :: L ∧ (∀ k, k ≠ 0 → k ≠ 1 → b k = a k))
        (fun _ _ => Kc * (vsz v + 1)))
    (hK : Kc ≤ KB) {v : Val} (hv : vsz v ≤ S) {V' L1 : List Val} :
    WordM main p (PreD (v :: V') L1) (PostD V' (v :: L1)) (fun _ _ => KB * (S + 1)) := by
  refine WordM.conseq (h main v V' L1) ?_ ?_ ?_
  · rintro vs a ⟨hvs, hP⟩
    exact ⟨hvs, by simpa using hP 1 (by decide)⟩
  · rintro vs a out b ⟨hvs, hP⟩ ⟨hout, hb1, hbk⟩
    refine ⟨hout, fun k hk0 => ?_⟩
    by_cases hk1 : k = 1
    · subst hk1; simpa using hb1
    · rw [hbk k hk0 hk1, hP k hk0, if_neg hk1, if_neg hk1]
  · intro vs a _
    calc Kc * (vsz v + 1) ≤ KB * (vsz v + 1) := Nat.mul_le_mul_right _ hK
      _ ≤ KB * (S + 1) := Nat.mul_le_mul_left _ (by omega)

/-- `auRoundPop 1`: move the first value of the parking stack to the top of stack `0`. -/
theorem auParkStepPop {main p : Cmd} {Kc KB S : ℕ}
    (h : ∀ (m : Cmd) (v : Val) (L rest : List Val),
      WordM m p (fun vs a => vs = rest ∧ a 1 = v :: L)
        (fun vs a out b => out = v :: vs ∧ b 1 = L ∧ (∀ k, k ≠ 0 → k ≠ 1 → b k = a k))
        (fun _ _ => Kc * (vsz v + 1)))
    (hK : Kc ≤ KB) {v : Val} (hv : vsz v ≤ S) {V L1 : List Val} :
    WordM main p (PreD V (v :: L1)) (PostD (v :: V) L1) (fun _ _ => KB * (S + 1)) := by
  refine WordM.conseq (h main v L1 V) ?_ ?_ ?_
  · rintro vs a ⟨hvs, hP⟩
    exact ⟨hvs, by simpa using hP 1 (by decide)⟩
  · rintro vs a out b ⟨hvs, hP⟩ ⟨hout, hb1, hbk⟩
    refine ⟨by rw [hout, hvs], fun k hk0 => ?_⟩
    by_cases hk1 : k = 1
    · subst hk1; simpa using hb1
    · rw [hbk k hk0 hk1, hP k hk0, if_neg hk1, if_neg hk1]
  · intro vs a _
    calc Kc * (vsz v + 1) ≤ KB * (vsz v + 1) := Nat.mul_le_mul_right _ hK
      _ ≤ KB * (S + 1) := Nat.mul_le_mul_left _ (by omega)

/-- `KernelLib.drop`: delete the top value of stack `0`. -/
theorem auParkStepDrop {main p : Cmd} {Kc KB S : ℕ}
    (h : ∀ m : Cmd, WordR m p (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => Kc * (vsz (vs.headD .nil) + 1)))
    (hK : Kc ≤ KB) {v : Val} (hv : vsz v ≤ S) {V' L1 : List Val} :
    WordM main p (PreD (v :: V') L1) (PostD V' L1) (fun _ _ => KB * (S + 1)) := by
  refine WordM.conseq (WordM.ofWordR (h main)) ?_ ?_ ?_
  · rintro vs a ⟨hvs, _⟩
    rw [hvs]; simp
  · rintro vs a out b ⟨hvs, hP⟩ ⟨⟨w, rest, hw, hout⟩, hb⟩
    have hwr : rest = V' := (List.cons.inj (hw.symm.trans hvs)).2
    refine ⟨by rw [hout, hwr], ?_⟩
    rw [hb]; exact hP
  · rintro vs a ⟨hvs, _⟩
    rw [hvs]
    simp only [List.headD_cons]
    calc Kc * (vsz v + 1) ≤ KB * (vsz v + 1) := Nat.mul_le_mul_right _ hK
      _ ≤ KB * (S + 1) := Nat.mul_le_mul_left _ (by omega)

/-- `KernelLib.consV`: form `cons a b` from the top two values (constant cost). -/
theorem auParkStepCons {main p : Cmd} {Kc KB S : ℕ}
    (h : ∀ m : Cmd, WordR m p (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => Kc))
    (hK : Kc ≤ KB) {V' L1 : List Val} {a b : Val} :
    WordM main p (PreD (a :: b :: V') L1) (PostD (.cons a b :: V') L1)
      (fun _ _ => KB * (S + 1)) := by
  refine WordM.conseq (WordM.ofWordR (h main)) ?_ ?_ ?_
  · rintro vs a' ⟨hvs, _⟩
    rw [hvs]; simp
  · rintro vs a' out b' ⟨hvs, hP⟩ ⟨⟨a₀, b₀, rest, hvs₀, hout⟩, hb⟩
    obtain ⟨h1, h2⟩ := List.cons.inj (hvs₀.symm.trans hvs)
    obtain ⟨h3, h4⟩ := List.cons.inj h2
    refine ⟨by rw [hout, h1, h3, h4], ?_⟩
    rw [hb]; exact hP
  · rintro vs a' _
    calc Kc ≤ KB := hK
      _ ≤ KB * (S + 1) := by
          calc KB = KB * 1 := (Nat.mul_one KB).symm
            _ ≤ KB * (S + 1) := Nat.mul_le_mul_left KB (by omega)

/-- `KernelLib.roll`: move the `j`-th value of stack `0` to the top. -/
theorem auParkStepRoll {main : Cmd} {p : ℕ → Cmd} {Kc KB S : ℕ}
    (h : ∀ (m : Cmd) (j : ℕ), WordR m (p j) (fun vs => j < vs.length)
      (fun vs out => out = vs.getD j .nil :: vs.eraseIdx j)
      (fun vs => Kc * (j + 1) * (((vs.take (j + 1)).map vsz).sum + 1)))
    (hK : Kc * 21 * 21 ≤ KB) {V L1 : List Val} {j : ℕ} (hj : j < V.length)
    (h21 : j + 1 ≤ 21) (hv : ∀ x ∈ V.take (j + 1), vsz x ≤ S) :
    WordM main (p j) (PreD V L1) (PostD (V.getD j .nil :: V.eraseIdx j) L1)
      (fun _ _ => KB * (S + 1)) := by
  refine WordM.conseq (WordM.ofWordR (h main j)) ?_ ?_ ?_
  · rintro vs a ⟨hvs, _⟩; rw [hvs]; exact hj
  · rintro vs a out b ⟨hvs, hP⟩ ⟨hout, hb⟩
    refine ⟨by rw [hout, hvs], ?_⟩
    rw [hb]; exact hP
  · rintro vs a ⟨hvs, _⟩
    rw [hvs]
    have hlen : (V.take (j + 1)).length ≤ 21 := by
      rw [List.length_take]; omega
    have hsum : Work.Fx.szl (V.take (j + 1)) ≤ 21 * S :=
      le_trans (szl_le_len_mul hv) (Nat.mul_le_mul_right S hlen)
    have h2 : Work.Fx.szl (V.take (j + 1)) + 1 ≤ 21 * (S + 1) := by nlinarith [hsum]
    calc Kc * (j + 1) * (((V.take (j + 1)).map vsz).sum + 1)
        = Kc * ((j + 1) * (Work.Fx.szl (V.take (j + 1)) + 1)) := by
          simp only [Work.Fx.szl]; ring
      _ ≤ Kc * (21 * (21 * (S + 1))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul h21 h2)
      _ = (Kc * 21 * 21) * (S + 1) := by ring
      _ ≤ KB * (S + 1) := Nat.mul_le_mul_right _ hK

end Work.Resample
