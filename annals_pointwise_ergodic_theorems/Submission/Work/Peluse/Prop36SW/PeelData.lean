import Mathlib
import Submission.Work.Peluse.Prop36SW.GenDefs
import Submission.Work.Peluse.ladderA_defs

/-!
# The data of one peel of the §5 chain

One application of `PeluseLadderA` followed by the peel of the long directions turns a state
`LState kω p M₁ M₂ N D A g γ` (with slot type `ι`, multiplicity `1`) into a state whose

* slot type is `PeelSlot s₀ = {s : Slot ι (fun _ => 1) // s ≠ s₀}`,
* multiplicity function is `peelKω kω s₀` (the transported multiplicities),
* coefficient function is `peelP` (it does not depend on the new parameters),
* parameter type is `PeelParam` (a triple: the old parameters `a ∈ A`, the old parameter-box point
  `b`, and the shifts of the `t'` long directions — the latter all range over the *same* set
  `arithIcc (p s₀ a) ⌊γ'M₁M₂⌋` because the ladder's long directions are equal), on which the
  function is `peelG`,
* ambient is `peelN` (the shifts move the support by at most `t'·|ι|·D·N`).

See `NOTES_prop36SW_of_ladderA_SESSION3.md` §3.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-- The slot type after peeling the slot `s₀`. -/
abbrev PeelSlot {ι : Type} (s₀ : Slot ι (fun _ => 1)) : Type := {s : Slot ι (fun _ => 1) // s ≠ s₀}

/-- The multiplicity function of the state after peeling `s₀`: the nonempty subsets of the
remaining slots, with the multiplicities transported along the inclusion. -/
def peelKω {ι : Type} [Fintype ι] [DecidableEq ι] (kω : SlotSet ι (fun _ => 1) → ℕ)
    (s₀ : Slot ι (fun _ => 1)) : SlotSet (PeelSlot s₀) (fun _ => 1) → ℕ :=
  fun ω => kω ⟨ω.1.image (fun x : Slot (PeelSlot s₀) (fun _ => 1) => x.1.1),
    Finset.image_nonempty.mpr ω.2⟩

/-- The parameter type of the state after peeling `s₀`. -/
abbrev PeelParam {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} [DecidableEq P]
    (p : ι → P → ℤ) (M₁ M₂ : ℕ) (A : Finset P) (γ' : ℝ) (t' : ℕ) (s₀ : Slot ι (fun _ => 1)) :
    Type :=
  Σ ab : {a : P // a ∈ A} × {b : Slot ι (fun _ => 1) → ℤ // b ∈ paramBox (k := fun _ : ι => 1) M₂},
    (j : Fin t') →
      ↥(arithIcc (p s₀.1 ab.1.1) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) ×
        ↥(arithIcc (p s₀.1 ab.1.1) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)

/-- The coefficient function of the state after peeling `s₀`: it does not depend on the new
parameters. -/
def peelP {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} [DecidableEq P]
    (p : ι → P → ℤ) (M₁ M₂ : ℕ) (A : Finset P) (γ' : ℝ) (t' : ℕ) (s₀ : Slot ι (fun _ => 1)) :
    PeelSlot s₀ → PeelParam p M₁ M₂ A γ' t' s₀ → ℤ :=
  fun s q => p s.1.1 q.1.1.1

/-- The function of the state after peeling `s₀`: the `t'`-fold iterated difference of the old
function along the extracted shifts. -/
def peelG {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} [DecidableEq P]
    (p : ι → P → ℤ) (M₁ M₂ : ℕ) (A : Finset P) (γ' : ℝ) (t' : ℕ) (s₀ : Slot ι (fun _ => 1))
    (g : P → ℤ → ℂ) : PeelParam p M₁ M₂ A γ' t' s₀ → ℤ → ℂ :=
  fun q => Ulower.iterDelta t' (fun j => (((q.2 j).1 : ℤ), ((q.2 j).2 : ℤ))) (g q.1.1.1)

/-- The ambient of the state after peeling `s₀`.  The shifts live in the long direction sets,
whose common difference is `p s₀ a` and whose length is `⌊γ'M₁M₂⌋`; by the state's shift bound
`|p s₀ a| M₁ M₂ ≤ D N` each shift is at most `γ' D N` in modulus, so `t'` of them move the support by
at most `t' ⌈γ'D⌉ N`. -/
def peelN (N D t' : ℕ) (γ' : ℝ) : ℕ := N * (1 + t' * ⌈γ' * (D : ℝ)⌉₊)

/-- The expansion `Ioo (-(H+1)) (H+1) = Icc (-H) H` on `ℤ`, the identification of the ladder's
parameter box with the closed box of the chain's states. -/
theorem Ioo_succ_eq_Icc (H : ℕ) :
    Finset.Ioo (-((H + 1 : ℕ) : ℤ)) ((H + 1 : ℕ) : ℤ) = Finset.Icc (-(H : ℤ)) (H : ℤ) := by
  ext x
  simp only [Finset.mem_Ioo, Finset.mem_Icc]
  constructor <;> intro h <;> omega

end

end Work.Peluse.Prop36SW
