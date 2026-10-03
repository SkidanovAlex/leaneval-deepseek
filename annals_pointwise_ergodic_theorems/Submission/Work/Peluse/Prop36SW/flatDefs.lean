import Mathlib
import Submission.Work.Peluse.Prop36SW.lstatePeelAbs

/-!
# The **flat** (`Fin n → ℤ`) parameter type of the §5 peel — the repair of the parameter-type defect

See `NOTES_prop36SW_of_ladderA_SESSION6.md`.  `PeluseLadderA` (`Holds/Corrected.lean`) quantifies
its coefficient functions as `p : ι → (Fin n → ℤ) → ℤ`, i.e. its parameter type is `Fin n → ℤ`, an
**infinite** type; its constants are chosen per datum `(n, k, kω, p, D)`.  The state of the §5 chain
must therefore be carried with parameter type `Fin n → ℤ` as well, with the long-direction *shift
values* stored in the coordinates: otherwise the datum of the `j`-th peel depends on the data
(`PeelData.PeelParam` mentions `M₁, M₂, A, γ'`), the ladder's constants become data-dependent, and
the data-independent `A, K` of `Prop36SW` cannot dominate them.

* `restr n t' x` — the first `n` coordinates (the old parameter);
* `shiftC n t' x i b` — the `2 t'` new coordinates (the `t'` shift pairs);
* `peelPFin p t' s₀` — the flat coefficient function (unchanged along the chain, data-independent);
* `peelGFin t' g` — the flat function family (`t'`-fold iterated difference along the shifts);
* `toFin` — the encoding of the nested `PeelParam` into the flat type;
* `shiftSetFin` — the parameter Finset of the flat state (the image of `univ` under `toFin`), which
  carries the constraints that `PeelParam` encoded in its *type*.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-- The long-direction window of the ladder's conclusion at `γ'`: `⌊γ' M₁ M₂⌋`. -/
def peelL (M₁ M₂ : ℕ) (γ' : ℝ) : ℕ := (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat

/-- The first `n` coordinates of a flat parameter: the old parameter. -/
def restr (n t' : ℕ) (x : Fin (n + 2 * t') → ℤ) : Fin n → ℤ := fun i => x (i.castAdd (2 * t'))

/-- The `i`-th shift coordinate of a flat parameter: `b = false` is the first, `b = true` the
second component of the `i`-th shift pair. -/
def shiftC (n t' : ℕ) (x : Fin (n + 2 * t') → ℤ) (i : Fin t') (b : Bool) : ℤ :=
  x ⟨n + 2 * (i : ℕ) + (if b then 1 else 0), by have := i.isLt; split <;> omega⟩

/-- **The flat coefficient function**: the old coefficient read at the old parameter, i.e. at the
first `n` coordinates.  On the chain this is a data-independent term. -/
def peelPFin {ι : Type} {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ) (t' : ℕ)
    (s₀ : Slot ι (fun _ => 1)) : PeelSlot s₀ → (Fin (n + 2 * t') → ℤ) → ℤ :=
  fun s x => p s.1.1 (restr n t' x)

/-- **The flat function family**: the `t'`-fold iterated difference along the stored shift values. -/
def peelGFin {n : ℕ} (t' : ℕ) (g : (Fin n → ℤ) → ℤ → ℂ) :
    (Fin (n + 2 * t') → ℤ) → ℤ → ℂ :=
  fun x => Ulower.iterDelta t' (fun i => (shiftC n t' x i false, shiftC n t' x i true))
    (g (restr n t' x))

/-- **The encoding of the nested parameter into the flat one**: the old parameter goes to the first
`n` coordinates, the `t'` shift *values* to the last `2 t'`. -/
def toFin {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ)
    (s₀ : Slot ι (fun _ => 1)) : PeelParam p M₁ M₂ A γ' t' s₀ → (Fin (n + 2 * t') → ℤ) :=
  fun q k =>
    if h : (k : ℕ) < n then q.1.1.1 ⟨k, h⟩
    else
      (if (k : ℕ) % 2 = 0 then
        ((q.2 ⟨((k : ℕ) - n) / 2, by have hk := k.isLt; omega⟩).1 : ℤ)
       else
        ((q.2 ⟨((k : ℕ) - n) / 2, by have hk := k.isLt; omega⟩).2 : ℤ))

/-- **The parameter Finset of the flat state**: the image of `univ` under `toFin`.  This carries the
constraints (old parameter in `A`, shifts in the long-direction set) that `PeelParam` encoded in its
type. -/
def shiftSetFin {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ)
    (s₀ : Slot ι (fun _ => 1)) : Finset (Fin (n + 2 * t') → ℤ) :=
  (Finset.univ : Finset (PeelParam p M₁ M₂ A γ' t' s₀)).image (toFin p M₁ M₂ A γ' t' s₀)

end

end Work.Peluse.Prop36SW
