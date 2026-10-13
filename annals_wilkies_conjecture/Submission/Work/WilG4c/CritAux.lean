/-
  WilG4c / `CritAux` — the auxiliary vocabulary for `Work.WilkG4c.CritMem`, the
  `Ω`-definability of the punctured-limit criterion `Crit` of `AlSliceBase`.

  `Crit p n f L = LocCrit p n f L ∩ {z | z ∈ LimeqP p n (dgSet p n f L.length L.get)}`.
  The second conjunct is a `LimeqP` (`fibreLimitEqMem_pi`), while `LocCrit p n f L` asks for a
  whole *cube-ball* around `Fin.init z` to lie in `UV p n f L.length`.  The ball-condensation
  is isolated here as `HypoRaw`: the set of points `u` such that some cube-ball around `u`
  (with the parameter fixed) is contained in `X`.

  The identification `LocCrit p n f L = {z | Fin.init z ∈ HypoRaw p n (UV p n f L.length)}`
  is definitional (`locCrit_eq`).
-/
import Mathlib
import Submission.Work.WilG4c.AlSliceBase

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- **Ball condensation.**  `u ∈ HypoRaw p n X` iff some cube-ball around `u`, keeping the
parameter `parPt u` fixed, is contained in `X`:
`∃ ρ > 0, ∀ w', parPt w' = parPt u → dist (cubePt w') (cubePt u) < ρ → w' ∈ X`. -/
def HypoRaw (p n : ℕ) (X : Set (Fin (p + (n + 1)) → ℝ)) : Set (Fin (p + (n + 1)) → ℝ) :=
  {u | ∃ ρ : ℝ, 0 < ρ ∧ ∀ w' : Fin (p + (n + 1)) → ℝ,
    parPt w' = parPt u → dist (cubePt w') (cubePt u) < ρ → w' ∈ X}

@[simp] theorem mem_HypoRaw {p n : ℕ} {X : Set (Fin (p + (n + 1)) → ℝ)}
    {u : Fin (p + (n + 1)) → ℝ} :
    u ∈ HypoRaw p n X ↔ ∃ ρ : ℝ, 0 < ρ ∧ ∀ w' : Fin (p + (n + 1)) → ℝ,
      parPt w' = parPt u → dist (cubePt w') (cubePt u) < ρ → w' ∈ X :=
  Iff.rfl

/-- `LocCrit` is the product of `HypoRaw (UV …)` with a free last coordinate. -/
theorem locCrit_eq (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (n + 1))) :
    LocCrit p n f L
      = {z : Fin (p + (n + 1) + 1) → ℝ | Fin.init z ∈ HypoRaw p n (UV p n f L.length)} :=
  rfl

/-- `Crit` is the intersection of that product with the `LimeqP` of the joint derivative graph
along `L`. -/
theorem crit_eq (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (n + 1))) :
    Crit p n f L
      = {z : Fin (p + (n + 1) + 1) → ℝ | Fin.init z ∈ HypoRaw p n (UV p n f L.length)}
        ∩ Work.WilG4c.LimeqP p n (dgSet p n f L.length (fun j => L.get j)) :=
  rfl

end Work.WilkG4c
