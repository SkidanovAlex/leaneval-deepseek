import Mathlib
import Submission.Work.Peluse.Basic

/-!
# The iterated `Δ'`-difference and Peluse's `□_s(H)`

These are the two definitions of the degree-lowering chapter (Peluse, §7–8, the case `ℓ = m = 2`);
they live in their own module so that the many helper modules about them can be imported by the
main degree-lowering statement without an import cycle.

* `iterDelta' t sh F` is the `t`-fold iterated difference `Δ'_{(sh 0)} ⋯ Δ'_{(sh (t-1))} F`, i.e.
  the function whose cube-term is `Work.Peluse.cubeTerm`.  It is the `Δ'_{(k_i^{(2)},k_i^{(3)})}` of
  Peluse's Lemma 7.4, and it appears in the dual functions `G_{ℓ,k}` of that lemma.
* `ThetaSet s D H` is Peluse's `□_s(H)`: the set of triples `(k⁽¹⁾, k⁽²⁾, k⁽³⁾)` with all `3s`
  coordinates in `[1,D]` and `(k⁽¹⁾, ω·k⁽²⁾ + (1-ω)·k⁽³⁾) ∈ H` for every `ω : Fin s → Bool`.
-/

namespace Work.Peluse.Ulower

noncomputable section

/-- The `t`-fold iterated `Δ'`-difference with shift pairs `sh`:
`iterDelta' 0 _ F = F` and
`iterDelta' (t+1) sh F x = iterDelta' t sh.tail F (x + (sh 0).1) * conj (iterDelta' t sh.tail F (x + (sh 0).2))`. -/
def iterDelta' : (t : ℕ) → (Fin t → ℤ × ℤ) → (ℤ → ℂ) → ℤ → ℂ
  | 0, _, F => F
  | t + 1, sh, F => fun x =>
      star (iterDelta' t (fun i => sh i.succ) F (x + (sh 0).1)) *
        iterDelta' t (fun i => sh i.succ) F (x + (sh 0).2)

/-- Peluse's `□_s(H)` (the `3s`-tuples of Peluse's Lemma 7.4). -/
def ThetaSet (s D : ℕ) (H : Finset ((Fin s → ℤ) × (Fin s → ℤ))) :
    Finset ((Fin s → ℤ) × (Fin s → ℤ) × (Fin s → ℤ)) :=
  ((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).product
    ((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).product
      (Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))))).filter
    (fun k => ∀ ω : Fin s → Bool,
      ((k.1, fun i => if ω i then k.2.1 i else k.2.2 i) ∈ H))

end

end Work.Peluse.Ulower
