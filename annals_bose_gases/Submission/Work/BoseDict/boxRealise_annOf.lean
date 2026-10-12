import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseDict.boxRealise_annOf_annOf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDict.boxRealise_annOf` — the box ↔ model dictionary for a superposed annihilation

With `boxRealise e d` the realisation of the model monomials `x^α` of degree `d` on the box
(`x^α ↦ (α!/√(d!)) • M_α`, `M_α = modeProd e d α`) and `boxAnnOf e w d` the box annihilation
of the superposition `η_w = Σ_l w_l e_l`, the intertwining identity

    boxRealise e d (annOf m w Ψ) = boxAnnOf e w d (boxRealise e (d+1) Ψ)

holds for every model vector `Ψ` carried by degree `d+1` (`annOf m w = Σ_l w_l · ann m l`
is the superposed model annihilation).  This is the superposition form of the mode-wise
identity `Work.BoseDict.boxRealise_ann`
(`boxRealise e d (ann m l Ψ) = boxAnn e l d (boxRealise e (d+1) Ψ)`), which the rows of the
model Hamiltonian (`Work.BoseB4.H2ndF`) require.

## Proof

The superposition statement is the lemma `Work.BoseDict.boxRealise_annOf'` of the module
`Work.BoseDict.boxRealise_annOf_annOf` (proved there as the first half of the double
superposition identity used for the rows containing a *product* of two annihilations).  Its
proof, recorded there, is the assembly of the three pieces of the dictionary:

* `Work.BoseDict.boxRealise_ann` — the mode-wise intertwining;
* `Work.BoseDict.integrable_conj_boxRealise` — integrability of `z ↦ conj(e l z)·Θ(z,y)`,
  which justifies commuting the finite sum `Σ_l w_l` with the integral;
* `Work.BoseDict.boxAnnOf_eq_sum` — `boxAnnOf e w d Θ = Σ_l w_l • boxAnn e l d Θ`.

Since the statement below is *verbatim* that of `boxRealise_annOf'`, this module simply
exposes it under the name the requester builds on.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseDict

theorem boxRealise_annOf {m d : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (he : ∀ l l', (∫ x : Work.BoseDict.Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) (Ψ : Work.BoseB4.RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 1) :
    Work.BoseDict.boxRealise e d (Work.BoseB4.annOf m w Ψ)
      = Work.BoseDict.boxAnnOf e w d (Work.BoseDict.boxRealise e (d + 1) Ψ) :=
  boxRealise_annOf' he hbdd hsupp w Ψ hΨ

end Work.BoseDict
