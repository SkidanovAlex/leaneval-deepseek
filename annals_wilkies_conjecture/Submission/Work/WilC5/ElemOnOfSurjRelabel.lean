import Mathlib

namespace Work.WilC5

theorem ElemOnOfSurjRelabel {L : FirstOrder.Language.{0,0}} {M N : Type}
    [L.Structure M] [L.Structure N]
    {β γ : Type} (iA : β → M) (jA : β → N) (iP : γ → M) (jP : γ → N) (s : β → γ)
    (hs : Function.Surjective s) (hi : iP ∘ s = iA) (hj : jP ∘ s = jA)
    (H : ∀ φ : L.Formula β, φ.Realize iA ↔ φ.Realize jA) :
    ∀ φ : L.Formula γ, φ.Realize iP ↔ φ.Realize jP := by
  -- Every γ-indexed variable is the image under `s` of some β-indexed variable; pick a
  -- section `t` of `s` and relabel the formula along it.
  intro φ
  classical
  choose t ht using hs
  have hst : s ∘ t = id := funext ht
  have hi' : iA ∘ t = iP := by
    rw [← hi, Function.comp_assoc, hst, Function.comp_id]
  have hj' : jA ∘ t = jP := by
    rw [← hj, Function.comp_assoc, hst, Function.comp_id]
  -- Realizing the relabelled formula against `iA` is realizing `φ` against `iA ∘ t = iP`.
  have h1 : (φ.relabel t).Realize iA ↔ φ.Realize iP := by
    rw [FirstOrder.Language.Formula.realize_relabel, hi']
  have h2 : (φ.relabel t).Realize jA ↔ φ.Realize jP := by
    rw [FirstOrder.Language.Formula.realize_relabel, hj']
  exact h1.symm.trans ((H (φ.relabel t)).trans h2)

end Work.WilC5
