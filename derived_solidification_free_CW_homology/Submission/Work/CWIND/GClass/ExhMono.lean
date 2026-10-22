import Submission.Work.CWIND.GClass.ExhSetup
import Submission.Work.CWIND.GClass.mono_AFunctor_map_incl

/-!
# CWIND/T9 — the transition maps of the exhaustion are monomorphisms

`homOfLE (Nat.le_succ n) : n ⟶ n + 1` in the category `ℕ` is sent by `exhTop` to the inclusion
`A n ⊆ A (n+1)`; the induced maps of singular chains and of the `A`-complexes are monomorphisms by
`mono_Cfun_map_incl` and `mono_AFunctor_map_incl` (file `mono_AFunctor_map_incl`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint

namespace Work.CWIND.GClass

open Work.CWIND

/-- **CWIND/T9, monomorphicity of the exhaustion maps.** -/
theorem ExhMono {X : TopCat.{0}} (A : ℕ → Set X) (hmono : Monotone A) :
    (∀ n, Mono ((CsingExh A hmono).map (homOfLE (Nat.le_succ n)))) ∧
      (∀ n, Mono ((Aexh A hmono).map (homOfLE (Nat.le_succ n)))) := by
  constructor
  · intro n
    exact mono_Cfun_map_incl (hmono (Nat.le_succ n))
  · intro n
    exact mono_AFunctor_map_incl (hmono (Nat.le_succ n))

end Work.CWIND.GClass
