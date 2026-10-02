import Mathlib
import Submission.Work.Top.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The "cross box" in the parameter plane is open

For Böttcher data `hN : NakaneData Mb Φ` and reals `θ R a b`, the set

```
{c : ℂ | c ∉ Mb ∧ |(rayRot θ (Φ c)).re - R| < a ∧ |(rayRot θ (Φ c)).im| < b}
```

-- the points off the connectedness locus whose rotated Böttcher coordinate lies in the open
rectangle `|Re w - R| < a`, `|Im w| < b` around the point `R` of the real axis -- is open in `ℂ`.

The point is that `Φ` is *not* assumed to be continuous on `ℂ` (only off `Mb`, where it agrees
with the homeomorphism `hN.e`), so openness cannot be read off from a globally continuous `Φ`.
Instead we use that `Mbᶜ` is open and that `Φ` restricts to a continuous map `Mbᶜ → ℂ`; the
`Subtype.val` image of an open subset of the open set `Mbᶜ` is again open (`IsOpenMap` of the
inclusion of an open set).
-/

open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.Top

/-- The open rectangle `{w | |w.re - R| < a ∧ |w.im| < b}` is open in `ℂ`. -/
private theorem isOpen_reImBox (R a b : ℝ) :
    IsOpen {w : ℂ | |w.re - R| < a ∧ |w.im| < b} := by
  have h1 : IsOpen {w : ℂ | |w.re - R| < a} :=
    isOpen_lt (continuous_abs.comp (Complex.continuous_re.sub continuous_const)) continuous_const
  have h2 : IsOpen {w : ℂ | |w.im| < b} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  exact h1.inter h2

theorem isOpen_crossBox {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) (θ R a b : ℝ) :
    IsOpen {c : ℂ | c ∉ Mb ∧ |(Work.Top.rayRot θ (Φ c)).re - R| < a ∧
      |(Work.Top.rayRot θ (Φ c)).im| < b} := by
  -- the target rectangle is open
  have hbox : IsOpen {w : ℂ | |w.re - R| < a ∧ |w.im| < b} := isOpen_reImBox R a b
  -- rotation is continuous
  have hray : Continuous (rayRot θ) := continuous_id.mul continuous_const
  -- `Φ` is continuous on `Mbᶜ`, since there it agrees with the homeomorphism `hN.e`
  have hG : Continuous (fun c : ↥Mbᶜ => rayRot θ (Φ (c : ℂ))) := by
    have h1 : Continuous (fun c : ↥Mbᶜ => ((hN.e c : ↥exteriorDisc) : ℂ)) :=
      continuous_subtype_val.comp hN.e.continuous
    have h2 : Continuous (fun c : ↥Mbᶜ => Φ (c : ℂ)) :=
      h1.congr (fun c => (hN.he c).symm)
    exact hray.comp h2
  -- the preimage in the subtype `Mbᶜ` is open
  have hpre : IsOpen ((fun c : ↥Mbᶜ => rayRot θ (Φ (c : ℂ))) ⁻¹'
      {w : ℂ | |w.re - R| < a ∧ |w.im| < b}) := hbox.preimage hG
  -- `Mbᶜ` is open, so the inclusion `Mbᶜ ↪ ℂ` is an open map
  have hmc : IsOpen (Mbᶜ) := hN.isClosed_mb.isOpen_compl
  have himg := hmc.isOpenMap_subtype_val _ hpre
  -- and the set of the statement is exactly that image
  have hS : {c : ℂ | c ∉ Mb ∧ |(rayRot θ (Φ c)).re - R| < a ∧ |(rayRot θ (Φ c)).im| < b}
      = Subtype.val '' ((fun c : ↥Mbᶜ => rayRot θ (Φ (c : ℂ))) ⁻¹'
          {w : ℂ | |w.re - R| < a ∧ |w.im| < b}) := by
    ext c
    constructor
    · rintro ⟨hc, h1, h2⟩
      exact ⟨⟨c, hc⟩, ⟨h1, h2⟩, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨d.2, hd.1, hd.2⟩
  rw [hS]
  exact himg

end Work.Top
