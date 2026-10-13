import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ZTrunc
import Submission.Work.FTS_RegExport.RXR5.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux

/-- **The `N`-block is unchanged by the truncation on the open quadrant.**

`ztrunc w` and `w` agree on the whole half-plane `z > 0`, which is an open neighbourhood of every
point of `Qd = Ioi 0 ×ˢ Ioo 0 (π/2)`.  `N α (Ftot α w) Φ` is built from `F = Ftot α w` and its
first derivatives (`pz`, `pth`, `Dz`) — germ-local, hence equal — and from the two nonlocal
quantities `L12 F z` (an `s`-integral over `s > z ≥ 0`) and `FK F z` (a `θ`-integral at fixed
`z > 0`), which are unchanged because `ztrunc w = w` on `Ioi 0`.  The `Φ`-argument is the same on
both sides.

Useful lemmas: `Construction.L12AddFstar`, `FTS_RegExport.RXR5.L12_congr_of_agreeOnQ`,
`RXR5.FK_congr_of_agreeOnQ`, `GalFields.RHS.L12f_congr_of_agreeOnQ`, plus the open-strip
congruences for `pz`/`pth`/`Dz` (`Spaces.pz_congr_of_isOpen`, `Spaces.Dz_congr_of_isOpen`,
`Spaces.DthIter_DzIter_eqOn_of_isOpen`-style) and the `PhiTil`/`Rop`/`Uop`/`Vop` unfolding.

The whole bundle of those congruences is already assembled in
`Work.FTS_RegExport.RXR5.Basic` as `RXR5.N_congr_of_agreeOnQ`: for two pairs `(F, Φ)`, `(F', Φ')`
that agree on the open quadrant, `N α F Φ = N α F' Φ'` there.  Hence it suffices to know that
`Ftot α (ztrunc w)` and `Ftot α w` agree on `Qd` (they do, since `Fstar α` is common and
`ztrunc w = w` for `z > 0`) and that the `Φ`-argument is literally the same on both sides. -/
theorem N_ztrunc_agree {α : ℝ} {Φs w Φg : Work.FTS.Galerkin.Fn} :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (Work.Construction.Ftot α
          (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ztrunc w))
          (fun z θ => Φs z θ + Φg z θ) z θ
        = Work.Construction.N α (Work.Construction.Ftot α w)
          (fun z θ => Φs z θ + Φg z θ) z θ := by
  intro z θ hzθ
  obtain ⟨hz, hθ, hθ2⟩ := hzθ
  exact Work.FTS_RegExport.RXR5.N_congr_of_agreeOnQ
    (F := Work.Construction.Ftot α (ztrunc w))
    (F' := Work.Construction.Ftot α w)
    (Φ := fun z θ => Φs z θ + Φg z θ)
    (Φ' := fun z θ => Φs z θ + Φg z θ)
    (fun z θ hz' _ _ => by
      show Work.Construction.Fstar α z θ + ztrunc w z θ
          = Work.Construction.Fstar α z θ + w z θ
      rw [ztrunc_of_pos hz'])
    (fun _ _ _ _ _ => rfl) hz hθ hθ2

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux
