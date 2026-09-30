import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SpecLin.Alt

-- First elementary piece of the affine-chart computation
-- `val_𝔫(ρ(h)) = #{m : 𝔫 = I_m + P} − #{m : 𝔫 = J_m + P}` to which (C4) is reduced
-- (see `DECIDED (10)` in `Alt/NOTES_chartCore.md`): the transversality bookkeeping.
-- `P = 𝔪_R·B` is the prime of the generic point of the special fibre, `𝔫 ⊇ P` a maximal ideal
-- (a closed point of the special fibre's chart), and `I ⊔ P` is the ideal of the point where the
-- section meets the special fibre; `I ⊔ P` maximal together with `I ≤ 𝔫` forces `I ⊔ P = 𝔫`.
-- Consequence used downstream: `ρ(f)` for `f ∈ I` generates the maximal ideal of the local ring
-- of `B/P` at `𝔫/P`, i.e. `val_𝔫(ρ(f)) = 1` — so a section equation contributes exactly `1` at
-- the point `𝔫` and `0` elsewhere.  No normality is involved.
theorem sup_eq_of_le_maximal {B : Type*} [CommRing B] {I P 𝔫 : Ideal B} [𝔫.IsMaximal]
    (hP : P ≤ 𝔫) (hI : I ≤ 𝔫) (hmax : (I ⊔ P).IsMaximal) : I ⊔ P = 𝔫 := by
  exact Ideal.IsMaximal.eq_of_le hmax (Ideal.IsMaximal.ne_top ‹𝔫.IsMaximal›) (sup_le hI hP)

end Work.SpecLin.Alt
