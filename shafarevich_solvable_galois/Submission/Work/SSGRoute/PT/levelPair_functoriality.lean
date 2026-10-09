import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PT.pt_pairing_ext
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Basic functoriality of the level pairing `levelPair`

Support file for the degree-`0`/`2` local Tate duality over the **full** decomposition group
`D_A = decomp k A` (the target `Work.SSGRoute.PT.localTatePairing_deg02` and its base case
`Work.SSGRoute.PT.localTatePairing_deg02_triv`).  `SSGRoute.PTExt.levelPair f ι x h` is the Yoneda
product of `Extʳ_G(M, A)` with `Hˢ(H, res_f M)` pushed into `H^{s+r}(H, B)`; here we record that it
is additive and trivial on the zero class in each variable — the "basic functoriality" every
consumer of the pairing calculus needs — and that `Ext⁰ = Hom`.  (The *level-wise* form of the
local pairing, `DESIGN_EXT`'s E7b, is refuted; see `PT/localTatePairing_deg02.lean`.)
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- The level pairing is additive in the `Ext` variable. -/
theorem levelPair_add {G H : Type} [Group G] [Group H] (f : H →* G)
    {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B) {r s : ℕ}
    (x x' : Abelian.Ext.{0} M A r) (h : extH (Rep.res f M) s) :
    levelPair f ι (x + x') h = levelPair f ι x h + levelPair f ι x' h := by
  simp only [levelPair]
  rw [extRes_add, Abelian.Ext.add_comp, Abelian.Ext.comp_add]

/-- The level pairing kills the zero `Ext` class. -/
theorem levelPair_zero {G H : Type} [Group G] [Group H] (f : H →* G)
    {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B) {r s : ℕ}
    (h : extH (Rep.res f M) s) :
    levelPair f ι (0 : Abelian.Ext.{0} M A r) h = 0 := by
  simp only [levelPair]
  rw [extRes_zero, Abelian.Ext.zero_comp, Abelian.Ext.comp_zero]

/-- The level pairing is additive in the `Hˢ` variable. -/
theorem levelPair_add_h {G H : Type} [Group G] [Group H] (f : H →* G)
    {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B) {r s : ℕ}
    (x : Abelian.Ext.{0} M A r) (h h' : extH (Rep.res f M) s) :
    levelPair f ι x (h + h') = levelPair f ι x h + levelPair f ι x h' := by
  simp only [levelPair]
  rw [Abelian.Ext.add_comp]

/-- The level pairing kills the zero `Hˢ` class. -/
theorem levelPair_zero_h {G H : Type} [Group G] [Group H] (f : H →* G)
    {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B) {r s : ℕ}
    (x : Abelian.Ext.{0} M A r) :
    levelPair f ι x (0 : extH (Rep.res f M) s) = 0 := by
  simp only [levelPair]
  rw [Abelian.Ext.zero_comp]

/-- `Ext⁰_G(M, A)` is `Hom_G(M, A)` (`mk₀` is a bijection); used whenever a pairing at `r = 0` is
analysed. -/
theorem extZeroEquivHom {G : Type} [Group G] (M A : Rep.{0} Coeff G) :
    Nonempty (Abelian.Ext.{0} M A 0 ≃ (M ⟶ A)) :=
  ⟨(Equiv.ofBijective Abelian.Ext.mk₀ (Abelian.Ext.mk₀_bijective M A)).symm⟩

end Work.SSGRoute
