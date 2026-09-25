import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.TowerSymbol
import Submission.NK.LocalReciprocityLubinTate.Basic

/-!
# The Lubin–Tate symbol tower together with its Lubin–Tate levels

`NK.LocalReciprocityLubinTate.LubinTateSymbolTower` records the levels `E_{m,n}`, their norm groups
`⟨π^{a m}⟩ · U^{n+1}`, and the canonical Artin symbols with those kernels, compatibly.  Classically each
level is the compositum `E_{m,n} = E^{ur}_{a m} · F(Λ_{π^{n+1}})`, and the Artin symbol is the product of
the unramified symbol (Frobenius) with the Lubin–Tate symbol of
`NK.LocalReciprocityLubinTate.LubinTate.exists_ltSymbol_family`.

This file isolates the part of that structure which is *needed to split the residue*
`NK.LocalReciprocityLubinTate.NormInKernel` into an unramified part and a Lubin–Tate part:

* the Lubin–Tate levels `ltLevel n = F(Λ_{π^n})` inside the tower levels;
* the Lubin–Tate symbols `ltSymbol n : Fˣ →* Gal(ltLevel n / F)`, with the Honda kernel
  `⟨π⟩ ⊔ U^n` (`NK.LocalReciprocityLubinTate.Unramified.hondaReciprocity`);
* the identity `symbol m n x |_{ltLevel (n+1)} = ltSymbol (n+1) x`.

With these, `NormInKernel` at a subfield `L ≤ E_{m,n}` reduces to: (i) the Frobenius component of the
symbol kills `N_{L/F} Lˣ`, which is a valuation statement about norms (`f | v(x)` for `x = N_{L/F} y`,
with `f` the inertia degree), and (ii) `ltSymbol (n+1)` kills `N_{L/F} Lˣ`, i.e. `NormInKernel` for the
*pure* Lubin–Tate level `F(Λ_{n+1})` — which is a *theorem* whenever `Gal(F(Λ_{n+1})/F)` is cyclic
(`NK.LocalReciprocityLubinTate.normGroup_map_eq_of_isCyclic`), e.g. for `F = ℚ_[p]` with `p` odd.

## Main definition

* `NK.LocalReciprocityLubinTate.LubinTateSymbolTowerWithLT`.
-/

open scoped Classical

namespace NK.LocalReciprocityLubinTate

universe u v

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- **A Lubin–Tate symbol tower together with its Lubin–Tate levels and symbols.**

This extends `NK.LocalReciprocityLubinTate.LubinTateSymbolTower` by the fields witnessing that each
symbol is the product of the unramified symbol and the canonical Lubin–Tate symbol at level `n+1`:
the Lubin–Tate levels `ltLevel`, the symbols `ltSymbol` with the Honda kernels, and the restriction
identity `symbol m n x |_{ltLevel (n+1)} = ltSymbol (n+1) x`. -/
structure LubinTateSymbolTowerWithLT (F : Type u) (F' : Type v) [Field F] [Field F']
    [Algebra F F'] [IsGalois F F'] (π : Fˣ) (a : ℕ → ℕ) (U : ℕ → Subgroup Fˣ) (q : ℕ)
    extends LubinTateSymbolTower F F' π a U q where
  /-- the Lubin–Tate level `F(Λ_{π^n})` inside the ambient maximal abelian extension. -/
  ltLevel : ℕ → IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F')
  /-- the canonical Lubin–Tate symbol at the level `F(Λ_{π^n})`. -/
  ltSymbol : ∀ n : ℕ, Fˣ →* (↥(ltLevel n) ≃ₐ[F] ↥(ltLevel n))
  /-- the Lubin–Tate level `F(Λ_{π^{n+1}})` is contained in every tower level `E_{m,n}`. -/
  ltLevel_le : ∀ m n : ℕ, ltLevel (n + 1) ≤ level m n
  /-- **Honda's reciprocity law**: the kernel of the Lubin–Tate symbol at level `n` is
  `⟨π⟩ · U^n`. -/
  ltSymbol_ker : ∀ n : ℕ, 1 ≤ n → MonoidHom.ker (ltSymbol n) = Subgroup.zpowers π ⊔ U n
  /-- the tower symbol restricts to the Lubin–Tate symbol on the Lubin–Tate level. -/
  symbol_apply_lt : ∀ (m n : ℕ) (x : Fˣ) (y : ↥(ltLevel (n + 1))),
    (((symbol m n x) ⟨y.1, ltLevel_le m n y.2⟩ : ↥(level m n)) : F') =
      (((ltSymbol (n + 1) x) y : ↥(ltLevel (n + 1))) : F')

end NK.LocalReciprocityLubinTate
