import Mathlib
import Submission.Work.Pi6.HALG.defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.HALG

open CategoryTheory

/-- A `ℤ`-module of cardinality `2` is `ℤ/2`; hence both `M/2M` and `M[2]` have `2` elements.

`twoKer M = M[2] = ker (x ↦ 2 • x)` and `twoCok M = M/2M = M ⧸ range (x ↦ 2 • x)` are the
`ModuleCat ℤ` objects of `Submission/Work/Pi6/HALG/defs.lean`. Route: `Nat.card ↥M = 2` gives
`Finite ↥M`, hence `2 • x = 0` for all `x` (`card_nsmul_eq_zero'`, after `Nat.card_ne_zero` +
`Nat.card_pos_iff` to get `Finite` and `Nonempty`); so `mulTwo M` is the zero map, `LinearMap.range`
is `⊥` and `LinearMap.ker` is `⊤`. Then `Nat.card ↥(twoKer M) = Nat.card ↥M` (a top submodule is the
whole module, `Submodule.topEquiv`) and `Nat.card ↥(twoCok M) = Nat.card ↥M` (quotient by `⊥`, e.g.
`Submodule.quotEquivOfEqBot` / the quotient map with trivial kernel). -/
theorem twoCok_twoKer_card_two {M : ModuleCat ℤ} (hM : Nat.card ↥M = 2) :
    Nat.card ↥(twoCok M) = 2 ∧ Nat.card ↥(twoKer M) = 2 := by
  -- An abelian group of order `2` has exponent `2`: every element satisfies `x + x = 0`.
  have hxx : ∀ x : ↥M, x + x = 0 := by
    intro x
    have hdvd : addOrderOf x ∣ 2 := by rw [← hM]; exact addOrderOf_dvd_natCard x
    have h2 : 2 • x = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp hdvd
    rwa [two_nsmul] at h2
  -- `mulTwo M` is `x ↦ x + x` (`mulTwo M = 2 • 𝟙 M`, and the scalar action on morphisms of
  -- `ModuleCat ℤ` is pointwise), hence the zero map.
  have hmulTwo_add : ∀ x : ↥M, (mulTwo M).hom x = x + x := by
    intro x
    show ((2 : ℤ) • 𝟙 M).hom x = x + x
    rw [show (2 : ℤ) • (𝟙 M : M ⟶ M) = 𝟙 M + 𝟙 M from two_zsmul _]
    simp
  have hzero : (mulTwo M).hom = 0 :=
    LinearMap.ext fun x => by rw [hmulTwo_add, hxx x, LinearMap.zero_apply]
  have hker : LinearMap.ker (mulTwo M).hom = ⊤ := LinearMap.ker_eq_top.mpr hzero
  have hrange : LinearMap.range (mulTwo M).hom = ⊥ := LinearMap.range_eq_bot.mpr hzero
  constructor
  -- `M/2M = M ⧸ ⊥ ≃ M`
  · change Nat.card (↥M ⧸ LinearMap.range (mulTwo M).hom) = 2
    rw [hrange]
    exact (Nat.card_congr (Submodule.quotEquivOfEqBot (⊥ : Submodule ℤ ↥M) rfl).toEquiv).trans hM
  -- `M[2] = ⊤ ≃ M`
  · change Nat.card ↥(LinearMap.ker (mulTwo M).hom) = 2
    rw [hker]
    exact (Nat.card_congr (Submodule.topEquiv (R := ℤ) (M := ↥M)).toEquiv).trans hM

end Work.Pi6.HALG
