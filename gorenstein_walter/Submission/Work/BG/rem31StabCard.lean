import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.s02_lemma21Ext

/-!
# Area BG: Remark 3.1 — the orbit–stabiliser count `|Λ_ν| · |Λν| = |H₀ : U|`

Bender–Glauberman (J. Algebra 70 (1981), Remark 3.1) need, for `ν ∈ Irr(H₀)`, the number of
`λ ∈ Λ` with `λν = ν` (their `|Λ_ν|`): it is `|H₀ : U| / |Λν|`, because `Λ` is a group of
order `|H₀ : U|` acting on the class functions of `H₀` with `Λν` as the orbit of `ν`.

Nothing about `ν` is used beyond `Λ` being a finite group: the identity is plain
orbit–stabiliser for the `Λ`-action `β • μ = λ_β · μ` of `Submission/Work/BG/s02_lamDual.lean`
together with the count `|Λ| = |Hom(H₀/U, ℂˣ)| = |H₀/U|` of the dual of a finite abelian group
(`CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`, which applies because `H₀/U` is cyclic
by `Sec2Ctx.quot_cyclic`, hence commutative — `Work.BG.mul_comm_quotGroup`).

Main results:

* `Work.BG.rem31LamDualCard` — `Nat.card (lamDual C) = (Uin C).index`;
* `Work.BG.rem31OrbitMulStab` — orbit–stabiliser in `Nat.card` form;
* `Work.BG.rem31StabCard` — the requested count.
-/

set_option linter.style.haveILetI false

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-- **The dual group has the order of `H₀/U`:** `|Λ| = |Hom(H₀/U, ℂˣ)| = |H₀/U| = |H₀ : U|`.
The quotient `H₀/U` is cyclic (`Sec2Ctx.quot_cyclic`), hence commutative, so the self-duality
of finite abelian groups applies with enough roots of unity in `ℂ`. -/
theorem rem31LamDualCard (C : Sec2Ctx G) :
    Nat.card (lamDual C) = (Work.GW2.C16.Uin C).index := by
  have hcomm : ∀ a b : quotGroup C.P, a * b = b * a :=
    fun a b => mul_comm_quotGroup C a b
  letI : CommGroup (quotGroup C.P) :=
    { (inferInstance : Group (quotGroup C.P)) with mul_comm := hcomm }
  haveI : Finite (quotGroup C.P) := inferInstance
  rw [Subgroup.index_eq_card]
  exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (quotGroup C.P) ℂ

/-- **Orbit–stabiliser for the `Λ`-action**: `|Λ_ν| · |Λν| = |Λ|`.  The explicit bijection
`Λ_ν × Λν ≃ Λ` of `MulAction.orbitProdStabilizerEquivGroup` is transported along `Nat.card`,
so no finiteness hypothesis is needed. -/
theorem rem31OrbitMulStab (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) :
    Nat.card ↥(lamStab C ν) * Nat.card ↥(MulAction.orbit (lamDual C) ν)
      = Nat.card (lamDual C) := by
  rw [lamStab, ← Nat.card_prod]
  exact Nat.card_congr ((Equiv.prodComm _ _).trans
    (MulAction.orbitProdStabilizerEquivGroup (lamDual C) ν))

theorem rem31StabCard {G : Type} [Group G] [Finite G] (C : Work.BG.Sec2Ctx G)
    (ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) :
    Nat.card ↥(Work.BG.lamStab C ν) * (Work.BG.lamOrbit C ν).ncard
      = (Work.GW2.C16.Uin C).index := by
  rw [← rem31LamDualCard C, ← rem31OrbitMulStab C ν, ← Nat.card_coe_set_eq, orbit_eq_lamOrbit]

end Work.BG
