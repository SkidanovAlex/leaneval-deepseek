/-
  WilC5 — quantifier elimination as a predicate on theories.

  This is the interface through which the residual content of area C5 (vdDMM Corollary 4.5, the
  quantifier elimination of the theory of the real exponential *with a symbol for the logarithm*)
  is meant to be attacked: `HasQE TElog` is a verbatim rendering of "`T_an(exp, log)` admits
  quantifier elimination", and it descends to the `LEc`-formula level
  (`Work.WilC5.Synthesis.DMM45_QE`) via the language map `LEc →ᴸ LElog` and
  `Work.WilC5.logStruct_model_TElog` (the definable expansion of a model of `TE` is a model of
  the log-theory, proved from `LogTranslation`).

  The companion `Saturation.lean` supplies `IsSaturated`, and `ExistsSaturated.lean` the
  existence of `κ`-saturated elementary extensions; those are the ingredients of the standard
  *quantifier elimination test* (vdDMM, §4, quoting [15]) which turns the embedding-extension
  property of Theorem 4.1 into quantifier elimination.
-/
import Mathlib.ModelTheory.Complexity

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

open FirstOrder Language

/-- **Quantifier elimination for a theory.**  Every formula is equivalent, over every model of
`T`, to a quantifier-free formula with the same free variables. -/
def HasQE {L : Language} (T : L.Theory) : Prop :=
  ∀ {n : ℕ} (φ : L.Formula (Fin n)), ∃ θ : L.Formula (Fin n), θ.IsQF ∧
    ∀ (M : Type) [L.Structure M], M ⊨ T → ∀ x : Fin n → M,
      Formula.Realize φ x ↔ Formula.Realize θ x

/-- A quantifier-free theory is one all of whose axioms are quantifier-free. -/
def IsQFAxiomatized {L : Language} (T : L.Theory) : Prop :=
  ∀ ⦃φ⦄, φ ∈ T → φ.IsQF

end Work.WilC5
