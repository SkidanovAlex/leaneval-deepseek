import Mathlib.Tactic.Have
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SmallBoxSliding.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The `dℓ`-scale cosine bump `chiSmall` is continuous for **every** `M`,
with no positivity hypothesis: `chiSmall M = chiSmallBase M / √(chiSmallNormSq M)`
is a continuous function divided by a constant, hence `chiSmallBase M`
multiplied by the constant `(√(chiSmallNormSq M))⁻¹`.  (The corpus lemma
`Submission.BoseGases.chiSmall_continuous` needs `1 ≤ M` only because it
proves the normalisation factor is nonzero; for continuity of the quotient
that is irrelevant, and the degenerate case `M = 0` — where the bump is
identically `0` — is covered by the same argument.) -/
lemma chiSmall_continuous_all (M : ℕ) :
    Continuous (fun z : ℝ³ => Submission.BoseGases.chiSmall M z) := by
  have hbase : Continuous (fun z : ℝ³ => Submission.BoseGases.chiSmallBase M z) :=
    Submission.BoseGases.chiSmallBase_continuous M
  have heq : (fun z : ℝ³ => Submission.BoseGases.chiSmall M z)
      = fun z => Submission.BoseGases.chiSmallBase M z *
          (Real.sqrt (Submission.BoseGases.chiSmallNormSq M))⁻¹ := by
    funext z; rw [Submission.BoseGases.chiSmall, div_eq_mul_inv]
  rw [heq]
  exact hbase.mul continuous_const

/-- Joint continuity of the two-factor small-box cutoff
`χ_{B(u)}(x) = χ_M(x/ℓ)·χ_M(x/(ℓd) − u)` in the pair `(u, x)` (here only the
`i`-th particle coordinate `x i` of `X N` is used): a product of two
compositions of the continuous bump `chiSmall M` with the continuous affine
maps `x ↦ ℓ⁻¹ • x` and `(u, x) ↦ (ℓd)⁻¹ • x − u`. No hypothesis on `M`, `ℓ`
or `d` is needed. -/
theorem chiSmallB_continuous_joint {N : ℕ} (M : ℕ) (ℓ d : ℝ) (i : Fin N) :
    Continuous (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
      Submission.BoseGases.chiSmallB M ℓ d p.1 (p.2 i)) := by
  have hchi : Continuous (fun z : ℝ³ => Submission.BoseGases.chiSmall M z) :=
    chiSmall_continuous_all M
  have hx : Continuous (fun p : ℝ³ × Submission.BoseGases.X N => p.2 i) :=
    (continuous_apply i).comp continuous_snd
  have h1 : Continuous (fun p : ℝ³ × Submission.BoseGases.X N =>
      Submission.BoseGases.chiScale ℓ (p.2 i)) :=
    (Submission.BoseGases.chiScale_continuous ℓ).comp hx
  have h2 : Continuous (fun p : ℝ³ × Submission.BoseGases.X N =>
      Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (p.2 i) - p.1)) :=
    hchi.comp ((hx.const_smul ((ℓ * d)⁻¹)).sub continuous_fst)
  have heq : (fun p : ℝ³ × Submission.BoseGases.X N =>
        Submission.BoseGases.chiSmallB M ℓ d p.1 (p.2 i))
      = fun p => Submission.BoseGases.chiScale ℓ (p.2 i) *
          Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (p.2 i) - p.1) := by
    funext p; rfl
  rw [heq]
  exact h1.mul h2

end Work.SmallBoxSliding
