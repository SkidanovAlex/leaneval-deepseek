import Mathlib
import Submission.Work.BG.Defs
import Submission.Work.BG.CharBridge
import Submission.Work.BG.Lambda
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.lambda_mul_mem
import Submission.OddOrder.GroupTheory.RepresentationTheory.CharacterProduct

/-!
# Area BG: shared vocabulary for Bender–Glauberman Lemma 1.7(ii)

This module collects the small definitions and product lemmas needed both by
`Submission.Work.BG.lemma17_ii` and by the lemmas delegated about it.

* `Work.BG.lambdaInf P β` — the inflation `Inf(β)` of a linear character
  `β : H₀/U →* ℂˣ` to a class function on `H₀` (so `Lambda P = Set.range (lambdaInf P)`);
* `Work.BG.orbitMap P rep hirr` — the parameterisation
  `(β, μ) ↦ Inf(β)·μ` of `Irr(H₀)` by `(H₀/U)^ * × rep`, where `rep` is a transversal
  of the `Λ`-orbits.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-- `Inf(β)`: the inflation to `H₀` of the linear character `β` of `H₀/U`. -/
noncomputable def lambdaInf (P : Hyp12 G) [(P.U.subgroupOf P.H0).Normal]
    (β : quotGroup P →* ℂˣ) : ClassFunction ↥P.H0 ℂ :=
  ClassFunction.compHom (quotMk P) (linearClassFunction β)

@[simp] theorem lambdaInf_apply (P : Hyp12 G) [(P.U.subgroupOf P.H0).Normal]
    (β : quotGroup P →* ℂˣ) (h : ↥P.H0) :
    lambdaInf P β h = (β (quotMk P h) : ℂ) := rfl

/-- The range of `lambdaInf P` is exactly `Lambda P`. -/
theorem lambdaInf_mem (P : Hyp12 G) [(P.U.subgroupOf P.H0).Normal]
    (β : quotGroup P →* ℂˣ) : lambdaInf P β ∈ Lambda P := ⟨β, rfl⟩

/-- `lambdaOrbitSum` expressed through `lambdaInf`. -/
theorem lambdaOrbitSum_eq_sum (P : Hyp12 G) [(P.U.subgroupOf P.H0).Normal]
    [Fintype (quotGroup P →* ℂˣ)] (δ : ClassFunction ↥P.H0 ℂ) :
    lambdaOrbitSum P δ = ∑ β : quotGroup P →* ℂˣ, lambdaInf P β * δ := rfl

/-- `Lambda P = Set.range (lambdaInf P)`. -/
theorem mem_Lambda_iff (P : Hyp12 G) [(P.U.subgroupOf P.H0).Normal]
    {δ : ClassFunction ↥P.H0 ℂ} :
    δ ∈ Lambda P ↔ ∃ β : quotGroup P →* ℂˣ, lambdaInf P β = δ := by
  constructor
  · rintro ⟨β, rfl⟩; exact ⟨β, rfl⟩
  · rintro ⟨β, rfl⟩; exact ⟨β, rfl⟩

/-- `Inf` is multiplicative: `Inf(β₁) · Inf(β₂) = Inf(β₁ β₂)`. -/
theorem lambdaInf_mul (P : Hyp12 G) [(P.U.subgroupOf P.H0).Normal]
    (β₁ β₂ : quotGroup P →* ℂˣ) :
    lambdaInf P β₁ * lambdaInf P β₂ = lambdaInf P (β₁ * β₂) := by
  ext h
  simp [lambdaInf, ClassFunction.mul_apply]

/-- `Inf(1)` is the trivial linear character of `H₀`. -/
theorem lambdaInf_one (P : Hyp12 G) [(P.U.subgroupOf P.H0).Normal] :
    lambdaInf P 1 = linearClassFunction (1 : ↥P.H0 →* ℂˣ) := by
  ext h
  simp [lambdaInf]

/-- `Inf(β⁻¹) · Inf(β)` is the trivial linear character of `H₀`. -/
theorem lambdaInf_inv_mul (P : Hyp12 G) [(P.U.subgroupOf P.H0).Normal]
    (β : quotGroup P →* ℂˣ) :
    lambdaInf P β⁻¹ * lambdaInf P β = linearClassFunction (1 : ↥P.H0 →* ℂˣ) := by
  rw [lambdaInf_mul, ← lambdaInf_one]
  exact congrArg (lambdaInf P) (inv_mul_cancel β)

/-- The pointwise product of class functions is associative. -/
theorem mul_assoc_cf {k : Type} [CommRing k] {H : Type} [Group H]
    (φ ψ χ : ClassFunction H k) : (φ * ψ) * χ = φ * (ψ * χ) := by
  ext g; simp only [ClassFunction.mul_apply]; ring

/-- The pointwise product of class functions is commutative. -/
theorem mul_comm_cf {k : Type} [CommRing k] {H : Type} [Group H]
    (φ ψ : ClassFunction H k) : φ * ψ = ψ * φ := by
  ext g; simp only [ClassFunction.mul_apply]; ring

/-- The trivial linear character is a left identity for the pointwise product. -/
theorem one_mul_cf {H : Type} [Group H] (φ : ClassFunction H ℂ) :
    linearClassFunction (1 : H →* ℂˣ) * φ = φ := by
  rw [mul_comm_cf, ClassFunction.mul_linearClassFunction_one]

/-- The parameterisation map `(β, μ) ↦ Inf(β)·μ : (H₀/U)^* × rep → Irr(H₀)`. -/
noncomputable def orbitMap (P : Hyp12 G) [(P.U.subgroupOf P.H0).Normal]
    (rep : Finset (ClassFunction ↥P.H0 ℂ))
    (hirr : ∀ μ ∈ rep, IsIrreducibleCharacter μ)
    (x : (quotGroup P →* ℂˣ) × ↥rep) : IrreducibleCharacter ↥P.H0 :=
  ⟨lambdaInf P x.1 * (x.2 : ClassFunction ↥P.H0 ℂ),
    lambda_mul_irreducible P (lambdaInf_mem P x.1) (hirr x.2.1 x.2.2)⟩

@[simp] theorem orbitMap_apply (P : Hyp12 G) [(P.U.subgroupOf P.H0).Normal]
    (rep : Finset (ClassFunction ↥P.H0 ℂ))
    (hirr : ∀ μ ∈ rep, IsIrreducibleCharacter μ)
    (x : (quotGroup P →* ℂˣ) × ↥rep) :
    (orbitMap P rep hirr x : ClassFunction ↥P.H0 ℂ) = lambdaInf P x.1 * x.2.1 := rfl

end Work.BG
