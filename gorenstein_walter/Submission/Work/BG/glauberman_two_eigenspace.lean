import Mathlib
import Submission.Work.BG.glauberman_two_setup

/-!
# The `±1`-eigenspace decomposition of `ρ(gInv σ)`

Let `σ` be an involutive automorphism of a group `U` and let `Γ = U ⋊ ⟨σ⟩` be the
semidirect product of `glauberman_two_setup.lean`, with `a = Gam.gInv σ ∈ Γ` the
involution corresponding to `σ`.  For a finite-dimensional complex representation
`ρ : Γ → GL(V)` the operator `A = ρ a` satisfies `A² = 1`, so `V` splits as the
direct sum of the `(+1)`- and `(-1)`-eigenspaces of `A`, and the character of `ρ`
on the fixed subgroup `C_U(σ) ≤ Γ` splits accordingly:

* `ρ.character (iot σ b) = ν⁺(b) + ν⁻(b)`,
* `ρ.character (a * iot σ b) = ν⁺(b) − ν⁻(b)`,

where `ν⁺`, `ν⁻` are the (genuine) characters of the restrictions of `ρ` to the
two eigenspaces (`b ∈ C_U(σ)` commutes with `a`, hence preserves both).

Thus `ν⁺ = (χ + χ_a)/2` and `ν⁻ = (χ − χ_a)/2` with `χ = ρ.character ∘ iot` and
`χ_a = ρ.character ∘ (a · iot ·)`; the content of the statement is that this
half-sum is again a genuine character, which we obtain by exhibiting the actual
subrepresentation on `range p`, where `p = ½(1 + A)` is the projection onto the
`(+1)`-eigenspace.

## Main results

* `Work.BG.exists_rep_trace_mul_of_idempotent` — the linear-algebra engine: an
  idempotent endomorphism `p` of `V` commuting with a representation `Φ` of a
  group `B` cuts out a subrepresentation on `range p` whose character is
  `b ↦ trace (p * Φ b)`.
* `Work.BG.trace_mul_conj_of_commute` — that function is a class function.
* `Work.BG.iot_mul_gInv_eq` — `a` commutes with the embedded copy of `C_U(σ)`.
* `Work.BG.glauberman_two_eigenspace` — the theorem above.
-/

namespace Work.BG

set_option linter.unusedSimpArgs false

open scoped BigOperators

/-! ## A linear-algebra engine -/

/-- **Engine.**  Let `p` be an idempotent endomorphism of a finite-dimensional complex
vector space `V` which commutes with every operator of a representation `Φ` of a group `B`.
Then the range of `p` is `Φ`-invariant and the restriction of `Φ` to it (a subrepresentation)
has character `b ↦ trace (p * Φ b)`.

Concretely `range p` is the `(+1)`-eigenspace of the projection `p`, and `trace (p * Φ b)`
is the trace of `Φ b` on that subspace. -/
theorem exists_rep_trace_mul_of_idempotent {B : Type} [Group B] {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V]
    (Φ : Representation ℂ B V) (p : Module.End ℂ V) (hp : IsIdempotentElem p)
    (hcomm : ∀ b : B, p * Φ b = Φ b * p) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (Ψ : Representation ℂ B W),
      ∀ b : B, Ψ.character b = LinearMap.trace ℂ V (p * Φ b) := by
  classical
  let P : Submodule ℂ V := LinearMap.range p
  have hproj : LinearMap.IsProj P p := LinearMap.IsIdempotentElem.isProj_range p hp
  have hsub : P.subtype ∘ₗ hproj.codRestrict = p :=
    LinearMap.IsProj.subtype_comp_codRestrict hproj
  have hef : ∀ y : V, (hproj.codRestrict y : V) = p y := fun y =>
    LinearMap.IsProj.codRestrict_apply hproj y
  have hfw : hproj.codRestrict ∘ₗ P.subtype = (1 : Module.End ℂ ↥P) := by
    apply LinearMap.ext
    intro x
    exact LinearMap.IsProj.codRestrict_apply_cod hproj x
  have hΨone : hproj.codRestrict ∘ₗ Φ 1 ∘ₗ P.subtype = (1 : Module.End ℂ ↥P) := by
    rw [map_one]
    exact hfw
  have hΨmul : ∀ a b : B,
      hproj.codRestrict ∘ₗ Φ (a * b) ∘ₗ P.subtype
        = (hproj.codRestrict ∘ₗ Φ a ∘ₗ P.subtype)
            * (hproj.codRestrict ∘ₗ Φ b ∘ₗ P.subtype) := by
    intro a b
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, Module.End.mul_apply, map_mul]
    have key : P.subtype (hproj.codRestrict (Φ b (P.subtype x))) = Φ b (P.subtype x) := by
      show (↑(hproj.codRestrict (Φ b (P.subtype x))) : V) = Φ b (P.subtype x)
      rw [hef, ← Module.End.mul_apply, hcomm b, Module.End.mul_apply]
      rw [hproj.map_id (P.subtype x) x.2]
    rw [key]
  have hchar : ∀ b : B,
      LinearMap.trace ℂ ↥P (hproj.codRestrict ∘ₗ Φ b ∘ₗ P.subtype)
        = LinearMap.trace ℂ V (p * Φ b) := by
    intro b
    have htc := LinearMap.trace_comp_comm' (R := ℂ) (f := P.subtype)
      (g := hproj.codRestrict ∘ₗ Φ b)
    rw [LinearMap.comp_assoc] at htc
    rw [htc, ← LinearMap.comp_assoc, hsub, Module.End.mul_eq_comp]
  exact ⟨↥P, inferInstance, inferInstance, inferInstance,
    { toFun := fun b => hproj.codRestrict ∘ₗ Φ b ∘ₗ P.subtype
      map_one' := hΨone
      map_mul' := hΨmul }, hchar⟩

/-- The function `b ↦ trace (p * Φ b)` attached to an idempotent operator `p` commuting with a
representation `Φ` is a class function. -/
theorem trace_mul_conj_of_commute {B : Type} [Group B] {V : Type} [AddCommGroup V] [Module ℂ V]
    (Φ : Representation ℂ B V) (p : Module.End ℂ V) (hcomm : ∀ b : B, p * Φ b = Φ b * p)
    (b h : B) :
    LinearMap.trace ℂ V (p * Φ (h * b * h⁻¹)) = LinearMap.trace ℂ V (p * Φ b) := by
  have hΦh' : Φ h⁻¹ * Φ h = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hstep : ∀ x : Module.End ℂ V, p * (Φ h * x) = Φ h * (p * x) := by
    intro x
    rw [← mul_assoc, hcomm h, mul_assoc]
  have hsplit : p * Φ (h * b * h⁻¹) = Φ h * (p * Φ b) * Φ h⁻¹ := by
    rw [map_mul, map_mul]
    calc p * (Φ h * Φ b * Φ h⁻¹)
        = p * (Φ h * (Φ b * Φ h⁻¹)) := by rw [mul_assoc]
      _ = Φ h * (p * (Φ b * Φ h⁻¹)) := hstep (Φ b * Φ h⁻¹)
      _ = Φ h * ((p * Φ b) * Φ h⁻¹) := by rw [← mul_assoc p (Φ b) (Φ h⁻¹)]
      _ = Φ h * (p * Φ b) * Φ h⁻¹ := by rw [← mul_assoc (Φ h) (p * Φ b) (Φ h⁻¹)]
  rw [hsplit, LinearMap.trace_mul_comm ℂ (Φ h * (p * Φ b)) (Φ h⁻¹), ← mul_assoc, hΦh', one_mul]

/-! ## The involution commutes with the fixed subgroup -/

/-- The involution `a = Gam.gInv σ` commutes with the embedded copy of the fixed subgroup
`C_U(σ)`. -/
theorem iot_mul_gInv_eq {U : Type} [Group U] (σ : MulAut U) (b : ↥(fixedSubgroup σ)) :
    Gam.iot σ (b : U) * Gam.gInv σ = Gam.gInv σ * Gam.iot σ (b : U) := by
  have hb : σ (b : U) = (b : U) := b.2
  have h1 : Gam.gInv σ * Gam.iot σ (b : U) * (Gam.gInv σ)⁻¹ = Gam.iot σ (b : U) := by
    rw [Gam.gInv_mul_iot σ (b : U), hb]
  exact (mul_inv_eq_iff_eq_mul.mp h1).symm

/-! ## The main theorem -/

theorem glauberman_two_eigenspace {U : Type} [Group U] (σ : MulAut U) (hσ : σ * σ = 1)
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Work.BG.Gam σ) V) :
    ∃ νp νm : OddOrder.RepresentationTheory.ClassFunction ↥(Work.BG.fixedSubgroup σ) ℂ,
      OddOrder.RepresentationTheory.IsCharacter νp ∧
      OddOrder.RepresentationTheory.IsCharacter νm ∧
      (∀ b : ↥(Work.BG.fixedSubgroup σ),
        ρ.character (Work.BG.Gam.iot σ (b : U)) = νp b + νm b) ∧
      (∀ b : ↥(Work.BG.fixedSubgroup σ),
        ρ.character (Work.BG.Gam.gInv σ * Work.BG.Gam.iot σ (b : U)) = νp b - νm b) := by
  classical
  -- The operator attached to the involution.
  set A : Module.End ℂ V := ρ (Gam.gInv σ) with hAdef
  have hAA : A * A = 1 := by
    rw [hAdef, ← map_mul, Gam.gInv_mul_self σ hσ, map_one]
  -- The two eigenspace projections.
  set p : Module.End ℂ V := (2 : ℂ)⁻¹ • (1 + A) with hpdef
  set q : Module.End ℂ V := (2 : ℂ)⁻¹ • (1 - A) with hqdef
  -- The character map of the fixed subgroup.
  let Φ : Representation ℂ ↥(fixedSubgroup σ) V :=
    (ρ.comp (Gam.iot σ)).comp (fixedSubgroup σ).subtype
  have hΦ : ∀ b : ↥(fixedSubgroup σ), Φ b = ρ (Gam.iot σ (b : U)) := fun _ => rfl
  -- The involution commutes with `Φ`.
  have hAΦ : ∀ b : ↥(fixedSubgroup σ), A * Φ b = Φ b * A := by
    intro b
    show ρ (Gam.gInv σ) * ρ (Gam.iot σ (b : U)) = ρ (Gam.iot σ (b : U)) * ρ (Gam.gInv σ)
    rw [← map_mul, ← map_mul]
    congr 1
    exact (iot_mul_gInv_eq σ b).symm
  have hAΦx : ∀ b : ↥(fixedSubgroup σ), ∀ x : V, A (Φ b x) = Φ b (A x) := fun b x => by
    have h := DFunLike.congr_fun (hAΦ b) x
    simpa [Module.End.mul_apply] using h
  have hA2x : ∀ x : V, A (A x) = x := fun x => by
    have h := DFunLike.congr_fun hAA x
    simpa [Module.End.mul_apply] using h
  -- Algebra of the projections.
  have hp_add_q : p + q = 1 := by
    show ((2 : ℂ)⁻¹ • (1 + A)) + ((2 : ℂ)⁻¹ • (1 - A)) = 1
    ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply]
    module
  have hp_sub_q : p - q = A := by
    show ((2 : ℂ)⁻¹ • (1 + A)) - ((2 : ℂ)⁻¹ • (1 - A)) = A
    ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply]
    module
  have hp_idem : IsIdempotentElem p := by
    show p * p = p
    show ((2 : ℂ)⁻¹ • (1 + A)) * ((2 : ℂ)⁻¹ • (1 + A)) = (2 : ℂ)⁻¹ • (1 + A)
    ext x
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, map_add, map_sub, map_smul, hA2x]
    module
  have hq_idem : IsIdempotentElem q := by
    show q * q = q
    show ((2 : ℂ)⁻¹ • (1 - A)) * ((2 : ℂ)⁻¹ • (1 - A)) = (2 : ℂ)⁻¹ • (1 - A)
    ext x
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, map_add, map_sub, map_smul, hA2x]
    module
  -- The projections commute with `Φ`.
  have hpcomm : ∀ b : ↥(fixedSubgroup σ), p * Φ b = Φ b * p := by
    intro b
    show ((2 : ℂ)⁻¹ • (1 + A)) * Φ b = Φ b * ((2 : ℂ)⁻¹ • (1 + A))
    ext x
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, map_add, map_sub, map_smul, hAΦx b]
  have hqcomm : ∀ b : ↥(fixedSubgroup σ), q * Φ b = Φ b * q := by
    intro b
    show ((2 : ℂ)⁻¹ • (1 - A)) * Φ b = Φ b * ((2 : ℂ)⁻¹ • (1 - A))
    ext x
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, map_add, map_sub, map_smul, hAΦx b]
  -- The two class functions.
  have hclassp : ∀ b h : ↥(fixedSubgroup σ),
      LinearMap.trace ℂ V (p * Φ (h * b * h⁻¹)) = LinearMap.trace ℂ V (p * Φ b) :=
    fun b h => trace_mul_conj_of_commute Φ p hpcomm b h
  have hclassm : ∀ b h : ↥(fixedSubgroup σ),
      LinearMap.trace ℂ V (q * Φ (h * b * h⁻¹)) = LinearMap.trace ℂ V (q * Φ b) :=
    fun b h => trace_mul_conj_of_commute Φ q hqcomm b h
  let νp : OddOrder.RepresentationTheory.ClassFunction ↥(fixedSubgroup σ) ℂ :=
    ⟨fun b => LinearMap.trace ℂ V (p * Φ b), hclassp⟩
  let νm : OddOrder.RepresentationTheory.ClassFunction ↥(fixedSubgroup σ) ℂ :=
    ⟨fun b => LinearMap.trace ℂ V (q * Φ b), hclassm⟩
  refine ⟨νp, νm, ?_, ?_, ?_, ?_⟩
  · -- `νp` is a genuine character
    obtain ⟨W, i1, i2, i3, Ψ, hΨ⟩ := exists_rep_trace_mul_of_idempotent Φ p hp_idem hpcomm
    exact ⟨W, i1, i2, i3, Ψ, funext fun b => (hΨ b).symm⟩
  · -- `νm` is a genuine character
    obtain ⟨W, i1, i2, i3, Ψ, hΨ⟩ := exists_rep_trace_mul_of_idempotent Φ q hq_idem hqcomm
    exact ⟨W, i1, i2, i3, Ψ, funext fun b => (hΨ b).symm⟩
  · -- value on `iot b`
    intro b
    calc ρ.character (Gam.iot σ (b : U))
        = LinearMap.trace ℂ V (Φ b) := by
            show LinearMap.trace ℂ V (ρ (Gam.iot σ (b : U))) = LinearMap.trace ℂ V (Φ b)
            rw [hΦ b]
      _ = LinearMap.trace ℂ V ((p + q) * Φ b) := by rw [hp_add_q, one_mul]
      _ = LinearMap.trace ℂ V (p * Φ b) + LinearMap.trace ℂ V (q * Φ b) := by
            rw [add_mul, map_add (LinearMap.trace ℂ V)]
      _ = νp b + νm b := rfl
  · -- value on `gInv σ * iot b`
    intro b
    calc ρ.character (Gam.gInv σ * Gam.iot σ (b : U))
        = LinearMap.trace ℂ V (A * Φ b) := by
            show LinearMap.trace ℂ V (ρ (Gam.gInv σ * Gam.iot σ (b : U)))
              = LinearMap.trace ℂ V (A * Φ b)
            rw [map_mul, hAdef, hΦ b]
      _ = LinearMap.trace ℂ V ((p - q) * Φ b) := by rw [hp_sub_q]
      _ = LinearMap.trace ℂ V (p * Φ b) - LinearMap.trace ℂ V (q * Φ b) := by
            rw [sub_mul, map_sub (LinearMap.trace ℂ V)]
      _ = νp b - νm b := rfl

end Work.BG
