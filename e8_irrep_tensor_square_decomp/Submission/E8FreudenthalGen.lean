import Submission.E8Freudenthal
import Submission.Commons.Algebra.Lie.SerreConstruction.weight_support_of_primitive
import Submission.E8Enum

/-!
# The Freudenthal/Casimir trace recursion for a general `e₈`-module with scalar Casimir

`Submission/E8Freudenthal.lean` proves the Freudenthal recursion for the weight multiplicities of
the irreducible quotient `L = V ⧸ N = L(ω₁+ω₈)`; the *only* structural inputs of its trace argument
are (i) that `L` is a finite-dimensional `U(e₈)`-module and (ii) that the Casimir element `Ω` acts
on `L` by a *scalar* (`Omega_smul_eq`, which follows from cyclicity and the Casimir eigenvalue on
the highest weight vector).

For the lower bound of `ncard = 40` (see the SESSION 21 section of the roadmap in
`Submission.lean`) the same recursion is needed for the *isotypic components*
`Z_ν = Q_ν(Ω)·T` of the tensor square `T = (V ⧸ N) ⊗ (V ⧸ N)`, `ν ∈ the40`: these are modules on
which `Ω` acts by the scalar `c(ν) = ⟪ν+ρ,ν+ρ⟫` (the projection `Q_ν` is a polynomial in the
commuting family `Ω`), but they are not of the shape `V ⧸ N'`.

This file provides the *generic* form of the recursion: for **any** finite-dimensional complex
`e₈`-module `M` carrying a `Module U(e₈)` structure compatible with the scalar action, such that
`Ω` acts on `M` by the scalar attached to a weight `Λ` and such that all weights of `M` lie in the
cone `Λ - ℕΦ⁺`, the weight multiplicities `m μ = finrank ℂ (Wt μ)` satisfy

  `(Bint Λ - Bint μ) * m μ = 2 * ∑ j ∑_{k=1}^{htOf (Λ-μ)} (brk (μ + k • pR j) j) * m (μ + k • pR j)`.

This is the verbatim generalisation of `Submission.E8Freudenthal.freudenthal_mul` (which is the
special case `M = V ⧸ N`, `Λ = ω₁+ω₈`): the file is COMPLETE and sorry-free.  Its main theorem is
`freudenthal_recursion` below; the ingredients are the generic action endomorphism `endM`, the
weight spaces `Wt`, the weight shift `endM_iota_mem_Wt`, the Cartan action
`endM_iota_cartan_apply`, the restricted root operators `EopM/FopM/FEmapM/EFmapM`, the traces
`StrM/TtrM` with the step relation `StrM_step`, the Casimir decomposition
`HHmapM`/`restOmegaM_eq`/`traceOmegaM_eq_sum`, the master trace identity `two_sum_StrM`, and the
string unfolding `shM`/`StrM_eq_sum`/`StrM_eq_zero_of_htOf_neg`/`StrM_last_zero`/
`StrM_eq_bil`/`sixty_StrM_eq`/`sixty_cas_sub`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

noncomputable section
open scoped BigOperators Matrix

namespace Submission.E8FreudenthalGen

open Commons.Algebra.Lie Commons.Algebra.Lie.SerreConstruction
open Submission.E8Casimir
open Submission.E8Character

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [-instance] Submission.Enveloping.instLieRingModuleE8
attribute [-instance] Submission.Enveloping.instLieModuleE8

abbrev L8 : Type := LieAlgebra.e₈ ℂ
abbrev U : Type := UniversalEnvelopingAlgebra ℂ L8

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [Module U M] [IsScalarTower ℂ U M]

/-- The endomorphism of `M` attached to an element of the enveloping algebra. -/
noncomputable def endM (u : U) : Module.End ℂ M where
  toFun x := u • x
  map_add' x y := smul_add u x y
  map_smul' c x := Submission.Enveloping.module_smul_comm_scalar (R := ℂ) (L := L8) u c x

@[simp] lemma endM_apply (u : U) (x : M) : endM (M := M) u x = u • x := rfl

lemma endM_mul (u u' : U) : endM (M := M) (u * u') = endM (M := M) u * endM (M := M) u' := by
  ext x; simp [mul_smul]

lemma endM_add (u u' : U) : endM (M := M) (u + u') = endM (M := M) u + endM (M := M) u' := by
  ext x; simp [add_smul]

lemma endM_sub (u u' : U) : endM (M := M) (u - u') = endM (M := M) u - endM (M := M) u' := by
  ext x; simp [sub_smul]

lemma endM_smul (c : ℂ) (u : U) : endM (M := M) (c • u) = c • endM (M := M) u := by
  ext x
  rw [LinearMap.smul_apply, endM_apply, endM_apply, smul_assoc]

@[simp] lemma endM_zero : endM (M := M) (0 : U) = 0 := by ext x; simp

lemma endM_sum {ι : Type*} (s : Finset ι) (f : ι → U) :
    endM (M := M) (∑ a ∈ s, f a) = ∑ a ∈ s, endM (M := M) (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, endM_add, ih]

lemma endM_pow (u : U) (n : ℕ) : endM (M := M) (u ^ n) = (endM (M := M) u) ^ n := by
  induction n with
  | zero => ext x; simp
  | succ n ih => rw [pow_succ, endM_mul, ih, pow_succ]

/-- The joint eigenspace of the Cartan generators at the integral weight `μ`. -/
def Wt (μ : Fin 8 → ℤ) : Submodule ℂ M :=
  ⨅ i : Fin 8, Module.End.eigenspace (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (SerreH i)))
    ((μ i : ℤ) : ℂ)

lemma mem_Wt_iff {μ : Fin 8 → ℤ} {x : M} :
    x ∈ Wt (M := M) μ ↔ ∀ i,
      endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (SerreH i)) x = ((μ i : ℤ) : ℂ) • x := by
  simp only [Wt, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

/-- **The weight shift**: acting by `ι x` with `x` in the adjoint weight space `e8W α` moves the
weight by `α`. -/
lemma endM_iota_mem_Wt (α : Fin 8 → ℤ) {x : L8} (hx : x ∈ e8W α)
    {μ : Fin 8 → ℤ} {y : M} (hy : y ∈ Wt (M := M) μ) :
    endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ x) y ∈ Wt (M := M) (μ + α) := by
  rw [mem_Wt_iff] at hy ⊢
  intro i
  have hy' : UniversalEnvelopingAlgebra.ι ℂ (SerreH i) • y = ((μ i : ℤ) : ℂ) • y := hy i
  have hb : ⁅SerreH i, x⁆ = ((α i : ℤ) : ℂ) • x := mem_e8W_iff.mp hx i
  have hrel : UniversalEnvelopingAlgebra.ι ℂ (SerreH i) * UniversalEnvelopingAlgebra.ι ℂ x
      = UniversalEnvelopingAlgebra.ι ℂ x * UniversalEnvelopingAlgebra.ι ℂ (SerreH i)
        + UniversalEnvelopingAlgebra.ι ℂ ⁅SerreH i, x⁆ := by
    rw [← Submission.Enveloping.ι_commutator_eq]
    abel
  rw [endM_apply, endM_apply, ← mul_smul, hrel, add_smul, mul_smul, hy',
    Submission.Enveloping.module_smul_comm_scalar (R := ℂ) (L := L8)
      (UniversalEnvelopingAlgebra.ι ℂ x) ((μ i : ℤ) : ℂ) y,
    hb, map_smul, IsScalarTower.smul_assoc, ← add_smul]
  congr 1
  simp only [Pi.add_apply, Int.cast_add]

/-! ## The action of a Cartan element on a weight space -/

/-- **A Cartan element acts on a weight space by the `κ`-dual functional.** -/
theorem endM_iota_cartan_apply {z : L8} (hz : z ∈ e8W 0) (ν : Fin 8 → ℤ) {y : M}
    (hy : y ∈ Wt (M := M) ν) :
    endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ z) y = (K (wdual ν) z) • y := by
  have hspan : z ∈ Submodule.span ℂ (Set.range SerreH) := by
    rw [← e8W_zero_eq_span_SerreH]; exact hz
  have key : ∀ z ∈ Submodule.span ℂ (Set.range SerreH),
      endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ z) y = (K (wdual ν) z) • y := by
    intro z hz'
    induction hz' using Submodule.span_induction with
    | mem u hu =>
        obtain ⟨i, rfl⟩ := hu
        rw [K_wdual_SerreH]
        exact mem_Wt_iff.mp hy i
    | zero => simp
    | add a b _ _ ha hb =>
        rw [map_add, endM_add, LinearMap.add_apply, ha, hb, map_add, add_smul]
    | smul c a _ ha =>
        rw [map_smul, endM_smul, LinearMap.smul_apply, ha, map_smul, smul_assoc]
  exact key z hspan

/-- **The coroot `(α_k)∨` acts on the weight space `Wt ν` by `(ν, α_k)_κ`.** -/
theorem endM_iota_wdual_pR_apply (k : Fin 120) (ν : Fin 8 → ℤ) {y : M}
    (hy : y ∈ Wt (M := M) ν) :
    endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (wdual (pR k))) y
      = (K (wdual ν) (wdual (pR k))) • y :=
  endM_iota_cartan_apply (wdual_mem_cartan (pR k)) ν hy

/-! ## The restricted operators and their traces -/

/-- The endomorphism of `Wt ν` induced by `u : U(e₈)`. -/
noncomputable def restM (ν : Fin 8 → ℤ) (u : U)
    (h : ∀ x ∈ Wt (M := M) ν, endM (M := M) u x ∈ Wt (M := M) ν) :
    ↥(Wt (M := M) ν) →ₗ[ℂ] ↥(Wt (M := M) ν) :=
  LinearMap.restrict (endM (M := M) u) h

/-- The restriction of the Casimir to a weight space, when the Casimir is a scalar `c`. -/
noncomputable def restOmegaM (c : ℂ) (hc : endM (M := M) Omega = c • 1)
    (ν : Fin 8 → ℤ) : ↥(Wt (M := M) ν) →ₗ[ℂ] ↥(Wt (M := M) ν) :=
  LinearMap.restrict (endM (M := M) Omega) (fun x hx => by
    have h : endM (M := M) Omega x = c • x := by
      rw [hc]; rfl
    rw [h]
    exact Submodule.smul_mem _ _ hx)

/-- The trace of the Casimir on a weight space. -/
noncomputable def traceOmegaM (c : ℂ) (hc : endM (M := M) Omega = c • 1)
    (ν : Fin 8 → ℤ) [Module.Finite ℂ ↥(Wt (M := M) ν)] : ℂ :=
  LinearMap.trace ℂ ↥(Wt (M := M) ν) (restOmegaM (M := M) c hc ν)

lemma traceOmegaM_eq (c : ℂ) (hc : endM (M := M) Omega = c • 1)
    (ν : Fin 8 → ℤ) [Module.Finite ℂ ↥(Wt (M := M) ν)] :
    traceOmegaM (M := M) c hc ν = c * (Module.finrank ℂ ↥(Wt (M := M) ν) : ℂ) := by
  have h : restOmegaM (M := M) c hc ν = c • (1 : Module.End ℂ ↥(Wt (M := M) ν)) := by
    ext x
    rw [LinearMap.smul_apply, Module.End.one_apply]
    show endM (M := M) Omega (x : M) = c • (x : M)
    rw [congrArg (fun f : Module.End ℂ M => f (x : M)) hc, LinearMap.smul_apply,
      Module.End.one_apply]
  rw [traceOmegaM, h, map_smul, LinearMap.trace_one, smul_eq_mul]

/-! ## The restricted root operators and their traces -/

/-- The raising operator `e_α` restricted to the weight spaces. -/
noncomputable def EopM (k : Fin 120) (ν : Fin 8 → ℤ) :
    ↥(Wt (M := M) ν) →ₗ[ℂ] ↥(Wt (M := M) (ν + pR k)) :=
  LinearMap.restrict (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (eRoot k)))
    (fun _x hx => endM_iota_mem_Wt (M := M) (pR k) (eRoot_mem k) hx)

/-- The lowering operator `f_α` restricted to the weight spaces. -/
noncomputable def FopM (k : Fin 120) (ν : Fin 8 → ℤ) :
    ↥(Wt (M := M) (ν + pR k)) →ₗ[ℂ] ↥(Wt (M := M) ν) :=
  LinearMap.restrict (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (fRoot k)))
    (fun _x hx => by
      have h := endM_iota_mem_Wt (M := M) (-(pR k)) (fRoot_mem k) hx
      rwa [add_assoc, add_neg_cancel, add_zero] at h)

lemma FEmapM_mem (k : Fin 120) (ν : Fin 8 → ℤ) {x : M} (hx : x ∈ Wt (M := M) ν) :
    ((endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (fRoot k)))
      * (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (eRoot k)))) x
      ∈ Wt (M := M) ν := by
  rw [Module.End.mul_apply]
  have h := endM_iota_mem_Wt (M := M) (-(pR k)) (fRoot_mem k)
    (endM_iota_mem_Wt (M := M) (pR k) (eRoot_mem k) hx)
  rwa [add_assoc, add_neg_cancel, add_zero] at h

lemma EFmapM_mem (k : Fin 120) (ν : Fin 8 → ℤ) {x : M} (hx : x ∈ Wt (M := M) ν) :
    ((endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (eRoot k)))
      * (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (fRoot k)))) x
      ∈ Wt (M := M) ν := by
  rw [Module.End.mul_apply]
  have h := endM_iota_mem_Wt (M := M) (pR k) (eRoot_mem k)
    (endM_iota_mem_Wt (M := M) (-(pR k)) (fRoot_mem k) hx)
  rwa [add_assoc, neg_add_cancel, add_zero] at h

/-- The restriction of `f_α ∘ e_α` to a weight space. -/
noncomputable def FEmapM (k : Fin 120) (ν : Fin 8 → ℤ) :
    ↥(Wt (M := M) ν) →ₗ[ℂ] ↥(Wt (M := M) ν) :=
  LinearMap.restrict ((endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (fRoot k)))
    * (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (eRoot k))))
    (fun _x hx => FEmapM_mem (M := M) k ν hx)

/-- The restriction of `e_α ∘ f_α` to a weight space. -/
noncomputable def EFmapM (k : Fin 120) (ν : Fin 8 → ℤ) :
    ↥(Wt (M := M) ν) →ₗ[ℂ] ↥(Wt (M := M) ν) :=
  LinearMap.restrict ((endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (eRoot k)))
    * (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (fRoot k))))
    (fun _x hx => EFmapM_mem (M := M) k ν hx)

lemma FEmapM_eq (k : Fin 120) (ν : Fin 8 → ℤ) :
    FEmapM (M := M) k ν = (FopM (M := M) k ν).comp (EopM (M := M) k ν) := by
  ext x; rfl

lemma EFmapM_eq (k : Fin 120) (ν : Fin 8 → ℤ) :
    EFmapM (M := M) k (ν + pR k) = (EopM (M := M) k ν).comp (FopM (M := M) k ν) := by
  ext x; rfl

/-- The commutator identity `[e_α, f_α] = (α∨)` on a weight space. -/
lemma EFmapM_sub_FEmapM (k : Fin 120) (ν : Fin 8 → ℤ) :
    EFmapM (M := M) k ν - FEmapM (M := M) k ν
      = (K (wdual ν) (wdual (pR k))) • (1 : Module.End ℂ ↥(Wt (M := M) ν)) := by
  have hcomm : (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (eRoot k)))
        * (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (fRoot k)))
      - (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (fRoot k)))
        * (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (eRoot k)))
      = endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (wdual (pR k))) := by
    rw [← endM_mul, ← endM_mul, ← endM_sub]
    congr 1
    exact (Submission.Enveloping.ι_commutator_eq (R := ℂ) (L := L8) (eRoot k) (fRoot k)).trans
      (by rw [eRoot_comm_fRoot k])
  ext x
  rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
  have hx : (x : M) ∈ Wt (M := M) ν := x.2
  have h := endM_iota_cartan_apply (M := M) (wdual_mem_cartan (pR k)) ν hx
  have e1 : (↑((EFmapM (M := M) k ν) x) : M)
      = ((endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (eRoot k)))
        * (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (fRoot k)))) (x : M) := rfl
  have e2 : (↑((FEmapM (M := M) k ν) x) : M)
      = ((endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (fRoot k)))
        * (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (eRoot k)))) (x : M) := rfl
  rw [show (↑(EFmapM (M := M) k ν x - FEmapM (M := M) k ν x) : M)
        = (↑((EFmapM (M := M) k ν) x) : M) - ↑((FEmapM (M := M) k ν) x)
      from map_sub (Submodule.subtype (Wt (M := M) ν)) _ _,
    e1, e2, ← LinearMap.sub_apply, hcomm]
  exact h

/-- The trace of `f_α ∘ e_α` on a weight space. -/
noncomputable def StrM (k : Fin 120) (ν : Fin 8 → ℤ) [Module.Finite ℂ ↥(Wt (M := M) ν)] : ℂ :=
  LinearMap.trace ℂ ↥(Wt (M := M) ν) (FEmapM (M := M) k ν)

/-- The trace of `e_α ∘ f_α` on a weight space. -/
noncomputable def TtrM (k : Fin 120) (ν : Fin 8 → ℤ) [Module.Finite ℂ ↥(Wt (M := M) ν)] : ℂ :=
  LinearMap.trace ℂ ↥(Wt (M := M) ν) (EFmapM (M := M) k ν)

lemma StrM_eq_TtrM (k : Fin 120) (ν : Fin 8 → ℤ)
    [Module.Finite ℂ ↥(Wt (M := M) ν)]
    [Module.Finite ℂ ↥(Wt (M := M) (ν + pR k))] :
    StrM (M := M) k ν = TtrM (M := M) k (ν + pR k) := by
  rw [StrM, FEmapM_eq, TtrM, EFmapM_eq]
  exact LinearMap.trace_comp_comm' (EopM (M := M) k ν) (FopM (M := M) k ν)

/-- **The step relation for the trace `S`.** -/
lemma StrM_step (k : Fin 120) (ν : Fin 8 → ℤ)
    [Module.Finite ℂ ↥(Wt (M := M) ν)]
    [Module.Finite ℂ ↥(Wt (M := M) (ν + pR k))] :
    StrM (M := M) k ν = StrM (M := M) k (ν + pR k)
      + (K (wdual (ν + pR k)) (wdual (pR k))) * (Module.finrank ℂ ↥(Wt (M := M) (ν + pR k)) : ℂ) := by
  have h := EFmapM_sub_FEmapM (M := M) k (ν + pR k)
  have htr : TtrM (M := M) k (ν + pR k) - StrM (M := M) k (ν + pR k)
      = (K (wdual (ν + pR k)) (wdual (pR k)))
        * (Module.finrank ℂ ↥(Wt (M := M) (ν + pR k)) : ℂ) := by
    rw [TtrM, StrM, ← map_sub, h, map_smul, LinearMap.trace_one, smul_eq_mul]
  rw [StrM_eq_TtrM (M := M) k ν]
  rw [sub_eq_iff_eq_add] at htr
  exact htr.trans (by rw [add_comm])

/-! ## The decomposition of the Casimir trace -/

/-- The restriction of the Cartan part `HᵢHⁱ` of the Casimir to a weight space. -/
noncomputable def HHmapM (i : Fin 8) (ν : Fin 8 → ℤ) :
    ↥(Wt (M := M) ν) →ₗ[ℂ] ↥(Wt (M := M) ν) :=
  LinearMap.restrict ((endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (SerreH i)))
      * (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (((hdual i : H) : L8)))))
    (fun _x hx => by
      rw [Module.End.mul_apply,
        endM_iota_cartan_apply (M := M) (hdual_mem_e8W_zero i) ν hx, map_smul]
      refine Submodule.smul_mem _ _ ?_
      have h2 := endM_iota_mem_Wt (M := M) 0 (serreH_mem_e8W_zero i) hx
      rwa [add_zero] at h2)

/-- The action of `HHmapM` on a weight space. -/
lemma HHmapM_apply (i : Fin 8) (ν : Fin 8 → ℤ) (x : ↥(Wt (M := M) ν)) :
    ((HHmapM (M := M) i ν) x : M)
      = (((ν i : ℤ) : ℂ) * (K (wdual ν) (((hdual i : H) : L8)))) • (x : M) := by
  have hx : (x : M) ∈ Wt (M := M) ν := x.2
  have h1 := endM_iota_cartan_apply (M := M) (hdual_mem_e8W_zero i) ν hx
  have h2 : endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (SerreH i)) (x : M)
      = ((ν i : ℤ) : ℂ) • (x : M) := mem_Wt_iff.mp hx i
  show (((endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (SerreH i)))
      * (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (((hdual i : H) : L8))))) (x : M))
      = (((ν i : ℤ) : ℂ) * (K (wdual ν) (((hdual i : H) : L8)))) • (x : M)
  rw [Module.End.mul_apply, h1, map_smul, h2, smul_smul]
  congr 1
  ring

/-- **Decomposition of the Casimir trace**: the Casimir splits into the Cartan part and the
root parts. -/
lemma restOmegaM_eq (c : ℂ) (hc : endM (M := M) Omega = c • 1) (ν : Fin 8 → ℤ) :
    restOmegaM (M := M) c hc ν = (∑ i : Fin 8, HHmapM (M := M) i ν)
      + (∑ k : Fin 120, EFmapM (M := M) k ν) + (∑ k : Fin 120, FEmapM (M := M) k ν) := by
  have hΩop : endM (M := M) Omega
      = (∑ i : Fin 8, (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (SerreH i)))
          * (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (((hdual i : H) : L8)))))
        + (∑ k : Fin 120, (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (eRoot k)))
          * (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (fRoot k))))
        + (∑ k : Fin 120, (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (fRoot k)))
          * (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (eRoot k)))) := by
    have hhom : endM (M := M) Omega
        = ∑ a : Idx, (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (bIdx a)))
          * (endM (M := M) (UniversalEnvelopingAlgebra.ι ℂ (bDual a))) := by
      rw [Omega, endM_sum]
      exact Finset.sum_congr rfl fun a _ => endM_mul (M := M) _ _
    rw [hhom]
    simp only [bIdx_apply, bFam_inl, bFam_inr_inl, bFam_inr_inr, bDual_inl, bDual_inr_inl,
      bDual_inr_inr, Fintype.sum_sum_type]
    abel
  ext x
  simp only [restOmegaM, HHmapM, EFmapM, FEmapM, LinearMap.coe_restrict_apply, LinearMap.add_apply,
    LinearMap.sum_apply, Submodule.coe_add, Submodule.coe_sum, Pi.add_apply, hΩop]

/-- **The trace of the Casimir, decomposed.** -/
lemma traceOmegaM_eq_sum (c : ℂ) (hc : endM (M := M) Omega = c • 1) (ν : Fin 8 → ℤ)
    [Module.Finite ℂ ↥(Wt (M := M) ν)] :
    traceOmegaM (M := M) c hc ν
      = (∑ i : Fin 8, K (wdual ν) (((hdual i : H) : L8)) * ((ν i : ℤ) : ℂ))
          * (Module.finrank ℂ ↥(Wt (M := M) ν) : ℂ)
        + (∑ k : Fin 120, TtrM (M := M) k ν) + (∑ k : Fin 120, StrM (M := M) k ν) := by
  have hH : ∀ i : Fin 8, LinearMap.trace ℂ ↥(Wt (M := M) ν) (HHmapM (M := M) i ν)
      = K (wdual ν) (((hdual i : H) : L8)) * ((ν i : ℤ) : ℂ)
        * (Module.finrank ℂ ↥(Wt (M := M) ν) : ℂ) := by
    intro i
    have h : HHmapM (M := M) i ν
        = (K (wdual ν) (((hdual i : H) : L8)) * ((ν i : ℤ) : ℂ))
          • (1 : Module.End ℂ ↥(Wt (M := M) ν)) := by
      ext x
      rw [LinearMap.smul_apply, Module.End.one_apply]
      rw [HHmapM_apply, mul_comm]
      rfl
    rw [h, map_smul, LinearMap.trace_one, smul_eq_mul]
  rw [traceOmegaM, restOmegaM_eq, map_add, map_add, map_sum, map_sum, map_sum,
    Finset.sum_congr rfl (fun i _ => hH i), Finset.sum_mul]
  rfl

/-! ## The trace recursion for the root operators -/

/-- The trace of `e_α f_α` on a weight space. -/
lemma TtrM_eq (k : Fin 120) (ν : Fin 8 → ℤ) [Module.Finite ℂ ↥(Wt (M := M) ν)] :
    TtrM (M := M) k ν = StrM (M := M) k ν
      + K (wdual ν) (wdual (pR k)) * (Module.finrank ℂ ↥(Wt (M := M) ν) : ℂ) := by
  have h := EFmapM_sub_FEmapM (M := M) k ν
  have h2 : TtrM (M := M) k ν - StrM (M := M) k ν
      = K (wdual ν) (wdual (pR k)) * (Module.finrank ℂ ↥(Wt (M := M) ν) : ℂ) := by
    rw [TtrM, StrM, ← map_sub, h, map_smul, LinearMap.trace_one, smul_eq_mul]
  rw [sub_eq_iff_eq_add] at h2
  exact h2.trans (add_comm _ _)

/-- The Cartan part of the Casimir trace sums to `⟪ν,ν⟫`. -/
lemma sum_cartanM (ν : Fin 8 → ℤ) :
    (∑ i : Fin 8, K (wdual ν) (((hdual i : H) : L8)) * ((ν i : ℤ) : ℂ))
      = K (wdual ν) (wdual ν) := by
  have h : ∀ z : L8,
      (∑ i : Fin 8, K z (((hdual i : H) : L8)) * ((ν i : ℤ) : ℂ)) = K z (wdual ν) := by
    intro z
    rw [wdual_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  exact h (wdual ν)

/-- The sum of the traces `T` in terms of the traces `S`. -/
lemma sum_TtrM_eq (ν : Fin 8 → ℤ) [Module.Finite ℂ ↥(Wt (M := M) ν)] :
    (∑ k : Fin 120, TtrM (M := M) k ν)
      = (∑ k : Fin 120, StrM (M := M) k ν)
        + K (wdual ν) (wdual twoRho) * (Module.finrank ℂ ↥(Wt (M := M) ν) : ℂ) := by
  have hmul : (∑ k : Fin 120, K (wdual ν) (wdual (pR k))
        * (Module.finrank ℂ ↥(Wt (M := M) ν) : ℂ))
      = (∑ k : Fin 120, K (wdual ν) (wdual (pR k)))
        * (Module.finrank ℂ ↥(Wt (M := M) ν) : ℂ) :=
    (Finset.sum_mul Finset.univ (fun k : Fin 120 => K (wdual ν) (wdual (pR k)))
      (Module.finrank ℂ ↥(Wt (M := M) ν) : ℂ)).symm
  rw [Finset.sum_congr rfl (fun k _ => TtrM_eq (M := M) k ν), Finset.sum_add_distrib, hmul]
  congr 1
  rw [← wdual_sum_pR, map_sum]

/-- **The master trace identity**: `2 Σ_α S_α = (c - ⟪ν,ν+2ρ⟫) dim Wt_ν`. -/
lemma two_sum_StrM (c : ℂ) (hc : endM (M := M) Omega = c • 1) (ν : Fin 8 → ℤ)
    [Module.Finite ℂ ↥(Wt (M := M) ν)] :
    2 * (∑ k : Fin 120, StrM (M := M) k ν)
      = (c - K (wdual ν) (wdual (ν + twoRho)))
        * (Module.finrank ℂ ↥(Wt (M := M) ν) : ℂ) := by
  have h1 : traceOmegaM (M := M) c hc ν
      = c * (Module.finrank ℂ ↥(Wt (M := M) ν) : ℂ) := traceOmegaM_eq (M := M) c hc ν
  have h2 : traceOmegaM (M := M) c hc ν
      = K (wdual ν) (wdual ν) * (Module.finrank ℂ ↥(Wt (M := M) ν) : ℂ)
        + (∑ k : Fin 120, TtrM (M := M) k ν) + (∑ k : Fin 120, StrM (M := M) k ν) := by
    rw [traceOmegaM_eq_sum, sum_cartanM]
  have h3 := sum_TtrM_eq (M := M) ν
  have hK : K (wdual ν) (wdual (ν + twoRho))
      = K (wdual ν) (wdual ν) + K (wdual ν) (wdual twoRho) := by
    rw [wdual_add, map_add]
  have key : c * (Module.finrank ℂ ↥(Wt (M := M) ν) : ℂ)
      = K (wdual ν) (wdual ν) * (Module.finrank ℂ ↥(Wt (M := M) ν) : ℂ)
        + ((∑ k : Fin 120, StrM (M := M) k ν)
          + K (wdual ν) (wdual twoRho) * (Module.finrank ℂ ↥(Wt (M := M) ν) : ℂ))
        + (∑ k : Fin 120, StrM (M := M) k ν) := by
    rw [← h1, h2, h3]
  rw [sub_mul, key, hK, add_mul]
  ring

variable [Module.Finite ℂ M]

instance wtFinite (ν : Fin 8 → ℤ) : Module.Finite ℂ ↥(Wt (M := M) ν) :=
  Module.Finite.of_injective (Submodule.subtype (Wt (M := M) ν)) Subtype.coe_injective

open UniversalEnvelopingAlgebra in
/-- The trace `S` vanishes on a trivial weight space. -/
lemma StrM_eq_zero_of_wt_bot (k : Fin 120) {σ : Fin 8 → ℤ} (h : Wt (M := M) σ = ⊥) :
    StrM (M := M) k σ = 0 := by
  have : Subsingleton ↥(Wt (M := M) σ) := ⟨fun a b => Subtype.ext (by
    have ha : (a : M) = 0 :=
      (Submodule.mem_bot ℂ).mp (show (a : M) ∈ (⊥ : Submodule ℂ M) from h ▸ a.2)
    have hb : (b : M) = 0 :=
      (Submodule.mem_bot ℂ).mp (show (b : M) ∈ (⊥ : Submodule ℂ M) from h ▸ b.2)
    rw [ha, hb])⟩
  haveI := this
  have hz : FEmapM (M := M) k σ = 0 := Subsingleton.elim _ _
  rw [StrM, hz, map_zero]

/-- The weight `ν + s·α` on the `α`-string through `ν`. -/
def shM (k : Fin 120) (ν : Fin 8 → ℤ) (s : ℕ) : Fin 8 → ℤ := ν + (s : ℤ) • pR k

lemma shM_zero (k : Fin 120) (ν : Fin 8 → ℤ) : shM k ν 0 = ν := by
  simp [shM]

lemma shM_succ (k : Fin 120) (ν : Fin 8 → ℤ) (s : ℕ) : shM k ν (s + 1) = shM k ν s + pR k := by
  simp only [shM, Nat.cast_succ, add_smul, one_smul]
  abel

open UniversalEnvelopingAlgebra in
/-- **Unfolding of the trace recursion.** -/
lemma StrM_eq_sum (k : Fin 120) (ν : Fin 8 → ℤ) (n : ℕ) :
    StrM (M := M) k ν = StrM (M := M) k (shM k ν n)
      + ∑ s ∈ Finset.Icc 1 n,
          K (wdual (shM k ν s)) (wdual (pR k))
            * (Module.finrank ℂ ↥(Wt (M := M) (shM k ν s)) : ℂ) := by
  induction n with
  | zero =>
      rw [Finset.Icc_eq_empty (by norm_num : ¬ (1 ≤ 0)), Finset.sum_empty, shM_zero, add_zero]
  | succ n ih =>
      have hsplit :
          (∑ s ∈ Finset.Icc 1 (n + 1),
              K (wdual (shM k ν s)) (wdual (pR k))
                * (Module.finrank ℂ ↥(Wt (M := M) (shM k ν s)) : ℂ))
            = (∑ s ∈ Finset.Icc 1 n,
                K (wdual (shM k ν s)) (wdual (pR k))
                  * (Module.finrank ℂ ↥(Wt (M := M) (shM k ν s)) : ℂ))
              + K (wdual (shM k ν (n + 1))) (wdual (pR k))
                * (Module.finrank ℂ ↥(Wt (M := M) (shM k ν (n + 1))) : ℂ) :=
        Finset.sum_Icc_succ_top (M := ℂ) (by omega : 1 ≤ n + 1) _
      rw [ih, hsplit, shM_succ, StrM_step (M := M) k (shM k ν n)]
      ring

open UniversalEnvelopingAlgebra in
/-- The trace `S` vanishes when the weight lies above `Λ`. -/
lemma StrM_eq_zero_of_htOf_neg (k : Fin 120) {Λ σ : Fin 8 → ℤ}
    (hsupp : ∀ τ : Fin 8 → ℤ, Wt (M := M) τ = ⊥ ∨ 0 ≤ htOf (Λ - τ))
    (h : htOf (Λ - σ) < 0) : StrM (M := M) k σ = 0 := by
  have h2 : htOf (Λ - (σ + pR k)) < 0 := by
    have he : htOf (Λ - (σ + pR k)) = htOf (Λ - σ) - htOf (pR k) := by
      simp only [htOf_sub, htOf_add]
      ring
    have hp : 0 < htOf (pR k) := htOf_pR_pos k
    omega
  have hb : Wt (M := M) (σ + pR k) = ⊥ := by
    rcases hsupp (σ + pR k) with h' | h'
    · exact h'
    · omega
  have hsh : shM k σ 1 = σ + pR k := by rw [shM_succ, shM_zero]
  have hdm : (Module.finrank ℂ ↥(Wt (M := M) (σ + pR k)) : ℂ) = 0 := by
    rw [hb]
    simp
  rw [StrM_eq_sum (M := M) k σ 1, hsh, StrM_eq_zero_of_wt_bot (M := M) k hb,
    Finset.sum_eq_zero (fun s hs => by
      rw [Finset.mem_Icc] at hs
      have : s = 1 := by omega
      subst this
      rw [hsh, hdm]
      simp), add_zero]

open UniversalEnvelopingAlgebra in
/-- The trace `S` vanishes at the end of the truncated `α`-string. -/
lemma StrM_last_zero (k : Fin 120) (ν : Fin 8 → ℤ) {Λ : Fin 8 → ℤ}
    (hsupp : ∀ τ : Fin 8 → ℤ, Wt (M := M) τ = ⊥ ∨ 0 ≤ htOf (Λ - τ))
    (hcon : 0 ≤ htOf (Λ - ν)) :
    StrM (M := M) k (shM k ν ((htOf (Λ - ν)).toNat)) = 0 := by
  set n := (htOf (Λ - ν)).toNat with hn
  have hle : htOf (Λ - ν) ≤ (n : ℤ) := by
    rw [hn, Int.toNat_of_nonneg hcon]
  have hα : 1 ≤ htOf (pR k) := htOf_pR k
  have hgt : htOf (Λ - (shM k ν n + pR k)) < 0 := by
    have he : htOf (Λ - (shM k ν n + pR k))
        = htOf (Λ - ν) - ((n : ℤ) + 1) * htOf (pR k) := by
      simp only [shM, htOf_sub, htOf_add, htOf_smul_int]
      ring
    rw [he]
    have h1 : ((n : ℤ) + 1) * htOf (pR k) ≥ (n : ℤ) + 1 := by nlinarith
    linarith
  have hb : Wt (M := M) (shM k ν n + pR k) = ⊥ := by
    rcases hsupp (shM k ν n + pR k) with h' | h'
    · exact h'
    · omega
  have hdm : (Module.finrank ℂ ↥(Wt (M := M) (shM k ν n + pR k)) : ℂ) = 0 := by
    rw [hb]; simp
  have hsh : shM k (shM k ν n) 1 = shM k ν n + pR k := by rw [shM_succ, shM_zero]
  rw [StrM_eq_sum (M := M) k (shM k ν n) 1, hsh, StrM_eq_zero_of_wt_bot (M := M) k hb,
    Finset.sum_eq_zero (fun s hs => by
      rw [Finset.mem_Icc] at hs
      have hs1 : s = 1 := by omega
      subst hs1
      rw [hsh, hdm]
      simp), add_zero]

/-! ## The Freudenthal recursion in the Weyl normalisation -/

/-- The Casimir eigenvalue attached to a weight `Λ` (in the Weyl normalisation). -/
noncomputable def casOf (Λ : Fin 8 → ℤ) : ℂ := K (wdual Λ) (wdual (Λ + twoRho))

/-- The Casimir eigenvalue of a weight, in the Weyl normalisation. -/
lemma cnu_eq_gen (ν : Fin 8 → ℤ) :
    K (wdual ν) (wdual (ν + twoRho)) = (1 / 60) * ((((Bint ν - Bint 0) : ℤ)) : ℂ) := by
  rw [Submission.E8Freudenthal.cnu_eq, Submission.E8Freudenthal.bil_twoRho,
    Submission.E8Freudenthal.sum_rhoZ]

open UniversalEnvelopingAlgebra in
/-- `StrM` in the Weyl normalisation. -/
lemma StrM_eq_bil (k : Fin 120) (ν : Fin 8 → ℤ) {Λ : Fin 8 → ℤ}
    (hsupp : ∀ τ : Fin 8 → ℤ, Wt (M := M) τ = ⊥ ∨ 0 ≤ htOf (Λ - τ))
    (hcon : 0 ≤ htOf (Λ - ν)) :
    StrM (M := M) k ν = (1 / 60) * ∑ s ∈ Finset.Icc 1 (htOf (Λ - ν)).toNat,
        ((brk (ν + s • pR k) k : ℤ) : ℂ)
          * (Module.finrank ℂ ↥(Wt (M := M) (ν + s • pR k)) : ℂ) := by
  rw [StrM_eq_sum (M := M) k ν ((htOf (Λ - ν)).toNat),
    StrM_last_zero (M := M) k ν hsupp hcon, zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hsh : shM k ν s = ν + s • pR k := by
    simp only [shM, Nat.cast_smul_eq_nsmul]
  rw [Submission.E8Freudenthal.K_wdual_pR, hsh]
  ring

open UniversalEnvelopingAlgebra in
/-- The trace `S` in the Weyl normalisation, multiplied by `60`. -/
lemma sixty_StrM_eq (k : Fin 120) (ν : Fin 8 → ℤ) {Λ : Fin 8 → ℤ}
    (hsupp : ∀ τ : Fin 8 → ℤ, Wt (M := M) τ = ⊥ ∨ 0 ≤ htOf (Λ - τ))
    (hcon : 0 ≤ htOf (Λ - ν)) :
    (60 : ℂ) * StrM (M := M) k ν = ∑ s ∈ Finset.Icc 1 (htOf (Λ - ν)).toNat,
        ((brk (ν + s • pR k) k : ℤ) : ℂ)
          * (Module.finrank ℂ ↥(Wt (M := M) (ν + s • pR k)) : ℂ) := by
  rw [StrM_eq_bil (M := M) k ν hsupp hcon, ← mul_assoc,
    show (60 : ℂ) * (1 / 60) = 1 by norm_num, one_mul]

open UniversalEnvelopingAlgebra in
/-- The Casimir eigenvalue difference, multiplied by `60`. -/
lemma sixty_cas_sub (Λ : Fin 8 → ℤ) (ν : Fin 8 → ℤ) :
    (60 : ℂ) * (casOf Λ - K (wdual ν) (wdual (ν + twoRho)))
      = ((Bint Λ - Bint ν : ℤ) : ℂ) := by
  rw [casOf, cnu_eq_gen Λ, cnu_eq_gen ν]
  push_cast
  ring

open UniversalEnvelopingAlgebra in
/-- **The Freudenthal recursion** for the multiplicities of a finite-dimensional module on which
the Casimir acts by the scalar attached to `Λ`. -/
theorem freudenthal_recursion (Λ : Fin 8 → ℤ)
    (hc : endM (M := M) Omega = casOf Λ • 1)
    (hsupp : ∀ τ : Fin 8 → ℤ, Wt (M := M) τ = ⊥ ∨ 0 ≤ htOf (Λ - τ))
    (ν : Fin 8 → ℤ) (hcon : 0 ≤ htOf (Λ - ν)) :
    ((Bint Λ - Bint ν : ℤ) : ℚ) * (Module.finrank ℂ ↥(Wt (M := M) ν) : ℚ)
      = 2 * ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (Λ - ν)).toNat,
          ((brk (ν + k • pR j) j : ℤ) : ℚ)
            * (Module.finrank ℂ ↥(Wt (M := M) (ν + k • pR j)) : ℚ) := by
  have hgoal : (((Bint Λ : ℤ) : ℂ) - ((Bint ν : ℤ) : ℂ))
        * (Module.finrank ℂ ↥(Wt (M := M) ν) : ℂ)
      = 2 * ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (Λ - ν)).toNat,
          ((brk (ν + k • pR j) j : ℤ) : ℂ)
            * (Module.finrank ℂ ↥(Wt (M := M) (ν + k • pR j)) : ℂ) := by
    have hsum : (60 : ℂ) * (∑ k : Fin 120, StrM (M := M) k ν)
        = ∑ k : Fin 120, ∑ s ∈ Finset.Icc 1 (htOf (Λ - ν)).toNat,
            ((brk (ν + s • pR k) k : ℤ) : ℂ)
              * (Module.finrank ℂ ↥(Wt (M := M) (ν + s • pR k)) : ℂ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => sixty_StrM_eq (M := M) k ν hsupp hcon)
    have h := congrArg (fun z : ℂ => (60 : ℂ) * z)
      (two_sum_StrM (M := M) (casOf Λ) hc ν)
    rw [← mul_assoc (60 : ℂ) (2 : ℂ),
      ← mul_assoc (60 : ℂ) (casOf Λ - K (wdual ν) (wdual (ν + twoRho))),
      sixty_cas_sub] at h
    rw [show (60 : ℂ) * 2 * (∑ k : Fin 120, StrM (M := M) k ν)
        = 2 * ((60 : ℂ) * ∑ k : Fin 120, StrM (M := M) k ν)
        from by ring, hsum] at h
    rw [h, Int.cast_sub]
  apply (Rat.cast_injective (α := ℂ))
  push_cast
  exact hgoal


/-! ## The Casimir on a cyclic module generated by a primitive vector

The Freudenthal recursion of the main theorem needs two inputs beyond the module structure: that the
Casimir acts by the *scalar* `casOf ν`, and that the weights lie in the cone `ν - ℕΦ⁺`.  Both are
supplied here for a module which is *cyclic* on a vector `z` killed by the simple raising operators
`SerreE i` and of Cartan weight `ν`.

The support bound is the commons lemma
`Commons.Algebra.Lie.SerreConstruction.weight_support_of_primitive`; the scalar action is obtained
from `Submission.E8Casimir.Omega_smul_highest_weight` (which needs `z` killed by *every* positive
root vector — this is where the support bound is used: a positive root vector `eRoot k` with
`eRoot k • z ≠ 0` would produce a weight `ν + pR k`, contradicting the support) together with the
cyclicity. -/

section Cyclic

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [Module U M] [IsScalarTower ℂ U M]

/-- **A positive root vector kills a primitive vector.**  If `z` generates the module and is a
lowest-`E`-weight vector of weight `ν`, then `eRoot k • z = 0` for every positive root `k`: a
non-zero `eRoot k • z` has Cartan weight `ν + pR k`, so by the support bound `pR k ∈ ℕΦ⁺` is
orthogonal to `ν - (ν + pR k)`, i.e. `pR k = 0`, absurd. -/
lemma eRoot_smul_eq_zero_of_cyclic [LieRingModule L8 M] [LieModule ℂ L8 M]
    (z : M) (ν : Fin 8 → ℤ)
    (hgen : ∀ m : M, ∃ u : U, u • z = m)
    (hE : ∀ i, UniversalEnvelopingAlgebra.ι ℂ (SerreE i) • z = 0)
    (hH : ∀ i, UniversalEnvelopingAlgebra.ι ℂ (SerreH i) • z = ((ν i : ℤ) : ℂ) • z)
    (k : Fin 120) : UniversalEnvelopingAlgebra.ι ℂ (eRoot k) • z = 0 := by
  by_contra hne
  have hz : z ∈ Wt (M := M) ν := mem_Wt_iff.mpr hH
  have hmem : UniversalEnvelopingAlgebra.ι ℂ (eRoot k) • z ∈ Wt (M := M) (ν + pR k) := by
    have h := endM_iota_mem_Wt (M := M) (pR k) (eRoot_mem k) hz
    rwa [endM_apply] at h
  have hxw := mem_Wt_iff.mp hmem
  have hsupp := Commons.Algebra.Lie.SerreConstruction.weight_support_of_primitive
    (M := M) z ν hgen hE hH hne hxw
  have hzero : ∀ i : Fin 8, coords (pR k) i = 0 := by
    intro i
    have h1 : 0 ≤ coords (ν - (ν + pR k)) i := hsupp i
    have h2 : coords (ν - (ν + pR k)) i = - coords (pR k) i := by
      rw [Submission.E8Enum.coords_sub, coords_add]
      simp
    have h3 := posCon_pR k i
    rw [h2] at h1
    omega
  exact pR_ne_zero k (by
    rw [← mulVec_coords (pR k)]
    have hc : coords (pR k) = 0 := funext hzero
    rw [hc, Matrix.mulVec_zero])

/-- **The support condition**: for a module cyclic on a primitive vector of weight `ν`, every weight
`τ` satisfies `0 ≤ htOf (ν - τ)` (the weight spaces off the cone vanish). -/
theorem Wt_eq_bot_or_le_htOf_of_cyclic [LieRingModule L8 M] [LieModule ℂ L8 M]
    (z : M) (ν : Fin 8 → ℤ)
    (hgen : ∀ m : M, ∃ u : U, u • z = m)
    (hE : ∀ i, UniversalEnvelopingAlgebra.ι ℂ (SerreE i) • z = 0)
    (hH : ∀ i, UniversalEnvelopingAlgebra.ι ℂ (SerreH i) • z = ((ν i : ℤ) : ℂ) • z)
    (τ : Fin 8 → ℤ) : Wt (M := M) τ = ⊥ ∨ 0 ≤ htOf (ν - τ) := by
  by_cases h : Wt (M := M) τ = ⊥
  · exact Or.inl h
  · refine Or.inr ?_
    obtain ⟨x, hx, hx0⟩ := (Wt (M := M) τ).ne_bot_iff.mp h
    have hsupp := Commons.Algebra.Lie.SerreConstruction.weight_support_of_primitive
      (M := M) z ν hgen hE hH hx0 (mem_Wt_iff.mp hx)
    rw [htOf_eq]
    exact Finset.sum_nonneg fun i _ => hsupp i

/-- **The Casimir acts on a cyclic highest-weight module by the scalar `casOf ν`.** -/
theorem endM_Omega_of_cyclic [LieRingModule L8 M] [LieModule ℂ L8 M]
    (z : M) (ν : Fin 8 → ℤ)
    (hgen : ∀ m : M, ∃ u : U, u • z = m)
    (hE : ∀ i, UniversalEnvelopingAlgebra.ι ℂ (SerreE i) • z = 0)
    (hH : ∀ i, UniversalEnvelopingAlgebra.ι ℂ (SerreH i) • z = ((ν i : ℤ) : ℂ) • z)
    (hι : ∀ (x : L8) (m : M), (UniversalEnvelopingAlgebra.ι ℂ x) • m = ⁅x, m⁆) :
    endM (M := M) Omega = casOf ν • 1 := by
  have he : ∀ k : Fin 120, ⁅eRoot k, z⁆ = 0 := fun k => by
    rw [← hι (eRoot k) z]
    exact eRoot_smul_eq_zero_of_cyclic (M := M) z ν hgen hE hH k
  have hv : ∀ i, ⁅SerreH i, z⁆ = ((ν i : ℤ) : ℂ) • z := fun i => by
    rw [← hι (SerreH i) z]
    exact hH i
  have hz := Submission.E8Casimir.Omega_smul_highest_weight (M := M) hι ν hv he
  ext m
  simp only [endM_apply, LinearMap.smul_apply, Module.End.one_apply]
  obtain ⟨u, rfl⟩ := hgen m
  calc Omega • (u • z) = (Omega * u) • z := (mul_smul _ _ _).symm
    _ = (u * Omega) • z := by rw [Submission.E8Casimir.Omega_mul_comm]
    _ = u • (Omega • z) := mul_smul _ _ _
    _ = u • (casOf ν • z) := by rw [show Omega • z = casOf ν • z from hz]
    _ = casOf ν • (u • z) :=
        Submission.Enveloping.module_smul_comm_scalar (R := ℂ) (L := L8) u (casOf ν) z

/-- **The Freudenthal recursion for the weight multiplicities of a cyclic highest-weight module**:
if `M` is generated by a primitive vector `z` of weight `ν`, then for every weight `μ` in the cone
the weight multiplicities of `M` satisfy the Freudenthal recursion with top weight `ν`. -/
theorem freudenthal_recursion_of_cyclic [LieRingModule L8 M] [LieModule ℂ L8 M]
    [Module.Finite ℂ M]
    (z : M) (ν : Fin 8 → ℤ)
    (hgen : ∀ m : M, ∃ u : U, u • z = m)
    (hE : ∀ i, UniversalEnvelopingAlgebra.ι ℂ (SerreE i) • z = 0)
    (hH : ∀ i, UniversalEnvelopingAlgebra.ι ℂ (SerreH i) • z = ((ν i : ℤ) : ℂ) • z)
    (hι : ∀ (x : L8) (m : M), (UniversalEnvelopingAlgebra.ι ℂ x) • m = ⁅x, m⁆)
    (μ : Fin 8 → ℤ) (hcon : 0 ≤ htOf (ν - μ)) :
    ((Bint ν - Bint μ : ℤ) : ℚ) * (Module.finrank ℂ ↥(Wt (M := M) μ) : ℚ)
      = 2 * ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (ν - μ)).toNat,
          ((brk (μ + k • pR j) j : ℤ) : ℚ)
            * (Module.finrank ℂ ↥(Wt (M := M) (μ + k • pR j)) : ℚ) :=
  freudenthal_recursion (M := M) ν
    (endM_Omega_of_cyclic (M := M) z ν hgen hE hH hι)
    (Wt_eq_bot_or_le_htOf_of_cyclic (M := M) z ν hgen hE hH) μ hcon

end Cyclic

end Submission.E8FreudenthalGen
