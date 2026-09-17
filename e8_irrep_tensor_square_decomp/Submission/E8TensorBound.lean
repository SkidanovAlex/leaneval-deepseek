import Submission.E8Tensor
import Submission.Commons.Algebra.Lie.CompleteReducibility.isSemisimpleModule_enveloping
import Submission.Commons.Algebra.Lie.SerreConstruction.exists_dominant_primitive_of_ne_bot
import Submission.Commons.Algebra.Lie.SerreConstruction.lieEquiv_of_same_primitive_weight
import Submission.Commons.RepresentationTheory.LieEnveloping.adjoin_range_iota

/-!
# The support bound and the weight decomposition of the tensor square

This file refines the weight structure of the tensor square `T N = (V ⧸ N) ⊗[ℂ] (V ⧸ N)`
built in `Submission.E8Tensor`:

* `exists_decomp_TLwt` — every element of `T N` is a finite sum of weight components;
* `posCon_of_mem_TLwt` — **the support bound for an arbitrary weight vector**: a non-zero
  `x ∈ TLwt N ν` has `2λ - ν ∈ ℕΦ⁺`, so `ν` is a dominant weight in the cone below `2λ`
  (`mem_the40`);
* the killer operators `killerT` and their products, giving `mem_TLwt_of_deriv_h_eq`: a vector on
  which every Cartan generator acts by the scalar `νⱼ` lies in `TLwt N ν`.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

noncomputable section
open scoped TensorProduct BigOperators

namespace Submission.E8TensorBound

open Submission.E8Tensor
open Submission.VermaWeight
open Submission.E8WeightSpaces
open UniversalEnvelopingAlgebra
open Submission.E8Character (posCon posCon_add)

variable {N : Submodule U V}

/-- Every element of the tensor square is a finite sum of weight components. -/
lemma exists_decomp_TLwt (x : T N) :
    ∃ (s : Finset (Fin 8 → ℤ)) (y : (Fin 8 → ℤ) → T N),
      (∀ μ ∈ s, y μ ∈ TLwt N μ) ∧ x = ∑ μ ∈ s, y μ := by
  classical
  have hx : x ∈ ⨆ μ : Fin 8 → ℤ, TLwt N μ := by rw [iSup_TLwt_eq_top]; trivial
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hx
  obtain ⟨y, hy⟩ := (Submodule.mem_iSup_finset_iff_exists_sum (fun μ => TLwt N μ) x).mp hs
  exact ⟨s, fun μ => y μ, fun μ _ => (y μ).2, hy.symm⟩

/-! ## The support bound for an arbitrary weight vector of the tensor square -/

/-- The set of pure tensors whose factors have weights summing to `ν`. -/
def tmulSet (N : Submodule U V) (ν : Fin 8 → ℤ) : Set (T N) :=
  {x : T N | ∃ (ν₁ ν₂ : Fin 8 → ℤ), ν₁ + ν₂ = ν ∧
    ∃ a ∈ Lwt N ν₁, ∃ b ∈ Lwt N ν₂, x = a ⊗ₜ[ℂ] b}

lemma TLwt_eq_span (N : Submodule U V) (ν : Fin 8 → ℤ) :
    TLwt N ν = Submodule.span ℂ (tmulSet N ν) := rfl

/-- **The support bound** for an arbitrary non-zero weight vector of the tensor square: its
weight lies in the cone `2λ - ℕΦ⁺`. -/
lemma posCon_of_mem_TLwt {ν : Fin 8 → ℤ} {x : T N} (hx : x ∈ TLwt N ν) (hx0 : x ≠ 0) :
    posCon (2 • Submission.E8Enum.lam - ν) := by
  classical
  have key : ∀ y : T N, y ∈ TLwt N ν → y ≠ 0 → posCon (2 • Submission.E8Enum.lam - ν) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        intro hz0
        obtain ⟨ν₁, ν₂, hsum, a, ha, b, hb, rfl⟩ := hz
        subst hsum
        exact posCon_two_lam_of_tmul ha (fun h => hz0 (by rw [h, TensorProduct.zero_tmul]))
          hb (fun h => hz0 (by rw [h, TensorProduct.tmul_zero]))
    | zero => intro h; exact absurd rfl h
    | add p q _ _ ihp ihq =>
        intro hpq
        by_cases hp0 : p = 0
        · exact ihq (by simpa [hp0] using hpq)
        · exact ihp hp0
    | smul c p _ ih =>
        intro hp0
        by_cases hc : c = 0
        · exact absurd (by rw [hc, zero_smul]) hp0
        · exact ih fun h => hp0 (by rw [h, smul_zero])
  exact key x hx hx0

/-! ## The killer operators -/

/-- `killMul c a b x` is the elementary identity `c • (a • x - b • x) = (c * (a - b)) • x`. -/
lemma killMul (c a b : ℂ) (x : T N) : c • (a • x - b • x) = (c * (a - b)) • x := by
  calc c • (a • x - b • x) = c • ((a - b) • x) :=
        congrArg (fun z => c • z) ((sub_smul a b x).symm)
    _ = (c * (a - b)) • x := smul_smul c (a - b) x

/-- The operator `(ν j - μ j)⁻¹ (H_j - μ_j)` on the tensor square: it kills `TLwt N μ` and (when
`μ j ≠ ν j`) fixes `TLwt N ν`. -/
noncomputable def killerT (ν μ : Fin 8 → ℤ) (j : Fin 8) : Module.End ℂ (T N) :=
  (((ν j - μ j : ℤ)) : ℂ)⁻¹ •
    (deriv (N := N) (Submission.E8Weights.SerreH j) -
      (((μ j : ℤ)) : ℂ) • (1 : Module.End ℂ (T N)))

lemma killerT_apply {ν μ : Fin 8 → ℤ} (j : Fin 8) {ξ : Fin 8 → ℤ} {x : T N}
    (hx : x ∈ TLwt N ξ) :
    killerT (N := N) ν μ j x
      = ((((ν j - μ j : ℤ)) : ℂ)⁻¹ * ((((ξ j : ℤ)) : ℂ) - (((μ j : ℤ)) : ℂ))) • x := by
  rw [killerT, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, deriv_h_eq_of_mem_TLwt (N := N) j hx]
  exact killMul _ _ _ _

lemma killerT_mem {ν μ : Fin 8 → ℤ} (j : Fin 8) {ξ : Fin 8 → ℤ} {x : T N}
    (hx : x ∈ TLwt N ξ) : killerT (N := N) ν μ j x ∈ TLwt N ξ := by
  rw [killerT_apply (N := N) j hx]
  exact Submodule.smul_mem _ _ hx

lemma killerT_kills {ν μ : Fin 8 → ℤ} (j : Fin 8) {x : T N} (hx : x ∈ TLwt N μ) :
    killerT (N := N) ν μ j x = 0 := by
  rw [killerT_apply (N := N) j hx]
  rw [sub_self, mul_zero, zero_smul]

lemma killerT_fixes {ν μ : Fin 8 → ℤ} {j : Fin 8} (hj : μ j ≠ ν j) {x : T N}
    (hx : x ∈ TLwt N ν) : killerT (N := N) ν μ j x = x := by
  rw [killerT_apply (N := N) j hx]
  have hne' : ((((ν j - μ j : ℤ)) : ℂ)) ≠ 0 := by
    have h0 : (ν j - μ j : ℤ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hj)
    exact fun h => h0 (Int.cast_eq_zero.mp h)
  have hcast : ((((ν j - μ j : ℤ)) : ℂ)) = ((((ν j : ℤ)) : ℂ)) - ((((μ j : ℤ)) : ℂ)) :=
    Int.cast_sub ..
  rw [← hcast, inv_mul_cancel₀ hne', one_smul]

/-- `killerT` fixes a vector on which `H_j` acts by the scalar `ν j`. -/
lemma killerT_eigen {ν μ : Fin 8 → ℤ} {j : Fin 8} (hj : μ j ≠ ν j) {x : T N}
    (hx : deriv (N := N) (Submission.E8Weights.SerreH j) x = (((ν j : ℤ)) : ℂ) • x) :
    killerT (N := N) ν μ j x = x := by
  rw [killerT, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, hx]
  have hne' : ((((ν j - μ j : ℤ)) : ℂ)) ≠ 0 := by
    have h0 : (ν j - μ j : ℤ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hj)
    exact fun h => h0 (Int.cast_eq_zero.mp h)
  have hcast : ((((ν j - μ j : ℤ)) : ℂ)) = ((((ν j : ℤ)) : ℂ)) - ((((μ j : ℤ)) : ℂ)) :=
    Int.cast_sub ..
  rw [killMul, ← hcast, inv_mul_cancel₀ hne', one_smul]

/-- The property that an endomorphism fixes every vector on which the Cartan acts by `ν`. -/
def FixEig (P : Module.End ℂ (T N)) (ν : Fin 8 → ℤ) : Prop :=
  ∀ y : T N, (∀ j, deriv (N := N) (Submission.E8Weights.SerreH j) y = (((ν j : ℤ)) : ℂ) • y)
    → P y = y

/-- **The killer product for the tensor square.**  For a finite set `s` of weights not containing
`ν` there is an endomorphism `P` of `T N` which preserves all weight spaces, fixes `TLwt N ν`,
kills `TLwt N μ` for every `μ ∈ s`, and fixes every vector on which the Cartan acts by `ν`. -/
lemma exists_killerT (s : Finset (Fin 8 → ℤ)) (ν : Fin 8 → ℤ) (hne : ∀ μ ∈ s, μ ≠ ν) :
    ∃ P : Module.End ℂ (T N),
      (∀ ξ : Fin 8 → ℤ, ∀ y : T N, y ∈ TLwt N ξ → P y ∈ TLwt N ξ) ∧
      (∀ y : T N, y ∈ TLwt N ν → P y = y) ∧
      (∀ μ ∈ s, ∀ y : T N, y ∈ TLwt N μ → P y = 0) ∧
      FixEig (N := N) P ν := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, fun ξ y hy => by simpa using hy, fun y hy => rfl, ?_, ?_⟩
      · intro μ hμ
        exact absurd hμ (Finset.notMem_empty μ)
      · intro y hy
        rfl
  | insert a s' ha ih =>
      obtain ⟨P', hpres', hfix', hkill', heig'⟩ :=
        ih (fun μ hμ => hne μ (Finset.mem_insert_of_mem hμ))
      obtain ⟨j, hj⟩ : ∃ j : Fin 8, a j ≠ ν j :=
        Function.ne_iff.mp (hne a (Finset.mem_insert_self a s'))
      refine ⟨(killerT (N := N) ν a j).comp P', ?_, ?_, ?_, ?_⟩
      · intro ξ y hy
        exact killerT_mem (N := N) j (hpres' ξ y hy)
      · intro y hy
        exact (congrArg (fun z => killerT (N := N) ν a j z) (hfix' y hy)).trans
          (killerT_fixes (N := N) hj hy)
      · intro μ hμ y hy
        rcases Finset.mem_insert.mp hμ with h | h
        · subst h
          exact killerT_kills (N := N) j (hpres' μ y hy)
        · exact (congrArg (fun z => killerT (N := N) ν a j z) (hkill' μ h y hy)).trans
            (map_zero _)
      · intro y hy
        exact (congrArg (fun z => killerT (N := N) ν a j z) (heig' y hy)).trans
          (killerT_eigen (N := N) hj (hy j))

/-- **A vector on which the Cartan acts by the scalars `ν j` lies in the weight space `TLwt N ν`.** -/
lemma mem_TLwt_of_deriv_h_eq (ν : Fin 8 → ℤ) (x : T N)
    (h : ∀ j, deriv (N := N) (Submission.E8Weights.SerreH j) x = (((ν j : ℤ)) : ℂ) • x) :
    x ∈ TLwt N ν := by
  classical
  obtain ⟨s, y, hy, hsum⟩ := exists_decomp_TLwt (N := N) x
  obtain ⟨P, hpres, hfix, hkill, heig⟩ :=
    exists_killerT (N := N) (s.erase ν) ν (fun μ hμ => Finset.ne_of_mem_erase hμ)
  have h1 : P x = x := heig x h
  have h2 : x = ∑ μ ∈ s, (if μ = ν then y μ else 0) := by
    rw [← h1, hsum, map_sum]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    by_cases hμν : μ = ν
    · subst hμν; rw [if_pos rfl]; exact hfix (y μ) (hy μ hμ)
    · rw [if_neg hμν]
      exact hkill μ (Finset.mem_erase.mpr ⟨hμν, hμ⟩) (y μ) (hy μ hμ)
  rw [Finset.sum_ite_eq' s ν y] at h2
  by_cases hν : ν ∈ s
  · rw [h2, if_pos hν]; exact hy ν hν
  · rw [h2, if_neg hν]; exact Submodule.zero_mem _



/-! ## The upper bound on the number of isotypic components -/

section Upper

open Submission.E8Enum

/-- The derivation Lie structure on the tensor square (the tensor product action). -/
noncomputable instance instLieRingT (N : Submodule U V) :
    LieRingModule (LieAlgebra.e₈ ℂ) (T N) := TensorProduct.LieModule.lieRingModule

/-- The derivation Lie module structure on the tensor square. -/
noncomputable instance instLieT (N : Submodule U V) :
    LieModule ℂ (LieAlgebra.e₈ ℂ) (T N) := TensorProduct.LieModule.lieModule

/-- The algebra homomorphism giving the action of the enveloping algebra on the tensor square. -/
noncomputable def uEnd (N : Submodule U V) : U →ₐ[ℂ] Module.End ℂ (T N) :=
  UniversalEnvelopingAlgebra.lift ℂ (LieModule.toEnd ℂ (LieAlgebra.e₈ ℂ) (T N))

/-- The `U(e₈)`-module structure on the tensor square, through the derivation action. -/
@[reducible] noncomputable instance (priority := 5000) instModT (N : Submodule U V) : Module U (T N) :=
  { Module.compHom (T N) (uEnd N).toRingHom with
    smul := fun u m => uEnd N u m }

/-- The instance `instModT` agrees with the enveloping-module structure of the framework. -/
example (N : Submodule U V) : instModT N =
    LeanEval.RepresentationTheory.lieModuleToEnvelopingModule ℂ (LieAlgebra.e₈ ℂ) (T N) := rfl

example (N : Submodule U V) : (inferInstance : Module U (T N)) = instModT N := rfl

/-- The scalar action of the enveloping algebra on the tensor square, at high priority. -/
instance (priority := 10000) instSMulT (N : Submodule U V) : SMul U (T N) := (instModT N).toSMul

/-- The enveloping-algebra module structure on a `U(e₈)`-submodule, at high priority. -/
instance (priority := 10000) instModuleUSub (S : Submodule U (T N)) : Module U ↥S :=
  Submodule.module S

/-- The `ℂ`-scalars and the enveloping algebra action on the tensor square form a scalar tower. -/
instance instISTTensor (N : Submodule U V) : IsScalarTower ℂ U (T N) := by
  refine ⟨fun c u m => ?_⟩
  show (uEnd N (c • u)) m = c • ((uEnd N u) m)
  rw [map_smul]
  rfl

/-- The `ℂ`-module structure on a `U(e₈)`-submodule of the tensor square (restriction of
scalars). -/
noncomputable instance instModuleSubC (S : Submodule U (T N)) : Module ℂ ↥S :=
  inferInstanceAs (Module ℂ ↥(S.restrictScalars ℂ))

instance instISTSub (S : Submodule U (T N)) : IsScalarTower ℂ U ↥S :=
  inferInstanceAs (IsScalarTower ℂ U ↥(S.restrictScalars ℂ))


lemma isSemisimple_tensor (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) : IsSemisimpleModule U (T N) := by
  haveI hk : LieAlgebra.IsKilling ℂ (LieAlgebra.e₈ ℂ) :=
    Commons.Algebra.Lie.SerreConstruction.e8_isKilling
  haveI hf : Module.Finite ℂ (T N) := finite_tensor N hvN hmax
  exact Commons.Algebra.Lie.CompleteReducibility.isSemisimpleModule_enveloping

/-- **A Lie isomorphism of simple submodules of the tensor square is an isomorphism over the
enveloping algebra.** -/
theorem submoduleLinearEquivOfLieEquiv {S S' : Submodule U (T N)}
    (e : ↥S ≃ₗ⁅ℂ, LieAlgebra.e₈ ℂ⁆ ↥S') : Nonempty (S ≃ₗ[U] S') := by
  have key : ∀ u ∈ Algebra.adjoin ℂ (Set.range (UniversalEnvelopingAlgebra.ι ℂ :
      LieAlgebra.e₈ ℂ → U)), ∀ m : ↥S, e (u • m) = u • e m := by
    intro u hu
    induction hu using Algebra.adjoin_induction with
    | mem x hx =>
        rcases hx with ⟨y, rfl⟩
        intro m
        rw [show (UniversalEnvelopingAlgebra.ι ℂ y) • m = ⁅y, m⁆ from rfl,
          show (UniversalEnvelopingAlgebra.ι ℂ y) • (e m) = ⁅y, e m⁆ from rfl]
        exact e.map_lie y m
    | algebraMap c =>
        intro m
        have hm : (algebraMap ℂ U c) • m = c • m := by
          rw [Algebra.algebraMap_eq_smul_one, IsScalarTower.smul_assoc, one_smul]
        have hm' : (algebraMap ℂ U c) • (e m) = c • (e m) := by
          rw [Algebra.algebraMap_eq_smul_one, IsScalarTower.smul_assoc, one_smul]
        rw [hm, hm']
        exact e.map_smul c m
    | add x y _ _ ihx ihy =>
        intro m
        rw [add_smul, map_add, ihx m, ihy m, add_smul]
    | mul x y _ _ ihx ihy =>
        intro m
        rw [mul_smul, ihx (y • m), ihy m, mul_smul]
  refine ⟨{ toFun := fun m => e m
            invFun := fun m => e.symm m
            map_add' := fun a b => map_add e a b
            map_smul' := fun u m => key u ?_ m
            left_inv := fun m => e.left_inv m
            right_inv := fun m => e.right_inv m }⟩
  rw [Commons.RepresentationTheory.LieEnveloping.adjoin_range_iota]
  trivial

/-- A simple submodule of the tensor square has a non-zero primitive vector of a dominant weight
belonging to `the40`. -/
lemma exists_prim_of_simple (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N)
    (S : Submodule U (T N)) (hS : IsSimpleModule U S) :
    ∃ (x : T N) (ν : Fin 8 → ℤ), x ∈ S ∧ x ≠ 0 ∧
      (∀ j, deriv (N := N) (Submission.E8Weights.SerreH j) x = (((ν j : ℤ)) : ℂ) • x) ∧
      (∀ j, deriv (N := N) (Submission.E8Weights.SerreE j) x = 0) ∧
      (∀ j, 0 ≤ ν j) ∧ ν ∈ the40 := by
  classical
  haveI hfin : Module.Finite ℂ (T N) := finite_tensor N hvN hmax
  have hbot : S ≠ ⊥ := by
    intro h
    haveI : Subsingleton ↥S := by rw [h]; infer_instance
    obtain ⟨a, b, hab⟩ := IsSimpleModule.nontrivial U S
    exact hab (Subsingleton.elim a b)
  have hKne : Commons.Algebra.Lie.CompleteReducibility.ofEnveloping S ≠ ⊥ := by
    intro h
    refine hbot (Submodule.ext fun m => ?_)
    constructor
    · intro hm
      rw [Submodule.mem_bot]
      have h1 : m ∈ Commons.Algebra.Lie.CompleteReducibility.ofEnveloping S :=
        (Commons.Algebra.Lie.CompleteReducibility.mem_ofEnveloping S m).mpr hm
      rw [h] at h1
      simpa using h1
    · intro hm
      rw [Submodule.mem_bot] at hm
      rw [hm]
      exact S.zero_mem
  obtain ⟨x, ν, hxN, hx0, hxH, hxE, hνd⟩ :=
    Commons.Algebra.Lie.SerreConstruction.exists_dominant_primitive_of_ne_bot
      (Commons.Algebra.Lie.CompleteReducibility.ofEnveloping S) hKne
  have hxS : x ∈ S := hxN
  have hH' : ∀ j, deriv (N := N) (Submission.E8Weights.SerreH j) x = (((ν j : ℤ)) : ℂ) • x :=
    fun j => hxH j
  have hE' : ∀ j, deriv (N := N) (Submission.E8Weights.SerreE j) x = 0 := fun j => hxE j
  have hpos : posCon (2 • Submission.E8Enum.lam - ν) :=
    posCon_of_mem_TLwt (mem_TLwt_of_deriv_h_eq ν x hH') hx0
  exact ⟨x, ν, hxS, hx0, hH', hE', hνd,
    mem_the40 (allNonneg_true.mpr hνd) (posB_true.mpr hpos)⟩

/-! ## The upper bound on the number of isotypic components -/

/-- The action of `ι x` on the tensor square is the derivation action. -/
lemma iota_smul_eq_deriv (x : LieAlgebra.e₈ ℂ) (m : T N) :
    (UniversalEnvelopingAlgebra.ι ℂ x) • m = deriv (N := N) x m := by
  show uEnd N (UniversalEnvelopingAlgebra.ι ℂ x) m = deriv (N := N) x m
  rw [show uEnd N = UniversalEnvelopingAlgebra.lift ℂ
    (LieModule.toEnd ℂ (LieAlgebra.e₈ ℂ) (T N)) from rfl]
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

/-- The Lie action on a `U(e₈)`-submodule of the tensor square, described through `deriv`. -/
lemma sub_bracket (S : Submodule U (T N)) (x : LieAlgebra.e₈ ℂ) (m : ↥S) :
    ⁅x, m⁆ = (⟨deriv (N := N) x m.1,
      by rw [← iota_smul_eq_deriv (N := N) x m.1]; exact S.smul_mem _ m.2⟩ : ↥S) := by
  apply Subtype.ext
  show (UniversalEnvelopingAlgebra.ι ℂ x) • (m.1 : T N) = deriv (N := N) x m.1
  exact iota_smul_eq_deriv (N := N) x m.1

/-- The data attached to an isotypic component of the tensor square: a simple submodule, a
primitive vector of dominant weight, and the weight itself. -/
structure CompData (N : Submodule U V) (c : isotypicComponents U (T N)) where
  /-- the simple submodule -/
  S : Submodule U (T N)
  /-- the primitive vector -/
  x : T N
  /-- the dominant weight of the primitive vector -/
  ν : Fin 8 → ℤ
  hxS : x ∈ S
  hx0 : x ≠ 0
  hsimp : IsSimpleModule U S
  hH : ∀ j, deriv (N := N) (Submission.E8Weights.SerreH j) x = (((ν j : ℤ)) : ℂ) • x
  hE : ∀ j, deriv (N := N) (Submission.E8Weights.SerreE j) x = 0
  hdom : ∀ j, 0 ≤ ν j
  hmem : ν ∈ Submission.E8Enum.the40
  hcomp : c.val = isotypicComponent U (T N) S

/-- Every non-zero isotypic component of the tensor square carries such data. -/
lemma exists_compData (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (c : isotypicComponents U (T N)) :
    Nonempty (CompData N c) := by
  classical
  haveI hss : IsSemisimpleModule U (T N) := isSemisimple_tensor N hvN hmax
  have hne : c.val ≠ ⊥ := (bot_lt_isotypicComponents c.2).ne'
  rcases IsSemisimpleModule.eq_bot_or_exists_simple_le c.val with h | ⟨S, hSle, hS⟩
  · exact absurd h hne
  · haveI := hS
    obtain ⟨x, ν, hxS, hx0, hH, hE, hdom, hmem⟩ := exists_prim_of_simple N hvN hmax S hS
    exact ⟨⟨S, x, ν, hxS, hx0, hS, hH, hE, hdom, hmem,
      eq_isotypicComponent_of_le c.2 hSle⟩⟩

/-- The chosen data for an isotypic component. -/
noncomputable def compData (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (c : isotypicComponents U (T N)) :
    CompData N c :=
  Classical.choice (exists_compData N hvN hmax c)

/-- **The weight map on the isotypic components of the tensor square is injective.** -/
lemma compData_inj_aux {N : Submodule U V} [Module.Finite ℂ (T N)]
    {c c' : isotypicComponents U (T N)}
    (d : CompData N c) (d' : CompData N c') (h : d.ν = d'.ν) : c = c' := by
  classical
  haveI hst : @IsScalarTower ℂ U ↥d.S (Algebra.toSMul) ((Submodule.module d.S).toSMul)
      ((instModuleSubC d.S).toSMul) := instISTSub d.S
  haveI hst' : @IsScalarTower ℂ U ↥d'.S (Algebra.toSMul) ((Submodule.module d'.S).toSMul)
      ((instModuleSubC d'.S).toSMul) := instISTSub d'.S
  haveI hfin : Module.Finite ℂ ↥d.S := Module.Finite.of_injective
    ({ toFun := fun m => (m : T N), map_add' := fun _ _ => rfl,
       map_smul' := fun _ _ => rfl } : ↥d.S →ₗ[ℂ] T N)
    (fun a b h => Subtype.ext (show (a : T N) = (b : T N) from h))
  haveI hfin' : Module.Finite ℂ ↥d'.S := Module.Finite.of_injective
    ({ toFun := fun m => (m : T N), map_add' := fun _ _ => rfl,
       map_smul' := fun _ _ => rfl } : ↥d'.S →ₗ[ℂ] T N)
    (fun a b h => Subtype.ext (show (a : T N) = (b : T N) from h))
  haveI hI : LieModule.IsIrreducible ℂ (LieAlgebra.e₈ ℂ) ↥d.S := by
    rw [Commons.RepresentationTheory.LieEnveloping.isIrreducible_iff_isSimpleModule (M := ↥d.S)
      (fun x m => rfl)]
    exact d.hsimp
  haveI hI' : LieModule.IsIrreducible ℂ (LieAlgebra.e₈ ℂ) ↥d'.S := by
    rw [Commons.RepresentationTheory.LieEnveloping.isIrreducible_iff_isSimpleModule (M := ↥d'.S)
      (fun x m => rfl)]
    exact d'.hsimp
  have hE' : ∀ i, ⁅Submission.E8Weights.SerreE i, (⟨d'.x, d'.hxS⟩ : ↥d'.S)⁆ = 0 := fun i => by
    rw [sub_bracket]
    exact Subtype.ext (d'.hE i)
  have hH' : ∀ i, ⁅Submission.E8Weights.SerreH i, (⟨d'.x, d'.hxS⟩ : ↥d'.S)⁆ =
      (((d.ν i : ℤ)) : ℂ) • (⟨d'.x, d'.hxS⟩ : ↥d'.S) := fun i => by
    rw [sub_bracket]
    refine Subtype.ext ?_
    show deriv (N := N) (Submission.E8Weights.SerreH i) d'.x = (((d.ν i : ℤ)) : ℂ) • d'.x
    rw [d'.hH i, ← h]
  have hE : ∀ i, ⁅Submission.E8Weights.SerreE i, (⟨d.x, d.hxS⟩ : ↥d.S)⁆ = 0 := fun i => by
    rw [sub_bracket]
    exact Subtype.ext (d.hE i)
  have hH : ∀ i, ⁅Submission.E8Weights.SerreH i, (⟨d.x, d.hxS⟩ : ↥d.S)⁆ =
      (((d.ν i : ℤ)) : ℂ) • (⟨d.x, d.hxS⟩ : ↥d.S) := fun i => by
    rw [sub_bracket]
    exact Subtype.ext (d.hH i)
  obtain ⟨e⟩ := Commons.Algebra.Lie.SerreConstruction.lieEquiv_of_same_primitive_weight hI hI'
    (x := (⟨d.x, d.hxS⟩ : ↥d.S)) (x' := (⟨d'.x, d'.hxS⟩ : ↥d'.S))
    (by intro h0; exact d.hx0 (congrArg Subtype.val h0)) hE hH
    (by intro h0; exact d'.hx0 (congrArg Subtype.val h0)) hE' hH'
  obtain ⟨e'⟩ := submoduleLinearEquivOfLieEquiv e
  have hcomp_eq : isotypicComponent U (T N) d.S = isotypicComponent U (T N) d'.S :=
    LinearEquiv.isotypicComponent_eq e'
  exact Subtype.ext (d.hcomp.trans (hcomp_eq.trans d'.hcomp.symm))

/-- The weight map on the isotypic components of the tensor square is injective. -/
lemma compData_inj (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) {c c' : isotypicComponents U (T N)}
    (h : (compData N hvN hmax c).ν = (compData N hvN hmax c').ν) : c = c' := by
  haveI hf : Module.Finite ℂ (T N) := finite_tensor N hvN hmax
  exact compData_inj_aux (compData N hvN hmax c) (compData N hvN hmax c') h

/-- **The tensor square of `L(ω₁+ω₈)` has at most forty isotypic components.** -/
theorem ncard_tensor_le_forty (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) :
    (isotypicComponents U (T N)).ncard ≤ 40 := by
  classical
  have hcard : ((Submission.E8Enum.the40.toFinset : Set (Fin 8 → ℤ))).ncard = 40 := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup Submission.E8Enum.the40_nodup,
      Submission.E8Enum.the40_length]
  refine le_trans (Set.ncard_le_ncard_of_injOn
    (s := isotypicComponents U (T N))
    (t := (Submission.E8Enum.the40.toFinset : Set (Fin 8 → ℤ)))
    (fun c => if h : c ∈ isotypicComponents U (T N)
      then (compData N hvN hmax ⟨c, h⟩).ν else 0) ?_ ?_) ?_
  · intro c hc
    simp only [dif_pos hc]
    exact Finset.mem_coe.mpr (List.mem_toFinset.mpr (compData N hvN hmax ⟨c, hc⟩).hmem)
  · intro c hc c' hc' h
    simp only [dif_pos hc, dif_pos hc'] at h
    exact Subtype.ext_iff.mp (compData_inj N hvN hmax h)
  · rw [hcard]


end Upper

end Submission.E8TensorBound
