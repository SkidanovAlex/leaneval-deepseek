/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The cohomological shrinking lemma (Proposition 6 of Schmidt–Wingberg)

This file contains the *technical heart* of §2 of A. Schmidt and K. Wingberg,
*Šafarevič's theorem on solvable groups as Galois groups* (arXiv:math/9809211):
the shrinking lemma for Tate cohomology, in the form in which the paper's proof of Theorem 15
uses it.

## The statement

Let `G` be a finite group, `p` a prime, `τ = (i,j)` a pair with `j ≥ 1`, `N` a finitely
generated `𝔽_p[G]`-module, `t, n ∈ ℕ`.  Then there is `r₀` such that for all `r ≥ r₀`: given
`t` elements `x_1, …, x_t` of `Ĥ⁻¹(G, E(r·n,τ) ⊗ N)` there is a *surjective* `G`-equivariant
homomorphism `Φ : F(r·n) → F(n)` of free `G`-operator groups whose induced map on
`Ĥ⁻¹(G, E(-,τ) ⊗ N)` kills all the `x_i`.

This is Proposition 6 for `k = -1`; the paper observes ("since `T` was arbitrary, we may
restrict to the case `k = -1`") that dimension shifting reduces the general degree to this one,
and the cases `k = 2`, `k = -2` actually used in Theorem 15 are obtained from it in
`Work.CohomologicalShrinking.Corollaries`.

## The proof

Following the paper:

* `Ĥ⁻¹(G, A) ↪ A_G = A/I_G A` (`Work.Tate.Hm1ToCoinv`, injective), so it suffices to kill the
  images in the coinvariants `(E(r·n,τ) ⊗ N)_G`;
* by Proposition 5 the coefficient module `E(r·n,τ) ⊗ N` is a quotient of
  `(F(r·n)/F(r·n)^2)^{⊗j} ⊗ N`, so the classes lift to `(F(r·n)/F(r·n)^2)^{⊗j} ⊗ N`;
* identifying `F(r·n)/F(r·n)^2 ≅ (F(n)/F(n)^2)^r` (the coordinate equivalence, which is a
  canonical datum produced by `exists_foldOperator`), the shrinking lemma **Proposition 2**
  (`Work.Shrinking.exists_forall_foldMap_rTensor_tensorPower_eq_zero`) produces
  `a ∈ 𝔽_p^r`, `a ≠ 0`, such that the folding map `φ_a` is surjective and kills the lifted
  elements;
* after rescaling `a` so that one of its coordinates is `1`, the folding map is induced on
  `F(r·n)/F(r·n)^2` by a *surjective* `G`-equivariant homomorphism `Φ : F(r·n) → F(n)`
  (`exists_foldOperator`), and naturality of `θ_τ` (`Prop5Data.θ_natural`) finishes the proof.

## What is assumed

Everything here is proved from the named hypothesis `Prop5Data` (Proposition 5, see
`Work.CohomologicalShrinking.Prop5` and `NOTES.md`) and the results of `Work.Shrinking`,
`Work.Tate` and `Work.GroupCohomology`.  There is no `sorry` in this file.
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.Prop5
import Submission.Work.CohomologicalShrinking.Functorial
import Submission.Work.CohomologicalShrinking.functorial.gradedMapAdd_smul
import Submission.Work.Tate.Coinvariants
import Submission.Work.Tate.Hm1ToCoinv_injective
import Submission.Work.Shrinking.Shrinking
import Submission.Work.CohomologicalShrinking.modsquare.squareQuotientToFun_bijective
import Submission.Work.CohomologicalShrinking.operator.exists_foldOperator
import Submission.Work.CohomologicalShrinking.operator.exists_foldOperator_of_basis
import Submission.Work.CohomologicalShrinking.shrinking.rTensor_map_foldMap_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

attribute [local instance] Classical.decEq

namespace Work.CohomologicalShrinking

set_option maxHeartbeats 800000

open scoped TensorProduct

universe u v w

variable {p : ℕ}

/-! ## Elementary equivariance of `f ⊗ id` -/

/-- If `f` is `G`-equivariant then so is `f ⊗ id`. -/
theorem rTensor_equiv (p : ℕ) {G M M' N : Type*} [Group G]
    [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    [AddCommGroup M'] [Module (ZMod p) M'] [DistribMulAction G M'] [SMulCommClass G (ZMod p) M']
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N] [SMulCommClass G (ZMod p) N]
    (f : M →ₗ[ZMod p] M') (hf : ∀ (g : G) (x : M), f (g • x) = g • f x) (g : G)
    (z : M ⊗[ZMod p] N) : f.rTensor N (g • z) = g • f.rTensor N z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
      rw [Work.Shrinking.diagTensor_smul_tmul, LinearMap.rTensor_tmul, hf,
        LinearMap.rTensor_tmul, Work.Shrinking.diagTensor_smul_tmul]
  | add z w hz hw => rw [smul_add, map_add, hz, hw, map_add, smul_add]

/-- The `𝔽_p`-linear map on graded pieces induced by a surjective `G`-equivariant homomorphism
is `G`-equivariant. -/
theorem gradedMapLin_smul (p : ℕ) {G P Q : Type*} [Group G] [Group P] [Group Q]
    [MulDistribMulAction G P] [MulDistribMulAction G Q]
    (ψ : P →* Q) (hψ : Function.Surjective ψ)
    (hψG : ∀ (g : G) (x : P), ψ (g • x) = g • ψ x) (i j : ℕ) (g : G)
    (z : Additive (refinedQuotient p P i j)) :
    gradedMapLin p ψ hψ i j (g • z) = g • gradedMapLin p ψ hψ i j z :=
  functorial.gradedMapAdd_smul p ψ hψ hψG i j g z

/-! ## Operator maps and their induced maps on `Ĥ⁻¹` -/

/-- A surjective `G`-equivariant homomorphism `F(m) → F(n)` of free `G`-operator groups. -/
structure OperatorMap (G : Type*) [Group G] (m n : ℕ) where
  /-- the underlying homomorphism -/
  toHom : Work.Shrinking.freeOperatorGroup G m →* Work.Shrinking.freeOperatorGroup G n
  /-- it is surjective -/
  surjective : Function.Surjective toHom
  /-- it is `G`-equivariant -/
  equivariant : ∀ (g : G) (y : Work.Shrinking.freeOperatorGroup G m),
    toHom (g • y) = g • toHom y

/-- The `G`-equivariant `𝔽_p`-linear map `E(m,τ) ⊗ N → E(n,τ) ⊗ N` induced by an operator
map. -/
noncomputable abbrev OperatorMap.gradedTensor (p : ℕ) [NeZero p] {G : Type*} [Group G]
    {i j : ℕ} (N : Type*) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] {m n : ℕ} (Φ : OperatorMap G m n) :
    (E p G m i j ⊗[ZMod p] N) →ₗ[ZMod p] (E p G n i j ⊗[ZMod p] N) :=
  (gradedMapLin p Φ.toHom Φ.surjective i j).rTensor N

/-- The induced map on `Ĥ⁻¹(G, E(-,τ) ⊗ N)`. -/
noncomputable def OperatorMap.hm1Map (p : ℕ) [NeZero p] (G : Type*) [Group G] [Fintype G]
    {i j : ℕ} (N : Type*) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] {m n : ℕ} (Φ : OperatorMap G m n) :
    Work.Tate.Hm1 G (E p G m i j ⊗[ZMod p] N) →+
      Work.Tate.Hm1 G (E p G n i j ⊗[ZMod p] N) :=
  Work.Tate.Hm1Map G (E p G m i j ⊗[ZMod p] N) (E p G n i j ⊗[ZMod p] N)
    ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor N)
    (fun g z => rTensor_equiv p (G := G) (f := gradedMapLin p Φ.toHom Φ.surjective i j)
      (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x) g z)

/-! ## Tensor-algebra lemmas used in the proof of the shrinking lemma -/

section TensorLemmas

variable {A B C N : Type*}

/-- `f ⊗ id` is surjective when `f` is. -/
theorem rTensor_surjective [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B] [AddCommGroup N] [Module (ZMod p) N]
    (f : A →ₗ[ZMod p] B) (hf : Function.Surjective f) :
    Function.Surjective (f.rTensor N) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul b n =>
      obtain ⟨a, rfl⟩ := hf b
      exact ⟨a ⊗ₜ n, by rw [LinearMap.rTensor_tmul]⟩
  | add z w hz hw =>
      obtain ⟨z', rfl⟩ := hz
      obtain ⟨w', rfl⟩ := hw
      exact ⟨z' + w', map_add _ _ _⟩

/-- `(g^{⊗j} ⊗ id) ∘ (f^{⊗j} ⊗ id) = (g ∘ f)^{⊗j} ⊗ id`. -/
theorem rTensor_piTensor_map_comp [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B] [AddCommGroup C] [Module (ZMod p) C]
    [AddCommGroup N] [Module (ZMod p) N] (j : ℕ) (f : C →ₗ[ZMod p] B) (g : B →ₗ[ZMod p] A) :
    ((PiTensorProduct.map (fun _ : Fin j => g)).rTensor N) ∘ₗ
        ((PiTensorProduct.map (fun _ : Fin j => f)).rTensor N)
      = (PiTensorProduct.map (fun _ : Fin j => g ∘ₗ f)).rTensor N := by
  rw [← LinearMap.rTensor_comp, ← PiTensorProduct.map_comp]

/-- `(id^{⊗j}) ⊗ id` is the identity. -/
theorem rTensor_piTensor_map_id [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup N] [Module (ZMod p) N] (j : ℕ) :
    (PiTensorProduct.map (fun _ : Fin j => (LinearMap.id : A →ₗ[ZMod p] A))).rTensor N
      = LinearMap.id := by
  rw [PiTensorProduct.map_id, LinearMap.rTensor_id]

/-- `φ_{ca} = c • φ_a` for the folding maps. -/
theorem foldMap_smul_eq [AddCommGroup A] [Module (ZMod p) A] {r : ℕ} (c : ZMod p)
    (a : Fin r → ZMod p) :
    Work.Shrinking.foldMap (M := A) (c • a)
      = c • Work.Shrinking.foldMap (M := A) a := by
  refine LinearMap.ext fun x => ?_
  simp only [Work.Shrinking.foldMap_apply, Pi.smul_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_smul c (a i) (x i)

end TensorLemmas

/-! ## The shrinking lemma -/

theorem exists_shrinking_Hm1_of_mult (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    {i j : ℕ} (hj : 1 ≤ j) (D : Prop5Data p G i j)
    (N : Type*) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] [Module.Finite (ZMod p) N]
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ r₀ : ℕ, ∀ r ≥ r₀, ∀ x : Fin t → Work.Tate.Hm1 G (E p G (r * n) i j ⊗[ZMod p] N),
      ∃ Φ : OperatorMap G (r * n) n, ∀ k : Fin t, Φ.hm1Map p G N (x k) = 0 := by
  classical
  haveI hMnontriv : Nontrivial (squareQuotient p G n) := by
    have hb := modsquare.squareQuotientToFun_bijective p G n
    have hne : (Pi.single (⟨0, hn⟩, (1 : G)) (1 : ZMod p) : Fin n × G → ZMod p) ≠ 0 := by
      intro h
      have h1 := congrFun h (⟨0, hn⟩, (1 : G))
      simpa using h1
    obtain ⟨u, hu⟩ := hb.2 (Pi.single (⟨0, hn⟩, (1 : G)) (1 : ZMod p))
    refine ⟨u, 0, fun h0 => hne ?_⟩
    rw [← hu, h0, map_zero]
  haveI hMfin : Module.Finite (ZMod p) (squareQuotient p G n) :=
    Module.Finite.of_surjective (modsquare.funToSquareQuotient p G n)
      (fun y => ⟨(squareQuotientToFun p G n) y,
        modsquare.funToSquareQuotient_squareQuotientToFun p G n y⟩)
  obtain ⟨r₀, hr₀⟩ := Work.Shrinking.exists_forall_foldMap_rTensor_tensorPower_eq_zero
    (p := p) (M := squareQuotient p G n) (N := N) j t hj hMnontriv
  refine ⟨max r₀ 1, fun r hr x => ?_⟩
  have hr₀' : r₀ ≤ r := le_trans (le_max_left r₀ 1) hr
  have hr1 : 1 ≤ r := le_trans (le_max_right r₀ 1) hr
  -- the canonical coordinate equivalence `e` and a reference operator map
  obtain ⟨e, _ψ₀, _hψ₀, he, _he_smul, _hψ₀G, _hψ₀comp⟩ :=
    operator.exists_foldOperator p G r n (k₀ := ⟨0, hr1⟩) (Pi.single ⟨0, hr1⟩ (1 : ZMod p))
      (by simp)
  -- representatives of the classes `x k`
  have hrep : ∀ k : Fin t, ∃ c : (Work.Tate.norm G (E p G (r * n) i j ⊗[ZMod p] N)).ker,
      Work.Tate.Hm1π G _ c = x k := fun k => QuotientAddGroup.mk'_surjective _ (x k)
  choose c hc using hrep
  -- lift the representatives to the tensor power of `F(r·n)/F(r·n)^2`
  have hlift : ∀ k : Fin t, ∃ w : (⨂[ZMod p]^j (squareQuotient p G (r * n))) ⊗[ZMod p] N,
      ((D.θ (r * n)).rTensor N) w = (c k : E p G (r * n) i j ⊗[ZMod p] N) :=
    fun k => rTensor_surjective (f := D.θ (r * n)) (D.θ_surjective (r * n)) _
  choose w hw using hlift
  -- transport to `(F(n)/F(n)^2)^r`
  let z : Fin t → (⨂[ZMod p]^j (Fin r → squareQuotient p G n)) ⊗[ZMod p] N :=
    fun k => ((PiTensorProduct.map (fun _ : Fin j => e.symm.toLinearMap)).rTensor N) (w k)
  obtain ⟨a, ha0, _ha_surj, hkill⟩ := hr₀ r hr₀' z
  -- normalise `a` so that some coordinate is `1`
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : Fin r, a k₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha0 (funext fun k => by simpa using h k)
  let cc : ZMod p := (a k₀)⁻¹
  let bv : Fin r → ZMod p := cc • a
  have hbv : bv k₀ = 1 := by
    simp only [bv, Pi.smul_apply, cc, smul_eq_mul, inv_mul_cancel₀ hk₀]
  obtain ⟨ψ, hψ, hψG, hψcomp⟩ :=
    operator.exists_foldOperator_of_basis p G r n (k₀ := k₀) bv hbv e he
  -- the induced map on the tensor power kills all the lifts
  have he_id : (PiTensorProduct.map (fun _ : Fin j => e.toLinearMap)).rTensor N ∘ₗ
      (PiTensorProduct.map (fun _ : Fin j => e.symm.toLinearMap)).rTensor N = LinearMap.id := by
    rw [rTensor_piTensor_map_comp]
    have hcomp1 : (fun _ : Fin j => e.toLinearMap ∘ₗ e.symm.toLinearMap)
        = (fun _ : Fin j => (LinearMap.id : squareQuotient p G (r * n) →ₗ[ZMod p]
            squareQuotient p G (r * n))) := by
      funext s
      ext y
      simp
    rw [hcomp1, rTensor_piTensor_map_id]
  have hcomp_map : ((PiTensorProduct.map (fun _ : Fin j => quotMapLin p G ψ hψ)).rTensor N) ∘ₗ
      ((PiTensorProduct.map (fun _ : Fin j => e.toLinearMap)).rTensor N)
      = (PiTensorProduct.map (fun _ : Fin j => Work.Shrinking.foldMap (M := squareQuotient p G n) bv)).rTensor N := by
    rw [rTensor_piTensor_map_comp, hψcomp]
  have hz : ∀ k : Fin t,
      ((PiTensorProduct.map (fun _ : Fin j => quotMapLin p G ψ hψ)).rTensor N) (w k) = 0 := by
    intro k
    have hwk : ((PiTensorProduct.map (fun _ : Fin j => e.toLinearMap)).rTensor N) (z k) = w k := by
      change ((PiTensorProduct.map (fun _ : Fin j => e.toLinearMap)).rTensor N)
        (((PiTensorProduct.map (fun _ : Fin j => e.symm.toLinearMap)).rTensor N) (w k)) = w k
      rw [← LinearMap.comp_apply, he_id]
      rfl
    rw [← hwk]
    have h1 : (((PiTensorProduct.map (fun _ : Fin j => quotMapLin p G ψ hψ)).rTensor N) ∘ₗ
        ((PiTensorProduct.map (fun _ : Fin j => e.toLinearMap)).rTensor N)) (z k) = 0 := by
      rw [hcomp_map]
      have hscale := Work.CohomologicalShrinking.shrinking.rTensor_map_foldMap_smul (p := p) (G := G)
        (M := squareQuotient p G n) (N := N) j r cc a (z k)
      rw [hscale, hkill k, smul_zero]
    simpa using h1
  -- naturality of `θ`
  have hnat : ((D.θ n).rTensor N) ∘ₗ
      ((PiTensorProduct.map (fun _ : Fin j => quotMapLin p G ψ hψ)).rTensor N)
      = ((gradedMapLin p ψ hψ i j).rTensor N) ∘ₗ ((D.θ (r * n)).rTensor N) := by
    rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp, D.θ_natural ψ hψ hψG]
  -- the induced map kills the representatives
  have hfin : ∀ k : Fin t,
      ((gradedMapLin p ψ hψ i j).rTensor N) (c k : E p G (r * n) i j ⊗[ZMod p] N) = 0 := by
    intro k
    rw [← hw k]
    have h1 : (((gradedMapLin p ψ hψ i j).rTensor N) ∘ₗ ((D.θ (r * n)).rTensor N)) (w k) = 0 := by
      rw [← hnat, LinearMap.comp_apply, hz k, map_zero]
    simpa using h1
  refine ⟨⟨ψ, hψ, hψG⟩, fun k => Work.Tate.Hm1ToCoinv_injective (G := G) ?_⟩
  rw [← hc k]
  show Work.Tate.Hm1ToCoinv G (E p G n i j ⊗[ZMod p] N)
      ((OperatorMap.hm1Map p G N ⟨ψ, hψ, hψG⟩) (Work.Tate.Hm1π G _ (c k))) = 0
  rw [show (OperatorMap.hm1Map p G N ⟨ψ, hψ, hψG⟩) (Work.Tate.Hm1π G _ (c k))
      = Work.Tate.Hm1Map G _ _ ((gradedMapLin p ψ hψ i j).rTensor N) _
          (Work.Tate.Hm1π G _ (c k)) from rfl]
  show Work.Tate.coinvMk G (E p G n i j ⊗[ZMod p] N)
      (((gradedMapLin p ψ hψ i j).rTensor N) (c k : E p G (r * n) i j ⊗[ZMod p] N)) = 0
  rw [Work.Tate.coinvMk_eq_zero_iff, hfin k]
  exact Work.Tate.zero_mem_augmentation

end Work.CohomologicalShrinking
