/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Proposition 7 of Schmidt–Wingberg: the `H₁`-variant of the shrinking lemma

Schmidt–Wingberg's **Proposition 7** is the variant of Proposition 6 in degree `H^{-2} = H₁`
("which goes back to an idea of V. V. Išhanov"), needed in step 4 of the proof of Theorem 15:

> for given elements `x₁, …, x_t ∈ H^{-2}(F(m)/F(m)^(ν), E(m,τ) ⊗ T)` there exists a surjective
> pro-`p` `G`-operator homomorphism `F(m) → F(n)` killing all the `x_i`.

Its proof in the paper is:

* the universal coefficient formula gives `H₁(F(n)/ν, E(n,τ) ⊗ T) ≅ F(n)/F(n)^2 ⊗ E(n,τ) ⊗ T`
  (`F(n)/ν` acts trivially on `E(n,τ) ⊗ T`);
* Proposition 5 implies a `G`-invariant surjection
  `(F(n)/F(n)^2)^{⊗(j+1)} ⊗ T ↠ H₁(F(n)/ν, E(n,τ) ⊗ T)` (the extra tensor factor is
  `F(n)/F(n)^2` itself);
* Proposition 2 applied with `s = j + 1` then produces the folding map, which is lifted to a
  surjective `G`-operator homomorphism exactly as in Proposition 6.

We state and prove this in the model

`Ĥ^{-2}(F(m)/ν, E(m,τ) ⊗ T) := squareQuotient p G m ⊗ (E p G m i j ⊗ T)`

(that is `F(m)/F(m)^2 ⊗ E(m,τ) ⊗ T`, the paper's model), with the map induced by an operator
map `Φ` being `Φ.h1Map = quotMap Φ ⊗ (gradedMap Φ ⊗ id)`.

The only unproved input is the surjection `σ` together with its naturality `hσnat`, which
encodes (i) the universal coefficient formula and Proposition 5 and (ii) the identification
`Q ⊗ ((⨂^j Q) ⊗ T) ≅ (⨂^{j+1} Q) ⊗ T` (associativity of the tensor power, `TensorPower.mulEquiv`)
together with the naturality of that identification; see `NOTES.md` §6.

Everything else in the derivation is proved here from the `k = -1` shrinking lemma of
`Shrinking.lean` / `Corollaries.lean` and Proposition 2 of `Work.Shrinking`.

## Main results

* `Work.CohomologicalShrinking.OperatorMap.h1Map` : the induced map on
  `F/F^2 ⊗ E ⊗ T`.
* `Work.CohomologicalShrinking.exists_shrinking_H1_of_sigma` : Proposition 7 (ii).
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.Shrinking
import Submission.Work.CohomologicalShrinking.Corollaries
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

attribute [local instance] Classical.decEq

namespace Work.CohomologicalShrinking

set_option maxHeartbeats 1600000

open scoped TensorProduct

universe u v w

variable {p : ℕ}

/-- The map induced by an operator map on `F(m)/F(m)^2 ⊗ E(m,τ) ⊗ T`, the model of
`H₁(F(m)/ν, E(m,τ) ⊗ T) = Ĥ^{-2}(F(m)/ν, E(m,τ) ⊗ T)`. -/
noncomputable def OperatorMap.h1Map (p : ℕ) [NeZero p] (G : Type*) [Group G]
    {i j : ℕ} (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] {m n : ℕ} (Φ : OperatorMap G m n) :
    squareQuotient p G m ⊗[ZMod p] (E p G m i j ⊗[ZMod p] T) →ₗ[ZMod p]
      squareQuotient p G n ⊗[ZMod p] (E p G n i j ⊗[ZMod p] T) :=
  TensorProduct.map (quotMapLin p G Φ.toHom Φ.surjective)
    ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T)

/-- **Proposition 7 (ii) of Schmidt–Wingberg**, in the model
`Ĥ^{-2}(F(m)/ν, E(m,τ) ⊗ T) = F(m)/F(m)^2 ⊗ E(m,τ) ⊗ T`.

Let `G` be a finite group, `p` a prime, `τ = (i,j)` with `j ≥ 1`, `T` a finitely generated
`𝔽_p[G]`-module, `t ∈ ℕ` and `n ≥ 1`.  Assume given, for every rank `m`, a surjective
`𝔽_p`-linear map `σ m : (F(m)/F(m)^2)^{⊗(j+1)} ⊗ T ↠ F(m)/F(m)^2 ⊗ E(m,τ) ⊗ T` (the
combination of the universal coefficient formula, Proposition 5 and the tensor-power
associativity) which is compatible with the maps induced by operator maps (`hσnat`).

Then there is `r₀` such that for all `r ≥ r₀` and all `x₁, …, x_t` in
`Ĥ^{-2}(F(r·n)/ν, E(r·n,τ) ⊗ T)` there is a surjective `G`-equivariant `Φ : F(r·n) → F(n)`
whose induced map `Φ.h1Map` kills all the `x_i`. -/
theorem exists_shrinking_H1_of_sigma (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    {i j : ℕ} (hj : 1 ≤ j) (D : Prop5Data p G i j)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] [Module.Finite (ZMod p) T]
    (σ : ∀ m : ℕ, (⨂[ZMod p]^(j + 1) (squareQuotient p G m)) ⊗[ZMod p] T →ₗ[ZMod p]
        (squareQuotient p G m ⊗[ZMod p] (E p G m i j ⊗[ZMod p] T)))
    (hσ : ∀ m : ℕ, Function.Surjective (σ m))
    (hσnat : ∀ ⦃m n : ℕ⦄ (Φ : OperatorMap G m n),
      (Φ.h1Map p G T).comp (σ m)
        = (σ n).comp
            ((PiTensorProduct.map (fun _ : Fin (j + 1) => quotMapLin p G Φ.toHom Φ.surjective)
              ).rTensor T))
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ r₀ : ℕ, ∀ r ≥ r₀,
      ∀ x : Fin t → squareQuotient p G (r * n) ⊗[ZMod p] (E p G (r * n) i j ⊗[ZMod p] T),
      ∃ Φ : OperatorMap G (r * n) n, ∀ k : Fin t, Φ.h1Map p G T (x k) = 0 := by
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
    (p := p) (M := squareQuotient p G n) (N := T) (j + 1) t (Nat.succ_le_succ (Nat.zero_le j))
      hMnontriv
  refine ⟨max r₀ 1, fun r hr x => ?_⟩
  have hr₀' : r₀ ≤ r := le_trans (le_max_left r₀ 1) hr
  have hr1 : 1 ≤ r := le_trans (le_max_right r₀ 1) hr
  obtain ⟨e, _ψ₀, _hψ₀, he, _he_smul, _hψ₀G, _hψ₀comp⟩ :=
    operator.exists_foldOperator p G r n (k₀ := ⟨0, hr1⟩) (Pi.single ⟨0, hr1⟩ (1 : ZMod p))
      (by simp)
  -- lift the classes to the `(j+1)`-fold tensor power
  have hlift : ∀ k : Fin t, ∃ w : (⨂[ZMod p]^(j + 1) (squareQuotient p G (r * n))) ⊗[ZMod p] T,
      σ (r * n) w = x k := fun k => hσ (r * n) (x k)
  choose w hw using hlift
  let z : Fin t → (⨂[ZMod p]^(j + 1) (Fin r → squareQuotient p G n)) ⊗[ZMod p] T :=
    fun k => ((PiTensorProduct.map (fun _ : Fin (j + 1) => e.symm.toLinearMap)).rTensor T) (w k)
  obtain ⟨a, ha0, _ha_surj, hkill⟩ := hr₀ r hr₀' z
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
  have he_id : (PiTensorProduct.map (fun _ : Fin (j + 1) => e.toLinearMap)).rTensor T ∘ₗ
      (PiTensorProduct.map (fun _ : Fin (j + 1) => e.symm.toLinearMap)).rTensor T
      = LinearMap.id := by
    rw [rTensor_piTensor_map_comp]
    have hcomp1 : (fun _ : Fin (j + 1) => e.toLinearMap ∘ₗ e.symm.toLinearMap)
        = (fun _ : Fin (j + 1) => (LinearMap.id : squareQuotient p G (r * n) →ₗ[ZMod p]
            squareQuotient p G (r * n))) := by
      funext s
      ext y
      simp
    rw [hcomp1, rTensor_piTensor_map_id]
  have hcomp_map : ((PiTensorProduct.map
        (fun _ : Fin (j + 1) => quotMapLin p G ψ hψ)).rTensor T) ∘ₗ
      ((PiTensorProduct.map (fun _ : Fin (j + 1) => e.toLinearMap)).rTensor T)
      = (PiTensorProduct.map (fun _ : Fin (j + 1) =>
          Work.Shrinking.foldMap (M := squareQuotient p G n) bv)).rTensor T := by
    rw [rTensor_piTensor_map_comp, hψcomp]
  have hz : ∀ k : Fin t,
      ((PiTensorProduct.map (fun _ : Fin (j + 1) => quotMapLin p G ψ hψ)).rTensor T) (w k) = 0 := by
    intro k
    have hwk : ((PiTensorProduct.map (fun _ : Fin (j + 1) => e.toLinearMap)).rTensor T) (z k)
        = w k := by
      change ((PiTensorProduct.map (fun _ : Fin (j + 1) => e.toLinearMap)).rTensor T)
        (((PiTensorProduct.map (fun _ : Fin (j + 1) => e.symm.toLinearMap)).rTensor T) (w k))
        = w k
      rw [← LinearMap.comp_apply, he_id]
      rfl
    rw [← hwk]
    have h1 : (((PiTensorProduct.map
          (fun _ : Fin (j + 1) => quotMapLin p G ψ hψ)).rTensor T) ∘ₗ
        ((PiTensorProduct.map (fun _ : Fin (j + 1) => e.toLinearMap)).rTensor T)) (z k) = 0 := by
      rw [hcomp_map]
      have hscale := Work.CohomologicalShrinking.shrinking.rTensor_map_foldMap_smul
        (p := p) (G := G) (M := squareQuotient p G n) (N := T) (j + 1) r cc a (z k)
      rw [hscale, hkill k, smul_zero]
    simpa using h1
  refine ⟨⟨ψ, hψ, hψG⟩, fun k => ?_⟩
  have hkey := congrFun (congrArg DFunLike.coe (hσnat (m := r * n) (n := n) ⟨ψ, hψ, hψG⟩)) (w k)
  rw [LinearMap.comp_apply, hw k, LinearMap.comp_apply, hz k, map_zero] at hkey
  exact hkey

end Work.CohomologicalShrinking
