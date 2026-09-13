import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit

namespace Commons.LinearAlgebra.Submodule

open Module

section General

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [Fintype V]

/-- For a basis `b` of a submodule `W ≤ V`, the image of `b` in `V` spans `W`. -/
lemma span_range_basis_coe {ι : Type*} (W : Submodule F V) (b : Basis ι F W) :
    Submodule.span F (Set.range (fun i => (b i : V))) = W := by
  have key : Submodule.map W.subtype (⊤ : Submodule F W) =
      Submodule.span F (Set.range (fun i => (b i : V))) := by
    rw [← b.span_eq, Submodule.map_span]
    congr 1
    rw [← Set.range_comp' (W.subtype) (⇑b)]
    simp only [Submodule.coe_subtype]
  rw [Submodule.map_top, Submodule.range_subtype] at key
  exact key.symm

/-- Framed `m`-dimensional subspaces of `V` (a subspace together with a basis) are in
bijection with linearly independent `m`-tuples of vectors of `V`. -/
noncomputable def frameEquiv (m : ℕ) :
    (Σ W : {W : Submodule F V // Module.finrank F W = m}, Basis (Fin m) F W.1) ≃
      {s : Fin m → V // LinearIndependent F s} :=
  Equiv.ofBijective
    (fun p => ⟨fun i => (p.2 i : V),
      p.2.linearIndependent.map' (Submodule.subtype p.1.1) (Submodule.ker_subtype _)⟩)
    ⟨fun p p' h => by
      obtain ⟨⟨W, hW⟩, b⟩ := p
      obtain ⟨⟨W', hW'⟩, b'⟩ := p'
      have hf : (fun i => (b i : V)) = (fun i => (b' i : V)) := by
        simpa using congrArg Subtype.val h
      have hWW : W = W' := by
        have hsp : Submodule.span F (Set.range (fun i => (b i : V))) =
            Submodule.span F (Set.range (fun i => (b' i : V))) := by rw [hf]
        rwa [span_range_basis_coe W b, span_range_basis_coe W' b'] at hsp
      subst hWW
      refine Sigma.ext (Subtype.ext rfl) ?_
      exact heq_of_eq (DFunLike.coe_injective (funext fun i => Subtype.ext (congr_fun hf i))),
     fun s => ⟨⟨⟨Submodule.span F (Set.range s.1), by
        rw [finrank_span_eq_card s.2, Fintype.card_fin]⟩, Basis.span s.2⟩, by
        apply Subtype.ext
        funext i
        exact Basis.coe_span_apply s.2 i⟩⟩

/-- A basis of `W` is the same thing as a linear equivalence `W ≃ₗ (Fin m → F)`. -/
noncomputable def basisEquivLinearEquiv (m : ℕ) (W : Submodule F V) :
    Basis (Fin m) F W ≃ (W ≃ₗ[F] (Fin m → F)) where
  toFun b := b.equivFun
  invFun e := Basis.ofEquivFun e
  left_inv b := Basis.ofEquivFun_equivFun b
  right_inv e := Basis.equivFun_ofEquivFun e

/-- Left composition with a fixed linear equivalence `φ : (Fin m → F) ≃ₗ W` is a bijection
from `W ≃ₗ (Fin m → F)` to `(Fin m → F) ≃ₗ (Fin m → F)`. -/
noncomputable def composeLinearEquiv {ι : Type*} [Finite ι] {W : Submodule F V}
    (φ : (ι → F) ≃ₗ[F] W) : (W ≃ₗ[F] (ι → F)) ≃ ((ι → F) ≃ₗ[F] (ι → F)) where
  toFun e := φ.trans e
  invFun g := φ.symm.trans g
  left_inv e := by
    dsimp only
    rw [← LinearEquiv.trans_assoc, LinearEquiv.symm_trans_self, LinearEquiv.refl_trans]
  right_inv g := by
    dsimp only
    rw [← LinearEquiv.trans_assoc, LinearEquiv.self_trans_symm, LinearEquiv.refl_trans]

/-- Every `m`-dimensional subspace has the same number of bases, namely the cardinality of
`GL_m(F)`. -/
lemma card_basis_eq_card_linearEquiv (m : ℕ)
    (W : {W : Submodule F V // Module.finrank F W = m}) :
    Nat.card (Basis (Fin m) F W.1) = Nat.card ((Fin m → F) ≃ₗ[F] (Fin m → F)) := by
  rw [Nat.card_congr (basisEquivLinearEquiv m W.1)]
  obtain ⟨φ⟩ : Nonempty ((Fin m → F) ≃ₗ[F] W.1) :=
    ⟨LinearEquiv.ofFinrankEq (Fin m → F) W.1 (by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, W.2])⟩
  exact Nat.card_congr (composeLinearEquiv φ)

/-- Counting framed subspaces: the number of pairs (subspace of dimension `m`, basis of it)
equals the number of `m`-dimensional subspaces times the number of bases of a single one. -/
theorem card_frame_sigma (m : ℕ) :
    Nat.card (Σ W : {W : Submodule F V // Module.finrank F W = m}, Basis (Fin m) F W.1) =
      Nat.card {W : Submodule F V // Module.finrank F W = m} *
        Nat.card ((Fin m → F) ≃ₗ[F] (Fin m → F)) := by
  classical
  haveI : Fintype {W : Submodule F V // Module.finrank F W = m} := inferInstance
  haveI hfin : ∀ W : {W : Submodule F V // Module.finrank F W = m},
      Finite (Basis (Fin m) F W.1) :=
    fun W => Finite.of_injective (fun b : Basis (Fin m) F W.1 => (b : Fin m → W.1))
      DFunLike.coe_injective
  rw [Nat.card_sigma]
  rw [Finset.sum_congr rfl (fun W _ => card_basis_eq_card_linearEquiv m W)]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card (α := {W : Submodule F V // Module.finrank F W = m})]

/-- The Gaussian-binomial counting identity for the number of `m`-dimensional subspaces of a
finite vector space `V` over a finite field `F`. -/
theorem card_submodule_mul_card_linearEquiv (m : ℕ) :
    Nat.card {W : Submodule F V // Module.finrank F W = m} *
        Nat.card ((Fin m → F) ≃ₗ[F] (Fin m → F)) =
      Nat.card {s : Fin m → V // LinearIndependent F s} := by
  rw [← card_frame_sigma m]
  exact Nat.card_congr (frameEquiv m)

end General

theorem card_submodule_finrank_mul_prod (n m : ℕ) :
    Nat.card {W : Submodule (ZMod 2) (Fin n → ZMod 2) // Module.finrank (ZMod 2) W = m} *
        (∏ i ∈ Finset.range m, (2 ^ m - 2 ^ i))
      = ∏ i ∈ Finset.range m, (2 ^ n - 2 ^ i) := by
  have hcount := card_submodule_mul_card_linearEquiv (F := ZMod 2) (V := Fin n → ZMod 2) m
  have hL1 : Nat.card (Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) =
      Nat.card ((Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2)) :=
    (Nat.card_congr (Matrix.GeneralLinearGroup.toLin (n := Fin m) (R := ZMod 2)).toEquiv).trans
      (Nat.card_congr
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin m → ZMod 2)).toEquiv)
  have hL : Nat.card ((Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2)) =
      ∏ i ∈ Finset.range m, (2 ^ m - 2 ^ i) := by
    rw [← hL1, Matrix.card_GL_field m, ZMod.card 2]
    exact Fin.prod_univ_eq_prod_range (fun j => 2 ^ m - 2 ^ j) m
  have hB : Nat.card {s : Fin m → (Fin n → ZMod 2) // LinearIndependent (ZMod 2) s} =
      ∏ i ∈ Finset.range m, (2 ^ n - 2 ^ i) := by
    by_cases hmn : m ≤ n
    · have hk : m ≤ Module.finrank (ZMod 2) (Fin n → ZMod 2) := by
        rw [Module.finrank_fintype_fun_eq_card (ZMod 2) (η := Fin n), Fintype.card_fin]
        exact hmn
      rw [card_linearIndependent (K := ZMod 2) (V := Fin n → ZMod 2) (k := m) hk,
        ZMod.card 2, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
      exact Fin.prod_univ_eq_prod_range (fun j => 2 ^ n - 2 ^ j) m
    · have hnm : n < m := by omega
      haveI : IsEmpty {s : Fin m → (Fin n → ZMod 2) // LinearIndependent (ZMod 2) s} :=
        ⟨fun s => by
          have h := s.2.fintype_card_le_finrank
          rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
          omega⟩
      rw [Nat.card_eq_zero.mpr (Or.inl ‹IsEmpty _›),
        Finset.prod_eq_zero (Finset.mem_range.mpr hnm) (by simp)]
  rw [← hL, hcount, hB]

end Commons.LinearAlgebra.Submodule