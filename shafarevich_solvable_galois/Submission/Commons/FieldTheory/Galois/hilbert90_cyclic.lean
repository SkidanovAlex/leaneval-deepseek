import Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped BigOperators
open Finset

namespace Commons.FieldTheory.Galois

open Module

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- y • σ as an additive endomorphism of L -/
def Fadd (σ : L ≃ₐ[K] L) (y : L) : L →+ L where
  toFun x := y * σ x
  map_zero' := by simp
  map_add' := by intro x z; simp [mul_add]

/-- partial product coefficient c_i = ∏_{j < i} σ^j y -/
def cycCoeff (σ : L ≃ₐ[K] L) (y : L) (i : ℕ) : L :=
  ∏ j ∈ Finset.range i, (σ ^ j) y

-- y * ∏_{j∈range i} σ^{j+1} y = ∏_{j∈range(i+1)} σ^j y
lemma y_mul_shift (σ : L ≃ₐ[K] L) (y : L) :
    ∀ i : ℕ, y * (∏ j ∈ Finset.range i, (σ ^ (j + 1)) y) = ∏ j ∈ Finset.range (i+1), (σ ^ j) y := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Finset.prod_range_succ]
      rw [Finset.prod_range_succ]
      rw [← ih]
      ring

-- σ (∏_{j∈range i} σ^j y) = ∏_{j∈range i} σ^{j+1} y
lemma shift_prod (σ : L ≃ₐ[K] L) (y : L) (i : ℕ) :
    σ (cycCoeff σ y i) = ∏ j ∈ Finset.range i, (σ ^ (j + 1)) y := by
  induction i with
  | zero => simp [cycCoeff]
  | succ i ih =>
      conv_lhs => rw [cycCoeff, Finset.prod_range_succ]
      rw [map_mul]
      change σ (cycCoeff σ y i) * σ ((σ ^ i) y) = ∏ j ∈ Finset.range (i + 1), (σ ^ (j + 1)) y
      rw [ih]
      rw [Finset.prod_range_succ]
      congr 1
      · rw [show (σ ^ (i + 1)) = σ * (σ ^ i) by rw [pow_succ']]
        rfl

-- expansion: iterate (y • σ) i x = c_i * σ^i x
lemma iterate_expand (σ : L ≃ₐ[K] L) (y : L) (x : L) :
    ∀ i : ℕ, (((Fadd σ y : L → L)^[i]) x) = cycCoeff σ y i * (σ ^ i) x := by
  intro i
  induction i with
  | zero =>
      simp [cycCoeff]
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih]
      change y * σ (cycCoeff σ y i * (σ ^ i) x) = cycCoeff σ y (i + 1) * (σ ^ (i + 1)) x
      rw [map_mul]
      rw [shift_prod]
      rw [← mul_assoc]
      rw [y_mul_shift]
      rw [cycCoeff]
      congr 1
      · rw [show (σ ^ (i + 1)) = σ * (σ ^ i) by rw [pow_succ']]
        rfl

lemma sum_range_iterate_eq (F : L → L) (n : ℕ) (x : L) :
    (∑ i ∈ Finset.range n, F^[i+1] x) = (∑ i ∈ Finset.range n, F^[i] x) + F^[n] x - F^[0] x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [ih]
      abel

/-- A bijection between `Fin (orderOf σ)` and the subgroup generated, given it is everything -/
noncomputable def powEquiv (σ : L ≃ₐ[K] L) (hfin : IsOfFinOrder σ)
    (hgen : Subgroup.zpowers σ = ⊤) : Fin (orderOf σ) ≃ (L ≃ₐ[K] L) := by
  have hset : ((Subgroup.zpowers σ : Set (L ≃ₐ[K] L)) =
      ((⊤ : Subgroup (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L))) := by
    exact congrArg (fun S : Subgroup (L ≃ₐ[K] L) => (S : Set (L ≃ₐ[K] L))) hgen
  refine (finEquivZPowers hfin).trans ?_
  refine (Equiv.subtypeEquiv (Equiv.refl (L ≃ₐ[K] L)) (fun a => ?_)).trans
    (Subgroup.topEquiv.toEquiv)
  change a ∈ (Subgroup.zpowers σ : Set (L ≃ₐ[K] L)) ↔
    a ∈ ((⊤ : Subgroup (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L))
  rw [hset]

@[simp] lemma powEquiv_apply (σ : L ≃ₐ[K] L) (hfin : IsOfFinOrder σ)
    (hgen : Subgroup.zpowers σ = ⊤) (i : Fin (orderOf σ)) :
    (powEquiv σ hfin hgen i : L ≃ₐ[K] L) = σ ^ (i : ℕ) := by
  simp [powEquiv, finEquivZPowers_apply]

/-- the product over the σ-powers equals the field norm -/
lemma prod_powers_eq_norm [FiniteDimensional K L] [IsGalois K L] (σ : L ≃ₐ[K] L)
    (hfin : IsOfFinOrder σ) (hgen : Subgroup.zpowers σ = ⊤) (y : L) :
    (∏ j ∈ Finset.range (orderOf σ), (σ ^ j) y) = algebraMap K L (Algebra.norm K y) := by
  rw [← Fin.prod_univ_eq_prod_range (fun j => (σ ^ j) y) (orderOf σ)]
  rw [Algebra.norm_eq_prod_automorphisms K y]
  exact Fintype.prod_equiv (powEquiv σ hfin hgen) (fun i => (σ ^ (i : ℕ)) y) (fun g => g y)
    (by intro i; simp)



-- Linear independence of the cyclic family of automorphisms
lemma cyclic_linIndep (σ : L ≃ₐ[K] L) :
    LinearIndependent L (fun i : Fin (orderOf σ) => AlgHom.toLinearMap ((σ ^ (i : ℕ)).toAlgHom)) := by
  -- family over algHoms is independent; compose with injective map from Fin
  refine (linearIndependent_algHom_toLinearMap K L L).comp
    (fun i : Fin (orderOf σ) => (σ ^ (i : ℕ)).toAlgHom) ?_
  -- injective
  intro i j hij
  -- toAlgHom injective ⟹ σ^i = σ^j as AlgEquiv
  have hσ : σ ^ (i : ℕ) = σ ^ (j : ℕ) := AlgEquiv.coe_toAlgHom_injective hij
  -- σ^i = σ^j, i,j < orderOf: i = j
  apply Fin.ext
  exact Nat.ModEq.eq_of_lt_of_lt ((pow_eq_pow_iff_modEq).mp hσ) i.isLt j.isLt



variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

theorem hilbert90_cyclic {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (σ : L ≃ₐ[K] L)
    (hgen : Subgroup.zpowers σ = ⊤) (y : L) :
    Algebra.norm K y = 1 ↔ ∃ z : Lˣ, y = σ (z : L) / (z : L) := by
  constructor
  · intro hN
    have hfin : IsOfFinOrder σ := isOfFinOrder_of_finite σ
    have hord : orderOf σ = Module.finrank K L := by
      rw [orderOf_eq_card_of_zpowers_eq_top hgen, IsGalois.card_aut_eq_finrank K L]
    have hpos : 0 < orderOf σ := by
      rw [hord]
      exact Module.finrank_pos
    have hσn : (σ ^ (orderOf σ)) = 1 := pow_orderOf_eq_one σ
    have hσn_apply : ∀ x : L, (σ ^ (orderOf σ)) x = x := by
      intro x
      rw [hσn]
      rfl
    have hprod : (∏ j ∈ Finset.range (orderOf σ), (σ ^ j) y) = 1 := by
      rw [prod_powers_eq_norm σ hfin hgen y, hN]
      simp
    have hF : ∀ x : L, (((Fadd σ y : L → L)^[orderOf σ]) x) = x := by
      intro x
      rw [iterate_expand]
      rw [cycCoeff, hprod, hσn_apply]
      simp
    let S : L → L := fun x => ∑ i ∈ Finset.range (orderOf σ), (((Fadd σ y : L → L)^[i]) x)
    have hfix : ∀ x : L, (Fadd σ y) (S x) = S x := by
      intro x
      dsimp [S]
      rw [map_sum]
      have hrewr : (∑ i ∈ Finset.range (orderOf σ),
          (Fadd σ y) (((Fadd σ y : L → L)^[i]) x)) =
          (∑ i ∈ Finset.range (orderOf σ), (((Fadd σ y : L → L)^[i + 1]) x)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Function.iterate_succ_apply']
      rw [hrewr]
      rw [sum_range_iterate_eq]
      rw [hF]
      simp
    have hSne : ∃ x, S x ≠ 0 := by
      by_contra hno
      have hS0 : ∀ x, S x = 0 := by
        intro x
        by_contra hx
        exact hno ⟨x, hx⟩
      let n : ℕ := orderOf σ
      let c : Fin n → L := fun i => cycCoeff σ y (i : ℕ)
      let φ : Fin n → L →ₗ[K] L := fun i => AlgHom.toLinearMap ((σ ^ (i : ℕ)).toAlgHom)
      have hφ : LinearIndependent L φ := by
        simpa [φ] using cyclic_linIndep σ
      have hcombo0 : (∑ i : Fin n, c i • φ i) = 0 := by
        apply LinearMap.ext
        intro x
        calc
          (∑ i : Fin n, c i • φ i) x = ∑ i : Fin n, c i • (φ i x) := by
            simp [Finset.sum_apply]
          _ = ∑ i : Fin n, cycCoeff σ y (i : ℕ) * (σ ^ (i : ℕ)) x := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [c, φ]
          _ = ∑ i ∈ Finset.range n, cycCoeff σ y i * (σ ^ i) x := by
            rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => cycCoeff σ y j * (σ ^ j) x) n]
          _ = S x := by
            dsimp [S, n]
            apply Finset.sum_congr rfl
            intro i hi
            rw [← iterate_expand σ y x i]
          _ = 0 := hS0 x
      have hzero : ∀ i : Fin n, c i = 0 := by
        exact (Fintype.linearIndependent_iff.mp hφ) c hcombo0
      have hc0zero : (1 : L) = 0 := by
        have h := hzero ⟨0, hpos⟩
        simpa [c, cycCoeff] using h
      exact one_ne_zero hc0zero
    rcases hSne with ⟨b0, hb0⟩
    let b : L := S b0
    have hb_ne0 : b ≠ 0 := hb0
    have hfixb : (Fadd σ y) b = b := hfix b0
    have hfixb' : y * σ b = b := by
      dsimp [b, Fadd] at hfixb ⊢
      exact hfixb
    have hσb_ne0 : σ b ≠ 0 := by
      intro hσb
      apply hb_ne0
      have hσb' : σ b = σ 0 := by rw [hσb]; simp
      exact σ.injective hσb'
    let z : Lˣ := Units.mk b⁻¹ b (by rw [inv_mul_cancel₀ hb_ne0]) (by rw [mul_inv_cancel₀ hb_ne0])
    refine ⟨z, ?_⟩
    have hy_eq : y = (σ b)⁻¹ * b := by
      calc
        y = (y * σ b) * (σ b)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hσb_ne0, mul_one]
        _ = b * (σ b)⁻¹ := by rw [hfixb']
        _ = (σ b)⁻¹ * b := by rw [mul_comm]
    have hzRHS : σ (z : L) / (z : L) = (σ b)⁻¹ * b := by
      dsimp [z]
      rw [div_eq_mul_inv]
      rw [map_inv₀]
      rw [inv_inv]
    calc
      y = (σ b)⁻¹ * b := hy_eq
      _ = σ (z : L) / (z : L) := hzRHS.symm
  · rintro ⟨z, hz⟩
    have hnz : Algebra.norm K (z : L) ≠ 0 := by
      intro h
      have hz0 : (z : L) = 0 := (Algebra.norm_eq_zero_iff.mp h)
      have hone : (1 : L) = 0 := by
        calc
          (1 : L) = (z : L) * (↑z⁻¹ : L) := by simp
          _ = 0 := by rw [hz0]; simp
      exact one_ne_zero hone
    calc
      Algebra.norm K y = Algebra.norm K (σ (z : L) / (z : L)) := by rw [hz]
      _ = Algebra.norm K (σ (z : L)) / Algebra.norm K (z : L) := by
        rw [div_eq_mul_inv, map_mul, Algebra.norm_inv]
        rw [div_eq_mul_inv]
      _ = 1 := by
        rw [Algebra.norm_eq_of_algEquiv σ (z : L)]
        rw [div_self hnz]

end Commons.FieldTheory.Galois