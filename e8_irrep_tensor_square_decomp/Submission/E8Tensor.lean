import Submission.E8Finrank
import Submission.Enveloping
import Submission.EnvelopingModule
import Submission.E8Enum

/-!
# The tensor square of the irreducible `e₈`-module `L(ω₁+ω₈) = V ⧸ N`

`V` is the Verma module `M(ω₁+ω₈)` (`Submission.VermaWeight.V`) and `N` its unique maximal
submodule, so that `L = V ⧸ N` is the irreducible `e₈`-module of highest weight `λ = ω₁+ω₈`
(dimension `779247`, `Submission.E8Finrank.finrank_eq`).  This file builds the **tensor square**
`T N = (V ⧸ N) ⊗[ℂ] (V ⧸ N)` with

* its `U(e₈)`-module structure (through the Lie-module dictionary `EnvelopingModule`);
* the **weight-space decomposition** `T = ⨆_ν TLwt N ν`, where `TLwt N ν` is the span of the pure
  tensors `a ⊗ b` with `a` of weight `ν₁`, `b` of weight `ν₂` and `ν₁ + ν₂ = ν`
  (`iSup_TLwt_eq_top`), together with the scalar action of the Cartan (`smul_h_eq_of_mem_TLwt`);
* the **support bound**: every weight of `T` is of the form `wtZ m₁ + wtZ m₂`, hence lies in
  `2λ - ℕΦ⁺` (`exists_wtZ_of_mem_TLwt`).

The last item is the input of the *upper bound* `ncard (isotypicComponents U T) ≤ 40`: every
simple submodule of `T` has a highest weight vector whose weight is a weight of `T`, hence a
dominant weight `ν` with `2λ - ν ∈ ℕΦ⁺`, i.e. one of the forty elements of `Submission.E8Enum.the40`.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

noncomputable section
open scoped TensorProduct BigOperators

namespace Submission.E8Tensor

open Submission.VermaWeight
open Submission.E8WeightSpaces
open UniversalEnvelopingAlgebra
open Submission.E8Character (posCon posCon_add posCon_iff_exists)

/-- The `E₈` Cartan matrix. -/
abbrev E8 : Matrix (Fin 8) (Fin 8) ℤ := CartanMatrix.E₈

/-- The tensor square of the irreducible quotient `L(ω₁+ω₈) = V ⧸ N`. -/
abbrev T (N : Submodule U V) : Type := (V ⧸ N) ⊗[ℂ] (V ⧸ N)

variable {N : Submodule U V}

/-! ## The action of `e₈` on the tensor square -/

/-- The action of `x : e₈` on the tensor square, as a linear endomorphism: this is the
tensor-product (derivation) action `x·(a⊗b) = x·a ⊗ b + a ⊗ x·b`. -/
noncomputable def deriv (x : LieAlgebra.e₈ ℂ) : Module.End ℂ (T N) :=
  TensorProduct.LieModule.hasBracketAux x

lemma deriv_tmul (x : LieAlgebra.e₈ ℂ) (a b : V ⧸ N) :
    deriv (N := N) x (a ⊗ₜ[ℂ] b) = ((ι ℂ x) • a) ⊗ₜ[ℂ] b + a ⊗ₜ[ℂ] ((ι ℂ x) • b) := by
  simp only [deriv, TensorProduct.LieModule.hasBracketAux, LinearMap.add_apply,
    LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LieModule.toEnd_apply_apply]
  rw [show ⁅x, a⁆ = (ι ℂ x) • a from rfl, show ⁅x, b⁆ = (ι ℂ x) • b from rfl]

/-- The action of `H_j` on a pure tensor whose factors have weights `ν₁`, `ν₂`. -/
lemma deriv_h_tmul (j : Fin 8) {ν₁ ν₂ : Fin 8 → ℤ} {a b : V ⧸ N}
    (ha : a ∈ Lwt N ν₁) (hb : b ∈ Lwt N ν₂) :
    deriv (N := N) (Submission.E8Weights.SerreH j) (a ⊗ₜ[ℂ] b)
      = ((((ν₁ j + ν₂ j : ℤ)) : ℂ)) • (a ⊗ₜ[ℂ] b) := by
  have hh : Submission.E8Weights.h j = (ι ℂ (Submission.E8Weights.SerreH j)) := rfl
  rw [deriv_tmul, ← hh]
  rw [← endU_apply N (Submission.E8Weights.h j) a,
    ← endU_apply N (Submission.E8Weights.h j) b,
    mem_Lwt_iff.mp ha j, mem_Lwt_iff.mp hb j]
  rw [show (((ν₁ j : ℤ) : ℂ) • a) ⊗ₜ[ℂ] b + a ⊗ₜ[ℂ] (((ν₂ j : ℤ) : ℂ) • b)
      = (((ν₁ j : ℤ) : ℂ)) • (a ⊗ₜ[ℂ] b) + (((ν₂ j : ℤ) : ℂ)) • (a ⊗ₜ[ℂ] b) from by
    rw [TensorProduct.smul_tmul', TensorProduct.tmul_smul]]
  rw [← add_smul]
  push_cast
  ring_nf

/-! ## The weight spaces of the tensor square -/

/-- The `ν`-weight space of the tensor square: the span of the pure tensors `a ⊗ b` with
`a ∈ Lwt N ν₁`, `b ∈ Lwt N ν₂` and `ν₁ + ν₂ = ν`. -/
def TLwt (N : Submodule U V) (ν : Fin 8 → ℤ) : Submodule ℂ (T N) :=
  Submodule.span ℂ {x : T N | ∃ (ν₁ ν₂ : Fin 8 → ℤ), ν₁ + ν₂ = ν ∧
    ∃ a ∈ Lwt N ν₁, ∃ b ∈ Lwt N ν₂, x = a ⊗ₜ[ℂ] b}

lemma tmul_mem_TLwt {ν₁ ν₂ : Fin 8 → ℤ} {a b : V ⧸ N}
    (ha : a ∈ Lwt N ν₁) (hb : b ∈ Lwt N ν₂) :
    a ⊗ₜ[ℂ] b ∈ TLwt N (ν₁ + ν₂) :=
  Submodule.subset_span ⟨ν₁, ν₂, rfl, a, ha, b, hb, rfl⟩

/-- `H_j` acts on the `ν`-weight space of the tensor square by the scalar `ν_j`. -/
lemma deriv_h_eq_of_mem_TLwt (j : Fin 8) {ν : Fin 8 → ℤ} {x : T N}
    (hx : x ∈ TLwt N ν) :
    deriv (N := N) (Submission.E8Weights.SerreH j) x = (((ν j : ℤ)) : ℂ) • x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨ν₁, ν₂, hsum, a, ha, b, hb, rfl⟩ := hy
      subst hsum
      exact deriv_h_tmul j ha hb
  | zero => rw [map_zero, smul_zero]
  | add p q _ _ ihp ihq => rw [map_add, ihp, ihq, smul_add]
  | smul c p _ ih => rw [map_smul, ih, smul_comm]

/-! ## Spanning and the support bound -/

/-- The weight `λ - wtZ m` lies in the positive cone `ℕΦ⁺`. -/
lemma posCon_lam_sub_wtZ (m : Fin 8 → ℕ) :
    posCon (Submission.E8Enum.lam - wtZ m) := by
  rw [posCon_iff_exists]
  refine ⟨m, ?_⟩
  funext i
  simp only [Pi.sub_apply, wtZ, Submission.E8Enum.lam, Matrix.mulVec, dotProduct,
    E8WeightSpaces.E8, E8Character.E8]
  rw [show (∑ a : Fin 8, ((m a : ℕ) : ℤ) * CartanMatrix.E₈ i a)
      = ∑ a : Fin 8, CartanMatrix.E₈ i a * ((m a : ℕ) : ℤ) from
    Finset.sum_congr rfl fun a _ => mul_comm _ _]
  by_cases h0 : i = 0 <;> by_cases h7 : i = 7 <;>
    simp [h0, h7]

/-- The tensor square is spanned by its weight spaces. -/
lemma iSup_TLwt_eq_top (N : Submodule U V) : (⨆ ν : Fin 8 → ℤ, TLwt N ν) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← TensorProduct.span_tmul_eq_top (R := ℂ)]
  refine Submodule.span_le.mpr ?_
  rintro y ⟨a, b, rfl⟩
  obtain ⟨s, y, hy, hsum₁⟩ := exists_decomp_Lw N a
  obtain ⟨t, z, hz, hsum₂⟩ := exists_decomp_Lw N b
  rw [hsum₁, hsum₂]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum]
  refine Submodule.sum_mem _ fun p hp => Submodule.sum_mem _ fun q hq => ?_
  exact le_iSup (fun ν : Fin 8 → ℤ => TLwt N ν) (wtZ q + wtZ p)
    (tmul_mem_TLwt (Lw_le_Lwt N q (hy q hq)) (Lw_le_Lwt N p (hz p hp)))

/-- A pure tensor of non-zero weight vectors has a weight which is the sum of two weights of
`L = V ⧸ N`; in particular, it lies in `2λ - ℕΦ⁺`. -/
lemma posCon_two_lam_of_tmul {ν₁ ν₂ : Fin 8 → ℤ} {a b : V ⧸ N}
    (ha : a ∈ Lwt N ν₁) (ha0 : a ≠ 0) (hb : b ∈ Lwt N ν₂) (hb0 : b ≠ 0) :
    posCon (2 • Submission.E8Enum.lam - (ν₁ + ν₂)) := by
  obtain ⟨m₁, hm₁⟩ := exists_wtZ_of_mem_Lwt N ha ha0
  obtain ⟨m₂, hm₂⟩ := exists_wtZ_of_mem_Lwt N hb hb0
  rw [hm₁, hm₂]
  have h : 2 • Submission.E8Enum.lam - (wtZ m₁ + wtZ m₂)
      = (Submission.E8Enum.lam - wtZ m₁) + (Submission.E8Enum.lam - wtZ m₂) := by
    ext i; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]; ring
  rw [h]
  exact posCon_add (posCon_lam_sub_wtZ m₁) (posCon_lam_sub_wtZ m₂)

/-! ## Finite-dimensionality -/

open Submission.E8Multiplicity Submission.E8Freudenthal in
/-- **`V ⧸ N` is finite-dimensional** when `N` is the maximal submodule of the Verma module
(so that `L = V ⧸ N` is the irreducible module of highest weight `ω₁+ω₈`). -/
theorem finite_quot (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) : Module.Finite ℂ (V ⧸ N) := by
  classical
  obtain ⟨L, hLnd, hLall, hL0, hL2, hL4, hL6, hL8, hL10⟩ :=
    Commons.LinearAlgebra.Matrix.Cartan.e8_lattice_count
  have hchar : ∀ w : Fin 8 → ℤ, (Submission.E8Numerics.mfun w : ℚ) = mul N w :=
    mfun_eq_mul N hvN hmax
  have hS : ∀ w : Fin 8 → ℤ, Lwt N w ≠ ⊥ → w ∈ L.toFinset := by
    intro w hw
    rw [List.mem_toFinset]
    apply hLall
    have hpos : 0 < dmul N w := by
      obtain ⟨x, hx, hx0⟩ := (Lwt N w).ne_bot_iff.mp hw
      haveI : Nontrivial ↥(Lwt N w) :=
        ⟨⟨⟨x, hx⟩, 0, fun h => hx0 (Subtype.ext_iff.mp h)⟩⟩
      exact Module.finrank_pos
    have hmul : mul N w ≠ 0 := by
      rw [mul]
      have : (0 : ℚ) < (dmul N w : ℚ) := by exact_mod_cast hpos
      exact ne_of_gt this
    have hmf : Submission.E8Numerics.mfun w ≠ 0 := by
      intro h0
      exact hmul (by rw [← hchar w, h0]; norm_num)
    have hq := (Submission.E8Support.mfun_ne_zero_iff w).mp hmf
    simp only [Submission.E8Numerics.qq] at hq
    rcases hq with h | h | h | h | h | h <;> rw [h] <;> norm_num
  have htop : L.toFinset.sup (fun w => Lwt N w) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← iSup_Lwt_eq_top]
    refine iSup_le fun w => ?_
    by_cases h : w ∈ L.toFinset
    · exact Finset.le_sup (f := fun w => Lwt N w) h
    · rw [show Lwt N w = ⊥ from by
        by_contra hne
        exact h (hS w hne)]
      exact bot_le
  haveI hsup : Module.Finite ℂ ↥(L.toFinset.sup (fun w => Lwt N w)) :=
    Submodule.finiteDimensional_finset_sup L.toFinset (fun w => Lwt N w)
  haveI : Module.Finite ℂ ↥(⊤ : Submodule ℂ (V ⧸ N)) :=
    LinearEquiv.finiteDimensional (LinearEquiv.ofEq _ _ htop)
  exact LinearEquiv.finiteDimensional (Submodule.topEquiv (R := ℂ))

/-- The tensor square of `L = V ⧸ N` is finite-dimensional. -/
theorem finite_tensor (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) : Module.Finite ℂ (T N) := by
  haveI := finite_quot N hvN hmax
  infer_instance

/-- **Independence of the weight spaces**: a non-zero vector lies in at most one `TLwt N ν`. -/
lemma eq_of_mem_TLwt_of_mem_TLwt {ν μ : Fin 8 → ℤ} {x : T N}
    (hx : x ∈ TLwt N ν) (hx' : x ∈ TLwt N μ) (hx0 : x ≠ 0) : ν = μ := by
  funext j
  have h1 := deriv_h_eq_of_mem_TLwt (N := N) j hx
  have h2 := deriv_h_eq_of_mem_TLwt (N := N) j hx'
  have hcast : (((ν j : ℤ) : ℂ)) = (((μ j : ℤ) : ℂ)) :=
    smul_left_injective ℂ hx0 (h1.symm.trans h2)
  exact Int.cast_injective hcast

end Submission.E8Tensor
