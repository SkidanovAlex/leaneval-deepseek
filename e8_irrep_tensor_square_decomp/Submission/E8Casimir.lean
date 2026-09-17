import Mathlib
import Submission.Commons.Algebra.Lie.e8_finrank
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_isKilling
import Submission.Commons.Algebra.Lie.SerreConstruction.e8W_zero_isCartan
import Submission.Commons.RepresentationTheory.LieEnveloping.adjoin_range_iota
import Submission.Commons.Algebra.Lie.Casimir.lie_commute
import Submission.WeylRoots
import Submission.Commons.LinearAlgebra.BilinForm.exists_dual_basis
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_norm_two_conj_simple

set_option maxRecDepth 100000

/-!
# The Casimir element of `e₈` and its eigenvalue on a highest-weight vector

We build the Casimir element `Ω ∈ U(e₈)` attached to the Killing form `κ` of the Serre-constructed
`e₈`, show it is central, and compute its eigenvalue on a highest-weight vector.

Ingredients:

* the Cartan subalgebra `H = e8W 0 = span {SerreH i}` (`e8W_zero_eq_span_SerreH`), with
  `IsCartanSubalgebra`;
* the **orthogonality lemma** `killingForm_eq_zero_of_add_ne_zero`: if `x ∈ e8W μ`, `y ∈ e8W ν` and
  `μ + ν ≠ 0` then `κ x y = 0`.  (Two lines from the invariance of `κ`, no trace arguments!)
* a κ-dual basis `hd` of `H`, and for each positive root `α` a pair `e_α ∈ e8W α`, `f_α ∈ e8W (-α)`
  with `κ (e_α) (f_α) = 1`;
* the family `{hᵢ} ∪ {e_α, f_α}` is orthonormal for `κ`, hence a basis (248 elements, `finrank = 248`),
  and `Casimir.lie_commute` then gives the centrality of `Ω`.
* `Ω · v = (λ, λ + 2ρ)_κ · v` for a highest weight vector of weight `λ`.
-/

set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators
open Matrix

namespace Submission.E8Casimir

open Commons.Algebra.Lie Commons.Algebra.Lie.SerreConstruction Commons.LinearAlgebra.Matrix.Cartan
open Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo

abbrev L8 : Type := LieAlgebra.e₈ ℂ

/-- The Killing form of `e₈(ℂ)`. -/
abbrev K : LinearMap.BilinForm ℂ L8 := killingForm ℂ L8

/-- Membership in the integral weight space `e8W μ`, unfolded. -/
lemma mem_e8W_iff {μ : Fin 8 → ℤ} {x : L8} :
    x ∈ e8W μ ↔ ∀ i : Fin 8, ⁅SerreH i, x⁆ = ((μ i : ℤ) : ℂ) • x := by
  rw [e8W_eq_W, mem_W_iff]

lemma killingForm_lieInvariant : K.lieInvariant L8 :=
  LieModule.traceForm_lieInvariant ℂ L8 L8

lemma killingForm_nondegenerate : (killingForm ℂ L8).Nondegenerate := by
  haveI := e8_isKilling
  exact LieAlgebra.IsKilling.killingForm_nondegenerate ℂ L8

/-- **Orthogonality of distinct weight spaces for the Killing form.**
If `x ∈ e8W μ`, `y ∈ e8W ν` and `μ + ν ≠ 0` then `κ x y = 0`. -/
theorem killingForm_eq_zero_of_add_ne_zero {μ ν : Fin 8 → ℤ} (h : μ + ν ≠ 0) {x y : L8}
    (hx : x ∈ e8W μ) (hy : y ∈ e8W ν) : K x y = 0 := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 8, μ i + ν i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (funext fun i => by have := hc i; simp only [Pi.add_apply]; omega)
  have hx' := (mem_e8W_iff.mp hx) i
  have hy' := (mem_e8W_iff.mp hy) i
  have hinv := killingForm_lieInvariant (SerreH i) x y
  rw [hx', hy'] at hinv
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at hinv
  have hzero : (((μ i : ℤ) : ℂ) + ((ν i : ℤ) : ℂ)) * K x y = 0 := by
    linear_combination hinv
  have hne : (((μ i : ℤ) : ℂ) + ((ν i : ℤ) : ℂ)) ≠ 0 := by
    intro h0
    apply hi
    have h1 : ((μ i : ℤ) : ℂ) = -((ν i : ℤ) : ℂ) := by linear_combination h0
    have h2 : (μ i : ℤ) = -(ν i : ℤ) := by exact_mod_cast h1
    omega
  exact (mul_eq_zero.mp hzero).resolve_left hne

/-- Every element of `e₈` is a finite sum of weight vectors. -/
lemma exists_decomp_weight (y : L8) :
    ∃ (s : Finset (Fin 8 → ℤ)) (g : (Fin 8 → ℤ) → L8),
      (∀ μ ∈ s, g μ ∈ e8W μ) ∧ y = ∑ μ ∈ s, g μ := by
  have hy : y ∈ ⨆ μ : Fin 8 → ℤ, e8W μ := by rw [e8W_iSup_eq_top]; trivial
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hy
  obtain ⟨g, hg, hsum⟩ := mem_iSup_finset_iff.mp hs
  exact ⟨s, g, hg, hsum⟩

/-- A linear functional of `e₈` which vanishes on every weight space is zero. -/
lemma linearMap_eq_zero_of_weight (T : L8 →ₗ[ℂ] ℂ)
    (h : ∀ μ, ∀ x ∈ e8W μ, T x = 0) : T = 0 := by
  ext z
  obtain ⟨s, g, hg, rfl⟩ := exists_decomp_weight z
  rw [map_sum]
  exact Finset.sum_eq_zero fun μ hμ => h μ _ (hg μ hμ)

/-- `κ x ·` vanishes identically on `e₈` when `x ∈ e8W 0` is orthogonal to `e8W 0`. -/
theorem killingForm_eq_zero_of_orthogonal_cartan {x : L8} (hx : x ∈ e8W 0)
    (h : ∀ y ∈ e8W 0, K x y = 0) : K x = 0 := by
  refine linearMap_eq_zero_of_weight _ fun μ y hy => ?_
  by_cases hμ0 : μ = 0
  · subst hμ0; exact h y hy
  · exact killingForm_eq_zero_of_add_ne_zero (by simpa using hμ0) hx hy

/-! ### The Cartan subalgebra and its `κ`-dual basis -/

/-- The Cartan subalgebra of `e₈`: the zero weight space `e8W 0 = span {SerreH i}`. -/
noncomputable def H : LieSubalgebra ℂ L8 :=
  e8W_zero_isCartan.choose

lemma mem_H_iff {x : L8} : x ∈ H ↔ x ∈ e8W 0 :=
  e8W_zero_isCartan.choose_spec.1 x

instance instIsCartan : H.IsCartanSubalgebra :=
  e8W_zero_isCartan.choose_spec.2

lemma serreH_mem_e8W_zero (i : Fin 8) : SerreH i ∈ e8W 0 := by
  rw [mem_e8W_iff]
  intro j
  simp [serreLie_HH]

/-- The `i`-th Serre `H`-generator, as an element of the Cartan subalgebra. -/
noncomputable def h (i : Fin 8) : H := ⟨SerreH i, mem_H_iff.mpr (serreH_mem_e8W_zero i)⟩

@[simp] lemma coe_h (i : Fin 8) : ((h i : H) : L8) = SerreH i := rfl

lemma h_linearIndependent : LinearIndependent ℂ h := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hg' : ∑ j, g j • SerreH j = 0 := by
    have := congrArg (fun z : H => (z : L8)) hg
    simpa using this
  exact Fintype.linearIndependent_iff.mp e8_H_linearIndependent g hg' i

lemma finrank_H : Module.finrank ℂ H = 8 := by
  have hsub : (H : Submodule ℂ L8) = e8W 0 := Submodule.ext fun x => mem_H_iff
  have h1 : Module.finrank ℂ ↥(e8W (0 : Fin 8 → ℤ)) = 8 := by
    rw [e8W_zero_eq_span_SerreH, finrank_span_eq_card e8_H_linearIndependent]
    simp
  have : Module.finrank ℂ ↥(H : Submodule ℂ L8) = 8 := by
    rw [hsub]; exact h1
  exact this

noncomputable def hBasis : Module.Basis (Fin 8) ℂ H :=
  basisOfLinearIndependentOfCardEqFinrank (K := ℂ) (V := H) h_linearIndependent
    (by rw [finrank_H]; simp)

lemma hBasis_apply (i : Fin 8) : ((hBasis i : H) : L8) = SerreH i := by
  have h1 : (hBasis i : H) = h i := by
    simp only [hBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
  rw [h1]; rfl

/-- The restriction of the Killing form to the Cartan subalgebra. -/
noncomputable def KH : LinearMap.BilinForm ℂ H := K.restrict (H : Submodule ℂ L8)

lemma KH_apply (u v : H) : KH u v = K (u : L8) (v : L8) := rfl

lemma KH_nondegenerate : KH.Nondegenerate := by
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · have hzero : ∀ y ∈ e8W (0 : Fin 8 → ℤ), K (u : L8) y = 0 := fun y hy => by
      have h := hu ⟨y, mem_H_iff.mpr hy⟩
      rw [KH_apply] at h
      simpa using h
    have hT : (K (u : L8)) = 0 :=
      killingForm_eq_zero_of_orthogonal_cartan (mem_H_iff.mp u.2) hzero
    exact Subtype.ext (killingForm_nondegenerate.1 (u : L8) fun z => congrFun (congrArg DFunLike.coe hT) z)
  · have hzero : ∀ y ∈ e8W (0 : Fin 8 → ℤ), K y (u : L8) = 0 := fun y hy => by
      have h := hu ⟨y, mem_H_iff.mpr hy⟩
      rw [KH_apply] at h
      simpa using h
    have hT : (K.flip (u : L8)) = 0 := by
      refine linearMap_eq_zero_of_weight _ fun μ x hx => ?_
      by_cases hμ0 : μ = 0
      · subst hμ0; exact hzero x hx
      · exact killingForm_eq_zero_of_add_ne_zero (μ := μ) (ν := 0) (by simpa using hμ0)
          hx (mem_H_iff.mp u.2)
    exact Subtype.ext (killingForm_nondegenerate.2 (u : L8)
      fun z => congrFun (congrArg DFunLike.coe hT) z)


/-! ### The `κ`-dual basis of the Cartan subalgebra -/

/-- A `κ`-dual family in the Cartan subalgebra: `κ (SerreH i) (hdual j) = δᵢⱼ`. -/
noncomputable def hdual : Fin 8 → H :=
  (Commons.LinearAlgebra.BilinForm.exists_dual_basis KH KH_nondegenerate hBasis).choose

lemma K_SerreH_hdual (i j : Fin 8) :
    K (SerreH i) (hdual j : L8) = if i = j then 1 else 0 := by
  have h := (Commons.LinearAlgebra.BilinForm.exists_dual_basis KH KH_nondegenerate hBasis).choose_spec i j
  have h' : KH (hBasis i) (hdual j) = if i = j then 1 else 0 := h
  rw [KH_apply, hBasis_apply] at h'
  simpa using h'

/-! ### The 120 positive roots, in `ω`-coordinates -/

/-- The 120 positive roots of `E₈`, in `ω`-coordinates (`μ i = ⟨μ, αᵢ∨⟩`). -/
def posR : List (Fin 8 → ℤ) := [
  ![0, 0, 0, 0, 0, 0, -1, 2],
  ![0, 0, 0, 0, 0, -1, 2, -1],
  ![0, 0, 0, 0, 0, -1, 1, 1],
  ![0, 0, 0, 0, -1, 2, -1, 0],
  ![0, 0, 0, 0, -1, 1, 1, -1],
  ![0, 0, 0, 0, -1, 1, 0, 1],
  ![0, 0, 0, -1, 2, -1, 0, 0],
  ![0, 0, 0, -1, 1, 1, -1, 0],
  ![0, 0, 0, -1, 1, 0, 1, -1],
  ![0, 0, 0, -1, 1, 0, 0, 1],
  ![0, -1, -1, 2, -1, 0, 0, 0],
  ![0, -1, -1, 1, 1, -1, 0, 0],
  ![0, -1, -1, 1, 0, 1, -1, 0],
  ![0, -1, -1, 1, 0, 0, 1, -1],
  ![0, -1, -1, 1, 0, 0, 0, 1],
  ![-1, 0, 2, -1, 0, 0, 0, 0],
  ![-1, -1, 1, 1, -1, 0, 0, 0],
  ![-1, -1, 1, 0, 1, -1, 0, 0],
  ![-1, -1, 1, 0, 0, 1, -1, 0],
  ![-1, -1, 1, 0, 0, 0, 1, -1],
  ![-1, -1, 1, 0, 0, 0, 0, 1],
  ![0, 2, 0, -1, 0, 0, 0, 0],
  ![0, 1, -1, 1, -1, 0, 0, 0],
  ![0, 1, -1, 0, 1, -1, 0, 0],
  ![0, 1, -1, 0, 0, 1, -1, 0],
  ![0, 1, -1, 0, 0, 0, 1, -1],
  ![0, 1, -1, 0, 0, 0, 0, 1],
  ![-1, 1, 1, 0, -1, 0, 0, 0],
  ![-1, 1, 1, -1, 1, -1, 0, 0],
  ![-1, 1, 1, -1, 0, 1, -1, 0],
  ![-1, 1, 1, -1, 0, 0, 1, -1],
  ![-1, 1, 1, -1, 0, 0, 0, 1],
  ![-1, 0, 0, 1, 0, -1, 0, 0],
  ![-1, 0, 0, 1, -1, 1, -1, 0],
  ![-1, 0, 0, 1, -1, 0, 1, -1],
  ![-1, 0, 0, 1, -1, 0, 0, 1],
  ![-1, 0, 0, 0, 1, 0, -1, 0],
  ![-1, 0, 0, 0, 1, -1, 1, -1],
  ![-1, 0, 0, 0, 1, -1, 0, 1],
  ![-1, 0, 0, 0, 0, 1, 0, -1],
  ![-1, 0, 0, 0, 0, 1, -1, 1],
  ![-1, 0, 0, 0, 0, 0, 1, 0],
  ![2, 0, -1, 0, 0, 0, 0, 0],
  ![1, 0, 1, -1, 0, 0, 0, 0],
  ![1, -1, 0, 1, -1, 0, 0, 0],
  ![1, -1, 0, 0, 1, -1, 0, 0],
  ![1, -1, 0, 0, 0, 1, -1, 0],
  ![1, -1, 0, 0, 0, 0, 1, -1],
  ![1, -1, 0, 0, 0, 0, 0, 1],
  ![1, 1, 0, 0, -1, 0, 0, 0],
  ![1, 1, 0, -1, 1, -1, 0, 0],
  ![1, 1, 0, -1, 0, 1, -1, 0],
  ![1, 1, 0, -1, 0, 0, 1, -1],
  ![1, 1, 0, -1, 0, 0, 0, 1],
  ![1, 0, -1, 1, 0, -1, 0, 0],
  ![1, 0, -1, 1, -1, 1, -1, 0],
  ![1, 0, -1, 1, -1, 0, 1, -1],
  ![1, 0, -1, 1, -1, 0, 0, 1],
  ![1, 0, -1, 0, 1, 0, -1, 0],
  ![1, 0, -1, 0, 1, -1, 1, -1],
  ![1, 0, -1, 0, 1, -1, 0, 1],
  ![1, 0, -1, 0, 0, 1, 0, -1],
  ![1, 0, -1, 0, 0, 1, -1, 1],
  ![1, 0, -1, 0, 0, 0, 1, 0],
  ![0, 0, 1, 0, 0, -1, 0, 0],
  ![0, 0, 1, 0, -1, 1, -1, 0],
  ![0, 0, 1, 0, -1, 0, 1, -1],
  ![0, 0, 1, 0, -1, 0, 0, 1],
  ![0, 0, 1, -1, 1, 0, -1, 0],
  ![0, 0, 1, -1, 1, -1, 1, -1],
  ![0, 0, 1, -1, 1, -1, 0, 1],
  ![0, 0, 1, -1, 0, 1, 0, -1],
  ![0, 0, 1, -1, 0, 1, -1, 1],
  ![0, 0, 1, -1, 0, 0, 1, 0],
  ![0, -1, 0, 1, 0, 0, -1, 0],
  ![0, -1, 0, 1, 0, -1, 1, -1],
  ![0, -1, 0, 1, 0, -1, 0, 1],
  ![0, -1, 0, 1, -1, 1, 0, -1],
  ![0, -1, 0, 1, -1, 1, -1, 1],
  ![0, -1, 0, 1, -1, 0, 1, 0],
  ![0, -1, 0, 0, 1, 0, 0, -1],
  ![0, -1, 0, 0, 1, 0, -1, 1],
  ![0, -1, 0, 0, 1, -1, 1, 0],
  ![0, -1, 0, 0, 0, 1, 0, 0],
  ![0, 1, 0, 0, 0, 0, -1, 0],
  ![0, 1, 0, 0, 0, -1, 1, -1],
  ![0, 1, 0, 0, 0, -1, 0, 1],
  ![0, 1, 0, 0, -1, 1, 0, -1],
  ![0, 1, 0, 0, -1, 1, -1, 1],
  ![0, 1, 0, 0, -1, 0, 1, 0],
  ![0, 1, 0, -1, 1, 0, 0, -1],
  ![0, 1, 0, -1, 1, 0, -1, 1],
  ![0, 1, 0, -1, 1, -1, 1, 0],
  ![0, 1, 0, -1, 0, 1, 0, 0],
  ![0, 0, -1, 1, 0, 0, 0, -1],
  ![0, 0, -1, 1, 0, 0, -1, 1],
  ![0, 0, -1, 1, 0, -1, 1, 0],
  ![0, 0, -1, 1, -1, 1, 0, 0],
  ![0, 0, -1, 0, 1, 0, 0, 0],
  ![-1, 0, 1, 0, 0, 0, 0, -1],
  ![-1, 0, 1, 0, 0, 0, -1, 1],
  ![-1, 0, 1, 0, 0, -1, 1, 0],
  ![-1, 0, 1, 0, -1, 1, 0, 0],
  ![-1, 0, 1, -1, 1, 0, 0, 0],
  ![-1, -1, 0, 1, 0, 0, 0, 0],
  ![-1, 1, 0, 0, 0, 0, 0, 0],
  ![1, 0, 0, 0, 0, 0, 0, -1],
  ![1, 0, 0, 0, 0, 0, -1, 1],
  ![1, 0, 0, 0, 0, -1, 1, 0],
  ![1, 0, 0, 0, -1, 1, 0, 0],
  ![1, 0, 0, -1, 1, 0, 0, 0],
  ![1, -1, -1, 1, 0, 0, 0, 0],
  ![0, -1, 1, 0, 0, 0, 0, 0],
  ![1, 1, -1, 0, 0, 0, 0, 0],
  ![0, 1, 1, -1, 0, 0, 0, 0],
  ![0, 0, 0, 1, -1, 0, 0, 0],
  ![0, 0, 0, 0, 1, -1, 0, 0],
  ![0, 0, 0, 0, 0, 1, -1, 0],
  ![0, 0, 0, 0, 0, 0, 1, -1],
  ![0, 0, 0, 0, 0, 0, 0, 1],
]

theorem posR_length : posR.length = 120 := rfl

theorem posR_nodup : posR.Nodup := by decide

/-- The `k`-th positive root of `E₈`. -/
def pR (k : Fin 120) : Fin 8 → ℤ := posR.get ⟨k.1, by rw [posR_length]; exact k.2⟩

theorem pR_injective : Function.Injective pR := by
  intro a b hab
  have h : posR.get ⟨a.1, by rw [posR_length]; exact a.2⟩ =
      posR.get ⟨b.1, by rw [posR_length]; exact b.2⟩ := hab
  have h2 := (List.Nodup.get_inj_iff posR_nodup).mp h
  exact Fin.ext (by simpa using congrArg Fin.val h2)



theorem pR_ne_zero : ∀ k : Fin 120, pR k ≠ 0 := by decide

theorem pR_qZ : ∀ k : Fin 120, qZ (pR k) = 2 := by decide

theorem pR_sum : ∀ i : Fin 8, ∑ j : Fin 120, (pR j) i = 2 := by decide

theorem pR_add_ne_zero : ∀ k l : Fin 120, pR k + pR l ≠ 0 := by decide

theorem pR_neg_add_ne_zero : ∀ k l : Fin 120, -(pR k) + -(pR l) ≠ 0 := by decide

theorem pR_e8q (k : Fin 120) : e8q (pR k) = 2 := by
  rw [e8q_eq_qZ, pR_qZ]
  norm_num

/-- The `k`-th positive root space is non-zero. -/
theorem e8W_pR_ne_bot (k : Fin 120) : e8W (pR k) ≠ ⊥ := by
  obtain ⟨L, k', hL⟩ :=
    Commons.LinearAlgebra.Matrix.Cartan.E8_norm_two_conj_simple (pR k) (pR_e8q k)
  intro hbot
  have h1 : Module.finrank ℂ ↥(e8W (pR k))
      = Module.finrank ℂ ↥(e8W (fun i => CartanMatrix.E₈ k' i)) := by
    rw [e8W_eq_wtSpace, e8W_eq_wtSpace, ← finrank_wtSpace_foldl L (pR k), hL]
  have h2 : Module.finrank ℂ ↥(e8W (fun i => CartanMatrix.E₈ k' i)) = 1 :=
    e8_simple_root_weightSpace_finrank_compat k'
  rw [hbot, finrank_bot, h2] at h1
  exact one_ne_zero h1.symm

/-- A non-zero element of the `k`-th positive root space. -/
noncomputable def eRoot (k : Fin 120) : L8 :=
  Classical.choose ((Submodule.ne_bot_iff (e8W (pR k))).mp (e8W_pR_ne_bot k))

lemma eRoot_mem (k : Fin 120) : eRoot k ∈ e8W (pR k) :=
  (Classical.choose_spec ((Submodule.ne_bot_iff (e8W (pR k))).mp (e8W_pR_ne_bot k))).1

lemma eRoot_ne_zero (k : Fin 120) : eRoot k ≠ 0 :=
  (Classical.choose_spec ((Submodule.ne_bot_iff (e8W (pR k))).mp (e8W_pR_ne_bot k))).2

/-- There is `y` in the opposite root space with `κ (eRoot k) y ≠ 0`. -/
lemma exists_fRoot (k : Fin 120) : ∃ y ∈ e8W (-(pR k)), K (eRoot k) y ≠ 0 := by
  by_contra hc
  push Not at hc
  have h2 : ∀ z : L8, K (eRoot k) z = 0 := by
    intro z
    obtain ⟨s, g, hg, rfl⟩ := exists_decomp_weight z
    rw [map_sum]
    refine Finset.sum_eq_zero fun μ hμ => ?_
    by_cases hμ0 : μ = -(pR k)
    · subst hμ0; exact hc _ (hg _ hμ)
    · refine killingForm_eq_zero_of_add_ne_zero (μ := pR k) (ν := μ) ?_ (eRoot_mem k) (hg μ hμ)
      intro hcon
      refine hμ0 ?_
      ext i
      have hh := congrFun hcon i
      simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at hh ⊢
      omega
  exact eRoot_ne_zero k (killingForm_nondegenerate.1 (eRoot k) h2)

/-- The `κ`-dual of `eRoot k` inside the opposite root space: `κ (eRoot k) (fRoot k) = 1`. -/
noncomputable def fRoot (k : Fin 120) : L8 :=
  (K (eRoot k) (Classical.choose (exists_fRoot k)))⁻¹ • Classical.choose (exists_fRoot k)

lemma fRoot_mem (k : Fin 120) : fRoot k ∈ e8W (-(pR k)) :=
  Submodule.smul_mem _ _ (Classical.choose_spec (exists_fRoot k)).1

lemma K_eRoot_fRoot (k : Fin 120) : K (eRoot k) (fRoot k) = 1 := by
  have h := (Classical.choose_spec (exists_fRoot k)).2
  rw [fRoot, map_smul, smul_eq_mul, inv_mul_cancel₀ h]

/-- Distinct weight spaces are orthogonal, so any two of the `eRoot`, `fRoot` are orthogonal
except for the paired `(eRoot k, fRoot k)`. -/
lemma K_eq_zero_of_sum_ne_zero {μ ν : Fin 8 → ℤ} (h : μ + ν ≠ 0) {x y : L8}
    (hx : x ∈ e8W μ) (hy : y ∈ e8W ν) : K x y = 0 :=
  killingForm_eq_zero_of_add_ne_zero h hx hy

lemma K_eRoot_eRoot (k l : Fin 120) : K (eRoot k) (eRoot l) = 0 :=
  K_eq_zero_of_sum_ne_zero (pR_add_ne_zero k l) (eRoot_mem k) (eRoot_mem l)

lemma K_fRoot_fRoot (k l : Fin 120) : K (fRoot k) (fRoot l) = 0 :=
  K_eq_zero_of_sum_ne_zero (pR_neg_add_ne_zero k l) (fRoot_mem k) (fRoot_mem l)

lemma K_eRoot_fRoot' (k l : Fin 120) : K (eRoot k) (fRoot l) = if k = l then 1 else 0 := by
  by_cases h : k = l
  · subst h; rw [if_pos rfl]; exact K_eRoot_fRoot k
  · rw [if_neg h]
    refine K_eq_zero_of_sum_ne_zero ?_ (eRoot_mem k) (fRoot_mem l)
    intro hcon
    have : pR k = pR l := by
      have h2 : pR k + -(pR l) = 0 := hcon
      ext i
      have hh := congrFun h2 i
      simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at hh
      omega
    exact h (pR_injective this)

lemma K_symm : ∀ x y : L8, K x y = K y x :=
  fun x y => (LinearMap.BilinForm.isSymm_iff.mpr (LieModule.traceForm_isSymm ℂ L8 L8)).eq x y

lemma K_fRoot_eRoot (k l : Fin 120) : K (fRoot k) (eRoot l) = if k = l then 1 else 0 := by
  rw [K_symm]
  simpa [eq_comm] using K_eRoot_fRoot' l k

/-! ### The orthonormal basis of `e₈` attached to the Killing form -/

/-- Index set for the basis `{SerreH i} ∪ {eRoot k} ∪ {fRoot k}` (248 elements). -/
abbrev Idx : Type := Fin 8 ⊕ (Fin 120 ⊕ Fin 120)

/-- The 248-element family `{SerreH i} ∪ {eRoot k} ∪ {fRoot k}`. -/
noncomputable def bFam : Idx → L8
  | Sum.inl i => SerreH i
  | Sum.inr (Sum.inl k) => eRoot k
  | Sum.inr (Sum.inr k) => fRoot k

/-- The `κ`-dual family. -/
noncomputable def bDual : Idx → L8
  | Sum.inl i => ((hdual i : H) : L8)
  | Sum.inr (Sum.inl k) => fRoot k
  | Sum.inr (Sum.inr k) => eRoot k

@[simp] lemma bFam_inl (i : Fin 8) : bFam (Sum.inl i) = SerreH i := rfl
@[simp] lemma bFam_inr_inl (k : Fin 120) : bFam (Sum.inr (Sum.inl k)) = eRoot k := rfl
@[simp] lemma bFam_inr_inr (k : Fin 120) : bFam (Sum.inr (Sum.inr k)) = fRoot k := rfl
@[simp] lemma bDual_inl (i : Fin 8) : bDual (Sum.inl i) = ((hdual i : H) : L8) := rfl
@[simp] lemma bDual_inr_inl (k : Fin 120) : bDual (Sum.inr (Sum.inl k)) = fRoot k := rfl
@[simp] lemma bDual_inr_inr (k : Fin 120) : bDual (Sum.inr (Sum.inr k)) = eRoot k := rfl

lemma fRoot_ne_zero (k : Fin 120) : fRoot k ≠ 0 := by
  intro h
  have h1 := K_eRoot_fRoot k
  rw [h, map_zero] at h1
  exact one_ne_zero h1.symm

lemma hdual_mem_e8W_zero (j : Fin 8) : ((hdual j : H) : L8) ∈ e8W 0 :=
  mem_H_iff.mp (hdual j).2

lemma K_of_mem_H_of_mem_ne {μ : Fin 8 → ℤ} (hμ : μ ≠ 0) {x y : L8} (hx : x ∈ e8W 0)
    (hy : y ∈ e8W μ) : K x y = 0 :=
  killingForm_eq_zero_of_add_ne_zero (μ := 0) (ν := μ) (by simpa using hμ) hx hy

lemma K_of_mem_ne_of_mem_H {μ : Fin 8 → ℤ} (hμ : μ ≠ 0) {x y : L8} (hx : x ∈ e8W μ)
    (hy : y ∈ e8W 0) : K x y = 0 :=
  killingForm_eq_zero_of_add_ne_zero (μ := μ) (ν := 0) (by simpa using hμ) hx hy

@[simp] lemma K_SerreH_eRoot (i : Fin 8) (l : Fin 120) : K (SerreH i) (eRoot l) = 0 :=
  K_of_mem_H_of_mem_ne (pR_ne_zero l) (serreH_mem_e8W_zero i) (eRoot_mem l)

@[simp] lemma K_SerreH_fRoot (i : Fin 8) (l : Fin 120) : K (SerreH i) (fRoot l) = 0 :=
  K_of_mem_H_of_mem_ne (neg_ne_zero.mpr (pR_ne_zero l)) (serreH_mem_e8W_zero i) (fRoot_mem l)

@[simp] lemma K_eRoot_SerreH (k : Fin 120) (j : Fin 8) : K (eRoot k) (SerreH j) = 0 :=
  K_of_mem_ne_of_mem_H (pR_ne_zero k) (eRoot_mem k) (serreH_mem_e8W_zero j)

@[simp] lemma K_fRoot_SerreH (k : Fin 120) (j : Fin 8) : K (fRoot k) (SerreH j) = 0 :=
  K_of_mem_ne_of_mem_H (neg_ne_zero.mpr (pR_ne_zero k)) (fRoot_mem k) (serreH_mem_e8W_zero j)

@[simp] lemma K_eRoot_hdual (k : Fin 120) (j : Fin 8) :
    K (eRoot k) ((hdual j : H) : L8) = 0 :=
  K_of_mem_ne_of_mem_H (pR_ne_zero k) (eRoot_mem k) (hdual_mem_e8W_zero j)

@[simp] lemma K_fRoot_hdual (k : Fin 120) (j : Fin 8) :
    K (fRoot k) ((hdual j : H) : L8) = 0 :=
  K_of_mem_ne_of_mem_H (neg_ne_zero.mpr (pR_ne_zero k)) (fRoot_mem k) (hdual_mem_e8W_zero j)

@[simp] lemma K_hdual_eRoot (j : Fin 8) (k : Fin 120) :
    K ((hdual j : H) : L8) (eRoot k) = 0 :=
  K_of_mem_H_of_mem_ne (pR_ne_zero k) (hdual_mem_e8W_zero j) (eRoot_mem k)

@[simp] lemma K_hdual_fRoot (j : Fin 8) (k : Fin 120) :
    K ((hdual j : H) : L8) (fRoot k) = 0 :=
  K_of_mem_H_of_mem_ne (neg_ne_zero.mpr (pR_ne_zero k)) (hdual_mem_e8W_zero j) (fRoot_mem k)

@[simp] lemma K_hdual_SerreH (i j : Fin 8) :
    K ((hdual i : H) : L8) (SerreH j) = if i = j then 1 else 0 := by
  rw [K_symm, K_SerreH_hdual]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem K_bFam_bDual (a b : Idx) : K (bFam a) (bDual b) = if a = b then 1 else 0 := by
  rcases a with i | (k | k) <;> rcases b with j | (l | l) <;>
    simp only [bFam_inl, bFam_inr_inl, bFam_inr_inr, bDual_inl, bDual_inr_inl, bDual_inr_inr,
      K_SerreH_hdual, K_hdual_SerreH, K_eRoot_fRoot', K_fRoot_eRoot, K_SerreH_eRoot,
      K_SerreH_fRoot, K_eRoot_hdual, K_fRoot_hdual, K_eRoot_SerreH, K_fRoot_SerreH,
      K_hdual_eRoot, K_hdual_fRoot, K_eRoot_eRoot, K_fRoot_fRoot] <;>
    simp [Sum.inl.injEq, Sum.inr.injEq]

theorem K_bDual_bFam (a b : Idx) : K (bDual a) (bFam b) = if a = b then 1 else 0 := by
  rcases a with i | (k | k) <;> rcases b with j | (l | l) <;>
    simp only [bFam_inl, bFam_inr_inl, bFam_inr_inr, bDual_inl, bDual_inr_inl, bDual_inr_inr,
      K_SerreH_hdual, K_hdual_SerreH, K_eRoot_fRoot', K_fRoot_eRoot, K_SerreH_eRoot,
      K_SerreH_fRoot, K_eRoot_hdual, K_fRoot_hdual, K_eRoot_SerreH, K_fRoot_SerreH,
      K_hdual_eRoot, K_hdual_fRoot, K_eRoot_eRoot, K_fRoot_fRoot] <;>
    simp [Sum.inl.injEq, Sum.inr.injEq]

theorem bFam_linearIndependent : LinearIndependent ℂ bFam := by
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have h := congrArg (fun z => K z (bDual i)) hsum
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, map_zero,
    smul_eq_mul] at h
  have h3 : ∑ j ∈ s, g j * K (bFam j) (bDual i) = g i * K (bFam i) (bDual i) := by
    refine Finset.sum_eq_single i ?_ ?_
    · intro b hb hbi
      simp [K_bFam_bDual, hbi]
    · intro hi'
      exact absurd hi hi'
  rw [h3, K_bFam_bDual, if_pos rfl, mul_one] at h
  exact h

theorem card_Idx : Fintype.card Idx = Module.finrank ℂ L8 := by
  rw [e8_finrank]
  simp only [Idx, Fintype.card_sum, Fintype.card_fin]

/-- The `κ`-orthonormal basis of `e₈` made of the Cartan basis and the root vectors. -/
noncomputable def bIdx : Module.Basis Idx ℂ L8 :=
  basisOfLinearIndependentOfCardEqFinrank bFam_linearIndependent card_Idx

lemma bIdx_apply (a : Idx) : bIdx a = bFam a :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank bFam_linearIndependent card_Idx) a

lemma bIdx_repr (v : L8) : v = ∑ a : Idx, K v (bDual a) • bIdx a :=
  Commons.Algebra.Lie.Casimir.repr_dual K bIdx bDual
    (fun i j => by rw [bIdx_apply]; exact K_bFam_bDual i j) v

/-! ### The Casimir element -/

/-- The Casimir element of `e₈` attached to the Killing form. -/
noncomputable def Omega : UniversalEnvelopingAlgebra ℂ L8 :=
  ∑ a : Idx, UniversalEnvelopingAlgebra.ι ℂ (bIdx a) *
    UniversalEnvelopingAlgebra.ι ℂ (bDual a)

theorem K_isSymm : K.IsSymm :=
  LinearMap.BilinForm.isSymm_iff.mpr (LieModule.traceForm_isSymm ℂ L8 L8)

/-- **The Casimir element is central.** -/
theorem Omega_central (x : L8) :
    UniversalEnvelopingAlgebra.ι ℂ x * Omega = Omega * UniversalEnvelopingAlgebra.ι ℂ x := by
  have h := Commons.Algebra.Lie.Casimir.lie_commute K K_isSymm killingForm_lieInvariant bIdx bDual
    (fun i j => by rw [bIdx_apply]; exact K_bFam_bDual i j)
    (fun i j => by rw [bIdx_apply]; exact K_bDual_bFam i j) x
  simpa [Omega] using h

/-! ### The `κ`-dual of an integral weight, and the coroot identity -/

/-- The element of the Cartan subalgebra which is `κ`-dual to the functional `μ`, realised as
`∑ j, μ j • (hdual j)`; it satisfies `κ (SerreH i) (wdual μ) = μ i`. -/
noncomputable def wdual (μ : Fin 8 → ℤ) : L8 :=
  ∑ j : Fin 8, ((μ j : ℤ) : ℂ) • ((hdual j : H) : L8)

lemma K_SerreH_wdual (i : Fin 8) (μ : Fin 8 → ℤ) :
    K (SerreH i) (wdual μ) = ((μ i : ℤ) : ℂ) := by
  simp [wdual, K_SerreH_hdual]

lemma K_wdual_SerreH (μ : Fin 8 → ℤ) (j : Fin 8) :
    K (wdual μ) (SerreH j) = ((μ j : ℤ) : ℂ) := by
  simp [wdual, K_hdual_SerreH]

lemma wdual_mem_cartan (μ : Fin 8 → ℤ) : wdual μ ∈ e8W 0 := by
  have h : ∀ j : Fin 8, ((hdual j : H) : L8) ∈ e8W 0 := fun j => mem_H_iff.mp (hdual j).2
  rw [wdual]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (h j)

/-- The linear functional `y ↦ κ y (wdual μ)` on `e₈`. -/
noncomputable def rootFun (μ : Fin 8 → ℤ) : L8 →ₗ[ℂ] ℂ := K.flip (wdual μ)

lemma rootFun_apply (μ : Fin 8 → ℤ) (y : L8) : rootFun μ y = K y (wdual μ) := rfl

/-- Weight vectors bracket into the sum of the weight spaces. -/
lemma lie_mem_e8W {μ ν : Fin 8 → ℤ} {x y : L8} (hx : x ∈ e8W μ) (hy : y ∈ e8W ν) :
    ⁅x, y⁆ ∈ e8W (μ + ν) := by
  rw [mem_e8W_iff] at hx hy ⊢
  intro i
  rw [leibniz_lie, hx i, hy i, smul_lie, lie_smul, Pi.add_apply, Int.cast_add, add_smul]

/-- On the Cartan subalgebra, `eRoot k` raises by the weight `pR k`. -/
lemma lie_eRoot_of_mem_cartan (k : Fin 120) {y : L8} (hy : y ∈ e8W 0) :
    ⁅eRoot k, y⁆ = - (rootFun (pR k) y) • eRoot k := by
  have hspan : y ∈ Submodule.span ℂ (Set.range SerreH) := by
    rw [← e8W_zero_eq_span_SerreH]; exact hy
  have hgen : ∀ i : Fin 8,
      ⁅eRoot k, SerreH i⁆ = - (rootFun (pR k) (SerreH i)) • eRoot k := by
    intro i
    rw [rootFun_apply, K_SerreH_wdual, ← lie_skew, mem_e8W_iff.mp (eRoot_mem k) i]
    rw [← neg_smul]
  have hker : Submodule.span ℂ (Set.range SerreH) ≤
      LinearMap.ker (LieAlgebra.ad ℂ L8 (eRoot k) + (rootFun (pR k)).smulRight (eRoot k)) := by
    rw [Submodule.span_le]
    intro z hz
    obtain ⟨i, rfl⟩ := hz
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.add_apply, LieAlgebra.ad_apply,
      LinearMap.smulRight_apply, hgen i]
    simp
  have hy' := hker hspan
  rw [LinearMap.mem_ker, LinearMap.add_apply, LieAlgebra.ad_apply,
    LinearMap.smulRight_apply] at hy'
  rw [eq_neg_of_add_eq_zero_left hy', neg_smul]

/-- **The coroot identity**: `⁅eRoot k, fRoot k⁆` is the `κ`-dual of the root `pR k`. -/
theorem eRoot_comm_fRoot (k : Fin 120) : ⁅eRoot k, fRoot k⁆ = wdual (pR k) := by
  have hmem : ⁅eRoot k, fRoot k⁆ - wdual (pR k) ∈ e8W 0 := by
    refine Submodule.sub_mem _ ?_ (wdual_mem_cartan _)
    have h := lie_mem_e8W (eRoot_mem k) (fRoot_mem k)
    simpa using h
  have hsum : ∀ y ∈ e8W 0, K (⁅eRoot k, fRoot k⁆ - wdual (pR k)) y = 0 := by
    intro y hy
    have h1 : K ⁅eRoot k, fRoot k⁆ y = -K (fRoot k) ⁅eRoot k, y⁆ :=
      killingForm_lieInvariant (eRoot k) (fRoot k) y
    have h2 : K (fRoot k) (eRoot k) = 1 := by simpa using K_fRoot_eRoot k k
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero, h1, lie_eRoot_of_mem_cartan k hy,
      map_smul, smul_eq_mul, h2, mul_one, neg_neg, rootFun_apply]
    exact K_symm y (wdual (pR k))
  have hd0 : (⟨⁅eRoot k, fRoot k⁆ - wdual (pR k), mem_H_iff.mpr hmem⟩ : H) = 0 :=
    KH_nondegenerate.1 ⟨_, mem_H_iff.mpr hmem⟩ (fun u => by
      rw [KH_apply]
      exact hsum (u : L8) (mem_H_iff.mp u.2))
  exact sub_eq_zero.mp (congrArg (fun z : H => (z : L8)) hd0)

/-! ### The Casimir eigenvalue on a highest weight vector -/

/-- The element `2ρ` in `ω`-coordinates (`ρ = (1,…,1)`). -/
def twoRho : Fin 8 → ℤ := fun _ => 2

lemma wdual_add (μ ν : Fin 8 → ℤ) : wdual (μ + ν) = wdual μ + wdual ν := by
  simp only [wdual, Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]

lemma wdual_sum_pR : (∑ k : Fin 120, wdual (pR k)) = wdual twoRho := by
  have h : ∀ j : Fin 8, (∑ k : Fin 120, (((pR k) j : ℤ) : ℂ)) = 2 := by
    intro j
    have h2 : (((∑ k : Fin 120, (pR k) j : ℤ)) : ℂ) = 2 := by
      rw [pR_sum j]; norm_num
    calc ∑ k : Fin 120, (((pR k) j : ℤ) : ℂ)
        = (((∑ k : Fin 120, (pR k) j : ℤ)) : ℂ) := by
          push_cast; rfl
      _ = 2 := h2
  simp only [wdual]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul, h j]
  rfl

lemma K_wdual_wdual_add (μ ν : Fin 8 → ℤ) :
    K (wdual μ) (wdual (μ + ν)) = K (wdual μ) (wdual μ) + K (wdual μ) (wdual ν) := by
  rw [wdual_add, map_add]

lemma wdual_eq_sum (μ : Fin 8 → ℤ) :
    wdual μ = ∑ i : Fin 8, ((μ i : ℤ) : ℂ) • ((hdual i : H) : L8) := rfl

section Eigenvalue

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [LieRingModule L8 M] [LieModule ℂ L8 M]

/-- On a vector of weight `lam`, every element of the Cartan subalgebra acts by the corresponding
value of the `κ`-dual functional. -/
lemma lie_of_mem_cartan_of_weight (lam : Fin 8 → ℤ) {v : M}
    (hv : ∀ i, ⁅SerreH i, v⁆ = ((lam i : ℤ) : ℂ) • v) {y : L8} (hy : y ∈ e8W 0) :
    ⁅y, v⁆ = (K (wdual lam) y) • v := by
  have hspan : y ∈ Submodule.span ℂ (Set.range SerreH) := by
    rw [← e8W_zero_eq_span_SerreH]; exact hy
  have key : ∀ z ∈ Submodule.span ℂ (Set.range SerreH),
      ⁅z, v⁆ = (K (wdual lam) z) • v := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem u hu =>
        obtain ⟨i, rfl⟩ := hu
        rw [K_wdual_SerreH, hv i]
    | zero => simp
    | add a b _ _ ha hb => rw [add_lie, ha, hb, map_add, add_smul]
    | smul c a _ ha =>
        rw [smul_lie, ha, map_smul]
        module
  exact key y hspan

/-- **The Casimir eigenvalue.**  On a highest weight vector `v` of weight `lam` (killed by all the
raising operators `eRoot k`), the Casimir element of `e₈` acts by the scalar
`(lam, lam + 2ρ)_κ = κ (wdual lam) (wdual lam + wdual 2ρ)` for the Killing form `κ`. -/
theorem Omega_smul_highest_weight [Module (UniversalEnvelopingAlgebra ℂ L8) M]
    (hι : ∀ (x : L8) (m : M), (UniversalEnvelopingAlgebra.ι ℂ x) • m = ⁅x, m⁆)
    (lam : Fin 8 → ℤ) {v : M}
    (hv : ∀ i, ⁅SerreH i, v⁆ = ((lam i : ℤ) : ℂ) • v)
    (he : ∀ k : Fin 120, ⁅eRoot k, v⁆ = 0) :
    Omega • v = (K (wdual lam) (wdual (lam + twoRho))) • v := by
  have hι2 : ∀ (x y : L8), (UniversalEnvelopingAlgebra.ι ℂ x * UniversalEnvelopingAlgebra.ι ℂ y) • v
      = ⁅x, ⁅y, v⁆⁆ := by
    intro x y
    rw [mul_smul, hι x, hι y]
  have hOmega : Omega • v = ∑ a : Idx, ⁅bIdx a, ⁅bDual a, v⁆⁆ := by
    rw [Omega, Finset.sum_smul]
    exact Finset.sum_congr rfl fun a _ => hι2 (bIdx a) (bDual a)
  -- split the sum over the three blocks
  have hsplit : (∑ a : Idx, ⁅bIdx a, ⁅bDual a, v⁆⁆)
      = (∑ i : Fin 8, ⁅SerreH i, ⁅((hdual i : H) : L8), v⁆⁆)
        + (∑ k : Fin 120, ⁅eRoot k, ⁅fRoot k, v⁆⁆)
        + (∑ k : Fin 120, ⁅fRoot k, ⁅eRoot k, v⁆⁆) := by
    simp only [bIdx_apply, bFam_inl, bFam_inr_inl, bFam_inr_inr,
      bDual_inl, bDual_inr_inl, bDual_inr_inr, Fintype.sum_sum_type]
    abel
  -- the `fRoot · eRoot` terms vanish
  have hzero : (∑ k : Fin 120, ⁅fRoot k, ⁅eRoot k, v⁆⁆) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [he k]; simp
  -- the Cartan block
  have hH : (∑ i : Fin 8, ⁅SerreH i, ⁅((hdual i : H) : L8), v⁆⁆)
      = (K (wdual lam) (wdual lam)) • v := by
    have hterm : ∀ i : Fin 8, ⁅SerreH i, ⁅((hdual i : H) : L8), v⁆⁆
        = ((K (wdual lam) ((hdual i : H) : L8)) * (((lam i : ℤ) : ℂ))) • v := by
      intro i
      rw [lie_of_mem_cartan_of_weight lam hv (hdual_mem_e8W_zero i), lie_smul, hv i,
        ← smul_smul]
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_smul]
    congr 1
    -- `wdual lam = ∑ i, K (wdual lam) (SerreH i) • hdual i`
    have hexp : wdual lam = ∑ i : Fin 8, K (wdual lam) (SerreH i) • ((hdual i : H) : L8) := by
      conv_lhs => rw [wdual_eq_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [K_wdual_SerreH]
    calc ∑ i : Fin 8, K (wdual lam) ((hdual i : H) : L8) * ((lam i : ℤ) : ℂ)
        = ∑ i : Fin 8, K (wdual lam) ((hdual i : H) : L8) * K (wdual lam) (SerreH i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [K_wdual_SerreH]
      _ = K (wdual lam) (∑ i : Fin 8, K (wdual lam) (SerreH i) • ((hdual i : H) : L8)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul, smul_eq_mul, mul_comm]
      _ = K (wdual lam) (wdual lam) := by rw [← hexp]
  -- the `eRoot · fRoot` block
  have hE : (∑ k : Fin 120, ⁅eRoot k, ⁅fRoot k, v⁆⁆)
      = (K (wdual lam) (wdual twoRho)) • v := by
    have hterm : ∀ k : Fin 120, ⁅eRoot k, ⁅fRoot k, v⁆⁆
        = (K (wdual lam) (wdual (pR k))) • v := by
      intro k
      rw [leibniz_lie, he k, lie_zero, add_zero, eRoot_comm_fRoot k,
        lie_of_mem_cartan_of_weight lam hv (wdual_mem_cartan (pR k))]
    rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.sum_smul, ← map_sum, wdual_sum_pR]
  rw [hOmega, hsplit, hzero, add_zero, hH, hE, ← add_smul, K_wdual_wdual_add]

end Eigenvalue

/-- The Casimir element commutes with every element of the enveloping algebra. -/
theorem Omega_mul_comm (u : UniversalEnvelopingAlgebra ℂ L8) : Omega * u = u * Omega := by
  have key : ∀ u ∈ Algebra.adjoin ℂ
      (Set.range (UniversalEnvelopingAlgebra.ι ℂ : L8 → UniversalEnvelopingAlgebra ℂ L8)),
      Omega * u = u * Omega := by
    intro u hu
    refine Algebra.adjoin_induction (p := fun x _ => Omega * x = x * Omega) ?_ ?_ ?_ ?_ hu
    · intro x hx
      obtain ⟨y, rfl⟩ := hx
      exact (Omega_central y).symm
    · intro c
      exact (Algebra.commutes c Omega).symm
    · intro a b _ _ ha hb
      rw [mul_add, add_mul, ha, hb]
    · intro a b _ _ ha hb
      calc Omega * (a * b) = (Omega * a) * b := (mul_assoc _ _ _).symm
        _ = (a * Omega) * b := by rw [ha]
        _ = a * (Omega * b) := mul_assoc _ _ _
        _ = a * (b * Omega) := by rw [hb]
        _ = (a * b) * Omega := (mul_assoc _ _ _).symm
  exact key u (by rw [Commons.RepresentationTheory.LieEnveloping.adjoin_range_iota]; trivial)

section Cyclic

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  [Module (UniversalEnvelopingAlgebra ℂ L8) M]
  [SMulCommClass ℂ (UniversalEnvelopingAlgebra ℂ L8) M]

/-- If a module over `U(e₈)` is generated by a single vector `v` on which the Casimir element acts
by the scalar `c`, then the Casimir acts by `c` on the whole module. -/
theorem Omega_smul_of_cyclic (v : M)
    (hgen : ∀ m : M, ∃ u : UniversalEnvelopingAlgebra ℂ L8, u • v = m)
    (c : ℂ) (hv : Omega • v = c • v) :
    ∀ m : M, Omega • m = c • m := by
  intro m
  obtain ⟨u, rfl⟩ := hgen m
  calc Omega • (u • v) = (Omega * u) • v := (mul_smul _ _ _).symm
    _ = (u * Omega) • v := by rw [Omega_mul_comm]
    _ = u • (Omega • v) := mul_smul _ _ _
    _ = u • (c • v) := by rw [hv]
    _ = c • (u • v) := (smul_comm c u v).symm

end Cyclic

end Submission.E8Casimir
