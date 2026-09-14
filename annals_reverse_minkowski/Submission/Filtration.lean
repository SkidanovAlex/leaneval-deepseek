import Mathlib
import ChallengeDeps
import Submission.QuotientLattice
import Submission.Uncrossing
import Submission.StableLattices
import Submission.Commons.LinearAlgebra.GramMatrix.gram_change_det
import Submission.SubLattice
import Submission.Commons.Lattice.Discrete.discreteTopology_of_le
import Submission.Commons.Lattice.Minimizer.finite_sublattices_det_le
import Submission.Commons.Geometry.LowerHull.exists_lower_hull_chain
import Submission.Commons.Geometry.LowerHull.vertex_below_chord
import Submission.Commons.Lattice.Determinant.det_lt_of_lt_same_rank

open Module Real Matrix
open Submission.QuotientLattice
open Submission.Uncrossing
open Submission.StableLattices
open scoped Real BigOperators InnerProductSpace RealInnerProductSpace
set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Canonical filtration machinery (paper §2.5, Prop. 2.7) — part 1: basics

This module collects the [B]-block infrastructure for the final reduction in Theorem 1.2:
scaling of determinants, mass inequalities along a primitive filtration chain, the ambient
orthogonal direct sum of the quotients, and stability of orthogonal direct sums.

The genuinely extremal part (existence of the canonical filtration with the "above the
segment" determinant inequalities, increasing slopes) will be built in later sessions on
top of this module; everything here is unconditional.
-/

namespace Submission.Filtration

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

noncomputable section

/-! ## Determinant of the trivial lattice and of scaled lattices -/

/-- The zero lattice has determinant one. -/
lemma det_bot : ReverseMinkowski.determinant (⊥ : Submodule ℤ E) = 1 := by
  classical
  unfold ReverseMinkowski.determinant
  have hfin0 : finrank ℤ (⊥ : Submodule ℤ E) = 0 := by
    haveI : DiscreteTopology (⊥ : Submodule ℤ E) := discrete_bot
    haveI : Module.Free ℤ (⊥ : Submodule ℤ E) := instModuleFree_of_discrete_submodule (⊥ : Submodule ℤ E)
    haveI : Module.Finite ℤ (⊥ : Submodule ℤ E) := instModuleFinite_of_discrete_submodule (⊥ : Submodule ℤ E)
    exact Module.finrank_eq_zero_of_subsingleton ℤ (⊥ : Submodule ℤ E)
  have hdet : ((ReverseMinkowski.B (⊥ : Submodule ℤ E)).transpose * ReverseMinkowski.B (⊥ : Submodule ℤ E)).det = 1 := by
    apply Matrix.det_eq_one_of_card_eq_zero
    simp [hfin0]
  rw [hdet]
  norm_num

/-- Multiplication by a nonzero real `α` is a `ℤ`-linear equivalence `ℒ ≃ₗ[ℤ] α•ℒ`. -/
def smulLinEquiv (α : ℝ) (hα : α ≠ 0) (ℒ : Submodule ℤ E) : ℒ ≃ₗ[ℤ] smulLattice α ℒ where
  toFun := fun y => ⟨α • (y : E), by
    rw [mem_smulLattice]
    exact ⟨y, y.2, rfl⟩⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    dsimp
    rw [smul_add]
  map_smul' := by
    intro k x
    apply Subtype.ext
    dsimp
    calc
      α • (k • (x : E)) = α • ((k : ℝ) • (x : E)) := by rw [Int.cast_smul_eq_zsmul ℝ k (x : E)]
      _ = ((k : ℝ) * α) • (x : E) := by rw [smul_smul, mul_comm]
      _ = (k : ℝ) • (α • (x : E)) := by rw [smul_smul]
      _ = k • (α • (x : E)) := by rw [Int.cast_smul_eq_zsmul ℝ k (α • (x : E))]
  invFun := fun z => ⟨(α⁻¹ : ℝ) • (z : E), by
    rcases (mem_smulLattice.mp z.2) with ⟨y, hy, hzy⟩
    have hz1 : (α⁻¹ : ℝ) • (z : E) = (y : E) := by
      rw [← hzy]
      rw [smul_smul]
      rw [inv_mul_cancel₀ hα, one_smul]
    exact by simpa [hz1] using hy⟩
  left_inv := by
    intro y
    apply Subtype.ext
    dsimp
    rw [smul_smul]
    rw [inv_mul_cancel₀ hα, one_smul]
  right_inv := by
    intro z
    apply Subtype.ext
    dsimp
    rw [smul_smul]
    rw [mul_inv_cancel₀ hα, one_smul]

/-- Scaling by any real `α` keeps a discrete lattice discrete (for `α = 0` the image is
the zero lattice, which is discrete). -/
instance discrete_smulLattice_inst (α : ℝ) (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    DiscreteTopology (smulLattice α ℒ) := by
  classical
  by_cases hα : α = 0
  · have hbot : smulLattice α ℒ = ⊥ := by
      apply le_bot_iff.mp
      intro z hz
      rcases (mem_smulLattice.mp hz) with ⟨y, hy, hzy⟩
      have hz0 : z = 0 := by
        rw [← hzy, hα]
        simp
      simpa [hz0] using (Submodule.zero_mem (⊥ : Submodule ℤ E))
    rw [hbot]
    exact discrete_bot
  · exact discrete_smulLattice α hα ℒ

/-- `smulLinEquiv` preserves ambient values: `((e y : α•ℒ) : E) = α • (y : E)`. -/
lemma smulLinEquiv_apply (α : ℝ) (hα : α ≠ 0) (ℒ : Submodule ℤ E) (y : ℒ) :
    (((smulLinEquiv α hα ℒ y : smulLattice α ℒ) : E)) = α • (y : E) := by
  rfl

/-- Scaling a lattice by `α ≠ 0` does not change its `ℤ`-rank. -/
lemma finrank_smulLattice (α : ℝ) (hα : α ≠ 0) (ℒ : Submodule ℤ E) :
    finrank ℤ (smulLattice α ℒ) = finrank ℤ ℒ := by
  exact (LinearEquiv.finrank_eq (smulLinEquiv α hα ℒ)).symm

/-- Determinant of a scaled lattice: `det(α•ℒ) = |α|^r · det ℒ`, `r = finrank ℤ ℒ`. -/
lemma det_smulLattice (α : ℝ) (hα : α ≠ 0) (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    ReverseMinkowski.determinant (smulLattice α ℒ) =
      |α| ^ (finrank ℤ ℒ) * ReverseMinkowski.determinant ℒ := by
  classical
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  let r : ℕ := finrank ℤ ℒ
  let v : Module.Basis (Fin r) ℤ ℒ := Module.finBasis ℤ ℒ
  let e : ℒ ≃ₗ[ℤ] smulLattice α ℒ := smulLinEquiv α hα ℒ
  let β : Module.Basis (Fin r) ℤ (smulLattice α ℒ) := v.map e
  haveI : Module.Free ℤ (smulLattice α ℒ) := Module.Free.of_basis β
  haveI : Module.Finite ℤ (smulLattice α ℒ) := Module.Finite.of_basis β
  let u : Fin r → E := fun j => ((v j : ℒ) : E)
  let w : Fin r → E := fun j => α • ((v j : ℒ) : E)
  have hβval : ∀ j : Fin r, ((β j : smulLattice α ℒ) : E) = w j := by
    intro j
    dsimp [β, w]
    exact smulLinEquiv_apply α hα ℒ (v j)
  have hgβw : Matrix.gram ℝ (fun j : Fin r => ((β j : smulLattice α ℒ) : E)) = Matrix.gram ℝ w := by
    ext a b
    simp [Matrix.gram, hβval]
  have hdetS : ReverseMinkowski.determinant (smulLattice α ℒ) =
      √((Matrix.gram ℝ w).det) := by
    calc
      ReverseMinkowski.determinant (smulLattice α ℒ) =
          √((Matrix.gram ℝ (fun j : Fin r => ((β j : smulLattice α ℒ) : E))).det) := by
            simpa using (Submission.Uncrossing.det_eq_sqrt_gram_any_basis (L := smulLattice α ℒ) β)
      _ = √((Matrix.gram ℝ w).det) := by rw [hgβw]
  have hdetL : ReverseMinkowski.determinant ℒ =
      √((Matrix.gram ℝ u).det) := by
    simpa [u] using (Submission.Uncrossing.det_eq_sqrt_gram_any_basis (L := ℒ) v)
  have hgw : (Matrix.gram ℝ w).det = α ^ (2 * r) * (Matrix.gram ℝ u).det := by
    have hmat : Matrix.gram ℝ w = (α ^ 2) • Matrix.gram ℝ u := by
      ext a b
      dsimp [Matrix.gram, w, u]
      rw [real_inner_smul_left, real_inner_smul_right]
      ring
    calc
      (Matrix.gram ℝ w).det = ((α ^ 2) • Matrix.gram ℝ u).det := by rw [hmat]
      _ = (α ^ 2) ^ Fintype.card (Fin r) * (Matrix.gram ℝ u).det := by rw [Matrix.det_smul]
      _ = (α ^ 2) ^ r * (Matrix.gram ℝ u).det := by rw [Fintype.card_fin]
      _ = α ^ (2 * r) * (Matrix.gram ℝ u).det := by rw [pow_mul]
  have hnonneg_u : 0 ≤ (Matrix.gram ℝ u).det :=
    (Matrix.posSemidef_gram ℝ u).det_nonneg
  have hsq : (α ^ r) ^ 2 = α ^ (2 * r) := by
    rw [← pow_mul]
    rw [show r * 2 = 2 * r by ring]
  have hsqrt : √(α ^ (2 * r) * (Matrix.gram ℝ u).det) =
      |α| ^ r * √((Matrix.gram ℝ u).det) := by
    calc
      √(α ^ (2 * r) * (Matrix.gram ℝ u).det) = √((α ^ r) ^ 2 * (Matrix.gram ℝ u).det) := by rw [← hsq]
      _ = √((α ^ r) ^ 2) * √((Matrix.gram ℝ u).det) := by
        rw [Real.sqrt_mul (sq_nonneg (α ^ r))]
      _ = |α ^ r| * √((Matrix.gram ℝ u).det) := by rw [Real.sqrt_sq_eq_abs]
      _ = |α| ^ r * √((Matrix.gram ℝ u).det) := by rw [abs_pow]
  calc
    ReverseMinkowski.determinant (smulLattice α ℒ) = √((Matrix.gram ℝ w).det) := hdetS
    _ = √(α ^ (2 * r) * (Matrix.gram ℝ u).det) := by rw [hgw]
    _ = |α| ^ r * √((Matrix.gram ℝ u).det) := hsqrt
    _ = |α| ^ r * ReverseMinkowski.determinant ℒ := by rw [hdetL]
    _ = |α| ^ (finrank ℤ ℒ) * ReverseMinkowski.determinant ℒ := by
      simp [r]

/-! ## Gaussian mass along a primitive filtration chain -/

/-- Determinant of a scaled lattice for a positive scale (no absolute value):
`det(α•ℒ) = α^r · det ℒ` for `0 < α`. -/
lemma det_smulLattice_pos (α : ℝ) (hα0 : 0 < α) (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    ReverseMinkowski.determinant (smulLattice α ℒ) =
      α ^ (finrank ℤ ℒ) * ReverseMinkowski.determinant ℒ := by
  rw [det_smulLattice α (ne_of_gt hα0) ℒ]
  rw [abs_of_nonneg (le_of_lt hα0)]

/-- Gaussian mass over the zero lattice is `1`. -/
lemma mass_bot (s : ℝ) : mass s (⊥ : Submodule ℤ E) = 1 := by
  classical
  dsimp [mass]
  let e : (⊥ : Submodule ℤ E) ≃ Unit := {
    toFun := fun _ => Unit.unit
    invFun := fun _ => ⟨0, by simp⟩
    left_inv := by
      intro y
      apply Subtype.ext
      have hy : (y : E) = 0 := (Submodule.mem_bot (R := ℤ) (M := E)).mp y.property
      exact hy.symm
    right_inv := by intro u; cases u; rfl }
  calc
    (∑' y : (⊥ : Submodule ℤ E), Real.exp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2))
        = ∑' u : Unit, Real.exp (-Real.pi * ‖((e.symm u : (⊥ : Submodule ℤ E)) : E)‖ ^ 2 / s ^ 2) := by
          exact (Equiv.tsum_eq e.symm (fun y : (⊥ : Submodule ℤ E) =>
            Real.exp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2))).symm
    _ = Real.exp (-Real.pi * ‖((e.symm Unit.unit : (⊥ : Submodule ℤ E)) : E)‖ ^ 2 / s ^ 2) := by
          rw [tsum_fintype]
          simp
    _ = 1 := by simp [e]

/-- The quotient piece `Lᵢ₊₁/Lᵢ` of a chain, realized by orthogonal projection. -/
def quotPiece (L : ℕ → Submodule ℤ E) (i : ℕ) : Submodule ℤ E :=
  quotLattice (L (i + 1)) (realSpan (L i))

/-- **Gaussian mass along a chain**: for a finite primitive filtration
`L₀ = ⊥ ≤ L₁ ≤ ⋯ ≤ L_k`, `ρ_s(L_k) ≤ ∏ᵢ ρ_s(Lᵢ₊₁/Lᵢ)`. -/
lemma mass_le_chain_quot_prod {k : ℕ} (L : ℕ → Submodule ℤ E)
    (h0 : L 0 = ⊥) (hchain : ∀ i, i < k → L i ≤ L (i + 1))
    (hprim : ∀ i, i < k → Primitive (L i) (L (i + 1)))
    (hLk : DiscreteTopology (L k)) (s : ℝ) (hs : 0 < s) :
    mass s (L k) ≤ ∏ i ∈ Finset.range k, mass s (quotPiece L i) := by
  classical
  induction k with
  | zero =>
      simp [h0, mass_bot]
  | succ k ih =>
      have hLk' : DiscreteTopology (L (k + 1)) := hLk
      haveI : DiscreteTopology (L (k + 1)) := hLk'
      haveI : DiscreteTopology (L k) := by
        exact Submission.LatticeBasics.discreteTopology_of_le (ℒ := L (k + 1)) (ℒ' := L k)
          (hchain k (Nat.lt_succ_self k))
      have hprimQ : Primitive (L k) (L (k + 1)) := hprim k (Nat.lt_succ_self k)
      have hstep : mass s (L (k + 1)) ≤ mass s (L k) * mass s (quotPiece L k) := by
        dsimp [quotPiece]
        haveI : DiscreteTopology (quotLattice (L (k + 1)) (realSpan (L k))) :=
          discrete_quotLattice (ℒ' := L k) (ℒ := L (k + 1)) (realSpan (L k)) (by rfl) hprimQ
        exact mass_le_mul_quot (ℒ' := L k) (ℒ := L (k + 1)) (S := realSpan (L k)) (by rfl) hprimQ s hs
      have hIH := ih (fun i hi => hchain i (Nat.lt_trans hi (Nat.lt_succ_self k)))
        (fun i hi => hprim i (Nat.lt_trans hi (Nat.lt_succ_self k))) (inferInstance : DiscreteTopology (L k))
      calc
        mass s (L (k + 1)) ≤ mass s (L k) * mass s (quotPiece L k) := hstep
        _ ≤ (∏ i ∈ Finset.range k, mass s (quotPiece L i)) * mass s (quotPiece L k) := by
          exact mul_le_mul_of_nonneg_right hIH (mass_nonneg (quotPiece L k) s)
        _ = ∏ i ∈ Finset.range (k + 1), mass s (quotPiece L i) := by
          rw [Finset.prod_range_succ]

/-! ## Orthogonality of the chain quotients and the ambient-sum mass identity -/

/-- Elements of the step-`i` quotient lie in the real span of `Lᵢ₊₁`. -/
lemma quotPiece_mem_realSpan_next {L : ℕ → Submodule ℤ E} {i : ℕ} (hstep : L i ≤ L (i + 1))
    {x : E} (hx : x ∈ quotPiece L i) : x ∈ realSpan (L (i + 1)) := by
  classical
  rcases (mem_quotLattice.mp hx) with ⟨y, hy, hxy⟩
  have hy' : (y : E) ∈ realSpan (L (i + 1)) := mem_realSpan (ℒ := L (i + 1)) hy
  have hz : ((realSpan (L i)).starProjection (y : E)) ∈ realSpan (L (i + 1)) := by
    have hs : realSpan (L i) ≤ realSpan (L (i + 1)) :=
      Submission.Uncrossing.realSpan_mono hstep
    exact hs (Submodule.starProjection_apply_mem (realSpan (L i)) (y : E))
  have hxy' : x = (y : E) - (realSpan (L i)).starProjection (y : E) := by
    rw [← hxy]
    rw [proj_orth_comp (realSpan (L i)) (y : E)]
  rw [hxy']
  exact Submodule.sub_mem (realSpan (L (i + 1))) hy' hz

/-- Elements of the step-`i` quotient lie in the orthogonal complement of the real span
of `Lᵢ`. -/
lemma quotPiece_mem_orth_prev {L : ℕ → Submodule ℤ E} {i : ℕ} {x : E} (hx : x ∈ quotPiece L i) :
    x ∈ (realSpan (L i))ᗮ := by
  exact quotLattice_le_orthogonal (L (i + 1)) (realSpan (L i)) hx

/-- Real span of a later element of a chain contains the earlier ones. -/
lemma realSpan_mem_of_chain (L : ℕ → Submodule ℤ E) (i : ℕ) {j : ℕ} :
    i < j → (∀ t, i ≤ t → t < j → L t ≤ L (t + 1)) → ∀ {x : E},
      x ∈ realSpan (L i) → x ∈ realSpan (L j) := by
  classical
  intro hij
  induction j with
  | zero => omega
  | succ j ih =>
      intro hstep x hx
      by_cases hlt : i < j
      · have hx' : x ∈ realSpan (L j) :=
          ih hlt (fun t ht1 ht2 => hstep t ht1 (Nat.lt_trans ht2 (Nat.lt_succ_self j))) hx
        exact Submission.Uncrossing.realSpan_mono (hstep j (le_of_lt hlt) (Nat.lt_succ_self j)) hx'
      · have heq : i = j := by omega
        subst i
        exact Submission.Uncrossing.realSpan_mono (hstep j (Nat.le_refl j) (Nat.lt_succ_self j)) hx

/-- For `i < j`, the quotient pieces `Qᵢ` and `Qⱼ` are elementwise orthogonal. -/
lemma quotPiece_orthogonal_of_lt {L : ℕ → Submodule ℤ E} {i j : ℕ}
    (hchain : ∀ t, i ≤ t → t < j → L t ≤ L (t + 1)) (hij : i < j) :
    OrthogonalPair (quotPiece L i) (quotPiece L j) := by
  intro x hx y hy
  have hxspan : x ∈ realSpan (L j) := by
    -- x ∈ realSpan (L (i+1)), and i+1 ≤ j
    have hx1 : x ∈ realSpan (L (i + 1)) := quotPiece_mem_realSpan_next (hchain i (Nat.le_refl i) hij) hx
    by_cases hij' : i + 1 < j
    · have hx2 : x ∈ realSpan (L j) :=
        realSpan_mem_of_chain L (i + 1) hij' (fun t ht1 ht2 => hchain t (Nat.le_trans (Nat.le_succ i) ht1) ht2) hx1
      exact hx2
    · have heq : i + 1 = j := by omega
      rw [← heq]
      exact hx1
  have hyorth : y ∈ (realSpan (L j))ᗮ := quotPiece_mem_orth_prev (L := L) (i := j) hy
  exact (Submodule.mem_orthogonal (K := realSpan (L j)) y).mp hyorth x hxspan

/-- Any two distinct quotient pieces of a chain are orthogonal (wrapped for `Fin`-indexed
use). -/
lemma quotPiece_orthogonal_fin {L : ℕ → Submodule ℤ E} {k : ℕ}
    (hchain : ∀ i, i < k → L i ≤ L (i + 1)) (i j : Fin k) (hij : i ≠ j) :
    OrthogonalPair (quotPiece L i.val) (quotPiece L j.val) := by
  have hc : i.val < j.val ∨ j.val < i.val := by omega
  rcases hc with hlt | hlt
  · exact quotPiece_orthogonal_of_lt (L := L) (i := i.val) (j := j.val)
      (fun t ht1 ht2 => hchain t (Nat.lt_trans ht2 j.isLt)) hlt
  · have hsym : OrthogonalPair (quotPiece L j.val) (quotPiece L i.val) :=
      quotPiece_orthogonal_of_lt (L := L) (i := j.val) (j := i.val)
        (fun t ht1 ht2 => hchain t (Nat.lt_trans ht2 i.isLt)) hlt
    intro x hx y hy
    have h' : ⟪(y : E), (x : E)⟫_ℝ = 0 := hsym y hy x hx
    rw [real_inner_comm]
    exact h'

/-- Scaling preserves elementwise orthogonality. -/
lemma orthogonal_smul {W₁ W₂ : Submodule ℤ E} (hop : OrthogonalPair W₁ W₂) (α₁ α₂ : ℝ) :
    OrthogonalPair (smulLattice α₁ W₁) (smulLattice α₂ W₂) := by
  intro x hx y hy
  rcases (mem_smulLattice.mp hx) with ⟨x₀, hx₀, hx0⟩
  rcases (mem_smulLattice.mp hy) with ⟨y₀, hy₀, hy0⟩
  have horth : ⟪(x₀ : E), (y₀ : E)⟫_ℝ = 0 := hop (x₀ : E) hx₀ (y₀ : E) hy₀
  rw [← hx0, ← hy0]
  rw [real_inner_smul_left, real_inner_smul_right]
  rw [horth]
  ring

/-- A lattice that appears at or before position `k` in a chain is contained in `L_k`. -/
lemma chain_le (L : ℕ → Submodule ℤ E) : ∀ {k : ℕ}, (∀ i, i < k → L i ≤ L (i + 1)) →
    ∀ {i : ℕ}, i ≤ k → L i ≤ L k := by
  classical
  intro k hchain
  induction k with
  | zero =>
      intro i hi
      have h : i = 0 := by omega
      subst h
      rfl
  | succ k ih =>
      intro i hi
      by_cases his : i ≤ k
      · have h1 : L i ≤ L k := ih (fun t ht => hchain t (Nat.lt_trans ht (Nat.lt_succ_self k))) his
        exact le_trans h1 (hchain k (Nat.lt_succ_self k))
      · have heq : i = k + 1 := by omega
        subst i
        rfl

/-- **Reduction along a chain (ambient sum)**: for a primitive filtration
`L₀ = ⊥ ≤ ⋯ ≤ L_k` with `0 < αᵢ ≤ 1`, the Gaussian mass of `L_k` is at most the mass of
the ambient orthogonal sum `⨆ᵢ (αᵢ · Lᵢ₊₁/Lᵢ)` of the scaled quotient pieces. -/
theorem mass_le_mass_sum_scaled {k : ℕ} (L : ℕ → Submodule ℤ E) (α : ℕ → ℝ)
    (h0 : L 0 = ⊥) (hchain : ∀ i, i < k → L i ≤ L (i + 1))
    (hprim : ∀ i, i < k → Primitive (L i) (L (i + 1)))
    (hα0 : ∀ i, i < k → 0 < α i) (hα1 : ∀ i, i < k → α i ≤ 1)
    (hLk : DiscreteTopology (L k)) (s : ℝ) (hs : 0 < s) :
    mass s (L k) ≤ mass s (⨆ i : Fin k, smulLattice (α i.val) (quotPiece L i.val)) := by
  classical
  haveI : DiscreteTopology (L k) := hLk
  let W : Fin k → Submodule ℤ E := fun i => quotPiece L i.val
  let S₀ : Submodule ℤ E := ⨆ i : Fin k, W i
  have hS₀ : S₀ = ⨆ i : Fin k, W i := rfl
  have hdiscW : ∀ i : Fin k, DiscreteTopology (W i) := by
    intro i
    have h1 : L i.val ≤ L k := chain_le L hchain (Nat.le_of_lt i.isLt)
    have h2 : L (i.val + 1) ≤ L k := chain_le L hchain (by omega)
    haveI : DiscreteTopology (L i.val) :=
      Submission.LatticeBasics.discreteTopology_of_le (ℒ := L k) (ℒ' := L i.val) h1
    haveI : DiscreteTopology (L (i.val + 1)) :=
      Submission.LatticeBasics.discreteTopology_of_le (ℒ := L k) (ℒ' := L (i.val + 1)) h2
    dsimp [W]
    exact discrete_quotLattice (ℒ' := L i.val) (ℒ := L (i.val + 1)) (realSpan (L i.val)) rfl
      (hprim i.val i.isLt)
  have horthW : ∀ i j : Fin k, i ≠ j → OrthogonalPair (W i) (W j) := by
    intro i j hij
    dsimp [W]
    exact quotPiece_orthogonal_fin hchain i j hij
  haveI : DiscreteTopology S₀ := discrete_supFam k W horthW hdiscW S₀ hS₀
  -- product over the chain pieces
  have hcl := mass_le_chain_quot_prod L h0 hchain hprim hLk s hs
  have hchainprod : mass s (L k) ≤ ∏ i ∈ Finset.range k, mass s (quotPiece L i) := hcl
  -- the product over range k equals the product over Fin k (reindexed through W)
  have hWval : ∀ i : Fin k, mass s (W i) = mass s (quotPiece L i.val) := by
    intro i
    rfl
  have hprod_fin : (∏ i : Fin k, mass s (W i)) = ∏ i ∈ Finset.range k, mass s (quotPiece L i) := by
    rw [Finset.prod_fin_eq_prod_range]
    apply Finset.prod_congr rfl
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    rw [dif_pos hik]
  -- mass of the ambient sum equals the product
  have hprod_sum : mass s S₀ = ∏ i : Fin k, mass s (W i) := by
    exact mass_finFam_prod (W := W) (S := S₀) hS₀ horthW hdiscW s hs
  -- scaled pieces: definitions
  let α' : Fin k → ℝ := fun i => α i.val
  let W' : Fin k → Submodule ℤ E := fun i => smulLattice (α i.val) (W i)
  let S' : Submodule ℤ E := ⨆ i : Fin k, W' i
  have hS' : S' = ⨆ i : Fin k, smulLattice (α' i) (W i) := by rfl
  have horthW' : ∀ i j : Fin k, i ≠ j → OrthogonalPair (W' i) (W' j) := by
    intro i j hij
    dsimp [W']
    exact orthogonal_smul (horthW i j hij) (α i.val) (α j.val)
  have hdiscW' : ∀ i : Fin k, DiscreteTopology (W' i) := by
    intro i
    dsimp [W']
    infer_instance
  haveI : DiscreteTopology S' := discrete_supFam k W' horthW' hdiscW' S' (by rfl)
  have hα0' : ∀ i : Fin k, 0 < α' i := by intro i; dsimp [α']; exact hα0 i.val i.isLt
  have hα1' : ∀ i : Fin k, α' i ≤ 1 := by intro i; dsimp [α']; exact hα1 i.val i.isLt
  have hprod_scaled : mass s S₀ ≤ mass s S' := by
    exact mass_finFam_le_scaled (W := W) (S := S₀) hS₀ horthW hdiscW α' hα0' hα1' S' hS' s hs
  calc
    mass s (L k) ≤ ∏ i ∈ Finset.range k, mass s (quotPiece L i) := hchainprod
    _ = ∏ i : Fin k, mass s (W i) := hprod_fin.symm
    _ = mass s S₀ := hprod_sum.symm
    _ ≤ mass s S' := hprod_scaled
    _ = mass s (⨆ i : Fin k, smulLattice (α i.val) (quotPiece L i.val)) := by
      rfl



/-! ## Determinant monotonicity for equal-rank submodules -/

/-- For two discrete lattices of the same `ℤ`-rank with `N ≤ L`, the smaller one has the
larger determinant: `det L ≤ det N`.  (A Gram change-of-basis argument: an integer
`r × r` matrix of nonzero determinant connects the bases, and its determinant squared is
at least one.) -/
lemma det_le_of_submodule_same_rank {N L : Submodule ℤ E} [DiscreteTopology N]
    [DiscreteTopology L] (hNL : N ≤ L) (hr : finrank ℤ N = finrank ℤ L) :
    ReverseMinkowski.determinant L ≤ ReverseMinkowski.determinant N := by
  classical
  haveI : Module.Free ℤ N := instModuleFree_of_discrete_submodule N
  haveI : Module.Finite ℤ N := instModuleFinite_of_discrete_submodule N
  haveI : Module.Free ℤ L := instModuleFree_of_discrete_submodule L
  haveI : Module.Finite ℤ L := instModuleFinite_of_discrete_submodule L
  let r : ℕ := finrank ℤ N
  let f : Module.Basis (Fin r) ℤ N := Module.finBasis ℤ N
  let e : Module.Basis (Fin r) ℤ L := (Module.finBasis ℤ L).reindex (finCongr hr.symm)
  let u : Fin r → E := fun i => ((e i : L) : E)
  let v : Fin r → E := fun i => ((f i : N) : E)
  have hxL : ∀ j : Fin r, ((f j : N) : E) ∈ L := by
    intro j
    exact hNL (f j).2
  let xL : Fin r → L := fun j => ⟨((f j : N) : E), hxL j⟩
  let A : Matrix (Fin r) (Fin r) ℤ := fun j i => e.repr (xL j) i
  have hfe : ∀ j : Fin r, v j = ∑ i : Fin r, (A j i : ℝ) • u i := by
    intro j
    have hExp := ambient_basis_expand (ℒ := L) (b := e) (xL j)
    calc
      v j = ((xL j : L) : E) := rfl
      _ = ∑ i : Fin r, (e.repr (xL j) i : ℤ) • ((e i : L) : E) := hExp
      _ = ∑ i : Fin r, (A j i : ℝ) • u i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Int.cast_smul_eq_zsmul ℝ (A j i) ((e i : L) : E)]
  have hdetL : ReverseMinkowski.determinant L = √((Matrix.gram ℝ u).det) := by
    simpa [u] using (Submission.Uncrossing.det_eq_sqrt_gram_any_basis (L := L) e)
  have hdetN : ReverseMinkowski.determinant N = √((Matrix.gram ℝ v).det) := by
    simpa [v] using (Submission.Uncrossing.det_eq_sqrt_gram_any_basis (L := N) f)
  have hlinU : LinearIndependent ℝ u := by
    dsimp [u]
    exact Commons.LinearAlgebra.Independence.discrete_basis_values_linIndep (ℒ := L) e
  have hlinV : LinearIndependent ℝ v := by
    dsimp [v]
    exact Commons.LinearAlgebra.Independence.discrete_basis_values_linIndep (ℒ := N) f
  have hgV_ne0 : (Matrix.gram ℝ v).det ≠ 0 := by
    exact (Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ)).2 hlinV
  have hgc := Commons.LinearAlgebra.GramMatrix.gram_change_det (e := u) (f := v) A hfe
  let A' : Matrix (Fin r) (Fin r) ℝ := A.map (fun z : ℤ => (z : ℝ))
  have hdAℤ_ne0 : A.det ≠ 0 := by
    intro hA0
    have hcast0 : A'.det = (A.det : ℝ) := by
      dsimp [A']
      rw [← Int.cast_det A]
    have hA'0 : A'.det = 0 := by
      rw [hcast0, hA0]
      norm_num
    have hsq0 : A'.det ^ 2 = 0 := by rw [hA'0]; norm_num
    have hgsq : (Matrix.gram ℝ v).det = 0 := by
      rw [hgc]
      rw [hsq0]
      ring
    exact hgV_ne0 hgsq
  have hAabs : 1 ≤ (A'.det) ^ 2 := by
    have hz : (1 : ℤ) ≤ |A.det| := Int.one_le_abs hdAℤ_ne0
    have hzℝ : (1 : ℝ) ≤ ((|A.det| : ℤ) : ℝ) := by exact_mod_cast hz
    have hzℝ2 : (1 : ℝ) ≤ ((|A.det| : ℤ) : ℝ) ^ 2 := by nlinarith
    have hcast : A'.det = (A.det : ℝ) := by
      dsimp [A']
      rw [← Int.cast_det A]
    rw [hcast]
    rw [← sq_abs (A.det : ℝ)]
    rw [← Int.cast_abs]
    exact hzℝ2
  have hgU0 : 0 ≤ (Matrix.gram ℝ u).det := (Matrix.posSemidef_gram ℝ u).det_nonneg
  have hgumul : (Matrix.gram ℝ u).det ≤ A'.det ^ 2 * (Matrix.gram ℝ u).det := by
    exact le_mul_of_one_le_left hgU0 (by simpa [A'] using hAabs)
  have hdet_le_gram : √((Matrix.gram ℝ u).det) ≤ √((Matrix.gram ℝ v).det) := by
    calc
      √((Matrix.gram ℝ u).det) ≤ √(A'.det ^ 2 * (Matrix.gram ℝ u).det) := Real.sqrt_le_sqrt hgumul
      _ = √((Matrix.gram ℝ v).det) := by
        congr 1
        rw [hgc]
  calc
    ReverseMinkowski.determinant L = √((Matrix.gram ℝ u).det) := hdetL
    _ ≤ √((Matrix.gram ℝ v).det) := hdet_le_gram
    _ = ReverseMinkowski.determinant N := hdetN.symm

/-- The left summand of an orthogonal pair is ambient-primitive in the sum. -/
lemma primitive_left_of_orthogonal {W₁ W₂ : Submodule ℤ E} (hop : OrthogonalPair W₁ W₂) :
    Primitive W₁ (W₁ ⊔ W₂) := by
  intro x
  constructor
  · intro hx
    exact ⟨(le_sup_left : W₁ ≤ W₁ ⊔ W₂) hx, mem_realSpan (ℒ := W₁) hx⟩
  · rintro ⟨hxsup, hxspan⟩
    rcases (Submodule.mem_sup.mp hxsup) with ⟨a, ha, b, hb, hxeq⟩
    have hxb : ⟪x, b⟫_ℝ = 0 := orth_pair_left_span hop x hxspan b hb
    have hab0 : ⟪a, b⟫_ℝ = 0 := hop a ha b hb
    have hbb : ‖b‖ = 0 := by
      have hxb' : ⟪a + b, b⟫_ℝ = 0 := by simpa [← hxeq] using hxb
      have hsum : ⟪a + b, b⟫_ℝ = ⟪a, b⟫_ℝ + ⟪b, b⟫_ℝ := by rw [inner_add_left]
      have hsq : ‖b‖ ^ 2 = ⟪b, b⟫_ℝ := by
        rw [real_inner_self_eq_norm_sq]
      have : ‖b‖ ^ 2 = 0 := by nlinarith
      nlinarith [sq_nonneg ‖b‖]
    have hb0 : b = 0 := norm_eq_zero.mp hbb
    have hxmem : a + b ∈ W₁ := by simpa [hb0] using ha
    simpa [hxeq] using hxmem

/-- A primitive sublattice of an ambient restricts to a primitive sublattice of any
sublattice of the ambient that contains it. -/
lemma primitive_of_le {L' L'' L : Submodule ℤ E} (hp : Primitive L' L)
    (hL''L : L'' ≤ L) (hL'L'' : L' ≤ L'') : Primitive L' L'' := by
  intro x
  constructor
  · intro hx
    exact ⟨hL'L'' hx, mem_realSpan (ℒ := L') hx⟩
  · rintro ⟨hxL'', hxspan⟩
    have hxL : x ∈ L := hL''L hxL''
    exact (hp x).mpr ⟨hxL, hxspan⟩

/-- For an orthogonal pair, the orthogonal projection of the sum onto `(realSpan W₁)ᗮ`
is exactly `W₂`. -/
lemma quot_orthogonal_sup_eq_right {W₁ W₂ : Submodule ℤ E} (hop : OrthogonalPair W₁ W₂) :
    quotLattice (W₁ ⊔ W₂) (realSpan W₁) = W₂ := by
  classical
  apply le_antisymm
  · intro x hx
    rcases (mem_quotLattice.mp hx) with ⟨y, hy, hproj⟩
    rcases (Submodule.mem_sup.mp hy) with ⟨a, ha, b, hb, hyeq⟩
    have hb_orth : b ∈ (realSpan W₁)ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro z hz
      exact orth_pair_left_span hop z hz b hb
    have hproj_eq : (realSpan W₁)ᗮ.starProjection y = b := by
      have hzero : (realSpan W₁)ᗮ.starProjection a = 0 :=
        starProjection_orthogonal_eq_zero_of_mem (realSpan W₁) (mem_realSpan (ℒ := W₁) ha)
      have hfix : (realSpan W₁)ᗮ.starProjection b = b :=
        (Submodule.starProjection_eq_self_iff).mpr hb_orth
      calc
        (realSpan W₁)ᗮ.starProjection y = (realSpan W₁)ᗮ.starProjection (a + b) := by rw [← hyeq]
        _ = (realSpan W₁)ᗮ.starProjection a + (realSpan W₁)ᗮ.starProjection b := by rw [map_add]
        _ = b := by rw [hzero, hfix, zero_add]
    have hxb : x = b := by
      rw [← hproj]
      exact hproj_eq
    exact hxb ▸ hb
  · intro x hx
    rw [mem_quotLattice]
    refine ⟨0 + x, ?_, ?_⟩
    · exact Submodule.add_mem (W₁ ⊔ W₂) (Submodule.zero_mem (W₁ ⊔ W₂))
        ((le_sup_right : W₂ ≤ W₁ ⊔ W₂) hx)
    · have hx_orth : x ∈ (realSpan W₁)ᗮ := by
        rw [Submodule.mem_orthogonal]
        intro z hz
        exact orth_pair_left_span hop z hz x hx
      have hfix : (realSpan W₁)ᗮ.starProjection x = x :=
        (Submodule.starProjection_eq_self_iff).mpr hx_orth
      simp [hfix]

/-- The projection of `W₁ ⊔ N` onto `(realSpan W₁)ᗮ` lies in `W₂`, when
`N ≤ W₁ ⊔ W₂` and `W₁ ⟂ W₂`. -/
lemma quot_orthogonal_sup_le_right {W₁ W₂ N : Submodule ℤ E} (hop : OrthogonalPair W₁ W₂)
    (hN : N ≤ W₁ ⊔ W₂) :
    quotLattice (W₁ ⊔ N) (realSpan W₁) ≤ W₂ := by
  classical
  intro x hx
  rcases (mem_quotLattice.mp hx) with ⟨y, hy, hproj⟩
  rcases (Submodule.mem_sup.mp hy) with ⟨a, ha, m, hm, hyeq⟩
  have hmSup : m ∈ W₁ ⊔ W₂ := hN hm
  rcases (Submodule.mem_sup.mp hmSup) with ⟨c, hc, d, hd, hmeq⟩
  have hd_orth : d ∈ (realSpan W₁)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    exact orth_pair_left_span hop z hz d hd
  have hfix : (realSpan W₁)ᗮ.starProjection d = d :=
    (Submodule.starProjection_eq_self_iff).mpr hd_orth
  have hzero (t : E) (ht : t ∈ W₁) : (realSpan W₁)ᗮ.starProjection t = 0 :=
    starProjection_orthogonal_eq_zero_of_mem (realSpan W₁) (mem_realSpan (ℒ := W₁) ht)
  have hproj_eq : (realSpan W₁)ᗮ.starProjection y = d := by
    calc
      (realSpan W₁)ᗮ.starProjection y = (realSpan W₁)ᗮ.starProjection (a + (c + d)) := by
        rw [← hyeq, ← hmeq]
      _ = (realSpan W₁)ᗮ.starProjection a + (realSpan W₁)ᗮ.starProjection (c + d) := by rw [map_add]
      _ = (realSpan W₁)ᗮ.starProjection a + ((realSpan W₁)ᗮ.starProjection c + (realSpan W₁)ᗮ.starProjection d) := by rw [map_add]
      _ = d := by rw [hzero a ha, hzero c hc, hfix, zero_add, zero_add]
  have hxb : x = d := by
    rw [← hproj]
    exact hproj_eq
  exact hxb ▸ hd

/-- Determinant of an orthogonal ambient sum: `det(W₁ ⊔ W₂) = det W₁ · det W₂`. -/
lemma det_sup_orthogonal {W₁ W₂ : Submodule ℤ E} [DiscreteTopology W₁] [DiscreteTopology W₂]
    [DiscreteTopology ↥(W₁ ⊔ W₂)] (hop : OrthogonalPair W₁ W₂) :
    ReverseMinkowski.determinant (W₁ ⊔ W₂) = ReverseMinkowski.determinant W₁ *
      ReverseMinkowski.determinant W₂ := by
  classical
  have hprim : Primitive W₁ (W₁ ⊔ W₂) := primitive_left_of_orthogonal hop
  have hq_eq : quotLattice (W₁ ⊔ W₂) (realSpan W₁) = W₂ := quot_orthogonal_sup_eq_right hop
  haveI : DiscreteTopology ↥(quotLattice (W₁ ⊔ W₂) (realSpan W₁)) := by
    rw [hq_eq]
    infer_instance
  have hq : ReverseMinkowski.determinant (quotLattice (W₁ ⊔ W₂) (realSpan W₁)) =
      ReverseMinkowski.determinant (W₁ ⊔ W₂) / ReverseMinkowski.determinant W₁ := by
    exact Submission.SubLattice.determinant_quot_generic (nA := n) (ℒ' := W₁) (ℒ := W₁ ⊔ W₂)
      (realSpan W₁) rfl hprim
  have hqW₂ : ReverseMinkowski.determinant (quotLattice (W₁ ⊔ W₂) (realSpan W₁)) =
      ReverseMinkowski.determinant W₂ := by
    exact Submission.Uncrossing.det_eq_of_eq
      (L₁ := quotLattice (W₁ ⊔ W₂) (realSpan W₁)) (L₂ := W₂) hq_eq
  have hpos : ReverseMinkowski.determinant W₁ ≠ 0 := ne_of_gt (det_pos (L := W₁))
  calc
    ReverseMinkowski.determinant (W₁ ⊔ W₂) =
        (ReverseMinkowski.determinant (W₁ ⊔ W₂) / ReverseMinkowski.determinant W₁) *
          ReverseMinkowski.determinant W₁ := by
            field_simp [hpos]
    _ = ReverseMinkowski.determinant (quotLattice (W₁ ⊔ W₂) (realSpan W₁)) *
        ReverseMinkowski.determinant W₁ := by
          rw [← hq]
    _ = ReverseMinkowski.determinant W₂ * ReverseMinkowski.determinant W₁ := by rw [hqW₂]
    _ = ReverseMinkowski.determinant W₁ * ReverseMinkowski.determinant W₂ := by ring

/-- The primitive closure of `M` inside `sup`: elements of `sup` lying in `realSpan M`. -/
def primitiveClosure (sup M : Submodule ℤ E) : Submodule ℤ E :=
  sup ⊓ (realSpan M).restrictScalars ℤ

lemma mem_primitiveClosure {sup M : Submodule ℤ E} {x : E} :
    x ∈ primitiveClosure sup M ↔ x ∈ sup ∧ x ∈ realSpan M := by
  rfl

/-- Real span is unchanged by taking the primitive closure. -/
lemma realSpan_closure_eq {sup M : Submodule ℤ E} (hM : M ≤ sup) :
    realSpan (primitiveClosure sup M) = realSpan M := by
  classical
  apply le_antisymm
  · change Submodule.span ℝ ((primitiveClosure sup M : Submodule ℤ E) : Set E) ≤ realSpan M
    rw [Submodule.span_le]
    intro x hx
    exact (Submodule.mem_inf.mp hx).2
  · have hMle : M ≤ primitiveClosure sup M := by
      intro x hx
      exact (mem_primitiveClosure).mpr ⟨hM hx, mem_realSpan (ℒ := M) hx⟩
    exact realSpan_mono (L₁ := M) (L₂ := primitiveClosure sup M) hMle

/-- The primitive closure of `M` in `sup` is ambient-primitive in `sup`. -/
lemma closure_primitive {sup M : Submodule ℤ E} (hM : M ≤ sup) :
    Primitive (primitiveClosure sup M) sup := by
  classical
  intro x
  constructor
  · intro hx
    exact ⟨(Submodule.mem_inf.mp hx).1, mem_realSpan (ℒ := primitiveClosure sup M) hx⟩
  · rintro ⟨hxsup, hxspan⟩
    rw [mem_primitiveClosure]
    have hspan' : x ∈ realSpan M := by
      simpa [realSpan_closure_eq hM] using hxspan
    exact ⟨hxsup, hspan'⟩

/-- The ℤ-ranks of `M` and its primitive closure coincide. -/
lemma finrank_closure_eq {sup M : Submodule ℤ E} [DiscreteTopology M]
    [DiscreteTopology ↥sup] (hM : M ≤ sup) :
    Module.finrank ℤ ↥(primitiveClosure sup M) = Module.finrank ℤ ↥M := by
  classical
  haveI : DiscreteTopology ↥(primitiveClosure sup M) :=
    Commons.Lattice.Discrete.discreteTopology_of_le (n := n) (ℒ := sup)
      (ℒ' := primitiveClosure sup M) (inf_le_left : primitiveClosure sup M ≤ sup)
  have h1 : Module.finrank ℝ ↥(realSpan (primitiveClosure sup M)) = Module.finrank ℤ ↥(primitiveClosure sup M) := by
    change Module.finrank ℝ ↥(Submodule.span ℝ ((primitiveClosure sup M : Submodule ℤ E) : Set E)) =
      Module.finrank ℤ ↥(primitiveClosure sup M)
    exact Commons.Lattice.Discrete.finrank_span_eq_finrank n (primitiveClosure sup M)
  have h2 : Module.finrank ℝ ↥(realSpan M) = Module.finrank ℤ ↥M := by
    change Module.finrank ℝ ↥(Submodule.span ℝ (M : Set E)) = Module.finrank ℤ ↥M
    exact Commons.Lattice.Discrete.finrank_span_eq_finrank n M
  calc
    Module.finrank ℤ ↥(primitiveClosure sup M) = Module.finrank ℝ ↥(realSpan (primitiveClosure sup M)) := h1.symm
    _ = Module.finrank ℝ ↥(realSpan M) := by rw [realSpan_closure_eq hM]
    _ = Module.finrank ℤ ↥M := h2

/-- Determinant of a sublattice dominates that of its primitive closure:
`det M̂ ≤ det M`. -/
lemma det_closure_le_det {sup M : Submodule ℤ E} [DiscreteTopology M]
    [DiscreteTopology ↥sup] [DiscreteTopology ↥(primitiveClosure sup M)] (hM : M ≤ sup) :
    ReverseMinkowski.determinant (primitiveClosure sup M) ≤ ReverseMinkowski.determinant M := by
  classical
  have hMle : M ≤ primitiveClosure sup M := by
    intro x hx
    exact (mem_primitiveClosure).mpr ⟨hM hx, mem_realSpan (ℒ := M) hx⟩
  exact det_le_of_submodule_same_rank (N := M) (L := primitiveClosure sup M) hMle
    (finrank_closure_eq (sup := sup) (M := M) hM).symm

/-- Any primitive sublattice of an orthogonal sum of two stable lattices has
determinant at least one. -/
lemma det_ge_one_of_primitive_le_sup {W₁ W₂ N : Submodule ℤ E}
    [DiscreteTopology W₁] [DiscreteTopology W₂] [DiscreteTopology ↥(W₁ ⊔ W₂)]
    (hop : OrthogonalPair W₁ W₂) (hSt₁ : Stable W₁) (hSt₂ : Stable W₂)
    (hN : N ≤ W₁ ⊔ W₂) (hpN : Primitive N (W₁ ⊔ W₂)) [DiscreteTopology N] :
    (1 : ℝ) ≤ ReverseMinkowski.determinant N := by
  classical
  have hprimW₁ : Primitive W₁ (W₁ ⊔ W₂) := primitive_left_of_orthogonal hop
  have hprimW₁N : Primitive W₁ (W₁ ⊔ N) := primitive_of_le hprimW₁
      (sup_le (le_sup_left : W₁ ≤ W₁ ⊔ W₂) hN) (le_sup_left : W₁ ≤ W₁ ⊔ N)
  have hQle : quotLattice (W₁ ⊔ N) (realSpan W₁) ≤ W₂ :=
    quot_orthogonal_sup_le_right (W₁ := W₁) (W₂ := W₂) (N := N) hop hN
  haveI : DiscreteTopology ↥(W₁ ⊔ N) :=
    Commons.Lattice.Discrete.discreteTopology_of_le (n := n) (ℒ := W₁ ⊔ W₂)
      (ℒ' := W₁ ⊔ N) (sup_le (le_sup_left : W₁ ≤ W₁ ⊔ W₂) hN)
  haveI : DiscreteTopology ↥(W₁ ⊓ N) :=
    Commons.Lattice.Discrete.discreteTopology_of_le (n := n) (ℒ := W₁)
      (ℒ' := W₁ ⊓ N) inf_le_left
  haveI : DiscreteTopology ↥(quotLattice (W₁ ⊔ N) (realSpan W₁)) :=
    Commons.Lattice.Discrete.discreteTopology_of_le (n := n) (ℒ := W₂)
      (ℒ' := quotLattice (W₁ ⊔ N) (realSpan W₁)) hQle
  let Q : Submodule ℤ E := quotLattice (W₁ ⊔ N) (realSpan W₁)
  have hq : ReverseMinkowski.determinant Q = ReverseMinkowski.determinant (W₁ ⊔ N) /
      ReverseMinkowski.determinant W₁ := by
    dsimp [Q]
    exact Submission.SubLattice.determinant_quot_generic (nA := n) (ℒ' := W₁)
      (ℒ := W₁ ⊔ N) (realSpan W₁) rfl hprimW₁N
  have hdetQge : (1 : ℝ) ≤ ReverseMinkowski.determinant Q := by
    dsimp [Q]
    exact hSt₂.2 (quotLattice (W₁ ⊔ N) (realSpan W₁)) hQle
  have hposW₁ : ReverseMinkowski.determinant W₁ ≠ 0 := ne_of_gt (det_pos (L := W₁))
  have hdetSupN : ReverseMinkowski.determinant (W₁ ⊔ N) = ReverseMinkowski.determinant W₁ *
      ReverseMinkowski.determinant Q := by
    calc
      ReverseMinkowski.determinant (W₁ ⊔ N) =
          (ReverseMinkowski.determinant (W₁ ⊔ N) / ReverseMinkowski.determinant W₁) *
            ReverseMinkowski.determinant W₁ := by
              field_simp [hposW₁]
      _ = ReverseMinkowski.determinant Q * ReverseMinkowski.determinant W₁ := by rw [← hq]
      _ = ReverseMinkowski.determinant W₁ * ReverseMinkowski.determinant Q := by ring
  have hdetSupNge1 : (1 : ℝ) ≤ ReverseMinkowski.determinant (W₁ ⊔ N) := by
    rw [hdetSupN]
    simpa [det_eq_one_of_stable hSt₁] using hdetQge
  have hdetInt : (1 : ℝ) ≤ ReverseMinkowski.determinant (W₁ ⊓ N) := by
    exact hSt₁.2 (W₁ ⊓ N) inf_le_left
  have huc : ReverseMinkowski.determinant (W₁ ⊔ N) * ReverseMinkowski.determinant (W₁ ⊓ N) ≤
      ReverseMinkowski.determinant N := by
    have h := Submission.Uncrossing.uncrossing_det (nA := n) (L := W₁ ⊔ W₂)
      (L₁ := W₁) (L₂ := N) (le_sup_left : W₁ ≤ W₁ ⊔ W₂) hN hprimW₁ hpN
    simpa [det_eq_one_of_stable hSt₁] using h
  have hA0 : 0 ≤ ReverseMinkowski.determinant (W₁ ⊔ N) :=
    le_of_lt (det_pos (L := W₁ ⊔ N))
  have hAB : ReverseMinkowski.determinant (W₁ ⊔ N) ≤
      ReverseMinkowski.determinant (W₁ ⊔ N) * ReverseMinkowski.determinant (W₁ ⊓ N) := by
    simpa using (mul_le_mul_of_nonneg_left hdetInt hA0)
  exact le_trans (le_trans hdetSupNge1 hAB) huc

/-- **The direct sum of two stable lattices is stable**: for pairwise-orthogonal stable
`W₁, W₂`, the ambient sum `W₁ ⊔ W₂` is stable. -/
theorem stable_sup {W₁ W₂ : Submodule ℤ E} [DiscreteTopology W₁] [DiscreteTopology W₂]
    [DiscreteTopology ↥(W₁ ⊔ W₂)] (hop : OrthogonalPair W₁ W₂)
    (hSt₁ : Stable W₁) (hSt₂ : Stable W₂) : Stable (W₁ ⊔ W₂) := by
  classical
  constructor
  · rw [det_sup_orthogonal (W₁ := W₁) (W₂ := W₂) hop]
    rw [det_eq_one_of_stable hSt₁, det_eq_one_of_stable hSt₂]
    norm_num
  · intro ℒ' hle hdt
    haveI : DiscreteTopology ↥ℒ' := hdt
    have hClo : primitiveClosure (W₁ ⊔ W₂) ℒ' ≤ W₁ ⊔ W₂ := by
      intro x hx
      exact (Submodule.mem_inf.mp hx).1
    have hPrimClo : Primitive (primitiveClosure (W₁ ⊔ W₂) ℒ') (W₁ ⊔ W₂) :=
      closure_primitive (sup := W₁ ⊔ W₂) (M := ℒ') hle
    haveI : DiscreteTopology ↥(primitiveClosure (W₁ ⊔ W₂) ℒ') :=
      Commons.Lattice.Discrete.discreteTopology_of_le (n := n) (ℒ := W₁ ⊔ W₂)
        (ℒ' := primitiveClosure (W₁ ⊔ W₂) ℒ') hClo
    have hdetM : (1 : ℝ) ≤ ReverseMinkowski.determinant (primitiveClosure (W₁ ⊔ W₂) ℒ') :=
      det_ge_one_of_primitive_le_sup (W₁ := W₁) (W₂ := W₂) (N := primitiveClosure (W₁ ⊔ W₂) ℒ')
        hop hSt₁ hSt₂ hClo hPrimClo
    have hdet_le : ReverseMinkowski.determinant (primitiveClosure (W₁ ⊔ W₂) ℒ') ≤
        ReverseMinkowski.determinant ℒ' :=
      det_closure_le_det (sup := W₁ ⊔ W₂) (M := ℒ') hle
    exact le_trans hdetM hdet_le


/-- The zero lattice is stable. -/
lemma stable_bot : Stable (⊥ : Submodule ℤ E) := by
  classical
  haveI : DiscreteTopology (⊥ : Submodule ℤ E) := discrete_bot
  constructor
  · exact det_bot
  · intro L hle hdt
    haveI : DiscreteTopology ↥L := hdt
    have hbot : L = ⊥ := by
      apply le_antisymm
      · exact hle
      · intro x hx
        have hx0 : x = 0 := (Submodule.mem_bot (R := ℤ) (M := E)).mp hx
        simpa [hx0]
    exact le_of_eq ((det_eq_of_eq (L₁ := L) (L₂ := ⊥) hbot).trans det_bot).symm

/-- A finite ambient sum of pairwise-orthogonal stable lattices is stable. -/
theorem stable_sup_fin (k : ℕ) (W : Fin k → Submodule ℤ E)
    (horth : ∀ i j : Fin k, i ≠ j → OrthogonalPair (W i) (W j))
    (hdisc : ∀ i : Fin k, DiscreteTopology (W i))
    (hSt : ∀ i : Fin k, Stable (W i))
    (S : Submodule ℤ E) (hS : S = ⨆ i : Fin k, W i) [DiscreteTopology S] :
    Stable S := by
  classical
  induction k generalizing S with
  | zero =>
      have hbot : S = ⊥ := by
        rw [hS]
        exact iSup_fin0_eq_bot
      constructor
      · exact (det_eq_of_eq (L₁ := S) (L₂ := ⊥) hbot).trans det_bot
      · intro L hle hdtL
        haveI : DiscreteTopology ↥L := hdtL
        have hLbot : L = ⊥ := by
          apply le_antisymm
          · exact le_trans hle (by rw [hbot])
          · intro x hx
            have hx0 : x = 0 := (Submodule.mem_bot (R := ℤ) (M := E)).mp hx
            simpa [hx0]
        exact le_of_eq ((det_eq_of_eq (L₁ := L) (L₂ := ⊥) hLbot).trans det_bot).symm
  | succ k ih =>
      let Tail : Submodule ℤ E := ⨆ j : Fin k, W (Fin.succ j)
      have horthT : ∀ i j : Fin k, i ≠ j → OrthogonalPair (W (Fin.succ i)) (W (Fin.succ j)) := by
        intro i j hij
        exact horth (Fin.succ i) (Fin.succ j) (by intro h; exact hij ((Fin.succ_injective k) h))
      have hdiscT : ∀ i : Fin k, DiscreteTopology (W (Fin.succ i)) := fun i => hdisc (Fin.succ i)
      have hStT : ∀ i : Fin k, Stable (W (Fin.succ i)) := fun i => hSt (Fin.succ i)
      haveI : DiscreteTopology Tail := by
        dsimp [Tail]
        exact discrete_supFam k (fun j : Fin k => W (Fin.succ j)) horthT hdiscT Tail (by rfl)
      have hStTail : Stable Tail := by
        dsimp [Tail]
        exact ih (fun j : Fin k => W (Fin.succ j)) horthT hdiscT hStT Tail (by rfl)
      have hSt0 : Stable (W 0) := hSt 0
      have hopT : OrthogonalPair (W 0) Tail := by
        dsimp [Tail]
        apply orthogonalPair_piece_iSup (W₀ := W 0) (Q := fun j : Fin k => W (Fin.succ j))
        intro j
        exact horth 0 (Fin.succ j) (by intro h; exact Fin.succ_ne_zero j h.symm)
      haveI : DiscreteTopology ↥(W 0 ⊔ Tail) := by
        change DiscreteTopology ↥(supMod (W 0) Tail)
        exact discrete_supMod hopT
      have hStSup : Stable (W 0 ⊔ Tail) := stable_sup (W₁ := W 0) (W₂ := Tail) hopT hSt0 hStTail
      have hsplit : S = W 0 ⊔ Tail := by
        rw [hS]
        rw [iSup_fin_succ_front (f := fun i : Fin (k + 1) => W i)]
      constructor
      · have hdetS : ReverseMinkowski.determinant S = ReverseMinkowski.determinant (W 0 ⊔ Tail) :=
          det_eq_of_eq (L₁ := S) (L₂ := W 0 ⊔ Tail) hsplit
        rw [hdetS]
        exact det_eq_one_of_stable hStSup
      · intro L hle hdtL
        haveI : DiscreteTopology ↥L := hdtL
        have hle' : L ≤ W 0 ⊔ Tail := by
          intro x hx
          have hxS : x ∈ S := hle hx
          simpa [hsplit] using hxS
        exact hStSup.2 L hle'


/-- The ℤ-rank of the quotient lattice is the difference of the ranks. -/
lemma finrank_quotLattice {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (S : Submodule ℝ E) (hS : S = realSpan ℒ') (hp : Primitive ℒ' ℒ) :
    Module.finrank ℤ ↥(quotLattice ℒ S) = Module.finrank ℤ ℒ - Module.finrank ℤ ℒ' := by
  classical
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  haveI : Module.Free ℤ ℒ' := instModuleFree_of_discrete_submodule ℒ'
  haveI : Module.Finite ℤ ℒ' := instModuleFinite_of_discrete_submodule ℒ'
  rcases (Submission.SubLattice.exists_adapted_quotBasis (ℒ' := ℒ') (ℒ := ℒ) S hS hp)
    with ⟨hd, e, β, he, hβ⟩
  haveI : Module.Free ℤ ↥(quotLattice ℒ S) := Module.Free.of_basis β
  haveI : Module.Finite ℤ ↥(quotLattice ℒ S) := Module.Finite.of_basis β
  simpa using (Module.finrank_eq_card_basis β)

/-- Rank additivity for a primitive pair: `rank ℒ = rank ℒ' + rank(ℒ/ℒ')`. -/
lemma finrank_eq_add_finrank_quotLattice {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    [DiscreteTopology ℒ'] (hle : ℒ' ≤ ℒ) (S : Submodule ℝ E) (hS : S = realSpan ℒ')
    (hp : Primitive ℒ' ℒ) :
    Module.finrank ℤ ℒ = Module.finrank ℤ ℒ' + Module.finrank ℤ ↥(quotLattice ℒ S) := by
  classical
  have hfin : Module.finrank ℤ ↥(quotLattice ℒ S) = Module.finrank ℤ ℒ - Module.finrank ℤ ℒ' :=
    finrank_quotLattice (ℒ' := ℒ') (ℒ := ℒ) S hS hp
  have hle' : Module.finrank ℤ ℒ' ≤ Module.finrank ℤ ℒ := by
    haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
    haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
    haveI : Module.Free ℤ ℒ' := instModuleFree_of_discrete_submodule ℒ'
    haveI : Module.Finite ℤ ℒ' := instModuleFinite_of_discrete_submodule ℒ'
    exact finrank_le_of_le (ℒ' := ℒ') (ℒ := ℒ) hle
  omega

/-- Orthogonality implies trivial intersection. -/
lemma inf_eq_bot_of_orthogonal {W₁ W₂ : Submodule ℤ E} (hop : OrthogonalPair W₁ W₂) :
    W₁ ⊓ W₂ = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hxW₁ : x ∈ W₁ := (Submodule.mem_inf.mp hx).1
    have hxW₂ : x ∈ W₂ := (Submodule.mem_inf.mp hx).2
    have hxx : ⟪x, x⟫_ℝ = 0 := hop x hxW₁ x hxW₂
    have hsq : ‖x‖ ^ 2 = 0 := by
      have := (real_inner_self_eq_norm_sq x)
      nlinarith
    have hx0 : x = 0 := (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))
    simpa [hx0]
  · exact bot_le

/-- Rank of a pairwise-orthogonal finite ambient sum is the sum of the ranks. -/
lemma finrank_sum_orthogonal_fin (k : ℕ) (W : Fin k → Submodule ℤ E)
    (horth : ∀ i j : Fin k, i ≠ j → OrthogonalPair (W i) (W j))
    (hdisc : ∀ i : Fin k, DiscreteTopology (W i))
    (S : Submodule ℤ E) (hS : S = ⨆ i : Fin k, W i) [DiscreteTopology S] :
    Module.finrank ℤ ↥S = ∑ i : Fin k, Module.finrank ℤ ↥(W i) := by
  classical
  induction k generalizing S with
  | zero =>
      have hbot : S = ⊥ := by rw [hS]; exact iSup_fin0_eq_bot
      rw [hbot]
      haveI : Module.Free ℤ ↥(⊥ : Submodule ℤ E) := instModuleFree_of_discrete_submodule (⊥ : Submodule ℤ E)
      haveI : Module.Finite ℤ ↥(⊥ : Submodule ℤ E) := instModuleFinite_of_discrete_submodule (⊥ : Submodule ℤ E)
      have hfin0 : Module.finrank ℤ ↥(⊥ : Submodule ℤ E) = 0 := Module.finrank_eq_zero_of_subsingleton ℤ (⊥ : Submodule ℤ E)
      simp [hfin0]
  | succ k ih =>
      let Tail : Submodule ℤ E := ⨆ j : Fin k, W (Fin.succ j)
      have horthT : ∀ i j : Fin k, i ≠ j → OrthogonalPair (W (Fin.succ i)) (W (Fin.succ j)) := by
        intro i j hij
        exact horth (Fin.succ i) (Fin.succ j) (by intro h; exact hij ((Fin.succ_injective k) h))
      have hdiscT : ∀ i : Fin k, DiscreteTopology (W (Fin.succ i)) := fun i => hdisc (Fin.succ i)
      haveI : DiscreteTopology Tail := by
        dsimp [Tail]
        exact discrete_supFam k (fun j : Fin k => W (Fin.succ j)) horthT hdiscT Tail (by rfl)
      have hfinTail : Module.finrank ℤ ↥Tail = ∑ j : Fin k, Module.finrank ℤ ↥(W (Fin.succ j)) := by
        dsimp [Tail]
        exact ih (fun j : Fin k => W (Fin.succ j)) horthT hdiscT Tail (by rfl)
      have hopT : OrthogonalPair (W 0) Tail := by
        dsimp [Tail]
        apply orthogonalPair_piece_iSup (W₀ := W 0) (Q := fun j : Fin k => W (Fin.succ j))
        intro j
        exact horth 0 (Fin.succ j) (by intro h; exact Fin.succ_ne_zero j h.symm)
      have hdisj : W 0 ⊓ Tail = ⊥ := inf_eq_bot_of_orthogonal hopT
      have hsplit : S = W 0 ⊔ Tail := by
        rw [hS]
        rw [iSup_fin_succ_front (f := fun i : Fin (k + 1) => W i)]
      haveI : DiscreteTopology ↥(W 0) := hdisc 0
      haveI : DiscreteTopology ↥(W 0 ⊔ Tail) := by
        change DiscreteTopology ↥(supMod (W 0) Tail)
        exact discrete_supMod hopT
      have hcomm := Commons.Lattice.Finrank.finrank_sup_add_finrank_inf_eq_of_discrete
        (n := n) (L₀ := W 0 ⊔ Tail) (L₁ := W 0) (L₂ := Tail) (le_sup_left : W 0 ≤ W 0 ⊔ Tail)
        (le_sup_right : Tail ≤ W 0 ⊔ Tail)
      have hfininf : Module.finrank ℤ ↥(W 0 ⊓ Tail) = 0 := by
        rw [hdisj]
        haveI : Module.Free ℤ ↥(⊥ : Submodule ℤ E) := instModuleFree_of_discrete_submodule (⊥ : Submodule ℤ E)
        haveI : Module.Finite ℤ ↥(⊥ : Submodule ℤ E) := instModuleFinite_of_discrete_submodule (⊥ : Submodule ℤ E)
        exact Module.finrank_eq_zero_of_subsingleton ℤ (⊥ : Submodule ℤ E)
      have hsplitFin : Module.finrank ℤ ↥(W 0 ⊔ Tail) = Module.finrank ℤ ↥(W 0) + Module.finrank ℤ ↥Tail := by
        omega
      calc
        Module.finrank ℤ ↥S = Module.finrank ℤ ↥(W 0 ⊔ Tail) := by rw [hsplit]
        _ = Module.finrank ℤ ↥(W 0) + Module.finrank ℤ ↥Tail := hsplitFin
        _ = Module.finrank ℤ ↥(W 0) + ∑ j : Fin k, Module.finrank ℤ ↥(W (Fin.succ j)) := by rw [hfinTail]
        _ = ∑ i : Fin (k + 1), Module.finrank ℤ ↥(W i) := by
          rw [Fin.sum_univ_succ]


/-- Along a primitive filtration chain from `⊥`, the ranks of the quotient pieces
sum to the rank of the top lattice. -/
lemma sum_finrank_quotPiece {k : ℕ} (L : ℕ → Submodule ℤ E)
    (h0 : L 0 = ⊥) (hchain : ∀ i, i < k → L i ≤ L (i + 1))
    (hprim : ∀ i, i < k → Primitive (L i) (L (i + 1)))
    (hLk : DiscreteTopology (L k)) :
    (∑ i ∈ Finset.range k, Module.finrank ℤ ↥(quotPiece L i)) = Module.finrank ℤ ↥(L k) := by
  classical
  induction k with
  | zero =>
      have hfin0 : Module.finrank ℤ ↥(L 0) = 0 := by
        rw [h0]
        haveI : Module.Free ℤ ↥(⊥ : Submodule ℤ E) := instModuleFree_of_discrete_submodule (⊥ : Submodule ℤ E)
        haveI : Module.Finite ℤ ↥(⊥ : Submodule ℤ E) := instModuleFinite_of_discrete_submodule (⊥ : Submodule ℤ E)
        exact Module.finrank_eq_zero_of_subsingleton ℤ (⊥ : Submodule ℤ E)
      simp [hfin0]
  | succ k ih =>
      haveI : DiscreteTopology (L (k + 1)) := hLk
      have hLk' : DiscreteTopology (L k) :=
        Submission.LatticeBasics.discreteTopology_of_le (ℒ := L (k + 1)) (ℒ' := L k)
          (hchain k (Nat.lt_succ_self k))
      have hIH := ih (fun i hi => hchain i (Nat.lt_trans hi (Nat.lt_succ_self k)))
        (fun i hi => hprim i (Nat.lt_trans hi (Nat.lt_succ_self k))) hLk'
      have hlast : Module.finrank ℤ ↥(quotPiece L k) =
          Module.finrank ℤ ↥(L (k + 1)) - Module.finrank ℤ ↥(L k) := by
        dsimp [quotPiece]
        exact finrank_quotLattice (ℒ' := L k) (ℒ := L (k + 1)) (realSpan (L k)) rfl
          (hprim k (Nat.lt_succ_self k))
      calc
        (∑ i ∈ Finset.range (k + 1), Module.finrank ℤ ↥(quotPiece L i))
            = (∑ i ∈ Finset.range k, Module.finrank ℤ ↥(quotPiece L i)) +
                Module.finrank ℤ ↥(quotPiece L k) := by rw [Finset.sum_range_succ]
        _ = Module.finrank ℤ ↥(L k) + Module.finrank ℤ ↥(quotPiece L k) := by rw [hIH]
        _ = Module.finrank ℤ ↥(L (k + 1)) := by
          rw [hlast]
          have hlerk : Module.finrank ℤ ↥(L k) ≤ Module.finrank ℤ ↥(L (k + 1)) := by
            haveI : Module.Free ℤ ↥(L k) := instModuleFree_of_discrete_submodule (L k)
            haveI : Module.Finite ℤ ↥(L k) := instModuleFinite_of_discrete_submodule (L k)
            haveI : Module.Free ℤ ↥(L (k + 1)) := instModuleFree_of_discrete_submodule (L (k + 1))
            haveI : Module.Finite ℤ ↥(L (k + 1)) := instModuleFinite_of_discrete_submodule (L (k + 1))
            exact finrank_le_of_le (ℒ' := L k) (ℒ := L (k + 1)) (hchain k (Nat.lt_succ_self k))
          omega




/-- The pullback of a quotient sublattice `M' ≤ quotLattice ℒ S`: all lattice points
whose projection lies in `M'`. -/
def interLattice (ℒ : Submodule ℤ E) (S : Submodule ℝ E) (M' : Submodule ℤ E) :
    Submodule ℤ E :=
  ℒ ⊓ (M'.comap (projMap S))

/-- Membership in the pullback. -/
lemma mem_interLattice {ℒ : Submodule ℤ E} {S : Submodule ℝ E} {M' : Submodule ℤ E} {x : E} :
    x ∈ interLattice ℒ S M' ↔ x ∈ ℒ ∧ (projMap S) x ∈ M' := by
  rfl

/-- The pullback lies in `ℒ`. -/
lemma interLattice_le (ℒ : Submodule ℤ E) (S : Submodule ℝ E) (M' : Submodule ℤ E) :
    interLattice ℒ S M' ≤ ℒ := inf_le_left

/-- The projection of the pullback of `M'` is exactly `M'`, for `M' ≤ quotLattice ℒ S`. -/
lemma map_interLattice_eq (ℒ : Submodule ℤ E) (S : Submodule ℝ E) {M' : Submodule ℤ E}
    (hM' : M' ≤ quotLattice ℒ S) :
    (interLattice ℒ S M').map (projMap S) = M' := by
  classical
  apply le_antisymm
  · intro x hx
    rcases (Submodule.mem_map.mp hx) with ⟨y, hy, hxy⟩
    have hyM : (projMap S) y ∈ M' := (mem_interLattice.mp hy).2
    simpa [hxy] using hyM
  · intro x hx
    have hxQ : x ∈ quotLattice ℒ S := hM' hx
    change x ∈ ℒ.map (projMap S) at hxQ
    rcases (Submodule.mem_map.mp hxQ) with ⟨y, hy, hxy⟩
    refine Submodule.mem_map.mpr ⟨y, ?_, hxy⟩
    exact (mem_interLattice).mpr ⟨hy, by simpa [hxy] using hx⟩

/-- If `ℒ'` is ambient-primitive in `ℒ`, the pullback of any `M' ≤ ℒ/ℒ'` contains `ℒ'`. -/
lemma le_interLattice_of_primitive {ℒ' ℒ : Submodule ℤ E} (S : Submodule ℝ E)
    (hS : S = realSpan ℒ') (hp : Primitive ℒ' ℒ) {M' : Submodule ℤ E} : ℒ' ≤ interLattice ℒ S M' := by
  intro x hx
  rw [mem_interLattice]
  constructor
  · exact Primitive.le hp hx
  · have hxS : x ∈ S := by simpa [hS] using mem_realSpan (ℒ := ℒ') hx
    have hπ0 : (projMap S) x = 0 := by
      simpa [projMap] using (starProjection_orthogonal_eq_zero_of_mem S hxS)
    simpa [hπ0]

/-- Determinant of the pullback: `det M = det ℒ' · det M'` for `M' ≤ ℒ/ℒ'`. -/
lemma det_intermediate_mul {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (S : Submodule ℝ E) (hS : S = realSpan ℒ') (hp : Primitive ℒ' ℒ)
    [DiscreteTopology ↥(quotLattice ℒ S)] {M' : Submodule ℤ E} [DiscreteTopology M']
    (hM' : M' ≤ quotLattice ℒ S) [DiscreteTopology ↥(interLattice ℒ S M')] :
    ReverseMinkowski.determinant (interLattice ℒ S M') =
      ReverseMinkowski.determinant ℒ' * ReverseMinkowski.determinant M' := by
  classical
  let M : Submodule ℤ E := interLattice ℒ S M'
  have hMle : M ≤ ℒ := by
    dsimp [M]
    exact interLattice_le ℒ S M'
  have hℒ'M : ℒ' ≤ M := le_interLattice_of_primitive (ℒ' := ℒ') (ℒ := ℒ) S hS hp (M' := M')
  have hpM : Primitive ℒ' M := primitive_of_le hp hMle hℒ'M
  haveI : DiscreteTopology ↥(quotLattice M S) := by
    -- quotLattice M S = M', and M' is discrete
    have hq : quotLattice M S = M' := by
      dsimp [M]
      change (interLattice ℒ S M').map (projMap S) = M'
      exact map_interLattice_eq ℒ S (M' := M') hM'
    rw [hq]
    infer_instance
  have hqM : ReverseMinkowski.determinant (quotLattice M S) =
      ReverseMinkowski.determinant M / ReverseMinkowski.determinant ℒ' := by
    dsimp [M]
    exact Submission.SubLattice.determinant_quot_generic (nA := n) (ℒ' := ℒ') (ℒ := M) S hS hpM
  have hqEq : quotLattice M S = M' := by
    dsimp [M]
    exact map_interLattice_eq ℒ S (M' := M') hM'
  have hqM' : ReverseMinkowski.determinant (quotLattice M S) = ReverseMinkowski.determinant M' :=
    det_eq_of_eq (L₁ := quotLattice M S) (L₂ := M') hqEq
  have hpos : ReverseMinkowski.determinant ℒ' ≠ 0 := ne_of_gt (det_pos (L := ℒ'))
  calc
    ReverseMinkowski.determinant M
        = (ReverseMinkowski.determinant M / ReverseMinkowski.determinant ℒ') *
            ReverseMinkowski.determinant ℒ' := by field_simp [hpos]
    _ = ReverseMinkowski.determinant M' * ReverseMinkowski.determinant ℒ' := by rw [← hqM, hqM']
    _ = ReverseMinkowski.determinant ℒ' * ReverseMinkowski.determinant M' := by ring






/-- A pair `ℒ' ⊆ ℒ` of (not necessarily distinct-rank) lattices is **extremal** when every
intermediate lattice `ℒ' ≤ M ≤ ℒ` lies on or above the segment between
`(rank ℒ', log det ℒ')` and `(rank ℒ, log det ℒ)` in the canonical plot. -/
def ExtremalPair (ℒ' ℒ : Submodule ℤ E) [DiscreteTopology ℒ'] [DiscreteTopology ℒ] : Prop :=
  ∀ M : Submodule ℤ E, [DiscreteTopology M] → ℒ' ≤ M → M ≤ ℒ →
    (Module.finrank ℤ ℒ - Module.finrank ℤ ℒ' : ℝ) *
        (Real.log (ReverseMinkowski.determinant M) - Real.log (ReverseMinkowski.determinant ℒ')) ≥
      (Module.finrank ℤ M - Module.finrank ℤ ℒ' : ℝ) *
        Real.log (ReverseMinkowski.determinant ℒ / ReverseMinkowski.determinant ℒ')

/-- Equal submodules have equal `ℤ`-ranks. -/
lemma finrank_eq_of_eq {p q : Submodule ℤ E} (h : p = q) :
    Module.finrank ℤ ↥p = Module.finrank ℤ ↥q :=
  LinearEquiv.finrank_eq (LinearEquiv.ofEq p q h)

/-- **Log-form extremal inequality for quotient sublattices.** -/
lemma extremal_quot_log_ineq {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ'] [DiscreteTopology ℒ]
    (S : Submodule ℝ E) (hS : S = realSpan ℒ') (hp : Primitive ℒ' ℒ)
    (hext : ExtremalPair ℒ' ℒ)
    [DiscreteTopology ↥(quotLattice ℒ S)]
    {N₀ : Submodule ℤ E} [DiscreteTopology N₀] (hN₀ : N₀ ≤ quotLattice ℒ S) :
    (Module.finrank ℤ ℒ - Module.finrank ℤ ℒ' : ℝ) *
        Real.log (ReverseMinkowski.determinant N₀) ≥
      (Module.finrank ℤ N₀ : ℝ) *
        Real.log (ReverseMinkowski.determinant (quotLattice ℒ S)) := by
  classical
  let M : Submodule ℤ E := interLattice ℒ S N₀
  have hMle : M ≤ ℒ := by
    dsimp [M]
    exact interLattice_le ℒ S N₀
  have hℒ'M : ℒ' ≤ M := by
    dsimp [M]
    exact le_interLattice_of_primitive (ℒ' := ℒ') (ℒ := ℒ) S hS hp (M' := N₀)
  haveI : DiscreteTopology ↥M :=
    Commons.Lattice.Discrete.discreteTopology_of_le (n := n) (ℒ := ℒ) (ℒ' := M) hMle
  have hExt := hext M hℒ'M hMle
  have hB0 : ReverseMinkowski.determinant ℒ' ≠ 0 := ne_of_gt (det_pos (L := ℒ'))
  have hC0 : ReverseMinkowski.determinant N₀ ≠ 0 := ne_of_gt (det_pos (L := N₀))
  have hdetM : ReverseMinkowski.determinant M = ReverseMinkowski.determinant ℒ' *
      ReverseMinkowski.determinant N₀ := by
    dsimp [M]
    exact det_intermediate_mul (ℒ' := ℒ') (ℒ := ℒ) S hS hp (M' := N₀) hN₀
  have hdetQ : ReverseMinkowski.determinant (quotLattice ℒ S) =
      ReverseMinkowski.determinant ℒ / ReverseMinkowski.determinant ℒ' := by
    exact Submission.SubLattice.determinant_quot_generic (nA := n) (ℒ' := ℒ') (ℒ := ℒ) S hS hp
  have hlogM : Real.log (ReverseMinkowski.determinant M) - Real.log (ReverseMinkowski.determinant ℒ') =
      Real.log (ReverseMinkowski.determinant N₀) := by
    calc
      Real.log (ReverseMinkowski.determinant M) - Real.log (ReverseMinkowski.determinant ℒ')
          = Real.log (ReverseMinkowski.determinant ℒ' * ReverseMinkowski.determinant N₀) -
              Real.log (ReverseMinkowski.determinant ℒ') := by rw [hdetM]
      _ = (Real.log (ReverseMinkowski.determinant ℒ') + Real.log (ReverseMinkowski.determinant N₀)) -
              Real.log (ReverseMinkowski.determinant ℒ') := by
            rw [Real.log_mul hB0 hC0]
      _ = Real.log (ReverseMinkowski.determinant N₀) := by ring
  have hqM : quotLattice M S = N₀ := by
    dsimp [M]
    exact map_interLattice_eq ℒ S (M' := N₀) hN₀
  have hpM : Primitive ℒ' M := primitive_of_le hp hMle hℒ'M
  have hfinM := finrank_eq_add_finrank_quotLattice (ℒ' := ℒ') (ℒ := M) hℒ'M S hS hpM
  have hfr : Module.finrank ℤ ↥(quotLattice M S) = Module.finrank ℤ ↥N₀ := finrank_eq_of_eq hqM
  have hrankM : Module.finrank ℤ M = Module.finrank ℤ ℒ' + Module.finrank ℤ N₀ := by
    rw [hfr] at hfinM
    exact hfinM
  have hRM : (Module.finrank ℤ M - Module.finrank ℤ ℒ' : ℝ) = (Module.finrank ℤ N₀ : ℝ) := by
    rw [hrankM]
    simp
  have hExt' : (Module.finrank ℤ ℒ - Module.finrank ℤ ℒ' : ℝ) *
        Real.log (ReverseMinkowski.determinant N₀) ≥
      (Module.finrank ℤ N₀ : ℝ) *
        Real.log (ReverseMinkowski.determinant (quotLattice ℒ S)) := by
    rw [hlogM, hRM, ← hdetQ] at hExt
    exact hExt
  exact hExt'

/-- Scaling by a real is monotone on submodules. -/
lemma smulLattice_mono (α : ℝ) {N₁ N₂ : Submodule ℤ E} (h : N₁ ≤ N₂) :
    smulLattice α N₁ ≤ smulLattice α N₂ := by
  intro x hx
  rcases (mem_smulLattice.mp hx) with ⟨y, hy, hxy⟩
  exact (mem_smulLattice).mpr ⟨y, h hy, hxy⟩

/-- `α • (β • N) = (α·β) • N`. -/
lemma smulLattice_mul (α β : ℝ) (N : Submodule ℤ E) :
    smulLattice α (smulLattice β N) = smulLattice (α * β) N := by
  classical
  apply le_antisymm
  · intro x hx
    rcases (mem_smulLattice.mp hx) with ⟨y, hy, hxy⟩
    rcases (mem_smulLattice.mp hy) with ⟨z, hz, hyz⟩
    refine (mem_smulLattice).mpr ⟨z, hz, ?_⟩
    calc
      (α * β) • (z : E) = α • (β • (z : E)) := by rw [mul_smul]
      _ = x := by rw [hyz, hxy]
  · intro x hx
    rcases (mem_smulLattice.mp hx) with ⟨z, hz, hxz⟩
    refine (mem_smulLattice).mpr ⟨β • (z : E), ?_, ?_⟩
    · exact (mem_smulLattice).mpr ⟨z, hz, rfl⟩
    · rw [mul_smul] at hxz
      exact hxz

/-- Scaling by `1` is the identity. -/
lemma smulLattice_one (N : Submodule ℤ E) : smulLattice (1 : ℝ) N = N := by
  classical
  apply le_antisymm
  · intro x hx
    rcases (mem_smulLattice.mp hx) with ⟨y, hy, hxy⟩
    have hx1 : (1 : ℝ) • (y : E) = y := one_smul ℝ (y : E)
    rwa [← hxy, hx1]
  · intro x hx
    refine (mem_smulLattice).mpr ⟨x, hx, ?_⟩
    rw [one_smul]

/-- For `α ≠ 0`, multiplication by `α⁻¹` undoes multiplication by `α`. -/
lemma smulLattice_inv_smul (α : ℝ) (hα : α ≠ 0) (N : Submodule ℤ E) :
    smulLattice α⁻¹ (smulLattice α N) = N := by
  classical
  have hmul : smulLattice α⁻¹ (smulLattice α N) = smulLattice (α⁻¹ * α) N := smulLattice_mul α⁻¹ α N
  rw [hmul]
  have h : α⁻¹ * α = 1 := inv_mul_cancel₀ hα
  rw [h]
  exact smulLattice_one N

/-- For `α ≠ 0`, scaling is injective on the lattice of submodules. -/
lemma smulLattice_le_of_le_smul (α : ℝ) (hα : α ≠ 0) {N₁ N₂ : Submodule ℤ E}
    (h : smulLattice α N₁ ≤ smulLattice α N₂) : N₁ ≤ N₂ := by
  have h' : smulLattice α⁻¹ (smulLattice α N₁) ≤ smulLattice α⁻¹ (smulLattice α N₂) :=
    smulLattice_mono α⁻¹ h
  simpa [smulLattice_inv_smul α hα] using h'

/-- **Subdeterminant bound on the scaled quotient.**  For an extremal pair and any
`N₀ ≤ ℒ/ℒ'`, with `α := exp(-log det Q / rank Q)` (`Q := ℒ/ℒ'`), `det(α • N₀) ≥ 1`. -/
lemma scaled_quot_subdet_ge_one {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ'] [DiscreteTopology ℒ]
    (S : Submodule ℝ E) (hS : S = realSpan ℒ') (hp : Primitive ℒ' ℒ)
    [DiscreteTopology ↥(quotLattice ℒ S)]
    (hr : 0 < Module.finrank ℤ ℒ - Module.finrank ℤ ℒ')
    (hext : ExtremalPair ℒ' ℒ)
    {N₀ : Submodule ℤ E} [DiscreteTopology N₀] (hN₀ : N₀ ≤ quotLattice ℒ S) :
    (1 : ℝ) ≤ ReverseMinkowski.determinant (smulLattice
      (rexp (-(Real.log (ReverseMinkowski.determinant (quotLattice ℒ S))) /
        (Module.finrank ℤ ℒ - Module.finrank ℤ ℒ' : ℝ))) N₀) := by
  classical
  let Q : Submodule ℤ E := quotLattice ℒ S
  haveI : DiscreteTopology Q := by
    dsimp [Q]
    infer_instance
  let r : ℝ := (Module.finrank ℤ ℒ - Module.finrank ℤ ℒ' : ℝ)
  let α : ℝ := rexp (-(Real.log (ReverseMinkowski.determinant Q)) / r)
  have hr0 : 0 < r := by
    dsimp [r]
    have hlt : Module.finrank ℤ ℒ' < Module.finrank ℤ ℒ := by
      exact Nat.lt_of_sub_pos hr
    have hlt' : (Module.finrank ℤ ℒ' : ℝ) < (Module.finrank ℤ ℒ : ℝ) := by exact_mod_cast hlt
    linarith
  have hrnz : r ≠ 0 := ne_of_gt hr0
  have hdetQpos : 0 < ReverseMinkowski.determinant Q := det_pos (L := Q)
  have hdetQnz : ReverseMinkowski.determinant Q ≠ 0 := ne_of_gt hdetQpos
  have hdetNpos : 0 < ReverseMinkowski.determinant N₀ := det_pos (L := N₀)
  have hdetNnz : ReverseMinkowski.determinant N₀ ≠ 0 := ne_of_gt hdetNpos
  have hαpos : 0 < α := by
    dsimp [α]
    exact Real.exp_pos _
  have hαnz : α ≠ 0 := ne_of_gt hαpos
  have hA := extremal_quot_log_ineq (ℒ' := ℒ') (ℒ := ℒ) S hS hp hext (N₀ := N₀) hN₀
  have hA' : (Module.finrank ℤ N₀ : ℝ) * Real.log (ReverseMinkowski.determinant Q) ≤
      r * Real.log (ReverseMinkowski.determinant N₀) := by
    dsimp [r]
    simpa [ge_iff_le] using hA
  have hdet_scaled : ReverseMinkowski.determinant (smulLattice α N₀) =
      α ^ (Module.finrank ℤ N₀) * ReverseMinkowski.determinant N₀ := by
    exact det_smulLattice_pos α hαpos N₀
  have hlog_scaled : Real.log (ReverseMinkowski.determinant (smulLattice α N₀)) =
      (Module.finrank ℤ N₀ : ℝ) * Real.log α + Real.log (ReverseMinkowski.determinant N₀) := by
    rw [hdet_scaled]
    rw [Real.log_mul (pow_ne_zero _ hαnz) hdetNnz]
    rw [Real.log_pow α (Module.finrank ℤ N₀)]
  have hlogα : Real.log α = -(Real.log (ReverseMinkowski.determinant Q)) / r := by
    dsimp [α]
    rw [Real.log_exp]
  have hmain : (Module.finrank ℤ N₀ : ℝ) * Real.log (ReverseMinkowski.determinant Q) / r ≤
      Real.log (ReverseMinkowski.determinant N₀) := by
    exact (div_le_iff₀ hr0).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hA')
  have hnonneg : 0 ≤ Real.log (ReverseMinkowski.determinant (smulLattice α N₀)) := by
    rw [hlog_scaled, hlogα]
    -- goal: 0 ≤ (k : ℝ) * (-(L) / r) + C ; ring-equal to C - (k * L) / r
    have heq : (Module.finrank ℤ N₀ : ℝ) * (-(Real.log (ReverseMinkowski.determinant Q)) / r) +
          Real.log (ReverseMinkowski.determinant N₀) =
        Real.log (ReverseMinkowski.determinant N₀) -
          ((Module.finrank ℤ N₀ : ℝ) * Real.log (ReverseMinkowski.determinant Q)) / r := by
      rw [neg_div]
      ring
    rw [heq]
    exact sub_nonneg.mpr hmain
  have hdetpos2 : 0 < ReverseMinkowski.determinant (smulLattice α N₀) := det_pos (L := smulLattice α N₀)
  have hone : (1 : ℝ) ≤ ReverseMinkowski.determinant (smulLattice α N₀) := by
    exact (Real.log_le_log_iff (by norm_num) hdetpos2).mp (by simpa using hnonneg)
  -- the goal is this claim with α := rexp(...) inlined
  change (1 : ℝ) ≤ ReverseMinkowski.determinant (smulLattice α N₀)
  exact hone
/-- The normalized scale of a quotient piece: `exp(-log det Q / rank Q)`. -/
def quotScale (ℒ' ℒ : Submodule ℤ E) [DiscreteTopology ℒ'] [DiscreteTopology ℒ]
    [DiscreteTopology ↥(quotLattice ℒ (realSpan ℒ'))] : ℝ :=
  rexp (-(Real.log (ReverseMinkowski.determinant (quotLattice ℒ (realSpan ℒ')))) /
    (Module.finrank ℤ ℒ - Module.finrank ℤ ℒ' : ℝ))

/-- **Prop 2.7(ii)**: the scaled quotient of an extremal pair is stable.  If `ℒ' ⊆ ℒ` is an
extremal pair of lattices with `rank ℒ > rank ℒ'`, then with `Q := ℒ/ℒ'` and
`α := det Q^(-1/rank Q) = exp(-log det Q / rank Q)`, the lattice `α • Q` is stable. -/
theorem stable_quot_of_extremal {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ'] [DiscreteTopology ℒ]
    (hp : Primitive ℒ' ℒ)
    [DiscreteTopology ↥(quotLattice ℒ (realSpan ℒ'))]
    (hr : 0 < Module.finrank ℤ ℒ - Module.finrank ℤ ℒ')
    (hext : ExtremalPair ℒ' ℒ) :
    let Q : Submodule ℤ E := quotLattice ℒ (realSpan ℒ')
    Stable (smulLattice (quotScale ℒ' ℒ) Q) := by
  classical
  let Q : Submodule ℤ E := quotLattice ℒ (realSpan ℒ')
  haveI : DiscreteTopology Q := by
    dsimp [Q]
    infer_instance
  let r : ℝ := (Module.finrank ℤ ℒ - Module.finrank ℤ ℒ' : ℝ)
  let α : ℝ := quotScale ℒ' ℒ
  change Stable (smulLattice α Q)
  have hαval : α = rexp (-(Real.log (ReverseMinkowski.determinant (quotLattice ℒ (realSpan ℒ')))) /
      (Module.finrank ℤ ℒ - Module.finrank ℤ ℒ' : ℝ)) := rfl
  have hαpos : 0 < α := by
    dsimp [α]
    exact Real.exp_pos _
  have hαnz : α ≠ 0 := ne_of_gt hαpos
  have hr0 : 0 < r := by
    dsimp [r]
    have hlt : Module.finrank ℤ ℒ' < Module.finrank ℤ ℒ := by
      exact Nat.lt_of_sub_pos hr
    have hlt' : (Module.finrank ℤ ℒ' : ℝ) < (Module.finrank ℤ ℒ : ℝ) := by exact_mod_cast hlt
    linarith
  have hrnz : r ≠ 0 := ne_of_gt hr0
  constructor
  · -- det(αQ) = 1
    have hdetQ : ReverseMinkowski.determinant (quotLattice ℒ (realSpan ℒ')) ≠ 0 :=
      ne_of_gt (det_pos (L := quotLattice ℒ (realSpan ℒ')))
    have hrankQ : Module.finrank ℤ ↥Q = Module.finrank ℤ ℒ - Module.finrank ℤ ℒ' := by
      dsimp [Q]
      exact finrank_quotLattice (ℒ' := ℒ') (ℒ := ℒ) (realSpan ℒ') rfl hp
    have hdet_scaled : ReverseMinkowski.determinant (smulLattice α Q) =
        α ^ (Module.finrank ℤ ↥Q) * ReverseMinkowski.determinant Q := by
      exact det_smulLattice_pos α hαpos Q
    have hlogα : Real.log α = -(Real.log (ReverseMinkowski.determinant Q)) / r := by
      dsimp [α, Q, quotScale]
      rw [Real.log_exp]
    have hlog : Real.log (ReverseMinkowski.determinant (smulLattice α Q)) = 0 := by
      rw [hdet_scaled]
      rw [Real.log_mul (pow_ne_zero _ hαnz) (det_pos (L := Q)).ne']
      rw [Real.log_pow α (Module.finrank ℤ ↥Q)]
      rw [hlogα]
      have hle' : Module.finrank ℤ ℒ' ≤ Module.finrank ℤ ℒ := Nat.le_of_lt (Nat.lt_of_sub_pos hr)
      have hf : (Module.finrank ℤ ↥Q : ℝ) = r := by
        rw [hrankQ]
        dsimp [r]
        rw [Nat.cast_sub hle']
      rw [hf]
      field_simp [hrnz]
      ring
    have hposd : 0 < ReverseMinkowski.determinant (smulLattice α Q) := det_pos (L := smulLattice α Q)
    calc
      ReverseMinkowski.determinant (smulLattice α Q) =
          rexp (Real.log (ReverseMinkowski.determinant (smulLattice α Q))) := (Real.exp_log hposd).symm
      _ = 1 := by
        rw [hlog]
        norm_num
  · -- all sublattices have det ≥ 1
    intro M hMle hdtM
    haveI : DiscreteTopology ↥M := hdtM
    have hN₀le : smulLattice α⁻¹ M ≤ Q := by
      calc
        smulLattice α⁻¹ M ≤ smulLattice α⁻¹ (smulLattice α Q) := smulLattice_mono α⁻¹ hMle
        _ = Q := smulLattice_inv_smul α hαnz Q
    haveI : DiscreteTopology ↥(smulLattice α⁻¹ M) :=
      Commons.Lattice.Discrete.discreteTopology_of_le (n := n) (ℒ := Q)
        (ℒ' := smulLattice α⁻¹ M) hN₀le
    have hb : (1 : ℝ) ≤ ReverseMinkowski.determinant (smulLattice α (smulLattice α⁻¹ M)) := by
      -- unfold α to the inline expression expected by the subdet lemma
      dsimp [α, Q]
      exact scaled_quot_subdet_ge_one (ℒ' := ℒ') (ℒ := ℒ) (realSpan ℒ') rfl hp hr hext
        (N₀ := smulLattice (quotScale ℒ' ℒ)⁻¹ M) hN₀le
    have hM : M = smulLattice α (smulLattice α⁻¹ M) := by
      calc
        M = smulLattice 1 M := (smulLattice_one M).symm
        _ = smulLattice (α * α⁻¹) M := by rw [mul_inv_cancel₀ hαnz]
        _ = smulLattice α (smulLattice α⁻¹ M) := (smulLattice_mul α α⁻¹ M).symm
    have hdetE : ReverseMinkowski.determinant M = ReverseMinkowski.determinant (smulLattice α (smulLattice α⁻¹ M)) :=
      det_eq_of_eq (L₁ := M) (L₂ := smulLattice α (smulLattice α⁻¹ M)) hM
    rw [hdetE]
    exact hb


/-- For a discrete lattice of rank at least `r` there is a rank-`r` sublattice. -/
lemma exists_rank_sublattice {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    {r : ℕ} (hr : r ≤ Module.finrank ℤ ℒ) :
    ∃ M : Submodule ℤ E, M ≤ ℒ ∧ Module.finrank ℤ M = r := by
  classical
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  let m : ℕ := Module.finrank ℤ ℒ
  let e : Module.Basis (Fin m) ℤ ℒ := Module.finBasis ℤ ℒ
  let w : Fin r → E := fun i => ((e (Fin.castLE hr i) : ℒ) : E)
  let M : Submodule ℤ E := Submodule.span ℤ (Set.range w)
  have hmem : ∀ i : Fin r, w i ∈ M := by
    intro i
    dsimp [M]
    exact Submodule.subset_span (by exact Set.mem_range.mpr ⟨i, rfl⟩)
  have hMle : M ≤ ℒ := by
    intro x hx
    refine Submodule.span_le.mpr ?_ hx
    intro y hy
    rcases (Set.mem_range.mp hy) with ⟨i, rfl⟩
    exact (e (Fin.castLE hr i)).2
  have hind : LinearIndependent ℤ w := by
    dsimp [w]
    have hlin : LinearIndependent ℤ (fun j : Fin m => ((e j : ℒ) : E)) := by
      exact (e.linearIndependent).map' (ℒ.subtype) (by simp)
    exact hlin.comp (Fin.castLE hr) (by
      intro a b hab
      exact Fin.castLE_injective hr hab)
  rcases (basis_of_ambient (M := M) (w := w) (by rfl) hmem hind) with ⟨β, hβval⟩
  have hfin : Module.finrank ℤ ↥M = r := by
    simpa using (Module.finrank_eq_card_basis β)
  refine ⟨M, hMle, hfin⟩

/-- A rank-`r` sublattice with determinant ≤ `C` has `r` spanning lattice vectors with
Gram determinant ≤ `C²`. -/
lemma in_cand_of_det_le {ℒ M : Submodule ℤ E} [DiscreteTopology ℒ] [DiscreteTopology M]
    (hMle : M ≤ ℒ) {r : ℕ} (hr : Module.finrank ℤ M = r) (C : ℝ) (hC : 0 ≤ C)
    (hdet : ReverseMinkowski.determinant M ≤ C) :
    (∃ w : Fin r → E, (∀ i : Fin r, w i ∈ M) ∧
      (∀ ⦃x⦄, x ∈ M → x ∈ Submodule.span ℤ (Set.range w)) ∧
      (Matrix.gram ℝ w).det ≤ C ^ 2) := by
  classical
  haveI : Module.Free ℤ M := instModuleFree_of_discrete_submodule M
  haveI : Module.Finite ℤ M := instModuleFinite_of_discrete_submodule M
  let β : Module.Basis (Fin r) ℤ M := (Module.finBasis ℤ M).reindex (finCongr hr)
  let w : Fin r → E := fun i => ((β i : M) : E)
  refine ⟨w, ?_, ?_, ?_⟩
  · intro i
    dsimp [w]
    exact (β i).2
  · intro x hx
    dsimp [w]
    let e : M := ⟨x, hx⟩
    refine (Submodule.mem_span_range_iff_exists_fun (R := ℤ)
      (v := fun i : Fin r => ((β i : M) : E)) (x := x)).mpr ⟨fun i => β.repr e i, ?_⟩
    have h := ambient_basis_expand (ℒ := M) (b := β) e
    calc
      (∑ i : Fin r, (β.repr e i : ℤ) • ((β i : M) : E)) = (e : E) := h.symm
      _ = x := rfl
  · have hdetM : ReverseMinkowski.determinant M = √((Matrix.gram ℝ w).det) := by
      change ReverseMinkowski.determinant M =
        √((Matrix.gram ℝ (fun i : Fin r => ((β i : M) : E))).det)
      exact det_eq_sqrt_gram_any_basis (L := M) β
    have hnonneg : 0 ≤ (Matrix.gram ℝ w).det := (Matrix.posSemidef_gram ℝ w).det_nonneg
    have hroot : √((Matrix.gram ℝ w).det) ≤ C := by
      simpa [hdetM] using hdet
    have hsq : (Matrix.gram ℝ w).det ≤ C ^ 2 := by
      calc
        (Matrix.gram ℝ w).det = (√((Matrix.gram ℝ w).det)) ^ 2 := (Real.sq_sqrt hnonneg).symm
        _ ≤ C ^ 2 := by
          exact sq_le_sq.mpr (by
            rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hC]
            exact hroot)
    exact hsq

/-- **Determinant-minimizer existence**: for a full-rank lattice `ℒ` and each `r ≤ finrank ℤ ℒ`,
there is a rank-`r` sublattice minimizing the determinant. -/
theorem exists_det_minimizer_rank {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {r : ℕ} (hr : r ≤ Module.finrank ℤ ℒ) :
    ∃ (M : Submodule ℤ E) (hMle : M ≤ ℒ) (hdM : DiscreteTopology M),
      Module.finrank ℤ M = r ∧
      ∀ (M' : Submodule ℤ E), M' ≤ ℒ → Module.finrank ℤ M' = r →
        ∀ hdM' : DiscreteTopology M',
          @ReverseMinkowski.determinant n M hdM ≤ @ReverseMinkowski.determinant n M' hdM' := by
  classical
  rcases (exists_rank_sublattice (ℒ := ℒ) hr) with ⟨M₀, hM₀le, hfinM₀⟩
  haveI : DiscreteTopology ↥M₀ :=
    Commons.Lattice.Discrete.discreteTopology_of_le (n := n) (ℒ := ℒ) (ℒ' := M₀) hM₀le
  let C : ℝ := ReverseMinkowski.determinant M₀
  have hC : 0 ≤ C := le_of_lt (det_pos (L := M₀))
  -- candidate set
  let cand : Set (Submodule ℤ E) := {M | M ≤ ℒ ∧ Module.finrank ℤ M = r ∧
    (∃ w : Fin r → E, (∀ i : Fin r, w i ∈ M) ∧
      (∀ ⦃x⦄, x ∈ M → x ∈ Submodule.span ℤ (Set.range w)) ∧
      (Matrix.gram ℝ w).det ≤ C ^ 2)}
  have hFin : cand.Finite := by
    dsimp [cand, C]
    exact Commons.Lattice.Minimizer.finite_sublattices_det_le (n := n) (L := ℒ) (C := C) (r := r)
  have hM₀cand : M₀ ∈ cand := by
    dsimp [cand, C]
    refine ⟨hM₀le, hfinM₀, ?_⟩
    exact in_cand_of_det_le (ℒ := ℒ) (M := M₀) hM₀le hfinM₀ C hC (by rfl)
  have hNe : cand.Nonempty := ⟨M₀, hM₀cand⟩
  -- det-value function on submodules (0 outside the candidates)
  let detVal : Submodule ℤ E → ℝ := fun M => if hMle : M ≤ ℒ then
    @ReverseMinkowski.determinant n M (Commons.Lattice.Discrete.discreteTopology_of_le (n := n)
      (ℒ := ℒ) (ℒ' := M) hMle) else 0
  -- finite argmin over the candidates
  have hne_fin : (hFin.toFinset).Nonempty := by
    refine ⟨M₀, ?_⟩
    rw [Set.Finite.mem_toFinset hFin]
    exact hM₀cand
  rcases (Finset.exists_min_image (s := hFin.toFinset) (f := detVal) hne_fin) with ⟨x, hx, hxmin⟩
  have hxcand : x ∈ cand := by
    rw [Set.Finite.mem_toFinset hFin] at hx
    exact hx
  -- minimality over Cand
  have hxmin_cand : ∀ M : Submodule ℤ E, M ∈ cand → detVal x ≤ detVal M := by
    intro M hM
    have hMfin : M ∈ hFin.toFinset := by
      rw [Set.Finite.mem_toFinset hFin]
      exact hM
    exact hxmin M hMfin
  have hxle : x ≤ ℒ := (hxcand.1)
  have hdetx : detVal x = @ReverseMinkowski.determinant n x (Commons.Lattice.Discrete.discreteTopology_of_le (n := n) (ℒ := ℒ) (ℒ' := x) hxle) := by
    dsimp [detVal]
    simp [hxle]
  -- x's own topology (a fixed witness)
  let hdx : DiscreteTopology x := by
    exact Commons.Lattice.Discrete.discreteTopology_of_le (n := n) (ℒ := ℒ) (ℒ' := x) hxle
  -- global minimality
  have hxmin_global : ∀ (M' : Submodule ℤ E), M' ≤ ℒ → Module.finrank ℤ M' = r →
      ∀ hdM' : DiscreteTopology M', @ReverseMinkowski.determinant n x hdx ≤ @ReverseMinkowski.determinant n M' hdM' := by
    intro M' hM'le hfinM' hdM'
    haveI : DiscreteTopology ↥M' := hdM'
    have hdetM' : @ReverseMinkowski.determinant n M' hdM' = ReverseMinkowski.determinant M' := rfl
    by_cases hsmall : ReverseMinkowski.determinant M' ≤ C
    · -- M' is a candidate
      have hM'cand : M' ∈ cand := by
        dsimp [cand, C]
        refine ⟨hM'le, hfinM', ?_⟩
        exact in_cand_of_det_le (ℒ := ℒ) (M := M') hM'le hfinM' C hC hsmall
      have hineq := hxmin_cand M' hM'cand
      -- detVal x ≤ detVal M'; both resolve to real dets
      have hdetValx : detVal x = @ReverseMinkowski.determinant n x hdx := by
        rw [hdetx]
      have hdetValM : detVal M' = @ReverseMinkowski.determinant n M' hdM' := by
        dsimp [detVal]
        simp [hM'le, hdM']
      simpa [hdetValx, hdetValM] using hineq
    · -- large determinant: beaten by M₀ itself
      have hx_le_M₀ : detVal x ≤ detVal M₀ := hxmin_cand M₀ hM₀cand
      have hdetValx : detVal x = @ReverseMinkowski.determinant n x hdx := by
        rw [hdetx]
      have hdetValM₀ : detVal M₀ = @ReverseMinkowski.determinant n M₀ (by
        exact Commons.Lattice.Discrete.discreteTopology_of_le (n := n) (ℒ := ℒ) (ℒ' := M₀) hM₀le) := by
        dsimp [detVal]
        simp [hM₀le]
      have hxM₀ : @ReverseMinkowski.determinant n x hdx ≤ ReverseMinkowski.determinant M₀ := by
        simpa [hdetValx, hdetValM₀, C] using hx_le_M₀
      have hbig : C ≤ @ReverseMinkowski.determinant n M' hdM' := by
        dsimp [C]
        exact le_of_lt (lt_of_not_ge hsmall)
      exact le_trans hxM₀ hbig
  refine ⟨x, hxle, hdx, (hxcand.2).1, hxmin_global⟩


/-- A chosen determinant-minimizer among the rank-`r` sublattices of a full-rank lattice `ℒ`
(which exists by `exists_det_minimizer_rank`). -/
noncomputable def detMinimizer {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (r : ℕ) (hr : r ≤ Module.finrank ℤ ℒ) : Submodule ℤ E :=
  Classical.choose (exists_det_minimizer_rank (ℒ := ℒ) hℒ hr)

/-- The chosen minimizer lies in `ℒ`. -/
lemma detMinimizer_le {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {r : ℕ} (hr : r ≤ Module.finrank ℤ ℒ) :
    detMinimizer hℒ r hr ≤ ℒ :=
  (Classical.choose_spec (exists_det_minimizer_rank (ℒ := ℒ) hℒ hr)).1

/-- The discreteness of the chosen minimizer (the witness from existence). -/
lemma detMinimizer_discrete {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {r : ℕ} (hr : r ≤ Module.finrank ℤ ℒ) :
    DiscreteTopology ↥(detMinimizer hℒ r hr) :=
  (Classical.choose_spec (exists_det_minimizer_rank (ℒ := ℒ) hℒ hr)).2.1

/-- The chosen minimizer has rank `r`. -/
lemma detMinimizer_rank {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {r : ℕ} (hr : r ≤ Module.finrank ℤ ℒ) :
    Module.finrank ℤ ↥(detMinimizer hℒ r hr) = r :=
  (Classical.choose_spec (exists_det_minimizer_rank (ℒ := ℒ) hℒ hr)).2.2.1

/-- Minimality: the chosen minimizer has the smallest determinant among rank-`r` sublattices
(expressed with the canonical discreteness witness `detMinimizer_discrete`). -/
lemma detMinimizer_le_det {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {r : ℕ} (hr : r ≤ Module.finrank ℤ ℒ) (M' : Submodule ℤ E) [DiscreteTopology M']
    (hM'le : M' ≤ ℒ) (hfin : Module.finrank ℤ M' = r) :
    @ReverseMinkowski.determinant n (detMinimizer hℒ r hr) (detMinimizer_discrete hℒ hr) ≤
      ReverseMinkowski.determinant M' := by
  classical
  let spec := Classical.choose_spec (exists_det_minimizer_rank (ℒ := ℒ) hℒ hr)
  have hdt0 : DiscreteTopology ↥(detMinimizer hℒ r hr) := spec.2.1
  have hfin0 : Module.finrank ℤ ↥(detMinimizer hℒ r hr) = r := spec.2.2.1
  have hmain := spec.2.2.2
  have h := hmain M' hM'le hfin (inferInstance : DiscreteTopology M')
  have hinstEq : detMinimizer_discrete hℒ hr = hdt0 := by
    exact Subsingleton.elim _ _
  simpa [detMinimizer, hinstEq] using h


/-- Log-determinant of the chosen rank-`r` determinant-minimizer of the full-rank lattice `ℒ`. -/
noncomputable def minLogDet {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (r : ℕ) (hr : r ≤ Module.finrank ℤ ℒ) : ℝ :=
  Real.log (@ReverseMinkowski.determinant n (detMinimizer hℒ r hr) (detMinimizer_discrete hℒ (r := r) hr))

/-- The log-determinant values of the per-rank minimizers, indexed by `Fin (n+1)`. -/
noncomputable def minLogSeq {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ) :
    Fin (n + 1) → ℝ :=
  fun i => minLogDet hℒ i.val (by have hfin : Module.finrank ℤ ℒ = n := fullrank_finrank ℒ hℒ; omega)

/-- Every sublattice of `ℒ` lies on or above the point of the chosen minimizer of its own rank:
`log det M ≥ minLogDet (rank M)`. -/
lemma minLogDet_le_log_det {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (M : Submodule ℤ E) [DiscreteTopology M] (hMle : M ≤ ℒ) :
    minLogDet hℒ (Module.finrank ℤ M) (finrank_le_of_le (ℒ' := M) (ℒ := ℒ) hMle) ≤
      Real.log (ReverseMinkowski.determinant M) := by
  classical
  let r : ℕ := Module.finrank ℤ M
  let hr : r ≤ Module.finrank ℤ ℒ := finrank_le_of_le (ℒ' := M) (ℒ := ℒ) hMle
  have hmin := detMinimizer_le_det (ℒ := ℒ) hℒ hr M hMle (by rfl)
  have hposL : 0 < @ReverseMinkowski.determinant n (detMinimizer hℒ r hr) (detMinimizer_discrete hℒ (r := r) hr) := by
    haveI : DiscreteTopology ↥(detMinimizer hℒ r hr) := detMinimizer_discrete hℒ (r := r) hr
    exact det_pos (L := detMinimizer hℒ r hr)
  have hposM : 0 < ReverseMinkowski.determinant M := det_pos (L := M)
  exact Real.log_le_log hposL hmin

/-- Fin-indexed form: a sublattice of rank `⟨finrank M, hrM⟩` (as an element of
`Fin (n+1)`) satisfies `minLogSeq ⟨finrank M, hrM⟩ ≤ log det M`. -/
lemma minLogSeq_le_log_det {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (M : Submodule ℤ E) [DiscreteTopology M] (hMle : M ≤ ℒ)
    (hrM : Module.finrank ℤ M < n + 1) :
    minLogSeq hℒ ⟨Module.finrank ℤ M, hrM⟩ ≤ Real.log (ReverseMinkowski.determinant M) := by
  classical
  have hleF : Module.finrank ℤ M ≤ Module.finrank ℤ ℒ :=
    finrank_le_of_le (ℒ' := M) (ℒ := ℒ) hMle
  have h := minLogDet_le_log_det hℒ M hMle
  have hEq : minLogSeq hℒ ⟨Module.finrank ℤ M, hrM⟩ = minLogDet hℒ (Module.finrank ℤ M) hleF := by
    dsimp [minLogSeq]
  rw [hEq]
  exact h

/-- **Hull of the determinant minimizers.**  The sequence `i ↦ log det(minimizer at rank i)`
(for `i = 0, …, n`) has a lower-hull vertex chain `0 = v₀ < ⋯ < v_k = n`; every sublattice of
`ℒ` whose rank `r` lies between two consecutive vertex ranks lies on or above the segment between
the consecutive vertex points (in log-det). -/
theorem hull_of_minimizers {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ) :
    ∃ (k : ℕ) (v : Fin (k + 1) → Fin (n + 1)),
      v 0 = 0 ∧
      v ⟨k, Nat.lt_succ_self k⟩ = ⟨n, Nat.lt_succ_self n⟩ ∧
      (∀ j : Fin k, (v (Fin.castSucc j)).val < (v (Fin.succ j)).val) ∧
      (∀ (j : Fin k) (M : Submodule ℤ E) [DiscreteTopology M], M ≤ ℒ →
        (v (Fin.castSucc j)).val ≤ Module.finrank ℤ M →
          Module.finrank ℤ M ≤ (v (Fin.succ j)).val →
            minLogSeq hℒ (v (Fin.castSucc j)) +
                (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) *
                  (((Module.finrank ℤ M : ℝ) - ((v (Fin.castSucc j)).val : ℝ)) /
                    (((v (Fin.succ j)).val : ℝ) - ((v (Fin.castSucc j)).val : ℝ))) ≤
              Real.log (ReverseMinkowski.determinant M)) ∧
      (∀ (j : Fin k) (hj : j.val + 1 < k),
        (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) /
            (((v (Fin.succ j)).val : ℝ) - ((v (Fin.castSucc j)).val : ℝ)) <
          (minLogSeq hℒ (v ⟨j.val + 2, by omega⟩) - minLogSeq hℒ (v (Fin.succ j))) /
            (((v ⟨j.val + 2, by omega⟩).val : ℝ) - ((v (Fin.succ j)).val : ℝ))) := by
  classical
  rcases (Commons.Geometry.LowerHull.exists_lower_hull_chain (N := n) (y := minLogSeq hℒ)) with
    ⟨k, v, hv0, hvN, hinc, hseg, hslope⟩
  refine ⟨k, v, ?_, ?_, ?_, ?_, ?_⟩
  · exact hv0
  · exact hvN
  · exact hinc
  · intro j M hdt hMle haM hMb
    haveI : DiscreteTopology ↥M := hdt
    have hrM' : Module.finrank ℤ M < n + 1 := by
      have hleF : Module.finrank ℤ M ≤ Module.finrank ℤ ℒ :=
        finrank_le_of_le (ℒ' := M) (ℒ := ℒ) hMle
      rw [fullrank_finrank ℒ hℒ] at hleF
      omega
    let i : Fin (n + 1) := ⟨Module.finrank ℤ M, hrM'⟩
    have hseg' := hseg j i (by simpa [i] using haM) (by simpa [i] using hMb)
    have h2 : minLogSeq hℒ i ≤ Real.log (ReverseMinkowski.determinant M) := by
      exact minLogSeq_le_log_det hℒ M hMle hrM' 
    have hstep : minLogSeq hℒ (v (Fin.castSucc j)) +
          (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) *
            (((Module.finrank ℤ M : ℝ) - ((v (Fin.castSucc j)).val : ℝ)) /
              (((v (Fin.succ j)).val : ℝ) - ((v (Fin.castSucc j)).val : ℝ))) ≤
        minLogSeq hℒ i := by
      -- hseg' : minLogSeq (v csj) + (minLogSeq (v sj) - minLogSeq (v csj)) *
      --   (((i.val : ℝ) - (v csj).val)/((v sj).val - (v csj).val)) ≤ minLogSeq i
      simpa [i] using hseg'
    exact le_trans hstep h2
  · exact hslope


/-- A hull-vertex rank is at most the rank of the ambient lattice. -/
lemma vtx_rank_le {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} (v : Fin (k + 1) → Fin (n + 1)) (j : Fin (k + 1)) :
    (v j).val ≤ Module.finrank ℤ ℒ := by
  have hfin : Module.finrank ℤ ℒ = n := fullrank_finrank ℒ hℒ
  omega

/-- The lattice of the hull vertex at chain position `j`: the determinant-minimizer at rank
`(v j).val`. -/
noncomputable def vtxMinimizer {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} (v : Fin (k + 1) → Fin (n + 1)) (j : Fin (k + 1)) : Submodule ℤ E :=
  detMinimizer hℒ (v j).val (vtx_rank_le hℒ v j)

/-- The canonical discreteness witness of a vertex minimizer. -/
lemma vtxMinimizer_discrete {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} (v : Fin (k + 1) → Fin (n + 1)) (j : Fin (k + 1)) :
    DiscreteTopology ↥(vtxMinimizer hℒ v j) := by
  dsimp [vtxMinimizer]
  exact detMinimizer_discrete hℒ (r := (v j).val) (vtx_rank_le hℒ v j)

/-- A vertex minimizer is a sublattice of `ℒ` of the vertex rank. -/
lemma vtxMinimizer_le {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} (v : Fin (k + 1) → Fin (n + 1)) (j : Fin (k + 1)) :
    vtxMinimizer hℒ v j ≤ ℒ := by
  dsimp [vtxMinimizer]
  exact detMinimizer_le hℒ (r := (v j).val) (vtx_rank_le hℒ v j)

/-- The rank of a vertex minimizer is the vertex rank. -/
lemma vtxMinimizer_rank {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} (v : Fin (k + 1) → Fin (n + 1)) (j : Fin (k + 1)) :
    Module.finrank ℤ ↥(vtxMinimizer hℒ v j) = (v j).val := by
  dsimp [vtxMinimizer]
  exact detMinimizer_rank hℒ (r := (v j).val) (vtx_rank_le hℒ v j)

/-- The log-determinant of a vertex minimizer equals the hull value at the vertex:
the vertex points sit ON the lower hull. -/
lemma minLogSeq_eq_log_vtxDet {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} (v : Fin (k + 1) → Fin (n + 1)) (j : Fin (k + 1)) :
    minLogSeq hℒ (v j) =
      Real.log (@ReverseMinkowski.determinant n (vtxMinimizer hℒ v j) (vtxMinimizer_discrete hℒ v j)) := by
  classical
  dsimp [minLogSeq, minLogDet, vtxMinimizer]


/-- A rank-`r` determinant-minimizer is ambient-primitive in `ℒ`. -/
lemma detMinimizer_primitive {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {r : ℕ} (hr : r ≤ Module.finrank ℤ ℒ) : Primitive (detMinimizer hℒ r hr) ℒ := by
  classical
  let L : Submodule ℤ E := detMinimizer hℒ r hr
  haveI : DiscreteTopology ↥L := by
    dsimp [L]
    exact detMinimizer_discrete hℒ (r := r) hr
  let P : Submodule ℤ E := primitiveClosure ℒ L
  have hLle : L ≤ ℒ := by
    dsimp [L]
    exact detMinimizer_le hℒ (r := r) hr
  have hLP : L ≤ P := by
    intro x hx
    exact (mem_primitiveClosure).mpr ⟨hLle hx, mem_realSpan (ℒ := L) hx⟩
  have hPle : P ≤ ℒ := inf_le_left
  haveI : DiscreteTopology ↥P :=
    Commons.Lattice.Discrete.discreteTopology_of_le (n := n) (ℒ := ℒ) (ℒ' := P) hPle
  have hfinP : Module.finrank ℤ ↥P = Module.finrank ℤ ↥L := by
    dsimp [P]
    exact finrank_closure_eq (sup := ℒ) (M := L) hLle
  have hrankL : Module.finrank ℤ ↥L = r := by
    dsimp [L]
    exact detMinimizer_rank hℒ (r := r) hr
  have hP : P = L := by
    have hPleL : P ≤ L := by
      by_contra hnot
      have hlt : L < P := lt_of_le_of_ne hLP (by
        intro hLP_eq
        apply hnot
        exact hLP_eq ▸ le_rfl)
      haveI : Module.Free ℤ L := instModuleFree_of_discrete_submodule L
      haveI : Module.Finite ℤ L := instModuleFinite_of_discrete_submodule L
      haveI : Module.Free ℤ P := instModuleFree_of_discrete_submodule P
      haveI : Module.Finite ℤ P := instModuleFinite_of_discrete_submodule P
      let r' : ℕ := Module.finrank ℤ L
      let e : Module.Basis (Fin r') ℤ L := Module.finBasis ℤ L
      let f : Module.Basis (Fin r') ℤ P := (Module.finBasis ℤ P).reindex (finCongr hfinP)
      have hstrict : √((Matrix.gram ℝ (fun i : Fin r' => ((e i : L) : E))).det) >
          √((Matrix.gram ℝ (fun i : Fin r' => ((f i : P) : E))).det) := by
        exact Commons.Lattice.Determinant.det_lt_of_lt_same_rank (N := n) (e := e) (f := f) hlt
      have hdetL : ReverseMinkowski.determinant L = √((Matrix.gram ℝ (fun i : Fin r' => ((e i : L) : E))).det) := by
        simpa [e, Matrix.gram] using (det_eq_sqrt_gram_any_basis (L := L) (Module.finBasis ℤ L))
      have hdetP : ReverseMinkowski.determinant P = √((Matrix.gram ℝ (fun i : Fin r' => ((f i : P) : E))).det) := by
        dsimp [f]
        simpa [Matrix.gram] using (det_eq_sqrt_gram_any_basis (L := P) ((Module.finBasis ℤ P).reindex (finCongr hfinP)))
      have hdetPL : ReverseMinkowski.determinant P < ReverseMinkowski.determinant L := by
        simpa [hdetL, hdetP] using hstrict
      have hfinPr : Module.finrank ℤ ↥P = r := by
        exact hfinP.trans hrankL
      have hmin := detMinimizer_le_det (ℒ := ℒ) hℒ hr P hPle hfinPr
      have hdetL_le : ReverseMinkowski.determinant L ≤ ReverseMinkowski.determinant P := by
        -- hmin : @det L (detMinimizer_discrete …) ≤ det P; L = detMinimizer with instance equal to witness
        simpa [L] using hmin
      exact (not_lt_of_ge hdetL_le) hdetPL
    exact le_antisymm hPleL hLP
  -- Primitive L ℒ
  intro x
  constructor
  · intro hx
    exact ⟨hLle hx, mem_realSpan (ℒ := L) hx⟩
  · rintro ⟨hxℒ, hxspan⟩
    have hxP : x ∈ P := (mem_primitiveClosure).mpr ⟨hxℒ, hxspan⟩
    simpa [hP] using hxP


/-- chord value of the affine segment through (c, u), (d, v) at abscissa x. -/
def chordv (c u d v x : ℝ) : ℝ := u + (v - u) * ((x - c) / (d - c))

/-- Chord values are monotone in the endpoint ordinates, for x between the abscissae. -/
lemma chordv_mono {c u u' d v v' x : ℝ} (hcd : c < d) (hcx : c ≤ x) (hxd : x ≤ d)
    (hu : u ≤ u') (hv : v ≤ v') : chordv c u d v x ≤ chordv c u' d v' x := by
  unfold chordv
  let t : ℝ := (x - c) / (d - c)
  have h1 : 0 ≤ t := by dsimp [t]; exact div_nonneg (sub_nonneg.mpr hcx) (sub_pos.mpr hcd).le
  have h2 : 0 ≤ 1 - t := by
    dsimp [t]
    have h3 : (x - c) / (d - c) ≤ 1 := by
      rw [div_le_one (sub_pos.mpr hcd)]
      nlinarith
    linarith
  have h3 : (u' - u) * (1 - t) ≥ 0 := mul_nonneg (sub_nonneg.mpr hu) h2
  have h4 : (v' - v) * t ≥ 0 := mul_nonneg (sub_nonneg.mpr hv) h1
  have hdecomp : (u' + (v' - u') * t) - (u + (v - u) * t) = (u' - u) * (1 - t) + (v' - v) * t := by
    ring
  change u + (v - u) * t ≤ u' + (v' - u') * t
  have hrew : 0 ≤ (u' + (v' - u') * t) - (u + (v - u) * t) := by
    rw [hdecomp]
    nlinarith
  exact sub_nonneg.mp hrew

/-- Reflection algebra: if the point (r, z) lies strictly below the affine line through
(c, u) and (d, v), its reflection (x, y) := (c + d - r, u + v - z) through the chord midpoint
lies strictly ABOVE that line at abscissa x. -/
lemma reflect_above_line {c u d v z r x : ℝ} (hcd : c < d) (hcr : c < r) (hrd : r < d)
    (hx : x = c + d - r) (hz : z < chordv c u d v r) :
    chordv c u d v x < u + v - z := by
  have hdc : d - c ≠ 0 := ne_of_gt (sub_pos.mpr hcd)
  have hxr : x - c = d - r := by
    rw [hx]
    ring
  have hdiff : (u + v - z) - chordv c u d v x = chordv c u d v r - z := by
    unfold chordv
    rw [hxr]
    field_simp [hdc]
    ring
  have hpos : 0 < (u + v - z) - chordv c u d v x := by
    rw [hdiff]
    exact sub_pos.mpr hz
  exact sub_pos.mp hpos

/-- Stuhler uncrossing in log form: for primitive `L₁, L₂ ≤ L`,
`log det(L₁⊓L₂) + log det(L₁⊔L₂) ≤ log det L₁ + log det L₂`. -/
lemma uncrossing_log {L L₁ L₂ : Submodule ℤ E} [DiscreteTopology L] [DiscreteTopology L₁]
    [DiscreteTopology L₂] [DiscreteTopology ↥(L₁ ⊔ L₂)] [DiscreteTopology ↥(L₁ ⊓ L₂)]
    (h₁ : L₁ ≤ L) (h₂ : L₂ ≤ L) (hp₁ : Primitive L₁ L) (hp₂ : Primitive L₂ L) :
    Real.log (ReverseMinkowski.determinant (L₁ ⊓ L₂)) +
        Real.log (ReverseMinkowski.determinant (L₁ ⊔ L₂)) ≤
      Real.log (ReverseMinkowski.determinant L₁) + Real.log (ReverseMinkowski.determinant L₂) := by
  classical
  have huc := uncrossing_det (L := L) (L₁ := L₁) (L₂ := L₂) h₁ h₂ hp₁ hp₂
  have hpos_sup : 0 < ReverseMinkowski.determinant (L₁ ⊔ L₂) := det_pos (L := L₁ ⊔ L₂)
  have hpos_inf : 0 < ReverseMinkowski.determinant (L₁ ⊓ L₂) := det_pos (L := L₁ ⊓ L₂)
  have hpos₁ : 0 < ReverseMinkowski.determinant L₁ := det_pos (L := L₁)
  have hpos₂ : 0 < ReverseMinkowski.determinant L₂ := det_pos (L := L₂)
  have hlog := Real.log_le_log (mul_pos hpos_sup hpos_inf) huc
  have hmul₁ : Real.log (ReverseMinkowski.determinant L₁) +
      Real.log (ReverseMinkowski.determinant L₂) =
      Real.log (ReverseMinkowski.determinant L₁ * ReverseMinkowski.determinant L₂) := by
    rw [Real.log_mul (ne_of_gt hpos₁) (ne_of_gt hpos₂)]
  calc
    Real.log (ReverseMinkowski.determinant (L₁ ⊓ L₂)) +
        Real.log (ReverseMinkowski.determinant (L₁ ⊔ L₂))
        = Real.log (ReverseMinkowski.determinant (L₁ ⊓ L₂) * ReverseMinkowski.determinant (L₁ ⊔ L₂)) := by
            rw [Real.log_mul (ne_of_gt hpos_inf) (ne_of_gt hpos_sup)]
    _ = Real.log (ReverseMinkowski.determinant (L₁ ⊔ L₂) * ReverseMinkowski.determinant (L₁ ⊓ L₂)) := by
            rw [mul_comm]
    _ ≤ Real.log (ReverseMinkowski.determinant L₁ * ReverseMinkowski.determinant L₂) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hlog
    _ = Real.log (ReverseMinkowski.determinant L₁) + Real.log (ReverseMinkowski.determinant L₂) := hmul₁.symm


/-- chord value of the affine segment through (c, u), (d, v) at abscissa x. -/
lemma detMinimizer_rank_sup_gt {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {r : ℕ} (hr : r ≤ Module.finrank ℤ ℒ) (M' : Submodule ℤ E) [DiscreteTopology M']
    (hM'le : M' ≤ ℒ) (hfin : Module.finrank ℤ M' ≤ r) (hnot : ¬ M' ≤ detMinimizer hℒ r hr) :
    r < Module.finrank ℤ ↥(detMinimizer hℒ r hr ⊔ M') := by
  classical
  let L : Submodule ℤ E := detMinimizer hℒ r hr
  haveI : DiscreteTopology ↥L := by dsimp [L]; exact detMinimizer_discrete hℒ (r := r) hr
  have hLle : L ≤ ℒ := by dsimp [L]; exact detMinimizer_le hℒ (r := r) hr
  haveI : DiscreteTopology ↥(L ⊔ M') :=
    Commons.Lattice.Discrete.discreteTopology_of_le (n := n) (ℒ := ℒ) (ℒ' := L ⊔ M')
      (sup_le hLle hM'le)
  have hrankL : Module.finrank ℤ ↥L = r := by
    dsimp [L]
    exact detMinimizer_rank hℒ (r := r) hr
  by_contra hnotr
  have hle_rk : Module.finrank ℤ ↥(L ⊔ M') ≤ r := le_of_not_gt hnotr
  have hgeq : r ≤ Module.finrank ℤ ↥(L ⊔ M') := by
    -- rank L = r ≤ rank(L ⊔ M') since L ⊆ L ⊔ M'
    have hleS : L ≤ L ⊔ M' := le_sup_left
    haveI : Module.Free ℤ L := instModuleFree_of_discrete_submodule L
    haveI : Module.Finite ℤ L := instModuleFinite_of_discrete_submodule L
    haveI : Module.Free ℤ ↥(L ⊔ M') := instModuleFree_of_discrete_submodule (L ⊔ M')
    haveI : Module.Finite ℤ ↥(L ⊔ M') := instModuleFinite_of_discrete_submodule (L ⊔ M')
    have hle' : Module.finrank ℤ ↥L ≤ Module.finrank ℤ ↥(L ⊔ M') :=
      finrank_le_of_le (ℒ' := L) (ℒ := L ⊔ M') hleS
    rwa [← hrankL]
  have hEq : Module.finrank ℤ ↥(L ⊔ M') = r := le_antisymm hle_rk hgeq
  -- L < L ⊔ M'
  have hlt : L < L ⊔ M' := by
    have hle1 : L ≤ L ⊔ M' := le_sup_left
    have hne : L ≠ L ⊔ M' := by
      intro hEqL
      apply hnot
      -- M' ⊆ L
      intro x hx
      have hxS : x ∈ L ⊔ M' := (le_sup_right : M' ≤ L ⊔ M') hx
      rwa [← hEqL] at hxS
    exact lt_of_le_of_ne hle1 hne
  -- det-strict: det(L ⊔ M') < det L
  haveI : Module.Free ℤ ↥(L ⊔ M') := instModuleFree_of_discrete_submodule (L ⊔ M')
  haveI : Module.Finite ℤ ↥(L ⊔ M') := instModuleFinite_of_discrete_submodule (L ⊔ M')
  let rr : ℕ := Module.finrank ℤ L
  let e : Module.Basis (Fin rr) ℤ L := Module.finBasis ℤ L
  have hfinSup : Module.finrank ℤ ↥(L ⊔ M') = Module.finrank ℤ ↥L := hEq.trans hrankL.symm
  let f : Module.Basis (Fin rr) ℤ ↥(L ⊔ M') := (Module.finBasis ℤ ↥(L ⊔ M')).reindex (finCongr hfinSup)
  have hstrict : √((Matrix.gram ℝ (fun i : Fin rr => ((e i : L) : E))).det) >
      √((Matrix.gram ℝ (fun i : Fin rr => ((f i : ↥(L ⊔ M')) : E))).det) := by
    exact Commons.Lattice.Determinant.det_lt_of_lt_same_rank (N := n) (e := e) (f := f) hlt
  have hdetL : ReverseMinkowski.determinant L = √((Matrix.gram ℝ (fun i : Fin rr => ((e i : L) : E))).det) := by
    simpa [e, Matrix.gram] using (det_eq_sqrt_gram_any_basis (L := L) (Module.finBasis ℤ L))
  have hdetS : ReverseMinkowski.determinant (L ⊔ M') = √((Matrix.gram ℝ (fun i : Fin rr => ((f i : ↥(L ⊔ M')) : E))).det) := by
    dsimp [f]
    simpa [Matrix.gram] using (det_eq_sqrt_gram_any_basis (L := L ⊔ M') ((Module.finBasis ℤ ↥(L ⊔ M')).reindex (finCongr hfinSup)))
  have hdetS_lt_L : ReverseMinkowski.determinant (L ⊔ M') < ReverseMinkowski.determinant L := by
    simpa [hdetL, hdetS] using hstrict
  -- minimality: det L ≤ det(L ⊔ M')
  have hmin : @ReverseMinkowski.determinant n (detMinimizer hℒ r hr) (detMinimizer_discrete hℒ (r := r) hr) ≤
      ReverseMinkowski.determinant (L ⊔ M') := by
    exact detMinimizer_le_det (ℒ := ℒ) hℒ hr (L ⊔ M') (sup_le hLle hM'le) hEq
  have hdetL_le_S : ReverseMinkowski.determinant L ≤ ReverseMinkowski.determinant (L ⊔ M') := by
    simpa [L] using hmin
  exact (not_lt_of_ge hdetL_le_S) hdetS_lt_L

theorem vertex_minimizers_nested {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ) :
    ∃ (k : ℕ) (v : Fin (k + 1) → Fin (n + 1)),
      v 0 = 0 ∧
      v ⟨k, Nat.lt_succ_self k⟩ = ⟨n, Nat.lt_succ_self n⟩ ∧
      (∀ j : Fin k, (v (Fin.castSucc j)).val < (v (Fin.succ j)).val) ∧
      (∀ j : Fin k, vtxMinimizer hℒ v (Fin.castSucc j) ≤ vtxMinimizer hℒ v (Fin.succ j)) := by
  classical
  rcases (Commons.Geometry.LowerHull.exists_lower_hull_chain (N := n) (y := minLogSeq hℒ)) with
    ⟨k, v, hv0, hvN, hinc, hseg, hslope⟩
  refine ⟨k, v, hv0, hvN, hinc, ?_⟩
  intro j
  let M' : Submodule ℤ E := vtxMinimizer hℒ v (Fin.castSucc j)
  let L : Submodule ℤ E := vtxMinimizer hℒ v (Fin.succ j)
  let r' : ℕ := (v (Fin.castSucc j)).val
  let r : ℕ := (v (Fin.succ j)).val
  have hfinM' : Module.finrank ℤ ↥M' = r' := by
    dsimp [M', r']
    exact vtxMinimizer_rank hℒ v (Fin.castSucc j)
  have hfinL : Module.finrank ℤ ↥L = r := by
    dsimp [L, r]
    exact vtxMinimizer_rank hℒ v (Fin.succ j)
  have hM'le : M' ≤ ℒ := by dsimp [M']; exact vtxMinimizer_le hℒ v (Fin.castSucc j)
  have hLle : L ≤ ℒ := by dsimp [L]; exact vtxMinimizer_le hℒ v (Fin.succ j)
  haveI : DiscreteTopology ↥M' := by dsimp [M']; exact vtxMinimizer_discrete hℒ v (Fin.castSucc j)
  haveI : DiscreteTopology ↥L := by dsimp [L]; exact vtxMinimizer_discrete hℒ v (Fin.succ j)
  have hr'r : r' < r := by dsimp [r', r]; exact hinc j
  have hpM' : Primitive M' ℒ := by
    dsimp [M', vtxMinimizer]
    exact detMinimizer_primitive hℒ (r := (v (Fin.castSucc j)).val) (vtx_rank_le hℒ v (Fin.castSucc j))
  have hpL : Primitive L ℒ := by
    dsimp [L, vtxMinimizer]
    exact detMinimizer_primitive hℒ (r := (v (Fin.succ j)).val) (vtx_rank_le hℒ v (Fin.succ j))
  by_contra hnot
  let inter : Submodule ℤ E := M' ⊓ L
  let sum : Submodule ℤ E := M' ⊔ L
  let c : ℕ := Module.finrank ℤ ↥inter
  let d : ℕ := Module.finrank ℤ ↥sum
  have hIle : inter ≤ ℒ := by dsimp [inter]; exact le_trans inf_le_left hM'le
  have hSle : sum ≤ ℒ := by dsimp [sum]; exact sup_le hM'le hLle
  haveI : DiscreteTopology ↥inter :=
    Commons.Lattice.Discrete.discreteTopology_of_le (n := n) (ℒ := ℒ) (ℒ' := inter) hIle
  haveI : DiscreteTopology ↥sum :=
    Commons.Lattice.Discrete.discreteTopology_of_le (n := n) (ℒ := ℒ) (ℒ' := sum) hSle
  -- (A) r < d via the rank-gap lemma
  have hrfinM' : Module.finrank ℤ M' ≤ r := by
    rw [hfinM']
    exact le_of_lt hr'r
  have hgap := detMinimizer_rank_sup_gt (ℒ := ℒ) hℒ (r := r) (vtx_rank_le hℒ v (Fin.succ j))
    M' hM'le hrfinM' hnot
  -- hgap : r < finrank ↥(detMinimizer hℒ r (vtx_rank_le …) ⊔ M')
  have hdgt : r < d := by
    dsimp [d, sum]
    -- finrank ↥(M' ⊔ L) = finrank ↥(detMinimizer ⊔ M') via sup_comm and L-defeq
    have heq1 : M' ⊔ L = detMinimizer hℒ r (vtx_rank_le hℒ v (Fin.succ j)) ⊔ M' := by
      dsimp [L, vtxMinimizer]
      rw [sup_comm]
    have hfeq : Module.finrank ℤ ↥(M' ⊔ L) = Module.finrank ℤ ↥(detMinimizer hℒ r (vtx_rank_le hℒ v (Fin.succ j)) ⊔ M') := by
      exact finrank_eq_of_eq heq1
    rw [hfeq]
    exact hgap
  -- (B) rank equations
  have hrank_uncross := uncrossing_rank (L := ℒ) (L₁ := M') (L₂ := L) hM'le hLle
  have hcd : Module.finrank ℤ ↥sum + Module.finrank ℤ ↥inter = r' + r := by
    dsimp [inter, sum]
    simpa [hfinM', hfinL] using hrank_uncross
  have hcr' : c < r' := by
    dsimp [c, d] at hcd ⊢
    omega
  have hcr : c < r := lt_trans hcr' hr'r
  have hr'd : r' < d := lt_trans hr'r hdgt
  have hcdlt : c < d := lt_trans hcr hdgt
  -- abscissa bounds
  have hr'le : r' ≤ n := by
    dsimp [r']
    exact Nat.lt_succ_iff.mp (v (Fin.castSucc j)).isLt
  have hcle : c ≤ n := by
    haveI : Module.Free ℤ ↥inter := instModuleFree_of_discrete_submodule inter
    haveI : Module.Finite ℤ ↥inter := instModuleFinite_of_discrete_submodule inter
    haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
    haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
    have hleF : Module.finrank ℤ ↥inter ≤ Module.finrank ℤ ℒ :=
      finrank_le_of_le (ℒ' := inter) (ℒ := ℒ) hIle
    have hfin : Module.finrank ℤ ℒ = n := fullrank_finrank ℒ hℒ
    dsimp [c]
    omega
  have hdle : d ≤ n := by
    haveI : Module.Free ℤ ↥sum := instModuleFree_of_discrete_submodule sum
    haveI : Module.Finite ℤ ↥sum := instModuleFinite_of_discrete_submodule sum
    haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
    haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
    have hleF : Module.finrank ℤ ↥sum ≤ Module.finrank ℤ ℒ :=
      finrank_le_of_le (ℒ' := sum) (ℒ := ℒ) hSle
    have hfin : Module.finrank ℤ ℒ = n := fullrank_finrank ℒ hℒ
    dsimp [d]
    omega
  let cfin : Fin (n + 1) := ⟨c, Nat.lt_succ_iff.mpr hcle⟩
  let dfin : Fin (n + 1) := ⟨d, Nat.lt_succ_iff.mpr hdle⟩
  -- log facts
  let Clog : ℝ := Real.log (ReverseMinkowski.determinant inter)
  let Dlog : ℝ := Real.log (ReverseMinkowski.determinant sum)
  have hC_ge : minLogSeq hℒ cfin ≤ Clog := by
    dsimp [Clog, cfin]
    exact minLogSeq_le_log_det hℒ inter hIle (by dsimp [c] at hcle ⊢; omega)
  have hD_ge : minLogSeq hℒ dfin ≤ Dlog := by
    dsimp [Dlog, dfin]
    exact minLogSeq_le_log_det hℒ sum hSle (by dsimp [d] at hdle ⊢; omega)
  -- vertex-below-chord at vertex (v (Fin.succ j)), abscissa r
  have hvb1 := Commons.Geometry.LowerHull.vertex_below_chord (y := minLogSeq hℒ)
    (hv0 := hv0) (hvN := hvN) (hinc := hinc) (hseg := hseg) (hslope := hslope)
    (r := v (Fin.succ j)) (c := cfin) (d := dfin)
    (hcr := hcr) (hrd := hdgt)
    (hvert := ⟨Fin.succ j, rfl⟩)
  have hvb1' : minLogSeq hℒ (v (Fin.succ j)) < chordv (c : ℝ) (minLogSeq hℒ cfin) (d : ℝ) (minLogSeq hℒ dfin) (r : ℝ) := by
    dsimp [r] at hvb1 ⊢
    simpa [cfin, dfin, chordv] using hvb1
  -- chord with actual inter/sum ≥ chord with data
  have hch1 : chordv (c : ℝ) (minLogSeq hℒ cfin) (d : ℝ) (minLogSeq hℒ dfin) (r : ℝ) ≤
      chordv (c : ℝ) Clog (d : ℝ) Dlog (r : ℝ) := by
    exact chordv_mono (by exact_mod_cast hcdlt) (le_of_lt (by exact_mod_cast hcr))
      (le_of_lt (by exact_mod_cast hdgt)) hC_ge hD_ge
  have hL_lt_c : minLogSeq hℒ (v (Fin.succ j)) < chordv (c : ℝ) Clog (d : ℝ) Dlog (r : ℝ) :=
    lt_of_lt_of_le hvb1' hch1
  -- L's log-det equals the hull value at r
  have hLlog : Real.log (ReverseMinkowski.determinant L) = minLogSeq hℒ (v (Fin.succ j)) := by
    simpa [L, vtxMinimizer] using (minLogSeq_eq_log_vtxDet hℒ v (Fin.succ j)).symm
  have hL_below : Real.log (ReverseMinkowski.determinant L) < chordv (c : ℝ) Clog (d : ℝ) Dlog (r : ℝ) := by
    rw [hLlog]
    exact hL_lt_c
  -- (D) reflection
  let yv : ℝ := Clog + Dlog - Real.log (ReverseMinkowski.determinant L)
  have hx_eq : (r' : ℝ) = (c : ℝ) + (d : ℝ) - (r : ℝ) := by
    have hcd' : (Module.finrank ℤ ↥sum : ℝ) + (Module.finrank ℤ ↥inter : ℝ) = (r' : ℝ) + (r : ℝ) := by
      exact_mod_cast hcd
    have hc : (c : ℝ) + (d : ℝ) = (r' : ℝ) + (r : ℝ) := by
      simpa [c, d, add_comm, add_left_comm, add_assoc] using hcd'
    linarith
  have hreflect := reflect_above_line (c := (c : ℝ)) (u := Clog) (d := (d : ℝ)) (v := Dlog)
    (z := Real.log (ReverseMinkowski.determinant L)) (r := (r : ℝ)) (x := (r' : ℝ))
    (by exact_mod_cast hcdlt) (by exact_mod_cast hcr) (by exact_mod_cast hdgt) hx_eq hL_below
  have hreflect' : chordv (c : ℝ) Clog (d : ℝ) Dlog (r' : ℝ) < yv := by
    simpa [yv] using hreflect
  -- (E) uncrossing_log: log det M' ≥ yv
  have hunc := uncrossing_log (L := ℒ) (L₁ := M') (L₂ := L) hM'le hLle hpM' hpL
  have hM'_ge_yv : yv ≤ Real.log (ReverseMinkowski.determinant M') := by
    dsimp [yv]
    have huc' : Clog + Dlog ≤ Real.log (ReverseMinkowski.determinant M') + Real.log (ReverseMinkowski.determinant L) := by
      simpa [Clog, Dlog, inter, sum] using hunc
    nlinarith [huc', hLlog]
  -- (F) vertex-below-chord at vertex (v (Fin.castSucc j)), abscissa r'
  have hvb2 := Commons.Geometry.LowerHull.vertex_below_chord (y := minLogSeq hℒ)
    (hv0 := hv0) (hvN := hvN) (hinc := hinc) (hseg := hseg) (hslope := hslope)
    (r := v (Fin.castSucc j)) (c := cfin) (d := dfin)
    (hcr := hcr') (hrd := hr'd)
    (hvert := ⟨Fin.castSucc j, rfl⟩)
  have hvb2' : minLogSeq hℒ (v (Fin.castSucc j)) < chordv (c : ℝ) (minLogSeq hℒ cfin) (d : ℝ) (minLogSeq hℒ dfin) (r' : ℝ) := by
    dsimp [r'] at hvb2 ⊢
    simpa [cfin, dfin, chordv] using hvb2
  have hch2 : chordv (c : ℝ) (minLogSeq hℒ cfin) (d : ℝ) (minLogSeq hℒ dfin) (r' : ℝ) ≤
      chordv (c : ℝ) Clog (d : ℝ) Dlog (r' : ℝ) := by
    exact chordv_mono (by exact_mod_cast hcdlt) (le_of_lt (by exact_mod_cast hcr'))
      (le_of_lt (by exact_mod_cast hr'd)) hC_ge hD_ge
  have hM_lt_c : minLogSeq hℒ (v (Fin.castSucc j)) < chordv (c : ℝ) Clog (d : ℝ) Dlog (r' : ℝ) :=
    lt_of_lt_of_le hvb2' hch2
  have hMlog : Real.log (ReverseMinkowski.determinant M') = minLogSeq hℒ (v (Fin.castSucc j)) := by
    simpa [M', vtxMinimizer] using (minLogSeq_eq_log_vtxDet hℒ v (Fin.castSucc j)).symm
  -- contradiction: logdet M' ≥ yv > chord > logdet M'
  have hbad1 : minLogSeq hℒ (v (Fin.castSucc j)) < yv := lt_trans hM_lt_c hreflect'
  have hbad2 : yv ≤ Real.log (ReverseMinkowski.determinant M') := hM'_ge_yv
  have hbad3 : minLogSeq hℒ (v (Fin.castSucc j)) < Real.log (ReverseMinkowski.determinant M') :=
    lt_of_lt_of_le hbad1 hbad2
  exact (not_lt_of_ge (by rw [hMlog])) hbad3


lemma vertex_nested_of_hull {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} {v : Fin (k + 1) → Fin (n + 1)}
    (hv0 : v 0 = 0)
    (hvN : v ⟨k, Nat.lt_succ_self k⟩ = ⟨n, Nat.lt_succ_self n⟩)
    (hinc : ∀ j : Fin k, (v (Fin.castSucc j)).val < (v (Fin.succ j)).val)
    (hseg : ∀ (j : Fin k) (i : Fin (n + 1)),
      (v (Fin.castSucc j)).val ≤ i.val → i.val ≤ (v (Fin.succ j)).val →
        minLogSeq hℒ (v (Fin.castSucc j)) +
            (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) *
              ((i.val - (v (Fin.castSucc j)).val) / ((v (Fin.succ j)).val - (v (Fin.castSucc j)).val)) ≤
          minLogSeq hℒ i)
    (hslope : ∀ (j : Fin k) (hj : j.val + 1 < k),
      (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) /
          ((v (Fin.succ j)).val - (v (Fin.castSucc j)).val) <
        (minLogSeq hℒ (v ⟨j.val + 2, by omega⟩) - minLogSeq hℒ (v (Fin.succ j))) /
          ((v ⟨j.val + 2, by omega⟩).val - (v (Fin.succ j)).val)) :
    ∀ j : Fin k, vtxMinimizer hℒ v (Fin.castSucc j) ≤ vtxMinimizer hℒ v (Fin.succ j) := by
  classical
  intro j
  let M' : Submodule ℤ E := vtxMinimizer hℒ v (Fin.castSucc j)
  let L : Submodule ℤ E := vtxMinimizer hℒ v (Fin.succ j)
  let r' : ℕ := (v (Fin.castSucc j)).val
  let r : ℕ := (v (Fin.succ j)).val
  have hfinM' : Module.finrank ℤ ↥M' = r' := by
    dsimp [M', r']
    exact vtxMinimizer_rank hℒ v (Fin.castSucc j)
  have hfinL : Module.finrank ℤ ↥L = r := by
    dsimp [L, r]
    exact vtxMinimizer_rank hℒ v (Fin.succ j)
  have hM'le : M' ≤ ℒ := by dsimp [M']; exact vtxMinimizer_le hℒ v (Fin.castSucc j)
  have hLle : L ≤ ℒ := by dsimp [L]; exact vtxMinimizer_le hℒ v (Fin.succ j)
  haveI : DiscreteTopology ↥M' := by dsimp [M']; exact vtxMinimizer_discrete hℒ v (Fin.castSucc j)
  haveI : DiscreteTopology ↥L := by dsimp [L]; exact vtxMinimizer_discrete hℒ v (Fin.succ j)
  have hr'r : r' < r := by dsimp [r', r]; exact hinc j
  have hpM' : Primitive M' ℒ := by
    dsimp [M', vtxMinimizer]
    exact detMinimizer_primitive hℒ (r := (v (Fin.castSucc j)).val) (vtx_rank_le hℒ v (Fin.castSucc j))
  have hpL : Primitive L ℒ := by
    dsimp [L, vtxMinimizer]
    exact detMinimizer_primitive hℒ (r := (v (Fin.succ j)).val) (vtx_rank_le hℒ v (Fin.succ j))
  by_contra hnot
  let inter : Submodule ℤ E := M' ⊓ L
  let sum : Submodule ℤ E := M' ⊔ L
  let c : ℕ := Module.finrank ℤ ↥inter
  let d : ℕ := Module.finrank ℤ ↥sum
  have hIle : inter ≤ ℒ := by dsimp [inter]; exact le_trans inf_le_left hM'le
  have hSle : sum ≤ ℒ := by dsimp [sum]; exact sup_le hM'le hLle
  haveI : DiscreteTopology ↥inter :=
    Commons.Lattice.Discrete.discreteTopology_of_le (n := n) (ℒ := ℒ) (ℒ' := inter) hIle
  haveI : DiscreteTopology ↥sum :=
    Commons.Lattice.Discrete.discreteTopology_of_le (n := n) (ℒ := ℒ) (ℒ' := sum) hSle
  -- (A) r < d via the rank-gap lemma
  have hrfinM' : Module.finrank ℤ M' ≤ r := by
    rw [hfinM']
    exact le_of_lt hr'r
  have hgap := detMinimizer_rank_sup_gt (ℒ := ℒ) hℒ (r := r) (vtx_rank_le hℒ v (Fin.succ j))
    M' hM'le hrfinM' hnot
  -- hgap : r < finrank ↥(detMinimizer hℒ r (vtx_rank_le …) ⊔ M')
  have hdgt : r < d := by
    dsimp [d, sum]
    -- finrank ↥(M' ⊔ L) = finrank ↥(detMinimizer ⊔ M') via sup_comm and L-defeq
    have heq1 : M' ⊔ L = detMinimizer hℒ r (vtx_rank_le hℒ v (Fin.succ j)) ⊔ M' := by
      dsimp [L, vtxMinimizer]
      rw [sup_comm]
    have hfeq : Module.finrank ℤ ↥(M' ⊔ L) = Module.finrank ℤ ↥(detMinimizer hℒ r (vtx_rank_le hℒ v (Fin.succ j)) ⊔ M') := by
      exact finrank_eq_of_eq heq1
    rw [hfeq]
    exact hgap
  -- (B) rank equations
  have hrank_uncross := uncrossing_rank (L := ℒ) (L₁ := M') (L₂ := L) hM'le hLle
  have hcd : Module.finrank ℤ ↥sum + Module.finrank ℤ ↥inter = r' + r := by
    dsimp [inter, sum]
    simpa [hfinM', hfinL] using hrank_uncross
  have hcr' : c < r' := by
    dsimp [c, d] at hcd ⊢
    omega
  have hcr : c < r := lt_trans hcr' hr'r
  have hr'd : r' < d := lt_trans hr'r hdgt
  have hcdlt : c < d := lt_trans hcr hdgt
  -- abscissa bounds
  have hr'le : r' ≤ n := by
    dsimp [r']
    exact Nat.lt_succ_iff.mp (v (Fin.castSucc j)).isLt
  have hcle : c ≤ n := by
    haveI : Module.Free ℤ ↥inter := instModuleFree_of_discrete_submodule inter
    haveI : Module.Finite ℤ ↥inter := instModuleFinite_of_discrete_submodule inter
    haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
    haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
    have hleF : Module.finrank ℤ ↥inter ≤ Module.finrank ℤ ℒ :=
      finrank_le_of_le (ℒ' := inter) (ℒ := ℒ) hIle
    have hfin : Module.finrank ℤ ℒ = n := fullrank_finrank ℒ hℒ
    dsimp [c]
    omega
  have hdle : d ≤ n := by
    haveI : Module.Free ℤ ↥sum := instModuleFree_of_discrete_submodule sum
    haveI : Module.Finite ℤ ↥sum := instModuleFinite_of_discrete_submodule sum
    haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
    haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
    have hleF : Module.finrank ℤ ↥sum ≤ Module.finrank ℤ ℒ :=
      finrank_le_of_le (ℒ' := sum) (ℒ := ℒ) hSle
    have hfin : Module.finrank ℤ ℒ = n := fullrank_finrank ℒ hℒ
    dsimp [d]
    omega
  let cfin : Fin (n + 1) := ⟨c, Nat.lt_succ_iff.mpr hcle⟩
  let dfin : Fin (n + 1) := ⟨d, Nat.lt_succ_iff.mpr hdle⟩
  -- log facts
  let Clog : ℝ := Real.log (ReverseMinkowski.determinant inter)
  let Dlog : ℝ := Real.log (ReverseMinkowski.determinant sum)
  have hC_ge : minLogSeq hℒ cfin ≤ Clog := by
    dsimp [Clog, cfin]
    exact minLogSeq_le_log_det hℒ inter hIle (by dsimp [c] at hcle ⊢; omega)
  have hD_ge : minLogSeq hℒ dfin ≤ Dlog := by
    dsimp [Dlog, dfin]
    exact minLogSeq_le_log_det hℒ sum hSle (by dsimp [d] at hdle ⊢; omega)
  -- vertex-below-chord at vertex (v (Fin.succ j)), abscissa r
  have hvb1 := Commons.Geometry.LowerHull.vertex_below_chord (y := minLogSeq hℒ)
    (hv0 := hv0) (hvN := hvN) (hinc := hinc) (hseg := hseg) (hslope := hslope)
    (r := v (Fin.succ j)) (c := cfin) (d := dfin)
    (hcr := hcr) (hrd := hdgt)
    (hvert := ⟨Fin.succ j, rfl⟩)
  have hvb1' : minLogSeq hℒ (v (Fin.succ j)) < chordv (c : ℝ) (minLogSeq hℒ cfin) (d : ℝ) (minLogSeq hℒ dfin) (r : ℝ) := by
    dsimp [r] at hvb1 ⊢
    simpa [cfin, dfin, chordv] using hvb1
  -- chord with actual inter/sum ≥ chord with data
  have hch1 : chordv (c : ℝ) (minLogSeq hℒ cfin) (d : ℝ) (minLogSeq hℒ dfin) (r : ℝ) ≤
      chordv (c : ℝ) Clog (d : ℝ) Dlog (r : ℝ) := by
    exact chordv_mono (by exact_mod_cast hcdlt) (le_of_lt (by exact_mod_cast hcr))
      (le_of_lt (by exact_mod_cast hdgt)) hC_ge hD_ge
  have hL_lt_c : minLogSeq hℒ (v (Fin.succ j)) < chordv (c : ℝ) Clog (d : ℝ) Dlog (r : ℝ) :=
    lt_of_lt_of_le hvb1' hch1
  -- L's log-det equals the hull value at r
  have hLlog : Real.log (ReverseMinkowski.determinant L) = minLogSeq hℒ (v (Fin.succ j)) := by
    simpa [L, vtxMinimizer] using (minLogSeq_eq_log_vtxDet hℒ v (Fin.succ j)).symm
  have hL_below : Real.log (ReverseMinkowski.determinant L) < chordv (c : ℝ) Clog (d : ℝ) Dlog (r : ℝ) := by
    rw [hLlog]
    exact hL_lt_c
  -- (D) reflection
  let yv : ℝ := Clog + Dlog - Real.log (ReverseMinkowski.determinant L)
  have hx_eq : (r' : ℝ) = (c : ℝ) + (d : ℝ) - (r : ℝ) := by
    have hcd' : (Module.finrank ℤ ↥sum : ℝ) + (Module.finrank ℤ ↥inter : ℝ) = (r' : ℝ) + (r : ℝ) := by
      exact_mod_cast hcd
    have hc : (c : ℝ) + (d : ℝ) = (r' : ℝ) + (r : ℝ) := by
      simpa [c, d, add_comm, add_left_comm, add_assoc] using hcd'
    linarith
  have hreflect := reflect_above_line (c := (c : ℝ)) (u := Clog) (d := (d : ℝ)) (v := Dlog)
    (z := Real.log (ReverseMinkowski.determinant L)) (r := (r : ℝ)) (x := (r' : ℝ))
    (by exact_mod_cast hcdlt) (by exact_mod_cast hcr) (by exact_mod_cast hdgt) hx_eq hL_below
  have hreflect' : chordv (c : ℝ) Clog (d : ℝ) Dlog (r' : ℝ) < yv := by
    simpa [yv] using hreflect
  -- (E) uncrossing_log: log det M' ≥ yv
  have hunc := uncrossing_log (L := ℒ) (L₁ := M') (L₂ := L) hM'le hLle hpM' hpL
  have hM'_ge_yv : yv ≤ Real.log (ReverseMinkowski.determinant M') := by
    dsimp [yv]
    have huc' : Clog + Dlog ≤ Real.log (ReverseMinkowski.determinant M') + Real.log (ReverseMinkowski.determinant L) := by
      simpa [Clog, Dlog, inter, sum] using hunc
    nlinarith [huc', hLlog]
  -- (F) vertex-below-chord at vertex (v (Fin.castSucc j)), abscissa r'
  have hvb2 := Commons.Geometry.LowerHull.vertex_below_chord (y := minLogSeq hℒ)
    (hv0 := hv0) (hvN := hvN) (hinc := hinc) (hseg := hseg) (hslope := hslope)
    (r := v (Fin.castSucc j)) (c := cfin) (d := dfin)
    (hcr := hcr') (hrd := hr'd)
    (hvert := ⟨Fin.castSucc j, rfl⟩)
  have hvb2' : minLogSeq hℒ (v (Fin.castSucc j)) < chordv (c : ℝ) (minLogSeq hℒ cfin) (d : ℝ) (minLogSeq hℒ dfin) (r' : ℝ) := by
    dsimp [r'] at hvb2 ⊢
    simpa [cfin, dfin, chordv] using hvb2
  have hch2 : chordv (c : ℝ) (minLogSeq hℒ cfin) (d : ℝ) (minLogSeq hℒ dfin) (r' : ℝ) ≤
      chordv (c : ℝ) Clog (d : ℝ) Dlog (r' : ℝ) := by
    exact chordv_mono (by exact_mod_cast hcdlt) (le_of_lt (by exact_mod_cast hcr'))
      (le_of_lt (by exact_mod_cast hr'd)) hC_ge hD_ge
  have hM_lt_c : minLogSeq hℒ (v (Fin.castSucc j)) < chordv (c : ℝ) Clog (d : ℝ) Dlog (r' : ℝ) :=
    lt_of_lt_of_le hvb2' hch2
  have hMlog : Real.log (ReverseMinkowski.determinant M') = minLogSeq hℒ (v (Fin.castSucc j)) := by
    simpa [M', vtxMinimizer] using (minLogSeq_eq_log_vtxDet hℒ v (Fin.castSucc j)).symm
  -- contradiction: logdet M' ≥ yv > chord > logdet M'
  have hbad1 : minLogSeq hℒ (v (Fin.castSucc j)) < yv := lt_trans hM_lt_c hreflect'
  have hbad2 : yv ≤ Real.log (ReverseMinkowski.determinant M') := hM'_ge_yv
  have hbad3 : minLogSeq hℒ (v (Fin.castSucc j)) < Real.log (ReverseMinkowski.determinant M') :=
    lt_of_lt_of_le hbad1 hbad2
  exact (not_lt_of_ge (by rw [hMlog])) hbad3

lemma eq_bot_of_finrank_zero {S : Submodule ℤ E} [DiscreteTopology S]
    (hfin : Module.finrank ℤ ↥S = 0) : S = ⊥ := by
  classical
  haveI : Module.Free ℤ ↥S := instModuleFree_of_discrete_submodule S
  haveI : Module.Finite ℤ ↥S := instModuleFinite_of_discrete_submodule S
  let b : Module.Basis (Fin 0) ℤ ↥S := (Module.finBasis ℤ ↥S).reindex (finCongr hfin)
  have hzero : ∀ x : S, x = 0 := by
    intro x
    have hsum := b.sum_repr x
    -- hsum : ∑ i : Fin 0, (b.repr x) i • b i = x ; LHS is 0
    simpa using hsum.symm
  apply le_antisymm
  · intro x hx
    have hx0 := hzero ⟨x, hx⟩
    exact congrArg (fun y : S => (y : E)) hx0
  · exact bot_le

-- generic: N ≤ ℒ with full rank and det N ≤ det ℒ forces N = ℒ
lemma eq_self_of_le_fullrank {N L : Submodule ℤ E} [DiscreteTopology N] [DiscreteTopology L]
    (hNL : N ≤ L) (hr : Module.finrank ℤ ↥N = Module.finrank ℤ ↥L)
    (hdet : ReverseMinkowski.determinant N ≤ ReverseMinkowski.determinant L) : N = L := by
  classical
  by_contra hne
  have hlt : N < L := lt_of_le_of_ne hNL hne
  haveI : Module.Free ℤ ↥N := instModuleFree_of_discrete_submodule N
  haveI : Module.Finite ℤ ↥N := instModuleFinite_of_discrete_submodule N
  haveI : Module.Free ℤ ↥L := instModuleFree_of_discrete_submodule L
  haveI : Module.Finite ℤ ↥L := instModuleFinite_of_discrete_submodule L
  let rr : ℕ := Module.finrank ℤ ↥N
  let e : Module.Basis (Fin rr) ℤ N := Module.finBasis ℤ N
  let f : Module.Basis (Fin rr) ℤ L := (Module.finBasis ℤ L).reindex (finCongr hr.symm)
  have hstrict : √((Matrix.gram ℝ (fun i : Fin rr => ((e i : N) : E))).det) >
      √((Matrix.gram ℝ (fun i : Fin rr => ((f i : L) : E))).det) := by
    exact Commons.Lattice.Determinant.det_lt_of_lt_same_rank (N := n) (e := e) (f := f) hlt
  have hdetN : ReverseMinkowski.determinant N = √((Matrix.gram ℝ (fun i : Fin rr => ((e i : N) : E))).det) := by
    simpa [e, Matrix.gram] using (det_eq_sqrt_gram_any_basis (L := N) (Module.finBasis ℤ N))
  have hdetL : ReverseMinkowski.determinant L = √((Matrix.gram ℝ (fun i : Fin rr => ((f i : L) : E))).det) := by
    dsimp [f]
    simpa [Matrix.gram] using (det_eq_sqrt_gram_any_basis (L := L) ((Module.finBasis ℤ L).reindex (finCongr hr.symm)))
  have hLtN : ReverseMinkowski.determinant L < ReverseMinkowski.determinant N := by
    simpa [hdetN, hdetL] using hstrict
  exact (not_lt_of_ge hdet) hLtN

-- vtx minimizer at a rank-0 vertex is ⊥
lemma vtxMinimizer_zero {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} {v : Fin (k + 1) → Fin (n + 1)} (hv0 : v 0 = 0) :
    vtxMinimizer hℒ v ⟨0, Nat.zero_lt_succ k⟩ = ⊥ := by
  have hfin : Module.finrank ℤ ↥(vtxMinimizer hℒ v ⟨0, Nat.zero_lt_succ k⟩) = 0 := by
    have h := vtxMinimizer_rank hℒ v ⟨0, Nat.zero_lt_succ k⟩
    -- h : finrank = (v ⟨0, _⟩).val
    have hv : (v ⟨0, Nat.zero_lt_succ k⟩).val = 0 := by
      simpa using congrArg Fin.val hv0
    rwa [hv] at h
  haveI : DiscreteTopology ↥(vtxMinimizer hℒ v ⟨0, Nat.zero_lt_succ k⟩) :=
    vtxMinimizer_discrete hℒ v ⟨0, Nat.zero_lt_succ k⟩
  exact eq_bot_of_finrank_zero hfin

-- vtx minimizer at the last vertex (rank n) equals ℒ
lemma vtxMinimizer_top {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} {v : Fin (k + 1) → Fin (n + 1)}
    (hvN : v ⟨k, Nat.lt_succ_self k⟩ = ⟨n, Nat.lt_succ_self n⟩) :
    vtxMinimizer hℒ v ⟨k, Nat.lt_succ_self k⟩ = ℒ := by
  classical
  let j : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  let M : Submodule ℤ E := vtxMinimizer hℒ v j
  have hMle : M ≤ ℒ := by dsimp [M]; exact vtxMinimizer_le hℒ v j
  haveI : DiscreteTopology ↥M := by dsimp [M]; exact vtxMinimizer_discrete hℒ v j
  haveI : DiscreteTopology ↥ℒ := by infer_instance
  have hr : Module.finrank ℤ ↥M = Module.finrank ℤ ℒ := by
    have h := vtxMinimizer_rank hℒ v j
    have hv : (v j).val = n := by
      dsimp [j]
      have hv' := congrArg Fin.val hvN
      simpa using hv'
    have hfin : Module.finrank ℤ ℒ = n := fullrank_finrank ℒ hℒ
    rw [h, hv, hfin]
  have hdet : ReverseMinkowski.determinant M ≤ ReverseMinkowski.determinant ℒ := by
    have hv : (v j).val = n := by
      dsimp [j]
      have hv' := congrArg Fin.val hvN
      simpa using hv'
    have hmin := detMinimizer_le_det (ℒ := ℒ) hℒ (vtx_rank_le hℒ v j) ℒ (le_refl ℒ)
      (by rw [fullrank_finrank ℒ hℒ, hv])
    dsimp [M, vtxMinimizer]
    simpa using hmin
  have hEq := eq_self_of_le_fullrank (N := M) (L := ℒ) hMle hr hdet
  exact hEq

lemma extremal_vtx_consecutive {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} {v : Fin (k + 1) → Fin (n + 1)}
    (hinc : ∀ j : Fin k, (v (Fin.castSucc j)).val < (v (Fin.succ j)).val)
    (hsegM : ∀ (j : Fin k) (M : Submodule ℤ E) [DiscreteTopology M], M ≤ ℒ →
        (v (Fin.castSucc j)).val ≤ Module.finrank ℤ M →
          Module.finrank ℤ M ≤ (v (Fin.succ j)).val →
            minLogSeq hℒ (v (Fin.castSucc j)) +
                (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) *
                  (((Module.finrank ℤ M : ℝ) - ((v (Fin.castSucc j)).val : ℝ)) /
                    (((v (Fin.succ j)).val : ℝ) - ((v (Fin.castSucc j)).val : ℝ))) ≤
              Real.log (ReverseMinkowski.determinant M))
    (j : Fin k) :
    @ExtremalPair n (vtxMinimizer hℒ v (Fin.castSucc j)) (vtxMinimizer hℒ v (Fin.succ j))
      (vtxMinimizer_discrete hℒ v (Fin.castSucc j)) (vtxMinimizer_discrete hℒ v (Fin.succ j)) := by
  classical
  let A : Submodule ℤ E := vtxMinimizer hℒ v (Fin.castSucc j)
  let B : Submodule ℤ E := vtxMinimizer hℒ v (Fin.succ j)
  haveI : DiscreteTopology ↥A := by dsimp [A]; exact vtxMinimizer_discrete hℒ v (Fin.castSucc j)
  haveI : DiscreteTopology ↥B := by dsimp [B]; exact vtxMinimizer_discrete hℒ v (Fin.succ j)
  let a : ℕ := (v (Fin.castSucc j)).val
  let b : ℕ := (v (Fin.succ j)).val
  have hABlt : a < b := by dsimp [a, b]; exact hinc j
  have hb0 : 0 < (b : ℝ) - (a : ℝ) := by
    have h' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hABlt
    linarith
  have hbnz : (b : ℝ) - (a : ℝ) ≠ 0 := ne_of_gt hb0
  intro M hdtM hAM hMB
  haveI : DiscreteTopology ↥M := hdtM
  have hMleℒ : M ≤ ℒ := le_trans hMB (vtxMinimizer_le hℒ v (Fin.succ j))
  -- rank between the vertex ranks
  let rA : ℕ := Module.finrank ℤ ↥A
  let rB : ℕ := Module.finrank ℤ ↥B
  let rM : ℕ := Module.finrank ℤ M
  have hrA : rA = a := by dsimp [rA, A, a]; exact vtxMinimizer_rank hℒ v (Fin.castSucc j)
  have hrB : rB = b := by dsimp [rB, B, b]; exact vtxMinimizer_rank hℒ v (Fin.succ j)
  have haM : a ≤ rM := by
    have hleF : Module.finrank ℤ ↥A ≤ Module.finrank ℤ M := by
      haveI : Module.Free ℤ ↥A := instModuleFree_of_discrete_submodule A
      haveI : Module.Finite ℤ ↥A := instModuleFinite_of_discrete_submodule A
      haveI : Module.Free ℤ ↥M := instModuleFree_of_discrete_submodule M
      haveI : Module.Finite ℤ ↥M := instModuleFinite_of_discrete_submodule M
      exact finrank_le_of_le (ℒ' := A) (ℒ := M) hAM
    dsimp [rM]
    rwa [← hrA]
  have hMb : rM ≤ b := by
    have hleF : Module.finrank ℤ ↥M ≤ Module.finrank ℤ ↥B := by
      haveI : Module.Free ℤ ↥B := instModuleFree_of_discrete_submodule B
      haveI : Module.Finite ℤ ↥B := instModuleFinite_of_discrete_submodule B
      haveI : Module.Free ℤ ↥M := instModuleFree_of_discrete_submodule M
      haveI : Module.Finite ℤ ↥M := instModuleFinite_of_discrete_submodule M
      exact finrank_le_of_le (ℒ' := M) (ℒ := B) hMB
    dsimp [rM]
    rwa [← hrB]
  -- segment bound at M
  have hseg' := hsegM j M hMleℒ haM hMb
  -- log facts
  let A₀ : ℝ := minLogSeq hℒ (v (Fin.castSucc j))
  let B₀ : ℝ := minLogSeq hℒ (v (Fin.succ j))
  let L : ℝ := Real.log (ReverseMinkowski.determinant M)
  have hA₀log : Real.log (@ReverseMinkowski.determinant n A (vtxMinimizer_discrete hℒ v (Fin.castSucc j))) = A₀ := by
    dsimp [A₀, A, vtxMinimizer]
    exact (minLogSeq_eq_log_vtxDet hℒ v (Fin.castSucc j)).symm
  have hB₀log : Real.log (@ReverseMinkowski.determinant n B (vtxMinimizer_discrete hℒ v (Fin.succ j))) = B₀ := by
    dsimp [B₀, B, vtxMinimizer]
    exact (minLogSeq_eq_log_vtxDet hℒ v (Fin.succ j)).symm
  have hmain : A₀ + (B₀ - A₀) * (((rM : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))) ≤ L := by
    dsimp [L, rM, a, b, A₀, B₀]
    exact hseg'
  -- multiply by (b - a) > 0
  have hcleared : (B₀ - A₀) * ((rM : ℝ) - (a : ℝ)) ≤ (b - a) * (L - A₀) := by
    have hsub : L - A₀ ≥ (B₀ - A₀) * (((rM : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))) := by
      linarith [hmain]
    have hmul := mul_le_mul_of_nonneg_left hsub (le_of_lt hb0)
    -- hmul : (b - a) * (L - A₀) ≥ (b-a) * ((B0-A0)*((rM-a)/(b-a)))
    have hx : (b : ℝ) - (a : ℝ) = (b : ℝ) - (a : ℝ) := rfl
    -- show (b-a)*((B0-A0)*((rM-a)/(b-a))) = (B0-A0)*(rM-a)
    have hsimpl : (b - a) * ((B₀ - A₀) * (((rM : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)))) =
        (B₀ - A₀) * ((rM : ℝ) - (a : ℝ)) := by
      calc
        (b - a) * ((B₀ - A₀) * (((rM : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))))
            = (B₀ - A₀) * ((b - a) * (((rM : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)))) := by ring
        _ = (B₀ - A₀) * ((rM : ℝ) - (a : ℝ)) := by rw [mul_div_cancel₀ ((rM : ℝ) - (a : ℝ)) hbnz]
    have hmul' : (B₀ - A₀) * ((rM : ℝ) - (a : ℝ)) ≤ (b - a) * (L - A₀) := by
      simpa [hsimpl] using hmul
    exact hmul'
  -- rewrite the vertex-log values in, i.e. LHS = (rB - rA)·(log det M − log det A)
  -- Goal: (rB - rA : ℝ)*(L - logA) ≥ (rM - rA : ℝ)*log (detB/detA)
  have hdetAnz : ReverseMinkowski.determinant A ≠ 0 := ne_of_gt (det_pos (L := A))
  have hdetBnz : ReverseMinkowski.determinant B ≠ 0 := ne_of_gt (det_pos (L := B))
  have hlogdiv : Real.log (ReverseMinkowski.determinant B / ReverseMinkowski.determinant A) =
      B₀ - A₀ := by
    rw [Real.log_div hdetBnz hdetAnz]
    -- log det B − log det A = B₀ − A₀
    have h1 : Real.log (ReverseMinkowski.determinant B) = B₀ := by
      have h2 := hB₀log
      -- det with the instance vtxMinimizer_discrete vs our instance (A/B-defeq): instance irrelevant
      simpa [B] using h2
    have h2 : Real.log (ReverseMinkowski.determinant A) = A₀ := by
      have h2' := hA₀log
      simpa [A] using h2'
    rw [h1, h2]
  have hlogM : Real.log (ReverseMinkowski.determinant M) - Real.log (ReverseMinkowski.determinant A) = L - A₀ := by
    have h1 : Real.log (ReverseMinkowski.determinant A) = A₀ := by
      have h2 := hA₀log
      simpa [A] using h2
    dsimp [L]
    rw [h1]
  -- Express hcleared in target form
  change (rB - rA : ℝ) * (Real.log (ReverseMinkowski.determinant M) - Real.log (ReverseMinkowski.determinant A)) ≥
      (rM - rA : ℝ) * Real.log (ReverseMinkowski.determinant B / ReverseMinkowski.determinant A)
  rw [hlogM, hlogdiv]
  -- now: (rB - rA)*(L - A₀) ≥ (rM - rA)*(B₀ - A₀); rA = a, rB = b
  have hrA' : (rA : ℝ) = (a : ℝ) := by rw [hrA]
  have hrB' : (rB : ℝ) = (b : ℝ) := by rw [hrB]
  rw [hrB', hrA']
  -- hcleared : (B₀ - A₀) * ((rM : ℝ) - (a : ℝ)) ≤ (b - a) * (L - A₀)
  -- goal: (b - a) * (L - A₀) ≥ (rM - a) * (B₀ - A₀)
  have hcleared' : (B₀ - A₀) * ((rM : ℝ) - (a : ℝ)) ≤ (b - a) * (L - A₀) := hcleared
  nlinarith

theorem canonical_chain {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ) :
    ∃ (k : ℕ) (v : Fin (k + 1) → Fin (n + 1)),
      v 0 = 0 ∧
      v ⟨k, Nat.lt_succ_self k⟩ = ⟨n, Nat.lt_succ_self n⟩ ∧
      (∀ j : Fin k, (v (Fin.castSucc j)).val < (v (Fin.succ j)).val) ∧
      (∀ (j : Fin k) (i : Fin (n + 1)),
        (v (Fin.castSucc j)).val ≤ i.val → i.val ≤ (v (Fin.succ j)).val →
          minLogSeq hℒ (v (Fin.castSucc j)) +
              (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) *
                ((i.val - (v (Fin.castSucc j)).val) / ((v (Fin.succ j)).val - (v (Fin.castSucc j)).val)) ≤
            minLogSeq hℒ i) ∧
      (∀ (j : Fin k) (hj : j.val + 1 < k),
        (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) /
            (((v (Fin.succ j)).val : ℝ) - ((v (Fin.castSucc j)).val : ℝ)) <
          (minLogSeq hℒ (v ⟨j.val + 2, by omega⟩) - minLogSeq hℒ (v (Fin.succ j))) /
            (((v ⟨j.val + 2, by omega⟩).val : ℝ) - ((v (Fin.succ j)).val : ℝ))) ∧
      (∀ j : Fin k, vtxMinimizer hℒ v (Fin.castSucc j) ≤ vtxMinimizer hℒ v (Fin.succ j)) := by
  classical
  rcases (Commons.Geometry.LowerHull.exists_lower_hull_chain (N := n) (y := minLogSeq hℒ)) with
    ⟨k, v, hv0, hvN, hinc, hseg, hslope⟩
  refine ⟨k, v, hv0, hvN, hinc, ?_, hslope, ?_⟩
  · exact hseg
  · exact vertex_nested_of_hull hℒ hv0 hvN hinc hseg hslope

/-- The vertex minimizer at the first vertex is the trivial lattice. -/
lemma vtxMinimizer_bot {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} {v : Fin (k + 1) → Fin (n + 1)} (hv0 : v 0 = 0) :
    vtxMinimizer hℒ v ⟨0, Nat.zero_lt_succ k⟩ = ⊥ := by
  classical
  have hfin : Module.finrank ℤ ↥(vtxMinimizer hℒ v ⟨0, Nat.zero_lt_succ k⟩) = 0 := by
    have h := vtxMinimizer_rank hℒ v ⟨0, Nat.zero_lt_succ k⟩
    have hv : (v ⟨0, Nat.zero_lt_succ k⟩).val = 0 := by simpa using congrArg Fin.val hv0
    rwa [hv] at h
  haveI : DiscreteTopology ↥(vtxMinimizer hℒ v ⟨0, Nat.zero_lt_succ k⟩) :=
    vtxMinimizer_discrete hℒ v ⟨0, Nat.zero_lt_succ k⟩
  exact eq_bot_of_finrank_zero hfin

/-- A `ℕ`-indexed chain from the vertices: `vtxChain v i` is the vertex minimizer of the
`min i k`-th vertex (constant `k`-vertex beyond the top). -/
noncomputable def vtxChain {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} (v : Fin (k + 1) → Fin (n + 1)) (i : ℕ) : Submodule ℤ E :=
  vtxMinimizer hℒ v ⟨min i k, by
    have h : min i k < k + 1 := Nat.lt_of_le_of_lt (Nat.min_le_right i k) (Nat.lt_succ_self k)
    exact h⟩

lemma vtxChain_of_le {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} (v : Fin (k + 1) → Fin (n + 1)) {i : ℕ} (hi : i ≤ k) :
    vtxChain hℒ v i = vtxMinimizer hℒ v ⟨i, Nat.lt_succ_iff.mpr hi⟩ := by
  classical
  dsimp [vtxChain]
  have hmin : min i k = i := by omega
  -- vtxMinimizer index: ⟨min i k, p⟩ vs ⟨i, q⟩ equal by Fin.ext (values min i k = i, proofs irrelevant)
  apply congrArg (fun t : Fin (k + 1) => vtxMinimizer hℒ v t)
  apply Fin.ext
  simp [hmin]

lemma vtxChain_bot {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} {v : Fin (k + 1) → Fin (n + 1)} (hv0 : v 0 = 0) :
    vtxChain hℒ v 0 = ⊥ := by
  have h := vtxChain_of_le hℒ v (k := k) (Nat.zero_le k)
  -- h : vtxChain v 0 = vtxMinimizer ⟨0, Nat.lt_succ_iff.mpr (Nat.zero_le k)⟩
  rw [h]
  exact vtxMinimizer_bot hℒ hv0

lemma vtxChain_top {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} {v : Fin (k + 1) → Fin (n + 1)}
    (hvN : v ⟨k, Nat.lt_succ_self k⟩ = ⟨n, Nat.lt_succ_self n⟩) :
    vtxChain hℒ v k = ℒ := by
  have h := vtxChain_of_le hℒ v (k := k) (le_refl k)
  -- h : vtxChain v k = vtxMinimizer ⟨k, Nat.lt_succ_iff.mpr (le_refl k)⟩
  rw [h]
  exact vtxMinimizer_top hℒ hvN

/-- Consecutive vertex minimizers in a hull chain are nested at the `ℕ`-chain level. -/
lemma vtxChain_step_le {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} {v : Fin (k + 1) → Fin (n + 1)}
    (hv0 : v 0 = 0) (hvN : v ⟨k, Nat.lt_succ_self k⟩ = ⟨n, Nat.lt_succ_self n⟩)
    (hinc : ∀ j : Fin k, (v (Fin.castSucc j)).val < (v (Fin.succ j)).val)
    (hseg : ∀ (j : Fin k) (i : Fin (n + 1)),
      (v (Fin.castSucc j)).val ≤ i.val → i.val ≤ (v (Fin.succ j)).val →
        minLogSeq hℒ (v (Fin.castSucc j)) +
            (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) *
              ((i.val - (v (Fin.castSucc j)).val) / ((v (Fin.succ j)).val - (v (Fin.castSucc j)).val)) ≤
          minLogSeq hℒ i)
    (hslope : ∀ (j : Fin k) (hj : j.val + 1 < k),
      (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) /
          ((v (Fin.succ j)).val - (v (Fin.castSucc j)).val) <
        (minLogSeq hℒ (v ⟨j.val + 2, by omega⟩) - minLogSeq hℒ (v (Fin.succ j))) /
          ((v ⟨j.val + 2, by omega⟩).val - (v (Fin.succ j)).val))
    {i : ℕ} (hi : i < k) :
    vtxChain hℒ v i ≤ vtxChain hℒ v (i + 1) := by
  classical
  have h1 := vtxChain_of_le hℒ v (i := i) (le_of_lt hi)
  have h2 := vtxChain_of_le hℒ v (i := i + 1) (Nat.succ_le_of_lt hi)
  rw [h1, h2]
  -- need vtxMinimizer ⟨i, _⟩ ≤ vtxMinimizer ⟨i+1, _⟩ from vertex_nested_of_hull at j = ⟨i, hi⟩
  have hnest := vertex_nested_of_hull hℒ hv0 hvN hinc hseg hslope
  have hstep := hnest ⟨i, hi⟩
  -- hstep : vtxMinimizer (Fin.castSucc ⟨i, hi⟩) ≤ vtxMinimizer (Fin.succ ⟨i, hi⟩)
  -- Fin.castSucc ⟨i, hi⟩ : Fin (k+1) with value i ; Fin.succ ⟨i,hi⟩ value i+1
  simpa using hstep

lemma hull_segM_of_seg {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} {v : Fin (k + 1) → Fin (n + 1)}
    (hseg : ∀ (j : Fin k) (i : Fin (n + 1)),
      (v (Fin.castSucc j)).val ≤ i.val → i.val ≤ (v (Fin.succ j)).val →
        minLogSeq hℒ (v (Fin.castSucc j)) +
            (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) *
              ((i.val - (v (Fin.castSucc j)).val) / ((v (Fin.succ j)).val - (v (Fin.castSucc j)).val)) ≤
          minLogSeq hℒ i)
    (j : Fin k) (M : Submodule ℤ E) [DiscreteTopology M] :
    M ≤ ℒ → (v (Fin.castSucc j)).val ≤ Module.finrank ℤ M →
      Module.finrank ℤ M ≤ (v (Fin.succ j)).val →
        minLogSeq hℒ (v (Fin.castSucc j)) +
            (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) *
              (((Module.finrank ℤ M : ℝ) - ((v (Fin.castSucc j)).val : ℝ)) /
                (((v (Fin.succ j)).val : ℝ) - ((v (Fin.castSucc j)).val : ℝ))) ≤
          Real.log (ReverseMinkowski.determinant M) := by
  classical
  intro hMle haM hMb
  have hrM' : Module.finrank ℤ M < n + 1 := by
    have hleF : Module.finrank ℤ M ≤ Module.finrank ℤ ℒ :=
      finrank_le_of_le (ℒ' := M) (ℒ := ℒ) hMle
    rw [fullrank_finrank ℒ hℒ] at hleF
    omega
  let i : Fin (n + 1) := ⟨Module.finrank ℤ M, hrM'⟩
  have hseg' := hseg j i (by simpa [i] using haM) (by simpa [i] using hMb)
  have h2 : minLogSeq hℒ i ≤ Real.log (ReverseMinkowski.determinant M) := by
    exact minLogSeq_le_log_det hℒ M hMle hrM'
  have hstep : minLogSeq hℒ (v (Fin.castSucc j)) +
        (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) *
          (((Module.finrank ℤ M : ℝ) - ((v (Fin.castSucc j)).val : ℝ)) /
            (((v (Fin.succ j)).val : ℝ) - ((v (Fin.castSucc j)).val : ℝ))) ≤
      minLogSeq hℒ i := by
    simpa [i] using hseg'
  exact le_trans hstep h2

/-- Consecutive vertex minimizers form an extremal pair (from the rank-indexed segment bound). -/
lemma extremal_vtx_consecutive_of_seg {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} {v : Fin (k + 1) → Fin (n + 1)}
    (hinc : ∀ j : Fin k, (v (Fin.castSucc j)).val < (v (Fin.succ j)).val)
    (hseg : ∀ (j : Fin k) (i : Fin (n + 1)),
      (v (Fin.castSucc j)).val ≤ i.val → i.val ≤ (v (Fin.succ j)).val →
        minLogSeq hℒ (v (Fin.castSucc j)) +
            (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) *
              ((i.val - (v (Fin.castSucc j)).val) / ((v (Fin.succ j)).val - (v (Fin.castSucc j)).val)) ≤
          minLogSeq hℒ i)
    (j : Fin k) :
    @ExtremalPair n (vtxMinimizer hℒ v (Fin.castSucc j)) (vtxMinimizer hℒ v (Fin.succ j))
      (vtxMinimizer_discrete hℒ v (Fin.castSucc j)) (vtxMinimizer_discrete hℒ v (Fin.succ j)) := by
  classical
  exact extremal_vtx_consecutive hℒ hinc (hull_segM_of_seg hℒ hseg) j

lemma vtxChain_discrete {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} (v : Fin (k + 1) → Fin (n + 1)) (i : ℕ) :
    DiscreteTopology ↥(vtxChain hℒ v i) := by
  classical
  dsimp [vtxChain]
  exact vtxMinimizer_discrete hℒ v ⟨min i k, by
    have h : min i k < k + 1 := Nat.lt_of_le_of_lt (Nat.min_le_right i k) (Nat.lt_succ_self k)
    exact h⟩

/-- The chain is inside `ℒ`. -/
lemma vtxChain_le {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} (v : Fin (k + 1) → Fin (n + 1)) (i : ℕ) :
    vtxChain hℒ v i ≤ ℒ := by
  classical
  dsimp [vtxChain]
  exact vtxMinimizer_le hℒ v ⟨min i k, by
    have h : min i k < k + 1 := Nat.lt_of_le_of_lt (Nat.min_le_right i k) (Nat.lt_succ_self k)
    exact h⟩

/-- The chain rank at `i ≤ k` is `(v i).val`. -/
lemma vtxChain_rank_of_le {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} (v : Fin (k + 1) → Fin (n + 1)) {i : ℕ} (hi : i ≤ k) :
    Module.finrank ℤ ↥(vtxChain hℒ v i) = (v ⟨i, Nat.lt_succ_iff.mpr hi⟩).val := by
  classical
  rw [vtxChain_of_le hℒ v hi]
  exact vtxMinimizer_rank hℒ v ⟨i, Nat.lt_succ_iff.mpr hi⟩

/-- Each chain step is primitive. -/
lemma vtxChain_primitive {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} {v : Fin (k + 1) → Fin (n + 1)}
    (hv0 : v 0 = 0) (hvN : v ⟨k, Nat.lt_succ_self k⟩ = ⟨n, Nat.lt_succ_self n⟩)
    (hinc : ∀ j : Fin k, (v (Fin.castSucc j)).val < (v (Fin.succ j)).val)
    (hseg : ∀ (j : Fin k) (i : Fin (n + 1)),
      (v (Fin.castSucc j)).val ≤ i.val → i.val ≤ (v (Fin.succ j)).val →
        minLogSeq hℒ (v (Fin.castSucc j)) +
            (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) *
              ((i.val - (v (Fin.castSucc j)).val) / ((v (Fin.succ j)).val - (v (Fin.castSucc j)).val)) ≤
          minLogSeq hℒ i)
    (hslope : ∀ (j : Fin k) (hj : j.val + 1 < k),
      (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) /
          ((v (Fin.succ j)).val - (v (Fin.castSucc j)).val) <
        (minLogSeq hℒ (v ⟨j.val + 2, by omega⟩) - minLogSeq hℒ (v (Fin.succ j))) /
          ((v ⟨j.val + 2, by omega⟩).val - (v (Fin.succ j)).val))
    {i : ℕ} (hi : i < k) : Primitive (vtxChain hℒ v i) (vtxChain hℒ v (i + 1)) := by
  classical
  let L0 : Submodule ℤ E := vtxMinimizer hℒ v ⟨i, Nat.lt_succ_iff.mpr (le_of_lt hi)⟩
  let L1 : Submodule ℤ E := vtxMinimizer hℒ v ⟨i + 1, Nat.lt_succ_iff.mpr (Nat.succ_le_of_lt hi)⟩
  have h1 : vtxChain hℒ v i = L0 := by
    dsimp [L0]
    exact vtxChain_of_le hℒ v (i := i) (le_of_lt hi)
  have h2 : vtxChain hℒ v (i + 1) = L1 := by
    dsimp [L1]
    exact vtxChain_of_le hℒ v (i := i + 1) (Nat.succ_le_of_lt hi)
  rw [h1, h2]
  change Primitive L0 L1
  have hp : Primitive L0 ℒ := by
    dsimp [L0, vtxMinimizer]
    exact detMinimizer_primitive hℒ (r := (v ⟨i, Nat.lt_succ_iff.mpr (le_of_lt hi)⟩).val)
      (vtx_rank_le hℒ v ⟨i, Nat.lt_succ_iff.mpr (le_of_lt hi)⟩)
  have hL1le : L1 ≤ ℒ := by
    dsimp [L1]
    exact vtxMinimizer_le hℒ v ⟨i + 1, Nat.lt_succ_iff.mpr (Nat.succ_le_of_lt hi)⟩
  have hL0L1 : L0 ≤ L1 := by
    have hnest := vertex_nested_of_hull hℒ hv0 hvN hinc hseg hslope
    have hstep := hnest ⟨i, hi⟩
    dsimp [L0, L1]
    simpa using hstep
  exact primitive_of_le hp hL1le hL0L1


/-- Extremal pair for a canonical chain step. -/
lemma vtxChain_extremal {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} {v : Fin (k + 1) → Fin (n + 1)}
    (hinc : ∀ j : Fin k, (v (Fin.castSucc j)).val < (v (Fin.succ j)).val)
    (hseg : ∀ (j : Fin k) (i : Fin (n + 1)),
      (v (Fin.castSucc j)).val ≤ i.val → i.val ≤ (v (Fin.succ j)).val →
        minLogSeq hℒ (v (Fin.castSucc j)) +
            (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) *
              ((i.val - (v (Fin.castSucc j)).val) / ((v (Fin.succ j)).val - (v (Fin.castSucc j)).val)) ≤
          minLogSeq hℒ i)
    {i : ℕ} (hi : i < k) :
    @ExtremalPair n (vtxChain hℒ v i) (vtxChain hℒ v (i + 1))
      (vtxChain_discrete hℒ v i) (vtxChain_discrete hℒ v (i + 1)) := by
  classical
  let L0 : Submodule ℤ E := vtxMinimizer hℒ v ⟨i, Nat.lt_succ_iff.mpr (le_of_lt hi)⟩
  let L1 : Submodule ℤ E := vtxMinimizer hℒ v ⟨i + 1, Nat.lt_succ_iff.mpr (Nat.succ_le_of_lt hi)⟩
  have h1 : vtxChain hℒ v i = L0 := by
    dsimp [L0]
    exact vtxChain_of_le hℒ v (i := i) (le_of_lt hi)
  have h2 : vtxChain hℒ v (i + 1) = L1 := by
    dsimp [L1]
    exact vtxChain_of_le hℒ v (i := i + 1) (Nat.succ_le_of_lt hi)
  have hEx : @ExtremalPair n L0 L1
      (vtxMinimizer_discrete hℒ v ⟨i, Nat.lt_succ_iff.mpr (le_of_lt hi)⟩)
      (vtxMinimizer_discrete hℒ v ⟨i + 1, Nat.lt_succ_iff.mpr (Nat.succ_le_of_lt hi)⟩) := by
    dsimp [L0, L1]
    exact extremal_vtx_consecutive_of_seg hℒ hinc hseg ⟨i, hi⟩
  -- goal : @ExtremalPair n (vtxChain hℒ v i) (vtxChain hℒ v (i+1)) (vtxChain_discrete...) (vtxChain_discrete...)
  haveI : DiscreteTopology ↥(vtxChain hℒ v i) := vtxChain_discrete hℒ v i
  haveI : DiscreteTopology ↥(vtxChain hℒ v (i + 1)) := vtxChain_discrete hℒ v (i + 1)
  -- rewrite the endpoints through h1, h2 by proving the unfolded statement
  change ∀ M : Submodule ℤ E, [DiscreteTopology M] → vtxChain hℒ v i ≤ M → M ≤ vtxChain hℒ v (i + 1) →
    (Module.finrank ℤ ↥(vtxChain hℒ v (i + 1)) - Module.finrank ℤ ↥(vtxChain hℒ v i) : ℝ) *
        (Real.log (ReverseMinkowski.determinant M) - Real.log (ReverseMinkowski.determinant (vtxChain hℒ v i))) ≥
      (Module.finrank ℤ M - Module.finrank ℤ ↥(vtxChain hℒ v i) : ℝ) *
        Real.log (ReverseMinkowski.determinant (vtxChain hℒ v (i + 1)) /
          ReverseMinkowski.determinant (vtxChain hℒ v i))
  intro M hdtM hAM hMB
  haveI : DiscreteTopology ↥M := hdtM
  have hExM := hEx M
  -- hExM : L0 ≤ M → M ≤ L1 → ineq(L0, L1 terms)
  have hAM' : L0 ≤ M := by simpa [h1] using hAM
  have hMB' : M ≤ L1 := by simpa [h2] using hMB
  -- conclusion: replace chain by minimizers in ranks/dets
  have hf0 : Module.finrank ℤ ↥(vtxChain hℒ v i) = Module.finrank ℤ ↥L0 := finrank_eq_of_eq h1
  have hf1 : Module.finrank ℤ ↥(vtxChain hℒ v (i + 1)) = Module.finrank ℤ ↥L1 := finrank_eq_of_eq h2
  haveI : DiscreteTopology ↥L0 := by
    dsimp [L0]
    exact vtxMinimizer_discrete hℒ v ⟨i, Nat.lt_succ_iff.mpr (le_of_lt hi)⟩
  haveI : DiscreteTopology ↥L1 := by
    dsimp [L1]
    exact vtxMinimizer_discrete hℒ v ⟨i + 1, Nat.lt_succ_iff.mpr (Nat.succ_le_of_lt hi)⟩
  have hd0 : ReverseMinkowski.determinant (vtxChain hℒ v i) = ReverseMinkowski.determinant L0 := by
    exact det_eq_of_eq (L₁ := vtxChain hℒ v i) (L₂ := L0) h1
  have hd1 : ReverseMinkowski.determinant (vtxChain hℒ v (i + 1)) = ReverseMinkowski.determinant L1 := by
    exact det_eq_of_eq (L₁ := vtxChain hℒ v (i + 1)) (L₂ := L1) h2
  -- hExM hAM hMB : (finrank L1 − finrank L0 : ℝ)·(log det M − log det L0) ≥ (finrank M − finrank L0 : ℝ)·log(det L1/det L0)
  have hfin := hExM hAM' hMB'
  -- rewrite the chain-goal using these equalities
  rw [hf0, hf1, hd0, hd1]
  exact hfin

lemma detMinimizer_bot_of_zero {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {hr : 0 ≤ Module.finrank ℤ ℒ} : detMinimizer hℒ 0 hr = ⊥ := by
  classical
  have hfin : Module.finrank ℤ ↥(detMinimizer hℒ 0 hr) = 0 := detMinimizer_rank hℒ (r := 0) hr
  haveI : DiscreteTopology ↥(detMinimizer hℒ 0 hr) := detMinimizer_discrete hℒ (r := 0) hr
  exact eq_bot_of_finrank_zero hfin

/-- `minLogSeq` at the zero rank is `log 1 = 0`. -/
lemma minLogSeq_zero {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ) :
    minLogSeq hℒ (0 : Fin (n + 1)) = 0 := by
  classical
  dsimp [minLogSeq, minLogDet]
  let p : 0 ≤ Module.finrank ℤ ℒ := by have hfin : Module.finrank ℤ ℒ = n := fullrank_finrank ℒ hℒ; omega
  change Real.log (@ReverseMinkowski.determinant n (detMinimizer hℒ 0 p) (detMinimizer_discrete hℒ (r := 0) p)) = 0
  have hbot : detMinimizer hℒ 0 p = ⊥ := detMinimizer_bot_of_zero hℒ
  have hd : @ReverseMinkowski.determinant n (detMinimizer hℒ 0 p) (detMinimizer_discrete hℒ (r := 0) p) =
      @ReverseMinkowski.determinant n (⊥ : Submodule ℤ E) (by infer_instance) := by
    exact @det_eq_of_eq n (detMinimizer hℒ 0 p) (⊥ : Submodule ℤ E)
      (detMinimizer_discrete hℒ (r := 0) p) (by infer_instance) hbot
  rw [hd]
  simp [det_bot]

/-- Generic: a strictly increasing ℕ-sequence satisfies `S 0 ≤ S i` for `i < k`. -/
lemma strict_inc_seq_le {k : ℕ} (S : ℕ → ℝ) (hinc : ∀ i : ℕ, i + 1 < k → S i < S (i + 1)) :
    ∀ (i : ℕ), i < k → S 0 ≤ S i := by
  intro i hi
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
      have hi' : i < k := by omega
      have h1 : S 0 ≤ S i := ih hi'
      have h2 : S i ≤ S (i + 1) := le_of_lt (hinc i hi)
      exact le_trans h1 h2

/-- The slope of the `i`-th segment of the vertex chain (between vertices `i` and `i+1`). -/
noncomputable def segSlope {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} (v : Fin (k + 1) → Fin (n + 1)) (i : ℕ) : ℝ :=
  if hi : i < k then
    (minLogSeq hℒ (v ⟨i + 1, by omega⟩) - minLogSeq hℒ (v ⟨i, by omega⟩)) /
      (((v ⟨i + 1, by omega⟩).val : ℝ) - ((v ⟨i, by omega⟩).val : ℝ))
  else 0

/-- The chain slopes strictly increase (ℕ-form of the hull-slope property). -/
lemma segSlope_inc {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} {v : Fin (k + 1) → Fin (n + 1)}
    (hslope : ∀ (j : Fin k) (hj : j.val + 1 < k),
      (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) /
          (((v (Fin.succ j)).val : ℝ) - ((v (Fin.castSucc j)).val : ℝ)) <
        (minLogSeq hℒ (v ⟨j.val + 2, by omega⟩) - minLogSeq hℒ (v (Fin.succ j))) /
          (((v ⟨j.val + 2, by omega⟩).val : ℝ) - ((v (Fin.succ j)).val : ℝ)))
    (i : ℕ) (hi : i + 1 < k) : segSlope hℒ v i < segSlope hℒ v (i + 1) := by
  classical
  dsimp [segSlope]
  have hi0 : i < k := by omega
  rw [dif_pos hi0, dif_pos hi]
  have h := hslope ⟨i, hi0⟩ hi
  simpa using h

/-- All chain slopes are nonnegative under the subdet hypothesis (slopes strictly increase
from a nonnegative first slope). -/
lemma segSlope_nonneg {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} {v : Fin (k + 1) → Fin (n + 1)}
    (hv0 : v 0 = 0) (hinc : ∀ j : Fin k, (v (Fin.castSucc j)).val < (v (Fin.succ j)).val)
    (hslope : ∀ (j : Fin k) (hj : j.val + 1 < k),
      (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) /
          (((v (Fin.succ j)).val : ℝ) - ((v (Fin.castSucc j)).val : ℝ)) <
        (minLogSeq hℒ (v ⟨j.val + 2, by omega⟩) - minLogSeq hℒ (v (Fin.succ j))) /
          (((v ⟨j.val + 2, by omega⟩).val : ℝ) - ((v (Fin.succ j)).val : ℝ)))
    (hdet : ∀ (M : Submodule ℤ E), [DiscreteTopology M] → M ≤ ℒ → (1 : ℝ) ≤ ReverseMinkowski.determinant M)
    {i : ℕ} (hi : i < k) : 0 ≤ segSlope hℒ v i := by
  classical
  by_cases hk0 : k = 0
  · omega
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    let j0 : Fin (k + 1) := ⟨0, by omega⟩
    let j1 : Fin (k + 1) := ⟨1, by omega⟩
    have hs0 : 0 ≤ segSlope hℒ v 0 := by
      dsimp [segSlope]
      rw [dif_pos hkpos]
      have hnum : 0 ≤ minLogSeq hℒ (v j1) - minLogSeq hℒ (v j0) := by
        haveI : DiscreteTopology ↥(vtxMinimizer hℒ v j1) := vtxMinimizer_discrete hℒ v j1
        have hEq1 : minLogSeq hℒ (v j1) =
            Real.log (@ReverseMinkowski.determinant n (vtxMinimizer hℒ v j1)
              (vtxMinimizer_discrete hℒ v j1)) := by
          exact minLogSeq_eq_log_vtxDet hℒ v j1
        have hd1 : (1 : ℝ) ≤ @ReverseMinkowski.determinant n (vtxMinimizer hℒ v j1)
              (vtxMinimizer_discrete hℒ v j1) := by
          exact hdet (vtxMinimizer hℒ v j1) (vtxMinimizer_le hℒ v j1)
        have hpos1 : 0 < @ReverseMinkowski.determinant n (vtxMinimizer hℒ v j1)
              (vtxMinimizer_discrete hℒ v j1) := by
          exact det_pos (L := vtxMinimizer hℒ v j1)
        have hlog1 : 0 ≤ Real.log (@ReverseMinkowski.determinant n (vtxMinimizer hℒ v j1)
              (vtxMinimizer_discrete hℒ v j1)) := by
          exact (Real.log_nonneg_iff hpos1).2 hd1
        have h1 : 0 ≤ minLogSeq hℒ (v j1) := by
          rw [hEq1]
          exact hlog1
        have hEq0 : minLogSeq hℒ (v j0) = 0 := by
          have hv : (v j0 : Fin (n + 1)) = (0 : Fin (n + 1)) := by
            dsimp [j0]
            simpa using hv0
          rw [hv]
          exact minLogSeq_zero hℒ
        linarith
      have hden : 0 < ((v j1).val : ℝ) - ((v j0).val : ℝ) := by
        have hlt := hinc ⟨0, hkpos⟩
        have hc : (v (Fin.castSucc ⟨0, hkpos⟩)).val = (v j0).val := by
          dsimp [j0]
        have hs : (v (Fin.succ ⟨0, hkpos⟩)).val = (v j1).val := by
          dsimp [j1]
        rw [hc, hs] at hlt
        have hlt' : ((v j0).val : ℝ) < ((v j1).val : ℝ) := by exact_mod_cast hlt
        linarith
      exact div_nonneg hnum (le_of_lt hden)
    have hmono : segSlope hℒ v 0 ≤ segSlope hℒ v i := by
      exact strict_inc_seq_le (segSlope hℒ v) (fun t ht => segSlope_inc hℒ hslope t ht) i hi
    linarith

noncomputable def canonScale {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} {v : Fin (k + 1) → Fin (n + 1)}
    (hv0 : v 0 = 0) (hvN : v ⟨k, Nat.lt_succ_self k⟩ = ⟨n, Nat.lt_succ_self n⟩)
    (hinc : ∀ j : Fin k, (v (Fin.castSucc j)).val < (v (Fin.succ j)).val)
    (hseg : ∀ (j : Fin k) (i : Fin (n + 1)),
      (v (Fin.castSucc j)).val ≤ i.val → i.val ≤ (v (Fin.succ j)).val →
        minLogSeq hℒ (v (Fin.castSucc j)) +
            (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) *
              ((i.val - (v (Fin.castSucc j)).val) / ((v (Fin.succ j)).val - (v (Fin.castSucc j)).val)) ≤
          minLogSeq hℒ i)
    (hslope : ∀ (j : Fin k) (hj : j.val + 1 < k),
      (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) /
          (((v (Fin.succ j)).val : ℝ) - ((v (Fin.castSucc j)).val : ℝ)) <
        (minLogSeq hℒ (v ⟨j.val + 2, by omega⟩) - minLogSeq hℒ (v (Fin.succ j))) /
          (((v ⟨j.val + 2, by omega⟩).val : ℝ) - ((v (Fin.succ j)).val : ℝ)))
    (i : ℕ) : ℝ :=
  if hi : i < k then
    @quotScale n (vtxChain hℒ v i) (vtxChain hℒ v (i + 1))
      (vtxChain_discrete hℒ v i) (vtxChain_discrete hℒ v (i + 1)) (by
        haveI : DiscreteTopology ↥(vtxChain hℒ v (i + 1)) := vtxChain_discrete hℒ v (i + 1)
        haveI : DiscreteTopology ↥(vtxChain hℒ v i) := vtxChain_discrete hℒ v i
        exact discrete_quotLattice (ℒ' := vtxChain hℒ v i) (ℒ := vtxChain hℒ v (i + 1))
          (realSpan (vtxChain hℒ v i)) rfl (vtxChain_primitive hℒ hv0 hvN hinc hseg hslope hi))
  else 1

/-- Canonical scale at a step below `k` is the quotient scale of the consecutive minimizers. -/
lemma canonScale_eq {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} {v : Fin (k + 1) → Fin (n + 1)}
    (hv0 : v 0 = 0) (hvN : v ⟨k, Nat.lt_succ_self k⟩ = ⟨n, Nat.lt_succ_self n⟩)
    (hinc : ∀ j : Fin k, (v (Fin.castSucc j)).val < (v (Fin.succ j)).val)
    (hseg : ∀ (j : Fin k) (i : Fin (n + 1)),
      (v (Fin.castSucc j)).val ≤ i.val → i.val ≤ (v (Fin.succ j)).val →
        minLogSeq hℒ (v (Fin.castSucc j)) +
            (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) *
              ((i.val - (v (Fin.castSucc j)).val) / ((v (Fin.succ j)).val - (v (Fin.castSucc j)).val)) ≤
          minLogSeq hℒ i)
    (hslope : ∀ (j : Fin k) (hj : j.val + 1 < k),
      (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) /
          (((v (Fin.succ j)).val : ℝ) - ((v (Fin.castSucc j)).val : ℝ)) <
        (minLogSeq hℒ (v ⟨j.val + 2, by omega⟩) - minLogSeq hℒ (v (Fin.succ j))) /
          (((v ⟨j.val + 2, by omega⟩).val : ℝ) - ((v (Fin.succ j)).val : ℝ)))
    {i : ℕ} (hi : i < k) :
    canonScale hℒ hv0 hvN hinc hseg hslope i =
      @quotScale n (vtxChain hℒ v i) (vtxChain hℒ v (i + 1))
        (vtxChain_discrete hℒ v i) (vtxChain_discrete hℒ v (i + 1)) (by
          haveI : DiscreteTopology ↥(vtxChain hℒ v (i + 1)) := vtxChain_discrete hℒ v (i + 1)
          haveI : DiscreteTopology ↥(vtxChain hℒ v i) := vtxChain_discrete hℒ v i
          exact discrete_quotLattice (ℒ' := vtxChain hℒ v i) (ℒ := vtxChain hℒ v (i + 1))
            (realSpan (vtxChain hℒ v i)) rfl (vtxChain_primitive hℒ hv0 hvN hinc hseg hslope hi)) := by
  classical
  dsimp [canonScale]
  rw [dif_pos hi]

/-- Canonical scale at each step is positive. -/
lemma canonScale_pos {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} {v : Fin (k + 1) → Fin (n + 1)}
    (hv0 : v 0 = 0) (hvN : v ⟨k, Nat.lt_succ_self k⟩ = ⟨n, Nat.lt_succ_self n⟩)
    (hinc : ∀ j : Fin k, (v (Fin.castSucc j)).val < (v (Fin.succ j)).val)
    (hseg : ∀ (j : Fin k) (i : Fin (n + 1)),
      (v (Fin.castSucc j)).val ≤ i.val → i.val ≤ (v (Fin.succ j)).val →
        minLogSeq hℒ (v (Fin.castSucc j)) +
            (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) *
              ((i.val - (v (Fin.castSucc j)).val) / ((v (Fin.succ j)).val - (v (Fin.castSucc j)).val)) ≤
          minLogSeq hℒ i)
    (hslope : ∀ (j : Fin k) (hj : j.val + 1 < k),
      (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) /
          (((v (Fin.succ j)).val : ℝ) - ((v (Fin.castSucc j)).val : ℝ)) <
        (minLogSeq hℒ (v ⟨j.val + 2, by omega⟩) - minLogSeq hℒ (v (Fin.succ j))) /
          (((v ⟨j.val + 2, by omega⟩).val : ℝ) - ((v (Fin.succ j)).val : ℝ)))
    {i : ℕ} (hi : i < k) : 0 < canonScale hℒ hv0 hvN hinc hseg hslope i := by
  classical
  rw [canonScale_eq hℒ hv0 hvN hinc hseg hslope hi]
  dsimp [quotScale]
  exact Real.exp_pos _

lemma quotLog_eq_slope_num {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} {v : Fin (k + 1) → Fin (n + 1)}
    (hv0 : v 0 = 0) (hvN : v ⟨k, Nat.lt_succ_self k⟩ = ⟨n, Nat.lt_succ_self n⟩)
    (hinc : ∀ j : Fin k, (v (Fin.castSucc j)).val < (v (Fin.succ j)).val)
    (hseg : ∀ (j : Fin k) (i : Fin (n + 1)),
      (v (Fin.castSucc j)).val ≤ i.val → i.val ≤ (v (Fin.succ j)).val →
        minLogSeq hℒ (v (Fin.castSucc j)) +
            (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) *
              ((i.val - (v (Fin.castSucc j)).val) / ((v (Fin.succ j)).val - (v (Fin.castSucc j)).val)) ≤
          minLogSeq hℒ i)
    (hslope : ∀ (j : Fin k) (hj : j.val + 1 < k),
      (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) /
          (((v (Fin.succ j)).val : ℝ) - ((v (Fin.castSucc j)).val : ℝ)) <
        (minLogSeq hℒ (v ⟨j.val + 2, by omega⟩) - minLogSeq hℒ (v (Fin.succ j))) /
          (((v ⟨j.val + 2, by omega⟩).val : ℝ) - ((v (Fin.succ j)).val : ℝ)))
    {i : ℕ} (hi : i < k)
    (hqDT : DiscreteTopology ↥(quotLattice (vtxChain hℒ v (i + 1)) (realSpan (vtxChain hℒ v i)))) :
    Real.log (@ReverseMinkowski.determinant n
      (quotLattice (vtxChain hℒ v (i + 1)) (realSpan (vtxChain hℒ v i))) hqDT) =
      minLogSeq hℒ (v ⟨i + 1, by omega⟩) - minLogSeq hℒ (v ⟨i, by omega⟩) := by
  classical
  have hL0 := vtxChain_of_le hℒ v (i := i) (le_of_lt hi)
  have hL1 := vtxChain_of_le hℒ v (i := i + 1) (Nat.succ_le_of_lt hi)
  let L0 : Submodule ℤ E := vtxMinimizer hℒ v ⟨i, Nat.lt_succ_iff.mpr (le_of_lt hi)⟩
  let L1 : Submodule ℤ E := vtxMinimizer hℒ v ⟨i + 1, Nat.lt_succ_iff.mpr (Nat.succ_le_of_lt hi)⟩
  haveI : DiscreteTopology ↥L0 := by dsimp [L0]; exact vtxMinimizer_discrete hℒ v ⟨i, Nat.lt_succ_iff.mpr (le_of_lt hi)⟩
  haveI : DiscreteTopology ↥L1 := by dsimp [L1]; exact vtxMinimizer_discrete hℒ v ⟨i + 1, Nat.lt_succ_iff.mpr (Nat.succ_le_of_lt hi)⟩
  have hprim : Primitive L0 L1 := by
    have hp := vtxChain_primitive hℒ hv0 hvN hinc hseg hslope hi
    rwa [hL0, hL1] at hp
  haveI : DiscreteTopology ↥(quotLattice L1 (realSpan L0)) := by
    exact discrete_quotLattice (ℒ' := L0) (ℒ := L1) (realSpan L0) rfl hprim
  -- step 1: rewrite the quotient lattice on the LHS via chain equalities
  have hQ : quotLattice (vtxChain hℒ v (i + 1)) (realSpan (vtxChain hℒ v i)) =
      quotLattice L1 (realSpan L0) := by
    have hR : realSpan (vtxChain hℒ v i) = realSpan L0 := by
      rw [hL0]
    rw [hL1, hR]
  have hdetQ : ReverseMinkowski.determinant (quotLattice L1 (realSpan L0)) =
      ReverseMinkowski.determinant L1 / ReverseMinkowski.determinant L0 := by
    exact Submission.SubLattice.determinant_quot_generic (nA := n) (ℒ' := L0) (ℒ := L1) (realSpan L0) rfl hprim
  have hpos0 : ReverseMinkowski.determinant L0 ≠ 0 := ne_of_gt (det_pos (L := L0))
  have hpos1 : ReverseMinkowski.determinant L1 ≠ 0 := ne_of_gt (det_pos (L := L1))
  haveI hq0 : DiscreteTopology ↥(quotLattice L1 (realSpan L0)) := by
    exact discrete_quotLattice (ℒ' := L0) (ℒ := L1) (realSpan L0) rfl hprim
  have hlogQ : Real.log (@ReverseMinkowski.determinant n (quotLattice L1 (realSpan L0)) hq0) =
      Real.log (ReverseMinkowski.determinant L1) - Real.log (ReverseMinkowski.determinant L0) := by
    rw [hdetQ]
    exact Real.log_div hpos1 hpos0
  have hlg0 : Real.log (ReverseMinkowski.determinant L0) = minLogSeq hℒ (v ⟨i, Nat.lt_succ_iff.mpr (le_of_lt hi)⟩) := by
    dsimp [L0]
    exact minLogSeq_eq_log_vtxDet hℒ v ⟨i, Nat.lt_succ_iff.mpr (le_of_lt hi)⟩
  have hlg1 : Real.log (ReverseMinkowski.determinant L1) = minLogSeq hℒ (v ⟨i + 1, Nat.lt_succ_iff.mpr (Nat.succ_le_of_lt hi)⟩) := by
    dsimp [L1]
    exact minLogSeq_eq_log_vtxDet hℒ v ⟨i + 1, Nat.lt_succ_iff.mpr (Nat.succ_le_of_lt hi)⟩
  have hdq : @ReverseMinkowski.determinant n (quotLattice (vtxChain hℒ v (i + 1)) (realSpan (vtxChain hℒ v i))) hqDT =
      @ReverseMinkowski.determinant n (quotLattice L1 (realSpan L0)) hq0 := by
    exact @det_eq_of_eq n (quotLattice (vtxChain hℒ v (i + 1)) (realSpan (vtxChain hℒ v i)))
      (quotLattice L1 (realSpan L0)) hqDT hq0 hQ
  rw [hdq]
  have hmain : Real.log (@ReverseMinkowski.determinant n (quotLattice L1 (realSpan L0)) hq0) =
      minLogSeq hℒ (v ⟨i + 1, Nat.lt_succ_iff.mpr (Nat.succ_le_of_lt hi)⟩) -
        minLogSeq hℒ (v ⟨i, Nat.lt_succ_iff.mpr (le_of_lt hi)⟩) := by
    rw [hlogQ, hlg1, hlg0]
  rw [← (show (v ⟨i + 1, Nat.lt_succ_iff.mpr (Nat.succ_le_of_lt hi)⟩) = v ⟨i + 1, by omega⟩ from rfl)]
  rw [← (show (v ⟨i, Nat.lt_succ_iff.mpr (le_of_lt hi)⟩) = v ⟨i, by omega⟩ from rfl)]
  exact hmain

/-- The canonical scale of a chain step is at most one (chain slopes are nonnegative). -/
lemma canonScale_le_one {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {k : ℕ} {v : Fin (k + 1) → Fin (n + 1)}
    (hv0 : v 0 = 0) (hvN : v ⟨k, Nat.lt_succ_self k⟩ = ⟨n, Nat.lt_succ_self n⟩)
    (hinc : ∀ j : Fin k, (v (Fin.castSucc j)).val < (v (Fin.succ j)).val)
    (hseg : ∀ (j : Fin k) (i : Fin (n + 1)),
      (v (Fin.castSucc j)).val ≤ i.val → i.val ≤ (v (Fin.succ j)).val →
        minLogSeq hℒ (v (Fin.castSucc j)) +
            (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) *
              ((i.val - (v (Fin.castSucc j)).val) / ((v (Fin.succ j)).val - (v (Fin.castSucc j)).val)) ≤
          minLogSeq hℒ i)
    (hslope : ∀ (j : Fin k) (hj : j.val + 1 < k),
      (minLogSeq hℒ (v (Fin.succ j)) - minLogSeq hℒ (v (Fin.castSucc j))) /
          (((v (Fin.succ j)).val : ℝ) - ((v (Fin.castSucc j)).val : ℝ)) <
        (minLogSeq hℒ (v ⟨j.val + 2, by omega⟩) - minLogSeq hℒ (v (Fin.succ j))) /
          (((v ⟨j.val + 2, by omega⟩).val : ℝ) - ((v (Fin.succ j)).val : ℝ)))
    (hdet : ∀ (M : Submodule ℤ E), [DiscreteTopology M] → M ≤ ℒ → (1 : ℝ) ≤ ReverseMinkowski.determinant M)
    {i : ℕ} (hi : i < k) : canonScale hℒ hv0 hvN hinc hseg hslope i ≤ 1 := by
  classical
  rw [canonScale_eq hℒ hv0 hvN hinc hseg hslope hi]
  dsimp [quotScale]
  rw [Real.exp_le_one_iff]
  let Q : Submodule ℤ E := quotLattice (vtxChain hℒ v (i + 1)) (realSpan (vtxChain hℒ v i))
  have hq : DiscreteTopology Q := by
    dsimp [Q]
    haveI : DiscreteTopology ↥(vtxChain hℒ v (i + 1)) := vtxChain_discrete hℒ v (i + 1)
    haveI : DiscreteTopology ↥(vtxChain hℒ v i) := vtxChain_discrete hℒ v i
    exact discrete_quotLattice (ℒ' := vtxChain hℒ v i) (ℒ := vtxChain hℒ v (i + 1))
      (realSpan (vtxChain hℒ v i)) rfl (vtxChain_primitive hℒ hv0 hvN hinc hseg hslope hi)
  let r : ℝ := (Module.finrank ℤ ↥(vtxChain hℒ v (i + 1)) - Module.finrank ℤ ↥(vtxChain hℒ v i) : ℝ)
  change -(Real.log (@ReverseMinkowski.determinant n Q hq)) / r ≤ 0
  have hr0 : 0 < r := by
    dsimp [r]
    -- finrank(vtxChain(i+1)) > finrank(vtxChain i)
    have h1 : Module.finrank ℤ ↥(vtxChain hℒ v (i + 1)) = (v ⟨i + 1, by omega⟩).val := by
      exact vtxChain_rank_of_le hℒ v (Nat.succ_le_of_lt hi)
    have h0 : Module.finrank ℤ ↥(vtxChain hℒ v i) = (v ⟨i, by omega⟩).val := by
      exact vtxChain_rank_of_le hℒ v (le_of_lt hi)
    have hlt : (v ⟨i, by omega⟩).val < (v ⟨i + 1, by omega⟩).val := by
      have hlt' := hinc ⟨i, hi⟩
      -- hlt' : (v (castSucc ⟨i,hi⟩)).val < (v (succ ⟨i,hi⟩)).val
      simpa using hlt'
    rw [h1, h0]
    have hc : ((v ⟨i + 1, by omega⟩).val : ℝ) - ((v ⟨i, by omega⟩).val : ℝ) > 0 := by
      have hc' : ((v ⟨i, by omega⟩).val : ℝ) < ((v ⟨i + 1, by omega⟩).val : ℝ) := by exact_mod_cast hlt
      linarith
    exact hc
  -- log det Q = numerator of the chain slope, and slope ≥ 0
  have hlog : Real.log (@ReverseMinkowski.determinant n Q hq) =
      minLogSeq hℒ (v ⟨i + 1, by omega⟩) - minLogSeq hℒ (v ⟨i, by omega⟩) := by
    dsimp [Q]
    exact quotLog_eq_slope_num hℒ hv0 hvN hinc hseg hslope hi hq
  have hsl0 : 0 ≤ segSlope hℒ v i := segSlope_nonneg hℒ hv0 hinc hslope hdet hi
  let num : ℝ := minLogSeq hℒ (v ⟨i + 1, by omega⟩) - minLogSeq hℒ (v ⟨i, by omega⟩)
  let den : ℝ := ((v ⟨i + 1, by omega⟩).val : ℝ) - ((v ⟨i, by omega⟩).val : ℝ)
  have hnum : 0 ≤ num := by
    have hsl0' : 0 ≤ num / den := by
      dsimp [num, den, segSlope] at hsl0 ⊢
      rwa [dif_pos hi] at hsl0
    have hden : 0 < den := by
      dsimp [den]
      have hlt : (v ⟨i, by omega⟩).val < (v ⟨i + 1, by omega⟩).val := by
        have hlt' := hinc ⟨i, hi⟩
        simpa using hlt'
      have hc' : ((v ⟨i, by omega⟩).val : ℝ) < ((v ⟨i + 1, by omega⟩).val : ℝ) := by exact_mod_cast hlt
      linarith
    have hmul0 : 0 ≤ (num / den) * den := mul_nonneg hsl0' (le_of_lt hden)
    calc
      0 ≤ (num / den) * den := hmul0
      _ = num := by
        field_simp [ne_of_gt hden]
  have hlog0 : 0 ≤ Real.log (@ReverseMinkowski.determinant n Q hq) := by
    rw [hlog]
    exact hnum
  -- goal: -log / r ≤ 0
  have hq0 : 0 ≤ Real.log (@ReverseMinkowski.determinant n Q hq) / r := div_nonneg hlog0 (le_of_lt hr0)
  rw [neg_div]
  exact (neg_nonpos.mpr hq0)

lemma stable_of_submodule_eq {W₁ W₂ : Submodule ℤ E} [DiscreteTopology W₁] [DiscreteTopology W₂]
    (h : W₁ = W₂) (hst : Stable W₂) : Stable W₁ := by
  constructor
  · have hd := det_eq_of_eq (L₁ := W₁) (L₂ := W₂) h
    rw [hd]
    exact det_eq_one_of_stable hst
  · intro L hle hdtL
    haveI : DiscreteTopology ↥L := hdtL
    have hle' : L ≤ W₂ := by rwa [h] at hle
    exact all_subdet_ge_one_of_stable hst L hle'

/-- **[B]-final**: for a lattice whose sublattices all have determinant ≥ 1, there is a stable
full-rank ambient lattice `S` with `mass s ℒ ≤ mass s S`. -/
theorem canonical_mass_bound {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (hdet : ∀ (M : Submodule ℤ E), [DiscreteTopology M] → M ≤ ℒ → (1 : ℝ) ≤ ReverseMinkowski.determinant M)
    (s : ℝ) (hs : 0 < s) :
    ∃ (S : Submodule ℤ E) (hSd : DiscreteTopology S),
      @Stable n S hSd ∧ Module.finrank ℤ S = n ∧ mass s ℒ ≤ mass s S := by
  classical
  rcases canonical_chain hℒ with ⟨k, v, hv0, hvN, hinc, hseg, hslope, hnest⟩
  let L : ℕ → Submodule ℤ E := vtxChain hℒ v
  let α : ℕ → ℝ := fun i => canonScale hℒ hv0 hvN hinc hseg hslope i
  have hL0 : L 0 = ⊥ := by dsimp [L]; exact vtxChain_bot hℒ hv0
  have hLk : L k = ℒ := by dsimp [L]; exact vtxChain_top hℒ hvN
  have hchain : ∀ i, i < k → L i ≤ L (i + 1) := by
    intro i hi
    dsimp [L]
    exact vtxChain_step_le hℒ hv0 hvN hinc hseg hslope hi
  have hprim : ∀ i, i < k → Primitive (L i) (L (i + 1)) := by
    intro i hi
    dsimp [L]
    exact vtxChain_primitive hℒ hv0 hvN hinc hseg hslope hi
  have hαpos : ∀ i, i < k → 0 < α i := by
    intro i hi
    dsimp [α]
    exact canonScale_pos hℒ hv0 hvN hinc hseg hslope hi
  have hα1 : ∀ i, i < k → α i ≤ 1 := by
    intro i hi
    dsimp [α]
    exact canonScale_le_one hℒ hv0 hvN hinc hseg hslope hdet hi
  haveI hLkDT : DiscreteTopology ↥(L k) := by
    dsimp [L]
    exact vtxChain_discrete hℒ v k
  -- quotient pieces: discreteness and orthogonality
  have hdiscQ : ∀ i : Fin k, DiscreteTopology ↥(quotPiece L i.val) := by
    intro i
    haveI : DiscreteTopology ↥(vtxChain hℒ v i.val) := vtxChain_discrete hℒ v i.val
    haveI : DiscreteTopology ↥(vtxChain hℒ v (i.val + 1)) := vtxChain_discrete hℒ v (i.val + 1)
    dsimp [quotPiece, L]
    exact discrete_quotLattice (ℒ' := vtxChain hℒ v i.val) (ℒ := vtxChain hℒ v (i.val + 1))
      (realSpan (vtxChain hℒ v i.val)) rfl (vtxChain_primitive hℒ hv0 hvN hinc hseg hslope i.isLt)
  have horthQ : ∀ i j : Fin k, i ≠ j → OrthogonalPair (quotPiece L i.val) (quotPiece L j.val) := by
    intro i j hij
    dsimp [L]
    exact quotPiece_orthogonal_fin (L := vtxChain hℒ v) hchain i j hij
  -- P := pieces in pure quotient-scale form
  let qs (i : Fin k) : ℝ :=
    @quotScale n (L i.val) (L (i.val + 1))
      (by dsimp [L]; exact vtxChain_discrete hℒ v i.val)
      (by dsimp [L]; exact vtxChain_discrete hℒ v (i.val + 1))
      (hdiscQ i)
  let P : Fin k → Submodule ℤ E := fun i => smulLattice (qs i) (quotPiece L i.val)
  let Psup : Submodule ℤ E := ⨆ i : Fin k, P i
  have hα_eq_qs : ∀ i : Fin k, α i.val = qs i := by
    intro i
    dsimp [α, qs]
    rw [canonScale_eq hℒ hv0 hvN hinc hseg hslope i.isLt]
  -- Psup = S (the α-form ambient sum)
  let S : Submodule ℤ E := ⨆ i : Fin k, smulLattice (α i.val) (quotPiece L i.val)
  have hPS : Psup = S := by
    dsimp [Psup, S]
    -- pointwise: smulLattice (qs i) Qᵢ = smulLattice (α i.val) Qᵢ
    have hpt : (fun i : Fin k => smulLattice (qs i) (quotPiece L i.val)) =
        (fun i : Fin k => smulLattice (α i.val) (quotPiece L i.val)) := by
      funext i
      apply congrArg (fun a : ℝ => smulLattice a (quotPiece L i.val))
      exact (hα_eq_qs i).symm
    rw [hpt]
  -- the mass bound (α-form) applies
  have hmassS : mass s ℒ ≤ mass s S := by
    have hmLk : mass s (L k) ≤ mass s S := by
      dsimp [S]
      exact mass_le_mass_sum_scaled L α hL0 hchain hprim hαpos hα1 hLkDT s hs
    have hEq : mass s (L k) = mass s ℒ := congrArg (fun A : Submodule ℤ E => mass s A) hLk
    rwa [hEq] at hmLk
  -- discreteness of pieces P
  have hdiscP : ∀ i : Fin k, DiscreteTopology ↥(P i) := by
    intro i
    dsimp [P]
    haveI : DiscreteTopology ↥(quotPiece L i.val) := hdiscQ i
    infer_instance
  have horthP : ∀ i j : Fin k, i ≠ j → OrthogonalPair (P i) (P j) := by
    intro i j hij
    dsimp [P]
    apply orthogonal_smul
    exact horthQ i j hij
  haveI hPsupDT : DiscreteTopology Psup := by
    dsimp [Psup, P]
    exact discrete_supFam k P horthP hdiscP Psup (by rfl)
  -- piece stability (quotient-scale form)
  have hstP : ∀ i : Fin k, Stable (P i) := by
    intro i
    haveI : DiscreteTopology ↥(vtxChain hℒ v i.val) := vtxChain_discrete hℒ v i.val
    haveI : DiscreteTopology ↥(vtxChain hℒ v (i.val + 1)) := vtxChain_discrete hℒ v (i.val + 1)
    have hprim_i : Primitive (L i.val) (L (i.val + 1)) := hprim i.val i.isLt
    have hext_i : @ExtremalPair n (L i.val) (L (i.val + 1))
        (by dsimp [L]; exact vtxChain_discrete hℒ v i.val)
        (by dsimp [L]; exact vtxChain_discrete hℒ v (i.val + 1)) := by
      dsimp [L]
      exact vtxChain_extremal hℒ hinc hseg i.isLt
    have hr_i : 0 < Module.finrank ℤ ↥(L (i.val + 1)) - Module.finrank ℤ ↥(L i.val) := by
      have hrk1 : Module.finrank ℤ ↥(vtxChain hℒ v (i.val + 1)) = (v (Fin.succ i)).val := by
        have h := vtxChain_rank_of_le hℒ v (i := i.val + 1) (Nat.succ_le_of_lt i.isLt)
        have hfin : (v ⟨i.val + 1, Nat.lt_succ_iff.mpr (Nat.succ_le_of_lt i.isLt)⟩) = v (Fin.succ i) := rfl
        rwa [hfin] at h
      have hrk0 : Module.finrank ℤ ↥(vtxChain hℒ v i.val) = (v (Fin.castSucc i)).val := by
        have h := vtxChain_rank_of_le hℒ v (i := i.val) (le_of_lt i.isLt)
        have hfin : (v ⟨i.val, Nat.lt_succ_iff.mpr (le_of_lt i.isLt)⟩) = v (Fin.castSucc i) := rfl
        rwa [hfin] at h
      have hltv : (v (Fin.castSucc i)).val < (v (Fin.succ i)).val := hinc i
      have hf0 : Module.finrank ℤ ↥(L i.val) = (v (Fin.castSucc i)).val := by
        dsimp [L]
        exact hrk0
      have hf1 : Module.finrank ℤ ↥(L (i.val + 1)) = (v (Fin.succ i)).val := by
        dsimp [L]
        exact hrk1
      rw [← hf1, ← hf0] at hltv
      exact (Nat.sub_pos_iff_lt).mpr hltv
    have hst_i : Stable (smulLattice (qs i) (quotPiece L i.val)) := by
      haveI : DiscreteTopology ↥(quotLattice (L (i.val + 1)) (realSpan (L i.val))) := by
        dsimp [L]
        exact hdiscQ i
      exact stable_quot_of_extremal (ℒ' := L i.val) (ℒ := L (i.val + 1))
        (hp := hprim_i) (hr := hr_i) (hext := hext_i)
    dsimp [P]
    exact hst_i
  -- stability of the sum
  have hstPsup : Stable Psup := by
    dsimp [Psup]
    exact stable_sup_fin k P horthP hdiscP hstP Psup (by rfl)
  have hSd : DiscreteTopology S := by
    -- S = Psup and Psup discrete
    rw [← hPS]
    exact hPsupDT
  have hstS : @Stable n S hSd := by
    haveI : DiscreteTopology ↥S := hSd
    exact stable_of_submodule_eq (W₁ := S) (W₂ := Psup) hPS.symm hstPsup
  -- rank of S
  have hqpos : ∀ i : Fin k, qs i ≠ 0 := by
    intro i
    have hpos : 0 < α i.val := hαpos i.val i.isLt
    rw [hα_eq_qs i] at hpos
    exact ne_of_gt hpos
  have hPrank : ∀ i : Fin k, Module.finrank ℤ ↥(P i) = Module.finrank ℤ ↥(quotPiece L i.val) := by
    intro i
    dsimp [P]
    exact finrank_smulLattice (qs i) (hqpos i) (quotPiece L i.val)
  have hsumP : (∑ i : Fin k, Module.finrank ℤ ↥(P i)) = ∑ i : Fin k, Module.finrank ℤ ↥(quotPiece L i.val) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hPrank i
  have hfinQ : (∑ i : Fin k, Module.finrank ℤ ↥(quotPiece L i.val)) =
      (∑ i ∈ Finset.range k, Module.finrank ℤ ↥(quotPiece L i)) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    rw [dif_pos hi']
  have hfinTop := sum_finrank_quotPiece L hL0 hchain hprim hLkDT
  have hrankS : Module.finrank ℤ S = n := by
    calc
      Module.finrank ℤ S = Module.finrank ℤ ↥Psup := finrank_eq_of_eq hPS.symm
      _ = (∑ i : Fin k, Module.finrank ℤ ↥(P i)) := by
        exact finrank_sum_orthogonal_fin k P horthP hdiscP Psup (by rfl)
      _ = (∑ i : Fin k, Module.finrank ℤ ↥(quotPiece L i.val)) := hsumP
      _ = (∑ i ∈ Finset.range k, Module.finrank ℤ ↥(quotPiece L i)) := hfinQ
      _ = Module.finrank ℤ ↥(L k) := hfinTop
      _ = n := by
        rw [hLk]
        exact fullrank_finrank ℒ hℒ
  exact ⟨S, hSd, hstS, hrankS, hmassS⟩
end
end Submission.Filtration
