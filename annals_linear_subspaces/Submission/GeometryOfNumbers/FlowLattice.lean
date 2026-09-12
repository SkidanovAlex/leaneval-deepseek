import Mathlib
import ChallengeDeps
import Submission.GeometryOfNumbers.SuccessiveMinima
import Submission.GeometryOfNumbers.DiagonalFlow

/-!
# Milestone (C): the flow lattice and its first short vector

For `0 < ℓ ≤ d` and flow coefficients `a, b` the two-scale diagonal map
`f := scaleMap (twoScale a b ℓ)` sends the standard lattice `ℤᵈ` to the flow lattice
`Λ := map f (ℤᵈ)`.  The first `ℓ` standard basis vectors are the "contracting directions"
(coefficient `a`); in particular `f (e₀)` is a nonzero lattice vector of norm `|a|`, so with
`a = exp(-t/ℓ)` the flow lattice has a nonzero vector of norm `e^{-t/ℓ}`, matching the
paper's "`a_t` has one contracting eigenvalue, giving short vectors of rate `−1/ℓ`".
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

open LinearSubspaces
open Submission.ExteriorCoordinates
open Submission.DiagonalFlow

namespace Submission.FlowLattice

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- The flow lattice `Λ = f(ℤᵈ)` for the two-scale diagonal map `f` (a ℤ-submodule of ℝᵈ),
presented as the ℤ-span of the flowed standard basis vectors `f((B d) i)` (this is the same
submodule as `Submodule.map f ℤᵈ`, see `flowLattice_eq_map`). -/
def flowLattice (a b : ℝ) (ℓ : ℕ) : Submodule ℤ ℝᵈ :=
  Submodule.span ℤ (Set.range (fun i : Fin d => (scaleMap (twoScale a b ℓ)) ((B d) i)))

/-- The image of any standard basis vector under the flow lies in the flow lattice. -/
lemma flowLattice_mem_std (a b : ℝ) (ℓ : ℕ) (i : Fin d) :
    (scaleMap (twoScale a b ℓ)) ((B d) i) ∈ flowLattice a b ℓ := by
  dsimp [flowLattice]
  exact Submodule.subset_span ⟨i, rfl⟩

/-- The first standard basis vector is contracted by the flow with coefficient `a`:
`f e₀ = a • e₀` (when `0 < ℓ`). -/
lemma scaleMap_std_zero (hd : 0 < d) (a b : ℝ) (ℓ : ℕ) (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d) :
    (scaleMap (twoScale a b ℓ)) ((B d) ⟨0, hd⟩) = a • ((B d) ⟨0, hd⟩) := by
  apply rd_ext
  intro j
  rw [scaleMap_apply]
  by_cases hj : j = ⟨0, hd⟩
  · subst j
    simp [twoScale_apply, hℓ]
  · have hval : j.val ≠ 0 := by
      intro hz
      apply hj
      apply Fin.ext
      exact hz
    simp [hj, hval]

/-- The flow lattice contains a nonzero vector of norm `|a|` (the image of the first
standard basis vector). -/
lemma flowLattice_short_vector (hd : 0 < d) (a b : ℝ) (ℓ : ℕ) (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d)
    (ha : a ≠ 0) :
    ∃ w : ℝᵈ, w ∈ flowLattice a b ℓ ∧ w ≠ 0 ∧ ‖w‖ = |a| := by
  classical
  let e₀ : ℝᵈ := (B d) ⟨0, hd⟩
  let f : ℝᵈ →ₗ[ℝ] ℝᵈ := scaleMap (twoScale a b ℓ)
  have hmem : f e₀ ∈ flowLattice a b ℓ := by
    dsimp [e₀, f]
    exact flowLattice_mem_std a b ℓ ⟨0, hd⟩
  refine ⟨f e₀, hmem, ?_, ?_⟩
  · -- f e₀ ≠ 0
    have he0norm : ‖e₀‖ = 1 := by
      dsimp [e₀]
      exact (B d).orthonormal.1 ⟨0, hd⟩
    have he0 : e₀ ≠ 0 := by
      intro h
      have : (‖e₀‖ : ℝ) = 0 := by rw [h]; norm_num
      rw [he0norm] at this
      norm_num at this
    intro hz
    apply ha
    have hsq := scaleMap_std_zero (d := d) hd a b ℓ hℓ hℓd
    have hsmul : a • e₀ = 0 := by
      dsimp [e₀]
      rw [hsq] at hz
      exact hz
    exact (smul_eq_zero.mp hsmul).resolve_right he0
  · -- ‖f e₀‖ = |a|
    have hsq := scaleMap_std_zero (d := d) hd a b ℓ hℓ hℓd
    have he0norm : ‖((B d) ⟨0, hd⟩ : ℝᵈ)‖ = 1 := (B d).orthonormal.1 ⟨0, hd⟩
    calc
      ‖(f e₀ : ℝᵈ)‖ = ‖a • ((B d) ⟨0, hd⟩)‖ := by
            dsimp [e₀, f]
            rw [hsq]
      _ = |a| * ‖((B d) ⟨0, hd⟩)‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = |a| := by rw [he0norm, mul_one]

/-- **Explicit short vector in the flow lattice**: with `a = exp(-t/ℓ)`,
`b = exp(t/(d-ℓ))`, the flow lattice contains a nonzero vector of norm `exp(-t/ℓ)`.
(Contracting eigenvalue direction; the paper's rate `−1/ℓ` for the first minimum.) -/
theorem flowLattice_exp_short (hd : 0 < d) (ℓ : ℕ) (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d) (t : ℝ) :
    ∃ w : ℝᵈ, w ∈ flowLattice (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ
      ∧ w ≠ 0 ∧ ‖w‖ = Real.exp (-t / (ℓ : ℝ)) := by
  have ha : Real.exp (-t / (ℓ : ℝ)) ≠ 0 := ne_of_gt (Real.exp_pos _)
  rcases flowLattice_short_vector (d := d) hd (Real.exp (-t / (ℓ : ℝ)))
    (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ hℓ hℓd ha with ⟨w, hmem, hw0, hw⟩
  refine ⟨w, hmem, hw0, ?_⟩
  -- |exp(-t/ℓ)| = exp(-t/ℓ) (exp > 0)
  rw [hw]
  rw [abs_of_pos (Real.exp_pos _)]


/-- The reciprocal two-scale map is a right inverse of the two-scale map (pointwise
`a·a⁻¹ = b·b⁻¹ = 1`): `scaleMap (twoScale a b ℓ) ∘ scaleMap (twoScale a b ℓ)⁻¹ = id`. -/
lemma scaleMap_twoScale_right_inv (a b : ℝ) (ℓ : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (scaleMap (twoScale a b ℓ)) ∘ₗ (scaleMap (fun i : Fin d => (twoScale a b ℓ i)⁻¹)) =
      LinearMap.id := by
  classical
  let s₂ : Fin d → ℝ := twoScale a b ℓ
  let s₁ : Fin d → ℝ := fun i => (s₂ i)⁻¹
  have h1 : ∀ i : Fin d, s₂ i * s₁ i = 1 := by
    intro i
    dsimp [s₁, s₂]
    rw [twoScale_apply (a := a) (b := b) (ℓ := ℓ) i]
    by_cases hi : i.val < ℓ
    · simp [hi]
      exact mul_inv_cancel₀ ha
    · simp [hi]
      exact mul_inv_cancel₀ hb
  apply LinearMap.ext
  intro x
  apply rd_ext
  intro i
  calc
    ((scaleMap s₂ ∘ₗ scaleMap s₁) x) i = s₂ i * (scaleMap s₁ x) i := by rw [LinearMap.comp_apply, scaleMap_apply]
    _ = s₂ i * (s₁ i * x i) := by rw [scaleMap_apply]
    _ = (s₂ i * s₁ i) * x i := by ring
    _ = x i := by rw [h1 i, one_mul]

/-- The reciprocal two-scale map is a left inverse of the two-scale map:
`scaleMap (twoScale a b ℓ)⁻¹ ∘ scaleMap (twoScale a b ℓ) = id`. -/
lemma scaleMap_twoScale_left_inv (a b : ℝ) (ℓ : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (scaleMap (fun i : Fin d => (twoScale a b ℓ i)⁻¹)) ∘ₗ (scaleMap (twoScale a b ℓ)) =
      LinearMap.id := by
  classical
  let s₂ : Fin d → ℝ := twoScale a b ℓ
  let s₁ : Fin d → ℝ := fun i => (s₂ i)⁻¹
  have h1 : ∀ i : Fin d, s₁ i * s₂ i = 1 := by
    intro i
    dsimp [s₁, s₂]
    rw [twoScale_apply (a := a) (b := b) (ℓ := ℓ) i]
    by_cases hi : i.val < ℓ
    · simp [hi]
      exact inv_mul_cancel₀ ha
    · simp [hi]
      exact inv_mul_cancel₀ hb
  apply LinearMap.ext
  intro x
  apply rd_ext
  intro i
  calc
    ((scaleMap s₁ ∘ₗ scaleMap s₂) x) i = s₁ i * (scaleMap s₂ x) i := by rw [LinearMap.comp_apply, scaleMap_apply]
    _ = s₁ i * (s₂ i * x i) := by rw [scaleMap_apply]
    _ = (s₁ i * s₂ i) * x i := by ring
    _ = x i := by rw [h1 i, one_mul]

/-- The two-scale diagonal map is a linear equivalence of ℝᵈ when both scales are nonzero.
(Blocker (1) for the covolume computation: gives the mapped ℝ-basis and the ℤ-basis of the
flow lattice.) -/
def scaleMapEquiv (a b : ℝ) (ℓ : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : RD d ≃ₗ[ℝ] RD d :=
  LinearEquiv.ofBijective (scaleMap (twoScale a b ℓ)) (by
    classical
    let s : Fin d → ℝ := twoScale a b ℓ
    let g : Fin d → ℝ := fun i => (s i)⁻¹
    have hleft : Function.LeftInverse (scaleMap g) (scaleMap s) := by
      intro x
      have hcomp := scaleMap_twoScale_left_inv (d := d) a b ℓ ha hb
      have hc := congrArg (fun (φ : RD d →ₗ[ℝ] RD d) => φ x) hcomp
      simpa [s, g] using hc
    have hright : Function.RightInverse (scaleMap g) (scaleMap s) := by
      intro x
      have hcomp := scaleMap_twoScale_right_inv (d := d) a b ℓ ha hb
      have hc := congrArg (fun (φ : RD d →ₗ[ℝ] RD d) => φ x) hcomp
      simpa [s, g] using hc
    exact ⟨
      (fun x y hxy => by
        have hgx : (scaleMap g) ((scaleMap s) x) = x := hleft x
        have hgy : (scaleMap g) ((scaleMap s) y) = y := hleft y
        have hc := congrArg (scaleMap g) hxy
        rw [hgx, hgy] at hc
        exact hc),
      (fun y => ⟨(scaleMap g) y, hright y⟩)⟩)


/-- The standard basis `(B d) i` of `ℝᵈ` is linearly independent over ℤ (blocker (2),
core fact: coordinates of an integer linear combination via the real coordinate functional
`(B d).toBasis.coord j`, using `z • x = (z : ℝ) • x` and `Int.cast_eq_zero`). -/
lemma linearIndependent_std_basis :
    LinearIndependent ℤ (fun i : Fin d => ((B d) i : EuclideanSpace ℝ (Fin d))) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let v : Fin d → RD d := fun i => ((B d) i : EuclideanSpace ℝ (Fin d))
  have hφ0 : ((B d).toBasis.coord j) (∑ i : Fin d, c i • v i) = 0 := by
    simpa [v] using congrArg ((B d).toBasis.coord j) hc
  have hcoord : ∀ i : Fin d, ((B d).toBasis.coord j) ((B d) i) = if i = j then 1 else 0 := by
    intro i
    by_cases hij : i = j <;> simp [Basis.coord_apply, hij]
  have hφ : ((B d).toBasis.coord j) (∑ i : Fin d, c i • v i) =
      ∑ i : Fin d, (c i : ℝ) • ((B d).toBasis.coord j) ((B d) i) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hcompat : (c i) • v i = ((c i : ℝ) • v i) := by
      dsimp [v]
      ext k
      simp
    rw [hcompat]
    rw [map_smul]
  have hφsum : (∑ i : Fin d, (c i : ℝ) • ((B d).toBasis.coord j) ((B d) i)) = 0 := by
    have hthis : ((B d).toBasis.coord j) (∑ i : Fin d, c i • v i) =
        ∑ i : Fin d, (c i : ℝ) • ((B d).toBasis.coord j) ((B d) i) := by
      simpa [v] using hφ
    rw [hthis] at hφ0
    exact hφ0
  have hsing : (Finset.univ : Finset (Fin d)).sum (fun i : Fin d =>
      (c i : ℝ) • ((B d).toBasis.coord j) ((B d) i)) =
      (c j : ℝ) • ((B d).toBasis.coord j) ((B d) j) := by
    exact Finset.sum_eq_single (s := Finset.univ) (f := fun i : Fin d =>
      (c i : ℝ) • ((B d).toBasis.coord j) ((B d) i)) (a := j)
      (by
        intro i hi hneq
        have : ((B d).toBasis.coord j) ((B d) i) = 0 := by
          rw [hcoord i]
          rw [if_neg hneq]
        rw [this]
        simp)
      (by intro hnot; exact (hnot (Finset.mem_univ j)).elim)
  have hsingval : (c j : ℝ) • ((B d).toBasis.coord j) ((B d) j) = (c j : ℝ) := by
    rw [hcoord j]
    simp
  have hcj : (c j : ℝ) = 0 := by
    have hφj : (c j : ℝ) • ((B d).toBasis.coord j) ((B d) j) = 0 := by
      rw [hsing] at hφsum
      exact hφsum
    rw [hsingval] at hφj
    exact hφj
  exact (Int.cast_eq_zero (α := ℝ)).mp hcj

/-- The flowed standard basis `f((B d) i)` is linearly independent over ℤ when the flow is
invertible (`a, b ≠ 0`): image of the ℤ-LI standard basis under the injective ℤ-linear map
`scaleMap (twoScale a b ℓ)`. -/
lemma linearIndependent_flow_basis (a b : ℝ) (ℓ : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent ℤ (fun i : Fin d => (scaleMap (twoScale a b ℓ)) ((B d) i)) := by
  classical
  let f : RD d →ₗ[ℤ] RD d := (scaleMap (twoScale a b ℓ)).restrictScalars ℤ
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply (scaleMapEquiv (d := d) a b ℓ ha hb).injective
    change (scaleMap (twoScale a b ℓ)) x = (scaleMap (twoScale a b ℓ)) y
    exact hxy
  have hker : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.mpr hf_inj
  have hfam : LinearIndependent ℤ (fun i : Fin d => f ((B d) i)) :=
    LinearIndependent.map (linearIndependent_std_basis (d := d)) (f := f) (by simp [hker])
  convert hfam using 1
  funext i
  rfl


/-- The flow lattice equals the image of the standard lattice `ℤᵈ` under the flow:
`flowLattice a b ℓ = map f ℤᵈ`. -/
lemma flowLattice_eq_map (a b : ℝ) (ℓ : ℕ) :
    flowLattice (d := d) a b ℓ = Submodule.map ((scaleMap (twoScale a b ℓ)).restrictScalars ℤ) (intPoints (d := d)) := by
  classical
  unfold flowLattice
  have hint : intPoints (d := d) = Submodule.span ℤ (Set.range (fun i : Fin d => ((B d) i : RD d))) := by
    dsimp [intPoints]
  rw [hint]
  rw [Submodule.map_span]
  congr 1
  -- after map_span: range (f ∘ (B d)) = f '' (range (B d))  (f := scaleMap, ℤ-restriction does not change the function)
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨(B d) i, ⟨i, rfl⟩, ?_⟩
    simp
  · rintro ⟨y, ⟨i, hy⟩, rfl⟩
    subst y
    refine ⟨i, rfl⟩

/-- The flow lattice coincides with the ℤ-span of the flowed basis as a `Basis.map` family
(when the flow is invertible). -/
lemma flowLattice_eq_span_map (a b : ℝ) (ℓ : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    flowLattice (d := d) a b ℓ = Submodule.span ℤ (Set.range
      ⇑((B d).toBasis.map (scaleMapEquiv (d := d) a b ℓ ha hb))) := by
  dsimp [flowLattice]
  congr 1

/-- The flow lattice is a discrete subgroup of ℝᵈ for an invertible two-scale flow. -/
instance flowLattice_discreteTopology (a b : ℝ) (ℓ : ℕ) [Fact (a ≠ 0)] [Fact (b ≠ 0)] :
    DiscreteTopology (flowLattice (d := d) a b ℓ) := by
  let g : RD d ≃ₗ[ℝ] RD d := scaleMapEquiv (d := d) a b ℓ (by exact Fact.out) (by exact Fact.out)
  let L₀ : Submodule ℤ (RD d) := Submodule.span ℤ (Set.range ⇑((B d).toBasis.map g))
  have hL : flowLattice (d := d) a b ℓ = L₀ := by
    simpa [L₀, g] using flowLattice_eq_span_map a b ℓ (by exact Fact.out) (by exact Fact.out)
  have hsub : (flowLattice (d := d) a b ℓ : Set (RD d)) ⊆ (L₀ : Set (RD d)) := by
    rw [hL]
  haveI : DiscreteTopology L₀ := by infer_instance
  change DiscreteTopology ((flowLattice (d := d) a b ℓ) : Set (RD d))
  exact DiscreteTopology.of_subset (inferInstance : DiscreteTopology (L₀ : Set (RD d))) hsub

/-- The flow lattice is a ℤ-lattice in ℝᵈ for an invertible two-scale flow. -/
instance flowLattice_isZLattice (a b : ℝ) (ℓ : ℕ) [Fact (a ≠ 0)] [Fact (b ≠ 0)] :
    IsZLattice ℝ (flowLattice (d := d) a b ℓ) := by
  refine ⟨?span_top⟩
  let g : RD d ≃ₗ[ℝ] RD d := scaleMapEquiv (d := d) a b ℓ (by exact Fact.out) (by exact Fact.out)
  let L₀ : Submodule ℤ (RD d) := Submodule.span ℤ (Set.range ⇑((B d).toBasis.map g))
  have hL : flowLattice (d := d) a b ℓ = L₀ := by
    simpa [L₀, g] using flowLattice_eq_span_map a b ℓ (by exact Fact.out) (by exact Fact.out)
  rw [hL]
  haveI : DiscreteTopology L₀ := by infer_instance
  haveI : IsZLattice ℝ L₀ := by infer_instance
  exact IsZLattice.span_top (K := ℝ) (L := L₀)

end Submission.FlowLattice
