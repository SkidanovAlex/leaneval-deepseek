import Mathlib
import Submission.GeometryOfNumbers.FlowLattice
import Submission.GeometryOfNumbers.FlowLatticeMinima
import Submission.GeometryOfNumbers.SuccessiveMinima
import Submission.GeometryOfNumbers.SuccessiveMinimaExtras
import Submission.Commons.Analysis.InnerProductSpace.normSq_sum_of_pairwise_orthogonal

/-!
# Model successive minima of the flow lattice: lower bounds and exact values

For real flow coefficients `a, b` with `0 < a ≤ b`, every nonzero point of the two-scale
flow lattice `flowLattice a b ℓ` (the `ℤ`-span of the flowed standard basis) has Euclidean
norm at least `a` (`a` is the smaller of the two scales, and any nonzero lattice point has a
nonzero integer coefficient of absolute value at least `1` in some standard direction).
The proof: members are `ℤ`-combinations of the mutually orthogonal flowed basis vectors
`f_j = s_j e_j`; Pythagoras (`normSq_sum_of_pairwise_orthogonal`) gives
`‖v‖² = Σⱼ (n_j)² s_j² ≥ s_i² ≥ a²` for a coordinate `i` with `n_i ≠ 0`.

Combining this uniform lower bound with the generic successive-minima lower-bound lemma
`SuccessiveMinima.successiveMinimum_ge_of_forall_ne_zero_norm_ge`, in the exponential flow
(`a = exp(-t/ℓ)`, `b = exp(t/(d-ℓ))`, `t ≥ 0`) we obtain the **exact model successive
minima**:

`λᵢ(a_t ℤᵈ) = exp(-t/ℓ)`  for every `1 ≤ i ≤ ℓ`     (`successiveMinimum_exp_eq`),

matching the paper's picture of `ℓ` contracting directions of rate `e^{-t/ℓ}`.  (Model
counterpart of paper §3 Prop 4 item 2: in the model the Grayson-polygon slopes are exactly
`-t/ℓ` on `[0, ℓ]`, and `Σᵢ log λᵢ = 0 = log covol` since the exponential flow is
unimodular.)  All results here are Mathlib-only.
-/

noncomputable section

open Set Filter Metric MeasureTheory Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

open LinearSubspaces
open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.FlowLattice
open Commons.Analysis.InnerProductSpace

namespace Submission.SuccessiveMinima

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Lower bound on `λᵢ` from a uniform lower bound on nonzero lattice points**:
if every nonzero lattice point has norm `≥ m`, then the `i`-th successive minimum satisfies
`m ≤ λᵢ` for every `1 ≤ i` (with `hS` the nonemptyness of the defining set). -/
lemma successiveMinimum_ge_of_forall_ne_zero_norm_ge (L : Submodule ℤ E) (m : ℝ)
    {i : ℕ} (hi1 : 1 ≤ i) (hS : (successiveMinimumSet L i).Nonempty)
    (h : ∀ v : L, v ≠ 0 → m ≤ ‖(v : E)‖) : m ≤ successiveMinimum L i := by
  refine le_csInf hS ?_
  rintro r ⟨hr0, f, hlin, hnorm⟩
  have hi0 : 0 < i := by omega
  let j : Fin i := ⟨0, hi0⟩
  have hnz : (f j : E) ≠ 0 := hlin.ne_zero j
  have hfj : f j ≠ 0 := by
    intro hz
    apply hnz
    exact congrArg Subtype.val hz
  exact le_trans (h (f j) hfj) (hnorm j)

/-- Nonemptyness of the defining set of `λᵢ` from an explicit family of `i` independent
lattice points of bounded norm. -/
lemma successiveMinimumSet_nonempty_of_exists_linearIndependent (L : Submodule ℤ E) (i : ℕ)
    (f : Fin i → L) (hlin : LinearIndependent ℤ (fun j : Fin i => (f j : E))) (R : ℝ)
    (hR : ∀ j : Fin i, ‖(f j : E)‖ ≤ R) (hR0 : 0 ≤ R) :
    (successiveMinimumSet L i).Nonempty := by
  refine ⟨R, hR0, f, hlin, hR⟩

end Submission.SuccessiveMinima

namespace Submission.FlowLatticeMinimaLower

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- Squared norm of a scalar multiple. -/
lemma norm_sq_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) (x : E) :
    ‖c • x‖ ^ 2 = c ^ 2 * ‖x‖ ^ 2 := by
  rw [norm_smul]
  rw [sq, sq]
  rw [Real.norm_eq_abs]
  rw [pow_two]
  rw [← abs_mul_abs_self c]
  ring

/-- Any coordinate of a vector is bounded by its norm (standard orthonormal coordinates). -/
lemma norm_ge_abs_coord (x : ℝᵈ) (i : Fin d) : |x i| ≤ ‖x‖ := by
  have hx2 : (x i) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (fun j hj => sq_nonneg (x j)) (Finset.mem_univ i)
  have hs : |x i| ≤ |‖x‖| := sq_le_sq.mp hx2
  simpa [abs_of_nonneg (norm_nonneg x)] using hs

/-- The flowed standard basis vectors are pairwise orthogonal. -/
lemma flow_basis_orthogonal {a b : ℝ} {ℓ : ℕ} :
    Pairwise (fun i j : Fin d => inner ℝ ((scaleMap (twoScale a b ℓ)) ((B d) i))
      ((scaleMap (twoScale a b ℓ)) ((B d) j)) = 0) := by
  intro i j hij
  rw [scaleMap_basis, scaleMap_basis]
  rw [inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply]
  rw [(B d).orthonormal.2 hij]
  ring

/-- The `twoScale` coefficients are nonnegative when `0 ≤ a, b`. -/
lemma twoScale_nonneg {a b : ℝ} {ℓ : ℕ} (i : Fin d) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    0 ≤ twoScale a b ℓ i := by
  dsimp [twoScale]
  by_cases h : i.val < ℓ <;> simp [h, ha0, hb0]

/-- Each flowed standard basis vector has norm equal to its flow scale. -/
lemma flow_basis_norm {a b : ℝ} {ℓ : ℕ} (i : Fin d) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    ‖(scaleMap (twoScale a b ℓ)) ((B d) i)‖ = twoScale a b ℓ i := by
  rw [scaleMap_basis]
  rw [norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg (twoScale_nonneg (d := d) (a := a) (b := b) (ℓ := ℓ) i ha0 hb0)]
  have he : ‖(B d) i‖ = 1 := (B d).orthonormal.1 i
  rw [he, mul_one]

/-- A member of the flow lattice is an integer combination of the flowed standard basis
vectors. -/
lemma mem_flowLattice_coords {a b : ℝ} {ℓ : ℕ} {v : ℝᵈ}
    (hv : v ∈ flowLattice (d := d) a b ℓ) :
    ∃ n : Fin d → ℤ, v = ∑ i : Fin d, n i • ((scaleMap (twoScale a b ℓ)) ((B d) i)) := by
  rcases (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv with ⟨n, hn⟩
  exact ⟨n, hn.symm⟩

/-- Norm-squared of an integer combination of the flowed basis (Pythagoras over the
orthogonal family). -/
lemma normSq_int_combination {a b : ℝ} {ℓ : ℕ} (n : Fin d → ℤ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    ‖(∑ j : Fin d, n j • (scaleMap (twoScale a b ℓ)) ((B d) j))‖ ^ 2 =
      ∑ j : Fin d, ((n j : ℝ) ^ 2) * (twoScale a b ℓ j) ^ 2 := by
  classical
  let f : Fin d → ℝᵈ := fun j => (scaleMap (twoScale a b ℓ)) ((B d) j)
  have hz : ‖(∑ j : Fin d, n j • f j)‖ ^ 2 =
      ∑ j : Fin d, ((n j : ℝ) ^ 2) * (twoScale a b ℓ j) ^ 2 := by
    let z : Fin d → ℝᵈ := fun j => ((n j : ℝ)) • f j
    have hze : (∑ j : Fin d, z j) = (∑ j : Fin d, n j • f j) := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [z]
      exact Int.cast_smul_eq_zsmul ℝ (n j) (f j)
    have horth : Pairwise (fun i j => inner ℝ (z i) (z j) = 0) := by
      intro i j hij
      dsimp [z]
      have hfij : inner ℝ (f i) (f j) = 0 :=
        (flow_basis_orthogonal (d := d) (a := a) (b := b) (ℓ := ℓ)) hij
      rw [inner_smul_left, inner_smul_right]
      simp only [starRingEnd_apply]
      rw [hfij]
      ring
    calc
      ‖(∑ j : Fin d, n j • f j)‖ ^ 2 = ‖(∑ j : Fin d, z j)‖ ^ 2 := by rw [hze]
      _ = ∑ j : Fin d, ‖z j‖ ^ 2 := normSq_sum_of_pairwise_orthogonal z horth
      _ = ∑ j : Fin d, ((n j : ℝ) ^ 2) * (twoScale a b ℓ j) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            dsimp [z]
            calc
              ‖(n j : ℝ) • f j‖ ^ 2 = (n j : ℝ) ^ 2 * ‖f j‖ ^ 2 := norm_sq_smul (n j : ℝ) (f j)
              _ = (n j : ℝ) ^ 2 * (twoScale a b ℓ j) ^ 2 := by
                    rw [flow_basis_norm (d := d) (a := a) (b := b) (ℓ := ℓ) j ha0 hb0]
  calc
    ‖(∑ j : Fin d, n j • (scaleMap (twoScale a b ℓ)) ((B d) j))‖ ^ 2
        = ‖(∑ j : Fin d, n j • f j)‖ ^ 2 := by rfl
    _ = ∑ j : Fin d, ((n j : ℝ) ^ 2) * (twoScale a b ℓ j) ^ 2 := hz

/-- **Uniform lower bound**: for `0 < a ≤ b`, every nonzero member of the flow lattice has
norm at least `a`. -/
lemma norm_ge_of_mem_flowLattice {a b : ℝ} {ℓ : ℕ} {v : ℝᵈ}
    (hv : v ∈ flowLattice (d := d) a b ℓ) (hv0 : v ≠ 0)
    (ha0 : 0 < a) (hab : a ≤ b) : a ≤ ‖v‖ := by
  classical
  have hb0 : 0 ≤ b := le_trans (le_of_lt ha0) hab
  rcases mem_flowLattice_coords (d := d) hv with ⟨n, hn⟩
  have hnz : ∃ i : Fin d, n i ≠ 0 := by
    by_contra hz
    apply hv0
    rw [hn]
    apply Finset.sum_eq_zero
    intro i hi
    have hni : n i = 0 := by
      by_contra hnni
      exact hz ⟨i, hnni⟩
    simp [hni]
  rcases hnz with ⟨i, hni⟩
  have hsq : ‖v‖ ^ 2 = ∑ j : Fin d, ((n j : ℝ) ^ 2) * (twoScale a b ℓ j) ^ 2 := by
    rw [hn]
    exact normSq_int_combination (d := d) (a := a) (b := b) (ℓ := ℓ) n (le_of_lt ha0) hb0
  have hs_i : 0 ≤ twoScale a b ℓ i :=
    twoScale_nonneg (d := d) (a := a) (b := b) (ℓ := ℓ) i (le_of_lt ha0) hb0
  have hle : a ≤ twoScale a b ℓ i := by
    dsimp [twoScale]
    by_cases h : i.val < ℓ
    · simp [h]
    · simp [h, hab]
  have hnn : 1 ≤ (n i : ℝ) ^ 2 := by
    have h1z : (1 : ℤ) ≤ (n i) ^ 2 := by
      have hpos : (0 : ℤ) < (n i) ^ 2 := sq_pos_of_ne_zero hni
      omega
    have hcast : (1 : ℝ) ≤ ((n i) ^ 2 : ℤ) := by exact_mod_cast h1z
    simpa [pow_two] using hcast
  have ha2v : a ^ 2 ≤ ‖v‖ ^ 2 := by
    have hs_le_term : (twoScale a b ℓ i) ^ 2 ≤
        ((n i : ℝ) ^ 2) * (twoScale a b ℓ i) ^ 2 := by
      exact le_mul_of_one_le_left (sq_nonneg (twoScale a b ℓ i)) hnn
    have hterm_le_sum : ((n i : ℝ) ^ 2) * (twoScale a b ℓ i) ^ 2 ≤
        ∑ j : Fin d, ((n j : ℝ) ^ 2) * (twoScale a b ℓ j) ^ 2 := by
      exact Finset.single_le_sum
        (fun j hj => mul_nonneg (sq_nonneg ((n j : ℝ))) (sq_nonneg (twoScale a b ℓ j)))
        (Finset.mem_univ i)
    calc
      a ^ 2 ≤ (twoScale a b ℓ i) ^ 2 := by
          exact sq_le_sq.mpr (by
            rw [abs_of_nonneg (le_of_lt ha0), abs_of_nonneg hs_i]
            exact hle)
      _ ≤ ‖v‖ ^ 2 := by
          calc
            (twoScale a b ℓ i) ^ 2 ≤ ((n i : ℝ) ^ 2) * (twoScale a b ℓ i) ^ 2 := hs_le_term
            _ ≤ ∑ j : Fin d, ((n j : ℝ) ^ 2) * (twoScale a b ℓ j) ^ 2 := hterm_le_sum
            _ = ‖v‖ ^ 2 := hsq.symm
  have h2 : |a| ≤ |‖v‖| := sq_le_sq.mp ha2v
  simpa [abs_of_nonneg (le_of_lt ha0), abs_of_nonneg (norm_nonneg v)] using h2

/-- **Lower bound on all successive minima of the flow lattice**: for `0 < a ≤ b`, every
`λᵢ` (`1 ≤ i ≤ d`) satisfies `a ≤ λᵢ` (no nonzero lattice point is shorter than `a`). -/
theorem successiveMinimum_ge_abs_a {a b : ℝ} {ℓ : ℕ} (ha0 : 0 < a) (hab : a ≤ b)
    (ha : a ≠ 0) (hb : b ≠ 0) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ d) :
    a ≤ Submission.SuccessiveMinima.successiveMinimum (flowLattice (d := d) a b ℓ) i := by
  have hnon : (Submission.SuccessiveMinima.successiveMinimumSet (flowLattice (d := d) a b ℓ) i).Nonempty := by
    refine Submission.SuccessiveMinima.successiveMinimumSet_nonempty_of_exists_linearIndependent
      (flowLattice (d := d) a b ℓ) i
      (Submission.FlowLatticeMinima.flowBasisFamily (d := d) a b ℓ hi)
      (Submission.FlowLatticeMinima.flowBasisFamily_linearIndependent (d := d) a b ℓ hi ha hb)
      (max |a| |b|)
      (fun j => Submission.FlowLatticeMinima.flowBasisFamily_norm_le (d := d) a b ℓ hi (r := j))
      (le_max_of_le_left (abs_nonneg a))
  exact Submission.SuccessiveMinima.successiveMinimum_ge_of_forall_ne_zero_norm_ge
    (flowLattice (d := d) a b ℓ) a hi1 hnon (by
      intro v hv0
      refine norm_ge_of_mem_flowLattice (d := d) (a := a) (b := b) (ℓ := ℓ) v.2 ?_ ha0 hab
      intro hzE
      apply hv0
      exact Subtype.ext hzE)

/-- **Exponential form of the lower bound**: for `t ≥ 0`, `λᵢ(a_t ℤᵈ) ≥ exp(-t/ℓ)` for
every `1 ≤ i ≤ d`. -/
theorem successiveMinimum_lower_exp {ℓ : ℕ} (hℓd : ℓ < d) (hℓ0 : 0 < ℓ) {t : ℝ} (ht : 0 ≤ t)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ d) :
    Real.exp (-t / (ℓ : ℝ)) ≤ Submission.SuccessiveMinima.successiveMinimum
      (flowLattice (d := d) (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ) i := by
  let a : ℝ := Real.exp (-t / (ℓ : ℝ))
  let b : ℝ := Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))
  have ha0 : 0 < a := by dsimp [a]; exact Real.exp_pos _
  have hab : a ≤ b := by
    dsimp [a, b]
    exact Real.exp_le_exp.mpr (by
      have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
      have hdmℓpos : (0 : ℝ) < (d : ℝ) - (ℓ : ℝ) := by
        rw [← Nat.cast_sub (le_of_lt hℓd)]
        exact_mod_cast (Nat.sub_pos_of_lt hℓd)
      have hcross : -t * ((d : ℝ) - (ℓ : ℝ)) ≤ t * (ℓ : ℝ) := by
        have hd0 : 0 ≤ (d : ℝ) - (ℓ : ℝ) := le_of_lt hdmℓpos
        have htd : 0 ≤ t * ((d : ℝ) - (ℓ : ℝ)) := mul_nonneg ht hd0
        have htℓ : 0 ≤ t * (ℓ : ℝ) := mul_nonneg ht (le_of_lt hℓpos)
        nlinarith
      rw [div_le_div_iff₀ hℓpos hdmℓpos]
      nlinarith)
  have hle : a ≤ Submission.SuccessiveMinima.successiveMinimum (flowLattice (d := d) a b ℓ) i := by
    exact successiveMinimum_ge_abs_a (d := d) (a := a) (b := b) (ℓ := ℓ) ha0 hab
      (ne_of_gt ha0) (ne_of_gt (Real.exp_pos _)) i hi1 hi
  simpa [a, b] using hle

/-- **Exact model successive minima of the exponential flow lattice**: for `t ≥ 0` and
`1 ≤ i ≤ ℓ`, `λᵢ(a_t ℤᵈ) = exp(-t/ℓ)` — the `ℓ` contracting directions are exactly the
`ℓ` first successive minima. -/
theorem successiveMinimum_exp_eq {ℓ : ℕ} (hℓd : ℓ < d) (hℓ0 : 0 < ℓ) {t : ℝ} (ht : 0 ≤ t)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ ℓ) :
    Submission.SuccessiveMinima.successiveMinimum
      (flowLattice (d := d) (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ) i =
        Real.exp (-t / (ℓ : ℝ)) := by
  apply le_antisymm
  · exact Submission.FlowLatticeMinima.successiveMinimum_exp_le (d := d) hℓd hℓ0 t i hi1 hi
  · exact successiveMinimum_lower_exp (d := d) hℓd hℓ0 ht i hi1 (le_trans hi (le_of_lt hℓd))

end Submission.FlowLatticeMinimaLower

namespace Submission.FlowLatticeMinimaLower

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-! ### The expanding directions: exact values `λᵢ = b` for `ℓ < i ≤ d`

For the two-scale flow with `0 < a ≤ b`, points of norm `< b` have vanishing coefficients on
all expanding coordinates (`j.val ≥ ℓ`), hence lie in the rank-`ℓ` "small" sublattice
`smallFlow` spanned by the first `ℓ` flowed basis vectors; consequently no `ℤ`-independent
family of more than `ℓ` lattice points can have all members of norm `< b`.  Therefore
`b ≤ λᵢ` for every `ℓ < i`, and in the exponential flow this gives the exact values
`λᵢ(a_t ℤᵈ) = exp(t/(d-ℓ))` for `ℓ < i ≤ d`. -/

/-- The `ℤ`-span of the first `ℓ` flowed standard basis vectors (the "small" directions). -/
def smallFlow (a b : ℝ) (ℓ : ℕ) (hℓd : ℓ ≤ d) : Submodule ℤ ℝᵈ :=
  Submodule.span ℤ (Set.range (fun j : {j : Fin d // j.val < ℓ} =>
    (scaleMap (twoScale a b ℓ)) ((B d) j.1)))

/-- The generating family of the small submodule is `ℤ`-independent. -/
lemma linearIndependent_smallFlow {a b : ℝ} {ℓ : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent ℤ (fun j : {j : Fin d // j.val < ℓ} =>
      ((scaleMap (twoScale a b ℓ)) ((B d) j.1) : ℝᵈ)) := by
  have hfull : LinearIndependent ℤ
      (fun j : Fin d => (scaleMap (twoScale a b ℓ)) ((B d) j) : Fin d → ℝᵈ) := by
    exact linearIndependent_flow_basis (d := d) a b ℓ ha hb
  let ι : {j : Fin d // j.val < ℓ} → Fin d := fun j => j.1
  have hιinj : Function.Injective ι := by
    intro a b h
    apply Subtype.ext
    exact h
  convert hfull.comp ι hιinj using 1
  ext j
  rfl

/-- The generating family of the small submodule is a `ℤ`-basis of it. -/
noncomputable def smallFlow_basis {a b : ℝ} {ℓ : ℕ} (hℓd : ℓ ≤ d)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Module.Basis {j : Fin d // j.val < ℓ} ℤ (smallFlow (d := d) a b ℓ hℓd) := by
  let g : {j : Fin d // j.val < ℓ} → smallFlow (d := d) a b ℓ hℓd :=
    fun j => ⟨(scaleMap (twoScale a b ℓ)) ((B d) j.1), Submodule.subset_span ⟨j, rfl⟩⟩
  have hLI : LinearIndependent ℤ g := by
    exact LinearIndependent.of_comp (smallFlow (d := d) a b ℓ hℓd).subtype
      (linearIndependent_smallFlow (d := d) (a := a) (b := b) (ℓ := ℓ) ha hb)
  have hspan : ⊤ ≤ Submodule.span ℤ (Set.range g) := by
    intro x hx
    rcases (Submodule.mem_span_range_iff_exists_fun ℤ).mp x.2 with ⟨c, hc⟩
    refine (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ?_
    refine ⟨c, ?_⟩
    apply Subtype.ext
    change ((∑ j : {j : Fin d // j.val < ℓ}, c j • g j : smallFlow (d := d) a b ℓ hℓd) : ℝᵈ) = x
    -- push the subtype coercion through the sum
    have hsum : ((∑ j : {j : Fin d // j.val < ℓ}, c j • g j : smallFlow (d := d) a b ℓ hℓd) : ℝᵈ) =
        ∑ j : {j : Fin d // j.val < ℓ}, c j • (scaleMap (twoScale a b ℓ)) ((B d) j.1) := by
      -- the coercion is a linear map: sums and smuls commute
      simp [g]
    rw [hsum]
    exact hc
  exact Module.Basis.mk hLI hspan

/-- The cardinality of the index type of the small submodule is `ℓ`. -/
lemma card_smallFlow_index (ℓ : ℕ) (hℓd : ℓ ≤ d) :
    Fintype.card {j : Fin d // j.val < ℓ} = ℓ := by
  classical
  let e : {j : Fin d // j.val < ℓ} ≃ Fin ℓ :=
    { toFun := fun j => ⟨j.1.val, j.2⟩
      invFun := fun r => ⟨⟨r.val, lt_of_lt_of_le r.isLt hℓd⟩, by simp⟩
      left_inv := by
        intro j
        apply Subtype.ext
        apply Fin.ext
        rfl
      right_inv := by
        intro r
        apply Fin.ext
        rfl }
  rw [Fintype.card_congr e, Fintype.card_fin]

/-- The small submodule has rank `ℓ`. -/
lemma finrank_smallFlow {a b : ℝ} {ℓ : ℕ} (hℓd : ℓ ≤ d)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Module.finrank ℤ (smallFlow (d := d) a b ℓ hℓd) = ℓ := by
  have hb' := smallFlow_basis (d := d) (a := a) (b := b) (ℓ := ℓ) hℓd ha hb
  rw [Module.finrank_eq_card_basis hb']
  exact card_smallFlow_index ℓ hℓd

/-- A nonzero coefficient on an expanding coordinate forces the norm to be at least the
expanding scale: `‖v‖ ≥ b` for `0 ≤ a ≤ b` when some `n j ≠ 0` with `j.val ≥ ℓ`. -/
lemma norm_ge_b_of_expanding_coord {a b : ℝ} {ℓ : ℕ} {v : ℝᵈ} {n : Fin d → ℤ}
    (hn : v = ∑ j : Fin d, n j • (scaleMap (twoScale a b ℓ)) ((B d) j))
    {j : Fin d} (hjℓ : ℓ ≤ j.val) (hnj : n j ≠ 0) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    b ≤ ‖v‖ := by
  classical
  have hsq : ‖v‖ ^ 2 = ∑ k : Fin d, ((n k : ℝ) ^ 2) * (twoScale a b ℓ k) ^ 2 := by
    rw [hn]
    exact normSq_int_combination (d := d) (a := a) (b := b) (ℓ := ℓ) n ha0 hb0
  have hs_j : twoScale a b ℓ j = b := by
    dsimp [twoScale]
    simp [hjℓ]
  have hnn : 1 ≤ (n j : ℝ) ^ 2 := by
    have h1z : (1 : ℤ) ≤ (n j) ^ 2 := by
      have hpos : (0 : ℤ) < (n j) ^ 2 := sq_pos_of_ne_zero hnj
      omega
    have hcast : (1 : ℝ) ≤ ((n j) ^ 2 : ℤ) := by exact_mod_cast h1z
    simpa [pow_two] using hcast
  have hb2 : b ^ 2 ≤ ‖v‖ ^ 2 := by
    calc
      b ^ 2 = (twoScale a b ℓ j) ^ 2 := by rw [hs_j]
      _ ≤ ((n j : ℝ) ^ 2) * (twoScale a b ℓ j) ^ 2 := by
            exact le_mul_of_one_le_left (sq_nonneg (twoScale a b ℓ j)) hnn
      _ ≤ ∑ k : Fin d, ((n k : ℝ) ^ 2) * (twoScale a b ℓ k) ^ 2 := by
            exact Finset.single_le_sum
              (fun k hk => mul_nonneg (sq_nonneg ((n k : ℝ))) (sq_nonneg (twoScale a b ℓ k)))
              (Finset.mem_univ j)
      _ = ‖v‖ ^ 2 := hsq.symm
  have hb0' : 0 ≤ b := hb0
  have h2 : |b| ≤ |‖v‖| := sq_le_sq.mp hb2
  simpa [abs_of_nonneg hb0, abs_of_nonneg (norm_nonneg v)] using h2

/-- A member of the flow lattice of norm `< b` lies in the small submodule (it has no
expanding coordinate). -/
lemma mem_smallFlow_of_norm_lt {a b : ℝ} {ℓ : ℕ} (hℓd : ℓ ≤ d)
    {v : ℝᵈ} (hv : v ∈ flowLattice (d := d) a b ℓ) (hvb : ‖v‖ < b)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    v ∈ smallFlow (d := d) a b ℓ hℓd := by
  classical
  rcases mem_flowLattice_coords (d := d) hv with ⟨n, hn⟩
  have hsmall : ∀ j : {j : Fin d // ¬ j.val < ℓ}, n j.1 = 0 := by
    intro j
    by_contra hnj
    have hbnd : b ≤ ‖v‖ := by
      exact norm_ge_b_of_expanding_coord (d := d) (a := a) (b := b) (ℓ := ℓ) hn
        (le_of_not_gt j.2) hnj ha0 hb0
    exact (not_lt_of_ge hbnd) hvb
  -- split the sum: only the small coordinates survive
  have hsplit : v = ∑ j : {j : Fin d // j.val < ℓ},
      n j.1 • (scaleMap (twoScale a b ℓ)) ((B d) j.1) := by
    rw [hn]
    have hsum : (∑ j : Fin d, n j • (scaleMap (twoScale a b ℓ)) ((B d) j)) =
        (∑ s : {j : Fin d // j.val < ℓ}, n s.1 • (scaleMap (twoScale a b ℓ)) ((B d) s.1)) +
        (∑ t : {j : Fin d // ¬ j.val < ℓ}, n t.1 • (scaleMap (twoScale a b ℓ)) ((B d) t.1)) := by
      exact (Fintype.sum_subtype_add_sum_subtype
        (p := fun j : Fin d => j.val < ℓ) (f := fun j => n j • (scaleMap (twoScale a b ℓ)) ((B d) j))).symm
    rw [hsum]
    simp [hsmall]
  rw [hsplit]
  refine Submodule.sum_mem _ ?_
  intro t ht
  exact Submodule.smul_mem _ (n t.1) (Submodule.subset_span ⟨t, rfl⟩)

/-- Any `ℤ`-independent family of more than `ℓ` lattice points has a member of norm at
least `b` (for `0 < a ≤ b`). -/
lemma exists_mem_norm_ge_b_of_linearIndependent {a b : ℝ} {ℓ : ℕ} (hℓd : ℓ ≤ d)
    (ha0 : 0 < a) (hab : a ≤ b) (ha : a ≠ 0) (hb : b ≠ 0) {i : ℕ} (hiℓ : ℓ < i)
    (f : Fin i → flowLattice (d := d) a b ℓ)
    (hlin : LinearIndependent ℤ (fun j : Fin i => ((f j : flowLattice (d := d) a b ℓ) : ℝᵈ))) :
    ∃ j : Fin i, b ≤ ‖((f j : flowLattice (d := d) a b ℓ) : ℝᵈ)‖ := by
  classical
  by_contra hno
  have hlt : ∀ j : Fin i, ‖((f j : flowLattice (d := d) a b ℓ) : ℝᵈ)‖ < b := by
    intro j
    have hle : ‖((f j : flowLattice (d := d) a b ℓ) : ℝᵈ)‖ ≤ b := by
      have : ¬ b ≤ ‖((f j : flowLattice (d := d) a b ℓ) : ℝᵈ)‖ := by
        intro hb'
        exact hno ⟨j, hb'⟩
      exact le_of_not_ge this
    exact lt_of_le_of_ne hle (by
      intro heq
      -- ‖f j‖ = b would give b ≤ ‖f j‖, contradiction
      exact hno ⟨j, ge_of_eq heq⟩)
  have hmem : ∀ j : Fin i,
      ((f j : flowLattice (d := d) a b ℓ) : ℝᵈ) ∈ smallFlow (d := d) a b ℓ hℓd := by
    intro j
    exact mem_smallFlow_of_norm_lt (d := d) (a := a) (b := b) (ℓ := ℓ) hℓd
      (f j).2 (hlt j) (le_of_lt ha0) (le_of_lt (lt_of_lt_of_le ha0 hab))
  let F : Fin i → smallFlow (d := d) a b ℓ hℓd := fun j => ⟨((f j : flowLattice (d := d) a b ℓ) : ℝᵈ), hmem j⟩
  have hLI : LinearIndependent ℤ F := by
    exact LinearIndependent.of_comp (smallFlow (d := d) a b ℓ hℓd).subtype hlin
  haveI : Module.Finite ℤ (smallFlow (d := d) a b ℓ hℓd) :=
    Module.Finite.of_basis (smallFlow_basis (d := d) (a := a) (b := b) (ℓ := ℓ) hℓd ha hb)
  have hcard := LinearIndependent.fintype_card_le_finrank hLI
  have hfin : Module.finrank ℤ (smallFlow (d := d) a b ℓ hℓd) = ℓ :=
    finrank_smallFlow (d := d) (a := a) (b := b) (ℓ := ℓ) hℓd ha hb
  rw [hfin] at hcard
  have hicard : i ≤ ℓ := by simpa using hcard
  omega

/-- **Lower bound on the successive minima above `ℓ`**: for `0 < a ≤ b` and `ℓ < i ≤ d`,
the `i`-th successive minimum satisfies `b ≤ λᵢ`. -/
theorem successiveMinimum_ge_b {a b : ℝ} {ℓ : ℕ} (hℓd : ℓ ≤ d) (ha0 : 0 < a) (hab : a ≤ b)
    (ha : a ≠ 0) (hb : b ≠ 0) (i : ℕ) (hiℓ : ℓ < i) (hi : i ≤ d) :
    b ≤ Submission.SuccessiveMinima.successiveMinimum (flowLattice (d := d) a b ℓ) i := by
  have hnon : (Submission.SuccessiveMinima.successiveMinimumSet (flowLattice (d := d) a b ℓ) i).Nonempty := by
    refine Submission.SuccessiveMinima.successiveMinimumSet_nonempty_of_exists_linearIndependent
      (flowLattice (d := d) a b ℓ) i
      (Submission.FlowLatticeMinima.flowBasisFamily (d := d) a b ℓ hi)
      (Submission.FlowLatticeMinima.flowBasisFamily_linearIndependent (d := d) a b ℓ hi ha hb)
      (max |a| |b|)
      (fun j => Submission.FlowLatticeMinima.flowBasisFamily_norm_le (d := d) a b ℓ hi (r := j))
      (le_max_of_le_left (abs_nonneg a))
  refine le_csInf hnon ?_
  rintro r ⟨hr0, f, hlin, hnorm⟩
  rcases exists_mem_norm_ge_b_of_linearIndependent (d := d) (a := a) (b := b) (ℓ := ℓ) hℓd ha0 hab ha hb hiℓ f hlin with ⟨j, hb'⟩
  exact le_trans hb' (hnorm j)

end Submission.FlowLatticeMinimaLower

namespace Submission.FlowLatticeMinimaLower

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- **Exponential form of the lower bound above `ℓ`**: for `t ≥ 0` and `ℓ < i ≤ d`,
`λᵢ(a_t ℤᵈ) ≥ exp(t/(d-ℓ))`. -/
theorem successiveMinimum_ge_b_exp {ℓ : ℕ} (hℓd : ℓ < d) (hℓ0 : 0 < ℓ) {t : ℝ} (ht : 0 ≤ t)
    (i : ℕ) (hiℓ : ℓ < i) (hi : i ≤ d) :
    Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≤ Submission.SuccessiveMinima.successiveMinimum
      (flowLattice (d := d) (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ) i := by
  let a : ℝ := Real.exp (-t / (ℓ : ℝ))
  let b : ℝ := Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))
  have ha0 : 0 < a := by dsimp [a]; exact Real.exp_pos _
  have hab : a ≤ b := by
    dsimp [a, b]
    exact Real.exp_le_exp.mpr (by
      have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
      have hdmℓpos : (0 : ℝ) < (d : ℝ) - (ℓ : ℝ) := by
        rw [← Nat.cast_sub (le_of_lt hℓd)]
        exact_mod_cast (Nat.sub_pos_of_lt hℓd)
      have hcross : -t * ((d : ℝ) - (ℓ : ℝ)) ≤ t * (ℓ : ℝ) := by
        have hd0 : 0 ≤ (d : ℝ) - (ℓ : ℝ) := le_of_lt hdmℓpos
        have htd : 0 ≤ t * ((d : ℝ) - (ℓ : ℝ)) := mul_nonneg ht hd0
        have htℓ : 0 ≤ t * (ℓ : ℝ) := mul_nonneg ht (le_of_lt hℓpos)
        nlinarith
      rw [div_le_div_iff₀ hℓpos hdmℓpos]
      nlinarith)
  have hle : b ≤ Submission.SuccessiveMinima.successiveMinimum (flowLattice (d := d) a b ℓ) i := by
    exact successiveMinimum_ge_b (d := d) (a := a) (b := b) (ℓ := ℓ) (le_of_lt hℓd) ha0 hab
      (ne_of_gt ha0) (ne_of_gt (Real.exp_pos _)) i hiℓ hi
  simpa [a, b] using hle

/-- **Exact model successive minima of the exponential flow lattice, expanding part**: for
`t ≥ 0` and `ℓ < i ≤ d`, `λᵢ(a_t ℤᵈ) = exp(t/(d-ℓ))`. -/
theorem successiveMinimum_exp_eq_gt_ell {ℓ : ℕ} (hℓd : ℓ < d) (hℓ0 : 0 < ℓ) {t : ℝ} (ht : 0 ≤ t)
    (i : ℕ) (hiℓ : ℓ < i) (hi : i ≤ d) :
    Submission.SuccessiveMinima.successiveMinimum
      (flowLattice (d := d) (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ) i =
        Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) := by
  apply le_antisymm
  · exact Submission.FlowLatticeMinima.successiveMinimum_exp_le_all (d := d) hℓd hℓ0 ht i (by omega) hi
  · exact successiveMinimum_ge_b_exp (d := d) hℓd hℓ0 ht i hiℓ hi

end Submission.FlowLatticeMinimaLower
