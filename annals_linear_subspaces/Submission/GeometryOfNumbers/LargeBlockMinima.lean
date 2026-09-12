import Mathlib
import Submission.GeometryOfNumbers.FlowLattice
import Submission.GeometryOfNumbers.FlowLatticeMinimaLower
import Submission.GeometryOfNumbers.SuccessiveMinima
import Submission.GeometryOfNumbers.SuccessiveMinimaExtras

/-!
# Exact successive minima of the expanding flow block

For the two-scale flow `f := scaleMap (twoScale a b ℓ)` with `0 < b` (and invertible flow
`a,b ≠ 0`), the "large" block `largeFlow a b ℓ` — the `ℤ`-span of the flowed standard basis
vectors on the **expanding** coordinates `j.val ≥ ℓ` — is a rank-`(d−ℓ)` lattice whose
every successive minimum equals `b`:

`λᵢ(largeFlow a b ℓ) = b`   for every `1 ≤ i ≤ d − ℓ`
(`successiveMinimum_largeFlow_eq`; exponential form `successiveMinimum_largeFlow_exp_eq`:
with `b = e^{t/(d−ℓ)}`, every block minimum is `e^{t/(d−ℓ)}`).

Proof structure (the mirror of `BlockMinima.successiveMinimum_smallFlow_eq` on the
expanding side of `ℓ`):
- upper bound `λᵢ ≤ b`: the first `i` expanding flowed basis vectors (`i ≤ d − ℓ`, indices
  `ℓ, …, ℓ+i−1`) are `ℤ`-independent members of `largeFlow` of norm exactly `b`
  (`largeVec_norm`);
- lower bound `b ≤ λᵢ`: every nonzero member of `largeFlow` is a combination of the
  mutually orthogonal expanding vectors, each of norm `b`, so by Pythagoras it has norm
  `≥ b` (`norm_ge_of_mem_largeFlow`); the generic TC-free lower-bound lemma
  `SuccessiveMinima.successiveMinimum_ge_of_forall_ne_zero_norm_ge` applies (nonemptyness
  witnessed by the explicit basis family).

This completes the block picture of paper §3 Prop 5's "successive minima of the sublattice
bounded by λ_{j_s}(a_t ℤᵈ)": for a pure expanding block (`j_s`-slice with `j_s ≥ ℓ`), the
block minima are all `b = e^{t/(d−ℓ)}`, matching the V-polygon slope `+t/(d−ℓ)` of
`Submission.Prop4Model` on the other side of `ℓ` (the `log λᵢ = c(i) − c(i−1)` model
Prop 4).  Also records the block's place in the full lattice
(`largeFlow_le_flowLattice`).

All results are Mathlib-only.
-/

noncomputable section

open Set Filter Metric MeasureTheory Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LinearSubspaces
open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.FlowLattice
open Submission.FlowLatticeMinimaLower (flow_basis_orthogonal norm_sq_smul)
open Commons.Analysis.InnerProductSpace (normSq_sum_of_pairwise_orthogonal)

namespace Submission.LargeBlockMinima

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- The index type of the expanding block: the standard directions `j` with
`ℓ ≤ j.val` (the `d − ℓ` directions on which the two-scale flow expands by `b`). -/
abbrev LargeIndex (d : ℕ) (ℓ : ℕ) : Type := {j : Fin d // ℓ ≤ j.val}

/-- The `ℤ`-span of the flowed standard basis vectors on the expanding coordinates
(`j.val ≥ ℓ`), the rank-`(d−ℓ)` "large" block of the two-scale flow lattice. -/
def largeFlow (a b : ℝ) (ℓ : ℕ) : Submodule ℤ ℝᵈ :=
  Submodule.span ℤ (Set.range (fun j : LargeIndex d ℓ =>
    (scaleMap (twoScale a b ℓ)) ((B d) j.1)))

/-- The embedding of the first `i` indices into the expanding block `{j : Fin d // ℓ ≤
j.val}` (requires `i ≤ d − ℓ`): `r ↦ ℓ + r`. -/
def largeEmb {i ℓ : ℕ} (hi : i ≤ d - ℓ) (hℓd : ℓ < d) : Fin i → LargeIndex d ℓ :=
  fun r => ⟨⟨ℓ + r.val, by
      have h1 : r.val < d - ℓ := lt_of_lt_of_le r.isLt hi
      have h2 : ℓ + r.val < ℓ + (d - ℓ) := Nat.add_lt_add_left h1 ℓ
      have h3 : ℓ + (d - ℓ) = d := Nat.add_sub_of_le (le_of_lt hℓd)
      exact lt_of_lt_of_le h2 (le_of_eq h3)⟩,
    by
      change ℓ ≤ ℓ + r.val
      exact Nat.le_add_right ℓ r.val⟩

lemma largeEmb_injective {i ℓ : ℕ} (hi : i ≤ d - ℓ) (hℓd : ℓ < d) :
    Function.Injective (largeEmb (d := d) hi hℓd) := by
  intro a b hab
  apply Fin.ext
  have hc : ℓ + a.val = ℓ + b.val := by
    exact congrArg (fun x : LargeIndex d ℓ => (x.1 : Fin d).val) hab
  omega

/-- The ambient image of the large-block generating family under the embedding of the first
`i` expanding indices. -/
def largeVec {i ℓ : ℕ} {a b : ℝ} (hi : i ≤ d - ℓ) (hℓd : ℓ < d) : Fin i → ℝᵈ :=
  fun r => (scaleMap (twoScale a b ℓ)) ((B d) (largeEmb (d := d) hi hℓd r).1)

/-- Norm of the `r`-th large vector is `b` (it is `b` times a unit standard basis vector on
an expanding coordinate). -/
lemma largeVec_norm {i ℓ : ℕ} {a b : ℝ} (hi : i ≤ d - ℓ) (hℓd : ℓ < d) (hb0 : 0 ≤ b)
    (r : Fin i) : ‖largeVec (d := d) (a := a) (b := b) (ℓ := ℓ) hi hℓd r‖ = b := by
  classical
  dsimp [largeVec]
  rw [scaleMap_basis]
  have hts : twoScale a b ℓ (largeEmb (d := d) hi hℓd r).1 = b := by
    rw [twoScale_apply]
    have hnot : ¬ (largeEmb (d := d) hi hℓd r).1.val < ℓ :=
      not_lt_of_ge (largeEmb (d := d) hi hℓd r).2
    simp [hnot]
  rw [hts]
  rw [norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg hb0]
  have hb1 : ‖(B d) (largeEmb (d := d) hi hℓd r).1‖ = 1 :=
    (B d).orthonormal.1 (largeEmb (d := d) hi hℓd r).1
  rw [hb1, mul_one]

/-- Each flowed expanding basis vector has norm `b` (its two-scale coefficient is `b`). -/
lemma largeBasisVec_norm {a b : ℝ} {ℓ : ℕ} (j : LargeIndex d ℓ) (hb0 : 0 ≤ b) :
    ‖(scaleMap (twoScale a b ℓ)) ((B d) j.1)‖ = b := by
  classical
  rw [scaleMap_basis]
  have hts : twoScale a b ℓ j.1 = b := by
    rw [twoScale_apply]
    have hnot : ¬ j.1.val < ℓ := not_lt_of_ge j.2
    simp [hnot]
  rw [hts]
  rw [norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg hb0]
  have hb1 : ‖(B d) j.1‖ = 1 := (B d).orthonormal.1 j.1
  rw [hb1, mul_one]

/-- The large vectors are members of the large block. -/
lemma largeVec_mem_largeFlow {i ℓ : ℕ} {a b : ℝ} (hi : i ≤ d - ℓ) (hℓd : ℓ < d)
    (r : Fin i) : largeVec (d := d) (a := a) (b := b) (ℓ := ℓ) hi hℓd r ∈
      largeFlow (d := d) a b ℓ := by
  unfold largeFlow
  exact Submodule.subset_span ⟨largeEmb (d := d) hi hℓd r, by rfl⟩

/-- The generating family of the large submodule (indexed by the expanding coordinates) is
`ℤ`-independent. -/
lemma linearIndependent_largeBlockFamily {a b : ℝ} {ℓ : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent ℤ (fun j : LargeIndex d ℓ =>
      ((scaleMap (twoScale a b ℓ)) ((B d) j.1) : ℝᵈ)) := by
  have hfull : LinearIndependent ℤ
      (fun j : Fin d => (scaleMap (twoScale a b ℓ)) ((B d) j) : Fin d → ℝᵈ) := by
    exact linearIndependent_flow_basis (d := d) a b ℓ ha hb
  let ι : LargeIndex d ℓ → Fin d := fun j => j.1
  have hιinj : Function.Injective ι := by
    intro x y h
    apply Subtype.ext
    exact h
  simpa [ι, Function.comp_def] using (hfull.comp ι hιinj)

/-- The large vectors (as members of the large block) are `ℤ`-linearly independent in the
ambient space. -/
lemma largeVec_linearIndependent {i ℓ : ℕ} {a b : ℝ} (hi : i ≤ d - ℓ) (hℓd : ℓ < d)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent ℤ (fun r : Fin i =>
      largeVec (d := d) (a := a) (b := b) (ℓ := ℓ) hi hℓd r) := by
  have hfull := linearIndependent_largeBlockFamily (d := d) (a := a) (b := b) (ℓ := ℓ) ha hb
  have hcomp : LinearIndependent ℤ (fun r : Fin i =>
      ((scaleMap (twoScale a b ℓ)) ((B d) (largeEmb (d := d) hi hℓd r).1) : ℝᵈ)) := by
    exact hfull.comp (largeEmb (d := d) hi hℓd) (largeEmb_injective (d := d) hi hℓd)
  simpa [largeVec] using hcomp

/-- The large block is a submodule of the full flow lattice. -/
lemma largeFlow_le_flowLattice (a b : ℝ) (ℓ : ℕ) :
    largeFlow (d := d) a b ℓ ≤ flowLattice (d := d) a b ℓ := by
  unfold largeFlow flowLattice
  apply Submodule.span_mono
  intro x hx
  rcases hx with ⟨j, hj⟩
  refine ⟨(j.1 : Fin d), ?_⟩
  simpa using hj

/-- A member of the large block is an integer combination of the flowed expanding basis
vectors. -/
lemma mem_largeFlow_coords {a b : ℝ} {ℓ : ℕ} {v : ℝᵈ}
    (hv : v ∈ largeFlow (d := d) a b ℓ) :
    ∃ n : LargeIndex d ℓ → ℤ, v = ∑ j : LargeIndex d ℓ,
      n j • ((scaleMap (twoScale a b ℓ)) ((B d) j.1)) := by
  classical
  rcases (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv with ⟨n, hn⟩
  exact ⟨n, hn.symm⟩

/-- Norm-squared of an integer combination of the expanding flowed basis (Pythagoras over
the orthogonal family, every scale equal to `b`). -/
lemma normSq_large_int_combination {a b : ℝ} {ℓ : ℕ} (n : LargeIndex d ℓ → ℤ) (hb0 : 0 ≤ b) :
    ‖(∑ j : LargeIndex d ℓ, n j • (scaleMap (twoScale a b ℓ)) ((B d) j.1))‖ ^ 2 =
      ∑ j : LargeIndex d ℓ, ((n j : ℝ) ^ 2) * b ^ 2 := by
  classical
  let f : LargeIndex d ℓ → ℝᵈ := fun j => (scaleMap (twoScale a b ℓ)) ((B d) j.1)
  have hz : ‖(∑ j : LargeIndex d ℓ, n j • f j)‖ ^ 2 =
      ∑ j : LargeIndex d ℓ, ((n j : ℝ) ^ 2) * b ^ 2 := by
    let z : LargeIndex d ℓ → ℝᵈ := fun j => ((n j : ℝ)) • f j
    have hze : (∑ j : LargeIndex d ℓ, z j) = (∑ j : LargeIndex d ℓ, n j • f j) := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [z]
      exact Int.cast_smul_eq_zsmul ℝ (n j) (f j)
    have horth : Pairwise (fun i j : LargeIndex d ℓ => inner ℝ (z i) (z j) = 0) := by
      intro i j hij
      dsimp [z]
      have hij1 : i.1 ≠ j.1 := by
        intro h
        apply hij
        exact Subtype.ext h
      have hfij : inner ℝ (f i) (f j) = 0 :=
        (flow_basis_orthogonal (d := d) (a := a) (b := b) (ℓ := ℓ)) hij1
      rw [inner_smul_left, inner_smul_right]
      simp only [starRingEnd_apply]
      rw [hfij]
      ring
    calc
      ‖(∑ j : LargeIndex d ℓ, n j • f j)‖ ^ 2 = ‖(∑ j : LargeIndex d ℓ, z j)‖ ^ 2 := by rw [hze]
      _ = ∑ j : LargeIndex d ℓ, ‖z j‖ ^ 2 := normSq_sum_of_pairwise_orthogonal z horth
      _ = ∑ j : LargeIndex d ℓ, ((n j : ℝ) ^ 2) * b ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            dsimp [z]
            calc
              ‖(n j : ℝ) • f j‖ ^ 2 = (n j : ℝ) ^ 2 * ‖f j‖ ^ 2 := norm_sq_smul (n j : ℝ) (f j)
              _ = (n j : ℝ) ^ 2 * b ^ 2 := by
                    rw [largeBasisVec_norm (d := d) (a := a) (b := b) (ℓ := ℓ) j hb0]
  calc
    ‖(∑ j : LargeIndex d ℓ, n j • (scaleMap (twoScale a b ℓ)) ((B d) j.1))‖ ^ 2
        = ‖(∑ j : LargeIndex d ℓ, n j • f j)‖ ^ 2 := by rfl
    _ = ∑ j : LargeIndex d ℓ, ((n j : ℝ) ^ 2) * b ^ 2 := hz

/-- **Uniform lower bound on the large block**: for `0 < b`, every nonzero member of
`largeFlow` has norm at least `b` (all its generating directions have scale `b`). -/
lemma norm_ge_of_mem_largeFlow {a b : ℝ} {ℓ : ℕ} {v : ℝᵈ}
    (hv : v ∈ largeFlow (d := d) a b ℓ) (hv0 : v ≠ 0) (hb0 : 0 < b) : b ≤ ‖v‖ := by
  classical
  rcases mem_largeFlow_coords (d := d) (a := a) (b := b) (ℓ := ℓ) hv with ⟨n, hn⟩
  have hnz : ∃ j : LargeIndex d ℓ, n j ≠ 0 := by
    by_contra hz
    apply hv0
    rw [hn]
    apply Finset.sum_eq_zero
    intro j hj
    have hnj : n j = 0 := by
      by_contra hnni
      exact hz ⟨j, hnni⟩
    simp [hnj]
  rcases hnz with ⟨j, hnj⟩
  have hsq : ‖v‖ ^ 2 = ∑ k : LargeIndex d ℓ, ((n k : ℝ) ^ 2) * b ^ 2 := by
    rw [hn]
    exact normSq_large_int_combination (d := d) (a := a) (b := b) (ℓ := ℓ) n (le_of_lt hb0)
  have hnn : 1 ≤ (n j : ℝ) ^ 2 := by
    have h1z : (1 : ℤ) ≤ (n j) ^ 2 := by
      have hpos : (0 : ℤ) < (n j) ^ 2 := sq_pos_of_ne_zero hnj
      omega
    have hcast : (1 : ℝ) ≤ ((n j) ^ 2 : ℤ) := by exact_mod_cast h1z
    simpa [pow_two] using hcast
  have hb2 : b ^ 2 ≤ ‖v‖ ^ 2 := by
    calc
      b ^ 2 ≤ ((n j : ℝ) ^ 2) * b ^ 2 := by
            exact le_mul_of_one_le_left (sq_nonneg b) hnn
      _ ≤ ∑ k : LargeIndex d ℓ, ((n k : ℝ) ^ 2) * b ^ 2 := by
            exact Finset.single_le_sum
              (fun k hk => mul_nonneg (sq_nonneg ((n k : ℝ))) (sq_nonneg b))
              (Finset.mem_univ j)
      _ = ‖v‖ ^ 2 := hsq.symm
  have h2 : |b| ≤ |‖v‖| := sq_le_sq.mp hb2
  simpa [abs_of_pos hb0, abs_of_nonneg (norm_nonneg v)] using h2

/-- **Exact successive minima of the expanding block**: for an invertible flow
(`a,b ≠ 0`) with `0 < b` and `1 ≤ i ≤ d − ℓ`, the `i`-th successive minimum of
`largeFlow a b ℓ` (the `ℤ`-span of the flowed standard basis vectors on the expanding
coordinates) equals `b`. -/
theorem successiveMinimum_largeFlow_eq {ℓ : ℕ} {a b : ℝ} (ha : a ≠ 0)
    (hb0 : 0 < b) {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ d - ℓ) :
    Submission.SuccessiveMinima.successiveMinimum (largeFlow (d := d) a b ℓ) i = b := by
  classical
  have hℓd : ℓ < d := by
    have h1 : 1 ≤ d - ℓ := le_trans hi1 hi
    omega
  let lf : Submodule ℤ ℝᵈ := largeFlow (d := d) a b ℓ
  have hb : b ≠ 0 := ne_of_gt hb0
  let g : Fin i → lf := fun r =>
    ⟨largeVec (d := d) (a := a) (b := b) (ℓ := ℓ) hi hℓd r,
      largeVec_mem_largeFlow (d := d) hi hℓd r⟩
  have hlin_g : LinearIndependent ℤ (fun r : Fin i => (g r : ℝᵈ)) := by
    simpa [g] using (largeVec_linearIndependent (d := d) (a := a) (b := b) (ℓ := ℓ)
      hi hℓd ha hb)
  have hnorm_g : ∀ r : Fin i, ‖(g r : ℝᵈ)‖ ≤ b := by
    intro r
    dsimp [g]
    rw [largeVec_norm (d := d) (a := a) (b := b) (ℓ := ℓ) hi hℓd (le_of_lt hb0) r]
  apply le_antisymm
  · -- upper: i independent block vectors of norm exactly b
    exact Submission.SuccessiveMinima.successiveMinimum_le_of_exists lf i (le_of_lt hb0)
      g hlin_g hnorm_g
  · -- lower: every nonzero block point has norm ≥ b
    have hnon : (Submission.SuccessiveMinima.successiveMinimumSet lf i).Nonempty := by
      refine Submission.SuccessiveMinima.successiveMinimumSet_nonempty_of_exists_linearIndependent
        lf i g hlin_g b hnorm_g (le_of_lt hb0)
    refine Submission.SuccessiveMinima.successiveMinimum_ge_of_forall_ne_zero_norm_ge
      lf b hi1 hnon ?_
    intro v hv0
    have hvE0 : (v : ℝᵈ) ≠ 0 := by
      intro h
      apply hv0
      exact Subtype.ext h
    exact norm_ge_of_mem_largeFlow (d := d) (a := a) (b := b) (ℓ := ℓ) v.2 hvE0 hb0

/-- **Exponential form**: for the exponential two-scale flow (`a = e^{−t/ℓ}`,
`b = e^{t/(d−ℓ)}`), every successive minimum of the expanding block equals
`e^{t/(d−ℓ)}` (block analogue of `FlowLatticeMinimaLower.successiveMinimum_exp_eq_gt_ell`,
exact and independent of the sign of `t`). -/
theorem successiveMinimum_largeFlow_exp_eq {ℓ : ℕ} {t : ℝ}
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ d - ℓ) :
    Submission.SuccessiveMinima.successiveMinimum (largeFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ) i =
      Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) := by
  let a : ℝ := Real.exp (-t / (ℓ : ℝ))
  let b : ℝ := Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))
  have ha : a ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hb0 : 0 < b := by dsimp [b]; exact Real.exp_pos _
  have hmain := successiveMinimum_largeFlow_eq (d := d) (ℓ := ℓ) (a := a) (b := b)
    ha hb0 (i := i) hi1 hi
  simpa [a, b] using hmain

/-- **Log of the expanding-block successive minimum**: `log λᵢ(largeFlow a_t) =
t/(d−ℓ)` for `1 ≤ i ≤ d − ℓ` (the expanding V-polygon slope). -/
theorem log_successiveMinimum_largeFlow_exp_eq {ℓ : ℕ} {t : ℝ}
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ d - ℓ) :
    Real.log (Submission.SuccessiveMinima.successiveMinimum (largeFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ) i) =
      t / ((d : ℝ) - (ℓ : ℝ)) := by
  rw [successiveMinimum_largeFlow_exp_eq (d := d) (t := t) hi1 hi]
  exact Real.log_exp (t / ((d : ℝ) - (ℓ : ℝ)))

end Submission.LargeBlockMinima
