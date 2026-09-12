import Mathlib
import Submission.GeometryOfNumbers.FlowLattice
import Submission.GeometryOfNumbers.FlowLatticeMinimaLower
import Submission.GeometryOfNumbers.SuccessiveMinima
import Submission.GeometryOfNumbers.SuccessiveMinimaExtras

/-!
# Exact successive minima of the contracting flow block

For the two-scale flow `f := scaleMap (twoScale a b ℓ)` with `0 < a ≤ b`, the "small" block
`smallFlow a b ℓ` — the `ℤ`-span of the first `ℓ` flowed standard basis vectors — is a
rank-`ℓ` lattice whose every successive minimum equals `a`:

`λᵢ(smallFlow a b ℓ) = a`   for every `1 ≤ i ≤ ℓ`    (`successiveMinimum_smallFlow_eq`).

Proof structure:
- upper bound `λᵢ ≤ a`: the first `i` flowed basis vectors (`i ≤ ℓ`) are `ℤ`-independent
  members of `smallFlow` of norm exactly `a` (`smallFlow_vec_norm`);
- lower bound `a ≤ λᵢ`: every nonzero member of `smallFlow` is a nonzero member of the full
  flow lattice, whose points all have norm `≥ a` (`norm_ge_of_mem_flowLattice`); the generic
  TC-free lower-bound lemma `SuccessiveMinima.successiveMinimum_ge_of_forall_ne_zero_norm_ge`
  then applies (nonemptyness of the defining set witnessed by the explicit basis family).

This is the model counterpart of the per-block successive-minima fact used in paper §3
Prop 5 ("the successive minima of the sublattice `a_t V_{j_s}(ℤ)` are all bounded by
`λ_{j_s}(a_t ℤᵈ)`"): for a pure contracting block `V_{j_s} = ℤ^ℓ`-slice with `j_s ≤ ℓ`,
both equal `a` (`successiveMinimum_exp_eq` gives `λ_{j_s}(a_tℤᵈ) = e^{-t/ℓ}`).  It also
demonstrates the TC-free successive-minima pattern for lattices of rank `< dim E` (the
ambient `IsZLattice` instance requires full-rank span, so the block minima are computed
with the explicit-basis witnesses instead).

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

namespace Submission.BlockMinima

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- The embedding of the first `i` indices into the index set `{j : Fin d // j.val < ℓ}`
of the small block (requires `i ≤ ℓ ≤ d`). -/
def smallEmb {i ℓ : ℕ} (hiℓ : i ≤ ℓ) (hℓd : ℓ ≤ d) : Fin i → {j : Fin d // j.val < ℓ} :=
  fun r => ⟨⟨r.val, lt_of_lt_of_le r.isLt (le_trans hiℓ hℓd)⟩,
    lt_of_lt_of_le r.isLt hiℓ⟩

lemma smallEmb_injective {i ℓ : ℕ} (hiℓ : i ≤ ℓ) (hℓd : ℓ ≤ d) :
    Function.Injective (smallEmb (d := d) hiℓ hℓd) := by
  intro a b hab
  apply Fin.ext
  have hc : ((smallEmb (d := d) hiℓ hℓd a).1 : Fin d) = (smallEmb (d := d) hiℓ hℓd b).1 := by
    exact congrArg (fun x : {j : Fin d // j.val < ℓ} => (x.1 : Fin d)) hab
  simpa [smallEmb] using hc

/-- The ambient image of the small-block generating family under the embedding of the first
`i` indices. -/
def smallVec {i ℓ : ℕ} {a b : ℝ} (hiℓ : i ≤ ℓ) (hℓd : ℓ ≤ d) : Fin i → ℝᵈ :=
  fun r => (scaleMap (twoScale a b ℓ)) ((B d) (smallEmb (d := d) hiℓ hℓd r).1)

/-- Norm of the `r`-th small vector is `a` (it is `a` times a unit standard basis vector). -/
lemma smallVec_norm {i ℓ : ℕ} {a b : ℝ} (hiℓ : i ≤ ℓ) (hℓd : ℓ ≤ d) (ha0 : 0 ≤ a) (r : Fin i) :
    ‖smallVec (d := d) (a := a) (b := b) (ℓ := ℓ) hiℓ hℓd r‖ = a := by
  classical
  dsimp [smallVec]
  rw [scaleMap_basis]
  have hts : twoScale a b ℓ (smallEmb (d := d) hiℓ hℓd r).1 = a := by
    rw [twoScale_apply]
    simp [(smallEmb (d := d) hiℓ hℓd r).2]
  rw [hts]
  rw [norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg ha0]
  have hb1 : ‖(B d) (smallEmb (d := d) hiℓ hℓd r).1‖ = 1 :=
    (B d).orthonormal.1 (smallEmb (d := d) hiℓ hℓd r).1
  rw [hb1, mul_one]

/-- The small vectors are members of the small block. -/
lemma smallVec_mem_smallFlow {i ℓ : ℕ} {a b : ℝ} (hℓd : ℓ ≤ d) (hiℓ : i ≤ ℓ) (r : Fin i) :
    smallVec (d := d) (a := a) (b := b) (ℓ := ℓ) hiℓ hℓd r ∈
      Submission.FlowLatticeMinimaLower.smallFlow (d := d) a b ℓ hℓd := by
  unfold Submission.FlowLatticeMinimaLower.smallFlow
  exact Submodule.subset_span ⟨smallEmb (d := d) hiℓ hℓd r, by rfl⟩

/-- The small vectors (as members of the small block) are `ℤ`-linearly independent in the
ambient space. -/
lemma smallVec_linearIndependent {i ℓ : ℕ} {a b : ℝ} (hℓd : ℓ ≤ d) (hiℓ : i ≤ ℓ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent ℤ (fun r : Fin i => smallVec (d := d) (a := a) (b := b) (ℓ := ℓ)
      hiℓ hℓd r) := by
  have hfull : LinearIndependent ℤ (fun j : {j : Fin d // j.val < ℓ} =>
      ((scaleMap (twoScale a b ℓ)) ((B d) j.1) : ℝᵈ)) := by
    exact Submission.FlowLatticeMinimaLower.linearIndependent_smallFlow (d := d)
      (a := a) (b := b) (ℓ := ℓ) ha hb
  exact hfull.comp (smallEmb (d := d) hiℓ hℓd) (smallEmb_injective (d := d) hiℓ hℓd)

/-- The small block is a submodule of the full flow lattice. -/
lemma smallFlow_le_flowLattice (a b : ℝ) (ℓ : ℕ) (hℓd : ℓ ≤ d) :
    Submission.FlowLatticeMinimaLower.smallFlow (d := d) a b ℓ hℓd ≤
      flowLattice (d := d) a b ℓ := by
  unfold Submission.FlowLatticeMinimaLower.smallFlow flowLattice
  apply Submodule.span_mono
  intro x hx
  rcases hx with ⟨j, hj⟩
  refine ⟨(j.1 : Fin d), ?_⟩
  simpa using hj

/-- **Exact successive minima of the contracting block**: for `0 < a ≤ b` and
`1 ≤ i ≤ ℓ`, the `i`-th successive minimum of `smallFlow a b ℓ` (the `ℤ`-span of the first
`ℓ` flowed standard basis vectors) equals `a`. -/
theorem successiveMinimum_smallFlow_eq {ℓ : ℕ} (hℓd : ℓ ≤ d) {a b : ℝ} (ha0 : 0 < a)
    (hb0 : 0 < b) (hab : a ≤ b) {i : ℕ} (hi1 : 1 ≤ i) (hiℓ : i ≤ ℓ) :
    Submission.SuccessiveMinima.successiveMinimum
      (Submission.FlowLatticeMinimaLower.smallFlow (d := d) a b ℓ hℓd) i = a := by
  classical
  let sf : Submodule ℤ ℝᵈ := Submission.FlowLatticeMinimaLower.smallFlow (d := d) a b ℓ hℓd
  have ha : a ≠ 0 := ne_of_gt ha0
  have hb : b ≠ 0 := ne_of_gt hb0
  let g : Fin i → sf := fun r =>
    ⟨smallVec (d := d) (a := a) (b := b) (ℓ := ℓ) hiℓ hℓd r,
      smallVec_mem_smallFlow (d := d) hℓd hiℓ r⟩
  have hlin_g : LinearIndependent ℤ (fun r : Fin i => (g r : ℝᵈ)) := by
    simpa [g] using (smallVec_linearIndependent (d := d) hℓd hiℓ ha hb)
  have hnorm_g : ∀ r : Fin i, ‖(g r : ℝᵈ)‖ ≤ a := by
    intro r
    dsimp [g]
    rw [smallVec_norm (d := d) hiℓ hℓd (le_of_lt ha0) r]
  apply le_antisymm
  · -- upper: i independent block vectors of norm exactly a
    exact Submission.SuccessiveMinima.successiveMinimum_le_of_exists sf i (le_of_lt ha0)
      g hlin_g hnorm_g
  · -- lower: every nonzero block point (hence every nonzero flow-lattice point) has norm ≥ a
    have hnon : (Submission.SuccessiveMinima.successiveMinimumSet sf i).Nonempty := by
      refine Submission.SuccessiveMinima.successiveMinimumSet_nonempty_of_exists_linearIndependent
        sf i g hlin_g a hnorm_g (le_of_lt ha0)
    refine Submission.SuccessiveMinima.successiveMinimum_ge_of_forall_ne_zero_norm_ge
      sf a hi1 hnon ?_
    intro v hv0
    have hvE0 : (v : ℝᵈ) ≠ 0 := by
      intro h
      apply hv0
      exact Subtype.ext h
    have hmem : (v : ℝᵈ) ∈ flowLattice (d := d) a b ℓ := by
      exact (smallFlow_le_flowLattice (d := d) a b ℓ hℓd) v.2
    exact Submission.FlowLatticeMinimaLower.norm_ge_of_mem_flowLattice (d := d)
      (v := (v : ℝᵈ)) hmem hvE0 ha0 hab

/-- **Exponential form**: for `0 ≤ t`, every successive minimum of the contracting block of
the exponential flow lattice `a_t ℤᵈ` equals `exp(-t/ℓ)` (block analogue of
`FlowLatticeMinimaLower.successiveMinimum_exp_eq`). -/
theorem successiveMinimum_smallFlow_exp_eq {ℓ : ℕ} (hℓd : ℓ < d) (hℓ0 : 0 < ℓ)
    {t : ℝ} (ht : 0 ≤ t) {i : ℕ} (hi1 : 1 ≤ i) (hiℓ : i ≤ ℓ) :
    Submission.SuccessiveMinima.successiveMinimum
      (Submission.FlowLatticeMinimaLower.smallFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (le_of_lt hℓd)) i =
        Real.exp (-t / (ℓ : ℝ)) := by
  let a : ℝ := Real.exp (-t / (ℓ : ℝ))
  let b : ℝ := Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))
  have ha0 : 0 < a := by dsimp [a]; exact Real.exp_pos _
  have hb0 : 0 < b := by dsimp [b]; exact Real.exp_pos _
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
  have hmain := successiveMinimum_smallFlow_eq (d := d) (ℓ := ℓ) (le_of_lt hℓd)
    (a := a) (b := b) ha0 hb0 hab (i := i) hi1 hiℓ
  simpa [a, b] using hmain

end Submission.BlockMinima
