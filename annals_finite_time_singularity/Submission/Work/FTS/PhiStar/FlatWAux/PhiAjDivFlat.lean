/-
# `Work.FTS.PhiStar.FlatWAux.PhiAjDivFlat`

The flat `(z+1)^k∂_z^k` estimate for the *divided* profile
`(z'+1)/z' · phiAj j α z'`, uniform in `α ∈ (0, 1/5]`, in `j ≤ 9` and in `k ≤ 7`:

`∃ A > 0, |(z+1)^k ∂_z^k ((·+1)/· · phiAj j α)(z)| ≤ A`.

This is the `phiAj`-instance of the input that `RadGreenDivFlatU` consumes: the divided profile
`(z+1)/z·phiAj j α z` has the same shape `(numerator)/(1+z)^(2j+1)` as `Radial.radGreen`'s
divided solutions, and the two-sided flat/decay data `PhiAjFlatDecayU` (a strictly stronger
input than what is needed here) is not required at all — the estimate follows from the rational
representation `phiAj j α = P_j/(1+z)^{2j+2}` proved in `PhiAjFlatDecay`.

## The route

`phiAj_div_eqOn_num` gives `phiAj j α z'/z' = Q(z')/(1+z')^{2j+2}` on `Ioi 0` with
`Q = phiAjNumDiv α j = (phiAjNum α j).divX`, `natDegree Q ≤ 2j`.  Multiplying by `z'+1`:

`(z'+1)/z' · phiAj j α z' = Q(z')/(1+z')^{2j+1}`   on `Ioi 0`

(`div_step`).  Hence, by `iteratedDeriv_congr_of_eqOn_isOpen` and `iteratedDeriv_rat`, the
`k`-th derivative at `z > 0` equals `(numIter (2j+1) Q k).eval z/(1+z)^{2j+1+k}`; multiplying by
`(z+1)^k` cancels one power of `1+z`, so

`(z+1)^k ∂_z^k ((z'+1)/z'·phiAj j α)(z) = (numIter (2j+1) Q k).eval z/(1+z)^{2j+1}`,

and `poly_eval_bound` (degree of `numIter` is still `≤ 2j`) bounds this by
`cl1 (numIter (2j+1) Q k)/(1+z) ≤ cl1 (numIter (2j+1) Q k)`, which is `≤ cit (2j) (2j+1) k · nb j`
by the `α`-uniform coefficient calculus of `PhiAjFlatDecayU`.  The constant `DivA` is the
(sum of the) `cit · nb` products over `j < 10`, `k < 8`.
-/
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.PhiStar.FlatWAux.PhiAjFlatDecayU
import Submission.Work.FTS.PhiStar.PhiAjFlatDecay
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.FlatWAux.ModeRescaledSmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

open Set

/-! ## The constant -/

/-- The constant of the flat bound for the divided `𝒜`-iterates: an `α`-free, `j`-free envelope
of the coefficient bounds `cit (2j) (2j+1) k · nb j`, `j ≤ 9`, `k ≤ 7`. -/
noncomputable def DivA : ℝ := 1 + ∑ j ∈ Finset.range 10, ∑ k ∈ Finset.range 8,
    Unif.cit (2 * j) (2 * j + 1) k * Unif.nb j

lemma DivA_pos : 0 < DivA := by
  rw [DivA]
  have h : (0 : ℝ) ≤ ∑ j ∈ Finset.range 10, ∑ k ∈ Finset.range 8,
      Unif.cit (2 * j) (2 * j + 1) k * Unif.nb j :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (Unif.cit_nonneg (2 * j) (2 * j + 1) k) (Unif.nb_nonneg j)
  linarith

lemma term_le_DivA {j k : ℕ} (hj : j ≤ 9) (hk : k ≤ 7) :
    Unif.cit (2 * j) (2 * j + 1) k * Unif.nb j ≤ DivA := by
  have hj10 : j ∈ Finset.range 10 := Finset.mem_range.mpr (by omega)
  have hk8 : k ∈ Finset.range 8 := Finset.mem_range.mpr (by omega)
  have hinner : ∀ j' ∈ Finset.range 10, 0 ≤ ∑ k' ∈ Finset.range 8,
      Unif.cit (2 * j') (2 * j' + 1) k' * Unif.nb j' := fun j' _ =>
    Finset.sum_nonneg fun k' _ =>
      mul_nonneg (Unif.cit_nonneg (2 * j') (2 * j' + 1) k') (Unif.nb_nonneg j')
  have h1 : Unif.cit (2 * j) (2 * j + 1) k * Unif.nb j
      ≤ ∑ k' ∈ Finset.range 8, Unif.cit (2 * j) (2 * j + 1) k' * Unif.nb j :=
    Finset.single_le_sum (fun k' _ =>
      mul_nonneg (Unif.cit_nonneg (2 * j) (2 * j + 1) k') (Unif.nb_nonneg j)) hk8
  have h2 : (∑ k' ∈ Finset.range 8, Unif.cit (2 * j) (2 * j + 1) k' * Unif.nb j)
      ≤ ∑ j' ∈ Finset.range 10, ∑ k' ∈ Finset.range 8,
          Unif.cit (2 * j') (2 * j' + 1) k' * Unif.nb j' :=
    Finset.single_le_sum hinner hj10
  rw [DivA]
  linarith

/-! ## The target -/

theorem PhiAjDivFlat : ∃ A : ℝ, 0 < A ∧
    ∀ (α : ℝ), 0 < α → α ≤ 1 / 5 → ∀ (j : ℕ), j ≤ 9 → ∀ (k : ℕ), k ≤ 7 → ∀ z : ℝ, 0 < z →
      |(z + 1) ^ k * iteratedDeriv k
        (fun z' => (z' + 1) / z' * Work.FTS.PhiStar.phiAj j α z') z| ≤ A := by
  refine ⟨DivA, DivA_pos, ?_⟩
  intro α hα hα5 j hj k hk z hz
  have hz1 : (-1 : ℝ) < z := by linarith
  have hQ : (phiAjNumDiv α j).natDegree ≤ 2 * j := phiAjNumDiv_natDegree_le α j
  have hN : (numIter (2 * j + 1) (phiAjNumDiv α j) k).natDegree ≤ 2 * j :=
    (numIter_natDegree_le (2 * j + 1) (phiAjNumDiv α j) k).trans hQ
  -- the divided profile is the rational function `Q/(1+z)^(2j+1)` on `(0,∞)`
  have hfun : Set.EqOn (fun z' : ℝ => (z' + 1) / z' * phiAj j α z')
      (fun z' : ℝ => (phiAjNumDiv α j).eval z' / (1 + z') ^ (2 * j + 1)) (Set.Ioi 0) := by
    intro z' hz'
    show (z' + 1) / z' * phiAj j α z' = (phiAjNumDiv α j).eval z' / (1 + z') ^ (2 * j + 1)
    have hd : phiAj j α z' / z' = (phiAjNumDiv α j).eval z' / (1 + z') ^ (2 * j + 2) :=
      phiAj_div_eqOn_num α j hz'
    have hne : (1 + z' : ℝ) ≠ 0 := by
      have : (0 : ℝ) < z' := hz'
      linarith
    have hne0 : z' ≠ 0 := ne_of_gt hz'
    have hmul : (z' + 1) / z' * phiAj j α z' = (z' + 1) * (phiAj j α z' / z') := by
      field_simp
    rw [hmul, hd]
    rw [show (2 * j + 2 : ℕ) = (2 * j + 1) + 1 from by omega, pow_succ]
    field_simp
    ring
  -- the iterated derivative against the numerator polynomial
  have heq : iteratedDeriv k (fun z' : ℝ => (z' + 1) / z' * phiAj j α z') z
      = (numIter (2 * j + 1) (phiAjNumDiv α j) k).eval z / (1 + z) ^ (2 * j + 1 + k) := by
    rw [iteratedDeriv_congr_of_eqOn_isOpen isOpen_Ioi hfun k hz]
    exact iteratedDeriv_rat (phiAjNumDiv α j) (2 * j + 1) (by omega) k hz1
  -- the `(z+1)^k` factor cancels one power of `1+z`
  have hne1 : (1 + z : ℝ) ≠ 0 := by linarith
  have hstep : (z + 1) ^ k * ((numIter (2 * j + 1) (phiAjNumDiv α j) k).eval z
        / (1 + z) ^ (2 * j + 1 + k))
      = (numIter (2 * j + 1) (phiAjNumDiv α j) k).eval z / (1 + z) ^ (2 * j + 1) := by
    rw [← mul_div_assoc, show (2 * j + 1 + k : ℕ) = k + (2 * j + 1) from by omega, pow_add]
    field_simp
    ring
  have hcl : (∑ i ∈ Finset.range (2 * j + 1),
        |(numIter (2 * j + 1) (phiAjNumDiv α j) k).coeff i|)
      = Unif.cl1 (numIter (2 * j + 1) (phiAjNumDiv α j) k) :=
    Unif.sum_range_coeff_eq_cl1 hN
  have hpe := poly_eval_bound (numIter (2 * j + 1) (phiAjNumDiv α j) k) hN hz.le
  rw [hcl] at hpe
  -- the `α`-uniform coefficient bound
  have hCN : Unif.cl1 (numIter (2 * j + 1) (phiAjNumDiv α j) k)
      ≤ Unif.cit (2 * j) (2 * j + 1) k * Unif.nb j := by
    have h1 := Unif.cl1_numIter_le (2 * j + 1) (2 * j) k hQ
    have h2 : Unif.cl1 (phiAjNumDiv α j) ≤ Unif.nb j :=
      (Unif.cl1_divX_le (phiAjNum α j)).trans (Unif.cl1_phiAjNum_le α hα hα5 j)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (Unif.cit_nonneg (2 * j) (2 * j + 1) k))
  have hCnn : 0 ≤ Unif.cl1 (numIter (2 * j + 1) (phiAjNumDiv α j) k) := Unif.cl1_nonneg _
  have hfin : |(numIter (2 * j + 1) (phiAjNumDiv α j) k).eval z / (1 + z) ^ (2 * j + 1)|
      ≤ Unif.cit (2 * j) (2 * j + 1) k * Unif.nb j := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + z) ^ (2 * j + 1))]
    have hpos : (0 : ℝ) < (1 + z) ^ (2 * j + 1) := by positivity
    calc |(numIter (2 * j + 1) (phiAjNumDiv α j) k).eval z| / (1 + z) ^ (2 * j + 1)
        ≤ Unif.cl1 (numIter (2 * j + 1) (phiAjNumDiv α j) k) * (1 + z) ^ (2 * j)
            / (1 + z) ^ (2 * j + 1) := by
          apply div_le_div_of_nonneg_right hpe hpos.le
      _ = Unif.cl1 (numIter (2 * j + 1) (phiAjNumDiv α j) k) / (1 + z) := by
          rw [pow_succ]
          field_simp
      _ ≤ Unif.cl1 (numIter (2 * j + 1) (phiAjNumDiv α j) k) :=
          div_le_self hCnn (by linarith)
      _ ≤ Unif.cit (2 * j) (2 * j + 1) k * Unif.nb j := hCN
  rw [heq, hstep]
  exact hfin.trans (term_le_DivA hj hk)

end Work.FTS.PhiStar.FlatWAux
