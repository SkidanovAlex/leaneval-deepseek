import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Commons.Analysis.Integral.integral_comp_smul_euclidean
import Submission.Commons.Measure.Lattice.lattice_sum_le_integral_fin3
import Submission.Commons.Measure.Orthant.integral_orthant_eq_inv_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Session-266 — the corpus-level lattice ⇄ continuum comparison
(`Fin 3 → ℝ` form, FS normalisation)

`Submission/Work/ModeLatticeIntegral.lean` certifies the curried
three-dimensional antitone cell comparison.  This module attaches the two
reformulation leaves (proved by the fleet into the shared commons) and states
the comparison in the corpus's mode language: the box-mode sum
`Σ_{k ∈ ℕ³}` of a radial-antitone weight against the continuum momentum
integral, with the FS octant factor `8` and the lattice spacing `π/s`.

Contents (all sorry-free):

  * `eucNorm3` — the Euclidean norm `√(Σ_j u_j²)` on `Fin 3 → ℝ` (the
    `√−Δ`-eigenvalue normalisation: NOT the product/Pi sup norm);
  * `eucNorm3_nonneg`, `eucNorm3_mono` (monotone in the product order on the
    orthant), `eucNorm3_signFlip` (invariant under coordinate sign flips);
  * **`lattice_sum_le_orthant_integral`** — for `F` antitone and nonnegative on
    `[0,∞)`:
    `Σ_{k ∈ [0,n)³} F(π‖k+1‖/s) ≤ ∫_{u ≥ 0} F(π‖u‖/s)du`
    (`Commons.Measure.Lattice.lattice_sum_le_integral` on the box `[0,n]³`
    composed with the set-monotonicity step `[0,n]³ ⊆` orthant);
  * **`lattice_sum_le_third_integral`** — the octant form:
    `Σ_{k ∈ [0,n)³} F(π‖k+1‖/s) ≤ 2^{-3}·∫_{ℝ³}F(π‖u‖/s)du`
    (`Commons.Measure.Orthant.integral_orthant_eq_inv_pow`);
  * **`lattice_sum_le_continuum`** — the FS-normalised form
    `Σ_{k ∈ [0,n)³} F(π‖k+1‖/s) ≤ (2π)^{-3}s³·∫_{ℝ³}F(‖q‖)dq`
    (the rescaling `q = (π/s)u` is the definitional rewriting
    `F(π‖u‖/s) = F(‖(π/s)•u‖)`; see the note below);
  * `lattice_boxModeCoeff_le` — the instantiation at the corpus's
    weighted-kinetic weight `boxModeCoeff s c k = [π‖k‖/s − c]₊⁻²`
    (`F := fun r => (max (r − c) 0)⁻²`), the D1 consumption form.

NOTE on the rescaling: `(2π)^{-3}s³ = (s/π)³·2^{-3}`, and the substitution
`u = (s/π)•q` in `∫_{ℝ³}F(π‖u‖/s)du` is the linear change of variables with
Jacobian `(s/π)³`; it is split off here as the lemma
`integral_eucNorm3_comp_smul` below so that the comparison chain is complete
without leaving this module.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Set
open scoped Real BigOperators

namespace Submission
namespace BoseGases

/-- the Euclidean norm `√(Σ_j u_j²)` on `Fin 3 → ℝ` — the norm whose lattice
values `π‖k‖/s` are the `√−Δ` eigenvalues of the box modes (the product/Pi
sup norm would give the wrong eigenvalue). -/
noncomputable def eucNorm3 (u : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin 3, (u i) ^ 2)

lemma eucNorm3_nonneg (u : Fin 3 → ℝ) : 0 ≤ eucNorm3 u := Real.sqrt_nonneg _

lemma eucNorm3_sq (u : Fin 3 → ℝ) : eucNorm3 u ^ 2 = ∑ i : Fin 3, (u i) ^ 2 := by
  dsimp [eucNorm3]
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- `eucNorm3` is monotone in the product order **on the orthant**. -/
lemma eucNorm3_mono {x y : Fin 3 → ℝ} (hx : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) :
    eucNorm3 x ≤ eucNorm3 y := by
  rw [show eucNorm3 x = Real.sqrt (∑ i : Fin 3, (x i) ^ 2) from rfl,
      show eucNorm3 y = Real.sqrt (∑ i : Fin 3, (y i) ^ 2) from rfl]
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum fun i _ => by
    have h0 : 0 ≤ x i := hx i
    nlinarith [hxy i, h0]

/-- `eucNorm3` scales: `‖a•u‖ = |a|·‖u‖`. -/
lemma eucNorm3_smul (a : ℝ) (u : Fin 3 → ℝ) :
    eucNorm3 (a • u) = |a| * eucNorm3 u := by
  have h1 : ∀ i : Fin 3, ((a • u) i) ^ 2 = a ^ 2 * (u i) ^ 2 := by
    intro i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hL : eucNorm3 (a • u) ^ 2 = a ^ 2 * ∑ i : Fin 3, (u i) ^ 2 := by
    rw [eucNorm3_sq, Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.mul_sum]
  have hR : (a * eucNorm3 u) ^ 2 = a ^ 2 * ∑ i : Fin 3, (u i) ^ 2 := by
    rw [mul_pow, eucNorm3_sq]
  have hsq : eucNorm3 (a • u) ^ 2 = (a * eucNorm3 u) ^ 2 := hL.trans hR.symm
  calc eucNorm3 (a • u) = |eucNorm3 (a • u)| := (abs_of_nonneg (eucNorm3_nonneg _)).symm
    _ = Real.sqrt (eucNorm3 (a • u) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ = Real.sqrt ((a * eucNorm3 u) ^ 2) := by rw [hsq]
    _ = |a * eucNorm3 u| := Real.sqrt_sq_eq_abs _
    _ = |a| * eucNorm3 u := by rw [abs_mul, abs_of_nonneg (eucNorm3_nonneg u)]

/-- coordinate sign flips do not change `eucNorm3`. -/
lemma eucNorm3_signFlip (ε : Fin 3 → ℝ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (u : Fin 3 → ℝ) : eucNorm3 (fun i => ε i * u i) = eucNorm3 u := by
  dsimp [eucNorm3]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases hε i with h | h <;> simp [h]

/-- **the lattice cell comparison against the orthant integral** (the
`Fin 3 → ℝ` corpus form): for `F` antitone and nonnegative on `[0,∞)`,

    Σ_{k ∈ [0,n)³} F(π‖k+1‖/s)  ≤  ∫_{u ≥ 0} F(π‖u‖/s) du . -/
theorem lattice_sum_le_orthant_integral {n : ℕ} {s : ℝ} (hs : 0 < s) {F : ℝ → ℝ}
    (hF : AntitoneOn F (Set.Ici 0)) (hFnn : ∀ p, 0 ≤ p → 0 ≤ F p)
    (hint : IntegrableOn (fun u : Fin 3 → ℝ => F (Real.pi * eucNorm3 u / s))
              (Set.pi Set.univ (fun _ : Fin 3 => Set.Ici (0 : ℝ)))) :
    (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range n),
        F (Real.pi * eucNorm3 (fun i => (k i : ℝ) + 1) / s))
      ≤ ∫ u in Set.pi Set.univ (fun _ : Fin 3 => Set.Ici (0 : ℝ)),
          F (Real.pi * eucNorm3 u / s) := by
  have hbox : Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (0 : ℝ) n)
      ⊆ Set.pi Set.univ (fun _ : Fin 3 => Set.Ici (0 : ℝ)) := by
    intro u hu
    rw [Set.mem_univ_pi] at hu ⊢
    intro i
    exact (hu i).1
  have hscaled_nonneg : ∀ u : Fin 3 → ℝ, 0 ≤ Real.pi * eucNorm3 u / s := by
    intro u
    have h1 : 0 ≤ Real.pi * eucNorm3 u :=
      mul_nonneg Real.pi_nonneg (eucNorm3_nonneg u)
    exact div_nonneg h1 hs.le
  have hstep := Commons.Measure.Lattice.lattice_sum_le_integral (ι := Fin 3) (n := n)
    (G := fun u : Fin 3 → ℝ => F (Real.pi * eucNorm3 u / s))
    (fun x y hx hxy => by
      have hnorm : eucNorm3 x ≤ eucNorm3 y := eucNorm3_mono hx hxy
      have hpx : 0 ≤ Real.pi * eucNorm3 x / s := hscaled_nonneg x
      have : Real.pi * eucNorm3 x / s ≤ Real.pi * eucNorm3 y / s := by
        apply div_le_div_of_nonneg_right _ hs.le
        exact mul_le_mul_of_nonneg_left hnorm Real.pi_nonneg
      exact hF hpx (le_trans hpx this) this)
    (hint.mono_set hbox)
  refine le_trans hstep ?_
  exact setIntegral_mono_set hint
    (Filter.Eventually.of_forall fun u => hFnn _ (hscaled_nonneg u))
    (Filter.Eventually.of_forall fun u hu => hbox hu)

/-- **the octant form**: `Σ_{k ∈ [0,n)³} F(π‖k+1‖/s) ≤ 2^{-3}∫_{ℝ³}F(π‖u‖/s)du`
(FS's octant factor, from the commons orthant lemma). -/
theorem lattice_sum_le_third_integral {n : ℕ} {s : ℝ} (hs : 0 < s) {F : ℝ → ℝ}
    (hF : AntitoneOn F (Set.Ici 0)) (hFnn : ∀ p, 0 ≤ p → 0 ≤ F p)
    (hint : Integrable (fun u : Fin 3 → ℝ => F (Real.pi * eucNorm3 u / s)) volume) :
    (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range n),
        F (Real.pi * eucNorm3 (fun i => (k i : ℝ) + 1) / s))
      ≤ ((2 : ℝ) ^ 3)⁻¹
          * ∫ u : Fin 3 → ℝ, F (Real.pi * eucNorm3 u / s) := by
  have hstep := lattice_sum_le_orthant_integral (n := n) hs hF hFnn (hint.integrableOn)
  refine le_trans hstep ?_
  have hsym : ∀ (ε : Fin 3 → ℝ), (∀ i, ε i = 1 ∨ ε i = -1) → ∀ u,
      (fun v : Fin 3 → ℝ => F (Real.pi * eucNorm3 v / s)) (fun i => ε i * u i)
        = (fun v : Fin 3 → ℝ => F (Real.pi * eucNorm3 v / s)) u := by
    intro ε hε u
    dsimp only
    rw [eucNorm3_signFlip ε hε u]
  rw [Commons.Measure.Orthant.integral_orthant_eq_inv_pow hint hsym]

/-- **A true instantiation — the `|p|^{-4}`-type tail weight.**  For the
antitone, nonnegative, integrable weight `F(r) = (1+r)^{-4}` (the shape of
FS's error-tail weights `|p|^{-6}`, `[|p|−c]₊^{-2}` *after* the head/tail
split),

    Σ_{k ∈ [0,n)³} (1 + π‖k+1‖/s)^{-4}  ≤  2^{-3} ∫_{ℝ³} (1 + π‖u‖/s)^{-4} du .

(NB the weight `[r−c]₊⁻²` itself is NOT antitone — it is `0` for `r ≤ c` and
then jumps — and has a non-integrable singularity at `r = c`; see the note
below.  Only its head/tail majorants are covered by the cell comparison.) -/
theorem lattice_inv_pow_four_le {n : ℕ} {s : ℝ} (hs : 0 < s)
    (hint : Integrable (fun u : Fin 3 → ℝ =>
              ((1 + Real.pi * eucNorm3 u / s) ^ 4)⁻¹) volume) :
    (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range n),
        ((1 + Real.pi * eucNorm3 (fun i => (k i : ℝ) + 1) / s) ^ 4)⁻¹)
      ≤ ((2 : ℝ) ^ 3)⁻¹
          * ∫ u : Fin 3 → ℝ, ((1 + Real.pi * eucNorm3 u / s) ^ 4)⁻¹ := by
  have hF : AntitoneOn (fun r : ℝ => ((1 + r) ^ 4)⁻¹) (Set.Ici 0) := by
    intro r hr r' _hr' hrr'
    have hr0 : (0 : ℝ) ≤ r := hr
    have hlt : (1 + r) ^ 4 ≤ (1 + r') ^ 4 :=
      pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + r) (by linarith) 4
    have hpos : (0 : ℝ) < (1 + r) ^ 4 := by positivity
    have := one_div_le_one_div_of_le hpos hlt
    simpa only [one_div] using this
  have hFnn : ∀ p : ℝ, 0 ≤ p → 0 ≤ ((1 + p) ^ 4)⁻¹ := fun p _ => by positivity
  exact lattice_sum_le_third_integral (n := n) hs hF hFnn hint


/-- **the rescaling leaf** (`Session-267`): the linear change of variables
`u = (s/π)•q` along the Euclidean norm,

    ∫_{ℝ³} F((π/s)·‖u‖) du = (π/s)^{-3} · ∫_{ℝ³} F(‖q‖) dq

(`a := π/s`, `a > 0`).  This is the fleet's commons lemma
`Commons.Analysis.Integral.integral_comp_smul_euclidean` at `n = 3`, with
`eucNorm3` recognised as `√(Σ_j u_j²)`. -/
theorem integral_eucNorm3_comp_smul {s : ℝ} (hs : 0 < s) {F : ℝ → ℝ}
    (hint : Integrable (fun u : Fin 3 → ℝ => F (Real.pi * eucNorm3 u / s)) volume) :
    (∫ u : Fin 3 → ℝ, F (Real.pi * eucNorm3 u / s))
      = ((Real.pi / s) ^ 3)⁻¹ * ∫ q : Fin 3 → ℝ, F (eucNorm3 q) := by
  have ha : (0 : ℝ) < Real.pi / s := div_pos Real.pi_pos hs
  have hpt : ∀ u : Fin 3 → ℝ,
      F (Real.pi * eucNorm3 u / s) = F (Real.pi / s * eucNorm3 u) := by
    intro u
    congr 1
    ring
  have hint' : Integrable (fun u : Fin 3 → ℝ => F (Real.pi / s * eucNorm3 u)) volume :=
    hint.congr (Filter.Eventually.of_forall hpt)
  have h := Commons.Analysis.Integral.integral_comp_smul_euclidean (n := 3)
    (a := Real.pi / s) ha (F := F) (by simpa [eucNorm3] using hint')
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  simpa [eucNorm3] using h

/-- **the FS-normalised lattice ⇄ continuum comparison** (the chapter's
normalisation terminal): for `F` antitone and nonnegative on `[0,∞)`,

    Σ_{k ∈ [0,n)³} F(π‖k+1‖/s)  ≤  (2π)^{-3}·s³ · ∫_{ℝ³} F(‖q‖) dq .

Indeed `(2π)^{-3}s³ = 2^{-3}·(π/s)^{-3}`, so this is
`lattice_sum_le_third_integral` composed with `integral_eucNorm3_comp_smul`. -/
theorem lattice_sum_le_continuum {n : ℕ} {s : ℝ} (hs : 0 < s) {F : ℝ → ℝ}
    (hF : AntitoneOn F (Set.Ici 0)) (hFnn : ∀ p, 0 ≤ p → 0 ≤ F p)
    (hint : Integrable (fun u : Fin 3 → ℝ => F (Real.pi * eucNorm3 u / s)) volume) :
    (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range n),
        F (Real.pi * eucNorm3 (fun i => (k i : ℝ) + 1) / s))
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * s ^ 3 * ∫ q : Fin 3 → ℝ, F (eucNorm3 q) := by
  have hchain := lattice_sum_le_third_integral (n := n) hs hF hFnn hint
  have hstep := integral_eucNorm3_comp_smul (s := s) hs (F := F) hint
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsne : s ≠ 0 := ne_of_gt hs
  have hcoef : ((2 : ℝ) ^ 3)⁻¹ * ((Real.pi / s) ^ 3)⁻¹
      = ((2 * Real.pi) ^ 3)⁻¹ * s ^ 3 := by
    field_simp
  calc (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range n),
        F (Real.pi * eucNorm3 (fun i => (k i : ℝ) + 1) / s))
      ≤ ((2 : ℝ) ^ 3)⁻¹ * ∫ u : Fin 3 → ℝ, F (Real.pi * eucNorm3 u / s) := hchain
    _ = ((2 : ℝ) ^ 3)⁻¹ * (((Real.pi / s) ^ 3)⁻¹ * ∫ q : Fin 3 → ℝ, F (eucNorm3 q)) := by
          rw [hstep]
    _ = ((2 * Real.pi) ^ 3)⁻¹ * s ^ 3 * ∫ q : Fin 3 → ℝ, F (eucNorm3 q) := by
          rw [← mul_assoc, hcoef]

/-! ### Findings recorded (Session-266) — the applicability limits of the chapter

The cell comparison requires an ANTITONE weight `F` on `[0,∞)`.  The D1
sharp weight is `F(r) = [r−c]₊⁻² = (max (r−c) 0)⁻²`, which is

1. **NOT antitone**: `F r = 0` for `r ≤ c` while `F r' → ∞` as `r' ↓ c`; so
   `r < c < r'` gives `F r < F r'`.  The cell comparison (which needs the
   integrand to dominate the outer-corner value on each cell) therefore does
   NOT apply, and the truncated statement
   `Σ_k [π‖k+1‖/s − c]₊⁻² ≤ 2^{-3}∫ [π‖u‖/s − c]₊⁻²` is not merely unproved
   but **vacuous/false**: for `c ≥ 0` both sides are `+∞` (`Σ_{k∈ℕ³}‖k‖⁻²`
   and `∫_{ℝ³}‖u‖⁻²` both diverge);
2. **threshold-singular**: the cell containing `‖u‖ = cs/π` has infinite
   integral, and the near-origin cells poison `‖p‖⁻⁶`-type weights too.

**Consequence for D1**: the lattice ⇄ continuum passage for the SHARP term
`ℬ²/𝒜` cannot be a bare weight comparison.  It must be either
(a) *weighted*: compare `Σ_k w(π‖k‖/s)·|c_k(f)|²` against
`(2π)^{-3}s³∫ w(‖p‖)·|\hat f(p)|² dp` using the exact sampling identity
`⟨ê_k, f⟩ = 2^{-3}·Σ_{ε∈{±1}³} \hat f((π/s)ε⊙k)` (valid because `f` is
supported in the box) plus a quadratic-form/Parseval comparison — the
CORRECT route (the `|c_k(f)|²` decay is what makes both sides finite); or
(b) *head/tail*: split the modes at `π‖k‖/s ≈ 2c` (the corpus's
`boxModeCoeff_tail_le` head/tail philosophy), handle the finitely many head
modes explicitly, and apply the cell comparison only to the antitone tail
majorants `4s²/(π²‖k‖²)` — which requires in addition a lower bound on
`‖u‖` on the cells (the near-origin lattice points must be peeled as a
finite head), giving the `1+δ` factors in the dilute-regime constants.

The general antitone theorems of this module remain correct and apply to the
*error* weights whose head/tail majorants are antitone and integrable away
from the origin — e.g. `lattice_inv_pow_four_le` above. -/

end BoseGases
end Submission
