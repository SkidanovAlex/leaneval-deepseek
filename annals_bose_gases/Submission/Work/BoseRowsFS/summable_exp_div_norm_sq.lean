import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowsFS.KernelDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.summable_exp_div_norm_sq` — the mode sum `Σ_j e^{-‖k_j‖²}/‖k_j‖²` converges

For the box modes `k_j = (2π/ℓ)·j` of the honest model (`Work.BoseRowsFS.kvec`), the
series

`Σ_{j ∈ ℤ³ \ {0}} e^{-‖k_j‖²} / ‖k_j‖²`

converges for every `ℓ ≥ 1`.  This is what makes every honest lattice series in the
`Ŵ₁²/‖k‖²` family (`Submission/Work/BoseRowsFS/sum_exp_div_norm_sq_le.lean` and the
§11 row `Σ_q Ŵ₁(q)²/‖q‖²`) a *finite* quantity at the box data, with no regularity
of `Ŵ₁` beyond `‖Ŵ₁‖_∞ ≤ 16π a` required.

## The mathematics

Write `z := vecZ j ∈ ℤ³ ⊆ ℝ³` for the lattice point of the label `j` and `c := 2π/ℓ`,
so that `‖k_j‖ = c‖z‖`.  The elementary bound

`e^{-u} ≤ 1/(1+u)`,  hence  `e^{-c²t}/(c²t) ≤ 1/((1+c²t)·c²t) ≤ c⁻⁴/t²`

(for `t = ‖z‖² > 0`) turns the summand into a multiple of `‖z‖⁻⁴`, and `Σ_{z ∈ ℤ³} ‖z‖⁻⁴ < ∞`
simply because `ℤ³` is a *lattice of rank `3`* in `ℝ³`: `ZLattice.summable_norm_pow_inv`
gives summability of `‖z‖⁻ⁿ` over any `ZLattice` of rank `< n`, and `3 < 4`.

Note there is a genuine subtlety here: the summand is *not* of polynomial decay — for a
fixed `j ≠ 0` the term is `O(ℓ²)` as `ℓ → ∞` — so the proof must keep track of the
`ℓ`-dependence, which it does through the constant `c⁻⁴ = (ℓ/(2π))⁴` multiplying a
genuinely summable weight.
-/

noncomputable section

open scoped BigOperators
open Module

namespace Work.BoseRowsFS

set_option autoImplicit false

/-! ## 1. The lattice `ℤ³` inside `ℝ³` and the summability of the weight `‖z‖⁻⁴` -/

/-- The rank-`3` integer lattice `ℤ³` of the box, inside `ℝ³`. -/
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private noncomputable def bE3 : Basis (Fin 3) ℝ E3 :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

private abbrev L3 : Submodule ℤ E3 := Submodule.span ℤ (Set.range bE3)

/-- The lattice point `(n 0, n 1, n 2) : ℝ³` of the label `n : Fin 3 → ℤ`; this is
exactly `Work.BoseRowsFS.vecZ n`. -/
private def toE (n : Fin 3 → ℤ) : E3 := WithLp.toLp 2 (fun i : Fin 3 => (n i : ℝ))

private lemma repr_toE (n : Fin 3 → ℤ) (i : Fin 3) : (bE3.repr (toE n)) i = (n i : ℝ) := by
  unfold bE3
  rw [OrthonormalBasis.coe_toBasis_repr_apply]
  rw [EuclideanSpace.basisFun_repr]
  simp [toE]

private lemma mem_toE (n : Fin 3 → ℤ) : toE n ∈ L3 := by
  unfold L3
  rw [bE3.mem_span_iff_repr_mem ℤ]
  intro i
  exact ⟨n i, by rw [repr_toE]; norm_num⟩

private def emb (n : Fin 3 → ℤ) : L3 := ⟨toE n, mem_toE n⟩

private lemma emb_injective : Function.Injective emb := by
  intro a b h
  apply funext
  intro i
  have hc := congrArg (fun z : L3 => (((z : E3)).ofLp) i) h
  change (a i : ℝ) = (b i : ℝ) at hc
  exact_mod_cast hc

private lemma finrank_lt : Module.finrank ℤ L3 < 4 := by
  have hfinE : Module.finrank ℝ E3 = 3 := by simp
  have hrank : Module.finrank ℤ L3 = Module.finrank ℝ E3 := ZLattice.rank ℝ L3
  rw [hrank, hfinE]
  norm_num

private lemma hLsum : Summable (fun z : L3 => ‖z‖⁻¹ ^ 4) :=
  ZLattice.summable_norm_pow_inv L3 4 finrank_lt

private lemma emb_norm_eq_vecZ (n : Fin 3 → ℤ) : ‖emb n‖ = ‖vecZ n‖ := rfl

/-- `Σ_{n : ℤ³} ‖vecZ n‖⁻⁴ < ∞`: the rank of the lattice is `3 < 4`. -/
private lemma summable_vecZ_inv_four : Summable (fun n : Fin 3 → ℤ => ‖vecZ n‖⁻¹ ^ 4) := by
  have h0 := hLsum.comp_injective (i := emb) emb_injective
  have h1 : Summable (fun n : Fin 3 → ℤ => ‖emb n‖⁻¹ ^ 4) := by
    simpa [Function.comp_def] using h0
  exact h1.congr (by intro n; rw [emb_norm_eq_vecZ])

/-! ## 2. The elementary Gaussian-over-square bound -/

private lemma inv_sq_sq (s : ℝ) : (s ^ 2)⁻¹ ^ 2 = s⁻¹ ^ 4 := by
  rw [inv_pow, inv_pow]
  congr 1
  rw [← pow_mul]

/-- **The pointwise decay of the summand.**  For `c > 0` and every real `t`,
`e^{-c²t}/(c²t) ≤ c⁻⁴·(t²)⁻¹`.  The proof is `e^{-u} ≤ 1/(1+u) ≤ 1/(c²t)`; for `t ≤ 0`
both sides are trivially comparable (`0` and a nonnegative number). -/
private lemma exp_div_sq_le (c t : ℝ) (hc : 0 < c) :
    Real.exp (-(c ^ 2 * t)) / (c ^ 2 * t) ≤ c⁻¹ ^ 4 * t⁻¹ ^ 2 := by
  rcases le_or_gt t 0 with ht | ht
  · have hx : c ^ 2 * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg c) ht
    exact le_trans (div_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) hx) (by positivity)
  · have hx : 0 < c ^ 2 * t := mul_pos (pow_pos hc 2) ht
    rw [div_le_iff₀ hx]
    have hexp : Real.exp (-(c ^ 2 * t)) ≤ (1 + c ^ 2 * t)⁻¹ := by
      rw [Real.exp_neg]
      exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr
        (by linarith [Real.add_one_le_exp (c ^ 2 * t)])
    have hrhs : c⁻¹ ^ 4 * t⁻¹ ^ 2 * (c ^ 2 * t) = (c ^ 2 * t)⁻¹ := by
      field_simp
    rw [hrhs]
    exact hexp.trans ((inv_le_inv₀ (by positivity) hx).mpr (by linarith))

/-- The summand at the mode `k_j = c·vecZ j` is dominated by `c⁻⁴‖vecZ j‖⁻⁴`. -/
private lemma term_le {ℓ c : ℝ} (hℓ : 1 ≤ ℓ) (hc : c = 2 * Real.pi / ℓ)
    (j : Fin 3 → ℤ) :
    Real.exp (-(‖kvec ℓ j‖ ^ 2)) / ‖kvec ℓ j‖ ^ 2 ≤ c⁻¹ ^ 4 * ‖vecZ j‖⁻¹ ^ 4 := by
  have hℓpos : 0 < ℓ := lt_of_lt_of_le one_pos hℓ
  have hcpos : 0 < c := by
    rw [hc]; exact div_pos (by positivity) hℓpos
  have hnorm : ‖kvec ℓ j‖ = c * ‖vecZ j‖ := by rw [norm_kvec hℓpos.le j, hc]
  have hsq : ‖kvec ℓ j‖ ^ 2 = c ^ 2 * ‖vecZ j‖ ^ 2 := by rw [hnorm, mul_pow]
  have h := exp_div_sq_le c (‖vecZ j‖ ^ 2) hcpos
  have hconv : c⁻¹ ^ 4 * (‖vecZ j‖ ^ 2)⁻¹ ^ 2 = c⁻¹ ^ 4 * ‖vecZ j‖⁻¹ ^ 4 := by
    rw [inv_sq_sq]
  have hgoal : Real.exp (-(c ^ 2 * ‖vecZ j‖ ^ 2)) / (c ^ 2 * ‖vecZ j‖ ^ 2)
      ≤ c⁻¹ ^ 4 * ‖vecZ j‖⁻¹ ^ 4 := h.trans (le_of_eq hconv)
  rw [hsq]
  exact hgoal

/-! ## 3. The theorem -/

/-- **The Gaussian mode sum divided by the kinetic energy is summable.**  For every
`ℓ ≥ 1`, `Σ_{j ≠ 0} e^{-‖k_j‖²}/‖k_j‖² < ∞` at the box modes `k_j = (2π/ℓ)·j`. -/
theorem summable_exp_div_norm_sq {ℓ : ℝ} (hℓ : 1 ≤ ℓ) :
    Summable (fun j : {j : Fin 3 → ℤ // j ≠ 0} =>
      Real.exp (-(‖Work.BoseRowsFS.kvec ℓ j.1‖ ^ 2)) / ‖Work.BoseRowsFS.kvec ℓ j.1‖ ^ 2) := by
  set c : ℝ := 2 * Real.pi / ℓ with hc
  have hmaj : Summable (fun j : {j : Fin 3 → ℤ // j ≠ 0} => c⁻¹ ^ 4 * ‖vecZ j.1‖⁻¹ ^ 4) := by
    have h := summable_vecZ_inv_four.subtype (fun n : Fin 3 → ℤ => n ≠ 0)
    have h2 : Summable (fun j : {j : Fin 3 → ℤ // j ≠ 0} => ‖vecZ j.1‖⁻¹ ^ 4) := by
      simpa [Function.comp_def] using h
    exact h2.mul_left _
  exact Summable.of_nonneg_of_le (fun j => by positivity)
    (fun j => term_le hℓ hc j.1) hmaj

end Work.BoseRowsFS
