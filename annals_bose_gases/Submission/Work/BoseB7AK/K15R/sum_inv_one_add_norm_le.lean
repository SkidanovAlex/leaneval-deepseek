import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseB7AK.K15R.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7AK.K15R.sum_inv_one_add_norm_le` — the lattice decay of the box's mode set

FS §10 needs the mode labels `kn = vec n = 2πn` (`Work.BoseB4.vec`) to be *decaying*:
every finite set of modes contributes at most a fixed amount to the lattice sums
of the chapter.  Concretely, for `3 < 2s` (i.e. `2 ≤ s`, which in three dimensions
is more than enough for convergence) there is a constant `C ≥ 0` with

    `∑_{n ∈ S} (1 + ‖vec n‖²)⁻ˢ ≤ C`

for **every** finite `S ⊆ ℤ³`.  Equivalently: the full lattice series converges.

The proof embeds `ℤ³` as the rank-`3` lattice `L = span ℤ {e₀,e₁,e₂} ⊆ ℝ³` and
uses the `ZLattice` summability theorem `ZLattice.summable_norm_pow_inv`
(`∑_{z ∈ L} ‖z‖⁻⁴ < ∞`, since `3 < 4`).  Pointwise,

    `(1 + ‖vec n‖²)⁻ˢ ≤ ‖toE n‖⁻⁴`   (`n ≠ 0`),

because `‖vec n‖ = 2π‖toE n‖` and `‖toE n‖ ≥ 1` for lattice points `n ≠ 0`; the
single term `n = 0` is added by hand.  The majorant is summable, so the family of
finite partial sums is bounded, and taking the total sum as `C` gives the claim.
-/

noncomputable section

open scoped BigOperators
open Module

namespace Work.BoseB7AK.K15R

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The standard orthonormal `ℝ`-basis of `ℝ³`, viewed as a `ℤ`-basis of the
lattice it spans. -/
private noncomputable def bE3 : Basis (Fin 3) ℝ E3 :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

/-- The integer lattice `ℤ³` sitting inside `ℝ³` as the `ℤ`-span of the standard
basis — the set of points `(n 0, n 1, n 2)`, `n : Fin 3 → ℤ`. -/
private abbrev L3 : Submodule ℤ E3 := Submodule.span ℤ (Set.range bE3)

/-- The lattice vector `(n 0, n 1, n 2) : ℝ³` associated with `n : Fin 3 → ℤ`.
Note `Work.BoseB4.vec n = 2π • toE n`. -/
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

/-- `∑_{z ∈ ℤ³} ‖z‖⁻⁴ < ∞` (the rank is `3 < 4`). -/
private lemma hLsum : Summable (fun z : L3 => ‖z‖⁻¹ ^ 4) :=
  ZLattice.summable_norm_pow_inv L3 4 finrank_lt

/-- The same series, indexed by the coordinate picture `Fin 3 → ℤ` of `ℤ³`. -/
private lemma toE_summable : Summable (fun n : Fin 3 → ℤ => ‖toE n‖⁻¹ ^ 4) := by
  have h0 := hLsum.comp_injective (i := emb) emb_injective
  have h1 : Summable (fun n : Fin 3 → ℤ => ‖emb n‖⁻¹ ^ 4) := by
    simpa [Function.comp_def] using h0
  exact h1.congr (by intro n; rfl)

private lemma toE_ne_zero (n : Fin 3 → ℤ) (hn : n ≠ 0) : toE n ≠ 0 := by
  intro h
  apply hn
  funext i
  have h' : ((n i : ℝ)) = 0 := by
    have := congrArg (fun z : E3 => z.ofLp i) h
    simpa [toE] using this
  exact_mod_cast h'

private lemma toE_zero : toE (0 : Fin 3 → ℤ) = 0 := by
  apply WithLp.ofLp_injective
  ext i
  simp [toE]

/-- The mode vector is `2π` times the lattice point: `vec n = 2π • toE n`. -/
private lemma norm_vec_eq (n : Fin 3 → ℤ) :
    ‖Work.BoseB4.vec n‖ = 2 * Real.pi * ‖toE n‖ := by
  have h : Work.BoseB4.vec n = (2 * Real.pi) • toE n := by
    simp only [Work.BoseB4.vec, toE]
    rw [← WithLp.toLp_smul]
    congr 1
  rw [h, norm_smul, Real.norm_of_nonneg (by positivity)]

private lemma vec_sq (n : Fin 3 → ℤ) :
    ‖Work.BoseB4.vec n‖ ^ 2 = 4 * Real.pi ^ 2 * ‖toE n‖ ^ 2 := by
  rw [norm_vec_eq]; ring

private lemma F_nonneg (s : ℕ) (n : Fin 3 → ℤ) :
    0 ≤ (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹ := by
  apply inv_nonneg.mpr
  positivity

/-- The pointwise decay: for a non-zero lattice point, `(1 + ‖vec n‖²)⁻ˢ` is
dominated by `‖toE n‖⁻⁴` (with `s ≥ 2`). -/
private lemma F_le (s : ℕ) (hs : 2 ≤ s) (n : Fin 3 → ℤ) (hn : n ≠ 0) :
    (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹ ≤ ‖toE n‖⁻¹ ^ 4 := by
  have ha_pos : 0 < ‖toE n‖ := norm_pos_iff.mpr (toE_ne_zero n hn)
  have hSpos : 0 < ‖toE n‖ ^ 2 := pow_pos ha_pos 2
  have hkey : (‖toE n‖ ^ 2) ^ 2 ≤ (1 + 4 * Real.pi ^ 2 * ‖toE n‖ ^ 2) ^ s := by
    have hSle : ‖toE n‖ ^ 2 ≤ 4 * Real.pi ^ 2 * ‖toE n‖ ^ 2 := by
      have h : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
      nlinarith [h, sq_nonneg ‖toE n‖]
    have h1 : (‖toE n‖ ^ 2) ^ 2 ≤ (1 + 4 * Real.pi ^ 2 * ‖toE n‖ ^ 2) ^ 2 := by
      apply pow_le_pow_left₀ (sq_nonneg _)
      linarith
    have h2 : (1 + 4 * Real.pi ^ 2 * ‖toE n‖ ^ 2) ^ 2
        ≤ (1 + 4 * Real.pi ^ 2 * ‖toE n‖ ^ 2) ^ s :=
      pow_le_pow_right₀ (by linarith) hs
    exact h1.trans h2
  have hden_pos : 0 < (1 + 4 * Real.pi ^ 2 * ‖toE n‖ ^ 2) ^ s := by positivity
  calc (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹
      = ((1 + 4 * Real.pi ^ 2 * ‖toE n‖ ^ 2) ^ s)⁻¹ := by rw [vec_sq]
    _ ≤ ((‖toE n‖ ^ 2) ^ 2)⁻¹ := (inv_le_inv₀ hden_pos (pow_pos hSpos 2)).mpr hkey
    _ = ‖toE n‖⁻¹ ^ 4 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, inv_pow, inv_pow]

theorem sum_inv_one_add_norm_le (s : ℕ) (hs : 3 < 2 * s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : Finset (Fin 3 → ℤ),
      (∑ n ∈ S, (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹) ≤ C := by
  have hs2 : 2 ≤ s := by omega
  have hF : Summable (fun n : Fin 3 → ℤ =>
      (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹) := by
    have hdelta : Summable (fun n : Fin 3 → ℤ => if n = 0 then (1 : ℝ) else 0) :=
      (hasSum_ite_eq (b := (0 : Fin 3 → ℤ)) (a := (1 : ℝ))).summable
    have hmaj : Summable (fun n : Fin 3 → ℤ =>
        ‖toE n‖⁻¹ ^ 4 + (if n = 0 then (1 : ℝ) else 0)) := toE_summable.add hdelta
    refine Summable.of_nonneg_of_le (f := fun n : Fin 3 → ℤ =>
        ‖toE n‖⁻¹ ^ 4 + (if n = 0 then (1 : ℝ) else 0))
      (g := fun n : Fin 3 → ℤ => (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹)
      (fun n => F_nonneg s n) (fun n => ?_) hmaj
    by_cases hn : n = 0
    · subst hn
      rw [norm_vec_eq, toE_zero]
      norm_num
    · exact le_trans (F_le s hs2 n hn) (le_add_of_nonneg_right (by positivity))
  refine ⟨∑' n : Fin 3 → ℤ, (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹,
    tsum_nonneg (fun n => F_nonneg s n), ?_⟩
  intro S
  exact hF.sum_le_tsum S (fun i _ => F_nonneg s i)

end Work.BoseB7AK.K15R
