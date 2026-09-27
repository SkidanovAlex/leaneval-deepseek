import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.homInv_cls_eq_of_conj
import Submission.Work.KT.idem_close_conj_of_isUnit
import Submission.Work.KT.isUnit_one_sub_of_matNorm_lt_one

/-!
# Homotopy invariance of `K₀` classes of idempotent matrices

`Work.KT.homotopy_inv`: a continuous path of idempotent matrices over a closed subalgebra `R` of a
complex Banach algebra `𝔄` has constant class in `K₀`.

The proof is the standard one.  Two idempotents `p`, `q` that are close are conjugate: with
`v = (2p - 1)(q - p)` the element `1 + v` equals `p q + (1 - p)(1 - q)`, is a unit as soon as
`‖v‖ < 1` (Neumann series) and satisfies `(1 + v) q = p (1 + v)`.  Conjugate idempotents have the
same `K₀`-class.  Continuity on the compact interval supplies, around every point, a neighbourhood
on which the class is constant, so the class is a locally constant function on the connected space
`[0,1]`, hence constant.

On the norm of `M_n(R)`: `Matrix` carries no normed-ring *instance* in Mathlib, and the normed-ring
structure `Matrix.linftyOpNormedRing` induces a uniformity that is not the one on which the
completeness instances for matrices are stated.  We therefore never install a normed-ring structure
on matrices; instead the `L∞`-operator norm is used as a plain function `homInvMatNorm` and the
auxiliary estimates are proved directly, while `K₀`-theoretic bookkeeping (which needs no norm) is
in the imported lemmas.
-/

namespace Work.KT

open Matrix Filter

open scoped Topology BigOperators NNReal

/-- The `L∞`-operator norm `sup_i ∑_j ‖A i j‖`, as a plain function on matrices (no norm instance
is imposed on matrices in this file). -/
def homInvMatNorm {R : Type*} [SeminormedRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : NNReal :=
  Finset.univ.sup fun i => ∑ j, ‖A i j‖₊

/-- Each entry is bounded by the `L∞`-operator norm. -/
lemma homInvMatNorm_entry_le {R : Type*} [SeminormedRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) : ‖A i j‖₊ ≤ homInvMatNorm A := by
  refine (Finset.single_le_sum (f := fun k => ‖A i k‖₊) (a := j) (fun k _ => zero_le)
    (Finset.mem_univ j)).trans ?_
  exact Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ i)

/-- An entrywise bound bounds the `L∞`-operator norm. -/
lemma homInvMatNorm_le_card_mul {R : Type*} [SeminormedRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) {c : NNReal} (h : ∀ i j, ‖A i j‖₊ ≤ c) :
    homInvMatNorm A ≤ n * c := by
  refine Finset.sup_le fun i _ => ?_
  calc ∑ j : Fin n, ‖A i j‖₊ ≤ ∑ _j : Fin n, c := Finset.sum_le_sum fun j _ => h i j
    _ = n * c := by simp

/-- The `L∞`-operator norm is invariant under negation. -/
lemma homInvMatNorm_neg {R : Type*} [SeminormedRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : homInvMatNorm (-A) = homInvMatNorm A := by
  simp [homInvMatNorm]

/-- The `L∞`-operator norm is submultiplicative. -/
lemma homInvMatNorm_mul_le {R : Type*} [SeminormedRing R] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) :
    homInvMatNorm (A * B) ≤ homInvMatNorm A * homInvMatNorm B := by
  letI := Matrix.linftyOpSeminormedAddCommGroup (m := Fin n) (n := Fin n) (α := R)
  simpa [homInvMatNorm, Matrix.linfty_opNNNorm_def] using Matrix.linfty_opNNNorm_mul A B

/-- Homotopy invariance: a continuous path of idempotent matrices over a closed subalgebra of a
complex Banach algebra (e.g. `C(X, ℂ)` for compact `X`, or `C(T, ℂ) × C(D, ℂ)`) has constant
class in `K₀`. -/
theorem homotopy_inv (𝔄 : Type) [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄]
    (R : Subalgebra ℂ 𝔄) (hR : IsClosed (R : Set 𝔄)) (n : ℕ)
    (γ : unitInterval → Matrix (Fin n) (Fin n) R) (hγ : Continuous γ)
    (hidem : ∀ t, γ t * γ t = γ t) :
    cls (⟨n, γ 0⟩ : Mat R) = cls ⟨n, γ 1⟩ := by
  haveI := hR.completeSpace_coe
  -- Around every point the class is constant.
  have hloc : ∀ t : unitInterval, ∀ᶠ s in 𝓝 t,
      cls (⟨n, γ s⟩ : Mat R) = cls ⟨n, γ t⟩ := by
    intro t
    -- `M` bounds the entries of `2 * γ t - 1` through the `L∞`-operator norm
    set M : NNReal := homInvMatNorm (2 * γ t - 1) with hM
    -- allowed size of an entry of `γ s - γ t`
    set e : NNReal := 1 / ((M + 1) * ((n : NNReal) + 1)) with he
    have he0 : 0 < e := by rw [he]; positivity
    -- the crucial numerical estimate `M * (n * e) < 1`
    have hMe : M * ((n : NNReal) * e) < 1 := by
      have heco : (e : ℝ) = 1 / (((M : ℝ) + 1) * ((n : ℝ) + 1)) := by
        rw [he]; push_cast; rfl
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [← NNReal.coe_lt_coe, NNReal.coe_one, NNReal.coe_mul, NNReal.coe_mul, heco,
        NNReal.coe_natCast]
      rw [show ((M : ℝ) * ((n : ℝ) * (1 / (((M : ℝ) + 1) * ((n : ℝ) + 1))))) =
        (M : ℝ) * (n : ℝ) / (((M : ℝ) + 1) * ((n : ℝ) + 1)) by ring]
      rw [div_lt_one (by positivity)]
      nlinarith [M.coe_nonneg, hn0]
    -- continuity of the entries
    have hclose : ∀ᶠ s in 𝓝 t, ∀ i j : Fin n, ‖γ s i j - γ t i j‖₊ < e := by
      refine Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => ?_
      rw [Metric.eventually_nhds_iff]
      obtain ⟨δ, hδ, hδ'⟩ :=
        (Metric.continuousAt_iff.mp ((hγ.matrix_elem i j).continuousAt)) (e : ℝ)
          (by exact_mod_cast he0)
      refine ⟨δ, hδ, fun s hs => ?_⟩
      have h := hδ' hs
      rw [dist_eq_norm] at h
      exact_mod_cast h
    filter_upwards [hclose] with s hs
    have hMnn : (0 : NNReal) ≤ homInvMatNorm (2 * γ t - 1) := zero_le
    have hB : homInvMatNorm (γ s - γ t) ≤ (n : NNReal) * e := by
      refine homInvMatNorm_le_card_mul _ fun i j => le_of_lt ?_
      simpa using hs i j
    -- the perturbation is small, so the conjugating element is a unit
    have hcrit : homInvMatNorm ((2 * γ t - 1) * (γ s - γ t)) < 1 := by
      calc homInvMatNorm ((2 * γ t - 1) * (γ s - γ t))
          ≤ homInvMatNorm (2 * γ t - 1) * homInvMatNorm (γ s - γ t) :=
            homInvMatNorm_mul_le _ _
        _ ≤ homInvMatNorm (2 * γ t - 1) * ((n : NNReal) * e) :=
            mul_le_mul_of_nonneg_left hB hMnn
        _ = M * ((n : NNReal) * e) := by rw [hM]
        _ < 1 := hMe
    have hneg : homInvMatNorm (-((2 * γ t - 1) * (γ s - γ t))) < 1 := by
      rw [homInvMatNorm_neg]; exact hcrit
    have hunit : IsUnit (1 + (2 * γ t - 1) * (γ s - γ t)) := by
      have h := isUnit_one_sub_of_matNorm_lt_one (-((2 * γ t - 1) * (γ s - γ t))) hneg
      simpa using h
    -- conjugate idempotents have equal `K₀`-class
    obtain ⟨u, hu⟩ := idem_close_conj_of_isUnit (hidem t) (hidem s) hunit
    exact (homInv_cls_eq_of_conj (γ t) (γ s) (hidem t) (hidem s) u hu).symm
  have hf : IsLocallyConstant (fun t : unitInterval => cls (⟨n, γ t⟩ : Mat R)) :=
    (IsLocallyConstant.iff_eventually_eq _).2 hloc
  exact hf.apply_eq_of_preconnectedSpace 0 1

end Work.KT
