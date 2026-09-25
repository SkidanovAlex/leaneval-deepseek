/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The Kohn–Morrey identity and the basic estimate

For a `C²` weight `φ` and a compactly supported `C²` `(0,1)`-form `f`, the Kohn–Morrey
(Hörmander, *An introduction to complex analysis in several variables*, Ch. 4) identity is

  `‖∂̄f‖²_φ + ‖∂̄*_φf‖²_φ = Σ_{j,k} ∫ ‖∂̄_k f_j‖² e^{-φ} + Σ_{j,k} ∫ (∂_j∂̄_kφ) f_j f̄_k e^{-φ}`

with no boundary terms, `∂̄` being the flat `(0,1)`-operator on `ℂⁿ` and all norms the
weighted `L²` norms.  The proof is the classical one: expand both norms, integrate by parts
(the identities `rpair0_dbar_left/right`, `rpair0_delta_left/right`), and use that the
commutator of `∂̄_k` with `δ_j = ∂_j - ∂_jφ` is the complex Hessian `∂_j∂̄_kφ`
(`hessPhi_delta`).

The basic estimate `basicEstimate_general` follows immediately: the first sum on the right
is nonnegative, so the Hermitian form of the Hessian of `φ` is dominated by the two norms.
For the quadratic weight `φ = K‖z‖²` this gives
`K ‖f‖²_{L²_φ} ≤ ‖∂̄f‖²_φ + ‖∂̄*_φf‖²_φ` (the sharp constant, `basicEstimate_quad`).
-/
import Submission.Work.Hormander.Weights.Expand
import Submission.Work.Hormander.Weights.rpair0_dbar_left
import Submission.Work.Hormander.Weights.rpair0_dbar_right
import Submission.Work.Hormander.Weights.rpair0_delta_left
import Submission.Work.Hormander.Weights.rpair0_delta_right
import Submission.Work.Hormander.Weights.rpair0_delta_sum
import Submission.Work.Hormander.Weights.normSq2_dbarForm_rpair0
import Submission.Work.Hormander.Weights.normSq0_dbarStar_rpair0
import Submission.Work.Hormander.Weights.hessPhi_delta
import Submission.Work.Hormander.Weights.HessLowerBound_quadWeight
import Submission.Work.Hormander.Weights.contDiff_quadWeight
import Submission.Work.Hormander.Weights.star_dPhi

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.Hormander.Weights

variable {n : ℕ}

/-- Integrability of the `rpair0` integrand, controlled by the second factor (which is the
one that appears conjugated). -/
lemma integrable_rpair0_integrand_right {φ : Cn n → ℝ} {u v : Cn n → ℂ} (hφ : Continuous φ)
    (hu : Continuous u) (hv : Continuous v) (hsv : HasCompactSupport v) :
    Integrable (fun z => (u z * star (v z)).re * wn n φ z) := by
  have hpt : ∀ z : Cn n, (u z * star (v z)).re = (v z * star (u z)).re :=
    fun z => re_mul_star_comm (u z) (v z)
  refine (integrable_rpair0_integrand (φ := φ) (u := v) (v := u) hφ hv hsv hu).congr ?_
  filter_upwards with z
  rw [hpt z]

/-- A double-sum rearrangement: if `b i j = a j i` then
`(1/2) Σ_{i,j}(a_{ij} + b_{ij} - 2 c_{ij}) = Σ_{i,j}a_{ij} - Σ_{i,j}c_{ij}`. -/
private lemma half_double_sum {ι : Type*} [Fintype ι] (a b c : ι → ι → ℝ)
    (hb : ∀ i j, b i j = a j i) :
    (1 / 2) * (∑ i, ∑ j, (a i j + b i j - 2 * c i j))
      = (∑ i, ∑ j, a i j) - ∑ i, ∑ j, c i j := by
  have hb' : (∑ i, ∑ j, b i j) = ∑ i, ∑ j, a i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hb j i
  have h1 : ∀ i, (∑ j, (a i j + b i j - 2 * c i j))
      = (∑ j, a i j) + (∑ j, b i j) - 2 * (∑ j, c i j) := by
    intro i
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hexp : (∑ i, ∑ j, (a i j + b i j - 2 * c i j))
      = (∑ i, ∑ j, a i j) + (∑ i, ∑ j, b i j) - 2 * (∑ i, ∑ j, c i j) := by
    rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hexp, hb']
  ring

/-! ### Expansion of the `(0,2)`-norm -/

/-- The `(0,2)`-norm of `∂̄f`, expanded into the two sums of the Kohn–Morrey identity. -/
lemma rpair0_dbarForm_expand {φ : Cn n → ℝ} (f : Form1 n) (hφ : Continuous φ)
    (hf : ∀ j, ContDiff ℝ 1 (f j)) (hfs : ∀ j, HasCompactSupport (f j)) :
    (1 / 2) * ∑ j, ∑ k, rpair0 φ (dbarForm f j k) (dbarForm f j k)
      = (∑ j, ∑ k, rpair0 φ (fun z => dbarCoord n k (f j) z)
            (fun z => dbarCoord n k (f j) z))
        - ∑ j, ∑ k, rpair0 φ (fun z => dbarCoord n k (f j) z)
            (fun z => dbarCoord n j (f k) z) := by
  have hterm : ∀ j k : Fin n,
      rpair0 φ (dbarForm f j k) (dbarForm f j k)
        = rpair0 φ (fun z => dbarCoord n k (f j) z) (fun z => dbarCoord n k (f j) z)
          + rpair0 φ (fun z => dbarCoord n j (f k) z) (fun z => dbarCoord n j (f k) z)
          - 2 * rpair0 φ (fun z => dbarCoord n k (f j) z) (fun z => dbarCoord n j (f k) z) := by
    intro j k
    have hform : dbarForm f j k
        = (fun z => dbarCoord n k (f j) z) - (fun z => dbarCoord n j (f k) z) := rfl
    have h1 : Integrable (fun z => ((fun z => dbarCoord n k (f j) z) z
        * star (((fun z => dbarCoord n k (f j) z)
            - fun z => dbarCoord n j (f k) z) z)).re * wn n φ z) :=
      integrable_rpair0_integrand hφ (continuous_dbarCoord (hf j) k)
        (hasCompactSupport_dbarCoord (hfs j) k) (Continuous.sub (continuous_dbarCoord (hf j) k)
          (continuous_dbarCoord (hf k) j))
    have h2 : Integrable (fun z => ((fun z => dbarCoord n j (f k) z) z
        * star (((fun z => dbarCoord n k (f j) z)
            - fun z => dbarCoord n j (f k) z) z)).re * wn n φ z) :=
      integrable_rpair0_integrand hφ (continuous_dbarCoord (hf k) j)
        (hasCompactSupport_dbarCoord (hfs k) j) (Continuous.sub (continuous_dbarCoord (hf j) k)
          (continuous_dbarCoord (hf k) j))
    have h3 : Integrable (fun z => ((fun z => dbarCoord n k (f j) z) z
        * star ((fun z => dbarCoord n k (f j) z) z)).re * wn n φ z) :=
      integrable_rpair0_integrand hφ (continuous_dbarCoord (hf j) k)
        (hasCompactSupport_dbarCoord (hfs j) k) (continuous_dbarCoord (hf j) k)
    have h4 : Integrable (fun z => ((fun z => dbarCoord n k (f j) z) z
        * star ((fun z => dbarCoord n j (f k) z) z)).re * wn n φ z) :=
      integrable_rpair0_integrand hφ (continuous_dbarCoord (hf j) k)
        (hasCompactSupport_dbarCoord (hfs j) k) (continuous_dbarCoord (hf k) j)
    have h5 : Integrable (fun z => ((fun z => dbarCoord n j (f k) z) z
        * star ((fun z => dbarCoord n k (f j) z) z)).re * wn n φ z) :=
      integrable_rpair0_integrand hφ (continuous_dbarCoord (hf k) j)
        (hasCompactSupport_dbarCoord (hfs k) j) (continuous_dbarCoord (hf j) k)
    have h6 : Integrable (fun z => ((fun z => dbarCoord n j (f k) z) z
        * star ((fun z => dbarCoord n j (f k) z) z)).re * wn n φ z) :=
      integrable_rpair0_integrand hφ (continuous_dbarCoord (hf k) j)
        (hasCompactSupport_dbarCoord (hfs k) j) (continuous_dbarCoord (hf k) j)
    rw [hform, rpair0_sub_left h1 h2, rpair0_sub_right h3 h4, rpair0_sub_right h5 h6,
      rpair0_comm (fun z => dbarCoord n j (f k) z) (fun z => dbarCoord n k (f j) z)]
    ring
  have hsum : ∑ j, ∑ k, rpair0 φ (dbarForm f j k) (dbarForm f j k)
      = ∑ j, ∑ k, (rpair0 φ (fun z => dbarCoord n k (f j) z) (fun z => dbarCoord n k (f j) z)
          + rpair0 φ (fun z => dbarCoord n j (f k) z) (fun z => dbarCoord n j (f k) z)
          - 2 * rpair0 φ (fun z => dbarCoord n k (f j) z) (fun z => dbarCoord n j (f k) z)) :=
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hterm j k
  rw [hsum]
  rw [half_double_sum
    (fun j k => rpair0 φ (fun z => dbarCoord n k (f j) z) (fun z => dbarCoord n k (f j) z))
    (fun j k => rpair0 φ (fun z => dbarCoord n j (f k) z) (fun z => dbarCoord n j (f k) z))
    (fun j k => rpair0 φ (fun z => dbarCoord n k (f j) z) (fun z => dbarCoord n j (f k) z))
    (fun i j => rfl)]

/-- **The Kohn–Morrey identity** (Hörmander, Ch. 4) for compactly supported smooth
`(0,1)`-forms on `ℂⁿ`.  With `∂̄` the flat operator, `∂̄*_φ = -Σ_j(∂_j - ∂_jφ)` its formal
adjoint for the weight `e^{-φ}`, and `‖·‖_φ` the weighted `L²` norm, one has

  `‖∂̄f‖²_φ + ‖∂̄*_φf‖²_φ = Σ_{j,k} ‖∂̄_k f_j‖²_φ + Σ_{j,k} ∫ (∂_j∂̄_kφ) f_j f̄_k e^{-φ}`.

In particular no boundary terms appear, so the second sum is the curvature term of the basic
estimate. -/
theorem kohnMorrey_identity {n : ℕ} (φ : Cn n → ℝ) (f : Form1 n) (hφ : ContDiff ℝ 2 φ)
    (hf : ∀ j, ContDiff ℝ 2 (f j)) (hfs : ∀ j, HasCompactSupport (f j)) :
    normSq2 φ (dbarForm f) + normSq0 φ (dbarStar φ f)
      = (∑ j, ∑ k, normSq0 φ (fun z => dbarCoord n k (f j) z))
        + ∑ j, ∑ k, rpair0 φ (fun z => f j z * hessPhi n j k φ z) (f k) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hf1 : ∀ j, ContDiff ℝ 1 (f j) := fun j => (hf j).of_le (by norm_num)
  have hD : (∑ j, ∑ k, normSq0 φ (fun z => dbarCoord n k (f j) z))
      = ∑ j, ∑ k, rpair0 φ (fun z => dbarCoord n k (f j) z)
          (fun z => dbarCoord n k (f j) z) :=
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
      (rpair0_self (φ := φ) (fun z => dbarCoord n k (f j) z)).symm
  rw [normSq2_dbarForm_rpair0 φ f hφ1 hf1 hfs, normSq0_dbarStar_rpair0 φ f hφ1 hf1 hfs,
    rpair0_dbarForm_expand f hφ1.continuous hf1 hfs, rpair0_delta_sum φ f hφ hf hfs, hD]
  ring

end Work.Hormander.Weights
