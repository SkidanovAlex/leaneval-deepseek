import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.GE.Api
import Submission.Work.Diff.GE.smp_defs
import Submission.Work.Diff.GE.rmFrame_eq_rot
import Submission.Work.Diff.GE.onFrame_orthogonal_change

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for Hamilton's maximum principle (MP area)

The Frobenius inner product `frobDot`/`frobNorm`/`frobDist`/`frobInfDist` on curvature arrays
`Curv4 n`, its algebra (Cauchy-Schwarz, triangle inequality, comparison with the instance sup norm),
compactness/convexity of the Frobenius balls, the elementary frame-independence lemmas for the
distance to an `O(n)`-invariant family, and membership lemmas.

This module is the *base* of the MP area: the delegated lemmas
(`Submission.Work.Diff.MP.{frobDot_rot, isCompact_frobBall, frob_nearest_supporting,
frobDot_nonpos_of_frobDist_min, dini_first_exit, ode_push_forward_of_invariant,
hessAt_nonpos_of_isLocalMax, frobInfDist_rmFrame_eq, max_principle, ...}`) import it, and the target
theorem file `Submission.Work.Diff.MP.hamilton_mp` imports them.  See `NOTES.md` in this directory
for the design of the remaining proof.

## Design

The proof is the *time-dependent maximum principle* of Chow–Lu (arXiv math/0211209, Theorem 2.3)
in the concrete setting of curvature arrays `Curv4 n`:

* `frobDot`, `frobNorm`, `frobDist` are the **Frobenius** inner product / norm / distance on
  `Curv4 n`.  They are needed (rather than the instance sup norm) because the maximum-principle
  argument uses the Euclidean *outward normal* of a convex set at its nearest point and the
  expansion `|w + h v|² = |w|² + 2 h ⟪w, v⟫ + O(h²)`.
* `MPData` collects the "reaction–diffusion" data: a family of curvature arrays `R t x` together
  with its Laplacian part `dR t x = lapRmFrame (G t) x (e t)` (the remaining piece of `ΔR`),
  the closed convex family `K t` (the pinching family intersected with a large ball), the uniform
  first-order expansion in time and the "spatial maximum ⇒ Laplacian ≤ 0" condition.
* `MPData.maxPrinciple` is the Chow–Lu theorem in this setting.
-/

set_option maxHeartbeats 2000000

namespace Work.Diff.MP

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-! ## The Frobenius inner product on `Curv4 n` -/

variable {n : ℕ}

/-- Frobenius inner product of two curvature arrays. -/
noncomputable def frobDot (R S : Curv4 n) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * S i j k l

/-- Frobenius norm of a curvature array. -/
noncomputable def frobNorm (R : Curv4 n) : ℝ := Real.sqrt (frobDot R R)

/-- Frobenius distance of two curvature arrays. -/
noncomputable def frobDist (R S : Curv4 n) : ℝ := frobNorm (R - S)

/-- The Frobenius distance from `P` to the set `K` (the analogue of `Metric.infDist` for the
Frobenius distance on curvature arrays; `0` for `K = ∅`, as in `Metric.infDist`). -/
noncomputable def frobInfDist (P : Curv4 n) (K : Set (Curv4 n)) : ℝ :=
  sInf ((fun S => frobDist P S) '' K)

/-- The Frobenius ball of radius `ρ`. -/
def frobBall (ρ : ℝ) : Set (Curv4 n) := {R | frobNorm R ≤ ρ}

@[simp] theorem frobBall_mem {ρ : ℝ} {R : Curv4 n} : R ∈ frobBall (n := n) ρ ↔ frobNorm R ≤ ρ :=
  Iff.rfl


/-! ## Elementary algebra of the Frobenius form -/

theorem frobDot_comm (R S : Curv4 n) : frobDot R S = frobDot S R := by
  simp only [frobDot]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem frobDot_add_left (R S T : Curv4 n) : frobDot (R + S) T = frobDot R T + frobDot S T := by
  simp only [frobDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem frobDot_add_right (R S T : Curv4 n) : frobDot R (S + T) = frobDot R S + frobDot R T := by
  rw [frobDot_comm R (S + T), frobDot_add_left, frobDot_comm S R, frobDot_comm T R]

theorem frobDot_smul_left (c : ℝ) (R S : Curv4 n) : frobDot (c • R) S = c * frobDot R S := by
  simp only [frobDot, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem frobDot_smul_right (c : ℝ) (R S : Curv4 n) : frobDot R (c • S) = c * frobDot R S := by
  rw [frobDot_comm R (c • S), frobDot_smul_left, frobDot_comm S R]

theorem frobDot_self_nonneg (R : Curv4 n) : 0 ≤ frobDot R R := by
  simp only [frobDot]
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  apply Finset.sum_nonneg; intro k _
  apply Finset.sum_nonneg; intro l _
  exact mul_self_nonneg _

theorem frobSq_eq_frobDot_self (R : Curv4 n) : frobSq R = frobDot R R := by
  simp only [frobSq, frobDot]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => sq (R i j k l)

theorem frobNorm_nonneg (R : Curv4 n) : 0 ≤ frobNorm R := Real.sqrt_nonneg _

theorem frobNorm_sq (R : Curv4 n) : frobNorm R ^ 2 = frobDot R R :=
  Real.sq_sqrt (frobDot_self_nonneg R)

theorem frobDot_self_eq_zero_iff (R : Curv4 n) : frobDot R R = 0 ↔ R = 0 := by
  constructor
  · intro h
    funext i j k l
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg
      (fun j _ => Finset.sum_nonneg (fun k _ => Finset.sum_nonneg
        (fun l _ => mul_self_nonneg _))))).mp h
    have h3 := h2 i (Finset.mem_univ i)
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Finset.sum_nonneg
      (fun k _ => Finset.sum_nonneg (fun l _ => mul_self_nonneg _)))).mp h3
    have h5 := h4 j (Finset.mem_univ j)
    have h6 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => Finset.sum_nonneg (fun l _ => mul_self_nonneg _))).mp h5
    have h7 := h6 k (Finset.mem_univ k)
    have h8 := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => mul_self_nonneg _)).mp h7
    have h9 := h8 l (Finset.mem_univ l)
    exact mul_self_eq_zero.mp h9
  · intro h
    rw [h]
    simp [frobDot]

theorem frobNorm_eq_zero_iff (R : Curv4 n) : frobNorm R = 0 ↔ R = 0 := by
  rw [frobNorm, Real.sqrt_eq_zero']
  exact ⟨fun h => frobDot_self_eq_zero_iff R |>.mp (le_antisymm h (frobDot_self_nonneg R)),
    fun h => by rw [h]; simp [frobDot]⟩

theorem frobDot_sub_left (R S T : Curv4 n) : frobDot (R - S) T = frobDot R T - frobDot S T := by
  rw [sub_eq_add_neg, frobDot_add_left]
  congr 1
  have : (-S : Curv4 n) = (-1 : ℝ) • S := by simp
  rw [this, frobDot_smul_left]
  ring

theorem frobDot_neg_right (R S : Curv4 n) : frobDot R (-S) = - frobDot R S := by
  have : (-S : Curv4 n) = (-1 : ℝ) • S := by simp
  rw [this, frobDot_smul_right]
  ring

theorem frobNorm_zero : frobNorm (0 : Curv4 n) = 0 := by
  simp [frobNorm, frobDot]

theorem frobNorm_neg (R : Curv4 n) : frobNorm (-R) = frobNorm R := by
  have h : frobDot (-R) (-R) = frobDot R R := by
    rw [show (-R : Curv4 n) = (-1 : ℝ) • R by simp, frobDot_smul_left, frobDot_smul_right]
    ring
  simp only [frobNorm, h]

theorem frob_cauchy_schwarz (R S : Curv4 n) :
    |frobDot R S| ≤ frobNorm R * frobNorm S := by
  have hexpand : ∀ t : ℝ,
      frobDot (R + t • S) (R + t • S) = frobDot R R + 2 * t * frobDot R S + t ^ 2 * frobDot S S := by
    intro t
    rw [frobDot_add_left, frobDot_add_right, frobDot_smul_left, frobDot_smul_right,
      frobDot_add_right, frobDot_smul_right, frobDot_comm S R]
    ring
  by_cases hS0 : frobDot S S = 0
  · have hS : S = 0 := (frobDot_self_eq_zero_iff S).mp hS0
    have hRS : frobDot R S = 0 := by rw [hS]; simp [frobDot]
    rw [hRS, hS, frobNorm_zero, abs_zero, mul_zero]
  · have hSpos : 0 < frobDot S S := lt_of_le_of_ne (frobDot_self_nonneg S) (Ne.symm hS0)
    have hkey : frobDot R S ^ 2 ≤ frobDot R R * frobDot S S := by
      have h0 : 0 ≤ frobDot R R + 2 * (-(frobDot R S / frobDot S S)) * frobDot R S
          + (-(frobDot R S / frobDot S S)) ^ 2 * frobDot S S := by
        rw [← hexpand]; exact frobDot_self_nonneg _
      have hsimp : frobDot R R + 2 * (-(frobDot R S / frobDot S S)) * frobDot R S
          + (-(frobDot R S / frobDot S S)) ^ 2 * frobDot S S
          = frobDot R R - frobDot R S ^ 2 / frobDot S S := by
        field_simp
        ring
      rw [hsimp] at h0
      have h1 : frobDot R S ^ 2 / frobDot S S ≤ frobDot R R := by linarith
      have h2 : frobDot R S ^ 2 ≤ frobDot R R * frobDot S S := by
        rw [div_le_iff₀ hSpos] at h1
        linarith
      exact h2
    have h3 : frobDot R S ^ 2 ≤ (frobNorm R * frobNorm S) ^ 2 := by
      rw [mul_pow, frobNorm_sq, frobNorm_sq]
      exact hkey
    have h4 : 0 ≤ frobNorm R * frobNorm S := mul_nonneg (frobNorm_nonneg R) (frobNorm_nonneg S)
    have h5 : |frobDot R S| ≤ |frobNorm R * frobNorm S| := sq_le_sq.mp h3
    rwa [abs_of_nonneg h4] at h5

theorem frobNorm_smul (c : ℝ) (R : Curv4 n) : frobNorm (c • R) = |c| * frobNorm R := by
  have h : frobDot (c • R) (c • R) = (|c| * frobNorm R) ^ 2 := by
    rw [frobDot_smul_left, frobDot_smul_right, ← frobNorm_sq]
    rw [mul_pow, sq_abs]
    ring
  rw [frobNorm, h, Real.sqrt_sq (mul_nonneg (abs_nonneg c) (frobNorm_nonneg R))]

theorem frobNorm_add_le (R S : Curv4 n) : frobNorm (R + S) ≤ frobNorm R + frobNorm S := by
  have hsq : frobNorm (R + S) ^ 2 = frobNorm R ^ 2 + 2 * frobDot R S + frobNorm S ^ 2 := by
    rw [frobNorm_sq, frobDot_add_left, frobDot_add_right, frobDot_add_right, frobDot_comm S R,
      frobNorm_sq R, frobNorm_sq S]
    ring
  have h1 : frobDot R S ≤ frobNorm R * frobNorm S := (abs_le.mp (frob_cauchy_schwarz R S)).2
  have hR := frobNorm_nonneg R
  have hS := frobNorm_nonneg S
  have h2 : frobNorm (R + S) ^ 2 ≤ (frobNorm R + frobNorm S) ^ 2 := by
    rw [hsq]; nlinarith [h1, hR, hS]
  have h3 : frobNorm (R + S) ≤ frobNorm R + frobNorm S := by
    have h4 : |frobNorm (R + S)| ≤ |frobNorm R + frobNorm S| := sq_le_sq.mp h2
    rwa [abs_of_nonneg (frobNorm_nonneg _), abs_of_nonneg (add_nonneg hR hS)] at h4
  exact h3

theorem frobDist_nonneg (R S : Curv4 n) : 0 ≤ frobDist R S := frobNorm_nonneg _

theorem frobDist_eq_zero_iff (R S : Curv4 n) : frobDist R S = 0 ↔ R = S := by
  rw [frobDist, frobNorm_eq_zero_iff, sub_eq_zero]

theorem frobDist_comm (R S : Curv4 n) : frobDist R S = frobDist S R := by
  simp only [frobDist]
  rw [← neg_sub R S, frobNorm_neg]

theorem frobDist_triangle (R S T : Curv4 n) : frobDist R T ≤ frobDist R S + frobDist S T := by
  have h : R - T = (R - S) + (S - T) := by abel
  rw [frobDist, h]
  exact frobNorm_add_le _ _

theorem frobInfDist_le {P : Curv4 n} {K : Set (Curv4 n)} {S : Curv4 n} (hS : S ∈ K) :
    frobInfDist P K ≤ frobDist P S :=
  csInf_le ⟨0, by rintro _ ⟨T, -, rfl⟩; exact frobDist_nonneg P T⟩ ⟨S, hS, rfl⟩

theorem le_frobInfDist {P : Curv4 n} {K : Set (Curv4 n)} {m : ℝ} (hKne : K.Nonempty)
    (h : ∀ S ∈ K, m ≤ frobDist P S) : m ≤ frobInfDist P K :=
  le_csInf ⟨frobDist P hKne.some, ⟨hKne.some, hKne.some_mem, rfl⟩⟩
    (by rintro _ ⟨S, hS, rfl⟩; exact h S hS)

theorem frobInfDist_nonneg (P : Curv4 n) (K : Set (Curv4 n)) : 0 ≤ frobInfDist P K := by
  rcases Set.eq_empty_or_nonempty K with hK | hKne
  · rw [frobInfDist, hK, Set.image_empty]; exact le_of_eq (Real.sInf_empty).symm
  · exact le_frobInfDist hKne (fun S _ => frobDist_nonneg P S)

theorem frobInfDist_eq_zero_of_mem {P : Curv4 n} {K : Set (Curv4 n)} (hP : P ∈ K) :
    frobInfDist P K = 0 :=
  le_antisymm (le_of_le_of_eq (frobInfDist_le hP) (by rw [frobDist_eq_zero_iff])) (frobInfDist_nonneg P K)

/-- Each coordinate is bounded by the Frobenius norm. -/
theorem abs_coord_le_frobNorm (R : Curv4 n) (i j k l : Fin n) : |R i j k l| ≤ frobNorm R := by
  have h1 : R i j k l ^ 2 ≤ ∑ d, R i j k d ^ 2 :=
    Finset.single_le_sum (fun d _ => sq_nonneg _) (Finset.mem_univ l)
  have h2 : (∑ d, R i j k d ^ 2) ≤ ∑ c, ∑ d, R i j c d ^ 2 :=
    Finset.single_le_sum (fun c _ => Finset.sum_nonneg (fun d _ => sq_nonneg _)) (Finset.mem_univ k)
  have h3 : (∑ c, ∑ d, R i j c d ^ 2) ≤ ∑ b, ∑ c, ∑ d, R i b c d ^ 2 :=
    Finset.single_le_sum (fun b _ => Finset.sum_nonneg (fun c _ =>
      Finset.sum_nonneg (fun d _ => sq_nonneg _))) (Finset.mem_univ j)
  have h4 : (∑ b, ∑ c, ∑ d, R i b c d ^ 2) ≤ ∑ a, ∑ b, ∑ c, ∑ d, R a b c d ^ 2 :=
    Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ =>
      Finset.sum_nonneg (fun c _ => Finset.sum_nonneg (fun d _ => sq_nonneg _))))
      (Finset.mem_univ i)
  have hsum : R i j k l ^ 2 ≤ frobDot R R := by
    calc R i j k l ^ 2 ≤ ∑ d, R i j k d ^ 2 := h1
      _ ≤ ∑ c, ∑ d, R i j c d ^ 2 := h2
      _ ≤ ∑ b, ∑ c, ∑ d, R i b c d ^ 2 := h3
      _ ≤ ∑ a, ∑ b, ∑ c, ∑ d, R a b c d ^ 2 := h4
      _ = frobDot R R := by simp [frobDot, sq]
  have h5 : Real.sqrt (R i j k l ^ 2) ≤ Real.sqrt (frobDot R R) := Real.sqrt_le_sqrt hsum
  simpa [frobNorm, Real.sqrt_sq_eq_abs] using h5

/-- If every coordinate is bounded by `C`, so is the sup norm (a Pi-type lemma). -/
theorem norm_pi_le {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, SeminormedAddGroup (G i)]
    (f : ∀ i, G i) {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ‖f i‖ ≤ C) : ‖f‖ ≤ C := by
  rw [Pi.norm_def]
  have key : Finset.univ.sup (fun b => ‖f b‖₊) ≤ Real.toNNReal C := by
    apply Finset.sup_le
    intro i _
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal C hC]
    simpa using h i
  have h2 : ((Finset.univ.sup (fun b => ‖f b‖₊) : NNReal) : ℝ) ≤ C := by
    rw [← Real.coe_toNNReal C hC]
    exact NNReal.coe_le_coe.mpr key
  simpa using h2

theorem norm_le_frobNorm (R : Curv4 n) : ‖R‖ ≤ frobNorm R := by
  have h0 : 0 ≤ frobNorm R := frobNorm_nonneg R
  refine norm_pi_le R h0 (fun i => ?_)
  refine norm_pi_le (R i) h0 (fun j => ?_)
  refine norm_pi_le (R i j) h0 (fun k => ?_)
  refine norm_pi_le (R i j k) h0 (fun l => ?_)
  simpa using abs_coord_le_frobNorm R i j k l

theorem coord_le_norm (R : Curv4 n) (i j k l : Fin n) : |R i j k l| ≤ ‖R‖ := by
  have h1 : ‖R i j k l‖ ≤ ‖R i j k‖ := norm_le_pi_norm (R i j k) l
  have h2 : ‖R i j k‖ ≤ ‖R i j‖ := norm_le_pi_norm (R i j) k
  have h3 : ‖R i j‖ ≤ ‖R i‖ := norm_le_pi_norm (R i) j
  have h4 : ‖R i‖ ≤ ‖R‖ := norm_le_pi_norm R i
  have h5 : ‖R i j k l‖ ≤ ‖R‖ := le_trans h1 (le_trans h2 (le_trans h3 h4))
  simpa using h5

theorem frobNorm_le_mul_norm (R : Curv4 n) : frobNorm R ≤ (n : ℝ) ^ 2 * ‖R‖ := by
  have h : frobDot R R ≤ ((n : ℝ) ^ 2 * ‖R‖) ^ 2 := by
    have hb : ∀ i j k l : Fin n, R i j k l * R i j k l ≤ ‖R‖ * ‖R‖ := by
      intro i j k l
      have h1 : |R i j k l| ≤ ‖R‖ := coord_le_norm R i j k l
      have h2 := abs_le.mp h1
      nlinarith [h2.1, h2.2, norm_nonneg R]
    calc frobDot R R
        = ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * R i j k l := rfl
      _ ≤ ∑ i, ∑ j, ∑ k, ∑ l, ‖R‖ * ‖R‖ := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          apply Finset.sum_le_sum; intro k _
          apply Finset.sum_le_sum; intro l _
          exact hb i j k l
      _ = (n : ℝ) ^ 4 * (‖R‖ * ‖R‖) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          ring
      _ = ((n : ℝ) ^ 2 * ‖R‖) ^ 2 := by ring
  have hnn : 0 ≤ (n : ℝ) ^ 2 * ‖R‖ := by positivity
  rw [frobNorm]
  exact le_trans (Real.sqrt_le_sqrt h) (le_of_eq (Real.sqrt_sq hnn))


/-- Membership from a vanishing Frobenius distance, for closed nonempty `K`.  (This is the bridge
from the maximum-principle conclusion `frobInfDist (rmC (G t) x) (K t) = 0` back to `rmC (G t) x ∈ K t`.
Note that `K.Nonempty` is needed: for `K = ∅` one has `frobInfDist P ∅ = 0`.) -/
theorem mem_of_frobInfDist_eq_zero {P : Curv4 n} {K : Set (Curv4 n)} (hKcl : IsClosed K)
    (hKne : K.Nonempty) (h : frobInfDist P K = 0) : P ∈ K := by
  refine hKcl.closure_subset ?_
  rw [Metric.mem_closure_iff]
  intro ε hε
  by_contra hcon
  push_neg at hcon
  have hle : ε ≤ frobInfDist P K :=
    le_frobInfDist hKne (fun S hS => le_trans (hcon S hS) (norm_le_frobNorm (P - S)))
  rw [h] at hle
  linarith

/-! ## Frames, `O(n)`-invariance and the curvature of a metric

The frozen `CurvIn g F` asks for membership of the curvature components in *every* orthonormal
frame.  Since `F` is `O(n)`-invariant (a field of `IsInvariantFamily`), membership in one
orthonormal frame implies membership in all of them (`rmFrame_mem_of_rmC_mem`), and likewise the
Frobenius distance from the curvature to `F t` is independent of the orthonormal frame used
(`frobInfDist_rmFrame_eq`). -/

/-- Given membership of the `onFrame`-components, membership in every orthonormal frame follows from
`O(n)`-invariance of the family. -/
theorem rmFrame_mem_of_rmC_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) (F : Set (Curv4 (Module.finrank ℝ E)))
    (hFrot : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ, ∀ R ∈ F, rot A R ∈ F)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (h : rmC g x ∈ F) :
    rmFrame g x e ∈ F := by
  obtain ⟨A, hA, hAe⟩ :=
    Work.Diff.GE.onFrame_orthogonal_change g x (onFrame g x) e
      (Work.Diff.GE.isONFrame_onFrame g x) he
  rw [Work.Diff.GE.rmFrame_eq_rot hLC g x (onFrame g x) e A hAe]
  exact hFrot A hA (rmC g x) h


/-- The `t`-fibre of a family whose space–time track is closed is closed. -/
theorem isClosed_fibre_of_isClosed_track {n : ℕ} {F : ℝ → Set (Curv4 n)}
    (h : IsClosed {p : ℝ × Curv4 n | p.2 ∈ F p.1}) (t : ℝ) : IsClosed (F t) := by
  have hcont : Continuous (fun S : Curv4 n => ((t, S) : ℝ × Curv4 n)) :=
    Continuous.prodMk continuous_const continuous_id
  have := h.preimage hcont
  convert this using 1
  ext S
  simp

/-- The `onFrame`-curvature at time `0` lies in `F 0` when the curvature lies in `F 0` in every
orthonormal frame. -/
theorem rmC_mem_of_curvIn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {G : ℝ → SMet I M} {F : ℝ → Set (Curv4 (Module.finrank ℝ E))}
    (h : CurvIn (G 0) (F 0)) (x : M) : rmC (G 0) x ∈ F 0 :=
  h x (onFrame (G 0) x) (Work.Diff.GE.isONFrame_onFrame (G 0) x)


theorem convex_frobBall (ρ : ℝ) : Convex ℝ (frobBall (n := n) ρ) := by
  intro P hP Q hQ a b ha hb hab
  simp only [frobBall_mem] at hP hQ ⊢
  calc frobNorm (a • P + b • Q) ≤ frobNorm (a • P) + frobNorm (b • Q) := frobNorm_add_le _ _
    _ = |a| * frobNorm P + |b| * frobNorm Q := by
        rw [frobNorm_smul, frobNorm_smul]
    _ = a * frobNorm P + b * frobNorm Q := by rw [abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * ρ + b * ρ := by
        exact add_le_add (mul_le_mul_of_nonneg_left hP ha) (mul_le_mul_of_nonneg_left hQ hb)
    _ = ρ := by rw [← add_mul, hab, one_mul]

theorem continuous_frobNorm : Continuous (frobNorm (n := n)) := by
  rw [continuous_iff_continuousAt]
  intro R
  refine Metric.continuousAt_iff.mpr fun ε hε => ⟨ε / ((n : ℝ) ^ 2 + 1), by positivity, ?_⟩
  intro S hS
  have h1 : |frobNorm S - frobNorm R| ≤ frobNorm (S - R) := by
    rw [abs_sub_le_iff]
    refine ⟨?_, ?_⟩
    · have := frobNorm_add_le (S - R) R
      rw [sub_add_cancel] at this
      linarith
    · have := frobNorm_add_le (R - S) S
      rw [sub_add_cancel] at this
      have hneg : frobNorm (R - S) = frobNorm (S - R) := by rw [← neg_sub S R, frobNorm_neg]
      linarith [this, le_of_eq hneg]
  have h2 : frobNorm (S - R) ≤ (n : ℝ) ^ 2 * ‖S - R‖ := frobNorm_le_mul_norm _
  have h3 : ‖S - R‖ < ε / ((n : ℝ) ^ 2 + 1) := by simpa [dist_eq_norm] using hS
  have h4 : (n : ℝ) ^ 2 * ‖S - R‖ = ((n : ℝ) ^ 2 + 1) * ‖S - R‖ - ‖S - R‖ := by ring
  have h5 : ((n : ℝ) ^ 2 + 1) * ‖S - R‖ < ε := by
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < (n : ℝ) ^ 2 + 1)] at h3
    linarith
  have h6 : |frobNorm S - frobNorm R| < ε := by
    linarith [h1, h2, h3, h4, h5, norm_nonneg (S - R)]
  simpa [Real.dist_eq] using h6

theorem isClosed_frobBall (ρ : ℝ) : IsClosed (frobBall (n := n) ρ) :=
  isClosed_Iic.preimage continuous_frobNorm

end Work.Diff.MP
