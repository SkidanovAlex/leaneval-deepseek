import Submission.NBody.Tonelli
import Submission.NBody.FirstVariation
import Mathlib

/-!
# Geometry of separated configurations (Liu--Yan--Zhou route)

This module starts the alternative, purely geometric proof of the main theorem of
Maderna--Venturelli (following J. Liu, D. Yan, Y. Zhou, *Existence of hyperbolic motions to a
class of Hamiltonians and generalized N-body system via a geometric approach*).  The proof
avoids Chazy's theorem, the Marchal--Saari theorem and weak KAM theory; it only uses estimates on
the Euclidean length and the angle of action minimisers, plus (for collision-freeness) Marchal's
theorem.

Here we set up the elementary geometry of *separated* configurations: a configuration `x` is
`Separated x ν` when all the mutual distances `dist (x i) (x j)` (`i ≠ j`) are at least `ν`.
The key lemmas are the stability of separation under small perturbations, the monotonicity of the
pair distances along a ray with non-negative angles (Lemma 2 of Liu--Yan--Zhou), and the explicit
"escape along `a`" estimate `findxast`.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- A configuration is `ν`-separated when all distinct bodies are at distance at least `ν`. -/
def Separated (x : EN E N) (ν : ℝ) : Prop := ∀ i j, i ≠ j → ν ≤ dist (x i) (x j)

lemma Separated.mono {x : EN E N} {ν ν' : ℝ} (h : Separated x ν') (hle : ν ≤ ν') :
    Separated x ν := fun i j hij => le_trans hle (h i j hij)

/-- Componentwise displacement is bounded by the configuration distance. -/
lemma dist_apply_le_dist {x y : EN E N} (i : Fin N) : dist (x i) (y i) ≤ dist x y := by
  have h : dist (x i) (y i) = ‖(x - y) i‖ := by rw [dist_eq_norm, PiLp.sub_apply]
  rw [h, dist_eq_norm]
  exact norm_apply_le_norm (x - y) i

/-- **Separation is stable under small perturbations** (Liu--Yan--Zhou, Lemma 2.1, first part). -/
lemma Separated.of_dist_le {x y : EN E N} {ν δ : ℝ} (h : Separated x ν)
    (hd : dist y x ≤ δ * ν) : Separated y (ν - 2 * (δ * ν)) := by
  intro i j hij
  have h1 : dist (x i) (x j) ≤ dist (x i) (y i) + dist (y i) (y j) + dist (y j) (x j) := by
    calc dist (x i) (x j) ≤ dist (x i) (y i) + dist (y i) (x j) := dist_triangle _ _ _
      _ ≤ dist (x i) (y i) + (dist (y i) (y j) + dist (y j) (x j)) := by
          gcongr; exact dist_triangle _ _ _
      _ = dist (x i) (y i) + dist (y i) (y j) + dist (y j) (x j) := by ring
  have h2 : dist (x i) (y i) ≤ dist y x := by rw [dist_comm]; exact dist_apply_le_dist i
  have h3 : dist (y j) (x j) ≤ dist y x := dist_apply_le_dist j
  have h4 := h i j hij
  linarith

/-- **The pairwise angles are preserved** (Liu--Yan--Zhou, Lemma 2.1, second part): if `y` is a
small perturbation of the `ν`-separated configuration `x`, then the angle between the pairs
`x i - x j` and `y i - y j` has cosine at least `1 - 4δ` where `δ = dist y x / ν`. -/
lemma inner_pair_ge_of_dist_le {x y : EN E N} {ν δ : ℝ} (h : Separated x ν) (hν : 0 < ν)
    (hd : dist y x ≤ δ * ν) (hδ : δ < 1 / 4) (i j : Fin N) (hij : i ≠ j) :
    (1 - 4 * δ) * (dist (x i) (x j) * dist (y i) (y j))
      ≤ inner ℝ (x i - x j) (y i - y j) := by
  have hδ0 : 0 ≤ δ := by
    have hthis := h i j hij
    have : 0 ≤ dist y x := dist_nonneg
    nlinarith
  set p : E := x i - x j with hp
  set e : E := (y i - x i) - (y j - x j) with he
  have hq : y i - y j = p + e := by rw [hp, he]; abel
  have hνp : ν ≤ ‖p‖ := by
    have hthis := h i j hij
    rw [dist_eq_norm] at hthis
    rw [← hp] at hthis
    exact hthis
  have hnorm_e : ‖e‖ ≤ 2 * (δ * ν) := by
    rw [he]
    calc ‖(y i - x i) - (y j - x j)‖ ≤ ‖y i - x i‖ + ‖y j - x j‖ := by
          rw [sub_eq_add_neg]
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [norm_neg]
      _ = dist (y i) (x i) + dist (y j) (x j) := by rw [dist_eq_norm, dist_eq_norm]
      _ ≤ dist y x + dist y x := by
          linarith [dist_apply_le_dist (x := y) (y := x) i, dist_apply_le_dist (x := y) (y := x) j]
      _ ≤ 2 * (δ * ν) := by linarith
  have hinner : inner ℝ p (p + e) = ‖p‖ ^ 2 + inner ℝ p e := by
    rw [inner_add_right, real_inner_self_eq_norm_sq]
  have hb1 : -(‖p‖ * ‖e‖) ≤ inner ℝ p e := by
    have h2 := abs_real_inner_le_norm p e
    linarith [(abs_le.mp h2).1]
  have hkey : (1 - 4 * δ) * (‖p‖ + ‖e‖) ≤ ‖p‖ - ‖e‖ := by
    have haux : 2 * δ * ν ≤ 2 * δ * ‖p‖ := by
      apply mul_le_mul_of_nonneg_left hνp
      linarith
    have h1 : 2 * ‖e‖ ≤ 4 * (δ * ν) := by linarith [hnorm_e]
    have h2 : 4 * (δ * ν) ≤ 4 * (δ * ‖p‖) := by linarith [haux]
    have h3 : (0:ℝ) ≤ 4 * δ * ‖e‖ := by positivity
    linarith
  have hle : ‖p + e‖ ≤ ‖p‖ + ‖e‖ := norm_add_le _ _
  have hfirst : (1 - 4 * δ) * (‖p‖ * ‖p + e‖) ≤ (1 - 4 * δ) * (‖p‖ * (‖p‖ + ‖e‖)) := by
    apply mul_le_mul_of_nonneg_left
    · exact mul_le_mul_of_nonneg_left hle (norm_nonneg p)
    · linarith [hδ]
  have hsecond : (1 - 4 * δ) * (‖p‖ * (‖p‖ + ‖e‖)) ≤ ‖p‖ * (‖p‖ - ‖e‖) := by
    rw [show (1 - 4 * δ) * (‖p‖ * (‖p‖ + ‖e‖)) = ‖p‖ * ((1 - 4 * δ) * (‖p‖ + ‖e‖)) by ring]
    exact mul_le_mul_of_nonneg_left hkey (norm_nonneg p)
  have hthird : ‖p‖ * (‖p‖ - ‖e‖) = ‖p‖ ^ 2 - ‖p‖ * ‖e‖ := by ring
  have hpx : dist (x i) (x j) = ‖p‖ := by rw [dist_eq_norm, ← hp]
  have hqx : dist (y i) (y j) = ‖p + e‖ := by rw [dist_eq_norm, hq]
  calc (1 - 4 * δ) * (dist (x i) (x j) * dist (y i) (y j))
      = (1 - 4 * δ) * (‖p‖ * ‖p + e‖) := by rw [hpx, hqx]
    _ ≤ ‖p‖ ^ 2 - ‖p‖ * ‖e‖ := hfirst.trans (hsecond.trans (le_of_eq hthird))
    _ ≤ ‖p‖ ^ 2 + inner ℝ p e := by linarith
    _ = inner ℝ p (p + e) := hinner.symm
    _ = inner ℝ (x i - x j) (y i - y j) := by rw [← hp, ← hq]

/-- **Monotonicity of the pair distances along a ray** (Liu--Yan--Zhou, Lemma 2.3): if all the
pairwise angles between `z` and `b` are non-negative, then translating `z` in the direction `b`
never decreases the mutual distances. -/
lemma dist_add_smul_ge {z b : EN E N} (h : ∀ i j, i ≠ j → 0 ≤ inner ℝ (z i - z j) (b i - b j))
    {t : ℝ} (ht : 0 ≤ t) (i j : Fin N) (hij : i ≠ j) :
    dist (z i) (z j) ≤ dist ((z + t • b) i) ((z + t • b) j) := by
  set p : E := z i - z j with hp
  set q : E := b i - b j with hq
  have hqeq : (z + t • b) i - (z + t • b) j = p + t • q := by
    rw [hp, hq]
    simp only [PiLp.add_apply, PiLp.smul_apply]
    module
  rw [dist_eq_norm, dist_eq_norm, hqeq, hp]
  have hkey : ‖p‖ ^ 2 ≤ ‖p + t • q‖ ^ 2 := by
    rw [norm_add_sq_real]
    have h1 : 0 ≤ 2 * inner ℝ p (t • q) := by
      rw [real_inner_smul_right]
      exact mul_nonneg (by norm_num) (mul_nonneg ht (h i j hij))
    have h2 : 0 ≤ ‖t • q‖ ^ 2 := sq_nonneg _
    linarith
  calc ‖p‖ = Real.sqrt (‖p‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖p + t • q‖ ^ 2) := Real.sqrt_le_sqrt hkey
    _ = ‖p + t • q‖ := Real.sqrt_sq (norm_nonneg _)

/-- A configuration without collisions has a positive separation (when `2 ≤ N`). -/
lemma exists_separated_of_withoutCollisions {a : EN E N} (h : WithoutCollisions a) (hN : 2 ≤ N) :
    ∃ ν > 0, Separated a ν := by
  haveI : Nonempty (Fin N × Fin N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  refine ⟨(Finset.univ : Finset (Fin N × Fin N)).inf' Finset.univ_nonempty
    (fun p => if p.1 = p.2 then 1 else dist (a p.1) (a p.2)), ?_, ?_⟩
  · refine (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun p _ => ?_)
    by_cases hpp : p.1 = p.2
    · simp [hpp]
    · simp only [hpp, if_false]
      exact dist_pos.mpr fun heq => h p.1 p.2 hpp (by rw [r, heq, dist_self])
  · intro i j hij
    have h := Finset.inf'_le (f := fun p : Fin N × Fin N => if p.1 = p.2 then 1 else dist (a p.1) (a p.2))
      (Finset.mem_univ (i, j))
    simp [hij] at h
    exact h

/-- Componentwise displacement is bounded in terms of a lower bound `c` for the masses. -/
lemma norm_apply_le_inv_sqrt_mul {m : Fin N → ℝ} {c : ℝ} (hc : 0 < c) (hmc : ∀ i, c ≤ m i)
    (y : EN E N) (i : Fin N) : ‖y i‖ ≤ (Real.sqrt c)⁻¹ * ‖y‖_[m] := by
  have hsum : c * ‖y i‖ ^ 2 ≤ ∑ k, m k * ‖y k‖ ^ 2 := by
    have h1 : m i * ‖y i‖ ^ 2 ≤ ∑ k, m k * ‖y k‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => m k * ‖y k‖ ^ 2)
        (fun k _ => mul_nonneg (by linarith [hmc k]) (sq_nonneg _)) (Finset.mem_univ i)
    have h2 : c * ‖y i‖ ^ 2 ≤ m i * ‖y i‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hmc i) (sq_nonneg _)
    linarith
  have hsq : ‖y‖_[m] ^ 2 = ∑ k, m k * ‖y k‖ ^ 2 := by
    rw [weightedNorm, Real.sq_sqrt]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (by linarith [hmc k]) (sq_nonneg _)
  have hkey : (Real.sqrt c * ‖y i‖) ^ 2 ≤ ‖y‖_[m] ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc.le, hsq]; exact hsum
  have h1 : Real.sqrt c * ‖y i‖ ≤ ‖y‖_[m] := by
    nlinarith [hkey, Real.sqrt_nonneg c, norm_nonneg (y i), weightedNorm_nonneg m y]
  rw [inv_mul_eq_div, le_div_iff₀ (Real.sqrt_pos.mpr hc)]
  linarith

/-- **Escape along `a`** (Liu--Yan--Zhou, Lemma 2.2, first part): if `‖a‖_[m] = 1` and `s` is
large compared with `‖x‖_[m]`, then the direction of `x + s • a` is within `ν/20` of `a`, where `ν`
is the separation of `a`. -/
lemma findxast {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {x a : EN E N} {ν s : ℝ} (hν : 0 < ν)
    (ha : ‖a‖_[m] = 1) (hs0 : 0 < s)
    (hs : ‖x‖_[m] + 40 * ‖x‖_[m] / ν ≤ s) :
    ‖(‖x + s • a‖_[m])⁻¹ • (x + s • a) - a‖_[m] ≤ ν / 20 := by
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hx0 : 0 ≤ ‖x‖_[m] := weightedNorm_nonneg m x
  have hlow : s - ‖x‖_[m] ≤ ‖x + s • a‖_[m] := by
    have h := weightedNorm_add_le hm0 (-x) (x + s • a)
    have h2 : (-x) + (x + s • a) = s • a := by
      rw [neg_add_cancel_left]
    rw [h2, weightedNorm_smul hm0 s a, ha, mul_one, abs_of_pos hs0] at h
    have h3 : ‖-x‖_[m] = ‖x‖_[m] := by
      have h4 : (-x : EN E N) = (-1 : ℝ) • x := by simp
      rw [h4]
      simpa using weightedNorm_smul hm0 (-1) x
    rw [h3] at h
    linarith
  have hupper : ‖x + s • a‖_[m] ≤ s + ‖x‖_[m] := by
    calc ‖x + s • a‖_[m] ≤ ‖x‖_[m] + ‖s • a‖_[m] := weightedNorm_add_le hm0 _ _
      _ = ‖x‖_[m] + s := by rw [weightedNorm_smul hm0 s a, ha, mul_one, abs_of_pos hs0]
      _ = s + ‖x‖_[m] := by ring
  have hdiff : ‖x + s • a - ‖x + s • a‖_[m] • a‖_[m] ≤ 2 * ‖x‖_[m] := by
    have h1 : x + s • a - ‖x + s • a‖_[m] • a = x + (s - ‖x + s • a‖_[m]) • a := by module
    rw [h1]
    have h2 : ‖x + (s - ‖x + s • a‖_[m]) • a‖_[m] ≤ ‖x‖_[m] + ‖(s - ‖x + s • a‖_[m]) • a‖_[m] :=
      weightedNorm_add_le hm0 _ _
    rw [weightedNorm_smul hm0 _ a, ha, mul_one] at h2
    have habs : |s - ‖x + s • a‖_[m]| ≤ ‖x‖_[m] := by
      rw [abs_sub_le_iff]
      exact ⟨by linarith, by linarith⟩
    linarith
  rcases eq_or_lt_of_le hx0 with hx | hx
  · have hxzero : x = 0 := (weightedNorm_eq_zero_iff hm x).mp hx.symm
    subst hxzero
    rw [zero_add]
    have hz : (‖s • a‖_[m])⁻¹ • (s • a) - a = 0 := by
      rw [weightedNorm_smul hm0 s a, ha, mul_one, abs_of_pos hs0, smul_smul,
        inv_mul_cancel₀ (ne_of_gt hs0), one_smul, sub_self]
    rw [hz, weightedNorm, Finset.sum_eq_zero (fun i _ => by simp [PiLp.zero_apply]),
      Real.sqrt_zero]
    positivity
  · have hden : 0 < ‖x + s • a‖_[m] := by
      have h1 : 40 * ‖x‖_[m] / ν ≤ s - ‖x‖_[m] := by linarith
      have h3 : 0 < 40 * ‖x‖_[m] / ν := by positivity
      linarith
    have hsplit : (‖x + s • a‖_[m])⁻¹ • (x + s • a) - a
        = (‖x + s • a‖_[m])⁻¹ • (x + s • a - ‖x + s • a‖_[m] • a) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hden), one_smul]
    rw [hsplit, weightedNorm_smul hm0 _ (x + s • a - ‖x + s • a‖_[m] • a),
      abs_of_pos (inv_pos.mpr hden)]
    have hden2 : 40 * ‖x‖_[m] / ν ≤ ‖x + s • a‖_[m] := by linarith
    have hpos : 0 < 40 * ‖x‖_[m] / ν := by positivity
    calc (‖x + s • a‖_[m])⁻¹ * ‖x + s • a - ‖x + s • a‖_[m] • a‖_[m]
        ≤ (‖x + s • a‖_[m])⁻¹ * (2 * ‖x‖_[m]) := by
          exact mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr hden.le)
      _ ≤ (40 * ‖x‖_[m] / ν)⁻¹ * (2 * ‖x‖_[m]) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact inv_anti₀ (by positivity) hden2
      _ = ν / 20 := by
          rw [inv_div]
          field_simp
          ring

/-- The Euclidean configuration norm is bounded by the mass norm (`= (√c)⁻¹ · ‖y‖_[m]` for
`c ≤ mᵢ`). -/
lemma norm_le_inv_sqrt_mul {m : Fin N → ℝ} {c : ℝ} (hc : 0 < c) (hmc : ∀ i, c ≤ m i)
    (y : EN E N) : ‖y‖ ≤ (Real.sqrt c)⁻¹ * ‖y‖_[m] := by
  have hnsq : ‖y‖ ^ 2 = ∑ k, ‖y k‖ ^ 2 := by rw [PiLp.norm_sq_eq_of_L2]
  have hmsq : ‖y‖_[m] ^ 2 = ∑ k, m k * ‖y k‖ ^ 2 := by
    rw [weightedNorm, Real.sq_sqrt]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (by linarith [hmc k]) (sq_nonneg _)
  have hle : c * ‖y‖ ^ 2 ≤ ‖y‖_[m] ^ 2 := by
    rw [hnsq, hmsq, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hmc k) (sq_nonneg _)
  have hkey : (Real.sqrt c * ‖y‖) ^ 2 ≤ ‖y‖_[m] ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc.le]; exact hle
  have h2 : Real.sqrt c * ‖y‖ ≤ ‖y‖_[m] := by
    nlinarith [hkey, Real.sqrt_nonneg c, norm_nonneg y, weightedNorm_nonneg m y]
  rw [inv_mul_eq_div, le_div_iff₀ (Real.sqrt_pos.mpr hc)]
  linarith

/-- **Separation is preserved along rays with non-negative angles**: if all the pairwise angles
between `z` and `b` are non-negative, then `z + t • b` is as separated as `z` for every `t ≥ 0`. -/
lemma Separated.add_smul_of_inner_nonneg {z b : EN E N} {ν t : ℝ} (hsep : Separated z ν)
    (hinn : ∀ i j, i ≠ j → 0 ≤ inner ℝ (z i - z j) (b i - b j)) (ht : 0 ≤ t) :
    Separated (z + t • b) ν := fun i j hij => le_trans (hsep i j hij) (dist_add_smul_ge hinn ht i j hij)

/-- **Escape along `a`** (Liu--Yan--Zhou, Lemma 2.2, second part): `x + s • a` stays separated
with separation `(24/25) s ν` as long as `s` is large compared with `‖x‖_[m]` (the constant `K`
controls the componentwise norm in terms of the mass norm, `K = (√c)⁻¹` for `c ≤ mᵢ`). -/
lemma findxast_separated {m : Fin N → ℝ} {x a : EN E N} {ν s K : ℝ} (hK : 0 < K)
    (hKn : ∀ y : EN E N, ‖y‖ ≤ K * ‖y‖_[m]) (hν : 0 < ν)
    (hsep : Separated a ν) (hs : 50 * K * ‖x‖_[m] / ν ≤ s) :
    Separated (x + s • a) ((24 / 25) * s * ν) := by
  have hs0 : 0 ≤ s := by
    have hx : 0 ≤ ‖x‖_[m] := weightedNorm_nonneg m x
    have : 0 ≤ 50 * K * ‖x‖_[m] / ν := by positivity
    linarith
  intro i j hij
  have hcomp : ∀ (y : EN E N) (i : Fin N), ‖y i‖ ≤ K * ‖y‖_[m] :=
    fun y i => (norm_apply_le_norm y i).trans (hKn y)
  have h1 : dist (x i) (x j) ≤ 2 * K * ‖x‖_[m] := by
    calc dist (x i) (x j) ≤ ‖x i‖ + ‖x j‖ := dist_le_norm_add_norm _ _
      _ ≤ K * ‖x‖_[m] + K * ‖x‖_[m] := add_le_add (hcomp x i) (hcomp x j)
      _ = 2 * K * ‖x‖_[m] := by ring
  have h2 : s * ν - dist (x i) (x j) ≤ dist ((x + s • a) i) ((x + s • a) j) := by
    rw [dist_eq_norm, dist_eq_norm]
    have heq : (x + s • a) i - (x + s • a) j = (x i - x j) + s • (a i - a j) := by
      simp only [PiLp.add_apply, PiLp.smul_apply]; module
    rw [heq]
    have h3 : ‖s • (a i - a j)‖ = s * ‖a i - a j‖ := by
      rw [norm_smul, Real.norm_of_nonneg hs0]
    have h4 : ν ≤ ‖a i - a j‖ := by
      have := hsep i j hij
      rwa [dist_eq_norm] at this
    have h6 : ‖s • (a i - a j)‖ - ‖x i - x j‖ ≤ ‖(x i - x j) + s • (a i - a j)‖ := by
      have h5 : ‖s • (a i - a j)‖ ≤ ‖(x i - x j) + s • (a i - a j)‖ + ‖x i - x j‖ := by
        have h5' : ‖((x i - x j) + s • (a i - a j)) - (x i - x j)‖ ≤
            ‖(x i - x j) + s • (a i - a j)‖ + ‖x i - x j‖ := norm_sub_le _ _
        rwa [add_sub_cancel_left] at h5'
      linarith
    rw [h3] at h6
    have h7 : ‖x i - x j‖ = dist (x i) (x j) := by rw [dist_eq_norm]
    rw [h7] at h6
    linarith [mul_le_mul_of_nonneg_left h4 hs0]
  have h8 : 2 * K * ‖x‖_[m] ≤ (1 / 25) * (s * ν) := by
    have h9 : 50 * K * ‖x‖_[m] ≤ s * ν := by
      have := (div_le_iff₀ hν).mp hs
      linarith
    linarith
  have : (24 / 25) * s * ν = s * ν - (1 / 25) * (s * ν) := by ring
  rw [this]
  linarith

/-- **Liu--Yan--Zhou, Lemma 2.4.**  If `z` is `ν`-separated, its normalised direction `c = z/‖z‖`
is (still) `ν`-separated and `b` is a small perturbation of `c` with a cosine bounded below, then
translating `z` in the direction `b` preserves `ν`-separation.  (Geometrically: the angle between
`z_i - z_j` and `b_i - b_j` is acute, so the mutual distances cannot decrease — `dist_add_smul_ge`.) -/
lemma separated_add_smul_of_close_direction {m : Fin N → ℝ} {z b : EN E N} {ν δ t : ℝ}
    (hz : Separated z ν) (hzm : 0 < ‖z‖_[m])
    (hν : 0 < ν) (hδ : δ < 1 / 4)
    (hc : Separated ((‖z‖_[m])⁻¹ • z) ν) (hcb : dist b ((‖z‖_[m])⁻¹ • z) ≤ δ * ν) (ht : 0 ≤ t) :
    Separated (z + t • b) ν := by
  set c : EN E N := (‖z‖_[m])⁻¹ • z with hcdef
  have hd : dist b c ≤ δ * ν := hcb
  have hnn : ∀ i j, i ≠ j → 0 ≤ inner ℝ (z i - z j) (b i - b j) := by
    intro i j hij
    have h := inner_pair_ge_of_dist_le (x := c) (y := b) hc hν hd hδ i j hij
    have hz : z i - z j = ‖z‖_[m] • (c i - c j) := by
      rw [hcdef]
      simp only [PiLp.smul_apply, smul_sub, smul_smul]
      rw [mul_inv_cancel₀ (ne_of_gt hzm)]
      simp
    have hscale : inner ℝ (z i - z j) (b i - b j) = ‖z‖_[m] * inner ℝ (c i - c j) (b i - b j) := by
      rw [hz, real_inner_smul_left]
    rw [hscale]
    have h1 : 0 < 1 - 4 * δ := by linarith
    have h2 : 0 ≤ dist (c i) (c j) * dist (b i) (b j) := by positivity
    have h3 : 0 ≤ inner ℝ (c i - c j) (b i - b j) := by nlinarith [h, h1, h2]
    exact mul_nonneg (weightedNorm_nonneg m z) h3
  exact Separated.add_smul_of_inner_nonneg hz hnn ht

end Submission.NBody