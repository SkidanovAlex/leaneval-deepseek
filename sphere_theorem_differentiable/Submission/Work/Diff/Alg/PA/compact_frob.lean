import Mathlib
import Submission.Work.Diff.Alg.PA.Defs
import Submission.Work.Diff.Alg.PA.R4_polarize
import Submission.Work.Diff.Alg.PA.R4_bianchi
import Submission.Work.Diff.Alg.Pinch.eq_zero_of_secK_eq_zero
import Submission.Work.Diff.Alg.q2p_secK_Iso
import Submission.Work.Diff.Alg.Pinch.Ccone_transversal_a_aux
import Submission.Work.Diff.GE.curv4_trace
import Submission.Work.Diff.L.pinchingSet_component_bound_v2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The trace-free part of a nearly-pinched curvature tensor is small

This is a piece of contract `PA` (`Submission.Diff.Grad`).  The task is the "compactness" statement
that, in the family of algebraic curvature tensors,

  `IsPinchedAlg δ R` with `δ → 1`  forces  `R° → 0`

(the trace-free part `R°` being measured by `frobSqTF`, the squared Frobenius distance to the
constant-curvature line).

## The quantitative statement

For `0 < δ < 1` and `R` an algebraic curvature tensor that is `δ`-pinched,

    `√|R°|² ≤ 8 n² ((1−δ)/δ) · √|R|²`.                        (★)

So `δ` close to `1` makes the ratio `√|R°|²/√|R|²` as small as we please — in particular
`compact_frob` below.  The conclusion is invariant under scaling `R ↦ λR` (`λ > 0`) and under
`O(n)`; (★) is a quantitative statement about the compact set of *normalised* pinched tensors.

## Proof of (★)

Fix a pair of distinct indices `i₀ ≠ j₀` (`n ≥ 2`) and put `s₀ = secK R (e_{i₀}) (e_{j₀})`.

*   `IsPinchedAlg δ R` applied to the pair `(e_{i₀}, e_{j₀})` against itself gives `s₀ ≥ 0`, and
    applied between `(e_{i₀}, e_{j₀})` and an arbitrary orthonormal pair `(u,v)` gives
    `δ s₀ ≤ secK R u v ≤ s₀/δ`.
*   Hence for the tensor `T = R − s₀ · Iso n` we have `|secK T u v| ≤ s₀ (1−δ)/δ =: S` on every
    orthonormal pair (`T` is an algebraic curvature tensor and `secK (Iso n) u v = 1`).
*   The polarization identity bounds *every* component of an algebraic curvature tensor by the
    values of its sectional curvature on orthonormal pairs
    (`Work.Diff.L.abs_secK_le_of_isONPair_abs_le`, `Work.Diff.L.abs_R4_stdB_le_of_secK_bound`):
    `|T i j k l| ≤ 8 S`.  Summing the squares, `|T|² ≤ n⁴ (8S)²`.
*   `|R°|² ≤ |T|²` for **every** `k` in `T = R − k · Iso n`: indeed
    `⟪R, Iso n⟫ = 2 scalAlg R` and `|Iso n|² = 2n(n−1)`, so
    `|R − k Iso|² − |R°|² = 2n(n−1) (k − scalAlg R/(n(n−1)))² ≥ 0`.
*   Finally `s₀² = (R i₀ j₀ i₀ j₀)² ≤ |R|²`, so `8 n² S ≤ 8 n² ((1−δ)/δ) √|R|²`.

## Assembly

Choosing `δ = max (1/2) (1 − ε/(32 n²))` makes `8 n² (1−δ)/δ ≤ ε`, and (★) gives `compact_frob`.
-/

set_option maxHeartbeats 800000

namespace Work.Diff.Alg.PA

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Linearity of `R4` in the tensor argument -/

theorem R4_sub_tensor (R S : Curv4 n) (a b c d : Fin n → ℝ) :
    R4 (R - S) a b c d = R4 R a b c d - R4 S a b c d := by
  simp only [R4, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem R4_smul_tensor (t : ℝ) (R : Curv4 n) (a b c d : Fin n → ℝ) :
    R4 (t • R) a b c d = t * R4 R a b c d := by
  simp only [R4, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- `secK` of `R - c • Iso n` (definitionally `R4` in the tensor argument). -/
theorem secK_sub_smul_Iso (R : Curv4 n) (c : ℝ) (u v : Fin n → ℝ) :
    secK (R - c • Iso n) u v = secK R u v - c * secK (Iso n) u v := by
  simp only [secK, R4_sub_tensor, R4_smul_tensor]

/-! ## Bilinearity of `tpair` and the expansion of `frobSq` -/

theorem tpair_sub_left (A A' B : Curv4 n) :
    tpair n (A - A') B = tpair n A B - tpair n A' B := by
  simp only [tpair, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem tpair_smul_left (c : ℝ) (A B : Curv4 n) :
    tpair n (c • A) B = c * tpair n A B := by
  simp only [tpair, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem tpair_sub_right (A B B' : Curv4 n) :
    tpair n A (B - B') = tpair n A B - tpair n A B' := by
  rw [tpair_comm n A (B - B'), tpair_sub_left, tpair_comm n B A, tpair_comm n B' A]

theorem tpair_smul_right (c : ℝ) (A B : Curv4 n) :
    tpair n A (c • B) = c * tpair n A B := by
  rw [tpair_comm n A (c • B), tpair_smul_left, tpair_comm n B A]

/-- Expansion of `frobSq` along a line `A - c • B`. -/
theorem frobSq_sub_smul (A B : Curv4 n) (c : ℝ) :
    frobSq (A - c • B) = frobSq A - 2 * c * tpair n A B + c ^ 2 * frobSq B := by
  rw [← tpair_self n (A - c • B)]
  rw [tpair_sub_right, tpair_sub_left, tpair_sub_left]
  rw [tpair_smul_left, tpair_smul_left, tpair_smul_right, tpair_smul_right, tpair_comm n B A]
  rw [tpair_self n A, tpair_self n B]
  ring

/-! ## The pairings with `Iso n` -/

/-- `⟪R, Iso n⟫ = 2 scalAlg R` for an algebraic curvature tensor.  Both sides are
`2 ∑ᵢⱼ Rᵢⱼᵢⱼ`: the two Kronecker deltas of `Iso` pick out `R i j i j` and `R i j j i`, and the
latter equals `-R i j i j` by antisymmetry of `R` in the last pair. -/
theorem tpair_Iso {R : Curv4 n} (hR : IsAlgCurv R) : tpair n R (Iso n) = 2 * scalAlg R := by
  have h1 : (∑ i, ∑ j, ∑ k, ∑ l,
      R i j k l * (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)) = scalAlg R := by
    simp only [scalAlg]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hl : ∀ k : Fin n,
        (∑ l, R i j k l * (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0))
          = (if i = k then R i j k j else 0) := by
      intro k
      have hll : (∑ l, R i j k l * (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0))
          = (if i = k then (1 : ℝ) else 0) * (∑ l, if j = l then R i j k l else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        by_cases hik : i = k <;> simp [hik]
      rw [hll, Finset.sum_ite_eq Finset.univ j (fun l => R i j k l)]
      simp only [Finset.mem_univ, if_true]
      by_cases hik : i = k <;> simp [hik]
    rw [Finset.sum_congr rfl (fun k _ => hl k),
      Finset.sum_ite_eq Finset.univ i (fun k => R i j k j)]
    simp
  have h2 : (∑ i, ∑ j, ∑ k, ∑ l,
      R i j k l * (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0))
        = -scalAlg R := by
    have hstep : (∑ i, ∑ j, ∑ k, ∑ l,
        R i j k l * (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0))
          = ∑ i, ∑ j, R i j j i := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hl : ∀ k : Fin n,
          (∑ l, R i j k l * (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0))
            = (if j = k then R i j k i else 0) := by
        intro k
        have hll : (∑ l, R i j k l * (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0))
            = (if j = k then (1 : ℝ) else 0) * (∑ l, if i = l then R i j k l else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          by_cases hjk : j = k <;> simp [hjk]
        rw [hll, Finset.sum_ite_eq Finset.univ i (fun l => R i j k l)]
        simp only [Finset.mem_univ, if_true]
        by_cases hjk : j = k <;> simp [hjk]
      rw [Finset.sum_congr rfl (fun k _ => hl k),
        Finset.sum_ite_eq Finset.univ j (fun k => R i j k i)]
      simp
    rw [hstep]
    have hneg : ∀ i j : Fin n, R i j j i = -R i j i j := fun i j => IsAlgCurv_antisym₃₄ hR i j i j
    simp only [hneg, scalAlg, Finset.sum_neg_distrib]
  calc tpair n R (Iso n)
      = (∑ i, ∑ j, ∑ k, ∑ l,
            R i j k l * (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0))
        - (∑ i, ∑ j, ∑ k, ∑ l,
            R i j k l * (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)) := by
        simp only [tpair, Iso, mul_sub, mul_assoc, Finset.sum_sub_distrib]
    _ = 2 * scalAlg R := by rw [h1, h2]; ring

/-- `|Iso n|² = 2 n (n-1)`. -/
theorem frobSq_Iso : frobSq (Iso n) = 2 * (n : ℝ) * ((n : ℝ) - 1) := by
  rw [← tpair_self n (Iso n), tpair_Iso (Work.Diff.Alg.Pinch.Iso_algCurv n),
    Work.Diff.Alg.Pinch.scalAlg_iso]
  ring

/-- The trace-free part of `R` is at most the Frobenius distance from `R` to **any** point of the
constant-curvature line: `|R°|² ≤ |R − k·Iso n|²` for every `k`, since the difference is
`2n(n−1) (k − scalAlg R/(n(n−1)))²`. -/
theorem frobSqTF_le_frobSq_sub_smul (hn : 2 ≤ n) {R : Curv4 n} (hR : IsAlgCurv R) (k : ℝ) :
    frobSqTF R ≤ frobSq (R - k • Iso n) := by
  have hm : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hD : n * (n - 1 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := rfl
  rw [frobSqTF, hD, frobSq_sub_smul, tpair_Iso hR, frobSq_Iso]
  have hne : (n : ℝ) ≠ 0 := ne_of_gt (by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith)
  have hne1 : (n : ℝ) - 1 ≠ 0 := ne_of_gt (by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith)
  have hkey : (frobSq R - 2 * k * (2 * scalAlg R) + k ^ 2 * (2 * (n : ℝ) * ((n : ℝ) - 1)))
      - (frobSq R - 2 * scalAlg R ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)))
      = 2 * ((n : ℝ) * ((n : ℝ) - 1) * k - scalAlg R) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    field_simp
    ring
  have hnn : (0 : ℝ) ≤ 2 * ((n : ℝ) * ((n : ℝ) - 1) * k - scalAlg R) ^ 2
      / ((n : ℝ) * ((n : ℝ) - 1)) := div_nonneg (by positivity) hm.le
  linarith [hkey, hnn]

/-! ## The quantitative pinching estimate -/

/-- Every component of a curvature array is bounded by its Frobenius norm. -/
theorem sq_component_le_frobSq (R : Curv4 n) (i j k l : Fin n) : R i j k l ^ 2 ≤ frobSq R := by
  have h1 : R i j k l ^ 2 ≤ ∑ l' : Fin n, R i j k l' ^ 2 :=
    Finset.single_le_sum (s := Finset.univ) (f := fun l' : Fin n => R i j k l' ^ 2)
      (a := l) (fun l' _ => sq_nonneg _) (Finset.mem_univ l)
  have h2 : (∑ l' : Fin n, R i j k l' ^ 2) ≤ ∑ k' : Fin n, ∑ l' : Fin n, R i j k' l' ^ 2 :=
    Finset.single_le_sum (s := Finset.univ)
      (f := fun k' : Fin n => ∑ l' : Fin n, R i j k' l' ^ 2) (a := k)
      (fun k' _ => Finset.sum_nonneg fun l' _ => sq_nonneg _) (Finset.mem_univ k)
  have h3 : (∑ k' : Fin n, ∑ l' : Fin n, R i j k' l' ^ 2)
      ≤ ∑ j' : Fin n, ∑ k' : Fin n, ∑ l' : Fin n, R i j' k' l' ^ 2 :=
    Finset.single_le_sum (s := Finset.univ)
      (f := fun j' : Fin n => ∑ k' : Fin n, ∑ l' : Fin n, R i j' k' l' ^ 2) (a := j)
      (fun j' _ => Finset.sum_nonneg fun k' _ => Finset.sum_nonneg fun l' _ => sq_nonneg _)
      (Finset.mem_univ j)
  have h4 : (∑ j' : Fin n, ∑ k' : Fin n, ∑ l' : Fin n, R i j' k' l' ^ 2) ≤ frobSq R := by
    have hfr : frobSq R
        = ∑ i' : Fin n, ∑ j' : Fin n, ∑ k' : Fin n, ∑ l' : Fin n, R i' j' k' l' ^ 2 := rfl
    rw [hfr]
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun i' : Fin n => ∑ j' : Fin n, ∑ k' : Fin n, ∑ l' : Fin n, R i' j' k' l' ^ 2)
      (a := i)
      (fun i' _ => Finset.sum_nonneg fun j' _ => Finset.sum_nonneg fun k' _ =>
        Finset.sum_nonneg fun l' _ => sq_nonneg _)
      (Finset.mem_univ i)
  exact le_trans h1 (le_trans h2 (le_trans h3 h4))

/-- **(★)**:  the trace-free part of a `δ`-pinched algebraic curvature tensor is at most
`8 n² (1−δ)/δ` times the tensor itself. -/
theorem frob_sqrt_le_pinched (n : ℕ) (hn : 2 ≤ n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (R : Curv4 n) (hR : IsAlgCurv R) (hpin : IsPinchedAlg δ R) :
    Real.sqrt (frobSqTF R) ≤ 8 * (n : ℝ) ^ 2 * ((1 - δ) / δ) * Real.sqrt (frobSq R) := by
  have hn0 : 0 < n := by omega
  have hn1 : 1 < n := by omega
  set i₀ : Fin n := ⟨0, hn0⟩ with hi₀
  set j₀ : Fin n := ⟨1, hn1⟩ with hj₀
  have hij : i₀ ≠ j₀ := by
    intro h
    have h2 : (i₀ : ℕ) = (j₀ : ℕ) := congrArg Fin.val h
    rw [hi₀, hj₀] at h2
    exact absurd h2 (by norm_num)
  have hon : IsONPair (stdB n i₀) (stdB n j₀) := isONPair_stdB hij
  set s₀ : ℝ := secK R (stdB n i₀) (stdB n j₀) with hs₀
  -- `0 ≤ s₀`
  have hs₀nn : 0 ≤ s₀ := by
    have h := hpin (stdB n i₀) (stdB n j₀) (stdB n i₀) (stdB n j₀) hon hon
    rw [← hs₀] at h
    nlinarith [h, hδ1]
  -- the two pinching inequalities
  have hlo : ∀ u v : Fin n → ℝ, IsONPair u v → δ * s₀ ≤ secK R u v := by
    intro u v huv
    have h := hpin u v (stdB n i₀) (stdB n j₀) huv hon
    rwa [← hs₀] at h
  have hhi : ∀ u v : Fin n → ℝ, IsONPair u v → secK R u v ≤ s₀ / δ := by
    intro u v huv
    have h := hpin (stdB n i₀) (stdB n j₀) u v hon huv
    rw [← hs₀] at h
    rw [le_div_iff₀ hδ0]
    linarith
  -- the tensor `T = R - s₀ • Iso n`
  have hSnn : 0 ≤ s₀ * ((1 - δ) / δ) := mul_nonneg hs₀nn (div_nonneg (by linarith) hδ0.le)
  have hT : IsAlgCurv (R - s₀ • Iso n) :=
    IsAlgCurv.sub hR (IsAlgCurv.smul (Work.Diff.Alg.Pinch.Iso_algCurv n) s₀)
  have hTsecK : ∀ u v : Fin n → ℝ, IsONPair u v →
      |secK (R - s₀ • Iso n) u v| ≤ s₀ * ((1 - δ) / δ) := by
    intro u v huv
    have hIso : secK (Iso n) u v = 1 := Work.Diff.Alg.q2p_secK_Iso huv
    rw [secK_sub_smul_Iso, hIso, mul_one]
    have h1 := hlo u v huv
    have h2 := hhi u v huv
    have h3 : s₀ / δ - s₀ = s₀ * ((1 - δ) / δ) := by field_simp
    have h4 : s₀ * (1 - δ) ≤ s₀ * ((1 - δ) / δ) := by
      apply mul_le_mul_of_nonneg_left _ hs₀nn
      rw [le_div_iff₀ hδ0]
      nlinarith [hδ0, hδ1]
    have hup : secK R u v - s₀ ≤ s₀ * ((1 - δ) / δ) := by linarith
    have hdn : -(s₀ * ((1 - δ) / δ)) ≤ secK R u v - s₀ := by linarith
    exact abs_le.mpr ⟨hdn, hup⟩
  -- polarization: every component of `T` is small
  have habs := Work.Diff.L.abs_secK_le_of_isONPair_abs_le hT hSnn hTsecK
  have hcomp := Work.Diff.L.abs_R4_stdB_le_of_secK_bound hT hSnn habs
  have hfT : frobSq (R - s₀ • Iso n) ≤ ((n : ℝ) ^ 2 * (8 * (s₀ * ((1 - δ) / δ)))) ^ 2 := by
    have hstep : ∀ i j k l : Fin n,
        ((R - s₀ • Iso n) i j k l) ^ 2 ≤ (8 * (s₀ * ((1 - δ) / δ))) ^ 2 := by
      intro i j k l
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hcomp i j k l) 2
    calc frobSq (R - s₀ • Iso n)
        = ∑ i, ∑ j, ∑ k, ∑ l, ((R - s₀ • Iso n) i j k l) ^ 2 := rfl
      _ ≤ ∑ i, ∑ j, ∑ k, ∑ l, (8 * (s₀ * ((1 - δ) / δ))) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hstep i j k l
      _ = ((n : ℝ) ^ 2 * (8 * (s₀ * ((1 - δ) / δ)))) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hsT : Real.sqrt (frobSq (R - s₀ • Iso n)) ≤ 8 * (n : ℝ) ^ 2 * (s₀ * ((1 - δ) / δ)) := by
    have h1 : Real.sqrt (frobSq (R - s₀ • Iso n))
        ≤ Real.sqrt (((n : ℝ) ^ 2 * (8 * (s₀ * ((1 - δ) / δ)))) ^ 2) := Real.sqrt_le_sqrt hfT
    rw [Real.sqrt_sq (mul_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)
      (mul_nonneg (by norm_num) hSnn))] at h1
    linarith [h1]
  -- `s₀ ≤ √|R|²`
  have hs0_le : s₀ ≤ Real.sqrt (frobSq R) := by
    have hchain : s₀ ^ 2 ≤ frobSq R := by
      have hsec : (secK R (stdB n i₀) (stdB n j₀)) ^ 2 ≤ frobSq R := by
        rw [secK_stdB]
        exact sq_component_le_frobSq R i₀ j₀ i₀ j₀
      rw [hs₀]
      exact hsec
    calc s₀ = Real.sqrt (s₀ ^ 2) := (Real.sqrt_sq hs₀nn).symm
      _ ≤ Real.sqrt (frobSq R) := Real.sqrt_le_sqrt hchain
  calc Real.sqrt (frobSqTF R)
      ≤ Real.sqrt (frobSq (R - s₀ • Iso n)) :=
        Real.sqrt_le_sqrt (frobSqTF_le_frobSq_sub_smul hn hR s₀)
    _ ≤ 8 * (n : ℝ) ^ 2 * (s₀ * ((1 - δ) / δ)) := hsT
    _ = 8 * (n : ℝ) ^ 2 * ((1 - δ) / δ) * s₀ := by ring
    _ ≤ 8 * (n : ℝ) ^ 2 * ((1 - δ) / δ) * Real.sqrt (frobSq R) :=
        mul_le_mul_of_nonneg_left hs0_le (by positivity)

end Work.Diff.Alg.PA

namespace Work.Diff.Alg.PA

open Finset Submission.Diff.Alg

theorem compact_frob (n : ℕ) (hn : 2 ≤ n) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, δ < 1 ∧ ∀ R : Curv4 n, IsAlgCurv R → IsPinchedAlg δ R →
      Real.sqrt (frobSqTF R) ≤ ε * Real.sqrt (frobSq R) := by
  intro ε hε
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hnRne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  set δ : ℝ := max (1 / 2) (1 - ε / (32 * (n : ℝ) ^ 2)) with hδdef
  have hδhalf : (1 / 2 : ℝ) ≤ δ := by rw [hδdef]; exact le_max_left _ _
  have hδε : 1 - ε / (32 * (n : ℝ) ^ 2) ≤ δ := by rw [hδdef]; exact le_max_right _ _
  have hδ0 : 0 < δ := lt_of_lt_of_le (by norm_num) hδhalf
  have hδ1 : δ < 1 := by
    rw [hδdef]
    refine max_lt (by norm_num) ?_
    have : 0 < ε / (32 * (n : ℝ) ^ 2) := by positivity
    linarith
  refine ⟨δ, hδ1, ?_⟩
  intro R hR hpin
  have hmain := frob_sqrt_le_pinched n hn hδ0 hδ1 R hR hpin
  have hconst : 8 * (n : ℝ) ^ 2 * ((1 - δ) / δ) ≤ ε := by
    have h1 : 1 - δ ≤ ε / (32 * (n : ℝ) ^ 2) := by linarith
    have hδnn : 0 ≤ 1 - δ := by linarith
    have hinv : 1 / δ ≤ 2 := by
      rw [div_le_iff₀ hδ0]
      linarith
    have h2 : (1 - δ) / δ ≤ 2 * (ε / (32 * (n : ℝ) ^ 2)) := by
      rw [show (1 - δ) / δ = (1 - δ) * (1 / δ) from by field_simp]
      calc (1 - δ) * (1 / δ) ≤ (1 - δ) * 2 := mul_le_mul_of_nonneg_left hinv hδnn
        _ ≤ 2 * (ε / (32 * (n : ℝ) ^ 2)) := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 8 * (n : ℝ) ^ 2)
    have h4 : 8 * (n : ℝ) ^ 2 * (2 * (ε / (32 * (n : ℝ) ^ 2))) = ε / 2 := by
      field_simp
      ring
    linarith
  calc Real.sqrt (frobSqTF R) ≤ 8 * (n : ℝ) ^ 2 * ((1 - δ) / δ) * Real.sqrt (frobSq R) := hmain
    _ ≤ ε * Real.sqrt (frobSq R) := mul_le_mul_of_nonneg_right hconst (Real.sqrt_nonneg _)

end Work.Diff.Alg.PA
