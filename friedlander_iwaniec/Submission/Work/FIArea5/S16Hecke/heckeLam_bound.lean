import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count_le_tau_of_pos

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- `|z|²` computed in coordinates: `(gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2`. -/
lemma gnorm_cast_eq (z : GaussianInt) : ((gnorm z : ℕ) : ℤ) = z.re ^ 2 + z.im ^ 2 := by
  rw [gnorm, Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg (by norm_num : (-1 : ℤ) ≤ 0) z),
    Zsqrtd.norm_def]
  ring

/-- The coordinate pair `(z.re, z.im)` determines `z`. -/
lemma re_im_injective : Function.Injective (fun z : GaussianInt => (z.re, z.im)) := by
  intro x y h
  simp only [Prod.mk.injEq] at h
  exact Zsqrtd.ext h.1 h.2

/-- **Size of the Hecke eigenvalue.** For `‖χ‖ ≤ 1` the Hecke eigenvalue `λ(n)` is bounded by
the number of primary Gaussian integers of norm `n`, which is at most `r₂(n)/4 ≤ τ(n)`; the factor
`4` below is generous.  This is what makes `L(s,ψ) = Σ_n λ(n)n^{-s}` absolutely convergent for
`re s > 1` and makes the local factors `Σ_ν λ(p^ν)p^{-νs}` bounded by `Σ_ν (ν+1)p^{-νσ}`, i.e. of
size `1 + O(p^{-σ})` — the structural input of (16.31)/(16.33).

Hint on the counting: the filtered set `{z ∈ gBox n : IsPrimary z ∧ gnorm z = n}` injects into the
set of pairs `(a,b) ∈ ℤ²` with `a² + b² = n` (occurring in
`Commons.NumberTheory.GaussianInt.two_squares_repr_count_le_tau_of_pos`, which bounds the number of
such pairs — in the box `Icc (-n) n ×ˢ Icc (-n) n` — by `4 · (Nat.divisors n).card`; every `z` with
`gnorm z = n` has `|z.re|, |z.im| ≤ n`). -/
theorem heckeLam_bound (chi : GaussianInt → ℂ) (k : ℤ) (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖heckeLam chi k n‖ ≤ 4 * ((n.divisors.card : ℕ) : ℝ) := by
  classical
  set S : Finset GaussianInt :=
    (gBox (n : ℤ)).filter (fun z => IsPrimary z ∧ gnorm z = n) with hS
  have hsum : ‖heckeLam chi k n‖ ≤ ∑ z ∈ S, ‖psi chi k z‖ := by
    rw [hS]
    exact norm_sum_le _ _
  have hone : ∑ z ∈ S, ‖psi chi k z‖ ≤ (S.card : ℝ) := by
    calc ∑ z ∈ S, ‖psi chi k z‖ ≤ ∑ _z ∈ S, (1 : ℝ) :=
          Finset.sum_le_sum (fun z _ => norm_psi_le_one chi k hchi z)
      _ = (S.card : ℝ) := by simp
  have hcount : (S.card : ℝ) ≤ 4 * ((n.divisors.card : ℕ) : ℝ) := by
    let U : Finset (ℤ × ℤ) :=
      ((Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ (Finset.Icc (-(n : ℤ)) (n : ℤ))).filter
        (fun p => p.1 ^ 2 + p.2 ^ 2 = (n : ℤ))
    have hsub : S.image (fun z : GaussianInt => (z.re, z.im)) ⊆ U := by
      intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨z, hz, rfl⟩ := hp
      rw [hS, Finset.mem_filter] at hz
      obtain ⟨hzbox, -, hgn⟩ := hz
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_product]
        exact mem_gBox_iff.mp hzbox
      · have h : ((gnorm z : ℕ) : ℤ) = (n : ℤ) := by rw [hgn]
        rw [gnorm_cast_eq z] at h
        exact h
    have himg : (S.image (fun z : GaussianInt => (z.re, z.im))).card = S.card :=
      Finset.card_image_of_injective S re_im_injective
    have hle : (S.image (fun z : GaussianInt => (z.re, z.im))).card ≤ U.card :=
      Finset.card_le_card hsub
    have hU : (U.card : ℤ) ≤ 4 * ((Nat.divisors n).card : ℤ) :=
      Commons.NumberTheory.GaussianInt.two_squares_repr_count_le_tau_of_pos n hn
    have hleR : (S.card : ℝ) ≤ (U.card : ℝ) := by
      have h : ((S.image (fun z : GaussianInt => (z.re, z.im))).card : ℝ) ≤ (U.card : ℝ) := by
        exact_mod_cast hle
      rwa [himg] at h
    have hU' : (U.card : ℝ) ≤ 4 * ((Nat.divisors n).card : ℝ) := by
      have h2 : ((U.card : ℤ) : ℝ) ≤ ((4 * ((Nat.divisors n).card : ℤ) : ℤ) : ℝ) := by
        exact_mod_cast hU
      simpa using h2
    linarith
  linarith

end

end Work.FIArea5.S16Hecke
