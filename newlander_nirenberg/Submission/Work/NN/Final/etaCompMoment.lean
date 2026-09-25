/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The moment identity for the normal-variable rescaling `eta`

`eta c` is the continuous linear map `(x, t) ↦ (x, c * t)` on `X × ℝ` (see
`Submission.Work.NN.Final.eta`).  The lemma `etaCompMoment` shows that if the weights
`lam j` reproduce the moments of the numbers `c j = -(ε j)` up to order `k`, then they
also reproduce the identity when applied to the multilinear map `Φ` with every
argument rescaled by `eta (c j)`, provided the arity `i` of `Φ` is at most `k`.

The proof is a two-fold use of `dilation_expansion` (the multilinear expansion of `Φ`
along a perturbation `a + c • e`): once for `Φ v` itself, and once for
`Φ (fun l => eta c (v l))`, after which only the scalar moment identity
`∑ j, lam j * (-(ε j)) ^ d = 1` (for `d ≤ k`) is needed.
-/
import Mathlib
import Submission.Work.NN.Final.eta
import Submission.Work.NN.Final.dilation_expansion

noncomputable section

namespace Work.NN.Final

open Finset

/-- Expansion of a continuous multilinear map along the perturbation
`a l ↦ a l + (r * c l) • e l`: the sum over subsets `s` of the coefficient
`r ^ #s * ∏ l ∈ s, c l` times `M` evaluated on the function that is `e` on `s`
and `a` off `s`.  This is `dilation_expansion` with the scalar `r` factored out of
the coefficients. -/
theorem dilation_expansion_scalar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ContinuousMultilinearMap ℝ (fun _ : ι => E) F) (a e : ι → E) (c : ι → ℝ) (r : ℝ) :
    M (fun l => a l + (r * c l) • e l) =
      ∑ s : Finset ι, (r ^ s.card) • ((∏ l ∈ s, c l) • M (s.piecewise e a)) := by
  rw [dilation_expansion M a e (fun l => r * c l)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, smul_smul]

theorem etaCompMoment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {ε lam : Fin (k + 1) → ℝ}
    (hlam : ∀ j : ℕ, j ≤ k → ∑ i : Fin (k + 1), lam i * (-(ε i)) ^ j = 1)
    (i : ℕ) (hi : i ≤ k)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin i => E × ℝ) ℂ) :
    ∑ j : Fin (k + 1), lam j • Φ.compContinuousLinearMap
        (fun _ => Work.NN.Final.eta (X := E) (-(ε j))) = Φ := by
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [_root_.sum_apply, _root_.smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  -- Decompose every argument `v l = (x l, t l)` as `a l + t l • e` with `e = (0, 1)`.
  set av : Fin i → E × ℝ := fun l => ((v l).1, 0) with hav
  set ev : Fin i → E × ℝ := fun _ => (0, 1) with hev
  set cc : Fin i → ℝ := fun l => (v l).2 with hcc
  have hv : v = fun l => av l + cc l • ev l := by
    funext l; simp [hav, hev, hcc]
  have hfam : ∀ c : ℝ, (fun l => eta (X := E) c (v l)) = fun l => av l + (c * cc l) • ev l := by
    intro c; funext l; simp [hav, hev, hcc, eta_apply]
  -- Rescaling each argument by `eta c` rescales the second coefficient by `c`.
  have hstep : ∀ j : Fin (k + 1),
      Φ (fun l => eta (X := E) (-(ε j)) (v l)) =
        ∑ s : Finset (Fin i), ((-(ε j)) ^ s.card) •
          ((∏ l ∈ s, cc l) • Φ (s.piecewise ev av)) := by
    intro j
    rw [hfam (-(ε j))]
    exact dilation_expansion_scalar Φ av ev cc (-(ε j))
  have hcard : ∀ s : Finset (Fin i), s.card ≤ k := by
    intro s
    calc s.card ≤ Fintype.card (Fin i) := Finset.card_le_univ s
      _ = i := Fintype.card_fin i
      _ ≤ k := hi
  calc ∑ j : Fin (k + 1), lam j • Φ (fun l => eta (X := E) (-(ε j)) (v l))
      = ∑ j : Fin (k + 1), lam j •
          ∑ s : Finset (Fin i), ((-(ε j)) ^ s.card) •
            ((∏ l ∈ s, cc l) • Φ (s.piecewise ev av)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hstep j]
    _ = ∑ j : Fin (k + 1), ∑ s : Finset (Fin i),
          (lam j * (-(ε j)) ^ s.card * (∏ l ∈ s, cc l)) • Φ (s.piecewise ev av) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [smul_smul, smul_smul]
    _ = ∑ s : Finset (Fin i), ∑ j : Fin (k + 1),
          (lam j * (-(ε j)) ^ s.card * (∏ l ∈ s, cc l)) • Φ (s.piecewise ev av) :=
        Finset.sum_comm
    _ = ∑ s : Finset (Fin i), (∏ l ∈ s, cc l) • Φ (s.piecewise ev av) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        rw [← Finset.sum_mul, hlam s.card (hcard s), one_mul]
    _ = Φ v := by
        rw [hv]
        exact (dilation_expansion Φ av ev cc).symm

end Work.NN.Final
