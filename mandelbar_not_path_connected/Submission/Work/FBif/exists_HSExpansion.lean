import Mathlib
import Submission.Work.FBif.Defs
import Submission.Work.FBif.Expansion
import Submission.Work.FBif.Cycle
import Submission.Work.FBif.exists_goodPerturbation
import Submission.Work.FBif.Prep
import Submission.Work.FBif.fifthIterate_expansion
import Submission.Work.FBif.perturbDiffBound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function
open scoped Topology
open Polynomial

set_option maxHeartbeats 1000000

noncomputable section

namespace Work.FBif

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- `s² = lam` and `‖lam‖ = 1` force `‖s‖ = 1`. -/
private theorem norm_eq_one_of_sq {s lam : ℂ} (hs : s ^ 2 = lam) (hlam : ‖lam‖ = 1) :
    ‖s‖ = 1 := by
  have h : ‖s‖ ^ 2 = 1 := by rw [← norm_pow, hs, hlam]
  nlinarith [norm_nonneg s]

/-- `(X - C a)² ∣ P` forces `P a = 0`. -/
private theorem eval_eq_zero_of_sq_dvd {P : ℂ[X]} {a : ℂ} (h : (X - C a) ^ 2 ∣ P) :
    P.eval a = 0 := by
  obtain ⟨R, rfl⟩ := h
  simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub]

/-- **Hubbard–Schleicher's estimate at a simple parabolic parameter** (arXiv:1209.1753,
Lemma 3.4; = MNS Thm 2.1 second half).

Let `c` be root-parabolic with parabolic point `z₁`.  Then there are `A : ℂ` with `Re A > 0` and
an antipolynomial `q` such that `GoodPerturbation c z₁ q` holds and the normalised perturbed
fifth iterate `g_ε(u) = (f_ε^5 (z₁ + s u) - z₁)/s` (with `f_ε = Tantibar c + ε q`) has the
`HSExpansion` shape: its constant term `g_ε(0)` has real part `≥ c₁ ε` and imaginary part
`O(ε²)`, and on a fixed disc it agrees with `ū + A ū²` up to `C(ε + ‖u‖)‖u‖² + c₂ ε²‖u‖`.

Route.  Write `p := Tantibar c`, and let `lam` be the conjugate-linear multiplier of `p^[5]` at
`z₁` (a unit, by `d.mult`: `Tsq^5 = p^[10]` has derivative `1` at `z₁`, so `‖lam‖² = 1`).  Take a
square root `s` of `lam` and construct `q` with `q (cyclePt c z₁ 4) = s * σ` where `σ = ±1` is
chosen so that `σ * Re(A₂/(lam s)) > 0` (possible by `d.simple`, see `fifthIterate_expansion`);
`exists_goodPerturbation` supplies such a `q` (use `Work.EL.RootParabolic.cyclePt_ne_four` for the
required distinctness of the cycle points).  In the coordinate `z = z₁ + s u` the linear part of
`p^[5]` is `ū`, so `A := A₂/(lam s)` has positive real part.  Finally
`f_ε^[5] = p^[5] + ε * V + O(ε²)` with `V(z₁+w) = q (cyclePt c z₁ 4) + O(‖w‖²)` (the first-order
terms of `V` vanish because `q` vanishes to second order on the cycle), so `g_ε(0) = ε + O(ε²)`
and the error is `O(ε‖u‖²) + O(‖u‖³) + O(ε²‖u‖)`; this is the `HSExpansion` datum. -/
theorem exists_HSExpansion (c : ℂ) (d : Work.EL.RootParabolic c) :
    ∃ A : ℂ, 0 < A.re ∧ ∃ q : ℂ → ℂ,
      Work.FBif.GoodPerturbation c d.z₁ q ∧ Work.FBif.HSExpansion c d.z₁ q A := by
  -- the expansion of the unperturbed fifth iterate at `z₁`
  obtain ⟨lam, A₂, hlam, δ₁, hδ₁, C₁, hC₁, hexp, hno⟩ := fifthIterate_expansion c d
  -- a square root of the conjugate-linear multiplier; the two choices of the sign of `s` make
  -- `Re (A₂/(lam s))` change sign, so one of them is positive
  obtain ⟨s₀, hs₀⟩ := IsAlgClosed.exists_pow_nat_eq lam (n := 2) (by norm_num)
  have hne : (A₂ / (lam * s₀)).re ≠ 0 := hno s₀ hs₀
  obtain ⟨s, hs2, hspos, hs1⟩ : ∃ s : ℂ, s ^ 2 = lam ∧
      0 < (A₂ / (lam * s)).re ∧ ‖s‖ = 1 := by
    by_cases hpos : 0 < (A₂ / (lam * s₀)).re
    · exact ⟨s₀, hs₀, hpos, norm_eq_one_of_sq hs₀ hlam⟩
    · refine ⟨-s₀, by rw [neg_sq]; exact hs₀, ?_,
        by rw [norm_neg]; exact norm_eq_one_of_sq hs₀ hlam⟩
      have hres : A₂ / (lam * -s₀) = -(A₂ / (lam * s₀)) := by ring
      rw [hres, Complex.neg_re, neg_pos]
      exact lt_of_le_of_ne (le_of_not_gt hpos) hne
  set A : ℂ := A₂ / (lam * s) with hA
  have hApos : 0 < A.re := hspos
  refine ⟨A, hApos, ?_⟩
  have hs0 : s ≠ 0 := by
    intro h; rw [h, norm_zero] at hs1; norm_num at hs1
  -- the perturbing antipolynomial, normalised so that `q z₄ = s`
  obtain ⟨q, hgood, hqv⟩ := exists_goodPerturbation c d.z₁ (v := s) hs0
    (fun j hj => Work.EL.RootParabolic.cyclePt_ne_four d hj)
  refine ⟨q, hgood, ?_⟩
  obtain ⟨P, hqP, hvan, hvan4, hqz₄⟩ := hgood
  have hqeq : q = fun z => P.eval (star z) := funext hqP
  -- the perturbative estimate
  obtain ⟨K, hK, δ₂, hδ₂, ε₀₂, hε₀₂, hbound⟩ :=
    perturbDiffBound c d.z₁ P d.per_half hvan hvan4
  -- the perturbed fifth iterate at `z₁` is *exactly* `z₁ + ε q(z₄)`
  have hfive : ∀ ε : ℝ, (perturb c q ε)^[5] d.z₁
      = d.z₁ + (ε : ℂ) * q (cyclePt c d.z₁ 4) := by
    intro ε
    rw [hqeq]
    exact perturb_iterate_fifth_at c d.z₁ P ε d.per_half
      (fun j hj => eval_eq_zero_of_sq_dvd (hvan j hj))
  have hg0 : ∀ ε : ℝ, normIter c q d.z₁ s ε 0 = (ε : ℂ) := by
    intro ε
    rw [normIter_zero, hfive ε, hqv]
    field_simp
    ring
  -- in the coordinate `z = z₁ + s u` the unperturbed quadratic part is `s (ū + A ū²)`
  have hquad : ∀ u : ℂ, lam * star (s * u) + A₂ * (star (s * u)) ^ 2
      = s * (star u + A * (star u) ^ 2) := by
    intro u
    have h1 : lam * star s = s := lam_mul_star_eq lam s hs2 hs1
    have h2 : A₂ * (star s) ^ 2 = s * A := by
      have h := div_coeff A₂ lam s hs2 hs1
      rw [show A₂ * (star s) ^ 2 = s * (A₂ * (star s) ^ 2 / s) from by field_simp]
      rw [h]
    rw [star_mul, mul_pow]
    linear_combination (star u) * h1 + (star u) ^ 2 * h2
  refine ⟨s, hs1, min δ₁ δ₂, lt_min hδ₁ hδ₂, C₁ + K, by linarith, 0, le_rfl, 1, one_pos,
    min 1 ε₀₂, lt_min one_pos hε₀₂, ?_, ?_, ?_⟩
  · -- the real part of the normalised constant term is `ε`
    intro ε hε hεlt
    rw [hg0 ε, one_mul]
    simp
  · -- its imaginary part vanishes
    intro ε hε hεlt
    rw [hg0 ε]
    simp
  · -- the error estimate
    intro ε hε hεlt u hu
    have hε₂ : ε < ε₀₂ := lt_of_lt_of_le hεlt (min_le_right _ _)
    have hu₁ : ‖s * u‖ ≤ δ₁ := by
      rw [norm_mul, hs1, one_mul]; exact le_trans hu (min_le_left _ _)
    have hu₂ : ‖s * u‖ ≤ δ₂ := by
      rw [norm_mul, hs1, one_mul]; exact le_trans hu (min_le_right _ _)
    have hun : ‖s * u‖ = ‖u‖ := by rw [norm_mul, hs1, one_mul]
    have hA1 : ‖(Tantibar c)^[5] (d.z₁ + s * u) - d.z₁
        - (lam * star (s * u) + A₂ * (star (s * u)) ^ 2)‖ ≤ C₁ * ‖u‖ ^ 3 := by
      have h := hexp (s * u) hu₁
      have heq : (Tantibar c)^[5] (d.z₁ + s * u) - d.z₁
          - (lam * star (s * u) + A₂ * (star (s * u)) ^ 2)
          = (Tantibar c)^[5] (d.z₁ + s * u) - d.z₁ - lam * star (s * u)
            - A₂ * (star (s * u)) ^ 2 := by ring
      rw [heq, ← hun]
      exact h
    have hA2 : ‖((perturb c q ε)^[5] (d.z₁ + s * u) - (Tantibar c)^[5] (d.z₁ + s * u))
        - ((perturb c q ε)^[5] d.z₁ - (Tantibar c)^[5] d.z₁)‖ ≤ K * ε * ‖u‖ ^ 2 := by
      rw [hqeq]
      have h := hbound ε hε hε₂ (s * u) hu₂
      rw [hun] at h
      exact h
    have hquad' : (lam * star (s * u) + A₂ * (star (s * u)) ^ 2) / s
        = star u + A * (star u) ^ 2 := by
      rw [hquad u]
      field_simp
    have hsplit : normIter c q d.z₁ s ε u - normIter c q d.z₁ s ε 0
        - (star u + A * (star u) ^ 2)
        = (((Tantibar c)^[5] (d.z₁ + s * u) - d.z₁
              - (lam * star (s * u) + A₂ * (star (s * u)) ^ 2))
            + (((perturb c q ε)^[5] (d.z₁ + s * u) - (Tantibar c)^[5] (d.z₁ + s * u))
              - ((perturb c q ε)^[5] d.z₁ - (Tantibar c)^[5] d.z₁))) / s := by
      rw [normIter, normIter, d.per_half]
      rw [show star u + A * (star u) ^ 2
          = (lam * star (s * u) + A₂ * (star (s * u)) ^ 2) / s
          from hquad'.symm]
      field_simp
      ring
    rw [hsplit, norm_div, hs1, div_one]
    have hsum : ‖((Tantibar c)^[5] (d.z₁ + s * u) - d.z₁
          - (lam * star (s * u) + A₂ * (star (s * u)) ^ 2))
        + (((perturb c q ε)^[5] (d.z₁ + s * u) - (Tantibar c)^[5] (d.z₁ + s * u))
          - ((perturb c q ε)^[5] d.z₁ - (Tantibar c)^[5] d.z₁))‖
        ≤ C₁ * ‖u‖ ^ 3 + K * ε * ‖u‖ ^ 2 :=
      (norm_add_le _ _).trans (add_le_add hA1 hA2)
    refine hsum.trans ?_
    have hfinal : C₁ * ‖u‖ ^ 3 + K * ε * ‖u‖ ^ 2 ≤ (C₁ + K) * (ε + ‖u‖) * ‖u‖ ^ 2 := by
      have h1 : 0 ≤ C₁ * ε * ‖u‖ ^ 2 := by positivity
      have h2 : 0 ≤ K * ‖u‖ ^ 3 := by positivity
      nlinarith [h1, h2]
    simp only [zero_mul, add_zero]
    exact hfinal

end Work.FBif

end
