import Mathlib
import Submission.Work.BW.Est17Ext
import Submission.Work.BW.DefsAC
import Submission.Work.BW.finplace_log_abs_support
import Submission.Work.BW.finplace_posLog_sgn_support
import Submission.Work.BW.finplace_ciSup_log_support

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open NumberField

/-- **Finite support of the finite-place integrand of `est17`.** `L = EL φ ρ` with
`ρ = rhoC φ α v L`, `inclE φ ρ : K →+* L`.  Needed so that `∑ᶠ` over the finite places of `L` can
be split (`finsum_add_distrib`) and compared (`finsum_le_finsum`).  All four functions have finite
support:
* `w ↦ log (⨆_λ w (inclE (p λ)))`: for all but finitely many `w`, `w (inclE (p λ)) = 1` for every
  `λ` (finitely many `λ`, `NumberField.FinitePlace.hasFiniteMulSupport`), hence the sup is `1`;
* `w ↦ ∑_j D_j · log⁺ w(α'_j)^{±1}`: for all but finitely many `w`, `w (inclE (α'_j)) = 1` for
  every `j`, hence each `log⁺ = 0`; if `inclE (α'_j) = 0` the summand is `log⁺ 0 = 0`;
* `w ↦ |log (w (inclE (2 : K)))|`: `inclE (2 : K) = (2 : L) ≠ 0`, and `w (2) = 1` for all but the
  finitely many `w` above `2`;
* any real linear combination of the three (with constants `z = |s|/2/2^J` and
  `2(J+1)·h·(D₀+1)`), which is what `est17_arch`/`est17_fin` produce. -/
theorem est17_fin_supports {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σl : Fin r → ℝ}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl) → K}
    [inst : NumberField (EL φ (rhoC φ α v L))]
    (hp : p ≠ 0) (s : ℤ) (J : ℕ) :
    Function.HasFiniteSupport (fun w : NumberField.FinitePlace (EL φ (rhoC φ α v L)) =>
        Real.log (⨆ lm, w (inclE φ (rhoC φ α v L) (p lm))))
      ∧ Function.HasFiniteSupport (fun w : NumberField.FinitePlace (EL φ (rhoC φ α v L)) =>
          ∑ j, ((pDj r (dK K) σl j : ℕ) : ℝ) *
            (if 0 ≤ s then w (inclE φ (rhoC φ α v L) (α' j))
               else (w (inclE φ (rhoC φ α v L) (α' j)))⁻¹).posLog)
      ∧ Function.HasFiniteSupport (fun w : NumberField.FinitePlace (EL φ (rhoC φ α v L)) =>
          |Real.log (w (inclE φ (rhoC φ α v L) (2 : K)))|)
      ∧ Function.HasFiniteSupport (fun w : NumberField.FinitePlace (EL φ (rhoC φ α v L)) =>
          Real.log (⨆ lm, w (inclE φ (rhoC φ α v L) (p lm)))
            + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) *
                (∑ j, ((pDj r (dK K) σl j : ℕ) : ℝ) *
                  (if 0 ≤ s then w (inclE φ (rhoC φ α v L) (α' j))
                     else (w (inclE φ (rhoC φ α v L) (α' j)))⁻¹).posLog)
            + 2 * ((J : ℝ) + 1) * (acH K b v : ℝ) * ((pD0 r (dK K) σl : ℝ) + 1)
                * |Real.log (w (inclE φ (rhoC φ α v L) (2 : K)))|) := by
  classical
  -- `p ≠ 0` gives an index `lm` with `inclE (p lm) ≠ 0`; the injectivity of `inclE` is used
  -- throughout to move between `K` and `L`.
  have hinj : Function.Injective (inclE φ (rhoC φ α v L)) := RingHom.injective _
  have hne : ∃ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl),
      inclE φ (rhoC φ α v L) (p lm) ≠ 0 := by
    obtain ⟨lm, hlm⟩ := Function.ne_iff.mp hp
    exact ⟨lm, fun h => hlm (hinj (by simpa using h))⟩
  -- (1) The `⨆`-term: off the finite union `⋃_{p lm ≠ 0} {w | w (p lm) ≠ 1}` the sup is `1`.
  have h1 : Function.HasFiniteSupport (fun w : NumberField.FinitePlace (EL φ (rhoC φ α v L)) =>
      Real.log (⨆ lm, w (inclE φ (rhoC φ α v L) (p lm)))) :=
    finplace_ciSup_log_support (x := fun lm => inclE φ (rhoC φ α v L) (p lm)) hne
  -- (3) The `2`-term: `inclE (2 : K) = (2 : L) ≠ 0`.
  have h2K : inclE φ (rhoC φ α v L) (2 : K) ≠ 0 := fun h =>
    two_ne_zero (hinj (by simpa using h))
  have h3 : Function.HasFiniteSupport (fun w : NumberField.FinitePlace (EL φ (rhoC φ α v L)) =>
      |Real.log (w (inclE φ (rhoC φ α v L) (2 : K)))|) :=
    (finplace_log_abs_support h2K).2
  -- (2) The `∑_j`-term: summand by summand, using `log⁺ 1 = log⁺ 1⁻¹ = 0` (and `log⁺ 0 = 0`
  -- when `α' j = 0`, in which case the summand vanishes identically).
  have hterm : ∀ j : Fin r, Function.HasFiniteSupport
      (fun w : NumberField.FinitePlace (EL φ (rhoC φ α v L)) =>
        ((pDj r (dK K) σl j : ℕ) : ℝ) *
          (if 0 ≤ s then w (inclE φ (rhoC φ α v L) (α' j))
             else (w (inclE φ (rhoC φ α v L) (α' j)))⁻¹).posLog) := by
    intro j
    by_cases hαj : α' j = 0
    · have hzero : (fun w : NumberField.FinitePlace (EL φ (rhoC φ α v L)) =>
          (((pDj r (dK K) σl j : ℕ) : ℝ) *
            (if 0 ≤ s then w (inclE φ (rhoC φ α v L) (α' j))
               else (w (inclE φ (rhoC φ α v L) (α' j)))⁻¹).posLog)) =
          fun _ => (0 : ℝ) := by
        funext w
        rw [hαj, map_zero, map_zero]
        by_cases hs : 0 ≤ s <;> simp [hs]
      rw [hzero]
      exact Set.finite_empty.subset fun w hw => by simpa using hw
    · exact finplace_posLog_sgn_support
        (x := inclE φ (rhoC φ α v L) (α' j)) (fun h => hαj (hinj (by simpa using h))) s _
  have h2 : Function.HasFiniteSupport (fun w : NumberField.FinitePlace (EL φ (rhoC φ α v L)) =>
      ∑ j, ((pDj r (dK K) σl j : ℕ) : ℝ) *
        (if 0 ≤ s then w (inclE φ (rhoC φ α v L) (α' j))
           else (w (inclE φ (rhoC φ α v L) (α' j)))⁻¹).posLog) :=
    Function.HasFiniteSupport.sum hterm Finset.univ
  -- (4) The linear combination, using closure of `HasFiniteSupport` under addition and
  -- multiplication by constants.
  have h4 : Function.HasFiniteSupport (fun w : NumberField.FinitePlace (EL φ (rhoC φ α v L)) =>
      Real.log (⨆ lm, w (inclE φ (rhoC φ α v L) (p lm)))
        + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) *
            (∑ j, ((pDj r (dK K) σl j : ℕ) : ℝ) *
              (if 0 ≤ s then w (inclE φ (rhoC φ α v L) (α' j))
                 else (w (inclE φ (rhoC φ α v L) (α' j)))⁻¹).posLog)
        + 2 * ((J : ℝ) + 1) * (acH K b v : ℝ) * ((pD0 r (dK K) σl : ℝ) + 1)
            * |Real.log (w (inclE φ (rhoC φ α v L) (2 : K)))|) := by
    refine (h1.add ?_).add ?_
    · exact Function.HasFiniteSupport.mul_right
        (fun _ : NumberField.FinitePlace (EL φ (rhoC φ α v L)) => (((|s| : ℤ) : ℝ) / 2 / 2 ^ J))
        h2
    · exact Function.HasFiniteSupport.mul_right
        (fun _ : NumberField.FinitePlace (EL φ (rhoC φ α v L)) =>
          2 * ((J : ℝ) + 1) * (acH K b v : ℝ) * ((pD0 r (dK K) σl : ℝ) + 1)) h3
  exact ⟨h1, h2, h3, h4⟩

end Work.BW
