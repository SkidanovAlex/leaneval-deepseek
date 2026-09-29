import Mathlib
import Submission.Work.ZeroEst.defs

namespace Work.ZeroEst

/-!
# A monomial of minimal total degree (`Work.ZeroEst.exists_minCoeff`)

The first step of the "reduction" node of area Z (`Submission.CDTPlan.ZeroEstimate`, see the
docstring of `Submission/Work/ZeroEst/defs.lean`): if a multivariate power series `G` over `ℚ`
in `d` variables is nonzero, then among the monomials occurring in `G` there is one of minimal
total degree `Finsupp.degree`, and every monomial of strictly smaller total degree has zero
coefficient in `G`.

Nothing is used about `degree` except that it is a `ℕ`-valued function of the exponent, so the
argument is the well-ordering of `ℕ`: let `k` be the least value of `degree` attained by an
exponent with nonzero coefficient, and take a witness of `k`.

(Recall that in Mathlib an `MvPowerSeries σ R` is a function `(σ →₀ ℕ) → R`, so `G ≠ 0` gives
an exponent with nonzero coefficient by extensionality.)
-/

theorem exists_minCoeff {d : ℕ} (G : MvPowerSeries (Fin d) ℚ) (hG : G ≠ 0) :
    ∃ n : Fin d →₀ ℕ, MvPowerSeries.coeff n G ≠ 0 ∧
      ∀ n' : Fin d →₀ ℕ, n'.degree < n.degree → MvPowerSeries.coeff n' G = 0 := by
  classical
  -- `G` has a monomial with nonzero coefficient.
  have hne : ∃ n : Fin d →₀ ℕ, MvPowerSeries.coeff n G ≠ 0 := by
    by_contra h
    simp only [not_exists, not_ne_iff] at h
    exact hG (MvPowerSeries.ext fun n => by rw [h n, MvPowerSeries.coeff_zero])
  -- The set of total degrees attained by such monomials is nonempty, and we take its least
  -- element and a witness of it.
  have hP : ∃ k : ℕ, ∃ n : Fin d →₀ ℕ, MvPowerSeries.coeff n G ≠ 0 ∧ n.degree = k := by
    obtain ⟨n, hn⟩ := hne
    exact ⟨n.degree, n, hn, rfl⟩
  obtain ⟨n₀, hn₀, hdeg⟩ := Nat.find_spec hP
  refine ⟨n₀, hn₀, fun n' hn' => ?_⟩
  -- `n₀.degree` is the least degree of a nonzero coefficient, so a monomial of smaller
  -- degree cannot have nonzero coefficient.
  by_contra hc
  have hle := Nat.find_min' hP ⟨n', hc, rfl⟩
  omega

end Work.ZeroEst
