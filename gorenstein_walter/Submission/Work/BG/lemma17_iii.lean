import Mathlib
import Submission.Work.BG.Defs
import Submission.Work.BG.Lambda
import Submission.Work.BG.H0Conj
import Submission.Work.BG.CharBridge
import Submission.Work.BG.lemma17_ii
import Submission.Work.BG.conjByH_basic
import Submission.Work.BG.lemma17_ii_aux
import Submission.Work.BG.lemma17_iii_aux
import Submission.Work.BG.lemma17_iii_dualC2
import Submission.Work.BG.lemma17_iii_lam2Conj
import Submission.Work.BG.lemma17_iii_regroup
import Submission.Work.BG.lemma17_iii_coeff

/-!
# Area BG: Bender–Glauberman 1981, Lemma 1.7(iii)

The formal target is `Work.BG.Lemma17iiiProp` (`Submission/Work/BG/H0Conj.lean`): with
Hypothesis 1.2, `|H₀ : U| = 2`, `s ∈ H ∖ H₀`, `λ₂` the non-trivial linear character of
`H₀/U`, `rep` a system of `Λ`-orbit representatives of `Irr(H₀)` (with trivial stabilisers,
`hfree`) and `χ ∈ ℤ[Irr G]`,

`χ(g) = ∑_{ν ∈ rep} (χ, (ν − λ₂ν^s)^G)_G · ν(g)` for all `g ∈ T = H₀ ∖ U`.

## Proof

Since `χ(g) = χ|_{H₀}(g)` and Fourier inversion expands `χ|_{H₀}` in `Irr(H₀)`, the
regrouping step `Work.BG.lemma17_iii_regroup` turns the left-hand side into

`∑_{μ ∈ rep} ( a_μ · μ(g) + a_{λ₂μ} · (λ₂μ)(g) )`,   `a_ν = (χ|_{H₀}, ν)_{H₀}`,

using that (i) `N_G(T) = H` forces `H` to normalise `U`, hence `H₀/U ≅ C₂`'s unique
non-trivial character `λ₂` is fixed by `s`-conjugation on `H₀`, and (ii) `Λ = {1, λ₂}` so the
`Λ`-orbits are the pairs `{μ, λ₂μ}` with `μ ∈ rep` (`hfree`, `hdisj`, `hov` supply the
covering and the trivial stabilisers).  On `T` the value of `λ₂` is `−1`
(`Work.BG.lemma17_iii_dualC2`), which turns the sum into
`∑_{μ ∈ rep} (a_μ − a_{λ₂μ}) · μ(g)`; finally Frobenius reciprocity together with the
`s`-invariance of `χ|_{H₀}` identifies the coefficient with
`(χ, (μ − λ₂μ^s)^G)_G` (`Work.BG.lemma17_iii_coeff`).
-/

namespace Work.BG

open OddOrder.RepresentationTheory

theorem lemma17_iii : Work.BG.Lemma17iiiProp := by
  intro G instG instFin instFintype P hUn hFintypeH0 hInvH0 hInvG hFintypeDual hFintypeIrr
    h2 s hs lam2 hlam2 rep hirr hfree hdisj hov χ hχ g hgU
  have hkey := lemma17_iii_regroup P h2 hlam2 rep hirr hfree hdisj hov χ g
  rw [hkey]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hBg : ClassFunction.compHom (quotMk P) (linearClassFunction lam2) g = -1 := by
    have hx : quotMk P g ≠ 1 := fun hh => hgU ((QuotientGroup.eq_one_iff g).mp hh)
    exact (lemma17_iii_dualC2 P h2 hlam2).2 (quotMk P g) hx
  rw [lemma17_iii_coeff P h2 s hlam2 χ μ]
  rw [ClassFunction.mul_apply, hBg]
  ring

end Work.BG
