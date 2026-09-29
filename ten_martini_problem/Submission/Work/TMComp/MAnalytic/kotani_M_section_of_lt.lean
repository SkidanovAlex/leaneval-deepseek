import Mathlib
import Submission.Work.TMContract.Defs
import Submission.Work.TMComp.MAnalytic.kotaniDomain_open_and_preconnected
import Submission.Work.TMComp.MAnalytic.amoM_section_upper
import Submission.Work.TMComp.MAnalytic.differentiableOn_mob_tmC_M

/-!
# Kotani's section relation on a *connected* Kotani domain

This is the corrected form of the requested lemma `Work.TMComp.MAnalytic.kotani_M_section`:
the hypothesis `a < b` (i.e. connectedness of `kotaniDomain a b`) was missing from the request,
and without it the statement is **false**, because for `a ≥ b` the domain is
`{z : ℂ | z.im ≠ 0}`, whose two halves `{im > 0}` and `{im < 0}` are disjoint open sets: the
identity theorem cannot cross the real axis, and `M` is completely free — modulo the
hypotheses — on the lower half plane.

Concretely, with `a = b = 0`, `λ > 0`, `β = 1/2` and `W = conj z` (`im z < 0`),

`  M z x := mfun α lam (conj z) x`  for `im z > 0`    (so that `M = amoM` above the axis), and
`  M z x := 1 / conj (mfun α lam (conj z) (α - x + β))`  for `im z < 0`,

satisfies every hypothesis (`hcont`, `hhol`, `hamoM`, `him`, `hper`) but not the conclusion.
Indeed, writing `u x := M z x`, the covariance relation `mfun W (y+α) = W - pot y - 1/mfun W y`
applied at `y = β - x` gives `1/u x = z - pot (β - x) - u (x + α)`, while the conclusion at `x`
is exactly `1/u x = z - pot x - u (x + α)`; both would force `pot (β - x) = pot x` for all `x`,
i.e. `pot ≡ 0` (at `x = 0`: `2λ cos (2πβ) = 2λ`, false for `β = 1/2`, `λ ≠ 0`).

With `a < b` the domain is star-shaped (hence preconnected) at the real midpoint `(a+b)/2`,
and the argument goes through: for fixed real `x`, both `z ↦ M z (x+α)` and
`z ↦ mob (tmC lam z x) (M z x)` are holomorphic on `kotaniDomain a b`, they agree on the
nonempty open subset `{4 < im z} ⊆ ℍ` (where `M` equals `amoM` and `amoM` satisfies the
section relation, `amoM_section_upper`), and the identity theorem propagates this to the
whole connected domain.
-/

namespace Work.TMComp.MAnalytic

open Work.TMContract Filter Topology

noncomputable section

/-- If `M` is a continuous, in `z` holomorphic, upper-half-plane valued, `x`-periodic section
which agrees with `amoM` on the upper half plane, and the Kotani domain is connected
(`a < b`), then `M` satisfies the invariant section relation `M z (x+α) = S_z(x) · M z x`
on the whole domain. -/
theorem kotani_M_section_of_lt {α lam a b : ℝ} (h0 : 0 < lam) (hab : a < b) {M : ℂ → ℝ → ℂ}
    (hcont : ContinuousOn (fun p : ℂ × ℝ => M p.1 p.2) (kotaniDomain a b ×ˢ Set.univ))
    (hhol : ∀ x : ℝ, DifferentiableOn ℂ (fun z => M z x) (kotaniDomain a b))
    (hamoM : ∀ z : ℂ, 0 < z.im → ∀ x : ℝ, M z x = amoM α lam z x)
    (him : ∀ z ∈ kotaniDomain a b, ∀ x : ℝ, 0 < (M z x).im)
    (hper : ∀ (z : ℂ) (x : ℝ), M z (x + 1) = M z x) :
    ∀ z ∈ kotaniDomain a b, ∀ x : ℝ,
      M z (x + α) = mob (tmC lam z x) (M z x) := by
  obtain ⟨hUopen, hUpre⟩ := kotaniDomain_open_and_preconnected a b hab
  intro z hz x
  -- both sides are holomorphic functions of `z` on the domain
  have hf : AnalyticOnNhd ℂ (fun w : ℂ => M w (x + α)) (kotaniDomain a b) :=
    (hhol (x + α)).analyticOnNhd hUopen
  have hg : AnalyticOnNhd ℂ (fun w : ℂ => mob (tmC lam w x) (M w x)) (kotaniDomain a b) :=
    (differentiableOn_mob_tmC_M (a := a) (b := b) (lam := lam) hhol him x).analyticOnNhd hUopen
  -- they agree on the open set `{4 < im z}`
  have hz0 : (((5 : ℝ) : ℂ) * Complex.I) ∈ kotaniDomain a b := by
    simp only [kotaniDomain, Set.mem_ofPred_eq]
    exact Or.inl (by simp)
  have hz0im : (((5 : ℝ) : ℂ) * Complex.I) ∈ {w : ℂ | 4 < w.im} := by
    simp only [Set.mem_ofPred_eq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, add_zero]
    norm_num
  have heq : (fun w : ℂ => M w (x + α))
      =ᶠ[nhds (((5 : ℝ) : ℂ) * Complex.I)] (fun w : ℂ => mob (tmC lam w x) (M w x)) := by
    refine Filter.eventually_of_mem
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz0im) ?_
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw
    have hwpos : 0 < w.im := by linarith
    change M w (x + α) = mob (tmC lam w x) (M w x)
    rw [hamoM w hwpos (x + α), hamoM w hwpos x]
    exact (amoM_section_upper (α := α) h0 (le_of_lt hw) x).symm
  -- identity theorem on the preconnected domain
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hf hg hUpre hz0 heq hz

end

end Work.TMComp.MAnalytic
