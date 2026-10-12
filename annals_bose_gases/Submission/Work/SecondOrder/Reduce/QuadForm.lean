import ChallengeDeps
import Submission.Work.SecondOrder.Reduce.pairStateE_eq_quadratic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/SecondOrder` — the residual as a finite quadratic form

By `Reduce.pairStateE_eq_quadratic` the energy of the pair-excited state *is*
the finite quadratic form `Σ_{p,q} w_p w_q · pairBilin p q` in the matching
amplitudes.  This module therefore records the variant of the family residual in
which the energy condition is stated directly for that quadratic form —
`PairFormBound` — and proves that it implies the family residual
`PairFamilyBound` (hence, by `Main.secondOrderUpperBound_of_pairFamily`, the
TrialState residual).

The point of the reformulation is that it isolates the *analytic* content of
the remaining gap from the structural content: the analytic content is the
finite quadratic-form inequality (the ESY/Yau–Yin computation), while
`pairStateE_eq_quadratic` (proved) is the structural identity that lets one
pass between the two.  The converse implication is not available without
regularity of the scattering solution (only `LocallyIntegrable` is known from
`IsScatteringSolution`), which is why `PairFamilyBound` — and not
`PairFormBound` — is the primitive residual.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.SecondOrder.Reduce

open Submission.BoseGases
open _root_.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The kinetic integrability needed by `pairStateE_eq_quadratic`. -/
def KinInt (N : ℕ) (ℓ : ℝ) (ψ : ℝ³ → ℝ) (G : ℝ³ → ℝ³ → ℝ) : Prop :=
  ∀ p ∈ pmatch N, ∀ q ∈ pmatch N, ∀ i : Fin N, ∀ k : Fin 3,
    MeasureTheory.IntegrableOn (fun x : X N =>
      fderiv ℝ (pairComp N ψ G p) x (kcDir N i k)
        * fderiv ℝ (pairComp N ψ G q) x (kcDir N i k)) (abox N ℓ)

/-- The potential integrability needed by `pairStateE_eq_quadratic`. -/
def PotInt (N : ℕ) (ℓ μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (ψ : ℝ³ → ℝ) (G : ℝ³ → ℝ³ → ℝ) : Prop :=
  ∀ p ∈ pmatch N, ∀ q ∈ pmatch N,
    MeasureTheory.IntegrableOn (fun x : X N => pairComp N ψ G p x * pairComp N ψ G q x *
      (- μ * (∑ i : Fin N, w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))
        + (1 / 2) * (∑ r ∈ pairSet N, wPairC ℓ v (x r.1) (x r.2)))) (abox N ℓ)

/-- **The pair-family residual in quadratic-form (Gram-matrix) form.**  The
energy condition is stated for `Σ_{p,q} w_p w_q · pairBilin p q` — the finite
quadratic form of the matching amplitudes — rather than for `pairStateE`. -/
def PairFormBound (N : ℕ) (ℓ μ C : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : Prop :=
  ∃ ψ : ℝ³ → ℝ, ∃ wt : ℕ → ℝ, ∃ G : ℝ³ → ℝ³ → ℝ,
    (∀ x y : ℝ³, G x y = G y x) ∧ Continuous (pairState N ψ wt G) ∧
      ContDiff ℝ 1 ψ ∧ ContDiff ℝ 1 (fun p : ℝ³ × ℝ³ => G p.1 p.2) ∧
      KinInt N ℓ ψ G ∧ PotInt N ℓ μ v h ψ G ∧
      pairStateZ N ℓ ψ wt G = 1 ∧
      (∑ p ∈ pmatch N, ∑ q ∈ pmatch N,
          wt (nPair p) * wt (nPair q) * pairBilin N ℓ μ v h ψ G p q)
        ≤ - 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 * (1 - C * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))

/-- **`PairFormBound` implies `PairFamilyBound`** — via the structural identity
`pairStateE_eq_quadratic`. -/
theorem pairFamilyBound_of_pairFormBound {N : ℕ} {ℓ μ C : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hb : PairFormBound N ℓ μ C v h) :
    Work.SecondOrder.PairFamilyBound N ℓ μ C v h := by
  obtain ⟨ψ, wt, G, hsym, hcont, hψ, hG, hkin, hpot, hnorm, hE⟩ := hb
  refine ⟨ψ, wt, G, hsym, hcont, hnorm, ?_⟩
  rw [pairStateE_eq_quadratic h hℓ hψ hG hkin hpot]
  exact hE

end Work.SecondOrder.Reduce
