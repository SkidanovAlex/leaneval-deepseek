import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseB7.Estimates
import Submission.Work.BoseB7.boseModel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.exists_estHyp` — the §10 kernel hypotheses are consistent

An explicit witness for `∃ E : Q3Env (ZMod 2), EstHyp (boseFockData (ZMod 2)) E`.
It exhibits that the kernel/parameter hypotheses shared by the estimates of
`lem:EstimatesOnQ3-js` (`Work.BoseB7.EstHyp`) are consistent.

The witness is the free bosonic Fock space over the two-element mode group
`ZMod 2` (`boseFockData`, whose commutator kernel is `[a_i,a_j†] = δ_{ij}`, so
`ccrK i j = if i = j then 1 else 0`), together with the parameter point

* `z = ℓ = μ = a = K_H = K_ℓ = K_L = d = s = δ = 1`, `ε_T = b = 𝓜 = 0`,
* all kernels `0` except `χ̂² = δ₀` — exactly the box commutator kernel of the
  free model in the form `χ̂²(i-j) - χ̂(i)χ̂(j)` with `χ̂ ≡ 0`,
* `𝒜 ≡ 1`, `ℬ ≡ 0`, hence `α ≡ 0`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

/-- The witness parameter point: `𝒜 ≡ 1`, `ℬ ≡ 0` (so `α ≡ 0`), `χ̂² = δ₀`
(matching the free-model commutator kernel `[a_i,a_j†] = δ_{ij}`), `χ̂ ≡ 0`,
and every other kernel/scalar set to a harmless value. -/
def estHypWitnessEnv : Q3Env (ZMod 2) where
  z := 1
  ell := 1
  mu := 1
  aScat := 1
  KH := 1
  Kl := 1
  KL := 1
  d := 1
  s := 1
  eT := 0
  b := 0
  intM := 1
  bigM := 0
  delta := 1
  fL := fun _ => 0
  W1 := fun _ => 0
  W1omega := fun _ => 0
  W1omega0 := 0
  hatChi := fun _ => 0
  hatChiSq := fun k => if k = 0 then 1 else 0
  tau := fun _ => 0
  A := fun _ => 1
  B := fun _ => 0

/-- The squeezing parameter of the witness vanishes (`ℬ ≡ 0`). -/
lemma estHypWitnessEnv_alpha (k : ZMod 2) : estHypWitnessEnv.alpha k = 0 := by
  simp [Q3Env.alpha, alphaCoef, Submission.BoseGases.bogAlpha, estHypWitnessEnv]

/-- The parameter `𝓁` of the witness equals `1`. -/
lemma estHypWitnessEnv_lille : estHypWitnessEnv.lille = 1 := by
  simp [Q3Env.lille, lille, estHypWitnessEnv]

theorem exists_estHyp :
    ∃ E : Work.BoseB7.Q3Env (ZMod 2),
      Work.BoseB7.EstHyp (Work.BoseB7.boseFockData (ZMod 2)) E := by
  refine ⟨estHypWitnessEnv, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Bsmall
    intro k; simp [estHypWitnessEnv]
  · -- alphaLe
    intro k; rw [estHypWitnessEnv_alpha k, estHypWitnessEnv_lille]; simp
  · -- alphaEven
    intro k; simp [estHypWitnessEnv_alpha]
  · -- fLnonneg
    intro s; simp [estHypWitnessEnv]
  · -- fLle_one
    intro s; simp [estHypWitnessEnv]
  · -- fLeven
    intro s; simp [estHypWitnessEnv]
  · -- hatChiSqEven
    intro s; by_cases hs : s = 0 <;> simp [estHypWitnessEnv, hs]
  · -- hatChiEven
    intro s; simp [estHypWitnessEnv]
  · -- W1even
    intro s; simp [estHypWitnessEnv]
  · -- W1omegaEven
    intro s; simp [estHypWitnessEnv]
  · -- hasKernel
    intro i j
    have hk : (boseFockData (ZMod 2)).ccrK i j = if i = j then 1 else 0 := by
      simp [boseFockData]
    rw [hk]
    simp [estHypWitnessEnv, sub_eq_zero]
  · -- ccrBound
    intro i j
    have hk : (boseFockData (ZMod 2)).ccrK i j = if i = j then 1 else 0 := by
      simp [boseFockData]
    rw [hk]; split <;> norm_num
  · -- tauNonneg
    intro k; simp [estHypWitnessEnv]
  · -- Apos
    intro k; simp [estHypWitnessEnv]
  · -- ell_pos
    simp [estHypWitnessEnv]
  · -- mu_pos
    simp [estHypWitnessEnv]
  · -- a_pos
    simp [estHypWitnessEnv]
  · -- z_ne
    simp [estHypWitnessEnv]
  · -- b_nonneg
    simp [estHypWitnessEnv]
  · -- eT_nonneg
    simp [estHypWitnessEnv]
  · -- bigM_nonneg
    simp [estHypWitnessEnv]

end Work.BoseB7
