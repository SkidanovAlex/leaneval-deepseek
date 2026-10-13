import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dth
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dz
import Submission.Work.FTS.CoercivityFix.Assembly.RegQAux
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.CoercivityFix.E2Bound.E2hat_HkIntegrand_le_uniform
import Submission.Work.FTS.CoercivityFix.PsiMul.PsiZop
import Submission.Work.FTS.CoercivityFix.PsiMul.HkMem_psi_mul
import Submission.Work.FTS.CoercivityFix.PsiMul.BdryTraces_psi_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Assembly

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! # `RegQ` is closed under multiplication by a radial factor with bounded `Zop`-iterates

The interior class `Work.FTS.Nonlin.RegQ α k g = SmoothQuad g ∧ HkMem α k g ∧ BdryTraces α k g`
(`Submission/Work/FTS/Vocab.lean`) is the class in which the whole a-priori chapter is stated.
Multiplication by a function `ψ = ψ(z)` of `z` alone is not a differential operator, but it is
controlled by the two facts proved in `FTS/CoercivityFix/PsiMul/`:

* `HkMem_psi_mul`: `HkMem α k g → HkMem α k (ψ·g)`, via the pointwise multiplier estimate
  `Work.FTS.CoercivityFix.E2Bound.SlotMul.HkIntegrand_zmul_uniform`
  (`HkIntegrand α k (ψ·g) ≤ C·(1+K)²·HkIntegrand α k g` on the open quadrant) and the
  majorant criterion `Work.FTS.LocData.HkMem_of_majorant`;
* `BdryTraces_psi_mul`: `BdryTraces α k g → BdryTraces α k (ψ·g)`, via the Leibniz expansion
  `Work.FTS.CoercivityFix.E2Bound.mixed_zmul` of `D_z^b D_θ^a (ψ·g)` and the squeeze theorem.

Both hypotheses are on the `Zop`-iterates `Zop^[c] ψ = (z ∂_z)^c ψ`, `c ≤ k`, which are required
to be bounded on `(0,∞)` by a common `K`.  Smoothness of `ψ` on `(-1,∞)` gives `SmoothQuad`, and
`SmoothQuad` is closed under multiplication.

For the concrete factor `ψ(z) = 1/(1+z)` used by `Lhat = 𝓛 − Transport = f + D_z f − 2f/(1+z)
− 3 D_θ f/(1+z)`, the bound is `Work.FTS.CoercivityFix.PsiMul.zop_psi_bound` (proved by the
Möbius-chart/polynomial argument of `E2Bound.zop_phi_bound`) and the smoothness is
`Work.FTS.CoercivityFix.PsiMul.contDiffOn_psi`.

Everything rests on `[propext, Classical.choice, Quot.sound]`. -/

/-- **A radial multiplier preserves the interior class `RegQ`.**  If `ψ : ℝ → ℝ` is `C^∞` on
`(-1,∞)` and each `Zop`-iterate `Zop^[c] ψ` (`c ≤ k`) is bounded by `K` on `(0,∞)`, then
`g ∈ RegQ α k` implies `ψ·g ∈ RegQ α k`. -/
theorem RegQ_psi_mul {α : ℝ} {k : ℕ} {ψ : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hKb : ∀ c ≤ k, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[c] ψ z| ≤ K)
    (hsm : ContDiffOn ℝ Work.Stability.smoothOrder ψ (Set.Ioi (-1)))
    {g : ℝ → ℝ → ℝ} (hg : Work.FTS.Nonlin.RegQ α k g) :
    Work.FTS.Nonlin.RegQ α k (fun z θ => ψ z * g z θ) :=
  ⟨Work.FTS.LocData.smoothQuad_mul
      (Work.FTS.CoercivityFix.E2Bound.smoothQuad_of_zOnly hsm) hg.1,
    Work.FTS.CoercivityFix.PsiMul.HkMem_psi_mul α k hK hKb hsm hg.1 hg.2.1,
    Work.FTS.CoercivityFix.PsiMul.BdryTraces_psi_mul α k hKb hsm hg.1 hg.2.2⟩

/-- **The radial factor `ψ(z) = 1/(1+z)`**: it is `C^∞` on `(-1,∞)` and all its `Zop`-iterates
up to order `n` are bounded on `(0,∞)` by `K`. -/
theorem psi_bound (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ c ≤ n, ∀ z ∈ Set.Ioi (0 : ℝ),
        |Work.Spaces.Zop^[c] (fun z : ℝ => 1 / (1 + z)) z| ≤ K) ∧
      ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 1 / (1 + z)) (Set.Ioi (-1)) := by
  obtain ⟨K, hK0, hKb⟩ := Work.FTS.CoercivityFix.PsiMul.zop_psi_bound n
  exact ⟨K, hK0, hKb, Work.FTS.CoercivityFix.PsiMul.contDiffOn_psi⟩

/-- **The class `RegQ` is closed under multiplication by `1/(1+z)`.** -/
theorem RegQ_oneDiv_mul {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.Nonlin.RegQ α k g) :
    Work.FTS.Nonlin.RegQ α k (fun z θ => (1 / (1 + z)) * g z θ) := by
  obtain ⟨K, hK0, hKb, hsm⟩ := psi_bound k
  exact RegQ_psi_mul hK0 hKb hsm hg

/-! ## The target: `Lhat` is a `RegQ`-port -/

/-- **`Work.FTS.Nonlin.RegQ α n` is preserved by `𝓛̂ = 𝓛 − Transport`.**  The operator
`Lhat f = f + D_z f − 2f/(1+z) − 3 D_θ f/(1+z)` (`CoercivityFix.Lhat_eq`) is the sum of the
radial-multiplier pieces `f`, `D_z f`, `(1/(1+z))·f` and `(1/(1+z))·D_θ f`, each of which lies in
`RegQ α n` as soon as `f ∈ RegQ α (n+1)`:
`f` by monotonicity of the class (`Apriori.regQ_mono`), `D_z f` by `QuadPorts.RegQ_dz`,
`D_θ f` by `QuadPorts.RegQ_dth` (which needs `0 < α`), and the two radial multiples by
`RegQ_oneDiv_mul`.  The class is closed under sums, scalar multiples and differences
(`Apriori.regQ_add`, `regQ_smul`, `regQ_sub`). -/
theorem Lhat_RegQ (α : ℝ) (hα : 0 < α) {n : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.RegQ α (n + 1) f) :
    Work.FTS.Nonlin.RegQ α n (Work.FTS.CoercivityFix.Lhat f) := by
  have hf' : Work.FTS.Nonlin.RegQ α n f :=
    regQ_mono (Nat.le_succ n) hf
  have hdz : Work.FTS.Nonlin.RegQ α n (Work.Spaces.Dz f) :=
    Work.FTS.CoercivityFix.QuadPorts.RegQ_dz α hf
  have hdth : Work.FTS.Nonlin.RegQ α n (Work.Spaces.Dth f) :=
    Work.FTS.CoercivityFix.QuadPorts.RegQ_dth α hα hf
  have hp1 : Work.FTS.Nonlin.RegQ α n (fun z θ => (1 / (1 + z)) * f z θ) :=
    RegQ_oneDiv_mul hf'
  have hp2 : Work.FTS.Nonlin.RegQ α n (fun z θ => (1 / (1 + z)) * Work.Spaces.Dth f z θ) :=
    RegQ_oneDiv_mul hdth
  have hmain : Work.FTS.Nonlin.RegQ α n
      (fun z θ => (f z θ + Work.Spaces.Dz f z θ)
        - 2 * ((1 / (1 + z)) * f z θ)
        - 3 * ((1 / (1 + z)) * Work.Spaces.Dth f z θ)) :=
    regQ_sub
      (regQ_sub
        (regQ_add hf' hdz)
        (regQ_smul 2 hp1))
      (regQ_smul 3 hp2)
  rw [show Work.FTS.CoercivityFix.Lhat f
      = fun z θ => (f z θ + Work.Spaces.Dz f z θ)
        - 2 * ((1 / (1 + z)) * f z θ)
        - 3 * ((1 / (1 + z)) * Work.Spaces.Dth f z θ) from by
    funext z θ
    rw [Work.FTS.CoercivityFix.Lhat_eq]
    ring]
  exact hmain

end

end Work.FTS.CoercivityFix.Assembly
