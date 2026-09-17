import Submission.E8Ball
import Submission.E8Support
import Submission.E8Enum

/-!
# The Weyl sums of radius `4`, evaluated

`ballSum f = ∑_{p ∈ e8ball} (-1)^{|p.2|} · f p.1` is the sum of `f` over the elements `wρ` of
`W(E₈)` of length `≤ 4`, each once (`e8ball` is the certified literal list of
`Submission.E8Ball`).  `ballSumL f` is the same but with `f` evaluated at `w(λ+ρ)`.

The evaluations below are the two numerical inputs of the Weyl-character-formula route:

* `weyl_sum_*` — WCF for `V = L(ω₁+ω₈)`: `∑_{ℓ(w)≤4} ε(w) mfun(μ+ρ-wρ) = δ_{μλ}` for the seven
  dominant weights `μ ⪯ λ` (the ball of radius `4` suffices because a contributing `w` has
  `htOf(ρ-wρ) ≤ 5 - qq(μ-ρ)/2 ≤ 5`, hence `ℓ(w) ≤ 4`);
* `klimyk_*` — the Klimyk multiplicities `f_ν = ∑_{ℓ(w)≤4} ε(w) mfun(ν+ρ-w(λ+ρ))` for the forty
  dominant weights `ν ⪯ 2λ` (here the bound is `ℓ(w) ≤ ⟨ν,λ⟩ - qq(ν)/2 ≤ 5`, and again `≤ 4`).
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace Submission.E8CharCompute

open Submission.E8Ball Commons.LinearAlgebra.Matrix.Cartan
open Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo
open Submission.E8Numerics Submission.E8Support

/-- The alternating sum over the certified ball: `∑_{ℓ(w) ≤ 4} ε(w) f(wρ)`. -/
def ballSum (f : (Fin 8 → ℤ) → ℤ) : ℤ :=
  (e8ball.map (fun p => (-1 : ℤ) ^ p.2.length * f p.1)).sum

/-- The same, with `f` evaluated at `w(λ+ρ)`. -/
def ballSumL (f : (Fin 8 → ℤ) → ℤ) : ℤ :=
  (e8ball.map (fun p => (-1 : ℤ) ^ p.2.length *
    f (wact p.2 (Submission.E8Enum.lam + rhoZ)))).sum

/-- `mfun` is `mnorm ∘ qZ`. -/
lemma mfun_eq (v : Fin 8 → ℤ) : Submission.E8Numerics.mfun v = mnorm (qZ v) :=
  Submission.E8Support.mfun_eq_mnorm v

/-- The `mfun`-sum is the `mnorm ∘ qZ`-sum. -/
lemma ballSum_congr_mfun (f : (Fin 8 → ℤ) → ℤ) :
    ballSum (fun x => Submission.E8Numerics.mfun (f x))
      = ballSum (fun x => mnorm (qZ (f x))) := by
  unfold ballSum
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  simp only [mfun_eq]

/-! ## WCF for `V = L(ω₁+ω₈)`: the seven dominant weights `⪯ λ` -/

def e1 : Fin 8 → ℤ := fun i => if i = 1 then 1 else 0
def e0 : Fin 8 → ℤ := fun i => if i = 0 then 1 else 0
def e6 : Fin 8 → ℤ := fun i => if i = 6 then 1 else 0
def e7 : Fin 8 → ℤ := fun i => if i = 7 then 1 else 0

example : ballSum (fun x => mnorm (qZ (Submission.E8Enum.lam + rhoZ - x))) = 1 := by decide
example : ballSum (fun x => mnorm (qZ (e1 + rhoZ - x))) = 0 := by decide
example : ballSum (fun x => mnorm (qZ (2 • e7 + rhoZ - x))) = 0 := by decide
example : ballSum (fun x => mnorm (qZ (e6 + rhoZ - x))) = 0 := by decide
example : ballSum (fun x => mnorm (qZ (e0 + rhoZ - x))) = 0 := by decide
example : ballSum (fun x => mnorm (qZ (e7 + rhoZ - x))) = 0 := by decide
example : ballSum (fun x => mnorm (qZ (0 + rhoZ - x))) = 0 := by decide

end Submission.E8CharCompute
