import Mathlib
import Submission.Work.Diff.EXT.splice_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The jet-level coordinate expression for the chart Ricci matrix

This file fixes the *vocabulary* of the lemma `Work.Diff.EXT.chartRic_mat_smooth_of_jet`: the
explicit coordinate (Christoffel) formula for the Ricci tensor, read off from the spatial `2`-jet
`(A, L, B)` of the chart matrix of a metric, together with the manifold-level notation
(`fvec`, `gmat`, `gRmC`) in which the bridge to `chartRicMat` is stated.

Notation: `n = Module.finrank ℝ E`, `bB` is the canonical basis of the model space `E`, and
`MatE = Fin n → Fin n → ℝ`.  Fix a chart centre `x₀` and a chart point `y = extChartAt I x₀ p`, and
let

`A i j  = g_{ij}(y)`,   `L (bB a) i j = ∂_a g_{ij}(y)`,   `B (bB a) (bB b) i j = ∂_a∂_b g_{ij}(y)`

be the metric coefficients in the coordinate frame of the chart at `x₀` together with their first
and second coordinate derivatives; these are the three components of
`jet2 (fun p : ℝ × E => chartMatFun g x₀ p.2) (0, y)`.  Then

* `jKz L a b c = Γ_{abc} = ½(∂_a g_{bc} + ∂_b g_{ac} - ∂_c g_{ab})` is the lowered (Koszul)
  Christoffel pairing;
* `jKzD B m a b c = ∂_m Γ_{abc}` is its derivative;
* `jInv A r s = γ^{rs}` is the inverse Gram matrix;
* `jGamU A L r a b = Γ^r_{ab} = ∑_p γ^{rp} Γ_{abp}` is the Christoffel symbol;
* `jRm A L B a b c d = R_{abcd} = ⟪R(σ_a,σ_b)σ_d, σ_c⟫` is the curvature component, given by
  `∂_a Γ_{dbc} - ∂_b Γ_{dac} - γ^{rs}Γ_{dbr}Γ_{acs} + γ^{rs}Γ_{dar}Γ_{bcs}`, the form in which the
  classical coordinate formula comes out of the Koszul pairing plus metric compatibility;
* `jRic A L B i j = Ric_{ij} = ∑_{k,l} γ^{kl} R_{kilj}` is the Ricci tensor;
* `ricPhi` is the resulting candidate `Φ`.

Nothing here is proved; the file only records the formulas.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

noncomputable section

/-- The derivative `∂_m Γ_{abc}` of the Koszul pairing, read off from the second spatial jet `B`. -/
def jKzD (B : E →L[ℝ] E →L[ℝ] MatE (E := E)) (m a b c : Fin (Module.finrank ℝ E)) : ℝ :=
  (1 / 2) * (B (bB m) (bB a) b c + B (bB m) (bB b) a c - B (bB m) (bB c) a b)

/-- The Koszul (lowered Christoffel) pairing `Γ_{abc} = ½(∂_a g_{bc} + ∂_b g_{ac} - ∂_c g_{ab})`,
read off from the first spatial jet `L` of the chart matrix. -/
def jKz (L : E →L[ℝ] MatE (E := E)) (a b c : Fin (Module.finrank ℝ E)) : ℝ :=
  (1 / 2) * (L (bB a) b c + L (bB b) a c - L (bB c) a b)

/-- The inverse Gram matrix (`γ^{rs}`) of the metric coefficients `A`. -/
def jInv (A : MatE (E := E)) (r s : Fin (Module.finrank ℝ E)) : ℝ :=
  (Matrix.of A)⁻¹ r s

/-- The Christoffel symbol `Γ^r_{ab} = ∑_p γ^{rp} Γ_{abp}`. -/
def jGamU (A : MatE (E := E)) (L : E →L[ℝ] MatE (E := E))
    (r a b : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ p, jInv A r p * jKz L a b p

/-- The curvature components `R_{abcd} = ⟪R(σ_a,σ_b)σ_d, σ_c⟫` in the coordinate frame, in the form
in which the classical coordinate formula comes out of the Koszul pairing together with metric
compatibility:
`R_{abcd} = ∂_a Γ_{dbc} - ∂_b Γ_{dac} - γ^{rs}Γ_{dbr}Γ_{acs} + γ^{rs}Γ_{dar}Γ_{bcs}`. -/
def jRm (A : MatE (E := E)) (L : E →L[ℝ] MatE (E := E))
    (B : E →L[ℝ] E →L[ℝ] MatE (E := E)) (a b c d : Fin (Module.finrank ℝ E)) : ℝ :=
  jKzD B a d b c - jKzD B b d a c
    - (∑ r, ∑ s, jInv A r s * jKz L d b r * jKz L a c s)
    + (∑ r, ∑ s, jInv A r s * jKz L d a r * jKz L b c s)

/-- The Ricci components `Ric_{ij} = ∑_{k,l} γ^{kl} R_{kilj}` in the coordinate frame. -/
def jRic (A : MatE (E := E)) (L : E →L[ℝ] MatE (E := E))
    (B : E →L[ℝ] E →L[ℝ] MatE (E := E)) (i j : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ k, ∑ l, jInv A k l * jRm A L B k i l j

/-- **The candidate `Φ`**: the coordinate expression for the Ricci matrix of a metric as a
function of the `2`-jet of its chart matrix. -/
def ricPhi (z : E × (MatE (E := E) × (E →L[ℝ] MatE (E := E)) ×
      (E →L[ℝ] E →L[ℝ] MatE (E := E)))) : MatE (E := E) :=
  fun i j => jRic z.2.1 z.2.2.1 z.2.2.2 i j

end

/-! ## The manifold-level notation -/

section Manifold

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The `k`-th vector of the coordinate frame of the chart at `x₀`, at the point `p`. -/
noncomputable def fvec (x₀ p : M) (k : Fin (Module.finrank ℝ E)) : TangentSpace I p :=
  Submission.Geodesic.frameVector (I := I) x₀ p (bB k)

/-- The Gram matrix of the coordinate frame at `p` (the chart matrix of `g` at `(extChartAt I x₀) p`). -/
noncomputable def gmat (g : Submission.Diff.SMet I M) (x₀ p : M) : MatE (E := E) :=
  fun r s => g.inner p (fvec (I := I) x₀ p r) (fvec (I := I) x₀ p s)

/-- The curvature components `⟪R(σ_a,σ_b)σ_d, σ_c⟫` of `g` in the coordinate frame at `p`. -/
noncomputable def gRmC (g : Submission.Diff.SMet I M) (x₀ p : M)
    (a b c d : Fin (Module.finrank ℝ E)) : ℝ :=
  g.inner p (Submission.Diff.rmVec (Submission.Diff.lcOf g) p
      (fvec (I := I) x₀ p a) (fvec (I := I) x₀ p b) (fvec (I := I) x₀ p d))
    (fvec (I := I) x₀ p c)

end Manifold

end Work.Diff.EXT
