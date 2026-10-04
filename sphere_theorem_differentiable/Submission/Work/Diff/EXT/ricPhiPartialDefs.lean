import Mathlib
import Submission.Work.Diff.EXT.splice_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The scalar-`2`-jet formula for the chart Ricci matrix (area `EXT`)

This file fixes the *vocabulary* of the lemma `Work.Diff.EXT.chartRic_jet_partial`: the explicit
coordinate (Christoffel) formula for the Ricci tensor, read off from the **scalar** `2`-jet of the
chart matrix of a metric, i.e. from the value, the first and the second *coordinate partial*
derivatives of `chartMatFun g x₀`.

Notation: `n = Module.finrank ℝ E`, `MatE = Fin n → Fin n → ℝ`, and

* `A i j`      is the metric coefficient `g_{ij}`,
* `L k i j`    is the first coordinate partial `∂_k g_{ij}`,
* `B k l i j`  is the second coordinate partial `∂_k∂_l g_{ij}`,

the three components of `sJetData (fun p : ℝ × E => chartMatFun g x₀ p.2) (0, y)`.  Then

* `sKz L a b c = Γ_{abc} = ½(∂_a g_{bc} + ∂_b g_{ac} − ∂_c g_{ab})` is the lowered (Koszul)
  Christoffel pairing;
* `sKzD B m a b c = ∂_m Γ_{abc}` is its derivative, read off from `B`;
* `sInv A r s = γ^{rs}` is the inverse Gram matrix;
* `sRm A L B a b c d = R_{abcd} = ⟪R(σ_a,σ_b)σ_d, σ_c⟫` is the curvature component, obtained from
  `R_{abcd} = ∂_a Γ_{bdc} − ∂_b Γ_{adc} − γ^{rs}Γ_{bdr}Γ_{acs} + γ^{rs}Γ_{adr}Γ_{bcs}`;
* `chartRicPhi` is the resulting candidate `Φ`: `Φ (y, (A, L, B)) i j = ∑_{k,l} γ^{kl} R_{kilj}`.

This is the scalar-jet analogue of `Work.Diff.EXT.ricPhi` (which reads `Φ` off the full `2`-jet
with continuous linear maps).  Only the definitions are recorded here.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

/-- The Koszul Christoffel pairing `Γ_{abc}` read off from the first coordinate partials `L`. -/
def sKz (L : Fin (Module.finrank ℝ E) → MatE (E := E))
    (a b c : Fin (Module.finrank ℝ E)) : ℝ :=
  (1 / 2) * (L a b c + L b a c - L c a b)

/-- The derivative `∂_m Γ_{abc}` of the Koszul pairing, read off from the second partials `B`. -/
def sKzD (B : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → MatE (E := E))
    (m a b c : Fin (Module.finrank ℝ E)) : ℝ :=
  (1 / 2) * (B m a b c + B m b a c - B m c a b)

/-- The inverse Gram matrix `γ^{rs}` of the metric coefficients `A`. -/
def sInv (A : MatE (E := E)) (r s : Fin (Module.finrank ℝ E)) : ℝ :=
  (Matrix.of A)⁻¹ r s

/-- The curvature components `R_{abcd} = ⟪R(σ_a,σ_b)σ_d, σ_c⟫` in the coordinate frame, read off
from the scalar `2`-jet `(A, L, B)` of the chart matrix. -/
def sRm (A : MatE (E := E)) (L : Fin (Module.finrank ℝ E) → MatE (E := E))
    (B : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → MatE (E := E))
    (a b c d : Fin (Module.finrank ℝ E)) : ℝ :=
  sKzD B a b d c - sKzD B b a d c
    - (∑ r, ∑ s, sInv A r s * sKz L b d r * sKz L a c s)
    + (∑ r, ∑ s, sInv A r s * sKz L a d r * sKz L b c s)

/-- **The candidate `Φ`** for `Work.Diff.EXT.chartRic_jet_partial`: the Ricci matrix of a metric as
a function of the scalar `2`-jet of its chart matrix,
`Φ (y, (A, L, B)) i j = ∑_{k,l} γ^{kl} R_{kilj}`. -/
def chartRicPhi
    (z : E × (MatE (E := E) × (Fin (Module.finrank ℝ E) → MatE (E := E)) ×
      (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → MatE (E := E)))) :
    MatE (E := E) :=
  fun i j => ∑ k, ∑ l, sInv z.2.1 k l * sRm z.2.1 z.2.2.1 z.2.2.2 k i l j

end

end Work.Diff.EXT

/-! ## Chart-frame vocabulary

Shorthands for the coordinate frame of the chart at `x₀`, its Gram matrix, and the scalar `2`-jet
of the chart matrix of a metric.  These are transparent (`abbrev`) or literal (`def`) wrappers, so
they cost nothing in the proofs; they keep the statements of the lemmas in this development short.
-/

namespace Work.Diff.EXT

section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]

/-- The coordinate-frame vector of the chart at `x₀` at the point `p` with coordinates `v`. -/
noncomputable abbrev cvec (x₀ p : M) (v : E) : TangentSpace I p :=
  Submission.Geodesic.frameVector (I := I) x₀ p v

/-- The Gram matrix of the coordinate frame of the chart at `x₀` at the point `p`. -/
noncomputable def cgramM (g : Submission.Diff.SMet I M) (x₀ p : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j => g.inner p (cvec (I := I) x₀ p (bB (E := E) i))
    (cvec (I := I) x₀ p (bB (E := E) j))

/-- The first component of the scalar `2`-jet of the chart matrix: its value at `y`. -/
noncomputable abbrev dJet0 (g : Submission.Diff.SMet I M) (x₀ : M) (y : E) : MatE (E := E) :=
  chartMatFun g x₀ y

/-- The first-order coordinate partial derivatives of the chart matrix at `y`, as a function of
the index `k` of the model basis. -/
noncomputable def dJet1 (g : Submission.Diff.SMet I M) (x₀ : M) (y : E) :
    Fin (Module.finrank ℝ E) → MatE (E := E) :=
  fun k => fderiv ℝ (chartMatFun g x₀) y (bB (E := E) k)

/-- The second-order coordinate partial derivatives of the chart matrix at `y`. -/
noncomputable def dJet2 (g : Submission.Diff.SMet I M) (x₀ : M) (y : E) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → MatE (E := E) :=
  fun k l => fderiv ℝ (fun y' : E => fderiv ℝ (chartMatFun g x₀) y') y
    (bB (E := E) k) (bB (E := E) l)

/-- The scalar `2`-jet of the chart matrix of `g` at `y`, packaged. -/
noncomputable abbrev chartJet (g : Submission.Diff.SMet I M) (x₀ : M) (y : E) :
    MatE (E := E) × (Fin (Module.finrank ℝ E) → MatE (E := E)) ×
      (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → MatE (E := E)) :=
  (dJet0 g x₀ y, dJet1 g x₀ y, dJet2 g x₀ y)

end Chart

end Work.Diff.EXT
