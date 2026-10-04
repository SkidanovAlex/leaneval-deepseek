import Mathlib
import Submission.Work.Diff.EXT.ricJetDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The DeTurck operator `P(g) = -2 Ric(g) + L_{W(g)} g` at the level of jets

This file fixes the *vocabulary* of the chartwise (jet-level) DeTurck operator, the modified Ricci
flow operator of the DeTurck trick whose principal part is the scalar operator
`Σ_{c,d} γ^{cd} ∂_c∂_d`:

  `W(g) = tr_g (∇^g - ∇^{g̃})`, i.e. `W^k = g^{ij}(Γ^k_{ij} - Γ̃^k_{ij})`   (`jWU`),
  `P(g) = -2 Ric(g) + L_{W(g)} g`                                          (`pPhi`),

where `g̃` is a fixed background metric and `Γ`, `Γ̃` are the Christoffel symbols of `g`, `g̃` read
in a chart.  All the formulas below are stated in terms of the spatial `2`-jet `(A, L, B)` of the
chart matrix of `g` (and the analogous `(Abar, Lbar, Bbar)` for the background), exactly in the language of
`Submission.Work.Diff.EXT.ricJetDefs`:

`A i j = g_{ij}`,   `L (bB a) i j = ∂_a g_{ij}`,   `B (bB a) (bB b) i j = ∂_a∂_b g_{ij}`.

The main statements about these definitions (proved elsewhere, by delegation) are

* `Work.Diff.STE.DeTurck.pPhi_decomp`:  `pPhi = secOp + pN`, i.e. the second-jet dependence of `P`
  is exactly the scalar principal part `secOp A B i j = Σ_{cd} γ^{cd} B(c)(d)(i)(j)`;
* the *bridge*: the chart matrix of the geometric tensor `-2Ric(g) + L_{W(g)}g` is the
  above expression in the jets.

## Numerical validation (Scratch_room/deTurck_jet_check.py, in the workspace root)

The definitions below were checked against an independent, exact-arithmetic computation (a
polynomial metric with rational coefficients, the classical coordinate formulas for `Γ`, `Ric`,
`W`, `∇W`, compared with the workspace's `jRic`, which is the verified coordinate expression of
Mathlib's `curv`): for random symmetric jet data and a flat background the two agree *exactly*, and
`pPhi - secOp` is independent of `B` (the DeTurck cancellation).  See `Scratch_room/` and the
`DESIGN.md` of this area.
-/

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

namespace Work.Diff.STE.DeTurck

open Work.Diff.EXT

noncomputable section

/-- The index type of all component computations: the canonical basis `bB` of the model space. -/
abbrev Idx (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :=
  Fin (Module.finrank ℝ E)

/-- First jets of the chart matrix: `E →L[ℝ] MatE`, with `L (bB a) i j = ∂_a g_{ij}`. -/
abbrev LinMat (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :=
  E →L[ℝ] Work.Diff.EXT.MatE (E := E)

/-- Second jets of the chart matrix: `B (bB a) (bB b) i j = ∂_a∂_b g_{ij}`. -/
abbrev BilMat (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :=
  E →L[ℝ] E →L[ℝ] Work.Diff.EXT.MatE (E := E)

/-- `∂_a γ^{ij} = -Σ_{pq} γ^{ip}γ^{jq} ∂_a g_{pq}`, the coordinate derivative of the inverse Gram
matrix, read off from the first jet `L`. -/
def jdInv (A : MatE (E := E)) (L : LinMat E) (a i j : Idx E) : ℝ :=
  -∑ p, ∑ q, jInv A i p * jInv A j q * L (bB (E := E) a) p q

/-- `∂_a Γ^r_{ij} = Σ_p (∂_a γ^{rp}) Γ_{ijp} + Σ_p γ^{rp} ∂_a Γ_{ijp}`, the coordinate derivative
of the upper Christoffel symbol, read off from the first and second jets. -/
def jdGamU (A : MatE (E := E)) (L : LinMat E) (B : BilMat E)
    (a r i j : Idx E) : ℝ :=
  ∑ p, (jdInv A L a r p * jKz L i j p + jInv A r p * jKzD B a i j p)

/-- The coordinates of the DeTurck field `W(g) = tr_g(∇^g - ∇^{g̃})`, i.e.
`W^k = Σ_{ij} g^{ij}(Γ^k_{ij} - Γ̃^k_{ij})`. -/
def jWU (A : MatE (E := E)) (L : LinMat E) (Abar : MatE (E := E)) (Lbar : LinMat E)
    (k : Idx E) : ℝ :=
  ∑ i, ∑ j, jInv A i j * (jGamU A L k i j - jGamU Abar Lbar k i j)

/-- The lowered DeTurck field `W_b = g_{bc}W^c`. -/
def jWb (A : MatE (E := E)) (L : LinMat E) (Abar : MatE (E := E)) (Lbar : LinMat E)
    (b : Idx E) : ℝ :=
  ∑ c, A b c * jWU A L Abar Lbar c

/-- `∂_a W^c`, the coordinate derivative of the DeTurck field, read off from the jets. -/
def jdWU (A : MatE (E := E)) (L : LinMat E) (B : BilMat E)
    (Abar : MatE (E := E)) (Lbar : LinMat E) (Bbar : BilMat E) (a c : Idx E) : ℝ :=
  ∑ i, ∑ j, (jdInv A L a i j * (jGamU A L c i j - jGamU Abar Lbar c i j)
    + jInv A i j * jdGamU A L B a c i j
    - jInv A i j * jdGamU Abar Lbar Bbar a c i j)

/-- `∂_a W_b`, the coordinate derivative of the lowered DeTurck field. -/
def jdWb (A : MatE (E := E)) (L : LinMat E) (B : BilMat E)
    (Abar : MatE (E := E)) (Lbar : LinMat E) (Bbar : BilMat E) (a b : Idx E) : ℝ :=
  ∑ c, (L (bB (E := E) a) b c * jWU A L Abar Lbar c + A b c * jdWU A L B Abar Lbar Bbar a c)

/-- `∇_a W_b = ∂_a W_b - Γ^c_{ab}W_c`, the covariant derivative of the (lowered) DeTurck field. -/
def jnabW (A : MatE (E := E)) (L : LinMat E) (B : BilMat E)
    (Abar : MatE (E := E)) (Lbar : LinMat E) (Bbar : BilMat E) (a b : Idx E) : ℝ :=
  jdWb A L B Abar Lbar Bbar a b - ∑ c, jGamU A L c a b * jWb A L Abar Lbar c

/-- `(L_W g)_{ab} = ∇_aW_b + ∇_bW_a`, the Lie derivative of the metric along the DeTurck field. -/
def jLW (A : MatE (E := E)) (L : LinMat E) (B : BilMat E)
    (Abar : MatE (E := E)) (Lbar : LinMat E) (Bbar : BilMat E) (a b : Idx E) : ℝ :=
  jnabW A L B Abar Lbar Bbar a b + jnabW A L B Abar Lbar Bbar b a

/-- **The DeTurck operator in coordinates**:
`P(g)_{ij} = -2 Ric_{ij} + (L_{W(g)} g)_{ij}`, as a function of the `2`-jet of the chart matrix of
`g` and of the (fixed) `2`-jet of the background metric `g̃`. -/
def pPhi (Abar : MatE (E := E)) (Lbar : LinMat E) (Bbar : BilMat E)
    (A : MatE (E := E)) (L : LinMat E) (B : BilMat E) : MatE (E := E) :=
  fun i j => -2 * jRic A L B i j + jLW A L B Abar Lbar Bbar i j

/-- The lower-order part of `pPhi`, i.e. `pPhi` evaluated at the vanishing second jet. -/
def pN (Abar : MatE (E := E)) (Lbar : LinMat E) (Bbar : BilMat E)
    (A : MatE (E := E)) (L : LinMat E) : MatE (E := E) :=
  pPhi Abar Lbar Bbar A L 0

/-- The scalar principal part `Σ_{c,d} γ^{cd} B(c)(d)` of the DeTurck operator. -/
def secOp (A : MatE (E := E)) (B : BilMat E) : MatE (E := E) :=
  fun i j => ∑ c, ∑ d, jInv A c d * B (bB (E := E) c) (bB (E := E) d) i j

end

end Work.Diff.STE.DeTurck
