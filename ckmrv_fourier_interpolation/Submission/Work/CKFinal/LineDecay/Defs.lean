import Mathlib
import Submission.Work.LayerCont.SplitPoint
import Submission.Work.Asymptotics.rectInt_eq_residue
import Submission.Work.Residues.ResidueSecondVariable
import Submission.Work.LayerCont.Right.Defs
import Submission.Work.LayerCont.Arc.Defs
import Submission.Work.LayerCont.FarTail.CuspFar
import Submission.Work.Asymptotics.CuspDecay.Regimes
import Submission.Work.Asymptotics.KPlus_slash_bound_funnel
import Submission.Work.Asymptotics.KMinus_slash_bound_E
import Submission.Work.Asymptotics.Instances
import Submission.Work.Residues.KPlus_isBigO_atImInfty
import Submission.Work.Residues.KMinus_isBigO_atImInfty

/-!
# The line-decay computation of CKMRV (4.2toshow2)/(4.2toshow3): shared definitions

This file sets up the objects of the contour-shift computation on the two lines
`Re τ = ±1/2`: the split point `H = 1`, the "shifted" evaluation `Kax K τ x t = K(τ, x + i t)`,
the second difference `Φ = 2K(τ,·) - K(τ,·-1) - K(τ,·+1)`, the pieces `P₁, P₂, P₃` of the
shifted representation, and the "hatted" layer (the layer built from the kernel `K̂` and the
model `Ĝ = -σ^{-d/2}𝒢(S•σ)`).
-/

noncomputable section

namespace Work.CKFinal

open UpperHalfPlane MeasureTheory
open scoped Topology Manifold

/-- The split point `H = 1` used in the contour shift on the lines `Re τ = ±1/2`. -/
def hsplit : ℝ := 1

/-- The point `x + i t` of `ℍ`, as an evaluation point of a two-variable kernel (the value is
`0` off `t > 0`, in the same junk-value convention as `Work.Kernels.Kaxis`). -/
def Kax (K : ℍ → ℍ → ℂ) (τ : ℍ) (x t : ℝ) : ℂ :=
  if h : 0 < t then K τ ((x : ℝ) +ᵥ Work.Kernels.imagAxis t h) else 0

lemma Kax_eq_Kaxis (K : ℍ → ℍ → ℂ) (τ : ℍ) (t : ℝ) :
    Kax K τ 0 t = Work.Kernels.Kaxis K τ t := by
  rw [Kax, Work.Kernels.Kaxis]
  by_cases h : 0 < t
  · rw [dif_pos h, dif_pos h]
    congr 1
    exact zero_vadd ℝ _
  · rw [dif_neg h, dif_neg h]

/-- The second difference of the kernel `K(τ,·)` in its second variable, evaluated at `i t`:
`Φ(τ,i t) = 2K(τ,i t) - K(τ,i t-1) - K(τ,i t+1)`.  By CKMRV §5.3 this equals
`(K|^z_{2-d/2}(T+T^{-1}-2I))(τ,i t) = 2(K̂|^z_{2-d/2}S)(τ,i t)`, and it is the integrand that
survives the contour shift (the cusp model is annihilated by the second difference). -/
def Phi (K : ℍ → ℍ → ℂ) (τ : ℍ) (t : ℝ) : ℂ :=
  2 * Kax K τ 0 t - Kax K τ (-1) t - Kax K τ 1 t

/-- The low piece `P₁ = sinSqC r · ∫_0^H K(τ,i y) e^{-λ y} dy` of the shifted representation
(`λ = π r²`); this is exactly the `layerLow` term of `paperLayer`. -/
def P1 (K : ℍ → ℍ → ℂ) (r : ℝ) (τ : ℍ) : ℂ :=
  Work.Asymptotics.sinSqC r * ∫ t in (0 : ℝ)..hsplit,
    Kax K τ 0 t * Work.Asymptotics.gaussWeight r t

/-- The horizontal pieces `P₂` of the shifted representation, at height `H = 1`. -/
def P2 (K : ℍ → ℍ → ℂ) (r : ℝ) (τ : ℍ) : ℂ :=
  - Complex.I * (∫ x in (0 : ℝ)..1,
      Kax K τ (x - 1) hsplit
        * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ)
            * ((x : ℂ) + (hsplit : ℂ) * Complex.I)))
    + Complex.I * (∫ x in (-1 : ℝ)..0,
      Kax K τ (x + 1) hsplit
        * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ)
            * ((x : ℂ) + (hsplit : ℂ) * Complex.I)))

/-- The tail piece `P₃ = ∫_H^∞ Φ(τ,i t) e^{-λ t} dt` of the shifted representation. -/
def P3 (K : ℍ → ℍ → ℂ) (r : ℝ) (τ : ℍ) : ℂ :=
  ∫ t in Set.Ici hsplit, Phi K τ t * Work.Asymptotics.gaussWeight r t

/-- The cusp model `𝒢_G(τ,z) = G₀₀ + zG₀₁ + e^{-2πiz}(G₁₀ + zG₁₁)` in the second variable,
for a general coefficient function `G` (so that `Gmodel G τ (i t) = Aexp G τ t`).  This is the
function that the second difference in `z` annihilates. -/
def Gmodel (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ : ℍ) (z : ℂ) : ℂ :=
  G 0 0 τ + z * G 0 1 τ
    + Complex.exp (-(2 * Real.pi * Complex.I * z)) * (G 1 0 τ + z * G 1 1 τ)

/-- The `low` part of the layer with an arbitrary kernel. -/
def layerLowK (K : ℍ → ℍ → ℂ) (r : ℝ) (τ : ℍ) : ℂ :=
  Work.Asymptotics.sinSqC r * ∫ t in (0 : ℝ)..1,
    Kax K τ 0 t * Work.Asymptotics.gaussWeight r t

/-- The `trunc` part of the layer with an arbitrary kernel and model. -/
def layerTruncK (K : ℍ → ℍ → ℂ) (G : Fin 2 → Fin 2 → ℍ → ℂ) (r : ℝ) (τ : ℍ) : ℂ :=
  Work.Asymptotics.sinSqC r * ∫ t in Set.Ici (1 : ℝ),
    (Kax K τ 0 t - Work.Asymptotics.Aexp G τ t) * Work.Asymptotics.gaussWeight r t

/-- The layer `F₂` with an arbitrary kernel and model. -/
def paperLayerK (K : ℍ → ℍ → ℂ) (G : Fin 2 → Fin 2 → ℍ → ℂ) (r : ℝ) (τ : ℍ) : ℂ :=
  layerLowK K r τ + layerTruncK K G r τ + Work.Asymptotics.highPart G τ r

/-- The model of the hatted kernel: `Ĝ_{ij}(σ) = -σ^{-d/2} 𝒢_{ij}(S•σ)`, so that
`Aexp G τ t = -σ^{d/2} Aexp Ĝ σ t` for `τ = S • σ`. -/
def Ghat (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Fin 2 → Fin 2 → ℍ → ℂ :=
  fun i j σ => -((σ : ℂ) ^ (-((d : ℤ) / 2))) * Work.Asymptotics.Gcusp ℓ d i j (ModularGroup.S • σ)

end Work.CKFinal
