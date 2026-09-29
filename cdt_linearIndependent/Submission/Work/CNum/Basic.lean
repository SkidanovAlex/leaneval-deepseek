import Mathlib
import Submission.CDTPlan.Interfaces

/-! # CNum: basic definitions for the certified numerics of `phiC` -/

namespace Work.CNum

open Complex Metric Filter Topology
open scoped BigOperators

/-- `c = 23/10`. -/
noncomputable def cR : ℝ := 23 / 10
/-- `(1+c^2)^2`. -/
noncomputable def AR : ℝ := (1 + cR ^ 2) ^ 2
/-- `16 c^2`. -/
noncomputable def BR : ℝ := 16 * cR ^ 2
/-- `2(c^2-1)`. -/
noncomputable def dR : ℝ := 2 * (cR ^ 2 - 1)
/-- The radicand `R(z) = (1+c^2)^2 (1+z)^2 - 16 c^2 z`. -/
noncomputable def Ra (z : ℂ) : ℂ := ((AR : ℂ) * (1 + z) ^ 2 - (BR : ℂ) * z)
/-- `κ = (8/3)(c^2-1)`. -/
noncomputable def kR : ℝ := (8 / 3) * (cR ^ 2 - 1)
noncomputable def aR : ℝ := 2 * kR * (1 + cR ^ 2)
noncomputable def bR : ℝ := kR ^ 2
noncomputable def c0R : ℝ := 4 * (1 - cR ^ 2) ^ 2
/-- centre of the second circle `C₂`. -/
noncomputable def cenC2 : ℝ := aR / bR
/-- squared radius of `C₂`. -/
noncomputable def rho2sq : ℝ := (aR / bR) ^ 2 - c0R / bR

/-- `psiC z = (3/4) Wfun z` where `W = -(A'(z-1)+√R)/d`. -/
noncomputable def Wfun (z : ℂ) : ℂ :=
  -(((1 + (cR : ℂ) ^ 2) * (z - 1) + Complex.sqrt (Ra z)) / (dR : ℂ))

/-- `Hfun φ = log ‖h((3/4) e^{iφ})‖` for `h = hauptH`, written as an explicit sum. -/
noncomputable def Hfun (φ : ℝ) : ℝ :=
  Real.log 192 + ∑' n : ℕ,
    24 * Real.log ‖1 + ((3 / 4 : ℝ) : ℂ) ^ (n + 1) * Complex.exp (Complex.I * (n + 1 : ℝ) * φ)‖

/-- `Jfun ψ = log ‖h(c₂ + ρ₂ e^{iψ})‖`, `c₂ = a/b`, `ρ₂ = √((a/b)^2 - c0/b)`. -/
noncomputable def Jfun (ψ : ℝ) : ℝ :=
  Real.log 256 + Real.log ‖(cenC2 : ℂ) + (Real.sqrt rho2sq : ℂ) * Complex.exp (Complex.I * ψ)‖ +
    ∑' n : ℕ, 24 * Real.log ‖1 + ((cenC2 : ℂ) + (Real.sqrt rho2sq : ℂ) *
      Complex.exp (Complex.I * ψ)) ^ (n + 1)‖

/-- `γ = 8c²/A - 1 = cos α`. -/
noncomputable def gamR : ℝ := 8 * cR ^ 2 / AR - 1
/-- `α = arccos γ`, the cusp angle on the unit circle. -/
noncomputable def alpR : ℝ := Real.arccos gamR
/-- `P(θ) = √(2A(cos θ - γ))`. -/
noncomputable def PR (θ : ℝ) : ℝ := Real.sqrt (2 * AR * (Real.cos θ - gamR))
/-- `Q(θ) = 2(1+c²) sin(θ/2)`. -/
noncomputable def QR (θ : ℝ) : ℝ := 2 * (1 + cR ^ 2) * Real.sin (θ / 2)
/-- `φ(θ) = θ/2 + π + arctan(Q/P)`, the argument of `Wfun (e^{iθ})` on the `C₁` arc. -/
noncomputable def phiR (θ : ℝ) : ℝ := θ / 2 + Real.pi + Real.arctan (QR θ / PR θ)

/-- The normalised `C₂` parameter: `V(θ) = (ψ_C(e^{iθ}) - c₂)/ρ₂`, a point of the unit circle. -/
noncomputable def Vof (θ : ℝ) : ℂ :=
  ((3 / 4 : ℂ) * Wfun (Complex.exp (Complex.I * θ)) - (cenC2 : ℂ)) / (Real.sqrt rho2sq : ℂ)

/-- `v(x) = (x-1)/(x+1)`, the artanh variable. -/
def avx (x : ℚ) : ℚ := (x - 1) / (x + 1)
/-- Partial sum `2 Σ_{i≤P} v^{2i+1}/(2i+1)` of the artanh series. -/
def asumx (v : ℚ) (P : ℕ) : ℚ := 2 * ∑ i ∈ Finset.range (P + 1), v ^ (2 * i + 1) / (2 * i + 1)
/-- Rational *lower* bound for `Real.log x`. -/
def rlogDn (x : ℚ) (P : ℕ) : ℚ :=
  if 1 ≤ x then asumx (avx x) P
  else -asumx (avx x⁻¹) P - 2 * (avx x⁻¹) ^ (2 * P + 3) / ((2 * P + 3) * (1 - (avx x⁻¹) ^ 2))
/-- Rational *upper* bound for `Real.log x`. -/
def rlogUp (x : ℚ) (P : ℕ) : ℚ :=
  if 1 ≤ x then asumx (avx x) P + 2 * (avx x) ^ (2 * P + 3) / ((2 * P + 3) * (1 - (avx x) ^ 2))
  else -asumx (avx x⁻¹) P

/-- Partial sum `Σ_{i≤P} (-1)^i x^{2i}/(2i)!` of the cosine series. -/
def cosT (x : ℚ) (P : ℕ) : ℚ := ∑ i ∈ Finset.range (P + 1), (-1 : ℚ) ^ i * x ^ (2 * i) / (2 * i).factorial
/-- Partial sum `Σ_{i≤P} (-1)^i x^{2i+1}/(2i+1)!` of the sine series. -/
def sinT (x : ℚ) (P : ℕ) : ℚ := ∑ i ∈ Finset.range (P + 1), (-1 : ℚ) ^ i * x ^ (2 * i + 1) / (2 * i + 1).factorial

end Work.CNum
