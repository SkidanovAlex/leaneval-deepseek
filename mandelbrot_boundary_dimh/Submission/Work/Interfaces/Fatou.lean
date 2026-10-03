import Mathlib

/-!
# FATOU area contract (lead). Shishikura Prop A.2.1, Lemma A.2.3, Lemma A.2.4. Design: NOTES_LEAD_fatou.md.
-/

open Set Filter Metric Complex
open scoped Topology Manifold

namespace MandelDim

noncomputable section

/-! ## FATOU area: interface (Shishikura, Prop. A.2.1, Lemma A.2.3, Lemma A.2.4). -/

/-- Shishikura's region `𝒬(b₁,b₂)`; `none` stands for `b₁ = -∞` resp. `b₂ = +∞`. -/
def Qreg (b₁ b₂ : Option ℂ) : Set ℂ :=
  {z | (∀ b ∈ b₁, -|(z - b).im| < (z - b).re) ∧ (∀ b ∈ b₂, (z - b).re < |(z - b).im|)}

/-- Admissible pair of vertices: `Re b₂ > Re b₁ + 4` when both are finite. -/
def QAdm (b₁ b₂ : Option ℂ) : Prop := ∀ a ∈ b₁, ∀ b ∈ b₂, a.re + 4 < b.re

/-- `F` is a near-translation on `Q` (A.2.2, with the constant `1/32` instead of `1/4`). -/
def NearTranslationOn (F : ℂ → ℂ) (Q : Set ℂ) : Prop :=
  DifferentiableOn ℂ F Q ∧ ∀ z ∈ Q, ‖F z - (z + 1)‖ ≤ 1 / 32 ∧ ‖deriv F z - 1‖ ≤ 1 / 32

/-- A (univalent) Fatou coordinate of `F` on `Q`. -/
def IsFatouCoordOn (F Φ : ℂ → ℂ) (Q : Set ℂ) : Prop :=
  DifferentiableOn ℂ Φ Q ∧ Set.InjOn Φ Q ∧ ∀ z ∈ Q, F z ∈ Q → Φ (F z) = Φ z + 1

/-- A.2.1(ii) existence + A.2.3 (the cylinder is `ℂ/ℤ`: every class mod `ℤ` is hit). -/
def FatouExists : Prop :=
  ∀ (b₁ b₂ : Option ℂ) (F : ℂ → ℂ), QAdm b₁ b₂ → NearTranslationOn F (Qreg b₁ b₂) →
    ∃ Φ : ℂ → ℂ, IsFatouCoordOn F Φ (Qreg b₁ b₂) ∧
      ∀ w : ℂ, ∃ z ∈ Qreg b₁ b₂, ∃ n : ℤ, Φ z = w + n

/-- A.2.1(i)/A.2.3 orbit relation: equal Fatou values mod `ℕ` means same orbit inside `Q`. -/
def FatouOrbit : Prop :=
  ∀ (b₁ b₂ : Option ℂ) (F Φ : ℂ → ℂ), QAdm b₁ b₂ → NearTranslationOn F (Qreg b₁ b₂) →
    IsFatouCoordOn F Φ (Qreg b₁ b₂) →
    ∀ z ∈ Qreg b₁ b₂, ∀ z' ∈ Qreg b₁ b₂, ∀ k : ℕ, Φ z' = Φ z + k →
      (∀ j ≤ k, F^[j] z ∈ Qreg b₁ b₂) ∧ F^[k] z = z'

/-- A.2.1(ii) uniqueness up to an additive constant. -/
def FatouUnique : Prop :=
  ∀ (b₁ b₂ : Option ℂ) (F Φ₁ Φ₂ : ℂ → ℂ), QAdm b₁ b₂ → NearTranslationOn F (Qreg b₁ b₂) →
    IsFatouCoordOn F Φ₁ (Qreg b₁ b₂) → IsFatouCoordOn F Φ₂ (Qreg b₁ b₂) →
    ∃ c : ℂ, ∀ z ∈ Qreg b₁ b₂, Φ₂ z = Φ₁ z + c

/-- A.2.1(iii) continuity, in the form the perturbation layer uses: the domains may move
(`𝒬_f^± → 𝒬_0^±`), every compact subset of the limit domain is eventually inside the moving
domains, and the maps converge uniformly on it. -/
def FatouContinuity : Prop :=
  ∀ (b₁ b₂ : ℕ → Option ℂ) (c₁ c₂ : Option ℂ) (F : ℕ → ℂ → ℂ) (F₀ : ℂ → ℂ)
    (Φ : ℕ → ℂ → ℂ) (Φ₀ : ℂ → ℂ) (z₀ : ℂ),
    (∀ n, QAdm (b₁ n) (b₂ n)) → QAdm c₁ c₂ →
    (∀ n, NearTranslationOn (F n) (Qreg (b₁ n) (b₂ n))) → NearTranslationOn F₀ (Qreg c₁ c₂) →
    (∀ K ⊆ Qreg c₁ c₂, IsCompact K →
      (∀ᶠ n in atTop, K ⊆ Qreg (b₁ n) (b₂ n)) ∧ TendstoUniformlyOn F F₀ atTop K) →
    (∀ n, IsFatouCoordOn (F n) (Φ n) (Qreg (b₁ n) (b₂ n))) → IsFatouCoordOn F₀ Φ₀ (Qreg c₁ c₂) →
    z₀ ∈ Qreg c₁ c₂ → (∀ᶠ n in atTop, Φ n z₀ = Φ₀ z₀) →
    ∀ K ⊆ Qreg c₁ c₂, IsCompact K → TendstoUniformlyOn Φ Φ₀ atTop K

/-- Lemma A.2.4(i): `Φ' ≈ 1/v` deep inside the domain (universal constants). -/
def FatouDerivEstimate : Prop :=
  ∃ R₁ C₁ C₂ : ℝ, 0 < R₁ ∧ 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (Φ v : ℂ → ℂ) (z₀ : ℂ) (R : ℝ), R₁ ≤ R →
      DifferentiableOn ℂ Φ (ball z₀ R) → Set.InjOn Φ (ball z₀ R) →
      DifferentiableOn ℂ v (ball z₀ R) → (∀ z ∈ ball z₀ R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ ball z₀ R, z + v z ∈ ball z₀ R → Φ (z + v z) = Φ z + 1) →
      ‖deriv Φ z₀ - 1 / v z₀‖ ≤ C₁ * (1 / R ^ 2 + ‖deriv v z₀‖) ∧
      ‖deriv Φ z₀ - 1 / v z₀‖ ≤ C₂ / R

/-- The two ends of the cylinder: if `F` is exponentially close to the translation by `ρ` high
up (resp. low down) in `Q`, the Fatou coordinate is `z/ρ + c + o(1)` there, uniformly on
vertical strips of width 4.  (Gives the extension of horn/return maps to `0` and `∞`.) -/
def FatouEnds : Prop :=
  ∀ (b₁ b₂ : Option ℂ) (F Φ : ℂ → ℂ) (ρ : ℂ) (M κ Y : ℝ), QAdm b₁ b₂ →
    NearTranslationOn F (Qreg b₁ b₂) → IsFatouCoordOn F Φ (Qreg b₁ b₂) →
    0 < κ → ‖ρ - 1‖ ≤ 1 / 32 →
    ((∀ z ∈ Qreg b₁ b₂, Y < z.im → ‖F z - (z + ρ)‖ ≤ M * Real.exp (-(κ * z.im))) →
      ∃ c : ℂ, ∀ x : ℝ, ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Qreg b₁ b₂, Y' < z.im → |z.re - x| ≤ 2 →
        ‖Φ z - z / ρ - c‖ < ε) ∧
    ((∀ z ∈ Qreg b₁ b₂, z.im < -Y → ‖F z - (z + ρ)‖ ≤ M * Real.exp (κ * z.im)) →
      ∃ c : ℂ, ∀ x : ℝ, ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Qreg b₁ b₂, z.im < -Y' → |z.re - x| ≤ 2 →
        ‖Φ z - z / ρ - c‖ < ε)

/-- THE FATOU AREA CONTRACT. -/
def FatouStatement : Prop :=
  FatouExists ∧ FatouOrbit ∧ FatouUnique ∧ FatouContinuity ∧ FatouDerivEstimate ∧ FatouEnds

/-! ## Optional: Lemma A.2.4(ii) (sector asymptotics). Not consumed by the planned PERT route. -/

/-- Open sector with vertex `ω` and directions `θ ∈ (θ₁, θ₂)`. -/
def sectorAt (ω : ℂ) (θ₁ θ₂ : ℝ) : Set ℂ :=
  {z | ∃ r : ℝ, 0 < r ∧ ∃ θ ∈ Ioo θ₁ θ₂, z = ω + r * exp (θ * I)}

def FatouSectorAsymptotic : Prop :=
  ∀ (Φ v : ℂ → ℂ) (ω : ℂ) (θ₁ θ₂ θ₁' θ₂' C ν : ℝ) (z₀ : ℂ),
    θ₁ < θ₁' → θ₁' < θ₂' → θ₂' < θ₂ → θ₂ - θ₁ ≤ Real.pi → 0 < ν → 0 ≤ C →
    DifferentiableOn ℂ Φ (sectorAt ω θ₁ θ₂) → Set.InjOn Φ (sectorAt ω θ₁ θ₂) →
    DifferentiableOn ℂ v (sectorAt ω θ₁ θ₂) →
    (∀ z ∈ sectorAt ω θ₁ θ₂, ‖v z - 1‖ < 1 / 4) →
    (∀ z ∈ sectorAt ω θ₁ θ₂, ‖deriv v z‖ ≤ C / ‖z - ω‖ ^ (1 + ν)) →
    (∀ z ∈ sectorAt ω θ₁ θ₂, z + v z ∈ sectorAt ω θ₁ θ₂ → Φ (z + v z) = Φ z + 1) →
    z₀ ∈ sectorAt ω θ₁ θ₂ →
    ∃ R₂ C₃ : ℝ, ∃ ξ : ℂ, 0 < R₂ ∧ 0 ≤ C₃ ∧ ∀ z ∈ sectorAt ω θ₁' θ₂', R₂ ≤ ‖z - ω‖ →
      ‖Φ z - (∫ t in (0 : ℝ)..1, (z - z₀) / v (z₀ + t * (z - z₀))) - ξ‖ ≤
        C₃ * (1 / ‖z - ω‖ + C / ‖z - ω‖ ^ ν)

/-! ## Named internal lemmas of the chosen route (statements) -/

/-- Wirtinger derivatives of a real-differentiable map `ℂ → ℂ`. -/
def dz (g : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ g z 1 - I * fderiv ℝ g z I) / 2
def dzbar (g : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ g z 1 + I * fderiv ℝ g z I) / 2

/-- FX-LA: a bounded injective `C¹` quasiconformal map of the whole plane does not exist
(length–area).  Used to exclude the upper half-plane case of uniformization. -/
def QCLiouville : Prop :=
  ∀ (g : ℂ → ℂ) (k M : ℝ), k < 1 → ContDiff ℝ 1 g → Function.Injective g →
    (∀ z, dz g z ≠ 0) → (∀ z, ‖dzbar g z‖ ≤ k * ‖dz g z‖) → (∀ z, ‖g z‖ ≤ M) → False

/-- FX-AFF: an injective entire map without fixed points is a nonzero translation. -/
def InjEntireTranslation : Prop :=
  ∀ A : ℂ → ℂ, Differentiable ℂ A → Function.Injective A → (∀ w, A w ≠ w) →
    ∃ b : ℂ, b ≠ 0 ∧ ∀ w, A w = w + b

/-- FX-IFT: `F` is univalent on `𝒬` (A.2.1(0)). -/
def FatouInjOnQ : Prop :=
  ∀ (b₁ b₂ : Option ℂ) (F : ℂ → ℂ), QAdm b₁ b₂ → NearTranslationOn F (Qreg b₁ b₂) →
    Set.InjOn F (Qreg b₁ b₂)

/-- FX-FUND (A.2.1(i)): with `x₀` a vertical line inside `𝒬`, every point of `𝒬` has exactly
one orbit point in `S∖F(ℓ) = {z ∈ 𝒬 | x₀ ≤ Re z, every F-preimage in 𝒬 has Re < x₀}`. -/
def fundStrip (F : ℂ → ℂ) (Q : Set ℂ) (x₀ : ℝ) : Set ℂ :=
  {z | z ∈ Q ∧ x₀ ≤ z.re ∧ ∀ w ∈ Q, F w = z → w.re < x₀}

def FatouFundamental : Prop :=
  ∀ (b₁ b₂ : Option ℂ) (F : ℂ → ℂ) (x₀ : ℝ), QAdm b₁ b₂ → NearTranslationOn F (Qreg b₁ b₂) →
    (∀ a ∈ b₁, a.re + 1 < x₀) → (∀ b ∈ b₂, x₀ + 3 < b.re) →
    ∀ z ∈ Qreg b₁ b₂, ∃ k : ℕ, ∃ s ∈ fundStrip F (Qreg b₁ b₂) x₀,
      ((∀ j ≤ k, F^[j] z ∈ Qreg b₁ b₂) ∧ F^[k] z = s) ∨
      ((∀ j ≤ k, F^[j] s ∈ Qreg b₁ b₂) ∧ F^[k] s = z)

open scoped ContDiff in
/-- The uniformization theorem for (noncompact, simply connected in the weak sense) Riemann surfaces,
as an explicit HYPOTHESIS for the uniformization route of FATOU (the route `Work.Fatou.fatouU`).
It is the statement of `Submission.uniformization` of our uniformization library (whose axiom
cleanliness is being checked separately); the route must not depend on anything else from it. -/
def UniformizationHyp : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X], ¬ CompactSpace X →
    ∀ x : X, Subsingleton (Additive (FundamentalGroup X x) →+ ℝ) →
      Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) ∨
      Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane)

end

end MandelDim
