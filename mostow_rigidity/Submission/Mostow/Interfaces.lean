import ChallengeDeps

/-!
# Mostow rigidity — driver interfaces (definitions and area `Prop`s only)

Written by the lead. DO NOT EDIT (every area is stated against this file).

## Model
* Hyperbolic space ℍⁿ is modelled on `E n = EuclideanSpace ℝ (Fin n)` through the global chart
  `u ↦ hlift u = (u, √(1+‖u‖²))` onto the upper sheet of the hyperboloid
  `{x : x₁²+…+xₙ² − x_{n+1}² = −1, x_{n+1} > 0}` in `ℝ^{Fin n ⊕ Fin 1}`.
  The matrices of `ChallengeDeps` act on `Fin n ⊕ Fin 1 → ℝ` by `mulVec`; `Sum.inr 0` is the time coordinate.
* Hyperbolic distance: `cosh (hdist u v) = tpart u * tpart v - ⟪u, v⟫`.
* Riemannian metric in the chart: `gH u v = ‖v‖² − ⟪u,v⟫²/(1+‖u‖²)` (quadratic form at `u`, vector `v`).
* Hyperbolic volume: `volH n = (1/√(1+‖u‖²)) · Lebesgue`.
* Boundary sphere: `Sph n = Metric.sphere 0 1 ⊂ E n`; `ξ ∈ Sph n` ↔ null ray `(ξ, 1)`.
  Busemann function (normalised at 0): `busemann ξ u = log (tpart u − ⟪u, ξ⟫)`; it → −∞ as `u → ξ`.
* `PO n 1` acts on `E n` by `g • u = actO (Quotient.out g) u`, where `actO A` applies `sign(A₀₀) · A` to the lift
  (sign chosen so the upper sheet is preserved), and on the sphere by `bd g ξ = bdO (Quotient.out g) ξ`
  (projectivised action on null rays). That these do not depend on the representative is a THEOREM
  (`POActionProp`, from `center = {±1}`).
-/

open LeanEval.Geometry.MostowRigidity MeasureTheory

namespace Submission.Mostow

noncomputable section

/-- the chart space of ℍⁿ -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
/-- O(n,1) as in the challenge -/
abbrev O1 (n : ℕ) := unitary (MatrixSum (Fin n) (Fin 1) ℝ)

variable {n : ℕ}

/-- the underlying matrix of an element of O(n,1) -/
def mat (A : O1 n) : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  MatrixSum.ofMatrix.symm (A : MatrixSum (Fin n) (Fin 1) ℝ)

/-- time coordinate of the hyperboloid point over `u` -/
def tpart (u : E n) : ℝ := √(1 + ‖u‖ ^ 2)

/-- the hyperboloid point over `u` -/
def hlift (u : E n) : Fin n ⊕ Fin 1 → ℝ := Sum.elim (fun i => u i) (fun _ => tpart u)

/-- `+1` if `A` preserves the upper sheet, `−1` if it swaps the sheets -/
def tsign (A : O1 n) : ℝ := if 0 < mat A (Sum.inr 0) (Sum.inr 0) then 1 else -1

/-- action of a matrix representative on the chart -/
def actO (A : O1 n) (u : E n) : E n :=
  WithLp.toLp 2 (fun i => tsign A * (Matrix.mulVec (mat A) (hlift u)) (Sum.inl i))

/-- boundary action of a matrix representative: `ξ ↦` the null ray of `A (ξ,1)`, renormalised -/
def bdO (A : O1 n) (ξ : E n) : E n :=
  let w := Matrix.mulVec (mat A) <| Sum.elim (fun i => ξ i) (fun _ => (1 : ℝ))
  WithLp.toLp 2 (fun i => w (Sum.inl i) / w (Sum.inr 0))

/-- a fixed representative -/
def rep (g : PO n 1) : O1 n := Quotient.out g

instance instSMulPO : SMul (PO n 1) (E n) := ⟨fun g u => actO (rep g) u⟩

/-- boundary action of `PO n 1` (meaningful on `Sph n`) -/
def bd (g : PO n 1) (ξ : E n) : E n := bdO (rep g) ξ

/-- the boundary sphere -/
def Sph (n : ℕ) : Set (E n) := Metric.sphere (0 : E n) 1

/-- hyperbolic distance -/
def hdist (u v : E n) : ℝ := Real.arcosh (tpart u * tpart v - inner ℝ u v)

/-- hyperbolic Riemannian quadratic form at `u` -/
def gH (u v : E n) : ℝ := ‖v‖ ^ 2 - (inner ℝ u v) ^ 2 / (1 + ‖u‖ ^ 2)

/-- hyperbolic volume -/
def volH (n : ℕ) : Measure (E n) :=
  (volume : Measure (E n)).withDensity (fun u => ENNReal.ofReal (tpart u)⁻¹)

/-- Jacobian of `F` with respect to hyperbolic volume -/
def hjac (F : E n → E n) (u : E n) : ℝ := |(fderiv ℝ F u).det| * (tpart u / tpart (F u))

/-- Busemann function of `ξ ∈ Sph n`, normalised by `busemann ξ 0 = 0` -/
def busemann (ξ u : E n) : ℝ := Real.log (tpart u - inner ℝ u ξ)

/-- open horoball at `ξ` of level `t` -/
def horoball (ξ : E n) (t : ℝ) : Set (E n) := {u | busemann ξ u < t}

/-- normalised rotation-invariant probability measure on `Sph n` (as a measure on `E n`) -/
def sigma (n : ℕ) : Measure (E n) :=
  let m : Measure (E n) := ((volume : Measure (E n)).toSphere).map Subtype.val
  (m Set.univ)⁻¹ • m

/-- visual (Poisson) measure seen from `u`: density `exp (-(n-1) busemann ξ u)` w.r.t. `sigma n` -/
def visual (n : ℕ) (u : E n) : Measure (E n) :=
  (sigma n).withDensity (fun ξ => ENNReal.ofReal (Real.exp (-((n : ℝ) - 1) * busemann ξ u)))

/-- the barycentre functional of a measure on the sphere -/
def baryFun (ν : Measure (E n)) (y : E n) : ℝ := ∫ ξ, busemann ξ y ∂ν

open Classical in
/-- the barycentre: a minimiser of `baryFun ν` (junk `0` if none) -/
def bar (ν : Measure (E n)) : E n :=
  if h : ∃ y, ∀ z, baryFun ν y ≤ baryFun ν z then h.choose else 0

/-- the Besson–Courtois–Gallot natural map of a boundary map `φ` -/
def natMap (φ : E n → E n) (u : E n) : E n := bar ((visual n u).map φ)

/-- a lattice, geometrically: discrete, with a fundamental domain of finite hyperbolic volume -/
def HypLattice (Γ : Subgroup (PO n 1)) : Prop :=
  IsDiscrete (SetLike.coe Γ) ∧
    ∃ D : Set (E n), IsFundamentalDomain Γ D (volH n) ∧ volH n D ≠ ⊤

/-- quasi-isometry of ℍⁿ (coarsely surjective) -/
def IsQI (Φ : E n → E n) : Prop :=
  ∃ K C : ℝ, 1 ≤ K ∧ 0 ≤ C ∧ (∀ u v, hdist (Φ u) (Φ v) ≤ K * hdist u v + C) ∧
    (∀ u v, hdist u v ≤ K * hdist (Φ u) (Φ v) + C) ∧ ∀ w, ∃ u, hdist (Φ u) w ≤ C

/-- parabolic isometry: no fixed point in ℍⁿ, infimal displacement 0 -/
def IsParabolic (g : PO n 1) : Prop :=
  (∀ u : E n, g • u ≠ u) ∧ ∀ ε > 0, ∃ u : E n, hdist u (g • u) < ε

/-! ## Area Props -/

/-- T1: the group side. -/
def POActionProp (n : ℕ) : Prop :=
  (∀ A : O1 n, A ∈ Subgroup.center (O1 n) ↔ A = 1 ∨ A = -1) ∧
  (∀ (A : O1 n) (u : E n), (A : PO n 1) • u = actO A u) ∧
  (∀ (A : O1 n) (ξ : E n), ξ ∈ Sph n → bd (A : PO n 1) ξ = bdO A ξ) ∧
  (∀ u : E n, (1 : PO n 1) • u = u) ∧
  (∀ (g h : PO n 1) (u : E n), (g * h) • u = g • (h • u)) ∧
  (∀ g : PO n 1, (∀ u : E n, g • u = u) → g = 1) ∧
  Continuous (fun p : PO n 1 × E n => p.1 • p.2) ∧
  (∀ (g : PO n 1) (ξ : E n), ξ ∈ Sph n → bd g ξ ∈ Sph n) ∧
  (∀ ξ ∈ Sph n, bd (1 : PO n 1) ξ = ξ) ∧
  (∀ (g h : PO n 1) (ξ : E n), ξ ∈ Sph n → bd (g * h) ξ = bd g (bd h ξ)) ∧
  (∀ g : PO n 1, ContinuousOn (bd g) (Sph n)) ∧
  (∀ g : PO n 1, Measurable (bd g))

/-- T2: hyperbolic geometry toolkit. -/
def HypIsometryProp (n : ℕ) : Prop :=
  (∀ u v : E n, 0 ≤ hdist u v) ∧ (∀ u v : E n, hdist u v = hdist v u) ∧
  (∀ u v : E n, hdist u v = 0 ↔ u = v) ∧
  (∀ u v w : E n, hdist u w ≤ hdist u v + hdist v w) ∧
  Continuous (fun p : E n × E n => hdist p.1 p.2) ∧
  (∀ (u : E n) (r : ℝ), IsCompact {v | hdist u v ≤ r}) ∧
  (∀ (g : PO n 1) (u v : E n), hdist (g • u) (g • v) = hdist u v) ∧
  (∀ F : E n → E n, (∀ u v, hdist (F u) (F v) = hdist u v) → ∃ g : PO n 1, ∀ u, F u = g • u) ∧
  (∀ g : PO n 1, ContDiff ℝ 1 (fun u : E n => g • u)) ∧
  (∀ (g : PO n 1) (u v : E n), gH (g • u) (fderiv ℝ (fun w : E n => g • w) u v) = gH u v) ∧
  (∀ (g : PO n 1) (u : E n), hjac (fun w : E n => g • w) u = 1) ∧
  (∀ g : PO n 1, MeasurePreserving (fun u : E n => g • u) (volH n) (volH n)) ∧
  (∀ (g : PO n 1) (ξ u : E n), ξ ∈ Sph n →
      busemann (bd g ξ) (g • u) = busemann ξ u + busemann (bd g ξ) (g • (0 : E n)))

/-- T3: visual measures. -/
def VisualProp (n : ℕ) : Prop :=
  ∀ u : E n, IsProbabilityMeasure (visual n u) ∧ visual n u (Sph n)ᶜ = 0 ∧
    (∀ ξ, visual n u {ξ} = 0) ∧
    (∀ U : Set (E n), IsOpen U → (U ∩ Sph n).Nonempty → 0 < visual n u U) ∧
    ∀ g : PO n 1, (visual n u).map (bd g) = visual n (g • u)

/-- T4: barycentre of an atomless probability measure on the sphere. -/
def BaryProp (n : ℕ) : Prop :=
  ∀ ν : Measure (E n), IsProbabilityMeasure ν → ν (Sph n)ᶜ = 0 → (∀ ξ, ν {ξ} = 0) →
    (∀ z, baryFun ν (bar ν) ≤ baryFun ν z) ∧
    (∀ y, (∀ z, baryFun ν y ≤ baryFun ν z) → y = bar ν) ∧
    ∀ g : PO n 1, bar (ν.map (bd g)) = g • bar ν

/-- B: the Haar-to-hyperbolic-volume bridge (only the direction needed). -/
def BridgeProp (n : ℕ) : Prop :=
  ∀ Γ : Subgroup (PO n 1), IsDiscrete (SetLike.coe Γ) → HasFundamentalDomain Γ (PO n 1) →
    covolume Γ (PO n 1) ≠ ⊤ → HypLattice Γ

/-- N1: equivariance of the natural map. -/
def NatMapEquivProp (n : ℕ) : Prop :=
  ∀ φ : E n → E n, Set.BijOn φ (Sph n) (Sph n) → ContinuousOn φ (Sph n) →
    ∀ g h : PO n 1, (∀ ξ ∈ Sph n, φ (bd g ξ) = bd h (φ ξ)) →
      ∀ u : E n, natMap φ (g • u) = h • natMap φ u

/-- N2: the BCG Jacobian inequality and its equality case (n ≥ 3 is used here). -/
def NatMapJacProp (n : ℕ) : Prop :=
  ∀ φ : E n → E n, Set.BijOn φ (Sph n) (Sph n) → ContinuousOn φ (Sph n) →
    ContDiff ℝ 1 (natMap φ) ∧ (∀ u, hjac (natMap φ) u ≤ 1) ∧
    ∀ u, hjac (natMap φ) u = 1 → ∀ v, gH (natMap φ u) (fderiv ℝ (natMap φ) u v) = gH u v

/-- N3: the natural map of a boundary homeomorphism is onto. -/
def NatMapSurjProp (n : ℕ) : Prop :=
  ∀ φ : E n → E n, Set.BijOn φ (Sph n) (Sph n) → ContinuousOn φ (Sph n) →
    Function.Surjective (natMap φ)

/-- V: volume squeeze and its equality case. -/
def VolumeProp (n : ℕ) : Prop :=
  ∀ (Γ Λ : Subgroup (PO n 1)), HypLattice Γ → HypLattice Λ →
    ∀ (f : Γ →* Λ) (F : E n → E n), ContDiff ℝ 1 F → Function.Surjective F →
      (∀ (γ : Γ) (u : E n), F (γ • u) = (f γ : PO n 1) • F u) → (∀ u, hjac F u ≤ 1) →
      ∀ DΓ DΛ : Set (E n), IsFundamentalDomain Γ DΓ (volH n) → IsFundamentalDomain Λ DΛ (volH n) →
        volH n DΛ ≤ volH n DΓ ∧ (volH n DΓ ≤ volH n DΛ → ∀ u, hjac F u = 1)

/-- L: a C¹ map with isometric differential is an isometry of ℍⁿ. -/
def LocalIsomProp (n : ℕ) : Prop :=
  ∀ F : E n → E n, ContDiff ℝ 1 F → (∀ u v, gH (F u) (fderiv ℝ F u v) = gH u v) →
    ∀ u v, hdist (F u) (F v) = hdist u v

/-- C1: a lattice is geometrically finite: invariant disjoint cusp horoballs, cocompact complement,
cusp stabilisers cocompact on the horospheres, cusps = parabolic fixed points. -/
def GeomFiniteProp (n : ℕ) : Prop :=
  ∀ Γ : Subgroup (PO n 1), HypLattice Γ →
    ∃ (P : Set (E n)) (ht : E n → ℝ), P ⊆ Sph n ∧
      (∀ (γ : Γ), ∀ ξ ∈ P, bd γ ξ ∈ P) ∧
      (∀ (γ : Γ), ∀ ξ ∈ P, ∀ u : E n,
          γ • u ∈ horoball (bd γ ξ) (ht (bd γ ξ)) ↔ u ∈ horoball ξ (ht ξ)) ∧
      P.Pairwise (fun ξ η => Disjoint (horoball ξ (ht ξ)) (horoball η (ht η))) ∧
      (∃ K : Set (E n), IsCompact K ∧
          ∀ u : E n, (∀ ξ ∈ P, u ∉ horoball ξ (ht ξ)) → ∃ γ : Γ, γ • u ∈ K) ∧
      (∀ ξ ∈ P, ∃ K : Set (E n), IsCompact K ∧
          ∀ u : E n, busemann ξ u = ht ξ → ∃ γ : Γ, bd γ ξ = ξ ∧ γ • u ∈ K) ∧
      (∀ ξ ∈ P, ∃ γ : Γ, IsParabolic (γ : PO n 1) ∧ bd γ ξ = ξ) ∧
      (∀ γ : Γ, IsParabolic (γ : PO n 1) → ∃ ξ ∈ P, bd γ ξ = ξ)

/-- C2: Prasad's cusp recognition: an abstract isomorphism of lattices preserves parabolicity. -/
def CuspRecognitionProp (n : ℕ) : Prop :=
  ∀ (Γ Λ : Subgroup (PO n 1)), HypLattice Γ → HypLattice Λ → ∀ (f : Γ ≃* Λ) (γ : Γ),
    IsParabolic (γ : PO n 1) → IsParabolic (f γ : PO n 1)

/-- C3: a coarsely equivariant quasi-isometry between lattices' spaces. -/
def QIProp (n : ℕ) : Prop :=
  ∀ (Γ Λ : Subgroup (PO n 1)), HypLattice Γ → HypLattice Λ → ∀ f : Γ ≃* Λ,
    ∃ Φ : E n → E n, IsQI Φ ∧
      ∀ γ : Γ, ∃ C : ℝ, ∀ u : E n, hdist (Φ (γ • u)) ((f γ : PO n 1) • Φ u) ≤ C

/-- C4: boundary extension of a quasi-isometry (Morse lemma), with equivariance. -/
def BoundaryExtProp (n : ℕ) : Prop :=
  ∀ Φ : E n → E n, IsQI Φ →
    ∃ φ : E n → E n, Set.BijOn φ (Sph n) (Sph n) ∧ ContinuousOn φ (Sph n) ∧
      ∀ g h : PO n 1, (∃ C : ℝ, ∀ u : E n, hdist (Φ (g • u)) (h • Φ u) ≤ C) →
        ∀ ξ ∈ Sph n, φ (bd g ξ) = bd h (φ ξ)

/-- Bb: Bieberbach's first theorem (in the form needed): a group acting properly discontinuously and
cocompactly by isometries on Euclidean `m`-space has a finite-index subgroup acting by translations
whose translation vectors span. -/
def BieberbachProp (m : ℕ) : Prop :=
  ∀ (G : Type) [Group G] (ρ : G →* (E m ≃ᵢ E m)),
    (∀ K : Set (E m), IsCompact K → {g : G | ((ρ g) '' K ∩ K).Nonempty}.Finite) →
    (∃ K : Set (E m), IsCompact K ∧ ∀ x : E m, ∃ g : G, ρ g x ∈ K) →
    ∃ (T : Subgroup G) (v : G → E m), T.FiniteIndex ∧ (∀ t ∈ T, ∀ x : E m, ρ t x = x + v t) ∧
      Submodule.span ℝ (v '' (T : Set G)) = ⊤

end

end Submission.Mostow
