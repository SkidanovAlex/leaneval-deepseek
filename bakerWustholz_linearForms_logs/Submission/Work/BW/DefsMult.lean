import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! Definitions for the multiplicity block (P86* route). Install next to `Defs.lean` as
`Submission/Work/BW/DefsMult.lean`, wrapped in `namespace Work.BW` and importing
`Submission.Work.BW.Defs`. Notation: `G = G_a × G_m^N ⊂ (P¹)^{N+1}`; affine coordinates
`Y₀,…,Y_N` (variable `0` is `Y₀`, variable `i.succ` is `Y_{i+1}`); homogeneous coordinates
`X_{i0}, X_{i1}` with `Y_i = X_{i1}/X_{i0}`. -/

/-- Homogeneous coordinate ring of `(P¹)^{N+1}`: variable `(i, 0)` is `X_{i0}`, `(i, 1)` is `X_{i1}`. -/
abbrev MR (N : ℕ) := MvPolynomial (Fin (N + 1) × Fin 2) ℂ

/-- Multidegree weight: both variables of the `i`-th factor have weight `e_i`. -/
noncomputable def mdeg (N : ℕ) : Fin (N + 1) × Fin 2 → (Fin (N + 1) →₀ ℕ) :=
  fun v => Finsupp.single v.1 1

/-- Multihomogeneous polynomials of multidegree exactly `d`. -/
noncomputable def homPiece (N : ℕ) (d : Fin (N + 1) →₀ ℕ) : Submodule ℂ (MR N) :=
  MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N) d

/-- A multihomogeneous ideal: stable under taking multihomogeneous components. -/
def MultiHom (N : ℕ) (I : Ideal (MR N)) : Prop :=
  ∀ p ∈ I, ∀ d, MvPolynomial.weightedHomogeneousComponent (mdeg N) d p ∈ I

/-- Ray Hilbert function `t ↦ dim_ℂ (R/I)_{tD}` (Hilbert function of the Segre–Veronese
section by `O(D)`). -/
noncomputable def rayHilb (N : ℕ) (D : Fin (N + 1) →₀ ℕ) (I : Ideal (MR N)) (t : ℕ) : ℕ :=
  Module.finrank ℂ ((homPiece N (t • D)) ⧸
    Submodule.comap (homPiece N (t • D)).subtype (I.restrictScalars ℂ))

/-- `q` agrees with the ray Hilbert function for all large `t`. -/
def IsRayPoly (N : ℕ) (D : Fin (N + 1) →₀ ℕ) (I : Ideal (MR N)) (q : Polynomial ℚ) : Prop :=
  ∀ᶠ t in Filter.atTop, ((rayHilb N D I t : ℕ) : ℚ) = q.eval (t : ℚ)

/-- The ray Hilbert polynomial (junk value `0` if none exists). -/
noncomputable def rayPoly (N : ℕ) (D : Fin (N + 1) →₀ ℕ) (I : Ideal (MR N)) : Polynomial ℚ :=
  open Classical in
  if h : ∃ q, IsRayPoly N D I q then Classical.choose h else 0

/-- Dimension of `Z(I) ⊂ (P¹)^{N+1}` read off the ray Hilbert polynomial. -/
noncomputable def rayDim (N : ℕ) (D : Fin (N + 1) →₀ ℕ) (I : Ideal (MR N)) : ℕ :=
  (rayPoly N D I).natDegree

/-- Philippon's `H(I; D)`: `(dim)!` times the leading coefficient of the ray Hilbert
polynomial (the degree of `Z(I)` in the embedding by `O(D)`). -/
noncomputable def rayDeg (N : ℕ) (D : Fin (N + 1) →₀ ℕ) (I : Ideal (MR N)) : ℚ :=
  ((rayPoly N D I).natDegree.factorial : ℚ) * (rayPoly N D I).leadingCoeff

/-- Length of `(R/I)_p` (the multiplicity of the primary component of `I` at `p`); `0` if
`p` is not prime. -/
noncomputable def primLen {R : Type*} [CommRing R] (I p : Ideal R) : ℕ∞ :=
  open Classical in
  if h : p.IsPrime then
    haveI := h
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p)))
  else 0

/-- `x` lies on the affine cone over `G`: `X_{00} ≠ 0` and `X_{i0} X_{i1} ≠ 0` for `i ≥ 1`. -/
def OnG (N : ℕ) (x : Fin (N + 1) × Fin 2 → ℂ) : Prop :=
  x (0, 0) ≠ 0 ∧ ∀ i : Fin N, x (i.succ, 0) ≠ 0 ∧ x (i.succ, 1) ≠ 0

/-- The maximal ideal of the cone point `x`. -/
noncomputable def ptIdeal (N : ℕ) (x : Fin (N + 1) × Fin 2 → ℂ) : Ideal (MR N) :=
  RingHom.ker (MvPolynomial.eval x)

/-- Cone point over the affine point `y`: `X_{i0} = 1`, `X_{i1} = y_i`. -/
def conePt (N : ℕ) (y : Fin (N + 1) → ℂ) : Fin (N + 1) × Fin 2 → ℂ :=
  fun v => if v.2 = 0 then 1 else y v.1

/-- `y ∈ G' = G_a^ε × ker 𝒵`, where the rows of `M` span `𝒵 ⊂ ℤ^N`
(`ε = true`: the `G_a` factor is included; `ε = false`: `y₀ = 0`). -/
def InSub (N ρ : ℕ) (ε : Bool) (M : Fin ρ → Fin N → ℤ) (y : Fin (N + 1) → ℂ) : Prop :=
  (ε = false → y 0 = 0) ∧ (∀ i : Fin N, y i.succ ≠ 0) ∧
    ∀ j, ∏ i, (y i.succ) ^ (M j i) = 1

/-- Multihomogeneous ideal of the closure of `G' = G_a^ε × ker 𝒵` in `(P¹)^{N+1}`. -/
noncomputable def subIdeal (N ρ : ℕ) (ε : Bool) (M : Fin ρ → Fin N → ℤ) : Ideal (MR N) :=
  Ideal.span {F | (∃ d, F ∈ homPiece N d) ∧
    ∀ y, InSub N ρ ε M y → MvPolynomial.eval (conePt N y) F = 0}

/-- The `ρ × ρ` minor `Δ_J` of `M` on the columns `J` (in increasing order). -/
noncomputable def minorJ {ρ N : ℕ} (M : Fin ρ → Fin N → ℤ) (J : Finset (Fin N))
    (hJ : J.card = ρ) : ℤ :=
  Matrix.det (fun a b : Fin ρ => M a (J.orderEmbOfFin hJ b))

/-- Lie algebra of `G' = G_a^ε × ker 𝒵` inside `Lie G = ℂ^{1+N}` (coordinate `0` = `G_a`). -/
noncomputable def lieSub (N ρ : ℕ) (ε : Bool) (M : Fin ρ → Fin N → ℤ) :
    Submodule ℂ (Fin (N + 1) → ℂ) :=
  (if ε then ⊤ else LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun _ : Fin (N + 1) => ℂ) 0)) ⊓
    ⨅ j : Fin ρ, LinearMap.ker
      (∑ i : Fin N, ((M j i : ℂ)) • LinearMap.proj (R := ℂ) (φ := fun _ : Fin (N + 1) => ℂ) i.succ)

/-- The invariant derivation of `G = G_a × G_m^N` with Lie vector `v`:
`v₀ ∂/∂Y₀ + ∑ᵢ v_{i+1} Y_{i+1} ∂/∂Y_{i+1}`. -/
noncomputable def derC {N : ℕ} (v : Fin (N + 1) → ℂ) (P : MvPolynomial (Fin (N + 1)) ℂ) :
    MvPolynomial (Fin (N + 1)) ℂ :=
  MvPolynomial.C (v 0) * MvPolynomial.pderiv 0 P +
    ∑ i : Fin N, MvPolynomial.C (v i.succ) * MvPolynomial.X i.succ *
      MvPolynomial.pderiv i.succ P

/-- `∏_m (derC (w m))^{t m}` applied to `P`. -/
noncomputable def applyW {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (t : Fin q → ℕ)
    (P : MvPolynomial (Fin (N + 1)) ℂ) : MvPolynomial (Fin (N + 1)) ℂ :=
  (List.finRange q).foldr (fun m Q => (derC (w m))^[t m] Q) P

/-- The point `s·γ = (s, θ^s)` of `G = G_a × G_m^N`. -/
noncomputable def ptTheta {N : ℕ} (θ : Fin N → ℂ) (s : ℕ) : Fin (N + 1) → ℂ :=
  Fin.cons (s : ℂ) (fun i => θ i ^ s)

/-- Number of classes of `{0·γ, …, S·γ}` modulo `G' = G_a^ε × ker 𝒵`. -/
noncomputable def cardMod {N ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ) (θ : Fin N → ℂ)
    (S : ℕ) : ℕ :=
  open Classical in
  ((Finset.range (S + 1)).image
    (fun s : ℕ => ((if ε then (0 : ℂ) else (s : ℂ)),
      fun j : Fin ρ => ∏ i, θ i ^ ((s : ℤ) * M j i)))).card

/-- BW §21 half split of a budget `x` into `r + 1` steps: `x/2` for step `0`, `x/(2r)` after. -/
noncomputable def halfSplit (r : ℕ) (x : ℝ) (m : ℕ) : ℕ :=
  if m = 0 then ⌊x / 2⌋₊ else ⌊x / (2 * r)⌋₊

/-- Constant of the `G_a × H'` case: `2^{1-ρ} (ρ!)² r^ρ (r+1)!/(r+1-ρ)!`. -/
noncomputable def constA (r ρ : ℕ) : ℝ :=
  (2 : ℝ) ^ (1 - (ρ : ℤ)) * (ρ.factorial : ℝ) ^ 2 * (r : ℝ) ^ ρ * ((r + 1).descFactorial ρ : ℝ)

/-- Constant of the `0 × H'` case: `2^{1-ρ} (ρ!)² r^ρ (r+1)!/(r-ρ)!`. -/
noncomputable def constB (r ρ : ℕ) : ℝ :=
  (2 : ℝ) ^ (1 - (ρ : ℤ)) * (ρ.factorial : ℝ) ^ 2 * (r : ℝ) ^ ρ *
    ((r + 1).descFactorial (ρ + 1) : ℝ)

/-- The §21 multiplicity data built from `PolyOut` parameters: `𝒮 = 2ξ^{-rI}S`. -/
noncomputable def calS (r d h : ℕ) : ℝ :=
  2 * pxi r ^ (-((r * pI r d : ℕ) : ℤ)) * (pS r d h : ℝ)

/-- `𝒯 = ξ^{rI+1} T`. -/
noncomputable def calT (r d : ℕ) (σ : Fin r → ℝ) : ℝ :=
  pxi r * pxi r ^ (r * pI r d) * (pT r d σ : ℝ)

/-- `𝒟₀ = h(D₀+1)`, `𝒟_j = 2^{-I} D_j`. -/
noncomputable def calD (r d h : ℕ) (σ : Fin r → ℝ) : Fin (r + 1) → ℝ :=
  Fin.cons ((h : ℝ) * ((pD0 r d σ : ℝ) + 1)) (fun i => (pDj r d σ i : ℝ) / 2 ^ pI r d)

/-- Philippon's `ℓ = codim_A(A ∩ G')`: `dim W − dim (W ∩ Lie G')`, `W = span (range w)`. -/
noncomputable def ellW {N q ρ : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (ε : Bool)
    (M : Fin ρ → Fin N → ℤ) : ℕ :=
  Module.finrank ℂ (Submodule.span ℂ (Set.range w)) -
    Module.finrank ℂ ((Submodule.span ℂ (Set.range w) ⊓ lieSub N ρ ε M : Submodule ℂ _))

end Work.BW
