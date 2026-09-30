import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! Definitions for the split of `zero_estimate_stepwise` (blocks B1–B3 and the §5.1 chain).
Install as `Submission/Work/BW/DefsB.lean`, importing `Submission.Work.BW.DefsMult`, inside
`namespace Work.BW`. Conventions: an affine point of `G = G_a × G_m^N` is `y : Fin (N+1) → ℂ`
with `y (i.succ) ≠ 0`; the group law is `(a, y) · (b, z) = (a + b, y z)`; cone points
`x : Fin (N+1) × Fin 2 → ℂ` are acted on by `coneAct`; `transl g` is the pull-back
`F ↦ F ∘ (g ⋆ ·)` on `MR N`, a graded ring map. -/

/-- The multidegree vector `D` as a finitely supported function. -/
noncomputable def fsD {N : ℕ} (D : Fin (N + 1) → ℕ) : Fin (N + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm D

/-- `y` is a point of `G = G_a × G_m^N` (affine coordinates). -/
def InG {N : ℕ} (y : Fin (N + 1) → ℂ) : Prop := ∀ i : Fin N, y i.succ ≠ 0

/-- Group law of `G` in affine coordinates. -/
noncomputable def gmul {N : ℕ} (g y : Fin (N + 1) → ℂ) : Fin (N + 1) → ℂ :=
  Fin.cons (g 0 + y 0) (fun i : Fin N => g i.succ * y i.succ)

/-- Inverse in `G`. -/
noncomputable def ginv {N : ℕ} (g : Fin (N + 1) → ℂ) : Fin (N + 1) → ℂ :=
  Fin.cons (-g 0) (fun i : Fin N => (g i.succ)⁻¹)

/-- Neutral element `(0, 1, …, 1)` of `G`. -/
noncomputable def gone (N : ℕ) : Fin (N + 1) → ℂ := Fin.cons 0 (fun _ : Fin N => 1)

/-- Action of `g ∈ G` on cone points: `X_{01} ↦ X_{01} + g₀ X_{00}`, `X_{i1} ↦ gᵢ X_{i1}`. -/
noncomputable def coneAct {N : ℕ} (g : Fin (N + 1) → ℂ) (x : Fin (N + 1) × Fin 2 → ℂ) :
    Fin (N + 1) × Fin 2 → ℂ :=
  fun v => if v.2 = 0 then x v else if v.1 = 0 then x v + g 0 * x (0, 0) else g v.1 * x v

/-- Translation `τ_g` on the homogeneous coordinate ring: `eval x (τ_g F) = eval (g ⋆ x) F`. -/
noncomputable def transl {N : ℕ} (g : Fin (N + 1) → ℂ) : MR N →ₐ[ℂ] MR N :=
  MvPolynomial.aeval (fun v : Fin (N + 1) × Fin 2 =>
    if v.2 = 0 then MvPolynomial.X v
    else if v.1 = 0 then MvPolynomial.X v + MvPolynomial.C (g 0) * MvPolynomial.X (0, 0)
    else MvPolynomial.C (g v.1) * MvPolynomial.X v)

/-- Homogeneous invariant derivation with Lie vector `w`:
`w₀ X_{00} ∂/∂X_{01} + ∑ᵢ w_{i+1} X_{i+1,1} ∂/∂X_{i+1,1}` (multidegree preserving). -/
noncomputable def derH {N : ℕ} (w : Fin (N + 1) → ℂ) (F : MR N) : MR N :=
  MvPolynomial.C (w 0) * MvPolynomial.X (0, 0) * MvPolynomial.pderiv (0, 1) F +
    ∑ i : Fin N, MvPolynomial.C (w i.succ) * MvPolynomial.X (i.succ, 1) *
      MvPolynomial.pderiv (i.succ, 1) F

/-- `∏_k (derH (w k))^{t k}` applied to `F` (Philippon's `δ^t`, before translation). -/
noncomputable def applyH {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (t : Fin q → ℕ) (F : MR N) :
    MR N :=
  (List.finRange q).foldr (fun m Q => (derH (w m))^[t m] Q) F

/-- Homogenisation of `P` to multidegree exactly `D`. -/
noncomputable def homog {N : ℕ} (D : Fin (N + 1) → ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) : MR N :=
  ∑ s ∈ P.support, MvPolynomial.C (P.coeff s) *
    ∏ i : Fin (N + 1), MvPolynomial.X (i, 1) ^ (s i) * MvPolynomial.X (i, 0) ^ (D i - s i)

/-- Generators of Philippon's `I_r`: `τ_{sγ} δ^t P^h` with `s ≤ A`, `|t| ≤ B`. -/
def chainGen {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (θ : Fin N → ℂ) (D : Fin (N + 1) → ℕ)
    (P : MvPolynomial (Fin (N + 1)) ℂ) (A B : ℕ) : Set (MR N) :=
  {F | ∃ (s : ℕ) (t : Fin q → ℕ), s ≤ A ∧ ∑ k, t k ≤ B ∧
    F = transl (ptTheta θ s) (applyH w t (homog D P))}

/-- Philippon's `I_r` (with `A = ∑_{m<r-1} Sq m`, `B = ∑_{m<r-1} Tq m`). -/
noncomputable def chainIdeal {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (θ : Fin N → ℂ) (D : Fin (N + 1) → ℕ)
    (P : MvPolynomial (Fin (N + 1)) ℂ) (A B : ℕ) : Ideal (MR N) :=
  Ideal.span (chainGen w θ D P A B)

/-- `p` passes through a point of `G` (on the cone). -/
def MeetsG (N : ℕ) (p : Ideal (MR N)) : Prop := ∃ x, OnG N x ∧ p ≤ ptIdeal N x

/-- `G`-points (affine) of `Z(𝔓)`. -/
def ZG {N : ℕ} (𝔓 : Ideal (MR N)) : Set (Fin (N + 1) → ℂ) :=
  {v | InG v ∧ ∀ F ∈ 𝔓, MvPolynomial.eval (conePt N v) F = 0}

/-- Philippon's `H_V(t)`: the `g ∈ G` with `τ_g δ^{t'} I ⊆ 𝔓` for all `|t'| ≤ t`. -/
def Hset {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (𝔓 I : Ideal (MR N)) (t : ℕ) :
    Set (Fin (N + 1) → ℂ) :=
  {g | InG g ∧ ∀ F ∈ I, ∀ t' : Fin q → ℕ, ∑ k, t' k ≤ t → transl g (applyH w t' F) ∈ 𝔓}

/-- Stabiliser `G_V = {g ∈ G : τ_g 𝔓 = 𝔓}`. -/
def stabG {N : ℕ} (𝔓 : Ideal (MR N)) : Set (Fin (N + 1) → ℂ) :=
  {g | InG g ∧ Ideal.map (transl g) 𝔓 = 𝔓}

/-- A Zariski-closed subgroup of `G`: a subgroup that is the zero set in `G` of polynomials. -/
def IsClosedSubG {N : ℕ} (H : Set (Fin (N + 1) → ℂ)) : Prop :=
  (∀ y ∈ H, InG y) ∧ gone N ∈ H ∧ (∀ a ∈ H, ∀ b ∈ H, gmul a b ∈ H) ∧
    (∀ a ∈ H, ginv a ∈ H) ∧
    ∃ S : Set (MvPolynomial (Fin (N + 1)) ℂ),
      H = {y | InG y ∧ ∀ f ∈ S, MvPolynomial.eval y f = 0}

/-- The connected subgroup `G' = G_a^ε × ker 𝒵` as a set. -/
def subSet (N ρ : ℕ) (ε : Bool) (M : Fin ρ → Fin N → ℤ) : Set (Fin (N + 1) → ℂ) :=
  {y | InSub N ρ ε M y}

/-- Ideal of the closure of the coset `σ ⋆ G'`: `τ_{σ⁻¹}(I(G'))`. -/
noncomputable def cosetIdeal {N ρ : ℕ} (σ : Fin (N + 1) → ℂ) (ε : Bool)
    (M : Fin ρ → Fin N → ℤ) : Ideal (MR N) :=
  Ideal.map (transl (ginv σ)) (subIdeal N ρ ε M)

/-- Generators of Philippon's `J'`: `τ_v F`, `F ∈ chainGen`, `v ∈ V ∩ G`. -/
def bigGen {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (θ : Fin N → ℂ) (D : Fin (N + 1) → ℕ)
    (P : MvPolynomial (Fin (N + 1)) ℂ) (A B : ℕ) (𝔓 : Ideal (MR N)) : Set (MR N) :=
  {F | ∃ v ∈ ZG 𝔓, ∃ Q ∈ chainGen w θ D P A B, F = transl v Q}

end Work.BW
