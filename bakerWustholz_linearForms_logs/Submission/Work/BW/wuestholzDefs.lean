import Mathlib
import Submission.Work.BW.DefsB

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Definitions for the Wüstholz multiplicity estimate (`Work.BW.wuestholz_length`).

The generators of the ideal `𝔓 = subIdeal N ρ ε M` of the connected subgroup
`G' = G_a^ε × ker 𝒵` are, up to units,
* the homogenised character equations `χ^{M_j} - 1` (`j : Fin ρ`), and
* `X₀₁` when `ε = false`.

For a derivation `derH w` one has `derH w (χ^{M_j}-1) = (M_j · w) · unitMon M j`, where
`unitMon M j = ∏ X_{i1}^{M⁺} X_{i0}^{M⁻}` is a unit in the local ring at `𝔓`.  These are the
ingredients of Philippon's 4.6–4.7 (`δ_i u_j ≡ δ_{ij}`), which is what the Wüstholz length
bound `C(T+ℓ,ℓ) ≤ primLen J 𝔓` is built from. -/

namespace Work.BW

/-- The unit monomial `∏ i, X_{i.succ,1}^{M i⁺} X_{i.succ,0}^{M i⁻}` attached to the row `M j`. -/
noncomputable def unitMon {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (j : Fin ρ) : MR N :=
  ∏ i : Fin N,
    MvPolynomial.X ((i.succ, (1 : Fin 2))) ^ (M j i).toNat *
      MvPolynomial.X ((i.succ, (0 : Fin 2))) ^ (-(M j i)).toNat

/-- The complementary monomial `∏ i, X_{i.succ,0}^{M i⁺} X_{i.succ,1}^{M i⁻}`. -/
noncomputable def dualMon {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (j : Fin ρ) : MR N :=
  ∏ i : Fin N,
    MvPolynomial.X ((i.succ, (0 : Fin 2))) ^ (M j i).toNat *
      MvPolynomial.X ((i.succ, (1 : Fin 2))) ^ (-(M j i)).toNat

/-- The multihomogeneous equation `χ^{M_j} - 1` of `ker 𝒵`, homogenised. -/
noncomputable def homogChi {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (j : Fin ρ) : MR N :=
  unitMon M j - dualMon M j

/-- The linear form attached to the `j`-th generator: `M_j · v` for `j : Fin ρ`, and the
`G_a`-coordinate `v 0` for the last index `ρ` (the generator `X₀₁`, used when `ε = false`). -/
noncomputable def chiFun {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (v : Fin (N + 1) → ℂ) :
    Fin (ρ + 1) → ℂ :=
  fun j => if h : (j : ℕ) < ρ then ∑ i : Fin N, (M ⟨j, h⟩ i : ℂ) * v i.succ else v 0

/-- The monomial multiplying `chiFun` in `derH w (uGen M ε j)`: the unit monomial `unitMon`
for `j : Fin ρ`, and `0` (when `ε = true`) or `X₀₀` (when `ε = false`) for the last index. -/
noncomputable def chiMon {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (ε : Bool) :
    Fin (ρ + 1) → MR N :=
  fun j => if h : (j : ℕ) < ρ then unitMon M ⟨j, h⟩
    else if ε then 0 else MvPolynomial.X (((0 : Fin (N + 1)), (0 : Fin 2)))

/-- The generators of `𝔓` used in the Wüstholz argument: the homogenised `χ^{M_j} - 1`
(`j : Fin ρ`), and `X₀₁` for the last index (when `ε = false`; `0` when `ε = true`). -/
noncomputable def uGen {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (ε : Bool) : Fin (ρ + 1) → MR N :=
  fun j => if h : (j : ℕ) < ρ then homogChi M ⟨j, h⟩
    else if ε then 0 else MvPolynomial.X (((0 : Fin (N + 1)), (1 : Fin 2)))

/-- Composition of a family of operators according to a multi-index:
`applyL Λ α = Λ 0^{α 0} ∘ Λ 1^{α 1} ∘ ⋯` (the same `foldr` convention as `applyH`). -/
noncomputable def applyL {R : Type*} {ℓ : ℕ} (Λ : Fin ℓ → R → R) (α : Fin ℓ → ℕ) (x : R) : R :=
  (List.finRange ℓ).foldr (fun i q => (Λ i)^[α i] q) x

/-- The "weighted degree-`τ` part" `∑_{|β| = τ} C β · ∏ u i ^ (β i)`. -/
noncomputable def weightedSum {R : Type*} [CommSemiring R] {ℓ : ℕ} (u : Fin ℓ → R) (τ : ℕ)
    (C : (Fin ℓ → ℕ) → R) : R :=
  ∑ β ∈ (Fintype.piFinset (fun _ : Fin ℓ => Finset.range (τ + 1))).filter
      (fun β => ∑ i, β i = τ), C β * ∏ i, u i ^ (β i)


/-- The constant-coefficient derivation `∑ k, c i k • derH (w k)` (the operator `Λ i` of the
Wüstholz argument). -/
noncomputable def opOf {N q ℓ : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (c : Fin ℓ → Fin q → ℂ)
    (i : Fin ℓ) (F : MR N) : MR N :=
  ∑ k, c i k • derH (w k) F

end Work.BW

namespace Work.BW

/-- The monomial `∏ i, u i ^ β i`. -/
noncomputable def monoPow {R : Type*} [CommMonoid R] {ℓ : ℕ} (u : Fin ℓ → R)
    (β : Fin ℓ → ℕ) : R :=
  ∏ i, u i ^ β i

/-- The multi-indices `β : Fin ℓ → ℕ` of total degree `τ` and entries `≤ τ`. -/
noncomputable def weightFinset (ℓ τ : ℕ) : Finset (Fin ℓ → ℕ) :=
  (Fintype.piFinset (fun _ : Fin ℓ => Finset.range (τ + 1))).filter (fun β => ∑ i, β i = τ)

lemma weightedSum_eq {R : Type*} [CommSemiring R] {ℓ : ℕ} (u : Fin ℓ → R) (τ : ℕ)
    (C : (Fin ℓ → ℕ) → R) :
    weightedSum u τ C = ∑ β ∈ weightFinset ℓ τ, C β * monoPow u β := rfl

/-- The index type of the generators of `𝔓` used in the Wüstholz argument: the `ρ` character
equations, plus the `G_a`-coordinate when `ε = false`. -/
abbrev uIdx (ρ : ℕ) (ε : Bool) : Type := Fin (ρ + (if ε then 0 else 1))

/-- The usable indices, viewed inside `Fin (ρ+1)`. -/
def uIdxEmb {ρ : ℕ} {ε : Bool} (j : uIdx ρ ε) : Fin (ρ + 1) :=
  ⟨j.1, lt_of_lt_of_le j.2 (by split <;> omega)⟩

/-- The matrix of linear forms `chiFun M (w k) j` attached to the generators. -/
noncomputable def chiMat {N q ρ : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (M : Fin ρ → Fin N → ℤ)
    (ε : Bool) : Matrix (uIdx ρ ε) (Fin q) ℂ :=
  Matrix.of (fun j k => chiFun M (w k) (uIdxEmb j))


end Work.BW
