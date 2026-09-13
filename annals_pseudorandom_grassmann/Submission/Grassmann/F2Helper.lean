import Submission.Grassmann.BasicLaplacians
import Submission.Grassmann.FClassification
import Submission.Commons.Combinatorics.QBinomial.sum_aij_mul_counts
import Submission.Commons.Combinatorics.QBinomial.sum_aij_mul_counts_gen

/-!
# The `𝓕₂` helper of arXiv:2209.04243 (`lem:F2 helper`)

This file develops §4.2 of arXiv:2209.04243: the upper bound for the contribution of the
pairs `(Y,Z) ∈ 𝓕₂(X)` (those with a common image vector or with kernels not spanning `W`) to
the Fourier expansion of `f²`.

The main output is `F2Sum_bound`, the exact formal counterpart of the paper's
`lem:F2 helper`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-! ## The normalised Fourier coefficients of `(L_{V₁} ∘ L_{W₁}[f])²` -/

/-- The square of the composed basic Laplacian `L_{V₁} ∘ L_{W₁}`, as a function on `L(V,W)`. -/
def Lap2 {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ :=
  fun A => Lup V₁ (Ldown W₁ f) A * Lup V₁ (Ldown W₁ f) A

/-- The normalised Fourier coefficient of `(L_{V₁} ∘ L_{W₁}[f])²`: the pair `(Y, X+Y)`
contributes exactly when `V₁ ⊆ Im Y ∩ Im(X+Y)` and `ker Y, ker(X+Y) ⊆ W₁`. -/
theorem fcoeff_Lap2 {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    fcoeff (Lap2 V₁ W₁ f) X =
      ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂,
        (if V₁ ≤ LinearMap.range Y.mulVecLin ∧ LinearMap.ker Y.mulVecLin ≤ W₁ ∧
            V₁ ≤ LinearMap.range (X + Y).mulVecLin ∧ LinearMap.ker (X + Y).mulVecLin ≤ W₁
          then fcoeff f Y * fcoeff f (X + Y) else 0) := by
  have hq : ((2 : ℂ) ^ (m * n)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hkey : ∀ Y : Matrix (Fin n) (Fin m) 𝔽₂,
      ((2 : ℂ) ^ (m * n))⁻¹ * (((2 : ℂ) ^ (m * n))⁻¹ *
        (((if V₁ ≤ LinearMap.range Y.mulVecLin then (1 : ℂ) else 0) *
            ((if LinearMap.ker Y.mulVecLin ≤ W₁ then (1 : ℂ) else 0) * fhat f Y)) *
          ((if V₁ ≤ LinearMap.range (X + Y).mulVecLin then (1 : ℂ) else 0) *
            ((if LinearMap.ker (X + Y).mulVecLin ≤ W₁ then (1 : ℂ) else 0) *
              fhat f (X + Y))))) =
      (if V₁ ≤ LinearMap.range Y.mulVecLin ∧ LinearMap.ker Y.mulVecLin ≤ W₁ ∧
          V₁ ≤ LinearMap.range (X + Y).mulVecLin ∧ LinearMap.ker (X + Y).mulVecLin ≤ W₁
        then fcoeff f Y * fcoeff f (X + Y) else 0) := by
    intro Y
    rw [fcoeff_eq, fcoeff_eq]
    by_cases h : V₁ ≤ LinearMap.range Y.mulVecLin ∧ LinearMap.ker Y.mulVecLin ≤ W₁ ∧
        V₁ ≤ LinearMap.range (X + Y).mulVecLin ∧ LinearMap.ker (X + Y).mulVecLin ≤ W₁
    · rw [if_pos h, if_pos h.1, if_pos h.2.1, if_pos h.2.2.1, if_pos h.2.2.2]
      ring
    · rw [if_neg h]
      by_cases h1 : V₁ ≤ LinearMap.range Y.mulVecLin
      · by_cases h2 : LinearMap.ker Y.mulVecLin ≤ W₁
        · rw [if_pos h1, if_pos h2]
          by_cases h3 : V₁ ≤ LinearMap.range (X + Y).mulVecLin
          · by_cases h4 : LinearMap.ker (X + Y).mulVecLin ≤ W₁
            · exact absurd ⟨h1, h2, h3, h4⟩ h
            · rw [if_neg h4]; ring
          · rw [if_neg h3]; ring
        · rw [if_neg h2]; ring
      · rw [if_neg h1]; ring
  change fcoeff (fun A => Lup V₁ (Ldown W₁ f) A * Lup V₁ (Ldown W₁ f) A) X = _
  rw [fcoeff_eq, fhat_sq_Lup_Ldown]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun Y _ => hkey Y

/-! ## A general counting identity for double indicators -/

/-- A double sum of `if p a ∧ q b then z else 0` factors into the two cardinalities. -/
lemma sum_sum_ite_and {α β : Type*} [Fintype α] [Fintype β]
    (p : α → Prop) (q : β → Prop) (z : ℂ) :
    (∑ a : α, ∑ b : β, (if p a ∧ q b then z else 0))
      = (Fintype.card {a : α // p a} : ℂ) * (Fintype.card {b : β // q b} : ℂ) * z := by
  have h : ∀ (a : α) (b : β),
      (if p a ∧ q b then z else 0)
        = (if p a then (1 : ℂ) else 0) * ((if q b then (1 : ℂ) else 0) * z) := by
    intro a b
    by_cases ha : p a <;> by_cases hb : q b <;> simp [ha, hb]
  simp only [h]
  rw [← Finset.sum_mul_sum]
  have h2 : (∑ b : β, (if q b then (1 : ℂ) else 0) * z)
      = (∑ b : β, (if q b then (1 : ℂ) else 0)) * z := (Finset.sum_mul _ _ _).symm
  rw [h2]
  have hp : (∑ a : α, (if p a then (1 : ℂ) else 0)) = (Fintype.card {a : α // p a} : ℂ) := by
    rw [Finset.sum_boole]
    rw [← Fintype.card_subtype p]
  have hq : (∑ b : β, (if q b then (1 : ℂ) else 0)) = (Fintype.card {b : β // q b} : ℂ) := by
    rw [Finset.sum_boole]
    rw [← Fintype.card_subtype q]
  rw [hp, hq]
  ring

/-! ## The `𝓕₂` sum and the Möbius coefficients -/

/-- The intersection of the images of `X, Y, Z` — the `V'` of the paper. -/
def Vint {m n : ℕ} (X Y Z : Matrix (Fin n) (Fin m) 𝔽₂) : Submodule 𝔽₂ (Fin n → 𝔽₂) :=
  LinearMap.range X.mulVecLin ⊓ LinearMap.range Y.mulVecLin ⊓ LinearMap.range Z.mulVecLin

/-- The sum of the kernels of `X, Y, Z` — the `W'` of the paper. -/
def Wsum {m n : ℕ} (X Y Z : Matrix (Fin n) (Fin m) 𝔽₂) : Submodule 𝔽₂ (Fin m → 𝔽₂) :=
  LinearMap.ker X.mulVecLin ⊔ LinearMap.ker Y.mulVecLin ⊔ LinearMap.ker Z.mulVecLin

/-- `(Y,Z) ∈ 𝓕₂(X)`: the pair has a common image vector, or kernels that fail to span `W`.
(The relation `Y + Z = X` is built into the indexing of `F2Sum`.)  Not to be confused with
`Submission.Grassmann.IsF2` (the paper's `𝓕₁`/`𝓕₂` classification of `lem:F1`). -/
def IsF2BS {m n : ℕ} (X Y Z : Matrix (Fin n) (Fin m) 𝔽₂) : Prop :=
  Vint X Y Z ≠ ⊥ ∨ Wsum X Y Z ≠ ⊤

/-- The `𝓕₂` contribution `Σ_{(Y,Z) ∈ 𝓕₂(X)} f̂(Y) f̂(Z)` of the paper. -/
def F2Sum {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : ℂ :=
  ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂,
    if IsF2BS X Y (X + Y) then fcoeff f Y * fcoeff f (X + Y) else 0

/-- The Möbius sequence of the paper's `lem:F2 helper`:
`a_k = (-1)^{k-1} q^{k(k-1)/2}` (`q = 2`). -/
def mob (k : ℕ) : ℤ := (-1 : ℤ) ^ (k - 1) * (2 : ℤ) ^ (k * (k - 1) / 2)

/-- The coefficient `a_{i,j}` of the paper's inclusion--exclusion identity. -/
def coefZ (i j : ℕ) : ℤ :=
  if i = 0 then (if j = 0 then 0 else mob j)
  else (if j = 0 then mob i else -(mob i * mob j))

/-- The number of `i`-dimensional subspaces of `Im X ⊓ Im Y ⊓ Im(X+Y)`. -/
def cntV {m n : ℕ} (X Y : Matrix (Fin n) (Fin m) 𝔽₂) (i : ℕ) : ℕ :=
  Nat.card {V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂) //
    V₁ ≤ Vint X Y (X + Y) ∧ Module.finrank 𝔽₂ V₁ = i}

/-- The number of codimension-`j` subspaces containing `ker X ⊔ ker Y ⊔ ker(X+Y)`. -/
def cntW {m n : ℕ} (X Y : Matrix (Fin n) (Fin m) 𝔽₂) (j : ℕ) : ℕ :=
  Nat.card {W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂) //
    Wsum X Y (X + Y) ≤ W₁ ∧ Module.finrank 𝔽₂ W₁ = m - j}

/-! ## The Möbius sequence -/

lemma mob_sum_eq_one (t : ℕ) (ht : 1 ≤ t) :
    ∑ i ∈ Finset.Icc 1 t, mob i * (Commons.Combinatorics.QBinomial.gb t i : ℤ) = 1 := by
  have h := Commons.Combinatorics.QBinomial.alt_sum_eq_one (n := t) ht
  simpa only [mob, Commons.Combinatorics.QBinomial.gb] using h

/-- Interchange of a triple sum: `∑_a ∑_b ∑_c g a b c = ∑_c ∑_a ∑_b g a b c`. -/
lemma sum_sum_sum_comm {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M]
    (g : α → β → γ → M) :
    (∑ a : α, ∑ b : β, ∑ c : γ, g a b c) = ∑ c : γ, ∑ a : α, ∑ b : β, g a b c := by
  have h1 : (∑ a : α, ∑ b : β, ∑ c : γ, g a b c) = ∑ a : α, ∑ c : γ, ∑ b : β, g a b c := by
    apply Finset.sum_congr rfl
    intro a _
    exact Finset.sum_comm
  rw [h1]
  exact Finset.sum_comm

/-- **The pair expansion of `Σ_{V₁ ∈ 𝓥_i(X), W₁ ∈ 𝓦_j(X)} (L_{V₁}∘L_{W₁}[f])²(X)`.**

Expanding the Fourier coefficient of `(L_{V₁}∘L_{W₁}[f])²` and interchanging the three sums,
the contribution of a character `Y` is the product of the two subspace counts. -/
lemma sum_pair_Lap2 {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (i j : ℕ) :
    (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j)
          then fcoeff (Lap2 V₁ W₁ f) X else 0))
      = ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂,
          (cntV X Y i : ℂ) * (cntW X Y j : ℂ) * (fcoeff f Y * fcoeff f (X + Y)) := by
  classical
  have hstep1 : ∀ (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)),
      (if (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j)
        then fcoeff (Lap2 V₁ W₁ f) X else 0)
      = (if (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j)
        then (1 : ℂ) else 0) * fcoeff (Lap2 V₁ W₁ f) X := by
    intro V₁ W₁
    by_cases h : (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j)
    · rw [if_pos h, if_pos h, one_mul]
    · rw [if_neg h, if_neg h, zero_mul]
  refine (Finset.sum_congr rfl fun V₁ _ =>
    Finset.sum_congr rfl fun W₁ _ => hstep1 V₁ W₁).trans ?_
  have hstep2 : ∀ (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)),
      (if (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j)
        then (1 : ℂ) else 0) * fcoeff (Lap2 V₁ W₁ f) X
        = ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂,
            (if (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j)
                ∧ (V₁ ≤ LinearMap.range Y.mulVecLin ∧ LinearMap.ker Y.mulVecLin ≤ W₁ ∧ V₁ ≤ LinearMap.range (X + Y).mulVecLin ∧ LinearMap.ker (X + Y).mulVecLin ≤ W₁)
              then fcoeff f Y * fcoeff f (X + Y) else 0) := by
    intro V₁ W₁
    rw [fcoeff_Lap2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Y _ => ?_
    by_cases hc : (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j)
    · by_cases hp : (V₁ ≤ LinearMap.range Y.mulVecLin ∧ LinearMap.ker Y.mulVecLin ≤ W₁ ∧ V₁ ≤ LinearMap.range (X + Y).mulVecLin ∧ LinearMap.ker (X + Y).mulVecLin ≤ W₁)
      · have hcp : (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j) ∧ (V₁ ≤ LinearMap.range Y.mulVecLin ∧ LinearMap.ker Y.mulVecLin ≤ W₁ ∧ V₁ ≤ LinearMap.range (X + Y).mulVecLin ∧ LinearMap.ker (X + Y).mulVecLin ≤ W₁) := ⟨hc, hp⟩
        rw [if_pos hcp, if_pos hp, if_pos hc, one_mul]
      · have hcp : ¬ ((V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j) ∧ (V₁ ≤ LinearMap.range Y.mulVecLin ∧ LinearMap.ker Y.mulVecLin ≤ W₁ ∧ V₁ ≤ LinearMap.range (X + Y).mulVecLin ∧ LinearMap.ker (X + Y).mulVecLin ≤ W₁)) := fun h => hp h.2
        rw [if_neg hcp, if_neg hp, if_pos hc, one_mul]
    · have hcp : ¬ ((V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j) ∧ (V₁ ≤ LinearMap.range Y.mulVecLin ∧ LinearMap.ker Y.mulVecLin ≤ W₁ ∧ V₁ ≤ LinearMap.range (X + Y).mulVecLin ∧ LinearMap.ker (X + Y).mulVecLin ≤ W₁)) := fun h => hc h.1
      rw [if_neg hcp, if_neg hc, zero_mul]
  refine (Finset.sum_congr rfl fun V₁ _ =>
    Finset.sum_congr rfl fun W₁ _ => hstep2 V₁ W₁).trans ?_
  rw [sum_sum_sum_comm]
  refine Finset.sum_congr rfl fun Y _ => ?_
  have hiff : ∀ (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)),
      (((V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j) ∧ (V₁ ≤ LinearMap.range Y.mulVecLin ∧ LinearMap.ker Y.mulVecLin ≤ W₁ ∧ V₁ ≤ LinearMap.range (X + Y).mulVecLin ∧ LinearMap.ker (X + Y).mulVecLin ≤ W₁))
        ↔ ((V₁ ≤ Vint X Y (X + Y) ∧ Module.finrank 𝔽₂ V₁ = i) ∧
            (Wsum X Y (X + Y) ≤ W₁ ∧ Module.finrank 𝔽₂ W₁ = m - j))) := by
    intro V₁ W₁
    rw [Vint, Wsum]
    simp only [le_inf_iff, sup_le_iff]
    tauto
  have hY1 : (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if ((V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j) ∧ (V₁ ≤ LinearMap.range Y.mulVecLin ∧ LinearMap.ker Y.mulVecLin ≤ W₁ ∧ V₁ ≤ LinearMap.range (X + Y).mulVecLin ∧ LinearMap.ker (X + Y).mulVecLin ≤ W₁)) then fcoeff f Y * fcoeff f (X + Y) else 0))
      = (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if (V₁ ≤ Vint X Y (X + Y) ∧ Module.finrank 𝔽₂ V₁ = i) ∧
            (Wsum X Y (X + Y) ≤ W₁ ∧ Module.finrank 𝔽₂ W₁ = m - j)
          then fcoeff f Y * fcoeff f (X + Y) else 0)) := by
    refine Finset.sum_congr rfl fun V₁ _ => Finset.sum_congr rfl fun W₁ _ => ?_
    by_cases h : ((V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j) ∧ (V₁ ≤ LinearMap.range Y.mulVecLin ∧ LinearMap.ker Y.mulVecLin ≤ W₁ ∧ V₁ ≤ LinearMap.range (X + Y).mulVecLin ∧ LinearMap.ker (X + Y).mulVecLin ≤ W₁))
    · rw [if_pos h, if_pos ((hiff V₁ W₁).mp h)]
    · rw [if_neg h, if_neg (fun hc => h ((hiff V₁ W₁).mpr hc))]
  rw [hY1]
  have hY2 : (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if (V₁ ≤ Vint X Y (X + Y) ∧ Module.finrank 𝔽₂ V₁ = i) ∧
            (Wsum X Y (X + Y) ≤ W₁ ∧ Module.finrank 𝔽₂ W₁ = m - j)
          then fcoeff f Y * fcoeff f (X + Y) else 0))
      = (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂),
          (if V₁ ≤ Vint X Y (X + Y) ∧ Module.finrank 𝔽₂ V₁ = i then (1 : ℂ) else 0)) *
        (∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
          (if Wsum X Y (X + Y) ≤ W₁ ∧ Module.finrank 𝔽₂ W₁ = m - j then (1 : ℂ) else 0)) *
        (fcoeff f Y * fcoeff f (X + Y)) := by
    have hpt : ∀ (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)),
        (if (V₁ ≤ Vint X Y (X + Y) ∧ Module.finrank 𝔽₂ V₁ = i) ∧
            (Wsum X Y (X + Y) ≤ W₁ ∧ Module.finrank 𝔽₂ W₁ = m - j)
          then fcoeff f Y * fcoeff f (X + Y) else 0)
        = (if V₁ ≤ Vint X Y (X + Y) ∧ Module.finrank 𝔽₂ V₁ = i then (1 : ℂ) else 0) *
          ((if Wsum X Y (X + Y) ≤ W₁ ∧ Module.finrank 𝔽₂ W₁ = m - j then (1 : ℂ) else 0) *
            (fcoeff f Y * fcoeff f (X + Y))) := by
      intro V₁ W₁
      by_cases hp : V₁ ≤ Vint X Y (X + Y) ∧ Module.finrank 𝔽₂ V₁ = i <;>
        by_cases hq : Wsum X Y (X + Y) ≤ W₁ ∧ Module.finrank 𝔽₂ W₁ = m - j <;>
        simp [hp, hq]
    refine (Finset.sum_congr rfl fun V₁ _ => Finset.sum_congr rfl fun W₁ _ => hpt V₁ W₁).trans ?_
    rw [← Finset.sum_mul_sum]
    rw [← Finset.sum_mul]
    ring
  rw [hY2]
  have hcardV : (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂),
        (if V₁ ≤ Vint X Y (X + Y) ∧ Module.finrank 𝔽₂ V₁ = i then (1 : ℂ) else 0))
      = (Fintype.card {V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂) //
          V₁ ≤ Vint X Y (X + Y) ∧ Module.finrank 𝔽₂ V₁ = i} : ℂ) := by
    rw [Finset.sum_boole]
    rw [← Fintype.card_subtype (fun V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂) =>
      V₁ ≤ Vint X Y (X + Y) ∧ Module.finrank 𝔽₂ V₁ = i)]
  have hcardW : (∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if Wsum X Y (X + Y) ≤ W₁ ∧ Module.finrank 𝔽₂ W₁ = m - j then (1 : ℂ) else 0))
      = (Fintype.card {W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂) //
          Wsum X Y (X + Y) ≤ W₁ ∧ Module.finrank 𝔽₂ W₁ = m - j} : ℂ) := by
    rw [Finset.sum_boole]
    rw [← Fintype.card_subtype (fun W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂) =>
      Wsum X Y (X + Y) ≤ W₁ ∧ Module.finrank 𝔽₂ W₁ = m - j)]
  rw [hcardV, hcardW, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  simp only [cntV, cntW]

/-- The `(i,j)`-weighted count of a character `Y`. -/
def gterm {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂) (i j : ℕ)
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) : ℂ :=
  (cntV X Y i : ℂ) * (cntW X Y j : ℂ)

/-- `sum_pair_Lap2` in terms of `gterm`. -/
lemma sum_pair_Lap2_gterm {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (i j : ℕ) :
    (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j) then fcoeff (Lap2 V₁ W₁ f) X else 0))
      = ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂,
          gterm X i j Y * (fcoeff f Y * fcoeff f (X + Y)) := by
  rw [sum_pair_Lap2]
  rfl

/-- Interchange of the `(i,j)`-sums with the character sum. -/
lemma sum_range_range_comm {M γ : Type*} [AddCommMonoid M] [Fintype γ]
    (n m : ℕ) (g : ℕ → ℕ → γ → M) :
    (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1), ∑ Y : γ, g i j Y)
      = ∑ Y : γ, ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1), g i j Y := by
  have h1 : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1), ∑ Y : γ, g i j Y)
      = ∑ i ∈ Finset.range (n + 1), ∑ Y : γ, ∑ j ∈ Finset.range (m + 1), g i j Y := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  rw [h1]
  exact Finset.sum_comm

/-- **The inclusion--exclusion identity of the `𝓕₂` helper**, in the Fourier-coefficient
normalisation: the `(i,j)`-weighted sum of the character counts is the indicator of `𝓕₂`. -/
lemma sum_aij_gterm {m n : ℕ} (X Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        (coefZ i j : ℂ) * gterm X i j Y)
      = if Vint X Y (X + Y) = ⊥ ∧ Wsum X Y (X + Y) = ⊤ then (0 : ℂ) else 1 := by
  classical
  have h' : (((∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        coefZ i j * ((cntV X Y i : ℤ) * (cntW X Y j : ℤ))) : ℤ)
      = (if Vint X Y (X + Y) = ⊥ ∧ Wsum X Y (X + Y) = ⊤ then 0 else 1 : ℤ)) :=
    Commons.Combinatorics.QBinomial.sum_aij_mul_counts_gen n m mob
      (fun t ht => mob_sum_eq_one t ht) (Vint X Y (X + Y)) (Wsum X Y (X + Y))
  have hcast : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        (coefZ i j : ℂ) * gterm X i j Y)
      = (((∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        coefZ i j * ((cntV X Y i : ℤ) * (cntW X Y j : ℤ))) : ℤ) : ℂ) := by
    push_cast
    simp only [gterm]
  rw [hcast, congrArg (fun z : ℤ => (z : ℂ)) h']
  split_ifs <;> norm_num

/-- **The main expansion identity of the `𝓕₂` helper**: the `𝓕₂` contribution is the
`(i,j)`-weighted sum of the `(L_{V₁}∘L_{W₁}[f])²` Fourier coefficients. -/
theorem F2Sum_eq_aij {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    F2Sum X f =
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        (coefZ i j : ℂ) *
          (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
            (if (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j) then fcoeff (Lap2 V₁ W₁ f) X else 0)) := by
  classical
  change (∑ Y : Matrix (Fin n) (Fin m) 𝔽₂,
      (if IsF2BS X Y (X + Y) then fcoeff f Y * fcoeff f (X + Y) else 0)) = _
  have hstep : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        (coefZ i j : ℂ) *
          (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
            (if (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j) then fcoeff (Lap2 V₁ W₁ f) X else 0)))
      = ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂,
          (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
              (coefZ i j : ℂ) * gterm X i j Y) *
            (fcoeff f Y * fcoeff f (X + Y)) := by
    have h1 : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          (coefZ i j : ℂ) *
            (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
              (if (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j) then fcoeff (Lap2 V₁ W₁ f) X else 0)))
        = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
            ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂,
              (coefZ i j : ℂ) * (gterm X i j Y * (fcoeff f Y * fcoeff f (X + Y))) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [sum_pair_Lap2_gterm, Finset.mul_sum]
    rw [h1, sum_range_range_comm]
    refine Finset.sum_congr rfl fun Y _ => ?_
    have h1' : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          (coefZ i j : ℂ) * (gterm X i j Y * (fcoeff f Y * fcoeff f (X + Y))))
        = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
            ((coefZ i j : ℂ) * gterm X i j Y) *
              (fcoeff f Y * fcoeff f (X + Y)) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h1']
    simp only [Finset.sum_mul]
  rw [hstep]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [sum_aij_gterm X Y]
  by_cases hc : Vint X Y (X + Y) = ⊥ ∧ Wsum X Y (X + Y) = ⊤
  · have hb : ¬ IsF2BS X Y (X + Y) := by
      intro h; rcases h with h | h
      · exact h hc.1
      · exact h hc.2
    rw [if_pos hc, if_neg hb, zero_mul]
  · have hb : IsF2BS X Y (X + Y) := by
      rcases not_and_or.mp hc with h | h
      · exact Or.inl h
      · exact Or.inr h
    rw [if_neg hc, if_pos hb, one_mul]

/-! ## The `𝓕₂` helper -/

/-- The Möbius coefficient is bounded by `q^{2k²}`. -/
lemma mob_abs_le (k : ℕ) : |((mob k : ℤ) : ℝ)| ≤ (2 : ℝ) ^ (2 * k ^ 2) := by
  have h1 : ((mob k : ℤ) : ℝ) = ((-1 : ℝ) ^ (k - 1)) * (2 : ℝ) ^ (k * (k - 1) / 2) := by
    rw [mob]
    push_cast
    ring
  rw [h1, abs_mul]
  have h2 : |((-1 : ℝ) ^ (k - 1))| = 1 := by
    rw [abs_pow]
    simp
  rw [h2, one_mul, abs_of_nonneg (by positivity)]
  refine pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ?_
  have h3 : k * (k - 1) ≤ k * k := Nat.mul_le_mul_left k (Nat.sub_le k 1)
  have h4 : k * k ≤ 2 * k ^ 2 := by rw [pow_two]; omega
  calc k * (k - 1) / 2 ≤ k * (k - 1) := Nat.div_le_self _ _
    _ ≤ k * k := h3
    _ ≤ 2 * k ^ 2 := h4

/-- The coefficient `a_{i,j}` of the inclusion--exclusion identity is bounded by
`q^{2i²+2j²}`, and vanishes for `(i,j) = (0,0)`. -/
lemma coefZ_abs_le (i j : ℕ) :
    |((coefZ i j : ℤ) : ℝ)|
      ≤ (if i = 0 ∧ j = 0 then 0 else (2 : ℝ) ^ (2 * i ^ 2 + 2 * j ^ 2)) := by
  by_cases hi : i = 0
  · by_cases hj : j = 0
    · subst hi; subst hj
      norm_num [coefZ]
    · subst hi
      have h0 : coefZ 0 j = mob j := by simp [coefZ, hj]
      rw [h0, if_neg (by simp [hj])]
      have h := mob_abs_le j
      simpa using h
  · by_cases hj : j = 0
    · subst hj
      have h0 : coefZ i 0 = mob i := by simp [coefZ, hi]
      rw [h0, if_neg (by simp [hi])]
      have h := mob_abs_le i
      simpa using h
    · have h0 : coefZ i j = -(mob i * mob j) := by simp [coefZ, hi, hj]
      rw [h0, if_neg (by simp [hi, hj])]
      have h1 := mob_abs_le i
      have h2 := mob_abs_le j
      have hc : ((mob i * mob j : ℤ) : ℝ) = ((mob i : ℤ) : ℝ) * ((mob j : ℤ) : ℝ) := by
        push_cast
        ring
      rw [Int.cast_neg, hc, abs_neg, abs_mul]
      calc |((mob i : ℤ) : ℝ)| * |((mob j : ℤ) : ℝ)|
          ≤ (2 : ℝ) ^ (2 * i ^ 2) * (2 : ℝ) ^ (2 * j ^ 2) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = (2 : ℝ) ^ (2 * i ^ 2 + 2 * j ^ 2) := by rw [← pow_add]

set_option maxHeartbeats 2000000 in
/-- **The `𝓕₂` helper of arXiv:2209.04243 (`lem:F2 helper`)**: the `𝓕₂` contribution is
bounded by the weighted sum of the `(L_{V₁}∘L_{W₁}[f])²` Fourier coefficients. -/
theorem F2_helper {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    ‖F2Sum X f‖ ≤
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        (if i = 0 ∧ j = 0 then 0 else (2 : ℝ) ^ (2 * i ^ 2 + 2 * j ^ 2)) *
          (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
            (if (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j) then ‖fcoeff (Lap2 V₁ W₁ f) X‖ else 0)) := by
  classical
  rw [F2Sum_eq_aij X f]
  have hS : ∀ (i j : ℕ),
      ‖∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j) then fcoeff (Lap2 V₁ W₁ f) X else 0)‖
      ≤ ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j) then ‖fcoeff (Lap2 V₁ W₁ f) X‖ else 0) := by
    intro i j
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum fun V₁ _ => ?_
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum fun W₁ _ => ?_
    by_cases h : (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j)
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, norm_zero]
  calc ‖∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        (coefZ i j : ℂ) *
          (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
            (if (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j) then fcoeff (Lap2 V₁ W₁ f) X else 0))‖
      ≤ ∑ i ∈ Finset.range (n + 1), ‖∑ j ∈ Finset.range (m + 1),
          (coefZ i j : ℂ) *
            (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
              (if (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j) then fcoeff (Lap2 V₁ W₁ f) X else 0))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          ‖(coefZ i j : ℂ) *
            (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
              (if (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j) then fcoeff (Lap2 V₁ W₁ f) X else 0))‖ :=
        Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          |((coefZ i j : ℤ) : ℝ)| *
            (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
              (if (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j) then ‖fcoeff (Lap2 V₁ W₁ f) X‖ else 0)) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, Complex.norm_intCast]
        exact mul_le_mul_of_nonneg_left (hS i j) (abs_nonneg _)
    _ ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          (if i = 0 ∧ j = 0 then 0 else (2 : ℝ) ^ (2 * i ^ 2 + 2 * j ^ 2)) *
            (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
              (if (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j) then ‖fcoeff (Lap2 V₁ W₁ f) X‖ else 0)) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        refine mul_le_mul_of_nonneg_right (coefZ_abs_le i j) ?_
        refine Finset.sum_nonneg fun V₁ _ => Finset.sum_nonneg fun W₁ _ => ?_
        by_cases h : (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j)
        · rw [if_pos h]; positivity
        · rw [if_neg h]


end

end Submission.Grassmann