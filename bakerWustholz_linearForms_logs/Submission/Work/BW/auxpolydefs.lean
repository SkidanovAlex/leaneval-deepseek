import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for `aux_poly` (Baker–Wüstholz §12–13)

This file fixes the notions used by the §12–13 auxiliary-polynomial construction:
the field `F = ℚ(α'₁,…,α'_r)`, the rational values `Δ(x;k)`, `Θ(x;k,l,m)` at integer
arguments, the integer `γ_j(λ)`, the coefficients of the linear system, and the index sets
for the unknowns and the equations.
-/

namespace Work.BW

open Complex

/-- The number field `ℚ(α'₁,…,α'_r) ≤ K` over which Siegel's box principle is applied. -/
noncomputable def auxField {K : Type*} [Field K] [Algebra ℚ K] {r : ℕ} (α' : Fin r → K) :
    IntermediateField ℚ K :=
  IntermediateField.adjoin ℚ (Set.range α')

/-- `α'_j`, viewed as an element of `auxField α'`. -/
def alphaF {K : Type*} [Field K] [Algebra ℚ K] {r : ℕ} (α' : Fin r → K) (j : Fin r) :
    auxField α' :=
  ⟨α' j, IntermediateField.subset_adjoin ℚ (Set.range α') ⟨j, rfl⟩⟩

@[simp] lemma alphaF_coe {K : Type*} [Field K] [Algebra ℚ K] {r : ℕ} (α' : Fin r → K)
    (j : Fin r) : ((alphaF α' j : auxField α') : K) = α' j := rfl

/-- `γ_j(λ) = ∑ᵢ (b_k ∂L_i/∂z_j − b_j ∂L_i/∂z_k) λᵢ ∈ ℤ`. -/
def gamInt {n r : ℕ} (b : Fin n → ℤ) (k : Fin n) (L : Fin r → Fin n → ℤ) (j : Fin n)
    (lm : Fin r → ℕ) : ℤ := ∑ i, derVec b k L j i * (lm i : ℤ)

@[simp] lemma gamInt_cast {n r : ℕ} (b : Fin n → ℤ) (k : Fin n) (L : Fin r → Fin n → ℤ)
    (j : Fin n) (lm : Fin r → ℕ) : ((gamInt b k L j lm : ℤ) : ℂ) = gam b k L j lm := by
  simp [gamInt, gam]

/-- `Δ(x;k) ∈ ℚ` for an integer argument. -/
noncomputable def deltaRat (x : ℤ) (k : ℕ) : ℚ := Polynomial.aeval (x : ℚ) (deltaPoly k)

/-- `Θ(x;k,l,m) ∈ ℚ` for an integer argument. -/
noncomputable def thetaRat (x : ℤ) (k l m : ℕ) : ℚ :=
  Polynomial.aeval (x : ℚ) (Polynomial.hasseDeriv m (deltaPoly k ^ l))

lemma Delta_eq_deltaRat (x : ℤ) (k : ℕ) : Delta (x : ℂ) k = (deltaRat x k : ℂ) := by
  simp only [Delta, deltaRat]
  rw [show (x : ℂ) = (Algebra.ofId ℚ ℂ) (x : ℚ) by simp]
  exact Polynomial.aeval_algHom_apply (Algebra.ofId ℚ ℂ) (x : ℚ) _

lemma Theta_eq_thetaRat (x : ℤ) (k l m : ℕ) : Theta (x : ℂ) k l m = (thetaRat x k l m : ℂ) := by
  simp only [Theta, thetaRat]
  rw [show (x : ℂ) = (Algebra.ofId ℚ ℂ) (x : ℚ) by simp]
  exact Polynomial.aeval_algHom_apply (Algebra.ofId ℚ ℂ) (x : ℚ) _

/-- The rational coefficient of `p(λ)` in the equation `Q(s, α'^s; t) = 0`. -/
noncomputable def coefRat {n r : ℕ} (b : Fin n → ℤ) (k : Fin n) (L : Fin r → Fin n → ℤ)
    (ι : Fin (r - 1) → Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (s : ℤ) (lm : AuxIdx r h D0 Dj) : ℚ :=
  (∏ m, deltaRat (gamInt b k L (ι m) fun i => (lm.2.2 i : ℕ)) (t m)) * (ulcm h : ℚ) ^ t0 *
    thetaRat (s + (lm.1 : ℤ)) h ((lm.2.1 : ℕ) + 1) t0

/-- The coefficient of `p(λ)` in the equation `Q(s, α'^s; t) = 0`, as an element of `ℚ(α')`. -/
noncomputable def coefF {K : Type*} [Field K] [Algebra ℚ K] {n r : ℕ} (b : Fin n → ℤ)
    (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (α' : Fin r → K)
    (h D0 : ℕ) (Dj : Fin r → ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ) (s : ℤ)
    (lm : AuxIdx r h D0 Dj) : auxField α' :=
  (coefRat b k L ι h D0 Dj t0 t s lm : auxField α') *
    ∏ j, alphaF α' j ^ (s * ((lm.2.2 j : ℕ) : ℤ))

/-- The set of multi-indices `t` with `t₀ + ∑ t ≤ T`. -/
abbrev MultIdx (r T : ℕ) : Type := {v : ℕ × (Fin (r - 1) → ℕ) // v.1 + ∑ m, v.2 m ≤ T}

noncomputable instance instFintypeMultIdx (r T : ℕ) : Fintype (MultIdx r T) :=
  Set.Finite.fintype <| Set.Finite.subset
    (Finset.finite_toSet ((Finset.range (T + 1)).product
      (Fintype.piFinset fun _ : Fin (r - 1) => Finset.range (T + 1))))
    (fun v hv => by
      have hsum : ∑ m, v.2 m ≤ T := le_trans (Nat.le_add_left _ _) hv
      have h0 : v.1 ≤ T := le_trans (Nat.le_add_right _ _) hv
      exact Finset.mem_coe.mpr (Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le h0),
         Fintype.mem_piFinset.mpr fun m => Finset.mem_range.mpr (Nat.lt_succ_of_le <|
           le_trans (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ m)) hsum)⟩))

/-- The index set of the equations of the system: `|s| ≤ S` and `t₀ + ∑ t ≤ T`. -/
abbrev AuxEqnIdx (r S T : ℕ) : Type := {s : ℤ // s ∈ Finset.Icc (-(S : ℤ)) S} × MultIdx r T

/-- The row of the linear system corresponding to the equation `e = (s,t)`. -/
noncomputable def sysRow {K : Type*} [Field K] [Algebra ℚ K] {n r : ℕ} (b : Fin n → ℤ)
    (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (α' : Fin r → K)
    (h D0 : ℕ) (Dj : Fin r → ℕ) {S T : ℕ} (e : AuxEqnIdx r S T) (lm : AuxIdx r h D0 Dj) :
    auxField α' :=
  coefF b k L ι α' h D0 Dj e.2.1.1 e.2.1.2 (e.1 : ℤ) lm

end Work.BW
