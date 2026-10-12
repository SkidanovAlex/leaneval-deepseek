import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseFixB2.Polar.polB_symm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Energy.gradeA_support_herm`

FS §6 (`lem:LocMatrices`): the matrix `𝒜_{ij}` of the graded box state is

* **supported** on `iRange nn × iRange nn` (it vanishes as soon as one of the two
  sector indices is outside `[0, n]`), and
* **Hermitian**: `𝒜_{ji} = conj(𝒜_{ij})`.

Likewise the norm profile `ψ_i = ‖1_{n₊=i}Ψ‖/‖Ψ‖` is supported on `iRange nn`
(it vanishes for `i ∉ [0,n]`).

`nn = fsNn v μ n = gradeNn n (fsM v μ) = max (n+1) (gradeMw 𝓜)` contains the whole
sector range `{0,…,n}`, so `iRange nn = [0, nn−1]` contains `[0,n]`; this is the only
arithmetic input.  Hermiticity is the symmetry of the polarised word `polB` (the
`(i,j) ↦ (j,i)` swap of the `if` guard is a reordering of a conjunction, and the value
is unchanged because `polB` is symmetric — `polB_comm` below, an unconditional
version of `Polar.polB_symm` — while the denominator is a product of the two sector
norms), together with the fact that `𝒜` takes **real** values, so `star` acts as the
identity.
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixB2.Energy

open Submission.BoseGases Work.BoseKinLoc Work.BoseBox Work.BoseBoxFix Work.UBB Work.UBBInputs3

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Symmetry of the polarised word, without smoothness hypotheses -/

/-- **The polarised box word is symmetric**, with no smoothness hypothesis (this is
`Polar.polB_symm` with the unused `ContDiff` assumptions dropped): since
`4·polB Φ Ψ = wordB (Φ+Ψ) − wordB (Φ−Ψ)` and `wordB` is even (`PolB.wordB_neg`),
applied to `Φ−Ψ = −(Ψ−Φ)`; the sum `Φ+Ψ = Ψ+Φ` is the same function. -/
lemma polB_comm (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (μ : ℝ) (n : ℕ) (Φ Ψ : X n → ℝ) :
    polB v h μ n Φ Ψ = polB v h μ n Ψ Φ := by
  have key : wordB v h μ n (fun x => Φ x - Ψ x) = wordB v h μ n (fun x => Ψ x - Φ x) := by
    have he : (fun x => Φ x - Ψ x) = (fun x => -(Ψ x - Φ x)) := by
      funext x; ring
    rw [he]
    exact Polar.PolB.wordB_neg v h μ n (fun x => Ψ x - Φ x)
  have hcomm : wordB v h μ n (fun x => Φ x + Ψ x) = wordB v h μ n (fun x => Ψ x + Φ x) := by
    congr 1
    funext x
    ring
  simp only [polB]
  rw [key, hcomm]

/-! ## 2. The real-valued matrix entry `gradeARe` underlying `gradeA` -/

/-- The real number whose image in `ℂ` is `gradeA v h μ n ℓ Φ i j`: same guard, but
with the value kept in `ℝ`. -/
def gradeARe (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (μ : ℝ) (n : ℕ) (ℓ : ℝ)
    (Φ : X n → ℝ) (i j : ℤ) : ℝ :=
  if 0 ≤ i ∧ i ≤ (n : ℤ) ∧ 0 ≤ j ∧ j ≤ (n : ℤ)
      ∧ 0 < normB v μ n (vecZ ℓ Φ i) ∧ 0 < normB v μ n (vecZ ℓ Φ j) then
    polB v h μ n (vecZ ℓ Φ i) (vecZ ℓ Φ j)
      / (Real.sqrt (normB v μ n (vecZ ℓ Φ i)) * Real.sqrt (normB v μ n (vecZ ℓ Φ j)))
  else 0

/-- `gradeA` is the image of `gradeARe` under `ℝ → ℂ`. -/
lemma gradeA_eq_ofReal (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (μ : ℝ) (n : ℕ) (ℓ : ℝ)
    (Φ : X n → ℝ) (i j : ℤ) :
    gradeA v h μ n ℓ Φ i j = ((gradeARe v h μ n ℓ Φ i j : ℝ) : ℂ) := by
  simp only [gradeA, gradeARe]
  by_cases hc : (0 ≤ i ∧ i ≤ (n : ℤ) ∧ 0 ≤ j ∧ j ≤ (n : ℤ)
      ∧ 0 < normB v μ n (vecZ ℓ Φ i) ∧ 0 < normB v μ n (vecZ ℓ Φ j))
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc]
    simp

/-- `gradeARe` is symmetric in its two indices: the guard is a conjunction, hence
invariant under the swap `(i,j) ↦ (j,i)`, and the value is unchanged by the symmetry
of `polB` and the commutativity of the product of the two sector norms. -/
lemma gradeARe_comm (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (μ : ℝ) (n : ℕ) (ℓ : ℝ)
    (Φ : X n → ℝ) (i j : ℤ) :
    gradeARe v h μ n ℓ Φ j i = gradeARe v h μ n ℓ Φ i j := by
  simp only [gradeARe]
  by_cases hc : (0 ≤ i ∧ i ≤ (n : ℤ) ∧ 0 ≤ j ∧ j ≤ (n : ℤ)
      ∧ 0 < normB v μ n (vecZ ℓ Φ i) ∧ 0 < normB v μ n (vecZ ℓ Φ j))
  · have hc' : (0 ≤ j ∧ j ≤ (n : ℤ) ∧ 0 ≤ i ∧ i ≤ (n : ℤ)
        ∧ 0 < normB v μ n (vecZ ℓ Φ j) ∧ 0 < normB v μ n (vecZ ℓ Φ i)) :=
      ⟨hc.2.2.1, hc.2.2.2.1, hc.1, hc.2.1, hc.2.2.2.2.2, hc.2.2.2.2.1⟩
    rw [if_pos hc', if_pos hc, polB_comm]
    ring
  · have hc' : ¬ (0 ≤ j ∧ j ≤ (n : ℤ) ∧ 0 ≤ i ∧ i ≤ (n : ℤ)
        ∧ 0 < normB v μ n (vecZ ℓ Φ j) ∧ 0 < normB v μ n (vecZ ℓ Φ i)) := by
      intro hh
      exact hc ⟨hh.2.2.1, hh.2.2.2.1, hh.1, hh.2.1, hh.2.2.2.2.2, hh.2.2.2.2.1⟩
    rw [if_neg hc', if_neg hc]

/-- `gradeA` vanishes away from its support condition. -/
lemma gradeA_eq_zero_of_not (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (μ : ℝ) (n : ℕ) (ℓ : ℝ)
    (Φ : X n → ℝ) (i j : ℤ)
    (hc : ¬ (0 ≤ i ∧ i ≤ (n : ℤ) ∧ 0 ≤ j ∧ j ≤ (n : ℤ)
      ∧ 0 < normB v μ n (vecZ ℓ Φ i) ∧ 0 < normB v μ n (vecZ ℓ Φ j))) :
    gradeA v h μ n ℓ Φ i j = 0 := by
  simp only [gradeA]
  rw [if_neg hc]

/-- `gradePsi` vanishes outside `[0,n]`. -/
lemma gradePsi_eq_zero_of_not (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (μ : ℝ) (n : ℕ) (ℓ : ℝ)
    (Φ : X n → ℝ) (j : ℤ) (hc : ¬ (0 ≤ j ∧ j ≤ (n : ℤ))) :
    gradePsi v h μ n ℓ Φ j = 0 := by
  simp only [gradePsi]
  rw [if_neg hc]

/-! ## 3. The index range -/

/-- Every integer in the sector range `[0,n]` lies in `iRange m` as soon as `n+1 ≤ m`
(`iRange m = [0, m−1]`). -/
lemma mem_iRange_of_le {m n : ℕ} (hn : n + 1 ≤ m) {i : ℤ} (h0 : 0 ≤ i)
    (hi : i ≤ (n : ℤ)) : i ∈ iRange m := by
  rw [iRange, Finset.mem_Icc]
  refine ⟨h0, ?_⟩
  have hm : (n : ℤ) + 1 ≤ (m : ℤ) := by
    have hcast : ((n + 1 : ℕ) : ℤ) ≤ ((m : ℕ) : ℤ) := by exact_mod_cast hn
    simpa using hcast
  linarith

/-! ## 4. The support/Hermiticity statement -/

theorem gradeA_support_herm {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hℓ : 0 < Work.BoseFixB2.fsSide v μ) : (∀ i j : ℤ, Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ i j ≠ 0 → i ∈ Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n) ∧ j ∈ Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n)) ∧ (∀ i j : ℤ, Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ j i = star (Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ i j)) ∧ (∀ j : ℤ, Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ j ≠ 0 → j ∈ Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n)) := by
  -- `n + 1 ≤ fsNn v μ n`, so `iRange (fsNn v μ n)` contains the whole sector range.
  have hnn : n + 1 ≤ fsNn v μ n := by
    rw [fsNn]
    exact succ_le_gradeNn n
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    by_cases hc : (0 ≤ i ∧ i ≤ (n : ℤ) ∧ 0 ≤ j ∧ j ≤ (n : ℤ)
        ∧ 0 < normB v μ n (vecZ (fsSide v μ) Φ i)
        ∧ 0 < normB v μ n (vecZ (fsSide v μ) Φ j))
    · exact ⟨mem_iRange_of_le hnn hc.1 hc.2.1,
             mem_iRange_of_le hnn hc.2.2.1 hc.2.2.2.1⟩
    · exact absurd (gradeA_eq_zero_of_not v h μ n (fsSide v μ) Φ i j hc) hij
  · intro i j
    rw [gradeA_eq_ofReal v h μ n (fsSide v μ) Φ j i,
        gradeA_eq_ofReal v h μ n (fsSide v μ) Φ i j,
        gradeARe_comm v h μ n (fsSide v μ) Φ i j]
    simp
  · intro j hj
    by_cases hc : (0 ≤ j ∧ j ≤ (n : ℤ))
    · exact mem_iRange_of_le hnn hc.1 hc.2
    · exact absurd (gradePsi_eq_zero_of_not v h μ n (fsSide v μ) Φ j hc) hj

end Work.BoseFixB2.Energy
