import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Psi
import Submission.Work.HP.IntForm
import Submission.Work.HP.PFDefs

/-!
# Definitions for the Möbius/lattice-point count in the product-factors bound (node N13)

This file only contains *definitions* (and one tiny lemma about `bigW`), so that the lemmas
delegated for the product-factors bound can import a stable, sorry-free module.

Notation (matching `Submission/Work/HP/PF_PLAN.md` §4): for a primitive coefficient vector `a`,
`B` a height bound, `W = bigW (wOf B)`, `α = log B`, `R = B^{1/(n+1-d)}`,

* `classPrimSet d n a b W α R` — the primitive `v : ℤ^{n+1}` in the coset `b mod W`, with
  `‖v‖ ≤ R`, lying in the cone region (`a ∈ 𝒞_{ν(v)}^{(α)}`).  This is the per-residue-class set
  whose cardinality Möbius inversion computes.
* `mobiusCount d n a b W k α R` — the `k`-th Möbius summand: the number of nonzero `z : ℤ^{n+1}`
  with `k z ≡ b (mod W)`, `‖z‖ ≤ R/k`, `z` in the cone region.
* `TubeOk d n a α T Wr` — the hypothesis of `grid_coset_lower`: the tube around the frontier of
  the cone region of radius `T`, at radius `8 (n+1) Wr`, has volume at most half of the region.
-/

set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Finset
open scoped BigOperators Pointwise

namespace Work.HP

/-- The primitive vectors of the coset `b mod W` of norm at most `R`, lying in the cone region
`{x : a ∈ 𝒞_{ν(x)}^{(α)}}`. -/
def classPrimSet (d n : ℕ) (a : Mon d n → ℤ) (b : Fin (n + 1) → ℤ) (W : ℕ) (α R : ℝ) :
    Set (Fin (n + 1) → ℤ) :=
  {v | IsPrim v ∧ eNorm v ≤ R ∧ (∀ i, (W : ℤ) ∣ v i - b i) ∧
    toR a ∈ Cgam (toR (veronese d n v)) α}

/-- The `k`-th Möbius summand of the count of `classPrimSet`: the number of nonzero `z` with
`k z ≡ b (mod W)`, `‖z‖ ≤ R/k`, `z` in the cone region. -/
def mobiusCount (d n : ℕ) (a : Mon d n → ℤ) (b : Fin (n + 1) → ℤ) (W : ℕ) (k : ℕ) (α R : ℝ) :
    ℕ :=
  {z : Fin (n + 1) → ℤ | z ≠ 0 ∧ (∀ i, (W : ℤ) ∣ (k : ℤ) * z i - b i) ∧
    eNorm z ≤ R / (k : ℝ) ∧ toR a ∈ Cgam (toR (veronese d n z)) α}.ncard

/-- The tube condition of `grid_coset_lower`: the `8(n+1)Wr`-neighbourhood of the frontier of the
cone region of radius `T` has volume at most half the volume of the region. -/
def TubeOk (d n : ℕ) (a : Mon d n → ℤ) (α T Wr : ℝ) : Prop :=
  (volume {x : Fin (n + 1) → ℝ | ∃ y ∈ frontier (coneRegion d n a α T),
      rNorm (x - y) ≤ 8 * ((n : ℝ) + 1) * Wr}).toReal
    ≤ (1 / 2) * (volume (coneRegion d n a α T)).toReal

/-- A prime at most `w` divides `bigW w`. -/
lemma prime_dvd_bigW {p : ℕ} (hp : p.Prime) {w : ℝ} (hw : (p : ℝ) ≤ w) : p ∣ bigW w := by
  have hmem : p ∈ (Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor hw), hp⟩
  have h1 : p ^ rOf p w ∣ ∏ q ∈ (Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime, q ^ rOf q w :=
    Finset.dvd_prod_of_mem (fun q => q ^ rOf q w) hmem
  exact dvd_trans (dvd_pow_self p ((by rw [rOf]; exact Nat.succ_ne_zero _))) h1

end Work.HP
