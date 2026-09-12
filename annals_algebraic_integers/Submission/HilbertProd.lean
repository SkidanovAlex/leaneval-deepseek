import Submission.MinkBox
import Submission.Quantile
import Submission.EnergyHalf
import Mathlib.Tactic

/-!
# Vandermonde product over `Fin d` (relabelled quantile nodes) equals `Vprod d`

Child task: prove `Submission.HilbertProd.pairProd_eq_Vprod` below
(replace the placeholder proof with a real one).  The parent (`Submission/HilbertMink.lean`) needs this exact lemma
to connect the `Fin d`-indexed product from `MinkBox.pairProd` with the
natural-index Vandermonde `EnergyHalf.Vprod` used by `EnergyHalf.energy_half`.

Definitions (all available from the imports above):

    alpha d i            = Quantile.alpha d i        (i-th quantile root)
    pairProd d α         = MinkBox.pairProd d α
                         = ∏ i : Fin d, ∏ j ∈ (univ.filter (fun j : Fin d => i < j)), |α i - α j|
    Vprod d              = EnergyHalf.Vprod d
                         = ∏ i ∈ Finset.Icc 1 d, ∏ j ∈ Finset.Icc (i + 1) d, |alpha d i - alpha d j|

On the left, α is the relabelling `fun k : Fin d => alpha d (k.val + 1)`, so
both sides are products over exactly the pairs `1 ≤ i < j ≤ d` of the same
factors `|alpha d i - alpha d j|` — the equality is pure Finset combinatorics
(no properties of `alpha` are needed beyond the indexing).
-/

noncomputable section
open Polynomial
open scoped Real BigOperators

namespace Submission.HilbertProd

open Submission.MinkBox
open Submission.Quantile
open Submission.EnergyHalf

/-- Relabel `j : Fin d` with `a ≤ j.val` as the natural index `j.val + 1`
(range `Finset.Icc (a + 1) d`). -/
lemma finprod_leval_eq_Icc_prod (d a : ℕ) (H : ℕ → ℝ) :
    (∏ j ∈ (Finset.univ.filter (fun j : Fin d => a ≤ j.val)), H (j.val + 1))
      = ∏ j ∈ Finset.Icc (a + 1) d, H j := by
  classical
  refine Finset.prod_bij' (s := Finset.univ.filter (fun j : Fin d => a ≤ j.val))
      (t := Finset.Icc (a + 1) d)
      (i := fun j _ => (j.val + 1 : ℕ))
      (j := fun k hk => (⟨k - 1, ?_⟩ : Fin d))
      ?hi ?hj ?left ?right ?h
  · rw [Finset.mem_Icc] at hk
    omega
  · intro j hj
    rw [Finset.mem_Icc]
    rw [Finset.mem_filter] at hj
    constructor <;> omega
  · intro k hk
    rw [Finset.mem_filter]
    rw [Finset.mem_Icc] at hk
    constructor
    · exact Finset.mem_univ _
    · simp
      omega
  · intro j hj
    apply Fin.ext
    simp
  · intro k hk
    rw [Finset.mem_Icc] at hk
    simp
    omega
  · intro j hj
    rfl

/-- The `Fin d`-staircase product (pairs `i < j` in `Fin d`, relabelled by
`+1` on each coordinate) equals the natural-index staircase product
(`1 ≤ i < j ≤ d`).  Pure Finset combinatorics; `F : ℕ → ℕ → ℝ` arbitrary. -/
lemma staircaseFin_eq_staircaseNat (d : ℕ) (F : ℕ → ℕ → ℝ) :
    (∏ i : Fin d, ∏ j ∈ (Finset.univ.filter (fun j : Fin d => i < j)),
      F (i.val + 1) (j.val + 1))
      = (∏ i ∈ Finset.Icc 1 d, ∏ j ∈ Finset.Icc (i + 1) d, F i j) := by
  classical
  refine Finset.prod_bij' (s := (Finset.univ : Finset (Fin d)))
      (t := Finset.Icc 1 d)
      (i := fun (k : Fin d) _ => (k.val + 1 : ℕ))
      (j := fun (a : ℕ) ha => (⟨a - 1, ?_⟩ : Fin d))
      ?hi ?hj ?left ?right ?h
  · -- a - 1 < d for a ∈ Icc 1 d
    rw [Finset.mem_Icc] at ha
    omega
  · -- forward map lands in Icc 1 d
    intro k _
    rw [Finset.mem_Icc]
    constructor <;> omega
  · -- inverse lands in univ
    intro a _
    simp
  · -- left inverse
    intro k _
    apply Fin.ext
    simp
  · -- right inverse
    intro a ha
    rw [Finset.mem_Icc] at ha
    simp
    omega
  · -- term equality: inner reindexing with a := k.val + 1
    intro k _
    have hcond : ∀ j : Fin d, (k < j) ↔ k.val + 1 ≤ j.val := by
      intro j
      rw [Fin.lt_def]
      omega
    have hfilter : Finset.univ.filter (fun j : Fin d => k < j)
        = Finset.univ.filter (fun j : Fin d => k.val + 1 ≤ j.val) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hcond]
    rw [hfilter]
    exact finprod_leval_eq_Icc_prod d (k.val + 1) (fun y => F (k.val + 1) y)

/-- The `Fin d`-relabelled Vandermonde product equals the natural-index one. -/
lemma pairProd_eq_Vprod (d : ℕ) (hd : 1 ≤ d) :
    pairProd d (fun k : Fin d => alpha d (k.val + 1)) = Vprod d := by
  have hd' : 1 ≤ d := hd
  calc
    pairProd d (fun k : Fin d => alpha d (k.val + 1))
        = ∏ i : Fin d, ∏ j ∈ (Finset.univ.filter (fun j : Fin d => i < j)),
            |alpha d (i.val + 1) - alpha d (j.val + 1)| := by
            rfl
    _ = Vprod d := by
            rw [Vprod]
            exact staircaseFin_eq_staircaseNat d (fun i j => |alpha d i - alpha d j|)

end Submission.HilbertProd
