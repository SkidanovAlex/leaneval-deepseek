import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDCommon
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.Lat.span_pair_lattice
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.PairsAux

/-!
# Case F of the large-`μ` part of the second moment

This file fixes the set over which the "case F" estimate of the paper
(Browning--Le Boudec--Sawin, *The Hasse principle for random Fano hypersurfaces*, Annals 2023,
proof of Lemma D, the quantity `𝓕_{d,n}(A,B)`) is summed, together with two elementary
consequences.

Recall
* `Omega d n B = {(x,y) : x,y ∈ Xi d n B, x ≠ y, x ≠ -y}`,
* `muXY n x y = 3n² max(𝔡₂/𝔡₃, ‖x‖‖y‖/𝔡₂²)` with `𝔡_r = dmin r {x,y}`.

"Case F" is the branch of the maximum in which `𝔡₂/𝔡₃ ≤ ‖x‖‖y‖/𝔡₂²`, i.e.
`𝔡₂³ ≤ 𝔡₃ ‖x‖‖y‖`.  The complementary case is `caseI`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.HP.Sig2

open Work.HP
open MvPolynomial Finset

/-- The set of pairs of `Ω_{d,n}(B)` lying in "case F" of the `μ`-dichotomy: `μ(x,y) > A` and
`𝔡₂(x,y)³ ≤ 𝔡₃(x,y) ‖x‖‖y‖`. -/
def caseFset (d n : ℕ) (A B : ℝ) : Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
  {p | p ∈ Omega d n B ∧ ¬ (muXY n p.1 p.2 ≤ A) ∧
    dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ 2
      ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * (eNorm p.1 * eNorm p.2)}

lemma caseFset_subset (d n : ℕ) (A B : ℝ) : caseFset d n A B ⊆ Omega d n B :=
  fun p hp => hp.1

lemma caseFset_finite (d n : ℕ) (A B : ℝ) : (caseFset d n A B).Finite :=
  ((MDBasic.finite_sets d n A B (fun _ => True)).2.2).subset (caseFset_subset d n A B)

/-- `1 ≤ 𝔡₂(x,y)`: every rank-`2` sublattice of `ℤ^ι` has covolume at least one. -/
lemma one_le_dmin_two {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ι → ℤ)
    (h : LinearIndependent ℤ ![x, y]) : 1 ≤ dmin 2 ({x, y} : Set (ι → ℤ)) := by
  obtain ⟨L, hLrk, hxL, hyL, -⟩ := Lat.span_pair_lattice x y h
  have hsub : ({x, y} : Set (ι → ℤ)) ⊆ L := by
    rintro z (rfl | rfl)
    · exact hxL
    · exact hyL
  rw [Work.HP.dmin]
  refine le_csInf ⟨Work.HP.detL L, L, hLrk, hsub, rfl⟩ ?_
  rintro D ⟨L', hL'rk, hL'sub, rfl⟩
  exact Lat.detL_ge_one L'

end Work.HP.Sig2
