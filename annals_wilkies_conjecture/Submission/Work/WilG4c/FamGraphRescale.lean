/-
  WilG4c / FamGraphRescale — the `Ω`-membership of a family's graph after an affine
  rescaling of its variables.

  The target (`Work.WilkG4c.FamGraphRescale`) is the "input rescaling" step of BNZ §5.3:
  replacing a family `f` by `(l, z) ↦ f l (q + z/K)` (a translation by `q` and a diagonal
  scaling by `1/K` of the variables) may only *raise* the format by a constant and the
  degree by `2`.  (No invertibility of the rescaling is assumed: for `K = 0` the map is the
  constant map `z ↦ q`, and Lean's `x / 0 = 0` handles it uniformly.)

  The set identity is `famGraph_resc_eq`: the graph of the rescaled family is the preimage
  of the graph of `f` under the affine map `(l, z, t) ↦ (l, q + z/K, t)`.  The `Ω`-content
  is the general affine pullback lemma `affPullback_mem`, built on the vocabulary of
  `Submission.Work.WilG4c.AffPullDefs` and the two facts proved in the sibling modules
  `Submission.Work.WilG4c.affPullDiag_mem` and `Submission.Work.WilG4c.affPullDiag_proj_eq`.
-/
import Mathlib
import Submission.Work.WilG4c.AffPullDefs
import Submission.Work.WilG4c.affPullDiag_mem
import Submission.Work.WilG4c.affPullDiag_proj_eq
import Submission.Work.WilG0.API
import Submission.Work.WilG0.liftNM_mem
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG4c.Subst

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

section Rescale

variable (p n : ℕ)

/-- The translation vector of the rescaling: `0` on the parameter and value coordinates,
`q` on the variable coordinates. -/
noncomputable def rescC (q : Fin (n + 1) → ℝ) : Fin (p + (n + 1) + 1) → ℝ :=
  fun i => if h : i.val < p + (n + 1) ∧ p ≤ i.val then q ⟨i.val - p, by omega⟩ else 0

/-- The diagonal of the linear part of the rescaling: `1` except on the variable
coordinates, where it is `1/K`. -/
noncomputable def rescS (K : ℕ) : Fin (p + (n + 1) + 1) → ℝ :=
  fun i => if h : i.val < p + (n + 1) ∧ p ≤ i.val then (1 : ℝ) / (K : ℝ) else 1

/-- The matrix of the linear part of the rescaling (diagonal with diagonal `rescS`). -/
noncomputable def rescM (K : ℕ) : Fin (p + (n + 1) + 1) → Fin (p + (n + 1) + 1) → ℝ :=
  fun i j => if i = j then rescS p n K i else 0

/-- The diagonal sum: `Σ_j (if i = j then s i else 0) * x j = s i * x i`. -/
theorem sum_diag_mul {N : ℕ} (s : Fin N → ℝ) (x : Fin N → ℝ) (i : Fin N) :
    (∑ j : Fin N, (if i = j then s i else 0) * x j) = s i * x i := by
  rw [Finset.sum_eq_single i (fun b _ hb => by rw [if_neg (Ne.symm hb), zero_mul])
    (fun hi => absurd (Finset.mem_univ i) hi)]
  rw [if_pos rfl]

/-- `affPullMap (rescC q) (rescM K) x = rescC q + rescS K · x`. -/
theorem affPullMap_resc (q : Fin (n + 1) → ℝ) (K : ℕ) (x : Fin (p + (n + 1) + 1) → ℝ)
    (i : Fin (p + (n + 1) + 1)) :
    affPullMap (rescC p n q) (rescM p n K) x i = rescC p n q i + rescS p n K i * x i := by
  have h : (∑ j : Fin (p + (n + 1) + 1), rescM p n K i j * x j) = rescS p n K i * x i := by
    simp only [rescM]
    exact sum_diag_mul (rescS p n K) x i
  rw [affPullMap_apply, h]

/-- `rescC q` vanishes on the parameter coordinates. -/
theorem rescC_lidx (q : Fin (n + 1) → ℝ) (i : Fin p) :
    rescC p n q (Fin.castSucc (Fin.castAdd (n + 1) i)) = 0 := by
  have h : ¬ ((Fin.castSucc (Fin.castAdd (n + 1) i) : Fin (p + (n + 1) + 1)).val < p + (n + 1)
      ∧ p ≤ (Fin.castSucc (Fin.castAdd (n + 1) i) : Fin (p + (n + 1) + 1)).val) := by
    simp only [Fin.val_castSucc, Fin.val_castAdd]
    omega
  unfold rescC
  rw [dif_neg h]

/-- `rescS K` is `1` on the parameter coordinates. -/
theorem rescS_lidx (K : ℕ) (i : Fin p) :
    rescS p n K (Fin.castSucc (Fin.castAdd (n + 1) i)) = 1 := by
  have h : ¬ ((Fin.castSucc (Fin.castAdd (n + 1) i) : Fin (p + (n + 1) + 1)).val < p + (n + 1)
      ∧ p ≤ (Fin.castSucc (Fin.castAdd (n + 1) i) : Fin (p + (n + 1) + 1)).val) := by
    simp only [Fin.val_castSucc, Fin.val_castAdd]
    omega
  unfold rescS
  rw [dif_neg h]

/-- `rescC q` reads off `q` on the variable coordinates. -/
theorem rescC_yidx (q : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    rescC p n q (Fin.castSucc (Fin.natAdd p j)) = q j := by
  have h : (Fin.castSucc (Fin.natAdd p j) : Fin (p + (n + 1) + 1)).val < p + (n + 1)
      ∧ p ≤ (Fin.castSucc (Fin.natAdd p j) : Fin (p + (n + 1) + 1)).val := by
    simp only [Fin.val_castSucc, Fin.val_natAdd]
    exact ⟨by omega, by omega⟩
  unfold rescC
  rw [dif_pos h]
  congr 1
  exact Fin.ext (by simp only [Fin.val_mk, Fin.val_castSucc, Fin.val_natAdd]; omega)

/-- `rescS K` is `1/K` on the variable coordinates. -/
theorem rescS_yidx (K : ℕ) (j : Fin (n + 1)) :
    rescS p n K (Fin.castSucc (Fin.natAdd p j)) = (1 : ℝ) / (K : ℝ) := by
  have h : (Fin.castSucc (Fin.natAdd p j) : Fin (p + (n + 1) + 1)).val < p + (n + 1)
      ∧ p ≤ (Fin.castSucc (Fin.natAdd p j) : Fin (p + (n + 1) + 1)).val := by
    simp only [Fin.val_castSucc, Fin.val_natAdd]
    exact ⟨by omega, by omega⟩
  unfold rescS
  rw [dif_pos h]

/-- `rescC q` vanishes on the value coordinate. -/
theorem rescC_tidx (q : Fin (n + 1) → ℝ) :
    rescC p n q (Fin.last (p + (n + 1))) = 0 := by
  have h : ¬ ((Fin.last (p + (n + 1)) : Fin (p + (n + 1) + 1)).val < p + (n + 1)
      ∧ p ≤ (Fin.last (p + (n + 1)) : Fin (p + (n + 1) + 1)).val) := by
    simp only [Fin.val_last]
    omega
  unfold rescC
  rw [dif_neg h]

/-- `rescS K` is `1` on the value coordinate. -/
theorem rescS_tidx (K : ℕ) :
    rescS p n K (Fin.last (p + (n + 1))) = 1 := by
  have h : ¬ ((Fin.last (p + (n + 1)) : Fin (p + (n + 1) + 1)).val < p + (n + 1)
      ∧ p ≤ (Fin.last (p + (n + 1)) : Fin (p + (n + 1) + 1)).val) := by
    simp only [Fin.val_last]
    omega
  unfold rescS
  rw [dif_neg h]

/-- The rescaled affine map is the identity on the parameter coordinates. -/
theorem affPullMap_lidx (q : Fin (n + 1) → ℝ) (K : ℕ) (x : Fin (p + (n + 1) + 1) → ℝ)
    (i : Fin p) :
    affPullMap (rescC p n q) (rescM p n K) x (Fin.castSucc (Fin.castAdd (n + 1) i))
      = x (Fin.castSucc (Fin.castAdd (n + 1) i)) := by
  rw [affPullMap_resc, rescC_lidx, rescS_lidx]
  ring

/-- The rescaled affine map acts on the variable coordinates by `q + ·/K`. -/
theorem affPullMap_yidx (q : Fin (n + 1) → ℝ) (K : ℕ) (x : Fin (p + (n + 1) + 1) → ℝ)
    (j : Fin (n + 1)) :
    affPullMap (rescC p n q) (rescM p n K) x (Fin.castSucc (Fin.natAdd p j))
      = q j + x (Fin.castSucc (Fin.natAdd p j)) / (K : ℝ) := by
  rw [affPullMap_resc, rescC_yidx, rescS_yidx, one_div, div_eq_mul_inv]
  ring

/-- The rescaled affine map is the identity on the value coordinate. -/
theorem affPullMap_tidx (q : Fin (n + 1) → ℝ) (K : ℕ) (x : Fin (p + (n + 1) + 1) → ℝ) :
    affPullMap (rescC p n q) (rescM p n K) x (Fin.last (p + (n + 1)))
      = x (Fin.last (p + (n + 1))) := by
  rw [affPullMap_resc, rescC_tidx, rescS_tidx]
  ring

/-- **The set identity**: the graph of the rescaled family is the preimage of the graph of
`f` under the affine map `(l, z, t) ↦ (l, q + z/K, t)`. -/
theorem famGraph_resc_eq (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (q : Fin (n + 1) → ℝ) (K : ℕ) :
    famGraph (fun l z => f l (fun j => q j + z j / (K : ℝ)))
      = {x : Fin (p + (n + 1) + 1) → ℝ |
          affPullMap (rescC p n q) (rescM p n K) x ∈ famGraph f} := by
  ext x
  simp only [famGraph, graphOf, Set.mem_ofPred_eq, Fin.init]
  rw [affPullMap_tidx p n q K x,
    show (fun i : Fin p => affPullMap (rescC p n q) (rescM p n K) x
        (Fin.castSucc (Fin.castAdd (n + 1) i)))
      = (fun i : Fin p => x (Fin.castSucc (Fin.castAdd (n + 1) i)))
      from funext fun i => affPullMap_lidx p n q K x i,
    show (fun j : Fin (n + 1) => affPullMap (rescC p n q) (rescM p n K) x
        (Fin.castSucc (Fin.natAdd p j)))
      = (fun j : Fin (n + 1) => q j + x (Fin.castSucc (Fin.natAdd p j)) / (K : ℝ))
      from funext fun j => affPullMap_yidx p n q K x j]

end Rescale

/-- **The affine pullback lemma**: the preimage of an `Ω F D N`-set under the affine map
`x ↦ c + M·x` is `Ω`, with format raised by a constant (independent of `F`) and degree
raised by `2`. -/
theorem affPullback_mem (S : SOMin) {N F D : ℕ} {X : Set (Fin N → ℝ)}
    (hX : X ∈ S.Ω F D N) (c : Fin N → ℝ) (M : Fin N → Fin N → ℝ) :
    {x : Fin N → ℝ | affPullMap c M x ∈ X} ∈ S.Ω (F + N + N + 1 + N) (D + 2) N := by
  have hLift : Work.WilG0.liftNM N N X ∈ S.Ω (F + N) D (N + N) :=
    Work.WilG0.liftNM_mem (S := S) hX N
  have hDiag : affPullDiag N c M ∈ S.Ω (N + N) 2 (N + N) := Work.WilG4c.affPullDiag_mem S N c M
  have hLift' : Work.WilG0.liftNM N N X ∈ S.Ω (F + N + N) D (N + N) :=
    Work.WilG0.Omega_mono_F (by omega) hLift
  have hDiag' : affPullDiag N c M ∈ S.Ω (F + N + N) 2 (N + N) :=
    Work.WilG0.Omega_mono_F (by omega) hDiag
  have hI : Work.WilG0.liftNM N N X ∩ affPullDiag N c M ∈
      S.Ω (F + N + N + 1) (D + 2) (N + N) :=
    Work.WilG0.Omega_inter2 hLift' hDiag'
  have hP : Work.WilG0.projLastIter N N (Work.WilG0.liftNM N N X ∩ affPullDiag N c M) ∈
      S.Ω (F + N + N + 1 + N) (D + 2) N :=
    Work.WilG4c.projIter_mem (S := S) (n := N) (m := N) hI
  rwa [Work.WilG4c.affPullDiag_proj_eq N c M X] at hP

/-- **Wilkie's conjecture for Pfaffian structures — the input rescaling step**: rescaling
the variables of a family by `z ↦ q + z/K` raises the format by a constant depending only
on `p`, `n` (and on `S`) and the degree by `2`. -/
theorem FamGraphRescale (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ K₀ : ℕ, ∀ (K : ℕ) (q : Fin (n + 1) → ℝ) (F0 D : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      WilkiesDesign.CG.famGraph (fun l z => f l (fun j => q j + z j / (K : ℝ)))
        ∈ S.Ω (F0 + K₀) (D + 2) (p + (n + 1) + 1) := by
  refine ⟨3 * (p + (n + 1) + 1) + 1, ?_⟩
  intro K q F0 D f hf
  rw [famGraph_resc_eq p n f q K]
  exact Work.WilG0.Omega_mono_F (by omega)
    (affPullback_mem (S := S) hf (rescC p n q) (rescM p n K))

end Work.WilkG4c

/-! ## The same statement under the directory's namespace spelling

The area directory is `Submission/Work/WilG4c`, and several files of the area (e.g.
`LipRescale.lean`, which does `open Work.WilG4c`) refer to this lemma as
`Work.WilG4c.FamGraphRescale`.  We expose the *identical* statement under that spelling as
well, as a one-line wrapper around the primary declaration. -/
namespace Work.WilG4c

/-- The input rescaling step, in the `Work.WilG4c` spelling; identical to
`Work.WilkG4c.FamGraphRescale`. -/
theorem FamGraphRescale (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ K₀ : ℕ, ∀ (K : ℕ) (q : Fin (n + 1) → ℝ) (F0 D : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      WilkiesDesign.CG.famGraph (fun l z => f l (fun j => q j + z j / (K : ℝ)))
        ∈ S.Ω (F0 + K₀) (D + 2) (p + (n + 1) + 1) :=
  Work.WilkG4c.FamGraphRescale S p n

end Work.WilG4c
