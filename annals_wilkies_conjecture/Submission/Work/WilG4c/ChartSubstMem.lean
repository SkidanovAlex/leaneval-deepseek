import Mathlib
import Submission.Work.WilG4c.FamGraphRescale
import Submission.Work.WilG4c.EngineDefs

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-!
  ## Affine reparametrisation of an `Ω`-definable family

  The reparametrisation `y ↦ (v + y)/lam` of the *value* variables of a family is the
  affine self-map `y ↦ v/lam + (1/lam)·y` of the variable block.  On the full ambient space
  `ℝ^{p+N+1}` (parameters `l`, variables `y`, value `t`) it is the affine map with

  * zero translation on the parameter and value coordinates and `v/lam` on the variables;
  * diagonal linear part `1` on the parameter and value coordinates and `1/lam` on the
    variables.

  The set identity `famGraph_csub_eq` below expresses the graph of the reparametrised
  family as the preimage of the graph of `f` under that affine map, so the general affine
  pullback lemma `affPullback_mem` (proved in `FamGraphRescale`) yields the `Ω`-membership,
  with format gain `3 * (p + N + 1) + 1` and degree gain `2`.  No invertibility of the
  rescaling is needed: the affine pullback is valid for an arbitrary matrix and translation.
-/

section Aux

variable (p N : ℕ)

/-- Translation vector of the chart substitution on `ℝ^{p+N+1}`: `0` on the parameter and
value coordinates, `q` on the variable coordinates. -/
noncomputable def csubC (q : Fin N → ℝ) : Fin (p + N + 1) → ℝ :=
  fun i => if h : p ≤ i.val ∧ i.val < p + N then q ⟨i.val - p, by omega⟩ else 0

/-- Diagonal of the linear part: `1` on the parameter and value coordinates, `s` on the
variable coordinates. -/
noncomputable def csubS (s : ℝ) : Fin (p + N + 1) → ℝ :=
  fun i => if _ : p ≤ i.val ∧ i.val < p + N then s else 1

/-- The diagonal matrix with diagonal `csubS`. -/
noncomputable def csubM (s : ℝ) : Fin (p + N + 1) → Fin (p + N + 1) → ℝ :=
  fun i j => if i = j then csubS p N s i else 0

/-- `csubC` vanishes on the parameter coordinates. -/
theorem csubC_lidx (q : Fin N → ℝ) (i : Fin p) :
    csubC p N q (Fin.castSucc (Fin.castAdd N i)) = 0 := by
  unfold csubC
  have h : ¬ (p ≤ (Fin.castSucc (Fin.castAdd N i) : Fin (p + N + 1)).val ∧
      (Fin.castSucc (Fin.castAdd N i) : Fin (p + N + 1)).val < p + N) := by
    simp only [Fin.val_castSucc, Fin.val_castAdd]; omega
  rw [dif_neg h]

/-- `csubS` is `1` on the parameter coordinates. -/
theorem csubS_lidx (s : ℝ) (i : Fin p) :
    csubS p N s (Fin.castSucc (Fin.castAdd N i)) = 1 := by
  unfold csubS
  have h : ¬ (p ≤ (Fin.castSucc (Fin.castAdd N i) : Fin (p + N + 1)).val ∧
      (Fin.castSucc (Fin.castAdd N i) : Fin (p + N + 1)).val < p + N) := by
    simp only [Fin.val_castSucc, Fin.val_castAdd]; omega
  rw [dif_neg h]

/-- `csubC` reads off `q` on the variable coordinates. -/
theorem csubC_yidx (q : Fin N → ℝ) (j : Fin N) :
    csubC p N q (Fin.castSucc (Fin.natAdd p j)) = q j := by
  unfold csubC
  have h : p ≤ (Fin.castSucc (Fin.natAdd p j) : Fin (p + N + 1)).val ∧
      (Fin.castSucc (Fin.natAdd p j) : Fin (p + N + 1)).val < p + N := by
    simp only [Fin.val_castSucc, Fin.val_natAdd]; omega
  rw [dif_pos h]
  congr 1
  exact Fin.ext (by simp only [Fin.val_castSucc, Fin.val_natAdd]; omega)

/-- `csubS` is `s` on the variable coordinates. -/
theorem csubS_yidx (s : ℝ) (j : Fin N) :
    csubS p N s (Fin.castSucc (Fin.natAdd p j)) = s := by
  unfold csubS
  have h : p ≤ (Fin.castSucc (Fin.natAdd p j) : Fin (p + N + 1)).val ∧
      (Fin.castSucc (Fin.natAdd p j) : Fin (p + N + 1)).val < p + N := by
    simp only [Fin.val_castSucc, Fin.val_natAdd]; omega
  rw [dif_pos h]

/-- `csubC` vanishes on the value coordinate. -/
theorem csubC_tidx (q : Fin N → ℝ) : csubC p N q (Fin.last (p + N)) = 0 := by
  unfold csubC
  have h : ¬ (p ≤ (Fin.last (p + N) : Fin (p + N + 1)).val ∧
      (Fin.last (p + N) : Fin (p + N + 1)).val < p + N) := by
    simp only [Fin.val_last]; omega
  rw [dif_neg h]

/-- `csubS` is `1` on the value coordinate. -/
theorem csubS_tidx (s : ℝ) : csubS p N s (Fin.last (p + N)) = 1 := by
  unfold csubS
  have h : ¬ (p ≤ (Fin.last (p + N) : Fin (p + N + 1)).val ∧
      (Fin.last (p + N) : Fin (p + N + 1)).val < p + N) := by
    simp only [Fin.val_last]; omega
  rw [dif_neg h]

/-- The affine map is `csubC q + csubS s · x` (diagonal linear part). -/
theorem affPullMap_csub (q : Fin N → ℝ) (s : ℝ) (x : Fin (p + N + 1) → ℝ)
    (i : Fin (p + N + 1)) :
    affPullMap (csubC p N q) (csubM p N s) x i = csubC p N q i + csubS p N s i * x i := by
  have h : (∑ j : Fin (p + N + 1), csubM p N s i j * x j) = csubS p N s i * x i := by
    simp only [csubM]
    exact sum_diag_mul (csubS p N s) x i
  rw [affPullMap_apply, h]

/-- The affine map is the identity on the parameter coordinates. -/
theorem affPullMap_csub_lidx (q : Fin N → ℝ) (s : ℝ) (x : Fin (p + N + 1) → ℝ)
    (i : Fin p) :
    affPullMap (csubC p N q) (csubM p N s) x (Fin.castSucc (Fin.castAdd N i))
      = x (Fin.castSucc (Fin.castAdd N i)) := by
  rw [affPullMap_csub, csubC_lidx, csubS_lidx]; ring

/-- The affine map acts on the variable coordinates by `q + s · (·)`. -/
theorem affPullMap_csub_yidx (q : Fin N → ℝ) (s : ℝ) (x : Fin (p + N + 1) → ℝ)
    (j : Fin N) :
    affPullMap (csubC p N q) (csubM p N s) x (Fin.castSucc (Fin.natAdd p j))
      = q j + s * x (Fin.castSucc (Fin.natAdd p j)) := by
  rw [affPullMap_csub, csubC_yidx, csubS_yidx]

/-- The affine map is the identity on the value coordinate. -/
theorem affPullMap_csub_tidx (q : Fin N → ℝ) (s : ℝ) (x : Fin (p + N + 1) → ℝ) :
    affPullMap (csubC p N q) (csubM p N s) x (Fin.last (p + N)) = x (Fin.last (p + N)) := by
  rw [affPullMap_csub, csubC_tidx, csubS_tidx]; ring

/-- **The set identity**: the graph of `(l, y) ↦ f l (q + s · y)` is the preimage of the
graph of `f` under the affine map `x ↦ csubC q + csubS s · x`. -/
theorem famGraph_csub_eq (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ) (q : Fin N → ℝ) (s : ℝ) :
    famGraph (fun (l : Fin p → ℝ) (y : Fin N → ℝ) => f l (fun j => q j + s * y j))
      = {x : Fin (p + N + 1) → ℝ | affPullMap (csubC p N q) (csubM p N s) x ∈ famGraph f} := by
  ext x
  simp only [famGraph, graphOf, Set.mem_ofPred_eq, Fin.init]
  rw [affPullMap_csub_tidx p N q s x,
    show (fun i : Fin p => affPullMap (csubC p N q) (csubM p N s) x
        (Fin.castSucc (Fin.castAdd N i)))
      = (fun i : Fin p => x (Fin.castSucc (Fin.castAdd N i)))
      from funext fun i => affPullMap_csub_lidx p N q s x i,
    show (fun j : Fin N => affPullMap (csubC p N q) (csubM p N s) x
        (Fin.castSucc (Fin.natAdd p j)))
      = (fun j : Fin N => q j + s * x (Fin.castSucc (Fin.natAdd p j)))
      from funext fun j => affPullMap_csub_yidx p N q s x j]

end Aux

/-- **Affine reparametrisation of an `Ω`-definable family.**  If `f` has an `Ω`-bounded graph,
then so has the reparametrised family `(l, y) ↦ f l ((v + y)/lam)`, with a format gain
depending only on the dimension and a degree gain of a constant. -/
theorem ChartSubstMem (S : SOMin) (p N : ℕ) : ∃ (A C : ℕ),
    ∀ (F0 D : ℕ) (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ) (v : Fin N → ℝ) (lam : ℝ),
      famGraph f ∈ S.Ω F0 D (p + N + 1) →
      famGraph (fun (l : Fin p → ℝ) (y : Fin N → ℝ) =>
        f l (fun i => (v i + y i) / lam)) ∈ S.Ω (F0 + A) (D + C) (p + N + 1) := by
  refine ⟨(p + N + 1) + (p + N + 1) + 1 + (p + N + 1), 2, ?_⟩
  intro F0 D f v lam hf
  -- `(v i + y i)/lam = v i/lam + (1/lam) * y i`, so the reparametrisation is the affine
  -- substitution `q = v/lam`, `s = 1/lam`.
  have hfun : (fun (l : Fin p → ℝ) (y : Fin N → ℝ) => f l (fun i => (v i + y i) / lam))
      = (fun (l : Fin p → ℝ) (y : Fin N → ℝ) =>
          f l (fun i => v i / lam + (1 / lam) * y i)) := by
    funext l y
    congr 1
    funext i
    rw [add_div, one_div, div_eq_mul_inv]
    ring
  rw [hfun, famGraph_csub_eq p N f (fun i => v i / lam) (1 / lam)]
  have h := affPullback_mem (S := S) hf (csubC p N (fun i => v i / lam)) (csubM p N (1 / lam))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

end Work.WilkG4c
