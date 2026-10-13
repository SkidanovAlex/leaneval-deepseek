/-
  WilE7 (`Submission.Work.WilE7.AboveAux.AboveDefs`): the semi-Pfaffian presentation of the
  *above cell* of the top sheet.

  Given a stratum `S : Stratum p (m+1)`, a `SemiPf` set `Z` defining the base cell
  `C = π_p (connectedComponentIn Z.set u₀)` and continuous sheets `s j : C → ℝ^{m+1}`, the
  *above cell* of the sheet `s j` is

    `above j = {y : Fin (p+1) → ℝ | Fin.init y ∈ C ∧
        (s j (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧ y (Fin.last p) ≤ 1}`.

  This is the *top* cell when `j = k-1` is the highest sheet (then the whole cell lies above it);
  it is the mirror image of the below cell of `Work.WilE7.BelowAux` with the vertical direction
  reversed (open lower bound `v₂ < t`, closed upper bound `t ≤ 1`).

  The ambient layout is *identical* to the below cell's: the fibre product `Z ×_{ℝ^p} S.X` with
  one extra vertical coordinate `t`, cut by the single inequality `v₂ < t` (the atom `abovePlow`).
  The closed upper bound `t ≤ 1` is supplied by the cube constraint on the vertical coordinate,
  exactly as `-1 ≤ t` was for the below cell.  Consequently all the coordinate bookkeeping
  (`belowDim`, `belowZ1`, `belowZ2`, `belowT`, `belowV2`, `belowPt`, `belowExtract`, `belowPerm`)
  of `Work.WilE7.BelowAux` is reused verbatim.

  It records

  * the point set (`aboveS_mem_iff`),
  * the format under a coordinate permutation (`aboveS_reindex_fmt`),
  * the canonical point `belowPt u v 1` of the set and its membership (`abovePt_mem`),
  * the region `aboveH` of `(base component) × ℝ` parametrising the cell, with its
    parametrisation `abovePhi` and the identities `abovePhi` satisfies.

  The connected-component argument ("the component through `belowPt u₀ (s (k-1) x₀) 1` projects
  exactly onto the above cell") is `Work.WilE7.AboveAux.aboveComp_sub` and `aboveComp_cov`, the
  assembly is `Submission/Work/WilE7/aboveCell_star_proved`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.fiberProduct_semiPf
import Submission.Work.WilE7.prodSet
import Submission.Work.WilE7.BelowAux.BelowDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.AboveAux
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.BelowAux

/-! ## §1. The single inequality atom `t - v₂ > 0` -/

/-- The atom `t - v₂`, positive exactly when the vertical coordinate is above the sheet. -/
def abovePlow (p m r : ℕ) : EAPoly (belowDim p m) r :=
  MvPolynomial.X (Sum.inl (belowTIdx p m)) - MvPolynomial.X (Sum.inl (belowV2Idx p m))

theorem eaEval_abovePlow {p m r : ℕ} (c : EAChain (belowDim p m) r)
    (w : Fin (belowDim p m) → ℝ) :
    eaEval c (abovePlow p m r) w = belowT w - belowV2 w := by
  simp [abovePlow, eaEval, belowT, belowV2, belowZ2, belowV2Idx, belowTIdx]

theorem atomDeg_abovePlow {p m r : ℕ} : atomDeg (abovePlow p m r) ≤ 2 := by
  have h := MvPolynomial.totalDegree_sub
    (MvPolynomial.X (Sum.inl (belowTIdx p m)) : EAPoly (belowDim p m) r)
    (MvPolynomial.X (Sum.inl (belowV2Idx p m)) : EAPoly (belowDim p m) r)
  rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X] at h
  simp only [atomDeg, abovePlow]
  omega

/-! ## §2. The construction and its point set -/

/-- The fibre product `W = Z ×_{ℝ^p} S.X` (two blocks `z₁`, `z₂`). -/
noncomputable def aboveW1 {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1)) :
    SemiPf (belowK p m) :=
  fiberProdZ (p := p) (q := m + 1) Z S.X

/-- The fibre product with the vertical coordinate appended (the cube in `ℝ¹`). -/
noncomputable def abovePadded {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1)) :
    SemiPf (belowDim p m) :=
  Work.WilE7.SemiPf.prod (aboveW1 Z S) Work.WilE7.bandCube1

/-- The `SemiPf` set of the above cell: the fibre product with the vertical coordinate, cut by
`v₂ < t`.  (The closed upper bound `t ≤ 1` comes from the cube constraint on `t`.) -/
noncomputable def aboveS {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1)) :
    SemiPf (belowDim p m) :=
  Work.WilE7.SemiPf.addConds (abovePadded Z S) []
    [abovePlow p m (abovePadded Z S).r]

theorem abovePadded_eq {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1)) :
    (abovePadded Z S).set = {w : Fin (belowDim p m) → ℝ |
      projFirst (belowK p m) 1 w ∈ (aboveW1 Z S).set ∧
      projSnd (belowK p m) 1 w ∈ cubeC 1} := by
  rw [abovePadded, prodSet, Work.WilE7.bandCube1_set]

theorem aboveW1_eq {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1))
    (u : Fin (belowK p m) → ℝ) :
    u ∈ (aboveW1 Z S).set ↔
      projFirst (p + (m + 1)) (p + (m + 1)) u ∈ Z.set ∧
      projSnd (p + (m + 1)) (p + (m + 1)) u ∈ S.X.set ∧
      projFirst p (m + 1) (projFirst (p + (m + 1)) (p + (m + 1)) u) =
        projFirst p (m + 1) (projSnd (p + (m + 1)) (p + (m + 1)) u) := by
  rw [aboveW1, fiberProdZ_set]
  rfl

/-- **The point set of `aboveS`.**  Membership is: `z₁ ∈ Z.set`, `z₂ ∈ S.X.set` over the same
base as `z₁`, `|t| ≤ 1` and `v₂ < t`. -/
theorem aboveS_mem_iff {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1))
    (w : Fin (belowDim p m) → ℝ) :
    w ∈ (aboveS Z S).set ↔
      belowZ1 w ∈ Z.set ∧ belowZ2 w ∈ S.X.set ∧
      projFirst p (m + 1) (belowZ1 w) = projFirst p (m + 1) (belowZ2 w) ∧
      |belowT w| ≤ 1 ∧ belowV2 w < belowT w := by
  rw [aboveS, Work.WilE7.SemiPf.addConds_set]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, List.not_mem_nil, IsEmpty.forall_iff,
    List.mem_cons, forall_eq_or_imp, forall_const, and_true]
  rw [eaEval_abovePlow]
  rw [abovePadded_eq]
  simp only [Set.mem_ofPred_eq]
  rw [aboveW1_eq]
  rw [belowZ1_projFirst, belowZ2_projSnd]
  rw [belowT_eq, Work.WilE7.mem_cubeC_one]
  simp only [sub_pos]
  tauto

/-- Reindexing `aboveS` along a permutation of the ambient coordinates does not change its
format (the ambient dimension is preserved: `(p+1) + belowFib p m = belowDim p m`). -/
theorem aboveS_reindex_fmt {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1))
    (e : Fin (belowDim p m) ≃ Fin ((p + 1) + belowFib p m)) :
    (Work.WilE7.SemiPf.reindex e (aboveS Z S)).fmt = (aboveS Z S).fmt := by
  simp only [WilkiesDesign.E.SemiPf.fmt, Work.WilE7.SemiPf.reindex, belowFib, belowDim, belowK]
  omega

/-! ## §3. The canonical point -/

/-- The parametrised point `belowPt u v t` lies in `aboveS` whenever its data satisfy the sheet
condition, the cube constraint and the strict inequality `v₂ < t`. -/
theorem abovePt_mem {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1))
    (u : Fin (p + (m + 1)) → ℝ) (hu : u ∈ Z.set) (v : Fin (m + 1) → ℝ) (t : ℝ)
    (hv : Fin.append (projFirst p (m + 1) u) v ∈ S.X.set) (ht : |t| ≤ 1)
    (h : v (Fin.last m) < t) :
    belowPt u v t ∈ (aboveS Z S).set := by
  rw [aboveS_mem_iff]
  exact ⟨by rwa [belowZ1_belowPt], by rwa [belowZ2_belowPt],
    by rw [belowZ1_belowPt, belowZ2_belowPt, projFirst_append],
    by rw [belowT_belowPt]; exact ht,
    by rw [belowT_belowPt, belowV2_belowPt]; exact h⟩

/-! ## §4. The parametrisation of the above cell -/

/-- The region of `(base component) × ℝ` parametrising the above cell: the base point runs over
the component of `Z` through `u₀` and the vertical coordinate over `(level of s j, 1]`. -/
def aboveH {p m k : ℕ} (Z : SemiPf (p + (m + 1)))
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (j : Fin k)
    (u₀ : Fin (p + (m + 1)) → ℝ) : Set ((Fin (p + (m + 1)) → ℝ) × ℝ) :=
  {q | q.1 ∈ connectedComponentIn Z.set u₀ ∧
    (s j (projFirst p (m + 1) q.1)) (Fin.last m) < q.2 ∧ q.2 ≤ 1}

theorem mem_aboveH {p m k : ℕ} {Z : SemiPf (p + (m + 1))}
    {s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)} {j : Fin k}
    {u₀ : Fin (p + (m + 1)) → ℝ} {q : (Fin (p + (m + 1)) → ℝ) × ℝ} :
    q ∈ aboveH Z s j u₀ ↔ q.1 ∈ connectedComponentIn Z.set u₀ ∧
      (s j (projFirst p (m + 1) q.1)) (Fin.last m) < q.2 ∧ q.2 ≤ 1 := Iff.rfl

/-- The parametrisation of the above cell: `(u, t) ↦ belowPt u (s j (π u)) t`. -/
def abovePhi {p m k : ℕ} (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (j : Fin k) :
    ((Fin (p + (m + 1)) → ℝ) × ℝ) → Fin (belowDim p m) → ℝ :=
  fun q => belowPt q.1 (s j (projFirst p (m + 1) q.1)) q.2

theorem belowZ1_abovePhi {p m k : ℕ} (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (j : Fin k) (q : (Fin (p + (m + 1)) → ℝ) × ℝ) :
    belowZ1 (abovePhi s j q) = q.1 :=
  belowZ1_belowPt _ _ _

theorem belowZ2_abovePhi {p m k : ℕ} (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (j : Fin k) (q : (Fin (p + (m + 1)) → ℝ) × ℝ) :
    belowZ2 (abovePhi s j q) =
      Fin.append (projFirst p (m + 1) q.1) (s j (projFirst p (m + 1) q.1)) :=
  belowZ2_belowPt _ _ _

theorem belowT_abovePhi {p m k : ℕ} (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (j : Fin k) (q : (Fin (p + (m + 1)) → ℝ) × ℝ) :
    belowT (abovePhi s j q) = q.2 :=
  belowT_belowPt _ _ _

theorem belowExtract_abovePhi {p m k : ℕ} (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (j : Fin k) (q : (Fin (p + (m + 1)) → ℝ) × ℝ) :
    belowExtract (abovePhi s j q) = Fin.snoc (projFirst p (m + 1) q.1) q.2 :=
  belowExtract_belowPt _ _ _

end Work.WilE7.AboveAux
