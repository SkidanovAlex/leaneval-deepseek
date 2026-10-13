/-
  WilE7 (`Submission.Work.WilE7.BelowAux.BelowDefs`): the semi-Pfaffian presentation of the
  *below cell* of a sheet.

  Given a stratum `S : Stratum p (m+1)`, a `SemiPf` set `Z` defining the base cell
  `C = π_p (connectedComponentIn Z.set u₀)` and continuous sheets `s j : C → ℝ^{m+1}`, the
  *below cell* of the sheet `s j` is

    `below j = {y : Fin (p+1) → ℝ | Fin.init y ∈ C ∧ -1 ≤ y (Fin.last p) ∧
        y (Fin.last p) < (s j (Fin.init y)) (Fin.last m)}`.

  The paper's cell decomposition needs this region (the vertical section below the lowest sheet)
  to be a `Star`-set and a sub-Pfaffian set.  This file builds the underlying semi-Pfaffian set

    `belowS Z S : SemiPf (belowDim p m)`

  — the fibre product `Z ×_{ℝ^p} S.X` with one extra vertical coordinate `t`, cut by the single
  inequality `t < v₂` (the `pos`-atom `belowPhigh`); the *closed* lower bound `-1 ≤ t` is supplied
  by the cube constraint on the vertical coordinate, exactly as in `bandS3`.

  It records

  * the point set (`belowS_mem_iff`),
  * the extraction map `belowExtract` (`base, t`) and the coordinate permutation `belowPerm`
    identifying it with `projFirst`,
  * the canonical point `belowPt` of the set and its membership, and
  * the region `belowH` of `(base component) × ℝ` which parametrises the cell, together with its
    parametrisation `belowPhi`.

  The connected-component argument ("the component through `belowPt u₀ (s j x₀) (-1)` projects
  exactly onto the below cell") is left to `Submission/Work/WilE7/BelowAux/belowComponent`, and
  the assembly to `Submission/Work/WilE7/belowCell_star_proved`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.fiberProduct_semiPf
import Submission.Work.WilE7.prodSet
import Submission.Work.WilE7.BandAux.BandDefs
import Submission.Work.WilE7.sheetDomain_open

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.BelowAux
open WilkiesDesign WilkiesDesign.E

/-! ## §1. The ambient dimensions and the coordinate indices -/

/-- The ambient dimension of the fibre product `Z ×_{ℝ^p} S.X` (two blocks of `p + (m+1)`
coordinates). -/
abbrev belowK (p m : ℕ) : ℕ := (p + (m + 1)) + (p + (m + 1))

/-- The ambient dimension of `belowS` (the fibre product plus the vertical coordinate). -/
abbrev belowDim (p m : ℕ) : ℕ := belowK p m + 1

/-- The fibre dimension of the `*`-piece: everything except the base and the vertical
coordinate. -/
abbrev belowFib (p m : ℕ) : ℕ := belowDim p m - (p + 1)

/-- Index of the `i`-th coordinate of the first block `z₁`. -/
def belowZ1Idx (p m : ℕ) (i : Fin (p + (m + 1))) : Fin (belowDim p m) :=
  Fin.castAdd 1 (Fin.castAdd (p + (m + 1)) i)

/-- Index of the `i`-th coordinate of the second block `z₂`. -/
def belowZ2Idx (p m : ℕ) (i : Fin (p + (m + 1))) : Fin (belowDim p m) :=
  Fin.castAdd 1 (Fin.natAdd (p + (m + 1)) i)

/-- Index of the vertical coordinate. -/
def belowTIdx (p m : ℕ) : Fin (belowDim p m) := Fin.last (belowK p m)

/-- Index of the vertical (last) coordinate of the second block, i.e. of the sheet level. -/
def belowV2Idx (p m : ℕ) : Fin (belowDim p m) := belowZ2Idx p m (Fin.natAdd p (Fin.last m))

/-- The first block of `w`. -/
def belowZ1 {p m : ℕ} (w : Fin (belowDim p m) → ℝ) : Fin (p + (m + 1)) → ℝ :=
  fun i => w (belowZ1Idx p m i)

/-- The second block of `w` (the point of the stratum). -/
def belowZ2 {p m : ℕ} (w : Fin (belowDim p m) → ℝ) : Fin (p + (m + 1)) → ℝ :=
  fun i => w (belowZ2Idx p m i)

/-- The vertical coordinate of `w`. -/
def belowT {p m : ℕ} (w : Fin (belowDim p m) → ℝ) : ℝ := w (belowTIdx p m)

/-- The level of the sheet, i.e. the last coordinate of the second block. -/
def belowV2 {p m : ℕ} (w : Fin (belowDim p m) → ℝ) : ℝ :=
  (belowZ2 w) (Fin.natAdd p (Fin.last m))

theorem belowT_apply {p m : ℕ} (w : Fin (belowDim p m) → ℝ) : w (belowTIdx p m) = belowT w := rfl

theorem belowV2_apply {p m : ℕ} (w : Fin (belowDim p m) → ℝ) :
    w (belowV2Idx p m) = belowV2 w := rfl

theorem belowT_eq {p m : ℕ} (w : Fin (belowDim p m) → ℝ) :
    belowT w = (projSnd (belowK p m) 1 w) 0 := by
  show w (Fin.last (belowK p m)) = w (Fin.natAdd (belowK p m) 0)
  exact congrArg w (Fin.ext (by simp [Fin.val_natAdd, Fin.val_last]))

theorem belowZ1_projFirst {p m : ℕ} (w : Fin (belowDim p m) → ℝ) :
    belowZ1 w = projFirst (p + (m + 1)) (p + (m + 1)) (projFirst (belowK p m) 1 w) := rfl

theorem belowZ2_projSnd {p m : ℕ} (w : Fin (belowDim p m) → ℝ) :
    belowZ2 w = projSnd (p + (m + 1)) (p + (m + 1)) (projFirst (belowK p m) 1 w) := rfl

/-! ## §2. Continuity of the coordinate maps -/

theorem continuous_belowZ1 {p m : ℕ} : Continuous (belowZ1 (p := p) (m := m)) :=
  continuous_pi fun i => continuous_apply (belowZ1Idx p m i)

theorem continuous_belowZ2 {p m : ℕ} : Continuous (belowZ2 (p := p) (m := m)) :=
  continuous_pi fun i => continuous_apply (belowZ2Idx p m i)

theorem continuous_belowT {p m : ℕ} : Continuous (belowT (p := p) (m := m)) :=
  continuous_apply (belowTIdx p m)

/-! ## §3. The single inequality atom `v₂ - t > 0` -/

/-- The atom `v₂ - t`, positive exactly when the vertical coordinate is below the sheet. -/
def belowPhigh (p m r : ℕ) : EAPoly (belowDim p m) r :=
  MvPolynomial.X (Sum.inl (belowV2Idx p m)) - MvPolynomial.X (Sum.inl (belowTIdx p m))

theorem eaEval_belowPhigh {p m r : ℕ} (c : EAChain (belowDim p m) r)
    (w : Fin (belowDim p m) → ℝ) :
    eaEval c (belowPhigh p m r) w = belowV2 w - belowT w := by
  simp [belowPhigh, eaEval, belowT, belowV2, belowZ2, belowV2Idx, belowTIdx]

theorem atomDeg_belowPhigh {p m r : ℕ} : atomDeg (belowPhigh p m r) ≤ 2 := by
  have h := MvPolynomial.totalDegree_sub
    (MvPolynomial.X (Sum.inl (belowV2Idx p m)) : EAPoly (belowDim p m) r)
    (MvPolynomial.X (Sum.inl (belowTIdx p m)) : EAPoly (belowDim p m) r)
  rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X] at h
  simp only [atomDeg, belowPhigh]
  omega

/-! ## §4. The construction and its point set -/

/-- The fibre product `W = Z ×_{ℝ^p} S.X` (two blocks `z₁`, `z₂`). -/
noncomputable def belowW1 {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1)) :
    SemiPf (belowK p m) :=
  fiberProdZ (p := p) (q := m + 1) Z S.X

/-- The fibre product with the vertical coordinate appended (the cube in `ℝ¹`). -/
noncomputable def belowPadded {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1)) :
    SemiPf (belowDim p m) :=
  Work.WilE7.SemiPf.prod (belowW1 Z S) Work.WilE7.bandCube1

/-- The `SemiPf` set of the below cell: the fibre product with the vertical coordinate, cut by
`t < v₂`.  (The closed lower bound `-1 ≤ t` comes from the cube constraint on `t`.) -/
noncomputable def belowS {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1)) :
    SemiPf (belowDim p m) :=
  Work.WilE7.SemiPf.addConds (belowPadded Z S) []
    [belowPhigh p m (belowPadded Z S).r]

theorem belowPadded_eq {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1)) :
    (belowPadded Z S).set = {w : Fin (belowDim p m) → ℝ |
      projFirst (belowK p m) 1 w ∈ (belowW1 Z S).set ∧
      projSnd (belowK p m) 1 w ∈ cubeC 1} := by
  rw [belowPadded, prodSet, Work.WilE7.bandCube1_set]

theorem belowW1_eq {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1))
    (u : Fin (belowK p m) → ℝ) :
    u ∈ (belowW1 Z S).set ↔
      projFirst (p + (m + 1)) (p + (m + 1)) u ∈ Z.set ∧
      projSnd (p + (m + 1)) (p + (m + 1)) u ∈ S.X.set ∧
      projFirst p (m + 1) (projFirst (p + (m + 1)) (p + (m + 1)) u) =
        projFirst p (m + 1) (projSnd (p + (m + 1)) (p + (m + 1)) u) := by
  rw [belowW1, fiberProdZ_set]
  rfl

/-- **The point set of `belowS`.**  Membership is: `z₁ ∈ Z.set`, `z₂ ∈ S.X.set` over the same
base as `z₁`, `|t| ≤ 1` and `t < v₂`. -/
theorem belowS_mem_iff {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1))
    (w : Fin (belowDim p m) → ℝ) :
    w ∈ (belowS Z S).set ↔
      belowZ1 w ∈ Z.set ∧ belowZ2 w ∈ S.X.set ∧
      projFirst p (m + 1) (belowZ1 w) = projFirst p (m + 1) (belowZ2 w) ∧
      |belowT w| ≤ 1 ∧ belowT w < belowV2 w := by
  rw [belowS, Work.WilE7.SemiPf.addConds_set]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, List.not_mem_nil, IsEmpty.forall_iff,
    List.mem_cons, forall_eq_or_imp, forall_const, and_true]
  rw [eaEval_belowPhigh]
  rw [belowPadded_eq]
  simp only [Set.mem_ofPred_eq]
  rw [belowW1_eq]
  rw [belowZ1_projFirst, belowZ2_projSnd]
  rw [belowT_eq, Work.WilE7.mem_cubeC_one]
  simp only [sub_pos]
  tauto

/-- Reindexing `belowS` along a permutation of the ambient coordinates does not change its
format (the ambient dimension is preserved: `(p+1) + belowFib p m = belowDim p m`). -/
theorem belowS_reindex_fmt {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1))
    (e : Fin (belowDim p m) ≃ Fin ((p + 1) + belowFib p m)) :
    (Work.WilE7.SemiPf.reindex e (belowS Z S)).fmt = (belowS Z S).fmt := by
  simp only [WilkiesDesign.E.SemiPf.fmt, Work.WilE7.SemiPf.reindex, belowFib, belowDim, belowK]
  omega

/-! ## §5. The extraction map and the coordinate permutation -/

/-- The "base + vertical" projection: send `w` to `Fin.snoc (π_p (z₁ w)) (t w)`. -/
def belowExtract {p m : ℕ} (w : Fin (belowDim p m) → ℝ) : Fin (p + 1) → ℝ :=
  Fin.snoc (fun i : Fin p => w (belowZ1Idx p m (Fin.castAdd (m + 1) i))) (w (belowTIdx p m))

theorem belowExtract_apply_castSucc {p m : ℕ} (w : Fin (belowDim p m) → ℝ) (i : Fin p) :
    belowExtract w (Fin.castSucc i) = w (belowZ1Idx p m (Fin.castAdd (m + 1) i)) := by
  simp only [belowExtract, Fin.snoc_castSucc]

theorem belowExtract_apply_last {p m : ℕ} (w : Fin (belowDim p m) → ℝ) :
    belowExtract w (Fin.last p) = belowT w := by
  simp only [belowExtract, Fin.snoc_last, belowT]

theorem belowExtract_eq_snoc {p m : ℕ} (w : Fin (belowDim p m) → ℝ) :
    belowExtract w = Fin.snoc (projFirst p (m + 1) (belowZ1 w)) (belowT w) := rfl

/-- The coordinate permutation bringing the vertical coordinate next to the base coordinates:
`(x, t, rest) ↦ (x_0, …, x_{p-1}, t, rest)`. -/
theorem belowPerm (p m : ℕ) :
    ∃ e : Fin (belowDim p m) ≃ Fin ((p + 1) + belowFib p m),
      ∀ y : Fin ((p + 1) + belowFib p m) → ℝ,
        projFirst (p + 1) (belowFib p m) y = belowExtract (fun i => y (e i)) := by
  have hp1 : p + 1 ≤ belowDim p m := by simp only [belowDim, belowK]; omega
  have h : belowDim p m = (p + 1) + belowFib p m := (Nat.add_sub_of_le hp1).symm
  have hp : p < belowDim p m := by omega
  have hK : belowK p m < belowDim p m := by simp only [belowDim]; omega
  have hKle : p ≤ belowK p m := by simp only [belowK]; omega
  refine ⟨(Equiv.swap (⟨p, hp⟩ : Fin (belowDim p m))
      (⟨belowK p m, hK⟩ : Fin (belowDim p m))).trans (finEquiv h), ?_⟩
  intro y
  funext j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · rw [projFirst, belowExtract, Fin.snoc_castSucc]
    congr 1
    apply Fin.ext
    simp only [Equiv.trans_apply, finEquiv_apply_val]
    rw [Equiv.swap_apply_of_ne_of_ne]
    · simp only [belowZ1Idx, Fin.val_castAdd, Fin.val_castSucc]
    · intro hc
      have h2 := congrArg Fin.val hc
      simp only [belowZ1Idx, Fin.val_castAdd] at h2
      omega
    · intro hc
      have h2 := congrArg Fin.val hc
      simp only [belowZ1Idx, Fin.val_castAdd] at h2
      omega
  · rw [projFirst, belowExtract, Fin.snoc_last]
    congr 1
    apply Fin.ext
    simp only [Equiv.trans_apply, finEquiv_apply_val]
    have hbT : belowTIdx p m = (⟨belowK p m, hK⟩ : Fin (belowDim p m)) :=
      Fin.ext (by simp only [belowTIdx, Fin.val_last])
    rw [← hbT, Equiv.swap_apply_right]
    simp only [Fin.val_castAdd, Fin.val_last]

/-! ## §6. The parametrised points of `belowS` -/

/-- The point of `belowS` with first block `u`, second block `(π_p u, v)` and vertical
coordinate `t`. -/
noncomputable def belowPt {p m : ℕ} (u : Fin (p + (m + 1)) → ℝ) (v : Fin (m + 1) → ℝ)
    (t : ℝ) : Fin (belowDim p m) → ℝ :=
  Fin.append (Fin.append u (Fin.append (projFirst p (m + 1) u) v)) (fun _ : Fin 1 => t)

theorem belowZ1_belowPt {p m : ℕ} (u : Fin (p + (m + 1)) → ℝ) (v : Fin (m + 1) → ℝ)
    (t : ℝ) : belowZ1 (belowPt u v t) = u := by
  rw [belowZ1_projFirst]
  simp only [belowPt, projFirst_append]

theorem belowZ2_belowPt {p m : ℕ} (u : Fin (p + (m + 1)) → ℝ) (v : Fin (m + 1) → ℝ)
    (t : ℝ) : belowZ2 (belowPt u v t) = Fin.append (projFirst p (m + 1) u) v := by
  rw [belowZ2_projSnd]
  simp only [belowPt, projFirst_append, projSnd_append]

theorem belowT_belowPt {p m : ℕ} (u : Fin (p + (m + 1)) → ℝ) (v : Fin (m + 1) → ℝ)
    (t : ℝ) : belowT (belowPt u v t) = t := by
  rw [belowT]
  show belowPt u v t (Fin.last (belowK p m)) = t
  rw [show Fin.last (belowK p m) = Fin.natAdd (belowK p m) 0 from
    Fin.ext (by simp [Fin.val_last, Fin.val_natAdd])]
  simp only [belowPt, Fin.append_right]

theorem belowV2_belowPt {p m : ℕ} (u : Fin (p + (m + 1)) → ℝ) (v : Fin (m + 1) → ℝ)
    (t : ℝ) : belowV2 (belowPt u v t) = v (Fin.last m) := by
  rw [belowV2, belowZ2_belowPt]
  simp only [Fin.append_right]

theorem belowExtract_belowPt {p m : ℕ} (u : Fin (p + (m + 1)) → ℝ) (v : Fin (m + 1) → ℝ)
    (t : ℝ) : belowExtract (belowPt u v t) = Fin.snoc (projFirst p (m + 1) u) t := by
  rw [belowExtract_eq_snoc, belowZ1_belowPt, belowT_belowPt]

/-- The parametrised point lies in `belowS` whenever its data satisfy the sheet condition,
the cube constraint and the strict inequality. -/
theorem belowPt_mem {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1))
    (u : Fin (p + (m + 1)) → ℝ) (hu : u ∈ Z.set) (v : Fin (m + 1) → ℝ) (t : ℝ)
    (hv : Fin.append (projFirst p (m + 1) u) v ∈ S.X.set) (ht : |t| ≤ 1)
    (h : t < v (Fin.last m)) :
    belowPt u v t ∈ (belowS Z S).set := by
  rw [belowS_mem_iff]
  exact ⟨by rwa [belowZ1_belowPt], by rwa [belowZ2_belowPt],
    by rw [belowZ1_belowPt, belowZ2_belowPt, projFirst_append],
    by rw [belowT_belowPt]; exact ht,
    by rw [belowT_belowPt, belowV2_belowPt]; exact h⟩

/-! ## §7. The parametrisation of the below cell -/

/-- The region of `(base component) × ℝ` parametrising the below cell: the base point runs over
the component of `Z` through `u₀` and the vertical coordinate over `[-1, level of s j)`. -/
def belowH {p m k : ℕ} (Z : SemiPf (p + (m + 1)))
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (j : Fin k)
    (u₀ : Fin (p + (m + 1)) → ℝ) : Set ((Fin (p + (m + 1)) → ℝ) × ℝ) :=
  {q | q.1 ∈ connectedComponentIn Z.set u₀ ∧ (-1 : ℝ) ≤ q.2 ∧
    q.2 < (s j (projFirst p (m + 1) q.1)) (Fin.last m)}

theorem mem_belowH {p m k : ℕ} {Z : SemiPf (p + (m + 1))}
    {s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)} {j : Fin k}
    {u₀ : Fin (p + (m + 1)) → ℝ} {q : (Fin (p + (m + 1)) → ℝ) × ℝ} :
    q ∈ belowH Z s j u₀ ↔ q.1 ∈ connectedComponentIn Z.set u₀ ∧ (-1 : ℝ) ≤ q.2 ∧
      q.2 < (s j (projFirst p (m + 1) q.1)) (Fin.last m) := Iff.rfl

/-- The parametrisation of the below cell: `(u, t) ↦ belowPt u (s j (π u)) t`. -/
def belowPhi {p m k : ℕ} (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (j : Fin k) :
    ((Fin (p + (m + 1)) → ℝ) × ℝ) → Fin (belowDim p m) → ℝ :=
  fun q => belowPt q.1 (s j (projFirst p (m + 1) q.1)) q.2

theorem belowZ1_belowPhi {p m k : ℕ} (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (j : Fin k) (q : (Fin (p + (m + 1)) → ℝ) × ℝ) :
    belowZ1 (belowPhi s j q) = q.1 :=
  belowZ1_belowPt _ _ _

theorem belowZ2_belowPhi {p m k : ℕ} (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (j : Fin k) (q : (Fin (p + (m + 1)) → ℝ) × ℝ) :
    belowZ2 (belowPhi s j q) = Fin.append (projFirst p (m + 1) q.1) (s j (projFirst p (m + 1) q.1)) :=
  belowZ2_belowPt _ _ _

theorem belowT_belowPhi {p m k : ℕ} (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (j : Fin k) (q : (Fin (p + (m + 1)) → ℝ) × ℝ) :
    belowT (belowPhi s j q) = q.2 :=
  belowT_belowPt _ _ _

theorem belowExtract_belowPhi {p m k : ℕ} (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (j : Fin k) (q : (Fin (p + (m + 1)) → ℝ) × ℝ) :
    belowExtract (belowPhi s j q) = Fin.snoc (projFirst p (m + 1) q.1) q.2 :=
  belowExtract_belowPt _ _ _

end Work.WilE7.BelowAux
