/-
  WilE7 (`Work.WilE7.BandAux.BandDefs`): the semi-Pfaffian presentation of the *band cell*
  between two sheets.

  Given a stratum `S : Stratum p (m+1)` and a `SemiPf` set `Z` defining the base cell
  `C = π_p (connectedComponentIn Z.set u₀)`, together with continuous sheets `s j : C → ℝ^{m+1}`
  (`j : Fin k`), the *band cell* between the sheets `i < j` is

    `band i j = {y : Fin (p+1) → ℝ | Fin.init y ∈ C ∧
        (s i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) < (s j (Fin.init y)) (Fin.last m)}`.

  This file builds the `SemiPf` set

    `bandS3 Z S : SemiPf (bandDim p m)`

  (a double fibre product `(Z ×_C S.X) ×_C (Z ×_C S.X)` with an extra vertical coordinate `t`,
  cut by the two inequalities `v₂ < t < v₂'`), and records
  * its point set (`bandS3_mem_iff`),
  * the coordinate permutation (`bandPerm`) identifying the "base + vertical" projection with the
    first `p+1` coordinates, and
  * the canonical point `bandPoint` of the set and its membership.

  The connected-component argument ("the component through `bandPoint` projects exactly onto the
  band") lives in `Work.WilE7.BandAux.bandComponent`; the assembly in
  `Submission/Work/WilE7/bandCell_star.lean`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.ProdDefs
import Submission.Work.WilE7.prodSet
import Submission.Work.WilE7.fiberProduct_semiPf
import Submission.Work.WilE7.pad_set
import Submission.Work.WilE7.star_proj
import Submission.Work.WilE8.Basic
import Submission.Work.WilE7.projFirst_fiberClosure
import Submission.Work.WilE7.stratGraph

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesDesign WilkiesDesign.E

/-! ## §1. Intersecting a semi-Pfaffian set with equations and inequalities

`SemiPf.addConds X E P` appends the equations `E` to `eqs` and the inequalities `P` to `pos`
of every branch of `redBasics X`.  Its point set is `X.set ∩ {E = 0} ∩ {P > 0}` and its degree
grows by at most `max 1 X.deg * (∑ atomDeg E + ∑ atomDeg P)`. -/

def SemiPf.addConds {k : ℕ} (X : SemiPf k) (E P : List (EAPoly k X.r)) : SemiPf k :=
  ⟨X.r, X.c, (redBasics X).map (fun B => (⟨B.eqs ++ E, B.pos ++ P⟩ : Basic k X.r))⟩

theorem Basic.holds_addConds {k r : ℕ} (c : EAChain k r) (B : Basic k r)
    (E P : List (EAPoly k r)) (z : Fin k → ℝ) :
    (⟨B.eqs ++ E, B.pos ++ P⟩ : Basic k r).holds c z ↔
      B.holds c z ∧ (∀ f ∈ E, eaEval c f z = 0) ∧ (∀ g ∈ P, 0 < eaEval c g z) := by
  simp only [Basic.holds, List.forall_mem_append]
  tauto

theorem SemiPf.addConds_set {k : ℕ} (X : SemiPf k) (E P : List (EAPoly k X.r)) :
    (SemiPf.addConds X E P).set = X.set ∩ {z | ∀ f ∈ E, eaEval X.c f z = 0} ∩
      {z | ∀ g ∈ P, 0 < eaEval X.c g z} := by
  ext z
  simp only [SemiPf.set, SemiPf.addConds, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hz, B, hB, hh⟩
    obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.mp hB
    obtain ⟨h1, h2, h3⟩ := (Basic.holds_addConds X.c B₀ E P z).mp hh
    exact ⟨⟨⟨hz, (exists_holds_redBasics X z).mp ⟨B₀, hB₀, h1⟩⟩, h2⟩, h3⟩
  · rintro ⟨⟨⟨hz, B, hB, h1⟩, h2⟩, h3⟩
    obtain ⟨B', hB', h1'⟩ := (exists_holds_redBasics X z).mpr ⟨B, hB, h1⟩
    exact ⟨hz, ⟨B'.eqs ++ E, B'.pos ++ P⟩, List.mem_map.mpr ⟨B', hB', rfl⟩,
      (Basic.holds_addConds X.c B' E P z).mpr ⟨h1', h2, h3⟩⟩

theorem SemiPf.addConds_fmt {k : ℕ} (X : SemiPf k) (E P : List (EAPoly k X.r)) :
    (SemiPf.addConds X E P).fmt = X.fmt := rfl

theorem basic_deg_addConds_eq {k r : ℕ} (B : Basic k r) (E P : List (EAPoly k r)) :
    (⟨B.eqs ++ E, B.pos ++ P⟩ : Basic k r).deg
      = B.deg + ((E.map atomDeg).sum + (P.map atomDeg).sum) := by
  simp only [Basic.deg, List.map_append, List.sum_append]
  ring

theorem basic_deg_addConds {k r : ℕ} (B : Basic k r) (E P : List (EAPoly k r)) :
    (⟨B.eqs ++ E, B.pos ++ P⟩ : Basic k r).deg
      ≤ B.deg + ((E.map atomDeg).sum + (P.map atomDeg).sum) :=
  (basic_deg_addConds_eq B E P).le

theorem SemiPf.addConds_deg_le {k : ℕ} (X : SemiPf k) (E P : List (EAPoly k X.r)) :
    (SemiPf.addConds X E P).deg ≤ X.deg + max 1 X.deg *
      ((E.map atomDeg).sum + (P.map atomDeg).sum) := by
  have hpt : ∀ B ∈ redBasics X,
      (⟨B.eqs ++ E, B.pos ++ P⟩ : Basic k X.r).deg
        ≤ B.deg + ((E.map atomDeg).sum + (P.map atomDeg).sum) :=
    fun B _ => basic_deg_addConds B E P
  have hdeg : (SemiPf.addConds X E P).deg
      ≤ ((redBasics X).map (fun B => B.deg + ((E.map atomDeg).sum + (P.map atomDeg).sum))).sum := by
    simp only [SemiPf.deg, SemiPf.addConds, List.map_map]
    exact sum_map_le_of_pointwise _ _ _ hpt
  rw [List.sum_map_add_const] at hdeg
  exact le_trans hdeg (Nat.add_le_add (redBasics_deg_le X)
    (Nat.mul_le_mul_right _ (redBasics_length_le X)))

/-! ## §2. The cube in one variable -/

/-- The `SemiPf` set of the closed cube `[-1,1] ⊆ ℝ¹`, as a single (trivial) branch. -/
noncomputable def bandCube1 : SemiPf 1 := Work.WilE8.cubeSemiPf 1

theorem bandCube1_set : bandCube1.set = cubeC 1 := Work.WilE8.cubeSemiPf_set 1

theorem mem_cubeC_one {v : Fin 1 → ℝ} : v ∈ cubeC 1 ↔ |v 0| ≤ 1 := by
  constructor
  · intro h; exact h 0
  · intro h i; fin_cases i; exact h

/-! ## §3. The ambient dimensions and the coordinate indices -/

/-- The ambient dimension of the double fibre product (four blocks of `p + (m+1)` coordinates). -/
abbrev bandK (p m : ℕ) : ℕ := ((p + (m + 1)) + (p + (m + 1))) + ((p + (m + 1)) + (p + (m + 1)))

/-- The ambient dimension of `bandS3` (the double fibre product plus the vertical coordinate). -/
abbrev bandDim (p m : ℕ) : ℕ := bandK p m + 1

/-- The fibre dimension of the `*`-piece: everything except the base and the vertical coordinate. -/
abbrev bandFib (p m : ℕ) : ℕ := bandDim p m - (p + 1)

/-- Index of the `i`-th coordinate of the first block `z₁`. -/
def bandZ1Idx (p m : ℕ) (i : Fin (p + (m + 1))) : Fin (bandDim p m) :=
  Fin.castAdd 1 (Fin.castAdd ((p + (m + 1)) + (p + (m + 1))) (Fin.castAdd (p + (m + 1)) i))

/-- Index of the `i`-th coordinate of the second block `z₂`. -/
def bandZ2Idx (p m : ℕ) (i : Fin (p + (m + 1))) : Fin (bandDim p m) :=
  Fin.castAdd 1 (Fin.castAdd ((p + (m + 1)) + (p + (m + 1))) (Fin.natAdd (p + (m + 1)) i))

/-- Index of the `i`-th coordinate of the third block `z₁'`. -/
def bandZ1'Idx (p m : ℕ) (i : Fin (p + (m + 1))) : Fin (bandDim p m) :=
  Fin.castAdd 1 (Fin.natAdd ((p + (m + 1)) + (p + (m + 1))) (Fin.castAdd (p + (m + 1)) i))

/-- Index of the `i`-th coordinate of the fourth block `z₂'`. -/
def bandZ2'Idx (p m : ℕ) (i : Fin (p + (m + 1))) : Fin (bandDim p m) :=
  Fin.castAdd 1 (Fin.natAdd ((p + (m + 1)) + (p + (m + 1))) (Fin.natAdd (p + (m + 1)) i))

/-- Index of the vertical coordinate. -/
def bandTIdx (p m : ℕ) : Fin (bandDim p m) := Fin.last (bandK p m)

/-- Index of the vertical coordinate of the sheet `z₂`. -/
def bandV2Idx (p m : ℕ) : Fin (bandDim p m) := bandZ2Idx p m (Fin.natAdd p (Fin.last m))

/-- Index of the vertical coordinate of the sheet `z₂'`. -/
def bandV2'Idx (p m : ℕ) : Fin (bandDim p m) := bandZ2'Idx p m (Fin.natAdd p (Fin.last m))

/-- The first block of `w`. -/
def bandZ1 {p m : ℕ} (w : Fin (bandDim p m) → ℝ) : Fin (p + (m + 1)) → ℝ :=
  fun i => w (bandZ1Idx p m i)

/-- The second block of `w`. -/
def bandZ2 {p m : ℕ} (w : Fin (bandDim p m) → ℝ) : Fin (p + (m + 1)) → ℝ :=
  fun i => w (bandZ2Idx p m i)

/-- The third block of `w`. -/
def bandZ1' {p m : ℕ} (w : Fin (bandDim p m) → ℝ) : Fin (p + (m + 1)) → ℝ :=
  fun i => w (bandZ1'Idx p m i)

/-- The fourth block of `w`. -/
def bandZ2' {p m : ℕ} (w : Fin (bandDim p m) → ℝ) : Fin (p + (m + 1)) → ℝ :=
  fun i => w (bandZ2'Idx p m i)

/-- The vertical coordinate of `w`. -/
def bandT {p m : ℕ} (w : Fin (bandDim p m) → ℝ) : ℝ := w (bandTIdx p m)

/-- The vertical coordinate of the second block (the level of the sheet `z₂`). -/
def bandV2 {p m : ℕ} (w : Fin (bandDim p m) → ℝ) : ℝ :=
  (bandZ2 w) (Fin.natAdd p (Fin.last m))

/-- The vertical coordinate of the fourth block (the level of the sheet `z₂'`). -/
def bandV2' {p m : ℕ} (w : Fin (bandDim p m) → ℝ) : ℝ :=
  (bandZ2' w) (Fin.natAdd p (Fin.last m))

theorem bandT_apply {p m : ℕ} (w : Fin (bandDim p m) → ℝ) : w (bandTIdx p m) = bandT w := rfl

theorem bandV2_apply {p m : ℕ} (w : Fin (bandDim p m) → ℝ) :
    w (bandV2Idx p m) = bandV2 w := rfl

theorem bandV2'_apply {p m : ℕ} (w : Fin (bandDim p m) → ℝ) :
    w (bandV2'Idx p m) = bandV2' w := rfl

theorem bandT_eq {p m : ℕ} (w : Fin (bandDim p m) → ℝ) :
    bandT w = (projSnd (bandK p m) 1 w) 0 := by
  show w (Fin.last (bandK p m)) = w (Fin.natAdd (bandK p m) 0)
  exact congrArg w (Fin.ext (by simp [Fin.val_natAdd, Fin.val_last]))

/-! ## §4. The two inequality atoms -/

/-- The atom `t - v₂`, positive exactly when the vertical coordinate is above the sheet `z₂`. -/
def bandPlow (p m r : ℕ) : EAPoly (bandDim p m) r :=
  MvPolynomial.X (Sum.inl (bandTIdx p m)) - MvPolynomial.X (Sum.inl (bandV2Idx p m))

/-- The atom `v₂' - t`, positive exactly when the vertical coordinate is below the sheet `z₂'`. -/
def bandPhigh (p m r : ℕ) : EAPoly (bandDim p m) r :=
  MvPolynomial.X (Sum.inl (bandV2'Idx p m)) - MvPolynomial.X (Sum.inl (bandTIdx p m))

theorem eaEval_bandPlow {p m r : ℕ} (c : EAChain (bandDim p m) r)
    (w : Fin (bandDim p m) → ℝ) :
    eaEval c (bandPlow p m r) w = bandT w - bandV2 w := by
  simp [bandPlow, eaEval, bandT, bandV2, bandZ2, bandV2Idx, bandTIdx]

theorem eaEval_bandPhigh {p m r : ℕ} (c : EAChain (bandDim p m) r)
    (w : Fin (bandDim p m) → ℝ) :
    eaEval c (bandPhigh p m r) w = bandV2' w - bandT w := by
  simp [bandPhigh, eaEval, bandT, bandV2', bandZ2', bandV2'Idx, bandTIdx]

theorem atomDeg_bandPlow {p m r : ℕ} : atomDeg (bandPlow p m r) ≤ 2 := by
  have h := MvPolynomial.totalDegree_sub
    (MvPolynomial.X (Sum.inl (bandTIdx p m)) : EAPoly (bandDim p m) r)
    (MvPolynomial.X (Sum.inl (bandV2Idx p m)) : EAPoly (bandDim p m) r)
  rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X] at h
  simp only [atomDeg, bandPlow]
  omega

theorem atomDeg_bandPhigh {p m r : ℕ} : atomDeg (bandPhigh p m r) ≤ 2 := by
  have h := MvPolynomial.totalDegree_sub
    (MvPolynomial.X (Sum.inl (bandV2'Idx p m)) : EAPoly (bandDim p m) r)
    (MvPolynomial.X (Sum.inl (bandTIdx p m)) : EAPoly (bandDim p m) r)
  rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X] at h
  simp only [atomDeg, bandPhigh]
  omega

/-! ## §5. The construction -/

/-- The fibre product `W = Z ×_{ℝ^p} S.X` (two blocks `z₁`, `z₂`). -/
noncomputable def bandW1 {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1)) :
    SemiPf ((p + (m + 1)) + (p + (m + 1))) :=
  fiberProdZ (p := p) (q := m + 1) Z S.X

/-- The double fibre product: two independent copies of `W`, glued along the diagonal of the
`W`-coordinates (so that both copies share their whole base `π_p`). -/
noncomputable def bandW2 {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1)) :
    SemiPf (bandK p m) :=
  fiberProdZ (p := p + (m + 1)) (q := p + (m + 1)) (bandW1 Z S) (bandW1 Z S)

/-- The double fibre product with the vertical coordinate appended (the cube in `ℝ¹`). -/
noncomputable def bandPadded {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1)) :
    SemiPf (bandDim p m) :=
  SemiPf.prod (bandW2 Z S) bandCube1

/-- The `SemiPf` set of the band: the double fibre product with the vertical coordinate, cut by
`v₂ < t < v₂'`. -/
noncomputable def bandS3 {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1)) :
    SemiPf (bandDim p m) :=
  SemiPf.addConds (bandPadded Z S) []
    [bandPlow p m (bandPadded Z S).r, bandPhigh p m (bandPadded Z S).r]

/-- Reindexing `bandS3` along a permutation of the ambient coordinates does not change its
format (the ambient dimension is preserved: `(p+1) + bandFib p m = bandDim p m`). -/
theorem bandS3_reindex_fmt {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1))
    (e : Fin (bandDim p m) ≃ Fin ((p + 1) + bandFib p m)) :
    (SemiPf.reindex e (bandS3 Z S)).fmt = (bandS3 Z S).fmt := by
  simp only [SemiPf.fmt, SemiPf.reindex, bandFib, bandDim, bandK]
  omega

theorem bandS3_fmt {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1)) :
    (bandS3 Z S).fmt = bandDim p m + (bandW2 Z S).r := by
  show bandDim p m + (bandS3 Z S).r = bandDim p m + (bandW2 Z S).r
  simp only [bandS3, bandPadded, SemiPf.addConds, SemiPf.prod, bandCube1,
    Work.WilE8.cubeSemiPf]
  omega

theorem bandPadded_eq {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1)) :
    (bandPadded Z S).set = {w : Fin (bandDim p m) → ℝ |
      projFirst (bandK p m) 1 w ∈ (bandW2 Z S).set ∧
      projSnd (bandK p m) 1 w ∈ cubeC 1} := by
  rw [bandPadded, prodSet, bandCube1_set]

theorem bandW2_eq {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1))
    (u : Fin (bandK p m) → ℝ) :
    u ∈ (bandW2 Z S).set ↔
      projFirst ((p + (m + 1)) + (p + (m + 1))) (p + (m + 1) + (p + (m + 1)))
          u ∈ (bandW1 Z S).set ∧
      projSnd ((p + (m + 1)) + (p + (m + 1))) (p + (m + 1) + (p + (m + 1)))
          u ∈ (bandW1 Z S).set ∧
      projFirst (p + (m + 1)) (p + (m + 1))
          (projFirst ((p + (m + 1)) + (p + (m + 1))) (p + (m + 1) + (p + (m + 1))) u) =
        projFirst (p + (m + 1)) (p + (m + 1))
          (projSnd ((p + (m + 1)) + (p + (m + 1))) (p + (m + 1) + (p + (m + 1))) u) := by
  rw [bandW2, fiberProdZ_set (p := p + (m + 1)) (q := p + (m + 1)) (bandW1 Z S) (bandW1 Z S)]
  rfl

theorem bandW1_eq {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1))
    (u : Fin ((p + (m + 1)) + (p + (m + 1))) → ℝ) :
    u ∈ (bandW1 Z S).set ↔
      projFirst (p + (m + 1)) (p + (m + 1)) u ∈ Z.set ∧
      projSnd (p + (m + 1)) (p + (m + 1)) u ∈ S.X.set ∧
      projFirst p (m + 1) (projFirst (p + (m + 1)) (p + (m + 1)) u) =
        projFirst p (m + 1) (projSnd (p + (m + 1)) (p + (m + 1)) u) := by
  rw [bandW1, fiberProdZ_set (p := p) (q := m + 1) Z S.X]
  rfl

theorem bandZ1_projFirst {p m : ℕ} (w : Fin (bandDim p m) → ℝ) :
    bandZ1 w = projFirst (p + (m + 1)) (p + (m + 1))
      (projFirst ((p + (m + 1)) + (p + (m + 1))) (p + (m + 1) + (p + (m + 1)))
        (projFirst (bandK p m) 1 w)) := rfl

theorem bandZ2_projSnd {p m : ℕ} (w : Fin (bandDim p m) → ℝ) :
    bandZ2 w = projSnd (p + (m + 1)) (p + (m + 1))
      (projFirst ((p + (m + 1)) + (p + (m + 1))) (p + (m + 1) + (p + (m + 1)))
        (projFirst (bandK p m) 1 w)) := rfl

theorem bandZ1'_projFirst {p m : ℕ} (w : Fin (bandDim p m) → ℝ) :
    bandZ1' w = projFirst (p + (m + 1)) (p + (m + 1))
      (projSnd ((p + (m + 1)) + (p + (m + 1))) (p + (m + 1) + (p + (m + 1)))
        (projFirst (bandK p m) 1 w)) := rfl

theorem bandZ2'_projSnd {p m : ℕ} (w : Fin (bandDim p m) → ℝ) :
    bandZ2' w = projSnd (p + (m + 1)) (p + (m + 1))
      (projSnd ((p + (m + 1)) + (p + (m + 1))) (p + (m + 1) + (p + (m + 1)))
        (projFirst (bandK p m) 1 w)) := rfl

/-! ## §6. The point set of `bandS3` -/

/-- **The point set of `bandS3`.**  Membership is: `z₁ ∈ Z.set`, `z₂, z₂' ∈ S.X.set`, both
fibres over the same base as `z₁` (via the diagonal `z₁ = z₁'`), `|t| ≤ 1` and
`v₂ < t < v₂'`. -/
theorem bandS3_mem_iff {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1))
    (w : Fin (bandDim p m) → ℝ) :
    w ∈ (bandS3 Z S).set ↔
      bandZ1 w ∈ Z.set ∧ bandZ2 w ∈ S.X.set ∧ bandZ1' w ∈ Z.set ∧ bandZ2' w ∈ S.X.set ∧
      projFirst p (m + 1) (bandZ1 w) = projFirst p (m + 1) (bandZ2 w) ∧
      projFirst p (m + 1) (bandZ1' w) = projFirst p (m + 1) (bandZ2' w) ∧
      bandZ1 w = bandZ1' w ∧
      |bandT w| ≤ 1 ∧ bandV2 w < bandT w ∧ bandT w < bandV2' w := by
  rw [bandS3, SemiPf.addConds_set]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, List.not_mem_nil, IsEmpty.forall_iff,
    List.mem_cons, forall_eq_or_imp, forall_const, and_true]
  rw [eaEval_bandPlow, eaEval_bandPhigh]
  rw [bandPadded_eq]
  simp only [Set.mem_ofPred_eq]
  rw [bandW2_eq]
  rw [bandW1_eq, bandW1_eq]
  rw [bandZ1_projFirst, bandZ2_projSnd, bandZ1'_projFirst, bandZ2'_projSnd]
  rw [bandT_eq, mem_cubeC_one]
  simp only [sub_pos] at *
  tauto

/-! ## §7. The extraction map and the coordinate permutation -/

/-- The "base + vertical" projection: send `w` to `Fin.snoc (π_p (z₁ w)) (t w)`. -/
def bandExtract {p m : ℕ} (w : Fin (bandDim p m) → ℝ) : Fin (p + 1) → ℝ :=
  Fin.snoc (fun i : Fin p => w (bandZ1Idx p m (Fin.castAdd (m + 1) i))) (w (bandTIdx p m))

theorem bandExtract_apply_castSucc {p m : ℕ} (w : Fin (bandDim p m) → ℝ) (i : Fin p) :
    bandExtract w (Fin.castSucc i) = w (bandZ1Idx p m (Fin.castAdd (m + 1) i)) := by
  simp only [bandExtract, Fin.snoc_castSucc]

theorem bandExtract_apply_last {p m : ℕ} (w : Fin (bandDim p m) → ℝ) :
    bandExtract w (Fin.last p) = bandT w := by
  simp only [bandExtract, Fin.snoc_last, bandT]

theorem bandExtract_eq_snoc {p m : ℕ} (w : Fin (bandDim p m) → ℝ) :
    bandExtract w = Fin.snoc (projFirst p (m + 1) (bandZ1 w)) (bandT w) := rfl

/-! ## §8. The parametrised points of `bandS3` -/

/-- The point of `bandS3` with first block `u`, second block `(π_p u, v)`, third block `u`,
fourth block `(π_p u, v')` and vertical coordinate `t`. -/
noncomputable def bandPt {p m : ℕ} (u : Fin (p + (m + 1)) → ℝ) (v v' : Fin (m + 1) → ℝ)
    (t : ℝ) : Fin (bandDim p m) → ℝ :=
  Fin.append
    (Fin.append (Fin.append u (Fin.append (projFirst p (m + 1) u) v))
      (Fin.append u (Fin.append (projFirst p (m + 1) u) v')))
    (fun _ : Fin 1 => t)

theorem bandZ1_bandPt {p m : ℕ} (u : Fin (p + (m + 1)) → ℝ) (v v' : Fin (m + 1) → ℝ)
    (t : ℝ) : bandZ1 (bandPt u v v' t) = u := by
  rw [bandZ1_projFirst]
  simp only [bandPt, projFirst_append]

theorem bandZ2_bandPt {p m : ℕ} (u : Fin (p + (m + 1)) → ℝ) (v v' : Fin (m + 1) → ℝ)
    (t : ℝ) : bandZ2 (bandPt u v v' t) = Fin.append (projFirst p (m + 1) u) v := by
  rw [bandZ2_projSnd]
  simp only [bandPt, projFirst_append, projSnd_append]

theorem bandZ1'_bandPt {p m : ℕ} (u : Fin (p + (m + 1)) → ℝ) (v v' : Fin (m + 1) → ℝ)
    (t : ℝ) : bandZ1' (bandPt u v v' t) = u := by
  rw [bandZ1'_projFirst]
  simp only [bandPt, projFirst_append, projSnd_append]

theorem bandZ2'_bandPt {p m : ℕ} (u : Fin (p + (m + 1)) → ℝ) (v v' : Fin (m + 1) → ℝ)
    (t : ℝ) : bandZ2' (bandPt u v v' t) = Fin.append (projFirst p (m + 1) u) v' := by
  rw [bandZ2'_projSnd]
  simp only [bandPt, projFirst_append, projSnd_append]

theorem bandT_bandPt {p m : ℕ} (u : Fin (p + (m + 1)) → ℝ) (v v' : Fin (m + 1) → ℝ)
    (t : ℝ) : bandT (bandPt u v v' t) = t := by
  rw [bandT]
  show bandPt u v v' t (Fin.last (bandK p m)) = t
  rw [show Fin.last (bandK p m) = Fin.natAdd (bandK p m) 0 from
    Fin.ext (by simp [Fin.val_last, Fin.val_natAdd])]
  simp only [bandPt, Fin.append_right]

theorem bandV2_bandPt {p m : ℕ} (u : Fin (p + (m + 1)) → ℝ) (v v' : Fin (m + 1) → ℝ)
    (t : ℝ) : bandV2 (bandPt u v v' t) = v (Fin.last m) := by
  rw [bandV2, bandZ2_bandPt]
  simp only [Fin.append_right]

theorem bandV2'_bandPt {p m : ℕ} (u : Fin (p + (m + 1)) → ℝ) (v v' : Fin (m + 1) → ℝ)
    (t : ℝ) : bandV2' (bandPt u v v' t) = v' (Fin.last m) := by
  rw [bandV2', bandZ2'_bandPt]
  simp only [Fin.append_right]

/-- The parametrised point lies in `bandS3` whenever its data satisfy the two sheet conditions
and the strict inequalities. -/
theorem bandPt_mem {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1))
    (u : Fin (p + (m + 1)) → ℝ) (hu : u ∈ Z.set) (v v' : Fin (m + 1) → ℝ) (t : ℝ)
    (hv : Fin.append (projFirst p (m + 1) u) v ∈ S.X.set)
    (hv' : Fin.append (projFirst p (m + 1) u) v' ∈ S.X.set)
    (ht : |t| ≤ 1) (h1 : v (Fin.last m) < t) (h2 : t < v' (Fin.last m)) :
    bandPt u v v' t ∈ (bandS3 Z S).set := by
  rw [bandS3_mem_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [bandZ1_bandPt]
  · rwa [bandZ2_bandPt]
  · rwa [bandZ1'_bandPt]
  · rwa [bandZ2'_bandPt]
  · rw [bandZ1_bandPt, bandZ2_bandPt, projFirst_append]
  · rw [bandZ1'_bandPt, bandZ2'_bandPt, projFirst_append]
  · rw [bandZ1_bandPt, bandZ1'_bandPt]
  · rw [bandT_bandPt]; exact ht
  · rw [bandV2_bandPt, bandT_bandPt]; exact h1
  · rw [bandT_bandPt, bandV2'_bandPt]; exact h2

/-- The coordinate permutation bringing the vertical coordinate next to the base coordinates:
`(x, t, rest) ↦ (x_0, …, x_{p-1}, t, rest)`. -/
theorem bandPerm (p m : ℕ) :
    ∃ e : Fin (bandDim p m) ≃ Fin ((p + 1) + bandFib p m),
      ∀ y : Fin ((p + 1) + bandFib p m) → ℝ,
        projFirst (p + 1) (bandFib p m) y = bandExtract (fun i => y (e i)) := by
  have hp1 : p + 1 ≤ bandDim p m := by simp only [bandDim, bandK]; omega
  have h : bandDim p m = (p + 1) + bandFib p m := (Nat.add_sub_of_le hp1).symm
  have hp : p < bandDim p m := by omega
  have hK : bandK p m < bandDim p m := by simp only [bandDim]; omega
  have hKle : p ≤ bandK p m := by simp only [bandK]; omega
  refine ⟨(Equiv.swap (⟨p, hp⟩ : Fin (bandDim p m))
      (⟨bandK p m, hK⟩ : Fin (bandDim p m))).trans (finEquiv h), ?_⟩
  intro y
  funext j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · rw [projFirst, bandExtract, Fin.snoc_castSucc]
    congr 1
    apply Fin.ext
    simp only [Equiv.trans_apply, finEquiv_apply_val]
    rw [Equiv.swap_apply_of_ne_of_ne]
    · simp only [bandZ1Idx, Fin.val_castAdd, Fin.val_castSucc]
    · intro hc
      have h2 := congrArg Fin.val hc
      simp only [bandZ1Idx, Fin.val_castAdd] at h2
      omega
    · intro hc
      have h2 := congrArg Fin.val hc
      simp only [bandZ1Idx, Fin.val_castAdd] at h2
      omega
  · rw [projFirst, bandExtract, Fin.snoc_last]
    congr 1
    apply Fin.ext
    simp only [Equiv.trans_apply, finEquiv_apply_val]
    have hbT : bandTIdx p m = (⟨bandK p m, hK⟩ : Fin (bandDim p m)) :=
      Fin.ext (by simp only [bandTIdx, Fin.val_last])
    rw [← hbT, Equiv.swap_apply_right]
    simp only [Fin.val_castAdd, Fin.val_last]

end Work.WilE7
