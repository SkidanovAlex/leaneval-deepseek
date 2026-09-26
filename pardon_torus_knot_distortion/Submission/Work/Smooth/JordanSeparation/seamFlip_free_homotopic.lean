import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_seamflip
import Submission.Work.Smooth.JordanSeparation.lwalk_corner
import Submission.Work.Smooth.JordanSeparation.lwalk_flipstep
import Submission.Work.Smooth.JordanSeparation.flip_loop_homotopic
import Submission.Work.Smooth.JordanSeparation.plCutLoop
import Submission.Work.Smooth.JordanSeparation.lwalk_transport

/-!
# The seam corner move is a free homotopy

`seamFlip_free_homotopic`: moving the seam vertex `W.v 0 = W.v W.n` of a closed lattice walk to the
opposite corner `W.v 0 - (1,1)` at *both* ends changes the lifted loop by a free homotopy (the base
point moves from `W.pt 0` to the opposite corner of the cell `cellCl W.c (W.v 0 - (1,1))`).

The proof splits both lifted loops into the first edge, the middle chain and the last edge, compares
the middle chains outright (`joinNat_cast_bound`), and moves the two corner pieces inside the convex
cell by `homotopic_of_convex_subset`.
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

/-! ### Splitting a `joinNat` into its first edge, its middle and its last edge -/

/-- **The three-piece split of a `joinNat`.**  A join of `1 + (m + 1)` paths is homotopic to its
first path, its middle `m` paths and its last path. -/
theorem joinNat_zero_mid_last {X : Type*} [TopologicalSpace X] {p : ℕ → X}
    (F : ∀ k, Path (p k) (p (k + 1))) (m : ℕ) :
    Path.Homotopic (joinNat F (1 + (m + 1)))
      ((F 0).trans ((joinNat (p := fun l => p (1 + l)) (fun l => F (1 + l)) m).trans
        (F (1 + m)))) := by
  exact (joinNat_cut F 1 m 1).trans
    (Path.Homotopic.hcomp (Path.Homotopic.refl_trans (F 0))
      (Path.Homotopic.hcomp (Path.Homotopic.refl _) (Path.Homotopic.refl_trans (F (1 + m)))))

/-- **The `loopNat` decomposition.**  The lifted loop of a walk of length `≥ 2` is homotopic (in
`↥U`) to the join of its clamped edges, split as first edge · middle chain · last edge, cast back
to the loop base point. -/
theorem loopNat_decomp {U : Set ℂ} (X : LWalk) (hX : ∀ t, X.path t ∈ U) (_h2 : 2 ≤ X.n)
    (hn : X.n = 1 + ((X.n - 2) + 1)) :
    Path.Homotopic (X.loopNat hX)
      (Path.cast ((X.edgeUNat hX 0).trans
          ((joinNat (p := fun l => X.ptMin hX (1 + l)) (fun l => X.edgeUNat hX (1 + l))
            (X.n - 2)).trans (X.edgeUNat hX (1 + (X.n - 2)))))
        rfl ((X.ptMin_zero_eq_last hX).trans (congrArg (X.ptMin hX) hn))) := by
  have hself : X.loopNat hX = Path.cast (joinNat (p := X.ptMin hX) (X.edgeUNat hX) X.n) rfl
      (X.ptMin_zero_eq_last hX) := by
    rw [LWalk.loopNat_eq_joinNat]
    exact path_cast_proof_irrel (joinNat (p := X.ptMin hX) (X.edgeUNat hX) X.n) _ rfl _ _
  have hjoin : joinNat (p := X.ptMin hX) (X.edgeUNat hX) X.n
      = Path.cast (joinNat (p := X.ptMin hX) (X.edgeUNat hX) (1 + ((X.n - 2) + 1))) rfl
          (congrArg (X.ptMin hX) hn) := joinNat_of_eq (X.edgeUNat hX) hn
  have hcast : X.loopNat hX =
      Path.cast (joinNat (p := X.ptMin hX) (X.edgeUNat hX) (1 + ((X.n - 2) + 1))) rfl
        ((X.ptMin_zero_eq_last hX).trans (congrArg (X.ptMin hX) hn)) := by
    rw [hself, hjoin, Path.cast_cast]
  exact (path_homotopic_of_eq hcast).trans
    (Path.Homotopic.pathCast (joinNat_zero_mid_last (X.edgeUNat hX) (X.n - 2)) rfl
      ((X.ptMin_zero_eq_last hX).trans (congrArg (X.ptMin hX) hn)))

/-! ### The seam flip agrees with the walk in the middle range -/

/-- Away from the seam, the seam flip has the same vertices, hence the same points. -/
theorem seamFlip_pt_eq {W : LWalk} (h2 : 2 ≤ W.n)
    (ha : W.v (W.n - 1) = W.v 0 - (1, 0) ∨ W.v (W.n - 1) = W.v 0 - (0, 1))
    (hb : W.v 1 = W.v 0 - (1, 0) ∨ W.v 1 = W.v 0 - (0, 1))
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ W.n - 1) :
    (W.seamFlip h2 ha hb).pt j = W.pt j := by
  show (W.seamFlip h2 ha hb).c * gpt ((W.seamFlip h2 ha hb).v j) = W.c * gpt (W.v j)
  rw [LWalk.seamFlip_c, LWalk.seamFlip_v_of_ne W h2 ha hb (by omega) (by omega)]


/-- Away from the seam, the seam flip has the same lifted points. -/
theorem seamFlip_ptMin_eq {U : Set ℂ} {W : LWalk} {hval : ∀ t, W.path t ∈ U} (h2 : 2 ≤ W.n)
    (ha : W.v (W.n - 1) = W.v 0 - (1, 0) ∨ W.v (W.n - 1) = W.v 0 - (0, 1))
    (hb : W.v 1 = W.v 0 - (1, 0) ∨ W.v 1 = W.v 0 - (0, 1))
    (hval' : ∀ t, (W.seamFlip h2 ha hb).path t ∈ U)
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ W.n - 1) :
    W.ptMin hval j = (W.seamFlip h2 ha hb).ptMin hval' j := by
  have hjn : j ≤ W.n := by omega
  have hjn' : j ≤ (W.seamFlip h2 ha hb).n := by rw [LWalk.seamFlip_n]; exact hjn
  rw [W.ptMin_eq_ptU hval j hjn, (W.seamFlip h2 ha hb).ptMin_eq_ptU hval' j hjn']
  exact Subtype.ext (seamFlip_pt_eq h2 ha hb hj1 hj2).symm

/-! ### Membership of the corner points in the corner cell -/

/-- The four lattice points around the seam all lie in the closed cell whose upper-right corner is
the seam vertex. -/
theorem seamFlip_corner_mem {W : LWalk} (_h2 : 2 ≤ W.n)
    (ha : W.v (W.n - 1) = W.v 0 - (1, 0) ∨ W.v (W.n - 1) = W.v 0 - (0, 1))
    (hb : W.v 1 = W.v 0 - (1, 0) ∨ W.v 1 = W.v 0 - (0, 1)) :
    W.pt 0 ∈ cellCl W.c (W.v 0 - (1, 1)) ∧ W.pt 1 ∈ cellCl W.c (W.v 0 - (1, 1)) ∧
      W.pt (W.n - 1) ∈ cellCl W.c (W.v 0 - (1, 1)) ∧
      W.c * gpt (W.v 0 - (1, 1)) ∈ cellCl W.c (W.v 0 - (1, 1)) := by
  have h10 : W.v 0 - (1, 0) = (W.v 0 - (1, 1)) + (0, 1) := by ext <;> simp
  have h01 : W.v 0 - (0, 1) = (W.v 0 - (1, 1)) + (1, 0) := by ext <;> simp
  have h00 : (W.v 0 - (1, 1)) + (1, 1) = W.v 0 := by ext <;> simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · show W.c * gpt (W.v 0) ∈ cellCl W.c (W.v 0 - (1, 1))
    have h := smul_gpt_add_one_one_mem_cellCl W.c W.cpos (W.v 0 - (1, 1))
    rw [h00] at h
    exact h
  · show W.c * gpt (W.v 1) ∈ cellCl W.c (W.v 0 - (1, 1))
    rcases hb with hb | hb
    · have h := smul_gpt_add_zero_one_mem_cellCl W.c W.cpos (W.v 0 - (1, 1))
      rw [show (W.v 0 - (1, 1)) + (0, 1) = W.v 1 from h10.symm.trans hb.symm] at h
      exact h
    · have h := smul_gpt_add_one_zero_mem_cellCl W.c W.cpos (W.v 0 - (1, 1))
      rw [show (W.v 0 - (1, 1)) + (1, 0) = W.v 1 from h01.symm.trans hb.symm] at h
      exact h
  · show W.c * gpt (W.v (W.n - 1)) ∈ cellCl W.c (W.v 0 - (1, 1))
    rcases ha with ha | ha
    · have h := smul_gpt_add_zero_one_mem_cellCl W.c W.cpos (W.v 0 - (1, 1))
      rw [show (W.v 0 - (1, 1)) + (0, 1) = W.v (W.n - 1) from h10.symm.trans ha.symm] at h
      exact h
    · have h := smul_gpt_add_one_zero_mem_cellCl W.c W.cpos (W.v 0 - (1, 1))
      rw [show (W.v 0 - (1, 1)) + (1, 0) = W.v (W.n - 1) from h01.symm.trans ha.symm] at h
      exact h
  · exact smul_gpt_mem_cellCl W.c W.cpos _

/-! ### The clamped edges of the seam flip agree with those of the walk -/

/-- In the middle range, the clamped lifted edges of the seam flip and of the walk have the same
values. -/
theorem seamFlip_edgeUNat_val_eq {U : Set ℂ} {W : LWalk} {hval : ∀ t, W.path t ∈ U}
    (h2 : 2 ≤ W.n)
    (ha : W.v (W.n - 1) = W.v 0 - (1, 0) ∨ W.v (W.n - 1) = W.v 0 - (0, 1))
    (hb : W.v 1 = W.v 0 - (1, 0) ∨ W.v 1 = W.v 0 - (0, 1))
    (hval' : ∀ t, (W.seamFlip h2 ha hb).path t ∈ U)
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j + 1 ≤ W.n - 1) (t : unitInterval) :
    (((W.seamFlip h2 ha hb).edgeUNat hval' j) t : ℂ) = ((W.edgeUNat hval j) t : ℂ) := by
  have hjn : j < W.n := by omega
  have hjn' : j < (W.seamFlip h2 ha hb).n := by rw [LWalk.seamFlip_n]; exact hjn
  rw [LWalk.edgeUNat_apply (hval := hval') (W := W.seamFlip h2 ha hb) j t,
    LWalk.edgeUNat_apply (hval := hval) (W := W) j t, dif_pos hjn', dif_pos hjn]
  simp only [LWalk.edge, segPath, Path.segment_apply]
  rw [seamFlip_pt_eq h2 ha hb hj1 (by omega), seamFlip_pt_eq h2 ha hb (by omega) hj2]

/-- In the middle range, the clamped lifted edges of the seam flip and of the walk agree, after
transporting the endpoints. -/
theorem seamFlip_edgeUNat_cast_eq {U : Set ℂ} {W : LWalk} {hval : ∀ t, W.path t ∈ U}
    (h2 : 2 ≤ W.n)
    (ha : W.v (W.n - 1) = W.v 0 - (1, 0) ∨ W.v (W.n - 1) = W.v 0 - (0, 1))
    (hb : W.v 1 = W.v 0 - (1, 0) ∨ W.v 1 = W.v 0 - (0, 1))
    (hval' : ∀ t, (W.seamFlip h2 ha hb).path t ∈ U)
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j + 1 ≤ W.n - 1)
    (e : W.ptMin hval j = (W.seamFlip h2 ha hb).ptMin hval' j)
    (e' : W.ptMin hval (j + 1) = (W.seamFlip h2 ha hb).ptMin hval' (j + 1)) :
    W.edgeUNat hval j = Path.cast ((W.seamFlip h2 ha hb).edgeUNat hval' j) e e' := by
  apply Path.ext
  funext t
  apply Subtype.ext
  simp only [Path.cast_coe]
  exact (seamFlip_edgeUNat_val_eq h2 ha hb hval' (by omega) (by omega) t).symm

/-- **The middle chains of the walk and of its seam flip agree.**  The join of the clamped edges
from index `1` to index `W.n - 1` is the same for the walk and for its seam flip, after transporting
the endpoints. -/
theorem seamFlip_mid_eq {U : Set ℂ} {W : LWalk} {hval : ∀ t, W.path t ∈ U}
    (h2 : 2 ≤ W.n)
    (ha : W.v (W.n - 1) = W.v 0 - (1, 0) ∨ W.v (W.n - 1) = W.v 0 - (0, 1))
    (hb : W.v 1 = W.v 0 - (1, 0) ∨ W.v 1 = W.v 0 - (0, 1))
    (hval' : ∀ t, (W.seamFlip h2 ha hb).path t ∈ U)
    (e : W.ptMin hval 1 = (W.seamFlip h2 ha hb).ptMin hval' 1)
    (e' : W.ptMin hval (1 + (W.n - 2)) =
      (W.seamFlip h2 ha hb).ptMin hval' (1 + (W.n - 2))) :
    joinNat (p := fun l => W.ptMin hval (1 + l)) (fun l => W.edgeUNat hval (1 + l))
        (W.n - 2)
      = Path.cast (joinNat (p := fun l => (W.seamFlip h2 ha hb).ptMin hval' (1 + l))
          (fun l => (W.seamFlip h2 ha hb).edgeUNat hval' (1 + l)) (W.n - 2)) e e' := by
  have h := joinNat_cast_bound (J := W.n - 2)
    (p := fun l => W.ptMin hval (1 + l))
    (q := fun l => (W.seamFlip h2 ha hb).ptMin hval' (1 + l))
    (fun k _ => seamFlip_ptMin_eq h2 ha hb hval' (by omega) (by omega))
    (fun l => W.edgeUNat hval (1 + l))
    (fun l => (W.seamFlip h2 ha hb).edgeUNat hval' (1 + l))
    (fun k _ => seamFlip_edgeUNat_cast_eq h2 ha hb hval' (by omega) (by omega) _ _)
    (W.n - 2) le_rfl
  have hcast : Path.cast (joinNat (p := fun l => (W.seamFlip h2 ha hb).ptMin hval' (1 + l))
        (fun l => (W.seamFlip h2 ha hb).edgeUNat hval' (1 + l)) (W.n - 2))
      ((fun k _ => seamFlip_ptMin_eq h2 ha hb hval' (by omega) (by omega)) 0
        (Nat.zero_le (W.n - 2)))
      ((fun k _ => seamFlip_ptMin_eq h2 ha hb hval' (by omega) (by omega)) (W.n - 2) le_rfl)
      = Path.cast (joinNat (p := fun l => (W.seamFlip h2 ha hb).ptMin hval' (1 + l))
        (fun l => (W.seamFlip h2 ha hb).edgeUNat hval' (1 + l)) (W.n - 2)) e e' :=
    path_cast_proof_irrel _ _ _ _ _
  rw [hcast] at h
  exact h

/-! ### Values of paths lying in a set -/

/-- An endpoint cast does not change the values. -/
theorem values_cast {U B : Set ℂ} {x y x' y' : ↥U} {γ : Path x y} (hx : x' = x) (hy : y' = y)
    (h : ∀ t, (γ t : ℂ) ∈ B) : ∀ t, ((Path.cast γ hx hy) t : ℂ) ∈ B := by
  intro t
  rw [path_cast_apply]
  exact h t

/-- The values of a composite are the values of its factors. -/
theorem values_trans {U B : Set ℂ} {x y z : ↥U} {p : Path x y} {q : Path y z}
    (hp : ∀ t, (p t : ℂ) ∈ B) (hq : ∀ t, (q t : ℂ) ∈ B) : ∀ t, ((p.trans q) t : ℂ) ∈ B := by
  intro t
  rw [Path.trans_apply]
  split_ifs with h
  · exact hp _
  · exact hq _

/-- The values of the reverse of a path are the values of the path. -/
theorem values_symm {U B : Set ℂ} {x y : ↥U} {p : Path x y} (hp : ∀ t, (p t : ℂ) ∈ B) :
    ∀ t, ((p.symm t : ↥U) : ℂ) ∈ B := by
  intro t
  rw [Path.symm_apply]
  exact hp _

/-- The straight segment between two points of a convex set stays in the set. -/
theorem segment_values_mem {B : Set ℂ} (hB : Convex ℝ B) {a b : ℂ} (ha : a ∈ B) (hb : b ∈ B) :
    ∀ t, (Path.segment a b : unitInterval → ℂ) t ∈ B := by
  intro t
  exact hB.segment_subset ha hb (by rw [← Path.range_segment]; exact ⟨t, rfl⟩)

/-- The values of a lifted segment. -/
theorem segIn_values_mem {U B : Set ℂ} (hB : Convex ℝ B) (hBU : B ⊆ U) {a b : ℂ}
    (ha : a ∈ B) (hb : b ∈ B) :
    ∀ t, (((segIn hB hBU ha hb) t : ↥U) : ℂ) ∈ B := by
  intro t
  rw [segIn_apply]
  exact segment_values_mem hB ha hb t

/-- The values of a clamped lifted edge, given that its endpoints lie in a convex set. -/
theorem edgeUNat_values_mem {U B : Set ℂ} {X : LWalk} {hX : ∀ t, X.path t ∈ U} {k : ℕ}
    (hk : k < X.n) {a b : ℂ} (ha : X.pt k = a) (hb : X.pt (k + 1) = b)
    (hB : Convex ℝ B) (haB : a ∈ B) (hbB : b ∈ B) :
    ∀ t, (((X.edgeUNat hX k) t : ↥U) : ℂ) ∈ B := by
  intro t
  rw [LWalk.edgeUNat_apply, dif_pos hk]
  simp only [LWalk.edge, segPath]
  rw [ha, hb]
  exact segment_values_mem hB haB hbB t

end

end Work.Smooth.JordanSeparation

namespace Work.Smooth.JordanSeparation

/-- **The seam corner move is a free homotopy.** -/
theorem seamFlip_free_homotopic {U : Set ℂ} {W : LWalk} {hval : ∀ t, W.path t ∈ U}
    (h2 : 2 ≤ W.n)
    (ha : W.v (W.n - 1) = W.v 0 - (1, 0) ∨ W.v (W.n - 1) = W.v 0 - (0, 1))
    (hb : W.v 1 = W.v 0 - (1, 0) ∨ W.v 1 = W.v 0 - (0, 1))
    (hcU : cellCl W.c (W.v 0 - (1, 1)) ⊆ U)
    (hval' : ∀ t, (W.seamFlip h2 ha hb).path t ∈ U) :
    FreeHomotopic (W.loopNat hval) ((W.seamFlip h2 ha hb).loopNat hval') := by
  -- the seam flip, as a named walk
  set Z : LWalk := W.seamFlip h2 ha hb with hZ
  have hvalZ : ∀ t, Z.path t ∈ U := hval'
  have hZn : Z.n = W.n := rfl
  have hZc : Z.c = W.c := rfl
  have hnW : W.n = 1 + ((W.n - 2) + 1) := by omega
  have hnZ : Z.n = 1 + ((Z.n - 2) + 1) := by rw [hZn]; omega
  -- the corner cell
  have hD : Convex ℝ (cellCl W.c (W.v 0 - (1, 1))) := convex_cellCl W.c W.cpos _
  have hDne : (cellCl W.c (W.v 0 - (1, 1))).Nonempty := ⟨_, smul_gpt_mem_cellCl W.c W.cpos _⟩
  obtain ⟨hv0D, hv1D, hvlD, hsD⟩ := seamFlip_corner_mem h2 ha hb
  -- the two base points as elements of `↥U`
  have hP0 : W.ptMin hval 0 = (⟨W.pt 0, hcU hv0D⟩ : ↥U) := by
    rw [W.ptMin_eq_ptU hval 0 (Nat.zero_le _)]
    exact Subtype.ext rfl
  have hZpt0 : Z.pt 0 = W.c * gpt (W.v 0 - (1, 1)) := by
    rw [hZ]
    show (W.seamFlip h2 ha hb).c * gpt ((W.seamFlip h2 ha hb).v 0) = W.c * gpt (W.v 0 - (1, 1))
    rw [LWalk.seamFlip_c, LWalk.seamFlip_v_zero]
  have hZ0 : Z.ptMin hvalZ 0 = (⟨W.c * gpt (W.v 0 - (1, 1)), hcU hsD⟩ : ↥U) := by
    rw [Z.ptMin_eq_ptU hvalZ 0 (Nat.zero_le _)]
    apply Subtype.ext
    simp only [LWalk.ptU_apply]
    exact hZpt0
  -- the conjugating path: the diagonal of the corner cell
  let diag : Path (W.ptMin hval 0) (Z.ptMin hvalZ 0) :=
    Path.cast (segIn hD hcU hv0D hsD) hP0 hZ0
  -- point agreement away from the seam
  have hmid : ∀ j, 1 ≤ j → j ≤ W.n - 1 → W.ptMin hval j = Z.ptMin hvalZ j :=
    fun j hj1 hj2 => seamFlip_ptMin_eq h2 ha hb hval' hj1 hj2
  have he1 : W.ptMin hval (1 + 0) = Z.ptMin hvalZ (1 + 0) := hmid 1 (by omega) (by omega)
  have hel : W.ptMin hval (1 + (W.n - 2)) = Z.ptMin hvalZ (1 + (W.n - 2)) :=
    hmid (1 + (W.n - 2)) (by omega) (by omega)
  -- closing endpoint equalities
  have hW0 : W.ptMin hval 0 = W.ptMin hval (1 + ((W.n - 2) + 1)) :=
    (W.ptMin_zero_eq_last hval).trans (congrArg (W.ptMin hval) hnW)
  have hZlast : Z.ptMin hvalZ 0 = Z.ptMin hvalZ (1 + ((W.n - 2) + 1)) :=
    (Z.ptMin_zero_eq_last hvalZ).trans (congrArg (Z.ptMin hvalZ) hnZ)
  -- the three pieces of each loop
  let AW : Path (W.ptMin hval 0) (W.ptMin hval (1 + 0)) := Path.cast (W.edgeUNat hval 0) rfl rfl
  let XW : Path (W.ptMin hval (1 + 0)) (W.ptMin hval (1 + (W.n - 2))) :=
    joinNat (p := fun l => W.ptMin hval (1 + l)) (fun l => W.edgeUNat hval (1 + l)) (W.n - 2)
  let MW : Path (W.ptMin hval (1 + 0)) (W.ptMin hval (1 + (W.n - 2))) := Path.cast XW rfl rfl
  let BW : Path (W.ptMin hval (1 + (W.n - 2))) (W.ptMin hval 0) :=
    Path.cast (W.edgeUNat hval (1 + (W.n - 2))) rfl hW0
  let AZ : Path (Z.ptMin hvalZ 0) (W.ptMin hval (1 + 0)) :=
    Path.cast (Z.edgeUNat hvalZ 0) rfl he1
  let XZ : Path (Z.ptMin hvalZ (1 + 0)) (Z.ptMin hvalZ (1 + (W.n - 2))) :=
    joinNat (p := fun l => Z.ptMin hvalZ (1 + l)) (fun l => Z.edgeUNat hvalZ (1 + l)) (W.n - 2)
  let MZ : Path (W.ptMin hval (1 + 0)) (W.ptMin hval (1 + (W.n - 2))) := Path.cast XZ he1 hel
  let BZ : Path (W.ptMin hval (1 + (W.n - 2))) (Z.ptMin hvalZ 0) :=
    Path.cast (Z.edgeUNat hvalZ (1 + (W.n - 2))) hel hZlast
  -- the two loop decompositions
  have hWeq : Path.cast ((W.edgeUNat hval 0).trans
        (XW.trans (W.edgeUNat hval (1 + (W.n - 2))))) rfl hW0
      = AW.trans (MW.trans BW) := by
    rw [cast_trans_general (W.edgeUNat hval 0) (XW.trans (W.edgeUNat hval (1 + (W.n - 2))))
        rfl rfl hW0,
      cast_trans_general XW (W.edgeUNat hval (1 + (W.n - 2))) rfl rfl hW0]
  have hZeq : Path.cast ((Z.edgeUNat hvalZ 0).trans
        (XZ.trans (Z.edgeUNat hvalZ (1 + (W.n - 2))))) rfl hZlast
      = AZ.trans (MZ.trans BZ) := by
    rw [cast_trans_general (Z.edgeUNat hvalZ 0) (XZ.trans (Z.edgeUNat hvalZ (1 + (W.n - 2))))
        rfl he1 hZlast,
      cast_trans_general XZ (Z.edgeUNat hvalZ (1 + (W.n - 2))) he1 hel hZlast]
  have hloopW : Path.Homotopic (W.loopNat hval) (AW.trans (MW.trans BW)) :=
    (loopNat_decomp W hval h2 hnW).trans (path_homotopic_of_eq hWeq)
  have hloopZ : Path.Homotopic (Z.loopNat hvalZ) (AZ.trans (MZ.trans BZ)) :=
    (loopNat_decomp Z hvalZ h2 hnZ).trans (path_homotopic_of_eq hZeq)
  -- the middle chains agree
  have hM : MW = MZ := by
    show Path.cast XW rfl rfl = Path.cast XZ he1 hel
    rw [Path.cast_self]
    exact seamFlip_mid_eq h2 ha hb hval' he1 hel
  have hloopW' : Path.Homotopic (W.loopNat hval) (AW.trans (MZ.trans BW)) :=
    hloopW.trans (path_homotopic_of_eq (by rw [hM]))
  -- the points of the corner cell
  have hidx : (1 : ℕ) + (W.n - 2) = W.n - 1 := by omega
  have hZpt1 : Z.pt 1 = W.pt 1 := seamFlip_pt_eq h2 ha hb (by omega) (by omega)
  have hZptl : Z.pt (1 + (W.n - 2)) = W.pt (W.n - 1) := by
    have h : (W.seamFlip h2 ha hb).pt (1 + (W.n - 2)) = W.pt (1 + (W.n - 2)) :=
      seamFlip_pt_eq h2 ha hb (by omega) (by omega)
    rw [hidx] at h ⊢
    exact h
  have hZptl1 : Z.pt ((1 + (W.n - 2)) + 1) = W.c * gpt (W.v 0 - (1, 1)) := by
    have h : (1 + (W.n - 2)) + 1 = Z.n := by rw [hZn]; omega
    rw [h, Z.pt_last, hZpt0]
  have hWptl : W.pt (1 + (W.n - 2)) = W.pt (W.n - 1) := by rw [hidx]
  have hWptl1 : W.pt ((1 + (W.n - 2)) + 1) = W.pt 0 := by
    rw [show (1 + (W.n - 2)) + 1 = W.n from by omega, W.pt_last]
  -- the values lie in the corner cell
  have hdval : ∀ t, ((diag t : ↥U) : ℂ) ∈ cellCl W.c (W.v 0 - (1, 1)) :=
    values_cast hP0 hZ0 (segIn_values_mem hD hcU hv0D hsD)
  have hAWval : ∀ t, ((AW t : ↥U) : ℂ) ∈ cellCl W.c (W.v 0 - (1, 1)) :=
    values_cast (γ := W.edgeUNat hval 0) rfl rfl
      (edgeUNat_values_mem (X := W) (hX := hval) (k := 0) (by omega) rfl rfl hD hv0D hv1D)
  have hAZval : ∀ t, ((AZ t : ↥U) : ℂ) ∈ cellCl W.c (W.v 0 - (1, 1)) :=
    values_cast (γ := Z.edgeUNat hvalZ 0) rfl he1
      (edgeUNat_values_mem (X := Z) (hX := hvalZ) (k := 0) (by rw [hZn]; omega)
        hZpt0 hZpt1 hD hsD hv1D)
  have hBWval : ∀ t, ((BW t : ↥U) : ℂ) ∈ cellCl W.c (W.v 0 - (1, 1)) :=
    values_cast (γ := W.edgeUNat hval (1 + (W.n - 2))) rfl hW0
      (edgeUNat_values_mem (X := W) (hX := hval) (k := 1 + (W.n - 2)) (by omega)
        hWptl hWptl1 hD hvlD hv0D)
  have hBZval : ∀ t, ((BZ t : ↥U) : ℂ) ∈ cellCl W.c (W.v 0 - (1, 1)) :=
    values_cast (γ := Z.edgeUNat hvalZ (1 + (W.n - 2))) hel hZlast
      (edgeUNat_values_mem (X := Z) (hX := hvalZ) (k := 1 + (W.n - 2)) (by rw [hZn]; omega)
        hZptl hZptl1 hD hvlD hsD)
  -- the two corner moves
  have h1 : Path.Homotopic (diag.symm.trans AW) AZ :=
    homotopic_of_convex_subset hD hDne hcU _ _
      (values_trans (values_symm hdval) hAWval) hAZval
  have h3 : Path.Homotopic (BW.trans diag) BZ :=
    homotopic_of_convex_subset hD hDne hcU _ _
      (values_trans hBWval hdval) hBZval
  -- the conjugation, reassembled
  have s1 : Path.Homotopic (diag.symm.trans ((AW.trans (MZ.trans BW)).trans diag))
      ((diag.symm.trans (AW.trans (MZ.trans BW))).trans diag) :=
    (Path.Homotopic.trans_assoc diag.symm (AW.trans (MZ.trans BW)) diag).symm
  have s2 : Path.Homotopic ((diag.symm.trans (AW.trans (MZ.trans BW))).trans diag)
      (((diag.symm.trans AW).trans (MZ.trans BW)).trans diag) :=
    Path.Homotopic.hcomp (Path.Homotopic.trans_assoc diag.symm AW (MZ.trans BW)).symm
      (Path.Homotopic.refl diag)
  have s3 : Path.Homotopic (((diag.symm.trans AW).trans (MZ.trans BW)).trans diag)
      ((diag.symm.trans AW).trans ((MZ.trans BW).trans diag)) :=
    Path.Homotopic.trans_assoc _ _ _
  have s4 : Path.Homotopic ((diag.symm.trans AW).trans ((MZ.trans BW).trans diag))
      ((diag.symm.trans AW).trans (MZ.trans (BW.trans diag))) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl _) (Path.Homotopic.trans_assoc MZ BW diag)
  have s5 : Path.Homotopic ((diag.symm.trans AW).trans (MZ.trans (BW.trans diag)))
      (AZ.trans (MZ.trans BZ)) :=
    Path.Homotopic.hcomp h1 (Path.Homotopic.hcomp (Path.Homotopic.refl _) h3)
  refine ⟨diag, ?_⟩
  refine (Path.Homotopic.hcomp (Path.Homotopic.refl diag.symm)
    (Path.Homotopic.hcomp hloopW' (Path.Homotopic.refl diag))).trans ?_
  exact (s1.trans (s2.trans (s3.trans (s4.trans s5)))).trans hloopZ.symm

end Work.Smooth.JordanSeparation
