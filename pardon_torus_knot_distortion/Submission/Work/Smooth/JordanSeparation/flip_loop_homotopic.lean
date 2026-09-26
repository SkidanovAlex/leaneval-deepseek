import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_peel
import Submission.Work.Smooth.JordanSeparation.lwalk_cornerglue
import Submission.Work.Smooth.JordanSeparation.lwalk_flipstep

/-!
# The corner move at loop level

`flip_loop_homotopic`: if the corner cell `cellCl W.c (W.v k - (1,1))` of the lex-max vertex
`W.v k` lies in `U`, then the loop of `W` and the loop of the flipped walk `W.flip …` (the vertex
`W.v k` moved to `W.v k - (1,1)`) are homotopic in `↥U`.

The proof splits both joins at the flipped pair of edges (`joinNat_split3`), compares the prefix,
the two-edge middle piece and the suffix (`joinNat_replace_pair`), and transfers the statement
across the closing casts of `loopNat`.
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

/-- Equal paths are homotopic. -/
theorem path_homotopic_of_eq {X : Type*} [TopologicalSpace X] {x y : X} {p q : Path x y}
    (h : p = q) : Path.Homotopic p q := h ▸ Path.Homotopic.refl p

/-! ### Splitting a join at two consecutive indices -/

/-- **Splitting a join at the two-step piece `i`, `i+1`.**  The join of `i + (2+m)` pieces is
homotopic to its `i`-piece prefix, followed by the two-step piece at `i`, followed by the
`m`-piece suffix. -/
theorem joinNat_split3 {X : Type*} [TopologicalSpace X] {p : ℕ → X} {F : ∀ j, Path (p j) (p (j + 1))}
    (i m : ℕ) :
    Path.Homotopic (joinNat F (i + (2 + m)))
      ((joinNat F i).trans (((F i).trans (F (i + 1))).trans
        (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) m))) := by
  have h1 := joinNat_add F i (2 + m)
  have h2 := joinNat_add (p := fun l => p (i + l)) (fun l => F (i + l)) 2 m
  have h3 : Path.Homotopic (joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) 2)
      ((F i).trans (F (i + 1))) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl_trans (F i)) (Path.Homotopic.refl (F (i + 1)))
  have h4 : Path.Homotopic
      ((joinNat F i).trans (joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) (2 + m)))
      ((joinNat F i).trans ((joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) 2).trans
        (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) m))) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl _) h2
  have h5 : Path.Homotopic
      ((joinNat F i).trans ((joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) 2).trans
        (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) m)))
      (((joinNat F i).trans (joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) 2)).trans
        (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) m)) :=
    (Path.Homotopic.trans_assoc _ _ _).symm
  have h6 : Path.Homotopic
      (((joinNat F i).trans (joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) 2)).trans
        (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) m))
      (((joinNat F i).trans ((F i).trans (F (i + 1)))).trans
        (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) m)) :=
    Path.Homotopic.hcomp (Path.Homotopic.hcomp (Path.Homotopic.refl _) h3)
      (Path.Homotopic.refl _)
  have h7 : Path.Homotopic
      (((joinNat F i).trans ((F i).trans (F (i + 1)))).trans
        (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) m))
      ((joinNat F i).trans (((F i).trans (F (i + 1))).trans
        (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) m))) :=
    Path.Homotopic.trans_assoc _ _ _
  exact h1.trans (h4.trans (h5.trans (h6.trans h7)))

/-- **Replacing the two-step piece `i`, `i+1` of a join.**  If the prefix, the two-step piece and
the suffix of two joins (over possibly different point families, with the relevant points
identified) agree, then the joins agree. -/
theorem joinNat_replace_pair {X : Type*} [TopologicalSpace X] {p q : ℕ → X}
    {F : ∀ j, Path (p j) (p (j + 1))} {G : ∀ j, Path (q j) (q (j + 1))} {i m : ℕ}
    (h0 : p 0 = q 0) (hi : p i = q i) (hi2 : p (i + 2) = q (i + 2))
    (hn : p (i + (2 + m)) = q (i + (2 + m)))
    (hpre : joinNat F i = Path.cast (joinNat G i) h0 hi)
    (hsuf : joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) m
      = Path.cast (joinNat (p := fun l => q (i + (2 + l))) (fun l => G (i + (2 + l))) m)
          hi2 hn)
    (hmid : Path.Homotopic ((F i).trans (F (i + 1)))
      (Path.cast ((G i).trans (G (i + 1))) hi hi2)) :
    Path.Homotopic (joinNat F (i + (2 + m))) (Path.cast (joinNat G (i + (2 + m))) h0 hn) := by
  have hA := joinNat_split3 (F := F) i m
  have hB : Path.Homotopic (Path.cast (joinNat G (i + (2 + m))) h0 hn)
      (Path.cast ((joinNat G i).trans (((G i).trans (G (i + 1))).trans
        (joinNat (p := fun l => q (i + (2 + l))) (fun l => G (i + (2 + l))) m))) h0 hn) :=
    Path.Homotopic.pathCast (joinNat_split3 (F := G) i m) h0 hn
  have hC : Path.cast ((joinNat G i).trans (((G i).trans (G (i + 1))).trans
        (joinNat (p := fun l => q (i + (2 + l))) (fun l => G (i + (2 + l))) m))) h0 hn
      = (Path.cast (joinNat G i) h0 hi).trans
          (((Path.cast ((G i).trans (G (i + 1))) hi hi2)).trans
            (Path.cast (joinNat (p := fun l => q (i + (2 + l)))
              (fun l => G (i + (2 + l))) m) hi2 hn)) := by
    rw [cast_trans_general (joinNat G i)
      (((G i).trans (G (i + 1))).trans
        (joinNat (p := fun l => q (i + (2 + l))) (fun l => G (i + (2 + l))) m)) h0 hi hn,
      cast_trans_general ((G i).trans (G (i + 1)))
        (joinNat (p := fun l => q (i + (2 + l))) (fun l => G (i + (2 + l))) m) hi hi2 hn]
  have hD : Path.Homotopic
      ((Path.cast (joinNat G i) h0 hi).trans
        ((Path.cast ((G i).trans (G (i + 1))) hi hi2).trans
          (Path.cast (joinNat (p := fun l => q (i + (2 + l)))
            (fun l => G (i + (2 + l))) m) hi2 hn)))
      ((joinNat F i).trans (((F i).trans (F (i + 1))).trans
        (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) m))) :=
    Path.Homotopic.hcomp (path_homotopic_of_eq hpre.symm)
      (Path.Homotopic.hcomp hmid.symm (path_homotopic_of_eq hsuf.symm))
  have hD' : Path.Homotopic
      (Path.cast ((joinNat G i).trans (((G i).trans (G (i + 1))).trans
        (joinNat (p := fun l => q (i + (2 + l))) (fun l => G (i + (2 + l))) m))) h0 hn)
      ((joinNat F i).trans (((F i).trans (F (i + 1))).trans
        (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) m))) := by
    rw [hC]; exact hD
  exact hA.trans (hB.trans hD').symm


/-! ### The point-level data of the flipped walk -/

/-- Away from the flipped index, the flipped walk has the same points as the original. -/
theorem flip_pt_of_ne {W : LWalk} {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ W.n)
    (ha : W.v (k - 1) = W.v k - (1, 0) ∨ W.v (k - 1) = W.v k - (0, 1))
    (hb : W.v (k + 1) = W.v k - (1, 0) ∨ W.v (k + 1) = W.v k - (0, 1)) {j : ℕ} (hj : j ≠ k) :
    (W.flip hk1 hk2 ha hb).pt j = W.pt j := by
  show (W.flip hk1 hk2 ha hb).c * gpt ((W.flip hk1 hk2 ha hb).v j) = W.c * gpt (W.v j)
  rw [LWalk.flip_c, LWalk.flip_v_of_ne W hk1 hk2 ha hb hj]

/-- The flipped vertex, as a point of `ℂ`. -/
theorem flip_pt_self {W : LWalk} {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ W.n)
    (ha : W.v (k - 1) = W.v k - (1, 0) ∨ W.v (k - 1) = W.v k - (0, 1))
    (hb : W.v (k + 1) = W.v k - (1, 0) ∨ W.v (k + 1) = W.v k - (0, 1)) :
    (W.flip hk1 hk2 ha hb).pt k = W.c * gpt (W.v k - (1, 1)) := by
  show (W.flip hk1 hk2 ha hb).c * gpt ((W.flip hk1 hk2 ha hb).v k) = W.c * gpt (W.v k - (1, 1))
  rw [LWalk.flip_c, LWalk.flip_v_self]

/-- Segments with equal endpoints have equal values. -/
theorem segment_congr_points {a b a' b' : ℂ} (e1 : a = a') (e2 : b = b') (t : unitInterval) :
    Path.segment a b t = Path.segment a' b' t := by
  rw [Path.segment_apply, Path.segment_apply, e1, e2]

/-- A clamped lifted edge, in the form of a cast of the lifted straight segment between its
endpoints. -/
theorem edgeUNat_eq_cast_segIn {U B : Set ℂ} {hB : Convex ℝ B} {hBU : B ⊆ U} {W : LWalk}
    {hval : ∀ t, W.path t ∈ U} {j : ℕ} (hj : j < W.n)
    (ha : W.pt j ∈ B) (hb : W.pt (j + 1) ∈ B) :
    W.edgeUNat hval j = Path.cast (segIn hB hBU ha hb)
      (W.ptMin_eq_ptU hval j (le_of_lt hj))
      (W.ptMin_eq_ptU hval (j + 1) (Nat.succ_le_of_lt hj)) := by
  have h := edgeUNat_eq_segIn (hB := hB) (hBU := hBU) (hval := hval) hj ha hb
  have h2 := congrArg (fun γ => γ.cast (W.ptMin_eq_ptU hval j (le_of_lt hj))
    (W.ptMin_eq_ptU hval (j + 1) (Nat.succ_le_of_lt hj))) h
  rw [Path.cast_cast, Path.cast_self] at h2
  exact h2

/-! ### The two-edge middle piece -/

/-- **The middle piece of the corner move.**  Cast to the endpoints of the original walk, the two
edges of the flipped walk at the corner are equal (as paths in `↥U`) to the two straight segments
through the opposite corner of the corner cell. -/
theorem flip_mid_eq {U B : Set ℂ} {W : LWalk} {hval : ∀ t, W.path t ∈ U} {k : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ W.n)
    (ha : W.v (k - 1) = W.v k - (1, 0) ∨ W.v (k - 1) = W.v k - (0, 1))
    (hb : W.v (k + 1) = W.v k - (1, 0) ∨ W.v (k + 1) = W.v k - (0, 1))
    {hB : Convex ℝ B} {hBU : B ⊆ U}
    (hval' : ∀ t, (W.flip hk1 hk2 ha hb).path t ∈ U)
    (haB : W.pt (k - 1) ∈ B) (hsB : W.c * gpt (W.v k - (1, 1)) ∈ B)
    (hbB : W.pt (k - 1 + 2) ∈ B)
    (hx : W.ptMin hval (k - 1) = (⟨W.pt (k - 1), hBU haB⟩ : ↥U))
    (hy : W.ptMin hval ((k - 1 + 1) + 1) = (⟨W.pt (k - 1 + 2), hBU hbB⟩ : ↥U))
    (e1 : W.ptMin hval (k - 1) = (W.flip hk1 hk2 ha hb).ptMin hval' (k - 1))
    (e2 : W.ptMin hval (k - 1 + 2) = (W.flip hk1 hk2 ha hb).ptMin hval' (k - 1 + 2)) :
    Path.cast (((W.flip hk1 hk2 ha hb).edgeUNat hval' (k - 1)).trans
        ((W.flip hk1 hk2 ha hb).edgeUNat hval' (k - 1 + 1))) e1 e2
      = Path.cast ((segIn hB hBU haB hsB).trans (segIn hB hBU hsB hbB)) hx hy := by
  have hpt1 : (W.flip hk1 hk2 ha hb).pt (k - 1) = W.pt (k - 1) :=
    flip_pt_of_ne hk1 hk2 ha hb (by omega)
  have hpt2 : (W.flip hk1 hk2 ha hb).pt (k - 1 + 1) = W.c * gpt (W.v k - (1, 1)) := by
    rw [show k - 1 + 1 = k from by omega]
    exact flip_pt_self hk1 hk2 ha hb
  have hpt3 : (W.flip hk1 hk2 ha hb).pt ((k - 1 + 1) + 1) = W.pt ((k - 1 + 1) + 1) :=
    flip_pt_of_ne hk1 hk2 ha hb (by omega)
  have hfle : k - 1 < (W.flip hk1 hk2 ha hb).n := by rw [LWalk.flip_n]; omega
  have hfle2 : k - 1 + 1 < (W.flip hk1 hk2 ha hb).n := by rw [LWalk.flip_n]; omega
  apply Path.ext
  funext t
  apply Subtype.ext
  rw [path_cast_apply, path_cast_apply, Path.trans_apply, Path.trans_apply]
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [dif_pos ht, dif_pos ht, LWalk.edgeUNat_apply, dif_pos hfle, segIn_apply]
    simp only [LWalk.edge, segPath, Path.segment_apply]
    rw [hpt1, hpt2]
  · rw [dif_neg ht, dif_neg ht, LWalk.edgeUNat_apply, dif_pos hfle2, segIn_apply]
    simp only [LWalk.edge, segPath, Path.segment_apply]
    rw [hpt2, hpt3]


/-- **The corner move at the two-edge middle piece of the loop.** -/
theorem flip_mid_homotopic {U : Set ℂ} {W : LWalk} {hval : ∀ t, W.path t ∈ U} {k : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ W.n)
    (ha : W.v (k - 1) = W.v k - (1, 0) ∨ W.v (k - 1) = W.v k - (0, 1))
    (hb : W.v (k + 1) = W.v k - (1, 0) ∨ W.v (k + 1) = W.v k - (0, 1))
    (hBU : cellCl W.c (W.v k - (1, 1)) ⊆ U)
    (hval' : ∀ t, (W.flip hk1 hk2 ha hb).path t ∈ U)
    (e1 : W.ptMin hval (k - 1) = (W.flip hk1 hk2 ha hb).ptMin hval' (k - 1))
    (e2 : W.ptMin hval (k - 1 + 2) = (W.flip hk1 hk2 ha hb).ptMin hval' (k - 1 + 2)) :
    Path.Homotopic ((W.edgeUNat hval (k - 1)).trans (W.edgeUNat hval (k - 1 + 1)))
      (Path.cast (((W.flip hk1 hk2 ha hb).edgeUNat hval' (k - 1)).trans
        ((W.flip hk1 hk2 ha hb).edgeUNat hval' (k - 1 + 1))) e1 e2) := by
  have hB : Convex ℝ (cellCl W.c (W.v k - (1, 1))) := convex_cellCl W.c W.cpos (W.v k - (1, 1))
  have hBne : (cellCl W.c (W.v k - (1, 1))).Nonempty :=
    ⟨_, smul_gpt_mem_cellCl W.c W.cpos (W.v k - (1, 1))⟩
  have hsB : W.c * gpt (W.v k - (1, 1)) ∈ cellCl W.c (W.v k - (1, 1)) :=
    smul_gpt_mem_cellCl W.c W.cpos (W.v k - (1, 1))
  have haB : W.pt (k - 1) ∈ cellCl W.c (W.v k - (1, 1)) := by
    show W.c * gpt (W.v (k - 1)) ∈ cellCl W.c (W.v k - (1, 1))
    rcases ha with ha | ha
    · rw [ha]
      have h := smul_gpt_add_zero_one_mem_cellCl W.c W.cpos (W.v k - (1, 1))
      rwa [show (W.v k - (1, 1)) + (0, 1) = W.v k - (1, 0) from by ext <;> simp] at h
    · rw [ha]
      have h := smul_gpt_add_one_zero_mem_cellCl W.c W.cpos (W.v k - (1, 1))
      rwa [show (W.v k - (1, 1)) + (1, 0) = W.v k - (0, 1) from by ext <;> simp] at h
  have hpB : W.pt (k - 1 + 1) ∈ cellCl W.c (W.v k - (1, 1)) := by
    show W.c * gpt (W.v (k - 1 + 1)) ∈ cellCl W.c (W.v k - (1, 1))
    rw [show k - 1 + 1 = k from by omega]
    have h := smul_gpt_add_one_one_mem_cellCl W.c W.cpos (W.v k - (1, 1))
    rwa [show (W.v k - (1, 1)) + (1, 1) = W.v k from by ext <;> simp] at h
  have hbB : W.pt (k - 1 + 2) ∈ cellCl W.c (W.v k - (1, 1)) := by
    show W.c * gpt (W.v (k - 1 + 2)) ∈ cellCl W.c (W.v k - (1, 1))
    rw [show k - 1 + 2 = k + 1 from by omega]
    rcases hb with hb | hb
    · rw [hb]
      have h := smul_gpt_add_zero_one_mem_cellCl W.c W.cpos (W.v k - (1, 1))
      rwa [show (W.v k - (1, 1)) + (0, 1) = W.v k - (1, 0) from by ext <;> simp] at h
    · rw [hb]
      have h := smul_gpt_add_one_zero_mem_cellCl W.c W.cpos (W.v k - (1, 1))
      rwa [show (W.v k - (1, 1)) + (1, 0) = W.v k - (0, 1) from by ext <;> simp] at h
  have hx : W.ptMin hval (k - 1) = (⟨W.pt (k - 1), hBU haB⟩ : ↥U) :=
    (W.ptMin_eq_ptU hval (k - 1) (by omega)).trans (Subtype.ext rfl)
  have hy : W.ptMin hval ((k - 1 + 1) + 1) = (⟨W.pt (k - 1 + 2), hBU hbB⟩ : ↥U) :=
    (W.ptMin_eq_ptU hval ((k - 1 + 1) + 1) (by omega)).trans (Subtype.ext rfl)
  have hcorner := edgeUNat_pair_corner_homotopic (B := cellCl W.c (W.v k - (1, 1)))
    (hB := hB) (hBU := hBU) (hval := hval) (j := k - 1) (by omega) (by omega) hBne
    (s := W.c * gpt (W.v k - (1, 1))) haB hpB hbB hsB
  have hmid := flip_mid_eq (B := cellCl W.c (W.v k - (1, 1))) (hB := hB) (hBU := hBU)
    hk1 hk2 ha hb hval' haB hsB hbB hx hy e1 e2
  have hcast : Path.cast ((segIn hB hBU haB hsB).trans (segIn hB hBU hsB hbB))
        (W.ptMin_eq_ptU hval (k - 1) (by omega))
        (W.ptMin_eq_ptU hval ((k - 1 + 1) + 1) (by omega))
      = Path.cast ((segIn hB hBU haB hsB).trans (segIn hB hBU hsB hbB)) hx hy :=
    path_cast_proof_irrel _ _ _ _ _
  rw [hmid]
  exact hcast ▸ hcorner



/-! ### The corner move of the join -/

/-- **The corner move of the join.**  The join of the clamped lifted edges of `W` is homotopic, in
`↥U`, to the join of the clamped lifted edges of the flipped walk, the two paths being compared
through the endpoint equalities `e0`, `en`. -/
theorem flip_joinNat_homotopic {U : Set ℂ} {W : LWalk} {hval : ∀ t, W.path t ∈ U} {k : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ W.n)
    (ha : W.v (k - 1) = W.v k - (1, 0) ∨ W.v (k - 1) = W.v k - (0, 1))
    (hb : W.v (k + 1) = W.v k - (1, 0) ∨ W.v (k + 1) = W.v k - (0, 1))
    (hBU : cellCl W.c (W.v k - (1, 1)) ⊆ U)
    (hval' : ∀ t, (W.flip hk1 hk2 ha hb).path t ∈ U)
    (e0 : W.ptMin hval 0 = (W.flip hk1 hk2 ha hb).ptMin hval' 0)
    (en : W.ptMin hval W.n = (W.flip hk1 hk2 ha hb).ptMin hval' W.n) :
    Path.Homotopic (joinNat (W.edgeUNat hval) W.n)
      (Path.cast (joinNat ((W.flip hk1 hk2 ha hb).edgeUNat hval') W.n) e0 en) := by
  have hindex : W.n = k - 1 + (2 + (W.n - (k - 1 + 2))) := by omega
  have hpre : joinNat (W.edgeUNat hval) (k - 1)
      = Path.cast (joinNat ((W.flip hk1 hk2 ha hb).edgeUNat hval') (k - 1))
          e0 (flip_ptMin_eq hk1 hk2 ha hb hval' (by omega) (by omega)) :=
    joinNat_cast_bound (J := k - 1)
      (h := fun j hj => flip_ptMin_eq hk1 hk2 ha hb hval' (by omega) (by omega))
      (F := W.edgeUNat hval) (G := (W.flip hk1 hk2 ha hb).edgeUNat hval')
      (hFG := fun j hj =>
        (flip_edgeUNat_eq hk1 hk2 ha hb hval' (by omega) (by omega) (by omega)).symm)
      (k - 1) le_rfl
  have hsuf : joinNat (p := fun l => W.ptMin hval (k - 1 + (2 + l)))
        (fun l => W.edgeUNat hval (k - 1 + (2 + l))) (W.n - (k - 1 + 2))
      = Path.cast (joinNat (p := fun l => (W.flip hk1 hk2 ha hb).ptMin hval' (k - 1 + (2 + l)))
          (fun l => (W.flip hk1 hk2 ha hb).edgeUNat hval' (k - 1 + (2 + l)))
          (W.n - (k - 1 + 2)))
          (flip_ptMin_eq hk1 hk2 ha hb hval' (by omega) (by omega))
          (flip_ptMin_eq hk1 hk2 ha hb hval' (by omega) (by omega)) :=
    joinNat_cast_bound (J := W.n - (k - 1 + 2))
      (h := fun l hl => flip_ptMin_eq hk1 hk2 ha hb hval' (by omega) (by omega))
      (F := fun l => W.edgeUNat hval (k - 1 + (2 + l)))
      (G := fun l => (W.flip hk1 hk2 ha hb).edgeUNat hval' (k - 1 + (2 + l)))
      (hFG := fun l hl =>
        (flip_edgeUNat_eq hk1 hk2 ha hb hval' (by omega) (by omega) (by omega)).symm)
      (W.n - (k - 1 + 2)) le_rfl
  have hmid := flip_mid_homotopic (hval := hval) hk1 hk2 ha hb hBU hval'
    (flip_ptMin_eq hk1 hk2 ha hb hval' (by omega) (by omega))
    (flip_ptMin_eq hk1 hk2 ha hb hval' (by omega) (by omega))
  have hmain := joinNat_replace_pair
    (F := W.edgeUNat hval) (G := (W.flip hk1 hk2 ha hb).edgeUNat hval')
    (i := k - 1) (m := W.n - (k - 1 + 2))
    e0 (flip_ptMin_eq hk1 hk2 ha hb hval' (by omega) (by omega))
    (flip_ptMin_eq hk1 hk2 ha hb hval' (by omega) (by omega))
    (flip_ptMin_eq hk1 hk2 ha hb hval' (by omega) (by omega))
    hpre hsuf hmid
  have hFn : joinNat (W.edgeUNat hval) W.n
      = Path.cast (joinNat (W.edgeUNat hval) (k - 1 + (2 + (W.n - (k - 1 + 2))))) rfl
          (congrArg (W.ptMin hval) hindex) :=
    joinNat_of_eq (W.edgeUNat hval) hindex
  have hGn : joinNat ((W.flip hk1 hk2 ha hb).edgeUNat hval') W.n
      = Path.cast (joinNat ((W.flip hk1 hk2 ha hb).edgeUNat hval')
            (k - 1 + (2 + (W.n - (k - 1 + 2))))) rfl
          (congrArg ((W.flip hk1 hk2 ha hb).ptMin hval') hindex) :=
    joinNat_of_eq ((W.flip hk1 hk2 ha hb).edgeUNat hval') hindex
  rw [hFn, hGn, Path.cast_cast]
  have hstep := Path.Homotopic.pathCast hmain rfl (congrArg (W.ptMin hval) hindex)
  rw [Path.cast_cast] at hstep
  refine hstep.trans (path_homotopic_of_eq ?_)
  exact path_cast_proof_irrel _ _ _ _ _


/-! ### The target -/

theorem flip_loop_homotopic {U : Set ℂ} {W : LWalk} {hval : ∀ t, W.path t ∈ U} {k : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ W.n)
    (ha : W.v (k - 1) = W.v k - (1, 0) ∨ W.v (k - 1) = W.v k - (0, 1))
    (hb : W.v (k + 1) = W.v k - (1, 0) ∨ W.v (k + 1) = W.v k - (0, 1))
    (hcU : cellCl W.c (W.v k - (1, 1)) ⊆ U)
    (hval' : ∀ t, (W.flip hk1 hk2 ha hb).path t ∈ U)
    (he : W.ptMin hval 0 = (W.flip hk1 hk2 ha hb).ptMin hval' 0) :
    Path.Homotopic (W.loopNat hval)
      (Path.cast ((W.flip hk1 hk2 ha hb).loopNat hval') he he) := by
  have hen : W.ptMin hval W.n = (W.flip hk1 hk2 ha hb).ptMin hval' W.n :=
    flip_ptMin_eq hk1 hk2 ha hb hval' le_rfl (by omega)
  have hjoin := flip_joinNat_homotopic hk1 hk2 ha hb hcU hval' he hen
  have hyA : W.ptMin hval 0 = W.ptMin hval W.n := W.ptMin_zero_eq_last hval
  have he' : W.ptMin hval 0
      = (W.flip hk1 hk2 ha hb).ptU hval' 0 (Nat.zero_le (W.flip hk1 hk2 ha hb).n) :=
    he.trans ((W.flip hk1 hk2 ha hb).ptMin_eq_ptU hval' 0
      (Nat.zero_le (W.flip hk1 hk2 ha hb).n))
  have hxB : (W.flip hk1 hk2 ha hb).ptU hval' 0 (Nat.zero_le (W.flip hk1 hk2 ha hb).n)
      = (W.flip hk1 hk2 ha hb).ptMin hval' 0 :=
    ((W.flip hk1 hk2 ha hb).ptMin_eq_ptU hval' 0
      (Nat.zero_le (W.flip hk1 hk2 ha hb).n)).symm
  have hyB : (W.flip hk1 hk2 ha hb).ptMin hval' 0
      = (W.flip hk1 hk2 ha hb).ptMin hval' W.n :=
    (W.flip hk1 hk2 ha hb).ptMin_zero_eq_last hval'
  have hstep : Path.Homotopic
      (Path.cast (joinNat (W.edgeUNat hval) W.n)
        (rfl : W.ptMin hval 0 = W.ptMin hval 0) hyA)
      (Path.cast (Path.cast (joinNat ((W.flip hk1 hk2 ha hb).edgeUNat hval') W.n)
        hxB hyB) he' he) := by
    refine (Path.Homotopic.pathCast hjoin rfl hyA).trans (path_homotopic_of_eq ?_)
    rw [Path.cast_cast, Path.cast_cast]
  exact hstep

end

end Work.Smooth.JordanSeparation
