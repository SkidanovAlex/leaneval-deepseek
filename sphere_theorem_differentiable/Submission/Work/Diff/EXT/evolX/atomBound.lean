import Mathlib
import Submission.Work.Diff.EXT.evolX.ladderAtoms
import Submission.Work.Diff.EXT.laplAt_curvNormK_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.evolX

/-- **The level bound for an atom of the ladder.**

`Atom g W m l s κ ξ F x` is the value at `x` of the level-`m` tower `∇^m Rm` evaluated on the tuple
whose slot `s` carries the level-`l` curvature vector `Zf g W l (F ∘ ξ)` and whose remaining slots
carry the tuple entries `F (κ i)` (`κ`, `ξ` are a partition of the tuple positions, `GoodDataN`).

The tower `∇^m Rm` is a multilinear form of Hilbert–Schmidt norm `√(curvNormK g x m)`
(`ckt_norm_le`), and the curvature vector `Zf g W l Ψ x = ∑ i, ckt g l (snoc Ψ (W i)) x • W i x` is a
linear combination of the `finrank` frame vectors with coefficients `ckt g l (snoc Ψ (W i)) x`, each
of Hilbert–Schmidt norm `√(curvNormK g x l)` times the product of the norms of `Ψ`.  Hence the atom
is bounded by `finrank · √f_l · √f_m · ∏ ‖F u‖ ≤ finrank · Shape (m+l) · ∏ ‖F u‖`.

The proof is the sharp (constant `1`) evaluation bound in an orthonormal frame: expand `Zf` in the
frame, apply `ckt_norm_le` at the two levels, and use that the frame is orthonormal at `x`
(`gNrm g x (W i x) = 1`), so that the products over the frame index and over the tuple positions
recombine into `∏ u, gNrm g x (F u x)` (`prod_split_of_goodDataN`). -/
theorem atomBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hW : ∀ i, Work.Diff.EXT.evolX.SmTf (I := I) (M := M) (W i))
    (hON : Work.Diff.EXT.evolX.ONFrameAt (I := I) (M := M) g x W)
    (m l N : ℕ) (s : Fin (m + 4))
    (κ : Fin (m + 4) → Fin N) (ξ : Fin (l + 3) → Fin N)
    (hgood : Work.Diff.EXT.evolX.GoodDataN m l N s κ ξ)
    (F : Fin N → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ u, Work.Diff.EXT.evolX.SmTf (I := I) (M := M) (F u)) :
    |Work.Diff.EXT.evolX.Atom (I := I) (M := M) g W m l N s κ ξ F x|
      ≤ (Module.finrank ℝ E : ℝ) * Work.Diff.EXT.Shape g x (m + l)
          * ∏ r : Fin N, Work.Diff.EXT.gNrm g x (F r x) := by
  classical
  -- ## Step 0: elementary facts
  have hONx : Submission.Diff.IsONFrame g x (fun i => W i x) := hON.self_of_nhds
  have hUnit : ∀ i : Fin (Module.finrank ℝ E), Work.Diff.EXT.gNrm g x (W i x) = 1 := by
    intro i
    show Real.sqrt (g.inner x (W i x) (W i x)) = 1
    rw [hONx i i, if_pos rfl, Real.sqrt_one]
  have hite : ∀ {c : Prop} [Decidable c]
      (A B : Work.Diff.EXT.TField (I := I) (M := M)) (y : M),
      (if c then A else B) y = if c then A y else B y := by
    intro c _ A B y
    by_cases h : c <;> simp [h]
  -- ## Step 1: the tuple of the atom, written with `Function.update`
  have hAtom_fun : Work.Diff.EXT.evolX.Atom (I := I) (M := M) g W m l N s κ ξ F
      = Work.Diff.EXT.ckt g m (Function.update (fun j : Fin (m + 4) => F (κ j)) s
          (Zf (I := I) (M := M) g W l (fun r : Fin (l + 3) => F (ξ r)))) := by
    funext y
    show Work.Diff.EXT.ckt g m (fun i : Fin (m + 4) => if i = s then
        Zf (I := I) (M := M) g W l (fun r : Fin (l + 3) => F (ξ r)) else F (κ i)) y
      = Work.Diff.EXT.ckt g m (Function.update (fun j : Fin (m + 4) => F (κ j)) s
          (Zf (I := I) (M := M) g W l (fun r : Fin (l + 3) => F (ξ r)))) y
    congr 1
    funext i
    rw [Function.update_apply]
  -- ## Step 2: `Zf` is smooth
  have hZf_sm : Work.Diff.GE.SmoothFieldT (I := I) (M := M)
      (Zf (I := I) (M := M) g W l (fun r : Fin (l + 3) => F (ξ r))) := by
    refine ContMDiff.sum_section (s := Finset.univ)
      (t := fun (i : Fin (Module.finrank ℝ E)) (y : M) =>
        (Work.Diff.EXT.ckt g l (Fin.snoc (fun r : Fin (l + 3) => F (ξ r)) (W i)) y)
          • W i y) ?_
    intro i _
    exact ((Work.Diff.EXT.tensProp_all hLC g l
        (Fin.snoc (fun r : Fin (l + 3) => F (ξ r)) (W i))
        (fun r => by
          rcases Fin.eq_castSucc_or_eq_last r with ⟨r', rfl⟩ | rfl
          · rw [Fin.snoc_castSucc]; exact hF (ξ r')
          · rw [Fin.snoc_last]; exact hW i)).1).smul_section (hW i)
  -- ## Step 3: the tuple of the atom is smooth
  have hG_sm : ∀ i : Fin (m + 4), Work.Diff.EXT.SmoothF
      ((Function.update (fun j : Fin (m + 4) => F (κ j)) s
        (Zf (I := I) (M := M) g W l (fun r : Fin (l + 3) => F (ξ r)))) i) := by
    intro i
    rw [Function.update_apply]
    by_cases h : i = s
    · rw [if_pos h]; exact hZf_sm
    · rw [if_neg h]; exact hF (κ i)
  -- ## Step 4: the atom is the value-level evaluation of the tower on the tuple of values
  have hKpt : Work.Diff.EXT.evolX.Atom (I := I) (M := M) g W m l N s κ ξ F x
      = Work.Diff.EXT.Kpt g x m (Function.update (fun j : Fin (m + 4) => F (κ j) x) s
          (Zf (I := I) (M := M) g W l (fun r : Fin (l + 3) => F (ξ r)) x)) := by
    rw [hAtom_fun]
    rw [Work.Diff.EXT.ckt_eq_Kpt' hLC g m x hG_sm]
    congr 1
    funext i
    rw [Function.update_apply, Function.update_apply, hite]
  -- ## Step 4b: value-level linearity of `Kpt` in one slot (for a sum of smuls)
  have hKptSumSlot : ∀ (k : ℕ) (w : Fin (k + 4) → TangentSpace I x) (s : Fin (k + 4))
      (c : Fin (Module.finrank ℝ E) → ℝ) (Y : Fin (Module.finrank ℝ E) → TangentSpace I x),
      Work.Diff.EXT.Kpt g x k (Function.update w s (∑ i, c i • Y i))
        = ∑ i, c i • Work.Diff.EXT.Kpt g x k (Function.update w s (Y i)) := by
    intro k w s c Y
    classical
    have key : ∀ t : Finset (Fin (Module.finrank ℝ E)),
        Work.Diff.EXT.Kpt g x k (Function.update w s (∑ i ∈ t, c i • Y i))
          = ∑ i ∈ t, c i • Work.Diff.EXT.Kpt g x k (Function.update w s (Y i)) := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        have h := Work.Diff.EXT.Kpt_smul hLC g x k w s (0 : ℝ) (w s)
        simpa using h
      | insert a t ha ih =>
        have hsum : (∑ i ∈ insert a t, c i • Y i) = c a • Y a + ∑ i ∈ t, c i • Y i := by
          rw [Finset.sum_insert ha]
        have step : Work.Diff.EXT.Kpt g x k
            (Function.update w s (c a • Y a + ∑ i ∈ t, c i • Y i))
            = Work.Diff.EXT.Kpt g x k (Function.update w s (c a • Y a))
              + Work.Diff.EXT.Kpt g x k (Function.update w s (∑ i ∈ t, c i • Y i)) :=
          Work.Diff.EXT.Kpt_add hLC g x k w s (c a • Y a) (∑ i ∈ t, c i • Y i)
        have step2 : Work.Diff.EXT.Kpt g x k (Function.update w s (c a • Y a))
            = c a • Work.Diff.EXT.Kpt g x k (Function.update w s (Y a)) :=
          Work.Diff.EXT.Kpt_smul hLC g x k w s (c a) (Y a)
        rw [hsum, step, step2, ih, Finset.sum_insert ha]
    simpa using key Finset.univ
  -- ## Step 5: expand the curvature vector in the orthonormal frame
  have hExp : Work.Diff.EXT.Kpt g x m (Function.update (fun j : Fin (m + 4) => F (κ j) x) s
        (Zf (I := I) (M := M) g W l (fun r : Fin (l + 3) => F (ξ r)) x))
      = ∑ i : Fin (Module.finrank ℝ E),
          (Work.Diff.EXT.ckt g l (Fin.snoc (fun r : Fin (l + 3) => F (ξ r)) (W i)) x)
            * Work.Diff.EXT.Kpt g x m
                (Function.update (fun j : Fin (m + 4) => F (κ j) x) s (W i x)) := by
    rw [show Zf (I := I) (M := M) g W l (fun r : Fin (l + 3) => F (ξ r)) x
        = ∑ i : Fin (Module.finrank ℝ E),
            (Work.Diff.EXT.ckt g l (Fin.snoc (fun r : Fin (l + 3) => F (ξ r)) (W i)) x)
              • (W i x) from rfl]
    simpa only [smul_eq_mul] using
      (hKptSumSlot m (fun j : Fin (m + 4) => F (κ j) x) s
        (fun i => Work.Diff.EXT.ckt g l (Fin.snoc (fun r : Fin (l + 3) => F (ξ r)) (W i)) x)
        (fun i => W i x))
  -- ## Step 6: the bound for a single summand
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      |(Work.Diff.EXT.ckt g l (Fin.snoc (fun r : Fin (l + 3) => F (ξ r)) (W i)) x)
        * Work.Diff.EXT.Kpt g x m
            (Function.update (fun j : Fin (m + 4) => F (κ j) x) s (W i x))|
      ≤ Real.sqrt (Work.Diff.EXT.curvNormK g x m) * Real.sqrt (Work.Diff.EXT.curvNormK g x l)
        * ((∏ r : Fin (l + 3), Work.Diff.EXT.gNrm g x (F (ξ r) x))
          * (∏ j ∈ Finset.univ.erase s, Work.Diff.EXT.gNrm g x (F (κ j) x))) := by
    intro i
    have hSnoc : ∀ r : Fin (l + 4), Work.Diff.EXT.SmoothF
        ((Fin.snoc (fun r : Fin (l + 3) => F (ξ r)) (W i) :
          Fin (l + 4) → Work.Diff.EXT.TField (I := I) (M := M)) r) := by
      intro r
      rcases Fin.eq_castSucc_or_eq_last r with ⟨r', rfl⟩ | rfl
      · rw [Fin.snoc_castSucc]; exact hF (ξ r')
      · rw [Fin.snoc_last]; exact hW i
    have hUpd : ∀ j : Fin (m + 4), Work.Diff.EXT.SmoothF
        ((Function.update (fun j : Fin (m + 4) => F (κ j)) s (W i)) j) := by
      intro j
      rw [Function.update_apply]
      by_cases h : j = s
      · rw [if_pos h]; exact hW i
      · rw [if_neg h]; exact hF (κ j)
    have hA := Work.Diff.EXT.ckt_norm_le hLC g x l
      (Fin.snoc (fun r : Fin (l + 3) => F (ξ r)) (W i)) hSnoc
    have hB := Work.Diff.EXT.ckt_norm_le hLC g x m
      (Function.update (fun j : Fin (m + 4) => F (κ j)) s (W i)) hUpd
    rw [Work.Diff.EXT.ckt_eq_Kpt' hLC g m x hUpd] at hB
    rw [show (fun j : Fin (m + 4) =>
          (Function.update (fun j : Fin (m + 4) => F (κ j)) s (W i)) j x)
        = Function.update (fun j : Fin (m + 4) => F (κ j) x) s (W i x) from by
          funext j
          rw [Function.update_apply, Function.update_apply, hite]] at hB
    have hAv : |Work.Diff.EXT.ckt g l (Fin.snoc (fun r : Fin (l + 3) => F (ξ r)) (W i)) x|
        ≤ Real.sqrt (Work.Diff.EXT.curvNormK g x l)
          * (∏ r : Fin (l + 3), Work.Diff.EXT.gNrm g x (F (ξ r) x)) := by
      refine hA.trans_eq ?_
      rw [show (∏ r : Fin (l + 4),
            Work.Diff.EXT.gNrm g x ((Fin.snoc (fun r : Fin (l + 3) => F (ξ r)) (W i) :
              Fin (l + 4) → Work.Diff.EXT.TField (I := I) (M := M)) r x))
          = (∏ r : Fin (l + 3), Work.Diff.EXT.gNrm g x (F (ξ r) x)) from by
            rw [Fin.prod_univ_castSucc]
            simp only [Fin.snoc_castSucc, Fin.snoc_last, hUnit i, mul_one]]
    have hBv : |Work.Diff.EXT.Kpt g x m
          (Function.update (fun j : Fin (m + 4) => F (κ j) x) s (W i x))|
        ≤ Real.sqrt (Work.Diff.EXT.curvNormK g x m)
          * (∏ j ∈ Finset.univ.erase s, Work.Diff.EXT.gNrm g x (F (κ j) x)) := by
      refine hB.trans_eq ?_
      rw [show (∏ j : Fin (m + 4),
            Work.Diff.EXT.gNrm g x
              ((Function.update (fun j : Fin (m + 4) => F (κ j)) s (W i)) j x))
          = (∏ j ∈ Finset.univ.erase s, Work.Diff.EXT.gNrm g x (F (κ j) x)) from by
            rw [← Finset.mul_prod_erase Finset.univ
              (fun j : Fin (m + 4) => Work.Diff.EXT.gNrm g x
                ((Function.update (fun j : Fin (m + 4) => F (κ j)) s (W i)) j x))
              (Finset.mem_univ s)]
            rw [Function.update_self, hUnit i, one_mul]
            refine Finset.prod_congr rfl (fun j hj => ?_)
            rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]]
    have hAnn : 0 ≤ Real.sqrt (Work.Diff.EXT.curvNormK g x l)
        * (∏ r : Fin (l + 3), Work.Diff.EXT.gNrm g x (F (ξ r) x)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Finset.prod_nonneg (fun r _ => Real.sqrt_nonneg _))
    calc |(Work.Diff.EXT.ckt g l (Fin.snoc (fun r : Fin (l + 3) => F (ξ r)) (W i)) x)
          * Work.Diff.EXT.Kpt g x m
              (Function.update (fun j : Fin (m + 4) => F (κ j) x) s (W i x))|
        = |Work.Diff.EXT.ckt g l (Fin.snoc (fun r : Fin (l + 3) => F (ξ r)) (W i)) x|
          * |Work.Diff.EXT.Kpt g x m
              (Function.update (fun j : Fin (m + 4) => F (κ j) x) s (W i x))| :=
          abs_mul _ _
      _ ≤ (Real.sqrt (Work.Diff.EXT.curvNormK g x l)
            * (∏ r : Fin (l + 3), Work.Diff.EXT.gNrm g x (F (ξ r) x)))
          * (Real.sqrt (Work.Diff.EXT.curvNormK g x m)
            * (∏ j ∈ Finset.univ.erase s, Work.Diff.EXT.gNrm g x (F (κ j) x))) :=
          mul_le_mul hAv hBv (abs_nonneg _) hAnn
      _ = Real.sqrt (Work.Diff.EXT.curvNormK g x m) * Real.sqrt (Work.Diff.EXT.curvNormK g x l)
          * ((∏ r : Fin (l + 3), Work.Diff.EXT.gNrm g x (F (ξ r) x))
            * (∏ j ∈ Finset.univ.erase s, Work.Diff.EXT.gNrm g x (F (κ j) x))) := by
          ring
  -- ## Step 7: the product identity from `GoodDataN`
  have hsplit : (∏ u : Fin N, Work.Diff.EXT.gNrm g x (F u x))
      = (∏ j ∈ Finset.univ.erase s, Work.Diff.EXT.gNrm g x (F (κ j) x))
        * (∏ r : Fin (l + 3), Work.Diff.EXT.gNrm g x (F (ξ r) x)) := by
    have h := prod_split_of_goodDataN (m := m) (l := l) (N := N) (s := s) (κ := κ) (ξ := ξ)
      hgood (fun u : Fin N => Work.Diff.EXT.gNrm g x (F u x))
    simpa only using h
  have hAB : (∏ r : Fin (l + 3), Work.Diff.EXT.gNrm g x (F (ξ r) x))
      * (∏ j ∈ Finset.univ.erase s, Work.Diff.EXT.gNrm g x (F (κ j) x))
      = ∏ u : Fin N, Work.Diff.EXT.gNrm g x (F u x) := by
    rw [hsplit]
    exact mul_comm _ _
  have hABnn : 0 ≤ (∏ r : Fin (l + 3), Work.Diff.EXT.gNrm g x (F (ξ r) x))
      * (∏ j ∈ Finset.univ.erase s, Work.Diff.EXT.gNrm g x (F (κ j) x)) :=
    mul_nonneg (Finset.prod_nonneg (fun r _ => Real.sqrt_nonneg _))
      (Finset.prod_nonneg (fun j _ => Real.sqrt_nonneg _))
  -- ## Step 8: assemble
  rw [hKpt, hExp]
  calc |∑ i : Fin (Module.finrank ℝ E),
          (Work.Diff.EXT.ckt g l (Fin.snoc (fun r : Fin (l + 3) => F (ξ r)) (W i)) x)
            * Work.Diff.EXT.Kpt g x m
                (Function.update (fun j : Fin (m + 4) => F (κ j) x) s (W i x))|
      ≤ ∑ i : Fin (Module.finrank ℝ E),
          |(Work.Diff.EXT.ckt g l (Fin.snoc (fun r : Fin (l + 3) => F (ξ r)) (W i)) x)
            * Work.Diff.EXT.Kpt g x m
                (Function.update (fun j : Fin (m + 4) => F (κ j) x) s (W i x))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (Module.finrank ℝ E),
          Real.sqrt (Work.Diff.EXT.curvNormK g x m) * Real.sqrt (Work.Diff.EXT.curvNormK g x l)
            * ((∏ r : Fin (l + 3), Work.Diff.EXT.gNrm g x (F (ξ r) x))
              * (∏ j ∈ Finset.univ.erase s, Work.Diff.EXT.gNrm g x (F (κ j) x))) :=
          Finset.sum_le_sum (fun i _ => hterm i)
    _ = (Module.finrank ℝ E : ℝ)
          * (Real.sqrt (Work.Diff.EXT.curvNormK g x m) * Real.sqrt (Work.Diff.EXT.curvNormK g x l)
            * ((∏ r : Fin (l + 3), Work.Diff.EXT.gNrm g x (F (ξ r) x))
              * (∏ j ∈ Finset.univ.erase s, Work.Diff.EXT.gNrm g x (F (κ j) x)))) := by
          rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    _ = ((Module.finrank ℝ E : ℝ)
          * (Real.sqrt (Work.Diff.EXT.curvNormK g x m) * Real.sqrt (Work.Diff.EXT.curvNormK g x l)))
          * ((∏ r : Fin (l + 3), Work.Diff.EXT.gNrm g x (F (ξ r) x))
              * (∏ j ∈ Finset.univ.erase s, Work.Diff.EXT.gNrm g x (F (κ j) x))) := by
          ring
    _ ≤ ((Module.finrank ℝ E : ℝ) * Work.Diff.EXT.Shape g x (m + l))
          * ((∏ r : Fin (l + 3), Work.Diff.EXT.gNrm g x (F (ξ r) x))
              * (∏ j ∈ Finset.univ.erase s, Work.Diff.EXT.gNrm g x (F (κ j) x))) := by
          refine mul_le_mul_of_nonneg_right ?_ hABnn
          exact mul_le_mul_of_nonneg_left
            (Work.Diff.EXT.sqrt_mul_sqrt_le_Shape g x (a := m) (b := l) (m := m + l) rfl)
            (by positivity)
    _ = (Module.finrank ℝ E : ℝ) * Work.Diff.EXT.Shape g x (m + l)
          * ∏ r : Fin N, Work.Diff.EXT.gNrm g x (F r x) := by
          rw [hAB]

end Work.Diff.EXT.evolX
