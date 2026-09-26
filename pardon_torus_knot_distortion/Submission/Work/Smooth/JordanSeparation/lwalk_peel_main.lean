import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_peel_aux
import Submission.Work.Smooth.JordanSeparation.seamFlip_free_homotopic

/-!
# The peel: every closed lattice walk inside `U` is null-homotopic in `U`

Strong induction on `peelMeasure N` (see `lwalk_measure.lean`): the base case `n ≤ 3`, the corner
move at the lex-max vertex (`flip` or, when the lex-max vertex is the seam, `seamFlip`), and the cut
at a double point for non-simple walks.  The two corner moves strictly decrease `peelMeasure`; the
cut strictly decreases `n`.  Every move is a homotopy inside `U`.
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

/-- **The peel.**  A closed lattice walk of at most `N` edges whose trace lies in `U` has a
null-homotopic lifted loop in `↥U`. -/
theorem lwalk_nullhomotopic_of_n_le (N : ℕ) {U : Set ℂ} (hUo : IsOpen U)
    (hpre : IsPreconnected (((↑) : ℂ → OnePoint ℂ) '' Uᶜ ∪ {OnePoint.infty})) :
    ∀ X : LWalk, X.n ≤ N → ∀ hval : ∀ t, X.path t ∈ U,
      Path.Homotopic (X.loopNat hval) (Path.refl (X.ptMin hval 0)) := by
  suffices h : ∀ m : ℕ, ∀ Y : LWalk, Y.n ≤ N → peelMeasure N Y < m →
      ∀ hval : ∀ t, Y.path t ∈ U,
        Path.Homotopic (Y.loopNat hval) (Path.refl (Y.ptMin hval 0)) by
    intro X hXN hval
    exact h (peelMeasure N X + 1) X hXN (Nat.lt_succ_self _) hval
  intro m
  induction m with
  | zero =>
      intro Y _ hlt
      exact absurd hlt (Nat.not_lt_zero _)
  | succ m ih =>
      intro Y hYN hlt hval
      have IH : ∀ (Z : LWalk) (_ : Z.n ≤ N), peelMeasure N Z < peelMeasure N Y →
          ∀ hZ : ∀ t, Z.path t ∈ U,
            Path.Homotopic (Z.loopNat hZ) (Path.refl (Z.ptMin hZ 0)) :=
        fun Z hZN hlt' hZ => ih Z hZN (by omega) hZ
      by_cases hsmall : Y.n ≤ 3
      · exact loopNat_nullhomotopic_of_n_le_three hval hsmall
      · have h4 : 4 ≤ Y.n := by omega
        by_cases hsimple : Y.IsSimple
        · by_cases hex : ∃ k, 1 ≤ k ∧ k + 1 ≤ Y.n ∧ Y.v k = vmax Y
          · obtain ⟨k, hk1, hk2, hk⟩ := hex
            -- the two neighbours of the lex-max vertex
            have ha : Y.v (k - 1) = Y.v k - (1, 0) ∨ Y.v (k - 1) = Y.v k - (0, 1) := by
              have hstep : GridStep (Y.v (k - 1)) (Y.v k) := by
                have h := Y.step (k - 1) (by omega)
                rwa [show k - 1 + 1 = k from by omega] at h
              refine LWalk.eq_sub_of_gridStep_le_left hstep ?_
              have h3 := le_vmax Y (by omega : k - 1 ≤ Y.n)
              rw [← hk] at h3
              exact (lexLe_iff _ _).mp h3
            have hb : Y.v (k + 1) = Y.v k - (1, 0) ∨ Y.v (k + 1) = Y.v k - (0, 1) := by
              have hstep : GridStep (Y.v (k + 1)) (Y.v k) :=
                gridStep_symm (Y.step k (by omega))
              refine LWalk.eq_sub_of_gridStep_le_left hstep ?_
              have h3 := le_vmax Y hk2
              rw [← hk] at h3
              exact (lexLe_iff _ _).mp h3
            have hcU := flip_corner_subset_U hUo hpre hsimple h4 hval hk1 hk2 hk
            have hval' := flip_path_mem_U (hval := hval) hk1 hk2 ha hb hcU
            have he : Y.ptMin hval 0 = (Y.flip hk1 hk2 ha hb).ptMin hval' 0 :=
              flip_ptMin_eq (hval := hval) hk1 hk2 ha hb hval' (Nat.zero_le _) (by omega)
            have hm : peelMeasure N (Y.flip hk1 hk2 ha hb) < peelMeasure N Y :=
              peelMeasure_corner (W := Y) (W' := Y.flip hk1 hk2 ha hb) hYN
                (by rw [LWalk.flip_n]; exact hYN) (LWalk.flip_n Y hk1 hk2 ha hb)
                (vmin_flip_eq hsimple h4 hk1 hk2 ha hb hk)
                (vmax_flip_lt hsimple hk1 hk2 ha hb hk)
            have hIH := IH (Y.flip hk1 hk2 ha hb) (by rw [LWalk.flip_n]; exact hYN) hm hval'
            exact (flip_loop_homotopic hk1 hk2 ha hb hcU hval' he).trans
              ((Path.Homotopic.pathCast hIH he he).trans
                (path_homotopic_of_eq (path_cast_refl he he)))
          · -- the lex-max vertex is the seam
            have hp : Y.v 0 = vmax Y := by
              obtain ⟨k0, hk0le, hk0⟩ := exists_vmax Y
              rcases Nat.eq_zero_or_pos k0 with h | h
              · rw [h] at hk0; exact hk0
              · by_cases hkn : k0 = Y.n
                · rw [hkn] at hk0
                  exact Y.closed.symm.trans hk0
                · exact absurd ⟨k0, h, by omega, hk0⟩ hex
            have h2 : 2 ≤ Y.n := by omega
            have ha : Y.v (Y.n - 1) = Y.v 0 - (1, 0) ∨ Y.v (Y.n - 1) = Y.v 0 - (0, 1) := by
              have hstep : GridStep (Y.v (Y.n - 1)) (Y.v 0) := by
                have h := Y.step (Y.n - 1) (by omega)
                rwa [show Y.n - 1 + 1 = Y.n from by omega, Y.closed] at h
              refine LWalk.eq_sub_of_gridStep_le_left hstep ?_
              have h3 := le_vmax Y (by omega : Y.n - 1 ≤ Y.n)
              rw [← hp] at h3
              exact (lexLe_iff _ _).mp h3
            have hb : Y.v 1 = Y.v 0 - (1, 0) ∨ Y.v 1 = Y.v 0 - (0, 1) := by
              have hstep : GridStep (Y.v 1) (Y.v 0) := by
                have h := gridStep_symm (Y.step 0 (by omega))
                rwa [show (0 : ℕ) + 1 = 1 from rfl] at h
              refine LWalk.eq_sub_of_gridStep_le_left hstep ?_
              have h3 := le_vmax Y (by omega : 1 ≤ Y.n)
              rw [← hp] at h3
              exact (lexLe_iff _ _).mp h3
            have hcU := seamFlip_corner_subset_U hUo hpre hsimple h4 hval hp
            have hval' := seamFlip_path_mem_U (hval := hval) h2 ha hb hcU
            have hfree := seamFlip_free_homotopic (hval := hval) h2 ha hb hcU hval'
            have hm : peelMeasure N (Y.seamFlip h2 ha hb) < peelMeasure N Y :=
              peelMeasure_corner (W := Y) (W' := Y.seamFlip h2 ha hb) hYN
                (by rw [LWalk.seamFlip_n]; exact hYN) (LWalk.seamFlip_n Y h2 ha hb)
                (seamFlip_vmin_eq hsimple h4 h2 ha hb hp)
                (seamFlip_vmax_lt hsimple h2 ha hb hp)
            have hIH := IH (Y.seamFlip h2 ha hb) (by rw [LWalk.seamFlip_n]; exact hYN) hm hval'
            exact freeHomotopic_refl (hfree.trans_homotopic hIH)
        · -- a non-simple walk: cut at a double point
          obtain ⟨i, j, hij, hj, hne, hcl⟩ := LWalk.exists_double_of_not_simple Y hsimple
          have hsub_lt : (Y.sub i j hij hj hcl).n < Y.n := by
            show j - i < Y.n
            rcases Nat.eq_zero_or_pos i with hi | hi
            · subst hi
              have hjn : j ≠ Y.n := fun hjn => hne (by rw [hjn])
              omega
            · omega
          have hdel_lt : (Y.del i j hij hj hcl).n < Y.n := by
            show i + (Y.n - j) < Y.n
            omega
          have hval_sub : ∀ t, (Y.sub i j hij hj hcl).path t ∈ U := fun t => by
            obtain ⟨t', ht'⟩ := LWalk.sub_range_subset (W := Y) i j hij hj hcl ⟨t, rfl⟩
            rw [← ht']; exact hval t'
          have hval_del : ∀ t, (Y.del i j hij hj hcl).path t ∈ U := fun t => by
            obtain ⟨t', ht'⟩ := LWalk.del_range_subset (W := Y) i j hij hj hcl ⟨t, rfl⟩
            rw [← ht']; exact hval t'
          have hsub := IH (Y.sub i j hij hj hcl) (by omega)
            (peelMeasure_cut (W := Y) (W' := Y.sub i j hij hj hcl) hYN (by omega) hsub_lt) hval_sub
          have hdel := IH (Y.del i j hij hj hcl) (by omega)
            (peelMeasure_cut (W := Y) (W' := Y.del i j hij hj hcl) hYN (by omega) hdel_lt) hval_del
          exact nullhomotopic_of_sub_del_loopNat hij hj hcl hval_sub hval_del hsub hdel

end

end Work.Smooth.JordanSeparation
