import Mathlib
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.TParity.LocalGraph
import Submission.Work.Drive.TParity.ChartDeriv

namespace Work.Drive.TParity

theorem isolated_of_face3 {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (D k))
    {b : Work.Drive.Amb 8} (hbb : b ∈ Submission.Drive.unitBox 8)
    (hbeq : Work.Drive.TParity.meet3 D b)
    (p : Fin 9) (hpe : b p = 0 ∨ b p = 1)
    (hpo : ∀ q : Fin 9, q ≠ p → b q ∈ Set.Ioo (0 : ℝ) 1)
    (hsurj_p : Function.Surjective (fun v : {v : Work.Drive.Amb 8 // v p = 0} =>
      fderiv ℝ (Work.Drive.TParity.chartDiff3 (D 0 (Work.Drive.TParity.bPartC 0 b)) D) b v.1)) :
    ∃ U : Set (Work.Drive.Amb 8), IsOpen U ∧ b ∈ U ∧ U ∩ Work.Drive.TParity.bK3 D ⊆ {b} := by
  -- The triple intersection set is, near `b`, the graph of a smooth map over the `p`-th
  -- coordinate (`exists_local_graph3`), and the graph's coordinate `p` is the only one that can
  -- meet the boundary of the box.
  obtain ⟨δ, ρ, η, hδ, hρ, hηcd, hηi, hηx, hchar⟩ :=
    exists_local_graph3 (D 0 (bPartC 0 b)) D hD (mem_region3_self D hbeq) hbeq p hsurj_p
  have hηc : Continuous η := hηcd.continuous
  -- The graph condition only holds for `|y p - b p| < δ`; shrink `δ` to below `1` as well, so that
  -- the two values `0` and `1` (both attained by `b p`) cannot both be within reach.
  set δ' : ℝ := min δ (1/2) with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδ (by norm_num)
  have hδ'le : δ' ≤ δ := min_le_left _ _
  have hδ'half : δ' ≤ 1/2 := min_le_right _ _
  -- The remaining coordinates of the graph are strictly inside the box near `b`.
  set W : Set (Amb 8) := ⋂ j : {j : Fin 9 // j ≠ p}, {y : Amb 8 | (η (y p)) j.1 ∈ Set.Ioo (0:ℝ) 1}
    with hWdef
  have hbW : b ∈ W := by
    rw [hWdef, Set.mem_iInter]
    intro j
    show (η (b p)) j.1 ∈ Set.Ioo (0:ℝ) 1
    rw [hηx]
    simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply, if_neg j.2, smul_zero, sub_zero]
    exact hpo j.1 j.2
  refine ⟨{y | |y p - b p| < δ'} ∩
      {y | ‖y - (y p) • EuclideanSpace.single p (1:ℝ) - η (y p)‖ < ρ} ∩ W, ?_, ?_, ?_⟩
  · -- openness
    rw [hWdef]
    refine ((isOpen_lt ?_ continuous_const).inter ?_).inter ?_
    · fun_prop
    · refine isOpen_lt ?_ continuous_const
      fun_prop
    · refine isOpen_iInter_of_finite (fun j => ?_)
      exact isOpen_Ioo.preimage (by fun_prop)
  · -- `b` belongs to it
    refine ⟨⟨by simp [hδ'pos], ?_⟩, hbW⟩
    show ‖b - b p • EuclideanSpace.single p (1:ℝ) - η (b p)‖ < ρ
    rw [hηx]
    simp [hρ]
  · -- no other boundary point of the triple intersection set lies in it
    rintro y ⟨⟨⟨hy1, hy2⟩, hyW⟩, hybK⟩
    rw [Set.mem_ofPred_eq] at hy1 hy2
    rw [Set.mem_singleton_iff]
    rw [mem_bK3] at hybK
    obtain ⟨-, hym, hybd⟩ := hybK
    have hyW' : ∀ j : {j : Fin 9 // j ≠ p}, (η (y p)) j.1 ∈ Set.Ioo (0:ℝ) 1 :=
      Set.mem_iInter.mp (hWdef ▸ hyW)
    have hδy : |y p - b p| < δ := lt_of_lt_of_le hy1 hδ'le
    have hgraph : y = (y p) • EuclideanSpace.single p (1:ℝ) + η (y p) :=
      (hchar y hδy hy2).2.mp hym
    obtain ⟨-, i, hi⟩ := hybd
    -- the boundary coordinate of `y` must be `p`
    have hip : i = p := by
      by_contra hne
      have hmem : (η (y p)) i ∈ Set.Ioo (0:ℝ) 1 := hyW' ⟨i, hne⟩
      have hval : y i = (η (y p)) i := by
        conv_lhs => rw [hgraph]
        rw [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, if_neg hne]
        simp
      rcases hi with h0 | h1
      · rw [hval] at h0; exact absurd h0 (ne_of_gt hmem.1)
      · rw [hval] at h1; exact absurd h1 (ne_of_lt hmem.2)
    rw [hip] at hi
    -- and then it must equal `b p`, hence `y = b`
    have hyp : y p = b p := by
      rcases hi with h | h <;> rcases hpe with hb | hb
      · rw [h, hb]
      · exfalso
        rw [h, hb] at hy1
        norm_num at hy1
        linarith [hδ'half]
      · exfalso
        rw [h, hb] at hy1
        norm_num at hy1
        linarith [hδ'half]
      · rw [h, hb]
    rw [hgraph, hyp, hηx]
    abel

end Work.Drive.TParity
