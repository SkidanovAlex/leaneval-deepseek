import Mathlib
import Submission.Work.Drive.N2C.mfrFootPlumbing
import Submission.Work.Drive.N2C.mfrFarPiece
import Submission.Work.Drive.N2C.mobiusShape
import Submission.Work.Drive.N2Lead.mobiusUpperCoreMarked
import Submission.Work.Drive.N2Lead.mfrStarRowsOfMarkedRows

namespace Work.Drive.N2C

theorem mfrCoreRowsX {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (hsep : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η < 2 * D.ηd)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (S : Work.Drive.N2Lead.MobiusPacket D η) (hshape : Work.Drive.N2C.MobiusShape D η S) :
    ∃ (ε εp Dp : ℝ), 0 < ε ∧ 0 < εp ∧ 0 ≤ Dp ∧
      (∀ y : M, f y = f p + 3 * η / 2 → ∃ k : Fin S.n,
        Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y) ∈
          (if k = S.i then Metric.ball (0 : ℂ) (Dp + 5)
            else Metric.ball (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos S.n k)
              + (Dp : ℂ) * Complex.I) 2)) ∧
      (∀ (y : M) (k : Fin S.n), f y = f p + 3 * η / 2 →
        Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y) ∈
          (if k = S.i then Metric.ball (0 : ℂ) (Dp + 5)
            else Metric.ball (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos S.n k)
              + (Dp : ℂ) * Complex.I) 2) →
        Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)
            ≠ (if k = S.i then 0
              else Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos S.n k)
                + (Dp : ℂ) * Complex.I) ∧
        ∀ v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) y,
          mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℝ)
            f y v = 0 → v ≠ 0 →
          ¬ (∃ t : ℝ, mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
              (modelWithCornersSelf ℝ ℂ)
              (fun z : M => Work.Drive.N2Lead.proj2
                (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp z)) y v
            = t • (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)
                - (if k = S.i then 0
                  else Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos S.n k)
                    + (Dp : ℂ) * Complex.I)))) ∧
      (∀ k : Fin S.n, (if k = S.i then (1 : ℂ) else -1) ≠ 0 ∧ ∀ x y : M,
        f x = f p + 3 * η / 2 → f y = f p + 3 * η / 2 →
        (∃ s : ℝ, 0 < s ∧ Work.Drive.N2Lead.proj2
            (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp x)
          = (if k = S.i then 0
              else Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos S.n k)
                + (Dp : ℂ) * Complex.I) + s • (if k = S.i then (1 : ℂ) else -1)) →
        (∃ s : ℝ, 0 < s ∧ Work.Drive.N2Lead.proj2
            (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)
          = (if k = S.i then 0
              else Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos S.n k)
                + (Dp : ℂ) * Complex.I) + s • (if k = S.i then (1 : ℂ) else -1)) → x = y) := by
  classical
  obtain ⟨ε, εp, Dp, hε, hε1, hεp, hεp1, hDp, hne, hrate, hray⟩ :=
    Work.Drive.N2Lead.mobiusUpperCoreMarked D hη hsmall hsep hf S hshape
  have hε19 : ε ≤ 19 := by linarith
  have hεp19 : εp ≤ 19 := by linarith
  have hband : f p + 3 * η / 2 ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) :=
    ⟨by linarith, by linarith⟩
  refine ⟨ε, εp, Dp, hε, hεp, hDp, ?_, ?_, ?_⟩
  · -- the coverage row
    intro y hy
    by_cases hreg : y ∈ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j)
        (D.ρ D.j)) S.Z (39 / 20)
    · refine ⟨S.i, ?_⟩
      rw [if_pos rfl, Metric.mem_ball, dist_zero_right]
      have h1 := Work.Drive.N2Lead.mobiusUpperModelNorm (D := D) hη hsmall S
        (ε := ε) (εp := εp) hDp y hy hreg
      have h2 := Work.Drive.N2Lead.norm_proj2_le
        (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)
      linarith
    · have hfl := S.hfootval y hreg (by rw [hy]; exact hband)
      obtain ⟨j, t, hjt⟩ := S.L.cover _ hfl
      by_cases hji : j = S.i
      · refine ⟨S.i, ?_⟩
        rw [if_pos rfl, Metric.mem_ball, dist_zero_right]
        have h1 := Work.Drive.N2Lead.mobiusTwisted_norm_le_marked (D := D) (S := S)
          (ε := ε) (εp := εp) (Dp := Dp) hDp (y := y) (t := t) hreg (by rw [hji] at hjt; exact hjt)
        have h2 := Work.Drive.N2Lead.norm_proj2_le
          (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)
        linarith
      · refine ⟨j, ?_⟩
        rw [if_neg hji, Metric.mem_ball, dist_eq_norm]
        have hval := Work.Drive.N2Lead.mobiusTwisted_far_proj (D := D) (S := S)
          (ε := ε) (εp := εp) (Dp := Dp) hε hε19 hεp hεp19 (j := j) hji (y := y) (t := t) hreg hjt
        rw [hval, add_sub_cancel_left, Work.Drive.N2C.norm_proj2_ang]
        norm_num
  · -- the rate row
    intro y k hy hz
    by_cases hk : k = S.i
    · subst hk
      rw [if_pos rfl] at hz
      rw [if_pos rfl]
      have hle : ‖Work.Drive.N2Lead.proj2
          (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)‖ ≤ Dp + 5 := by
        rw [Metric.mem_ball, dist_zero_right] at hz
        linarith
      refine ⟨hne y hy, ?_⟩
      intro v hv hvne h
      obtain ⟨t, ht⟩ := h
      exact hrate y hy hle v hv hvne ⟨t, by simpa using ht⟩
    · have hz2 : dist (Work.Drive.N2Lead.proj2
          (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y))
          (Work.Drive.N2Lead.mfrO S.n S.i Dp k) < 2 := by
        rw [if_neg hk] at hz
        rw [Metric.mem_ball] at hz
        rwa [← Work.Drive.N2Lead.mfrO_of_ne S.n S.i Dp hk] at hz
      obtain ⟨hnotmem, t, hjt⟩ := Work.Drive.N2Lead.mfr_far_classify (D := D) hη hsmall S
        hε hε19 hεp hεp19 hDp hk hy hz2
      have hfp := Work.Drive.N2C.mfrFarPiece (D := D) hη hsmall hf S hε hε19 hεp hεp19 hDp
        hk hy hnotmem hjt
      obtain ⟨-, hneF, hrateF⟩ := hfp
      rw [if_neg hk]
      exact ⟨hneF, fun v hv hvne h => by
        obtain ⟨t', ht'⟩ := h
        exact hrateF v hv hvne ⟨t', ht'⟩⟩
  · -- the ray row
    intro k
    by_cases hk : k = S.i
    · subst hk
      refine ⟨?_, ?_⟩
      · rw [if_pos rfl]; norm_num
      · intro x y hx hy hxs hys
        refine hray x y hx hy ?_ ?_
        · obtain ⟨s, hs0, hs⟩ := hxs
          refine ⟨s, hs0, ?_⟩
          rw [hs]
          simp
        · obtain ⟨s, hs0, hs⟩ := hys
          refine ⟨s, hs0, ?_⟩
          rw [hs]
          simp
    · refine ⟨?_, ?_⟩
      · rw [if_neg hk]; norm_num
      · intro x y hx hy hxs hys
        have hxs' : ∃ s : ℝ, 0 < s ∧ Work.Drive.N2Lead.proj2
            (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp x)
            = Work.Drive.N2Lead.mfrO S.n S.i Dp k + s • (-1 : ℂ) := by
          obtain ⟨s, hs0, hs⟩ := hxs
          refine ⟨s, hs0, ?_⟩
          rw [hs, Work.Drive.N2Lead.mfrO_of_ne S.n S.i Dp hk]
          simp [hk]
        have hys' : ∃ s : ℝ, 0 < s ∧ Work.Drive.N2Lead.proj2
            (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)
            = Work.Drive.N2Lead.mfrO S.n S.i Dp k + s • (-1 : ℂ) := by
          obtain ⟨s, hs0, hs⟩ := hys
          refine ⟨s, hs0, ?_⟩
          rw [hs, Work.Drive.N2Lead.mfrO_of_ne S.n S.i Dp hk]
          simp [hk]
        obtain ⟨hxnot, hxfoot⟩ := Work.Drive.N2Lead.mfr_ray_foot (D := D) hη hsmall S
          hε hε19 hεp hεp19 hDp hk hx hxs'
        obtain ⟨hynot, hyfoot⟩ := Work.Drive.N2Lead.mfr_ray_foot (D := D) hη hsmall S
          hε hε19 hεp hεp19 hDp hk hy hys'
        have hfooteq : Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) x
            = Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y := hxfoot.trans hyfoot.symm
        have hG : Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp x
            = Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y := by
          rw [Work.Drive.N2Lead.mobiusTwisted_foot (D := D) (S := S) (ε := ε) (εp := εp)
              (Dp := Dp) (y := x) hxnot,
            Work.Drive.N2Lead.mobiusTwisted_foot (D := D) (S := S) (ε := ε) (εp := εp)
              (Dp := Dp) (y := y) hynot, hfooteq]
        exact Work.Drive.N2C.mfr_injOn_level (D := D) hη hsmall hf S hεp hDp hx hy hG

end Work.Drive.N2C
