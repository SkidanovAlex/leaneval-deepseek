import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.ValMinAbs
import Submission.Work.BoseFixR.Rb5Lin.SincKernelReduction
import Submission.Work.BoseRowsL.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsL.Bookkeeping

set_option maxHeartbeats 800000

/-!
# `Work.BoseRowsL.Bookkeeping.sum_lab_eq_latBall`

The sum over the *excited* momenta of the periodic lattice cube `Lab N = (ZMod (2N+1))³`
inside the ball of radius `K` is the sum over the lattice points `(2π)ℤ³ ∖ {0}` inside the
same ball.  Concretely, the box momenta `kmomLab ℓ N k = ℓ⁻¹ • vec (labVec N k)` are indexed
by the centred representatives `labVec N k ∈ [-N,N]³ ⊂ ℤ³`, and every integer vector `n ≠ 0`
with `‖ℓ⁻¹ • vec n‖ ≤ K` has its coordinates bounded by `N` as soon as
`K ≤ 2πN/ℓ`, so it lies in the image of the cube.

All the analytic content is the elementary bound
`|n i| ≤ ‖ℓ⁻¹ • vec n‖·ℓ/(2π) ≤ N`; the rest is `Finset.image` bookkeeping.
-/

/-- The unit lattice vector `(n 0, n 1, n 2) ∈ ℝ³` of a lattice point. -/
private def zlp (m : Fin 3 → ℤ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i : Fin 3 => (m i : ℝ))

/-- A coordinate of a lattice point is bounded by its Euclidean norm. -/
private lemma coord_le_norm_zlp (m : Fin 3 → ℤ) (i : Fin 3) :
    |(m i : ℝ)| ≤ ‖zlp m‖ := by
  have h := PiLp.norm_apply_le (zlp m) i
  simpa [zlp, Real.norm_eq_abs] using h

/-- `Work.BoseB4.vec m = 2π • (unit lattice vector)`. -/
private lemma vec_eq_two_pi_smul_zlp (m : Fin 3 → ℤ) :
    Work.BoseB4.vec m = (2 * Real.pi) • zlp m := by
  show WithLp.toLp 2 (fun i : Fin 3 => 2 * Real.pi * (m i : ℝ))
      = (2 * Real.pi) • WithLp.toLp 2 (fun i : Fin 3 => (m i : ℝ))
  rw [← WithLp.toLp_smul]
  congr 1
/-- `labVec N` is injective (`ZMod.valMinAbs` is a section of `ℤ → ZMod (2N+1)`). -/
private lemma labVec_injective_local (N : ℕ) :
    Function.Injective (Work.BoseBoxFock.labVec N) := by
  intro a b hab
  funext i
  exact ZMod.valMinAbs_inj.mp (congrFun hab i)

/-- The label `0` of the cube has centred vector `0`. -/
private lemma labVec_zero_local (N : ℕ) :
    Work.BoseBoxFock.labVec N (0 : Work.BoseBoxFock.Lab N) = 0 := by
  funext i
  simp [Work.BoseBoxFock.labVec]

/-- `labVec N` hits every point of the box `[-N,N]³`. -/
private lemma labVec_mk_local (N : ℕ) {m : Fin 3 → ℤ}
    (hm : ∀ i : Fin 3, -(N : ℤ) ≤ m i ∧ m i ≤ (N : ℤ)) :
    Work.BoseBoxFock.labVec N (fun i => (m i : ZMod (2 * N + 1))) = m := by
  funext i
  haveI : NeZero (2 * N + 1) := ⟨by omega⟩
  rw [Work.BoseBoxFock.labVec]
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  rw [Set.mem_Ioc]
  have := hm i
  constructor <;> omega

theorem sum_lab_eq_latBall {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (ℓ : ℝ) (N : ℕ) (K : ℝ)
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) (hℓ : 0 < ℓ) (hK : K ≤ 2 * Real.pi * N / ℓ) :
    ∃ S : Finset (Fin 3 → ℤ),
      (∀ n ∈ S, ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ≤ K) ∧
      (∀ n : Fin 3 → ℤ, n ≠ 0 → ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ≤ K → n ∈ S) ∧
      ∑ k ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab N)).filter
              (fun k => ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ≤ K), g (Work.BoseBoxFock.kmomLab ℓ N k)
        = ∑ n ∈ S, g (ℓ⁻¹ • Work.BoseB4.vec n) := by
  classical
  set T : Finset (Work.BoseBoxFock.Lab N) :=
    (Work.BoseB7.excited (Work.BoseBoxFock.Lab N)).filter
      (fun k => ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ≤ K) with hTdef
  refine ⟨T.image (Work.BoseBoxFock.labVec N), ?_, ?_, ?_⟩
  · -- membership in the ball is inherited from the filter
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨k, hk, rfl⟩ := hn
    rw [hTdef] at hk
    have hk' := (Finset.mem_filter.mp hk).2
    simpa only [Work.BoseBoxFock.kmomLab] using hk'
  · -- every lattice point of the ball sits in the box `[-N,N]³`, hence in `S`
    intro n hn0 hnK
    -- the norm bound `‖ℓ⁻¹ • vec n‖ ≤ K ≤ 2πN/ℓ` forces `‖n‖ ≤ N`
    have hnorm : ‖ℓ⁻¹ • Work.BoseB4.vec n‖ = ℓ⁻¹ * (2 * Real.pi) * ‖zlp n‖ := by
      rw [vec_eq_two_pi_smul_zlp, smul_smul, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ℓ⁻¹ * (2 * Real.pi))]
    have hA : 2 * Real.pi * ‖zlp n‖ ≤ K * ℓ := by
      have h := mul_le_mul_of_nonneg_left (hnorm ▸ hnK) hℓ.le
      have hl : ℓ * (ℓ⁻¹ * (2 * Real.pi) * ‖zlp n‖) = 2 * Real.pi * ‖zlp n‖ := by
        calc ℓ * (ℓ⁻¹ * (2 * Real.pi) * ‖zlp n‖)
            = (ℓ * ℓ⁻¹) * (2 * Real.pi * ‖zlp n‖) := by ring
          _ = 2 * Real.pi * ‖zlp n‖ := by rw [mul_inv_cancel₀ (ne_of_gt hℓ), one_mul]
      linarith [h, hl]
    have hB : K * ℓ ≤ 2 * Real.pi * (N : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hK hℓ.le
      rw [div_mul_cancel₀ _ (ne_of_gt hℓ)] at h
      exact h
    have hC : ‖zlp n‖ ≤ (N : ℝ) :=
      le_of_mul_le_mul_left (le_trans hA hB) (by positivity : (0 : ℝ) < 2 * Real.pi)
    have hbox : ∀ i : Fin 3, -(N : ℤ) ≤ n i ∧ n i ≤ (N : ℤ) := by
      intro i
      have h1 : |(n i : ℝ)| ≤ (N : ℝ) := le_trans (coord_le_norm_zlp n i) hC
      rw [abs_le] at h1
      exact ⟨by exact_mod_cast h1.1, by exact_mod_cast h1.2⟩
    -- the label of `n` in the cube, and the fact that it maps back to `n`
    let k : Work.BoseBoxFock.Lab N := fun i => (n i : ZMod (2 * N + 1))
    have hlab : Work.BoseBoxFock.labVec N k = n := labVec_mk_local N hbox
    have hk0 : k ≠ 0 := by
      intro hk
      refine hn0 ?_
      rw [← hlab, hk, labVec_zero_local]
    have hkT : k ∈ T := by
      rw [hTdef, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Work.BoseB7.excited, Finset.mem_erase]
        exact ⟨hk0, Finset.mem_univ k⟩
      · have hkm : Work.BoseBoxFock.kmomLab ℓ N k = ℓ⁻¹ • Work.BoseB4.vec n := by
          rw [Work.BoseBoxFock.kmomLab, hlab]
        rwa [hkm]
    exact Finset.mem_image.mpr ⟨k, hkT, hlab⟩
  · -- the two sums are the same sum over `T`, reindexed along the injection `labVec N`
    rw [Finset.sum_image (s := T) (g := Work.BoseBoxFock.labVec N)
      (f := fun n => g (ℓ⁻¹ • Work.BoseB4.vec n))
      (fun a _ b _ hab => labVec_injective_local N hab)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [Work.BoseBoxFock.kmomLab]

end Work.BoseRowsL.Bookkeeping
