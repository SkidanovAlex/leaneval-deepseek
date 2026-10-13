import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsSpace
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSqIter_mixed_Jeps_le6
import Submission.Work.FTS.StrongEps.PZeroAux.Pz_l12
import Submission.Work.FTS.StrongEps.EpsSqTools.L12_sub_EpsSq_le
import Submission.Work.FTS.StrongEps.PZeroAux.mixed_Pz
import Submission.Work.FTS.StrongEps.PZeroAux.pzNorm_pos
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartAux
import Submission.Work.FTS.StrongEps.EpsSqTools.BumpEpsSqBound
import Submission.Work.FTS.StrongEps.JepsHkMem.AuxMeas
import Submission.Work.FTS.StrongEps.JepsSmoothOpen
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaSlotJeps
import Submission.Work.FTS.StrongEps.EpsRLX.BumpSlotFour

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The `ε`-weight vanishes off the open quadrant

The weight `epsW α z θ = w z / sin(2θ)^{γ/2}` degenerates on the three coordinate lines that make
up the boundary of the closed quadrant `Iz ×ˢ Iθ`: at `z = 0` because `w 0 = 0`, and at
`θ = 0, π/2` because `sin(2θ) = 0` and `γ/2 ≠ 0` (Lean's totalised inversion then gives `0`).
Consequently `EpsSq`/`EpsMem` only see the values of a datum on the *open* quadrant `Q0`, which is
what the projection identity `mixed b a (Pz f) = mixed b a f - c · mixed b a bump` (proved on `Q0`
by `PZeroAux.mixed_Pz`) can be transferred along. -/

theorem epsW_eq_zero_of_not_mem {α : ℝ} (hα : 0 < α) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) (hQ : ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2)) :
    epsW α z θ = 0 := by
  have hgam : Work.Spaces.gam α / 2 ≠ 0 := by
    rw [Work.Spaces.gam]; intro h; linarith
  rw [Work.Spaces.Iz, Set.mem_Ici] at hz
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  rcases eq_or_lt_of_le hz with h | h
  · subst h
    simp only [epsW, Work.Spaces.w]
    norm_num
  rcases eq_or_lt_of_le hθ.1 with h2 | h2
  · subst h2
    simp only [epsW, Work.Spaces.w]
    rw [show Real.sin (2 * 0) = 0 by norm_num, Real.zero_rpow hgam]
    simp
  rcases lt_or_eq_of_le hθ.2 with h3 | h3
  · exact absurd ⟨h, h2, h3⟩ hQ
  · subst h3
    simp only [epsW, Work.Spaces.w]
    rw [show Real.sin (2 * (Real.pi / 2)) = 0 by
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi], Real.zero_rpow hgam]
    simp

/-- The weighted square of a datum agrees on `Iz ×ˢ Iθ` as soon as the two data agree on `Q0`. -/
theorem epsW_sq_congr_of_eqOn_Q0 {α : ℝ} (hα : 0 < α) {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (f z θ * epsW α z θ) ^ 2 = (g z θ * epsW α z θ) ^ 2 := by
  intro z hz θ hθ
  by_cases hQ : 0 < z ∧ 0 < θ ∧ θ < π / 2
  · rw [h z θ hQ.1 hQ.2.1 hQ.2.2]
  · rw [epsW_eq_zero_of_not_mem hα hz hθ hQ, mul_zero, mul_zero]

/-- **`EpsSq` only sees the values of the datum on the open quadrant.** -/
theorem EpsSq_congr_Q0 {α : ℝ} (hα : 0 < α) {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    EpsSq α f = EpsSq α g := by
  have hpt := epsW_sq_congr_of_eqOn_Q0 hα h
  rw [EpsSq, EpsSq]
  refine MeasureTheory.setIntegral_congr_fun
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) ?_
  intro z hz
  refine MeasureTheory.setIntegral_congr_fun
    (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) ?_
  intro θ hθ
  exact hpt z hz θ hθ

/-- **`EpsMem` only sees the values of the datum on the open quadrant.** -/
theorem EpsMem_congr_Q0 {α : ℝ} (hα : 0 < α) {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    EpsMem α f ↔ EpsMem α g := by
  have hpt := epsW_sq_congr_of_eqOn_Q0 hα h
  constructor <;> intro hf
  · rw [EpsMem] at hf ⊢
    refine hf.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) ?_
    rintro ⟨z, θ⟩ hh
    simp only [Set.mem_prod] at hh
    exact hpt z hh.1 θ hh.2
  · rw [EpsMem] at hf ⊢
    refine hf.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) ?_
    rintro ⟨z, θ⟩ hh
    simp only [Set.mem_prod] at hh
    exact (hpt z hh.1 θ hh.2).symm

/-! ## Almost-everywhere strong measurability of the slots -/

/-- The mixed slots of the mollified datum are a.e. strongly measurable in the weighted sense. -/
theorem AK_mixed_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {δ : ℝ → ℝ → ℝ} (hδ : Work.FTS.EllipticEst.SmoothOpen δ)
    (α : ℝ) (b a : ℕ) :
    Work.FTS.StrongEps.EpsSqTools.AK α
      (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε δ)) :=
  Work.FTS.StrongEps.EpsSqTools.AK_of_uncurry
    (Work.FTS.StrongEps.JepsHkMem.aestronglyMeasurable_mixed_Jeps hρ.moll hε
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall δ).mp hδ) b a)

/-- The mixed slots of the correction profile are a.e. strongly measurable in the weighted sense. -/
theorem AK_mixed_bump (α : ℝ) (j i : ℕ) :
    Work.FTS.StrongEps.EpsSqTools.AK α
      (Work.Spaces.mixed j i Work.FTS.StrongEps.bump) :=
  Work.FTS.StrongEps.EpsSqTools.AK_of_uncurry
    (Work.Spaces.aesm_of_continuousOn_Qd _
      ((Work.FTS.StrongEps.smoothOpen_bump.mixed j i).continuousOn))

theorem DeltaSlotEpsSq (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ ε ∈ Set.Ioc 0 1, ∀ {δ : Work.FTS.Galerkin.Fn},
      Work.FTS.EllipticEst.SmoothOpen δ → Work.Spaces.HkMem α 6 δ →
      Work.FTS.StrongEps.EpsMem α δ → ∀ b a : ℕ, a + b ≤ 4 →
      Work.FTS.StrongEps.EpsMem α
          (Work.Spaces.mixed b a (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε δ))) ∧
      Work.FTS.StrongEps.EpsSq α
          (Work.Spaces.mixed b a (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε δ)))
        ≤ C * (C / ε) ^ 12 * Work.FTS.StrongEps.EpsSq α δ := by
  obtain ⟨CJ, hCJpos, hCJ⟩ := DeltaSlotJeps ρ hρ
  obtain ⟨K, hKpos, hK⟩ := BumpSlotFour
  obtain ⟨C12, hC12pos, hC12⟩ := Work.FTS.StrongEps.EpsSqTools.L12_le_sqrt_EpsSq
  have hpz : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  set m : ℝ := max 1 (max (2 * CJ) (2 * K * (C12 / Work.FTS.StrongEps.pzNorm) ^ 2 * CJ)) with hm
  have hm1 : (1 : ℝ) ≤ m := by rw [hm]; exact le_max_left _ _
  have hmA : 2 * CJ ≤ m := by
    rw [hm]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hmB : 2 * K * (C12 / Work.FTS.StrongEps.pzNorm) ^ 2 * CJ ≤ m := by
    rw [hm]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hm1
  have hmnn : (0 : ℝ) ≤ m := hmpos.le
  refine ⟨2 * m, by linarith, ?_⟩
  intro α hα ε hε δ hδsm hδHk hδmem b a hab
  have hα0 : 0 < α := hα.1
  have hε0 : 0 < ε := hε.1
  have hε1 : ε ≤ 1 := hε.2
  let J : ℝ → ℝ → ℝ := Work.FTS.StrongEps.Jeps ρ ε δ
  let c : ℝ := Work.Construction.L12 J 0 / Work.FTS.StrongEps.pzNorm
  have hJsm : Work.FTS.EllipticEst.SmoothOpen J :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε0
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall δ).mp hδsm)
  obtain ⟨hJmem, hJsq⟩ := hCJ α hα ε hε (δ := δ) hδsm hδmem b a hab
  obtain ⟨hBmem, hBsq⟩ := hK α hα b a (by omega)
  have hJ0mem : Work.FTS.StrongEps.EpsMem α J :=
    (hCJ α hα ε hε (δ := δ) hδsm hδmem 0 0 (by norm_num)).1
  have hakJ : Work.FTS.StrongEps.EpsSqTools.AK α (Work.Spaces.mixed b a J) :=
    AK_mixed_Jeps hρ hε0 hδsm α b a
  have hakB : Work.FTS.StrongEps.EpsSqTools.AK α
      (fun z θ => c * Work.Spaces.mixed b a Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.StrongEps.EpsSqTools.AK_const_mul c (AK_mixed_bump α b a)
  have hcBmem : Work.FTS.StrongEps.EpsMem α
      (fun z θ => c * Work.Spaces.mixed b a Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.StrongEps.EpsSqTools.EpsMem_const_mul c hBmem
  have hmem_sub : Work.FTS.StrongEps.EpsMem α
      (fun z θ => Work.Spaces.mixed b a J z θ
        - c * Work.Spaces.mixed b a Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.StrongEps.EpsSqTools.EpsMem_sub hakJ hakB hJmem hcBmem
  have hident : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed b a (Work.FTS.StrongEps.Pz J) z θ
        = Work.Spaces.mixed b a J z θ
          - c * Work.Spaces.mixed b a Work.FTS.StrongEps.bump z θ := by
    intro z θ hz hθ hθ2
    exact Work.FTS.StrongEps.PZeroAux.mixed_Pz hJsm hz ⟨hθ, hθ2⟩ b a
  -- the level-zero slot of `J`
  have hE2 : Work.FTS.StrongEps.EpsSq α J ≤ CJ * Work.FTS.StrongEps.EpsSq α δ := by
    have h0 := (hCJ α hα ε hε (δ := δ) hδsm hδmem 0 0 (by norm_num)).2
    have h0' : Work.FTS.StrongEps.EpsSq α J
        ≤ CJ * (CJ / ε) ^ (2 * (0 + 0)) * Work.FTS.StrongEps.EpsSq α δ := h0
    rw [show (2 : ℕ) * (0 + 0) = 0 from rfl, pow_zero, mul_one] at h0'
    exact h0'
  -- the size of the projection coefficient
  have hL12 : |Work.Construction.L12 J 0| ≤ C12 * Real.sqrt (Work.FTS.StrongEps.EpsSq α J) :=
    hC12 α hα J hJ0mem 0 (by simp [Work.Spaces.Iz])
  have hc2 : c ^ 2
      ≤ (C12 / Work.FTS.StrongEps.pzNorm) ^ 2 * (CJ * Work.FTS.StrongEps.EpsSq α δ) := by
    have h1 : (Work.Construction.L12 J 0) ^ 2
        ≤ (C12 * Real.sqrt (Work.FTS.StrongEps.EpsSq α J)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hL12 2
    have h2 : (C12 * Real.sqrt (Work.FTS.StrongEps.EpsSq α J)) ^ 2
        = C12 ^ 2 * Work.FTS.StrongEps.EpsSq α J := by
      rw [mul_pow, Real.sq_sqrt (Work.FTS.StrongEps.EpsSq_nonneg α J)]
    calc c ^ 2
        = (Work.Construction.L12 J 0) ^ 2 / Work.FTS.StrongEps.pzNorm ^ 2 := by
          show (Work.Construction.L12 J 0 / Work.FTS.StrongEps.pzNorm) ^ 2 = _
          rw [div_pow]
      _ ≤ (C12 * Real.sqrt (Work.FTS.StrongEps.EpsSq α J)) ^ 2
            / Work.FTS.StrongEps.pzNorm ^ 2 :=
          div_le_div_of_nonneg_right h1 (sq_nonneg _)
      _ = C12 ^ 2 * Work.FTS.StrongEps.EpsSq α J / Work.FTS.StrongEps.pzNorm ^ 2 := by rw [h2]
      _ = (C12 / Work.FTS.StrongEps.pzNorm) ^ 2 * Work.FTS.StrongEps.EpsSq α J := by
          rw [div_pow]; ring
      _ ≤ (C12 / Work.FTS.StrongEps.pzNorm) ^ 2 * (CJ * Work.FTS.StrongEps.EpsSq α δ) :=
          mul_le_mul_of_nonneg_left hE2 (sq_nonneg _)
  -- the correction slot
  have hBsq' : Work.FTS.StrongEps.EpsSq α
      (fun z θ => c * Work.Spaces.mixed b a Work.FTS.StrongEps.bump z θ)
      ≤ c ^ 2 * K := by
    rw [Work.FTS.StrongEps.EpsSqTools.EpsSq_const_mul]
    exact mul_le_mul_of_nonneg_left hBsq (sq_nonneg c)
  -- the two-sided bound
  have hmain : Work.FTS.StrongEps.EpsSq α
      (fun z θ => Work.Spaces.mixed b a J z θ
        - c * Work.Spaces.mixed b a Work.FTS.StrongEps.bump z θ)
      ≤ (2 * CJ * (CJ / ε) ^ (2 * (a + b))
          + 2 * K * (C12 / Work.FTS.StrongEps.pzNorm) ^ 2 * CJ)
          * Work.FTS.StrongEps.EpsSq α δ := by
    have hsub := Work.FTS.StrongEps.EpsSqTools.EpsSq_sub_le_of_mem hJmem hcBmem
    have step2 : 2 * Work.FTS.StrongEps.EpsSq α (Work.Spaces.mixed b a J)
        ≤ 2 * (CJ * (CJ / ε) ^ (2 * (a + b)) * Work.FTS.StrongEps.EpsSq α δ) :=
      mul_le_mul_of_nonneg_left hJsq (by norm_num)
    have step3 : 2 * Work.FTS.StrongEps.EpsSq α
        (fun z θ => c * Work.Spaces.mixed b a Work.FTS.StrongEps.bump z θ)
        ≤ 2 * (c ^ 2 * K) := mul_le_mul_of_nonneg_left hBsq' (by norm_num)
    have step4 : 2 * (c ^ 2 * K)
        ≤ 2 * (K * (C12 / Work.FTS.StrongEps.pzNorm) ^ 2 * CJ
            * Work.FTS.StrongEps.EpsSq α δ) := by
      have h : c ^ 2 * K
          ≤ ((C12 / Work.FTS.StrongEps.pzNorm) ^ 2
              * (CJ * Work.FTS.StrongEps.EpsSq α δ)) * K :=
        mul_le_mul_of_nonneg_right hc2 hKpos.le
      have h' : ((C12 / Work.FTS.StrongEps.pzNorm) ^ 2
            * (CJ * Work.FTS.StrongEps.EpsSq α δ)) * K
          = K * (C12 / Work.FTS.StrongEps.pzNorm) ^ 2 * CJ
              * Work.FTS.StrongEps.EpsSq α δ := by ring
      rw [h'] at h
      linarith
    calc Work.FTS.StrongEps.EpsSq α
          (fun z θ => Work.Spaces.mixed b a J z θ
            - c * Work.Spaces.mixed b a Work.FTS.StrongEps.bump z θ)
        ≤ 2 * Work.FTS.StrongEps.EpsSq α (Work.Spaces.mixed b a J)
            + 2 * Work.FTS.StrongEps.EpsSq α
              (fun z θ => c * Work.Spaces.mixed b a Work.FTS.StrongEps.bump z θ) := hsub
      _ ≤ 2 * (CJ * (CJ / ε) ^ (2 * (a + b)) * Work.FTS.StrongEps.EpsSq α δ)
            + 2 * (c ^ 2 * K) := by linarith
      _ ≤ 2 * (CJ * (CJ / ε) ^ (2 * (a + b)) * Work.FTS.StrongEps.EpsSq α δ)
            + 2 * (K * (C12 / Work.FTS.StrongEps.pzNorm) ^ 2 * CJ
                * Work.FTS.StrongEps.EpsSq α δ) := by linarith
      _ = (2 * CJ * (CJ / ε) ^ (2 * (a + b))
            + 2 * K * (C12 / Work.FTS.StrongEps.pzNorm) ^ 2 * CJ)
            * Work.FTS.StrongEps.EpsSq α δ := by ring
  -- the constants
  have harith : 2 * CJ * (CJ / ε) ^ (2 * (a + b))
      + 2 * K * (C12 / Work.FTS.StrongEps.pzNorm) ^ 2 * CJ
      ≤ 2 * m * (2 * m / ε) ^ 12 := by
    have hCJm : CJ ≤ m := by linarith [hCJpos, hmA]
    have hCJ2m : CJ ≤ 2 * m := by linarith [hmnn]
    have hbase : CJ / ε ≤ 2 * m / ε := div_le_div_of_nonneg_right hCJ2m hε0.le
    have hbase0 : (0 : ℝ) ≤ CJ / ε := div_nonneg hCJpos.le hε0.le
    have hbase2m : (1 : ℝ) ≤ 2 * m / ε := by
      rw [le_div_iff₀ hε0]
      nlinarith [hm1, hε1]
    have hpow1 : (CJ / ε) ^ (2 * (a + b)) ≤ (2 * m / ε) ^ (2 * (a + b)) :=
      pow_le_pow_left₀ hbase0 hbase _
    have hpow2 : (2 * m / ε) ^ (2 * (a + b)) ≤ (2 * m / ε) ^ 12 :=
      pow_le_pow_right₀ hbase2m (by omega)
    have h1 : 2 * CJ * (CJ / ε) ^ (2 * (a + b)) ≤ m * (2 * m / ε) ^ 12 :=
      calc 2 * CJ * (CJ / ε) ^ (2 * (a + b))
          ≤ m * (2 * m / ε) ^ (2 * (a + b)) :=
            mul_le_mul hmA hpow1 (pow_nonneg hbase0 _) hmnn
        _ ≤ m * (2 * m / ε) ^ 12 := mul_le_mul_of_nonneg_left hpow2 hmnn
    have h2 : 2 * K * (C12 / Work.FTS.StrongEps.pzNorm) ^ 2 * CJ
        ≤ m * (2 * m / ε) ^ 12 := by
      have h12 : (1 : ℝ) ≤ (2 * m / ε) ^ 12 := by
        calc (1 : ℝ) = 1 ^ 12 := by norm_num
          _ ≤ (2 * m / ε) ^ 12 := pow_le_pow_left₀ (by norm_num) hbase2m 12
      nlinarith [hmB, h12, hmnn]
    linarith
  constructor
  · exact (EpsMem_congr_Q0 hα0 hident).mpr hmem_sub
  · have hsq_eq : Work.FTS.StrongEps.EpsSq α
        (Work.Spaces.mixed b a (Work.FTS.StrongEps.Pz J))
        = Work.FTS.StrongEps.EpsSq α
          (fun z θ => Work.Spaces.mixed b a J z θ
            - c * Work.Spaces.mixed b a Work.FTS.StrongEps.bump z θ) :=
      EpsSq_congr_Q0 hα0 hident
    show Work.FTS.StrongEps.EpsSq α
        (Work.Spaces.mixed b a (Work.FTS.StrongEps.Pz J))
      ≤ 2 * m * (2 * m / ε) ^ 12 * Work.FTS.StrongEps.EpsSq α δ
    rw [hsq_eq]
    calc Work.FTS.StrongEps.EpsSq α
          (fun z θ => Work.Spaces.mixed b a J z θ
            - c * Work.Spaces.mixed b a Work.FTS.StrongEps.bump z θ)
        ≤ (2 * CJ * (CJ / ε) ^ (2 * (a + b))
            + 2 * K * (C12 / Work.FTS.StrongEps.pzNorm) ^ 2 * CJ)
            * Work.FTS.StrongEps.EpsSq α δ := hmain
      _ ≤ 2 * m * (2 * m / ε) ^ 12 * Work.FTS.StrongEps.EpsSq α δ :=
          mul_le_mul_of_nonneg_right harith (Work.FTS.StrongEps.EpsSq_nonneg α δ)

end Work.FTS.StrongEps.EpsRLX
