import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.Honesty.EllEstUnifAllClean
import Submission.Work.FTS.PhiStar.Honesty.ellEstUnif_diff
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenCoer.SlotWCommon
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.N6_prod
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.Spaces.SmoothCompact_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

set_option autoImplicit false

/-- **The a priori bounds for the three slots, from a bound and the Cauchy property of the
sources.**

This is the honest content of `slot_aPriori`: `EllEstUnif` at level `k+1` gives
`α²|z²∂_z²Ψ_n|_{ℋ^{k+1}} + |∂_θθΨ_n|_{ℋ^{k+1}} ≤ C|G_n|_{ℋ^{k+1}}`, and the same estimate applied
to the difference data `(G_n − G_m, Ψ_n − Ψ_m)` (which is in the class by `ellWeakPos_sub`) gives
the Cauchy property.  The third slot is `D_z ∂_θθΨ_n` and is bounded at level `k` by
`HkSq α k (D_z u) ≤ HkSq α (k+1) u`. -/
theorem slot_aPriori_of_source (k : ℕ) (hk : 1 ≤ k) {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {G : ℕ → ℝ → ℝ → ℝ}
    (hsmG : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n))
    (hGn : ∀ n : ℕ, Work.Spaces.HkMem α (k + 1) (G n))
    (hEll : ∀ n : ℕ, Work.FTS.EllipticEst.TT.EllWeakPos α (k + 1) (G n)
      (Work.FTS.PhiStar.Series.psiSeries α (G n)))
    (hbound : ∃ B : ℝ, ∀ n : ℕ, Work.Spaces.HkSq α (k + 1) (G n) ≤ B)
    (hcauchy : Filter.Tendsto (fun nm : ℕ × ℕ => Work.Spaces.HkSq α (k + 1)
        (fun z θ => G nm.1 z θ - G nm.2 z θ)) (Filter.atTop ×ˢ Filter.atTop) (nhds 0)) :
    ∃ B : ℝ, 0 < B ∧
      (∀ (r : Fin 3) (n : ℕ), Work.Spaces.HkMem α k
        (slot r.1 (Work.FTS.PhiStar.Series.psiSeries α (G n)))) ∧
      (∀ (r : Fin 3) (n : ℕ), Work.Spaces.HkSq α k
        (slot r.1 (Work.FTS.PhiStar.Series.psiSeries α (G n))) ≤ B) ∧
      (∀ (r : Fin 3) (n m : ℕ), Work.Spaces.HkMem α k
        (fun z θ => slot r.1 (Work.FTS.PhiStar.Series.psiSeries α (G n)) z θ
          - slot r.1 (Work.FTS.PhiStar.Series.psiSeries α (G m)) z θ)) ∧
      (∀ r : Fin 3, Filter.Tendsto (fun nm : ℕ × ℕ => Work.Spaces.HkSq α k
          (fun z θ => slot r.1 (Work.FTS.PhiStar.Series.psiSeries α (G nm.1)) z θ
            - slot r.1 (Work.FTS.PhiStar.Series.psiSeries α (G nm.2)) z θ))
        (Filter.atTop ×ˢ Filter.atTop) (nhds 0)) := by
  have hk2 : 2 ≤ k + 1 := by omega
  obtain ⟨C, hCpos, hEst⟩ := Work.FTS.PhiStar.Honesty.ellEstUnifAll_clean (k + 1) hk2
  -- shorthand
  set Ψ : ℕ → ℝ → ℝ → ℝ := fun n => Work.FTS.PhiStar.Series.psiSeries α (G n) with hΨdef
  have hΨ : ∀ n, Ψ n = Work.FTS.PhiStar.Series.psiSeries α (G n) := fun n => rfl
  have hsmΨ : ∀ n, Work.FTS.EllipticEst.SmoothOpen (Ψ n) :=
    fun n => Work.FTS.EllipticEst.smoothOpen_of_forall (hEll n).smooth
  obtain ⟨B₀, hB₀⟩ := hbound
  have hB₀nn : 0 ≤ B₀ := le_trans (Work.Spaces.HkSq_nonneg α (k + 1) (G 0)) (hB₀ 0)
  have hGN : ∀ n, Work.Spaces.HkNorm α (k + 1) (G n) ≤ Real.sqrt B₀ := by
    intro n
    rw [Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt (hB₀ n)
  -- the elliptic estimate for one datum, in the two forms needed
  have hNorm2 : ∀ n, Work.Spaces.HkNorm α (k + 1) (Work.Spaces.pthIter 2 (Ψ n))
      ≤ C * Work.Spaces.HkNorm α (k + 1) (G n) := by
    intro n
    have hE := hEst α (G n) (Ψ n) hα hα4 (hEll n)
    have h0 : 0 ≤ α ^ 2 * Work.Spaces.HkNorm α (k + 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Ψ n) z θ) :=
      mul_nonneg (sq_nonneg α) (Real.sqrt_nonneg _)
    linarith
  have hNorm1 : ∀ n, Work.Spaces.HkNorm α (k + 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Ψ n) z θ)
      ≤ C * Work.Spaces.HkNorm α (k + 1) (G n) / α ^ 2 := by
    intro n
    have hE := hEst α (G n) (Ψ n) hα hα4 (hEll n)
    have h0 : 0 ≤ Work.Spaces.HkNorm α (k + 1) (Work.Spaces.pthIter 2 (Ψ n)) :=
      Real.sqrt_nonneg _
    have h3 : α ^ 2 * Work.Spaces.HkNorm α (k + 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Ψ n) z θ)
        ≤ C * Work.Spaces.HkNorm α (k + 1) (G n) := by linarith
    have hα2 : 0 < α ^ 2 := pow_pos hα 2
    calc Work.Spaces.HkNorm α (k + 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Ψ n) z θ)
        = α ^ 2 * Work.Spaces.HkNorm α (k + 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Ψ n) z θ) / α ^ 2 := by
          field_simp
      _ ≤ C * Work.Spaces.HkNorm α (k + 1) (G n) / α ^ 2 := by gcongr
  -- the level-`(k+1)` bounds, squared
  have hsq2 : ∀ n, Work.Spaces.HkSq α (k + 1) (Work.Spaces.pthIter 2 (Ψ n))
      ≤ (C * Real.sqrt B₀) ^ 2 := by
    intro n
    calc Work.Spaces.HkSq α (k + 1) (Work.Spaces.pthIter 2 (Ψ n))
        ≤ C ^ 2 * Work.Spaces.HkSq α (k + 1) (G n) :=
          HkSq_le_of_HkNorm_le α hCpos.le (hNorm2 n)
      _ ≤ C ^ 2 * B₀ := mul_le_mul_of_nonneg_left (hB₀ n) (sq_nonneg C)
      _ = (C * Real.sqrt B₀) ^ 2 := by rw [mul_pow, Real.sq_sqrt hB₀nn]
  have hsq1 : ∀ n, Work.Spaces.HkSq α (k + 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Ψ n) z θ)
      ≤ (C * Real.sqrt B₀ / α ^ 2) ^ 2 := by
    intro n
    have hN : Work.Spaces.HkNorm α (k + 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Ψ n) z θ)
        ≤ (C / α ^ 2) * Work.Spaces.HkNorm α (k + 1) (G n) := by
      calc _ ≤ C * Work.Spaces.HkNorm α (k + 1) (G n) / α ^ 2 := hNorm1 n
        _ = (C / α ^ 2) * Work.Spaces.HkNorm α (k + 1) (G n) := by ring
    calc Work.Spaces.HkSq α (k + 1)
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Ψ n) z θ)
        ≤ (C / α ^ 2) ^ 2 * Work.Spaces.HkSq α (k + 1) (G n) :=
          HkSq_le_of_HkNorm_le α (by positivity) hN
      _ ≤ (C / α ^ 2) ^ 2 * B₀ := mul_le_mul_of_nonneg_left (hB₀ n) (sq_nonneg _)
      _ = (C * Real.sqrt B₀ / α ^ 2) ^ 2 := by
          rw [show (C * Real.sqrt B₀ / α ^ 2) ^ 2 = C ^ 2 * B₀ / (α ^ 2) ^ 2 from by
            rw [div_pow, mul_pow, Real.sq_sqrt hB₀nn]]
          ring
  -- the level-`k` bounds (slot1 and slot2 by monotonicity, slot3 by the index shift)
  have hlev1 : ∀ n, Work.Spaces.HkSq α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Ψ n) z θ)
      ≤ (C * Real.sqrt B₀ / α ^ 2) ^ 2 :=
    fun n => le_trans (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by omega) (hEll n).memA)
      (hsq1 n)
  have hlev2 : ∀ n, Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 (Ψ n))
      ≤ (C * Real.sqrt B₀) ^ 2 :=
    fun n => le_trans (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by omega) (hEll n).memB)
      (hsq2 n)
  have hlev3 : ∀ n, Work.Spaces.HkSq α k
        (Work.Spaces.Dz (Work.Spaces.pthIter 2 (Ψ n)))
      ≤ (C * Real.sqrt B₀) ^ 2 :=
    fun n => le_trans
      (Work.FTS.StrongPersist.hkSq_dz_le_open α k
        (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl (hsmΨ n) 2) (hEll n).memB)
      (hsq2 n)
  -- the difference data and its estimate
  have hDiffEll : ∀ n m : ℕ, Work.FTS.EllipticEst.TT.EllWeakPos α (k + 1)
      (fun z θ => G n z θ - G m z θ) (fun z θ => Ψ n z θ - Ψ m z θ) :=
    fun n m => ellWeakPos_sub (k + 1) (hEll n) (hEll m)
  have hDiffNorm : ∀ n m : ℕ,
      Work.Spaces.HkNorm α (k + 1) (Work.Spaces.pthIter 2 (fun z θ => Ψ n z θ - Ψ m z θ))
        ≤ C * Work.Spaces.HkNorm α (k + 1) (fun z θ => G n z θ - G m z θ) := by
    intro n m
    have hE := hEst α (fun z θ => G n z θ - G m z θ)
      (fun z θ => Ψ n z θ - Ψ m z θ) hα hα4 (hDiffEll n m)
    have h0 : 0 ≤ α ^ 2 * Work.Spaces.HkNorm α (k + 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ n z θ - Ψ m z θ) z θ) :=
      mul_nonneg (sq_nonneg α) (Real.sqrt_nonneg _)
    linarith
  have hDiffNorm1 : ∀ n m : ℕ,
      Work.Spaces.HkNorm α (k + 1)
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ n z θ - Ψ m z θ) z θ)
        ≤ C * Work.Spaces.HkNorm α (k + 1) (fun z θ => G n z θ - G m z θ) / α ^ 2 := by
    intro n m
    have hE := hEst α (fun z θ => G n z θ - G m z θ)
      (fun z θ => Ψ n z θ - Ψ m z θ) hα hα4 (hDiffEll n m)
    have h0 : 0 ≤ Work.Spaces.HkNorm α (k + 1)
        (Work.Spaces.pthIter 2 (fun z θ => Ψ n z θ - Ψ m z θ)) := Real.sqrt_nonneg _
    have h3 : α ^ 2 * Work.Spaces.HkNorm α (k + 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ n z θ - Ψ m z θ) z θ)
        ≤ C * Work.Spaces.HkNorm α (k + 1) (fun z θ => G n z θ - G m z θ) := by linarith
    have hα2 : 0 < α ^ 2 := pow_pos hα 2
    calc Work.Spaces.HkNorm α (k + 1)
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ n z θ - Ψ m z θ) z θ)
        = α ^ 2 * Work.Spaces.HkNorm α (k + 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ n z θ - Ψ m z θ) z θ)
            / α ^ 2 := by field_simp
      _ ≤ C * Work.Spaces.HkNorm α (k + 1) (fun z θ => G n z θ - G m z θ) / α ^ 2 := by gcongr
  -- the Cauchy bounds for the three slots of the *differences*
  have hC2 : ∀ n m : ℕ, Work.Spaces.HkSq α k
        (fun z θ => Work.Spaces.pthIter 2 (Ψ n) z θ - Work.Spaces.pthIter 2 (Ψ m) z θ)
      ≤ C ^ 2 * Work.Spaces.HkSq α (k + 1) (fun z θ => G n z θ - G m z θ) := by
    intro n m
    have hcongr : Work.Spaces.HkSq α k
          (fun z θ => Work.Spaces.pthIter 2 (Ψ n) z θ - Work.Spaces.pthIter 2 (Ψ m) z θ)
        = Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 (fun z θ => Ψ n z θ - Ψ m z θ)) := by
      rw [Work.FTS.EllipticEst.HkSq_congr_open]
      intro z θ hz hθ hθ2
      exact (Work.FTS.GalBasis.pthIter_sub_eqOn (V := Work.FTS.EllipticEst.Q0)
        Work.FTS.EllipticEst.isOpen_Q0 2 ((hsmΨ n).forall 3) ((hsmΨ m).forall 3)
        (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from ⟨hz, hθ, hθ2⟩)).symm
    calc Work.Spaces.HkSq α k
          (fun z θ => Work.Spaces.pthIter 2 (Ψ n) z θ - Work.Spaces.pthIter 2 (Ψ m) z θ)
        = Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 (fun z θ => Ψ n z θ - Ψ m z θ)) :=
          hcongr
      _ ≤ Work.Spaces.HkSq α (k + 1)
            (Work.Spaces.pthIter 2 (fun z θ => Ψ n z θ - Ψ m z θ)) :=
          Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by omega) (hDiffEll n m).memB
      _ ≤ C ^ 2 * Work.Spaces.HkSq α (k + 1) (fun z θ => G n z θ - G m z θ) :=
          HkSq_le_of_HkNorm_le α hCpos.le (hDiffNorm n m)
  have hC1 : ∀ n m : ℕ, Work.Spaces.HkSq α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Ψ n) z θ
          - z ^ 2 * Work.Spaces.pzIter 2 (Ψ m) z θ)
      ≤ (C / α ^ 2) ^ 2 * Work.Spaces.HkSq α (k + 1) (fun z θ => G n z θ - G m z θ) := by
    intro n m
    have hcongr : Work.Spaces.HkSq α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Ψ n) z θ
            - z ^ 2 * Work.Spaces.pzIter 2 (Ψ m) z θ)
        = Work.Spaces.HkSq α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ n z θ - Ψ m z θ) z θ) := by
      rw [Work.FTS.EllipticEst.HkSq_congr_open]
      intro z θ hz hθ hθ2
      have hsub := Work.FTS.GalBasis.pzIter_sub_eqOn (V := Work.FTS.EllipticEst.Q0)
        Work.FTS.EllipticEst.isOpen_Q0 2 ((hsmΨ n).forall 3) ((hsmΨ m).forall 3)
        (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from ⟨hz, hθ, hθ2⟩)
      simp only [Function.uncurry] at hsub
      rw [← mul_sub, ← hsub]
    have hCα : 0 ≤ C / α ^ 2 := by positivity
    calc Work.Spaces.HkSq α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Ψ n) z θ
            - z ^ 2 * Work.Spaces.pzIter 2 (Ψ m) z θ)
        = Work.Spaces.HkSq α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ n z θ - Ψ m z θ) z θ) :=
          hcongr
      _ ≤ Work.Spaces.HkSq α (k + 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ n z θ - Ψ m z θ) z θ) :=
          Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by omega) (hDiffEll n m).memA
      _ ≤ (C / α ^ 2) ^ 2 * Work.Spaces.HkSq α (k + 1) (fun z θ => G n z θ - G m z θ) := by
          have hD := hDiffNorm1 n m
          have h' : Work.Spaces.HkNorm α (k + 1)
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ n z θ - Ψ m z θ) z θ)
              ≤ (C / α ^ 2) * Work.Spaces.HkNorm α (k + 1)
                (fun z θ => G n z θ - G m z θ) := by
            calc _ ≤ C * Work.Spaces.HkNorm α (k + 1) (fun z θ => G n z θ - G m z θ) / α ^ 2 := hD
              _ = (C / α ^ 2) * Work.Spaces.HkNorm α (k + 1)
                    (fun z θ => G n z θ - G m z θ) := by ring
          exact HkSq_le_of_HkNorm_le α hCα h'
  have hC3 : ∀ n m : ℕ, Work.Spaces.HkSq α k
        (fun z θ => Work.Spaces.Dz (Work.Spaces.pthIter 2 (Ψ n)) z θ
          - Work.Spaces.Dz (Work.Spaces.pthIter 2 (Ψ m)) z θ)
      ≤ C ^ 2 * Work.Spaces.HkSq α (k + 1) (fun z θ => G n z θ - G m z θ) := by
    intro n m
    have hcongr : Work.Spaces.HkSq α k
          (fun z θ => Work.Spaces.Dz (Work.Spaces.pthIter 2 (Ψ n)) z θ
            - Work.Spaces.Dz (Work.Spaces.pthIter 2 (Ψ m)) z θ)
        = Work.Spaces.HkSq α k
            (Work.Spaces.Dz (Work.Spaces.pthIter 2 (fun z θ => Ψ n z θ - Ψ m z θ))) := by
      rw [Work.FTS.EllipticEst.HkSq_congr_open]
      intro z θ hz hθ hθ2
      exact Dz_pthIter2_sub (hsmΨ n) (hsmΨ m) z θ hz hθ hθ2
    calc Work.Spaces.HkSq α k
          (fun z θ => Work.Spaces.Dz (Work.Spaces.pthIter 2 (Ψ n)) z θ
            - Work.Spaces.Dz (Work.Spaces.pthIter 2 (Ψ m)) z θ)
        = Work.Spaces.HkSq α k
            (Work.Spaces.Dz (Work.Spaces.pthIter 2 (fun z θ => Ψ n z θ - Ψ m z θ))) := hcongr
      _ ≤ Work.Spaces.HkSq α (k + 1)
            (Work.Spaces.pthIter 2 (fun z θ => Ψ n z θ - Ψ m z θ)) :=
          Work.FTS.StrongPersist.hkSq_dz_le_open α k
            (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl
              (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl (hsmΨ n) (hsmΨ m)) 2)
            (hDiffEll n m).memB
      _ ≤ C ^ 2 * Work.Spaces.HkSq α (k + 1) (fun z θ => G n z θ - G m z θ) :=
          HkSq_le_of_HkNorm_le α hCpos.le (hDiffNorm n m)
  -- the HkMem clauses
  have hmem1 : ∀ n, Work.Spaces.HkMem α k
      (Work.Spaces.Dz (Work.Spaces.pthIter 2 (Ψ n))) :=
    fun n => Work.FTS.OpenPkg.HkMem_mono_open
      (Work.FTS.EllipticEst.SmoothOpen.Dz
        (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl (hsmΨ n) 2)) k (by omega) (hEll n).memZPth2
  have hmem2 : ∀ n, Work.Spaces.HkMem α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Ψ n) z θ) :=
    fun n => Work.FTS.OpenPkg.HkMem_mono_open
      (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
        Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl ((hsmΨ n).pzIter 2)) k (by omega) (hEll n).memA
  have hmem3 : ∀ n, Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 (Ψ n)) :=
    fun n => Work.FTS.OpenPkg.HkMem_mono_open
      (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl (hsmΨ n) 2) k (by omega) (hEll n).memB
  -- and for the differences (transfer from the difference data along `Q0`)
  have hdmem2 : ∀ n m, Work.Spaces.HkMem α k
      (fun z θ => Work.Spaces.pthIter 2 (Ψ n) z θ - Work.Spaces.pthIter 2 (Ψ m) z θ) := by
    intro n m
    refine (Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k
      (Work.FTS.OpenPkg.HkMem_mono_open
        (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl
          (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl (hsmΨ n) (hsmΨ m)) 2)
        k (by omega) (hDiffEll n m).memB) ?_)
    intro z hz θ hθ
    have h := Work.FTS.GalBasis.pthIter_sub_eqOn (V := Work.FTS.EllipticEst.Q0)
      Work.FTS.EllipticEst.isOpen_Q0 2 ((hsmΨ n).forall 3) ((hsmΨ m).forall 3)
      (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from ⟨hz, hθ⟩)
    simpa only [Function.uncurry] using h
  have hdmem1 : ∀ n m, Work.Spaces.HkMem α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Ψ n) z θ
        - z ^ 2 * Work.Spaces.pzIter 2 (Ψ m) z θ) := by
    intro n m
    refine (Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k
      (Work.FTS.OpenPkg.HkMem_mono_open
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
          Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
          ((Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl (hsmΨ n) (hsmΨ m)).pzIter 2))
        k (by omega) (hDiffEll n m).memA) ?_)
    intro z hz θ hθ
    have hsub := Work.FTS.GalBasis.pzIter_sub_eqOn (V := Work.FTS.EllipticEst.Q0)
      Work.FTS.EllipticEst.isOpen_Q0 2 ((hsmΨ n).forall 3) ((hsmΨ m).forall 3)
      (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from ⟨hz, hθ⟩)
    simp only [Function.uncurry] at hsub
    rw [← mul_sub, ← hsub]
  have hdmem3 : ∀ n m, Work.Spaces.HkMem α k
      (fun z θ => Work.Spaces.Dz (Work.Spaces.pthIter 2 (Ψ n)) z θ
        - Work.Spaces.Dz (Work.Spaces.pthIter 2 (Ψ m)) z θ) := by
    intro n m
    refine (Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k
      (Work.FTS.OpenPkg.HkMem_mono_open
        (Work.FTS.EllipticEst.SmoothOpen.Dz
          (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl
            (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl (hsmΨ n) (hsmΨ m)) 2))
        k (by omega) (hDiffEll n m).memZPth2) ?_)
    intro z hz θ hθ
    exact (Dz_pthIter2_sub (hsmΨ n) (hsmΨ m) z θ hz hθ.1 hθ.2).symm
  -- the squeeze for the Cauchy property
  have hTend2 : Filter.Tendsto (fun nm : ℕ × ℕ => Work.Spaces.HkSq α k
      (fun z θ => Work.Spaces.pthIter 2 (Ψ nm.1) z θ
        - Work.Spaces.pthIter 2 (Ψ nm.2) z θ))
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
    refine squeeze_zero (fun nm => Work.Spaces.HkSq_nonneg α k _)
      (fun nm => hC2 nm.1 nm.2) ?_
    simpa using hcauchy.const_mul (C ^ 2)
  have hTend1 : Filter.Tendsto (fun nm : ℕ × ℕ => Work.Spaces.HkSq α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Ψ nm.1) z θ
        - z ^ 2 * Work.Spaces.pzIter 2 (Ψ nm.2) z θ))
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
    refine squeeze_zero (fun nm => Work.Spaces.HkSq_nonneg α k _)
      (fun nm => hC1 nm.1 nm.2) ?_
    simpa using hcauchy.const_mul ((C / α ^ 2) ^ 2)
  have hTend3 : Filter.Tendsto (fun nm : ℕ × ℕ => Work.Spaces.HkSq α k
      (fun z θ => Work.Spaces.Dz (Work.Spaces.pthIter 2 (Ψ nm.1)) z θ
        - Work.Spaces.Dz (Work.Spaces.pthIter 2 (Ψ nm.2)) z θ))
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
    refine squeeze_zero (fun nm => Work.Spaces.HkSq_nonneg α k _)
      (fun nm => hC3 nm.1 nm.2) ?_
    simpa using hcauchy.const_mul (C ^ 2)
  -- assemble
  refine ⟨max 1 (max ((C * Real.sqrt B₀ / α ^ 2) ^ 2) ((C * Real.sqrt B₀) ^ 2)),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_, ?_, ?_, ?_⟩
  · intro r n
    fin_cases r
    · exact hmem2 n
    · exact hmem3 n
    · exact hmem1 n
  · intro r n
    fin_cases r
    · exact le_trans (hlev1 n) (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact le_trans (hlev2 n) (le_trans (le_max_right _ _) (le_max_right _ _))
    · exact le_trans (hlev3 n) (le_trans (le_max_right _ _) (le_max_right _ _))
  · intro r n m
    fin_cases r
    · exact hdmem1 n m
    · exact hdmem2 n m
    · exact hdmem3 n m
  · intro r
    fin_cases r
    · exact hTend1
    · exact hTend2
    · exact hTend3

end Work.FTS.PhiStar.Honesty.SlotsLimit
