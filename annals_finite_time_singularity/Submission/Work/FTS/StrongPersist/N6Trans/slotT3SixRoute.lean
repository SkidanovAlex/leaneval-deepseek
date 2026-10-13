import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.GoodOpenBase
import Submission.Work.FTS.VocabO
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.L6Remainder
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.L6Flux.flux_prod_le
import Submission.Work.FTS.StrongPersist.N6Trans.HardPair.mixedTerm_le_six
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.coefFamSix
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.pureGamFamSix
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.fluxFamSix
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.fluxFamSixTop
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixSummandBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The pointwise majorant of the transport integrand by the Leibniz summands of
`mixed b a (f · D_z g)` (`Work.FTS.TransportS.mixed_mul_Dz_open`), with `ρ ≥ 0`. -/
theorem abs_mixed_Dz_le_sum {f g ρ : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (a b : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hρ : 0 ≤ ρ z θ) :
    ρ z θ * |Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
        * Work.Spaces.mixed b a g z θ|
      ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (ρ z θ * |Work.Spaces.mixed b₁ a₁ f z θ
                * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|
                * |Work.Spaces.mixed b a g z θ|) := by
  have hX := Work.FTS.TransportS.mixed_mul_Dz_open b a f g hf hg z θ hz hθ0 hθ1
  -- the absolute value of the Leibniz sum
  have habs : |Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ|
      ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (|Work.Spaces.mixed b₁ a₁ f z θ|
                * |Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|) := by
    rw [hX]
    calc |∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (Work.Spaces.mixed b₁ a₁ f z θ
                  * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ)|
        ≤ ∑ a₁ ∈ Finset.range (a + 1),
            |∑ b₁ ∈ Finset.range (b + 1),
              ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
                * (Work.Spaces.mixed b₁ a₁ f z θ
                    * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            |((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (Work.Spaces.mixed b₁ a₁ f z θ
                  * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ)| :=
          Finset.sum_le_sum fun a₁ _ => Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (|Work.Spaces.mixed b₁ a₁ f z θ|
                  * |Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|) := by
          refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun b₁ _ => ?_
          rw [abs_mul, abs_mul, abs_mul]
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a.choose a₁ : ℝ)),
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b.choose b₁ : ℝ))]
          try ring_nf
  calc ρ z θ * |Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
        * Work.Spaces.mixed b a g z θ|
      = ρ z θ * |Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ|
        * |Work.Spaces.mixed b a g z θ| := by rw [abs_mul]; ring
    _ ≤ ρ z θ * (∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (|Work.Spaces.mixed b₁ a₁ f z θ|
                * |Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|))
        * |Work.Spaces.mixed b a g z θ| := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs hρ) (abs_nonneg _)
    _ = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (ρ z θ * |Work.Spaces.mixed b₁ a₁ f z θ
                * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|
                * |Work.Spaces.mixed b a g z θ|) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a₁ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b₁ _ => ?_
        rw [abs_mul]
        ring

theorem slotT3SixRoute : ∃ C α₂ : ℝ, 0 < C ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (f g : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
        Work.FTS.VocabO.CoefThMem 3 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
        Work.Spaces.HkMem α 7 g → Work.Spaces.DecayAll 6 g →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
        ≤ C * α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
            * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
  obtain ⟨Cs, hCs, hSum⟩ := Work.FTS.StrongPersist.N6Trans.SixRoute.sixSummandBound
  have hCs1 : (0 : ℝ) < 64 * Cs + 1 := by linarith [hCs]
  have hone : (0 : ℝ) < 1 := by norm_num
  refine ⟨64 * Cs + 1, 1, hCs1, hone, ?_⟩
  intro α hαmem f g a b ρ hf hfw hfc hg hgm hgm7 hdec hab hleaf
  have hα : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  have hW0 : 0 ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hfw
  have hK0 : 0 ≤ Work.FTS.VocabO.CoefTh 3 f := Work.FTS.TransportS.coefTh_nonneg 3 f
  have hHs0 : 0 ≤ Work.Spaces.HkSq α 6 g := Work.Spaces.HkSq_nonneg α 6 g
  -- the per-summand integrability and bounds
  have hint : ∀ a₁ ≤ a, ∀ b₁ ≤ b, MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
      * Work.Spaces.mixed b₁ a₁ f p.1 p.2
      * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
      * Work.Spaces.mixed b a g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    fun a₁ ha₁ b₁ hb₁ =>
      (hSum α hαmem f g a b a₁ b₁ ρ hf hfw hfc hg hgm hgm7 hdec hab hleaf ha₁ hb₁).1
  have hbd : ∀ a₁ ≤ a, ∀ b₁ ≤ b, |∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
      * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
      * Work.Spaces.mixed b a g p.1 p.2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
      ≤ Cs * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f) * Work.Spaces.HkSq α 6 g :=
    fun a₁ ha₁ b₁ hb₁ =>
      (hSum α hαmem f g a b a₁ b₁ ρ hf hfw hfc hg hgm hgm7 hdec hab hleaf ha₁ hb₁).2
  -- the majorant majorising the `(0,0)`-free Leibniz summands is integrable, hence so is `ρ·X·Y`
  have hmaj : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (ρ p.1 p.2 * |Work.Spaces.mixed b₁ a₁ f p.1 p.2
              * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2|
              * |Work.Spaces.mixed b a g p.1 p.2|))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine MeasureTheory.integrable_finset_sum _ fun a₁ ha₁ => ?_
    refine MeasureTheory.integrable_finset_sum _ fun b₁ hb₁ => ?_
    have ha₁' : a₁ ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha₁)
    have hb₁' : b₁ ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁)
    refine (((hint a₁ ha₁' b₁ hb₁').abs).const_mul
      ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))).congr ?_
    filter_upwards [Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * |ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
                * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
                * Work.Spaces.mixed b a g p.1 p.2|
          = ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (ρ p.1 p.2 * |Work.Spaces.mixed b₁ a₁ f p.1 p.2
                  * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2|
                  * |Work.Spaces.mixed b a g p.1 p.2|))
      (fun z θ hz hθ0 hθ1 => by
        simp only [abs_mul, abs_of_nonneg (Work.FTS.TransportS.T3SlotAux.IsLeafW.nonneg hleaf z
          ⟨le_of_lt hθ0, le_of_lt hθ1⟩)]
        ring)] with p hp
    exact hp
  have hXY : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
      * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) p.1 p.2
      * Work.Spaces.mixed b a g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
    · -- a.e. strong measurability of the transport integrand
      have hcont : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2
          * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) p.1 p.2
          * Work.Spaces.mixed b a g p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
        have hρcont : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
          rcases hleaf with h | h | ⟨_, h⟩
          · subst h
            simpa [Work.FTS.TransportS.leafEta, Work.FTS.TransportS.SlotT2.canonW] using
              Work.FTS.TransportS.SlotT2.continuousOn_canonW Work.Spaces.eta
          · subst h
            simpa [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.SlotT2.canonW] using
              Work.FTS.TransportS.SlotT2.continuousOn_canonW 0
          · subst h
            simpa [Work.FTS.TransportS.leafGam, Work.FTS.TransportS.SlotT2.canonW] using
              Work.FTS.TransportS.SlotT2.continuousOn_canonW (Work.Spaces.gam α)
        have hXcont : ContinuousOn (fun p : ℝ × ℝ =>
            Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) p.1 p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
          have hpt : ∀ p ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2),
              Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) p.1 p.2
                = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
                    ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
                      * (Work.Spaces.mixed b₁ a₁ f p.1 p.2
                          * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2) :=
            fun p hp =>
              Work.FTS.TransportS.mixed_mul_Dz_open b a f g hf hg p.1 p.2 hp.1 hp.2.1 hp.2.2
          refine ContinuousOn.congr ?_ hpt
          refine continuousOn_finset_sum _ fun a₁ _ => ?_
          refine continuousOn_finset_sum _ fun b₁ _ => ?_
          refine ContinuousOn.const_mul ?_ _
          exact ((Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hf b₁ a₁).mul
            (Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hg
              (b - b₁ + 1) (a - a₁)))
        exact (hρcont.mul hXcont).mul
          (Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hg b a)
      exact Work.Spaces.aesm_of_continuousOn_Qd _ hcont
    · have hpt : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)), ‖ρ p.1 p.2
            * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) p.1 p.2
            * Work.Spaces.mixed b a g p.1 p.2‖
          ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
              ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
                * (ρ p.1 p.2 * |Work.Spaces.mixed b₁ a₁ f p.1 p.2
                    * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2|
                    * |Work.Spaces.mixed b a g p.1 p.2|) :=
        Work.FTS.TransportS.ae_of_forall_Qd fun z θ hz hθ0 hθ1 => by
          rw [Real.norm_eq_abs]
          have hlhs : |ρ z θ * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
                * Work.Spaces.mixed b a g z θ|
              = ρ z θ * |Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
                * Work.Spaces.mixed b a g z θ| := by
            rw [show ρ z θ * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
                  * Work.Spaces.mixed b a g z θ
                = ρ z θ * (Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
                  * Work.Spaces.mixed b a g z θ) from by ring,
              abs_mul,
              abs_of_nonneg (Work.FTS.TransportS.T3SlotAux.IsLeafW.nonneg hleaf z
                ⟨le_of_lt hθ0, le_of_lt hθ1⟩)]
          rw [hlhs]
          exact abs_mixed_Dz_le_sum (f := f) (g := g) (ρ := ρ) hf hg a b hz hθ0 hθ1
            (Work.FTS.TransportS.T3SlotAux.IsLeafW.nonneg hleaf z ⟨le_of_lt hθ0, le_of_lt hθ1⟩)
      filter_upwards [hpt] with p hp
      exact hp
  -- the expansion
  rw [Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion (α := α) a b ρ hf hg hXY hint]
  -- ### the summation
  set Kv : ℝ := Cs * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
      * Work.Spaces.HkSq α 6 g with hKv
  have hKv0 : 0 ≤ Kv := by
    rw [hKv]
    have h1 : 0 ≤ Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f := by linarith
    positivity
  have hbnd : ∀ a₁ b₁ : ℕ, a₁ ≤ a → b₁ ≤ b →
      |((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
        * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
            * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
            * Work.Spaces.mixed b a g p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))|
      ≤ ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * Kv := by
    intro a₁ b₁ ha₁ hb₁
    have h4 : |∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
            * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
            * Work.Spaces.mixed b a g p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))| ≤ Kv := by
      rw [hKv]
      exact hbd a₁ ha₁ b₁ hb₁
    rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    exact mul_le_mul_of_nonneg_left h4
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hbinom : (∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
      ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))) = (2 : ℝ) ^ a * (2 : ℝ) ^ b := by
    rw [← Finset.sum_mul_sum]
    congr 1
    · rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
    · rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
  have hpow : (2 : ℝ) ^ a * (2 : ℝ) ^ b ≤ 64 := by
    rw [← pow_add]
    calc (2 : ℝ) ^ (a + b) ≤ (2 : ℝ) ^ 6 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 64 := by norm_num
  have hmain : |∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
              * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
              * Work.Spaces.mixed b a g p.1 p.2
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)))|
      ≤ 64 * Kv := by
    have h1 : |∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
                * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
                * Work.Spaces.mixed b a g p.1 p.2
              ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                (MeasureTheory.volume.restrict Work.Spaces.Iθ)))|
        ≤ ∑ a₁ ∈ Finset.range (a + 1), |∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
                  * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
                  * Work.Spaces.mixed b a g p.1 p.2
                ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                  (MeasureTheory.volume.restrict Work.Spaces.Iθ)))| :=
          Finset.abs_sum_le_sum_abs _ _
    have h2 : (∑ a₁ ∈ Finset.range (a + 1), |∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
                  * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
                  * Work.Spaces.mixed b a g p.1 p.2
                ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                  (MeasureTheory.volume.restrict Work.Spaces.Iθ)))|)
        ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * Kv := by
      refine Finset.sum_le_sum fun a₁ ha₁ => ?_
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      exact Finset.sum_le_sum fun b₁ hb₁ => hbnd a₁ b₁
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha₁))
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁))
    have h3 : (∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * Kv)
        = (∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))) * Kv := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a₁ _ => ?_
      rw [Finset.sum_mul]
    refine (h1.trans h2).trans ?_
    rw [h3, hbinom]
    exact mul_le_mul_of_nonneg_right hpow hKv0
  -- ### the reduction to the statement
  rw [hKv] at hmain
  have hαle1 : (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg (le_of_lt hα) (1 / 2)]
    rw [one_le_inv₀ (Real.rpow_pos_of_pos hα (1 / 2))]
    exact Real.rpow_le_one (le_of_lt hα) hα1 (by norm_num)
  have hsq : (Work.Spaces.HkNorm α 6 g) ^ 2 = Work.Spaces.HkSq α 6 g := by
    rw [Work.Spaces.HkNorm]
    exact Real.sq_sqrt hHs0
  have hfin : 64 * (Cs * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
        * Work.Spaces.HkSq α 6 g)
      ≤ (64 * Cs + 1) * α ^ (-(1 / 2 : ℝ))
          * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
          * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
    rw [hsq]
    have h1 : 0 ≤ Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f := by linarith
    have h2 : 0 ≤ Cs * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
        * Work.Spaces.HkSq α 6 g := by positivity
    nlinarith [hαle1, h1, h2, hHs0, hCs.le,
      mul_le_mul_of_nonneg_right hαle1 (mul_nonneg h1 hHs0),
      mul_le_mul_of_nonneg_left hCs.le (mul_nonneg h1 hHs0)]
  exact hmain.trans hfin

end

end Work.FTS.StrongPersist.N6Trans
