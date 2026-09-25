import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmCz.eucRadialBound
import Submission.Work.CR.Flat.Cauchy.bmCz.abs_eucNorm_sub_le
import Submission.Work.CR.Flat.Cauchy.bmCz.czAux
import Submission.Work.CR.Flat.Cauchy.bmCz.czFarKernelDiff
import Submission.Work.CR.Flat.Cauchy.bmCz.czCrescent

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy.bmCz

open Work.CR.Flat.Cauchy

/-- Continuity of a Hölder map on `ℂⁿ`. -/
theorem continuous_of_holder_euc {n : ℕ} {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    {g : (Fin n → ℂ) → ℂ} (hg : ∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) :
    Continuous g := by
  have hH : HolderWith (Real.toNNReal K) (Real.toNNReal α) g := by
    intro x y
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
    refine le_trans (ENNReal.ofReal_le_ofReal (hg x y)) ?_
    rw [ENNReal.ofReal_mul hK, ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hα.le]
    rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal K hK, Real.coe_toNNReal α hα.le]
  exact hH.continuous (by rw [Real.toNNReal_pos]; exact hα)

open Work.CR.Flat.Cauchy in
theorem czKernel_holderBound {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {R : ℝ} (hR : 0 < R)
    {Φ : (Fin n → ℂ) → ℂ} (hΦm : MeasureTheory.AEStronglyMeasurable Φ MeasureTheory.volume)
    {A : ℝ} (hA : 0 < A)
    (hP1 : ∀ x : Fin n → ℂ, x ≠ 0 → ‖Φ x‖ ≤ A / (Work.CR.Flat.Cauchy.eucNorm x) ^ (2 * n))
    (hP2 : ∀ x h : Fin n → ℂ, 2 * Work.CR.Flat.Cauchy.eucNorm h ≤ Work.CR.Flat.Cauchy.eucNorm x →
      ‖Φ (x - h) - Φ x‖ ≤ A * Work.CR.Flat.Cauchy.eucNorm h / (Work.CR.Flat.Cauchy.eucNorm x) ^ (2 * n + 1))
    (hH2 : ∀ a b : ℝ, 0 < a → a < b → ∫ x in Work.CR.Flat.Cauchy.eucShell a b, Φ x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ), 0 ≤ K → ∀ g : (Fin n → ℂ) → ℂ,
      (∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) →
      (∀ x : Fin n → ℂ, R ≤ Work.CR.Flat.Cauchy.eucNorm x → g x = 0) →
      (∀ z : Fin n → ℂ,
        ‖∫ x in Work.CR.Flat.Cauchy.eucBall (4 * R), Φ x * (g (z + x) - g z)‖ ≤ C * K) ∧
      (∀ z z' : Fin n → ℂ,
        ‖(∫ x in Work.CR.Flat.Cauchy.eucBall (4 * R), Φ x * (g (z + x) - g z))
            - (∫ x in Work.CR.Flat.Cauchy.eucBall (4 * R), Φ x * (g (z' + x) - g z'))‖
          ≤ C * K * ‖z - z'‖ ^ α) := by
  classical
  obtain ⟨Crad, hCradpos, hCrad⟩ := eucRadialBound hn (α - 2 * (n : ℝ)) (by linarith)
  obtain ⟨Ccr, hCcrpos, hCcr⟩ := czCrescent hn hα hα1
  obtain ⟨Cfr, hCfrpos, hCfr⟩ := czFarKernelDiff hn hα hα1 hA hR
  set CA : ℝ := A * Crad * (4 * R) ^ α with hCA
  set CB : ℝ := 2 * A * Crad * (2 * Real.sqrt n) ^ α + Cfr * A * (Real.sqrt n) ^ α
      + Ccr * A * (Real.sqrt n) ^ α with hCB
  have hCApos : 0 < CA := by rw [hCA]; positivity
  have hCBpos : 0 < CB := by rw [hCB]; positivity
  have hsqn : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  refine ⟨max (max CA CB) (2 * CA), ?_, ?_⟩
  · positivity
  · intro K hK g hg hgsupp
    have hgcont : Continuous g := continuous_of_holder_euc hα hK hg
    have hgmeas : AEStronglyMeasurable g volume := hgcont.aestronglyMeasurable
    have hmeas_of : ∀ w : Fin n → ℂ,
        AEStronglyMeasurable (fun x : Fin n → ℂ => Φ x * (g (w + x) - g w))
          (volume.restrict (eucBall (n := n) (4 * R))) := by
      intro w
      refine (hΦm.mono_measure Measure.restrict_le_self).mul ?_
      exact (((hgcont.comp (continuous_const.add continuous_id)).sub
        continuous_const).aestronglyMeasurable).mono_measure Measure.restrict_le_self
    have hball : ∀ z, ‖∫ x in eucBall (4 * R), Φ x * (g (z + x) - g z)‖ ≤ CA * K := by
      intro z
      have hInt : IntegrableOn (fun x : Fin n → ℂ => Φ x * (g (z + x) - g z))
          (eucBall (n := n) (4 * R)) volume :=
        integrableOn_of_le_eucNorm_rpow_ball hn (s := α - 2 * (n : ℝ)) (by linarith)
          (hmeas_of z) (C := A * K) (by positivity)
          (fun x _ => norm_Phi_mul_le hα hα1 hA hK hP1 hg z x)
      have hmaj : IntegrableOn (fun x : Fin n → ℂ => A * K * eucNorm x ^ (α - 2 * (n : ℝ)))
          (eucBall (n := n) (4 * R)) volume :=
        MeasureTheory.Integrable.const_mul
          (integrableOn_eucNorm_rpow_ball hn (by linarith) (4 * R)) (A * K)
      have hb := norm_setIntegral_le_of_norm_le' (measurableSet_eucBall (n := n) (4 * R)) hmaj
        (fun x _ => norm_Phi_mul_le hα hα1 hA hK hP1 hg z x)
      refine le_trans hb ?_
      rw [MeasureTheory.integral_const_mul]
      have h4 := hCrad (4 * R) (by linarith)
      rw [show α - 2 * (n : ℝ) + 2 * (n : ℝ) = α from by ring] at h4
      calc A * K * ∫ x in eucBall (n := n) (4 * R), eucNorm x ^ (α - 2 * (n : ℝ))
          ≤ A * K * (Crad * (4 * R) ^ α) := mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = A * Crad * (4 * R) ^ α * K := by ring
    constructor
    · intro z
      refine le_trans (hball z) ?_
      refine mul_le_mul_of_nonneg_right ?_ hK
      exact le_trans (le_max_left _ _) (le_max_left _ _)
    · intro z z'
      by_cases hzz : z = z'
      · subst hzz
        rw [sub_self, norm_zero, sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero]
      · have hδpos : 0 < ‖z - z'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzz)
        rcases le_or_gt 1 ‖z - z'‖ with hδ1 | hδ1
        · -- global case
          have hp : (1:ℝ) ≤ ‖z - z'‖ ^ α := Real.one_le_rpow hδ1 hα.le
          have hCpos : 0 ≤ max (max CA CB) (2 * CA) :=
            le_of_lt (lt_of_lt_of_le (by linarith [hCApos]) (le_max_right _ _))
          calc ‖(∫ x in eucBall (4 * R), Φ x * (g (z + x) - g z))
                - (∫ x in eucBall (4 * R), Φ x * (g (z' + x) - g z'))‖
              ≤ ‖∫ x in eucBall (4 * R), Φ x * (g (z + x) - g z)‖
                + ‖∫ x in eucBall (4 * R), Φ x * (g (z' + x) - g z')‖ := norm_sub_le _ _
            _ ≤ 2 * CA * K := by
                rw [show 2 * CA * K = CA * K + CA * K from by ring]
                exact add_le_add (hball z) (hball z')
            _ ≤ max (max CA CB) (2 * CA) * K * ‖z - z'‖ ^ α := by
                have h1 : 2 * CA * K ≤ max (max CA CB) (2 * CA) * K :=
                  mul_le_mul_of_nonneg_right (le_max_right _ _) hK
                have h2 : max (max CA CB) (2 * CA) * K * 1
                    ≤ max (max CA CB) (2 * CA) * K * ‖z - z'‖ ^ α :=
                  mul_le_mul_of_nonneg_left hp (mul_nonneg hCpos hK)
                calc 2 * CA * K ≤ max (max CA CB) (2 * CA) * K := h1
                  _ = max (max CA CB) (2 * CA) * K * 1 := by ring
                  _ ≤ max (max CA CB) (2 * CA) * K * ‖z - z'‖ ^ α := h2
        · -- ================= local case =================
          set h : Fin n → ℂ := z' - z with hh
          have hz' : z + h = z' := by rw [hh]; abel
          have hhnz : h ≠ 0 := by rw [hh]; exact sub_ne_zero.mpr (Ne.symm hzz)
          set η : ℝ := eucNorm h with hη
          have hηpos : 0 < η := by rw [hη]; exact eucNorm_pos hhnz
          have hηnneg : 0 ≤ η := le_of_lt hηpos
          have hηδ : η ≤ Real.sqrt n * ‖z - z'‖ := by
            rw [hη, hh]
            calc eucNorm (z' - z) ≤ Real.sqrt n * ‖z' - z‖ := eucNorm_le_sqrt_mul_norm _
              _ = Real.sqrt n * ‖z - z'‖ := by rw [norm_sub_rev]
          have hηα : η ^ α ≤ (Real.sqrt n) ^ α * ‖z - z'‖ ^ α := by
            calc η ^ α ≤ (Real.sqrt n * ‖z - z'‖) ^ α := Real.rpow_le_rpow hηnneg hηδ hα.le
              _ = (Real.sqrt n) ^ α * ‖z - z'‖ ^ α :=
                  Real.mul_rpow (Real.sqrt_nonneg n) (norm_nonneg _)
          have h2ηα : (2 * η) ^ α ≤ (2 * Real.sqrt n) ^ α * ‖z - z'‖ ^ α := by
            have h2 : 2 * η ≤ 2 * (Real.sqrt n * ‖z - z'‖) := by linarith [hηδ]
            calc (2 * η) ^ α ≤ (2 * (Real.sqrt n * ‖z - z'‖)) ^ α :=
                  Real.rpow_le_rpow (by linarith) h2 hα.le
              _ = (2 * Real.sqrt n) ^ α * ‖z - z'‖ ^ α := by
                  rw [show 2 * (Real.sqrt n * ‖z - z'‖) = (2 * Real.sqrt n) * ‖z - z'‖ from by ring]
                  exact Real.mul_rpow (by linarith) (norm_nonneg _)
          set S1 : Set (Fin n → ℂ) := eucBall (2 * η) ∩ eucBall (4 * R) with hS1
          set S2 : Set (Fin n → ℂ) := eucShell (2 * η) (4 * R) with hS2
          have hS1m : MeasurableSet S1 := by
            rw [hS1]; exact (measurableSet_eucBall _).inter (measurableSet_eucBall _)
          have hS2m : MeasurableSet S2 := by rw [hS2]; exact measurableSet_eucShell _ _
          have hS1sub : S1 ⊆ eucBall (n := n) (2 * η) := by rw [hS1]; exact inter_subset_left
          have hS1subB : S1 ⊆ eucBall (n := n) (4 * R) := by rw [hS1]; exact inter_subset_right
          have hS2subB : S2 ⊆ eucBall (n := n) (4 * R) := by
            rw [hS2]; intro x hx; exact hx.2
          have hdisj : Disjoint S1 S2 := by
            rw [Set.disjoint_left]
            intro x hx hx'
            rw [hS1] at hx; rw [hS2] at hx'
            simp only [mem_eucBall, mem_eucShell, Set.mem_inter_iff] at hx hx'
            linarith [hx.1, hx'.1]
          have hunion : S1 ∪ S2 = eucBall (4 * R) := by
            rw [hS1, hS2]
            ext x
            simp only [mem_eucBall, mem_eucShell, Set.mem_union, Set.mem_inter_iff]
            constructor
            · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
            · intro hx
              rcases lt_or_ge (eucNorm x) (2 * η) with hlt | hge
              · exact Or.inl ⟨hlt, hx⟩
              · exact Or.inr ⟨hge, hx⟩
          have hIntBall : ∀ w : Fin n → ℂ,
              IntegrableOn (fun x : Fin n → ℂ => Φ x * (g (w + x) - g w))
                (eucBall (n := n) (4 * R)) volume := by
            intro w
            exact integrableOn_of_le_eucNorm_rpow_ball hn (s := α - 2 * (n : ℝ)) (by linarith)
              (hmeas_of w) (C := A * K) (by positivity)
              (fun x _ => norm_Phi_mul_le hα hα1 hA hK hP1 hg w x)
          have hIntS1 : ∀ w : Fin n → ℂ,
              IntegrableOn (fun x : Fin n → ℂ => Φ x * (g (w + x) - g w)) S1 volume :=
            fun w => (hIntBall w).mono_set hS1subB
          have hIntS2 : ∀ w : Fin n → ℂ,
              IntegrableOn (fun x : Fin n → ℂ => Φ x * (g (w + x) - g w)) S2 volume :=
            fun w => (hIntBall w).mono_set hS2subB
          have hsplit_z : ∫ x in eucBall (4 * R), Φ x * (g (z + x) - g z)
              = (∫ x in S1, Φ x * (g (z + x) - g z))
                + (∫ x in S2, Φ x * (g (z + x) - g z)) := by
            rw [← hunion]
            exact MeasureTheory.setIntegral_union hdisj hS2m (hIntS1 z) (hIntS2 z)
          have hsplit_z' : ∫ x in eucBall (4 * R), Φ x * (g (z' + x) - g z')
              = (∫ x in S1, Φ x * (g (z' + x) - g z'))
                + (∫ x in S2, Φ x * (g (z' + x) - g z')) := by
            rw [← hunion]
            exact MeasureTheory.setIntegral_union hdisj hS2m (hIntS1 z') (hIntS2 z')
          have hmain : (∫ x in eucBall (4 * R), Φ x * (g (z + x) - g z))
                - (∫ x in eucBall (4 * R), Φ x * (g (z' + x) - g z'))
              = ((∫ x in S1, Φ x * (g (z + x) - g z))
                  - (∫ x in S1, Φ x * (g (z' + x) - g z')))
                + ((∫ x in S2, Φ x * (g (z + x) - g z))
                  - (∫ x in S2, Φ x * (g (z' + x) - g z'))) := by
            rw [hsplit_z, hsplit_z']; ring
          -- ---- S1 estimate ----
          have hS1e : ∫ x in S1, eucNorm x ^ (α - 2 * (n : ℝ)) ≤ Crad * (2 * η) ^ α := by
            have h4 := hCrad (2 * η) (by linarith)
            rw [show α - 2 * (n : ℝ) + 2 * (n : ℝ) = α from by ring] at h4
            refine le_trans (MeasureTheory.setIntegral_mono_set ?_ ?_ ?_) h4
            · exact integrableOn_eucNorm_rpow_ball hn (by linarith) (2 * η)
            · filter_upwards with x using Real.rpow_nonneg (eucNorm_nonneg x) _
            · filter_upwards with x hx using hS1sub hx
          have hS1bound : ‖(∫ x in S1, Φ x * (g (z + x) - g z))
                - (∫ x in S1, Φ x * (g (z' + x) - g z'))‖
              ≤ 2 * A * Crad * (2 * η) ^ α * K := by
            have hA1 : ‖∫ x in S1, Φ x * (g (z + x) - g z)‖ ≤ A * Crad * (2 * η) ^ α * K := by
              have hmaj1 : IntegrableOn (fun x : Fin n → ℂ => A * K * eucNorm x ^ (α - 2 * (n : ℝ)))
                  S1 volume :=
                MeasureTheory.IntegrableOn.mono_set
                  (MeasureTheory.Integrable.const_mul
                    (integrableOn_eucNorm_rpow_ball hn (by linarith) (2 * η)) (A * K)) hS1sub
              have hb := norm_setIntegral_le_of_norm_le' hS1m hmaj1
                (fun x _ => norm_Phi_mul_le hα hα1 hA hK hP1 hg z x)
              refine le_trans hb ?_
              rw [MeasureTheory.integral_const_mul]
              calc A * K * ∫ x in S1, eucNorm x ^ (α - 2 * (n : ℝ))
                  ≤ A * K * (Crad * (2 * η) ^ α) := mul_le_mul_of_nonneg_left hS1e (by positivity)
                _ = A * Crad * (2 * η) ^ α * K := by ring
            have hA2 : ‖∫ x in S1, Φ x * (g (z' + x) - g z')‖ ≤ A * Crad * (2 * η) ^ α * K := by
              have hmaj1 : IntegrableOn (fun x : Fin n → ℂ => A * K * eucNorm x ^ (α - 2 * (n : ℝ)))
                  S1 volume :=
                MeasureTheory.IntegrableOn.mono_set
                  (MeasureTheory.Integrable.const_mul
                    (integrableOn_eucNorm_rpow_ball hn (by linarith) (2 * η)) (A * K)) hS1sub
              have hb := norm_setIntegral_le_of_norm_le' hS1m hmaj1
                (fun x _ => norm_Phi_mul_le hα hα1 hA hK hP1 hg z' x)
              refine le_trans hb ?_
              rw [MeasureTheory.integral_const_mul]
              calc A * K * ∫ x in S1, eucNorm x ^ (α - 2 * (n : ℝ))
                  ≤ A * K * (Crad * (2 * η) ^ α) := mul_le_mul_of_nonneg_left hS1e (by positivity)
                _ = A * Crad * (2 * η) ^ α * K := by ring
            calc ‖(∫ x in S1, Φ x * (g (z + x) - g z))
                  - (∫ x in S1, Φ x * (g (z' + x) - g z'))‖
                ≤ ‖∫ x in S1, Φ x * (g (z + x) - g z)‖
                  + ‖∫ x in S1, Φ x * (g (z' + x) - g z')‖ := norm_sub_le _ _
              _ ≤ 2 * A * Crad * (2 * η) ^ α * K := by
                  rw [show 2 * A * Crad * (2 * η) ^ α * K
                      = A * Crad * (2 * η) ^ α * K + A * Crad * (2 * η) ^ α * K from by ring]
                  exact add_le_add hA1 hA2
          -- ---- S2 estimate ----
          have hS2bound : ‖(∫ x in S2, Φ x * (g (z + x) - g z))
                - (∫ x in S2, Φ x * (g (z' + x) - g z'))‖
              ≤ (Cfr + Ccr) * A * K * η ^ α := by
            by_cases h2ηlt : 2 * η < 4 * R
            · have hPhiZero : ∫ x in S2, Φ x = 0 := hH2 (2 * η) (4 * R) (by linarith) h2ηlt
              have hIntPhi2 : IntegrableOn Φ S2 volume := by
                refine integrableOn_of_norm_le_const_aux (F := Φ) hS2m
                  (volume_lt_top_of_subset_eucNorm (M := 4 * R)
                    (fun x hx => le_of_lt hx.2))
                  (hΦm.mono_measure Measure.restrict_le_self) (M := A / (2 * η) ^ (2 * n)) ?_
                intro x hx
                rw [mem_eucShell] at hx
                have hxne : x ≠ 0 := by
                  intro h0; rw [h0, eucNorm_zero] at hx; linarith [hx.1]
                refine le_trans (hP1 x hxne) ?_
                exact div_le_div_of_nonneg_left hA.le (pow_pos (by linarith) _)
                  (pow_le_pow_left₀ (by linarith) hx.1 _)
              have hIntPhi_const : IntegrableOn (fun x : Fin n → ℂ => Φ x * (g z - g z'))
                  S2 volume :=
                (hIntPhi2.const_mul (g z - g z')).congr
                  (Filter.Eventually.of_forall (fun x => by ring))
              have hIntPhi_z' : IntegrableOn (fun x : Fin n → ℂ => Φ x * (g (z + x) - g z'))
                  S2 volume := by
                refine ((hIntS2 z).add hIntPhi_const).congr
                  (Filter.Eventually.of_forall (fun x => ?_))
                simp only [Pi.add_apply]
                ring
              have hstep1 : ∫ x in S2, Φ x * (g (z + x) - g z)
                  = ∫ x in S2, Φ x * (g (z + x) - g z') := by
                have hpt : ∀ x : Fin n → ℂ,
                    Φ x * (g (z + x) - g z) = Φ x * (g (z + x) - g z') + Φ x * (g z' - g z) := by
                  intro x; ring
                rw [setIntegral_congr_fun hS2m (fun x _ => hpt x),
                  MeasureTheory.integral_add (hIntPhi_z' ) ((hIntPhi2.const_mul (g z' - g z)).congr
                    (Filter.Eventually.of_forall (fun x => by ring)))]
                have hzero : ∫ x in S2, Φ x * (g z' - g z) = 0 := by
                  rw [show (fun x : Fin n → ℂ => Φ x * (g z' - g z))
                        = (fun x => (g z' - g z) * Φ x) from by funext x; ring]
                  rw [MeasureTheory.integral_const_mul, hPhiZero, mul_zero]
                rw [hzero, add_zero]
              set F : (Fin n → ℂ) → ℂ := fun u => Φ (u - h) * (g (z + u) - g z') with hF
              set S2T : Set (Fin n → ℂ) := (fun u : Fin n → ℂ => u + h) '' S2 with hS2T
              have hS2Teq : S2T = {u : Fin n → ℂ | 2 * η ≤ eucNorm (u - h)
                  ∧ eucNorm (u - h) < 4 * R} := by
                rw [hS2T, hS2]
                ext u
                simp only [Set.mem_image, mem_eucShell, Set.mem_setOf_eq]
                constructor
                · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
                  simpa using ⟨h1, h2⟩
                · intro hu
                  exact ⟨u - h, ⟨hu.1, hu.2⟩, by ring⟩
              set cmax : ℝ := max ((3/2 : ℝ) ^ (α - 2 * (n : ℝ)))
                  ((1/2 : ℝ) ^ (α - 2 * (n : ℝ))) with hcmax
              have hF_pt : ∀ u : Fin n → ℂ,
                  ‖F u‖ ≤ (A * K) * eucNorm (u - h) ^ (α - 2 * (n : ℝ)) := by
                intro u
                rw [hF]
                have hh2 := norm_Phi_mul_le hα hα1 hA hK hP1 hg z' (u - h)
                simpa [show z' + (u - h) = z + u from by rw [← hz']; abel] using hh2
              have hF_pt' : ∀ u : Fin n → ℂ, u ∈ S2 →
                  ‖F u‖ ≤ (A * K) * cmax * eucNorm u ^ (α - 2 * (n : ℝ)) := by
                intro u hu
                rw [mem_eucShell] at hu
                have hupos : 0 < eucNorm u := by linarith [hu.1, hηpos]
                have h3 : eucNorm (u - h) ≤ (3/2) * eucNorm u := by
                  calc eucNorm (u - h) ≤ eucNorm u + eucNorm h := eucNorm_sub_le u h
                    _ = eucNorm u + η := by rw [hη]
                    _ ≤ (3/2) * eucNorm u := by linarith [hu.1]
                have h4 : (1/2 : ℝ) * eucNorm u ≤ eucNorm (u - h) := by
                  have h5 : eucNorm u ≤ eucNorm (u - h) + eucNorm h := by
                    have h6 := eucNorm_add_le (u - h) h
                    simpa using h6
                  have h7 : eucNorm h ≤ (1/2 : ℝ) * eucNorm u := by
                    rw [← hη]; linarith [hu.1]
                  linarith
                have h6 : eucNorm (u - h) ^ (α - 2 * (n : ℝ))
                    ≤ cmax * eucNorm u ^ (α - 2 * (n : ℝ)) := by
                  rcases le_or_gt (α - 2 * (n : ℝ)) 0 with ht | ht
                  · calc eucNorm (u - h) ^ (α - 2 * (n : ℝ))
                        ≤ ((1/2 : ℝ) * eucNorm u) ^ (α - 2 * (n : ℝ)) :=
                          Real.rpow_le_rpow_of_nonpos (by positivity) h4 ht
                      _ = (1/2 : ℝ) ^ (α - 2 * (n : ℝ)) * eucNorm u ^ (α - 2 * (n : ℝ)) :=
                          Real.mul_rpow (by norm_num) (eucNorm_nonneg u)
                      _ ≤ cmax * eucNorm u ^ (α - 2 * (n : ℝ)) := by
                          rw [hcmax]
                          exact mul_le_mul_of_nonneg_right (le_max_right _ _)
                            (Real.rpow_nonneg (eucNorm_nonneg u) _)
                  · calc eucNorm (u - h) ^ (α - 2 * (n : ℝ))
                        ≤ ((3/2 : ℝ) * eucNorm u) ^ (α - 2 * (n : ℝ)) :=
                          Real.rpow_le_rpow (eucNorm_nonneg (u - h)) h3 ht.le
                      _ = (3/2 : ℝ) ^ (α - 2 * (n : ℝ)) * eucNorm u ^ (α - 2 * (n : ℝ)) :=
                          Real.mul_rpow (by norm_num) (eucNorm_nonneg u)
                      _ ≤ cmax * eucNorm u ^ (α - 2 * (n : ℝ)) := by
                          rw [hcmax]
                          exact mul_le_mul_of_nonneg_right (le_max_left _ _)
                            (Real.rpow_nonneg (eucNorm_nonneg u) _)
                calc ‖F u‖ ≤ (A * K) * eucNorm (u - h) ^ (α - 2 * (n : ℝ)) := hF_pt u
                  _ ≤ (A * K) * (cmax * eucNorm u ^ (α - 2 * (n : ℝ))) :=
                      mul_le_mul_of_nonneg_left h6 (by positivity)
                  _ = (A * K) * cmax * eucNorm u ^ (α - 2 * (n : ℝ)) := by ring
              have hFmeas : AEStronglyMeasurable (F) volume := by
                rw [hF]
                exact (aestronglyMeasurable_comp_sub hΦm h).mul
                  (((hgcont.comp (continuous_const.add continuous_id)).sub
                    continuous_const).aestronglyMeasurable)
              have hIntF2 : IntegrableOn F S2 volume := by
                refine integrableOn_of_le_eucNorm_rpow_shell (s := α - 2 * (n : ℝ))
                  (a := 2 * η) (b := 4 * R) (by linarith : 0 < 2 * η) (le_of_lt h2ηlt)
                  (P := F) ?_ (C := A * K * cmax) (by positivity) hF_pt'
                exact hFmeas.mono_measure Measure.restrict_le_self
              have htrans : ∫ x in S2, Φ x * (g (z' + x) - g z') = ∫ u in S2T, F u := by
                have hfun : (fun x : Fin n → ℂ => Φ x * (g (z' + x) - g z'))
                    = fun x => F (x + h) := by
                  funext x
                  simp only [hF]
                  rw [add_sub_cancel_right, show z + (x + h) = z' + x from by rw [← hz']; abel]
                rw [hfun, hS2T]
                exact setIntegral_translate_euc h F S2
              have hcres2 : ‖(∫ u in S2, F u) - (∫ u in S2T, F u)‖ ≤ Ccr * (A * K) * η ^ α := by
                have hc := hCcr (B := A * K) (η := η) (b := 4 * R) (by positivity) hηpos
                  (le_of_lt h2ηlt) hη hFmeas hF_pt
                rwa [← hS2, ← hS2Teq] at hc
              have hfar2 : ‖∫ x in S2, (Φ x - Φ (x - h)) * (g (z + x) - g z')‖
                  ≤ Cfr * A * K * η ^ α := by
                have hf := hCfr (Φ := Φ) (h := h) (z := z) (K := K) (η := η) hK hηpos hη hP2 hg
                rw [← hS2] at hf
                rw [← hz']
                exact hf
              have hmid : (∫ u in S2, Φ u * (g (z + u) - g z')) - (∫ x in S2, F x)
                  = ∫ x in S2, (Φ x - Φ (x - h)) * (g (z + x) - g z') := by
                rw [← MeasureTheory.integral_sub hIntPhi_z' hIntF2]
                refine setIntegral_congr_fun hS2m (fun x _ => ?_)
                simp only [hF]; ring
              have hS2eq : (∫ x in S2, Φ x * (g (z + x) - g z))
                    - (∫ x in S2, Φ x * (g (z' + x) - g z'))
                  = (∫ x in S2, (Φ x - Φ (x - h)) * (g (z + x) - g z'))
                    + ((∫ x in S2, F x) - (∫ x in S2T, F x)) := by
                rw [hstep1, htrans, ← hmid]
                ring
              calc ‖(∫ x in S2, Φ x * (g (z + x) - g z))
                    - (∫ x in S2, Φ x * (g (z' + x) - g z'))‖
                  = ‖(∫ x in S2, (Φ x - Φ (x - h)) * (g (z + x) - g z'))
                      + ((∫ x in S2, F x) - (∫ u in S2T, F u))‖ := by rw [hS2eq]
                _ ≤ ‖∫ x in S2, (Φ x - Φ (x - h)) * (g (z + x) - g z')‖
                    + ‖(∫ x in S2, F x) - (∫ u in S2T, F u)‖ := norm_add_le _ _
                _ ≤ Cfr * A * K * η ^ α + Ccr * (A * K) * η ^ α := add_le_add hfar2 hcres2
                _ = (Cfr + Ccr) * A * K * η ^ α := by ring
            · push_neg at h2ηlt
              have hempty : S2 = ∅ := by
                rw [hS2]
                ext x
                simp only [mem_eucShell, Set.mem_empty_iff_false, iff_false, not_and]
                intro h h4R
                linarith
              rw [hempty, MeasureTheory.setIntegral_empty, MeasureTheory.setIntegral_empty,
                sub_self, norm_zero]
              positivity
          -- ---- combination ----
          have hterm1 : 2 * A * Crad * (2 * η) ^ α * K
              ≤ 2 * A * Crad * (2 * Real.sqrt n) ^ α * K * ‖z - z'‖ ^ α := by
            rw [show 2 * A * Crad * (2 * η) ^ α * K = (2 * A * Crad * K) * (2 * η) ^ α
              from by ring]
            rw [show 2 * A * Crad * (2 * Real.sqrt n) ^ α * K * ‖z - z'‖ ^ α
                = (2 * A * Crad * K) * ((2 * Real.sqrt n) ^ α * ‖z - z'‖ ^ α) from by ring]
            exact mul_le_mul_of_nonneg_left h2ηα (by positivity)
          have hterm2 : (Cfr + Ccr) * A * K * η ^ α
              ≤ (Cfr * A * (Real.sqrt n) ^ α + Ccr * A * (Real.sqrt n) ^ α) * K * ‖z - z'‖ ^ α := by
            rw [show (Cfr + Ccr) * A * K * η ^ α = ((Cfr + Ccr) * A * K) * η ^ α from by ring]
            rw [show (Cfr * A * (Real.sqrt n) ^ α + Ccr * A * (Real.sqrt n) ^ α) * K * ‖z - z'‖ ^ α
                = ((Cfr + Ccr) * A * K) * ((Real.sqrt n) ^ α * ‖z - z'‖ ^ α) from by ring]
            exact mul_le_mul_of_nonneg_left hηα (by positivity)
          calc ‖(∫ x in eucBall (4 * R), Φ x * (g (z + x) - g z))
                - (∫ x in eucBall (4 * R), Φ x * (g (z' + x) - g z'))‖
              ≤ ‖(∫ x in S1, Φ x * (g (z + x) - g z))
                  - (∫ x in S1, Φ x * (g (z' + x) - g z'))‖
                + ‖(∫ x in S2, Φ x * (g (z + x) - g z))
                  - (∫ x in S2, Φ x * (g (z' + x) - g z'))‖ := by
                  rw [hmain]; exact norm_add_le _ _
            _ ≤ 2 * A * Crad * (2 * η) ^ α * K + (Cfr + Ccr) * A * K * η ^ α :=
                add_le_add hS1bound hS2bound
            _ ≤ CB * K * ‖z - z'‖ ^ α := by
                rw [hCB]
                linarith [hterm1, hterm2]
            _ ≤ max (max CA CB) (2 * CA) * K * ‖z - z'‖ ^ α := by
                rw [show CB * K * ‖z - z'‖ ^ α = (CB * K) * ‖z - z'‖ ^ α from by ring]
                rw [show max (max CA CB) (2 * CA) * K * ‖z - z'‖ ^ α
                    = (max (max CA CB) (2 * CA) * K) * ‖z - z'‖ ^ α from by ring]
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right
                    (le_trans (le_max_right _ _) (le_max_left _ _)) hK)
                  (Real.rpow_nonneg (norm_nonneg _) α)
