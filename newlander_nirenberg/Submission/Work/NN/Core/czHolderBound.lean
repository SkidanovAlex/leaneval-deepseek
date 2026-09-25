import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCz.czFarKernelDiff
import Submission.Work.CR.Flat.Cauchy.bmCz.czCrescent
import Submission.Work.NN.Core.czHolderDefs

set_option autoImplicit false

noncomputable section

namespace Work.NN.Core

open MeasureTheory Set
open scoped NNReal ENNReal
open Work.CR.Flat.Cauchy

variable {n : ℕ}

/-- A globally `α`-Hölder function with `0 < α` is continuous. -/
lemma continuous_of_holder_bound {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    {g : (Fin n → ℂ) → ℂ} (hg : ∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) :
    Continuous g := by
  have hH : HolderWith (Real.toNNReal K) (Real.toNNReal α) g := by
    intro x y
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
    refine le_trans (ENNReal.ofReal_le_ofReal (hg x y)) ?_
    rw [ENNReal.ofReal_mul hK, ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hα.le]
    rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal K hK, Real.coe_toNNReal α hα.le]
  exact hH.continuous (by rw [Real.toNNReal_pos]; exact hα)

theorem czHolderBound {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {R : ℝ} (hR : 0 < R)
    {Φ : (Fin n → ℂ) → ℂ} (hΦm : AEStronglyMeasurable Φ volume)
    {A : ℝ} (hA : 0 < A)
    (hP1 : ∀ x : Fin n → ℂ, x ≠ 0 → ‖Φ x‖ ≤ A / (eucNorm x) ^ (2 * n))
    (hP2 : ∀ x h : Fin n → ℂ, 2 * eucNorm h ≤ eucNorm x →
      ‖Φ (x - h) - Φ x‖ ≤ A * eucNorm h / (eucNorm x) ^ (2 * n + 1))
    (hH2 : ∀ a b : ℝ, 0 < a → a < b → ∫ x in eucShell a b, Φ x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ), 0 ≤ K → ∀ g : (Fin n → ℂ) → ℂ,
      (∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) →
      (∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0) →
      (∀ z : Fin n → ℂ,
        ‖∫ x in eucBall (4 * R), Φ x * (g (z + x) - g z)‖ ≤ C * K) ∧
      (∀ z z' : Fin n → ℂ,
        ‖(∫ x in eucBall (4 * R), Φ x * (g (z + x) - g z))
            - (∫ x in eucBall (4 * R), Φ x * (g (z' + x) - g z'))‖
          ≤ C * K * ‖z - z'‖ ^ α) := by
  -- the fleet's building blocks
  obtain ⟨Crad, hCradpos, hCrad⟩ :=
    Work.CR.Flat.Cauchy.bmCz.eucRadialBound hn (α - 2 * (n : ℝ)) (by linarith)
  obtain ⟨Cfr, hCfrpos, hCfr⟩ :=
    Work.CR.Flat.Cauchy.bmCz.czFarKernelDiff hn hα hα1 hA hR
  obtain ⟨Ccr, hCcrpos, hCcr⟩ := Work.CR.Flat.Cauchy.bmCz.czCrescent hn hα hα1
  have hαnn : (0 : ℝ) ≤ α := le_of_lt hα
  have h4R : 0 < 4 * R := by linarith
  -- the final constants
  set CA : ℝ := A * Crad * (4 * R) ^ α with hCA
  set CB : ℝ := 2 * A * Crad * (2 * Real.sqrt n) ^ α + (Cfr + Ccr) * A * (Real.sqrt n) ^ α
    with hCB
  have hCApos : 0 < CA := by
    rw [hCA]; exact mul_pos (mul_pos hA hCradpos) (Real.rpow_pos_of_pos h4R α)
  have hCBnn : 0 ≤ CB := by rw [hCB]; positivity
  refine ⟨max CA CB, lt_of_lt_of_le hCApos (le_max_left _ _), ?_⟩
  intro K hK g hg hsupp
  have hgcont : Continuous g := continuous_of_holder_bound hα hK hg
  -- ===== the size bound =====
  have hA_int : ∀ z : Fin n → ℂ, IntegrableOn (fun x : Fin n → ℂ => Φ x * (g (z + x) - g z))
      (eucBall (4 * R)) volume := by
    intro z
    refine Work.CR.Flat.Cauchy.integrableOn_of_le_eucNorm_rpow_ball (s := α - 2 * (n : ℝ))
      (ρ := 4 * R) hn (by linarith) (P := fun x : Fin n → ℂ => Φ x * (g (z + x) - g z))
      ?_ (C := A * K) (mul_nonneg hA.le hK) ?_
    · exact (hΦm.mul (((hgcont.comp (continuous_const.add continuous_id)).sub
        continuous_const).aestronglyMeasurable)).mono_measure
        (Measure.restrict_le_self : volume.restrict (eucBall (4 * R)) ≤ volume)
    · intro x _
      exact Work.CR.Flat.Cauchy.norm_Phi_mul_le hα hα1 hA hK hP1 hg z x
  have hbound1 : ∀ z : Fin n → ℂ,
      ‖∫ x in eucBall (4 * R), Φ x * (g (z + x) - g z)‖ ≤ CA * K := by
    intro z
    have hmaj : IntegrableOn (fun x : Fin n → ℂ => A * K * eucNorm x ^ (α - 2 * (n : ℝ)))
        (eucBall (4 * R)) volume :=
      (Work.CR.Flat.Cauchy.integrableOn_eucNorm_rpow_ball (n := n) (s := α - 2 * (n : ℝ))
        hn (by linarith) (4 * R)).const_mul (A * K)
    have hstep : ‖∫ x in eucBall (4 * R), Φ x * (g (z + x) - g z)‖
        ≤ ∫ x : Fin n → ℂ in eucBall (4 * R), A * K * eucNorm x ^ (α - 2 * (n : ℝ)) :=
      Work.CR.Flat.Cauchy.norm_setIntegral_le_of_norm_le' (measurableSet_eucBall (n := n) (4 * R))
        hmaj (fun x _ => Work.CR.Flat.Cauchy.norm_Phi_mul_le hα hα1 hA hK hP1 hg z x)
    calc ‖∫ x in eucBall (4 * R), Φ x * (g (z + x) - g z)‖
        ≤ ∫ x : Fin n → ℂ in eucBall (4 * R), A * K * eucNorm x ^ (α - 2 * (n : ℝ)) := hstep
      _ = A * K * ∫ x in eucBall (4 * R), eucNorm x ^ (α - 2 * (n : ℝ)) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ A * K * (Crad * (4 * R) ^ (α - 2 * (n : ℝ) + 2 * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left (hCrad (4 * R) h4R) (by positivity)
      _ = CA * K := by rw [hCA]; ring
  have hbound1' : ∀ z : Fin n → ℂ,
      ‖∫ x in eucBall (4 * R), Φ x * (g (z + x) - g z)‖ ≤ max CA CB * K :=
    fun z => (hbound1 z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hK)
  refine ⟨hbound1', ?_⟩
  -- ===== the Hölder bound =====
  intro z z'
  by_cases hzz : z = z'
  · subst hzz
    have hz0 : ‖(∫ x in eucBall (4 * R), Φ x * (g (z + x) - g z))
        - (∫ x in eucBall (4 * R), Φ x * (g (z + x) - g z))‖ = 0 := by
      rw [sub_self, norm_zero]
    rw [hz0]
    exact mul_nonneg (mul_nonneg (le_max_of_le_left hCApos.le) hK)
      (Real.rpow_nonneg (norm_nonneg _) α)
  · set η : ℝ := eucNorm (z - z') with hηdef
    set h : Fin n → ℂ := z' - z with hhdef
    have hηpos : 0 < η := by rw [hηdef]; exact eucNorm_pos (sub_ne_zero.mpr hzz)
    have hηeq : eucNorm h = η := by rw [hhdef, hηdef, eucNorm_sub_comm]
    have hzh : z + h = z' := by rw [hhdef]; abel
    have hηnn : 0 ≤ η := le_of_lt hηpos
    -- the two integrands
    set A1 : (Fin n → ℂ) → ℂ := fun x => Φ x * (g (z + x) - g z) with hA1
    set A2 : (Fin n → ℂ) → ℂ := fun x => Φ x * (g (z' + x) - g z') with hA2
    -- the split sets
    set S1 : Set (Fin n → ℂ) := eucBall (2 * η) ∩ eucBall (4 * R) with hS1
    set S2 : Set (Fin n → ℂ) := eucShell (2 * η) (4 * R) with hS2
    have hS1m : MeasurableSet S1 := by rw [hS1]; exact (measurableSet_eucBall _).inter (measurableSet_eucBall _)
    have hS2m : MeasurableSet S2 := by rw [hS2]; exact measurableSet_eucShell _ _
    have hdisj : Disjoint S1 S2 := by
      rw [Set.disjoint_left, hS1, hS2]
      intro x hx hx'
      rw [Set.mem_inter_iff, mem_eucBall] at hx
      rw [mem_eucShell] at hx'
      linarith [hx.1, hx'.1]
    have hunion : S1 ∪ S2 = eucBall (4 * R) := by
      ext x
      rw [Set.mem_union, hS1, hS2, Set.mem_inter_iff, mem_eucBall, mem_eucShell, mem_eucBall]
      constructor
      · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact h
      · intro hx
        rcases lt_or_ge (eucNorm x) (2 * η) with hlt | hge
        · exact Or.inl ⟨hlt, hx⟩
        · exact Or.inr ⟨hge, hx⟩
    have hS1sub : S1 ⊆ eucBall (2 * η) := by rw [hS1]; exact inter_subset_left
    have hS1subB : S1 ⊆ eucBall (4 * R) := by rw [hS1]; exact inter_subset_right
    have hS2sub : S2 ⊆ eucBall (4 * R) := by
      intro x hx
      rw [hS2, mem_eucShell] at hx
      rw [mem_eucBall]; exact hx.2
    -- integrability of both integrands on the whole ball and on the two pieces
    have hIntA1 : IntegrableOn A1 (eucBall (4 * R)) volume := hA_int z
    have hIntA2 : IntegrableOn A2 (eucBall (4 * R)) volume := hA_int z'
    have hsplitA1 : ∫ x in eucBall (4 * R), A1 x = (∫ x in S1, A1 x) + (∫ x in S2, A1 x) := by
      rw [← hunion]
      exact MeasureTheory.setIntegral_union hdisj hS2m
        (hIntA1.mono_set (by rw [← hunion]; exact Set.subset_union_left))
        (hIntA1.mono_set (by rw [← hunion]; exact Set.subset_union_right))
    have hsplitA2 : ∫ x in eucBall (4 * R), A2 x = (∫ x in S1, A2 x) + (∫ x in S2, A2 x) := by
      rw [← hunion]
      exact MeasureTheory.setIntegral_union hdisj hS2m
        (hIntA2.mono_set (by rw [← hunion]; exact Set.subset_union_left))
        (hIntA2.mono_set (by rw [← hunion]; exact Set.subset_union_right))
    have hrewrite : (∫ x in eucBall (4 * R), A1 x) - (∫ x in eucBall (4 * R), A2 x)
        = ((∫ x in S1, A1 x) - (∫ x in S1, A2 x))
          + ((∫ x in S2, A1 x) - (∫ x in S2, A2 x)) := by
      rw [hsplitA1, hsplitA2]; ring
    -- ===== bound on S1 =====
    have hS1b1 : ‖∫ x in S1, A1 x‖ ≤ A * Crad * (2 * η) ^ α * K := by
      have hmaj : IntegrableOn (fun x : Fin n → ℂ => A * K * eucNorm x ^ (α - 2 * (n : ℝ)))
          (eucBall (2 * η)) volume :=
        (Work.CR.Flat.Cauchy.integrableOn_eucNorm_rpow_ball (n := n) (s := α - 2 * (n : ℝ))
          hn (by linarith) (2 * η)).const_mul (A * K)
      have hIntn : IntegrableOn (fun x : Fin n → ℂ => ‖A1 x‖) S1 volume :=
        (hIntA1.mono_set hS1subB).norm
      have hmajS1 : IntegrableOn (fun x : Fin n → ℂ => A * K * eucNorm x ^ (α - 2 * (n : ℝ)))
          S1 volume := hmaj.mono_set hS1sub
      have hs1 : ‖∫ x in S1, A1 x‖ ≤ ∫ x : Fin n → ℂ in S1, A * K * eucNorm x ^ (α - 2 * (n : ℝ)) :=
        (norm_integral_le_integral_norm _).trans
          (MeasureTheory.setIntegral_mono_on hIntn hmajS1 hS1m (fun x _ =>
            Work.CR.Flat.Cauchy.norm_Phi_mul_le hα hα1 hA hK hP1 hg z x))
      have hs2 : ∫ x : Fin n → ℂ in S1, A * K * eucNorm x ^ (α - 2 * (n : ℝ))
          ≤ ∫ x : Fin n → ℂ in eucBall (2 * η), A * K * eucNorm x ^ (α - 2 * (n : ℝ)) :=
        MeasureTheory.setIntegral_mono_set hmaj
          (Filter.Eventually.of_forall (fun x =>
            mul_nonneg (mul_nonneg hA.le hK) (Real.rpow_nonneg (eucNorm_nonneg x) _)))
          (Filter.Eventually.of_forall (fun x hx => hS1sub hx))
      have hs3 : ∫ x : Fin n → ℂ in eucBall (2 * η), A * K * eucNorm x ^ (α - 2 * (n : ℝ))
          = A * K * ∫ x : Fin n → ℂ in eucBall (2 * η), eucNorm x ^ (α - 2 * (n : ℝ)) := by
        rw [MeasureTheory.integral_const_mul]
      have hs4 : ∫ x : Fin n → ℂ in eucBall (2 * η), eucNorm x ^ (α - 2 * (n : ℝ))
          ≤ Crad * (2 * η) ^ (α - 2 * (n : ℝ) + 2 * (n : ℝ)) := hCrad (2 * η) (by linarith)
      calc ‖∫ x in S1, A1 x‖ ≤ ∫ x : Fin n → ℂ in S1, A * K * eucNorm x ^ (α - 2 * (n : ℝ)) := hs1
        _ ≤ ∫ x : Fin n → ℂ in eucBall (2 * η), A * K * eucNorm x ^ (α - 2 * (n : ℝ)) := hs2
        _ = A * K * ∫ x : Fin n → ℂ in eucBall (2 * η), eucNorm x ^ (α - 2 * (n : ℝ)) := hs3
        _ ≤ A * K * (Crad * (2 * η) ^ (α - 2 * (n : ℝ) + 2 * (n : ℝ))) :=
            mul_le_mul_of_nonneg_left hs4 (by positivity)
        _ = A * Crad * (2 * η) ^ α * K := by ring
    have hS1b2 : ‖∫ x in S1, A2 x‖ ≤ A * Crad * (2 * η) ^ α * K := by
      have hmaj : IntegrableOn (fun x : Fin n → ℂ => A * K * eucNorm x ^ (α - 2 * (n : ℝ)))
          (eucBall (2 * η)) volume :=
        (Work.CR.Flat.Cauchy.integrableOn_eucNorm_rpow_ball (n := n) (s := α - 2 * (n : ℝ))
          hn (by linarith) (2 * η)).const_mul (A * K)
      have hIntn : IntegrableOn (fun x : Fin n → ℂ => ‖A2 x‖) S1 volume :=
        (hIntA2.mono_set hS1subB).norm
      have hmajS1 : IntegrableOn (fun x : Fin n → ℂ => A * K * eucNorm x ^ (α - 2 * (n : ℝ)))
          S1 volume := hmaj.mono_set hS1sub
      have hs1 : ‖∫ x in S1, A2 x‖ ≤ ∫ x : Fin n → ℂ in S1, A * K * eucNorm x ^ (α - 2 * (n : ℝ)) :=
        (norm_integral_le_integral_norm _).trans
          (MeasureTheory.setIntegral_mono_on hIntn hmajS1 hS1m (fun x _ =>
            Work.CR.Flat.Cauchy.norm_Phi_mul_le hα hα1 hA hK hP1 hg z' x))
      have hs2 : ∫ x : Fin n → ℂ in S1, A * K * eucNorm x ^ (α - 2 * (n : ℝ))
          ≤ ∫ x : Fin n → ℂ in eucBall (2 * η), A * K * eucNorm x ^ (α - 2 * (n : ℝ)) :=
        MeasureTheory.setIntegral_mono_set hmaj
          (Filter.Eventually.of_forall (fun x =>
            mul_nonneg (mul_nonneg hA.le hK) (Real.rpow_nonneg (eucNorm_nonneg x) _)))
          (Filter.Eventually.of_forall (fun x hx => hS1sub hx))
      have hs3 : ∫ x : Fin n → ℂ in eucBall (2 * η), A * K * eucNorm x ^ (α - 2 * (n : ℝ))
          = A * K * ∫ x : Fin n → ℂ in eucBall (2 * η), eucNorm x ^ (α - 2 * (n : ℝ)) := by
        rw [MeasureTheory.integral_const_mul]
      have hs4 : ∫ x : Fin n → ℂ in eucBall (2 * η), eucNorm x ^ (α - 2 * (n : ℝ))
          ≤ Crad * (2 * η) ^ (α - 2 * (n : ℝ) + 2 * (n : ℝ)) := hCrad (2 * η) (by linarith)
      calc ‖∫ x in S1, A2 x‖ ≤ ∫ x : Fin n → ℂ in S1, A * K * eucNorm x ^ (α - 2 * (n : ℝ)) := hs1
        _ ≤ ∫ x : Fin n → ℂ in eucBall (2 * η), A * K * eucNorm x ^ (α - 2 * (n : ℝ)) := hs2
        _ = A * K * ∫ x : Fin n → ℂ in eucBall (2 * η), eucNorm x ^ (α - 2 * (n : ℝ)) := hs3
        _ ≤ A * K * (Crad * (2 * η) ^ (α - 2 * (n : ℝ) + 2 * (n : ℝ))) :=
            mul_le_mul_of_nonneg_left hs4 (by positivity)
        _ = A * Crad * (2 * η) ^ α * K := by ring
    have hS1bound : ‖(∫ x in S1, A1 x) - (∫ x in S1, A2 x)‖ ≤ 2 * A * Crad * (2 * η) ^ α * K := by
      calc ‖(∫ x in S1, A1 x) - (∫ x in S1, A2 x)‖
          ≤ ‖∫ x in S1, A1 x‖ + ‖∫ x in S1, A2 x‖ := norm_sub_le _ _
        _ ≤ A * Crad * (2 * η) ^ α * K + A * Crad * (2 * η) ^ α * K := add_le_add hS1b1 hS1b2
        _ = 2 * A * Crad * (2 * η) ^ α * K := by ring
    -- ===== bound on S2 =====
    have hS2bound : ‖(∫ x in S2, A1 x) - (∫ x in S2, A2 x)‖ ≤ (Cfr + Ccr) * A * K * η ^ α := by
      rcases lt_or_ge (2 * η) (4 * R) with h2ηlt | h2ηge
      · -- the substantive case
        have h2ηle : 2 * η ≤ 4 * R := le_of_lt h2ηlt
        have h2ηpos : 0 < 2 * η := by linarith
        -- drop the constant `g z` using the vanishing mean on the shell
        have hPhiZero : ∫ x in S2, Φ x = 0 := by
          rw [hS2]
          exact hH2 (2 * η) (4 * R) h2ηpos h2ηlt
        have hIntPhi : IntegrableOn Φ S2 volume := by
          refine Work.CR.Flat.Cauchy.integrableOn_of_norm_le_const_aux
            (E := ℂ) (F := Φ) hS2m ?_ ?_ (M := A / (2 * η) ^ (2 * n)) ?_
          · exact Work.CR.Flat.Cauchy.volume_lt_top_of_subset_eucNorm
              (fun x hx => le_of_lt (hS2sub hx))
          · exact hΦm.mono_measure Measure.restrict_le_self
          · intro x hx
            rw [hS2, mem_eucShell] at hx
            have hxne : x ≠ 0 := by
              intro h0
              rw [h0, eucNorm_zero] at hx
              linarith [hx.1, h2ηpos]
            exact le_trans (hP1 x hxne)
              (div_le_div_of_nonneg_left hA.le (by positivity)
                (pow_le_pow_left₀ (by linarith) hx.1 (2 * n)))
        -- the intermediate integrand with the constant `g z'` only
        have hB2pt : ∀ x ∈ S2, ‖Φ x * (g (z + x) - g z')‖
            ≤ A / (2 * η) ^ (2 * n) * (K * (4 * R + η) ^ α) := by
          intro x hx
          rw [hS2, mem_eucShell] at hx
          have hxne : x ≠ 0 := by
            intro h0
            rw [h0, eucNorm_zero] at hx
            linarith [hx.1, h2ηpos]
          rw [norm_mul]
          have h1 : ‖Φ x‖ ≤ A / (2 * η) ^ (2 * n) :=
            le_trans (hP1 x hxne)
              (div_le_div_of_nonneg_left hA.le (pow_pos (by linarith : (0:ℝ) < 2 * η) _)
                (pow_le_pow_left₀ h2ηpos.le hx.1 (2 * n)))
          have h2 : ‖g (z + x) - g z'‖ ≤ K * (4 * R + η) ^ α := by
            have hge := hg (z + x) z'
            rw [show (z + x) - z' = x - h from by rw [hhdef]; abel] at hge
            have hbd : ‖x - h‖ ≤ 4 * R + η := by
              calc ‖x - h‖ ≤ eucNorm (x - h) := pi_norm_le_eucNorm _
                _ ≤ eucNorm x + eucNorm h := Work.CR.Flat.Cauchy.eucNorm_sub_le x h
                _ ≤ 4 * R + η := by rw [hηeq]; linarith [hx.2]
            calc ‖g (z + x) - g z'‖ ≤ K * ‖x - h‖ ^ α := hge
              _ ≤ K * (4 * R + η) ^ α :=
                  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hbd hα.le) hK
          exact mul_le_mul h1 h2 (norm_nonneg _)
            (div_nonneg hA.le (pow_pos (by linarith : (0:ℝ) < 2 * η) _).le)
        have hIntB2 : IntegrableOn (fun x : Fin n → ℂ => Φ x * (g (z + x) - g z')) S2 volume := by
          refine Work.CR.Flat.Cauchy.integrableOn_of_norm_le_const_aux
            (E := ℂ) (F := fun x : Fin n → ℂ => Φ x * (g (z + x) - g z')) hS2m ?_ ?_
            (M := A / (2 * η) ^ (2 * n) * (K * (4 * R + η) ^ α)) ?_
          · exact Work.CR.Flat.Cauchy.volume_lt_top_of_subset_eucNorm
              (fun x hx => le_of_lt (hS2sub hx))
          · exact (hΦm.mul (((hgcont.comp (continuous_const.add continuous_id)).sub
              continuous_const).aestronglyMeasurable)).mono_measure Measure.restrict_le_self
          · intro x hx; exact hB2pt x hx
        have hIntc : IntegrableOn (fun x : Fin n → ℂ => Φ x * (g z' - g z)) S2 volume :=
          (hIntPhi.mul_const (g z' - g z)).congr (Filter.Eventually.of_forall (fun x => by ring))
        have hzero : ∫ x in S2, Φ x * (g z' - g z) = 0 := by
          have h1 : ∫ x in S2, Φ x * (g z' - g z) = ∫ x in S2, (g z' - g z) * Φ x :=
            setIntegral_congr_fun hS2m (fun x _ => by ring)
          rw [h1, MeasureTheory.integral_const_mul, hPhiZero, mul_zero]
        have hcancel1 : ∫ x in S2, A1 x = ∫ x in S2, (fun x : Fin n → ℂ => Φ x * (g (z + x) - g z')) x := by
          have hpt : ∀ x : Fin n → ℂ,
              A1 x = Φ x * (g (z + x) - g z') + Φ x * (g z' - g z) := by
            intro x; rw [hA1]; ring
          rw [setIntegral_congr_fun hS2m (fun x _ => hpt x),
            MeasureTheory.integral_add hIntB2 hIntc, hzero, add_zero]
        -- the shifted function
        set F : (Fin n → ℂ) → ℂ := fun u => Φ (u - h) * (g (z + u) - g z') with hF
        set S2T : Set (Fin n → ℂ) := (fun u : Fin n → ℂ => u + h) '' S2 with hS2T
        have hS2Teq : S2T = {u : Fin n → ℂ | 2 * η ≤ eucNorm (u - h) ∧ eucNorm (u - h) < 4 * R} := by
          rw [hS2T, hS2]
          ext u
          simp only [Set.mem_image, mem_eucShell, Set.mem_ofPred_eq]
          constructor
          · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
            simpa using ⟨h1, h2⟩
          · intro hu
            exact ⟨u - h, ⟨hu.1, hu.2⟩, by ring⟩
        have htrans : ∫ x in S2, A2 x = ∫ u in S2T, F u := by
          have hfun : A2 = fun x : Fin n → ℂ => F (x + h) := by
            funext x
            simp only [hA2, hF]
            have h1 : x + h - h = x := by abel
            have h2 : z + (x + h) = z' + x := by rw [← hzh]; abel
            rw [h1, h2]
          rw [hfun, hS2T]
          exact Work.CR.Flat.Cauchy.setIntegral_translate_euc h F S2
        have hFpt : ∀ u : Fin n → ℂ, ‖F u‖ ≤ A * K * eucNorm (u - h) ^ (α - 2 * (n : ℝ)) := by
          intro u
          have key := Work.CR.Flat.Cauchy.norm_Phi_mul_le hα hα1 hA hK hP1 hg z' (u - h)
          simpa [hF, show z' + (u - h) = z + u from by rw [← hzh]; abel] using key
        have hFmeas : AEStronglyMeasurable F volume := by
          rw [hF]
          exact (Work.CR.Flat.Cauchy.aestronglyMeasurable_comp_sub hΦm h).mul
            (((hgcont.comp (continuous_const.add continuous_id)).sub
              continuous_const).aestronglyMeasurable)
        have hIntF2 : IntegrableOn F S2 volume := by
          refine Work.CR.Flat.Cauchy.integrableOn_of_le_eucNorm_rpow_shell
            (s := α - 2 * (n : ℝ)) (a := 2 * η) (b := 4 * R)
            h2ηpos h2ηle (hFmeas.mono_measure Measure.restrict_le_self)
            (C := A * K * (1 / 2 : ℝ) ^ (α - 2 * (n : ℝ))) (by positivity) ?_
          intro u hu
          rw [mem_eucShell] at hu
          have hupos : 0 < eucNorm u := by linarith [hu.1]
          have h1 : eucNorm u ≤ eucNorm (u - h) + η := by
            have h2 : eucNorm u = eucNorm ((u - h) + h) := by
              congr 1; abel
            calc eucNorm u = eucNorm ((u - h) + h) := h2
              _ ≤ eucNorm (u - h) + eucNorm h := Work.CR.Flat.Cauchy.eucNorm_add_le (u - h) h
              _ = eucNorm (u - h) + η := by rw [hηeq]
          have h2 : (1 / 2 : ℝ) * eucNorm u ≤ eucNorm (u - h) := by
            have : η ≤ (1 / 2 : ℝ) * eucNorm u := by linarith [hu.1]
            linarith
          have hexp : α - 2 * (n : ℝ) ≤ 0 := by
            have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            linarith
          have h3 : eucNorm (u - h) ^ (α - 2 * (n : ℝ))
              ≤ ((1 / 2 : ℝ) * eucNorm u) ^ (α - 2 * (n : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) h2 hexp
          rw [Real.mul_rpow (by norm_num) (eucNorm_nonneg u)] at h3
          calc ‖F u‖ ≤ A * K * eucNorm (u - h) ^ (α - 2 * (n : ℝ)) := hFpt u
            _ ≤ A * K * ((1 / 2 : ℝ) ^ (α - 2 * (n : ℝ))
                  * eucNorm u ^ (α - 2 * (n : ℝ))) :=
                mul_le_mul_of_nonneg_left h3 (by positivity)
            _ = A * K * (1 / 2 : ℝ) ^ (α - 2 * (n : ℝ)) * eucNorm u ^ (α - 2 * (n : ℝ)) := by ring
        have hmid : (∫ x in S2, (fun x : Fin n → ℂ => Φ x * (g (z + x) - g z')) x) - (∫ x in S2, F x)
            = ∫ x in S2, (Φ x - Φ (x - h)) * (g (z + x) - g z') := by
          rw [← MeasureTheory.integral_sub hIntB2 hIntF2]
          refine setIntegral_congr_fun hS2m (fun x _ => ?_)
          simp only [hF]; ring
        have hS2eq : (∫ x in S2, A1 x) - (∫ x in S2, A2 x)
            = (∫ x in S2, (Φ x - Φ (x - h)) * (g (z + x) - g z'))
              + ((∫ x in S2, F x) - (∫ u in S2T, F u)) := by
          rw [hcancel1, htrans, ← hmid]
          ring
        have hfar : ‖∫ x in S2, (Φ x - Φ (x - h)) * (g (z + x) - g z')‖
            ≤ Cfr * A * K * η ^ α := by
          have hf := hCfr (Φ := Φ) (h := h) (z := z) (K := K) (η := η)
            hK hηpos hηeq hP2 hg
          rw [← hS2] at hf
          rw [show g (z + h) = g z' from by rw [hzh]] at hf
          exact hf
        have hcres : ‖(∫ u in S2, F u) - (∫ u in S2T, F u)‖ ≤ Ccr * (A * K) * η ^ α := by
          have hc := hCcr (B := A * K) (η := η) (b := 4 * R) (by positivity) hηpos h2ηle
            (h := h) hηeq hFmeas hFpt
          rwa [← hS2, ← hS2Teq] at hc
        calc ‖(∫ x in S2, A1 x) - (∫ x in S2, A2 x)‖
            = ‖(∫ x in S2, (Φ x - Φ (x - h)) * (g (z + x) - g z'))
                + ((∫ x in S2, F x) - (∫ u in S2T, F u))‖ := by rw [hS2eq]
          _ ≤ ‖∫ x in S2, (Φ x - Φ (x - h)) * (g (z + x) - g z')‖
              + ‖(∫ x in S2, F x) - (∫ u in S2T, F u)‖ := norm_add_le _ _
          _ ≤ Cfr * A * K * η ^ α + Ccr * (A * K) * η ^ α := add_le_add hfar hcres
          _ = (Cfr + Ccr) * A * K * η ^ α := by ring
      · -- the degenerate case: S2 is empty
        have hempty : S2 = ∅ := by
          rw [hS2]
          ext x
          simp only [mem_eucShell, Set.mem_empty_iff_false, iff_false, not_and]
          intro hx h4R
          linarith
        rw [hempty, MeasureTheory.setIntegral_empty, MeasureTheory.setIntegral_empty, sub_self,
          norm_zero]
        have hnn : 0 ≤ (Cfr + Ccr) * A * K * η ^ α :=
          mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt (add_pos_of_pos_of_nonneg hCfrpos hCcrpos.le))
            hA.le) hK) (Real.rpow_nonneg hηnn α)
        exact hnn
    -- ===== combine =====
    have hηbound : η ≤ Real.sqrt n * ‖z - z'‖ :=
      Work.CR.Flat.Cauchy.bmCz.eucNorm_le_sqrt_mul_norm (z - z')
    have hηpow : η ^ α ≤ (Real.sqrt n) ^ α * ‖z - z'‖ ^ α := by
      have h := Real.rpow_le_rpow hηnn hηbound hαnn
      rwa [Real.mul_rpow (Real.sqrt_nonneg n) (norm_nonneg _)] at h
    have h2ηpow : (2 * η) ^ α ≤ (2 * Real.sqrt n) ^ α * ‖z - z'‖ ^ α := by
      have h1 : (2 * η) ≤ 2 * Real.sqrt n * ‖z - z'‖ := by linarith
      have h2 := Real.rpow_le_rpow (by positivity) h1 hαnn
      rwa [Real.mul_rpow (by norm_num) (norm_nonneg _)] at h2
    have hmain : ‖(∫ x in S1, A1 x) - (∫ x in S1, A2 x)‖ + ‖(∫ x in S2, A1 x) - (∫ x in S2, A2 x)‖
        ≤ CB * K * ‖z - z'‖ ^ α := by
      have h1 : 2 * A * Crad * (2 * η) ^ α * K
          ≤ 2 * A * Crad * (2 * Real.sqrt n) ^ α * K * ‖z - z'‖ ^ α := by
        rw [show 2 * A * Crad * (2 * η) ^ α * K = (2 * A * Crad * K) * (2 * η) ^ α from by ring,
          show 2 * A * Crad * (2 * Real.sqrt n) ^ α * K * ‖z - z'‖ ^ α
            = (2 * A * Crad * K) * ((2 * Real.sqrt n) ^ α * ‖z - z'‖ ^ α) from by ring]
        exact mul_le_mul_of_nonneg_left h2ηpow (by positivity)
      have h2 : (Cfr + Ccr) * A * K * η ^ α
          ≤ (Cfr + Ccr) * A * (Real.sqrt n) ^ α * K * ‖z - z'‖ ^ α := by
        rw [show (Cfr + Ccr) * A * K * η ^ α = ((Cfr + Ccr) * A * K) * η ^ α from by ring,
          show (Cfr + Ccr) * A * (Real.sqrt n) ^ α * K * ‖z - z'‖ ^ α
            = ((Cfr + Ccr) * A * K) * ((Real.sqrt n) ^ α * ‖z - z'‖ ^ α) from by ring]
        exact mul_le_mul_of_nonneg_left hηpow (by positivity)
      calc ‖(∫ x in S1, A1 x) - (∫ x in S1, A2 x)‖ + ‖(∫ x in S2, A1 x) - (∫ x in S2, A2 x)‖
          ≤ 2 * A * Crad * (2 * η) ^ α * K + (Cfr + Ccr) * A * K * η ^ α :=
            add_le_add hS1bound hS2bound
        _ ≤ 2 * A * Crad * (2 * Real.sqrt n) ^ α * K * ‖z - z'‖ ^ α
              + (Cfr + Ccr) * A * (Real.sqrt n) ^ α * K * ‖z - z'‖ ^ α := add_le_add h1 h2
        _ = CB * K * ‖z - z'‖ ^ α := by rw [hCB]; ring
    have hfinal : ‖(∫ x in eucBall (4 * R), A1 x) - (∫ x in eucBall (4 * R), A2 x)‖
        ≤ CB * K * ‖z - z'‖ ^ α := by
      rw [hrewrite]
      exact le_trans (norm_add_le _ _) hmain
    exact le_trans hfinal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right CA CB) hK)
      (Real.rpow_nonneg (norm_nonneg _) α))

end Work.NN.Core
