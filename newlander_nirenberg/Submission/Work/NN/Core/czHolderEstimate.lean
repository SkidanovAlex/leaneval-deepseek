/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The Calderón–Zygmund (Schauder) estimate for a singular integral kernel on `ℂⁿ`

This file proves `Work.NN.Core.czHolderEstimate`: for a kernel `Φ` of homogeneity `-2n` on
`ℂⁿ = Fin n → ℂ` (size bound, kernel-difference bound, vanishing mean on every annulus centred at
the origin) and an `α`-Hölder function `g` (`0 < α < 1`), the truncated singular integral

  `z ↦ ∫_{‖x‖ < 4R} Φ x · (g (z + x) - g z)`

is bounded and `α`-Hölder, with constants depending only on `n, α, A, R`.

The proof is the classical Calderón–Zygmund argument:

* the difference `I z - I z'` is the integral of `Φ x ((g (z+x) - g z) - (g (z'+x) - g z'))`;
* it is split into the ball of radius `2η` (`η = ‖z - z'‖`), where the Hölder continuity of `g`
  and the integrability of `‖x‖^{α-2n}` give `O(η^α)`, and into the surrounding annulus
  `2η ≤ ‖x‖ < 4R`;
* in the annulus the vanishing mean lets one drop the constants `g z`, `g z'`, and the remaining
  integral is the kernel-difference of `Φ` against `g (z + ·) - g (z + h)` on the annulus
  (`czFarKernelDiff`) plus the change of the annulus under translation by `h = z' - z`
  (`czCrescent`); both are `O(η^α)`.

The two Calderón–Zygmund estimates for the annulus, and the radial/measure-theoretic
infrastructure, are in `Work/CR/Flat/Cauchy/bmCz/`.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmCz.eucRadialBound
import Submission.Work.CR.Flat.Cauchy.bmCz.abs_eucNorm_sub_le
import Submission.Work.CR.Flat.Cauchy.bmCz.czAux
import Submission.Work.CR.Flat.Cauchy.bmCz.czFarKernelDiff
import Submission.Work.CR.Flat.Cauchy.bmCz.czCrescent
import Submission.Work.NN.Core.czHolderDefs

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace Work.NN.Core

open Work.CR.Flat.Cauchy

/-- A globally `α`-Hölder function with `0 < α` is continuous. -/
lemma continuous_of_holder_euc'' {n : ℕ} {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    {g : (Fin n → ℂ) → ℂ} (hg : ∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) :
    Continuous g := by
  have hH : HolderWith (Real.toNNReal K) (Real.toNNReal α) g := by
    intro x y
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
    refine le_trans (ENNReal.ofReal_le_ofReal (hg x y)) ?_
    rw [ENNReal.ofReal_mul hK, ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hα.le]
    rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal K hK, Real.coe_toNNReal α hα.le]
  exact hH.continuous (by rw [Real.toNNReal_pos]; exact hα)

/-- A function bounded on a finite-measure measurable set is integrable there. -/
lemma integrableOn_of_norm_le_const_nn {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {s : Set (Fin n → ℂ)} (hsm : MeasurableSet s) (hfin : (volume : Measure (Fin n → ℂ)) s < ⊤)
    {F : (Fin n → ℂ) → E} (hm : AEStronglyMeasurable F (volume.restrict s)) {M : ℝ}
    (h : ∀ x ∈ s, ‖F x‖ ≤ M) : IntegrableOn F s volume :=
  MeasureTheory.IntegrableOn.of_bound hfin hm M
    ((MeasureTheory.ae_restrict_iff' hsm).mpr (Filter.Eventually.of_forall fun x hx => h x hx))

/-- **Calderón–Zygmund (Schauder) estimate for a singular integral kernel.**  Let `Φ : ℂⁿ → ℂ`
(`n ≥ 1`, `ℂⁿ = Fin n → ℂ` with the Euclidean norm `eucNorm`) satisfy the three classical
conditions of a Calderón–Zygmund kernel of homogeneity `-2n`:

* a size bound `‖Φ x‖ ≤ A / ‖x‖^{2n}` for `x ≠ 0`;
* a difference bound `‖Φ (x - h) - Φ x‖ ≤ A ‖h‖ / ‖x‖^{2n+1}` for `2‖h‖ ≤ ‖x‖`;
* vanishing mean on shells: `∫_{a ≤ ‖x‖ < b} Φ = 0`.

Let `g : ℂⁿ → ℂ` be `α`-Hölder with constant `K` for some `0 < α < 1`, vanishing off the ball of
radius `R`.  Then the convolution `z ↦ ∫_{‖x‖ < 4R} Φ x · (g (z + x) - g z) dx` is bounded by
`C K` and is `α`-Hölder with constant `C K`, with `C` depending only on `n, α, A, R`.

This is the real-analysis core of the Bochner–Martinelli Schauder estimate. -/
theorem czHolderEstimate {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {R : ℝ} (hR : 0 < R)
    {Φ : (Fin n → ℂ) → ℂ} (hΦm : AEStronglyMeasurable Φ volume)
    {A : ℝ} (hA : 0 < A)
    (hP1 : ∀ x : Fin n → ℂ, x ≠ 0 →
      ‖Φ x‖ ≤ A / (Work.CR.Flat.Cauchy.eucNorm x) ^ (2 * n))
    (hP2 : ∀ x h : Fin n → ℂ,
      2 * Work.CR.Flat.Cauchy.eucNorm h ≤ Work.CR.Flat.Cauchy.eucNorm x →
      ‖Φ (x - h) - Φ x‖
        ≤ A * Work.CR.Flat.Cauchy.eucNorm h / (Work.CR.Flat.Cauchy.eucNorm x) ^ (2 * n + 1))
    (hH2 : ∀ a b : ℝ, 0 < a → a < b →
      ∫ x in Work.CR.Flat.Cauchy.eucShell a b, Φ x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ), 0 ≤ K → ∀ g : (Fin n → ℂ) → ℂ,
      (∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) →
      (∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0) →
      (∀ z : Fin n → ℂ,
        ‖∫ x in Work.CR.Flat.Cauchy.eucBall (4 * R), Φ x * (g (z + x) - g z)‖ ≤ C * K) ∧
      (∀ z z' : Fin n → ℂ,
        ‖(∫ x in Work.CR.Flat.Cauchy.eucBall (4 * R), Φ x * (g (z + x) - g z))
            - (∫ x in Work.CR.Flat.Cauchy.eucBall (4 * R), Φ x * (g (z' + x) - g z'))‖
          ≤ C * K * ‖z - z'‖ ^ α) := by
  obtain ⟨Crad, hCradpos, hCrad⟩ :=
    Work.CR.Flat.Cauchy.bmCz.eucRadialBound hn (α - 2 * (n : ℝ)) (by linarith)
  obtain ⟨Cfr, hCfrpos, hCfr⟩ :=
    Work.CR.Flat.Cauchy.bmCz.czFarKernelDiff hn hα hα1 hA hR
  obtain ⟨Ccr, hCcrpos, hCcr⟩ :=
    Work.CR.Flat.Cauchy.bmCz.czCrescent hn hα hα1
  have hsqnpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hsqn1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  set CA : ℝ := A * Crad * (4 * R) ^ α with hCA
  set CB : ℝ := 2 * A * Crad * (2 * Real.sqrt n) ^ α + (Cfr + Ccr) * A * (Real.sqrt n) ^ α
    with hCB
  have hCApos : 0 < CA := by rw [hCA]; positivity
  have hCBpos : 0 < CB := by
    rw [hCB]
    have h1 : 0 < (2 * Real.sqrt n) ^ α := Real.rpow_pos_of_pos (by positivity) _
    have h2 : 0 < (Real.sqrt n) ^ α := Real.rpow_pos_of_pos hsqnpos _
    positivity
  refine ⟨max (max CA CB) (2 * CA), ?_, ?_⟩
  · exact lt_of_lt_of_le hCApos
      (le_trans (le_max_left CA CB) (le_max_left (max CA CB) (2 * CA)))
  · intro K hK g hg hgsupp
    have hgcont : Continuous g := continuous_of_holder_euc'' hα hK hg
    have hmeas_of : ∀ w : Fin n → ℂ,
        AEStronglyMeasurable (fun x : Fin n → ℂ => Φ x * (g (w + x) - g w))
          (volume.restrict (eucBall (n := n) (4 * R))) := by
      intro w
      refine (hΦm.mono_measure Measure.restrict_le_self).mul ?_
      exact (((hgcont.comp (continuous_const.add continuous_id)).sub
        continuous_const).aestronglyMeasurable).mono_measure Measure.restrict_le_self
    have hIntBall : ∀ w : Fin n → ℂ,
        IntegrableOn (fun x : Fin n → ℂ => Φ x * (g (w + x) - g w))
          (eucBall (n := n) (4 * R)) volume := by
      intro w
      refine integrableOn_of_le_eucNorm_rpow_ball (n := n) hn (s := α - 2 * (n : ℝ))
        (by linarith) (ρ := 4 * R) (hmeas_of w) (C := A * K) (by positivity) (fun x _ => ?_)
      exact norm_Phi_mul_le hα hα1 hA hK hP1 hg w x
    have hbdd : ∀ z : Fin n → ℂ,
        ‖∫ x in eucBall (n := n) (4 * R), Φ x * (g (z + x) - g z)‖ ≤ CA * K := by
      intro z
      have hmaj : IntegrableOn (fun x : Fin n → ℂ => A * K * eucNorm x ^ (α - 2 * (n : ℝ)))
          (eucBall (n := n) (4 * R)) volume :=
        (integrableOn_eucNorm_rpow_ball hn (by linarith) (4 * R)).const_mul (A * K)
      have hb := norm_setIntegral_le_of_norm_le' (measurableSet_eucBall (n := n) (4 * R)) hmaj
        (fun x _ => norm_Phi_mul_le hα hα1 hA hK hP1 hg z x)
      rw [MeasureTheory.integral_const_mul] at hb
      have h4 := hCrad (4 * R) (by linarith)
      rw [show α - 2 * (n : ℝ) + 2 * (n : ℝ) = α from by ring] at h4
      calc ‖∫ x in eucBall (n := n) (4 * R), Φ x * (g (z + x) - g z)‖
          ≤ A * K * ∫ x in eucBall (n := n) (4 * R), eucNorm x ^ (α - 2 * (n : ℝ)) := hb
        _ ≤ A * K * (Crad * (4 * R) ^ α) := mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = CA * K := by rw [hCA]; ring
    constructor
    · intro z
      refine le_trans (hbdd z) ?_
      exact mul_le_mul_of_nonneg_right
        (le_trans (le_max_left CA CB) (le_max_left (max CA CB) (2 * CA))) hK
    · intro z z'
      by_cases hzz : z = z'
      · subst hzz
        have h0 : (0 : ℝ) ^ α = 0 := Real.zero_rpow (ne_of_gt hα)
        simp [h0]
      · have hδpos : 0 < ‖z - z'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzz)
        rcases le_or_gt 1 ‖z - z'‖ with hδ1 | hδ1
        · -- the two points are far apart: use the uniform bound twice
          have hp : (1 : ℝ) ≤ ‖z - z'‖ ^ α := Real.one_le_rpow hδ1 hα.le
          have hsum : ‖(∫ x in eucBall (n := n) (4 * R), Φ x * (g (z + x) - g z))
              - (∫ x in eucBall (n := n) (4 * R), Φ x * (g (z' + x) - g z'))‖
              ≤ 2 * (CA * K) := by
            refine le_trans (norm_sub_le _ _) ?_
            rw [show 2 * (CA * K) = CA * K + CA * K from by ring]
            exact add_le_add (hbdd z) (hbdd z')
          calc ‖(∫ x in eucBall (n := n) (4 * R), Φ x * (g (z + x) - g z))
                - (∫ x in eucBall (n := n) (4 * R), Φ x * (g (z' + x) - g z'))‖
              ≤ 2 * (CA * K) := hsum
            _ = (2 * CA) * K := by ring
            _ ≤ max (max CA CB) (2 * CA) * K :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) hK
            _ = max (max CA CB) (2 * CA) * K * 1 := by ring
            _ ≤ max (max CA CB) (2 * CA) * K * ‖z - z'‖ ^ α :=
                mul_le_mul_of_nonneg_left hp (by positivity)
        · -- the two points are close
          set h : Fin n → ℂ := z' - z with hh
          have hzh : z + h = z' := by rw [hh]; abel
          have hhnz : h ≠ 0 := by rw [hh]; exact sub_ne_zero.mpr (Ne.symm hzz)
          set η : ℝ := eucNorm h with hη
          have hηpos : 0 < η := by rw [hη]; exact eucNorm_pos hhnz
          have hηδ : η ≤ Real.sqrt n * ‖z - z'‖ := by
            rw [hη, hh]
            calc eucNorm (z' - z) ≤ Real.sqrt n * ‖z' - z‖ := Work.CR.Flat.Cauchy.bmCz.eucNorm_le_sqrt_mul_norm _
              _ = Real.sqrt n * ‖z - z'‖ := by rw [norm_sub_rev]
          have hηα : η ^ α ≤ (Real.sqrt n) ^ α * ‖z - z'‖ ^ α := by
            calc η ^ α ≤ (Real.sqrt n * ‖z - z'‖) ^ α := Real.rpow_le_rpow hηpos.le hηδ hα.le
              _ = (Real.sqrt n) ^ α * ‖z - z'‖ ^ α :=
                  Real.mul_rpow (Real.sqrt_nonneg n) (norm_nonneg _)
          have h2ηα : (2 * η) ^ α ≤ (2 * Real.sqrt n) ^ α * ‖z - z'‖ ^ α := by
            have h2 : 2 * η ≤ 2 * (Real.sqrt n * ‖z - z'‖) := by linarith
            calc (2 * η) ^ α ≤ (2 * (Real.sqrt n * ‖z - z'‖)) ^ α :=
                  Real.rpow_le_rpow (by linarith) h2 hα.le
              _ = (2 * Real.sqrt n) ^ α * ‖z - z'‖ ^ α := by
                  rw [show 2 * (Real.sqrt n * ‖z - z'‖) = (2 * Real.sqrt n) * ‖z - z'‖ from by ring]
                  exact Real.mul_rpow (by positivity) (norm_nonneg _)
          set S1 : Set (Fin n → ℂ) := eucBall (n := n) (2 * η) ∩ eucBall (n := n) (4 * R) with hS1
          set S2 : Set (Fin n → ℂ) := eucShell (n := n) (2 * η) (4 * R) with hS2
          have hS1m : MeasurableSet S1 := by
            rw [hS1]; exact (measurableSet_eucBall _).inter (measurableSet_eucBall _)
          have hS2m : MeasurableSet S2 := by rw [hS2]; exact measurableSet_eucShell _ _
          have hS1sub : S1 ⊆ eucBall (n := n) (2 * η) := by rw [hS1]; exact inter_subset_left
          have hS1subB : S1 ⊆ eucBall (n := n) (4 * R) := by rw [hS1]; exact inter_subset_right
          have hS2subB : S2 ⊆ eucBall (n := n) (4 * R) := by
            rw [hS2]; intro x hx; exact hx.2
          have hS2fin : (volume : Measure (Fin n → ℂ)) S2 < ⊤ := by
            refine volume_lt_top_of_subset_eucNorm (M := 4 * R) ?_
            intro x hx
            rw [hS2] at hx
            exact le_of_lt hx.2
          have hdisj : Disjoint S1 S2 := by
            rw [Set.disjoint_left]
            intro x hx hx'
            rw [hS1] at hx
            rw [hS2] at hx'
            exact absurd hx.1 (not_lt.mpr hx'.1)
          have hunion : S1 ∪ S2 = eucBall (n := n) (4 * R) := by
            rw [hS1, hS2]
            ext x
            simp only [mem_eucBall, mem_eucShell, Set.mem_union, Set.mem_inter_iff]
            constructor
            · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
            · intro hx
              rcases lt_or_ge (eucNorm x) (2 * η) with hlt | hge
              · exact Or.inl ⟨hlt, hx⟩
              · exact Or.inr ⟨hge, hx⟩
          have hIntS1 : ∀ w : Fin n → ℂ,
              IntegrableOn (fun x : Fin n → ℂ => Φ x * (g (w + x) - g w)) S1 volume :=
            fun w => (hIntBall w).mono_set hS1subB
          have hIntS2 : ∀ w : Fin n → ℂ,
              IntegrableOn (fun x : Fin n → ℂ => Φ x * (g (w + x) - g w)) S2 volume :=
            fun w => (hIntBall w).mono_set hS2subB
          have hsplit_z : ∫ x in eucBall (n := n) (4 * R), Φ x * (g (z + x) - g z)
              = (∫ x in S1, Φ x * (g (z + x) - g z))
                + (∫ x in S2, Φ x * (g (z + x) - g z)) := by
            rw [← hunion]
            exact MeasureTheory.setIntegral_union hdisj hS2m (hIntS1 z) (hIntS2 z)
          have hsplit_z' : ∫ x in eucBall (n := n) (4 * R), Φ x * (g (z' + x) - g z')
              = (∫ x in S1, Φ x * (g (z' + x) - g z'))
                + (∫ x in S2, Φ x * (g (z' + x) - g z')) := by
            rw [← hunion]
            exact MeasureTheory.setIntegral_union hdisj hS2m (hIntS1 z') (hIntS2 z')
          have hmain : (∫ x in eucBall (n := n) (4 * R), Φ x * (g (z + x) - g z))
                - (∫ x in eucBall (n := n) (4 * R), Φ x * (g (z' + x) - g z'))
              = ((∫ x in S1, Φ x * (g (z + x) - g z))
                  - (∫ x in S1, Φ x * (g (z' + x) - g z')))
                + ((∫ x in S2, Φ x * (g (z + x) - g z))
                  - (∫ x in S2, Φ x * (g (z' + x) - g z'))) := by
            rw [hsplit_z, hsplit_z']; ring
          -- ---------- the inner ball `S1` ----------
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
            have hmaj1 : IntegrableOn (fun x : Fin n → ℂ => A * K * eucNorm x ^ (α - 2 * (n : ℝ)))
                S1 volume :=
              MeasureTheory.IntegrableOn.mono_set
                (MeasureTheory.Integrable.const_mul
                  (integrableOn_eucNorm_rpow_ball hn (by linarith) (2 * η)) (A * K)) hS1sub
            have hA1 : ‖∫ x in S1, Φ x * (g (z + x) - g z)‖ ≤ A * Crad * (2 * η) ^ α * K := by
              have hb := norm_setIntegral_le_of_norm_le' hS1m hmaj1
                (fun x _ => norm_Phi_mul_le hα hα1 hA hK hP1 hg z x)
              rw [MeasureTheory.integral_const_mul] at hb
              calc ‖∫ x in S1, Φ x * (g (z + x) - g z)‖
                  ≤ A * K * ∫ x in S1, eucNorm x ^ (α - 2 * (n : ℝ)) := hb
                _ ≤ A * K * (Crad * (2 * η) ^ α) := mul_le_mul_of_nonneg_left hS1e (by positivity)
                _ = A * Crad * (2 * η) ^ α * K := by ring
            have hA2 : ‖∫ x in S1, Φ x * (g (z' + x) - g z')‖ ≤ A * Crad * (2 * η) ^ α * K := by
              have hb := norm_setIntegral_le_of_norm_le' hS1m hmaj1
                (fun x _ => norm_Phi_mul_le hα hα1 hA hK hP1 hg z' x)
              rw [MeasureTheory.integral_const_mul] at hb
              calc ‖∫ x in S1, Φ x * (g (z' + x) - g z')‖
                  ≤ A * K * ∫ x in S1, eucNorm x ^ (α - 2 * (n : ℝ)) := hb
                _ ≤ A * K * (Crad * (2 * η) ^ α) := mul_le_mul_of_nonneg_left hS1e (by positivity)
                _ = A * Crad * (2 * η) ^ α * K := by ring
            calc ‖(∫ x in S1, Φ x * (g (z + x) - g z))
                  - (∫ x in S1, Φ x * (g (z' + x) - g z'))‖
                ≤ ‖∫ x in S1, Φ x * (g (z + x) - g z)‖
                  + ‖∫ x in S1, Φ x * (g (z' + x) - g z')‖ := norm_sub_le _ _
              _ ≤ 2 * A * Crad * (2 * η) ^ α * K := by
                  rw [show 2 * A * Crad * (2 * η) ^ α * K
                      = A * Crad * (2 * η) ^ α * K + A * Crad * (2 * η) ^ α * K from by ring]
                  exact add_le_add hA1 hA2
          -- ---------- the annulus `S2` ----------
          have hS2bound : ‖(∫ x in S2, Φ x * (g (z + x) - g z))
                - (∫ x in S2, Φ x * (g (z' + x) - g z'))‖
              ≤ (Cfr + Ccr) * A * K * η ^ α := by
            by_cases h2ηlt : 2 * η < 4 * R
            · have h2ηle : 2 * η ≤ 4 * R := le_of_lt h2ηlt
              have hη2R : η < 2 * R := by linarith
              have hPhiZero : ∫ x in S2, Φ x = 0 := by
                rw [hS2]; exact hH2 (2 * η) (4 * R) (by linarith) h2ηlt
              have hIntPhi : IntegrableOn Φ S2 volume := by
                refine integrableOn_of_norm_le_const_nn hS2m hS2fin
                  (hΦm.mono_measure Measure.restrict_le_self) (M := A / (2 * η) ^ (2 * n)) ?_
                intro x hx
                rw [hS2] at hx
                have hxne : x ≠ 0 := by
                  intro h0
                  rw [h0, mem_eucShell] at hx
                  rw [eucNorm_zero] at hx
                  linarith [hx.1, hηpos]
                exact le_trans (hP1 x hxne)
                  (div_le_div_of_nonneg_left hA.le (pow_pos (by linarith) _)
                    (pow_le_pow_left₀ (by linarith) hx.1 _))
              have hmeas_z' : AEStronglyMeasurable
                  (fun x : Fin n → ℂ => Φ x * (g (z + x) - g z')) volume :=
                hΦm.mul (((hgcont.comp (continuous_const.add continuous_id)).sub
                  continuous_const).aestronglyMeasurable)
              have hInt_z' : IntegrableOn (fun x : Fin n → ℂ => Φ x * (g (z + x) - g z'))
                  S2 volume := by
                refine integrableOn_of_norm_le_const_nn hS2m hS2fin
                  (hmeas_z'.mono_measure (Measure.restrict_le_self :
                    volume.restrict S2 ≤ volume))
                  (M := A / (2 * η) ^ (2 * n) * (K * (6 * R) ^ α)) ?_
                intro x hx
                rw [hS2] at hx
                have hxne : x ≠ 0 := by
                  intro h0
                  rw [h0, mem_eucShell] at hx
                  rw [eucNorm_zero] at hx
                  linarith [hx.1, hηpos]
                have h1 : ‖Φ x‖ ≤ A / (2 * η) ^ (2 * n) :=
                  le_trans (hP1 x hxne)
                    (div_le_div_of_nonneg_left hA.le (pow_pos (by linarith) _)
                      (pow_le_pow_left₀ (by linarith) hx.1 _))
                have h2 : ‖g (z + x) - g z'‖ ≤ K * (6 * R) ^ α := by
                  have hge := hg (z + x) z'
                  rw [show (z + x) - z' = x - h from by rw [hh]; abel] at hge
                  have hbd : ‖x - h‖ ≤ 6 * R := by
                    calc ‖x - h‖ ≤ eucNorm (x - h) := pi_norm_le_eucNorm _
                      _ ≤ eucNorm x + eucNorm h := eucNorm_sub_le x h
                      _ ≤ 4 * R + η := by linarith [hx.2]
                      _ ≤ 6 * R := by linarith [hη2R]
                  calc ‖g (z + x) - g z'‖ ≤ K * ‖x - h‖ ^ α := hge
                    _ ≤ K * (6 * R) ^ α :=
                        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hbd hα.le) hK
                rw [norm_mul]
                exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
              have hInt_c : IntegrableOn (fun x : Fin n → ℂ => Φ x * (g z' - g z)) S2 volume :=
                (hIntPhi.const_mul (g z' - g z)).congr
                  (Filter.Eventually.of_forall (fun x => by ring))
              have hstep1 : ∫ x in S2, Φ x * (g (z + x) - g z)
                  = ∫ x in S2, Φ x * (g (z + x) - g z') := by
                have hpt : ∀ x : Fin n → ℂ,
                    Φ x * (g (z + x) - g z)
                      = Φ x * (g (z + x) - g z') + Φ x * (g z' - g z) := by
                  intro x; ring
                rw [setIntegral_congr_fun hS2m (fun x _ => hpt x),
                  MeasureTheory.integral_add hInt_z' hInt_c]
                have hzero : ∫ x in S2, Φ x * (g z' - g z) = 0 := by
                  rw [show (fun x : Fin n → ℂ => Φ x * (g z' - g z))
                      = fun x : Fin n → ℂ => (g z' - g z) * Φ x from by funext x; ring]
                  rw [MeasureTheory.integral_const_mul, hPhiZero, mul_zero]
                rw [hzero, add_zero]
              -- the shifted-integrand function
              set F : (Fin n → ℂ) → ℂ := fun u => Φ (u - h) * (g (z + u) - g z') with hF
              set S2T : Set (Fin n → ℂ) := (fun u : Fin n → ℂ => u + h) '' S2 with hS2T
              have hS2Teq : S2T = {u : Fin n → ℂ | 2 * η ≤ eucNorm (u - h) ∧ eucNorm (u - h) < 4 * R} := by
                rw [hS2T, hS2]
                ext u
                simp only [Set.mem_image, mem_eucShell, Set.mem_setOf_eq]
                constructor
                · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
                  simpa using ⟨h1, h2⟩
                · intro hu
                  exact ⟨u - h, ⟨hu.1, hu.2⟩, by ring⟩
              have htrans : ∫ x in S2, Φ x * (g (z' + x) - g z') = ∫ u in S2T, F u := by
                have hfun : (fun x : Fin n → ℂ => Φ x * (g (z' + x) - g z'))
                    = fun x : Fin n → ℂ => F (x + h) := by
                  funext x
                  simp only [hF]
                  rw [add_sub_cancel_right,
                    show z + (x + h) = z' + x from by rw [← hzh]; abel]
                rw [hfun, hS2T]
                exact setIntegral_translate_euc h F S2
              have hF_pt : ∀ u : Fin n → ℂ, ‖F u‖ ≤ A * K * eucNorm (u - h) ^ (α - 2 * (n : ℝ)) := by
                intro u
                have key := norm_Phi_mul_le hα hα1 hA hK hP1 hg z' (u - h)
                simpa [hF, show z' + (u - h) = z + u from by rw [← hzh]; abel] using key
              have hFmeas : AEStronglyMeasurable F volume := by
                rw [hF]
                exact (aestronglyMeasurable_comp_sub hΦm h).mul
                  (((hgcont.comp (continuous_const.add continuous_id)).sub
                    continuous_const).aestronglyMeasurable)
              have hIntF2 : IntegrableOn F S2 volume := by
                refine integrableOn_of_le_eucNorm_rpow_shell (n := n) (s := α - 2 * (n : ℝ))
                  (a := 2 * η) (b := 4 * R) (by linarith) h2ηle
                  (hFmeas.mono_measure (Measure.restrict_le_self : volume.restrict
                    (eucShell (n := n) (2 * η) (4 * R)) ≤ volume))
                  (C := A * K * (1 / 2 : ℝ) ^ (α - 2 * (n : ℝ))) (by positivity) ?_
                intro u hu
                rw [mem_eucShell] at hu
                have hupos : 0 < eucNorm u := by linarith [hu.1]
                have h1 : eucNorm u ≤ eucNorm (u - h) + η := by
                  have h2 : eucNorm u = eucNorm ((u - h) + h) := by
                    congr 1
                    abel
                  calc eucNorm u = eucNorm ((u - h) + h) := h2
                    _ ≤ eucNorm (u - h) + eucNorm h := eucNorm_add_le (u - h) h
                    _ = eucNorm (u - h) + η := by rw [hη]
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
                calc ‖F u‖ ≤ A * K * eucNorm (u - h) ^ (α - 2 * (n : ℝ)) := hF_pt u
                  _ ≤ A * K * ((1 / 2 : ℝ) ^ (α - 2 * (n : ℝ))
                        * eucNorm u ^ (α - 2 * (n : ℝ))) :=
                      mul_le_mul_of_nonneg_left h3 (by positivity)
                  _ = A * K * (1 / 2 : ℝ) ^ (α - 2 * (n : ℝ))
                        * eucNorm u ^ (α - 2 * (n : ℝ)) := by ring
              have hmid : (∫ u in S2, Φ u * (g (z + u) - g z')) - (∫ x in S2, F x)
                  = ∫ x in S2, (Φ x - Φ (x - h)) * (g (z + x) - g z') := by
                rw [← MeasureTheory.integral_sub hInt_z' hIntF2]
                refine setIntegral_congr_fun hS2m (fun x _ => ?_)
                simp only [hF]; ring
              have hS2eq : (∫ x in S2, Φ x * (g (z + x) - g z))
                    - (∫ x in S2, Φ x * (g (z' + x) - g z'))
                  = (∫ x in S2, (Φ x - Φ (x - h)) * (g (z + x) - g z'))
                    + ((∫ x in S2, F x) - (∫ u in S2T, F u)) := by
                rw [hstep1, htrans, ← hmid]
                ring
              have hfar : ‖∫ x in S2, (Φ x - Φ (x - h)) * (g (z + x) - g z')‖
                  ≤ Cfr * A * K * η ^ α := by
                have hf := hCfr (Φ := Φ) (h := h) (z := z) (K := K) (η := η)
                  hK hηpos hη.symm hP2 hg
                rw [← hS2] at hf
                rw [show g (z + h) = g z' from by rw [hzh]] at hf
                exact hf
              have hcres : ‖(∫ u in S2, F u) - (∫ u in S2T, F u)‖ ≤ Ccr * (A * K) * η ^ α := by
                have hc := hCcr (B := A * K) (η := η) (b := 4 * R) (by positivity) hηpos h2ηle
                  hη.symm hFmeas hF_pt
                rwa [← hS2, ← hS2Teq] at hc
              calc ‖(∫ x in S2, Φ x * (g (z + x) - g z))
                    - (∫ x in S2, Φ x * (g (z' + x) - g z'))‖
                  = ‖(∫ x in S2, (Φ x - Φ (x - h)) * (g (z + x) - g z'))
                      + ((∫ x in S2, F x) - (∫ u in S2T, F u))‖ := by rw [hS2eq]
                _ ≤ ‖∫ x in S2, (Φ x - Φ (x - h)) * (g (z + x) - g z')‖
                    + ‖(∫ x in S2, F x) - (∫ u in S2T, F u)‖ := norm_add_le _ _
                _ ≤ Cfr * A * K * η ^ α + Ccr * (A * K) * η ^ α := add_le_add hfar hcres
                _ = (Cfr + Ccr) * A * K * η ^ α := by ring
            · push_neg at h2ηlt
              have hempty : S2 = ∅ := by
                rw [hS2]
                ext x
                simp only [mem_eucShell, Set.mem_empty_iff_false, iff_false, not_and]
                intro hx h4R
                linarith
              rw [hempty, MeasureTheory.setIntegral_empty, MeasureTheory.setIntegral_empty,
                sub_self, norm_zero]
              exact mul_nonneg
                (mul_nonneg (mul_nonneg (le_of_lt (add_pos_of_pos_of_nonneg hCfrpos hCcrpos.le))
                  hA.le) hK)
                (Real.rpow_nonneg (le_of_lt hηpos) _)
          -- ---------- combination ----------
          have ht1 : 2 * A * Crad * (2 * η) ^ α * K
              ≤ 2 * A * Crad * (2 * Real.sqrt n) ^ α * K * ‖z - z'‖ ^ α := by
            rw [show 2 * A * Crad * (2 * η) ^ α * K
                = (2 * A * Crad * K) * (2 * η) ^ α from by ring]
            rw [show 2 * A * Crad * (2 * Real.sqrt n) ^ α * K * ‖z - z'‖ ^ α
                = (2 * A * Crad * K) * ((2 * Real.sqrt n) ^ α * ‖z - z'‖ ^ α) from by ring]
            exact mul_le_mul_of_nonneg_left h2ηα (by positivity)
          have ht2 : (Cfr + Ccr) * A * K * η ^ α
              ≤ (Cfr + Ccr) * A * (Real.sqrt n) ^ α * K * ‖z - z'‖ ^ α := by
            rw [show (Cfr + Ccr) * A * K * η ^ α = ((Cfr + Ccr) * A * K) * η ^ α from by ring]
            rw [show (Cfr + Ccr) * A * (Real.sqrt n) ^ α * K * ‖z - z'‖ ^ α
                = ((Cfr + Ccr) * A * K) * ((Real.sqrt n) ^ α * ‖z - z'‖ ^ α) from by ring]
            exact mul_le_mul_of_nonneg_left hηα (by positivity)
          have hfinal : ‖(∫ x in eucBall (n := n) (4 * R), Φ x * (g (z + x) - g z))
                - (∫ x in eucBall (n := n) (4 * R), Φ x * (g (z' + x) - g z'))‖
              ≤ CB * K * ‖z - z'‖ ^ α := by
            rw [hmain]
            calc ‖(∫ x in S1, Φ x * (g (z + x) - g z))
                    - (∫ x in S1, Φ x * (g (z' + x) - g z'))
                  + ((∫ x in S2, Φ x * (g (z + x) - g z))
                    - (∫ x in S2, Φ x * (g (z' + x) - g z')))‖
                ≤ ‖(∫ x in S1, Φ x * (g (z + x) - g z))
                    - (∫ x in S1, Φ x * (g (z' + x) - g z'))‖
                  + ‖(∫ x in S2, Φ x * (g (z + x) - g z))
                    - (∫ x in S2, Φ x * (g (z' + x) - g z'))‖ := norm_add_le _ _
              _ ≤ 2 * A * Crad * (2 * η) ^ α * K + (Cfr + Ccr) * A * K * η ^ α :=
                  add_le_add hS1bound hS2bound
              _ ≤ 2 * A * Crad * (2 * Real.sqrt n) ^ α * K * ‖z - z'‖ ^ α
                    + (Cfr + Ccr) * A * (Real.sqrt n) ^ α * K * ‖z - z'‖ ^ α :=
                  add_le_add ht1 ht2
              _ = CB * K * ‖z - z'‖ ^ α := by rw [hCB]; ring
          calc ‖(∫ x in eucBall (n := n) (4 * R), Φ x * (g (z + x) - g z))
                - (∫ x in eucBall (n := n) (4 * R), Φ x * (g (z' + x) - g z'))‖
              ≤ CB * K * ‖z - z'‖ ^ α := hfinal
            _ ≤ max (max CA CB) (2 * CA) * K * ‖z - z'‖ ^ α := by
                refine mul_le_mul_of_nonneg_right ?_ ?_
                · exact mul_le_mul_of_nonneg_right
                    (le_trans (le_max_right CA CB) (le_max_left (max CA CB) (2 * CA))) hK
                · exact Real.rpow_nonneg (norm_nonneg _) _

end Work.NN.Core
