import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.SmallBoxSliding.boxMass_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The volume of a coordinate box in `ℝ³` -/

theorem volume_prod_Icc_fin3 (α β : Fin 3 → ℝ) :
    (MeasureTheory.volume {y : ℝ³ | ∀ k : Fin 3, y k ∈ Set.Icc (α k) (β k)})
      = ∏ k : Fin 3, ENNReal.ofReal (β k - α k) := by
  set C : Set (Fin 3 → ℝ) := Set.pi (Set.univ : Set (Fin 3)) (fun k => Set.Icc (α k) (β k))
    with hC
  have hbox : {y : ℝ³ | ∀ k : Fin 3, y k ∈ Set.Icc (α k) (β k)} = WithLp.ofLp ⁻¹' C := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hC, Set.mem_pi, Set.mem_univ, true_implies]
  rw [hbox]
  have hCmeas : MeasurableSet C := by
    rw [hC]
    exact MeasurableSet.pi Set.countable_univ (fun k _ => measurableSet_Icc)
  rw [MeasurePreserving.measure_preimage (PiLp.volume_preserving_ofLp (Fin 3))
    hCmeas.nullMeasurableSet]
  rw [hC, volume_pi, Measure.pi_pi]
  simp [Real.volume_Icc]

/-! ## 2. `dlBox` as a coordinate box -/

theorem dlBox_eq_prod_Icc (ℓ d : ℝ) (u : ℝ³) :
    Submission.BoseGases.dlBox ℓ d u
      = {y : ℝ³ | ∀ k : Fin 3,
          y k ∈ Set.Icc (max (((ℓ * d) • u) k - ℓ * d / 2) (-(ℓ / 2)))
                (min (((ℓ * d) • u) k + ℓ * d / 2) (ℓ / 2))} := by
  ext y
  simp only [Submission.BoseGases.mem_dlBox_iff, Submission.BoseGases.mem_acube_iff,
    Set.mem_ofPred_eq, Set.mem_Icc, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨h1, h2⟩ k
    exact ⟨max_le (by linarith [(h2 k).1]) (by linarith [(h1 k).1]),
      le_min (by linarith [(h2 k).2]) (by linarith [(h1 k).2])⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro k
      have h1 := (h k).1
      have h2 := le_max_right (ℓ * d * u.ofLp k - ℓ * d / 2) (-(ℓ / 2))
      have h3 := (h k).2
      have h4 := min_le_right (ℓ * d * u.ofLp k + ℓ * d / 2) (ℓ / 2)
      exact ⟨by linarith, by linarith⟩
    · intro k
      have h1 := (h k).1
      have h2 := le_max_left (ℓ * d * u.ofLp k - ℓ * d / 2) (-(ℓ / 2))
      have h3 := (h k).2
      have h4 := min_le_left (ℓ * d * u.ofLp k + ℓ * d / 2) (ℓ / 2)
      exact ⟨by linarith, by linarith⟩

/-! ## 3. The per-coordinate cutoff/box-length bound -/

theorem cutPerDir_le {M : ℕ} (hM : 1 ≤ M) {ℓ d c t : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (ht : |t| ≤ ℓ / 2) (htc : |t - c| ≤ ℓ * d / 2) :
    (ℓ * d / 2 - |t - c|) ^ (2 * M)
      ≤ (min (c + ℓ * d / 2) (ℓ / 2) - max (c - ℓ * d / 2) (-(ℓ / 2)))
          * max ((ℓ * d) ^ (2 * M - 1))
              ((ℓ * d) ^ (2 * M) * (1 / 2) ^ (2 * M) / min (ℓ * d / 2) ℓ) := by
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  have hm : 0 < min (ℓ * d / 2) ℓ := lt_min (by linarith) hℓ
  have hmlld : min (ℓ * d / 2) ℓ ≤ ℓ * d := by
    have := min_le_left (ℓ * d / 2) ℓ; linarith
  have hml : min (ℓ * d / 2) ℓ ≤ ℓ := min_le_right _ _
  have ht1 : -(ℓ / 2) ≤ t := (abs_le.mp ht).1
  have ht2 : t ≤ ℓ / 2 := (abs_le.mp ht).2
  have htc' : -(ℓ * d / 2) ≤ t - c ∧ t - c ≤ ℓ * d / 2 := abs_le.mp htc
  have hA : ℓ * d / 2 - |t - c| = min (t - (c - ℓ * d / 2)) ((c + ℓ * d / 2) - t) := by
    rcases le_total (t - c) 0 with h | h
    · rw [abs_of_nonpos h]
      rw [show ℓ * d / 2 - -(t - c) = t - (c - ℓ * d / 2) by ring]
      rw [min_eq_left (by linarith)]
    · rw [abs_of_nonneg h]
      rw [show ℓ * d / 2 - (t - c) = (c + ℓ * d / 2) - t by ring]
      rw [min_eq_right (by linarith)]
  have hA0 : 0 ≤ ℓ * d / 2 - |t - c| := by linarith [abs_nonneg (t - c)]
  have hAle : ℓ * d / 2 - |t - c| ≤ ℓ * d / 2 := by linarith [abs_nonneg (t - c)]
  have key_in : ∀ A L : ℝ, 0 ≤ A → 0 ≤ L → min (ℓ * d / 2) ℓ ≤ L → A ≤ ℓ * d / 2 →
      A ^ (2 * M) ≤ L * max ((ℓ * d) ^ (2 * M - 1))
        ((ℓ * d) ^ (2 * M) * (1 / 2) ^ (2 * M) / min (ℓ * d / 2) ℓ) := by
    intro A L hA0 hL0 hmL hAL
    have h1 : A ^ (2 * M) ≤ (ℓ * d / 2) ^ (2 * M) := pow_le_pow_left₀ hA0 hAL (2 * M)
    have h6 : (ℓ * d / 2) ^ (2 * M) = (ℓ * d) ^ (2 * M) * (1 / 2) ^ (2 * M) := by
      rw [div_eq_mul_inv, mul_pow, one_div]
    have hY : (0:ℝ) ≤ (ℓ * d) ^ (2 * M) * (1 / 2) ^ (2 * M) / min (ℓ * d / 2) ℓ := by
      positivity
    have h7 : ((ℓ * d) ^ (2 * M) * (1 / 2) ^ (2 * M) / min (ℓ * d / 2) ℓ) * min (ℓ * d / 2) ℓ
        = (ℓ * d) ^ (2 * M) * (1 / 2) ^ (2 * M) := div_mul_cancel₀ _ (ne_of_gt hm)
    have h8 : ((ℓ * d) ^ (2 * M) * (1 / 2) ^ (2 * M) / min (ℓ * d / 2) ℓ) * min (ℓ * d / 2) ℓ
        ≤ ((ℓ * d) ^ (2 * M) * (1 / 2) ^ (2 * M) / min (ℓ * d / 2) ℓ) * L :=
      mul_le_mul_of_nonneg_left hmL hY
    have h9 : ((ℓ * d) ^ (2 * M) * (1 / 2) ^ (2 * M) / min (ℓ * d / 2) ℓ) * L
        ≤ L * max ((ℓ * d) ^ (2 * M - 1))
            ((ℓ * d) ^ (2 * M) * (1 / 2) ^ (2 * M) / min (ℓ * d / 2) ℓ) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) hL0
    calc A ^ (2 * M) ≤ (ℓ * d / 2) ^ (2 * M) := h1
      _ = (ℓ * d) ^ (2 * M) * (1 / 2) ^ (2 * M) := h6
      _ = ((ℓ * d) ^ (2 * M) * (1 / 2) ^ (2 * M) / min (ℓ * d / 2) ℓ) * min (ℓ * d / 2) ℓ :=
          h7.symm
      _ ≤ ((ℓ * d) ^ (2 * M) * (1 / 2) ^ (2 * M) / min (ℓ * d / 2) ℓ) * L := h8
      _ ≤ L * max ((ℓ * d) ^ (2 * M - 1))
            ((ℓ * d) ^ (2 * M) * (1 / 2) ^ (2 * M) / min (ℓ * d / 2) ℓ) := h9
  have key_out : ∀ A L : ℝ, 0 ≤ A → 0 ≤ L → A ≤ L → L ≤ ℓ * d →
      A ^ (2 * M) ≤ L * max ((ℓ * d) ^ (2 * M - 1))
        ((ℓ * d) ^ (2 * M) * (1 / 2) ^ (2 * M) / min (ℓ * d / 2) ℓ) := by
    intro A L hA0 hL0 hAL hLld
    have h1 : A ^ (2 * M) ≤ L ^ (2 * M) := pow_le_pow_left₀ hA0 hAL (2 * M)
    have h2 : L ^ (2 * M) = L * L ^ (2 * M - 1) := by
      conv_lhs => rw [show 2 * M = (2 * M - 1) + 1 by omega, pow_succ]
      ring
    have h3 : L ^ (2 * M - 1) ≤ (ℓ * d) ^ (2 * M - 1) :=
      pow_le_pow_left₀ hL0 hLld (2 * M - 1)
    have h4 : L * L ^ (2 * M - 1) ≤ L * (ℓ * d) ^ (2 * M - 1) :=
      mul_le_mul_of_nonneg_left h3 hL0
    have h5 : L * (ℓ * d) ^ (2 * M - 1) ≤ L * max ((ℓ * d) ^ (2 * M - 1))
        ((ℓ * d) ^ (2 * M) * (1 / 2) ^ (2 * M) / min (ℓ * d / 2) ℓ) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hL0
    calc A ^ (2 * M) ≤ L ^ (2 * M) := h1
      _ = L * L ^ (2 * M - 1) := h2
      _ ≤ L * (ℓ * d) ^ (2 * M - 1) := h4
      _ ≤ L * max ((ℓ * d) ^ (2 * M - 1))
            ((ℓ * d) ^ (2 * M) * (1 / 2) ^ (2 * M) / min (ℓ * d / 2) ℓ) := h5
  rcases le_total (-(ℓ / 2)) (c - ℓ * d / 2) with ha | ha
  · rcases le_total (c + ℓ * d / 2) (ℓ / 2) with hb | hb
    · have hL : min (c + ℓ * d / 2) (ℓ / 2) - max (c - ℓ * d / 2) (-(ℓ / 2)) = ℓ * d := by
        rw [min_eq_left hb, max_eq_left ha]; ring
      rw [hL]
      exact key_in _ _ hA0 hld.le hmlld hAle
    · have hL : min (c + ℓ * d / 2) (ℓ / 2) - max (c - ℓ * d / 2) (-(ℓ / 2))
          = ℓ / 2 - (c - ℓ * d / 2) := by
        rw [min_eq_right hb, max_eq_left ha]
      have hLld : ℓ / 2 - (c - ℓ * d / 2) ≤ ℓ * d := by linarith
      have hAL : ℓ * d / 2 - |t - c| ≤ ℓ / 2 - (c - ℓ * d / 2) := by
        rw [hA]
        exact le_trans (min_le_left _ _) (by linarith [ht2])
      rw [hL]
      exact key_out _ _ hA0 (by linarith) hAL hLld
  · rcases le_total (c + ℓ * d / 2) (ℓ / 2) with hb | hb
    · have hL : min (c + ℓ * d / 2) (ℓ / 2) - max (c - ℓ * d / 2) (-(ℓ / 2))
          = (c + ℓ * d / 2) + ℓ / 2 := by
        rw [min_eq_left hb, max_eq_right ha]; ring
      have hLld : (c + ℓ * d / 2) + ℓ / 2 ≤ ℓ * d := by linarith
      have hAL : ℓ * d / 2 - |t - c| ≤ (c + ℓ * d / 2) + ℓ / 2 := by
        rw [hA]
        exact le_trans (min_le_right _ _) (by linarith [ht1])
      rw [hL]
      exact key_out _ _ hA0 (by linarith) hAL hLld
    · have hL : min (c + ℓ * d / 2) (ℓ / 2) - max (c - ℓ * d / 2) (-(ℓ / 2)) = ℓ := by
        rw [min_eq_right hb, max_eq_right ha]; ring
      rw [hL]
      exact key_in _ _ hA0 hℓ.le hml hAle

/-! ## 4. The product form of the cosine-bump decay -/

theorem chiSmall_prod_decay {M : ℕ} (hM : 1 ≤ M) (z : ℝ³) :
    |Submission.BoseGases.chiSmall M z|
      ≤ 4 ^ (2 * M) * Submission.BoseGases.chiSmallDecay M
          * ∏ k : Fin 3, (max (1 / 2 - |z k|) 0) ^ M := by
  have hp : ∀ k : Fin 3, 0 ≤ max (1 / 2 - |z k|) 0 := fun k => le_max_right _ _
  have hbase : |Submission.BoseGases.chiSmallBase M z|
      ≤ 4 ^ (3 * M) * ∏ k : Fin 3, (max (1 / 2 - |z k|) 0) ^ M := by
    rw [Submission.BoseGases.chiSmallBase]
    rw [abs_of_nonneg (pow_nonneg (mul_nonneg (mul_nonneg
      (Submission.BoseGases.zeta1d_nonneg _)
      (Submission.BoseGases.zeta1d_nonneg _)) (Submission.BoseGases.zeta1d_nonneg _)) M)]
    have hprod : (Submission.BoseGases.zeta1d (z 0) * Submission.BoseGases.zeta1d (z 1)
        * Submission.BoseGases.zeta1d (z 2))
        ≤ ∏ k : Fin 3, (4 * max (1 / 2 - |z k|) 0) := by
      rw [Fin.prod_univ_three]
      have h0 := Submission.BoseGases.zeta1d_le_four_max (z 0)
      have h1 := Submission.BoseGases.zeta1d_le_four_max (z 1)
      have h2 := Submission.BoseGases.zeta1d_le_four_max (z 2)
      have hn1 := Submission.BoseGases.zeta1d_nonneg (z 1)
      have hn2 := Submission.BoseGases.zeta1d_nonneg (z 2)
      have h01 : Submission.BoseGases.zeta1d (z 0) * Submission.BoseGases.zeta1d (z 1)
          ≤ (4 * max (1 / 2 - |z 0|) 0) * (4 * max (1 / 2 - |z 1|) 0) :=
        mul_le_mul h0 h1 hn1 (by positivity)
      exact mul_le_mul h01 h2 hn2 (by positivity)
    calc (Submission.BoseGases.zeta1d (z 0) * Submission.BoseGases.zeta1d (z 1)
          * Submission.BoseGases.zeta1d (z 2)) ^ M
        ≤ (∏ k : Fin 3, (4 * max (1 / 2 - |z k|) 0)) ^ M :=
          pow_le_pow_left₀ (mul_nonneg (mul_nonneg (Submission.BoseGases.zeta1d_nonneg _)
            (Submission.BoseGases.zeta1d_nonneg _)) (Submission.BoseGases.zeta1d_nonneg _)) hprod M
      _ = 4 ^ (3 * M) * ∏ k : Fin 3, (max (1 / 2 - |z k|) 0) ^ M := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
          simp only [Finset.card_univ, Fintype.card_fin]
          rw [mul_pow, ← pow_mul, Finset.prod_pow]
  rw [Submission.BoseGases.chiSmall_abs_eq hM z, Submission.BoseGases.chiSmallDecay]
  have hnf : 0 ≤ Submission.BoseGases.chiSmallNormFactor M :=
    Submission.BoseGases.chiSmallNormFactor_nonneg M
  calc |Submission.BoseGases.chiSmallBase M z| * Submission.BoseGases.chiSmallNormFactor M
      ≤ (4 ^ (3 * M) * ∏ k : Fin 3, (max (1 / 2 - |z k|) 0) ^ M)
          * Submission.BoseGases.chiSmallNormFactor M :=
        mul_le_mul_of_nonneg_right hbase hnf
    _ = 4 ^ (2 * M) * (Submission.BoseGases.chiSmallNormFactor M * 4 ^ M)
          * ∏ k : Fin 3, (max (1 / 2 - |z k|) 0) ^ M := by
        rw [show (4:ℝ) ^ (3 * M) = 4 ^ (2 * M) * 4 ^ M by rw [← pow_add]; ring_nf]
        ring

/-! ## 5. The key geometric lemma: the cutoff at a point of the box is controlled by `|B(u)|` -/

/-- The `k`-th side length of the sliding box `dlBox ℓ d u`. -/
noncomputable def boxSide (ℓ d : ℝ) (u : ℝ³) (k : Fin 3) : ℝ :=
  min (((ℓ * d) • u) k + ℓ * d / 2) (ℓ / 2) - max (((ℓ * d) • u) k - ℓ * d / 2) (-(ℓ / 2))

/-- **The two-factor cutoff at a point of the sliding box is bounded by the box volume.**
For `t ∈ B(u) = dlBox ℓ d u`, in the dilute regime `R0 ≤ ℓd/16`, `R0 ≤ ℓ·chiR0`,

`χ_{B(u)}(t)² ≤ C·(chiSupAbs·chiSmallDecay M)²·|B(u)|`,

with `C` depending only on `R0` and `M`. -/
theorem chiB_sq_le_boxMass {M : ℕ} (hM : 1 ≤ M) {R0 : ℝ} (hR0 : 0 < R0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
      (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
      (u t : ℝ³), t ∈ Submission.BoseGases.dlBox ℓ d u →
      (Submission.BoseGases.chiSmallB M ℓ d u t) ^ 2
        ≤ C * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
            * Work.SmallBoxSliding.boxMass ℓ d u := by
  refine ⟨4 ^ (4 * M) * (max ((16 * R0)⁻¹)
      ((1 / 2 : ℝ) ^ (2 * M) / min (8 * R0) (R0 / Submission.BoseGases.chiR0))) ^ 3,
    mul_nonneg (by positivity) (pow_nonneg (by positivity) 3), ?_⟩
  intro ℓ d hℓ hd hR hRχ u t ht
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  have hchiR0 : 0 < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
  have h16 : 16 * R0 ≤ ℓ * d := by linarith
  have hm0 : 0 < min (ℓ * d / 2) ℓ := lt_min (by linarith) hℓ
  have hn0 : 0 < min (8 * R0) (R0 / Submission.BoseGases.chiR0) :=
    lt_min (by linarith) (div_pos hR0 hchiR0)
  have hmle : min (8 * R0) (R0 / Submission.BoseGases.chiR0) ≤ min (ℓ * d / 2) ℓ := by
    refine min_le_min ?_ ?_
    · linarith
    · rw [div_le_iff₀ hchiR0]; linarith
  have hmmld : min (ℓ * d / 2) ℓ ≤ ℓ * d :=
    le_trans (min_le_left _ _) (by linarith)
  have hmml : min (ℓ * d / 2) ℓ ≤ ℓ := min_le_right _ _
  -- membership in the two cubes, coordinatewise
  have hmem := (Submission.BoseGases.mem_dlBox_iff ℓ d u t).mp ht
  have htco : ∀ k : Fin 3, |t k| ≤ ℓ / 2 ∧ |t k - ((ℓ * d) • u) k| ≤ ℓ * d / 2 := by
    intro k
    have h1 := (Submission.BoseGases.mem_acube_iff ℓ t).mp hmem.1 k
    have h2 := (Submission.BoseGases.mem_acube_iff (ℓ * d) (t - (ℓ * d) • u)).mp hmem.2 k
    rw [Set.mem_Icc] at h1 h2
    have h2' : t k - ((ℓ * d) • u) k ∈ Set.Icc (-(ℓ * d) / 2) ((ℓ * d) / 2) := by
      simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h2
    rw [Set.mem_Icc] at h2'
    exact ⟨by rw [abs_le]; exact ⟨by linarith [h1.1], by linarith [h1.2]⟩,
      by rw [abs_le]; exact ⟨by linarith [h2'.1], by linarith [h2'.2]⟩⟩
  have hLnn : ∀ k : Fin 3, 0 ≤ boxSide ℓ d u k := by
    intro k
    have h1 := (abs_le.mp (htco k).1)
    have h2 := (abs_le.mp (htco k).2)
    have ha : max (((ℓ * d) • u) k - ℓ * d / 2) (-(ℓ / 2)) ≤ t k := by
      rw [max_le_iff]; exact ⟨by linarith, by linarith⟩
    have hb : t k ≤ min (((ℓ * d) • u) k + ℓ * d / 2) (ℓ / 2) := by
      rw [le_min_iff]; exact ⟨by linarith, by linarith⟩
    rw [boxSide]
    exact sub_nonneg.mpr (le_trans ha hb)
  -- the volume is the product of the side lengths
  have hboxmass : Work.SmallBoxSliding.boxMass ℓ d u = ∏ k : Fin 3, boxSide ℓ d u k := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def,
      dlBox_eq_prod_Icc, volume_prod_Icc_fin3, ENNReal.toReal_prod]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [show min (((ℓ * d) • u) k + ℓ * d / 2) (ℓ / 2)
        - max (((ℓ * d) • u) k - ℓ * d / 2) (-(ℓ / 2)) = boxSide ℓ d u k from rfl]
    rw [ENNReal.toReal_ofReal (hLnn k)]
  -- the per-coordinate cutoff bound
  have hcut : ∀ k : Fin 3,
      (max (ℓ * d / 2 - |t k - ((ℓ * d) • u) k|) 0) ^ (2 * M)
        ≤ boxSide ℓ d u k * (ℓ * d) ^ (2 * M)
            * max ((ℓ * d)⁻¹)
              ((1 / 2 : ℝ) ^ (2 * M) / min (ℓ * d / 2) ℓ) := by
    intro k
    obtain ⟨h1, h2⟩ := htco k
    have hnn : 0 ≤ ℓ * d / 2 - |t k - ((ℓ * d) • u) k| :=
      by linarith [abs_nonneg (t k - ((ℓ * d) • u) k)]
    rw [max_eq_left hnn]
    have hbase := cutPerDir_le (M := M) hM hℓ hd h1 h2
    have hbase' : (ℓ * d / 2 - |t k - ((ℓ * d) • u) k|) ^ (2 * M)
        ≤ boxSide ℓ d u k * max ((ℓ * d) ^ (2 * M - 1))
            ((ℓ * d) ^ (2 * M) * (1 / 2 : ℝ) ^ (2 * M) / min (ℓ * d / 2) ℓ) := by
      rw [boxSide]
      exact hbase
    have hpow : (ℓ * d) ^ (2 * M) * (ℓ * d)⁻¹ = (ℓ * d) ^ (2 * M - 1) := by
      rw [← div_eq_mul_inv]
      conv_lhs => rw [show 2 * M = (2 * M - 1) + 1 by omega, pow_succ]
      exact mul_div_cancel_right₀ _ (ne_of_gt hld)
    have hsub : (ℓ * d) ^ (2 * M - 1)
        ≤ (ℓ * d) ^ (2 * M) * max ((ℓ * d)⁻¹)
            ((1 / 2 : ℝ) ^ (2 * M) / min (ℓ * d / 2) ℓ) := by
      rw [← hpow]
      exact mul_le_mul_of_nonneg_left (le_max_left ((ℓ * d)⁻¹)
        ((1 / 2 : ℝ) ^ (2 * M) / min (ℓ * d / 2) ℓ)) (by positivity)
    have hsec : (ℓ * d) ^ (2 * M) * (1 / 2 : ℝ) ^ (2 * M) / min (ℓ * d / 2) ℓ
        ≤ (ℓ * d) ^ (2 * M) * max ((ℓ * d)⁻¹)
            ((1 / 2 : ℝ) ^ (2 * M) / min (ℓ * d / 2) ℓ) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (le_max_right ((ℓ * d)⁻¹)
        ((1 / 2 : ℝ) ^ (2 * M) / min (ℓ * d / 2) ℓ)) (by positivity)
    refine le_trans hbase' ?_
    calc boxSide ℓ d u k * max ((ℓ * d) ^ (2 * M - 1))
          ((ℓ * d) ^ (2 * M) * (1 / 2 : ℝ) ^ (2 * M) / min (ℓ * d / 2) ℓ)
        ≤ boxSide ℓ d u k * ((ℓ * d) ^ (2 * M) * max ((ℓ * d)⁻¹)
            ((1 / 2 : ℝ) ^ (2 * M) / min (ℓ * d / 2) ℓ)) :=
          mul_le_mul_of_nonneg_left (max_le hsub hsec) (hLnn k)
      _ = boxSide ℓ d u k * (ℓ * d) ^ (2 * M) * max ((ℓ * d)⁻¹)
            ((1 / 2 : ℝ) ^ (2 * M) / min (ℓ * d / 2) ℓ) := by ring
  -- the product of the cutoff factors
  have hcutprod : ∏ k : Fin 3, (max (ℓ * d / 2 - |t k - ((ℓ * d) • u) k|) 0) ^ (2 * M)
      ≤ (∏ k : Fin 3, boxSide ℓ d u k) * (ℓ * d) ^ (6 * M)
          * (max ((ℓ * d)⁻¹) ((1 / 2 : ℝ) ^ (2 * M) / min (ℓ * d / 2) ℓ)) ^ 3 := by
    calc ∏ k : Fin 3, (max (ℓ * d / 2 - |t k - ((ℓ * d) • u) k|) 0) ^ (2 * M)
        ≤ ∏ k : Fin 3, (boxSide ℓ d u k * (ℓ * d) ^ (2 * M)
            * max ((ℓ * d)⁻¹) ((1 / 2 : ℝ) ^ (2 * M) / min (ℓ * d / 2) ℓ)) :=
          Finset.prod_le_prod₀ (fun k _ => by positivity) (fun k _ => hcut k)
      _ = (∏ k : Fin 3, boxSide ℓ d u k)
            * ((ℓ * d) ^ (2 * M)) ^ 3
            * (max ((ℓ * d)⁻¹) ((1 / 2 : ℝ) ^ (2 * M) / min (ℓ * d / 2) ℓ)) ^ 3 := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
            Finset.prod_const]
          simp only [Finset.card_univ, Fintype.card_fin]
      _ = (∏ k : Fin 3, boxSide ℓ d u k) * (ℓ * d) ^ (6 * M)
            * (max ((ℓ * d)⁻¹) ((1 / 2 : ℝ) ^ (2 * M) / min (ℓ * d / 2) ℓ)) ^ 3 := by
          rw [← pow_mul, show 2 * M * 3 = 6 * M by omega]
  -- the change of variables in the bump argument
  have hzk : ∀ k : Fin 3, ((ℓ * d)⁻¹ • t - u) k = (t k - ((ℓ * d) • u) k) / (ℓ * d) := by
    intro k
    simp only [Pi.sub_apply, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    field_simp
  have hz : ∏ k : Fin 3, (max (1 / 2 - |((ℓ * d)⁻¹ • t - u) k|) 0) ^ (2 * M)
      = (∏ k : Fin 3, (max (ℓ * d / 2 - |t k - ((ℓ * d) • u) k|) 0) ^ (2 * M))
          / (ℓ * d) ^ (6 * M) := by
    have hk : ∀ k : Fin 3, (max (1 / 2 - |((ℓ * d)⁻¹ • t - u) k|) 0) ^ (2 * M)
        = (max (ℓ * d / 2 - |t k - ((ℓ * d) • u) k|) 0) ^ (2 * M) / (ℓ * d) ^ (2 * M) := by
      intro k
      have h1 : max (1 / 2 - |((ℓ * d)⁻¹ • t - u) k|) 0
          = max (ℓ * d / 2 - |t k - ((ℓ * d) • u) k|) 0 / (ℓ * d) := by
        rw [hzk k, abs_div, abs_of_pos hld,
          show (1 / 2 : ℝ) - |t k - ((ℓ * d) • u) k| / (ℓ * d)
            = (ℓ * d / 2 - |t k - ((ℓ * d) • u) k|) / (ℓ * d) by
            field_simp,
          show max (ℓ * d / 2 - |t k - ((ℓ * d) • u) k|) 0 / (ℓ * d)
            = max ((ℓ * d / 2 - |t k - ((ℓ * d) • u) k|) / (ℓ * d)) (0 / (ℓ * d)) from
            Submission.BoseGases.max_div_eq_div_max hld,
          zero_div]
      rw [h1, div_pow]
    rw [Finset.prod_congr rfl (fun k _ => hk k)]
    rw [Finset.prod_div_distrib, Finset.prod_const]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [← pow_mul, show 2 * M * 3 = 6 * M by omega]
  -- the squared bump factor
  have hdec := chiSmall_prod_decay (M := M) hM ((ℓ * d)⁻¹ • t - u)
  have hsmall : (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • t - u)) ^ 2
      ≤ (4 ^ (2 * M) * Submission.BoseGases.chiSmallDecay M) ^ 2
        * ∏ k : Fin 3, (max (1 / 2 - |((ℓ * d)⁻¹ • t - u) k|) 0) ^ (2 * M) := by
    rw [show (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • t - u)) ^ 2
        = |Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • t - u)| ^ 2 from (sq_abs _).symm]
    calc |Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • t - u)| ^ 2
        ≤ ((4 ^ (2 * M) * Submission.BoseGases.chiSmallDecay M)
            * ∏ k : Fin 3, (max (1 / 2 - |((ℓ * d)⁻¹ • t - u) k|) 0) ^ M) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hdec 2
      _ = (4 ^ (2 * M) * Submission.BoseGases.chiSmallDecay M) ^ 2
            * (∏ k : Fin 3, (max (1 / 2 - |((ℓ * d)⁻¹ • t - u) k|) 0) ^ M) ^ 2 := by
          rw [mul_pow]
      _ = (4 ^ (2 * M) * Submission.BoseGases.chiSmallDecay M) ^ 2
            * ∏ k : Fin 3, (max (1 / 2 - |((ℓ * d)⁻¹ • t - u) k|) 0) ^ (2 * M) := by
          congr 1
          rw [← Finset.prod_pow]
          exact Finset.prod_congr rfl (fun k _ => by
            rw [← pow_mul, show M * 2 = 2 * M by omega])
  -- the geometric factor: `E ≤ E'`
  have hE : (max ((ℓ * d)⁻¹) ((1 / 2 : ℝ) ^ (2 * M) / min (ℓ * d / 2) ℓ)) ^ 3
      ≤ (max ((16 * R0)⁻¹)
          ((1 / 2 : ℝ) ^ (2 * M) / min (8 * R0) (R0 / Submission.BoseGases.chiR0))) ^ 3 := by
    have hbase_le : max ((ℓ * d)⁻¹) ((1 / 2 : ℝ) ^ (2 * M) / min (ℓ * d / 2) ℓ)
        ≤ max ((16 * R0)⁻¹)
          ((1 / 2 : ℝ) ^ (2 * M) / min (8 * R0) (R0 / Submission.BoseGases.chiR0)) := by
      refine max_le ?_ ?_
      · have hpos : (0:ℝ) < 16 * R0 := by linarith
        exact le_trans ((inv_le_inv₀ hld hpos).mpr h16) (le_max_left _ _)
      · refine le_trans ?_ (le_max_right ((16 * R0)⁻¹)
          ((1 / 2 : ℝ) ^ (2 * M) / min (8 * R0) (R0 / Submission.BoseGases.chiR0)))
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ hm0 hn0).mpr hmle) (by positivity)
    exact pow_le_pow_left₀ (by positivity) hbase_le 3
  -- the product of the cutoff factors is bounded by the box mass
  have hprodV : ∏ k : Fin 3, (max (1 / 2 - |((ℓ * d)⁻¹ • t - u) k|) 0) ^ (2 * M)
      ≤ Work.SmallBoxSliding.boxMass ℓ d u
          * (max ((16 * R0)⁻¹)
            ((1 / 2 : ℝ) ^ (2 * M) / min (8 * R0) (R0 / Submission.BoseGases.chiR0))) ^ 3 := by
    rw [hz, div_le_iff₀ (by positivity : (0:ℝ) < (ℓ * d) ^ (6 * M))]
    calc ∏ k : Fin 3, (max (ℓ * d / 2 - |t k - ((ℓ * d) • u) k|) 0) ^ (2 * M)
        ≤ (∏ k : Fin 3, boxSide ℓ d u k) * (ℓ * d) ^ (6 * M)
            * (max ((ℓ * d)⁻¹) ((1 / 2 : ℝ) ^ (2 * M) / min (ℓ * d / 2) ℓ)) ^ 3 := hcutprod
      _ = Work.SmallBoxSliding.boxMass ℓ d u
            * ((ℓ * d) ^ (6 * M)
              * (max ((ℓ * d)⁻¹) ((1 / 2 : ℝ) ^ (2 * M) / min (ℓ * d / 2) ℓ)) ^ 3) := by
          rw [hboxmass]; ring
      _ ≤ Work.SmallBoxSliding.boxMass ℓ d u
            * ((ℓ * d) ^ (6 * M)
              * (max ((16 * R0)⁻¹)
                ((1 / 2 : ℝ) ^ (2 * M)
                  / min (8 * R0) (R0 / Submission.BoseGases.chiR0))) ^ 3) := by
          refine mul_le_mul_of_nonneg_left ?_ (by
            rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
            exact ENNReal.toReal_nonneg)
          exact mul_le_mul_of_nonneg_left hE (by positivity)
      _ = Work.SmallBoxSliding.boxMass ℓ d u
            * (max ((16 * R0)⁻¹)
              ((1 / 2 : ℝ) ^ (2 * M)
                / min (8 * R0) (R0 / Submission.BoseGases.chiR0))) ^ 3
            * (ℓ * d) ^ (6 * M) := by ring
  -- conclusion
  have hchi : (Submission.BoseGases.chiScale ℓ t) ^ 2 ≤ Submission.BoseGases.chiSupAbs ^ 2 := by
    rw [← sq_abs (Submission.BoseGases.chiScale ℓ t)]
    exact pow_le_pow_left₀ (abs_nonneg _) (Submission.BoseGases.chiScale_abs_le_sup ℓ t) 2
  have hone : (Submission.BoseGases.chiSmallB M ℓ d u t) ^ 2
      = (Submission.BoseGases.chiScale ℓ t) ^ 2
        * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • t - u)) ^ 2 := by
    rw [Submission.BoseGases.chiSmallB, mul_pow]
  rw [hone]
  calc (Submission.BoseGases.chiScale ℓ t) ^ 2
        * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • t - u)) ^ 2
      ≤ Submission.BoseGases.chiSupAbs ^ 2
        * ((4 ^ (2 * M) * Submission.BoseGases.chiSmallDecay M) ^ 2
          * (Work.SmallBoxSliding.boxMass ℓ d u
            * (max ((16 * R0)⁻¹)
              ((1 / 2 : ℝ) ^ (2 * M)
                / min (8 * R0) (R0 / Submission.BoseGases.chiR0))) ^ 3)) := by
        refine mul_le_mul hchi ?_ (by positivity) (by positivity)
        exact le_trans hsmall (mul_le_mul_of_nonneg_left hprodV (by positivity))
    _ = 4 ^ (4 * M) * (max ((16 * R0)⁻¹)
            ((1 / 2 : ℝ) ^ (2 * M)
              / min (8 * R0) (R0 / Submission.BoseGases.chiR0))) ^ 3
          * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
          * Work.SmallBoxSliding.boxMass ℓ d u := by
        rw [mul_pow]
        ring


end Work.BoseFixB1S
