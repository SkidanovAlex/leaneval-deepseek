import Mathlib
import Submission.Work.HP.BCS.Defs
import Submission.Work.HP.BCS.coneTube_bound
import Submission.Work.HP.BCS.count_from_layer
import Submission.Work.HP.BCS.volume_shell_le
import Submission.Work.HP.BCS.layer_subset_coneTube

set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 2000000

open MeasureTheory
open scoped Pointwise

namespace Work.HP.BCS

/-- The two-cone slice of the ball of radius `T`. -/
def Kt {k : ℕ} (a b : EuclideanSpace ℝ (Fin k)) (c d T : ℝ) :
    Set (EuclideanSpace ℝ (Fin k)) :=
  {y | y ∈ coneSet a c ∧ y ∈ coneSet b d ∧ ‖y‖ ≤ T}

lemma mem_Kt {k : ℕ} {a b : EuclideanSpace ℝ (Fin k)} {c d T : ℝ}
    {y : EuclideanSpace ℝ (Fin k)} :
    y ∈ Kt a b c d T ↔ |inner ℝ a y| ≤ c * ‖y‖ ∧ |inner ℝ b y| ≤ d * ‖y‖ ∧ ‖y‖ ≤ T := by
  simp [Kt, coneSet]

/-- The volume of the unit ball in `ℝ^k`. -/
def unitBallVolume (k : ℕ) : ℝ :=
  volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1)

lemma unitBallVolume_nonneg (k : ℕ) : 0 ≤ unitBallVolume k := measureReal_nonneg

lemma cellRad_nonneg {k : ℕ} (Ψ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) :
    0 ≤ cellRad Ψ := by
  rw [cellRad]
  exact Finset.sum_nonneg fun i _ => norm_nonneg _

/-! ## Elementary `ENNReal` helpers -/

private lemma ofReal_add3_le {a b c D : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c ≤ D) :
    ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c ≤ ENNReal.ofReal D := by
  rw [← ENNReal.ofReal_add ha hb, ← ENNReal.ofReal_add (add_nonneg ha hb) hc]
  exact ENNReal.ofReal_le_ofReal h

private lemma ofReal_add2_le {a b D : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b ≤ D) :
    ENNReal.ofReal a + ENNReal.ofReal b ≤ ENNReal.ofReal D := by
  rw [← ENNReal.ofReal_add ha hb]
  exact ENNReal.ofReal_le_ofReal h

/-! ## Homogeneity of the slice -/

lemma Kt_smul (k : ℕ) (a b : EuclideanSpace ℝ (Fin k)) (c d T : ℝ) (hT : 0 < T) :
    Kt a b c d T = T • Kt a b c d 1 := by
  ext y
  rw [mem_Kt, Set.mem_smul_set]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hinv : 0 ≤ T⁻¹ := inv_nonneg.mpr hT.le
    refine ⟨T⁻¹ • y, ?_, ?_⟩
    · rw [mem_Kt]
      have hnorm : ‖T⁻¹ • y‖ = T⁻¹ * ‖y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv]
      refine ⟨?_, ?_, ?_⟩
      · rw [real_inner_smul_right, abs_mul, abs_of_nonneg hinv, hnorm]
        calc T⁻¹ * |inner ℝ a y| ≤ T⁻¹ * (c * ‖y‖) := mul_le_mul_of_nonneg_left h1 hinv
          _ = c * (T⁻¹ * ‖y‖) := by ring
      · rw [real_inner_smul_right, abs_mul, abs_of_nonneg hinv, hnorm]
        calc T⁻¹ * |inner ℝ b y| ≤ T⁻¹ * (d * ‖y‖) := mul_le_mul_of_nonneg_left h2 hinv
          _ = d * (T⁻¹ * ‖y‖) := by ring
      · rw [hnorm]
        calc T⁻¹ * ‖y‖ ≤ T⁻¹ * T := mul_le_mul_of_nonneg_left h3 hinv
          _ = 1 := inv_mul_cancel₀ (ne_of_gt hT)
    · rw [← mul_smul, mul_inv_cancel₀ (ne_of_gt hT), one_smul]
  · rintro ⟨x, hx, hxy⟩
    rw [mem_Kt] at hx
    rw [← hxy]
    obtain ⟨h1, h2, h3⟩ := hx
    have hTnn : 0 ≤ T := hT.le
    have hnorm : ‖T • x‖ = T * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hTnn]
    refine ⟨?_, ?_, ?_⟩
    · rw [real_inner_smul_right, abs_mul, abs_of_nonneg hTnn, hnorm]
      calc T * |inner ℝ a x| ≤ T * (c * ‖x‖) := mul_le_mul_of_nonneg_left h1 hTnn
        _ = c * (T * ‖x‖) := by ring
    · rw [real_inner_smul_right, abs_mul, abs_of_nonneg hTnn, hnorm]
      calc T * |inner ℝ b x| ≤ T * (d * ‖x‖) := mul_le_mul_of_nonneg_left h2 hTnn
        _ = d * (T * ‖x‖) := by ring
    · rw [hnorm]
      calc T * ‖x‖ ≤ T * 1 := mul_le_mul_of_nonneg_left h3 hTnn
        _ = T := mul_one T

lemma Kt_volume_smul (k : ℕ) (a b : EuclideanSpace ℝ (Fin k)) (c d T : ℝ) (hT : 0 < T) :
    (volume (Kt a b c d T)).toReal = T ^ k * (volume (Kt a b c d 1)).toReal := by
  rw [Kt_smul k a b c d T hT, Measure.addHaar_smul_of_nonneg volume hT.le,
    finrank_euclideanSpace, Fintype.card_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hT.le k)]

/-! ## Finiteness of the lattice points in a ball -/

lemma finite_int_abs_le (M : ℝ) : {n : ℤ | |(n : ℝ)| ≤ M}.Finite := by
  refine Set.Finite.subset (Set.finite_Icc ⌈-M⌉ ⌊M⌋) ?_
  intro n hn
  have hn' : |(n : ℝ)| ≤ M := by simpa using hn
  have hn'' := abs_le.mp hn'
  rw [Set.mem_Icc]
  exact ⟨Int.ceil_le.mpr (by linarith [hn''.1]), Int.le_floor.mpr hn''.2⟩

lemma latImage_inter_ball_finite (k : ℕ)
    (Ψ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
    (hΨ : Function.Injective Ψ) (T : ℝ) :
    (latImage Ψ ∩ {y : EuclideanSpace ℝ (Fin k) | ‖y‖ ≤ T}).Finite := by
  classical
  have hsurj : Function.Surjective Ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hΨ
  obtain ⟨e, he⟩ : ∃ e : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      ∀ x, e x = Ψ x :=
    ⟨LinearEquiv.ofBijective Ψ ⟨hΨ, hsurj⟩, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k),
      ∀ x, ‖e.symm x‖ ≤ ‖g‖ * ‖x‖ :=
    ⟨LinearMap.toContinuousLinearMap e.symm.toLinearMap, fun x => by
      simpa using ContinuousLinearMap.le_opNorm (LinearMap.toContinuousLinearMap e.symm.toLinearMap) x⟩
  have himg : latImage Ψ ∩ {y : EuclideanSpace ℝ (Fin k) | ‖y‖ ≤ T}
      = Ψ '' (toEk '' {t : Fin k → ℤ | ‖Ψ (toEk t)‖ ≤ T}) := by
    ext y
    constructor
    · rintro ⟨⟨z, ⟨t, rfl⟩, rfl⟩, hy⟩
      exact ⟨toEk t, ⟨t, by simpa using hy, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨⟨toEk t, ⟨t, rfl⟩, rfl⟩, ht⟩
  have hbox : ({t : Fin k → ℤ | ∀ i, |(t i : ℝ)| ≤ ‖g‖ * T}).Finite := by
    simpa using Set.Finite.pi' (fun _ : Fin k => finite_int_abs_le (‖g‖ * T))
  have hsub : {t : Fin k → ℤ | ‖Ψ (toEk t)‖ ≤ T}
      ⊆ {t : Fin k → ℤ | ∀ i, |(t i : ℝ)| ≤ ‖g‖ * T} := by
    intro t htT i
    have h2 : toEk t = e.symm (Ψ (toEk t)) := by
      rw [← he (toEk t), LinearEquiv.symm_apply_apply]
    calc |(t i : ℝ)| = |(toEk t).ofLp i| := by simp [toEk]
      _ ≤ ‖toEk t‖ := PiLp.norm_apply_le (toEk t) i
      _ = ‖e.symm (Ψ (toEk t))‖ := congrArg (fun z => ‖z‖) h2
      _ ≤ ‖g‖ * ‖Ψ (toEk t)‖ := hg _
      _ ≤ ‖g‖ * T := mul_le_mul_of_nonneg_left htT (norm_nonneg g)
  rw [himg]
  exact Set.Finite.image Ψ (Set.Finite.image toEk (hbox.subset hsub))

/-! ## The volume of the boundary layer -/

/-- Numerical estimate in the case `2R ≤ T`. -/
private lemma arith_caseA {k : ℕ} {ω Ct R S : ℝ} (hω : 0 ≤ ω) (hCt : 0 ≤ Ct) (hR : 0 ≤ R)
    (hS : 0 ≤ S) {b1 b2 b3 : ℝ} (hb1 : b1 = ω * (k : ℝ) * (4 * R) * S ^ (k - 1))
    (hb2 : b2 ≤ Ct * (3 * R) * S ^ (k - 1)) (hb3 : b3 ≤ Ct * (3 * R) * S ^ (k - 1)) :
    b1 + b2 + b3 ≤ (4 * (k : ℝ) * ω + 6 * Ct + 3 * ω + 1) * S ^ (k - 1) * R := by
  subst hb1
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hp : 0 ≤ S ^ (k - 1) := pow_nonneg hS _
  have h1 : 0 ≤ R * S ^ (k - 1) := mul_nonneg hR hp
  have h2 : 0 ≤ Ct * ((3 * R) * S ^ (k - 1)) := mul_nonneg hCt (mul_nonneg (by linarith) hp)
  have h3 : 0 ≤ ω * ((k : ℝ) * ((4 * R) * S ^ (k - 1))) :=
    mul_nonneg hω (mul_nonneg hk (mul_nonneg (by linarith) hp))
  nlinarith [hb2, hb3, h1, h2, h3, mul_nonneg h1 hCt, mul_nonneg h1 hω]

/-- Numerical estimate in the case `T < 2R`. -/
private lemma arith_caseB {k : ℕ} (hk : 1 ≤ k) {ω C R S : ℝ} (hω : 0 ≤ ω) (hR : 0 ≤ R)
    (hS : 0 ≤ S) (hSR : S ≤ 3 * R) (hC : 3 * ω ≤ C) :
    ω * S ^ k ≤ C * S ^ (k - 1) * R := by
  have hp : 0 ≤ S ^ (k - 1) := pow_nonneg hS _
  have hSk : S ^ k = S * S ^ (k - 1) :=
    (congrArg (fun m : ℕ => S ^ m) (Nat.succ_pred_eq_of_pos hk).symm).trans (pow_succ' S (k - 1))
  rw [hSk]
  nlinarith [mul_nonneg hω hp, mul_nonneg hR hp, mul_nonneg hS hp]

lemma layer_volume_le (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ψ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
      (a b : EuclideanSpace ℝ (Fin k)) (c d T : ℝ),
      0 ≤ c → 0 ≤ d → 1 ≤ T →
      volume (layer (Kt a b c d T) (cellRad Ψ))
        ≤ ENNReal.ofReal (C * (T + cellRad Ψ) ^ (k - 1) * cellRad Ψ) := by
  obtain ⟨Ct, hCtpos, hCt⟩ := coneTube_bound k hk
  refine ⟨4 * (k : ℝ) * unitBallVolume k + 6 * Ct + 3 * unitBallVolume k + 1, ?_, ?_⟩
  · have h1 : 0 ≤ 4 * (k : ℝ) * unitBallVolume k :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg k)) (unitBallVolume_nonneg k)
    have h2 : 0 ≤ 6 * Ct := mul_nonneg (by norm_num) hCtpos.le
    have h3 : 0 ≤ 3 * unitBallVolume k := mul_nonneg (by norm_num) (unitBallVolume_nonneg k)
    linarith
  intro Ψ a b c d T hc hd hT
  have hRnn : 0 ≤ cellRad Ψ := cellRad_nonneg Ψ
  have hSn : 0 ≤ T + cellRad Ψ := by linarith
  have hpow : 0 ≤ (T + cellRad Ψ) ^ (k - 1) := pow_nonneg hSn _
  have hωnn : 0 ≤ unitBallVolume k := unitBallVolume_nonneg k
  -- the tube term and its nonnegativity
  have htubenn : 0 ≤ Ct * (3 * cellRad Ψ) * (T + cellRad Ψ) ^ (k - 1) :=
    mul_nonneg (mul_nonneg hCtpos.le (by linarith)) hpow
  have hshellnn : 0 ≤ unitBallVolume k * (k : ℝ) * (4 * cellRad Ψ) * (T + cellRad Ψ) ^ (k - 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg hωnn (Nat.cast_nonneg k)) (by linarith)) hpow
  -- the raw layer inclusion
  have hsub : ∀ x : EuclideanSpace ℝ (Fin k), x ∈ layer (Kt a b c d T) (cellRad Ψ) →
      (T - 3 * cellRad Ψ < ‖x‖ ∧ ‖x‖ ≤ T + cellRad Ψ)
        ∨ (c < ‖a‖ ∧ x ∈ coneTube a c (T + cellRad Ψ) (3 * cellRad Ψ))
        ∨ (d < ‖b‖ ∧ x ∈ coneTube b d (T + cellRad Ψ) (3 * cellRad Ψ)) := by
    intro x hx
    obtain ⟨h1, h2⟩ := layer_subset_coneTube k a b c d T (cellRad Ψ) hx
    rcases h2 with h2 | ⟨h2, h3⟩ | ⟨h2, h3⟩
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (Or.inl ⟨h2, h3⟩)
    · exact Or.inr (Or.inr ⟨h2, h3⟩)
  by_cases hRA : 2 * cellRad Ψ ≤ T
  · -- Case A: `2R ≤ T`
    have h3RS : 3 * cellRad Ψ ≤ T + cellRad Ψ := by linarith
    have hr3 : 0 ≤ 3 * cellRad Ψ := by linarith
    have hS1 : 1 ≤ T + cellRad Ψ := by linarith
    -- inclusion of the layer in shell ∪ tubes (the tubes only when genuinely needed)
    have hsub_all : layer (Kt a b c d T) (cellRad Ψ) ⊆
        {x : EuclideanSpace ℝ (Fin k) | T - 3 * cellRad Ψ < ‖x‖ ∧ ‖x‖ ≤ T + cellRad Ψ}
          ∪ coneTube a c (T + cellRad Ψ) (3 * cellRad Ψ)
          ∪ coneTube b d (T + cellRad Ψ) (3 * cellRad Ψ) := by
      intro x hx
      rcases hsub x hx with h | ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    have hsub_a (hdb : ¬ d < ‖b‖) : layer (Kt a b c d T) (cellRad Ψ) ⊆
        {x : EuclideanSpace ℝ (Fin k) | T - 3 * cellRad Ψ < ‖x‖ ∧ ‖x‖ ≤ T + cellRad Ψ}
          ∪ coneTube a c (T + cellRad Ψ) (3 * cellRad Ψ) := by
      intro x hx
      rcases hsub x hx with h | ⟨-, h⟩ | ⟨hd', -⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd hd' hdb
    have hsub_shell (hca : ¬ c < ‖a‖) (hdb : ¬ d < ‖b‖) :
        layer (Kt a b c d T) (cellRad Ψ) ⊆
          {x : EuclideanSpace ℝ (Fin k) | T - 3 * cellRad Ψ < ‖x‖ ∧ ‖x‖ ≤ T + cellRad Ψ} := by
      intro x hx
      rcases hsub x hx with h | ⟨hc', -⟩ | ⟨hd', -⟩
      · exact h
      · exact absurd hc' hca
      · exact absurd hd' hdb
    have htube_a (hca : c < ‖a‖) : volume (coneTube a c (T + cellRad Ψ) (3 * cellRad Ψ))
        ≤ ENNReal.ofReal (Ct * (3 * cellRad Ψ) * (T + cellRad Ψ) ^ (k - 1)) :=
      hCt a c (T + cellRad Ψ) (3 * cellRad Ψ) hc hca hr3 h3RS hS1
    have htube_b (hdb : d < ‖b‖) : volume (coneTube b d (T + cellRad Ψ) (3 * cellRad Ψ))
        ≤ ENNReal.ofReal (Ct * (3 * cellRad Ψ) * (T + cellRad Ψ) ^ (k - 1)) :=
      hCt b d (T + cellRad Ψ) (3 * cellRad Ψ) hd hdb hr3 h3RS hS1
    -- the volume of the shell
    have hshell : volume {x : EuclideanSpace ℝ (Fin k) |
          T - 3 * cellRad Ψ < ‖x‖ ∧ ‖x‖ ≤ T + cellRad Ψ}
        ≤ ENNReal.ofReal (unitBallVolume k * (k : ℝ) * (4 * cellRad Ψ)
            * (T + cellRad Ψ) ^ (k - 1)) := by
      have hA : 0 ≤ max 0 (T - 3 * cellRad Ψ) := le_max_left _ _
      have hsubS : {x : EuclideanSpace ℝ (Fin k) |
            T - 3 * cellRad Ψ < ‖x‖ ∧ ‖x‖ ≤ T + cellRad Ψ}
          ⊆ {v : EuclideanSpace ℝ (Fin k) |
              max 0 (T - 3 * cellRad Ψ) ≤ ‖v‖ ∧ ‖v‖ ≤ T + cellRad Ψ} := by
        rintro x ⟨hx1, hx2⟩
        exact ⟨max_le (norm_nonneg x) hx1.le, hx2⟩
      have h := volume_shell_le (V := EuclideanSpace ℝ (Fin k)) k
        (by rw [finrank_euclideanSpace, Fintype.card_fin]) hk
        (max 0 (T - 3 * cellRad Ψ)) (T + cellRad Ψ) hA hSn
      refine le_trans (measure_mono hsubS) (le_trans h (ENNReal.ofReal_le_ofReal ?_))
      have hmax : max 0 (T + cellRad Ψ - max 0 (T - 3 * cellRad Ψ)) ≤ 4 * cellRad Ψ := by
        refine max_le (by linarith) ?_
        have hle := le_max_right (0 : ℝ) (T - 3 * cellRad Ψ)
        have := sub_le_sub_left hle (T + cellRad Ψ)
        linarith
      have hnn1 : 0 ≤ unitBallVolume k * (k : ℝ) :=
        mul_nonneg hωnn (Nat.cast_nonneg k)
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax hnn1) hpow
      rw [unitBallVolume]
      exact this
    -- the four sub-cases
    by_cases hca : c < ‖a‖ <;> by_cases hdb : d < ‖b‖
    · have hvol : volume (layer (Kt a b c d T) (cellRad Ψ)) ≤
          volume {x : EuclideanSpace ℝ (Fin k) |
              T - 3 * cellRad Ψ < ‖x‖ ∧ ‖x‖ ≤ T + cellRad Ψ}
            + volume (coneTube a c (T + cellRad Ψ) (3 * cellRad Ψ))
            + volume (coneTube b d (T + cellRad Ψ) (3 * cellRad Ψ)) := by
        calc volume (layer (Kt a b c d T) (cellRad Ψ))
            ≤ volume ({x : EuclideanSpace ℝ (Fin k) |
                  T - 3 * cellRad Ψ < ‖x‖ ∧ ‖x‖ ≤ T + cellRad Ψ}
                ∪ coneTube a c (T + cellRad Ψ) (3 * cellRad Ψ)
                ∪ coneTube b d (T + cellRad Ψ) (3 * cellRad Ψ)) := measure_mono hsub_all
          _ ≤ volume ({x : EuclideanSpace ℝ (Fin k) |
                  T - 3 * cellRad Ψ < ‖x‖ ∧ ‖x‖ ≤ T + cellRad Ψ}
                ∪ coneTube a c (T + cellRad Ψ) (3 * cellRad Ψ))
                + volume (coneTube b d (T + cellRad Ψ) (3 * cellRad Ψ)) := measure_union_le _ _
          _ ≤ (volume {x : EuclideanSpace ℝ (Fin k) |
                  T - 3 * cellRad Ψ < ‖x‖ ∧ ‖x‖ ≤ T + cellRad Ψ}
                + volume (coneTube a c (T + cellRad Ψ) (3 * cellRad Ψ)))
                + volume (coneTube b d (T + cellRad Ψ) (3 * cellRad Ψ)) := by
              gcongr
              exact measure_union_le _ _
      have hsum : (volume {x : EuclideanSpace ℝ (Fin k) |
              T - 3 * cellRad Ψ < ‖x‖ ∧ ‖x‖ ≤ T + cellRad Ψ}
            + volume (coneTube a c (T + cellRad Ψ) (3 * cellRad Ψ)))
            + volume (coneTube b d (T + cellRad Ψ) (3 * cellRad Ψ))
          ≤ (ENNReal.ofReal (unitBallVolume k * (k : ℝ) * (4 * cellRad Ψ)
                * (T + cellRad Ψ) ^ (k - 1))
              + ENNReal.ofReal (Ct * (3 * cellRad Ψ) * (T + cellRad Ψ) ^ (k - 1)))
            + ENNReal.ofReal (Ct * (3 * cellRad Ψ) * (T + cellRad Ψ) ^ (k - 1)) :=
        add_le_add (add_le_add hshell (htube_a hca)) (htube_b hdb)
      refine le_trans hvol (le_trans hsum (ofReal_add3_le hshellnn htubenn htubenn
        (arith_caseA hωnn hCtpos.le hRnn hSn rfl le_rfl le_rfl)))
    · have hvol : volume (layer (Kt a b c d T) (cellRad Ψ)) ≤
          volume {x : EuclideanSpace ℝ (Fin k) |
              T - 3 * cellRad Ψ < ‖x‖ ∧ ‖x‖ ≤ T + cellRad Ψ}
            + volume (coneTube a c (T + cellRad Ψ) (3 * cellRad Ψ)) := by
        calc volume (layer (Kt a b c d T) (cellRad Ψ))
            ≤ volume ({x : EuclideanSpace ℝ (Fin k) |
                  T - 3 * cellRad Ψ < ‖x‖ ∧ ‖x‖ ≤ T + cellRad Ψ}
                ∪ coneTube a c (T + cellRad Ψ) (3 * cellRad Ψ)) := measure_mono (hsub_a hdb)
          _ ≤ volume {x : EuclideanSpace ℝ (Fin k) |
                  T - 3 * cellRad Ψ < ‖x‖ ∧ ‖x‖ ≤ T + cellRad Ψ}
                + volume (coneTube a c (T + cellRad Ψ) (3 * cellRad Ψ)) := measure_union_le _ _
      have hsum : volume {x : EuclideanSpace ℝ (Fin k) |
              T - 3 * cellRad Ψ < ‖x‖ ∧ ‖x‖ ≤ T + cellRad Ψ}
            + volume (coneTube a c (T + cellRad Ψ) (3 * cellRad Ψ))
          ≤ ENNReal.ofReal (unitBallVolume k * (k : ℝ) * (4 * cellRad Ψ)
                * (T + cellRad Ψ) ^ (k - 1))
              + ENNReal.ofReal (Ct * (3 * cellRad Ψ) * (T + cellRad Ψ) ^ (k - 1)) :=
        add_le_add hshell (htube_a hca)
      refine le_trans hvol (le_trans hsum (ofReal_add2_le hshellnn htubenn ?_))
      simpa using arith_caseA
        (b2 := Ct * (3 * cellRad Ψ) * (T + cellRad Ψ) ^ (k - 1)) (b3 := 0)
        hωnn hCtpos.le hRnn hSn rfl le_rfl htubenn
    · have hvol : volume (layer (Kt a b c d T) (cellRad Ψ)) ≤
          volume {x : EuclideanSpace ℝ (Fin k) |
              T - 3 * cellRad Ψ < ‖x‖ ∧ ‖x‖ ≤ T + cellRad Ψ}
            + volume (coneTube b d (T + cellRad Ψ) (3 * cellRad Ψ)) := by
        have hsubset : layer (Kt a b c d T) (cellRad Ψ) ⊆
            {x : EuclideanSpace ℝ (Fin k) | T - 3 * cellRad Ψ < ‖x‖ ∧ ‖x‖ ≤ T + cellRad Ψ}
              ∪ coneTube b d (T + cellRad Ψ) (3 * cellRad Ψ) := by
          intro x hx
          rcases hsub x hx with h | ⟨hc', -⟩ | ⟨-, h⟩
          · exact Or.inl h
          · exact absurd hc' hca
          · exact Or.inr h
        calc volume (layer (Kt a b c d T) (cellRad Ψ))
            ≤ volume ({x : EuclideanSpace ℝ (Fin k) |
                  T - 3 * cellRad Ψ < ‖x‖ ∧ ‖x‖ ≤ T + cellRad Ψ}
                ∪ coneTube b d (T + cellRad Ψ) (3 * cellRad Ψ)) := measure_mono hsubset
          _ ≤ volume {x : EuclideanSpace ℝ (Fin k) |
                  T - 3 * cellRad Ψ < ‖x‖ ∧ ‖x‖ ≤ T + cellRad Ψ}
                + volume (coneTube b d (T + cellRad Ψ) (3 * cellRad Ψ)) := measure_union_le _ _
      have hsum : volume {x : EuclideanSpace ℝ (Fin k) |
              T - 3 * cellRad Ψ < ‖x‖ ∧ ‖x‖ ≤ T + cellRad Ψ}
            + volume (coneTube b d (T + cellRad Ψ) (3 * cellRad Ψ))
          ≤ ENNReal.ofReal (unitBallVolume k * (k : ℝ) * (4 * cellRad Ψ)
                * (T + cellRad Ψ) ^ (k - 1))
              + ENNReal.ofReal (Ct * (3 * cellRad Ψ) * (T + cellRad Ψ) ^ (k - 1)) :=
        add_le_add hshell (htube_b hdb)
      refine le_trans hvol (le_trans hsum (ofReal_add2_le hshellnn htubenn ?_))
      simpa using arith_caseA
        (b2 := Ct * (3 * cellRad Ψ) * (T + cellRad Ψ) ^ (k - 1)) (b3 := 0)
        hωnn hCtpos.le hRnn hSn rfl le_rfl htubenn
    · refine le_trans (measure_mono (hsub_shell hca hdb)) ?_
      refine le_trans hshell (ENNReal.ofReal_le_ofReal ?_)
      have h := arith_caseA (b1 := unitBallVolume k * (k : ℝ) * (4 * cellRad Ψ)
          * (T + cellRad Ψ) ^ (k - 1)) (b2 := 0) (b3 := 0)
        hωnn hCtpos.le hRnn hSn rfl htubenn htubenn
      simpa using h
  · -- Case B: `T < 2R`
    push Not at hRA
    have hS3R : T + cellRad Ψ ≤ 3 * cellRad Ψ := by linarith
    have hsubB : layer (Kt a b c d T) (cellRad Ψ) ⊆
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) (T + cellRad Ψ) := by
      intro x hx
      rcases hsub x hx with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
      · simpa using h
      · simpa using h.1
      · simpa using h.1
    have hball : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) (T + cellRad Ψ))
        = ENNReal.ofReal (unitBallVolume k * (T + cellRad Ψ) ^ k) := by
      have hne : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) (T + cellRad Ψ)) ≠ ⊤ :=
        measure_closedBall_lt_top.ne
      have h1 : (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k))
            (T + cellRad Ψ))).toReal = unitBallVolume k * (T + cellRad Ψ) ^ k := by
        rw [← measureReal_def, Measure.addHaar_real_closedBall volume 0 hSn,
          finrank_euclideanSpace, Fintype.card_fin, unitBallVolume]
        ring
      rw [← ENNReal.ofReal_toReal hne, h1]
    refine le_trans (measure_mono hsubB) (le_trans (le_of_eq hball) (ENNReal.ofReal_le_ofReal ?_))
    refine arith_caseB hk hωnn hRnn hSn hS3R ?_
    have h1 : 0 ≤ 4 * (k : ℝ) * unitBallVolume k :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg k)) hωnn
    have h2 : 0 ≤ 6 * Ct := mul_nonneg (by norm_num) hCtpos.le
    have h3 : 0 ≤ 1 := by norm_num
    linarith

/-! ## The lattice point count -/

-- Lattice point counting in a two-cone slice of a ball, in coordinates.
-- See the module docstring of the original statement: `count_from_layer` reduces the count to a
-- bound on the volume of the boundary layer, `layer_volume_le` supplies that bound, and
-- `Kt_volume_smul` identifies the main term `T^k * vol (K_1)`.
theorem cone_count_core (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ψ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)),
      Function.Injective Ψ → ∀ (a b : EuclideanSpace ℝ (Fin k)) (c d T : ℝ),
      0 ≤ c → 0 ≤ d → 1 ≤ T →
      |((({y : EuclideanSpace ℝ (Fin k) | y ∈ Work.HP.BCS.latImage Ψ ∧
            y ∈ Work.HP.BCS.coneSet a c ∧ y ∈ Work.HP.BCS.coneSet b d ∧ ‖y‖ ≤ T}).ncard : ℝ) -
          T ^ k * (MeasureTheory.volume {y : EuclideanSpace ℝ (Fin k) |
              y ∈ Work.HP.BCS.coneSet a c ∧ y ∈ Work.HP.BCS.coneSet b d ∧ ‖y‖ ≤ 1}).toReal
            / Ψ.normDet)|
        ≤ C * (T + Work.HP.BCS.cellRad Ψ) ^ (k - 1) * Work.HP.BCS.cellRad Ψ / Ψ.normDet := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := count_from_layer k hk
  obtain ⟨C₂, hC₂pos, hC₂⟩ := layer_volume_le k hk
  refine ⟨C₁ * C₂, by positivity, ?_⟩
  intro Ψ hΨ a b c d T hc hd hT
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT
  have hRnn : 0 ≤ cellRad Ψ := cellRad_nonneg Ψ
  have hMnn : 0 ≤ C₂ * (T + cellRad Ψ) ^ (k - 1) * cellRad Ψ :=
    mul_nonneg (mul_nonneg hC₂pos.le (pow_nonneg (by linarith) _)) hRnn
  have hfin : (latImage Ψ ∩ Kt a b c d T).Finite := by
    refine (latImage_inter_ball_finite k Ψ hΨ T).subset ?_
    intro y hy
    exact ⟨hy.1, (mem_Kt.mp hy.2).2.2⟩
  have hKne : volume (Kt a b c d T) ≠ ⊤ := by
    refine ne_top_of_le_ne_top
      (measure_closedBall_lt_top (x := (0 : EuclideanSpace ℝ (Fin k))) (r := T)).ne
      (measure_mono ?_)
    intro y hy
    simpa using (mem_Kt.mp hy).2.2
  have hlayer : volume (layer (Kt a b c d T) (cellRad Ψ))
      ≤ ENNReal.ofReal (C₂ * (T + cellRad Ψ) ^ (k - 1) * cellRad Ψ) :=
    hC₂ Ψ a b c d T hc hd hT
  have hmain := hC₁ Ψ hΨ (Kt a b c d T) (cellRad Ψ)
      (C₂ * (T + cellRad Ψ) ^ (k - 1) * cellRad Ψ) hRnn hMnn le_rfl hfin hKne hlayer
  rw [Kt_volume_smul k a b c d T hTpos] at hmain
  have hset : {y : EuclideanSpace ℝ (Fin k) | y ∈ Work.HP.BCS.latImage Ψ ∧
      y ∈ Work.HP.BCS.coneSet a c ∧ y ∈ Work.HP.BCS.coneSet b d ∧ ‖y‖ ≤ T}
      = latImage Ψ ∩ Kt a b c d T := rfl
  have hvol1 : {y : EuclideanSpace ℝ (Fin k) |
      y ∈ Work.HP.BCS.coneSet a c ∧ y ∈ Work.HP.BCS.coneSet b d ∧ ‖y‖ ≤ 1}
      = Kt a b c d 1 := rfl
  rw [hset, hvol1]
  refine le_trans hmain (le_of_eq ?_)
  ring

end Work.HP.BCS
