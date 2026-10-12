import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseBogFS.BogFSCompare
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The real-part bound behind `chat`: `|Ŵ(k)| ≤ ‖𝓕 W k‖`. -/
private lemma abs_chat_le_kinFT_norm (W : E3 → ℝ) (k : E3) :
    |Work.BoseFixR.chat W k|
      ≤ ‖Submission.BoseGases.kinFT (fun y : E3 => ((W y : ℝ) : ℂ)) k‖ := by
  rw [Work.BoseFixR.chat]
  exact Complex.abs_re_le_norm _

/-- `√P • t` has norm `√P ‖t‖`. -/
private lemma norm_sqrt_smul (P : ℝ) (t : E3) :
    ‖Real.sqrt P • t‖ = Real.sqrt P * ‖t‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg P)]

theorem betaSc_decay :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R ρ μ : ℝ},
      0 < R → 0 < ρ → 0 < _root_.BoseGases.a v → (∀ x, 0 ≤ v x) →
      _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R →
      R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0 →
      ∀ t : EuclideanSpace ℝ (Fin 3),
        |Work.BoseBogFS.betaSc v h ρ μ t|
          ≤ K * (1 + R) ^ 3
            / (_root_.BoseGases.a v
                * (1 + Real.sqrt (ρ * _root_.BoseGases.a v) * ‖t‖)) := by
  obtain ⟨K, hK0, hK⟩ := W1funDecay_momentsAbs
  refine ⟨K, hK0, ?_⟩
  intro v h R ρ μ hR hρ hav hv hvrad hv_supp hRℓ t
  -- the box scale is positive: `R > 0` and `R ≤ ℓ·chiR0`
  have hchi : 0 < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
  have hℓ : 0 < Work.BoseFixR.ell v μ := by
    by_contra hcon
    have hcon' : Work.BoseFixR.ell v μ ≤ 0 := le_of_not_gt hcon
    have h2 : Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcon' (le_of_lt hchi)
    linarith
  -- the Fourier decay of `Ŵ₁` at `q = √(ρ a) • t`, from the moment bound on `W₁`
  have hb := hK (v := v) (h := h) (R := R) (ℓ := Work.BoseFixR.ell v μ)
    hR hℓ hv hvrad hv_supp hRℓ 0 (by norm_num) (0 : Fin 3)
    (Real.sqrt (ρ * _root_.BoseGases.a v) • t)
  have hb' : ‖Submission.BoseGases.kinFT
      (fun y : E3 => ((Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ) y : ℝ) : ℂ))
      (Real.sqrt (ρ * _root_.BoseGases.a v) • t)‖
      ≤ K * (1 + R) ^ 3 / (1 + ‖Real.sqrt (ρ * _root_.BoseGases.a v) • t‖) := by
    simpa using hb
  have hchat : |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
        (Real.sqrt (ρ * _root_.BoseGases.a v) • t)|
      ≤ K * (1 + R) ^ 3 / (1 + ‖Real.sqrt (ρ * _root_.BoseGases.a v) • t‖) :=
    le_trans (abs_chat_le_kinFT_norm (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) _) hb'
  have hqnorm : ‖Real.sqrt (ρ * _root_.BoseGases.a v) • t‖
      = Real.sqrt (ρ * _root_.BoseGases.a v) * ‖t‖ :=
    norm_sqrt_smul (ρ * _root_.BoseGases.a v) t
  rw [hqnorm] at hchat
  rw [betaSc_eq v hρ.ne' hav.ne' t, abs_mul, abs_inv, abs_of_pos hav]
  have hmain : (_root_.BoseGases.a v)⁻¹
        * |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
            (Real.sqrt (ρ * _root_.BoseGases.a v) • t)|
      ≤ (_root_.BoseGases.a v)⁻¹
        * (K * (1 + R) ^ 3 / (1 + Real.sqrt (ρ * _root_.BoseGases.a v) * ‖t‖)) :=
    mul_le_mul_of_nonneg_left hchat (inv_nonneg.mpr (le_of_lt hav))
  have heq : (_root_.BoseGases.a v)⁻¹
        * (K * (1 + R) ^ 3 / (1 + Real.sqrt (ρ * _root_.BoseGases.a v) * ‖t‖))
      = K * (1 + R) ^ 3
        / (_root_.BoseGases.a v * (1 + Real.sqrt (ρ * _root_.BoseGases.a v) * ‖t‖)) := by
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rwa [heq] at hmain

end Work.BoseBogFS
