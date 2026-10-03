import Mathlib
import Submission.Work.KMTPlan.A6.BilinearAverageLqUniform
import Submission.Work.KMTPlan.A6.exists_interp_theta
import Submission.Work.KMTPlan.A6.bileInterpIw

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6

set_option maxHeartbeats 1000000

open Work.Analysis.Concentration (LpNormZMod polyBilinearAverageZMod)

theorem MdlBileOfR1 (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (havg : ∀ (q : ℝ), 1 ≤ q → q < 2 * (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1) →
      ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℕ) [NeZero Q] (f g : ZMod Q → ℂ),
        Work.Analysis.Concentration.LpNormZMod Q q
            (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f g)
          ≤ C * Work.Analysis.Concentration.LpNormZMod Q 2 f *
              Work.Analysis.Concentration.LpNormZMod Q 2 g)
    (hI : Work.KMTContract.ImprovKMT P) (r : ℝ) (hr : 2 ≤ r)
    (hrd : r < 2 * (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1)) :
    ∃ c : ℝ, 0 < c ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, 0 < C ∧
      ∀ (Q : ℕ) [NeZero Q] (l : ℕ) (f g : ZMod Q → ℂ),
        (Work.KMTPlan.A6.MdlIwMinorArc ρ l Q f ∨ Work.KMTPlan.A6.MdlIwMinorArc ρ l Q g) →
        Work.Analysis.Concentration.LpNormZMod Q r
            (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f g)
          ≤ C * (2 : ℝ) ^ (-(c * (l : ℝ))) *
              Work.Analysis.Concentration.LpNormZMod Q 2 f *
              Work.Analysis.Concentration.LpNormZMod Q 2 g := by

  -- The two inputs: the `L¹` estimate with gain `2^{-c₁·l}` under the Ionescu--Wainger
  -- minor-arc hypothesis (`MdlBileR1OfImprov`), and the unconditional `L^q` estimate for
  -- `1 ≤ q < 2d/(d-1)` (`havg`, the paper's (avg-1)), both uniform in the modulus `Q`.
  obtain ⟨c₁, hc₁, hbile1⟩ := MdlBileR1OfImprov P hd hI
  have hdR : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
  -- Interpolation data: an intermediate exponent `q₀ ∈ (r, 2d/(d-1))` and the weight `θ`.
  obtain ⟨q₀, θ, -, hqM, hq1, hθpos, hθle, hrel⟩ :=
    exists_interp_theta (d := (P.natDegree : ℝ)) hdR hr hrd
  refine ⟨c₁ * θ, mul_pos hc₁ hθpos, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨C₁, hC₁pos, hC₁⟩ := hbile1 ρ hρ hρ1
  obtain ⟨C₂, hC₂pos, hC₂⟩ := havg q₀ hq1.le hqM
  refine ⟨C₁ ^ θ * C₂ ^ (1 - θ),
    mul_pos (Real.rpow_pos_of_pos hC₁pos θ) (Real.rpow_pos_of_pos hC₂pos (1 - θ)), ?_⟩
  intro Q hNZ l f g hm
  -- the two endpoint estimates at this `(Q, l)`
  have h1 : ∀ f' g' : ZMod Q → ℂ,
      (MdlIwMinorArc ρ l Q f' ∨ MdlIwMinorArc ρ l Q g') →
      LpNormZMod Q 1 (polyBilinearAverageZMod Polynomial.X P Q f' g') ≤
        (C₁ * (2 : ℝ) ^ (-(c₁ * (l : ℝ)))) * LpNormZMod Q 2 f' * LpNormZMod Q 2 g' :=
    fun f' g' h => hC₁ Q l f' g' h
  have h2 : ∀ f' g' : ZMod Q → ℂ,
      LpNormZMod Q q₀ (polyBilinearAverageZMod Polynomial.X P Q f' g') ≤
        C₂ * LpNormZMod Q 2 f' * LpNormZMod Q 2 g' :=
    fun f' g' => hC₂ Q f' g'
  have hεpos : (0 : ℝ) ≤ C₁ * (2 : ℝ) ^ (-(c₁ * (l : ℝ))) :=
    mul_nonneg (le_of_lt hC₁pos)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(c₁ * (l : ℝ))))
  -- log-convexity of the `Lᵖ` norms interpolates the two endpoint estimates at `r`
  have hmain := bileInterpIw (P := P) (Q := Q) (ρ := ρ) (l := l) (q₀ := q₀) (r := r)
    (θ := θ) (ε := C₁ * (2 : ℝ) ^ (-(c₁ * (l : ℝ)))) (C := C₂)
    hq1 hθpos.le hθle hrel hεpos hC₂pos.le h1 h2 f g hm
  -- the gain bookkeeping `(C₁ · 2^{-c₁l})^θ = C₁^θ · 2^{-(c₁θ)l}`
  have hεθ : (C₁ * (2 : ℝ) ^ (-(c₁ * (l : ℝ)))) ^ θ
      = C₁ ^ θ * (2 : ℝ) ^ (-((c₁ * θ) * (l : ℝ))) := by
    rw [Real.mul_rpow (le_of_lt hC₁pos)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(c₁ * (l : ℝ)))),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      show -(c₁ * (l : ℝ)) * θ = -((c₁ * θ) * (l : ℝ)) from by ring]
  calc LpNormZMod Q r (polyBilinearAverageZMod Polynomial.X P Q f g)
      ≤ (C₁ * (2 : ℝ) ^ (-(c₁ * (l : ℝ)))) ^ θ * C₂ ^ (1 - θ) *
          (LpNormZMod Q 2 f * LpNormZMod Q 2 g) := by
        simpa only [mul_assoc] using hmain
    _ = (C₁ ^ θ * C₂ ^ (1 - θ)) * (2 : ℝ) ^ (-((c₁ * θ) * (l : ℝ))) *
          (LpNormZMod Q 2 f * LpNormZMod Q 2 g) := by
        rw [hεθ]; ac_rfl
    _ = (C₁ ^ θ * C₂ ^ (1 - θ)) * (2 : ℝ) ^ (-((c₁ * θ) * (l : ℝ))) *
          LpNormZMod Q 2 f * LpNormZMod Q 2 g := by ac_rfl


end Work.KMTPlan.A6
