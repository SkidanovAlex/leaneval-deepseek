import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.ChiSmallWallis.cos_pi_mul_interval_eq
import Submission.Work.ChiSmallWallis.cos_pow_half_pi_interval
import Submission.Work.ChiSmallWallis.zeta1d_pow_eq_cos_interval
import Submission.Work.SmallBoxTBWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `L²`-normalisation of the cosine-`M` bump: `∫χ_M² = (C(2M,M)/4^M)³`

FS `final_v2.tex` §SmallBoxes normalises the three-factor cosine bump
`χ_M(x) = (ζ(x₁)ζ(x₂)ζ(x₃))^M / √(∫(ζζζ)^{2M})`.  This file computes its
normalisation integral `chiSmallNormSq M = ∫_{ℝ³} (chiSmallBase M)²` in closed
form:

    chiSmallNormSq M = ((Nat.choose (2*M) M : ℝ) / 4^M)^3 .

The proof splits into two independent halves.

**Fubini half** (`chiSmallNormSq_eq_cube_zeta1d_integral`): the three-factor
integrand is a product of one-coordinate functions, so the `ℝ³`-integral is the
cube of the one-dimensional integral `∫_ℝ ζ^{2M}`; the change of variables
`ℝ³ ≅ (Fin 3 → ℝ)` is the volume-preserving `WithLp` equivalence.

**One-dimensional half** (`zeta1d_pow_two_mul_integral_eq_choose`): on its
support `ζ` is `cos (π ·)` and vanishes elsewhere, so

    ∫_ℝ ζ^{2M} = ∫_{-1/2}^{1/2} cos(πx)^{2M} dx = 2π⁻¹ ∫_0^{π/2} cos^{2M}
                = 2π⁻¹ · (π/2) · ∏_{i<M} (2i+1)/(2i+2)
                = ∏_{i<M} (2i+1)/(2i+2) = C(2M,M)/4^M ,

the middle identities being the change of variables `t = πx`, the evenness of
`cos^{2M}` and the Wallis cosine integral `EulerSine.integral_cos_pow_eq`; the
last is the elementary product identity `prod_range_two_mul_add_one_div_eq_choose`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.SmallBoxTBWord

set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The Wallis product `∏_{i<M} (2i+1)/(2i+2)` equals the normalised central
binomial coefficient `C(2M,M)/4^M`. -/
lemma prod_range_two_mul_add_one_div_eq_choose (M : ℕ) :
    (∏ i ∈ Finset.range M, (2 * (i:ℝ) + 1) / (2 * i + 2))
      = (Nat.choose (2*M) M : ℝ) / 4^M := by
  induction M with
  | zero => simp
  | succ n ih =>
    -- the induction step is the central-binomial recurrence
    -- `(n+1) * C(2n+2,n+1) = 2*(2n+1)*C(2n,n)`
    have hrec : (Nat.choose (2*n+2) (n+1) : ℝ) / 4^(n+1)
        = ((Nat.choose (2*n) n : ℝ) / 4^n) * ((2*(n:ℝ)+1)/(2*(n:ℝ)+2)) := by
      have h := Nat.succ_mul_centralBinom_succ n
      rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
      have h2 : (2*(n+1) : ℕ) = 2*n+2 := by ring
      rw [h2] at h
      have hR : ((n:ℝ)+1) * (Nat.choose (2*n+2) (n+1) : ℝ)
          = 2 * (2*(n:ℝ)+1) * (Nat.choose (2*n) n : ℝ) := by
        exact_mod_cast h
      have hkey : 2 * (Nat.choose (2*n+2) (n+1) : ℝ) * ((n:ℝ)+1)
          = 4 * (Nat.choose (2*n) n : ℝ) * (2*(n:ℝ)+1) := by
        linear_combination 2 * hR
      rw [show (4:ℝ)^(n+1) = 4 * 4^n by rw [pow_succ]; ring,
          div_mul_div_comm, show (2 * (n:ℝ) + 2) = 2 * ((n:ℝ)+1) by ring]
      rw [div_eq_div_iff (by positivity) (by positivity)]
      linear_combination (4^n) * hkey
    rw [Finset.prod_range_succ, ih]
    rw [show 2 * (n + 1) = 2 * n + 2 by ring]
    exact hrec.symm

/-- **Fubini factorization** of the normalisation integral: the `ℝ³`-integral of
the squared three-factor bump is the cube of the one-dimensional integral of
`ζ^{2M}`. -/
lemma chiSmallNormSq_eq_cube_zeta1d_integral (M : ℕ) :
    Submission.BoseGases.chiSmallNormSq M
      = (∫ y : ℝ, Submission.BoseGases.zeta1d y ^ (2*M))^3 := by
  unfold Submission.BoseGases.chiSmallNormSq
  have hmp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) volume volume :=
    PiLp.volume_preserving_toLp (Fin 3)
  rw [← hmp.integral_comp' (fun z : ℝ³ => (Submission.BoseGases.chiSmallBase M z)^2)]
  simp only [MeasurableEquiv.coe_toLp]
  have hpt : ∀ w : Fin 3 → ℝ, (Submission.BoseGases.chiSmallBase M (WithLp.toLp 2 w))^2
      = ∏ j : Fin 3, Submission.BoseGases.zeta1d (w j) ^ (2*M) := by
    intro w
    have h1 : Submission.BoseGases.chiSmallBase M (WithLp.toLp 2 w)
        = (∏ j : Fin 3, Submission.BoseGases.zeta1d (w j))^M := by
      rw [Submission.BoseGases.chiSmallBase, Fin.prod_univ_three]
    rw [h1, ← pow_mul, show M * 2 = 2 * M by ring, ← Finset.prod_pow]
  simp_rw [hpt]
  rw [MeasureTheory.integral_fintype_prod_volume_eq_pow
        (f := fun y : ℝ => Submission.BoseGases.zeta1d y ^ (2*M))]
  norm_num

/-- The one-dimensional integral `∫_ℝ ζ^{2M}` in closed form. -/
lemma zeta1d_pow_two_mul_integral_eq_choose (M : ℕ) (hM : 1 ≤ M) :
    ∫ y : ℝ, Submission.BoseGases.zeta1d y ^ (2*M)
      = (Nat.choose (2*M) M : ℝ) / 4^M := by
  calc ∫ y : ℝ, Submission.BoseGases.zeta1d y ^ (2*M)
      = ∫ x in (-(1/2):ℝ)..(1/2), Real.cos (Real.pi * x) ^ (2*M) :=
        Work.ChiSmallWallis.zeta1d_pow_eq_cos_interval M hM
    _ = 2 * Real.pi⁻¹ * ∫ x in (0:ℝ)..(Real.pi/2), Real.cos x ^ (2*M) :=
        Work.ChiSmallWallis.cos_pi_mul_interval_eq M
    _ = 2 * Real.pi⁻¹ * (Real.pi/2 * ∏ i ∈ Finset.range M, (2*(i:ℝ)+1)/(2*i+2)) := by
        rw [Work.ChiSmallWallis.cos_pow_half_pi_interval M]
    _ = 2 * Real.pi⁻¹ * (Real.pi/2 * ((Nat.choose (2*M) M : ℝ)/4^M)) := by
        rw [prod_range_two_mul_add_one_div_eq_choose M]
    _ = (Nat.choose (2*M) M : ℝ) / 4^M := by field_simp

theorem chiSmallNormSq_eq_choose (M : ℕ) (hM : 1 ≤ M) : Submission.BoseGases.chiSmallNormSq M = ((Nat.choose (2 * M) M : ℝ) / 4 ^ M) ^ 3 := by
  rw [chiSmallNormSq_eq_cube_zeta1d_integral M, zeta1d_pow_two_mul_integral_eq_choose M hM]

end Work.SmallBoxTBWord
