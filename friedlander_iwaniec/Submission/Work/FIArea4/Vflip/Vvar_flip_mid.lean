import Mathlib
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIArea4.Evar_le_trivial
import Submission.Work.FIArea4.jacobi_congruence_count
import Submission.Work.FIArea4.polya_vinogradov
import Submission.Work.FIArea4.P13_sharp_evar
import Submission.Work.FIArea4.Vflip.vfm_plumbing
import Submission.Work.FIArea4.Vflip.Vflip_large_dyadic
import Submission.Work.FIArea4.Vflip.Vvar_le_of_mul_lt_D
import Submission.Work.FIArea4.Vflip.Vvar_strip_le
import Submission.Work.FIArea4.Vflip.p14T12_dyadic_sum_le

namespace Work.FIArea4.Vflip

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The range `D ^ 2 ≤ R * S`

For `D ≤ √(R S)` the sharp trivial local variance bound `P13_sharp_evar`,
`E(d) ≤ (4RS/d + 2√(RS) + 2)·Σ‖α‖²`, already suffices.  This is the first half of `Vvar_flip_mid`;
it is a self-contained (re-)proof of `Work.FIArea4.Vvar_flip_small`, kept local so that
`Vvar_flip_mid` does not have to import the module `Work.FIArea4.Vvar_flip_middle` (which imports
it). -/

/-- The harmonic sum over a dyadic range: `∑_{D < d ≤ 2D} 1/d ≤ 1`. -/
private lemma vfm_harmonic (D : ℕ) (hD : 0 < D) :
    (∑ d ∈ Finset.Ioc D (2*D), (d:ℝ)⁻¹) ≤ 1 := by
  have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD
  have hle : ∀ d ∈ Finset.Ioc D (2*D), (d:ℝ)⁻¹ ≤ (D:ℝ)⁻¹ := by
    intro d hd
    rw [Finset.mem_Ioc] at hd
    exact inv_anti₀ hDpos (by exact_mod_cast hd.1.le)
  have hcard : ((Finset.Ioc D (2*D)).card : ℝ) ≤ (D:ℝ) := by
    rw [Nat.card_Ioc]; exact_mod_cast (by omega : 2*D - D ≤ D)
  calc (∑ d ∈ Finset.Ioc D (2*D), (d:ℝ)⁻¹)
      ≤ ∑ _d ∈ Finset.Ioc D (2*D), (D:ℝ)⁻¹ := Finset.sum_le_sum hle
    _ = ((Finset.Ioc D (2*D)).card : ℝ) * (D:ℝ)⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (D:ℝ) * (D:ℝ)⁻¹ := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 1 := by rw [mul_inv_cancel₀ (ne_of_gt hDpos)]

/-- `p14L2 ≤ p14Ener`: the weight `τ(r) ≥ 1`. -/
private lemma vfm_L2_le_Ener (R S : ℕ) (α : ℕ → ℕ → ℂ) :
    p14L2 R S α ≤ p14Ener R S α := by
  unfold p14L2 p14Ener
  refine Finset.sum_le_sum (fun r hr => Finset.sum_le_sum (fun s hs => ?_))
  rw [Finset.mem_Icc] at hr
  have hcard : (1:ℝ) ≤ ((r.divisors.card : ℕ) : ℝ) := by
    have hr1 : r ≠ 0 := by omega
    have h1 : 1 ∈ r.divisors := by rw [Nat.mem_divisors]; exact ⟨one_dvd r, hr1⟩
    have : 1 ≤ r.divisors.card := Finset.card_pos.mpr ⟨1, h1⟩
    exact_mod_cast this
  nlinarith [Complex.normSq_nonneg (α r s)]

/-- The numerical core of the `D² ≤ RS` case: for `1 ≤ D, R, S` and `D² ≤ RS`,
`4·RS + (2√(RS)+2)·D ≤ 12·(bracket)`. -/
private lemma vfm_numerics_small (ε : ℝ) (hε : 0 < ε) (D R S : ℕ) (hD : 1 ≤ D) (hR : 1 ≤ R)
    (hS : 1 ≤ S) (hDSq : D * D ≤ R * S) :
    4 * (R:ℝ) * (S:ℝ) + (2*Real.sqrt ((R:ℝ)*(S:ℝ)) + 2)*(D:ℝ) ≤ 12 * p14T12 D R S ε := by
  have hDd : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hRd : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  have hSd : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
  have hT1 : (1:ℝ) ≤ (R:ℝ)*(S:ℝ) := by nlinarith
  have hT0 : (0:ℝ) < (R:ℝ)*(S:ℝ) := by linarith
  have hDsq : (D:ℝ)^2 ≤ (R:ℝ)*(S:ℝ) := by
    have h : ((D*D:ℕ):ℝ) ≤ ((R*S:ℕ):ℝ) := by exact_mod_cast hDSq
    push_cast at h; linarith
  have hsqrtT : (D:ℝ) ≤ Real.sqrt ((R:ℝ)*(S:ℝ)) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]; exact hDsq
  have hTpow : ((R:ℝ)*(S:ℝ))^((3:ℝ)/2) = ((R:ℝ)*(S:ℝ)) * Real.sqrt ((R:ℝ)*(S:ℝ)) := by
    rw [show (3:ℝ)/2 = 1 + 1/2 by norm_num, Real.rpow_add hT0, Real.rpow_one, Real.sqrt_eq_rpow]
  have hkey1 : (R:ℝ)*(S:ℝ) ≤ (D:ℝ)⁻¹ * ((R:ℝ)*(S:ℝ))^((3:ℝ)/2) * (((R:ℝ)*(S:ℝ))^ε) := by
    have hge : (R:ℝ)*(S:ℝ) ≤ (D:ℝ)⁻¹ * ((R:ℝ)*(S:ℝ))^((3:ℝ)/2) := by
      rw [hTpow, inv_mul_eq_div, le_div_iff₀ (by linarith : (0:ℝ) < (D:ℝ))]
      nlinarith [hsqrtT, Real.sqrt_nonneg ((R:ℝ)*(S:ℝ)), hT0]
    have hTe : (1:ℝ) ≤ ((R:ℝ)*(S:ℝ))^ε := Real.one_le_rpow hT1 hε.le
    calc (R:ℝ)*(S:ℝ) ≤ (D:ℝ)⁻¹ * ((R:ℝ)*(S:ℝ))^((3:ℝ)/2) := hge
      _ ≤ (D:ℝ)⁻¹ * ((R:ℝ)*(S:ℝ))^((3:ℝ)/2) * (((R:ℝ)*(S:ℝ))^ε) :=
          le_mul_of_one_le_right (by positivity) hTe
  have hp14 : (D:ℝ)⁻¹ * ((R:ℝ)*(S:ℝ))^((3:ℝ)/2) * (((R:ℝ)*(S:ℝ))^ε) ≤ p14T12 D R S ε := by
    unfold p14T12
    have hexp : ((D:ℝ)⁻¹*((R:ℝ)*(S:ℝ))^((3:ℝ)/2) + (R:ℝ)*(S:ℝ)^((3:ℝ)/4) + (S:ℝ)*(R:ℝ)^((3:ℝ)/4)) * (((R:ℝ)*(S:ℝ))^ε)
        = (D:ℝ)⁻¹*((R:ℝ)*(S:ℝ))^((3:ℝ)/2)*(((R:ℝ)*(S:ℝ))^ε) + ((R:ℝ)*(S:ℝ)^((3:ℝ)/4))*(((R:ℝ)*(S:ℝ))^ε) + ((S:ℝ)*(R:ℝ)^((3:ℝ)/4))*(((R:ℝ)*(S:ℝ))^ε) := by ring
    have hlog : (0:ℝ) ≤ Real.log (2 * (R:ℝ) * (S:ℝ)) := Real.log_nonneg (by nlinarith)
    have h0 : 0 ≤ (D:ℝ) + (D:ℝ)^((1:ℝ)/3)*((R:ℝ)*(S:ℝ))^((2:ℝ)/3)*(Real.log (2 * (R:ℝ) * (S:ℝ))+1)^4 := by positivity
    have h1 : 0 ≤ ((R:ℝ)*(S:ℝ)^((3:ℝ)/4))*(((R:ℝ)*(S:ℝ))^ε) := by positivity
    have h2 : 0 ≤ ((S:ℝ)*(R:ℝ)^((3:ℝ)/4))*(((R:ℝ)*(S:ℝ))^ε) := by positivity
    linarith [hexp, h0, h1, h2]
  have hTle : (R:ℝ)*(S:ℝ) ≤ p14T12 D R S ε := le_trans hkey1 hp14
  have hDleT : (D:ℝ) ≤ (R:ℝ)*(S:ℝ) := by nlinarith [hDd, hDsq]
  have hsT : (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)) ≤ (R:ℝ)*(S:ℝ) := by
    have h1 : Real.sqrt ((R:ℝ)*(S:ℝ)) * Real.sqrt ((R:ℝ)*(S:ℝ)) = (R:ℝ)*(S:ℝ) := Real.mul_self_sqrt (le_of_lt hT0)
    nlinarith [hsqrtT, Real.sqrt_nonneg ((R:ℝ)*(S:ℝ))]
  nlinarith [hTle, hDleT, hsT, hT1, hDd]

/-- **The `D² ≤ RS` half of `Vvar_flip_mid`.** -/
theorem Vvar_flip_small' (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      D * D ≤ R * S →
      Work.FIPlan.Vvar R S D α ≤ C * p14T12 D R S ε * p14Ener R S α := by
  refine ⟨12, by norm_num, ?_⟩
  intro D R S α hD hR hS hDSq
  have hL2nn : 0 ≤ p14L2 R S α := by
    unfold p14L2
    exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _))
  have hE : ∀ d ∈ Finset.Ioc D (2*D),
      Work.FIPlan.Evar R S d α
        ≤ (4 * (R:ℝ) * (S:ℝ) / (d:ℝ) + 2*Real.sqrt ((R:ℝ)*(S:ℝ)) + 2) * p14L2 R S α := by
    intro d hd
    rw [Finset.mem_Ioc] at hd
    have hd0 : 0 < d := lt_of_le_of_lt (Nat.zero_le D) hd.1
    exact P13_sharp_evar R S d α hd0
  have hV : Work.FIPlan.Vvar R S D α
      ≤ (∑ d ∈ Finset.Ioc D (2*D),
          (4 * (R:ℝ) * (S:ℝ) / (d:ℝ) + 2*Real.sqrt ((R:ℝ)*(S:ℝ)) + 2)) * p14L2 R S α := by
    rw [Work.FIPlan.Vvar]
    calc ∑ d ∈ Finset.Ioc D (2*D), Work.FIPlan.Evar R S d α
        ≤ ∑ d ∈ Finset.Ioc D (2*D),
            (4 * (R:ℝ) * (S:ℝ) / (d:ℝ) + 2*Real.sqrt ((R:ℝ)*(S:ℝ)) + 2) * p14L2 R S α :=
          Finset.sum_le_sum hE
      _ = (∑ d ∈ Finset.Ioc D (2*D),
            (4 * (R:ℝ) * (S:ℝ) / (d:ℝ) + 2*Real.sqrt ((R:ℝ)*(S:ℝ)) + 2)) * p14L2 R S α := by
          rw [Finset.sum_mul]
  have hsum : (∑ d ∈ Finset.Ioc D (2*D),
        (4 * (R:ℝ) * (S:ℝ) / (d:ℝ) + 2*Real.sqrt ((R:ℝ)*(S:ℝ)) + 2))
      ≤ 4 * (R:ℝ) * (S:ℝ) + (2*Real.sqrt ((R:ℝ)*(S:ℝ)) + 2)*(D:ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have h1 : (∑ d ∈ Finset.Ioc D (2*D), 4 * (R:ℝ) * (S:ℝ) / (d:ℝ))
        = 4 * (R:ℝ) * (S:ℝ) * (∑ d ∈ Finset.Ioc D (2*D), (d:ℝ)⁻¹) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun d _ => by rw [div_eq_mul_inv])
    have h2 : (∑ _d ∈ Finset.Ioc D (2*D), (2*Real.sqrt ((R:ℝ)*(S:ℝ))))
        = ((Finset.Ioc D (2*D)).card : ℝ) * (2*Real.sqrt ((R:ℝ)*(S:ℝ))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h3 : (∑ _d ∈ Finset.Ioc D (2*D), (2:ℝ))
        = ((Finset.Ioc D (2*D)).card : ℝ) * 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [h1, h2, h3]
    have hharm := vfm_harmonic D (by omega)
    have hcard : ((Finset.Ioc D (2*D)).card : ℝ) ≤ (D:ℝ) := by
      rw [Nat.card_Ioc]; exact_mod_cast (by omega : 2*D - D ≤ D)
    have h4 : 0 ≤ 4 * (R:ℝ) * (S:ℝ) := by positivity
    have h5 : 0 ≤ 2*Real.sqrt ((R:ℝ)*(S:ℝ)) := by positivity
    nlinarith [hharm, hcard, h4, h5]
  have hp14nn : 0 ≤ p14T12 D R S ε := by
    unfold p14T12
    have hRd : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    have hSd : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
    have hlog : (0:ℝ) ≤ Real.log (2 * (R:ℝ) * (S:ℝ)) := Real.log_nonneg (by nlinarith)
    positivity
  calc Work.FIPlan.Vvar R S D α
      ≤ (∑ d ∈ Finset.Ioc D (2*D),
          (4 * (R:ℝ) * (S:ℝ) / (d:ℝ) + 2*Real.sqrt ((R:ℝ)*(S:ℝ)) + 2)) * p14L2 R S α := hV
    _ ≤ (4 * (R:ℝ) * (S:ℝ) + (2*Real.sqrt ((R:ℝ)*(S:ℝ)) + 2)*(D:ℝ)) * p14L2 R S α :=
        mul_le_mul_of_nonneg_right hsum hL2nn
    _ ≤ (12 * p14T12 D R S ε) * p14L2 R S α :=
        mul_le_mul_of_nonneg_right (vfm_numerics_small ε hε D R S hD hR hS hDSq) hL2nn
    _ ≤ (12 * p14T12 D R S ε) * p14Ener R S α :=
        mul_le_mul_of_nonneg_left (vfm_L2_le_Ener R S α) (by nlinarith [hp14nn])
    _ = 12 * p14T12 D R S ε * p14Ener R S α := by ring

/-- **Friedlander–Iwaniec, Proposition 12.1** (the "flipping of moduli"), in the box form used
by the assembly of Proposition 14.1.

`Work.FIPlan.Vvar R S D α = Σ_{D<d≤2D} Σ_{a mod d} |Σ_{r̄s ≡ a (d)} α r s (r|d')|²` is the
Jacobi-twisted variance of FI §11 and `p14T12` is the bracket `L(D,R,S)` of FI (12.4).  The
hypothesis `(r,2s) = 1` on the support of `α` is the paper's (12.1).

The proof splits on the size of `D`: for `D² ≤ R·S` the sharp trivial local bound
`P13_sharp_evar` already suffices (`Work.FIArea4.Vflip.Vvar_flip_small'`, which needs neither
`h11` nor the coprimality), while for `R·S < D·D` (with `D ≤ R·S`) it is exactly
`Work.FIArea4.Vflip.Vflip_large_full`, the §12 argument (smooth majorant, near-diagonal
removal, Möbius reduction by the common divisor, reciprocity flip of the Jacobi weight,
Fourier–Mellin separation and the crude local bound), assembled from
`Work.FIArea4.Vflip.Vflip_large_dyadic` + the full-box reduction `vfm_large_full`. -/
theorem Vvar_flip_mid (ε : ℝ) (hε : 0 < ε) (h11 : Work.FIArea4.p14Prop111All) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      D ≤ R * S →
      (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
        Work.FIPlan.Vvar R S D α ≤
          C * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S α := by
  -- the large range `R*S < D*D`, via the §12 flip (`vfm_large_full` of the plumbing, whose five
  -- inputs are the dyadic-box estimate, the boundary strips, the two small ranges and the
  -- dyadic summability of the bracket)
  have hcell : ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      D ≤ R * S → R * S < D * D →
      (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
      (∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S) →
        Work.FIPlan.Vvar R S D α ≤
          C * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S α :=
    Vflip_large_dyadic ε hε h11
  have hmed : ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (β : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      R * S < D → (∀ r s, β r s ≠ 0 → Nat.Coprime r (2 * s)) →
        Work.FIPlan.Vvar R S D β ≤ C * (D : ℝ) * Work.FIArea4.p14L2 R S β :=
    ⟨33, by norm_num, fun D R S β hD hR hS hRS hcop =>
      Vvar_le_of_mul_lt_D D R S β hD hR hS hRS hcop⟩
  have hstrip : ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (β : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      (∀ r s, β r s ≠ 0 → r = 1 ∨ s = 1) →
        Work.FIPlan.Vvar R S D β ≤
          C * ((R : ℝ) + (S : ℝ) + (D : ℝ)) * Work.FIArea4.p14L2 R S β :=
    ⟨16, by norm_num, fun D R S β hD hR hS hsupp =>
      Vvar_strip_le D R S β hD hR hS hsupp⟩
  have hsmall : ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      D * D ≤ R * S →
        Work.FIPlan.Vvar R S D α ≤
          C * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S α :=
    Vvar_flip_small' ε hε
  have hdyad : ∃ C : ℝ, 0 < C ∧ ∀ (D R S JR JS : ℕ), 1 ≤ D → 1 ≤ R → 1 ≤ S → D ≤ R * S →
      (2:ℕ)^JR ≤ 2*R → (2:ℕ)^JS ≤ 2*S →
      (∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
        Work.FIArea4.p14T12 D ((2:ℕ)^j) ((2:ℕ)^k) ε) ≤ C * Work.FIArea4.p14T12 D R S ε :=
    p14T12_dyadic_sum_le ε hε
  obtain ⟨C₁, hC₁, hL⟩ := vfm_large_full hε hcell hmed hstrip hsmall hdyad
  obtain ⟨C₂, hC₂, hSm⟩ := Vvar_flip_small' ε hε
  refine ⟨max C₁ C₂, lt_of_lt_of_le hC₂ (le_max_right C₁ C₂), ?_⟩
  intro D R S α hD hR hS hDle hcop
  have hT12 : (0:ℝ) < Work.FIArea4.p14T12 D R S ε := by
    unfold Work.FIArea4.p14T12
    have : (0:ℝ) < (D:ℝ) := by exact_mod_cast (by omega : 0 < D)
    positivity
  have hEnn : (0:ℝ) ≤ Work.FIArea4.p14Ener R S α := by
    unfold Work.FIArea4.p14Ener
    exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ =>
      mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)))
  have hTE : (0:ℝ) ≤ Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S α :=
    mul_nonneg hT12.le hEnn
  by_cases hcase : D * D ≤ R * S
  · calc Work.FIPlan.Vvar R S D α
        ≤ C₂ * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S α :=
          hSm D R S α hD hR hS hcase
      _ ≤ max C₁ C₂ * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S α :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hT12.le) hEnn
  · push_neg at hcase
    calc Work.FIPlan.Vvar R S D α
        ≤ C₁ * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S α :=
          hL D R S α hD hR hS hDle hcase hcop
      _ ≤ max C₁ C₂ * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S α :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hT12.le) hEnn

end

end Work.FIArea4.Vflip
