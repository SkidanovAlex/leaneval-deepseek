import Mathlib
import Submission.PairwiseFourier
import Submission.Truncation
import Submission.Commons.MeasureTheory.Integral.integral_prod_indicator_cube_compl_le

open scoped BigOperators Topology FourierTransform SchwartzMap
open Filter MeasureTheory

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# The `ξ`-truncation of the pairwise Lemma 4.1

P8 Lemma 4.1 replaces the kernel `K = ∏_{p ∤ WN} K_p` by its pole part; the
comparison is proved on the truncation cube `|ξ_j|, |ξ'_j| ≤ √(log x)` (in the
paper's normalisation) and the complement is controlled by the crude bound
`|K| ≪ log^{3k}x` together with the rapid decay of the Schwartz transforms.

This module carries out that truncation for the `k`-coordinate *pairwise* kernel
`pairKernel` (`Submission.PairwiseKernel`), i.e. for the kernel whose P8 (41)
asymptotic is `KernelLimitFamily.kernel_pole_asymptotic_family_eps`:

  * `norm_pairKernel_sub_pairPole_le_cube` — on-cube comparison;
  * `norm_pairPoleP_le` — the growth bound for the pole part;
  * `pairCube_integral_le` — the on-cube integral comparison;
  * `pairOffCube_le` — the off-cube estimate (via the union bound
    `Commons.MeasureTheory.Integral.integral_prod_indicator_cube_compl_le`);
  * `pairKernel_integral_asymptotic` — the assembled comparison against the
    main term `pairPoleMainTerm`.

All kernel-verified, zero `sorry`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-! ## The cube, the pole part and the phase -/

/-- The truncation cube in the `2k` Fourier variables. -/
def truncCubeK (k : ℕ) (x : ℕ) : Set (Fin k → ℝ × ℝ) :=
  ⋂ j : Fin k, (fun p : Fin k → ℝ × ℝ => p j) ⁻¹' truncCube x

@[simp] lemma mem_truncCubeK_iff {k x : ℕ} {p : Fin k → ℝ × ℝ} :
    p ∈ truncCubeK k x ↔ ∀ j, p j ∈ truncCube x := Set.mem_iInter

lemma measurableSet_truncCubeK (k x : ℕ) : MeasurableSet (truncCubeK k x) :=
  MeasurableSet.iInter (fun j =>
    (measurableSet_truncCube x).preimage (continuous_apply j).measurable)

lemma mem_truncCubeK {k x : ℕ} {p : Fin k → ℝ × ℝ} (hp : p ∈ truncCubeK k x) (j : Fin k) :
    |(p j).1| ≤ Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi) ∧
      |(p j).2| ≤ Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi) :=
  mem_truncCube (mem_truncCubeK_iff.mp hp j)

/-- The pairwise kernel at the sieve's Fourier variables. -/
noncomputable def pairKernelP {k : ℕ} (W N : ℕ → ℕ) (x : ℕ) (p : Fin k → ℝ × ℝ) : ℂ :=
  pairKernel ((W x) * (N x)) (fun j => logZ (-(2 * Real.pi * (p j).1)) x)
    (fun j => logZ (-(2 * Real.pi * (p j).2)) x)

/-- The pole part `∏_j [poleFactor_j]⁻¹` of the pairwise kernel. -/
noncomputable def pairPoleP {k : ℕ} (W N : ℕ → ℕ) (x : ℕ) (p : Fin k → ℝ × ℝ) : ℂ :=
  ∏ j : Fin k, (poleFactor (W x) (N x) (-(2 * Real.pi * (p j).1)) (-(2 * Real.pi * (p j).2)) x)⁻¹

/-- The phase of the `2k`-fold integral: the Fourier transforms of the cutoffs. -/
noncomputable def pairPhase {k : ℕ} (F G : Fin k → ℝ → ℝ) (p : Fin k → ℝ × ℝ) : ℂ :=
  ∏ j : Fin k, (fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2)

/-- The polynomial weight of the pole bound: `1 + 2π|t|`. -/
noncomputable def pairW (t : ℝ) : ℝ := 1 + 2 * Real.pi * |t|

lemma one_le_pairW (t : ℝ) : 1 ≤ pairW t := by
  rw [pairW]
  have : 0 ≤ 2 * Real.pi * |t| := by positivity
  linarith

lemma pairW_nonneg (t : ℝ) : 0 ≤ pairW t := le_trans zero_le_one (one_le_pairW t)

/-- The one-coordinate weighted `L¹` norm of a Schwartz transform. -/
noncomputable def pairCF (F : ℝ → ℝ) : ℝ :=
  ∫ ξ : ℝ, pairW ξ * ‖fourierCut F ξ‖

/-! ## The on-cube comparison -/

/-- **On-cube comparison of the pairwise kernel and its pole part.** -/
theorem norm_pairKernel_sub_pairPole_le_cube {k : ℕ} (hk : 1 ≤ k)
    (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0)
    (hcop : ∀ x, (W x).Coprime (N x))
    (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x * N x)
    (hlq : Tendsto (fun x : ℕ =>
        Real.log (((W x) * (N x) : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ x : ℕ, x₀ ≤ x → ∀ p ∈ truncCubeK k x,
        ‖pairKernelP W N x p - pairPoleP W N x p‖ ≤ ε x * ‖pairPoleP W N x p‖ := by
  obtain ⟨x₀, ε, hε, hb⟩ :=
    kernel_pole_asymptotic_family_eps k hk W N hW hN hcop w hw hsmall hlq
  refine ⟨max x₀ 2, ε, hε, fun x hx p hp => ?_⟩
  have hx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hξ : ∀ j : Fin k, |-(2 * Real.pi * (p j).1)| ≤ Real.sqrt (Real.log (x : ℝ)) := by
    intro j
    obtain ⟨h1, _⟩ := mem_truncCubeK hp j
    rw [abs_neg, abs_mul, abs_of_pos h2pi]
    calc 2 * Real.pi * |(p j).1|
        ≤ 2 * Real.pi * (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_left h1 h2pi.le
      _ = Real.sqrt (Real.log (x : ℝ)) := by
          rw [← mul_div_assoc, mul_div_cancel_left₀ _ (by positivity : (2 : ℝ) * Real.pi ≠ 0)]
  have hξ' : ∀ j : Fin k, |-(2 * Real.pi * (p j).2)| ≤ Real.sqrt (Real.log (x : ℝ)) := by
    intro j
    obtain ⟨_, h2⟩ := mem_truncCubeK hp j
    rw [abs_neg, abs_mul, abs_of_pos h2pi]
    calc 2 * Real.pi * |(p j).2|
        ≤ 2 * Real.pi * (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_left h2 h2pi.le
      _ = Real.sqrt (Real.log (x : ℝ)) := by
          rw [← mul_div_assoc, mul_div_cancel_left₀ _ (by positivity : (2 : ℝ) * Real.pi ≠ 0)]
  obtain ⟨L, hL, hbd⟩ := hb x hx₀ (fun j => -(2 * Real.pi * (p j).1))
    (fun j => -(2 * Real.pi * (p j).2)) hξ hξ'
  have hK : pairKernelP W N x p = L := by
    unfold pairKernelP
    exact pairKernel_eq_of_tendsto hL
  have honepole : (∏ j : Fin k, poleFactor (W x) (N x) (-(2 * Real.pi * (p j).1))
      (-(2 * Real.pi * (p j).2)) x) = (pairPoleP W N x p)⁻¹ := by
    rw [pairPoleP, Finset.prod_inv_distrib, inv_inv]
  have hne : pairPoleP W N x p ≠ 0 := by
    rw [pairPoleP]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => inv_ne_zero (poleFactor_ne_zero (W x) (N x)
      (hW x) (hN x) _ _ hlogpos.ne'))
  have hkey : pairKernelP W N x p * (pairPoleP W N x p)⁻¹ - 1 = L *
      (∏ j : Fin k, poleFactor (W x) (N x) (-(2 * Real.pi * (p j).1))
        (-(2 * Real.pi * (p j).2)) x) - 1 := by
    rw [hK, honepole]
  have h2 : ‖pairKernelP W N x p * (pairPoleP W N x p)⁻¹ - 1‖ ≤ ε x := by
    rw [hkey]; exact hbd
  have hEq : pairKernelP W N x p - pairPoleP W N x p =
      pairPoleP W N x p * (pairKernelP W N x p * (pairPoleP W N x p)⁻¹ - 1) := by
    field_simp
  calc ‖pairKernelP W N x p - pairPoleP W N x p‖
      = ‖pairPoleP W N x p * (pairKernelP W N x p * (pairPoleP W N x p)⁻¹ - 1)‖ := by
        rw [hEq]
    _ = ‖pairPoleP W N x p‖ * ‖pairKernelP W N x p * (pairPoleP W N x p)⁻¹ - 1‖ :=
        norm_mul _ _
    _ ≤ ‖pairPoleP W N x p‖ * ε x := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ε x * ‖pairPoleP W N x p‖ := by ring


/-! ## The dominating function of the `2k`-fold phase -/

/-- The one-coordinate dominating weight: the Schwartz weights times the
polynomial growth of the pole factor. -/
noncomputable def pairDomCoord {k : ℕ} (F G : Fin k → ℝ → ℝ) (j : Fin k) (q : ℝ × ℝ) : ℝ :=
  pairW q.1 * ‖fourierCut (F j) q.1‖ * (pairW q.2 * ‖fourierCut (G j) q.2‖)

/-- The dominating weight of the `2k`-fold integral. -/
noncomputable def pairDom {k : ℕ} (F G : Fin k → ℝ → ℝ) (p : Fin k → ℝ × ℝ) : ℝ :=
  ∏ j : Fin k, pairDomCoord F G j (p j)

/-- The (weight-free) norm of the phase. -/
noncomputable def pairPhaseNorm {k : ℕ} (F G : Fin k → ℝ → ℝ) (p : Fin k → ℝ × ℝ) : ℝ :=
  ∏ j : Fin k, (‖fourierCut (F j) (p j).1‖ * ‖fourierCut (G j) (p j).2‖)

lemma pairDomCoord_nonneg {k : ℕ} (F G : Fin k → ℝ → ℝ) (j : Fin k) (q : ℝ × ℝ) :
    0 ≤ pairDomCoord F G j q := by
  rw [pairDomCoord]
  exact mul_nonneg (mul_nonneg (pairW_nonneg _) (norm_nonneg _))
    (mul_nonneg (pairW_nonneg _) (norm_nonneg _))

lemma pairDom_nonneg {k : ℕ} (F G : Fin k → ℝ → ℝ) (p : Fin k → ℝ × ℝ) :
    0 ≤ pairDom F G p := by
  rw [pairDom]
  exact Finset.prod_nonneg (fun j _ => by
    rw [pairDomCoord]
    exact mul_nonneg (mul_nonneg (pairW_nonneg _) (norm_nonneg _))
      (mul_nonneg (pairW_nonneg _) (norm_nonneg _)))

lemma pairPhaseNorm_nonneg {k : ℕ} (F G : Fin k → ℝ → ℝ) (p : Fin k → ℝ × ℝ) :
    0 ≤ pairPhaseNorm F G p :=
  Finset.prod_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The norm of the phase is its `pairPhaseNorm`. -/
lemma norm_pairPhase_eq {k : ℕ} (F G : Fin k → ℝ → ℝ) (p : Fin k → ℝ × ℝ) :
    ‖pairPhase F G p‖ = pairPhaseNorm F G p := by
  rw [pairPhase, pairPhaseNorm, norm_prod]
  exact Finset.prod_congr rfl (fun j _ => norm_mul _ _)

lemma pairPhaseNorm_le_pairDom {k : ℕ} (F G : Fin k → ℝ → ℝ) (p : Fin k → ℝ × ℝ) :
    pairPhaseNorm F G p ≤ pairDom F G p := by
  rw [pairPhaseNorm, pairDom]
  refine Finset.prod_le_prod₀ (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun j _ => ?_)
  rw [pairDomCoord]
  have h1 : (1 : ℝ) ≤ pairW (p j).1 := one_le_pairW _
  have h2 : (1 : ℝ) ≤ pairW (p j).2 := one_le_pairW _
  calc ‖fourierCut (F j) (p j).1‖ * ‖fourierCut (G j) (p j).2‖
      = (1 * ‖fourierCut (F j) (p j).1‖) * (1 * ‖fourierCut (G j) (p j).2‖) := by ring
    _ ≤ (pairW (p j).1 * ‖fourierCut (F j) (p j).1‖) *
          (pairW (p j).2 * ‖fourierCut (G j) (p j).2‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
          (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) (by positivity) (by positivity)

/-- Integrability of the weighted Schwartz transform. -/
lemma integrable_pairW_mul_fourierCut (F : ℝ → ℝ) (hcs : HasCompactSupport F)
    (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F) :
    Integrable (fun ξ : ℝ => pairW ξ * ‖fourierCut F ξ‖) :=
  integrable_one_add_abs_mul_norm_fourierCut F hcs hsm

/-- Integrability of the one-coordinate dominating weight. -/
lemma integrable_pairDomCoord {k : ℕ} (F G : Fin k → ℝ → ℝ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j)) (j : Fin k) :
    Integrable (pairDomCoord F G j) := by
  rw [show (volume : Measure (ℝ × ℝ)) = Measure.prod volume volume from rfl]
  have h := (integrable_pairW_mul_fourierCut (F j) (hcsF j) (hsmF j)).mul_prod
    (integrable_pairW_mul_fourierCut (G j) (hcsG j) (hsmG j))
  refine h.congr (Filter.Eventually.of_forall (fun q => ?_))
  rw [pairDomCoord]

/-- The integral of the one-coordinate dominating weight. -/
lemma integral_pairDomCoord {k : ℕ} (F G : Fin k → ℝ → ℝ) (j : Fin k) :
    ∫ q : ℝ × ℝ, pairDomCoord F G j q = pairCF (F j) * pairCF (G j) := by
  rw [show (∫ q : ℝ × ℝ, pairDomCoord F G j q) =
      ∫ q : ℝ × ℝ, pairW q.1 * ‖fourierCut (F j) q.1‖ * (pairW q.2 * ‖fourierCut (G j) q.2‖) from
    integral_congr_ae (Filter.Eventually.of_forall (fun q => rfl))]
  exact (integral_mul_integral_eq_real (fun ξ : ℝ => pairW ξ * ‖fourierCut (F j) ξ‖)
    (fun ξ : ℝ => pairW ξ * ‖fourierCut (G j) ξ‖)).symm

/-- Integrability of the dominating weight. -/
lemma integrable_pairDom {k : ℕ} (F G : Fin k → ℝ → ℝ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j)) :
    Integrable (pairDom F G) := by
  have hsingle := fun j : Fin k => integrable_pairDomCoord F G hcsF hsmF hcsG hsmG j
  exact MeasureTheory.Integrable.fintype_prod hsingle

/-- The integral of the dominating weight. -/
lemma integral_pairDom {k : ℕ} (F G : Fin k → ℝ → ℝ) :
    ∫ p : Fin k → ℝ × ℝ, pairDom F G p = ∏ j : Fin k, (pairCF (F j) * pairCF (G j)) := by
  rw [show (∫ p : Fin k → ℝ × ℝ, pairDom F G p) =
      ∫ p : Fin k → ℝ × ℝ, ∏ j : Fin k, pairDomCoord F G j (p j) from
    integral_congr_ae (Filter.Eventually.of_forall (fun p => rfl))]
  rw [MeasureTheory.integral_fintype_prod_volume_eq_prod
    (fun j (q : ℝ × ℝ) => pairDomCoord F G j q)]
  exact Finset.prod_congr rfl (fun j _ => integral_pairDomCoord F G j)

/-! ## Growth of the pole part -/

/-- **Growth bound for the pole part.** -/
lemma norm_pairPoleP_le {k : ℕ} (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0)
    {x : ℕ} (hlogpos : 0 < Real.log (x : ℝ)) (p : Fin k → ℝ × ℝ) :
    ‖pairPoleP W N x p‖ ≤ (prefactor W N x) ^ k *
      ∏ j : Fin k, (pairW (p j).1 * pairW (p j).2) := by
  rw [pairPoleP, norm_prod]
  have hper : ∀ j : Fin k, ‖(poleFactor (W x) (N x) (-(2 * Real.pi * (p j).1))
      (-(2 * Real.pi * (p j).2)) x)⁻¹‖ ≤
      prefactor W N x * (pairW (p j).1 * pairW (p j).2) := by
    intro j
    have h := norm_poleInv_le (W x) (N x) (hW x) (hN x) hlogpos.ne' hlogpos
      ((p j).1) ((p j).2)
    have hpre_eq : prefactor W N x * (pairW (p j).1 * pairW (p j).2) =
        ((N x : ℝ) / ((N x).totient : ℝ)) * ((W x : ℝ) / ((W x).totient : ℝ)) *
          (Real.log (x : ℝ))⁻¹ * pairW (p j).1 * pairW (p j).2 := by
      rw [prefactor]; ring
    rw [hpre_eq, pairW]
    exact h
  calc ∏ j : Fin k, ‖(poleFactor (W x) (N x) (-(2 * Real.pi * (p j).1))
        (-(2 * Real.pi * (p j).2)) x)⁻¹‖
      ≤ ∏ j : Fin k, (prefactor W N x * (pairW (p j).1 * pairW (p j).2)) :=
        Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => hper j)
    _ = (prefactor W N x) ^ k *
        ∏ j : Fin k, (pairW (p j).1 * pairW (p j).2) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## The on-cube integral comparison -/

/-- **On-cube integral comparison.** -/
theorem pairCube_integral_le {k : ℕ} (hk : 1 ≤ k) (F G : Fin k → ℝ → ℝ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0)
    (hcop : ∀ x, (W x).Coprime (N x))
    (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x * N x)
    (hlq : Tendsto (fun x : ℕ =>
        Real.log (((W x) * (N x) : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ x : ℕ, x₀ ≤ x →
        (∫ p in truncCubeK k x,
            ‖(pairKernelP W N x p - pairPoleP W N x p) * pairPhase F G p‖) ≤
          |ε x| * prefactor W N x ^ k * ∏ j : Fin k, (pairCF (F j) * pairCF (G j)) := by
  obtain ⟨x₀, ε, hε, hcomp⟩ :=
    norm_pairKernel_sub_pairPole_le_cube hk W N hW hN hcop w hw hsmall hlq
  refine ⟨max x₀ 2, ε, hε, fun x hx => ?_⟩
  have hx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hpre : 0 ≤ prefactor W N x := by
    rw [prefactor]
    have h1 : (0 : ℝ) < ((N x).totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hN x))
    have h2 : (0 : ℝ) < ((W x).totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hW x))
    positivity
  have hpt : ∀ p ∈ truncCubeK k x,
      ‖(pairKernelP W N x p - pairPoleP W N x p) * pairPhase F G p‖ ≤
        |ε x| * prefactor W N x ^ k * pairDom F G p := by
    intro p hp
    have hmm := hcomp x hx₀ p hp
    have hP := norm_pairPoleP_le W N hW hN hlogpos p
    rw [norm_mul, norm_pairPhase_eq F G p]
    have hε0 : (0 : ℝ) ≤ |ε x| := abs_nonneg _
    have hstep1 : ‖pairKernelP W N x p - pairPoleP W N x p‖ * pairPhaseNorm F G p ≤
        (|ε x| * ‖pairPoleP W N x p‖) * pairPhaseNorm F G p :=
      mul_le_mul_of_nonneg_right (hmm.trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)))
        (pairPhaseNorm_nonneg F G p)
    have hprod : (prefactor W N x) ^ k *
        (∏ j : Fin k, (pairW (p j).1 * pairW (p j).2)) * pairPhaseNorm F G p ≤
        (prefactor W N x) ^ k * pairDom F G p := by
      have h1 : (∏ j : Fin k, (pairW (p j).1 * pairW (p j).2)) * pairPhaseNorm F G p ≤
          pairDom F G p := by
        rw [pairPhaseNorm, pairDom]
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_le_prod₀ (fun j _ => mul_nonneg (mul_nonneg (pairW_nonneg _)
          (pairW_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (fun j _ => ?_)
        rw [pairDomCoord]
        have : (pairW (p j).1 * pairW (p j).2) *
            (‖fourierCut (F j) (p j).1‖ * ‖fourierCut (G j) (p j).2‖) =
            (pairW (p j).1 * ‖fourierCut (F j) (p j).1‖) *
              (pairW (p j).2 * ‖fourierCut (G j) (p j).2‖) := by ring
        rw [this]
      have hpk : 0 ≤ (prefactor W N x) ^ k := pow_nonneg hpre k
      calc (prefactor W N x) ^ k *
            (∏ j : Fin k, (pairW (p j).1 * pairW (p j).2)) * pairPhaseNorm F G p
          = (prefactor W N x) ^ k *
            ((∏ j : Fin k, (pairW (p j).1 * pairW (p j).2)) * pairPhaseNorm F G p) := by ring
        _ ≤ (prefactor W N x) ^ k * pairDom F G p := mul_le_mul_of_nonneg_left h1 hpk
    calc ‖pairKernelP W N x p - pairPoleP W N x p‖ * pairPhaseNorm F G p
        ≤ (|ε x| * ‖pairPoleP W N x p‖) * pairPhaseNorm F G p := hstep1
      _ ≤ (|ε x| * ((prefactor W N x) ^ k *
            ∏ j : Fin k, (pairW (p j).1 * pairW (p j).2))) * pairPhaseNorm F G p :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP hε0)
            (pairPhaseNorm_nonneg F G p)
      _ = |ε x| * ((prefactor W N x) ^ k *
            (∏ j : Fin k, (pairW (p j).1 * pairW (p j).2)) * pairPhaseNorm F G p) := by ring
      _ ≤ |ε x| * ((prefactor W N x) ^ k * pairDom F G p) :=
          mul_le_mul_of_nonneg_left hprod hε0
      _ = |ε x| * prefactor W N x ^ k * pairDom F G p := by ring
  have hInt : Integrable (fun p : Fin k → ℝ × ℝ =>
      |ε x| * prefactor W N x ^ k * pairDom F G p) :=
    (integrable_pairDom F G hcsF hsmF hcsG hsmG).const_mul _
  have hmono : (∫ p in truncCubeK k x,
        ‖(pairKernelP W N x p - pairPoleP W N x p) * pairPhase F G p‖) ≤
      ∫ p : Fin k → ℝ × ℝ, |ε x| * prefactor W N x ^ k * pairDom F G p := by
    rw [(integral_indicator (measurableSet_truncCubeK k x)).symm]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun p => ?_)) hInt
      (Filter.Eventually.of_forall (fun p => ?_))
    · by_cases hp : p ∈ truncCubeK k x
      · rw [Set.indicator_of_mem hp]; exact norm_nonneg _
      · rw [Set.indicator_of_notMem hp]; exact le_rfl
    · by_cases hp : p ∈ truncCubeK k x
      · rw [Set.indicator_of_mem hp]; exact hpt p hp
      · rw [Set.indicator_of_notMem hp]
        exact mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hpre k)) (pairDom_nonneg F G p)
  refine hmono.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_pairDom F G]


/-! ## The off-cube estimate -/

/-- The complement of the truncation cube is contained in the union of the
coordinate strips. -/
lemma compl_truncCubeK_subset {k x : ℕ} :
    (truncCubeK k x)ᶜ ⊆ {p : Fin k → ℝ × ℝ |
      ∃ j, Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi) ≤ |(p j).1| ∨
        Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi) ≤ |(p j).2|} := by
  intro p hp
  simp only [Set.mem_compl_iff, mem_truncCubeK_iff, Set.mem_setOf_eq] at hp ⊢
  push_neg at hp
  obtain ⟨j, hj⟩ := hp
  refine ⟨j, ?_⟩
  simp only [truncCube, Set.mem_prod, Set.mem_Icc] at hj
  rw [not_and_or] at hj
  have key : ∀ t : ℝ, ¬(-(Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) ≤ t ∧
      t ≤ Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) →
      Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi) ≤ |t| := by
    intro t ht
    refine le_of_lt (not_le.mp fun hle => ht ⟨?_, ?_⟩)
    · rw [abs_le] at hle; exact hle.1
    · rw [abs_le] at hle; exact hle.2
  rcases hj with hj | hj
  · exact Or.inl (key _ hj)
  · exact Or.inr (key _ hj)

lemma pairCF_nonneg {k : ℕ} (F : Fin k → ℝ → ℝ) (j : Fin k) : 0 ≤ pairCF (F j) := by
  rw [pairCF]
  exact integral_nonneg (fun t => mul_nonneg (pairW_nonneg t) (norm_nonneg _))

/-- The set integral of the one-coordinate weight over the strip `ρ ≤ |q.1|`
separates. -/
lemma setIntegral_pairDomCoord_fst {k : ℕ} (F G : Fin k → ℝ → ℝ) (j : Fin k) (ρ : ℝ) :
    (∫ q in {q : ℝ × ℝ | ρ ≤ |q.1|}, pairDomCoord F G j q) =
      (∫ t in {t : ℝ | ρ ≤ |t|}, pairW t * ‖fourierCut (F j) t‖) * pairCF (G j) := by
  have hset : {q : ℝ × ℝ | ρ ≤ |q.1|} = {t : ℝ | ρ ≤ |t|} ×ˢ Set.univ := by
    ext q; simp
  rw [hset, show (volume : Measure (ℝ × ℝ)) = Measure.prod volume volume from rfl]
  rw [show pairDomCoord F G j = fun q : ℝ × ℝ =>
      (pairW q.1 * ‖fourierCut (F j) q.1‖) * (pairW q.2 * ‖fourierCut (G j) q.2‖) from rfl]
  dsimp only
  have h := MeasureTheory.setIntegral_prod_mul (μ := volume) (ν := volume)
    (fun t : ℝ => pairW t * ‖fourierCut (F j) t‖)
    (fun t : ℝ => pairW t * ‖fourierCut (G j) t‖) {t : ℝ | ρ ≤ |t|} Set.univ
  rw [MeasureTheory.setIntegral_univ] at h
  exact h

/-- The set integral of the one-coordinate weight over the strip `ρ ≤ |q.2|`
separates. -/
lemma setIntegral_pairDomCoord_snd {k : ℕ} (F G : Fin k → ℝ → ℝ) (j : Fin k) (ρ : ℝ) :
    (∫ q in {q : ℝ × ℝ | ρ ≤ |q.2|}, pairDomCoord F G j q) =
      pairCF (F j) * (∫ t in {t : ℝ | ρ ≤ |t|}, pairW t * ‖fourierCut (G j) t‖) := by
  have hset : {q : ℝ × ℝ | ρ ≤ |q.2|} = Set.univ ×ˢ {t : ℝ | ρ ≤ |t|} := by
    ext q; simp
  rw [hset, show (volume : Measure (ℝ × ℝ)) = Measure.prod volume volume from rfl]
  rw [show pairDomCoord F G j = fun q : ℝ × ℝ =>
      (pairW q.1 * ‖fourierCut (F j) q.1‖) * (pairW q.2 * ‖fourierCut (G j) q.2‖) from rfl]
  dsimp only
  have h := MeasureTheory.setIntegral_prod_mul (μ := volume) (ν := volume)
    (fun t : ℝ => pairW t * ‖fourierCut (F j) t‖)
    (fun t : ℝ => pairW t * ‖fourierCut (G j) t‖) Set.univ {t : ℝ | ρ ≤ |t|}
  rw [MeasureTheory.setIntegral_univ] at h
  exact h

/-- Integrability of the `(1 + |t|)`-weighted Schwartz transform. -/
lemma integrable_one_add_abs_mul_norm_fourierCut_pow1 (F : ℝ → ℝ) (hcs : HasCompactSupport F)
    (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F) :
    Integrable (fun t : ℝ => (1 + |t|) * ‖fourierCut F t‖) := by
  refine Integrable.mono' (integrable_one_add_abs_mul_norm_fourierCut F hcs hsm) ?_ ?_
  · have h : Continuous (fourierCut F) := by
      have h2 := (schwartzCut F hcs hsm).continuous
      rw [schwartzCut_coe F hcs hsm] at h2
      exact h2
    exact ((continuous_const.add continuous_abs).mul h.norm).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1 + |t|) * ‖fourierCut F t‖)]
    have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have h2 : 1 + |t| ≤ 1 + 2 * Real.pi * |t| := by
      nlinarith [abs_nonneg t, hpi]
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

/-- One-dimensional tail bound for the weighted Schwartz transform. -/
lemma tail_pairW_le (F : ℝ → ℝ) (hcs : HasCompactSupport F) (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F)
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃ρ : ℝ⦄, 1 ≤ ρ →
      (∫ t in {t : ℝ | ρ ≤ |t|}, pairW t * ‖fourierCut F t‖) ≤ C / ρ ^ m := by
  obtain ⟨C, hC, h⟩ := Commons.Analysis.Schwartz.integral_norm_compl_mul_rpow_le
    (schwartzCut F hcs hsm) 1 m
  refine ⟨2 * Real.pi * C, by positivity, fun ρ hρ => ?_⟩
  have h1 : (∫ t in {t : ℝ | ρ ≤ |t|}, pairW t * ‖fourierCut F t‖) ≤
      ∫ t in {t : ℝ | ρ ≤ |t|}, (2 * Real.pi) * ((1 + |t|) * ‖fourierCut F t‖) := by
    refine integral_mono_ae (integrable_pairW_mul_fourierCut F hcs hsm).integrableOn
      (((integrable_one_add_abs_mul_norm_fourierCut_pow1 F hcs hsm).integrableOn).const_mul
        (2 * Real.pi)) (Filter.Eventually.of_forall (fun t => ?_))
    dsimp only
    have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hW : pairW t ≤ 2 * Real.pi * (1 + |t|) := by
      rw [pairW]
      nlinarith [abs_nonneg t, hpi]
    calc pairW t * ‖fourierCut F t‖ ≤ (2 * Real.pi * (1 + |t|)) * ‖fourierCut F t‖ :=
          mul_le_mul_of_nonneg_right hW (norm_nonneg _)
      _ = 2 * Real.pi * ((1 + |t|) * ‖fourierCut F t‖) := by ring
  rw [integral_const_mul] at h1
  have h2 : (∫ t in {t : ℝ | ρ ≤ |t|}, (1 + |t|) * ‖fourierCut F t‖) ≤ C / ρ ^ m := by
    simpa [pow_one, schwartzCut_coe F hcs hsm, fourierCut] using h ρ hρ
  calc (∫ t in {t : ℝ | ρ ≤ |t|}, pairW t * ‖fourierCut F t‖)
      ≤ 2 * Real.pi * (∫ t in {t : ℝ | ρ ≤ |t|}, (1 + |t|) * ‖fourierCut F t‖) := h1
    _ ≤ 2 * Real.pi * (C / ρ ^ m) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 * Real.pi * C / ρ ^ m := by ring


/-- The tail bound holds for all positive radii (absorbing the `ρ ≤ 1` case into
the full integral). -/
lemma tail_pairW_le_all (F : ℝ → ℝ) (hcs : HasCompactSupport F) (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F)
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃ρ : ℝ⦄, 0 < ρ →
      (∫ t in {t : ℝ | ρ ≤ |t|}, pairW t * ‖fourierCut F t‖) ≤ C / ρ ^ m := by
  obtain ⟨C, hC, h⟩ := tail_pairW_le F hcs hsm m
  set I : ℝ := ∫ t : ℝ, pairW t * ‖fourierCut F t‖ with hI
  have hI0 : 0 ≤ I := integral_nonneg (fun t => mul_nonneg (pairW_nonneg t) (norm_nonneg _))
  refine ⟨max C I + 1, by positivity, fun ρ hρ => ?_⟩
  by_cases hρ1 : 1 ≤ ρ
  · refine (h hρ1).trans ?_
    exact div_le_div_of_nonneg_right (by linarith [le_max_left C I]) (pow_pos hρ m).le
  · push_neg at hρ1
    have hmono : (∫ t in {t : ℝ | ρ ≤ |t|}, pairW t * ‖fourierCut F t‖) ≤ I := by
      rw [show (∫ t in {t : ℝ | ρ ≤ |t|}, pairW t * ‖fourierCut F t‖) =
          ∫ t, ({t : ℝ | ρ ≤ |t|}).indicator (fun t => pairW t * ‖fourierCut F t‖) t from
        (integral_indicator (by measurability)).symm]
      rw [hI]
      refine integral_mono ((integrable_pairW_mul_fourierCut F hcs hsm).indicator
        (by measurability)) (integrable_pairW_mul_fourierCut F hcs hsm) (fun t => ?_)
      by_cases ht : t ∈ {t : ℝ | ρ ≤ |t|}
      · rw [Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht]
        exact mul_nonneg (pairW_nonneg t) (norm_nonneg _)
    calc (∫ t in {t : ℝ | ρ ≤ |t|}, pairW t * ‖fourierCut F t‖) ≤ I := hmono
      _ ≤ (max C I + 1) / ρ ^ m := by
          have h1 : I ≤ max C I + 1 := by linarith [le_max_right C I]
          have h2 : (1 : ℝ) ≤ (ρ ^ m)⁻¹ := by
            rw [one_le_inv₀ (pow_pos hρ m)]
            exact pow_le_one₀ hρ.le hρ1.le
          calc I = I * 1 := by ring
            _ ≤ I * (ρ ^ m)⁻¹ := mul_le_mul_of_nonneg_left h2 hI0
            _ ≤ (max C I + 1) * (ρ ^ m)⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = (max C I + 1) / ρ ^ m := by rw [div_eq_mul_inv]

theorem pairOffCube_le {k : ℕ} (hk : 1 ≤ k) (F G : Fin k → ℝ → ℝ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0) (m : ℕ) :
    ∃ x₀ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, x₀ ≤ x →
      (∫ p in (truncCubeK k x)ᶜ, ‖pairKernelP W N x p * pairPhase F G p‖) ≤
        C * (Real.log (x : ℝ)) ^ (3 * k) /
          (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) ^ m := by
  obtain ⟨Ck, hCkpos, hCkev⟩ := crudeKernelCoord_eventually_uniform k
  choose CF hCF using fun j : Fin k => tail_pairW_le_all (F j) (hcsF j) (hsmF j) m
  choose CG hCG using fun j : Fin k => tail_pairW_le_all (G j) (hcsG j) (hsmG j) m
  set S : ℝ := ∑ j : Fin k, (CF j + CG j) with hSdef
  set K1 : ℝ := ∏ j : Fin k, ((1 + pairCF (F j)) * (1 + pairCF (G j))) with hK1def
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg (fun j _ => by linarith [(hCF j).1.le, (hCG j).1.le])
  have hK1nn : 0 ≤ K1 := by
    rw [hK1def]
    exact Finset.prod_nonneg (fun j _ => mul_nonneg (by linarith [pairCF_nonneg F j])
      (by linarith [pairCF_nonneg G j]))
  have hCpos : (0 : ℝ) < Ck * (S * K1 + 1) := by positivity
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp (hCkev.and (eventually_ge_atTop 2))
  refine ⟨x₀, Ck * (S * K1 + 1), hCpos, fun x hx => ?_⟩
  obtain ⟨hPx, hx2⟩ := hx₀ x hx
  have hx1 : 1 < x := by omega
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx1)
  set rho : ℝ := Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi) with hrhodef
  have hrho_pos : 0 < rho := by
    rw [hrhodef]
    exact div_pos (Real.sqrt_pos.mpr hlogpos) (by positivity)
  have hrhom : 0 < rho ^ m := pow_pos hrho_pos m
  have hLnn : 0 ≤ (Real.log (x : ℝ)) ^ (3 * k) := by positivity
  -- ### 1. the crude pointwise kernel bound
  have hKbound : ∀ p : Fin k → ℝ × ℝ,
      ‖pairKernelP W N x p‖ ≤ Ck * (Real.log (x : ℝ)) ^ (3 * k) := by
    intro p
    have hq : W x * N x ≠ 0 := mul_ne_zero (hW x) (hN x)
    have ha : ∀ j : Fin k, 0 < (logZ (-(2 * Real.pi * (p j).1)) x).re := by
      intro j; rw [logZ_re]; positivity
    have hb : ∀ j : Fin k, 0 < (logZ (-(2 * Real.pi * (p j).2)) x).re := by
      intro j; rw [logZ_re]; positivity
    have hC : ∀ n : ℕ, ‖∏ pr ∈ Sfilter (W x * N x) n,
        coordLocalK pr (fun j => logZ (-(2 * Real.pi * (p j).1)) x)
          (fun j => logZ (-(2 * Real.pi * (p j).2)) x)‖ ≤
        Ck * (Real.log (x : ℝ)) ^ (3 * k) := by
      intro n
      have h := hPx (W x * N x) n (fun j => logZ (-(2 * Real.pi * (p j).1)) x)
        (fun j => logZ (-(2 * Real.pi * (p j).2)) x)
        (fun j => logZ_re _ x) (fun j => logZ_re _ x)
      simpa [Sfilter] using h
    have hres := norm_pairKernel_le (q := W x * N x) hq ha hb hC
    simpa [pairKernelP] using hres
  -- ### 2. pointwise domination by the weight
  have hdom : ∀ p : Fin k → ℝ × ℝ,
      ‖pairKernelP W N x p * pairPhase F G p‖ ≤
        Ck * (Real.log (x : ℝ)) ^ (3 * k) * pairDom F G p := by
    intro p
    rw [norm_mul, norm_pairPhase_eq F G p]
    have h1 := hKbound p
    have h2 := pairPhaseNorm_le_pairDom F G p
    have h3 : 0 ≤ Ck * (Real.log (x : ℝ)) ^ (3 * k) := mul_nonneg hCkpos.le hLnn
    exact mul_le_mul h1 h2 (pairPhaseNorm_nonneg F G p) h3
  -- ### 3. the conditional integrands
  have hset_meas : MeasurableSet (truncCubeK k x)ᶜ := (measurableSet_truncCubeK k x).compl
  have hcond_meas : MeasurableSet {p : Fin k → ℝ × ℝ | ∃ j, rho ≤ |(p j).1| ∨ rho ≤ |(p j).2|} := by
    have hEq : {p : Fin k → ℝ × ℝ | ∃ j, rho ≤ |(p j).1| ∨ rho ≤ |(p j).2|}
        = ⋃ j, ((fun p : Fin k → ℝ × ℝ => |(p j).1|) ⁻¹' Set.Ici rho ∪
                (fun p : Fin k → ℝ × ℝ => |(p j).2|) ⁻¹' Set.Ici rho) := by
      ext p; simp
    rw [hEq]
    refine MeasurableSet.iUnion (fun j => MeasurableSet.union ?_ ?_)
    · exact measurableSet_Ici.preimage (((measurable_pi_apply j).fst).abs)
    · exact measurableSet_Ici.preimage (((measurable_pi_apply j).snd).abs)
  have hDomInt : Integrable (pairDom F G) := integrable_pairDom F G hcsF hsmF hcsG hsmG
  have hIntC : Integrable ({p : Fin k → ℝ × ℝ |
      ∃ j, rho ≤ |(p j).1| ∨ rho ≤ |(p j).2|}.indicator (pairDom F G)) :=
    hDomInt.indicator hcond_meas
  -- ### 4a. passing to the union-of-strips indicator
  have step4a : (∫ p in (truncCubeK k x)ᶜ, pairDom F G p) ≤
      ∫ p, {p : Fin k → ℝ × ℝ | ∃ j, rho ≤ |(p j).1| ∨ rho ≤ |(p j).2|}.indicator
        (pairDom F G) p := by
    rw [← integral_indicator hset_meas]
    refine integral_mono (hDomInt.indicator hset_meas) hIntC (fun p => ?_)
    by_cases hp : p ∈ (truncCubeK k x)ᶜ
    · have hmem : p ∈ {q : Fin k → ℝ × ℝ | ∃ j, rho ≤ |(q j).1| ∨ rho ≤ |(q j).2|} := by
        have hsub := compl_truncCubeK_subset hp
        rw [hrhodef]
        exact hsub
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hp]
      exact Set.indicator_nonneg (fun q _ => pairDom_nonneg F G q) p
  -- ### 4b. the union bound (commons L41)
  have step4b : (∫ p, {p : Fin k → ℝ × ℝ | ∃ j, rho ≤ |(p j).1| ∨ rho ≤ |(p j).2|}.indicator
        (pairDom F G) p)
      ≤ ∑ j : Fin k, ((∫ q in {q : ℝ × ℝ | rho ≤ |q.1|}, pairDomCoord F G j q) +
            (∫ q in {q : ℝ × ℝ | rho ≤ |q.2|}, pairDomCoord F G j q)) *
          ∏ i ∈ Finset.univ.erase j, ∫ q : ℝ × ℝ, pairDomCoord F G i q := by
    have hif : (∫ p : Fin k → ℝ × ℝ, {p : Fin k → ℝ × ℝ |
          ∃ j, rho ≤ |(p j).1| ∨ rho ≤ |(p j).2|}.indicator (pairDom F G) p)
        = ∫ p : Fin k → ℝ × ℝ, (if ∃ j, rho ≤ |(p j).1| ∨ rho ≤ |(p j).2| then
            ∏ j, pairDomCoord F G j (p j) else 0) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      dsimp only
      by_cases h : ∃ j, rho ≤ |(p j).1| ∨ rho ≤ |(p j).2|
      · rw [Set.indicator_of_mem (show p ∈ {q : Fin k → ℝ × ℝ |
            ∃ j, rho ≤ |(q j).1| ∨ rho ≤ |(q j).2|} from h), if_pos h]
        rfl
      · rw [Set.indicator_of_notMem (show p ∉ {q : Fin k → ℝ × ℝ |
            ∃ j, rho ≤ |(q j).1| ∨ rho ≤ |(q j).2|} from h), if_neg h]
    rw [hif]
    exact Commons.MeasureTheory.Integral.integral_prod_indicator_cube_compl_le (pairDomCoord F G) rho
      (fun j => integrable_pairDomCoord F G hcsF hsmF hcsG hsmG j)
      (fun j q => pairDomCoord_nonneg F G j q)
  -- ### 5. the per-coordinate bounds
  have hK1erase : ∀ j : Fin k,
      pairCF (G j) * (∏ i ∈ Finset.univ.erase j, (1 + pairCF (F i)) * (1 + pairCF (G i)))
        ≤ K1 := by
    intro j
    have hPnn : 0 ≤ ∏ i ∈ Finset.univ.erase j, (1 + pairCF (F i)) * (1 + pairCF (G i)) :=
      Finset.prod_nonneg (fun i _ => mul_nonneg (by linarith [pairCF_nonneg F i])
        (by linarith [pairCF_nonneg G i]))
    have hle : pairCF (G j) ≤ (1 + pairCF (F j)) * (1 + pairCF (G j)) := by
      have h1 := pairCF_nonneg F j
      have h2 := pairCF_nonneg G j
      nlinarith [mul_nonneg h1 h2]
    rw [hK1def, ← Finset.mul_prod_erase Finset.univ
      (fun i : Fin k => (1 + pairCF (F i)) * (1 + pairCF (G i))) (Finset.mem_univ j)]
    exact mul_le_mul_of_nonneg_right hle hPnn
  have hK1eraseF : ∀ j : Fin k,
      pairCF (F j) * (∏ i ∈ Finset.univ.erase j, (1 + pairCF (F i)) * (1 + pairCF (G i)))
        ≤ K1 := by
    intro j
    have hPnn : 0 ≤ ∏ i ∈ Finset.univ.erase j, (1 + pairCF (F i)) * (1 + pairCF (G i)) :=
      Finset.prod_nonneg (fun i _ => mul_nonneg (by linarith [pairCF_nonneg F i])
        (by linarith [pairCF_nonneg G i]))
    have hle : pairCF (F j) ≤ (1 + pairCF (F j)) * (1 + pairCF (G j)) := by
      have h1 := pairCF_nonneg F j
      have h2 := pairCF_nonneg G j
      nlinarith [mul_nonneg h1 h2]
    rw [hK1def, ← Finset.mul_prod_erase Finset.univ
      (fun i : Fin k => (1 + pairCF (F i)) * (1 + pairCF (G i))) (Finset.mem_univ j)]
    exact mul_le_mul_of_nonneg_right hle hPnn
  have hP' : ∀ j : Fin k,
      (∏ i ∈ Finset.univ.erase j, ∫ q : ℝ × ℝ, pairDomCoord F G i q) ≤
        ∏ i ∈ Finset.univ.erase j, (1 + pairCF (F i)) * (1 + pairCF (G i)) := by
    intro j
    have hInt : ∀ i : Fin k, (∫ q : ℝ × ℝ, pairDomCoord F G i q) =
        pairCF (F i) * pairCF (G i) := fun i => integral_pairDomCoord F G i
    simp only [hInt]
    refine Finset.prod_le_prod₀ (fun i _ => mul_nonneg (pairCF_nonneg F i) (pairCF_nonneg G i))
      (fun i _ => ?_)
    have h1 := pairCF_nonneg F i
    have h2 := pairCF_nonneg G i
    nlinarith [mul_nonneg h1 h2]
  have hsummand : ∀ j : Fin k,
      ((∫ q in {q : ℝ × ℝ | rho ≤ |q.1|}, pairDomCoord F G j q) +
          (∫ q in {q : ℝ × ℝ | rho ≤ |q.2|}, pairDomCoord F G j q)) *
        (∏ i ∈ Finset.univ.erase j, ∫ q : ℝ × ℝ, pairDomCoord F G i q)
      ≤ ((CF j + CG j) / rho ^ m) * K1 := by
    intro j
    have hcf : 0 ≤ CF j / rho ^ m := div_nonneg (hCF j).1.le hrhom.le
    have hcg : 0 ≤ CG j / rho ^ m := div_nonneg (hCG j).1.le hrhom.le
    have hPnn : 0 ≤ ∏ i ∈ Finset.univ.erase j, ∫ q : ℝ × ℝ, pairDomCoord F G i q :=
      Finset.prod_nonneg (fun i _ => integral_nonneg (fun q => pairDomCoord_nonneg F G i q))
    have hP'nn : 0 ≤ ∏ i ∈ Finset.univ.erase j, (1 + pairCF (F i)) * (1 + pairCF (G i)) :=
      Finset.prod_nonneg (fun i _ => mul_nonneg (by linarith [pairCF_nonneg F i])
        (by linarith [pairCF_nonneg G i]))
    -- the two coordinate tails
    have h1 : (∫ t in {t : ℝ | rho ≤ |t|}, pairW t * ‖fourierCut (F j) t‖) ≤ CF j / rho ^ m :=
      (hCF j).2 hrho_pos
    have h2 : (∫ t in {t : ℝ | rho ≤ |t|}, pairW t * ‖fourierCut (G j) t‖) ≤ CG j / rho ^ m :=
      (hCG j).2 hrho_pos
    have hAB : (∫ q in {q : ℝ × ℝ | rho ≤ |q.1|}, pairDomCoord F G j q) +
        (∫ q in {q : ℝ × ℝ | rho ≤ |q.2|}, pairDomCoord F G j q) ≤
        (CF j / rho ^ m) * pairCF (G j) + pairCF (F j) * (CG j / rho ^ m) := by
      rw [setIntegral_pairDomCoord_fst F G j rho, setIntegral_pairDomCoord_snd F G j rho]
      exact add_le_add (mul_le_mul_of_nonneg_right h1 (pairCF_nonneg G j))
        (mul_le_mul_of_nonneg_left h2 (pairCF_nonneg F j))
    have hcoefnn : 0 ≤ (CF j / rho ^ m) * pairCF (G j) + pairCF (F j) * (CG j / rho ^ m) :=
      add_nonneg (mul_nonneg hcf (pairCF_nonneg G j)) (mul_nonneg (pairCF_nonneg F j) hcg)
    calc ((∫ q in {q : ℝ × ℝ | rho ≤ |q.1|}, pairDomCoord F G j q) +
          (∫ q in {q : ℝ × ℝ | rho ≤ |q.2|}, pairDomCoord F G j q)) *
          (∏ i ∈ Finset.univ.erase j, ∫ q : ℝ × ℝ, pairDomCoord F G i q)
        ≤ ((CF j / rho ^ m) * pairCF (G j) + pairCF (F j) * (CG j / rho ^ m)) *
          (∏ i ∈ Finset.univ.erase j, ∫ q : ℝ × ℝ, pairDomCoord F G i q) :=
          mul_le_mul_of_nonneg_right hAB hPnn
      _ ≤ ((CF j / rho ^ m) * pairCF (G j) + pairCF (F j) * (CG j / rho ^ m)) *
          (∏ i ∈ Finset.univ.erase j, (1 + pairCF (F i)) * (1 + pairCF (G i))) :=
          mul_le_mul_of_nonneg_left (hP' j) hcoefnn
      _ = (CF j / rho ^ m) * (pairCF (G j) *
            (∏ i ∈ Finset.univ.erase j, (1 + pairCF (F i)) * (1 + pairCF (G i)))) +
          (CG j / rho ^ m) * (pairCF (F j) *
            (∏ i ∈ Finset.univ.erase j, (1 + pairCF (F i)) * (1 + pairCF (G i)))) := by ring
      _ ≤ (CF j / rho ^ m) * K1 + (CG j / rho ^ m) * K1 :=
          add_le_add (mul_le_mul_of_nonneg_left (hK1erase j) hcf)
            (mul_le_mul_of_nonneg_left (hK1eraseF j) hcg)
      _ = ((CF j + CG j) / rho ^ m) * K1 := by ring
  have step5 : (∑ j : Fin k, ((∫ q in {q : ℝ × ℝ | rho ≤ |q.1|}, pairDomCoord F G j q) +
        (∫ q in {q : ℝ × ℝ | rho ≤ |q.2|}, pairDomCoord F G j q)) *
        (∏ i ∈ Finset.univ.erase j, ∫ q : ℝ × ℝ, pairDomCoord F G i q))
      ≤ S * K1 / rho ^ m := by
    calc (∑ j : Fin k, ((∫ q in {q : ℝ × ℝ | rho ≤ |q.1|}, pairDomCoord F G j q) +
          (∫ q in {q : ℝ × ℝ | rho ≤ |q.2|}, pairDomCoord F G j q)) *
          (∏ i ∈ Finset.univ.erase j, ∫ q : ℝ × ℝ, pairDomCoord F G i q))
        ≤ ∑ j : Fin k, ((CF j + CG j) / rho ^ m) * K1 :=
          Finset.sum_le_sum (fun j _ => hsummand j)
      _ = (∑ j : Fin k, (CF j + CG j)) * K1 / rho ^ m := by
          have h : ∀ j : Fin k, ((CF j + CG j) / rho ^ m) * K1 =
              ((CF j + CG j) * K1) / rho ^ m := fun j => by ring
          simp only [h]
          rw [← Finset.sum_div, Finset.sum_mul]
      _ = S * K1 / rho ^ m := by rw [hSdef]
  -- ### 6. the final chain
  have step4 := le_trans step4a step4b
  calc (∫ p in (truncCubeK k x)ᶜ, ‖pairKernelP W N x p * pairPhase F G p‖)
      = ∫ p, (truncCubeK k x)ᶜ.indicator
          (fun p => ‖pairKernelP W N x p * pairPhase F G p‖) p :=
        (integral_indicator hset_meas).symm
    _ ≤ ∫ p, Ck * (Real.log (x : ℝ)) ^ (3 * k) *
          ((truncCubeK k x)ᶜ.indicator (pairDom F G) p) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun p => ?_))
          (hDomInt.indicator hset_meas |>.const_mul _)
          (Filter.Eventually.of_forall (fun p => ?_))
        · exact Set.indicator_nonneg (fun q _ => norm_nonneg _) p
        · dsimp only
          by_cases hp : p ∈ (truncCubeK k x)ᶜ
          · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
            exact hdom p
          · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, mul_zero]
    _ = Ck * (Real.log (x : ℝ)) ^ (3 * k) *
          (∫ p in (truncCubeK k x)ᶜ, pairDom F G p) := by
        rw [integral_const_mul, integral_indicator hset_meas]
    _ ≤ Ck * (Real.log (x : ℝ)) ^ (3 * k) *
          (∑ j : Fin k, ((∫ q in {q : ℝ × ℝ | rho ≤ |q.1|}, pairDomCoord F G j q) +
            (∫ q in {q : ℝ × ℝ | rho ≤ |q.2|}, pairDomCoord F G j q)) *
              ∏ i ∈ Finset.univ.erase j, ∫ q : ℝ × ℝ, pairDomCoord F G i q) :=
        mul_le_mul_of_nonneg_left step4 (mul_nonneg hCkpos.le hLnn)
    _ ≤ Ck * (Real.log (x : ℝ)) ^ (3 * k) * (S * K1 / rho ^ m) :=
        mul_le_mul_of_nonneg_left step5 (mul_nonneg hCkpos.le hLnn)
    _ ≤ Ck * (S * K1 + 1) * (Real.log (x : ℝ)) ^ (3 * k) / rho ^ m := by
        have hcoef : 0 ≤ Ck * (Real.log (x : ℝ)) ^ (3 * k) / rho ^ m :=
          div_nonneg (mul_nonneg hCkpos.le hLnn) hrhom.le
        calc Ck * (Real.log (x : ℝ)) ^ (3 * k) * (S * K1 / rho ^ m)
            = (Ck * (Real.log (x : ℝ)) ^ (3 * k) / rho ^ m) * (S * K1) := by ring
          _ ≤ (Ck * (Real.log (x : ℝ)) ^ (3 * k) / rho ^ m) * (S * K1 + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) hcoef
          _ = Ck * (S * K1 + 1) * (Real.log (x : ℝ)) ^ (3 * k) / rho ^ m := by ring

/-- The `pairW`-weighted phase norm is exactly the dominating weight. -/
lemma prodW_mul_phaseNorm_eq_pairDom {k : ℕ} (F G : Fin k → ℝ → ℝ) (p : Fin k → ℝ × ℝ) :
    (∏ j : Fin k, (pairW (p j).1 * pairW (p j).2)) * pairPhaseNorm F G p = pairDom F G p := by
  rw [pairPhaseNorm, pairDom, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [pairDomCoord]
  ring

/-- **Off-cube bound for the dominating weight.** -/
theorem pairOffCube_pairDom_le {k : ℕ} (F G : Fin k → ℝ → ℝ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 2 ≤ x →
      (∫ p in (truncCubeK k x)ᶜ, pairDom F G p) ≤
        C / (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) ^ m := by
  choose CF hCF using fun j : Fin k => tail_pairW_le_all (F j) (hcsF j) (hsmF j) m
  choose CG hCG using fun j : Fin k => tail_pairW_le_all (G j) (hcsG j) (hsmG j) m
  set S : ℝ := ∑ j : Fin k, (CF j + CG j) with hSdef
  set K1 : ℝ := ∏ j : Fin k, ((1 + pairCF (F j)) * (1 + pairCF (G j))) with hK1def
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg (fun j _ => by linarith [(hCF j).1.le, (hCG j).1.le])
  have hK1nn : 0 ≤ K1 := by
    rw [hK1def]
    exact Finset.prod_nonneg (fun j _ => mul_nonneg (by linarith [pairCF_nonneg F j])
      (by linarith [pairCF_nonneg G j]))
  refine ⟨S * K1 + 1, by positivity, fun x hx2 => ?_⟩
  have hx1 : 1 < x := by omega
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx1)
  set rho : ℝ := Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi) with hrhodef
  have hrho_pos : 0 < rho := by
    rw [hrhodef]
    exact div_pos (Real.sqrt_pos.mpr hlogpos) (by positivity)
  have hrhom : 0 < rho ^ m := pow_pos hrho_pos m
  have hset_meas : MeasurableSet (truncCubeK k x)ᶜ := (measurableSet_truncCubeK k x).compl
  have hcond_meas : MeasurableSet {p : Fin k → ℝ × ℝ | ∃ j, rho ≤ |(p j).1| ∨ rho ≤ |(p j).2|} := by
    have hEq : {p : Fin k → ℝ × ℝ | ∃ j, rho ≤ |(p j).1| ∨ rho ≤ |(p j).2|}
        = ⋃ j, ((fun p : Fin k → ℝ × ℝ => |(p j).1|) ⁻¹' Set.Ici rho ∪
                (fun p : Fin k → ℝ × ℝ => |(p j).2|) ⁻¹' Set.Ici rho) := by
      ext p; simp
    rw [hEq]
    refine MeasurableSet.iUnion (fun j => MeasurableSet.union ?_ ?_)
    · exact measurableSet_Ici.preimage (((measurable_pi_apply j).fst).abs)
    · exact measurableSet_Ici.preimage (((measurable_pi_apply j).snd).abs)
  have hDomInt : Integrable (pairDom F G) := integrable_pairDom F G hcsF hsmF hcsG hsmG
  have hIntC : Integrable ({p : Fin k → ℝ × ℝ |
      ∃ j, rho ≤ |(p j).1| ∨ rho ≤ |(p j).2|}.indicator (pairDom F G)) :=
    hDomInt.indicator hcond_meas
  have step4a : (∫ p in (truncCubeK k x)ᶜ, pairDom F G p) ≤
      ∫ p, {p : Fin k → ℝ × ℝ | ∃ j, rho ≤ |(p j).1| ∨ rho ≤ |(p j).2|}.indicator
        (pairDom F G) p := by
    rw [← integral_indicator hset_meas]
    refine integral_mono (hDomInt.indicator hset_meas) hIntC (fun p => ?_)
    by_cases hp : p ∈ (truncCubeK k x)ᶜ
    · have hmem : p ∈ {q : Fin k → ℝ × ℝ | ∃ j, rho ≤ |(q j).1| ∨ rho ≤ |(q j).2|} := by
        have hsub := compl_truncCubeK_subset hp
        rw [hrhodef]
        exact hsub
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hp]
      exact Set.indicator_nonneg (fun q _ => pairDom_nonneg F G q) p
  have step4b : (∫ p, {p : Fin k → ℝ × ℝ | ∃ j, rho ≤ |(p j).1| ∨ rho ≤ |(p j).2|}.indicator
        (pairDom F G) p)
      ≤ ∑ j : Fin k, ((∫ q in {q : ℝ × ℝ | rho ≤ |q.1|}, pairDomCoord F G j q) +
            (∫ q in {q : ℝ × ℝ | rho ≤ |q.2|}, pairDomCoord F G j q)) *
          ∏ i ∈ Finset.univ.erase j, ∫ q : ℝ × ℝ, pairDomCoord F G i q := by
    have hif : (∫ p : Fin k → ℝ × ℝ, {p : Fin k → ℝ × ℝ |
          ∃ j, rho ≤ |(p j).1| ∨ rho ≤ |(p j).2|}.indicator (pairDom F G) p)
        = ∫ p : Fin k → ℝ × ℝ, (if ∃ j, rho ≤ |(p j).1| ∨ rho ≤ |(p j).2| then
            ∏ j, pairDomCoord F G j (p j) else 0) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      dsimp only
      by_cases h : ∃ j, rho ≤ |(p j).1| ∨ rho ≤ |(p j).2|
      · rw [Set.indicator_of_mem (show p ∈ {q : Fin k → ℝ × ℝ |
            ∃ j, rho ≤ |(q j).1| ∨ rho ≤ |(q j).2|} from h), if_pos h]
        rfl
      · rw [Set.indicator_of_notMem (show p ∉ {q : Fin k → ℝ × ℝ |
            ∃ j, rho ≤ |(q j).1| ∨ rho ≤ |(q j).2|} from h), if_neg h]
    rw [hif]
    exact Commons.MeasureTheory.Integral.integral_prod_indicator_cube_compl_le (pairDomCoord F G) rho
      (fun j => integrable_pairDomCoord F G hcsF hsmF hcsG hsmG j)
      (fun j q => pairDomCoord_nonneg F G j q)
  have hK1erase : ∀ j : Fin k,
      pairCF (G j) * (∏ i ∈ Finset.univ.erase j, (1 + pairCF (F i)) * (1 + pairCF (G i)))
        ≤ K1 := by
    intro j
    have hPnn : 0 ≤ ∏ i ∈ Finset.univ.erase j, (1 + pairCF (F i)) * (1 + pairCF (G i)) :=
      Finset.prod_nonneg (fun i _ => mul_nonneg (by linarith [pairCF_nonneg F i])
        (by linarith [pairCF_nonneg G i]))
    have hle : pairCF (G j) ≤ (1 + pairCF (F j)) * (1 + pairCF (G j)) := by
      have h1 := pairCF_nonneg F j
      have h2 := pairCF_nonneg G j
      nlinarith [mul_nonneg h1 h2]
    rw [hK1def, ← Finset.mul_prod_erase Finset.univ
      (fun i : Fin k => (1 + pairCF (F i)) * (1 + pairCF (G i))) (Finset.mem_univ j)]
    exact mul_le_mul_of_nonneg_right hle hPnn
  have hK1eraseF : ∀ j : Fin k,
      pairCF (F j) * (∏ i ∈ Finset.univ.erase j, (1 + pairCF (F i)) * (1 + pairCF (G i)))
        ≤ K1 := by
    intro j
    have hPnn : 0 ≤ ∏ i ∈ Finset.univ.erase j, (1 + pairCF (F i)) * (1 + pairCF (G i)) :=
      Finset.prod_nonneg (fun i _ => mul_nonneg (by linarith [pairCF_nonneg F i])
        (by linarith [pairCF_nonneg G i]))
    have hle : pairCF (F j) ≤ (1 + pairCF (F j)) * (1 + pairCF (G j)) := by
      have h1 := pairCF_nonneg F j
      have h2 := pairCF_nonneg G j
      nlinarith [mul_nonneg h1 h2]
    rw [hK1def, ← Finset.mul_prod_erase Finset.univ
      (fun i : Fin k => (1 + pairCF (F i)) * (1 + pairCF (G i))) (Finset.mem_univ j)]
    exact mul_le_mul_of_nonneg_right hle hPnn
  have hP' : ∀ j : Fin k,
      (∏ i ∈ Finset.univ.erase j, ∫ q : ℝ × ℝ, pairDomCoord F G i q) ≤
        ∏ i ∈ Finset.univ.erase j, (1 + pairCF (F i)) * (1 + pairCF (G i)) := by
    intro j
    have hInt : ∀ i : Fin k, (∫ q : ℝ × ℝ, pairDomCoord F G i q) =
        pairCF (F i) * pairCF (G i) := fun i => integral_pairDomCoord F G i
    simp only [hInt]
    refine Finset.prod_le_prod₀ (fun i _ => mul_nonneg (pairCF_nonneg F i) (pairCF_nonneg G i))
      (fun i _ => ?_)
    have h1 := pairCF_nonneg F i
    have h2 := pairCF_nonneg G i
    nlinarith [mul_nonneg h1 h2]
  have hsummand : ∀ j : Fin k,
      ((∫ q in {q : ℝ × ℝ | rho ≤ |q.1|}, pairDomCoord F G j q) +
          (∫ q in {q : ℝ × ℝ | rho ≤ |q.2|}, pairDomCoord F G j q)) *
        (∏ i ∈ Finset.univ.erase j, ∫ q : ℝ × ℝ, pairDomCoord F G i q)
      ≤ ((CF j + CG j) / rho ^ m) * K1 := by
    intro j
    have hcf : 0 ≤ CF j / rho ^ m := div_nonneg (hCF j).1.le hrhom.le
    have hcg : 0 ≤ CG j / rho ^ m := div_nonneg (hCG j).1.le hrhom.le
    have hPnn : 0 ≤ ∏ i ∈ Finset.univ.erase j, ∫ q : ℝ × ℝ, pairDomCoord F G i q :=
      Finset.prod_nonneg (fun i _ => integral_nonneg (fun q => pairDomCoord_nonneg F G i q))
    have h1 : (∫ t in {t : ℝ | rho ≤ |t|}, pairW t * ‖fourierCut (F j) t‖) ≤ CF j / rho ^ m :=
      (hCF j).2 hrho_pos
    have h2 : (∫ t in {t : ℝ | rho ≤ |t|}, pairW t * ‖fourierCut (G j) t‖) ≤ CG j / rho ^ m :=
      (hCG j).2 hrho_pos
    have hAB : (∫ q in {q : ℝ × ℝ | rho ≤ |q.1|}, pairDomCoord F G j q) +
        (∫ q in {q : ℝ × ℝ | rho ≤ |q.2|}, pairDomCoord F G j q) ≤
        (CF j / rho ^ m) * pairCF (G j) + pairCF (F j) * (CG j / rho ^ m) := by
      rw [setIntegral_pairDomCoord_fst F G j rho, setIntegral_pairDomCoord_snd F G j rho]
      exact add_le_add (mul_le_mul_of_nonneg_right h1 (pairCF_nonneg G j))
        (mul_le_mul_of_nonneg_left h2 (pairCF_nonneg F j))
    have hcoefnn : 0 ≤ (CF j / rho ^ m) * pairCF (G j) + pairCF (F j) * (CG j / rho ^ m) :=
      add_nonneg (mul_nonneg hcf (pairCF_nonneg G j)) (mul_nonneg (pairCF_nonneg F j) hcg)
    calc ((∫ q in {q : ℝ × ℝ | rho ≤ |q.1|}, pairDomCoord F G j q) +
          (∫ q in {q : ℝ × ℝ | rho ≤ |q.2|}, pairDomCoord F G j q)) *
          (∏ i ∈ Finset.univ.erase j, ∫ q : ℝ × ℝ, pairDomCoord F G i q)
        ≤ ((CF j / rho ^ m) * pairCF (G j) + pairCF (F j) * (CG j / rho ^ m)) *
          (∏ i ∈ Finset.univ.erase j, ∫ q : ℝ × ℝ, pairDomCoord F G i q) :=
          mul_le_mul_of_nonneg_right hAB hPnn
      _ ≤ ((CF j / rho ^ m) * pairCF (G j) + pairCF (F j) * (CG j / rho ^ m)) *
          (∏ i ∈ Finset.univ.erase j, (1 + pairCF (F i)) * (1 + pairCF (G i))) :=
          mul_le_mul_of_nonneg_left (hP' j) hcoefnn
      _ = (CF j / rho ^ m) * (pairCF (G j) *
            (∏ i ∈ Finset.univ.erase j, (1 + pairCF (F i)) * (1 + pairCF (G i)))) +
          (CG j / rho ^ m) * (pairCF (F j) *
            (∏ i ∈ Finset.univ.erase j, (1 + pairCF (F i)) * (1 + pairCF (G i)))) := by ring
      _ ≤ (CF j / rho ^ m) * K1 + (CG j / rho ^ m) * K1 :=
          add_le_add (mul_le_mul_of_nonneg_left (hK1erase j) hcf)
            (mul_le_mul_of_nonneg_left (hK1eraseF j) hcg)
      _ = ((CF j + CG j) / rho ^ m) * K1 := by ring
  have step5 : (∑ j : Fin k, ((∫ q in {q : ℝ × ℝ | rho ≤ |q.1|}, pairDomCoord F G j q) +
        (∫ q in {q : ℝ × ℝ | rho ≤ |q.2|}, pairDomCoord F G j q)) *
        (∏ i ∈ Finset.univ.erase j, ∫ q : ℝ × ℝ, pairDomCoord F G i q))
      ≤ S * K1 / rho ^ m := by
    calc (∑ j : Fin k, ((∫ q in {q : ℝ × ℝ | rho ≤ |q.1|}, pairDomCoord F G j q) +
          (∫ q in {q : ℝ × ℝ | rho ≤ |q.2|}, pairDomCoord F G j q)) *
          (∏ i ∈ Finset.univ.erase j, ∫ q : ℝ × ℝ, pairDomCoord F G i q))
        ≤ ∑ j : Fin k, ((CF j + CG j) / rho ^ m) * K1 :=
          Finset.sum_le_sum (fun j _ => hsummand j)
      _ = (∑ j : Fin k, (CF j + CG j)) * K1 / rho ^ m := by
          have h : ∀ j : Fin k, ((CF j + CG j) / rho ^ m) * K1 =
              ((CF j + CG j) * K1) / rho ^ m := fun j => by ring
          simp only [h]
          rw [← Finset.sum_div, Finset.sum_mul]
      _ = S * K1 / rho ^ m := by rw [hSdef]
  refine (le_trans step4a (le_trans step4b step5)).trans ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have : (S * K1 + 1) * (rho ^ m)⁻¹ = S * K1 * (rho ^ m)⁻¹ + (rho ^ m)⁻¹ := by ring
  rw [this]
  have h1 : 0 ≤ (rho ^ m)⁻¹ := by positivity
  linarith [show S * K1 * (rho ^ m)⁻¹ = (S * K1) * (rho ^ m)⁻¹ from rfl]

end Commons.NumberTheory.MaynardSieve
