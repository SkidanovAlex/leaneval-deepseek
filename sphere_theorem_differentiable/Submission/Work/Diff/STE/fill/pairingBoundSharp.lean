import Mathlib
import Submission.Work.Diff.STE.flat.pairing_sharp
import Submission.Work.Diff.STE.flat.integral_prod_shifted_family
import Submission.Work.Diff.STE.flat.norm_iteratedFDeriv_comp_prod_le
import Submission.Work.Diff.STE.flat.Sobolev.rnorm_seriesFun_rpow_le
import Submission.Work.Diff.STE.flat.nonlin_coeff_bound
import Submission.Work.Diff.STE.flat.phi_bound
import Submission.Work.Diff.STE.flat.level_step
import Submission.Work.Diff.STE.flat.level_linear
import Submission.Work.Diff.STE.flat.leibniz_l2_gen
import Submission.Work.Diff.STE.commutator_core
import Submission.Work.Diff.STE.commutator_pd
import Submission.Work.Diff.STE.pdList_mul_sub
import Submission.Work.Diff.STE.flat.CSq_symInvC_le
import Submission.Work.Diff.STE.flat.Nfun_CSq_level_bound
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.flat.pdList_eq_pdVec
import Submission.Work.Diff.STE.norm_seriesFun_le
import Submission.Work.Diff.STE.fill.symInv_garding_bounds
import Submission.Work.Diff.STE.fill.symInv_deriv_Lp_bound
import Submission.Work.Diff.STE.flat.symInv_deriv_Lp_bound
import Submission.Work.Diff.STE.flat.jet_l2_le_uniform
import Submission.Work.Diff.STE.flat.Sobolev.block_rnorm_le_rpow
import Submission.Work.Diff.STE.bessel_continuous
import Submission.Work.Diff.STE.flat.galerkin.inv_entry_le_of_quadForm
import Submission.Work.Diff.STE.flat.pairing_bound_sharp
import Submission.Work.Diff.STE.flat.comm_sharp_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.fill

open MeasureTheory BigOperators Filter

noncomputable section

set_option maxHeartbeats 10000000

/-!
# The sharp static pairing bound `Work.Diff.STE.flat.PairingBoundSharp`

This file proves `Work.Diff.STE.fill.pairingBoundSharp`, the a priori estimate left open in
`Submission/Work/Diff/STE/flat/pairing_sharp.lean`.

## Structure

* `rnorm_seriesFun_eta` -- the sharp `L^{2p}` Sobolev embedding on the torus with an explicit slack
  `η > 0` and a constant *uniform in `p` and `j`*.
* `L2re_pair_holder`, `L2re_cauchy` -- the Hölder/Cauchy–Schwarz estimates for the pairing.
* `symInvC_sup_le`, `symInvC_pd_one_sup`, `symInvC_L2_le` -- bounds for the symmetrised inverse
  metric (order `0`, order `1`, and all orders `≤ k`).
* `u_Lr_eta`, `u_L2_le` -- bounds for the iterated derivatives of the unknown.
* `comm_exponents` -- the Hölder exponent allocation for the commutator.
* `comm_bound` -- the commutator piece.
* `decomp_pairing_k` -- the level-`k` decomposition of the pairing of the DeTurck nonlinearity.
* `zero_pair_bound` -- the zeroth order piece.
* `pairingBoundSharp` -- the assembly.
-/

/-! ## The sharp Sobolev embedding with an explicit slack -/

/-- **The sharp `L^{2p}` Sobolev embedding with an explicit slack and an exponent-free
constant.**  For `η > 0` there is a constant `C`, depending only on the index type `ι` and on
`η`, such that for every real `p ≥ 1`, every real weight level `j ≥ card ι · (1/2 - 1/(2p)) + η`
and every coefficient family `γ` with `Σ_k ⟨k⟩^{2j}‖γ k‖² < ∞` one has
`‖seriesFun γ‖_{L^{2p}} ≤ C · (Σ_k ⟨k⟩^{2j}‖γ k‖²)^{1/2}`.

(The constant is *not* allowed to depend on `p` or `j`: this is exactly what the commutator
estimate needs, and it is why the slack `η` must be fixed in advance.  The proof is the dyadic
assembly `exists_bound_of_pieces_explicit` with `K = 6^{card ι / 2}` and the given `η`.) -/
theorem rnorm_seriesFun_eta {ι : Type*} [Fintype ι] [DecidableEq ι] (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (p : ℝ) (hp : 1 ≤ p) (j : ℝ),
        (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)) + η ≤ j →
        ∀ γ : (ι → ℤ) → ℂ,
          Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2) →
          Work.Diff.STE.flat.rnorm (2 * p) (Work.Diff.STE.seriesFun γ)
            ≤ C * (∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2) ^ (1 / 2 : ℝ) := by
  classical
  set K : ℝ := (6 : ℝ) ^ (((Fintype.card ι : ℕ) : ℝ) / 2) with hKdef
  refine ⟨max 1 (K * (∑' m : ℕ, ((2 : ℝ) ^ (-(2 * η))) ^ m) ^ (1 / 2 : ℝ)),
    le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro p hp j hj γ hγ
  have h2p : (2 : ℝ) ≤ 2 * p := by linarith
  have hθnn : (0 : ℝ) ≤ 1 / 2 - 1 / (2 * p) := by
    have h1 : 1 / (2 * p) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2p
    linarith
  have hcte : (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)) < j := by linarith
  have hηle : η ≤ j - (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)) := by linarith
  have hblock : ∀ (m : ℕ) (γ' : (ι → ℤ) → ℂ), Summable (fun k : ι → ℤ => ‖γ' k‖) →
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ j * ‖γ' k‖ ^ 2) →
      Work.Diff.STE.flat.rnorm (2 * p)
          (Work.Diff.STE.seriesFun (Work.Diff.STE.flat.blockCoeff m γ'))
        ≤ K * (2 : ℝ) ^ (-(m : ℝ) * η)
          * (Work.Diff.STE.flat.blockMass j m γ') ^ (1 / 2 : ℝ) := by
    intro m γ' h1 h2
    have hKle : (6 : ℝ) ^ ((Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p))) ≤ K := by
      rw [hKdef]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      calc (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p))
          ≤ (Fintype.card ι : ℝ) * (1 / 2) :=
            mul_le_mul_of_nonneg_left (by
              have : (0 : ℝ) < 2 * p := by linarith
              have h2 : 0 ≤ 1 / (2 * p) := by positivity
              linarith) (by positivity)
        _ = ((Fintype.card ι : ℕ) : ℝ) / 2 := by push_cast; ring
    have hexp : -(m : ℝ) * (j - (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)))
        ≤ -(m : ℝ) * η := by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
      nlinarith
    have h2le : (2 : ℝ) ^ (-(m : ℝ) * (j - (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p))))
        ≤ (2 : ℝ) ^ (-(m : ℝ) * η) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hb := Work.Diff.STE.flat.Sobolev.block_rnorm_le_rpow p hp j (le_of_lt hcte) m γ' h1 h2
    have hMnn : 0 ≤ (Work.Diff.STE.flat.blockMass j m γ') ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg (Work.Diff.STE.flat.blockMass_nonneg j m γ') _
    refine hb.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hMnn
    exact mul_le_mul hKle h2le (by positivity) (by positivity)
  have hmain := Work.Diff.STE.flat.exists_bound_of_pieces_explicit (ι := ι) p hp j hcte K η
    (by positivity) hη hblock
    (fun g hg => Work.Diff.STE.flat.Sobolev.tsum_annulus (E := ℂ) g hg)
    (fun g hg => Work.Diff.STE.flat.Sobolev.tsum_annulus (E := ℝ) g hg)
    (fun γ' h1 h2 => Work.Diff.STE.flat.Sobolev.summable_blockMass j γ' h2)
    (fun q hq g f hm hf hfg hsum => Work.Diff.STE.flat.Sobolev.rnorm_tsum_le q hq hm hf hfg hsum)
    γ hγ
  simpa only [hKdef] using hmain

/-! ## Elementary `L²` and Hölder estimates for the pairing -/

/-- A continuous function on the unit cube is in every `L^p`. -/
theorem memLp_of_cont_cube {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*}
    [NormedAddCommGroup E] {f : (ι → ℝ) → E} (hf : Continuous f) (p : ℝ) :
    MemLp f (ENNReal.ofReal p) (volume.restrict (unitCube (ι := ι))) := by
  haveI := Work.Diff.STE.BesselCont.isFiniteMeasure_restrict_unitCube (ι := ι)
  have hK : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem (Work.Diff.STE.BesselCont.measSet_unitCube (ι := ι))] with x hx
  exact hC x (fun i _ => ⟨(hx i (Set.mem_univ i)).1.le, (hx i (Set.mem_univ i)).2⟩)

/-- The `rpow` arithmetic of the Hölder chain: `(a^{1/p})^{1/2} = a^{1/(2p)}`. -/
private lemma rpow_half (a : ℝ) (ha : 0 ≤ a) (p : ℝ) (hp : p ≠ 0) :
    (a ^ (1 / p)) ^ (1 / 2 : ℝ) = a ^ (1 / (2 * p)) := by
  rw [← Real.rpow_mul ha]
  congr 1
  field_simp

set_option maxHeartbeats 1000000 in
/-- **Hölder on the unit cube** (Cauchy–Schwarz + two-factor Hölder), in the shape used by the
commutator estimate: `|⟨F·G, h⟩| ≤ ‖F‖_{L^{2p}} ‖G‖_{L^{2q}} ‖h‖_{L²}` when `1/p + 1/q = 1`. -/
theorem L2re_pair_holder {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ℝ) (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1)
    {F G h : (ι → ℝ) → ℂ} (hFc : Continuous F) (hGc : Continuous G) (hhc : Continuous h) :
    |Work.Diff.STE.L2re (fun x => F x * G x) h|
      ≤ Work.Diff.STE.flat.rnorm (2 * p) F * Work.Diff.STE.flat.rnorm (2 * q) G
        * Work.Diff.STE.flat.rnorm 2 h := by
  haveI := Work.Diff.STE.BesselCont.isFiniteMeasure_restrict_unitCube (ι := ι)
  have hstep1 : |Work.Diff.STE.L2re (fun x => F x * G x) h|
      ≤ ∫ x in (unitCube (ι := ι)), ‖F x‖ * ‖G x‖ * ‖h x‖ := by
    have h1 : |Work.Diff.STE.L2re (fun x => F x * G x) h|
        ≤ ‖∫ x in (unitCube (ι := ι)), (F x * G x) * star (h x)‖ := by
      have h : Work.Diff.STE.L2re (fun x => F x * G x) h
          = (∫ x in (unitCube (ι := ι)), (F x * G x) * star (h x)).re := rfl
      rw [h]
      exact Complex.abs_re_le_norm _
    refine h1.trans ?_
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [norm_mul, Complex.star_def, Complex.norm_conj]
  have h2p : (0 : ℝ) ≤ 2 := by norm_num
  have h22 : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hF1 : MemLp (fun x : ι → ℝ => ‖F x‖ * ‖G x‖) (ENNReal.ofReal 2)
      (volume.restrict (unitCube (ι := ι))) :=
    memLp_of_cont_cube (ι := ι) (hFc.norm.mul hGc.norm) 2
  have hh1 : MemLp (fun x : ι → ℝ => ‖h x‖) (ENNReal.ofReal 2)
      (volume.restrict (unitCube (ι := ι))) :=
    memLp_of_cont_cube (ι := ι) hhc.norm 2
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (unitCube (ι := ι)))
    (f := fun x : ι → ℝ => ‖F x‖ * ‖G x‖) (g := fun x : ι → ℝ => ‖h x‖) h22
    (Eventually.of_forall fun x => by positivity) (Eventually.of_forall fun x => by positivity)
    hF1 hh1
  have hpq' : p.HolderConjugate q :=
    Real.holderConjugate_iff.mpr ⟨hp, by simpa [one_div] using hpq⟩
  have hF2 : MemLp (fun x : ι → ℝ => ‖F x‖ ^ (2 : ℝ)) (ENNReal.ofReal p)
      (volume.restrict (unitCube (ι := ι))) :=
    memLp_of_cont_cube (ι := ι) ((Real.continuous_rpow_const h2p).comp hFc.norm) p
  have hG2 : MemLp (fun x : ι → ℝ => ‖G x‖ ^ (2 : ℝ)) (ENNReal.ofReal q)
      (volume.restrict (unitCube (ι := ι))) :=
    memLp_of_cont_cube (ι := ι) ((Real.continuous_rpow_const h2p).comp hGc.norm) q
  have hh2 := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (unitCube (ι := ι)))
    (f := fun x : ι → ℝ => ‖F x‖ ^ (2 : ℝ)) (g := fun x : ι → ℝ => ‖G x‖ ^ (2 : ℝ)) hpq'
    (Eventually.of_forall fun x => by positivity) (Eventually.of_forall fun x => by positivity)
    hF2 hG2
  have hMnn : 0 ≤ ∫ x in (unitCube (ι := ι)), (‖F x‖ * ‖G x‖) ^ (2 : ℝ) :=
    integral_nonneg fun x => by positivity
  have hAnn : 0 ≤ ∫ x in (unitCube (ι := ι)), ‖F x‖ ^ (2 * p) :=
    integral_nonneg fun x => by positivity
  have hBnn : 0 ≤ ∫ x in (unitCube (ι := ι)), ‖G x‖ ^ (2 * q) :=
    integral_nonneg fun x => by positivity
  have hHnn : 0 ≤ ∫ x in (unitCube (ι := ι)), ‖h x‖ ^ (2 : ℝ) :=
    integral_nonneg fun x => by positivity
  have hMform : (∫ x in (unitCube (ι := ι)), (‖F x‖ * ‖G x‖) ^ (2 : ℝ))
      = ∫ x in (unitCube (ι := ι)), ‖F x‖ ^ (2 : ℝ) * ‖G x‖ ^ (2 : ℝ) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only []
    exact Real.mul_rpow (norm_nonneg _) (norm_nonneg _)
  have hAp : (∫ x in (unitCube (ι := ι)), (‖F x‖ ^ (2 : ℝ)) ^ p)
      = ∫ x in (unitCube (ι := ι)), ‖F x‖ ^ (2 * p) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only []
    rw [← Real.rpow_mul (norm_nonneg _)]
  have hBq : (∫ x in (unitCube (ι := ι)), (‖G x‖ ^ (2 : ℝ)) ^ q)
      = ∫ x in (unitCube (ι := ι)), ‖G x‖ ^ (2 * q) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only []
    rw [← Real.rpow_mul (norm_nonneg _)]
  have hMle : (∫ x in (unitCube (ι := ι)), (‖F x‖ * ‖G x‖) ^ (2 : ℝ))
      ≤ (∫ x in (unitCube (ι := ι)), ‖F x‖ ^ (2 * p)) ^ (1 / p)
        * (∫ x in (unitCube (ι := ι)), ‖G x‖ ^ (2 * q)) ^ (1 / q) := by
    rw [← hMform, hAp, hBq] at hh2
    exact hh2
  have hroot : (∫ x in (unitCube (ι := ι)), (‖F x‖ * ‖G x‖) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ (∫ x in (unitCube (ι := ι)), ‖F x‖ ^ (2 * p)) ^ (1 / (2 * p))
        * (∫ x in (unitCube (ι := ι)), ‖G x‖ ^ (2 * q)) ^ (1 / (2 * q)) := by
    have h1 : ((∫ x in (unitCube (ι := ι)), ‖F x‖ ^ (2 * p)) ^ (1 / p)
        * (∫ x in (unitCube (ι := ι)), ‖G x‖ ^ (2 * q)) ^ (1 / q)) ^ (1 / 2 : ℝ)
        = (∫ x in (unitCube (ι := ι)), ‖F x‖ ^ (2 * p)) ^ (1 / (2 * p))
          * (∫ x in (unitCube (ι := ι)), ‖G x‖ ^ (2 * q)) ^ (1 / (2 * q)) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hAnn _) (Real.rpow_nonneg hBnn _),
        rpow_half _ hAnn p (by positivity), rpow_half _ hBnn q (by positivity)]
    rw [← h1]
    exact Real.rpow_le_rpow hMnn hMle (by norm_num)
  simp only [Work.Diff.STE.flat.rnorm]
  calc |Work.Diff.STE.L2re (fun x => F x * G x) h|
      ≤ ∫ x in (unitCube (ι := ι)), (‖F x‖ * ‖G x‖) * ‖h x‖ := hstep1
    _ ≤ (∫ x in (unitCube (ι := ι)), (‖F x‖ * ‖G x‖) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
          * (∫ x in (unitCube (ι := ι)), ‖h x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hcs
    _ ≤ ((∫ x in (unitCube (ι := ι)), ‖F x‖ ^ (2 * p)) ^ (1 / (2 * p))
          * (∫ x in (unitCube (ι := ι)), ‖G x‖ ^ (2 * q)) ^ (1 / (2 * q)))
          * (∫ x in (unitCube (ι := ι)), ‖h x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hroot (Real.rpow_nonneg hHnn _)

set_option maxHeartbeats 1000000 in
/-- **Cauchy–Schwarz for `L2re`.** -/
theorem L2re_cauchy {ι : Type*} [Fintype ι] [DecidableEq ι] {F G : (ι → ℝ) → ℂ}
    (hF : Continuous F) (hG : Continuous G) :
    |Work.Diff.STE.L2re F G| ≤ Real.sqrt (∫ x in unitCube, ‖F x‖ ^ (2 : ℝ))
      * Real.sqrt (∫ x in unitCube, ‖G x‖ ^ (2 : ℝ)) := by
  haveI := Work.Diff.STE.BesselCont.isFiniteMeasure_restrict_unitCube (ι := ι)
  have hstep1 : |Work.Diff.STE.L2re F G| ≤ ∫ x in unitCube, ‖F x‖ * ‖G x‖ := by
    have h1 : |Work.Diff.STE.L2re F G| ≤ ‖∫ x in unitCube, F x * star (G x)‖ := by
      have h : Work.Diff.STE.L2re F G = (∫ x in unitCube, F x * star (G x)).re := rfl
      rw [h]
      exact Complex.abs_re_le_norm _
    refine h1.trans ?_
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [norm_mul, Complex.star_def, Complex.norm_conj]
  have h22 : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have h1 : MemLp (fun x : ι → ℝ => ‖F x‖) (ENNReal.ofReal 2)
      (volume.restrict (unitCube (ι := ι))) := memLp_of_cont_cube (ι := ι) hF.norm 2
  have h2 : MemLp (fun x : ι → ℝ => ‖G x‖) (ENNReal.ofReal 2)
      (volume.restrict (unitCube (ι := ι))) := memLp_of_cont_cube (ι := ι) hG.norm 2
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (unitCube (ι := ι)))
    (f := fun x : ι → ℝ => ‖F x‖) (g := fun x : ι → ℝ => ‖G x‖) h22
    (Eventually.of_forall fun x => by positivity) (Eventually.of_forall fun x => by positivity) h1 h2
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hcs
  exact hstep1.trans hcs

/-- The `rpow`-exponent `2` integral is the usual one. -/
private lemma sqrt_integral_two {ι : Type*} [Fintype ι] (F : (ι → ℝ) → ℂ) :
    Real.sqrt (∫ x in unitCube, ‖F x‖ ^ (2 : ℝ))
      = Real.sqrt (∫ x in unitCube, ‖F x‖ ^ 2) := by
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only []
  exact Real.rpow_two (‖F x‖)

/-! ## Bounds for the symmetrised inverse metric -/

/-- **Sup bound of the symmetrised inverse metric.**  Uniform ellipticity with constant `lam > 0`
alone gives `|(reMat u)⁻¹| ≤ lam⁻¹` entrywise, hence `‖symInvC c a b‖ ≤ lam⁻¹`: no energy
hypothesis is needed. -/
theorem symInvC_sup_le {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
      Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM c) ≤ B ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
      ∀ (a b : Fin n) (x : Fin n → ℝ), ‖Work.Diff.STE.flat.symInvC c a b x‖ ≤ C := by
  refine ⟨lam⁻¹, by positivity, ?_⟩
  intro N c hc hen hell a b x
  have hG : ∀ p q : Fin n,
      |((Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x))⁻¹) p q| ≤ lam⁻¹ :=
    fun p q => Work.Diff.STE.flat.galerkin.inv_entry_le_of_quadForm _ hlam (hell x) p q
  simp only [Work.Diff.STE.flat.symInvC_apply, Work.Diff.STE.flat.symInvR_apply,
    Complex.norm_real, Real.norm_eq_abs]
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  refine (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr ?_
  nlinarith [abs_add_le (((Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x))⁻¹) a b)
    (((Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x))⁻¹) b a), hG a b, hG b a]

/-- **Sup bound for the first derivatives of the symmetrised inverse metric.** -/
theorem symInvC_pd_one_sup {n : ℕ} (hn : 1 ≤ n) (k : ℕ)
    (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
      Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM c) ≤ B ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
      ∀ (a b i : Fin n) (x : Fin n → ℝ),
        ‖Work.Diff.STE.pd i (Work.Diff.STE.flat.symInvC c a b) x‖ ≤ C := by
  obtain ⟨lam', hlam', Cg, hCg, hgb⟩ := symInv_garding_bounds hn k hk lam hlam B hB
  refine ⟨Cg, hCg, ?_⟩
  intro N c hc hen hell a b i x
  obtain ⟨hsmR, _hsmC, _hperR, _hperC, hpdr, _hell⟩ := hgb N c hc hen hell
  have hdiff : DifferentiableAt ℝ (Work.Diff.STE.flat.symInvR c a b) x :=
    ((hsmR a b).differentiable (by simp)).differentiableAt
  have hgd := Work.Diff.STE.ga_pd_ofReal i (Work.Diff.STE.flat.symInvR c a b) x hdiff
  have h1 : Work.Diff.STE.pd i (Work.Diff.STE.flat.symInvC c a b) x
      = ((Work.Diff.STE.pdR i (Work.Diff.STE.flat.symInvR c a b) x : ℝ) : ℂ) := hgd
  rw [h1, Complex.norm_real, Real.norm_eq_abs]
  exact hpdr a b i x

/-- **`L²` bound for the derivatives of the symmetrised inverse metric at the full level `k`.**
Direct Parseval computation from the level-`k` coefficient bound `CSq_symInvC_le`. -/
theorem symInvC_L2_le {n : ℕ} (hn : 1 ≤ n) (k : ℕ)
    (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
      Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM c) ≤ B ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
      ∀ (a b : Fin n) (q : List (Fin n)), q.length ≤ k →
        (∫ x in Work.Diff.STE.unitCube,
            ‖Work.Diff.STE.pdList q (fun y => Work.Diff.STE.flat.symInvC c a b y) x‖ ^ 2)
          ≤ C := by
  have hσ : Work.Diff.STE.flat.sob n ≤ k := sob_le_of_card hk
  obtain ⟨Ccsq, hCcsq, hCSQ⟩ := Work.Diff.STE.flat.CSq_symInvC_le hn k hσ lam hlam B hB
  refine ⟨((2 * Real.pi) ^ 2) ^ k * Ccsq, by positivity, ?_⟩
  intro N c hc hen hell a b q hq
  set f : (Fin n → ℝ) → ℂ := fun y => Work.Diff.STE.flat.symInvC c a b y with hfdef
  have hsmper := Work.Diff.STE.flat.symInvC_contDiff_periodic hσ hB hlam hc hen hell a b
  have hfsm : ContDiff ℝ (⊤ : ℕ∞) f := hsmper.1
  have hfper : Work.Diff.STE.Periodic1 f := hsmper.2
  have hcsq : Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff f) ≤ Ccsq :=
    hCSQ N c hc hen hell a b
  have hfd : ∀ K : ℕ, Summable (fun m : Fin n → ℤ =>
      (Work.Diff.STE.wt m) ^ K * ‖Work.Diff.STE.fourierCoeff f m‖ ^ 2) :=
    fun K => Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff f hfsm hfper K
  have hfl1 : ∀ K : ℕ, Summable (fun m : Fin n → ℤ =>
      (Work.Diff.STE.wt m) ^ K * ‖Work.Diff.STE.fourierCoeff f m‖) :=
    fun K => Work.Diff.STE.flat.invJet_summable_moment_of_wt_sq _ hfd K
  have hFser : f = Work.Diff.STE.seriesFun (Work.Diff.STE.fourierCoeff f) :=
    funext fun x => (Work.Diff.STE.flat.seriesFun_fourierCoeff f hfsm hfper x).symm
  have hpd : Work.Diff.STE.pdList q f
      = Work.Diff.STE.seriesFun (Work.Diff.STE.dmulV q (Work.Diff.STE.fourierCoeff f)) := by
    conv_lhs => rw [hFser]
    exact funext fun x => Work.Diff.STE.pdList_seriesFun q (Work.Diff.STE.fourierCoeff f) hfl1 x
  have hdsum : Summable (fun m : Fin n → ℤ =>
      ‖Work.Diff.STE.dmulV q (Work.Diff.STE.fourierCoeff f) m‖) := by
    simpa using Work.Diff.STE.summable_dmulV q (Work.Diff.STE.fourierCoeff f) hfl1 0
  have hpar := Work.Diff.STE.integral_normSq_seriesFun
    (Work.Diff.STE.dmulV q (Work.Diff.STE.fourierCoeff f)) hdsum
  have hmass := Work.Diff.STE.flat.summable_wt_dmulV_le q 0 k (Work.Diff.STE.fourierCoeff f)
    (by simpa using hq) (hfd k)
  rw [hpd, hpar]
  have h1 : (∑' m : Fin n → ℤ, ‖Work.Diff.STE.dmulV q (Work.Diff.STE.fourierCoeff f) m‖ ^ 2)
      = ∑' m : Fin n → ℤ, (Work.Diff.STE.wt m) ^ (0 : ℝ)
          * ‖Work.Diff.STE.dmulV q (Work.Diff.STE.fourierCoeff f) m‖ ^ 2 := by
    refine tsum_congr fun m => ?_
    rw [Real.rpow_zero, one_mul]
  rw [h1]
  have h2pi : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  calc ∑' m : Fin n → ℤ, (Work.Diff.STE.wt m) ^ (0 : ℝ)
        * ‖Work.Diff.STE.dmulV q (Work.Diff.STE.fourierCoeff f) m‖ ^ 2
      ≤ ((2 * Real.pi) ^ 2) ^ q.length * ∑' m : Fin n → ℤ,
          (Work.Diff.STE.wt m) ^ k * ‖Work.Diff.STE.fourierCoeff f m‖ ^ 2 := hmass.2
    _ = ((2 * Real.pi) ^ 2) ^ q.length * Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff f) := by
        rw [Work.Diff.STE.CSq]
    _ ≤ ((2 * Real.pi) ^ 2) ^ q.length * Ccsq := mul_le_mul_of_nonneg_left hcsq (by positivity)
    _ ≤ ((2 * Real.pi) ^ 2) ^ k * Ccsq :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h2pi hq) hCcsq

/-! ## Bounds for the unknown -/

/-- **The sharp `L^r` bound for the derivatives of the unknown, with an explicit slack and a
constant uniform in the order `m` and the exponent `r`.**  The weight level used is `k - m`
(so that the level-`k` energy suffices and the bound carries the factor `B` rather than
`√(1 + ENormSqFull (k+1))`). -/
theorem u_Lr_eta {n : ℕ} (k : ℕ) (B : ℝ) (hB : 0 ≤ B) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
        (∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
        Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM c) ≤ B ^ 2 →
        ∀ (m : ℕ) (r : ℝ), 2 ≤ r →
          (m : ℝ) + (n : ℝ) / 2 - (n : ℝ) / r + η ≤ (k : ℝ) →
          ∀ (q : List (Fin n)), q.length = m → ∀ (i j : Fin n),
            (∫ x in Work.Diff.STE.unitCube,
                ‖Work.Diff.STE.pdList q
                  (fun y => Work.Diff.STE.Flat.seriesFunM c y i j) x‖ ^ r) ^ (1 / r)
              ≤ C * B := by
  classical
  have hη0 : 0 < η := hη
  obtain ⟨Csob, hCsob, hSob⟩ := rnorm_seriesFun_eta (ι := Fin n) η hη
  obtain ⟨Ccsq, hCcsq, hCSQ⟩ := Work.Diff.STE.CSq_le_ENormSq_seriesFun (ι := Fin n) k
  refine ⟨Csob * (2 * Real.pi) ^ k * Real.sqrt Ccsq + 1, by positivity, ?_⟩
  intro N c hc hen m r hr hmq q hqlen i j
  have hmk : m < k := by
    have h1 : (m : ℝ) < (k : ℝ) := by
      have h2 : (n : ℝ) / r ≤ (n : ℝ) / 2 := by
        have h1 : (1 : ℝ) / r ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hr
        have h3 : (n : ℝ) * ((1 : ℝ) / r) ≤ (n : ℝ) * (1 / 2) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)
        calc (n : ℝ) / r = (n : ℝ) * ((1 : ℝ) / r) := by rw [div_eq_mul_one_div]
          _ ≤ (n : ℝ) * (1 / 2) := h3
          _ = (n : ℝ) / 2 := by rw [div_eq_mul_one_div]; ring
      have h3 : (0 : ℝ) ≤ (n : ℝ) / 2 - (n : ℝ) / r := by linarith
      have h5 : (m : ℝ) + η ≤ (k : ℝ) := by linarith [hmq, h3]
      linarith [h5, hη]
    exact_mod_cast h1
  have hkle : q.length ≤ k := by omega
  have hmom : ∀ M : ℕ, Summable (fun k' : Fin n → ℤ =>
      (Work.Diff.STE.wt k') ^ M * ‖c k' i j‖) :=
    fun M => Work.Diff.STE.flat.summable_moment_box c hc i j M
  have hfun : (fun y : Fin n → ℝ => Work.Diff.STE.Flat.seriesFunM c y i j)
      = Work.Diff.STE.seriesFun (fun μ : Fin n → ℤ => c μ i j) := by
    funext y; rw [Work.Diff.STE.Flat.seriesFunM_apply]
  have hpd : Work.Diff.STE.pdList q (fun y => Work.Diff.STE.Flat.seriesFunM c y i j)
      = Work.Diff.STE.seriesFun
          (Work.Diff.STE.dmulV q (fun μ : Fin n → ℤ => c μ i j)) := by
    rw [hfun]
    exact funext fun x => Work.Diff.STE.pdList_seriesFun q (fun μ => c μ i j) hmom x
  set γ : (Fin n → ℤ) → ℂ := fun μ => c μ i j with hγdef
  have hγmom : ∀ M : ℕ, Summable (fun μ : Fin n → ℤ => (Work.Diff.STE.wt μ) ^ M * ‖γ μ‖) := by
    intro M; rw [hγdef]; exact hmom M
  have hγ2 : Summable (fun μ : Fin n → ℤ => (Work.Diff.STE.wt μ) ^ k * ‖γ μ‖ ^ 2) :=
    Work.Diff.STE.summable_wt_pow_mul_norm_sq γ hγmom k
  -- the level at which the weighted mass is taken
  set j₀ : ℝ := (k : ℝ) - (m : ℝ) with hj₀def
  have hr2 : 2 * (r / 2) = r := by ring
  have hsobcond : (Fintype.card (Fin n) : ℝ) * (1 / 2 - 1 / (2 * (r / 2))) + η ≤ j₀ := by
    have hcard : (Fintype.card (Fin n) : ℝ) = (n : ℝ) := by simp
    have h1 : (Fintype.card (Fin n) : ℝ) * (1 / 2 - 1 / (2 * (r / 2))) + η
        = (n : ℝ) / 2 - (n : ℝ) / r + η := by
      rw [hcard, hr2]; ring
    rw [hj₀def, h1]
    linarith [hmq]
  have hjq : j₀ + (q.length : ℝ) ≤ (k : ℝ) := by
    rw [hj₀def, hqlen]
    linarith
  have hmass := Work.Diff.STE.flat.summable_wt_dmulV_le q j₀ k γ hjq hγ2
  have hγfun : Work.Diff.STE.seriesFun γ = fun y => Work.Diff.STE.Flat.seriesFunM c y i j := by
    rw [hγdef]; exact hfun.symm
  rw [hpd]
  have hsobr := hSob (r / 2) (by linarith) j₀ hsobcond
      (Work.Diff.STE.dmulV q γ) hmass.1
  rw [hr2] at hsobr
  simp only [Work.Diff.STE.flat.rnorm] at hsobr
  -- bound the weighted mass by `B`
  have hCSQk : Work.Diff.STE.CSq k γ
      ≤ Ccsq * Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM c) := by
    have hcs := hCSQ γ hγmom
    rw [hγfun] at hcs
    have h1 : Work.Diff.STE.ENormSq k
          (fun y => Work.Diff.STE.Flat.seriesFunM c y i j)
        ≤ Work.Diff.STE.Flat.ENormSqM k (Work.Diff.STE.Flat.seriesFunM c) :=
      Work.Diff.STE.flat.ENormSq_le_ENormSqM _ i j
    have h2 : Work.Diff.STE.ENormSq 0
          (fun y => Work.Diff.STE.Flat.seriesFunM c y i j)
        ≤ Work.Diff.STE.Flat.ENormSqM 0 (Work.Diff.STE.Flat.seriesFunM c) :=
      Work.Diff.STE.flat.ENormSq_le_ENormSqM (j := 0) _ i j
    refine hcs.trans ?_
    rw [Work.Diff.STE.Flat.ENormSqFull]
    exact mul_le_mul_of_nonneg_left (by linarith [h1, h2]) hCcsq
  have hsqrt : (∑' μ : Fin n → ℤ, (Work.Diff.STE.wt μ) ^ j₀
        * ‖Work.Diff.STE.dmulV q γ μ‖ ^ 2) ^ (1 / 2 : ℝ)
      ≤ (2 * Real.pi) ^ k * (Real.sqrt Ccsq * B) := by
    have hnn : 0 ≤ ∑' μ : Fin n → ℤ, (Work.Diff.STE.wt μ) ^ j₀
        * ‖Work.Diff.STE.dmulV q γ μ‖ ^ 2 :=
      tsum_nonneg fun μ => mul_nonneg (Real.rpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos μ)) _)
        (sq_nonneg _)
    have h1 : (∑' μ : Fin n → ℤ, (Work.Diff.STE.wt μ) ^ j₀
          * ‖Work.Diff.STE.dmulV q γ μ‖ ^ 2)
        ≤ ((2 * Real.pi) ^ 2) ^ q.length * Work.Diff.STE.CSq k γ := hmass.2
    have h2 : ((2 * Real.pi) ^ 2) ^ q.length * Work.Diff.STE.CSq k γ
        ≤ ((2 * Real.pi) ^ 2) ^ k * (Ccsq * B ^ 2) := by
      refine mul_le_mul ?_ ?_ (Work.Diff.STE.CSq_nonneg k γ) (by positivity)
      · exact pow_le_pow_right₀ (by nlinarith [Real.pi_gt_three]) hkle
      · exact hCSQk.trans (mul_le_mul_of_nonneg_left hen hCcsq)
    have h3 : (((2 * Real.pi) ^ 2) ^ k * (Ccsq * B ^ 2)) ^ (1 / 2 : ℝ)
        = (2 * Real.pi) ^ k * (Real.sqrt Ccsq * B) := by
      have hA : (0 : ℝ) ≤ ((2 * Real.pi) ^ 2) ^ k := by positivity
      have hB' : (0 : ℝ) ≤ Ccsq * B ^ 2 := by positivity
      rw [Real.mul_rpow hA hB', ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      have h1 : Real.sqrt ((((2 : ℝ) * Real.pi) ^ 2) ^ k) = (2 * Real.pi) ^ k := by
        rw [show (((2 : ℝ) * Real.pi) ^ 2) ^ k = (((2 : ℝ) * Real.pi) ^ k) ^ 2 from by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 k]]
        exact Real.sqrt_sq (by positivity)
      rw [h1, Real.sqrt_mul hCcsq, Real.sqrt_sq hB]
    calc (∑' μ : Fin n → ℤ, (Work.Diff.STE.wt μ) ^ j₀
          * ‖Work.Diff.STE.dmulV q γ μ‖ ^ 2) ^ (1 / 2 : ℝ)
        ≤ (((2 * Real.pi) ^ 2) ^ q.length * Work.Diff.STE.CSq k γ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hnn h1 (by norm_num)
      _ ≤ (((2 * Real.pi) ^ 2) ^ k * (Ccsq * B ^ 2)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow
            (mul_nonneg (by positivity) (Work.Diff.STE.CSq_nonneg k γ)) h2 (by norm_num)
      _ = (2 * Real.pi) ^ k * (Real.sqrt Ccsq * B) := h3
  refine hsobr.trans ?_
  refine (mul_le_mul_of_nonneg_left hsqrt hCsob).trans ?_
  have hAs : Csob * ((2 * Real.pi) ^ k * (Real.sqrt Ccsq * B))
      = (Csob * (2 * Real.pi) ^ k * Real.sqrt Ccsq) * B := by ring
  rw [hAs]
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hB

/-- **The exact `L²` bounds for the derivatives of the unknown.**  For orders `≤ k` the level-`k`
energy suffices; for order `k+1` the level-`(k+1)` energy is used. -/
theorem u_L2_le {n : ℕ} (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
        (∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
        Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM c) ≤ B ^ 2 →
        (∀ (q : List (Fin n)) (i j : Fin n), q.length ≤ k →
            (∫ x in Work.Diff.STE.unitCube,
                ‖Work.Diff.STE.pdList q
                  (fun y => Work.Diff.STE.Flat.seriesFunM c y i j) x‖ ^ 2) ^ (1 / 2 : ℝ)
              ≤ C * B) ∧
        (∀ (q : List (Fin n)) (i j : Fin n), q.length = k + 1 →
            (∫ x in Work.Diff.STE.unitCube,
                ‖Work.Diff.STE.pdList q
                  (fun y => Work.Diff.STE.Flat.seriesFunM c y i j) x‖ ^ 2) ^ (1 / 2 : ℝ)
              ≤ C * (1 + (Work.Diff.STE.Flat.ENormSqFull (k + 1)
                  (Work.Diff.STE.Flat.seriesFunM c)) ^ (1 / 2 : ℝ))) := by
  have hk1 : 1 ≤ k := by
    have h := hk
    simp only [Fintype.card_fin] at h
    omega
  obtain ⟨Cj, hCj, hj⟩ := Work.Diff.STE.flat.jet_l2_le_uniform (n := n) (s := k) hk1
  refine ⟨max 1 (Real.sqrt Cj), le_trans zero_le_one (le_max_left _ _), ?_⟩
  have hCmax : Real.sqrt Cj ≤ max 1 (Real.sqrt Cj) := le_max_right _ _
  intro N c hc hen
  constructor
  · intro q i j hq
    have hmom : ∀ M : ℕ, Summable (fun k' : Fin n → ℤ =>
        (Work.Diff.STE.wt k') ^ M * ‖c k' i j‖) :=
      fun M => Work.Diff.STE.flat.summable_moment_box c hc i j M
    have hget : Work.Diff.STE.pdList q (fun y => Work.Diff.STE.Flat.seriesFunM c y i j)
        = Work.Diff.STE.pdVec q.length (fun t : Fin q.length => q.get t)
            (fun y => Work.Diff.STE.Flat.seriesFunM c y i j) :=
      Work.Diff.STE.flat.pdList_eq_pdVec q _
    rw [hget, ← Real.sqrt_eq_rpow]
    have h := hj q.length hq N c hc (fun t : Fin q.length => q.get t) i j
    have hstep : Real.sqrt (∫ x in Work.Diff.STE.unitCube,
          ‖Work.Diff.STE.pdVec q.length (fun t : Fin q.length => q.get t)
            (fun y => Work.Diff.STE.Flat.seriesFunM c y i j) x‖ ^ 2)
        ≤ Real.sqrt Cj * B := by
      refine (Real.sqrt_le_sqrt (h.trans (mul_le_mul_of_nonneg_left hen hCj))).trans ?_
      rw [Real.sqrt_mul hCj, Real.sqrt_sq hB]
    refine hstep.trans ?_
    refine mul_le_mul_of_nonneg_right hCmax hB
  · intro q i j hq
    have h1 : (∫ x in Work.Diff.STE.unitCube,
          ‖Work.Diff.STE.pdList q (fun y => Work.Diff.STE.Flat.seriesFunM c y i j) x‖ ^ 2)
        ≤ Work.Diff.STE.ENormSq q.length
            (fun y => Work.Diff.STE.Flat.seriesFunM c y i j) :=
      Work.Diff.STE.cm_integral_pdList_le_ENormSq q _
    have h2 : Work.Diff.STE.ENormSq q.length
          (fun y => Work.Diff.STE.Flat.seriesFunM c y i j)
        ≤ Work.Diff.STE.Flat.ENormSqM (k + 1) (Work.Diff.STE.Flat.seriesFunM c) := by
      rw [hq]
      exact Work.Diff.STE.flat.ENormSq_le_ENormSqM (Work.Diff.STE.Flat.seriesFunM c) i j
    have h3 : Work.Diff.STE.Flat.ENormSqM (k + 1) (Work.Diff.STE.Flat.seriesFunM c)
        ≤ Work.Diff.STE.Flat.ENormSqFull (k + 1) (Work.Diff.STE.Flat.seriesFunM c) :=
      Work.Diff.STE.flat.ENormSqM_le_ENormSqFull (k + 1) _
    have hE0 : (0 : ℝ) ≤ Real.sqrt (Work.Diff.STE.Flat.ENormSqFull (k + 1)
        (Work.Diff.STE.Flat.seriesFunM c)) := Real.sqrt_nonneg _
    rw [← Real.sqrt_eq_rpow]
    refine (Real.sqrt_le_sqrt (h1.trans (h2.trans h3))).trans ?_
    calc Real.sqrt (Work.Diff.STE.Flat.ENormSqFull (k + 1) (Work.Diff.STE.Flat.seriesFunM c))
        ≤ max 1 (Real.sqrt Cj)
            * (1 + (Work.Diff.STE.Flat.ENormSqFull (k + 1)
                (Work.Diff.STE.Flat.seriesFunM c)) ^ (1 / 2 : ℝ)) := by
          rw [← Real.sqrt_eq_rpow]
          have h1le : (1 : ℝ) ≤ max 1 (Real.sqrt Cj) := le_max_left _ _
          nlinarith [hE0, h1le, mul_le_mul_of_nonneg_right h1le (by linarith : (0:ℝ) ≤ 1 + Real.sqrt _)]


/-! ## The sharp `L^r` bound for the symmetrised inverse metric (uniform) -/

/-- **The sharp `L^r` bound for the derivatives of the symmetrised inverse metric, with an
explicit slack and a constant uniform in the order and the exponent.** -/
theorem symInvC_Lr_eta {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
        (∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
        Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM c) ≤ B ^ 2 →
        (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
        ∀ (a b : Fin n) (q : List (Fin n)) (r : ℝ), 2 ≤ r →
          (q.length : ℝ) + (n : ℝ) / 2 - (n : ℝ) / r + η ≤ (k : ℝ) →
          (∫ x in Work.Diff.STE.unitCube,
              ‖Work.Diff.STE.pdList q (fun y => Work.Diff.STE.flat.symInvC c a b y) x‖ ^ r)
            ^ (1 / r) ≤ C := by
  obtain ⟨Csob, hCsob, hSob⟩ := rnorm_seriesFun_eta (ι := Fin n) η hη
  obtain ⟨Cinv, hCinv, hCinv'⟩ :=
    Work.Diff.STE.flat.CSq_symInvC_le hn k (sob_le_of_card hk) lam hlam B hB
  obtain ⟨_lam', _hlam', _Kg, _hKg, hgb⟩ :=
    Work.Diff.STE.fill.symInv_garding_bounds hn k hk lam hlam B hB
  refine ⟨Csob * (2 * Real.pi) ^ k * Real.sqrt Cinv, by positivity, ?_⟩
  intro N c hc hE hell a b q r hr hkq
  obtain ⟨_hsmR, hsmC, _hperR, hperC, _hpdr, _hgard⟩ := hgb N c hc hE hell
  set γ : (Fin n → ℤ) → ℂ :=
    Work.Diff.STE.fourierCoeff (fun y : Fin n → ℝ => Work.Diff.STE.flat.symInvC c a b y)
    with hγdef
  have hsmF : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => Work.Diff.STE.flat.symInvC c a b y) :=
    hsmC a b
  have hperF : Work.Diff.STE.Periodic1
      (fun y : Fin n → ℝ => Work.Diff.STE.flat.symInvC c a b y) := hperC a b
  have hFeq : Work.Diff.STE.seriesFun γ
      = fun y : Fin n → ℝ => Work.Diff.STE.flat.symInvC c a b y :=
    funext (Work.Diff.STE.flat.seriesFun_fourierCoeff _ hsmF hperF)
  have hmom2 : ∀ K : ℕ, Summable (fun m : Fin n → ℤ =>
      (Work.Diff.STE.wt m) ^ K * ‖γ m‖ ^ 2) :=
    fun K => Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff _ hsmF hperF K
  have hmom1 : ∀ K : ℕ, Summable (fun m : Fin n → ℤ =>
      (Work.Diff.STE.wt m) ^ K * ‖γ m‖) :=
    fun K => Work.Diff.STE.flat.invJet_summable_moment_of_wt_sq γ hmom2 K
  have hpdall : Work.Diff.STE.pdList q (fun y : Fin n → ℝ =>
        Work.Diff.STE.flat.symInvC c a b y)
      = Work.Diff.STE.seriesFun (Work.Diff.STE.dmulV q γ) := by
    rw [← hFeq]
    exact funext fun x => Work.Diff.STE.pdList_seriesFun q γ hmom1 x
  have hlen : q.length < k := by
    have h2 : (n : ℝ) / r ≤ (n : ℝ) / 2 := by
      have h1 : (1 : ℝ) / r ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hr
      have h3 : (n : ℝ) * ((1 : ℝ) / r) ≤ (n : ℝ) * (1 / 2) :=
        mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)
      calc (n : ℝ) / r = (n : ℝ) * ((1 : ℝ) / r) := by rw [div_eq_mul_one_div]
        _ ≤ (n : ℝ) * (1 / 2) := h3
        _ = (n : ℝ) / 2 := by rw [div_eq_mul_one_div]; ring
    have h3 : (0 : ℝ) ≤ (n : ℝ) / 2 - (n : ℝ) / r := by linarith
    have h1 : (q.length : ℝ) < (k : ℝ) := by linarith
    exact_mod_cast h1
  set j₀ : ℝ := (k : ℝ) - (q.length : ℝ) with hj₀def
  have hr2 : 2 * (r / 2) = r := by ring
  have hcond : (Fintype.card (Fin n) : ℝ) * (1 / 2 - 1 / (2 * (r / 2))) + η ≤ j₀ := by
    have hcard : (Fintype.card (Fin n) : ℝ) = (n : ℝ) := by simp
    have h1 : (Fintype.card (Fin n) : ℝ) * (1 / 2 - 1 / (2 * (r / 2))) + η
        = (n : ℝ) / 2 - (n : ℝ) / r + η := by
      rw [hcard, hr2]; ring
    rw [hj₀def, h1]
    linarith [hkq]
  have hγ2 : Summable (fun μ : Fin n → ℤ =>
      (Work.Diff.STE.wt μ) ^ k * ‖γ μ‖ ^ 2) := hmom2 k
  have hjq : j₀ + (q.length : ℝ) ≤ (k : ℝ) := by
    rw [hj₀def]; linarith
  have hmass := Work.Diff.STE.flat.summable_wt_dmulV_le q j₀ k γ hjq hγ2
  have hsobr := hSob (r / 2) (by linarith) j₀ hcond (Work.Diff.STE.dmulV q γ) hmass.1
  rw [hr2] at hsobr
  simp only [Work.Diff.STE.flat.rnorm] at hsobr
  rw [hpdall]
  refine hsobr.trans ?_
  have h1 : (∑' μ : Fin n → ℤ, (Work.Diff.STE.wt μ) ^ j₀
        * ‖Work.Diff.STE.dmulV q γ μ‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 2) ^ q.length * Work.Diff.STE.CSq k γ := hmass.2
  have h2 : Work.Diff.STE.CSq k γ ≤ Cinv := hCinv' N c hc hE hell a b
  have hnn : 0 ≤ ∑' μ : Fin n → ℤ, (Work.Diff.STE.wt μ) ^ j₀
      * ‖Work.Diff.STE.dmulV q γ μ‖ ^ 2 :=
    tsum_nonneg fun μ => mul_nonneg (Real.rpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos μ)) _)
      (sq_nonneg _)
  have h3 : (∑' μ : Fin n → ℤ, (Work.Diff.STE.wt μ) ^ j₀
        * ‖Work.Diff.STE.dmulV q γ μ‖ ^ 2) ^ (1 / 2 : ℝ)
      ≤ (2 * Real.pi) ^ k * Real.sqrt Cinv := by
    have h4 : ((2 * Real.pi) ^ 2) ^ q.length * Work.Diff.STE.CSq k γ
        ≤ ((2 * Real.pi) ^ 2) ^ k * Cinv := by
      refine mul_le_mul ?_ h2 (Work.Diff.STE.CSq_nonneg k γ) (by positivity)
      exact pow_le_pow_right₀ (by nlinarith [Real.pi_gt_three]) (le_of_lt hlen)
    have h5 : (((2 * Real.pi) ^ 2) ^ k * Cinv) ^ (1 / 2 : ℝ)
        = (2 * Real.pi) ^ k * Real.sqrt Cinv := by
      have hA : (0 : ℝ) ≤ ((2 * Real.pi) ^ 2) ^ k := by positivity
      rw [Real.mul_rpow hA hCinv, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      have h6 : Real.sqrt ((((2 : ℝ) * Real.pi) ^ 2) ^ k) = (2 * Real.pi) ^ k := by
        rw [show (((2 : ℝ) * Real.pi) ^ 2) ^ k = (((2 : ℝ) * Real.pi) ^ k) ^ 2 from by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 k]]
        exact Real.sqrt_sq (by positivity)
      rw [h6]
    calc (∑' μ : Fin n → ℤ, (Work.Diff.STE.wt μ) ^ j₀
          * ‖Work.Diff.STE.dmulV q γ μ‖ ^ 2) ^ (1 / 2 : ℝ)
        ≤ (((2 * Real.pi) ^ 2) ^ q.length * Work.Diff.STE.CSq k γ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hnn h1 (by norm_num)
      _ ≤ (((2 * Real.pi) ^ 2) ^ k * Cinv) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (mul_nonneg (by positivity) (Work.Diff.STE.CSq_nonneg k γ)) h4
            (by norm_num)
      _ = (2 * Real.pi) ^ k * Real.sqrt Cinv := h5
  calc Csob * (∑' μ : Fin n → ℤ, (Work.Diff.STE.wt μ) ^ j₀
        * ‖Work.Diff.STE.dmulV q γ μ‖ ^ 2) ^ (1 / 2 : ℝ)
      ≤ Csob * ((2 * Real.pi) ^ k * Real.sqrt Cinv) :=
        mul_le_mul_of_nonneg_left h3 hCsob
    _ = Csob * (2 * Real.pi) ^ k * Real.sqrt Cinv := by ring

/-- **Sup bound for the derivatives of the symmetrised inverse metric up to the Sobolev level.** -/
theorem symInvC_pd_sup_le {n : ℕ} (hn : 1 ≤ n) (k : ℕ)
    (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
      Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM c) ≤ B ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
      ∀ (a b : Fin n) (q : List (Fin n)) (x : Fin n → ℝ),
        q.length + Work.Diff.STE.flat.sob n ≤ k →
        ‖Work.Diff.STE.pdList q (fun y => Work.Diff.STE.flat.symInvC c a b y) x‖ ≤ C := by
  have hσ : Work.Diff.STE.flat.sob n ≤ k := sob_le_of_card hk
  obtain ⟨Csup, hCsupnn, hCsup'⟩ := Work.Diff.STE.norm_seriesFun_le (ι := Fin n)
    (Work.Diff.STE.flat.sob n) (by simpa using Work.Diff.STE.flat.n_lt_two_sob n)
  obtain ⟨Cinv, hCinvnn, hCinv'⟩ :=
    Work.Diff.STE.flat.CSq_symInvC_le hn k hσ lam hlam B hB
  obtain ⟨_lam', _hlam', _Kg, _hKg, hgb⟩ :=
    Work.Diff.STE.fill.symInv_garding_bounds hn k hk lam hlam B hB
  refine ⟨Csup * (2 * Real.pi) ^ k * Real.sqrt Cinv * (1 + B), by positivity, ?_⟩
  intro N c hc hE hell a b q x hq
  obtain ⟨_hsmR, hsmC, _hperR, hperC, _hpdr, _hgard⟩ := hgb N c hc hE hell
  set γ : (Fin n → ℤ) → ℂ :=
    Work.Diff.STE.fourierCoeff (fun y : Fin n → ℝ => Work.Diff.STE.flat.symInvC c a b y)
    with hγdef
  have hsmF : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => Work.Diff.STE.flat.symInvC c a b y) :=
    hsmC a b
  have hperF : Work.Diff.STE.Periodic1
      (fun y : Fin n → ℝ => Work.Diff.STE.flat.symInvC c a b y) := hperC a b
  have hmom2 : ∀ K : ℕ, Summable (fun m : Fin n → ℤ =>
      (Work.Diff.STE.wt m) ^ K * ‖γ m‖ ^ 2) :=
    fun K => Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff _ hsmF hperF K
  have hmom1 : ∀ K : ℕ, Summable (fun m : Fin n → ℤ =>
      (Work.Diff.STE.wt m) ^ K * ‖γ m‖) :=
    fun K => Work.Diff.STE.flat.invJet_summable_moment_of_wt_sq γ hmom2 K
  have hFeq : Work.Diff.STE.seriesFun γ
      = fun y : Fin n → ℝ => Work.Diff.STE.flat.symInvC c a b y :=
    funext (Work.Diff.STE.flat.seriesFun_fourierCoeff _ hsmF hperF)
  have hcsq : Work.Diff.STE.CSq k γ ≤ Cinv := hCinv' N c hc hE hell a b
  have hcsq' : Work.Diff.STE.CSq k γ ≤ Cinv * (1 + B) ^ 2 := by
    refine hcsq.trans ?_
    have h1 : (1 : ℝ) ≤ (1 + B) ^ 2 := by nlinarith [hB]
    nlinarith [hCinvnn, h1]
  have hget : Work.Diff.STE.pdList q (fun y : Fin n → ℝ =>
        Work.Diff.STE.flat.symInvC c a b y)
      = Work.Diff.STE.pdVec q.length (fun t : Fin q.length => q.get t)
          (fun y : Fin n → ℝ => Work.Diff.STE.flat.symInvC c a b y) :=
    Work.Diff.STE.flat.pdList_eq_pdVec q _
  rw [hget, ← hFeq]
  exact Work.Diff.STE.flat.invJet_sup_pdVec_seriesFun_le (n := n) (s := k) hσ
    (d := γ) hmom1 hCsupnn hCsup' hCinvnn hB hcsq' q.length hq
    (fun t : Fin q.length => q.get t) x

/-! ## The Hölder exponent allocation for the commutator -/

/-- **The exponent allocation.**  For an order `j` with `3 ≤ j < k` and the sharp threshold there
are exponents `r₁, r₂ > 2` with `1/r₁ + 1/r₂ = 1/2` such that both prices (with the fixed slack
`1/8`) are at most `k`. -/
theorem comm_exponents {n k j : ℕ} (hn : 1 ≤ n) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (hj : 3 ≤ j) (hjk : j < k) :
    ∃ r₁ r₂ : ℝ, 2 < r₁ ∧ 2 < r₂ ∧ 1 / r₁ + 1 / r₂ = 1 / 2 ∧
      (j : ℝ) + (n : ℝ) / 2 - (n : ℝ) / r₁ + 1 / 8 ≤ (k : ℝ) ∧
      ((k : ℝ) - (j : ℝ) + 2) + (n : ℝ) / 2 - (n : ℝ) / r₂ + 1 / 8 ≤ (k : ℝ) := by
  have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hkR : (n : ℝ) / 2 + 5 / 2 ≤ (k : ℝ) := by
    have h := hk
    simp only [Fintype.card_fin] at h
    have h1 : n + 5 ≤ 2 * k := by omega
    have h2 : ((n + 5 : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hJ3 : (3 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hJK : (j : ℝ) < (k : ℝ) := by exact_mod_cast hjk
  set Xm1 : ℝ := (j : ℝ) + (n : ℝ) / 2 - (k : ℝ) + 1 / 8 with hXm1
  set Xm2 : ℝ := (n : ℝ) / 2 + 2 - (j : ℝ) + 1 / 8 with hXm2
  set X₁ : ℝ := (max Xm1 0 + min ((j : ℝ) - 2 - 1 / 8) ((n : ℝ) / 2)) / 2 with hX₁
  set X₂ : ℝ := (n : ℝ) / 2 - X₁ with hX₂
  have hS : (n : ℝ) / 2 + 9 / 4 < (k : ℝ) := by linarith [hkR]
  have hJK1 : (j : ℝ) + 1 ≤ (k : ℝ) := by
    have h2 : j + 1 ≤ k := by omega
    exact_mod_cast h2
  have hlow : Xm1 < min ((j : ℝ) - 2 - 1 / 8) ((n : ℝ) / 2) := by
    refine lt_min ?_ ?_
    · rw [hXm1]; linarith
    · rw [hXm1]; linarith [hJK1]
  have hpos : 0 < min ((j : ℝ) - 2 - 1 / 8) ((n : ℝ) / 2) := by
    refine lt_min ?_ ?_
    · linarith
    · linarith
  have hmaxlt : max Xm1 0 < min ((j : ℝ) - 2 - 1 / 8) ((n : ℝ) / 2) := max_lt hlow hpos
  have hX1gt : max Xm1 0 < X₁ := by rw [hX₁]; linarith
  have hX1lt : X₁ < min ((j : ℝ) - 2 - 1 / 8) ((n : ℝ) / 2) := by rw [hX₁]; linarith
  have hX1pos : 0 < X₁ := lt_of_le_of_lt (le_max_right _ _) hX1gt
  have hX1ge : Xm1 ≤ X₁ := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hX1gt)
  have hX1n : X₁ < (n : ℝ) / 2 := lt_of_lt_of_le hX1lt (min_le_right _ _)
  have hX1j : X₁ < (j : ℝ) - 2 - 1 / 8 := lt_of_lt_of_le hX1lt (min_le_left _ _)
  have hX2ge : Xm2 ≤ X₂ := by rw [hX₂, hXm2]; linarith
  have hX2pos : 0 < X₂ := by rw [hX₂]; linarith
  have hX2n : X₂ < (n : ℝ) / 2 := by rw [hX₂]; linarith
  refine ⟨(n : ℝ) / X₁, (n : ℝ) / X₂, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hX1pos]; linarith
  · rw [lt_div_iff₀ hX2pos]; linarith
  · rw [one_div_div, one_div_div]
    field_simp
    rw [hX₂]; ring
  · have hdiv : (n : ℝ) / ((n : ℝ) / X₁) = X₁ := by
      field_simp
    rw [hdiv, hXm1] at *
    linarith
  · have hdiv : (n : ℝ) / ((n : ℝ) / X₂) = X₂ := by
      field_simp
    rw [hdiv]
    have h2 := hX2ge
    rw [hXm2] at h2
    linarith

/-! ## The assembly -/

end

end Work.Diff.STE.fill

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators

open Work.Diff.STE.Flat

noncomputable section

private lemma periodic1_sum' {n : ℕ} {ι' : Type*} [Fintype ι']
    {g : ι' → (Fin n → ℝ) → ℂ} (hg : ∀ a, Periodic1 (g a)) :
    Periodic1 (fun x => ∑ a, g a x) := by
  intro i x
  simp only [Pi.add_apply]
  exact Finset.sum_congr rfl (fun a _ => hg a i x)

private lemma periodic1_mul' {n : ℕ} {f g : (Fin n → ℝ) → ℂ}
    (hf : Periodic1 f) (hg : Periodic1 g) : Periodic1 (fun x => f x * g x) := by
  intro i x
  simp only [Pi.add_apply]
  rw [hf i x, hg i x]

private lemma periodic1_pd' {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : Periodic1 f) (j : Fin n) :
    Periodic1 (pd j f) :=
  fun i x => Work.Diff.STE.periodicIn_pd_of_differentiable i j
    (hf.differentiable (by simp)) (hper i) x

/-- **The sharp static pairing bound, assembled from the four proved pieces.**  This is
`Work.Diff.STE.flat.pairingBoundSharp_of_pieces` with
`Work.Diff.STE.flat.pairing_comm_sharp` replaced by the fully proved
`Work.Diff.STE.flat.comm_sharp_bound`. -/
theorem pairingBoundSharp_via_comm {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (hshape : IsDeTurckNonlin Φ)
    (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B) :
    Work.Diff.STE.flat.PairingBoundSharp n k Φ hshape lam B := by
  classical
  obtain ⟨lam', hlam', Cd, hCd, hgb⟩ := symInv_garding_bounds hn k hk lam hlam B hB
  obtain ⟨Cg, hCg, hgard⟩ := pairing_gard_sharp hn k hk lam hlam B hB lam' hlam'
  obtain ⟨Cc, hCc, hcomm⟩ := comm_sharp_bound hn k hk lam hlam B hB lam' hlam'
  obtain ⟨Cz, hCz, hzero⟩ := pairing_zero_sharp hn k hk Φ hshape lam hlam B hB
  obtain ⟨hΦsm, Nfun, hNsm, hNdec, hNper⟩ := hshape
  obtain ⟨Cn, hCn, hN⟩ := pairing_N_sharp hn k hk Nfun hNsm hNper lam hlam B hB
  -- the absorption constant: the two square-root terms are priced against the dissipation
  set Ctot : ℝ := (Cn + Cz) * Real.sqrt (1 + B ^ 2) with hCtotdef
  have hCtot0 : 0 ≤ Ctot := by rw [hCtotdef]; positivity
  set eps : ℝ := lam' / (16 * (Ctot + 1)) with hepsdef
  have heps0 : 0 < eps := by rw [hepsdef]; positivity
  have heps_le : Ctot * eps ≤ lam' / 16 := by
    rw [hepsdef, mul_div, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 16)]
    nlinarith [hlam', hCtot0]
  refine ⟨Cg + Cc + Ctot * (eps + 1 / (4 * eps)) + 1, by positivity, ?_⟩
  intro N c hc hen hell
  -- the Gårding bounds, needed for smoothness/periodicity of the principal coefficient
  obtain ⟨hsmR, hsmC, hperR, hperC, hpdr, hell'⟩ := hgb N c hc hen hell
  have hSer : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x => seriesFunM c x i j) :=
    fun i j => Work.Diff.STE.contDiff_seriesFun (c := fun k' : Fin n → ℤ => c k' i j)
      (fun M' => summable_moment_box c hc i j M')
  have hSerper : ∀ i j : Fin n, Periodic1 (fun x => seriesFunM c x i j) := by
    intro i j
    have h := Work.Diff.STE.periodic_seriesFun (fun k' : Fin n → ℤ => c k' i j)
    simpa only [seriesFunM_apply] using h
  -- the pointwise decomposition of the nonlinearity
  obtain ⟨hdec, hfsm, hfper⟩ := Phi_decomp_smooth (c := c) Φ Nfun hNdec hNsm hNper hΦsm hlam hell
    (fun i j M' => summable_moment_box c hc i j M')
  -- smoothness of the lower-order term
  have hPsm : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ a, ∑ b, symInvC c a b x
      * pd a (pd b (fun z => seriesFunM c z i j)) x) := by
    intro i j
    refine ContDiff.sum fun a _ => ContDiff.sum fun b _ => ?_
    exact (hsmC a b).mul (contDiff_pd_top (contDiff_pd_top (hSer i j) b) a)
  have hNfsm : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x => Nfun (x, jetP c x) i j) := by
    intro i j
    have hdiff : ContDiff ℝ (⊤ : ℕ∞) (fun x => Φ (x, jetM (seriesFunM c) x) i j
        - ∑ a, ∑ b, symInvC c a b x * pd a (pd b (fun z => seriesFunM c z i j)) x) :=
      (hfsm i j).sub (hPsm i j)
    have hfun : (fun x => Φ (x, jetM (seriesFunM c) x) i j
          - ∑ a, ∑ b, symInvC c a b x * pd a (pd b (fun z => seriesFunM c z i j)) x)
        = fun x => Nfun (x, jetP c x) i j := by
      funext x
      rw [hdec x i j]
      ring
    rwa [hfun] at hdiff
  -- periodicity of the lower-order term
  have hPper : ∀ i j : Fin n, Periodic1 (fun x => ∑ a, ∑ b, symInvC c a b x
      * pd a (pd b (fun z => seriesFunM c z i j)) x) := by
    intro i j
    refine periodic1_sum' fun a => periodic1_sum' fun b => ?_
    refine periodic1_mul' (hperC a b) ?_
    exact periodic1_pd' (contDiff_pd_top (hSer i j) b)
      (periodic1_pd' (hSer i j) (hSerper i j) b) a
  have hNper' : ∀ i j : Fin n, Periodic1 (fun x => Nfun (x, jetP c x) i j) := by
    intro i j
    have hfun : (fun x => Φ (x, jetM (seriesFunM c) x) i j
          - ∑ a, ∑ b, symInvC c a b x * pd a (pd b (fun z => seriesFunM c z i j)) x)
        = fun x => Nfun (x, jetP c x) i j := by
      funext x
      rw [hdec x i j]
      ring
    rw [← hfun]
    intro k' x
    simp only [Pi.sub_apply]
    rw [show Φ (x + Pi.single k' 1, jetM (seriesFunM c) (x + Pi.single k' 1)) i j
          = Φ (x, jetM (seriesFunM c) x) i j from hfper i j k' x,
      show (∑ a, ∑ b, symInvC c a b (x + Pi.single k' 1)
              * pd a (pd b (fun z => seriesFunM c z i j)) (x + Pi.single k' 1))
            = ∑ a, ∑ b, symInvC c a b x * pd a (pd b (fun z => seriesFunM c z i j)) x
          from hPper i j k' x]
  -- the level-`k` decomposition, summed over the indices
  have hAij : ∀ i j : Fin n,
      (∑ l : Fin k → Fin n, L2re (pdVec k l (fun x => Φ (x, jetM (seriesFunM c) x) i j))
          (pdVec k l (fun x => seriesFunM c x i j)))
        ≤ (∑ l : Fin k → Fin n,
            L2re (fun x => ∑ a, ∑ b, symInvC c a b x
                * pd a (pd b (pdVec k l (fun y => seriesFunM c y i j))) x)
              (pdVec k l (fun y => seriesFunM c y i j)))
          + (∑ a, ∑ b, |∑ l : Fin k → Fin n,
              L2re (fun x => pdVec k l (fun y => symInvC c a b y
                    * pd a (pd b (fun z => seriesFunM c z i j)) y) x
                  - symInvC c a b x * pdVec k l
                      (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
                (pdVec k l (fun x => seriesFunM c x i j))|)
          + |∑ l : Fin k → Fin n,
              L2re (pdVec k l (fun x => Nfun (x, jetP c x) i j))
                (pdVec k l (fun x => seriesFunM c x i j))| :=
    fun i j => decomp_pairing_le_k (n := n) (k := k)
      (f := fun x => Φ (x, jetM (seriesFunM c) x))
      (Nf := fun x i j => Nfun (x, jetP c x) i j)
      (A := fun a b => symInvC c a b) (c := c) hdec hsmC hNfsm hSer i j
  have hAk : (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin k → Fin n,
        L2re (pdVec k l (fun x => Φ (x, jetM (seriesFunM c) x) i j))
          (pdVec k l (fun x => seriesFunM c x i j)))
      ≤ (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin k → Fin n,
          L2re (fun x => ∑ a, ∑ b, symInvC c a b x
              * pd a (pd b (pdVec k l (fun y => seriesFunM c y i j))) x)
            (pdVec k l (fun y => seriesFunM c y i j)))
        + (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n, |∑ l : Fin k → Fin n,
            L2re (fun x => pdVec k l (fun y => symInvC c a b y
                  * pd a (pd b (fun z => seriesFunM c z i j)) y) x
                - symInvC c a b x * pdVec k l
                    (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
              (pdVec k l (fun x => seriesFunM c x i j))|)
        + (∑ i : Fin n, ∑ j : Fin n, |∑ l : Fin k → Fin n,
            L2re (pdVec k l (fun x => Nfun (x, jetP c x) i j))
              (pdVec k l (fun x => seriesFunM c x i j))|) := by
    have h1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hAij i j
    refine h1.trans ?_
    simp only [Finset.sum_add_distrib]
    exact le_of_eq (by abel)
  -- the zeroth order part
  have hZ : (∑ i : Fin n, ∑ j : Fin n,
        L2re (fun x => Φ (x, jetM (seriesFunM c) x) i j) (fun x => seriesFunM c x i j))
      ≤ Cz * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c)) :=
    (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => le_abs_self _).trans
      (hzero N c hc hen hell)
  -- the three pieces of the level-`k` part
  have hGard := hgard N c hc hen hell hell'
  have hComm := hcomm N c hc hen hell fun x ξ => hell' x ξ
  have hNterm := hN N c hc hen hell hNfsm hNper'
  -- the absorption
  have hEM0 : 0 ≤ ENormSqM (k + 1) (seriesFunM c) := ENormSqM_nonneg (k + 1) _
  have hE0B : ENormSqM 0 (seriesFunM c) ≤ B ^ 2 :=
    (ENormSqM_zero_le_ENormSqFull k (seriesFunM c)).trans hen
  have hEdec : ENormSqFull (k + 1) (seriesFunM c)
      = ENormSqM (k + 1) (seriesFunM c) + ENormSqM 0 (seriesFunM c) := rfl
  have hEsq : 1 + ENormSqFull (k + 1) (seriesFunM c)
      ≤ (1 + B ^ 2) * (1 + ENormSqM (k + 1) (seriesFunM c)) := by
    rw [hEdec]
    nlinarith [hE0B, hB]
  have hsqrtE : (Cn + Cz) * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c))
      ≤ Ctot * Real.sqrt (1 + ENormSqM (k + 1) (seriesFunM c)) := by
    have h1 : Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c))
        ≤ Real.sqrt (1 + B ^ 2) * Real.sqrt (1 + ENormSqM (k + 1) (seriesFunM c)) := by
      calc Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c))
          ≤ Real.sqrt ((1 + B ^ 2) * (1 + ENormSqM (k + 1) (seriesFunM c))) :=
            Real.sqrt_le_sqrt hEsq
        _ = Real.sqrt (1 + B ^ 2) * Real.sqrt (1 + ENormSqM (k + 1) (seriesFunM c)) := by
            rw [Real.sqrt_mul (by positivity)]
    rw [hCtotdef, mul_assoc]
    refine mul_le_mul_of_nonneg_left h1 (by positivity)
  have habs : ∀ X : ℝ, 0 ≤ X →
      Real.sqrt (1 + X) ≤ eps * X + (eps + 1 / (4 * eps)) := by
    intro X hX
    have h1 : (0 : ℝ) ≤ 1 + X := by linarith
    have hsq := Real.sq_sqrt h1
    have h4 : 4 * eps * Real.sqrt (1 + X) ≤ 4 * eps ^ 2 * (1 + X) + 1 := by
      nlinarith [sq_nonneg (2 * eps * Real.sqrt (1 + X) - 1), hsq, heps0]
    have h5 : Real.sqrt (1 + X) ≤ (4 * eps ^ 2 * (1 + X) + 1) / (4 * eps) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * eps)]
      linarith [h4]
    have h6 : (4 * eps ^ 2 * (1 + X) + 1) / (4 * eps) = eps * (1 + X) + 1 / (4 * eps) := by
      field_simp
    linarith [h5, h6]
  have hkey : Ctot * Real.sqrt (1 + ENormSqM (k + 1) (seriesFunM c))
      ≤ Ctot * (eps + 1 / (4 * eps)) + (lam' / 16) * ENormSqM (k + 1) (seriesFunM c) := by
    have h1 : Ctot * Real.sqrt (1 + ENormSqM (k + 1) (seriesFunM c))
        ≤ Ctot * (eps * ENormSqM (k + 1) (seriesFunM c) + (eps + 1 / (4 * eps))) :=
      mul_le_mul_of_nonneg_left (habs _ hEM0) hCtot0
    have h2 : Ctot * (eps * ENormSqM (k + 1) (seriesFunM c))
        ≤ (lam' / 16) * ENormSqM (k + 1) (seriesFunM c) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right heps_le hEM0
    linarith [h1, h2]
  -- the final estimate
  have hfin : pairSharp n k Φ c
      ≤ Cg + Cc + Ctot * (eps + 1 / (4 * eps)) + 1 := by
    have hsplit : pairSharp n k Φ c
        = (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin k → Fin n,
            L2re (pdVec k l (fun x => Φ (x, jetM (seriesFunM c) x) i j))
              (pdVec k l (fun x => seriesFunM c x i j)))
          + (∑ i : Fin n, ∑ j : Fin n,
              L2re (fun x => Φ (x, jetM (seriesFunM c) x) i j)
                (fun x => seriesFunM c x i j)) := by
      simp only [pairSharp, Finset.sum_add_distrib]
    rw [hsplit]
    have hstep : (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin k → Fin n,
            L2re (pdVec k l (fun x => Φ (x, jetM (seriesFunM c) x) i j))
              (pdVec k l (fun x => seriesFunM c x i j)))
          + (∑ i : Fin n, ∑ j : Fin n,
              L2re (fun x => Φ (x, jetM (seriesFunM c) x) i j)
                (fun x => seriesFunM c x i j))
        ≤ (-(lam' / 2) * ENormSqM (k + 1) (seriesFunM c) + Cg)
          + ((lam' / 8) * ENormSqM (k + 1) (seriesFunM c) + Cc)
          + ((Cn + Cz) * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c))) := by
      have h1 : (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin k → Fin n,
            L2re (pdVec k l (fun x => Φ (x, jetM (seriesFunM c) x) i j))
              (pdVec k l (fun x => seriesFunM c x i j)))
          ≤ (-(lam' / 2) * ENormSqM (k + 1) (seriesFunM c) + Cg)
            + ((lam' / 8) * ENormSqM (k + 1) (seriesFunM c) + Cc)
            + (Cn * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c))) := by
        linarith [hAk, hGard, hComm, hNterm]
      have h2 : (∑ i : Fin n, ∑ j : Fin n,
            L2re (fun x => Φ (x, jetM (seriesFunM c) x) i j)
              (fun x => seriesFunM c x i j))
          ≤ Cz * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c)) := hZ
      linarith [h1, h2]
    calc _ ≤ (-(lam' / 2) * ENormSqM (k + 1) (seriesFunM c) + Cg)
          + ((lam' / 8) * ENormSqM (k + 1) (seriesFunM c) + Cc)
          + ((Cn + Cz) * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c))) := hstep
      _ ≤ (-(lam' / 2) * ENormSqM (k + 1) (seriesFunM c) + Cg)
          + ((lam' / 8) * ENormSqM (k + 1) (seriesFunM c) + Cc)
          + (Ctot * Real.sqrt (1 + ENormSqM (k + 1) (seriesFunM c))) := by
            linarith [hsqrtE]
      _ ≤ (-(lam' / 2) * ENormSqM (k + 1) (seriesFunM c) + Cg)
          + ((lam' / 8) * ENormSqM (k + 1) (seriesFunM c) + Cc)
          + (Ctot * (eps + 1 / (4 * eps))
            + (lam' / 16) * ENormSqM (k + 1) (seriesFunM c)) := by linarith [hkey]
      _ ≤ Cg + Cc + Ctot * (eps + 1 / (4 * eps)) + 1 := by
        have h3 : -(lam' / 2) * ENormSqM (k + 1) (seriesFunM c)
            + (lam' / 8) * ENormSqM (k + 1) (seriesFunM c)
            + (lam' / 16) * ENormSqM (k + 1) (seriesFunM c) ≤ 0 :=
          by nlinarith [hEM0, hlam']
        linarith [h3]
  exact hfin

end

end Work.Diff.STE.flat

namespace Work.Diff.STE.fill

/-- **The target**: the sharp static pairing bound (see
`Submission/Work/Diff/STE/flat/pairing_sharp.lean`). -/
theorem pairingBoundSharp {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B) :
    Work.Diff.STE.flat.PairingBoundSharp n k Φ hshape lam B :=
  Work.Diff.STE.flat.pairingBoundSharp_via_comm hn Φ hshape k hk lam hlam B hB

end Work.Diff.STE.fill
