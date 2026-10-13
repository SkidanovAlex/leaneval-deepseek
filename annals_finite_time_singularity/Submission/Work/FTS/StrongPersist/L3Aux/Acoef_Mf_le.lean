import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Coercivity.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.OpenPkg.l12_open_bundle
import Submission.Work.FTS.EllipticEst.UopHk.L12_w_sq_integrable
import Submission.Work.FTS.EllipticEst.UopHk.L12_contDiffOn_reg
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.StrongPersist.L3Aux.L12f_slot_le
import Submission.Work.FTS.StrongPersist.L3Aux.acoef_gamCoef_slots_le
import Submission.Work.FTS.StrongPersist.L3Aux.GamJetBounds
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulCore
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth
import Submission.Work.FTS.StrongPersist.L3Aux.HkIntegrand_sep_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-!
# `Work.FTS.StrongPersist.L3Aux.Acoef_Mf_le`

The `ℋ³`-regularity and the `ℋ³`-bound of the **nonlocal summand** `A(α)·L₁₂(f)` of the
level-three linear operator, in its open-quadrant (`C³`) form:

* `Acf α f = acf(z)·(Γ(θ)/c(α))·L₁₂(f)(z)` is `C³` on the open quadrant `Q0 = (0,∞)×(0,π/2)`;
* `Acf α f ∈ ℋ³` (weighted-integral honesty);
* `HkSq α 3 (Acf α f) ≤ C·HkSq α 4 f`.

The route (all pieces are already in the workspace):

* the *first* conjunct: `L₁₂(f) ∈ C³((0,∞))` from the residue class (`HkMem α 4 f`,
  `UopHk.contDiffOn_L12_of_smoothOpen_Hk`), `z ↦ 2z/(1+z)²` is `C^∞` there, and
  `θ ↦ (sinθcos²θ)^{α/3}/c(α)` is `C^∞` on `(0,π/2)`; a product of separated smooth factors is
  jointly smooth;
* the *multiplier step*: `D_z` does not see the angular factor, so every `ℋ³`-slot of
  `acf·(gc·L₁₂f)` is a binomial sum of slots of `gc·L₁₂f` weighted by the bounded `Zop`-jets of
  `z ↦ 2z/(1+z)²` (`zslot_supBound`, value `24000`).  This is `zmul_pt` (`ZmulCore`),
  instantiated at finite smoothness (`zmul_finite_open` below);
* the *angular step*: for a separated datum `C(θ)·B(z)` the `ℋ³`-integrand factorises
  (`HkIntegrand_sep_le`), and the angular masses `∫(Γ/c)² sin^{-η}` and
  `∫(D_θ^i(Γ/c))² sin^{-γ}` are bounded uniformly in `α` (`GamJetBounds`, `10¹⁵`);
* the *radial step*: the pure `D_z`-slots of `L₁₂ f` are bounded by `HkSq α 4 f` on `Iz`
  (`L12f_slot_le`);
* the assembly integrates the resulting pointwise bound (`HkMem_of_majorant`,
  `integral_mono_of_nonneg`).
-/

/-! ## The function of the statement in separated form

`Acf α f = acf(z) · (Γ(θ)/c(α)) · L₁₂(f)(z)` with `acf(z) = 2z/(1+z)²`; the association of
the product is chosen so that the `z`-only and `θ`-only factors separate. -/

/-- The radial factor `z ↦ 2z/(1+z)²` of the nonlocal coefficient. -/
private def acf (z : ℝ) : ℝ := 2 * z / (1 + z) ^ 2

/-- The angular factor `θ ↦ Γ(θ)/c(α)`. -/
private def gcf (α : ℝ) (θ : ℝ) : ℝ := Work.Spaces.Gam α θ / Work.Spaces.c α

/-- The nonlocal summand `acf(z)·(Γ(θ)/c(α))·L₁₂(f)(z)`. -/
private def Acf (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => acf z * (gcf α θ * Work.Construction.L12 f z)

private theorem Acf_apply (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Acf α f z θ
      = (2 * z / (1 + z) ^ 2)
        * ((Work.Spaces.Gam α θ / Work.Spaces.c α) * Work.Construction.L12 f z) := rfl

/-- The function of the statement equals `Acf α f`. -/
private theorem Acf_eq_stmt (α : ℝ) (f : ℝ → ℝ → ℝ) :
    (fun z θ => ((2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam α θ / Work.Spaces.c α))
        * Work.Construction.L12 f z) = Acf α f := by
  funext z θ
  rw [Acf_apply]
  ring

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
private theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-! ## The first conjunct: `C³` on the open quadrant -/

/-- `z ↦ 2z/(1+z)²` is `C³` on `(0,∞)`. -/
private theorem contDiffOn_three_acf : ContDiffOn ℝ 3 acf (Set.Ioi (0 : ℝ)) := by
  have h0 : ContDiffOn ℝ ⊤ acf (Set.Ioi (-1 : ℝ)) := by
    have hfun : acf = fun z => 2 * z / (1 + z) ^ 2 := by funext z; rfl
    rw [hfun]
    exact contDiffOn_two_z_div
  exact (h0.mono (fun z hz => by
    simp only [Set.mem_Ioi] at hz ⊢
    linarith)).of_le le_top

/-- `θ ↦ Γ(θ)/c(α)` is `C³` on `(0,π/2)`. -/
private theorem contDiffOn_three_gcf (α : ℝ) :
    ContDiffOn ℝ 3 (gcf α) (Set.Ioo (0 : ℝ) (π / 2)) := by
  have hbase : ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    (Real.contDiff_sin.contDiffOn).mul ((Real.contDiff_cos.contDiffOn).pow 2)
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), Real.sin θ * Real.cos θ ^ 2 ≠ 0 := by
    intro θ hθ
    have h1 : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have hgam : ContDiffOn ℝ ⊤ (fun θ : ℝ => Work.Spaces.Gam α θ)
      (Set.Ioo (0 : ℝ) (π / 2)) := hbase.rpow_const_of_ne hne
  exact (hgam.div_const (Work.Spaces.c α)).of_le le_top

/-- **The nonlocal summand is `C³` on the open quadrant.** -/
private theorem contDiffOn_three_Acf {α : ℝ} {f : ℝ → ℝ → ℝ}
    (h12 : ContDiffOn ℝ 3 (Work.Construction.L12 f) (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ 3 (Function.uncurry (Acf α f)) Work.FTS.EllipticEst.Q0 := by
  have hA : ContDiffOn ℝ 3 (fun z => acf z * Work.Construction.L12 f z) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_three_acf.mul h12
  have hB : ContDiffOn ℝ 3 (gcf α) (Set.Ioo (0 : ℝ) (π / 2)) := contDiffOn_three_gcf α
  have hprod : ContDiffOn ℝ 3
      (fun p : ℝ × ℝ => (fun z => acf z * Work.Construction.L12 f z) p.1 * gcf α p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    (hA.comp contDiffOn_fst (fun p hp => hp.1)).mul
      (hB.comp contDiffOn_snd (fun p hp => hp.2))
  have hfun : Function.uncurry (Acf α f)
      = fun p : ℝ × ℝ => (fun z => acf z * Work.Construction.L12 f z) p.1 * gcf α p.2 := by
    funext p
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Acf, gcf, acf]
    ring
  rw [hfun]
  exact hprod

/-! ## The finite-order multiplier estimate

`zmul_pt` (`ZmulCore`) is the algebraic core: given, at a point, the two Leibniz expansions
of `D_z^i(φ·g)` and `D_z^jD_θ^i(φ·g)` for a `z`-only multiplier `φ` and a bound `K` on the
`Zop`-jets of `φ`, it proves `HkIntegrand α k (φ·g) ≤ zmulConst k·(1+K)²·HkIntegrand α k g`.
Here the expansions are supplied at *finite* smoothness on `(0,∞)` by
`FinalClock.DzIter_mul_of_contDiffOn` / `mixed_mul_of_contDiffOn`, which is exactly the regime
needed when `g` contains `L₁₂(f)`. -/

private theorem zmul_finite_open (α : ℝ) (k : ℕ) (φ : ℝ → ℝ) (g : ℝ → ℝ → ℝ) {K : ℝ}
    (hK : 0 ≤ K)
    (hB : ∀ (b : ℕ), b ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] φ z| ≤ K)
    (hφ : ∀ (b : ℕ), b ≤ k → ContDiffOn ℝ b φ (Set.Ioi (0 : ℝ)))
    (hg : ∀ (i : ℕ), i ≤ k → ∀ θ : ℝ,
      ContDiffOn ℝ i (fun z => g z θ) (Set.Ioi (0 : ℝ)))
    (hgθ : ∀ (j i : ℕ), 1 ≤ i → i + j ≤ k → ∀ θ : ℝ,
      ContDiffOn ℝ j (fun z => Work.Spaces.DthIter i g z θ) (Set.Ioi (0 : ℝ))) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ,
      Work.Spaces.HkIntegrand α k (fun z θ => φ z * g z θ) z θ
        ≤ zmulConst k * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α k g z θ := by
  intro z hz θ
  refine zmul_pt α k φ g hK (fun b hb => hB b hb z hz) ?_ ?_
  · intro i hi
    exact Work.FTS.FinalClock.DzIter_mul_of_contDiffOn i φ g isOpen_Ioi
      (hφ i hi) (hg i hi θ) z hz
  · intro j i hi hij
    exact Work.FTS.FinalClock.mixed_mul_of_contDiffOn j i φ g isOpen_Ioi
      (hφ j (by omega)) (hgθ j i hi hij θ) z hz

/-- **Step A**: the `ℋ³`-integrand of the nonlocal summand is dominated by that of
`(Γ(θ)/c(α))·L₁₂(f)(z)`, with the constant `zmulConst 3·(1+24000)²`.

(`24000` is `zslot_supBound`: every `D_z`-iterate of `z ↦ 2z/(1+z)²` up to order `4` is bounded
by `24000` on `Iz`.) -/
private theorem acf_integrand_le (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 (Acf α f) z θ
        ≤ zmulConst 3 * (1 + 24000) ^ 2
          * Work.Spaces.HkIntegrand α 3 (fun z θ => gcf α θ * Work.Construction.L12 f z) z θ := by
  have hK : (0 : ℝ) ≤ 24000 := by norm_num
  have hL3 : ContDiffOn ℝ 3 (Work.Construction.L12 f) (Set.Ioi (0 : ℝ)) :=
    (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 4 f hsm hmem
      (by norm_num)).1
  have h12 : ∀ (i : ℕ), i ≤ 3 → ContDiffOn ℝ i (Work.Construction.L12 f)
      (Set.Ioi (0 : ℝ)) := by
    intro i hi
    exact hL3.of_le (by exact_mod_cast hi)
  have hB : ∀ (b : ℕ), b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] acf z| ≤ 24000 := by
    intro b hb z hz
    have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (le_of_lt hz)
    have h0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_refl 0, by linarith [Real.pi_pos]⟩
    have h1 := zslot_supBound b (by omega) z hzI 0 h0
    have h2 : Work.Spaces.Zop^[b] acf z
        = Work.Spaces.DzIter b (fun z (_ : ℝ) => acf z) z 0 :=
      (congrFun (Work.Spaces.Zop_slice b (fun z (_ : ℝ) => acf z) 0) z).symm
    rw [h2]
    exact h1
  have hφ : ∀ (b : ℕ), b ≤ 3 → ContDiffOn ℝ b acf (Set.Ioi (0 : ℝ)) := by
    intro b hb
    exact contDiffOn_three_acf.of_le (by exact_mod_cast hb)
  have hg : ∀ (i : ℕ), i ≤ 3 → ∀ θ : ℝ,
      ContDiffOn ℝ i (fun z => gcf α θ * Work.Construction.L12 f z) (Set.Ioi (0 : ℝ)) := by
    intro i hi θ
    simpa only [smul_eq_mul] using (h12 i hi).const_smul (gcf α θ)
  have hgθ : ∀ (j i : ℕ), 1 ≤ i → i + j ≤ 3 → ∀ θ : ℝ,
      ContDiffOn ℝ j (fun z => Work.Spaces.DthIter i
        (fun z θ => gcf α θ * Work.Construction.L12 f z) z θ) (Set.Ioi (0 : ℝ)) := by
    intro j i hi hij θ
    have hdec : (fun z => Work.Spaces.DthIter i
        (fun z θ => gcf α θ * Work.Construction.L12 f z) z θ)
        = fun z => Work.Spaces.dthU^[i] (gcf α) θ * Work.Construction.L12 f z := by
      funext z
      exact Work.Spaces.DthIter_decomp i (gcf α) (fun z => Work.Construction.L12 f z) z θ
    rw [hdec]
    have hj : ContDiffOn ℝ j (Work.Construction.L12 f) (Set.Ioi (0 : ℝ)) :=
      h12 j (by omega)
    simpa only [smul_eq_mul] using hj.const_smul (Work.Spaces.dthU^[i] (gcf α) θ)
  intro z hz θ hθ
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    rw [Work.FTS.LocData.HkIntegrand_zero_fst, Work.FTS.LocData.HkIntegrand_zero_fst]
    exact le_of_eq (by ring)
  · exact zmul_finite_open α 3 acf
      (fun z θ => gcf α θ * Work.Construction.L12 f z) hK hB hφ hg hgθ z hzpos θ

/-! ## The angular masses

The `θ`-factor of the majorant: the `η`-summand plus the `γ`-summands of the mixed block, with
their masses bounded uniformly in `α` by `GamJetBounds`. -/

/-- The angular factor of the majorant of the `ℋ³`-integrand of a separated datum. -/
private def Mth (α : ℝ) : ℝ → ℝ := fun θ =>
  (gcf α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    + ∑ i ∈ Finset.range 4,
        (if 1 ≤ i then (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)

private theorem Mth_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Mth α θ := by
  have hs := sin_two_nonneg_Iθ hθ
  have h1 : 0 ≤ (gcf α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)
  have h2 : 0 ≤ ∑ i ∈ Finset.range 4,
      (if 1 ≤ i then (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0) :=
    Finset.sum_nonneg fun i _ => by
      split_ifs with _
      · exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)
      · exact le_refl 0
  exact add_nonneg h1 h2

/-- The `γ`-mass integrand of the `dthU`-jet, in the `DthIter`-form of `GamJetBounds`. -/
private theorem gam_mass_form (i : ℕ) (α : ℝ) :
    (fun θ : ℝ => (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = fun θ : ℝ =>
          (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  funext θ
  rw [Work.FTS.LocData.DthIter_rad_eq i (fun θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ]
  rfl

/-- **The angular majorant and its mass.**  From the two `GamJetBounds` inputs (the `η`-mass of
`Γ/c` and the `γ`-masses of its `θ`-jets, both bounded by `K`), the angular factor `Mth α`
is integrable on `Iθ` with `∫_θ Mth α ≤ 5K`. -/
private theorem Mth_int_le (α : ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hη : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ≤ K)
    (hγ : ∀ (i : ℕ), 1 ≤ i → i ≤ 4 →
      MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DthIter i
        (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ≤ K) :
    MeasureTheory.IntegrableOn (Mth α) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Mth α θ) ≤ 5 * K := by
  have hγ' : ∀ (i : ℕ), 1 ≤ i → i ≤ 4 →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ≤ K := by
    intro i hi1 hi4
    obtain ⟨hI, hB⟩ := hγ i hi1 hi4
    exact ⟨by rwa [← gam_mass_form i α] at hI, by rwa [← gam_mass_form i α] at hB⟩
  -- integrability
  have hsum : MeasureTheory.IntegrableOn (fun θ : ℝ => ∑ i ∈ Finset.range 4,
      (if 1 ≤ i then (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)) Work.Spaces.Iθ := by
    refine MeasureTheory.integrable_finset_sum (Finset.range 4) (fun i hi => ?_)
    by_cases h : 1 ≤ i
    · simp only [if_pos h]
      exact (hγ' i h (by rw [Finset.mem_range] at hi; omega)).1
    · simp only [if_neg h]
      exact integrableOn_zero
  have hInt : MeasureTheory.IntegrableOn (Mth α) Work.Spaces.Iθ := hη.1.add hsum
  refine ⟨hInt, ?_⟩
  -- the value of the integral
  have hMth : Mth α = fun θ : ℝ =>
      (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + ∑ i ∈ Finset.range 4,
            (if 1 ≤ i then (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0) := rfl
  have hsumInt : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range 4,
      (if 1 ≤ i then (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
      = ∑ i ∈ Finset.range 4,
          (∫ θ in Work.Spaces.Iθ, (if 1 ≤ i then (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)) :=
    MeasureTheory.integral_finset_sum (Finset.range 4) (fun i hi => by
      by_cases h : 1 ≤ i
      · simp only [if_pos h]
        exact (hγ' i h (by rw [Finset.mem_range] at hi; omega)).1
      · simp only [if_neg h]
        exact integrableOn_zero)
  have hsplit : (∫ θ in Work.Spaces.Iθ, Mth α θ)
      = (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        + ∑ i ∈ Finset.range 4,
            (∫ θ in Work.Spaces.Iθ, (if 1 ≤ i then (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)) := by
    rw [hMth, MeasureTheory.integral_add hη.1 hsum, hsumInt]
  rw [hsplit]
  have hsum_le : (∑ i ∈ Finset.range 4,
      (∫ θ in Work.Spaces.Iθ, (if 1 ≤ i then (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))) ≤ 4 * K := by
    calc (∑ i ∈ Finset.range 4,
          (∫ θ in Work.Spaces.Iθ, (if 1 ≤ i then (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)))
        ≤ ∑ _i ∈ Finset.range 4, K := Finset.sum_le_sum fun i hi => by
          by_cases h : 1 ≤ i
          · simp only [if_pos h]
            exact (hγ' i h (by rw [Finset.mem_range] at hi; omega)).2
          · simp only [if_neg h]
            rw [MeasureTheory.integral_zero]
            exact hK
      _ = 4 * K := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  linarith [hη.2, hsum_le]

/-- The radial factor of the majorant: the `D_z`-slots of `L₁₂(f)`. -/
private def Sz (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ q ∈ Finset.range 4,
    (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2

private theorem Sz_nonneg (f : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ Sz f z :=
  Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **The radial factor and its weighted mass**: the four `D_z`-slots of `L₁₂(f)` are integrable
on `Iz` and their total mass is at most `4·C₂·HkSq α 4 f`. -/
private theorem Sz_integrable {α : ℝ} (f : ℝ → ℝ → ℝ) {C₂ : ℝ}
    (h : ∀ q ≤ 4, MeasureTheory.IntegrableOn (fun z : ℝ =>
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, (Work.Spaces.DzIter q
          (fun z _ => Work.Construction.L12 f z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ C₂ * Work.Spaces.HkSq α 4 f) :
    MeasureTheory.IntegrableOn (Sz f) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, Sz f z) ≤ 4 * (C₂ * Work.Spaces.HkSq α 4 f) := by
  have hint : MeasureTheory.IntegrableOn (Sz f) Work.Spaces.Iz :=
    MeasureTheory.integrable_finset_sum (Finset.range 4)
      (fun q hq => (h q (by rw [Finset.mem_range] at hq; omega)).1)
  refine ⟨hint, ?_⟩
  have hval : (∫ z in Work.Spaces.Iz, Sz f z) = ∑ q ∈ Finset.range 4,
      (∫ z in Work.Spaces.Iz, (Work.Spaces.DzIter q
        (fun z _ => Work.Construction.L12 f z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2) :=
    MeasureTheory.integral_finset_sum (Finset.range 4)
      (fun q hq => (h q (by rw [Finset.mem_range] at hq; omega)).1)
  rw [hval]
  calc (∑ q ∈ Finset.range 4, (∫ z in Work.Spaces.Iz, (Work.Spaces.DzIter q
        (fun z _ => Work.Construction.L12 f z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2))
      ≤ ∑ _q ∈ Finset.range 4, (C₂ * Work.Spaces.HkSq α 4 f) :=
        Finset.sum_le_sum fun q hq =>
          (h q (by rw [Finset.mem_range] at hq; omega)).2
    _ = 4 * (C₂ * Work.Spaces.HkSq α 4 f) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem Acoef_Mf_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.Construction.L12 f 0 = 0 →
    ContDiffOn ℝ 3 (Function.uncurry (fun z θ =>
      ((2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam α θ / Work.Spaces.c α))
        * Work.Construction.L12 f z)) Work.FTS.EllipticEst.Q0 ∧
    Work.Spaces.HkMem α 3 (fun z θ => ((2 * z / (1 + z) ^ 2)
        * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * Work.Construction.L12 f z) ∧
    Work.Spaces.HkSq α 3 (fun z θ => ((2 * z / (1 + z) ^ 2)
        * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * Work.Construction.L12 f z)
      ≤ C * Work.Spaces.HkSq α 4 f := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := L12f_slot_le
  obtain ⟨K₂, hK₂pos, -, hK₂η, hK₂γ⟩ := GamJetBounds
  refine ⟨zmulConst 3 * (1 + 24000) ^ 2 * (5 * K₂) * (4 * C₂) + 1, ?_, ?_⟩
  · have h1 : 0 < zmulConst 3 * (1 + 24000) ^ 2 := by
      have := zmulConst_pos 3
      positivity
    have h2 : 0 < 5 * K₂ := by linarith
    have h3 : 0 < 4 * C₂ := by linarith
    positivity
  · intro α f hα hα1 hsm hmem hL120
    have hC₀pos : (0 : ℝ) < zmulConst 3 * (1 + 24000) ^ 2 := by
      have := zmulConst_pos 3
      positivity
    -- ### `L₁₂(f)` is `C³` on `(0,∞)`, hence the nonlocal summand is `C³` on the quadrant
    have hL3 : ContDiffOn ℝ 3 (Work.Construction.L12 f) (Set.Ioi (0 : ℝ)) :=
      (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 4 f hsm hmem
        (by norm_num)).1
    have hAcf3 : ContDiffOn ℝ 3 (Function.uncurry (Acf α f)) Work.FTS.EllipticEst.Q0 :=
      contDiffOn_three_Acf hL3
    -- ### the auxiliary estimates
    have hslot : ∀ q ≤ 4, MeasureTheory.IntegrableOn (fun z : ℝ =>
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, (Work.Spaces.DzIter q
            (fun z _ => Work.Construction.L12 f z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ C₂ * Work.Spaces.HkSq α 4 f := fun q hq =>
      hC₂ α hα hα1 f hsm hmem hL120 q hq
    have hSz := Sz_integrable (α := α) f hslot
    have hMth := Mth_int_le α hK₂pos.le (hK₂η α hα hα1) (hK₂γ α hα hα1)
    -- ### the pointwise domination of the integrand
    have hstepA : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 3 (Acf α f) z θ
          ≤ zmulConst 3 * (1 + 24000) ^ 2
            * Work.Spaces.HkIntegrand α 3
                (fun z θ => gcf α θ * Work.Construction.L12 f z) z θ :=
      acf_integrand_le α f hsm hmem
    have hstepB : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 3
            (fun z θ => gcf α θ * Work.Construction.L12 f z) z θ ≤ Mth α θ * Sz f z := by
      intro z _ θ hθ
      simpa only [Mth, Sz] using
        (HkIntegrand_sep_le (α := α) (C := gcf α)
          (B := fun z => Work.Construction.L12 f z) (z := z) (θ := θ) hθ)
    have hpoint : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 3 (Acf α f) z θ
          ≤ (zmulConst 3 * (1 + 24000) ^ 2) * (Mth α θ * Sz f z) := by
      intro z hz θ hθ
      exact le_trans (hstepA z hz θ hθ)
        (mul_le_mul_of_nonneg_left (hstepB z hz θ hθ) hC₀pos.le)
    -- ### conjunct 2: `Acf α f ∈ ℋ³`
    have hMslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => (zmulConst 3 * (1 + 24000) ^ 2) * (Mth α θ * Sz f z)) Work.Spaces.Iθ :=
      fun z _ => (hMth.1.mul_const (Sz f z)).const_mul (zmulConst 3 * (1 + 24000) ^ 2)
    have hMz : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        (zmulConst 3 * (1 + 24000) ^ 2) * (Mth α θ * Sz f z)) Work.Spaces.Iz := by
      have hval : (fun z => ∫ θ in Work.Spaces.Iθ,
            (zmulConst 3 * (1 + 24000) ^ 2) * (Mth α θ * Sz f z))
          = fun z => (zmulConst 3 * (1 + 24000) ^ 2 * (∫ θ in Work.Spaces.Iθ, Mth α θ))
              * Sz f z := by
        funext z
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]
        ring
      rw [hval]
      exact hSz.1.const_mul (zmulConst 3 * (1 + 24000) ^ 2 * (∫ θ in Work.Spaces.Iθ, Mth α θ))
    have hconj2acf : Work.Spaces.HkMem α 3 (Acf α f) :=
      Work.FTS.LocData.HkMem_of_majorant α 3
        (Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn α le_rfl hAcf3)
        hMslice hMz hpoint
    -- ### conjunct 3: the weighted bound
    have hinner : ∀ z ∈ Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 3 (Acf α f) z θ)
        ≤ (zmulConst 3 * (1 + 24000) ^ 2) * (Sz f z * (5 * K₂)) := by
      intro z hz
      have hii := MeasureTheory.integral_mono_of_nonneg
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun θ => Work.Spaces.HkIntegrand α 3 (Acf α f) z θ)
        (g := fun θ => (zmulConst 3 * (1 + 24000) ^ 2) * (Mth α θ * Sz f z))
        (Filter.Eventually.of_forall fun θ =>
          Work.Spaces.HkIntegrand_nonneg α 3 (Acf α f) z θ)
        (hMslice z hz)
        ((MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
          (Filter.Eventually.of_forall fun θ hθ => hpoint z hz θ hθ))
      have hvalθ : (∫ θ in Work.Spaces.Iθ,
            (zmulConst 3 * (1 + 24000) ^ 2) * (Mth α θ * Sz f z))
          = (zmulConst 3 * (1 + 24000) ^ 2)
              * ((∫ θ in Work.Spaces.Iθ, Mth α θ) * Sz f z) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]
      refine hii.trans ?_
      rw [hvalθ]
      refine mul_le_mul_of_nonneg_left ?_ hC₀pos.le
      calc (∫ θ in Work.Spaces.Iθ, Mth α θ) * Sz f z ≤ (5 * K₂) * Sz f z :=
            mul_le_mul_of_nonneg_right hMth.2 (Sz_nonneg f z)
        _ = Sz f z * (5 * K₂) := by ring
    have hdomInt : MeasureTheory.IntegrableOn (fun z : ℝ =>
        (zmulConst 3 * (1 + 24000) ^ 2) * (Sz f z * (5 * K₂))) Work.Spaces.Iz :=
      (hSz.1.mul_const (5 * K₂)).const_mul (zmulConst 3 * (1 + 24000) ^ 2)
    have houter := MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 3 (Acf α f) z θ)
      (g := fun z => (zmulConst 3 * (1 + 24000) ^ 2) * (Sz f z * (5 * K₂)))
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg_of_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 3 (Acf α f) z θ)))
      hdomInt
      ((MeasureTheory.ae_restrict_iff' measurableSet_Ici).mpr
        (Filter.Eventually.of_forall fun z hz => hinner z hz))
    have hfinal : Work.Spaces.HkSq α 3 (Acf α f)
        ≤ (zmulConst 3 * (1 + 24000) ^ 2 * (5 * K₂) * (4 * C₂)) * Work.Spaces.HkSq α 4 f := by
      have hvalz : (∫ z in Work.Spaces.Iz,
            (zmulConst 3 * (1 + 24000) ^ 2) * (Sz f z * (5 * K₂)))
          = (zmulConst 3 * (1 + 24000) ^ 2 * (5 * K₂))
              * (∫ z in Work.Spaces.Iz, Sz f z) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]
        ring
      calc Work.Spaces.HkSq α 3 (Acf α f)
          = ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 3 (Acf α f) z θ) := rfl
        _ ≤ ∫ z in Work.Spaces.Iz,
              (zmulConst 3 * (1 + 24000) ^ 2) * (Sz f z * (5 * K₂)) := houter
        _ = (zmulConst 3 * (1 + 24000) ^ 2 * (5 * K₂))
              * (∫ z in Work.Spaces.Iz, Sz f z) := hvalz
        _ ≤ (zmulConst 3 * (1 + 24000) ^ 2 * (5 * K₂)) * (4 * (C₂ * Work.Spaces.HkSq α 4 f)) :=
            mul_le_mul_of_nonneg_left hSz.2 (by positivity)
        _ = (zmulConst 3 * (1 + 24000) ^ 2 * (5 * K₂) * (4 * C₂))
              * Work.Spaces.HkSq α 4 f := by ring
    have hconj3 : Work.Spaces.HkSq α 3 (fun z θ => ((2 * z / (1 + z) ^ 2)
          * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * Work.Construction.L12 f z)
        ≤ (zmulConst 3 * (1 + 24000) ^ 2 * (5 * K₂) * (4 * C₂) + 1)
            * Work.Spaces.HkSq α 4 f := by
      rw [Acf_eq_stmt α f]
      exact le_trans hfinal (mul_le_mul_of_nonneg_right (by linarith)
        (Work.Spaces.HkSq_nonneg α 4 f))
    refine ⟨?_, ?_, hconj3⟩
    · rw [Acf_eq_stmt α f]
      exact hAcf3
    · rw [Acf_eq_stmt α f]
      exact hconj2acf

end Work.FTS.StrongPersist.L3Aux
