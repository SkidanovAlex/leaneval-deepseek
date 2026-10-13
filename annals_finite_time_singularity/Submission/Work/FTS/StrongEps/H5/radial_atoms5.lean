/-
# `Work.FTS.StrongEps.H5.radial_atoms5` — the three radial/angular-transform atoms at level `5`

The level-`5` lifts of the three proved level-4 lemmas `OpenPkg.l12H_field`, `OpenPkg.fkH_field`
and `NonlinRows.NRow10aux.mul_phi_Hk` (with `φ z = z/(1+z)`).

The three atoms are the pieces

* `l12Atoms5` — `L₁₂ g` is radial and `ℋ⁵`-honest with `|L₁₂ g|_{ℋ⁵} ≤ C |g|_{ℋ⁵}`;
* `fkAtoms5`  — `FK g` (the zeroth angular moment, `= 3·𝔽_* g`) is likewise;
* `phiAtoms5` — multiplication by the bounded radial profile `φ` satisfies `|φ·g|_{ℋ⁵} ≤ C |g|_{ℋ⁵}`;

and the target `radial_atoms5` is their conjunction with a single constant.

The level-4 proofs are re-run one slot higher, using the four delivered level-`5` bricks

* `Atoms.QangSq5`  — `∫_z (Qang g i)²w² ≤ (∫_θ K²)·|g|²_{ℋ⁵}` for `i ≤ 5`;
* `Atoms.QangDiff5` — `∂_z (Qang g j) = Qang g (j+1)/z` for `j ≤ 3`, continuity for `j ≤ 4`;
* `Atoms.QangAe5`  — the a.e. identity `D_z^i (Qang g 0) = Qang g i`, `i ≤ 5`;
* `Atoms.radialBounded5_majorant` — the pointwise majorant for a bounded radial factor;

together with `Bricks5.L12Bundle5`, the middle stage of the `L₁₂` estimate (the index-raising
recursion up to `k = 4` and the weighted Hardy slot `∫(L₁₂ g)²w² ≤ 107 ∫(Qang g 0)²w²`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.H5.Atoms.QangSq5
import Submission.Work.FTS.StrongEps.H5.Atoms.QangDiff5
import Submission.Work.FTS.StrongEps.H5.Atoms.QangAe5
import Submission.Work.FTS.StrongEps.H5.Atoms.radialBounded5_majorant
import Submission.Work.FTS.StrongEps.H5.Bricks5.L12Bundle5
import Submission.Work.FTS.OpenPkg.l12H_field
import Submission.Work.FTS.OpenPkg.fkH_field
import Submission.Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
import Submission.Work.FTS.OpenPkg.radialMul_field
import Submission.Work.FTS.NonlinRows.NRow10aux.phiSelfFacts
import Submission.Work.FTS.NonlinRows.NRow10aux.hkmem_of_majorant
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.phiDzdIter6_bound
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The `L₁₂` atom at level `5`.**  For a level-`5` open-quadrant datum `g` with vanishing
zero mode, the radial function `z ↦ L₁₂(g)(z)` is `ℋ⁵`-honest and its `ℋ⁵`-norm is controlled
by that of `g`, with an `α`-independent constant.  This is `OpenPkg.l12H_field` one slot higher:
only the pure `D_z`-summands of the level-`5` integrand survive, the `i = 0` one is the weighted
Hardy inequality (`Bricks5.L12Bundle5`) and the `i ≥ 1` ones are the angular moments
`D_z^i L₁₂(g) = -Qang g (i-1)`, bounded by `Atoms.QangSq5`. -/
theorem l12Atoms5 :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ g : Work.FTS.Galerkin.Fn,
      Work.FTS.VocabO.HQo α 5 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.HkMem α 5 (fun z _ => Work.Construction.L12 g z) ∧
      Work.Spaces.HkNorm α 5 (fun z _ => Work.Construction.L12 g z)
        ≤ C * Work.Spaces.HkNorm α 5 g := by
  set AK : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 with hAKdef
  set Cθ : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hCθdef
  have hCθnn : 0 ≤ Cθ := by
    rw [hCθdef]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => Real.rpow_nonneg (Work.Elliptic.sin_two_nonneg_of_mem hθ) _)
  refine ⟨Real.sqrt (112 * AK * Cθ) + 1, ?_, ?_⟩
  · have h := Real.sqrt_nonneg (112 * AK * Cθ)
    linarith
  intro α hαpos hα1 g hg h0
  obtain ⟨hsm, hmem⟩ := hg
  have h0e : Work.Elliptic.L12 g 0 = 0 := by
    rw [← Work.FTS.H2.constructionL12_eq_ellipticL12 g]
    exact h0
  have hQint0 : MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    (Atoms.QangSq5 hsm hmem 0 (by norm_num)).1
  have hqder : ∀ j : ℕ, j ≤ 3 → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => Work.Elliptic.Qang g j w)
        (Work.Elliptic.Qang g (j + 1) z / z) z := (Atoms.QangDiff5 hsm hmem).1
  obtain ⟨hgen, hInt0, hBnd0⟩ := l12Bundle5 hsm hmem h0e hqder hQint0
  set u : ℝ → ℝ := fun z => Work.Elliptic.L12 g z with hudef
  have hgen' : ∀ k : ℕ, k ≤ 4 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) u z = - Work.Elliptic.Qang g k z := by
    intro k hk z hz
    rw [hudef]
    exact hgen k hk z hz
  -- ## the a.e. transfer `D_z^i (L₁₂ g) = -Qang g (i-1)` on `Iz`, `1 ≤ i ≤ 5`
  have htrans : ∀ i : ℕ, 1 ≤ i → i ≤ 5 →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (Work.Elliptic.Qang g (i - 1) z) ^ 2 * (Work.Spaces.w z) ^ 2
          = (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro i hi hi5
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)] with z hz0 hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz0)
    have hsub : i - 1 ≤ 4 := by omega
    have key : Work.Elliptic.DzdIter i u z = - Work.Elliptic.Qang g (i - 1) z := by
      have h := hgen' (i - 1) hsub z hzpos
      rwa [show i - 1 + 1 = i by omega] at h
    rw [key, neg_sq]
  -- ## integrability of every weighted slot
  have hInt : ∀ i : ℕ, i ≤ 5 → MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    intro i hi5
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      simpa only [hudef, Work.Elliptic.DzdIter_zero] using hInt0
    · exact (Atoms.QangSq5 hsm hmem (i - 1) (by omega)).1.congr (htrans i h hi5)
  have hsum_int : ∀ i ∈ Finset.range 6, MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => hInt i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  -- ## the bounds of the individual slots
  have hBnd0' : (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 0 u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 107 * (AK * Work.Spaces.HkSq α 5 g) := by
    have hb : (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter 0 u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 107 * (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      simpa only [hudef, Work.Elliptic.DzdIter_zero] using hBnd0
    have hQ := (Atoms.QangSq5 hsm hmem 0 (by norm_num)).2
    rw [← hAKdef] at hQ
    exact le_trans hb (mul_le_mul_of_nonneg_left hQ (by norm_num))
  have hBndI : ∀ i : ℕ, 1 ≤ i → i ≤ 5 → (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ AK * Work.Spaces.HkSq α 5 g := by
    intro i hi hi5
    rw [hAKdef, ← MeasureTheory.integral_congr_ae (htrans i hi hi5)]
    exact (Atoms.QangSq5 hsm hmem (i - 1) (by omega)).2
  -- ## the sum of the slots
  have hsum_le : (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 6,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 112 * (AK * Work.Spaces.HkSq α 5 g) := by
    rw [MeasureTheory.integral_finsetSum (Finset.range 6) hsum_int,
      Finset.sum_range_succ']
    have h4 : (∑ i ∈ Finset.range 5, (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter (i + 1) u z) ^ 2 * (Work.Spaces.w z) ^ 2))
        ≤ ∑ _i ∈ Finset.range 5, AK * Work.Spaces.HkSq α 5 g :=
      Finset.sum_le_sum fun i hi => by
        rw [Finset.mem_range] at hi
        exact hBndI (i + 1) (by omega) (by omega)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h4
    refine le_trans (add_le_add h4 hBnd0') (le_of_eq ?_)
    ring
  -- ## the energy
  have hHkSq : Work.Spaces.HkSq α 5 (fun z θ => u z)
      = (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 6,
          (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) * Cθ := by
    rw [Work.Elliptic.HkSq_rad, hCθdef]
  have hbound : Work.Spaces.HkSq α 5 (fun z θ => u z)
      ≤ (112 * AK * Cθ) * Work.Spaces.HkSq α 5 g := by
    rw [hHkSq]
    refine le_trans (mul_le_mul_of_nonneg_right hsum_le hCθnn) (le_of_eq ?_)
    ring
  have hXng : 0 ≤ Work.Spaces.HkNorm α 5 g := Real.sqrt_nonneg _
  have hXn : Work.Spaces.HkNorm α 5 (fun z θ => u z)
      ≤ Real.sqrt (112 * AK * Cθ) * Work.Spaces.HkNorm α 5 g := by
    have h112 : 0 ≤ 112 * AK * Cθ := by
      have hAK : 0 ≤ AK := by
        rw [hAKdef]
        exact setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
      nlinarith
    calc Work.Spaces.HkNorm α 5 (fun z θ => u z)
        = Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => u z)) := rfl
      _ ≤ Real.sqrt ((112 * AK * Cθ) * Work.Spaces.HkSq α 5 g) := Real.sqrt_le_sqrt hbound
      _ = Real.sqrt (112 * AK * Cθ) * Work.Spaces.HkNorm α 5 g := by
          rw [Real.sqrt_mul h112]
          rfl
  -- ## membership in `ℋ⁵`
  have hsinI : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta]; norm_num)).1
  have hHkMem : Work.Spaces.HkMem α 5 (fun z θ => u z) := by
    constructor
    · intro z _
      refine MeasureTheory.Integrable.congr (f := fun θ =>
        (∑ i ∈ Finset.range 6, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ?_ ?_
      · exact hsinI.const_mul _
      · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => (Work.FTS.H2.HkIntegrand_rad' α 5 u z hθ).symm)
    · refine MeasureTheory.Integrable.congr (f := fun z =>
        (∑ i ∈ Finset.range 6, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * Cθ) ?_ ?_
      · exact (MeasureTheory.integrable_finsetSum (Finset.range 6) hsum_int).mul_const Cθ
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z _ => ?_)
        simp only [Work.Spaces.Iθ, hCθdef]
        rw [setIntegral_congr_fun (f := fun θ => Work.Spaces.HkIntegrand α 5 (fun z θ => u z) z θ)
          (g := fun θ => (∑ i ∈ Finset.range 6,
              (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          measurableSet_Icc (fun θ hθ => Work.FTS.H2.HkIntegrand_rad' α 5 u z hθ)]
        rw [MeasureTheory.integral_const_mul]
  -- ## back to `Work.Construction.L12`
  have hfun : (fun z (_ : ℝ) => Work.Construction.L12 g z) = (fun z (_ : ℝ) => u z) := by
    funext z θ
    rw [hudef]
    exact congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 g) z
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hHkMem
  · rw [hfun]
    exact le_trans hXn
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hXng)

/-- **The `FK` atom at level `5`.**  The angular moment `FK g z = ∫_θ K(θ)·g(z,θ) dθ` is the
radial function `Qang g 0 = -D_z L₁₂(g)`; at level `5` it is again `ℋ⁵`-honest with an
`α`-independent norm bound.  This is `OpenPkg.fkH_field` one slot higher: `FK g` has no angular
derivatives, and each pure `D_z`-slot is the angular moment `D_z^i (Qang g 0) = Qang g i`
(`Atoms.QangAe5`), bounded by `Atoms.QangSq5`. -/
theorem fkAtoms5 :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ g : Work.FTS.Galerkin.Fn,
      Work.FTS.VocabO.HQo α 5 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.HkMem α 5 (fun z _ => Work.Construction.FK g z) ∧
      Work.Spaces.HkNorm α 5 (fun z _ => Work.Construction.FK g z)
        ≤ C * Work.Spaces.HkNorm α 5 g := by
  set AK : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 with hAKdef
  set Cθ : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hCθdef
  have hCθnn : 0 ≤ Cθ := by
    rw [hCθdef]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => Real.rpow_nonneg (Work.Elliptic.sin_two_nonneg_of_mem hθ) _)
  have hAKnn : 0 ≤ AK := by
    rw [hAKdef]
    exact setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  refine ⟨Real.sqrt (6 * AK * Cθ) + 1, ?_, ?_⟩
  · have h := Real.sqrt_nonneg (6 * AK * Cθ)
    linarith
  intro α hαpos hα1 g hg _
  obtain ⟨hsm, hmem⟩ := hg
  set u : ℝ → ℝ := fun z => Work.Elliptic.Qang g 0 z with hudef
  -- ## the a.e. identity `D_z^i (FK g) = Qang g i` for `i ≤ 5`
  have hae : ∀ᵐ z ∂(MeasureTheory.volume), z ∈ Work.Spaces.Iz → ∀ i ∈ Finset.range 6,
      Work.Elliptic.DzdIter i u z = Work.Elliptic.Qang g i z := by
    filter_upwards [Atoms.QangAe5 hsm hmem, MeasureTheory.Measure.ae_ne volume (0 : ℝ)]
      with z hz hne hzI
    exact hz (lt_of_le_of_ne hzI (Ne.symm hne))
  have htransfer : ∀ i : ℕ, i ≤ 5 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        = (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro i hi
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [hae] with z hz hzI
    rw [← hz hzI i (Finset.mem_range.mpr (by omega : i < 6))]
  have hInt : ∀ i : ℕ, i ≤ 5 → MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    intro i hi
    exact (Atoms.QangSq5 hsm hmem i hi).1.congr (htransfer i hi)
  have hBnd : ∀ i : ℕ, i ≤ 5 → (∫ z in Work.Spaces.Iz,
      (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ AK * Work.Spaces.HkSq α 5 g := by
    intro i hi
    rw [hAKdef, ← MeasureTheory.integral_congr_ae (htransfer i hi)]
    exact (Atoms.QangSq5 hsm hmem i hi).2
  have hsum_int : ∀ i ∈ Finset.range 6, MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => hInt i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have hsum_le : (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 6,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 6 * (AK * Work.Spaces.HkSq α 5 g) := by
    rw [MeasureTheory.integral_finsetSum (Finset.range 6) hsum_int]
    calc ∑ i ∈ Finset.range 6, (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∑ _i ∈ Finset.range 6, (AK * Work.Spaces.HkSq α 5 g) :=
          Finset.sum_le_sum fun i hi => hBnd i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      _ = 6 * (AK * Work.Spaces.HkSq α 5 g) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  -- ## the `ℋ⁵`-energy and the norm bound
  have hHkSq : Work.Spaces.HkSq α 5 (fun z θ => u z) = (∫ z in Work.Spaces.Iz,
        ∑ i ∈ Finset.range 6, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) * Cθ := by
    rw [Work.Elliptic.HkSq_rad, hCθdef]
  have hbound : Work.Spaces.HkSq α 5 (fun z θ => u z) ≤ (6 * AK * Cθ) * Work.Spaces.HkSq α 5 g := by
    rw [hHkSq]
    refine le_trans (mul_le_mul_of_nonneg_right hsum_le hCθnn) (le_of_eq ?_)
    ring
  have hXng : 0 ≤ Work.Spaces.HkNorm α 5 g := Real.sqrt_nonneg _
  have hXn : Work.Spaces.HkNorm α 5 (fun z θ => u z)
      ≤ Real.sqrt (6 * AK * Cθ) * Work.Spaces.HkNorm α 5 g := by
    have h6 : 0 ≤ 6 * AK * Cθ := by nlinarith
    calc Work.Spaces.HkNorm α 5 (fun z θ => u z)
        = Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => u z)) := rfl
      _ ≤ Real.sqrt ((6 * AK * Cθ) * Work.Spaces.HkSq α 5 g) := Real.sqrt_le_sqrt hbound
      _ = Real.sqrt (6 * AK * Cθ) * Work.Spaces.HkNorm α 5 g := by
          rw [Real.sqrt_mul h6]
          rfl
  -- ## membership in `ℋ⁵`
  have hsinI : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta]; norm_num)).1
  have hHkMem : Work.Spaces.HkMem α 5 (fun z θ => u z) := by
    constructor
    · intro z hz
      refine MeasureTheory.Integrable.congr (f := fun θ =>
        (∑ i ∈ Finset.range 6, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ?_ ?_
      · exact hsinI.const_mul _
      · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => (Work.FTS.H2.HkIntegrand_rad' α 5 u z hθ).symm)
    · refine MeasureTheory.Integrable.congr (f := fun z =>
        (∑ i ∈ Finset.range 6, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) * Cθ) ?_ ?_
      · exact (MeasureTheory.integrable_finsetSum (Finset.range 6) hsum_int).mul_const Cθ
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z _ => ?_)
        simp only [Work.Spaces.Iθ, hCθdef]
        rw [setIntegral_congr_fun (f := fun θ => Work.Spaces.HkIntegrand α 5 (fun z θ => u z) z θ)
          (g := fun θ => (∑ i ∈ Finset.range 6,
              (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          measurableSet_Icc (fun θ hθ => Work.FTS.H2.HkIntegrand_rad' α 5 u z hθ)]
        rw [MeasureTheory.integral_const_mul]
  -- ## `FK g` is the radial function `u`
  have hfun : (fun z (_ : ℝ) => Work.Construction.FK g z) = (fun z (_ : ℝ) => u z) := by
    funext z θ
    rw [hudef]
    simp only [Work.Construction.FK, Work.Elliptic.Qang, Work.Spaces.DzIter_zero]
    rw [← Work.Elliptic.Ktheta_eq_K]
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hHkMem
  · rw [hfun]
    exact le_trans hXn
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hXng)

/-- **The `φ`-multiplication atom at level `5`.**  Multiplication by the bounded radial profile
`φ(z) = z/(1+z)` does not change the `ℋ⁵`-norm up to a universal constant.  This is
`NonlinRows.NRow10aux.mul_phi_Hk` one slot higher: the pointwise majorant
`HkIntegrand α 5 (φ·g) ≤ K·Br²·HkIntegrand α 5 g` is `Atoms.radialBounded5_majorant` applied
with the uniform bound `Br = 10⁴` for `|D_z^b φ|`, `b ≤ 5`
(`StrongPersist.H6Rows.Npair6SupAux.phiDzdIter6_bound`), and `hkmem_of_majorant` transports
`HkMem`/`HkSq` along it. -/
theorem phiAtoms5 :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ g : Work.FTS.Galerkin.Fn,
      Work.FTS.VocabO.HQo α 5 g →
      Work.Spaces.HkMem α 5 (fun z θ => z / (1 + z) * g z θ) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * g z θ)
        ≤ C * Work.Spaces.HkNorm α 5 g := by
  obtain ⟨K, hKpos, hK⟩ := Atoms.radialBounded5_majorant
  have hphiSO : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z)) := by
    simpa [Work.FTS.NonlinRows.NRow10aux.phiF]
      using Work.FTS.NonlinRows.NRow10aux.phiSelf_smoothOpen
  refine ⟨Real.sqrt (K * 10000 ^ 2) + 1, by positivity, ?_⟩
  intro α hα hα1 g hg
  obtain ⟨hgSO, hgm⟩ := hg
  have hSO : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z / (1 + z) * g z θ) :=
    Work.FTS.OpenPkg.smoothOpen_sepMul hphiSO hgSO
  have hmaj' : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.HkIntegrand α 5 (fun z θ => z / (1 + z) * g z θ) z θ
        ≤ (K * 10000 ^ 2) * Work.Spaces.HkIntegrand α 5 g z θ := by
    intro z hz θ hθ
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [← hz0]
      have h1 : Work.Spaces.HkIntegrand α 5 (fun z θ => z / (1 + z) * g z θ) 0 θ = 0 := by
        simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
        simp
      have h2 : Work.Spaces.HkIntegrand α 5 g 0 θ = 0 := by
        simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
        simp
      rw [h1, h2, mul_zero]
    · exact hK α (fun z => z / (1 + z)) g 10000 hphiSO hgSO (by norm_num)
        (fun b hb z hz => Work.FTS.StrongPersist.H6Rows.Npair6SupAux.phiDzdIter6_bound
          b (by omega) z hz) z θ hzpos hθ.1 hθ.2
  obtain ⟨hmem, hsq⟩ :=
    Work.FTS.NonlinRows.NRow10aux.hkmem_of_majorant α 5
      (mul_nonneg hKpos.le (by norm_num : (0 : ℝ) ≤ 10000 ^ 2)) hSO hgm hmaj'
  refine ⟨hmem, ?_⟩
  have hXn : 0 ≤ Work.Spaces.HkNorm α 5 g := Real.sqrt_nonneg _
  have hsqrt : Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * g z θ)
      ≤ Real.sqrt (K * 10000 ^ 2) * Work.Spaces.HkNorm α 5 g := by
    rw [Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => z / (1 + z) * g z θ))
        ≤ Real.sqrt ((K * 10000 ^ 2) * Work.Spaces.HkSq α 5 g) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (K * 10000 ^ 2) * Real.sqrt (Work.Spaces.HkSq α 5 g) :=
          Real.sqrt_mul (by positivity) _
      _ = Real.sqrt (K * 10000 ^ 2) * Work.Spaces.HkNorm α 5 g := rfl
  calc Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * g z θ)
      ≤ Real.sqrt (K * 10000 ^ 2) * Work.Spaces.HkNorm α 5 g := hsqrt
    _ ≤ (Real.sqrt (K * 10000 ^ 2) + 1) * Work.Spaces.HkNorm α 5 g := by
        refine mul_le_mul_of_nonneg_right ?_ hXn
        linarith

/-- **The three radial/angular-transform atoms at level `5`**: the level-`5` lifts of the three
proved level-4 lemmas `OpenPkg.l12H_field`, `OpenPkg.fkH_field` and
`NonlinRows.NRow10aux.mul_phi_Hk` (with `φ z = z/(1+z)`).

The statements are literal `4 → 5` transliterations (`Xn → HkNorm α 5`, `HQo α 4 → HQo α 5`):
`L₁₂ g` is radial and `ℋ⁵`-honest with `|L₁₂ g|_{ℋ⁵} ≤ C |g|_{ℋ⁵}`; so is `FK g` (which is
`3·𝔽_* g`); and multiplication by the bounded radial profile `φ` satisfies
`|φ·g|_{ℋ⁵} ≤ C |g|_{ℋ⁵}`.

They are the atoms of the level-`5` nonlinear blocks.  Proofs: re-run the three level-4 files with
one more slot, i.e. five (rather than four) radial `D_z`-slots for the two radial transforms; the
lemmas `Qang_sq_leQ_open` and `Qang_sq_w_sq_integral_open` of `OpenPkg/QangOpen.lean` are stated
with `HkMem α 4` (and `i ≤ 4`) and need their `HkMem α 5` versions; for the `φ`-multiplication the
`radialBounded_majorant` machinery of `Nonlinear.RadialProd` is used (the level-4 bound
`phiSelf_DzdIter_bound_phiF : |D_z^b φ| ≤ 1` is stated for `b ≤ 4` and is needed at `b = 5`,
where `D_z^5 φ = t(1-t)(1-30t+150t²-240t³+120t⁴)`, `t = z/(1+z)`, of sup `≈ 0.25 < 1`).  The
`θ`-derivatives of `L₁₂ g` and `FK g` vanish identically (a `θ`-independent function), which is
what the level-`5` mixed slots use. -/
theorem radial_atoms5 :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ g : Work.FTS.Galerkin.Fn,
      Work.FTS.VocabO.HQo α 5 g → Work.Construction.L12 g 0 = 0 →
      (Work.Spaces.HkMem α 5 (fun z _ => Work.Construction.L12 g z) ∧
        Work.Spaces.HkNorm α 5 (fun z _ => Work.Construction.L12 g z)
          ≤ C * Work.Spaces.HkNorm α 5 g) ∧
      (Work.Spaces.HkMem α 5 (fun z _ => Work.Construction.FK g z) ∧
        Work.Spaces.HkNorm α 5 (fun z _ => Work.Construction.FK g z)
          ≤ C * Work.Spaces.HkNorm α 5 g) ∧
      (Work.Spaces.HkMem α 5 (fun z θ => z / (1 + z) * g z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * g z θ)
          ≤ C * Work.Spaces.HkNorm α 5 g) := by
  obtain ⟨C1, hC1pos, hC1⟩ := l12Atoms5
  obtain ⟨C2, hC2pos, hC2⟩ := fkAtoms5
  obtain ⟨C3, hC3pos, hC3⟩ := phiAtoms5
  refine ⟨max (max C1 C2) C3, ?_, ?_⟩
  · exact lt_of_lt_of_le hC1pos (le_trans (le_max_left C1 C2) (le_max_left _ C3))
  intro α hα hα1 g hg h0
  obtain ⟨h1m, h1b⟩ := hC1 α hα hα1 g hg h0
  obtain ⟨h2m, h2b⟩ := hC2 α hα hα1 g hg h0
  obtain ⟨h3m, h3b⟩ := hC3 α hα hα1 g hg
  have hng : 0 ≤ Work.Spaces.HkNorm α 5 g := Real.sqrt_nonneg _
  refine ⟨⟨h1m, ?_⟩, ⟨h2m, ?_⟩, ⟨h3m, ?_⟩⟩
  · exact le_trans h1b (mul_le_mul_of_nonneg_right
      (le_trans (le_max_left C1 C2) (le_max_left _ C3)) hng)
  · exact le_trans h2b (mul_le_mul_of_nonneg_right
      (le_trans (le_max_right C1 C2) (le_max_left _ C3)) hng)
  · exact le_trans h3b (mul_le_mul_of_nonneg_right
      (le_max_right (max C1 C2) C3) hng)

end Work.FTS.StrongEps.H5
