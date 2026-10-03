/-
# The left height-zero range `l₁ = 0`, `l₂ ≥ 1` of the bounded-height main-part estimate

`Work.KMTPlan.A6.BoundedHMain.heightZeroLeft` is the range `l₁ = 0` of
`Work.KMTPlan.A6.HeightZeroMainBound` (the bounded-height `(2,2,1)` estimate for the concrete §5
columns `Work.KMTAreas.A7.mainPartTuple` in the low case `k₁ = 0 ∨ k₂ = 0`).

The proof is the pointwise splitting

  `mainPartTuple = (band §6 error) + (off-band §6 error) + loMixedTuple`

of the model-approximation chapter of §6--§8 of Krause--Mirek--Tao, together with the
subadditivity of the variational norm and of `eLpNorm` and the three constituent estimates:

* `bandErr_of_singleScale` (`HZ/Err.lean`): the band-restricted §6 error, summed over the lacunary
  scales at bounded height (from the single-scale statement `SingleScaleErrBand`);
* `Work.Analysis.LoMixedPorts.offBandBoundedHeight`: the off-band §6 error at bounded height;
* `modelBound` (`HZ/Model.lean`): the §8 model bound at bounded height.

The two linear inputs of the model bound are the *level-`0`* estimate
`Work.KMTPlan.A6.LowModApproxBoundedH.plainVarF_lev0` and the bounded-height `g`-side estimate
`gsideBoundedHeight` (`HZ/Gside.lean`); the §6 crux is the `ℓ¹(ℤ²)` mass bound `symDMassLeOne`
(`HZ/SymDMass.lean`).  No `AreaA1` is used.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.BoundedHMain.Defs
import Submission.Work.KMTPlan.A6.BoundedHMain.HZ.Model
import Submission.Work.KMTPlan.A6.BoundedHMain.HZ.SingleScale
import Submission.Work.Analysis.LoMixedPorts.offBandBoundedHeight
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6.BoundedHMain

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7 Work.KMTContract
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

noncomputable section

/-- **The left height-zero range `l₁ = 0`, `l₂ ≥ 1`, from the single-scale §6 estimate.** -/
theorem heightZeroLeft_aux (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℕ)
    (hs : SingleScaleErrBand P) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ ≤ B → (k₁ = 0 ∨ k₂ = 0) → 1 ≤ l₂ →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x))
          1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  obtain ⟨Kb, hKb⟩ := bandErr_of_singleScale P hd r hr C₀ hC₀ ρ hρ hρ1 B hs
  obtain ⟨Ko, hKo⟩ := Work.Analysis.LoMixedPorts.offBandBoundedHeight P hd r hr C₀ hC₀ ρ hρ hρ1 B
  obtain ⟨Km, hKm⟩ := modelBoundLoMixed P hd r hr C₀ hC₀ ρ hρ hρ1 B
  refine ⟨fun Λ => max 1 (Kb Λ + Ko Λ + Km Λ), ?_⟩
  intro a Λ l₂ k₁ k₂ f g hΛ ha ha1 hlB hk hl₂
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  -- the three families
  set bf : ℕ → ℤ → ℂ := fun n x =>
    if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n
      ∧ Work.KMTAreas.A7.loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) then
      Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
        - Work.KMTAreas.A7.loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x
    else 0 with hbf
  set of_ : ℕ → ℤ → ℂ := fun n x =>
    if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n
      ∧ ¬ Work.KMTAreas.A7.loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) then
      Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
        - Work.KMTAreas.A7.loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x
    else 0 with hof
  set md : ℕ → ℤ → ℂ := fun n x =>
    (if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
      Work.KMTAreas.A7.loMixedOp ρ P (Nat.floor (a n)) l₂ k₁ k₂ f g x
    else 0) with hmd
  -- the pointwise splitting
  have hsplit : ∀ n x, Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
      = bf n x + of_ n x + md n x := by
    intro n x
    rw [Work.KMTAreas.A7.mainPartTuple_apply ρ P C₀ a f g 0 l₂ k₁ k₂ n x]
    by_cases hg : Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n
    · by_cases hb : Work.KMTAreas.A7.loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n))
      · have h1 : Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n
            ∧ Work.KMTAreas.A7.loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) := ⟨hg, hb⟩
        have h2 : ¬ (Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n
            ∧ ¬ Work.KMTAreas.A7.loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n))) :=
          fun h => h.2 hb
        simp only [hbf, hof, hmd, if_pos h1, if_neg h2, if_pos hg,
          Work.KMTAreas.A7.mainPartTuple_apply, Work.KMTAreas.A7.loMixedTuple_apply]
        ring_nf
      · have h1 : ¬ (Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n
            ∧ Work.KMTAreas.A7.loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n))) :=
          fun h => hb h.2
        have h2 : Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n
            ∧ ¬ Work.KMTAreas.A7.loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) := ⟨hg, hb⟩
        simp only [hbf, hof, hmd, if_neg h1, if_pos h2, if_pos hg,
          Work.KMTAreas.A7.mainPartTuple_apply, Work.KMTAreas.A7.loMixedTuple_apply]
        ring_nf
    · have h1 : ¬ (Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n
          ∧ Work.KMTAreas.A7.loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n))) :=
        fun h => hg h.1
      have h2 : ¬ (Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n
          ∧ ¬ Work.KMTAreas.A7.loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n))) :=
        fun h => hg h.1
      simp only [hbf, hof, hmd, if_neg h1, if_neg h2, if_neg hg,
        Work.KMTAreas.A7.mainPartTuple_apply, Work.KMTAreas.A7.loMixedTuple_apply]
      ring_nf
  -- the pointwise variational bound
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x)
      ≤ PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => bf n x)
        + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => of_ n x)
        + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => md n x) := by
    intro x
    have hfun : (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x)
        = (fun n : ℕ => bf n x) + (fun n : ℕ => of_ n x) + (fun n : ℕ => md n x) := by
      funext n
      exact hsplit n x
    rw [hfun]
    refine (variationalNorm_add_le hr1 _ _).trans ?_
    exact add_le_add (variationalNorm_add_le hr1 _ _) le_rfl
  -- the degenerate case `f = 0`
  by_cases hf0 : MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count = 0
  · have hz : f = 0 := by
      have h := (MeasureTheory.eLpNorm_eq_zero_iff (p := (2 : ENNReal)) (by norm_num)).mp hf0
      funext x
      simpa using MeasureTheory.Measure.ae_count_iff.mp h x
    have hfun : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x)) = 0 := by
      funext x
      have h0 : (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x)
          = fun _ : ℕ => (0 : ℂ) := by
        funext n
        rw [hz]
        exact Work.KMTAreas.A7.lpss_mainPartTuple_zero_left ρ P C₀ a g l₂ k₁ k₂ n x
      rw [h0]
      exact Work.KMTAreas.A7.variationalNorm_zero r hr1
    rw [hfun, MeasureTheory.eLpNorm_zero]
    simp
  -- the degenerate case where `g` is not in `ℓ²`
  by_cases hgT : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count = ⊤
  · have hK0 : ((max 1 (Kb Λ + Ko Λ + Km Λ) : NNReal) : ENNReal) ≠ 0 := by
      rw [Ne, ENNReal.coe_eq_zero]
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    rw [hgT, ENNReal.mul_top (mul_ne_zero hK0 hf0)]
    exact le_top
  -- the main case: `g ∈ ℓ²`, hence bounded
  obtain ⟨Cg, hCg⟩ :=
    Work.KMTAreas.A7.bounded_of_eLpNorm_count_lt_top (p := (2 : ENNReal)) (by norm_num)
      (lt_top_iff_ne_top.mpr hgT)
  have hb := hKb a Λ l₂ k₁ k₂ f g hΛ ha ha1 hlB hl₂
  have ho := hKo a Λ l₂ k₁ k₂ f g hΛ ha ha1 hlB hk hl₂
  have hm := hKm a Λ l₂ k₁ k₂ f g Cg hΛ ha ha1 hlB hl₂ hCg
  -- the triangle inequality in `ℓ¹`
  refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
    (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x))
    (g := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => bf n x)
      + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => of_ n x)
      + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => md n x))
    (fun x => by rw [enorm_eq_self, enorm_eq_self]; exact hpt x)).trans ?_
  refine (MeasureTheory.eLpNorm_add_le le_rfl).trans ?_
  refine (add_le_add (MeasureTheory.eLpNorm_add_le le_rfl) le_rfl).trans ?_
  refine (add_le_add (add_le_add hb ho) hm).trans ?_
  -- the arithmetic of the constant
  have hfac : (Kb Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
      + (Ko Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
      + (Km Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
      = ((Kb Λ : ENNReal) + Ko Λ + Km Λ) * MeasureTheory.eLpNorm f 2
          MeasureTheory.Measure.count * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    ring
  rw [hfac]
  refine mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl
  rw [← ENNReal.coe_add, ← ENNReal.coe_add]
  exact ENNReal.coe_le_coe.mpr (le_max_right _ _)

theorem heightZeroLeft (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℕ) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ ≤ B → (k₁ = 0 ∨ k₂ = 0) → 1 ≤ l₂ →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x))
          1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
  heightZeroLeft_aux P hd r hr C₀ hC₀ ρ hρ hρ1 B (Work.KMTAreas.A7.singleScaleErrBand P hd)

end

end Work.KMTPlan.A6.BoundedHMain
