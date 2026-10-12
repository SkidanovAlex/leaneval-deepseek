import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.PotCubic_exists
import Submission.Work.BoseBoxFock.frkCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.lowBandDefs` — the algebra of the low band and the two residuals of LB1

`Work.BoseBoxFock.FRK.LowBandNPlusLinear` (LB1 of `LEAD_DESIGN_formrowkin_v2.md` §4) is

    (F_{P_H} − F_{excited}) ≤ K·ℓ⁻³·(Σ_{s∈excited}|f_L s|)·(Σ_{k∈excited∖P_H}|Ŵ₁ k|)·cnPlus ℓ Φ,

with `F_L = (∫ star Θ · potCubic … L … Θ).re`, `Θ = boxRestrictC ℓ Φ`.

This module contains

* `potCubicAtom` — the weight-free `(s,k)`-word of the cubic row,
* `potCubic_eq_sum_atom` — `potCubic` as the weighted sum of the atoms,
* `potCubic_lowBand_split` / `potCubic_lowBand_split'` — `potCubic(excited) = potCubic(P_H) +
  potCubic(LB)` as operators,
* **(A)** `LowBandAtomAbs` — the weight-free absolute two-slot bound (the analytic heart),
* **(B)** `LowBandWeightArith` — the weight-spread arithmetic.

See `FINDING_lowBandNPlusLinear.md` for the analysis of (A) and (B).
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.FRK

open Work.BoseBoxFock Work.BoseB4 Work.BoseDict

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The weight-free atom of the cubic row, and the low-band split -/

/-- The `(s,k)`-summand of `potCubic` **without** its scalar weight `ℓ⁻³f_L(s)Ŵ₁(k)`: the four
terms of FS's `eq:kroelleQ3z` (the word `ã_s†a_{s−k}a_k` and its formal adjoint). -/
noncomputable def potCubicAtom {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {m : ℕ} [NeZero m] {ι : Type*}
    (B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ))
    (f g : Mode → Fin m → ℝ) (s k : Mode) : ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ) :=
  ((B (rankOnePair (evec0 m) (f (s - k)))) ∘ (B (rankOnePair (g s) (f k)))
      - B ((rankOnePair (evec0 m) (f (s - k))).comp (rankOnePair (g s) (f k))))
    + ((B (rankOnePair (f k) (g s))) ∘ (B (rankOnePair (f (s - k)) (evec0 m)))
      - B ((rankOnePair (f k) (g s)).comp (rankOnePair (f (s - k)) (evec0 m))))

/-- `potCubic` is the weighted sum of the atoms. -/
theorem potCubic_eq_sum_atom {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {m : ℕ} [NeZero m] {ι : Type*}
    (B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ))
    (f g : Mode → Fin m → ℝ) (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode)
    (Θ : (ι → Ω) → ℂ) :
    potCubic B f g PHs E Θ
      = (E.ell ^ (-(3 : ℝ))) • (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ PHs,
          (E.fL s * E.W1 k) • potCubicAtom B f g s k Θ) := by
  funext x
  simp only [potCubic, potCubicAtom, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
    Finset.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring_nf

/-- `FockData.PHset E ⊆ excited`. -/
theorem PHset_subset_excited {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) :
    F.PHset E ⊆ Work.BoseB7.excited Mode := by
  intro k hk
  rw [Work.BoseB7.FockData.PHset, Finset.mem_filter] at hk
  exact hk.1

/-- **The low-band split** (operator identity): the `k`-sum over the excited labels is the
`P_H`-sum plus the low band `excited ∖ P_H`. -/
theorem potCubic_lowBand_split {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {m : ℕ} [NeZero m] {ι : Type*}
    (B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ))
    (f g : Mode → Fin m → ℝ) (PHs : Finset Mode) (hsub : PHs ⊆ Work.BoseB7.excited Mode)
    (E : Work.BoseB7.Q3Env Mode) :
    potCubic B f g (Work.BoseB7.excited Mode) E
      = potCubic B f g PHs E + potCubic B f g (Work.BoseB7.excited Mode \ PHs) E := by
  have hunion : PHs ∪ (Work.BoseB7.excited Mode \ PHs) = Work.BoseB7.excited Mode :=
    Finset.union_sdiff_of_subset hsub
  have hdis : Disjoint PHs (Work.BoseB7.excited Mode \ PHs) := Finset.disjoint_sdiff
  funext Θ
  have h := potCubic_finset_split B f g PHs (Work.BoseB7.excited Mode \ PHs) hdis E Θ
  rw [hunion] at h
  exact h

/-- The same split, solved for the `P_H`-sum. -/
theorem potCubic_lowBand_split' {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode]
    {m : ℕ} [NeZero m] {ι : Type*}
    (B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ))
    (f g : Mode → Fin m → ℝ) (PHs : Finset Mode) (hsub : PHs ⊆ Work.BoseB7.excited Mode)
    (E : Work.BoseB7.Q3Env Mode) :
    potCubic B f g PHs E
      = potCubic B f g (Work.BoseB7.excited Mode) E
        - potCubic B f g (Work.BoseB7.excited Mode \ PHs) E := by
  rw [potCubic_lowBand_split B f g PHs hsub E]
  abel

/-! ## 2. The two residuals of LB1 -/

/- ⚠ **DECLARED FALSE by the fleet's prover; do not re-file.  Read
`FINDING_lowBandAtomAbs_FALSE.md` and `FINDING_lowBandNPlusLinear_session2.md` §2-§4 before
believing or re-using this statement.**  The prover's mechanism is right — the atoms are
`2√(n−1)γ_s conj(c_{k,s−k})` (the design's own formula), the sum over the low band does not
dilute, and "each atom ≪ RHS but there are `M_sM_k` of them" — but the *exponents* in that report
use `K_H = X^{−8/3}` whereas the proved `Work.BoseB7.KH_val` gives `K_H = t^{−549/1292} =
X^{−549/4}`; with the correct `K_H` the low-band count is `M_k ≍ t^{−0.239}` (not `t^{−1.489}`)
and that particular ratio tends to `0`.  Either way (A) is the *wrong intermediate*: what LB1
needs is the *weighted* statement, whose truth rests on the `IsLowB` kinetic budget (§4 of the
session-2 FINDING) and not on any statement about the unweighted sum. -/

/-- **(A) The weight-free absolute two-slot low-band bound.** [FALSE — do not re-file]

For every admissible parameter point, every admissible box state `Φ` and every honest family `e`
satisfying FS's pinning hypotheses, the *absolute* sum of the atoms of the low band
`excited ∖ P_H`, taken over the *support of the weight* `f_L` (where `f_L` is zero the term carries
no weight in the target, and the sum over the remaining labels would not be `N`-uniform), is
dominated by `C·√(2μℓ³)·cnPlus`, with `C` a *fixed* constant.

This is the analytic heart of LB1: the weights `f_L`, `Ŵ₁` and the prefactor `ℓ⁻³` have been
stripped, so it is strictly more general than the target; it is the place where the excited-count
structure of the admissible class enters (one annihilator per side is paired with `n₊ = Q`, and
the surviving condensate factor is `≤ √n ≤ √(2μℓ³)`). -/
def LowBandAtomAbs (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (Nmin : ℝ → ℕ) (ε₀ C : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Nmin μ ≤ (HM μ).N) →
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
        (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
        0 < Work.BoseBoxFix.normB v μ n Φ →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
          (Φ : Submission.BoseGases.X n → ℝ) →
        ∀ (e : Fin (HM μ).m → Ω → ℂ),
          (∀ l, Measurable (e l)) →
          (∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C) →
          (∀ l, Function.support (e l)
            ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBox.sideAt μ (BoseGases.a v))) →
          (∀ l l', (∫ z : Ω, star (e l z) * e l' z)
            = (if l = l' then (1 : ℂ) else 0)) →
          (∀ l l', MeasureTheory.Integrable (fun z : Ω => star (e l z) * e l' z)) →
          (∀ l, MeasureTheory.MemLp (e l) ⊤) →
          (∃ c : ℂ, (starRingEnd ℂ) c * c
              = ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)⁻¹ ∧
            e 0 =ᵐ[MeasureTheory.volume] fun x => c * Work.BoseK15.corpusBox.thetaFun
                (Work.BoseBox.sideAt μ (BoseGases.a v)) x) →
          (∀ (k : Lab (HM μ).N) (l : Fin (HM μ).m),
            (∫ z : Ω, star (e l z)
                * Work.BoseK15.corpusBox.qVec (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k) z)
              = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
                  * (HM μ).f k l : ℝ) : ℂ)) →
          (∀ (s : Lab (HM μ).N) (l : Fin (HM μ).m), s ≠ 0 →
            (∫ z : Ω, star (e l z)
                * Work.BoseK15.corpusBox.thetaExp (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N s) z)
              = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
                  * (HM μ).g s l : ℝ) : ℂ)) →
          (∫ z : Ω, star (e 0 z)
              * Work.BoseK15.corpusBox.thetaFun (Work.BoseBox.sideAt μ (BoseGases.a v)) z)
            = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) →
          ∀ (T_NH : (Fin (HM μ).m → ℝ) →ₗ[ℝ] (Fin (HM μ).m → ℝ)),
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NH
                = Work.BoseB4.dGamma (HM μ).m T_NH →
            (∑ s ∈ (Work.BoseB7.excited (Lab (HM μ).N)).filter
                  (fun s => (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.fL s ≠ 0),
                ∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N)
                  \ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E,
                  |(Work.BoseDict.cIPn n
                      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ)
                      (potCubicAtom (fun T => boxSlotSum e T) (HM μ).f (HM μ).g s k
                        (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ))).re|)
              ≤ C * Real.sqrt (2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3)
                  * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Φ : Submission.BoseGases.X n → ℝ)

/- ⚠ **REFUTED — see `FINDING_lowBandNPlusLinear_session2.md` §2.  Do not re-file.**  The statement
below is FALSE: it concerns the *environment only* and fails in the *small-lattice* regime — take
`Nmin ≡ 0` and an honest family with `(HM μ).N = 4` (`exists_honestModes v μ 4`): for small
`t = μ(a v)³` every one of the `729` lattice labels lies simultaneously in the `f_L`-ball and in
the low band, so the two sums on the right are bounded while `√(2μℓ³) → ∞`. -/

/-- **(B) The weight-spread arithmetic of the low band.** [FALSE — do not re-file]

In the `√(2μℓ³)`-normalisation, *every single* weight of the low band is dominated by the two sums:
`√(2μℓ³)·|f_L s|·|Ŵ₁ k| ≤ K·(Σ|f_L|)(Σ|Ŵ₁|)` for all `s ∈ excited` and `k ∈ excited ∖ P_H`.  The
statement is pointwise in the weights (no `Finset.sup`), which is exactly the form needed to pull
the weights out of the atom sum in the assembly.  Only the environment is involved, so this is the
pure lattice-counting statement (LB2-type) of the design; its margin is `t^{0.09}`. -/
def LowBandWeightArith (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (Nmin : ℝ → ℕ) (ε₀ K : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Nmin μ ≤ (HM μ).N) →
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
      ∀ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
        ∀ k ∈ Work.BoseB7.excited (Lab (HM μ).N)
            \ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E,
          Real.sqrt (2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3)
              * |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.fL s|
              * |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k|
            ≤ K * (∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
                |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.fL s|)
              * (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N)
                    \ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E,
                  |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k|)

/-! ## 2. Linearity of `cIPn` over the atom sum

The assembly of LB1 expands `potCubic` into its atoms and takes the finite `(s,k)`-sum *out of the
integral*.  The only ingredient is integrability of each atom-integrand (supplied by
`Work.BoseBoxFock.FRK.cIPn_potCubic_integrable` in the target file). -/

/-- `cIPn` is additive in its second argument (given integrability). -/
theorem cIPn_add {d : ℕ} {Θ X Y : Work.BoseDict.Xn d → ℂ}
    (hX : MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Θ x) * X x))
    (hY : MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Θ x) * Y x)) :
    Work.BoseDict.cIPn d Θ (X + Y)
      = Work.BoseDict.cIPn d Θ X + Work.BoseDict.cIPn d Θ Y := by
  simp only [Work.BoseDict.cIPn]
  rw [show (fun x => (starRingEnd ℂ) (Θ x) * (X + Y) x)
        = (fun x => (starRingEnd ℂ) (Θ x) * X x + (starRingEnd ℂ) (Θ x) * Y x) from
      funext fun x => by simp only [Pi.add_apply]; ring]
  rw [MeasureTheory.integral_add hX hY]

/-- `cIPn` is homogeneous under the real scalars. -/
theorem cIPn_smul {d : ℕ} (c : ℝ) {Θ X : Work.BoseDict.Xn d → ℂ} :
    Work.BoseDict.cIPn d Θ (c • X) = (c : ℂ) * Work.BoseDict.cIPn d Θ X := by
  simp only [Work.BoseDict.cIPn]
  rw [show (fun x => (starRingEnd ℂ) (Θ x) * (c • X) x)
        = (fun x => ((c : ℂ)) * ((starRingEnd ℂ) (Θ x) * X x)) from
      funext fun x => by simp only [Pi.smul_apply, Complex.real_smul]; ring]
  rw [MeasureTheory.integral_const_mul]

/-- The `star Θ`-multiple of a real-scaled finite sum is integrable when its summands are. -/
theorem integrable_star_mul_sum {ι : Type*} {d : ℕ} (S : Finset ι) (w : ι → ℝ)
    {F : ι → Work.BoseDict.Xn d → ℂ} {Θ : Work.BoseDict.Xn d → ℂ}
    (hF : ∀ i ∈ S, MeasureTheory.Integrable
      (fun x => (starRingEnd ℂ) (Θ x) * F i x)) :
    MeasureTheory.Integrable
      (fun x => (starRingEnd ℂ) (Θ x) * (∑ i ∈ S, (w i : ℝ) • F i) x) := by
  classical
  rw [show (fun x => (starRingEnd ℂ) (Θ x) * (∑ i ∈ S, (w i : ℝ) • F i) x)
        = (fun x => ∑ i ∈ S, ((w i : ℂ)) * ((starRingEnd ℂ) (Θ x) * F i x)) from
      funext fun x => by
        simp only [Finset.sum_apply, Pi.smul_apply, Complex.real_smul]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring]
  exact integrable_finsetSum S (fun i hi => (hF i hi).const_mul _)

/-- **Linearity of `cIPn` over the weighted atom sum** (the expansion of
`potCubic_eq_sum_atom`). -/
theorem cIPn_sum_smul {ι : Type*} {d : ℕ} (S : Finset ι) (w : ι → ℝ)
    {F : ι → Work.BoseDict.Xn d → ℂ} {Θ : Work.BoseDict.Xn d → ℂ}
    (hF : ∀ i ∈ S, MeasureTheory.Integrable
      (fun x => (starRingEnd ℂ) (Θ x) * F i x)) :
    Work.BoseDict.cIPn d Θ (∑ i ∈ S, (w i : ℝ) • F i)
      = ∑ i ∈ S, (w i : ℂ) * Work.BoseDict.cIPn d Θ (F i) := by
  have hsum : Work.BoseDict.cIPn d Θ (∑ i ∈ S, (w i : ℝ) • F i)
      = ∑ i ∈ S, Work.BoseDict.cIPn d Θ ((w i : ℝ) • F i) := by
    simp only [Work.BoseDict.cIPn]
    rw [show (fun x => (starRingEnd ℂ) (Θ x) * (∑ i ∈ S, (w i : ℝ) • F i) x)
          = (fun x => ∑ i ∈ S, (starRingEnd ℂ) (Θ x) * ((w i : ℝ) • F i) x) from
        funext fun x => by simp only [Finset.sum_apply]; rw [Finset.mul_sum]]
    rw [integral_finsetSum S (fun i hi => by
      rw [show (fun x => (starRingEnd ℂ) (Θ x) * ((w i : ℝ) • F i) x)
            = (fun x => ((w i : ℂ)) * ((starRingEnd ℂ) (Θ x) * F i x)) from
          funext fun x => by simp only [Pi.smul_apply, Complex.real_smul]; ring]
      exact (hF i hi).const_mul _)]
  rw [hsum]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Work.BoseDict.cIPn]
  rw [show (fun x => (starRingEnd ℂ) (Θ x) * ((w i : ℝ) • F i) x)
        = (fun x => ((w i : ℂ)) * ((starRingEnd ℂ) (Θ x) * F i x)) from
      funext fun x => by simp only [Pi.smul_apply, Complex.real_smul]; ring]
  rw [MeasureTheory.integral_const_mul]

end Work.BoseBoxFock.FRK
