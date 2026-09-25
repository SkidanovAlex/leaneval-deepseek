import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusPartitionDefs
import Submission.Work.BourgainPlan.Maximal.annulusSymbolSmooth_annAtomC
import Submission.Work.BourgainPlan.Maximal.annulusSquareLp_finset
import Submission.Work.BourgainPlan.Maximal.annulusSquare_l2
import Submission.Work.BourgainPlan.Maximal.annulusConv_finsetSum_eq
import Submission.Work.BourgainPlan.Maximal.annulusConv_star_pairing
import Submission.Work.BourgainPlan.Maximal.ENNReal_sqrt_tsum_lintegral_sq_le
import Submission.Work.BourgainPlan.Maximal.eLpNormPairingCriterion
import Submission.Work.BourgainPlan.Maximal.annulusConvStarPairingLp
import Submission.Commons.Analysis.Convolution.eLpNorm_convolution_le_complex

open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

set_option maxHeartbeats 800000

private lemma integral_star_complex (f : ℝ → ℂ) :
    (∫ x : ℝ, star (f x)) = star (∫ x : ℝ, f x) := by
  rw [Complex.star_def]
  exact integral_conj

private lemma enorm_star_complex (z : ℂ) : ‖star z‖ₑ = ‖z‖ₑ := by
  rw [← ofReal_norm (star z), ← ofReal_norm z]
  congr 1
  exact Complex.norm_conj z

private lemma eLpNorm_ennreal_eq {r : ℝ} (hr : 0 < r) (f : ℝ → ℝ≥0∞)
    (hf : AEMeasurable f (volume : Measure ℝ)) :
    eLpNorm f (ENNReal.ofReal r) (volume : Measure ℝ) = (∫⁻ x, f x ^ r) ^ (1 / r) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top
      hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hr.le]
  simp only [enorm_eq_self]

private lemma eLpNorm_ennreal_rpow {r : ℝ} (hr : 0 < r) (f : ℝ → ℝ≥0∞)
    (hf : AEMeasurable f (volume : Measure ℝ)) :
    (eLpNorm f (ENNReal.ofReal r) (volume : Measure ℝ)) ^ r = ∫⁻ x, f x ^ r := by
  rw [eLpNorm_ennreal_eq hr f hf, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (ne_of_gt hr),
    ENNReal.rpow_one]

private lemma sq_rpow {a : ℝ≥0∞} {p : ℝ} :
    (a ^ ((1:ℝ)/2)) ^ p = a ^ (p/2) := by
  rw [← ENNReal.rpow_mul]
  congr 1
  ring


/-- Turn a bound on the `eLpNorm` into the corresponding bound on the `p`-th power integral. -/
private lemma pow_step {p : ℝ} (hp : 0 < p) {S : ℝ → ℂ} {sq : ℝ → ℝ≥0∞} {C₁ : ℝ} (hC : 0 < C₁)
    (hmain : eLpNorm S (ENNReal.ofReal p) (volume : Measure ℝ)
      ≤ ENNReal.ofReal C₁ * eLpNorm sq (ENNReal.ofReal p) (volume : Measure ℝ))
    (hsq : AEMeasurable sq (volume : Measure ℝ)) :
    ∫⁻ x : ℝ, ‖S x‖ₑ ^ p ≤ ENNReal.ofReal (C₁ ^ p) * ∫⁻ x : ℝ, sq x ^ p := by
  by_cases hS : AEStronglyMeasurable S (volume : Measure ℝ)
  swap
  · -- then `eLpNorm S = ∞`, forcing `∫⁻ sq ^ p = ∞`
    rw [eLpNorm_of_not_aestronglyMeasurable hS, top_le_iff,
      eLpNorm_ennreal_eq hp sq hsq] at hmain
    have hI : (∫⁻ x : ℝ, sq x ^ p) = ⊤ := by
      by_contra hne
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by positivity) hne) hmain
    rw [hI, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hC p))]
    exact le_top
  calc ∫⁻ x : ℝ, ‖S x‖ₑ ^ p
      = (eLpNorm S (ENNReal.ofReal p) (volume : Measure ℝ)) ^ p := by
        rw [← eLpNorm_enorm S hS]
        exact (eLpNorm_ennreal_rpow hp (fun x => ‖S x‖ₑ) hS.enorm).symm
    _ ≤ (ENNReal.ofReal C₁ * eLpNorm sq (ENNReal.ofReal p) (volume : Measure ℝ)) ^ p :=
        ENNReal.rpow_le_rpow hmain hp.le
    _ = ENNReal.ofReal (C₁ ^ p) * (eLpNorm sq (ENNReal.ofReal p) (volume : Measure ℝ)) ^ p := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ENNReal.ofReal_rpow_of_nonneg hC.le hp.le]
    _ = ENNReal.ofReal (C₁ ^ p) * ∫⁻ x : ℝ, sq x ^ p := by
        rw [eLpNorm_ennreal_rpow hp sq hsq]

/-- **The dual (reverse) Littlewood--Paley estimate for the annulus projections.**  For every
`1 < p < ∞` there is `C > 0` such that for every base scale `j ∈ ℤ`, every finite index set
`F ⊆ ℤ` and every family `g n ∈ L^p(ℝ)` (`n ∈ F`),

`∫⁻ x, ‖∑_{n ∈ F} (K_{j+n} * g n)(x)‖^p dx ≤ C^p ∫⁻ x, (∑_{n ∈ F} ‖g n (x)‖²)^{p/2} dx`,

where `K_m = 𝓕⁻(annAtomC m)` is the annulus kernel of the partition atom
(`annulusConv annAtomC m`).

This is the *adjoint* of the forward Littlewood--Paley square-function estimate
(`annulusSquareLp_finset` for the family `annAtomC`: `‖(∑_n ‖K_{j+n} * f‖²)^{1/2}‖_p ≲ ‖f‖_p`
uniformly in `j` and `F`), and it is exactly MST §6.1's step
`‖∑_n S_{j+n} h_n‖_p ≲ ‖(∑_n ‖h_n‖²)^{1/2}‖_p`; note that it holds for **arbitrary** `L^p` families
`g n` and therefore needs no frequency-support hypothesis on the `h_n`.

Route (with `q := p/(p-1)`).
*Preliminaries.*  The file must **not** import
`Submission/Work/BourgainPlan/Maximal/eLpNorm_le_of_pairing_bound_memLp.lean`: that module pulls in
`Submission/Commons/Analysis/MeasureTheory/eLpNorm_iSup_of_monotone_aemeasurable.lean`, which
redeclares `Commons.Analysis.MeasureTheory.iSup_rpow_eq` and therefore clashes with the annulus
square-function chain.  Instead prove the duality criterion locally, following the proof of that
module (the extremal truncated test function `g := 1_A • (‖h‖^{p-2} • h)`, `A := {‖h‖ ≤ N} ∩ Icc (-M) M`)
but replacing its final monotone-convergence step by Mathlib's `lintegral_iSup'` (which needs only
`AEMeasurable`).  Also derive the `L²`-only form of `annulusConv_star_pairing` (the proved version
assumes `L¹ ∩ L²` in both arguments) by truncating the first argument in value and in space and
passing to the limit in `L²` (Young: `‖K * g‖₂ ≤ ‖K‖₁ ‖g‖₂`).
*Step 1, `L²` inputs.*  Assume `MemLp (g n) 2` as well.  With
`S := ∑_{n∈F} annulusConv annAtomC (j+n) (g n)` and `sq := (∑_{n∈F} ‖g n‖²)^{1/2}`, show the pairing
bound with `E := ofReal C * eLpNorm sq (ofReal p)`: for `w` with `MemLp w 2` and `MemLp w (ofReal q)`,
expand `∫ x, S x * star (w x)` as the finite sum of
`∫ x, (annulusConv annAtomC (j+n) (g n)) x * star (w x)` (Hölder), apply the self-adjointness
identity to each term, bound the resulting `∫ (∑_n ‖g n‖ ‖K_{j+n} * w‖)` by pointwise Cauchy--Schwarz
and Hölder, and finish with the forward estimate at `q` (`annulusSquareLp_finset` with the same `j`,
`F`).  Then the duality criterion gives `eLpNorm S (ofReal p) ≤ E`, and raising to the `p`-th power
gives the claim.  (`MemLp S (ofReal p)` and a.e. measurability of `S` come from the single-term
forward bound at `p` and finite summation.)
*Step 2, general `L^p` inputs.*  For `N : ℕ` put `g^N n := g n * 1_{B_{n,N}}` with
`B_{n,N} := {x | ‖g n x‖ ≤ N} ∩ Icc (-N) N`, so that `g^N n ∈ L² ∩ L^p` and Step 1 applies; the
right-hand sides increase to `∫⁻ (∑_n ‖g n‖²)^{p/2}` (monotone convergence), and
`∑_n annulusConv annAtomC (j+n) (g^N n)` tends to `S` in `L^p` (each term by dominated convergence
together with the single-term forward bound at `p`), so the Fatou inequality gives the claim. -/
theorem annulusProjectionDual (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℤ) (F : Finset ℤ) (g : ℤ → ℝ → ℂ),
      (∀ n ∈ F, MeasureTheory.MemLp (g n) (ENNReal.ofReal p)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) →
      ∫⁻ x : ℝ, ‖∑ n ∈ F, Work.BourgainPlan.Maximal.annulusConv
          Work.BourgainPlan.Maximal.annAtomC (j + n) (g n) x‖ₑ ^ p
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x : ℝ, (∑ n ∈ F, ‖g n x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
  classical
  have hp0 : (0:ℝ) < p := lt_trans zero_lt_one hp
  have hp1 : (0:ℝ) < p - 1 := by linarith
  set q : ℝ := p / (p - 1) with hqdef
  have hq0 : 0 < q := by rw [hqdef]; positivity
  have hq1 : 1 < q := by rw [hqdef, lt_div_iff₀ hp1]; linarith
  have hpq : p.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    exact ⟨hp, by rw [hqdef]; field_simp; ring⟩
  have hpinv : p⁻¹ + q⁻¹ = 1 := (Real.holderConjugate_iff.mp hpq).2
  obtain ⟨C₀, hC₀pos, hfwd⟩ :=
    annulusSquareLp_finset (b := annAtomC) annulusSymbolSmooth_annAtomC contDiff_annAtomC
      (p := q) hq1
  have hCpos : 0 < C₀ ^ (1/q) := Real.rpow_pos_of_pos hC₀pos _
  refine ⟨C₀ ^ (1 / q), hCpos, fun j F g hg => ?_⟩
  -- abbreviations
  set sq : ℝ → ℝ≥0∞ := fun x => (∑ n ∈ F, ‖g n x‖ₑ ^ (2 : ℝ)) ^ ((1:ℝ)/2) with hsqdef
  set S : ℝ → ℂ := fun x => ∑ n ∈ F, annulusConv annAtomC (j + n) (g n) x with hSdef
  set E : ENNReal := ENNReal.ofReal (C₀ ^ (1/q)) * eLpNorm sq (ENNReal.ofReal p) volume with hEdef
  have hsqm : AEMeasurable sq (volume : Measure ℝ) := by
    simp only [hsqdef]
    refine ENNReal.continuous_rpow_const.measurable.comp_aemeasurable ?_
    exact Finset.aemeasurable_fun_sum F (fun n hn =>
      ((hg n hn).aemeasurable.enorm).pow_const (2:ℝ))
  have hgoal : ∫⁻ x : ℝ, ‖S x‖ₑ ^ p
      ≤ ENNReal.ofReal ((C₀ ^ (1/q)) ^ p) * ∫⁻ x : ℝ, sq x ^ p := by
    by_cases hEtop : E = ⊤
    · have hsqtop : ∫⁻ x : ℝ, sq x ^ p = ⊤ := by
        rw [← eLpNorm_ennreal_rpow hp0 sq hsqm]
        have hEt : eLpNorm sq (ENNReal.ofReal p) volume = ⊤ := by
          rcases ENNReal.mul_eq_top.mp (by rw [← hEdef]; exact hEtop) with ⟨-, h2⟩ | ⟨h1, -⟩
          · exact h2
          · exact absurd h1 ENNReal.ofReal_ne_top
        rw [hEt, ENNReal.top_rpow_of_pos hp0]
      rw [hsqtop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hCpos p))]
      exact le_top
    · have hmain : eLpNorm S (ENNReal.ofReal p) volume ≤ E := by
        refine eLpNormPairingCriterion S hp ?_ E hEtop ?_
        · rw [hSdef]
          exact (Finset.aemeasurable_fun_sum F (fun n hn =>
            aemeasurable_annulusConv annAtomC (j + n) (hg n hn).aemeasurable
              (aemeasurable_annulusK annAtomC (j + n)))).aestronglyMeasurable
        · intro w hw2 hwq
          haveI hHT : (ENNReal.ofReal p).HolderTriple (ENNReal.ofReal q) 1 := by
            rw [ENNReal.holderTriple_iff, inv_one, ← ENNReal.ofReal_inv_of_pos (by linarith : (0:ℝ) < p),
              ← ENNReal.ofReal_inv_of_pos hq0,
              ← ENNReal.ofReal_add (inv_nonneg.mpr (by linarith : (0:ℝ) ≤ p))
                (inv_nonneg.mpr hq0.le), hpinv, ENNReal.ofReal_one]
          have hwae : AEMeasurable w (volume : Measure ℝ) := hwq.aemeasurable
          -- the convolution of every scale is in L^p
          have hmem_conv : ∀ n ∈ F, MemLp (annulusConv annAtomC (j + n) (g n))
              (ENNReal.ofReal p) (volume : Measure ℝ) := by
            intro n hn
            have hK : MemLp (annulusK annAtomC (j + n)) 1 (volume : Measure ℝ) :=
              memLp_one_iff_integrable.mpr
                (integrable_annulusK annAtomC annulusSymbolSmooth_annAtomC contDiff_annAtomC (j + n))
            exact lt_of_le_of_lt
              (Commons.Analysis.Convolution.eLpNorm_convolution_le_complex (annulusK annAtomC (j + n))
                (g n) p (le_of_lt hp) hK (hg n hn))
              (ENNReal.mul_lt_top hK.eLpNorm_lt_top (hg n hn).eLpNorm_lt_top)
          -- the splitting of the pairing into the finite sum
          have hsplit : (∫ x : ℝ, S x * star (w x))
              = ∑ n ∈ F, ∫ x : ℝ,
                  annulusConv annAtomC (j + n) (g n) x * star (w x) := by
            simp only [hSdef]
            rw [show (fun x : ℝ => (∑ n ∈ F, annulusConv annAtomC (j + n) (g n) x) * star (w x))
                  = fun x : ℝ => ∑ n ∈ F, annulusConv annAtomC (j + n) (g n) x * star (w x) by
                funext x; rw [Finset.sum_mul]]
            rw [integral_finsetSum]
            intro n hn
            exact (hmem_conv n hn).integrable_mul hwq.star
          have hterm : ∀ n ∈ F, (∫ x : ℝ, annulusConv annAtomC (j + n) (g n) x * star (w x))
              = ∫ x : ℝ, g n x * star (annulusConv annAtomC (j + n) w x) := fun n hn =>
            annulusConvStarPairingLp (j + n) hp hpq (g n) w (hg n hn) hwq
          set sqw : ℝ → ℝ≥0∞ :=
            fun x => (∑ n ∈ F, ‖annulusConv annAtomC (j + n) w x‖ₑ ^ (2 : ℝ)) ^ ((1:ℝ)/2) with hsqwdef
          have hAEMsq : AEMeasurable sq (volume : Measure ℝ) := by
            simp only [hsqdef]
            refine ENNReal.continuous_rpow_const.measurable.comp_aemeasurable ?_
            exact Finset.aemeasurable_fun_sum F (fun n hn =>
              ((hg n hn).aemeasurable.enorm).pow_const (2:ℝ))
          have hAEMsqw : AEMeasurable sqw (volume : Measure ℝ) := by
            simp only [hsqwdef]
            refine ENNReal.continuous_rpow_const.measurable.comp_aemeasurable ?_
            exact Finset.aemeasurable_fun_sum F (fun n hn =>
              ((aemeasurable_annulusConv annAtomC (j + n) hwae
                (aemeasurable_annulusK annAtomC (j + n))).enorm).pow_const (2:ℝ))
          have hsqwle : eLpNorm sqw (ENNReal.ofReal q) volume
              ≤ ENNReal.ofReal (C₀ ^ (1/q)) * eLpNorm w (ENNReal.ofReal q) volume := by
            rw [eLpNorm_ennreal_eq hq0 sqw hAEMsqw]
            have h1 : ∫⁻ x, sqw x ^ q
                ≤ ENNReal.ofReal C₀ * ∫⁻ x, ‖w x‖ₑ ^ q := by
              rw [show (fun x : ℝ => sqw x ^ q) = fun x : ℝ =>
                  (∑ n ∈ F, ‖annulusConv annAtomC (j + n) w x‖ₑ ^ (2 : ℝ)) ^ (q / 2) by
                funext x
                simp only [hsqwdef, sq_rpow]]
              exact hfwd j F w hwq
            calc (∫⁻ x, sqw x ^ q) ^ (1 / q)
                ≤ (ENNReal.ofReal C₀ * ∫⁻ x, ‖w x‖ₑ ^ q) ^ (1 / q) :=
                  ENNReal.rpow_le_rpow h1 (by positivity)
              _ = (ENNReal.ofReal C₀) ^ (1 / q) * (∫⁻ x, ‖w x‖ₑ ^ q) ^ (1 / q) :=
                  ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
              _ = ENNReal.ofReal (C₀ ^ (1/q)) * eLpNorm w (ENNReal.ofReal q) volume := by
                  rw [ENNReal.ofReal_rpow_of_nonneg hC₀pos.le (by positivity),
                    eLpNorm_eq_lintegral_rpow_enorm_toReal
                      (ENNReal.ofReal_ne_zero_iff.mpr hq0) ENNReal.ofReal_ne_top hwq.aestronglyMeasurable,
                    ENNReal.toReal_ofReal hq0.le]
          have hchain : ‖∫ x : ℝ, S x * star (w x)‖ₑ
              ≤ ENNReal.ofReal (C₀ ^ (1/q)) * eLpNorm sq (ENNReal.ofReal p) volume
                * eLpNorm w (ENNReal.ofReal q) volume := by
            calc ‖∫ x : ℝ, S x * star (w x)‖ₑ
                = ‖∑ n ∈ F, ∫ x : ℝ, g n x * star (annulusConv annAtomC (j + n) w x)‖ₑ := by
                  rw [hsplit]
                  congr 1
                  exact Finset.sum_congr rfl hterm
              _ ≤ ∑ n ∈ F, ‖∫ x : ℝ, g n x * star (annulusConv annAtomC (j + n) w x)‖ₑ :=
                  enorm_sum_le F _
              _ ≤ ∑ n ∈ F, ∫⁻ x, ‖g n x‖ₑ * ‖annulusConv annAtomC (j + n) w x‖ₑ := by
                  refine Finset.sum_le_sum (fun n hn => ?_)
                  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
                  refine lintegral_congr (fun x => ?_)
                  rw [enorm_mul, enorm_star_complex]
              _ = ∫⁻ x, ∑ n ∈ F, ‖g n x‖ₑ * ‖annulusConv annAtomC (j + n) w x‖ₑ := by
                  rw [lintegral_finsetSum']
                  intro n hn
                  exact ((hg n hn).aemeasurable.enorm).mul
                    ((aemeasurable_annulusConv annAtomC (j + n) hwae
                      (aemeasurable_annulusK annAtomC (j + n))).enorm)
              _ ≤ ∫⁻ x, sq x * sqw x := by
                  refine lintegral_mono (fun x => ?_)
                  simp only [hsqdef, hsqwdef]
                  exact ennreal_finset_sum_mul_le_sqrt_mul_sqrt F _ _
              _ ≤ (∫⁻ x, sq x ^ p) ^ (1/p) * (∫⁻ x, sqw x ^ q) ^ (1/q) :=
                  ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hAEMsq hAEMsqw
              _ = eLpNorm sq (ENNReal.ofReal p) volume * eLpNorm sqw (ENNReal.ofReal q) volume := by
                  rw [eLpNorm_ennreal_eq hp0 sq hAEMsq, eLpNorm_ennreal_eq hq0 sqw hAEMsqw]
              _ ≤ eLpNorm sq (ENNReal.ofReal p) volume
                    * (ENNReal.ofReal (C₀ ^ (1/q)) * eLpNorm w (ENNReal.ofReal q) volume) :=
                  mul_le_mul' le_rfl hsqwle
              _ = ENNReal.ofReal (C₀ ^ (1/q)) * eLpNorm sq (ENNReal.ofReal p) volume
                    * eLpNorm w (ENNReal.ofReal q) volume := by ring
          have hinner_eq : (∫ x : ℝ, inner ℂ (S x) (w x))
              = star (∫ x : ℝ, S x * star (w x)) := by
            rw [← integral_star_complex (fun x : ℝ => S x * star (w x))]
            refine integral_congr_ae (Eventually.of_forall (fun x => ?_))
            show inner ℂ (S x) (w x) = star (S x * star (w x))
            rw [RCLike.inner_apply, star_mul, star_star, Complex.star_def]
          rw [hinner_eq, enorm_star_complex, hEdef]
          exact hchain
      rw [hEdef] at hmain
      exact pow_step hp0 hCpos hmain hsqm
  calc ∫⁻ x : ℝ, ‖∑ n ∈ F, annulusConv annAtomC (j + n) (g n) x‖ₑ ^ p
      = ∫⁻ x : ℝ, ‖S x‖ₑ ^ p := rfl
    _ ≤ ENNReal.ofReal ((C₀ ^ (1/q)) ^ p) * ∫⁻ x : ℝ, sq x ^ p := hgoal
    _ = ENNReal.ofReal ((C₀ ^ (1/q)) ^ p) * ∫⁻ x : ℝ, (∑ n ∈ F, ‖g n x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
        congr 1
        refine lintegral_congr (fun x => ?_)
        simp only [hsqdef, sq_rpow]

end Work.BourgainPlan.Maximal
