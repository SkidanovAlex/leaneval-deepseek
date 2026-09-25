import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusSqfunDefs
import Submission.Work.BourgainPlan.Maximal.annulusSymbolSum_mikhlin
import Submission.Work.BourgainPlan.Maximal.annulusSquareLpDefs
import Submission.Work.BourgainPlan.Maximal.annulusSqfun_finsetMikhlin
import Submission.Work.BourgainPlan.Maximal.annulusConv_finsetSum_eq
import Submission.Work.BourgainPlan.Maximal.rademacher_lower_finset
import Submission.Work.BourgainPlan.IonescuWainger.rademacher_two_stage_lower

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BourgainPlan.Maximal

set_option linter.style.haveILetI false

/-- **The lower Rademacher (Khintchine) inequality, uniformly in the index type.**

For every `p ≥ 1` there is `c > 0` with

  `c · (∑_i ‖u i‖²)^{p/2} ≤ (∑_{ε : ι → Bool} ‖∑_i ε_i u i‖^p) / |ι → Bool|`

for **every** finite index type `ι` and every family `u : ι → ℂ` — the lower half of Khintchine's
inequality with the constant `c` not depending on `ι`.  This is the form needed for the annulus
square function, where the index set is an arbitrary finite `F ⊆ ℤ` and the constant has to be
uniform in `F`.

Like `rademacher_lower_finset`, this is an immediate corollary of the two-stage lower bound
`Work.BourgainPlan.IonescuWainger.rademacher_two_stage_lower` with the second index type
specialised to `Unit`: the inner sum over `η : Unit → Bool` has two terms of coefficient `±1`, so
it contributes `2 · ‖Σ_i ε_i u_i‖^p` and the cardinality factor `|Unit → Bool| = 2` cancels.  The
*difference* from `rademacher_lower_finset` is the quantifier order: there `{ι}` is bound
*outside* the `∃ c`, here it is *inside*. -/
theorem rademacher_lower_uniform (p : ℝ) (hp : 1 ≤ p) :
    ∃ c : ℝ, 0 < c ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → ℂ),
      ENNReal.ofReal c * (∑ i : ι, ‖u i‖ₑ ^ (2:ℝ)) ^ (p / 2)
        ≤ (∑ ε : ι → Bool, ‖∑ i : ι, (if ε i then (1 : ℂ) else -1) * u i‖ₑ ^ p) *
            (Fintype.card (ι → Bool) : ENNReal)⁻¹ := by
  obtain ⟨c, hc, h⟩ := Work.BourgainPlan.IonescuWainger.rademacher_two_stage_lower p hp
  refine ⟨c, hc, fun {ι} _ _ u => ?_⟩
  classical
  -- Specialise the second index type of the two-stage bound to `Unit` and set `a i _ = u i`.
  have key := h (κ := Unit) (fun i (_ : Unit) => u i)
  -- The left-hand side: the inner (single-term) sum over `Unit` contributes nothing new.
  have hL : (∑ i : ι, ∑ t : Unit, ‖(fun i (_ : Unit) => u i) i t‖ₑ ^ (2:ℝ))
      = ∑ i : ι, ‖u i‖ₑ ^ (2:ℝ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_unique]
  -- The right-hand side: for each `ε` the sum over `η : Unit → Bool` has the two terms
  -- `‖Σ_i ε_i u_i‖ₑ ^ p`, so it equals `2 * ‖Σ_i ε_i u_i‖ₑ ^ p`.
  have hR : (∑ ε : ι → Bool, ∑ η : Unit → Bool, ‖∑ i : ι, ∑ t : Unit,
        (if ε i then (1:ℂ) else -1) * (if η t then (1:ℂ) else -1)
          * (fun i (_ : Unit) => u i) i t‖ₑ ^ p)
      = 2 * (∑ ε : ι → Bool, ‖∑ i : ι, (if ε i then (1:ℂ) else -1) * u i‖ₑ ^ p) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ε _ => ?_
    have hF : ∀ η : Unit → Bool,
        ‖∑ i : ι, ∑ t : Unit, (if ε i then (1:ℂ) else -1) * (if η t then (1:ℂ) else -1)
            * (fun i (_ : Unit) => u i) i t‖ₑ ^ p
          = ‖∑ i : ι, (if ε i then (1:ℂ) else -1) * u i‖ₑ ^ p := by
      intro η
      -- Factor the `±1` coefficient `η ()` out of the whole sum.
      have hsum : (∑ i : ι, ∑ t : Unit, (if ε i then (1:ℂ) else -1) * (if η t then (1:ℂ) else -1)
            * (fun i (_ : Unit) => u i) i t)
          = (if η () then (1:ℂ) else -1) * ∑ i : ι, (if ε i then (1:ℂ) else -1) * u i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Fintype.sum_unique]
        ring
      have hnorm : ‖∑ i : ι, ∑ t : Unit, (if ε i then (1:ℂ) else -1) * (if η t then (1:ℂ) else -1)
            * (fun i (_ : Unit) => u i) i t‖
          = ‖∑ i : ι, (if ε i then (1:ℂ) else -1) * u i‖ := by
        rw [hsum, norm_mul,
          show ‖(if η () then (1:ℂ) else -1)‖ = 1 from by rcases η () <;> simp,
          one_mul]
      rw [← ofReal_norm, ← ofReal_norm, hnorm]
    rw [Finset.sum_congr rfl (fun η _ => hF η), Finset.sum_const, Finset.card_univ]
    rw [show Fintype.card (Unit → Bool) = 2 from by simp [Fintype.card_bool],
      two_nsmul, two_mul]
  have hD : (Fintype.card (Unit → Bool) : ENNReal) = 2 := by
    rw [show Fintype.card (Unit → Bool) = 2 from by simp [Fintype.card_bool]]
    norm_num
  rw [hL, hR, hD] at key
  refine le_trans key (le_of_eq ?_)
  -- Pure `ENNReal` arithmetic: `2 * A * (C * 2)⁻¹ = A * C⁻¹`.
  set A : ENNReal := ∑ ε : ι → Bool, ‖∑ i : ι, (if ε i then (1:ℂ) else -1) * u i‖ₑ ^ p
  set D : ENNReal := (Fintype.card (ι → Bool) : ENNReal)
  rw [ENNReal.mul_inv (Or.inr (by norm_num : (2:ENNReal) ≠ ⊤))
      (Or.inr (by norm_num : (2:ENNReal) ≠ 0))]
  calc (2 * A) * (D⁻¹ * 2⁻¹)
      = (2 * 2⁻¹) * (A * D⁻¹) := by ring
    _ = 1 * (A * D⁻¹) := by
        rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
    _ = A * D⁻¹ := one_mul _

/-- **The `L^p` bound of the annulus square function on finite index sets.**

For an annulus symbol family `b` (`AnnulusSymbolSmooth b`, each `b m` of class `C^∞`) and every
`1 < p < ∞` there is `C > 0` with, for every base scale `j ∈ ℤ`, every finite `F ⊆ ℤ` and every
`f ∈ L^p(ℝ)`,

  `∫⁻ x, (∑_{n ∈ F} ‖(K_{j+n} * f)(x)‖²)^{p/2} ≤ C ∫⁻ x, ‖f x‖^p`,

with `K_m = 𝓕⁻ (b m)` and `(K_{j+n} * f)(x) = annulusConv b (j+n) f x`.  The constant is uniform in
`j` and in the finite set `F` — this is MST's `(eq:52)` input 2 (the Littlewood–Paley square-function
bound) restricted to finitely many scales, which the module `annulusSquareLp` then extends to the
full two-sided sum `∑'_n` by monotone convergence (`annulusSquareLp_of_finset`).

Suggested proof (every ingredient is already proved in the workspace):

* **Khintchine / randomisation, pointwise in `x`.** Use the lower Rademacher/Khintchine inequality
  with the finite index type `ι := ↥F` and `u (i : ↥F) := annulusConv b (j + ↑i) f x`.
  ⚠ **Uniformity caveat (raised by the reviewer).** The already-proved
  `Work.BourgainPlan.Maximal.rademacher_lower_finset` binds `{ι} [Fintype ι]` *outside* its `∃ c`,
  so its constant may depend on `ι` and must NOT be used here (our constant has to be uniform in
  `F`).  Use instead the uniform source
  `Work.BourgainPlan.IonescuWainger.rademacher_two_stage_lower p (le_of_lt hp)` — which quantifies
  `ι` *inside* the `∃ c` — specialising its second index type to `Unit` (or `PUnit`) and following
  verbatim the PUnit-specialisation already carried out in
  `Submission/Work/BourgainPlan/Maximal/rademacher_lower_finset.lean` (a ~60-line body that can be
  copied with the quantifier order `∃ c, ∀ {ι} [Fintype ι] [DecidableEq ι] (u : ι → ℂ), …`).
  Put that uniform variant in this module as a helper if convenient.  Rewrite `∑ i : ↥F` as
  `∑ n ∈ F` with `Finset.sum_attach`/`Finset.univ_eq_attach`.
* **Integrate** the pointwise inequality in `x` (`MeasureTheory.lintegral_mono`,
  `MeasureTheory.lintegral_const_mul'` to pull `ENNReal.ofReal c` out of the integral, and
  `MeasureTheory.lintegral_finsetSum'` to pull the finite sum over the sign vectors
  `ε : ↥F → Bool` out of the integral; a.e.-measurability of `annulusConv b (j+i) f` is
  `Work.BourgainPlan.Maximal.aemeasurable_annulusConv` — in
  `czBad_lintegral_compl_czStar_le.lean` — applied to `hf.aestronglyMeasurable.aemeasurable`).
* **Bound each sign vector** with `annulusSymbolSum_convolution_le (b) hb hsmooth hp`: for
  `ε : ↥F → Bool`, the identification result `annulusConv_finsetSum_eq b hb hsmooth hp.le j F
  (fun n => if h : n ∈ F then (if ε ⟨n, h⟩ then 1 else -1) else 1) f hf x` rewrites the signed sum
  `∑_{n∈F} (if ε ⟨n,_⟩ then 1 else -1) * annulusConv b (j+n) f x` into
  `∫ y, 𝓕⁻ (annulusSymbolSum b j F coeff) (x - y) * f y`, and `annulusSymbolSum_convolution_le`
  bounds its `∫⁻ ‖·‖ₑ^p` by `ofReal Cm * ∫⁻ ‖f‖ₑ^p` (the coefficient family has `‖·‖ ≤ 1`).
* **Collect:** the `(Fintype.card (↥F → Bool))⁻¹` factor cancels against the sum over the
  `card (↥F → Bool)` sign vectors, and the final constant is `c⁻¹ * Cm`.

`Work.BourgainPlan.Maximal.annulusSquareLp_of_finset` (in `annulusSquareLpDefs.lean`) is the
(already proved) consumer of this statement. -/
theorem annulusSquareLp_finset (b : ℤ → ℝ → ℂ)
    (hb : Work.BourgainPlan.Maximal.AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℤ) (F : Finset ℤ) (f : ℝ → ℂ),
      MeasureTheory.MemLp f (ENNReal.ofReal p) (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
      ∫⁻ x : ℝ,
          (∑ n ∈ F,
              ‖Work.BourgainPlan.Maximal.annulusConv b (j + n) f x‖ₑ ^ (2 : ℝ)) ^ (p / 2)
        ≤ ENNReal.ofReal C * ∫⁻ x : ℝ, ‖f x‖ₑ ^ p := by
  obtain ⟨c, hc, hrad⟩ := rademacher_lower_uniform p (le_of_lt hp)
  obtain ⟨Cm, hCm, hmik⟩ := annulusSymbolSum_convolution_le b hb hsmooth hp
  refine ⟨c⁻¹ * Cm, mul_pos (inv_pos.mpr hc) hCm, fun j F f hf => ?_⟩
  classical
  set J : ℝ≥0∞ := ∫⁻ x : ℝ, ‖f x‖ₑ ^ p with hJ
  -- the coefficient family on all of `ℤ` determined by a sign vector on `↥F`
  set coeff : (↥F → Bool) → ℤ → ℂ :=
    fun ε n => if h : n ∈ F then (if ε ⟨n, h⟩ then (1 : ℂ) else -1) else 1 with hcoeff
  have hcoeff_le : ∀ (ε : ↥F → Bool) (n : ℤ), ‖coeff ε n‖ ≤ 1 := by
    intro ε n
    simp only [hcoeff]
    split_ifs <;> simp
  -- the pointwise Khintchine (Rademacher) lower bound, uniform in `F`
  have hpt : ∀ x : ℝ,
      ENNReal.ofReal c * (∑ i : ↥F, ‖annulusConv b (j + (i : ℤ)) f x‖ₑ ^ (2 : ℝ)) ^ (p / 2)
        ≤ (∑ ε : ↥F → Bool, ‖∑ i : ↥F, (if ε i then (1 : ℂ) else -1)
              * annulusConv b (j + (i : ℤ)) f x‖ₑ ^ p)
            * (Fintype.card (↥F → Bool) : ℝ≥0∞)⁻¹ :=
    fun x => hrad (u := fun i : ↥F => annulusConv b (j + (i : ℤ)) f x)
  -- rewriting the sum over the subtype as a sum over `F`
  have hattach : ∀ (ε : ↥F → Bool) (x : ℝ),
      (∑ i : ↥F, (if ε i then (1 : ℂ) else -1) * annulusConv b (j + (i : ℤ)) f x)
        = ∑ n ∈ F, coeff ε n * annulusConv b (j + n) f x := by
    intro ε x
    rw [Finset.univ_eq_attach]
    rw [← Finset.sum_attach F (fun n : ℤ => coeff ε n * annulusConv b (j + n) f x)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [hcoeff]
  -- the signed sum is the convolution with the signed symbol sum
  have hident : ∀ (ε : ↥F → Bool) (x : ℝ),
      (∑ i : ↥F, (if ε i then (1 : ℂ) else -1) * annulusConv b (j + (i : ℤ)) f x)
        = ∫ y : ℝ,
            FourierTransformInv.fourierInv (annulusSymbolSum b j F (coeff ε)) (x - y) * f y :=
    fun ε x => (hattach ε x).trans
      (annulusConv_finsetSum_eq b hb hsmooth hp.le j F (coeff ε) f hf x)
  -- the Mikhlin bound for each sign vector
  have hbound : ∀ ε : ↥F → Bool,
      ∫⁻ x : ℝ, ‖∑ i : ↥F, (if ε i then (1 : ℂ) else -1)
          * annulusConv b (j + (i : ℤ)) f x‖ₑ ^ p
        ≤ ENNReal.ofReal Cm * J := by
    intro ε
    calc ∫⁻ x : ℝ, ‖∑ i : ↥F, (if ε i then (1 : ℂ) else -1)
            * annulusConv b (j + (i : ℤ)) f x‖ₑ ^ p
        = ∫⁻ x : ℝ, ‖∫ y : ℝ,
              FourierTransformInv.fourierInv (annulusSymbolSum b j F (coeff ε)) (x - y)
                * f y‖ₑ ^ p :=
          lintegral_congr (fun x => by rw [hident ε x])
      _ ≤ ENNReal.ofReal Cm * ∫⁻ x : ℝ, ‖f x‖ₑ ^ p :=
          hmik j F (coeff ε) (hcoeff_le ε) f hf
      _ = ENNReal.ofReal Cm * J := by rw [hJ]
  -- a.e. measurability of each signed convolution
  have hmeas : ∀ ε : ↥F → Bool, AEMeasurable (fun x : ℝ =>
      ‖∑ i : ↥F, (if ε i then (1 : ℂ) else -1) * annulusConv b (j + (i : ℤ)) f x‖ₑ ^ p)
      (volume : Measure ℝ) := by
    intro ε
    refine (AEMeasurable.enorm ?_).pow_const p
    refine Finset.aemeasurable_fun_sum (Finset.univ : Finset (↥F)) (fun i _ => ?_)
    exact (aemeasurable_annulusConv b (j + (i : ℤ)) hf.aestronglyMeasurable.aemeasurable
      (aemeasurable_annulusK b (j + (i : ℤ)))).const_mul (if ε i then (1 : ℂ) else -1)
  -- the assembled bound, with the `card (↥F → Bool)` factor cancelling
  have hkey : ENNReal.ofReal c * (∫⁻ x : ℝ,
      (∑ i : ↥F, ‖annulusConv b (j + (i : ℤ)) f x‖ₑ ^ (2 : ℝ)) ^ (p / 2))
        ≤ ENNReal.ofReal Cm * J := by
    have hD0 : (Fintype.card (↥F → Bool) : ℝ≥0∞) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      exact Fintype.card_ne_zero
    have hDtop : (Fintype.card (↥F → Bool) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [← lintegral_const_mul' (ENNReal.ofReal c) (fun x : ℝ =>
      (∑ i : ↥F, ‖annulusConv b (j + (i : ℤ)) f x‖ₑ ^ (2 : ℝ)) ^ (p / 2))
      ENNReal.ofReal_ne_top]
    calc ∫⁻ x : ℝ, ENNReal.ofReal c
          * (∑ i : ↥F, ‖annulusConv b (j + (i : ℤ)) f x‖ₑ ^ (2 : ℝ)) ^ (p / 2)
        ≤ ∫⁻ x : ℝ, (∑ ε : ↥F → Bool, ‖∑ i : ↥F, (if ε i then (1 : ℂ) else -1)
              * annulusConv b (j + (i : ℤ)) f x‖ₑ ^ p)
            * (Fintype.card (↥F → Bool) : ℝ≥0∞)⁻¹ :=
          lintegral_mono hpt
      _ = (∑ ε : ↥F → Bool, ∫⁻ x : ℝ, ‖∑ i : ↥F, (if ε i then (1 : ℂ) else -1)
              * annulusConv b (j + (i : ℤ)) f x‖ₑ ^ p)
            * (Fintype.card (↥F → Bool) : ℝ≥0∞)⁻¹ := by
          rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hD0)]
          congr 1
          rw [lintegral_finsetSum' (Finset.univ : Finset (↥F → Bool)) (fun ε _ => hmeas ε)]
      _ ≤ (∑ ε : ↥F → Bool, ENNReal.ofReal Cm * J)
            * (Fintype.card (↥F → Bool) : ℝ≥0∞)⁻¹ :=
          mul_le_mul_left (Finset.sum_le_sum (fun ε _ => hbound ε)) _
      _ = ((Fintype.card (↥F → Bool) : ℝ≥0∞) * (ENNReal.ofReal Cm * J))
            * (Fintype.card (↥F → Bool) : ℝ≥0∞)⁻¹ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ENNReal.ofReal Cm * J := by
          rw [show ((Fintype.card (↥F → Bool) : ℝ≥0∞) * (ENNReal.ofReal Cm * J))
                * (Fintype.card (↥F → Bool) : ℝ≥0∞)⁻¹
              = ((Fintype.card (↥F → Bool) : ℝ≥0∞) * (Fintype.card (↥F → Bool) : ℝ≥0∞)⁻¹)
                * (ENNReal.ofReal Cm * J) by ring,
            ENNReal.mul_inv_cancel hD0 hDtop, one_mul]
  -- undo the factor `ofReal c`
  have hI : (∫⁻ x : ℝ,
      (∑ i : ↥F, ‖annulusConv b (j + (i : ℤ)) f x‖ₑ ^ (2 : ℝ)) ^ (p / 2))
        ≤ ENNReal.ofReal (c⁻¹ * Cm) * J := by
    have hcne : ENNReal.ofReal c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hc
    have hctop : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
    calc (∫⁻ x : ℝ, (∑ i : ↥F, ‖annulusConv b (j + (i : ℤ)) f x‖ₑ ^ (2 : ℝ)) ^ (p / 2))
        = (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal c * (∫⁻ x : ℝ,
            (∑ i : ↥F, ‖annulusConv b (j + (i : ℤ)) f x‖ₑ ^ (2 : ℝ)) ^ (p / 2))) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hcne hctop, one_mul]
      _ ≤ (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal Cm * J) := mul_le_mul_right hkey _
      _ = ENNReal.ofReal (c⁻¹ * Cm) * J := by
          rw [← ENNReal.ofReal_inv_of_pos hc, ← mul_assoc,
            ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hc))]
  -- rewrite the sum over `F` back into the subtype form
  calc ∫⁻ x : ℝ, (∑ n ∈ F, ‖annulusConv b (j + n) f x‖ₑ ^ (2 : ℝ)) ^ (p / 2)
      = ∫⁻ x : ℝ, (∑ i : ↥F, ‖annulusConv b (j + (i : ℤ)) f x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
        refine lintegral_congr (fun x => ?_)
        congr 1
        exact (Finset.sum_attach F (fun n : ℤ => ‖annulusConv b (j + n) f x‖ₑ ^ (2 : ℝ))).symm
    _ ≤ ENNReal.ofReal (c⁻¹ * Cm) * J := hI
    _ = ENNReal.ofReal (c⁻¹ * Cm) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ p := by rw [hJ]

end Work.BourgainPlan.Maximal
