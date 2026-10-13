import Mathlib
import Submission.Work.DSM5c.Devissage.almostAcyc_span_of_bot
import Submission.Work.DSM5c.G2.isSMulRegular_chartUntilt
import Submission.Work.DSM5c.CharPChart
import Submission.Work.DSM5b.CechIsoDefs
import Submission.Work.DSM5c.Cech.perfChartCoaug_d01

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.DSM5c.Lp

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open CategoryTheory.Limits

/-! ## Two elementary generalities about `IsSMulRegular` -/

/-- **Regularity is inherited from the factors of a product type.**  For the coordinatewise action
on `(i : β) → M i`, an element acting injectively on every factor acts injectively on the product
(no finiteness of the index type is needed). -/
theorem isSMulRegular_pi_family {R : Type*} {β : Type*} {M : β → Type*} [∀ i, SMul R (M i)]
    {r : R} (h : ∀ i, IsSMulRegular (M i) r) : IsSMulRegular ((i : β) → M i) r :=
  fun a b hab => by
    funext i
    exact h i (by simpa only [Pi.smul_apply] using congrFun hab i)

/-- **Regularity is transported by a linear equivalence.** -/
theorem isSMulRegular_of_linearEquiv {R : Type*} [Semiring R] {M N : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (e : M ≃ₗ[R] N) {r : R} (h : IsSMulRegular N r) : IsSMulRegular M r := by
  have h' : ∀ x y : N, r • x = r • y → x = y := h
  intro a b hab
  refine e.injective (h' _ _ ?_)
  rw [← e.map_smul, ← e.map_smul]
  exact congrArg e hab

/-! ## The two side conditions of the dévissage -/

/-- **The perfected tilted chart is regular for `(ϖ♭)^p`**: `Work.DSM5c.G2.chartPhi_tiltVarpi_isSMulRegular`
gives regularity of the image of `ϖ♭` (times `p`, i.e. of its `p`-th power), and the `R`-module
structure of the chart is the one induced by `algebraMap (PreTilt W p) _ = chartPhi …`. -/
theorem isSMulRegular_perfChartRing_tiltVarpi_pow {p : ℕ} [Fact p.Prime] {W : Type}
    [CommRing W] [Fact ¬IsUnit (p : W)] [IsAdicComplete (Ideal.span {(p : W)}) W]
    {ι : Type} [DecidableEq ι] (Q : DSMap.PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (S : Finset ι) :
    IsSMulRegular ↥(perfChartRing p (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) S)
      ((Work.DSM5c.tiltVarpi Q) ^ p) := by
  have h := (Work.DSM5c.G2.chartPhi_tiltVarpi_isSMulRegular Q t tr htr0 htr j₀ e S).pow p
  have hpt : ∀ x : ↥(Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e S),
      ((Work.DSM5c.tiltVarpi Q) ^ p) • x
        = ((Work.DSM5c.chartPhi Q t tr htr0 htr j₀ e S (Work.DSM5c.tiltVarpi Q)) ^ p) • x := by
    intro x
    rw [Algebra.smul_def, smul_eq_mul, ← map_pow]
    rfl
  rw [IsSMulRegular] at h ⊢
  change Function.Injective (fun x : ↥(Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e S) =>
    ((Work.DSM5c.tiltVarpi Q) ^ p) • x)
  intro a b hab
  exact h (by
    change ((Work.DSM5c.chartPhi Q t tr htr0 htr j₀ e S (Work.DSM5c.tiltVarpi Q)) ^ p) • a
      = ((Work.DSM5c.chartPhi Q t tr htr0 htr j₀ e S (Work.DSM5c.tiltVarpi Q)) ^ p) • b
    rw [← hpt a, ← hpt b]
    exact hab)

/-- **`hreg` of the dévissage**: the terms of the Čech complex of the perfected tilted charts are
regular for `(ϖ♭)^p`.  By `Work.DSM5b.coordIso` the degree-`q` term is linearly isomorphic to the
product `Work.DSM5b.PCX p t' q` of the perfected chart rings `perfChartRing p t' (tupRng τ)`, so
regularity follows factorwise from `isSMulRegular_perfChartRing_tiltVarpi_pow`. -/
theorem isSMulRegular_tiltGenCechTerm {p : ℕ} [Fact p.Prime] {W : Type} [CommRing W]
    [Fact ¬IsUnit (p : W)] [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type} [Finite ι]
    [DecidableEq ι] (Q : DSMap.PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (q : ℕ) :
    IsSMulRegular
      (((CategoryTheory.cechComplexFunctor (DSMap.Mix2.chartIdx ι)).obj
        (DSMap.Mix2.perfChartPresheaf p
          (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e))).X q)
      ((Work.DSM5c.tiltVarpi Q) ^ p) := by
  have hfac := isSMulRegular_perfChartRing_tiltVarpi_pow Q t tr htr0 htr j₀ e
  have hpi : IsSMulRegular (Work.DSM5b.PCX p (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) q)
      ((Work.DSM5c.tiltVarpi Q) ^ p) :=
    isSMulRegular_pi_family
      (M := fun τ : Fin (q + 1) → ι => ↥(perfChartRing p
        (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) (Work.DSM5b.tupRng τ)))
      (fun τ => hfac (Work.DSM5b.tupRng τ))
  change IsSMulRegular ↥(Work.DSM5b.KX p (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) q)
    ((Work.DSM5c.tiltVarpi Q) ^ p)
  exact isSMulRegular_of_linearEquiv
    (Work.DSM5b.coordIso p (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) q).toLinearEquiv hpi

/-- **The characteristic-`p` input at the tilted chart datum, modulo `((ϖ♭)^p)`.**  `hM5b` is `area_M5b` read at the tilted generators `Work.DSM5c.chartTiltGen` with `T := tiltVarpi Q`; the conclusion upgrades the ideal `⊥` to `((ϖ♭)^p)` by the dévissage `Work.DSM5c.Devissage.almostAcyc_span_of_bot` with `u := (tiltVarpi Q)^p`.

(The two side conditions of the dévissage are the `0`-cocycle property of the diagonal coaugmentation `perfChartCoaug` and `IsSMulRegular` of the terms of the Čech complex — a finite product of the `Work.DSM5c.tiltChart`s, each regular for `chartPhi … (tiltVarpi Q)` by `Work.DSM5c.G2.chartPhi_tiltVarpi_isSMulRegular`.) -/
theorem almostAcyc_tiltGen {p : ℕ} [Fact p.Prime] {W : Type} [CommRing W] [Fact ¬IsUnit (p : W)] [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type} [Finite ι] [DecidableEq ι] (Q : DSMap.PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (hM5b : Work.DSM5c.M5bInput p (PreTilt W p) (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) (Work.DSM5c.tiltVarpi Q)) : DSMap.Mix2.AlmostAcyc (fun k => (frobeniusEquiv (PreTilt W p) p).symm^[k] (Work.DSM5c.tiltVarpi Q)) (Ideal.span {(Work.DSM5c.tiltVarpi Q) ^ p}) ((CategoryTheory.cechComplexFunctor (DSMap.Mix2.chartIdx ι)).obj (DSMap.Mix2.perfChartPresheaf p (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e))) (DSMap.Mix2.perfChartCoaug p (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e)) := by
  have hroot : ∀ k, ((frobeniusEquiv (PreTilt W p) p).symm^[k + 1] (Work.DSM5c.tiltVarpi Q)) ^ p
      = (frobeniusEquiv (PreTilt W p) p).symm^[k] (Work.DSM5c.tiltVarpi Q) := by
    intro k
    have key : ∀ y : PreTilt W p, ((frobeniusEquiv (PreTilt W p) p).symm y) ^ p = y := by
      intro y
      rw [← frobenius_def, ← coe_frobeniusEquiv]
      exact (frobeniusEquiv (PreTilt W p) p).apply_symm_apply y
    rw [Function.iterate_succ_apply']
    exact key _
  exact Work.DSM5c.Devissage.almostAcyc_span_of_bot
    (fun k => (frobeniusEquiv (PreTilt W p) p).symm^[k] (Work.DSM5c.tiltVarpi Q)) hroot
    ((Work.DSM5c.tiltVarpi Q) ^ p) _ _
    (fun w => Work.DSM5c.Cech.perfChartCoaug_d01 (p := p) (R := PreTilt W p) (ι := ι)
      (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) w)
    (fun q => isSMulRegular_tiltGenCechTerm Q t tr htr0 htr j₀ e q)
    hM5b

end Work.DSM5c.Lp
