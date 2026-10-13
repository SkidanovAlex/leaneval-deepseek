import Mathlib
import Submission.Work.DSM5c.Devissage.almostAcyc_span_of_bot
import Submission.Work.DSM5c.Lp.almostAcyc_tiltGen
import Submission.Work.DSM5c.G2.isSMulRegular_chartUntiltU
import Submission.Work.DSM5c.CharPChart
import Submission.Work.DSM5b.CechIsoDefs
import Submission.Work.DSM5c.Cech.perfChartCoaug_d01

/-!
# DSM5c/Lp — the tilt-side chain at an arbitrary universe

Universe-polymorphic (`Type u`) restatements of

* `Work.DSM5c.Cech.perfChartCoaug_d01` — the diagonal coaugmentation of the perfected chart Čech
  complex is a `0`-cocycle (together with its auxiliary `perfChartRho_algebraMap`);
* `Work.DSM5c.Lp.isSMulRegular_perfChartRing_tiltVarpi_pow` and
  `Work.DSM5c.Lp.isSMulRegular_tiltGenCechTerm` — the terms of the Čech complex of the perfected
  *tilted* charts are regular for `(ϖ♭)^p` (using the already universe-polymorphic
  `Work.DSM5c.G2.U.chartPhi_tiltVarpi_isSMulRegular`);
* `Work.DSM5c.Lp.almostAcyc_tiltGen` — the characteristic-`p` input read at the tilted chart datum,
  modulo `((ϖ♭)^p)`.

The `Type 0` originals are pinned (`{W : Type}`, `{R : Type}` = `Type 0` in Lean 4) and unusable at
`Type u`, where the assembly of the M5c node (`Submission/Work/DSM5c/Main.lean`) lives.  All the
ingredients are already universe-polymorphic, so only the binders change.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open CategoryTheory.Limits Opposite

universe u

namespace Work.DSM5c.Cech

/-- **The restriction maps `rho` of the perfected chart rings commute with `algebraMap`**
(universe-polymorphic copy of `Work.DSM5c.Cech.perfChartRho_algebraMap`). -/
lemma perfChartRho_algebraMapU {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p]
    [PerfectRing R p] {ι : Type u} [Finite ι] [DecidableEq ι] (t : ι → R) {S T : Finset ι}
    (h : S ⊆ T) (w : R) :
    Work.DSM5b.rho p t h
      ⟨algebraMap R (Localization.Away (tS t S)) w, (perfChartRing p t S).algebraMap_mem w⟩
      = ⟨algebraMap R (Localization.Away (tS t T)) w, (perfChartRing p t T).algebraMap_mem w⟩ := by
  apply Subtype.ext
  rw [Work.DSM5b.rho_coe]
  exact AlgHom.commutes (locRes t h) w

/-- **The diagonal coaugmentation of the perfected chart Čech complex is a 0-cocycle**
(universe-polymorphic copy of `Work.DSM5c.Cech.perfChartCoaug_d01`). -/
theorem perfChartCoaug_d01U {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p]
    [PerfectRing R p] {ι : Type u} [Finite ι] [DecidableEq ι] (t : ι → R) (w : R) :
    (((CategoryTheory.cechComplexFunctor (DSMap.Mix2.chartIdx ι)).obj
        (DSMap.Mix2.perfChartPresheaf p t)).d 0 1)
      ((DSMap.Mix2.perfChartCoaug p t).hom w) = 0 := by
  have key : Work.DSM5b.PCd p t 0
      (Work.DSM5b.PCAux.PhiQ p R t ((perfChartCoaug p t).hom w)) = 0 := by
    have hz : ∀ τ : Fin 1 → ι, Work.DSM5b.PCAux.PhiQ p R t ((perfChartCoaug p t).hom w) τ
        = ⟨algebraMap R (Localization.Away (tS t (Work.DSM5b.tupRng τ))) w,
            (perfChartRing p t (Work.DSM5b.tupRng τ)).algebraMap_mem w⟩ := fun τ =>
      congrFun (Work.DSM5b.PCAux.PhiQ_coaug p R t w) τ
    funext τ
    rw [Work.DSM5b.PCd_apply]
    have hterm : ∀ i : Fin 2, (-1 : R) ^ (i : ℕ) •
        Work.DSM5b.rho p t (Work.DSM5b.tupRng_del_subset i τ)
          (Work.DSM5b.PCAux.PhiQ p R t ((perfChartCoaug p t).hom w) (Work.DSM5b.tupDel i τ))
        = (-1 : R) ^ (i : ℕ) •
          (⟨algebraMap R (Localization.Away (tS t (Work.DSM5b.tupRng τ))) w,
            (perfChartRing p t (Work.DSM5b.tupRng τ)).algebraMap_mem w⟩ :
              ↥(perfChartRing p t (Work.DSM5b.tupRng τ))) := by
      intro i
      rw [hz (Work.DSM5b.tupDel i τ),
        perfChartRho_algebraMapU t (Work.DSM5b.tupRng_del_subset i τ) w]
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    rw [Fin.sum_univ_two]
    simp
  exact (Work.DSM5b.PCAux.PhiQ_d_iff p R t ((perfChartCoaug p t).hom w)).mpr key

end Work.DSM5c.Cech

namespace Work.DSM5c.Lp

/-- **The perfected tilted chart is regular for `(ϖ♭)^p`** (universe-polymorphic copy of
`Work.DSM5c.Lp.isSMulRegular_perfChartRing_tiltVarpi_pow`). -/
theorem isSMulRegular_perfChartRing_tiltVarpi_powU {p : ℕ} [Fact p.Prime] {W : Type u}
    [CommRing W] [Fact ¬IsUnit (p : W)] [IsAdicComplete (Ideal.span {(p : W)}) W]
    {ι : Type u} [DecidableEq ι] (Q : DSMap.PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (S : Finset ι) :
    IsSMulRegular ↥(perfChartRing p (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) S)
      ((Work.DSM5c.tiltVarpi Q) ^ p) := by
  have h := (Work.DSM5c.G2.U.chartPhi_tiltVarpi_isSMulRegular Q t tr htr0 htr j₀ e S).pow p
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

/-- **`hreg` of the dévissage** (universe-polymorphic copy of
`Work.DSM5c.Lp.isSMulRegular_tiltGenCechTerm`): the terms of the Čech complex of the perfected
tilted charts are regular for `(ϖ♭)^p`. -/
theorem isSMulRegular_tiltGenCechTermU {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W]
    [Fact ¬IsUnit (p : W)] [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type u} [Finite ι]
    [DecidableEq ι] (Q : DSMap.PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (q : ℕ) :
    IsSMulRegular
      (((CategoryTheory.cechComplexFunctor (DSMap.Mix2.chartIdx ι)).obj
        (DSMap.Mix2.perfChartPresheaf p
          (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e))).X q)
      ((Work.DSM5c.tiltVarpi Q) ^ p) := by
  have hfac := isSMulRegular_perfChartRing_tiltVarpi_powU Q t tr htr0 htr j₀ e
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

/-- **The characteristic-`p` input at the tilted chart datum, modulo `((ϖ♭)^p)`**
(universe-polymorphic copy of `Work.DSM5c.Lp.almostAcyc_tiltGen`). -/
theorem almostAcyc_tiltGenU {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W]
    [Fact ¬IsUnit (p : W)] [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type u} [Finite ι]
    [DecidableEq ι] (Q : DSMap.PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (hM5b : Work.DSM5c.M5bInput p (PreTilt W p)
      (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) (Work.DSM5c.tiltVarpi Q)) :
    DSMap.Mix2.AlmostAcyc (fun k => (frobeniusEquiv (PreTilt W p) p).symm^[k]
      (Work.DSM5c.tiltVarpi Q)) (Ideal.span {(Work.DSM5c.tiltVarpi Q) ^ p})
      ((CategoryTheory.cechComplexFunctor (DSMap.Mix2.chartIdx ι)).obj
        (DSMap.Mix2.perfChartPresheaf p
          (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e)))
      (DSMap.Mix2.perfChartCoaug p (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e)) := by
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
    (fun w => Work.DSM5c.Cech.perfChartCoaug_d01U (p := p) (R := PreTilt W p) (ι := ι)
      (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) w)
    (fun q => isSMulRegular_tiltGenCechTermU Q t tr htr0 htr j₀ e q)
    hM5b

end Work.DSM5c.Lp
