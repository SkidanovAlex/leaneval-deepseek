import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Defs
import Submission.Work.BoseFixB2.Polar.trialVal_parallelogram
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Polar.neuFrac_parallelogram`

**The parallelogram identity for the box Neumann-resolvent fraction `neuFrac`.**

`neuFrac ℓ a² u φ` (FS `eq:DefT`'s first term, `Work.BoseKinLoc.neuFrac`) is defined as the
infimum, over globally smooth compactly supported trials `g`, of FS's Dirichlet trial
functional

`T(φ,g) = ∫_{Λ} φ² − 2a²∫_{Λ} φ g + a²(Σ_k∫_{Λ}(∂_k g)² + a²∫_{Λ} g²)`,
`Λ = lamBox ℓ u = ℓu + acube ℓ`

(`Work.BoseKinLoc.Kinetic.trialVal`).  We show that `φ ↦ neuFrac ℓ a² u φ` is a quadratic
form, i.e. satisfies the parallelogram law

`Q(f+g) + Q(f−g) = 2Q(f) + 2Q(g)`

for smooth `f, g`.

## Why the argument is purely *algebraic about the trial class*

Write `C` for the trial class (globally smooth, compactly supported functions), so that
`Q(φ) = sInf {T(φ,g) : g ∈ C}` and `Q(φ) ≤ T(φ,g)` for every `g ∈ C` (the latter because the
trial set is bounded below as soon as `φ²` is integrable on the box,
`Kinetic.bddBelow_trialSet_of_integrableOn'`).

The point is that, in the *pair* `(φ,g)`, the functional `T` is a **quadratic form**: with
`(A,B) ↦ (A+B, A−B)` a bijection of `C × C` (its inverse being `(P,Q) ↦ ((P±Q)/2)`, and `C`
is a real vector space),

`T(f+g, A+B) + T(f−g, A−B) = 2·(T(f,A) + T(g,B))`   (`trialVal_parallelogram`).

Both directions of the parallelogram law now follow from `le_csInf`, without knowing anything
about *which* trial attains the infimum — no resolvent theory, no completion of the square:

* `2Q(f) + 2Q(g) ≥ Q(f+g) + Q(f−g)`:  for all `A, B ∈ C`,
  `Q(f+g) + Q(f−g) ≤ T(f+g,A+B) + T(f−g,A−B) = 2T(f,A) + 2T(g,B)`; take the infimum in `B`,
  then in `A` (`le_csInf`).
* `Q(f+g) + Q(f−g) ≥ 2Q(f) + 2Q(g)`:  for all `P, Q ∈ C`, the *inverse* substitution
  `A = (P+Q)/2`, `B = (P−Q)/2` gives
  `T(f+g,P) + T(f−g,Q) = 2T(f,A) + 2T(g,B) ≥ 2Q(f) + 2Q(g)`; take the infimum in `Q`, then
  in `P`.

The two directions pin the identity.  This is the polarisation input of the `BoseFixB2`
polarised-word construction (`Work.BoseFixB2.polB` uses `wordB(Φ+Ψ) − wordB(Φ−Ψ)`, FS §6).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB2.Polar

set_option autoImplicit false
set_option linter.unusedVariables false

theorem neuFrac_parallelogram {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2) (u : EuclideanSpace ℝ (Fin 3)) {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) : Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => f z + g z) + Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => f z - g z) = 2 * Work.BoseKinLoc.neuFrac ℓ a2 u f + 2 * Work.BoseKinLoc.neuFrac ℓ a2 u g := by
  have ha2le : (0 : ℝ) ≤ a2 := le_of_lt ha2
  -- write the two `f ± g` states in the pointwise-addition form used everywhere below
  show Work.BoseKinLoc.neuFrac ℓ a2 u (f + g) + Work.BoseKinLoc.neuFrac ℓ a2 u (f - g)
      = 2 * Work.BoseKinLoc.neuFrac ℓ a2 u f + 2 * Work.BoseKinLoc.neuFrac ℓ a2 u g
  have hcf : Continuous f := hf.continuous
  have hcg : Continuous g := hg.continuous
  -- the four states are square-integrable on the box
  have hIf : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (f z) ^ 2)
      (MeasureTheory.volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
    integrableOn_sq_of_continuous hℓ u hcf
  have hIg : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (g z) ^ 2)
      (MeasureTheory.volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
    integrableOn_sq_of_continuous hℓ u hcg
  have hIfg : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => ((f + g) z) ^ 2)
      (MeasureTheory.volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
    integrableOn_sq_of_continuous hℓ u (hcf.add hcg)
  have hIfm : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => ((f - g) z) ^ 2)
      (MeasureTheory.volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
    integrableOn_sq_of_continuous hℓ u (hcf.sub hcg)
  -- the upper-bound half of the variational principle, in `sInf` form
  have hSf : ∀ A : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ENat) A →
      HasCompactSupport A →
      sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u f)
        ≤ Work.BoseKinLoc.Kinetic.trialVal ℓ a2 u f A := by
    intro A hA hAs
    have h := neuFrac_le_trialVal_of_integrableOn (ℓ := ℓ) (a2 := a2) ha2le u hIf hA hAs
    rwa [Work.BoseKinLoc.Kinetic.neuFrac_eq_sInf_trialSet] at h
  have hSg : ∀ A : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ENat) A →
      HasCompactSupport A →
      sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u g)
        ≤ Work.BoseKinLoc.Kinetic.trialVal ℓ a2 u g A := by
    intro A hA hAs
    have h := neuFrac_le_trialVal_of_integrableOn (ℓ := ℓ) (a2 := a2) ha2le u hIg hA hAs
    rwa [Work.BoseKinLoc.Kinetic.neuFrac_eq_sInf_trialSet] at h
  have hSfg : ∀ A : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ENat) A →
      HasCompactSupport A →
      sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u (f + g))
        ≤ Work.BoseKinLoc.Kinetic.trialVal ℓ a2 u (f + g) A := by
    intro A hA hAs
    have h := neuFrac_le_trialVal_of_integrableOn (ℓ := ℓ) (a2 := a2) ha2le u hIfg hA hAs
    rwa [Work.BoseKinLoc.Kinetic.neuFrac_eq_sInf_trialSet] at h
  have hSfm : ∀ A : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ENat) A →
      HasCompactSupport A →
      sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u (f - g))
        ≤ Work.BoseKinLoc.Kinetic.trialVal ℓ a2 u (f - g) A := by
    intro A hA hAs
    have h := neuFrac_le_trialVal_of_integrableOn (ℓ := ℓ) (a2 := a2) ha2le u hIfm hA hAs
    rwa [Work.BoseKinLoc.Kinetic.neuFrac_eq_sInf_trialSet] at h
  -- `Q(f+g) + Q(f−g) ≤ 2Q(f) + 2Q(g)`: take the infimum of `2T(f,A) + 2T(g,B)`
  have hdir1 : sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u (f + g))
        + sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u (f - g))
      ≤ 2 * sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u f)
        + 2 * sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u g) := by
    -- the parallelogram identity turns the pair `(A+B, A−B)` into `2T(f,A) + 2T(g,B)`
    have key : ∀ A B : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ENat) A →
        HasCompactSupport A → ContDiff ℝ (⊤ : ENat) B → HasCompactSupport B →
        sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u (f + g))
            + sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u (f - g))
          ≤ 2 * Work.BoseKinLoc.Kinetic.trialVal ℓ a2 u f A
            + 2 * Work.BoseKinLoc.Kinetic.trialVal ℓ a2 u g B := by
      intro A B hA hAs hB hBs
      have h1 := hSfg (A + B) (hA.add hB) (hAs.add hBs)
      have h2 := hSfm (A - B) (hA.sub hB) (hAs.sub hBs)
      have h3 := trialVal_parallelogram (ℓ := ℓ) (a2 := a2) u hf hg hA hAs hB hBs
      linarith
    -- infimum in `B`, then in `A`
    have hstep : (sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u (f + g))
          + sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u (f - g))
          - 2 * sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u g)) / 2
        ≤ sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u f) := by
      refine le_csInf ⟨_, Work.BoseKinLoc.Kinetic.zero_mem_trialSet ℓ a2 u f⟩ ?_
      rintro c ⟨A, hA, hAs, rfl⟩
      have hinner : (sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u (f + g))
            + sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u (f - g))
            - 2 * Work.BoseKinLoc.Kinetic.trialVal ℓ a2 u f A) / 2
          ≤ sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u g) := by
        refine le_csInf ⟨_, Work.BoseKinLoc.Kinetic.zero_mem_trialSet ℓ a2 u g⟩ ?_
        rintro c ⟨B, hB, hBs, rfl⟩
        have hk := key A B hA hAs hB hBs
        linarith
      linarith
    linarith
  -- `2Q(f) + 2Q(g) ≤ Q(f+g) + Q(f−g)`: the inverse substitution `A = (P+Q)/2`, `B = (P−Q)/2`
  have hdir2 : 2 * sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u f)
        + 2 * sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u g)
      ≤ sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u (f + g))
        + sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u (f - g)) := by
    have key2 : ∀ P Q : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ENat) P →
        HasCompactSupport P → ContDiff ℝ (⊤ : ENat) Q → HasCompactSupport Q →
        2 * sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u f)
            + 2 * sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u g)
          ≤ Work.BoseKinLoc.Kinetic.trialVal ℓ a2 u (f + g) P
            + Work.BoseKinLoc.Kinetic.trialVal ℓ a2 u (f - g) Q := by
      intro P Q hP hPs hQ hQs
      have hAc : ContDiff ℝ (⊤ : ENat)
          (fun z : EuclideanSpace ℝ (Fin 3) => (P z + Q z) / 2) :=
        contDiff_half_sum hP hQ
      have hAcs : HasCompactSupport
          (fun z : EuclideanSpace ℝ (Fin 3) => (P z + Q z) / 2) :=
        hasCompactSupport_half_sum hPs hQs
      have hBc : ContDiff ℝ (⊤ : ENat)
          (fun z : EuclideanSpace ℝ (Fin 3) => (P z - Q z) / 2) :=
        contDiff_half_diff hP hQ
      have hBcs : HasCompactSupport
          (fun z : EuclideanSpace ℝ (Fin 3) => (P z - Q z) / 2) :=
        hasCompactSupport_half_diff hPs hQs
      have halg := trialVal_parallelogram (ℓ := ℓ) (a2 := a2) u hf hg hAc hAcs hBc hBcs
      have hsum : (fun z : EuclideanSpace ℝ (Fin 3) => (P z + Q z) / 2)
            + (fun z : EuclideanSpace ℝ (Fin 3) => (P z - Q z) / 2) = P := by
        funext z
        simp only [Pi.add_apply]
        ring
      have hdiff : (fun z : EuclideanSpace ℝ (Fin 3) => (P z + Q z) / 2)
            - (fun z : EuclideanSpace ℝ (Fin 3) => (P z - Q z) / 2) = Q := by
        funext z
        simp only [Pi.sub_apply]
        ring
      rw [hsum, hdiff] at halg
      have h1 := hSf (fun z : EuclideanSpace ℝ (Fin 3) => (P z + Q z) / 2) hAc hAcs
      have h2 := hSg (fun z : EuclideanSpace ℝ (Fin 3) => (P z - Q z) / 2) hBc hBcs
      linarith
    -- infimum in `Q`, then in `P`
    have hstep : (2 * sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u f)
          + 2 * sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u g)
          - sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u (f - g)))
        ≤ sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u (f + g)) := by
      refine le_csInf ⟨_, Work.BoseKinLoc.Kinetic.zero_mem_trialSet ℓ a2 u (f + g)⟩ ?_
      rintro c ⟨P, hP, hPs, rfl⟩
      have hinner : (2 * sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u f)
            + 2 * sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u g)
            - Work.BoseKinLoc.Kinetic.trialVal ℓ a2 u (f + g) P)
          ≤ sInf (Work.BoseKinLoc.Kinetic.trialSet ℓ a2 u (f - g)) := by
        refine le_csInf ⟨_, Work.BoseKinLoc.Kinetic.zero_mem_trialSet ℓ a2 u (f - g)⟩ ?_
        rintro c ⟨Q, hQ, hQs, rfl⟩
        have hk := key2 P Q hP hPs hQ hQs
        linarith
      linarith
    linarith
  -- `neuFrac` is *definitionally* the `sInf` of the trial set, so the two inequalities
  -- transfer to the statement at hand
  have hdir1' : Work.BoseKinLoc.neuFrac ℓ a2 u (f + g)
        + Work.BoseKinLoc.neuFrac ℓ a2 u (f - g)
      ≤ 2 * Work.BoseKinLoc.neuFrac ℓ a2 u f + 2 * Work.BoseKinLoc.neuFrac ℓ a2 u g := hdir1
  have hdir2' : 2 * Work.BoseKinLoc.neuFrac ℓ a2 u f + 2 * Work.BoseKinLoc.neuFrac ℓ a2 u g
      ≤ Work.BoseKinLoc.neuFrac ℓ a2 u (f + g) + Work.BoseKinLoc.neuFrac ℓ a2 u (f - g) := hdir2
  linarith

end Work.BoseFixB2.Polar
