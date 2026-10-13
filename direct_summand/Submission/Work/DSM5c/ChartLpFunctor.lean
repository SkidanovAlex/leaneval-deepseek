import Submission.Work.DSM5c.ChartLp
import Submission.Work.DSM5c.Lp.chartLMap_algebraMap

/-!
# DSM5c — the mod-`p` comparison presheaf `Lp`

`Submission/Work/DSM5c/ChartLp.lean` supplies the objects `L_S = R_S ⧸ (φ_S (ϖ♭) ^ p)`, their
`W`-algebra structures `chartLAlg` (through PB2) and the restriction maps `chartLMap`; the child
`Submission/Work/DSM5c/Lp/chartLMap_algebraMap.lean` proves that `chartLMap` is `W`-linear for those
structures.  This file records the elementwise laws of `chartLMap` and the objects
`Work.DSM5c.chartLpObj` of the presheaf

  `Work.DSM5c.chartLp … : (Finset ι)ᵒᵖᵒᵖ ⥤ ModuleCat.{a} W`,

the `Lp` of the M5c transport (`NOTES.md` §20.2): the codomain of the termwise surjection
`Dp ⟶ Lp` with kernel `(p) · ⊤`, and the home of the characteristic-`p` input read through the
mod-`p` comparison.

The bundling of `chartLpObj` and `chartLMap` into the presheaf itself (`chartLp`), together with the
surjection `chartDToLp` and its kernel computation, is delegated: the statement to use is
`Work.DSM5c.Lp.chartDToLp_exists` in `Submission/Work/DSM5c/Lp/`.  The obstruction is purely
elaboration-theoretic — the `W`-module structure on `L_S` comes from the non-global instance
`chartLAlg`, so `ModuleCat.ofHom`-based bundling spends the whole heartbeat budget in `whnf` /
instance synthesis (a `set_option maxHeartbeats 6000000` does not help); the fix is the one that
worked for the functor `Work.DSM5c.chartD` in `Submission/Work/DSM5c/ChartFunctor.lean`: state the
`W`-linearity as a *closed* lemma and feed it to `ModuleCat.ofHom` as a term.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

namespace Work.DSM5c

universe a

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

section Lp

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
  [IsAdicComplete (Ideal.span {(p : W)}) W]
variable {ι : Type a} [DecidableEq ι]

/-- The self-map of the mod-`p` chart is the identity. -/
theorem chartLMap_self (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (S : Finset ι) (h : S ⊆ S)
    (x : tiltChart Q t tr htr0 htr j₀ e S ⧸ chartLIdeal Q t tr htr0 htr j₀ e S) :
    chartLMap Q t tr htr0 htr j₀ e h x = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Subsingleton.elim h (subset_refl S)]
  exact chartLMap_self_mk Q t tr htr0 htr j₀ e S a

/-- The composition rule for the mod-`p` chart restrictions. -/
theorem chartLMap_comp (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    {S T V : Finset ι} (h₁ : S ⊆ T) (h₂ : T ⊆ V)
    (x : tiltChart Q t tr htr0 htr j₀ e S ⧸ chartLIdeal Q t tr htr0 htr j₀ e S) :
    chartLMap Q t tr htr0 htr j₀ e (h₁.trans h₂) x =
      chartLMap Q t tr htr0 htr j₀ e h₂ (chartLMap Q t tr htr0 htr j₀ e h₁ x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact chartLMap_comp_mk Q t tr htr0 htr j₀ e h₁ h₂ a

/-- The object of `chartLp` at `S`: the mod-`p` chart `L_S`, as a `W`-module through `chartLAlg`. -/
noncomputable def chartLpObj (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (S : (Finset ι)ᵒᵖᵒᵖ) : ModuleCat.{a} W := by
  letI := chartLAlg Q t tr htr0 htr j₀ e S.unop.unop
  exact ModuleCat.of W (tiltChart Q t tr htr0 htr j₀ e S.unop.unop ⧸
    chartLIdeal Q t tr htr0 htr j₀ e S.unop.unop)

end Lp

end Work.DSM5c
