import Mathlib
import Submission.Work.DSM5c.Lp.chartDToLp_exists
import Submission.Work.DSM5c.ChartFunctor

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option allowUnsafeReducibility true

-- See `LpDefs.lean`: the locally `reducible` attributes let the quotient API rewrite under the
-- bundled chart objects (which are `def`s in other modules).
attribute [local reducible] Work.DSM5c.chartDObj Work.DSM5c.chartD Work.DSM5c.chartDOfHom
  Work.DSM5c.Lp.chartLQObj Work.DSM5c.Lp.chartLQOfHom Work.DSM5c.Lp.chartLQEta
  Work.DSM5c.Lp.chartLQ Work.DSM5c.Lp.chartUntiltIdeal

namespace Work.DSM5c.Lp

universe u

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2 Opposite

/-- **Universe-polymorphic restatement of `Work.DSM5c.Lp.chartDToLp_exists`** (transport step 5: the
mod-`p` chart presheaf `Lp` and the termwise surjection `Dp ⟶ Lp` with kernel `(p) · ⊤`).

The original is stated at `Type 0` and is unusable at `Type a`; the frozen node
`DSMap.Mix2.area_M5c` and the assembly in `Submission/Work/DSM5c/Main.lean` live at `Type a`
(`W : Type a`, `ι : Type a`).  Per the reviews, all the ingredients
(`Work.DSM5c.chartD`, `Work.DSM5c.chartLpObj`, `Work.DSM5c.Lp.chartLQ`,
`Work.DSM5c.Lp.chartLQEta`, `Work.DSM5c.Lp.chartLQEta_app_surjective`,
`Work.DSM5c.Lp.chartCmpLinear_ker`, `Work.DSM5c.Lp.ker_Pi_map_span`) are *already* universe
polymorphic, so only the two binders of this declaration need loosening and the proof transfers
verbatim.  Keep the original file. -/
theorem chartDToLp_existsU {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W] [Fact ¬IsUnit (p : W)]
    [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type u} [DecidableEq ι]
    (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) :
    ∃ (Lp : (Finset ι)ᵒᵖᵒᵖ ⥤ ModuleCat W)
      (f : (cechComplexFunctor (chartIdx ι)).obj
          (Work.DSM5c.chartD (p := p) (W := W) Q hθ t tr htr0 htr j₀ e) ⟶
        (cechComplexFunctor (chartIdx ι)).obj Lp),
      (∀ (S : (Finset ι)ᵒᵖᵒᵖ), Nonempty (Lp.obj S ≅
        Work.DSM5c.chartLpObj (p := p) (W := W) Q t tr htr0 htr j₀ e S)) ∧
      (∀ q, Function.Surjective (f.f q).hom) ∧
      (∀ (q : ℕ) (x : ((cechComplexFunctor (chartIdx ι)).obj
          (Work.DSM5c.chartD (p := p) (W := W) Q hθ t tr htr0 htr j₀ e)).X q),
        (f.f q).hom x = 0 ↔ x ∈ Ideal.span {(p : W)} •
          (⊤ : Submodule W (((cechComplexFunctor (chartIdx ι)).obj
            (Work.DSM5c.chartD (p := p) (W := W) Q hθ t tr htr0 htr j₀ e)).X q))) := by
  refine ⟨chartLQ Q hθ t tr htr0 htr j₀ e,
    (cechComplexFunctor (chartIdx ι)).map (chartLQEta Q hθ t tr htr0 htr j₀ e), ?_, ?_, ?_⟩
  · intro S
    exact chartLQObj_iso Q hθ t tr htr0 htr j₀ e S
  · intro q
    have hq : ((cechComplexFunctor (chartIdx ι)).map
        (chartLQEta Q hθ t tr htr0 htr j₀ e)).f q =
        CategoryTheory.Limits.Pi.map (fun i : (Fin (q + 1) → ι) =>
          (chartLQEta Q hθ t tr htr0 htr j₀ e).app (cechIdx (q := q) i)) :=
      cech_map_f (chartD Q hθ t tr htr0 htr j₀ e) (chartLQ Q hθ t tr htr0 htr j₀ e)
        (chartLQEta Q hθ t tr htr0 htr j₀ e) q
    rw [hq]
    exact surjective_Pi_map _ _ _ (fun i => chartLQEta_app_surjective Q hθ t tr htr0 htr j₀ e _)
  · intro q x
    have hq : ((cechComplexFunctor (chartIdx ι)).map
        (chartLQEta Q hθ t tr htr0 htr j₀ e)).f q =
        CategoryTheory.Limits.Pi.map (fun i : (Fin (q + 1) → ι) =>
          (chartLQEta Q hθ t tr htr0 htr j₀ e).app (cechIdx (q := q) i)) :=
      cech_map_f (chartD Q hθ t tr htr0 htr j₀ e) (chartLQ Q hθ t tr htr0 htr j₀ e)
        (chartLQEta Q hθ t tr htr0 htr j₀ e) q
    rw [hq]
    have key : ∀ y : ↥(∏ᶜ fun i : (Fin (q + 1) → ι) =>
        (chartD Q hθ t tr htr0 htr j₀ e).obj (cechIdx (q := q) i)),
        (CategoryTheory.Limits.Pi.map fun i : (Fin (q + 1) → ι) =>
          (chartLQEta Q hθ t tr htr0 htr j₀ e).app (cechIdx (q := q) i)).hom y = 0 ↔
        y ∈ Ideal.span {(p : W)} • (⊤ : Submodule W ↥(∏ᶜ fun i : (Fin (q + 1) → ι) =>
          (chartD Q hθ t tr htr0 htr j₀ e).obj (cechIdx (q := q) i))) := by
      intro y
      rw [← LinearMap.mem_ker,
        ker_Pi_map_span (fun i : (Fin (q + 1) → ι) =>
            (chartD Q hθ t tr htr0 htr j₀ e).obj (cechIdx (q := q) i))
          (fun i => (chartLQ Q hθ t tr htr0 htr j₀ e).obj (cechIdx (q := q) i))
          (fun i => (chartLQEta Q hθ t tr htr0 htr j₀ e).app (cechIdx (q := q) i))
          (p : W)
          (fun i => by
            letI := chartDAlg Q hθ t tr htr0 htr j₀ e (cechIdx (q := q) i).unop.unop
            exact Submodule.ker_mkQ (chartDpTop Q hθ t tr htr0 htr j₀ e
              (cechIdx (q := q) i).unop.unop))]
    exact key x

end Work.DSM5c.Lp
