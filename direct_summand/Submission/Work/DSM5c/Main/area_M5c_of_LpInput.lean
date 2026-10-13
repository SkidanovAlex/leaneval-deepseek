import Mathlib
import Submission.Work.DSM5c.G2.isSMulRegular_chartUntiltU
import Submission.Work.DSM5c.Lp.chartDToLp_existsU
import Submission.Work.DSM5c.Cech.chartCoaug_isCocycleU
import Submission.Work.DSM5c.Eta.exists_chartMapU
import Submission.Work.DSM5c.Devissage.almostAcyc_of_surjective_kernel_v2
import Submission.Work.DSM5c.Devissage.almostAcyc_span_pow
import Submission.Work.DSM5c.CharP

namespace Work.DSM5c.Main

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe u

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.haveILetI false

/-! ## Helper lemmas: `p`-torsion-freeness of the terms of the chart Čech complex

The dévissage `Work.DSM5c.almostAcyc_span_pow` consumes `hreg : ∀ q, IsSMulRegular (K.X q) (p : W)`
for `K = Č (Work.DSM5c.chartD …)`.  The degree-`q` term of the Čech complex is the categorical
product `∏ᶜ` of the chart untilts `D_S` over the `(q+1)`-tuples of chart indices, so the input is

* a general fact about `ModuleCat`: `IsSMulRegular` of a categorical product is the conjunction of
  the `IsSMulRegular` of the factors (`isSMulRegular_piObj`), and

* the `Type 0`-free chart input `Work.DSM5c.G2.isSMulRegular_chartUntiltU`, i.e. that `p` is a
  non-zero-divisor of `D_S` (`isSMulRegular_chartDCechTerm`). -/

/-- **`IsSMulRegular` of a categorical product of `W`-modules.**  If `r` acts injectively on every
factor `Z i`, it acts injectively on the product `∏ᶜ Z`: transport along the linear equivalence
`ModuleCat.piIsoPi Z : ∏ᶜ Z ≃ₗ[W] (∀ i, Z i)` and apply `IsSMulRegular.pi`.

No finiteness of the index type is needed. -/
lemma isSMulRegular_piObj {W : Type u} [CommRing W] {ι : Type u} (Z : ι → ModuleCat.{u} W)
    (r : W) (h : ∀ i, IsSMulRegular (Z i) r) : IsSMulRegular (↥(∏ᶜ Z)) r := by
  have hpi : IsSMulRegular (↥(ModuleCat.of W (∀ i, Z i))) r := IsSMulRegular.pi (fun i => h i)
  intro x y hxy
  refine (CategoryTheory.Iso.toLinearEquiv (ModuleCat.piIsoPi Z)).injective ?_
  exact hpi ((map_smul _ r x).symm.trans ((congrArg _ hxy).trans (map_smul _ r y)))

/-- **`p` is a non-zero-divisor of every term of the chart Čech complex.**  The degree-`q` term of
`Č (Work.DSM5c.chartD …)` is the product of the chart untilts `D_S = untiltOf R_S φ_S` over the
`(q+1)`-tuples `S` of chart indices (`Work.DSM5c.Lp.cechIdx`); each factor is `p`-torsion-free by
`Work.DSM5c.G2.isSMulRegular_chartUntiltU`, and `IsSMulRegular` of a product is componentwise. -/
lemma isSMulRegular_chartDCechTerm {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W]
    [Fact ¬IsUnit (p : W)] [IsAdicComplete (Ideal.span {(p : W)}) W]
    {ι : Type u} [DecidableEq ι]
    (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (hj₀ : t j₀ = Q.ϖ 0 ^ e) (q : ℕ) :
    IsSMulRegular
      (((cechComplexFunctor (chartIdx ι)).obj
        (Work.DSM5c.chartD (p := p) (W := W) Q hθ t tr htr0 htr j₀ e)).X q)
      (p : W) := by
  change IsSMulRegular (↥((∏ᶜ (fun i : (Fin (q + 1) → ι) =>
      (Work.DSM5c.chartD (p := p) (W := W) Q hθ t tr htr0 htr j₀ e).obj
        (Work.DSM5c.Lp.cechIdx (q := q) i))) : ModuleCat.{u} W)) (p : W)
  refine isSMulRegular_piObj _ _ (fun i => ?_)
  have hG2 := Work.DSM5c.G2.isSMulRegular_chartUntiltU (p := p) (W := W) Q t tr htr0 htr j₀ e
    hj₀ (Work.DSM5c.Lp.cechIdx (q := q) i).unop.unop
  letI := Work.DSM5c.chartDAlg (p := p) (W := W) Q hθ t tr htr0 htr j₀ e
    (Work.DSM5c.Lp.cechIdx (q := q) i).unop.unop
  change IsSMulRegular (Work.DSM5c.untiltOf
    (Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e (Work.DSM5c.Lp.cechIdx (q := q) i).unop.unop)
    (Work.DSM5c.chartPhi Q t tr htr0 htr j₀ e
      (Work.DSM5c.Lp.cechIdx (q := q) i).unop.unop)) (p : W)
  refine (isSMulRegular_map (f := algebraMap W (Work.DSM5c.untiltOf
      (Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e (Work.DSM5c.Lp.cechIdx (q := q) i).unop.unop)
      (Work.DSM5c.chartPhi Q t tr htr0 htr j₀ e
        (Work.DSM5c.Lp.cechIdx (q := q) i).unop.unop))) (a := (p : W)) ?_).mp ?_
  · intro m
    rw [Algebra.smul_def]; rfl
  · rw [map_natCast]
    exact hG2

/-- **The Čech-level surjectivity/kernel pair of the mod-`p` chart comparison** (transport step 5
of `NOTES.md` §20.2), for the specific witnesses `Work.DSM5c.Lp.chartLQ` and
`Work.DSM5c.Lp.chartLQEta` that the frozen input `hL` of `area_M5c_of_LpInput` refers to: the
degree-`q` component of `Č (chartLQEta …)` is termwise surjective with kernel exactly
`(p) · ⊤ ⊆ (Č (chartD …)).X q`.

This is the pair `(hsurj, hker)` of hypotheses of
`Work.DSM5c.Devissage.almostAcyc_of_surjective_kernel_v2`.  It is a componentwise reading of
`Work.DSM5c.Lp.cech_map_f` + `Work.DSM5c.Lp.surjective_Pi_map` + `Work.DSM5c.Lp.ker_Pi_map_span`,
i.e. the two conjuncts that `Work.DSM5c.Lp.chartDToLp_existsU` proves about its *existential*
witnesses. -/
private lemma cechChartLQEta_surj_ker {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W]
    [Fact ¬IsUnit (p : W)] [IsAdicComplete (Ideal.span {(p : W)}) W]
    {ι : Type u} [DecidableEq ι]
    (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) :
    (∀ q, Function.Surjective (((cechComplexFunctor (chartIdx ι)).map
      (Work.DSM5c.Lp.chartLQEta (p := p) (W := W) Q hθ t tr htr0 htr j₀ e)).f q).hom) ∧
    (∀ (q : ℕ) (x : ((cechComplexFunctor (chartIdx ι)).obj
        (Work.DSM5c.chartD (p := p) (W := W) Q hθ t tr htr0 htr j₀ e)).X q),
      (((cechComplexFunctor (chartIdx ι)).map
        (Work.DSM5c.Lp.chartLQEta (p := p) (W := W) Q hθ t tr htr0 htr j₀ e)).f q).hom x = 0 ↔
      x ∈ Ideal.span {(p : W)} • (⊤ : Submodule W (((cechComplexFunctor (chartIdx ι)).obj
        (Work.DSM5c.chartD (p := p) (W := W) Q hθ t tr htr0 htr j₀ e)).X q))) := by
  constructor
  · intro q
    rw [Work.DSM5c.Lp.cech_map_f (Work.DSM5c.chartD Q hθ t tr htr0 htr j₀ e)
        (Work.DSM5c.Lp.chartLQ Q hθ t tr htr0 htr j₀ e)
        (Work.DSM5c.Lp.chartLQEta Q hθ t tr htr0 htr j₀ e) q]
    exact Work.DSM5c.Lp.surjective_Pi_map _ _ _
      (fun i => Work.DSM5c.Lp.chartLQEta_app_surjective Q hθ t tr htr0 htr j₀ e _)
  · intro q x
    rw [Work.DSM5c.Lp.cech_map_f (Work.DSM5c.chartD Q hθ t tr htr0 htr j₀ e)
        (Work.DSM5c.Lp.chartLQ Q hθ t tr htr0 htr j₀ e)
        (Work.DSM5c.Lp.chartLQEta Q hθ t tr htr0 htr j₀ e) q]
    have key : ∀ y : ↥(∏ᶜ fun i : (Fin (q + 1) → ι) =>
        (Work.DSM5c.chartD Q hθ t tr htr0 htr j₀ e).obj (Work.DSM5c.Lp.cechIdx (q := q) i)),
        (CategoryTheory.Limits.Pi.map fun i : (Fin (q + 1) → ι) =>
          (Work.DSM5c.Lp.chartLQEta Q hθ t tr htr0 htr j₀ e).app
            (Work.DSM5c.Lp.cechIdx (q := q) i)).hom y = 0 ↔
        y ∈ Ideal.span {(p : W)} • (⊤ : Submodule W ↥(∏ᶜ fun i : (Fin (q + 1) → ι) =>
          (Work.DSM5c.chartD Q hθ t tr htr0 htr j₀ e).obj
            (Work.DSM5c.Lp.cechIdx (q := q) i))) := by
      intro y
      rw [← LinearMap.mem_ker,
        Work.DSM5c.Lp.ker_Pi_map_span (fun i : (Fin (q + 1) → ι) =>
            (Work.DSM5c.chartD Q hθ t tr htr0 htr j₀ e).obj
              (Work.DSM5c.Lp.cechIdx (q := q) i))
          (fun i => (Work.DSM5c.Lp.chartLQ Q hθ t tr htr0 htr j₀ e).obj
            (Work.DSM5c.Lp.cechIdx (q := q) i))
          (fun i => (Work.DSM5c.Lp.chartLQEta Q hθ t tr htr0 htr j₀ e).app
            (Work.DSM5c.Lp.cechIdx (q := q) i))
          (p : W)
          (fun i => by
            letI := Work.DSM5c.chartDAlg Q hθ t tr htr0 htr j₀ e
              (Work.DSM5c.Lp.cechIdx (q := q) i).unop.unop
            exact Submodule.ker_mkQ (Work.DSM5c.Lp.chartDpTop Q hθ t tr htr0 htr j₀ e
              (Work.DSM5c.Lp.cechIdx (q := q) i).unop.unop))]
    exact key x

/-- **The M5c node, reduced to the *pinned* mod-`p`-chart input** (`NOTES.md` §22.2): the frozen
conclusion of `DSMap.Mix2.area_M5c` (at an arbitrary universe), from

* the hypothesis `hj₀ : t j₀ = QW.ϖ 0 ^ e` of the frozen node — which is *needed*, since it is what
  makes the chart map `η` of `Work.DSM5c.Eta.exists_chartMapU` (with its unit property
  `η_S (algebraMap w) = w • 1`) exist, and

* the characteristic-`p` input on the mod-`p` chart complex, *pinned* by the `he`-equation:
  `hL η hη` supplies `eL` with `AlmostAcyc QW.ϖ (span{p}) (Č chartLQ) eL` and
  `(Č chartLQEta).f 0 ((Č η).f 0 ((chartCoaugW t) w)) = eL.hom w` — which is exactly
  `Work.DSM5c.Lp.almostAcyc_chartLQU` instantiated at `η` and `hη`.

Suggested proof: obtain `hθ := Work.DSM5c.G2.U.surjective_fontaineTheta_of_perfectoidData QW`, then
`obtain ⟨η, hη⟩ := Work.DSM5c.Eta.exists_chartMapU … hj₀`,
`obtain ⟨eL, hAcyc, he⟩ := hL η hη`, `refine ⟨Work.DSM5c.chartD … , η, fun m => ?_⟩`, and finish with
`Work.DSM5c.almostAcyc_span_pow` applied to
`Work.DSM5c.Devissage.almostAcyc_of_surjective_kernel_v2 QW.ϖ _ _ (Č chartLQEta) hsurj hker eK eL he hAcyc`
(where `eK := chartCoaugW t ≫ (Č η).f 0`, `hsurj`/`hker` come from
`Work.DSM5c.Lp.chartDToLp_existsU`'s witness `chartLQEta` and its `ker_Pi_map_span` helpers), the
cocycle condition from `Work.DSM5c.Cech.chartCoaug_isCocycleU`, and `hreg` from
`Work.DSM5c.G2.isSMulRegular_chartUntiltU` together with `IsSMulRegular.pi`. -/
theorem area_M5c_of_LpInput {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W]
    [Fact ¬IsUnit (p : W)] [IsAdicComplete (Ideal.span {(p : W)}) W]
    (QW : DSMap.PerfectoidData p W) {ι : Type u} [Finite ι] [DecidableEq ι]
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (hj₀ : t j₀ = QW.ϖ 0 ^ e)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (hL : ∀ (η : DSMap.Mix2.chartPresheaf t ⟶
        Work.DSM5c.chartD (p := p) (W := W) QW hθ t tr htr0 htr j₀ e),
      (∀ (S : (Finset ι)ᵒᵖᵒᵖ) (w : W),
        letI := Work.DSM5c.chartDAlg (p := p) (W := W) QW hθ t tr htr0 htr j₀ e S.unop.unop
        η.app S (algebraMap W (DSMap.Mix2.chartRing t S.unop.unop) w) =
          w • (1 : Work.DSM5c.untiltOf (p := p) (W := W)
            (Work.DSM5c.tiltChart QW t tr htr0 htr j₀ e S.unop.unop)
            (Work.DSM5c.chartPhi QW t tr htr0 htr j₀ e S.unop.unop))) →
      ∃ eL : ModuleCat.of W W ⟶ ((cechComplexFunctor (chartIdx ι)).obj
          (Work.DSM5c.Lp.chartLQ (p := p) (W := W) QW hθ t tr htr0 htr j₀ e)).X 0,
        DSMap.Mix2.AlmostAcyc QW.ϖ (Ideal.span {(p : W)})
          ((cechComplexFunctor (chartIdx ι)).obj
            (Work.DSM5c.Lp.chartLQ (p := p) (W := W) QW hθ t tr htr0 htr j₀ e)) eL ∧
        (∀ w : W,
          (((cechComplexFunctor (chartIdx ι)).map
              (Work.DSM5c.Lp.chartLQEta (p := p) (W := W) QW hθ t tr htr0 htr j₀ e)).f 0).hom
            (((cechComplexFunctor (chartIdx ι)).map η).f 0
              ((chartCoaugW t).hom w)) = eL.hom w)) :
    ∃ (Dp : (Finset ι)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} W) (η : DSMap.Mix2.chartPresheaf t ⟶ Dp),
      ∀ m, DSMap.Mix2.AlmostAcyc QW.ϖ (Ideal.span {(p : W) ^ m})
        ((cechComplexFunctor (DSMap.Mix2.chartIdx ι)).obj Dp)
        (DSMap.Mix2.chartCoaugW t ≫
          ((cechComplexFunctor (DSMap.Mix2.chartIdx ι)).map η).f 0) := by
  -- the chart map `η` of gap G1, with its unit property
  obtain ⟨η, hη⟩ :=
    Work.DSM5c.Eta.exists_chartMapU (p := p) (W := W) QW hθ t tr htr0 htr j₀ e hj₀
  -- the pinned mod-`p` input on the chart complex `Č (Lp)`
  obtain ⟨eL, hLacyc, heL⟩ := hL η hη
  refine ⟨Work.DSM5c.chartD (p := p) (W := W) QW hθ t tr htr0 htr j₀ e, η, fun m => ?_⟩
  -- the surjectivity/kernel pair of the mod-`p` comparison `Č (chartD) ⟶ Č (chartLQ)`
  have hsk := cechChartLQEta_surj_ker (p := p) (W := W) QW hθ t tr htr0 htr j₀ e
  -- the coaugmentation is a `0`-cocycle (the `hη`-hypothesis is needed and used here)
  have he : ∀ w : W,
      (((cechComplexFunctor (chartIdx ι)).obj
          (Work.DSM5c.chartD (p := p) (W := W) QW hθ t tr htr0 htr j₀ e)).d 0 1).hom
        ((DSMap.Mix2.chartCoaugW t ≫
          ((cechComplexFunctor (chartIdx ι)).map η).f 0).hom w) = 0 :=
    fun w => Work.DSM5c.Cech.chartCoaug_isCocycleU QW hθ t tr htr0 htr j₀ e η hη w
  -- `p`-torsion-freeness of the terms of `Č (chartD)`
  have hreg : ∀ q, IsSMulRegular
      (((cechComplexFunctor (chartIdx ι)).obj
        (Work.DSM5c.chartD (p := p) (W := W) QW hθ t tr htr0 htr j₀ e)).X q) (p : W) :=
    fun q => isSMulRegular_chartDCechTerm (p := p) (W := W) QW hθ t tr htr0 htr j₀ e hj₀ q
  -- the mod-`p` statement on `Č (chartD)`, by dévissage through `Č (chartD) ⟶ Č (chartLQ)`
  have hK : AlmostAcyc QW.ϖ (Ideal.span {(p : W)})
      ((cechComplexFunctor (chartIdx ι)).obj
        (Work.DSM5c.chartD (p := p) (W := W) QW hθ t tr htr0 htr j₀ e))
      (DSMap.Mix2.chartCoaugW t ≫ ((cechComplexFunctor (chartIdx ι)).map η).f 0) :=
    Work.DSM5c.Devissage.almostAcyc_of_surjective_kernel_v2 (p := p) (W := W) QW.ϖ _ _
      ((cechComplexFunctor (chartIdx ι)).map
        (Work.DSM5c.Lp.chartLQEta (p := p) (W := W) QW hθ t tr htr0 htr j₀ e))
      hsk.1 hsk.2 _ eL heL hLacyc
  -- dévissage `p ↦ p ^ m`
  exact Work.DSM5c.almostAcyc_span_pow (p := p) (ϖ := QW.ϖ) (W := W) QW.root _ _ he hK hreg m

end Work.DSM5c.Main
