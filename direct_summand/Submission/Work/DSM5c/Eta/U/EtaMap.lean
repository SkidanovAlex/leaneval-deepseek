import Mathlib
import Submission.Work.DSM5c.Eta.U.Setup
import Submission.Work.DSM5c.Eta.U.GLocFracU
import Submission.Work.DSM5c.Eta.U.ChartRingGLocRange
import Submission.Work.DSM5c.Eta.U.ExistsAlgHomOfLeRange
import Submission.Work.DSM5c.Eta.U.ChartDMapTeich
import Submission.Work.DSM5c.Eta.U.LocResFracT
import Submission.Work.DSM5c.Eta.U.TiltChartResFracU
import Submission.Work.DSM5c.ChartFunctor
import Submission.Work.DSM5c.ChartPresheafLaws

universe a

/-!
# DSM5c / Eta — the chart map `η : chartPresheaf t ⟶ chartD` (gap G1) from the crux

This file assembles the chart map `η` of the M5c node (`DSMap.Mix2.area_M5c`, gap G1 of
`Submission/Work/DSM5c/NOTES.md` §20.3) from the single remaining input:

* `Work.DSM5c.Eta.U.IsSMulRegular (DS … S) (vS … S)` for every `S` — i.e. injectivity of the
  localisation map `Work.DSM5c.Eta.U.locD … S : D_S →+* D_S[1/v_S]` (the "chart ring sits inside the
  perfectoid chart" input); its consequence `∀ S, Function.Injective (locD … S)` is the hypothesis
  of the main theorem below.

Given that, each `η_S : chartRing t S →+* D_S` is produced by the descent
`Work.DSM5c.Eta.U.exists_algHom_of_le_range` from the generator dictionary
`Work.DSM5c.Eta.U.gLoc_fracU` and the range containment `Work.DSM5c.Eta.U.chartRing_gLoc_range`, and the
naturality in `S` is the generator computation
`t_k/t_i ↦ ♯(u_k/u_i)` together with `Work.DSM5c.Eta.U.chartDMap_teich`,
`Work.DSM5c.Eta.U.locRes_fracT` and `Work.DSM5c.Eta.U.tiltChartRes_fracU`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.DSM5c.Eta.U

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

section Setup

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
  [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type a} [DecidableEq ι]
  (Q : DSMap.PerfectoidData p W)
  (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
  (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
  (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)

/-- **The restriction map of the honest chart rings** `chartRing t S →+* chartRing t T` for
`S ⊆ T`: the localisation map `locRes t h` restricted to the chart rings.  This is the ring-level
form of the morphism data of the presheaf `chartPresheaf t`. -/
noncomputable def chartRingMap {S T : Finset ι} (h : S ⊆ T) :
    DSMap.Mix2.chartRing t S →ₐ[W] DSMap.Mix2.chartRing t T :=
  ((locRes t h).comp (DSMap.Mix2.chartRing t S).val).codRestrict (DSMap.Mix2.chartRing t T)
    (fun x => DSMap.Mix2.chartRing_map_le t h ⟨x.1, x.2, rfl⟩)

@[simp] theorem chartRingMap_coe {S T : Finset ι} (h : S ⊆ T) (x : DSMap.Mix2.chartRing t S) :
    (chartRingMap t h x : Localization.Away (tS t T)) = locRes t h x.1 :=
  rfl

/-- **A chart generator is the honest fraction.** -/
theorem fracT_generator (S : Finset ι) {i : ι} (hi : i ∈ S) (k : ι) :
    (⟨fracT t S i k hi, Algebra.subset_adjoin ⟨i, hi, k, fracT_spec t S i k hi⟩⟩ :
      DSMap.Mix2.chartRing t S) =
      ⟨fracT t S i k hi, Algebra.subset_adjoin ⟨i, hi, k, fracT_spec t S i k hi⟩⟩ := rfl

/-- **The single-chart descent.**  If the localisation map `locD S : D_S →+* D_S[1/v_S]` is
injective, then the generator assignment `t_k/t_i ↦ ♯(u_k/u_i)` extends to a `W`-algebra map
`η_S : chartRing t S →+* D_S`, characterised by `locD S ∘ η_S = gLoc S`. -/
private theorem exists_etaAux (hj₀ : t j₀ = Q.ϖ 0 ^ e)
    (hInj : ∀ S : Finset ι, Function.Injective (locD Q hθ t tr htr0 htr j₀ e S)) (S : Finset ι) :
    letI := DSalg Q hθ t tr htr0 htr j₀ e S
    ∃ f : DSMap.Mix2.chartRing t S →ₐ[W] DS Q t tr htr0 htr j₀ e S,
      ∀ x : DSMap.Mix2.chartRing t S,
        locD Q hθ t tr htr0 htr j₀ e S (f x) = gLoc Q hθ t tr htr0 htr j₀ e S x.1 := by
  letI := DSalg Q hθ t tr htr0 htr j₀ e S
  letI := DSlocAlg Q hθ t tr htr0 htr j₀ e S
  obtain ⟨f, hf⟩ := exists_algHom_of_le_range (W := W)
    (B := Localization.Away (tS t S))
    (C := DS Q t tr htr0 htr j₀ e S)
    (C' := DSloc Q hθ t tr htr0 htr j₀ e S)
    (ι := ({ toRingHom := locD Q hθ t tr htr0 htr j₀ e S, commutes' := fun w => rfl } :
      DS Q t tr htr0 htr j₀ e S →ₐ[W] DSloc Q hθ t tr htr0 htr j₀ e S))
    (hInj S)
    (g := ({ toRingHom := gLoc Q hθ t tr htr0 htr j₀ e S, commutes' := fun w => gLoc_algebraMap Q hθ t tr htr0 htr j₀ e S w } :
      Localization.Away (tS t S) →ₐ[W] DSloc Q hθ t tr htr0 htr j₀ e S))
    (G := chartGens t S) (by
      intro x hx
      obtain ⟨d, hd⟩ := chartRing_gLoc_range Q hθ t tr htr0 htr j₀ e hj₀ S x
        (Algebra.subset_adjoin hx)
      exact ⟨d, hd⟩)
  exact ⟨f, fun x => hf x⟩

/-- **The chart map on one chart.** -/
noncomputable def etaAlg (hj₀ : t j₀ = Q.ϖ 0 ^ e)
    (hInj : ∀ S : Finset ι, Function.Injective (locD Q hθ t tr htr0 htr j₀ e S)) (S : Finset ι) :
    letI := DSalg Q hθ t tr htr0 htr j₀ e S
    DSMap.Mix2.chartRing t S →ₐ[W] DS Q t tr htr0 htr j₀ e S :=
  Classical.choose (exists_etaAux Q hθ t tr htr0 htr j₀ e hj₀ hInj S)

/-- **The defining property of `etaAlg`**: it is a lift of the localisation map `gLoc S` along
`locD S` on the honest chart ring. -/
theorem etaAlg_spec (hj₀ : t j₀ = Q.ϖ 0 ^ e)
    (hInj : ∀ S : Finset ι, Function.Injective (locD Q hθ t tr htr0 htr j₀ e S)) (S : Finset ι)
    (x : DSMap.Mix2.chartRing t S) :
    locD Q hθ t tr htr0 htr j₀ e S (etaAlg Q hθ t tr htr0 htr j₀ e hj₀ hInj S x)
      = gLoc Q hθ t tr htr0 htr j₀ e S x.1 :=
  Classical.choose_spec (exists_etaAux Q hθ t tr htr0 htr j₀ e hj₀ hInj S) x

/-- **`η_S` on the image of `W`**: the `W`-algebra structure of the chart untilt. -/
theorem etaAlg_algebraMap (hj₀ : t j₀ = Q.ϖ 0 ^ e)
    (hInj : ∀ S : Finset ι, Function.Injective (locD Q hθ t tr htr0 htr j₀ e S)) (S : Finset ι)
    (w : W) :
    letI := DSalg Q hθ t tr htr0 htr j₀ e S
    etaAlg Q hθ t tr htr0 htr j₀ e hj₀ hInj S (algebraMap W (DSMap.Mix2.chartRing t S) w)
      = untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) w := by
  letI := DSalg Q hθ t tr htr0 htr j₀ e S
  refine hInj S ?_
  rw [etaAlg_spec Q hθ t tr htr0 htr j₀ e hj₀ hInj S
    (algebraMap W (DSMap.Mix2.chartRing t S) w)]
  exact gLoc_algebraMap Q hθ t tr htr0 htr j₀ e S w

/-- **`η_S` on the chart generators** (the generator dictionary): the honest fraction `t_k/t_i`
maps to the Teichmüller image of the tilted fraction `u_k/u_i`. -/
theorem etaAlg_fracT (hj₀ : t j₀ = Q.ϖ 0 ^ e)
    (hInj : ∀ S : Finset ι, Function.Injective (locD Q hθ t tr htr0 htr j₀ e S)) (S : Finset ι)
    {i : ι} (hi : i ∈ S) (k : ι) :
    letI := DSalg Q hθ t tr htr0 htr j₀ e S
    etaAlg Q hθ t tr htr0 htr j₀ e hj₀ hInj S
        (⟨fracT t S i k hi, Algebra.subset_adjoin ⟨i, hi, k, fracT_spec t S i k hi⟩⟩ :
          DSMap.Mix2.chartRing t S)
      = teich Q t tr htr0 htr j₀ e S (fracU Q t tr htr0 htr j₀ e S i k hi) := by
  letI := DSalg Q hθ t tr htr0 htr j₀ e S
  refine hInj S ?_
  rw [etaAlg_spec Q hθ t tr htr0 htr j₀ e hj₀ hInj S
    (⟨fracT t S i k hi, Algebra.subset_adjoin ⟨i, hi, k, fracT_spec t S i k hi⟩⟩ :
      DSMap.Mix2.chartRing t S)]
  exact gLoc_fracU Q hθ t tr htr0 htr j₀ e hj₀ S hi k

/-- **The generator computation of the naturality square**: the two composites
`chartRing t S → D_S → D_T` and `chartRing t S → chartRing t T → D_T` agree on the chart
generators, i.e. on the honest fractions `t_k/t_i`. -/
theorem etaAlg_fracT_natural (hj₀ : t j₀ = Q.ϖ 0 ^ e)
    (hInj : ∀ S : Finset ι, Function.Injective (locD Q hθ t tr htr0 htr j₀ e S))
    {S T : Finset ι} (h : S ⊆ T) {i : ι} (hi : i ∈ S) (k : ι) :
    letI := DSalg Q hθ t tr htr0 htr j₀ e S
    letI := DSalg Q hθ t tr htr0 htr j₀ e T
    chartDMap Q hθ t tr htr0 htr j₀ e h
        (etaAlg Q hθ t tr htr0 htr j₀ e hj₀ hInj S
          (⟨fracT t S i k hi, Algebra.subset_adjoin ⟨i, hi, k, fracT_spec t S i k hi⟩⟩ :
            DSMap.Mix2.chartRing t S))
      = etaAlg Q hθ t tr htr0 htr j₀ e hj₀ hInj T
          (chartRingMap t h
            (⟨fracT t S i k hi, Algebra.subset_adjoin ⟨i, hi, k, fracT_spec t S i k hi⟩⟩ :
              DSMap.Mix2.chartRing t S)) := by
  letI := DSalg Q hθ t tr htr0 htr j₀ e S
  letI := DSalg Q hθ t tr htr0 htr j₀ e T
  have hx : chartRingMap t h
      (⟨fracT t S i k hi, Algebra.subset_adjoin ⟨i, hi, k, fracT_spec t S i k hi⟩⟩ :
        DSMap.Mix2.chartRing t S)
      = (⟨fracT t T i k (h hi), Algebra.subset_adjoin ⟨i, h hi, k, fracT_spec t T i k (h hi)⟩⟩ :
        DSMap.Mix2.chartRing t T) := by
    refine Subtype.ext ?_
    rw [chartRingMap_coe]
    exact locRes_fracT t h hi k
  rw [etaAlg_fracT Q hθ t tr htr0 htr j₀ e hj₀ hInj S hi k, chartDMap_teich, hx]
  exact (congrArg (teich Q t tr htr0 htr j₀ e T)
    (tiltChartRes_fracU Q t tr htr0 htr j₀ e h hi k)).trans
    (etaAlg_fracT Q hθ t tr htr0 htr j₀ e hj₀ hInj T (h hi) k).symm

/-- **`chartDMap` promoted to a `W`-algebra map**. -/
noncomputable def chartDAlgHom {S T : Finset ι} (h : S ⊆ T) :
    letI := DSalg Q hθ t tr htr0 htr j₀ e S
    letI := DSalg Q hθ t tr htr0 htr j₀ e T
    DS Q t tr htr0 htr j₀ e S →ₐ[W] DS Q t tr htr0 htr j₀ e T := by
  letI := DSalg Q hθ t tr htr0 htr j₀ e S
  letI := DSalg Q hθ t tr htr0 htr j₀ e T
  exact
    { toRingHom := untiltOf.map (chartPhi Q t tr htr0 htr j₀ e S)
        (chartPhi Q t tr htr0 htr j₀ e T) (tiltChartRes Q t tr htr0 htr j₀ e h)
        (RingHom.ext fun r => tiltChartRes_algebraMap Q t tr htr0 htr j₀ e h r),
      commutes' := fun w => untiltOf.map_algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S)
        (chartPhi Q t tr htr0 htr j₀ e T) (tiltChartRes Q t tr htr0 htr j₀ e h)
        (RingHom.ext fun r => tiltChartRes_algebraMap Q t tr htr0 htr j₀ e h r) w }

/-- The `chartDMap`-`chartDAlgHom` dictionary. -/
theorem chartDMap_eq_chartDAlgHom {S T : Finset ι} (h : S ⊆ T)
    (x : DS Q t tr htr0 htr j₀ e S) :
    chartDMap Q hθ t tr htr0 htr j₀ e h x = chartDAlgHom Q hθ t tr htr0 htr j₀ e h x := rfl

/-- **Naturality of the single-chart maps `η_S` in `S`.**  For `S ⊆ T` the square
`chartRing t S → chartRing t T → D_T` and `chartRing t S → D_S → D_T` commute.  Both composites are
`W`-algebra maps out of the chart ring, which is generated by the chart fractions `t_k/t_i`, where
the claim is `Work.DSM5c.Eta.U.etaAlg_fracT_natural`. -/
theorem etaAlg_natural (hj₀ : t j₀ = Q.ϖ 0 ^ e)
    (hInj : ∀ S : Finset ι, Function.Injective (locD Q hθ t tr htr0 htr j₀ e S))
    {S T : Finset ι} (h : S ⊆ T) (x : DSMap.Mix2.chartRing t S) :
    chartDMap Q hθ t tr htr0 htr j₀ e h
        (etaAlg Q hθ t tr htr0 htr j₀ e hj₀ hInj S x)
      = etaAlg Q hθ t tr htr0 htr j₀ e hj₀ hInj T (chartRingMap t h x) := by
  letI := DSalg Q hθ t tr htr0 htr j₀ e S
  letI := DSalg Q hθ t tr htr0 htr j₀ e T
  rw [chartDMap_eq_chartDAlgHom]
  have key : ∀ (y : Localization.Away (tS t S))
      (hy : y ∈ Algebra.adjoin W (chartGens t S)),
      chartDAlgHom Q hθ t tr htr0 htr j₀ e h
          (etaAlg Q hθ t tr htr0 htr j₀ e hj₀ hInj S ⟨y, hy⟩)
        = etaAlg Q hθ t tr htr0 htr j₀ e hj₀ hInj T (chartRingMap t h ⟨y, hy⟩) := by
    intro y hy
    refine Algebra.adjoin_induction (p := fun y hy =>
        chartDAlgHom Q hθ t tr htr0 htr j₀ e h
            (etaAlg Q hθ t tr htr0 htr j₀ e hj₀ hInj S ⟨y, hy⟩)
          = etaAlg Q hθ t tr htr0 htr j₀ e hj₀ hInj T (chartRingMap t h ⟨y, hy⟩))
      ?_ ?_ ?_ ?_ hy
    · -- the chart generators
      intro z hz
      have hzmem : z ∈ chartGens t S := hz
      obtain ⟨i, hi, k, hze⟩ := hzmem
      have hzeq : z = fracT t S i k hi := by
        have hu : IsUnit (algebraMap W (Localization.Away (tS t S)) (t i)) :=
          ⟨unitT t S i hi, unitT_spec t S i hi⟩
        exact IsUnit.mul_right_cancel hu (hze.trans (fracT_spec t S i k hi).symm)
      have hsub :
          (⟨z, Algebra.subset_adjoin hz⟩ : DSMap.Mix2.chartRing t S)
            = (⟨fracT t S i k hi,
                Algebra.subset_adjoin ⟨i, hi, k, fracT_spec t S i k hi⟩⟩ :
              DSMap.Mix2.chartRing t S) := Subtype.ext hzeq
      rw [hsub]
      exact etaAlg_fracT_natural Q hθ t tr htr0 htr j₀ e hj₀ hInj h hi k
    · -- the image of `W`
      intro r
      rw [show (⟨algebraMap W (Localization.Away (tS t S)) r, _⟩ :
            ↥(DSMap.Mix2.chartRing t S))
          = algebraMap W ↥(DSMap.Mix2.chartRing t S) r from Subtype.ext rfl,
        etaAlg_algebraMap Q hθ t tr htr0 htr j₀ e hj₀ hInj S r,
        AlgHom.commutes (chartRingMap t h) r,
        etaAlg_algebraMap Q hθ t tr htr0 htr j₀ e hj₀ hInj T r]
      exact AlgHom.commutes (chartDAlgHom Q hθ t tr htr0 htr j₀ e h) r
    · -- sums
      intro a b ha hb iha ihb
      rw [show (⟨a + b, _⟩ : ↥(DSMap.Mix2.chartRing t S))
          = (⟨a, ha⟩ : ↥(DSMap.Mix2.chartRing t S)) + ⟨b, hb⟩ from rfl,
        map_add (etaAlg Q hθ t tr htr0 htr j₀ e hj₀ hInj S),
        map_add (chartDAlgHom Q hθ t tr htr0 htr j₀ e h),
        map_add (chartRingMap t h),
        map_add (etaAlg Q hθ t tr htr0 htr j₀ e hj₀ hInj T), iha, ihb]
    · -- products
      intro a b ha hb iha ihb
      rw [show (⟨a * b, _⟩ : ↥(DSMap.Mix2.chartRing t S))
          = (⟨a, ha⟩ : ↥(DSMap.Mix2.chartRing t S)) * ⟨b, hb⟩ from rfl,
        map_mul (etaAlg Q hθ t tr htr0 htr j₀ e hj₀ hInj S),
        map_mul (chartDAlgHom Q hθ t tr htr0 htr j₀ e h),
        map_mul (chartRingMap t h),
        map_mul (etaAlg Q hθ t tr htr0 htr j₀ e hj₀ hInj T), iha, ihb]
  exact key x.1 x.2

/-- **The restriction map on elements of the chart presheaf**: the presheaf map of
`chartPresheaf t` is the ring map `chartRingMap t h`. -/
theorem chartPresheaf_map_apply {S T : (Finset ι)ᵒᵖᵒᵖ} (f : S ⟶ T)
    (x : (DSMap.Mix2.chartPresheaf t).obj S) :
    (DSMap.Mix2.chartPresheaf t).map f x
      = chartRingMap t (leOfHom f.unop.unop) x :=
  rfl

/-- **The chart map on a single chart, as a `W`-linear map.** -/
noncomputable def etaLin (hj₀ : t j₀ = Q.ϖ 0 ^ e)
    (hInj : ∀ S : Finset ι, Function.Injective (locD Q hθ t tr htr0 htr j₀ e S)) (S : Finset ι) :
    letI := DSalg Q hθ t tr htr0 htr j₀ e S
    DSMap.Mix2.chartRing t S →ₗ[W] DS Q t tr htr0 htr j₀ e S := by
  letI := DSalg Q hθ t tr htr0 htr j₀ e S
  exact (etaAlg Q hθ t tr htr0 htr j₀ e hj₀ hInj S).toLinearMap

/-- The underlying function of `etaLin` is `etaAlg`. -/
theorem etaLin_apply (hj₀ : t j₀ = Q.ϖ 0 ^ e)
    (hInj : ∀ S : Finset ι, Function.Injective (locD Q hθ t tr htr0 htr j₀ e S)) (S : Finset ι)
    (x : DSMap.Mix2.chartRing t S) :
    etaLin Q hθ t tr htr0 htr j₀ e hj₀ hInj S x
      = etaAlg Q hθ t tr htr0 htr j₀ e hj₀ hInj S x :=
  rfl

/-- **The chart map `η` of the M5c node**, given the regularity input
`∀ S, Function.Injective (locD … S)` (which is `Work.DSM5c.Eta.U.isSMulRegular_teich` for the
generator `vS S`). -/
noncomputable def etaNat (hj₀ : t j₀ = Q.ϖ 0 ^ e)
    (hInj : ∀ S : Finset ι, Function.Injective (locD Q hθ t tr htr0 htr j₀ e S)) :
    DSMap.Mix2.chartPresheaf t ⟶ Work.DSM5c.chartD Q hθ t tr htr0 htr j₀ e where
  app S := by
    letI := DSalg Q hθ t tr htr0 htr j₀ e S.unop.unop
    exact ModuleCat.ofHom (etaLin Q hθ t tr htr0 htr j₀ e hj₀ hInj S.unop.unop)
  naturality {S T} f := by
    letI := DSalg Q hθ t tr htr0 htr j₀ e S.unop.unop
    letI := DSalg Q hθ t tr htr0 htr j₀ e T.unop.unop
    ext x
    show etaAlg Q hθ t tr htr0 htr j₀ e hj₀ hInj T.unop.unop
        ((DSMap.Mix2.chartPresheaf t).map f x)
      = chartDMap Q hθ t tr htr0 htr j₀ e (leOfHom f.unop.unop)
          (etaAlg Q hθ t tr htr0 htr j₀ e hj₀ hInj S.unop.unop x)
    rw [chartPresheaf_map_apply]
    exact (etaAlg_natural Q hθ t tr htr0 htr j₀ e hj₀ hInj (leOfHom f.unop.unop) x).symm

/-- The components of `etaNat` are `etaAlg`. -/
theorem etaNat_app_apply (hj₀ : t j₀ = Q.ϖ 0 ^ e)
    (hInj : ∀ S : Finset ι, Function.Injective (locD Q hθ t tr htr0 htr j₀ e S))
    (S : (Finset ι)ᵒᵖᵒᵖ) (x : DSMap.Mix2.chartRing t S.unop.unop) :
    (etaNat Q hθ t tr htr0 htr j₀ e hj₀ hInj).app S x
      = etaAlg Q hθ t tr htr0 htr j₀ e hj₀ hInj S.unop.unop x := by
  letI := DSalg Q hθ t tr htr0 htr j₀ e S.unop.unop
  rfl

/-- `w • 1` in a chart untilt is the image of `w` under the `W`-algebra structure. -/
theorem smul_one_eq_algebraMap (S : (Finset ι)ᵒᵖᵒᵖ) (w : W) :
    letI := DSalg Q hθ t tr htr0 htr j₀ e S.unop.unop
    w • (1 : DS Q t tr htr0 htr j₀ e S.unop.unop)
      = untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S.unop.unop) w := by
  letI := DSalg Q hθ t tr htr0 htr j₀ e S.unop.unop
  rw [Algebra.smul_def w (1 : DS Q t tr htr0 htr j₀ e S.unop.unop), mul_one]
  rfl

/-- **The defining property of the chart map `η` on the unit of `W`**: it is the `W`-algebra
structure of the chart untilt, so that `η_S (algebraMap W _ w) = w • 1`. -/
theorem etaNat_app_algebraMap (hj₀ : t j₀ = Q.ϖ 0 ^ e)
    (hInj : ∀ S : Finset ι, Function.Injective (locD Q hθ t tr htr0 htr j₀ e S))
    (S : (Finset ι)ᵒᵖᵒᵖ) (w : W) :
    letI := Work.DSM5c.chartDAlg Q hθ t tr htr0 htr j₀ e S.unop.unop
    (etaNat Q hθ t tr htr0 htr j₀ e hj₀ hInj).app S
        (algebraMap W (DSMap.Mix2.chartRing t S.unop.unop) w)
      = w • (1 : DS Q t tr htr0 htr j₀ e S.unop.unop) := by
  letI := DSalg Q hθ t tr htr0 htr j₀ e S.unop.unop
  rw [etaNat_app_apply, etaAlg_algebraMap]
  exact (smul_one_eq_algebraMap Q hθ t tr htr0 htr j₀ e S w).symm

end Setup

end Work.DSM5c.Eta.U