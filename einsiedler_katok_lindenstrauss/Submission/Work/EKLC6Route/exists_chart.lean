import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLComp.X3Background
import Submission.Work.EKLC6Core.thin_boundary_ae
import Submission.Work.EKLC6Core.InjRadius
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLComp.prove_X3
import Submission.Work.EKLC6Core.contraction_rate_uminus
import Submission.Work.EKLC6Core.mem_uminus_of_entry_form
import Submission.Work.EKLContract.Lemmas.isHoro_Upar
import Submission.Work.EKLC6Route.exists_uminus_mul_VtSet
import Submission.Work.EKLC6Route.VtSet_subgroup_unique
import Submission.Work.EKLC6Route.exists_coord_maps
import Submission.Work.EKLC6Route.exists_good_radius


set_option maxHeartbeats 2000000

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract Work.EKLC6Core

namespace Work.EKLC6Route

/-!
# `Work.EKLC6Route.exists_chart` — a `G⁰G⁺(t)`-chart exists for every probability measure

This file proves the chart-existence lemma `L2a` of `EKLComp/C6GEOM_ROUTE_LEAD.md` §3.1: for
every probability measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` there are `z₀, r, ρ, δ > 0`
(`δ ≤ 1/100`, `4000 r ≤ δ`, `4000 ρ ≤ δ`) and *Borel* maps `uc, θ : X₃ → SL₃(ℝ)` such that

* `uc ((u * k) • z₀) = u` and `θ ((u * k) • z₀) = k` for `u ∈ Uball (Uminus t) (2r)` and
  `k ∈ VtSet t ∩ V (2ρ)` (`Chart.coord`),
* the action map `g ↦ g • z₀` is injective on `V δ` at the points `(u * k) • z₀` (`Chart.inj`),
* `μ (chartSet t z₀ uc θ r ρ) > 0` (`Chart.pos`),
* the `U`-shell `|dev (uc x) - r| ≤ ε` has measure `≤ c ε` (`Chart.thin`, Pisa 7.27).

## Structure of the proof

* `z₀` is a point all of whose neighbourhoods have positive `μ`-measure (the support of `μ`).
* `δ` is chosen below `1/100`, below the big-cell threshold `δ₀` of
  `Work.EKLC6Route.exists_uminus_mul_VtSet` and below `injCap z₀ / 16`; then
  `ρ := δ/8000`, `A := δ/4000 = 2ρ`, `r₀ := δ/16000` and the good radius `r ∈ (r₀, 2r₀)` is
  chosen with `Work.EKLC6Route.exists_good_radius` so that the monotone function
  `s ↦ μ {x : uc x ∈ Uball (Uminus t) s}` has a linear symmetric increment at `r`.
* `uc, θ` are the Borel coordinates produced by `Work.EKLC6Route.exists_coord_maps`, whose
  injectivity hypothesis is `smul_mul_inj_aux` below: two elements of the closed box
  `Ucl (Uminus t) A × (VtSet t ∩ Ucl ⊤ A)` giving the same point of `X₃` have the same
  coordinates, by `Work.EKLC6Core.InjAt` and the uniqueness half of
  `Work.EKLC6Route.VtSet_subgroup_unique`.
* `Chart.pos`: the big-cell decomposition writes every `g ∈ V δ₁` (`δ₁ := min r ρ / 40`) as
  `u k` with `u ∈ Uball (Uminus t) r`, `k ∈ VtSet t ∩ V ρ`, so `V δ₁ • z₀ ⊆ chartSet t z₀ uc θ r ρ`,
  and `V δ₁ • z₀` is a neighbourhood of `z₀`.
* `Chart.thin`: the shell `{x ∈ chartSet (2r, ρ) : |dev (uc x) - r| ≤ ε}` is contained in
  `𝒜 (r + 2ε) \ 𝒜 (r - 2ε)` with `𝒜 s := chartSet t z₀ uc θ s ρ` (the strict inequality
  `dev < r + 2ε` of `𝒜` absorbs the closed condition), so its measure is at most
  `ofReal (F (r + 2ε) - F (r - 2ε)) ≤ ofReal (2 c ε)`.
-/

/-! ## Helper lemmas of my own -/

theorem dev_lt_iff_aux (g : Work.EKLContract.SL3) (s : ℝ) :
    dev g < s ↔ ∀ i j : Fin 3,
      |toMat g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < s := by
  rw [dev, Finset.sup'_lt_iff]
  constructor
  · intro h i j; exact h (i, j) (Finset.mem_univ _)
  · intro h p _; exact h p.1 p.2

theorem dev_le_iff_aux (g : Work.EKLContract.SL3) (s : ℝ) :
    dev g ≤ s ↔ ∀ i j : Fin 3,
      |toMat g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ s := by
  rw [dev, Finset.sup'_le_iff]
  constructor
  · intro h i j; exact h (i, j) (Finset.mem_univ _)
  · intro h p _; exact h p.1 p.2

theorem mem_Uball_iff_dev_aux {U : Subgroup Work.EKLContract.SL3} {s : ℝ}
    {g : Work.EKLContract.SL3} :
    g ∈ Work.EKLComp.Uball U s ↔ g ∈ U ∧ dev g < s := by
  rw [Work.EKLComp.Uball, dev_lt_iff_aux]
  exact Iff.rfl

theorem mem_Ucl_iff_dev_aux {U : Subgroup Work.EKLContract.SL3} {s : ℝ}
    {g : Work.EKLContract.SL3} :
    g ∈ Work.EKLComp.Ucl U s ↔ g ∈ U ∧ dev g ≤ s := by
  rw [Work.EKLComp.Ucl, dev_le_iff_aux]
  exact Iff.rfl

/-- `Uball U s ⊆ Ucl U s'` for `s ≤ s'`. -/
theorem Uball_subset_Ucl_aux {U : Subgroup Work.EKLContract.SL3} {s s' : ℝ} (h : s ≤ s') :
    Work.EKLComp.Uball U s ⊆ Work.EKLComp.Ucl U s' := by
  intro g hg
  rw [mem_Ucl_iff_dev_aux, mem_Uball_iff_dev_aux] at *
  exact ⟨hg.1, le_of_lt (lt_of_lt_of_le hg.2 h)⟩

/-- `V s ⊆ Ucl ⊤ s'` for `s ≤ s'`. -/
theorem V_subset_Ucl_top_aux {s s' : ℝ} (h : s ≤ s') :
    Work.EKLContract.V s ⊆ Work.EKLComp.Ucl (⊤ : Subgroup Work.EKLContract.SL3) s' := by
  intro g hg
  rw [mem_Ucl_iff_dev_aux]
  refine ⟨trivial, ?_⟩
  rw [dev_le_iff_aux]
  intro i j
  have h1 : |toMat g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < s := hg i j
  linarith

/-- `Ucl U s ⊆ V (2 * s)` for `0 < s`. -/
theorem Ucl_subset_V_aux {U : Subgroup Work.EKLContract.SL3} {s : ℝ} (hs : 0 < s) :
    Work.EKLComp.Ucl U s ⊆ Work.EKLContract.V (2 * s) := by
  intro g hg
  rw [Work.EKLComp.Ucl] at hg
  intro i j
  have h1 : |toMat g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ s := hg.2 i j
  linarith

theorem exists_forall_nhds_pos_aux {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] :
    ∃ z0 : Work.EKLContract.X3, ∀ s : Set Work.EKLContract.X3, s ∈ nhds z0 → 0 < μ s := by
  have hne : μ ≠ 0 := by
    intro h
    have h1 : μ Set.univ = 1 := MeasureTheory.measure_univ
    rw [h] at h1
    simp at h1
  obtain ⟨z0, hz0⟩ := MeasureTheory.Measure.nonempty_support (μ := μ) hne
  exact ⟨z0, fun s hs => (MeasureTheory.Measure.mem_support_iff_forall z0).mp hz0 s hs⟩

theorem chartSet_mono_aux {t : Fin 3 → ℝ} {z0 : Work.EKLContract.X3}
    {uc θ : Work.EKLContract.X3 → Work.EKLContract.SL3} {a a' b b' : ℝ}
    (ha : a ≤ a') (hb : b ≤ b') :
    chartSet t z0 uc θ a b ⊆ chartSet t z0 uc θ a' b' := by
  rintro x ⟨hu, hk, heq⟩
  refine ⟨Work.EKLComp.Uball_mono ha hu, ⟨hk.1, ?_⟩, heq⟩
  exact Work.Misiurewicz.V_mono hb hk.2

/-- Measurability of `chartSet`. -/
theorem measurableSet_chartSet_aux {t : Fin 3 → ℝ} {z0 : Work.EKLContract.X3}
    {uc θ : Work.EKLContract.X3 → Work.EKLContract.SL3} {a b : ℝ}
    (huc : Measurable uc) (hθ : Measurable θ) :
    MeasurableSet (chartSet t z0 uc θ a b) := by
  have hentry : ∀ i j : Fin 3, Measurable
      (fun g : Work.EKLContract.SL3 => toMat g i j) :=
    fun i j => (Work.EKLContract.Lemmas.continuous_toMat_entry i j).measurable
  have hUball : MeasurableSet (Work.EKLComp.Uball (Work.EKLC6Core.Uminus t) a) := by
    have hset : Work.EKLComp.Uball (Work.EKLC6Core.Uminus t) a =
        (Work.EKLC6Core.Uminus t : Set Work.EKLContract.SL3) ∩
          {g : Work.EKLContract.SL3 |
            ∀ i j : Fin 3, |toMat g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < a} := by
      ext g; exact Iff.rfl
    rw [hset]
    refine MeasurableSet.inter ((uminus_isHoro t).1.1.measurableSet) ?_
    have hinner : {g : Work.EKLContract.SL3 |
        ∀ i j : Fin 3, |toMat g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < a} =
        ⋂ (p : Fin 3 × Fin 3),
          {g : Work.EKLContract.SL3 |
            |toMat g p.1 p.2 - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2| < a} := by
      ext g
      simp only [Set.mem_iInter]
      exact ⟨fun h p => h p.1 p.2, fun h i j => h (i, j)⟩
    rw [hinner]
    exact MeasurableSet.iInter fun p =>
      ((hentry p.1 p.2).sub measurable_const).abs measurableSet_Iio
  have hV : MeasurableSet (Work.EKLC6Route.VtSet t ∩ Work.EKLContract.V b) := by
    have hVt : MeasurableSet (Work.EKLC6Route.VtSet t) := by
      have hset : Work.EKLC6Route.VtSet t =
          ⋂ (p : Fin 3 × Fin 3), ⋂ (_ : t p.1 < t p.2),
            {g : Work.EKLContract.SL3 | toMat g p.1 p.2 = 0} := by
        ext g
        simp only [Set.mem_iInter]
        exact ⟨fun h p hp => h p.1 p.2 hp, fun h i j hij => h (i, j) hij⟩
      rw [hset]
      refine MeasurableSet.iInter fun p => MeasurableSet.iInter fun _ => ?_
      exact measurableSet_eq_fun (hentry p.1 p.2) measurable_const
    have hVopen : MeasurableSet (Work.EKLContract.V b) := by
      have hset : Work.EKLContract.V b =
          ⋂ (p : Fin 3 × Fin 3),
            {g : Work.EKLContract.SL3 |
              |toMat g p.1 p.2 - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2| < b} := by
        ext g
        simp only [Set.mem_iInter]
        exact ⟨fun h p => h p.1 p.2, fun h i j => h (i, j)⟩
      rw [hset]
      exact MeasurableSet.iInter fun p =>
        ((hentry p.1 p.2).sub measurable_const).abs measurableSet_Iio
    exact hVt.inter hVopen
  have heq : MeasurableSet {x : Work.EKLContract.X3 | (uc x * θ x) • z0 = x} := by
    have hcont : Continuous (fun p : Work.EKLContract.SL3 × Work.EKLContract.SL3 =>
        (p.1 * p.2) • z0) := by fun_prop
    exact measurableSet_eq_fun (hcont.measurable.comp (huc.prodMk hθ)) measurable_id
  exact (huc hUball).inter ((hθ hV).inter heq)

/-- Injectivity of the chart map on a closed box. -/
theorem smul_mul_inj_aux {t : Fin 3 → ℝ} {z0 : Work.EKLContract.X3} {A : ℝ}
    (hA : 0 < A) (hA2 : A ≤ 1 / 2) (hAinj : 10 * A ≤ injCap z0 / 4) :
    ∀ u : Work.EKLContract.SL3, u ∈ Work.EKLComp.Ucl (Work.EKLC6Core.Uminus t) A →
      ∀ k : Work.EKLContract.SL3, k ∈ Work.EKLC6Route.VtSet t ∩
        Work.EKLComp.Ucl (⊤ : Subgroup Work.EKLContract.SL3) A →
      ∀ u' : Work.EKLContract.SL3, u' ∈ Work.EKLComp.Ucl (Work.EKLC6Core.Uminus t) A →
      ∀ k' : Work.EKLContract.SL3, k' ∈ Work.EKLC6Route.VtSet t ∩
        Work.EKLComp.Ucl (⊤ : Subgroup Work.EKLContract.SL3) A →
      (u * k) • z0 = (u' * k') • z0 → u = u' ∧ k = k' := by
  intro u hu k hk u' hu' k' hk' heq
  have hcap : 0 < injCap z0 := injCap_pos z0
  have huV : u ∈ Work.EKLContract.V (2 * A) := Ucl_subset_V_aux hA hu
  have hkV : k ∈ Work.EKLContract.V (2 * A) := Ucl_subset_V_aux hA hk.2
  have hu'V : u' ∈ Work.EKLContract.V (2 * A) := Ucl_subset_V_aux hA hu'
  have hk'V : k' ∈ Work.EKLContract.V (2 * A) := Ucl_subset_V_aux hA hk'.2
  have hσ0 : (0 : ℝ) ≤ 2 * A := by linarith
  have hukV : u * k ∈ Work.EKLContract.V (2 * A + 2 * A + 3 * (2 * A) * (2 * A)) :=
    V_mul_subset_V hσ0 hσ0 huV hkV
  have hu'k'V : u' * k' ∈ Work.EKLContract.V (2 * A + 2 * A + 3 * (2 * A) * (2 * A)) :=
    V_mul_subset_V hσ0 hσ0 hu'V hk'V
  have hσ : 2 * A + 2 * A + 3 * (2 * A) * (2 * A) ≤ injCap z0 / 4 := by
    nlinarith [hA, hA2, hAinj, hcap]
  have hinj : InjAt z0 (injCap z0 / 4) :=
    injAt_of_lt_injCap (by linarith) (by linarith)
  have hprod : u * k = u' * k' :=
    hinj (u * k) (u' * k') (Work.Misiurewicz.V_mono hσ hukV)
      (Work.Misiurewicz.V_mono hσ hu'k'V) heq
  obtain ⟨-, -, -, huniq⟩ := VtSet_subgroup_unique t
  exact huniq u u' k k' hu.1 hu'.1 hk.1 hk'.1 hprod


/-- **The chart exists**: every probability measure on `X₃ = SL₃(ℝ)/SL₃(ℤ)` admits a
`G⁰G⁺(t)`-chart in the sense of `Work.EKLC6Route.Chart`. -/
theorem exists_chart {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ) :
    Nonempty (Work.EKLC6Route.Chart μ t) := by
  classical
  obtain ⟨z0, hz0⟩ := exists_forall_nhds_pos_aux (μ := μ)
  obtain ⟨δ₀, hδ₀pos, hδ₀1, hfac⟩ := exists_uminus_mul_VtSet t
  have hcap : 0 < injCap z0 := injCap_pos z0
  have hcap1 : injCap z0 ≤ 1 / 2 := injCap_le_half z0
  -- ## the constants
  set δ : ℝ := min (min (1 / 100) δ₀) (injCap z0 / 16) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min (lt_min (by norm_num) hδ₀pos) (by linarith)
  have hδ1 : δ ≤ 1 / 100 := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδδ₀ : δ ≤ δ₀ := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδcap : δ ≤ injCap z0 / 16 := by rw [hδdef]; exact min_le_right _ _
  set ρ : ℝ := δ / 8000 with hρdef
  set r₀ : ℝ := δ / 16000 with hr₀def
  set A : ℝ := δ / 4000 with hAdef
  have hρpos : 0 < ρ := by rw [hρdef]; positivity
  have hr₀pos : 0 < r₀ := by rw [hr₀def]; positivity
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hAρ : A = 2 * ρ := by rw [hAdef, hρdef]; ring
  have hAr : A = 2 * (2 * r₀) := by rw [hAdef, hr₀def]; ring
  have hA64 : A ≤ injCap z0 / 64 := by rw [hAdef]; linarith [hδcap, hcap]
  have hA2 : A ≤ 1 / 2 := by linarith [hA64, hcap]
  have hAinj : 10 * A ≤ injCap z0 / 4 := by linarith [hA64, hcap]
  -- ## the chart map is injective on the closed box `Ucl (Uminus t) A × (VtSet t ∩ Ucl ⊤ A)`
  have hinj_closed := smul_mul_inj_aux (t := t) (z0 := z0) hApos hA2 hAinj
  -- ## the Borel coordinate maps
  obtain ⟨uc, θ, huc, hθ, hcoord⟩ := exists_coord_maps t z0 A A hApos hApos hinj_closed
  -- ## the monotone family `s ↦ μ {x : uc x ∈ Uball (Uminus t) s}`
  set 𝒜 : ℝ → Set Work.EKLContract.X3 := fun s => chartSet t z0 uc θ s ρ with h𝒜
  set F : ℝ → ℝ := fun s => (μ (𝒜 s)).toReal with hF
  have h𝒜meas : ∀ s, MeasurableSet (𝒜 s) := fun s => measurableSet_chartSet_aux huc hθ
  have hFmono : Monotone F := by
    intro a b hab
    rw [hF]
    exact ENNReal.toReal_mono (measure_ne_top μ (𝒜 b))
      (measure_mono (chartSet_mono_aux hab le_rfl))
  have hF1 : ∀ s, F s ≤ 1 := by
    intro s
    rw [hF]
    calc (μ (𝒜 s)).toReal ≤ (μ Set.univ).toReal :=
          ENNReal.toReal_mono (measure_ne_top μ Set.univ) (measure_mono (Set.subset_univ _))
      _ = 1 := by rw [MeasureTheory.measure_univ]; simp
  have hF0 : ∀ s, 0 ≤ F s := fun s => ENNReal.toReal_nonneg
  -- ## choose a radius `r` at which the `U`-shell is thin
  obtain ⟨r, hrmem, c, _hc0, hcbd⟩ :=
    exists_good_radius hFmono hF1 hF0 (a := r₀) (b := 2 * r₀) (by linarith [hr₀pos])
  have hrpos : 0 < r := lt_trans hr₀pos hrmem.1
  have hrA : 2 * r ≤ A := by rw [hAr]; linarith [hrmem.2]
  have hrδ : 4000 * r ≤ δ := by
    have h2 : 2 * r₀ = δ / 8000 := by rw [hr₀def]; ring
    linarith [hrmem.2, h2, hδpos]
  -- ## the coordinates hold on the chart's own ball
  have hcoord' : ∀ u ∈ Work.EKLComp.Uball (Uminus t) (2 * r),
      ∀ k ∈ VtSet t ∩ V (2 * ρ),
      uc ((u * k) • z0) = u ∧ θ ((u * k) • z0) = k := by
    intro u hu k hk
    refine hcoord u (Uball_subset_Ucl_aux hrA hu) k ⟨hk.1, ?_⟩
    exact V_subset_Ucl_top_aux (by rw [hAρ]) hk.2
  -- ## the action is free on the chart
  have hinj_field : ∀ u ∈ Work.EKLComp.Uball (Uminus t) (2 * r),
      ∀ k ∈ VtSet t ∩ V (2 * ρ), ∀ g h : Work.EKLContract.SL3,
      g ∈ V δ → h ∈ V δ → g • ((u * k) • z0) = h • ((u * k) • z0) → g = h := by
    intro u hu k hk g h hg hh heq
    set σ : ℝ := 4 * r + 4 * ρ + 3 * (4 * r) * (4 * ρ) with hσdef
    have hu4 : u ∈ V (4 * r) := fun i j => by have := hu.2 i j; linarith
    have hk4 : k ∈ V (4 * ρ) := fun i j => by have := hk.2 i j; linarith
    have huk : u * k ∈ V σ := by
      rw [hσdef]
      exact V_mul_subset_V (by linarith) (by linarith) hu4 hk4
    have hσ8 : σ ≤ injCap z0 / 8 := by
      have h2 : r < δ / 8000 := by
        have h3 : 2 * r₀ = δ / 8000 := by rw [hr₀def]; ring
        linarith [hrmem.2, h3]
      rw [hσdef, hρdef]
      nlinarith [h2, hδcap, hcap, hrpos]
    have hz0inj : InjAt z0 (injCap z0 / 4) :=
      injAt_of_lt_injCap (by linarith) (by linarith)
    have htr : InjAt ((u * k) • z0) (injCap z0 / 16) := by
      have h1 : InjAt ((u * k) • z0) ((injCap z0 / 4) / 4) :=
        hz0inj.transfer (r := injCap z0 / 4) (a := σ)
          (by linarith [hcap1]) (by rw [hσdef]; positivity) (by linarith [hσ8, hcap])
          (by linarith [hσ8, hcap]) huk
      rwa [show (injCap z0 / 4) / 4 = injCap z0 / 16 from by ring] at h1
    exact htr g h (Work.Misiurewicz.V_mono hδcap hg) (Work.Misiurewicz.V_mono hδcap hh) heq
  -- ## positivity of the chart
  have hpos : 0 < μ (chartSet t z0 uc θ r ρ) := by
    set δ₁ : ℝ := min r ρ / 40 with hδ₁def
    have hδ₁pos : 0 < δ₁ := by
      rw [hδ₁def]
      exact div_pos (lt_min hrpos hρpos) (by norm_num)
    have hδ₁δ₀ : δ₁ ≤ δ₀ := by
      rw [hδ₁def]
      have h1 : min r ρ / 40 ≤ ρ / 40 :=
        div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      have h2 : ρ / 40 ≤ δ := by rw [hρdef]; linarith [hδpos]
      linarith
    have h40r : 40 * δ₁ ≤ r := by
      rw [hδ₁def, mul_div_cancel₀]
      exact min_le_left _ _
      norm_num
    have h40ρ : 40 * δ₁ ≤ ρ := by
      rw [hδ₁def, mul_div_cancel₀]
      exact min_le_right _ _
      norm_num
    have hsub : (fun g : Work.EKLContract.SL3 => g • z0) '' V δ₁ ⊆
        chartSet t z0 uc θ r ρ := by
      rintro x ⟨w, hw, rfl⟩
      obtain ⟨u, hu, k, hk, rfl⟩ := hfac δ₁ hδ₁pos hδ₁δ₀ w hw
      obtain ⟨h1, h2⟩ := hcoord' u (Work.EKLComp.Uball_mono (by linarith [h40r]) hu) k
        ⟨hk.1, Work.Misiurewicz.V_mono (by linarith [h40ρ]) hk.2⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [h1]; exact Work.EKLComp.Uball_mono h40r hu
      · rw [h2]; exact ⟨hk.1, Work.Misiurewicz.V_mono h40ρ hk.2⟩
      · rw [h1, h2]
    have hnhds : (fun g : Work.EKLContract.SL3 => g • z0) '' V δ₁ ∈ nhds z0 :=
      Work.EKLComp.orbit_image_V_mem_nhds z0 δ₁ hδ₁pos
    exact lt_of_lt_of_le (hz0 _ hnhds) (measure_mono hsub)
  -- ## thinness of the shell `|dev (uc x) - r| ≤ ε`
  have hthin : ∃ c : ℝ, ∀ ε : ℝ, 0 < ε →
      μ {x | x ∈ chartSet t z0 uc θ (2 * r) ρ ∧ |dev (uc x) - r| ≤ ε} ≤
        ENNReal.ofReal (c * ε) := by
    refine ⟨2 * c, fun ε hε => ?_⟩
    have hsub : {x : Work.EKLContract.X3 |
        x ∈ 𝒜 (2 * r) ∧ |dev (uc x) - r| ≤ ε} ⊆ 𝒜 (r + 2 * ε) \ 𝒜 (r - 2 * ε) := by
      rintro x ⟨hx, hdev⟩
      obtain ⟨hu, hk, heq⟩ := hx
      obtain ⟨hdev1, hdev2⟩ := abs_le.mp hdev
      refine (Set.mem_sdiff x).mpr ⟨?_, ?_⟩
      · refine ⟨?_, hk, heq⟩
        rw [mem_Uball_iff_dev_aux]
        exact ⟨hu.1, by linarith⟩
      · intro hx'
        obtain ⟨hu', -, -⟩ := hx'
        rw [mem_Uball_iff_dev_aux] at hu'
        linarith [hu'.2]
    have hsubm : 𝒜 (r - 2 * ε) ⊆ 𝒜 (r + 2 * ε) :=
      chartSet_mono_aux (by linarith) le_rfl
    refine le_trans (measure_mono hsub) ?_
    calc μ (𝒜 (r + 2 * ε) \ 𝒜 (r - 2 * ε))
        = μ (𝒜 (r + 2 * ε)) - μ (𝒜 (r - 2 * ε)) :=
          measure_sdiff hsubm (h𝒜meas _).nullMeasurableSet (measure_ne_top μ _)
      _ = ENNReal.ofReal (F (r + 2 * ε) - F (r - 2 * ε)) := by
          have h1 : (μ (𝒜 (r + 2 * ε)) - μ (𝒜 (r - 2 * ε))).toReal =
              F (r + 2 * ε) - F (r - 2 * ε) :=
            ENNReal.toReal_sub_of_le (measure_mono hsubm) (measure_ne_top μ _)
          rw [← h1]
          exact (ENNReal.ofReal_toReal
            (ne_top_of_lt (lt_of_le_of_lt tsub_le_self (measure_lt_top μ _)))).symm
      _ ≤ ENNReal.ofReal (c * (2 * ε)) := ENNReal.ofReal_le_ofReal (hcbd (2 * ε) (by linarith))
      _ = ENNReal.ofReal ((2 * c) * ε) := by
          congr 1
          ring
  exact ⟨{ z0 := z0, r := r, ρ := ρ, δ := δ, uc := uc, θ := θ, hr := hrpos, hρ := hρpos, hδ := hδpos, hδ1 := hδ1, hrδ := hrδ, hρδ := by rw [hρdef]; linarith [hδpos], huc := huc, hθ := hθ, coord := hcoord', inj := hinj_field, pos := hpos, thin := hthin }⟩

end Work.EKLC6Route
