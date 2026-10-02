import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.analyticOnNhd_invFunOn
import Submission.Work.ELRig.analyticOn_rayPt_of_analytic
import Submission.Work.ELRig.analyticOnNhd_dynBottcher
import Submission.Work.ELRig.Cyl.continuous_tau
import Submission.Work.ELRig.exists_liftCurvesV2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Classical Filter Set
open scoped Topology

/-! ## Two general facts -/

/-- The set of values that a function takes *constantly near a point* of an open set is countable:
each such value is determined by a rational interval on which the function is constant. -/
theorem countable_locally_eq_values {f : ℝ → ℝ} {W : Set ℝ} (hW : IsOpen W) :
    {v : ℝ | ∃ x ∈ W, ∀ᶠ z in 𝓝 x, f z = v}.Countable := by
  let T : ℚ × ℚ → Set ℝ := fun pq => {v : ℝ | (pq.1 : ℝ) < (pq.2 : ℝ) ∧
      Set.Ioo (pq.1 : ℝ) (pq.2 : ℝ) ⊆ W ∧ ∀ t ∈ Set.Ioo (pq.1 : ℝ) (pq.2 : ℝ), f t = v}
  have hT : ∀ pq : ℚ × ℚ, (T pq).Countable := fun pq =>
    Set.Subsingleton.countable (by
      rintro v ⟨hpq, -, hv⟩ v' ⟨-, -, hv'⟩
      obtain ⟨t, ht⟩ := exists_between hpq
      exact (hv t ht).symm.trans (hv' t ht))
  refine Set.Countable.mono ?_ (Set.countable_iUnion hT)
  rintro v ⟨x, hxW, hx⟩
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hx
  obtain ⟨δ', hδ'pos, hδ'⟩ := Metric.isOpen_iff.mp hW x hxW
  have hminpos : 0 < min δ δ' := lt_min hδpos hδ'pos
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show x - min δ δ' < x by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x < x + min δ δ' by linarith)
  refine Set.mem_iUnion.mpr ⟨(p, q), lt_trans hp2 hq1, ?_, ?_⟩
  · intro z hz
    exact hδ' (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hz.1, min_le_right δ δ'], by linarith [hz.2, min_le_right δ δ']⟩)
  · intro z hz
    have h1 : z ∈ Metric.ball x δ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hz.1, min_le_left δ δ'], by linarith [hz.2, min_le_left δ δ']⟩
    exact hδ h1

/-- A countable set of reals misses some point of any nondegenerate open interval: a countable
set cannot contain an interval of positive length. -/
theorem exists_pos_lt_notMem_countable {ε : ℝ} (hε : 0 < ε) {s : Set ℝ} (hs : s.Countable) :
    ∃ η : ℝ, η ∈ Set.Ioo 0 ε ∧ η ∉ s := by
  by_contra h
  push_neg at h
  have hcount : (Set.Ioo (0 : ℝ) ε).Countable := hs.mono (fun η hη => h η hη)
  have hzero := hcount.measure_zero MeasureTheory.volume
  rw [Real.volume_Ioo] at hzero
  have := ENNReal.ofReal_eq_zero.mp hzero
  linarith

/-! ## The level set in one period -/

/-!
# `levelSet_im_finite_small`

For a `RayCylLift` `L` whose first lift `γ₁` is pinned (`hpin`) to the `Ψ`-inverse branch of the
root ray on one period `[N, N+1]`, the level sets of `Im γ₁` and of `Im γ₂ = -Im γ₁` in that
period are finite for every level `y + η` with `η ∈ (0, ε)` outside a countable exceptional set.

Proof.  On `u ∈ [N, N+1]` the pinning reads `γ₁ u = E (rayPt α₁ (τ u))`, where `E` is the inverse
branch of `Ψ` on the half plane `U = {Re w < -R}`.  The set of those `u` for which the ray point
`rayPt α₁ (τ u)` has *no* `U`-preimage under `Ψ` is a subsingleton: there `hpin` forces `γ₁ u` to
be the default value of `invFunOn` (a fixed point independent of `u`), and `rayPt α₁` is injective
in its level.  Hence – apart from at most one point of the interval – the level set is the
`τ`-preimage of the level set of the chart `G = Im ∘ E ∘ rayPt α₁`, which is real analytic on the
open set `W` of those levels `t` whose ray point `rayPt α₁ t` does lie in `Ψ '' U`.  If a level set
of `G` inside `W` is infinite it has an accumulation point `x`; at an interior accumulation point
the analytic alternative (given by `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`) makes `G`
constant on a neighbourhood, so the level is a *locally constant value* of `G` — and there are only
countably many of those; while an accumulation at the boundary of `W` happens only for the level
which is the imaginary part of the default value (there the continuity of `γ₁` applies).  Both
countable collections are avoided by the choice of `η` (`exists_pos_lt_notMem_countable`: a
countable set misses some point of any interval of positive length). -/

theorem levelSet_im_finite_small {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) (N : ℝ)
    (hpin : ∀ u : ℝ, u ∈ Set.Icc N (N + 1) → L.γ₁ u = Function.invFunOn fl.Ψ
      {w : ℂ | w.re < -L.R} (Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u)))
    (y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η < ε ∧
      ({s : ℝ | s ∈ Set.Ico N (N + 1) ∧ (L.γ₁ s).im = y + η}).Finite ∧
      ({s : ℝ | s ∈ Set.Ico N (N + 1) ∧ (L.γ₂ s).im = y + η}).Finite := by
  -- ## `τ` is continuous and strictly increasing
  have hτcont : Continuous L.τ := (Work.ELRig.Cyl.continuous_tau d fl L).1
  have hτmono : Monotone L.τ := L.hτmono.monotone
  have hτinj : Function.Injective L.τ := L.hτmono.injective
  -- ## the half plane `U`, the inverse branch `E`, and the pinned family
  set U : Set ℂ := {w : ℂ | w.re < -L.R} with hUdef
  have hUopen : IsOpen U := by rw [hUdef]; exact isOpen_lt Complex.continuous_re continuous_const
  have hΨan : AnalyticOnNhd ℂ fl.Ψ U := by
    rw [hUdef]; exact fl.Ψ_diff.differentiableOn.analyticOnNhd hUopen
  have hInj : Set.InjOn fl.Ψ U := L.hinj
  set E : ℂ → ℂ := Function.invFunOn fl.Ψ U with hEdef
  have hEan : AnalyticOnNhd ℂ E (fl.Ψ '' U) := by
    rw [hEdef]; exact analyticOnNhd_invFunOn hUopen hΨan hInj
  have hpin' : ∀ u : ℝ, u ∈ Set.Icc N (N + 1) →
      L.γ₁ u = E (Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u)) := by
    intro u hu
    rw [hEdef, hUdef]
    exact hpin u hu
  -- ## the exceptional locus is a subsingleton
  have hKsub : ∀ u₁ u₂ : ℝ, u₁ ∈ Set.Icc N (N + 1) → u₂ ∈ Set.Icc N (N + 1) →
      Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u₁) ∉ fl.Ψ '' U →
      Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u₂) ∉ fl.Ψ '' U → u₁ = u₂ := by
    intro u₁ u₂ h₁ h₂ hm₁ hm₂
    have hneg₁ : ¬ ∃ a ∈ U, fl.Ψ a = Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u₁) :=
      fun ⟨a, ha, hax⟩ => hm₁ ⟨a, ha, hax⟩
    have hneg₂ : ¬ ∃ a ∈ U, fl.Ψ a = Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u₂) :=
      fun ⟨a, ha, hax⟩ => hm₂ ⟨a, ha, hax⟩
    have econst : E (Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u₁))
        = E (Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u₂)) := by
      rw [hEdef, Function.invFunOn_neg hneg₁, Function.invFunOn_neg hneg₂]
    have eγ : L.γ₁ u₁ = L.γ₁ u₂ := by rw [hpin' u₁ h₁, hpin' u₂ h₂]; exact econst
    have ept : Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u₁)
        = Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u₂) := by
      rw [← L.hΨ₁ u₁, ← L.hΨ₁ u₂, eγ]
    exact hτinj (Work.ELRig.rayPt_level_inj d.hN (L.hτ1 u₁) (L.hτ1 u₂) ept)
  -- ## the chart region `W`, its chart `G`, and the analyticity of `G`
  have hray_an : AnalyticOn ℝ (fun t : ℝ => Work.EL.rayPt d.hN Work.EL.alpha1 t) (Set.Ioi 1) :=
    analyticOn_rayPt_of_analytic d.hN (analyticOnNhd_dynBottcher d.bottcher) Work.EL.alpha1
  have hUimg_open : IsOpen (fl.Ψ '' U) := by
    rw [Metric.isOpen_iff]
    rintro y ⟨x₀, hx₀, rfl⟩
    obtain ⟨δ, hδpos, σ, -, hσr, hσm, -⟩ :=
      exists_analytic_localInverse_of_injOn hUopen hΨan hInj hx₀
    exact ⟨δ, hδpos, fun z hz => ⟨σ z, hσm z hz, hσr z hz⟩⟩
  set W : Set ℝ := {t : ℝ | Work.EL.rayPt d.hN Work.EL.alpha1 t ∈ fl.Ψ '' U} ∩ Set.Ioi 1
    with hWdef
  have hWopen : IsOpen W := by
    rw [hWdef, isOpen_iff_mem_nhds]
    rintro t ⟨htm, ht1⟩
    have hcont : ContinuousAt (fun t : ℝ => Work.EL.rayPt d.hN Work.EL.alpha1 t) t :=
      (hray_an.analyticAt (isOpen_Ioi.mem_nhds ht1)).continuousAt
    exact Filter.inter_mem (hcont.preimage_mem_nhds (hUimg_open.mem_nhds htm))
      (isOpen_Ioi.mem_nhds ht1)
  set G : ℝ → ℝ := fun t : ℝ => (E (Work.EL.rayPt d.hN Work.EL.alpha1 t)).im with hGdef
  have hGan : AnalyticOnNhd ℝ G W := by
    intro t ht
    have ht1 : t ∈ Set.Ioi (1 : ℝ) := ht.2
    have hrat : AnalyticAt ℝ (fun t : ℝ => Work.EL.rayPt d.hN Work.EL.alpha1 t) t :=
      hray_an.analyticAt (isOpen_Ioi.mem_nhds ht1)
    have hEx : AnalyticAt ℝ E (Work.EL.rayPt d.hN Work.EL.alpha1 t) :=
      (hEan _ ht.1).restrictScalars
    have hcomp : AnalyticAt ℝ (fun t : ℝ => E (Work.EL.rayPt d.hN Work.EL.alpha1 t)) t :=
      hEx.comp hrat
    have h2 := (ContinuousLinearMap.analyticAt Complex.imCLM
      (E (Work.EL.rayPt d.hN Work.EL.alpha1 t))).comp
      (x := t) (f := fun s : ℝ => E (Work.EL.rayPt d.hN Work.EL.alpha1 s)) hcomp
    simpa [G, hGdef, Function.comp_def] using h2
  -- ## the imaginary part of the default value, and the bad set of levels
  have hcval : ∃ cval : ℝ, ∀ x : ℂ, x ∉ fl.Ψ '' U → (E x).im = cval := by
    by_cases h : ∃ x : ℂ, x ∉ fl.Ψ '' U
    · refine ⟨(E (Classical.choose h)).im, fun x hx => ?_⟩
      have h₁ : ¬ ∃ a ∈ U, fl.Ψ a = x := fun ⟨a, ha, hax⟩ => hx ⟨a, ha, hax⟩
      have h₂ : ¬ ∃ a ∈ U, fl.Ψ a = Classical.choose h :=
        fun ⟨a, ha, hax⟩ => (Classical.choose_spec h) ⟨a, ha, hax⟩
      have := congrArg Complex.im (show E x = E (Classical.choose h) from by
        rw [hEdef, Function.invFunOn_neg h₁, Function.invFunOn_neg h₂])
      simpa using this
    · exact ⟨0, fun x hx => absurd ⟨x, hx⟩ h⟩
  obtain ⟨cval, hcval⟩ := hcval
  let LCM : Set ℝ := {v : ℝ | ∃ x ∈ W, ∀ᶠ z in 𝓝 x, G z = v}
  have hLCMcount : LCM.Countable := countable_locally_eq_values hWopen
  set Bad : Set ℝ := {v : ℝ | v ∈ LCM ∨ -v ∈ LCM ∨ v = cval ∨ v = -cval} with hBaddef
  have hBadcount : Bad.Countable := by
    rw [hBaddef]
    refine Set.Countable.mono ?_ ((hLCMcount.union (hLCMcount.image Neg.neg)).union
      (Set.Finite.countable ((Set.finite_singleton (-cval)).insert cval)))
    intro v hv
    rcases hv with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨-v, h, neg_neg v⟩)
    · exact Or.inr (by simp [h])
    · exact Or.inr (by simp [h])
  -- ## the analytic heart: away from the bad levels the level set of `Im γ₁` is finite
  have hkey : ∀ v : ℝ, v ∉ LCM → v ≠ cval →
      ({s : ℝ | s ∈ Set.Ico N (N + 1) ∧ (L.γ₁ s).im = v}).Finite := by
    intro v hvlcm hvc
    by_contra hfin
    rw [Set.not_finite] at hfin
    set Z₁ : Set ℝ := {u : ℝ | u ∈ Set.Icc N (N + 1) ∧ (L.γ₁ u).im = v} with hZ₁
    have hZ₁inf : Z₁.Infinite :=
      hfin.mono (fun s hs => ⟨⟨hs.1.1, le_of_lt hs.1.2⟩, hs.2⟩)
    obtain ⟨x, hxI, hxacc⟩ :=
      Set.Infinite.exists_accPt_of_subset_isCompact hZ₁inf isCompact_Icc (fun u hu => hu.1)
    have hlev : (L.γ₁ x).im = v := by
      have hclosed : IsClosed {u : ℝ | (L.γ₁ u).im = v} :=
        isClosed_eq (Complex.continuous_im.comp L.cont₁) continuous_const
      exact (isClosed_iff_accPt.mp hclosed) x
        (hxacc.mono (Filter.principal_mono.mpr (fun u hu => hu.2)))
    by_cases hxK : Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ x) ∈ fl.Ψ '' U
    · -- **good case**: the accumulation happens where the chart is analytic
      -- the exceptional locus of the interval is a subsingleton, hence finite
      set Kset : Set ℝ := {u : ℝ | u ∈ Set.Icc N (N + 1) ∧
        Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u) ∉ fl.Ψ '' U} with hKset
      have hKfin : Kset.Finite := Set.Subsingleton.finite (fun u hu u' hu' =>
        hKsub u u' hu.1 hu'.1 hu.2 hu'.2)
      set ZA : Set ℝ := {u : ℝ | u ∈ Z₁ ∧
        Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u) ∈ fl.Ψ '' U} with hZA
      have hZAdiff : Z₁ \ Kset ⊆ ZA := by
        rintro u ⟨hu, huK⟩
        exact ⟨hu, by
          by_contra hmem
          exact huK ⟨hu.1, hmem⟩⟩
      have hZAinf : ZA.Infinite := (hZ₁inf.sdiff hKfin).mono hZAdiff
      have hxW : L.τ x ∈ W :=
        ⟨hxK, lt_of_lt_of_le (L.hτ1 N) (hτmono hxI.1)⟩
      have hnotK : x ∉ Kset := fun h => h.2 hxK
      -- accumulate at `x` inside the chart region
      have hxacc₂ : AccPt x (𝓟 ZA) := by
        rw [accPt_iff_nhds] at hxacc
        rw [accPt_iff_nhds]
        intro V hV
        have hV' : V ∩ Ksetᶜ ∈ 𝓝 x :=
          Filter.inter_mem hV ((hKfin.isClosed.isOpen_compl).mem_nhds hnotK)
        obtain ⟨u, hu, hux⟩ := hxacc (V ∩ Ksetᶜ) hV'
        exact ⟨u, ⟨hu.1.1, hZAdiff ⟨hu.2, hu.1.2⟩⟩, hux⟩
      have hxaccA : AccPt (L.τ x) (𝓟 (L.τ '' ZA)) := by
        rw [accPt_iff_nhds] at hxacc₂
        rw [accPt_iff_nhds]
        intro V hV
        have hpre : L.τ ⁻¹' V ∈ 𝓝 x := hτcont.continuousAt.preimage_mem_nhds hV
        obtain ⟨u, hu, hux⟩ := hxacc₂ (L.τ ⁻¹' V) hpre
        exact ⟨L.τ u, ⟨hu.1, ⟨u, hu.2, rfl⟩⟩, fun h => hux (hτinj h)⟩
      -- the level points accumulate at `L.τ x`
      have hZAle : L.τ '' ZA ⊆ {t : ℝ | G t = v} := by
        rintro t ⟨u, hu, rfl⟩
        have hGu : G (L.τ u) = (L.γ₁ u).im := by
          simp only [hGdef]
          rw [← hpin' u hu.1.1]
        show G (L.τ u) = v
        rw [hGu, hu.1.2]
      have hdich : (∀ᶠ z in 𝓝 (L.τ x), G z = v) ∨ (∀ᶠ z in 𝓝[≠] (L.τ x), G z ≠ v) := by
        rcases ((hGan (L.τ x) hxW).sub analyticAt_const).eventually_eq_zero_or_eventually_ne_zero
          with h0 | hne
        · left
          filter_upwards [h0] with z hz
          simp only [Pi.sub_apply] at hz
          exact sub_eq_zero.mp hz
        · right
          filter_upwards [hne] with z hz
          simp only [Pi.sub_apply] at hz
          exact sub_ne_zero.mp hz
      rcases hdich with h0 | hne
      · exact hvlcm ⟨L.τ x, hxW, h0⟩
      · exfalso
        have hne' : ∀ᶠ z in 𝓝 (L.τ x), z ≠ L.τ x → G z ≠ v := by
          have h := eventually_nhdsWithin_iff.mp hne
          simpa [Set.mem_compl_iff] using h
        rw [accPt_iff_nhds] at hxaccA
        obtain ⟨t, ht, htx⟩ := hxaccA {z : ℝ | z ≠ L.τ x → G z ≠ v} hne'
        obtain ⟨u, hu, hut⟩ := ht.2
        exact (ht.1 htx) (by rw [← hut]; exact hZAle ⟨u, hu, rfl⟩)
    · -- **bad case**: `x` is the exceptional point, so `v` is the default level
      have hxc : (E (Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ x))).im = cval := hcval _ hxK
      rw [← hpin' x hxI, hlev] at hxc
      exact hvc hxc
  -- ## choose the small `η` avoiding the countable bad set, and finish
  have hcountpre : {η : ℝ | y + η ∈ Bad}.Countable :=
    hBadcount.preimage (f := fun η : ℝ => y + η) (by intro a b hab; linarith)
  obtain ⟨η, hηmem, hηnot⟩ := exists_pos_lt_notMem_countable hε hcountpre
  have h1 : y + η ∉ LCM := fun h => hηnot (by rw [hBaddef]; exact Or.inl h)
  have h2 : -(y + η) ∉ LCM := fun h => hηnot (by rw [hBaddef]; exact Or.inr (Or.inl h))
  have h3 : y + η ≠ cval := fun h =>
    hηnot (by rw [hBaddef]; exact Or.inr (Or.inr (Or.inl h)))
  have h4 : y + η ≠ -cval := fun h =>
    hηnot (by rw [hBaddef]; exact Or.inr (Or.inr (Or.inr h)))
  have h4' : -(y + η) ≠ cval := fun h => h4 (by linarith)
  refine ⟨η, hηmem.1, hηmem.2, hkey (y + η) h1 h3, ?_⟩
  have hγ₂ : ∀ s : ℝ, (L.γ₂ s).im = -(L.γ₁ s).im := by
    intro s
    rw [L.anti s]
    simp
  have heq : {s : ℝ | s ∈ Set.Ico N (N + 1) ∧ (L.γ₂ s).im = y + η}
      = {s : ℝ | s ∈ Set.Ico N (N + 1) ∧ (L.γ₁ s).im = -(y + η)} := by
    ext s
    simp only [Set.mem_ofPred_eq]
    rw [hγ₂ s]
    constructor <;> (rintro ⟨hs, h⟩; exact ⟨hs, by linarith⟩)
  rw [heq]
  exact hkey (-(y + η)) h2 h4'

end Work.ELRig
