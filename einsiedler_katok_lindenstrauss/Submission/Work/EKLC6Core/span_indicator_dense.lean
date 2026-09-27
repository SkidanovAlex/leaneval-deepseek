import Mathlib
import Submission.Work.EKLC6Core.setIntegral_eq_zero_of_generates

namespace Work.EKLC6Core

open MeasureTheory

/-- The submodule of `L²`-functions (with respect to a finite measure). -/
private def memLpSubmodule (X : Type*) [MeasurableSpace X] (ν : Measure X) :
    Submodule ℝ (X → ℝ) where
  carrier := {g | MemLp g 2 ν}
  zero_mem' := MemLp.zero
  add_mem' := by intro a b ha hb; exact ha.add hb
  smul_mem' := by intro c a ha; exact ha.const_smul c

/-- Functions that are a.e. equal to a function whose `L²`-class lies in a fixed submodule. -/
private def toLpMemSubmodule (X : Type*) [MeasurableSpace X] (ν : Measure X)
    (K : Submodule ℝ (Lp ℝ 2 ν)) : Submodule ℝ (X → ℝ) where
  carrier := {x | ∃ m : MemLp x 2 ν, MemLp.toLp x m ∈ K}
  zero_mem' := ⟨MemLp.zero, by rw [MemLp.toLp_zero]; exact Submodule.zero_mem _⟩
  add_mem' := by
    intro a b ha hb
    obtain ⟨m1, hm1⟩ := ha
    obtain ⟨m2, hm2⟩ := hb
    exact ⟨m1.add m2, by show m1.toLp a + m2.toLp b ∈ K; exact Submodule.add_mem _ hm1 hm2⟩
  smul_mem' := by
    intro c a ha
    obtain ⟨m1, hm1⟩ := ha
    exact ⟨m1.const_smul c, by show c • m1.toLp a ∈ K; exact Submodule.smul_mem _ c hm1⟩

theorem span_indicator_dense {X : Type*} [MeasurableSpace X] (S : ℕ → Set X) (hS : ∀ n, MeasurableSet (S n)) (hπ : ∀ m n, ∃ k, S m ∩ S n = S k) (hU : ∃ k, S k = Set.univ) (hgen : MeasurableSpace.generateFrom (Set.range S) = (inferInstance : MeasurableSpace X)) (ν : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure ν] (f : X → ℝ) (hf : MeasureTheory.MemLp f 2 ν) {ε : ℝ} (hε : 0 < ε) : ∃ (ι : Finset ℕ) (c : ℕ → ℝ), ∫ x, (f x - ∑ n ∈ ι, c n * (S n).indicator (fun _ => (1 : ℝ)) x) ^ 2 ∂ν < ε := by
  classical
  have hfin : ∀ s : Set X, ν s ≠ ⊤ := fun s => measure_ne_top ν s
  -- The indicator functions `1_{S n}`.
  let ind : ℕ → X → ℝ := fun n => (S n).indicator (fun _ => 1)
  have hMemLp_ind : ∀ n, MemLp (ind n) 2 ν := fun n =>
    memLp_indicator_const 2 (hS n) 1 (Or.inr (hfin (S n)))
  have hMemLp_span : ∀ g ∈ Submodule.span ℝ (Set.range ind), MemLp g 2 ν := by
    have hle : Submodule.span ℝ (Set.range ind) ≤ memLpSubmodule X ν :=
      Submodule.span_le.mpr (by rintro g ⟨n, rfl⟩; exact hMemLp_ind n)
    exact fun g hg => hle hg
  -- The corresponding span inside `L²`.
  let v : ℕ → Lp ℝ 2 ν := fun n => indicatorConstLp 2 (hS n) (hfin (S n)) 1
  let K : Submodule ℝ (Lp ℝ 2 ν) := Submodule.span ℝ (Set.range v)
  -- The natural map from the function-span to `L²`.
  let F : (Submodule.span ℝ (Set.range ind)) → Lp ℝ 2 ν :=
    fun g => (hMemLp_span g.1 g.2).toLp g.1
  ------------------------------------------------------------------------------
  -- Step 1: `K` has trivial orthogonal complement.
  ------------------------------------------------------------------------------
  have hKorth : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro g hg
    rw [Submodule.mem_orthogonal] at hg
    have hzero : ∀ n, ∫ x in S n, (g : X → ℝ) x ∂ν = 0 := by
      intro n
      have hu : v n ∈ K := Submodule.subset_span ⟨n, rfl⟩
      have h1 := hg (v n) hu
      rwa [L2.inner_indicatorConstLp_one (hS n) (hfin (S n)) g] at h1
    have hint : Integrable (g : X → ℝ) ν := (Lp.memLp g).integrable (by norm_num)
    have hD := setIntegral_eq_zero_of_generates (h := (g : X → ℝ)) S hS hπ hU hgen ν hint hzero
    have hfint : ∀ s, MeasurableSet s → ν s < ⊤ → IntegrableOn (g : X → ℝ) s ν :=
      fun s _ _ => hint.mono_measure Measure.restrict_le_self
    have hae : (g : X → ℝ) =ᵐ[ν] 0 :=
      Lp.ae_eq_zero_of_forall_setIntegral_eq_zero g (by norm_num) (by norm_num) hfint
        (fun s hs _ => hD s hs)
    apply Lp.ext
    filter_upwards [hae, Lp.coeFn_zero ℝ 2 ν] with x hx hx0
    rw [hx, hx0]
  have hKtop : K.topologicalClosure = ⊤ := Submodule.topologicalClosure_eq_top_iff.mpr hKorth
  ------------------------------------------------------------------------------
  -- Step 2: basic properties of the map `F`, and its range is `K`.
  ------------------------------------------------------------------------------
  have hF_gen : ∀ n, F ⟨ind n, Submodule.subset_span ⟨n, rfl⟩⟩ = v n := fun n => rfl
  have hF_zero : F 0 = 0 := rfl
  have hF_add : ∀ g₁ g₂ : Submodule.span ℝ (Set.range ind), F (g₁ + g₂) = F g₁ + F g₂ :=
    fun g₁ g₂ => rfl
  have hF_smul : ∀ (a : ℝ) (g : Submodule.span ℝ (Set.range ind)), F (a • g) = a • F g :=
    fun a g => rfl
  have hF_subset : Set.range F ⊆ (K : Set (Lp ℝ 2 ν)) := by
    rintro y ⟨g, rfl⟩
    have hA : Submodule.span ℝ (Set.range ind) ≤ toLpMemSubmodule X ν K :=
      Submodule.span_le.mpr (by
        rintro x ⟨n, rfl⟩
        refine ⟨memLp_indicator_const 2 (hS n) (1 : ℝ) (Or.inr (hfin (S n))), ?_⟩
        show v n ∈ K
        exact Submodule.subset_span ⟨n, rfl⟩)
    obtain ⟨m, hm⟩ := hA g.2
    dsimp only [F]
    rw [MemLp.toLp_congr (hMemLp_span g.1 g.2) m (Filter.EventuallyEq.refl _ _)]
    exact hm
  have hF_range : Set.range F = (K : Set (Lp ℝ 2 ν)) := by
    apply Set.Subset.antisymm hF_subset
    intro y hy
    have hB : Submodule.span ℝ (Set.range v) ≤
        ({ carrier := Set.range F,
           zero_mem' := ⟨0, hF_zero⟩,
           add_mem' := (by
             intro a b ha hb
             obtain ⟨g₁, rfl⟩ := ha
             obtain ⟨g₂, rfl⟩ := hb
             exact ⟨g₁ + g₂, hF_add g₁ g₂⟩),
           smul_mem' := (by
             intro c a ha
             obtain ⟨g, rfl⟩ := ha
             exact ⟨c • g, hF_smul c g⟩) } : Submodule ℝ (Lp ℝ 2 ν)) :=
      Submodule.span_le.mpr (by
        rintro _ ⟨n, rfl⟩
        exact ⟨⟨ind n, Submodule.subset_span ⟨n, rfl⟩⟩, hF_gen n⟩)
    exact hB hy
  ------------------------------------------------------------------------------
  -- Step 3: extract a nearby element of `range F` and convert it into a combo.
  ------------------------------------------------------------------------------
  set δ : ℝ := Real.sqrt (ε / 2) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact Real.sqrt_pos_of_pos (by linarith)
  have hδsq : δ ^ 2 = ε / 2 := by rw [hδdef]; exact Real.sq_sqrt (by positivity)
  have hxcl : (hf.toLp f) ∈ closure (Set.range F) := by
    have hxK : (hf.toLp f) ∈ closure (K : Set (Lp ℝ 2 ν)) := by
      rw [← Submodule.topologicalClosure_coe, hKtop]
      exact Submodule.mem_top
    rwa [← hF_range] at hxK
  obtain ⟨g, hgdist⟩ := Metric.mem_closure_range_iff.mp hxcl δ hδpos
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp g.2
  set p : X → ℝ := fun x => ∑ i ∈ c.support, c i * ind i x with hpdef
  have hp_eq : c.sum (fun i a => a • ind i) = p := by
    funext x
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hpdef]
  have hgp : g.1 = p := hc.symm.trans hp_eq
  have hp : MemLp p 2 ν := hgp ▸ hMemLp_span g.1 g.2
  have hFg : F g = hp.toLp p := by
    dsimp only [F]
    exact MemLp.toLp_congr _ _ (by filter_upwards with x; rw [hgp])
  have hdist2 : dist (hf.toLp f) (hp.toLp p) < δ := by rw [← hFg]; exact hgdist
  rw [dist_eq_norm] at hdist2
  have hsub : hf.toLp f - hp.toLp p = (hf.sub hp).toLp (f - p) := (MemLp.toLp_sub hf hp).symm
  rw [hsub, Lp.norm_toLp, toReal_eLpNorm] at hdist2
  have hlp : lpNorm (f - p) 2 ν = Real.sqrt (∫ x, ‖(f - p) x‖ ^ 2 ∂ν) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (p := 2) (by norm_num) (by norm_num)
      (MemLp.aestronglyMeasurable (hf.sub hp))]
    rw [Real.sqrt_eq_rpow]
    have h2 : ENNReal.toReal 2 = (2 : ℝ) := by norm_num
    rw [h2]
    norm_num
  rw [hlp] at hdist2
  have hA_nonneg : 0 ≤ ∫ x, ‖(f - p) x‖ ^ 2 ∂ν := integral_nonneg (fun x => sq_nonneg _)
  have hA : ∫ x, ‖(f - p) x‖ ^ 2 ∂ν < ε := by
    have hlt : ∫ x, ‖(f - p) x‖ ^ 2 ∂ν < ε / 2 := by
      rw [hδdef] at hdist2
      exact (Real.sqrt_lt_sqrt_iff hA_nonneg).mp hdist2
    linarith
  have hAeq : ∫ x, ‖(f - p) x‖ ^ 2 ∂ν = ∫ x, (f x - p x) ^ 2 ∂ν := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Pi.sub_apply, Real.norm_eq_abs, sq_abs]
  refine ⟨c.support, fun n => c n, ?_⟩
  show ∫ x, (f x - ∑ i ∈ c.support, c i * ind i x) ^ 2 ∂ν < ε
  exact hAeq ▸ hA

end Work.EKLC6Core
