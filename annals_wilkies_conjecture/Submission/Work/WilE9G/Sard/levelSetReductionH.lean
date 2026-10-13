import Mathlib
import Submission.Work.WilE9G.Sard.FlatDefs
import Submission.Work.WilE9G.Sard.levelSetChartV
import Submission.Work.WilE9G.Sard.exists_local_hypersurface

/-!
# The "strict" branch of the flatness recursion

`levelSetReductionH` is the step of the analytic Sard recursion in which the `j`-th derivative of
`F` is non-zero at the point `x ∈ A`, while `A ⊆ flatSetV F (j-1) ∩ critSet F` (so all derivatives
of orders `1, …, j-1` vanish on `A`, and `F` is critical there).

The flatness assumption forces `A` to lie, near `x`, in the zero set of a scalar analytic function
with non-vanishing gradient: indeed `j ≥ 2` gives `fderiv ℝ F x = 0`, so `exists_local_hypersurface`
produces such a function `g` from a directional derivative of `F`.  The level set `{g = g x}` is,
near `x`, the analytic image of a set in `ℝ^{d-1}` (`chart_of_regular_level`, obtained from the
analytic level-set chart `levelSetChartV` by reindexing the kernel `ker (fderiv ℝ g x)` along a
continuous linear equivalence with `ℝ^{d-1}`).  Pulling `F` back along that parametrisation gives a
map `F' : ℝ^{d-1} → ℝ^m` with `A' ⊆ flatCrit F' j` (`flatCrit_comp_subset`):

* the flatness survives because every term in the Faà di Bruno expansion of `D^i (F ∘ γ)` involves
  `D^k F (γ t)` with `1 ≤ k ≤ i ≤ j-1`, all of which vanish;
* the criticality survives because `fderiv ℝ F (γ t) = 0` and precomposition with the zero map is
  never surjective for a non-trivial target.

The induction hypothesis `H` in dimension `d - 1` then gives the result, and the chart recovers
every point of `A` near `x`, so the two null sets correspond.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.WilE9G.Sard

open MeasureTheory
open scoped Topology

/-! ## Faà di Bruno: flatness of a composition -/

/-- **Flatness of a composite.**  If all the iterated derivatives of `G` of orders `1, …, n`
vanish at `f x`, and both `f` and `G` are `C^n` at the relevant points, then all the iterated
derivatives of `G ∘ f` of orders `1, …, n` vanish at `x`.

This is the Faà di Bruno formula (`iteratedFDeriv_comp`): the `i`-th derivative of the composite
is a sum of terms which all factor through `D^{|π|}G (f x)` with `|π| ≥ 1` the length of an
ordered partition of `i`, and `|π| ≤ i`. -/
lemma iteratedFDeriv_comp_eq_zero_of_flat {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E → F} {g : F → G} {x : E} {n : ℕ}
    (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x)
    (h0 : ∀ i, 1 ≤ i → i ≤ n → iteratedFDeriv 𝕜 i g (f x) = 0) :
    ∀ i, 1 ≤ i → i ≤ n → iteratedFDeriv 𝕜 i (g ∘ f) x = 0 := by
  intro i hi1 hin
  rw [iteratedFDeriv_comp hg hf
    (show (i : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) from by exact_mod_cast hin)]
  refine Finset.sum_eq_zero (fun c _ => ?_)
  ext v
  rw [FormalMultilinearSeries.compAlongOrderedFinpartition_apply]
  have hsz : ftaylorSeries 𝕜 g (f x) c.length = 0 := by
    show iteratedFDeriv 𝕜 c.length g (f x) = 0
    exact h0 c.length (c.length_pos (by omega)) (le_trans c.length_le hin)
  simp [hsz]

/-- A vanishing first iterated derivative is a vanishing Fréchet derivative. -/
lemma fderiv_eq_zero_of_iteratedFDeriv_one_eq_zero {d m : ℕ} {F : (Fin d → ℝ) → (Fin m → ℝ)}
    {x : Fin d → ℝ} (h : iteratedFDeriv ℝ 1 F x = 0) : fderiv ℝ F x = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  have h2 : (iteratedFDeriv ℝ 1 F x) (fun _ : Fin 1 => v) = 0 := by
    rw [h]
    simp
  simpa [iteratedFDeriv_one_apply] using h2

/-- The zero map into `ℝ^m` is not surjective when `m ≥ 1`, even after composing with any
continuous linear map. -/
lemma not_surjective_zero_comp_aux {d d' m : ℕ} (f : (Fin d' → ℝ) →L[ℝ] (Fin d → ℝ))
    (hm : 0 < m) :
    ¬ Function.Surjective ((0 : (Fin d → ℝ) →L[ℝ] (Fin m → ℝ)).comp f) := by
  intro hsurj
  obtain ⟨v, hv⟩ := hsurj (Pi.single ⟨0, hm⟩ (1 : ℝ))
  have h2 : (1 : ℝ) = 0 := by
    have h3 := congrFun hv ⟨0, hm⟩
    simpa using h3.symm
  exact one_ne_zero h2

/-- **`flatCrit` is preserved by composition.**  If `A` consists of flat-critical points of `F`
(derivatives of orders `1, …, j-1` vanishing, and non-surjective derivative) and `g` maps `A'` into
`A`, then `A'` consists of flat-critical points of `F ∘ g`. -/
lemma flatCrit_comp_subset {d d' m j : ℕ} {F : (Fin d → ℝ) → (Fin m → ℝ)}
    {g : (Fin d' → ℝ) → (Fin d → ℝ)} {A : Set (Fin d → ℝ)} {A' : Set (Fin d' → ℝ)}
    (hj : 2 ≤ j) (hm : 0 < m) (hAflat : A ⊆ flatSetV F (j - 1)) (hAcrit : A ⊆ critSet F)
    (hA : A' ⊆ g ⁻¹' A) (hF : ∀ y ∈ A, AnalyticAt ℝ F y) (hg : ∀ t ∈ A', AnalyticAt ℝ g t) :
    A' ⊆ flatCrit (F ∘ g) j := by
  intro t ht
  have hgt : g t ∈ A := hA ht
  refine ⟨?_, ?_⟩
  · -- the iterated derivatives of orders `1, …, j-1` still vanish
    have h1 : ∀ i, 1 ≤ i → i ≤ j - 1 → iteratedFDeriv ℝ i F (g t) = 0 :=
      fun i hi hi' => hAflat hgt i hi hi'
    have h2 := iteratedFDeriv_comp_eq_zero_of_flat (n := j - 1)
      ((hF (g t) hgt).contDiffAt) ((hg t ht).contDiffAt) h1
    exact fun i hi hi' => h2 i hi hi'
  · -- the derivative of the composite vanishes, hence is not surjective
    have hf0 : fderiv ℝ F (g t) = 0 :=
      fderiv_eq_zero_of_iteratedFDeriv_one_eq_zero (hAflat hgt 1 le_rfl (by omega))
    have hchain : fderiv ℝ (F ∘ g) t = (fderiv ℝ F (g t)).comp (fderiv ℝ g t) :=
      (((hF (g t) hgt).differentiableAt.hasFDerivAt).comp t
        ((hg t ht).differentiableAt.hasFDerivAt)).fderiv
    show ¬ Function.Surjective (fderiv ℝ (F ∘ g) t)
    rw [hchain, hf0]
    exact not_surjective_zero_comp_aux (fderiv ℝ g t) hm

/-! ## The analytic chart of a regular level set -/

/-- A non-zero continuous linear functional on `ℝ^d` is onto. -/
lemma range_eq_top_of_ne_zero {d : ℕ} {T : (Fin d → ℝ) →L[ℝ] ℝ} (hT : T ≠ 0) :
    T.range = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro y
  have hex : ∃ v : Fin d → ℝ, T v ≠ 0 := by
    by_contra hcon
    exact hT (ContinuousLinearMap.ext fun v => by
      by_contra hv
      exact hcon ⟨v, hv⟩)
  obtain ⟨v, hv⟩ := hex
  refine ⟨(y / (T v)) • v, ?_⟩
  rw [map_smul, smul_eq_mul]
  exact div_mul_cancel₀ y hv

/-- **A reindexed analytic chart of a regular level set.**  If `h : ℝ^d → ℝ` is analytic at `x`
with non-vanishing derivative there, then the level set `{h = h x}` is, near `x`, the analytic
image of a set in `ℝ^{d-1}`, and there is an explicit continuous map `C` recovering the parameter
of a level point.

This is `levelSetChartV` applied to `h` packaged as a map into `Fin 1 → ℝ`, together with a
reindexing of the kernel `ker (fderiv ℝ h x)` (which has dimension `d - 1`) along a continuous
linear equivalence with `ℝ^{d-1}`. -/
lemma chart_of_regular_level {d : ℕ} (h : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (hh : AnalyticAt ℝ h x) (hgrad : fderiv ℝ h x ≠ 0) :
    ∃ (γ : (Fin (d - 1) → ℝ) → (Fin d → ℝ)) (V : Set (Fin (d - 1) → ℝ))
      (U : Set (Fin d → ℝ)) (C : (Fin d → ℝ) →L[ℝ] (Fin (d - 1) → ℝ)),
      IsOpen V ∧ IsOpen U ∧ (0 : Fin (d - 1) → ℝ) ∈ V ∧ x ∈ U ∧ γ 0 = x ∧
      (∀ v ∈ V, AnalyticAt ℝ γ v) ∧ (∀ v ∈ V, γ v ∈ U) ∧ (∀ v ∈ V, h (γ v) = h x) ∧
      (∀ y ∈ U, h y = h x → C (y - x) ∈ V ∧ γ (C (y - x)) = y) := by
  classical
  -- package `h` as a map into `Fin 1 → ℝ`
  set Hk : (Fin d → ℝ) → (Fin 1 → ℝ) := fun y _ => h y with hHk
  have hHkan : AnalyticAt ℝ Hk x := by
    rw [hHk]
    exact analyticAt_pi_iff.mpr (fun _ : Fin 1 => hh)
  have hHkderiv : fderiv ℝ Hk x = ContinuousLinearMap.pi (fun _ : Fin 1 => fderiv ℝ h x) := by
    rw [hHk]
    exact fderiv_pi (fun _ : Fin 1 => hh.differentiableAt)
  have hsurj_h : (fderiv ℝ h x).range = ⊤ := range_eq_top_of_ne_zero hgrad
  have hHksurj : (fderiv ℝ Hk x).range = ⊤ := by
    rw [hHkderiv, Submodule.eq_top_iff']
    intro y
    have hyT : y 0 ∈ (fderiv ℝ h x).range := by rw [hsurj_h]; trivial
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hyT
    refine LinearMap.mem_range.mpr ⟨v, ?_⟩
    show (ContinuousLinearMap.pi (fun _ : Fin 1 => fderiv ℝ h x)) v = y
    funext i
    rw [ContinuousLinearMap.pi_apply]
    exact hv.trans (congrArg y (Subsingleton.elim i 0)).symm
  -- the analytic chart in the kernel model
  obtain ⟨γ₀, V₀, U, C₀, hV₀o, hUo, h0V₀, hxU, hγ₀0, hγ₀an, hγ₀U, hγ₀lvl, hχ₀⟩ :=
    levelSetChartV Hk x hHkan hHksurj
  -- the kernel has dimension `d - 1`
  have hfin : Module.finrank ℝ (fderiv ℝ Hk x).ker = d - 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker
      ((fderiv ℝ Hk x) : (Fin d → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
    rw [hHksurj, finrank_top] at h1
    simp only [Module.finrank_fin_fun] at h1
    omega
  haveI : CompleteSpace (fderiv ℝ Hk x).ker := (fderiv ℝ Hk x).isClosed_ker.completeSpace_coe
  let e : (Fin (d - 1) → ℝ) ≃L[ℝ] (fderiv ℝ Hk x).ker :=
    (LinearEquiv.ofFinrankEq (Fin (d - 1) → ℝ) (fderiv ℝ Hk x).ker
      (by rw [Module.finrank_fin_fun, hfin])).toContinuousLinearEquiv
  refine ⟨γ₀ ∘ ⇑e, ⇑e ⁻¹' V₀, U,
    ContinuousLinearMap.comp (ContinuousLinearEquiv.toContinuousLinearMap e.symm) C₀,
    hV₀o.preimage e.continuous, hUo, ?_, hxU, ?_, ?_, ?_, ?_, ?_⟩
  · show e 0 ∈ V₀
    rw [map_zero]
    exact h0V₀
  · show (γ₀ ∘ ⇑e) 0 = x
    rw [Function.comp_apply, map_zero, hγ₀0]
  · intro v hv
    exact (hγ₀an (e v) hv).comp
      (ContinuousLinearMap.analyticAt (e : (Fin (d - 1) → ℝ) →L[ℝ] (fderiv ℝ Hk x).ker) v)
  · intro v hv
    exact hγ₀U (e v) hv
  · intro v hv
    exact congrFun (hγ₀lvl (e v) hv) 0
  · intro y hy hyh
    have hyh' : Hk y = Hk x := by
      rw [hHk]
      funext i
      exact hyh
    obtain ⟨h1, h2⟩ := hχ₀ y hy hyh'
    refine ⟨?_, ?_⟩
    · show e (e.symm (C₀ (y - x))) ∈ V₀
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact h1
    · show γ₀ (e (e.symm (C₀ (y - x)))) = y
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact h2

/-! ## The reduction -/

theorem levelSetReductionH {d m j : ℕ} (hj : 2 ≤ j)
    (H : ∀ (d' : ℕ), d' < d → ∀ (F' : (Fin d' → ℝ) → (Fin m → ℝ)) (A' : Set (Fin d' → ℝ)),
      A' ⊆ flatCrit F' j → (∀ t ∈ A', AnalyticAt ℝ F' t) →
      ∀ x₀ ∈ A', ∃ δ > 0, MeasureTheory.volume (F' '' (A' ∩ Metric.ball x₀ δ)) = 0)
    (F : (Fin d → ℝ) → (Fin m → ℝ)) (A : Set (Fin d → ℝ))
    (hflat : A ⊆ flatSetV F (j - 1)) (hcrit : A ⊆ critSet F) (han : ∀ x ∈ A, AnalyticAt ℝ F x)
    (x : Fin d → ℝ) (hx : x ∈ A) (hxj : iteratedFDeriv ℝ j F x ≠ 0) :
    ∃ δ > 0, MeasureTheory.volume (F '' (A ∩ Metric.ball x δ)) = 0 := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- the target is a point: the critical set is empty, so `A` is empty
    subst hm0
    have hAempty : A = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      exact hcrit hy (fun b => ⟨0, funext fun i => i.elim0⟩)
    exact ⟨1, one_pos, by rw [hAempty, Set.empty_inter, Set.image_empty, measure_empty]⟩
  · -- `m ≥ 1`
    -- `j ≥ 2` puts `x` in the zero locus of the first derivative
    have hfd0 : fderiv ℝ F x = 0 := by
      have h1 : iteratedFDeriv ℝ 1 F x = 0 := hflat hx 1 le_rfl (by omega)
      refine ContinuousLinearMap.ext fun v => ?_
      have h2 : (iteratedFDeriv ℝ 1 F x) (fun _ : Fin 1 => v) = 0 := by
        rw [h1]
        simp
      simpa [iteratedFDeriv_one_apply] using h2
    -- the hypersurface function supplied by the first non-vanishing derivative
    have hnot : ¬ (∀ i, 1 ≤ i → iteratedFDeriv ℝ i F x = 0) :=
      fun hcon => hxj (hcon j (by omega))
    obtain ⟨J, g, B, hJ1, hBo, hxB, hBU, hgan, hg0, hgrad, hgvan, hgflat⟩ :=
      exists_local_hypersurface (f := F) (U := {y : Fin d → ℝ | AnalyticAt ℝ F y})
        (isOpen_analyticAt ℝ F) (fun y hy => hy.analyticWithinAt) (han x hx) hfd0 hnot
    -- `J` is the order at which the vanishing stops, so `J ≤ j - 1`
    have hJle : J ≤ j - 1 := by
      by_contra hcon
      exact hxj (hgflat j (by omega) (by omega))
    -- `g` vanishes on `A ∩ B`
    have hAz : ∀ y ∈ A ∩ B, g y = 0 := fun y hy =>
      hgvan y hy.2 (fun i hi hiJ => hflat hy.1 i hi (le_trans hiJ hJle))
    -- the analytic parametrisation of the level set `{g = g x}` near `x`
    obtain ⟨γ, V, Uc, C, hVo, hUco, h0V, hxUc, hγ0, hγan, hγU, hγlvl, hχ⟩ :=
      chart_of_regular_level g x (AnalyticOn.analyticAt (hBo.mem_nhds hxB) hgan) (hgrad x hxB)
    -- the ambient dimension is positive
    have hd1 : 1 ≤ d := by
      by_contra hcon
      have hd0 : d = 0 := by omega
      subst hd0
      refine hgrad x hxB (ContinuousLinearMap.ext fun v => ?_)
      haveI : Subsingleton (Fin 0 → ℝ) := ⟨fun a b => funext fun i => i.elim0⟩
      have hv : v = 0 := Subsingleton.elim v 0
      rw [hv]
      exact map_zero _
    -- the reduced data
    set F' : (Fin (d - 1) → ℝ) → (Fin m → ℝ) := F ∘ γ with hF'def
    set A' : Set (Fin (d - 1) → ℝ) := {t | γ t ∈ A} ∩ V with hA'def
    have hA'flat : A' ⊆ flatCrit F' j := by
      rw [hF'def]
      exact flatCrit_comp_subset hj hmpos hflat hcrit
        (fun t ht => ht.1) han (fun t ht => hγan t ht.2)
    have hA'an : ∀ t ∈ A', AnalyticAt ℝ F' t := by
      intro t ht
      rw [hF'def]
      exact (han (γ t) ht.1).comp (hγan t ht.2)
    have h0A' : (0 : Fin (d - 1) → ℝ) ∈ A' := by
      refine ⟨?_, h0V⟩
      show γ 0 ∈ A
      rw [hγ0]
      exact hx
    -- the induction hypothesis in dimension `d - 1`
    obtain ⟨δ', hδ'pos, hδ'null⟩ := H (d - 1) (by omega) F' A' hA'flat hA'an 0 h0A'
    -- a ball on which the chart recovers every point of `A`
    have hcont : Continuous fun y : Fin d → ℝ => C (y - x) :=
      C.continuous.comp (continuous_id.sub continuous_const)
    have hmem : (Uc ∩ B ∩ {y : Fin d → ℝ | C (y - x) ∈ Metric.ball 0 δ'}) ∈ 𝓝 x :=
      Filter.inter_mem (Filter.inter_mem (hUco.mem_nhds hxUc) (hBo.mem_nhds hxB))
        (hcont.continuousAt.preimage_mem_nhds (by
          rw [show C (x - x) = 0 from by rw [sub_self, map_zero]]
          exact Metric.ball_mem_nhds 0 hδ'pos))
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hmem
    refine ⟨ε, hεpos, ?_⟩
    refine measure_mono_null ?_ hδ'null
    rintro z ⟨y, ⟨hyA, hyb⟩, rfl⟩
    have hyUc : y ∈ Uc := (hεsub hyb).1.1
    have hyB : y ∈ B := (hεsub hyb).1.2
    have hyδ : C (y - x) ∈ Metric.ball 0 δ' := (hεsub hyb).2
    have hyh : g y = g x := by rw [hAz y ⟨hyA, hyB⟩, hg0]
    obtain ⟨hyV, hyγ⟩ := hχ y hyUc hyh
    refine ⟨C (y - x), ⟨⟨?_, hyV⟩, hyδ⟩, ?_⟩
    · show γ (C (y - x)) ∈ A
      rw [hyγ]
      exact hyA
    · show F (γ (C (y - x))) = F y
      rw [hyγ]

end Work.WilE9G.Sard
