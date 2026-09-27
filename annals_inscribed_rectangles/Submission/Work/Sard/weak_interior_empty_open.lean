import Mathlib
import Submission.Work.Sard.wp.Defs
import Submission.Work.Sard.holder_two_fderiv_eq_zero
import Submission.Work.Sard.holder_three_snd_fderiv_eq_zero
import Submission.Work.Sard.submersion_smooth
import Submission.Work.Sard.block_fderiv_prodMk
import Submission.Work.Embedding.isInvertible_adjoint_comp
import Submission.Work.Drive.sard_weak_empty_interior

universe u v

set_option maxHeartbeats 4000000

/-!
# Weak Sard: critical values of a smooth map `E → F`, `finrank E = finrank F + 1`, have empty interior

Target: `Work.Sard.weak_interior_empty_open`.  The proof is by strong induction on `finrank ℝ F`
(`Work.Sard.wp.WeakSard.all`), following the classical proof of Sard's theorem:

* on the stratum where the derivative does not vanish, the implicit function theorem writes `ρ`
  locally as `(w, c) ↦ (w, g w c)`, so that critical points correspond to critical points of the
  slice maps `c ↦ g w c`, whose target has smaller dimension — this is the induction step;
* on the stratum where the derivative vanishes, `ρ` is `2`-Hölder and the image has Hausdorff
  dimension at most `(finrank E)/2 < finrank F` when `finrank F ≥ 2`; for `finrank F = 1` the
  stratum is split further, using the `3`-Hölder estimate where the second derivative vanishes and
  the one-dimensional Sard theorem where it does not;
* the strata are assembled with a σ-compact exhaustion and Baire category.
-/

open scoped ContDiff Topology NNReal ENNReal
open MeasureTheory Set Filter

namespace Work.Sard.wp

/-! ### Localizing a globally proven Hölder estimate -/

/-- If two functions agree eventually at a point, they agree on an open neighbourhood. -/
theorem exists_isOpen_eq_of_eventuallyEq {E F : Type*} [TopologicalSpace E] {G ρ : E → F} {x : E}
    (h : G =ᶠ[𝓝 x] ρ) : ∃ A : Set E, IsOpen A ∧ x ∈ A ∧ ∀ y ∈ A, G y = ρ y := by
  obtain ⟨t, ht_sub, htop, hxt⟩ := mem_nhds_iff.mp h
  exact ⟨t, htop, hxt, fun y hy => ht_sub hy⟩

/-- **`2`-Hölder estimate on the flat stratum, local version.**  A map which is smooth on an open
set `U` is, near every point of `{fderiv ℝ ρ = 0} ∩ K` (`K ⊆ U`), `2`-Hölder along that set. -/
theorem holder_two_on_flat {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set E} (hU : IsOpen U) {ρ : E → F}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ U) {K : Set E} (hKU : K ⊆ U) :
    ∀ x ∈ {z : E | fderiv ℝ ρ z = 0} ∩ K,
      ∃ C : NNReal, ∃ t ∈ nhdsWithin x ({z : E | fderiv ℝ ρ z = 0} ∩ K),
        HolderOnWith C 2 ρ t := by
  intro x hx
  obtain ⟨hx0, hxK⟩ := hx
  obtain ⟨G, hGsm, hGeq⟩ :=
    Work.Sard.wp.exists_contDiff_eq_nhds_local ρ x U (hU.mem_nhds (hKU hxK)) hρ
  have hxG : fderiv ℝ G x = 0 := by rw [hGeq.fderiv_eq, hx0]
  obtain ⟨C, t, ht, hHt⟩ := Work.Sard.holder_two_fderiv_eq_zero G hGsm K x ⟨hxG, hxK⟩
  obtain ⟨A, hAopen, hxA, hAeq⟩ := Work.Sard.wp.exists_isOpen_eq_of_eventuallyEq hGeq
  have hfd : ∀ y ∈ A, fderiv ℝ G y = fderiv ℝ ρ y := by
    intro y hy
    exact Filter.EventuallyEq.fderiv_eq
      (Filter.eventuallyEq_of_mem (hAopen.mem_nhds hy) fun z hz => hAeq z hz)
  obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhdsWithin_iff.mp ht
  obtain ⟨ε', hε', hε'A⟩ := Metric.mem_nhds_iff.mp (hAopen.mem_nhds hxA)
  refine ⟨C, t ∩ A, ?_, ?_⟩
  · rw [Metric.mem_nhdsWithin_iff]
    refine ⟨min ε ε', lt_min hε hε', ?_⟩
    rintro y ⟨hball, hy0, hyK⟩
    have hyε : y ∈ Metric.ball x ε := Metric.ball_subset_ball (min_le_left _ _) hball
    have hyε' : y ∈ Metric.ball x ε' := Metric.ball_subset_ball (min_le_right _ _) hball
    have hyA : y ∈ A := hε'A hyε'
    have hyS : y ∈ {z : E | fderiv ℝ G z = 0} ∩ K := by
      refine ⟨?_, hyK⟩
      show fderiv ℝ G y = 0
      rw [hfd y hyA, hy0]
    exact ⟨hεt ⟨hyε, hyS⟩, hyA⟩
  · intro y hy y' hy'
    obtain ⟨hyt, hyA⟩ := hy
    obtain ⟨hy't, hy'A⟩ := hy'
    have hbound := hHt y hyt y' hy't
    rwa [hAeq y hyA, hAeq y' hy'A] at hbound

/-- **`3`-Hölder estimate on the doubly flat stratum, local version.** -/
theorem holder_three_on_flat {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set E} (hU : IsOpen U) {ρ : E → F}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ U) {K : Set E} (hKU : K ⊆ U) :
    ∀ x ∈ {z : E | fderiv ℝ ρ z = 0 ∧ fderiv ℝ (fun y => fderiv ℝ ρ y) z = 0} ∩ K,
      ∃ C : NNReal,
        ∃ t ∈ nhdsWithin x
            ({z : E | fderiv ℝ ρ z = 0 ∧ fderiv ℝ (fun y => fderiv ℝ ρ y) z = 0} ∩ K),
          HolderOnWith C 3 ρ t := by
  intro x hx
  obtain ⟨⟨hx0, hx1⟩, hxK⟩ := hx
  obtain ⟨G, hGsm, hGeq⟩ :=
    Work.Sard.wp.exists_contDiff_eq_nhds_local ρ x U (hU.mem_nhds (hKU hxK)) hρ
  have hxG : fderiv ℝ G x = 0 := by rw [hGeq.fderiv_eq, hx0]
  obtain ⟨A, hAopen, hxA, hAeq⟩ := Work.Sard.wp.exists_isOpen_eq_of_eventuallyEq hGeq
  have hfd : ∀ y ∈ A, fderiv ℝ G y = fderiv ℝ ρ y := by
    intro y hy
    exact Filter.EventuallyEq.fderiv_eq
      (Filter.eventuallyEq_of_mem (hAopen.mem_nhds hy) fun z hz => hAeq z hz)
  have h2fd : ∀ y ∈ A,
      fderiv ℝ (fun z => fderiv ℝ G z) y = fderiv ℝ (fun z => fderiv ℝ ρ z) y := by
    intro y hy
    exact Filter.EventuallyEq.fderiv_eq
      (Filter.eventuallyEq_of_mem (hAopen.mem_nhds hy) fun z hz => hfd z hz)
  have hxG1 : fderiv ℝ (fun y => fderiv ℝ G y) x = 0 := by
    rw [h2fd x hxA, hx1]
  obtain ⟨C, t, ht, hHt⟩ :=
    Work.Sard.holder_three_snd_fderiv_eq_zero G hGsm K x ⟨⟨hxG, hxG1⟩, hxK⟩
  obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhdsWithin_iff.mp ht
  obtain ⟨ε', hε', hε'A⟩ := Metric.mem_nhds_iff.mp (hAopen.mem_nhds hxA)
  refine ⟨C, t ∩ A, ?_, ?_⟩
  · rw [Metric.mem_nhdsWithin_iff]
    refine ⟨min ε ε', lt_min hε hε', ?_⟩
    rintro y ⟨hball, ⟨hy0, hy1⟩, hyK⟩
    have hyε : y ∈ Metric.ball x ε := Metric.ball_subset_ball (min_le_left _ _) hball
    have hyε' : y ∈ Metric.ball x ε' := Metric.ball_subset_ball (min_le_right _ _) hball
    have hyA : y ∈ A := hε'A hyε'
    have hyS : y ∈ {z : E | fderiv ℝ G z = 0 ∧ fderiv ℝ (fun y => fderiv ℝ G y) z = 0} ∩ K := by
      refine ⟨⟨?_, ?_⟩, hyK⟩
      · show fderiv ℝ G y = 0
        rw [hfd y hyA, hy0]
      · show fderiv ℝ (fun z => fderiv ℝ G z) y = 0
        rw [h2fd y hyA, hy1]
    exact ⟨hεt ⟨hyε, hyS⟩, hyA⟩
  · intro y hy y' hy'
    obtain ⟨hyt, hyA⟩ := hy
    obtain ⟨hy't, hy'A⟩ := hy'
    have hbound := hHt y hyt y' hy't
    rwa [hAeq y hyA, hAeq y' hy'A] at hbound

/-- **Flat stratum, `finrank ℝ F ≥ 2`.**  When the target has dimension at least `2`, the image of
the zero set of the derivative has empty interior (it has Hausdorff dimension at most
`(finrank ℝ F + 1)/2 < finrank ℝ F`). -/
theorem flat_image_interior_empty_of_two_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F + 1) (h2 : 2 ≤ Module.finrank ℝ F)
    {U : Set E} (hU : IsOpen U) {ρ : E → F}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ U) {K : Set E} (hKU : K ⊆ U) :
    interior (ρ '' ({z : E | fderiv ℝ ρ z = 0} ∩ K)) = ∅ := by
  rw [interior_eq_empty_iff_dense_compl]
  set S : Set E := {z : E | fderiv ℝ ρ z = 0} ∩ K with hS
  have hholder : ∀ x ∈ S, ∃ C : NNReal, ∃ t ∈ nhdsWithin x S, HolderOnWith C 2 ρ t :=
    holder_two_on_flat hU hρ hKU
  have h1 : dimH (ρ '' S) ≤ dimH S / (2 : ℝ≥0∞) :=
    dimH_image_le_of_locally_holder_on (by norm_num) hholder
  have h2' : dimH S ≤ (Module.finrank ℝ E : ℝ≥0∞) := by
    calc dimH S ≤ dimH (univ : Set E) := dimH_mono (subset_univ _)
      _ = (Module.finrank ℝ E : ℝ≥0∞) := Real.dimH_univ_eq_finrank E
  have harith : ((Module.finrank ℝ F + 1 : ℕ) : ℝ≥0∞) / 2 < (Module.finrank ℝ F : ℝ≥0∞) := by
    have hR : (((Module.finrank ℝ F + 1 : ℕ)) : ℝ) / 2 < ((Module.finrank ℝ F : ℕ) : ℝ) := by
      have : (2:ℝ) ≤ (Module.finrank ℝ F : ℝ) := by exact_mod_cast h2
      push_cast
      linarith
    have hNN : (((Module.finrank ℝ F + 1 : ℕ)) : ℝ≥0) / 2 < ((Module.finrank ℝ F : ℕ) : ℝ≥0) := by
      rw [← NNReal.coe_lt_coe]
      push_cast
      simpa using hR
    have hENN : ((((Module.finrank ℝ F + 1 : ℕ)) : ℝ≥0) : ℝ≥0∞) /
        (((2:ℝ≥0)) : ℝ≥0∞) < (((Module.finrank ℝ F : ℕ) : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.coe_div (by norm_num : (2:ℝ≥0) ≠ 0)]
      exact ENNReal.coe_lt_coe.mpr hNN
    simpa using hENN
  have hmid : dimH (ρ '' S) ≤ (Module.finrank ℝ E : ℝ≥0∞) / 2 :=
    le_trans h1 (ENNReal.div_le_div_right h2' 2)
  have h3 : dimH (ρ '' S) < (Module.finrank ℝ F : ℝ≥0∞) :=
    lt_of_le_of_lt hmid (by rw [hdim]; exact harith)
  exact dense_compl_of_dimH_lt_finrank h3






/-- The set of surjective continuous linear maps is open. -/
theorem isOpen_setOf_surjective_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] :
    IsOpen {L : E →L[ℝ] F | Function.Surjective L} := by
  have hset : {L : E →L[ℝ] F | Function.Surjective L}
      = ⋃ (S : F →L[ℝ] E), {L : E →L[ℝ] F | (L.comp S).IsInvertible} := by
    ext L
    constructor
    · intro hL
      obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective (L : E →ₗ[ℝ] F)
        (by rw [LinearMap.range_eq_top]; exact hL)
      refine Set.mem_iUnion.mpr ⟨LinearMap.toContinuousLinearMap g, ?_⟩
      have hcomp : L.comp (LinearMap.toContinuousLinearMap g) = ContinuousLinearMap.id ℝ F := by
        ext y
        exact congrFun (congrArg DFunLike.coe hg) y
      refine ⟨ContinuousLinearEquiv.refl ℝ F, ?_⟩
      rw [ContinuousLinearEquiv.coe_refl]
      exact hcomp.symm
    · intro hL
      obtain ⟨S, hS⟩ := Set.mem_iUnion.mp hL
      obtain ⟨e, he⟩ := hS
      intro y
      refine ⟨S (e.symm y), ?_⟩
      have h1 : L (S (e.symm y)) = y := by
        have h2 : (L.comp S) (e.symm y) = y := by
          rw [show L.comp S = (e : F →L[ℝ] F) from he.symm]
          exact e.apply_symm_apply y
        rwa [ContinuousLinearMap.comp_apply] at h2
      exact h1
  rw [hset]
  refine isOpen_iUnion fun S => ?_
  exact Work.Embedding.isOpen_isInvertible.preimage (continuous_id.clm_comp_const S)

/-- An open subset of a finite dimensional real normed space is a countable union of compact sets. -/
theorem exists_countable_compact_exhaust {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set E} (hU : IsOpen U) :
    ∃ K : ℕ → Set E, (∀ m, IsCompact (K m)) ∧ (∀ m, K m ⊆ U) ∧ (⋃ m, K m) = U := by
  refine ⟨fun m => {x : E | ‖x‖ ≤ (m : ℝ)} ∩ {x : E | ∀ y, y ∉ U → (1:ℝ) / (m + 1) ≤ ‖x - y‖},
    ?_, ?_, ?_⟩
  · intro m
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · have h1 : IsClosed {x : E | ‖x‖ ≤ (m : ℝ)} := by
        simpa only [Metric.closedBall, dist_eq_norm, sub_zero] using
          Metric.isClosed_closedBall (x := (0:E)) (ε := (m:ℝ))
      have h2 : IsClosed {x : E | ∀ y, y ∉ U → (1:ℝ)/(m+1) ≤ ‖x - y‖} := by
        have heq : {x : E | ∀ y, y ∉ U → (1:ℝ)/(m+1) ≤ ‖x - y‖}
            = ⋂ (y : E), ⋂ (_ : y ∉ U), {x : E | (1:ℝ)/(m+1) ≤ ‖x - y‖} := by
          ext x; simp only [Set.mem_ofPred_eq, Set.mem_iInter]
        rw [heq]
        exact isClosed_iInter fun y => isClosed_iInter fun _ =>
          isClosed_le continuous_const ((continuous_id.sub continuous_const).norm)
      exact h1.inter h2
    · refine (Metric.isBounded_closedBall (x := (0:E)) (r := (m:ℝ))).subset ?_
      intro x hx
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx.1
  · intro m x hx
    by_contra hxU
    have h := hx.2 x hxU
    have hpos : (0:ℝ) < (1:ℝ)/(m+1) := by positivity
    rw [sub_self, norm_zero] at h
    linarith
  · ext x
    constructor
    · intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨m, hm⟩ := hx
      by_contra hxU
      have h := hm.2 x hxU
      have hpos : (0:ℝ) < (1:ℝ)/(m+1) := by positivity
      rw [sub_self, norm_zero] at h
      linarith
    · intro hxU
      rw [Set.mem_iUnion]
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
      have hdist : ∀ y, y ∉ U → r ≤ ‖x - y‖ := by
        intro y hy
        by_contra hlt
        rw [not_le] at hlt
        exact hy (hball (by rw [Metric.mem_ball, dist_comm, dist_eq_norm]; exact hlt))
      obtain ⟨m, hm⟩ := exists_nat_ge (max ‖x‖ (1/r + 1))
      refine ⟨m, ?_, ?_⟩
      · exact le_trans (le_max_left _ _) hm
      · intro y hy
        have h2 : 1/r + 1 ≤ (m:ℝ) := le_trans (le_max_right _ _) hm
        have h3 : (1:ℝ) < r * ((m:ℝ)+1) := by
          have h4 : (1:ℝ)/r < (m:ℝ) + 1 := by linarith
          have := (div_lt_iff₀ hr).mp h4
          linarith
        have h5 : (1:ℝ)/((m:ℝ)+1) ≤ r := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < (m:ℝ)+1)]
          linarith
        exact le_trans h5 (hdist y hy)

/-- If `y ∈ L.range` then the second component of the splitting `L.range × M ≃ F` at `y` is `0`. -/
lemma prodEquiv_symm_snd_of_mem {F : Type*} [AddCommGroup F] [Module ℝ F]
    {L : F →ₗ[ℝ] F} (M : Submodule ℝ F) (hM : IsCompl L.range M) {y : F} (hy : y ∈ L.range) :
    ((Submodule.prodEquivOfIsCompl L.range M hM).symm y).2 = 0 := by
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hy
  have h := Submodule.prodEquivOfIsCompl_symm_apply_left L.range M hM ⟨L v, ⟨v, rfl⟩⟩
  exact congrArg Prod.snd h


/-! ### The local model at a point where the derivative does not vanish -/

/-- **Local model.**  If `fderiv ℝ ρ z ≠ 0` then near `z` the critical values of `ρ` have empty
interior. -/
theorem local_model_rank_ge_one {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hE : Module.finrank ℝ E = Module.finrank ℝ F + 1)
    {U : Set E} (hU : IsOpen U) {ρ : E → F}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ U) {z : E} (hz : z ∈ U)
    (hL : fderiv ℝ ρ z ≠ 0)
    (IH : ∀ m : ℕ, m < Module.finrank ℝ F → WeakSard.{u, v} m) :
    ∃ V : Set E, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
      interior (ρ '' ({y : E | y ∈ closure V ∧
        ¬ Function.Surjective (fderivWithin ℝ ρ U y)})) = ∅ := by
  classical
  -- ### Step 1: globalize `ρ` near `z`
  obtain ⟨G, hGsm, hGeq⟩ := exists_contDiff_eq_nhds_local ρ z U (hU.mem_nhds hz) hρ
  obtain ⟨A, hAopen, hzA, hAeq⟩ := exists_isOpen_eq_of_eventuallyEq hGeq
  -- ### Step 2: the derivative at `z`
  set L : E →L[ℝ] F := fderiv ℝ ρ z with hLset
  have hLG : fderiv ℝ G z = L := by
    rw [hLset]
    exact Filter.EventuallyEq.fderiv_eq hGeq
  have hLne : L ≠ 0 := by simpa only [hLset] using hL
  -- ### Step 3: the splitting `F ≃ L.range × M`
  obtain ⟨M, hM⟩ := Submodule.exists_isCompl L.range
  let pr : F →ₗ[ℝ] ↥L.range := Submodule.projectionOnto L.range M hM
  let e₀ : F ≃ₗ[ℝ] (↥L.range × ↥M) := (Submodule.prodEquivOfIsCompl L.range M hM).symm
  have he₁ : ∀ y : F, (e₀ y).1 = pr y := fun y => rfl
  have he₂zero : ∀ y : F, y ∈ L.range → (e₀ y).2 = 0 := by
    intro y hy
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hy
    have hv' : L v = y := hv
    rw [← hv']
    exact congrArg Prod.snd
      (Submodule.prodEquivOfIsCompl_symm_apply_left L.range M hM ⟨L v, ⟨v, rfl⟩⟩)
  have hpr_left : ∀ v : ↥L.range, pr (v : F) = v := fun v => Submodule.projectionOnto_apply_left hM v
  have hpr_zero : ∀ y : F, pr y = 0 ↔ y ∈ M := fun y => Submodule.projectionOnto_apply_eq_zero_iff hM
  let eC : F →L[ℝ] (↥L.range × ↥M) := LinearMap.toContinuousLinearMap e₀.toLinearMap
  let eI : (↥L.range × ↥M) →L[ℝ] F := LinearMap.toContinuousLinearMap e₀.symm.toLinearMap
  have hEC : ∀ y : F, eC y = e₀ y := fun y => rfl
  have hEI : ∀ y : (↥L.range × ↥M), eI y = e₀.symm y := fun y => rfl
  have hECsurj : Function.Surjective eC := fun y => ⟨eI y, by
    show eC (eI y) = y
    rw [hEC, hEI]
    simp⟩
  -- ### Step 4: `u = pr ∘ G` is a submersion at `z`
  let prc : F →L[ℝ] ↥L.range := LinearMap.toContinuousLinearMap pr
  have hprc : ∀ y : F, prc y = pr y := fun y => rfl
  let u : E → ↥L.range := prc ∘ G
  have hu_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u := prc.contDiff.comp hGsm
  have hdu : fderiv ℝ u z = prc.comp L := by
    have h1 : HasFDerivAt G L z := by
      rw [← hLG]; exact (hGsm.differentiable (by simp)).differentiableAt.hasFDerivAt
    exact (prc.hasFDerivAt.comp z h1).fderiv
  have hdu_surj : Function.Surjective (fderiv ℝ u z) := by
    rw [hdu]
    intro w
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp w.2
    have hv' : L v = (w : F) := hv
    refine ⟨v, ?_⟩
    show prc (L v) = w
    rw [hv', hprc]
    exact hpr_left w
  -- ### Step 5: the submersion parametrisation
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (fderiv ℝ u z).ker
  obtain ⟨Φ, O, hOopen, hObase, hΦsm, hΦu, hΦbase, hΦinv⟩ :=
    Work.Sard.submersion_smooth u hu_sm z hdu_surj C hC
  -- ### Step 6: the model map
  let κ : E →L[ℝ] ↥((fderiv ℝ u z).ker) :=
    LinearMap.toContinuousLinearMap (Submodule.projectionOnto (fderiv ℝ u z).ker C hC)
  have hκc : ∀ y : E, κ y = (Submodule.projectionOnto (fderiv ℝ u z).ker C hC) y := fun y => rfl
  have hκ_left : ∀ v : ↥((fderiv ℝ u z).ker), κ (v : E) = v := by
    intro v; rw [hκc]; exact Submodule.projectionOnto_apply_left hC v
  have hκ_zero : ∀ v : ↥C, κ (v : E) = 0 := by
    intro v; rw [hκc]; exact (Submodule.projectionOnto_apply_eq_zero_iff hC).mpr v.2
  let Θ : E → (↥L.range × ↥((fderiv ℝ u z).ker)) := fun x => (u x, κ x)
  have hΘ_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ := hu_sm.prodMk κ.contDiff
  have hΘ_cont : Continuous Θ := hΘ_sm.continuous
  have hnhds2 : {x : E | Θ x ∈ O} ∈ 𝓝 z :=
    (hOopen.preimage hΘ_cont).mem_nhds (by
      show Θ z ∈ O
      rw [show Θ z = (u z, (Submodule.projectionOnto (fderiv ℝ u z).ker C hC) z) from rfl]
      exact hObase)
  obtain ⟨Ω₀, hΩ₀sub, hΩ₀open, hzΩ₀⟩ :=
    mem_nhds_iff.mp (Filter.inter_mem hΦinv hnhds2)
  have hΩ₀1 : ∀ x ∈ Ω₀, Φ (Θ x) = x := fun x hx => (hΩ₀sub hx).1
  have hΩ₀2 : ∀ x ∈ Ω₀, Θ x ∈ O := fun x hx => (hΩ₀sub hx).2
  -- ### Step 7: points where `fderiv ℝ u` restricted to `C` is invertible
  let Z : Set E := {x : E | ((fderiv ℝ u x).comp C.subtypeL).IsInvertible}
  have hZopen : IsOpen Z := by
    have hcont : Continuous (fun x : E => (fderiv ℝ u x).comp C.subtypeL) :=
      (hu_sm.continuous_fderiv (by simp)).clm_comp_const C.subtypeL
    exact hcont.isOpen_preimage _ Work.Embedding.isOpen_isInvertible
  have hker_eq : (fderiv ℝ u z).ker = L.ker := by
    rw [hdu]
    ext v
    change (prc ∘L L) v = 0 ↔ L v = 0
    rw [ContinuousLinearMap.comp_apply, hprc]
    constructor
    · intro hv
      have h1 : L v ∈ M := (hpr_zero (L v)).mp hv
      have h2 : L v ∈ L.range := ⟨v, rfl⟩
      have h3 : L v ∈ L.range ⊓ M := ⟨h2, h1⟩
      rw [hM.inf_eq_bot, Submodule.mem_bot] at h3
      exact h3
    · intro hv; rw [hv, map_zero]
  have hC' : IsCompl L.ker C := by rw [← hker_eq]; exact hC
  have hzZ : z ∈ Z := by
    show ((fderiv ℝ u z).comp C.subtypeL).IsInvertible
    have hφ : (fderiv ℝ u z).comp C.subtypeL = prc.comp (L.comp C.subtypeL) := by
      rw [hdu, ContinuousLinearMap.comp_assoc]
    rw [hφ]
    have hinj : Function.Injective (prc.comp (L.comp C.subtypeL) : ↥C →L[ℝ] ↥L.range) := by
      intro u1 u2 huv
      have hsub : (u1 - u2 : ↥C) = 0 := by
        have h0 : prc (L (((u1 - u2 : ↥C)) : E)) = 0 := by
          have h1 : (prc.comp (L.comp C.subtypeL)) (u1 - u2) = 0 := by
            rw [map_sub, huv, sub_self]
          simpa using h1
        have h1 : L (((u1 - u2 : ↥C)) : E) ∈ M := (hpr_zero _).mp h0
        have h2 : L (((u1 - u2 : ↥C)) : E) ∈ L.range := ⟨((u1 - u2 : ↥C) : E), rfl⟩
        have h3 : L (((u1 - u2 : ↥C)) : E) ∈ L.range ⊓ M := ⟨h2, h1⟩
        rw [hM.inf_eq_bot, Submodule.mem_bot] at h3
        have h4 : (((u1 - u2 : ↥C)) : E) ∈ L.ker ⊓ C := ⟨h3, (u1 - u2).2⟩
        rw [hC'.inf_eq_bot, Submodule.mem_bot] at h4
        exact Subtype.ext h4
      exact sub_eq_zero.mp hsub
    have hdimC : Module.finrank ℝ ↥C = Module.finrank ℝ ↥L.range := by
      have h1 : Module.finrank ℝ ↥L.range + Module.finrank ℝ ↥L.ker = Module.finrank ℝ E :=
        LinearMap.finrank_range_add_finrank_ker L.toLinearMap
      have h2 : Module.finrank ℝ ↥L.ker + Module.finrank ℝ ↥C = Module.finrank ℝ E :=
        Submodule.finrank_add_eq_of_isCompl hC'
      omega
    have hsurj : Function.Surjective (prc.comp (L.comp C.subtypeL) : ↥C →L[ℝ] ↥L.range) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := (prc.comp (L.comp C.subtypeL) : ↥C →ₗ[ℝ] ↥L.range)) hdimC).mp hinj
    refine ⟨ContinuousLinearEquiv.ofBijective
      (prc.comp (L.comp C.subtypeL) : ↥C →L[ℝ] ↥L.range) ?_ ?_, ?_⟩
    · exact LinearMap.ker_eq_bot.mpr hinj
    · exact LinearMap.range_eq_top.mpr hsurj
    · exact (ContinuousLinearEquiv.coe_ofBijective
        (prc.comp (L.comp C.subtypeL) : ↥C →L[ℝ] ↥L.range)
        (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)).symm
  -- ### Step 8: the neighbourhood `V`
  let Ω : Set E := Ω₀ ∩ A ∩ Z ∩ U
  have hΩopen : IsOpen Ω := ((hΩ₀open.inter hAopen).inter hZopen).inter hU
  have hzΩ : z ∈ Ω := ⟨⟨⟨hzΩ₀, hzA⟩, hzZ⟩, hz⟩
  obtain ⟨r, hr, hrΩ⟩ : ∃ r > 0, Metric.closedBall z r ⊆ Ω := by
    obtain ⟨r, hr, hr'⟩ := Metric.mem_nhds_iff.mp (hΩopen.mem_nhds hzΩ)
    exact ⟨r/2, by positivity, fun x hx => hr' (Metric.closedBall_subset_ball (by linarith) hx)⟩
  refine ⟨Metric.ball z r, Metric.isOpen_ball, Metric.mem_ball_self hr, ?_, ?_⟩
  · intro x hx
    exact (hrΩ (Metric.ball_subset_closedBall hx)).2
  · -- ### Step 9: the criticality transfer
    let g : (↥L.range × ↥((fderiv ℝ u z).ker)) → ↥M := fun y => (e₀ (G (Φ y))).2
    let Ψ : (↥L.range × ↥((fderiv ℝ u z).ker)) → (↥L.range × ↥M) := fun y => (y.1, g y)
    have hgm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g O := by
      have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => G (Φ y)) O :=
        hGsm.comp_contDiffOn hΦsm
      have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => e₀ (G (Φ y))) O :=
        (LinearMap.toContinuousLinearMap e₀.toLinearMap).contDiff.comp_contDiffOn h1
      exact (ContinuousLinearMap.snd ℝ (↥L.range) (↥M)).contDiff.comp_contDiffOn h2
    have hΨ_eq : ∀ x ∈ Ω, e₀ (ρ x) = Ψ (Θ x) := by
      intro x hx
      obtain ⟨⟨⟨hxΩ₀, hxA⟩, hxZ⟩, hxU⟩ := hx
      have h1 : (e₀ (ρ x)).1 = u x := by
        rw [he₁]
        show pr (ρ x) = prc (G x)
        rw [hAeq x hxA, hprc]
      have h2 : (e₀ (ρ x)).2 = g (Θ x) := by
        have hΦx : Φ (Θ x) = x := hΩ₀1 x hxΩ₀
        have hρ : ρ x = G (Φ (Θ x)) := by rw [hΦx]; exact (hAeq x hxA).symm
        rw [hρ]
      exact Prod.ext h1 h2
    have hΘ_surj : ∀ x ∈ Z, Function.Surjective (fderiv ℝ Θ x) := by
      intro x hxZ
      obtain ⟨eCx : ↥C ≃L[ℝ] ↥L.range, heCx⟩ := hxZ
      have hdΘ : fderiv ℝ Θ x = (fderiv ℝ u x).prod κ := by
        have h1 : HasFDerivAt (fun y : E => (u y, κ y)) ((fderiv ℝ u x).prod κ) x :=
          ((hu_sm.differentiable (by simp)).differentiableAt.hasFDerivAt).prodMk κ.hasFDerivAt
        have h2 : (fun y : E => (u y, κ y)) = Θ := rfl
        rw [← h2]
        exact h1.fderiv
      rw [hdΘ]
      rintro ⟨a, b⟩
      let c : ↥C := eCx.symm (a - fderiv ℝ u x (b : E))
      have hc : eCx c = a - fderiv ℝ u x (b : E) := by
        show eCx (eCx.symm _) = _
        rw [ContinuousLinearEquiv.apply_symm_apply]
      have hc' : (fderiv ℝ u x) ((c : E)) = (eCx : ↥C →L[ℝ] ↥L.range) c := by
        have h : ((fderiv ℝ u x).comp C.subtypeL) c = (eCx : ↥C →L[ℝ] ↥L.range) c := by
          rw [heCx.symm]
        simpa using h
      refine ⟨(c : E) + (b : E), ?_⟩
      rw [ContinuousLinearMap.prod_apply, map_add, map_add, hκ_zero c, hκ_left b, zero_add, hc']
      refine Prod.ext ?_ rfl
      show eCx c + (fderiv ℝ u x) (b : E) = a
      rw [hc]
      abel
    have htransfer : ∀ x ∈ Ω,
        (¬ Function.Surjective (fderivWithin ℝ ρ U x)) ↔
          ¬ Function.Surjective (fderiv ℝ Ψ (Θ x)) := by
      intro x hx
      obtain ⟨⟨⟨hxΩ₀, hxA⟩, hxZ⟩, hxU⟩ := hx
      have hxU' : fderivWithin ℝ ρ U x = fderiv ℝ ρ x :=
        fderivWithin_of_mem_nhds (hU.mem_nhds hxU)
      have hρdiff : HasFDerivAt ρ (fderiv ℝ ρ x) x :=
        (hρ.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp) |>.hasFDerivAt
      have hderiv1 : fderiv ℝ (e₀ ∘ ρ) x = eC.comp (fderiv ℝ ρ x) := by
        have h2 : HasFDerivAt (e₀ : F → (↥L.range × ↥M)) eC (ρ x) := by
          change HasFDerivAt eC eC (ρ x)
          exact eC.hasFDerivAt
        exact (h2.comp x hρdiff).fderiv
      have hderiv2 : fderiv ℝ (Ψ ∘ Θ) x
          = (fderiv ℝ Ψ (Θ x)).comp (fderiv ℝ Θ x) := by
        have h1 : HasFDerivAt Θ (fderiv ℝ Θ x) x :=
          (hΘ_sm.differentiable (by simp)).differentiableAt.hasFDerivAt
        have hg' : HasFDerivAt g (fderiv ℝ g (Θ x)) (Θ x) :=
          ((hgm.contDiffAt (hOopen.mem_nhds (hΩ₀2 x hxΩ₀))).differentiableAt (by simp)).hasFDerivAt
        have hfst : HasFDerivAt (fun y : (↥L.range × ↥((fderiv ℝ u z).ker)) => y.1)
            (ContinuousLinearMap.fst ℝ (↥L.range) (↥((fderiv ℝ u z).ker))) (Θ x) :=
          ContinuousLinearMap.hasFDerivAt
            (ContinuousLinearMap.fst ℝ (↥L.range) (↥((fderiv ℝ u z).ker)))
        have h2 : HasFDerivAt Ψ (fderiv ℝ Ψ (Θ x)) (Θ x) := by
          have h3 : HasFDerivAt Ψ
              ((ContinuousLinearMap.fst ℝ (↥L.range) (↥((fderiv ℝ u z).ker))).prod
                (fderiv ℝ g (Θ x))) (Θ x) := hfst.prodMk hg'
          rw [h3.fderiv]
          exact h3
        exact (h2.comp x h1).fderiv
      have heq : eC.comp (fderiv ℝ ρ x) = (fderiv ℝ Ψ (Θ x)).comp (fderiv ℝ Θ x) := by
        rw [← hderiv1, ← hderiv2]
        exact Filter.EventuallyEq.fderiv_eq (by
          filter_upwards [hΩopen.mem_nhds ⟨⟨⟨hxΩ₀, hxA⟩, hxZ⟩, hxU⟩] with y hy
          exact hΨ_eq y hy)
      have hsurjΘ : Function.Surjective (fderiv ℝ Θ x) := hΘ_surj x hxZ
      have hsurj_eC : Function.Surjective (eC.comp (fderiv ℝ ρ x)) ↔
          Function.Surjective (fderiv ℝ ρ x) :=
        ⟨fun h y => by
          obtain ⟨v, hv⟩ := h (eC y)
          refine ⟨v, e₀.injective ?_⟩
          rw [hEC] at hv
          rwa [ContinuousLinearMap.comp_apply] at hv,
         fun h => hECsurj.comp h⟩
      have hsurj_comp : Function.Surjective ((fderiv ℝ Ψ (Θ x)).comp (fderiv ℝ Θ x)) ↔
          Function.Surjective (fderiv ℝ Ψ (Θ x)) :=
        ⟨fun h y => by
          obtain ⟨v, hv⟩ := h y
          exact ⟨(fderiv ℝ Θ x) v, by rw [← hv, ContinuousLinearMap.comp_apply]⟩,
         fun h => h.comp hsurjΘ⟩
      rw [hxU']
      exact (not_congr hsurj_eC.symm).trans
        ((not_congr (by rw [heq])).trans (not_congr hsurj_comp))
    -- ### the slice maps and their critical value sets
    let Ow : ↥L.range → Set ↥((fderiv ℝ u z).ker) := fun w => {c | (w, c) ∈ O}
    let gw : ↥L.range → ↥((fderiv ℝ u z).ker) → ↥M :=
      fun w c => if (w, c) ∈ O then g (w, c) else 0
    have hgw_eq : ∀ (w : ↥L.range) (c : ↥((fderiv ℝ u z).ker)), (w, c) ∈ O →
        gw w c = g (w, c) := fun w c hc => by simp only [gw, if_pos hc]
    have hOw : ∀ w, IsOpen (Ow w) := fun w =>
      hOopen.preimage (continuous_const.prodMk continuous_id)
    have hgw_sm : ∀ w, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gw w) (Ow w) := by
      intro w
      have hslice : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun c : ↥((fderiv ℝ u z).ker) => g (w, c)) (Ow w) := by
        have hproj : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun c : ↥((fderiv ℝ u z).ker) => (w, c)) (Ow w) :=
          contDiffOn_const.prodMk contDiffOn_id
        exact hgm.comp hproj (fun c hc => hc)
      exact hslice.congr (fun c hc => hgw_eq w c hc)
    let N : ↥L.range → Set ↥M := fun w => gw w '' (Ow w ∩
      {c : ↥((fderiv ℝ u z).ker) | ¬ Function.Surjective (fderivWithin ℝ (gw w) (Ow w) c)})
    have hNempty : ∀ w, interior (N w) = ∅ := by
      intro w
      have hdimK : Module.finrank ℝ ↥((fderiv ℝ u z).ker) = Module.finrank ℝ ↥M + 1 := by
        have h1' : Module.finrank ℝ ↥(fderiv ℝ u z).range +
            Module.finrank ℝ ↥(fderiv ℝ u z).ker = Module.finrank ℝ E :=
          LinearMap.finrank_range_add_finrank_ker (fderiv ℝ u z).toLinearMap
        have h1 : Module.finrank ℝ ↥(fderiv ℝ u z).ker +
            Module.finrank ℝ ↥(fderiv ℝ u z).range = Module.finrank ℝ E := by
          rw [add_comm]; exact h1'
        have h2 : (fderiv ℝ u z).range = ⊤ := LinearMap.range_eq_top.mpr hdu_surj
        have h4 : Module.finrank ℝ ↥(fderiv ℝ u z).range = Module.finrank ℝ ↥L.range := by
          rw [h2]
          exact (Submodule.topEquiv (R := ℝ) (M := ↥L.range)).finrank_eq
        have h5 : Module.finrank ℝ ↥L.range + Module.finrank ℝ ↥M = Module.finrank ℝ F :=
          Submodule.finrank_add_eq_of_isCompl hM
        omega
      have hlt : Module.finrank ℝ ↥M < Module.finrank ℝ F := by
        have hpos : 1 ≤ Module.finrank ℝ ↥L.range := by
          by_contra hcon
          push_neg at hcon
          have hzero : Module.finrank ℝ ↥L.range = 0 := by omega
          rw [Submodule.finrank_eq_zero] at hzero
          refine hLne ?_
          ext v
          have : L v ∈ (⊥ : Submodule ℝ F) := by rw [← hzero]; exact ⟨v, rfl⟩
          simpa using this
        have h5 : Module.finrank ℝ ↥L.range + Module.finrank ℝ ↥M = Module.finrank ℝ F :=
          Submodule.finrank_add_eq_of_isCompl hM
        omega
      exact IH (Module.finrank ℝ ↥M) hlt ↥((fderiv ℝ u z).ker) ↥M rfl hdimK
        (Ow w) (hOw w) (gw w) (hgw_sm w)
    have htube : interior (⋃ w : ↥L.range, ({w} : Set ↥L.range) ×ˢ N w) = ∅ :=
      interior_iUnion_slices_eq_empty N hNempty
    -- ### the image of the critical set is contained in the slices
    have himg : e₀ '' (ρ '' (Ω ∩ {y : E | ¬ Function.Surjective (fderivWithin ℝ ρ U y)}))
        ⊆ ⋃ w : ↥L.range, ({w} : Set ↥L.range) ×ˢ N w := by
      rintro y ⟨z₀, ⟨x, ⟨hxΩ, hxK⟩, hxz⟩, hzy⟩
      have hy : y = e₀ (ρ x) := by rw [← hzy, hxz]
      rw [hy]
      have hΨx : ¬ Function.Surjective (fderiv ℝ Ψ (Θ x)) := (htransfer x hxΩ).mp hxK
      have hdiffg : DifferentiableAt ℝ g (Θ x) :=
        ((hgm.contDiffAt (hOopen.mem_nhds (hΩ₀2 x hxΩ.1.1.1))).differentiableAt (by simp))
      have hΨx' : ¬ Function.Surjective
          (fderiv ℝ (fun w : (↥L.range × ↥((fderiv ℝ u z).ker)) => (w.1, g w)) (Θ x)) := hΨx
      have hslice : ¬ Function.Surjective (fderiv ℝ (fun c => g ((Θ x).1, c)) (Θ x).2) :=
        fun hs => hΨx' ((Work.Sard.block_fderiv_prodMk g (Θ x) hdiffg).mpr hs)
      have hΘO : Θ x ∈ O := hΩ₀2 x hxΩ.1.1.1
      have hcrit' : ¬ Function.Surjective
          (fderivWithin ℝ (fun c => g ((Θ x).1, c)) (Ow (Θ x).1) (Θ x).2) := by
        rw [fderivWithin_of_mem_nhds ((hOw _).mem_nhds hΘO)]
        exact hslice
      have hconge : fderivWithin ℝ (gw (Θ x).1) (Ow (Θ x).1) (Θ x).2
          = fderivWithin ℝ (fun c => g ((Θ x).1, c)) (Ow (Θ x).1) (Θ x).2 :=
        fderivWithin_congr (fun c hc => hgw_eq (Θ x).1 c hc)
          (hgw_eq (Θ x).1 (Θ x).2 hΘO)
      have hcrit : ¬ Function.Surjective
          (fderivWithin ℝ (gw (Θ x).1) (Ow (Θ x).1) (Θ x).2) := by
        rw [hconge]
        exact hcrit'
      refine Set.mem_iUnion.mpr ⟨(Θ x).1, ?_⟩
      refine ⟨?_, ?_⟩
      · simpa using congrArg Prod.fst (hΨ_eq x hxΩ)
      · refine ⟨(Θ x).2, ⟨hΘO, hcrit⟩, ?_⟩
        rw [hgw_eq (Θ x).1 (Θ x).2 hΘO]
        exact (congrArg Prod.snd (hΨ_eq x hxΩ)).symm
    -- ### conclusion
    let eh : F ≃ₜ (↥L.range × ↥M) :=
      { toFun := eC
        invFun := eI
        left_inv := fun y => by rw [hEC, hEI]; simp
        right_inv := fun y => by rw [hEC, hEI]; simp
        continuous_toFun := eC.continuous
        continuous_invFun := eI.continuous }
    have hmain : interior (ρ '' (Ω ∩ {y : E |
        ¬ Function.Surjective (fderivWithin ℝ ρ U y)})) = ∅ := by
      let eh : F ≃ₜ (↥L.range × ↥M) :=
        { toFun := eC
          invFun := eI
          left_inv := fun y => by rw [hEC, hEI]; simp
          right_inv := fun y => by rw [hEC, hEI]; simp
          continuous_toFun := eC.continuous
          continuous_invFun := eI.continuous }
      have himg' : eC '' (ρ '' (Ω ∩ {y : E |
          ¬ Function.Surjective (fderivWithin ℝ ρ U y)}))
          ⊆ ⋃ w : ↥L.range, ({w} : Set ↥L.range) ×ˢ N w := by
        rw [show eC = (e₀ : F → (↥L.range × ↥M)) from funext hEC]
        exact himg
      have h1 : interior (eC '' (ρ '' (Ω ∩ {y : E |
          ¬ Function.Surjective (fderivWithin ℝ ρ U y)}))) = ∅ := by
        refine eq_empty_of_subset_empty ?_
        rw [← htube]
        exact interior_mono himg'
      have h2 : eh '' (ρ '' (Ω ∩ {y : E | ¬ Function.Surjective (fderivWithin ℝ ρ U y)})) =
          eC '' (ρ '' (Ω ∩ {y : E | ¬ Function.Surjective (fderivWithin ℝ ρ U y)})) := rfl
      rw [← h2, ← Homeomorph.image_interior] at h1
      have h4 : eh.symm '' (eh '' interior (ρ '' (Ω ∩ {y : E |
          ¬ Function.Surjective (fderivWithin ℝ ρ U y)})))
          = interior (ρ '' (Ω ∩ {y : E | ¬ Function.Surjective (fderivWithin ℝ ρ U y)})) := by
        rw [Set.image_image,
          show (fun x => eh.symm (eh x)) = id from funext fun x => eh.symm_apply_apply x,
          Set.image_id]
      rw [show interior (ρ '' (Ω ∩ {y : E | ¬ Function.Surjective (fderivWithin ℝ ρ U y)})) =
          eh.symm '' (eh '' interior (ρ '' (Ω ∩ {y : E |
            ¬ Function.Surjective (fderivWithin ℝ ρ U y)}))) from h4.symm, h1, Set.image_empty]
    have hpiece : ρ '' ({y : E | y ∈ closure (Metric.ball z r) ∧
        ¬ Function.Surjective (fderivWithin ℝ ρ U y)}) ⊆
        ρ '' (Ω ∩ {y : E | ¬ Function.Surjective (fderivWithin ℝ ρ U y)}) := by
      refine Set.image_mono ?_
      rintro y ⟨hy, hyK⟩
      rw [closure_ball z hr.ne'] at hy
      exact ⟨hrΩ hy, hyK⟩
    exact eq_empty_of_subset_empty
      ((interior_mono hpiece).trans (by rw [hmain]))

/-! ### Assembly of the weak Sard theorem on an open set

The local model `local_model_rank_ge_one` and the flat stratum estimates (`flat_finrank_one`,
`flat_image_interior_empty_of_two_le`) give the weak Sard statement on a *compact* subset of the
open set `U`; a `σ`-compact exhaustion of `U` together with Baire category
(`interior_eq_empty_iUnion_isClosed`) then gives it on all of `U`. -/

/-- If `K` is compact and every point of `K` outside `S` has a neighbourhood disjoint from `S`,
then `K ∩ S` is compact (indeed `K ∩ S = K ∩ closure S`). -/
lemma isCompact_inter_of_eventually_not {X : Type*} [TopologicalSpace X] {K S : Set X}
    (hK : IsCompact K) (h : ∀ z ∈ K, z ∉ S → ∀ᶠ w in 𝓝 z, w ∉ S) : IsCompact (S ∩ K) := by
  have hsub : S ∩ K = closure S ∩ K := by
    ext z
    constructor
    · rintro ⟨hzS, hzK⟩
      exact ⟨subset_closure hzS, hzK⟩
    · rintro ⟨hzcl, hzK⟩
      refine ⟨?_, hzK⟩
      by_contra hzS
      obtain ⟨w, hw1, hw2⟩ := mem_closure_iff_nhds.mp hzcl {w | w ∉ S} (h z hzK hzS)
      exact hw1 hw2
  rw [hsub]
  exact hK.inter_left isClosed_closure

/-- The derivative of a map smooth on an open set is continuous at every point of that set. -/
lemma continuousAt_fderiv_of_contDiffOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {ρ : E → F}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ U) {z : E} (hz : z ∈ U) :
    ContinuousAt (fun z : E => fderiv ℝ ρ z) z :=
  (hρ.continuousOn_fderiv_of_isOpen hU (by simp)).continuousAt (hU.mem_nhds hz)

/-- **Flat stratum, target dimension one.**  The image of the zero set of the derivative has empty
interior.  Near every point of the compact set `K` the map `ρ` agrees with a globally smooth map, to
which the one-dimensional Hausdorff dimension analysis `Work.Drive.flat_case_one` applies. -/
theorem flat_finrank_one {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hE : Module.finrank ℝ E = Module.finrank ℝ F + 1) (hF₁ : Module.finrank ℝ F = 1)
    (U : Set E) (hU : IsOpen U) (ρ : E → F)
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ U)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U) :
    interior (ρ '' ({z : E | fderiv ℝ ρ z = 0} ∩ K)) = ∅ := by
  classical
  have hE2 : Module.finrank ℝ E = 2 := by omega
  set Sf : Set E := {z : E | fderiv ℝ ρ z = 0} with hSf
  -- at each point of `K`, `ρ` agrees with a globally smooth map on a ball
  have hloc : ∀ x : ↥K, ∃ (G : E → F) (ε : ℝ), 0 < ε ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G ∧ Metric.ball (x : E) ε ⊆ U ∧
      (∀ z ∈ Metric.ball (x : E) ε, G z = ρ z) ∧
      (∀ z ∈ Metric.ball (x : E) ε, fderiv ℝ G z = fderiv ℝ ρ z) := by
    intro x
    obtain ⟨G, hGsm, hGeq⟩ :=
      exists_contDiff_eq_nhds_local ρ (x : E) U (hU.mem_nhds (hKU x.2)) hρ
    have h4 : U ∩ {z : E | G z = ρ z} ∩ {z : E | fderiv ℝ G z = fderiv ℝ ρ z}
        ∈ 𝓝 (x : E) :=
      Filter.inter_mem (Filter.inter_mem (hU.mem_nhds (hKU x.2)) hGeq)
        (hGeq.fderiv)
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp h4
    exact ⟨G, ε, hε, hGsm, fun z hz => (hεsub hz).1.1, fun z hz => (hεsub hz).1.2,
      fun z hz => (hεsub hz).2⟩
  choose G ε hεpos hGsm hεU hGeq hfd_eq using hloc
  -- a finite subcover
  have hcover : K ⊆ ⋃ x : ↥K, Metric.ball (x : E) (ε x / 2) := by
    intro z hz
    refine Set.mem_iUnion.mpr ⟨⟨z, hz⟩, ?_⟩
    rw [Metric.mem_ball, dist_self]
    linarith [hεpos ⟨z, hz⟩]
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : ↥K => Metric.ball (x : E) (ε x / 2))
    (fun _ => Metric.isOpen_ball) hcover
  -- the pieces of the compact set
  have hKf : IsCompact (Sf ∩ K) := by
    refine isCompact_inter_of_eventually_not hK fun z hzK hz => ?_
    have hzf : fderiv ℝ ρ z ≠ 0 := by
      by_contra h
      exact hz (by rw [hSf]; exact h)
    exact (continuousAt_fderiv_of_contDiffOn hU hρ (hKU hzK)).eventually_ne hzf
  have hpiece_closed : ∀ x : ↥K,
      IsClosed (ρ '' ((Sf ∩ K) ∩ Metric.closedBall (x : E) (ε x / 2))) := by
    intro x
    exact ((hKf.inter_right Metric.isClosed_closedBall).image_of_continuousOn
      (hρ.continuousOn.mono fun z hz => hKU hz.1.2)).isClosed
  have hpiece_int : ∀ x : ↥K,
      interior (ρ '' ((Sf ∩ K) ∩ Metric.closedBall (x : E) (ε x / 2))) = ∅ := by
    intro x
    have hball : Metric.closedBall (x : E) (ε x / 2) ⊆ Metric.ball (x : E) (ε x) :=
      Metric.closedBall_subset_ball (by linarith [hεpos x])
    have hdom : (Sf ∩ K) ∩ Metric.closedBall (x : E) (ε x / 2)
        = ({z : E | fderiv ℝ (G x) z = 0} : Set E)
          ∩ (K ∩ Metric.closedBall (x : E) (ε x / 2)) := by
      ext z
      constructor
      · rintro ⟨⟨hzSf, hzK⟩, hzC⟩
        refine ⟨?_, hzK, hzC⟩
        show fderiv ℝ (G x) z = 0
        rw [hfd_eq x z (hball hzC)]
        rwa [hSf] at hzSf
      · rintro ⟨hz0, hzK, hzC⟩
        refine ⟨⟨?_, hzK⟩, hzC⟩
        show z ∈ Sf
        rw [hSf]
        show fderiv ℝ ρ z = 0
        rw [← hfd_eq x z (hball hzC)]
        exact hz0
    have himg : ρ '' ((Sf ∩ K) ∩ Metric.closedBall (x : E) (ε x / 2))
        = G x '' (({z : E | fderiv ℝ (G x) z = 0} : Set E)
            ∩ (K ∩ Metric.closedBall (x : E) (ε x / 2))) := by
      rw [hdom]
      exact Set.image_congr fun z hz => (hGeq x z (hball hz.2.2)).symm
    rw [himg]
    exact Work.Drive.flat_case_one hE2 hF₁ (G x) (hGsm x)
      (K ∩ Metric.closedBall (x : E) (ε x / 2)) (hK.inter_right Metric.isClosed_closedBall)
  have hunion : interior (⋃ x ∈ s, ρ ''
      ((Sf ∩ K) ∩ Metric.closedBall (x : E) (ε x / 2))) = ∅ := by
    rw [show (⋃ x ∈ s, ρ '' ((Sf ∩ K) ∩ Metric.closedBall (x : E) (ε x / 2)))
        = ⋃ x : {x // x ∈ s}, ρ '' ((Sf ∩ K)
            ∩ Metric.closedBall ((x : ↥K) : E) (ε (x : ↥K) / 2)) from by ext y; simp]
    exact interior_eq_empty_iUnion_isClosed (fun i => hpiece_closed i) (fun i => hpiece_int i)
  have hsub3 : ρ '' (Sf ∩ K) ⊆ ⋃ x ∈ s, ρ ''
      ((Sf ∩ K) ∩ Metric.closedBall (x : E) (ε x / 2)) := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨hzSf, hzK⟩ := hz
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (hs hzK)
    obtain ⟨hxs, hzx⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hxs,
      Set.mem_image_of_mem ρ ⟨⟨hzSf, hzK⟩, Metric.ball_subset_closedBall hzx⟩⟩⟩
  have hgoal : interior (ρ '' (Sf ∩ K)) = ∅ :=
    le_bot_iff.mp ((interior_mono hsub3).trans (le_of_eq hunion))
  rwa [hSf] at hgoal

/-- **Critical values on a compact piece.**  For `K` compact inside the open set `U` and `ρ` smooth
on `U`, the image under `ρ` of the critical points of `K` has empty interior.  The flat stratum
`{fderiv ℝ ρ = 0}` is handled by the Hausdorff dimension estimates (`flat_finrank_one` and
`flat_image_interior_empty_of_two_le`), the non-flat stratum by the local model
`local_model_rank_ge_one` and a finite cover argument. -/
theorem crit_image_interior_eq_empty_of_compact {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hE : Module.finrank ℝ E = Module.finrank ℝ F + 1)
    (IH : ∀ m' : ℕ, m' < Module.finrank ℝ F → WeakSard.{u, v} m')
    {U : Set E} (hU : IsOpen U) {ρ : E → F}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ U)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    interior (ρ '' ({z : E | ¬ Function.Surjective (fderiv ℝ ρ z)} ∩ K)) = ∅ := by
  classical
  set Sc : Set E := {z : E | ¬ Function.Surjective (fderiv ℝ ρ z)} with hSc
  set Sf : Set E := {z : E | fderiv ℝ ρ z = 0} with hSf
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ F) with h0 | hpos
  · -- ## target of dimension zero: every linear map into `F` is surjective
    haveI : Subsingleton F := Module.finrank_zero_iff.mp h0
    have hSc_empty : Sc = ∅ := by
      ext z
      exact ⟨fun hz => absurd (fun y => ⟨0, Subsingleton.elim _ _⟩) hz,
        fun hz => absurd hz (Set.notMem_empty z)⟩
    rw [hSc_empty, Set.empty_inter, Set.image_empty, interior_empty]
  · -- ## compactness of the two strata
    have hct : ∀ z ∈ U, ContinuousAt (fun z : E => fderiv ℝ ρ z) z :=
      fun z hz => continuousAt_fderiv_of_contDiffOn hU hρ hz
    have hKc : IsCompact (Sc ∩ K) := by
      refine isCompact_inter_of_eventually_not hK fun z hzK hz => ?_
      have hsurj : Function.Surjective (fderiv ℝ ρ z) := by
        by_contra h
        exact hz (by rw [hSc]; exact h)
      have hmem : (fun z : E => fderiv ℝ ρ z) ⁻¹'
          {L : E →L[ℝ] F | Function.Surjective L} ∈ 𝓝 z :=
        (hct z (hKU hzK)).preimage_mem_nhds
          ((isOpen_setOf_surjective_clm (E := E) (F := F)).mem_nhds hsurj)
      refine Filter.mem_of_superset hmem ?_
      intro w hw
      simpa [hSc] using hw
    have hKf : IsCompact (Sf ∩ K) := by
      refine isCompact_inter_of_eventually_not hK fun z hzK hz => ?_
      have hzf : fderiv ℝ ρ z ≠ 0 := by
        by_contra h
        exact hz (by rw [hSf]; exact h)
      simpa [hSf] using (hct z (hKU hzK)).eventually_ne hzf
    -- ## the flat stratum
    have hflat_int : interior (ρ '' (Sf ∩ K)) = ∅ := by
      rcases lt_or_ge (Module.finrank ℝ F) 2 with h2 | h2
      · have h1 : Module.finrank ℝ F = 1 := by omega
        have h := flat_finrank_one hE h1 U hU ρ hρ K hK hKU
        rwa [← hSf] at h
      · have h := flat_image_interior_empty_of_two_le hE h2 hU hρ hKU
        rwa [← hSf] at h
    have hflat_closed : IsClosed (ρ '' (Sf ∩ K)) :=
      (hKf.image_of_continuousOn (hρ.continuousOn.mono fun z hz => hKU hz.2)).isClosed
    -- ## the non-flat stratum, via an exhaustion of the open set where `fderiv ≠ 0`
    set W : Set E := U ∩ {z : E | fderiv ℝ ρ z ≠ 0} with hW
    have hWopen : IsOpen W := by
      rw [hW, isOpen_iff_mem_nhds]
      rintro z ⟨hzU, hzf⟩
      have h1 : {L : E →L[ℝ] F | L ≠ 0} ∈ 𝓝 (fderiv ℝ ρ z) :=
        isClosed_singleton.isOpen_compl.mem_nhds (by simpa using hzf)
      exact Filter.inter_mem (hU.mem_nhds hzU) ((hct z hzU).preimage_mem_nhds h1)
    obtain ⟨Ω, hΩc, hΩW, hΩcov⟩ := exists_countable_compact_exhaust hWopen
    have hloc : ∀ (n : ℕ) (x : ↥(Sc ∩ K ∩ Ω n)), ∃ r : ℝ, 0 < r ∧
        interior (ρ '' ({y : E | y ∈ closure (Metric.ball (x : E) r) ∧
          ¬ Function.Surjective (fderivWithin ℝ ρ U y)})) = ∅ := by
      intro n x
      have hxSK : (x : E) ∈ Sc ∩ K := x.2.1
      have hxU : (x : E) ∈ U := hKU hxSK.2
      have hxL : fderiv ℝ ρ (x : E) ≠ 0 := (hΩW n x.2.2).2
      obtain ⟨V, hVopen, hxV, -, hVint⟩ := local_model_rank_ge_one hE hU hρ hxU hxL IH
      obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp (hVopen.mem_nhds hxV)
      refine ⟨r, hr, ?_⟩
      have hsub : {y : E | y ∈ closure (Metric.ball (x : E) r) ∧
            ¬ Function.Surjective (fderivWithin ℝ ρ U y)}
          ⊆ {y : E | y ∈ closure V ∧ ¬ Function.Surjective (fderivWithin ℝ ρ U y)} := by
        rintro y ⟨hy, hyc⟩
        exact ⟨closure_mono hrV hy, hyc⟩
      exact le_bot_iff.mp ((interior_mono (Set.image_mono hsub)).trans (le_of_eq hVint))
    choose r hrpos hrint using hloc
    have hΩint : ∀ n : ℕ, interior (ρ '' (Sc ∩ K ∩ Ω n)) = ∅ := by
      intro n
      have hKΩ : IsCompact (Sc ∩ K ∩ Ω n) := hKc.inter_right (hΩc n).isClosed
      obtain ⟨s, hs⟩ := hKΩ.elim_finite_subcover
        (fun x : ↥(Sc ∩ K ∩ Ω n) => Metric.ball (x : E) (r n x / 2))
        (fun _ => Metric.isOpen_ball) (fun z hz => by
          refine Set.mem_iUnion.mpr ⟨⟨z, hz⟩, ?_⟩
          rw [Metric.mem_ball, dist_self]
          linarith [hrpos n ⟨z, hz⟩])
      have hpiece_closed : ∀ x : ↥(Sc ∩ K ∩ Ω n), IsClosed
          (ρ '' ((Sc ∩ K ∩ Ω n) ∩ Metric.closedBall (x : E) (r n x / 2))) := by
        intro x
        exact ((hKΩ.inter_right Metric.isClosed_closedBall).image_of_continuousOn
          (hρ.continuousOn.mono fun z hz => hKU hz.1.1.2)).isClosed
      have hpiece_int : ∀ x : ↥(Sc ∩ K ∩ Ω n), interior
          (ρ '' ((Sc ∩ K ∩ Ω n) ∩ Metric.closedBall (x : E) (r n x / 2))) = ∅ := by
        intro x
        have hxb : Metric.closedBall (x : E) (r n x / 2) ⊆ Metric.ball (x : E) (r n x) :=
          Metric.closedBall_subset_ball (by linarith [hrpos n x])
        have hsub : (Sc ∩ K ∩ Ω n) ∩ Metric.closedBall (x : E) (r n x / 2)
            ⊆ {y : E | y ∈ closure (Metric.ball (x : E) (r n x)) ∧
                ¬ Function.Surjective (fderivWithin ℝ ρ U y)} := by
          rintro y ⟨⟨⟨hySc, hyK⟩, hyΩ⟩, hyb⟩
          refine ⟨subset_closure (hxb hyb), ?_⟩
          have hyS : ¬ Function.Surjective (fderiv ℝ ρ y) := hySc
          rwa [fderivWithin_of_isOpen hU (hKU hyK)]
        exact le_bot_iff.mp ((interior_mono (Set.image_mono hsub)).trans (le_of_eq (hrint n x)))
      have hunion : interior (⋃ x ∈ s, ρ ''
          ((Sc ∩ K ∩ Ω n) ∩ Metric.closedBall (x : E) (r n x / 2))) = ∅ := by
        rw [show (⋃ x ∈ s, ρ '' ((Sc ∩ K ∩ Ω n) ∩ Metric.closedBall (x : E) (r n x / 2)))
            = ⋃ x : {x // x ∈ s}, ρ '' ((Sc ∩ K ∩ Ω n)
                ∩ Metric.closedBall ((x : ↥(Sc ∩ K ∩ Ω n)) : E)
                  (r n (x : ↥(Sc ∩ K ∩ Ω n)) / 2)) from by ext y; simp]
        exact interior_eq_empty_iUnion_isClosed (fun i => hpiece_closed i)
          (fun i => hpiece_int i)
      have hsub2 : ρ '' (Sc ∩ K ∩ Ω n) ⊆
          ⋃ x ∈ s, ρ '' ((Sc ∩ K ∩ Ω n) ∩ Metric.closedBall (x : E) (r n x / 2)) := by
        rintro y ⟨z, hz, rfl⟩
        obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (hs hz)
        obtain ⟨hxs, hzx⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hxs,
          Set.mem_image_of_mem ρ ⟨hz, Metric.ball_subset_closedBall hzx⟩⟩⟩
      exact le_bot_iff.mp ((interior_mono hsub2).trans (le_of_eq hunion))
    have hΩ_closed : ∀ n, IsClosed (ρ '' (Sc ∩ K ∩ Ω n)) := by
      intro n
      exact ((hKc.inter_right (hΩc n).isClosed).image_of_continuousOn
        (hρ.continuousOn.mono fun z hz => hKU hz.1.2)).isClosed
    -- ## assemble the strata
    have hKsub : Sc ∩ K ⊆ (Sf ∩ K) ∪ ⋃ n, (Sc ∩ K ∩ Ω n) := by
      rintro z ⟨hzSc, hzK⟩
      by_cases hz0 : fderiv ℝ ρ z = 0
      · exact Or.inl ⟨by rw [hSf]; exact hz0, hzK⟩
      · have hzW : z ∈ W := by rw [hW]; exact ⟨hKU hzK, hz0⟩
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (by rw [hΩcov]; exact hzW)
        exact Or.inr (Set.mem_iUnion.mpr ⟨n, ⟨⟨hzSc, hzK⟩, hn⟩⟩)
    let V : ℕ → Set F := fun n => if n = 0 then ρ '' (Sf ∩ K) else ρ '' (Sc ∩ K ∩ Ω (n - 1))
    have hVc : ∀ n, IsClosed (V n) := by
      intro n
      by_cases hn : n = 0
      · rw [show V n = ρ '' (Sf ∩ K) from by simp only [V, if_pos hn]]
        exact hflat_closed
      · rw [show V n = ρ '' (Sc ∩ K ∩ Ω (n - 1)) from by simp only [V, if_neg hn]]
        exact hΩ_closed (n - 1)
    have hVi : ∀ n, interior (V n) = ∅ := by
      intro n
      by_cases hn : n = 0
      · rw [show V n = ρ '' (Sf ∩ K) from by simp only [V, if_pos hn]]
        exact hflat_int
      · rw [show V n = ρ '' (Sc ∩ K ∩ Ω (n - 1)) from by simp only [V, if_neg hn]]
        exact hΩint (n - 1)
    have hsubV : ρ '' (Sc ∩ K) ⊆ ⋃ n, V n := by
      rintro y ⟨z, hz, rfl⟩
      rcases hKsub hz with h | h
      · exact Set.mem_iUnion.mpr ⟨0, by
          rw [show V 0 = ρ '' (Sf ∩ K) from by simp only [V, if_pos rfl]]
          exact Set.mem_image_of_mem ρ h⟩
      · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
        refine Set.mem_iUnion.mpr ⟨n + 1, ?_⟩
        rw [show V (n + 1) = ρ '' (Sc ∩ K ∩ Ω n) from by
          simp only [V, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]]
        exact Set.mem_image_of_mem ρ hn
    have hgoal : interior (ρ '' (Sc ∩ K)) = ∅ :=
      le_bot_iff.mp ((interior_mono hsubV).trans (le_of_eq (interior_eq_empty_iUnion_isClosed hVc hVi)))
    rwa [hSc] at hgoal

/-- **Weak Sard's theorem at every level.**  Exhaust the open set `U` by compacts, apply the compact
statement on each piece and finish with Baire category. -/
theorem weakSard_all : ∀ n : ℕ, WeakSard.{u, v} n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E _ _ _ F _ _ _ hF hE U hU ρ hρ
    have hIH : ∀ m' : ℕ, m' < Module.finrank ℝ F → WeakSard.{u, v} m' := by
      intro m' hm'
      exact ih m' (by rw [hF] at hm'; exact hm')
    obtain ⟨K, hKc, hKU, hKcov⟩ := exists_countable_compact_exhaust hU
    have hset : U ∩ {z : E | ¬ Function.Surjective (fderivWithin ℝ ρ U z)}
        = U ∩ {z : E | ¬ Function.Surjective (fderiv ℝ ρ z)} := by
      ext z
      constructor
      · rintro ⟨hzU, hz⟩
        refine ⟨hzU, ?_⟩
        simp only [Set.mem_ofPred_eq] at hz
        show ¬ Function.Surjective (fderiv ℝ ρ z)
        rwa [fderivWithin_of_isOpen hU hzU] at hz
      · rintro ⟨hzU, hz⟩
        refine ⟨hzU, ?_⟩
        show ¬ Function.Surjective (fderivWithin ℝ ρ U z)
        rw [fderivWithin_of_isOpen hU hzU]
        exact hz
    rw [hset]
    set Sc : Set E := {z : E | ¬ Function.Surjective (fderiv ℝ ρ z)} with hSc
    have hVc : ∀ m, IsClosed (ρ '' (Sc ∩ K m)) := by
      intro m
      have hcomp : IsCompact (K m ∩ Sc) := by
        have h : IsCompact (Sc ∩ K m) := by
          refine isCompact_inter_of_eventually_not (K := K m) (S := Sc) (hKc m)
            fun z hzK hz => ?_
          have hsurj : Function.Surjective (fderiv ℝ ρ z) := by
            by_contra hh
            exact hz hh
          have hmem : (fun z : E => fderiv ℝ ρ z) ⁻¹'
              {L : E →L[ℝ] F | Function.Surjective L} ∈ 𝓝 z :=
            (continuousAt_fderiv_of_contDiffOn hU hρ (hKU m hzK)).preimage_mem_nhds
              ((isOpen_setOf_surjective_clm (E := E) (F := F)).mem_nhds hsurj)
          refine Filter.mem_of_superset hmem ?_
          intro w hw hwSc
          have hwSc' : ¬ Function.Surjective (fderiv ℝ ρ w) := by simpa [hSc] using hwSc
          exact hwSc' hw
        rwa [Set.inter_comm] at h
      have himg : ρ '' (Sc ∩ K m) = ρ '' (K m ∩ Sc) := by rw [Set.inter_comm]
      rw [himg]
      exact (hcomp.image_of_continuousOn (hρ.continuousOn.mono fun z hz => hKU m hz.1)).isClosed
    have hVi : ∀ m, interior (ρ '' (Sc ∩ K m)) = ∅ := fun m =>
      crit_image_interior_eq_empty_of_compact hE hIH hU hρ (hKc m) (hKU m)
    have hBaire := interior_eq_empty_iUnion_isClosed hVc hVi
    have hsub : ρ '' (U ∩ Sc) ⊆ ⋃ m, ρ '' (Sc ∩ K m) := by
      rintro y ⟨z, hz, rfl⟩
      obtain ⟨hzU, hzc⟩ := hz
      have hzcov : z ∈ ⋃ m, K m := by rw [hKcov]; exact hzU
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hzcov
      exact Set.mem_iUnion.mpr ⟨m, Set.mem_image_of_mem ρ ⟨hzc, hm⟩⟩
    have hgoal : interior (ρ '' (U ∩ Sc)) = ∅ :=
      le_bot_iff.mp ((interior_mono hsub).trans (le_of_eq hBaire))
    rwa [hSc] at hgoal

end Work.Sard.wp

namespace Work.Sard

/-- **Weak Sard's theorem, open set version.**  For a `C^∞` map `ρ : ℝ^{n+1} → ℝⁿ` on an open set
`U`, the image of the set of points of `U` at which the derivative fails to be surjective has empty
interior. -/
theorem weak_interior_empty_open {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU : IsOpen U)
    (ρ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n))
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ U) :
    interior (ρ '' (U ∩ {z | ¬ Function.Surjective (fderivWithin ℝ ρ U z)})) = ∅ := by
  refine Work.Sard.wp.weakSard_all n (EuclideanSpace ℝ (Fin (n + 1)))
    (EuclideanSpace ℝ (Fin n)) ?_ ?_ U hU ρ hρ
  · rw [finrank_euclideanSpace_fin]
  · rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]

end Work.Sard

/-- The statement is also available under the root-namespace name `weak_interior_empty_open`, the
name under which it was requested. -/
theorem weak_interior_empty_open {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU : IsOpen U)
    (ρ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n))
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ U) :
    interior (ρ '' (U ∩ {z | ¬ Function.Surjective (fderivWithin ℝ ρ U z)})) = ∅ :=
  Work.Sard.weak_interior_empty_open hU ρ hρ
