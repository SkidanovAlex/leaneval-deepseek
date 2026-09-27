import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.levelCurveDefs
import Submission.Work.Projection.dimH_levelSet_le
import Submission.Work.Projection.dimH_image_le_of_contDiffOn
import Submission.Work.Drive.N2.isCritical_iff_chartRep
import Submission.Work.Compat.MFDerivCongrV433

namespace Work.Drive.N2

open scoped Manifold ContDiff
open Filter Topology

/-!
# Covering a regular level set of a function on a surface by finitely many curves

The main theorem of this file is `Work.Drive.N2.exists_finite_levelCover`: for a smooth function
`f : M → ℝ` on a compact surface `M`, a value `b` such that no critical point of `f` lies over `b`,
the level set `{x | f x = b}` is covered by the images of finitely many curves `γ i : ℝ → M`,
smooth on an open set `V i`, each of which is tangent to the level set with injective derivative.

The proof is local.  Near a regular point `x` of `f`, in the chart at `x`, the level set is the
image of a curve, and the curve is `C^∞` on a *neighbourhood* of the parameter (this is the only
place where the difference between `C^∞` at a point and on a neighbourhood matters).  Compactness
of the level set then produces a finite subcover.
-/

/-- A nonzero functional on a normed space attains the value `1`. -/
lemma exists_map_eq_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) : ∃ e : E, ℓ e = 1 := by
  obtain ⟨v, hv⟩ : ∃ v : E, ℓ v ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hℓ (ContinuousLinearMap.ext h)
  exact ⟨(ℓ v)⁻¹ • v, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]⟩

/-- A nonzero functional on a `2`-dimensional real vector space has a one-dimensional kernel. -/
lemma finrank_ker_eq_one {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (hfin : Module.finrank ℝ E = 2) {ℓ : E →ₗ[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    Module.finrank ℝ (LinearMap.ker ℓ) = 1 := by
  have hsurj : Function.Surjective ℓ := by
    obtain ⟨v, hv⟩ : ∃ v : E, ℓ v ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hℓ (LinearMap.ext h)
    intro y
    exact ⟨((ℓ v)⁻¹ * y) • v, by rw [map_smul, smul_eq_mul]; field_simp⟩
  have h1 : Module.finrank ℝ (LinearMap.range ℓ) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have h2 := LinearMap.finrank_range_add_finrank_ker ℓ
  omega

/-- A nonzero element of the kernel of a nonzero functional on a `2`-dimensional space generates
the whole kernel. -/
lemma ker_eq_span_of_mem {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (hfin : Module.finrank ℝ E = 2) {ℓ : E →ₗ[ℝ] ℝ} {a : E} (hℓ : ℓ ≠ 0) (ha : a ≠ 0)
    (hker : ℓ a = 0) :
    LinearMap.ker ℓ = Submodule.span ℝ {a} := by
  have h3 : Module.finrank ℝ (LinearMap.ker ℓ) = 1 := finrank_ker_eq_one hfin hℓ
  have h4 : Module.finrank ℝ (Submodule.span ℝ ({a} : Set E)) = 1 := by
    rw [finrank_span_singleton ha]
  have hle : Submodule.span ℝ ({a} : Set E) ≤ LinearMap.ker ℓ := by
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hker
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [h3, h4])).symm

/-- In a two-dimensional space, the range of an injective map `ℝ → V` is the kernel of any nonzero
functional that vanishes on it. -/
lemma range_eq_ker_dim_two {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (hfin : Module.finrank ℝ V = 2)
    (L : ℝ →ₗ[ℝ] V) (M : V →ₗ[ℝ] ℝ) (hL : Function.Injective L) (hM : M ≠ 0)
    (hker : ∀ w : ℝ, M (L w) = 0) :
    ∀ v : V, M v = 0 → ∃ w : ℝ, L w = v := by
  have ha : (L 1 : V) ≠ 0 := by
    intro h
    have h1 : (1 : ℝ) = 0 := hL (by rw [h, map_zero])
    norm_num at h1
  have hker_eq : LinearMap.ker M = Submodule.span ℝ {L 1} :=
    ker_eq_span_of_mem hfin hM ha (by simpa using hker 1)
  intro v hv
  have hvker : v ∈ LinearMap.ker M := by
    rw [LinearMap.mem_ker]
    exact hv
  rw [hker_eq] at hvker
  obtain ⟨w, hw⟩ := Submodule.mem_span_singleton.mp hvker
  refine ⟨w, ?_⟩
  rw [show L w = w • L 1 from by simpa using map_smul L w (1 : ℝ)]
  exact hw

/-- **Local parametrisation of a regular level set in a surface.**

Let `g : E → ℝ` be `C^∞` on an open set `Ω ∋ p`, with `g p = b` and `fderiv ℝ g p ≠ 0`, where `E`
is a two-dimensional real normed space.  Then the level set `{g = b}` is, near `p`, the image of a
`C^∞` curve `F : ℝ → E` defined on an open set `V ∋ 0`: `F 0 = p`, `g (F t) = b` on `V`, the
derivative of `F` is injective on `V`, and the image of `V` covers `{g = b}` inside an open set
`U ∋ p`. -/
theorem exists_levelParam_of_isRegular {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hfin : Module.finrank ℝ E = 2)
    (g : E → ℝ) (p : E) (b : ℝ) (Ω : Set E)
    (hΩ : IsOpen Ω) (hp : p ∈ Ω) (hg : ContDiffOn ℝ ∞ g Ω) (hgp : g p = b)
    (hd : fderiv ℝ g p ≠ 0) :
    ∃ (V : Set ℝ) (F : ℝ → E) (U : Set E),
      IsOpen V ∧ 0 ∈ V ∧ IsOpen U ∧ p ∈ U ∧ F 0 = p ∧
      ContDiffOn ℝ ∞ F V ∧
      (∀ t ∈ V, g (F t) = b) ∧
      (∀ t ∈ V, Function.Injective (fderiv ℝ F t)) ∧
      ({y : E | g y = b} ∩ U ⊆ F '' V) := by
  classical
  set ℓ : E →L[ℝ] ℝ := fderiv ℝ g p with hℓdef
  have hℓ : ℓ ≠ 0 := hd
  obtain ⟨e₀, he₀⟩ := exists_map_eq_one hℓ
  have hℓ' : (ℓ : E →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h
    exact hℓ (ContinuousLinearMap.ext fun v => by
      have := DFunLike.congr_fun h v
      simpa using this)
  have hker_fin : Module.finrank ℝ (LinearMap.ker (ℓ : E →ₗ[ℝ] ℝ)) = 1 :=
    finrank_ker_eq_one hfin hℓ'
  have hker_ne : LinearMap.ker (ℓ : E →ₗ[ℝ] ℝ) ≠ ⊥ := by
    intro h
    have : Module.finrank ℝ (LinearMap.ker (ℓ : E →ₗ[ℝ] ℝ)) = 0 := by
      rw [h]; exact finrank_bot ℝ E
    omega
  obtain ⟨a, haker, ha0⟩ := (Submodule.ne_bot_iff _).mp hker_ne
  have hker_a : ℓ a = 0 := haker
  -- the "coordinate replacement" map: it replaces the `ℓ`-coordinate by `g - b`
  set T : E → E := fun y => y + (g y - b - ℓ (y - p)) • e₀ with hTdef
  have hTp : T p = p := by simp [hTdef, hgp]
  have hℓT : ∀ y : E, ℓ (T y) = ℓ p + (g y - b) := by
    intro y
    simp only [hTdef, map_add, map_smul, smul_eq_mul]
    rw [he₀, mul_one, map_sub]
    ring
  have hTderiv : ∀ y ∈ Ω, HasFDerivAt T (1 + (fderiv ℝ g y - ℓ).smulRight e₀) y := by
    intro y hy
    have hgy : HasFDerivAt g (fderiv ℝ g y) y :=
      ((hg.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
    have h1 : HasFDerivAt (fun y : E => g y - b - ℓ (y - p)) (fderiv ℝ g y - ℓ) y :=
      (hgy.sub_const b).sub
        ((ContinuousLinearMap.hasFDerivAt ℓ).comp y ((hasFDerivAt_id y).sub_const p))
    have h2 : HasFDerivAt (fun y : E => (g y - b - ℓ (y - p)) • e₀)
        ((fderiv ℝ g y - ℓ).smulRight e₀) y := h1.smul_const e₀
    rw [hTdef]
    exact (hasFDerivAt_id y).add h2
  have hTderiv_p : fderiv ℝ T p = 1 := by
    rw [(hTderiv p hp).fderiv, ← hℓdef]
    simp
  have hT_cd : ∀ y ∈ Ω, ContDiffAt ℝ ∞ T y := by
    intro y hy
    have hgy : ContDiffAt ℝ ∞ g y := hg.contDiffAt (hΩ.mem_nhds hy)
    have h1 : ContDiffAt ℝ ∞ (fun y : E => g y - b - ℓ (y - p)) y :=
      (hgy.sub contDiffAt_const).sub
        (((ContinuousLinearMap.contDiff ℓ).contDiffAt).comp y
          (contDiffAt_id.sub contDiffAt_const))
    have h2 : ContDiffAt ℝ ∞ (fun y : E => (g y - b - ℓ (y - p)) • e₀) y := h1.smul_const e₀
    have h3 : ContDiffAt ℝ ∞ (fun y : E => y + (g y - b - ℓ (y - p)) • e₀) y :=
      contDiffAt_id.add h2
    rw [hTdef]
    exact h3
  have hT_cd_nat : ∀ (m : ℕ) (y : E), y ∈ Ω → ContDiffAt ℝ (m : ℕ∞ω) T y := by
    intro m y hy
    have hgy : ContDiffAt ℝ (m : ℕ∞ω) g y :=
      (contDiffWithinAt_infty.mp (hg.contDiffAt (hΩ.mem_nhds hy))) m
    have h1 : ContDiffAt ℝ (m : ℕ∞ω) (fun y : E => g y - b - ℓ (y - p)) y :=
      (hgy.sub contDiffAt_const).sub
        (((ContinuousLinearMap.contDiff ℓ).contDiffAt).comp y
          (contDiffAt_id.sub contDiffAt_const))
    have h2 : ContDiffAt ℝ (m : ℕ∞ω) (fun y : E => (g y - b - ℓ (y - p)) • e₀) y :=
      h1.smul_const e₀
    have h3 : ContDiffAt ℝ (m : ℕ∞ω) (fun y : E => y + (g y - b - ℓ (y - p)) • e₀) y :=
      contDiffAt_id.add h2
    rw [hTdef]
    exact h3
  have hT_strict : HasStrictFDerivAt T
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) p := by
    have h := (hT_cd p hp).hasStrictFDerivAt (n := ∞) (by simp)
    rw [hTderiv_p] at h
    exact h
  set e_loc : OpenPartialHomeomorph E E := hT_strict.toOpenPartialHomeomorph T with he_locdef
  have he_loc_coe : (e_loc : E → E) = T := by
    rw [he_locdef]
    exact HasStrictFDerivAt.toOpenPartialHomeomorph_coe hT_strict
  have hp_src : p ∈ e_loc.source := hT_strict.mem_toOpenPartialHomeomorph_source
  have hTp_tgt : T p ∈ e_loc.target := hT_strict.image_mem_toOpenPartialHomeomorph_target
  -- the set of points of the target where the local inverse is smooth with invertible derivative
  set W : Set E := {z : E | z ∈ e_loc.target ∧ (e_loc.symm : E → E) z ∈ Ω ∧
      fderiv ℝ g ((e_loc.symm : E → E) z) e₀ ≠ 0} with hWdef
  have hsymm_Tp : (e_loc.symm : E → E) (T p) = p := by
    have h := e_loc.left_inv hp_src
    rw [show (e_loc : E → E) p = T p from congrFun he_loc_coe p] at h
    exact h.symm ▸ rfl
  have hTp_W : T p ∈ W := by
    refine ⟨hTp_tgt, ?_, ?_⟩
    · rw [hsymm_Tp]; exact hp
    · rw [hsymm_Tp, ← hℓdef, he₀]; exact one_ne_zero
  have hWopen : IsOpen W := by
    refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    obtain ⟨hzt, hzΩ, hzne⟩ := hz
    have hcont : ContinuousAt (e_loc.symm : E → E) z := e_loc.continuousAt_symm hzt
    have hfd : ContinuousAt (fderiv ℝ g) ((e_loc.symm : E → E) z) :=
      (hg.contDiffAt (hΩ.mem_nhds hzΩ)).continuousAt_fderiv (n := ∞) (by simp)
    have hcomp : ContinuousAt (fun z : E => fderiv ℝ g ((e_loc.symm : E → E) z) e₀) z :=
      ((ContinuousLinearMap.apply ℝ ℝ e₀).continuous.continuousAt.comp
        (hfd.comp hcont))
    exact Filter.inter_mem (e_loc.open_target.mem_nhds hzt)
      (Filter.inter_mem (hcont.preimage_mem_nhds (hΩ.mem_nhds hzΩ))
        (hcomp.preimage_mem_nhds (isOpen_ne.mem_nhds hzne)))
  -- the local inverse is `C^n` at every point of `W`, for every finite `n`
  have hsymm_cd : ∀ z ∈ W, ∀ n : ℕ, ContDiffAt ℝ n (e_loc.symm : E → E) z := by
    intro z hz n
    obtain ⟨hzt, hzΩ, hzne⟩ := hz
    have hy_src : (e_loc.symm : E → E) z ∈ e_loc.source := e_loc.map_target hzt
    have hInv : (fderiv ℝ T ((e_loc.symm : E → E) z)).IsInvertible := by
      rw [(hTderiv ((e_loc.symm : E → E) z) hzΩ).fderiv]
      exact Work.Projection.isInvertible_one_add (fderiv ℝ g ((e_loc.symm : E → E) z)) ℓ e₀
        he₀ hzne
    obtain ⟨f', hf'⟩ := hInv
    have hfd_T : HasFDerivAt T (f' : E →L[ℝ] E) ((e_loc.symm : E → E) z) := by
      have h := hTderiv ((e_loc.symm : E → E) z) hzΩ
      have h1 : (f' : E →L[ℝ] E) = 1 + (fderiv ℝ g ((e_loc.symm : E → E) z) - ℓ).smulRight e₀ := by
        rw [hf', h.fderiv]
      rw [← h1] at h
      exact h
    have hev : (e_loc : E → E) =ᶠ[𝓝 ((e_loc.symm : E → E) z)] T := by
      filter_upwards [e_loc.open_source.mem_nhds hy_src] with w _
      rw [he_loc_coe]
    have hfd_e : HasFDerivAt (e_loc : E → E) (f' : E →L[ℝ] E) ((e_loc.symm : E → E) z) :=
      hfd_T.congr_of_eventuallyEq hev
    have hcd_e : ContDiffAt ℝ n (e_loc : E → E) ((e_loc.symm : E → E) z) := by
      refine (Filter.EventuallyEq.congr_contDiffWithinAt_of_insert
        (s := Set.univ) (f₁ := (e_loc : E → E)) (f := T) ?_).mpr ?_
      · simpa [nhdsWithin_univ] using hev
      · exact hT_cd_nat n _ hzΩ
    exact e_loc.contDiffAt_symm hzt hfd_e hcd_e
  -- the parametrisation of the level set and its domain
  set F : ℝ → E := fun t => (e_loc.symm : E → E) (T p + t • a) with hFdef
  set V : Set ℝ := {t : ℝ | T p + t • a ∈ W} with hVdef
  have hVopen : IsOpen V :=
    hWopen.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have h0V : (0 : ℝ) ∈ V := by
    rw [hVdef]
    simpa using hTp_W
  have hF0 : F 0 = p := by
    rw [hFdef]
    simpa using hsymm_Tp
  have hFsm : ContDiffOn ℝ ∞ F V := by
    intro t ht
    rw [contDiffWithinAt_infty]
    intro n
    have hzW : T p + t • a ∈ W := by simpa [hVdef] using ht
    rw [contDiffWithinAt_congr_set (f := F) (s := V) (x := t) (t := Set.univ) ?_]
    · exact (hsymm_cd _ hzW n).comp t
        (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
    · exact eventuallyEq_univ.mpr (hVopen.mem_nhds ht)
  have hlev : ∀ t ∈ V, g (F t) = b := by
    intro t ht
    have hzW : T p + t • a ∈ W := by simpa [hVdef] using ht
    have hzT : T ((e_loc.symm : E → E) (T p + t • a)) = T p + t • a := by
      rw [← he_loc_coe]
      exact e_loc.right_inv hzW.1
    have h1 := hℓT ((e_loc.symm : E → E) (T p + t • a))
    rw [hzT] at h1
    have h2 : ℓ (T p + t • a) = ℓ p := by
      rw [map_add, map_smul, smul_eq_mul, hker_a, mul_zero, add_zero]
      simpa [hTp, hgp] using hℓT p
    rw [h2] at h1
    rw [hFdef]
    linarith
  have hFinj : ∀ t ∈ V, Function.Injective (fderiv ℝ F t) := by
    intro t ht
    have hzW : T p + t • a ∈ W := by simpa [hVdef] using ht
    obtain ⟨hzt, hzΩ, hzne⟩ := hzW
    have hy_src : (e_loc.symm : E → E) (T p + t • a) ∈ e_loc.source := e_loc.map_target hzt
    have hInv : (fderiv ℝ T ((e_loc.symm : E → E) (T p + t • a))).IsInvertible := by
      rw [(hTderiv ((e_loc.symm : E → E) (T p + t • a)) hzΩ).fderiv]
      exact Work.Projection.isInvertible_one_add
        (fderiv ℝ g ((e_loc.symm : E → E) (T p + t • a))) ℓ e₀ he₀ hzne
    obtain ⟨f', hf'⟩ := hInv
    have hfd_T : HasFDerivAt T (f' : E →L[ℝ] E) ((e_loc.symm : E → E) (T p + t • a)) := by
      have h := hTderiv ((e_loc.symm : E → E) (T p + t • a)) hzΩ
      have h1 : (f' : E →L[ℝ] E)
          = 1 + (fderiv ℝ g ((e_loc.symm : E → E) (T p + t • a)) - ℓ).smulRight e₀ := by
        rw [hf', h.fderiv]
      rw [← h1] at h
      exact h
    have hev : (e_loc : E → E) =ᶠ[𝓝 ((e_loc.symm : E → E) (T p + t • a))] T := by
      filter_upwards [e_loc.open_source.mem_nhds hy_src] with w _
      rw [he_loc_coe]
    have hfd_e : HasFDerivAt (e_loc : E → E) (f' : E →L[ℝ] E)
        ((e_loc.symm : E → E) (T p + t • a)) := hfd_T.congr_of_eventuallyEq hev
    have hfd_symm : HasFDerivAt (e_loc.symm : E → E)
        (((f'.symm : E ≃L[ℝ] E)) : E →L[ℝ] E) (T p + t • a) :=
      e_loc.hasFDerivAt_symm hzt hfd_e
    rw [hFdef]
    have hchain : HasFDerivAt (fun s : ℝ => (e_loc.symm : E → E) (T p + s • a))
        ((↑(f'.symm) : E →L[ℝ] E) ∘L ((1 : ℝ →L[ℝ] ℝ).smulRight a)) t :=
      hfd_symm.comp t (((hasFDerivAt_id t).smul_const a).const_add (T p))
    rw [hchain.fderiv]
    intro x y hxy
    have hxy' : (↑(f'.symm) : E → E) (x • a) = (↑(f'.symm) : E → E) (y • a) := by
      simpa [ContinuousLinearMap.smulRight_apply, one_apply_eq_self] using hxy
    have h2 : x • a = y • a := f'.symm.injective hxy'
    have h3 : (x - y) • a = 0 := by rw [sub_smul, h2, sub_self]
    have h4 : x - y = 0 := (smul_eq_zero.mp h3).resolve_right ha0
    linarith
  set U : Set E := e_loc.source ∩ (Ω ∩ T ⁻¹' W) with hUdef
  have hUopen : IsOpen U := by
    have hT_contOn : ContinuousOn T Ω := fun y hy => (hT_cd y hy).continuousAt.continuousWithinAt
    exact e_loc.open_source.inter (hT_contOn.isOpen_inter_preimage hΩ hWopen)
  have hpU : p ∈ U := by
    refine ⟨hp_src, hp, ?_⟩
    exact hTp_W
  have hcov : {y : E | g y = b} ∩ U ⊆ F '' V := by
    intro y hy
    have hyb : g y = b := hy.1
    have hysrc : y ∈ e_loc.source := hy.2.1
    have hyΩ : y ∈ Ω := hy.2.2.1
    have hyW : T y ∈ W := hy.2.2.2
    have h1 : ℓ (T y) = ℓ p := by
      rw [hℓT, hyb]
      ring
    have h2 : ℓ (T p) = ℓ p := by
      simpa [hTp, hgp] using hℓT p
    have h3 : T y - T p ∈ Submodule.span ℝ {a} := by
      rw [← ker_eq_span_of_mem hfin hℓ' ha0 hker_a, LinearMap.mem_ker]
      have hy1 : (ℓ : E →ₗ[ℝ] ℝ) (T y) = ℓ p := h1
      have hy2 : (ℓ : E →ₗ[ℝ] ℝ) (T p) = ℓ p := h2
      rw [map_sub, hy1, hy2, sub_self]
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h3
    have ht' : T p + t • a = T y := by rw [ht]; abel
    refine ⟨t, ?_, ?_⟩
    · show T p + t • a ∈ W
      rw [ht']
      exact hyW
    · show (e_loc.symm : E → E) (T p + t • a) = y
      rw [ht', ← congrFun he_loc_coe y]
      exact e_loc.left_inv hysrc
  exact ⟨V, F, U, hVopen, h0V, hUopen, hpU, hF0, hFsm, hlev, hFinj, hcov⟩

/-- **Local parametrisation of a regular level set of a smooth function on a surface.**

Let `M` be a smooth surface, `f : M → ℝ` smooth, all of whose points over `b` are regular points,
`x₀` a point over `b`, and let `F : ℝ → ℝ²` parametrise the chart-level set of the chart at `x₀`
over an open set `V ∋ 0`, with injective derivative and covering the level set inside an open set
`U ∋ e x₀`, where `e` is the extended chart at `x₀`.  Then the level set of `f` is parametrised near
`x₀` by `γ := e.symm ∘ F`: there is an open `U' ∋ x₀` with `{f = b} ∩ U' ⊆ γ '' V'` for an open
`V' ⊆ V ∋ 0`, the curve `γ` is smooth on `V'`, lies in the level set, has injective differential
whose image is exactly the kernel of `df`. -/
theorem localLevelParam {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ f) (b : ℝ) (x₀ : M)
    (hreg : ∀ x : M, f x = b → ¬ Work.Drive.Morse.IsCritical f x)
    (V : Set ℝ) (F : ℝ → EuclideanSpace ℝ (Fin 2)) (U : Set (EuclideanSpace ℝ (Fin 2)))
    (hV : IsOpen V) (hU : IsOpen U)
    (hpinU : (extChartAt (𝓡 2) x₀) x₀ ∈ U)
    (hFsm : ContDiffOn ℝ ∞ F V)
    (hlev : ∀ t ∈ V, f ((extChartAt (𝓡 2) x₀).symm (F t)) = b)
    (hFinj : ∀ t ∈ V, Function.Injective (fderiv ℝ F t))
    (hcov : {y : EuclideanSpace ℝ (Fin 2) | f ((extChartAt (𝓡 2) x₀).symm y) = b} ∩ U ⊆ F '' V) :
    ∃ (U' : Set M) (V' : Set ℝ) (γ : ℝ → M),
      IsOpen U' ∧ x₀ ∈ U' ∧ IsOpen V' ∧ V' ⊆ V ∧
      ContMDiffOn 𝓘(ℝ,ℝ) (𝓡 2) ∞ γ V' ∧
      (∀ t ∈ V', f (γ t) = b) ∧
      (∀ t ∈ V', Function.Injective (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t)) ∧
      (∀ (t : ℝ), t ∈ V' → ∀ w : TangentSpace (𝓘(ℝ,ℝ)) t,
        mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ t) (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t w) = 0) ∧
      (∀ (t : ℝ), t ∈ V' → ∀ v : TangentSpace (𝓡 2) (γ t),
        mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ t) v = 0 →
          ∃ w : TangentSpace (𝓘(ℝ,ℝ)) t, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t w = v) ∧
      ({x : M | f x = b} ∩ U' ⊆ γ '' V') := by
  classical
  set e := extChartAt (𝓡 2) x₀ with hedef
  set γ : ℝ → M := fun t => e.symm (F t) with hγdef
  set V' : Set ℝ := V ∩ F ⁻¹' e.target with hV'def
  set U' : Set M := e.source ∩ e ⁻¹' U with hU'def
  have hx₀src : x₀ ∈ e.source := by
    rw [hedef, extChartAt_source]
    exact mem_chart_source _ _
  have hV'sub : V' ⊆ V := by rw [hV'def]; exact Set.inter_subset_left
  have hV'open : IsOpen V' := by
    rw [hV'def]
    refine isOpen_iff_mem_nhds.mpr fun t ht => ?_
    have htV : t ∈ V := ht.1
    have hFcont : ContinuousAt F t := hFsm.continuousOn.continuousAt (hV.mem_nhds htV)
    exact Filter.inter_mem (hV.mem_nhds htV)
      (hFcont.preimage_mem_nhds
        ((isOpen_extChartAt_target (I := 𝓡 2) x₀).mem_nhds ht.2))
  have hU'open : IsOpen U' := by
    rw [hU'def]
    refine (continuousOn_extChartAt (I := 𝓡 2) x₀).isOpen_inter_preimage
      (isOpen_extChartAt_source (I := 𝓡 2) x₀) hU
  have hx₀U' : x₀ ∈ U' := by
    rw [hU'def]
    exact ⟨hx₀src, hpinU⟩
  have hγsm : ContMDiffOn 𝓘(ℝ,ℝ) (𝓡 2) ∞ γ V' := by
    rw [hγdef]
    refine (contMDiffOn_extChartAt_symm (I := 𝓡 2) x₀).comp ?_ ?_
    · exact hFsm.contMDiffOn.mono hV'sub
    · rw [hV'def]
      rintro t ⟨-, ht⟩
      exact ht
  have hlev' : ∀ t ∈ V', f (γ t) = b := fun t ht => hlev t (hV'sub ht)
  have hγmd : ∀ t ∈ V', MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2) γ t := by
    intro t ht
    exact (hγsm.contMDiffAt (hV'open.mem_nhds ht)).mdifferentiableAt (by simp)
  have hinj' : ∀ t ∈ V', Function.Injective (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t) := by
    intro t ht
    have htV : t ∈ V := hV'sub ht
    have hFt_tgt : F t ∈ e.target := ht.2
    have hc : MDifferentiableAt 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) (𝓡 2) (e.symm) (F t) := by
      have h := mdifferentiableWithinAt_extChartAt_symm (I := 𝓡 2) (x := x₀) hFt_tgt
      rw [ModelWithCorners.range_eq_univ] at h
      simpa [MDifferentiableAt, MDifferentiableWithinAt, ChartedSpace.LiftPropAt, hedef] using h
    have hF : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) F t :=
      (hFsm.contDiffAt (hV.mem_nhds htV)).contMDiffAt.mdifferentiableAt (by simp)
    have hcomp : mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t =
        (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) (𝓡 2) (e.symm) (F t)) ∘L mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) F t := by
      rw [hγdef]
      exact mfderiv_comp t hc hF
    rw [hcomp]
    have hinv : Function.Injective
        (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) (𝓡 2) (e.symm) (F t)) := by
      have h := isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 2) (x := x₀) hFt_tgt
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using h.injective
    intro x y hxy
    have h1 : (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) (𝓡 2) (e.symm) (F t))
        ((mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) F t) x)
        = (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) (𝓡 2) (e.symm) (F t))
        ((mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) F t) y) := hxy
    have h2 : (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) F t) x
        = (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) F t) y := hinv h1
    rw [mfderiv_eq_fderiv] at h2
    exact hFinj t htV h2
  have hker' : ∀ (t : ℝ), t ∈ V' → ∀ w : TangentSpace (𝓘(ℝ,ℝ)) t,
      mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ t) (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t w) = 0 := by
    intro t ht w
    have htV : t ∈ V := hV'sub ht
    have hconst : (f ∘ γ) =ᶠ[𝓝 t] (fun _ => b) := by
      filter_upwards [hV.mem_nhds htV] with s hs
      exact hlev s hs
    have h1 : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (f ∘ γ) t = 0 := by
      rw [Filter.EventuallyEq.mfderiv_eq_v433 hconst (x := t)]
      exact mfderiv_const
    have h2 : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (f ∘ γ) t =
        (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ t)) ∘L (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t) :=
      mfderiv_comp t (hf.mdifferentiableAt (by simp)) (hγmd t ht)
    have h3 : (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ t)) ∘L (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t) = 0 := by
      rw [← h2]; exact h1
    show ((mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ t)) ∘L (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t)) w = 0
    rw [h3]
    rfl
  have hsurj' : ∀ (t : ℝ), t ∈ V' → ∀ v : TangentSpace (𝓡 2) (γ t),
      mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ t) v = 0 →
        ∃ w : TangentSpace (𝓘(ℝ,ℝ)) t, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t w = v := by
    intro t ht v hv
    have hfin : Module.finrank ℝ (TangentSpace (𝓡 2) (γ t)) = 2 := by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2
      exact finrank_euclideanSpace_fin
    have hM : (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ t)) ≠ 0 := by
      simpa [Work.Drive.Morse.IsCritical] using hreg (γ t) (hlev' t ht)
    haveI : FiniteDimensional ℝ (TangentSpace (𝓡 2) (γ t)) :=
      inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 2)))
    have hL : Function.Injective (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t).toLinearMap := hinj' t ht
    have hM' : (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ t)).toLinearMap ≠ 0 := by
      intro h
      exact hM (ContinuousLinearMap.ext fun v => by
        have := DFunLike.congr_fun h v
        simpa using this)
    exact range_eq_ker_dim_two hfin (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t).toLinearMap
      (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ t)).toLinearMap hL hM' (fun w => hker' t ht w) v hv
  have hcov' : {x : M | f x = b} ∩ U' ⊆ γ '' V' := by
    rintro x ⟨hxb, hxU⟩
    have hxsrc : x ∈ e.source := hxU.1
    have heU : e x ∈ U := hxU.2
    have hexb : e x ∈ {y : EuclideanSpace ℝ (Fin 2) | f (e.symm y) = b} := by
      show f (e.symm (e x)) = b
      rw [e.left_inv hxsrc]
      exact hxb
    obtain ⟨t, htV, htF⟩ := hcov ⟨hexb, heU⟩
    refine ⟨t, ?_, ?_⟩
    · rw [hV'def]
      refine ⟨htV, ?_⟩
      show F t ∈ e.target
      rw [htF]
      exact e.map_source hxsrc
    · rw [hγdef]
      show e.symm (F t) = x
      rw [htF, e.left_inv hxsrc]
  exact ⟨U', V', γ, hU'open, hx₀U', hV'open, hV'sub, hγsm, hlev', hinj', hker', hsurj', hcov'⟩

open scoped Manifold ContDiff in
theorem exists_finite_levelCover {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (b : ℝ)
    (hreg : ∀ x : M, f x = b → ¬ Work.Drive.Morse.IsCritical f x) :
    ∃ (N : ℕ) (γ : Fin N → ℝ → M) (V : Fin N → Set ℝ),
      (∀ i, IsOpen (V i)) ∧
      (∀ i, ContMDiffOn 𝓘(ℝ,ℝ) (𝓡 2) ∞ (γ i) (V i)) ∧
      (∀ (i : Fin N) (t : ℝ), t ∈ V i → f (γ i t) = b) ∧
      (∀ (i : Fin N) (t : ℝ), t ∈ V i → Function.Injective (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ i) t)) ∧
      (∀ (i : Fin N) (t : ℝ), t ∈ V i → ∀ w : TangentSpace (𝓘(ℝ,ℝ)) t,
        mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ i t) (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ i) t w) = 0) ∧
      (∀ (i : Fin N) (t : ℝ), t ∈ V i → ∀ v : TangentSpace (𝓡 2) (γ i t),
        mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ i t) v = 0 →
          ∃ w : TangentSpace (𝓘(ℝ,ℝ)) t, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ i) t w = v) ∧
      ({x : M | f x = b} ⊆ ⋃ i, γ i '' V i) := by
  classical
  -- the level set is compact
  have hScompact : IsCompact {x : M | f x = b} :=
    (isClosed_eq hf.continuous continuous_const).isCompact
  -- local data at every point of the level set
  have hlocal : ∀ q : {x : M // f x = b},
      ∃ (U : Set M) (V : Set ℝ) (γ : ℝ → M),
        IsOpen U ∧ q.1 ∈ U ∧ IsOpen V ∧
        ContMDiffOn 𝓘(ℝ,ℝ) (𝓡 2) ∞ γ V ∧
        (∀ t ∈ V, f (γ t) = b) ∧
        (∀ t ∈ V, Function.Injective (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t)) ∧
        (∀ (t : ℝ), t ∈ V → ∀ w : TangentSpace (𝓘(ℝ,ℝ)) t,
          mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ t) (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t w) = 0) ∧
        (∀ (t : ℝ), t ∈ V → ∀ v : TangentSpace (𝓡 2) (γ t),
          mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ t) v = 0 →
            ∃ w : TangentSpace (𝓘(ℝ,ℝ)) t, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t w = v) ∧
        ({x : M | f x = b} ∩ U ⊆ γ '' V) := by
    intro q
    set e := extChartAt (𝓡 2) q.1 with hedef
    have hxsrc : q.1 ∈ e.source := by
      rw [hedef, extChartAt_source]
      exact mem_chart_source _ _
    have hptgt : e q.1 ∈ e.target := e.map_source hxsrc
    have hΩ : IsOpen e.target := isOpen_extChartAt_target (I := 𝓡 2) q.1
    have hgp : f (e.symm (e q.1)) = b := by
      rw [e.left_inv hxsrc]
      exact q.2
    have hg : ContDiffOn ℝ ∞ (fun y => f (e.symm y)) e.target := by
      have h1 : ContMDiffOn 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) (𝓡 2) ∞ (e.symm) e.target :=
        contMDiffOn_extChartAt_symm (I := 𝓡 2) q.1
      have h2 : ContMDiffOn (𝓡 2) 𝓘(ℝ,ℝ) ∞ f Set.univ := hf.contMDiffOn
      exact (h2.comp h1 (Set.subset_univ _)).contDiffOn
    have hd : fderiv ℝ (fun y => f (e.symm y)) (e q.1) ≠ 0 := by
      intro h
      refine hreg q.1 q.2 ?_
      rw [Work.Drive.Morse.IsCritical]
      exact (mfderiv_eq_zero_iff_chartRep f hf q.1 q.1 hxsrc).mpr h
    obtain ⟨V, F, U, hV, h0V, hU, hpU, hF0, hFsm, hlev, hFinj, hcov⟩ :=
      exists_levelParam_of_isRegular finrank_euclideanSpace_fin
        (fun y => f (e.symm y)) (e q.1) b e.target hΩ hptgt hg hgp hd
    obtain ⟨U', V', γ, hU'open, hxU', hV'open, -, hγsm, hlev', hinj', hker', hsurj', hcov'⟩ :=
      localLevelParam f hf b q.1 hreg V F U hV hU hpU hFsm hlev hFinj hcov
    exact ⟨U', V', γ, hU'open, hxU', hV'open, hγsm, hlev', hinj', hker', hsurj', hcov'⟩
  choose U V γ hUopen hxU hVopen hγsm hlev hinj hker hsurj hcov using hlocal
  -- a finite subcover
  obtain ⟨t, ht⟩ := hScompact.elim_finite_subcover U hUopen
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  let γ' : Fin t.card → ℝ → M := fun k => γ (t.equivFin.symm k)
  let V' : Fin t.card → Set ℝ := fun k => V (t.equivFin.symm k)
  have hV'open : ∀ k, IsOpen (V' k) := fun k => hVopen _
  have hγ'sm : ∀ k, ContMDiffOn 𝓘(ℝ,ℝ) (𝓡 2) ∞ (γ' k) (V' k) := fun k => hγsm _
  have hlev' : ∀ (k : Fin t.card) (s : ℝ), s ∈ V' k → f (γ' k s) = b :=
    fun k s hs => hlev (t.equivFin.symm k) s hs
  have hinj' : ∀ (k : Fin t.card) (s : ℝ), s ∈ V' k →
      Function.Injective (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ' k) s) :=
    fun k s hs => hinj (t.equivFin.symm k) s hs
  have hker' : ∀ (k : Fin t.card) (s : ℝ), s ∈ V' k → ∀ w : TangentSpace (𝓘(ℝ,ℝ)) s,
      mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ' k s) (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ' k) s w) = 0 :=
    fun k s hs w => hker (t.equivFin.symm k) s hs w
  have hsurj' : ∀ (k : Fin t.card) (s : ℝ), s ∈ V' k → ∀ v : TangentSpace (𝓡 2) (γ' k s),
      mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ' k s) v = 0 →
        ∃ w : TangentSpace (𝓘(ℝ,ℝ)) s, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ' k) s w = v :=
    fun k s hs v hv => hsurj (t.equivFin.symm k) s hs v hv
  have hcov' : {x : M | f x = b} ⊆ ⋃ k, γ' k '' V' k := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
    refine Set.mem_iUnion.mpr ⟨t.equivFin ⟨i, hi⟩, ?_⟩
    have hsymm : t.equivFin.symm (t.equivFin ⟨i, hi⟩) = ⟨i, hi⟩ := Equiv.symm_apply_apply _ _
    show x ∈ γ (t.equivFin.symm (t.equivFin ⟨i, hi⟩)) '' V (t.equivFin.symm (t.equivFin ⟨i, hi⟩))
    rw [hsymm]
    exact hcov i ⟨hx, hxi⟩
  exact ⟨t.card, γ', V', hV'open, hγ'sm, hlev', hinj', hker', hsurj', hcov'⟩

end Work.Drive.N2
