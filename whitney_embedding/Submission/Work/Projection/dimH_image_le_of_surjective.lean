import Mathlib
import Submission.Work.Projection.dimH_image_le_of_contDiffOn

open scoped Manifold ContDiff
open Topology MeasureTheory Set

namespace Work.Projection


/-- Covering by locally Lipschitz parametrisations. -/
lemma dimH_le_of_local_lipschitz_param {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [SecondCountableTopology E] {S : Set E} {d : ENNReal}
    (h : ∀ x ∈ S, ∃ (H : Submodule ℝ E) (g : H → E) (V : Set H) (U : Set E),
        (Module.finrank ℝ H : ENNReal) ≤ d ∧ IsOpen V ∧
        (∃ K t, V ⊆ t ∧ LipschitzOnWith K g t) ∧ IsOpen U ∧ x ∈ U ∧ S ∩ U ⊆ g '' V) :
    dimH S ≤ d := by
  have h' : ∀ s : S, ∃ (H : Submodule ℝ E) (g : H → E) (V : Set H) (U : Set E),
      (Module.finrank ℝ H : ENNReal) ≤ d ∧ IsOpen V ∧
      (∃ K t, V ⊆ t ∧ LipschitzOnWith K g t) ∧ IsOpen U ∧ (s : E) ∈ U ∧ S ∩ U ⊆ g '' V :=
    fun s => h s.1 s.2
  choose H g V U hspec using h'
  have hcover : S ⊆ ⋃ s : S, U s := fun x hx =>
    mem_iUnion.2 ⟨⟨x, hx⟩, (hspec ⟨x, hx⟩).2.2.2.2.1⟩
  obtain ⟨c, hc_count, hc_cov⟩ := (HereditarilyLindelofSpace.isLindelof S).elim_countable_subcover
    U (fun s => (hspec s).2.2.2.1) hcover
  calc dimH S ≤ dimH (⋃ s ∈ c, S ∩ U s) := by
        refine dimH_mono fun x hx => ?_
        obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 (hc_cov hx)
        exact mem_iUnion₂.2 ⟨s, hs, hx, hxs⟩
    _ = ⨆ s ∈ c, dimH (S ∩ U s) := dimH_bUnion hc_count _
    _ ≤ d := by
        refine iSup₂_le fun s _ => ?_
        calc dimH (S ∩ U s) ≤ dimH (g s '' V s) := dimH_mono (hspec s).2.2.2.2.2
          _ ≤ dimH (V s) := by
              refine dimH_image_le_of_locally_lipschitzOn fun y hy => ?_
              obtain ⟨K, t, hVt, hLip⟩ := (hspec s).2.2.1
              exact ⟨K, t, Filter.mem_of_superset
                (self_mem_nhdsWithin : V s ∈ 𝓝[V s] y) hVt, hLip⟩
          _ ≤ (Module.finrank ℝ (H s) : ENNReal) := by
              calc dimH (V s) ≤ dimH (Set.univ : Set (H s)) := dimH_mono (subset_univ _)
                _ = (Module.finrank ℝ (H s) : ENNReal) := Real.dimH_univ_eq_finrank _
          _ ≤ d := (hspec s).1




/-- The local parametrisation of the level set of a surjective map. -/
lemma exists_local_param_of_contDiffAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (Φ : E → F) (a : E) (hΦa : ContDiffAt ℝ 1 Φ a) (ha0 : Φ a = 0)
    (hsurj : Function.Surjective (fderiv ℝ Φ a)) :
    ∃ (H : Submodule ℝ E) (g : H → E) (V : Set H) (U : Set E),
      Module.finrank ℝ H = Module.finrank ℝ E - Module.finrank ℝ F ∧ IsOpen V ∧
      (∃ K t, V ⊆ t ∧ LipschitzOnWith K g t) ∧ IsOpen U ∧ a ∈ U ∧
      Φ ⁻¹' {0} ∩ U ⊆ g '' V := by
  set L : E →L[ℝ] F := fderiv ℝ Φ a with hL
  have hLsurj : Function.Surjective L := hsurj
  obtain ⟨σ, hσ⟩ := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional
    (f := L) hLsurj
  have hσL : ∀ y : F, L (σ y) = y := fun y => hσ y
  have hΦfd : HasFDerivAt Φ L a := by
    rw [hL]
    exact (hΦa.differentiableAt (by norm_num)).hasFDerivAt
  -- the coordinate replacement map
  have hΘcont : ContDiffAt ℝ 1 (fun y : E => y + σ (Φ y - (L y - L a))) a := by
    have hinner : ContDiffAt ℝ 1 (fun y : E => Φ y - (L y - L a)) a :=
      hΦa.sub (((ContinuousLinearMap.contDiff (n := (1 : ℕ∞ω)) L).contDiffAt).sub
        (contDiffAt_const (x := a) (c := L a) (n := (1 : ℕ∞ω))))
    exact (contDiffAt_id (x := a) (n := (1 : ℕ∞ω))).add
      (((ContinuousLinearMap.contDiff (n := (1 : ℕ∞ω)) σ).contDiffAt).comp a hinner)
  have hΘfd : HasFDerivAt (fun y : E => y + σ (Φ y - (L y - L a)))
      ((1 : E →L[ℝ] E)) a := by
    have hLin : HasFDerivAt (fun y : E => L y - L a) L a := L.hasFDerivAt.sub_const (L a)
    have hinner : HasFDerivAt (fun y : E => Φ y - (L y - L a)) (L - L) a := hΦfd.sub hLin
    have hcomp : HasFDerivAt (fun y : E => σ (Φ y - (L y - L a))) (σ.comp (L - L)) a :=
      σ.hasFDerivAt.comp a hinner
    have hsum := (hasFDerivAt_id (x := a)).add hcomp
    have hder : (ContinuousLinearMap.id ℝ E + σ.comp (L - L)) = ContinuousLinearMap.id ℝ E := by
      simp
    rw [hder] at hsum
    exact hsum
  have hΘstrict : HasStrictFDerivAt (fun y : E => y + σ (Φ y - (L y - L a)))
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) a :=
    hΘcont.hasStrictFDerivAt' hΘfd (by norm_num)
  have hΘa : a + σ (Φ a - (L a - L a)) = a := by
    rw [show L a - L a = 0 from sub_self (L a), sub_zero, ha0, map_zero, add_zero]
  set LI : E → E :=
    hΘstrict.localInverse (fun y : E => y + σ (Φ y - (L y - L a)))
      (ContinuousLinearEquiv.refl ℝ E) a with hLI
  have hleft : ∀ᶠ x in 𝓝 a, LI ((fun y : E => y + σ (Φ y - (L y - L a))) x) = x :=
    hΘstrict.eventually_left_inverse
  obtain ⟨K, t, ht, hLip⟩ := hΘstrict.to_localInverse.exists_lipschitzOnWith
  have ht' : t ∈ 𝓝 a := by simpa only [hΘa] using ht
  have hnhd1 : {x | LI ((fun y : E => y + σ (Φ y - (L y - L a))) x) = x} ∩ t ∈ 𝓝 a :=
    Filter.inter_mem hleft ht'
  obtain ⟨U₀, hU₀sub, hU₀open, haU₀⟩ := mem_nhds_iff.mp hnhd1
  have hθcont : ContinuousAt (fun y : E => y + σ (Φ y - (L y - L a))) a := hΘcont.continuousAt
  have hnhd2 : {x | LI ((fun y : E => y + σ (Φ y - (L y - L a))) x) = x} ∩ t ∩
      {x | (fun y : E => y + σ (Φ y - (L y - L a))) x ∈ U₀} ∈ 𝓝 a :=
    Filter.inter_mem hnhd1 (hθcont.preimage_mem_nhds (hU₀open.mem_nhds (by rw [hΘa]; exact haU₀)))
  obtain ⟨U, hUsub, hUopen, haU⟩ := mem_nhds_iff.mp hnhd2
  have hrange : L.range = ⊤ := L.range_eq_top_of_surjective hLsurj
  have hfin : Module.finrank ℝ L.ker = Module.finrank ℝ E - Module.finrank ℝ F := by
    have hrank := (L : E →ₗ[ℝ] F).finrank_range_add_finrank_ker
    rw [show (L : E →ₗ[ℝ] F).range = ⊤ from hrange, finrank_top] at hrank
    omega
  have hcomp : LipschitzOnWith K (fun w : L.ker => LI (a + (w : E)))
      {w : L.ker | a + (w : E) ∈ t} := by
    refine LipschitzOnWith.of_dist_le_mul fun w hw w' hw' => ?_
    have h1 : dist (LI (a + (w : E))) (LI (a + (w' : E))) ≤
        K * dist (a + (w : E)) (a + (w' : E)) :=
        hLip.dist_le_mul (x := a + (w : E)) hw (y := a + (w' : E)) hw'
    calc dist (LI (a + (w : E))) (LI (a + (w' : E)))
        ≤ K * dist (a + (w : E)) (a + (w' : E)) := h1
      _ = K * dist w w' := by rw [dist_add_left, Subtype.dist_eq]
  refine ⟨L.ker, fun w : L.ker => LI (a + (w : E)), {w : L.ker | a + (w : E) ∈ U₀},
    U, hfin, hU₀open.preimage (by fun_prop), ⟨K, {w : L.ker | a + (w : E) ∈ t}, ?_, hcomp⟩,
    hUopen, haU, ?_⟩
  · intro w hw
    exact (hU₀sub hw).2
  · rintro y ⟨hy0, hyU⟩
    have hyLI : LI ((fun y : E => y + σ (Φ y - (L y - L a))) y) = y := (hUsub hyU).1.1
    have hyΘ : (fun y : E => y + σ (Φ y - (L y - L a))) y ∈ U₀ := (hUsub hyU).2
    have hkey : L ((fun y : E => y + σ (Φ y - (L y - L a))) y - a) = Φ y := by
      rw [map_sub, map_add, hσL]
      abel
    have hker : (fun y : E => y + σ (Φ y - (L y - L a))) y - a ∈ L.ker := by
      rw [LinearMap.mem_ker]
      exact hkey.trans hy0
    refine ⟨⟨(fun y : E => y + σ (Φ y - (L y - L a))) y - a, hker⟩, ?_, ?_⟩
    · show a + ((fun y : E => y + σ (Φ y - (L y - L a))) y - a) ∈ U₀
      have : a + ((fun y : E => y + σ (Φ y - (L y - L a))) y - a) =
          (fun y : E => y + σ (Φ y - (L y - L a))) y := by abel
      rw [this]
      exact hyΘ
    · show LI (a + ((fun y : E => y + σ (Φ y - (L y - L a))) y - a)) = y
      have : a + ((fun y : E => y + σ (Φ y - (L y - L a))) y - a) =
          (fun y : E => y + σ (Φ y - (L y - L a))) y := by abel
      rw [this]
      exact hyLI

/-- **The level set of a surjection and its image under a `C¹` map have small Hausdorff
dimension.** -/
theorem dimH_image_le_of_surjective {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Φ : E → F) (D : Set E)
    (hΦ : ∀ x ∈ D, ContDiffAt ℝ 1 Φ x)
    (hsurj : ∀ x ∈ D, Φ x = 0 → Function.Surjective (fderiv ℝ Φ x))
    (φ : E → G) (hφ : ∀ x ∈ D, ContDiffAt ℝ 1 φ x) :
    dimH (φ '' (D ∩ Φ ⁻¹' {0})) ≤ ((Module.finrank ℝ E - Module.finrank ℝ F : ℕ) : ENNReal) := by
  have hlevel : dimH (D ∩ Φ ⁻¹' {0}) ≤
      ((Module.finrank ℝ E - Module.finrank ℝ F : ℕ) : ENNReal) := by
    refine dimH_le_of_local_lipschitz_param fun x hx => ?_
    obtain ⟨H, g, V, U, hfin, hVopen, hLip, hUopen, hxU, hsub⟩ :=
      exists_local_param_of_contDiffAt Φ x (hΦ x hx.1) hx.2 (hsurj x hx.1 hx.2)
    exact ⟨H, g, V, U, by rw [hfin], hVopen, hLip, hUopen, hxU,
      fun y hy => hsub ⟨hy.1.2, hy.2⟩⟩
  refine (dimH_image_le_of_locally_lipschitzOn fun x hx => ?_).trans hlevel
  obtain ⟨K, t, ht, hK⟩ := (hφ x hx.1).exists_lipschitzOnWith
  exact ⟨K, t, nhdsWithin_le_nhds ht, hK⟩


end Work.Projection
