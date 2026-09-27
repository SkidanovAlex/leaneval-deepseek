import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2Lead.twistDefs
import Submission.Work.Drive.N2Lead.starShapedRadial
import Submission.Work.Drive.N2Lead.starShapedComponents
import Submission.Work.Drive.N2Lead.smoothArgLiftCinf
import Submission.Work.Drive.N2Lead.isCertifiedAt_of_roundImage
import Submission.Work.Drive.N2Lead.isLevelIsotopy_squash
import Submission.Work.Drive.N2Lead.isLevelIsotopy_ambient_local
import Submission.Work.Drive.N2.exists_levelComponentCurves
import Submission.Work.Drive.N2C.levelCurves_ofComponentCurves

set_option maxHeartbeats 1000000

/-!
# The star-regions certificate: the radial push of the level picture

This is the engine of `Work.Drive.N2Lead.isCertifiedAt_of_starRegions`
(`Submission/Work/Drive/N2Lead/isCertifiedAt_of_starRegions.lean`).

The level picture `y ↦ g y` (`g : M → ℝ³`, `f` a Morse function, `u` a regular value) is assumed to
be split by finitely many pairwise disjoint convex open *regions* `Ω k ⊆ ℂ` of the plane, each
containing the closed ball of radius `ρ k > 0` about its centre `o k`, and such that

* the picture's planar projection `proj2 (g ·)` never meets the centre `o k` on the region `Ω k`
  and has non-vanishing angular rate about `o k` there (`hrate`), and
* one ray of `Ω k` is hit at most once by the level picture (`hhit`).

The engine has two halves:

* the **component analysis** of the level (`isRadialGraph_of_starRegion`): each connected component
  of the level is mapped by `proj2 ∘ g` onto a *radial graph* about the centre of the region it
  occupies (every ray is hit exactly once, and the angular rate is strictly monotone); this uses the
  argument lift `smoothArgLiftComplex`;
* the **piecewise radial push** (`pushMap`) which at time `s` moves, inside every region `Ω k`, each
  point radially towards the round circle of radius `ρ k` about `o k` (a convex combination stays in
  `Ω k`, and the target point lies in the closed ball contained in `Ω k`).
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Function Filter

noncomputable section

/-! ## A continuous path in a union of pairwise disjoint open sets -/

/-- **A continuous path whose values lie in a union of pairwise disjoint open sets lies in one of
them.**  The preimage of the set containing the value at `0` is open (openness) and closed (the
complement is the union of the other preimages, each open), and `ℝ` is preconnected. -/
theorem pathRegionConst {ι : Type*} {Ω : ι → Set ℂ} (hΩ : ∀ i, IsOpen (Ω i))
    (hdisj : Pairwise fun i j => Disjoint (Ω i) (Ω j))
    {γ : ℝ → ℂ} (hγ : Continuous γ) (h : ∀ t : ℝ, ∃ i, γ t ∈ Ω i) :
    ∃ i, ∀ t : ℝ, γ t ∈ Ω i := by
  obtain ⟨i₀, hi₀⟩ := h 0
  refine ⟨i₀, fun t => ?_⟩
  have hopen : IsOpen (γ ⁻¹' Ω i₀) := (hΩ i₀).preimage hγ
  have hclosed : IsClosed (γ ⁻¹' Ω i₀) := by
    rw [← isOpen_compl_iff]
    have hcompl : (γ ⁻¹' Ω i₀)ᶜ = ⋃ i : {i : ι // i ≠ i₀}, γ ⁻¹' Ω i.1 := by
      ext t
      constructor
      · intro ht
        obtain ⟨i, hi⟩ := h t
        have hne : i ≠ i₀ := fun hh => ht (hh ▸ hi)
        exact Set.mem_iUnion.2 ⟨⟨i, hne⟩, hi⟩
      · intro hcon
        obtain ⟨i, hit⟩ := Set.mem_iUnion.1 hcon
        exact Set.disjoint_left.mp (hdisj i.2) hit
    rw [hcompl]
    exact isOpen_iUnion fun i => (hΩ i.1).preimage hγ
  rcases (isClopen_iff.mp (⟨hclosed, hopen⟩ : IsClopen (γ ⁻¹' Ω i₀))) with h0 | h0
  · have hmem : (0 : ℝ) ∈ γ ⁻¹' Ω i₀ := hi₀
    rw [h0] at hmem
    exact absurd hmem (Set.notMem_empty 0)
  · show t ∈ γ ⁻¹' Ω i₀
    rw [h0]
    trivial

/-! ## The piecewise radial push -/

section Push

variable {K : ℕ} {Ω : Fin K → Set ℂ} {o : Fin K → ℂ} {ρ : Fin K → ℝ}

/-- The points of `ℝ³` whose planar projection lies in one of the regions and is not its centre. -/
def PushDomain (Ω : Fin K → Set ℂ) (o : Fin K → ℂ) : Set E3 :=
  {v : E3 | ∃ k : Fin K, proj2 v ∈ Ω k ∧ proj2 v ≠ o k}

/-- **The piecewise radial push.**  If the planar projection of `v` lies in the region `Ω k` at a
point different from the centre `o k`, push `v` radially (inside the plane) towards the round circle
of radius `ρ k` about `o k`: at time `s` the radial coordinate `r` is sent to
`(1 - σ s) r + σ s ρ k` with `σ = Real.smoothTransition`, so at `s = 0` nothing moves and at `s ≥ 1`
the image lies on the circle.  Off the domain the map is the identity. -/
noncomputable def pushMap (Ω : Fin K → Set ℂ) (o : Fin K → ℂ) (ρ : Fin K → ℝ) (s : ℝ) (v : E3) :
    E3 := by
  classical
  exact if h : v ∈ PushDomain Ω o then
    radFlat (pl (o (Classical.choose h))) (ρ (Classical.choose h)) s v
  else v

/-- On a region, the push is the radial map with that region's centre and radius. -/
theorem pushMap_of_mem (hdisj : Pairwise fun k l : Fin K => Disjoint (Ω k) (Ω l))
    (s : ℝ) (v : E3) (k : Fin K) (hk : proj2 v ∈ Ω k) (hne : proj2 v ≠ o k) :
    pushMap Ω o ρ s v = radFlat (pl (o k)) (ρ k) s v := by
  have h : v ∈ PushDomain Ω o := ⟨k, hk, hne⟩
  rw [pushMap, dif_pos h]
  have hch : proj2 v ∈ Ω (Classical.choose h) := (Classical.choose_spec h).1
  have hkeq : Classical.choose h = k := by
    by_contra hk'
    exact (Set.disjoint_left.mp (hdisj (Ne.symm hk')) hk) hch
  rw [hkeq]

/-- The push does not move anything at time `0`. -/
theorem pushMap_zero (Ω : Fin K → Set ℂ) (o : Fin K → ℂ) (ρ : Fin K → ℝ) (v : E3) :
    pushMap Ω o ρ 0 v = v := by
  by_cases h : v ∈ PushDomain Ω o
  · rw [pushMap, dif_pos h]
    exact radFlat_zero _ _ v
  · rw [pushMap, dif_neg h]

/-- The push fixes the complement of its domain. -/
theorem pushMap_eq_self {s : ℝ} {v : E3} (h : v ∉ PushDomain Ω o) : pushMap Ω o ρ s v = v := by
  rw [pushMap, dif_neg h]

/-- The domain of the push is open. -/
theorem isOpen_pushDomain (hΩ : ∀ k : Fin K, IsOpen (Ω k)) : IsOpen (PushDomain Ω o) := by
  have h : PushDomain Ω o = ⋃ k : Fin K, {v : E3 | proj2 v ∈ Ω k ∧ proj2 v ≠ o k} := by
    ext v
    simp only [PushDomain, mem_setOf_eq, mem_iUnion]
  rw [h]
  exact isOpen_iUnion fun k =>
    ((hΩ k).preimage proj2CLM.continuous).inter (isOpen_ne.preimage proj2CLM.continuous)

/-- **The uncurried push is smooth at every point of its domain.** -/
theorem contMDiffAt_uncurry_pushMap (hΩ : ∀ k : Fin K, IsOpen (Ω k))
    (hdisj : Pairwise fun k l : Fin K => Disjoint (Ω k) (Ω l)) {s : ℝ} {v : E3}
    (hv : v ∈ PushDomain Ω o) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E3)) 𝓘(ℝ, E3) tpC
      (Function.uncurry (pushMap Ω o ρ)) (s, v) := by
  obtain ⟨k, hk, hne⟩ := hv
  have hpu : proj2 (v - pl (o k)) ≠ 0 := by
    rw [proj2_sub, proj2_pl]
    exact sub_ne_zero.mpr hne
  have hcomp : ContDiffAt ℝ tpC
      (fun p : ℝ × E3 => radFlat (pl (o k)) (ρ k) p.1 p.2) (s, v) := by
    have haux := contDiffAt_uncurry_radFlatAux (o := pl (o k)) (r := ρ k) (s := s)
      (u := v - pl (o k)) hpu
    have hlin : ContDiffAt ℝ tpC (fun p : ℝ × E3 => ((p.1, p.2 - pl (o k)) : ℝ × E3)) (s, v) :=
      contDiffAt_fst.prodMk (contDiffAt_snd.sub contDiffAt_const)
    have h2 := haux.comp (s, v) hlin
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp_apply, Function.uncurry_apply_pair]
    rw [radFlat_eq_aux]
  have hmodel : ContMDiffAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E3)) 𝓘(ℝ, E3) tpC
      (fun p : ℝ × E3 => radFlat (pl (o k)) (ρ k) p.1 p.2) (s, v) := by
    have h1 : ContMDiffAt 𝓘(ℝ, ℝ × E3) 𝓘(ℝ, E3) tpC
        (fun p : ℝ × E3 => radFlat (pl (o k)) (ρ k) p.1 p.2) (s, v) :=
      contMDiffAt_iff_contDiffAt.mpr hcomp
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h1
    exact h1
  refine hmodel.congr_of_eventuallyEq ?_
  have hU : {v' : E3 | proj2 v' ∈ Ω k ∧ proj2 v' ≠ o k} ∈ 𝓝 v :=
    Filter.inter_mem (((hΩ k).preimage proj2CLM.continuous).mem_nhds hk)
      ((isOpen_ne.preimage proj2CLM.continuous).mem_nhds hne)
  have hU' : (fun p : ℝ × E3 => p.2) ⁻¹' {v' : E3 | proj2 v' ∈ Ω k ∧ proj2 v' ≠ o k}
      ∈ 𝓝 (s, v) :=
    continuous_snd.continuousAt.preimage_mem_nhds hU
  filter_upwards [hU'] with p hp
  exact pushMap_of_mem hdisj p.1 p.2 k hp.1 hp.2

/-- **The planar projection of the push lies in the region.**  The push is a convex combination of
the original point and of the point of the round circle of radius `ρ k` in the same direction, which
lies in the closed ball contained in `Ω k`. -/
theorem proj2_pushMap_mem (hdisj : Pairwise fun k l : Fin K => Disjoint (Ω k) (Ω l))
    (hρ : ∀ k : Fin K, 0 < ρ k)
    (hconv : ∀ k : Fin K, Convex ℝ (Ω k))
    (hball : ∀ k : Fin K, Metric.closedBall (o k) (ρ k) ⊆ Ω k)
    {s : ℝ} {v : E3} {k : Fin K} (hk : proj2 v ∈ Ω k) (hne : proj2 v ≠ o k) :
    proj2 (pushMap Ω o ρ s v) ∈ Ω k := by
  have hpm : pushMap Ω o ρ s v = radFlat (pl (o k)) (ρ k) s v :=
    pushMap_of_mem (K := K) (Ω := Ω) (o := o) (ρ := ρ) hdisj s v k hk hne
  rw [hpm]
  have hlam : 0 < ‖proj2 v - o k‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hval : proj2 (radFlat (pl (o k)) (ρ k) s v)
      = o k + radCoeff (ρ k) s (v - pl (o k)) • (proj2 v - o k) := by
    have h1 : radFlat (pl (o k)) (ρ k) s v
        = (radFlat (pl (o k)) (ρ k) s v - pl (o k)) + pl (o k) := by abel
    rw [h1, proj2_add, proj2_radFlat_sub, proj2_sub, proj2_pl]
    abel
  have hcoeff : radCoeff (ρ k) s (v - pl (o k))
      = (1 - Real.smoothTransition s) + Real.smoothTransition s * (ρ k / ‖proj2 v - o k‖) := by
    rw [radCoeff_apply, proj2_sub, proj2_pl]
  rw [hval, hcoeff]
  set σ := Real.smoothTransition s with hσ
  have hσ0 : 0 ≤ σ := Real.smoothTransition.nonneg s
  have hσ1 : σ ≤ 1 := Real.smoothTransition.le_one s
  have hpt2 : o k + (ρ k / ‖proj2 v - o k‖) • (proj2 v - o k) ∈ Ω k := by
    refine hball k ?_
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsub : o k + (ρ k / ‖proj2 v - o k‖) • (proj2 v - o k) - o k
        = (ρ k / ‖proj2 v - o k‖) • (proj2 v - o k) := by abel
    have hnorm : ‖(ρ k / ‖proj2 v - o k‖) • (proj2 v - o k)‖ = ρ k := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (hρ k) hlam)]
      field_simp
    rw [hsub, hnorm]
  have hcomb : (1 - σ) • (proj2 v) + σ • (o k + (ρ k / ‖proj2 v - o k‖) • (proj2 v - o k)) ∈ Ω k :=
    (convex_iff_add_mem.mp (hconv k)) hk hpt2 (by linarith) hσ0 (by ring)
  have hkey : o k + ((1 - σ) + σ * (ρ k / ‖proj2 v - o k‖)) • (proj2 v - o k)
      = (1 - σ) • (proj2 v) + σ • (o k + (ρ k / ‖proj2 v - o k‖) • (proj2 v - o k)) := by
    module
  rw [hkey]
  exact hcomb

end Push

end

end Work.Drive.N2Lead
