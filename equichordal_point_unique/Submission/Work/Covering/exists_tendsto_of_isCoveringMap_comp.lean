import Mathlib

/-!
# A path whose image under a covering map has a limit has a limit

If `p : X → Y` is a covering map and `ζ : ℝ → X` is a path defined on `(-∞,1)` whose image
`p ∘ ζ` converges to `y` as `t → 1⁻`, then `ζ` itself converges as `t → 1⁻`.

The point is the usual sheet argument: `y` has an evenly covered neighbourhood `U`; for `t`
sufficiently close to `1` the point `p (ζ t)` lies in `U`, so `ζ t` lies in `p ⁻¹' U`. The
preimage `p ⁻¹' U` splits into disjoint open sheets, and the connected tail `ζ ((r,1))` must lie
in a single sheet. On that sheet `ζ` is the inverse of the (local) homeomorphism, hence
converges.

This is used in the equichordal point problem to see that a radius of the uniformizing disc
does not converge in the base surface.
-/

open Filter _root_.Topology

/-- **Covering maps do not create limits.** If `p ∘ ζ` has a limit at `1⁻` for a path `ζ`
defined on `(-∞, 1)`, then `ζ` has a limit at `1⁻`. -/
theorem exists_tendsto_of_isCoveringMap_comp {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {p : X → Y} (hp : IsCoveringMap p) {ζ : ℝ → X}
    (hζ : ContinuousOn ζ (Set.Iio 1)) {y : Y}
    (hy : Tendsto (fun t : ℝ => p (ζ t)) (nhdsWithin 1 (Set.Iio 1)) (nhds y)) :
    ∃ x : X, Tendsto ζ (nhdsWithin 1 (Set.Iio 1)) (nhds x) := by
  classical
  obtain ⟨hI, U, hyU, hUo, _hpUo, H, hH⟩ := hp y
  have hmemU : U ∈ nhds y := hUo.mem_nhds hyU
  have hev : ∀ᶠ t in nhdsWithin 1 (Set.Iio 1), p (ζ t) ∈ U := hy hmemU
  obtain ⟨b, hb1, hbsub⟩ := (nhdsLT_basis (1 : ℝ)).mem_iff.1 hev
  have hIoo_mem : Set.Ioo b 1 ∈ nhdsWithin 1 (Set.Iio 1) :=
    (nhdsLT_basis (1 : ℝ)).mem_iff.mpr ⟨b, hb1, fun t ht => ht⟩
  have ht0 : (b + 1) / 2 ∈ Set.Ioo b 1 := ⟨by linarith, by linarith⟩
  -- a point of the fibre of `y`, read off from the sheet `U`
  let i : ↥(p ⁻¹' {y}) := (H ⟨ζ ((b + 1) / 2), hbsub ht0⟩).2
  -- the sheet index is constant along a connected tail
  have hconst : ∀ t (ht : t ∈ Set.Ioo b 1), (H ⟨ζ t, hbsub ht⟩).2 = i := by
    intro t ht
    have hcont : Continuous fun s : ↥(Set.Ioo b 1) => (H ⟨ζ s.1, hbsub s.2⟩).2 := by
      apply Continuous.comp continuous_snd
      apply Continuous.comp H.continuous
      exact Continuous.subtype_mk
        (hζ.comp_continuous continuous_subtype_val (fun s => s.2.2)) (fun s => hbsub s.2)
    haveI : PreconnectedSpace ↥(Set.Ioo b 1) :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
    have hpre : IsPreconnected (Set.range fun s : ↥(Set.Ioo b 1) => (H ⟨ζ s.1, hbsub s.2⟩).2) :=
      isPreconnected_range hcont
    have hmem : i ∈ Set.range fun s : ↥(Set.Ioo b 1) => (H ⟨ζ s.1, hbsub s.2⟩).2 :=
      ⟨⟨(b + 1) / 2, ht0⟩, rfl⟩
    have hcomp := hpre.subset_connectedComponent hmem
    have hsub : connectedComponent i ⊆ ({i} : Set ↥(p ⁻¹' {y})) :=
      IsClopen.connectedComponent_subset
        ⟨isClosed_singleton, (discreteTopology_iff_isOpen_singleton.mp hI) i⟩ (Set.mem_singleton i)
    exact Set.mem_singleton_iff.mp (hsub (hcomp ⟨⟨t, ht⟩, rfl⟩))
  -- the totalised family of points of `U`
  let K : ℝ → ↥U := fun t => if ht : t ∈ Set.Ioo b 1 then ⟨p (ζ t), hbsub ht⟩ else ⟨y, hyU⟩
  have hKeq : ∀ᶠ t in nhdsWithin 1 (Set.Iio 1), p (ζ t) = (K t : Y) := by
    filter_upwards [hIoo_mem] with t ht
    dsimp only [K]
    rw [dite_eq_left ht]
  have hK : Tendsto K (nhdsWithin 1 (Set.Iio 1)) (nhds (⟨y, hyU⟩ : ↥U)) :=
    tendsto_subtype_rng.mpr (hy.congr' hKeq)
  have hKprod : Tendsto (fun t => (K t, i)) (nhdsWithin 1 (Set.Iio 1))
      (nhds ((⟨y, hyU⟩ : ↥U), i)) := hK.prodMk_nhds tendsto_const_nhds
  refine ⟨(H.symm ((⟨y, hyU⟩ : ↥U), i)).val, ?_⟩
  have h1 : Tendsto (fun t => (H.symm ((K t), i)).val) (nhdsWithin 1 (Set.Iio 1))
      (nhds (H.symm ((⟨y, hyU⟩ : ↥U), i)).val) :=
    (continuous_subtype_val.tendsto _).comp
      ((H.symm.continuous.tendsto ((⟨y, hyU⟩ : ↥U), i)).comp hKprod)
  refine h1.congr' ?_
  filter_upwards [hIoo_mem] with t ht
  have hKt : K t = (⟨p (ζ t), hbsub ht⟩ : ↥U) := by dsimp only [K]; rw [dite_eq_left ht]
  rw [hKt]
  have hHt2 : (H ⟨ζ t, hbsub ht⟩).1 = (⟨p (ζ t), hbsub ht⟩ : ↥U) :=
    Subtype.ext (hH ⟨ζ t, hbsub ht⟩)
  have hHt3 : (H ⟨ζ t, hbsub ht⟩).2 = i := hconst t ht
  have hHt4 : (H ⟨ζ t, hbsub ht⟩ : ↥U × ↥(p ⁻¹' {y}))
      = ((⟨p (ζ t), hbsub ht⟩ : ↥U), i) := Prod.eq_iff_fst_eq_snd_eq.mpr ⟨hHt2, hHt3⟩
  have h := congrArg (fun z => H.symm z) hHt4
  rw [Homeomorph.symm_apply_apply] at h
  exact (congrArg Subtype.val h.symm)
