import Mathlib

/-!
# `Work.Horn.HB.isCompact_preimage_of_isCoveringMap_finite`

The preimage under a covering map of a compact set on which the fibres are finite is compact.

The base `B` is only assumed locally compact, *not* Hausdorff, so this is not a consequence of
Mathlib's proper-map API (`isProperMap_iff_isCompact_preimage` needs `T2Space` +
`CompactlyCoherentSpace`), and `IsProperMap.isCompact_preimage` would need the map to be closed,
which a covering map with infinite fibres (e.g. `ℝ → S¹`) is not.  The proof is the honest
finite-cover argument.

Fix `b ∈ K` and a trivialisation `H : ↥(p ⁻¹' Ub) ≃ₜ ↥Ub × ↥(p ⁻¹' {b})` of `p` over an evenly
covered open `Ub ∋ b`.  The fibre `p ⁻¹' {b}` is finite, hence so is the family of "sheets"
`A_f := {x ∈ p ⁻¹' Ub | (H x).2 = f}`, and `p` maps each sheet homeomorphically onto `Ub`.  For
each sheet `f` the point of `A_f` above `b` is in the open cover, so some `U (idx f)` contains a
neighbourhood `Vf f` of `b` *inside that sheet* (`Vf f` is the image of an open subset of `Ub`
under the open map `Ub ↪ B`).  Intersecting the `Vf f` over the finitely many `f` (and with `Ub`)
produces a neighbourhood `Vb ∋ b` whose preimage is covered by the finitely many `U (idx f)`:
indeed, if `x ∈ p ⁻¹' Vb`, the sheet `g` of `x` obeys `g ∈ p ⁻¹' {b}`, so `p x ∈ Vb ⊆ Vf g`, which
forces `x ∈ U (idx g)` because `p` is injective on the sheet `A_g`.

Compactness of `K` then supplies finitely many such `Vb` covering `K`, whose index sets combine to
a finite subcover of `p ⁻¹' K` by the given open cover.
-/

namespace Work.Horn.HB

open Set Topology

theorem isCompact_preimage_of_isCoveringMap_finite {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] [LocallyCompactSpace B] {p : E → B} (hcov : IsCoveringMap p)
    {K : Set B} (hK : IsCompact K) (hfin : ∀ b ∈ K, (p ⁻¹' {b}).Finite) :
    IsCompact (p ⁻¹' K) := by
  classical
  refine (isCompact_iff_finite_subcover).mpr ?_
  intro ι U hUo hSU
  -- Crux: every `b ∈ K` has a neighbourhood whose preimage is covered by finitely many `U i`.
  have crux : ∀ b ∈ K, ∃ vT : Set B × Finset ι,
      vT.1 ∈ 𝓝 b ∧ p ⁻¹' vT.1 ⊆ ⋃ i ∈ vT.2, U i := by
    intro b hbK
    -- local trivialisation of `p` at `b`
    obtain ⟨_, Ub, hbUb, hUb, _, H, hH⟩ := hcov b
    have hft : Fintype ↥(p ⁻¹' {b}) := (hfin b hbK).fintype
    -- the point of the sheet `f` above `b` lies in the cover, giving an index `idx f`
    have hchoice : ∀ f : ↥(p ⁻¹' {b}), ∃ i : ι,
        ((H.symm (⟨b, hbUb⟩, f) : ↥(p ⁻¹' Ub)) : E) ∈ U i := by
      intro f
      have hkey : p ((H.symm (⟨b, hbUb⟩, f) : ↥(p ⁻¹' Ub)) : E) = b := by
        have h1 := hH (H.symm (⟨b, hbUb⟩, f))
        rw [Homeomorph.apply_symm_apply] at h1
        exact h1.symm
      have hmem : ((H.symm (⟨b, hbUb⟩, f) : ↥(p ⁻¹' Ub)) : E) ∈ p ⁻¹' K := by
        rw [mem_preimage, hkey]
        exact hbK
      exact mem_iUnion.mp (hSU hmem)
    let idx : ↥(p ⁻¹' {b}) → ι := fun f => Classical.choose (hchoice f)
    have hidx : ∀ f, ((H.symm (⟨b, hbUb⟩, f) : ↥(p ⁻¹' Ub)) : E) ∈ U (idx f) :=
      fun f => Classical.choose_spec (hchoice f)
    -- the neighbourhood of `b` inside the sheet `f` on which `p` lands in `U (idx f)`
    let Vf : ↥(p ⁻¹' {b}) → Set B := fun f =>
      Subtype.val '' {u : ↥Ub | ((H.symm (u, f) : ↥(p ⁻¹' Ub)) : E) ∈ U (idx f)}
    have hVfopen : ∀ f, IsOpen (Vf f) := by
      intro f
      have hcont : Continuous (fun u : ↥Ub => ((H.symm (u, f) : ↥(p ⁻¹' Ub)) : E)) :=
        continuous_subtype_val.comp (H.symm.continuous.comp
          (continuous_id.prodMk continuous_const))
      exact hUb.isOpenMap_subtype_val _ ((hUo (idx f)).preimage hcont)
    have hbVf : ∀ f, b ∈ Vf f := fun f => ⟨⟨b, hbUb⟩, hidx f, rfl⟩
    have hVbopen : IsOpen (Ub ∩ ⋂ f, Vf f) := hUb.inter (isOpen_iInter_of_finite hVfopen)
    have hbVb : b ∈ Ub ∩ ⋂ f, Vf f := ⟨hbUb, mem_iInter.mpr hbVf⟩
    let T : Finset ι := (@Finset.univ _ hft).image idx
    refine ⟨(Ub ∩ ⋂ f, Vf f, T), hVbopen.mem_nhds hbVb, ?_⟩
    intro x hx
    have hxUb : p x ∈ Ub := hx.1
    have hxVf : ∀ f, p x ∈ Vf f := fun f => mem_iInter.mp hx.2 f
    -- `g` is the sheet of `x`, so the sheet of `p x` over `g` is exactly `x`
    let g : ↥(p ⁻¹' {b}) := (H ⟨x, hxUb⟩).2
    obtain ⟨u, hu, huv⟩ := hxVf g
    have hueq : u = ⟨p x, hxUb⟩ := Subtype.ext huv
    have hHg : H ⟨x, hxUb⟩ = ((⟨p x, hxUb⟩ : ↥Ub), g) := by
      refine Prod.ext ?_ rfl
      exact Subtype.ext (hH ⟨x, hxUb⟩)
    have hsymm : ((H.symm ((⟨p x, hxUb⟩ : ↥Ub), g) : ↥(p ⁻¹' Ub)) : E) = x := by
      have h1 : H.symm (((⟨p x, hxUb⟩ : ↥Ub), g)) = (⟨x, hxUb⟩ : ↥(p ⁻¹' Ub)) := by
        rw [← hHg, Homeomorph.symm_apply_apply]
      rw [h1]
    have hu_raw : ((H.symm (u, g) : ↥(p ⁻¹' Ub)) : E) ∈ U (idx g) := hu
    have hu' : ((H.symm ((⟨p x, hxUb⟩ : ↥Ub), g) : ↥(p ⁻¹' Ub)) : E) ∈ U (idx g) := by
      rw [hueq] at hu_raw
      exact hu_raw
    rw [hsymm] at hu'
    exact mem_iUnion₂.mpr ⟨idx g, Finset.mem_image.mpr ⟨g, @Finset.mem_univ _ hft g, rfl⟩, hu'⟩
  -- turn the local statement into a global one
  let F : B → Set B × Finset ι := fun b =>
    if hb : b ∈ K then Classical.choose (crux b hb) else (univ, ∅)
  have hFmem : ∀ b ∈ K, (F b).1 ∈ 𝓝 b := by
    intro b hb
    simp only [F, dite_eq_left hb]
    exact (Classical.choose_spec (crux b hb)).1
  have hFsub : ∀ b ∈ K, p ⁻¹' (F b).1 ⊆ ⋃ i ∈ (F b).2, U i := by
    intro b hb
    simp only [F, dite_eq_left hb]
    exact (Classical.choose_spec (crux b hb)).2
  obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover (fun b => (F b).1) hFmem
  refine ⟨t.biUnion (fun b => (F b).2), ?_⟩
  intro x hx
  have hpxK : p x ∈ K := hx
  obtain ⟨b, hbt, hpb⟩ := mem_iUnion₂.mp (hKt hpxK)
  obtain ⟨i, hiT, hxi⟩ := mem_iUnion₂.mp (hFsub b (htK b hbt) hpb)
  exact mem_iUnion₂.mpr ⟨i, Finset.mem_biUnion.mpr ⟨b, hbt, hiT⟩, hxi⟩

end Work.Horn.HB
