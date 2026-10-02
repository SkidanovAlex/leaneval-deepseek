import Mathlib
import Submission.Work.ELAssembly.covering_sheet
import Submission.Work.ELAssembly.fibre_equiv
import Submission.Work.ELPull.isCoveringMapOn_tsqIterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A connected cover of a connected base with a minimal fibre is a bijection

`Work.ELAssembly.bijOn_of_isCoveringMapOn_of_fibre`: if `f : ℂ → ℂ` is a covering map over the
open preconnected set `V`, `U` is an open preconnected subset of `f ⁻¹' V` whose frontier does
not meet `f ⁻¹' V` (hypothesis `hcl`), and the fibre of `f` over some `v₀ ∈ V` meets `U` in at
most one point, then `f` maps `U` bijectively onto `V`.

The proof shows that the "number of sheets" of the covering over `U`, i.e. the cardinal (and
more refined: the emptiness and the subsingleton-ness) of `U ∩ f ⁻¹' {z}`, is locally constant
as a function of `z`; since `V` is preconnected it is constant on `V`.  The value at `v₀` is
`≤ 1` by hypothesis and `≥ 1` because `U` is nonempty, so every fibre is a singleton.

The local constancy is proved by choosing around `z ∈ V` a preconnected evenly covered
neighbourhood `W ⊆ V`, restricting the trivialisation of the covering to `W`
(`Work.ELAssembly.restrictHomeo`), and observing that the sheets over `W` are either entirely
inside `U` or disjoint from it (because `U` is clopen over `f ⁻¹' W` there); hence the fibres
over all points of `W` are in bijection with the same index set `J`
(`Work.ELAssembly.fibre_equiv`).
-/

namespace Work.ELAssembly

open Set

/-- An `Equiv` between two subtypes transfers nonemptiness of the underlying sets. -/
lemma nonempty_iff_of_equiv {α β : Type*} {s : Set α} {t : Set β} (e : ↥s ≃ ↥t) :
    s.Nonempty ↔ t.Nonempty :=
  ⟨fun ⟨a, ha⟩ => ⟨(e ⟨a, ha⟩).1, (e ⟨a, ha⟩).2⟩,
   fun ⟨b, hb⟩ => ⟨(e.symm ⟨b, hb⟩).1, (e.symm ⟨b, hb⟩).2⟩⟩

/-- An `Equiv` between two subtypes transfers the subsingleton property of the underlying
sets. -/
lemma subsingleton_iff_of_equiv {α β : Type*} {s : Set α} {t : Set β} (e : ↥s ≃ ↥t) :
    s.Subsingleton ↔ t.Subsingleton := by
  constructor
  · intro hs a ha b hb
    have h : e.symm ⟨a, ha⟩ = e.symm ⟨b, hb⟩ :=
      Subtype.ext (hs (e.symm ⟨a, ha⟩).2 (e.symm ⟨b, hb⟩).2)
    have h2 : (⟨a, ha⟩ : ↥t) = ⟨b, hb⟩ := by simpa using congrArg e h
    exact Subtype.ext_iff.mp h2
  · intro ht a ha b hb
    have h : (⟨a, ha⟩ : ↥s) = ⟨b, hb⟩ :=
      e.injective (Subtype.ext (ht (e ⟨a, ha⟩).2 (e ⟨b, hb⟩).2))
    exact Subtype.ext_iff.mp h

/-- If `z ∉ V` then no point of `U` maps to `z`. -/
lemma fiber_empty {f : ℂ → ℂ} {U V : Set ℂ} (hmap : Set.MapsTo f U V) {z : ℂ} (hz : z ∉ V) :
    U ∩ f ⁻¹' {z} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hxU, hxz⟩
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hxz
  exact hz (hxz ▸ hmap hxU)

/-- **Local constancy of the fibre of `U`.**  For every `z ∈ V` there is an open neighbourhood
`W ∋ z` such that over all `z' ∈ W` the fibre `U ∩ f ⁻¹' {z'}` has the same nonemptiness and
subsingleton-ness as the fibre over `z`. -/
lemma fibre_local {f : ℂ → ℂ} {U V : Set ℂ}
    (hf : Continuous f) (hcov : IsCoveringMapOn f V)
    (hUo : IsOpen U) (hVo : IsOpen V) (hmap : Set.MapsTo f U V)
    (hcl : ∀ x ∈ closure U, f x ∈ V → x ∈ U)
    {z : ℂ} (hz : z ∈ V) :
    ∃ W : Set ℂ, z ∈ W ∧ IsOpen W ∧
      (∀ z' ∈ W, (U ∩ f ⁻¹' {z'}).Nonempty ↔ (U ∩ f ⁻¹' {z}).Nonempty) ∧
      (∀ z' ∈ W, (U ∩ f ⁻¹' {z'}).Subsingleton ↔ (U ∩ f ⁻¹' {z}).Subsingleton) := by
  obtain ⟨-, W₀, hzW₀, hW₀o, -, H, hH⟩ := hcov z hz
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp ((hW₀o.inter hVo).mem_nhds ⟨hzW₀, hz⟩)
  have hzW : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  have hWp : IsPreconnected (Metric.ball z r) := (convex_ball z r).isPreconnected
  have hWW₀ : Metric.ball z r ⊆ W₀ := hball.trans Set.inter_subset_left
  have hWV : Metric.ball z r ⊆ V := hball.trans Set.inter_subset_right
  refine ⟨Metric.ball z r, hzW, Metric.isOpen_ball, ?_, ?_⟩
  · let H' := restrictHomeo hf hWW₀ H hH
    have hH' : ∀ e, (H' e).1.1 = f e.1 := fun e => restrictHomeo_apply hf hWW₀ H hH e
    have hAcl : IsClopen (Subtype.val ⁻¹' U : Set ↥(f ⁻¹' Metric.ball z r)) := by
      refine ⟨?_, hUo.preimage continuous_subtype_val⟩
      rw [isClosed_induced_iff]
      refine ⟨closure U, isClosed_closure, ?_⟩
      ext e
      simp only [Set.mem_preimage]
      exact ⟨fun he => hcl e.1 he (hWV e.2), fun he => subset_closure he⟩
    intro z' hz'
    exact (nonempty_iff_of_equiv (fibre_equiv hWp H' hH' hAcl hzW z' hz')).trans
      (nonempty_iff_of_equiv (fibre_equiv hWp H' hH' hAcl hzW z hzW)).symm
  · let H' := restrictHomeo hf hWW₀ H hH
    have hH' : ∀ e, (H' e).1.1 = f e.1 := fun e => restrictHomeo_apply hf hWW₀ H hH e
    have hAcl : IsClopen (Subtype.val ⁻¹' U : Set ↥(f ⁻¹' Metric.ball z r)) := by
      refine ⟨?_, hUo.preimage continuous_subtype_val⟩
      rw [isClosed_induced_iff]
      refine ⟨closure U, isClosed_closure, ?_⟩
      ext e
      simp only [Set.mem_preimage]
      exact ⟨fun he => hcl e.1 he (hWV e.2), fun he => subset_closure he⟩
    intro z' hz'
    exact (subsingleton_iff_of_equiv (fibre_equiv hWp H' hH' hAcl hzW z' hz')).trans
      (subsingleton_iff_of_equiv (fibre_equiv hWp H' hH' hAcl hzW z hzW)).symm

theorem bijOn_of_isCoveringMapOn_of_fibre {f : ℂ → ℂ} {U V : Set ℂ} (hf : Continuous f) (hcov : IsCoveringMapOn f V) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hVo : IsOpen V) (hVc : IsPreconnected V) (hmap : Set.MapsTo f U V) (hcl : ∀ x ∈ closure U, f x ∈ V → x ∈ U) {v₀ : ℂ} (hv₀ : v₀ ∈ V) (hfib : (U ∩ f ⁻¹' {v₀}).Subsingleton) : Set.BijOn f U V := by
  haveI := Subtype.preconnectedSpace hVc
  have hPN : IsLocallyConstant (fun z : ↥V => (U ∩ f ⁻¹' {z.1}).Nonempty) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro z
    obtain ⟨W, hzW, hWo, hiffN, -⟩ := fibre_local hf hcov hUo hVo hmap hcl z.2
    exact ⟨Subtype.val ⁻¹' W, hWo.preimage continuous_subtype_val, hzW,
      fun z' hz' => propext (hiffN z'.1 hz')⟩
  have hPS : IsLocallyConstant (fun z : ↥V => (U ∩ f ⁻¹' {z.1}).Subsingleton) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro z
    obtain ⟨W, hzW, hWo, -, hiffS⟩ := fibre_local hf hcov hUo hVo hmap hcl z.2
    exact ⟨Subtype.val ⁻¹' W, hWo.preimage continuous_subtype_val, hzW,
      fun z' hz' => propext (hiffS z'.1 hz')⟩
  have hPSv : ∀ z ∈ V, (U ∩ f ⁻¹' {z}).Subsingleton := by
    intro z hz
    have h := hPS.apply_eq_of_preconnectedSpace (⟨z, hz⟩ : ↥V) (⟨v₀, hv₀⟩ : ↥V)
    rw [h]; exact hfib
  have hPNv : ∀ z ∈ V, (U ∩ f ⁻¹' {z}).Nonempty := by
    intro z hz
    obtain ⟨u, huU⟩ := hUne
    have h := hPN.apply_eq_of_preconnectedSpace (⟨f u, hmap huU⟩ : ↥V) (⟨z, hz⟩ : ↥V)
    rw [← h]
    exact ⟨u, huU, by simp⟩
  refine ⟨hmap, ?_, ?_⟩
  · intro x hxU y hyU hxy
    have hs := hPSv (f x) (hmap hxU)
    exact hs ⟨hxU, rfl⟩ ⟨hyU, by rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hxy.symm⟩
  · intro z hz
    obtain ⟨x, hxU, hx⟩ := hPNv z hz
    exact ⟨x, hxU, Set.mem_singleton_iff.mp hx⟩

end Work.ELAssembly
