import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Submission.Work.SSGRoute.PTW.Prelude
import Submission.Work.SSGRoute.PTW.abs_ideleClassGroup_pow_surjective
import Submission.Work.SSGRoute.PTW.archDefs
import Submission.Work.SSGRoute.PTW.compactSpace_ker_abs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The quotient of the idèle class group by its identity component

For a number field `K`, the quotient `C_K ⧸ C_K⁰` of the idèle class group by the connected
component of the identity is a **compact totally disconnected** topological group.

This is the structure theorem for the "component group" of `C_K`: the content
`|·| : C_K →* ℝˣ` restricted to `C_K⁰` is already onto the positive reals, so
`C_K⁰ · ker |·| = C_K` and `C_K ⧸ C_K⁰` is a continuous image of the compact group `ker |·|`
(finiteness of the class group and Dirichlet's unit theorem, `compactSpace_ker_abs`).  Total
disconnectedness is the general fact that a topological group modulo its identity component is
totally disconnected.

The auxiliary lemmas below (`exists_continuous_section_infinitePlace`,
`continuous_mk_archPlaceIdele`, `abs_val_mk_archPlaceIdele_update`,
`exists_connectedComponentOfOne_abs_eq`, `connectedComponent_sup_ker_abs`) build the continuous
archimedean section of the content map: for every positive real `r` the class of an idèle which is
`1` at every finite place and whose only non-trivial archimedean component has norm `r` lies in
`C_K⁰` and has content `r`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField

noncomputable section

namespace Work.SSGRoute.PTW

open NK.GlobalCFT

private theorem exists_continuous_section_infinitePlace (K : Type) [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) :
    ∃ σ : ℝ → (w.Completion)ˣ, Continuous σ ∧ σ 0 = 1 ∧
      ∀ s : ℝ, ‖((σ s : (w.Completion)ˣ) : w.Completion)‖ = Real.exp s := by
  rcases w.isReal_or_isComplex with h | h
  · let e : w.Completion ≃ᵢ ℝ := NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal h
    have he0 : e 0 = 0 := by
      change NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal h 0 = 0
      exact map_zero _
    have he1 : e.symm 1 = 1 := by
      change (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal h).symm 1 = 1
      exact map_one _
    have hne : ∀ s : ℝ, e.symm (Real.exp s) ≠ 0 := by
      intro s h0
      have h1 : e (e.symm (Real.exp s)) = Real.exp s := e.apply_symm_apply _
      rw [h0, he0] at h1
      exact Real.exp_ne_zero s h1.symm
    have hnorm : ∀ x : w.Completion, ‖e x‖ = ‖x‖ := by
      intro x
      change ‖NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal h x‖ = ‖x‖
      exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal h).norm_map_of_map_zero
        (map_zero _) x
    have hval : Continuous (fun s : ℝ => ((Units.mk0 (e.symm (Real.exp s)) (hne s) : (w.Completion)ˣ) : w.Completion)) := by
      simpa only [Units.val_mk0] using (show Continuous (fun s : ℝ => e.symm (Real.exp s)) from by fun_prop)
    refine ⟨fun s => Units.mk0 (e.symm (Real.exp s)) (hne s), ?_, ?_, ?_⟩
    · rw [Units.continuous_iff]
      refine ⟨hval, ?_⟩
      have h2 : Continuous (fun s : ℝ => (e.symm (Real.exp s))⁻¹) :=
        (show Continuous (fun s : ℝ => e.symm (Real.exp s)) from by fun_prop).inv₀ hne
      simpa [Units.val_inv_eq_inv_val, Units.val_mk0] using h2
    · apply Units.ext
      rw [Units.val_mk0, Units.val_one]
      show e.symm (Real.exp 0) = 1
      rw [Real.exp_zero]
      exact he1
    · intro s
      change ‖e.symm (Real.exp s)‖ = Real.exp s
      have h2 := hnorm (e.symm (Real.exp s))
      rw [e.apply_symm_apply] at h2
      rw [← h2, Real.norm_of_nonneg (Real.exp_pos s).le]
  · let e : w.Completion ≃ᵢ ℂ := NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex h
    have he0 : e 0 = 0 := by
      change NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex h 0 = 0
      exact map_zero _
    have he1 : e.symm 1 = 1 := by
      change (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex h).symm 1 = 1
      exact map_one _
    have hne : ∀ s : ℝ, e.symm (((Real.exp s : ℝ)) : ℂ) ≠ 0 := by
      intro s h0
      have h1 : e (e.symm (((Real.exp s : ℝ)) : ℂ)) = (((Real.exp s : ℝ)) : ℂ) := e.apply_symm_apply _
      rw [h0, he0] at h1
      have h2 : ((Real.exp s : ℝ) : ℂ) = 0 := h1.symm
      have h3 : Real.exp s = 0 := by exact_mod_cast h2
      exact Real.exp_ne_zero s h3
    have hnorm : ∀ x : w.Completion, ‖e x‖ = ‖x‖ := by
      intro x
      change ‖NumberField.InfinitePlace.Completion.extensionEmbedding w x‖ = ‖x‖
      exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
        (map_zero _) x
    have hval : Continuous (fun s : ℝ => ((Units.mk0 (e.symm (((Real.exp s : ℝ)) : ℂ)) (hne s) : (w.Completion)ˣ) : w.Completion)) := by
      simpa only [Units.val_mk0] using (show Continuous (fun s : ℝ => e.symm (((Real.exp s : ℝ)) : ℂ)) from by fun_prop)
    refine ⟨fun s => Units.mk0 (e.symm (((Real.exp s : ℝ)) : ℂ)) (hne s), ?_, ?_, ?_⟩
    · rw [Units.continuous_iff]
      refine ⟨hval, ?_⟩
      have h2 : Continuous (fun s : ℝ => (e.symm (((Real.exp s : ℝ)) : ℂ))⁻¹) :=
        (show Continuous (fun s : ℝ => e.symm (((Real.exp s : ℝ)) : ℂ)) from by fun_prop).inv₀ hne
      simpa [Units.val_inv_eq_inv_val, Units.val_mk0] using h2
    · apply Units.ext
      rw [Units.val_mk0, Units.val_one]
      show e.symm (((Real.exp 0 : ℝ)) : ℂ) = 1
      rw [Real.exp_zero, Complex.ofReal_one]
      exact he1
    · intro s
      change ‖e.symm (((Real.exp s : ℝ)) : ℂ)‖ = Real.exp s
      have h2 := hnorm (e.symm (((Real.exp s : ℝ)) : ℂ))
      rw [e.apply_symm_apply] at h2
      rw [← h2, Complex.norm_of_nonneg (Real.exp_pos s).le]

/-- **The archimedean idèle family attached to a continuous family of local units is continuous
after passing to `C_K`.** -/
private theorem continuous_mk_archPlaceIdele (K : Type) [Field K] [NumberField K]
    [DecidableEq (NumberField.InfinitePlace K)]
    (w₀ : NumberField.InfinitePlace K) (f : ℝ → (w₀.Completion)ˣ) (hf : Continuous f) :
    Continuous (fun t : ℝ => NK.GlobalCFT.IdeleClassGroup.mk K
      (archPlaceIdele K (Function.update (fun w : NumberField.InfinitePlace K => (1 : (w.Completion)ˣ)) w₀ (f t)))) := by
  classical
  have hb : Continuous (fun t : ℝ => Function.update
      (fun w : NumberField.InfinitePlace K => (1 : (w.Completion)ˣ)) w₀ (f t)) := by
    rw [continuous_pi_iff]
    intro w
    by_cases hw : w = w₀
    · subst hw
      simpa [Function.update_self] using hf
    · simp only [Function.update_of_ne hw]
      exact continuous_const
  have ha : Continuous (fun t : ℝ => archPlaceVal K (Function.update
      (fun w : NumberField.InfinitePlace K => (1 : (w.Completion)ˣ)) w₀ (f t))) := by
    rw [continuous_pi_iff]
    intro v
    rcases v with w | q
    · have hc : Continuous (fun t : ℝ => (Function.update
          (fun w : NumberField.InfinitePlace K => (1 : (w.Completion)ˣ)) w₀ (f t)) w) :=
        (continuous_apply w).comp hb
      exact hc.subtype_mk _
    · exact continuous_const
  have harch : Continuous (fun t : ℝ => archPlaceIdele K (Function.update
      (fun w : NumberField.InfinitePlace K => (1 : (w.Completion)ˣ)) w₀ (f t))) := by
    change Continuous (fun t : ℝ => RestrictedProduct.structureMap
      (fun v : Place K => (Place.localField K v)ˣ)
      (fun v : Place K => (Place.localUnits K v : Set ((Place.localField K v)ˣ))) Filter.cofinite
      (archPlaceVal K (Function.update
        (fun w : NumberField.InfinitePlace K => (1 : (w.Completion)ˣ)) w₀ (f t))))
    exact (RestrictedProduct.isEmbedding_structureMap
      (R := fun v : Place K => (Place.localField K v)ˣ)
      (A := fun v : Place K => (Place.localUnits K v : Set ((Place.localField K v)ˣ)))
      (𝓕 := Filter.cofinite)).continuous.comp ha
  exact (QuotientGroup.continuous_mk (N := Idele.principalSubgroup K)).comp harch

/-- **The content of `mk` of the archimedean idèle supported at `w₀`.** -/
private theorem abs_val_mk_archPlaceIdele_update (K : Type) [Field K] [NumberField K]
    [DecidableEq (NumberField.InfinitePlace K)]
    (w₀ : NumberField.InfinitePlace K) (x : (w₀.Completion)ˣ) :
    ((NK.GlobalCFT.IdeleClassGroup.abs K (NK.GlobalCFT.IdeleClassGroup.mk K
        (archPlaceIdele K (Function.update (fun w : NumberField.InfinitePlace K => (1 : (w.Completion)ˣ)) w₀ x))) : ℝˣ) : ℝ)
      = ‖((x : (w₀.Completion)ˣ) : w₀.Completion)‖ ^ w₀.mult := by
  classical
  rw [IdeleClassGroup.abs_mk]
  rw [IdeleClassGroup.abs_val_eq_prod_of_localUnits (S := ∅)]
  · rw [Finset.prod_empty, one_mul]
    rw [Finset.prod_eq_single w₀]
    · rw [archPlaceIdele_infinite, Function.update_self]
    · intro w _ hw
      rw [archPlaceIdele_infinite, Function.update_of_ne hw]
      simp
    · intro h; exact absurd (Finset.mem_univ w₀) h
  · intro q _
    rw [archPlaceIdele_finite]
    exact Subgroup.one_mem _

/-- **The content of `C_K` is positive.** -/
private theorem ideleClassGroup_abs_pos (K : Type) [Field K] [NumberField K]
    (x : IdeleClassGroup K) : 0 < ((IdeleClassGroup.abs K x : ℝˣ) : ℝ) := by
  obtain ⟨a, rfl⟩ := IdeleClassGroup.mk_surjective K x
  rw [IdeleClassGroup.abs_mk]
  exact idele_abs_pos K a

/-- **The content restricted to the identity component of `C_K` is onto the positive reals.**  A
positive real is the content of the class of an archimedean idèle (supported at one infinite place)
in the identity component of `C_K`. -/
private theorem exists_connectedComponentOfOne_abs_eq (K : Type) [Field K] [NumberField K]
    (r : ℝˣ) (hr : 0 < (r : ℝ)) :
    ∃ g ∈ Subgroup.connectedComponentOfOne (IdeleClassGroup K), IdeleClassGroup.abs K g = r := by
  classical
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace K))
  obtain ⟨σ, hσc, hσ0, hσn⟩ := exists_continuous_section_infinitePlace K w₀
  set m : ℝ := (w₀.mult : ℝ) with hm
  have hmpos : 0 < m := by rw [hm]; exact_mod_cast NumberField.InfinitePlace.mult_pos (w := w₀)
  let f : ℝ → (w₀.Completion)ˣ := fun t => σ (t / m)
  have hfc : Continuous f := hσc.comp (continuous_id.div_const m)
  let F : ℝ → NK.GlobalCFT.IdeleClassGroup K := fun t => IdeleClassGroup.mk K
      (archPlaceIdele K (Function.update (fun w : NumberField.InfinitePlace K => (1 : (w.Completion)ˣ)) w₀ (f t)))
  have hFc : Continuous F := continuous_mk_archPlaceIdele K w₀ f hfc
  have hF0 : F 0 = 1 := by
    have hf0 : f 0 = 1 := by
      show σ (0 / m) = 1
      rw [zero_div]
      exact hσ0
    have hupd : Function.update (fun w : NumberField.InfinitePlace K => (1 : (w.Completion)ˣ)) w₀ (f 0)
        = (fun w : NumberField.InfinitePlace K => (1 : (w.Completion)ˣ)) := by
      rw [hf0]
      exact Function.update_eq_self w₀ _
    have harch : archPlaceIdele K (fun w : NumberField.InfinitePlace K => (1 : (w.Completion)ˣ))
        = (1 : Idele K) := by
      refine Idele.ext fun v => ?_
      rcases v with w | q
      · rw [archPlaceIdele_infinite, Idele.one_apply]
      · rw [archPlaceIdele_finite, Idele.one_apply]
    show IdeleClassGroup.mk K (archPlaceIdele K (Function.update (fun w : NumberField.InfinitePlace K => (1 : (w.Completion)ˣ)) w₀ (f 0))) = 1
    rw [hupd, harch, map_one]
  have hsub : Set.range F ⊆ (Subgroup.connectedComponentOfOne (IdeleClassGroup K) : Set (IdeleClassGroup K)) := by
    have hpre : IsPreconnected (Set.range F) := isPreconnected_range hFc
    have h := hpre.subset_connectedComponent (x := F 0) ⟨0, rfl⟩
    rw [hF0] at h
    exact h
  refine ⟨F (Real.log (r : ℝ)), hsub ⟨Real.log (r : ℝ), rfl⟩, ?_⟩
  apply Units.ext
  show ((IdeleClassGroup.abs K (IdeleClassGroup.mk K
        (archPlaceIdele K (Function.update (fun w : NumberField.InfinitePlace K => (1 : (w.Completion)ˣ)) w₀ (f (Real.log (r : ℝ)))))) : ℝˣ) : ℝ) = (r : ℝ)
  rw [abs_val_mk_archPlaceIdele_update K w₀ (f (Real.log (r : ℝ)))]
  have hnorm : ‖((f (Real.log (r : ℝ)) : (w₀.Completion)ˣ) : w₀.Completion)‖
      = Real.exp (Real.log (r : ℝ) / m) := by
    show ‖((σ ((Real.log (r : ℝ)) / m) : (w₀.Completion)ˣ) : w₀.Completion)‖ = Real.exp (Real.log (r : ℝ) / m)
    exact hσn _
  rw [hnorm, ← Real.exp_nat_mul (Real.log (r : ℝ) / m) w₀.mult]
  have hmul : (w₀.mult : ℝ) * (Real.log (r : ℝ) / m) = Real.log (r : ℝ) := by
    rw [← hm]; field_simp
  rw [hmul, Real.exp_log hr]

/-- **The identity component and the kernel of the content generate `C_K`.** -/
private theorem connectedComponent_sup_ker_abs_aux (K : Type) [Field K] [NumberField K] :
    Subgroup.connectedComponentOfOne (IdeleClassGroup K) ⊔ (IdeleClassGroup.abs K).ker = ⊤ := by
  classical
  rw [eq_top_iff]
  intro x _
  obtain ⟨g, hg, hgabs⟩ := exists_connectedComponentOfOne_abs_eq K (IdeleClassGroup.abs K x)
    (ideleClassGroup_abs_pos K x)
  have h2 : g⁻¹ * x ∈ (IdeleClassGroup.abs K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgabs, inv_mul_cancel]
  have hmem := Subgroup.mul_mem _ (Subgroup.mem_sup_left hg) (Subgroup.mem_sup_right h2)
  rwa [mul_inv_cancel_left] at hmem

/-- **The quotient of any topological group by its identity component is totally disconnected.** -/
private theorem totallyDisconnectedSpace_quotient_connectedComponentOfOne_aux (G : Type*)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    TotallyDisconnectedSpace (G ⧸ Subgroup.connectedComponentOfOne G) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  set G₀ := Subgroup.connectedComponentOfOne G with hG₀
  set A : Subgroup G := (Subgroup.connectedComponentOfOne (G ⧸ G₀)).comap (QuotientGroup.mk' G₀)
    with hA
  have hpre : IsPreconnected ((QuotientGroup.mk' G₀) '' (G₀ : Set G)) :=
    (isPreconnected_connectedComponent (x := (1 : G))).image
      ((QuotientGroup.mk' G₀) : G → G ⧸ G₀)
      (QuotientGroup.continuous_mk (N := G₀)).continuousOn
  have hmap2 : Subgroup.map (QuotientGroup.mk' G₀) A =
      Subgroup.connectedComponentOfOne (G ⧸ G₀) := by
    rw [hA, Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr
      (QuotientGroup.mk'_surjective G₀)]
    simp
  have hGN : G₀ ≤ A := by
    intro x hx
    have h1 : (1 : G ⧸ G₀) ∈ (QuotientGroup.mk' G₀) '' (G₀ : Set G) :=
      ⟨1, G₀.one_mem, by simp⟩
    exact hpre.subset_connectedComponent h1 ⟨x, hx, rfl⟩
  have hApre : IsPreconnected (A : Set G) := by
    refine isPreconnected_of_isPreconnected_image_mk hGN isPreconnected_connectedComponent ?_
    have hmap : ((QuotientGroup.mk' G₀) '' (A : Set G)) =
        (Subgroup.connectedComponentOfOne (G ⧸ G₀) : Set (G ⧸ G₀)) := by
      rw [← Subgroup.coe_map, hmap2]
    rw [hmap]
    exact isPreconnected_connectedComponent
  have hAle : A ≤ G₀ := hApre.subset_connectedComponent A.one_mem
  have hbot : Subgroup.map (QuotientGroup.mk' G₀) A = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hAle
  have hmem : Subgroup.connectedComponentOfOne (G ⧸ G₀) = ⊥ := by
    rw [← hmap2, hbot]
  have hc := congrArg (fun S : Subgroup (G ⧸ G₀) => (S : Set (G ⧸ G₀))) hmem
  rw [Subgroup.coe_bot] at hc
  exact hc

/-- **The quotient of `C_K` by its identity component is compact**: it is a continuous image of the
compact kernel of the content. -/
private theorem compactSpace_quotient_connectedComponentOfOne (K : Type) [Field K] [NumberField K] :
    CompactSpace (IdeleClassGroup K ⧸ Subgroup.connectedComponentOfOne (IdeleClassGroup K)) := by
  classical
  have hsup := connectedComponent_sup_ker_abs_aux K
  haveI : CompactSpace ↥((IdeleClassGroup.abs K).ker) := compactSpace_ker_abs K
  haveI : IsClosed ((Subgroup.connectedComponentOfOne (IdeleClassGroup K)) :
      Set (IdeleClassGroup K)) := isClosed_connectedComponent
  set N := Subgroup.connectedComponentOfOne (IdeleClassGroup K) with hN
  let φ : ↥((IdeleClassGroup.abs K).ker) → IdeleClassGroup K ⧸ N :=
    fun k => QuotientGroup.mk' N (k : IdeleClassGroup K)
  have hcont : Continuous φ :=
    (QuotientGroup.continuous_mk (N := N)).comp continuous_subtype_val
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective N z
    have hw : w ∈ Subgroup.connectedComponentOfOne (IdeleClassGroup K) ⊔
        (IdeleClassGroup.abs K).ker := by
      rw [hsup]; exact Subgroup.mem_top w
    rcases Subgroup.mem_sup.mp hw with ⟨a, ha, b, hb, hab⟩
    refine ⟨⟨b, hb⟩, ?_⟩
    show QuotientGroup.mk' N b = QuotientGroup.mk' N w
    have ha1 : QuotientGroup.mk' N a = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff a).mpr ha
    rw [← hab, map_mul, ha1, one_mul]
  have hc := isCompact_range hcont
  rw [Set.range_eq_univ.mpr hsurj] at hc
  exact isCompact_univ_iff.mp hc

/-- **The component group of the idèle class group is compact and totally disconnected.** -/
theorem ideleClassGroup_quotient_instances (K : Type) [Field K] [NumberField K] :
    CompactSpace (NK.GlobalCFT.IdeleClassGroup K ⧸ Subgroup.connectedComponentOfOne (NK.GlobalCFT.IdeleClassGroup K)) ∧
      TotallyDisconnectedSpace (NK.GlobalCFT.IdeleClassGroup K ⧸ Subgroup.connectedComponentOfOne (NK.GlobalCFT.IdeleClassGroup K)) := by
  constructor
  · exact compactSpace_quotient_connectedComponentOfOne K
  · exact totallyDisconnectedSpace_quotient_connectedComponentOfOne_aux
      (NK.GlobalCFT.IdeleClassGroup K)

end Work.SSGRoute.PTW
