import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Submission.NK.GlobalCFT.IdeleNorm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFT.IdeleClassGroup

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

/-- **Each local absolute value is continuous.** At an infinite place `localAbs K (ofInfinite w)`
is `x ↦ ‖x‖ ^ w.mult`, and at a finite place it is `x ↦ ‖x‖`.  Since `ℝˣ` carries the subspace
topology from `ℝ` (`IsOpenUnits ℝ`), it suffices that the composite with `Units.val` — the norm,
or a power of it — is continuous. -/
theorem continuous_localAbs {K : Type*} [Field K] [NumberField K] (v : Place K) :
    Continuous (Idele.localAbs K v) := by
  cases v with
  | inl w =>
    refine ((IsOpenUnits.isOpenEmbedding_unitsVal (M := ℝ)).toIsEmbedding.toIsInducing).continuous_iff.mpr ?_
    show Continuous (fun x : w.Completionˣ => ‖(x : w.Completion)‖ ^ w.mult)
    exact (continuous_norm.comp Units.continuous_val).pow w.mult
  | inr q =>
    refine ((IsOpenUnits.isOpenEmbedding_unitsVal (M := ℝ)).toIsEmbedding.toIsInducing).continuous_iff.mpr ?_
    show Continuous (fun x : (q.adicCompletion K)ˣ => ‖(x : q.adicCompletion K)‖)
    exact continuous_norm.comp Units.continuous_val

/-- **The content of an idèle is continuous.**  The restricted product topology is the inductive
limit of the pieces `Πʳ v, [K_vˣ, 𝒪_vˣ]_[𝓟 S]` over cofinite `S`, so by
`RestrictedProduct.continuous_dom` it suffices to prove continuity on each such piece.  On such a
piece `x v` is a local unit for every `v ∈ S`, hence `localAbs K v (x v) = 1` there, and the
remaining places are the finite set `Sᶜ ∪ {archimedean places}`; so the content is a *finite*
product of the continuous functions `x ↦ localAbs K v (x v)`. -/
theorem continuous_abs_aux {K : Type*} [Field K] [NumberField K] :
    Continuous (Idele.abs K) := by
  have h := (RestrictedProduct.continuous_dom
      (R := fun v : Place K => (Place.localField K v)ˣ)
      (A := fun v : Place K => (Place.localUnits K v : Set _))
      (𝓕 := Filter.cofinite)
      (f := ⇑(Idele.abs K)))
  refine h.mpr ?_
  intro S hS
  change Continuous (fun x : Πʳ v : Place K,
      [(Place.localField K v)ˣ, ↑(Place.localUnits K v)]_[Filter.principal S] =>
      ∏ᶠ v, Idele.localAbs K v (x v))
  have hSfin : (Sᶜ : Set (Place K)).Finite :=
    Filter.mem_cofinite.mp (Filter.le_principal_iff.mp hS)
  have hInf : {v : Place K | Place.IsInfinite v}.Finite := by
    have h2 : {v : Place K | Place.IsInfinite v} = Set.range (Place.ofInfinite (K := K)) := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_range]
      rw [Place.isInfinite_iff]
      exact ⟨fun ⟨w, h⟩ => ⟨w, h.symm⟩, fun ⟨w, h⟩ => ⟨w, h.symm⟩⟩
    rw [h2]
    exact Set.finite_range _
  set F : Finset (Place K) := (hSfin.union hInf).toFinset with hF
  have hFcoe : (F : Set (Place K)) = Sᶜ ∪ {v | Place.IsInfinite v} := by
    rw [hF, Set.Finite.coe_toFinset]
  have heq : (fun x : Πʳ v : Place K,
      [(Place.localField K v)ˣ, ↑(Place.localUnits K v)]_[Filter.principal S] =>
      ∏ᶠ v, Idele.localAbs K v (x v))
      = fun x => ∏ v ∈ F, Idele.localAbs K v (x v) := by
    funext x
    rw [finprod_eq_prod_of_mulSupport_subset (fun v => Idele.localAbs K v (x v))]
    intro v hv
    rw [hFcoe]
    by_cases hinf : Place.IsInfinite v
    · exact Or.inr hinf
    · refine Or.inl ?_
      intro hvS
      exfalso
      have hxmem := (Filter.eventually_principal.mp x.2) v hvS
      obtain ⟨q, rfl⟩ := Place.isFinite_iff.mp hinf
      exact hv (Idele.localAbs_ofFinite_eq_one hxmem)
  rw [heq]
  apply continuous_finsetProd
  intro v _
  exact (continuous_localAbs v).comp (RestrictedProduct.continuous_eval v)

/-- **The norm-one idèles form a closed subgroup of the idèle group.** The subgroup
`Idele.normOne K = ker (Idele.abs K)` of idèles of content `1` is the kernel of the content
homomorphism, so it suffices that the content `Idele.abs K : 𝕀 K →* ℝˣ` is continuous, which is
`continuous_abs_aux`. The target `ℝˣ` is `T1`, so `{1}` is closed in it and the preimage is
closed. -/
theorem isClosed_normOne {K : Type*} [Field K] [NumberField K] :
    IsClosed ((NK.GlobalCFT.Idele.normOne K : Subgroup (NK.GlobalCFT.Idele K)) :
      Set (NK.GlobalCFT.Idele K)) := by
  rw [show ((NK.GlobalCFT.Idele.normOne K : Subgroup (NK.GlobalCFT.Idele K)) :
      Set (NK.GlobalCFT.Idele K)) = (⇑(NK.GlobalCFT.Idele.abs K)) ⁻¹' {1} from by
    ext x
    simp [NK.GlobalCFT.Idele.mem_normOne]]
  exact IsClosed.preimage continuous_abs_aux isClosed_singleton

end

end NK.GlobalCFT.IdeleClassGroup
