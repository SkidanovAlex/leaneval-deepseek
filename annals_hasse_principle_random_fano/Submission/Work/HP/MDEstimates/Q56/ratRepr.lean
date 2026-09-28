import Mathlib
import Submission.Work.HP.Q44Setup

set_option autoImplicit false
noncomputable section

open Work.HP

namespace Work.HP.MDEstimates.Q56

/-- Coordinatewise coercion `ℤ^ι → ℚ^ι`, as a `ℤ`-linear map. -/
private def castPi {ι : Type*} : (ι → ℤ) →ₗ[ℤ] (ι → ℚ) where
  toFun v := fun i => (v i : ℚ)
  map_add' v w := by ext i; simp
  map_smul' n v := by ext i; simp

private lemma castPi_injective {ι : Type*} : Function.Injective (castPi (ι := ι)) := by
  intro v w h
  funext i
  have := congrFun h i
  simpa [castPi] using this

/-- Every `u ∈ L` is a `ℚ`-linear combination of any `ℤ`-linearly independent family of
`rk L` elements of a sublattice `L ⊆ ℤ^ι`. -/
lemma exists_ratRepr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) (f : Fin (Work.HP.rk L) → ι → ℤ)
    (hfL : ∀ j, f j ∈ L) (hf : LinearIndependent ℤ f) {u : ι → ℤ} (hu : u ∈ L) :
    ∃ s : Fin (Work.HP.rk L) → ℚ, ∀ i, (u i : ℚ) = ∑ j, s j * (f j i : ℚ) := by
  classical
  -- A `ℤ`-basis `b` of `L`.
  let b : Module.Basis (Fin (Work.HP.rk L)) ℤ L := Module.finBasis ℤ L
  -- The `ℚ`-vectors associated with `f` and with `b`.
  let gQ : Fin (Work.HP.rk L) → (ι → ℚ) := fun j => castPi (f j)
  let cQ : Fin (Work.HP.rk L) → (ι → ℚ) := fun j => castPi (b j : ι → ℤ)
  have hker : (castPi (ι := ι)).ker = ⊥ := LinearMap.ker_eq_bot.mpr castPi_injective
  -- `ℤ`- and `ℚ`-linear independence of the two families.
  have hgQ_Z : LinearIndependent ℤ gQ := by
    have h := hf.map' (castPi (ι := ι)) hker
    simpa [gQ, Function.comp_def] using h
  have hbZ : LinearIndependent ℤ (fun j => (b j : ι → ℤ)) := by
    have h := b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
    simpa [Function.comp_def] using h
  have hcQ_Z : LinearIndependent ℤ cQ := by
    have h := hbZ.map' (castPi (ι := ι)) hker
    simpa [cQ, Function.comp_def] using h
  have hgQ_Q : LinearIndependent ℚ gQ := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hgQ_Z
  have hcQ_Q : LinearIndependent ℚ cQ := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hcQ_Z
  -- both `ℚ`-spans have dimension `rk L`
  have hfing : Module.finrank ℚ (Submodule.span ℚ (Set.range gQ)) = Work.HP.rk L := by
    rw [finrank_span_eq_card hgQ_Q]; simp
  have hfinc : Module.finrank ℚ (Submodule.span ℚ (Set.range cQ)) = Work.HP.rk L := by
    rw [finrank_span_eq_card hcQ_Q]; simp
  -- every element of `L` lies in the `ℚ`-span of the `cQ j`
  have key : ∀ x : L, castPi (x : ι → ℤ) ∈ Submodule.span ℚ (Set.range cQ) := by
    intro x
    have hrepr : ∑ j, (b.repr x) j • (b j : ι → ℤ) = (x : ι → ℤ) := by
      have h := congrArg (Submodule.subtype L) (b.sum_repr x)
      simpa only [map_sum, map_smul, Submodule.coe_subtype] using h
    rw [← hrepr, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul]
    rw [show castPi ((b j : ι → ℤ)) = cQ j from rfl,
        ← Int.cast_smul_eq_zsmul ℚ ((b.repr x) j) (cQ j)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
  have hle : Submodule.span ℚ (Set.range gQ) ≤ Submodule.span ℚ (Set.range cQ) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact key ⟨f j, hfL j⟩
  have heq : Submodule.span ℚ (Set.range gQ) = Submodule.span ℚ (Set.range cQ) :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hfing, hfinc])
  -- hence `u` is a `ℚ`-combination of the `gQ j`
  have humem : castPi u ∈ Submodule.span ℚ (Set.range gQ) := by
    rw [heq]; exact key ⟨u, hu⟩
  obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp humem
  -- read off the coefficients coordinatewise
  refine ⟨s, fun i => ?_⟩
  have := congrFun hs i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, castPi] at this
  exact this.symm

/-- Every vector `u` of a rank-`3` sublattice `L ⊆ ℤ^5` lies in the `ℚ`-span of any
`ℤ`-linearly independent triple `v` of elements of `L`. -/
lemma ratRepr {L : Submodule ℤ (Fin 5 → ℤ)} (hL : Work.HP.rk L = 3)
    {v : Fin 3 → (Fin 5 → ℤ)} (hv : LinearIndependent ℤ v) (hvL : ∀ j, v j ∈ L)
    {u : Fin 5 → ℤ} (hu : u ∈ L) :
    ∃ s : Fin 3 → ℚ, ∀ i : Fin 5, (u i : ℚ) = ∑ j : Fin 3, s j * (v j i : ℚ) := by
  classical
  -- reindex `v` to the index type `Fin (rk L)` of the basis of `L`
  set e : Fin (Work.HP.rk L) ≃ Fin 3 := finCongr hL with he
  have hf : LinearIndependent ℤ (fun k : Fin (Work.HP.rk L) => v (e k)) :=
    hv.comp e e.injective
  have hfL : ∀ k, v (e k) ∈ L := fun k => hvL (e k)
  obtain ⟨s, hs⟩ := exists_ratRepr L (fun k => v (e k)) hfL hf hu
  refine ⟨fun j => s (e.symm j), fun i => ?_⟩
  have hs' := hs i
  rw [hs']
  refine (Fintype.sum_equiv e.symm
    (fun j : Fin 3 => s (e.symm j) * (v j i : ℚ))
    (fun k : Fin (Work.HP.rk L) => s k * (v (e k) i : ℚ)) ?_).symm
  intro j
  simp only [Equiv.apply_symm_apply]

end Work.HP.MDEstimates.Q56
