import Mathlib
import Submission.Work.SSGRoute.GrunwaldEscapeCore.TopologySetup
import Submission.NK.UchidaKummer.Approximation.isOpenEllPowSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain
open scoped NumberField RestrictedProduct

noncomputable section

namespace Work.SSGRoute.GrunwaldEscapeCore

open NK.GlobalCFT

variable {K : Type} [Field K] [NumberField K]

/-! ## Two elementary topological inputs -/

/-- A finite intersection of open sets, in "for all" form. -/
theorem isOpen_forall_mem_finset {X : Type*} [TopologicalSpace X] {α : Type*}
    (s : Finset α) (f : α → Set X) (h : ∀ i ∈ s, IsOpen (f i)) :
    IsOpen {x : X | ∀ i ∈ s, x ∈ f i} := by
  rw [show {x : X | ∀ i ∈ s, x ∈ f i} = ⋂ i ∈ s, f i from by ext x; simp]
  exact isOpen_biInter_finset h

/-- **The local congruence ball is open.**  `{u : K_qˣ | IsCongAt K m q u}` is the preimage under
the continuous map `u ↦ u - 1` of the open ball `{z | v z ≤ exp (-m q)}` of the valued field
`K_q` (a closed ball of the `q`-adic topology, which is open because the value group is discrete,
`NK.UchidaKummer.Approximation.isOpen_val_le_exp_neg`). -/
theorem isOpen_isCongAt_set (m : HeightOneSpectrum (RingOfIntegers K) → ℕ)
    (q : HeightOneSpectrum (RingOfIntegers K)) :
    IsOpen {u : (q.adicCompletion K)ˣ | NK.NUV2.RouteB.IsCongAt K m q u} := by
  have h : IsOpen {z : q.adicCompletion K |
      Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) z
        ≤ WithZero.exp (-(m q : ℤ))} :=
    NK.UchidaKummer.Approximation.isOpen_val_le_exp_neg (K := K) q (m q)
  have hcont : Continuous fun u : (q.adicCompletion K)ˣ =>
      (((u : (q.adicCompletion K)ˣ) : q.adicCompletion K) - 1) :=
    Units.continuous_val.sub continuous_const
  unfold NK.NUV2.RouteB.IsCongAt
  exact h.preimage hcont

/-! ## The congruence subgroup is open -/

/-- The congruence subgroup `U(𝔪) ≤ 𝕀 K` of a modulus is **open** in the idèle group.

`U(𝔪)` is the subgroup of idèles which are local units at every finite place, congruent to `1`
modulo `𝔪 q` at the primes `q` of the support, and positive at the real places in `𝔪.pos`.  Its
non-trivial conditions are imposed at the finitely many places of `supportFinset ∪ 𝔪.pos` (the
finite places are finitely many, and so are the infinite places, by `NumberField`), so it
contains a basic neighbourhood of `1` of the restricted-product topology; as a subgroup, it is
therefore open (`Subgroup.isOpen_of_mem_nhds`).

The neighbourhood basis of the restricted product is the one used in
`Submission/NK/NUV2/RouteB/RayModulus/exists_modulus_le.lean`
(`RestrictedProduct.nhds_eq_map_structureMap`, `nhds_pi`, `Filter.mem_pi'`); the only local inputs
are that `{y : (q.adicCompletion K)ˣ // Valued.v ↑y - 1 < exp (-(n : ℤ))}` is an open neighbourhood
of `1` at a finite place, and that the positive reals are an open neighbourhood of `1` in
`(w.Completion)ˣ ≃ ℝˣ` at a real place (`isometryEquivRealOfIsReal`). -/
theorem isOpen_congSubgroup {K : Type} [Field K] [NumberField K]
    (𝔪 : NK.NUV2.RouteB.Modulus K) :
    IsOpen (NK.NUV2.RouteB.CongSubgroup K 𝔪 : Set (NK.GlobalCFT.Idele K)) := by
  classical
  -- ### The first open piece: local units at every finite place
  have h1 : IsOpen {x : Idele K |
      ∀ v : Place K, v ∉ {v : Place K | v.IsInfinite} → x v ∈ Place.localUnits K v} := by
    exact RestrictedProduct.isOpen_forall_imp_mem
      (ι := Place K)
      (R := fun v : Place K => (Place.localField K v)ˣ)
      (A := fun v : Place K => (Place.localUnits K v : Set _))
      (p := fun v : Place K => v ∉ {v : Place K | v.IsInfinite})
      (fun v => Place.isOpen_localUnits v)
  -- ### The second open piece: the congruence balls at the support of `𝔪`
  have h2 : IsOpen {x : Idele K | ∀ q ∈ 𝔪.supportFinset,
      NK.NUV2.RouteB.IsCongAt K 𝔪.exps q (x (Place.ofFinite q))} :=
    isOpen_forall_mem_finset 𝔪.supportFinset
      (fun q => {x : Idele K | NK.NUV2.RouteB.IsCongAt K 𝔪.exps q (x (Place.ofFinite q))})
      (fun q _ => (isOpen_isCongAt_set (K := K) 𝔪.exps q).preimage
        (f := fun x : Idele K => x (Place.ofFinite q))
        (RestrictedProduct.continuous_eval (Place.ofFinite q)))
  -- ### The third open piece: positivity at the real places of `𝔪.pos`
  let f : InfinitePlace K → Set (Idele K) := fun w =>
    if h : w.IsReal then
      {x : Idele K | 0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal h)
        ((x (Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion)}
    else ⊤
  let s : Finset (InfinitePlace K) := Finset.univ.filter (fun w => w.IsReal ∧ w ∈ 𝔪.pos)
  have hfopen : ∀ w ∈ s, IsOpen (f w) := by
    intro w _
    by_cases h : w.IsReal
    · rw [show f w = {x : Idele K |
          0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal h)
            ((x (Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion)} from dif_pos h]
      have hcont : Continuous fun x : Idele K =>
          (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal h)
            ((x (Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion) :=
        (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal h).continuous.comp
          (Units.continuous_val.comp (RestrictedProduct.continuous_eval (Place.ofInfinite w)))
      exact isOpen_Ioi.preimage hcont
    · rw [show f w = ⊤ from dif_neg h]
      exact isOpen_univ
  have h3 : IsOpen {x : Idele K | ∀ w ∈ s, x ∈ f w} := by
    rw [show {x : Idele K | ∀ w ∈ s, x ∈ f w} = ⋂ w ∈ s, f w from by ext x; simp]
    exact isOpen_biInter_finset hfopen
  -- ### The intersection of the three pieces is contained in `U(𝔪)`
  have hsub : ({x : Idele K | ∀ v : Place K, v ∉ {v : Place K | v.IsInfinite} →
        x v ∈ Place.localUnits K v} ∩
      ({x : Idele K | ∀ q ∈ 𝔪.supportFinset,
        NK.NUV2.RouteB.IsCongAt K 𝔪.exps q (x (Place.ofFinite q))} ∩
       {x : Idele K | ∀ w ∈ s, x ∈ f w})) ⊆
      ((NK.NUV2.RouteB.CongSubgroup K 𝔪 : Subgroup (Idele K)) : Set (Idele K)) := by
    rintro x ⟨hx1, hx2, hx3⟩
    change x ∈ NK.NUV2.RouteB.CongSubgroup K 𝔪
    rw [NK.NUV2.RouteB.Modulus.mem_congSubgroup_iff]
    refine ⟨fun q => ⟨?_, ?_⟩, ?_⟩
    · have h := hx1 (Place.ofFinite q) (by simp)
      rwa [Place.mem_localUnits_ofFinite_iff_valued_eq_one] at h
    · by_cases hq : q ∈ 𝔪.supportFinset
      · exact hx2 q hq
      · -- at a prime outside the support the congruence condition is automatic
        have h0 := 𝔪.exps_eq_zero_of_not_mem hq
        have hu : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            (((x (Place.ofFinite q) : (q.adicCompletion K)ˣ) : q.adicCompletion K)) = 1 := by
          have h := hx1 (Place.ofFinite q) (by simp)
          rwa [Place.mem_localUnits_ofFinite_iff_valued_eq_one] at h
        rw [NK.NUV2.RouteB.IsCongAt, h0]
        refine le_trans (Valuation.map_sub _ _ _) (le_of_eq ?_)
        rw [hu, Valuation.map_one, max_self]
        exact WithZero.exp_zero.symm
    · intro w hw hpos
      have hws : w ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw, hpos⟩
      have hxw := hx3 w hws
      rw [show f w = {x : Idele K |
          0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            ((x (Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion)} from dif_pos hw] at hxw
      exact hxw
  -- ### `1` lies in the intersection, hence `U(𝔪)` is a neighbourhood of `1`
  have hone : (1 : Idele K) ∈ ({x : Idele K | ∀ v : Place K, v ∉ {v : Place K | v.IsInfinite} →
        x v ∈ Place.localUnits K v} ∩
      ({x : Idele K | ∀ q ∈ 𝔪.supportFinset,
        NK.NUV2.RouteB.IsCongAt K 𝔪.exps q (x (Place.ofFinite q))} ∩
       {x : Idele K | ∀ w ∈ s, x ∈ f w})) := by
    refine ⟨?_, ?_, ?_⟩
    · intro v _
      rcases v with w | q
      · exact Place.mem_localUnits_ofInfinite
      · rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one]
        simp
    · intro q _
      rw [NK.NUV2.RouteB.IsCongAt]
      simp
    · intro w hw
      obtain ⟨-, hwr, -⟩ := Finset.mem_filter.mp hw
      rw [show f w = {x : Idele K |
          0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hwr)
            ((x (Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion)} from dif_pos hwr]
      simp
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset
    ((h1.inter (h2.inter h3)).mem_nhds hone) hsub)

end Work.SSGRoute.GrunwaldEscapeCore
