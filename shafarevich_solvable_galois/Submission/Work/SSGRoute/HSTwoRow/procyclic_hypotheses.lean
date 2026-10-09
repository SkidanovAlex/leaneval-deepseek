import Mathlib
import Submission.Work.SSGRoute.H2locAux.Defs
import Submission.Work.SSGRoute.isCoboundary2On_top_of_procyclicGrowth
import Submission.Work.SSGRoute.map_topologicalClosure_zpowers_subtype
import Submission.Work.SSGRoute.PT.Cgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The procyclic hypotheses for `C = closure (zpowers σ)`

`Work.SSGRoute.isCoboundary2On_top_of_procyclicGrowth` needs, for `Γ = C = closure (zpowers σ)`,
that every normal finite-index subgroup of `C` has cyclic quotient and that every open normal
`U ≤ C` contains an open normal `V` with `p ∣ [U : V]`.  Both follow from the hypothesis `hZ`
("`C` has a surjection onto `ZMod n` for every `n > 0`"), via the structural fact
`exists_pow_mul_pow_zpowersClosure`: every element of `C` is `σ^j * y^n` with `j < n`.
-/

open scoped Pointwise

namespace Work.SSGRoute.HSTwoRow

noncomputable section

/-- **Key fact.**  For `C = closure (zpowers σ)` and `n > 0`, every element of `↥C` is
`σ^j * y^n` with `j < n`.  Proof: the set `S = ⋃_{j<n} σ^j • (n-th powers)` is closed (a finite
union of images of the compact set of `n`-th powers) and contains the cyclic subgroup generated
by `σ` (write an arbitrary integer exponent as `j + n * q`), hence contains
`closure (zpowers σ) = ↥C`. -/
lemma exists_pow_mul_pow_zpowersClosure
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (σ : Ω ≃ₐ[k] Ω) :
    ∀ (n : ℕ), 0 < n → ∀ x : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)),
      ∃ j : ℕ, j < n ∧ ∃ y : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)),
        x = (⟨σ, Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers σ)⟩ :
              ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) ^ j * y ^ n := by
  intro n hn
  haveI : CompactSpace (Ω ≃ₐ[k] Ω) := inferInstance
  haveI : T2Space (Ω ≃ₐ[k] Ω) := krullTopology_t2 (K := k) (L := Ω)
  set C : Subgroup (Ω ≃ₐ[k] Ω) := Subgroup.topologicalClosure (Subgroup.zpowers σ) with hCdef
  have hσC : σ ∈ C := by
    rw [hCdef]; exact Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers σ)
  have hCclosed : IsClosed (C : Set (Ω ≃ₐ[k] Ω)) := by
    rw [hCdef]; exact Subgroup.isClosed_topologicalClosure _
  haveI : CompactSpace ↥C := isCompact_iff_compactSpace.mp hCclosed.isCompact
  set s : ↥C := ⟨σ, hσC⟩ with hsdef
  set S : Set ↥C := ⋃ j ∈ Finset.range n,
      (fun z : ↥C => s ^ j * z) '' (Set.range (fun y : ↥C => y ^ n)) with hSdef
  have hSclosed : IsClosed S := by
    rw [hSdef]
    refine isClosed_biUnion_finset fun j _ => ?_
    exact ((isCompact_range (continuous_id.pow n)).image
      (continuous_const.mul continuous_id)).isClosed
  have hle : (Subgroup.zpowers s : Set ↥C) ⊆ S := by
    intro z hz
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hmn : m % (n : ℤ) + (n : ℤ) * (m / (n : ℤ)) = m := Int.emod_add_mul_ediv m n
    have hj0 : 0 ≤ m % (n : ℤ) := Int.emod_nonneg m (by exact_mod_cast hn.ne')
    have hjn : m % (n : ℤ) < (n : ℤ) := Int.emod_lt_of_pos m (by exact_mod_cast hn)
    set j : ℕ := (m % (n : ℤ)).toNat with hjdef
    have hjc : (j : ℤ) = m % (n : ℤ) := by
      rw [hjdef]; exact Int.toNat_of_nonneg hj0
    have hjlt : j < n := by
      have : (j : ℤ) < (n : ℤ) := by rw [hjc]; exact hjn
      exact_mod_cast this
    have hsp : s ^ m = s ^ j * (s ^ (m / (n : ℤ))) ^ n := by
      conv_lhs => rw [← hmn]
      rw [zpow_add, mul_comm (n : ℤ) (m / (n : ℤ)), zpow_mul, ← hjc, zpow_natCast,
        zpow_natCast]
    rw [hsp]
    refine Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hjlt, ?_⟩⟩
    exact ⟨(s ^ (m / (n : ℤ))) ^ n, ⟨s ^ (m / (n : ℤ)), rfl⟩, rfl⟩
  have htop : Subgroup.topologicalClosure (Subgroup.zpowers s) = ⊤ := by
    have hmap := Work.SSGRoute.map_topologicalClosure_zpowers_subtype C hCclosed σ hσC
    have h2 : (Subgroup.topologicalClosure (Subgroup.zpowers s)).map C.subtype = C := by
      simpa [hCdef, hsdef] using hmap
    refine eq_top_iff.mpr fun y _ => ?_
    have hy : (y : Ω ≃ₐ[k] Ω) ∈ (Subgroup.topologicalClosure (Subgroup.zpowers s)).map
        C.subtype := by rw [h2]; exact y.2
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    have hzy' : z = y := Subtype.ext hzy
    rwa [hzy'] at hz
  -- now the element
  intro x
  have hxcl : x ∈ closure ((Subgroup.zpowers s : Set ↥C)) := by
    change x ∈ Subgroup.topologicalClosure (Subgroup.zpowers s)
    rw [htop]; trivial
  have hxS : x ∈ S := hSclosed.closure_subset_iff.mpr hle hxcl
  rw [hSdef] at hxS
  obtain ⟨j, hxS⟩ := Set.mem_iUnion.mp hxS
  obtain ⟨hj, hxS⟩ := Set.mem_iUnion.mp hxS
  obtain ⟨y, hy, hyx⟩ := hxS
  obtain ⟨y', hy'⟩ := hy
  exact ⟨j, Finset.mem_range.mp hj, y', by rw [← hyx, show y' ^ n = y from hy']⟩

/-- **`C = closure (zpowers σ)` is procyclic.**  Every normal finite-index subgroup `N ≤ ↥C` has
cyclic quotient: by `exists_pow_mul_pow_zpowersClosure` every element of `↥C` is `σ^j * y^n` with
`n = N.index`, and `y^n ∈ N`, so the quotient is generated by the image of `σ`. -/
lemma isProCyclicGrp_zpowersClosure
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (σ : Ω ≃ₐ[k] Ω) :
    Work.SSGRoute.IsProCyclicGrp ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) := by
  intro N hNnorm hNfin
  haveI := hNnorm
  haveI hNfin' : N.FiniteIndex := hNfin
  haveI : Fintype (↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) ⧸ N) :=
    Fintype.ofFinite _
  have hpos : 0 < N.index := Nat.pos_of_ne_zero hNfin.index_ne_zero
  set s : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) :=
    ⟨σ, Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers σ)⟩ with hsdef
  refine (isCyclic_iff_exists_zpowers_eq_top).mpr ⟨QuotientGroup.mk' N s, ?_⟩
  rw [eq_top_iff]
  rintro y -
  induction y using QuotientGroup.induction_on with
  | H x =>
    show QuotientGroup.mk' N x ∈ Subgroup.zpowers (QuotientGroup.mk' N s)
    obtain ⟨j, hj, y', hy⟩ := exists_pow_mul_pow_zpowersClosure k Ω σ N.index hpos x
    rw [hy, map_mul, map_pow, map_pow]
    have hyN : (QuotientGroup.mk' N y') ^ N.index = 1 := by
      rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
      exact pow_card_eq_one
    rw [hyN, mul_one]
    exact Subgroup.mem_zpowers_iff.mpr ⟨(j : ℤ), by rw [zpow_natCast]⟩

/-- **The procyclic hypotheses for `C = closure (zpowers σ)`.** -/
theorem procyclic_hypotheses
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (σ : Ω ≃ₐ[k] Ω)
    (hZ : ∀ n : ℕ, 0 < n → ∃ f : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) →*
        Multiplicative (ZMod n), Function.Surjective f) :
    Work.SSGRoute.IsProCyclicGrp ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) ∧
    (∀ (U : Subgroup ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))),
        IsOpen (U : Set ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) → U.Normal →
        ∃ V : Subgroup ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)),
          V ≤ U ∧ IsOpen (V : Set ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) ∧
            V.Normal ∧ p ∣ (V.subgroupOf U).index) := by
  exact ⟨isProCyclicGrp_zpowersClosure k Ω σ, PT.hbig_zpowersClosure k Ω p σ hZ⟩

end

end Work.SSGRoute.HSTwoRow
