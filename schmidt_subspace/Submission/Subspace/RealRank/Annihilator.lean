import Mathlib
import Submission.Subspace.RealRank.Exterior
import Submission.Commons.LinearAlgebra.Plucker.eq_span_of_minors_proportional

/-!
# The annihilator identity: a hyperplane determines its `W`

For `r + k = N`, a family `u : Fin N → (Fin N → K)` (thought of as a basis of `K^N`) and a
`k`-element index set `t` with complement `Tstar` (`|Tstar| = r`), the wedge

`ω := ⋀_{i ∈ t} u i ∈ ⋀^k K^N`

has annihilator `{Y ∈ ⋀^r : Y ∧ ω = 0} = span {⋀_{i ∈ S} u i : S ≠ Tstar}` — a hyperplane of
`⋀^r`.  Consequently the *span of the `t`-indexed members of the family* is determined by that
hyperplane:

`span {u i : i ∈ t}` is a function of `ker (wedgePair · ω)`.

This is the "annihilator identity" of the rank descent: the hyperplane `V(Π_k(Q))` (which
`maximal_rank_finiteness` shows takes only finitely many values) determines the descended
subspace `W_k(Q)` (the span of the first `k` successive minima).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators exteriorPower
open ExteriorAlgebra

namespace Submission.Subspace.RealRank

variable {K : Type*} [Field K] {N r k : ℕ}

/-- **Two nonzero linear functionals with the same kernel are proportional.** -/
lemma exists_smul_of_ker_eq {V : Type*} [AddCommGroup V] [Module K V]
    (f g : V →ₗ[K] K) (hf : f ≠ 0) (h : LinearMap.ker f = LinearMap.ker g) :
    ∃ c : K, c ≠ 0 ∧ g = c • f := by
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hf (LinearMap.ext hcon)
  have hv' : v ∉ LinearMap.ker f := fun hmem => hv (LinearMap.mem_ker.mp hmem)
  have hgv : g v ≠ 0 := fun hzero => hv' (by rw [h]; exact LinearMap.mem_ker.mpr hzero)
  refine ⟨g v / f v, div_ne_zero hgv hv, ?_⟩
  ext u
  have hker : u - (f u / f v) • v ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hv, sub_self]
  have hker' : u - (f u / f v) • v ∈ LinearMap.ker g := by rw [← h]; exact hker
  rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul] at hker'
  have hgu : g u = (f u / f v) * g v := sub_eq_zero.mp hker'
  simp only [LinearMap.smul_apply, smul_eq_mul, hgu]
  field_simp

/-- The wedge of the `t`-indexed members of a family is `ιMulti` of the order-embedded
family. -/
lemma iMulti_family_eq_iMulti_comp (u : Fin N → Fin N → K)
    (t : Set.powersetCard (Fin N) k) :
    exteriorPower.ιMulti_family K k u t
      = exteriorPower.ιMulti K k (u ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm t)) := rfl

/-- The range of the order embedding attached to `t` is `t` itself. -/
lemma range_ofFinEmbEquiv_symm (t : Set.powersetCard (Fin N) k) :
    Set.range (⇑(Set.powersetCard.ofFinEmbEquiv.symm t) : Fin k → Fin N)
      = (↑t : Set (Fin N)) := by
  ext i
  rw [Set.mem_range]
  exact Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t i

/-- **The annihilator of `⋀_{i ∈ t} u i` is the span of the complementary wedges.** -/
theorem ker_wedgePairLinLeft_eq_span (hrk : r + k = N)
    (u : Fin N → (Fin N → K)) (hu : LinearIndependent K u)
    (Tstar : Set.powersetCard (Fin N) r) (t : Set.powersetCard (Fin N) k)
    (ht : (↑t : Finset (Fin N)) = (↑Tstar)ᶜ) :
    LinearMap.ker (wedgePairLinLeft hrk (exteriorPower.ιMulti_family K k u t)) =
      Submodule.span K (Set.range (fun S : {S : Set.powersetCard (Fin N) r // S ≠ Tstar} =>
        exteriorPower.ιMulti_family K r u (S : Set.powersetCard (Fin N) r))) := by
  classical
  have hmemt : ∀ i : Fin N, i ∈ (↑t : Finset (Fin N)) ↔ i ∉ (↑Tstar : Finset (Fin N)) := by
    intro i; rw [ht]; exact Finset.mem_compl
  have hdisj : Disjoint (Tstar : Finset (Fin N)) (t : Finset (Fin N)) := by
    rw [Finset.disjoint_left]
    intro a ha hat
    exact ((hmemt a).mp hat) ha
  have huni : (Tstar : Finset (Fin N)) ∪ (t : Finset (Fin N)) = Finset.univ := by
    ext a
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases h : a ∈ (Tstar : Finset (Fin N))
    · exact Or.inl h
    · exact Or.inr ((hmemt a).mpr h)
  -- a basis whose underlying family is `u`
  have hspanu : ⊤ ≤ Submodule.span K (Set.range u) := by
    rw [top_le_iff]
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [finrank_span_eq_card hu, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  set b : Module.Basis (Fin N) K (Fin N → K) := Module.Basis.mk hu hspanu with hbdef
  have hbu : ⇑b = u := by rw [hbdef]; exact Module.Basis.coe_mk hu hspanu
  have hB : ∀ S : Set.powersetCard (Fin N) r,
      b.exteriorPower r S = exteriorPower.ιMulti_family K r u S := by
    intro S
    rw [exteriorPower.basis_apply, hbu]
  have hdiag : wedgePair hrk (exteriorPower.ιMulti_family K r u Tstar)
      (exteriorPower.ιMulti_family K k u t) ≠ 0 := by
    rw [wedgePair_iMulti_family_eq_smul_of_disjoint hrk u Tstar t hdisj huni]
    exact mul_ne_zero
      (((Set.powersetCard.permOfDisjoint hdisj).sign.isUnit).map (Int.castRingHom K)).ne_zero
      (topCoeff_iMulti_family_ne_zero u hu)
  have hoff : ∀ S : Set.powersetCard (Fin N) r, S ≠ Tstar →
      wedgePair hrk (exteriorPower.ιMulti_family K r u S)
        (exteriorPower.ιMulti_family K k u t) = 0 := by
    intro S hS
    refine wedgePair_iMulti_family_eq_zero_of_not_disjoint hrk u S t ?_
    intro hdj
    have hsub : (↑S : Finset (Fin N)) ⊆ (↑Tstar : Finset (Fin N)) := by
      intro a ha
      by_contra hcon
      exact (Finset.disjoint_left.mp hdj ha) ((hmemt a).mpr hcon)
    exact hS (Subtype.ext (Finset.eq_of_subset_of_card_le hsub
      (by rw [Set.powersetCard.card_eq, Set.powersetCard.card_eq])))
  refine le_antisymm ?_ ?_
  · -- every element of the kernel misses the `Tstar` coordinate
    intro Y hY
    rw [LinearMap.mem_ker, wedgePairLinLeft_apply] at hY
    have hsum : wedgePair hrk Y (exteriorPower.ιMulti_family K k u t) =
        ∑ S : Set.powersetCard (Fin N) r, (b.exteriorPower r).repr Y S *
          wedgePair hrk (b.exteriorPower r S) (exteriorPower.ιMulti_family K k u t) := by
      have hY' : Y = ∑ S : Set.powersetCard (Fin N) r,
          (b.exteriorPower r).repr Y S • b.exteriorPower r S :=
        (Module.Basis.sum_repr (b.exteriorPower r) Y).symm
      conv_lhs => rw [hY']
      rw [← wedgePairLinLeft_apply, map_sum]
      exact Finset.sum_congr rfl fun S _ => by
        rw [map_smul, smul_eq_mul, wedgePairLinLeft_apply]
    have hzero : (b.exteriorPower r).repr Y Tstar = 0 := by
      have h1 : (∑ S : Set.powersetCard (Fin N) r, (b.exteriorPower r).repr Y S *
          wedgePair hrk (b.exteriorPower r S) (exteriorPower.ιMulti_family K k u t)) = 0 := by
        rw [← hsum, hY]
      rw [Finset.sum_eq_single Tstar] at h1
      · rcases mul_eq_zero.mp h1 with h | h
        · exact h
        · rw [hB Tstar] at h; exact absurd h hdiag
      · intro S _ hS
        rw [hB S, hoff S hS, mul_zero]
      · intro hT
        exact absurd (Finset.mem_univ Tstar) hT
    have hY' : Y = ∑ S : Set.powersetCard (Fin N) r,
        (b.exteriorPower r).repr Y S • b.exteriorPower r S :=
      (Module.Basis.sum_repr (b.exteriorPower r) Y).symm
    rw [hY']
    refine Submodule.sum_mem _ fun S _ => ?_
    by_cases hS : S = Tstar
    · rw [hS, hzero, zero_smul]
      exact Submodule.zero_mem _
    · rw [hB S]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨S, hS⟩, rfl⟩)
  · rw [Submodule.span_le]
    rintro v ⟨S, rfl⟩
    show wedgePairLinLeft hrk (exteriorPower.ιMulti_family K k u t)
      (exteriorPower.ιMulti_family K r u (S : Set.powersetCard (Fin N) r)) = 0
    rw [wedgePairLinLeft_apply]
    exact hoff (S : Set.powersetCard (Fin N) r) S.2

/-- **The hyperplane determines the span of the `t`-indexed family.** -/
theorem span_image_eq_of_ker_eq (hrk : r + k = N)
    (u u' : Fin N → (Fin N → K)) (hu : LinearIndependent K u) (hu' : LinearIndependent K u')
    (Tstar : Set.powersetCard (Fin N) r) (t : Set.powersetCard (Fin N) k)
    (ht : (↑t : Finset (Fin N)) = (↑Tstar)ᶜ)
    (h : LinearMap.ker (wedgePairLinLeft hrk (exteriorPower.ιMulti_family K k u t))
        = LinearMap.ker (wedgePairLinLeft hrk (exteriorPower.ιMulti_family K k u' t))) :
    Submodule.span K (u '' (↑t : Set (Fin N))) = Submodule.span K (u' '' (↑t : Set (Fin N))) := by
  classical
  have hmemt : ∀ i : Fin N, i ∈ (↑t : Finset (Fin N)) ↔ i ∉ (↑Tstar : Finset (Fin N)) := by
    intro i; rw [ht]; exact Finset.mem_compl
  have hdisj : Disjoint (Tstar : Finset (Fin N)) (t : Finset (Fin N)) := by
    rw [Finset.disjoint_left]
    intro a ha hat
    exact ((hmemt a).mp hat) ha
  have huni : (Tstar : Finset (Fin N)) ∪ (t : Finset (Fin N)) = Finset.univ := by
    ext a
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases h : a ∈ (Tstar : Finset (Fin N))
    · exact Or.inl h
    · exact Or.inr ((hmemt a).mpr h)
  have hne : wedgePairLinLeft hrk (exteriorPower.ιMulti_family K k u t) ≠ 0 := by
    intro hzero
    have hval : wedgePair hrk (exteriorPower.ιMulti_family K r u Tstar)
        (exteriorPower.ιMulti_family K k u t) = 0 := by
      rw [← wedgePairLinLeft_apply]
      exact congrFun (congrArg DFunLike.coe hzero) _
    rw [wedgePair_iMulti_family_eq_smul_of_disjoint hrk u Tstar t hdisj huni] at hval
    exact (mul_ne_zero
      (((Set.powersetCard.permOfDisjoint hdisj).sign.isUnit).map (Int.castRingHom K)).ne_zero
      (topCoeff_iMulti_family_ne_zero u hu)) hval
  obtain ⟨c, hc, hcprop⟩ := exists_smul_of_ker_eq
    (wedgePairLinLeft hrk (exteriorPower.ιMulti_family K k u t))
    (wedgePairLinLeft hrk (exteriorPower.ιMulti_family K k u' t)) hne h
  have homega : exteriorPower.ιMulti_family K k u' t
      = c • exteriorPower.ιMulti_family K k u t := by
    refine sub_eq_zero.mp (wedgePair_right_nondegenerate (K := K) (N := N) (r := r) (k := k)
      hrk _ fun Y => ?_)
    have hlin : ∀ ω : ⋀[K]^k (Fin N → K),
        wedgePairLinRight hrk Y ω = wedgePairLinLeft hrk ω Y := fun ω => by
      rw [wedgePairLinRight_apply]; rfl
    rw [← wedgePairLinRight_apply, map_sub, map_smul, smul_eq_mul, hlin, hlin, hcprop,
      LinearMap.smul_apply, smul_eq_mul]
    ring
  have homega' : exteriorPower.ιMulti K k (u' ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm t))
      = c • exteriorPower.ιMulti K k (u ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm t)) := by
    rw [← iMulti_family_eq_iMulti_comp u' t, ← iMulti_family_eq_iMulti_comp u t, homega]
  set e := Set.powersetCard.ofFinEmbEquiv.symm t with he
  have homega'' : ExteriorAlgebra.ιMulti K k (u' ∘ ⇑e)
      = c • ExteriorAlgebra.ιMulti K k (u ∘ ⇑e) := by
    have h := congrArg (fun z : ⋀[K]^k (Fin N → K) => (z : ExteriorAlgebra K (Fin N → K))) homega'
    simpa only [exteriorPower.ιMulti_apply_coe, Submodule.coe_smul] using h
  have hu'e : LinearIndependent K (u' ∘ ⇑e) := hu'.comp _ e.injective
  have hue : LinearIndependent K (u ∘ ⇑e) := hu.comp _ e.injective
  have hle : Submodule.span K (Set.range (u' ∘ ⇑e)) ≤ Submodule.span K (Set.range (u ∘ ⇑e)) :=
    Commons.LinearAlgebra.Plucker.span_le_of_iMulti_eq_smul (K := K) (u := u' ∘ ⇑e)
      (u' := u ∘ ⇑e) hu'e hue hc homega''
  have hle' : Submodule.span K (Set.range (u ∘ ⇑e)) ≤ Submodule.span K (Set.range (u' ∘ ⇑e)) := by
    refine Commons.LinearAlgebra.Plucker.span_le_of_iMulti_eq_smul (K := K) (u := u ∘ ⇑e)
      (u' := u' ∘ ⇑e) hue hu'e (inv_ne_zero hc) ?_
    rw [homega'', smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [← range_ofFinEmbEquiv_symm t, ← Set.range_comp u ⇑e, ← Set.range_comp u' ⇑e]
  exact le_antisymm hle' hle

end Submission.Subspace.RealRank
