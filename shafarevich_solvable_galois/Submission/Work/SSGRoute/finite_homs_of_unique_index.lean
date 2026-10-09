import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finitely many homomorphisms `Q →* M` when subgroups are determined by their index

If `M` is a finite group and `Q` is a group in which two subgroups with the same
(non-zero, i.e. finite) index are necessarily equal, then there are only finitely many
group homomorphisms `Q →* M`.

The argument is the following.  Every homomorphism `φ : Q →* M` has as kernel a subgroup
whose index is `Nat.card (Q ⧸ ker φ) = Nat.card φ.range ≤ Nat.card M`, in particular it is
a non-zero index.  By the hypothesis, for a fixed value `n ≥ 1` there is at most one
subgroup of index `n`, so the homomorphisms whose kernel has index `n` form a single
"fibre", and that fibre consists of homomorphisms whose kernel contains the (unique)
subgroup `K` of index `n`.  Such homomorphisms factor through `Q ⧸ K.normalClosure`, a
*finite* group, so there are only finitely many of them.  Summing over the finitely many
possible indices `n ∈ {1, …, Nat.card M}` gives finiteness of `Q →* M`.
-/

namespace Work.SSGRoute

/-- **Finitely many homomorphisms with kernel containing a finite-index subgroup.**
If `K ≤ Q` has finite index (`K.index ≠ 0`) and `M` is finite, then only finitely many
homomorphisms `Q →* M` have `K ≤ ker φ`.

Such a `φ` is constant on left cosets of `K`, hence factors through the (finite) quotient
by the normal core; we use the normal closure `K.normalClosure` for this, which is normal
of index dividing `K.index` and therefore `≠ 0`. -/
lemma finite_homs_ker_le {Q : Type*} [Group Q] (M : Type*) [Group M] [Finite M]
    (K : Subgroup Q) (hK : K.index ≠ 0) :
    Set.Finite {φ : Q →* M | K ≤ MonoidHom.ker φ} := by
  classical
  -- pass to the normal closure of `K`, through which every such `φ` factors
  let N : Subgroup Q := Subgroup.normalClosure (K : Set Q)
  haveI : N.Normal := Subgroup.normalClosure_normal
  have hKle : K ≤ N := Subgroup.le_normalClosure
  have hset : {φ : Q →* M | K ≤ MonoidHom.ker φ}
      = {φ : Q →* M | N ≤ MonoidHom.ker φ} := by
    ext φ
    exact ⟨fun hφ => Subgroup.normalClosure_le_normal (N := MonoidHom.ker φ) hφ,
           fun hφ => le_trans hKle hφ⟩
  rw [hset]
  -- `N` still has finite index, because its index divides that of `K`
  have hNidx : N.index ≠ 0 := by
    intro h0
    have hd : N.index ∣ K.index := Subgroup.index_dvd_of_le hKle
    rw [h0] at hd
    exact hK (Nat.eq_zero_of_zero_dvd hd)
  haveI : Finite (Q ⧸ N) := (Subgroup.index_ne_zero_iff_finite).mp hNidx
  haveI : Finite (Q ⧸ N →* M) :=
    Finite.of_injective (fun f : Q ⧸ N →* M => (f : Q ⧸ N → M))
      (fun f g hh => MonoidHom.ext (congrFun hh))
  -- `φ ↦ (Q → Q ⧸ N) ≫ φ` is injective on homs with `N ≤ ker φ`
  refine Finite.of_injective
    (fun φ : {φ : Q →* M // N ≤ MonoidHom.ker φ} => QuotientGroup.lift N φ.1 φ.2) ?_
  intro φ ψ hφψ
  have h : QuotientGroup.lift N φ.1 φ.2 = QuotientGroup.lift N ψ.1 ψ.2 := hφψ
  refine Subtype.ext ?_
  rw [← QuotientGroup.lift_comp_mk' N φ.1 φ.2, ← QuotientGroup.lift_comp_mk' N ψ.1 ψ.2, h]

theorem finite_homs_of_unique_index {Q : Type*} [Group Q] (M : Type*) [Group M] [Finite M]
    (h : ∀ K K' : Subgroup Q, K.index = K'.index → K.index ≠ 0 → K = K') :
    Finite (Q →* M) := by
  classical
  rw [← Set.finite_univ_iff]
  -- the index of a kernel is a non-zero natural number at most `Nat.card M`
  have hmem : ∀ φ : Q →* M, (MonoidHom.ker φ).index ∈ Finset.Icc 1 (Nat.card M) := by
    intro φ
    rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · rw [Subgroup.index_eq_card, Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
      exact Nat.card_pos
    · rw [Subgroup.index_eq_card, Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
      exact Nat.card_le_card_of_injective (fun x : φ.range => (x : M))
        (fun a b hh => Subtype.ext hh)
  -- `Q →* M` is covered by the finitely many fibres of the index map
  have hcover : (Set.univ : Set (Q →* M))
      = ⋃ n ∈ (Finset.Icc 1 (Nat.card M) : Set ℕ),
          {φ : Q →* M | (MonoidHom.ker φ).index = n} := by
    ext φ
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
    exact ⟨(MonoidHom.ker φ).index, by simpa using hmem φ, rfl⟩
  rw [hcover]
  refine Set.Finite.biUnion (Finset.finite_toSet _) ?_
  intro n hn
  by_cases hK : ∃ K : Subgroup Q, K.index = n
  · -- the fibre is contained in the finitely many homs with kernel containing `K`
    obtain ⟨K, hKn⟩ := hK
    have hn0 : n ≠ 0 := by
      have h1 := (Finset.mem_Icc.mp hn).1
      omega
    refine (finite_homs_ker_le M K ?_).subset ?_
    · rw [hKn]; exact hn0
    · intro φ hφ
      have hker : MonoidHom.ker φ = K :=
        h (MonoidHom.ker φ) K (by rw [hφ, hKn]) (by rw [hφ]; exact hn0)
      exact le_of_eq hker.symm
  · -- no subgroup of this index: the fibre is empty
    push Not at hK
    have hempty : {φ : Q →* M | (MonoidHom.ker φ).index = n} = ∅ := by
      ext φ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hφ => hK (MonoidHom.ker φ) hφ
    rw [hempty]; exact Set.finite_empty

end Work.SSGRoute
