import Mathlib
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_det_smul
import Submission.Commons.LinearAlgebra.ExteriorPower.iMultiDual_ne_zero_of_linearIndependent

/-!
# The wedge pairing and the annihilator of a wedge

For a field `K` and `r + k = N`, the wedge product followed by the top coefficient (the
coefficient of `e_0 ∧ ⋯ ∧ e_{N-1}` in `⋀^N (Fin N → K)`) gives a bilinear pairing

`wedgePair : ⋀^r (Fin N → K) → ⋀^k (Fin N → K) → K`.

Facts proved here (used for the "annihilator identity" of the rank descent):

* the pairing of two wedges of the *same* family vanishes unless the index sets are
  complementary, and in the complementary case it is a nonzero multiple of the determinant
  of the family (`wedgePair_iMulti_family_eq_zero_of_not_disjoint`,
  `wedgePair_iMulti_family_eq_smul_of_disjoint`);
* the top coefficient of the full wedge of a linearly independent family is nonzero
  (`topCoeff_iMulti_family_ne_zero`);
* the pairing is nondegenerate in its second argument
  (`wedgePair_right_nondegenerate`), so the functional `wedgePair · ω` determines `ω`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators exteriorPower
open ExteriorAlgebra

namespace Submission.Subspace.RealRank

variable {K : Type*} [Field K] {N r k : ℕ}

/-- Casting an element of `Set.powersetCard` along an equality of the cardinalities does not
change the underlying finset. -/
lemma val_cast_powersetCard {α : Type*} {n m : ℕ} (h : n = m) (x : Set.powersetCard α n) :
    (h ▸ x : Set.powersetCard α m).val = x.val := by
  subst h; rfl

/-- Reindexing `ιMulti_family` in the degree (the underlying set of indices is unchanged). -/
lemma iMulti_family_cast {M : Type*} {d m : ℕ} [AddCommGroup M] [Module K M] (h : d = m)
    (w : Fin N → M) (s : Set.powersetCard (Fin N) d) :
    ExteriorAlgebra.ιMulti_family K d w s = ExteriorAlgebra.ιMulti_family K m w (h ▸ s) := by
  subst h; rfl

/-- The coefficient of the top basis element `e_0 ∧ ⋯ ∧ e_{N-1}` in `⋀^N (Fin N → K)`. -/
noncomputable def topCoeff (K : Type*) [Field K] (N : ℕ) :
    ⋀[K]^N (Fin N → K) →ₗ[K] K :=
  exteriorPower.ιMultiDual K N (Pi.basisFun K (Fin N))
    (Set.powersetCard.ofFinEmb N (Fin N) (Function.Embedding.refl (Fin N)))

/-- Multiplication by a fixed `k`-vector, as a linear map into the top exterior power. -/
noncomputable def mulWedgeRight (h : r + k = N) (ω : ⋀[K]^k (Fin N → K)) :
    ⋀[K]^r (Fin N → K) →ₗ[K] ⋀[K]^N (Fin N → K) :=
  ((LinearMap.mulRight K (ω : ExteriorAlgebra K (Fin N → K))).comp
    (Submodule.subtype _)).codRestrict _
    (fun Y => h ▸ (SetLike.mul_mem_graded (A := fun i => ⋀[K]^i (Fin N → K)) Y.2 ω.2))

/-- Multiplication by a fixed `r`-vector, as a linear map into the top exterior power. -/
noncomputable def mulWedgeLeft (h : r + k = N) (Y : ⋀[K]^r (Fin N → K)) :
    ⋀[K]^k (Fin N → K) →ₗ[K] ⋀[K]^N (Fin N → K) :=
  ((LinearMap.mulLeft K (Y : ExteriorAlgebra K (Fin N → K))).comp
    (Submodule.subtype _)).codRestrict _
    (fun ω => h ▸ (SetLike.mul_mem_graded (A := fun i => ⋀[K]^i (Fin N → K)) Y.2 ω.2))

/-- The wedge pairing `⋀^r × ⋀^k → K` for `r + k = N`. -/
noncomputable def wedgePair (h : r + k = N)
    (Y : ⋀[K]^r (Fin N → K)) (ω : ⋀[K]^k (Fin N → K)) : K :=
  topCoeff K N (mulWedgeRight h ω Y)

/-- The wedge pairing, as a linear map in its first argument. -/
noncomputable def wedgePairLinLeft (h : r + k = N) (ω : ⋀[K]^k (Fin N → K)) :
    ⋀[K]^r (Fin N → K) →ₗ[K] K :=
  (topCoeff K N).comp (mulWedgeRight h ω)

/-- The wedge pairing, as a linear map in its second argument. -/
noncomputable def wedgePairLinRight (h : r + k = N) (Y : ⋀[K]^r (Fin N → K)) :
    ⋀[K]^k (Fin N → K) →ₗ[K] K :=
  (topCoeff K N).comp (mulWedgeLeft h Y)

@[simp] lemma wedgePair_eq_linLeft (h : r + k = N) (Y : ⋀[K]^r (Fin N → K))
    (ω : ⋀[K]^k (Fin N → K)) : wedgePairLinLeft h ω Y = wedgePair h Y ω := rfl

lemma wedgePairLinLeft_apply (h : r + k = N) (Y : ⋀[K]^r (Fin N → K))
    (ω : ⋀[K]^k (Fin N → K)) : wedgePairLinLeft h ω Y = wedgePair h Y ω := rfl

lemma wedgePairLinRight_apply (h : r + k = N) (Y : ⋀[K]^r (Fin N → K))
    (ω : ⋀[K]^k (Fin N → K)) : wedgePairLinRight h Y ω = wedgePair h Y ω := by
  show topCoeff K N (mulWedgeLeft h Y ω) = topCoeff K N (mulWedgeRight h ω Y)
  congr 1

/-- The pairing of two wedges of the same family vanishes when the index sets meet. -/
lemma wedgePair_iMulti_family_eq_zero_of_not_disjoint (h : r + k = N)
    (w : Fin N → (Fin N → K))
    (s : Set.powersetCard (Fin N) r) (t : Set.powersetCard (Fin N) k)
    (hnd : ¬ Disjoint (s : Finset (Fin N)) (t : Finset (Fin N))) :
    wedgePair h (exteriorPower.ιMulti_family K r w s)
      (exteriorPower.ιMulti_family K k w t) = 0 := by
  have hx : ((exteriorPower.ιMulti_family K r w s : ExteriorAlgebra K (Fin N → K))
      * (exteriorPower.ιMulti_family K k w t : ExteriorAlgebra K (Fin N → K))) = 0 := by
    rw [exteriorPower.ιMulti_family_apply_coe, exteriorPower.ιMulti_family_apply_coe,
      ExteriorAlgebra.ιMulti_family_mul_of_not_disjoint K w s t hnd]
  have hz : mulWedgeRight h (exteriorPower.ιMulti_family K k w t)
      (exteriorPower.ιMulti_family K r w s) = 0 := Subtype.ext hx
  rw [wedgePair, hz, map_zero]

/-- The pairing of two wedges of the same family with complementary index sets. -/
lemma wedgePair_iMulti_family_eq_smul_of_disjoint (h : r + k = N)
    (w : Fin N → (Fin N → K))
    (s : Set.powersetCard (Fin N) r) (t : Set.powersetCard (Fin N) k)
    (hd : Disjoint (s : Finset (Fin N)) (t : Finset (Fin N)))
    (hu : (s : Finset (Fin N)) ∪ (t : Finset (Fin N)) = Finset.univ) :
    wedgePair h (exteriorPower.ιMulti_family K r w s)
      (exteriorPower.ιMulti_family K k w t)
      = (((Set.powersetCard.permOfDisjoint hd).sign : ℤ) : K) *
        topCoeff K N (exteriorPower.ιMulti_family K N w
          (Set.powersetCard.ofFinEmb N (Fin N) (Function.Embedding.refl (Fin N)))) := by
  have hident : ExteriorAlgebra.ιMulti_family K (r + k) w (Set.powersetCard.disjUnion hd)
      = ExteriorAlgebra.ιMulti_family K N w
        (Set.powersetCard.ofFinEmb N (Fin N) (Function.Embedding.refl (Fin N))) := by
    rw [iMulti_family_cast (K := K) h w (Set.powersetCard.disjUnion hd)]
    congr 1
    apply Subtype.ext
    simp only [val_cast_powersetCard, Set.powersetCard.val_ofFinEmb, Finset.map_refl,
      Set.powersetCard.coe_disjUnion, Finset.disjUnion_eq_union, hu]
  have hx : ((exteriorPower.ιMulti_family K r w s : ExteriorAlgebra K (Fin N → K))
      * (exteriorPower.ιMulti_family K k w t : ExteriorAlgebra K (Fin N → K)))
      = (((Set.powersetCard.permOfDisjoint hd).sign : ℤ) : K) •
        (ExteriorAlgebra.ιMulti_family K N w
          (Set.powersetCard.ofFinEmb N (Fin N) (Function.Embedding.refl (Fin N)))) := by
    rw [exteriorPower.ιMulti_family_apply_coe, exteriorPower.ιMulti_family_apply_coe,
      ExteriorAlgebra.ιMulti_family_mul_of_disjoint K w s t hd, hident, Units.smul_def,
      Int.cast_smul_eq_zsmul]
  have hz : mulWedgeRight h (exteriorPower.ιMulti_family K k w t)
      (exteriorPower.ιMulti_family K r w s)
      = (((Set.powersetCard.permOfDisjoint hd).sign : ℤ) : K) •
        (exteriorPower.ιMulti_family K N w
          (Set.powersetCard.ofFinEmb N (Fin N) (Function.Embedding.refl (Fin N)))) :=
    Subtype.ext hx
  rw [wedgePair, hz, map_smul, smul_eq_mul]

/-- The top coefficient of the full wedge of the standard basis is `1`. -/
lemma topCoeff_basis_eq_one :
    topCoeff K N (exteriorPower.ιMulti_family K N (Pi.basisFun K (Fin N))
      (Set.powersetCard.ofFinEmb N (Fin N) (Function.Embedding.refl (Fin N)))) = 1 := by
  unfold topCoeff
  exact exteriorPower.ιMultiDual_apply_diag K N (Pi.basisFun K (Fin N))
    (Set.powersetCard.ofFinEmb N (Fin N) (Function.Embedding.refl (Fin N)))

/-- The top coefficient of the full wedge of a family is the determinant of the coordinate
matrix, hence nonzero for a linearly independent family. -/
lemma topCoeff_iMulti_family_ne_zero (w : Fin N → (Fin N → K))
    (hw : LinearIndependent K w) :
    topCoeff K N (exteriorPower.ιMulti_family K N w
      (Set.powersetCard.ofFinEmb N (Fin N) (Function.Embedding.refl (Fin N)))) ≠ 0 := by
  unfold topCoeff
  exact Commons.LinearAlgebra.ExteriorPower.iMultiDual_ne_zero_of_linearIndependent w hw

/-- **Nondegeneracy of the wedge pairing in its second argument.** -/
theorem wedgePair_right_nondegenerate (h : r + k = N)
    (ω : ⋀[K]^k (Fin N → K))
    (H : ∀ Y : ⋀[K]^r (Fin N → K), wedgePair h Y ω = 0) : ω = 0 := by
  classical
  set b := Pi.basisFun K (Fin N) with hb
  set B : Module.Basis (Set.powersetCard (Fin N) k) K (⋀[K]^k (Fin N → K)) :=
    b.exteriorPower k with hB
  have hexp : ω = ∑ t : Set.powersetCard (Fin N) k, (B.repr ω) t • B t :=
    (Module.Basis.sum_repr B ω).symm
  have hbasis : ∀ t : Set.powersetCard (Fin N) k, B t = exteriorPower.ιMulti_family K k b t :=
    fun t => exteriorPower.basis_apply K k b t
  have hcoeff : ∀ t₀ : Set.powersetCard (Fin N) k, (B.repr ω) t₀ = 0 := by
    intro t₀
    set s₀ : Set.powersetCard (Fin N) r := Set.powersetCard.compl (by simpa using h) t₀ with hs₀
    have hds : Disjoint (s₀ : Finset (Fin N)) (t₀ : Finset (Fin N)) := by
      rw [hs₀, Finset.disjoint_left]
      intro a ha
      rw [Set.powersetCard.coe_compl, Finset.mem_compl] at ha
      exact ha
    have hus : (s₀ : Finset (Fin N)) ∪ (t₀ : Finset (Fin N)) = Finset.univ := by
      ext a
      rw [Finset.mem_union, hs₀, Set.powersetCard.coe_compl, Finset.mem_compl]
      by_cases hmem : a ∈ (t₀ : Finset (Fin N)) <;> simp [hmem]
    have hY : (wedgePairLinRight h (exteriorPower.ιMulti_family K r b s₀)) ω = 0 := by
      rw [wedgePairLinRight_apply]
      exact H _
    have hsum : (wedgePairLinRight h (exteriorPower.ιMulti_family K r b s₀)) ω
        = (B.repr ω) t₀ *
          (wedgePairLinRight h (exteriorPower.ιMulti_family K r b s₀) (B t₀)) := by
      conv_lhs => rw [hexp]
      rw [map_sum]
      rw [Finset.sum_eq_single t₀]
      · rw [map_smul, smul_eq_mul, hbasis t₀]
      · intro t _ ht
        have hnd : ¬ Disjoint (s₀ : Finset (Fin N)) (t : Finset (Fin N)) := by
          intro hdj
          have hsub : (t : Finset (Fin N)) ⊆ (t₀ : Finset (Fin N)) := by
            intro a ha
            by_contra hcon
            have : a ∈ (s₀ : Finset (Fin N)) := by
              rw [hs₀, Set.powersetCard.coe_compl, Finset.mem_compl]; exact hcon
            exact (Finset.disjoint_left.mp hdj this) ha
          exact ht (Subtype.ext (Finset.eq_of_subset_of_card_le hsub
            (by rw [Set.powersetCard.card_eq, Set.powersetCard.card_eq])))
        rw [map_smul, smul_eq_mul, hbasis t, wedgePairLinRight_apply,
          wedgePair_iMulti_family_eq_zero_of_not_disjoint h b s₀ t hnd, mul_zero]
      · intro ht
        exact absurd (Finset.mem_univ t₀) ht
    rw [hsum, hbasis t₀, wedgePairLinRight_apply] at hY
    have hdiag : wedgePair h (exteriorPower.ιMulti_family K r b s₀)
        (exteriorPower.ιMulti_family K k b t₀)
        = (((Set.powersetCard.permOfDisjoint hds).sign : ℤ) : K) *
          topCoeff K N (exteriorPower.ιMulti_family K N b
            (Set.powersetCard.ofFinEmb N (Fin N) (Function.Embedding.refl (Fin N)))) :=
      wedgePair_iMulti_family_eq_smul_of_disjoint h b s₀ t₀ hds hus
    rw [hdiag, topCoeff_basis_eq_one, mul_one] at hY
    have hne : ((((Set.powersetCard.permOfDisjoint hds).sign : ℤˣ) : ℤ) : K) ≠ 0 :=
      (((Set.powersetCard.permOfDisjoint hds).sign.isUnit).map (Int.castRingHom K)).ne_zero
    exact (mul_eq_zero.mp hY).resolve_right hne
  rw [hexp]
  simp only [hcoeff, zero_smul, Finset.sum_const_zero]

end Submission.Subspace.RealRank
