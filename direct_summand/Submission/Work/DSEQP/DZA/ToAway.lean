/-
# Area DZA: the chart ring `Away 𝒜 (xS S)` as the degree-zero part of the chart localization

`Work.DSEQP.gf_degzero_away`: there is an `A`-linear isomorphism, natural in `S`, between
`(A[x₀,…,x_N][1/x_S])₀` and `Away (MvPolynomial.homogeneousSubmodule (Fin (N+1)) A) (xS S)`.
The map is the obvious one on the generating fractions `m / xS S ^ k` with `m ∈ 𝒜 (k · S.card)`.
-/
import Submission.Work.DSEQP.DZA.Chart

open MvPolynomial HomogeneousLocalization
open scoped BigOperators

namespace Work.DSEQP.DZA

universe a

variable {A : Type a} [CommRing A] {N : ℕ}

noncomputable section

/-! ## 5. The `A`-linear map `degZero S → Away 𝒜 (xS S)` -/

section ToAway

/-- `HasRepr S x k m` : `x = m / xS S ^ k` with `m` homogeneous of degree `k * S.card`. -/
def HasRepr (S : Finset (Fin (N + 1)))
    (x : Work.DSCOH.locAt (A := A) (M := MvPolynomial (Fin (N + 1)) A) S) (k : ℕ)
    (m : MvPolynomial (Fin (N + 1)) A) : Prop :=
  m ∈ Work.DSCOH.homSub A (N + 1) (k * S.card) ∧
    x = Work.DSCOH.divPow (A := A) (M := MvPolynomial (Fin (N + 1)) A) S k
      (Work.DSCOH.toLoc (A := A) (M := MvPolynomial (Fin (N + 1)) A) S m)

lemma exists_hasRepr (S : Finset (Fin (N + 1)))
    {x : Work.DSCOH.locAt (A := A) (M := MvPolynomial (Fin (N + 1)) A) S}
    (hx : x ∈ Work.DSCOH.degZero (A := A) (M := MvPolynomial (Fin (N + 1)) A)
      (Work.DSCOH.homSub A (N + 1)) S) : ∃ k m, HasRepr (A := A) (N := N) S x k m := by
  obtain ⟨k, m, hm, hx'⟩ := Work.DSCOH.degZero_exists_repr (A := A) (n := N + 1)
    (M := MvPolynomial (Fin (N + 1)) A) (Work.DSCOH.homSub A (N + 1)) S hx
  exact ⟨k, m, hm, hx'⟩

noncomputable def reprK (S : Finset (Fin (N + 1)))
    (x : ↥(Work.DSCOH.degZero (A := A) (M := MvPolynomial (Fin (N + 1)) A)
      (Work.DSCOH.homSub A (N + 1)) S)) : ℕ :=
  Classical.choose (exists_hasRepr (A := A) (N := N) S x.2)

noncomputable def reprM (S : Finset (Fin (N + 1)))
    (x : ↥(Work.DSCOH.degZero (A := A) (M := MvPolynomial (Fin (N + 1)) A)
      (Work.DSCOH.homSub A (N + 1)) S)) : MvPolynomial (Fin (N + 1)) A :=
  Classical.choose (Classical.choose_spec (exists_hasRepr (A := A) (N := N) S x.2))

lemma repr_spec (S : Finset (Fin (N + 1)))
    (x : ↥(Work.DSCOH.degZero (A := A) (M := MvPolynomial (Fin (N + 1)) A)
      (Work.DSCOH.homSub A (N + 1)) S)) :
    HasRepr (A := A) (N := N) S (x : Work.DSCOH.locAt (A := A)
      (M := MvPolynomial (Fin (N + 1)) A) S) (reprK (A := A) (N := N) S x)
      (reprM (A := A) (N := N) S x) :=
  Classical.choose_spec (Classical.choose_spec (exists_hasRepr (A := A) (N := N) S x.2))

/-- The underlying function of the isomorphism, on a chosen presentation. -/
noncomputable def toAwayFun (S : Finset (Fin (N + 1)))
    (x : ↥(Work.DSCOH.degZero (A := A) (M := MvPolynomial (Fin (N + 1)) A)
      (Work.DSCOH.homSub A (N + 1)) S)) :
    Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S) :=
  Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_mem_homSub S) (reprK (A := A) (N := N) S x)
    (reprM (A := A) (N := N) S x) (repr_spec (A := A) (N := N) S x).1

/-- The value of `toAwayFun` on an explicitly given presentation. -/
lemma toAwayFun_of_repr (S : Finset (Fin (N + 1)))
    (x : ↥(Work.DSCOH.degZero (A := A) (M := MvPolynomial (Fin (N + 1)) A)
      (Work.DSCOH.homSub A (N + 1)) S)) {k : ℕ} {m : MvPolynomial (Fin (N + 1)) A}
    (hm : m ∈ Work.DSCOH.homSub A (N + 1) (k * S.card))
    (hx : (x : Work.DSCOH.locAt (A := A) (M := MvPolynomial (Fin (N + 1)) A) S) =
      Work.DSCOH.divPow (A := A) (M := MvPolynomial (Fin (N + 1)) A) S k
        (Work.DSCOH.toLoc (A := A) (M := MvPolynomial (Fin (N + 1)) A) S m)) :
    toAwayFun (A := A) (N := N) S x =
      Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_mem_homSub S) k m hm := by
  unfold toAwayFun
  rw [away_mk_eq_iff (Work.DSEQP.xS_mem_homSub S) (isRegular_xS S)
    (reprK (A := A) (N := N) S x) k (reprM (A := A) (N := N) S x) m
    (repr_spec (A := A) (N := N) S x).1 hm]
  exact (locAt_divPow_eq_iff S (reprK (A := A) (N := N) S x) k
    (reprM (A := A) (N := N) S x) m).mp
    (by rw [← (repr_spec (A := A) (N := N) S x).2, hx])

/-- **The `A`-linear map `degZero S → Away 𝒜 (xS S)`.** -/
noncomputable def toAway (S : Finset (Fin (N + 1))) :
    ↥(Work.DSCOH.degZero (A := A) (M := MvPolynomial (Fin (N + 1)) A)
      (Work.DSCOH.homSub A (N + 1)) S) →ₗ[A]
      Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S) where
  toFun := toAwayFun (A := A) (N := N) S
  map_add' x y := by
    obtain ⟨kx, mx, hmx, hx⟩ := Work.DSCOH.degZero_exists_repr (A := A) (n := N + 1)
      (M := MvPolynomial (Fin (N + 1)) A) (Work.DSCOH.homSub A (N + 1)) S x.2
    obtain ⟨ky, my, hmy, hy⟩ := Work.DSCOH.degZero_exists_repr (A := A) (n := N + 1)
      (M := MvPolynomial (Fin (N + 1)) A) (Work.DSCOH.homSub A (N + 1)) S y.2
    have hxy : ((x + y : ↥(Work.DSCOH.degZero (A := A) (M := MvPolynomial (Fin (N + 1)) A)
        (Work.DSCOH.homSub A (N + 1)) S)) :
        Work.DSCOH.locAt (A := A) (M := MvPolynomial (Fin (N + 1)) A) S) =
        Work.DSCOH.divPow (A := A) (M := MvPolynomial (Fin (N + 1)) A) S (kx + ky)
          (Work.DSCOH.toLoc (A := A) (M := MvPolynomial (Fin (N + 1)) A) S
            ((Work.DSEQP.xS (A := A) S) ^ ky * mx + (Work.DSEQP.xS (A := A) S) ^ kx * my)) := by
      rw [Submodule.coe_add, hx, hy, divPow_toLoc_add]
    rw [toAwayFun_of_repr (A := A) (N := N) S (x + y) (pow_mul_mem (S := S) (k := kx) (k' := ky) (m := mx) (m' := my) hmx hmy) hxy,
      toAwayFun_of_repr (A := A) (N := N) S x hmx hx,
      toAwayFun_of_repr (A := A) (N := N) S y hmy hy,
      away_mk_add_pad (Work.DSEQP.xS_mem_homSub S) kx ky mx my hmx hmy (mul_pow_mem (S := S) (k := kx) (k' := ky) (m := mx) (m' := my) hmx hmy)]
    exact away_mk_congr_num (Work.DSEQP.xS_mem_homSub S) (kx + ky) (by ring) _ _
  map_smul' c x := by
    obtain ⟨kx, mx, hmx, hx⟩ := Work.DSCOH.degZero_exists_repr (A := A) (n := N + 1)
      (M := MvPolynomial (Fin (N + 1)) A) (Work.DSCOH.homSub A (N + 1)) S x.2
    have hcx : ((c • x : ↥(Work.DSCOH.degZero (A := A) (M := MvPolynomial (Fin (N + 1)) A)
        (Work.DSCOH.homSub A (N + 1)) S)) :
        Work.DSCOH.locAt (A := A) (M := MvPolynomial (Fin (N + 1)) A) S) =
        Work.DSCOH.divPow (A := A) (M := MvPolynomial (Fin (N + 1)) A) S kx
          (Work.DSCOH.toLoc (A := A) (M := MvPolynomial (Fin (N + 1)) A) S (c • mx)) := by
      rw [Submodule.coe_smul, hx, divPow_toLoc_smul]
    rw [toAwayFun_of_repr (A := A) (N := N) S (c • x) (Submodule.smul_mem _ c hmx) hcx,
      toAwayFun_of_repr (A := A) (N := N) S x hmx hx]
    rw [RingHom.id_apply]
    conv_rhs => rw [Algebra.smul_def]
    exact (AtoAway_mul_away_mk (A := A) (N := N) S c kx mx hmx (Submodule.smul_mem _ c hmx)).symm

lemma toAway_apply_repr (S : Finset (Fin (N + 1)))
    (x : ↥(Work.DSCOH.degZero (A := A) (M := MvPolynomial (Fin (N + 1)) A)
      (Work.DSCOH.homSub A (N + 1)) S)) {k : ℕ} {m : MvPolynomial (Fin (N + 1)) A}
    (hm : m ∈ Work.DSCOH.homSub A (N + 1) (k * S.card))
    (hx : (x : Work.DSCOH.locAt (A := A) (M := MvPolynomial (Fin (N + 1)) A) S) =
      Work.DSCOH.divPow (A := A) (M := MvPolynomial (Fin (N + 1)) A) S k
        (Work.DSCOH.toLoc (A := A) (M := MvPolynomial (Fin (N + 1)) A) S m)) :
    toAway (A := A) (N := N) S x =
      Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_mem_homSub S) k m hm :=
  toAwayFun_of_repr (A := A) (N := N) S x hm hx

lemma toAway_injective (S : Finset (Fin (N + 1))) :
    Function.Injective (toAway (A := A) (N := N) S) := by
  intro x y hxy
  obtain ⟨kx, mx, hmx, hx⟩ := Work.DSCOH.degZero_exists_repr (A := A) (n := N + 1)
    (M := MvPolynomial (Fin (N + 1)) A) (Work.DSCOH.homSub A (N + 1)) S x.2
  obtain ⟨ky, my, hmy, hy⟩ := Work.DSCOH.degZero_exists_repr (A := A) (n := N + 1)
    (M := MvPolynomial (Fin (N + 1)) A) (Work.DSCOH.homSub A (N + 1)) S y.2
  rw [toAway_apply_repr (A := A) (N := N) S x hmx hx,
    toAway_apply_repr (A := A) (N := N) S y hmy hy] at hxy
  have h := (away_mk_eq_iff (Work.DSEQP.xS_mem_homSub S) (isRegular_xS S) kx ky mx my
    hmx hmy).mp hxy
  apply Subtype.ext
  rw [hx, hy]
  exact (locAt_divPow_eq_iff S kx ky mx my).mpr h

lemma toAway_surjective (S : Finset (Fin (N + 1))) :
    Function.Surjective (toAway (A := A) (N := N) S) := by
  intro z
  obtain ⟨k, m, hm, hz⟩ := HomogeneousLocalization.Away.mk_surjective
    (𝒜 := DSMap.PGr A N) (f := Work.DSEQP.xS (A := A) S) (Work.DSEQP.xS_mem_homSub S) z
  refine ⟨⟨Work.DSCOH.divPow (A := A) (M := MvPolynomial (Fin (N + 1)) A) S k
      (Work.DSCOH.toLoc (A := A) (M := MvPolynomial (Fin (N + 1)) A) S m),
      Work.DSCOH.divPow_toLoc_mem (A := A) (n := N + 1)
        (M := MvPolynomial (Fin (N + 1)) A) (Work.DSCOH.homSub A (N + 1)) S k hm⟩, ?_⟩
  exact (toAway_apply_repr (A := A) (N := N) S _ hm rfl).trans hz

lemma toAway_bijective (S : Finset (Fin (N + 1))) :
    Function.Bijective (toAway (A := A) (N := N) S) :=
  ⟨toAway_injective (A := A) (N := N) S, toAway_surjective (A := A) (N := N) S⟩

/-- **The isomorphism.** -/
noncomputable def e (S : Finset (Fin (N + 1))) (hS : S.Nonempty) :
    ↥(Work.DSCOH.degZero (A := A) (M := MvPolynomial (Fin (N + 1)) A)
      (Work.DSCOH.homSub A (N + 1)) S) ≃ₗ[A]
      Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S) :=
  LinearEquiv.ofBijective (toAway (A := A) (N := N) S) (toAway_bijective (A := A) (N := N) S)

/-- **Naturality** of `toAway` in `S`. -/
lemma toAway_natural {S T : Finset (Fin (N + 1))} (hST : S ⊆ T)
    (x : ↥(Work.DSCOH.degZero (A := A) (M := MvPolynomial (Fin (N + 1)) A)
      (Work.DSCOH.homSub A (N + 1)) S)) :
    toAway (A := A) (N := N) T (Work.DSCOH.degPartRestrict (A := A) (n := N + 1)
        (M := MvPolynomial (Fin (N + 1)) A) (Work.DSCOH.homSub A (N + 1))
        (Work.DSCOH.resAt (A := A) (M := MvPolynomial (Fin (N + 1)) A) hST)
        (fun y hy => Work.DSCOH.resAt_degZero (A := A)
          (M := MvPolynomial (Fin (N + 1)) A) hST y hy) x)
      = Work.DSEQP.awayRes (A := A) (N := N) hST (toAway (A := A) (N := N) S x) := by
  obtain ⟨k, m, hm, hx⟩ := Work.DSCOH.degZero_exists_repr (A := A) (n := N + 1)
    (M := MvPolynomial (Fin (N + 1)) A) (Work.DSCOH.homSub A (N + 1)) S x.2
  have hres : ((Work.DSCOH.degPartRestrict (A := A) (n := N + 1)
      (M := MvPolynomial (Fin (N + 1)) A) (Work.DSCOH.homSub A (N + 1))
      (Work.DSCOH.resAt (A := A) (M := MvPolynomial (Fin (N + 1)) A) hST)
      (fun y hy => Work.DSCOH.resAt_degZero (A := A) (M := MvPolynomial (Fin (N + 1)) A)
        hST y hy) x : ↥(Work.DSCOH.degZero (A := A) (M := MvPolynomial (Fin (N + 1)) A)
        (Work.DSCOH.homSub A (N + 1)) T)) :
      Work.DSCOH.locAt (A := A) (M := MvPolynomial (Fin (N + 1)) A) T) =
      Work.DSCOH.divPow (A := A) (M := MvPolynomial (Fin (N + 1)) A) T k
        (Work.DSCOH.toLoc (A := A) (M := MvPolynomial (Fin (N + 1)) A) T
          ((Work.DSEQP.xS (A := A) (T \ S)) ^ k * m)) := by
    change Work.DSCOH.resAt (A := A) (M := MvPolynomial (Fin (N + 1)) A) hST
        (x : Work.DSCOH.locAt (A := A) (M := MvPolynomial (Fin (N + 1)) A) S) = _
    rw [hx, Work.DSCOH.resAt_divPow_toLoc, smul_self_eq_mul]
    rfl
  rw [toAway_apply_repr (A := A) (N := N) T _ (xS_sdiff_pow_mul_mem (S := S) (T := T) hST (k := k) (m := m) hm) hres,
    toAway_apply_repr (A := A) (N := N) S x hm hx,
    Work.DSEQP.awayRes, HomogeneousLocalization.awayMap_mk]
  apply HomogeneousLocalization.val_injective
    (Submonoid.powers (Work.DSEQP.xS (A := A) T))
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by ring⟩

end ToAway



end

end Work.DSEQP.DZA
