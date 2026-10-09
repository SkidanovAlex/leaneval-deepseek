import Mathlib
import Submission.Work.SSGRoute.H9.NarrowOpen
import Submission.Work.H9Narrow.NarrowPos
import Submission.Work.SSGRoute.finiteIndex_gesU
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finite index of the narrow modulus

The positivity conditions of `Work.SSGRoute.H9.narrowGesU` only concern the archimedean places, and
at a real place they can be flipped by the `onePlace` idèle whose component there is `-1`.  Hence
for every `x ∈ powTIdeles` there is a product `s` of such sign-flips with
`x · s ∈ narrowPowTIdeles` (`exists_signFlip_mul_mem_narrowPowTIdeles`); consequently the quotient
`C_K ⧸ narrowGesU` is a quotient of the finite set `(C_K ⧸ gesU) × (Finset (InfinitePlace K))`
(the first factor finite because `gesU` has finite index, `Work.SSGRoute.finiteIndex_gesU`),
whence `(narrowGesU K p T').FiniteIndex`.

Auxiliary fact proved here as well: the comparison `w.Completion ≃+* ℝ` is *independent of the
proof* that `w` is real (it is pinned down by continuity and by its values on `K`), so `IsPosInf`
at a real place is the single inequality `0 < ρ e_{w}`.
-/

open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT
open NK.Chebotarev

namespace Work.SSGRoute.H9

variable {K : Type} [Field K] [NumberField K]

noncomputable local instance instDecidableEqInfinitePlace : DecidableEq (InfinitePlace K) :=
  Classical.decEq _

/-- **The comparison with `ℝ` at a real infinite place does not depend on the proof of realness.**
Both are continuous ring homomorphisms `w.Completion →+* ℝ` agreeing on the dense image of `K`
(where they are `embedding_of_isReal h`). -/
theorem ringEquivRealOfIsReal_congr {w : InfinitePlace K} (h1 h2 : w.IsReal) :
    (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal h1 : w.Completion →+* ℝ) =
      NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal h2 := by
  have hfun : (fun y : w.Completion =>
        NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal h1 y) =
      fun y : w.Completion =>
        NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal h2 y := by
    refine Continuous.ext_on (NumberField.InfinitePlace.Completion.denseRange_coe (v := w))
      ?_ ?_ ?_
    · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal h1).continuous
    · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal h2).continuous
    · intro y hy
      obtain ⟨c, rfl⟩ := hy
      simp only [NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
        NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe,
        Work.SSGRoute.ZDataTwo.embedding_of_isReal_eq h1 h2]
  exact RingHom.ext fun y => congrFun hfun y

/-- At a real place, `IsPosInf` is the single inequality `0 < ρ e_{w}` (for any realness proof). -/
theorem isPosInf_iff {w : InfinitePlace K} (hw : w.IsReal) (x : w.Completionˣ) :
    IsPosInf K w x ↔
      0 < NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw (x : w.Completion) := by
  constructor
  · exact fun h => h hw
  · intro h hw'
    have h2 : (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw' :
        w.Completion →+* ℝ) =
        NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw :=
      ringEquivRealOfIsReal_congr hw' hw
    have h3 : NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw' (x : w.Completion) =
        NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw (x : w.Completion) :=
      RingHom.congr_fun h2 (x : w.Completion)
    rw [h3]
    exact h

/-- **The sign-flip idèle of a finite set of infinite places**: the product, over `F`, of the
idèles whose component at `w ∈ F` is `-1` and whose other components are `1`. -/
noncomputable def signFlip (F : Finset (InfinitePlace K)) : Idele K :=
  F.prod fun w => NK.HassePrinciple.onePlace (Place.ofInfinite w)
    (-1 : (Place.localField K (Place.ofInfinite w))ˣ)

@[simp] theorem signFlip_empty : signFlip (K := K) ∅ = 1 := Finset.prod_empty

theorem signFlip_insert {F : Finset (InfinitePlace K)} {w : InfinitePlace K} (hw : w ∉ F) :
    signFlip (K := K) (insert w F) = NK.HassePrinciple.onePlace (Place.ofInfinite w)
        (-1 : (Place.localField K (Place.ofInfinite w))ˣ) * signFlip F :=
  Finset.prod_insert hw

/-- The finite components of a sign-flip are trivial. -/
theorem signFlip_apply_ofFinite (F : Finset (InfinitePlace K)) (q : PrimeIdeal K) :
    signFlip (K := K) F (Place.ofFinite q) = 1 := by
  classical
  induction F using Finset.induction with
  | empty => simp [signFlip]
  | insert w' F hw' ih =>
      rw [signFlip_insert hw', Idele.mul_apply,
        NK.HassePrinciple.onePlace_apply_ne (Place.ofInfinite_ne_ofFinite w' q).symm, ih,
          mul_one]

/-- Every sign-flip lies in the wide `E_{T,unr}`. -/
theorem signFlip_mem_powTIdeles (p : ℕ) (T' : Finset (PrimeIdeal K))
    (F : Finset (InfinitePlace K)) :
    signFlip (K := K) F ∈ Work.SSGRoute.powTIdeles K p T' := by
  classical
  rw [Work.SSGRoute.mem_powTIdeles]
  constructor
  · intro 𝔭 _
    rw [signFlip_apply_ofFinite F 𝔭]
    exact Subgroup.one_mem _
  · intro v hv
    rcases v with w | q
    · refine absurd (fun 𝔭 h => False.elim ?_) hv
      exact (Place.ofInfinite_ne_ofFinite w 𝔭) h.symm
    · rw [signFlip_apply_ofFinite F q]
      exact Subgroup.one_mem _

/-- The component of a sign-flip at an infinite place: `-1` on the set, `1` outside. -/
theorem signFlip_apply_ofInfinite (F : Finset (InfinitePlace K)) (w : InfinitePlace K) :
    ((signFlip (K := K) F (Place.ofInfinite w) :
        (Place.localField K (Place.ofInfinite w))ˣ) : w.Completion)
      = if w ∈ F then (-1 : w.Completion) else 1 := by
  classical
  induction F using Finset.induction with
  | empty => simp [signFlip]
  | insert w' F hw' ih =>
      rw [signFlip_insert hw', Idele.mul_apply, Units.val_mul]
      by_cases h : w = w'
      · subst h
        rw [NK.HassePrinciple.onePlace_apply_self, ih, if_neg hw',
          if_pos (Finset.mem_insert_self _ _)]
        simp
      · have hne : Place.ofInfinite w ≠ Place.ofInfinite w' :=
          fun hh => h (Place.ofInfinite_inj.mp hh)
        rw [NK.HassePrinciple.onePlace_apply_ne hne, ih]
        by_cases hF : w ∈ F <;> simp [Finset.mem_insert, hF, h]

/-- **The covering of the wide `E` by the narrow one and the sign-flips.**  For `x ∈ powTIdeles`
there is a finite set `F` of infinite places (namely the places at which `x` is not positive) with
`x · signFlip F ∈ narrowPowTIdeles`. -/
theorem exists_signFlip_mul_mem_narrowPowTIdeles (p : ℕ) (T' : Finset (PrimeIdeal K))
    {x : Idele K} (hx : x ∈ Work.SSGRoute.powTIdeles K p T') :
    ∃ F : Finset (InfinitePlace K),
      x * signFlip (K := K) F ∈ narrowPowTIdeles K p T' := by
  classical
  refine ⟨Finset.univ.filter fun w => ¬ IsPosInf K w (x (Place.ofInfinite w)), ?_⟩
  set F := Finset.univ.filter (fun w => ¬ IsPosInf K w (x (Place.ofInfinite w))) with hFdef
  have hFmem : ∀ w : InfinitePlace K, w ∈ F ↔ ¬ IsPosInf K w (x (Place.ofInfinite w)) := by
    intro w
    rw [hFdef, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ w, h⟩⟩
  rw [mem_narrowPowTIdeles]
  refine ⟨Subgroup.mul_mem _ hx (signFlip_mem_powTIdeles p T' F), ?_⟩
  intro w hw
  have hmul : ((x * signFlip (K := K) F) (Place.ofInfinite w) : w.Completion) =
      (x (Place.ofInfinite w) : w.Completion) *
        (signFlip (K := K) F (Place.ofInfinite w) : w.Completion) := by
    rw [Idele.mul_apply, Units.val_mul]
  rw [hmul, signFlip_apply_ofInfinite, map_mul]
  by_cases hpos : IsPosInf K w (x (Place.ofInfinite w))
  · rw [if_neg (fun h => (hFmem w).mp h hpos), map_one, mul_one]
    exact (isPosInf_iff (x := x (Place.ofInfinite w)) hw).mp hpos
  · rw [if_pos ((hFmem w).mpr hpos), map_neg, map_one]
    have hnot' : ¬ (0 < NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw
        (((x (Place.ofInfinite w) : (Place.localField K (Place.ofInfinite w))ˣ)) :
          w.Completion)) := by
      rwa [← isPosInf_iff hw]
    have hne : NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw
        (((x (Place.ofInfinite w) : (Place.localField K (Place.ofInfinite w))ˣ)) :
          w.Completion) ≠ 0 := by
      intro h0
      exact (x (Place.ofInfinite w)).ne_zero
        ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).injective
          (by rw [h0, map_zero]))
    have hlt : NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw
        (((x (Place.ofInfinite w) : (Place.localField K (Place.ofInfinite w))ˣ)) :
          w.Completion) < 0 :=
      lt_of_le_of_ne (not_lt.mp hnot') hne
    linarith

/-- **Every class is a sign-flip multiple of a class of the narrow `U`.**  For `x ∈ C_K` there are
a class `q` of `C_K ⧸ gesU` and a finite set `F` of infinite places with
`mk (out q · signFlip F) = mk x` in `C_K ⧸ narrowGesU`. -/
theorem exists_signFlip_rep (p : ℕ) [Fact p.Prime] (T' : Finset (PrimeIdeal K))
    (x : IdeleClassGroup K) :
    ∃ (q : IdeleClassGroup K ⧸ GrunwaldEscapeCore.gesU K p T')
      (F : Finset (InfinitePlace K)),
      ((Quotient.out q * (signFlip (K := K) F)⁻¹ : IdeleClassGroup K) :
          IdeleClassGroup K ⧸ narrowGesU K p T') =
        ((x : IdeleClassGroup K ⧸ narrowGesU K p T')) := by
  classical
  set q : IdeleClassGroup K ⧸ GrunwaldEscapeCore.gesU K p T' :=
    ((x : IdeleClassGroup K ⧸ GrunwaldEscapeCore.gesU K p T')) with hq
  have hmem : (Quotient.out q)⁻¹ * x ∈ GrunwaldEscapeCore.gesU K p T' := by
    rw [← QuotientGroup.eq_one_iff]
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq' q, hq]
    exact inv_mul_cancel _
  obtain ⟨e, he, heq⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨c, hc, d, hd, hcd⟩ := Subgroup.mem_sup.mp he
  obtain ⟨F, hF⟩ := exists_signFlip_mul_mem_narrowPowTIdeles p T' hd
  refine ⟨q, F, ?_⟩
  -- the principal factor `c` is invisible in `C_K`
  have hc1 : IdeleClassGroup.mk K c = 1 := by
    rw [← MonoidHom.mem_ker, Work.SSGRoute.ker_mk_eq_principal]
    exact hc
  have hxd : x = Quotient.out q * IdeleClassGroup.mk K d := by
    have h1 : IdeleClassGroup.mk K e = IdeleClassGroup.mk K d := by
      rw [← hcd, map_mul, hc1, one_mul]
    rw [← h1, heq]
    group
  rw [QuotientGroup.eq]
  have hform : ((Quotient.out q * (signFlip (K := K) F)⁻¹ : IdeleClassGroup K)⁻¹ * x :
      IdeleClassGroup K) =
      (signFlip (K := K) F : IdeleClassGroup K) * IdeleClassGroup.mk K d := by
    have hsinv : (((signFlip (K := K) F)⁻¹ : Idele K) : IdeleClassGroup K) =
        ((signFlip (K := K) F : IdeleClassGroup K))⁻¹ :=
      map_inv (IdeleClassGroup.mk K) (signFlip (K := K) F)
    rw [hxd, hsinv]
    group
  rw [hform]
  refine Subgroup.mem_map.mpr ⟨signFlip (K := K) F * d, Subgroup.mem_sup_right ?_, ?_⟩
  · rw [mul_comm]
    exact hF
  · rw [map_mul]
    rfl

/-- **The narrow modulus has finite index in `C_K`.**  Every class of `C_K` is a class of the
narrow `U` times the class of a sign-flip, so `(C_K ⧸ narrowGesU)` is a quotient of the finite set
`(C_K ⧸ gesU) × (Finset (InfinitePlace K))`. -/
theorem narrowGesU_finiteIndex (p : ℕ) [Fact p.Prime] (T' : Finset (PrimeIdeal K)) :
    (narrowGesU K p T').FiniteIndex := by
  classical
  haveI hges : (GrunwaldEscapeCore.gesU K p T').FiniteIndex :=
    Work.SSGRoute.finiteIndex_gesU (K := K) (p := p) T'
  haveI hfinq : Finite (IdeleClassGroup K ⧸ GrunwaldEscapeCore.gesU K p T') :=
    Subgroup.finiteIndex_iff_finite_quotient.mp hges
  haveI : Finite (IdeleClassGroup K ⧸ narrowGesU K p T') := by
    refine Finite.of_surjective
      (fun r : (IdeleClassGroup K ⧸ GrunwaldEscapeCore.gesU K p T') ×
          Finset (InfinitePlace K) =>
        ((Quotient.out r.1 * (signFlip (K := K) r.2)⁻¹ : IdeleClassGroup K) :
          IdeleClassGroup K ⧸ narrowGesU K p T')) ?_
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (narrowGesU K p T') y
    obtain ⟨q, F, hqF⟩ := exists_signFlip_rep p T' x
    refine ⟨(q, F), ?_⟩
    show ((Quotient.out q * (signFlip (K := K) F)⁻¹ : IdeleClassGroup K) :
        IdeleClassGroup K ⧸ narrowGesU K p T') = y
    rw [hqF, ← hx]
    rfl
  exact Subgroup.finiteIndex_of_finite_quotient

end Work.SSGRoute.H9
