import Mathlib.Algebra.Field.Shrink
import Mathlib.FieldTheory.Galois.Infinite
import Submission.Commons.FieldTheory.Galois.isSeparable_of_ringEquiv
import Submission.Commons.FieldTheory.IsSepClosed.countable_of_isSepClosure
import Submission.Commons.NumberTheory.NumberField.countable

namespace Commons.FieldTheory.Galois

open scoped NumberField
open IntermediateField

universe u₁ u₂ u₃ u₄

/-- The property of being separably closed transfers across a ring isomorphism. -/
theorem isSepClosed_of_ringEquiv_aux {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    [IsSepClosed K] : IsSepClosed L := by
  refine IsSepClosed.mk fun p hp => ?_
  have hcomp : ((e : K →+* L).comp (e.symm : L →+* K)) = RingHom.id L := by ext x; simp
  have hmap : (p.map (e.symm : L →+* K)).map (e : K →+* L) = p := by
    rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  have hspl : (p.map (e.symm : L →+* K)).Splits :=
    IsSepClosed.splits_of_separable _ (hp.map)
  have := hspl.map (e : K →+* L)
  rwa [hmap] at this

theorem eq_one_of_preserves_and_centralizes_aux {k : Type u₁} {E : Type u₂} [Field k] [Field E] [Algebra k E]
    [NumberField k] [IsSepClosure k E]
    (hZ : ∀ (F : Type u₃) [Field F] [NumberField F] (F' : Type u₄) [Field F'] [Algebra F F']
        [IsSepClosure F F'], ∀ c : Gal(F'/F), (∀ h : Gal(F'/F), c * h = h * c) → c = 1)
    (c : E ≃+* E)
    (hpres : ∀ x ∈ (algebraMap k E).range, c x ∈ (algebraMap k E).range)
    (hcomm : ∀ g : Gal(E/k), c.trans (g.toRingEquiv.trans c.symm) = g.toRingEquiv) :
    c = 1 := by
  -- ## Part 1: the Galois-theoretic reduction
  letI : Algebra ℚ E := RingHom.toAlgebra ((algebraMap k E).comp (algebraMap ℚ k))
  haveI hST : IsScalarTower ℚ k E := IsScalarTower.of_algebraMap_eq (fun q => rfl)
  have hQ1 : ∀ q : ℚ, algebraMap ℚ E q = (q : E) := by
    intro q
    show (algebraMap k E) (algebraMap ℚ k q) = (q : E)
    rw [show algebraMap ℚ k q = (q : k) by exact map_ratCast _ q, map_ratCast]
  have hcQ : ∀ q : ℚ, c (algebraMap ℚ E q) = algebraMap ℚ E q := by
    intro q
    rw [hQ1 q, map_ratCast]
  let C : Gal(E/ℚ) := AlgEquiv.ofRingEquiv (f := c) hcQ
  have hCapply : ∀ x : E, C x = c x := fun _ => rfl
  haveI halgK : Algebra.IsAlgebraic ℚ k := inferInstance
  haveI halgkE : Algebra.IsAlgebraic k E := inferInstance
  haveI halgQE : Algebra.IsAlgebraic ℚ E := Algebra.IsAlgebraic.trans ℚ k E
  haveI hintQE : Algebra.IsIntegral ℚ E := inferInstance
  haveI hsepQE : Algebra.IsSeparable ℚ E := inferInstance
  haveI hssc : IsSepClosed E := IsSepClosure.sep_closed k
  haveI hsscQ : IsSepClosure ℚ E := ⟨hssc, hsepQE⟩
  haveI hgalQ : IsGalois ℚ E := IsSepClosure.isGalois
  haveI ht2 : T2Space Gal(E/ℚ) := krullTopology_t2
  let K₀ : Set Gal(E/ℚ) := Set.range (fun g : Gal(E/k) => g.restrictScalars ℚ)
  have hcommC : ∀ g : Gal(E/k), C * (g.restrictScalars ℚ) = (g.restrictScalars ℚ) * C := by
    intro g
    apply AlgEquiv.ext
    intro x
    simp only [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply, hCapply]
    have h := congrArg (fun (e : E ≃+* E) => e x) (hcomm g)
    have h2 : g (c x) = c (g x) := by
      have h3 := congrArg c h
      simpa using h3
    exact h2.symm
  let H : Subgroup Gal(E/ℚ) := Subgroup.closure ({C} ∪ K₀)
  have hC_mem_H : C ∈ H := Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_singleton C))
  have hZclosed : IsClosed
      ((Subgroup.centralizer ({C} : Set Gal(E/ℚ))) : Set Gal(E/ℚ)) := by
    have heq : (Set.centralizer ({C} : Set Gal(E/ℚ)))
        = ((Subgroup.centralizer ({C} : Set Gal(E/ℚ))) : Set Gal(E/ℚ)) := by
      ext x
      rw [Set.mem_centralizer_iff]
      show (∀ m ∈ ({C} : Set Gal(E/ℚ)), m * x = x * m) ↔
        x ∈ Subgroup.centralizer ({C} : Set Gal(E/ℚ))
      rw [Subgroup.mem_centralizer_iff]
    rw [← heq]
    exact Set.isClosed_centralizer _
  have hH_le_Z : H ≤ Subgroup.centralizer ({C} : Set Gal(E/ℚ)) := by
    rw [Subgroup.closure_le]
    intro x hx
    show x ∈ Subgroup.centralizer ({C} : Set Gal(E/ℚ))
    rw [Subgroup.mem_centralizer_iff]
    rcases hx with hx | hx
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      rfl
    · rcases hx with ⟨g, rfl⟩
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hcommC g
  have hHbar_le_Z : H.topologicalClosure ≤ Subgroup.centralizer ({C} : Set Gal(E/ℚ)) :=
    Subgroup.topologicalClosure_minimal H hH_le_Z hZclosed
  have hC_in_Hbar : C ∈ H.topologicalClosure := Subgroup.le_topologicalClosure H hC_mem_H
  let F : IntermediateField ℚ E := IntermediateField.fixedField H.topologicalClosure
  have hF_fix : F.fixingSubgroup = H.topologicalClosure :=
    InfiniteGalois.fixingSubgroup_fixedField
      ⟨H.topologicalClosure, Subgroup.isClosed_topologicalClosure H⟩
  have hF_sub : ∀ x : E, x ∈ F → x ∈ (algebraMap k E).range := by
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hfix : ∀ f : Gal(E/k), f x = x := by
      intro f
      have hmem : f.restrictScalars ℚ ∈ H.topologicalClosure :=
        Subgroup.le_topologicalClosure H
          (Subgroup.subset_closure (Set.mem_union_right _
            (show f.restrictScalars ℚ ∈ K₀ from ⟨f, rfl⟩)))
      have := hx _ hmem
      simpa using this
    have hx' := (InfiniteGalois.mem_bot_iff_fixed (k := k) (K := E) x).mpr hfix
    exact (IntermediateField.mem_bot).mp hx'
  have hCFfix : ∀ x : ↥F, c (algebraMap ↥F E x) = algebraMap ↥F E x := by
    intro x
    have hx : (x : E) ∈ IntermediateField.fixedField H.topologicalClosure := x.2
    rw [IntermediateField.mem_fixedField_iff] at hx
    have := hx C hC_in_Hbar
    rw [hCapply] at this
    exact this
  let CF : Gal(E/↥F) := AlgEquiv.ofRingEquiv (f := c) hCFfix
  have hcent : ∀ h : Gal(E/↥F), CF * h = h * CF := by
    intro h
    have hh : (h.restrictScalars ℚ) ∈ F.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      show (AlgEquiv.restrictScalars ℚ h) x = x
      have := h.commutes ⟨x, hx⟩
      simpa using this
    rw [hF_fix] at hh
    have hCZ : C * (h.restrictScalars ℚ) = (h.restrictScalars ℚ) * C :=
      (Subgroup.mem_centralizer_iff.mp (hHbar_le_Z hh)) C (Set.mem_singleton C)
    apply AlgEquiv.ext
    intro x
    change c (h x) = h (c x)
    have hh2 := congrArg (fun (e : E ≃ₐ[ℚ] E) => e x) hCZ
    simpa [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply, hCapply] using hh2
  -- ## Part 2 : shrink the number field `↥F` and `E` into the universes of `hZ`
  haveI hsepFE : Algebra.IsSeparable ↥F E :=
    Algebra.isSeparable_tower_top_of_isSeparable (F := ℚ) (L := ↥F) (E := E)
  haveI hcountk : Countable k := Commons.NumberTheory.NumberField.countable
  haveI hcountE : Countable E :=
    Commons.FieldTheory.IsSepClosed.countable_of_isSepClosure (k := k) (E := E)
  -- ↥F injects into `k`, hence is countable
  have hpre : ∀ x : ↥F, ∃ y : k, algebraMap k E y = (x : E) := fun x => hF_sub x x.2
  let φ : ↥F → k := fun x => Classical.choose (hpre x)
  have hφ : ∀ x : ↥F, algebraMap k E (φ x) = (x : E) := fun x => Classical.choose_spec (hpre x)
  haveI hcountF : Countable ↥F := by
    refine Function.Injective.countable (f := φ) ?_
    intro x y hxy
    apply Subtype.ext
    rw [← hφ x, ← hφ y, hxy]
  -- `↥F` is a number field, via the preimage in `k`
  let Fk : Subfield k :=
    { carrier := {y : k | algebraMap k E y ∈ F}
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_mul]
        exact mul_mem hx hy
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        rw [map_one]
        exact one_mem F
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_add]
        exact add_mem hx hy
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        rw [map_zero]
        exact zero_mem F
      neg_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [map_neg]
        exact neg_mem hx
      inv_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [map_inv₀]
        exact inv_mem hx }
  haveI hNFk : NumberField ↥Fk := NumberField.of_subfield Fk
  let fk : ↥Fk →+* ↥F :=
    { toFun := fun y => ⟨algebraMap k E (y : k), y.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  have hfk_inj : Function.Injective fk := by
    intro x y hxy
    apply Subtype.ext
    show (x : k) = (y : k)
    apply (algebraMap k E).injective
    exact Subtype.ext_iff.mp hxy
  have hfk_surj : Function.Surjective fk := by
    intro x
    refine ⟨⟨φ x, ?_⟩, ?_⟩
    · show algebraMap k E (φ x) ∈ F
      rw [hφ x]
      exact x.2
    · apply Subtype.ext
      show algebraMap k E (φ x) = (x : E)
      rw [hφ x]
  let isoF : ↥Fk ≃+* ↥F := RingEquiv.ofBijective fk ⟨hfk_inj, hfk_surj⟩
  haveI hNFF : NumberField ↥F := NumberField.of_ringEquiv ↥Fk ↥F isoF
  haveI hsmallF : Small.{u₃} ↥F := inferInstance
  haveI hsmallE : Small.{u₄} E := inferInstance
  let F₀ : Type u₃ := Shrink.{u₃} ↥F
  let E₀ : Type u₄ := Shrink.{u₄} E
  let ρF : F₀ ≃+* ↥F := Shrink.ringEquiv ↥F
  let ρE : E₀ ≃+* E := Shrink.ringEquiv E
  haveI hChF₀ : CharZero F₀ :=
    charZero_of_injective_ringHom (f := (ρF.symm : ↥F →+* F₀)) (RingEquiv.injective ρF.symm)
  haveI hNF₀ : NumberField F₀ := NumberField.of_ringEquiv ↥F F₀ ρF.symm
  let algFE : F₀ →+* E₀ :=
    (ρE.symm : E →+* E₀).comp ((algebraMap ↥F E).comp (ρF : F₀ →+* ↥F))
  letI hAlgFE₀ : Algebra F₀ E₀ := algFE.toAlgebra
  have hcompat : ∀ x : F₀, ρE (algebraMap F₀ E₀ x) = algebraMap ↥F E (ρF x) := by
    intro x
    show ρE (algFE x) = algebraMap ↥F E (ρF x)
    simp [algFE]
  haveI hsscE₀ : IsSepClosed E₀ :=
    isSepClosed_of_ringEquiv_aux ρE.symm
  haveI hsepFE₀ : Algebra.IsSeparable F₀ E₀ :=
    Commons.FieldTheory.Galois.isSeparable_of_ringEquiv ρF ρE hcompat
  haveI hsscFE₀ : IsSepClosure F₀ E₀ := ⟨inferInstance, inferInstance⟩
  -- the transported automorphism
  have hc₀fix : ∀ x : F₀,
      (ρE.trans (c.trans ρE.symm)) (algebraMap F₀ E₀ x) = algebraMap F₀ E₀ x := by
    intro x
    show ρE.symm (c (ρE (algebraMap F₀ E₀ x))) = algebraMap F₀ E₀ x
    rw [hcompat x, hCFfix (ρF x), ← hcompat x, RingEquiv.symm_apply_apply]
  let c₀ : Gal(E₀/F₀) := AlgEquiv.ofRingEquiv (f := ρE.trans (c.trans ρE.symm)) hc₀fix
  have hcentral : ∀ h : Gal(E₀/F₀), c₀ * h = h * c₀ := by
    intro h
    have hh'fix : ∀ y : ↥F,
        (ρE.symm.trans (h.toRingEquiv.trans ρE)) (algebraMap ↥F E y) = algebraMap ↥F E y := by
      intro y
      have h1 : ρE (algebraMap F₀ E₀ (ρF.symm y)) = algebraMap ↥F E y := by
        rw [hcompat (ρF.symm y), RingEquiv.apply_symm_apply]
      have hy : ρE.symm (algebraMap ↥F E y) = algebraMap F₀ E₀ (ρF.symm y) := by
        rw [← h1, RingEquiv.symm_apply_apply]
      show ρE (h (ρE.symm (algebraMap ↥F E y))) = algebraMap ↥F E y
      rw [hy, h.commutes (ρF.symm y), hcompat (ρF.symm y), RingEquiv.apply_symm_apply]
    let h' : Gal(E/↥F) :=
      AlgEquiv.ofRingEquiv (f := ρE.symm.trans (h.toRingEquiv.trans ρE)) hh'fix
    have hcomm' : ∀ z : E, c (h' z) = h' (c z) := by
      have key := congrArg (fun (e : E ≃ₐ[↥F] E) => e) (hcent h')
      intro z
      have hh3 : CF (h' z) = h' (CF z) := by
        have := congrArg (fun (e : E ≃ₐ[↥F] E) => e z) (hcent h')
        simpa [AlgEquiv.mul_apply] using this
      exact hh3
    apply AlgEquiv.ext
    intro x
    show ρE.symm (c (ρE (h x))) = h (ρE.symm (c (ρE x)))
    have h1 : ρE (h x) = h' (ρE x) := by
      show ρE (h x) = ρE (h (ρE.symm (ρE x)))
      rw [RingEquiv.symm_apply_apply]
    have h2 : ∀ z : E, ρE.symm (h' z) = h (ρE.symm z) := by
      intro z
      show ρE.symm (ρE (h (ρE.symm z))) = h (ρE.symm z)
      rw [RingEquiv.symm_apply_apply]
    rw [h1, hcomm' (ρE x), h2]
  have hc₀_1 : c₀ = 1 := hZ F₀ E₀ c₀ hcentral
  have hfinal : ∀ y : E, c y = y := by
    intro y
    have hrule : ∀ x : E₀, ρE (c₀ x) = c (ρE x) := by
      intro x
      show ρE (ρE.symm (c (ρE x))) = c (ρE x)
      rw [RingEquiv.apply_symm_apply]
    have h0 : c₀ (ρE.symm y) = ρE.symm y := by
      have := congrArg (fun (e : Gal(E₀/F₀)) => e (ρE.symm y)) hc₀_1
      simpa using this
    calc c y = c (ρE (ρE.symm y)) := by rw [RingEquiv.apply_symm_apply]
      _ = ρE (c₀ (ρE.symm y)) := (hrule (ρE.symm y)).symm
      _ = ρE (ρE.symm y) := by rw [h0]
      _ = y := by rw [RingEquiv.apply_symm_apply]
  exact RingEquiv.ext hfinal

/-- **Centralizer triviality from triviality of the centres of absolute Galois groups.**

Let `E` be a separable closure of the number field `k`, and let `c` be a ring automorphism of `E`
which preserves the image of `k` and commutes with `Gal(E/k)` (conjugation by `c` is the identity
on `Gal(E/k)`).  Then `c = 1`, assuming the triviality of the centre of the absolute Galois group of
every number field (`hZ`, this is CoNF XII (12.1.6), in the form needed here).

Proof sketch.  Write `k' = (algebraMap k E).range ≅ k`; it is the fixed field of `Gal(E/k)`.
The hypothesis `hpres` and its version for `c⁻¹` (which also commutes with `Gal(E/k)`) show that
`c` restricts to a ring automorphism `δ` of `k'`, necessarily of finite order `n`.

* If `δ = 1`, then `c` is `k`-linear, i.e. `c ∈ Gal(E/k)`, and `c` commutes with all of
  `Gal(E/k)`, so `c = 1` by `hZ` applied to the number field `k`.
* If `δ ≠ 1`, let `F = (k')^δ` be the fixed field of `⟨δ⟩` in `k'`.  Then `k'/F` is Galois with
  group `⟨δ⟩` (Artin's theorem), the restriction map `H := Gal(E/F) → Gal(k'/F)` is surjective
  with kernel `Gal(E/k)`, so `H = ⋃_{i<n} c^i Gal(E/k)`, and since `c` commutes with `Gal(E/k)`
  and with itself, `c ∈ Z(H)`.  As `E` is a separable closure of the number field `F` (note
  `c` fixes `F` pointwise), `hZ` applied to `F` gives `Z(Gal(E/F)) = 1`, hence `c = 1` — a
  contradiction with `c|_{k'} = δ ≠ 1`.

Note on the proof.  The hypothesis `hZ` quantifies over number fields in universes `u₃` and `u₄`
that are independent of those of `k` and `E`, so it cannot be applied directly to a subfield of `E`.
The proof below therefore (i) produces a number field `F` (a subfield of `E`) with
`c ∈ Z(Gal(E/F))` (via the Krull topology and the infinite Galois correspondence), (ii) shrinks `F`
and `E` into the universes `u₃`, `u₄` of `hZ` and transports the algebraic structure along the
resulting equivalences, and (iii) applies `hZ` there. -/
theorem eq_one_of_preserves_and_centralizes {k E : Type*} [Field k] [Field E] [Algebra k E]
    [NumberField k] [IsSepClosure k E]
    (hZ : ∀ (F : Type*) [Field F] [NumberField F] (F' : Type*) [Field F'] [Algebra F F']
        [IsSepClosure F F'], ∀ c : Gal(F'/F), (∀ h : Gal(F'/F), c * h = h * c) → c = 1)
    (c : E ≃+* E)
    (hpres : ∀ x ∈ (algebraMap k E).range, c x ∈ (algebraMap k E).range)
    (hcomm : ∀ g : Gal(E/k), c.trans (g.toRingEquiv.trans c.symm) = g.toRingEquiv) :
    c = 1 :=
  eq_one_of_preserves_and_centralizes_aux hZ c hpres hcomm

end Commons.FieldTheory.Galois