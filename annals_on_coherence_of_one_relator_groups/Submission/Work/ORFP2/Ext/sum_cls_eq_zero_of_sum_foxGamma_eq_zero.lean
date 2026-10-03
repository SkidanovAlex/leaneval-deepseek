import Mathlib
import Submission.Work.ORFP2.ExtSetup
import Submission.Work.ORFP2.ExtGamma
import Submission.Work.ORFP2.Ext.ActDefs

namespace Work.ORFP2.Ext

open MonoidAlgebra

variable (k : Type*) [CommRing k] {n : ℕ} {G : Type*} [Group G]

/-- The weighted fibre sum: the part of `a` in the coset `φ ⁻¹' {c}`, conjugated by `sec c`. -/
noncomputable def wtFib (φ : FreeGroup (Fin n) →* G) (hφ : Function.Surjective φ) (c : G) :
    MonoidAlgebra k (FreeGroup (Fin n)) →ₗ[k] KerMod k φ :=
  (act k φ (sec φ hφ c)).comp (fibSum k φ hφ c)

lemma wtFib_apply (φ : FreeGroup (Fin n) →* G) (hφ : Function.Surjective φ) (c : G)
    (a : MonoidAlgebra k (FreeGroup (Fin n))) :
    wtFib k φ hφ c a = act k φ (sec φ hφ c) (fibSum k φ hφ c a) := rfl

lemma foxPush_apply (φ : FreeGroup (Fin n) →* G)
    (v : Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) (i : Fin n) :
    foxPush k φ v i = phiAlg k φ (v i) :=
  Finsupp.mapRange_apply

/-- `foxPush` as a `k`-linear map. -/
noncomputable def foxPushLM (φ : FreeGroup (Fin n) →* G) :
    (Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) →ₗ[k] (Fin n →₀ MonoidAlgebra k G) where
  toFun := foxPush k φ
  map_add' := foxPush_add k φ
  map_smul' t v := by
    conv_lhs => rw [← IsScalarTower.algebraMap_smul (MonoidAlgebra k (FreeGroup (Fin n))) t v]
    rw [show foxPush k φ ((algebraMap k (MonoidAlgebra k (FreeGroup (Fin n))) t) • v)
        = (algebraMap k (MonoidAlgebra k G) t) • foxPush k φ v from by
      rw [foxPush_smul, AlgHom.commutes]]
    exact IsScalarTower.algebraMap_smul (MonoidAlgebra k G) t (foxPush k φ v)

lemma nw_eq_self_of_mem_ker (φ : FreeGroup (Fin n) →* G) (hφ : Function.Surjective φ)
    {w : FreeGroup (Fin n)} (hw : w ∈ φ.ker) : nw φ hφ w = w := by
  rw [nw, MonoidHom.mem_ker.mp hw, sec_one, inv_one, one_mul]

lemma fibWeight_one_of_mem_ker (φ : FreeGroup (Fin n) →* G) (hφ : Function.Surjective φ)
    {w : FreeGroup (Fin n)} (hw : w ∈ φ.ker) :
    fibWeight k φ hφ 1 w = cls k φ ⟨w, hw⟩ := by
  rw [fibWeight_of_eq k φ hφ (MonoidHom.mem_ker.mpr hw)]
  congr 1
  exact Subtype.ext (nw_eq_self_of_mem_ker φ hφ hw)

lemma fibWeight_one_one (φ : FreeGroup (Fin n) →* G) (hφ : Function.Surjective φ) :
    fibWeight k φ hφ 1 (1 : FreeGroup (Fin n)) = 0 := by
  rw [fibWeight_of_eq k φ hφ (c := 1) (w := 1) (map_one φ)]
  rw [show (⟨nw φ hφ 1, nw_mem φ hφ 1⟩ : ↥(φ.ker)) = 1 from Subtype.ext (nw_one φ hφ),
    cls_one]

/-- The constant correction element. -/
noncomputable def deltaC (φ : FreeGroup (Fin n) →* G) (hφ : Function.Surjective φ)
    (c : G) (w : FreeGroup (Fin n)) : ↥(φ.ker) :=
  ⟨(sec φ hφ c)⁻¹ * sec φ hφ (c * (φ w)⁻¹) * sec φ hφ (φ w), by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, phi_sec]
    group⟩

lemma delta_eq_deltaC (φ : FreeGroup (Fin n) →* G) (hφ : Function.Surjective φ)
    {z w : FreeGroup (Fin n)} {c : G} (hz : φ z = c * (φ w)⁻¹) :
    delta φ hφ z w = deltaC φ hφ c w := by
  refine Subtype.ext ?_
  simp only [delta, deltaC, Subtype.coe_mk]
  have hzw : φ (z * w) = c := by rw [map_mul, hz]; group
  rw [hzw, hz]

theorem act_fibSum_mul_single_aux (φ : FreeGroup (Fin n) →* G) (hφ : Function.Surjective φ)
    {a : MonoidAlgebra k (FreeGroup (Fin n))} (ha : a ∈ Jspan k φ)
    (c : G) (w : FreeGroup (Fin n)) :
    act k φ (sec φ hφ c) (fibSum k φ hφ c (a * MonoidAlgebra.single w 1))
      = act k φ (sec φ hφ (c * (φ w)⁻¹)) (fibSum k φ hφ (c * (φ w)⁻¹) a) := by
  classical
  set c' := c * (φ w)⁻¹ with hc'
  set ρ : KerMod k φ := act k φ (sec φ hφ c) (cls k φ (deltaC φ hφ c w))
    + act k φ (sec φ hφ c) (cls k φ ⟨nw φ hφ w, nw_mem φ hφ w⟩) with hρ
  have hexp : a = ∑ z ∈ a.coeff.support, a.coeff z • MonoidAlgebra.single z 1 :=
    Work.ORFP2.eq_sum_smul_single k (FreeGroup (Fin n)) a
  have hmul : a * MonoidAlgebra.single w 1
      = ∑ z ∈ a.coeff.support, a.coeff z • MonoidAlgebra.single (z * w) 1 := by
    conv_lhs => rw [hexp]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z _
    rw [smul_mul_assoc, MonoidAlgebra.single_mul_single, mul_one]
  -- pointwise computation
  have hpt : ∀ z ∈ a.coeff.support,
      act k φ (sec φ hφ c) (fibWeight k φ hφ c (z * w))
        = act k φ (sec φ hφ c') (fibWeight k φ hφ c' z)
          + (if φ z = c' then ρ else 0) := by
    intro z _
    by_cases hz : φ z = c'
    · rw [if_pos hz]
      have hzw : φ (z * w) = c := by rw [map_mul, hz, hc']; group
      rw [fibWeight_of_eq k φ hφ hzw, fibWeight_of_eq k φ hφ hz]
      rw [cls_nw_mul k φ hφ z w, map_add, map_add, act_comp]
      rw [act_same_coset k φ (y := sec φ hφ c * (sec φ hφ (φ w))⁻¹)
        (y' := sec φ hφ c') ?_ (cls k φ ⟨nw φ hφ z, nw_mem φ hφ z⟩)]
      · rw [hρ, show delta φ hφ z w = deltaC φ hφ c w from delta_eq_deltaC φ hφ hz]
        abel
      · rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv, phi_sec]
        rw [hc']
        group
    · rw [if_neg hz]
      have hzw : φ (z * w) ≠ c := by
        intro hh
        apply hz
        have h2 : c' * φ w = c := by rw [hc']; group
        have h3 : φ z * φ w = c' * φ w := by rw [← map_mul, hh, h2]
        exact mul_right_cancel h3
      rw [fibWeight_of_ne k φ hφ hzw, fibWeight_of_ne k φ hφ hz, map_zero, map_zero, add_zero]
  -- assembly
  have hL : act k φ (sec φ hφ c) (fibSum k φ hφ c (a * MonoidAlgebra.single w 1))
      = ∑ z ∈ a.coeff.support, a.coeff z •
          (act k φ (sec φ hφ c) (fibWeight k φ hφ c (z * w))) := by
    rw [hmul, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [map_smul, fibSum_single, map_smul, one_smul]
  have hR : act k φ (sec φ hφ c') (fibSum k φ hφ c' a)
      = ∑ z ∈ a.coeff.support, a.coeff z •
          (act k φ (sec φ hφ c') (fibWeight k φ hφ c' z)) := by
    conv_lhs => rw [hexp]
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [map_smul, fibSum_single, map_smul, one_smul]
  rw [hL, hR]
  rw [show (∑ z ∈ a.coeff.support, a.coeff z •
        (act k φ (sec φ hφ c) (fibWeight k φ hφ c (z * w))))
      = ∑ z ∈ a.coeff.support, (a.coeff z •
          (act k φ (sec φ hφ c') (fibWeight k φ hφ c' z))
          + a.coeff z • (if φ z = c' then ρ else 0)) from by
    apply Finset.sum_congr rfl
    intro z hz
    rw [hpt z hz, smul_add]]
  rw [Finset.sum_add_distrib]
  rw [show (∑ z ∈ a.coeff.support, a.coeff z • (if φ z = c' then ρ else 0))
      = (∑ z ∈ a.coeff.support, (if φ z = c' then a.coeff z else 0)) • ρ from by
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : φ z = c'
    · rw [if_pos hz, if_pos hz]
    · rw [if_neg hz, if_neg hz, smul_zero, zero_smul]]
  have hmu : (∑ z ∈ a.coeff.support, (if φ z = c' then a.coeff z else 0)) = mu k φ c' a := by
    rw [mu_apply]
    apply Finset.sum_congr rfl
    intro z _
    by_cases h : φ z = c'
    · rw [if_pos h, muWeight_of_eq k φ h, mul_one]
    · rw [if_neg h, muWeight_of_ne k φ h, mul_zero]
  rw [hmu, mu_eq_zero_of_mem_Jspan k φ ha c', zero_smul, add_zero]

theorem sum_cls_eq_zero_of_sum_foxGamma_eq_zero (k : Type*) [CommRing k]
    (hbasis : FreeGroupAugIdealBasis k) {n : ℕ} {G : Type*} [Group G]
    (φ : FreeGroup (Fin n) →* G) (hφ : Function.Surjective φ)
    {ι : Type*} (s : Finset ι) (x : ι → ↥(φ.ker)) (c : ι → k)
    (h : ∑ i ∈ s, c i • foxGamma k hbasis n φ (x i) = 0) :
    ∑ i ∈ s, c i • cls k φ (x i) = 0 := by
  classical
  -- The element `ω = ∑ c_i D(x_i)` of `k[F]ⁿ`.
  set ω : Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n)) :=
    ∑ i ∈ s, c i • foxDelta k hbasis n (x i : FreeGroup (Fin n)) with hω
  have hpush : foxPush k φ ω = 0 := by
    rw [hω]
    change foxPushLM k φ (∑ i ∈ s, c i • foxDelta k hbasis n (x i : FreeGroup (Fin n))) = 0
    rw [map_sum]
    rw [show (∑ i ∈ s, foxPushLM k φ (c i • foxDelta k hbasis n (x i : FreeGroup (Fin n))))
        = ∑ i ∈ s, c i • foxGamma k hbasis n φ (x i) from by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      rfl]
    exact h
  have hmem : ∀ i : Fin n, ω i ∈ JJ k φ := by
    intro i
    have h1 : (foxPush k φ ω) i = 0 := by
      simpa using congrArg (fun v : Fin n →₀ MonoidAlgebra k G => v i) hpush
    show phiAlg k φ (ω i) = 0
    rw [← h1, foxPush_apply]
  have hJ : ∀ i : Fin n, ω i ∈ Jspan k φ := fun i => (mem_JJ_iff k φ hφ (ω i)).mp (hmem i)
  -- `z = Λ ω = ∑ c_i (x_i - 1)`
  have hZ : foxLambda k n ω
      = ∑ i ∈ s, c i • (MonoidAlgebra.single (x i : FreeGroup (Fin n)) 1 - 1) := by
    rw [hω, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show foxLambda k n (c i • foxDelta k hbasis n (x i : FreeGroup (Fin n)))
        = foxLambda k n ((algebraMap k (MonoidAlgebra k (FreeGroup (Fin n))) (c i)) •
            foxDelta k hbasis n (x i : FreeGroup (Fin n))) from by
          rw [IsScalarTower.algebraMap_smul]]
    rw [map_smul, foxLambda_foxDelta, IsScalarTower.algebraMap_smul]
  -- the various fibre sums of `z`
  have hfib1 : ∀ (y : ↥(φ.ker)),
      fibSum k φ hφ 1 (MonoidAlgebra.single (y : FreeGroup (Fin n)) 1) = cls k φ y := by
    intro y
    rw [fibSum_single, fibWeight_of_eq k φ hφ (c := 1) (w := (y : FreeGroup (Fin n)))
      (MonoidHom.mem_ker.mpr y.2), one_smul]
    congr 1
    exact Subtype.ext (nw_eq_self_of_mem_ker φ hφ y.2)
  have hfib0 : fibSum k φ hφ 1 (1 : MonoidAlgebra k (FreeGroup (Fin n))) = 0 := by
    rw [show (1 : MonoidAlgebra k (FreeGroup (Fin n))) = MonoidAlgebra.single 1 1 from
      MonoidAlgebra.one_def]
    rw [fibSum_single, fibWeight_one_one k φ hφ, smul_zero]
  have hZ3 : (∑ i ∈ s, c i • cls k φ (x i)) = fibSum k φ hφ 1 (foxLambda k n ω) := by
    rw [hZ, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, map_sub, hfib1 (x i), hfib0, sub_zero]
  have hzero : ∀ c' : G, c' ≠ 1 → wtFib k φ hφ c' (foxLambda k n ω) = 0 := by
    intro c' hc'
    have hfs : fibSum k φ hφ c' (foxLambda k n ω) = 0 := by
      rw [hZ, map_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [map_smul, map_sub]
      rw [show (1 : MonoidAlgebra k (FreeGroup (Fin n))) = MonoidAlgebra.single 1 1 from
        MonoidAlgebra.one_def]
      rw [fibSum_single, fibSum_single, one_smul, one_smul]
      have h1 : fibWeight k φ hφ c' (x i : FreeGroup (Fin n)) = 0 :=
        fibWeight_of_ne k φ hφ (by
          rw [MonoidHom.mem_ker.mp (x i).2]
          exact fun hh => hc' hh.symm)
      have h2 : fibWeight k φ hφ c' (1 : FreeGroup (Fin n)) = 0 :=
        fibWeight_of_ne k φ hφ (by rw [map_one]; exact fun hh => hc' hh.symm)
      rw [h1, h2, sub_zero, smul_zero]
    rw [wtFib_apply, hfs, map_zero]
  -- the finite set of cosets carrying the telescoping
  let Sset : Fin n → Finset G := fun i => (ω i).coeff.support.image (fun w => φ w)
  let T : Finset G := insert 1 ((Finset.univ.biUnion Sset) ∪
    (Finset.univ.biUnion (fun i : Fin n => (Sset i).image (fun c' => c' * φ (FreeGroup.of i)))))
  have hT1 : (1 : G) ∈ T := Finset.mem_insert.mpr (Or.inl rfl)
  have hST : ∀ i : Fin n, Sset i ⊆ T := by
    intro i c' hc'
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr (Or.inl
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hc'⟩))))
  have hSTg : ∀ i : Fin n, ∀ c' ∈ Sset i, c' * φ (FreeGroup.of i) ∈ T := by
    intro i c' hc'
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr (Or.inr
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
        Finset.mem_image.mpr ⟨c', hc', rfl⟩⟩))))
  have hvanish : ∀ i : Fin n, ∀ c' : G, c' ∉ Sset i → wtFib k φ hφ c' (ω i) = 0 := by
    intro i c' hc'
    have hfs : fibSum k φ hφ c' (ω i) = 0 := by
      apply fibSum_eq_zero_of_ne k φ hφ c'
      intro w hw hwc'
      exact hc' (Finset.mem_image.mpr ⟨w, hw, hwc'⟩)
    rw [wtFib_apply, hfs, map_zero]
  have hcrux : ∀ i : Fin n, ∀ c' : G,
      wtFib k φ hφ c' (ω i * MonoidAlgebra.single (FreeGroup.of i) 1)
        = wtFib k φ hφ (c' * (φ (FreeGroup.of i))⁻¹) (ω i) := by
    intro i c'
    rw [wtFib_apply, wtFib_apply]
    exact act_fibSum_mul_single_aux k φ hφ (hJ i) c' (FreeGroup.of i)
  have hreindex : ∀ i : Fin n,
      (∑ c' ∈ T, wtFib k φ hφ (c' * (φ (FreeGroup.of i))⁻¹) (ω i))
        = ∑ c' ∈ T, wtFib k φ hφ c' (ω i) := by
    intro i
    set U : Finset G := T.image (fun c'' => c'' * (φ (FreeGroup.of i))⁻¹) with hU
    have hUsum : (∑ c' ∈ U, wtFib k φ hφ c' (ω i))
        = ∑ c' ∈ T, wtFib k φ hφ (c' * (φ (FreeGroup.of i))⁻¹) (ω i) :=
      Finset.sum_image (fun a _ b _ hh => mul_right_cancel hh)
    have hsub : Sset i ⊆ U := by
      intro c' hc'
      refine Finset.mem_image.mpr ⟨c' * φ (FreeGroup.of i), ?_, ?_⟩
      · exact hSTg i c' hc'
      · rw [mul_inv_cancel_right]
    have hA : (∑ c' ∈ Sset i, wtFib k φ hφ c' (ω i))
        = ∑ c' ∈ U, wtFib k φ hφ c' (ω i) :=
      Finset.sum_subset hsub (fun x _ hxs => hvanish i x hxs)
    have hB : (∑ c' ∈ Sset i, wtFib k φ hφ c' (ω i))
        = ∑ c' ∈ T, wtFib k φ hφ c' (ω i) :=
      Finset.sum_subset (hST i) (fun x _ hxs => hvanish i x hxs)
    rw [← hUsum, ← hA, hB]
  have htel : ∑ c' ∈ T, wtFib k φ hφ c' (foxLambda k n ω) = 0 := by
    rw [show foxLambda k n ω = ∑ i ∈ ω.support,
        ω i * (MonoidAlgebra.single (FreeGroup.of i) 1 - 1) from foxLambda_apply k n ω]
    rw [show (∑ c' ∈ T, wtFib k φ hφ c' (∑ i ∈ ω.support,
          ω i * (MonoidAlgebra.single (FreeGroup.of i) 1 - 1)))
        = ∑ c' ∈ T, ∑ i ∈ ω.support,
            wtFib k φ hφ c' (ω i * (MonoidAlgebra.single (FreeGroup.of i) 1 - 1)) from by
      apply Finset.sum_congr rfl
      intro c' _
      rw [map_sum]]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    rw [mul_sub, mul_one]
    rw [show (∑ c' ∈ T, (wtFib k φ hφ c' (ω i * MonoidAlgebra.single (FreeGroup.of i) 1 - ω i)))
        = (∑ c' ∈ T, wtFib k φ hφ c' (ω i * MonoidAlgebra.single (FreeGroup.of i) 1))
          - ∑ c' ∈ T, wtFib k φ hφ c' (ω i) from by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun c' _ => map_sub (wtFib k φ hφ c') _ _)]
    rw [show (∑ c' ∈ T, wtFib k φ hφ c' (ω i * MonoidAlgebra.single (FreeGroup.of i) 1))
        = ∑ c' ∈ T, wtFib k φ hφ c' (ω i) from by
      rw [Finset.sum_congr rfl (fun c' _ => hcrux i c')]
      exact hreindex i]
    rw [sub_self]
  have hwt1 : wtFib k φ hφ 1 (foxLambda k n ω) = fibSum k φ hφ 1 (foxLambda k n ω) := by
    rw [wtFib_apply, sec_one, act_one]
  have hsum1 : ∑ c' ∈ T, wtFib k φ hφ c' (foxLambda k n ω)
      = wtFib k φ hφ 1 (foxLambda k n ω) := by
    apply Finset.sum_eq_single 1
    · intro b _ hb
      exact hzero b hb
    · intro h1
      exact absurd hT1 h1
  rw [hZ3, ← hwt1, ← hsum1]
  exact htel

end Work.ORFP2.Ext
