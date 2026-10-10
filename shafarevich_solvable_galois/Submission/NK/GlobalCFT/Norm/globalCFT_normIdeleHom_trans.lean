import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFT.Norm.NormTransAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped NumberField RestrictedProduct NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.Norm

/-- The infinite-place case of the transitivity of the idèlic norm. -/
theorem globalCFT_normIdeleFun_trans_infinite {K L M : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    (x : Idele M) (v : InfinitePlace K) :
    Idele.normIdeleFun K L (Idele.normIdeleHom L M x) (Place.ofInfinite v) =
      Idele.normIdeleFun K M x (Place.ofInfinite v) := by
  classical
  simp only [Idele.normIdeleFun_ofInfinite, Idele.normIdeleHom_apply]
  let Θ : InfinitePlace L → InfinitePlace M → (Place.localField K (Place.ofInfinite v))ˣ :=
    fun a b =>
      if ha : a ∈ Place.fiberInfinite (K := K) (L := L) v then
        (@Place.localNormInfinite K _ L _ _
            a v (liesOver_of_mem_fiberInfinite (K := K) (L := L) ha))
          (if hb : b ∈ Place.fiberInfinite (K := L) (L := M) a then
            (@Place.localNormInfinite L _ M _ _
              b a (liesOver_of_mem_fiberInfinite (K := L) (L := M) hb))
              (x (Place.ofInfinite b))
           else 1)
      else 1
  let H : InfinitePlace M → (Place.localField K (Place.ofInfinite v))ˣ :=
    fun b =>
      if hb : b ∈ Place.fiberInfinite (K := K) (L := M) v then
        (@Place.localNormInfinite K _ M _ _
          b v (liesOver_of_mem_fiberInfinite (K := K) (L := M) hb))
          (x (Place.ofInfinite b))
      else 1
  have hR : (∏ u ∈ (Place.fiberInfinite (K := K) (L := M) v).attach,
      (@Place.localNormInfinite K _ M _ _ u.1 v
        (liesOver_of_mem_fiberInfinite (K := K) (L := M) u.2)) (x (Place.ofInfinite u.1)))
      = ∏ b ∈ Place.fiberInfinite (K := K) (L := M) v, H b :=
    Finset.prod_attach_dite _ (fun b hb =>
      (@Place.localNormInfinite K _ M _ _ b v
        (liesOver_of_mem_fiberInfinite (K := K) (L := M) hb)) (x (Place.ofInfinite b)))
  have hA : (∏ w ∈ (Place.fiberInfinite (K := K) (L := L) v).attach,
      (@Place.localNormInfinite K _ L _ _ w.1 v
        (liesOver_of_mem_fiberInfinite (K := K) (L := L) w.2))
      (∏ b ∈ (Place.fiberInfinite (K := L) (L := M) w.1).attach,
        (@Place.localNormInfinite L _ M _ _ b.1 w.1
          (liesOver_of_mem_fiberInfinite (K := L) (L := M) b.2))
          (x (Place.ofInfinite b.1))))
      = ∏ w ∈ (Place.fiberInfinite (K := K) (L := L) v).attach,
          ∏ b ∈ Place.fiberInfinite (K := L) (L := M) w.1, Θ w.1 b := by
    refine Finset.prod_congr rfl (fun w _ => ?_)
    have h1 := Finset.prod_attach_dite (Place.fiberInfinite (K := L) (L := M) w.1)
      (fun b hb => (@Place.localNormInfinite L _ M _ _ b w.1
        (liesOver_of_mem_fiberInfinite (K := L) (L := M) hb)) (x (Place.ofInfinite b)))
    rw [h1, map_prod]
    refine Finset.prod_congr rfl (fun b hb => ?_)
    simp only [Θ, dif_pos w.2, dif_pos hb]
  have hunion : (Place.fiberInfinite (K := K) (L := L) v).biUnion
      (fun a => Place.fiberInfinite (K := L) (L := M) a)
      = Place.fiberInfinite (K := K) (L := M) v := by
    ext b
    rw [Finset.mem_biUnion, mem_fiberInfinite_tower (L := L) v b]
  have hdisj : (Place.fiberInfinite (K := K) (L := L) v : Set (InfinitePlace L)).PairwiseDisjoint
      (fun a => Place.fiberInfinite (K := L) (L := M) a) :=
    pairwiseDisjoint_fiberInfinite v
  have hB : (∏ w ∈ (Place.fiberInfinite (K := K) (L := L) v).attach,
        ∏ b ∈ Place.fiberInfinite (K := L) (L := M) w.1, Θ w.1 b)
      = ∏ a ∈ Place.fiberInfinite (K := K) (L := L) v,
        (if h : a ∈ Place.fiberInfinite (K := K) (L := L) v then
          ∏ b ∈ Place.fiberInfinite (K := L) (L := M) a, Θ a b else 1) :=
    Finset.prod_attach_dite _ (fun a _ => ∏ b ∈ Place.fiberInfinite (K := L) (L := M) a, Θ a b)
  have hC : (∏ a ∈ Place.fiberInfinite (K := K) (L := L) v,
        (if h : a ∈ Place.fiberInfinite (K := K) (L := L) v then
          ∏ b ∈ Place.fiberInfinite (K := L) (L := M) a, Θ a b else 1))
      = ∏ a ∈ Place.fiberInfinite (K := K) (L := L) v,
          ∏ b ∈ Place.fiberInfinite (K := L) (L := M) a, Θ a b := by
    refine Finset.prod_congr rfl (fun a ha => ?_)
    rw [dif_pos ha]
  have hD : (∏ a ∈ Place.fiberInfinite (K := K) (L := L) v,
          ∏ b ∈ Place.fiberInfinite (K := L) (L := M) a, Θ a b)
      = ∏ b ∈ Place.fiberInfinite (K := K) (L := M) v, H b := by
    refine Finset.prod_biUnion_congr hunion hdisj (fun a ha b hb => ?_)
    have hmem : b ∈ Place.fiberInfinite (K := K) (L := M) v :=
      (mem_fiberInfinite_tower (L := L) v b).mpr ⟨a, ha, hb⟩
    haveI h1 : a.LiesOver v := liesOver_of_mem_fiberInfinite (K := K) (L := L) ha
    haveI h2 : b.LiesOver a := liesOver_of_mem_fiberInfinite (K := L) (L := M) hb
    haveI h3 : b.LiesOver v := liesOver_of_mem_fiberInfinite (K := K) (L := M) hmem
    simp only [Θ, H, dif_pos ha, dif_pos hb, dif_pos hmem]
    exact localNormInfinite_trans (v := v) (w := a) (w' := b) (y := x (Place.ofInfinite b))
  rw [hA, hB, hC, hD, hR]

/-- The finite-place case of the transitivity of the idèlic norm. -/
theorem globalCFT_normIdeleFun_trans_finite {K L M : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    (x : Idele M) (Q : HeightOneSpectrum (𝓞 K)) :
    Idele.normIdeleFun K L (Idele.normIdeleHom L M x) (Place.ofFinite Q) =
      Idele.normIdeleFun K M x (Place.ofFinite Q) := by
  classical
  simp only [Idele.normIdeleFun_ofFinite, Idele.normIdeleHom_apply]
  let Θ : HeightOneSpectrum (𝓞 L) → HeightOneSpectrum (𝓞 M) →
      (Place.localField K (Place.ofFinite Q))ˣ :=
    fun a b =>
      if ha : a ∈ Place.primesOverFinite (K := K) (L := L) Q then
        (@Place.localNormFinite K _ _ L _ _ _
            a Q (liesOver_of_mem_primesOverFinite (K := K) (L := L) ha))
          (if hb : b ∈ Place.primesOverFinite (K := L) (L := M) a then
            (@Place.localNormFinite L _ _ M _ _ _
              b a (liesOver_of_mem_primesOverFinite (K := L) (L := M) hb))
              (x (Place.ofFinite b))
           else 1)
      else 1
  let H : HeightOneSpectrum (𝓞 M) → (Place.localField K (Place.ofFinite Q))ˣ :=
    fun b =>
      if hb : b ∈ Place.primesOverFinite (K := K) (L := M) Q then
        (@Place.localNormFinite K _ _ M _ _ _
          b Q (liesOver_of_mem_primesOverFinite (K := K) (L := M) hb))
          (x (Place.ofFinite b))
      else 1
  have hR : (∏ u ∈ (Place.primesOverFinite (K := K) (L := M) Q).attach,
      (@Place.localNormFinite K _ _ M _ _ _ u.1 Q
        (liesOver_of_mem_primesOverFinite (K := K) (L := M) u.2)) (x (Place.ofFinite u.1)))
      = ∏ b ∈ Place.primesOverFinite (K := K) (L := M) Q, H b :=
    Finset.prod_attach_dite _ (fun b hb =>
      (@Place.localNormFinite K _ _ M _ _ _ b Q
        (liesOver_of_mem_primesOverFinite (K := K) (L := M) hb)) (x (Place.ofFinite b)))
  have hA : (∏ w ∈ (Place.primesOverFinite (K := K) (L := L) Q).attach,
      (@Place.localNormFinite K _ _ L _ _ _ w.1 Q
        (liesOver_of_mem_primesOverFinite (K := K) (L := L) w.2))
      (∏ b ∈ (Place.primesOverFinite (K := L) (L := M) w.1).attach,
        (@Place.localNormFinite L _ _ M _ _ _ b.1 w.1
          (liesOver_of_mem_primesOverFinite (K := L) (L := M) b.2))
          (x (Place.ofFinite b.1))))
      = ∏ w ∈ (Place.primesOverFinite (K := K) (L := L) Q).attach,
          ∏ b ∈ Place.primesOverFinite (K := L) (L := M) w.1, Θ w.1 b := by
    refine Finset.prod_congr rfl (fun w _ => ?_)
    have h1 := Finset.prod_attach_dite (Place.primesOverFinite (K := L) (L := M) w.1)
      (fun b hb => (@Place.localNormFinite L _ _ M _ _ _ b w.1
        (liesOver_of_mem_primesOverFinite (K := L) (L := M) hb)) (x (Place.ofFinite b)))
    rw [h1, map_prod]
    refine Finset.prod_congr rfl (fun b hb => ?_)
    simp only [Θ, dif_pos w.2, dif_pos hb]
  have hunion : (Place.primesOverFinite (K := K) (L := L) Q).biUnion
      (fun a => Place.primesOverFinite (K := L) (L := M) a)
      = Place.primesOverFinite (K := K) (L := M) Q := by
    ext b
    rw [Finset.mem_biUnion, mem_primesOverFinite_tower (L := L) Q b]
  have hdisj :
      (Place.primesOverFinite (K := K) (L := L) Q : Set (HeightOneSpectrum (𝓞 L))).PairwiseDisjoint
        (fun a => Place.primesOverFinite (K := L) (L := M) a) :=
    pairwiseDisjoint_primesOverFinite Q
  have hB : (∏ w ∈ (Place.primesOverFinite (K := K) (L := L) Q).attach,
        ∏ b ∈ Place.primesOverFinite (K := L) (L := M) w.1, Θ w.1 b)
      = ∏ a ∈ Place.primesOverFinite (K := K) (L := L) Q,
        (if h : a ∈ Place.primesOverFinite (K := K) (L := L) Q then
          ∏ b ∈ Place.primesOverFinite (K := L) (L := M) a, Θ a b else 1) :=
    Finset.prod_attach_dite _ (fun a _ => ∏ b ∈ Place.primesOverFinite (K := L) (L := M) a, Θ a b)
  have hC : (∏ a ∈ Place.primesOverFinite (K := K) (L := L) Q,
        (if h : a ∈ Place.primesOverFinite (K := K) (L := L) Q then
          ∏ b ∈ Place.primesOverFinite (K := L) (L := M) a, Θ a b else 1))
      = ∏ a ∈ Place.primesOverFinite (K := K) (L := L) Q,
          ∏ b ∈ Place.primesOverFinite (K := L) (L := M) a, Θ a b := by
    refine Finset.prod_congr rfl (fun a ha => ?_)
    rw [dif_pos ha]
  have hD : (∏ a ∈ Place.primesOverFinite (K := K) (L := L) Q,
          ∏ b ∈ Place.primesOverFinite (K := L) (L := M) a, Θ a b)
      = ∏ b ∈ Place.primesOverFinite (K := K) (L := M) Q, H b := by
    refine Finset.prod_biUnion_congr hunion hdisj (fun a ha b hb => ?_)
    have hmem : b ∈ Place.primesOverFinite (K := K) (L := M) Q :=
      (mem_primesOverFinite_tower (L := L) Q b).mpr ⟨a, ha, hb⟩
    haveI h1 : a.asIdeal.LiesOver Q.asIdeal :=
      liesOver_of_mem_primesOverFinite (K := K) (L := L) ha
    haveI h2 : b.asIdeal.LiesOver a.asIdeal :=
      liesOver_of_mem_primesOverFinite (K := L) (L := M) hb
    haveI h3 : b.asIdeal.LiesOver Q.asIdeal :=
      liesOver_of_mem_primesOverFinite (K := K) (L := M) hmem
    simp only [Θ, H, dif_pos ha, dif_pos hb, dif_pos hmem]
    exact localNormFinite_trans (K := K) (L := L) (M := M) Q a b h1 h2 h3
      (x (Place.ofFinite b))
  rw [hA, hB, hC, hD, hR]

/-- **Transitivity of the idèlic norm**: for a tower `M / L / K` of number fields, the idèlic norm
`N_{M/K}` is the composite of `N_{L/K}` and `N_{M/L}`. -/
theorem globalCFT_normIdeleHom_trans {K L M : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [FiniteDimensional K L] [FiniteDimensional L M]
    [FiniteDimensional K M] :
    (NK.GlobalCFT.Idele.normIdeleHom K L).comp (NK.GlobalCFT.Idele.normIdeleHom L M) =
      NK.GlobalCFT.Idele.normIdeleHom K M := by
  apply MonoidHom.ext
  intro x
  apply Idele.ext
  intro v
  cases v with
  | inl v =>
      simpa only [MonoidHom.comp_apply, Idele.normIdeleHom_apply] using
        globalCFT_normIdeleFun_trans_infinite (L := L) x v
  | inr Q =>
      simpa only [MonoidHom.comp_apply, Idele.normIdeleHom_apply] using
        globalCFT_normIdeleFun_trans_finite (L := L) x Q

end NK.GlobalCFT.Norm
