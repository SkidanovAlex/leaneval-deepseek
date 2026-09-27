import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.BallKFrame
import Submission.Work.KT.bott_aux
import Submission.Work.KT.bott_geom
import Submission.Work.KT.ext_product
import Submission.Work.KT.fund_product

namespace Work.KT

open Matrix

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

/-! ## Pointwise computations for the two slice maps -/

section Slices

variable (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [ProperSpace W]

lemma ba_prFst_pairPtC (y0W : Ball W) (hW : y0W ∈ bdry W) (x : Ball V) :
    prFst V W (pairPtC V W y0W hW x) = x := Subtype.ext rfl

lemma ba_prSnd_pairPtC (y0W : Ball W) (hW : y0W ∈ bdry W) (x : Ball V) :
    prSnd V W (pairPtC V W y0W hW x) = y0W := Subtype.ext rfl

lemma ba_prFst_pairPtD (y0V : Ball V) (hV : y0V ∈ bdry V) (y : Ball W) :
    prFst V W (pairPtD V W y0V hV y) = y0V := Subtype.ext rfl

lemma ba_prSnd_pairPtD (y0V : Ball V) (hV : y0V ∈ bdry V) (y : Ball W) :
    prSnd V W (pairPtD V W y0V hV y) = y := Subtype.ext rfl

lemma ba_sliceV_comp_pullFst (y0W : Ball W) (hW : y0W ∈ bdry W) :
    (sliceV V W y0W hW).comp (pullFst V W) = AlgHom.id ℂ (Kpair V) := by
  apply AlgHom.ext
  intro g
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  show (g : C(Ball V, ℂ)) (prFst V W (pairPtC V W y0W hW x)) = (g : C(Ball V, ℂ)) x
  rw [ba_prFst_pairPtC]

lemma ba_sliceV_comp_pullSnd (y0W : Ball W) (hW : y0W ∈ bdry W) :
    (sliceV V W y0W hW).comp (pullSnd V W)
      = (Algebra.ofId ℂ (Kpair V)).comp (augPair W y0W) := by
  apply AlgHom.ext
  intro t
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  show (t : C(Ball W, ℂ)) (prSnd V W (pairPtC V W y0W hW x)) = (t : C(Ball W, ℂ)) y0W
  rw [ba_prSnd_pairPtC]

lemma ba_sliceW_comp_pullSnd (y0V : Ball V) (hV : y0V ∈ bdry V) :
    (sliceW V W y0V hV).comp (pullSnd V W) = AlgHom.id ℂ (Kpair W) := by
  apply AlgHom.ext
  intro t
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  show (t : C(Ball W, ℂ)) (prSnd V W (pairPtD V W y0V hV y)) = (t : C(Ball W, ℂ)) y
  rw [ba_prSnd_pairPtD]

lemma ba_sliceW_comp_pullFst (y0V : Ball V) (hV : y0V ∈ bdry V) :
    (sliceW V W y0V hV).comp (pullFst V W)
      = (Algebra.ofId ℂ (Kpair W)).comp (augPair V y0V) := by
  apply AlgHom.ext
  intro g
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  show (g : C(Ball V, ℂ)) (prFst V W (pairPtD V W y0V hV y)) = (g : C(Ball V, ℂ)) y0V
  rw [ba_prFst_pairPtD]

end Slices

section SmashSlices

variable (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [ProperSpace W]

lemma ba_sliceV_comp_smashIncl (y0W : Ball W) (hW : y0W ∈ bdry W)
    (y0 : Ball (V × W)) (hy0 : y0 ∈ bdry (V × W)) :
    (sliceV V W y0W hW).comp (smashIncl V W)
      = (Algebra.ofId ℂ (Kpair V)).comp (augPair (V × W) y0) := by
  apply AlgHom.ext
  intro g
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  show (g : C(Ball (V × W), ℂ)) (pairPtC V W y0W hW x) = (g : C(Ball (V × W), ℂ)) y0
  exact g.2 _ (pairPtC_mem_bdry V W y0W hW x) _ hy0

lemma ba_sliceW_comp_smashIncl (y0V : Ball V) (hV : y0V ∈ bdry V)
    (y0 : Ball (V × W)) (hy0 : y0 ∈ bdry (V × W)) :
    (sliceW V W y0V hV).comp (smashIncl V W)
      = (Algebra.ofId ℂ (Kpair W)).comp (augPair (V × W) y0) := by
  apply AlgHom.ext
  intro g
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  show (g : C(Ball (V × W), ℂ)) (pairPtD V W y0V hV y) = (g : C(Ball (V × W), ℂ)) y0
  exact g.2 _ (pairPtD_mem_bdry V W y0V hV y) _ hy0

end SmashSlices

/-! ## The Bott suspension lemma -/

/-- **Bott periodicity (suspension) on reduced `K`-theory**: for a two-dimensional `W`, the
external product with a generator `H` of the reduced group of `Kpair W` is an isomorphism from the
reduced group of `Kpair V` onto the reduced group of `Kpair (V × W)` (both groups being the kernels
of the augmentations).  `V` is assumed nonzero-dimensional (otherwise the map is `0 → K̃(S²)`).
The intended proof uses `Submission.Work.KT.ext_product` (import it once it builds) for the
external product `μx` and its injectivity on reduced classes, and `Submission.Work.KT.BallKFrame`
for `Xq`/`prodIso`/`sliceV`, together with `fund_product` applied to `X = Xq V`. -/
theorem bott_susp (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (y0V : Ball V) (hV : y0V ∈ bdry V) (y0W : Ball W) (hW : y0W ∈ bdry W)
    (y0 : Ball (V × W)) (hy0 : y0 ∈ bdry (V × W))
    (hVd : 1 ≤ Module.finrank ℝ V) (hWd : Module.finrank ℝ W = 2)
    (H : K0 (Kpair W)) (hH0 : K0.mapA (augPair W y0W) H = 0)
    (hH1 : ∀ k : ℤ, k • H = 0 → k = 0)
    (hH2 : ∀ z, K0.mapA (augPair W y0W) z = 0 → ∃ k : ℤ, z = k • H)
    (μx : K0 (Kpair V) →+ K0 (Kpair W) →+ K0 (Kpair (V × W)))
    (hμx : IsExtProd V W y0V y0W y0 μx) :
    (∀ z, K0.mapA (augPair (V × W) y0) z = 0 →
        ∃ s, K0.mapA (augPair V y0V) s = 0 ∧ μx s H = z) ∧
    (∀ s t, K0.mapA (augPair V y0V) s = 0 → K0.mapA (augPair V y0V) t = 0 →
        μx s H = μx t H → s = t) := by
  classical
  haveI : ProperSpace V := FiniteDimensional.proper ℝ V
  haveI : ProperSpace W := FiniteDimensional.proper ℝ W
  -- ## the geometry: the transport of `fund_product` to the pair `(V, W)`
  obtain ⟨Γ, EW, hΓfst, hΓsnd⟩ := ba_prodAlgCM V W hWd
  let Γa : prodAlg V W →ₐ[ℂ] C(Xq V × S2, ℂ) := Γ.toAlgHom
  let Γs : C(Xq V × S2, ℂ) →ₐ[ℂ] prodAlg V W := Γ.symm.toAlgHom
  let EWs : C(S2, ℂ) →ₐ[ℂ] Kpair W := EW.symm.toAlgHom
  have hΓfst' : Γa.comp (pullFst V W)
      = (pullAlg (ContinuousMap.fst : C(Xq V × S2, Xq V))).comp (qIso V).toAlgHom := hΓfst
  have hΓsnd' : Γa.comp (pullSnd V W)
      = (pullAlg (ContinuousMap.snd : C(Xq V × S2, S2))).comp EW.toAlgHom := hΓsnd
  have hcommP : ∀ x y : prodAlg V W, x * y = y * x := fun x y => by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    simp only [Subalgebra.coe_mul, ContinuousMap.mul_apply]
    exact mul_comm _ _
  have hcommV : ∀ x y : Kpair V, x * y = y * x := fun x y => by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    simp only [Subalgebra.coe_mul, ContinuousMap.mul_apply]
    exact mul_comm _ _
  have hcommW : ∀ x y : Kpair W, x * y = y * x := fun x y => by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    simp only [Subalgebra.coe_mul, ContinuousMap.mul_apply]
    exact mul_comm _ _
  -- ## products on the four algebras
  obtain ⟨μfp, hμfp⟩ := ba_exists_isK0Mul (C(Xq V × S2, ℂ)) (fun x y => mul_comm x y)
  obtain ⟨μP, hμP⟩ := ba_exists_isK0Mul (prodAlg V W) hcommP
  obtain ⟨μV, hμV⟩ := ba_exists_isK0Mul (Kpair V) hcommV
  obtain ⟨μW, hμW⟩ := ba_exists_isK0Mul (Kpair W) hcommW
  -- ## the transported Hopf class, and its reduction
  let H' : K0 (Kpair W) := K0.mapA EWs (cls hopfIdem)
  let r0 : K0 ℂ := K0.mapA (augPair W y0W) H'
  let Hr : K0 (Kpair W) := H' - K0.mapA (Algebra.ofId ℂ (Kpair W)) r0
  have hHr : K0.mapA (augPair W y0W) Hr = 0 := ba_reduced_sub_const (augPair W y0W) H'
  obtain ⟨m, hm⟩ := hH2 Hr hHr
  -- ## the elementary slice computations, at the level of `K₀`
  have hV_of_fst : ∀ x : K0 (Kpair V),
      K0.mapA (sliceV V W y0W hW) (K0.mapA (pullFst V W) x) = x := by
    intro x
    rw [ba_mapA_comp_apply (pullFst V W) (sliceV V W y0W hW) x,
      ba_sliceV_comp_pullFst V W y0W hW, ba_mapA_id_apply]
  have hV_of_snd : ∀ t : K0 (Kpair W),
      K0.mapA (sliceV V W y0W hW) (K0.mapA (pullSnd V W) t)
        = K0.mapA (Algebra.ofId ℂ (Kpair V)) (K0.mapA (augPair W y0W) t) := by
    intro t
    rw [ba_mapA_comp_apply (pullSnd V W) (sliceV V W y0W hW) t,
      ba_sliceV_comp_pullSnd V W y0W hW,
      ba_mapA_comp_apply (augPair W y0W) (Algebra.ofId ℂ (Kpair V)) t]
  have hW_of_snd : ∀ t : K0 (Kpair W),
      K0.mapA (sliceW V W y0V hV) (K0.mapA (pullSnd V W) t) = t := by
    intro t
    rw [ba_mapA_comp_apply (pullSnd V W) (sliceW V W y0V hV) t,
      ba_sliceW_comp_pullSnd V W y0V hV, ba_mapA_id_apply]
  have hW_of_fst : ∀ x : K0 (Kpair V),
      K0.mapA (sliceW V W y0V hV) (K0.mapA (pullFst V W) x)
        = K0.mapA (Algebra.ofId ℂ (Kpair W)) (K0.mapA (augPair V y0V) x) := by
    intro x
    rw [ba_mapA_comp_apply (pullFst V W) (sliceW V W y0V hV) x,
      ba_sliceW_comp_pullFst V W y0V hV,
      ba_mapA_comp_apply (augPair V y0V) (Algebra.ofId ℂ (Kpair W)) x]
  have hV_of_smash : ∀ z : K0 (Kpair (V × W)),
      K0.mapA (sliceV V W y0W hW) (K0.mapA (smashIncl V W) z)
        = K0.mapA (Algebra.ofId ℂ (Kpair V)) (K0.mapA (augPair (V × W) y0) z) := by
    intro z
    rw [ba_mapA_comp_apply (smashIncl V W) (sliceV V W y0W hW) z,
      ba_sliceV_comp_smashIncl V W y0W hW y0 hy0,
      ba_mapA_comp_apply (augPair (V × W) y0) (Algebra.ofId ℂ (Kpair V)) z]
  have hW_of_smash : ∀ z : K0 (Kpair (V × W)),
      K0.mapA (sliceW V W y0V hV) (K0.mapA (smashIncl V W) z)
        = K0.mapA (Algebra.ofId ℂ (Kpair W)) (K0.mapA (augPair (V × W) y0) z) := by
    intro z
    rw [ba_mapA_comp_apply (smashIncl V W) (sliceW V W y0V hV) z,
      ba_sliceW_comp_smashIncl V W y0V hV y0 hy0,
      ba_mapA_comp_apply (augPair (V × W) y0) (Algebra.ofId ℂ (Kpair W)) z]
  -- ## naturality of the products under the slice maps
  have hnatV : ∀ x y : K0 (prodAlg V W),
      K0.mapA (sliceV V W y0W hW) (μP x y)
        = μV (K0.mapA (sliceV V W y0W hW) x) (K0.mapA (sliceV V W y0W hW) y) :=
    fun x y => ba_k0_mul_natural (prodAlg V W) (Kpair V)
      (sliceV V W y0W hW).toRingHom μP μV hcommP hμP hμV x y
  have hnatW : ∀ x y : K0 (prodAlg V W),
      K0.mapA (sliceW V W y0V hV) (μP x y)
        = μW (K0.mapA (sliceW V W y0V hV) x) (K0.mapA (sliceW V W y0V hV) y) :=
    fun x y => ba_k0_mul_natural (prodAlg V W) (Kpair W)
      (sliceW V W y0V hV).toRingHom μP μW hcommP hμP hμW x y
  have hnatF : ∀ x y : K0 (Kpair V),
      K0.mapA (pullFst V W) (μV x y)
        = μP (K0.mapA (pullFst V W) x) (K0.mapA (pullFst V W) y) :=
    fun x y => ba_k0_mul_natural (Kpair V) (prodAlg V W) (pullFst V W).toRingHom
      μV μP hcommV hμV hμP x y
  have hnatS : ∀ x y : K0 (Kpair W),
      K0.mapA (pullSnd V W) (μW x y)
        = μP (K0.mapA (pullSnd V W) x) (K0.mapA (pullSnd V W) y) :=
    fun x y => ba_k0_mul_natural (Kpair W) (prodAlg V W) (pullSnd V W).toRingHom
      μW μP hcommW hμW hμP x y
  -- ## the transport of `fund_product` to the pair `(V, W)`
  have hΓpush_fst : ∀ x : K0 (Kpair V), K0.mapA Γa (K0.mapA (pullFst V W) x)
        = K0.mapA (pullAlg (ContinuousMap.fst : C(Xq V × S2, Xq V)))
            (K0.mapA (qIso V).toAlgHom x) := by
    intro x
    rw [ba_mapA_comp_apply (pullFst V W) Γa x, hΓfst']
    exact (ba_mapA_comp_apply (qIso V).toAlgHom
      (pullAlg (ContinuousMap.fst : C(Xq V × S2, Xq V))) x).symm
  have hEW : K0.mapA EW.toAlgHom (K0.mapA EWs (cls hopfIdem)) = cls hopfIdem :=
    ba_mapA_apply_symm EW (cls hopfIdem)
  have hΓpull_snd : K0.mapA Γa (K0.mapA (pullSnd V W) H')
      = K0.mapA (pullAlg (ContinuousMap.snd : C(Xq V × S2, S2))) (cls hopfIdem) := by
    rw [ba_mapA_comp_apply (pullSnd V W) Γa H', hΓsnd',
      ← ba_mapA_comp_apply EW.toAlgHom (pullAlg (ContinuousMap.snd : C(Xq V × S2, S2))) H',
      hEW]
  have hconj : ∀ x y : K0 (prodAlg V W), K0.mapA Γs (μfp (K0.mapA Γa x) (K0.mapA Γa y))
      = μP x y := fun x y => (ba_conjMul_eq Γ hcommP μP hμP μfp hμfp x y).symm
  -- ## the bijection `Φ`
  let fp : K0 C(Xq V, ℂ) × K0 C(Xq V, ℂ) → K0 C(Xq V × S2, ℂ) := fun ab =>
    K0.mapA (pullAlg (ContinuousMap.fst : C(Xq V × S2, Xq V))) ab.1 +
      μfp (K0.mapA (pullAlg (ContinuousMap.fst : C(Xq V × S2, Xq V))) ab.2)
        (K0.mapA (pullAlg (ContinuousMap.snd : C(Xq V × S2, S2))) (cls hopfIdem))
  have hfp : Function.Bijective fp := fund_product (Xq V) μfp hμfp
  let qp : K0 (Kpair V) × K0 (Kpair V) → K0 C(Xq V, ℂ) × K0 C(Xq V, ℂ) := fun ab =>
    (K0.mapA (qIso V).toAlgHom ab.1, K0.mapA (qIso V).toAlgHom ab.2)
  have hqp : Function.Bijective qp := by
    constructor
    · rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
      simp only [qp, Prod.mk.injEq] at h
      obtain ⟨e1, e2⟩ := h
      exact Prod.ext (ba_mapA_injective (qIso V) e1) (ba_mapA_injective (qIso V) e2)
    · rintro ⟨c, d⟩
      exact ⟨(K0.mapA (qIso V).symm.toAlgHom c, K0.mapA (qIso V).symm.toAlgHom d), by
        simp only [qp, ba_mapA_apply_symm]⟩
  let F : K0 (Kpair V) × K0 (Kpair V) → K0 C(Xq V × S2, ℂ) := fun ab => fp (qp ab)
  have hF : Function.Bijective F := hfp.comp hqp
  -- ## `Φ` has the shape required by the theorem
  have hΦeq : ∀ ab : K0 (Kpair V) × K0 (Kpair V), K0.mapA Γs (F ab)
      = K0.mapA (pullFst V W) ab.1
        + μP (K0.mapA (pullFst V W) ab.2) (K0.mapA (pullSnd V W) H') := by
    rintro ⟨a, b⟩
    simp only [F, fp, qp]
    rw [map_add]
    congr 1
    · rw [ba_mapA_comp_apply (qIso V).toAlgHom
          (pullAlg (ContinuousMap.fst : C(Xq V × S2, Xq V))) a, ← hΓfst',
        ← ba_mapA_comp_apply (pullFst V W) Γa a, ba_mapA_symm_apply]
    · rw [← hΓpush_fst b, ← hΓpull_snd, hconj]
  let Φ : K0 (Kpair V) × K0 (Kpair V) → K0 (prodAlg V W) := fun ab =>
    K0.mapA (pullFst V W) ab.1
      + μP (K0.mapA (pullFst V W) ab.2) (K0.mapA (pullSnd V W) H')
  have hΦeq' : ∀ ab, K0.mapA Γs (F ab) = Φ ab := fun ab => hΦeq ab
  have hΦ : Function.Bijective Φ := by
    have hinj : Function.Injective (K0.mapA Γs) := ba_mapA_injective Γ.symm
    constructor
    · intro ab ab' hab
      refine hF.1 (hinj ?_)
      rw [hΦeq' ab, hΦeq' ab', hab]
    · intro z
      obtain ⟨w, hw⟩ := hF.2 (K0.mapA Γa z)
      refine ⟨w, ?_⟩
      rw [← hΦeq' w, hw, ba_mapA_symm_apply]
  -- ## the two consequences of `ext_product`
  have hsmash_inj : ∀ w : K0 (Kpair (V × W)),
      K0.mapA (augPair (V × W) y0) w = 0 → K0.mapA (smashIncl V W) w = 0 → w = 0 :=
    (ext_product V W y0V hV y0W hW y0 hy0).2
  -- ## the constants
  have hH'split : H' = Hr + K0.mapA (Algebra.ofId ℂ (Kpair W)) r0 := by
    simp only [Hr]
    abel
  have hH'split_pull : K0.mapA (pullSnd V W) H'
      = K0.mapA (pullSnd V W) Hr + K0.mapA (Algebra.ofId ℂ (prodAlg V W)) r0 := by
    rw [hH'split, map_add, ba_const_natural (pullSnd V W) r0]
  have hHr_mul : K0.mapA (pullSnd V W) Hr = m • K0.mapA (pullSnd V W) H := by
    rw [hm, map_zsmul]
  have hmul : ∀ (x y : K0 (prodAlg V W)) (k : ℤ), μP (k • x) y = k • μP x y := by
    intro x y k
    rw [map_zsmul]
    rfl
  have hmul2 : ∀ (x y : K0 (prodAlg V W)) (k : ℤ), μP x (k • y) = k • μP x y :=
    fun x y k => map_zsmul (μP x) k y
  -- ## surjectivity
  constructor
  · intro z hz
    obtain ⟨ab, hab⟩ := hΦ.2 (K0.mapA (smashIncl V W) z)
    obtain ⟨a, b⟩ := ab
    -- slice at `D_V × {y0W}`: the first coordinate vanishes
    have hzV : K0.mapA (sliceV V W y0W hW) (K0.mapA (smashIncl V W) z) = 0 := by
      rw [hV_of_smash z, hz, map_zero]
    have hslice : a + μV b (K0.mapA (Algebra.ofId ℂ (Kpair V)) r0) = 0 := by
      have h := hzV
      rw [← hab] at h
      simp only [Φ] at h
      rw [map_add, hV_of_fst a, hnatV, hV_of_fst b, hV_of_snd H'] at h
      exact h
    have ha : a = -μV b (K0.mapA (Algebra.ofId ℂ (Kpair V)) r0) :=
      eq_neg_of_add_eq_zero_left hslice
    -- consequently the external product with `Hr` already computes `smashIncl z`
    have hz1 : μP (K0.mapA (pullFst V W) b) (K0.mapA (pullSnd V W) Hr)
        = K0.mapA (smashIncl V W) z := by
      rw [← hab]
      simp only [Φ]
      rw [ha, map_neg, hnatF, ba_const_natural (pullFst V W) r0, hH'split_pull, map_add]
      abel
    -- slice at `{y0V} × D_W`: the reduced part of the second coordinate multiplies `H` to zero
    have hzW : K0.mapA (sliceW V W y0V hV) (K0.mapA (smashIncl V W) z) = 0 := by
      rw [hW_of_smash z, hz, map_zero]
    have hsliceW : μW (K0.mapA (Algebra.ofId ℂ (Kpair W)) (K0.mapA (augPair V y0V) b)) Hr
        = 0 := by
      have h := hzW
      rw [← hz1, hnatW, hW_of_fst b, hW_of_snd Hr] at h
      exact h
    have hb0 : m • μW (K0.mapA (Algebra.ofId ℂ (Kpair W)) (K0.mapA (augPair V y0V) b)) H
        = 0 := by
      have h := hsliceW
      rw [hm, map_zsmul] at h
      exact h
    -- the reduced part of the second coordinate
    let b'' : K0 (Kpair V) := b - K0.mapA (Algebra.ofId ℂ (Kpair V)) (K0.mapA (augPair V y0V) b)
    have hb'' : K0.mapA (augPair V y0V) b'' = 0 := ba_reduced_sub_const (augPair V y0V) b
    have hb_split : b = b'' + K0.mapA (Algebra.ofId ℂ (Kpair V)) (K0.mapA (augPair V y0V) b) := by
      simp only [b'']
      abel
    -- the constant correction vanishes
    have hkill : μP (K0.mapA (pullFst V W) (K0.mapA (Algebra.ofId ℂ (Kpair V))
        (K0.mapA (augPair V y0V) b))) (K0.mapA (pullSnd V W) Hr) = 0 := by
      rw [ba_const_natural (pullFst V W) _]
      rw [hHr_mul, hmul2]
      rw [show μP (K0.mapA (Algebra.ofId ℂ (prodAlg V W)) (K0.mapA (augPair V y0V) b))
            (K0.mapA (pullSnd V W) H)
          = K0.mapA (pullSnd V W)
              (μW (K0.mapA (Algebra.ofId ℂ (Kpair W)) (K0.mapA (augPair V y0V) b)) H) from by
        rw [← ba_const_natural (pullSnd V W) (K0.mapA (augPair V y0V) b), ← hnatS]]
      rw [← map_zsmul, hb0, map_zero]
    have hz2 : μP (K0.mapA (pullFst V W) b'') (K0.mapA (pullSnd V W) Hr)
        = K0.mapA (smashIncl V W) z := by
      rw [← hz1]
      conv_rhs => rw [hb_split]
      rw [map_add, AddMonoidHom.map_add, AddMonoidHom.add_apply, hkill, add_zero]
    -- the class `m • b''` does the job
    have hz1' : μP (K0.mapA (pullFst V W) (m • b'')) (K0.mapA (pullSnd V W) H)
        = K0.mapA (smashIncl V W) z := by
      rw [← hz2]
      rw [map_zsmul, hmul, hHr_mul, hmul2]
    refine ⟨m • b'', ?_, ?_⟩
    · rw [map_zsmul, hb'', smul_zero]
    · have hs2 : K0.mapA (smashIncl V W) (μx (m • b'') H) = K0.mapA (smashIncl V W) z := by
        rw [(hμx (m • b'') H (by rw [map_zsmul, hb'', smul_zero]) hH0).2 μP hμP, hz1']
      have hred : K0.mapA (augPair (V × W) y0) (μx (m • b'') H - z) = 0 := by
        rw [map_sub, (hμx (m • b'') H (by rw [map_zsmul, hb'', smul_zero]) hH0).1, hz,
          sub_zero]
      have hsm : K0.mapA (smashIncl V W) (μx (m • b'') H - z) = 0 := by
        rw [map_sub, hs2, sub_self]
      exact sub_eq_zero.mp (hsmash_inj _ hred hsm)
  · -- ## injectivity
    intro s t hs ht hst
    have hred : K0.mapA (augPair V y0V) (s - t) = 0 := by
      rw [map_sub, hs, ht, sub_zero]
    have hzero : μx (s - t) H = 0 := by
      rw [map_sub, AddMonoidHom.sub_apply, hst, sub_self]
    have h1 : K0.mapA (smashIncl V W) (μx (s - t) H)
        = μP (K0.mapA (pullFst V W) (s - t)) (K0.mapA (pullSnd V W) H) :=
      (hμx (s - t) H hred hH0).2 μP hμP
    have h2 : μP (K0.mapA (pullFst V W) (s - t)) (K0.mapA (pullSnd V W) H) = 0 := by
      rw [← h1, hzero, map_zero]
    -- the two elements of `K₀(Kpair V) × K₀(Kpair V)` have the same image under `Φ`
    have h3 : Φ (0, s - t)
        = Φ (μV (s - t) (K0.mapA (Algebra.ofId ℂ (Kpair V)) r0), 0) := by
      have hzero' : μP (K0.mapA (pullFst V W) (s - t)) (K0.mapA (pullSnd V W) Hr) = 0 := by
        rw [hHr_mul, hmul2, h2, smul_zero]
      simp only [Φ, map_zero, zero_add, add_zero, AddMonoidHom.zero_apply, hH'split_pull, map_add,
        hzero']
      rw [← ba_const_natural (pullFst V W) r0, ← hnatF]
    have h4 : (0, s - t) = (μV (s - t) (K0.mapA (Algebra.ofId ℂ (Kpair V)) r0), 0) :=
      hΦ.1 h3
    have h5 : s - t = 0 := (Prod.mk.injEq _ _ _ _).mp h4 |>.2
    exact sub_eq_zero.mp h5

end

end Work.KT
