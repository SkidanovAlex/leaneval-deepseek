import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.BallKFrame
import Submission.Work.KT.psi_exists
import Submission.Work.KT.ballK_dim2
import Submission.Work.KT.bott_susp
import Submission.Work.KT.ext_product
import Submission.Work.KT.ExtGen.Basic
import Submission.Work.KT.ExtGen.Radial

namespace Work.KT

open Matrix

noncomputable section

set_option maxHeartbeats 1600000

/-! ### Wrappers (final version: read off `Work.KT.ExtAux`, i.e. the node `k0_basic`) -/

theorem bs_k0Mul_exists (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) :
    ∃ μ : K0 A →+ K0 A →+ K0 A, IsK0Mul μ :=
  ExtAux.k0Mul_exists A hcomm

theorem bs_mapA_comp_alg {A B C : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    [Ring C] [Algebra ℂ C] (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] C) :
    K0.mapA (ψ.comp φ) = (K0.mapA ψ).comp (K0.mapA φ) :=
  ExtAux.k0map_comp A B C φ.toRingHom ψ.toRingHom

theorem bs_mapA_id_alg {A : Type} [Ring A] [Algebra ℂ A] :
    K0.mapA (AlgHom.id ℂ A) = AddMonoidHom.id (K0 A) :=
  ExtAux.k0map_id A

/-! ## Elementary helpers -/

lemma bs_commKpair (V : Type) [NormedAddCommGroup V] :
    ∀ x y : Kpair V, x * y = y * x :=
  fun x y => Subtype.ext (mul_comm x.1 y.1)

lemma bs_commProdAlg (V W : Type) [NormedAddCommGroup V] [NormedAddCommGroup W] :
    ∀ x y : prodAlg V W, x * y = y * x :=
  fun x y => Subtype.ext (mul_comm x.1 y.1)

lemma bs_commC : ∀ x y : ℂ, x * y = y * x := fun x y => mul_comm x y

/-- A boundary point forces positive dimension. -/
lemma bs_one_le_finrank {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {y0 : Ball V} (hy0 : y0 ∈ bdry V) :
    1 ≤ Module.finrank ℝ V := by
  by_contra h
  have h0 : Module.finrank ℝ V = 0 := by omega
  haveI : Subsingleton V := (Module.finrank_eq_zero_iff_of_free ℝ V).mp h0
  have h1 : ‖(y0 : V)‖ = 1 := hy0
  rw [Subsingleton.elim (y0 : V) 0, norm_zero] at h1
  exact one_ne_zero h1.symm

/-! ## Functoriality of `K₀` on classes -/

lemma bs_mapA_comp_apply {A B C : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    [Ring C] [Algebra ℂ C] (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] C) (x : K0 A) :
    K0.mapA ψ (K0.mapA φ x) = K0.mapA (ψ.comp φ) x := by
  rw [bs_mapA_comp_alg φ ψ]
  rfl

lemma bs_mapA_id_apply {A : Type} [Ring A] [Algebra ℂ A] (x : K0 A) :
    K0.mapA (AlgHom.id ℂ A) x = x := by
  rw [bs_mapA_id_alg]
  rfl

lemma bs_mapA_symm_self {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (E : A ≃ₐ[ℂ] B) (x : K0 A) :
    K0.mapA E.symm.toAlgHom (K0.mapA E.toAlgHom x) = x := by
  rw [bs_mapA_comp_apply E.toAlgHom E.symm.toAlgHom x]
  have h : E.symm.toAlgHom.comp E.toAlgHom = AlgHom.id ℂ A := by
    ext y
    exact E.symm_apply_apply y
  rw [h]
  exact bs_mapA_id_apply x

lemma bs_mapA_self_symm {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (E : A ≃ₐ[ℂ] B) (y : K0 B) :
    K0.mapA E.toAlgHom (K0.mapA E.symm.toAlgHom y) = y := by
  rw [bs_mapA_comp_apply E.symm.toAlgHom E.toAlgHom y]
  have h : E.toAlgHom.comp E.symm.toAlgHom = AlgHom.id ℂ B := by
    ext y
    exact E.apply_symm_apply y
  rw [h]
  exact bs_mapA_id_apply y

lemma bs_muX_smul_smul {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (μx : A →+ B →+ C) (k l : ℤ) (a : A) (b : B) :
    μx (k • a) (l • b) = (k * l) • μx a b := by
  rw [map_zsmul, map_zsmul, AddMonoidHom.smul_apply, smul_smul, mul_comm l k]

/-! ## Transport of the Bott class along an algebra isomorphism -/

/-- The generator data of a two-dimensional Bott class transports along an algebra isomorphism
compatible with the augmentations. -/
lemma bs_genData_transfer {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (hcommA : ∀ x y : A, x * y = y * x) (hcommB : ∀ x y : B, x * y = y * x)
    (E : A ≃ₐ[ℂ] B) (εA : A →ₐ[ℂ] ℂ) (εB : B →ₐ[ℂ] ℂ)
    (hε : ∀ x : A, εA x = εB (E x))
    (h : ∃ H : K0 B, K0.mapA εB H = 0 ∧ (∀ k : ℤ, k • H = 0 → k = 0) ∧
      (∀ z, K0.mapA εB z = 0 → ∃ k : ℤ, z = k • H) ∧
      (∀ ψ : K0 B →+ K0 B, IsPsi2 ψ → ψ H = 2 • H) ∧
      (∀ ψ : K0 B →+ K0 B, IsPsi3 ψ → ψ H = 3 • H)) :
    ∃ H : K0 A, K0.mapA εA H = 0 ∧ (∀ k : ℤ, k • H = 0 → k = 0) ∧
      (∀ z, K0.mapA εA z = 0 → ∃ k : ℤ, z = k • H) ∧
      (∀ ψ : K0 A →+ K0 A, IsPsi2 ψ → ψ H = 2 • H) ∧
      (∀ ψ : K0 A →+ K0 A, IsPsi3 ψ → ψ H = 3 • H) := by
  obtain ⟨H₀, h0, h1, h2, h2ψ, h3ψ⟩ := h
  have hεA : εA = εB.comp E.toAlgHom := AlgHom.ext hε
  set HA : K0 A := K0.mapA E.symm.toAlgHom H₀ with hHA
  have hε' : εA.comp E.symm.toAlgHom = εB := by
    rw [hεA, AlgHom.comp_assoc]
    rw [show E.toAlgHom.comp E.symm.toAlgHom = AlgHom.id ℂ B from by
      ext y
      exact E.apply_symm_apply y]
    rw [AlgHom.comp_id]
  refine ⟨HA, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hHA, bs_mapA_comp_apply E.symm.toAlgHom εA H₀, hε', h0]
  · intro k hk
    have hz : k • H₀ = 0 := by
      have h2' : K0.mapA E.toAlgHom (k • HA) = k • H₀ := by
        rw [map_zsmul, hHA, bs_mapA_self_symm E H₀]
      rw [← h2', hk, map_zero]
    exact h1 k hz
  · intro z hz
    have hzB : K0.mapA εB (K0.mapA E.toAlgHom z) = 0 := by
      rw [bs_mapA_comp_apply E.toAlgHom εB z, ← hεA]
      exact hz
    obtain ⟨k, hk⟩ := h2 (K0.mapA E.toAlgHom z) hzB
    refine ⟨k, ?_⟩
    rw [hHA, ← bs_mapA_symm_self E z, hk, map_zsmul]
  · intro ψ hψ
    obtain ⟨ψB, hψB⟩ := (psi_exists.1 B hcommB).1
    have hnat := (psi_exists.2.1 A B hcommA hcommB E.toAlgHom ψ ψB).1 hψ hψB
    have step : K0.mapA E.toAlgHom (ψ HA) = 2 • H₀ := by
      rw [hnat HA, hHA, bs_mapA_self_symm E H₀, h2ψ ψB hψB]
    calc ψ HA = K0.mapA E.symm.toAlgHom (K0.mapA E.toAlgHom (ψ HA)) :=
          (bs_mapA_symm_self E (ψ HA)).symm
      _ = K0.mapA E.symm.toAlgHom (2 • H₀) := by rw [step]
      _ = 2 • HA := by rw [map_nsmul, hHA]
  · intro ψ hψ
    obtain ⟨ψB, hψB⟩ := (psi_exists.1 B hcommB).2
    have hnat := (psi_exists.2.1 A B hcommA hcommB E.toAlgHom ψ ψB).2 hψ hψB
    have step : K0.mapA E.toAlgHom (ψ HA) = 3 • H₀ := by
      rw [hnat HA, hHA, bs_mapA_self_symm E H₀, h3ψ ψB hψB]
    calc ψ HA = K0.mapA E.symm.toAlgHom (K0.mapA E.toAlgHom (ψ HA)) :=
          (bs_mapA_symm_self E (ψ HA)).symm
      _ = K0.mapA E.symm.toAlgHom (3 • H₀) := by rw [step]
      _ = 3 • HA := by rw [map_nsmul, hHA]

/-! ## The Bott class on an abstract two-dimensional space -/

/-- **Bott class in dimension two**, on an abstract two-dimensional normed space: transport of
`ballK_dim2` from `ℝ²` along the radial normalisation of any linear equivalence. -/
lemma bs_bottClass_dim2 (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (y0W : Ball W) (hW : y0W ∈ bdry W)
    (hWd : Module.finrank ℝ W = 2) :
    ∃ H : K0 (Kpair W), K0.mapA (augPair W y0W) H = 0 ∧
      (∀ k : ℤ, k • H = 0 → k = 0) ∧
      (∀ z, K0.mapA (augPair W y0W) z = 0 → ∃ k : ℤ, z = k • H) ∧
      (∀ ψ : K0 (Kpair W) →+ K0 (Kpair W), IsPsi2 ψ → ψ H = 2 • H) ∧
      (∀ ψ : K0 (Kpair W) →+ K0 (Kpair W), IsPsi3 ψ → ψ H = 3 • H) := by
  have hfr : Module.finrank ℝ W = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [hWd, finrank_euclideanSpace_fin]
  let e : W ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2) := LinearEquiv.ofFinrankEq W _ hfr
  set y0E : Ball (EuclideanSpace ℝ (Fin 2)) := ExtGen.phiBall e y0W with hy0E
  have hy0Em : y0E ∈ bdry (EuclideanSpace ℝ (Fin 2)) := by
    rw [hy0E]
    exact ExtGen.phiBall_mem_bdry e hW
  obtain ⟨H₀, hH₀⟩ := ballK_dim2 y0E hy0Em
  set E : Kpair W ≃ₐ[ℂ] Kpair (EuclideanSpace ℝ (Fin 2)) :=
    pairPullbackEquiv (ExtGen.psiBallCM e) (ExtGen.phiBallCM e)
      (fun y => ExtGen.phiBall_psiBall e y) (fun x => ExtGen.psiBall_phiBall e x)
      (fun y hy => ExtGen.psiBall_mem_bdry e hy)
      (fun x hx => ExtGen.phiBall_mem_bdry e hx) with hE
  have hcomp : ∀ x : Kpair W,
      augPair W y0W x = augPair (EuclideanSpace ℝ (Fin 2)) y0E (E x) := by
    intro x
    have hE' : ((E x : Kpair (EuclideanSpace ℝ (Fin 2))) :
          C(Ball (EuclideanSpace ℝ (Fin 2)), ℂ))
        = (x : C(Ball W, ℂ)).comp (ExtGen.psiBallCM e) := by
      rw [hE]
      rfl
    have hval : ((E x : Kpair (EuclideanSpace ℝ (Fin 2))) :
          C(Ball (EuclideanSpace ℝ (Fin 2)), ℂ)) y0E = (x : C(Ball W, ℂ)) y0W := by
      rw [hE', ContinuousMap.comp_apply, ExtGen.psiBallCM_apply, hy0E,
        ExtGen.psiBall_phiBall]
    simp only [augPair, AlgHom.comp_apply, ContinuousMap.evalAlgHom_apply]
    exact hval.symm
  exact bs_genData_transfer (bs_commKpair W) (bs_commKpair (EuclideanSpace ℝ (Fin 2)))
    E (augPair W y0W) (augPair (EuclideanSpace ℝ (Fin 2)) y0E) hcomp ⟨H₀, hH₀⟩

/-! ## `ψ` and the external product -/

/-- `ψ²` preserves the reduced subgroup. -/
lemma bs_psi2_preserves_red {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (y0 : Ball V) (ψ : K0 (Kpair V) →+ K0 (Kpair V)) (hψ : IsPsi2 ψ)
    {z : K0 (Kpair V)} (hz : K0.mapA (augPair V y0) z = 0) :
    K0.mapA (augPair V y0) (ψ z) = 0 := by
  obtain ⟨ψℂ, hψℂ⟩ := (psi_exists.1 ℂ bs_commC).1
  have hnat := (psi_exists.2.1 (Kpair V) ℂ (bs_commKpair V) bs_commC
    (augPair V y0) ψ ψℂ).1 hψ hψℂ z
  rw [hnat, hz, map_zero]

/-- `ψ³` preserves the reduced subgroup. -/
lemma bs_psi3_preserves_red {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (y0 : Ball V) (ψ : K0 (Kpair V) →+ K0 (Kpair V)) (hψ : IsPsi3 ψ)
    {z : K0 (Kpair V)} (hz : K0.mapA (augPair V y0) z = 0) :
    K0.mapA (augPair V y0) (ψ z) = 0 := by
  obtain ⟨ψℂ, hψℂ⟩ := (psi_exists.1 ℂ bs_commC).2
  have hnat := (psi_exists.2.1 (Kpair V) ℂ (bs_commKpair V) bs_commC
    (augPair V y0) ψ ψℂ).2 hψ hψℂ z
  rw [hnat, hz, map_zero]

/-- `ψ²` is multiplicative for the reduced external product. -/
lemma bs_psi2_ext {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (y0V : Ball V) (y0W : Ball W) (y0 : Ball (V × W))
    (μx : K0 (Kpair V) →+ K0 (Kpair W) →+ K0 (Kpair (V × W)))
    (hμx : IsExtProd V W y0V y0W y0 μx)
    (hpart2 : ∀ w : K0 (Kpair (V × W)), K0.mapA (augPair (V × W) y0) w = 0 →
      K0.mapA (smashIncl V W) w = 0 → w = 0)
    (ψV : K0 (Kpair V) →+ K0 (Kpair V)) (ψW : K0 (Kpair W) →+ K0 (Kpair W))
    (ψ : K0 (Kpair (V × W)) →+ K0 (Kpair (V × W)))
    (hψV : IsPsi2 ψV) (hψW : IsPsi2 ψW) (hψ : IsPsi2 ψ)
    {s : K0 (Kpair V)} (hs : K0.mapA (augPair V y0V) s = 0)
    {t : K0 (Kpair W)} (ht : K0.mapA (augPair W y0W) t = 0) :
    ψ (μx s t) = μx (ψV s) (ψW t) := by
  obtain ⟨μ, hμ⟩ := bs_k0Mul_exists (prodAlg V W) (bs_commProdAlg V W)
  obtain ⟨ψP, hψP⟩ := (psi_exists.1 (prodAlg V W) (bs_commProdAlg V W)).1
  obtain ⟨ψP3, hψP3⟩ := (psi_exists.1 (prodAlg V W) (bs_commProdAlg V W)).2
  have e1 : K0.mapA (smashIncl V W) (ψ (μx s t))
      = ψP (K0.mapA (smashIncl V W) (μx s t)) :=
    (psi_exists.2.1 (Kpair (V × W)) (prodAlg V W) (bs_commKpair (V × W))
      (bs_commProdAlg V W) (smashIncl V W) ψ ψP).1 hψ hψP (μx s t)
  have e2 : K0.mapA (smashIncl V W) (μx s t)
      = μ (K0.mapA (pullFst V W) s) (K0.mapA (pullSnd V W) t) :=
    (hμx s t hs ht).2 μ hμ
  have e3 : ψP (μ (K0.mapA (pullFst V W) s) (K0.mapA (pullSnd V W) t))
      = μ (ψP (K0.mapA (pullFst V W) s)) (ψP (K0.mapA (pullSnd V W) t)) :=
    ((psi_exists.2.2.1 (prodAlg V W) (bs_commProdAlg V W) μ ψP ψP3 hμ hψP hψP3)
      (K0.mapA (pullFst V W) s) (K0.mapA (pullSnd V W) t)).1
  have e4 : ψP (K0.mapA (pullFst V W) s) = K0.mapA (pullFst V W) (ψV s) :=
    ((psi_exists.2.1 (Kpair V) (prodAlg V W) (bs_commKpair V) (bs_commProdAlg V W)
      (pullFst V W) ψV ψP).1 hψV hψP s).symm
  have e5 : ψP (K0.mapA (pullSnd V W) t) = K0.mapA (pullSnd V W) (ψW t) :=
    ((psi_exists.2.1 (Kpair W) (prodAlg V W) (bs_commKpair W) (bs_commProdAlg V W)
      (pullSnd V W) ψW ψP).1 hψW hψP t).symm
  have hrV : K0.mapA (augPair V y0V) (ψV s) = 0 := bs_psi2_preserves_red y0V ψV hψV hs
  have hrW : K0.mapA (augPair W y0W) (ψW t) = 0 := bs_psi2_preserves_red y0W ψW hψW ht
  have e6 : K0.mapA (smashIncl V W) (μx (ψV s) (ψW t))
      = μ (K0.mapA (pullFst V W) (ψV s)) (K0.mapA (pullSnd V W) (ψW t)) :=
    (hμx (ψV s) (ψW t) hrV hrW).2 μ hμ
  have hsm : K0.mapA (smashIncl V W) (ψ (μx s t) - μx (ψV s) (ψW t)) = 0 := by
    rw [map_sub, e1, e2, e3, e4, e5, e6, sub_self]
  have haug : K0.mapA (augPair (V × W) y0) (ψ (μx s t) - μx (ψV s) (ψW t)) = 0 := by
    rw [map_sub, bs_psi2_preserves_red y0 ψ hψ (hμx s t hs ht).1,
      (hμx (ψV s) (ψW t) hrV hrW).1, sub_self]
  exact sub_eq_zero.mp (hpart2 _ haug hsm)

/-- `ψ³` is multiplicative for the reduced external product. -/
lemma bs_psi3_ext {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (y0V : Ball V) (y0W : Ball W) (y0 : Ball (V × W))
    (μx : K0 (Kpair V) →+ K0 (Kpair W) →+ K0 (Kpair (V × W)))
    (hμx : IsExtProd V W y0V y0W y0 μx)
    (hpart2 : ∀ w : K0 (Kpair (V × W)), K0.mapA (augPair (V × W) y0) w = 0 →
      K0.mapA (smashIncl V W) w = 0 → w = 0)
    (ψV : K0 (Kpair V) →+ K0 (Kpair V)) (ψW : K0 (Kpair W) →+ K0 (Kpair W))
    (ψ : K0 (Kpair (V × W)) →+ K0 (Kpair (V × W)))
    (hψV : IsPsi3 ψV) (hψW : IsPsi3 ψW) (hψ : IsPsi3 ψ)
    {s : K0 (Kpair V)} (hs : K0.mapA (augPair V y0V) s = 0)
    {t : K0 (Kpair W)} (ht : K0.mapA (augPair W y0W) t = 0) :
    ψ (μx s t) = μx (ψV s) (ψW t) := by
  obtain ⟨μ, hμ⟩ := bs_k0Mul_exists (prodAlg V W) (bs_commProdAlg V W)
  obtain ⟨ψP, hψP⟩ := (psi_exists.1 (prodAlg V W) (bs_commProdAlg V W)).2
  obtain ⟨ψP2, hψP2⟩ := (psi_exists.1 (prodAlg V W) (bs_commProdAlg V W)).1
  have e1 : K0.mapA (smashIncl V W) (ψ (μx s t))
      = ψP (K0.mapA (smashIncl V W) (μx s t)) :=
    (psi_exists.2.1 (Kpair (V × W)) (prodAlg V W) (bs_commKpair (V × W))
      (bs_commProdAlg V W) (smashIncl V W) ψ ψP).2 hψ hψP (μx s t)
  have e2 : K0.mapA (smashIncl V W) (μx s t)
      = μ (K0.mapA (pullFst V W) s) (K0.mapA (pullSnd V W) t) :=
    (hμx s t hs ht).2 μ hμ
  have e3 : ψP (μ (K0.mapA (pullFst V W) s) (K0.mapA (pullSnd V W) t))
      = μ (ψP (K0.mapA (pullFst V W) s)) (ψP (K0.mapA (pullSnd V W) t)) :=
    ((psi_exists.2.2.1 (prodAlg V W) (bs_commProdAlg V W) μ ψP2 ψP hμ hψP2 hψP)
      (K0.mapA (pullFst V W) s) (K0.mapA (pullSnd V W) t)).2
  have e4 : ψP (K0.mapA (pullFst V W) s) = K0.mapA (pullFst V W) (ψV s) :=
    ((psi_exists.2.1 (Kpair V) (prodAlg V W) (bs_commKpair V) (bs_commProdAlg V W)
      (pullFst V W) ψV ψP).2 hψV hψP s).symm
  have e5 : ψP (K0.mapA (pullSnd V W) t) = K0.mapA (pullSnd V W) (ψW t) :=
    ((psi_exists.2.1 (Kpair W) (prodAlg V W) (bs_commKpair W) (bs_commProdAlg V W)
      (pullSnd V W) ψW ψP).2 hψW hψP t).symm
  have hrV : K0.mapA (augPair V y0V) (ψV s) = 0 := bs_psi3_preserves_red y0V ψV hψV hs
  have hrW : K0.mapA (augPair W y0W) (ψW t) = 0 := bs_psi3_preserves_red y0W ψW hψW ht
  have e6 : K0.mapA (smashIncl V W) (μx (ψV s) (ψW t))
      = μ (K0.mapA (pullFst V W) (ψV s)) (K0.mapA (pullSnd V W) (ψW t)) :=
    (hμx (ψV s) (ψW t) hrV hrW).2 μ hμ
  have hsm : K0.mapA (smashIncl V W) (ψ (μx s t) - μx (ψV s) (ψW t)) = 0 := by
    rw [map_sub, e1, e2, e3, e4, e5, e6, sub_self]
  have haug : K0.mapA (augPair (V × W) y0) (ψ (μx s t) - μx (ψV s) (ψW t)) = 0 := by
    rw [map_sub, bs_psi3_preserves_red y0 ψ hψ (hμx s t hs ht).1,
      (hμx (ψV s) (ψW t) hrV hrW).1, sub_self]
  exact sub_eq_zero.mp (hpart2 _ haug hsm)

/-! ## The suspension step -/

/-- **The suspension step of `ball_K`**: `K̃(D_V/S_V) → K̃(D_{V×W}/S_{V×W})` for a
two-dimensional `W` raises the dimension by two and multiplies the `ψ`-eigenvalues by `2`,`3`.

If the reduced group of `Kpair V` is infinite cyclic with `ψ² = 2^j`, `ψ³ = 3^j` (or vanishes
when `dim V = 2j+1`), then the same holds for `Kpair (V × W)` with `j+1`, for two-dimensional `W`.

Ingredients (`depends_on` lists only modules that build today; import the others once they
build): `Work.KT.bott_susp` (external product with the Bott class `H` of `W` is injective on and
surjective onto reduced classes — `fund_product` applied to `Xq V`, via `Work.KT.ext_product`),
`Work.KT.ballK_dim2` and `Work.KT.ballK_transfer` (to get the Bott class `H` on the abstract
`W` and its eigenvalues `ψ²H = 2H`, `ψ³H = 3H`), `Work.KT.psi_exists` and `Work.KT.k0_basic`.
Given `g` with `ker (augPair V y0V) = ℤ·g`, the generator of `ker (augPair (V×W) y0)` is `μx g H`,
and `ψ (μx s H) = μx (ψ_V s) (ψ_W H)` (naturality and multiplicativity of `ψ` for the external
product, by comparing `smashIncl`-images and using injectivity of `smashIncl` on reduced classes),
so `ψ (μx s H) = μx (2^j • s) (2 • H) = 2^(j+1) • μx s H`. -/
theorem ballK_step (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (y0V : Ball V) (hV : y0V ∈ bdry V) (y0W : Ball W) (hW : y0W ∈ bdry W)
    (y0 : Ball (V × W)) (hy0 : y0 ∈ bdry (V × W))
    (hVd : 1 ≤ Module.finrank ℝ V) (hWd : Module.finrank ℝ W = 2) (j : ℕ)
    (h : BallKStmt V y0V hV j) : BallKStmt (V × W) y0 hy0 (j + 1) := by
  obtain ⟨H, hH0, hH1, hH2, hH2ψ, hH3ψ⟩ := bs_bottClass_dim2 W y0W hW hWd
  obtain ⟨⟨μx, hμx⟩, hpart2⟩ := ext_product V W y0V hV y0W hW y0 hy0
  unfold BallKStmt at h ⊢
  refine ⟨?_, ?_⟩
  · intro hfin
    have hVfr : Module.finrank ℝ V = 2 * j := by
      have hprod : Module.finrank ℝ (V × W) = Module.finrank ℝ V + Module.finrank ℝ W :=
        Module.finrank_prod
      omega
    have hVd1 : 1 ≤ Module.finrank ℝ V := bs_one_le_finrank hV
    obtain ⟨surj, inj⟩ :=
      bott_susp V W y0V hV y0W hW y0 hy0 hVd1 hWd H hH0 hH1 hH2 μx hμx
    obtain ⟨g, hgred, hgnz, hggen⟩ := (h.1 hVfr).1
    refine ⟨⟨μx g H, (hμx g H hgred hH0).1, ?_, ?_⟩, ?_, ?_⟩
    · intro k hk
      have hred_kg : K0.mapA (augPair V y0V) (k • g) = 0 := by
        rw [map_zsmul, hgred, smul_zero]
      have hkg : k • g = 0 :=
        inj (k • g) 0 hred_kg (map_zero _) (by
          rw [map_zsmul]
          simpa using hk)
      exact hgnz k hkg
    · intro z hz
      obtain ⟨s, hs, hsz⟩ := surj z hz
      obtain ⟨k, hk⟩ := hggen s hs
      refine ⟨k, ?_⟩
      rw [← hsz, hk, map_zsmul]
      exact AddMonoidHom.smul_apply k (μx g) H
    · intro ψ hψ z hz
      obtain ⟨s, hs, hsz⟩ := surj z hz
      obtain ⟨ψV, hψV⟩ := (psi_exists.1 (Kpair V) (bs_commKpair V)).1
      obtain ⟨ψW, hψW⟩ := (psi_exists.1 (Kpair W) (bs_commKpair W)).1
      have key := bs_psi2_ext y0V y0W y0 μx hμx hpart2 ψV ψW ψ hψV hψW hψ hs hH0
      rw [← hsz, key, (h.1 hVfr).2.1 ψV hψV s hs, hH2ψ ψW hψW]
      calc μx ((2 : ℤ) ^ j • s) (2 • H)
          = μx ((2 : ℤ) ^ j • s) (((2 : ℕ) : ℤ) • H) := by rw [← natCast_zsmul H 2]
        _ = (((2 : ℤ) ^ j) * ((2 : ℕ) : ℤ)) • μx s H :=
              bs_muX_smul_smul μx ((2 : ℤ) ^ j) ((2 : ℕ) : ℤ) s H
        _ = (2 : ℤ) ^ (j + 1) • μx s H := by
              rw [pow_succ]
              simp
    · intro ψ hψ z hz
      obtain ⟨s, hs, hsz⟩ := surj z hz
      obtain ⟨ψV, hψV⟩ := (psi_exists.1 (Kpair V) (bs_commKpair V)).2
      obtain ⟨ψW, hψW⟩ := (psi_exists.1 (Kpair W) (bs_commKpair W)).2
      have key := bs_psi3_ext y0V y0W y0 μx hμx hpart2 ψV ψW ψ hψV hψW hψ hs hH0
      rw [← hsz, key, (h.1 hVfr).2.2 ψV hψV s hs, hH3ψ ψW hψW]
      calc μx ((3 : ℤ) ^ j • s) (3 • H)
          = μx ((3 : ℤ) ^ j • s) (((3 : ℕ) : ℤ) • H) := by rw [← natCast_zsmul H 3]
        _ = (((3 : ℤ) ^ j) * ((3 : ℕ) : ℤ)) • μx s H :=
              bs_muX_smul_smul μx ((3 : ℤ) ^ j) ((3 : ℕ) : ℤ) s H
        _ = (3 : ℤ) ^ (j + 1) • μx s H := by
              rw [pow_succ]
              simp
  · intro hfin z hz
    have hVfr : Module.finrank ℝ V = 2 * j + 1 := by
      have hprod : Module.finrank ℝ (V × W) = Module.finrank ℝ V + Module.finrank ℝ W :=
        Module.finrank_prod
      omega
    have hVd1 : 1 ≤ Module.finrank ℝ V := bs_one_le_finrank hV
    obtain ⟨surj, _⟩ :=
      bott_susp V W y0V hV y0W hW y0 hy0 hVd1 hWd H hH0 hH1 hH2 μx hμx
    obtain ⟨s, hs, hsz⟩ := surj z hz
    rw [← hsz, h.2 hVfr s hs]
    simp

end

end Work.KT
