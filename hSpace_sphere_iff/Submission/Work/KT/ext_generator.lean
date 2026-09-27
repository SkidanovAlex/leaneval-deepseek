import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.ExtGen.Basic
import Submission.Work.KT.ExtGen.peel
import Submission.Work.KT.ExtGen.pairIso_of_linearEquiv
import Submission.Work.KT.ExtGen.susp_surj
import Submission.Work.KT.ExtGen.ext_nesting
import Submission.Work.KT.ext_product
import Submission.Work.KT.EG.seed_R2
import Submission.Work.KT.k0_basic

namespace Work.KT

noncomputable section

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 8000000
/-! ## 1. Elementary functoriality of `K0.mapA` -/

/-- `K0.mapA` is functorial (composition form), with explicit ring arguments. -/
lemma eg_mapA_comp' {A B C : Type} [Ring A] [Ring B] [Ring C]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C] (φ : B →ₐ[ℂ] C) (ψ : A →ₐ[ℂ] B) :
    K0.mapA (A := A) (B := C) (φ.comp ψ)
      = (K0.mapA (A := B) (B := C) φ).comp (K0.mapA (A := A) (B := B) ψ) :=
  K0.map_comp ψ.toRingHom φ.toRingHom

/-- `K0.mapA` is functorial (applied form), with explicit ring arguments. -/
lemma eg_mapA_comp_apply (A B C : Type) [Ring A] [Ring B] [Ring C] [Algebra ℂ A] [Algebra ℂ B]
    [Algebra ℂ C] (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] C) (x : K0 A) :
    K0.mapA (A := B) (B := C) ψ (K0.mapA (A := A) (B := B) φ x)
      = K0.mapA (A := A) (B := C) (ψ.comp φ) x := by
  rw [← AddMonoidHom.comp_apply (K0.mapA (A := B) (B := C) ψ) (K0.mapA (A := A) (B := B) φ) x,
    ← eg_mapA_comp' (A := A) (B := B) (C := C) ψ φ]

/-- `K0.mapA` of the identity, with explicit ring arguments. -/
lemma eg_mapA_id' (A : Type) [Ring A] [Algebra ℂ A] :
    K0.mapA (A := A) (B := A) (AlgHom.id ℂ A) = AddMonoidHom.id (K0 A) :=
  K0.map_id

/-- `E.symm.toAlgHom ∘ E.toAlgHom = id`. -/
lemma eg_symm_comp (A B : Type) [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (E : A ≃ₐ[ℂ] B) : E.symm.toAlgHom.comp E.toAlgHom = AlgHom.id ℂ A := by
  ext x
  exact E.symm_apply_apply x

/-- `E.toAlgHom ∘ E.symm.toAlgHom = id`. -/
lemma eg_comp_symm (A B : Type) [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (E : A ≃ₐ[ℂ] B) : E.toAlgHom.comp E.symm.toAlgHom = AlgHom.id ℂ B := by
  ext x
  exact E.apply_symm_apply x

/-- Evaluation in the second variable, as an additive homomorphism. -/
def eg_eval₂ {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (μ : A →+ B →+ C) (b : B) : A →+ C :=
  AddMonoidHom.mk' (fun a => μ a b) (by
    intro x y
    show μ (x + y) b = μ x b + μ y b
    have h : μ (x + y) = μ x + μ y := AddMonoidHom.map_add μ x y
    rw [h]
    rfl)

/-- `a² = 1` for `a = ±1`. -/
lemma eg_sq_eq_one {a : ℤ} (ha : a = 1 ∨ a = -1) : a * a = 1 := by
  rcases ha with h1 | h1 <;> rw [h1] <;> norm_num

/-- `a * b = ±1` for `a = ±1`, `b = ±1`. -/
lemma eg_mul_eq_pm_one {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with h1 | h1 <;> rcases hb with h2 | h2 <;> rw [h1, h2] <;> norm_num

/-! ## 2. Transport along an isomorphism of pair structures -/

/-- Reduced elements are carried to reduced elements. -/
lemma mapA_reduced_fwd {U U' : Type} [NormedAddCommGroup U] [NormedAddCommGroup U']
    (E : Kpair U ≃ₐ[ℂ] Kpair U') (y : Ball U) (y' : Ball U')
    (h : (augPair U' y').comp E.toAlgHom = augPair U y)
    {z : K0 (Kpair U)} (hz : K0.mapA (A := Kpair U) (B := ℂ) (augPair U y) z = 0) :
    K0.mapA (A := Kpair U') (B := ℂ) (augPair U' y')
      (K0.mapA (A := Kpair U) (B := Kpair U') E.toAlgHom z) = 0 := by
  rw [eg_mapA_comp_apply (Kpair U) (Kpair U') ℂ E.toAlgHom (augPair U' y') z, h, hz]

/-- Reducedness transfers backwards along `E`. -/
lemma mapA_reduced_bwd {U U' : Type} [NormedAddCommGroup U] [NormedAddCommGroup U']
    (E : Kpair U ≃ₐ[ℂ] Kpair U') (y : Ball U) (y' : Ball U')
    (h : (augPair U' y').comp E.toAlgHom = augPair U y)
    {z : K0 (Kpair U')} (hz : K0.mapA (A := Kpair U') (B := ℂ) (augPair U' y') z = 0) :
    K0.mapA (A := Kpair U) (B := ℂ) (augPair U y)
      (K0.mapA (A := Kpair U') (B := Kpair U) E.symm.toAlgHom z) = 0 := by
  have h' : (augPair U y).comp E.symm.toAlgHom = augPair U' y' := by
    ext x
    rw [AlgHom.comp_apply, ← h, AlgHom.comp_apply]
    exact congrArg (fun w => (augPair U' y') w) (E.apply_symm_apply x)
  rw [eg_mapA_comp_apply (Kpair U') (Kpair U) ℂ E.symm.toAlgHom (augPair U y) z, h', hz]

/-- Generators are carried to generators. -/
lemma mapA_generates_fwd {U U' : Type} [NormedAddCommGroup U] [NormedAddCommGroup U']
    (E : Kpair U ≃ₐ[ℂ] Kpair U') (y : Ball U) (y' : Ball U')
    (h : (augPair U' y').comp E.toAlgHom = augPair U y)
    {s : K0 (Kpair U)} (hs : K0.mapA (A := Kpair U) (B := ℂ) (augPair U y) s = 0)
    (hsg : ∀ z, K0.mapA (A := Kpair U) (B := ℂ) (augPair U y) z = 0 → ∃ n : ℤ, z = n • s) :
    ∀ z, K0.mapA (A := Kpair U') (B := ℂ) (augPair U' y') z = 0 →
      ∃ n : ℤ, z = n • (K0.mapA (A := Kpair U) (B := Kpair U') E.toAlgHom s) := by
  intro z hz
  have hz' : K0.mapA (A := Kpair U) (B := ℂ) (augPair U y)
      (K0.mapA (A := Kpair U') (B := Kpair U) E.symm.toAlgHom z) = 0 :=
    mapA_reduced_bwd E y y' h hz
  obtain ⟨n, hn⟩ := hsg _ hz'
  refine ⟨n, ?_⟩
  have hz2 : K0.mapA (A := Kpair U) (B := Kpair U') E.toAlgHom
      (K0.mapA (A := Kpair U') (B := Kpair U) E.symm.toAlgHom z) = z := by
    rw [eg_mapA_comp_apply (Kpair U') (Kpair U) (Kpair U') E.symm.toAlgHom E.toAlgHom z,
      eg_comp_symm (Kpair U) (Kpair U') E, eg_mapA_id' (Kpair U')]
    rfl
  calc z = K0.mapA (A := Kpair U) (B := Kpair U') E.toAlgHom
        (K0.mapA (A := Kpair U') (B := Kpair U) E.symm.toAlgHom z) := hz2.symm
    _ = K0.mapA (A := Kpair U) (B := Kpair U') E.toAlgHom (n • s) := by rw [hn]
    _ = n • K0.mapA (A := Kpair U) (B := Kpair U') E.toAlgHom s :=
        AddMonoidHom.map_zsmul (K0.mapA (A := Kpair U) (B := Kpair U') E.toAlgHom) n s

/-- **Naturality of the external product for an isomorphism of pair structures.** -/
lemma pairIso_mapA_mu {V W V' W' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V']
    [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
    (S : pairIso V W V' W')
    (y0V : Ball V) (hV : y0V ∈ bdry V) (y0W : Ball W) (hW : y0W ∈ bdry W)
    (y0 : Ball (V × W)) (hy0 : y0 ∈ bdry (V × W))
    (y0V' : Ball V') (hV' : y0V' ∈ bdry V') (y0W' : Ball W') (hW' : y0W' ∈ bdry W')
    (y0' : Ball (V' × W')) (hy0' : y0' ∈ bdry (V' × W'))
    (μx : K0 (Kpair V) →+ K0 (Kpair W) →+ K0 (Kpair (V × W)))
    (hμx : IsExtProd V W y0V y0W y0 μx)
    (μx' : K0 (Kpair V') →+ K0 (Kpair W') →+ K0 (Kpair (V' × W')))
    (hμx' : IsExtProd V' W' y0V' y0W' y0' μx')
    (s : K0 (Kpair V)) (hs : K0.mapA (A := Kpair V) (B := ℂ) (augPair V y0V) s = 0)
    (t : K0 (Kpair W)) (ht : K0.mapA (A := Kpair W) (B := ℂ) (augPair W y0W) t = 0) :
    K0.mapA (A := Kpair (V × W)) (B := Kpair (V' × W')) S.EPi.toAlgHom (μx s t) =
      μx' (K0.mapA (A := Kpair V) (B := Kpair V') S.EV.toAlgHom s)
          (K0.mapA (A := Kpair W) (B := Kpair W') S.EW.toAlgHom t) := by
  have hVred : K0.mapA (A := Kpair V') (B := ℂ) (augPair V' y0V')
      (K0.mapA (A := Kpair V) (B := Kpair V') S.EV.toAlgHom s) = 0 := by
    obtain ⟨y, hy, hc⟩ := S.hV y0V' hV'
    have hys : K0.mapA (A := Kpair V) (B := ℂ) (augPair V y) s = 0 := by
      rw [mapA_augPair_apply_eq_of_mem_bdry V y y0V hy hV s]
      exact hs
    exact mapA_reduced_fwd S.EV y y0V' hc hys
  have hWred : K0.mapA (A := Kpair W') (B := ℂ) (augPair W' y0W')
      (K0.mapA (A := Kpair W) (B := Kpair W') S.EW.toAlgHom t) = 0 := by
    obtain ⟨y, hy, hc⟩ := S.hW y0W' hW'
    have hyt : K0.mapA (A := Kpair W) (B := ℂ) (augPair W y) t = 0 := by
      rw [mapA_augPair_apply_eq_of_mem_bdry W y y0W hy hW t]
      exact ht
    exact mapA_reduced_fwd S.EW y y0W' hc hyt
  have hPired : K0.mapA (A := Kpair (V' × W')) (B := ℂ) (augPair (V' × W') y0')
      (K0.mapA (A := Kpair (V × W)) (B := Kpair (V' × W')) S.EPi.toAlgHom (μx s t)) = 0 := by
    obtain ⟨y, hy, hc⟩ := S.hPi y0' hy0'
    have hyp : K0.mapA (A := Kpair (V × W)) (B := ℂ) (augPair (V × W) y) (μx s t) = 0 := by
      rw [mapA_augPair_apply_eq_of_mem_bdry (V × W) y y0 hy hy0 (μx s t)]
      exact (hμx s t hs ht).1
    exact mapA_reduced_fwd S.EPi y y0' hc hyp
  have hcomm : ∀ x y : prodAlg V W, x * y = y * x :=
    fun x y => Subtype.ext (mul_comm x.1 y.1)
  obtain ⟨μ, hμ, -, -, -⟩ := k0_basic.1 (prodAlg V W) hcomm
  obtain ⟨μ', hμ', -, -, -⟩ := k0_basic.1 (prodAlg V' W')
    (fun x y => Subtype.ext (mul_comm x.1 y.1))
  have hsm : K0.mapA (A := Kpair (V × W)) (B := prodAlg V W) (smashIncl V W) (μx s t) =
      μ (K0.mapA (A := Kpair V) (B := prodAlg V W) (pullFst V W) s)
        (K0.mapA (A := Kpair W) (B := prodAlg V W) (pullSnd V W) t) :=
    (hμx s t hs ht).2 μ hμ
  have hsm' : K0.mapA (A := Kpair (V' × W')) (B := prodAlg V' W') (smashIncl V' W')
      (μx' (K0.mapA (A := Kpair V) (B := Kpair V') S.EV.toAlgHom s)
           (K0.mapA (A := Kpair W) (B := Kpair W') S.EW.toAlgHom t)) =
      μ' (K0.mapA (A := Kpair V') (B := prodAlg V' W') (pullFst V' W')
            (K0.mapA (A := Kpair V) (B := Kpair V') S.EV.toAlgHom s))
         (K0.mapA (A := Kpair W') (B := prodAlg V' W') (pullSnd V' W')
            (K0.mapA (A := Kpair W) (B := Kpair W') S.EW.toAlgHom t)) :=
    (hμx' _ _ hVred hWred).2 μ' hμ'
  have hv : K0.mapA (A := prodAlg V W) (B := prodAlg V' W') S.Phi.toAlgHom
        (K0.mapA (A := Kpair V) (B := prodAlg V W) (pullFst V W) s) =
      K0.mapA (A := Kpair V') (B := prodAlg V' W') (pullFst V' W')
        (K0.mapA (A := Kpair V) (B := Kpair V') S.EV.toAlgHom s) := by
    rw [eg_mapA_comp_apply (Kpair V) (prodAlg V W) (prodAlg V' W') (pullFst V W)
        S.Phi.toAlgHom s,
      S.hfst,
      (eg_mapA_comp_apply (Kpair V) (Kpair V') (prodAlg V' W') S.EV.toAlgHom
        (pullFst V' W') s).symm]
  have hw : K0.mapA (A := prodAlg V W) (B := prodAlg V' W') S.Phi.toAlgHom
        (K0.mapA (A := Kpair W) (B := prodAlg V W) (pullSnd V W) t) =
      K0.mapA (A := Kpair W') (B := prodAlg V' W') (pullSnd V' W')
        (K0.mapA (A := Kpair W) (B := Kpair W') S.EW.toAlgHom t) := by
    rw [eg_mapA_comp_apply (Kpair W) (prodAlg V W) (prodAlg V' W') (pullSnd V W)
        S.Phi.toAlgHom t,
      S.hsnd,
      (eg_mapA_comp_apply (Kpair W) (Kpair W') (prodAlg V' W') S.EW.toAlgHom
        (pullSnd V' W') t).symm]
  have hkey : K0.mapA (A := Kpair (V' × W')) (B := prodAlg V' W') (smashIncl V' W')
        (K0.mapA (A := Kpair (V × W)) (B := Kpair (V' × W')) S.EPi.toAlgHom (μx s t)) =
      K0.mapA (A := Kpair (V' × W')) (B := prodAlg V' W') (smashIncl V' W')
        (μx' (K0.mapA (A := Kpair V) (B := Kpair V') S.EV.toAlgHom s)
             (K0.mapA (A := Kpair W) (B := Kpair W') S.EW.toAlgHom t)) := by
    calc K0.mapA (A := Kpair (V' × W')) (B := prodAlg V' W') (smashIncl V' W')
          (K0.mapA (A := Kpair (V × W)) (B := Kpair (V' × W')) S.EPi.toAlgHom (μx s t))
        = K0.mapA (A := Kpair (V × W)) (B := prodAlg V' W')
            ((smashIncl V' W').comp S.EPi.toAlgHom) (μx s t) :=
          eg_mapA_comp_apply (Kpair (V × W)) (Kpair (V' × W')) (prodAlg V' W')
            S.EPi.toAlgHom (smashIncl V' W') (μx s t)
      _ = K0.mapA (A := Kpair (V × W)) (B := prodAlg V' W')
            (S.Phi.toAlgHom.comp (smashIncl V W)) (μx s t) := by rw [S.hsm]
      _ = K0.mapA (A := prodAlg V W) (B := prodAlg V' W') S.Phi.toAlgHom
            (K0.mapA (A := Kpair (V × W)) (B := prodAlg V W) (smashIncl V W) (μx s t)) :=
          (eg_mapA_comp_apply (Kpair (V × W)) (prodAlg V W) (prodAlg V' W') (smashIncl V W)
            S.Phi.toAlgHom (μx s t)).symm
      _ = K0.mapA (A := prodAlg V W) (B := prodAlg V' W') S.Phi.toAlgHom
            (μ (K0.mapA (A := Kpair V) (B := prodAlg V W) (pullFst V W) s)
               (K0.mapA (A := Kpair W) (B := prodAlg V W) (pullSnd V W) t)) := by rw [hsm]
      _ = μ' (K0.mapA (A := prodAlg V W) (B := prodAlg V' W') S.Phi.toAlgHom
                (K0.mapA (A := Kpair V) (B := prodAlg V W) (pullFst V W) s))
             (K0.mapA (A := prodAlg V W) (B := prodAlg V' W') S.Phi.toAlgHom
                (K0.mapA (A := Kpair W) (B := prodAlg V W) (pullSnd V W) t)) :=
          k0_basic.2.1 (prodAlg V W) (prodAlg V' W') hcomm S.Phi.toRingHom μ μ' hμ hμ'
            (K0.mapA (A := Kpair V) (B := prodAlg V W) (pullFst V W) s)
            (K0.mapA (A := Kpair W) (B := prodAlg V W) (pullSnd V W) t)
      _ = μ' (K0.mapA (A := Kpair V') (B := prodAlg V' W') (pullFst V' W')
                (K0.mapA (A := Kpair V) (B := Kpair V') S.EV.toAlgHom s))
             (K0.mapA (A := Kpair W') (B := prodAlg V' W') (pullSnd V' W')
                (K0.mapA (A := Kpair W) (B := Kpair W') S.EW.toAlgHom t)) := by rw [hv, hw]
      _ = K0.mapA (A := Kpair (V' × W')) (B := prodAlg V' W') (smashIncl V' W')
            (μx' (K0.mapA (A := Kpair V) (B := Kpair V') S.EV.toAlgHom s)
                 (K0.mapA (A := Kpair W) (B := Kpair W') S.EW.toAlgHom t)) := hsm'.symm
  have hdiff : K0.mapA (A := Kpair (V' × W')) (B := prodAlg V' W') (smashIncl V' W')
      (K0.mapA (A := Kpair (V × W)) (B := Kpair (V' × W')) S.EPi.toAlgHom (μx s t) -
        μx' (K0.mapA (A := Kpair V) (B := Kpair V') S.EV.toAlgHom s)
            (K0.mapA (A := Kpair W) (B := Kpair W') S.EW.toAlgHom t)) = 0 := by
    rw [map_sub, hkey, sub_self]
  have hreddiff : K0.mapA (A := Kpair (V' × W')) (B := ℂ) (augPair (V' × W') y0')
      (K0.mapA (A := Kpair (V × W)) (B := Kpair (V' × W')) S.EPi.toAlgHom (μx s t) -
        μx' (K0.mapA (A := Kpair V) (B := Kpair V') S.EV.toAlgHom s)
            (K0.mapA (A := Kpair W) (B := Kpair W') S.EW.toAlgHom t)) = 0 := by
    rw [map_sub, hPired, (hμx' _ _ hVred hWred).1, sub_self]
  have h0 := (ext_product V' W' y0V' hV' y0W' hW' y0' hy0').2 _ hreddiff hdiff
  exact sub_eq_zero.mp h0

/-! ## 3. Reduction to a pair of a fixed shape -/

/-- **Transport of the target statement along an isomorphism of pair structures.** -/
lemma eg_transport {V W V' W' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V']
    [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
    (S : pairIso V W V' W')
    (y0V : Ball V) (hV : y0V ∈ bdry V) (y0W : Ball W) (hW : y0W ∈ bdry W)
    (y0 : Ball (V × W)) (hy0 : y0 ∈ bdry (V × W))
    (y0V' : Ball V') (hV' : y0V' ∈ bdry V') (y0W' : Ball W') (hW' : y0W' ∈ bdry W')
    (y0' : Ball (V' × W')) (hy0' : y0' ∈ bdry (V' × W'))
    (μx : K0 (Kpair V) →+ K0 (Kpair W) →+ K0 (Kpair (V × W)))
    (hμx : IsExtProd V W y0V y0W y0 μx)
    (μx' : K0 (Kpair V') →+ K0 (Kpair W') →+ K0 (Kpair (V' × W')))
    (hμx' : IsExtProd V' W' y0V' y0W' y0' μx')
    (s : K0 (Kpair V)) (hs : K0.mapA (A := Kpair V) (B := ℂ) (augPair V y0V) s = 0)
    (t : K0 (Kpair W)) (ht : K0.mapA (A := Kpair W) (B := ℂ) (augPair W y0W) t = 0)
    (h : ∀ z', K0.mapA (A := Kpair (V' × W')) (B := ℂ) (augPair (V' × W') y0') z' = 0 →
        ∃ n : ℤ, z' = n • μx' (K0.mapA (A := Kpair V) (B := Kpair V') S.EV.toAlgHom s)
          (K0.mapA (A := Kpair W) (B := Kpair W') S.EW.toAlgHom t)) :
    ∀ z, K0.mapA (A := Kpair (V × W)) (B := ℂ) (augPair (V × W) y0) z = 0 →
      ∃ n : ℤ, z = n • μx s t := by
  intro z hz
  obtain ⟨y₁, hy₁, hc₁⟩ := S.hPi y0' hy0'
  have hc₁' : (augPair (V' × W') y0').comp S.EPi.toAlgHom = augPair (V × W) y0 := by
    rw [hc₁, augPair_eq_of_mem_bdry (V × W) y₁ y0 hy₁ hy0]
  have hz' : K0.mapA (A := Kpair (V' × W')) (B := ℂ) (augPair (V' × W') y0')
      (K0.mapA (A := Kpair (V × W)) (B := Kpair (V' × W')) S.EPi.toAlgHom z) = 0 :=
    mapA_reduced_fwd S.EPi y0 y0' hc₁' hz
  obtain ⟨n, hn⟩ := h _ hz'
  have hnat := pairIso_mapA_mu S y0V hV y0W hW y0 hy0 y0V' hV' y0W' hW' y0' hy0'
    μx hμx μx' hμx' s hs t ht
  have h5 : K0.mapA (A := Kpair (V' × W')) (B := Kpair (V × W)) S.EPi.symm.toAlgHom
      (μx' (K0.mapA (A := Kpair V) (B := Kpair V') S.EV.toAlgHom s)
          (K0.mapA (A := Kpair W) (B := Kpair W') S.EW.toAlgHom t)) = μx s t := by
    rw [← hnat,
      eg_mapA_comp_apply (Kpair (V × W)) (Kpair (V' × W')) (Kpair (V × W)) S.EPi.toAlgHom
        S.EPi.symm.toAlgHom (μx s t),
      eg_symm_comp (Kpair (V × W)) (Kpair (V' × W')) S.EPi, eg_mapA_id' (Kpair (V × W))]
    rfl
  refine ⟨n, ?_⟩
  calc z = K0.mapA (A := Kpair (V' × W')) (B := Kpair (V × W)) S.EPi.symm.toAlgHom
        (K0.mapA (A := Kpair (V × W)) (B := Kpair (V' × W')) S.EPi.toAlgHom z) := by
        rw [eg_mapA_comp_apply (Kpair (V × W)) (Kpair (V' × W')) (Kpair (V × W)) S.EPi.toAlgHom
            S.EPi.symm.toAlgHom z,
          eg_symm_comp (Kpair (V × W)) (Kpair (V' × W')) S.EPi, eg_mapA_id' (Kpair (V × W))]
        rfl
    _ = K0.mapA (A := Kpair (V' × W')) (B := Kpair (V × W)) S.EPi.symm.toAlgHom
          (n • μx' (K0.mapA (A := Kpair V) (B := Kpair V') S.EV.toAlgHom s)
             (K0.mapA (A := Kpair W) (B := Kpair W') S.EW.toAlgHom t)) := by rw [hn]
    _ = n • K0.mapA (A := Kpair (V' × W')) (B := Kpair (V × W)) S.EPi.symm.toAlgHom
          (μx' (K0.mapA (A := Kpair V) (B := Kpair V') S.EV.toAlgHom s)
             (K0.mapA (A := Kpair W) (B := Kpair W') S.EW.toAlgHom t)) :=
        AddMonoidHom.map_zsmul
          (K0.mapA (A := Kpair (V' × W')) (B := Kpair (V × W)) S.EPi.symm.toAlgHom) n _
    _ = n • μx s t := by rw [h5]

/-! ## 4. The induction statement -/

/-- The assertion of the node for `dim W = 2*k`. -/
def egStmt (k : ℕ) : Prop :=
  ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (y0V : Ball V) (hV : y0V ∈ bdry V) (y0W : Ball W) (hW : y0W ∈ bdry W)
    (y0 : Ball (V × W)) (hy0 : y0 ∈ bdry (V × W)) (j : ℕ)
    (hVd : Module.finrank ℝ V = 2 * j) (hWd : Module.finrank ℝ W = 2 * k)
    (μx : K0 (Kpair V) →+ K0 (Kpair W) →+ K0 (Kpair (V × W)))
    (hμx : IsExtProd V W y0V y0W y0 μx) (s : K0 (Kpair V)) (t : K0 (Kpair W))
    (hs : K0.mapA (A := Kpair V) (B := ℂ) (augPair V y0V) s = 0)
    (hsg : ∀ z, K0.mapA (A := Kpair V) (B := ℂ) (augPair V y0V) z = 0 → ∃ n : ℤ, z = n • s)
    (ht : K0.mapA (A := Kpair W) (B := ℂ) (augPair W y0W) t = 0)
    (htg : ∀ z, K0.mapA (A := Kpair W) (B := ℂ) (augPair W y0W) z = 0 → ∃ n : ℤ, z = n • t),
    ∀ z, K0.mapA (A := Kpair (V × W)) (B := ℂ) (augPair (V × W) y0) z = 0 →
      ∃ n : ℤ, z = n • μx s t

/-! ## 5. Boundary points of products, and non-emptiness -/

/-- A boundary point of a product, from boundary points of the two factors. -/
def eg_prodPt {U U' : Type} [NormedAddCommGroup U] [NormedAddCommGroup U']
    (y : Ball U) (z : Ball U') : Ball (U × U') :=
  ⟨(y, z), by
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    exact max_le (mem_closedBall_zero_iff.mp y.2) (mem_closedBall_zero_iff.mp z.2)⟩

/-- `eg_prodPt` produces boundary points. -/
lemma eg_prodPt_mem_bdry {U U' : Type} [NormedAddCommGroup U] [NormedAddCommGroup U']
    {y : Ball U} (hy : y ∈ bdry U) {z : Ball U'} (hz : z ∈ bdry U') :
    eg_prodPt y z ∈ bdry (U × U') := by
  have hy' : ‖(y : U)‖ = 1 := hy
  have hz' : ‖(z : U')‖ = 1 := hz
  show ‖((eg_prodPt y z : Ball (U × U')) : U × U')‖ = 1
  rw [Prod.norm_def]
  show max ‖(y : U)‖ ‖(z : U')‖ = 1
  rw [hy', hz', max_self]

/-- In a nontrivial normed space the boundary is nonempty. -/
lemma eg_bdry_exists (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] :
    ∃ y : Ball E, y ∈ bdry E := by
  obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).mpr zero_le_one
  have hv1 : ‖v‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hv
  exact ⟨⟨v, by simp [Metric.mem_closedBall, dist_zero_right, hv1]⟩, hv1⟩

/-- The Bott base case, as a hypothesis: `K̃(Kpair R2)` is infinite cyclic.  It is supplied by
`Work.KT.EG.seed_R2` (from `Work.KT.fund_product`); nothing else in this file depends on
`ball_K`, `ballK_dim2` or the Adams-operation chain. -/
def Seed : Prop :=
  ∀ (y0R : Ball R2) (hR : y0R ∈ bdry R2), ∃ b : K0 (Kpair R2),
    K0.mapA (A := Kpair R2) (B := ℂ) (augPair R2 y0R) b = 0 ∧
    (∀ n : ℤ, n • b = 0 → n = 0) ∧
    (∀ z, K0.mapA (A := Kpair R2) (B := ℂ) (augPair R2 y0R) z = 0 → ∃ n : ℤ, z = n • b)

/-- The Bott seed: `K̃(Kpair R2) = ℤ`.  Taken from `Work.KT.EG.seed_R2`, which derives it (by
change of norm, `Work.KT.EG.transport_seed`) from the proved base case `Work.KT.ballK_dim2` of the
`D2` chain — so this line adds *no* dependency beyond `Work.KT.ballK_dim2`, which is `sorry`-free.
The alternative route `Work.KT.EG.seed_R2_fp` (via `Work.KT.fund_product` and the sphere model
`EG.S2_gen`) is a drop-in replacement for this line. -/
lemma seed_of_ballK : Seed := EG.seed_R2

/-! ## 6. The base case `dim W = 2` -/

/-- The external product of generators is a generator when `dim W = 2`. -/
theorem ext_generator_base : egStmt 1 := by
  intro V W _ _ _ _ _ _ y0V hV y0W hW y0 hy0 j hVd hWd μx hμx s t hs hsg ht htg
  have hfrR2 : Module.finrank ℝ R2 = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  obtain ⟨eW⟩ : Nonempty (W ≃ₗ[ℝ] R2) :=
    FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq.mpr (by rw [hWd, hfrR2])
  obtain ⟨S⟩ := ExtGen.pairIso_of_linearEquiv V W V R2 (LinearEquiv.refl ℝ V) eW
  obtain ⟨y0R, hy0R⟩ := eg_bdry_exists R2
  obtain ⟨y0VR, hy0VR⟩ : ∃ y : Ball (V × R2), y ∈ bdry (V × R2) :=
    ⟨eg_prodPt y0V y0R, eg_prodPt_mem_bdry hV hy0R⟩
  obtain ⟨μx₂, hμx₂⟩ := (ext_product V R2 y0V hV y0R hy0R y0VR hy0VR).1
  obtain ⟨b, hb, hbinf, hbgen⟩ := seed_of_ballK y0R hy0R
  have hsuspSurj := ExtGen.susp_bijective_surj V j hVd y0V hV y0R hy0R y0VR hy0VR
    μx₂ hμx₂ b hb hbgen hbinf
  obtain ⟨yW, hyW, hcW⟩ := S.hW y0R hy0R
  have hcW' : (augPair R2 y0R).comp S.EW.toAlgHom = augPair W y0W := by
    rw [hcW, augPair_eq_of_mem_bdry W yW y0W hyW hW]
  have ht' : K0.mapA (A := Kpair R2) (B := ℂ) (augPair R2 y0R)
      (K0.mapA (A := Kpair W) (B := Kpair R2) S.EW.toAlgHom t) = 0 :=
    mapA_reduced_fwd S.EW y0W y0R hcW' ht
  have ht'gen : ∀ w, K0.mapA (A := Kpair R2) (B := ℂ) (augPair R2 y0R) w = 0 →
      ∃ m : ℤ, w = m • (K0.mapA (A := Kpair W) (B := Kpair R2) S.EW.toAlgHom t) :=
    mapA_generates_fwd S.EW y0W y0R hcW' ht htg
  have hker : ∀ z : K0 (Kpair R2),
      (k0Rank.comp (K0.mapA (A := Kpair R2) (B := ℂ) (augPair R2 y0R))) z = 0 →
      K0.mapA (A := Kpair R2) (B := ℂ) (augPair R2 y0R) z = 0 := by
    intro z hz
    have h3 : k0Rank (K0.mapA (A := Kpair R2) (B := ℂ) (augPair R2 y0R) z) =
        k0Rank (0 : K0 ℂ) := by
      show (k0Rank.comp (K0.mapA (A := Kpair R2) (B := ℂ) (augPair R2 y0R))) z =
        k0Rank (0 : K0 ℂ)
      rw [hz, map_zero]
    exact k0RankEquiv.injective h3
  obtain ⟨ε, hε, htε⟩ := exists_eq_smul_eq_one_or_neg_one
    (k0Rank.comp (K0.mapA (A := Kpair R2) (B := ℂ) (augPair R2 y0R))) (K0.mapA (A := Kpair W) (B := Kpair R2) S.EW.toAlgHom t) b
    (by show k0Rank (K0.mapA (A := Kpair R2) (B := ℂ) (augPair R2 y0R)
          (K0.mapA (A := Kpair W) (B := Kpair R2) S.EW.toAlgHom t)) = 0
        rw [ht', map_zero])
    (by show k0Rank (K0.mapA (A := Kpair R2) (B := ℂ) (augPair R2 y0R) b) = 0
        rw [hb, map_zero])
    (fun z hz => hbgen z (hker z hz)) (fun z hz => ht'gen z (hker z hz)) hbinf
  have hεε : ε * ε = 1 := eg_sq_eq_one hε
  have hbε : b = ε • (K0.mapA (A := Kpair W) (B := Kpair R2) S.EW.toAlgHom t) := by
    rw [htε, smul_smul, hεε]
    simp
  have hmain : ∀ z', K0.mapA (A := Kpair (V × R2)) (B := ℂ) (augPair (V × R2) y0VR) z' = 0 →
      ∃ n : ℤ, z' = n • μx₂ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s)
        (K0.mapA (A := Kpair W) (B := Kpair R2) S.EW.toAlgHom t) := by
    intro z' hz'
    obtain ⟨u, hu, huz⟩ := hsuspSurj z' hz'
    obtain ⟨yV, hyV, hcV⟩ := S.hV y0V hV
    have hcV' : (augPair V y0V).comp S.EV.toAlgHom = augPair V y0V := by
      rw [hcV, augPair_eq_of_mem_bdry V yV y0V hyV hV]
    have hsgen : ∀ w, K0.mapA (A := Kpair V) (B := ℂ) (augPair V y0V) w = 0 →
        ∃ m : ℤ, w = m • (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s) :=
      mapA_generates_fwd S.EV y0V y0V hcV' hs hsg
    obtain ⟨n, hn⟩ := hsgen u hu
    refine ⟨ε * n, ?_⟩
    have hconv : μx₂ u b = (ε * n) • μx₂ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s) (K0.mapA (A := Kpair W) (B := Kpair R2) S.EW.toAlgHom t) := by
      calc μx₂ u b
          = μx₂ u (ε • (K0.mapA (A := Kpair W) (B := Kpair R2) S.EW.toAlgHom t)) := by rw [hbε]
        _ = ε • (μx₂ u (K0.mapA (A := Kpair W) (B := Kpair R2) S.EW.toAlgHom t)) := AddMonoidHom.map_zsmul (μx₂ u) ε (K0.mapA (A := Kpair W) (B := Kpair R2) S.EW.toAlgHom t)
        _ = ε • (μx₂ (n • K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s)
              (K0.mapA (A := Kpair W) (B := Kpair R2) S.EW.toAlgHom t)) := by rw [hn]
        _ = ε • (n • (μx₂ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s)
              (K0.mapA (A := Kpair W) (B := Kpair R2) S.EW.toAlgHom t))) := by
              rw [show μx₂ (n • (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s))
                    (K0.mapA (A := Kpair W) (B := Kpair R2) S.EW.toAlgHom t)
                  = (eg_eval₂ μx₂ (K0.mapA (A := Kpair W) (B := Kpair R2) S.EW.toAlgHom t))
                    (n • (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s)) from rfl,
                AddMonoidHom.map_zsmul (eg_eval₂ μx₂ (K0.mapA (A := Kpair W) (B := Kpair R2)
                  S.EW.toAlgHom t)) n (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s),
                show (eg_eval₂ μx₂ (K0.mapA (A := Kpair W) (B := Kpair R2) S.EW.toAlgHom t))
                    (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s)
                  = μx₂ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s)
                    (K0.mapA (A := Kpair W) (B := Kpair R2) S.EW.toAlgHom t) from rfl]
        _ = (ε * n) • μx₂ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s)
              (K0.mapA (A := Kpair W) (B := Kpair R2) S.EW.toAlgHom t) :=
            smul_smul ε n (μx₂ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s)
              (K0.mapA (A := Kpair W) (B := Kpair R2) S.EW.toAlgHom t))
    calc z' = μx₂ u b := huz.symm
      _ = (ε * n) • μx₂ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s)
            (K0.mapA (A := Kpair W) (B := Kpair R2) S.EW.toAlgHom t) := hconv
  exact eg_transport S y0V hV y0W hW y0 hy0 y0V hV y0R hy0R y0VR hy0VR
    μx hμx μx₂ hμx₂ s hs t ht hmain


/-! ## 6b. Generators of the reduced group in every even dimension -/

/-- Reversed augmentation compatibility of an algebra isomorphism of `Kpair`s. -/
lemma eg_aug_symm {U U' : Type} [NormedAddCommGroup U] [NormedAddCommGroup U']
    (E : Kpair U ≃ₐ[ℂ] Kpair U') (y : Ball U) (y' : Ball U')
    (h : (augPair U' y').comp E.toAlgHom = augPair U y) :
    (augPair U y).comp E.symm.toAlgHom = augPair U' y' := by
  ext x
  rw [AlgHom.comp_apply, ← h, AlgHom.comp_apply]
  exact congrArg (fun w => (augPair U' y') w) (E.apply_symm_apply x)

/-- Reduced generators transport backwards along an isomorphism of `Kpair`s. -/
lemma eg_gen_transfer_bwd {U U' : Type} [NormedAddCommGroup U] [NormedAddCommGroup U']
    (E : Kpair U ≃ₐ[ℂ] Kpair U') (y : Ball U) (y' : Ball U')
    (h : (augPair U' y').comp E.toAlgHom = augPair U y)
    {g : K0 (Kpair U')}
    (hg : K0.mapA (A := Kpair U') (B := ℂ) (augPair U' y') g = 0)
    (hginf : ∀ n : ℤ, n • g = 0 → n = 0)
    (hggen : ∀ z, K0.mapA (A := Kpair U') (B := ℂ) (augPair U' y') z = 0 →
      ∃ n : ℤ, z = n • g) :
    ∃ g' : K0 (Kpair U), K0.mapA (A := Kpair U) (B := ℂ) (augPair U y) g' = 0 ∧
      (∀ n : ℤ, n • g' = 0 → n = 0) ∧
      (∀ z, K0.mapA (A := Kpair U) (B := ℂ) (augPair U y) z = 0 → ∃ n : ℤ, z = n • g') := by
  have h' : (augPair U y).comp E.symm.toAlgHom = augPair U' y' := eg_aug_symm E y y' h
  refine ⟨K0.mapA (A := Kpair U') (B := Kpair U) E.symm.toAlgHom g,
    mapA_reduced_bwd E y y' h hg, ?_, ?_⟩
  · intro n hn
    apply hginf n
    have h1 : K0.mapA (A := Kpair U) (B := Kpair U') E.toAlgHom
        (K0.mapA (A := Kpair U') (B := Kpair U) E.symm.toAlgHom g) = g := by
      rw [eg_mapA_comp_apply (Kpair U') (Kpair U) (Kpair U') E.symm.toAlgHom E.toAlgHom g,
        eg_comp_symm (Kpair U) (Kpair U') E, eg_mapA_id' (Kpair U')]
      rfl
    calc n • g = n • K0.mapA (A := Kpair U) (B := Kpair U') E.toAlgHom
            (K0.mapA (A := Kpair U') (B := Kpair U) E.symm.toAlgHom g) := by rw [h1]
      _ = K0.mapA (A := Kpair U) (B := Kpair U') E.toAlgHom
            (n • K0.mapA (A := Kpair U') (B := Kpair U) E.symm.toAlgHom g) :=
          (AddMonoidHom.map_zsmul (K0.mapA (A := Kpair U) (B := Kpair U') E.toAlgHom) n _).symm
      _ = 0 := by rw [hn, map_zero]
  · intro z hz
    exact mapA_generates_fwd E.symm y' y h' hg hggen z hz

/-- In every even dimension the reduced group of `Kpair V` is generated by a class of infinite
order, given the Bott seed (by induction: `V ≅ Std (2j) × R2` and the suspension isomorphism). -/
theorem gen_even_aux (hs : Seed) : ∀ i, 1 ≤ i → ∀ (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (y0 : Ball V) (hy0 : y0 ∈ bdry V),
    Module.finrank ℝ V = 2 * i →
    ∃ g : K0 (Kpair V), K0.mapA (A := Kpair V) (B := ℂ) (augPair V y0) g = 0 ∧
      (∀ z, K0.mapA (A := Kpair V) (B := ℂ) (augPair V y0) z = 0 → ∃ n : ℤ, z = n • g) := by
  intro i
  induction i with
  | zero => intro hi; exact absurd hi (by omega)
  | succ j ih =>
    intro _ V _ _ _ y0 hy0 hV
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      have hV2 : Module.finrank ℝ V = 2 := by rw [hV]
      have hfrR2 : Module.finrank ℝ R2 = 2 := by rw [Module.finrank_prod, Module.finrank_self]
      obtain ⟨e⟩ : Nonempty (V ≃ₗ[ℝ] R2) :=
        FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq.mpr (by rw [hV2, hfrR2])
      obtain ⟨S⟩ := ExtGen.pairIso_of_linearEquiv V V R2 R2 e e
      obtain ⟨y0R, hy0R⟩ := eg_bdry_exists R2
      obtain ⟨y, hy, hc⟩ := S.hV y0R hy0R
      have hc' : (augPair R2 y0R).comp S.EV.toAlgHom = augPair V y0 := by
        rw [hc, augPair_eq_of_mem_bdry V y y0 hy hy0]
      obtain ⟨b, hb, _hbinf, hbgen⟩ := hs y0R hy0R
      refine ⟨K0.mapA (A := Kpair R2) (B := Kpair V) S.EV.symm.toAlgHom b,
        mapA_reduced_bwd S.EV y0 y0R hc' hb, ?_⟩
      intro z hz
      exact mapA_generates_fwd S.EV.symm y0R y0 (eg_aug_symm S.EV y0 y0R hc') hb hbgen z hz
    · have hfrStd : Module.finrank ℝ (Std (2 * j)) = 2 * j := Module.finrank_fin_fun ℝ
      haveI : Nonempty (Fin (2 * j)) :=
        ⟨⟨0, Nat.mul_pos (by norm_num) (Nat.lt_of_lt_of_le Nat.zero_lt_one hjpos)⟩⟩
      haveI : Nontrivial (Std (2 * j)) := inferInstance
      obtain ⟨e⟩ : Nonempty (V ≃ₗ[ℝ] (Std (2 * j) × R2)) := by
        have h := ExtGen.peel V (j + 1) (by omega) hV
        rw [show 2 * ((j + 1) - 1) = 2 * j from by omega] at h
        exact h
      obtain ⟨S⟩ := ExtGen.pairIso_of_linearEquiv V V (Std (2 * j) × R2) (Std (2 * j) × R2) e e
      obtain ⟨y0W, hy0W⟩ := eg_bdry_exists (Std (2 * j))
      obtain ⟨y0R, hy0R⟩ := eg_bdry_exists R2
      obtain ⟨y0W1, hy0W1⟩ : ∃ y : Ball (Std (2 * j) × R2), y ∈ bdry (Std (2 * j) × R2) :=
        ⟨eg_prodPt y0W y0R, eg_prodPt_mem_bdry hy0W hy0R⟩
      obtain ⟨g₀, hg₀, hg₀gen⟩ := ih hjpos (Std (2 * j)) y0W hy0W hfrStd
      obtain ⟨b, hb, hbinf, hbgen⟩ := hs y0R hy0R
      obtain ⟨μx, hμx⟩ := (ext_product (Std (2 * j)) R2 y0W hy0W y0R hy0R y0W1 hy0W1).1
      have hsurj := ExtGen.susp_bijective_surj (Std (2 * j)) j hfrStd y0W hy0W y0R hy0R
        y0W1 hy0W1 μx hμx b hb hbgen hbinf
      have hred : K0.mapA (A := Kpair (Std (2 * j) × R2)) (B := ℂ)
          (augPair (Std (2 * j) × R2) y0W1) (μx g₀ b) = 0 := (hμx g₀ b hg₀ hb).1
      have hgen : ∀ z, K0.mapA (A := Kpair (Std (2 * j) × R2)) (B := ℂ)
          (augPair (Std (2 * j) × R2) y0W1) z = 0 → ∃ n : ℤ, z = n • μx g₀ b := by
        intro z hz
        obtain ⟨u, hu, huz⟩ := hsurj z hz
        obtain ⟨n, hn⟩ := hg₀gen u hu
        refine ⟨n, ?_⟩
        rw [← huz, hn, show μx (n • g₀) b = (eg_eval₂ μx b) (n • g₀) from rfl,
          AddMonoidHom.map_zsmul (eg_eval₂ μx b) n g₀]
        rfl
      obtain ⟨yW, hyW, hcW⟩ := S.hW y0W1 hy0W1
      have hcW' : (augPair (Std (2 * j) × R2) y0W1).comp S.EW.toAlgHom = augPair V y0 := by
        rw [hcW, augPair_eq_of_mem_bdry V yW y0 hyW hy0]
      refine ⟨K0.mapA (A := Kpair (Std (2 * j) × R2)) (B := Kpair V) S.EW.symm.toAlgHom
          (μx g₀ b), mapA_reduced_bwd S.EW y0 y0W1 hcW' hred, ?_⟩
      intro z hz
      exact mapA_generates_fwd S.EW.symm y0W1 y0 (eg_aug_symm S.EW y0 y0W1 hcW')
        hred hgen z hz

/-! ## 7. The induction step -/

/-- The induction step: from `dim W = 2k` deduce `dim W = 2(k+1)`, `k ≥ 1`. -/
theorem eg_step (k : ℕ) (hk : 1 ≤ k) (ih : egStmt k) : egStmt (k + 1) := by
  intro V W _ _ _ _ _ _ y0V hV y0W hW y0 hy0 j hVd hWd μx hμx s t hs hsg ht htg
  obtain ⟨eW⟩ : Nonempty (W ≃ₗ[ℝ] (Std (2 * k) × R2)) := by
    have h := ExtGen.peel W (k + 1) (by omega) hWd
    rw [show 2 * ((k + 1) - 1) = 2 * k from by omega] at h
    exact h
  obtain ⟨S⟩ := ExtGen.pairIso_of_linearEquiv V W V (Std (2 * k) × R2)
    (LinearEquiv.refl ℝ V) eW
  haveI : Nonempty (Fin (2 * k)) :=
    ⟨⟨0, Nat.mul_pos (by norm_num) (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)⟩⟩
  haveI : Nontrivial (Std (2 * k)) := inferInstance
  obtain ⟨y0W₀, hy0W₀⟩ := eg_bdry_exists (Std (2 * k))
  obtain ⟨y0R, hy0R⟩ := eg_bdry_exists R2
  obtain ⟨y0W₁, hy0W₁⟩ : ∃ y : Ball (Std (2 * k) × R2), y ∈ bdry (Std (2 * k) × R2) :=
    ⟨eg_prodPt y0W₀ y0R, eg_prodPt_mem_bdry hy0W₀ hy0R⟩
  obtain ⟨y0VW₀, hy0VW₀⟩ : ∃ y : Ball (V × Std (2 * k)), y ∈ bdry (V × Std (2 * k)) :=
    ⟨eg_prodPt y0V y0W₀, eg_prodPt_mem_bdry hV hy0W₀⟩
  obtain ⟨y0VW₁, hy0VW₁⟩ :
      ∃ y : Ball (V × (Std (2 * k) × R2)), y ∈ bdry (V × (Std (2 * k) × R2)) :=
    ⟨eg_prodPt y0V y0W₁, eg_prodPt_mem_bdry hV hy0W₁⟩
  obtain ⟨y0VW₀R, hy0VW₀R⟩ :
      ∃ y : Ball ((V × Std (2 * k)) × R2), y ∈ bdry ((V × Std (2 * k)) × R2) :=
    ⟨eg_prodPt y0VW₀ y0R, eg_prodPt_mem_bdry hy0VW₀ hy0R⟩
  have hfrR2 : Module.finrank ℝ R2 = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  have hfrW₀ : Module.finrank ℝ (Std (2 * k)) = 2 * k := Module.finrank_fin_fun ℝ
  have hfrV : Module.finrank ℝ (V × Std (2 * k)) = 2 * (j + k) := by
    rw [Module.finrank_prod, hVd, hfrW₀]
    omega
  obtain ⟨μx₁, hμx₁⟩ := (ext_product V (Std (2 * k) × R2) y0V hV y0W₁ hy0W₁ y0VW₁ hy0VW₁).1
  obtain ⟨μx₀, hμx₀⟩ := (ext_product V (Std (2 * k)) y0V hV y0W₀ hy0W₀ y0VW₀ hy0VW₀).1
  obtain ⟨μx₃, hμx₃⟩ := (ext_product (Std (2 * k)) R2 y0W₀ hy0W₀ y0R hy0R y0W₁ hy0W₁).1
  obtain ⟨μx₂, hμx₂⟩ := (ext_product (V × Std (2 * k)) R2 y0VW₀ hy0VW₀ y0R hy0R y0VW₀R hy0VW₀R).1
  obtain ⟨t₀, ht₀, ht₀gen⟩ :=
    gen_even_aux seed_of_ballK k hk (Std (2 * k)) y0W₀ hy0W₀ hfrW₀
  obtain ⟨b, hb, hbinf, hbgen⟩ := seed_of_ballK y0R hy0R
  have hsuspSurj := ExtGen.susp_bijective_surj (V × Std (2 * k)) (j + k) hfrV
    y0VW₀ hy0VW₀ y0R hy0R y0VW₀R hy0VW₀R μx₂ hμx₂ b hb hbgen hbinf
  obtain ⟨yW, hyW, hcW⟩ := S.hW y0W₁ hy0W₁
  have hcW' : (augPair (Std (2 * k) × R2) y0W₁).comp S.EW.toAlgHom = augPair W y0W := by
    rw [hcW, augPair_eq_of_mem_bdry W yW y0W hyW hW]
  have ht' : K0.mapA (A := Kpair (Std (2 * k) × R2)) (B := ℂ)
      (augPair (Std (2 * k) × R2) y0W₁)
      (K0.mapA (A := Kpair W) (B := Kpair (Std (2 * k) × R2)) S.EW.toAlgHom t) = 0 :=
    mapA_reduced_fwd S.EW y0W y0W₁ hcW' ht
  have ht'gen : ∀ w, K0.mapA (A := Kpair (Std (2 * k) × R2)) (B := ℂ)
      (augPair (Std (2 * k) × R2) y0W₁) w = 0 →
      ∃ m : ℤ, w = m • (K0.mapA (A := Kpair W) (B := Kpair (Std (2 * k) × R2))
        S.EW.toAlgHom t) :=
    mapA_generates_fwd S.EW y0W y0W₁ hcW' ht htg
  obtain ⟨yV, hyV, hcV⟩ := S.hV y0V hV
  have hcV' : (augPair V y0V).comp S.EV.toAlgHom = augPair V y0V := by
    rw [hcV, augPair_eq_of_mem_bdry V yV y0V hyV hV]
  have hs' : K0.mapA (A := Kpair V) (B := ℂ) (augPair V y0V)
      (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s) = 0 :=
    mapA_reduced_fwd S.EV y0V y0V hcV' hs
  have hs'gen : ∀ w, K0.mapA (A := Kpair V) (B := ℂ) (augPair V y0V) w = 0 →
      ∃ m : ℤ, w = m • (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s) :=
    mapA_generates_fwd S.EV y0V y0V hcV' hs hsg
  have hred₃ : K0.mapA (A := Kpair (Std (2 * k) × R2)) (B := ℂ)
      (augPair (Std (2 * k) × R2) y0W₁) (μx₃ t₀ b) = 0 := (hμx₃ t₀ b ht₀ hb).1
  have hassoc := ExtGen.ext_nesting V (Std (2 * k)) R2 y0V hV y0W₀ hy0W₀ y0R hy0R
    y0VW₀ hy0VW₀ y0W₁ hy0W₁ y0VW₁ hy0VW₁ y0VW₀R hy0VW₀R
    μx₀ hμx₀ μx₃ hμx₃ μx₁ hμx₁ μx₂ hμx₂ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s) hs' t₀ ht₀ b hb
  have hmain : ∀ z', K0.mapA (A := Kpair (V × (Std (2 * k) × R2))) (B := ℂ)
      (augPair (V × (Std (2 * k) × R2)) y0VW₁) z' = 0 → ∃ n : ℤ, z' = n • μx₁ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s) (K0.mapA (A := Kpair W) (B := Kpair (Std (2 * k) × R2)) S.EW.toAlgHom t) := by
    intro z' hz'
    set z'' : K0 (Kpair ((V × Std (2 * k)) × R2)) :=
      K0.mapA (A := Kpair (V × (Std (2 * k) × R2))) (B := Kpair ((V × Std (2 * k)) × R2))
        (pairAssocEquiv V (Std (2 * k)) R2).symm.toAlgHom z' with hz''def
    have hz''A : K0.mapA (A := Kpair ((V × Std (2 * k)) × R2)) (B := ℂ)
        (augPair ((V × Std (2 * k)) × R2) (ballAssoc V (Std (2 * k)) R2 y0VW₁)) z'' = 0 := by
      rw [hz''def]
      refine mapA_reduced_fwd (pairAssocEquiv V (Std (2 * k)) R2).symm y0VW₁
        (ballAssoc V (Std (2 * k)) R2 y0VW₁) ?_ hz'
      have h2 : ((augPair (V × (Std (2 * k) × R2)) y0VW₁).comp
          (pairAssocEquiv V (Std (2 * k)) R2).toAlgHom).comp
          (pairAssocEquiv V (Std (2 * k)) R2).symm.toAlgHom =
          (augPair ((V × Std (2 * k)) × R2) (ballAssoc V (Std (2 * k)) R2 y0VW₁)).comp
            (pairAssocEquiv V (Std (2 * k)) R2).symm.toAlgHom := by
        rw [ExtGen.augPair_comp_pairAssocEquiv V (Std (2 * k)) R2 y0VW₁]
      rw [AlgHom.comp_assoc,
        eg_comp_symm (Kpair ((V × Std (2 * k)) × R2)) (Kpair (V × (Std (2 * k) × R2)))
          (pairAssocEquiv V (Std (2 * k)) R2),
        AlgHom.comp_id] at h2
      exact h2.symm
    have hz''red : K0.mapA (A := Kpair ((V × Std (2 * k)) × R2)) (B := ℂ)
        (augPair ((V × Std (2 * k)) × R2) y0VW₀R) z'' = 0 := by
      rw [mapA_augPair_apply_eq_of_mem_bdry ((V × Std (2 * k)) × R2)
        y0VW₀R (ballAssoc V (Std (2 * k)) R2 y0VW₁)
        hy0VW₀R ((ExtGen.bdry_ballAssoc_iff V (Std (2 * k)) R2 y0VW₁).mpr hy0VW₁)]
      exact hz''A
    obtain ⟨u, hu, huz⟩ := hsuspSurj z'' hz''red
    obtain ⟨m, hm⟩ := ih V (Std (2 * k)) y0V hV y0W₀ hy0W₀ y0VW₀ hy0VW₀ j hVd hfrW₀
      μx₀ hμx₀ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s) t₀ hs' hs'gen ht₀ ht₀gen u hu
    have hz''eq : z'' = m • (μx₂ (μx₀ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s) t₀) b) := by
      calc z'' = μx₂ u b := huz.symm
        _ = μx₂ (m • μx₀ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s) t₀) b := by rw [hm]
        _ = m • (μx₂ (μx₀ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s) t₀) b) := by
            rw [show μx₂ (m • μx₀ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s) t₀) b
                  = (eg_eval₂ μx₂ b) (m • μx₀ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s) t₀) from rfl,
              AddMonoidHom.map_zsmul (eg_eval₂ μx₂ b) m
                (μx₀ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s) t₀),
              show (eg_eval₂ μx₂ b)
                    (μx₀ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s) t₀)
                  = μx₂ (μx₀ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s) t₀) b from rfl]
    have hz'eq : z' = m • μx₁ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s) (μx₃ t₀ b) := by
      calc z' = K0.mapA (A := Kpair ((V × Std (2 * k)) × R2))
            (B := Kpair (V × (Std (2 * k) × R2)))
            (pairAssocEquiv V (Std (2 * k)) R2).toAlgHom z'' := by
              rw [hz''def,
                eg_mapA_comp_apply (Kpair (V × (Std (2 * k) × R2)))
                  (Kpair ((V × Std (2 * k)) × R2)) (Kpair (V × (Std (2 * k) × R2)))
                  (pairAssocEquiv V (Std (2 * k)) R2).symm.toAlgHom
                  (pairAssocEquiv V (Std (2 * k)) R2).toAlgHom z',
                eg_comp_symm (Kpair ((V × Std (2 * k)) × R2))
                  (Kpair (V × (Std (2 * k) × R2))) (pairAssocEquiv V (Std (2 * k)) R2),
                eg_mapA_id' (Kpair (V × (Std (2 * k) × R2)))]
              rfl
        _ = K0.mapA (A := Kpair ((V × Std (2 * k)) × R2))
              (B := Kpair (V × (Std (2 * k) × R2)))
              (pairAssocEquiv V (Std (2 * k)) R2).toAlgHom
              (m • (μx₂ (μx₀ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s) t₀) b)) := by rw [hz''eq]
        _ = m • K0.mapA (A := Kpair ((V × Std (2 * k)) × R2))
              (B := Kpair (V × (Std (2 * k) × R2)))
              (pairAssocEquiv V (Std (2 * k)) R2).toAlgHom (μx₂ (μx₀ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s) t₀) b) :=
            AddMonoidHom.map_zsmul _ m _
        _ = m • μx₁ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s) (μx₃ t₀ b) := by rw [hassoc]
    obtain ⟨m₀, hm₀⟩ := ht'gen (μx₃ t₀ b) hred₃
    refine ⟨m * m₀, ?_⟩
    have hconv : μx₁ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s) (μx₃ t₀ b)
        = m₀ • μx₁ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s)
            (K0.mapA (A := Kpair W) (B := Kpair (Std (2 * k) × R2)) S.EW.toAlgHom t) := by
      rw [hm₀]
      exact AddMonoidHom.map_zsmul
        (μx₁ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s)) m₀
        (K0.mapA (A := Kpair W) (B := Kpair (Std (2 * k) × R2)) S.EW.toAlgHom t)
    calc z' = m • μx₁ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s) (μx₃ t₀ b) :=
          hz'eq
      _ = m • (m₀ • μx₁ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s)
            (K0.mapA (A := Kpair W) (B := Kpair (Std (2 * k) × R2)) S.EW.toAlgHom t)) := by
          rw [hconv]
      _ = (m * m₀) • μx₁ (K0.mapA (A := Kpair V) (B := Kpair V) S.EV.toAlgHom s)
            (K0.mapA (A := Kpair W) (B := Kpair (Std (2 * k) × R2)) S.EW.toAlgHom t) :=
          smul_smul m m₀ _
  exact eg_transport S y0V hV y0W hW y0 hy0 y0V hV y0W₁ hy0W₁ y0VW₁ hy0VW₁
    μx hμx μx₁ hμx₁ s hs t ht hmain

/-! ## 8. The induction -/

/-- The induction over `k`. -/
theorem ext_generator_aux : ∀ k, egStmt k := by
  intro k
  induction k with
  | zero =>
    intro V W _ _ _ _ _ _ y0V hV y0W hW y0 hy0 j hVd hWd μx hμx s t hs hsg ht htg z hz
    have h0 : Module.finrank ℝ W = 0 := by simp [hWd]
    haveI : Subsingleton W := Module.finrank_zero_iff.mp h0
    have hW0 : (y0W : W) = 0 := Subsingleton.elim _ _
    have hz0 : ‖(y0W : W)‖ = 0 := by rw [hW0, norm_zero]
    have hW1 : ‖(y0W : W)‖ = 1 := hW
    exact absurd (hW1.symm.trans hz0 : (1 : ℝ) = 0) (by norm_num)
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0]; exact ext_generator_base
    · exact eg_step k hkpos ih

end

end Work.KT

namespace Work.KT

/-- For even-dimensional `V`, `W` the external product of generators of `K̃(S^{dim V})` and
`K̃(S^{dim W})` generates `K̃(S^{dim V + dim W})`. -/
theorem ext_generator (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (y0V : Ball V) (hV : y0V ∈ bdry V) (y0W : Ball W) (hW : y0W ∈ bdry W)
    (y0 : Ball (V × W)) (hy0 : y0 ∈ bdry (V × W)) (j k : ℕ)
    (hVd : Module.finrank ℝ V = 2 * j) (hWd : Module.finrank ℝ W = 2 * k)
    (μx : K0 (Kpair V) →+ K0 (Kpair W) →+ K0 (Kpair (V × W)))
    (hμx : IsExtProd V W y0V y0W y0 μx) (s : K0 (Kpair V)) (t : K0 (Kpair W))
    (hs : K0.mapA (augPair V y0V) s = 0)
    (hsg : ∀ z, K0.mapA (augPair V y0V) z = 0 → ∃ n : ℤ, z = n • s)
    (ht : K0.mapA (augPair W y0W) t = 0)
    (htg : ∀ z, K0.mapA (augPair W y0W) z = 0 → ∃ n : ℤ, z = n • t) :
    ∀ z, K0.mapA (augPair (V × W) y0) z = 0 → ∃ n : ℤ, z = n • μx s t :=
  ext_generator_aux k V W y0V hV y0W hW y0 hy0 j hVd hWd μx hμx s t hs hsg ht htg

end Work.KT
