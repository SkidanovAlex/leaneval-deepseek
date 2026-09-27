import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.HopfK.Basic
import Submission.Work.KT.homotopy_inv

namespace Work.KT

open Matrix
open scoped Topology

noncomputable section

/-! ## The radial self-map of the ball -/

private def hkRcVec (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (t : ℝ) (z : V) : V :=
  (1 - t) • z + t • ((max ‖z‖ (1 / 2 : ℝ))⁻¹ • z)

private lemma hkRcVec_zero (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (z : V) :
    hkRcVec V 0 z = z := by
  simp [hkRcVec]

private lemma hkRcVec_one {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {z : V} (hz : (1 : ℝ) / 2 ≤ ‖z‖) : hkRcVec V 1 z = ‖z‖⁻¹ • z := by
  rw [hkRcVec, sub_self, zero_smul, zero_add, one_smul, max_eq_left hz]

private lemma hkRcVec_bdry {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (t : ℝ) {y : V} (hy : ‖y‖ = 1) : hkRcVec V t y = y := by
  rw [hkRcVec, hy, max_eq_left (by norm_num : ((1 : ℝ) / 2) ≤ 1), inv_one, one_smul,
    ← add_smul, sub_add_cancel, one_smul]

private lemma hkRcVec_norm_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {z : V} (hz : ‖z‖ ≤ 1) : ‖hkRcVec V t z‖ ≤ 1 := by
  have h1 : (0:ℝ) < max ‖z‖ (1/2:ℝ) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hpsi : ‖(max ‖z‖ (1/2:ℝ))⁻¹ • z‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr h1.le)]
    calc (max ‖z‖ (1/2:ℝ))⁻¹ * ‖z‖ ≤ (max ‖z‖ (1/2:ℝ))⁻¹ * max ‖z‖ (1/2:ℝ) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (inv_nonneg.mpr h1.le)
      _ = 1 := inv_mul_cancel₀ h1.ne'
  rw [hkRcVec]
  calc ‖(1 - t) • z + t • ((max ‖z‖ (1/2:ℝ))⁻¹ • z)‖
      ≤ ‖(1 - t) • z‖ + ‖t • ((max ‖z‖ (1/2:ℝ))⁻¹ • z)‖ := norm_add_le _ _
    _ = (1 - t) * ‖z‖ + t * ‖(max ‖z‖ (1/2:ℝ))⁻¹ • z‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg ht0]
    _ ≤ (1 - t) * 1 + t * 1 := by gcongr
    _ = 1 := by ring

private lemma hkRcVec_continuous (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    Continuous fun p : unitInterval × Ball V => hkRcVec V (p.1 : ℝ) (p.2 : V) := by
  unfold hkRcVec
  have hz : Continuous fun p : unitInterval × Ball V => (p.2 : V) :=
    continuous_subtype_val.comp continuous_snd
  have hn : Continuous fun p : unitInterval × Ball V => ‖(p.2 : V)‖ := hz.norm
  have hm : Continuous fun p : unitInterval × Ball V => max ‖(p.2 : V)‖ (1/2:ℝ) :=
    hn.max continuous_const
  have hinv : Continuous fun p : unitInterval × Ball V => (max ‖(p.2 : V)‖ (1/2:ℝ))⁻¹ :=
    hm.inv₀ (fun p => by positivity)
  have h1 : Continuous fun p : unitInterval × Ball V => (1 - (p.1 : ℝ)) :=
    continuous_const.sub (continuous_subtype_val.comp continuous_fst)
  exact (h1.smul hz).add ((continuous_subtype_val.comp continuous_fst).smul (hinv.smul hz))

private def hkRcMap (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    C(unitInterval × Ball V, Ball V) where
  toFun p := ⟨hkRcVec V (p.1 : ℝ) (p.2 : V), by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    refine hkRcVec_norm_le V (p.1 : ℝ) p.1.2.1 p.1.2.2 ?_
    have h := p.2.2
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
    exact h⟩
  continuous_toFun := Continuous.subtype_mk (hkRcVec_continuous V) _

private lemma hkRcMap_zero (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (z : Ball V) :
    hkRcMap V (0, z) = z := by
  apply Subtype.ext
  change hkRcVec V ((0 : unitInterval) : ℝ) (z : V) = (z : V)
  rw [show ((0 : unitInterval) : ℝ) = 0 from rfl]
  exact hkRcVec_zero V (z : V)

private lemma hkRcMap_bdry (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (t : unitInterval) (y : Ball V) (hy : y ∈ bdry V) : hkRcMap V (t, y) = y := by
  apply Subtype.ext
  change hkRcVec V ((t : unitInterval) : ℝ) (y : V) = (y : V)
  exact hkRcVec_bdry ((t : unitInterval) : ℝ) hy

private lemma hkRcMap_one (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (z : Ball V) (hz : (1 : ℝ) / 2 ≤ ‖(z : V)‖) :
    ((hkRcMap V (1, z) : Ball V) : V) = ((normPtBall z : Ball V) : V) := by
  rw [normPtBall_coe]
  change hkRcVec V ((1 : unitInterval) : ℝ) (z : V) = (‖(z : V)‖)⁻¹ • (z : V)
  rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]
  exact hkRcVec_one hz

/-! ## The crux: homotopy invariance under a path of algebra endomorphisms -/

private lemma hkRcClsEqOfHomotopicEndo {𝔄 : Type} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄]
    [CompleteSpace 𝔄] (A : Subalgebra ℂ 𝔄) (hA : IsClosed (A : Set 𝔄)) (n : ℕ)
    (P : Matrix (Fin n) (Fin n) A) (hP : P * P = P)
    (Ψ : unitInterval → A →ₐ[ℂ] A)
    (hΨ : ∀ a : A, Continuous fun t : unitInterval => Ψ t a)
    (h0 : ∀ a : A, Ψ 0 a = a) :
    cls (⟨n, P⟩ : Mat A) = cls (⟨n, P.map (Ψ 1)⟩) := by
  have hcont : Continuous fun t : unitInterval => P.map (Ψ t) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simpa only [Matrix.map_apply] using hΨ (P i j)
  have hidem : ∀ t : unitInterval, P.map (Ψ t) * P.map (Ψ t) = P.map (Ψ t) := by
    intro t
    rw [← Matrix.map_mul, hP]
  have hmain := homotopy_inv 𝔄 A hA n (fun t : unitInterval => P.map (Ψ t)) hcont hidem
  have h0' : P.map (Ψ 0) = P := by
    funext i j
    exact h0 (P i j)
  rw [h0'] at hmain
  exact hmain

private lemma hkRcConeClosed (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) :
    IsClosed ((coneAlg f : Subalgebra ℂ (C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ))) :
      Set (C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ))) := by
  have hset : ((coneAlg f : Subalgebra ℂ (C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ))) :
        Set (C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ))) =
      ⋂ (y : Ball (Eu m × Eu m)) (hy : ‖(y : Eu m × Eu m)‖ = 1),
        {z : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ) |
          z.2 y = z.1 (f ⟨(y : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy⟩)} := by
    ext z; simp [coneAlg, Set.mem_iInter]
  rw [hset]
  refine isClosed_iInter fun y => isClosed_iInter fun hy => isClosed_eq ?_ ?_
  · fun_prop
  · fun_prop

/-! ## The pull-back endomorphism of the cone algebra -/

private def hkRcPsiAmb (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (φ : C(unitInterval × Ball (Eu m × Eu m), Ball (Eu m × Eu m))) (t : unitInterval) :
    (C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)) →ₐ[ℂ]
      (C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)) :=
  AlgHom.prod (AlgHom.fst ℂ (C(Tgt m, ℂ)) (C(Ball (Eu m × Eu m), ℂ)))
    ((pullAlg (φ.curry t)).comp
      (AlgHom.snd ℂ (C(Tgt m, ℂ)) (C(Ball (Eu m × Eu m), ℂ))))

private lemma hkRcPsiAmb_apply (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (φ : C(unitInterval × Ball (Eu m × Eu m), Ball (Eu m × Eu m))) (t : unitInterval)
    (z : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)) :
    hkRcPsiAmb m f φ t z = (z.1, z.2.comp (φ.curry t)) := rfl

private def hkRcPsi (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (φ : C(unitInterval × Ball (Eu m × Eu m), Ball (Eu m × Eu m)))
    (hφb : ∀ (t : unitInterval) (y : Ball (Eu m × Eu m)),
      y ∈ bdry (Eu m × Eu m) → φ (t, y) = y)
    (t : unitInterval) : coneAlg f →ₐ[ℂ] coneAlg f :=
  AlgHom.codRestrict ((hkRcPsiAmb m f φ t).comp (coneAlg f).val) (coneAlg f) (by
    intro a y hy
    simp only [AlgHom.comp_apply, hkRcPsiAmb_apply]
    rw [ContinuousMap.comp_apply]
    rw [show (φ.curry t) y = y from by rw [ContinuousMap.curry_apply]; exact hφb t y hy]
    exact a.property y hy)

private lemma hkRcPsi_val (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (φ : C(unitInterval × Ball (Eu m × Eu m), Ball (Eu m × Eu m)))
    (hφb : ∀ (t : unitInterval) (y : Ball (Eu m × Eu m)),
      y ∈ bdry (Eu m × Eu m) → φ (t, y) = y)
    (t : unitInterval) (a : coneAlg f) :
    ((hkRcPsi m f φ hφb t a : coneAlg f) :
        C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)) =
      hkRcPsiAmb m f φ t (a : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)) := rfl

private lemma hkRcPsi_val' (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (φ : C(unitInterval × Ball (Eu m × Eu m), Ball (Eu m × Eu m)))
    (hφb : ∀ (t : unitInterval) (y : Ball (Eu m × Eu m)),
      y ∈ bdry (Eu m × Eu m) → φ (t, y) = y)
    (t : unitInterval) (a : coneAlg f) :
    ((hkRcPsi m f φ hφb t a : coneAlg f) :
        C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)) =
      ((a : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)).1,
        (a : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)).2.comp (φ.curry t)) := by
  rw [hkRcPsi_val, hkRcPsiAmb_apply]

private lemma hkRcPsi_zero (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (φ : C(unitInterval × Ball (Eu m × Eu m), Ball (Eu m × Eu m)))
    (hφb : ∀ (t : unitInterval) (y : Ball (Eu m × Eu m)),
      y ∈ bdry (Eu m × Eu m) → φ (t, y) = y)
    (hφ0 : ∀ z : Ball (Eu m × Eu m), φ (0, z) = z) :
    ∀ a : coneAlg f, hkRcPsi m f φ hφb 0 a = a := by
  intro a
  apply Subtype.ext
  rw [hkRcPsi_val']
  refine Prod.ext rfl ?_
  have hcurry : φ.curry 0 = ContinuousMap.id (Ball (Eu m × Eu m)) := by
    apply ContinuousMap.ext
    intro z
    rw [ContinuousMap.curry_apply]
    exact hφ0 z
  rw [hcurry, ContinuousMap.comp_id]

private lemma hkRcPsi_continuous (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (φ : C(unitInterval × Ball (Eu m × Eu m), Ball (Eu m × Eu m)))
    (hφb : ∀ (t : unitInterval) (y : Ball (Eu m × Eu m)),
      y ∈ bdry (Eu m × Eu m) → φ (t, y) = y) :
    ∀ a : coneAlg f, Continuous fun t : unitInterval => hkRcPsi m f φ hφb t a := by
  intro a
  have h2 : Continuous fun t : unitInterval =>
      (((a : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)).2).comp (φ.curry t)) := by
    have h : Continuous fun t : unitInterval =>
        ((((a : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)).2).comp φ).curry) t :=
      (((a : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)).2).comp φ).curry.continuous
    refine h.congr (fun t => ?_)
    apply ContinuousMap.ext
    intro z
    simp only [ContinuousMap.curry_apply, ContinuousMap.comp_apply]
  have hmain : Continuous fun t : unitInterval =>
      hkRcPsiAmb m f φ t (a : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)) := by
    have heq : (fun t : unitInterval =>
        hkRcPsiAmb m f φ t (a : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ))) =
        (fun t : unitInterval => ((a : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)).1,
          ((a : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)).2).comp (φ.curry t))) := by
      funext t
      exact hkRcPsiAmb_apply m f φ t (a : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ))
    rw [heq]
    exact continuous_const.prodMk h2
  exact Continuous.subtype_mk hmain (fun t => (hkRcPsi m f φ hφb t a).property)

private lemma hkRcEvalD_apply (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (z : Ball (Eu m × Eu m)) (b : coneAlg f) :
    evalD m f z b = ((b : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)).2) z := rfl

private lemma hkRcEvalD_psi (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (φ : C(unitInterval × Ball (Eu m × Eu m), Ball (Eu m × Eu m)))
    (hφb : ∀ (t : unitInterval) (y : Ball (Eu m × Eu m)),
      y ∈ bdry (Eu m × Eu m) → φ (t, y) = y)
    (t : unitInterval) (a : coneAlg f) (z : Ball (Eu m × Eu m)) :
    evalD m f z (hkRcPsi m f φ hφb t a) =
      ((a : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)).2) (φ (t, z)) := by
  rw [hkRcEvalD_apply, hkRcPsi_val']
  rfl

private lemma hkRcAux (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (φ : C(unitInterval × Ball (Eu m × Eu m), Ball (Eu m × Eu m)))
    (hφ0 : ∀ z : Ball (Eu m × Eu m), φ (0, z) = z)
    (hφb : ∀ (t : unitInterval) (y : Ball (Eu m × Eu m)),
      y ∈ bdry (Eu m × Eu m) → φ (t, y) = y)
    (hφ1 : ∀ z : Ball (Eu m × Eu m), (1 : ℝ) / 2 ≤ ‖(z : Eu m × Eu m)‖ →
      ((φ (1, z) : Ball (Eu m × Eu m)) : Eu m × Eu m) =
        ((normPtBall z : Ball (Eu m × Eu m)) : Eu m × Eu m))
    (n : ℕ) (P : Matrix (Fin n) (Fin n) (coneAlg f)) (hP : P * P = P) :
    ∃ P' : Matrix (Fin n) (Fin n) (coneAlg f), P' * P' = P' ∧
      cls (⟨n, P'⟩ : Mat (coneAlg f)) = cls (⟨n, P⟩ : Mat (coneAlg f)) ∧
      ∀ (z : Ball (Eu m × Eu m)), (1 : ℝ) / 2 ≤ ‖(z : Eu m × Eu m)‖ →
        P'.map (evalD m f z) = P'.map (evalD m f (normPtBall z)) := by
  refine ⟨P.map (hkRcPsi m f φ hφb 1), ?_, ?_, ?_⟩
  · rw [← Matrix.map_mul, hP]
  · exact (hkRcClsEqOfHomotopicEndo
      (𝔄 := C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)) (A := coneAlg f)
      (hkRcConeClosed m f) n P hP (hkRcPsi m f φ hφb)
      (hkRcPsi_continuous m f φ hφb) (hkRcPsi_zero m f φ hφb hφ0)).symm
  · intro z hz
    have hnorm_ne : ‖(z : Eu m × Eu m)‖ ≠ 0 := by
      intro h0
      rw [h0] at hz
      norm_num at hz
    have hmem : normPtBall z ∈ bdry (Eu m × Eu m) := by
      show ‖((normPtBall z : Ball (Eu m × Eu m)) : Eu m × Eu m)‖ = 1
      rw [normPtBall_coe, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ hnorm_ne]
    have hφz : φ (1, z) = normPtBall z := Subtype.ext (hφ1 z hz)
    have hφn : φ (1, normPtBall z) = normPtBall z := hφb 1 (normPtBall z) hmem
    ext i j
    show (evalD m f z) (hkRcPsi m f φ hφb 1 (P i j)) =
      (evalD m f (normPtBall z)) (hkRcPsi m f φ hφb 1 (P i j))
    rw [hkRcEvalD_psi m f φ hφb 1 (P i j) z,
      hkRcEvalD_psi m f φ hφb 1 (P i j) (normPtBall z), hφz, hφn]

/-- **Radial collaring in the cell.**  An idempotent matrix over the mapping cone can be replaced,
without changing its class in `K₀`, by an idempotent matrix whose cell component is constant along
the rays with `‖z‖ ≥ 1/2` (where `‖·‖` is the sup norm on `Eu m × Eu m`). -/
theorem hk_radial_collar (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (f : C(Sph (Eu m × Eu m), Tgt m)) (n : ℕ)
    (P : Matrix (Fin n) (Fin n) (coneAlg f)) (hP : P * P = P) :
    ∃ P' : Matrix (Fin n) (Fin n) (coneAlg f), P' * P' = P' ∧
      cls (⟨n, P'⟩ : Mat (coneAlg f)) = cls (⟨n, P⟩ : Mat (coneAlg f)) ∧
      ∀ (z : Ball (Eu m × Eu m)), (1 : ℝ) / 2 ≤ ‖(z : Eu m × Eu m)‖ →
        P'.map (evalD m f z) = P'.map (evalD m f (normPtBall z)) :=
  hkRcAux m f (hkRcMap (Eu m × Eu m)) (hkRcMap_zero _)
    (fun t y hy => hkRcMap_bdry _ t y hy) (fun z hz => hkRcMap_one _ z hz) n P hP

end

end Work.KT
