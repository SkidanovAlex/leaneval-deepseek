import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.Fund.Geom
import Submission.Work.KT.homotopy_inv
import Submission.Work.KT.k0_rep
import Submission.Work.KT.Bott.GlueAux

/-!
# `Work.KT.Fund.Disc` — the disc is contractible: `K₀(C(X × D)) ≅ K₀(C(X))`

Radial homotopy of idempotents over `X × D`: every idempotent matrix over `C(X × D, ℂ)` is
homotopic, through idempotent matrices, to the pull-back of its value on `X × {0}`.  Hence
`K₀(C(X × D, ℂ)) ≅ K₀(C(X, ℂ))` via the two maps `sD` (pull-back along the projection) and `ev0`
(evaluation at `0`), which are mutually inverse.

This is the first ingredient of the clutching construction for `Work.KT.fund_product`.
-/

namespace Work.KT.Fund

open Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

lemma one_isIdem_local (R : Type) [Ring R] (n : ℕ) : (Mat.one R n).IsIdem := by
  unfold Mat.IsIdem Mat.one
  exact Matrix.one_mul 1

/-! ## The disc coordinates -/

/-- The projection `X × D → X`. -/
def projX : C(X × Ball ℂ, X) := ContinuousMap.fst

/-- The zero section `X → X × D`, `x ↦ (x, 0)`. -/
def zeroX : C(X, X × Ball ℂ) :=
  { toFun := fun x => (x, ⟨0, by rw [Metric.mem_closedBall, dist_zero_right]; norm_num⟩)
    continuous_toFun := by fun_prop }

@[simp] lemma zeroX_apply_fst (x : X) : (zeroX X x).1 = x := rfl
@[simp] lemma zeroX_apply_snd (x : X) : ((zeroX X x).2 : ℂ) = 0 := rfl

lemma mem_ball_smul (r : unitInterval) (v : Ball ℂ) :
    (r : ℝ) • (v : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul]
  have hv : ‖(v : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.mp v.2
  have hr : ‖(r : ℝ)‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg r.2.1]; exact r.2.2
  calc ‖(r : ℝ)‖ * ‖(v : ℂ)‖ ≤ 1 * 1 := mul_le_mul hr hv (norm_nonneg _) zero_le_one
    _ = 1 := by norm_num

/-- The radial self-map `v ↦ r • v` of the closed unit ball of `ℂ`. -/
def ballSmul (r : unitInterval) : C(Ball ℂ, Ball ℂ) :=
  { toFun := fun v => ⟨(r : ℝ) • (v : ℂ), mem_ball_smul r v⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      show Continuous (fun v : Ball ℂ => (r : ℝ) • (v : ℂ))
      fun_prop }

@[simp] lemma ballSmul_apply (r : unitInterval) (v : Ball ℂ) :
    ((ballSmul r v : Ball ℂ) : ℂ) = (r : ℝ) • (v : ℂ) := rfl

/-- The radial map `(x, v) ↦ (x, r • v)` of `X × D`. -/
def radP (r : unitInterval) : C(X × Ball ℂ, X × Ball ℂ) :=
  { toFun := fun p => (p.1, ballSmul r p.2)
    continuous_toFun := continuous_fst.prodMk ((ballSmul r).continuous.comp continuous_snd) }

@[simp] lemma radP_apply_fst (r : unitInterval) (p : X × Ball ℂ) :
    ((radP X r p).1 : X) = p.1 := rfl

@[simp] lemma radP_apply_snd (r : unitInterval) (p : X × Ball ℂ) :
    ((radP X r p).2 : ℂ) = (r : ℝ) • (p.2 : ℂ) := rfl

lemma radP_one (p : X × Ball ℂ) : radP X 1 p = p := by
  refine Prod.ext rfl (Subtype.ext ?_)
  rw [radP_apply_snd]
  show ((1 : unitInterval) : ℝ) • (p.2 : ℂ) = (p.2 : ℂ)
  rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, one_smul]

/-- `pullAlg (radP X r)` as a ring homomorphism. -/
def radHom (r : unitInterval) : C(X × Ball ℂ, ℂ) →+* C(X × Ball ℂ, ℂ) :=
  (pullAlg (radP X r)).toRingHom

@[simp] lemma radHom_apply (r : unitInterval) (g : C(X × Ball ℂ, ℂ)) (p : X × Ball ℂ) :
    radHom X r g p = g (radP X r p) := rfl

/-- The family `(r, v) ↦ r • v` on the ball. -/
def ballSmulFam : C(unitInterval × Ball ℂ, Ball ℂ) :=
  { toFun := fun q => ⟨(q.1 : ℝ) • (q.2 : ℂ), by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul]
      have hv : ‖(q.2 : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.mp q.2.2
      have hr : ‖(q.1 : ℝ)‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg q.1.2.1]; exact q.1.2.2
      calc ‖(q.1 : ℝ)‖ * ‖(q.2 : ℂ)‖ ≤ 1 * 1 := mul_le_mul hr hv (norm_nonneg _) zero_le_one
        _ = 1 := by norm_num⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      show Continuous (fun q : unitInterval × Ball ℂ => (q.1 : ℝ) • (q.2 : ℂ))
      fun_prop }

@[simp] lemma ballSmulFam_apply (r : unitInterval) (v : Ball ℂ) :
    ((ballSmulFam (r, v) : Ball ℂ) : ℂ) = (r : ℝ) • (v : ℂ) := rfl

/-- The radial family, as a continuous map `[0,1] × X × D → X × D`. -/
def radFam : C(unitInterval × (X × Ball ℂ), X × Ball ℂ) :=
  { toFun := fun q => (q.2.1, ballSmulFam (q.1, q.2.2))
    continuous_toFun := by
      apply Continuous.prodMk
      · exact continuous_fst.comp continuous_snd
      · exact ballSmulFam.continuous.comp
          (continuous_fst.prodMk (continuous_snd.comp continuous_snd)) }

lemma radFam_apply (r : unitInterval) (p : X × Ball ℂ) : radFam X (r, p) = radP X r p := rfl

/-- The radial path of a continuous function: `r ↦ g ∘ radP X r`. -/
def radPath (g : C(X × Ball ℂ, ℂ)) : C(unitInterval, C(X × Ball ℂ, ℂ)) :=
  (g.comp (radFam X)).curry

lemma radPath_apply (g : C(X × Ball ℂ, ℂ)) (r : unitInterval) (p : X × Ball ℂ) :
    radPath X g r p = g (radP X r p) := by
  rw [radPath, ContinuousMap.curry_apply]
  rfl

/-! ## Contravariance of `pullAlg` -/

/-- Contravariant composition of `pullAlg` (as algebra homomorphisms). -/
lemma pullAlg_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) :
    (pullAlg (g.comp f)) = (pullAlg f).comp (pullAlg g) := by
  rw [show (pullAlg (g.comp f))
      = (ContinuousMap.compStarAlgHom' ℂ ℂ (g.comp f)).toAlgHom from rfl,
    ContinuousMap.compStarAlgHom'_comp]
  rfl

/-- The same, for the underlying ring homomorphisms. -/
lemma pullAlg_comp_toRingHom {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) :
    (pullAlg (g.comp f)).toRingHom = (pullAlg f).toRingHom.comp (pullAlg g).toRingHom := by
  rw [pullAlg_comp f g]
  rfl

lemma pullAlg_id (X : Type) [TopologicalSpace X] :
    pullAlg (ContinuousMap.id X) = AlgHom.id ℂ C(X, ℂ) := by
  refine AlgHom.ext fun φ => ?_
  refine ContinuousMap.ext fun x => ?_
  rfl

/-- `projX ∘ zeroX = id`. -/
lemma projX_comp_zeroX : (projX X).comp (zeroX X) = ContinuousMap.id X := by
  refine ContinuousMap.ext fun x => ?_
  rfl

/-- `zeroX ∘ projX` is the radial projection onto the zero section. -/
lemma zeroX_comp_projX : (zeroX X).comp (projX X) = radP X 0 := by
  refine ContinuousMap.ext fun p => ?_
  rw [ContinuousMap.comp_apply]
  refine Prod.ext ?_ (Subtype.ext ?_)
  · rw [zeroX_apply_fst, radP_apply_fst]
    simp [projX]
  · rw [zeroX_apply_snd, radP_apply_snd,
      show ((0 : unitInterval) : ℝ) = 0 from rfl, zero_smul]

/-! ## Homotopy invariance in a Banach algebra -/

/-- The canonical ring homomorphism `𝔄 → ↥⊤`. -/
def topHom (𝔄 : Type) [Ring 𝔄] [Algebra ℂ 𝔄] : 𝔄 →+* ↥(⊤ : Subalgebra ℂ 𝔄) where
  toFun a := ⟨a, by simp⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Homotopy invariance of the class of a path of idempotent matrices over a complex Banach
algebra (the case `R = ⊤` of `Work.KT.homotopy_inv`). -/
theorem cls_eq_of_path (𝔄 : Type) [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄]
    {n : ℕ} (γ : unitInterval → Matrix (Fin n) (Fin n) 𝔄) (hγ : Continuous γ)
    (hidem : ∀ t, γ t * γ t = γ t) :
    cls (⟨n, γ 0⟩ : Mat 𝔄) = cls (⟨n, γ 1⟩ : Mat 𝔄) := by
  let ψ : ↥(⊤ : Subalgebra ℂ 𝔄) →+* 𝔄 := (Subalgebra.val (⊤ : Subalgebra ℂ 𝔄)).toRingHom
  let γ' : unitInterval → Matrix (Fin n) (Fin n) ↥(⊤ : Subalgebra ℂ 𝔄) :=
    fun t => (γ t).map (topHom 𝔄)
  have hγ' : Continuous γ' := by
    apply continuous_matrix
    intro i j
    have h1 : Continuous (fun t : unitInterval => γ t i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp hγ)
    have h2 : (fun t : unitInterval => γ' t i j)
        = fun t => (⟨γ t i j, by simp⟩ : ↥(⊤ : Subalgebra ℂ 𝔄)) := by
      funext t
      rfl
    rw [h2]
    exact Continuous.subtype_mk h1 _
  have hidem' : ∀ t, γ' t * γ' t = γ' t := by
    intro t
    dsimp only [γ']
    rw [← Matrix.map_mul, hidem t]
  have key := homotopy_inv 𝔄 ⊤ isClosed_univ n γ' hγ' hidem'
  have hcoe : ∀ t : unitInterval, (γ' t).map ψ = γ t := by
    intro t
    ext i j
    rfl
  have hmap : ∀ t : unitInterval,
      K0.map ψ (cls (⟨n, γ' t⟩ : Mat _)) = cls (⟨n, γ t⟩ : Mat 𝔄) := by
    intro t
    rw [K0.map_cls _ (show Mat.IsIdem (⟨n, γ' t⟩ : Mat _) from hidem' t)]
    show cls (⟨n, (γ' t).map ψ⟩ : Mat 𝔄) = cls (⟨n, γ t⟩ : Mat 𝔄)
    rw [hcoe t]
  rw [← hmap 0, ← hmap 1, key]

/-! ## Radial triviality of idempotents over the disc -/

/-- Every idempotent matrix over `C(X × D, ℂ)` has the same class as its radial pull-back to
`X × {0}`. -/
theorem cls_map_rad_zero {n : ℕ} (P : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (hP : P * P = P) :
    cls (⟨n, P.map (radHom X 0)⟩ : Mat C(X × Ball ℂ, ℂ)) = cls (⟨n, P⟩ : Mat _) := by
  let γ : unitInterval → Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
    fun r => Matrix.of (fun i j => radPath X (P i j) r)
  have hγeq : ∀ r, γ r = P.map (radHom X r) := by
    intro r
    apply Matrix.ext
    intro i j
    refine ContinuousMap.ext fun p => ?_
    rw [Matrix.map_apply]
    show radPath X (P i j) r p = radHom X r (P i j) p
    rw [radPath_apply, radHom_apply]
  have hcont : Continuous γ := by
    apply continuous_matrix
    intro i j
    exact (radPath X (P i j)).continuous
  have hidem : ∀ r, γ r * γ r = γ r := by
    intro r
    rw [hγeq r, ← Matrix.map_mul, hP]
  have key := cls_eq_of_path (C(X × Ball ℂ, ℂ)) γ hcont hidem
  have h0 : (⟨n, γ 0⟩ : Mat C(X × Ball ℂ, ℂ)) = ⟨n, P.map (radHom X 0)⟩ := by
    rw [hγeq 0]
  have h1 : (⟨n, γ 1⟩ : Mat C(X × Ball ℂ, ℂ)) = ⟨n, P⟩ := by
    rw [hγeq 1]
    congr 1
    ext i j
    rw [Matrix.map_apply, radHom_apply, radP_one]
  rw [h0, h1] at key
  exact key

/-! ## The two maps -/

/-- Pull-back of `K₀`-classes along the projection `X × D → X`. -/
def sD : K0 C(X, ℂ) →+ K0 C(X × Ball ℂ, ℂ) :=
  K0.mapA (pullAlg (projX X))

/-- Evaluation at the zero section `X → X × D`. -/
def ev0 : K0 C(X × Ball ℂ, ℂ) →+ K0 C(X, ℂ) :=
  K0.mapA (pullAlg (zeroX X))

lemma radHom_zero_eq :
    (pullAlg (projX X)).toRingHom.comp (pullAlg (zeroX X)).toRingHom = radHom X 0 := by
  rw [← pullAlg_comp_toRingHom (projX X) (zeroX X), zeroX_comp_projX X]
  rfl

lemma comp_zeroX_projX_eq_id :
    (pullAlg (zeroX X)).toRingHom.comp (pullAlg (projX X)).toRingHom
      = RingHom.id (C(X, ℂ)) := by
  rw [← pullAlg_comp_toRingHom (zeroX X) (projX X), projX_comp_zeroX X, pullAlg_id X]
  rfl

/-- `ev0 ∘ sD = id`. -/
theorem ev0_sD (a : K0 C(X, ℂ)) : ev0 X (sD X a) = a := by
  change K0.map (pullAlg (zeroX X)).toRingHom
    (K0.map (pullAlg (projX X)).toRingHom a) = a
  rw [← K0.map_comp_apply (pullAlg (projX X)).toRingHom (pullAlg (zeroX X)).toRingHom a,
    comp_zeroX_projX_eq_id X, K0.map_id_apply]

lemma sD_one (n : ℕ) :
    sD X (cls (Mat.one C(X, ℂ) n)) = cls (Mat.one C(X × Ball ℂ, ℂ) n) := by
  change K0.map (pullAlg (projX X)).toRingHom (cls (Mat.one C(X, ℂ) n)) = _
  rw [K0.map_cls _ (one_isIdem_local (C(X, ℂ)) n)]
  congr 1
  exact Work.KT.Bott.Mat.map_one' (pullAlg (projX X)).toRingHom n

/-- `sD ∘ ev0 = id`: this is the radial triviality of idempotents over the disc. -/
theorem sD_ev0 (x : K0 C(X × Ball ℂ, ℂ)) : sD X (ev0 X x) = x := by
  obtain ⟨F, m, hF, hx⟩ := k0_rep x
  rw [hx, map_sub, map_sub]
  congr 1
  · obtain ⟨nF, MF⟩ := F
    change K0.map (pullAlg (projX X)).toRingHom
      (K0.map (pullAlg (zeroX X)).toRingHom (cls (⟨nF, MF⟩ : Mat _)))
        = cls (⟨nF, MF⟩ : Mat C(X × Ball ℂ, ℂ))
    rw [K0.map_cls _ hF, K0.map_cls _ (Mat.IsIdem.map _ hF),
      ← Mat.map_comp (pullAlg (zeroX X)).toRingHom (pullAlg (projX X)).toRingHom
        (⟨nF, MF⟩ : Mat _),
      radHom_zero_eq]
    exact cls_map_rad_zero X MF hF
  · change K0.map (pullAlg (projX X)).toRingHom
      (K0.map (pullAlg (zeroX X)).toRingHom (cls (Mat.one C(X × Ball ℂ, ℂ) m)))
        = cls (Mat.one C(X × Ball ℂ, ℂ) m)
    rw [K0.map_cls _ (one_isIdem_local (C(X × Ball ℂ, ℂ)) m),
      Work.KT.Bott.Mat.map_one']
    exact sD_one X m

/-- `K₀` of the disc algebra is `K₀` of the base, via `sD`. -/
def sDEquiv : K0 C(X, ℂ) ≃+ K0 C(X × Ball ℂ, ℂ) where
  toFun := sD X
  invFun := ev0 X
  left_inv := ev0_sD X
  right_inv := sD_ev0 X
  map_add' := map_add _

theorem sD_bijective : Function.Bijective (sD X) := (sDEquiv X).bijective

lemma sD_injective : Function.Injective (sD X) := (sDEquiv X).injective

lemma ev0_injective : Function.Injective (ev0 X) := (sDEquiv X).symm.injective

end

end Work.KT.Fund
