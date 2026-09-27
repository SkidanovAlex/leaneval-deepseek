import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.BallKFrame
import Submission.Work.KT.Fund.Geom
import Submission.Work.KT.ExtGen.Radial

/-!
# `Work.KT.bott_geom` — `Xq W ≅ S²` for a two-dimensional `W`, and the transported algebra

The Bott product theorem `Work.KT.fund_product` computes `K₀(C(X × S²))` for a compact Hausdorff
space `X`.  To apply it to the pair `(V, W)` of the Bott suspension lemma, where `W` is an
arbitrary two-dimensional real normed space, we need to identify `Xq V × Xq W` with `Xq V × S²`.

* `bcol : Ball ℂ → S2` is the standard collapse map of the closed unit disc of `ℂ = ℝ²` onto `S²`
  (the boundary circle is collapsed to the north pole); it is continuous, surjective, and its
  fibres are the singletons of the open disc together with the whole boundary circle;
* combined with the radial normalisation `W ≅ ℂ` it descends to a homeomorphism `Xq W ≃ₜ S2`;
* `ba_prodAlgCM` transports the resulting identification of function algebras into the statement
  `prodAlg V W ≃ₐ[ℂ] C(Xq V × S2, ℂ)`, compatible with the two projections.
-/

namespace Work.KT

open Matrix

noncomputable section

/-! ## The radial scalar -/

/-- `bsFun r = π · sinc (π r)`, the continuous extension of `sin (π r)/r` to `r = 0`. -/
def bsFun (r : ℝ) : ℝ := Real.pi * Real.sinc (Real.pi * r)

lemma continuous_bsFun : Continuous bsFun :=
  continuous_const.mul (Real.continuous_sinc.comp (continuous_const.mul continuous_id))

@[simp] lemma bsFun_zero : bsFun 0 = Real.pi := by simp [bsFun]

/-- The defining property of `bsFun`. -/
lemma bsFun_mul (r : ℝ) : bsFun r * r = Real.sin (Real.pi * r) := by
  rcases eq_or_ne r 0 with hr | hr
  · subst hr; simp [bsFun]
  · rw [bsFun, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hr)]
    field_simp

@[simp] lemma bsFun_one : bsFun 1 = 0 := by
  rw [bsFun, show Real.pi * 1 = Real.pi by ring, Real.sinc_of_ne_zero Real.pi_ne_zero,
    Real.sin_pi, zero_div, mul_zero]

lemma bsFun_ne_zero {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : bsFun r ≠ 0 := by
  intro h
  have hmul : Real.sin (Real.pi * r) = 0 := by rw [← bsFun_mul, h, zero_mul]
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hmul
  have hr : r = (n : ℝ) := by
    have h' : Real.pi * (n : ℝ) = Real.pi * r := by
      rw [mul_comm Real.pi (n : ℝ)]; exact hn
    exact (mul_left_cancel₀ Real.pi_ne_zero h').symm
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by rw [← hr]; exact h0
  have hn1 : (n : ℝ) < 1 := by rw [← hr]; exact h1
  have hnz : n = 0 := by
    have h0' : (0 : ℤ) ≤ n := by exact_mod_cast hn0
    have h1' : n < 1 := by exact_mod_cast hn1
    omega
  have : r = 0 := by rw [hr, hnz]; norm_num
  rw [this, bsFun_zero] at h
  exact Real.pi_ne_zero h

lemma bsFun_pos {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : 0 < bsFun r := by
  rcases eq_or_lt_of_le h0 with h | h
  · subst h; rw [bsFun_zero]; exact Real.pi_pos
  · have hmul : bsFun r * r = Real.sin (Real.pi * r) := bsFun_mul r
    have hπr : 0 < Real.pi * r := mul_pos Real.pi_pos h
    have hlt : Real.pi * r < Real.pi := by nlinarith [Real.pi_pos]
    have hsin : 0 < Real.sin (Real.pi * r) := Real.sin_pos_of_pos_of_lt_pi hπr hlt
    have hpos : 0 < bsFun r * r := by rw [hmul]; exact hsin
    have hmulpos : 0 < r * bsFun r := by rw [mul_comm]; exact hpos
    exact pos_of_mul_pos_right hmulpos h.le

/-- Pull-back of continuous functions along a homeomorphism, as an algebra equivalence.  Defined
locally so that this file depends on as few upstream names as possible. -/
def ba_pullAlgEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    C(Y, ℂ) ≃ₐ[ℂ] C(X, ℂ) where
  toFun := pullAlg ⟨e, e.continuous_toFun⟩
  invFun := pullAlg ⟨e.symm, e.symm.continuous_toFun⟩
  left_inv := by intro f; ext x; simp [pullAlg]
  right_inv := by intro g; ext y; simp [pullAlg]
  map_mul' := by intro f g; ext x; simp [pullAlg]
  map_add' := by intro f g; ext x; simp [pullAlg]
  commutes' := by intro c; ext x; simp [pullAlg]

@[simp] lemma ba_pullAlgEquiv_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (f : C(Y, ℂ)) :
    ba_pullAlgEquiv e f = f.comp ⟨e, e.continuous_toFun⟩ := rfl

/-! ## The collapse map `D_ℂ → S²` -/

/-- `Fund.mk3 z t = Fund.mk3 z' t'` iff `z = z'` and `t = t'`. -/
lemma bmk3_inj {z z' : ℂ} {t t' : ℝ} :
    Fund.mk3 z t = Fund.mk3 z' t' ↔ z = z' ∧ t = t' := by
  constructor
  · intro h
    have h0 : z.re = z'.re := by
      simpa [Fund.mk3_apply_zero] using congrArg (fun f : EuclideanSpace ℝ (Fin 3) => f 0) h
    have h1 : z.im = z'.im := by
      simpa [Fund.mk3_apply_one] using congrArg (fun f : EuclideanSpace ℝ (Fin 3) => f 1) h
    have h2 : t = t' := by
      simpa [Fund.mk3_apply_two] using congrArg (fun f : EuclideanSpace ℝ (Fin 3) => f 2) h
    exact ⟨Complex.ext h0 h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A point of the boundary circle of the disc of `ℂ`. -/
def bone : Ball ℂ := ⟨(1 : ℂ), by rw [mem_closedBall_zero_iff]; norm_num⟩

lemma bone_bdry : bone ∈ bdry ℂ := by
  change ‖(bone : ℂ)‖ = 1
  simp [bone]

/-- The collapse map `D_ℂ → S²` (unbundled). -/
def bcolFun (v : Ball ℂ) : EuclideanSpace ℝ (Fin 3) :=
  Fund.mk3 (bsFun ‖(v : ℂ)‖ • (v : ℂ)) (-Real.cos (Real.pi * ‖(v : ℂ)‖))

lemma bcolFun_apply (v : Ball ℂ) :
    bcolFun v = Fund.mk3 (bsFun ‖(v : ℂ)‖ • (v : ℂ)) (-Real.cos (Real.pi * ‖(v : ℂ)‖)) := rfl

lemma bcol_norm (v : Ball ℂ) : ‖bcolFun v‖ = 1 := by
  have h1 : ‖bsFun ‖(v : ℂ)‖ • (v : ℂ)‖ ^ 2 = (Real.sin (Real.pi * ‖(v : ℂ)‖)) ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ← mul_pow, bsFun_mul]
  have h2 : ‖(-Real.cos (Real.pi * ‖(v : ℂ)‖))‖ ^ 2 = (Real.cos (Real.pi * ‖(v : ℂ)‖)) ^ 2 := by
    rw [norm_neg, Real.norm_eq_abs, sq_abs]
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, bcolFun, Fund.norm_mk3_sq, h1,
    show (-Real.cos (Real.pi * ‖(v : ℂ)‖)) ^ 2
      = (Real.cos (Real.pi * ‖(v : ℂ)‖)) ^ 2 from neg_sq _,
    Real.sin_sq_add_cos_sq, one_pow]

/-- The collapse map `D_ℂ → S²` as a map into the sphere. -/
def bcol (v : Ball ℂ) : S2 := ⟨bcolFun v, by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact bcol_norm v⟩

@[simp] lemma bcol_coe (v : Ball ℂ) : ((bcol v : S2) : EuclideanSpace ℝ (Fin 3)) = bcolFun v := rfl

lemma continuous_bcolFun : Continuous bcolFun := by
  unfold bcolFun
  refine Fund.continuous_mk3.comp (Continuous.prodMk ?_ ?_)
  · exact (continuous_bsFun.comp (continuous_norm.comp continuous_subtype_val)).smul
      continuous_subtype_val
  · exact (Real.continuous_cos.comp
      (continuous_const.mul (continuous_norm.comp continuous_subtype_val))).neg

lemma continuous_bcol : Continuous bcol :=
  continuous_bcolFun.subtype_mk _

/-- On the boundary circle the collapse map is constantly the north pole. -/
lemma bcol_bdry (v : Ball ℂ) (hv : v ∈ bdry ℂ) : bcol v = bcol bone := by
  have hnorm : ‖(v : ℂ)‖ = 1 := hv
  apply Subtype.ext
  rw [bcol_coe, bcol_coe]
  simp only [bcolFun, hnorm, bsFun_one, zero_smul, mul_one, Real.cos_pi, neg_neg]
  rw [show ((bone : Ball ℂ) : ℂ) = 1 from rfl, norm_one]
  simp only [bsFun_one, zero_smul, mul_one, Real.cos_pi, neg_neg]

/-- The fibres of the collapse map: the singletons of the open disc, together with the whole
boundary circle. -/
lemma bcol_eq_iff (v v' : Ball ℂ) :
    bcol v = bcol v' ↔ v = v' ∨ (v ∈ bdry ℂ ∧ v' ∈ bdry ℂ) := by
  rw [Subtype.ext_iff, bcol_coe, bcol_coe, bcolFun, bcolFun, bmk3_inj]
  simp only [neg_inj]
  constructor
  · rintro ⟨h1, h2⟩
    have hxle : ‖(v : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.mp v.2
    have hxle' : ‖(v' : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.mp v'.2
    have hxnn : (0 : ℝ) ≤ ‖(v : ℂ)‖ := norm_nonneg _
    have hxnn' : (0 : ℝ) ≤ ‖(v' : ℂ)‖ := norm_nonneg _
    have hmem : Real.pi * ‖(v : ℂ)‖ ∈ Set.Icc 0 Real.pi :=
      ⟨mul_nonneg Real.pi_pos.le hxnn, mul_le_of_le_one_right Real.pi_pos.le hxle⟩
    have hmem' : Real.pi * ‖(v' : ℂ)‖ ∈ Set.Icc 0 Real.pi :=
      ⟨mul_nonneg Real.pi_pos.le hxnn', mul_le_of_le_one_right Real.pi_pos.le hxle'⟩
    have hpeq : Real.pi * ‖(v : ℂ)‖ = Real.pi * ‖(v' : ℂ)‖ :=
      Real.strictAntiOn_cos.injOn hmem hmem' h2
    have hreq : ‖(v : ℂ)‖ = ‖(v' : ℂ)‖ := mul_left_cancel₀ Real.pi_ne_zero hpeq
    by_cases hrx : ‖(v : ℂ)‖ = 1
    · right
      refine ⟨show v ∈ bdry ℂ from hrx, ?_⟩
      show ‖(v' : ℂ)‖ = 1
      rw [← hreq]; exact hrx
    · left
      have hlt : ‖(v : ℂ)‖ < 1 := lt_of_le_of_ne hxle hrx
      have h1' : bsFun ‖(v : ℂ)‖ • (v : ℂ) = bsFun ‖(v : ℂ)‖ • (v' : ℂ) := by
        rw [← hreq] at h1
        exact h1
      have hsub : bsFun ‖(v : ℂ)‖ • ((v : ℂ) - (v' : ℂ)) = 0 := by
        rw [smul_sub, h1', sub_self]
      have hvsub : (v : ℂ) - (v' : ℂ) = 0 := by
        rcases smul_eq_zero.mp hsub with hz | hz
        · exact absurd hz (bsFun_ne_zero hxnn hlt)
        · exact hz
      exact Subtype.ext (sub_eq_zero.mp hvsub)
  · rintro (rfl | ⟨hvb, hv'b⟩)
    · exact ⟨rfl, rfl⟩
    · have h1 : ‖(v : ℂ)‖ = 1 := hvb
      have h2 : ‖(v' : ℂ)‖ = 1 := hv'b
      simp [bcolFun, bsFun_one, h1, h2]

/-! ## Surjectivity of the collapse map -/

/-- The radial angle `arccos (-t)/π`. -/
def bAngle (t : ℝ) : ℝ := Real.arccos (-t) / Real.pi

lemma cos_pi_bAngle {t : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 1) :
    Real.cos (Real.pi * bAngle t) = -t := by
  rw [bAngle, mul_div_cancel₀ _ Real.pi_ne_zero]
  exact Real.cos_arccos (by linarith) (by linarith)

lemma sin_pi_bAngle (t : ℝ) :
    Real.sin (Real.pi * bAngle t) = Real.sqrt (1 - t ^ 2) := by
  rw [bAngle, mul_div_cancel₀ _ Real.pi_ne_zero]
  rw [Real.sin_arccos]
  congr 1
  ring

lemma bAngle_nonneg (t : ℝ) : 0 ≤ bAngle t :=
  div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le

lemma bAngle_le_one (t : ℝ) : bAngle t ≤ 1 := by
  rw [bAngle, div_le_one Real.pi_pos]
  simpa using Real.arccos_le_pi (-t)

/-- A point of the unit sphere of `ℝ³` has the form `(z, t)` with `‖z‖² + t² = 1`; every such
point is in the image of the collapse map. -/
lemma bcol_surjective : Function.Surjective bcol := by
  intro y
  set z : ℂ := ((y : EuclideanSpace ℝ (Fin 3)) 0 : ℂ)
    + Complex.I * ((y : EuclideanSpace ℝ (Fin 3)) 1 : ℂ) with hz
  set t : ℝ := (y : EuclideanSpace ℝ (Fin 3)) 2 with ht
  have hy : (y : EuclideanSpace ℝ (Fin 3)) = Fund.mk3 z t := by
    rw [hz, ht, Fund.mk3]
    apply WithLp.ofLp_injective
    ext i
    fin_cases i <;> simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hnorm : ‖(y : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    have h := Metric.mem_sphere.mp y.2
    rwa [dist_eq_norm, sub_zero] at h
  have hzt : ‖z‖ ^ 2 + t ^ 2 = 1 := by
    have h := Fund.norm_mk3_sq z t
    rw [← hy, hnorm, one_pow] at h
    linarith
  have ht1 : t ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖z‖]
  have hlow : -1 ≤ t := (abs_le.mp ((sq_le_one_iff_abs_le_one t).mp ht1)).1
  have hupp : t ≤ 1 := (abs_le.mp ((sq_le_one_iff_abs_le_one t).mp ht1)).2
  set r : ℝ := bAngle t with hr
  have hr0 : 0 ≤ r := by rw [hr]; exact bAngle_nonneg t
  have hr1 : r ≤ 1 := by rw [hr]; exact bAngle_le_one t
  have hcos : Real.cos (Real.pi * r) = -t := by rw [hr]; exact cos_pi_bAngle hlow hupp
  have hsin : Real.sin (Real.pi * r) = Real.sqrt (1 - t ^ 2) := by
    rw [hr]; exact sin_pi_bAngle t
  have hznorm : ‖z‖ = Real.sqrt (1 - t ^ 2) := by
    have h2 : ‖z‖ ^ 2 = 1 - t ^ 2 := by linarith
    rw [← h2, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg z)]
  have hsinz : Real.sin (Real.pi * r) = ‖z‖ := by rw [hsin, hznorm]
  by_cases hr1' : r = 1
  · -- north pole case
    have ht_one : t = 1 := by
      have h := hcos
      rw [hr1', mul_one, Real.cos_pi] at h
      linarith
    have hz0 : z = 0 := by
      have hnsq : ‖z‖ ^ 2 = 0 := by nlinarith [hzt, ht_one]
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnsq)
    refine ⟨bone, ?_⟩
    rw [bcol_bdry _ bone_bdry]
    apply Subtype.ext
    rw [bcol_coe, hy, hz0, ht_one]
    simp [bcolFun, bone]
  · -- interior case
    have hrlt : r < 1 := lt_of_le_of_ne hr1 hr1'
    have hsne : bsFun r ≠ 0 := bsFun_ne_zero hr0 hrlt
    have hspos : 0 < bsFun r := bsFun_pos hr0 hrlt
    have hvn : ‖z‖ = bsFun r * r := by rw [← hsinz, ← bsFun_mul]
    set vv : ℂ := (bsFun r)⁻¹ • z with hvv
    have hvvnorm : ‖vv‖ = r := by
      rw [hvv, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hspos), hvn]
      rw [← mul_assoc, inv_mul_cancel₀ hsne, one_mul]
    have hmem : vv ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall_zero_iff, hvvnorm]; exact hr1
    refine ⟨⟨vv, hmem⟩, ?_⟩
    apply Subtype.ext
    rw [bcol_coe]
    simp only [bcolFun]
    rw [show ‖((⟨vv, hmem⟩ : Ball ℂ) : ℂ)‖ = r from hvvnorm]
    rw [hy, bmk3_inj]
    refine ⟨?_, ?_⟩
    · rw [hvv, smul_smul, mul_inv_cancel₀ hsne, one_smul]
    · rw [hcos]; ring

/-! ## `Xq W ≃ₜ S²` for a two-dimensional `W` -/

/-- For a two-dimensional real normed space `W`, the quotient `Xq W = D_W/S_W` is the `2`-sphere. -/
theorem ba_exists_homeo_Xq_S2 (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (hWd : Module.finrank ℝ W = 2) : Nonempty (Xq W ≃ₜ S2) := by
  haveI : ProperSpace W := FiniteDimensional.proper ℝ W
  have hfr : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  obtain ⟨e⟩ : Nonempty (W ≃ₗ[ℝ] ℂ) :=
    ⟨LinearEquiv.ofFinrankEq _ _ (by rw [hWd, hfr])⟩
  have hcont : Continuous (fun x : Ball W => bcol (ExtGen.phiBall e x)) :=
    continuous_bcol.comp (ExtGen.continuous_phiBall e)
  have hfib : ∀ x x' : Ball W, qMap W x = qMap W x' →
      bcol (ExtGen.phiBall e x) = bcol (ExtGen.phiBall e x') := by
    intro x x' h
    rcases (qMap_eq_iff W).mp h with h' | ⟨hx, hx'⟩
    · rw [h']
    · rw [bcol_bdry _ (ExtGen.phiBall_mem_bdry e hx),
        bcol_bdry _ (ExtGen.phiBall_mem_bdry e hx')]
  let Φ : C(Xq W, S2) := (isQuotientMap_qMap W).lift ⟨_, hcont⟩ hfib
  have hl : Φ.comp (qMap W) = ⟨_, hcont⟩ := Topology.IsQuotientMap.lift_comp _ _ _
  have hΦ : ∀ x : Ball W, Φ (qMap W x) = bcol (ExtGen.phiBall e x) := by
    intro x
    have := congrFun (congrArg DFunLike.coe hl) x
    simpa using this
  have hsurj : Function.Surjective Φ := by
    intro y
    obtain ⟨v, hv⟩ := bcol_surjective y
    refine ⟨qMap W (ExtGen.psiBall e v), ?_⟩
    rw [hΦ, ExtGen.phiBall_psiBall, hv]
  have hinj : Function.Injective Φ := by
    intro a b hab
    obtain ⟨x, rfl⟩ := surjective_qMap W a
    obtain ⟨x', rfl⟩ := surjective_qMap W b
    rw [hΦ, hΦ] at hab
    rcases (bcol_eq_iff _ _).mp hab with h' | ⟨hx, hx'⟩
    · have h2 : ExtGen.psiBall e (ExtGen.phiBall e x)
          = ExtGen.psiBall e (ExtGen.phiBall e x') := by rw [h']
      rw [ExtGen.psiBall_phiBall, ExtGen.psiBall_phiBall] at h2
      rw [h2]
    · have hxW : x ∈ bdry W := by
        have h2 := ExtGen.psiBall_mem_bdry e hx
        rwa [ExtGen.psiBall_phiBall] at h2
      have hxW' : x' ∈ bdry W := by
        have h2 := ExtGen.psiBall_mem_bdry e hx'
        rwa [ExtGen.psiBall_phiBall] at h2
      exact qMap_eq_of_mem_bdry W hxW hxW'
  exact ⟨Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective Φ ⟨hinj, hsurj⟩) Φ.continuous⟩

/-- The product of a homeomorphism with the identity, `X × Y ≃ₜ X × Z`. -/
def ba_prodHomeo {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : Y ≃ₜ Z) : X × Y ≃ₜ X × Z where
  toFun := fun p => (p.1, e p.2)
  invFun := fun p => (p.1, e.symm p.2)
  left_inv := by intro p; simp
  right_inv := by intro p; simp
  continuous_toFun := continuous_fst.prodMk (e.continuous.comp continuous_snd)
  continuous_invFun := continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)

@[simp] lemma ba_prodHomeo_apply {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (e : Y ≃ₜ Z) (p : X × Y) : ba_prodHomeo e p = (p.1, e p.2) := rfl

/-! ## The transported algebra isomorphism -/

section ProdAlg

variable (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- `prodIso` commutes with the pull-backs of the projections. -/
lemma ba_prodPush_pullFst (g : Kpair V) :
    prodPush V W (pullFst V W g) =
      pullAlg (ContinuousMap.fst : C(Xq V × Xq W, Xq V)) (qPush V g) := by
  ext x
  obtain ⟨z, rfl⟩ := surjective_qMapProd V W x
  show (prodPush V W (pullFst V W g)) (qMapProd V W z)
    = (pullAlg (ContinuousMap.fst : C(Xq V × Xq W, Xq V)) (qPush V g)) (qMapProd V W z)
  rw [show (prodPush V W (pullFst V W g)) (qMapProd V W z)
      = ((prodPush V W (pullFst V W g)).comp (qMapProd V W)) z from rfl,
    prodPush_comp_qMapProd]
  rw [show (pullAlg (ContinuousMap.fst : C(Xq V × Xq W, Xq V)) (qPush V g)) (qMapProd V W z)
      = ((qPush V g).comp ((ContinuousMap.fst : C(Xq V × Xq W, Xq V)).comp
          (qMapProd V W))) z from rfl]
  rw [show ((ContinuousMap.fst : C(Xq V × Xq W, Xq V)).comp (qMapProd V W))
      = (qMap V).comp (prFst V W) from rfl, ← ContinuousMap.comp_assoc, qPush_comp_qMap]
  rfl

/-- `prodIso` commutes with the pull-backs of the projections (second factor). -/
lemma ba_prodPush_pullSnd (t : Kpair W) :
    prodPush V W (pullSnd V W t) =
      pullAlg (ContinuousMap.snd : C(Xq V × Xq W, Xq W)) (qPush W t) := by
  ext x
  obtain ⟨z, rfl⟩ := surjective_qMapProd V W x
  show (prodPush V W (pullSnd V W t)) (qMapProd V W z)
    = (pullAlg (ContinuousMap.snd : C(Xq V × Xq W, Xq W)) (qPush W t)) (qMapProd V W z)
  rw [show (prodPush V W (pullSnd V W t)) (qMapProd V W z)
      = ((prodPush V W (pullSnd V W t)).comp (qMapProd V W)) z from rfl,
    prodPush_comp_qMapProd]
  rw [show (pullAlg (ContinuousMap.snd : C(Xq V × Xq W, Xq W)) (qPush W t)) (qMapProd V W z)
      = ((qPush W t).comp ((ContinuousMap.snd : C(Xq V × Xq W, Xq W)).comp
          (qMapProd V W))) z from rfl]
  rw [show ((ContinuousMap.snd : C(Xq V × Xq W, Xq W)).comp (qMapProd V W))
      = (qMap W).comp (prSnd V W) from rfl, ← ContinuousMap.comp_assoc, qPush_comp_qMap]
  rfl

/-- **The algebra isomorphism underlying the transport of `fund_product`**: for a two-dimensional
`W`, `prodAlg V W = C(Xq V × Xq W)` is identified with `C(Xq V × S²)`, compatibly with the two
projections. -/
theorem ba_prodAlgCM (hWd : Module.finrank ℝ W = 2) :
    ∃ (Γ : prodAlg V W ≃ₐ[ℂ] C(Xq V × S2, ℂ)) (EW : Kpair W ≃ₐ[ℂ] C(S2, ℂ)),
      Γ.toAlgHom.comp (pullFst V W) =
        (pullAlg (ContinuousMap.fst : C(Xq V × S2, Xq V))).comp (qIso V).toAlgHom ∧
      Γ.toAlgHom.comp (pullSnd V W) =
        (pullAlg (ContinuousMap.snd : C(Xq V × S2, S2))).comp EW.toAlgHom := by
  obtain ⟨hω⟩ : Nonempty (Xq W ≃ₜ S2) := ba_exists_homeo_Xq_S2 W hWd
  let e : Xq V × S2 ≃ₜ Xq V × Xq W := ba_prodHomeo hω.symm
  let Γ : prodAlg V W ≃ₐ[ℂ] C(Xq V × S2, ℂ) := (prodIso V W).trans (ba_pullAlgEquiv e)
  let EW : Kpair W ≃ₐ[ℂ] C(S2, ℂ) := (qIso W).trans (ba_pullAlgEquiv hω.symm)
  refine ⟨Γ, EW, ?_, ?_⟩
  · apply AlgHom.ext
    intro g
    show ba_pullAlgEquiv e (prodPush V W (pullFst V W g))
      = (pullAlg (ContinuousMap.fst : C(Xq V × S2, Xq V))) (qPush V g)
    rw [ba_prodPush_pullFst V W g]
    ext x
    show (pullAlg (ContinuousMap.fst : C(Xq V × Xq W, Xq V)) (qPush V g)) (e x)
      = (pullAlg (ContinuousMap.fst : C(Xq V × S2, Xq V)) (qPush V g)) x
    show (qPush V g) ((ContinuousMap.fst : C(Xq V × Xq W, Xq V)) (e x))
      = (qPush V g) ((ContinuousMap.fst : C(Xq V × S2, Xq V)) x)
    congr 1
  · apply AlgHom.ext
    intro t
    show ba_pullAlgEquiv e (prodPush V W (pullSnd V W t))
      = (pullAlg (ContinuousMap.snd : C(Xq V × S2, S2))) (ba_pullAlgEquiv hω.symm (qPush W t))
    rw [ba_prodPush_pullSnd V W t]
    ext x
    show (pullAlg (ContinuousMap.snd : C(Xq V × Xq W, Xq W)) (qPush W t)) (e x)
      = (pullAlg (ContinuousMap.snd : C(Xq V × S2, S2))) (ba_pullAlgEquiv hω.symm (qPush W t)) x
    show (qPush W t) ((ContinuousMap.snd : C(Xq V × Xq W, Xq W)) (e x))
      = (ba_pullAlgEquiv hω.symm (qPush W t)) ((ContinuousMap.snd : C(Xq V × S2, S2)) x)
    show (qPush W t) (e x).2 = (qPush W t) (hω.symm x.2)
    congr 1

end ProdAlg

end

end Work.KT
