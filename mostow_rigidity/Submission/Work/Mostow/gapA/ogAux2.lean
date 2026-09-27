import Mathlib
import Submission.Work.Mostow.gapA.ogAux
import Submission.Work.Mostow.QIDefs

/-!
# Pieces of the `oriented_generator` proof

* `hdist_two_mul_fixed`: an isometry fixing a point moves the base point by at most twice the
  distance to that point;
* `fixed_mem_geodSet`: the fixed points of a rotation about `geodSet a b` lie on `geodSet a b`;
* `finite_inter_axisSub`: the intersection of a lattice with the pointwise stabiliser of a
  geodesic is finite;
* `mink_self_nonneg_of_mem_NormP`, `eq_zero_of_mem_NormP_of_mink_self_eq_zero`,
  `finrank_NormP`: the normal plane is positive definite of dimension `2`;
* `pb_exists`: existence of an orthonormal basis of the normal plane;
* `rotMat_det`: the normal action of `g ∈ AxisSub` has determinant `1`;
* `exp_pow_eq_one_iff_dvd`, `orderOf_exp_neg`, `zpowers_eq_of_card`: the order theory of
  `exp (-(2π/n) i)` in `ℂˣ`.
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open _root_.Matrix

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

variable {a b : E 3}

/-! ## Two elementary geometric lemmas -/

theorem hdist_two_mul_fixed (hI : Submission.Mostow.HypIsometryProp 3)
    (g : LeanEval.Geometry.MostowRigidity.PO 3 1) (p : Submission.Mostow.E 3)
    (hp : g • p = p) :
    Submission.Mostow.hdist (0 : Submission.Mostow.E 3) (g • (0 : Submission.Mostow.E 3)) ≤
      2 * Submission.Mostow.hdist (0 : Submission.Mostow.E 3) p := by
  have hI' := HypIsoData.ofProp hI
  have h1 := hI'.triangle (0 : E 3) p (g • (0 : E 3))
  have h2 := hI'.triangle p (g • p) (g • (0 : E 3))
  have h3 : hdist p (g • p) = 0 := by
    rw [hp]
    exact (hI'.eq_zero p p).mpr rfl
  have h4 : hdist (g • p) (g • (0 : E 3)) = hdist p 0 := hI'.isom_smul g p 0
  have h5 : hdist p 0 = hdist 0 p := hI'.symm p 0
  linarith

theorem fixed_mem_geodSet (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3) (a b : Submission.Mostow.E 3)
    (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3) (hab : a ≠ b)
    (B : Work.Mostow.gapA.PB a b) (g : LeanEval.Geometry.MostowRigidity.PO 3 1)
    (hg : g ∈ Work.Mostow.gapA.AxisSub hA a b)
    (c : ℝ) (hc : c ≠ 1)
    (hparam : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Work.Mostow.mink Z (Work.Mostow.nvec a) = 0 →
      Work.Mostow.mink Z (Work.Mostow.nvec b) = 0 →
      Work.Mostow.mink (Matrix.mulVec (Work.Mostow.emat g) Z) Z = c * Work.Mostow.mink Z Z)
    {u : Submission.Mostow.E 3} (hu : g • u = u) :
    u ∈ Work.Mostow.geodSet a b := by
  obtain ⟨hg1, hg2, -⟩ := mem_AxisSub_iff.mp hg
  have hkey := mink_hlift_emat_hlift hA hI g a b u ha hb hab hg1 hg2 c hparam
  have h1 : mink (hlift u) (Matrix.mulVec (emat g) (hlift u)) = -1 := by
    rw [emat_hlift, hu, mink_hlift_self']
  rw [h1] at hkey
  have h2 : (1 - c) * mink (gcN a b u) (gcN a b u) = 0 := by linarith
  have h3 : mink (gcN a b u) (gcN a b u) = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (sub_eq_zero.mp h) (Ne.symm hc)
    · exact h
  exact (gcN_eq_zero_iff a b ha hb hab u).mp (gcN_eq_zero_of_self a b ha hb hab u h3)

/-! ## Finiteness of the intersection with a lattice -/

theorem finite_inter_axisSub (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO 3 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (a b : Submission.Mostow.E 3) (ha : a ∈ Submission.Mostow.Sph 3)
    (hb : b ∈ Submission.Mostow.Sph 3) (hab : a ≠ b) :
    Finite ↥(Γ ⊓ Work.Mostow.gapA.AxisSub hA a b) := by
  have hI' := HypIsoData.ofProp hI
  have hR : ({γ : Γ | Submission.Mostow.hdist (0 : E 3)
      ((γ : PO 3 1) • (0 : E 3)) ≤ 2 * Submission.Mostow.hdist (0 : E 3) (gcAxisPt a b 0)}
      : Set Γ).Finite :=
    finite_nearStab (POBasic.ofProp hA) hI' hΓ.1 _
  set f : ↥(Γ ⊓ AxisSub hA a b) → Γ :=
    fun g => ⟨(g : PO 3 1), (Subgroup.mem_inf.mp g.2).1⟩ with hf
  have hsub : ∀ g, f g ∈ ({γ : Γ | Submission.Mostow.hdist (0 : E 3)
      ((γ : PO 3 1) • (0 : E 3)) ≤ 2 * Submission.Mostow.hdist (0 : E 3) (gcAxisPt a b 0)}
      : Set Γ) := by
    intro g
    have hmem : (g : PO 3 1) ∈ AxisSub hA a b := (Subgroup.mem_inf.mp g.2).2
    have hfix : (g : PO 3 1) • (gcAxisPt a b 0) = gcAxisPt a b 0 :=
      geodSet_fixed_of_mem_AxisSub hA ha hb hab hmem _ (gcAxisPt_mem_geodSet a b ha hb hab 0)
    exact hdist_two_mul_fixed hI (g : PO 3 1) (gcAxisPt a b 0) hfix
  have hinj : Function.Injective f := by
    intro g h hgh
    exact Subtype.ext (congrArg (fun z : Γ => (z : PO 3 1)) hgh)
  have hpre : f ⁻¹' ({γ : Γ | Submission.Mostow.hdist (0 : E 3)
      ((γ : PO 3 1) • (0 : E 3)) ≤ 2 * Submission.Mostow.hdist (0 : E 3) (gcAxisPt a b 0)}
      : Set Γ) = Set.univ :=
    Set.eq_univ_of_forall (fun g => hsub g)
  have hfin : (Set.univ : Set ↥(Γ ⊓ AxisSub hA a b)).Finite := by
    rw [← hpre]
    exact hR.preimage (fun _ _ _ _ h' => hinj h')
  exact Set.finite_univ_iff.mp hfin

/-! ## The normal plane is positive definite of dimension `2` -/

lemma mink_pair_ne_zero (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) :
    mink (nvec a) (nvec b) ≠ 0 := by
  rw [mink_nvec_nvec']
  have hlt : inner ℝ a b < 1 :=
    inner_lt_one_of_ne_unit ((mem_Sph_iff a).mp ha) ((mem_Sph_iff b).mp hb) hab
  linarith

lemma mink_self_nonneg_of_mem_NormP (ha : a ∈ Sph 3) {Z : Fin 3 ⊕ Fin 1 → ℝ}
    (hZ : Z ∈ NormP a b) : 0 ≤ mink Z Z := by
  have hZa : mform Z (theta a) = 0 := by
    rw [← mink_eq_mform, ← nvec_eq_theta]
    exact (mem_NormP.mp hZ).1
  rw [mink_eq_mform, mform_self_eq_hspat_horoProj ha hZa]
  positivity

lemma eq_zero_of_mem_NormP_of_mink_self_eq_zero (ha : a ∈ Sph 3) (hb : b ∈ Sph 3)
    (hab : a ≠ b) {Z : Fin 3 ⊕ Fin 1 → ℝ} (hZ : Z ∈ NormP a b) (h0 : mink Z Z = 0) :
    Z = 0 := by
  have hZa : mform Z (theta a) = 0 := by
    rw [← mink_eq_mform, ← nvec_eq_theta]
    exact (mem_NormP.mp hZ).1
  have hZb : mink Z (nvec b) = 0 := (mem_NormP.mp hZ).2
  have hnorm : ‖hspat (horoProj a Z)‖ = 0 := by
    have h := mform_self_eq_hspat_horoProj ha hZa
    rw [← mink_eq_mform, h0] at h
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h.symm
  have hsp : hspat (horoProj a Z) = 0 := norm_eq_zero.mp hnorm
  have hht : htime (horoProj a Z) = 0 := htime_eq_zero_of_horoProj a ha (horoProj_idem a ha Z)
  have hproj : horoProj a Z = 0 := by
    rw [eq_elim_hspat_htime (horoProj a Z), hsp, hht]
    ext k
    rcases k with i | j
    · simp
    · simp
  have hdec := eq_horoProj_add hZa
  rw [hproj, zero_add] at hdec
  have hq : mform Z (horoEta a) = 0 := by
    have hpair : mform Z (theta b) = (mform Z (horoEta a) / 2) * mform (theta a) (theta b) := by
      conv_lhs => rw [hdec]
      rw [mform_smul_left, mform_theta_theta_pair]
    have hb0 : mform Z (theta b) = 0 := by
      rw [← mink_eq_mform, ← nvec_eq_theta]
      exact hZb
    rw [hb0] at hpair
    have hne : mform (theta a) (theta b) ≠ 0 := by
      rw [← mink_eq_mform, ← nvec_eq_theta, ← nvec_eq_theta]
      exact mink_pair_ne_zero ha hb hab
    have hq2 : mform Z (horoEta a) / 2 = 0 := (mul_eq_zero.mp hpair.symm).resolve_right hne
    exact (div_eq_zero_iff.mp hq2).resolve_right (by norm_num)
  rw [hdec, hq]
  simp

lemma finrank_NormP (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) :
    Module.finrank ℝ (NormP a b) = 2 := by
  classical
  have hc : mink (nvec a) (nvec b) ≠ 0 := mink_pair_ne_zero ha hb hab
  set f : (Fin 3 ⊕ Fin 1 → ℝ) →ₗ[ℝ] ℝ × ℝ :=
    { toFun := fun x => (mink x (nvec a), mink x (nvec b))
      map_add' := by intro x y; simp [minkSeg_add_left]
      map_smul' := by intro c x; simp [mink_smul_left''] } with hf
  have hker : LinearMap.ker f = NormP a b := by
    ext x
    rw [LinearMap.mem_ker, mem_NormP]
    constructor
    · intro hx
      exact ⟨congrArg Prod.fst hx, congrArg Prod.snd hx⟩
    · rintro ⟨h1, h2⟩
      exact Prod.ext h1 h2
  have hrange : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    refine ⟨(y.1 / mink (nvec b) (nvec a)) • nvec b
      + (y.2 / mink (nvec a) (nvec b)) • nvec a, ?_⟩
    have h1 : mink (nvec a) (nvec a) = 0 := mink_nvec_self' ha
    have h2 : mink (nvec b) (nvec b) = 0 := mink_nvec_self' hb
    have hba : mink (nvec b) (nvec a) = mink (nvec a) (nvec b) := minkSeg_comm _ _
    refine Prod.ext ?_ ?_
    · show mink ((y.1 / mink (nvec b) (nvec a)) • nvec b
          + (y.2 / mink (nvec a) (nvec b)) • nvec a) (nvec a) = y.1
      rw [minkSeg_add_left, mink_smul_left'', mink_smul_left'', h1]
      simp only [mul_zero, add_zero]
      exact div_mul_cancel₀ y.1 (by rw [hba]; exact hc)
    · show mink ((y.1 / mink (nvec b) (nvec a)) • nvec b
          + (y.2 / mink (nvec a) (nvec b)) • nvec a) (nvec b) = y.2
      rw [minkSeg_add_left, mink_smul_left'', mink_smul_left'', h2]
      simp only [mul_zero, zero_add]
      exact div_mul_cancel₀ y.2 hc
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hker, finrank_top] at h1
  have h2 : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp [Module.finrank_prod]
  have h3 : Module.finrank ℝ (Fin 3 ⊕ Fin 1 → ℝ) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  omega

/-! ## The order of `exp (-(2π/n) i)` -/

lemma exp_pow_eq_one_iff_dvd (n : ℕ) (hn : 0 < n) (z : ℂˣ)
    (hz : (z : ℂ) = Complex.exp (-(2 * Real.pi / (n : ℝ)) * Complex.I)) (m : ℕ) :
    z ^ m = 1 ↔ n ∣ m := by
  have hn0 : n ≠ 0 := hn.ne'
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (n : ℝ))) n :=
    Complex.isPrimitiveRoot_exp n hn0
  set u : ℂˣ := Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / (n : ℝ)))
    (Complex.exp_ne_zero _) with hu
  have hzu : z = u⁻¹ := by
    ext
    rw [hz, hu, Units.val_inv_eq_inv_val, Units.val_mk0, ← Complex.exp_neg]
    congr 1
    ring
  rw [hzu, inv_pow, inv_eq_one]
  constructor
  · intro h
    have h' : (Complex.exp (2 * Real.pi * Complex.I / (n : ℝ))) ^ m = 1 := by
      have := congrArg (fun w : ℂˣ => (w : ℂ)) h
      simpa [hu, Units.val_pow_eq_pow_val] using this
    exact (hζ.pow_eq_one_iff_dvd m).mp h'
  · intro h
    apply Units.ext
    simp only [hu, Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0]
    exact (hζ.pow_eq_one_iff_dvd m).mpr h

theorem orderOf_exp_neg (n : ℕ) (hn : 0 < n) (z : ℂˣ)
    (hz : (z : ℂ) = Complex.exp (-(2 * Real.pi / (n : ℝ)) * Complex.I)) : orderOf z = n := by
  have h1 : orderOf z ∣ n :=
    orderOf_dvd_iff_pow_eq_one.mpr ((exp_pow_eq_one_iff_dvd n hn z hz n).mpr (dvd_refl n))
  have h2 : n ∣ orderOf z :=
    (exp_pow_eq_one_iff_dvd n hn z hz (orderOf z)).mp (pow_orderOf_eq_one z)
  exact Nat.dvd_antisymm h1 h2

/-- If a finite subgroup `G ≤ ℂˣ` of order `n` contains `exp (-(2π/n) i)`, then it is generated
by it. -/
lemma zpowers_eq_of_card (n : ℕ) (hn : 0 < n) (G : Subgroup ℂˣ) [Finite ↥G]
    (hcard : Nat.card G = n)
    (hle : G ≤ rootsOfUnity n ℂ) (z : ℂˣ) (hzG : z ∈ G)
    (hz : (z : ℂ) = Complex.exp (-(2 * Real.pi / (n : ℝ)) * Complex.I)) :
    G = Subgroup.zpowers z := by
  have hord : orderOf z = n := orderOf_exp_neg n hn z hz
  have hzle : Subgroup.zpowers z ≤ G := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact G.zpow_mem hzG k
  have hcardz : Nat.card ↥G ≤ Nat.card ↥(Subgroup.zpowers z) := by
    rw [Nat.card_zpowers, hord, hcard]
  exact (Subgroup.eq_of_le_of_card_ge hzle hcardz).symm

end

end Work.Mostow.gapA
