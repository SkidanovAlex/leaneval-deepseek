import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.gapA.geodFacts
import Submission.Work.Mostow.gapA.geodEquiv
import Submission.Work.Mostow.gapA.nilpotentPairNearIdAt
import Submission.Work.Mostow.gapA.commuteRotEqOrInv
import Submission.Work.Mostow.frobeniusCommute
import Submission.Work.Mostow.boundedTorsionAux
import Submission.Work.Mostow.finite_nearStab_compact
import Submission.Work.Mostow.nilp_torsionGen_finite

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

set_option maxHeartbeats 1000000

/-! ## Elementary helpers -/

/-- Membership of a subgroup does not change the order (local copy, so that this file does not
import `Submission.Work.Mostow.gapA_three`). -/
lemma isOfFinOrder_subgroup_coe_iff' {G : Type*} [Group G] (H : Subgroup G) (g : H) :
    IsOfFinOrder (g : G) ↔ IsOfFinOrder g := by
  rw [← orderOf_pos_iff, ← orderOf_pos_iff, Subgroup.orderOf_coe]

/-- `bd` is injective on the boundary sphere. -/
lemma bd_injOn_sph (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (g : LeanEval.Geometry.MostowRigidity.PO n 1) :
    ∀ x y : Submission.Mostow.E n, x ∈ Submission.Mostow.Sph n → y ∈ Submission.Mostow.Sph n →
      Submission.Mostow.bd g x = Submission.Mostow.bd g y → x = y := by
  intro x y hx hy hxy
  have hAb := Work.Mostow.POBasic.ofProp hA
  have h1 : Submission.Mostow.bd g⁻¹ (Submission.Mostow.bd g x)
      = Submission.Mostow.bd g⁻¹ (Submission.Mostow.bd g y) :=
    congrArg (Submission.Mostow.bd g⁻¹) hxy
  have hx' : Submission.Mostow.bd g⁻¹ (Submission.Mostow.bd g x) = x := by
    rw [← hAb.bd_mul g⁻¹ g x hx, inv_mul_cancel, hAb.bd_one x hx]
  have hy' : Submission.Mostow.bd g⁻¹ (Submission.Mostow.bd g y) = y := by
    rw [← hAb.bd_mul g⁻¹ g y hy, inv_mul_cancel, hAb.bd_one y hy]
  rwa [hx', hy'] at h1

/-- `IsRotationAbout` is transported by conjugation. -/
lemma isRotationAbout_conj (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (f : LeanEval.Geometry.MostowRigidity.PO n 1)
    (a b : Submission.Mostow.E n) (ha : a ∈ Submission.Mostow.Sph n)
    (hb : b ∈ Submission.Mostow.Sph n) (hab : a ≠ b) (θ : ℝ)
    (hf : Work.Mostow.IsRotationAbout f a b θ) (g : LeanEval.Geometry.MostowRigidity.PO n 1) :
    Work.Mostow.IsRotationAbout (g⁻¹ * f * g) (Submission.Mostow.bd g⁻¹ a)
      (Submission.Mostow.bd g⁻¹ b) θ := by
  have hAb := Work.Mostow.POBasic.ofProp hA
  have hIb := Work.Mostow.HypIsoData.ofProp hI
  obtain ⟨hfix, hdisp⟩ := hf
  obtain ⟨hgeo1, hgeo2⟩ := Work.Mostow.gapA.geodEquiv n hn hA hI a b ha hb g⁻¹
  have hconj : ∀ u : Submission.Mostow.E n,
      (g⁻¹ * f * g) • u = g⁻¹ • (f • (g • u)) := by
    intro u
    rw [hAb.mul_smul (g⁻¹ * f) g u, hAb.mul_smul g⁻¹ f (g • u)]
  have hcancel : ∀ v : Submission.Mostow.E n, g⁻¹ • (g • v) = v := by
    intro v
    rw [← hAb.mul_smul g⁻¹ g v, inv_mul_cancel, hAb.one_smul]
  constructor
  · intro u
    rw [hconj u]
    have hiff : g⁻¹ • (f • (g • u)) = u ↔ f • (g • u) = g • u := by
      constructor
      · intro h
        have h' := congrArg (fun x : Submission.Mostow.E n => g • x) h
        rw [← hAb.mul_smul g g⁻¹ (f • (g • u)), mul_inv_cancel, hAb.one_smul] at h'
        rw [h']
      · intro h
        rw [h, hcancel u]
    rw [hiff, hfix (g • u), hgeo2 (g • u), hcancel u]
  · intro u
    rw [hconj u, ← hIb.isom_smul g u (g⁻¹ • (f • (g • u)))]
    have hg' : g • (g⁻¹ • (f • (g • u))) = f • (g • u) := by
      rw [← hAb.mul_smul g g⁻¹ (f • (g • u)), mul_inv_cancel, hAb.one_smul]
    rw [hg', hdisp (g • u), ← hgeo1 (g • u), hcancel u]

/-- An element of a finite subgroup has finite order. -/
lemma isOfFinOrder_of_mem_finite_subgroup {G : Type*} [Group G] (S : Subgroup G) [Finite ↑S]
    (g : G) (hg : g ∈ S) : IsOfFinOrder g :=
  (Submonoid.isOfFinOrder_coe).mpr (isOfFinOrder_of_finite (⟨g, hg⟩ : ↑S))

/-- An element of a discrete subgroup fixing a point has finite order. -/
lemma isOfFinOrder_of_fixes_point (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ))
    (g : LeanEval.Geometry.MostowRigidity.PO n 1) (hg : g ∈ Γ) (p : Submission.Mostow.E n)
    (hp : g • p = p) : IsOfFinOrder g := by
  have hAb := Work.Mostow.POBasic.ofProp hA
  have hIb := Work.Mostow.HypIsoData.ofProp hI
  have hfinset : ({γ : Γ | (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • p = p}).Finite := by
    refine (Work.Mostow.finite_nearStab_compact hAb hIb hdisc
      (K₁ := {p}) (K₂ := {p}) isCompact_singleton isCompact_singleton).subset ?_
    rintro γ hγ
    exact ⟨p, rfl, p, rfl, hγ⟩
  -- the stabiliser as a subgroup of `Γ`
  set S : Subgroup Γ :=
    { carrier := {γ : Γ | (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • p = p}
      mul_mem' := by
        intro a b ha hb
        show ((a * b : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) • p = p
        rw [Subgroup.coe_mul, hAb.mul_smul (a : _) (b : _) p, hb, ha]
      one_mem' := by
        show ((1 : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) • p = p
        rw [Subgroup.coe_one, hAb.one_smul]
      inv_mem' := by
        intro a ha
        show (((a⁻¹ : Γ)) : LeanEval.Geometry.MostowRigidity.PO n 1) • p = p
        calc (((a⁻¹ : Γ)) : LeanEval.Geometry.MostowRigidity.PO n 1) • p
            = (((a⁻¹ : Γ)) : LeanEval.Geometry.MostowRigidity.PO n 1) •
                (((a : Γ)) : LeanEval.Geometry.MostowRigidity.PO n 1) • p := by rw [ha]
          _ = ((((a⁻¹ : Γ)) : LeanEval.Geometry.MostowRigidity.PO n 1) *
                (((a : Γ)) : LeanEval.Geometry.MostowRigidity.PO n 1)) • p :=
                (hAb.mul_smul _ _ p).symm
          _ = (1 : LeanEval.Geometry.MostowRigidity.PO n 1) • p := by
                rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
          _ = p := hAb.one_smul p } with hS
  haveI hSfin : Finite ↑S :=
    (show ({γ : Γ | (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • p = p}).Finite from
      hfinset).to_subtype
  exact (isOfFinOrder_subgroup_coe_iff' Γ ⟨g, hg⟩).mpr
    (isOfFinOrder_of_mem_finite_subgroup S (⟨g, hg⟩ : Γ) hp)

/-- If `g` fixes the geodesic `geodSet a b` pointwise then it is near-identity at every point of
that geodesic, with a bound given by the displacement at distance `1`. -/
lemma nearIdAt_of_fixes_geod (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (g : LeanEval.Geometry.MostowRigidity.PO n 1) (a b : Submission.Mostow.E n)
    (ha : a ∈ Submission.Mostow.Sph n) (hb : b ∈ Submission.Mostow.Sph n) (hab : a ≠ b)
    (θ : ℝ) (hf : Work.Mostow.IsRotationAbout g a b θ)
    (δ : ℝ) (hδ : 2 * Real.arsinh (Real.sinh 1 * Real.sin (θ / 2)) < δ)
    (p : Submission.Mostow.E n) (hp : p ∈ Work.Mostow.geodSet a b) :
    Submission.Mostow.NearIdAt g p δ := by
  obtain ⟨hnonempty, hnonneg, hzero, hlip, hfar⟩ :=
    Work.Mostow.gapA.geodFacts n hn hA hI a b ha hb hab
  have hsinpos : 0 ≤ Real.sin (θ / 2) := by
    obtain ⟨u₁, -, hu₁⟩ := hfar p
    have hd : 0 < Real.sinh (Work.Mostow.distGeod a b u₁) :=
      Real.sinh_pos_iff.mpr (lt_of_lt_of_le one_pos hu₁)
    have hge : 0 ≤ Real.arsinh (Real.sinh (Work.Mostow.distGeod a b u₁) * Real.sin (θ / 2)) := by
      have h0 : 0 ≤ Submission.Mostow.hdist u₁ (g • u₁) :=
        (Work.Mostow.HypIsoData.ofProp hI).nonneg _ _
      rw [hf.2 u₁] at h0
      linarith
    have hz : 0 ≤ Real.sinh (Work.Mostow.distGeod a b u₁) * Real.sin (θ / 2) :=
      (Real.arsinh_nonneg_iff).mp hge
    by_contra hcon
    exact absurd hz (not_le.mpr (mul_neg_of_pos_of_neg hd (not_le.mp hcon)))
  intro u hu
  have h1 : Work.Mostow.distGeod a b u ≤ 1 := by
    have h2 := hlip u p
    rw [hzero p |>.mpr hp, sub_zero] at h2
    have h3 : Work.Mostow.distGeod a b u ≤ Submission.Mostow.hdist u p := (abs_le.mp h2).2
    have h4 : Submission.Mostow.hdist u p ≤ 1 := by
      rw [(Work.Mostow.HypIsoData.ofProp hI).symm]; exact hu
    linarith
  rw [hf.2 u]
  refine lt_of_le_of_lt ?_ hδ
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  apply (Real.arsinh_le_arsinh).mpr
  exact mul_le_mul_of_nonneg_right ((Real.sinh_le_sinh).mpr h1) hsinpos

/-- The upper bound on `sin (π/M)` coming from the near-identity of a rotation of angle `2π/M`. -/
lemma sin_pi_div_lt_half {M : ℕ} (_hM : 3 ≤ M) {η : ℝ}
    (h : 2 * Real.arsinh (Real.sinh 1 * Real.sin (Real.pi / (M : ℝ))) < η) (hη : η ≤ 1 / 1000) :
    Real.sin (Real.pi / (M : ℝ)) < 1 / 2 := by
  have h1 : Real.arsinh (Real.sinh 1 * Real.sin (Real.pi / (M : ℝ))) < 1 / 2000 := by linarith
  have h2 : Real.sinh 1 * Real.sin (Real.pi / (M : ℝ)) < Real.sinh (1 / 2000) := by
    have h1' : Real.arsinh (Real.sinh 1 * Real.sin (Real.pi / (M : ℝ)))
        < Real.arsinh (Real.sinh (1 / 2000)) := by
      rwa [Real.arsinh_sinh]
    exact (Real.arsinh_lt_arsinh).mp h1'
  have hexp : Real.exp (1 / 2000) ≤ 1 / (1 - 1 / 2000) :=
    Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
  have hexpn : (1 : ℝ) - 1 / 2000 ≤ Real.exp (-(1 / 2000)) := by
    have h := Real.add_one_le_exp (-(1 / 2000))
    linarith
  have hsinh2000 : Real.sinh (1 / 2000) < 1 / 4 := by
    have hdef : Real.sinh (1 / 2000) = (Real.exp (1 / 2000) - Real.exp (-(1 / 2000))) / 2 :=
      Real.sinh_eq (1 / 2000)
    rw [hdef]
    have h3 : Real.exp (1 / 2000) - Real.exp (-(1 / 2000))
        ≤ 1 / (1 - 1 / 2000) - (1 - 1 / 2000) := sub_le_sub hexp hexpn
    have h4 : 1 / (1 - 1 / 2000 : ℝ) - (1 - 1 / 2000) = 1 / 1999 + 1 / 2000 := by
      norm_num
    have h5 : (1 / 1999 + 1 / 2000 : ℝ) / 2 < 1 / 4 := by norm_num
    linarith [h4 ▸ h3]
  have hsinh1 : (1 / 2 : ℝ) ≤ Real.sinh 1 := by
    have h6 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp 1
      linarith
    have h7 : Real.exp (-1) ≤ 1 := by
      have := Real.exp_le_exp.mpr (by norm_num : (-1 : ℝ) ≤ 0)
      rwa [Real.exp_zero] at this
    have h8 : Real.sinh 1 = (Real.exp 1 - Real.exp (-1)) / 2 := Real.sinh_eq 1
    rw [h8]; linarith
  have h10 : Real.sinh 1 * Real.sin (Real.pi / (M : ℝ)) < 1 / 4 := lt_trans h2 hsinh2000
  have h11 : Real.sin (Real.pi / (M : ℝ)) < 1 / 2 := by
    nlinarith [hsinh1, h10]
  exact h11

/-- `sin (π/M) < 1/2` with `M ≥ 3` forces `6 ≤ M`. -/
lemma six_le_of_sin_lt (M : ℕ) (hM : 3 ≤ M) (h : Real.sin (Real.pi / (M : ℝ)) < 1 / 2) :
    6 ≤ M := by
  by_contra hcon
  have hM5 : M ≤ 5 := by omega
  have hMpos : (0:ℝ) < (M : ℝ) := by positivity
  have h1 : Real.pi / (5 : ℝ) ≤ Real.pi / (M : ℝ) :=
    div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) hMpos (by exact_mod_cast hM5)
  have h2 : Real.pi / (M : ℝ) ≤ Real.pi / 2 := by
    have h2a : Real.pi / (M : ℝ) ≤ Real.pi / 3 :=
      div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) (by norm_num)
        (by exact_mod_cast hM : (3:ℝ) ≤ (M:ℝ))
    linarith [Real.pi_pos, h2a]
  have h3 : -(Real.pi / 2) ≤ Real.pi / 5 := by linarith [Real.pi_pos]
  have h4 : Real.sin (Real.pi / 5) ≤ Real.sin (Real.pi / (M : ℝ)) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two h3 h2 h1
  have h5 : (1 / 2 : ℝ) ≤ Real.sin (Real.pi / 5) := by
    have h6 : -(Real.pi / 2) ≤ Real.pi / 6 := by linarith [Real.pi_pos]
    have h7 : Real.pi / 5 ≤ Real.pi / 2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by norm_num)
    have h8 : Real.pi / 6 ≤ Real.pi / 5 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by norm_num)
    have := Real.sin_le_sin_of_le_of_le_pi_div_two h6 h7 h8
    rwa [Real.sin_pi_div_six] at this
  linarith

/-! ## The main theorem -/

theorem conjCount3 (hA : Submission.Mostow.POActionProp 3) (hI : Submission.Mostow.HypIsometryProp 3)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO 3 1)) (hΓ : Submission.Mostow.HypLattice Γ) :
    ∃ η_Z : ℝ, 0 < η_Z ∧ ∀ (M : ℕ) (_hM : 3 ≤ M)
      (a b : Submission.Mostow.E 3) (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3)
      (hab : a ≠ b) (b₀ : LeanEval.Geometry.MostowRigidity.PO 3 1) (hb₀ : b₀ ∈ Γ)
      (hrot : Work.Mostow.IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)))
      (η₁ : ℝ) (hη₁ : 0 < η₁) (hη₁Z : η₁ ≤ η_Z)
      (w : Submission.Mostow.E 3) (γ : LeanEval.Geometry.MostowRigidity.PO 3 1) (_hγ : γ ∈ Γ),
      Submission.Mostow.NearIdAt b₀ w η₁ → Submission.Mostow.NearIdAt (γ⁻¹ * b₀ * γ) w η₁ →
      γ⁻¹ * b₀ * γ = b₀ ∨ γ⁻¹ * b₀ * γ = b₀⁻¹ := by
  have hAb := Work.Mostow.POBasic.ofProp hA
  have hIb := Work.Mostow.HypIsoData.ofProp hI
  obtain ⟨θZ, hθZpos, hθZ⟩ := Work.Mostow.gapA.nilpotentPairNearIdAt 3 (by norm_num) hA hI
  obtain ⟨θF, hθFpos, hθF⟩ := Work.Mostow.frobeniusCommute 3 (by norm_num) hA hI
  refine ⟨min (min (θZ / 2) (θF / 2)) (1 / 1000), by positivity, ?_⟩
  intro M hM a b ha hb hab b₀ hb₀ hrot η₁ hη₁ hη₁Z w γ hγ h1 h2
  have hηθZhalf : η₁ ≤ θZ / 2 := le_trans hη₁Z (le_trans (min_le_left _ _) (min_le_left _ _))
  have hηθFhalf : η₁ ≤ θF / 2 := le_trans hη₁Z (le_trans (min_le_left _ _) (min_le_right _ _))
  have hη1000 : η₁ ≤ 1 / 1000 := le_trans hη₁Z (min_le_right _ _)
  -- geometric facts about the geodesic
  obtain ⟨hnonempty, hnonneg, hzero, hlip, hfar⟩ :=
    Work.Mostow.gapA.geodFacts 3 (by norm_num) hA hI a b ha hb hab
  -- Step 1: the displacement bound from a far point
  obtain ⟨u₀, hu₀1, hu₀2⟩ := hfar w
  have hstep : 2 * Real.arsinh (Real.sinh 1 * Real.sin (Real.pi / (M : ℝ))) < η₁ := by
    have hu := h1 u₀ hu₀1
    rw [hrot.2 u₀] at hu
    rw [show (2 * Real.pi / (M : ℝ)) / 2 = Real.pi / (M : ℝ) by ring] at hu
    refine lt_of_le_of_lt ?_ hu
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
    apply (Real.arsinh_le_arsinh).mpr
    refine mul_le_mul_of_nonneg_right ((Real.sinh_le_sinh).mpr hu₀2) ?_
    have hM3 : (3:ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hpi : Real.pi / (M : ℝ) ≤ Real.pi := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_pos, hM3]
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) hpi
  -- Step 2: `6 ≤ M`
  have hM6 : 6 ≤ M := six_le_of_sin_lt M hM (sin_pi_div_lt_half hM hstep hη1000)
  -- Step 3: the conjugated rotation
  have hrot₁ : Work.Mostow.IsRotationAbout (γ⁻¹ * b₀ * γ) (Submission.Mostow.bd γ⁻¹ a)
      (Submission.Mostow.bd γ⁻¹ b) (2 * Real.pi / (M : ℝ)) :=
    isRotationAbout_conj 3 (by norm_num) hA hI b₀ a b ha hb hab (2 * Real.pi / (M:ℝ)) hrot γ
  have hbda : Submission.Mostow.bd γ⁻¹ a ∈ Submission.Mostow.Sph 3 := hAb.bd_mem _ _ ha
  have hbdb : Submission.Mostow.bd γ⁻¹ b ∈ Submission.Mostow.Sph 3 := hAb.bd_mem _ _ hb
  have hbdab : Submission.Mostow.bd γ⁻¹ a ≠ Submission.Mostow.bd γ⁻¹ b := by
    intro heq
    exact hab (bd_injOn_sph 3 hA γ⁻¹ a b ha hb heq)
  -- Step 4: Zassenhaus
  have hγmem : γ⁻¹ * b₀ * γ ∈ Γ := Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) hb₀) hγ
  have h1Z : Submission.Mostow.NearIdAt b₀ w θZ :=
    fun u hu => lt_of_lt_of_le (h1 u hu) (by linarith [hηθZhalf, hθZpos])
  have h2Z : Submission.Mostow.NearIdAt (γ⁻¹ * b₀ * γ) w θZ :=
    fun u hu => lt_of_lt_of_le (h2 u hu) (by linarith [hηθZhalf, hθZpos])
  have hnil : Group.IsNilpotent (Subgroup.closure
      ({b₀, γ⁻¹ * b₀ * γ} : Set (LeanEval.Geometry.MostowRigidity.PO 3 1))) :=
    hθZ Γ hΓ.1 w ⟨b₀, hb₀⟩ ⟨γ⁻¹ * b₀ * γ, hγmem⟩ h1Z h2Z
  -- Step 5: torsion
  obtain ⟨p₀, hp₀⟩ := hnonempty
  have hb₀p₀ : b₀ • p₀ = p₀ := (hrot.1 p₀).mpr hp₀
  have htor₀ : IsOfFinOrder b₀ := isOfFinOrder_of_fixes_point 3 hA hI Γ hΓ.1 b₀ hb₀ p₀ hb₀p₀
  have hp₀' : (γ⁻¹ * b₀ * γ) • (γ⁻¹ • p₀) = γ⁻¹ • p₀ := by
    rw [hAb.mul_smul (γ⁻¹ * b₀) γ (γ⁻¹ • p₀), hAb.mul_smul γ⁻¹ b₀ (γ • (γ⁻¹ • p₀))]
    have h1 : γ • (γ⁻¹ • p₀) = p₀ := by
      rw [← hAb.mul_smul γ γ⁻¹ p₀, mul_inv_cancel, hAb.one_smul]
    rw [h1, hb₀p₀]
  have htor₁ : IsOfFinOrder (γ⁻¹ * b₀ * γ) :=
    isOfFinOrder_of_fixes_point 3 hA hI Γ hΓ.1 (γ⁻¹ * b₀ * γ) hγmem (γ⁻¹ • p₀) hp₀'
  -- Step 6: finiteness of the closure
  set H : Subgroup (LeanEval.Geometry.MostowRigidity.PO 3 1) :=
    Subgroup.closure ({b₀, γ⁻¹ * b₀ * γ} : Set (LeanEval.Geometry.MostowRigidity.PO 3 1)) with hHdef
  haveI : Group.IsNilpotent ↥H := hnil
  haveI : Group.FG ↥H :=
    Group.closure_finite_fg ({b₀, γ⁻¹ * b₀ * γ} : Set (LeanEval.Geometry.MostowRigidity.PO 3 1))
  have hgen : Subgroup.closure {h : ↥H | IsOfFinOrder h} = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro x
    have hb₀H : IsOfFinOrder (⟨b₀, by rw [hHdef]; exact Subgroup.subset_closure (by simp)⟩ : ↥H) :=
      (Submonoid.isOfFinOrder_coe).mp htor₀
    have hb₁H : IsOfFinOrder (⟨γ⁻¹ * b₀ * γ,
        by rw [hHdef]; exact Subgroup.subset_closure (by simp)⟩ : ↥H) :=
      (Submonoid.isOfFinOrder_coe).mp htor₁
    have hsub : H ≤ (Subgroup.closure {h : ↥H | IsOfFinOrder h}).map H.subtype := by
      rw [hHdef, Subgroup.closure_le]
      intro y hy
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ⟨_, Subgroup.subset_closure hb₀H, rfl⟩
      · exact ⟨_, Subgroup.subset_closure hb₁H, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hsub x.2
    have hyx' : y = x := Subtype.ext hyx
    rwa [hyx'] at hy
  haveI hHfin : Finite ↥H := Work.Mostow.nilp_torsionGen_finite hgen
  -- Step 7: a common fixed point
  obtain ⟨p, hp⟩ := Work.Mostow.fixPoint_of_finite hA H hHfin
  have hb₀H : b₀ ∈ H := by rw [hHdef]; exact Subgroup.subset_closure (by simp)
  have hb₁H : γ⁻¹ * b₀ * γ ∈ H := by rw [hHdef]; exact Subgroup.subset_closure (by simp)
  have hpg : p ∈ Work.Mostow.geodSet a b := (hrot.1 p).mp (hp b₀ hb₀H)
  have hpg₁ : p ∈ Work.Mostow.geodSet (Submission.Mostow.bd γ⁻¹ a) (Submission.Mostow.bd γ⁻¹ b) :=
    (hrot₁.1 p).mp (hp (γ⁻¹ * b₀ * γ) hb₁H)
  -- Step 8: near-identity at the fixed point
  have hδF : 2 * Real.arsinh (Real.sinh 1 * Real.sin ((2 * Real.pi / (M:ℝ)) / 2)) < θF := by
    have h2pi : (2 * Real.pi / (M:ℝ)) / 2 = Real.pi / (M:ℝ) := by ring
    rw [h2pi]
    linarith [hstep, hηθFhalf, hθFpos]
  have hnear₀ : Submission.Mostow.NearIdAt b₀ p θF :=
    nearIdAt_of_fixes_geod 3 (by norm_num) hA hI b₀ a b ha hb hab (2 * Real.pi / (M:ℝ)) hrot θF
      hδF p hpg
  have hnear₁ : Submission.Mostow.NearIdAt (γ⁻¹ * b₀ * γ) p θF :=
    nearIdAt_of_fixes_geod 3 (by norm_num) hA hI (γ⁻¹ * b₀ * γ) (Submission.Mostow.bd γ⁻¹ a)
      (Submission.Mostow.bd γ⁻¹ b) hbda hbdb hbdab (2 * Real.pi / (M:ℝ)) hrot₁ θF hδF p hpg₁
  -- Step 9: commutativity from the finite-group lemma
  have hcomm : b₀ * (γ⁻¹ * b₀ * γ) = (γ⁻¹ * b₀ * γ) * b₀ :=
    hθF H hHfin p hp b₀ hb₀H (γ⁻¹ * b₀ * γ) hb₁H hnear₀ hnear₁
  -- Step 10: the final geometric step
  exact commuteRotEqOrInv hA hI M hM6 a b (Submission.Mostow.bd γ⁻¹ a) (Submission.Mostow.bd γ⁻¹ b)
    ha hb hbda hbdb hab hbdab b₀ (γ⁻¹ * b₀ * γ) hrot hrot₁ hcomm

end Work.Mostow.gapA
