import Mathlib
import Submission.Work.Mostow.gapA.tubeDefs
import Submission.Work.Mostow.gapA.commuteRotEqOrInv
import Submission.Work.Mostow.gapA.rotSetup

set_option maxHeartbeats 1600000

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

noncomputable section

/-- Polarisation of the quadratic-form identity `mform v (T v) = c * mform v v` on the
perpendicular of the axis plane. -/
private theorem mform_polarize_perp {n : ℕ} (g : PO n 1) (a b : E n) (c : ℝ)
    (hQ : ∀ v : Fin n ⊕ Fin 1 → ℝ, mform v (nvec a) = 0 → mform v (nvec b) = 0 →
      mform v (Matrix.mulVec (emat g) v) = c * mform v v)
    (x y : Fin n ⊕ Fin 1 → ℝ)
    (hxa : mform x (nvec a) = 0) (hxb : mform x (nvec b) = 0)
    (hya : mform y (nvec a) = 0) (hyb : mform y (nvec b) = 0) :
    mform (Matrix.mulVec (emat g) x) y + mform x (Matrix.mulVec (emat g) y)
      = 2 * c * mform x y := by
  have h1 := hQ (x + y) (by rw [mform_add_left, hxa, hya, add_zero])
    (by rw [mform_add_left, hxb, hyb, add_zero])
  have hx := hQ x hxa hxb
  have hy := hQ y hya hyb
  simp only [Matrix.mulVec_add, mform_add_left, mform_add_right, hx, hy] at h1
  rw [mform_comm y (Matrix.mulVec (emat g) x), mform_comm y x] at h1
  linarith

/-- On the perpendicular of the axis plane the lift satisfies `T² = 2c T - id`. -/
private theorem emat_sqOnPerp (g : PO 3 1) (a b : E 3)
    (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) (c : ℝ)
    (hfix : ∀ x : Fin 3 ⊕ Fin 1 → ℝ, x ∈ axisPlane a b → Matrix.mulVec (emat g) x = x)
    (hQ : ∀ v : Fin 3 ⊕ Fin 1 → ℝ, mform v (nvec a) = 0 → mform v (nvec b) = 0 →
      mform v (Matrix.mulVec (emat g) v) = c * mform v v)
    (v : Fin 3 ⊕ Fin 1 → ℝ) (hva : mform v (nvec a) = 0) (hvb : mform v (nvec b) = 0) :
    Matrix.mulVec (emat g) (Matrix.mulVec (emat g) v) = (2 * c) • Matrix.mulVec (emat g) v - v := by
  have hJ : IsJOrth (emat g) := emat_isJOrth g
  have hv : v ∈ axisPerp a b := ⟨hva, hvb⟩
  have hTv : Matrix.mulVec (emat g) v ∈ axisPerp a b :=
    mulVec_mem_axisPerp_of_fixes hJ a b hfix hv
  have hT2v : Matrix.mulVec (emat g) (Matrix.mulVec (emat g) v) ∈ axisPerp a b :=
    mulVec_mem_axisPerp_of_fixes hJ a b hfix hTv
  set z : Fin 3 ⊕ Fin 1 → ℝ :=
    Matrix.mulVec (emat g) (Matrix.mulVec (emat g) v) + v - (2 * c) • Matrix.mulVec (emat g) v
    with hzdef
  have hzmem : z ∈ axisPerp a b := by
    rw [hzdef]
    exact Submodule.sub_mem _ (Submodule.add_mem _ hT2v hv) (Submodule.smul_mem _ _ hTv)
  have hp := mform_polarize_perp g a b c hQ (Matrix.mulVec (emat g) v) z
    hTv.1 hTv.2 hzmem.1 hzmem.2
  have hTz : mform (Matrix.mulVec (emat g) v) (Matrix.mulVec (emat g) z) = mform v z :=
    mform_mulVec_mulVec hJ v z
  have hzz : mform z z = 0 := by
    have h : mform z z
        = (mform (Matrix.mulVec (emat g) (Matrix.mulVec (emat g) v)) z + mform v z)
          - (2 * c) * mform (Matrix.mulVec (emat g) v) z := by
      conv_lhs => rw [hzdef]
      rw [mform_sub_left, mform_add_left, mform_smul_left]
    rw [h]
    linarith [hp, hTz]
  have hz0 : z = 0 := by
    by_contra hne
    exact absurd hzz (ne_of_gt (axisQ_posdef a b ha hb hab z hne hzmem.1 hzmem.2))
  have hmain : Matrix.mulVec (emat g) (Matrix.mulVec (emat g) v) + v
      = (2 * c) • Matrix.mulVec (emat g) v := by
    rw [hzdef] at hz0
    exact sub_eq_zero.mp hz0
  exact eq_sub_iff_add_eq.mpr hmain

/-- de Moivre along the orbit: the powers of `T` act on the perpendicular of the axis plane as
the rotation of angle `α`, where `c = cos α`, `s = sin α ≠ 0`. -/
private theorem powOnPerp_aux (T : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℝ) (a b : E 3)
    (α c s : ℝ) (hc : c = Real.cos α) (hs : s = Real.sin α) (hsne : s ≠ 0)
    (hT2 : ∀ v : Fin 3 ⊕ Fin 1 → ℝ, mform v (nvec a) = 0 → mform v (nvec b) = 0 →
      Matrix.mulVec T (Matrix.mulVec T v) = (2 * c) • Matrix.mulVec T v - v)
    (hTV : ∀ w : Fin 3 ⊕ Fin 1 → ℝ, mform w (nvec a) = 0 → mform w (nvec b) = 0 →
      mform (Matrix.mulVec T w) (nvec a) = 0 ∧ mform (Matrix.mulVec T w) (nvec b) = 0) :
    ∀ k : ℕ, ∀ w : Fin 3 ⊕ Fin 1 → ℝ, mform w (nvec a) = 0 → mform w (nvec b) = 0 →
      Matrix.mulVec (T ^ k) w
        = Real.cos ((k : ℝ) * α) • w
          + (Real.sin ((k : ℝ) * α) / s) • (Matrix.mulVec T w - c • w) := by
  intro k
  induction k with
  | zero =>
      intro w hwa hwb
      rw [pow_zero, Matrix.one_mulVec, Nat.cast_zero, zero_mul, Real.cos_zero, Real.sin_zero,
        one_smul, zero_div, zero_smul, add_zero]
  | succ k ih =>
      intro w hwa hwb
      have hTw := hTV w hwa hwb
      have ihw := ih (Matrix.mulVec T w) hTw.1 hTw.2
      have hsq := hT2 w hwa hwb
      have harg : ((k : ℝ) + 1) * α = (k : ℝ) * α + α := by ring
      have hsin1 : Real.sin (((k : ℝ) + 1) * α)
          = s * Real.cos ((k : ℝ) * α) + c * Real.sin ((k : ℝ) * α) := by
        rw [harg, Real.sin_add, ← hs, ← hc]; ring
      have hcos1 : Real.cos (((k : ℝ) + 1) * α)
          = c * Real.cos ((k : ℝ) * α) - s * Real.sin ((k : ℝ) * α) := by
        rw [harg, Real.cos_add, ← hc, ← hs]; ring
      have hsc : s ^ 2 + c ^ 2 = 1 := by rw [hs, hc]; exact Real.sin_sq_add_cos_sq α
      have hcoef1 : Real.cos ((k : ℝ) * α) + (Real.sin ((k : ℝ) * α) / s) * c
          = Real.sin (((k : ℝ) + 1) * α) / s := by
        rw [hsin1]
        field_simp
        try ring
      have hcoef2 : -(Real.sin ((k : ℝ) * α) / s)
          = Real.cos (((k : ℝ) + 1) * α) - (Real.sin (((k : ℝ) + 1) * α) / s) * c := by
        have hsc' : s ^ 2 = 1 - c ^ 2 := by linarith [hsc]
        rw [hcos1, hsin1]
        field_simp
        ring_nf
        rw [hsc']
        ring
      have hkc : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by push_cast; ring
      rw [pow_succ, ← Matrix.mulVec_mulVec, ihw, hsq, hkc]
      have hL : Real.cos ((k : ℝ) * α) • Matrix.mulVec T w
            + (Real.sin ((k : ℝ) * α) / s)
              • (((2 * c) • Matrix.mulVec T w - w) - c • Matrix.mulVec T w)
          = (Real.sin (((k : ℝ) + 1) * α) / s) • Matrix.mulVec T w
            - (Real.sin ((k : ℝ) * α) / s) • w := by
        rw [show Real.cos ((k : ℝ) * α) • Matrix.mulVec T w
              + (Real.sin ((k : ℝ) * α) / s)
                • (((2 * c) • Matrix.mulVec T w - w) - c • Matrix.mulVec T w)
            = (Real.cos ((k : ℝ) * α) + (Real.sin ((k : ℝ) * α) / s) * c)
                • Matrix.mulVec T w
              - (Real.sin ((k : ℝ) * α) / s) • w from by module]
        rw [hcoef1]
      have hR : Real.cos (((k : ℝ) + 1) * α) • w
            + (Real.sin (((k : ℝ) + 1) * α) / s) • (Matrix.mulVec T w - c • w)
          = (Real.sin (((k : ℝ) + 1) * α) / s) • Matrix.mulVec T w
            - (Real.sin ((k : ℝ) * α) / s) • w := by
        rw [show Real.cos (((k : ℝ) + 1) * α) • w
              + (Real.sin (((k : ℝ) + 1) * α) / s) • (Matrix.mulVec T w - c • w)
            = (Real.sin (((k : ℝ) + 1) * α) / s) • Matrix.mulVec T w
              + (Real.cos (((k : ℝ) + 1) * α) - (Real.sin (((k : ℝ) + 1) * α) / s) * c) • w
            from by module]
        rw [← hcoef2, neg_smul, sub_eq_add_neg]
      rw [hL, hR]

/-- **A rotation about a geodesic by `2π/M` has order `M`.** -/
theorem orderOfRotAbout (hA : Submission.Mostow.POActionProp 3) (hI : Submission.Mostow.HypIsometryProp 3)
    (a b : Submission.Mostow.E 3) (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3)
    (hab : a ≠ b) (M : ℕ) (hM : 0 < M) (b₀ : LeanEval.Geometry.MostowRigidity.PO 3 1)
    (hrot : Work.Mostow.IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ))) :
    orderOf b₀ = M := by
  have hfix : ∀ u : E 3, u ∈ geodSet a b → b₀ • u = u := fun u hu => (hrot.1 u).mpr hu
  have hfixPl : ∀ x : Fin 3 ⊕ Fin 1 → ℝ, x ∈ axisPlane a b → Matrix.mulVec (emat b₀) x = x :=
    emat_fixes_axisPlane b₀ a b ha hb hab hfix
  have hQ : ∀ v : Fin 3 ⊕ Fin 1 → ℝ, mform v (nvec a) = 0 → mform v (nvec b) = 0 →
      mform v (Matrix.mulVec (emat b₀) v) = Real.cos (2 * Real.pi / (M : ℝ)) * mform v v :=
    fun v h1 h2 => emat_cos_form b₀ a b ha hb hab (2 * Real.pi / (M : ℝ)) hrot hfix v h1 h2
  have hfixPow : ∀ k : ℕ, ∀ p : Fin 3 ⊕ Fin 1 → ℝ,
      p ∈ axisPlane a b → Matrix.mulVec ((emat b₀) ^ k) p = p := by
    intro k
    induction k with
    | zero => intro p hp; rw [pow_zero, Matrix.one_mulVec]
    | succ k ih =>
        intro p hp
        have hp' : Matrix.mulVec (emat b₀) p ∈ axisPlane a b := by rw [hfixPl p hp]; exact hp
        rw [pow_succ, ← Matrix.mulVec_mulVec, ih (Matrix.mulVec (emat b₀) p) hp', hfixPl p hp]
  by_cases hM1 : M = 1
  · -- `M = 1`: the "rotation" is the identity
    have h0 : ∀ u : E 3, hdist u (b₀ • u) = 0 := by
      intro u
      have h2 := hrot.2 u
      rw [hM1] at h2
      have hπ : (2 * Real.pi / ((1 : ℕ) : ℝ)) / 2 = Real.pi := by norm_num
      rw [hπ, Real.sin_pi] at h2
      simpa using h2
    have hb1 : b₀ = 1 := hA.2.2.2.2.2.1 b₀
      (fun u => ((hI.2.2.1 u (b₀ • u)).mp (h0 u)).symm)
    rw [hb1, orderOf_one, hM1]
  · by_cases hM2 : M = 2
    · -- `M = 2`: the rotation is minus the identity on the normal plane
      have hc2 : Real.cos (2 * Real.pi / (M : ℝ)) = -1 := by
        rw [hM2]
        have hπ : 2 * Real.pi / ((2 : ℕ) : ℝ) = Real.pi := by norm_num
        rw [hπ, Real.cos_pi]
      have hQ2 : ∀ v : Fin 3 ⊕ Fin 1 → ℝ, mform v (nvec a) = 0 → mform v (nvec b) = 0 →
          mform v (Matrix.mulVec (emat b₀) v) = - mform v v := by
        intro v h1 h2
        rw [hQ v h1 h2, hc2]; ring
      have hneg : ∀ v : Fin 3 ⊕ Fin 1 → ℝ, mform v (nvec a) = 0 → mform v (nvec b) = 0 →
          Matrix.mulVec (emat b₀) v = -v := by
        intro v hva hvb
        have hv : v ∈ axisPerp a b := ⟨hva, hvb⟩
        have hw : Matrix.mulVec (emat b₀) v + v ∈ axisPerp a b :=
          Submodule.add_mem _ (mulVec_mem_axisPerp_of_fixes (emat_isJOrth b₀) a b hfixPl hv) hv
        have hww : mform (Matrix.mulVec (emat b₀) v + v)
            (Matrix.mulVec (emat b₀) v + v) = 0 := by
          rw [mform_add_left, mform_add_right, mform_add_right,
            mform_mulVec_mulVec (emat_isJOrth b₀),
            mform_comm (Matrix.mulVec (emat b₀) v) v, hQ2 v hva hvb]
          ring
        have hw0 : Matrix.mulVec (emat b₀) v + v = 0 := by
          by_contra hne
          exact absurd hww (ne_of_gt (axisQ_posdef a b ha hb hab _ hne hw.1 hw.2))
        exact add_eq_zero_iff_eq_neg.mp hw0
      have hT2 : ∀ v : Fin 3 ⊕ Fin 1 → ℝ, mform v (nvec a) = 0 → mform v (nvec b) = 0 →
          Matrix.mulVec (emat b₀) (Matrix.mulVec (emat b₀) v) = v := by
        intro v hva hvb
        rw [hneg v hva hvb, Matrix.mulVec_neg, hneg v hva hvb, neg_neg]
      have hsq2 : (emat b₀) ^ 2 = 1 := by
        apply Matrix.ext_of_hlift
        intro u
        rw [Matrix.one_mulVec]
        obtain ⟨q, v, hq, hva, hvb, huv⟩ := exists_axis_decomp a b ha hb hab (hlift u)
        rw [huv, pow_two, ← Matrix.mulVec_mulVec]
        rw [Matrix.mulVec_add, hfixPl q hq]
        rw [Matrix.mulVec_add, hfixPl q hq]
        rw [hT2 v hva hvb]
      have hb02 : b₀ ^ 2 = 1 := by
        apply emat_injective hA
        rw [emat_pow hA, hsq2, emat_one hA]
      obtain ⟨Z, hZaθ, hZbθ, hZZ⟩ := perpNullUnit (n := 3) (by norm_num) ha hb hab
      have hZa : mform Z (nvec a) = 0 := by simpa [nvec_eq_theta] using hZaθ
      have hZb : mform Z (nvec b) = 0 := by simpa [nvec_eq_theta] using hZbθ
      have hZne : Z ≠ 0 := by
        intro h0
        rw [h0, mform_zero_left] at hZZ
        norm_num at hZZ
      have hb0ne : b₀ ≠ 1 := by
        intro hone
        have h2 : Matrix.mulVec (emat b₀) Z = Z := by
          rw [hone, emat_one hA, Matrix.one_mulVec]
        have h3 := hneg Z hZa hZb
        rw [h3] at h2
        have h4 : Z = 0 := by
          have hsum2 : (2 : ℝ) • Z = 0 := by
            rw [two_smul]
            nth_rewrite 1 [← h2]
            exact neg_add_cancel Z
          exact (smul_eq_zero.mp hsum2).resolve_left (by norm_num)
        exact hZne h4
      have hdvd : orderOf b₀ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hb02
      have hpos : 0 < orderOf b₀ := by
        rcases Nat.eq_zero_or_pos (orderOf b₀) with h | h
        · exfalso
          rw [orderOf_eq_zero_iff] at h
          exact h (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, hb02⟩)
        · exact h
      have hle : orderOf b₀ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      have hne1 : orderOf b₀ ≠ 1 := fun h => hb0ne (orderOf_eq_one_iff.mp h)
      rw [hM2]
      omega
    · -- `M ≥ 3`
      have hM3 : 3 ≤ M := by omega
      have hsne : Real.sin (2 * Real.pi / (M : ℝ)) ≠ 0 := by
        apply ne_of_gt
        apply Real.sin_pos_of_pos_of_lt_pi
        · positivity
        · rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (M : ℝ))]
          nlinarith [Real.pi_pos,
            show (2 : ℝ) < (M : ℝ) from by exact_mod_cast (by omega : 2 < M)]
      have hT2 : ∀ v : Fin 3 ⊕ Fin 1 → ℝ, mform v (nvec a) = 0 → mform v (nvec b) = 0 →
          Matrix.mulVec (emat b₀) (Matrix.mulVec (emat b₀) v)
            = (2 * Real.cos (2 * Real.pi / (M : ℝ))) • Matrix.mulVec (emat b₀) v - v :=
        fun v h1 h2 =>
          emat_sqOnPerp b₀ a b ha hb hab (Real.cos (2 * Real.pi / (M : ℝ))) hfixPl hQ v h1 h2
      have hTV : ∀ w : Fin 3 ⊕ Fin 1 → ℝ, mform w (nvec a) = 0 → mform w (nvec b) = 0 →
          mform (Matrix.mulVec (emat b₀) w) (nvec a) = 0
            ∧ mform (Matrix.mulVec (emat b₀) w) (nvec b) = 0 :=
        fun w h1 h2 =>
          mulVec_mem_axisPerp_of_fixes (emat_isJOrth b₀) a b hfixPl ⟨h1, h2⟩
      have hpow := powOnPerp_aux (emat b₀) a b (2 * Real.pi / (M : ℝ))
        (Real.cos (2 * Real.pi / (M : ℝ))) (Real.sin (2 * Real.pi / (M : ℝ)))
        rfl rfl hsne hT2 hTV
      have hpowM : ∀ w : Fin 3 ⊕ Fin 1 → ℝ, mform w (nvec a) = 0 → mform w (nvec b) = 0 →
          Matrix.mulVec ((emat b₀) ^ M) w = w := by
        intro w h1 h2
        have h := hpow M w h1 h2
        rw [h]
        have hMα : (M : ℝ) * (2 * Real.pi / (M : ℝ)) = 2 * Real.pi := by
          rw [mul_comm]
          exact div_mul_cancel₀ _ (by positivity : (M : ℝ) ≠ 0)
        rw [hMα, Real.cos_two_pi, Real.sin_two_pi, one_smul, zero_div, zero_smul, add_zero]
      have hmat : (emat b₀) ^ M = 1 := by
        apply Matrix.ext_of_hlift
        intro u
        rw [Matrix.one_mulVec]
        obtain ⟨q, v, hq, hva, hvb, huv⟩ := exists_axis_decomp a b ha hb hab (hlift u)
        rw [huv, Matrix.mulVec_add, hfixPow M q hq, hpowM v hva hvb]
      have hb0M : b₀ ^ M = 1 := by
        apply emat_injective hA
        rw [emat_pow hA, hmat, emat_one hA]
      obtain ⟨Z, hZaθ, hZbθ, hZZ⟩ := perpNullUnit (n := 3) (by norm_num) ha hb hab
      have hZa : mform Z (nvec a) = 0 := by simpa [nvec_eq_theta] using hZaθ
      have hZb : mform Z (nvec b) = 0 := by simpa [nvec_eq_theta] using hZbθ
      have hne : ∀ k : ℕ, 0 < k → k < M → b₀ ^ k ≠ 1 := by
        intro k hk0 hkM hcon
        have h1 : Matrix.mulVec ((emat b₀) ^ k) Z = Z := by
          rw [← emat_pow hA, hcon, emat_one hA, Matrix.one_mulVec]
        have h2 := hpow k Z hZa hZb
        rw [h2] at h1
        have hcos1 : Real.cos ((k : ℝ) * (2 * Real.pi / (M : ℝ))) = 1 := by
          have hcong := congrArg (mform Z) h1
          rw [mform_add_right, mform_smul_right, mform_smul_right, mform_sub_right,
            mform_smul_right, hQ Z hZa hZb, hZZ] at hcong
          simpa using hcong
        have hkαpos : 0 < (k : ℝ) * (2 * Real.pi / (M : ℝ)) := by
          exact mul_pos (by exact_mod_cast hk0) (by positivity)
        have hkαlt : (k : ℝ) * (2 * Real.pi / (M : ℝ)) < 2 * Real.pi := by
          have hMpos : (0 : ℝ) < (M : ℝ) := by positivity
          have hkM' : (k : ℝ) < (M : ℝ) := by exact_mod_cast hkM
          have hratio : (k : ℝ) / (M : ℝ) < 1 := by
            rw [div_lt_one hMpos]; exact hkM'
          calc (k : ℝ) * (2 * Real.pi / (M : ℝ))
              = 2 * Real.pi * ((k : ℝ) / (M : ℝ)) := by ring
            _ < 2 * Real.pi * 1 := mul_lt_mul_of_pos_left hratio (by positivity)
            _ = 2 * Real.pi := by ring
        have hx0 : (k : ℝ) * (2 * Real.pi / (M : ℝ)) = 0 :=
          (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) hkαlt).mp hcos1
        linarith
      have hdvd : orderOf b₀ ∣ M := orderOf_dvd_iff_pow_eq_one.mpr hb0M
      have hpos : 0 < orderOf b₀ := by
        rcases Nat.eq_zero_or_pos (orderOf b₀) with h | h
        · exfalso
          rw [orderOf_eq_zero_iff] at h
          exact h (isOfFinOrder_iff_pow_eq_one.mpr ⟨M, hM, hb0M⟩)
        · exact h
      have hle : orderOf b₀ ≤ M := Nat.le_of_dvd hM hdvd
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact absurd (pow_orderOf_eq_one b₀) (hne (orderOf b₀) hpos hlt)
      · exact heq

end

end Work.Mostow.gapA
