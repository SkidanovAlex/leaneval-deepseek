import Mathlib
import Submission.Work.RPCore.Defs
import Submission.Work.RPCore.Flow.Basic
import Submission.Work.RPCore.Saddle.descent_dir_exists
import Submission.Work.RPCore.Saddle.taylor_second_order_closedBall

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

namespace Work.RPCore.Saddle

open Set
open scoped Topology

noncomputable section

/-- The ambient space `ℝ × (ℝ^k × ℝ^l)` of the saddle-descent construction. -/
abbrev Dom (k l : ℕ) : Type := ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))

theorem exists_descent_isotopy {k l : ℕ}
    (F : ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) → ℝ)
    (hF : ContDiff ℝ 2 F) (δ : ℝ) (hδ : 0 < δ)
    (hδF : ∀ z, δ ≤ ‖fderiv ℝ F z‖)
    (U : Set (ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)))) (hUopen : IsOpen U)
    (R : ℝ) (hUR : ∀ z ∈ U, ‖z‖ ≤ R)
    (c c' : ℝ) (hc'c : c' < c) (hU : ∀ z ∈ U, F z ≤ c') :
    ∃ η : (ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))) →
        (ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))),
      Continuous η ∧ (∀ z ∈ U, η z = z) ∧
      (∀ z, ‖z‖ ≤ R → F z ≤ c + 1 / 2 → F (η z) ≤ max (F z - 1) ((c + c') / 2)) := by
  by_cases hRneg : R < 0
  · refine ⟨id, continuous_id, fun z _ => rfl, ?_⟩
    intro z hz _
    exact absurd (le_trans (norm_nonneg z) hz) (not_le.mpr hRneg)
  · push_neg at hRneg
    obtain ⟨u, hucont, hu1, hud⟩ :=
      descent_dir_exists F (hF.of_le (by norm_num)) δ hδ hδF
    set ρ : ℝ := R + 4 / δ + 4 with hρdef
    obtain ⟨M, hM0, hMbound⟩ := taylor_second_order_closedBall F hF ρ
    set s : ℝ := min 1 (δ / (4 * (M + 1))) with hsdef
    have hspos : 0 < s := lt_min zero_lt_one (by positivity)
    have hsle1 : s ≤ 1 := min_le_left _ _
    have hsb : s ≤ δ / (4 * (M + 1)) := min_le_right _ _
    have hMs : M * s ≤ δ / 2 := by
      have h2 : M * (δ / (4 * (M + 1))) ≤ δ / 2 := by
        have hpos : (0 : ℝ) < 4 * (M + 1) := by positivity
        have heq : M * (δ / (4 * (M + 1))) = M * δ / (4 * (M + 1)) := by ring
        rw [heq, div_le_iff₀ hpos]
        nlinarith [hδ, hM0]
      exact le_trans (mul_le_mul_of_nonneg_left hsb hM0) h2
    set e : ℝ := s * δ / 4 with hedef
    have hepos : 0 < e := by rw [hedef]; positivity
    set N : ℕ := ⌈(4 / δ + 1) / s⌉₊ + 1 with hNdef
    have hNcast : (N : ℝ) = (⌈(4 / δ + 1) / s⌉₊ : ℝ) + 1 := by
      rw [hNdef]; push_cast; ring
    have hNs_ge : 4 / δ + 1 ≤ (N : ℝ) * s := by
      have h1 : (4 / δ + 1) / s ≤ (⌈(4 / δ + 1) / s⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : 4 / δ + 1 ≤ (⌈(4 / δ + 1) / s⌉₊ : ℝ) * s := (div_le_iff₀ hspos).mp h1
      rw [hNcast]
      linarith [h2, hspos.le]
    have hNs_lt : (N : ℝ) * s < 4 / δ + 3 := by
      have h1 : (⌈(4 / δ + 1) / s⌉₊ : ℝ) < (4 / δ + 1) / s + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      rw [hNcast]
      have h2 : ((⌈(4 / δ + 1) / s⌉₊ : ℝ) + 1) * s < ((4 / δ + 1) / s + 2) * s := by
        apply mul_lt_mul_of_pos_right _ hspos
        linarith
      have h3 : ((4 / δ + 1) / s + 2) * s = (4 / δ + 1) + 2 * s := by
        field_simp
      rw [h3] at h2
      nlinarith [h2, hsle1]
    have hregionρ : R + (N : ℝ) * s + s < ρ := by
      rw [hρdef]; linarith [hNs_lt, hsle1]
    have hNe : 1 ≤ (N : ℝ) * e := by
      have h1 : (N : ℝ) * e = (N : ℝ) * s * (δ / 4) := by rw [hedef]; ring
      rw [h1]
      have h2 : (4 / δ + 1) * (δ / 4) ≤ (N : ℝ) * s * (δ / 4) :=
        mul_le_mul_of_nonneg_right hNs_ge (by positivity)
      have h3 : (4 / δ + 1) * (δ / 4) = 1 + δ / 4 := by
        field_simp
      rw [h3] at h2
      linarith [h2, hδ]
    set ψ : ℝ → ℝ := fun t => Real.smoothTransition ((t - c') / ((c + c') / 2 - c')) with hψdef
    have hβden : 0 < (c + c') / 2 - c' := by linarith
    have hψ0 : ∀ t, t ≤ c' → ψ t = 0 := by
      intro t ht
      rw [hψdef]
      exact Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
    have hψ1 : ∀ t, (c + c') / 2 ≤ t → ψ t = 1 := by
      intro t ht
      rw [hψdef]
      exact Real.smoothTransition.one_of_one_le (by rw [one_le_div hβden]; linarith)
    have hψnn : ∀ t, 0 ≤ ψ t := fun t => by
      rw [hψdef]; exact Real.smoothTransition.nonneg _
    have hψle1 : ∀ t, ψ t ≤ 1 := fun t => by
      rw [hψdef]; exact Real.smoothTransition.le_one _
    have hψcont : Continuous ψ := by rw [hψdef]; fun_prop
    set Tmap : Dom k l → Dom k l := fun w => w + (ψ (F w) * s) • u w with hTdef
    have hTmap : ∀ w, Tmap w = w + (ψ (F w) * s) • u w := fun w => by rw [hTdef]
    have hTcont : Continuous Tmap := by
      rw [hTdef]
      exact continuous_id.add (((hψcont.comp hF.continuous).mul continuous_const).smul hucont)
    set η : Dom k l → Dom k l := Tmap^[N] with hηdef
    have hηcont : Continuous η := by rw [hηdef]; exact hTcont.iterate N
    have hmove : ∀ w : Dom k l, ‖Tmap w‖ ≤ ‖w‖ + s := by
      intro w
      have hsub : Tmap w - w = (ψ (F w) * s) • u w := by rw [hTmap w]; abel
      have hnn : 0 ≤ ψ (F w) * s := mul_nonneg (hψnn _) hspos.le
      calc ‖Tmap w‖ = ‖w + (Tmap w - w)‖ := by rw [add_sub_cancel]
        _ ≤ ‖w‖ + ‖Tmap w - w‖ := norm_add_le _ _
        _ = ‖w‖ + ‖(ψ (F w) * s) • u w‖ := by rw [hsub]
        _ ≤ ‖w‖ + ψ (F w) * s := by
            gcongr
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnn]
            exact mul_le_of_le_one_right hnn (hu1 w)
        _ ≤ ‖w‖ + s := by
            gcongr
            exact mul_le_of_le_one_left hspos.le (hψle1 _)
    have hregion : ∀ z : Dom k l, ‖z‖ ≤ R → ∀ m : ℕ, ‖(Tmap^[m]) z‖ ≤ R + (m : ℝ) * s := by
      intro z hz m
      induction m with
      | zero => simpa using hz
      | succ m ih =>
          rw [Function.iterate_succ_apply']
          calc ‖Tmap ((Tmap^[m]) z)‖ ≤ ‖(Tmap^[m]) z‖ + s := hmove _
            _ ≤ (R + (m : ℝ) * s) + s := by linarith
            _ = R + ((m + 1 : ℕ) : ℝ) * s := by push_cast; ring
    have hstep : ∀ w : Dom k l, ‖w‖ ≤ ρ → ‖Tmap w‖ ≤ ρ →
        F (Tmap w) ≤ F w - ψ (F w) * e := by
      intro w hw hTw
      set hvec : Dom k l := (ψ (F w) * s) • u w with hvecdef
      have hTw' : ‖w + hvec‖ ≤ ρ := by rw [← hTmap w]; exact hTw
      have hMstep := hMbound w hvec hw hTw'
      have hnn : 0 ≤ ψ (F w) * s := mul_nonneg (hψnn _) hspos.le
      have hdf : (fderiv ℝ F w) hvec ≤ -ψ (F w) * s * δ / 2 := by
        have hudw := hud w
        rw [hvecdef, map_smul, smul_eq_mul]
        calc (ψ (F w) * s) * (fderiv ℝ F w) (u w) ≤ (ψ (F w) * s) * (-δ / 2) :=
              mul_le_mul_of_nonneg_left hudw hnn
          _ = -ψ (F w) * s * δ / 2 := by ring
      have hnorm : ‖hvec‖ ^ 2 ≤ ψ (F w) * s ^ 2 := by
        have h1 : ‖hvec‖ ≤ ψ (F w) * s := by
          rw [hvecdef, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnn]
          exact mul_le_of_le_one_right hnn (hu1 w)
        have h4 : (ψ (F w) * s) ^ 2 ≤ ψ (F w) * s ^ 2 := by
          have h5 : (ψ (F w) * s) ^ 2 = (ψ (F w) * s ^ 2) * ψ (F w) := by ring
          rw [h5]
          simpa using mul_le_mul_of_nonneg_left (hψle1 _)
            (mul_nonneg (hψnn _) (by positivity : (0 : ℝ) ≤ s ^ 2))
        calc ‖hvec‖ ^ 2 ≤ (ψ (F w) * s) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
          _ ≤ ψ (F w) * s ^ 2 := h4
      rw [hTmap w]
      have h1 : F (w + hvec) ≤ F w + (-ψ (F w) * s * δ / 2) + M / 2 * (ψ (F w) * s ^ 2) := by
        have e2 : M / 2 * ‖hvec‖ ^ 2 ≤ M / 2 * (ψ (F w) * s ^ 2) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
        linarith [hMstep, hdf, e2]
      have h2 : M / 2 * (ψ (F w) * s ^ 2) ≤ ψ (F w) * s * δ / 4 := by
        have hbase : ψ (F w) * s * (M * s) ≤ ψ (F w) * s * (δ / 2) :=
          mul_le_mul_of_nonneg_left hMs hnn
        nlinarith [hbase]
      have h3 : F w + (-ψ (F w) * s * δ / 2) + M / 2 * (ψ (F w) * s ^ 2) ≤ F w - ψ (F w) * e := by
        rw [hedef]
        nlinarith [h2]
      linarith [h1, h3]
    have hFstep : ∀ w : Dom k l, ‖w‖ ≤ R + (N : ℝ) * s → F (Tmap w) ≤ F w - ψ (F w) * e := by
      intro w hw
      have hwρ : ‖w‖ ≤ ρ := by linarith [hw, hregionρ]
      have hTwρ : ‖Tmap w‖ ≤ ρ := by linarith [hmove w, hw, hregionρ]
      exact hstep w hwρ hTwρ
    have hbound : ∀ z : Dom k l, ‖z‖ ≤ R → ∀ m : ℕ, m ≤ N →
        F ((Tmap^[m]) z) ≤ max (F z - (m : ℝ) * e) ((c + c') / 2) := by
      intro z hz m
      induction m with
      | zero => intro _; simp
      | succ m ih =>
          intro hm
          rw [Function.iterate_succ_apply']
          have hmN : m ≤ N := Nat.le_of_succ_le hm
          have ih' := ih hmN
          have hw : ‖(Tmap^[m]) z‖ ≤ R + (N : ℝ) * s := by
            have h1 := hregion z hz m
            have h2 : (m : ℝ) * s ≤ (N : ℝ) * s :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hmN) hspos.le
            linarith
          have hs := hFstep ((Tmap^[m]) z) hw
          rcases le_or_gt (F ((Tmap^[m]) z)) ((c + c') / 2) with hle | hgt
          · have hdec : F (Tmap ((Tmap^[m]) z)) ≤ F ((Tmap^[m]) z) := by
              have h2 : 0 ≤ ψ (F ((Tmap^[m]) z)) * e := mul_nonneg (hψnn _) hepos.le
              linarith
            calc F (Tmap ((Tmap^[m]) z)) ≤ F ((Tmap^[m]) z) := hdec
              _ ≤ (c + c') / 2 := hle
              _ ≤ max (F z - ((m + 1 : ℕ) : ℝ) * e) ((c + c') / 2) := le_max_right _ _
          · have hψw : ψ (F ((Tmap^[m]) z)) = 1 := hψ1 _ hgt.le
            have hdec : F (Tmap ((Tmap^[m]) z)) ≤ F ((Tmap^[m]) z) - e := by
              simpa [hψw] using hs
            have hb : (c + c') / 2 < max (F z - (m : ℝ) * e) ((c + c') / 2) :=
              lt_of_lt_of_le hgt ih'
            have hmax : max (F z - (m : ℝ) * e) ((c + c') / 2) = F z - (m : ℝ) * e := by
              rcases max_cases (F z - (m : ℝ) * e) ((c + c') / 2) with ⟨he, _⟩ | ⟨he, _⟩
              · exact he
              · rw [he] at hb; exact absurd hb (lt_irrefl _)
            calc F (Tmap ((Tmap^[m]) z)) ≤ F ((Tmap^[m]) z) - e := hdec
              _ ≤ (F z - (m : ℝ) * e) - e := by rw [hmax] at ih'; linarith
              _ = F z - ((m + 1 : ℕ) : ℝ) * e := by push_cast; ring
              _ ≤ max (F z - ((m + 1 : ℕ) : ℝ) * e) ((c + c') / 2) := le_max_left _ _
    refine ⟨η, hηcont, ?_, ?_⟩
    · intro z hz
      have hzF : F z ≤ c' := hU z hz
      have hfix : ∀ m : ℕ, (Tmap^[m]) z = z := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
            rw [Function.iterate_succ_apply', ih, hTmap z, hψ0 (F z) hzF,
              zero_mul, zero_smul, add_zero]
      rw [hηdef]
      exact hfix N
    · intro z hzR _
      have hb := hbound z hzR N le_rfl
      rw [hηdef]
      refine le_trans hb ?_
      exact max_le (le_trans (sub_le_sub_left hNe (F z)) (le_max_left _ _)) (le_max_right _ _)

end

end Work.RPCore.Saddle
