import Mathlib
import Submission.Work.Mostow.bieberbachDefs
import Submission.Work.Mostow.bieberbachAssemblyMain

/-!
# Bieberbach's first theorem

The key lemma (Buser's commutator argument) and the final assembly.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

set_option maxHeartbeats 4000000

noncomputable section

variable {m : ℕ} {G : Type*} [Group G]

/-- **Bieberbach's key lemma (Buser's form).**  An element of a cocompact, properly
discontinuous group of isometries of Euclidean space whose rotation part is within `1/2` of the
identity is a pure translation. -/
theorem keyLemma (ρ : G →* (E m ≃ᵢ E m))
    (hpd : ∀ K : Set (E m), IsCompact K → {g : G | ((ρ g) '' K ∩ K).Nonempty}.Finite)
    (hcoc : ∃ K : Set (E m), IsCompact K ∧ ∀ x : E m, ∃ g : G, ρ g x ∈ K)
    (hmini : ∀ (u : E m), ‖u‖ = 1 → ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∃ g : G, ∃ t : ℝ, 1 ≤ t ∧ mOf (linPart ρ g) ≤ ε ∧ ‖trPart ρ g + t • u‖ ≤ δ * t)
    (g : G) (hg : mOf (linPart ρ g) < 1/2) : linPart ρ g = 1 := by
  by_contra hne
  obtain ⟨α, hαF0, hαmin⟩ : ∃ k : G, (0 < mOf (linPart ρ k) ∧ mOf (linPart ρ k) < 1/2) ∧
      ∀ j : G, (0 < mOf (linPart ρ j) ∧ mOf (linPart ρ j) < 1/2) →
        ‖trPart ρ k‖ ≤ ‖trPart ρ j‖ := by
    have hgpos : 0 < mOf (linPart ρ g) := by
      rcases lt_or_eq_of_le (mOf_nonneg (linPart ρ g)) with h | h
      · exact h
      · exact absurd ((mOf_eq_zero_iff).mp h.symm) hne
    obtain ⟨α, hα, hαmin⟩ := exists_argmin ρ hpd
      {k : G | 0 < mOf (linPart ρ k) ∧ mOf (linPart ρ k) < 1/2} g ⟨hgpos, hg⟩
    exact ⟨α, hα, hαmin⟩
  have hαlt : mOf (linPart ρ α) < 1/2 := hαF0.2
  have hαpos : 0 < mOf (linPart ρ α) := hαF0.1
  have hαne : linPart ρ α ≠ 1 := fun h => by
    have h0 : mOf (linPart ρ α) = 0 := (mOf_eq_zero_iff).mpr h
    rw [h0] at hαpos
    exact (lt_irrefl (0:ℝ)) hαpos
  obtain ⟨c, hcpos, hc⟩ := bndFixPerp (linPart ρ α) hαne
  set Es : Submodule ℝ (E m) := fixSub (linPart ρ α) with hEsdef
  have hfix : ∀ x ∈ Es, linPart ρ α x = x := by
    intro x hx; rw [hEsdef] at hx; exact (mem_fixSub).mp hx
  have hfixPerp : ∀ x ∈ Esᗮ, linPart ρ α x ∈ Esᗮ := by
    intro x hx
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro y hy
    have hy' : (linPart ρ α)⁻¹ y = y := by
      have h1 : (linPart ρ α)⁻¹ ((linPart ρ α) y) = (linPart ρ α)⁻¹ y := by
        rw [hfix y hy]
      simpa using h1.symm
    have hinner : inner ℝ y ((linPart ρ α) x) = inner ℝ y x := by
      have h3 : (linPart ρ α) ((linPart ρ α)⁻¹ y) = y := by simp
      have h2 := LinearIsometryEquiv.inner_map_map (linPart ρ α) ((linPart ρ α)⁻¹ y) x
      rw [h3] at h2
      rw [h2, hy']
    rw [hinner]
    exact hx y hy
  obtain ⟨y, hy⟩ : ∃ y : E m, linPart ρ α y ≠ y := by
    by_contra hcon
    push_neg at hcon
    exact hαne (LinearIsometryEquiv.ext hcon)
  have hyq : y - Es.starProjection y ≠ 0 := by
    intro h0
    have hyE : y ∈ Es := by
      have h1 : y = Es.starProjection y := sub_eq_zero.mp h0
      rw [h1]; exact Submodule.starProjection_apply_mem Es y
    exact hy (hfix y hyE)
  set u : E m := (‖y - Es.starProjection y‖)⁻¹ • (y - Es.starProjection y) with hudef
  have huE : u ∈ Esᗮ := Submodule.smul_mem _ _ (Submodule.sub_starProjection_mem_orthogonal y)
  have hu1 : ‖u‖ = 1 := by
    have hnorm : ‖y - Es.starProjection y‖ ≠ 0 := norm_ne_zero_iff.mpr hyq
    rw [hudef, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ hnorm]
  set eps : ℝ := min (c/1000) (1/1000) with hepsdef
  have hepspos : 0 < eps := lt_min (by linarith) (by norm_num)
  have hepsc : eps ≤ c/1000 := min_le_left _ _
  have heps8 : eps ≤ 1/1000 := min_le_right _ _
  obtain ⟨β, t, ht1, hβm, hβdir⟩ := hmini u hu1 eps (1/4) hepspos (by norm_num)
  set b : E m := trPart ρ β with hbdef
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hu_t : ‖t • u‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt htpos), hu1, mul_one]
  have hb_lb : (3/4) * t ≤ ‖b‖ := by
    have habs : ‖t • u‖ - ‖b + t • u‖ ≤ ‖b‖ := by
      have h := abs_norm_sub_norm_le (t • u) (b + t • u)
      have h2 : (t • u) - (b + t • u) = -b := by abel
      rw [h2, norm_neg] at h
      exact (le_abs_self _).trans h
    calc (3/4) * t = t - (1/4) * t := by ring
      _ ≤ ‖t • u‖ - ‖b + t • u‖ := by rw [hu_t]; linarith [hβdir]
      _ ≤ ‖b‖ := habs
  have hb_ne : b ≠ 0 := by
    intro h0
    have h1 : ‖b‖ = 0 := by rw [h0, norm_zero]
    nlinarith [hb_lb, htpos]
  have hproj_tu : Es.starProjection (t • u) = 0 := by
    rw [map_smul, starProjection_eq_zero_of_mem_orthogonal Es huE, smul_zero]
  have hβproj : ‖Es.starProjection b‖ < ‖b - Es.starProjection b‖ := by
    have h1 : ‖Es.starProjection b‖ ≤ (1/4) * t := by
      have hb' : b = -(t • u) + (b + t • u) := by abel
      have hcalc : ‖Es.starProjection b‖ = ‖Es.starProjection (b + t • u)‖ := by
        conv_lhs => rw [hb']
        rw [map_add, map_neg, hproj_tu, neg_zero, zero_add]
      rw [hcalc]
      exact le_trans (Submodule.norm_starProjection_apply_le Es _) hβdir
    have h2 : t - (1/4) * t ≤ ‖b - Es.starProjection b‖ := by
      have hb'' : Es.starProjection b - b
          = (t • u) - ((b + t • u) - Es.starProjection (b + t • u)) := by
        conv_rhs => rw [map_add, hproj_tu, add_zero]
        abel
      have h3 : ‖(b + t • u) - Es.starProjection (b + t • u)‖ ≤ ‖b + t • u‖ :=
        norm_sub_starProjection_le Es _
      have h4 := abs_norm_sub_norm_le (t • u) ((b + t • u) - Es.starProjection (b + t • u))
      have h5 : ‖t • u‖ - ‖(b + t • u) - Es.starProjection (b + t • u)‖
          ≤ ‖(t • u) - ((b + t • u) - Es.starProjection (b + t • u))‖ :=
        (le_abs_self _).trans h4
      rw [hu_t] at h5
      rw [show b - Es.starProjection b = -(Es.starProjection b - b) from by abel, norm_neg,
        hb'']
      linarith
    have h3 : (1/4) * t < t - (1/4) * t := by linarith
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le h3 h2)
  obtain ⟨β₀, hβ₀F, hβ₀min⟩ : ∃ k : G, (trPart ρ k ≠ 0 ∧ mOf (linPart ρ k) ≤ eps ∧
        ‖Es.starProjection (trPart ρ k)‖ < ‖trPart ρ k - Es.starProjection (trPart ρ k)‖) ∧
      ∀ j : G, (trPart ρ j ≠ 0 ∧ mOf (linPart ρ j) ≤ eps ∧
        ‖Es.starProjection (trPart ρ j)‖ < ‖trPart ρ j - Es.starProjection (trPart ρ j)‖) →
        ‖trPart ρ k‖ ≤ ‖trPart ρ j‖ :=
    exists_argmin ρ hpd _ β ⟨hb_ne, hβm, hβproj⟩
  set A : E m ≃ₗᵢ[ℝ] E m := linPart ρ α with hAdef
  set B : E m ≃ₗᵢ[ℝ] E m := linPart ρ β₀ with hBdef
  set a : E m := trPart ρ α with hadef
  set b₀ : E m := trPart ρ β₀ with hb₀def
  set R : E m ≃ₗᵢ[ℝ] E m := A * B * A⁻¹ * B⁻¹ with hRdef
  set γ : G := α * β₀ * α⁻¹ * β₀⁻¹ with hγdef
  have hγlin : linPart ρ γ = R := by
    rw [hγdef, hRdef, hAdef, hBdef, linPart_mul, linPart_mul, linPart_mul, linPart_inv,
      linPart_inv]
  have hγtr : trPart ρ γ = (A b₀ - R b₀) + (a - A (B (A⁻¹ a))) := by
    rw [hγdef, trPart_commutator, hAdef, hBdef, hRdef, hadef, hb₀def]
    simp only [LinearIsometryEquiv.mul_def, LinearIsometryEquiv.trans_apply]
    abel
  have hmB : mOf B ≤ eps := by rw [hBdef]; exact hβ₀F.2.1
  have hb₀ne : b₀ ≠ 0 := by rw [hb₀def]; exact hβ₀F.1
  have hb₀dir : ‖Es.starProjection b₀‖ < ‖b₀ - Es.starProjection b₀‖ := by
    rw [hb₀def]; exact hβ₀F.2.2
  have hR_le_B : mOf R ≤ mOf B := by
    have h := mOf_commutator A B
    have h1 : 2 * mOf A * mOf B ≤ mOf B := by nlinarith [mOf_nonneg B, hαlt]
    rw [hRdef]
    exact le_trans h h1
  have hR_le : mOf R ≤ eps := le_trans hR_le_B hmB
  set r : E m := (b₀ - R b₀) + (a - A (B (A⁻¹ a))) with hrdef
  have hr_le : ‖r‖ ≤ 2 * mOf B * ‖b₀‖ := by
    by_cases hB0 : mOf B = 0
    · have hB1 : B = 1 := (mOf_eq_zero_iff).mp hB0
      have hR1 : R = 1 := by rw [hRdef, hB1]; group
      have hr0 : r = 0 := by rw [hrdef, hR1, hB1]; simp
      rw [hr0, norm_zero, hB0]
      simp
    · have hBpos : 0 < mOf B := lt_of_le_of_ne (mOf_nonneg B) (Ne.symm hB0)
      have hBlt : mOf B < 1/2 := lt_of_le_of_lt hmB (lt_of_le_of_lt heps8 (by norm_num))
      have hβ₀F0 : (0 < mOf (linPart ρ β₀) ∧ mOf (linPart ρ β₀) < 1/2) := by
        rw [← hBdef]; exact ⟨hBpos, hBlt⟩
      have hb₀_ge : ‖a‖ ≤ ‖b₀‖ := by
        have h1 := hαmin β₀ hβ₀F0
        simpa only [← hadef, ← hb₀def] using h1
      have hbnd1 : ‖b₀ - R b₀‖ ≤ mOf R * ‖b₀‖ := by
        have heq : b₀ - R b₀ = -((opOf R - 1) b₀) := by
          rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, opOf_apply]; abel
        rw [heq, norm_neg]
        exact le_trans (ContinuousLinearMap.le_opNorm _ _) (le_of_eq rfl)
      have hbnd2 : ‖a - A (B (A⁻¹ a))‖ ≤ mOf B * ‖a‖ := by
        have heq : a - A (B (A⁻¹ a)) = -((opOf (A * B * A⁻¹) - 1) a) := by
          rw [opOf_mul, opOf_mul]
          simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, opOf_apply,
            LinearIsometryEquiv.mul_def, LinearIsometryEquiv.trans_apply]
          abel
        rw [heq, norm_neg]
        calc ‖(opOf (A * B * A⁻¹) - 1) a‖ ≤ ‖opOf (A * B * A⁻¹) - 1‖ * ‖a‖ :=
              (opOf (A * B * A⁻¹) - 1).le_opNorm a
          _ ≤ mOf B * ‖a‖ := by gcongr; exact norm_opOf_conj_le A B
      calc ‖r‖ = ‖(b₀ - R b₀) + (a - A (B (A⁻¹ a)))‖ := by rw [hrdef]
        _ ≤ ‖b₀ - R b₀‖ + ‖a - A (B (A⁻¹ a))‖ := norm_add_le _ _
        _ ≤ mOf R * ‖b₀‖ + mOf B * ‖a‖ := add_le_add hbnd1 hbnd2
        _ ≤ mOf B * ‖b₀‖ + mOf B * ‖b₀‖ := by
            have h1 : mOf R * ‖b₀‖ ≤ mOf B * ‖b₀‖ :=
              mul_le_mul_of_nonneg_right hR_le_B (norm_nonneg _)
            have h2 : mOf B * ‖a‖ ≤ mOf B * ‖b₀‖ :=
              mul_le_mul_of_nonneg_left hb₀_ge (mOf_nonneg B)
            linarith
        _ = 2 * mOf B * ‖b₀‖ := by ring
  have hq : b₀ - Es.starProjection b₀ ∈ Esᗮ := Submodule.sub_starProjection_mem_orthogonal b₀
  have hp : Es.starProjection b₀ ∈ Es := Submodule.starProjection_apply_mem Es b₀
  have hAq : A (b₀ - Es.starProjection b₀) ∈ Esᗮ := by rw [hAdef]; exact hfixPerp _ hq
  have hAb₀ : A b₀ - b₀ = A (b₀ - Es.starProjection b₀) - (b₀ - Es.starProjection b₀) := by
    have hdec : b₀ = Es.starProjection b₀ + (b₀ - Es.starProjection b₀) := by abel
    rw [hdec, map_add, hfix _ hp]; abel
  have hw : trPart ρ γ = (A b₀ - b₀) + r := by rw [hγtr, hrdef]; abel
  have hprojAq : Es.starProjection
      (A (b₀ - Es.starProjection b₀) - (b₀ - Es.starProjection b₀)) = 0 :=
    starProjection_eq_zero_of_mem_orthogonal Es (Submodule.sub_mem _ hAq hq)
  have hprojw : Es.starProjection (trPart ρ γ) = Es.starProjection r := by
    rw [hw, hAb₀, map_add, hprojAq, zero_add]
  have hwsub : trPart ρ γ - Es.starProjection (trPart ρ γ)
      = (A (b₀ - Es.starProjection b₀) - (b₀ - Es.starProjection b₀))
        + (r - Es.starProjection r) := by
    rw [hprojw, hw, hAb₀]; abel
  have hb₀pos : 0 < ‖b₀‖ := norm_pos_iff.mpr hb₀ne
  have hr_small : ‖r‖ ≤ (c/500) * ‖b₀‖ := by
    have h1 : 2 * mOf B ≤ c/500 := by
      have h2 : 2 * eps ≤ c/500 := by linarith [hepsc]
      have := mOf_nonneg B
      linarith
    nlinarith [hr_le, h1, hb₀pos.le]
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2 : (7/5:ℝ) ≤ Real.sqrt 2 := by nlinarith [hs, Real.sqrt_nonneg 2]
  have hsub_ge : c * ‖b₀‖ / 2 ≤ ‖trPart ρ γ - Es.starProjection (trPart ρ γ)‖ := by
    have hA : c * ‖b₀ - Es.starProjection b₀‖
        ≤ ‖A (b₀ - Es.starProjection b₀) - (b₀ - Es.starProjection b₀)‖ := by
      have h1 := hc (b₀ - Es.starProjection b₀) hq
      simpa only [← hAdef] using h1
    have h2 : ‖r - Es.starProjection r‖ ≤ ‖r‖ := norm_sub_starProjection_le Es r
    have h4 : ‖b₀‖ ≤ Real.sqrt 2 * ‖b₀ - Es.starProjection b₀‖ :=
      norm_le_sqrt_two_mul_sub_starProjection Es b₀ hb₀dir
    have hq4 : Real.sqrt 2 / 2 * ‖b₀‖ ≤ ‖b₀ - Es.starProjection b₀‖ := by
      nlinarith [h4, hs, Real.sqrt_nonneg 2]
    have h5 : Real.sqrt 2 / 2 * c * ‖b₀‖
        ≤ ‖A (b₀ - Es.starProjection b₀) - (b₀ - Es.starProjection b₀)‖ := by
      nlinarith [hA, hq4, hcpos]
    have hrt : ‖A (b₀ - Es.starProjection b₀) - (b₀ - Es.starProjection b₀)‖
        - ‖r - Es.starProjection r‖
        ≤ ‖(A (b₀ - Es.starProjection b₀) - (b₀ - Es.starProjection b₀))
          + (r - Es.starProjection r)‖ := by
      have habs := abs_norm_sub_norm_le
        (A (b₀ - Es.starProjection b₀) - (b₀ - Es.starProjection b₀))
        (-(r - Es.starProjection r))
      have he : (A (b₀ - Es.starProjection b₀) - (b₀ - Es.starProjection b₀))
          - (-(r - Es.starProjection r))
          = (A (b₀ - Es.starProjection b₀) - (b₀ - Es.starProjection b₀))
            + (r - Es.starProjection r) := by abel
      rw [he, norm_neg] at habs
      exact (le_abs_self _).trans habs
    have h6 : (c/2) * ‖b₀‖ ≤ (Real.sqrt 2 / 2 - 1/500 : ℝ) * c * ‖b₀‖ := by
      have h6' : (1:ℝ)/2 ≤ Real.sqrt 2 / 2 - 1/500 := by linarith [hs2]
      have h0 : (0:ℝ) ≤ c * ‖b₀‖ := by positivity
      calc (c/2) * ‖b₀‖ = (1/2 : ℝ) * (c * ‖b₀‖) := by ring
        _ ≤ (Real.sqrt 2 / 2 - 1/500) * (c * ‖b₀‖) := mul_le_mul_of_nonneg_right h6' h0
        _ = (Real.sqrt 2 / 2 - 1/500 : ℝ) * c * ‖b₀‖ := by ring
    rw [hwsub]
    nlinarith [hrt, h5, h2, hr_small, h6]
  have hproj_le : ‖Es.starProjection (trPart ρ γ)‖ ≤ (c/500) * ‖b₀‖ := by
    rw [hprojw]
    calc ‖Es.starProjection r‖ ≤ ‖r‖ := Submodule.norm_starProjection_apply_le Es r
      _ ≤ (c/500) * ‖b₀‖ := hr_small
  have hdirw : ‖Es.starProjection (trPart ρ γ)‖ < ‖trPart ρ γ - Es.starProjection (trPart ρ γ)‖ := by
    have h1 : (c/500) * ‖b₀‖ < c * ‖b₀‖ / 2 := by nlinarith [hb₀pos, hcpos]
    linarith [hproj_le, hsub_ge]
  have hw_ne : trPart ρ γ ≠ 0 := by
    intro h0
    have h1 : ‖trPart ρ γ - Es.starProjection (trPart ρ γ)‖ = 0 := by
      rw [h0, map_zero, sub_zero, norm_zero]
    have h2 : (0:ℝ) < c * ‖b₀‖ / 2 := by positivity
    linarith [hsub_ge, h1, h2]
  have hγF : (trPart ρ γ ≠ 0 ∧ mOf (linPart ρ γ) ≤ eps ∧
      ‖Es.starProjection (trPart ρ γ)‖ < ‖trPart ρ γ - Es.starProjection (trPart ρ γ)‖) :=
    ⟨hw_ne, by rw [hγlin]; exact hR_le, hdirw⟩
  have hw_lt : ‖trPart ρ γ‖ < ‖b₀‖ := by
    rw [hw]
    have h1 : ‖(A b₀ - b₀) + r‖ ≤ ‖A b₀ - b₀‖ + ‖r‖ := norm_add_le _ _
    have h2 : ‖A b₀ - b₀‖ ≤ mOf A * ‖b₀‖ := mOf_apply A b₀
    have h3 : ‖r‖ ≤ 2 * eps * ‖b₀‖ := by nlinarith [hr_le, hmB, hb₀pos.le]
    have h4 : mOf A + 2 * eps < 1 := by nlinarith [hαlt, heps8]
    have h5 : ‖A b₀ - b₀‖ + ‖r‖ ≤ (mOf A + 2 * eps) * ‖b₀‖ := by
      nlinarith [h2, h3, hb₀pos.le]
    nlinarith [h1, h5, h4, hb₀pos]
  have hfin := hβ₀min γ hγF
  have hfin' : ‖b₀‖ ≤ ‖trPart ρ γ‖ := by simpa only [hb₀def] using hfin
  linarith [hw_lt, hfin']

end

end Work.Mostow

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- **Bieberbach's first theorem**, in the form required by the project. -/
theorem bieberbach (m : ℕ) : BieberbachProp m := by
  intro G _ ρ hpd hcoc
  have hmini : ∀ (u : E m), ‖u‖ = 1 → ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∃ g : G, ∃ t : ℝ, 1 ≤ t ∧ mOf (linPart ρ g) ≤ ε ∧ ‖trPart ρ g + t • u‖ ≤ δ * t :=
    fun u hu ε δ hε hδ => miniLemma ρ hcoc u hu ε δ hε hδ
  have hkey : ∀ g : G, mOf (linPart ρ g) < 1/2 → linPart ρ g = 1 :=
    fun g hg => keyLemma ρ hpd hcoc hmini g hg
  have hfin : (Set.range (linPartHom ρ)).Finite := range_linPartHom_finite ρ hkey
  haveI : Finite (linPartHom ρ).range := Set.finite_coe_iff.mpr (by rwa [MonoidHom.coe_range])
  refine ⟨(linPartHom ρ).ker, trPart ρ, inferInstance, ?_, ?_⟩
  · intro t ht x
    rw [MonoidHom.mem_ker] at ht
    have ht' : linPart ρ t = 1 := ht
    rw [apply_eq, ht']; simp
  · exact span_trPart_ker_linPartHom ρ hmini hkey

end Work.Mostow
