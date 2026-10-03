import Mathlib
import Submission.Work.Motion.Basic
import Submission.Work.Motion.Coding
import Submission.Work.Motion.Holder
import Submission.Work.Motion.koebe_distortion
import Submission.Work.Motion.exists_sep
import Submission.Work.Motion.deriv_ratio_and_lips

namespace Work.Motion

open Metric Set Filter
open MandelDim
open LeanEval.Dynamics.MandelbrotBoundary

noncomputable section

section Helpers

variable {c₀ : ℂ} {N : ℕ} {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {r K : ℝ}

/-- Two points of the core piece `closedBall p D.s` are at distance at most `2 D.s`. -/
lemma coding_dist_le_two_s (D : PertData c₀ N τ n p r K) {c : ℂ} (hc : c ∈ ball c₀ D.ρ)
    (ω ω' : ℕ → Fin N) : ‖D.coding c ω - D.coding c ω'‖ ≤ 2 * D.s := by
  have hU : ‖D.coding c ω - p‖ ≤ D.s := by
    have h := D.coding_mem c hc ω
    rwa [mem_closedBall, dist_eq_norm] at h
  have hV : ‖D.coding c ω' - p‖ ≤ D.s := by
    have h := D.coding_mem c hc ω'
    rwa [mem_closedBall, dist_eq_norm] at h
  calc ‖D.coding c ω - D.coding c ω'‖
      = ‖(D.coding c ω - p) + (p - D.coding c ω')‖ := by congr 1; ring
    _ ≤ ‖D.coding c ω - p‖ + ‖p - D.coding c ω'‖ := norm_add_le _ _
    _ ≤ 2 * D.s := by
        have hrev : ‖p - D.coding c ω'‖ = ‖D.coding c ω' - p‖ := norm_sub_rev _ _
        linarith

/-- Koebe constants for the core disc `ball p (r/2)`: a sub-disc radius `σ` with
`D.s ≤ σ * (r/2)` and constants `cK, CK` such that every holomorphic injection of `ball p (r/2)`
distorts distance by at most the factor `CK / cK` between points of `closedBall p (σ * (r/2))`. -/
lemma koebe_two_sided (D : PertData c₀ N τ n p r K) :
    ∃ σ cK CK : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < cK ∧ 0 < CK ∧ D.s ≤ σ * (r / 2) ∧
      ∀ (f : ℂ → ℂ), DifferentiableOn ℂ f (ball p (r / 2)) → InjOn f (ball p (r / 2)) →
        ∀ u ∈ closedBall p (σ * (r / 2)), ∀ v ∈ closedBall p (σ * (r / 2)),
          cK * ‖deriv f p‖ * ‖u - v‖ ≤ ‖f u - f v‖ ∧
          ‖f u - f v‖ ≤ CK * ‖deriv f p‖ * ‖u - v‖ := by
  have hr : 0 < r := D.r_pos
  set σ : ℝ := (2 * D.s / r + 1) / 2 with hσdef
  have hσ0 : 0 < σ := by
    rw [hσdef]
    have h : 0 ≤ 2 * D.s / r := div_nonneg (by linarith [D.hs0]) hr.le
    linarith
  have hσ1 : σ < 1 := by
    rw [hσdef]
    have h : 2 * D.s / r < 1 := by
      rw [div_lt_one hr]
      linarith [D.hsr]
    linarith
  have hsσ : D.s ≤ σ * (r / 2) := by
    rw [hσdef]
    have h : (2 * D.s / r + 1) / 2 * (r / 2) = D.s / 2 + r / 4 := by
      field_simp
      ring
    rw [h]
    linarith [D.hsr]
  obtain ⟨cK, CK, hcK, hCK, -, H⟩ := koebe_distortion σ hσ0 hσ1
  exact ⟨σ, cK, CK, hσ0, hσ1, hcK, hCK, hsσ,
    fun f hd hi => (H f p (r / 2) (by linarith) hd hi).2⟩

/-- **Upper Koebe comparison for the coding map.** For codes agreeing on their first `k` letters,
the distance of the two coding points is bounded by a constant times the modulus of the derivative
at `p` of the common `k`-fold composite `pComp (τc c) ω k`. -/
lemma piece_koebe_upper (D : PertData c₀ N τ n p r K) :
    ∃ Cu : ℝ, 0 ≤ Cu ∧ ∀ c ∈ ball c₀ D.ρ, ∀ (k : ℕ) (ω ω' : ℕ → Fin N),
      (∀ j < k, ω j = ω' j) →
      ‖D.coding c ω - D.coding c ω'‖ ≤ Cu * ‖deriv (pComp (D.τc c) ω k) p‖ := by
  obtain ⟨σ, cK, CK, hσ0, hσ1, hcK, hCK, hsσ, H⟩ := koebe_two_sided D
  set Cu : ℝ := max (2 * D.s) (CK * (2 * D.s)) with hCudef
  have hCu0 : 0 ≤ Cu := by
    rw [hCudef]; exact le_max_iff.mpr (Or.inl (by linarith [D.hs0]))
  have hCu1 : 2 * D.s ≤ Cu := by rw [hCudef]; exact le_max_left _ _
  have hCu2 : CK * (2 * D.s) ≤ Cu := by rw [hCudef]; exact le_max_right _ _
  refine ⟨Cu, hCu0, ?_⟩
  intro c hc k ω ω' hagree
  set U := D.coding c (fun j => ω (j + k)) with hUdef
  set V := D.coding c (fun j => ω' (j + k)) with hVdef
  have hUU : D.coding c ω = pComp (D.τc c) ω k U := by
    rw [hUdef]
    exact D.coding_eq_pComp c hc ω k
  have hcong : pComp (D.τc c) ω' k = pComp (D.τc c) ω k :=
    pComp_congr k (fun j hj => (hagree j hj).symm)
  have hVV : D.coding c ω' = pComp (D.τc c) ω k V := by
    rw [hVdef, D.coding_eq_pComp c hc ω' k, hcong]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hd : ‖deriv (pComp (D.τc c) ω 0) p‖ = 1 := by rw [pComp_zero, deriv_id, norm_one]
    rw [hd, mul_one]
    exact le_trans (coding_dist_le_two_s D hc ω ω') hCu1
  · have hU1 : U ∈ closedBall p D.s := by rw [hUdef]; exact D.coding_mem c hc _
    have hV1 : V ∈ closedBall p D.s := by rw [hVdef]; exact D.coding_mem c hc _
    have hUV : ‖U - V‖ ≤ 2 * D.s := by
      rw [hUdef, hVdef]
      exact coding_dist_le_two_s D hc _ _
    have hr2 : (0 : ℝ) < r / 2 := by linarith [D.r_pos]
    have hdiff : DifferentiableOn ℂ (pComp (D.τc c) ω k) (ball p (r / 2)) :=
      D.pComp_diffOn c hc ω k
    have hinj : InjOn (pComp (D.τc c) ω k) (ball p (r / 2)) := D.pComp_injOn c hc ω k
    have hko := (H (pComp (D.τc c) ω k) hdiff hinj U
      (closedBall_subset_closedBall hsσ hU1) V (closedBall_subset_closedBall hsσ hV1)).2
    have hfin : ‖pComp (D.τc c) ω k U - pComp (D.τc c) ω k V‖
        ≤ Cu * ‖deriv (pComp (D.τc c) ω k) p‖ := by
      refine le_trans hko ?_
      have h1 : CK * ‖deriv (pComp (D.τc c) ω k) p‖ * ‖U - V‖
          ≤ CK * ‖deriv (pComp (D.τc c) ω k) p‖ * (2 * D.s) :=
        mul_le_mul_of_nonneg_left hUV (mul_nonneg hCK.le (norm_nonneg _))
      have h2 : CK * ‖deriv (pComp (D.τc c) ω k) p‖ * (2 * D.s)
          ≤ Cu * ‖deriv (pComp (D.τc c) ω k) p‖ := by
        have he : CK * ‖deriv (pComp (D.τc c) ω k) p‖ * (2 * D.s)
            = (CK * (2 * D.s)) * ‖deriv (pComp (D.τc c) ω k) p‖ := by ring
        rw [he]
        exact mul_le_mul_of_nonneg_right hCu2 (norm_nonneg _)
      linarith
    rw [hUU, hVV]
    exact hfin

/-- **Lower Koebe comparison for the coding map.** If the level-1 pieces of distinct letters are
separated by `g > 0` on `ball c₀ ρs`, then for codes whose first `k` letters agree and whose `k`-th
letters differ, the distance of the coding points is at least a constant times the modulus of the
derivative at `p` of the common `k`-fold composite. -/
lemma piece_koebe_lower (D : PertData c₀ N τ n p r K) {ρs g : ℝ} (hρs : 0 < ρs)
    (hρsD : ρs ≤ D.ρ) (hg : 0 < g)
    (hsep : ∀ (i j : Fin N), i ≠ j → ∀ c ∈ ball c₀ ρs,
      ∀ x ∈ closedBall p (r / 2), ∀ y ∈ closedBall p (r / 2),
        g ≤ ‖D.τc c i x - D.τc c j y‖) :
    ∃ cl : ℝ, 0 < cl ∧ ∀ c ∈ ball c₀ ρs, ∀ (k : ℕ) (ω ω' : ℕ → Fin N),
      (∀ j < k, ω j = ω' j) → ω k ≠ ω' k →
      cl * ‖deriv (pComp (D.τc c) ω k) p‖ ≤ ‖D.coding c ω - D.coding c ω'‖ := by
  obtain ⟨σ, cK, CK, hσ0, hσ1, hcK, hCK, hsσ, H⟩ := koebe_two_sided D
  refine ⟨cK * g, mul_pos hcK hg, ?_⟩
  intro c hc k ω ω' hagree hkdiff
  have hcD : c ∈ ball c₀ D.ρ := ball_subset_ball hρsD hc
  set U := D.coding c (fun j => ω (j + k)) with hUdef
  set V := D.coding c (fun j => ω' (j + k)) with hVdef
  have hUU : D.coding c ω = pComp (D.τc c) ω k U := by
    rw [hUdef]
    exact D.coding_eq_pComp c hcD ω k
  have hcong : pComp (D.τc c) ω' k = pComp (D.τc c) ω k :=
    pComp_congr k (fun j hj => (hagree j hj).symm)
  have hVV : D.coding c ω' = pComp (D.τc c) ω k V := by
    rw [hVdef, D.coding_eq_pComp c hcD ω' k, hcong]
  obtain ⟨x, hx, hxeq⟩ := D.coding_shift_mem c hcD ω k
  obtain ⟨y, hy, hyeq⟩ := D.coding_shift_mem c hcD ω' k
  have hUeq : U = D.τc c (ω k) x := by rw [hUdef]; exact hxeq
  have hVeq : V = D.τc c (ω' k) y := by rw [hVdef]; exact hyeq
  have hUV : g ≤ ‖U - V‖ := by
    have h := hsep (ω k) (ω' k) hkdiff c hc x hx y hy
    rwa [hUeq, hVeq]
  have hU1 : U ∈ closedBall p D.s := by rw [hUdef]; exact D.coding_mem c hcD _
  have hV1 : V ∈ closedBall p D.s := by rw [hVdef]; exact D.coding_mem c hcD _
  have hr2 : (0 : ℝ) < r / 2 := by linarith [D.r_pos]
  have hdiff : DifferentiableOn ℂ (pComp (D.τc c) ω k) (ball p (r / 2)) := D.pComp_diffOn c hcD ω k
  have hinj : InjOn (pComp (D.τc c) ω k) (ball p (r / 2)) := D.pComp_injOn c hcD ω k
  have hko := (H (pComp (D.τc c) ω k) hdiff hinj U
    (closedBall_subset_closedBall hsσ hU1) V (closedBall_subset_closedBall hsσ hV1)).1
  have hfin : (cK * g) * ‖deriv (pComp (D.τc c) ω k) p‖
      ≤ ‖pComp (D.τc c) ω k U - pComp (D.τc c) ω k V‖ := by
    refine le_trans ?_ hko
    have he : (cK * g) * ‖deriv (pComp (D.τc c) ω k) p‖
        = cK * ‖deriv (pComp (D.τc c) ω k) p‖ * g := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hUV (mul_nonneg hcK.le (norm_nonneg _))
  rw [hUU, hVV]
  exact hfin

/-- Scalar step: if `δ ≤ M θ^k` and `r ≤ γ log (1/θ)` with `0 < θ < 1`, `M ≥ 0`, `δ ≥ 0`,
`γ > 0`, then `exp (k r) δ^γ ≤ M^γ`. -/
lemma exp_rpow_le {θ δ r γ M : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hγ : 0 < γ) {k : ℕ} (hk : δ ≤ M * θ ^ k) (hr : r ≤ γ * Real.log (1 / θ)) :
    Real.exp ((k : ℝ) * r) * δ ^ γ ≤ M ^ γ := by
  have hθk : (0 : ℝ) ≤ θ ^ k := pow_nonneg hθ0.le k
  have h1 : δ ^ γ ≤ M ^ γ * Real.exp (-(((k : ℝ) * γ) * Real.log (1 / θ))) := by
    have h2 : δ ^ γ ≤ (M * θ ^ k) ^ γ := Real.rpow_le_rpow hδ hk hγ.le
    rw [Real.mul_rpow hM hθk] at h2
    refine h2.trans (le_of_eq ?_)
    congr 1
    rw [← Real.rpow_natCast θ k, ← Real.rpow_mul hθ0.le, Real.rpow_def_of_pos hθ0]
    rw [one_div, Real.log_inv]
    ring
  have hexp : Real.exp ((k : ℝ) * r) * Real.exp (-(((k : ℝ) * γ) * Real.log (1 / θ)))
      = Real.exp ((k : ℝ) * r - ((k : ℝ) * γ) * Real.log (1 / θ)) := by
    rw [← Real.exp_add]
    rfl
  have harg : (k : ℝ) * r - ((k : ℝ) * γ) * Real.log (1 / θ) ≤ 0 := by
    have h6 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h7 : r - γ * Real.log (1 / θ) ≤ 0 := by linarith
    have h8 : (k : ℝ) * (r - γ * Real.log (1 / θ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h6 h7
    nlinarith [h8]
  calc Real.exp ((k : ℝ) * r) * δ ^ γ
      ≤ Real.exp ((k : ℝ) * r) * (M ^ γ * Real.exp (-(((k : ℝ) * γ) * Real.log (1 / θ)))) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = M ^ γ * (Real.exp ((k : ℝ) * r) * Real.exp (-(((k : ℝ) * γ) * Real.log (1 / θ)))) := by
        ring
    _ = M ^ γ * Real.exp ((k : ℝ) * r - ((k : ℝ) * γ) * Real.log (1 / θ)) := by rw [hexp]
    _ ≤ M ^ γ * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr harg)
        (Real.rpow_nonneg hM γ)
    _ = M ^ γ := mul_one _

/-- Scalar step, combined form: `exp (k r) δ ≤ M^γ δ^a` whenever `a + γ = 1` and
`exp (k r) δ^γ ≤ M^γ`, together with `δ ≤ M θ^k` and the smallness of `r`. -/
lemma exp_mul_le_rpow_mul {θ M δ r a γ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hM : 0 ≤ M)
    (hδ : 0 ≤ δ) (hγ : 0 < γ) (ha : a + γ = 1) {k : ℕ} (hk : δ ≤ M * θ ^ k)
    (hr : r ≤ γ * Real.log (1 / θ)) :
    Real.exp ((k : ℝ) * r) * δ ≤ M ^ γ * δ ^ a := by
  rcases eq_or_lt_of_le hδ with h0 | hpos
  · rw [← h0, mul_zero]
    exact mul_nonneg (Real.rpow_nonneg hM γ) (Real.rpow_nonneg (le_refl 0) a)
  · have hkey := exp_rpow_le hθ0 hθ1 hM hδ hγ hk hr
    have hδeq : δ = δ ^ γ * δ ^ a := by
      rw [← Real.rpow_add hpos, show γ + a = 1 by linarith, Real.rpow_one]
    calc Real.exp ((k : ℝ) * r) * δ
        = Real.exp ((k : ℝ) * r) * (δ ^ γ * δ ^ a) :=
            congrArg (fun t => Real.exp ((k : ℝ) * r) * t) hδeq
      _ = (Real.exp ((k : ℝ) * r) * δ ^ γ) * δ ^ a := by ring
      _ ≤ M ^ γ * δ ^ a := mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg hδ a)

end Helpers

/-- **Hölder continuity of the coding map in the parameter**, exponent `a < 1`.  Route: for codes
`ω ≠ ω'` first differing at position `k`, put `Φ = pComp (τc c) ω k` and `U = π c (ω shifted by k)`,
`V = π c (ω' shifted by k)`; then `π c ω = Φ U`, `π c ω' = Φ V`, and `U, V` lie in the level-1 pieces
of the distinct letters `ω k ≠ ω' k`, so `‖U - V‖ ∈ [g, 2s]` (`exists_sep`).  Koebe
(`koebe_distortion` with `σ = 2s/r`, `R = r/2`, using `pComp_diffOn`/`pComp_injOn` from `Motion/Holder`)
gives `c‖Φ'p‖‖U-V‖ ≤ ‖ΦU-ΦV‖ ≤ C‖Φ'p‖‖U-V‖`, and `deriv_ratio_and_lips` gives
`‖Φ'(p)‖ ≤ exp(kL‖c-c'‖)‖Φ_{c'}'(p)‖`.  Hence `δ_c ≤ K e^{kL‖c-c'‖} δ_{c'}` with
`K = C·2s/(c·g)`; combine with the contraction `δ_{c'} ≤ (2s/θ')θ'^k`, `θ' = (1+θ)/2`, and shrink `ρ`
so that `2Lρ ≤ (1-a)log(1/θ')`, giving `δ_c ≤ K(2s/θ')^{1-a}δ_{c'}^a`. -/
theorem coding_holder {c₀ : ℂ} {N : ℕ} {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {r K : ℝ}
    (hN : 1 ≤ N) (hIFS : IsConformalIFS N τ p r K) (D : PertData c₀ N τ n p r K)
    (a : ℝ) (ha : a < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ D.ρ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ c ∈ ball c₀ ρ, ∀ c' ∈ ball c₀ ρ, ∀ ω ω' : ℕ → Fin N,
        ‖D.coding c ω - D.coding c ω'‖ ≤ C * ‖D.coding c' ω - D.coding c' ω'‖ ^ a := by
  classical
  obtain ⟨ρs, hρs_pos, hρs_le, g, hg, hsep⟩ := exists_sep hN hIFS D
  obtain ⟨Cu, hCu0, hCu⟩ := piece_koebe_upper D
  obtain ⟨cl, hcl0, hcl⟩ := piece_koebe_lower D hρs_pos hρs_le hg hsep
  obtain ⟨L, Λ, hL0, hΛ0, hlips, hratio⟩ := deriv_ratio_and_lips D
  set θ : ℝ := (1 + D.θ) / 2 with hθdef
  have hθpos : 0 < θ := by rw [hθdef]; linarith [D.hθ0]
  have hθlt1 : θ < 1 := by rw [hθdef]; linarith [D.hθ1]
  set M : ℝ := 2 * D.s / θ with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; exact div_nonneg (by linarith [D.hs0]) hθpos.le
  set γ : ℝ := 1 - a with hγdef
  have hγpos : 0 < γ := by rw [hγdef]; linarith
  have hlogpos : 0 < Real.log (1 / θ) := by
    rw [one_div]
    exact Real.log_pos (one_lt_inv_iff₀.mpr ⟨hθpos, hθlt1⟩)
  have hgl : 0 ≤ γ * Real.log (1 / θ) := mul_nonneg hγpos.le hlogpos.le
  set ρ : ℝ := min D.ρ (min ρs (γ * Real.log (1 / θ) / (2 * (L + 1)))) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact lt_min D.hρ (lt_min hρs_pos (div_pos (mul_pos hγpos hlogpos) (by linarith)))
  have hρD : ρ ≤ D.ρ := by rw [hρdef]; exact min_le_left _ _
  have hρρs : ρ ≤ ρs := by
    rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρf : ρ ≤ γ * Real.log (1 / θ) / (2 * (L + 1)) := by
    rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hsmall : 2 * L * ρ ≤ γ * Real.log (1 / θ) := by
    have hfac : 2 * L * (γ * Real.log (1 / θ) / (2 * (L + 1))) ≤ γ * Real.log (1 / θ) := by
      have hL1 : (0 : ℝ) < 2 * (L + 1) := by linarith
      have hfrac : 2 * L / (2 * (L + 1)) ≤ 1 := by
        rw [div_le_one hL1]
        linarith
      have hre : 2 * L * (γ * Real.log (1 / θ) / (2 * (L + 1)))
          = γ * Real.log (1 / θ) * (2 * L / (2 * (L + 1))) := by
        rw [← mul_div_assoc, mul_comm (2 * L), mul_div_assoc]
      rw [hre]
      exact mul_le_of_le_one_right hgl hfrac
    have hmono : 2 * L * ρ ≤ 2 * L * (γ * Real.log (1 / θ) / (2 * (L + 1))) :=
      mul_le_mul_of_nonneg_left hρf (by linarith : (0 : ℝ) ≤ 2 * L)
    linarith
  have hC0 : 0 ≤ Cu * M ^ γ / cl :=
    div_nonneg (mul_nonneg hCu0 (Real.rpow_nonneg hM0 γ)) hcl0.le
  refine ⟨ρ, hρpos, hρD, Cu * M ^ γ / cl, hC0, ?_⟩
  intro c hc c' hc' ω ω'
  by_cases hω : ω = ω'
  · subst hω
    simp only [sub_self, norm_zero]
    exact mul_nonneg hC0 (Real.rpow_nonneg (le_refl 0) a)
  · have hex : ∃ j, ω j ≠ ω' j := by
      by_contra h
      exact hω (funext (by simpa [not_exists] using h))
    set k := Nat.find hex with hkdef
    have hkdiff : ω k ≠ ω' k := Nat.find_spec hex
    have hkagree : ∀ j < k, ω j = ω' j := by
      intro j hj
      by_contra h
      exact Nat.find_min hex hj h
    have hcD : c ∈ ball c₀ D.ρ := ball_subset_ball hρD hc
    have hcD' : c' ∈ ball c₀ D.ρ := ball_subset_ball hρD hc'
    have hcs' : c' ∈ ball c₀ ρs := ball_subset_ball hρρs hc'
    have hup := hCu c hcD k ω ω' hkagree
    have hlow := hcl c' hcs' k ω ω' hkagree hkdiff
    have hrat := hratio k ω c hcD c' hcD'
    set δ := ‖D.coding c ω - D.coding c ω'‖ with hδdef
    set δ' := ‖D.coding c' ω - D.coding c' ω'‖ with hδ'def
    have hcontr : δ' ≤ M * θ ^ k := by
      rw [hδ'def, hMdef, hθdef]
      exact D.coding_contract c' hcD' hkagree
    have hr_le : L * ‖c - c'‖ ≤ γ * Real.log (1 / θ) := by
      have h2ρ : ‖c - c'‖ ≤ 2 * ρ := by
        have h1 : ‖c - c₀‖ < ρ := by simpa [mem_ball, dist_eq_norm] using hc
        have h2 : ‖c' - c₀‖ < ρ := by simpa [mem_ball, dist_eq_norm] using hc'
        calc ‖c - c'‖ = ‖(c - c₀) - (c' - c₀)‖ := by congr 1; ring
          _ ≤ ‖c - c₀‖ + ‖c' - c₀‖ := norm_sub_le _ _
          _ ≤ 2 * ρ := by linarith
      have h3 : L * ‖c - c'‖ ≤ L * (2 * ρ) := mul_le_mul_of_nonneg_left h2ρ hL0
      have h4 : L * (2 * ρ) = 2 * L * ρ := by ring
      linarith
    have hscal : Real.exp ((k : ℝ) * (L * ‖c - c'‖)) * δ' ≤ M ^ γ * δ' ^ a :=
      exp_mul_le_rpow_mul (θ := θ) (M := M) (δ := δ') (r := L * ‖c - c'‖) (a := a) (γ := γ)
        hθpos hθlt1 hM0 (norm_nonneg _) hγpos (by rw [hγdef]; ring) hcontr hr_le
    have hrat' : ‖deriv (pComp (D.τc c) ω k) p‖
        ≤ Real.exp ((k : ℝ) * (L * ‖c - c'‖)) * ‖deriv (pComp (D.τc c') ω k) p‖ := by
      have h := hrat
      rwa [show (k : ℝ) * L * ‖c - c'‖ = (k : ℝ) * (L * ‖c - c'‖) by ring] at h
    have hlow' : cl * ‖deriv (pComp (D.τc c') ω k) p‖ ≤ δ' := by
      rw [hδ'def]; exact hlow
    have hstep1 : cl * δ ≤ Cu * (cl * ‖deriv (pComp (D.τc c) ω k) p‖) := by
      calc cl * δ = cl * ‖D.coding c ω - D.coding c ω'‖ := by rw [hδdef]
        _ ≤ cl * (Cu * ‖deriv (pComp (D.τc c) ω k) p‖) :=
            mul_le_mul_of_nonneg_left hup hcl0.le
        _ = Cu * (cl * ‖deriv (pComp (D.τc c) ω k) p‖) := by ring
    have hstep2 : cl * ‖deriv (pComp (D.τc c) ω k) p‖
        ≤ Real.exp ((k : ℝ) * (L * ‖c - c'‖)) * δ' := by
      calc cl * ‖deriv (pComp (D.τc c) ω k) p‖
          ≤ cl * (Real.exp ((k : ℝ) * (L * ‖c - c'‖))
              * ‖deriv (pComp (D.τc c') ω k) p‖) :=
            mul_le_mul_of_nonneg_left hrat' hcl0.le
        _ = Real.exp ((k : ℝ) * (L * ‖c - c'‖))
              * (cl * ‖deriv (pComp (D.τc c') ω k) p‖) := by ring
        _ ≤ Real.exp ((k : ℝ) * (L * ‖c - c'‖)) * δ' :=
            mul_le_mul_of_nonneg_left hlow' (Real.exp_pos _).le
    have hmain : δ * cl ≤ Cu * M ^ γ * δ' ^ a := by
      calc δ * cl = cl * δ := by ring
        _ ≤ Cu * (cl * ‖deriv (pComp (D.τc c) ω k) p‖) := hstep1
        _ ≤ Cu * (Real.exp ((k : ℝ) * (L * ‖c - c'‖)) * δ') :=
            mul_le_mul_of_nonneg_left hstep2 hCu0
        _ ≤ Cu * (M ^ γ * δ' ^ a) := mul_le_mul_of_nonneg_left hscal hCu0
        _ = Cu * M ^ γ * δ' ^ a := by ring
    have hCe : Cu * M ^ γ / cl * δ' ^ a = Cu * M ^ γ * δ' ^ a / cl := by ring
    rw [hCe, le_div_iff₀ hcl0]
    exact hmain

end

end Work.Motion
