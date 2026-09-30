import Mathlib
import Submission.Work.RiemLib.Commons.Analysis.ODE.exists_global_solution_of_lipschitz
import Submission.Work.RiemLib.Commons.Analysis.ODE.dist_le_exp_mul_dist_of_hasDerivAt_of_norm_sub_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Commons.Analysis.ODE

open Set Metric Filter
open scoped Topology

/-! ### Radial retraction onto a closed ball

We need, for a vector field `f` that is `K`-Lipschitz only on a closed ball of radius `R` about
`z₀`, a *globally* Lipschitz field agreeing with `f` on that ball, so that the global existence
theorem for Lipschitz ODEs applies.  This is obtained by composing `f` with the radial retraction
of `E` onto the ball.  The radial retraction is Lipschitz with constant `2` on any normed space
(it is *not* an isometry in general normed spaces). -/

/-- Radial retraction of a normed space onto the closed ball of radius `R` about the origin. -/
noncomputable def radialRetract {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) (X : E) : E := if ‖X‖ ≤ R then X else (R / ‖X‖) • X

theorem norm_radialRetract_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 ≤ R) (X : E) : ‖radialRetract R X‖ ≤ R := by
  by_cases h : ‖X‖ ≤ R
  · rw [radialRetract, if_pos h]; exact h
  · rw [radialRetract, if_neg h, norm_smul, Real.norm_of_nonneg (div_nonneg hR (norm_nonneg X))]
    have hne : ‖X‖ ≠ 0 := ne_of_gt (lt_of_le_of_lt hR (lt_of_not_ge h))
    rw [div_mul_cancel₀ R hne]

theorem radialRetract_eq_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (X : E) (h : ‖X‖ ≤ R) : radialRetract R X = X := by
  rw [radialRetract, if_pos h]

theorem norm_radialRetract_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 ≤ R) (X Y : E) :
    ‖radialRetract R X - radialRetract R Y‖ ≤ 2 * ‖X - Y‖ := by
  by_cases hX : ‖X‖ ≤ R
  · by_cases hY : ‖Y‖ ≤ R
    · rw [radialRetract_eq_self X hX, radialRetract_eq_self Y hY]
      linarith [norm_nonneg (X - Y)]
    · rw [radialRetract_eq_self X hX, radialRetract, if_neg hY]
      have hYgt : R < ‖Y‖ := lt_of_not_ge hY
      have hYpos : 0 < ‖Y‖ := lt_of_le_of_lt hR hYgt
      have hcoef : 0 ≤ 1 - R / ‖Y‖ := by
        have : R / ‖Y‖ ≤ 1 := (div_le_one hYpos).mpr (le_of_lt hYgt)
        linarith
      have hdecomp : X - (R / ‖Y‖) • Y = (X - Y) + (1 - R / ‖Y‖) • Y := by
        rw [sub_smul, one_smul, sub_add_sub_cancel]
      calc ‖X - (R / ‖Y‖) • Y‖
          = ‖(X - Y) + (1 - R / ‖Y‖) • Y‖ := by rw [hdecomp]
        _ ≤ ‖X - Y‖ + ‖(1 - R / ‖Y‖) • Y‖ := norm_add_le _ _
        _ = ‖X - Y‖ + (1 - R / ‖Y‖) * ‖Y‖ := by
              rw [norm_smul, Real.norm_of_nonneg hcoef]
        _ = ‖X - Y‖ + (‖Y‖ - R) := by
              rw [sub_mul, one_mul, div_mul_cancel₀ R (ne_of_gt hYpos)]
        _ ≤ ‖X - Y‖ + ‖X - Y‖ := by
              have h1 : ‖Y‖ - R ≤ ‖Y‖ - ‖X‖ := by linarith
              have h2 : ‖Y‖ - ‖X‖ ≤ ‖X - Y‖ := by
                have := norm_sub_norm_le Y X
                rwa [norm_sub_rev Y X] at this
              linarith
        _ = 2 * ‖X - Y‖ := by ring
  · by_cases hY : ‖Y‖ ≤ R
    · rw [radialRetract_eq_self Y hY, radialRetract, if_neg hX]
      have hXgt : R < ‖X‖ := lt_of_not_ge hX
      have hXpos : 0 < ‖X‖ := lt_of_le_of_lt hR hXgt
      have hcoef : 0 ≤ 1 - R / ‖X‖ := by
        have : R / ‖X‖ ≤ 1 := (div_le_one hXpos).mpr (le_of_lt hXgt)
        linarith
      have hdecomp : (R / ‖X‖) • X - Y = (X - Y) - (1 - R / ‖X‖) • X := by
        rw [sub_smul, one_smul]
        abel
      calc ‖(R / ‖X‖) • X - Y‖
          = ‖(X - Y) - (1 - R / ‖X‖) • X‖ := by rw [hdecomp]
        _ ≤ ‖X - Y‖ + ‖(1 - R / ‖X‖) • X‖ := norm_sub_le _ _
        _ = ‖X - Y‖ + (1 - R / ‖X‖) * ‖X‖ := by
              rw [norm_smul, Real.norm_of_nonneg hcoef]
        _ = ‖X - Y‖ + (‖X‖ - R) := by
              rw [sub_mul, one_mul, div_mul_cancel₀ R (ne_of_gt hXpos)]
        _ ≤ ‖X - Y‖ + ‖X - Y‖ := by
              have h1 : ‖X‖ - R ≤ ‖X‖ - ‖Y‖ := by linarith
              have h2 : ‖X‖ - ‖Y‖ ≤ ‖X - Y‖ := norm_sub_norm_le X Y
              linarith
        _ = 2 * ‖X - Y‖ := by ring
    · rw [radialRetract, if_neg hX, radialRetract, if_neg hY]
      have hXgt : R < ‖X‖ := lt_of_not_ge hX
      have hYgt : R < ‖Y‖ := lt_of_not_ge hY
      have hXpos : 0 < ‖X‖ := lt_of_le_of_lt hR hXgt
      have hYpos : 0 < ‖Y‖ := lt_of_le_of_lt hR hYgt
      have hdecomp : (R / ‖X‖) • X - (R / ‖Y‖) • Y
          = (R / ‖X‖) • (X - Y) + (R / ‖X‖ - R / ‖Y‖) • Y := by
        rw [smul_sub, sub_smul]
        abel
      have hsub : R / ‖X‖ - R / ‖Y‖ = R * (‖Y‖ - ‖X‖) / (‖X‖ * ‖Y‖) := by
        field_simp
      have habs : |R / ‖X‖ - R / ‖Y‖| = R * |‖Y‖ - ‖X‖| / (‖X‖ * ‖Y‖) := by
        rw [hsub, abs_div, abs_of_pos (mul_pos hXpos hYpos), abs_mul, abs_of_nonneg hR]
      have hle_abs : |‖Y‖ - ‖X‖| ≤ ‖X - Y‖ := by
        have := abs_norm_sub_norm_le Y X
        rwa [norm_sub_rev Y X] at this
      have hmain : |R / ‖X‖ - R / ‖Y‖| * ‖Y‖ ≤ (R / ‖X‖) * ‖X - Y‖ := by
        rw [habs]
        have h1 : R * |‖Y‖ - ‖X‖| ≤ R * ‖X - Y‖ := mul_le_mul_of_nonneg_left hle_abs hR
        have h2 : R * |‖Y‖ - ‖X‖| / (‖X‖ * ‖Y‖) ≤ R * ‖X - Y‖ / (‖X‖ * ‖Y‖) :=
          div_le_div_of_nonneg_right h1 (le_of_lt (mul_pos hXpos hYpos))
        have h3 := mul_le_mul_of_nonneg_right h2 (norm_nonneg Y)
        have h4 : R * ‖X - Y‖ / (‖X‖ * ‖Y‖) * ‖Y‖ = (R / ‖X‖) * ‖X - Y‖ := by
          field_simp
        linarith [h3, h4 ▸ le_refl (R * ‖X - Y‖ / (‖X‖ * ‖Y‖) * ‖Y‖)]
      calc ‖(R / ‖X‖) • X - (R / ‖Y‖) • Y‖
          = ‖(R / ‖X‖) • (X - Y) + (R / ‖X‖ - R / ‖Y‖) • Y‖ := by rw [hdecomp]
        _ ≤ ‖(R / ‖X‖) • (X - Y)‖ + ‖(R / ‖X‖ - R / ‖Y‖) • Y‖ := norm_add_le _ _
        _ = (R / ‖X‖) * ‖X - Y‖ + |R / ‖X‖ - R / ‖Y‖| * ‖Y‖ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg (div_nonneg hR (norm_nonneg X)),
                Real.norm_eq_abs]
        _ ≤ 2 * ‖X - Y‖ := by
              have hcoef : R / ‖X‖ ≤ 1 := (div_le_one hXpos).mpr (le_of_lt hXgt)
              nlinarith [norm_nonneg (X - Y), hmain, hcoef]

theorem dist_radialRetract_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 ≤ R) (X Y : E) :
    dist (radialRetract R X) (radialRetract R Y) ≤ 2 * dist X Y := by
  rw [dist_eq_norm, dist_eq_norm]
  exact norm_radialRetract_sub_le hR X Y

/-! ### Continuous dependence on initial data (Grönwall form) -/

/-- **Continuous dependence on initial data for `x' = f x` (Gronwall form).**

Let `f` be `K`-Lipschitz on the closed ball of radius `R` around `z₀`, and let `u` be a solution of
`u' = f u` on `Icc a b` with `u a = z₀` staying within `R/2` of `z₀`.  Then every initial datum `z`
with `dist z z₀ * exp (K * (b - a)) ≤ R/4` gives rise to a solution `v` of `v' = f v` on all of
`Icc a b` with `v a = z`, and `dist (v t) (u t) ≤ dist z z₀ * exp (K * (b - a))` for all
`t ∈ Icc a b`. -/
theorem solution_close_of_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {z₀ : E} {R : ℝ} (hR : 0 < R) {K : ℝ} (hK : 0 ≤ K)
    (hf : ∀ x ∈ Metric.closedBall z₀ R, ∀ y ∈ Metric.closedBall z₀ R,
      dist (f x) (f y) ≤ K * dist x y)
    {a b : ℝ} (hab : a ≤ b) {u : ℝ → E}
    (hu : ∀ t ∈ Set.Icc a b, HasDerivAt u (f (u t)) t) (hu0 : u a = z₀)
    (huB : ∀ t ∈ Set.Icc a b, dist (u t) z₀ ≤ R / 2) :
    ∀ z : E, dist z z₀ * Real.exp (K * (b - a)) ≤ R / 4 →
      ∃ v : ℝ → E, v a = z ∧ (∀ t ∈ Set.Icc a b, HasDerivAt v (f (v t)) t) ∧
        (∀ t ∈ Set.Icc a b, dist (v t) (u t) ≤ dist z z₀ * Real.exp (K * (b - a)))
:= by
  intro z hz
  -- The truncated (globally Lipschitz) field.
  let G : E → E := fun x => z₀ + radialRetract R (x - z₀)
  let Phi : E → E := fun x => f (G x)
  have hG_ball : ∀ x, dist (G x) z₀ ≤ R := fun x => by
    simpa only [G, dist_eq_norm, add_sub_cancel_left]
      using norm_radialRetract_le hR.le (x - z₀)
  have hG_fix : ∀ x, dist x z₀ ≤ R → G x = x := fun x hx => by
    have hx' : ‖x - z₀‖ ≤ R := by rwa [dist_eq_norm] at hx
    simp only [G]
    rw [radialRetract_eq_self (x - z₀) hx', add_sub_cancel]
  have hG_lip : ∀ x y, dist (G x) (G y) ≤ 2 * dist x y := fun x y => by
    have h := dist_radialRetract_le hR.le (x - z₀) (y - z₀)
    have e1 : G x - G y = radialRetract R (x - z₀) - radialRetract R (y - z₀) := by
      simp only [G]; abel
    have e2 : (x - z₀) - (y - z₀) = x - y := by abel
    rw [dist_eq_norm, dist_eq_norm] at h
    rw [dist_eq_norm, dist_eq_norm]
    rw [e2] at h
    rw [e1]
    exact h
  have hPhi_lip : LipschitzWith ⟨2 * K, by linarith [hK]⟩ Phi := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    simp only [Phi]
    have h2 : dist (f (G x)) (f (G y)) ≤ K * dist (G x) (G y) :=
      hf (G x) (Metric.mem_closedBall.mpr (hG_ball x)) (G y)
        (Metric.mem_closedBall.mpr (hG_ball y))
    calc dist (f (G x)) (f (G y)) ≤ K * dist (G x) (G y) := h2
      _ ≤ K * (2 * dist x y) := mul_le_mul_of_nonneg_left (hG_lip x y) hK
      _ = 2 * K * dist x y := by ring
  -- A global solution of the truncated field, shifted to start at time `a`.
  obtain ⟨Y, hY0, hY⟩ := exists_global_solution_of_lipschitz hPhi_lip z
  let V : ℝ → E := fun t => Y (t - a)
  have hV0 : V a = z := by simp only [V, sub_self, hY0]
  have hVderiv : ∀ t, HasDerivAt V (Phi (V t)) t := fun t => by
    have h1 : HasDerivAt (fun s : ℝ => s - a) 1 t := (hasDerivAt_id t).sub_const a
    have h2 := (hY (t - a)).scomp t h1
    simpa only [V, Function.comp_def, one_smul, mul_one] using h2
  -- Basic bounds on the distance of the initial data to `z₀`.
  have hc0 : 0 ≤ dist z z₀ := dist_nonneg
  have hexp1 : 1 ≤ Real.exp (K * (b - a)) :=
    Real.one_le_exp (mul_nonneg hK (sub_nonneg.mpr hab))
  have hc_le : dist z z₀ ≤ R / 4 := by
    calc dist z z₀ = dist z z₀ * 1 := by ring
      _ ≤ dist z z₀ * Real.exp (K * (b - a)) := mul_le_mul_of_nonneg_left hexp1 hc0
      _ ≤ R / 4 := hz
  have hcR : dist z z₀ ≤ R := by linarith
  -- The maximal interval on which `V` remains in the ball.
  let S : Set ℝ := {t | a ≤ t ∧ t ≤ b ∧ ∀ s ∈ Set.Icc a t, dist (V s) z₀ ≤ R}
  have hSa : a ∈ S := by
    refine ⟨le_refl a, hab, ?_⟩
    intro s hs
    obtain ⟨hs1, hs2⟩ := Set.mem_Icc.mp hs
    rw [show s = a from le_antisymm hs2 hs1, hV0]
    exact hcR
  have hSbdd : BddAbove S := ⟨b, fun t ht => ht.2.1⟩
  have hSne : S.Nonempty := ⟨a, hSa⟩
  -- On `S`, Grönwall gives the estimate.
  have gron : ∀ t ∈ S, dist (V t) (u t) ≤ dist z z₀ * Real.exp (K * (t - a)) := by
    intro t ht
    obtain ⟨hat, htb, hball⟩ := ht
    have hx : ∀ s ∈ Set.Icc a t, HasDerivAt V (Phi (V s)) s := fun s _ => hVderiv s
    have hy : ∀ s ∈ Set.Icc a t, HasDerivAt u (f (u s)) s :=
      fun s hs => hu s ⟨hs.1, le_trans hs.2 htb⟩
    have hxy : ∀ s ∈ Set.Icc a t, ‖Phi (V s) - f (u s)‖ ≤ K * ‖V s - u s‖ := by
      intro s hs
      have hVs : dist (V s) z₀ ≤ R := hball s hs
      have hus : dist (u s) z₀ ≤ R :=
        le_trans (huB s ⟨hs.1, le_trans hs.2 htb⟩) (by linarith)
      have hPhiV : Phi (V s) = f (V s) := by simp only [Phi, hG_fix (V s) hVs]
      rw [hPhiV]
      have h := hf (V s) (by rwa [Metric.mem_closedBall]) (u s)
        (by rwa [Metric.mem_closedBall])
      simpa only [dist_eq_norm] using h
    have hmain := dist_le_exp_mul_dist_of_hasDerivAt_of_norm_sub_le (x := V) (y := u)
      (x' := fun s => Phi (V s)) (y' := fun s => f (u s)) (L := K) hat hK hx hy hxy
    rw [hV0, hu0] at hmain
    exact hmain
  have hbound : ∀ t ∈ S, dist (V t) z₀ ≤ 3 * R / 4 := by
    intro t ht
    have h1 := gron t ht
    obtain ⟨hat, htb, hball⟩ := ht
    have hexp : Real.exp (K * (t - a)) ≤ Real.exp (K * (b - a)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hK)
    have h2 : dist z z₀ * Real.exp (K * (t - a)) ≤ R / 4 :=
      le_trans (mul_le_mul_of_nonneg_left hexp dist_nonneg) hz
    calc dist (V t) z₀ ≤ dist (V t) (u t) + dist (u t) z₀ := dist_triangle _ _ _
      _ ≤ dist z z₀ * Real.exp (K * (t - a)) + R / 2 := by
            linarith [huB t ⟨hat, htb⟩]
      _ ≤ R / 4 + R / 2 := by linarith
      _ = 3 * R / 4 := by ring
  have haσ : a ≤ sSup S := le_csSup hSbdd hSa
  have hσb : sSup S ≤ b := csSup_le hSne (fun t ht => ht.2.1)
  have hmem_lt : ∀ s, a ≤ s → s < sSup S → s ∈ S := by
    intro s has hσ
    obtain ⟨t, htS, hst⟩ := (lt_csSup_iff hSbdd hSne).mp hσ
    refine ⟨has, le_trans (le_of_lt hst) htS.2.1, ?_⟩
    intro r hr
    exact htS.2.2 r ⟨hr.1, le_trans hr.2 (le_of_lt hst)⟩
  have hVcont : Continuous V :=
    continuous_iff_continuousAt.mpr (fun t => (hVderiv t).continuousAt)
  have hcl : IsClosed {t : ℝ | dist (V t) z₀ ≤ 3 * R / 4} :=
    isClosed_le (hVcont.dist continuous_const) continuous_const
  have hσmem : sSup S ∈ S := by
    have hσcl : sSup S ∈ closure S := csSup_mem_closure hSne hSbdd
    have hσ3 : dist (V (sSup S)) z₀ ≤ 3 * R / 4 := by
      have hmem : sSup S ∈ closure {t : ℝ | dist (V t) z₀ ≤ 3 * R / 4} :=
        closure_mono hbound hσcl
      rwa [hcl.closure_eq] at hmem
    refine ⟨haσ, hσb, ?_⟩
    intro s hs
    rcases lt_or_ge s (sSup S) with hlt | hge
    · have hsS := hmem_lt s hs.1 hlt
      exact hsS.2.2 s ⟨hs.1, le_refl s⟩
    · rw [le_antisymm hs.2 hge]
      linarith [hσ3, hR]
  -- `S` reaches `b`.
  have hτ_eq_b : sSup S = b := by
    have hle : sSup S ≤ b := hσmem.2.1
    by_contra hne
    have hlt : sSup S < b := lt_of_le_of_ne hle hne
    have hltR : dist (V (sSup S)) z₀ < R := by
      have := hbound (sSup S) hσmem; linarith
    obtain ⟨δ, hδpos, hδ⟩ := (Metric.continuousAt_iff.mp (hVcont.dist continuous_const).continuousAt)
      (R - dist (V (sSup S)) z₀) (by linarith)
    have hgen : ∀ s, sSup S < s → s ≤ min (sSup S + δ / 2) b → dist (V s) z₀ < R := by
      intro s hsgt hst
      have h1 : s ≤ sSup S + δ / 2 := le_trans hst (min_le_left _ _)
      have hsd : dist s (sSup S) < δ := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith)]
        linarith
      have h2 := hδ hsd
      rw [Real.dist_eq] at h2
      have h3 := le_abs_self (dist (V s) z₀ - dist (V (sSup S)) z₀)
      linarith
    have htS : min (sSup S + δ / 2) b ∈ S := by
      have htgt : sSup S < min (sSup S + δ / 2) b := lt_min (by linarith) hlt
      have htleb : min (sSup S + δ / 2) b ≤ b := min_le_right _ _
      refine ⟨le_trans haσ (le_of_lt htgt), htleb, ?_⟩
      intro s hs
      rcases lt_or_ge s (sSup S) with hlt2 | hge2
      · have hsS := hmem_lt s hs.1 hlt2
        exact hsS.2.2 s ⟨hs.1, le_refl s⟩
      · rcases eq_or_lt_of_le hge2 with heq | hlt3
        · rw [← heq]; linarith
        · exact le_of_lt (hgen s hlt3 hs.2)
    have hcon : min (sSup S + δ / 2) b ≤ sSup S := le_csSup hSbdd htS
    have : sSup S < min (sSup S + δ / 2) b := lt_min (by linarith) hlt
    linarith
  have hSfull : S = Set.Icc a b := by
    ext t
    constructor
    · intro ht; exact ⟨ht.1, ht.2.1⟩
    · intro ht
      refine ⟨ht.1, ht.2, ?_⟩
      intro s hs
      exact hσmem.2.2 s ⟨hs.1, le_trans hs.2 (by rw [hτ_eq_b]; exact ht.2)⟩
  refine ⟨V, hV0, ?_, ?_⟩
  · intro t ht
    have htS : t ∈ S := by rw [hSfull]; exact ht
    have hmem : dist (V t) z₀ ≤ R := htS.2.2 t ⟨ht.1, le_refl t⟩
    have hPhiV : Phi (V t) = f (V t) := by simp only [Phi, hG_fix (V t) hmem]
    exact (hVderiv t).congr_deriv hPhiV
  · intro t ht
    have htS : t ∈ S := by rw [hSfull]; exact ht
    have h1 := gron t htS
    have hexp : Real.exp (K * (t - a)) ≤ Real.exp (K * (b - a)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hK)
    calc dist (V t) (u t) ≤ dist z z₀ * Real.exp (K * (t - a)) := h1
      _ ≤ dist z z₀ * Real.exp (K * (b - a)) := mul_le_mul_of_nonneg_left hexp dist_nonneg

end Commons.Analysis.ODE
