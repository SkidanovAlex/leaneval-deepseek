import Mathlib
import Submission.Work.RPB.B5.exists_rho_per
import Submission.Work.RPB.B5.RhoPerDefs
import Submission.Work.RPB.B5.extend_rho_per_kappa
import Submission.Work.RPB.B5.rhoPer_deriv_pos_kappa
import Submission.Work.RPB.B5.Defs

/-!
# B5: the middle reparametrisation `rho` of the chord annulus (node B5)

`Work.RPB.B5.exists_rho_per_kappa` is the `kappa`-parametrised version of
`Work.RPB.B5.exists_rho_per`: the level inverse `ρh` of the chart lives on the interval
`(-κ,κ)` rather than `(-1,1)`, the agreement window is two-sided (`|x + √2| < δ`), and `δ` is
additionally constrained by `δ ≤ κ / (4√2)`.

The construction is the same blend `rhoPer ρe δ δA u₂` of the three branches (the `ρh`-branch
`ρe ∘ sig`, the affine branch `rhoMid` and the quadratic branch `rhoQuad`) as in
`exists_rho_per`; the only changes are the constants (`1` is replaced by `κ` throughout) and the
two-sided agreement.  The ingredients are

* `Work.RPB.B5.extend_rho_per_kappa` — the global `C⁸` extension `ρe` of `ρh` on the scaled slab,
  agreeing with `ρh` on `|σ| < κ/2`, Lipschitz and with strictly negative `σ`-derivative on
  `|σ| ≤ κ/4`;
* `Work.RPB.B5.rhoPer_deriv_pos_kappa` — positivity of the `x`-derivative of the blend on
  `(-√2, 0]`.
-/

open scoped ContDiff

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

noncomputable section

namespace Work.RPB.B5

theorem exists_rho_per_kappa (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    (ρ₀ : ℝ) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ) (κ : ℝ)
    (hρ₀ : 0 < ρ₀) (hπ : Real.pi ^ 2 / 4 < ρ₀) (hκ : 0 < κ)
    (hW : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hh : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hhper : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ)
    (hhmono : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      deriv (fun s : ℝ => ρh τ t s) σ ≠ 0)
    (hhpos : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) 0, 0 < ρh τ t σ)
    (hhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ) :
    ∃ rho : ℝ → ℝ → ℝ → ℝ,
      ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => rho z.1 z.2.1 z.2.2) ∧
      (∀ τ x t, rho τ x (t + 2 * Real.pi) = rho τ x t) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (-Real.sqrt 2) 0, ∀ t : ℝ,
        rho τ x t ∈ Set.Ioo (-ρ₀) ρ₀) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Ioc (-Real.sqrt 2) 0, ∀ t : ℝ,
        0 < rho τ x t ∧ rho τ x t ≤ Real.pi ^ 2 / 4) ∧
      (∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ δ ≤ κ / (4 * Real.sqrt 2) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Ioo (-Real.sqrt 2 - δ) (-Real.sqrt 2 + δ),
          ∀ t : ℝ, rho τ x t = ρh τ t (sig x)) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (-δ) 0, ∀ t : ℝ,
          rho τ x t = Real.pi ^ 2 / 4 * (1 + x / Real.sqrt 2) ^ 2)) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Ioc (-Real.sqrt 2) 0, ∀ t : ℝ,
        deriv (fun y => rho τ y t) x ≠ 0) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, rho τ 0 t = Real.pi ^ 2 / 4) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, rho τ (-Real.sqrt 2) t = 0) := by
  classical
  -- ### Step 1: the global `C⁸` extension `ρe` of `ρh`
  obtain ⟨ρe, L, hLpos, hρecd, hρeper, hρe0, hρeagree, hLip, hder⟩ :=
    extend_rho_per_kappa ρh κ hκ hh hh0 hhper hhmono hhpos
  -- ### Step 2: the constants
  set c : ℝ := min (min (1 / 4) (κ / 4)) (Real.pi ^ 2 / (4 * L)) with hc
  set δA : ℝ := min (c / (2 * Real.sqrt 2)) (Real.pi ^ 2 / (32 * Real.sqrt 2 * L)) with hδA
  set δ : ℝ := min (δA / 2) (min (1 / 8) (κ / 8)) with hδ
  set u₂ : ℝ := (1 + Real.sqrt 17) / 8 with hu₂
  have h2p : (0 : ℝ) < Real.sqrt 2 := sqrt2_pos'
  have hcpos : 0 < c := by
    rw [hc]
    exact lt_min (lt_min (by norm_num) (div_pos hκ (by norm_num)))
      (div_pos (by positivity) (by positivity))
  have hc4 : c ≤ 1 / 4 := by
    rw [hc]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hcκ4 : c ≤ κ / 4 := by
    rw [hc]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hLc : L * c ≤ Real.pi ^ 2 / 4 := by
    have h : c ≤ Real.pi ^ 2 / (4 * L) := by rw [hc]; exact min_le_right _ _
    have h1 : L * (Real.pi ^ 2 / (4 * L)) = Real.pi ^ 2 / 4 := by
      field_simp <;> ring
    nlinarith [hLpos, h, h1]
  have hδA_1 : δA ≤ c / (2 * Real.sqrt 2) := by rw [hδA]; exact min_le_left _ _
  have hδA_2 : δA ≤ Real.pi ^ 2 / (32 * Real.sqrt 2 * L) := by
    rw [hδA]; exact min_le_right _ _
  have hδApos : 0 < δA := by
    rw [hδA]
    exact lt_min (div_pos hcpos (by positivity)) (div_pos (by positivity) (by positivity))
  have hδA4 : Real.sqrt 2 * δA ≤ κ / 4 := by
    have h7 : Real.sqrt 2 * (c / (2 * Real.sqrt 2)) = c / 2 := by
      field_simp <;> ring
    have h8 : Real.sqrt 2 * δA ≤ Real.sqrt 2 * (c / (2 * Real.sqrt 2)) :=
      mul_le_mul_of_nonneg_left hδA_1 (le_of_lt h2p)
    linarith [h8, h7, hcκ4, hκ]
  have h32 : L * Real.sqrt 2 * δA ≤ Real.pi ^ 2 / 32 := by
    have h7 : L * Real.sqrt 2 * (Real.pi ^ 2 / (32 * Real.sqrt 2 * L)) = Real.pi ^ 2 / 32 := by
      field_simp <;> ring
    have h8 : L * Real.sqrt 2 * δA
        ≤ L * Real.sqrt 2 * (Real.pi ^ 2 / (32 * Real.sqrt 2 * L)) :=
      mul_le_mul_of_nonneg_left hδA_2 (by positivity)
    linarith [h8, h7]
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min (by linarith) (lt_min (by norm_num) (div_pos hκ (by norm_num)))
  have hδδA : δ < δA := by
    rw [hδ]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ8 : δ ≤ 1 / 8 := by
    rw [hδ]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδκ8 : δ ≤ κ / 8 := by
    rw [hδ]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hδ4 : δ < 1 / 4 := by linarith
  have hδκ : δ ≤ κ / (4 * Real.sqrt 2) := by
    have hle : (1 : ℝ) / 8 ≤ 1 / (4 * Real.sqrt 2) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have h1 : κ / 8 ≤ κ * (1 / (4 * Real.sqrt 2)) := by
      rw [show κ / 8 = κ * (1 / 8) by ring]
      exact mul_le_mul_of_nonneg_left hle (le_of_lt hκ)
    have h2 : κ * (1 / (4 * Real.sqrt 2)) = κ / (4 * Real.sqrt 2) := by ring
    linarith [hδκ8, h1, h2]
  have hc_div : c / (2 * Real.sqrt 2) ≤ 1 / 8 := by
    have hR : (1 : ℝ) / (8 * Real.sqrt 2) * (2 * Real.sqrt 2) = 1 / 4 := by
      field_simp <;> ring
    have h1 : c / (2 * Real.sqrt 2) ≤ (1 : ℝ) / (8 * Real.sqrt 2) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt 2), hR]
      exact hc4
    have h2 : (1 : ℝ) / (8 * Real.sqrt 2) ≤ 1 / 8 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 8 * Real.sqrt 2)]
      have h3 : (1 : ℝ) / 8 * (8 * Real.sqrt 2) = Real.sqrt 2 := by ring
      rw [h3]
      exact one_le_sqrt2
    linarith
  have hδA_le8 : δA ≤ 1 / 8 := by linarith [hδA_1, hc_div]
  have hδA_lt : δA < Real.sqrt 2 := by linarith [hδA_le8, nine_eighth_lt_sqrt2]
  have hδA_le : δA ≤ Real.sqrt 2 - δ := by
    linarith [hδA_le8, hδ8, nine_eighth_lt_sqrt2]
  have hu₂1 : δA < u₂ := by
    have hbig : (1 : ℝ) / 8 < u₂ := by rw [hu₂]; linarith [sqrt17_ge_four]
    linarith [hδA_le8, hbig]
  have hu₂2 : u₂ < Real.sqrt 2 - δ := by
    have h1 : u₂ < 1 := by rw [hu₂]; linarith [sqrt17_lt_seven]
    have h2 := nine_eighth_lt_sqrt2
    linarith [h1, hδ8, h2]
  have hu₂3 : 4 * u₂ ^ 2 ≥ 1 + u₂ := by
    rw [hu₂]
    have h17 : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
    nlinarith [Real.sqrt_nonneg 17]
  -- ### Step 3: `|sig x| ≤ c` on the region where the `ρh`-branch is active
  have hsig_le : ∀ x : ℝ, -Real.sqrt 2 ≤ x → x + Real.sqrt 2 ≤ δA → |sig x| ≤ c := by
    intro x hx1 hx2
    have h6 : Real.sqrt 2 * δA ≤ c / 2 := by
      have h7 : Real.sqrt 2 * (c / (2 * Real.sqrt 2)) = c / 2 := by
        field_simp <;> ring
      have h8 : Real.sqrt 2 * δA ≤ Real.sqrt 2 * (c / (2 * Real.sqrt 2)) :=
        mul_le_mul_of_nonneg_left hδA_1 (le_of_lt h2p)
      linarith [h8, h7]
    have h4 : Real.sqrt 2 * (x + Real.sqrt 2) ≤ c / 2 := by
      have h5 : Real.sqrt 2 * (x + Real.sqrt 2) ≤ Real.sqrt 2 * δA :=
        mul_le_mul_of_nonneg_left hx2 (le_of_lt h2p)
      linarith [h5, h6]
    have h2' : x + Real.sqrt 2 ≤ 2 * Real.sqrt 2 := by
      linarith [hx2, hδA_le8, h2p]
    have h3 := sig_abs_le_rp hx1 h2'
    linarith [h3, h4, hcpos]
  -- ### Step 3b: `|sig x| < κ/2` on the two-sided `δ`-window
  have hsig_near : ∀ x : ℝ, |x + Real.sqrt 2| < δ → |sig x| < κ / 2 := by
    intro x hx
    set u : ℝ := x + Real.sqrt 2 with hu
    have huabs : |u| < δ := hx
    have hule : |u| ≤ 1 / 8 := le_of_lt (lt_of_lt_of_le huabs hδ8)
    have hsige : sig x = u ^ 2 / 2 - Real.sqrt 2 * u := by
      rw [hu]; exact sig_eq' x
    have hb : |sig x| ≤ (Real.sqrt 2 + 1 / 16) * |u| := by
      rw [hsige]
      have h1 : |u ^ 2 / 2 - Real.sqrt 2 * u| ≤ |u ^ 2 / 2| + |Real.sqrt 2 * u| :=
        abs_sub _ _
      have h2 : |u ^ 2 / 2| = |u| ^ 2 / 2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_pow]
      have h3 : |Real.sqrt 2 * u| = Real.sqrt 2 * |u| := by
        rw [abs_mul, abs_of_pos h2p]
      rw [h2, h3] at h1
      have h4 : |u| ^ 2 / 2 ≤ |u| / 16 := by nlinarith [hule, abs_nonneg u]
      nlinarith [h1, h4]
    have hcoef : Real.sqrt 2 + 1 / 16 ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have hstep : (Real.sqrt 2 + 1 / 16) * |u| < κ / 2 := by
      have h1 : (Real.sqrt 2 + 1 / 16) * |u| ≤ 2 * |u| :=
        mul_le_mul_of_nonneg_right hcoef (abs_nonneg u)
      have h2 : 2 * |u| < 2 * δ := by linarith [huabs]
      have h3 : 2 * δ ≤ κ / 4 := by linarith [hδκ8]
      linarith [h1, h2, h3, hκ]
    exact lt_of_le_of_lt hb hstep
  -- ### Step 4: the upper bound `rho ≤ π²/4`
  have hval_le : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x : ℝ, -Real.sqrt 2 ≤ x → x ≤ 0 → ∀ t : ℝ,
      rhoPer ρe δ δA u₂ τ x t ≤ Real.pi ^ 2 / 4 := by
    intro τ hτ x hx1 hx2 t
    rcases eq_or_lt_of_le (wL_nonneg δ δA x) with hw | hw
    · have hw0 : wL δ δA x = 0 := hw.symm
      have hsum : wM δ δA u₂ x * (Real.pi ^ 2 / 4) + wR δ u₂ x * (Real.pi ^ 2 / 4)
          = Real.pi ^ 2 / 4 := by
        have h1 : wM δ δA u₂ x + wR δ u₂ x = 1 := by unfold wM; rw [hw0]; ring
        rw [← add_mul, h1, one_mul]
      have h1 : rhoMid x ≤ Real.pi ^ 2 / 4 := rhoMid_le' x (by linarith)
      have h2 : rhoQuad x ≤ Real.pi ^ 2 / 4 := rhoQuad_le' x hx1 hx2
      have h3 : 0 ≤ wM δ δA u₂ x := wM_nonneg hδδA hu₂1 hu₂2 x
      have h4 : 0 ≤ wR δ u₂ x := wR_nonneg δ u₂ x
      have h5 : rhoPer ρe δ δA u₂ τ x t
          = wM δ δA u₂ x * rhoMid x + wR δ u₂ x * rhoQuad x := by
        unfold rhoPer; rw [hw0]; ring
      have hA' := mul_le_mul_of_nonneg_left h1 h3
      have hB' := mul_le_mul_of_nonneg_left h2 h4
      rw [h5]
      linarith [hA', hB', hsum]
    · have hu : x + Real.sqrt 2 < δA := by
        by_contra hc'
        rw [wL_eq_zero hδδA (le_of_not_gt hc')] at hw
        exact lt_irrefl 0 hw
      have hR0 : wR δ u₂ x = 0 := wR_eq_zero hu₂2 (by linarith [le_of_lt hu, hu₂1])
      have hs2 : |sig x| ≤ c := hsig_le x hx1 (le_of_lt hu)
      have hs4 : |sig x| ≤ κ / 4 := by linarith [hs2, hcκ4]
      have hb := hLip τ hτ t (sig x) hs4
      have hAeq : ρe τ t (sig x) = ρh τ t (sig x) :=
        hρeagree τ hτ t (sig x) (by linarith [hs2, hcκ4, hκ])
      have hLu : L * |sig x| ≤ Real.pi ^ 2 / 4 := by
        have := mul_le_mul_of_nonneg_left hs2 (le_of_lt hLpos)
        linarith [this, hLc]
      have hA1 : ρh τ t (sig x) ≤ Real.pi ^ 2 / 4 := le_trans (abs_le.mp hb).2 hLu
      have hsum : wL δ δA x * (Real.pi ^ 2 / 4) + wM δ δA u₂ x * (Real.pi ^ 2 / 4)
          = Real.pi ^ 2 / 4 := by
        have h1 : wL δ δA x + wM δ δA u₂ x = 1 := by unfold wM; rw [hR0]; ring
        rw [← add_mul, h1, one_mul]
      have h1 : rhoMid x ≤ Real.pi ^ 2 / 4 := rhoMid_le' x (by linarith)
      have h3 : 0 ≤ wM δ δA u₂ x := wM_nonneg hδδA hu₂1 hu₂2 x
      have hwl : 0 ≤ wL δ δA x := wL_nonneg δ δA x
      have h5 : rhoPer ρe δ δA u₂ τ x t
          = wL δ δA x * ρe τ t (sig x) + wM δ δA u₂ x * rhoMid x := by
        unfold rhoPer; rw [hR0]; ring
      have hA' := mul_le_mul_of_nonneg_left hA1 hwl
      have hB' := mul_le_mul_of_nonneg_left h1 h3
      rw [h5, hAeq]
      linarith [hA', hB', hsum]
  -- ### Step 5: assembly
  refine ⟨rhoPer ρe δ δA u₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    have hproj : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => z.2.1) := by fun_prop
    have hmap : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.2, sig z.2.1))) := by
      refine ContDiff.prodMk (by fun_prop) ?_
      exact ContDiff.prodMk (by fun_prop) (sig_contDiff.comp (by fun_prop))
    have h1 : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) =>
        wL δ δA z.2.1 * ρe z.1 z.2.2 (sig z.2.1)) :=
      ContDiff.mul ((wL_contDiff δ δA).comp hproj) (hρecd.comp hmap)
    have h2 : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => wM δ δA u₂ z.2.1 * rhoMid z.2.1) :=
      ContDiff.mul ((wM_contDiff δ δA u₂).comp hproj) (by unfold rhoMid; fun_prop)
    have h3 : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => wR δ u₂ z.2.1 * rhoQuad z.2.1) :=
      ContDiff.mul ((wR_contDiff δ u₂).comp hproj) (by unfold rhoQuad; fun_prop)
    unfold rhoPer
    exact ContDiff.add (ContDiff.add h1 h2) h3
  · -- periodicity
    intro τ x t
    unfold rhoPer
    rw [hρeper τ t (sig x)]
  · -- the bound `(-ρ₀, ρ₀)`
    intro τ hτ x hx t
    obtain ⟨hx1, hx2⟩ := hx
    have hn : 0 ≤ rhoPer ρe δ δA u₂ τ x t := by
      rcases eq_or_lt_of_le (wL_nonneg δ δA x) with hw | hw
      · have hw0 : wL δ δA x = 0 := hw.symm
        have h3 : 0 ≤ wM δ δA u₂ x := wM_nonneg hδδA hu₂1 hu₂2 x
        have h4 : 0 ≤ wR δ u₂ x := wR_nonneg δ u₂ x
        have h1 : 0 ≤ rhoMid x := le_of_lt (rhoMid_pos' x (by linarith [hx1, h2p]))
        have h2 : 0 ≤ rhoQuad x := rhoQuad_nonneg' x
        have h5 : rhoPer ρe δ δA u₂ τ x t
            = wM δ δA u₂ x * rhoMid x + wR δ u₂ x * rhoQuad x := by
          unfold rhoPer; rw [hw0]; ring
        rw [h5]
        exact add_nonneg (mul_nonneg h3 h1) (mul_nonneg h4 h2)
      · have hu : x + Real.sqrt 2 < δA := by
          by_contra hc'
          rw [wL_eq_zero hδδA (le_of_not_gt hc')] at hw
          exact lt_irrefl 0 hw
        have hR0 : wR δ u₂ x = 0 := wR_eq_zero hu₂2 (by linarith [le_of_lt hu, hu₂1])
        have hs2 : |sig x| ≤ c := hsig_le x hx1 (le_of_lt hu)
        have hAeq : ρe τ t (sig x) = ρh τ t (sig x) :=
          hρeagree τ hτ t (sig x) (by linarith [hs2, hcκ4, hκ])
        have hs : |sig x| < κ / 2 := by linarith [hs2, hcκ4, hκ]
        have hsig' : -κ < sig x := by
          have h := (abs_le.mp (le_of_lt hs)).1
          linarith
        have hsigI : sig x ∈ Set.Icc (-κ) 0 := by
          refine ⟨le_of_lt hsig', ?_⟩
          rw [sig_eq' x]
          have hu0 : 0 ≤ x + Real.sqrt 2 := by linarith [hx1, h2p]
          have hu2 : x + Real.sqrt 2 ≤ 2 * Real.sqrt 2 := by linarith [hx2, h2p]
          nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu2)]
        have hApos : 0 ≤ ρh τ t (sig x) := by
          rcases lt_or_eq_of_le hsigI.2 with h0 | h0
          · exact le_of_lt (hhpos τ hτ t (sig x) ⟨hsig', h0⟩)
          · rw [h0]; exact (hh0 τ hτ t).ge
        have h3 : 0 ≤ wM δ δA u₂ x := wM_nonneg hδδA hu₂1 hu₂2 x
        have h1 : 0 ≤ rhoMid x := le_of_lt (rhoMid_pos' x (by linarith [hx1, h2p]))
        have h5 : rhoPer ρe δ δA u₂ τ x t
            = wL δ δA x * ρe τ t (sig x) + wM δ δA u₂ x * rhoMid x := by
          unfold rhoPer; rw [hR0]; ring
        rw [h5, hAeq]
        exact add_nonneg (mul_nonneg (le_of_lt hw) hApos) (mul_nonneg h3 h1)
    have hl := hval_le τ hτ x hx1 hx2 t
    exact ⟨by linarith, by linarith⟩
  · -- positivity and the bound `π²/4`
    intro τ hτ x hx t
    obtain ⟨hx1, hx2⟩ := hx
    have hx1' : -Real.sqrt 2 ≤ x := le_of_lt hx1
    refine ⟨?_, hval_le τ hτ x hx1' hx2 t⟩
    rcases eq_or_lt_of_le (wL_nonneg δ δA x) with hw | hw
    · have hw0 : wL δ δA x = 0 := hw.symm
      have hsum : wM δ δA u₂ x + wR δ u₂ x = 1 := by unfold wM; rw [hw0]; ring
      have h3 : 0 ≤ wM δ δA u₂ x := wM_nonneg hδδA hu₂1 hu₂2 x
      have h4 : 0 ≤ wR δ u₂ x := wR_nonneg δ u₂ x
      have h1 : 0 < rhoMid x := rhoMid_pos' x (by linarith [hx1, h2p])
      have h2 : 0 < rhoQuad x := rhoQuad_pos' x hx1
      have h5 : rhoPer ρe δ δA u₂ τ x t
          = wM δ δA u₂ x * rhoMid x + wR δ u₂ x * rhoQuad x := by
        unfold rhoPer; rw [hw0]; ring
      rw [h5]
      rcases lt_or_ge 0 (wM δ δA u₂ x) with h6 | h6
      · exact lt_of_lt_of_le (mul_pos h6 h1)
          (le_add_of_nonneg_right (mul_nonneg h4 (le_of_lt h2)))
      · have h6' : wM δ δA u₂ x = 0 := le_antisymm h6 h3
        have h7 : 0 < wR δ u₂ x := by linarith [hsum, h6']
        have h8 := mul_pos h7 h2
        rw [h6']
        simpa using h8
    · have hu : x + Real.sqrt 2 < δA := by
        by_contra hc'
        rw [wL_eq_zero hδδA (le_of_not_gt hc')] at hw
        exact lt_irrefl 0 hw
      have hR0 : wR δ u₂ x = 0 := wR_eq_zero hu₂2 (by linarith [le_of_lt hu, hu₂1])
      have hs2 : |sig x| ≤ c := hsig_le x hx1' (le_of_lt hu)
      have hAeq : ρe τ t (sig x) = ρh τ t (sig x) :=
        hρeagree τ hτ t (sig x) (by linarith [hs2, hcκ4, hκ])
      have hs : |sig x| < κ / 2 := by linarith [hs2, hcκ4, hκ]
      have hsig : sig x ∈ Set.Ioo (-κ) 0 := by
        refine ⟨by linarith [(abs_le.mp (le_of_lt hs)).1], ?_⟩
        rw [sig_eq' x]
        have hu0 : 0 < x + Real.sqrt 2 := by linarith [hx1, h2p]
        have hu2 : x + Real.sqrt 2 ≤ 2 * Real.sqrt 2 := by linarith [hx2, h2p]
        nlinarith [hu0, hu2, h2p]
      have hApos : 0 < ρh τ t (sig x) := hhpos τ hτ t (sig x) hsig
      have h1 : 0 < rhoMid x := rhoMid_pos' x (by linarith [hx1, h2p])
      have h3 : 0 ≤ wM δ δA u₂ x := wM_nonneg hδδA hu₂1 hu₂2 x
      have h5 : rhoPer ρe δ δA u₂ τ x t
          = wL δ δA x * ρe τ t (sig x) + wM δ δA u₂ x * rhoMid x := by
        unfold rhoPer; rw [hR0]; ring
      have hA' : 0 < wL δ δA x * ρh τ t (sig x) := mul_pos hw hApos
      have hB' := mul_nonneg h3 (le_of_lt h1)
      rw [h5, hAeq]
      exact lt_of_lt_of_le hA' (le_add_of_nonneg_right hB')
  · -- the two agreement regions
    refine ⟨δ, hδpos, hδ4, hδκ, ?_, ?_⟩
    · intro τ hτ x hx t
      rw [Set.mem_Ioo] at hx
      have hu1 : x + Real.sqrt 2 < δ := by linarith [hx.2]
      have hL1 : wL δ δA x = 1 := wL_eq_one hδδA (le_of_lt hu1)
      have hR0 : wR δ u₂ x = 0 := wR_eq_zero hu₂2 (by linarith [hu1, hδδA, hu₂1])
      have hm : wM δ δA u₂ x = 0 := by unfold wM; rw [hL1, hR0]; ring
      have hs : |sig x| < κ / 2 := by
        apply hsig_near x
        rw [abs_lt]
        exact ⟨by linarith [hx.1], hu1⟩
      have h5 : rhoPer ρe δ δA u₂ τ x t = ρe τ t (sig x) := by
        unfold rhoPer; rw [hL1, hm, hR0]; ring
      rw [h5]
      exact hρeagree τ hτ t (sig x) hs
    · intro τ hτ x hx t
      obtain ⟨hx1, hx2⟩ := hx
      have hL0 : wL δ δA x = 0 := wL_eq_zero hδδA (by linarith [hx1, hδA_le])
      have hR1 : wR δ u₂ x = 1 := wR_eq_one hu₂2 hx1
      have hm : wM δ δA u₂ x = 0 := by unfold wM; rw [hL0, hR1]; ring
      have h5 : rhoPer ρe δ δA u₂ τ x t = rhoQuad x := by
        unfold rhoPer; rw [hL0, hm, hR1]; ring
      rw [h5, rhoQuad]
  · -- the derivative does not vanish
    intro τ hτ x hx t
    have hA : ∀ τ' ∈ Set.Icc (0 : ℝ) 1, ∀ t' x' : ℝ, δ < x' + Real.sqrt 2 →
        x' + Real.sqrt 2 < δA → ρe τ' t' (sig x') ≤ Real.pi ^ 2 / 32 := by
      intro τ' hτ' t' x' h1 h2
      have hx1' : -Real.sqrt 2 ≤ x' := by linarith [h1, hδpos, h2p]
      have hx2' : x' + Real.sqrt 2 ≤ 2 * Real.sqrt 2 := by linarith [h2, hδA_lt, h2p]
      have habs : |sig x'| ≤ Real.sqrt 2 * (x' + Real.sqrt 2) := sig_abs_le_rp hx1' hx2'
      have hsm : |sig x'| ≤ κ / 4 := by
        have h3 : Real.sqrt 2 * (x' + Real.sqrt 2) ≤ Real.sqrt 2 * δA :=
          mul_le_mul_of_nonneg_left (le_of_lt h2) (le_of_lt h2p)
        linarith [habs, h3, hδA4]
      have hs : |sig x'| < κ / 2 := by linarith [hsm, hκ]
      have heq : ρe τ' t' (sig x') = ρh τ' t' (sig x') := hρeagree τ' hτ' t' (sig x') hs
      have hb := hLip τ' hτ' t' (sig x') hsm
      have hLu : L * |sig x'| ≤ Real.pi ^ 2 / 32 := by
        have h1' : L * |sig x'| ≤ L * (Real.sqrt 2 * (x' + Real.sqrt 2)) :=
          mul_le_mul_of_nonneg_left habs (le_of_lt hLpos)
        have h2' : L * (Real.sqrt 2 * (x' + Real.sqrt 2)) ≤ L * Real.sqrt 2 * δA := by
          have h4 := mul_le_mul_of_nonneg_left (le_of_lt h2) (le_of_lt h2p)
          nlinarith [hLpos, h4]
        exact le_trans h1' (le_trans h2' h32)
      calc ρe τ' t' (sig x') = ρh τ' t' (sig x') := heq
        _ ≤ L * |sig x'| := (abs_le.mp hb).2
        _ ≤ Real.pi ^ 2 / 32 := hLu
    exact ne_of_gt
      (rhoPer_deriv_pos_kappa ρe δ δA u₂ κ hκ hδpos hδδA hu₂1 hu₂2 hδA4 hder hA hu₂3 τ hτ x hx t)
  · -- value at `x = 0`
    intro τ hτ t
    have hR1 : wR δ u₂ 0 = 1 := wR_eq_one hu₂2 (by linarith [hδpos])
    have hL0 : wL δ δA 0 = 0 := wL_eq_zero hδδA (by linarith [hδA_lt])
    have hm : wM δ δA u₂ 0 = 0 := by unfold wM; rw [hL0, hR1]; ring
    have h5 : rhoPer ρe δ δA u₂ τ 0 t = rhoQuad 0 := by
      unfold rhoPer; rw [hL0, hm, hR1]; ring
    rw [h5, rhoQuad]
    norm_num
  · -- value at `x = -√2`
    intro τ hτ t
    have hL1 : wL δ δA (-Real.sqrt 2) = 1 := by
      refine wL_eq_one hδδA ?_
      linarith [hδpos]
    have hR0 : wR δ u₂ (-Real.sqrt 2) = 0 := by
      refine wR_eq_zero hu₂2 ?_
      linarith [hu₂1, h2p]
    have hm : wM δ δA u₂ (-Real.sqrt 2) = 0 := by unfold wM; rw [hL1, hR0]; ring
    have h5 : rhoPer ρe δ δA u₂ τ (-Real.sqrt 2) t = ρe τ t (sig (-Real.sqrt 2)) := by
      unfold rhoPer; rw [hL1, hm, hR0]; ring
    rw [h5]
    have hz : sig (-Real.sqrt 2) = 0 := by
      rw [sig_eq']
      rw [show -Real.sqrt 2 + Real.sqrt 2 = 0 by ring]
      ring
    rw [hz]
    exact hρe0 τ t

end Work.RPB.B5

