import Mathlib
import Submission.Work.Diff.Alg.Pinch.Chat_margin
import Submission.Work.Diff.Alg.Pinch.ChatT_one_step_pic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Room around a `PIC2` tensor in a strictly positive direction

`Work.Diff.Alg.Pinch.inPIC2_room`: if `S` is an algebraic curvature tensor in the cone `InPIC2`
(nonnegative complex sectional curvature) and `W` is an algebraic curvature tensor that is
*strictly* positive in every direction `(x,y,z,w)` in which `EFun S` vanishes but the round sphere
does not (i.e. in every non-degenerate null direction of `S`), then small perturbations
`S + τ • (W + Y)` of `S` in the direction `W` are again in `InPIC2`: there are `ε > 0`, `ρ > 0`
with `InPIC2 (S + τ • (W + Y))` whenever `0 < τ ≤ ε`, `Y` is algebraic and `‖Y‖ ≤ ρ`.

This is the "room" statement behind the Böhm–Wilking / Brendle–Schoen pinching set argument: the
strictness of `W` on the null frame of `S` is *uniform* over the compact set of normalized
directions, so it survives a linearization in `τ` together with an arbitrarily small tensor
perturbation.

## Route

All three forms `EFun S`, `EFun W`, `EFun Y` are quartic forms in the real four-tuple
`(x,y,z,w)` which only depend on the complex pair `(ζ, η) = (x + iy, z + iw)`, are `ℂ`-bilinear in
the sense `EFun R (a • ζ) (d • η) = |a d|² EFun R ζ η` (for algebraic `R`), and are *invariant*
under the unipotent change `η ↦ η + c • ζ`.  Hence an arbitrary pair can be reduced, without
changing the value of any of the three forms, to a `cHerm`-orthonormal pair `(u,v)` (rescaling by
nonnegative factors `t, t'`):

  `EFun R ζ η = t · t' · EFun R u v`,  `(u,v) ∈ ChatT_K n`  (`‖u‖ = ‖v‖ = 1`, `cHerm u v = 0`),

unless `ζ = 0` or `η ∈ ℂζ`, in which case *all* the forms vanish.

On the compact set `K = ChatT_K n` the two inputs of the compact margin lemma
`ChatT_compact_eps_delta` hold: `EFunC S ≥ 0` (from `InPIC2 S`) and `EFunC W > 0` wherever
`EFunC S = 0` (from `hstrict`, since `EFunC (Iso n) = 1` on `K`).  This yields `ε > 0` and, at
`s = ε`, a margin `δ > 0` with `δ ≤ EFunC S u v + ε * EFunC W u v` for all `(u,v) ∈ K`.
The perturbation is controlled by `cm_EF_bound` (`|EFunC Y| ≤ C₁ ‖Y‖` on `K`), so with
`ρ = δ / (2 ε C₁)` the two estimates combine: multiplying by `2 ε > 0`,

  `2 ε (A + τ(B + C)) ≥ 2 ε A + 2 τ (δ - A) - τ δ = 2 A (ε - τ) + τ δ ≥ 0`

for `0 < τ ≤ ε`, `A = EFunC S u v ≥ 0`, `B = EFunC W u v`, `C = EFunC Y u v ≥ -δ/(2ε)`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg Work.Diff.Alg.Q2P Work.Diff.Alg.Q2PR

variable {n : ℕ}

/-- On the compact set `ChatT_K n` of complex orthonormal pairs, the isotropic-curvature form of an
algebraic curvature tensor is bounded by its sup norm (this is `cm_EF_bound` together with
`EFunC (Iso n) = 1` on `K`). -/
theorem room_EFunC_bound (n : ℕ) {C : ℝ}
    (hC : ∀ D : Submission.Diff.Alg.Curv4 n, Submission.Diff.Alg.IsAlgCurv D →
      ∀ x y z w : Fin n → ℝ,
        |Cone.EF D x y z w| ≤ C * ‖D‖ * Cone.EF (Submission.Diff.Alg.Iso n) x y z w) :
    ∀ D : Submission.Diff.Alg.Curv4 n, Submission.Diff.Alg.IsAlgCurv D →
      ∀ p ∈ ChatT_K n, |EFunC D p.1 p.2| ≤ C * ‖D‖ := by
  intro D hD p hp
  have h := hC D hD (cRe p.1) (cIm p.1) (cRe p.2) (cIm p.2)
  have h1 : Cone.EF (Submission.Diff.Alg.Iso n) (cRe p.1) (cIm p.1) (cRe p.2) (cIm p.2) = 1 :=
    ChatT_K_isZeroFree hp
  rw [h1, mul_one] at h
  exact h

theorem inPIC2_room (n : ℕ) {S W : Submission.Diff.Alg.Curv4 n} (hS : Submission.Diff.Alg.IsAlgCurv S) (hW : Submission.Diff.Alg.IsAlgCurv W)
    (hP : Submission.Diff.Alg.InPIC2 S)
    (hstrict : ∀ x y z w : Fin n → ℝ, Work.Diff.Alg.Q2P.EFun S x y z w = 0 →
      Work.Diff.Alg.Q2P.EFun (Submission.Diff.Alg.Iso n) x y z w ≠ 0 → 0 < Work.Diff.Alg.Q2P.EFun W x y z w) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ ε →
      ∀ Y : Submission.Diff.Alg.Curv4 n, Submission.Diff.Alg.IsAlgCurv Y → ‖Y‖ ≤ ρ → Submission.Diff.Alg.InPIC2 (S + τ • (W + Y)) := by
  obtain ⟨C, hC0, hC⟩ := cm_EF_bound n
  set C₁ : ℝ := max C 1 with hC₁def
  have hC₁pos : 0 < C₁ := lt_of_lt_of_le one_pos (le_max_right C 1)
  have hCle : C ≤ C₁ := le_max_left C 1
  -- the perturbation bound on the compact set
  have hpert : ∀ D : Curv4 n, IsAlgCurv D → ∀ p ∈ ChatT_K n, |EFunC D p.1 p.2| ≤ C₁ * ‖D‖ := by
    intro D hD p hp
    have h1 := room_EFunC_bound n hC D hD p hp
    have h2 : C * ‖D‖ ≤ C₁ * ‖D‖ := mul_le_mul_of_nonneg_right hCle (norm_nonneg D)
    linarith
  -- the two pointwise inputs of the compact margin lemma on `ChatT_K n`
  have hAK : ∀ p ∈ ChatT_K n, 0 ≤ EFunC S p.1 p.2 := fun p _ => ChatT_inPIC2_EFunC hP p.1 p.2
  have hAB : ∀ p ∈ ChatT_K n, EFunC S p.1 p.2 = 0 → 0 < EFunC W p.1 p.2 := by
    intro p hp h0
    refine ChatT_strict_EFunC hstrict h0 ?_
    rw [ChatT_K_isZeroFree hp]
    exact one_ne_zero
  obtain ⟨ε, hε0, hε⟩ := ChatT_compact_eps_delta (ChatT_K_compact n)
    (ChatT_continuous_EFunC S).continuousOn (ChatT_continuous_EFunC W).continuousOn hAK hAB
  obtain ⟨δ, hδ0, hδ⟩ := hε ε hε0 le_rfl
  have hpos2 : 0 < 2 * ε * C₁ := mul_pos (mul_pos (by norm_num) hε0) hC₁pos
  refine ⟨ε, hε0, δ / (2 * ε * C₁), div_pos hδ0 hpos2, ?_⟩
  intro τ hτ0 hτε Y hYalg hYρ
  have hYb : ∀ p ∈ ChatT_K n, -(C₁ * ‖Y‖) ≤ EFunC Y p.1 p.2 := by
    intro p hp
    have h1 := hpert Y hYalg p hp
    exact (abs_le.mp h1).1
  rw [Work.Diff.Alg.Q2P.inPIC2_iff_c]
  intro ζ η
  have hlin1 : EFunC (S + τ • (W + Y)) ζ η = EFunC S ζ η + τ * EFunC (W + Y) ζ η := by
    simpa using ChatT_EFunC_lin S (W + Y) 0 τ 0 ζ η
  have hlin2 : EFunC (W + Y) ζ η = EFunC W ζ η + EFunC Y ζ η := by
    simpa using ChatT_EFunC_lin W Y 0 1 0 ζ η
  rw [hlin1, hlin2]
  by_cases hζ0 : ζ = 0
  · -- degenerate case: the first vector vanishes
    rw [hζ0, ChatT_EFunC_zero_left, ChatT_EFunC_zero_left, ChatT_EFunC_zero_left]
    simp
  · -- project the second vector onto the `cHerm`-orthogonal complement of the first
    have hζζ : cHerm ζ ζ ≠ 0 := by
      rw [cHerm_self]
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (ChatT_cNSq_pos.mpr hζ0))
    set η' : Fin n → ℂ := η - (cHerm η ζ / cHerm ζ ζ) • ζ with hη'def
    have horth : cHerm η' ζ = 0 := by
      rw [hη'def]
      exact ChatT_cHerm_proj hζζ
    have hproj : ∀ R : Curv4 n, IsAlgCurv R → EFunC R ζ η = EFunC R ζ η' := by
      intro R hR
      rw [hη'def]
      exact (ChatT_EFunC_sub_smul R hR ζ η (cHerm η ζ / cHerm ζ ζ)).symm
    by_cases hη'0 : η' = 0
    · -- degenerate case: the pair is complex dependent, so all three forms vanish
      have hz : ∀ R : Curv4 n, IsAlgCurv R → EFunC R ζ η = 0 := by
        intro R hR
        rw [hproj R hR, hη'0, ChatT_EFunC_zero_right]
      rw [hz S hS, hz W hW, hz Y hYalg]
      simp
    · -- non-degenerate case: rescale to a point of the compact set and use the margin
      have horth' : cHerm ζ η' = 0 := by
        rw [cHerm_conj_symm, horth]
        simp
      obtain ⟨t, t', u, v, ht, ht', hu, hv, huv, hzu, hzv⟩ := ChatT_normalize hζ0 hη'0 horth'
      have hpK : (u, v) ∈ ChatT_K n := ⟨hu, hv, huv⟩
      have hδuv : δ ≤ EFunC S u v + ε * EFunC W u v := hδ (u, v) hpK
      have hAuv : 0 ≤ EFunC S u v := hAK (u, v) hpK
      have hYuv : -(C₁ * ‖Y‖) ≤ EFunC Y u v := hYb (u, v) hpK
      have hSsc : EFunC S ζ η = t * t' * EFunC S u v := by
        rw [hproj S hS, hzu, hzv]
        exact ChatT_EFunC_sqrt_smul S hS u v ht.le ht'.le
      have hWsc : EFunC W ζ η = t * t' * EFunC W u v := by
        rw [hproj W hW, hzu, hzv]
        exact ChatT_EFunC_sqrt_smul W hW u v ht.le ht'.le
      have hYsc : EFunC Y ζ η = t * t' * EFunC Y u v := by
        rw [hproj Y hYalg, hzu, hzv]
        exact ChatT_EFunC_sqrt_smul Y hYalg u v ht.le ht'.le
      rw [hSsc, hWsc, hYsc]
      -- the core inequality at the normalized pair
      have hcore : 0 ≤ EFunC S u v + τ * (EFunC W u v + EFunC Y u v) := by
        have hεB : δ - EFunC S u v ≤ ε * EFunC W u v := by linarith [hδuv]
        have hρb : (2 * ε * C₁) * ‖Y‖ ≤ δ := by
          calc (2 * ε * C₁) * ‖Y‖ ≤ (2 * ε * C₁) * (δ / (2 * ε * C₁)) :=
                mul_le_mul_of_nonneg_left hYρ hpos2.le
            _ = δ := by rw [mul_comm]; exact div_mul_cancel₀ δ (ne_of_gt hpos2)
        have h1 : 2 * τ * (δ - EFunC S u v) ≤ 2 * ε * τ * EFunC W u v := by
          have h : 2 * τ * (δ - EFunC S u v) ≤ 2 * τ * (ε * EFunC W u v) :=
            mul_le_mul_of_nonneg_left hεB (by positivity)
          nlinarith [h]
        have h2 : -(τ * δ) ≤ 2 * ε * τ * EFunC Y u v := by
          have hτδ : τ * ((2 * ε * C₁) * ‖Y‖) ≤ τ * δ :=
            mul_le_mul_of_nonneg_left hρb hτ0.le
          have h : -(2 * ε * τ * (C₁ * ‖Y‖)) ≤ 2 * ε * τ * EFunC Y u v := by
            have h' := mul_le_mul_of_nonneg_left hYuv (by positivity : (0:ℝ) ≤ 2 * ε * τ)
            simpa [mul_neg] using h'
          nlinarith [h, hτδ]
        have h3 : 0 ≤ 2 * EFunC S u v * (ε - τ) :=
          mul_nonneg (mul_nonneg (by norm_num) hAuv) (sub_nonneg.mpr hτε)
        have h4 : 0 ≤ τ * δ := mul_nonneg hτ0.le hδ0.le
        have hexp : 2 * ε * (EFunC S u v + τ * (EFunC W u v + EFunC Y u v))
            = 2 * ε * EFunC S u v + 2 * ε * τ * EFunC W u v
              + 2 * ε * τ * EFunC Y u v := by ring
        have hbig : 0 ≤ 2 * ε * (EFunC S u v + τ * (EFunC W u v + EFunC Y u v)) := by
          rw [hexp]
          nlinarith [h1, h2, h3, h4]
        exact (mul_nonneg_iff_of_pos_left (mul_pos (by norm_num) hε0)).mp hbig
      have hfac : t * t' * EFunC S u v + τ * (t * t' * EFunC W u v + t * t' * EFunC Y u v)
          = t * t' * (EFunC S u v + τ * (EFunC W u v + EFunC Y u v)) := by ring
      rw [hfac]
      exact mul_nonneg (mul_nonneg ht.le ht'.le) hcore

end Work.Diff.Alg.Pinch
