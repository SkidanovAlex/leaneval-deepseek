import Mathlib
import Submission.Work.SeedCertNum.Petal

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

/-! ## Auxiliary lemmas for `petal_P2`

The telescope `w(F z) = w(z) + 1 + η` is split into

* `fatouW_step_expansion` — the (pure field) algebraic identity, and
* `fatouW_drift_bound` — the norm bound `‖η‖ ≤ η*`.

Both are stated for the abstract Taylor step `u ↦ u + A u² + E u` and are applied to
`u = z - z₁`, `Eu = E u`. -/

/-- The algebraic identity behind the Fatou coordinate of the Taylor model:
with `w(u) = -1/(A u)` and `x = A u + E u / u`,
`w(u(1+x)) = w(u) + 1 - (x + w(u)·(E u/u))/(1+x)`.  (Here `u(1+x) = u + A u² + E u`.) -/
private lemma fatouW_step_expansion {A u Eu : ℂ} (hA : A ≠ 0) (hu : u ≠ 0)
    (h1 : 1 + (A * u + Eu / u) ≠ 0) :
    -1 / (A * (u + A * u ^ 2 + Eu)) =
      -1 / (A * u) + 1 - ((A * u + Eu / u) + (-1 / (A * u)) * (Eu / u)) /
        (1 + (A * u + Eu / u)) := by
  have hstep1 : -1 / (A * (u + A * u ^ 2 + Eu)) =
      (-1 / (A * u)) / (1 + (A * u + Eu / u)) := by
    field_simp
    ring
  rw [hstep1]
  have hwx : (-1 / (A * u)) * (A * u + Eu / u) = -1 + (-1 / (A * u)) * (Eu / u) := by
    field_simp
    ring
  have hkey : ∀ (w x e : ℂ), 1 + x ≠ 0 → w * x = -1 + w * e →
      w / (1 + x) = w + 1 - (x + w * e) / (1 + x) := by
    intro w x e hx hwx'
    field_simp
    have hexp : (1 + x) * (w + 1) - (x + w * e) = w + (w * x - (-1 + w * e)) := by ring
    rw [hexp, hwx']
    ring
  exact hkey _ _ _ h1 hwx

/-- Pure real arithmetic: `(c+d)/(1-a(1+k)) ≤ k + a(1+k)²/(1-a(1+k))` when `c ≤ a(1+k)`,
`d ≤ k` and `a(1+k) < 1` (which forces `1 - a(1+k) > 0`); the identity
`(a(1+k)+k)/(1-a(1+k)) = k + a(1+k)²/(1-a(1+k))` is the rearranged `a(1+k)² = (a(1+k)+k) - k(1-a(1+k))`. -/
private lemma drift_arith {c d k a : ℝ} (ha1k : a * (1 + k) < 1)
    (hc : c ≤ a * (1 + k)) (hd : d ≤ k) :
    (c + d) / (1 - a * (1 + k)) ≤ k + a * (1 + k) ^ 2 / (1 - a * (1 + k)) := by
  have h1 : 0 < 1 - a * (1 + k) := by linarith
  have hnum : c + d ≤ a * (1 + k) + k := by linarith
  have h2 : (c + d) / (1 - a * (1 + k)) ≤ (a * (1 + k) + k) / (1 - a * (1 + k)) :=
    div_le_div_of_nonneg_right hnum h1.le
  refine le_trans h2 ?_
  have h3 : (a * (1 + k) + k) / (1 - a * (1 + k)) =
      k + a * (1 + k) ^ 2 / (1 - a * (1 + k)) := by
    field_simp
    ring
  rw [h3]

/-- **The one-step drift bound**: for the Taylor model `u ↦ u + A u² + E u` with
`‖E u‖ ≤ M ‖u‖³` on `‖u‖ ≤ ρ₁` (`A ≠ 0`), the Fatou coordinate `w(u) = -1/(A u)` satisfies
`‖w(u + A u² + E u) - w(u) - 1‖ ≤ κ + a(1+κ)²/(1 - a(1+κ))` with `a = ‖A‖ρ₁`,
`κ = Mρ₁/‖A‖`. -/
private lemma fatouW_drift_bound {A u Eu : ℂ} {M ρ₁ : ℝ}
    (hA : A ≠ 0) (hu : u ≠ 0) (hM : 0 ≤ M) (hρ₁ : 0 < ρ₁) (huρ : ‖u‖ ≤ ρ₁)
    (hEu : ‖Eu‖ ≤ M * ‖u‖ ^ 3)
    (hsmall : (‖A‖ * ρ₁) * (1 + M * ρ₁ / ‖A‖) < 1) :
    ‖-1 / (A * (u + A * u ^ 2 + Eu)) - (-1 / (A * u)) - 1‖ ≤
      M * ρ₁ / ‖A‖ + (‖A‖ * ρ₁) * (1 + M * ρ₁ / ‖A‖) ^ 2
        / (1 - (‖A‖ * ρ₁) * (1 + M * ρ₁ / ‖A‖)) := by
  have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hAne : ‖A‖ ≠ 0 := ne_of_gt hApos
  have hune : ‖u‖ ≠ 0 := ne_of_gt hupos
  -- bound on ε = Eu/u
  have he : ‖Eu / u‖ ≤ M * ‖u‖ ^ 2 := by
    rw [norm_div, div_le_iff₀ hupos]
    calc ‖Eu‖ ≤ M * ‖u‖ ^ 3 := hEu
      _ = M * ‖u‖ ^ 2 * ‖u‖ := by ring
  -- bound on x = A u + Eu/u
  have hx1 : ‖A * u + Eu / u‖ ≤ ‖A‖ * ‖u‖ + M * ‖u‖ ^ 2 := by
    calc ‖A * u + Eu / u‖ ≤ ‖A * u‖ + ‖Eu / u‖ := norm_add_le _ _
      _ = ‖A‖ * ‖u‖ + ‖Eu / u‖ := by rw [norm_mul]
      _ ≤ ‖A‖ * ‖u‖ + M * ‖u‖ ^ 2 := by linarith
  have hMuu : M * ‖u‖ ^ 2 ≤ ‖A‖ * ‖u‖ * (M * ρ₁ / ‖A‖) := by
    rw [show ‖A‖ * ‖u‖ * (M * ρ₁ / ‖A‖) = M * ‖u‖ * ρ₁ by field_simp; try ring]
    rw [show M * ‖u‖ ^ 2 = M * ‖u‖ * ‖u‖ by ring]
    exact mul_le_mul_of_nonneg_left huρ (by positivity)
  have hx2 : ‖A * u + Eu / u‖ ≤ ‖A‖ * ‖u‖ * (1 + M * ρ₁ / ‖A‖) := by
    have : ‖A‖ * ‖u‖ * (1 + M * ρ₁ / ‖A‖)
        = ‖A‖ * ‖u‖ + ‖A‖ * ‖u‖ * (M * ρ₁ / ‖A‖) := by ring
    rw [this]
    linarith
  have hxk : ‖A * u + Eu / u‖ ≤ (‖A‖ * ρ₁) * (1 + M * ρ₁ / ‖A‖) := by
    calc ‖A * u + Eu / u‖ ≤ ‖A‖ * ‖u‖ * (1 + M * ρ₁ / ‖A‖) := hx2
      _ ≤ (‖A‖ * ρ₁) * (1 + M * ρ₁ / ‖A‖) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left huρ hApos.le
  have hxlt : ‖A * u + Eu / u‖ < 1 := lt_of_le_of_lt hxk hsmall
  -- |1 + x| is bounded below
  have h1xge : 1 - ‖A * u + Eu / u‖ ≤ ‖1 + (A * u + Eu / u)‖ := by
    have h := norm_sub_le (1 + (A * u + Eu / u)) (A * u + Eu / u)
    have hz : (1 + (A * u + Eu / u)) - (A * u + Eu / u) = (1 : ℂ) := by ring
    rw [hz, norm_one] at h
    linarith
  have h1xpos : 0 < ‖1 + (A * u + Eu / u)‖ := by linarith
  have h1xne : 1 + (A * u + Eu / u) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h1xpos
    exact lt_irrefl 0 h1xpos
  have hden : 1 - (‖A‖ * ρ₁) * (1 + M * ρ₁ / ‖A‖) ≤ ‖1 + (A * u + Eu / u)‖ := by linarith
  have hdenpos : 0 < 1 - (‖A‖ * ρ₁) * (1 + M * ρ₁ / ‖A‖) := by linarith
  -- bound on w(u)·(Eu/u)
  have hwe : ‖(-1 / (A * u)) * (Eu / u)‖ ≤ M * ρ₁ / ‖A‖ := by
    have h1 : ‖-1 / (A * u)‖ = 1 / (‖A‖ * ‖u‖) := by
      rw [norm_div, norm_neg, norm_one, norm_mul]
    rw [norm_mul, h1]
    calc (1 / (‖A‖ * ‖u‖)) * ‖Eu / u‖ ≤ (1 / (‖A‖ * ‖u‖)) * (M * ‖u‖ ^ 2) :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ = M * ‖u‖ / ‖A‖ := by field_simp; try ring
      _ ≤ M * ρ₁ / ‖A‖ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left huρ hM) hApos.le
  have hnum : ‖(A * u + Eu / u) + (-1 / (A * u)) * (Eu / u)‖ ≤
      (‖A‖ * ρ₁) * (1 + M * ρ₁ / ‖A‖) + M * ρ₁ / ‖A‖ := by
    calc ‖(A * u + Eu / u) + (-1 / (A * u)) * (Eu / u)‖
        ≤ ‖A * u + Eu / u‖ + ‖(-1 / (A * u)) * (Eu / u)‖ := norm_add_le _ _
      _ ≤ (‖A‖ * ρ₁) * (1 + M * ρ₁ / ‖A‖) + M * ρ₁ / ‖A‖ := by linarith
  -- the algebra and the norm bound
  have hexp := fatouW_step_expansion hA hu h1xne
  have hL : -1 / (A * (u + A * u ^ 2 + Eu)) - (-1 / (A * u)) - 1 =
      - ((A * u + Eu / u) + (-1 / (A * u)) * (Eu / u)) / (1 + (A * u + Eu / u)) := by
    rw [hexp]; ring
  rw [hL]
  calc ‖-((A * u + Eu / u) + (-1 / (A * u)) * (Eu / u)) / (1 + (A * u + Eu / u))‖
      ≤ ((‖A‖ * ρ₁) * (1 + M * ρ₁ / ‖A‖) + M * ρ₁ / ‖A‖) /
          (1 - (‖A‖ * ρ₁) * (1 + M * ρ₁ / ‖A‖)) := by
        rw [norm_div, norm_neg]
        exact div_le_div₀ (by positivity) hnum hdenpos hden
    _ ≤ M * ρ₁ / ‖A‖ + (‖A‖ * ρ₁) * (1 + M * ρ₁ / ‖A‖) ^ 2
          / (1 - (‖A‖ * ρ₁) * (1 + M * ρ₁ / ‖A‖)) :=
        drift_arith hsmall le_rfl le_rfl

/-- **P2 of the petal model** (`NOTES_LEAD_mandelbar_noncusp.md` §2.5): the repelling petal is
backward invariant under `F`, with a definite drift `δ` in the Fatou coordinate.

Hypotheses as in `petal_P1` (Taylor model `F (z₁+u) = z₁ + u + A u² + E u` with
`‖E u‖ ≤ M ‖u‖³` for `‖u‖ ≤ ρ₂`, `A ≠ 0`, `ρ₁ < ρ₂`, `a := ‖A‖ρ₁`, `κ := Mρ₁/‖A‖`, the smallness
`a (1+κ) < 1`, and the constants `(C1) κ + a(1+κ)²/(1 - a(1+κ)) ≤ 1 - δ`, `(C2) R ≥ 1/a`).

Conclusion: for `z ∈ ball z₁ ρ₁` with `F z ∈ petal z₁ A R`, one has `z ∈ petal z₁ A R` and
`Re (fatouW z₁ A z) ≤ Re (fatouW z₁ A (F z)) - δ`.

Proof: put `u = z - z₁` (so `‖u‖ ≤ ρ₁ < ρ₂`) and `u' = F z - z₁ = u (1 + A u + ε)`,
`ε = E u / u`; the same estimate as in `petal_P1` gives `w(u') = w(u) + 1 + η` with `‖η‖ ≤ η* ≤ 1 - δ`,
hence `Re w(u') ≥ Re w(u) + δ`, i.e. `Re w(u) ≤ Re w(u') - δ`.  If `F z ∈ petal z₁ A R`, then
`u' ≠ 0`, so `u ≠ 0` (and `z ≠ z₁`), and
`Re w(u) ≤ Re w(u') - δ < -R - δ < -R`, so `z ∈ petal z₁ A R`. -/
theorem petal_P2 {F E : ℂ → ℂ} {z₁ A : ℂ} {M ρ₁ ρ₂ δ R : ℝ}
    (hA : A ≠ 0) (hM : 0 ≤ M) (hρ₁ : 0 < ρ₁) (hρρ : ρ₁ < ρ₂) (hδ : 0 < δ)
    (hsmall : (‖A‖ * ρ₁) * (1 + M * ρ₁ / ‖A‖) < 1)
    (hmodel : ∀ u : ℂ, ‖u‖ ≤ ρ₂ → F (z₁ + u) = z₁ + u + A * u ^ 2 + E u)
    (hE : ∀ u : ℂ, ‖u‖ ≤ ρ₂ → ‖E u‖ ≤ M * ‖u‖ ^ 3)
    (hC1 : M * ρ₁ / ‖A‖ + (‖A‖ * ρ₁) * (1 + M * ρ₁ / ‖A‖) ^ 2
              / (1 - (‖A‖ * ρ₁) * (1 + M * ρ₁ / ‖A‖)) ≤ 1 - δ)
    (hC2 : 1 / (‖A‖ * ρ₁) ≤ R) :
    ∀ z : ℂ, z ∈ Metric.ball z₁ ρ₁ → F z ∈ Work.SeedCert.petal z₁ A R →
      z ∈ Work.SeedCert.petal z₁ A R ∧
        (Work.SeedCert.fatouW z₁ A z).re ≤ (Work.SeedCert.fatouW z₁ A (F z)).re - δ := by
  intro z hz hFz
  rw [Work.SeedCert.mem_petal] at hFz
  obtain ⟨hFne, hFre⟩ := hFz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have hρ₂pos : 0 < ρ₂ := lt_trans hρ₁ hρρ
  by_cases hzz : z = z₁
  · -- `z = z₁`: then `F z = z₁ ∉ petal`, contradicting the hypothesis
    exfalso
    subst hzz
    have h0mem : ‖(0 : ℂ)‖ ≤ ρ₂ := by simpa using hρ₂pos.le
    have hE0 : E 0 = 0 := by
      have h := hE 0 h0mem
      have h2 : ‖E 0‖ ≤ 0 := by simpa using h
      exact norm_le_zero_iff.mp h2
    have hmod := hmodel 0 h0mem
    simp only [add_zero, pow_two, mul_zero, hE0] at hmod
    exact hFne hmod
  · -- the interesting case
    set u : ℂ := z - z₁ with hu
    have hzu : z = z₁ + u := by rw [hu]; ring
    have hsub : z - z₁ = u := by rw [hzu]; ring
    have hu_ne : u ≠ 0 := by rw [← hsub]; exact sub_ne_zero.mpr hzz
    have hu_lt : ‖u‖ < ρ₁ := hz
    have hu_le : ‖u‖ ≤ ρ₁ := le_of_lt hu_lt
    have hu_le₂ : ‖u‖ ≤ ρ₂ := le_of_lt (lt_trans hu_lt hρρ)
    have hFz_eq : F z = z₁ + u + A * u ^ 2 + E u := by
      rw [hzu]
      exact hmodel u hu_le₂
    have hFsub : F z - z₁ = u + A * u ^ 2 + E u := by
      rw [hFz_eq]; ring
    have hwz : Work.SeedCert.fatouW z₁ A z = -1 / (A * u) := by
      simp only [Work.SeedCert.fatouW, hsub]
    have hwFz : Work.SeedCert.fatouW z₁ A (F z) = -1 / (A * (u + A * u ^ 2 + E u)) := by
      simp only [Work.SeedCert.fatouW, hFsub]
    have hdrift := fatouW_drift_bound (A := A) (u := u) (Eu := E u)
      hA hu_ne hM hρ₁ hu_le (hE u hu_le₂) hsmall
    have hη : ‖-1 / (A * (u + A * u ^ 2 + E u)) - (-1 / (A * u)) - 1‖
        ≤ 1 - δ := le_trans hdrift hC1
    have hη' : ‖Work.SeedCert.fatouW z₁ A (F z) - Work.SeedCert.fatouW z₁ A z - 1‖ ≤ 1 - δ := by
      rw [hwz, hwFz]; exact hη
    have hdecomp : (Work.SeedCert.fatouW z₁ A (F z)).re
        = (Work.SeedCert.fatouW z₁ A z).re + 1
          + (Work.SeedCert.fatouW z₁ A (F z) - Work.SeedCert.fatouW z₁ A z - 1).re := by
      simp only [Complex.sub_re, Complex.one_re]
      ring
    have hneg : -(‖Work.SeedCert.fatouW z₁ A (F z) - Work.SeedCert.fatouW z₁ A z - 1‖)
        ≤ (Work.SeedCert.fatouW z₁ A (F z) - Work.SeedCert.fatouW z₁ A z - 1).re := by
      have h := Complex.re_le_norm
        (-(Work.SeedCert.fatouW z₁ A (F z) - Work.SeedCert.fatouW z₁ A z - 1))
      rw [Complex.neg_re, norm_neg] at h
      linarith
    have hre : (Work.SeedCert.fatouW z₁ A z).re ≤ (Work.SeedCert.fatouW z₁ A (F z)).re - δ := by
      linarith
    refine ⟨?_, hre⟩
    rw [Work.SeedCert.mem_petal]
    exact ⟨hzz, by linarith⟩

end Work.SeedCertNum
