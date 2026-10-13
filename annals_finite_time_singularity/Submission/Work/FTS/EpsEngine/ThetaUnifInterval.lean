/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/ThetaUnifInterval.lean`

`Work.FTS.EpsEngine.ThetaUnifInterval`: the **uniform angular flatness** `ThetaUnif α k` passes to
the interval average `(z,θ) ↦ ∫_a^b H s z θ ds` of a family `s ↦ H s` of profiles smooth on the
open quadrant, provided the family is

* `C^∞` in `(z,θ)` on the open quadrant for every `s ∈ [0,T]` (`hsm`),
* a.e.-strongly measurable in `s` in every slot of order `≤ k` (`hmeas`),
* uniformly bounded in `s` in every slot of order `≤ k` on compacta of the open quadrant (`hsup`),

and satisfies the two `ε`-`δ` angular conditions `ht0`, `ht1` *uniformly in* `s ∈ [0,T]`.

`ThetaUnif α k f` is the pair of `ε`-`δ` conditions (`UnifTraceDefs`)

  `∀ θ → 0⁺, ∀ z > 0,  sin(2θ)^{1-γ} · (D_z^b D_θ^a f z θ)² ≤ ε'`,
  `∀ θ → (π/2)⁻, ∀ z > 0,  sin(2θ)^{1-γ} · (D_z^b D_θ^a f z θ)² ≤ ε'`,

*uniform in `z`*, for every slot `a + b ≤ k`.

## Proof

Two ingredients:

* **the exchange identity** `mixed j i (∫_s H s) = ∫_s mixed j i (H s)` at a point of the open
  quadrant, which is `PerzTools.mixed_intervalIntegral_eq_gen_restricted`; it needs a *single*
  constant bounding all slots of order `≤ k` on a compact box, whereas `hsup` supplies one
  constant *per slot*.  `hsup_uniform` (below) produces the uniform constant by summing the
  finitely many per-slot ones over the box;
* **the elementary averaging**: if `B · (g s)² ≤ εt` for every `s ∈ [a,b]`, then
  `|∫_a^b g| ≤ √(εt/B) · (b-a)`, so `B · (∫_a^b g)² ≤ εt · (b-a)²`; choosing
  `εt = ε' / (1 + (b-a)²)` gives `≤ ε'`.  The pointwise bound on `g s` comes from `ht0`/`ht1`
  (with the index swap `u ↦ p`, `v ↦ q`), the interval-`sup` bound is
  `intervalIntegral.norm_integral_le_of_norm_le_const`, and the arithmetic is `core_bound`.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EpsEngine.UnifTraceDefs
import Submission.Work.FTS.EpsEngine.PerzTools.mixed_intervalIntegral_eq_gen_restricted

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **From per-slot bounds on compacta to one bound for every slot.**  If every slot
`D_z^jD_θ^i` (`j + i ≤ k`) has its own bound on a compact `K ⊆ Q0`, uniform in `s ∈ [0,T]`, then a
single constant bounds *all* the slots on `K`.  (The slots are finitely many, so take the sum of
the constants; each individual constant is `≥ 0`, hence dominated by the sum.) -/
private theorem hsup_uniform {k : ℕ} {H : ℝ → ℝ → ℝ → ℝ} {T : ℝ}
    (hsup : ∀ (j i : ℕ), j + i ≤ k → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K,
        |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C) :
    ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C := by
  intro K hK hKQ
  classical
  have hnn : ∀ p ∈ (Finset.range (k + 1)).product (Finset.range (k + 1)),
      0 ≤ (if h : p.1 + p.2 ≤ k then Classical.choose (hsup p.1 p.2 h K hK hKQ) else 0) := by
    intro p _
    split_ifs with h
    · exact (Classical.choose_spec (hsup p.1 p.2 h K hK hKQ)).1
    · exact le_rfl
  refine ⟨∑ p ∈ (Finset.range (k + 1)).product (Finset.range (k + 1)),
      (if h : p.1 + p.2 ≤ k then Classical.choose (hsup p.1 p.2 h K hK hKQ) else 0),
    Finset.sum_nonneg hnn, ?_⟩
  intro s hs q hq j i hji
  have hmem : (j, i) ∈ (Finset.range (k + 1)).product (Finset.range (k + 1)) :=
    Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  have hle := Finset.single_le_sum
    (s := (Finset.range (k + 1)).product (Finset.range (k + 1)))
    (f := fun p : ℕ × ℕ =>
      if h : p.1 + p.2 ≤ k then Classical.choose (hsup p.1 p.2 h K hK hKQ) else 0)
    hnn hmem
  rw [dite_eq_left hji] at hle
  exact le_trans ((Classical.choose_spec (hsup j i hji K hK hKQ)).2 s hs q hq) hle

/-- **The exchange identity at a point of the open quadrant**, from the restricted-measurability
form `PerzTools.mixed_intervalIntegral_eq_gen_restricted`, with the uniform-in-slot compact
bounds supplied by `huni`. -/
private theorem exch_at {H : ℝ → ℝ → ℝ → ℝ} {T a b : ℝ} {k : ℕ}
    (haT : a ∈ Set.Icc (0 : ℝ) T) (hbT : b ∈ Set.Icc (0 : ℝ) T) (hab : a ≤ b)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (H s))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (huni : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C)
    {j i : ℕ} (hji : j + i ≤ k) {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
      = ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ := by
  obtain ⟨hz0, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
  have hboxQ : Set.Icc (z / 2) (z + 1) ×ˢ Set.Icc (θ / 2) ((θ + Real.pi / 2) / 2)
      ⊆ Work.FTS.EllipticEst.Q0 := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
    exact Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨by linarith [hq1.1], by linarith [hq2.1], by linarith [hq2.2, Real.pi_pos]⟩
  obtain ⟨C, hC0, hC⟩ := huni _ (isCompact_Icc.prod isCompact_Icc) hboxQ
  refine PerzTools.mixed_intervalIntegral_eq_gen_restricted (n := k) (C := C)
    (z₁ := z / 2) (z₂ := z + 1) (θ₁ := θ / 2) (θ₂ := (θ + Real.pi / 2) / 2)
    haT hbT hab hC0 ?_ hmeas ?_ hboxQ hji z θ ?_
  · intro s hs
    exact Work.FTS.EllipticEst.smoothOpen_of_forall (hsm s hs)
  · intro s hs j' i' hji' q hq
    exact hC s hs q hq j' i' hji'
  · exact Set.mem_prod.mpr ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith [Real.pi_pos]⟩⟩

/-- **The elementary averaging arithmetic.**  If `|x| ≤ √(εt/B)·L` with `B > 0`, `εt > 0`,
`L ≥ 0` and `εt·L² ≤ ε'`, then `B·x² ≤ ε'`.  (Here `x = ∫_a^b g` and `√(εt/B)` is the supremum
bound on `|g s|` coming from `B·(g s)² ≤ εt`.) -/
private lemma core_bound {B εt ε' x L : ℝ} (hB : 0 < B) (hεt : 0 < εt) (hL : 0 ≤ L)
    (hεtL : εt * L ^ 2 ≤ ε') (hx : |x| ≤ Real.sqrt (εt / B) * L) : B * x ^ 2 ≤ ε' := by
  have hM0 : 0 ≤ Real.sqrt (εt / B) := Real.sqrt_nonneg _
  have hMsq : Real.sqrt (εt / B) ^ 2 = εt / B := Real.sq_sqrt (le_of_lt (div_pos hεt hB))
  have hx2 : x ^ 2 ≤ (Real.sqrt (εt / B) * L) ^ 2 := by
    rw [← sq_abs x]
    exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  have h2 : B * x ^ 2 ≤ B * (Real.sqrt (εt / B) * L) ^ 2 :=
    mul_le_mul_of_nonneg_left hx2 (le_of_lt hB)
  have h3 : B * (Real.sqrt (εt / B) * L) ^ 2 = εt * L ^ 2 := by
    rw [mul_pow, hMsq]
    field_simp
  linarith [h2, h3]

/-- **Uniform angular flatness passes to the interval average.** -/
theorem ThetaUnifInterval {α T : ℝ} {k : ℕ} {a b : ℝ} (hT : 0 ≤ T)
    (haT : a ∈ Set.Icc (0 : ℝ) T) (hbT : b ∈ Set.Icc (0 : ℝ) T) (hab : a ≤ b)
    {H : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (H s))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hsup : ∀ (j i : ℕ), j + i ≤ k → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K,
        |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C)
    (ht0 : ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, 0 < θ → θ < δ → ∀ z : ℝ, 0 < z →
      ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ u v : ℕ, u + v ≤ k →
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed v u (H s) z θ) ^ 2 ≤ ε')
    (ht1 : ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, θ < Real.pi / 2 → Real.pi / 2 - δ < θ → ∀ z : ℝ, 0 < z →
      ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ u v : ℕ, u + v ≤ k →
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed v u (H s) z θ) ^ 2 ≤ ε') :
    Work.FTS.EpsEngine.ThetaUnif α k (fun z θ => ∫ s in a..b, H s z θ) := by
  have hL0 : 0 ≤ b - a := by linarith
  have h1L : (0 : ℝ) < 1 + (b - a) ^ 2 := by positivity
  have huni := hsup_uniform (k := k) (H := H) (T := T) hsup
  refine ⟨?_, ?_⟩
  · -- the `θ → 0⁺` end
    intro p q hpq ε' hε'
    obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := ht0 (ε' / (1 + (b - a) ^ 2)) (div_pos hε' h1L)
    refine ⟨min δ₀ (Real.pi / 4), lt_min hδ₀pos (by linarith [Real.pi_pos]), ?_⟩
    intro θ hθ0 hθδ z hz
    have hθδ₀ : θ < δ₀ := lt_of_lt_of_le hθδ (min_le_left _ _)
    have hθπ4 : θ < Real.pi / 4 := lt_of_lt_of_le hθδ (min_le_right _ _)
    have hθπ2 : θ < Real.pi / 2 := by linarith [Real.pi_pos]
    have hB : 0 < Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
      Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)) _
    rw [exch_at (k := k) (j := q) (i := p) haT hbT hab hsm hmeas huni (by omega : q + p ≤ k) ⟨hz, hθ0, hθπ2⟩]
    refine core_bound hB (div_pos hε' h1L) hL0 ?_ ?_
    · rw [div_mul_eq_mul_div, div_le_iff₀ h1L]
      nlinarith [sq_nonneg (b - a), hε'.le]
    · have hq : 0 ≤ (ε' / (1 + (b - a) ^ 2)) / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
        le_of_lt (div_pos (div_pos hε' h1L) hB)
      set M : ℝ := Real.sqrt ((ε' / (1 + (b - a) ^ 2))
        / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)) with hM
      have hpt : ∀ s ∈ Set.uIoc a b, ‖Work.Spaces.mixed q p (H s) z θ‖ ≤ M := by
        intro s hs
        rw [Set.uIoc_of_le hab] at hs
        have hsT : s ∈ Set.Icc (0 : ℝ) T :=
          ⟨le_trans haT.1 (le_of_lt hs.1), le_trans hs.2 hbT.2⟩
        have hh := hδ₀ θ hθ0 hθδ₀ z hz s hsT p q hpq
        rw [Real.norm_eq_abs, hM, Real.le_sqrt (abs_nonneg _) hq, sq_abs, le_div_iff₀ hB]
        linarith [hh]
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      rwa [Real.norm_eq_abs, hM, abs_of_nonneg hL0] at hnorm
  · -- the `θ → (π/2)⁻` end
    intro p q hpq ε' hε'
    obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := ht1 (ε' / (1 + (b - a) ^ 2)) (div_pos hε' h1L)
    refine ⟨min δ₀ (Real.pi / 4), lt_min hδ₀pos (by linarith [Real.pi_pos]), ?_⟩
    intro θ hθπ2 hθδ z hz
    have hθδ₀ : Real.pi / 2 - δ₀ < θ := by
      have h : Real.pi / 2 - δ₀ ≤ Real.pi / 2 - min δ₀ (Real.pi / 4) := by
        linarith [min_le_left δ₀ (Real.pi / 4)]
      linarith
    have hθ0 : 0 < θ := by
      have h : Real.pi / 2 - Real.pi / 4 ≤ Real.pi / 2 - min δ₀ (Real.pi / 4) := by
        linarith [min_le_right δ₀ (Real.pi / 4)]
      linarith [Real.pi_pos]
    have hB : 0 < Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
      Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)) _
    rw [exch_at (k := k) (j := q) (i := p) haT hbT hab hsm hmeas huni (by omega : q + p ≤ k) ⟨hz, hθ0, hθπ2⟩]
    refine core_bound hB (div_pos hε' h1L) hL0 ?_ ?_
    · rw [div_mul_eq_mul_div, div_le_iff₀ h1L]
      nlinarith [sq_nonneg (b - a), hε'.le]
    · have hq : 0 ≤ (ε' / (1 + (b - a) ^ 2)) / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
        le_of_lt (div_pos (div_pos hε' h1L) hB)
      set M : ℝ := Real.sqrt ((ε' / (1 + (b - a) ^ 2))
        / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)) with hM
      have hpt : ∀ s ∈ Set.uIoc a b, ‖Work.Spaces.mixed q p (H s) z θ‖ ≤ M := by
        intro s hs
        rw [Set.uIoc_of_le hab] at hs
        have hsT : s ∈ Set.Icc (0 : ℝ) T :=
          ⟨le_trans haT.1 (le_of_lt hs.1), le_trans hs.2 hbT.2⟩
        have hh := hδ₀ θ hθπ2 hθδ₀ z hz s hsT p q hpq
        rw [Real.norm_eq_abs, hM, Real.le_sqrt (abs_nonneg _) hq, sq_abs, le_div_iff₀ hB]
        linarith [hh]
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      rwa [Real.norm_eq_abs, hM, abs_of_nonneg hL0] at hnorm

end Work.FTS.EpsEngine
