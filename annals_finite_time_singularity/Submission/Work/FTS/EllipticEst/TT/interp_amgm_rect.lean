import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.TT.interpGammaDefs
import Submission.Work.Blocks.IMC.cs_integral_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-!
# `TT.interp_amgm_rect`

The weighted Cauchy–Schwarz ("AM–GM") inequality for two functions `P`, `Q` supported in a
rectangle `[A,B] × [c,d] ⊂ (0,∞) × (0,π/2)`:

```
∫_z∫_θ P Q w² σ_a  ≤  √( (∫_z∫_θ P² w² σ_a) (∫_z∫_θ Q² w² σ_a) )
```

with `w z = (1+z)²/z²` the radial weight and `σ_a(θ) = sin(2θ)^{2-γ(α)}` the angular weight
(`γ(α) = 1 + α/10`).

Because the two factors of the square root are nonnegative, this is Cauchy–Schwarz in `L²` for
the measure `dz dθ` restricted to the rectangle, applied to the two functions
`P · w · sin(2θ)^{(2-γ)/2}` and `Q · w · sin(2θ)^{(2-γ)/2}`, whose product is the left-hand
integrand and whose squares are the two right-hand integrands.  The iterated integrals over
`Iz = [0,∞)`, `Iθ = [0,π/2]` are converted into integrals over the product measure on the
rectangle by Fubini (`MeasureTheory.setIntegral_prod`), using the support hypothesis; both
continuity and hence integrability come from `ContinuousOn.integrableOn_compact`.
-/

/-- A function that vanishes on `T \ S` and whose restriction to `S` is integrable is integrable
on `T`. -/
private lemma integrableOn_of_supported {S T : Set (ℝ × ℝ)} {R : ℝ × ℝ → ℝ}
    (hSmeas : MeasurableSet S) (hTmeas : MeasurableSet T) (hST : S ⊆ T)
    (hSint : IntegrableOn R S (volume : Measure (ℝ × ℝ)))
    (hvan : ∀ p ∈ T, p ∉ S → R p = 0) :
    IntegrableOn R T (volume : Measure (ℝ × ℝ)) := by
  have hdiff : IntegrableOn R (T \ S) (volume : Measure (ℝ × ℝ)) :=
    (integrableOn_zero (s := T \ S) (μ := (volume : Measure (ℝ × ℝ)))).congr_fun
      (fun p hp => (hvan p hp.1 hp.2).symm) (hTmeas.diff hSmeas)
  have hun := hSint.union hdiff
  rwa [Set.union_sdiff_cancel hST] at hun

/-- Integrals over `T` and over `S` agree when the function vanishes on `T \ S` and `S ⊆ T`. -/
private lemma setIntegral_eq_of_supported {S T : Set (ℝ × ℝ)} {R : ℝ × ℝ → ℝ}
    (hTmeas : MeasurableSet T) (hST : S ⊆ T) (hvan : ∀ p ∈ T, p ∉ S → R p = 0) :
    ∫ p in T, R p = ∫ p in S, R p :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hTmeas hST (fun p hp => hvan p hp.1 hp.2)

theorem interp_amgm_rect {A B c d : ℝ} (hA : 0 < A) (hAB : A < B) (hc : 0 < c) (hcd : c < d)
    (hd : d < Real.pi / 2) {α : ℝ} (hα : 0 < α) (hα6 : α ≤ 1 / 4)
    {P Q : ℝ → ℝ → ℝ}
    (hPc : ContinuousOn (Function.uncurry P) (Set.Icc A B ×ˢ Set.Icc c d))
    (hPz : ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → P z θ = 0)
    (hQc : ContinuousOn (Function.uncurry Q) (Set.Icc A B ×ˢ Set.Icc c d))
    (hQz : ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → Q z θ = 0) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        P z θ * Q z θ * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.TT.sigA α θ)
      ≤ Real.sqrt ((∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (P z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.TT.sigA α θ)
        * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (Q z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.TT.sigA α θ)) := by
  -- The three functionals appearing in the statement.
  set I0 : ℝ := ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      P z θ * Q z θ * (Work.Spaces.w z) ^ 2 * sigA α θ with hI0
  set If : ℝ := ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (P z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sigA α θ with hIf
  set Ig : ℝ := ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Q z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sigA α θ with hIg
  -- The support rectangle `S`, and the quadrant `Iz × Iθ`.
  set S : Set (ℝ × ℝ) := Set.Icc A B ×ˢ Set.Icc c d with hS
  have hSmeas : MeasurableSet S := by
    rw [hS]; exact measurableSet_Icc.prod measurableSet_Icc
  have hScomp : IsCompact S := by
    rw [hS]; exact isCompact_Icc.prod isCompact_Icc
  have hIz : MeasurableSet Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]; exact measurableSet_Ici
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hTmeas : MeasurableSet (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := hIz.prod hIθ
  have hST : S ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
    intro p hp
    rw [hS] at hp
    rw [Work.Spaces.Iz, Work.Spaces.Iθ]
    simp only [Set.mem_prod, Set.mem_Icc, Set.mem_Ici] at hp ⊢
    exact ⟨le_trans hA.le hp.1.1, le_trans hc.le hp.2.1, le_trans hp.2.2 hd.le⟩
  -- The half exponent `(2-γ)/2`, which is nonnegative for `α ≤ 1/4`.
  set e : ℝ := (2 - Work.Spaces.gam α) / 2 with he
  have he0 : 0 ≤ e := by
    rw [he, Work.Spaces.gam]; linarith
  -- The two `L²` functions.
  let f : ℝ × ℝ → ℝ := fun p => P p.1 p.2 * Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ e
  let g : ℝ × ℝ → ℝ := fun p => Q p.1 p.2 * Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ e
  -- Continuity of the pieces on `S`.
  have hPcf : ContinuousOn (fun p : ℝ × ℝ => P p.1 p.2) S := hPc
  have hQcf : ContinuousOn (fun p : ℝ × ℝ => Q p.1 p.2) S := hQc
  have hcont_w : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) S := by
    show ContinuousOn (fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2) S
    refine ContinuousOn.div (((continuous_const.add continuous_fst).pow 2).continuousOn)
      ((continuous_fst.pow 2).continuousOn) ?_
    intro p hp
    rw [hS] at hp
    simp only [Set.mem_prod, Set.mem_Icc] at hp
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hA hp.1.1))
  have hcont_s : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ e) S :=
    (Real.continuous_sin.comp
      ((continuous_const : Continuous fun _ : ℝ × ℝ => (2 : ℝ)).mul continuous_snd)).continuousOn
      |>.rpow_const (fun x _ => Or.inr he0)
  have hcontf : ContinuousOn f S := by
    show ContinuousOn (fun p : ℝ × ℝ =>
      P p.1 p.2 * Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ e) S
    exact (hPcf.mul hcont_w).mul hcont_s
  have hcontg : ContinuousOn g S := by
    show ContinuousOn (fun p : ℝ × ℝ =>
      Q p.1 p.2 * Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ e) S
    exact (hQcf.mul hcont_w).mul hcont_s
  -- Integrability of the three integrands on the compact rectangle `S`.
  have hfgS : IntegrableOn (fun p : ℝ × ℝ => f p * g p) S (volume : Measure (ℝ × ℝ)) :=
    (hcontf.mul hcontg).integrableOn_compact hScomp
  have hf2S : IntegrableOn (fun p : ℝ × ℝ => f p ^ 2) S (volume : Measure (ℝ × ℝ)) :=
    (hcontf.pow 2).integrableOn_compact hScomp
  have hg2S : IntegrableOn (fun p : ℝ × ℝ => g p ^ 2) S (volume : Measure (ℝ × ℝ)) :=
    (hcontg.pow 2).integrableOn_compact hScomp
  -- Pointwise identities on the angular interval.
  have hpt_fg : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
      f (z, θ) * g (z, θ) = P z θ * Q z θ * (Work.Spaces.w z) ^ 2 * sigA α θ := by
    intro z θ hθ
    have hsq : ((Real.sin (2 * θ)) ^ e) ^ 2 = sigA α θ := by
      rw [he]; exact sin_rpow_half_sq (α := α) hθ
    have h1 : (P z θ * Work.Spaces.w z * (Real.sin (2 * θ)) ^ e)
          * (Q z θ * Work.Spaces.w z * (Real.sin (2 * θ)) ^ e)
        = P z θ * Q z θ * (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ e) ^ 2 := by
      ring
    change (P z θ * Work.Spaces.w z * (Real.sin (2 * θ)) ^ e)
          * (Q z θ * Work.Spaces.w z * (Real.sin (2 * θ)) ^ e)
        = P z θ * Q z θ * (Work.Spaces.w z) ^ 2 * sigA α θ
    rw [h1, hsq]
  have hpt_f2 : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
      (f (z, θ)) ^ 2 = (P z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sigA α θ := by
    intro z θ hθ
    have hsq : ((Real.sin (2 * θ)) ^ e) ^ 2 = sigA α θ := by
      rw [he]; exact sin_rpow_half_sq (α := α) hθ
    have h1 : (P z θ * Work.Spaces.w z * (Real.sin (2 * θ)) ^ e) ^ 2
        = (P z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ e) ^ 2 := by
      ring
    change (P z θ * Work.Spaces.w z * (Real.sin (2 * θ)) ^ e) ^ 2
        = (P z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sigA α θ
    rw [h1, hsq]
  have hpt_g2 : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
      (g (z, θ)) ^ 2 = (Q z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sigA α θ := by
    intro z θ hθ
    have hsq : ((Real.sin (2 * θ)) ^ e) ^ 2 = sigA α θ := by
      rw [he]; exact sin_rpow_half_sq (α := α) hθ
    have h1 : (Q z θ * Work.Spaces.w z * (Real.sin (2 * θ)) ^ e) ^ 2
        = (Q z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ e) ^ 2 := by
      ring
    change (Q z θ * Work.Spaces.w z * (Real.sin (2 * θ)) ^ e) ^ 2
        = (Q z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sigA α θ
    rw [h1, hsq]
  -- Vanishing on the complement of the rectangle.
  have hvanP : ∀ p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, p ∉ S → P p.1 p.2 = 0 := by
    intro p _ hpS
    by_cases h1 : p.1 ∈ Set.Icc A B
    · by_cases h2 : p.2 ∈ Set.Icc c d
      · exact absurd ⟨h1, h2⟩ hpS
      · exact hPz p.1 p.2 (Or.inr h2)
    · exact hPz p.1 p.2 (Or.inl h1)
  have hvanQ : ∀ p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, p ∉ S → Q p.1 p.2 = 0 := by
    intro p _ hpS
    by_cases h1 : p.1 ∈ Set.Icc A B
    · by_cases h2 : p.2 ∈ Set.Icc c d
      · exact absurd ⟨h1, h2⟩ hpS
      · exact hQz p.1 p.2 (Or.inr h2)
    · exact hQz p.1 p.2 (Or.inl h1)
  have hvan_fg : ∀ p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, p ∉ S → f p * g p = 0 := by
    intro p hp hpq
    change (P p.1 p.2 * Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ e)
        * (Q p.1 p.2 * Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ e) = 0
    rw [hvanP p hp hpq]
    simp
  have hvan_f2 : ∀ p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, p ∉ S → f p ^ 2 = 0 := by
    intro p hp hpq
    change (P p.1 p.2 * Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ e) ^ 2 = 0
    rw [hvanP p hp hpq]
    simp
  have hvan_g2 : ∀ p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, p ∉ S → g p ^ 2 = 0 := by
    intro p hp hpq
    change (Q p.1 p.2 * Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ e) ^ 2 = 0
    rw [hvanQ p hp hpq]
    simp
  -- Integrability on the quadrant, from integrability on the rectangle plus the support.
  have hfgT : IntegrableOn (fun p : ℝ × ℝ => f p * g p) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      (volume : Measure (ℝ × ℝ)) := integrableOn_of_supported hSmeas hTmeas hST hfgS hvan_fg
  have hf2T : IntegrableOn (fun p : ℝ × ℝ => f p ^ 2) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      (volume : Measure (ℝ × ℝ)) := integrableOn_of_supported hSmeas hTmeas hST hf2S hvan_f2
  have hg2T : IntegrableOn (fun p : ℝ × ℝ => g p ^ 2) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      (volume : Measure (ℝ × ℝ)) := integrableOn_of_supported hSmeas hTmeas hST hg2S hvan_g2
  -- Identification of the three functionals with the integrals over the rectangle.
  have hI0eq : I0 = ∫ p in S, f p * g p := by
    rw [hI0]
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          P z θ * Q z θ * (Work.Spaces.w z) ^ 2 * sigA α θ)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, f (z, θ) * g (z, θ) :=
          setIntegral_congr_fun hIz (fun z _ =>
            setIntegral_congr_fun hIθ (fun θ hθ => (hpt_fg z θ hθ).symm))
      _ = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, f p * g p :=
          (setIntegral_prod (fun p : ℝ × ℝ => f p * g p) hfgT).symm
      _ = ∫ p in S, f p * g p := setIntegral_eq_of_supported hTmeas hST hvan_fg
  have hIfeq : If = ∫ p in S, f p ^ 2 := by
    rw [hIf]
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (P z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sigA α θ)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (f (z, θ)) ^ 2 :=
          setIntegral_congr_fun hIz (fun z _ =>
            setIntegral_congr_fun hIθ (fun θ hθ => (hpt_f2 z θ hθ).symm))
      _ = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, f p ^ 2 :=
          (setIntegral_prod (fun p : ℝ × ℝ => f p ^ 2) hf2T).symm
      _ = ∫ p in S, f p ^ 2 := setIntegral_eq_of_supported hTmeas hST hvan_f2
  have hIgeq : Ig = ∫ p in S, g p ^ 2 := by
    rw [hIg]
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Q z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sigA α θ)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (g (z, θ)) ^ 2 :=
          setIntegral_congr_fun hIz (fun z _ =>
            setIntegral_congr_fun hIθ (fun θ hθ => (hpt_g2 z θ hθ).symm))
      _ = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, g p ^ 2 :=
          (setIntegral_prod (fun p : ℝ × ℝ => g p ^ 2) hg2T).symm
      _ = ∫ p in S, g p ^ 2 := setIntegral_eq_of_supported hTmeas hST hvan_g2
  -- Cauchy–Schwarz on the rectangle.
  have hcs := Work.Blocks.IMC.cs_integral_mul_le (volume.restrict S)
    (hcontf.aestronglyMeasurable hSmeas) (hcontg.aestronglyMeasurable hSmeas)
    (show Integrable (fun p : ℝ × ℝ => f p ^ 2) (volume.restrict S) from hf2S)
    (show Integrable (fun p : ℝ × ℝ => g p ^ 2) (volume.restrict S) from hg2S)
  rw [← hI0eq, ← hIfeq, ← hIgeq] at hcs
  -- The two square-root arguments are nonnegative.
  have hIf0 : 0 ≤ If := by
    rw [hIf]
    refine setIntegral_nonneg hIz (fun z _ =>
      setIntegral_nonneg hIθ (fun θ hθ => ?_))
    exact mul_nonneg (mul_nonneg (sq_nonneg (P z θ)) (sq_nonneg (Work.Spaces.w z)))
      (sigA_nonneg α θ hθ)
  calc I0 ≤ |I0| := le_abs_self I0
    _ ≤ Real.sqrt If * Real.sqrt Ig := hcs
    _ = Real.sqrt (If * Ig) := (Real.sqrt_mul hIf0 Ig).symm

end Work.FTS.EllipticEst.TT
