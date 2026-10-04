import Mathlib
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.Diff.STE.Lead.R_abs_le
import Submission.Work.Diff.STE.Lead.Rper_norm_le_of_R_abs_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A uniform sup bound for the periodised localised components `D.Rper i h a b`

The Layer B3 data `D` come with a uniform upper bound `C` for the chart volume densities on the
`σ`-balls (`Work.Diff.STE.B3.dens_bound_sigma`), and the localised component `D.R i h a b` is
`ψ i · √(dens i) · (chart matrix of h)` (`Work.Diff.STE.B3Data.R`), so its sup bound is controlled
by the sup bound of the chart matrix of `h` in the orthonormal frame `e i`
(`Work.Diff.STE.Lead.R_abs_le`); since `R i h a b` is supported in the open unit cube, the same
bound holds for its periodisation `D.Rper i h a b` (`Work.Diff.STE.Lead.Rper_norm_le_of_R_abs_le`).

It remains to pass from the *quadratic form* bounds
`lam · g₀(v,v) ≤ h(v,v) ≤ K · g₀(v,v)` (with `lam > 0`, `K ≥ 0`) to a bound on the *bilinear form*
`h`.  This is Cauchy–Schwarz for a symmetric positive semidefinite bilinear form, in the form proved
below (`bilin_abs_le_sqrt_aux`): for symmetric `B` with `B (w,w) ≥ 0` and `B (w,w) ≤ K G w` one has
`|B u v| ≤ K √(G u) √(G v)`. The proof uses the two vectors `b • u ± a • v` shifted by the *square
roots* `a = √(G u)`, `b = √(G v)`: the cross terms of the two associated quadratic forms are
`±2ab B u v`, whence `2ab |B u v| ≤ b² B u u + a² B v v ≤ 2 K a² b²`; dividing by `2ab` (the
degenerate case `ab = 0` forces `u = 0` or `v = 0` by positive definiteness of `G`) gives the claim.

Hence `‖D.Rper i h a b z‖ ≤ √C · K ≤ max (√C) 1 · (K+1)`, uniformly in `h`, `lam`, `K`, `i`, `a`,
`b` and `z` — which is the statement of `Rper_sup_bound`, with `U := max (√C) 1`.
-/

namespace Work.Diff.STE.Lead.GalTame

/-- **Cauchy–Schwarz for a symmetric positive semidefinite bilinear form**, in the *scaled* form
needed to pass from quadratic-form bounds to a bound on the bilinear form.

Let `V` be a real module, `B : V → V → ℝ` bilinear and symmetric, and let `G : V → ℝ` be positive
definite (in the sense `G w = 0 → w = 0`) and nonnegative.  If `B` is nonnegative as a quadratic
form and dominated by `K · G`, i.e. `B w w ≤ K * G w` for all `w`, with `K ≥ 0`, then

`|B u v| ≤ K * √(G u) * √(G v)`.

The bilinearity hypotheses are stated explicitly (as equalities of functions) so that the lemma
applies to any bilinear pairing, in particular to the `ℝ`-bilinear maps
`TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ` of `Work.Diff.STE.Bil`. -/
lemma bilin_abs_le_sqrt_aux {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V → V → ℝ)
    (Badd1 : ∀ u₁ u₂ v, B (u₁ + u₂) v = B u₁ v + B u₂ v)
    (Bsmul1 : ∀ (c : ℝ) u v, B (c • u) v = c * B u v)
    (Badd2 : ∀ u v₁ v₂, B u (v₁ + v₂) = B u v₁ + B u v₂)
    (Bsmul2 : ∀ (c : ℝ) u v, B u (c • v) = c * B u v)
    (hBsym : ∀ u v, B u v = B v u)
    {G : V → ℝ} (hGnn : ∀ w, 0 ≤ G w) (hGpos : ∀ w, G w = 0 → w = 0)
    (hBnn : ∀ w, 0 ≤ B w w)
    {K : ℝ} (hK : 0 ≤ K) (hub : ∀ w, B w w ≤ K * G w) :
    ∀ u v, |B u v| ≤ K * Real.sqrt (G u) * Real.sqrt (G v) := by
  intro u v
  set a : ℝ := Real.sqrt (G u) with ha
  set b : ℝ := Real.sqrt (G v) with hb
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have haa : a * a = G u := by rw [ha, ← sq]; exact Real.sq_sqrt (hGnn u)
  have hbb : b * b = G v := by rw [hb, ← sq]; exact Real.sq_sqrt (hGnn v)
  -- linearity in the two arguments for negated vectors
  have Bneg1 : ∀ x y : V, B (-x) y = - B x y := by intro x y; simpa using Bsmul1 (-1) x y
  have Bneg2 : ∀ x y : V, B x (-y) = - B x y := by intro x y; simpa using Bsmul2 (-1) x y
  -- the two associated quadratic forms, expanded
  have e1 : B (b • u + a • v) (b • u + a • v)
      = b * b * B u u + 2 * (a * b) * B u v + a * a * B v v := by
    simp only [Badd1, Badd2, Bsmul1, Bsmul2, hBsym v u]
    ring
  have e2 : B (b • u - a • v) (b • u - a • v)
      = b * b * B u u - 2 * (a * b) * B u v + a * a * B v v := by
    simp only [sub_eq_add_neg, Badd1, Badd2, Bsmul1, Bsmul2, Bneg1, Bneg2, hBsym v u]
    ring
  -- both are nonnegative, whence `2 a b |B u v| ≤ b² B u u + a² B v v`
  have key : 2 * (a * b) * |B u v| ≤ b * b * B u u + a * a * B v v := by
    have h1 : 0 ≤ B (b • u + a • v) (b • u + a • v) := hBnn _
    have h2 : 0 ≤ B (b • u - a • v) (b • u - a • v) := hBnn _
    rw [e1] at h1
    rw [e2] at h2
    have hab0 : 0 ≤ 2 * (a * b) := by positivity
    have h5 : |2 * (a * b) * B u v| ≤ b * b * B u u + a * a * B v v := by
      rw [abs_le]
      constructor <;> linarith
    rwa [abs_mul, abs_of_nonneg hab0] at h5
  -- the right-hand side is at most `2 K (ab)²`
  have step : 2 * (a * b) * |B u v| ≤ 2 * (a * b) * (K * (a * b)) := by
    calc 2 * (a * b) * |B u v| ≤ b * b * B u u + a * a * B v v := key
      _ ≤ b * b * (K * G u) + a * a * (K * G v) := by
          exact add_le_add (mul_le_mul_of_nonneg_left (hub u) (by positivity))
            (mul_le_mul_of_nonneg_left (hub v) (by positivity))
      _ = 2 * (a * b) * (K * (a * b)) := by rw [← haa, ← hbb]; ring
  by_cases hab : a * b = 0
  · -- degenerate case: one of `u`, `v` vanishes
    rcases mul_eq_zero.mp hab with ha' | hb'
    · have h0 : B 0 v = 0 := by simpa using Bsmul1 0 (0 : V) v
      have hGuu : G u = 0 := by rw [← haa, ha', mul_zero]
      have hu : u = 0 := hGpos u hGuu
      rw [hu, h0, abs_zero]
      positivity
    · have h0 : B u 0 = 0 := by simpa using Bsmul2 0 u 0
      have hGvv : G v = 0 := by rw [← hbb, hb', mul_zero]
      have hv : v = 0 := hGpos v hGvv
      rw [hv, h0, abs_zero]
      positivity
  · have habpos : 0 < a * b := lt_of_le_of_ne (mul_nonneg ha0 hb0) (Ne.symm hab)
    have h2ab : 0 < 2 * (a * b) := by linarith
    have hle : |B u v| ≤ K * (a * b) := le_of_mul_le_mul_left step h2ab
    simpa only [ha, hb, mul_assoc] using hle

theorem Rper_sup_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) :
    ∃ U : ℝ, 0 ≤ U ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M)) (lam K : ℝ), 0 < lam → 0 ≤ K →
        (∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u) →
        (∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v) →
        (∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v) →
        ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
          ‖D.Rper i h a b z‖ ≤ U * (K + 1) := by
  -- a uniform upper bound for the chart volume densities on the `σ`-balls
  obtain ⟨c, C, hc, hC, hdens⟩ := Work.Diff.STE.B3.dens_bound_sigma (I := I) (M := M) D
  refine ⟨max (Real.sqrt C) 1, le_trans (Real.sqrt_nonneg C) (le_max_left _ _), ?_⟩
  intro h lam K hlam hK hsymm hlow hhigh
  -- Cauchy–Schwarz: the quadratic-form bounds imply the bilinear bound `|h v w| ≤ K √ √`
  have hbound : ∀ (y : M) (u' v' : TangentSpace I y),
      |h y u' v'| ≤ K * Real.sqrt (g₀.inner y u' u') * Real.sqrt (g₀.inner y v' v') := by
    intro y u' v'
    have hGnn : ∀ w : TangentSpace I y, 0 ≤ g₀.inner y w w := by
      intro w
      rcases eq_or_ne w 0 with rfl | hw
      · simp
      · exact le_of_lt (g₀.pos y w hw)
    have hBnn : ∀ w : TangentSpace I y, 0 ≤ h y w w :=
      fun w => le_trans (mul_nonneg (le_of_lt hlam) (hGnn w)) (hlow y w)
    have hGpos : ∀ w : TangentSpace I y, g₀.inner y w w = 0 → w = 0 := by
      intro w hw
      by_contra hne
      exact (ne_of_gt (g₀.pos y w hne)) hw
    exact bilin_abs_le_sqrt_aux (fun u v => h y u v)
      (fun u₁ u₂ v => by rw [map_add, add_apply])
      (fun cc u v => by rw [map_smul, smul_apply, smul_eq_mul])
      (fun u v₁ v₂ => map_add (h y u) v₁ v₂)
      (fun cc u v => by rw [map_smul (h y u) cc v, smul_eq_mul])
      (fun u v => hsymm y u v) hGnn hGpos hBnn hK (fun w => hhigh y w) u' v'
  -- the sup bound of the localised component
  have hR : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (w : Fin (Module.finrank ℝ E) → ℝ), |D.R i h a b w| ≤ Real.sqrt C * K :=
    Work.Diff.STE.Lead.R_abs_le (I := I) (M := M) D h K C hK hC
      (fun i z hz => (hdens i z hz).2) hbound
  have hL : 0 ≤ Real.sqrt C * K := mul_nonneg (Real.sqrt_nonneg C) hK
  intro i a b z
  -- the same bound for the periodisation, and absorb `√C · K ≤ max (√C) 1 · (K+1)`
  have h1 := Work.Diff.STE.Lead.Rper_norm_le_of_R_abs_le (I := I) (M := M) D h i a b hL
    (fun w => hR i a b w) z
  have hU0 : 0 ≤ max (Real.sqrt C) 1 := le_trans (Real.sqrt_nonneg C) (le_max_left _ _)
  have h2 : Real.sqrt C * K ≤ max (Real.sqrt C) 1 * (K + 1) := by
    have h3 : Real.sqrt C * K ≤ max (Real.sqrt C) 1 * K :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hK
    have h4 : max (Real.sqrt C) 1 * K ≤ max (Real.sqrt C) 1 * (K + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hU0
    linarith
  linarith

end Work.Diff.STE.Lead.GalTame
