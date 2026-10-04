import Mathlib
import Submission.Work.Diff.EXT.evolX.srcStauDefs
import Submission.Work.Diff.EXT.evolX.ckt_sqFlow_jointSmoothAt
import Submission.Work.Diff.EXT.evolX.derivWithin_sqrt_eq_half

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `srcStau` is a correct model of the one-sided time derivative `dtOpD`

The explicit model operator

`srcStau Hf k τ F y = (1/2) • (if τ = 0 then ∂_τ(∂_σ (ckt (Hf σ) k F y)) ∣₀
                                        else ∂_σ (ckt (Hf σ) k F y) ∣_τ / τ)`

had been introduced (in `Work.Diff.EXT.evolX.srcConnVar_continuousAt_zero`) as the model of the
one-sided time-derivative operator

`dtOpD G t k F y = ∂_t⁺ (ckt (G ·) k F y)   (derivative within `Set.Ioi 0`)`

of the curvature tower along a Ricci flow `G` on `[0,T)`.  The identity proved here is that, for the
time-reparametrised family `Hf = cfq_sqFlow G = τ ↦ G (τ²)` and for **every** `t ∈ [0,T)`
(including the initial time `t = 0`, where the derivative is one-sided), the two operators agree on
every tuple of globally smooth fields:

`dtOpD G t k F = srcStau (cfq_sqFlow G) k (√t) F`.

The content is the chain rule `t = τ²`, `∂_σ (ckt (G (σ²)) k F) ∣_τ = 2τ · ∂_t (ckt (G t) k F) ∣_{τ²}`
at interior times `t > 0`, together with the "even function" computation at `τ = 0`: the family
`τ ↦ ckt (G (τ²)) k F y` is even and `C^∞` at `0`, so the one-sided derivative of
`s ↦ ckt (G s) k F y` at `0` is half its second `τ`-derivative at `0`
(`Work.Diff.EXT.evolX.derivWithin_sqrt_eq_half`).
-/

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set Filter

namespace Work.Diff.EXT.evolX

/-- **The `t`-slice of a jointly `C^∞` family.**  If `Φ : ℝ × M → ℝ` is jointly `C^∞` at
`(t₀, x)`, then `t ↦ Φ (t, x)` is `C^∞` at `t₀`. -/
theorem srcStau_slice_fst
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {Φ : ℝ × M → ℝ} {t₀ : ℝ} {x : M}
    (hΦ : Work.Diff.EXT.JointSmoothAt I M Φ t₀ x) :
    ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun t : ℝ => Φ (t, x)) t₀ := by
  have h2 : ContMDiffAt 𝓘(ℝ,ℝ) ((𝓘(ℝ,ℝ)).prod I) ∞ (fun t : ℝ => ((t, x) : ℝ × M)) t₀ :=
    contMDiffAt_id.prodMk contMDiffAt_const
  have h3 := hΦ.comp t₀ h2
  simpa only [Function.comp_def] using h3

/-- **The model `srcStau` at `τ = 0`.**  At the origin the `if`-branch defining `srcStau` is the
first one, giving half of the second `τ`-derivative of the tower family. -/
theorem srcStau_zero_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (Hf : ℝ → Submission.Diff.SMet I M) (k : ℕ)
    (F : Fin (k + 4) → Work.Diff.EXT.TField (I := I) (M := M)) (y : M) :
    srcStau Hf k 0 F y
      = (1/2) * deriv (deriv (fun σ : ℝ => Work.Diff.EXT.ckt (Hf σ) k F y)) 0 := by
  simp only [srcStau, ↓reduceIte]

theorem srcStau_eq_dtOpD
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) {G : ℝ → Submission.Diff.SMet I M} {T : ℝ}
    (hflow : Submission.Diff.IsRicciFlow G T) {k : ℕ} {t : ℝ} (ht : t ∈ Set.Ico 0 T)
    {F : Fin (k + 4) → Work.Diff.EXT.TField (I := I) (M := M)}
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) :
    (fun y : M => Work.Diff.EXT.dtOpD (I := I) (M := M) G t k F y)
      = fun y : M => Work.Diff.EXT.evolX.srcStau (Work.Diff.GE.cfq_sqFlow G) k (Real.sqrt t) F y := by
  funext y
  rw [Work.Diff.EXT.dtOpD]
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · -- ## The initial time `t = 0`
    rw [← h0]
    have hT : 0 < T := by rw [← h0] at ht; exact ht.2
    obtain ⟨ρ, hρpos, hρT⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ^ 2 < T :=
      ⟨Real.sqrt T / 2, by positivity, by
        rw [div_pow, Real.sq_sqrt hT.le]; nlinarith⟩
    -- joint smoothness of the reparametrised tower at `τ = 0`
    have hΨ : Work.Diff.EXT.JointSmoothAt I M
        (fun p : ℝ × M => Work.Diff.EXT.ckt (Work.Diff.GE.cfq_sqFlow G p.1) k F p.2) 0 y :=
      ckt_sqFlow_jointSmoothAt (I := I) (M := M) hLC hT hρpos hρT hflow
        ⟨by linarith, hρpos⟩ (y := y) (k := k) (U := F) (hU := hF)
    have hg : ContDiffAt ℝ ∞
        (fun σ : ℝ => Work.Diff.EXT.ckt (Work.Diff.GE.cfq_sqFlow G σ) k F y) 0 :=
      (srcStau_slice_fst (I := I) (M := M) hΨ).contDiffAt
    -- the tower family of `τ ↦ G (τ²)` is even
    have hev : ∀ τ : ℝ, (fun σ : ℝ => Work.Diff.EXT.ckt (Work.Diff.GE.cfq_sqFlow G σ) k F y) (-τ)
        = (fun σ : ℝ => Work.Diff.EXT.ckt (Work.Diff.GE.cfq_sqFlow G σ) k F y) τ := by
      intro τ; simp only [Work.Diff.GE.cfq_sqFlow, neg_sq]
    have hRA := derivWithin_sqrt_eq_half (g := fun σ : ℝ =>
        Work.Diff.EXT.ckt (Work.Diff.GE.cfq_sqFlow G σ) k F y) hg hev
    -- replace the even family by the flow family on `(0, ∞)`
    have hEqOn : Set.EqOn (fun s : ℝ => Work.Diff.EXT.ckt (G s) k F y)
        (fun s : ℝ => Work.Diff.EXT.ckt (Work.Diff.GE.cfq_sqFlow G (Real.sqrt s)) k F y)
        (Set.Ioi 0) := by
      intro s hs
      simp only [Work.Diff.GE.cfq_sqFlow]
      rw [Real.sq_sqrt (le_of_lt hs)]
    have hx : (fun s : ℝ => Work.Diff.EXT.ckt (G s) k F y) 0
        = (fun s : ℝ => Work.Diff.EXT.ckt (Work.Diff.GE.cfq_sqFlow G (Real.sqrt s)) k F y) 0 := by
      simp only [Work.Diff.GE.cfq_sqFlow, Real.sqrt_zero, pow_two, mul_zero]
    have htr := derivWithin_congr hEqOn hx
    rw [Real.sqrt_zero, srcStau_zero_eq, htr, hRA]
    ring
  · -- ## Interior times `t > 0`: the chain rule for `t = τ²`
    have hτne : Real.sqrt t ≠ 0 := by positivity
    have hτ2 : (Real.sqrt t)^2 = t := Real.sq_sqrt hpos.le
    have hfam : Work.Diff.EXT.JointSmoothAt I M
        (fun p : ℝ × M => Work.Diff.EXT.ckt (G p.1) k F p.2) t y :=
      Work.Diff.EXT.ckt_familySmoothAt (I := I) (M := M) hLC hflow ⟨hpos, ht.2⟩ (hU := hF)
    have haC : ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun s : ℝ => Work.Diff.EXT.ckt (G s) k F y) t :=
      srcStau_slice_fst (I := I) (M := M) hfam
    have ha : DifferentiableAt ℝ (fun s : ℝ => Work.Diff.EXT.ckt (G s) k F y) t :=
      haC.contDiffAt.differentiableAt (by simp)
    simp only [srcStau]
    rw [if_neg hτne]
    -- `t` is an interior point of `Ioi 0`, so the one-sided derivative is the derivative
    rw [derivWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hpos)]
    have hd2 : deriv (fun σ : ℝ => σ^2) (Real.sqrt t) = 2 * Real.sqrt t := by
      simpa using (hasDerivAt_pow 2 (Real.sqrt t)).deriv
    have ha' : DifferentiableAt ℝ (fun s : ℝ => Work.Diff.EXT.ckt (G s) k F y) ((Real.sqrt t)^2) := by
      rw [hτ2]; exact ha
    -- the chain rule: `(ckt (G (σ²)))' = (ckt (G s))'(σ²) · 2σ`
    have hcomp : deriv (fun σ : ℝ => Work.Diff.EXT.ckt (Work.Diff.GE.cfq_sqFlow G σ) k F y)
          (Real.sqrt t)
        = deriv (fun s : ℝ => Work.Diff.EXT.ckt (G s) k F y) ((Real.sqrt t)^2)
            * (2 * Real.sqrt t) := by
      have hcc : (fun σ : ℝ => Work.Diff.EXT.ckt (Work.Diff.GE.cfq_sqFlow G σ) k F y)
          = (fun s : ℝ => Work.Diff.EXT.ckt (G s) k F y) ∘ (fun σ : ℝ => σ^2) := rfl
      rw [hcc, deriv_comp (x := Real.sqrt t) (h := fun σ : ℝ => σ^2)
            (h₂ := fun s : ℝ => Work.Diff.EXT.ckt (G s) k F y)
            ha' (differentiableAt_pow 2 (x := Real.sqrt t)), hd2]
    rw [hcomp, hτ2]
    field_simp

end Work.Diff.EXT.evolX
