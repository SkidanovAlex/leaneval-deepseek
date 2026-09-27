import Mathlib
import Submission.Work.Whitney.exists_addDoublePoint_both_signs_located
import Submission.Work.Whitney.SignCompare

/-!
# Inserting a double point of a chosen sign, in an oriented atlas

This is the first half of the endgame of Whitney's strong embedding theorem: given a smooth
immersion `f : M → ℝ^{2n}`, a *clean* chart `c` (smooth on its source, inverse smooth everywhere,
centred at a point whose value has no other preimage), the clean-ball data at a radius `R`, a
cut-off model with support radius `R` and deviation `δ`, and the tubular data `H, ρ, L`, one can
modify `f` inside the `R`-ball by *gluing the model in*, obtaining an immersion `f'` whose double
point set is that of `f` plus a single new (transverse) double point `(p', q')` with `‖c p'‖ < R`,
`‖c q'‖ < R`, and such that `f' = f` outside the ball (in particular on a neighbourhood of the two
preimages `p₁, p₂` of a pre-existing double point `P`).

The new point `(p', q')` comes with *opposite* signs in the two variants `fp`, `fm` of the
modification (`Work.Whitney.exists_addDoublePoint_both_signs_located`).  Reading the two signs in a
chart `c₃` of an oriented atlas containing the inserted points (via
`Work.Whitney.doubleDetC_transition` and the nonvanishing of the transition factor), exactly one of
the two variants makes `P` and `(p', q')` have opposite signs relative to the atlas
(`Work.Whitney.oppositeSign_or_of_neg`), so the insertion can be performed with a *chosen* sign.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology Filter

/-- Differentiability of a chart representation of a smooth map through a chart whose inverse is
smooth everywhere. -/
theorem differentiableAt_comp_chart_globally_smooth {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {g : M → EuclideanSpace ℝ (Fin (2 * n))}
    (hg : ∀ y : M, ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) g y)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hsymm : ∀ u : EuclideanSpace ℝ (Fin n),
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm u)
    (u : EuclideanSpace ℝ (Fin n)) :
    DifferentiableAt ℝ (fun v : EuclideanSpace ℝ (Fin n) => g (c.symm v)) u := by
  have h1 : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (g ∘ c.symm) u := (hg (c.symm u)).comp u (hsymm u)
  exact (contMDiffAt_iff_contDiffAt.mp h1).differentiableAt (by simp)

/-- Differentiability of the transition function `c ∘ c'.symm` at a point of the source of `c'`. -/
theorem differentiableAt_transition_of_globally_smooth {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (c c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hcsm : ∀ y : M, y ∈ c.source →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c y)
    (hc'symm : ∀ u : EuclideanSpace ℝ (Fin n), u ∈ c'.target →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c'.symm u)
    (p : M) (hp : p ∈ c.source) (hpd : p ∈ c'.source) :
    DifferentiableAt ℝ (fun v : EuclideanSpace ℝ (Fin n) => c (c'.symm v)) (c' p) := by
  have h1 : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (c ∘ c'.symm) (c' p) :=
    (hcsm (c'.symm (c' p)) (by rw [c'.left_inv hpd]; exact hp)).comp (c' p)
      (hc'symm (c' p) (c'.map_source hpd))
  exact (contMDiffAt_iff_contDiffAt.mp h1).differentiableAt (by simp)

/-- **Insertion of a transverse double point of a chosen sign.** -/
theorem exists_addDoublePoint_oriented {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ c.target)
    (hcsm : ∀ y : M, y ∈ c.source →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c y)
    (hsymm : ∀ u : EuclideanSpace ℝ (Fin n),
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm u)
    (R η : ℝ) (hR : 0 < R) (hη : 0 < η)
    (hclean : ∀ y : M, ‖c y‖ < R → ∀ z : M, f y = f z → z = y)
    (hsep : ∀ y z : M, ‖c y‖ < R →
      2 * R ≤ ‖c z‖ → f y ≠ f z → η ≤ ‖f y - f z‖)
    (hsrc : ∀ y : M, ‖c y‖ < 3 * R → y ∈ c.source)
    (hball : Metric.ball 0 (3 * R) ⊆ c.target)
    (β : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) (a b : Fin n → ℝ) (δ : ℝ)
    (hβc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hβimm : ∀ u, Function.Injective (fderiv ℝ β u))
    (hab : a ≠ b) (hβab : β a = β b)
    (hβuniq : ∀ u v, u ≠ v → β u = β v → (u = a ∧ v = b) ∨ (u = b ∧ v = a))
    (hδ : 0 < δ)
    (hβact : ∀ u, ‖u‖ < R → (β u).2 ≠ 0)
    (hβR : ∀ u, R ≤ ‖u‖ → β u = Work.Whitney.inclModel n u)
    (hβδ : ∀ u, ‖β u - Work.Whitney.inclModel n u‖ ≤ δ)
    (hdet : LinearMap.det (((fderiv ℝ β a).coprod (fderiv ℝ β b)).toLinearMap) ≠ 0)
    (hRa : ‖a‖ < R) (hRb : ‖b‖ < R)
    (H : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin (2 * n)))
    (hHc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H)
    (hHaxis : ∀ u, H (u, 0) = f (c.symm u))
    (ρ L : ℝ) (hρ : 0 < ρ) (hL : 0 < L)
    (hHinj : Set.InjOn H (Metric.ball 0 ρ))
    (hHimm : ∀ z ∈ Metric.ball 0 ρ, Function.Injective (fderiv ℝ H z))
    (hHLip : ∀ z ∈ Metric.ball 0 ρ, ∀ z' ∈ Metric.ball 0 ρ, ‖H z - H z'‖ ≤ L * ‖z - z'‖)
    (hρR : 2 * R + δ ≤ ρ) (hδLη : L * δ < η)
    (p₁ p₂ : M) (hfp : f p₁ = f p₂) (hpne : p₁ ≠ p₂)
    (hn₁ : ∀ᶠ y in 𝓝 p₁, R < ‖c y‖) (hn₂ : ∀ᶠ y in 𝓝 p₂, R < ‖c y‖)
    (A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))))
    (hA : Work.Whitney.IsOrientedAtlas A)
    (c₁ c₂ c₃ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc₁ : c₁ ∈ A) (hc₂ : c₂ ∈ A) (hc₃ : c₃ ∈ A)
    (hp₁ : p₁ ∈ c₁.source) (hp₂ : p₂ ∈ c₂.source)
    (hP : Work.Whitney.pairDet f c₁ c₂ p₁ p₂ ≠ 0)
    (hs₃ : ∀ y : M, ‖c y‖ < 3 * R → y ∈ c₃.source)
    (hc₃sm : ∀ y : M, y ∈ c₃.source →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c₃ y)
    (hc₃symm : ∀ u : EuclideanSpace ℝ (Fin n), u ∈ c₃.target →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c₃.symm u)
    (htrans : ∀ y : M, ‖c y‖ < 3 * R →
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => c (c₃.symm u)) (c₃ y)).det ≠ 0) :
    ∃ (f' : M → EuclideanSpace ℝ (Fin (2 * n))) (p' q' : M),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f' ∧
      (∀ y, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f' y)) ∧
      Work.Whitney.doubleSet f' = Work.Whitney.doubleSet f ∪ {(p', q'), (q', p')} ∧
      f' =ᶠ[𝓝 p₁] f ∧ f' =ᶠ[𝓝 p₂] f ∧
      Work.Whitney.OppositeSign A f' p₁ p₂ p' q' := by
  classical
  -- the region modified by the gluing
  have hUopen : IsOpen {y : M | ‖c y‖ < 3 * R} := by
    have hset : {y : M | ‖c y‖ < 3 * R} = c.source ∩ c ⁻¹' Metric.ball 0 (3 * R) := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Metric.mem_ball,
        dist_eq_norm, sub_zero]
      constructor
      · intro hy
        exact ⟨hsrc y hy, hy⟩
      · intro h
        exact h.2
    rw [hset]
    exact c.continuousOn_toFun.isOpen_inter_preimage c.open_source Metric.isOpen_ball
  have h0U : c.symm 0 ∈ {y : M | ‖c y‖ < 3 * R} := by
    show ‖c (c.symm 0)‖ < 3 * R
    rw [c.right_inv h0, norm_zero]
    linarith
  have hUsub : {y : M | ‖c y‖ < 3 * R} ⊆ c.source := fun y hy => hsrc y hy
  have hballU : Metric.ball 0 (3 * R) ⊆ c '' {y : M | ‖c y‖ < 3 * R} := by
    intro u hu
    have hu' : u ∈ c.target := hball hu
    refine ⟨c.symm u, ?_, c.right_inv hu'⟩
    show ‖c (c.symm u)‖ < 3 * R
    rw [c.right_inv hu']
    rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at hu
  obtain ⟨fp, fm, p', q', hfp_sm, hfm_sm, hfp_imm, hfm_imm, hfp_out, hfm_out,
    hp'lt, hq'lt, hfp_ds, hfm_ds, hfp_detC, hflip_c⟩ :=
    Work.Whitney.exists_addDoublePoint_both_signs_located hn f hf himm c h0 hcsm
      (fun u _ => hsymm u)
      _ hUopen h0U hUsub H hHc hHaxis ρ L hρ hL hHinj hHimm hHLip β hβc hβimm a b hab hβab
      hβuniq R δ η hR hδ hη hβact hβR hβδ hdet hRa hRb hρR hδLη hballU hsrc hclean hsep
  -- the inserted points lie in the chart and in the atlas chart
  have hp'src : p' ∈ c.source := hsrc p' (by linarith)
  have hq'src : q' ∈ c.source := hsrc q' (by linarith)
  have hp'₃ : p' ∈ c₃.source := hs₃ p' (by linarith)
  have hq'₃ : q' ∈ c₃.source := hs₃ q' (by linarith)
  -- the modification is the identity near the two preimages
  have heq₁p : fp =ᶠ[𝓝 p₁] f := hn₁.mono fun y hy => hfp_out y (le_of_lt hy)
  have heq₂p : fp =ᶠ[𝓝 p₂] f := hn₂.mono fun y hy => hfp_out y (le_of_lt hy)
  have heq₁m : fm =ᶠ[𝓝 p₁] f := hn₁.mono fun y hy => hfm_out y (le_of_lt hy)
  have heq₂m : fm =ᶠ[𝓝 p₂] f := hn₂.mono fun y hy => hfm_out y (le_of_lt hy)
  -- the transition factor, and the signs read in the atlas chart `c₃`
  set T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun u => c (c₃.symm u) with hT
  have hTp' : (fderiv ℝ T (c₃ p')).det ≠ 0 := htrans p' (by linarith)
  have hTq' : (fderiv ℝ T (c₃ q')).det ≠ 0 := htrans q' (by linarith)
  have htransp : Work.Whitney.doubleDetC fp c₃ p' q' =
      Work.Whitney.doubleDetC fp c p' q' * ((fderiv ℝ T (c₃ p')).det * (fderiv ℝ T (c₃ q')).det) :=
    Work.Whitney.doubleDetC_transition fp c c₃ p' q' hp'src hp'₃ hq'src hq'₃
      (Work.Whitney.differentiableAt_comp_chart_globally_smooth
        (fun y => hfp_sm y) c hsymm (c p'))
      (Work.Whitney.differentiableAt_comp_chart_globally_smooth
        (fun y => hfp_sm y) c hsymm (c q'))
      (Work.Whitney.differentiableAt_transition_of_globally_smooth c c₃ hcsm hc₃symm p' hp'src hp'₃)
      (Work.Whitney.differentiableAt_transition_of_globally_smooth c c₃ hcsm hc₃symm q' hq'src hq'₃)
  have htransm : Work.Whitney.doubleDetC fm c₃ p' q' =
      Work.Whitney.doubleDetC fm c p' q' * ((fderiv ℝ T (c₃ p')).det * (fderiv ℝ T (c₃ q')).det) :=
    Work.Whitney.doubleDetC_transition fm c c₃ p' q' hp'src hp'₃ hq'src hq'₃
      (Work.Whitney.differentiableAt_comp_chart_globally_smooth
        (fun y => hfm_sm y) c hsymm (c p'))
      (Work.Whitney.differentiableAt_comp_chart_globally_smooth
        (fun y => hfm_sm y) c hsymm (c q'))
      (Work.Whitney.differentiableAt_transition_of_globally_smooth c c₃ hcsm hc₃symm p' hp'src hp'₃)
      (Work.Whitney.differentiableAt_transition_of_globally_smooth c c₃ hcsm hc₃symm q' hq'src hq'₃)
  have hfactor : (fderiv ℝ T (c₃ p')).det * (fderiv ℝ T (c₃ q')).det ≠ 0 :=
    mul_ne_zero hTp' hTq'
  have hB : Work.Whitney.doubleDetC fp c₃ p' q' ≠ 0 := by
    rw [htransp]
    exact mul_ne_zero hfp_detC hfactor
  have hflip : Work.Whitney.doubleDetC fm c₃ p' q' = - Work.Whitney.doubleDetC fp c₃ p' q' := by
    rw [htransm, htransp, hflip_c]
    ring
  rcases Work.Whitney.oppositeSign_or_of_neg A f fp fm p₁ p₂ p' q' c₁ c₂ c₃ hc₁ hc₂ hc₃
    hp₁ hp₂ hp'₃ hq'₃ heq₁p heq₂p heq₁m heq₂m hP hB hflip with h | h
  · exact ⟨fp, p', q', hfp_sm, hfp_imm, hfp_ds, heq₁p, heq₂p, h⟩
  · exact ⟨fm, p', q', hfm_sm, hfm_imm, hfm_ds, heq₁m, heq₂m, h⟩

end Work.Whitney
