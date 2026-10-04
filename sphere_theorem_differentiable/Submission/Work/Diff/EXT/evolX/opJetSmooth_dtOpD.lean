import Mathlib
import Submission.Work.Diff.EXT.jetSmoothDefs
import Submission.Work.Diff.EXT.ladderSrcDefs
import Submission.Work.Diff.EXT.ladderEfDefs
import Submission.Work.Diff.EXT.covK_familySmooth
import Submission.Work.Diff.EXT.ckt_step_aux
import Submission.Work.Diff.GE.continuous_flow_quantities
import Submission.Work.Diff.EXT.evolX.opJetSmooth_lapOpE
import Submission.Work.Diff.EXT.evolX.jointSmoothAt_tDeriv
import Submission.Work.Diff.EXT.evolX.jointSmoothAt_iteratedDeriv_two_tzero
import Submission.Work.Diff.EXT.evolX.ckt_sqFlow_jointSmoothAt
import Submission.Work.Diff.EXT.evolX.derivWithin_sqrt_eq_half

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# All the jets of the one-sided time-derivative operator `dtOpD` are `C^∞`

`Work.Diff.EXT.JetSmoothOp g K S x` is the condition under which `jetAll` is *linear* in a packed
operator `S` (`Work.Diff.EXT.jetAll_sub_of_JetSmoothOp`): for every jet order `l` and every tuple
`F` of smooth fields, the function `y ↦ jetAll g l K S F y` is mdifferentiable near `x`.

Here we discharge it for the **one-sided time-derivative operator of the curvature tower**

`Work.Diff.EXT.dtOpD G t k F y = ∂ₜ⁺ (ckt (G ·) k F y)`,

i.e. the `s`-derivative within `Set.Ioi 0` at the time `t` of the level-`k` tower along a Ricci flow
`G` on `[0,T)` (`Submission.Diff.IsRicciFlow G T`), for every `t ∈ Set.Ico 0 T` — including the
initial time `t = 0`, where the derivative is one-sided.

## The proof

Following the sibling `Work.Diff.EXT.evolX.opJetSmooth_lapOpE`, all the jets are `C^∞` as soon as
the *level-zero* operator maps smooth tuples to `C^∞` functions
(`Work.Diff.EXT.evolX.jetAll_contMDiff_of_base`, whose step `extStep_contMDiff` combines the
chain rule for the derivative of a `C^∞` function along a smooth field with the smoothness of the
Leibniz corrections `dirF g X v = ∇_X v` from the proved contract `LCSmooth`).  So only

`∀ F smooth, ContMDiff I 𝓘(ℝ,ℝ) ∞ (fun y ↦ dtOpD G t k F y)`

remains — the two cases of the statement.

* **Interior times** `t ∈ Ioo 0 T`: `Ioi 0 ∈ 𝓝 t`, so `dtOpD` is the honest two-sided derivative
  `deriv (fun s ↦ ckt (G s) k F y) t`.  The family `(s,y) ↦ ckt (G s) k F y` is jointly `C^∞` at
  `(t,y)` (`Work.Diff.EXT.ckt_familySmoothAt`) and the partial derivative of a jointly `C^∞`
  family is jointly `C^∞` (`Work.Diff.EXT.evolX.jointSmoothAt_tDeriv`); slicing in `y` gives the
  claim.

* **The initial time** `t = 0`: the metric family is only jointly smooth on the *half-open*
  interval `[0,T)`, where no two-sided `t`-derivative exists.  The remedy is the standard time
  reparametrisation `t = τ²`: the family `τ ↦ G (τ²)` is jointly `C^∞` on the *open* interval
  `(-ρ,ρ)` (`ρ² < T`, `Work.Diff.GE.cfq_jointSmooth_sqFlow`), so the tower
  `Ψ(τ,y) = ckt (G (τ²)) k F y` is jointly `C^∞` at `(0,y)`
  (`Work.Diff.EXT.evolX.ckt_sqFlow_jointSmoothAt`).  Since `Ψ` is *even* in `τ`, the one-sided
  derivative `∂_s⁺ (Ψ (√s, ·))` exists and equals half of the second `τ`-derivative of `Ψ` at
  `0` (`Work.Diff.EXT.evolX.derivWithin_sqrt_eq_half` — Taylor expansion of an even function),
  and that second derivative is a `C^∞` function of `y`
  (`Work.Diff.EXT.evolX.jointSmoothAt_iteratedDeriv_two_tzero`).  As `τ² = s` for `s ≥ 0`, the
  one-sided derivative of `s ↦ Ψ (√s, y)` at `0` is the one-sided derivative of
  `s ↦ ckt (G s) k F y` at `0`, i.e. `dtOpD G 0 k F y`.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Plumbing: the two slices of a jointly smooth family -/

/-- **The `y`-slice of a jointly smooth family.**  If `Φ : ℝ × M → ℝ` is jointly `C^∞` at
`(t₀, x)`, then `y ↦ Φ (t₀, y)` is `C^∞` at `x`. -/
theorem opjs_slice {Φ : ℝ × M → ℝ} {t₀ : ℝ} {x : M}
    (hΦ : JointSmoothAt I M Φ t₀ x) :
    ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun y : M => Φ (t₀, y)) x := by
  have h2 : ContMDiffAt I ((𝓘(ℝ,ℝ)).prod I) ∞ (fun y : M => ((t₀, y) : ℝ × M)) x :=
    contMDiffAt_const.prodMk contMDiffAt_id
  have h3 := hΦ.comp x h2
  simpa only [Function.comp_def] using h3

/-- **The `t`-slice of a jointly smooth family.**  If `Φ : ℝ × M → ℝ` is jointly `C^∞` at
`(t₀, x)`, then `t ↦ Φ (t, x)` is `C^∞` at `t₀`. -/
theorem opjs_slice_fst {Φ : ℝ × M → ℝ} {t₀ : ℝ} {x : M}
    (hΦ : JointSmoothAt I M Φ t₀ x) :
    ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun t : ℝ => Φ (t, x)) t₀ := by
  have h2 : ContMDiffAt 𝓘(ℝ,ℝ) ((𝓘(ℝ,ℝ)).prod I) ∞ (fun t : ℝ => ((t, x) : ℝ × M)) t₀ :=
    contMDiffAt_id.prodMk contMDiffAt_const
  have h3 := hΦ.comp t₀ h2
  simpa only [Function.comp_def] using h3

/-- **An even function has vanishing derivative at the origin.** -/
theorem opjs_deriv_neg_eq_zero {g : ℝ → ℝ} (he : ∀ τ : ℝ, g (-τ) = g τ) : deriv g 0 = 0 := by
  have hfun : (fun τ : ℝ => g (-τ)) = g := funext fun τ => he τ
  have h2 : deriv (fun τ : ℝ => g (-τ)) 0 = -deriv g 0 := by
    simpa using deriv_comp_neg (f := g) (x := (0 : ℝ))
  rw [hfun] at h2
  linarith

/-! ## The level-zero operator is `C^∞` on smooth tuples -/

/-- **The time-derivative operator is `C^∞` at interior times.**  For `t ∈ Ioo 0 T` the one-sided
derivative `dtOpD` is the honest two-sided derivative, and the tower family
`(s,y) ↦ ckt (G s) k F y` is jointly `C^∞` at `(t,y)` (`Work.Diff.EXT.ckt_familySmoothAt`), whose
partial `s`-derivative is jointly `C^∞` by `Work.Diff.EXT.evolX.jointSmoothAt_tDeriv`. -/
theorem opjs_dtOpD_contMDiffAt_pos
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) {G : ℝ → SMet I M} {T : ℝ}
    (hflow : IsRicciFlow G T) {t : ℝ} (ht : t ∈ Set.Ioo 0 T) {k : ℕ}
    {F : Fin (k + 4) → TField (I := I) (M := M)} (hF : ∀ i, SmoothF (F i)) (y : M) :
    ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun z : M => dtOpD (I := I) (M := M) G t k F z) y := by
  have hfam : JointSmoothAt I M (fun p : ℝ × M => ckt (G p.1) k F p.2) t y :=
    Work.Diff.EXT.ckt_familySmoothAt (I := I) (M := M) hLC hflow ht hF
  have hd : JointSmoothAt I M (fun p : ℝ × M => deriv (fun s : ℝ => ckt (G s) k F p.2) p.1) t y :=
    jointSmoothAt_tDeriv (I := I) (M := M) hfam
  refine (opjs_slice (I := I) (M := M) hd).congr_of_eventuallyEq ?_
  filter_upwards with z
  show derivWithin (fun s : ℝ => ckt (G s) k F z) (Set.Ioi 0) t
    = deriv (fun s : ℝ => ckt (G s) k F z) t
  exact derivWithin_of_mem_nhds (isOpen_Ioi.mem_nhds ht.1)

/-- **The time-derivative operator is `C^∞` at the initial time.**  The reparametrisation
`t = τ²` turns the half-open time interval `[0,T)` into the open interval `(-ρ,ρ)` (`ρ² < T`), on
which the tower family `Ψ (τ,y) = ckt (G (τ²)) k F y` is jointly `C^∞` at `(0,y)`; since `Ψ` is
even in `τ`, the one-sided derivative in `s = τ²` at `0` is half of the second `τ`-derivative of
`Ψ` at `0`, which is a `C^∞` function of `y`. -/
theorem opjs_dtOpD_contMDiffAt_zero
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) {G : ℝ → SMet I M} {T : ℝ}
    (hT : 0 < T) (hflow : IsRicciFlow G T) {k : ℕ}
    {F : Fin (k + 4) → TField (I := I) (M := M)} (hF : ∀ i, SmoothF (F i)) (y : M) :
    ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun z : M => dtOpD (I := I) (M := M) G 0 k F z) y := by
  obtain ⟨ρ, hρpos, hρT⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ^ 2 < T :=
    ⟨Real.sqrt T / 2, by positivity, by
      rw [div_pow, Real.sq_sqrt hT.le]; nlinarith⟩
  have hΨ : ∀ z : M, JointSmoothAt I M
      (fun p : ℝ × M => ckt (Work.Diff.GE.cfq_sqFlow G p.1) k F p.2) 0 z := fun z =>
    ckt_sqFlow_jointSmoothAt (I := I) (M := M) hLC hT hρpos hρT hflow
      ⟨by linarith, hρpos⟩ (y := z) (k := k) (U := F) (hU := hF)
  have hslice : ContMDiffAt I 𝓘(ℝ,ℝ) ∞
      (fun z : M => deriv (fun s : ℝ => deriv (fun τ : ℝ =>
        ckt (Work.Diff.GE.cfq_sqFlow G τ) k F z) s) 0) y :=
    jointSmoothAt_iteratedDeriv_two_tzero (I := I) (M := M) (hΨ y)
  refine (hslice.div_const 2).congr_of_eventuallyEq ?_
  filter_upwards with z
  set g : ℝ → ℝ := fun τ : ℝ => ckt (Work.Diff.GE.cfq_sqFlow G τ) k F z with hgdef
  have hg : ContDiffAt ℝ ∞ g 0 :=
    (opjs_slice_fst (I := I) (M := M) (hΨ z)).contDiffAt
  have hev : ∀ τ : ℝ, g (-τ) = g τ := by
    intro τ
    simp only [hgdef, Work.Diff.GE.cfq_sqFlow]
    rw [show (-τ) ^ 2 = τ ^ 2 from by ring]
  have hRA := derivWithin_sqrt_eq_half (g := g) hg hev
  have hEqOn : Set.EqOn (fun s : ℝ => ckt (G s) k F z) (fun s : ℝ => g (Real.sqrt s))
      (Set.Ioi 0) := by
    intro s hs
    simp only [hgdef, Work.Diff.GE.cfq_sqFlow]
    rw [Real.sq_sqrt (le_of_lt hs)]
  have hx : (fun s : ℝ => ckt (G s) k F z) 0 = (fun s : ℝ => g (Real.sqrt s)) 0 := by
    simp only [hgdef, Work.Diff.GE.cfq_sqFlow, Real.sqrt_zero, pow_two, mul_zero]
  have htr : derivWithin (fun s : ℝ => ckt (G s) k F z) (Set.Ioi 0) 0
      = derivWithin (fun s : ℝ => g (Real.sqrt s)) (Set.Ioi 0) 0 :=
    derivWithin_congr hEqOn hx
  have hder : deriv (deriv g) 0
      = deriv (fun s : ℝ => deriv (fun τ : ℝ =>
          ckt (Work.Diff.GE.cfq_sqFlow G τ) k F z) s) 0 := by
    rw [hgdef]
  show derivWithin (fun s : ℝ => ckt (G s) k F z) (Set.Ioi 0) 0
    = deriv (fun s : ℝ => deriv (fun τ : ℝ =>
        ckt (Work.Diff.GE.cfq_sqFlow G τ) k F z) s) 0 / 2
  rw [htr, hRA, hder]

/-- **The level-zero operator of the target is `C^∞` on smooth tuples**: for every smooth tuple
`F` of fields, the function `y ↦ dtOpD G t k F y` is `C^∞`. -/
theorem opjs_dtOpD_contMDiff
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) {G : ℝ → SMet I M} {T : ℝ}
    (hflow : IsRicciFlow G T) {t : ℝ} (ht : t ∈ Set.Ico 0 T) {k : ℕ}
    {F : Fin (k + 4) → TField (I := I) (M := M)} (hF : ∀ i, SmoothF (F i)) :
    ContMDiff I 𝓘(ℝ,ℝ) ∞ (fun z : M => dtOpD (I := I) (M := M) G t k F z) := by
  intro y
  rcases lt_or_eq_of_le ht.1 with hpos | h0
  · exact opjs_dtOpD_contMDiffAt_pos (I := I) (M := M) hLC hflow ⟨hpos, ht.2⟩ hF y
  · subst h0
    exact opjs_dtOpD_contMDiffAt_zero (I := I) (M := M) hLC ht.2 hflow hF y

/-! ## The target -/

/-- **All the jets of the one-sided time-derivative operator of the tower are mdifferentiable.**
Along a Ricci flow `G` on `[0,T)`, at every time `t ∈ [0,T)` (the initial time included, where the
time derivative is one-sided) and at every point `x`, the packed operator
`F ↦ ∂ₜ⁺ (ckt (G ·) k F x)` satisfies `Work.Diff.EXT.JetSmoothOp`: all its `jetAll`-jets are
mdifferentiable near `x`.  This is the condition under which `jetAll` is linear in the operator
(`Work.Diff.EXT.jetAll_sub_of_JetSmoothOp`), which is what the ladder step of the `k`-th order Shi
estimate uses to split the reaction into its two sources. -/
theorem opJetSmooth_dtOpD
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (k : ℕ) :
    ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
      ∀ t ∈ Set.Ico 0 T, ∀ x : M,
        Work.Diff.EXT.JetSmoothOp (I := I) (M := M) (G t) (k + 4)
          (Work.Diff.EXT.dtOpD (I := I) (M := M) G t k) x := by
  intro G T hflow t ht x
  have hLC : Submission.Diff.LCSmooth I M := Work.EXT.lcSmooth_noBoundary (I := I) (M := M)
  have hbase : ∀ F : Fin (k + 4) → TField (I := I) (M := M),
      (∀ i, SmoothF (F i)) → ContMDiff I 𝓘(ℝ,ℝ) ∞
        (fun y : M => dtOpD (I := I) (M := M) G t k F y) :=
    fun F hF => opjs_dtOpD_contMDiff (I := I) (M := M) hLC hflow ht hF
  have hj := jetAll_contMDiff_of_base (I := I) (M := M) hLC (G t)
    (S := dtOpD (I := I) (M := M) G t k) hbase
  filter_upwards with y
  intro l F hF
  exact (hj l F hF).contMDiffAt.mdifferentiableAt (by simp)

end Work.Diff.EXT.evolX
