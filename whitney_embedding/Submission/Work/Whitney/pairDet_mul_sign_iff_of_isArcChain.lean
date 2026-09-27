import Mathlib
import Submission.Work.Whitney.ArcFraming
import Submission.Work.Whitney.posTransitionAt_of_isArcChain
import Submission.Work.Whitney.oppositeSign_iff

/-!
# The sign of the framed comparison of two double points is independent of the charts

`Work.Whitney.OppositeType` (in `Submission/Work/Whitney/ArcFraming.lean`) compares two transverse
double points `(p₁,p₂)`, `(q₁,q₂)` of an immersion `f : M → ℝ^{2n}` *without* a global oriented
atlas: the charts `c₁, c₃` at `p₁, q₁` are joined by a chain of charts along an arc `γ₁` with
positive transitions (`Work.Whitney.IsArcChain`), and likewise `c₂, c₄` along `γ₂`, and the
comparison is the sign of `pairDet f c₁ c₂ p₁ p₂ * pairDet f c₃ c₄ q₁ q₂`.

This file proves that this sign depends only on the *chains*, not on the particular charts: if
`(c₁,c₃)` and `(c₁',c₃')` are both chains along `γ₁` and `(c₂,c₄)`, `(c₂',c₄')` both chains along
`γ₂`, then the two products have the same sign.

The two inputs are

* `posTransitionAt_iff_of_isArcChain` : the transport along an arc is *well defined* — the
  underlying induction `Work.Whitney.chainData_transport_aux` already yields the equivalence, only
  its one-directional wrapper `Work.Whitney.posTransitionAt_of_isArcChain` was packaged before;
* `pairDet_change_first_of_isSmoothChart`, `pairDet_change_second_of_isSmoothChart` : the
  change-of-chart formula for `pairDet`, in the chart-smooth form needed here (the versions in
  `Submission/Work/Whitney/oppositeSign_iff.lean` assume an oriented atlas, which does not exist on
  a non-orientable `M`).

Combining: replacing `c₁` by `c₁'` multiplies `pairDet f c₁ c₂ p₁ p₂` by the transition determinant
`det (D (c₁' ∘ c₁.symm) (c₁ p₁))`, and similarly for the other three charts, so
`pairDet f c₁ c₂ p₁ p₂ * pairDet f c₃ c₄ q₁ q₂`
`= (pairDet f c₁' c₂' p₁ p₂ * pairDet f c₃' c₄' q₁ q₂) * (A B C D)`
where `A B` are the two transition determinants at `p₁, p₂` and `C D` the two at `q₁, q₂`.  The
transport says `sign A = sign C` and `sign B = sign D`, hence `A B C D > 0` (none of the four is
zero because the two charts are smooth and meet at the point), and multiplying by a positive number
preserves both `0 < ·` and `· < 0`.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology Filter

set_option linter.unusedSectionVars false

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-! ## The transport along an arc, as an equivalence -/

/-- **Transport along an arc.**  Two chains of charts along the same continuous arc `γ` relate the
endpoint charts with the same sign.  This is the two-sided form of
`Work.Whitney.posTransitionAt_of_isArcChain`; the underlying induction
`Work.Whitney.chainData_transport_aux` already proves the equivalence. -/
theorem posTransitionAt_iff_of_isArcChain {γ : ℝ → M} (hγ : Continuous γ)
    {c d c' d' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (h : IsArcChain γ c d) (h' : IsArcChain γ c' d') :
    PosTransitionAt c c' (γ 0) ↔ PosTransitionAt d d' (γ 1) := by
  obtain ⟨N, hN, dd, t, h1⟩ := h
  obtain ⟨P, hP, ff, s, h2⟩ := h'
  exact chainData_transport_aux (N + P) N P hN hP γ hγ 0 1 c d c' d' dd t ff s le_rfl h1 h2

/-! ## Smoothness and differentiability bookkeeping -/

/-- The **first** chart of an arc chain is a smooth chart. -/
theorem isSmoothChart_left_of_isArcChain {γ : ℝ → M}
    {c d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} (h : IsArcChain γ c d) :
    IsSmoothChart c := by
  obtain ⟨N, hN, dd, t, hdata⟩ := h
  obtain ⟨ht0, htb, htmono, hdd0, hddN, hγa, hγb, hsm, hcov, hjunc⟩ := hdata
  rw [← hdd0]
  exact hsm 0

/-- The **last** chart of an arc chain is a smooth chart. -/
theorem isSmoothChart_right_of_isArcChain {γ : ℝ → M}
    {c d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} (h : IsArcChain γ c d) :
    IsSmoothChart d := by
  obtain ⟨N, hN, dd, t, hdata⟩ := h
  obtain ⟨ht0, htb, htmono, hdd0, hddN, hγa, hγb, hsm, hcov, hjunc⟩ := hdata
  rw [← hddN]
  exact hsm (Fin.last N)

/-- The chart representation `u ↦ f (c.symm u)` of a smooth map `f` through a smooth chart `c` is
differentiable at `c p` for `p` in the source of `c`. -/
theorem differentiableAt_comp_symm_of_isSmoothChart
    {f : M → EuclideanSpace ℝ (Fin (2 * n))}
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} (hc : IsSmoothChart c)
    {p : M} (hp : p ∈ c.source) :
    DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c.symm u)) (c p) := by
  have h1 : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f
      (c.symm (c p)) := by
    rw [c.left_inv hp]
    exact hf.contMDiffAt
  have h2 : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm (c p) :=
    hc.2.contMDiffAt (c.open_target.mem_nhds (c.map_source hp))
  exact (((ContMDiffAt.comp (x := c p) h1 h2).contDiffAt).differentiableAt (by simp))

/-! ## Change of chart for `pairDet`, without an oriented atlas -/

/-- **Change of the first chart.**  For two smooth charts `c, c'` containing `p`,
`pairDet f c c₂ p p₂` differs from `pairDet f c' c₂ p p₂` by the determinant of the transition
`c' ∘ c.symm` at `c p`.  (Chart-smooth companion of `Work.Whitney.pairDet_change_first`, which
requires an oriented atlas.) -/
theorem pairDet_change_first_of_isSmoothChart
    {f : M → EuclideanSpace ℝ (Fin (2 * n))}
    {c c' c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : IsSmoothChart c) (hc' : IsSmoothChart c') {p p₂ : M}
    (hp : p ∈ c.source) (hp' : p ∈ c'.source)
    (hdiff : DifferentiableAt ℝ
      (fun u : EuclideanSpace ℝ (Fin n) => f (c'.symm u)) (c' p)) :
    pairDet f c c₂ p p₂ = pairDet f c' c₂ p p₂ *
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => c' (c.symm u)) (c p)).det := by
  have hτ : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => c' (c.symm u)) (c p) :=
    chart_transition_differentiableAt hc hc' hp hp'
  have hval : c' (c.symm (c p)) = c' p := by rw [c.left_inv hp]
  have hevent : ∀ᶠ u in 𝓝 (c p), c.symm u ∈ c'.source :=
    (c.tendsto_symm hp).eventually (c'.open_source.mem_nhds hp')
  have hEE : (fun u : EuclideanSpace ℝ (Fin n) => f (c.symm u)) =ᶠ[𝓝 (c p)]
      (fun u => f (c'.symm u)) ∘ (fun u : EuclideanSpace ℝ (Fin n) => c' (c.symm u)) := by
    filter_upwards [hevent] with u hu
    simp only [Function.comp_apply]
    rw [c'.left_inv hu]
  have hchain : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c.symm u)) (c p) =
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c'.symm u)) (c' p)).comp
        (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => c' (c.symm u)) (c p)) := by
    rw [hEE.fderiv_eq]
    rw [fderiv_comp (c p) (by rw [hval]; exact hdiff) hτ, hval]
  rw [pairDet, pairDet]
  exact det_comp_coprod_left (Work.Projection.pairEquiv n) _ _ _ _ hchain

/-- **Change of the second chart.**  For two smooth charts `c₂, c₂'` containing `p₂`,
`pairDet f c c₂ p p₂` differs from `pairDet f c c₂' p p₂` by the determinant of the transition
`c₂' ∘ c₂.symm` at `c₂ p₂`.  (Chart-smooth companion of `Work.Whitney.pairDet_change_second`.) -/
theorem pairDet_change_second_of_isSmoothChart
    {f : M → EuclideanSpace ℝ (Fin (2 * n))}
    {c c₂ c₂' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc₂ : IsSmoothChart c₂) (hc₂' : IsSmoothChart c₂') {p p₂ : M}
    (hp₂ : p₂ ∈ c₂.source) (hp₂' : p₂ ∈ c₂'.source)
    (hdiff : DifferentiableAt ℝ
      (fun u : EuclideanSpace ℝ (Fin n) => f (c₂'.symm u)) (c₂' p₂)) :
    pairDet f c c₂ p p₂ = pairDet f c c₂' p p₂ *
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => c₂' (c₂.symm u)) (c₂ p₂)).det := by
  have hτ : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => c₂' (c₂.symm u)) (c₂ p₂) :=
    chart_transition_differentiableAt hc₂ hc₂' hp₂ hp₂'
  have hval : c₂' (c₂.symm (c₂ p₂)) = c₂' p₂ := by rw [c₂.left_inv hp₂]
  have hevent : ∀ᶠ u in 𝓝 (c₂ p₂), c₂.symm u ∈ c₂'.source :=
    (c₂.tendsto_symm hp₂).eventually (c₂'.open_source.mem_nhds hp₂')
  have hEE : (fun u : EuclideanSpace ℝ (Fin n) => f (c₂.symm u)) =ᶠ[𝓝 (c₂ p₂)]
      (fun u => f (c₂'.symm u)) ∘ (fun u : EuclideanSpace ℝ (Fin n) => c₂' (c₂.symm u)) := by
    filter_upwards [hevent] with u hu
    simp only [Function.comp_apply]
    rw [c₂'.left_inv hu]
  have hchain : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c₂.symm u)) (c₂ p₂) =
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c₂'.symm u)) (c₂' p₂)).comp
        (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => c₂' (c₂.symm u)) (c₂ p₂)) := by
    rw [hEE.fderiv_eq]
    rw [fderiv_comp (c₂ p₂) (by rw [hval]; exact hdiff) hτ, hval]
  rw [pairDet, pairDet]
  exact det_comp_coprod_right (Work.Projection.pairEquiv n) _ _ _ _ hchain

/-- Multiplication of a real number by a *positive* number preserves strict negativity. -/
private lemma mul_neg_iff_of_pos_right {a b : ℝ} (h : 0 < b) : (a * b < 0 ↔ a < 0) := by
  have key := mul_neg_iff (a := a) (b := b)
  constructor
  · intro hab
    rcases key.mp hab with h1 | h1
    · exact absurd h1.2 (not_lt.mpr (le_of_lt h))
    · exact h1.1
  · intro ha
    exact key.mpr (Or.inr ⟨ha, h⟩)

/-! ## The main statement -/

theorem pairDet_mul_sign_iff_of_isArcChain {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → EuclideanSpace ℝ (Fin (2 * n))}
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {γ₁ γ₂ : ℝ → M}
    (hγ₁ : Continuous γ₁) (hγ₂ : Continuous γ₂) {p₁ p₂ q₁ q₂ : M}
    (hp₁ : γ₁ 0 = p₁) (hq₁ : γ₁ 1 = q₁) (hp₂ : γ₂ 0 = p₂) (hq₂ : γ₂ 1 = q₂)
    {c₁ c₂ c₃ c₄ c₁' c₂' c₃' c₄' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (m₁ : p₁ ∈ c₁.source) (m₂ : p₂ ∈ c₂.source) (m₃ : q₁ ∈ c₃.source) (m₄ : q₂ ∈ c₄.source)
    (m₁' : p₁ ∈ c₁'.source) (m₂' : p₂ ∈ c₂'.source) (m₃' : q₁ ∈ c₃'.source)
    (m₄' : q₂ ∈ c₄'.source)
    (ha : Work.Whitney.IsArcChain γ₁ c₁ c₃) (hb : Work.Whitney.IsArcChain γ₂ c₂ c₄)
    (ha' : Work.Whitney.IsArcChain γ₁ c₁' c₃') (hb' : Work.Whitney.IsArcChain γ₂ c₂' c₄') :
    (0 < Work.Whitney.pairDet f c₁ c₂ p₁ p₂ * Work.Whitney.pairDet f c₃ c₄ q₁ q₂ ↔
      0 < Work.Whitney.pairDet f c₁' c₂' p₁ p₂ * Work.Whitney.pairDet f c₃' c₄' q₁ q₂) ∧
      (Work.Whitney.pairDet f c₁ c₂ p₁ p₂ * Work.Whitney.pairDet f c₃ c₄ q₁ q₂ < 0 ↔
        Work.Whitney.pairDet f c₁' c₂' p₁ p₂ * Work.Whitney.pairDet f c₃' c₄' q₁ q₂ < 0) := by
  -- smoothness of the eight charts
  have hc₁ : IsSmoothChart c₁ := isSmoothChart_left_of_isArcChain ha
  have hc₃ : IsSmoothChart c₃ := isSmoothChart_right_of_isArcChain ha
  have hc₂ : IsSmoothChart c₂ := isSmoothChart_left_of_isArcChain hb
  have hc₄ : IsSmoothChart c₄ := isSmoothChart_right_of_isArcChain hb
  have hc₁' : IsSmoothChart c₁' := isSmoothChart_left_of_isArcChain ha'
  have hc₃' : IsSmoothChart c₃' := isSmoothChart_right_of_isArcChain ha'
  have hc₂' : IsSmoothChart c₂' := isSmoothChart_left_of_isArcChain hb'
  have hc₄' : IsSmoothChart c₄' := isSmoothChart_right_of_isArcChain hb'
  -- differentiability of `f` through the four "new" charts
  have hd₁ : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c₁'.symm u))
      (c₁' p₁) := differentiableAt_comp_symm_of_isSmoothChart hf hc₁' m₁'
  have hd₂ : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c₂'.symm u))
      (c₂' p₂) := differentiableAt_comp_symm_of_isSmoothChart hf hc₂' m₂'
  have hd₃ : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c₃'.symm u))
      (c₃' q₁) := differentiableAt_comp_symm_of_isSmoothChart hf hc₃' m₃'
  have hd₄ : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c₄'.symm u))
      (c₄' q₂) := differentiableAt_comp_symm_of_isSmoothChart hf hc₄' m₄'
  -- the four transition determinants
  set A : ℝ := (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => c₁' (c₁.symm u)) (c₁ p₁)).det
    with hAdef
  set B : ℝ := (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => c₂' (c₂.symm u)) (c₂ p₂)).det
    with hBdef
  set C : ℝ := (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => c₃' (c₃.symm u)) (c₃ q₁)).det
    with hCdef
  set D : ℝ := (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => c₄' (c₄.symm u)) (c₄ q₂)).det
    with hDdef
  have hApt : (0 < A) ↔ PosTransitionAt c₁ c₁' p₁ := by rw [hAdef]; rfl
  have hBpt : (0 < B) ↔ PosTransitionAt c₂ c₂' p₂ := by rw [hBdef]; rfl
  have hCpt : (0 < C) ↔ PosTransitionAt c₃ c₃' q₁ := by rw [hCdef]; rfl
  have hDpt : (0 < D) ↔ PosTransitionAt c₄ c₄' q₂ := by rw [hDdef]; rfl
  -- the transport along the two arcs
  have htr₁ : PosTransitionAt c₁ c₁' p₁ ↔ PosTransitionAt c₃ c₃' q₁ := by
    have h := posTransitionAt_iff_of_isArcChain hγ₁ ha ha'
    rw [hp₁, hq₁] at h
    exact h
  have htr₂ : PosTransitionAt c₂ c₂' p₂ ↔ PosTransitionAt c₄ c₄' q₂ := by
    have h := posTransitionAt_iff_of_isArcChain hγ₂ hb hb'
    rw [hp₂, hq₂] at h
    exact h
  -- none of the four determinants vanishes
  have hAne : A ≠ 0 := by
    rw [hAdef]
    intro h0
    have h := det_transition_mul hc₁ hc₁' m₁ m₁'
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  have hBne : B ≠ 0 := by
    rw [hBdef]
    intro h0
    have h := det_transition_mul hc₂ hc₂' m₂ m₂'
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  have hCne : C ≠ 0 := by
    rw [hCdef]
    intro h0
    have h := det_transition_mul hc₃ hc₃' m₃ m₃'
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  have hDne : D ≠ 0 := by
    rw [hDdef]
    intro h0
    have h := det_transition_mul hc₄ hc₄' m₄ m₄'
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  -- the signs at the two ends of each arc agree
  have hsignAC : 0 < A * C := by
    have hiff : (0 < A) ↔ (0 < C) := hApt.trans (htr₁.trans hCpt.symm)
    rcases lt_or_gt_of_ne hAne with hlt | hgt
    · have hClt : C < 0 := by
        rcases lt_or_gt_of_ne hCne with h | h
        · exact h
        · exact absurd (hiff.mpr h) (not_lt.mpr (le_of_lt hlt))
      exact mul_pos_of_neg_of_neg hlt hClt
    · exact mul_pos hgt (hiff.mp hgt)
  have hsignBD : 0 < B * D := by
    have hiff : (0 < B) ↔ (0 < D) := hBpt.trans (htr₂.trans hDpt.symm)
    rcases lt_or_gt_of_ne hBne with hlt | hgt
    · have hDlt : D < 0 := by
        rcases lt_or_gt_of_ne hDne with h | h
        · exact h
        · exact absurd (hiff.mpr h) (not_lt.mpr (le_of_lt hlt))
      exact mul_pos_of_neg_of_neg hlt hDlt
    · exact mul_pos hgt (hiff.mp hgt)
  have hσ : 0 < A * B * C * D := by
    have : A * B * C * D = (A * C) * (B * D) := by ring
    rw [this]
    exact mul_pos hsignAC hsignBD
  -- the four change-of-chart identities
  have eq1 : pairDet f c₁ c₂ p₁ p₂ = pairDet f c₁' c₂ p₁ p₂ * A :=
    pairDet_change_first_of_isSmoothChart hc₁ hc₁' m₁ m₁' hd₁
  have eq2 : pairDet f c₁' c₂ p₁ p₂ = pairDet f c₁' c₂' p₁ p₂ * B :=
    pairDet_change_second_of_isSmoothChart hc₂ hc₂' m₂ m₂' hd₂
  have eq3 : pairDet f c₃ c₄ q₁ q₂ = pairDet f c₃' c₄ q₁ q₂ * C :=
    pairDet_change_first_of_isSmoothChart hc₃ hc₃' m₃ m₃' hd₃
  have eq4 : pairDet f c₃' c₄ q₁ q₂ = pairDet f c₃' c₄' q₁ q₂ * D :=
    pairDet_change_second_of_isSmoothChart hc₄ hc₄' m₄ m₄' hd₄
  have hL : pairDet f c₁ c₂ p₁ p₂ * pairDet f c₃ c₄ q₁ q₂ =
      (pairDet f c₁' c₂' p₁ p₂ * pairDet f c₃' c₄' q₁ q₂) * (A * B * C * D) := by
    rw [eq1, eq2, eq3, eq4]
    ring
  constructor
  · rw [hL, mul_pos_iff_of_pos_right hσ]
  · rw [hL, mul_neg_iff_of_pos_right hσ]

end Work.Whitney
