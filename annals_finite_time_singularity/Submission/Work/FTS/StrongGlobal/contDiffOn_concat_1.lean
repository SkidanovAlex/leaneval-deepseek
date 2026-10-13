import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongGlobal.junction_fderiv_eq
import Submission.Work.FTS.StrongGlobal.continuousAt_ite_le
import Submission.Work.FTS.StrongGlobal.exists_box_subset_slab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongGlobal

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fam)

set_option linter.unusedVariables false

noncomputable section

/-! ## The tool-kit of the junction

The junction lemma `contDiffOn_concat_1` is proved by localising at the junction hyperplane
`{τ = τ₀}`: the box `concatBox x y τ₀ ε` straddles it, the concatenation is differentiable at every
point of the box with the (explicit) derivative `concatStep`, and `concatStep` is continuous on the
box because its two branches `fderiv ℝ (uncurry3 G)` and `fderiv ℝ (uncurry3 H)` are continuous
there and agree at the hyperplane.  That agreement is the one genuinely two-sided ingredient,
`junction_fderiv_eq`: on the hyperplane the two families agree as *functions of `(z,θ)`*, hence so
do their `z`- and `θ`-partials, while their `τ`-partials agree by hypothesis. -/

/-- The open box centred at `(x,y,τ₀)` of half-width `ε`; in the fake-time variable it straddles
the junction hyperplane `{τ = τ₀}`. -/
def concatBox (x y τ₀ ε : ℝ) : Set P3 :=
  Set.Ioo (x - ε) (x + ε) ×ˢ Set.Ioo (y - ε) (y + ε) ×ˢ Set.Ioo (τ₀ - ε) (τ₀ + ε)

theorem concatBox_mono {x y τ₀ ε ε' : ℝ} (h : ε ≤ ε') :
    concatBox x y τ₀ ε ⊆ concatBox x y τ₀ ε' := by
  intro p hp
  simp only [concatBox, Set.mem_prod, Set.mem_Ioo] at hp ⊢
  obtain ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩, h3a, h3b⟩ := hp
  exact ⟨⟨by linarith, by linarith⟩, ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩⟩

theorem mem_concatBox {x y τ₀ ε : ℝ} (hε : 0 < ε) : (x, y, τ₀) ∈ concatBox x y τ₀ ε := by
  simp only [concatBox, Set.mem_prod, Set.mem_Ioo]
  exact ⟨⟨by linarith, by linarith⟩, ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩⟩

theorem isOpen_concatBox (x y τ₀ ε : ℝ) : IsOpen (concatBox x y τ₀ ε) := by
  simp only [concatBox]
  exact isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_Ioo)

/-- The piecewise fake-time derivative of the concatenation at the junction `τ₀`: the derivative
of the left piece `G` on the closed half `{τ ≤ τ₀}`, of the right piece `H` on `{τ₀ ≤ τ}`. -/
def concatStep (G H : Fam) (τ₀ : ℝ) : P3 → P3 →L[ℝ] ℝ :=
  fun p => if p.2.2 ≤ τ₀ then fderiv ℝ (uncurry3 G) p else fderiv ℝ (uncurry3 H) p

theorem concatStep_apply_le {G H : Fam} {τ₀ : ℝ} {p : P3} (h : p.2.2 ≤ τ₀) :
    concatStep G H τ₀ p = fderiv ℝ (uncurry3 G) p := by
  simp only [concatStep, ite_eq_left h]

theorem concatStep_apply_gt {G H : Fam} {τ₀ : ℝ} {p : P3} (h : τ₀ < p.2.2) :
    concatStep G H τ₀ p = fderiv ℝ (uncurry3 H) p := by
  simp only [concatStep, ite_eq_right (not_le.mpr h)]

/-- On the closed right half `{τ₀ ≤ τ}`, intersected with the open quadrant where the two families
are known to agree at `τ₀`, the concatenation agrees with `H`. -/
theorem eqOn_concat_right_quadrant {G H : Fam} {τ₀ a' b' : ℝ}
    (hval : ∀ z' θ', 0 < z' → 0 < θ' → θ' < Real.pi / 2 → G z' θ' τ₀ = H z' θ' τ₀) :
    EqOn (uncurry3 (concat G H τ₀)) (uncurry3 H)
      ({p : P3 | τ₀ ≤ p.2.2} ∩ slab a' b') := by
  intro p hp
  obtain ⟨hpτ, hps⟩ := hp
  simp only [Set.mem_ofPred_eq] at hpτ
  obtain ⟨hz, hθ0, hθ1, -, -⟩ := mem_slab.mp hps
  rcases lt_or_eq_of_le hpτ with hlt | heq
  · change concat G H τ₀ p.1 p.2.1 p.2.2 = H p.1 p.2.1 p.2.2
    rw [concat_apply_of_gt hlt]
  · have h1 : uncurry3 (concat G H τ₀) p = G p.1 p.2.1 τ₀ := by
      change concat G H τ₀ p.1 p.2.1 p.2.2 = G p.1 p.2.1 τ₀
      rw [concat_apply_of_le (le_of_eq heq.symm), heq.symm]
    have h2 : uncurry3 H p = H p.1 p.2.1 τ₀ := by
      change H p.1 p.2.1 p.2.2 = H p.1 p.2.1 τ₀
      rw [heq]
    rw [h1, h2]
    exact hval p.1 p.2.1 hz hθ0 hθ1

/-- **A junction point of the open quadrant is a `C¹` point of the concatenation.**  Both pieces
are `C¹` on open slabs containing the point (the junction time is interior to both), and they agree
at the junction in value and in fake-time derivative, so the concatenation is `C¹` there. -/
theorem contDiffAt_concat_junction {G H : Fam} {τ₀ a b a' b' : ℝ}
    (hG : ContDiffOn ℝ 1 (uncurry3 G) (slab a b))
    (hH : ContDiffOn ℝ 1 (uncurry3 H) (slab a' b'))
    (hGa : a < τ₀) (hGb : τ₀ < b) (hHa : a' < τ₀) (hHb : τ₀ < b')
    (hval : ∀ z' θ', 0 < z' → 0 < θ' → θ' < Real.pi / 2 → G z' θ' τ₀ = H z' θ' τ₀)
    (hder : ∀ z' θ', 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      deriv (fun s => G z' θ' s) τ₀ = deriv (fun s => H z' θ' s) τ₀)
    {x y : ℝ} (hx : 0 < x) (hy0 : 0 < y) (hy1 : y < Real.pi / 2) :
    ContDiffAt ℝ 1 (uncurry3 (concat G H τ₀)) (x, y, τ₀) := by
  obtain ⟨ε₁, hε₁pos, hε₁sub⟩ := exists_box_subset_slab (τ₀ := τ₀) hx hy0 hy1 hGa hGb
  obtain ⟨ε₂, hε₂pos, hε₂sub⟩ := exists_box_subset_slab (τ₀ := τ₀) hx hy0 hy1 hHa hHb
  let ε : ℝ := min ε₁ ε₂
  have hεpos : 0 < ε := lt_min hε₁pos hε₂pos
  have hεle₁ : ε ≤ ε₁ := min_le_left _ _
  have hεle₂ : ε ≤ ε₂ := min_le_right _ _
  let u : Set P3 := concatBox x y τ₀ ε
  have huopen : IsOpen u := isOpen_concatBox x y τ₀ ε
  have hqu : (x, y, τ₀) ∈ u := mem_concatBox hεpos
  have hu₁ : u ⊆ slab a b := fun p hp => hε₁sub (concatBox_mono hεle₁ hp)
  have hu₂ : u ⊆ slab a' b' := fun p hp => hε₂sub (concatBox_mono hεle₂ hp)
  -- differentiability of the two pieces at every point of the box
  have hXdiff : ∀ p ∈ u, DifferentiableAt ℝ (uncurry3 G) p := fun p hp =>
    (hG.contDiffAt ((isOpen_slab a b).mem_nhds (hu₁ hp))).differentiableAt one_ne_zero
  have hYdiff : ∀ p ∈ u, DifferentiableAt ℝ (uncurry3 H) p := fun p hp =>
    (hH.contDiffAt ((isOpen_slab a' b').mem_nhds (hu₂ hp))).differentiableAt one_ne_zero
  -- continuity of the two derivatives
  have hXcont : ContinuousOn (fderiv ℝ (uncurry3 G)) (slab a b) :=
    hG.continuousOn_fderiv_of_isOpen (isOpen_slab a b) le_rfl
  have hYcont : ContinuousOn (fderiv ℝ (uncurry3 H)) (slab a' b') :=
    hH.continuousOn_fderiv_of_isOpen (isOpen_slab a' b') le_rfl
  -- the two derivatives agree at the hyperplane points of the box
  have hJunc : ∀ p ∈ u, p.2.2 = τ₀ → fderiv ℝ (uncurry3 G) p = fderiv ℝ (uncurry3 H) p := by
    intro p hp hpτ
    obtain ⟨hpz, hpθ0, hpθ1, -, -⟩ := mem_slab.mp (hu₁ hp)
    have hpp : p = (p.1, p.2.1, τ₀) := by rw [← hpτ]
    have hGd : DifferentiableAt ℝ (uncurry3 G) (p.1, p.2.1, τ₀) := by
      have h : DifferentiableAt ℝ (uncurry3 G) p := hXdiff p hp
      rwa [hpp] at h
    have hHd : DifferentiableAt ℝ (uncurry3 H) (p.1, p.2.1, τ₀) := by
      have h : DifferentiableAt ℝ (uncurry3 H) p := hYdiff p hp
      rwa [hpp] at h
    have hJ := junction_fderiv_eq hpz hpθ0 hpθ1 hGd hHd hval hder
    rwa [hpp.symm] at hJ
  -- the within-derivatives: `concatStep` is a derivative of the concatenation on the box
  have hderiv : ∀ p ∈ u,
      HasFDerivWithinAt (uncurry3 (concat G H τ₀)) (concatStep G H τ₀ p) u p := by
    intro p hp
    rcases lt_trichotomy p.2.2 τ₀ with hlt | heq | hgt
    · -- strictly before the junction: the concatenation is `G` nearby
      have h1 : HasFDerivWithinAt (uncurry3 G) (fderiv ℝ (uncurry3 G) p) u p :=
        (hXdiff p hp).hasFDerivAt.hasFDerivWithinAt
      have h2 : (uncurry3 (concat G H τ₀)) =ᶠ[𝓝[u] p] (uncurry3 G) := by
        have hopen : IsOpen {q : P3 | q.2.2 < τ₀} := isOpen_lt (by fun_prop) continuous_const
        have hmem : u ∩ {q : P3 | q.2.2 < τ₀} ∈ 𝓝[u] p := by
          rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
          exact ⟨{q : P3 | q.2.2 < τ₀}, hopen.mem_nhds hlt, fun q hq => ⟨hq.2, hq.1⟩⟩
        filter_upwards [hmem] with q hq
        change concat G H τ₀ q.1 q.2.1 q.2.2 = G q.1 q.2.1 q.2.2
        rw [concat_apply_of_le (le_of_lt hq.2)]
      have h3 : uncurry3 (concat G H τ₀) p = uncurry3 G p := by
        change concat G H τ₀ p.1 p.2.1 p.2.2 = G p.1 p.2.1 p.2.2
        rw [concat_apply_of_le (le_of_lt hlt)]
      have h4 := h1.congr_of_eventuallyEq h2 h3
      rw [concatStep_apply_le (le_of_lt hlt)]
      exact h4
    · -- on the junction hyperplane: glue the two one-sided derivatives
      obtain ⟨hpz, hpθ0, hpθ1, -, -⟩ := mem_slab.mp (hu₁ hp)
      have hJ := hJunc p hp heq
      have hS : HasFDerivWithinAt (uncurry3 (concat G H τ₀)) (fderiv ℝ (uncurry3 G) p)
          {q : P3 | q.2.2 ≤ τ₀} p :=
        ((hXdiff p hp).hasFDerivAt.hasFDerivWithinAt).congr eqOn_concat_left
          (by change concat G H τ₀ p.1 p.2.1 p.2.2 = G p.1 p.2.1 p.2.2
              rw [concat_apply_of_le (le_of_eq heq)])
      have hT₁ : HasFDerivWithinAt (uncurry3 (concat G H τ₀)) (fderiv ℝ (uncurry3 H) p)
          ({q : P3 | τ₀ ≤ q.2.2} ∩ slab a' b') p := by
        refine ((hYdiff p hp).hasFDerivAt.hasFDerivWithinAt).congr
          (eqOn_concat_right_quadrant hval) ?_
        change concat G H τ₀ p.1 p.2.1 p.2.2 = H p.1 p.2.1 p.2.2
        rw [concat_apply_of_le (le_of_eq heq), heq]
        exact hval p.1 p.2.1 hpz hpθ0 hpθ1
      have hT : HasFDerivWithinAt (uncurry3 (concat G H τ₀)) (fderiv ℝ (uncurry3 G) p)
          {q : P3 | τ₀ ≤ q.2.2} p := by
        rw [← hJ] at hT₁
        refine hT₁.mono_of_mem_nhdsWithin ?_
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        exact ⟨slab a' b', (isOpen_slab a' b').mem_nhds (hu₂ hp), fun q hq => ⟨hq.2, hq.1⟩⟩
      have hunion : HasFDerivWithinAt (uncurry3 (concat G H τ₀)) (fderiv ℝ (uncurry3 G) p)
          ({q : P3 | q.2.2 ≤ τ₀} ∪ {q : P3 | τ₀ ≤ q.2.2}) p := hS.union hT
      have hcover : {q : P3 | q.2.2 ≤ τ₀} ∪ {q : P3 | τ₀ ≤ q.2.2} = univ := by
        ext q
        simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
        exact le_total q.2.2 τ₀
      rw [hcover, hasFDerivWithinAt_univ] at hunion
      rw [concatStep_apply_le (le_of_eq heq)]
      exact hunion.hasFDerivWithinAt
    · -- strictly after the junction: the concatenation is `H` nearby
      have h1 : HasFDerivWithinAt (uncurry3 H) (fderiv ℝ (uncurry3 H) p) u p :=
        (hYdiff p hp).hasFDerivAt.hasFDerivWithinAt
      have h2 : (uncurry3 (concat G H τ₀)) =ᶠ[𝓝[u] p] (uncurry3 H) := by
        have hopen : IsOpen {q : P3 | τ₀ < q.2.2} := isOpen_lt continuous_const (by fun_prop)
        have hmem : u ∩ {q : P3 | τ₀ < q.2.2} ∈ 𝓝[u] p := by
          rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
          exact ⟨{q : P3 | τ₀ < q.2.2}, hopen.mem_nhds hgt, fun q hq => ⟨hq.2, hq.1⟩⟩
        filter_upwards [hmem] with q hq
        change concat G H τ₀ q.1 q.2.1 q.2.2 = H q.1 q.2.1 q.2.2
        rw [concat_apply_of_gt hq.2]
      have h3 : uncurry3 (concat G H τ₀) p = uncurry3 H p := by
        change concat G H τ₀ p.1 p.2.1 p.2.2 = H p.1 p.2.1 p.2.2
        rw [concat_apply_of_gt hgt]
      have h4 := h1.congr_of_eventuallyEq h2 h3
      rw [concatStep_apply_gt hgt]
      exact h4
  -- `concatStep` is continuous on the box
  have hf'cont : ContinuousOn (concatStep G H τ₀) u := by
    intro p hp
    obtain ⟨hpz, hpθ0, hpθ1, -, -⟩ := mem_slab.mp (hu₁ hp)
    have hXc : ContinuousAt (fderiv ℝ (uncurry3 G)) p :=
      hXcont.continuousAt ((isOpen_slab a b).mem_nhds (hu₁ hp))
    have hYc : ContinuousAt (fderiv ℝ (uncurry3 H)) p :=
      hYcont.continuousAt ((isOpen_slab a' b').mem_nhds (hu₂ hp))
    rcases lt_trichotomy p.2.2 τ₀ with hlt | heq | hgt
    · have hev : concatStep G H τ₀ =ᶠ[𝓝[u] p] fderiv ℝ (uncurry3 G) := by
        have hopen : IsOpen {q : P3 | q.2.2 < τ₀} := isOpen_lt (by fun_prop) continuous_const
        have hmem : u ∩ {q : P3 | q.2.2 < τ₀} ∈ 𝓝[u] p := by
          rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
          exact ⟨{q : P3 | q.2.2 < τ₀}, hopen.mem_nhds hlt, fun q hq => ⟨hq.2, hq.1⟩⟩
        filter_upwards [hmem] with q hq
        rw [concatStep_apply_le (le_of_lt hq.2)]
      refine (hXc.continuousWithinAt).congr_of_eventuallyEq hev ?_
      rw [concatStep_apply_le (le_of_lt hlt)]
    · have heq' := hJunc p hp heq
      show ContinuousWithinAt
        (fun q : P3 => if q.2.2 ≤ τ₀ then fderiv ℝ (uncurry3 G) q else fderiv ℝ (uncurry3 H) q)
        u p
      exact (continuousAt_ite_le hXc hYc heq').continuousWithinAt
    · have hev : concatStep G H τ₀ =ᶠ[𝓝[u] p] fderiv ℝ (uncurry3 H) := by
        have hopen : IsOpen {q : P3 | τ₀ < q.2.2} := isOpen_lt continuous_const (by fun_prop)
        have hmem : u ∩ {q : P3 | τ₀ < q.2.2} ∈ 𝓝[u] p := by
          rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
          exact ⟨{q : P3 | τ₀ < q.2.2}, hopen.mem_nhds hgt, fun q hq => ⟨hq.2, hq.1⟩⟩
        filter_upwards [hmem] with q hq
        rw [concatStep_apply_gt hq.2]
      refine (hYc.continuousWithinAt).congr_of_eventuallyEq hev ?_
      rw [concatStep_apply_gt hgt]
  -- the `C¹`-characterisation at the junction point
  have hmain : ContDiffWithinAt ℝ ((0 : WithTop ℕ∞) + 1) (uncurry3 (concat G H τ₀)) univ
      (x, y, τ₀) := by
    rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt (𝕜 := ℝ) (n := (0 : WithTop ℕ∞))
      (f := uncurry3 (concat G H τ₀)) (s := univ) (x := (x, y, τ₀)) (by norm_num)]
    refine ⟨u, ?_, ?_, concatStep G H τ₀, hderiv, ?_⟩
    · rw [Set.insert_eq_of_mem (Set.mem_univ _), nhdsWithin_univ]
      exact huopen.mem_nhds hqu
    · intro h
      exact absurd h (by simp)
    · refine (contDiffWithinAt_zero hqu).mpr ⟨u, self_mem_nhdsWithin, ?_⟩
      rwa [Set.inter_self]
  exact hmain

/-- **The junction glue for the joint `C¹`-regularity of a concatenation of two pieces.**

Let `G` and `H` be two families, jointly `C¹` on the open slabs `(0,∞)×(0,π/2)×(a,b)` resp.
`(0,∞)×(0,π/2)×(a',b')` of fake time (`Work.FTS.StrongGlobal.slab a b`), the junction time `τ₀`
being interior to both slabs and `a ≤ a'`.  Assume

* `G` and `H` agree on the whole hyperplane `{τ = τ₀}` as functions of `(z,θ)` (`hval`), and
* their fake-time derivatives agree there (`hder`).

Then the concatenation `Work.FTS.StrongGlobal.concat G H τ₀` (`G` for `τ ≤ τ₀`, `H` for `τ > τ₀`)
is jointly `C¹` on the slab `(a',b')`.

Proof plan.  Off the hyperplane the concatenation agrees with `G` (if `τ < τ₀`) or with `H`
(if `τ > τ₀`) on a neighbourhood, and the relevant slab contains that neighbourhood, so
`ContDiffOn` follows from the corresponding hypothesis (`ContDiffOn.mono`); only the hyperplane
points of the slab are at issue.  Fix such a point `q = (z,θ,τ₀)`.  Take
`u := Metric.ball q ε ∩ (Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2) ×ˢ Set.univ)` for `ε` small: then
`u ∈ 𝓝[insert q (slab a' b')] q` and `u ⊆` the set where the hypotheses on `(z',θ')` apply.
(i) the concatenation is differentiable at every point of `u`: off the hyperplane it is `G` or `H`
nearby; at a hyperplane point the spatial derivative of the concatenation is `∂G = ∂H` (the two
restrictions of `G` and `H` to the hyperplane are the same function by `hval`) and the fake-time
one-sided derivatives agree by `hder`, so `HasFDerivWithinAt.union` (on the two closed half spaces
`{τ ≤ τ₀}` and `{τ₀ ≤ τ}`) gives `HasFDerivAt`.
(ii) the chosen derivative function `f' := fderiv ℝ` of the concatenation is continuous at `q`,
because on either side it is `fderiv ℝ G` or `fderiv ℝ H`, both continuous at `q` with the same
value (again `hval` + `hder`).
Conclude with `contDiffWithinAt_succ_iff_hasFDerivWithinAt (n := 0)`
(`ContDiffWithinAt ℝ (0+1) f u q ↔ ∃ f', (∀ x ∈ u, HasFDerivWithinAt f (f' x) u x) ∧
ContDiffWithinAt ℝ 0 f' u q`) and `contDiffWithinAt_zero`, then `ContDiffWithinAt.mono`. -/
theorem contDiffOn_concat_1 {G H : Work.FTS.Galerkin.Fam} {τ₀ a b a' b' : ℝ}
    (hG : ContDiffOn ℝ 1 (Work.FTS.StrongGlobal.uncurry3 G) (Work.FTS.StrongGlobal.slab a b))
    (hH : ContDiffOn ℝ 1 (Work.FTS.StrongGlobal.uncurry3 H) (Work.FTS.StrongGlobal.slab a' b'))
    (ha : a ≤ a') (hGa : a < τ₀) (hGb : τ₀ < b)
    (hHa : a' < τ₀) (hHb : τ₀ < b')
    (hval : ∀ z' θ', 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      G z' θ' τ₀ = H z' θ' τ₀)
    (hder : ∀ z' θ', 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      deriv (fun s => G z' θ' s) τ₀ = deriv (fun s => H z' θ' s) τ₀) :
    ContDiffOn ℝ 1 (Work.FTS.StrongGlobal.uncurry3 (Work.FTS.StrongGlobal.concat G H τ₀))
      (Work.FTS.StrongGlobal.slab a' b') := by
  rw [(isOpen_slab a' b').contDiffOn_iff]
  intro p hp
  rcases p with ⟨x, y, τ⟩
  obtain ⟨hx, hy0, hy1, hτa, hτb⟩ := mem_slab.mp hp
  rcases lt_trichotomy τ τ₀ with hlt | heq | hgt
  · -- before the junction: the concatenation agrees with `G`
    have hp' : (x, y, τ) ∈ slab a b :=
      mem_slab.mpr ⟨hx, hy0, hy1, by linarith, by linarith⟩
    have hGat : ContDiffAt ℝ 1 (uncurry3 G) (x, y, τ) :=
      hG.contDiffAt ((isOpen_slab a b).mem_nhds hp')
    refine hGat.congr_of_eventuallyEq ?_
    have hopen : IsOpen {q : P3 | q.2.2 < τ₀} := isOpen_lt (by fun_prop) continuous_const
    filter_upwards [hopen.mem_nhds hlt] with q hq
    change concat G H τ₀ q.1 q.2.1 q.2.2 = G q.1 q.2.1 q.2.2
    rw [concat_apply_of_le (le_of_lt hq)]
  · -- at the junction
    subst heq
    exact contDiffAt_concat_junction hG hH hGa hGb hHa hHb hval hder hx hy0 hy1
  · -- after the junction: the concatenation agrees with `H`
    have hHat : ContDiffAt ℝ 1 (uncurry3 H) (x, y, τ) :=
      hH.contDiffAt ((isOpen_slab a' b').mem_nhds hp)
    refine hHat.congr_of_eventuallyEq ?_
    have hopen : IsOpen {q : P3 | τ₀ < q.2.2} := isOpen_lt continuous_const (by fun_prop)
    filter_upwards [hopen.mem_nhds hgt] with q hq
    change concat G H τ₀ q.1 q.2.1 q.2.2 = H q.1 q.2.1 q.2.2
    rw [concat_apply_of_gt hq]

end

end Work.FTS.StrongGlobal
