import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.BoseFixB1B.boxMarginDefs
import Submission.Work.BoseFixB1B.cutFun_lip
import Submission.Work.BoseFixB1B.cutFun_support_subset
import Submission.Work.BoseFixB1B.plateau_basic
import Submission.Work.BoseFixB1B.plateau_lip
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.exists_smoothCutoff` — the smooth cutoff of the sliding box

For the sliding box `B(u) = dlBox ℓ d u` there is a family `γ_δ` (`δ > 0`) of smooth
cutoffs which are `1` on the inner box `{x | boxMargin ℓ d u x ≥ δ}`, are supported in
`B(u)`, take values in `[0,1]`, and whose derivatives are bounded by `C/δ` with a constant
`C` independent of `δ`.

The construction is the product of six one-dimensional plateau factors
(`Submission.Work.BoseFixB1B.cutoffDefs`), the point being that
`{boxMargin ℓ d u · ≥ δ}` is *exactly* the product of the six slabs

  `|x i| ≤ ℓ/2 - δ`,  `|(x - (ℓd)•u) i| ≤ ℓd/2 - δ`,

so that each factor is `1` precisely on the corresponding slab and vanishes on its complement;
the derivative bound is then the sum of the six Lipschitz constants.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-! ### A Lipschitz constant for `Real.smoothTransition` -/

/-- **`Real.smoothTransition` is Lipschitz.**  `σ = Real.smoothTransition` is `0` on
`(-∞,0]`, `1` on `[1,∞)` and smooth, so it is Lipschitz with a constant `K` (any `K ≥ 1`
above the sup of `|σ'|` on `[0,1]` works).

Proof: `σ` agrees on `[0,1]` with `G := σ · (bump)` where `bump` is a `C^∞` bump function
equal to `1` on a neighbourhood of `[0,2]`; being smooth with compact support, `G` is
Lipschitz (`ContDiff.lipschitzWith_of_hasCompactSupport`).  This gives the Lipschitz bound
for `σ` on `[0,1]`, and outside `[0,1]` the claim follows from the constancy of `σ` there
(the "jump" from `0` to `1` happens over a distance `≥ 1`). -/
lemma smoothTransition_abs_sub_le :
    ∃ K : ℝ, 0 < K ∧
      ∀ x y : ℝ, |Real.smoothTransition y - Real.smoothTransition x| ≤ K * |y - x| := by
  let b : ContDiffBump (0 : ℝ) := ⟨2, 3, by norm_num, by norm_num⟩
  let G : ℝ → ℝ := fun t => Real.smoothTransition t * (b : ℝ → ℝ) t
  have hbrIn : b.rIn = 2 := rfl
  have hGcd : ContDiff ℝ (⊤ : ENat) G := Real.smoothTransition.contDiff.mul b.contDiff
  have hGsupp : HasCompactSupport G := b.hasCompactSupport.mul_left
  obtain ⟨K₀, hK₀⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hGsupp hGcd (by simp)
  have hagree : ∀ t ∈ Set.Icc (0:ℝ) 1, G t = Real.smoothTransition t := by
    intro t ht
    have hmem : t ∈ closedBall (0:ℝ) b.rIn := by
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le]
      rw [hbrIn]
      constructor <;> linarith [ht.1, ht.2]
    show Real.smoothTransition t * (b : ℝ → ℝ) t = Real.smoothTransition t
    rw [ContDiffBump.one_of_mem_closedBall b hmem, mul_one]
  have h01 : ∀ a b' : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b' → b' ≤ 1 →
      |Real.smoothTransition b' - Real.smoothTransition a| ≤ (K₀ : ℝ) * |b' - a| := by
    intro a b' ha0 ha1 hb0 hb1
    have h := hK₀.dist_le_mul a b'
    rw [hagree a ⟨ha0, ha1⟩, hagree b' ⟨hb0, hb1⟩, Real.dist_eq, Real.dist_eq] at h
    simpa [abs_sub_comm] using h
  set K₁ : ℝ := max (K₀ : ℝ) 1 with hK₁
  have hK₁pos : 0 < K₁ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hK₀le : (K₀ : ℝ) ≤ K₁ := le_max_left _ _
  have key : ∀ x y : ℝ, x ≤ y →
      |Real.smoothTransition y - Real.smoothTransition x| ≤ K₁ * |y - x| := by
    intro x y hxy
    have hmono : Real.smoothTransition x ≤ Real.smoothTransition y :=
      Real.smoothTransition.monotone hxy
    have hsub : 0 ≤ y - x := by linarith
    rw [abs_of_nonneg hsub, abs_of_nonneg (sub_nonneg.mpr hmono)]
    rcases le_or_gt y 0 with hy | hy
    · rw [Real.smoothTransition.zero_of_nonpos (le_trans hxy hy),
        Real.smoothTransition.zero_of_nonpos hy, sub_self]
      exact mul_nonneg (le_of_lt hK₁pos) hsub
    rcases le_or_gt 1 x with hx | hx
    · rw [Real.smoothTransition.one_of_one_le (le_trans hx hxy),
        Real.smoothTransition.one_of_one_le hx, sub_self]
      exact mul_nonneg (le_of_lt hK₁pos) hsub
    rcases le_or_gt 0 x with hx0 | hx0
    · rcases le_or_gt y 1 with hy1 | hy1
      · have h := h01 x y hx0 (le_of_lt hx) (le_of_lt hy) hy1
        have h2 : (K₀:ℝ) * |y - x| ≤ K₁ * (y - x) := by
          rw [abs_of_nonneg hsub]
          exact mul_le_mul_of_nonneg_right hK₀le hsub
        exact le_trans (le_trans (le_abs_self _) h) h2
      · have h := h01 x 1 hx0 (le_of_lt hx) (by norm_num) le_rfl
        have h1 : 1 - Real.smoothTransition x ≤ (K₀ : ℝ) * (1 - x) := by
          rw [Real.smoothTransition.one, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - x),
            abs_of_nonneg (by linarith [Real.smoothTransition.le_one x] :
              (0:ℝ) ≤ 1 - Real.smoothTransition x)] at h
          linarith
        rw [Real.smoothTransition.one_of_one_le (le_of_lt hy1)]
        have hA : (K₀:ℝ) * (1 - x) ≤ K₁ * (1 - x) :=
          mul_le_mul_of_nonneg_right hK₀le (by linarith)
        have hB : K₁ * (1 - x) ≤ K₁ * (y - x) :=
          mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hK₁pos)
        linarith
    · rcases le_or_gt y 1 with hy1 | hy1
      · have h := h01 0 y le_rfl (by norm_num) (le_of_lt hy) hy1
        rw [Real.smoothTransition.zero_of_nonpos (le_of_lt hx0)]
        have h1 : Real.smoothTransition y ≤ (K₀ : ℝ) * y := by
          have hz : |Real.smoothTransition y - Real.smoothTransition 0| =
              Real.smoothTransition y := by
            rw [Real.smoothTransition.zero, sub_zero,
              abs_of_nonneg (Real.smoothTransition.nonneg y)]
          have hy' : |y - 0| = y := by rw [sub_zero, abs_of_nonneg (le_of_lt hy)]
          rwa [hz, hy'] at h
        have hA : (K₀:ℝ) * y ≤ K₁ * y := mul_le_mul_of_nonneg_right hK₀le (le_of_lt hy)
        have hB : K₁ * y ≤ K₁ * (y - x) :=
          mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hK₁pos)
        linarith
      · rw [Real.smoothTransition.one_of_one_le (le_of_lt hy1),
          Real.smoothTransition.zero_of_nonpos (le_of_lt hx0), sub_zero]
        have h3 : (1:ℝ) ≤ y - x := by linarith
        have h4 : (1:ℝ) ≤ K₁ := le_max_right _ _
        calc (1:ℝ) = 1 * 1 := by ring
          _ ≤ K₁ * (y - x) := mul_le_mul h4 h3 zero_le_one (le_of_lt hK₁pos)
  refine ⟨K₁, hK₁pos, fun x y => ?_⟩
  rcases le_total x y with hxy | hyx
  · exact key x y hxy
  · calc |Real.smoothTransition y - Real.smoothTransition x|
        = |Real.smoothTransition x - Real.smoothTransition y| := abs_sub_comm ..
      _ ≤ K₁ * |x - y| := key y x hyx
      _ = K₁ * |y - x| := by rw [abs_sub_comm]

/-! ### The product structure of `cutFun` -/

/-- `cutFun` as a product of two three-fold products over `Fin 3`. -/
lemma cutFun_eq_prod (c : ℝ³) (f g : ℝ → ℝ) (x : ℝ³) :
    cutFun c f g x = (∏ i : Fin 3, f (x i)) * (∏ i : Fin 3, g ((x - c) i)) := by
  simp only [cutFun, Fin.prod_univ_three]
  ring

/-- `cutFun` of smooth factors is smooth. -/
lemma contDiff_cutFun {c : ℝ³} {f g : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ENat) f)
    (hg : ContDiff ℝ (⊤ : ENat) g) : ContDiff ℝ (⊤ : ENat) (cutFun c f g) := by
  rw [show cutFun c f g = fun x : ℝ³ => (∏ i : Fin 3, f (x i)) * (∏ i : Fin 3, g ((x - c) i))
      from funext fun x => cutFun_eq_prod c f g x]
  simp only [Fin.prod_univ_three]
  fun_prop

/-- `cutFun` of `[0,1]`-valued factors is `[0,1]`-valued. -/
lemma cutFun_Icc {c : ℝ³} {f g : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1)
    (hg : ∀ t, 0 ≤ g t ∧ g t ≤ 1) : ∀ x, 0 ≤ cutFun c f g x ∧ cutFun c f g x ≤ 1 := by
  intro x
  rw [cutFun_eq_prod]
  have hfn : 0 ≤ ∏ i : Fin 3, f (x i) := Finset.prod_nonneg fun i _ => (hf (x i)).1
  have hfp : (∏ i : Fin 3, f (x i)) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => (hf (x i)).1) (fun i _ => (hf (x i)).2)
  have hgn : 0 ≤ ∏ i : Fin 3, g ((x - c) i) := Finset.prod_nonneg fun i _ => (hg _).1
  have hgp : (∏ i : Fin 3, g ((x - c) i)) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => (hg _).1) (fun i _ => (hg _).2)
  refine ⟨mul_nonneg hfn hgn, ?_⟩
  have h := mul_le_mul hfp hgp hgn zero_le_one
  simpa using h

/-- `cutFun` of factors that are `1` on the inner slabs is `1` on the inner box. -/
lemma cutFun_eq_one {c : ℝ³} {A B δ : ℝ} {f g : ℝ → ℝ}
    (hf : ∀ t, |t| ≤ A - δ → f t = 1) (hg : ∀ t, |t| ≤ B - δ → g t = 1) :
    ∀ x, (∀ i, |x i| ≤ A - δ) → (∀ i, |(x - c) i| ≤ B - δ) → cutFun c f g x = 1 := by
  intro x h1 h2
  rw [cutFun_eq_prod, Finset.prod_eq_one (fun i _ => hf _ (h1 i)),
    Finset.prod_eq_one (fun i _ => hg _ (h2 i)), mul_one]

theorem exists_smoothCutoff {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∃ γ : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiff ℝ (⊤ : ENat) γ ∧
      tsupport γ ⊆ Submission.BoseGases.dlBox ℓ d u ∧
      (∀ x, 0 ≤ γ x ∧ γ x ≤ 1) ∧
      (∀ x, Work.BoseFixB1B.boxMargin ℓ d u x ≥ δ → γ x = 1) ∧
      (∀ x, ‖fderiv ℝ γ x‖ ≤ C / δ) := by
  obtain ⟨K, hKpos, hKlip⟩ := smoothTransition_abs_sub_le
  refine ⟨12 * K, by positivity, fun δ hδ => ?_⟩
  obtain ⟨hcd, hIcc, hzero, hone⟩ := plateau_basic (A := ℓ / 2) (δ := δ) hδ
  obtain ⟨hcd', hIcc', hzero', hone'⟩ := plateau_basic (A := ℓ * d / 2) (δ := δ) hδ
  refine ⟨cutFun ((ℓ * d) • u) (plateau (ℓ / 2) δ) (plateau (ℓ * d / 2) δ), ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness: a product of six smooth plateau factors
    exact contDiff_cutFun hcd hcd'
  · -- support: the plateau factors vanish outside the two cubes
    exact cutFun_support_subset u hzero hzero'
  · -- range: the factors are `[0,1]`-valued
    exact cutFun_Icc hIcc hIcc'
  · -- the factors are `1` on the inner slabs, i.e. on `{boxMargin · ≥ δ}`
    intro x hx
    apply cutFun_eq_one hone hone'
    · intro i
      have h1 := boxMargin_le_coord (ℓ := ℓ) (d := d) u x i
      have h2 := abs_nonneg (x i)
      show |x i| ≤ ℓ / 2 - δ
      linarith
    · intro i
      have h1 := boxMargin_le_transCoord (ℓ := ℓ) (d := d) u x i
      have h2 := abs_nonneg ((x - (ℓ * d) • u) i)
      show |(x - (ℓ * d) • u) i| ≤ ℓ * d / 2 - δ
      linarith
  · -- derivative bound: the Lipschitz constants of the six factors add
    intro x
    have hK0 : (0 : ℝ) ≤ K := le_of_lt hKpos
    have hLpos : 0 ≤ 2 * K / δ := by positivity
    have hb : ∀ t : ℝ, |plateau (ℓ / 2) δ t| ≤ 1 := fun t =>
      abs_le.mpr ⟨by linarith [(hIcc t).1], (hIcc t).2⟩
    have hb' : ∀ t : ℝ, |plateau (ℓ * d / 2) δ t| ≤ 1 := fun t =>
      abs_le.mpr ⟨by linarith [(hIcc' t).1], (hIcc' t).2⟩
    have hmain := cutFun_lip (c := (ℓ * d) • u) (f := plateau (ℓ / 2) δ)
      (g := plateau (ℓ * d / 2) δ) hLpos hLpos
      (plateau_lip (A := ℓ / 2) hK0 hKlip hδ)
      (plateau_lip (A := ℓ * d / 2) hK0 hKlip hδ) hb hb'
    refine norm_fderiv_le_of_lip' ℝ (by positivity : (0 : ℝ) ≤ 12 * K / δ)
      (Filter.Eventually.of_forall fun y => ?_)
    have h24 : (3 * (2 * K / δ) + 3 * (2 * K / δ)) = 12 * K / δ := by
      field_simp
      ring
    have h := hmain x y
    rw [h24] at h
    rwa [Real.norm_eq_abs]

end Work.BoseFixB1B
