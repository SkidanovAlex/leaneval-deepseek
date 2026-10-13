/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H6Pair6Aux/Ip6DzAux` — auxiliary lemmas for `ip6_dz_self`

The target `Work.FTS.StrongPersist.H6Pair6Aux.ip6_dz_self` bounds the `ℋ⁶`-pairing of a
profile against one of its `D_z`-derivatives,

`|IP6 1 … 1 α (D_z f) f| ≤ C |f|_{ℋ⁶}²`.

The route is: the unfolding `TransportS.ip4_unfold_bound` bounds the pairing by `3^5·10^22`
times the *slot sum* `SlotSum α 6 (D_z f) f`, whose terms are the elementary pairings

`slotPairing ρ a b (D_z f) f = ∫_z ∫_θ ρ · D_z^bD_θ^a(D_z f) · D_z^bD_θ^a f`

over the slots `a + b ≤ 6` and the three leaf weights `ρ ∈ {w²sin(2θ)^{-η}, w²,
w²sin(2θ)^{-γ}}`.  On the open quadrant `D_z^bD_θ^a(D_z f) = D_z^{b+1}D_θ^a f`, so each slot
term is `∫_z∫_θ (w)²θ_w·(D_zV)·V` with `V = D_z^bD_θ^a f`; the radial integration by parts
(`dzSelf2d`, with the level-one form `dzSelf1d`) bounds it by `2∫_z∫_θ (w)²θ_w·V²` — and
`∫_z∫_θ (w)²θ_w V² ≤ HkSq α 6 f` by the domination of the slot weights by the summands of
`HkIntegrand α 6 f` (`intSlotLeHkSq`); for the slots with `a + b ≤ 5` the AM–GM inequality
suffices.

This file collects the auxiliary lemmas of that assembly.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.bt_aux
import Submission.Work.FTS.TransportS.Slots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- `sin(2θ) ≥ 0` for `θ ∈ Iθ`. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  have h1 : (0 : ℝ) ≤ 2 * θ := by linarith [hθ.1]
  have h2 : 2 * θ ≤ Real.pi := by linarith [hθ.2, Real.pi_pos]
  exact Real.sin_nonneg_of_mem_Icc ⟨h1, h2⟩

/-! ## The `z`-slices of a `SmoothOpen` function are smooth on the open half line -/

/-- If `f` is `C^∞` on the open quadrant, then for every `θ ∈ (0,π/2)` the `z`-slice
`z ↦ f z θ` is `C^n` on `(0,∞)`. -/
theorem SmoothOpen.slice {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) (n : ℕ) :
    ContDiffOn ℝ n (fun z => f z θ) (Set.Ioi 0) := by
  have h1 : ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0 := hf.forall n
  have h2 : ContDiffOn ℝ n (fun z : ℝ => (z, θ)) (Set.Ioi 0) :=
    contDiffOn_id.prodMk contDiffOn_const
  refine (h1.comp h2 ?_).congr (fun z _ => rfl)
  intro z hz
  exact ⟨hz, hθ.1, hθ.2⟩

/-! ## Monotonicity of the iterated integral over `Iz × Iθ` for nonnegative functions -/

/-- For nonnegative `A ≤ B` (the second inequality only a.e. in `θ`), the iterated integral of
`A` is bounded by that of `B`; only the radial marginal integrability of `B` and the a.e.
angular slice integrability of `B` are needed. -/
theorem int2_mono {A B : ℝ → ℝ → ℝ}
    (hAB : ∀ z, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), A z θ ≤ B z θ)
    (hA : ∀ z θ, 0 ≤ A z θ)
    (hBslice : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      IntegrableOn (fun θ => B z θ) Work.Spaces.Iθ)
    (hB : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, B z θ) Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, A z θ)
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, B z θ := by
  refine MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ => hA z θ) hB ?_
  filter_upwards [hBslice] with z hz
  exact MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun θ => hA z θ) hz (hAB z)

/-! ## The pure and mixed slot weights are summands of `HkIntegrand α 6 f` -/

/-- The pure `D_z`-slot weight at level six: for `θ ∈ Iθ`,
`w(z)² sin(2θ)^{-η} (D_z^i f)² ≤ HkIntegrand α 6 f`. -/
theorem sq_le_HkIntegrand_pure6 (α : ℝ) {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (i : ℕ) (hi : i ≤ 6) :
    (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.DzIter i f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have heq : (Work.Spaces.DzIter i f z θ * (Work.Spaces.w z
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.DzIter i f z θ) ^ 2 := by
    rw [Work.Spaces.sq_mul_div_rpow _ _ _ _ hs (ne_of_gt Work.Spaces.eta_pos)]
    ring
  have h := Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ i hi
  rwa [heq] at h

/-- The mixed slot weight at level six: for `1 ≤ i`, `i + j ≤ 6` and `θ ∈ Iθ`,
`w(z)² sin(2θ)^{-γ} (D_z^jD_θ^i f)² ≤ HkIntegrand α 6 f`. -/
theorem sq_le_HkIntegrand_mixed6 (α : ℝ) (hα : 0 < α) {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 6) :
    (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j i f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  have heq : (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j i f z θ) ^ 2 := by
    rw [mul_pow, Work.Spaces.bt_Wt_sq α z θ hα hθ]
    ring
  have h := Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ i j hi hij
  rwa [heq] at h

/-! ## The shift of a slot pairing in its first argument -/

/-- **The slot pairing shifts along `D_z` in its first argument** (on the open quadrant):
`slotPairing ρ a b (D_z u) v = ∫_z∫_θ ρ · D_z^{b+1}D_θ^a u · D_z^bD_θ^a v`. -/
theorem slotPairing_dz_left (ρ : ℝ → ℝ → ℝ) (a b : ℕ) {u : ℝ → ℝ → ℝ}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (v : ℝ → ℝ → ℝ) :
    Work.FTS.TransportS.slotPairing ρ a b (Work.Spaces.Dz u) v
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ρ z θ * Work.Spaces.mixed (b + 1) a u z θ * Work.Spaces.mixed b a v z θ := by
  unfold Work.FTS.TransportS.slotPairing
  refine Work.FTS.TransportS.setIntegral2_congr_Q0 (fun p hp => ?_)
  have h := Work.FTS.TransportS.mixed_dz_eqOn hu b a hp
  simp only [Function.uncurry] at h
  simp only [Function.uncurry]
  rw [h]

/-! ## The caps of the three leaf weights on the open interval -/

/-- `1 ≤ sin(2θ)^{-η}` on the open interval. -/
theorem one_le_sin_eta {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
  Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ

/-- `1 ≤ sin(2θ)^{-γ}` on the open interval. -/
theorem one_le_sin_gam {α : ℝ} (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
  Work.FTS.TransportS.one_le_rpow_neg (le_of_lt (Work.Spaces.gam_pos hα)) hθ

/-- `sin(2θ)^{-η} ≤ sin(2θ)^{-γ}` on the closed interval. -/
theorem sin_eta_le_gam {α : ℝ} (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
  Work.FTS.H2.rpow_eta_le_gam hα hθ

/-! ## The three leaf weights as `w²·θ_w` -/

/-- The `η`-leaf weight is `w(z)² sin(2θ)^{-η}` (definitionally). -/
theorem leafEta_eq (z θ : ℝ) :
    Work.FTS.TransportS.leafEta z θ
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := rfl

/-- The constant leaf weight is `w(z)²`. -/
theorem leafOne_eq (z θ : ℝ) :
    Work.FTS.TransportS.leafOne z θ = (Work.Spaces.w z) ^ 2 := rfl

/-- The `γ`-leaf weight is `w(z)² sin(2θ)^{-γ}` (definitionally). -/
theorem leafGam_eq (α : ℝ) (z θ : ℝ) :
    Work.FTS.TransportS.leafGam α z θ
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := rfl

/-! ## The finite sum of the slot terms -/

/-- The slot sum of level six is a finite sum of at most `28` three-term groups. -/
theorem slotSum_six_card :
    (∑ a ∈ Finset.range (6 + 1), ∑ _b ∈ Finset.range (6 + 1 - a), (1 : ℝ)) = 28 := by
  norm_num [Finset.sum_range_succ]

/-! ## The a.e. form of a statement on the open quadrant -/

/-- **A statement which holds on the open quadrant holds a.e. for the product measure**
`(volume|Iz).prod (volume|Iθ)`: the complement of the open quadrant inside `Iz × Iθ` is the
union of the coordinate hyperplane `z = 0` and the two boundary lines `θ = 0`, `θ = π/2`, a
null set. -/
theorem ae_prod_Ioo {p : ℝ → ℝ → Prop}
    (h : ∀ θ ∈ Set.Ioo 0 (π / 2), ∀ z ∈ Set.Ioi 0, p z θ) :
    ∀ᵐ q ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)),
      p q.1 q.2 := by
  have hae : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[volume.prod volume] (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2)).symm
  rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_congr_set hae]
  exact MeasureTheory.ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioo)
    (fun q hq => h q.2 hq.2 q.1 hq.1)

/-! ## Continuity of the weight factors on the open quadrant -/

/-- `sin(2θ) > 0` on the open interval. -/
theorem sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `z ↦ w(z)²` is continuous on the open quadrant. -/
theorem continuousOn_w_sq_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2) Work.FTS.EllipticEst.Q0 := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2) (continuousOn_fst.pow 2)
      (fun p hp => pow_ne_zero 2 (ne_of_gt (Set.mem_prod.mp hp).1))
  exact (h1.pow 2).congr (fun p _ => rfl)

/-- `(z,θ) ↦ sin(2θ)^{-q}` is continuous on the open quadrant. -/
theorem continuousOn_sin_rpow_Q0 (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-q)) Work.FTS.EllipticEst.Q0 :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (sin_two_pos hp.2)))

/-! ## Integrability of a slot under a pointwise cap -/

/-- **Integrability of a capped slot**: if the slot with the *larger* `θ`-weight is product
integrable, then so is the slot with any smaller nonnegative `θ`-weight (the two agree up to
the null sets `θ = 0, π/2`). -/
theorem integrable_prod_of_cap {X : ℝ → ℝ → ℝ}
    (hXc : ContinuousOn (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    {q q' : ℝ}
    (hle : ∀ θ ∈ Set.Ioo 0 (π / 2), (Real.sin (2 * θ)) ^ (-q) ≤ (Real.sin (2 * θ)) ^ (-q'))
    (hbig : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q')
        * (X p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
        * (X p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  refine hbig.mono' ?_ ?_
  · exact Work.Spaces.aesm_of_continuousOn_Qd _
      ((continuousOn_w_sq_Q0.mul (continuousOn_sin_rpow_Q0 q)).mul (hXc.pow 2))
  · refine ae_prod_Ioo (p := fun z θ =>
      ‖(Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * (X z θ) ^ 2‖
        ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q') * (X z θ) ^ 2)
      (fun θ hθ z _ => ?_)
    have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-q) :=
      Real.rpow_nonneg (sin_two_nonneg_Iθ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) _
    have hpos := Real.rpow_pos_of_pos (sin_two_pos hθ) (-q')
    have hθnn : (0 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-q') := le_of_lt hpos
    have hsq : (0 : ℝ) ≤ (X z θ) ^ 2 := sq_nonneg _
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hsnn) hsq)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hle θ hθ) (sq_nonneg (Work.Spaces.w z))) hsq

/-- The elementary `2|xy| ≤ x² + y²`. -/
theorem abs_mul_le_half (x y : ℝ) : |x * y| ≤ (1 / 2) * x ^ 2 + (1 / 2) * y ^ 2 := by
  have h1 : x * y ≤ (1 / 2) * x ^ 2 + (1 / 2) * y ^ 2 := by nlinarith [sq_nonneg (x - y)]
  have h2 : -(x * y) ≤ (1 / 2) * x ^ 2 + (1 / 2) * y ^ 2 := by nlinarith [sq_nonneg (x + y)]
  rw [abs_le]
  constructor <;> linarith

/-- **The AM–GM bound for a slot.**  Given the pointwise domination of the two weighted
squares by the `ℋ⁶`-integrand of `f`, the weighted product is bounded by `HkSq α 6 f`. -/
theorem slotAMGM {α : ℝ} {f : ℝ → ℝ → ℝ} {X Y : ℝ → ℝ → ℝ} {q : ℝ}
    (h6 : Work.Spaces.HkMem α 6 f)
    (hq_nn : ∀ θ ∈ Set.Ioo 0 (π / 2), 0 ≤ (Real.sin (2 * θ)) ^ (-q))
    (hdomX : ∀ z θ, θ ∈ Set.Ioo 0 (π / 2) → (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-q) * (X z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ)
    (hdomY : ∀ z θ, θ ∈ Set.Ioo 0 (π / 2) → (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-q) * (Y z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ)
    (hAesm : MeasureTheory.AEStronglyMeasurable (Function.uncurry (fun z θ =>
        (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * (X z θ * Y z θ)))
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-q) * (X z θ * Y z θ)| ≤ Work.Spaces.HkSq α 6 f := by
  have hdom : ∀ z, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      |(Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * (X z θ * Y z θ)|
        ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z
    refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
    have hs : 0 ≤ (Real.sin (2 * θ)) ^ (-q) := hq_nn θ ⟨h1, h2⟩
    have he : |(Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * (X z θ * Y z θ)|
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * |X z θ * Y z θ| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hs]
    rw [he]
    calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * |X z θ * Y z θ|
        ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * ((1 / 2) * (X z θ) ^ 2 + (1 / 2) * (Y z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left (abs_mul_le_half (X z θ) (Y z θ))
            (mul_nonneg (sq_nonneg _) hs)
      _ = (1 / 2) * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * (X z θ) ^ 2)
          + (1 / 2) * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * (Y z θ) ^ 2) := by ring
      _ ≤ Work.Spaces.HkIntegrand α 6 f z θ := by linarith [hdomX z θ ⟨h1, h2⟩, hdomY z θ ⟨h1, h2⟩]
  have hBslice : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 6 f z θ) Work.Spaces.Iθ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => h6.1 z hz)
  have hIntAbs : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, |(Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
        * (X z θ * Y z θ)|) (volume.restrict Work.Spaces.Iz) := by
    refine MeasureTheory.Integrable.mono' h6.2 ?_ ?_
    · have hnorm : MeasureTheory.AEStronglyMeasurable
          (fun z => ∫ θ in Work.Spaces.Iθ,
            ‖Function.uncurry (fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
              * (X z θ * Y z θ)) (z, θ)‖)
          (volume.restrict Work.Spaces.Iz) := hAesm.norm.integral_prod_right'
      refine hnorm.congr ?_
      filter_upwards with z
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun θ => by
          simp only [Real.norm_eq_abs, Function.uncurry])
    · filter_upwards [hBslice] with z hz
      rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => abs_nonneg _)]
      exact MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => abs_nonneg _) hz (hdom z)
  have hstep1 : |∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * (X z θ * Y z θ))|
      ≤ ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * (X z θ * Y z θ)| :=
    abs_integral_le_integral_abs
  have hstep2 : (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * (X z θ * Y z θ)|)
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          |(Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * (X z θ * Y z θ)| :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => abs_nonneg _) hIntAbs
      (Filter.Eventually.of_forall fun z => abs_integral_le_integral_abs)
  have hstep3 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        |(Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * (X z θ * Y z θ)|)
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 6 f z θ :=
    int2_mono (fun z => hdom z) (fun z θ => abs_nonneg _) hBslice h6.2
  have hstep4 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 f z θ) = Work.Spaces.HkSq α 6 f := rfl
  linarith

end Work.FTS.StrongPersist.H6Pair6Aux
