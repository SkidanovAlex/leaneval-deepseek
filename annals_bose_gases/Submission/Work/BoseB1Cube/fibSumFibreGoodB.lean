import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.integrable_fibSumIntegrand
import Submission.Work.BoseB1Cube.uint_uint_le_z
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

/-- **The fibre-restriction inequality at the level of the sliding fibre sum** — FS's restriction
step (`eq:BSsliding2` → `eq:appsliding`, `final_v2.tex` l.3600–3640) applied to
`Work.BoseFixB1.fibSum` (`perBoxF_localised.lean`): the `u`-integral of the fibre sum over the
complement of `goodSet ℓ d μ` is dominated by three times its integral over the boundary layer
`goodSet ℓ d μ \ interiorSet ℓ d μ` (`SmallBoxSliding.Defs`; the layer is where FS substitute
`m(u) = 4`).

Import `Submission.Work.BoseB1Cube.goodCubeDefs`.  The `χ_M`-level input is taken as the explicit
hypothesis `hF1` (it is `Work.BoseB1Cube.chiFibreGood`, proved separately; here it is supplied in
the *interface* form needed below, i.e. restricted to `z, y ∈ acube ℓ` with
`|z_j − y_j| ≤ ℓ d / 16`).

**Spelling note:** the smoothness hypothesis is `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ`, i.e. the
*smooth* order `∞ = (↑⊤ : WithTop ℕ∞)` — **not** `ContDiff ℝ (⊤ : WithTop ℕ∞)`, which in this
Mathlib denotes the *analytic* order (`ContDiff.of_le`, and `∞ < ⊤` in `WithTop ℕ∞`);
`Work.BoseKinLoc.BoxState.contDiff` is the smooth one.  (`Continuous Φ` would also suffice.)

PROOF RECIPE.
* `wSmall1Pair h M ℓ d u z y = chiSmallB M ℓ d u z * W * chiSmallB M ℓ d u y` with
  `W = g0 v h (z−y) / (conv3Small M ((ℓd)⁻¹•(z−y)) * convScale ℓ (z−y))`
  (`wSmall1Pair = wSmallPair M ℓ d u (g0 v h)`, `wSmallPair`, `wSmallScaled`; the division has the
  `ℝ`-convention `x/0 = 0`), and `chiSmallB M ℓ d u z = chiScale ℓ z * chiSmall M ((ℓd)⁻¹•z − u)`,
  `chiSmallB M ℓ d u y = chiScale ℓ y * chiSmall M ((ℓd)⁻¹•y − u)`; a sibling agent's
  `Submission/Work/BoseB1Cube/fibSumFibreAux.lean` already proves the exact factorisation
  (`wSmall1Pair_eq_Kf_mul_Bl`) and the pointwise transfer
  (`uint_le_of_hF1`, `uy_swap`, `ae_Kf_nonneg`, `Bl_nonneg`) — import and glue it if green;
* hence the `u`-integral factorises exactly:
  `∫ u in s, wSmall1Pair … = chiScale ℓ z * chiScale ℓ y * W *
      ∫ u in s, chiSmall M ((ℓd)⁻¹•z − u) * chiSmall M ((ℓd)⁻¹•y − u)`
  for any set `s`, and the last factor is bounded by `hF1` (after the substitutions
  `a = (ℓd)⁻¹•z`, `b = (ℓd)⁻¹•y`, `ν = (1+d)/(2d)`, `δ' = μ^{-1/3}/(ℓd)`, and the two set
  identifications `{|u_j| ≤ ν − δ'} = goodSet ℓ d μ`, `{|u_j| ≤ ν − 2δ'} = interiorSet ℓ d μ`,
  which are the coordinate rescaling `|((ℓd)•u)_j| = ℓd|u_j|`); the hypotheses of `hF1` come from
  `z, y ∈ acube ℓ` (giving `|a_j|, |b_j| ≤ 1/(2d) = ν − 1/2`), from `|z_j − y_j| ≤ ℓd/16` and from
  `hδ'8 : μ^{-1/3}/(ℓd) ≤ 1/8`; the case `|z−y| ≥ R` is trivial because then `g0 v h (z−y) = 0`
  (support of `g₀ ⊆ ball 0 R ⊆ ball 0 (ℓd/16)`, `hRd`) and both sides vanish;
* the factor `chiScale ℓ z * chiScale ℓ y * W` is nonnegative a.e. in `y`
  (`chiBase_nonneg`; `conv3Small ≥ 0`, `convScale ℓ ≥ 0`, and `g0 v h ≥ 0` a.e.
  by `Submission.BoseGases.g0_nonneg_ae`), so the pointwise-in-`(z,y)` bound above can be
  integrated against `y` over `acube ℓ` and against `x` over `abox n ℓ` with the weight
  `Φ x ^ 2 ≥ 0` (`integral_mono_ae`);
* the two Fubini exchanges needed to compare `∫ u in s, fibSum u` with the iterated integral
  `∫ x, Φ x^2 ∑ i, ∫ y, (∫ u in s, wSmall1Pair …)` are the standard ones (all integrands are
  bounded on the compact boxes — `abox n ℓ` is compact, `acube ℓ` is compact, the `u`-support is
  the fixed cube `{|u_j| ≤ ν}`, and `wSmall1Pair` is bounded by `Work.BoseFixB1.abs_wSmall1Pair_le`
  / `wSmall1Pair_fibre_abs_le`); use `MeasureTheory.integral_integral_swap` (both orders are
  integrable) or the `lintegral`-Tonelli route. -/
theorem fibSumFibreGoodB {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) {M : ℕ} (hM : 1 ≤ M)
    {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hRd : R ≤ ℓ * d / 16)
    (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) (hμ : 0 < μ)
    (hδ'8 : μ ^ (-1 / 3 : ℝ) / (ℓ * d) ≤ 1 / 8)
    (hF1 : ∀ z y : EuclideanSpace ℝ (Fin 3), z ∈ Submission.BoseGases.acube ℓ →
      y ∈ Submission.BoseGases.acube ℓ →
      (∀ j : Fin 3, |(z - y).ofLp j| ≤ ℓ * d / 16) →
      (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ,
          Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z - u) *
            Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u))
        ≤ 3 * (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ
                        \ Work.SmallBoxSliding.interiorSet ℓ d μ),
            Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z - u) *
              Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)))
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) :
    (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ,
        Work.BoseFixB1.fibSum h M ℓ d u Φ)
      ≤ 3 * (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ
                      \ Work.SmallBoxSliding.interiorSet ℓ d μ),
          Work.BoseFixB1.fibSum h M ℓ d u Φ) := by
  -- The assembly follows the recipe in the docstring; the two halves of the restriction step are
  -- supplied by the *proved* corpus lemmas `Work.BoseB1Cube.uint_uint_le_z` (the pointwise-in-`z`
  -- comparison at the level of `wSmall1Pair`, i.e. `hF1` transferred across `Kf`) and
  -- `Work.BoseB1Cube.integrable_fibSumIntegrand` (joint `(u,x)`-integrability of the Fubini
  -- integrand).  Everything below is the `(u,x)` Fubini exchange, the linearity of the
  -- `u`-integral in the `x`-variable, and the final `integral_mono_of_nonneg` with the a.e.
  -- nonnegativity of the minorant (`fibSum ≥ 0` is not needed: the fibre is nonnegative).
  have _hμ := hμ
  have _hδ'8 := hδ'8
  -- (0) `hF1` in the `Bl`-spelling of `fibSumFibreAux`
  have hF1B : ∀ z y : EuclideanSpace ℝ (Fin 3), z ∈ Submission.BoseGases.acube ℓ →
      y ∈ Submission.BoseGases.acube ℓ →
      (∀ j : Fin 3, |(z - y).ofLp j| ≤ ℓ * d / 16) →
      (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ, Bl M ℓ d u z y)
        ≤ 3 * (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ
                        \ Work.SmallBoxSliding.interiorSet ℓ d μ), Bl M ℓ d u z y) :=
    fun z y hz hy hab => by simpa only [Bl] using hF1 z y hz hy hab
  -- (1) the `y`-fibre at each `(u,z)` is nonnegative
  have hfibnn : ∀ u z : EuclideanSpace ℝ (Fin 3),
      0 ≤ ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u z y := by
    intro u z
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_of_ae (ae_Kf_nonneg hv hvrad hR hv_supp h z)]
      with y hy
    rw [wSmall1Pair_eq_Kf_mul_Bl h M ℓ d u z y]
    exact mul_nonneg hy (Bl_nonneg M ℓ d u z y)
  -- (2) the pointwise-in-`z` restriction inequality at the level of `wSmall1Pair`
  have hZ : ∀ z : EuclideanSpace ℝ (Fin 3), z ∈ Submission.BoseGases.acube ℓ →
      (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ,
          ∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmall1Pair h M ℓ d u z y)
        ≤ 3 * (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ
                        \ Work.SmallBoxSliding.interiorSet ℓ d μ),
            ∫ y in Submission.BoseGases.acube ℓ,
              Submission.BoseGases.wSmall1Pair h M ℓ d u z y) :=
    fun z hz => uint_uint_le_z h hv hvrad hR hv_supp hM hℓ hd hRd hRχ hF1B hz
  -- (3a) linearity of the `u`-integral in the `x`-variable
  have hswap_pt : ∀ (s : Set (EuclideanSpace ℝ (Fin 3))) (x : Submission.BoseGases.X n),
      (∫ u in s, Φ x ^ 2 * ∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
        = Φ x ^ 2 * ∑ i : Fin n, ∫ u in s, ∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y := by
    intro s x
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact MeasureTheory.integral_finsetSum Finset.univ (fun i _ =>
      ((Work.SmallBoxSliding.integrable_wSmall1Pair_prod hv_supp hR h hM hℓ hd hRd hRχ
        (x i)).integral_prod_left).mono_measure MeasureTheory.Measure.restrict_le_self)
  -- (3b) the `(u,x)`-Fubini exchange
  have hFub : ∀ s : Set (EuclideanSpace ℝ (Fin 3)),
      (∫ u in s, Work.BoseFixB1.fibSum h M ℓ d u Φ)
        = ∫ x in Submission.BoseGases.abox n ℓ, Φ x ^ 2 *
            ∑ i : Fin n, ∫ u in s, ∫ y in Submission.BoseGases.acube ℓ,
              Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y := by
    intro s
    have hjoint :=
      integrable_fibSumIntegrand h hv hvrad hR hv_supp hM hℓ hd hRd hRχ Φ hΦ.continuous s
    have hsw := MeasureTheory.integral_integral_swap
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict s)
      (ν := (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ))
      (f := fun (u : EuclideanSpace ℝ (Fin 3)) (x : Submission.BoseGases.X n) =>
        Φ x ^ 2 * ∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y) hjoint
    have hfib : (∫ u in s, Work.BoseFixB1.fibSum h M ℓ d u Φ)
        = ∫ u in s, ∫ x in Submission.BoseGases.abox n ℓ, Φ x ^ 2 *
            ∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
              Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y := rfl
    rw [hfib, hsw]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun x => hswap_pt s x))
  -- (4) the majorant of the final comparison is integrable
  have hIntMaj : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        ∫ u, (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
          Φ p.2 ^ 2 * ∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmall1Pair h M ℓ d p.1 (p.2 i) y) (u, x)
        ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Work.SmallBoxSliding.goodSet ℓ d μ
            \ Work.SmallBoxSliding.interiorSet ℓ d μ)))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) :=
    (integrable_fibSumIntegrand h hv hvrad hR hv_supp hM hℓ hd hRd hRχ Φ hΦ.continuous
      (Work.SmallBoxSliding.goodSet ℓ d μ
        \ Work.SmallBoxSliding.interiorSet ℓ d μ)).integral_prod_right
  have hIntMaj3 : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n => 3 * (Φ x ^ 2 * ∑ i : Fin n,
        ∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ
                  \ Work.SmallBoxSliding.interiorSet ℓ d μ),
          ∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) :=
    (hIntMaj.congr (Filter.Eventually.of_forall (fun x =>
      hswap_pt (Work.SmallBoxSliding.goodSet ℓ d μ
        \ Work.SmallBoxSliding.interiorSet ℓ d μ) x))).const_mul 3
  -- (5) nonnegativity of the minorant, and the pointwise comparison
  have hminor_nn : 0 ≤ᵐ[((MeasureTheory.volume : MeasureTheory.Measure
        (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ))]
      (fun x : Submission.BoseGases.X n => Φ x ^ 2 * ∑ i : Fin n,
        ∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ,
          ∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y) :=
    Filter.Eventually.of_forall (fun x => mul_nonneg (sq_nonneg (Φ x))
      (Finset.sum_nonneg (fun i _ =>
        MeasureTheory.integral_nonneg (fun u => hfibnn u (x i)))))
  have hle : ∀ x ∈ Submission.BoseGases.abox n ℓ,
      Φ x ^ 2 * ∑ i : Fin n, ∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ,
          ∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y
        ≤ 3 * (Φ x ^ 2 * ∑ i : Fin n,
            ∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ
                      \ Work.SmallBoxSliding.interiorSet ℓ d μ),
              ∫ y in Submission.BoseGases.acube ℓ,
                Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y) := by
    intro x hx
    have hsum : (∑ i : Fin n, ∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ,
          ∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
        ≤ 3 * ∑ i : Fin n, ∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ
                      \ Work.SmallBoxSliding.interiorSet ℓ d μ),
              ∫ y in Submission.BoseGases.acube ℓ,
                Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y := by
      calc (∑ i : Fin n, ∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ,
              ∫ y in Submission.BoseGases.acube ℓ,
                Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
          ≤ ∑ i : Fin n, 3 * (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ
                      \ Work.SmallBoxSliding.interiorSet ℓ d μ),
              ∫ y in Submission.BoseGases.acube ℓ,
                Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y) :=
            Finset.sum_le_sum (fun i _ => hZ (x i) (hx i))
        _ = 3 * ∑ i : Fin n, ∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ
                      \ Work.SmallBoxSliding.interiorSet ℓ d μ),
              ∫ y in Submission.BoseGases.acube ℓ,
                Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y := by
            rw [Finset.mul_sum]
    calc Φ x ^ 2 * ∑ i : Fin n, ∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ,
            ∫ y in Submission.BoseGases.acube ℓ,
              Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y
        ≤ Φ x ^ 2 * (3 * ∑ i : Fin n, ∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ
                      \ Work.SmallBoxSliding.interiorSet ℓ d μ),
              ∫ y in Submission.BoseGases.acube ℓ,
                Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y) :=
          mul_le_mul_of_nonneg_left hsum (sq_nonneg (Φ x))
      _ = 3 * (Φ x ^ 2 * ∑ i : Fin n,
            ∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ
                      \ Work.SmallBoxSliding.interiorSet ℓ d μ),
              ∫ y in Submission.BoseGases.acube ℓ,
                Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y) := by
          ring
  -- (6) assemble
  rw [hFub ((Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ),
    hFub (Work.SmallBoxSliding.goodSet ℓ d μ \ Work.SmallBoxSliding.interiorSet ℓ d μ)]
  exact le_trans
    (MeasureTheory.integral_mono_of_nonneg hminor_nn hIntMaj3
      (MeasureTheory.ae_restrict_of_forall_mem (Submission.BoseGases.abox_measurable n ℓ) hle))
    (le_of_eq (MeasureTheory.integral_const_mul 3 _))

end Work.BoseB1Cube
