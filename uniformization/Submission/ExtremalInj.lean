import ChallengeDeps
import Submission.Extremal
import Submission.ExtremalOnto
import Submission.ExtremalExist
import Submission.PackagingOpen
import Submission.Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic
import Submission.Commons.Analysis.Complex.Analytic.locallyUniformLimit_injective_or_const

/-!
# The injective extremal problem

The extremal-derivative route of `Submission/ExtremalOnto.lean` produces, from any holomorphic
`f : X → ℂ` with `‖f‖ ≤ 1`, `f x₀ = 0` missing a value `a ∈ 𝔻`, a *new* holomorphic function `g`
with a strictly larger derivative at `x₀`.  The construction is `g = M_b ∘ √(M_a ∘ f)`, and
therefore **preserves injectivity**: if `f` is injective then so is `g`.

This is the key extra piece needed for the classical Riemann-mapping argument: consider the
family of *injective* members of the extremal family.  A maximising sequence is normal (Montel),
and its limit is injective (Hurwitz's theorem, a commons result) as soon as the extremal value is
positive — injectivity is never lost in the limit unless the limit is constant.  The extremal
solution of the injective problem therefore maps `X` *onto* `𝔻` (otherwise the amplification
would produce an injective competitor with a larger derivative), hence is a biholomorphism
`X ≅ 𝔻`.

Consequently the uniformization theorem is reduced to the dichotomy
`(∃ injective holomorphic f : X → 𝔻 with f x₀ = 0)` or `X ≅ ℂ`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## Injectivity of the disc automorphism -/

/-- The Möbius transformation `mobiusA a` is injective on the closed unit disc. -/
theorem mobiusA_injOn {a : ℂ} (ha : ‖a‖ < 1) {w w' : ℂ} (hw : ‖w‖ ≤ 1) (hw' : ‖w'‖ ≤ 1)
    (h : mobiusA a w = mobiusA a w') : w = w' := by
  have h1 : 1 - (starRingEnd ℂ) a * w ≠ 0 := mobiusA_denom_ne_zero ha hw
  have h2 : 1 - (starRingEnd ℂ) a * w' ≠ 0 := mobiusA_denom_ne_zero ha hw'
  have h3 : (w - a) * (1 - (starRingEnd ℂ) a * w') = (w' - a) * (1 - (starRingEnd ℂ) a * w) := by
    have hh := h
    simp only [mobiusA] at hh
    rw [div_eq_div_iff h1 h2] at hh
    exact hh
  have key : (w - w') * (1 - (starRingEnd ℂ) a * a) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp key with hzero | hzero
  · exact sub_eq_zero.mp hzero
  · exfalso
    have h3' : (starRingEnd ℂ) a * a = 1 := (sub_eq_zero.mp hzero).symm
    rw [← Complex.normSq_eq_conj_mul_self] at h3'
    have h4 : Complex.normSq a = 1 := by exact_mod_cast h3'
    rw [Complex.normSq_eq_norm_sq] at h4
    have : ‖a‖ = 1 := by nlinarith [norm_nonneg a, h4]
    linarith

/-- Every point of a `ℂ`-charted space has a distinct companion (the chart target is open). -/
theorem exists_ne_of_chartedSpace (z : X) : ∃ y : X, y ≠ z := by
  have hz : (chartAt ℂ z) z ∈ (chartAt ℂ z).target :=
    (chartAt ℂ z).map_source (mem_chart_source ℂ z)
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp (chartAt ℂ z).open_target _ hz
  set v : ℂ := (chartAt ℂ z) z + ((r / 2 : ℝ) : ℂ) with hv
  have hvmem : v ∈ (chartAt ℂ z).target := hrsub (by
    rw [hv, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith)
  have hvne : v ≠ (chartAt ℂ z) z := by
    intro h
    have h' : ((r / 2 : ℝ) : ℂ) = 0 := by
      have h2 : (chartAt ℂ z) z + ((r / 2 : ℝ) : ℂ) = (chartAt ℂ z) z + 0 := by
        rw [add_zero]
        rw [hv] at h
        exact h
      exact add_left_cancel h2
    have hd' : r / 2 = 0 := by exact_mod_cast h'
    linarith
  refine ⟨(chartAt ℂ z).symm v, fun hy => ?_⟩
  have hcontra : v = (chartAt ℂ z) z := by
    have h1 : (chartAt ℂ z) ((chartAt ℂ z).symm v) = (chartAt ℂ z) z := by rw [hy]
    rwa [(chartAt ℂ z).right_inv hvmem] at h1
  exact hvne hcontra

/-! ## The amplification preserves injectivity -/

/-- **The Möbius (square-root) amplification, preserving injectivity.**  Same statement as
`Submission.exists_holomorphicOnX_deriv_eq_of_misses_value`, with the additional conclusion that
the amplified function is injective whenever `f` is. -/
theorem exists_injective_holomorphicOnX_deriv_eq_of_misses_value {x₀ : X} [ConnectedSpace X]
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    {f : X → ℂ} (hf : HolomorphicOnX f univ) (hb : ∀ x, ‖f x‖ ≤ 1) (h0 : f x₀ = 0)
    (hinjf : Function.Injective f)
    {a : ℂ} (ha : ‖a‖ < 1) (hmiss : ∀ x, f x ≠ a) :
    ∃ g : X → ℂ, HolomorphicOnX g univ ∧ (∀ x, ‖g x‖ ≤ 1) ∧ g x₀ = 0 ∧
      Function.Injective g ∧
      ‖deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ =
        (1 + ‖a‖) / (2 * Real.sqrt ‖a‖) *
          ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ := by
  have ha0 : a ≠ 0 := by
    intro h; exact hmiss x₀ (by rw [h0, h])
  have hanorm : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  set φ : X → ℂ := fun x => mobiusA a (f x) with hφ
  have hφhol : HolomorphicOnX φ univ := hf.mobiusA_comp (fun x _ => hb x) ha
  have hφne : ∀ x, φ x ≠ 0 := fun x => mobiusA_ne_zero ha (hb x) (hmiss x)
  obtain ⟨H, hHhol, hHexp⟩ := HolomorphicOnX.exists_log_of_ne_zero x₀ hφhol hφne
  set h : X → ℂ := fun x => Complex.exp (H x * 2⁻¹) with hh
  have hhol : HolomorphicOnX h univ := fun x hx =>
    ((hHhol x hx).mul_const ((2:ℂ)⁻¹)).cexp
  have hh2 : ∀ x, h x ^ 2 = φ x := by
    intro x
    show Complex.exp (H x * 2⁻¹) ^ 2 = φ x
    rw [hHexp x, sq, ← Complex.exp_add]
    congr 1
    ring_nf
  have hhnorm : ∀ x, ‖h x‖ ≤ 1 := by
    intro x
    have h2 : ‖h x‖ ^ 2 ≤ 1 := by
      rw [← norm_pow, hh2 x, hφ]
      exact norm_mobiusA_le ha (hb x)
    nlinarith [norm_nonneg (h x)]
  set b : ℂ := h x₀ with hbdef
  have hb_sq : ‖b‖ ^ 2 = ‖a‖ := by
    have h1 : b ^ 2 = φ x₀ := by rw [hbdef]; exact hh2 x₀
    have h2 : φ x₀ = -a := by
      show mobiusA a (f x₀) = -a
      rw [h0, mobiusA_apply_zero]
    rw [← norm_pow, h1, h2, norm_neg]
  have hb_sqrt : ‖b‖ = Real.sqrt ‖a‖ := by
    have h3 : (0:ℝ) ≤ Real.sqrt ‖a‖ := Real.sqrt_nonneg _
    have h4 : (Real.sqrt ‖a‖) ^ 2 = ‖a‖ := Real.sq_sqrt (norm_nonneg a)
    nlinarith [norm_nonneg b, h3, hb_sq, h4]
  have hb_lt : ‖b‖ < 1 := by
    rw [hb_sqrt]
    rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 1)]
    simpa using ha
  have hb_ne : b ≠ 0 := by
    intro h; rw [h] at hb_sq; simp at hb_sq
    linarith [hanorm]
  -- injectivity of the intermediate maps
  have hφinj : Function.Injective φ := fun p q hpq =>
    hinjf (mobiusA_injOn ha (hb p) (hb q) hpq)
  have hhinj : Function.Injective h := fun p q hpq =>
    hφinj (by rw [← hh2 p, ← hh2 q, hpq])
  have hginj : Function.Injective (fun x => mobiusA b (h x)) := fun p q hpq =>
    hhinj (mobiusA_injOn hb_lt (hhnorm p) (hhnorm q) hpq)
  refine ⟨fun x => mobiusA b (h x), hhol.mobiusA_comp (fun x _ => hhnorm x) hb_lt,
    fun x => norm_mobiusA_le hb_lt (hhnorm x), ?_, hginj, ?_⟩
  · show mobiusA (h x₀) (h x₀) = 0
    exact mobiusA_self _
  -- the derivative computation, in the chart at `x₀`
  have E1 : (fun x => mobiusA b (h x)) ∘ (chartAt ℂ x₀).symm
      = mobiusA b ∘ (h ∘ (chartAt ℂ x₀).symm) := rfl
  have E2 : (φ ∘ (chartAt ℂ x₀).symm)
      = mobiusA a ∘ (f ∘ (chartAt ℂ x₀).symm) := rfl
  have E3 : (h ∘ (chartAt ℂ x₀).symm) * (h ∘ (chartAt ℂ x₀).symm) = φ ∘ (chartAt ℂ x₀).symm := by
    funext w
    simp only [Pi.mul_apply, Function.comp_apply]
    simpa [sq] using hh2 ((chartAt ℂ x₀).symm w)
  have hx₀src : x₀ ∈ (chartAt ℂ x₀).source := mem_chart_source ℂ x₀
  have hleft : (chartAt ℂ x₀).symm ((chartAt ℂ x₀) x₀) = x₀ := (chartAt ℂ x₀).left_inv hx₀src
  have hF : AnalyticAt ℂ (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) := hf x₀ (mem_univ x₀)
  have hHc : AnalyticAt ℂ (h ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) := hhol x₀ (mem_univ x₀)
  have hGc : AnalyticAt ℂ ((fun x => mobiusA b (h x)) ∘ (chartAt ℂ x₀).symm)
      ((chartAt ℂ x₀) x₀) :=
    (hhol.mobiusA_comp (fun x _ => hhnorm x) hb_lt) x₀ (mem_univ x₀)
  have hHcval : (h ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = b := by
    simp only [Function.comp_apply, hleft, hbdef]
  have hFval : (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 0 := by
    simp only [Function.comp_apply, hleft, h0]
  have hHcne : (h ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) ≠ 0 := by
    rw [hHcval]; exact hb_ne
  have hden_a : 1 - (starRingEnd ℂ) a * (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) ≠ 0 := by
    rw [hFval]; norm_num
  have D1 : deriv (φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)
      = (1 - (starRingEnd ℂ) a * a) * deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) := by
    rw [E2]
    rw [deriv_comp _ (analyticAt_mobiusA a hden_a).differentiableAt hF.differentiableAt]
    rw [hFval, deriv_mobiusA_zero]
  have D2 : deriv (h ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)
      = deriv (φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)
        / (2 * (h ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)) := by
    have hdm : deriv (φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)
        = 2 * (h ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)
          * deriv (h ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) := by
      rw [← E3, deriv_mul hHc.differentiableAt hHc.differentiableAt]
      ring
    rw [hdm]
    field_simp
  have D3 : deriv ((fun x => mobiusA b (h x)) ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)
      = (1 / (1 - (starRingEnd ℂ) b * b)) * deriv (h ∘ (chartAt ℂ x₀).symm)
          ((chartAt ℂ x₀) x₀) := by
    rw [E1]
    rw [deriv_comp _ (analyticAt_mobiusA b ?_).differentiableAt hHc.differentiableAt]
    · rw [hHcval, deriv_mobiusA_self hb_lt]
    · rw [hHcval]
      exact mobiusA_denom_ne_zero hb_lt (le_of_lt hb_lt)
  have key : deriv ((fun x => mobiusA b (h x)) ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)
      = (1 / (1 - (starRingEnd ℂ) b * b)) *
          ((1 - (starRingEnd ℂ) a * a) * deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)
            / (2 * b)) := by
    rw [D3, D2, D1, hHcval]
  rw [key]
  have hnorm_b : ‖1 - (starRingEnd ℂ) b * b‖ = 1 - ‖b‖ ^ 2 := by
    have h1 : 1 - (starRingEnd ℂ) b * b = ((1 - Complex.normSq b : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_conj_mul_self]
      push_cast
      ring
    rw [h1, Complex.norm_real, Complex.normSq_eq_norm_sq, Real.norm_eq_abs]
    exact abs_of_nonneg (by nlinarith [norm_nonneg b, hb_lt])
  have hnorm_a : ‖1 - (starRingEnd ℂ) a * a‖ = 1 - ‖a‖ ^ 2 := by
    have h1 : 1 - (starRingEnd ℂ) a * a = ((1 - Complex.normSq a : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_conj_mul_self]
      push_cast
      ring
    rw [h1, Complex.norm_real, Complex.normSq_eq_norm_sq, Real.norm_eq_abs]
    exact abs_of_nonneg (by nlinarith [norm_nonneg a, ha])
  simp only [norm_mul, norm_div, norm_one]
  rw [hnorm_b, hnorm_a, hb_sqrt, Real.sq_sqrt (norm_nonneg a)]
  have hne1 : (1 - ‖a‖) ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; linarith [ha]
  have hne2 : (2 * Real.sqrt ‖a‖) ≠ 0 := by positivity
  field_simp
  norm_num
  ring


/-! ## The injective extremal family -/

/-- The family of *injective* members of the extremal family. -/
def injFamily (x₀ : X) : Set (X → ℂ) := {f ∈ extremalFamily x₀ | Function.Injective f}

theorem injFamily_holomorphic {x₀ : X} {f : X → ℂ} (hf : f ∈ injFamily x₀) :
    HolomorphicOnX f univ := hf.1.1

theorem injFamily_norm {x₀ : X} {f : X → ℂ} (hf : f ∈ injFamily x₀) : ∀ x, ‖f x‖ ≤ 1 :=
  hf.1.2.1

theorem injFamily_zero {x₀ : X} {f : X → ℂ} (hf : f ∈ injFamily x₀) : f x₀ = 0 := hf.1.2.2

theorem injFamily_injective {x₀ : X} {f : X → ℂ} (hf : f ∈ injFamily x₀) :
    Function.Injective f := hf.2

theorem injFamily_subset_extremalFamily (x₀ : X) : injFamily x₀ ⊆ extremalFamily x₀ :=
  fun f hf => hf.1

/-- The set of derivative norms over the injective family. -/
def injDerivSet (x₀ : X) : Set ℝ :=
  (fun f : X → ℂ => ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖) '' injFamily x₀

/-- The supremum of the derivative norms over the injective family. -/
def injDerivative (x₀ : X) : ℝ := sSup (injDerivSet x₀)

theorem injDerivSet_bddAbove {x₀ : X} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall (chartAt ℂ x₀ x₀) ρ ⊆ (chartAt ℂ x₀).target) :
    BddAbove (injDerivSet x₀) := by
  obtain ⟨M, hM⟩ := extremalDerivative_bddAbove (X := X) hρ hsub
  exact ⟨M, fun y hy => hM (Set.image_mono (injFamily_subset_extremalFamily x₀) hy)⟩

/-! ## Existence of the extremal injective function -/

/-- **The extremal injective function exists.**  A maximising sequence in the injective family is
normal (Montel), and its limit is injective by Hurwitz's theorem as soon as the extremal value is
positive. -/
theorem exists_extremal_injective (x₀ : X) [ConnectedSpace X] [SecondCountableTopology X]
    (hne : (injFamily x₀).Nonempty) (hpos : 0 < injDerivative x₀) :
    ∃ f ∈ injFamily x₀,
      ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ = injDerivative x₀ := by
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  obtain ⟨ρ, hρ, hsub⟩ := exists_chartDisc_radius (X := X) x₀
  have hbdd : BddAbove (injDerivSet x₀) := injDerivSet_bddAbove hρ hsub
  have hseq : ∀ n : ℕ, ∃ f ∈ injFamily x₀,
      injDerivative x₀ - ((n : ℝ) + 1)⁻¹ <
        ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ := by
    intro n
    have hlt : injDerivative x₀ - ((n : ℝ) + 1)⁻¹ < sSup (injDerivSet x₀) := by
      rw [← injDerivative]
      have : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
      linarith
    obtain ⟨y, ⟨f, hf, rfl⟩, hy⟩ := exists_lt_of_lt_csSup (hne.image _) hlt
    exact ⟨f, hf, hy⟩
  choose f hf hfbound using hseq
  obtain ⟨φ, g, hφmono, hconv, hghol⟩ :=
    montel_on_X (X := X) x₀ f (fun n => (hf n).1.1) (fun n x => (hf n).1.2.1 x)
  have hgE : g ∈ extremalFamily x₀ := by
    refine ⟨hghol, ?_, ?_⟩
    · intro x
      exact le_of_tendsto (hconv.tendsto_at (mem_univ x)).norm
        (Eventually.of_forall fun n => (hf (φ n)).1.2.1 x)
    · have hpt : Tendsto (fun n => f (φ n) x₀) atTop (𝓝 (g x₀)) :=
        hconv.tendsto_at (mem_univ x₀)
      have hzero : (fun n => f (φ n) x₀) = fun _ => (0 : ℂ) := by
        funext n; exact (hf (φ n)).1.2.2
      rw [hzero] at hpt
      exact tendsto_nhds_unique hpt tendsto_const_nhds
  -- Hurwitz: the limit is injective or constant
  have hInjOrConst : Function.Injective g ∨ ∃ c : ℂ, ∀ x, g x = c :=
    Commons.Analysis.Complex.Analytic.locallyUniformLimit_injective_or_const
      (X := X) (f := fun n => f (φ n)) (g := g)
      (fun n x => (hf (φ n)).1.1 x (mem_univ x))
      (fun x => hghol x (mem_univ x)) hconv (fun n => (hf (φ n)).2)
  -- convergence of the derivatives on the chart at `x₀`
  have hconv' : TendstoLocallyUniformlyOn (fun n => (f (φ n)) ∘ (chartAt ℂ x₀).symm)
      (g ∘ (chartAt ℂ x₀).symm) atTop (chartAt ℂ x₀).target :=
    hconv.comp (chartAt ℂ x₀).symm (mapsTo_univ _ _) (chartAt ℂ x₀).continuousOn_symm
  have hderivconv : TendstoLocallyUniformlyOn
      (deriv ∘ fun n => (f (φ n)) ∘ (chartAt ℂ x₀).symm)
      (deriv (g ∘ (chartAt ℂ x₀).symm)) atTop (chartAt ℂ x₀).target := by
    refine hconv'.deriv ?_ (chartAt ℂ x₀).open_target
    filter_upwards with n
    intro w hw
    exact ((analyticOnNhd_chart_at (hf (φ n)).1.1 x₀) w hw).differentiableWithinAt
  have hpt := hderivconv.tendsto_at ((chartAt ℂ x₀).map_source (mem_chart_source ℂ x₀))
  have hnorm : Tendsto (fun n => ‖deriv ((f (φ n)) ∘ (chartAt ℂ x₀).symm)
      ((chartAt ℂ x₀) x₀)‖) atTop
      (𝓝 ‖deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖) := hpt.norm
  have hupper : ∀ n : ℕ, ‖deriv ((f (φ n)) ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖
      ≤ injDerivative x₀ := fun n =>
    le_csSup hbdd ⟨f (φ n), hf (φ n), rfl⟩
  have hlower : Tendsto (fun n : ℕ => injDerivative x₀ - ((φ n : ℝ) + 1)⁻¹) atTop
      (𝓝 (injDerivative x₀)) := by
    have hφR : Tendsto (fun n : ℕ => ((φ n : ℝ))) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hφmono.tendsto_atTop
    have h0 : Tendsto (fun n : ℕ => ((φ n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 hφR)
    simpa using tendsto_const_nhds.sub h0
  have hlim : ‖deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ = injDerivative x₀ :=
    tendsto_nhds_unique hnorm
      (tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
        (Eventually.of_forall fun n => le_of_lt (hfbound (φ n)))
        (Eventually.of_forall hupper))
  have hgInj : Function.Injective g := by
    rcases hInjOrConst with h | ⟨c, hc⟩
    · exact h
    · exfalso
      have hg0 : g x₀ = 0 := hgE.2.2
      have h0 : deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 0 := by
        have hconst : (g ∘ (chartAt ℂ x₀).symm) = fun _ => (0 : ℂ) := by
          funext w
          have h1 : g ((chartAt ℂ x₀).symm w) = c := hc _
          have h2 : g x₀ = c := hc x₀
          rw [Function.comp_apply, h1, ← h2, hg0]
        rw [hconst, deriv_const]
      rw [h0, norm_zero] at hlim
      linarith
  exact ⟨g, ⟨hgE, hgInj⟩, hlim⟩

/-! ## The extremal injective function is onto the disc -/

/-- **The extremal injective function maps onto the unit disc**: otherwise the injectivity-preserving
amplification would produce an injective competitor with a strictly larger derivative. -/
theorem injExtremal_onto {x₀ : X} [ConnectedSpace X]
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)] {f : X → ℂ}
    (hf : f ∈ injFamily x₀)
    (hmax : ∀ g ∈ injFamily x₀,
      ‖deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ ≤
        ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖)
    (hpos : 0 < ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖) :
    ∀ a : ℂ, ‖a‖ < 1 → ∃ x : X, f x = a := by
  intro a ha
  by_contra hcon
  push_neg at hcon
  have hmiss : ∀ x : X, f x ≠ a := fun x hx => hcon x hx
  have ha0 : a ≠ 0 := fun h => (hmiss x₀) (by rw [h, hf.1.2.2])
  have hanorm : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  obtain ⟨g, hghol, hgnorm, hg0, hginj, hderiv⟩ :=
    exists_injective_holomorphicOnX_deriv_eq_of_misses_value (x₀ := x₀)
      (hf.1.1) (hf.1.2.1) (hf.1.2.2) hf.2 ha hmiss
  have hgmem : g ∈ injFamily x₀ := ⟨⟨hghol, hgnorm, hg0⟩, hginj⟩
  have hfac : 1 < (1 + ‖a‖) / (2 * Real.sqrt ‖a‖) := by
    have hsqrt_pos : 0 < Real.sqrt ‖a‖ := Real.sqrt_pos.mpr hanorm
    have hsqrt_lt_one : Real.sqrt ‖a‖ < 1 := (Real.sqrt_lt' one_pos).mpr (by norm_num at ha ⊢; exact ha)
    have hsq : (Real.sqrt ‖a‖) ^ 2 = ‖a‖ := Real.sq_sqrt (norm_nonneg a)
    have hlt : 1 + ‖a‖ > 2 * Real.sqrt ‖a‖ := by nlinarith [hsqrt_pos, hsqrt_lt_one, hsq]
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have hle := hmax g hgmem
  rw [hderiv] at hle
  have hD : (0:ℝ) ≤ ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ := norm_nonneg _
  nlinarith [hfac, hpos, hD, hle]

/-! ## The injective-extremal reduction of the uniformization theorem -/

/-- **Case A of uniformization: an injective holomorphic function into the disc exists.**  Then the
theorem holds: the extremal injective function is onto, hence a biholomorphism onto `𝔻`. -/
theorem uniformization_of_injective_into_disc {x₀ : X} [ConnectedSpace X]
    [SecondCountableTopology X] [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    (hne : (injFamily x₀).Nonempty) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) := by
  obtain ⟨ρ, hρ, hsub⟩ := exists_chartDisc_radius (X := X) x₀
  have hbdd : BddAbove (injDerivSet x₀) := injDerivSet_bddAbove hρ hsub
  have hpos : 0 < injDerivative x₀ := by
    obtain ⟨g₀, hg₀⟩ := hne
    have hne0 : ‖deriv (g₀ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ ≠ 0 := by
      have h1 := Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic
        (X := X) (Φ := g₀) hg₀.2 (fun x => hg₀.1.1 x (mem_univ x)) (exists_ne_of_chartedSpace x₀)
      simpa [norm_eq_zero] using h1
    have h2 : ‖deriv (g₀ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ ≤ injDerivative x₀ :=
      le_csSup hbdd ⟨g₀, hg₀, rfl⟩
    have h3 : 0 < ‖deriv (g₀ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne0)
    linarith
  obtain ⟨f, hf, hmaxeq⟩ := exists_extremal_injective (X := X) x₀ hne hpos
  have hmax : ∀ g ∈ injFamily x₀,
      ‖deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ ≤
        ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ := by
    intro g hg
    rw [hmaxeq]
    exact le_csSup hbdd ⟨g, hg, rfl⟩
  have hposf : 0 < ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ := by
    rw [hmaxeq]; exact hpos
  have honto : ∀ a : ℂ, ‖a‖ < 1 → ∃ x : X, f x = a :=
    injExtremal_onto hf hmax hposf
  -- the image is contained in the open disc (open mapping)
  have hlt : ∀ x : X, ‖f x‖ < 1 := by
    intro x
    by_contra hcon
    have h1le : 1 ≤ ‖f x‖ := not_lt.mp hcon
    have heq : ‖f x‖ = 1 := le_antisymm (hf.1.2.1 x) h1le
    set F : ℂ → ℂ := f ∘ (chartAt ℂ x).symm with hFdef
    set z : ℂ := (chartAt ℂ x) x with hzdef
    have hana : AnalyticAt ℂ F z := hf.1.1 x (mem_univ x)
    -- a chart ball around `x` inside the target
    have hzt : z ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source (mem_chart_source ℂ x)
    obtain ⟨ρc, hρc, hρcsub⟩ := Metric.isOpen_iff.mp (chartAt ℂ x).open_target _ hzt
    have hnotconst : ¬ (∀ᶠ y in 𝓝 z, F y = F z) := by
      intro hcon'
      obtain ⟨δ, hδ, hδsub⟩ := Metric.eventually_nhds_iff.mp hcon'
      set δ' : ℝ := min δ ρc with hδ'def
      have hδ'pos : 0 < δ' := lt_min hδ hρc
      set z' : ℂ := z + ((δ' / 2 : ℝ) : ℂ) with hz'def
      have hz'ne : z' ≠ z := by
        intro h
        have h2 : z + ((δ' / 2 : ℝ) : ℂ) = z + 0 := by rw [add_zero]; exact h
        have h3 : ((δ' / 2 : ℝ) : ℂ) = 0 := add_left_cancel h2
        have h4 : δ' / 2 = 0 := by exact_mod_cast h3
        linarith
      have hdz : dist z' z < δ := by
        rw [hz'def, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
        have : δ' / 2 ≤ δ / 2 := by rw [hδ'def]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
        linarith
      have hz't : z' ∈ (chartAt ℂ x).target := hρcsub (by
        rw [hz'def, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith)]
        have : δ' / 2 ≤ ρc / 2 := by rw [hδ'def]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
        linarith)
      have hFz' : F z' = F z := hδsub hdz
      have hyne : (chartAt ℂ x).symm z' ≠ x := by
        intro hy
        have h2 : (chartAt ℂ x) ((chartAt ℂ x).symm z') = (chartAt ℂ x) x := by rw [hy]
        rw [(chartAt ℂ x).right_inv hz't] at h2
        exact hz'ne (by rw [hzdef]; exact h2)
      have hfeq : f ((chartAt ℂ x).symm z') = f x := by
        have h2 : F z' = F z := hFz'
        simp only [hFdef, Function.comp_apply] at h2
        rw [h2]
        simp only [hzdef, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
      exact hyne (hf.2 hfeq)
    have hmap := hana.eventually_constant_or_nhds_le_map_nhds.resolve_left hnotconst
    have hIntF : F z ∈ interior (F '' Set.univ) := by
      have h1 : F '' Set.univ ∈ map F (𝓝 z) := by
        rw [Filter.mem_map]
        exact Filter.mem_of_superset Filter.univ_mem (by intro y _; exact ⟨y, mem_univ y, rfl⟩)
      exact mem_interior_iff_mem_nhds.mpr (hmap h1)
    have hsubimg : F '' Set.univ ⊆ f '' Set.univ := by
      rintro w ⟨y, -, rfl⟩
      exact ⟨(chartAt ℂ x).symm y, mem_univ _, rfl⟩
    have hInt : F z ∈ interior (f '' Set.univ) := interior_mono hsubimg hIntF
    have hmem : f x ∈ interior (f '' Set.univ) := by
      have h1 : F z = f x := by
        rw [hFdef, hzdef, Function.comp_apply,
          (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
      rw [← h1]
      exact hInt
    -- the image lies in the closed disc, so an interior point has modulus < 1
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hmem)
    have hfimage : f '' Set.univ ⊆ Metric.closedBall (0 : ℂ) 1 := by
      rintro w ⟨y, -, rfl⟩
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact hf.1.2.1 y
    have hball : Metric.ball (f x) ε ⊆ Metric.closedBall (0 : ℂ) 1 := hεsub.trans hfimage
    have hptmem : f x * (((1 + ε / 2 : ℝ)) : ℂ) ∈ Metric.ball (f x) ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hrew : f x * (((1 + ε / 2 : ℝ)) : ℂ) - f x = f x * (((ε / 2 : ℝ)) : ℂ) := by
        push_cast
        ring
      rw [hrew, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), heq]
      norm_num
      linarith
    have hpt := hball hptmem
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith), heq, one_mul] at hpt
    linarith
  have hode : ∀ x : X, deriv (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0 := fun x =>
    Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic (X := X) (Φ := f) hf.2
      (fun x => hf.1.1 x (mem_univ x)) (exists_ne_of_chartedSpace x)
  have hbij : Function.Bijective (fun x => (⟨f x, by
      show f x ∈ Metric.ball (0 : ℂ) 1
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hlt x⟩ : Helpers.DiscOpen)) := by
    constructor
    · intro p q hpq
      exact hf.2 (congrArg Subtype.val hpq)
    · intro w
      have hw : ‖(w : ℂ)‖ < 1 := by
        have h : (w : ℂ) ∈ Metric.ball (0 : ℂ) 1 := w.2
        rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h
        exact h
      obtain ⟨x, hx⟩ := honto (w : ℂ) hw
      exact ⟨x, Subtype.ext hx⟩
  exact uniformization_of_bijective_to_disc (fun x => by
      show f x ∈ Metric.ball (0 : ℂ) 1
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hlt x) hbij hf.1.1 hode


/-! ## The reduction of the uniformization theorem -/

/-- **The uniformization theorem follows from the dichotomy `(D′)`.**  If either the injective
extremal family is non-empty (Case A: then `X` is biholomorphic to `𝔻`, by
`uniformization_of_injective_into_disc`) or `X` is biholomorphic to `ℂ` (Case B), then the
conclusion of the uniformization theorem holds. -/
theorem uniformization_of_injective_or_plane {x₀ : X} [ConnectedSpace X]
    [SecondCountableTopology X] [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    (h : (injFamily x₀).Nonempty ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ)) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) := by
  rcases h with h | h
  · exact uniformization_of_injective_into_disc h
  · exact Or.inl h

end Submission
