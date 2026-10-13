/-
Copyright: work module for the Elgindi finite-time singularity project.

# `N6Trans/Hon/Defs`: the honest (open-quadrant) bundles of the level-4 transport clauses

The frozen level-4 transport clauses (`VocabO.T2Clause` and its per-slot engine
`TransportS.T2Sup.slotAbsBound`) are stated on the class `T2SG α g = RegQ α 4 g ∧ HkMem α 5 g ∧
DecayAll 4 g`, whose `RegQ`-component carries `SmoothQuad` (smoothness on the *half-strip*
`Ioi (-1) ×ˢ Ioo 0 (π/2)`) and `BdryTraces α 4 g` (the pointwise vanishing of
`z·(D_z^bD_θ^a g · w)²` at `z → 0⁺` and `z → ∞`).  The *honest* clauses of the level-six
chapter (`StrongPersist.T2Clause6` and the three nodes `N6Trans.IP4T*Honest`) replace that
bundle by

`SmoothOpen g ∧ HkMem α 4 g ∧ HkMem α 5 g ∧ DecayAll 4 g`,

i.e. smoothness only on the *open* quadrant plus one extra order of honesty.

This file fixes that bundle (`HonG`), the (unchanged) `f`-side bundle `HonF`, the two
pointwise facts the honest route can use in place of the frozen ones

* `pwAny_sup` — the honest order-`≤ 2` sup bound `|mixed b a g z θ| ≤ C/√(γ-1)·|g|_{ℋ⁴}`
  (immediate from `OpenPkg.ProdOpen.PwAny`, the open-quadrant form of Elgindi's
  `SecondDerivativesBounded`; the frozen route used `T2Qaux.supQ_T2Q`, which needs
  `SmoothQuad` and `DecayAll`);
* `prim_limit_zero` — the abstract form of `H2.ZibpLimit`: a primitive bounded by
  `c · z · F(z)` with `∫ F < ∞` can only have the limit `0` at `0⁺` and at `∞`.  This is what
  replaces `BdryTraces` in the radial integration by parts;

and the two `Prop`-valued statements of the two genuinely new or ported pieces:

* `TopSlotHonProp` — the honest radial integration by parts for the five top slots
  (`a + b = 4`), the replacement of `TransportS.T2Sup.Main.topSlotBound` (whose boundary
  hypothesis is `BdryTraces`);
* `DelicateHonProp` — the honest form of `TransportS.T2Sup.delicateBound` (the paper's
  delicate term), i.e. the same estimate with the honest `g`-bundle.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.OpenPkg.ProdOpen.PwOpen
import Submission.Work.FTS.H2.ZibpLimit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The two bundles -/

/-- **The honest `g`-side bundle** of the level-4 transport clauses: `C^∞` on the open
quadrant, honesty in `ℋ⁴` and `ℋ⁵`, and the mixed radial decay of order `4`. -/
structure HonG (α : ℝ) (g : Fn) : Prop where
  sm : Work.FTS.EllipticEst.SmoothOpen g
  hk4 : Work.Spaces.HkMem α 4 g
  hk5 : Work.Spaces.HkMem α 5 g
  dec : Work.Spaces.DecayAll 4 g

/-- **The `f`-side bundle** of the level-4 transport clauses (verbatim `T2SF`). -/
def HonF (α : ℝ) (f : Fn) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen f ∧ Work.Spaces.HkMem α 4 f ∧
    Work.FTS.VocabO.CoefThMem 1 f

theorem HonF.sm {α : ℝ} {f : Fn} (h : HonF α f) : Work.FTS.EllipticEst.SmoothOpen f := h.1
theorem HonF.hk {α : ℝ} {f : Fn} (h : HonF α f) : Work.Spaces.HkMem α 4 f := h.2.1
theorem HonF.coef {α : ℝ} {f : Fn} (h : HonF α f) : Work.FTS.VocabO.CoefThMem 1 f := h.2.2

/-- The frozen `f`-side bundle is the honest one. -/
theorem honF_of_T2SF {α : ℝ} {f : Fn} (h : Work.FTS.TransportS.T2SF α f) : HonF α f :=
  ⟨h.1, h.2.1, h.2.2⟩

/-- The honest `g`-bundle supplies the open-quadrant smoothness of every mixed slot. -/
theorem HonG.mixed {α : ℝ} {g : Fn} (h : HonG α g) (j i : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.mixed j i g) := h.sm.mixed j i

/-! ## The honest order-`≤ 2` sup bound -/

/-- **The honest sup bound.**  For `g` in the open-quadrant class `HQo α 4 = SmoothOpen ∧
HkMem α 4`, every mixed slot of order `≤ 2` is pointwise bounded by
`√C / √(γ-1) · |g|_{ℋ⁴}` with a universal `C` — the open-quadrant form of Elgindi's
`SecondDerivativesBounded` (`OpenPkg.ProdOpen.PwAny`).  This replaces the frozen
`T2Qaux.supQ_T2Q` in the honest route. -/
theorem pwAny_sup : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ) (b a : ℕ),
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
    a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a g z θ|
        ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 g := by
  obtain ⟨C, hC, h⟩ := Work.FTS.OpenPkg.ProdOpen.PwAny
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, ?_⟩
  intro α g b a hα hα1 hsm hm hab z θ hz hθ hθ2
  have hg1 : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hsq := h α g b a hα hα1 hsm hm hab z hz θ ⟨hθ, hθ2⟩
  have hXn : Work.Spaces.HkSq α 4 g = (Work.Spaces.HkNorm α 4 g) ^ 2 := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 g)]
  rw [hXn, div_mul_eq_mul_div] at hsq
  have hsq' : (Work.Spaces.mixed b a g z θ) ^ 2
      ≤ (Real.sqrt C / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.Spaces.HkNorm α 4 g) ^ 2 := by
    have hmul : C * (Work.Spaces.HkNorm α 4 g) ^ 2 / (Work.Spaces.gam α - 1)
        = (Real.sqrt C / Real.sqrt (Work.Spaces.gam α - 1)
            * Work.Spaces.HkNorm α 4 g) ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt hC.le, Real.sq_sqrt hg1.le]
      ring
    linarith [hsq, hmul.le, hmul.ge]
  calc |Work.Spaces.mixed b a g z θ|
      = Real.sqrt ((Work.Spaces.mixed b a g z θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((Real.sqrt C / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.Spaces.HkNorm α 4 g) ^ 2) := Real.sqrt_le_sqrt hsq'
    _ = Real.sqrt C / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 g :=
        Real.sqrt_sq (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          (Work.Spaces.HkNorm_nonneg α 4 g))

/-! ## The abstract vanishing of a dominated primitive -/

/-- **Abstract `ZibpLimit`.**  If `|u z| ≤ c · z · F z` for `z > 0` with `c ≥ 0` and `F`
integrable on `Iz`, then `u` can only have the limit `0` at `0⁺` and at `+∞`.  (A non-zero
limit forces `F z ≥ C/z` on a ray, resp. near `0⁺`, contradicting the integrability of `F`.) -/
theorem prim_limit_zero {u F : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ z : ℝ, 0 < z → |u z| ≤ c * z * F z)
    (hF : MeasureTheory.IntegrableOn F Work.Spaces.Iz) :
    (∀ L : ℝ, Filter.Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 L) → L = 0) ∧
      (∀ L : ℝ, Filter.Tendsto u Filter.atTop (𝓝 L) → L = 0) := by
  have hev_of : ∀ {L : ℝ} {l : Filter ℝ}, Filter.Tendsto u l (𝓝 L) → L ≠ 0 →
      ∀ᶠ z in l, |L| / 2 ≤ |u z| := by
    intro L l hL hne
    have hpos : 0 < |L| := abs_pos.2 hne
    have hball : Metric.ball L (|L| / 2) ∈ 𝓝 L := Metric.ball_mem_nhds L (by linarith)
    filter_upwards [hL hball] with z hz
    have hz' : |u z - L| < |L| / 2 := by
      have h1 := Metric.mem_ball.1 hz
      rwa [Real.dist_eq] at h1
    have h2 : |L| - |u z| ≤ |L - u z| := abs_sub_abs_le_abs_sub L (u z)
    rw [abs_sub_comm L (u z)] at h2
    linarith
  have hstep : ∀ {L z : ℝ}, 0 < c → 0 < z → |L| / 2 ≤ |u z| → (|L| / (2 * c)) / z ≤ F z := by
    intro L z hcp hz hb
    have h1 : |L| / 2 ≤ c * z * F z := le_trans hb (h z hz)
    have h2 : |L| ≤ 2 * c * z * F z := by linarith
    have h2' : |L| / (2 * c) ≤ z * F z := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [h2]
    rw [div_le_iff₀ hz]; linarith [h2']
  constructor
  · intro L hL
    by_cases hc0 : c = 0
    · subst hc0
      refine tendsto_nhds_unique hL ?_
      refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      have h1 : |u z| ≤ 0 := by simpa using h z hz
      exact (abs_eq_zero.1 (le_antisymm h1 (abs_nonneg _))).symm
    · by_contra hne
      have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      have hev := hev_of hL hne
      obtain ⟨ε, hε, hsub⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.1 hev
      exact (Work.FTS.H2.not_integrableOn_Ici_of_le_inv_nearZero
        (c := |L| / (2 * c)) (ε := ε) (div_pos (abs_pos.2 hne) (by positivity)) hε
        (fun z hz0 hzε => hstep hcpos hz0 (hsub ⟨hz0, hzε⟩))) hF
  · intro L hL
    by_cases hc0 : c = 0
    · subst hc0
      refine tendsto_nhds_unique hL ?_
      refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
      filter_upwards [Filter.Ioi_mem_atTop (0 : ℝ)] with z hz
      have h1 : |u z| ≤ 0 := by simpa using h z hz
      exact (abs_eq_zero.1 (le_antisymm h1 (abs_nonneg _))).symm
    · by_contra hne
      have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      have hev := hev_of hL hne
      obtain ⟨Z, hZ⟩ := Filter.eventually_atTop.1 hev
      exact (Work.FTS.H2.not_integrableOn_Ici_of_le_inv_atTop
        (c := |L| / (2 * c)) (Z := max Z 1) (div_pos (abs_pos.2 hne) (by positivity))
        (by positivity) (fun z hz => hstep hcpos
          (lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hz))
          (hZ z (le_trans (le_max_left _ _) hz)))) hF

/-! ## The two `Prop`s -/

/-- **The honest top-slot radial integration by parts** (`a + b = 4`).  For `0 < α ≤ 1`,
`f` with open-quadrant smoothness and the two pointwise bounds `|f|, |D_z f| ≤ Mf`, and `g`
in the honest bundle, the top pairing with the canonical weight `canonW q` (`q ≤ γ`, and
`q ≤ η` when `a = 0`) is bounded by `C·Mf·|g|²_{ℋ⁴}`.

This is the replacement of `TransportS.T2Sup.Main.topSlotBound`, whose boundary hypothesis is
the per-angle vanishing `z (D_z^bD_θ^a g · w)² → 0` (`BdryTraces`); the honest proof uses
`HkMem α 4 g`/`HkMem α 5 g` (integrability of the slots of order `4` and `5`) instead. -/
def TopSlotHonProp : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) (q Mf : ℝ),
    0 < α → α ≤ 1 → 0 ≤ Mf → a + b = 4 → (a = 0 → q ≤ Work.Spaces.eta) →
    q ≤ Work.Spaces.gam α →
    Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
    Work.Spaces.DecayAll 4 g → Work.Spaces.HkMem α 4 g → Work.Spaces.HkMem α 5 g →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf) →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |Work.Spaces.Dz f z θ| ≤ Mf) →
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ|
      ≤ C * Mf * Work.Spaces.HkSq α 4 g

/-- **The honest delicate bound** (the paper's delicate term of the transport estimate): the
same estimate as `TransportS.T2Sup.DelicateProp` with the honest `g`-bundle in place of
`T2SG α g`. -/
def DelicateHonProp : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (α q : ℝ) (f g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → 0 ≤ q → q ≤ Work.Spaces.gam α →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.VocabO.CoefThMem 1 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
    Work.Spaces.HkMem α 5 g → Work.Spaces.DecayAll 4 g →
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
          * |Work.Spaces.mixed 3 1 g z θ|)
      ≤ C * α ^ (-(1 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
          * Work.Spaces.HkSq α 4 g

end Work.FTS.StrongPersist.N6Trans.Hon
