/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/ClassCFromHonesty.lean` — the class-`C` invariant of
# `Pz (J_ε u)` from `SmoothOpen u + HkMem α 4 u + EpsMem α u` + the two analytic residuals

The lead's design `cbc/fts_e5swap_e4chapters.md` §B4 records that the class-`C` invariance of the
local step's Picard iteration (`XBall.classC` in `hkeepIter`/`hlimP`, and `EpsDatumP` in `hd`) does
*not* need to be routed through `StrongEps.BdryTraces_Jeps` (whose hypotheses are uniform ε-δ rates
of the *un-mollified* profile): `BdryTraces` asks only for **pointwise** limits, and its `z`-half
follows from `ℋ^{k+2}`-honesty alone (leaf (T1) = `EpsEngine.zTraces_T1`, proved), while its
`θ`-half at the pure-`D_z` slots is the structural θ-boundary item.

This module splits `BdryTraces` into its two halves (`ZTraces`, `TauTraces`), discharges
*everything* field by field, and isolates exactly two analytic residuals:

* `TauTraces α 10 (Pz (J_ε u))` — the θ-half of the boundary traces (the structural θ-boundary
  vanishing at rate `sin(2θ)^{(γ-1)/2}`, uniform in the second variable);
* `fsm` — all-order smoothness of the angular moment `F_*(Pz (J_ε u))` on `(0,∞)`.

Everything else — `norm`, `reg`, `mem`/`mem8`/`mem10`, the `tr`/`tr7` `z`-halves, `axis`, `l12`,
`thTr` — is *produced* from `SmoothOpen u`, `HkMem α 4 u` and `EpsMem α u`, via the unconditional
gain `TenOfEight.HkMem_Jeps_gain_pos`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EpsEngine.zTraces_T1
import Submission.Work.FTS.StrongEps.TenOfEight.GainAll
import Submission.Work.FTS.EpsEngine.FepsData
import Submission.Work.FTS.StrongEps.MolClassC
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.L12_Pz_Jeps_zero
import Submission.Work.FTS.StrongEps.PZero
import Submission.Work.FTS.EllipticEst.Fstar_contDiffOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two halves of `BdryTraces` -/

/-- **The `z`-half of `BdryTraces`**: the radial boundary limits of the weighted slots. -/
def ZTraces (α : ℝ) (k : ℕ) (f : Fn) : Prop :=
  ∀ a b : ℕ, a + b ≤ k → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
    Filter.Tendsto (fun z => z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun z => z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (nhds 0)

/-- **The θ-half of `BdryTraces`**: the angular boundary limits of the weighted slots. -/
def TauTraces (α : ℝ) (k : ℕ) (f : Fn) : Prop :=
  ∀ a b : ℕ, a + b ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ),
    Filter.Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a f z θ) ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a f z θ) ^ 2) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds 0)

/-- `BdryTraces` is the conjunction of its two halves. -/
theorem bdryTraces_iff_z_tau {α : ℝ} {k : ℕ} {f : Fn} :
    Work.FTS.Nonlin.BdryTraces α k f ↔ ZTraces α k f ∧ TauTraces α k f := by
  constructor
  · intro h
    exact ⟨fun a b hab => (h a b hab).1, fun a b hab => (h a b hab).2⟩
  · intro h a b hab
    exact ⟨h.1 a b hab, h.2 a b hab⟩

/-- Reassemble `BdryTraces` from its two halves. -/
theorem bdryTraces_of_z_tau {α : ℝ} {k : ℕ} {f : Fn} (hz : ZTraces α k f)
    (ht : TauTraces α k f) : Work.FTS.Nonlin.BdryTraces α k f :=
  fun a b hab => ⟨hz a b hab, ht a b hab⟩

theorem ZTraces.mono {α : ℝ} {k l : ℕ} {f : Fn} (hkl : k ≤ l) (h : ZTraces α l f) :
    ZTraces α k f := fun a b hab => h a b (le_trans hab hkl)

theorem TauTraces.mono {α : ℝ} {k l : ℕ} {f : Fn} (hkl : k ≤ l) (h : TauTraces α l f) :
    TauTraces α k f := fun a b hab => h a b (le_trans hab hkl)

/-- **The θ-half `ThetaTraces` of `ClassC` is implied by `TauTraces`** (its slots are the
`(a,b) = (0,s)` ones). -/
theorem thetaTraces_of_tauTraces {α : ℝ} {k : ℕ} {f : Fn} (h : TauTraces α k f) :
    Work.FTS.PhiStar.ThetaTraces α k f :=
  fun s hs z hz => h 0 s (by omega) z hz

/-! ## The `z`-half from `ℋ`-honesty (leaf (T1), proved) -/

/-- **The `z`-half of `BdryTraces` from `ℋ^{k+2}`-honesty** (the proved leaf
`Work.FTS.EpsEngine.zTraces_T1`, repackaged). -/
theorem zTraces_of_HkMem {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {k : ℕ} {f : Fn}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hk : Work.Spaces.HkMem α (k + 2) f) :
    ZTraces α k f := fun a b hab θ hθ =>
  Work.FTS.EpsEngine.zTraces_T1 hα hα1 k f hf hk a b hab θ hθ

/-! ## `axis` from the `z`-trace at `(a,b) = (0,0)` -/

/-- **The axis condition `g z θ / z → 0` from the `z`-trace at the `(0,0)`-slot.**  If
`z ↦ z (g z θ · w z)²` vanishes at `0⁺` for every interior angle `θ`, then `g z θ / z → 0`: for
`z < 1` the identity `z (g w)² = (g/z)² (1+z)⁴ / z` gives `(g/z)² ≤ z (g w)²`. -/
theorem axis_of_zTrace {α : ℝ} {g : Fn}
    (h : ZTraces α 0 g) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Filter.Tendsto (fun z => g z θ / z) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  intro θ hθ
  rw [Metric.tendsto_nhds]
  intro η hη
  have hη2 : 0 < η ^ 2 := pow_pos hη 2
  have htend := (h 0 0 (le_refl 0) θ hθ).1
  rw [Metric.tendsto_nhds] at htend
  have hz1 : ∀ᶠ z : ℝ in nhdsWithin 0 (Set.Ioi 0), z < 1 :=
    Filter.mem_of_superset (Filter.mem_inf_of_left (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
      (fun x hx => hx)
  have hz0 : ∀ᶠ z : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < z := self_mem_nhdsWithin
  filter_upwards [htend (min 1 (η ^ 2)) (lt_min one_pos hη2), hz1, hz0] with z hz hzlt hzpos
  -- `(g/z)² · ((1+z)⁴/z) < min 1 (η²)`, and `(1+z)⁴/z ≥ 1` for `z ∈ (0,1)`
  have hnn : 0 ≤ z * (g z θ * Work.Spaces.w z) ^ 2 := mul_nonneg hzpos.le (sq_nonneg _)
  have habslt : z * (g z θ * Work.Spaces.w z) ^ 2 < min 1 (η ^ 2) := by
    have hh : |z * (g z θ * Work.Spaces.w z) ^ 2| < min 1 (η ^ 2) := by
      have hz' := hz
      rw [Real.dist_eq, sub_zero] at hz'
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
        Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] using hz'
    rwa [abs_of_nonneg hnn] at hh
  have hw : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
  have hident : z * (g z θ * Work.Spaces.w z) ^ 2
      = (g z θ / z) ^ 2 * ((1 + z) ^ 4 / z) := by
    rw [hw]; field_simp
  have hval : (g z θ / z) ^ 2 * ((1 + z) ^ 4 / z) < min 1 (η ^ 2) := by
    rwa [hident] at habslt
  have hbig : 1 ≤ (1 + z) ^ 4 / z := by
    rw [le_div_iff₀ hzpos]
    have h1z : (0 : ℝ) < 1 + z := by linarith
    nlinarith [hzpos, hzlt, pow_pos h1z 4]
  have hsq : (g z θ / z) ^ 2 < η ^ 2 := by
    have h2 : (g z θ / z) ^ 2 * ((1 + z) ^ 4 / z) < η ^ 2 :=
      lt_of_lt_of_le hval (min_le_right _ _)
    nlinarith [sq_nonneg (g z θ / z), h2, hbig]
  rw [Real.dist_eq, sub_zero, ← Real.sqrt_sq_eq_abs]
  calc Real.sqrt ((g z θ / z) ^ 2) < Real.sqrt (η ^ 2) := Real.sqrt_lt_sqrt (sq_nonneg _) hsq
    _ = η := Real.sqrt_sq hη.le

/-! ## Elementary facts about `Pz (J_ε u)` -/

/-- `Pz (J_ε u)` vanishes off the open quadrant (the projection only subtracts a multiple of the
bump, supported in a box inside the quadrant). -/
theorem eq_zero_off_Q0_Pz_Jeps {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {u : Fn} {q : ℝ × ℝ}
    (hq : q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u) q.1 q.2 = 0 := by
  have hq' : ¬(0 < q.1 ∧ q.2 ∈ Set.Ioo 0 (Real.pi / 2)) := fun h => hq ⟨h.1, h.2⟩
  have hbump0 : Work.FTS.StrongEps.bump q.1 q.2 = 0 := by
    rw [Work.FTS.StrongEps.bump_eq_zero_iff]
    by_cases h1 : 0 < q.1
    · by_cases h2 : q.2 ∈ Set.Ioo 0 (Real.pi / 2)
      · exact absurd ⟨h1, h2⟩ hq'
      · rw [Set.mem_Ioo, not_and_or] at h2
        rcases h2 with h2 | h2
        · exact Or.inr (Or.inr (Or.inl (by linarith [Real.pi_pos])))
        · exact Or.inr (Or.inr (Or.inr (by linarith [Real.pi_pos])))
    · exact Or.inl (by linarith)
  rw [Work.FTS.StrongEps.Pz_apply, Work.FTS.StrongEps.Jeps_eq_zero ρ ε _ hq', hbump0]
  ring

/-- `normTh` is the identity on `Pz (J_ε u)`. -/
theorem normTh_Pz_Jeps {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {u : Fn} :
    Work.FTS.EllSol.normTh (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u))
      = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u) := by
  funext z θ
  by_cases h : θ ∈ Set.Ioo 0 (Real.pi / 2)
  · simp only [Work.FTS.EllSol.normTh, if_pos h]
  · rw [Work.FTS.EllSol.normTh, if_neg h]
    exact (eq_zero_off_Q0_Pz_Jeps (ρ := ρ) (ε := ε) (u := u) (q := (z, θ))
      (fun hc => h hc.2)).symm

/-- **`ℋ^k`-honesty of the projected mollified profile at any order `k ≥ 1`, from `ℋ¹`-honesty of
the raw profile.**  The unconditioned gain `TenOfEight.HkMem_Jeps_gain_pos` raises any order `≥ 1`
to any higher order, and `Pz` only adds a multiple of the bump. -/
theorem hkMem_Pz_Jeps_of_gain {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {ε : ℝ} (hε : 0 < ε) {u : Fn} {k : ℕ} (hk : 1 ≤ k)
    (hsu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmu : Work.Spaces.HkMem α k u) (m : ℕ) :
    Work.Spaces.HkMem α (k + m) (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)) := by
  have hJ : Work.Spaces.HkMem α (k + m) (Work.FTS.StrongEps.Jeps ρ ε u) :=
    Work.FTS.StrongEps.TenOfEight.HkMem_Jeps_gain_pos hρ α hα.1 hα.2 k m hk ε hε u hsu hmu
  have hJsmo : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε u) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hsu
  exact HkMem_Pz_of hJsmo hJ

/-- **The class-`C` clause of `Pz (J_ε u)`, from `SmoothOpen u + HkMem α 4 u + EpsMem α u` and TWO
analytic residuals.**  Every field is produced except

* `TauTraces α 10 (Pz (J_ε u))` — the θ-half of the boundary traces (structural: the θ-boundary
  vanishing of the scheme's right-hand side at rate `sin(2θ)^{(γ-1)/2}`), and
* `fsm` — all-order smoothness on `(0,∞)` of the angular moment `F_*(Pz (J_ε u))`.

The `z`-halves of `tr`, `tr7` come from the proved leaf `zTraces_T1` (with `ℋ⁸`/`ℋ⁹`-honesty of
`Pz (J_ε u)`, both derived here from the raw `ℋ⁴`), `axis` from the `(0,0)` `z`-trace,
`mem`/`mem8`/`mem10` and `thTr` from the gain, and `l12` from `L12_Pz_Jeps_zero`. -/
theorem classC_Pz_Jeps_of_parts {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) (hα1 : α ≤ 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {u : Fn}
    (hsu : Work.FTS.EllipticEst.SmoothOpen u) (hmu : Work.Spaces.HkMem α 4 u)
    (hme : Work.FTS.StrongEps.EpsMem α u)
    (htau : TauTraces α 10 (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)))
    (hfsm : ∀ m : ℕ, ContDiffOn ℝ m
      (Work.Elliptic.Fstar (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)))
      (Set.Ioi 0)) :
    Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)) := by
  have hsuQ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall u).mp hsu
  have hreg : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)) :=
    smoothOpen_Pz_of_smoothOpen (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hsuQ)
  have h1u : Work.Spaces.HkMem α 1 u :=
    Work.FTS.OpenPkg.HkMem_mono_open hsu 1 (by norm_num) hmu
  have hgm : ∀ m : ℕ, 1 ≤ m →
      Work.Spaces.HkMem α m (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)) := by
    intro m hm
    have hm1 : m = 1 + (m - 1) := by omega
    rw [hm1]
    exact hkMem_Pz_Jeps_of_gain hρ hα hε (by norm_num : 1 ≤ 1) hsuQ h1u (m - 1)
  refine
    { norm := normTh_Pz_Jeps
      reg := hreg
      mem := hgm 7 (by norm_num)
      mem8 := hgm 8 (by norm_num)
      mem10 := hgm 10 (by norm_num)
      tr := bdryTraces_of_z_tau (zTraces_of_HkMem hα.1 hα1 hreg (hgm 8 (by norm_num)))
        (TauTraces.mono (by norm_num) htau)
      tr7 := bdryTraces_of_z_tau (zTraces_of_HkMem hα.1 hα1 hreg (hgm 9 (by norm_num)))
        (TauTraces.mono (by norm_num) htau)
      fsm := hfsm
      axis := axis_of_zTrace (zTraces_of_HkMem hα.1 hα1 hreg (hgm 2 (by norm_num)))
      l12 := Work.FTS.StrongEps.EpsSqTools.LinAux.L12_Pz_Jeps_zero ρ hρ hα ⟨hε, hε1⟩
        hsuQ hme
      thTr := thetaTraces_of_tauTraces htau }

end Work.FTS.EpsEngine
