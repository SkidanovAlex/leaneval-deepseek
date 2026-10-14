import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.hkSqFepsSub_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.regFromVolterra
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le
import Submission.Work.FTS.StrongEps.IsEpsSolPQ.EpsSq_intervalIntegral_le_sqrt
import Submission.Work.FTS.StrongEps.IsEpsSolPQ.epsSolP_volterra
import Submission.Work.FTS.StrongEps.MolClassC
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.RhsCont
import Submission.Work.FTS.StrongEps.TenOfEight.GainAll
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongPersist.H6Aux.E2Facts
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.TransportS.t2SlotGuarded
import Submission.Work.FTS_BSIdentP.Slim.TendstoPhiOddPi
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_bounds
import Submission.Work.FTS_RegExport.RXVP.NoHdat.velPkgEasy_noHdat
import Submission.Work.FTS_RegExport.RXVP.thLip
import Submission.Work.FTS_RegExport.RXVP3.velPkgOpen_of_vopLower
import Submission.Work.FTS_RegExport.RXVPMain
import Submission.Work.StabilityFar.Decay.KernelDefs
-- ===== merged: Submission.Work.FTS.EpsEngine.ClassCFromHonesty =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.Feps_data_of_xball8 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The order-`8` data of `Feps` on the `XBall` class.**  There is a constant `Ce8 > 0`,
depending on `α, ε, C₀, Ce, Cs, R` (but *not* on the profile `u`), such that for every `u` in the
`XBall` invariant the right-hand side `Feps α ρ ε Φs E u` is `SmoothOpen`, `ℋ⁸`-honest, and of
`ℋ⁸`-size at most `Ce8`. -/
theorem Feps_data_of_xball8 {α C₀ Ce Cs R ε : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) :
    ∃ Ce8 : ℝ, 0 < Ce8 ∧ ∀ u : Work.FTS.Galerkin.Fn,
      Work.FTS.EpsEngine.XBall α ρ ε R C₀ u →
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EpsEngine.Feps α ρ ε Φs E u) ∧
      Work.Spaces.HkMem α 8 (Work.FTS.EpsEngine.Feps α ρ ε Φs E u) ∧
      Work.Spaces.HkNorm α 8 (Work.FTS.EpsEngine.Feps α ρ ε Φs E u) ≤ Ce8 := by
  -- ## the order-`8` counterflow constant of `Pz ∘ J_ε`
  obtain ⟨CJ, hCJpos, hCJ⟩ := Work.FTS.EpsEngine.HkSq_JepsPz_le8 ρ hρ
  have hratio : 0 ≤ CJ / ε := div_nonneg hCJpos.le hε.le
  -- ## the profile data of `profRHS` and its `ε`-space size (both uniform on the `XBall` class)
  obtain ⟨CX, hCX, hX⟩ :=
    Work.FTS.StrongEps.EpsRLX.XDataClean (α := α) (Ce := Ce) (Cs := Cs) (C₀ := C₀)
      (B := Real.sqrt (CJ * (CJ / ε) ^ (2 * 6) * R)) (Φs := Φs) (E := E)
      hα hEll hstar hml (Real.sqrt_nonneg _)
  obtain ⟨RP, hRP, hProf⟩ :=
    Work.FTS.StrongEps.EpsRLX.ProfRHSEpsData (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (B := Real.sqrt (CJ * (CJ / ε) ^ (2 * 6) * R)) (Φs := Φs) (E := E)
      hα hEll hstar hml (Real.sqrt_nonneg _)
  refine ⟨Real.sqrt (CJ * (CJ / ε) ^ (2 * 8) * RP), ?_, ?_⟩
  · exact Real.sqrt_pos.mpr (mul_pos (mul_pos hCJpos (pow_pos (div_pos hCJpos hε) _)) hRP)
  · intro u hu
    -- ## the `XBall` data
    have husmo : Work.FTS.EllipticEst.SmoothOpen u := hu.smoothOpen
    have humem : Work.FTS.StrongEps.EpsMem α u := hu.mem
    have husq : Work.FTS.StrongEps.EpsSq α u ≤ R := hu.sq_le
    have huC : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)) :=
      hu.classC
    have huball : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u))
        ≤ C₀ * α ^ 2 := hu.ball
    set W : Fn := Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u) with hWdef
    -- ## the uniform `ℋ⁶`-bound of `W` (order `6 ≤ 8` of the counterflow)
    have hW6 : Work.Spaces.HkNorm α 6 W
        ≤ Real.sqrt (CJ * (CJ / ε) ^ (2 * 6) * R) := by
      have h := hCJ α hα ε hε hε1 6 (by norm_num) u husmo humem
      have hle : Work.Spaces.HkSq α 6 W ≤ CJ * (CJ / ε) ^ (2 * 6) * R :=
        le_trans h (mul_le_mul_of_nonneg_left husq
          (mul_nonneg hCJpos.le (pow_nonneg hratio _)))
      rw [Work.Spaces.HkNorm]
      exact Real.sqrt_le_sqrt hle
    -- ## the pre-mollified right-hand side
    set g : Fn := Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W with hgdef
    obtain ⟨hgsmo, hgmem4, -⟩ := hX (W := W) huC huball hW6
    obtain ⟨hgmeme, hgsq⟩ := hProf (W := W) huC huball hW6
    have hgsmQuad : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.StrongEps.Quad :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hgsmo
    -- ## the mollified gain `ℋ⁴ → ℋ⁸`
    have hJ8 : Work.Spaces.HkMem α 8 (Work.FTS.StrongEps.Jeps ρ ε g) :=
      Work.FTS.StrongEps.TenOfEight.HkMem_Jeps_gain_pos hρ α hα.1 hα.2 4 4 (by norm_num)
        ε hε g hgsmQuad hgmem4
    have hJsmo : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε g) :=
      Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hgsmQuad
    have hFeps : Feps α ρ ε Φs E u = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε g) :=
      rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hFeps]
      exact Work.FTS.EpsEngine.smoothOpen_Pz_of_smoothOpen hJsmo
    · rw [hFeps]
      exact Work.FTS.EpsEngine.HkMem_Pz_of hJsmo hJ8
    · rw [hFeps, Work.Spaces.HkNorm]
      refine Real.sqrt_le_sqrt ?_
      exact (hCJ α hα ε hε hε1 8 (by norm_num) g hgsmo hgmeme).trans
        (mul_le_mul_of_nonneg_left hgsq (mul_nonneg hCJpos.le (pow_nonneg hratio _)))

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.RHSDataPerz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option linter.unusedVariables false


end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.SmoothOpenIterProd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps
open Work.FTS.StrongEps.EpsLocalPStar

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The time-Lipschitz bound of the `(n+1)`-st Picard curve** (the `hEq` input of the lead's
Fubini lemma, in the ordered form): the increment of the `(n+1)`-st iterate over `(a,b] ⊆ [0,δ]` is
the parametric integral of the level-`n` curve, so the Minkowski bound gives
`EpsSq (w_a − w_b) ≤ (b−a)²·L`. -/
theorem EpsSq_iter_succ_sub_le {α L δ : ℝ} {F : Fn → Fn} {h₀ : Fn} {P : Fn → Prop} (n : ℕ)
    (hL : 0 ≤ L)
    (hPn : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → P (slice (iter F h₀ n) τ))
    (hbd : ∀ u : Fn, P u → EpsMem α (F u) ∧ EpsSq α (F u) ≤ L)
    (haesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => F (slice (iter F h₀ n) p.1) p.2.1 p.2.2)
      (((volume : Measure ℝ).restrict (Set.Icc 0 δ)).prod volume))
    (hcont_n : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ContinuousOn (fun s : ℝ => F (slice (iter F h₀ n) s) z θ) (Set.Icc 0 δ)) :
    ∀ a ∈ Set.Icc 0 δ, ∀ b ∈ Set.Icc 0 δ, a ≤ b →
      EpsSq α (fun z θ => slice (iter F h₀ (n + 1)) a z θ
        - slice (iter F h₀ (n + 1)) b z θ) ≤ (b - a) * ((b - a) * L) := by
  intro a ha b hb hab
  have hbound := EpsSq_integral_iter_le (α := α) (L := L) (δ := δ) (F := F) (h₀ := h₀) (P := P)
    n hL hPn hbd haesm
  have hiter : ∀ τ z' θ' : ℝ, slice (iter F h₀ (n + 1)) τ z' θ'
      = h₀ z' θ' + ∫ t in (0 : ℝ)..τ, F (slice (iter F h₀ n) t) z' θ' := by
    intro τ z' θ'
    rw [iter_succ F h₀ n]
    simp only [Work.FTS.Galerkin.slice_apply]
  have hdiff : ∀ᵐ p ∂DomM,
      (fun z' θ' => slice (iter F h₀ (n + 1)) a z' θ'
        - slice (iter F h₀ (n + 1)) b z' θ') p.1 p.2
        = (fun z' θ' => -∫ t in a..b, F (slice (iter F h₀ n) t) z' θ') p.1 p.2 := by
    filter_upwards [ae_open_DomM] with p hp
    obtain ⟨hz', hθ'0, hθ'1⟩ := hp
    have hc : ContinuousOn (fun t : ℝ => F (slice (iter F h₀ n) t) p.1 p.2)
        (Set.Icc 0 δ) := hcont_n p.1 p.2 hz' hθ'0 hθ'1
    rw [hiter a p.1 p.2, hiter b p.1 p.2]
    have h1 : IntervalIntegrable (fun t : ℝ => F (slice (iter F h₀ n) t) p.1 p.2) volume 0 a :=
      ContinuousOn.intervalIntegrable_of_Icc ha.1 (hc.mono (Set.Icc_subset_Icc_right ha.2))
    have h2 : IntervalIntegrable (fun t : ℝ => F (slice (iter F h₀ n) t) p.1 p.2) volume a b :=
      ContinuousOn.intervalIntegrable_of_Icc hab
        (hc.mono (fun x hx => ⟨le_trans ha.1 hx.1, le_trans hx.2 hb.2⟩))
    have hadj := (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
    rw [hadj]
    ring
  have h0 := EpsSq_congr_ae (α := α)
    (f := fun z' θ' => slice (iter F h₀ (n + 1)) a z' θ'
      - slice (iter F h₀ (n + 1)) b z' θ')
    (g := fun z' θ' => -∫ t in a..b, F (slice (iter F h₀ n) t) z' θ') hdiff
  rw [h0, EpsSq_neg2]
  exact hbound a ha b hb hab

/-- **The time-Lipschitz bound `hEq`** in the shape consumed by the lead's
`SORuling.smoothOpen_iter_succ_XBall` (`Lw = L`): `EpsSq (w_s − w_t) ≤ L (s−t)²` for all
`s, t ∈ [0,δ]`. -/
theorem EpsSq_iter_sub_sq_le {α Cpt L δ : ℝ} {F : Fn → Fn} {h₀ : Fn} {P : Fn → Prop} (n : ℕ)
    (hδ : 0 < δ) (hL : 0 ≤ L) (hCpt : 0 ≤ Cpt)
    (hP : ∀ m : ℕ, m ≤ n → ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → P (slice (iter F h₀ m) τ))
    (hcontP : ∀ u : Fn, P u → ContinuousOn (fun q : ℝ × ℝ => F u q.1 q.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hzeroP : ∀ u : Fn, P u → ∀ q : ℝ × ℝ,
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → F u q.1 q.2 = 0)
    (hbd : ∀ u : Fn, P u → EpsMem α (F u) ∧ EpsSq α (F u) ≤ L)
    (hpt : ∀ u v : Fn, P u → P v → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F u z θ - F v z θ| ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => u z θ - v z θ))) :
    ∀ s ∈ Set.Icc 0 δ, ∀ t ∈ Set.Icc 0 δ, EpsSq α (fun z θ =>
      slice (iter F h₀ n) s z θ - slice (iter F h₀ n) t z θ) ≤ L * (s - t) ^ 2 := by
  intro s hs t ht
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- level `0`: the curve is constant (the iterate `0` is `h₀`)
    subst hn
    have hz : (fun z θ => slice (iter F h₀ 0) s z θ - slice (iter F h₀ 0) t z θ)
        = fun _ _ => (0 : ℝ) := by
      funext z θ
      simp only [iter_zero, Work.FTS.Galerkin.slice_apply, sub_self]
    rw [hz, EpsSq_zero]
    exact mul_nonneg hL (sq_nonneg _)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hcont_meas := iter_cont_meas_prefix (α := α) (Cpt := Cpt) (L := L) (δ := δ)
      (F := F) (h₀ := h₀) (P := P) k hδ hL hCpt (fun m hm => hP m (by omega))
      hcontP hzeroP hbd hpt
    obtain ⟨hcontAll, haesmAll⟩ := hcont_meas
    rcases le_total s t with hle | hle
    · refine le_trans (EpsSq_iter_succ_sub_le (α := α) (L := L) (δ := δ) (F := F) (h₀ := h₀)
        (P := P) k hL (hP k (by omega)) hbd (haesmAll k (by omega))
        (hcontAll k (by omega)) s hs t ht hle) (le_of_eq ?_)
      rw [show (t - s) * ((t - s) * L) = L * (s - t) ^ 2 by ring]
    · have h := EpsSq_iter_succ_sub_le (α := α) (L := L) (δ := δ) (F := F) (h₀ := h₀)
        (P := P) k hL (hP k (by omega)) hbd (haesmAll k (by omega))
        (hcontAll k (by omega)) t ht s hs hle
      have heq : (fun z θ => slice (iter F h₀ (k + 1)) s z θ
          - slice (iter F h₀ (k + 1)) t z θ)
          = fun z θ => -(slice (iter F h₀ (k + 1)) t z θ
            - slice (iter F h₀ (k + 1)) s z θ) := by
        funext z θ; ring
      rw [heq, EpsSq_neg2]
      refine le_trans h (le_of_eq ?_)
      rw [show (s - t) * ((s - t) * L) = L * (s - t) ^ 2 by ring]

/-- **The `SmoothOpen` clause of `hkeepIter`, in the prefix form needed by its induction**: if the
levels `≤ n` of the Picard iteration of `Feps` all lie in `XBall` on `[0,δ]` (and the two gates of
`Feps` hold on `XBall`), then every slice of the `(n+1)`-st iterate is `SmoothOpen`.  This is the
lead's `SORuling.smoothOpen_iter_succ_XBall` with its two remaining inputs produced by
`iter_cont_meas_prefix` (`hFint`) and `EpsSq_iter_sub_sq_le` (`hEq`, with `Lw = L`). -/
theorem smoothOpen_iter_succ_XBall_prefix {α C₀ R Ce Cs Cpt L δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {ε : ℝ} {h₀ : Fn} (n : ℕ)
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : MuLamOK α C₀ Φs E) (hR : 0 ≤ R)
    (hδ : 0 < δ) (hL : 0 ≤ L) (hCpt : 0 ≤ Cpt)
    (h0 : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hP : ∀ m : ℕ, m ≤ n → ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → XBall α ρ ε R C₀
      (slice (iter (Feps α ρ ε Φs E) h₀ m) τ))
    (hcontP : ∀ u : Fn, XBall α ρ ε R C₀ u → ContinuousOn (fun q : ℝ × ℝ =>
      Feps α ρ ε Φs E u q.1 q.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hzeroP : ∀ u : Fn, XBall α ρ ε R C₀ u → ∀ q : ℝ × ℝ,
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → Feps α ρ ε Φs E u q.1 q.2 = 0)
    (hbd : ∀ u : Fn, XBall α ρ ε R C₀ u →
      EpsMem α (Feps α ρ ε Φs E u) ∧ EpsSq α (Feps α ρ ε Φs E u) ≤ L)
    (hpt : ∀ u v : Fn, XBall α ρ ε R C₀ u → XBall α ρ ε R C₀ v →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ|
          ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => u z θ - v z θ))) :
    ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      Work.FTS.EllipticEst.SmoothOpen (slice (iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ) := by
  obtain ⟨hcontAll, _haesmAll⟩ :=
    iter_cont_meas_prefix (α := α) (Cpt := Cpt) (L := L) (δ := δ)
      (F := Feps α ρ ε Φs E) (h₀ := h₀) (P := fun u => XBall α ρ ε R C₀ u)
      n hδ hL hCpt hP hcontP hzeroP hbd hpt
  have hEq := EpsSq_iter_sub_sq_le (α := α) (Cpt := Cpt) (L := L) (δ := δ)
    (F := Feps α ρ ε Φs E) (h₀ := h₀) (P := fun u => XBall α ρ ε R C₀ u)
    n hδ hL hCpt hP hcontP hzeroP hbd hpt
  have hFint : ∀ τ ∈ Set.Icc 0 δ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      IntervalIntegrable (fun s => Feps α ρ ε Φs E
        (slice (iter (Feps α ρ ε Φs E) h₀ n) s) z θ) volume 0 τ := by
    intro τ hτ z θ hz hθ
    exact ContinuousOn.intervalIntegrable_of_Icc hτ.1
      (((hcontAll n le_rfl) z θ hz hθ.1 hθ.2).mono (Set.Icc_subset_Icc_right hτ.2))
  intro τ hτ
  exact SORuling.smoothOpen_iter_succ_XBall (α := α) (C₀ := C₀) (R := R) (Ce := Ce) (Cs := Cs)
    (Lw := L) (δ := δ) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (h₀ := h₀)
    hα hρ hε hε1 hEll hstar hml hR hL n h0 (fun s hs => hP n le_rfl s hs) hEq hFint hτ

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.aesm_epsRHSP_fam_of_gate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open MeasureTheory Set Filter
open scoped Real Topology
open Work.FTS.Galerkin (Fn)

/-- **The pointwise Lipschitz gate of `Feps` on the `X`-ball**: there is `C > 0` with
`|Feps u z θ − Feps v z θ| ≤ C √(EpsSq (u−v))` on the open quadrant, for all `u, v ∈ XBall`.

This is `profRHS_sub_sup_le_Sq` with its hypotheses read off the `XBall` structure (and the
`τ`-free form `Feps u = epsRHPSlice … 0 u`, `Feps_eq_epsRHPSlice`). -/
theorem pt_of_XBall {α C₀ R Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : Fn, XBall α ρ ε R C₀ u → XBall α ρ ε R C₀ v →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ|
        ≤ C * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
  obtain ⟨C, hCpos, hC⟩ :=
    Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le_Sq (α := α) (C₀ := C₀) (Ce := Ce)
      (Cs := Cs) (R := R) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε)
      hα hρ hε hε1 hEll hstar hml hR
  refine ⟨C, hCpos, fun u v hu hv z θ hz hθ1 hθ2 => ?_⟩
  have h1 := hC hu.smoothOpen hv.smoothOpen hu.mem hu.sq_le hv.mem hv.sq_le
    hu.classC hv.classC hu.ball hv.ball z θ hz hθ1 hθ2
  rwa [← Feps_eq_epsRHPSlice α ρ ε Φs E 0 u, ← Feps_eq_epsRHPSlice α ρ ε Φs E 0 v] at h1


end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.EpsEngine.slice_iter_succ_mollForm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Convolution
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Fubini for the projected mollified right-hand side.**  If the integrand has the (pointwise, on
the open quadrant) mollified form `F (slice W s) = J_ε (G s) − c s · bump` for `s ∈ [0,τ]`, and the
family `G` is jointly continuous in the log coordinates, then its time integral is

    ∫₀^τ F (slice W s) z θ  =  J_ε (∫₀^τ G s ds) z θ − (∫₀^τ c s ds) · bump z θ .

The `hG`-continuity makes `(s, x) ↦ Jker ρ ε x · logPull (G ⌊s⌋) (· − x)` product-integrable, which
is what `SORuling.conv_intervalIntegral_swap` needs. -/
private theorem intervalIntegral_Jeps_swap_aux {ρ : ℝ × ℝ → ℝ} {ε τ : ℝ}
    (hρ : IsSmoothKernel ρ) (hε : 0 < ε) (hτ : 0 ≤ τ)
    {F : Fn → Fn} {W : Fam} {G : ℝ → Fn} {c : ℝ → ℝ}
    (hF : ∀ s ∈ Set.Icc 0 τ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      F (slice W s) z θ = Jeps ρ ε (G s) z θ - c s * bump z θ)
    (hG : Continuous (fun q : ℝ × (ℝ × ℝ) => logPull (G q.1) q.2))
    (hFint : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      IntervalIntegrable (fun s => F (slice W s) z θ) volume 0 τ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (∫ s in (0 : ℝ)..τ, F (slice W s) z θ)
      = Jeps ρ ε (fun z' θ' => ∫ s in (0 : ℝ)..τ, G s z' θ') z θ
        - (∫ s in (0 : ℝ)..τ, c s) * bump z θ := by
  set Ψ : Fn := fun z θ => ∫ s in (0 : ℝ)..τ, G s z θ with hΨdef
  have hlogΨ : logPull Ψ = fun x => ∫ s in (0 : ℝ)..τ, logPull (G s) x := rfl
  have hB := SORuling.conv_intervalIntegral_swap (k := Jker ρ ε)
    (contDiff_Jker ρ hρ ε 0).continuous (hasCompactSupport_Jker ρ hρ hε)
    (H := fun s => logPull (G s)) hG hτ (sOf z, zetaOf θ)
  have hJs : (fun s => Jeps ρ ε (G s) z θ) = fun s =>
      (Jker ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] logPull (G s))
        (sOf z, zetaOf θ) :=
    funext fun s => Jeps_eq_conv ρ ε _ hz hθ
  have hJΨ : Jeps ρ ε Ψ z θ = (Jker ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (fun y => ∫ s in (0 : ℝ)..τ, logPull (G s) y)) (sOf z, zetaOf θ) := by
    rw [Jeps_eq_conv ρ ε Ψ hz hθ, hlogΨ]
  have hA : IntervalIntegrable (fun s => Jeps ρ ε (G s) z θ) volume 0 τ := by
    rw [hJs]; exact hB.1
  have hAint : ∫ s in (0 : ℝ)..τ, Jeps ρ ε (G s) z θ = Jeps ρ ε Ψ z θ := by
    rw [hJs, hB.2, hJΨ]
  have hFeq : ∀ s ∈ uIcc (0 : ℝ) τ,
      F (slice W s) z θ = Jeps ρ ε (G s) z θ - c s * bump z θ := by
    intro s hs
    rw [uIcc_of_le hτ] at hs
    exact hF s hs z θ hz hθ
  have hcb : ∫ s in (0 : ℝ)..τ, c s * bump z θ
      = ∫ s in (0 : ℝ)..τ, (Jeps ρ ε (G s) z θ - F (slice W s) z θ) := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    show c s * bump z θ = Jeps ρ ε (G s) z θ - F (slice W s) z θ
    rw [hFeq s hs]; ring
  have hsub := intervalIntegral.integral_sub hA (hFint z θ hz hθ)
  have hmc : ∫ s in (0 : ℝ)..τ, c s * bump z θ = (∫ s in (0 : ℝ)..τ, c s) * bump z θ :=
    intervalIntegral.integral_mul_const _ _
  show ∫ s in (0 : ℝ)..τ, F (slice W s) z θ = Jeps ρ ε Ψ z θ
    - (∫ s in (0 : ℝ)..τ, c s) * bump z θ
  linarith [hcb, hsub, hmc, hAint]

theorem slice_iter_succ_mollForm {α C₀ R Ce Cs Lw δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℝ} {h₀ : Work.FTS.Galerkin.Fn} (n : ℕ)
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw)
    (h0 : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hP : ∀ s ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R C₀
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter
        (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) s))
    (hEq : ∀ s ∈ Set.Icc 0 δ, ∀ t ∈ Set.Icc 0 δ, Work.FTS.StrongEps.EpsSq α (fun z θ =>
      Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter
        (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) s z θ
        - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) t z θ) ≤ Lw * (s - t) ^ 2)
    (hFint : ∀ τ ∈ Set.Icc 0 δ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      IntervalIntegrable (fun s => Work.FTS.EpsEngine.Feps α ρ ε Φs E
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) s) z θ) volume 0 τ)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 δ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter
        (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ (n + 1)) τ z θ
      = h₀ z θ
        + Work.FTS.StrongEps.Jeps ρ ε (fun z' θ' => ∫ s in (0 : ℝ)..τ,
            Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
              (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
                (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter
                  (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) s))) z' θ') z θ
        - (∫ s in (0 : ℝ)..τ, Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε
            (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
              (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
                (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter
                  (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) s))))) 0
            / Work.FTS.StrongEps.pzNorm) * Work.FTS.StrongEps.bump z θ := by
  have hτ0 : (0 : ℝ) ≤ τ := hτ.1
  -- the *unclamped* and *clamped* families of pre-mollified right-hand sides
  set Gr : ℝ → Fn := fun s => EpsLocalPStar.profRHS α Φs E
      (Pz (Jeps ρ ε (slice (EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s))) with hGr
  set Gc : ℝ → Fn := fun s => Gr (Set.projIcc 0 τ hτ0 s : ℝ) with hGc
  have hGc_eq : ∀ s ∈ Set.Icc 0 τ, Gc s = Gr s := by
    intro s hs
    simp only [hGc]
    exact congrArg Gr (by rw [Set.projIcc_of_mem hτ0 hs])
  -- the iterate unfolds to `h₀ + ∫₀^τ Feps (slice (iter n) s) z θ`
  have hiter : slice (EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ z θ
      = h₀ z θ + ∫ s in (0 : ℝ)..τ, Feps α ρ ε Φs E
          (slice (EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s) z θ := by
    simp only [EpsLocalPStar.iter_succ, slice]
  -- `Gr` is continuous on the open quadrant and Lipschitz in the time parameter
  have hcont : ∀ s ∈ Set.Icc 0 τ, ContinuousOn (Function.uncurry (Gr s))
      Work.FTS.EllipticEst.Q0 := by
    intro s hs
    have hsδ : s ∈ Set.Icc 0 δ := ⟨hs.1, le_trans hs.2 hτ.2⟩
    exact ((smoothOpen_profRHS_of_classC (α := α) (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E)
      hα hEll hstar (hP s hsδ).classC).forall 0).continuousOn
  obtain ⟨C, hCpos, hC⟩ := EpsLocalPStar.profRHS_pre_sub_pt_le_Sq (α := α) (C₀ := C₀) (Ce := Ce)
    (Cs := Cs) (R := R) (ρ := ρ) (Φs := Φs) (E := E)
    hα hρ hε hε1 hEll hstar hml hR
  set K : NNReal := ⟨C * Real.sqrt Lw, mul_nonneg hCpos.le (Real.sqrt_nonneg _)⟩ with hK
  have hlip : ∀ s ∈ Set.Icc 0 τ, ∀ t ∈ Set.Icc 0 τ, ∀ z θ : ℝ, 0 < z →
      θ ∈ Set.Ioo 0 (Real.pi / 2) → |Gr s z θ - Gr t z θ| ≤ K * |s - t| := by
    intro s hs t ht z θ hz' hθ'
    have hsδ : s ∈ Set.Icc 0 δ := ⟨hs.1, le_trans hs.2 hτ.2⟩
    have htδ : t ∈ Set.Icc 0 δ := ⟨ht.1, le_trans ht.2 hτ.2⟩
    have hPs := hP s hsδ
    have hPt := hP t htδ
    have h1 := hC hPs.smoothOpen hPt.smoothOpen hPs.mem hPs.sq_le hPt.mem hPt.sq_le
      hPs.classC hPt.classC hPs.ball hPt.ball z θ hz' hθ'.1 hθ'.2
    have h2 : Real.sqrt (EpsSq α (fun z θ =>
          slice (EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s z θ
            - slice (EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) t z θ))
        ≤ Real.sqrt Lw * |s - t| := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hLw]
      exact Real.sqrt_le_sqrt (hEq s hsδ t htδ)
    calc |Gr s z θ - Gr t z θ|
        ≤ C * Real.sqrt (EpsSq α (fun z θ =>
            slice (EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s z θ
              - slice (EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) t z θ)) := h1
      _ ≤ C * (Real.sqrt Lw * |s - t|) := mul_le_mul_of_nonneg_left h2 hCpos.le
      _ = (K : ℝ) * |s - t| := by
          show C * (Real.sqrt Lw * |s - t|) = (C * Real.sqrt Lw) * |s - t|
          ring
  have hG : Continuous (fun q : ℝ × (ℝ × ℝ) => logPull (Gc q.1) q.2) :=
    SORuling.continuous_logPull_family hτ0 hcont hlip
  -- the pointwise mollified form of `Feps` at the iterated slices
  have hFpt : ∀ s ∈ Set.Icc 0 τ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Feps α ρ ε Φs E (slice (EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s) z θ
        = Jeps ρ ε (Gc s) z θ
          - (Work.Construction.L12 (Jeps ρ ε (Gc s)) 0 / pzNorm) * bump z θ := by
    intro s hs z θ hz' hθ'
    show Pz (Jeps ρ ε (Gr s)) z θ = Jeps ρ ε (Gc s) z θ
      - (Work.Construction.L12 (Jeps ρ ε (Gc s)) 0 / pzNorm) * bump z θ
    rw [hGc_eq s hs, Pz_apply]
  -- Fubini
  have hswap := intervalIntegral_Jeps_swap_aux (ρ := ρ) (ε := ε) (τ := τ) hρ hε hτ0
    (F := Feps α ρ ε Φs E) (W := EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) (G := Gc)
    (c := fun s => Work.Construction.L12 (Jeps ρ ε (Gc s)) 0 / pzNorm) (z := z) (θ := θ)
    hFpt hG (fun z θ hz' hθ' => hFint τ hτ z θ hz' hθ') hz hθ
  -- remove the time clamping inside `J_ε` and inside the projection coefficient
  have hΨeq : (fun z' θ' => ∫ s in (0 : ℝ)..τ, Gc s z' θ')
      = fun z' θ' => ∫ s in (0 : ℝ)..τ, EpsLocalPStar.profRHS α Φs E
          (Pz (Jeps ρ ε (slice (EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s))) z' θ' := by
    funext z' θ'
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [uIcc_of_le hτ0] at hs
    rw [hGc_eq s hs]
  have hceq : (∫ s in (0 : ℝ)..τ, Work.Construction.L12 (Jeps ρ ε (Gc s)) 0 / pzNorm)
      = ∫ s in (0 : ℝ)..τ, Work.Construction.L12 (Jeps ρ ε (EpsLocalPStar.profRHS α Φs E
          (Pz (Jeps ρ ε (slice (EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s))))) 0
          / pzNorm := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [uIcc_of_le hτ0] at hs
    rw [hGc_eq s hs]
  rw [hiter, hswap, hΨeq, hceq]
  ring

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.LeafD2.hAc_slab =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.LeafD2

theorem hAc_slab {α C₀ Ce Cs R ε δ Cpt : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {h₀ : Work.FTS.Galerkin.Fn}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hC₀ : 0 < C₀)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α (2 * C₀) Φs E)
    (hδ : 0 < δ) (hR : 0 < R) (hsm0 : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hlim : ∀ τ ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀)
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ))
    (hvol : ∀ z θ τ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → τ ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ z θ τ
        = h₀ z θ + ∫ s in (0 : ℝ)..τ,
            Work.FTS.EpsEngine.Feps α ρ ε Φs E
              (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) s) z θ)
    (hCpt : 0 ≤ Cpt)
    (hpt : ∀ u v : Work.FTS.Galerkin.Fn, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u →
      Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) v →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.FTS.EpsEngine.Feps α ρ ε Φs E u z θ - Work.FTS.EpsEngine.Feps α ρ ε Φs E v z θ|
          ≤ Cpt * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)))
    (hLip : ∃ L' : ℝ, 0 < L' ∧ ∀ σ ∈ Set.Icc 0 δ, ∀ τ ∈ Set.Icc 0 δ,
      Work.FTS.StrongEps.EpsMem α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) σ z θ
          - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) σ z θ
          - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ z θ)
        ≤ L' * (σ - τ) ^ 2) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        Work.FTS.EpsEngine.Feps α ρ ε Φs E
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) p.2.2)
          p.1 p.2.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 δ) := by
  -- The map is `p ↦ Feps (u_{p.2.2}) p.1 p.2.1`.  It is
  --  * continuous in `(z, θ) = (p.1, p.2.1)` at every fixed time `τ = p.2.2 ∈ Icc 0 δ`
  --    (`EpsEngine.continuousOn_Feps_of_XBall`, using `hlim`),
  --  * Lipschitz in `τ`, uniformly in `(z, θ) ∈ Ioi 0 ×ˢ Ioo 0 (π/2)`, with constant
  --    `Cpt · √L'` (`hpt` against `hLip`),
  -- so the joint continuity is an `ε/2`-argument.
  intro p hp
  rw [Metric.continuousWithinAt_iff]
  intro e he
  -- abbreviation: the limit family of the Picard scheme
  let LF : Work.FTS.Galerkin.Fam :=
    Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀
  have hz : 0 < p.1 := hp.1
  have hθ1 : 0 < p.2.1 := hp.2.1.1
  have hθ2 : p.2.1 < Real.pi / 2 := hp.2.1.2
  have hτp : p.2.2 ∈ Set.Icc (0 : ℝ) δ := hp.2.2
  -- ## the Lipschitz-in-`τ` data
  obtain ⟨L', hL'pos, hLip'⟩ := hLip
  have hK : 0 ≤ Cpt * Real.sqrt L' := mul_nonneg hCpt (Real.sqrt_nonneg L')
  have hden : 0 < 2 * (Cpt * Real.sqrt L' + 1) := by linarith
  have hδe : 0 < e / (2 * (Cpt * Real.sqrt L' + 1)) := div_pos he hden
  -- ## continuity in `(z, θ)` at the fixed slice `τ = p.2.2`
  have hcont : ContinuousOn (fun q : ℝ × ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E
      (Work.FTS.Galerkin.slice LF p.2.2) q.1 q.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EpsEngine.continuousOn_Feps_of_XBall (α := α) (Ce := Ce) (Cs := Cs) (R := R)
      (C₀ := 2 * C₀) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε)
      (u := Work.FTS.Galerkin.slice LF p.2.2) hα hρ hε hEll hstar (hlim p.2.2 hτp)).1
  have hmem : (p.1, p.2.1) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := ⟨hz, hθ1, hθ2⟩
  have hopen : IsOpen (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) : Set (ℝ × ℝ)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hca : ContinuousAt (fun q : ℝ × ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E
      (Work.FTS.Galerkin.slice LF p.2.2) q.1 q.2) (p.1, p.2.1) :=
    (hcont (p.1, p.2.1) hmem).continuousAt (hopen.mem_nhds hmem)
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.continuousAt_iff.1 hca (e / 2) (by linarith)
  refine ⟨min δ₂ (e / (2 * (Cpt * Real.sqrt L' + 1))), lt_min hδ₂pos hδe, ?_⟩
  intro x hx hxd
  have hx1 : 0 < x.1 := hx.1
  have hxθ1 : 0 < x.2.1 := hx.2.1.1
  have hxθ2 : x.2.1 < Real.pi / 2 := hx.2.1.2
  have hxτ : x.2.2 ∈ Set.Icc (0 : ℝ) δ := hx.2.2
  -- ## the time difference is small
  have hdτ : |x.2.2 - p.2.2| < e / (2 * (Cpt * Real.sqrt L' + 1)) := by
    have hcoord : |x.2.2 - p.2.2| ≤ dist x p := by
      have h4 : dist x p
          = max (dist x.1 p.1) (max (dist x.2.1 p.2.1) (dist x.2.2 p.2.2)) := by
        simp only [Prod.dist_eq]
      have h3 : dist x.2.2 p.2.2 = |x.2.2 - p.2.2| := Real.dist_eq _ _
      rw [h4, h3]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    exact lt_of_le_of_lt hcoord (lt_of_lt_of_le hxd (min_le_right _ _))
  -- ## the `(z, θ)`-difference is small
  have hdzθ : dist (x.1, x.2.1) (p.1, p.2.1) < δ₂ := by
    have h4 : dist x p
        = max (dist x.1 p.1) (max (dist x.2.1 p.2.1) (dist x.2.2 p.2.2)) := by
      simp only [Prod.dist_eq]
    have h5 : dist (x.1, x.2.1) (p.1, p.2.1)
        = max (dist x.1 p.1) (dist x.2.1 p.2.1) := by
      simp only [Prod.dist_eq]
    have hle : dist (x.1, x.2.1) (p.1, p.2.1) ≤ dist x p := by
      rw [h5, h4]
      exact max_le_max le_rfl (le_max_left _ _)
    exact lt_of_le_of_lt hle (lt_of_lt_of_le hxd (min_le_left _ _))
  -- ## the two `e/2`-pieces
  have he2 : |Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice LF p.2.2) x.1 x.2.1
      - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice LF p.2.2) p.1 p.2.1|
      < e / 2 := by
    simpa only [Real.dist_eq] using hδ₂ hdzθ
  have he1 : |Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice LF x.2.2) x.1 x.2.1
      - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice LF p.2.2) x.1 x.2.1|
      < e / 2 := by
    have hpt' := hpt (Work.FTS.Galerkin.slice LF x.2.2) (Work.FTS.Galerkin.slice LF p.2.2)
      (hlim x.2.2 hxτ) (hlim p.2.2 hτp) x.1 x.2.1 hx1 hxθ1 hxθ2
    have hdiff : Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice LF x.2.2 z θ - Work.FTS.Galerkin.slice LF p.2.2 z θ)
        ≤ L' * (x.2.2 - p.2.2) ^ 2 := (hLip' x.2.2 hxτ p.2.2 hτp).2
    have hsqrt : Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice LF x.2.2 z θ - Work.FTS.Galerkin.slice LF p.2.2 z θ))
        ≤ Real.sqrt L' * |x.2.2 - p.2.2| := by
      calc Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ =>
              Work.FTS.Galerkin.slice LF x.2.2 z θ - Work.FTS.Galerkin.slice LF p.2.2 z θ))
          ≤ Real.sqrt (L' * (x.2.2 - p.2.2) ^ 2) := Real.sqrt_le_sqrt hdiff
        _ = Real.sqrt L' * Real.sqrt ((x.2.2 - p.2.2) ^ 2) := Real.sqrt_mul hL'pos.le _
        _ = Real.sqrt L' * |x.2.2 - p.2.2| := by rw [Real.sqrt_sq_eq_abs]
    have hmain : Cpt * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice LF x.2.2 z θ - Work.FTS.Galerkin.slice LF p.2.2 z θ))
        < e / 2 := by
      calc Cpt * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ =>
              Work.FTS.Galerkin.slice LF x.2.2 z θ - Work.FTS.Galerkin.slice LF p.2.2 z θ))
          ≤ Cpt * (Real.sqrt L' * |x.2.2 - p.2.2|) := mul_le_mul_of_nonneg_left hsqrt hCpt
        _ = Cpt * Real.sqrt L' * |x.2.2 - p.2.2| := by ring
        _ ≤ Cpt * Real.sqrt L' * (e / (2 * (Cpt * Real.sqrt L' + 1))) :=
              mul_le_mul_of_nonneg_left (le_of_lt hdτ) hK
        _ < e / 2 := by
              rw [← mul_div_assoc]
              rw [div_lt_iff₀ hden]
              nlinarith [he]
    exact lt_of_le_of_lt hpt' hmain
  -- ## triangle inequality
  rw [Real.dist_eq]
  calc |Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice LF x.2.2) x.1 x.2.1
        - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice LF p.2.2) p.1 p.2.1|
      ≤ |Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice LF x.2.2) x.1 x.2.1
          - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice LF p.2.2) x.1 x.2.1|
        + |Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice LF p.2.2) x.1 x.2.1
          - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice LF p.2.2) p.1 p.2.1| :=
          abs_sub_le _ _ _
    _ < e / 2 + e / 2 := add_lt_add he1 he2
    _ = e := by ring

end Work.FTS.StrongEps.EpsE4Thr.LeafD2
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.volterra_of_xball =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits

theorem volterra_of_xball {α C₁ Ce Cs R ε δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {h₀ : Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α C₁ Φs E)
    (hδ : 0 < δ) (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε δ Φs E h₀ g)
    (hreg : Work.FTS.StrongEps.EpsRegP α ρ ε δ g)
    (hX : ∀ τ ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R C₁ (Work.FTS.Galerkin.slice g τ)) :
    ∀ z θ τ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → τ ∈ Set.Icc 0 δ →
      g z θ τ = g z θ 0 + ∫ s in (0 : ℝ)..τ, Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g s) z θ := by
  intro z θ τ hQ hτ
  rw [Work.FTS.EllipticEst.mem_Q0] at hQ
  obtain ⟨hz, hθ0, hθ1⟩ := hQ
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  -- The integrand is the fake-time derivative of the jointly `C¹` family, hence continuous:
  have hcont : ContinuousOn
      (fun s : ℝ =>
        Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g s) z θ)
      (Set.Icc 0 δ) :=
    Work.FTS.StrongEps.IsEpsSolPQ.continuousOn_derivWithin_curve
      (f := fun p : ℝ × (ℝ × ℝ) => g p.1 p.2.1 p.2.2)
      (v := fun s : ℝ =>
        Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g s) z θ)
      hδ hz hθ hreg.1 (fun s hs => by
        have h := hsol.2 z θ s hz hθ hs
        rwa [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice α ρ ε Φs E] at h)
  have hmemI : Set.MapsTo (fun s : ℝ => (z, (θ, s))) (Set.Icc 0 τ)
      (Work.FTS.StrongEps.IsEpsSolPQ.Dset δ) := by
    intro s hs
    rw [Work.FTS.StrongEps.IsEpsSolPQ.mem_Dset]
    exact ⟨hz, hθ0, hθ1, hs.1, le_trans hs.2 hτ.2⟩
  have hprim : ContinuousOn (fun s : ℝ => g z θ s) (Set.Icc 0 τ) :=
    hreg.1.continuousOn.comp (by fun_prop) hmemI
  have hint : IntervalIntegrable
      (fun s : ℝ =>
        Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g s) z θ)
      MeasureTheory.volume 0 τ :=
    ContinuousOn.intervalIntegrable_of_Icc hτ.1
      (hcont.mono (fun x hx => ⟨hx.1, le_trans hx.2 hτ.2⟩))
  -- The fundamental theorem of calculus in the fake time:
  have hFTC : (∫ s in (0 : ℝ)..τ,
        Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g s) z θ)
      = g z θ τ - g z θ 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ.1 hprim (fun x hx => ?_) hint
    have hxδ : x < δ := lt_of_lt_of_le hx.2 hτ.2
    have h := hsol.2 z θ x hz hθ ⟨hx.1.le, hxδ.le⟩
    rw [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice α ρ ε Φs E] at h
    exact h.hasDerivAt (Icc_mem_nhds hx.1 hxδ)
  linarith [hFTC]

end Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.RegDataOfXBall =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `EpsE4Thr/RegDataOfXBall.lean` — OPEN LEAF-D2 `regData_of_xball`

curric-46 install 2026-10-12 (REVIEW F2; `cbc/fts_regularity_interface.md` §2 last bullet).  The
producer of `RegDataD` (the hypotheses of LEAF-D `regFromVolterra'`) for `F = Feps` along the
Picard limit family, given its slices in the `X`-ball and its Volterra identity.  TRUE at fixed `ε`
(research-low; the hardest regularity item — dispatch first).

Route (mollified form `Feps w_σ = J_ε Φ_σ − c_σ • bump`, `Φ_σ = profRHS(P₀ J_ε w_σ)`):
* curve `EpsSq`-Lipschitz: `hvol` + the `hbd` gate of `EpsRHSPLipX_Sq` at radius `2 C₀`
  (`EpsSq_intervalIntegral_le_gen`);
* `hAy` (per-slice `C¹`): `smoothOpen_Feps_of_classC` (or `continuousOn_Feps_of_XBall` / `Feps_data_of_xball8`);
* `hAc` (joint continuity): per-slice continuity + the uniform-in-`y` difference bound
  `profRHS_sub_sup_le_Sq` / `profRHS_pre_sub_pt_le_Sq` + the `EpsSq`-Lipschitz bound
  (`EpsEngine.continuous_logPull_family`);
* `hB` (the real work): `∂_y J_ε Φ_σ = ∇Jker ⋆ Φ_σ` jointly continuous (`conv_intervalIntegral_swap`),
  and `c_σ` continuous (evaluate at a point where `bump ≠ 0`, use `hpt`).
No `σ`-derivative of the right-hand side is needed.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R5

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.EpsEngine (XBall Feps)
open Work.FTS.StrongEps.EpsLocalPStar (limFam)

set_option autoImplicit false
set_option linter.unusedVariables false


end Work.FTS.StrongEps.EpsE4Thr.E4R5
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXVP.velPkg_proved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXVP.velPkg_proved` — RX-VP, up to the one missing hypothesis `hVop`

`VelPkg` (frozen `RegExportIface`) = `VelPkgOpen` (the repaired package: open-`θ`
`bnd`/`vz0`/`cont`, no `axis`; seven of eight fields PROVED in `RXVP3/`) plus the `thHol` clause
(PROVED here as `RXVP.thHol_proved`, the A8 assembly of the THL leaves A1a–A7).

The single remaining input is `hVop`, the pointwise **lower bound on the `V`-slot of the stream
function**: on the open quadrant

    `2 * pExp α * Vop (slice (psiR α Φs E (tauExt g)) τ) z θ ≥ -(1 - maxMu α (PsiCan Φs E g) g τ)`.

By the proved closed form (`RXVP3.vz0_of_vopLower.vz7_eq_of_vop`) this is *equivalent* to the
field `VelPkg.vz0`; it is the pointwise form in which the constraint is geometric (a lower bound
on the axial strain of the stream function), and it is what the frozen interface needs to add —
see `NOTES_session_gaps.md` §2 (G3).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)
open Work.FTS.RegExportIface

namespace Work.FTS_RegExport.RXVP

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

theorem velPkg_proved (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E) (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    {g : Fam} (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β z θ)
    (hμ : ClockBd α Φs E g)
    (hVop : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ →
      -(1 - Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g τ)
        ≤ 2 * pExp α * Work.Construction.Vop
            (slice (psiR α Φs E (tauExt g)) τ) z θ) :
    ∀ S > 0, VelPkg (pExp α) (Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g)
      (gS α (tauExt g)) (psiR α Φs E (tauExt g)) S := by
  intro S hS
  exact Work.FTS_RegExport.VelPkg_of_open
    (Work.FTS_RegExport.RXVP3.velPkgOpen_of_vopLower (Φs := Φs) (E := E)
      hα hα13 hEll hEL3 hStar hSol hOK hdat hμ hVop S hS)
    (thHol_proved (Φs := Φs) (E := E) hα hα13 hEll hEL3 hStar hSol hOK hμ S hS)

end Work.FTS_RegExport.RXVP
end
end
