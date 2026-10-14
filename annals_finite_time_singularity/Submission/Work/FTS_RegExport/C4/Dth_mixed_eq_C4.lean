import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.N6.sliceAvg_le6
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.mixedSupSix
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.classC_mixed_sup_le_four =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## The level-`6` angular integrability of a mixed slot

The `SupPort` chain of `classC_mixed_sup_le` is stated with `ℋ⁴`-membership throughout.  For
the order-`4` trade-off proved here the same chain has to be re-run with the level-`6`
`ℋ`-integrand, so we need the two integrability inputs of the angular Hardy inequality
(`Work.FTS.StrongEps.SupPort.HardyThetaOpen`) at level `6`:

* `integrableOn_mixed_sq_rpow6`: the slot `D_z^jD_θ^if` against its own weight
  `sin(2θ)^{-γ}` (for `1 ≤ i`, `i + j ≤ 6`);
* `integrableOn_pth_sq_rpow6`: the `∂_θ`-slot against the weight `sin(2θ)^{2-γ}`, which the
  identity `sin(2θ)·∂_θ(D_z^jD_θ^if) = D_z^jD_θ^{i+1}f` turns into the next slot.

Both are the level-`4` lemmas `Work.FTS.TransportS.T2SupB2.integrableOn_mixed_sq_rpow` and
`Work.FTS.TransportS.T2SupB2.integrableOn_pth_sq_rpow` with `4 ↦ 6`: the only level-dependent
input, `Work.FTS.EllipticEst.integrableOn_mixedSummand`, is stated for an arbitrary level. -/

/-- The weighted mixed slot `(D_z^jD_θ^if · Wt)²` divided by the (constant) radial weight
`(w z)²` is the slot against its own angular weight `sin(2θ)^{-γ}`. -/
theorem integrableOn_mixed_sq_rpow6 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 6) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun t => (Work.Spaces.mixed j i f z t) ^ 2
        * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
  have hbase := Work.FTS.EllipticEst.integrableOn_mixedSummand α 6 hF hmem i j hi hij
    (z := z) (Set.mem_Ici.mpr (le_of_lt hz))
  have hw : (Work.Spaces.w z) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (Work.FTS.TransportS.one_le_w hz))
  have hae : (fun t => (Work.Spaces.mixed j i f z t) ^ 2
        * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α)))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun t => (Work.Spaces.mixed j i f z t * Work.Spaces.Wt α z t) ^ 2
        * ((Work.Spaces.w z) ^ 2)⁻¹) := by
    rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => ?_)
    show (Work.Spaces.mixed j i f z t) ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α))
      = (Work.Spaces.mixed j i f z t * Work.Spaces.Wt α z t) ^ 2
        * ((Work.Spaces.w z) ^ 2)⁻¹
    have hs : 0 < Real.sin (2 * t) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])
    have hw2 : ((Work.Spaces.w z) ^ 2) ≠ 0 := pow_ne_zero 2 hw
    rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z t hs]
    field_simp
  exact (hbase.mul_const _).congr hae.symm

/-- The `∂_θ`-slot of a mixed slot against the weight `sin(2θ)^{2-γ}` is `θ`-integrable, as
soon as the next slot `D_z^jD_θ^{i+1}f` with its own weight is (i.e. for `i + j ≤ 5`). -/
theorem integrableOn_pth_sq_rpow6 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f)
    (j i : ℕ) (hij : i + j ≤ 5) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun t => (Work.Spaces.pth (Work.Spaces.mixed j i f) z t) ^ 2
        * (Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  refine (integrableOn_mixed_sq_rpow6 hF hmem j (i + 1) (by omega) (by omega) hz).congr ?_
  rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => ?_)
  show (Work.Spaces.mixed j (i + 1) f z t) ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α))
      = (Work.Spaces.pth (Work.Spaces.mixed j i f) z t) ^ 2
        * (Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α)
  have hs : 0 < Real.sin (2 * t) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])
  have hsplit : (Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * t)) ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α)) := by
    rw [show (2 : ℝ) - Work.Spaces.gam α
        = (2 : ℝ) + (-(Work.Spaces.gam α)) by ring, Real.rpow_add hs, Real.rpow_two]
  rw [← Work.FTS.TransportS.T2SupB2.sin_mul_pth_mixed hF j i hz ht, hsplit]
  ring

/-! ## The order-`4` interior trade-off -/

/-- **The interior `L^∞`–`ℋ⁶` trade-off on the open class.**  For `f` of class `C^∞` on the
open quadrant, honestly in `ℋ⁶`, with the `θ`-limits and the decay at `z → ∞` of
`BdryTraces α 6 f`, every mixed slot `D_z^bD_θ^a f` of order `a + b ≤ 4` is bounded at each
point of the open quadrant by `C/√(γ-1)·|f|_{ℋ⁶}` for a universal constant `C`.

The proof is the level-`6` re-run of the `ℋ⁴` version: the angular Hardy inequality
`HardyThetaOpen` at the slot `D_z^bD_θ^af` (whose `θ → 0⁺` boundary value vanishes by
`BdryTraces`) gives

  `(D_z^bD_θ^af(z,θ))² ≤ (100/(γ-1)) ∫_θ (∂_θD_z^bD_θ^af)² sin(2θ)^{2-γ}`,

the identity `sin(2θ)∂_θ(D_z^bD_θ^af) = D_z^bD_θ^{a+1}f` rewrites the integral as the
`γ`-weighted angular slice of the next slot `D_z^bD_θ^{a+1}f` (of order `a+b+1 ≤ 5`), and
`Work.FTS.StrongPersist.N6.sliceAng_le6` bounds that slice by `C·|f|²_{ℋ⁶}`. -/
theorem mixedSup_pt_le_of_smoothOpen6 :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) {f : ℝ → ℝ → ℝ}, 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.FTS.Nonlin.BdryTraces α 6 f →
      ∀ (b a : ℕ), a + b ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a f z θ| ≤ C / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.Spaces.HkNorm α 6 f := by
  obtain ⟨C6, hC6pos, hC6⟩ := Work.FTS.StrongPersist.N6.sliceAng_le6
  refine ⟨10 * Real.sqrt C6, by positivity, ?_⟩
  intro α f hα hα1 hF hmem hbd b a hab z θ hz hθ0 hθ1
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hC6nn : (0 : ℝ) ≤ C6 := hC6pos.le
  -- the boundary value of the `θ`-slice at `0⁺`
  have h0 : Filter.Tendsto (fun θ' => Work.Spaces.mixed b a f z θ')
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    Work.FTS.H2.tendsto_nhdsGT_zero_of_traces α hα
      ((hbd a b (by omega)).2 z (Set.mem_Ioi.mpr hz) |>.1)
  -- integrability of the angular Hardy integrand
  have hAint := integrableOn_pth_sq_rpow6 hF hmem b a (by omega) hz
  -- the angular Hardy inequality
  have hHT := Work.FTS.StrongEps.SupPort.HardyThetaOpen α hα hα1 (Work.Spaces.mixed b a f) z
    (hF.mixed b a) hz h0 hAint θ ⟨hθ0, hθ1⟩
  -- the angular integral is the `γ`-weighted slice of the next slot
  have hAeq : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      = ∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
    Work.FTS.TransportS.T2SupB2.setIntegral_pth_sq_eq hF b a hz
  have hAng := hC6 α f b (a + 1) hα hα1 hF hmem (by omega) (by omega) z hz
  have hc : (0 : ℝ) ≤ 100 / (Work.Spaces.gam α - 1) := div_nonneg (by norm_num) hγ1.le
  have hmix : (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ (100 / (Work.Spaces.gam α - 1)) * (C6 * Work.Spaces.HkSq α 6 f) := by
    calc (Work.Spaces.mixed b a f z θ) ^ 2
        ≤ (100 / (Work.Spaces.gam α - 1)) * ∫ σ in Work.Spaces.Iθ,
            (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
              * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := hHT
      _ = (100 / (Work.Spaces.gam α - 1)) * ∫ σ in Work.Spaces.Iθ,
            (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
              * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by rw [hAeq]
      _ ≤ (100 / (Work.Spaces.gam α - 1)) * (C6 * Work.Spaces.HkSq α 6 f) :=
          mul_le_mul_of_nonneg_left hAng hc
  have h2 : |Work.Spaces.mixed b a f z θ|
      ≤ Real.sqrt ((100 / (Work.Spaces.gam α - 1)) * (C6 * Work.Spaces.HkSq α 6 f)) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hmix
  -- the square root is the announced constant times `|f|_{ℋ⁶}`
  have hsq1 : Real.sqrt (100 / (Work.Spaces.gam α - 1))
      = 10 / Real.sqrt (Work.Spaces.gam α - 1) := by
    rw [Real.sqrt_div (x := (100 : ℝ)) (by norm_num) (Work.Spaces.gam α - 1),
      show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h3 : Real.sqrt ((100 / (Work.Spaces.gam α - 1)) * (C6 * Work.Spaces.HkSq α 6 f))
      = 10 * Real.sqrt C6 / Real.sqrt (Work.Spaces.gam α - 1)
        * Work.Spaces.HkNorm α 6 f := by
    calc Real.sqrt ((100 / (Work.Spaces.gam α - 1)) * (C6 * Work.Spaces.HkSq α 6 f))
        = Real.sqrt ((100 / (Work.Spaces.gam α - 1)) * C6)
            * Real.sqrt (Work.Spaces.HkSq α 6 f) := by
          rw [show (100 / (Work.Spaces.gam α - 1)) * (C6 * Work.Spaces.HkSq α 6 f)
                = ((100 / (Work.Spaces.gam α - 1)) * C6) * Work.Spaces.HkSq α 6 f
              from by ring,
            Real.sqrt_mul (by positivity)]
      _ = (Real.sqrt (100 / (Work.Spaces.gam α - 1)) * Real.sqrt C6)
            * Real.sqrt (Work.Spaces.HkSq α 6 f) := by
          rw [Real.sqrt_mul hc]
      _ = (10 / Real.sqrt (Work.Spaces.gam α - 1) * Real.sqrt C6)
            * Work.Spaces.HkNorm α 6 f := by
          rw [hsq1, Work.Spaces.HkNorm]
      _ = 10 * Real.sqrt C6 / Real.sqrt (Work.Spaces.gam α - 1)
            * Work.Spaces.HkNorm α 6 f := by ring
  exact le_trans h2 (le_of_eq h3)

/-! ## The target -/

theorem classC_mixed_sup_le_four :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α f → ∀ (b a : ℕ), a + b ≤ 4 → ∀ {z θ : ℝ},
      (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.mixed b a f z θ|
        ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.StrongGlobal.Xn6 α f := by
  obtain ⟨C, hCpos, hC⟩ := mixedSup_pt_le_of_smoothOpen6
  refine ⟨C, hCpos, ?_⟩
  intro α hα f hf b a hab z θ hzθ
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hmem6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hf.reg 6 (by norm_num) hf.mem
  have hbd6 : Work.FTS.Nonlin.BdryTraces α 6 f := hf.tr
  exact hC α hα0 hα1 hf.reg hmem6 hbd6 b a hab z θ hzθ.1 hzθ.2.1 hzθ.2.2

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.C4

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 800000

/-!
# `D_θ` of a mixed derivative, at the finite order `C⁴`

The curvilinear operators `D_z f = z ∂_z f` and `D_θ f = sin(2θ) ∂_θ f` commute wherever the
datum is `C²` (Clairaut), so `D_θ (D_z^b D_θ^a f) = D_z^b D_θ^{a+1} f` — the identity behind
the definition `D_θ^{i+1} = D_θ ∘ D_θ^i` of `mixed`.

The existing proofs of this identity in the workspace (`Work.Spaces.Dth_DzIter_comm_eqOn`,
`Work.FTS.CoercivityFix.QuadPorts.DzIter_DthIter_comm_quad`, …) are stated for a datum which
is `C^∞` (or analytic) on an open set.  Here only the *finite* order is available: the datum
is `C⁴` on the open quadrant `Q0` and the total order `a + b + 1` of the derivatives involved
is `≤ 4`.  Since the proof of the identity only ever differentiates the datum `a + b + 1`
times, the same argument runs verbatim at the finite order, provided the `D`-calculus is
available at finite order — which it is, in
`Work.FTS.StrongEps.contDiffOn_uncurry_{pz,pth,Dz,Dth,DzIter,DthIter}_*`.

The key auxiliary is `Dth_DzIter_comm_fin`: `D_θ` commutes with `D_z^b` on an open set on
which the datum is `C^{b+1}`.  The induction on `b` moves one `D_z` past the `D_θ` by Clairaut
(which needs `C²` of `D_z^b g`, i.e. `C^{b+2}` of `g`), and the two sides of the resulting
identity `D_z (D_θ (D_z^b g)) = D_z (D_z^b (D_θ g))` are compared by the induction hypothesis
for the *same* open set, using `pz_congr_of_isOpen`.
-/

/-- **Commutation of `D_θ` with the radial iterates, at the finite order `b + 1`.**

If `g` is `C^{b+1}` on an open set `V`, then `D_θ (D_z^b g) = D_z^b (D_θ g)` on `V`.

(The induction uses `C^{b+2}` of `g` at the step `b ↦ b+1` — Clairaut for `D_z^b g` — which is
more than the hypothesis of the statement needs; the statement itself is phrased with the
minimal order `b + 1` so that it can be applied to `g = D_θ^a f` of a `C⁴` datum.) -/
theorem Dth_DzIter_comm_fin (b : ℕ) {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ (b + 1) (Function.uncurry g) V) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DzIter b g)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.Dth g))) V := by
  induction b with
  | zero => intro y hy; rfl
  | succ b ih =>
      -- `g` is `C^{b+1}` as well, and `D_z^b g` is `C²`
      have hb : ContDiffOn ℝ (b + 1) (Function.uncurry g) V :=
        h.of_le (by exact_mod_cast (show (b + 1 : ℕ) ≤ b + 1 + 1 by omega))
      have hih : Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DzIter b g)))
          (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.Dth g))) V := ih hb
      have h2b : ContDiffOn ℝ (2 + b) (Function.uncurry g) V := by
        have key : ((2 : WithTop ℕ∞) + (b : WithTop ℕ∞)) = ((b : WithTop ℕ∞) + 1 + 1) := by
          exact_mod_cast (show (2 + b : ℕ) = b + 1 + 1 by omega)
        rw [key]
        exact h
      have hC2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.DzIter b g)) V :=
        Work.FTS.StrongEps.contDiffOn_uncurry_DzIter_shift hV b 2 h2b
      intro y hy
      have hcy : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter b g)) y :=
        hC2.contDiffAt (hV.mem_nhds hy)
      -- Clairaut at `y` for `D_z^b g`
      have hcomm : Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b g)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DzIter b g)) y.1 y.2 :=
        (Work.Spaces.Dz_Dth_comm hcy).symm
      show Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b g)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.Dth g)) y.1 y.2
      rw [hcomm]
      -- the two functions inside the outer `D_z` agree on the open set `V`
      show y.1 * Work.Spaces.pz (Work.Spaces.Dth (Work.Spaces.DzIter b g)) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.Dth g)) y.1 y.2
      rw [Work.Spaces.pz_congr_of_isOpen hV hih hy]

/-- **The `C⁴` shift identity**: for a datum `f` of class `C⁴` on the open quadrant `Q0` and
`a + b + 1 ≤ 4`, the operator `D_θ` shifts the angular index of the mixed derivative,
`D_θ (D_z^b D_θ^a f) = D_z^b D_θ^{a+1} f`, at every interior point of `Q0`. -/
theorem Dth_mixed_eq_C4 {f : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (b a : ℕ) (hab : a + b + 1 ≤ 4) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ = Work.Spaces.mixed b (a + 1) f z θ := by
  have hy : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ⟩
  -- `D_θ^a f` is `C^{b+1}`, since `f` is `C^{a+b+1}`
  have hab2 : (b + 1 + a : ℕ) ≤ 4 := by omega
  have h1 : ContDiffOn ℝ (b + 1 + a) (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    hF.of_le (Nat.cast_le.mpr hab2)
  have hfin : ContDiffOn ℝ (b + 1) (Function.uncurry (Work.Spaces.DthIter a f))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_DthIter_shift
      Work.FTS.EllipticEst.isOpen_Q0 a (b + 1) h1
  have hpt := (Dth_DzIter_comm_fin b Work.FTS.EllipticEst.isOpen_Q0 hfin) hy
  rw [show Work.Spaces.mixed b a f
      = Work.Spaces.DzIter b (Work.Spaces.DthIter a f) from rfl]
  rw [show Work.Spaces.mixed b (a + 1) f
      = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter a f)) from rfl]
  simpa only [Function.uncurry] using hpt

end Work.FTS_RegExport.C4
end
