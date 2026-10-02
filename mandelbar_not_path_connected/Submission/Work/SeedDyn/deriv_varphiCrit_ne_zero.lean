import Mathlib
import Submission.Work.SeedDyn.Defs
import Submission.Work.Bottcher.CritBottcherExists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# D7 of the SeedDyn design note: `φ' ≠ 0` on the escaping set

This module proves the *conditional* statement of the design note
(`Submission/Work/NOTES_LEAD_mandelbar_seed.md` §1.3, line D7): given the three "D-table"
inputs

* **D4** (`h4`): `φ (Tsq c z) = φ z ^ 4` on `esc c`,
* **D5** (`h5`): `deriv (Tsq c) z ≠ 0` on `esc c`,
* **D6** (`h6`): `deriv φ z → 1` as `‖z‖ → ∞`,

the derivative of the Böttcher coordinate has no zeros on the escaping set.

The argument is the one of the design note.  Differentiating D4 gives, at every `w ∈ esc c`,

```
φ' (Tsq c w) * (Tsq c)' w = 4 * φ w ^ 3 * φ' w.
```

If `φ' z = 0`, this equation and D5 propagate the vanishing of `φ'` to the whole forward orbit of
`z` under the holomorphic quartic `Tsq c = (T_c)^[2]`; but `z` escapes, so that orbit is eventually
outside any ball, while D6 forces `φ'` to be nonzero there.  Contradiction.

The three inputs are hypotheses here because they are proved separately (in the modules
`varphiCrit_comm_Tsq`, `deriv_Tsq_ne_zero`, `deriv_varphiCrit_tendsto_one`).
-/

open scoped Topology ComplexConjugate
open Classical Filter

namespace Work.SeedDyn

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-- **Differentiated Böttcher equation.**  For `c ∈ M*`, differentiating the relation
`φ (Tsq c w) = φ w ^ 4` (which holds on the *open* set `esc c`) at `w ∈ esc c` gives

`φ' (Tsq c w) * (Tsq c)' w = 4 * φ w ^ 3 * φ' w`.

Analyticity of `φ` on `esc c` (`analyticOnNhd_varphiCrit_esc`) supplies the two differentiability
hypotheses needed for the chain rule and the power rule. -/
theorem deriv_varphiCrit_comp_Tsq (c : ℂ) (hc : c ∈ Mandelbar)
    (h4 : ∀ z ∈ esc c,
      Work.Bottcher.varphiCrit c (Work.Landing.Tsq c z) = Work.Bottcher.varphiCrit c z ^ 4)
    {w : ℂ} (hw : w ∈ esc c) :
    deriv (Work.Bottcher.varphiCrit c) (Work.Landing.Tsq c w) * deriv (Work.Landing.Tsq c) w
      = 4 * Work.Bottcher.varphiCrit c w ^ 3 * deriv (Work.Bottcher.varphiCrit c) w := by
  -- the function `φ (Tsq c ·) - φ · ^ 4` vanishes on a neighbourhood of `w` (namely on `esc c`)
  have hF : ((fun u => Work.Bottcher.varphiCrit c (Work.Landing.Tsq c u)) -
        (fun u => Work.Bottcher.varphiCrit c u ^ 4)) =ᶠ[𝓝 w] 0 := by
    have hnhds : esc c ∈ 𝓝 w := (isOpen_esc c).mem_nhds hw
    filter_upwards [hnhds] with u hu
    simp only [Pi.sub_apply, Pi.zero_apply]
    rw [h4 u hu, sub_self]
  have h0 : deriv ((fun u => Work.Bottcher.varphiCrit c (Work.Landing.Tsq c u)) -
      (fun u => Work.Bottcher.varphiCrit c u ^ 4)) w = 0 := by
    rw [Filter.EventuallyEq.deriv_eq hF]
    simp
  -- differentiability of the pieces
  have hdφ : DifferentiableAt ℂ (Work.Bottcher.varphiCrit c) (Work.Landing.Tsq c w) :=
    ((analyticOnNhd_varphiCrit_esc hc) (Work.Landing.Tsq c w) (Tsq_mem_esc hw)).differentiableAt
  have hdφw : DifferentiableAt ℂ (Work.Bottcher.varphiCrit c) w :=
    ((analyticOnNhd_varphiCrit_esc hc) w hw).differentiableAt
  have hdp : DifferentiableAt ℂ (Work.Landing.Tsq c) w := by
    rw [show Work.Landing.Tsq c = fun z => (z ^ 2 + star c) ^ 2 + c from rfl]
    fun_prop
  have hd1 : DifferentiableAt ℂ (fun u => Work.Bottcher.varphiCrit c (Work.Landing.Tsq c u)) w :=
    hdφ.comp w hdp
  have hd2 : DifferentiableAt ℂ (fun u => Work.Bottcher.varphiCrit c u ^ 4) w := hdφw.pow 4
  rw [deriv_sub hd1 hd2] at h0
  have hcomp : deriv (fun u => Work.Bottcher.varphiCrit c (Work.Landing.Tsq c u)) w
      = deriv (Work.Bottcher.varphiCrit c) (Work.Landing.Tsq c w) * deriv (Work.Landing.Tsq c) w :=
    deriv_comp w hdφ hdp
  have hpow : deriv (fun u => Work.Bottcher.varphiCrit c u ^ 4) w
      = 4 * Work.Bottcher.varphiCrit c w ^ 3 * deriv (Work.Bottcher.varphiCrit c) w := by
    rw [show (fun u => Work.Bottcher.varphiCrit c u ^ 4) =
      (Work.Bottcher.varphiCrit c) ^ 4 from rfl]
    rw [deriv_pow hdφw 4]
    norm_num
  rw [hcomp, hpow] at h0
  exact sub_eq_zero.mp h0

/-- **D7.**  Under the three D-table inputs D4, D5, D6 the derivative of the canonical Böttcher
coordinate `varphiCrit c` has no zero on the escaping set of a mandelbar parameter.

Proof: if `φ' z = 0`, the differentiated Böttcher equation forces `φ'` to vanish at all points of
the forward orbit of `z` under `Tsq c` (using D5 to divide out the derivative of `Tsq c`).  The
orbit of an escaping point tends to infinity, so by D6 it eventually leaves any ball and there
`φ'` is within `1/2` of `1`, hence nonzero. -/
theorem deriv_varphiCrit_ne_zero {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    (h4 : ∀ z ∈ Work.SeedDyn.esc c,
      Work.Bottcher.varphiCrit c (Work.Landing.Tsq c z) = Work.Bottcher.varphiCrit c z ^ 4)
    (h5 : ∀ z ∈ Work.SeedDyn.esc c, deriv (Work.Landing.Tsq c) z ≠ 0)
    (h6 : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      ‖deriv (Work.Bottcher.varphiCrit c) z - 1‖ ≤ ε)
    {z : ℂ} (hz : z ∈ Work.SeedDyn.esc c) :
    deriv (Work.Bottcher.varphiCrit c) z ≠ 0 := by
  intro hz0
  -- the differentiated Böttcher equation at every point of the escaping set
  have hkey : ∀ w ∈ esc c,
      deriv (Work.Bottcher.varphiCrit c) (Work.Landing.Tsq c w) * deriv (Work.Landing.Tsq c) w
        = 4 * Work.Bottcher.varphiCrit c w ^ 3 * deriv (Work.Bottcher.varphiCrit c) w :=
    fun w hw => deriv_varphiCrit_comp_Tsq c hc h4 hw
  -- D6 with ε = 1/2: far out, `φ'` is within `1/2` of `1`
  obtain ⟨R, hR⟩ := h6 (1 / 2) (by norm_num)
  -- the orbit of `z` under `Tsq c` (index `2 n` of the `T_c`-orbit) is eventually outside that ball
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hz.eventually_gt R)
  -- induction: `φ'` vanishes at every `Tsq`-iterate of `z`
  have hiter : ∀ n : ℕ, deriv (Work.Bottcher.varphiCrit c) (Work.ParamRays.orbit c z (2 * n)) = 0 := by
    intro n
    induction n with
    | zero => simpa using hz0
    | succ n ih =>
        have hesc : Work.ParamRays.orbit c z (2 * n) ∈ esc c := hz.iterate (2 * n)
        have hk := hkey _ hesc
        rw [ih, mul_zero] at hk
        have hd : deriv (Work.Bottcher.varphiCrit c)
            (Work.Landing.Tsq c (Work.ParamRays.orbit c z (2 * n))) = 0 := by
          rcases mul_eq_zero.mp hk with h | h
          · exact h
          · exact absurd h (h5 _ hesc)
        have hidx : Work.ParamRays.orbit c z (2 * (n + 1))
            = Work.Landing.Tsq c (Work.ParamRays.orbit c z (2 * n)) := by
          rw [show 2 * (n + 1) = 2 * n + 2 from by ring, Work.ParamRays.orbit_add]
          exact (Work.ELPull.Tsq_eq_iterate c _).symm
        rw [hidx, hd]
  -- the orbit eventually leaves the ball of radius `R`
  have hNR : R ≤ ‖Work.ParamRays.orbit c z (2 * N)‖ := by
    have h := hN (2 * N) (by omega)
    linarith
  have hbig := hR (Work.ParamRays.orbit c z (2 * N)) hNR
  rw [hiter N] at hbig
  norm_num at hbig

end

end Work.SeedDyn
