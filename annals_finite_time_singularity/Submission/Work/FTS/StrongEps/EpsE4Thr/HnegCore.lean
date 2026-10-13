/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsE4Thr/HnegCore.lean` — the algebraic core of the `hneg` clause (item (VII))

The level-four barrier (`apriori_fourth_of_barrier_open[_endpoint]`) consumes

  `hneg : ∀ τ ∈ Ico 0 T', E τ = Y → E4' τ < 0`,

and the proved energy identity (`DiagCurveISolution.EnergyDeriv_IP4_JfamP_of_solution`) supplies

  `E4' τ = 2 · IP4 … α (Pz (J_ε (epsRHSP τ))) x_τ`,   `x_τ = slice (JfamP ρ ε g) τ`.

So `hneg` is the sign statement `IP α f x < 0` for the scheme's right-hand side `f`, at the times
at which the barrier level is met.  The scheme's right-hand side splits as

  `epsRHSP τ = Pz (J_ε (epsWP τ))`,   `epsWP τ = dynLin α (JfamP ρ ε g) τ + dynRHS … τ`,

i.e. (up to the `O(ε)` double-mollification defect) a **dissipative** part
`dynLin = -𝓛_Γ^T x` and a **nonlinear** part.  This module isolates the sign argument:

* `IP_dynLin_le_of_eq` — the dissipative half at the barrier level: from the proved open-class
  coercivity `OpenLinear.IP_dynLin_le_open` and the comparability clause `UnifIPO.up` (which turns
  `IP α x x = Y` into `HkSq α 4 x ≥ Y / Cup`),
  `IP α (dynLin α g τ) x ≤ - cc · (Y / Cup)`;
* `hneg_core` — the algebraic core: if `f = u + w` pointwise with `u` dissipative
  (`IP α u x ≤ - cc (Y/Cup)`) and the small part bounded by `|IP α w x| ≤ P < cc (Y/Cup)`, then
  `IP α f x < 0`.

Hence the *whole* remaining content of `hneg` is the single nonlinear bound

  `|IP4 … α w x_τ| ≤ P`,  `P < cc · (Y / Cup)`,   `w := Pz (J_ε (epsRHSP τ)) - dynLin α (JfamP ρ ε g) τ`,

i.e. the N4 pairing estimate at the open-class slices together with the `O(ε)` defect estimate
(`IP_perturb`).  That is item (VII) of the owner notes.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenLinear
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_const_mul
import Submission.Work.FTS.StrongEps.PZeroScheme

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice dynLin)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The dissipative half of `hneg` at the barrier level.**

From the open-class coercivity of `𝓛_Γ^T` (`OpenLinear.IP_dynLin_le_open`, on `CoerAdmO`) and the
comparability clause `UnifIPO.up` — which, together with the barrier hypothesis `IP α x x = Y`,
gives `HkSq α 4 x ≥ Y / Cup` — the pairing of the linear part of the scheme with `x` is bounded by
`- cc (Y / Cup)`. -/
theorem IP_dynLin_le_of_eq {α α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ} {g : Fam} {τ : ℝ}
    (hIP : UnifIPO IP α₂ cc clo Cup Ccs) (hα : α ∈ Set.Ioc 0 α₂)
    (hcoer : CoerAdmO α (slice g τ))
    (hregL : RegQo α 4 (Work.Coercivity.LGammaT α (slice g τ)))
    {Y : ℝ} (hY : IP α (slice g τ) (slice g τ) = Y) :
    IP α (dynLin α g τ) (slice g τ) ≤ - cc * (Y / Cup) := by
  have hd := IP_dynLin_le_open (IP := IP) hIP hα hcoer hregL
  have hup := hIP.up α hα (slice g τ) hcoer
  have hCup : 0 < Cup := hIP.pos.2.2.2.1
  have hcc : 0 < cc := hIP.pos.2.1
  have hsq : Y / Cup ≤ Work.Spaces.HkSq α 4 (slice g τ) := by
    rw [div_le_iff₀ hCup]
    rw [← hY, mul_comm (Work.Spaces.HkSq α 4 (slice g τ)) Cup]
    exact hup
  have h2 : cc * (Y / Cup) ≤ cc * Work.Spaces.HkSq α 4 (slice g τ) :=
    mul_le_mul_of_nonneg_left hsq hcc.le
  linarith

/-- **The algebraic core of `hneg`.**  If the piece `f` of the scheme's right-hand side splits
pointwise as `f = u + w`, with the dissipative part `u` satisfying `IP α u x ≤ - cc (Y / Cup)` and
the nonlinear part bounded in the pairing by `|IP α w x| ≤ P < cc (Y / Cup)`, then the pairing of
`f` with `x` is strictly negative.

The three `RegQo α 4` hypotheses are what the algebraic clauses `UnifIPO.add_fst` consume; along
the route they are supplied by the class-`C` clause of the datum (every projected mollified slice
is `RegQo α 4`, and the pieces are pointwise combinations of such). -/
theorem hneg_core {IP : ℝ → Fn → Fn → ℝ} {α₂ cc clo Cup Ccs : ℝ}
    (hIP : UnifIPO IP α₂ cc clo Cup Ccs) {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂)
    {x u w f : Fn} {Y P : ℝ} (hx : CoerAdmO α x)
    (hu : RegQo α 4 u) (hw : RegQo α 4 w) (hf : RegQo α 4 f)
    (hfu : f = u + w)
    (hcoer : IP α u x ≤ - cc * (Y / Cup))
    (hP : |IP α w x| ≤ P) (hPlt : P < cc * (Y / Cup)) :
    IP α f x < 0 := by
  have hx4 : RegQo α 4 x := hx.regQoFour
  rw [hfu, hIP.add_fst α hα u w x hu hw hx4]
  have hwle : IP α w x ≤ P := le_trans (le_abs_self _) hP
  linarith

/-- **The algebraic core of `hneg`, in the `Qd`-form.**

Same as `hneg_core`, but the split `f = u + w` is only required on the open quadrant
`Work.Construction.Qd` (which is co-null for the pairing's measure): the congruence clause
`UnifIPO.congr_qd` transports the pairing across the difference.  This is the form in which the
route produces the split (the scheme's right-hand side is an explicit pointwise expression on the
quadrant). -/
theorem hneg_core_qd {IP : ℝ → Fn → Fn → ℝ} {α₂ cc clo Cup Ccs : ℝ}
    (hIP : UnifIPO IP α₂ cc clo Cup Ccs) {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂)
    {x u w f : Fn} {Y P : ℝ} (hx : CoerAdmO α x)
    (hu : RegQo α 4 u) (hw : RegQo α 4 w) (hf : RegQo α 4 f)
    (hfu : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = (u + w) z θ)
    (hcoer : IP α u x ≤ - cc * (Y / Cup))
    (hP : |IP α w x| ≤ P) (hPlt : P < cc * (Y / Cup)) :
    IP α f x < 0 := by
  have hx4 : RegQo α 4 x := hx.regQoFour
  rw [hIP.congr_qd α hα f (u + w) x hf hx4 hfu,
    hIP.add_fst α hα u w x hu hw hx4]
  have hwle : IP α w x ≤ P := le_trans (le_abs_self _) hP
  linarith

/-- **`hneg` of the level-four barrier, reduced to the pointwise split and the nonlinear
bound.**

Along the projected `P₀`-scheme the right-hand side of the energy identity is
`f = Pz (J_ε (epsRHSP τ))`, and the scheme's right-hand side decomposes on the quadrant as
`Pz (J_ε (epsRHSP τ)) = dynLin α (JfamP ρ ε g) τ + w`.  Given that split, the class data, the
insertion of the numerical factor `2` (`E4' τ = 2 · IP α f x`, which is the proved energy
identity), and the single **nonlinear bound** `|IP α w x| ≤ P < cc (Y/Cup)`, the energy
derivative is strictly negative — i.e. `hneg`.

The dissipative half is `IP_dynLin_le_of_eq` (from the proved coercivity `IP_dynLin_le_open` and
`UnifIPO.up`), so the only remaining input of item (VII) is the bound on `w` (the N4 pairing
estimate at the open-class slices, plus the `O(ε)` double-mollification defect). -/
theorem hneg_of_split {IP : ℝ → Fn → Fn → ℝ} {α₂ cc clo Cup Ccs : ℝ}
    (hIP : UnifIPO IP α₂ cc clo Cup Ccs) {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂)
    {ρ : ℝ × ℝ → ℝ} {ε T T' τ Y P : ℝ} {g : Fam} {E4' : ℝ → ℝ}
    (hcoer : CoerAdmO α (slice (JfamP ρ ε g) τ))
    (hL : RegQo α 4 (Work.Coercivity.LGammaT α (slice (JfamP ρ ε g) τ)))
    {f w : Fn} (hf : RegQo α 4 f) (hw : RegQo α 4 w)
    (hsplit : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      f z θ = (dynLin α (JfamP ρ ε g) τ + w) z θ)
    (hY : IP α (slice (JfamP ρ ε g) τ) (slice (JfamP ρ ε g) τ) = Y)
    (hP : |IP α w (slice (JfamP ρ ε g) τ)| ≤ P) (hPlt : P < cc * (Y / Cup))
    (hE4' : E4' τ = 2 * IP α f (slice (JfamP ρ ε g) τ)) :
    E4' τ < 0 := by
  have hu_eq : dynLin α (JfamP ρ ε g) τ
      = fun z θ => (-1 : ℝ) * Work.Coercivity.LGammaT α (slice (JfamP ρ ε g) τ) z θ := by
    rw [dynLin_eq_neg_LGammaT]
    funext z θ
    ring
  have hu : RegQo α 4 (dynLin α (JfamP ρ ε g) τ) := by
    rw [hu_eq]
    exact regQo_const_mul (c := (-1 : ℝ)) hL
  have hcoerY : IP α (dynLin α (JfamP ρ ε g) τ) (slice (JfamP ρ ε g) τ)
      ≤ - cc * (Y / Cup) :=
    IP_dynLin_le_of_eq (IP := IP) (g := JfamP ρ ε g) (τ := τ) hIP hα hcoer hL hY
  have hmain := hneg_core_qd (x := slice (JfamP ρ ε g) τ)
    (u := dynLin α (JfamP ρ ε g) τ) (w := w) (f := f) (Y := Y) (P := P)
    hIP hα hcoer hu hw hf hsplit hcoerY hP hPlt
  rw [hE4']
  linarith

/-! ## The explicit split of the energy derivative's vector field -/

/-- **The vector field of the energy identity, split into the dissipative part and the rest.**

Along the projected `P₀`-scheme the energy identity is
`E4' τ = 2 · IP α f x_τ` with `f = Pz (J_ε (epsRHSP τ))` and `x_τ = slice (JfamP ρ ε g) τ`.  This
lemma writes `f` as `dynLin α (JfamP ρ ε g) τ + w` with `w` *explicitly*:

  `w = dynRHS τ + (J_ε(epsWP τ) − epsWP τ) − c₁ · bump + (J_ε(epsRHSP τ) − epsRHSP τ) − c₂ · bump`

(`c₁ = L₁₂(J_ε(epsWP τ))(0)/pzNorm`, `c₂ = L₁₂(J_ε(epsRHSP τ))(0)/pzNorm`), where the two `J_ε − id`
terms are the *mollification defects* and the two `c·bump` terms the *projection corrections*.  So
the nonlinear bound `|IP α w x| ≤ P` of `hneg_of_split` splits into the N4 estimate for `dynRHS`
and the `O(ε)` defect estimates (`IP_perturb`), which is exactly the content of item (VII). -/
theorem epsRHSP_split {α ε τ z θ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam} :
    Pz (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ)) z θ
      = Work.FTS.Galerkin.dynLin α (JfamP ρ ε g) τ z θ
        + (Work.FTS.Galerkin.dynRHS α (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g))
              (JfamP ρ ε g) τ z θ
            + (Work.FTS.StrongEps.Jeps ρ ε
                  (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ) z θ
                - Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ z θ)
            - (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε
                  (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ)) 0 / pzNorm) * bump z θ
            + (Work.FTS.StrongEps.Jeps ρ ε
                  (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ) z θ
                - Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ z θ)
            - (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε
                  (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ)) 0 / pzNorm) * bump z θ) := by
  have h2 : Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ z θ
      = Work.FTS.Galerkin.dynLin α (JfamP ρ ε g) τ z θ
        + Work.FTS.Galerkin.dynRHS α (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g))
            (JfamP ρ ε g) τ z θ := rfl
  have h1 : Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ z θ
      = Work.FTS.Galerkin.dynLin α (JfamP ρ ε g) τ z θ
        + Work.FTS.Galerkin.dynRHS α (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g))
            (JfamP ρ ε g) τ z θ
        + (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ) z θ
            - Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ z θ)
        - (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε
              (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ)) 0 / pzNorm) * bump z θ := by
    rw [Work.FTS.StrongEps.epsRHSP_eq_Pz_Jeps_epsWP, Pz_apply, h2]
    ring
  rw [Pz_apply, h1]
  ring

end Work.FTS.StrongEps.EpsE4Thr
