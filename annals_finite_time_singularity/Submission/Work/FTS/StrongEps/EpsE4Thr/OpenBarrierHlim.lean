/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsE4Thr/OpenBarrierHlim.lean` — the level-four barrier with the endpoint handled by a
**Fatou/limsup** condition instead of continuity

`OpenBarrierEndpoint.apriori_fourth_of_barrier_open_endpoint` reduced the continuity input of the
level-four barrier to the single one-sided condition `ContinuousWithinAt E (Icc 0 T') T'`.  That is
still more than the route can supply: the *energy* `E = IP α x x` is a pairing of order-four slots,
and its left limit at `T'` is not available.

What the route **does** supply (given joint regularity of the flow on the closed slab) is the
a.e. convergence of the slots `mixed a b (slice (JfamP ρ ε g) s) → mixed a b (slice (JfamP ρ ε g) T')`
as `s → T'` from the left.  By Fatou (`HkSq_le_of_ae_tendsto_mixed`) this yields the **one-sided
limsup bound**

  `hlimsq : ∀ B, (∀ τ ∈ Ico 0 T', HkSq α 4 (x τ) ≤ B) → HkSq α 4 (x T') ≤ B`,

which is all the barrier needs: the barrier on `Ico 0 T'` (from `hderiv` alone) gives
`E τ ≤ Y` for `τ < T'`; the coercivity clause `lo` gives `HkSq α 4 (x τ) ≤ Y / clo` there; and
`hlimsq` extends that bound to `T'`; finally `Xn = √(HkSq)` and `Y ≤ clo (C₀α²)²` turn it into
`Xn α (x τ) ≤ C₀ α²`.

This module records that route: `apriori_fourth_of_barrier_open_hlim` (the barrier with `hlimsq`),
its clause-level composite, and the two open-class *level conditions* used to produce `h0`.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.EpsE4Thr.BarrierIco
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenBarrier
import Submission.Work.FTS.StrongEps.EpsE4Thr.UnifIPOIP4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "IP4" => Work.FTS.CoercivityFix.Assembly.IP4

/-! ## The level condition in the open class -/

/-- **The exact datum condition for `h0` of the level-four barrier, in the open class.**  If the
admissible datum `x` satisfies `Xn α x < √(clo/Cup) · r`, then its energy is strictly below the
level `clo · r²`.  The open-class twin of `BarrierThreshold.energy_lt_of_strict_norm` (which is
stated for the frozen `UnifIP`/`CoerAdm`). -/
theorem energy_lt_of_strict_norm_open {α α₂ cc clo Cup Ccs r : ℝ} {IP : ℝ → Fn → Fn → ℝ} {x : Fn}
    (hIP : UnifIPO IP α₂ cc clo Cup Ccs) (hα : α ∈ Set.Ioc 0 α₂) (hx : CoerAdmO α x)
    (hX : Work.FTS.Nonlin.Xn α x < Real.sqrt (clo / Cup) * r) :
    IP α x x < clo * r ^ 2 := by
  have hCup : 0 < Cup := hIP.pos.2.2.2.1
  have hclo : 0 < clo := hIP.pos.2.2.1
  have hup := hIP.up α hα x hx
  have hsq : Work.Spaces.HkSq α 4 x = (Work.FTS.Nonlin.Xn α x) ^ 2 := by
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
      Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 x)]
  have hratio : (0 : ℝ) ≤ clo / Cup := div_nonneg hclo.le hCup.le
  have hXnn : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α x := Work.Spaces.HkNorm_nonneg α 4 x
  have hsqX : (Work.FTS.Nonlin.Xn α x) ^ 2 < (Real.sqrt (clo / Cup) * r) ^ 2 :=
    pow_lt_pow_left₀ hX hXnn (by norm_num)
  have hsqrt2 : (Real.sqrt (clo / Cup)) ^ 2 = clo / Cup := Real.sq_sqrt hratio
  calc IP α x x ≤ Cup * Work.Spaces.HkSq α 4 x := hup
    _ = Cup * (Work.FTS.Nonlin.Xn α x) ^ 2 := by rw [hsq]
    _ < Cup * (Real.sqrt (clo / Cup) * r) ^ 2 := mul_lt_mul_of_pos_left hsqX hCup
    _ = clo * r ^ 2 := by
        rw [mul_pow, hsqrt2]
        field_simp

/-- **`h0` of the level-four barrier from the sharp datum bound**, open class: at the barrier level
`clo · (C₀α²)²` the datum condition is `Xn α x < √(clo/Cup) · C₀ α²`. -/
theorem h0_of_datum_ratio_open {α α₂ cc clo Cup Ccs C₀ : ℝ} {IP : ℝ → Fn → Fn → ℝ} {x : Fn}
    (hIP : UnifIPO IP α₂ cc clo Cup Ccs) (hα : α ∈ Set.Ioc 0 α₂) (hx : CoerAdmO α x)
    (hX : Work.FTS.Nonlin.Xn α x < Real.sqrt (clo / Cup) * (C₀ * α ^ 2)) :
    IP α x x < clo * (C₀ * α ^ 2) ^ 2 :=
  energy_lt_of_strict_norm_open hIP hα hx hX

/-! ## The barrier with the Fatou/limsup condition -/

/-- **The level-four barrier of the a-priori estimate, with the endpoint handled by a one-sided
`ℋ⁴`-limsup condition.**

The analogue of `apriori_fourth_of_barrier_open`/`…_endpoint`, with the continuity hypothesis
replaced by

  `hlimsq : ∀ B, (∀ τ ∈ Ico 0 T', HkSq α 4 (x τ) ≤ B) → HkSq α 4 (x T') ≤ B`,

which is what the a.e. slot convergence at `T'` gives by Fatou
(`HkSq_le_of_ae_tendsto_mixed`).  The barrier on `Ico 0 T'` (`barrier_within_Ico_of_hasDerivWithinAt`,
fed only by `hderiv`) gives the energy bound there, `lo` converts it into an `ℋ⁴`-bound, and
`hlimsq` extends the latter to `T'`. -/
theorem apriori_fourth_of_barrier_open_hlim {α C₀ Y cc clo Cup Ccs α₂ : ℝ}
    {IP : ℝ → Fn → Fn → ℝ}
    {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {ε T T' : ℝ} {g : Fam} {E4' : ℝ → ℝ}
    (hIP : UnifIPO IP α₂ cc clo Cup Ccs) (hα : α ∈ Set.Ioc 0 α₂)
    (hC₀ : 0 < C₀) (hY0 : 0 < Y) (hY : Y ≤ clo * (C₀ * α ^ 2) ^ 2)
    (hT' : 0 < T')
    (hreg : Work.FTS.StrongEps.EpsRegP α ρ ε T' g)
    (hlimsq : ∀ B : ℝ,
      (∀ τ ∈ Set.Ico 0 T', Work.Spaces.HkSq α 4 (slice (JfamP ρ ε g) τ) ≤ B) →
      Work.Spaces.HkSq α 4 (slice (JfamP ρ ε g) T') ≤ B)
    (h0 : IP α (slice (JfamP ρ ε g) 0) (slice (JfamP ρ ε g) 0) < Y)
    (hderiv : ∀ τ ∈ Set.Ico 0 T', HasDerivWithinAt
      (fun s => IP α (slice (JfamP ρ ε g) s) (slice (JfamP ρ ε g) s)) (E4' τ) (Set.Icc 0 T') τ)
    (hneg : ∀ τ ∈ Set.Ico 0 T', IP α (slice (JfamP ρ ε g) τ) (slice (JfamP ρ ε g) τ) = Y →
      E4' τ < 0) :
    ∀ τ ∈ Set.Icc 0 T',
      Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 := by
  have hcoer : ∀ τ ∈ Set.Icc 0 T', CoerAdmO α (slice (JfamP ρ ε g) τ) :=
    coerAdmO_slice_JfamP hreg
  have hclo : 0 < clo := hIP.pos.2.2.1
  -- the barrier on the half-open interval, from `hderiv` alone
  have hbar : ∀ τ ∈ Set.Ico 0 T',
      IP α (slice (JfamP ρ ε g) τ) (slice (JfamP ρ ε g) τ) ≤ Y :=
    barrier_within_Ico_of_hasDerivWithinAt
      (E := fun s => IP α (slice (JfamP ρ ε g) s) (slice (JfamP ρ ε g) s))
      (E' := E4') (Y := Y) (T := T') hT' hderiv h0 hneg
  -- the induced `ℋ⁴`-bound on the half-open interval
  have hsqIco : ∀ τ ∈ Set.Ico 0 T', Work.Spaces.HkSq α 4 (slice (JfamP ρ ε g) τ) ≤ Y / clo := by
    intro τ hτ
    have h1 := hIP.lo α hα _ (hcoer τ ⟨hτ.1, hτ.2.le⟩)
    have h2 := hbar τ hτ
    rw [le_div_iff₀ hclo, mul_comm (Work.Spaces.HkSq α 4 (slice (JfamP ρ ε g) τ)) clo]
    linarith
  -- the Fatou step at the endpoint
  have hsqT : Work.Spaces.HkSq α 4 (slice (JfamP ρ ε g) T') ≤ Y / clo := hlimsq _ hsqIco
  have hlev : Y / clo ≤ (C₀ * α ^ 2) ^ 2 := by
    rw [div_le_iff₀ hclo, mul_comm ((C₀ * α ^ 2) ^ 2) clo]
    exact hY
  have hZnn : 0 ≤ C₀ * α ^ 2 := by positivity
  intro τ hτ
  have hsq : Work.Spaces.HkSq α 4 (slice (JfamP ρ ε g) τ) ≤ (C₀ * α ^ 2) ^ 2 := by
    rcases lt_or_eq_of_le hτ.2 with h | h
    · exact le_trans (hsqIco τ ⟨hτ.1, h⟩) hlev
    · rw [h]; exact le_trans hsqT hlev
  have hnorm : Real.sqrt (Work.Spaces.HkSq α 4 (slice (JfamP ρ ε g) τ)) ≤ C₀ * α ^ 2 := by
    have h1 := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hZnn] at h1
  simpa [Work.Spaces.HkNorm, Work.FTS.Nonlin.Xn] using hnorm

/-- **The level-four small ball from the four open-class clauses, with the Fatou/limsup endpoint
condition.**  The analogue of `AprioriFourthOpen.apriori_fourth_of_open_clauses` with `hcont`
replaced by `hlimsq`. -/
theorem apriori_fourth_of_open_clauses_hlim {α C₀ Y cc clo Cup c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ}
    {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {ε T T' : ℝ} {g : Fam} {E4' : ℝ → ℝ}
    (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂) (h₁' : 0 ≤ c₁') (h₂' : 0 ≤ c₂')
    (h₁'' : 0 ≤ c₁'') (h₂'' : 0 ≤ c₂'')
    {α₂ : ℝ} (hα₂ : 0 < α₂) (hcc : 0 < cc) (hclo : 0 < clo) (hCup : 0 < Cup)
    (hlo : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, CoerAdmO α f →
      clo * Work.Spaces.HkSq α 4 f ≤ IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f f)
    (hup : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, CoerAdmO α f →
      IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f f ≤ Cup * Work.Spaces.HkSq α 4 f)
    (hcoer : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, CoerAdmO α f →
      cc * Work.Spaces.HkSq α 4 f
        ≤ IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (Work.Coercivity.LGammaT α f) f)
    (hdz : ∃ Cdz : ℝ, 0 < Cdz ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, CoerAdmO α f →
      |IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (Work.Spaces.Dz f) f| ≤ Cdz * Work.FTS.Nonlin.Xn α f ^ 2)
    (hα : α ∈ Set.Ioc 0 α₂) (hα1 : α ≤ 1) (hC₀ : 0 < C₀) (hY0 : 0 < Y)
    (hY : Y ≤ clo * (C₀ * α ^ 2) ^ 2) (hT' : 0 < T')
    (hreg : Work.FTS.StrongEps.EpsRegP α ρ ε T' g)
    (hlimsq : ∀ B : ℝ,
      (∀ τ ∈ Set.Ico 0 T', Work.Spaces.HkSq α 4 (slice (JfamP ρ ε g) τ) ≤ B) →
      Work.Spaces.HkSq α 4 (slice (JfamP ρ ε g) T') ≤ B)
    (h0 : IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
      (slice (JfamP ρ ε g) 0) (slice (JfamP ρ ε g) 0) < Y)
    (hderiv : ∀ τ ∈ Set.Ico 0 T', HasDerivWithinAt
      (fun s => IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
        (slice (JfamP ρ ε g) s) (slice (JfamP ρ ε g) s)) (E4' τ) (Set.Icc 0 T') τ)
    (hneg : ∀ τ ∈ Set.Ico 0 T', IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
      (slice (JfamP ρ ε g) τ) (slice (JfamP ρ ε g) τ) = Y → E4' τ < 0) :
    ∀ τ ∈ Set.Icc 0 T',
      Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 := by
  obtain ⟨Ccs, hCcs_pos, hU⟩ :=
    unifIPO_IP4_of_open_clauses h₁ h₂ h₁' h₂' h₁'' h₂'' hα₂ hcc hclo hCup
      hlo hup hcoer hdz
  exact apriori_fourth_of_barrier_open_hlim (IP := IP4 c₁ c₂ c₁' c₂' c₁'' c₂'')
    (α := α) (α₂ := min α₂ 1) (C₀ := C₀) (Y := Y) (cc := cc) (clo := clo) (Cup := Cup)
    (Ccs := Ccs) (ρ := ρ) (Φs := Φs) (E := E) (g₀ := g₀) (ε := ε) (T := T) (T' := T')
    (g := g) (E4' := E4') hU ⟨hα.1, le_min hα.2 hα1⟩
    hC₀ hY0 hY hT' hreg hlimsq h0 hderiv hneg

end Work.FTS.StrongEps.EpsE4Thr
