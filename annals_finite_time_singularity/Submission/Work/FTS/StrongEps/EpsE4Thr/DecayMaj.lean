/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/DecayMaj.lean` — the **majorant (`Maj`) clause** of
`EpsUniformMem`, and the repair of `AprioriDecay`

`EpsUniformMem` (`Submission/Work/FTS/StrongEps/EpsMem.lean`) has, as the *last* conjunct of each
per-`τ` conjunction, the clause `EpsDecay α ρ Φs E ε τ g Maj`, where `Maj` is chosen **before** the
quantifier over `ε` (hence uniformly in the approximating sequence).  `EpsDecay` requires

* `0 ≤ Maj`, `Maj ≤ 1` and `IntegrableOn (fun z => Maj z / z) (Ioi 0)`, and
* pointwise domination `|D_z^jD_θ^i f z θ| ≤ Maj z` (`SlotMaj 1`) of the *projected* slice
  `f = slice (JfamP ρ ε g) τ`, and `SlotMaj 0` of the three elliptic blocks of
  `PhiTil α f (slice (PsiCan Φs E (JfamP ρ ε g)) τ)`.

**Status of the clause in the tree.**  Nothing produces it.  Its only consumer is
`Reduction.EpsUniformMem_of_localStep_apriori`, through the *hypothesis*
`AprioriDecay α ρ T Φs E g₀ Maj`; the lead's session-15 note
(`StrongEps/NOTES_session15.md` §1) records that this makes `AprioriDecay` "the (new) analytic
obligation of the E4 chapter".  This file starts that chapter: it fixes the vocabulary of the
clause (`thetaSup`, the packaging `exists_Maj_of_thetaSup`), assembles `EpsDecay` from four
`SlotMaj`-bounds (`EpsDecay_of_Maj`), and provides the *repaired* interface
`AprioriDecayB`/`EpsUniformMem_of_localStep_aprioriB`.

**The defect of `AprioriDecay` as defined.**  It quantifies over *all* `g` with `IsEpsSolP` and
`EpsRegP`, and `EpsRegP` carries no *size* bound on `Xn α (slice (JfamP ρ ε g) τ)` — only the
`ℋ⁶`-membership and the class-`C` clause.  But the domination `|f z θ| ≤ Maj z ≤ 1` is a
*pointwise* bound, and every available pointwise estimate is proportional to a *norm* of the
profile (`hkMem_pointwise_min`: `|mixed j i f z θ| ≤ C·min z 1·HkNorm α 4 f`).  Hence a single
`Maj`, fixed before `g`, cannot dominate the slices of *all* `EpsRegP`-solutions: the honest
interface is the ball-carrying `AprioriDecayB`, whose extra clause is exactly what `AprioriP`
proves and what the reduction has in hand.  `AprioriDecayB` is a *weakening* of `AprioriDecay`
(`AprioriDecay.toB`), so every future producer of the un-balled form is still usable.

**Second observation (interface item).**  `SlotMaj` quantifies over **all** `θ : ℝ`, not only the
open quadrant.  For the *projected slice* this is harmless (`Jeps` and `bump` both vanish off the
quadrant, so `Pz (J_ε f)` does too, and `ClassC.norm` records the same for class-`C` profiles;
the slots vanish off the quadrant as well), but nothing in the tree controls the off-quadrant
values of the elliptic blocks `Rop α (PhiTil α f Φg)` (`Φg = Φs + E f`; `StarPkgo2.smooth` and
`EllPkgGo.smooth` are statements about the *open* quadrant only, and the numerical operators
`Rop`/`Uop`/`Vop` are totalised at the junk angles).  A producer of `EpsDecay` therefore needs
either a `normTh`-type vanishing clause on `Φs`/`E f`, or the restriction of `SlotMaj` to
`θ ∈ Ioo 0 (π/2)`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.Reduction

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
open Work.FTS.StrongGlobal (Xn6)
open Work.FTS.StrongGlobal (Xn6)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The angular supremum of the low slots -/

/-- **The angular supremum of the slots of order `≤ k`**, taken over the *rational* angles of the
open quadrant (a countable supremum, hence an a.e. strongly measurable function of `z` whenever the
slot functions are jointly continuous on the open quadrant — then this is the honest angular
supremum).

The majorant `Maj` of `EpsDecay` has to dominate this function; the content of the `Maj`-clause is
that some such function is `1/z`-integrable and `≤ 1`. -/
noncomputable def thetaSup (k : ℕ) (f : Fn) : ℝ → ℝ := fun z =>
  max 0 (⨆ q : ℚ, ⨆ p : Fin (k + 1) × Fin (k + 1),
    if ((q : ℝ) ∈ Set.Ioo 0 (π / 2)) ∧ ((p.1 : ℕ) + (p.2 : ℕ) ≤ k)
      then |Work.Spaces.mixed (p.1 : ℕ) (p.2 : ℕ) f z (q : ℝ)| else 0)

/-- `thetaSup` is nonnegative (the `max 0` in the definition). -/
theorem thetaSup_nonneg (k : ℕ) (f : Fn) (z : ℝ) : 0 ≤ thetaSup k f z := le_max_left _ _

/-- **The angular supremum is `≤ 1` on the open quadrant as soon as every slot is `≤ 1` there at
every angle.** -/
theorem thetaSup_le_one {k : ℕ} {f : Fn}
    (hpt : ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Set.Ioo 0 (π / 2), ∀ j i : ℕ, j + i ≤ k →
      |Work.Spaces.mixed j i f z θ| ≤ 1) {z : ℝ} (hz : z ∈ Set.Ioi 0) :
    thetaSup k f z ≤ 1 := by
  refine max_le zero_le_one ?_
  refine ciSup_le (fun q => ciSup_le (fun p => ?_))
  by_cases h : ((q : ℝ) ∈ Set.Ioo 0 (π / 2)) ∧ ((p.1 : ℕ) + (p.2 : ℕ) ≤ k)
  · rw [if_pos h]
    exact hpt z hz (q : ℝ) h.1 (p.1 : ℕ) (p.2 : ℕ) h.2
  · rw [if_neg h]
    exact zero_le_one

/-- **The majorant of `EpsDecay` from the angular supremum.**  If the slots of order `≤ k` of `f`
are dominated (at *every* angle, as `SlotMaj` demands) by `thetaSup k f`, the supremum is `≤ 1`
on the open quadrant and `thetaSup k f / ·` is integrable against `1/z`, then
`Maj := min 1 (thetaSup k f)` is a majorant for the slots of order `≤ k` in the sense of
`SlotMaj k`. -/
theorem exists_Maj_of_thetaSup {k : ℕ} {f : Fn}
    (hdom : ∀ z ∈ Set.Ioi 0, ∀ θ : ℝ, ∀ j i : ℕ, j + i ≤ k →
      |Work.Spaces.mixed j i f z θ| ≤ thetaSup k f z)
    (hint : IntegrableOn (fun z => thetaSup k f z / z) (Set.Ioi 0))
    (hone : ∀ z ∈ Set.Ioi 0, thetaSup k f z ≤ 1) :
    ∃ Maj : ℝ → ℝ, (∀ z, 0 ≤ Maj z) ∧ (∀ z, Maj z ≤ 1) ∧
      IntegrableOn (fun z => Maj z / z) (Set.Ioi 0) ∧ SlotMaj k Maj f := by
  refine ⟨fun z => min 1 (thetaSup k f z), fun z => le_min zero_le_one (thetaSup_nonneg k f z),
    fun z => min_le_left _ _, ?_, ?_⟩
  · -- the integrability on `Ioi 0` follows from `hint` by the pointwise identity on that set
    refine IntegrableOn.congr_fun hint ?_ measurableSet_Ioi
    intro z hz
    show thetaSup k f z / z = min 1 (thetaSup k f z) / z
    rw [min_eq_right (hone z hz)]
  · intro z hz θ j i hji
    have h1 : |Work.Spaces.mixed j i f z θ| ≤ thetaSup k f z := hdom z hz θ j i hji
    have h2 : min 1 (thetaSup k f z) = thetaSup k f z := min_eq_right (hone z hz)
    change |Work.Spaces.mixed j i f z θ| ≤ min 1 (thetaSup k f z)
    rw [h2]; exact h1

/-! ## The packaging from a `SlotMaj` bound -/

/-- **The `EpsDecay` majorant from a `SlotMaj` bound on a candidate `U`.**  This is the interface
consumed by the producers: it is enough to exhibit *one* function `U` (nonnegative, `≤ 1` on the
open quadrant, `1/z`-integrable) that dominates the slots of `f` at every angle. -/
theorem exists_Maj_of_slotMaj {k : ℕ} {f : Fn} {U : ℝ → ℝ}
    (h0 : ∀ z, 0 ≤ U z) (hSM : SlotMaj k U f)
    (hint : IntegrableOn (fun z => U z / z) (Set.Ioi 0))
    (hone : ∀ z ∈ Set.Ioi 0, U z ≤ 1) :
    ∃ Maj : ℝ → ℝ, (∀ z, 0 ≤ Maj z) ∧ (∀ z, Maj z ≤ 1) ∧
      IntegrableOn (fun z => Maj z / z) (Set.Ioi 0) ∧ SlotMaj k Maj f := by
  refine ⟨fun z => min 1 (U z), fun z => le_min zero_le_one (h0 z), fun z => min_le_left _ _,
    ?_, ?_⟩
  · refine IntegrableOn.congr_fun hint ?_ measurableSet_Ioi
    intro z hz
    show U z / z = min 1 (U z) / z
    rw [min_eq_right (hone z hz)]
  · intro z hz θ j i hji
    have h1 : |Work.Spaces.mixed j i f z θ| ≤ U z := hSM z hz θ j i hji
    have h2 : min 1 (U z) = U z := min_eq_right (hone z hz)
    change |Work.Spaces.mixed j i f z θ| ≤ min 1 (U z)
    rw [h2]; exact h1

/-- **The projected slice vanishes off the open quadrant** (both `Jeps` and `bump` do), which is
what makes the *junk angles* of `SlotMaj` harmless for the projected slices. -/
theorem Pz_Jeps_eq_zero_of_theta {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {f : Fn} {z θ : ℝ}
    (hθ : θ ∉ Set.Ioo 0 (π / 2)) : Pz (Jeps ρ ε f) z θ = 0 := by
  have hbox : ¬ (Real.pi / 4 < θ ∧ θ < 3 * Real.pi / 8) := fun hc =>
    hθ ⟨by linarith [Real.pi_pos, hc.1], by linarith [Real.pi_pos, hc.2]⟩
  have hb : bump z θ = 0 := by
    rw [bump_eq_zero_iff]
    right; right
    by_contra hcon
    push_neg at hcon
    exact hbox hcon
  rw [Pz_apply, Jeps_eq_zero_of_theta ρ ε f hθ, hb]
  ring

/-- **The `EpsDecay` majorant with an arbitrary cap `C`** (the lead's ruling of 2026-10-11: the
`Uop/sin 2θ` and `Vop` slots of `EpsDecay` require an explicit constant `C ≥ 3`, because their
explicit pieces do not vanish at `z = 0`).  Same construction as `exists_Maj_of_slotMaj`, with
`Maj := min (max 1 C) U`; the cap is `max 1 C` so that the `Maj ≤ 1` case is the special case
`C ≤ 1`. -/
theorem exists_Maj_of_slotMaj_le {k : ℕ} {f : Fn} {U : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h0 : ∀ z, 0 ≤ U z) (hSM : SlotMaj k U f)
    (hint : IntegrableOn (fun z => U z / z) (Set.Ioi 0))
    (hone : ∀ z ∈ Set.Ioi 0, U z ≤ C) :
    ∃ Maj : ℝ → ℝ, (∀ z, 0 ≤ Maj z) ∧ (∀ z, Maj z ≤ max 1 C) ∧
      IntegrableOn (fun z => Maj z / z) (Set.Ioi 0) ∧ SlotMaj k Maj f := by
  refine ⟨fun z => min (max 1 C) (U z), fun z => le_min (le_max_of_le_left zero_le_one)
    (h0 z), fun z => min_le_left _ _, ?_, ?_⟩
  · refine IntegrableOn.congr_fun hint ?_ measurableSet_Ioi
    intro z hz
    show U z / z = min (max 1 C) (U z) / z
    rw [min_eq_right (le_max_of_le_right (hone z hz))]
  · intro z hz θ j i hji
    have h1 : |Work.Spaces.mixed j i f z θ| ≤ U z := hSM z hz θ j i hji
    have h2 : min (max 1 C) (U z) = U z := min_eq_right (le_max_of_le_right (hone z hz))
    change |Work.Spaces.mixed j i f z θ| ≤ min (max 1 C) (U z)
    rw [h2]; exact h1

/-! ## Assembling `EpsDecay` from four `SlotMaj` bounds -/

/-- **`EpsDecay` from the four pointwise bounds.**  The five conjuncts of `EpsDecay` in
definitional order (bounded-block form, 2026-10-12: the three elliptic blocks `≤ 3` on the open
quadrant). -/
theorem EpsDecay_of_Maj {α : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {ε τ : ℝ} {g : Fam}
    {Maj : ℝ → ℝ}
    (h0 : ∀ z, 0 ≤ Maj z) (h1 : ∀ z, Maj z ≤ 1)
    (hint : IntegrableOn (fun z => Maj z / z) (Set.Ioi 0))
    (hs : SlotMaj 1 Maj (slice (JfamP ρ ε g) τ))
    (hB :
      ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
        |Work.Construction.Rop α (Work.Construction.PhiTil α (slice (JfamP ρ ε g) τ)
            (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) τ)) z θ| ≤ 3 ∧
        |Work.Construction.Uop α (Work.Construction.PhiTil α (slice (JfamP ρ ε g) τ)
            (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) τ)) z θ
            / Work.Construction.s2 θ| ≤ 3 ∧
        |Work.Construction.Vop (Work.Construction.PhiTil α (slice (JfamP ρ ε g) τ)
            (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) τ)) z θ| ≤ 3) :
    EpsDecay α ρ Φs E ε τ g Maj := ⟨h0, h1, hint, hs, hB⟩

/-! ## The repaired a-priori decay interface -/

/-- **The ball-carrying a-priori decay bound**: the honest form of `AprioriDecay`.  Its extra
clause is the *small ball* for the projected slices — exactly what `AprioriP` proves, and the
missing input that makes the pointwise domination producible (`Maj` must be chosen before the
solutions, so it can only be sized by a bound available *a priori*). -/
def AprioriDecayB (α : ℝ) (ρ : ℝ × ℝ → ℝ) (T : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (C₀ : ℝ) (Maj : ℝ → ℝ) : Prop :=
  IntegrableOn (fun z => Maj z / z) (Set.Ioi 0) ∧
    ∀ ε ∈ Set.Ioc 0 1, ∀ g : Fam, IsEpsSolP α ρ ε T Φs E g₀ g → EpsRegP α ρ ε T g →
      (∀ τ ∈ Set.Icc 0 T,
        Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2) →
      ∀ τ ∈ Set.Icc 0 T, EpsDecay α ρ Φs E ε τ g Maj

/-- **`AprioriDecay` implies `AprioriDecayB`**: the ball-carrying form is *weaker*, so every
producer of the un-balled form remains usable. -/
theorem AprioriDecay.toB {α : ℝ} {ρ : ℝ × ℝ → ℝ} {T : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {C₀ : ℝ} {Maj : ℝ → ℝ} (h : AprioriDecay α ρ T Φs E g₀ Maj) :
    AprioriDecayB α ρ T Φs E g₀ C₀ Maj :=
  ⟨h.1, fun ε hε g hsol hreg _ => h.2 ε hε g hsol hreg⟩

/-! ## The decay producer interface -/

/-- **The ball-carrying a-priori decay bound from a single majorant.**  This is the interface the
producers target: one function `Maj` (`0 ≤ ·`, `≤ 1`, `1/z`-integrable) whose slots dominate the
projected slice *and* the three elliptic blocks along every regular solution of the scheme with
the small ball. -/
theorem AprioriDecayB_of_Maj {α C₀ T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {Maj : ℝ → ℝ}
    (hint : IntegrableOn (fun z => Maj z / z) (Set.Ioi 0))
    (h0 : ∀ z, 0 ≤ Maj z) (h1 : ∀ z, Maj z ≤ 1)
    (hsl : ∀ ε ∈ Set.Ioc 0 1, ∀ g : Fam, IsEpsSolP α ρ ε T Φs E g₀ g → EpsRegP α ρ ε T g →
      (∀ τ ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2) →
      ∀ τ ∈ Set.Icc 0 T, SlotMaj 1 Maj (slice (JfamP ρ ε g) τ))
    (hB : ∀ ε ∈ Set.Ioc 0 1, ∀ g : Fam, IsEpsSolP α ρ ε T Φs E g₀ g → EpsRegP α ρ ε T g →
      (∀ τ ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2) →
      ∀ τ ∈ Set.Icc 0 T,
        ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
          |Work.Construction.Rop α (Work.Construction.PhiTil α (slice (JfamP ρ ε g) τ)
              (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) τ)) z θ| ≤ 3 ∧
          |Work.Construction.Uop α (Work.Construction.PhiTil α (slice (JfamP ρ ε g) τ)
              (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) τ)) z θ
              / Work.Construction.s2 θ| ≤ 3 ∧
          |Work.Construction.Vop (Work.Construction.PhiTil α (slice (JfamP ρ ε g) τ)
              (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) τ)) z θ| ≤ 3) :
    AprioriDecayB α ρ T Φs E g₀ C₀ Maj :=
  ⟨hint, fun ε hε g hsol hreg hb τ hτ =>
    EpsDecay_of_Maj (h0) (h1) hint (hsl ε hε g hsol hreg hb τ hτ)
      (hB ε hε g hsol hreg hb τ hτ)⟩

/-! ## The corrected assembly of `EpsUniformMem` -/

/-- **`EpsE4Thr` reduces to its two documented inputs plus the *ball-carrying* decay bound.**
This is `EpsUniformMem_of_localStep_apriori` with the hypothesis `hdec : AprioriDecay` replaced by
the weaker `hdecB : AprioriDecayB` (the ball is supplied by the a-priori bound `hbnd` at the point
where the decay clause is produced). -/
theorem EpsUniformMem_of_localStep_aprioriB {α C₀ K M : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {g₀ : Fn}
    (hvan : ∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0)
    (hρ : IsSmoothKernel ρ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K) (h6 : Xn6 α g₀ ≤ K * α ^ 2) (hM : K ≤ M)
    (hsmall : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε ∈ Set.Ioc 0 ε₁,
      Work.FTS.Nonlin.Xn α (Jeps ρ ε g₀) ≤ C₀ * α ^ 2)
    (hd : ∀ ε : ℝ, 0 < ε → EpsDatum α ρ ε g₀)
    (hstep : ∀ ε : ℝ, 0 < ε → LocalStepP α ρ ε Φs E C₀)
    (hapr : ∀ ε : ℝ, 0 < ε → ∀ T : ℝ, 0 < T → AprioriP α ρ ε T Φs E g₀ C₀ M)
    (hdecB : ∀ T : ℝ, 0 < T → ∃ Maj : ℝ → ℝ, AprioriDecayB α ρ T Φs E g₀ C₀ Maj) :
    EpsUniformMem α ρ Φs E g₀ C₀ K := by
  obtain ⟨ε₁, hε₁, hsmallb⟩ := hsmall
  refine ⟨hvan, l12_zero_of_epsDatum ⟨hα, hα1⟩ hρ hd, ?_⟩
  intro T hT
  obtain ⟨Maj, hMajint, hMaj⟩ := hdecB T hT
  refine ⟨M, hM, min ε₁ 1, lt_min hε₁ one_pos, Maj, hMajint, ?_⟩
  intro ε hε
  have hεpos : 0 < ε := hε.1
  have hεle : ε ≤ min ε₁ 1 := hε.2
  have hPz : Pz (Jeps ρ ε g₀) = Jeps ρ ε g₀ :=
    Pz_self_of_l12 (Work.FTS.ClassC.ClassC.l12_zero (hd ε hεpos).2.2)
  have hsmall₀ : Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε g₀)) ≤ C₀ * α ^ 2 := by
    rw [hPz]
    exact hsmallb ε ⟨hεpos, le_trans hεle (min_le_left _ _)⟩
  have hg₀M : Xn6 α g₀ ≤ M := by
    have hα2le : α ^ 2 ≤ 1 := pow_le_one₀ hα.le hα1
    calc Xn6 α g₀ ≤ K * α ^ 2 := h6
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left hα2le hK
      _ = K := mul_one K
      _ ≤ M := hM
  obtain ⟨g, hsol, hreg, hbnd⟩ :=
    exists_sol_of_localStep_apriori hT (le_trans hK hM) hg₀M hsmall₀
      (EpsDatum.toDatumP (hd ε hεpos)) (hstep ε hεpos) (hapr ε hεpos T hT)
  refine ⟨g, hsol, ?_⟩
  intro τ hτ
  have hdP : EpsDatumP α ρ ε (slice g τ) := hreg.2 τ hτ
  have hCmem : Work.Spaces.HkMem α 7 (slice (JfamP ρ ε g) τ) := hdP.2.2.mem
  have hCsm : Work.FTS.EllipticEst.SmoothOpen (slice (JfamP ρ ε g) τ) := hdP.2.2.reg
  have h4 : Work.Spaces.HkMem α 4 (slice (JfamP ρ ε g) τ) :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hCsm hCmem
  exact ⟨hdP.1, h4, hdP.2.1, (hbnd τ hτ).2, (hbnd τ hτ).1, by rw [slice_JfamP]; exact hdP.2.2,
    hreg.1,
    hMaj ε ⟨hεpos, le_trans hεle (min_le_right _ _)⟩ g hsol hreg
      (fun σ hσ => (hbnd σ hσ).2) τ hτ⟩

end Work.FTS.StrongEps.EpsE4Thr
