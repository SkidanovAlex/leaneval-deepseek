import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep7.flat_pair_transfer_le
import Submission.Work.Diff.STE.B3.SymCalcStep7.pairOp_aux
import Submission.Work.Diff.STE.B3.SymCalcStep7.flat_multiplier_gain
import Submission.Work.Diff.STE.B3.SymCalcStep6.lapPow_algebra
import Submission.Work.Diff.STE.B3.flat_diag_pairing_le
import Submission.Work.Diff.STE.flat.fourierCoeff_seriesFun
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliaries for the sharp pairing estimate `pairOp_pairing_le_sharp`

This file collects the `L2re`-calculus used by `pairOp_pairing_le_sharp`:

* the elementary algebra of the real pairing `L2re f g = Re ∫ f · conj g` (symmetry, moving
  multipliers from one side to the other, additivity/subtractivity of the continuous pairings);
* its Fourier representation and the **self-adjointness of the flat Fourier multipliers**
  `lapPow k` and `flatCut ρ ε`, whose symbols are real;
* the **adjointness of the chart transfer**: from the hypothesis
  `L2re u (compMap T v) = L2re (|det DT'| • compMap T' u) v` (the change of variables formula on the
  flat torus, proved in `compMap_adjoint.lean`) one gets the adjoints of `compMap T'`, and, with the
  Friedrichs cutoff `S_ε = flatCut ρ ε` in the middle, of the transported cutoff
  `V = conjCut ρ ε T T' = compMap T' ∘ S_ε ∘ compMap T` and of the transported Laplacian power
  `P = conjLapPow k T T' = compMap T ∘ Λ^k ∘ compMap T'`.
-/

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE.B3.SymCalcStep7

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. The Jacobian of the inverse chart transition, as a complex-valued multiplier -/

/-- The (complex-valued) Jacobian determinant `|det DT'|` of the inverse transition `T'`. -/
noncomputable def jacDetC (T' : (ι → ℝ) → (ι → ℝ)) : (ι → ℝ) → ℂ :=
  fun x => ((|(fderiv ℝ T' x).det| : ℝ) : ℂ)

/-- The reciprocal `1/|det DT'|`, as a multiplier. -/
noncomputable def jacInvC (T' : (ι → ℝ) → (ι → ℝ)) : (ι → ℝ) → ℂ :=
  fun x => (((|(fderiv ℝ T' x).det|)⁻¹ : ℝ) : ℂ)

/-- `|det DT'|` is real, hence fixed by `star`. -/
@[simp] theorem star_jacDetC (T' : (ι → ℝ) → (ι → ℝ)) (x : ι → ℝ) :
    star (jacDetC T' x) = jacDetC T' x := by
  simp only [jacDetC, Complex.star_def, Complex.conj_ofReal]

/-- `1/|det DT'|` is real, hence fixed by `star`. -/
@[simp] theorem star_jacInvC (T' : (ι → ℝ) → (ι → ℝ)) (x : ι → ℝ) :
    star (jacInvC T' x) = jacInvC T' x := by
  simp only [jacInvC, Complex.star_def, Complex.conj_ofReal]

/-- The structure facts about `jacDetC`/`jacInvC` that the adjointness lemmas need. -/
def JacFacts (T' : (ι → ℝ) → (ι → ℝ)) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (jacDetC T') ∧ Work.Diff.STE.Periodic1 (jacDetC T')
    ∧ (∀ x : ι → ℝ, jacDetC T' x ≠ 0)
    ∧ ContDiff ℝ (⊤ : ℕ∞) (jacInvC T') ∧ Work.Diff.STE.Periodic1 (jacInvC T')
    ∧ (∀ x : ι → ℝ, jacDetC T' x * jacInvC T' x = 1)

/-! ## 2. The elementary algebra of `L2re` -/

/-- `L2re` is symmetric. -/
theorem L2re_comm' (f g : (ι → ℝ) → ℂ) :
    Work.Diff.STE.L2re f g = Work.Diff.STE.L2re g f := by
  have h : (∫ x in Work.Diff.STE.unitCube, g x * star (f x))
      = star (∫ x in Work.Diff.STE.unitCube, f x * star (g x)) := by
    simp only [Complex.star_def]
    rw [← integral_conj (f := fun x : ι → ℝ => f x * (starRingEnd ℂ) (g x))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [map_mul, starRingEnd_self_apply]
    ring
  rw [Work.Diff.STE.L2re, Work.Diff.STE.L2re, h]
  rw [Complex.star_def, Complex.conj_re]

/-- Moving a multiplier from the second argument of `L2re` to the first. -/
theorem L2re_mul_snd (c f g : (ι → ℝ) → ℂ) :
    Work.Diff.STE.L2re f (fun x => c x * g x)
      = Work.Diff.STE.L2re (fun x => star (c x) * f x) g := by
  simp only [Work.Diff.STE.L2re]
  refine congrArg Complex.re ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [star_mul, star_star]
  ring

/-- Moving a multiplier from the first argument of `L2re` to the second. -/
theorem L2re_mul_fst (c f g : (ι → ℝ) → ℂ) :
    Work.Diff.STE.L2re (fun x => c x * f x) g
      = Work.Diff.STE.L2re f (fun x => star (c x) * g x) := by
  simp only [Work.Diff.STE.L2re]
  refine congrArg Complex.re ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [star_mul, star_star]
  ring

/-- Additivity of `L2re` in its second argument (for continuous entries). -/
theorem L2re_add_snd' {y g₁ g₂ : (ι → ℝ) → ℂ} (hy : Continuous y) (hg₁ : Continuous g₁)
    (hg₂ : Continuous g₂) :
    Work.Diff.STE.L2re y (g₁ + g₂) = Work.Diff.STE.L2re y g₁ + Work.Diff.STE.L2re y g₂ := by
  have h1 : Integrable (fun x : ι → ℝ => y x * star (g₁ x))
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous (hy.mul (continuous_star.comp hg₁))
  have h2 : Integrable (fun x : ι → ℝ => y x * star (g₂ x))
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous (hy.mul (continuous_star.comp hg₂))
  simp only [Work.Diff.STE.L2re]
  rw [show (fun x : ι → ℝ => y x * star ((g₁ + g₂) x))
      = fun x => y x * star (g₁ x) + y x * star (g₂ x) by
    funext x
    simp only [Pi.add_apply, star_add]
    ring]
  rw [integral_add h1 h2]
  exact Complex.add_re _ _

/-- Subtractivity of `L2re` in its second argument (for continuous entries). -/
theorem L2re_sub_snd' {y g₁ g₂ : (ι → ℝ) → ℂ} (hy : Continuous y) (hg₁ : Continuous g₁)
    (hg₂ : Continuous g₂) :
    Work.Diff.STE.L2re y (g₁ - g₂) = Work.Diff.STE.L2re y g₁ - Work.Diff.STE.L2re y g₂ := by
  have h1 : Integrable (fun x : ι → ℝ => y x * star (g₁ x))
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous (hy.mul (continuous_star.comp hg₁))
  have h2 : Integrable (fun x : ι → ℝ => y x * star (g₂ x))
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous (hy.mul (continuous_star.comp hg₂))
  simp only [Work.Diff.STE.L2re]
  rw [show (fun x : ι → ℝ => y x * star ((g₁ - g₂) x))
      = fun x => y x * star (g₁ x) - y x * star (g₂ x) by
    funext x
    simp only [Pi.sub_apply, star_sub]
    ring]
  rw [integral_sub h1 h2]
  exact Complex.sub_re _ _

/-- Additivity of `L2re` in its first argument (for continuous entries). -/
theorem L2re_add_fst' {y₁ y₂ g : (ι → ℝ) → ℂ} (hy₁ : Continuous y₁) (hy₂ : Continuous y₂)
    (hg : Continuous g) :
    Work.Diff.STE.L2re (y₁ + y₂) g = Work.Diff.STE.L2re y₁ g + Work.Diff.STE.L2re y₂ g := by
  have h1 : Integrable (fun x : ι → ℝ => y₁ x * star (g x))
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous (hy₁.mul (continuous_star.comp hg))
  have h2 : Integrable (fun x : ι → ℝ => y₂ x * star (g x))
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous (hy₂.mul (continuous_star.comp hg))
  simp only [Work.Diff.STE.L2re]
  rw [show (fun x : ι → ℝ => (y₁ + y₂) x * star (g x))
      = fun x => y₁ x * star (g x) + y₂ x * star (g x) by
    funext x
    simp only [Pi.add_apply]
    ring]
  rw [integral_add h1 h2]
  exact Complex.add_re _ _

/-- Subtractivity of `L2re` in its first argument (for continuous entries). -/
theorem L2re_sub_fst' {y₁ y₂ g : (ι → ℝ) → ℂ} (hy₁ : Continuous y₁) (hy₂ : Continuous y₂)
    (hg : Continuous g) :
    Work.Diff.STE.L2re (y₁ - y₂) g = Work.Diff.STE.L2re y₁ g - Work.Diff.STE.L2re y₂ g := by
  have h1 : Integrable (fun x : ι → ℝ => y₁ x * star (g x))
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous (hy₁.mul (continuous_star.comp hg))
  have h2 : Integrable (fun x : ι → ℝ => y₂ x * star (g x))
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous (hy₂.mul (continuous_star.comp hg))
  simp only [Work.Diff.STE.L2re]
  rw [show (fun x : ι → ℝ => (y₁ - y₂) x * star (g x))
      = fun x => y₁ x * star (g x) - y₂ x * star (g x) by
    funext x
    simp only [Pi.sub_apply]
    ring]
  rw [integral_sub h1 h2]
  exact Complex.sub_re _ _

/-! ## 3. The Fourier representation and self-adjointness of the flat multipliers -/

/-- **The Fourier representation of the real pairing**: for smooth `1`-periodic `f` and `g`,
`L2re f g = Re Σ_m f̂(m) conj(ĝ(m))`. -/
theorem L2re_eq_tsum (f g : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfp : Work.Diff.STE.Periodic1 f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgp : Work.Diff.STE.Periodic1 g) :
    Work.Diff.STE.L2re f g
      = (∑' m : ι → ℤ,
          Work.Diff.STE.fourierCoeff f m * star (Work.Diff.STE.fourierCoeff g m)).re := by
  have hg' : g = Work.Diff.STE.seriesFun (Work.Diff.STE.fourierCoeff g) :=
    funext fun x => (Work.Diff.STE.flat.seriesFun_fourierCoeff g hg hgp x).symm
  have h := Work.Diff.STE.B3.L2re_seriesFun_eq f hf hfp (Work.Diff.STE.fourierCoeff g)
    (Work.Diff.STE.B3.summable_norm_fourierCoeff g hg hgp)
  rw [← hg'] at h
  exact h

/-- **`lapPow k` is self-adjoint for the real pairing** (its symbol `flatLam m ^ k` is real). -/
theorem L2re_lapPow (k : ℕ) {f g : (ι → ℝ) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfp : Work.Diff.STE.Periodic1 f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgp : Work.Diff.STE.Periodic1 g) :
    Work.Diff.STE.L2re f (Work.Diff.STE.B3.SymCalcStep5.lapPow k g)
      = Work.Diff.STE.L2re (Work.Diff.STE.B3.SymCalcStep5.lapPow k f) g := by
  have hgl : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalcStep5.lapPow k g) :=
    (Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).2.2.1 g hg hgp
  have hglp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalcStep5.lapPow k g) :=
    (Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).2.2.2 g
  have hfl : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalcStep5.lapPow k f) :=
    (Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).2.2.1 f hf hfp
  have hflp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalcStep5.lapPow k f) :=
    (Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).2.2.2 f
  rw [L2re_eq_tsum f (Work.Diff.STE.B3.SymCalcStep5.lapPow k g) hf hfp hgl hglp,
    L2re_eq_tsum (Work.Diff.STE.B3.SymCalcStep5.lapPow k f) g hfl hflp hg hgp]
  refine congrArg Complex.re (tsum_congr fun m => ?_)
  rw [(Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).1 g hg hgp,
    (Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).1 f hf hfp]
  simp only [Complex.star_def, star_mul, Complex.conj_ofReal]
  ring

/-- **`flatCut ρ ε` is self-adjoint for the real pairing** (its symbol `ρ (ε • m)` is real). -/
theorem L2re_flatCut (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ)
    {f g : (ι → ℝ) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfp : Work.Diff.STE.Periodic1 f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgp : Work.Diff.STE.Periodic1 g) :
    Work.Diff.STE.L2re f (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g)
      = Work.Diff.STE.L2re (Work.Diff.STE.B3.SymCalc.flatCut ρ ε f) g := by
  have hgl : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε hg hgp
  have hglp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε g
  have hfl : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.flatCut ρ ε f) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε hf hfp
  have hflp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.flatCut ρ ε f) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε f
  rw [L2re_eq_tsum f (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) hf hfp hgl hglp,
    L2re_eq_tsum (Work.Diff.STE.B3.SymCalc.flatCut ρ ε f) g hfl hflp hg hgp]
  refine congrArg Complex.re (tsum_congr fun m => ?_)
  rw [Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_flatCut ρ hρ ε hg hgp,
    Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_flatCut ρ hρ ε hf hfp]
  simp only [Complex.star_def, star_mul, Complex.conj_ofReal]
  ring

/-! ## 4. The adjointness of the chart transfer -/

/-- **The adjoint of `compMap T`** (the change of variables hypothesis), restated with
`jacDetC`. -/
theorem L2re_compMap_T_adj {T T' : (ι → ℝ) → (ι → ℝ)}
    (hVadj : ∀ (u v : (ι → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
        ContDiff ℝ (⊤ : ℕ∞) v → Work.Diff.STE.Periodic1 v →
        Work.Diff.STE.L2re u (Work.Diff.STE.B3.SymCalc.compMap T v)
          = Work.Diff.STE.L2re (fun x : ι → ℝ => jacDetC T' x
              * Work.Diff.STE.B3.SymCalc.compMap T' u x) v)
    {u v : (ι → ℝ) → ℂ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hup : Work.Diff.STE.Periodic1 u)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvp : Work.Diff.STE.Periodic1 v) :
    Work.Diff.STE.L2re u (Work.Diff.STE.B3.SymCalc.compMap T v)
      = Work.Diff.STE.L2re (fun x : ι → ℝ => jacDetC T' x
          * Work.Diff.STE.B3.SymCalc.compMap T' u x) v :=
  hVadj u v hu hup hv hvp

/-- **The adjoint of `compMap T'`**: `⟨p, compMap T' q⟩ = ⟨compMap T (jacInvC T' · p), q⟩`. -/
theorem L2re_compMap_T'_adj {T T' : (ι → ℝ) → (ι → ℝ)} (hJac : JacFacts T')
    (hVadj : ∀ (u v : (ι → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
        ContDiff ℝ (⊤ : ℕ∞) v → Work.Diff.STE.Periodic1 v →
        Work.Diff.STE.L2re u (Work.Diff.STE.B3.SymCalc.compMap T v)
          = Work.Diff.STE.L2re (fun x : ι → ℝ => jacDetC T' x
              * Work.Diff.STE.B3.SymCalc.compMap T' u x) v)
    {p q : (ι → ℝ) → ℂ} (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hpp : Work.Diff.STE.Periodic1 p)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hqp : Work.Diff.STE.Periodic1 q) :
    Work.Diff.STE.L2re p (Work.Diff.STE.B3.SymCalc.compMap T' q)
      = Work.Diff.STE.L2re (Work.Diff.STE.B3.SymCalc.compMap T
          (fun y : ι → ℝ => jacInvC T' y * p y)) q := by
  have hJsm : ContDiff ℝ (⊤ : ℕ∞) (jacDetC T') := hJac.1
  have hJper : Work.Diff.STE.Periodic1 (jacDetC T') := hJac.2.1
  have hJne : ∀ x : ι → ℝ, jacDetC T' x ≠ 0 := hJac.2.2.1
  have hKsm : ContDiff ℝ (⊤ : ℕ∞) (jacInvC T') := hJac.2.2.2.1
  have hKper : Work.Diff.STE.Periodic1 (jacInvC T') := hJac.2.2.2.2.1
  have hJK : ∀ x : ι → ℝ, jacDetC T' x * jacInvC T' x = 1 := hJac.2.2.2.2.2
  have husm : ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => jacInvC T' y * p y) := hKsm.mul hp
  have huper : Work.Diff.STE.Periodic1 (fun y : ι → ℝ => jacInvC T' y * p y) :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hKper hpp
  have hkey := hVadj q (fun y : ι → ℝ => jacInvC T' y * p y) hq hqp husm huper
  have hrhs : Work.Diff.STE.L2re (fun x : ι → ℝ => jacDetC T' x
        * Work.Diff.STE.B3.SymCalc.compMap T' q x)
      (fun y : ι → ℝ => jacInvC T' y * p y)
      = Work.Diff.STE.L2re (Work.Diff.STE.B3.SymCalc.compMap T' q) p := by
    rw [L2re_mul_fst]
    refine congrArg (fun w => Work.Diff.STE.L2re (Work.Diff.STE.B3.SymCalc.compMap T' q) w) ?_
    funext y
    rw [star_jacDetC, ← mul_assoc, hJK y, one_mul]
  rw [L2re_comm' p (Work.Diff.STE.B3.SymCalc.compMap T' q),
    L2re_comm' (Work.Diff.STE.B3.SymCalc.compMap T (fun y : ι → ℝ => jacInvC T' y * p y)) q,
    ← hrhs]
  exact hkey.symm

/-- **The adjoint of the transported cutoff** `V = conjCut ρ ε T T'`:
`⟨p, V q⟩ = ⟨jacDetC T' · V (jacInvC T' · p), q⟩`. -/
theorem L2re_conjCut_adj {T T' : (ι → ℝ) → (ι → ℝ)} (hJac : JacFacts T')
    (hVadj : ∀ (u v : (ι → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
        ContDiff ℝ (⊤ : ℕ∞) v → Work.Diff.STE.Periodic1 v →
        Work.Diff.STE.L2re u (Work.Diff.STE.B3.SymCalc.compMap T v)
          = Work.Diff.STE.L2re (fun x : ι → ℝ => jacDetC T' x
              * Work.Diff.STE.B3.SymCalc.compMap T' u x) v)
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    {p q : (ι → ℝ) → ℂ} (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hpp : Work.Diff.STE.Periodic1 p)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hqp : Work.Diff.STE.Periodic1 q) :
    Work.Diff.STE.L2re p (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' q)
      = Work.Diff.STE.L2re (fun x : ι → ℝ => jacDetC T' x
          * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' (fun y : ι → ℝ => jacInvC T' y * p y) x)
        q := by
  have hKsm : ContDiff ℝ (⊤ : ℕ∞) (jacInvC T') := hJac.2.2.2.1
  have hKper : Work.Diff.STE.Periodic1 (jacInvC T') := hJac.2.2.2.2.1
  have hpinv : ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => jacInvC T' y * p y) := hKsm.mul hp
  have hpinvp : Work.Diff.STE.Periodic1 (fun y : ι → ℝ => jacInvC T' y * p y) :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hKper hpp
  have hAp : ContDiff ℝ (⊤ : ℕ∞)
      (Work.Diff.STE.B3.SymCalc.compMap T (fun y : ι → ℝ => jacInvC T' y * p y)) :=
    hpinv.comp hT
  have hApp : Work.Diff.STE.Periodic1
      (Work.Diff.STE.B3.SymCalc.compMap T (fun y : ι → ℝ => jacInvC T' y * p y)) := by
    intro i x
    show jacInvC T' (T (x + Pi.single i 1)) * p (T (x + Pi.single i 1))
      = jacInvC T' (T x) * p (T x)
    rw [hTper i x]
    exact hpinvp i (T x)
  have hSA : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
      (Work.Diff.STE.B3.SymCalc.compMap T (fun y : ι → ℝ => jacInvC T' y * p y))) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε hAp hApp
  have hSAp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
      (Work.Diff.STE.B3.SymCalc.compMap T (fun y : ι → ℝ => jacInvC T' y * p y))) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε _
  have hAq : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.compMap T q) := hq.comp hT
  have hAqp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.compMap T q) := by
    intro i x
    show q (T (x + Pi.single i 1)) = q (T x)
    rw [hTper i x]
    exact hqp i (T x)
  have hSAq : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
      (Work.Diff.STE.B3.SymCalc.compMap T q)) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε hAq hAqp
  have hSAqp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
      (Work.Diff.STE.B3.SymCalc.compMap T q)) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε _
  rw [show Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' q
      = Work.Diff.STE.B3.SymCalc.compMap T'
          (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Work.Diff.STE.B3.SymCalc.compMap T q))
      from rfl]
  rw [L2re_compMap_T'_adj (q := Work.Diff.STE.B3.SymCalc.flatCut ρ ε
        (Work.Diff.STE.B3.SymCalc.compMap T q)) hJac hVadj hp hpp hSAq hSAqp]
  rw [L2re_flatCut ρ hρ ε hAp hApp hAq hAqp]
  rw [L2re_compMap_T_adj hVadj hSA hSAp hq hqp]
  refine congrArg (fun w => Work.Diff.STE.L2re w q) ?_
  funext x
  rfl

/-- **The adjoint of the transported Laplacian power** `P = conjLapPow k T T'`:
`⟨p, P q⟩ = ⟨jacInvC T' ∘ T · Λ^k (jacDetC T' · compMap T' p), q⟩`. -/
theorem L2re_conjLapPow_adj {T T' : (ι → ℝ) → (ι → ℝ)} (hJac : JacFacts T')
    (hVadj : ∀ (u v : (ι → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
        ContDiff ℝ (⊤ : ℕ∞) v → Work.Diff.STE.Periodic1 v →
        Work.Diff.STE.L2re u (Work.Diff.STE.B3.SymCalc.compMap T v)
          = Work.Diff.STE.L2re (fun x : ι → ℝ => jacDetC T' x
              * Work.Diff.STE.B3.SymCalc.compMap T' u x) v)
    (k : ℕ) (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    {p q : (ι → ℝ) → ℂ} (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hpp : Work.Diff.STE.Periodic1 p)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hqp : Work.Diff.STE.Periodic1 q) :
    Work.Diff.STE.L2re p (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' q)
      = Work.Diff.STE.L2re (fun x : ι → ℝ => jacInvC T' (T x)
          * Work.Diff.STE.B3.SymCalcStep5.lapPow k
              (fun z : ι → ℝ => jacDetC T' z * p (T' z)) (T x)) q := by
  have hJsm : ContDiff ℝ (⊤ : ℕ∞) (jacDetC T') := hJac.1
  have hJper : Work.Diff.STE.Periodic1 (jacDetC T') := hJac.2.1
  have hT'per : ∀ (i : ι) (y : ι → ℝ), T' (y + Pi.single i 1) = T' y + Pi.single i 1 :=
    Work.Diff.STE.B3.SymCalcStep1.shift_T' T T' hTper hTinv1 hTinv2
  have hA'p : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.compMap T' p) := hp.comp hT'
  have hA'pp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.compMap T' p) := by
    intro i y
    show p (T' (y + Pi.single i 1)) = p (T' y)
    rw [hT'per i y]
    exact hpp i (T' y)
  have hA'q : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.compMap T' q) := hq.comp hT'
  have hA'qp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.compMap T' q) := by
    intro i y
    show q (T' (y + Pi.single i 1)) = q (T' y)
    rw [hT'per i y]
    exact hqp i (T' y)
  have hJp : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ι → ℝ => jacDetC T' z * Work.Diff.STE.B3.SymCalc.compMap T' p z) :=
    hJsm.mul hA'p
  have hJpp : Work.Diff.STE.Periodic1
      (fun z : ι → ℝ => jacDetC T' z * Work.Diff.STE.B3.SymCalc.compMap T' p z) :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hJper hA'pp
  have hLsm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalcStep5.lapPow k
      (fun z : ι → ℝ => jacDetC T' z * Work.Diff.STE.B3.SymCalc.compMap T' p z)) :=
    (Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).2.2.1 _ hJp hJpp
  have hLsp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalcStep5.lapPow k
      (fun z : ι → ℝ => jacDetC T' z * Work.Diff.STE.B3.SymCalc.compMap T' p z)) :=
    (Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).2.2.2 _
  have hΛA'q : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalcStep5.lapPow k
      (Work.Diff.STE.B3.SymCalc.compMap T' q)) :=
    (Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).2.2.1 _ hA'q hA'qp
  have hΛA'qp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalcStep5.lapPow k
      (Work.Diff.STE.B3.SymCalc.compMap T' q)) :=
    (Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).2.2.2 _
  rw [show Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' q
      = Work.Diff.STE.B3.SymCalc.compMap T
          (Work.Diff.STE.B3.SymCalcStep5.lapPow k (Work.Diff.STE.B3.SymCalc.compMap T' q))
      from rfl]
  rw [L2re_compMap_T_adj hVadj hp hpp hΛA'q hΛA'qp]
  rw [L2re_lapPow k hJp hJpp hA'q hA'qp]
  rw [L2re_compMap_T'_adj hJac hVadj hLsm hLsp hq hqp]
  refine congrArg (fun w => Work.Diff.STE.L2re w q) ?_
  funext x
  rfl

/-! ## 5. Linearity (subtractivity) of the operators, and `CSq` bookkeeping -/

/-- `seriesFun` commutes with negation. -/
theorem seriesFun_neg (c : (ι → ℤ) → ℂ) :
    Work.Diff.STE.seriesFun (fun k => -c k) = fun x => -Work.Diff.STE.seriesFun c x := by
  funext x
  simp only [Work.Diff.STE.seriesFun]
  rw [show (fun k : ι → ℤ => -c k * Work.Diff.STE.fourierExp k x)
      = fun k => -(c k * Work.Diff.STE.fourierExp k x) by funext k; ring]
  rw [tsum_neg]

/-- `lapPow k` commutes with negation. -/
theorem lapPow_neg (k : ℕ) (u : (ι → ℝ) → ℂ) :
    Work.Diff.STE.B3.SymCalcStep5.lapPow k (fun x => -u x)
      = fun x => -Work.Diff.STE.B3.SymCalcStep5.lapPow k u x := by
  rw [Work.Diff.STE.B3.SymCalcStep6.lapPow_eq_seriesFun,
    Work.Diff.STE.B3.SymCalcStep6.lapPow_eq_seriesFun]
  have hc : (fun m : ι → ℤ => (((Work.Diff.STE.B3.SymCalc.flatLam m) ^ k : ℝ) : ℂ)
        * Work.Diff.STE.fourierCoeff (fun x => -u x) m)
      = fun m => -((((Work.Diff.STE.B3.SymCalc.flatLam m) ^ k : ℝ) : ℂ)
        * Work.Diff.STE.fourierCoeff u m) := by
    funext m
    rw [Work.Diff.STE.B3.SymCalcStep6.fourierCoeff_neg]
    ring
  rw [hc, seriesFun_neg]

/-- `conjLapPow k T T'` commutes with negation. -/
theorem conjLapPow_neg (k : ℕ) (T T' : (ι → ℝ) → (ι → ℝ)) (u : (ι → ℝ) → ℂ) :
    Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' (fun x => -u x)
      = fun x => -Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' u x := by
  rw [show Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' (fun x => -u x)
      = Work.Diff.STE.B3.SymCalc.compMap T
          (Work.Diff.STE.B3.SymCalcStep5.lapPow k
            (Work.Diff.STE.B3.SymCalc.compMap T' (fun x => -u x))) from rfl]
  rw [show Work.Diff.STE.B3.SymCalc.compMap T' (fun x => -u x)
      = fun y => -Work.Diff.STE.B3.SymCalc.compMap T' u y from rfl]
  rw [lapPow_neg]
  rw [show Work.Diff.STE.B3.SymCalc.compMap T (fun y => -Work.Diff.STE.B3.SymCalcStep5.lapPow k
        (Work.Diff.STE.B3.SymCalc.compMap T' u) y)
      = fun x => -Work.Diff.STE.B3.SymCalc.compMap T
        (Work.Diff.STE.B3.SymCalcStep5.lapPow k (Work.Diff.STE.B3.SymCalc.compMap T' u)) x from rfl]
  rw [show Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' u
      = Work.Diff.STE.B3.SymCalc.compMap T
          (Work.Diff.STE.B3.SymCalcStep5.lapPow k (Work.Diff.STE.B3.SymCalc.compMap T' u))
      from rfl]

/-- Subtractivity of the transported cutoff `V = conjCut ρ ε T T'`. -/
theorem conjCut_sub (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ)
    (T T' : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    {u v : (ι → ℝ) → ℂ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hup : Work.Diff.STE.Periodic1 u)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvp : Work.Diff.STE.Periodic1 v) :
    Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' (u - v)
      = Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' u
        - Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' v := by
  have hw : ContDiff ℝ (⊤ : ℕ∞) (fun x => u x - v x) := hu.sub hv
  have hwp : Work.Diff.STE.Periodic1 (fun x => u x - v x) := by
    intro i x
    show u (x + Pi.single i 1) - v (x + Pi.single i 1) = u x - v x
    rw [hup i x, hvp i x]
  have hadd := Work.Diff.STE.B3.SymCalcStep7.conjCut_add ρ hρ T T' hT hT' hTper ε hw hwp hv hvp
  have hsum : (fun x => u x - v x) + v = u := by
    funext x
    show u x - v x + v x = u x
    ring
  rw [hsum] at hadd
  rw [hadd]
  abel

/-- Subtractivity of the Friedrichs cutoff `S = flatCut ρ ε`. -/
theorem flatCut_sub (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ)
    {u v : (ι → ℝ) → ℂ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hup : Work.Diff.STE.Periodic1 u)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvp : Work.Diff.STE.Periodic1 v) :
    Work.Diff.STE.B3.SymCalc.flatCut ρ ε (u - v)
      = Work.Diff.STE.B3.SymCalc.flatCut ρ ε u
        - Work.Diff.STE.B3.SymCalc.flatCut ρ ε v := by
  have hw : ContDiff ℝ (⊤ : ℕ∞) (fun x => u x - v x) := hu.sub hv
  have hwp : Work.Diff.STE.Periodic1 (fun x => u x - v x) := by
    intro i x
    show u (x + Pi.single i 1) - v (x + Pi.single i 1) = u x - v x
    rw [hup i x, hvp i x]
  have hadd := Work.Diff.STE.B3.SymCalcStep7.flatCut_add ρ hρ ε hw hwp hv hvp
  have hsum : (fun x => u x - v x) + v = u := by
    funext x
    show u x - v x + v x = u x
    ring
  rw [hsum] at hadd
  rw [hadd]
  abel

/-- Subtractivity of `lapPow k`. -/
theorem lapPow_sub (k : ℕ) {u v : (ι → ℝ) → ℂ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hup : Work.Diff.STE.Periodic1 u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvp : Work.Diff.STE.Periodic1 v) :
    Work.Diff.STE.B3.SymCalcStep5.lapPow k (u - v)
      = Work.Diff.STE.B3.SymCalcStep5.lapPow k u
        - Work.Diff.STE.B3.SymCalcStep5.lapPow k v := by
  have hw : ContDiff ℝ (⊤ : ℕ∞) (fun x => u x - v x) := hu.sub hv
  have hwp : Work.Diff.STE.Periodic1 (fun x => u x - v x) := by
    intro i x
    show u (x + Pi.single i 1) - v (x + Pi.single i 1) = u x - v x
    rw [hup i x, hvp i x]
  have hadd := Work.Diff.STE.B3.SymCalcStep6.lapPow_algebra.2 k (fun x => u x - v x) v hw hv hwp hvp
  have hsum : (fun x => u x - v x) + v = u := by
    funext x
    show u x - v x + v x = u x
    ring
  rw [hsum] at hadd
  rw [hadd]
  abel

/-- `CSq` is unchanged by negation. -/
theorem CSq_neg_eq (s : ℕ) (c : (ι → ℤ) → ℂ) :
    Work.Diff.STE.CSq s (fun m => -c m) = Work.Diff.STE.CSq s c := by
  simp only [Work.Diff.STE.CSq]
  exact tsum_congr fun m => by rw [norm_neg]

/-- `CSq` is monotone in the level. -/
theorem CSq_mono_level {s t : ℕ} (hst : s ≤ t) {c : (ι → ℤ) → ℂ}
    (h : Summable fun m => (Work.Diff.STE.wt m) ^ t * ‖c m‖ ^ 2) :
    Work.Diff.STE.CSq s c ≤ Work.Diff.STE.CSq t c := by
  have hterm : ∀ m : ι → ℤ, (Work.Diff.STE.wt m) ^ s * ‖c m‖ ^ 2
      ≤ (Work.Diff.STE.wt m) ^ t * ‖c m‖ ^ 2 := by
    intro m
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact pow_le_pow_right₀ (Work.Diff.STE.wt_one_le m) hst
  have hsumL : Summable fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ s * ‖c m‖ ^ 2 :=
    Summable.of_nonneg_of_le
      (fun m => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) _) (sq_nonneg _))
      hterm h
  simp only [Work.Diff.STE.CSq]
  exact Summable.tsum_le_tsum hterm hsumL h

/-- The `CSq s` of a pointwise sum is at most twice the sum of the `CSq s`. -/
theorem CSq_add_le (s : ℕ) {c d : (ι → ℤ) → ℂ}
    (hc : Summable fun m => (Work.Diff.STE.wt m) ^ s * ‖c m‖ ^ 2)
    (hd : Summable fun m => (Work.Diff.STE.wt m) ^ s * ‖d m‖ ^ 2) :
    Work.Diff.STE.CSq s (fun m => c m + d m)
      ≤ 2 * (Work.Diff.STE.CSq s c + Work.Diff.STE.CSq s d) := by
  have hterm : ∀ m : ι → ℤ, (Work.Diff.STE.wt m) ^ s * ‖c m + d m‖ ^ 2
      ≤ 2 * ((Work.Diff.STE.wt m) ^ s * ‖c m‖ ^ 2 + (Work.Diff.STE.wt m) ^ s * ‖d m‖ ^ 2) := by
    intro m
    have h2 : ‖c m + d m‖ ^ 2 ≤ 2 * (‖c m‖ ^ 2 + ‖d m‖ ^ 2) := by
      have h1 : ‖c m + d m‖ ≤ ‖c m‖ + ‖d m‖ := norm_add_le _ _
      have h3 : (‖c m‖ + ‖d m‖) ^ 2 ≤ 2 * (‖c m‖ ^ 2 + ‖d m‖ ^ 2) := by
        nlinarith [sq_nonneg (‖c m‖ - ‖d m‖)]
      exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h3
    have hw : (0 : ℝ) ≤ (Work.Diff.STE.wt m) ^ s := pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) _
    calc (Work.Diff.STE.wt m) ^ s * ‖c m + d m‖ ^ 2
        ≤ (Work.Diff.STE.wt m) ^ s * (2 * (‖c m‖ ^ 2 + ‖d m‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 hw
      _ = 2 * ((Work.Diff.STE.wt m) ^ s * ‖c m‖ ^ 2 + (Work.Diff.STE.wt m) ^ s * ‖d m‖ ^ 2) := by
          ring
  have hsumL : Summable fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ s * ‖c m + d m‖ ^ 2 :=
    Summable.of_nonneg_of_le
      (fun m => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) _) (sq_nonneg _))
      hterm ((hc.add hd).mul_left 2)
  simp only [Work.Diff.STE.CSq]
  refine (Summable.tsum_le_tsum hterm hsumL ((hc.add hd).mul_left 2)).trans (le_of_eq ?_)
  rw [tsum_mul_left, hc.tsum_add hd]

/-- The `CSq s` of a pointwise difference is at most the sum of the `CSq s`. -/
theorem CSq_sub_le (s : ℕ) {c d : (ι → ℤ) → ℂ}
    (hc : Summable fun m => (Work.Diff.STE.wt m) ^ s * ‖c m‖ ^ 2)
    (hd : Summable fun m => (Work.Diff.STE.wt m) ^ s * ‖d m‖ ^ 2) :
    Work.Diff.STE.CSq s (fun m => c m - d m)
      ≤ 2 * (Work.Diff.STE.CSq s c + Work.Diff.STE.CSq s d) := by
  have hterm : ∀ m : ι → ℤ, (Work.Diff.STE.wt m) ^ s * ‖c m - d m‖ ^ 2
      ≤ 2 * ((Work.Diff.STE.wt m) ^ s * ‖c m‖ ^ 2 + (Work.Diff.STE.wt m) ^ s * ‖d m‖ ^ 2) := by
    intro m
    have h2 : ‖c m - d m‖ ^ 2 ≤ 2 * (‖c m‖ ^ 2 + ‖d m‖ ^ 2) := by
      have h1 : ‖c m - d m‖ ≤ ‖c m‖ + ‖d m‖ := norm_sub_le _ _
      have h3 : (‖c m‖ + ‖d m‖) ^ 2 ≤ 2 * (‖c m‖ ^ 2 + ‖d m‖ ^ 2) := by
        nlinarith [sq_nonneg (‖c m‖ - ‖d m‖)]
      exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h3
    have hw : (0 : ℝ) ≤ (Work.Diff.STE.wt m) ^ s := pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) _
    calc (Work.Diff.STE.wt m) ^ s * ‖c m - d m‖ ^ 2
        ≤ (Work.Diff.STE.wt m) ^ s * (2 * (‖c m‖ ^ 2 + ‖d m‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 hw
      _ = 2 * ((Work.Diff.STE.wt m) ^ s * ‖c m‖ ^ 2 + (Work.Diff.STE.wt m) ^ s * ‖d m‖ ^ 2) := by
          ring
  have hsumL : Summable fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ s * ‖c m - d m‖ ^ 2 :=
    Summable.of_nonneg_of_le
      (fun m => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) _) (sq_nonneg _))
      hterm ((hc.add hd).mul_left 2)
  simp only [Work.Diff.STE.CSq]
  refine (Summable.tsum_le_tsum hterm hsumL ((hc.add hd).mul_left 2)).trans (le_of_eq ?_)
  rw [tsum_mul_left, hc.tsum_add hd]


/-! ## 6. The transposed pairing kernels `E_i` of the six pieces of `pairOp`

Each `E_i` is the result of moving the `i`-th piece of the six-term decomposition of `pairOp`
(`Work.Diff.STE.B3.SymCalcStep7.pairOp_eq_pieces`) across the `L2re` pairing: the identity
`L2re y (piece_i g) = L2re (E_i y) g` (proved in `pairOp_pairing_le_sharp.lean`) is obtained from
the adjointness of `compMap T`, `compMap T'`, `conjCut` and `conjLapPow` together with the
self-adjointness of `lapPow` and `flatCut` (sections 3 and 4 above). -/

/-- The adjoint `P†` of the transported Laplacian power `P = conjLapPow k T T'` (see
`L2re_conjLapPow_adj`). -/
noncomputable def Padj (k : ℕ) (T T' : (ι → ℝ) → (ι → ℝ)) (u : (ι → ℝ) → ℂ) :
    (ι → ℝ) → ℂ :=
  fun x => jacInvC T' (T x) * Work.Diff.STE.B3.SymCalcStep5.lapPow k
    (fun z => jacDetC T' z * u (T' z)) (T x)

/-- The `Ki·(Λ − [Λ,Ki])`-defect: `[Λ, M_{jacInvC T'}] γ = Λ (jacInvC T' · γ) − jacInvC T' · Λ γ`. -/
noncomputable def lapCommDef (k : ℕ) (T' : (ι → ℝ) → (ι → ℝ)) (γ : (ι → ℝ) → ℂ) :
    (ι → ℝ) → ℂ :=
  fun u => Work.Diff.STE.B3.SymCalcStep5.lapPow k (fun v => jacInvC T' v * γ v) u
    - jacInvC T' u * Work.Diff.STE.B3.SymCalcStep5.lapPow k γ u

/-- The excess of `P† = P + ΔP` over `P`. -/
noncomputable def conjPadjExcess (k : ℕ) (T T' : (ι → ℝ) → (ι → ℝ)) (z : (ι → ℝ) → ℂ) :
    (ι → ℝ) → ℂ :=
  fun x => Padj k T T' z x - Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' z x

/-- The first transposed kernel: the transpose of `M_{ab}(Λ V − V Λ)` applied to `w`. -/
noncomputable def EFA (k : ℕ) (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (T T' : (ι → ℝ) → (ι → ℝ))
    (w : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  fun x => jacDetC T' x * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
        (fun u => jacInvC T' u * Work.Diff.STE.B3.SymCalcStep5.lapPow k w u) x
    - Work.Diff.STE.B3.SymCalcStep5.lapPow k
        (fun u => jacDetC T' u * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
          (fun v => jacInvC T' v * w v) u) x

/-- The second transposed kernel: the transpose of `M_{ab}(P S − S P)` applied to `w`. -/
noncomputable def EFB (k : ℕ) (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (T T' : (ι → ℝ) → (ι → ℝ))
    (w : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  fun x => Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun u => Padj k T T' w u) x
    - Padj k T T' (fun u => Work.Diff.STE.B3.SymCalc.flatCut ρ ε w u) x

/-- The third transposed kernel: the transpose of `M_a [Λ, M_b] V` applied to `w` (with the
multiplier `b' = star b`). -/
noncomputable def EFC (k : ℕ) (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (T T' : (ι → ℝ) → (ι → ℝ))
    (b' w : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  fun x => jacDetC T' x * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
        (fun u => jacInvC T' u * (b' u * Work.Diff.STE.B3.SymCalcStep5.lapPow k w u
          - Work.Diff.STE.B3.SymCalcStep5.lapPow k (fun v => b' v * w v) u)) x

/-- The fourth transposed kernel: the transpose of `M_a [M_b, S] P` applied to `w` (with the
multiplier `b' = star b`). -/
noncomputable def EFD (k : ℕ) (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (T T' : (ι → ℝ) → (ι → ℝ))
    (b' w : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  Padj k T T' (fun u => Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun v => b' v * w v) u
    - b' u * Work.Diff.STE.B3.SymCalc.flatCut ρ ε w u)

/-- The fifth transposed kernel: the transpose of `M_c [P, M_d] S` applied to `w` (with the
multiplier `d' = star d`). -/
noncomputable def EFE (k : ℕ) (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (T T' : (ι → ℝ) → (ι → ℝ))
    (d' w : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  fun x => Work.Diff.STE.B3.SymCalc.flatCut ρ ε
        (fun u => d' u * Padj k T T' w u - Padj k T T' (fun v => d' v * w v) u) x

/-- The sixth transposed kernel: the transpose of `−M_c [V, M_d] Λ` applied to `w` (with the
multiplier `d' = star d`). -/
noncomputable def EFF (k : ℕ) (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (T T' : (ι → ℝ) → (ι → ℝ))
    (d' w : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  fun x => Work.Diff.STE.B3.SymCalcStep5.lapPow k
        (fun u => jacDetC T' u * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
            (fun z => jacInvC T' z * (d' z * w z)) u
          - d' u * (jacDetC T' u * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
            (fun z => jacInvC T' z * w z) u)) x

/-- `ContDiff` is preserved by `star` (complex conjugation). -/
theorem contDiff_star {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => star (f x)) :=
  Complex.conjCLE.contDiff.comp hf

/-- `Periodic1` is preserved by `star` (complex conjugation). -/
theorem periodic1_star {f : (ι → ℝ) → ℂ} (hf : Work.Diff.STE.Periodic1 f) :
    Work.Diff.STE.Periodic1 (fun x => star (f x)) := fun i x => by
  show star (f (x + Pi.single i 1)) = star (f x)
  rw [hf i x]

/-- `ContDiff` and `Periodic1` are preserved by multiplication with a scalar. -/
theorem periodic1_smul (r : ℂ) {f : (ι → ℝ) → ℂ} (hf : Work.Diff.STE.Periodic1 f) :
    Work.Diff.STE.Periodic1 (fun x => r * f x) := fun i x => by
  show r * f (x + Pi.single i 1) = r * f x
  rw [hf i x]


/-! ## 7. Unfolding lemmas for the auxiliary definitions -/

@[simp] theorem lapCommDef_apply (k : ℕ) (T' : (ι → ℝ) → (ι → ℝ)) (γ : (ι → ℝ) → ℂ)
    (u : ι → ℝ) :
    lapCommDef k T' γ u = Work.Diff.STE.B3.SymCalcStep5.lapPow k
        (fun v => jacInvC T' v * γ v) u - jacInvC T' u * Work.Diff.STE.B3.SymCalcStep5.lapPow k γ u :=
  rfl

@[simp] theorem Padj_apply (k : ℕ) (T T' : (ι → ℝ) → (ι → ℝ)) (u : (ι → ℝ) → ℂ)
    (x : ι → ℝ) :
    Padj k T T' u x = jacInvC T' (T x) * Work.Diff.STE.B3.SymCalcStep5.lapPow k
      (fun z => jacDetC T' z * u (T' z)) (T x) := rfl

@[simp] theorem conjPadjExcess_apply (k : ℕ) (T T' : (ι → ℝ) → (ι → ℝ)) (z : (ι → ℝ) → ℂ)
    (x : ι → ℝ) :
    conjPadjExcess k T T' z x = Padj k T T' z x
      - Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' z x := rfl

@[simp] theorem EFA_apply (k : ℕ) (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (T T' : (ι → ℝ) → (ι → ℝ))
    (w : (ι → ℝ) → ℂ) (x : ι → ℝ) :
    EFA k ρ ε T T' w x = jacDetC T' x * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
        (fun u => jacInvC T' u * Work.Diff.STE.B3.SymCalcStep5.lapPow k w u) x
      - Work.Diff.STE.B3.SymCalcStep5.lapPow k
        (fun u => jacDetC T' u * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
          (fun v => jacInvC T' v * w v) u) x := rfl

@[simp] theorem EFB_apply (k : ℕ) (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (T T' : (ι → ℝ) → (ι → ℝ))
    (w : (ι → ℝ) → ℂ) (x : ι → ℝ) :
    EFB k ρ ε T T' w x = Work.Diff.STE.B3.SymCalc.flatCut ρ ε
        (fun u => Padj k T T' w u) x
      - Padj k T T' (fun u => Work.Diff.STE.B3.SymCalc.flatCut ρ ε w u) x := rfl

@[simp] theorem EFC_apply (k : ℕ) (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (T T' : (ι → ℝ) → (ι → ℝ))
    (b' w : (ι → ℝ) → ℂ) (x : ι → ℝ) :
    EFC k ρ ε T T' b' w x = jacDetC T' x * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
        (fun u => jacInvC T' u * (b' u * Work.Diff.STE.B3.SymCalcStep5.lapPow k w u
          - Work.Diff.STE.B3.SymCalcStep5.lapPow k (fun v => b' v * w v) u)) x := rfl

@[simp] theorem EFD_apply (k : ℕ) (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (T T' : (ι → ℝ) → (ι → ℝ))
    (b' w : (ι → ℝ) → ℂ) (x : ι → ℝ) :
    EFD k ρ ε T T' b' w x = Padj k T T' (fun u => Work.Diff.STE.B3.SymCalc.flatCut ρ ε
        (fun v => b' v * w v) u - b' u * Work.Diff.STE.B3.SymCalc.flatCut ρ ε w u) x := rfl

@[simp] theorem EFE_apply (k : ℕ) (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (T T' : (ι → ℝ) → (ι → ℝ))
    (d' w : (ι → ℝ) → ℂ) (x : ι → ℝ) :
    EFE k ρ ε T T' d' w x = Work.Diff.STE.B3.SymCalc.flatCut ρ ε
        (fun u => d' u * Padj k T T' w u - Padj k T T' (fun v => d' v * w v) u) x := rfl

@[simp] theorem EFF_apply (k : ℕ) (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (T T' : (ι → ℝ) → (ι → ℝ))
    (d' w : (ι → ℝ) → ℂ) (x : ι → ℝ) :
    EFF k ρ ε T T' d' w x = Work.Diff.STE.B3.SymCalcStep5.lapPow k
        (fun u => jacDetC T' u * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
            (fun z => jacInvC T' z * (d' z * w z)) u
          - d' u * (jacDetC T' u * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
            (fun z => jacInvC T' z * w z) u)) x := rfl

/-- `compMap` is subtractive. -/
theorem compMap_sub (T : (ι → ℝ) → (ι → ℝ)) (u v : (ι → ℝ) → ℂ) :
    Work.Diff.STE.B3.SymCalc.compMap T (u - v)
      = Work.Diff.STE.B3.SymCalc.compMap T u - Work.Diff.STE.B3.SymCalc.compMap T v := by
  have h2 : Work.Diff.STE.B3.SymCalc.compMap T (-v)
      = -Work.Diff.STE.B3.SymCalc.compMap T v :=
    Work.Diff.STE.B3.SymCalcStep6.compMap_neg T v
  rw [show (u - v) = u + (-v) from rfl, Work.Diff.STE.B3.SymCalcStep6.compMap_add, h2,
    sub_eq_add_neg]


/-- `Padj k T T' u = compMap T (jacInvC T' · Λ^k (jacDetC T' · u ∘ T'))`. -/
theorem Padj_eq_compMap (k : ℕ) (T T' : (ι → ℝ) → (ι → ℝ)) (u : (ι → ℝ) → ℂ) :
    Padj k T T' u = Work.Diff.STE.B3.SymCalc.compMap T
      (fun y => jacInvC T' y * Work.Diff.STE.B3.SymCalcStep5.lapPow k
        (fun z => jacDetC T' z * u (T' z)) y) := rfl

/-- `Padj` preserves smoothness. -/
theorem Padj_contDiff (k : ℕ) {T T' : (ι → ℝ) → (ι → ℝ)} (hJac : JacFacts T')
    (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    {u : (ι → ℝ) → ℂ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hup : Work.Diff.STE.Periodic1 u) :
    ContDiff ℝ (⊤ : ℕ∞) (Padj k T T' u) := by
  have hinner : Work.Diff.STE.Periodic1 (fun z => jacDetC T' z * u (T' z)) := by
    intro i y
    show jacDetC T' (y + Pi.single i 1) * u (T' (y + Pi.single i 1))
      = jacDetC T' y * u (T' y)
    rw [Work.Diff.STE.B3.SymCalcStep1.shift_T' T T' hTper hTinv1 hTinv2 i y, hJac.2.1 i y]
    congr 1
    exact hup i (T' y)
  rw [Padj_eq_compMap]
  exact (hJac.2.2.2.1.mul ((Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).2.2.1 _
    (hJac.1.mul (hu.comp hT')) hinner)).comp hT

/-- `Padj` preserves `1`-periodicity. -/
theorem Padj_periodic (k : ℕ) {T T' : (ι → ℝ) → (ι → ℝ)} (hJac : JacFacts T')
    (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    {u : (ι → ℝ) → ℂ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hup : Work.Diff.STE.Periodic1 u) :
    Work.Diff.STE.Periodic1 (Padj k T T' u) := by
  have hinner : Work.Diff.STE.Periodic1 (fun z => jacDetC T' z * u (T' z)) := by
    intro i y
    show jacDetC T' (y + Pi.single i 1) * u (T' (y + Pi.single i 1))
      = jacDetC T' y * u (T' y)
    rw [Work.Diff.STE.B3.SymCalcStep1.shift_T' T T' hTper hTinv1 hTinv2 i y, hJac.2.1 i y]
    congr 1
    exact hup i (T' y)
  rw [Padj_eq_compMap]
  intro i x
  show (fun y : ι → ℝ => jacInvC T' y * Work.Diff.STE.B3.SymCalcStep5.lapPow k
      (fun z => jacDetC T' z * u (T' z)) y) (T (x + Pi.single i 1))
    = (fun y : ι → ℝ => jacInvC T' y * Work.Diff.STE.B3.SymCalcStep5.lapPow k
      (fun z => jacDetC T' z * u (T' z)) y) (T x)
  rw [hTper i x]
  exact (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hJac.2.2.2.2.1
    ((Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).2.2.2 _)) i (T x)

/-- Negation in the second argument of `L2re`. -/
theorem L2re_neg_snd (y g : (ι → ℝ) → ℂ) :
    Work.Diff.STE.L2re y (fun x => -g x) = -Work.Diff.STE.L2re y g := by
  simp only [Work.Diff.STE.L2re]
  rw [show (∫ x in Work.Diff.STE.unitCube, y x * star (-g x))
      = ∫ x in Work.Diff.STE.unitCube, -(y x * star (g x)) by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [star_neg]
    ring]
  rw [integral_neg]
  simp

/-- Negation in the first argument of `L2re`. -/
theorem L2re_neg_fst (y g : (ι → ℝ) → ℂ) :
    Work.Diff.STE.L2re (fun x => -y x) g = -Work.Diff.STE.L2re y g := by
  simp only [Work.Diff.STE.L2re]
  rw [show (∫ x in Work.Diff.STE.unitCube, (-y x) * star (g x))
      = ∫ x in Work.Diff.STE.unitCube, -(y x * star (g x)) by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring]
  rw [integral_neg]
  simp


end Work.Diff.STE.B3.SymCalcStep7
