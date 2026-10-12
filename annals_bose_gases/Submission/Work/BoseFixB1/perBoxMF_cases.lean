import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.perBoxFWeight_holds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The thin-box predicate, and the case-split shape -/

/-- **The degenerate ("thin") boxes.**  No pair of points at which the localised cutoff
`χ_{B(u)}` is nonzero lies within the support of `g₀ = v(1−w₀)`.  This is the geometric form of
"the cutoff support of the box is thinner than `supp g₀`" — the configuration family for which
the per-`u` mass lower bound `∬w_{1,B(u)} ≥ c(a v)χMass` is FALSE (see
`FINDING_perBoxF_ledger.md` §1a, `FINDING_w1MassB_ge_const_mul_chiMass.md`): on such a box the
localised one-body *and* two-body kernels vanish identically and `PerBoxMF` is trivial
(`perBoxMF_of_thin_support`). -/
def IsThinBox (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∀ x y : EuclideanSpace ℝ (Fin 3),
    Submission.BoseGases.chiSmallB (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u x ≠ 0 →
    Submission.BoseGases.chiSmallB (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u y ≠ 0 →
    Submission.BoseGases.g0 v h (x - y) = 0

/-- **`PerBoxMF` with a case hypothesis on `(μ, u)`.**  This is `PerBoxMF`'s inequality verbatim,
with the extra hypothesis `P μ u` on the admissible point and the box.  The two instances below
(`PerBoxMF_thin`, `PerBoxMF_thick`) are the case split of `PerBoxMF` on `IsThinBox`. -/
def PerBoxMFCase (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ)
    (P : ℝ → EuclideanSpace ℝ (Fin 3) → Prop) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        P μ u →
        (1 / 4) * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u *
            (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
              ((nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
                  chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) - μ) ^ 2))
          - (1 / 2) * μ ^ 2 * w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
          - C * perBoxErr v μ R n Φ u
        ≤ sbWord h μ u (Φ : X n → ℝ)

/-- The **thin** (degenerate) case of `PerBoxMF`. -/
abbrev PerBoxMF_thin (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) :
    Prop :=
  PerBoxMFCase v h R (fun μ u => IsThinBox v h μ u)

/-- The **thick** case of `PerBoxMF`: what remains after the degenerate boxes are peeled off.
Every `(μ, u)` on the good set carries a pair `x, y` with `χ_{B(u)}(x) ≠ 0`, `χ_{B(u)}(y) ≠ 0`
and `g₀(x−y) ≠ 0`. -/
abbrev PerBoxMF_thick (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) :
    Prop :=
  PerBoxMFCase v h R (fun μ u => ¬ IsThinBox v h μ u)

/-- **The fibre of the localised one-body kernel** at a point `x`:
`∫_{acube ℓ} w_{1,B(u)}(x,y) dy`.  This is exactly the integrand of the chemical-potential term
of `qLHSword` (`Submission.BoseGases.w1Fibre ℓ (wSmall1Pair h M ℓ d u)`), and its `x`-integral is
`w1MassB h M ℓ d u`. -/
noncomputable def fibB {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ)
    (ℓ d : ℝ) (u x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∫ y in Submission.BoseGases.acube ℓ, Submission.BoseGases.wSmall1Pair h M ℓ d u x y

/-- **The boxes on which the localised one-body kernel has vanishing fibre.**  This is the
hypothesis of the proved `Work.BoseFixB1.perBoxMF_of_fibre_zero` (where the whole inequality holds
*without* the error bracket: `W = 0` kills the `F`-term and the background, and
`sbWord = sbKin + ∫Φ²(−μ·fibre + pair) ≥ 0`).  It is *strictly weaker* than `IsThinBox`: on a
thin box every fibre vanishes (`isZeroFibreBox_of_thin`), but a fibre can vanish while some pair
still has `g₀ ≠ 0` (a measure-theoretic degeneracy).  Hence peeling the zero-fibre boxes peels
strictly more than peeling the thin ones, and — since the zero-fibre case is *already proved*
(`perBoxMF_zeroFibre_holds`) — it is the sharpest available reduction of `PerBoxMF`. -/
def IsZeroFibreBox (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin 3),
    fibB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x = 0

/-- The **zero-fibre** case of `PerBoxMF` (proved, with `C = 0`). -/
abbrev PerBoxMF_zeroFibre (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (R : ℝ) : Prop :=
  PerBoxMFCase v h R (fun μ u => IsZeroFibreBox v h μ u)

/-- The **positive-fibre** case of `PerBoxMF`: what remains after the zero-fibre boxes are peeled
off.  Every `(μ,u)` on the good set carries a point `x` with `∫_{acube ℓ}w_{1,B(u)}(x,y)dy ≠ 0`
(and hence, since the fibre is a.e. nonnegative, a point with strictly positive fibre). -/
abbrev PerBoxMF_posFibre (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) :
    Prop :=
  PerBoxMFCase v h R (fun μ u => ¬ IsZeroFibreBox v h μ u)

/-! ## 2. Elementary facts about the localised kernels

`perBoxMFCase_*`-prefixed so that no name collides with the (frequently rewritten)
`perBoxFWeight_holds.lean`. -/

/-- The cosine-`M` self-convolution is nonnegative. -/
theorem perBoxMFCase_conv3Small_nonneg (M : ℕ) (x : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Submission.BoseGases.conv3Small M x := by
  rw [Submission.BoseGases.conv3Small]
  exact integral_nonneg fun y => mul_nonneg (Submission.BoseGases.chiSmall_nonneg M y)
    (Submission.BoseGases.chiSmall_nonneg M _)

/-- The scaled self-convolution of the small bump is nonnegative. -/
theorem perBoxMFCase_convScaleSmall_nonneg (M : ℕ) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Submission.BoseGases.convScaleSmall M c x := by
  rw [Submission.BoseGases.convScaleSmall]
  exact perBoxMFCase_conv3Small_nonneg M _

/-- The localised cutoff factor is nonnegative. -/
theorem perBoxMFCase_chiSmallB_nonneg (M : ℕ) (ℓ d : ℝ) (u x : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Submission.BoseGases.chiSmallB M ℓ d u x := by
  rw [Submission.BoseGases.chiSmallB]
  exact mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ x)
    (Submission.BoseGases.chiSmall_nonneg M _)

/-- **The localised two-body kernel is nonnegative for a nonnegative numerator.** -/
theorem perBoxMFCase_wSmallPair_nonneg {M : ℕ} {ℓ d : ℝ} {u x y : EuclideanSpace ℝ (Fin 3)}
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : 0 ≤ f) :
    0 ≤ Submission.BoseGases.wSmallPair M ℓ d u f x y := by
  rw [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled]
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · exact perBoxMFCase_chiSmallB_nonneg M ℓ d u x
  · exact div_nonneg (div_nonneg (hf _) (perBoxMFCase_convScaleSmall_nonneg M (ℓ * d) _))
      (Submission.BoseGases.convScale_nonneg ℓ _)
  · exact perBoxMFCase_chiSmallB_nonneg M ℓ d u y

/-- The count `nCountB` is nonnegative. -/
theorem perBoxMFCase_nCountB_nonneg {M : ℕ} {ℓ d : ℝ} {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ}
    (x : X n) : 0 ≤ nCountB M ℓ d u x := by
  simp only [nCountB]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The cutoff mass `chiMass` is nonnegative. -/
theorem perBoxMFCase_chiMass_nonneg (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ chiMass M ℓ d u := by
  simp only [chiMass]
  exact integral_nonneg fun x => sq_nonneg _

/-- **The error bracket `perBoxErr` is nonnegative** at every admissible point (`0 < μ`,
`0 < a v`, `0 < K_B`, and the two masses `chiMass`, `‖Φ‖²` are nonnegative). -/
theorem perBoxErr_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε₀ μ R : ℝ} {n : ℕ}
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ perBoxErr v μ R n Φ u := by
  have hμ : 0 ≤ μ := le_of_lt (adm_mu_pos hAdm)
  have ha : 0 ≤ a v := le_of_lt (adm_a_pos hAdm)
  have hKB : 0 ≤ (paramsAt μ (a v)).KB := le_of_lt (paramsAt_KB_pos hAdm)
  have hchi : 0 ≤ chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u :=
    perBoxMFCase_chiMass_nonneg _ _ _ _
  have hnb : 0 ≤ normB v μ n (Φ : X n → ℝ) := by
    rw [normB, Work.BoseKinLoc.sqNormB]
    exact integral_nonneg fun x => sq_nonneg _
  have hS : 0 ≤ (R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
      + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) :=
    add_nonneg (sq_nonneg _)
      (mul_nonneg (pow_nonneg hKB 3)
        (Real.rpow_nonneg (mul_nonneg hμ (pow_nonneg ha 3)) _))
  have hprod : 0 ≤ μ ^ 2 * (a v)
      * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
        + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
      * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
      * normB v μ n (Φ : X n → ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) ha) hS) hchi) hnb
  have hlin : 0 ≤ μ * (a v) * normB v μ n (Φ : X n → ℝ) := mul_nonneg (mul_nonneg hμ ha) hnb
  rw [perBoxErr]
  linarith [hprod, hlin]

/-! ## 2b. The count-variable form of the crux's `F`-term

`PerBoxMF`'s left side is `¼·W·∫Φ²(t−μ)²` with `t = nCountB/chiMass` the *smooth density* — a
degree-`0`-in-`Φ` function of the configuration.  The corpus's count machinery
(`Work.BoseFixB1.WB.peel_aP_g`, `WB.pq_split_meas`, the `P/Q` split) acts instead on the two
*count moments* `S₂ = ∫Φ²·(nCountB)²` and `S₁ = ∫Φ²·nCountB`.  The following exact identity is the
bridge; it is what makes `PerBoxMF` a statement about `(S₂, S₁, ‖Φ‖², χ, W, Wp)` and hence
amenable to that machinery (and it is also the reason the *degree-4* `A₀`-main square
`(cS1/ℓ³ − μ)²` is the *wrong* object at the state level: `t` is degree `0`, while `cS1` is
degree `2` in `Φ`; see `FINDING_perBoxMF_cases.md` §2b). -/

/-- **The crux's `F`-term in the count variables** (exact identity):
`∫Φ²(t−μ)² = χ⁻²·S₂ − 2μχ⁻¹·S₁ + μ²·‖Φ‖²`, where `t = nCountB/chiMass`, `S₂`, `S₁` are the
`nCountB`-moments and `χ = chiMass M ℓ d u`. -/
theorem integral_sq_sub_mu_eq_countForm {M : ℕ} {ℓ d μ : ℝ} {n : ℕ}
    {u : EuclideanSpace ℝ (Fin 3)} {Φ : X n → ℝ}
    (hI2 : IntegrableOn (fun x : X n => (Φ x) ^ 2 * (nCountB M ℓ d u x) ^ 2)
      (abox n ℓ) volume)
    (hI1 : IntegrableOn (fun x : X n => (Φ x) ^ 2 * nCountB M ℓ d u x) (abox n ℓ) volume)
    (hI0 : IntegrableOn (fun x : X n => (Φ x) ^ 2) (abox n ℓ) volume) :
    (∫ x in abox n ℓ, (Φ x) ^ 2 *
        ((nCountB M ℓ d u x / chiMass M ℓ d u) - μ) ^ 2)
      = ((chiMass M ℓ d u)⁻¹) ^ 2
          * (∫ x in abox n ℓ, (Φ x) ^ 2 * (nCountB M ℓ d u x) ^ 2)
        - 2 * μ * (chiMass M ℓ d u)⁻¹
            * (∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
        + μ ^ 2 * (∫ x in abox n ℓ, (Φ x) ^ 2) := by
  set χ : ℝ := chiMass M ℓ d u with hχ
  have hJ2 : IntegrableOn (fun x : X n => (χ⁻¹) ^ 2 * ((Φ x) ^ 2 * (nCountB M ℓ d u x) ^ 2))
      (abox n ℓ) volume := hI2.const_mul _
  have hJ1 : IntegrableOn (fun x : X n => (2 * μ * χ⁻¹) * ((Φ x) ^ 2 * nCountB M ℓ d u x))
      (abox n ℓ) volume := hI1.const_mul _
  have hJ0 : IntegrableOn (fun x : X n => μ ^ 2 * (Φ x) ^ 2) (abox n ℓ) volume := hI0.const_mul _
  have hJsub : IntegrableOn (fun x : X n =>
      (χ⁻¹) ^ 2 * ((Φ x) ^ 2 * (nCountB M ℓ d u x) ^ 2)
        - (2 * μ * χ⁻¹) * ((Φ x) ^ 2 * nCountB M ℓ d u x)) (abox n ℓ) volume :=
    hJ2.sub hJ1
  rw [show (fun x : X n => (Φ x) ^ 2 *
        ((nCountB M ℓ d u x / χ) - μ) ^ 2)
      = fun x : X n => ((χ⁻¹) ^ 2 * ((Φ x) ^ 2 * (nCountB M ℓ d u x) ^ 2)
          - (2 * μ * χ⁻¹) * ((Φ x) ^ 2 * nCountB M ℓ d u x))
          + μ ^ 2 * (Φ x) ^ 2 from funext fun x => by
        rw [div_eq_mul_inv]; ring]
  rw [integral_add hJsub hJ0, integral_sub hJ2 hJ1, integral_const_mul, integral_const_mul,
    integral_const_mul]

/-! ## 3. The thin case -/

/-- **The thin case of `PerBoxMF` holds**, with `ε₀ = 1` and `C = 0` (the inequality holds
*without* the error bracket).  This is `perBoxMF_of_thin_support` (`hthin` gives it verbatim)
plus the elementary nonnegativity of the localised two-body kernel and of `sbKin`. -/
theorem perBoxMF_thin_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hv : 0 ≤ v) : PerBoxMF_thin v h R := by
  refine ⟨1, 0, one_pos, le_refl 0, fun μ hAdm n Φ u _hu hthin => ?_⟩
  have hμ : 0 < μ := adm_mu_pos hAdm
  have hM1 : 1 ≤ (paramsAt μ (a v)).M := by
    rw [M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hℓ0 : 0 < sideAt μ (a v) := adm_ell_pos hAdm
  have hpair_nn : ∀ x y : EuclideanSpace ℝ (Fin 3),
      0 ≤ Submission.BoseGases.wSmallPair (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u v x y := fun x y =>
    perBoxMFCase_wSmallPair_nonneg (M := (paramsAt μ (a v)).M) (ℓ := sideAt μ (a v))
      (d := (paramsAt μ (a v)).d) (u := u) (x := x) (y := y) hv
  have hkin : 0 ≤ sbKin (v := v) μ (paramsAt μ (a v)).M u Φ := by
    rw [sbKin]
    exact Work.UBBInputs9.A.tBwordBInd_nonneg hℓ0 (adm_eT_bounds hAdm).1 u (Φ : X n → ℝ)
  have key := perBoxMF_of_thin_support h hμ u (Φ : X n → ℝ) hM1 hℓ0 hthin hpair_nn hkin
  simpa using key

/-! ## 3b. The finer peel: zero-fibre boxes -/

/-- **A thin box has vanishing fibre everywhere.**  If no pair with `χ_B ≠ 0` on both points has
`g₀ ≠ 0`, then the fibre integrand `χ_B(x)χ_B(y)g₀(x−y)/(…)` vanishes identically (for `χ_B(x)=0`
trivially, for `χ_B(x)≠0` by thinness of the `y`-factor), hence the fibre is `0` at every `x`. -/
theorem isZeroFibreBox_of_thin {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ : ℝ} {u : EuclideanSpace ℝ (Fin 3)} (hthin : IsThinBox v h μ u) :
    IsZeroFibreBox v h μ u := by
  intro x
  rw [fibB, show (fun y : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.wSmall1Pair h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u x y) = fun _ => (0 : ℝ) from ?_]
  · simp
  funext y
  by_cases hx : Submission.BoseGases.chiSmallB (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u x = 0
  · simp [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair, hx]
  by_cases hy : Submission.BoseGases.chiSmallB (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u y = 0
  · simp [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair, hy]
  · have hsc : Submission.BoseGases.wSmallScaled (paramsAt μ (a v)).M
        (sideAt μ (a v) * (paramsAt μ (a v)).d)
        (Submission.BoseGases.g0 v h) (x - y) = 0 := by
      rw [Submission.BoseGases.wSmallScaled, hthin x y hx hy, zero_div]
    simp [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair, hsc]

/-- **The zero-fibre case of `PerBoxMF` holds**, with `ε₀ = 1` and `C = 0` — the same shape as
the thin case, but from the (weaker) hypothesis that the localised fibre vanishes.  This is
`Work.BoseFixB1.perBoxMF_of_fibre_zero` plus the nonnegativity of the localised two-body kernel
and of `sbKin`. -/
theorem perBoxMF_zeroFibre_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hv : 0 ≤ v) : PerBoxMF_zeroFibre v h R := by
  refine ⟨1, 0, one_pos, le_refl 0, fun μ hAdm n Φ u _hu hfib => ?_⟩
  have hμ : 0 < μ := adm_mu_pos hAdm
  have hM1 : 1 ≤ (paramsAt μ (a v)).M := by
    rw [M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hℓ0 : 0 < sideAt μ (a v) := adm_ell_pos hAdm
  have hpair_nn : ∀ x y : EuclideanSpace ℝ (Fin 3),
      0 ≤ Submission.BoseGases.wSmallPair (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u v x y := fun x y =>
    perBoxMFCase_wSmallPair_nonneg (M := (paramsAt μ (a v)).M) (ℓ := sideAt μ (a v))
      (d := (paramsAt μ (a v)).d) (u := u) (x := x) (y := y) hv
  have hkin : 0 ≤ sbKin (v := v) μ (paramsAt μ (a v)).M u Φ := by
    rw [sbKin]
    exact Work.UBBInputs9.A.tBwordBInd_nonneg hℓ0 (adm_eT_bounds hAdm).1 u (Φ : X n → ℝ)
  have hdeg : ∀ x : EuclideanSpace ℝ (Fin 3),
      (∫ y in Submission.BoseGases.acube (sideAt μ (a v)),
        Submission.BoseGases.wSmall1Pair h (paramsAt μ (a v)).M (sideAt μ (a v))
          (paramsAt μ (a v)).d u x y) = 0 := fun x => hfib x
  have key := perBoxMF_of_fibre_zero h hμ u (Φ : X n → ℝ) hM1 hℓ0 hdeg hpair_nn hkin
  simpa using key

/-! ## 4. The case split: `PerBoxMF` from its thin and thick cases -/

/-- **`PerBoxMF` follows from its thin and thick cases.**  The thresholds are combined by
`min`/`max` and `Adm.mono`; the two error brackets by monotonicity of `C ↦ C·perBoxErr`
(`perBoxErr_nonneg`). -/
theorem perBoxMF_of_thin_thick {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hthin : PerBoxMF_thin v h R) (hthick : PerBoxMF_thick v h R) :
    PerBoxMF v h R := by
  obtain ⟨ε₁, C₁, hε₁, hC₁, H₁⟩ := hthin
  obtain ⟨ε₂, C₂, hε₂, hC₂, H₂⟩ := hthick
  refine ⟨min ε₁ ε₂, max C₁ C₂, lt_min hε₁ hε₂, le_max_of_le_left hC₁,
    fun μ hAdm n Φ u hu => ?_⟩
  have h₁ : Work.BoseBoxFix.Adm v ε₁ μ := Adm.mono (ε₀' := min ε₁ ε₂) (ε₀ := ε₁) hAdm
    (min_le_left _ _)
  have h₂ : Work.BoseBoxFix.Adm v ε₂ μ := Adm.mono (ε₀' := min ε₁ ε₂) (ε₀ := ε₂) hAdm
    (min_le_right _ _)
  have herr : 0 ≤ perBoxErr v μ R n Φ u := perBoxErr_nonneg h₁ Φ u
  by_cases hthinμ : IsThinBox v h μ u
  · have key := H₁ μ h₁ n Φ u hu hthinμ
    have hC : C₁ * perBoxErr v μ R n Φ u ≤ max C₁ C₂ * perBoxErr v μ R n Φ u :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) herr
    linarith
  · have key := H₂ μ h₂ n Φ u hu hthinμ
    have hC : C₂ * perBoxErr v μ R n Φ u ≤ max C₁ C₂ * perBoxErr v μ R n Φ u :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) herr
    linarith

/-- **`PerBoxMF` follows from `PerBoxMF_thick`** — the mean-field ("fat box") case.  The thin
case is automatic (`perBoxMF_thin_holds`), so this is the exact residual obligation of the
a-priori chapter. -/
theorem perBoxMF_of_thick {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hv : 0 ≤ v) (hthick : PerBoxMF_thick v h R) : PerBoxMF v h R :=
  perBoxMF_of_thin_thick (perBoxMF_thin_holds hv) hthick

/-- **`PerBoxMF` follows from its zero-fibre and positive-fibre cases.**  Same assembly as
`perBoxMF_of_thin_thick`, with `IsZeroFibreBox` in place of `IsThinBox`. -/
theorem perBoxMF_of_zeroFibre_posFibre {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {R : ℝ} (hzero : PerBoxMF_zeroFibre v h R)
    (hpos : PerBoxMF_posFibre v h R) : PerBoxMF v h R := by
  obtain ⟨ε₁, C₁, hε₁, hC₁, H₁⟩ := hzero
  obtain ⟨ε₂, C₂, hε₂, hC₂, H₂⟩ := hpos
  refine ⟨min ε₁ ε₂, max C₁ C₂, lt_min hε₁ hε₂, le_max_of_le_left hC₁,
    fun μ hAdm n Φ u hu => ?_⟩
  have h₁ : Work.BoseBoxFix.Adm v ε₁ μ := Adm.mono (ε₀' := min ε₁ ε₂) (ε₀ := ε₁) hAdm
    (min_le_left _ _)
  have h₂ : Work.BoseBoxFix.Adm v ε₂ μ := Adm.mono (ε₀' := min ε₁ ε₂) (ε₀ := ε₂) hAdm
    (min_le_right _ _)
  have herr : 0 ≤ perBoxErr v μ R n Φ u := perBoxErr_nonneg h₁ Φ u
  by_cases hz : IsZeroFibreBox v h μ u
  · have key := H₁ μ h₁ n Φ u hu hz
    have hC : C₁ * perBoxErr v μ R n Φ u ≤ max C₁ C₂ * perBoxErr v μ R n Φ u :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) herr
    linarith
  · have key := H₂ μ h₂ n Φ u hu hz
    have hC : C₂ * perBoxErr v μ R n Φ u ≤ max C₁ C₂ * perBoxErr v μ R n Φ u :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) herr
    linarith

/-- **`PerBoxMF` follows from `PerBoxMF_posFibre`** — the *sharpest available* residual: the
zero-fibre boxes are discharged by `perBoxMF_zeroFibre_holds`, which covers strictly more than the
thin case (`isZeroFibreBox_of_thin`). -/
theorem perBoxMF_of_posFibre {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hv : 0 ≤ v) (hpos : PerBoxMF_posFibre v h R) : PerBoxMF v h R :=
  perBoxMF_of_zeroFibre_posFibre (perBoxMF_zeroFibre_holds hv) hpos

/-- **The `Thick` residual covers the `PosFibre` one**: `¬IsZeroFibreBox ⟹ ¬IsThinBox`
(contrapositive of `isZeroFibreBox_of_thin`), so a proof of the thick case is a proof of the
positive-fibre case.  Hence `PerBoxMF_thick` remains a sufficient (if not the sharpest) residual,
and a prover of `PerBoxMF_thick` may use `perBoxMF_zeroFibre_holds` as a case lemma. -/
theorem perBoxMF_posFibre_of_thick {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hthick : PerBoxMF_thick v h R) : PerBoxMF_posFibre v h R := by
  obtain ⟨ε, C, hε, hC, H⟩ := hthick
  exact ⟨ε, C, hε, hC, fun μ hAdm n Φ u hu hnz =>
    H μ hAdm n Φ u hu (fun hthin => hnz (isZeroFibreBox_of_thin hthin))⟩

end Work.BoseFixB1
