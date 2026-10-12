import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBox.q3WindowDef
import Submission.Work.BoseFixB3.Arith.b3HAbsorbRoot_holds
import Submission.Work.BoseFixGlue.Sector.FibreBound
import Submission.Work.BoseKinLoc.Sector.word_translate
import Submission.Work.BoseKinLoc.Word.kinFormB_nonneg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixGlue.Sector.fibreSumBound_to_fibreInput`

**The case analysis of the fibre bound**: the sector-sum form `FibreSumBound` (the per-fibre
argument plus the norm bookkeeping) implies the box-form fibre bound `FibreInput`, at a possibly
smaller diluteness threshold `ε' ≤ ε`.

For an admissible `μ` (`Adm v ε' μ`) and a smooth symmetric state `Φ` supported in the centred box
`abox N L`, and every translation `u`:

* **translation** (`word_translate`, `wt_integral_shiftN`): the anchored form
  `boxForm N … u Φ` is `boxForm N … 0 Ψ` with `Ψ z = Φ (ℓ u + z)`, and `∫Ψ² = ∫Φ²`;
* **Case A** (`boxForm_fibreSumA_of_integrable`): if the potential integrand of `Ψ` (at the
  anchored translation `0`) is integrable, the anchored form *is* the fibre sum, so
  `FibreSumBound` (applied to `Ψ`, whose support lies in the translated box `(-ℓu) + abox N L`)
  gives the claim;
* **Case B**: otherwise Mathlib's Bochner integral gives the potential term the junk value `0`, so
  the anchored form collapses to the whole-space kinetic word, which is nonnegative in FS's
  parameter regime (`fsT_nonneg_of_continuous` through `kinForm_nonneg_of_sign`); with
  `min 0 EΛ ≤ 0` and `∫Ψ² ≥ 0` this dominates `min 0 EΛ · ∫Ψ²`.

The parameter regime of the kinetic word (`0 < d`, `0 < s`, `0 ≤ εT ≤ 1`, `0 ≤ b`, and `0 < ℓ`)
comes from `Adm` itself: `Adm` forces `0 < a v` (a *nonpositive* scattering length makes
`ParamsOK (fsParams t) t` unsatisfiable, `not_paramsOK_of_nonpos`), and then FS's parameters at
diluteness `μ(a v)³ ∈ (0, 1]` are the monomials `t^{c/323} ∈ (0, 1]`.

## Contents

* `contDiff_shiftN`, `tsupport_shift_subset`, `permInvariant_shift` — the translated state (copied
  from the skeleton `Sector/fibre_bound_v3`, which is not imported here);
* `kinForm_nonneg_of_sign` — Case B in the FS sign regime;
* `not_paramsOK_of_nonpos`, `a_pos_of_adm` — the scattering length of an admissible potential;
* `fibreSumBound_to_fibreInput` — the target.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixGlue.Sector

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The translated `N`-body state -/

/-- The `N`-particle translation `x ↦ (i ↦ ℓ•u + x i)` is smooth. -/
private lemma contDiff_shiftN {N : ℕ} (ℓ : ℝ) (u : ℝ³) :
    ContDiff ℝ (⊤ : ENat) fun z : Submission.BoseGases.X N => fun i : Fin N => ℓ • u + z i := by
  refine contDiff_pi.mpr fun i => ?_
  exact contDiff_const.add (contDiff_apply ℝ ℝ³ i)

/-- The support of the translated state lies in the translated box. -/
private lemma tsupport_shift_subset {N : ℕ} {ℓ L : ℝ} (u : ℝ³)
    {Φ : Submission.BoseGases.X N → ℝ}
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox N L) :
    tsupport (fun z : Submission.BoseGases.X N => Φ (fun i : Fin N => ℓ • u + z i))
      ⊆ (fun x : Submission.BoseGases.X N => fun i : Fin N => (-(ℓ • u)) + x i) ''
          Submission.BoseGases.abox N L := by
  have himage : (fun x : Submission.BoseGases.X N => fun i : Fin N => (-(ℓ • u)) + x i) ''
        Submission.BoseGases.abox N L
      = {z : Submission.BoseGases.X N |
          ∀ i : Fin N, z i + ℓ • u ∈ Submission.BoseGases.acube L} := by
    ext z
    rw [Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩ i
      show (fun i : Fin N => (-(ℓ • u)) + x i) i + ℓ • u ∈ Submission.BoseGases.acube L
      rw [show (-(ℓ • u)) + x i + ℓ • u = x i from by abel]
      exact hx i
    · intro h
      exact ⟨fun i => z i + ℓ • u, fun i => h i, by
        funext i; show (-(ℓ • u)) + (z i + ℓ • u) = z i; abel⟩
  have hclosed : IsClosed {z : Submission.BoseGases.X N |
      ∀ i : Fin N, z i + ℓ • u ∈ Submission.BoseGases.acube L} := by
    have hset : {z : Submission.BoseGases.X N |
        ∀ i : Fin N, z i + ℓ • u ∈ Submission.BoseGases.acube L}
        = ⋂ i : Fin N, (fun z : Submission.BoseGases.X N => z i + ℓ • u) ⁻¹'
            Submission.BoseGases.acube L := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
    rw [hset]
    exact isClosed_iInter fun i => (Submission.BoseGases.acube_isClosed L).preimage (by fun_prop)
  rw [himage]
  refine closure_minimal ?_ hclosed
  intro z hz i
  have h1 := hsupp (subset_tsupport Φ hz) i
  show z i + ℓ • u ∈ Submission.BoseGases.acube L
  rw [add_comm]
  exact h1

/-- The translated state of a permutation invariant state is permutation invariant. -/
private lemma permInvariant_shift {N : ℕ} (ℓ : ℝ) (u : ℝ³)
    {Φ : Submission.BoseGases.X N → ℝ} (hsym : Submission.BoseGases.PermInvariant N Φ) :
    Submission.BoseGases.PermInvariant N
      (fun z : Submission.BoseGases.X N => Φ (fun i : Fin N => ℓ • u + z i)) := by
  intro σ z
  exact hsym σ (fun i : Fin N => ℓ • u + z i)

/-! ## 2. Case B in the FS sign regime: the whole-space kinetic word is nonnegative -/

/-- **The whole-space kinetic word is nonnegative in the FS sign regime.**  If the kinetic
parameters satisfy `0 < d`, `0 < s`, `0 ≤ ε_T ≤ 1`, `0 ≤ b` (the sign part of FS
`eq:BSlidingassp`), then the one-body word `fsT` is pointwise nonnegative on *continuous* states
(`Word.fsT_nonneg_of_continuous`), hence each slot integrand of the whole-space kinetic word is
pointwise nonnegative and so is the word itself. -/
private theorem kinForm_nonneg_of_sign {N : ℕ} {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hs : 0 < s) (hεT : 0 ≤ εT) (hεT1 : εT ≤ 1) (hb : 0 ≤ b)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : Continuous Ψ) :
    0 ≤ Work.BoseKinLoc.kinForm N ℓ d s εT b 0 Ψ := by
  unfold Work.BoseKinLoc.kinForm Work.BoseKinLoc.slotForm
  refine Finset.sum_nonneg fun i _ => ?_
  refine mul_nonneg (zpow_nonneg hℓ.le _) (integral_nonneg fun x => ?_)
  exact mul_nonneg (Work.BoseKinLoc.Word.kinFormB_indU_nonneg ℓ 0 (x i))
    (Work.BoseKinLoc.Word.fsT_nonneg_of_continuous hℓ hd hs hεT hεT1 hb 0
      (Work.BoseKinLoc.Word.kinFormB_fibre_continuous i x hΨ))

/-! ## 3. `Adm` is empty for a nonpositive scattering length -/

/-- FS's parameter conditions are unsatisfiable at every nonpositive diluteness `t`: at `t = 0`
FS's `con:sKell` fails (both `s` and `K_ℓ` vanish), and for `t < 0` FS's `con:KellKLd` fails
(Mathlib's real power at a negative base is `exp (log t · y)·cos (πy)`, so `t^{1/2} = 0` while
`d^{2M-2} > 0`). -/
private lemma not_paramsOK_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    ¬ ParamsOK (fsParams t) t := by
  rcases lt_or_eq_of_le ht with h | h
  · exact Work.BoseFixB3.Arith.not_paramsOK_of_neg h
  · subst h
    exact not_paramsOK_fsParams_zero

/-- **The scattering length of an admissible potential is positive.**  If `Adm v ε μ` holds then
`t = μ (a v)³ ≥ 0`, and `t = 0` is already excluded by `ParamsOK`; since `μ > 0`, this forces
`a v > 0`. -/
private lemma a_pos_of_adm {v : ℝ³ → ℝ} {ε μ : ℝ} (h : Adm v ε μ) : 0 < a v := by
  by_contra hcon
  have hcon : a v ≤ 0 := le_of_not_gt hcon
  have ha3 : (a v) ^ 3 ≤ 0 := by
    have h1 : 0 ≤ (a v) * (a v) := mul_nonneg_of_nonpos_of_nonpos hcon hcon
    calc (a v) ^ 3 = ((a v) * (a v)) * (a v) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 hcon
  exact not_paramsOK_of_nonpos (mul_nonpos_of_nonneg_of_nonpos h.1.le ha3) h.2.2

/-! ## 4. The target -/

theorem fibreSumBound_to_fibreInput {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {ε : ℝ} (hε : 0 < ε) (hA : Work.BoseFixGlue.FibreSumBound v h ε) :
    ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ Work.BoseFixGlue.FibreInput v h ε' := by
  classical
  refine ⟨min ε 1, lt_min hε one_pos, min_le_left ε 1, ?_⟩
  intro μ hAdm N L _hℓL Φ hΦ hsym hsupp u
  have hμ : 0 < μ := hAdm.1
  have hav : 0 < a v := a_pos_of_adm hAdm
  have hAdmε : Adm v ε μ := ⟨hμ, le_trans hAdm.2.1 (min_le_left ε 1), hAdm.2.2⟩
  -- FS's parameters at the diluteness `t = μ (a v)³ ∈ (0, 1]`
  have ht : 0 < μ * (a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
  have ht1 : μ * (a v) ^ 3 ≤ 1 := le_trans hAdm.2.1 (min_le_right ε 1)
  have hℓ : 0 < ℓB v μ := sideB_pos hμ hav
  have hd : 0 < dB v μ := by
    rw [dB_def]
    simp only [paramsAt, fsParams]
    exact fsXp_pos ht
  have hs : 0 < sB v μ := by
    rw [sB_def]
    simp only [paramsAt, fsParams]
    exact fsXp_pos ht
  have hεT0 : 0 ≤ eTB v μ := by
    rw [eTB_def]
    simp only [paramsAt, fsParams]
    exact (fsXp_pos ht).le
  have hεT1 : eTB v μ ≤ 1 := by
    rw [eTB_def]
    simp only [paramsAt, fsParams]
    exact fsXp_le_one ht ht1 (by norm_num)
  have hb : 0 ≤ bB v μ := by
    rw [bB_eq_bValue]
    norm_num [bValue]
  -- the translated state `Ψ z = Φ (ℓ u + z)`, supported in the translated box `(-ℓu) + abox N L`
  have hΨcd : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : X N => Φ (fun i : Fin N => ℓB v μ • u + z i)) :=
    hΦ.comp (contDiff_shiftN (ℓB v μ) u)
  have hΨsym : PermInvariant N (fun z : X N => Φ (fun i : Fin N => ℓB v μ • u + z i)) :=
    permInvariant_shift (ℓB v μ) u hsym
  have hΨsupp : tsupport (fun z : X N => Φ (fun i : Fin N => ℓB v μ • u + z i)) ⊆
      (fun x : X N => fun i : Fin N => (-(ℓB v μ • u)) + x i) '' abox N L :=
    tsupport_shift_subset u hsupp
  have hB : boxForm N v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ) u Φ
      = boxForm N v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ) 0
          (fun z : X N => Φ (fun i : Fin N => ℓB v μ • u + z i)) :=
    Work.BoseKinLoc.Sector.word_translate v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ)
      (bB v μ) u hℓ Φ
  have hI : (∫ x : X N, (Φ x) ^ 2)
      = ∫ z : X N, (Φ (fun i : Fin N => ℓB v μ • u + z i)) ^ 2 :=
    (Work.BoseKinLoc.Sector.wt_integral_shiftN (ℓB v μ) u
      (fun x : X N => (Φ x) ^ 2)).symm
  rw [hB, hI]
  -- Case split on the integrability of the potential integrand of `Ψ`
  by_cases hInt : MeasureTheory.Integrable (fun x : X N =>
      (Φ (fun i : Fin N => ℓB v μ • u + x i)) ^ 2
        * potWordU N v (g0 v h) (ℓB v μ) μ 0 x)
  · -- ## Case A: the anchored form is the fibre sum
    rw [Work.BoseKinLoc.Sector.boxForm_fibreSumA_of_integrable (ℓ := ℓB v μ) (L := L)
      (c := -(ℓB v μ • u)) hℓ hΨcd hΨsupp hInt]
    exact hA μ hAdmε N L (-(ℓB v μ • u)) _ hΨcd hΨsym hΨsupp
  · -- ## Case B: the potential term is Mathlib's junk value `0`, and the kinetic word is `≥ 0`
    rw [Work.BoseKinLoc.boxForm,
      show (∫ x : X N, (Φ (fun i : Fin N => ℓB v μ • u + x i)) ^ 2
          * potWordU N v (g0 v h) (ℓB v μ) μ 0 x)
        = 0 from MeasureTheory.integral_undef hInt, add_zero]
    have hkin : 0 ≤ kinForm N (ℓB v μ) (dB v μ) (sB v μ) (eTB v μ) (bB v μ) 0
        (fun z : X N => Φ (fun i : Fin N => ℓB v μ • u + z i)) :=
      kinForm_nonneg_of_sign hℓ hd hs hεT0 hεT1 hb hΨcd.continuous
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg (min_le_left 0 _)
      (integral_nonneg fun z => sq_nonneg _)) hkin

end Work.BoseFixGlue.Sector
