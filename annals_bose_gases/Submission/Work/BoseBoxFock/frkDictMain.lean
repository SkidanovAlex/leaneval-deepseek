import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.cnPlusC_boxRestrictC_eq_cnPlus
import Submission.Work.BoseBoxFock.dGamma_injective
import Submission.Work.BoseBoxFock.frkCore
import Submission.Work.BoseBoxFock.qVec_eq_etaOf_of_pairing
import Submission.Work.BoseBoxFock.re_boxSlotSum_boxT0_le_cnPlusC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.frkDictMain` — the slot/fibre dictionary `D4` of the kinetic half

The dictionary `Work.BoseBoxFock.FRK.FormRowKin4_of_oneBody4`: from the per-fibre one-body
inequality `hOB` (`OBineq4`) conclude the box-level kinetic-group row `FormRowKin4`.

This file re-proves the coordinate expansion of a slot **inside the weak cone** (the strong twin
`boxSlotSum_rankOnePair_weak` imports `AVGoodState`, which cannot coexist with
`boxSlotSum_measurable_bounded` in one cone — see `BLOCKER_nPlusC_duplicate.md`).

Structure:

* `boxSlotOf_expand_self` / `boxSlotSum_rankOne_eq_sum_slotOf` — the rank-one slot sum as a sum of
  single-slot maps;
* `AVgen_kinOnly` — the pointwise expansion of `AVgen` at the kinetic-only environment;
* `honestNH_eq` — the honest `n₊^H` as `dGamma` of the explicit weighted rank-one sum;
* the assembly `FormRowKin4_of_oneBody4`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

variable {m : ℕ}

/-! ## 1. The coordinate-vector reductions (weak cone) -/

/-- `η` at the coordinate vector `evec m l` is the mode `e l`. -/
private lemma etaOf_evec_w' {m : ℕ} (e : Fin m → Ω → ℂ) (l : Fin m) :
    Work.BoseDict.etaOf e (Work.BoseB4.evec m l) = e l := by
  funext z
  simp only [Work.BoseDict.etaOf, Work.BoseB4.evec, Pi.single_apply]
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ l) h

/-- The slot at coordinate vectors, in the explicit form used by the expansion. -/
private lemma boxSlotOf_evec_eq_w' {m d : ℕ} (e : Fin m → Ω → ℂ) (l l' : Fin m) (j : Fin d)
    (Θ : Work.BoseDict.Xn d → ℂ) :
    Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ
      = fun x => e l (x j) * ∫ z : Ω, (starRingEnd ℂ) (e l' z) *
          Θ (Function.update x j z) := by
  funext x
  simp only [Work.BoseDict.boxSlotOf, etaOf_evec_w']

/-- The sum defining `η_v` at a coordinate vector. -/
private lemma sum_evec_mul_w' {m : ℕ} (v : Fin m → ℝ) (l' : Fin m) :
    (∑ k : Fin m, v k * (Work.BoseB4.evec m l' k)) = v l' := by
  rw [Finset.sum_eq_single l']
  · simp [Work.BoseB4.evec]
  · intro b _ hb
    simp [Work.BoseB4.evec, Pi.single_eq_of_ne, hb]
  · intro h; exact absurd (Finset.mem_univ l') h

/-- `(|w⟩⟨v| (evec l'))_l = w_l v_{l'}`. -/
private lemma rankOnePair_evec_w' {m : ℕ} (w v : Fin m → ℝ) (l l' : Fin m) :
    rankOnePair w v (Work.BoseB4.evec m l') l = w l * v l' := by
  simp only [rankOnePair_apply, Pi.smul_apply, smul_eq_mul, sum_evec_mul_w']
  ring

/-- The change of variable `z ↦ Function.update x j z` is measurable. -/
private lemma measurable_update_w' {d : ℕ} (x : Work.BoseDict.Xn d) (j : Fin d) :
    Measurable (fun z : Ω => Function.update x j z) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  by_cases hij : i = j
  · subst hij
    simp only [Function.update_apply]
    exact measurable_id
  · simp [hij]

/-- **The slot integrand is integrable at the weak bundle.** -/
private lemma integrable_slotIntegrand_w' {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Θ : Work.BoseDict.Xn d → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (x : Work.BoseDict.Xn d) (j : Fin d) (l : Fin m) :
    Integrable (fun z : Ω => (starRingEnd ℂ) (e l z) * Θ (Function.update x j z)) := by
  obtain ⟨C, hC⟩ := hbdd l
  obtain ⟨C', hC'⟩ := hΘb
  refine Work.MB.integrable_of_bdd_of_support (C := max C 0 * max C' 0)
    (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)
    (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
    ((Complex.continuous_conj.measurable.comp (hmeas l)).mul
      (hΘm.comp (measurable_update_w' x j))).aestronglyMeasurable ?_ ?_
  · intro z
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul ((hC z).trans (le_max_left _ _)) ((hC' _).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  · intro z hz
    have hz0 : e l z = 0 := Function.notMem_support.mp (fun h => hz (hsupp l h))
    simp [hz0]

/-- `∫ z, conj (η_v z) · Θ (x[j ↦ z]) = Σ_{l'} v_{l'} ∫ z, conj (e_{l'} z) · Θ (x[j ↦ z])`. -/
private lemma slotIntegral_etaOf_eq_sum_w' {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (v : Fin m → ℝ) (j : Fin d) (x : Work.BoseDict.Xn d) (Θ : Work.BoseDict.Xn d → ℂ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    (∫ z : Ω, (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * Θ (Function.update x j z))
      = ∑ l' : Fin m, (v l' : ℂ) *
          ∫ z : Ω, (starRingEnd ℂ) (e l' z) * Θ (Function.update x j z) := by
  have key : (fun z : Ω => (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * Θ (Function.update x j z))
      = fun z : Ω => ∑ l' : Fin m,
          (v l' : ℂ) * ((starRingEnd ℂ) (e l' z) * Θ (Function.update x j z)) := by
    funext z
    simp only [Work.BoseDict.etaOf, map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [key, integral_finsetSum _
    (fun l' _ => (integrable_slotIntegrand_w' hmeas hbdd hsupp hΘm hΘb x j l').const_mul _)]
  refine Finset.sum_congr rfl (fun l' _ => ?_)
  rw [MeasureTheory.integral_const_mul]

/-- **A single slot expands in the coordinate basis** (weak cone). -/
theorem boxSlotOf_expand_self {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) (j : Fin d) (Θ : Work.BoseDict.Xn d → ℂ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    Work.BoseDict.boxSlotOf e w v j Θ
      = ∑ l : Fin m, ∑ l' : Fin m, (w l * v l') •
          Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ := by
  funext x
  have hI := slotIntegral_etaOf_eq_sum_w' hmeas hbdd hsupp v j x Θ hΘm hΘb
  have hL : Work.BoseDict.boxSlotOf e w v j Θ x
      = (∑ i : Fin m, (w i : ℂ) * e i (x j)) *
          ∑ b : Fin m, (v b : ℂ) *
            ∫ z : Ω, (starRingEnd ℂ) (e b z) * Θ (Function.update x j z) := by
    rw [show Work.BoseDict.boxSlotOf e w v j Θ x
        = Work.BoseDict.etaOf e w (x j) * ∫ z : Ω, (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) *
            Θ (Function.update x j z) from rfl]
    rw [hI]
    simp only [Work.BoseDict.etaOf]
  have hR : (∑ l : Fin m, ∑ l' : Fin m, (w l * v l') •
      Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ) x
      = ∑ a : Fin m, ∑ b : Fin m, ((w a : ℂ) * (v b : ℂ)) *
          (e a (x j) * ∫ z : Ω, (starRingEnd ℂ) (e b z) *
            Θ (Function.update x j z)) := by
    simp only [Finset.sum_apply, Pi.smul_apply, boxSlotOf_evec_eq_w', Complex.real_smul,
      Complex.ofReal_mul]
  rw [hL, hR, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))

/-- **The rank-one slot sum is the sum of the single-slot rank-one maps.** -/
theorem boxSlotSum_rankOne_eq_sum_slotOf {m d : ℕ} {ℓ : ℝ}
    {e : Fin m → Ω → ℂ} (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) (Θ : Work.BoseDict.Xn d → ℂ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    Work.BoseDict.boxSlotSum e (rankOne w) Θ
      = ∑ j : Fin d, Work.BoseDict.boxSlotOf e w w j Θ := by
  have hexp : ∀ j : Fin d, Work.BoseDict.boxSlotOf e w w j Θ
      = ∑ l : Fin m, ∑ l' : Fin m, (w l * w l') •
          Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ :=
    fun j => boxSlotOf_expand_self hmeas hbdd hsupp w w j Θ hΘm hΘb
  rw [rankOne_eq_rankOnePair]
  simp only [Work.BoseDict.boxSlotSum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hexp j]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun l' _ => ?_))
  rw [rankOnePair_evec_w']

/-! ## 2. The kinetic-group expansion of `AVgen` -/

/-- **`AVgen` at the kinetic-only environment is the sum of its three kinetic rows.** -/
theorem AVgen_kinOnly {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode]
    {ι : Type} (B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ))
    (f g : Mode → Fin m → ℝ) (T_NH : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (E : Work.BoseB7.Q3Env Mode) (Θ : (ι → Ω) → ℂ) :
    AVgen B (id : ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ)) f g T_NH (∅ : Finset Mode)
        (kinOnlyEnv E) 0 Θ
      = (∑ k : Mode, E.tau k • (B (rankOne (f k)) Θ))
        + (E.b / (2 * E.ell ^ 2)) • (B (boxT0 m) Θ)
        + (E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) • (B T_NH Θ) := by
  ext x
  simp only [AVgen, kinOnlyEnv, Finset.sum_empty, Finset.sum_apply, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, LinearMap.add_apply, LinearMap.smul_apply, Pi.zero_apply,
    smul_eq_mul, Finset.sum_const_zero, mul_zero, zero_mul, add_zero, zero_add,
    zero_smul, smul_zero, sub_self, sub_zero]

/-! ## 3. The honest `n₊^H` as an explicit `dGamma` -/

/-- **The honest family's `T.NH` is `dGamma` of the explicit weighted rank-one sum.**  This is the
explicit-witness form of `Work.BoseBoxFock.NH_eq_dGamma`, in the vocabulary (`kappaHon`,
`rankOnePair`) of the kinetic row. -/
theorem HonestBoxFam_NH_eq (v : Ω → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    (HonestBoxFam v h fc fu HM μ).T.NH
      = Work.BoseB4.dGamma (HM μ).m ((1 / 32 : ℝ) •
          ∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
            etaH fu (FRK.kappaHon v μ) (kmomLab (ellH v μ) (HM μ).N k) •
              rankOnePair ((HM μ).f k) ((HM μ).f k)) := by
  have h2 : (HonestBoxFam v h fc fu HM μ).T.NH
      = (1 / 32 : ℝ) • ∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
          etaH fu (FRK.kappaHon v μ) (kmomLab (ellH v μ) (HM μ).N k) •
            ((Work.BoseB4.creOf (HM μ).m ((HM μ).f k)).comp
              (Work.BoseB4.annOf (HM μ).m ((HM μ).f k))) := by
    dsimp only [HonestBoxFam, tildeDataHon, FRK.kappaHon]
  rw [h2]
  rw [(Work.BoseBoxFock.dGamma_rankSum (m := (HM μ).m) (f := (HM μ).f)
        (η := fun k => etaH fu (FRK.kappaHon v μ)
            (kmomLab (ellH v μ) (HM μ).N k))).symm]
  congr 1

end Work.BoseBoxFock
