import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1B.CutFibreForms
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.fibreSideConditions_cut`

The **side conditions** for the two states of the sharp-fibre program — the smooth approximants
`Ψ_δ = (∏ i, γ δ (x i))·ψ` (`Work.BoseFixB1B.cutProd (γ δ) ψ`) and the sharp in-box state
`W = 1_{B(u)^k}·ψ` (`Work.BoseFixB1B.sharpBoxState (dlBox L d u) ψ`) — in the vocabulary of
`Work.SmallBoxTBWord.boxQ` (`Q_{B(u),i}`):

* `Q_{B(u),i}Ψ_δ` is a.e.-measurable, bounded by `2·Cb` on `abox (n+1) L`, and its `i`-th
  windowed fibre `z ↦ χ_B(z)·Q_{B(u),i}Ψ_δ(kcInsN n i (z,r))` is `C^∞` on `abox n L`;
* the same three statements for `Q_{B(u),i}W`.

The smooth case is pure calculus (`boxQ` of a smooth function is smooth, `boxQ_contDiff`).  The
sharp case is the delicate one: `boxQ W` is *not* smooth, but its windowed slot-`i` fibre is,
because (a) the box mean `boxP` of a state of the form `Φ(kcInsN n i (·, r))` is *constant in the
slot-`i` variable*, and (b) on the support of `χ_B` the sharp indicator `1_{B(u)}` can be replaced
by the corresponding *smooth* factor `ψ(kcInsN n i (·, r))` (the `χ_B`-cutoff already kills the
`z ∉ B(u)` part).
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators ENNReal Classical

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedTactic false

/-! ## 1. Elementary facts about `kcInsN` -/

/-- **Overwriting the `i`-th slot of `kcInsN n i (z, r)` gives `kcInsN n i (w, r)`.** -/
theorem update_kcInsN {n : ℕ} (i : Fin (n + 1)) (r : X n) (z w : E3) :
    Function.update (kcInsN n i (z, r)) i w = kcInsN n i (w, r) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [kc_insN_apply_same]
  · rw [Function.update_of_ne hj]
    exact kc_insN_other_indep n i z w r j hj

/-- **`z ↦ kcInsN n i (z, r)` is smooth.**  It is `Function.update c i` for `c = kcInsN n i (0,r)`,
and `Function.update c i z = c + Function.update 0 i (z - c i)` is a translate of a linear map. -/
theorem contDiff_kcInsN_snd {n : ℕ} (i : Fin (n + 1)) (r : X n) :
    ContDiff ℝ (⊤ : ENat) (fun z : E3 => kcInsN n i (z, r)) := by
  have hfun : (fun z : E3 => kcInsN n i (z, r))
      = fun z => Function.update (kcInsN n i (0, r)) i z := by
    funext z j
    by_cases hj : j = i
    · subst hj; simp [kc_insN_apply_same]
    · rw [Function.update_of_ne hj]
      exact kc_insN_other_indep n i z 0 r j hj
  rw [hfun]
  have hsplit : (fun z : E3 => Function.update (kcInsN n i (0, r)) i z)
      = fun z => kcInsN n i (0, r)
          + Function.update (0 : X (n + 1)) i (z - (kcInsN n i (0, r)) i) := by
    funext z j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [hsplit]
  exact contDiff_const.add
    ((contDiff_update (⊤ : ENat) (0 : X (n + 1)) i).comp (by fun_prop))

/-! ## 2. The box projection of a `kcInsN`-fibre -/

/-- **The box mean `boxP` is constant along the `kcInsN n i (·, r)`-line.**  Explicitly
`boxP volA A i Φ (kcInsN n i (z,r)) = (1/volA)·∫_{w∈A} Φ (kcInsN n i (w,r))`. -/
theorem boxP_kcInsN {n : ℕ} (volA : ℝ) (A : Set E3) (i : Fin (n + 1))
    (Φ : X (n + 1) → ℝ) (r : X n) (z : E3) :
    Work.SmallBoxTBWord.boxP volA A i Φ (kcInsN n i (z, r))
      = (1 / volA) * ∫ w in A, Φ (kcInsN n i (w, r)) := by
  rw [Work.SmallBoxTBWord.boxP]
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with w
  congr 1
  exact update_kcInsN i r z w

/-- **The box mean-free projection along the `kcInsN n i (·, r)`-line.** -/
theorem boxQ_kcInsN {n : ℕ} (volA : ℝ) (A : Set E3) (i : Fin (n + 1))
    (Φ : X (n + 1) → ℝ) (r : X n) (z : E3) :
    Work.SmallBoxTBWord.boxQ volA A i Φ (kcInsN n i (z, r))
      = Φ (kcInsN n i (z, r)) - (1 / volA) * ∫ w in A, Φ (kcInsN n i (w, r)) := by
  simp only [Work.SmallBoxTBWord.boxQ]
  rw [boxP_kcInsN]

/-! ## 3. Generic side conditions for `boxQ` -/

/-- **The box mean-free projection is measurable whenever the state is.**  The box mean is the
parameter integral `x ↦ ∫_{z∈A} Φ (x_{i←z}) dz`, measurable in `x` by the Bochner version of
Fubini's theorem for the (jointly measurable) integrand `(x,z) ↦ Φ (x_{i←z})`. -/
theorem measurable_boxQ {N : ℕ} {A : Set E3} (volA : ℝ) (i : Fin N)
    {Φ : X N → ℝ} (hΦ : Measurable Φ) :
    Measurable (Work.SmallBoxTBWord.boxQ volA A i Φ) := by
  have hcurve : Measurable (fun p : X N × E3 => Φ (Function.update p.1 i p.2)) :=
    hΦ.comp (by fun_prop)
  have hint : StronglyMeasurable (fun x : X N =>
      ∫ z, Φ (Function.update x i z) ∂(volume.restrict A)) :=
    StronglyMeasurable.integral_prod_right' (ν := volume.restrict A) hcurve.stronglyMeasurable
  have hP : Measurable (Work.SmallBoxTBWord.boxP volA A i Φ) := by
    change Measurable (fun x : X N => (1 / volA) * ∫ z in A, Φ (Function.update x i z))
    exact (hint.const_mul (1 / volA)).measurable
  change Measurable (fun x => Φ x - Work.SmallBoxTBWord.boxP volA A i Φ x)
  exact hΦ.sub hP

/-- **The box mean-free projection of a state bounded by `C` on the ambient box is bounded by
`2C`.**  Both `Φ x` and the box mean `(1/volA)∫_{z∈A}Φ(x_{i←z})` are bounded by `C` there — the
latter because `A ⊆ acube ℓ`, so that inserting `z ∈ A` into slot `i` of `x ∈ abox N ℓ` keeps the
configuration inside `abox N ℓ`, and because `volA = |A|`. -/
theorem abs_boxQ_le_two {N : ℕ} {ℓ volA C : ℝ} {A : Set E3}
    (hℓ : 0 ≤ ℓ) (hAc : A ⊆ acube ℓ) (hvolA : volA = volume.real A)
    (hC : 0 ≤ C) {i : Fin N} {Φ : X N → ℝ}
    (hΦ : ∀ x ∈ abox N ℓ, |Φ x| ≤ C) :
    ∀ x ∈ abox N ℓ, |Work.SmallBoxTBWord.boxQ volA A i Φ x| ≤ 2 * C := by
  intro x hx
  have hfin : (volume : Measure E3) A < ∞ :=
    lt_of_le_of_lt (measure_mono hAc) (acube_lt_top ℓ hℓ)
  have hupd : ∀ z ∈ A, Function.update x i z ∈ abox N ℓ := by
    intro z hz
    rw [mem_abox_iff] at hx ⊢
    intro j
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]; exact hAc hz
    · rw [Function.update_of_ne hj]; exact hx j
  have hint : |∫ z in A, Φ (Function.update x i z)| ≤ C * volA := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := A) hfin
      (f := fun z => Φ (Function.update x i z)) (C := C) (fun z hz => by
        rw [Real.norm_eq_abs]; exact hΦ _ (hupd z hz))
    rw [Real.norm_eq_abs, ← hvolA] at h
    exact h
  have hP : |Work.SmallBoxTBWord.boxP volA A i Φ x| ≤ C := by
    rw [Work.SmallBoxTBWord.boxP]
    by_cases hvol0 : volA = 0
    · rw [hvol0, div_zero, zero_mul, abs_zero]; exact hC
    · have hpos : 0 < volA :=
        lt_of_le_of_ne (by rw [hvolA]; exact measureReal_nonneg) (Ne.symm hvol0)
      rw [abs_mul, abs_of_pos (one_div_pos.mpr hpos)]
      have h2 : (1 / volA) * (C * volA) = C := by field_simp
      calc (1 / volA) * |∫ z in A, Φ (Function.update x i z)|
          ≤ (1 / volA) * (C * volA) := mul_le_mul_of_nonneg_left hint (by positivity)
        _ = C := h2
  simp only [Work.SmallBoxTBWord.boxQ]
  calc |Φ x - Work.SmallBoxTBWord.boxP volA A i Φ x|
        ≤ |Φ x| + |Work.SmallBoxTBWord.boxP volA A i Φ x| := abs_sub _ _
    _ ≤ C + C := add_le_add (hΦ x hx) hP
    _ = 2 * C := by ring

/-! ## 4. The smooth approximant `cutProd (γ δ) ψ` -/

/-- **The product approximant is smooth** when `γ` and `ψ` are. -/
theorem contDiff_cutProd {k : ℕ} {γ : E3 → ℝ} {ψ : X k → ℝ}
    (hγ : ContDiff ℝ (⊤ : ENat) γ) (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    ContDiff ℝ (⊤ : ENat) (cutProd γ ψ) := by
  change ContDiff ℝ (⊤ : ENat) (fun x : X k => (∏ i : Fin k, γ (x i)) * ψ x)
  fun_prop

/-- **The product approximant is bounded by the state bound** for `0 ≤ γ ≤ 1`. -/
theorem abs_cutProd_le {k : ℕ} {ℓ Cb : ℝ} {γ : E3 → ℝ} {ψ : X k → ℝ}
    (hγ01 : ∀ x, 0 ≤ γ x ∧ γ x ≤ 1)
    (hψb : ∀ x ∈ abox k ℓ, |ψ x| ≤ Cb) :
    ∀ x ∈ abox k ℓ, |cutProd γ ψ x| ≤ Cb := by
  intro x hx
  have hprod0 : 0 ≤ ∏ i : Fin k, γ (x i) :=
    Finset.prod_nonneg (fun i _ => (hγ01 (x i)).1)
  have hprod1 : (∏ i : Fin k, γ (x i)) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => (hγ01 (x i)).1) (fun i _ => (hγ01 (x i)).2)
  have hcut : cutProd γ ψ x = (∏ i : Fin k, γ (x i)) * ψ x := rfl
  rw [hcut, abs_mul, abs_of_nonneg hprod0]
  calc (∏ i : Fin k, γ (x i)) * |ψ x| ≤ 1 * Cb :=
        mul_le_mul hprod1 (hψb x hx) (abs_nonneg _) zero_le_one
    _ = Cb := one_mul Cb

/-! ## 5. The sharp in-box state -/

/-- **The sharp in-box state is measurable** when the box and the state are. -/
theorem sharpBoxState_measurable {k : ℕ} {B : Set E3} (hB : MeasurableSet B)
    {ψ : X k → ℝ} (hψ : Measurable ψ) : Measurable (sharpBoxState B ψ) := by
  rw [sharpBoxState]
  refine hψ.indicator ?_
  rw [Work.PerSector.slotBox]
  rw [show {z : Fin k → E3 | ∀ i, z i ∈ B} = ⋂ i, {z : Fin k → E3 | z i ∈ B} from by
        ext z; simp [Set.mem_iInter]]
  exact MeasurableSet.iInter (fun i => hB.preimage (measurable_pi_apply i))

/-- **The sharp state is bounded by the state bound.** -/
theorem abs_sharpBoxState_le {k : ℕ} {ℓ Cb : ℝ} {B : Set E3} {ψ : X k → ℝ}
    (hCb : 0 ≤ Cb) (hψb : ∀ x ∈ abox k ℓ, |ψ x| ≤ Cb) :
    ∀ x ∈ abox k ℓ, |sharpBoxState B ψ x| ≤ Cb := by
  intro x hx
  by_cases hcond : ∀ i : Fin k, x i ∈ B
  · rw [sharpState_eq_self_of_mem hcond]; exact hψb x hx
  · rw [sharpState_eq_zero_of_notMem hcond, abs_zero]; exact hCb

/-- **The sharp indicator collapses on the support of `χ_{B(u)}`.**  On the support of the window
`χ_{B(u)}` the sharp box indicator `1_{B(u)}` may be dropped, at the price of the (continuous)
factor `ψ(kcInsN n i (·,r))`; the remaining condition on the *other* slots is independent of `z`. -/
theorem chiB_sharpBoxState_kcInsN {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (u : E3) (ψ : X (n + 1) → ℝ) (i : Fin (n + 1)) (r : X n) (z : E3) :
    Submission.BoseGases.chiB L d u z *
      sharpBoxState (dlBox L d u) ψ (kcInsN n i (z, r))
    = Submission.BoseGases.chiB L d u z *
        ((if ∀ j : Fin (n + 1), j ≠ i → (kcInsN n i (0, r)) j ∈ dlBox L d u
          then (1 : ℝ) else 0) * ψ (kcInsN n i (z, r))) := by
  rw [sharpState_apply]
  by_cases hP : ∀ j : Fin (n + 1), j ≠ i → (kcInsN n i (0, r)) j ∈ dlBox L d u
  · rw [if_pos hP]
    by_cases hcond : ∀ j : Fin (n + 1), (kcInsN n i (z, r)) j ∈ dlBox L d u
    · rw [if_pos hcond]; ring
    · rw [if_neg hcond]
      have hzB : z ∉ dlBox L d u := by
        intro hz
        apply hcond
        intro j
        by_cases hj : j = i
        · subst hj; rwa [kc_insN_apply_same]
        · rw [kc_insN_other_indep n i z 0 r j hj]; exact hP j hj
      have hchi : Submission.BoseGases.chiB L d u z = 0 := by
        by_contra hne
        exact hzB (chiB_support_mem hL hd u z hne)
      rw [hchi]; ring
  · rw [if_neg hP]
    push Not at hP
    obtain ⟨j, hji, hjB⟩ := hP
    have hcond : ¬ ∀ j' : Fin (n + 1), (kcInsN n i (z, r)) j' ∈ dlBox L d u := by
      intro hc
      exact hjB (by rw [← kc_insN_other_indep n i z 0 r j hji]; exact hc j)
    rw [if_neg hcond]; ring

/-- **The windowed slot-`i` fibre of `Q_{B(u),i}` applied to the sharp state is smooth.**  This is
the upshot of `boxQ_kcInsN` (the box mean is constant in the slot variable) and
`chiB_sharpBoxState_kcInsN` (the sharp indicator collapses on the support of `χ_B`). -/
theorem chiB_boxQ_sharpBoxState_fibre {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (u : E3) (ψ : X (n + 1) → ℝ) (i : Fin (n + 1)) (r : X n) :
    (fun z : E3 => Submission.BoseGases.chiB L d u z *
        Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (dlBox L d u) i
          (sharpBoxState (dlBox L d u) ψ)
          (kcInsN n i (z, r)))
      = fun z : E3 => Submission.BoseGases.chiB L d u z *
          ((if ∀ j : Fin (n + 1), j ≠ i → (kcInsN n i (0, r)) j ∈ dlBox L d u
            then (1 : ℝ) else 0) * ψ (kcInsN n i (z, r))
          - (1 / Work.SmallBoxSliding.boxMass L d u) *
              ∫ w in dlBox L d u,
                sharpBoxState (dlBox L d u) ψ (kcInsN n i (w, r))) := by
  funext z
  rw [boxQ_kcInsN, mul_sub]
  rw [chiB_sharpBoxState_kcInsN hL hd u ψ i r z]
  ring

/-! ## 6. The side conditions -/

theorem fibreSideConditions_cut {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3))
    {ψ : Submission.BoseGases.X (n+1) → ℝ} {K Cb : ℝ}
    {γ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hcut : Work.BoseFixB1B.IsCutFamily L d u K γ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hCb : 0 ≤ Cb)
    (hψb : ∀ x ∈ Submission.BoseGases.abox (n+1) L, |ψ x| ≤ Cb) :
    (∀ δ : ℝ, 0 < δ → ∀ i : Fin (n+1),
        AEMeasurable (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i (Work.BoseFixB1B.cutProd (γ δ) ψ))
        ∧ (∀ x ∈ Submission.BoseGases.abox (n+1) L,
            |Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i (Work.BoseFixB1B.cutProd (γ δ) ψ) x| ≤ 2 * Cb)
        ∧ (∀ r ∈ Submission.BoseGases.abox n L, ContDiff ℝ (⊤ : ENat)
            (fun z : EuclideanSpace ℝ (Fin 3) =>
            Submission.BoseGases.chiB L d u z *
              Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) i (Work.BoseFixB1B.cutProd (γ δ) ψ)
                (Submission.BoseGases.kcInsN n i (z, r)))))
    ∧ (∀ i : Fin (n+1),
        AEMeasurable (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i
            (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ))
        ∧ (∀ x ∈ Submission.BoseGases.abox (n+1) L,
            |Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i
              (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) x| ≤ 2 * Cb)
        ∧ (∀ r ∈ Submission.BoseGases.abox n L, ContDiff ℝ (⊤ : ENat)
            (fun z : EuclideanSpace ℝ (Fin 3) =>
            Submission.BoseGases.chiB L d u z *
              Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) i
                (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ)
                (Submission.BoseGases.kcInsN n i (z, r))))) := by
  have hAc : dlBox L d u ⊆ acube L := Work.SmallBoxSliding.dlBox_subset_acube L d u
  have hmeasA : MeasurableSet (dlBox L d u) := Work.SmallBoxSliding.measurableSet_dlBox L d u
  have hvolA : Work.SmallBoxSliding.boxMass L d u = volume.real (dlBox L d u) :=
    Work.SmallBoxSliding.boxMass_eq_measureReal L d u
  have hcl : IsCompact (dlBox L d u) := Work.SmallBoxTBWord.isCompact_dlBox hL hd u
  constructor
  · intro δ hδ i
    obtain ⟨hcd, -, h01, -, -⟩ := hcut.2 δ hδ
    have hCd : ContDiff ℝ (⊤ : ENat) (cutProd (γ δ) ψ) := contDiff_cutProd hcd hψ
    refine ⟨?_, ?_, ?_⟩
    · exact ((Work.SmallBoxTBWord.boxQ_contDiff hcl (Work.SmallBoxSliding.boxMass L d u) i
        hCd).continuous).aemeasurable
    · intro x hx
      exact abs_boxQ_le_two hL.le hAc hvolA hCb (abs_cutProd_le h01 hψb) x hx
    · intro r _
      exact (Work.SmallBoxTBWord.contDiff_chiB hL hd u).mul
        ((Work.SmallBoxTBWord.boxQ_contDiff hcl (Work.SmallBoxSliding.boxMass L d u) i
          hCd).comp (contDiff_kcInsN_snd i r))
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · exact (measurable_boxQ (A := dlBox L d u) (Work.SmallBoxSliding.boxMass L d u) i
        (sharpBoxState_measurable hmeasA hψ.continuous.measurable)).aemeasurable
    · intro x hx
      exact abs_boxQ_le_two hL.le hAc hvolA hCb (abs_sharpBoxState_le hCb hψb) x hx
    · intro r _
      rw [chiB_boxQ_sharpBoxState_fibre hL hd u ψ i r]
      by_cases hP : ∀ j : Fin (n + 1), j ≠ i → (kcInsN n i (0, r)) j ∈ dlBox L d u
      · rw [if_pos hP]
        exact (Work.SmallBoxTBWord.contDiff_chiB hL hd u).mul
          (((contDiff_const (c := (1 : ℝ))).mul
            (hψ.comp (contDiff_kcInsN_snd i r))).sub contDiff_const)
      · rw [if_neg hP]
        exact (Work.SmallBoxTBWord.contDiff_chiB hL hd u).mul
          (((contDiff_const (c := (0 : ℝ))).mul
            (hψ.comp (contDiff_kcInsN_snd i r))).sub contDiff_const)

end Work.BoseFixB1B
