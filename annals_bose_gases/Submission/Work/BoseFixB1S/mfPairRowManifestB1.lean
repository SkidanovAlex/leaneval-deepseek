import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1S.boxPInd_sq_le_self
import Submission.Work.BoseFixB1S.mfRows
import Submission.Work.BoseFixB1S.qSideLossB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open scoped ENNReal

/-! ## Helper lemmas for the manifest pair row

The target `mfPairRowManifestB1` is the *per-pair* compression (Jensen) step of the flat branch's
manifest identity: for a single ordered pair `p` of slots, with `σ = 1_A(x_{p.1})(1_A(x_{p.2})Φ)`
and `A_p = P_{p.1}P_{p.2}Φ`, the manifest square dominates the pair-condensate square up to the
AM–GM (Cauchy–Schwarz) correction built from the *unweighted* two-slot defect
`∫(σ − A_p)² ≤ ∫(Q_{p.1}Φ)² + ∫(Q_{p.2}Φ)²`.

The three ingredients are:
* `boxW_nonneg` — the localised pair kernel is pointwise nonnegative (`0 ≤ v`);
* `integrableOn_boxW_slot` — the slot-pullback of the kernel is integrable, from the target's
  hypothesis `hWint` (integrability of the kernel on `A × A`);
* `sqrt_arith_aux` — the scalar AM–GM/`√` arithmetic;
* `pIndQInd_orth_two`, `boxQInd_contract` — the projection algebra for the defect bound.
-/

/-- The localised pair kernel `boxW h μ u = wSmallPair M ℓ d u v` is pointwise nonnegative for a
nonnegative potential. -/
theorem boxW_nonneg {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (μ : ℝ) (u : ℝ³) :
    ∀ x y : ℝ³, 0 ≤ boxW h μ u x y := by
  intro x y
  exact wSmallPair_nonneg_B1S u x y (f := v) (hv (x - y))

/-- **Slot-pullback integrability of the localised pair kernel.**  If the kernel is integrable on
`A × A` (`A = boxA v μ u`) and vanishes off `A × A`, then for distinct slots `i j` and any
a.e.-strongly-measurable, a.e.-bounded weight `S`, the function `x ↦ S x · boxW h μ u (x i) (x j)`
is integrable over the centred box `abox N ℓ`.

Proof: let `W'` be a measurable representative of the (uncurried) kernel on
`volume.restrict (A × A)` (supplied by `hWint.aestronglyMeasurable`), put `V = 1_{A×A}·W'`.  Since
the kernel vanishes off `A × A`, `V = W` a.e. for Lebesgue measure, hence also a.e. for
`volume.restrict (acube ℓ ×ˢ acube ℓ)`; `V` is integrable on the cube square (it is dominated by
`W'` on the measurable set `A × A ⊆ acube ℓ ×ˢ acube ℓ`), so
`Submission.BoseGases.integrableOn_pair_comp_ae` makes the pullback `x ↦ V (x i, x j)` integrable on
the box, and
`Submission.BoseGases.ae_eq_pair_pullback` transfers the a.e.-equality of the pullbacks to `W`. -/
theorem integrableOn_boxW_slot {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) {μ : ℝ} {u : ℝ³}
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓside : ℓ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    (hWint : MeasureTheory.Integrable (fun p : ℝ³ × ℝ³ => boxW h μ u p.1 p.2)
      (MeasureTheory.volume.restrict (boxA v μ u ×ˢ boxA v μ u)))
    (hW0 : ∀ x y : ℝ³, (x ∉ boxA v μ u ∨ y ∉ boxA v μ u) → boxW h μ u x y = 0)
    {S : Submission.BoseGases.X N → ℝ}
    (hSm : MeasureTheory.AEStronglyMeasurable S
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)))
    {C : ℝ} (hSb : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      |S x| ≤ C) :
    MeasureTheory.Integrable (fun x : Submission.BoseGases.X N => S x * boxW h μ u (x i) (x j))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
  classical
  have hAmeas : MeasurableSet (boxA v μ u) := Work.SmallBoxSliding.measurableSet_dlBox _ _ _
  have hA2meas : MeasurableSet (boxA v μ u ×ˢ boxA v μ u) := hAmeas.prod hAmeas
  have hAc : boxA v μ u ⊆ Submission.BoseGases.acube ℓ := by
    rw [hℓside]
    exact Work.SmallBoxSliding.dlBox_subset_acube _ _ _
  -- the measurable representative of the kernel on `A × A`
  have hWaesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => boxW h μ u p.1 p.2)
      (MeasureTheory.volume.restrict (boxA v μ u ×ˢ boxA v μ u)) := hWint.aestronglyMeasurable
  set W' : ℝ³ × ℝ³ → ℝ :=
    MeasureTheory.AEStronglyMeasurable.mk (fun p : ℝ³ × ℝ³ => boxW h μ u p.1 p.2) hWaesm
    with hW'def
  have hW'm : Measurable W' := by
    rw [hW'def]; exact hWaesm.stronglyMeasurable_mk.measurable
  have hW'ae : (fun p : ℝ³ × ℝ³ => boxW h μ u p.1 p.2)
      =ᵐ[MeasureTheory.volume.restrict (boxA v μ u ×ˢ boxA v μ u)] W' := by
    rw [hW'def]; exact hWaesm.ae_eq_mk
  have hW'int : MeasureTheory.Integrable W'
      (MeasureTheory.volume.restrict (boxA v μ u ×ˢ boxA v μ u)) := hWint.congr hW'ae
  set V : ℝ³ × ℝ³ → ℝ := (boxA v μ u ×ˢ boxA v μ u).indicator W' with hVdef
  have hVm : Measurable V := by
    rw [hVdef]; exact hW'm.indicator hA2meas
  -- `V = W` a.e. for Lebesgue measure
  have hVae : (fun p : ℝ³ × ℝ³ => boxW h μ u p.1 p.2) =ᵐ[MeasureTheory.volume] V := by
    show ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure (ℝ³ × ℝ³)),
      (fun p : ℝ³ × ℝ³ => boxW h μ u p.1 p.2) p = V p
    rw [MeasureTheory.ae_iff]
    obtain ⟨G, hGsub, hGm, hGnull⟩ :=
      MeasureTheory.exists_measurable_superset_of_null (MeasureTheory.ae_iff.mp hW'ae)
    have hsub : {p : ℝ³ × ℝ³ | ¬ ((fun p : ℝ³ × ℝ³ => boxW h μ u p.1 p.2) p = V p)}
        ⊆ G ∩ (boxA v μ u ×ˢ boxA v μ u) := by
      intro p hp
      have hpmem : p ∈ boxA v μ u ×ˢ boxA v μ u := by
        by_contra hpn
        have h1 : V p = 0 := by rw [hVdef]; exact Set.indicator_of_notMem hpn W'
        have h2 : boxW h μ u p.1 p.2 = 0 := by
          by_cases hx : p.1 ∈ boxA v μ u
          · exact hW0 p.1 p.2 (Or.inr (fun hy => hpn (Set.mem_prod.mpr ⟨hx, hy⟩)))
          · exact hW0 p.1 p.2 (Or.inl hx)
        exact hp (by simpa only [h1] using h2)
      refine ⟨hGsub ?_, hpmem⟩
      have hVp : V p = W' p := by rw [hVdef]; exact Set.indicator_of_mem hpmem W'
      intro hEq
      exact hp (by rw [hVp, hEq])
    have hnull : (MeasureTheory.volume : MeasureTheory.Measure (ℝ³ × ℝ³))
        (G ∩ (boxA v μ u ×ˢ boxA v μ u)) = 0 := by
      rw [← MeasureTheory.Measure.restrict_apply hGm]
      exact hGnull
    exact MeasureTheory.measure_mono_null hsub hnull
  -- `V` is integrable on `A × A`, hence (it vanishes off `A × A`) globally
  have hV_AA : MeasureTheory.IntegrableOn V (boxA v μ u ×ˢ boxA v μ u) MeasureTheory.volume := by
    refine MeasureTheory.IntegrableOn.congr_fun hW'int ?_ hA2meas
    intro p hp
    rw [hVdef]; exact (Set.indicator_of_mem hp W').symm
  have hVint : MeasureTheory.Integrable V MeasureTheory.volume :=
    MeasureTheory.IntegrableOn.integrable_of_forall_notMem_eq_zero hV_AA (by
      intro p hp
      rw [hVdef]; exact Set.indicator_of_notMem hp W')
  have hVcube : MeasureTheory.IntegrableOn V
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) MeasureTheory.volume :=
    hVint.integrableOn
  -- peel to the slots
  obtain ⟨q, rfl⟩ : ∃ q, N = q + 2 := ⟨N - 2, by
    have h2 : 2 ≤ N := by
      by_contra hcon
      refine hij (Fin.ext ?_)
      have hi := i.isLt
      have hj := j.isLt
      omega
    omega⟩
  have hVpull : MeasureTheory.Integrable (fun x : Submission.BoseGases.X (q + 2) => V (x i, x j))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox (q + 2) ℓ)) :=
    Submission.BoseGases.integrableOn_pair_comp_ae hℓ i j hij hVcube
  have hdom : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X (q + 2) => C * |V (x i, x j)|)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox (q + 2) ℓ)) :=
    hVpull.abs.const_mul C
  have hSm' : MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X (q + 2) => S x * V (x i, x j))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox (q + 2) ℓ)) :=
    hSm.mul hVpull.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox (q + 2) ℓ)),
      ‖S x * V (x i, x j)‖ ≤ C * |V (x i, x j)| := by
    filter_upwards [hSb] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have hSVint : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X (q + 2) => S x * V (x i, x j))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox (q + 2) ℓ)) :=
    MeasureTheory.Integrable.mono' hdom hSm' hbound
  -- transfer the a.e. equality to the pullbacks
  have hVae' : (fun p : ℝ³ × ℝ³ => boxW h μ u p.1 p.2)
      =ᵐ[MeasureTheory.volume.restrict
        (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)] V :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_le_self) hVae
  have hpull : (fun x : Submission.BoseGases.X (q + 2) => boxW h μ u (x i) (x j))
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (q + 2) ℓ)]
      (fun x : Submission.BoseGases.X (q + 2) => V (x i, x j)) :=
    Submission.BoseGases.ae_eq_pair_pullback hℓ hij hVae'
  have hEq : (fun x : Submission.BoseGases.X (q + 2) => S x * V (x i, x j))
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (q + 2) ℓ)]
      (fun x : Submission.BoseGases.X (q + 2) => S x * boxW h μ u (x i) (x j)) := by
    filter_upwards [hpull] with x hx
    rw [hx]
  exact hSVint.congr hEq

/-- **The scalar AM–GM / Cauchy–Schwarz arithmetic of the manifest pair row.**  If `I` obeys the
AM–GM family `I ≥ −(lam·A + B/lam)/2` for every `lam > 0` (which is what the pointwise
`2gew + lam·g²w + (1/lam)e²w ≥ 0` integrates to), then `I ≥ −√(A·B)`; combined with
`B ≤ Kw·(q1+q2)` this gives the manifest row. -/
theorem sqrt_arith_aux {A B I Kw q1 q2 : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hKw : 0 ≤ Kw)
    (hBl : B ≤ Kw * (q1 + q2))
    (h : ∀ lam : ℝ, 0 < lam → -((lam * A + (1 / lam) * B) / 2) ≤ I) :
    A - 2 * Real.sqrt (Kw * (q1 + q2)) * Real.sqrt A ≤ A + 2 * I + B := by
  have hkey : -Real.sqrt (A * B) ≤ I := by
    by_cases hA0 : A = 0
    · subst hA0
      rw [zero_mul, Real.sqrt_zero, neg_zero]
      by_cases hB0 : B = 0
      · subst hB0
        have h1 := h 1 one_pos
        norm_num at h1
        linarith
      · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
        by_contra hcon
        rw [not_le] at hcon
        have hlam : 0 < -B / I := div_pos_of_neg_of_neg (by linarith : -B < 0) (by linarith : I < 0)
        have h1 := h (-B / I) hlam
        have hval : -(((-B / I) * 0 + (1 / (-B / I)) * B) / 2) = I / 2 := by
          have hmid : (1 / (-B / I)) * B = -I := by
            field_simp
          rw [mul_zero, zero_add, hmid]
          ring
        rw [hval] at h1
        linarith
    · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
      by_cases hB0 : B = 0
      · subst hB0
        rw [mul_zero, Real.sqrt_zero, neg_zero]
        by_contra hcon
        rw [not_le] at hcon
        have hlam : 0 < -I / A := div_pos (by linarith) hApos
        have h1 := h (-I / A) hlam
        have hval : -(((-I / A) * A + (1 / (-I / A)) * 0) / 2) = I / 2 := by
          have hmid : (-I / A) * A = -I := by
            field_simp
          rw [hmid, mul_zero, add_zero]
          ring
        rw [hval] at h1
        linarith
      · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
        have hAp : 0 < Real.sqrt A := Real.sqrt_pos.mpr hApos
        have hBp : 0 < Real.sqrt B := Real.sqrt_pos.mpr hBpos
        have hlam : 0 < Real.sqrt B / Real.sqrt A := div_pos hBp hAp
        have h1 := h (Real.sqrt B / Real.sqrt A) hlam
        have hval : -(((Real.sqrt B / Real.sqrt A) * A
              + (1 / (Real.sqrt B / Real.sqrt A)) * B) / 2) = -Real.sqrt (A * B) := by
          have h1a : (Real.sqrt B / Real.sqrt A) * A = Real.sqrt A * Real.sqrt B := by
            rw [div_mul_eq_mul_div]
            field_simp
            rw [Real.sq_sqrt hA]
          have h1b : (1 / (Real.sqrt B / Real.sqrt A)) * B = Real.sqrt A * Real.sqrt B := by
            rw [one_div_div, div_mul_eq_mul_div]
            field_simp
            rw [Real.sq_sqrt hB]
          rw [h1a, h1b, Real.sqrt_mul hA B]
          ring
        rw [hval] at h1
        exact h1
  have hC : 0 ≤ Kw * (q1 + q2) := le_trans hB hBl
  have hsqrt : Real.sqrt B ≤ Real.sqrt (Kw * (q1 + q2)) := Real.sqrt_le_sqrt hBl
  have hAB : -2 * Real.sqrt (Kw * (q1 + q2)) * Real.sqrt A ≤ 2 * I + B := by
    have h2 : 2 * (-Real.sqrt (A * B)) ≤ 2 * I := by linarith
    have h3 : Real.sqrt A * Real.sqrt B ≤ Real.sqrt A * Real.sqrt (Kw * (q1 + q2)) :=
      mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg A)
    have h4 : Real.sqrt (A * B) = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA B
    nlinarith [h2, h3, h4, hB, Real.sqrt_nonneg A]
  linarith

/-- The mean-free box projection `Q_i f = 1_A(· i)·f − P_i f` of a measurable state is measurable. -/
theorem measurable_isQ {N : ℕ} (volA : ℝ) (A : Set ℝ³) (hA : MeasurableSet A) (i : Fin N)
    {f : Submission.BoseGases.X N → ℝ} (hf : Measurable f) :
    Measurable (Work.UBBInputs8.boxQInd volA A i f) := by
  have h : Work.UBBInputs8.boxQInd volA A i f
      = fun x : Submission.BoseGases.X N =>
        Aind A (x i) * f x - Work.UBBInputs8.boxPInd volA A i f x := by
    funext x
    rw [Work.UBBInputs8.boxQInd]
    rfl
  rw [h]
  exact ((measurable_sigAt A hA i).mul hf).sub (measurable_boxPInd volA A hA i hf)

/-- **Orthogonality of the box projection and its complement, in different states.**
`∫_{abox N ℓ} (P_i f)·(Q_i g) = 0` for measurable `f`, `g` bounded on the box.

Route: `P_i f · Q_i g = P_i f · (1_A(· i) g − P_i g) = P_i f · g − P_i f · P_i g` pointwise
(`1_A(· i)·P_i f = P_i f`), and both terms integrate to `∫ f · P_i g` — the first by
`boxPIndSelfAdjoint`, the second by `boxPIndSelfAdjoint` at `(f, P_i g)` together with the pointwise
idempotence `boxPInd_idempotent`. -/
theorem pIndQInd_orth {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set ℝ³} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N) {f g : Submission.BoseGases.X N → ℝ}
    (hfm : Measurable f) {Cf : ℝ} (hfb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |f x| ≤ Cf)
    (hgm : Measurable g) {Cg : ℝ} (hgb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |g x| ≤ Cg) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxPInd volA A i f x * Work.UBBInputs8.boxQInd volA A i g x) = 0 := by
  have hPf_m : Measurable (Work.UBBInputs8.boxPInd volA A i f) :=
    measurable_boxPInd volA A hA i hfm
  have hPf_b : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A i f x| ≤ Cf :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc i hfb
  have hPg_m : Measurable (Work.UBBInputs8.boxPInd volA A i g) :=
    measurable_boxPInd volA A hA i hgm
  have hPg_b : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A i g x| ≤ Cg :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc i hgb
  have hint1 : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => Work.UBBInputs8.boxPInd volA A i f x * g x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    integrableOn_mul_of_bound hℓ hPf_m hgm hPf_b hgb
  have hint2 : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxPInd volA A i f x * Work.UBBInputs8.boxPInd volA A i g x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    integrableOn_mul_of_bound hℓ hPf_m hPg_m hPf_b hPg_b
  have hpt : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A i f x * Work.UBBInputs8.boxQInd volA A i g x
        = Work.UBBInputs8.boxPInd volA A i f x * g x
          - Work.UBBInputs8.boxPInd volA A i f x * Work.UBBInputs8.boxPInd volA A i g x := by
    intro x _
    have hQ : Work.UBBInputs8.boxQInd volA A i g x
        = Aind A (x i) * g x - Work.UBBInputs8.boxPInd volA A i g x := rfl
    have hfold : Aind A (x i) * Work.UBBInputs8.boxPInd volA A i f x
        = Work.UBBInputs8.boxPInd volA A i f x := aind_mul_boxPInd volA i f x
    rw [hQ, mul_sub]
    congr 1
    rw [← mul_assoc, mul_comm (Work.UBBInputs8.boxPInd volA A i f x) (Aind A (x i)), hfold]
  have hself1 := boxPIndSelfAdjoint (N := N) (i := i) hℓ hvol hA hvolA hAc hfm hfb hgm hgb
  have hself2 := boxPIndSelfAdjoint (N := N) (i := i) hℓ hvol hA hvolA hAc hfm hfb hPg_m hPg_b
  have hidem : (∫ x in Submission.BoseGases.abox N ℓ,
        f x * Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A i g) x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          f x * Work.UBBInputs8.boxPInd volA A i g x :=
    setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ) (fun x _ => by
      rw [boxPInd_idempotent hℓ hvol hA hvolA hAc i g x])
  calc (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxPInd volA A i f x * Work.UBBInputs8.boxQInd volA A i g x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i f x * g x
            - Work.UBBInputs8.boxPInd volA A i f x * Work.UBBInputs8.boxPInd volA A i g x) :=
        setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ) hpt
    _ = (∫ x in Submission.BoseGases.abox N ℓ, Work.UBBInputs8.boxPInd volA A i f x * g x)
          - ∫ x in Submission.BoseGases.abox N ℓ,
              Work.UBBInputs8.boxPInd volA A i f x * Work.UBBInputs8.boxPInd volA A i g x :=
        MeasureTheory.integral_sub hint1 hint2
    _ = (∫ x in Submission.BoseGases.abox N ℓ, f x * Work.UBBInputs8.boxPInd volA A i g x)
          - ∫ x in Submission.BoseGases.abox N ℓ, f x * Work.UBBInputs8.boxPInd volA A i g x := by
        rw [hself1, hself2, hidem]
    _ = 0 := sub_self _

/-- **The two-slot defect bound.**  For a continuous state `Ψ` on the centred box and distinct
slots `i j`, the square of the defect `1_A(x_i)·(1_A(x_j)·Ψ) − P_iP_jΨ` is bounded, integrated,
by the sum of the two one-slot `Q`-counts.

Route: `1_A(x i)·1_A(x j)·Ψ = P_iP_jΨ + P_iQ_jΨ + Q_iP_jΨ + Q_iQ_jΨ` pointwise on the box
(`boxPatternSum`), so the defect is `X + (Y + Z)` with `X = P_iQ_jΨ` and `Y + Z`; the cross term
`∫X(Y+Z)` vanishes by `pIndQInd_orth`, `∫X² ≤ ∫(Q_jΨ)²` by the contraction `boxPInd_sq_le_self`, and
`Y + Z = 1_A(· j)·Q_iΨ` (`boxQInd_add` + `boxQInd_smul`), whence `∫(Y+Z)² ≤ ∫(Q_iΨ)²`. -/
theorem boxDefect_le {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set ℝ³} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {i j : Fin N} (hij : i ≠ j)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨc : Continuous Ψ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Aind A (x i) * (Aind A (x j) * Ψ x)
          - Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x) ^ 2)
      ≤ (∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Ψ x) ^ 2)
        + (∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxQInd volA A j Ψ x) ^ 2) := by
  obtain ⟨C, hC0, hC, hPb, hQb⟩ := boxBounds hℓ hvol hA hvolA hAc hΨc
  have hP2m : Measurable (Work.UBBInputs8.boxPInd volA A j Ψ) :=
    measurable_boxPInd volA A hA j hΨc.measurable
  have hQ2m : Measurable (Work.UBBInputs8.boxQInd volA A j Ψ) :=
    measurable_isQ volA A hA j hΨc.measurable
  have hQ1m : Measurable (Work.UBBInputs8.boxQInd volA A i Ψ) :=
    measurable_isQ volA A hA i hΨc.measurable
  have hP2b : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Work.UBBInputs8.boxPInd volA A j Ψ x| ≤ C :=
    fun x hx => hPb j x hx
  have hQ2b : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Work.UBBInputs8.boxQInd volA A j Ψ x| ≤ 2 * C :=
    fun x hx => hQb j x hx
  have hQ1b : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Work.UBBInputs8.boxQInd volA A i Ψ x| ≤ 2 * C :=
    fun x hx => hQb i x hx
  have hP12b : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x| ≤ C :=
    fun x hx => abs_boxPInd_le hℓ hvol hA hvolA hAc i hP2b x hx
  have hP1Q2m : Measurable
      (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ)) :=
    measurable_boxPInd volA A hA i hQ2m
  have hP1Q2b : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x| ≤ 2 * C :=
    fun x hx => abs_boxPInd_le hℓ hvol hA hvolA hAc i hQ2b x hx
  have hQ1P2m : Measurable
      (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ)) :=
    measurable_isQ volA A hA i hP2m
  have hQ1P2b : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x| ≤ 2 * (2 * C) :=
    fun x hx => by
      have h := hQb i x hx
      simp only [Work.UBBInputs8.boxQInd] at h ⊢
      calc |Aind A (x i) * Work.UBBInputs8.boxPInd volA A j Ψ x
            - Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x|
          ≤ |Aind A (x i) * Work.UBBInputs8.boxPInd volA A j Ψ x|
            + |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x| := by
            simpa [sub_eq_add_neg] using abs_add_le
              (Aind A (x i) * Work.UBBInputs8.boxPInd volA A j Ψ x)
              (-(Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x))
        _ ≤ C + C := by
            refine add_le_add ?_ (hP12b x hx)
            rw [abs_mul]
            have hb := mul_le_mul (Aind_abs_le_one A (x i)) (hP2b x hx)
              (abs_nonneg (Work.UBBInputs8.boxPInd volA A j Ψ x)) (by norm_num)
            simpa using hb
        _ ≤ 2 * (2 * C) := by linarith
  have hQ1Q2m : Measurable
      (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ)) :=
    measurable_isQ volA A hA i hQ2m
  have hQ1Q2b : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x| ≤ 2 * (2 * C) := by
    intro x hx
    have h := hQb i x hx
    simp only [Work.UBBInputs8.boxQInd] at h ⊢
    calc |Aind A (x i) * Work.UBBInputs8.boxQInd volA A j Ψ x
          - Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x|
        ≤ |Aind A (x i) * Work.UBBInputs8.boxQInd volA A j Ψ x|
          + |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x| := by
          simpa [sub_eq_add_neg] using abs_add_le
            (Aind A (x i) * Work.UBBInputs8.boxQInd volA A j Ψ x)
            (-(Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x))
      _ ≤ 2 * C + 2 * C := by
          refine add_le_add ?_ (hP1Q2b x hx)
          rw [abs_mul]
          have hb := mul_le_mul (Aind_abs_le_one A (x i)) (hQ2b x hx)
            (abs_nonneg (Work.UBBInputs8.boxQInd volA A j Ψ x)) (by norm_num)
          linarith [hb]
      _ ≤ 2 * (2 * C) := by linarith
  -- the pointwise decomposition of the defect
  have hpt : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Aind A (x i) * (Aind A (x j) * Ψ x)
          - Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
        = Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
          + (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
            + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) := by
    intro x hx
    have h1 := boxPatternSum hℓ hvol hA hvolA hAc hij hΨc x hx
    have h2 : Aind A (x i) * (Aind A (x j) * Ψ x) = Aind A (x i) * Aind A (x j) * Ψ x := by
      ring
    linarith [h1, h2]
  -- integrability of the three pieces
  have hX2int : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) ^ 2)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    integrableOn_sq_of_bound hℓ hP1Q2m hP1Q2b
  have hQ1sq : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => (Work.UBBInputs8.boxQInd volA A i Ψ x) ^ 2)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    integrableOn_sq_of_bound hℓ hQ1m hQ1b
  have hQ2sq : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => (Work.UBBInputs8.boxQInd volA A j Ψ x) ^ 2)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    integrableOn_sq_of_bound hℓ hQ2m hQ2b
  -- `Y + Z = 1_A(· j)·Q_iΨ`
  have hYZeq : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
        + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
      = Aind A (x j) * Work.UBBInputs8.boxQInd volA A i Ψ x := by
    intro x hx
    have hP2slot : MeasureTheory.IntegrableOn
        (fun z => Work.UBBInputs8.boxPInd volA A j Ψ (Function.update x i z)) A
        MeasureTheory.volume :=
      slotInt_of_bound hℓ hA hAc i x hx hP2m hP2b
    have hQ2slot : MeasureTheory.IntegrableOn
        (fun z => Work.UBBInputs8.boxQInd volA A j Ψ (Function.update x i z)) A
        MeasureTheory.volume :=
      slotInt_of_bound hℓ hA hAc i x hx hQ2m hQ2b
    have hadd := boxQInd_add (volA := volA) A i x
      (Φ := Work.UBBInputs8.boxPInd volA A j Ψ)
      (Ψ := Work.UBBInputs8.boxQInd volA A j Ψ) hP2slot hQ2slot
    have hsum : (Work.UBBInputs8.boxPInd volA A j Ψ + Work.UBBInputs8.boxQInd volA A j Ψ)
        = fun y => Aind A (y j) * Ψ y := by
      funext y
      rw [Pi.add_apply, Work.UBBInputs8.boxQInd]
      simp only [Aind]
      ring
    rw [hsum] at hadd
    have hsmul := boxQInd_smul volA A hij Ψ x
    rw [← hadd, hsmul, Work.UBBInputs8.boxQInd]
    simp only [Aind]
    ring
  -- the cross term vanishes
  have hYZint : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
          + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) ^ 2)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
    have hb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
          + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x|
        ≤ 2 * (2 * C) + 2 * (2 * C) := by
      intro x hx
      have h1 := hQ1P2b x hx
      have h2 := hQ1Q2b x hx
      calc |Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
            + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x|
          ≤ |Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x|
            + |Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x| :=
            abs_add_le _ _
        _ ≤ 2 * (2 * C) + 2 * (2 * C) := by linarith
    exact integrableOn_sq_of_bound hℓ (hQ1P2m.add hQ1Q2m) hb
  have hXWint : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
          * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
            + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    integrableOn_mul_of_bound hℓ hP1Q2m (hQ1P2m.add hQ1Q2m) hP1Q2b (Cg := 2 * (2 * C) + 2 * (2 * C))
      (by
        intro x hx
        have h1 := hQ1P2b x hx
        have h2 := hQ1Q2b x hx
        calc |Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
              + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x|
            ≤ |Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x|
              + |Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x| :=
              abs_add_le _ _
          _ ≤ 2 * (2 * C) + 2 * (2 * C) := by linarith)
  have hXYint : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
          * Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    integrableOn_mul_of_bound hℓ hP1Q2m hQ1P2m hP1Q2b hQ1P2b
  have hXZint : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
          * Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    integrableOn_mul_of_bound hℓ hP1Q2m hQ1Q2m hP1Q2b hQ1Q2b
  have hcross : (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
          * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
            + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x)) = 0 := by
    have hsplit : (∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
            * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
              + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x))
        = (∫ x in Submission.BoseGases.abox N ℓ,
            Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
              * Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x)
          + ∫ x in Submission.BoseGases.abox N ℓ,
              Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
                * Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x := by
      rw [show (fun x : Submission.BoseGases.X N =>
            Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
              * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
                + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x))
          = (fun x : Submission.BoseGases.X N =>
              Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
                * Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
              + Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
                * Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x)
          from by funext x; ring]
      rw [MeasureTheory.integral_add hXYint hXZint]
    rw [hsplit]
    have h0a : (∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
            * Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x) = 0 :=
      pIndQInd_orth hℓ hvol hA hvolA hAc i hQ2m hQ2b hP2m hP2b
    have h0b : (∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
            * Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) = 0 :=
      pIndQInd_orth hℓ hvol hA hvolA hAc i hQ2m hQ2b hQ2m hQ2b
    rw [h0a, h0b, add_zero]
  -- `∫ X² ≤ q_j`
  have hX2le : (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxQInd volA A j Ψ x) ^ 2 :=
    boxPInd_sq_le_self hℓ hvol hA hvolA hAc i hQ2m hQ2b
  -- `∫ (Y+Z)² ≤ q_i`
  have hYZle : (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
          + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Ψ x) ^ 2 := by
    have h1 : (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
            + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) ^ 2)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            (Aind A (x j) * Work.UBBInputs8.boxQInd volA A i Ψ x) ^ 2 :=
      setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
        (fun x hx => by rw [hYZeq x hx])
    rw [h1]
    refine MeasureTheory.integral_mono_of_nonneg ?_ hQ1sq ?_
    · filter_upwards with x
      positivity
    · filter_upwards with x
      show (Aind A (x j) * Work.UBBInputs8.boxQInd volA A i Ψ x) ^ 2
        ≤ (Work.UBBInputs8.boxQInd volA A i Ψ x) ^ 2
      rw [mul_pow]
      refine mul_le_of_le_one_left (sq_nonneg _) ?_
      have h2 := Aind_abs_le_one A (x j)
      nlinarith [abs_nonneg (Aind A (x j)), sq_abs (Aind A (x j))]
  -- assembly
  have hstep1 : (∫ x in Submission.BoseGases.abox N ℓ,
        (Aind A (x i) * (Aind A (x j) * Ψ x)
          - Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
            + (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
              + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x)) ^ 2 :=
    setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
      (fun x hx => by rw [hpt x hx])
  have hstep2 : (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
          + (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
            + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x)) ^ 2)
      = (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) ^ 2)
        + 2 * (∫ x in Submission.BoseGases.abox N ℓ,
            Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
              * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
                + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x))
        + (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
              + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) ^ 2) := by
    have hpt1 : (fun x : Submission.BoseGases.X N =>
          (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
            + (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
              + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x)) ^ 2)
        = (fun x : Submission.BoseGases.X N =>
            (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) ^ 2
            + 2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
              * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
                + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x)))
          + (fun x : Submission.BoseGases.X N =>
            (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
              + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) ^ 2) := by
      funext x
      show (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x + (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x)) ^ 2
        = (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) ^ 2 + 2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x)) + (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) ^ 2
      ring
    have hstep2a : (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
            + (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
              + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x)) ^ 2)
        = (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) ^ 2
              + 2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
                * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
                  + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x)))
          + (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
                + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) ^ 2) := by
      rw [hpt1]
      exact MeasureTheory.integral_add (hX2int.add (hXWint.const_mul 2)) hYZint
    have hpt2 : (fun x : Submission.BoseGases.X N =>
            (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) ^ 2
            + 2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
              * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
                + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x)))
        = (fun x : Submission.BoseGases.X N =>
            (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) ^ 2)
          + (fun x : Submission.BoseGases.X N =>
            2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
              * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
                + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x))) := by
      funext x
      show (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) ^ 2 + 2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x))
        = (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) ^ 2 + 2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x))
      ring
    have hstep2b : (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) ^ 2
            + 2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
              * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
                + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x)))
        = (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) ^ 2)
          + 2 * (∫ x in Submission.BoseGases.abox N ℓ,
              Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
                * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
                  + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x)) := by
      have hsplit : (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) ^ 2
            + 2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
              * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
                + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x)))
          = (∫ x in Submission.BoseGases.abox N ℓ,
                (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) ^ 2)
            + ∫ x in Submission.BoseGases.abox N ℓ,
                2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
                  * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x
                    + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x)) :=
        MeasureTheory.integral_add hX2int (hXWint.const_mul 2)
      rw [hsplit, MeasureTheory.integral_const_mul]
    rw [hstep2a, hstep2b]
  rw [hstep1, hstep2, hcross]
  linarith [hX2le, hYZle]

/-- **The abstract per-pair manifest row.**  With `sg = g + e` pointwise, a weight `0 ≤ K ≤ Kw`,
integrable weighted integrals and the *unweighted* two-slot defect bound `∫e² ≤ q1 + q2`, the
manifest square dominates the pair-condensate square up to the AM–GM correction:

    ∫sg²K ≥ ∫g²K − 2√(Kw(q1+q2))·√(∫g²K) .

Route: `∫sg²K = ∫g²K + 2∫geK + ∫e²K` (linearity), the pointwise square
`λ²g²K + 2λ·geK + e²K = (λg+e)²K ≥ 0` integrates and linearizes to the AM–GM family
`∫geK ≥ −(λ∫g²K + (1/λ)∫e²K)/2`, `sqrt_arith_aux` turns the family into `∫geK ≥ −√(B·Q)`, and
`∫e²K ≤ Kw·(q1+q2)` (from `0 ≤ K ≤ Kw` and the defect bound) closes the arithmetic. -/
theorem manifest_row_core {α : Type*} [MeasurableSpace α] {ν : MeasureTheory.Measure α}
    {sg g e K : α → ℝ} {q1 q2 Kw : ℝ}
    (hsplit : ∀ x, sg x = g x + e x)
    (hKnn : ∀ x, 0 ≤ K x) (hKw : ∀ x, K x ≤ Kw) (hKwnn : 0 ≤ Kw)
    (hint_sg : MeasureTheory.Integrable (fun x => (sg x) ^ 2 * K x) ν)
    (hint_g2 : MeasureTheory.Integrable (fun x => (g x) ^ 2 * K x) ν)
    (hint_e2 : MeasureTheory.Integrable (fun x => (e x) ^ 2 * K x) ν)
    (hint_ge : MeasureTheory.Integrable (fun x => g x * e x * K x) ν)
    (hint_e2u : MeasureTheory.Integrable (fun x => (e x) ^ 2) ν)
    (hdef : (∫ x, (e x) ^ 2 ∂ν) ≤ q1 + q2) :
    (∫ x, (g x) ^ 2 * K x ∂ν) - 2 * (Real.sqrt (Kw * (q1 + q2))
        * Real.sqrt (∫ x, (g x) ^ 2 * K x ∂ν))
      ≤ ∫ x, (sg x) ^ 2 * K x ∂ν := by
  have hge2 : MeasureTheory.Integrable (fun x => 2 * (g x * e x * K x)) ν := hint_ge.const_mul 2
  have hBnn : 0 ≤ ∫ x, (g x) ^ 2 * K x ∂ν :=
    MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (hKnn x)))
  have hQnn : 0 ≤ ∫ x, (e x) ^ 2 * K x ∂ν :=
    MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (hKnn x)))
  -- (1) the linear expansion
  have hlin : (∫ x, (sg x) ^ 2 * K x ∂ν)
      = (∫ x, (g x) ^ 2 * K x ∂ν) + 2 * (∫ x, g x * e x * K x ∂ν)
        + (∫ x, (e x) ^ 2 * K x ∂ν) := by
    have hpt : (fun x => (sg x) ^ 2 * K x)
        = (fun x => (g x) ^ 2 * K x + 2 * (g x * e x * K x)) + (fun x => (e x) ^ 2 * K x) := by
      funext x
      rw [hsplit x]
      show (g x + e x) ^ 2 * K x
        = (g x) ^ 2 * K x + 2 * (g x * e x * K x) + (e x) ^ 2 * K x
      ring
    have hstep : (∫ x, (sg x) ^ 2 * K x ∂ν)
        = (∫ x, (g x) ^ 2 * K x + 2 * (g x * e x * K x) ∂ν)
          + (∫ x, (e x) ^ 2 * K x ∂ν) := by
      rw [hpt]
      exact MeasureTheory.integral_add (hint_g2.add hge2) hint_e2
    have hpt2 : (fun x => (g x) ^ 2 * K x + 2 * (g x * e x * K x))
        = (fun x => (g x) ^ 2 * K x) + (fun x => 2 * (g x * e x * K x)) := by
      funext x
      show (g x) ^ 2 * K x + 2 * (g x * e x * K x)
        = (g x) ^ 2 * K x + 2 * (g x * e x * K x)
      ring
    rw [hstep, hpt2]
    have e1 : MeasureTheory.integral ν ((fun x : α => (g x) ^ 2 * K x)
          + (fun x : α => 2 * (g x * e x * K x)))
        = (∫ x, (g x) ^ 2 * K x ∂ν) + 2 * (∫ x, g x * e x * K x ∂ν) := by
      have h0 : MeasureTheory.integral ν ((fun x : α => (g x) ^ 2 * K x)
            + (fun x : α => 2 * (g x * e x * K x)))
          = (∫ x, (g x) ^ 2 * K x ∂ν) + (∫ x, 2 * (g x * e x * K x) ∂ν) :=
        MeasureTheory.integral_add hint_g2 hge2
      rw [h0, MeasureTheory.integral_const_mul]
    rw [e1]
  -- (2) the AM–GM family
  have hamgm : ∀ lam : ℝ, 0 < lam →
      -((lam * (∫ x, (g x) ^ 2 * K x ∂ν) + (1 / lam) * (∫ x, (e x) ^ 2 * K x ∂ν)) / 2)
        ≤ ∫ x, g x * e x * K x ∂ν := by
    intro lam hlam
    have hpt : ∀ x, 0 ≤ lam ^ 2 * ((g x) ^ 2 * K x) + 2 * lam * (g x * e x * K x)
        + (e x) ^ 2 * K x := by
      intro x
      have hsq : lam ^ 2 * ((g x) ^ 2 * K x) + 2 * lam * (g x * e x * K x) + (e x) ^ 2 * K x
          = (lam * g x + e x) ^ 2 * K x := by ring
      rw [hsq]
      exact mul_nonneg (sq_nonneg _) (hKnn x)
    have hint1 : MeasureTheory.Integrable (fun x => lam ^ 2 * ((g x) ^ 2 * K x)) ν :=
      hint_g2.const_mul _
    have hint2 : MeasureTheory.Integrable (fun x => 2 * lam * (g x * e x * K x)) ν :=
      hint_ge.const_mul _
    have hnn : 0 ≤ ∫ x, lam ^ 2 * ((g x) ^ 2 * K x) + 2 * lam * (g x * e x * K x)
        + (e x) ^ 2 * K x ∂ν :=
      MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall hpt)
    have hpt2 : (fun x => lam ^ 2 * ((g x) ^ 2 * K x) + 2 * lam * (g x * e x * K x)
          + (e x) ^ 2 * K x)
        = ((fun x : α => lam ^ 2 * ((g x) ^ 2 * K x))
            + (fun x : α => 2 * lam * (g x * e x * K x)))
          + (fun x : α => (e x) ^ 2 * K x) := by
      funext x
      show lam ^ 2 * ((g x) ^ 2 * K x) + 2 * lam * (g x * e x * K x) + (e x) ^ 2 * K x
        = lam ^ 2 * ((g x) ^ 2 * K x) + 2 * lam * (g x * e x * K x) + (e x) ^ 2 * K x
      ring
    rw [hpt2] at hnn
    have e2 : MeasureTheory.integral ν (((fun x : α => lam ^ 2 * ((g x) ^ 2 * K x))
          + (fun x : α => 2 * lam * (g x * e x * K x))) + (fun x : α => (e x) ^ 2 * K x))
        = (MeasureTheory.integral ν ((fun x : α => lam ^ 2 * ((g x) ^ 2 * K x))
              + (fun x : α => 2 * lam * (g x * e x * K x))))
          + (∫ x, (e x) ^ 2 * K x ∂ν) :=
      MeasureTheory.integral_add (hint1.add hint2) hint_e2
    rw [e2] at hnn
    have e1 : MeasureTheory.integral ν ((fun x : α => lam ^ 2 * ((g x) ^ 2 * K x))
          + (fun x : α => 2 * lam * (g x * e x * K x)))
        = lam ^ 2 * (∫ x, (g x) ^ 2 * K x ∂ν) + 2 * lam * (∫ x, g x * e x * K x ∂ν) := by
      have h0 : MeasureTheory.integral ν ((fun x : α => lam ^ 2 * ((g x) ^ 2 * K x))
            + (fun x : α => 2 * lam * (g x * e x * K x)))
          = (∫ x, lam ^ 2 * ((g x) ^ 2 * K x) ∂ν)
            + (∫ x, 2 * lam * (g x * e x * K x) ∂ν) :=
        MeasureTheory.integral_add hint1 hint2
      rw [h0, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [e1] at hnn
    have h4 : (lam ^ 2 * (∫ x, (g x) ^ 2 * K x ∂ν)
          + 2 * lam * (∫ x, g x * e x * K x ∂ν) + (∫ x, (e x) ^ 2 * K x ∂ν)) / (2 * lam)
        = (lam * (∫ x, (g x) ^ 2 * K x ∂ν)
            + (1 / lam) * (∫ x, (e x) ^ 2 * K x ∂ν)) / 2
          + (∫ x, g x * e x * K x ∂ν) := by
      field_simp
      ring
    have h5 : 0 ≤ (lam * (∫ x, (g x) ^ 2 * K x ∂ν)
          + (1 / lam) * (∫ x, (e x) ^ 2 * K x ∂ν)) / 2
        + (∫ x, g x * e x * K x ∂ν) := by
      have hpos : 0 < 2 * lam := by linarith
      have := div_nonneg hnn hpos.le
      rwa [h4] at this
    linarith
  -- (3) the weighted defect bound
  have hQle : (∫ x, (e x) ^ 2 * K x ∂ν) ≤ Kw * (q1 + q2) := by
    have hmono : (∫ x, (e x) ^ 2 * K x ∂ν) ≤ ∫ x, Kw * (e x) ^ 2 ∂ν := by
      refine MeasureTheory.integral_mono_ae hint_e2 (hint_e2u.const_mul Kw) ?_
      filter_upwards with x
      have h := mul_le_mul_of_nonneg_right (hKw x) (sq_nonneg (e x))
      simpa only [mul_comm] using h
    have hval : (∫ x, Kw * (e x) ^ 2 ∂ν) = Kw * (∫ x, (e x) ^ 2 ∂ν) :=
      MeasureTheory.integral_const_mul Kw _
    have hle : Kw * (∫ x, (e x) ^ 2 ∂ν) ≤ Kw * (q1 + q2) :=
      mul_le_mul_of_nonneg_left hdef hKwnn
    linarith
  have harith := sqrt_arith_aux (A := ∫ x, (g x) ^ 2 * K x ∂ν) (B := ∫ x, (e x) ^ 2 * K x ∂ν)
    (I := ∫ x, g x * e x * K x ∂ν) (Kw := Kw) (q1 := q1) (q2 := q2)
    hBnn hQnn hKwnn hQle hamgm
  have heq : (2 : ℝ) * (Real.sqrt (Kw * (q1 + q2)) * Real.sqrt (∫ x, (g x) ^ 2 * K x ∂ν))
      = 2 * Real.sqrt (Kw * (q1 + q2)) * Real.sqrt (∫ x, (g x) ^ 2 * K x ∂ν) := by ring
  rw [heq]
  linarith [hlin, harith]

theorem mfPairRowManifestB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {μ Kw : ℝ} (hμ : 0 < μ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3))
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hV : 0 < Work.BoseFixB1S.mfV v μ u) (hΦc : Continuous Φ)
    (hsupp : Work.BoseFixB1S.mfSupp v μ n Φ u)
    (hKw : ∀ x y : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1S.boxW h μ u x y ≤ Kw)
    (hWint : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixB1S.boxW h μ u p.1 p.2)
      (MeasureTheory.volume.restrict (Work.BoseFixB1S.boxA v μ u ×ˢ Work.BoseFixB1S.boxA v μ u)))
    {p : Fin n × Fin n} (hp : p ∈ Submission.BoseGases.pairSet n) :
    (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        ((Work.BoseFixB1S.boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.1)
          * ((Work.BoseFixB1S.boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2
          * Work.BoseFixB1S.boxW h μ u (x p.1) (x p.2))
      ≥ (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          (Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.1
            (Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.2 Φ) x) ^ 2
            * Work.BoseFixB1S.boxW h μ u (x p.1) (x p.2))
        - 2 * (Real.sqrt (Kw
              * ((∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                    (Work.UBBInputs8.boxQInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.1 Φ x) ^ 2)
                + (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                    (Work.UBBInputs8.boxQInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.2 Φ x) ^ 2)))
            * Real.sqrt (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.1
                  (Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.2 Φ) x) ^ 2
                  * Work.BoseFixB1S.boxW h μ u (x p.1) (x p.2))) := by
  classical
  have hij : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
  -- the kernel is nonnegative and bounded above
  have hKnn : ∀ x y : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseFixB1S.boxW h μ u x y :=
    boxW_nonneg h hv μ u
  have hKwnn : 0 ≤ Kw := by
    have h1 := hKw 0 0
    have h2 := hKnn 0 0
    linarith
  -- geometry of the sliding box
  have hAmeas : MeasurableSet (Work.BoseFixB1S.boxA v μ u) :=
    Work.SmallBoxSliding.measurableSet_dlBox _ _ _
  have hAc : Work.BoseFixB1S.boxA v μ u ⊆
      Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) :=
    Work.SmallBoxSliding.dlBox_subset_acube _ _ _
  have hvolA : Work.BoseFixB1S.mfV v μ u =
      (MeasureTheory.volume (Work.BoseFixB1S.boxA v μ u)).toReal := by
    rw [Work.BoseFixB1S.mfV_def, Work.BoseFixB1S.boxA,
      Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  -- a bound for the state on the compact box
  obtain ⟨BΦ, hBΦ⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    (f := Φ) hΦc.continuousOn
  have hBΦ0 : 0 ≤ BΦ := le_trans (norm_nonneg _)
    (hBΦ 0 (Submission.BoseGases.zero_mem_abox hℓ.le))
  have hΦb : ∀ x ∈ Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      |Φ x| ≤ BΦ := fun x hx => by simpa [Real.norm_eq_abs] using hBΦ x hx
  -- the kernel vanishes as soon as one argument leaves the sliding box
  have hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    simp [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue]
  have hdpos : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := by
    show 0 < Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 6
    exact Work.BoseBox.fsXp_pos (mul_pos hμ (pow_pos hav 3))
  have hW0 : ∀ x y : EuclideanSpace ℝ (Fin 3),
      (x ∉ Work.BoseFixB1S.boxA v μ u ∨ y ∉ Work.BoseFixB1S.boxA v μ u) →
      Work.BoseFixB1S.boxW h μ u x y = 0 := by
    intro x y hxy
    have hz : ∀ a : EuclideanSpace ℝ (Fin 3), a ∉ Work.BoseFixB1S.boxA v μ u →
        Submission.BoseGases.chiSmallB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u a = 0 := by
      intro a ha
      by_contra hc
      exact ha (Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hdpos hc)
    rcases hxy with hx | hy
    · simp only [Work.BoseFixB1S.boxW, Submission.BoseGases.wSmallPair, hz x hx, zero_mul]
    · simp only [Work.BoseFixB1S.boxW, Submission.BoseGases.wSmallPair, hz y hy, mul_zero]
  -- the four functions of the row
  let sg : Submission.BoseGases.X n → ℝ := fun x =>
    Aind (Work.BoseFixB1S.boxA v μ u) (x p.1)
      * (Aind (Work.BoseFixB1S.boxA v μ u) (x p.2) * Φ x)
  let gg : Submission.BoseGases.X n → ℝ := fun x =>
    Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.1
      (Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.2 Φ) x
  let ee : Submission.BoseGases.X n → ℝ := fun x => sg x - gg x
  let K : Submission.BoseGases.X n → ℝ := fun x => Work.BoseFixB1S.boxW h μ u (x p.1) (x p.2)
  have hbox := Submission.BoseGases.abox_measurable n
    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
  have hsgm : Measurable sg := by
    show Measurable (fun x : Submission.BoseGases.X n =>
      Aind (Work.BoseFixB1S.boxA v μ u) (x p.1)
        * (Aind (Work.BoseFixB1S.boxA v μ u) (x p.2) * Φ x))
    exact (measurable_sigAt (Work.BoseFixB1S.boxA v μ u) hAmeas p.1).mul
      ((measurable_sigAt (Work.BoseFixB1S.boxA v μ u) hAmeas p.2).mul hΦc.measurable)
  have hggm : Measurable gg := by
    show Measurable (fun x : Submission.BoseGases.X n =>
      Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.1
        (Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u)
          p.2 Φ) x)
    exact measurable_boxPInd _ _ hAmeas p.1
      (measurable_boxPInd _ _ hAmeas p.2 hΦc.measurable)
  have heem : Measurable ee := by
    show Measurable (fun x : Submission.BoseGases.X n => sg x - gg x)
    exact hsgm.sub hggm
  have hsg2m : Measurable (fun x : Submission.BoseGases.X n => (sg x) ^ 2) := by fun_prop
  have hgg2m : Measurable (fun x : Submission.BoseGases.X n => (gg x) ^ 2) := by fun_prop
  have hee2m : Measurable (fun x : Submission.BoseGases.X n => (ee x) ^ 2) := by fun_prop
  have hgem : Measurable (fun x : Submission.BoseGases.X n => gg x * ee x) := by fun_prop
  have hbd_sg : ∀ x ∈ Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      |sg x| ≤ BΦ := by
    intro x hx
    show |Aind (Work.BoseFixB1S.boxA v μ u) (x p.1)
      * (Aind (Work.BoseFixB1S.boxA v μ u) (x p.2) * Φ x)| ≤ BΦ
    rw [abs_mul]
    calc |Aind (Work.BoseFixB1S.boxA v μ u) (x p.1)|
          * |Aind (Work.BoseFixB1S.boxA v μ u) (x p.2) * Φ x|
        ≤ 1 * |Φ x| := by
          refine mul_le_mul (Aind_abs_le_one _ (x p.1)) ?_ (abs_nonneg _) (by norm_num)
          rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (Aind_abs_le_one _ (x p.2))
      _ ≤ BΦ := by rw [one_mul]; exact hΦb x hx
  have hbd_gg : ∀ x ∈ Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      |gg x| ≤ BΦ := by
    intro x hx
    show |Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.1
      (Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u)
        p.2 Φ) x| ≤ BΦ
    exact abs_boxPInd_le hℓ hV hAmeas hvolA hAc p.1
      (abs_boxPInd_le hℓ hV hAmeas hvolA hAc p.2 hΦb) x hx
  have hbd_ee : ∀ x ∈ Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      |ee x| ≤ 2 * BΦ := by
    intro x hx
    show |sg x - gg x| ≤ 2 * BΦ
    have h1 := hbd_sg x hx
    have h2 := hbd_gg x hx
    calc |sg x - gg x| ≤ |sg x| + |gg x| := by
          simpa [sub_eq_add_neg] using abs_add_le (sg x) (-(gg x))
      _ ≤ BΦ + BΦ := by linarith
      _ = 2 * BΦ := by ring
  have aeb : ∀ {S : Submission.BoseGases.X n → ℝ} {C : ℝ},
      (∀ x ∈ Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        |S x| ≤ C) →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))), |S x| ≤ C :=
    fun hb => (MeasureTheory.ae_restrict_iff' hbox).mpr (Filter.Eventually.of_forall hb)
  -- integrability of the four weighted integrands
  have hint_sg : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n => (sg x) ^ 2 * K x)
      (MeasureTheory.volume.restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))) := by
    show MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n => (sg x) ^ 2 * Work.BoseFixB1S.boxW h μ u (x p.1) (x p.2))
      (MeasureTheory.volume.restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))
    exact integrableOn_boxW_slot (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      h hℓ rfl hij hWint hW0 (S := fun x => (sg x) ^ 2) hsg2m.aestronglyMeasurable
      (aeb (S := fun x => (sg x) ^ 2) (C := BΦ ^ 2) (fun x hx => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbd_sg x hx) 2))
  have hint_g2 : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n => (gg x) ^ 2 * K x)
      (MeasureTheory.volume.restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))) := by
    show MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n => (gg x) ^ 2 * Work.BoseFixB1S.boxW h μ u (x p.1) (x p.2))
      (MeasureTheory.volume.restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))
    exact integrableOn_boxW_slot (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      h hℓ rfl hij hWint hW0 (S := fun x => (gg x) ^ 2) hgg2m.aestronglyMeasurable
      (aeb (S := fun x => (gg x) ^ 2) (C := BΦ ^ 2) (fun x hx => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbd_gg x hx) 2))
  have hint_e2 : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n => (ee x) ^ 2 * K x)
      (MeasureTheory.volume.restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))) := by
    show MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n => (ee x) ^ 2 * Work.BoseFixB1S.boxW h μ u (x p.1) (x p.2))
      (MeasureTheory.volume.restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))
    exact integrableOn_boxW_slot (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      h hℓ rfl hij hWint hW0 (S := fun x => (ee x) ^ 2) hee2m.aestronglyMeasurable
      (aeb (S := fun x => (ee x) ^ 2) (C := (2 * BΦ) ^ 2) (fun x hx => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbd_ee x hx) 2))
  have hint_ge : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n => gg x * ee x * K x)
      (MeasureTheory.volume.restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))) := by
    show MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n => gg x * ee x * Work.BoseFixB1S.boxW h μ u (x p.1) (x p.2))
      (MeasureTheory.volume.restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))
    exact integrableOn_boxW_slot (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      h hℓ rfl hij hWint hW0 (S := fun x => gg x * ee x) hgem.aestronglyMeasurable
      (aeb (S := fun x => gg x * ee x) (C := BΦ * (2 * BΦ)) (fun x hx => by
        rw [abs_mul]
        exact mul_le_mul (hbd_gg x hx) (hbd_ee x hx) (abs_nonneg _) hBΦ0))
  have hint_e2u : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n => (ee x) ^ 2)
      (MeasureTheory.volume.restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))) :=
    integrableOn_sq_of_bound hℓ heem hbd_ee
  -- the unweighted two-slot defect bound
  have hdef : (∫ x, (ee x) ^ 2 ∂(MeasureTheory.volume.restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
      ≤ (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Work.UBBInputs8.boxQInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u)
              p.1 Φ x) ^ 2)
        + ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Work.UBBInputs8.boxQInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u)
              p.2 Φ x) ^ 2 := by
    have hd := boxDefect_le (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      hℓ hV hAmeas hvolA hAc hij hΦc
    have hcongr : (fun x : Submission.BoseGases.X n => (ee x) ^ 2)
        = fun x : Submission.BoseGases.X n =>
            (Aind (Work.BoseFixB1S.boxA v μ u) (x p.1)
                * (Aind (Work.BoseFixB1S.boxA v μ u) (x p.2) * Φ x)
              - Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u)
                  (Work.BoseFixB1S.boxA v μ u) p.1
                  (Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u)
                    (Work.BoseFixB1S.boxA v μ u) p.2 Φ) x) ^ 2 := by
      funext x
      show (sg x - gg x) ^ 2 = _
      rfl
    rw [hcongr]
    exact hd
  -- the abstract per-pair row
  exact manifest_row_core (ν := MeasureTheory.volume.restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))
    (sg := sg) (g := gg) (e := ee) (K := K)
    (q1 := ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        (Work.UBBInputs8.boxQInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u)
          p.1 Φ x) ^ 2)
    (q2 := ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        (Work.UBBInputs8.boxQInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u)
          p.2 Φ x) ^ 2)
    (Kw := Kw)
    (by intro x; show sg x = gg x + (sg x - gg x); ring)
    (by intro x; exact hKnn (x p.1) (x p.2))
    (by intro x; exact hKw (x p.1) (x p.2))
    hKwnn hint_sg hint_g2 hint_e2 hint_ge hint_e2u hdef

end Work.BoseFixB1S
