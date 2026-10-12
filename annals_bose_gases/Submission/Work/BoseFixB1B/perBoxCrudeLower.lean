import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.perBoxF_thick
import Submission.Work.BoseFixB1B.boxPIndPairFactor
import Submission.Work.BoseFixB1B.fibre_pair_joint
import Submission.Work.BoseFixB1S.integrableOn_phi_sq_indicator
import Submission.Work.BoseFixR.SlabCondensedHalf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

open MeasureTheory
open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false


/-! ## 1. The linear fibre bound for the localised one-body kernel

`|∫_y wSmall1Pair h M ℓ d u x y dy| ≤ K · a · χ_{B(u)}(x)`.

This is the *linear* (not quadratic) bound: `BoseFixB1/w1Fibre_chiB_sq_bounds_core` records
that the χ²-version is false.  The proof is the port of
`Work.UBBInputs8.A.exists_fibre_wSmall1Pair_le` to real-valued `d` (the auxiliary estimates
`abs_wSmall1Pair_chiB_le`, `abs_chiSmallB_le`, `abs_wSmallScaled_le` are all stated for
`d : ℝ`; only the wrapper was typed with `d : ℕ`). -/

theorem fibre_chiB_le_general {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hdR : R0 ≤ (ℓ * d) / 16) (hdRχ : R0 ≤ ℓ * chiR0) :
    ∀ (u x : EuclideanSpace ℝ (Fin 3)),
      |∫ y in acube ℓ, wSmall1Pair h M ℓ d u x y|
        ≤ (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * (chiSupAbs * chiSmallDecay M)
            * (∫ w : EuclideanSpace ℝ (Fin 3), |g0 v h w|))
          * chiSmallB M ℓ d u x := by
  set c₁ : ℝ := 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ with hc₁def
  set c₂ : ℝ := chiSupAbs * chiSmallDecay M with hc₂def
  set G : ℝ := ∫ w : EuclideanSpace ℝ (Fin 3), |g0 v h w| with hGdef
  have hc₁ : 0 ≤ c₁ := by
    rw [hc₁def]
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr (Work.SmallBoxSliding.smallConvLower_nonneg M))
  have hc₂ : 0 ≤ c₂ := by
    rw [hc₂def]; exact mul_nonneg chiSupAbs_nonneg (chiSmallDecay_nonneg M)
  have hG : 0 ≤ G := by rw [hGdef]; exact integral_nonneg (fun w => abs_nonneg (g0 v h w))
  intro u z
  set A : ℝ := chiSmallB M ℓ d u z with hAdef
  have hA : 0 ≤ A := by rw [hAdef]; exact chiSmallB_nonneg M ℓ d u z
  have hgi : Integrable (fun y : EuclideanSpace ℝ (Fin 3) => |g0 v h (z - y)|) :=
    (g0_integrable hR0 hv_supp h).abs.comp_sub_left z
  have hmaj : Integrable (fun y : EuclideanSpace ℝ (Fin 3) => c₁ * A * c₂ * |g0 v h (z - y)|) :=
    hgi.const_mul (c₁ * A * c₂)
  have hmajOn : IntegrableOn (fun y : EuclideanSpace ℝ (Fin 3) => c₁ * A * c₂ * |g0 v h (z - y)|) (acube ℓ) :=
    hmaj.integrableOn
  have hpt : ∀ y : EuclideanSpace ℝ (Fin 3), |wSmall1Pair h M ℓ d u z y| ≤ c₁ * A * c₂ * |g0 v h (z - y)| := by
    intro y
    have hD := Work.UBBInputs8.A.abs_wSmall1Pair_chiB_le (v := v) hv_supp hR0 h hM hℓ hd
      hdR hdRχ u z y
    have hyb : chiSmallB M ℓ d u y ≤ c₂ := by
      rw [hc₂def]
      have hb := Work.SmallBoxSliding.abs_chiSmallB_le (M := M) (ℓ := ℓ) (d := d) hM u y
      have h2 : chiSmall M ((ℓ * d)⁻¹ • y - u) ≤ chiSmallDecay M := by
        have h' := chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • y - u)
        rwa [abs_of_nonneg (chiSmall_nonneg M _)] at h'
      have hbnn : 0 ≤ chiSmallB M ℓ d u y := chiSmallB_nonneg M ℓ d u y
      rw [abs_of_nonneg hbnn] at hb
      calc chiSmallB M ℓ d u y ≤ chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • y - u) := hb
        _ ≤ chiSupAbs * chiSmallDecay M := mul_le_mul_of_nonneg_left h2 chiSupAbs_nonneg
    have hnn : 0 ≤ c₁ * A * |g0 v h (z - y)| :=
      mul_nonneg (mul_nonneg hc₁ hA) (abs_nonneg (g0 v h (z - y)))
    calc |wSmall1Pair h M ℓ d u z y| ≤ c₁ * A * |g0 v h (z - y)| * chiSmallB M ℓ d u y := by
          rw [hAdef, hc₁def]; exact hD
      _ ≤ c₁ * A * |g0 v h (z - y)| * c₂ := mul_le_mul_of_nonneg_left hyb hnn
      _ = c₁ * A * c₂ * |g0 v h (z - y)| := by ring
  have hstep1 : |∫ y in acube ℓ, wSmall1Pair h M ℓ d u z y| ≤
      ∫ y in acube ℓ, |wSmall1Pair h M ℓ d u z y| := by
    have hh := norm_integral_le_integral_norm
      (μ := volume.restrict (acube ℓ)) (f := fun y : EuclideanSpace ℝ (Fin 3) => wSmall1Pair h M ℓ d u z y)
    simpa only [Real.norm_eq_abs] using hh
  have hstep2 : ∫ y in acube ℓ, |wSmall1Pair h M ℓ d u z y| ≤
      ∫ y in acube ℓ, (c₁ * A * c₂ * |g0 v h (z - y)|) := by
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun y => abs_nonneg (wSmall1Pair h M ℓ d u z y))
    · exact hmajOn
    · filter_upwards with y
      exact hpt y
  have hstep3 : ∫ y in acube ℓ, (c₁ * A * c₂ * |g0 v h (z - y)|) =
      (c₁ * A * c₂) * (∫ y in acube ℓ, |g0 v h (z - y)|) := integral_const_mul _ _
  have hstep4 : ∫ y in acube ℓ, |g0 v h (z - y)| ≤ ∫ y : EuclideanSpace ℝ (Fin 3), |g0 v h (z - y)| :=
    setIntegral_le_integral hgi (ae_of_all _ (fun y => abs_nonneg (g0 v h (z - y))))
  have hstep5 : (∫ y : EuclideanSpace ℝ (Fin 3), |g0 v h (z - y)|) = G := by
    rw [hGdef]
    exact integral_sub_left_eq_self (fun w : EuclideanSpace ℝ (Fin 3) => |g0 v h w|) volume z
  calc |∫ y in acube ℓ, wSmall1Pair h M ℓ d u z y|
      ≤ ∫ y in acube ℓ, |wSmall1Pair h M ℓ d u z y| := hstep1
    _ ≤ ∫ y in acube ℓ, (c₁ * A * c₂ * |g0 v h (z - y)|) := hstep2
    _ = (c₁ * A * c₂) * (∫ y in acube ℓ, |g0 v h (z - y)|) := hstep3
    _ ≤ (c₁ * A * c₂) * (∫ y : EuclideanSpace ℝ (Fin 3), |g0 v h (z - y)|) :=
        mul_le_mul_of_nonneg_left hstep4 (mul_nonneg (mul_nonneg hc₁ hA) hc₂)
    _ = (c₁ * A * c₂) * G := by rw [hstep5]
    _ = (c₁ * c₂ * G) * A := by ring

/-- The fibre bound at FS's parameters, in the `∃ ε₀` form used by the chapter (the `ε₀` is
what supplies the regime hypotheses `R ≤ ℓd/16`, `R ≤ ℓ·chiR0` via
`Work.BoseFixB1.regime_sideAt_ge`). -/
theorem fibre_chiB_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (u x : EuclideanSpace ℝ (Fin 3)),
          |∫ y in acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              wSmall1Pair h
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x y|
            ≤ C * (_root_.BoseGases.a v)
                * chiSmallB
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x := by
  classical
  obtain ⟨ε₀, hε₀, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  set c : ℝ := 2 * (Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue)⁻¹
      * (chiSupAbs * chiSmallDecay Work.BoseBox.mValue)
      * (∫ w : EuclideanSpace ℝ (Fin 3), |g0 v h w|) with hcdef
  have hc0 : 0 ≤ c := by
    rw [hcdef]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num)
        (inv_nonneg.mpr (Work.SmallBoxSliding.smallConvLower_nonneg _)))
      (mul_nonneg chiSupAbs_nonneg (chiSmallDecay_nonneg _)))
      (integral_nonneg (fun w => abs_nonneg (g0 v h w)))
  refine ⟨ε₀, c / (_root_.BoseGases.a v), hε₀, div_nonneg hc0 (le_of_lt hav), ?_⟩
  intro μ hAdm
  obtain ⟨hR16, hRχ⟩ := hreg μ (Work.BoseFixB1.adm_mu_pos hAdm) (Work.BoseFixB1.adm_dilute hAdm)
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    norm_num [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue]
  have hMdef : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M = Work.BoseBox.mValue := rfl
  intro u x
  have hb := fibre_chiB_le_general (v := v) (h := h) (R0 := R) hv_supp hR
    (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) hM hℓ hd hR16 hRχ u x
  rw [hMdef] at hb
  rw [hMdef]
  have hae : c / (_root_.BoseGases.a v) * (_root_.BoseGases.a v) = c :=
    div_mul_cancel₀ c (ne_of_gt hav)
  calc |∫ y in acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        wSmall1Pair h Work.BoseBox.mValue
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x y|
      ≤ c * chiSmallB Work.BoseBox.mValue
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x := hb
    _ = c / (_root_.BoseGases.a v) * (_root_.BoseGases.a v)
          * chiSmallB Work.BoseBox.mValue
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x := by rw [hae]

/-! ## 2. The flat-part (`q0word`) identities at the box projections

The exact identities that the completion of squares for the flat parts rests on.  `P_i` is
FS's box projection `Work.UBBInputs8.boxPInd volA A i`,
`P_iΦ = volA⁻¹⟨1_A,Φ⟩·1_A(x_i)`; on the box `A` it is *constant in slot `i`*, so for the
kernel `w = wSmallPair M ℓ d u v` (supported in `A × A`, `A = dlBox ℓ d u`):

* one slot:  `∫_{abox}(P_iΦ)(x)² F(x_i) dx = (∫_A F/|A|)·‖P_iΦ‖²`   (pairs with the fibre bound);
* two slots: `∫_{abox}(P_iP_jΦ)(x)² w(x_i,x_j) dx = (∬_{A×A}w/|A|²)·‖P_iP_jΦ‖²`   (the mean-field
  term of the flat-part completion of squares).

These are the *first* lemmas of the `q0word` port; `Work.SmallBoxA0/PotSharp.lean`
(`q0word_sharp`) is the cube-kernel template, `Submission/PotWords.lean` the identity template.

**SKELETON** (the pair identity's proof is still open — the files under
`Submission/Work/BoseFixB1B/` are not in `Submission.lean`'s import cone). -/

/- (**Single-coordinate peeling** is proved in
`Submission/Work/BoseFixB1B/integral_abox_indep_mul_coord.lean` — imported at the top —
together with its measure-theoretic heart `peel_slot_pi`.) -/

/-- **Flat-part chemical identity** (`P_i` is constant in slot `i` on `A`):

    `∫_{abox}(P_iΦ)(x)² F(x_i) dx = (‖P_iΦ‖² / ∫_{acube}1_A) · (∫_{acube}1_A·F)`,

Proof route: `(P_iΦ)(x)² = (volA⁻¹∫_AΦ(x_{i←·}))²·1_A(x_i)`, the factor `c(x_{≠i})²` does not
depend on `x_i`, and `∫_{abox}` factorises over the slot `i` (the corpus's
`Submission.BoseGases.restrict_abox_eq_pi` / `integral_abox_comp_apply` are the tools). -/
theorem boxPInd_sq_mul_comp {N : ℕ} {L : ℝ} (hL : 0 < L) {A : Set ℝ³} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube L) {volA : ℝ} (hvol : volA ≠ 0) (i : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} {F : ℝ³ → ℝ}
    (hInt1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        ((1 / volA) * (∫ z in A, Φ (Function.update x i z))) ^ 2
          * (A.indicator (fun _ => (1 : ℝ)) (x i) * F (x i)))
      (Submission.BoseGases.abox N L))
    (hInt2 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        ((1 / volA) * (∫ z in A, Φ (Function.update x i z))) ^ 2)
      (Submission.BoseGases.abox N L))
    (hInt3 : MeasureTheory.IntegrableOn (fun a : ℝ³ => A.indicator (fun _ => (1 : ℝ)) a * F a)
      (Submission.BoseGases.acube L))
    (hInt4 : MeasureTheory.IntegrableOn (A.indicator (fun _ => (1 : ℝ)))
      (Submission.BoseGases.acube L))
    (hInt5 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        ((1 / volA) * (∫ z in A, Φ (Function.update x i z))) ^ 2
          * A.indicator (fun _ => (1 : ℝ)) (x i))
      (Submission.BoseGases.abox N L))
    (hApos : 0 < ∫ a in Submission.BoseGases.acube L, A.indicator (fun _ => (1 : ℝ)) a) :
    ∫ x in Submission.BoseGases.abox N L,
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * F (x i)
      = ((∫ x in Submission.BoseGases.abox N L,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
            / (∫ a in Submission.BoseGases.acube L, A.indicator (fun _ => (1 : ℝ)) a))
          * (∫ a in Submission.BoseGases.acube L, A.indicator (fun _ => (1 : ℝ)) a * F a) := by
  classical
  -- the slot-`i`-independent factor
  set c : Submission.BoseGases.X N → ℝ :=
    fun x => (1 / volA) * ∫ z in A, Φ (Function.update x i z) with hc
  have hbox : ∀ x : Submission.BoseGases.X N,
      Work.UBBInputs8.boxPInd volA A i Φ x = c x * A.indicator (fun _ => (1 : ℝ)) (x i) := by
    intro x; rfl
  have hind : ∀ a : ℝ³,
      A.indicator (fun _ => (1 : ℝ)) a ^ 2 = A.indicator (fun _ => (1 : ℝ)) a := by
    intro a
    by_cases ha : a ∈ A
    · rw [Set.indicator_of_mem ha]; norm_num
    · rw [Set.indicator_of_notMem ha]; norm_num
  have hupd : ∀ (x : Submission.BoseGases.X N) (a z : ℝ³),
      Function.update (Function.update x i a) i z = Function.update x i z := by
    intro x a z
    funext j
    simp only [Function.update_apply]
    by_cases hj : j = i <;> simp [hj]
  have hcindep : ∀ (x : Submission.BoseGases.X N) (a : ℝ³), c (Function.update x i a) = c x := by
    intro x a
    simp only [hc]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall (fun z => congrArg Φ (hupd x a z)))
  have hpt : ∀ x : Submission.BoseGases.X N,
      (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * F (x i)
        = c x ^ 2 * (A.indicator (fun _ => (1 : ℝ)) (x i) * F (x i)) := by
    intro x
    rw [hbox x, mul_pow, hind (x i)]
    ring
  have hpt2 : ∀ x : Submission.BoseGases.X N,
      (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
        = c x ^ 2 * A.indicator (fun _ => (1 : ℝ)) (x i) := by
    intro x
    rw [hbox x, mul_pow, hind (x i)]
  -- integrability in the `c`-normal form
  have hI1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      c x ^ 2 * (A.indicator (fun _ => (1 : ℝ)) (x i) * F (x i)))
      (Submission.BoseGases.abox N L) := by
    simpa only [hc] using hInt1
  have hI2 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => c x ^ 2)
      (Submission.BoseGases.abox N L) := by
    simpa only [hc] using hInt2
  have hI5 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      c x ^ 2 * A.indicator (fun _ => (1 : ℝ)) (x i)) (Submission.BoseGases.abox N L) := by
    simpa only [hc] using hInt5
  -- the two peels
  have peel1 := Work.BoseFixB1B.integral_abox_indep_mul_coord (ℓ := L) hL i
    (g := fun x : Submission.BoseGases.X N => c x ^ 2)
    (h := fun a : ℝ³ => A.indicator (fun _ => (1 : ℝ)) a * F a)
    (fun x a => by rw [hcindep x a]) hI1 hI2 hInt3
  have peel2 := Work.BoseFixB1B.integral_abox_indep_mul_coord (ℓ := L) hL i
    (g := fun x : Submission.BoseGases.X N => c x ^ 2)
    (h := fun a : ℝ³ => A.indicator (fun _ => (1 : ℝ)) a)
    (fun x a => by rw [hcindep x a]) hI5 hI2 hInt4
  have hnorm : ∫ x in Submission.BoseGases.abox N L,
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
      = ((∫ x in Submission.BoseGases.abox N L, c x ^ 2) / L ^ 3)
          * (∫ a in Submission.BoseGases.acube L, A.indicator (fun _ => (1 : ℝ)) a) := by
    have h1 : (fun x : Submission.BoseGases.X N => (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
        = fun x => c x ^ 2 * A.indicator (fun _ => (1 : ℝ)) (x i) := funext (fun x => hpt2 x)
    rw [h1]
    exact peel2
  have hnum : ∫ x in Submission.BoseGases.abox N L,
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * F (x i)
      = ((∫ x in Submission.BoseGases.abox N L, c x ^ 2) / L ^ 3)
          * (∫ a in Submission.BoseGases.acube L, A.indicator (fun _ => (1 : ℝ)) a * F a) := by
    have h1 : (fun x : Submission.BoseGases.X N =>
          (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * F (x i))
        = fun x => c x ^ 2 * (A.indicator (fun _ => (1 : ℝ)) (x i) * F (x i)) := funext (fun x => hpt x)
    rw [h1]
    exact peel1
  rw [hnum, hnorm]
  have hAne : (∫ a in Submission.BoseGases.acube L, A.indicator (fun _ => (1 : ℝ)) a) ≠ 0 :=
    ne_of_gt hApos
  rw [mul_div_cancel_right₀ _ hAne]

/-- **Flat-part pair identity** (the mean-field term): for distinct slots and a kernel supported
in `A × A`,

    `∫_{abox}(P_iP_jΦ)(x)² w(x_i,x_j) dx = (∬_{A×A}w / |A|²) · ‖P_iP_jΦ‖²`.

Proof route: `P_iP_jΦ` is constant in the two slots on `A` (the double mean of `Φ` over `A²`
times `1_A(x_i)1_A(x_j)`), and `∫_{abox}` factorises over the two slots against the kernel
(`aboxFubini`-style product decomposition of `X N`; the localised kernels
`wSmallPair M ℓ d u v` are supported in `dlBox ℓ d u × dlBox ℓ d u`). -/
theorem boxPInd_pair_factor {N : ℕ} {L : ℝ} (hL : 0 < L) {A : Set ℝ³} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube L) {volA : ℝ} (hvol : volA ≠ 0)
    {i j : Fin N} (hij : i ≠ j) {Φ : Submission.BoseGases.X N → ℝ} {w : ℝ³ → ℝ³ → ℝ}
    (hInt1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (((1 / volA) * ((1 / volA) * ∫ z in A, ∫ z' in A,
            Φ (Function.update (Function.update x i z) j z')))) ^ 2
          * (A.indicator (fun _ => (1 : ℝ)) (x i)
              * (A.indicator (fun _ => (1 : ℝ)) (x j) * w (x i) (x j))))
      (Submission.BoseGases.abox N L))
    (hInt2 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (((1 / volA) * ((1 / volA) * ∫ z in A, ∫ z' in A,
            Φ (Function.update (Function.update x i z) j z')))) ^ 2)
      (Submission.BoseGases.abox N L))
    (hInt3 : MeasureTheory.IntegrableOn (fun p : ℝ³ × ℝ³ =>
        A.indicator (fun _ => (1 : ℝ)) p.1
          * (A.indicator (fun _ => (1 : ℝ)) p.2 * w p.1 p.2))
      (Submission.BoseGases.acube L ×ˢ Submission.BoseGases.acube L))
    (hInt4 : MeasureTheory.IntegrableOn (fun p : ℝ³ × ℝ³ =>
        A.indicator (fun _ => (1 : ℝ)) p.1 * A.indicator (fun _ => (1 : ℝ)) p.2)
      (Submission.BoseGases.acube L ×ˢ Submission.BoseGases.acube L))
    (hInt5 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (((1 / volA) * ((1 / volA) * ∫ z in A, ∫ z' in A,
            Φ (Function.update (Function.update x i z) j z')))) ^ 2
          * (A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j)))
      (Submission.BoseGases.abox N L))
    (hApos : 0 < ∫ p in Submission.BoseGases.acube L ×ˢ Submission.BoseGases.acube L,
        A.indicator (fun _ => (1 : ℝ)) p.1 * A.indicator (fun _ => (1 : ℝ)) p.2) :
    ∫ x in Submission.BoseGases.abox N L,
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2
          * w (x i) (x j)
      = ((∫ x in Submission.BoseGases.abox N L,
              (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2)
            / (∫ p in Submission.BoseGases.acube L ×ˢ Submission.BoseGases.acube L,
                A.indicator (fun _ => (1 : ℝ)) p.1 * A.indicator (fun _ => (1 : ℝ)) p.2))
          * (∫ p in Submission.BoseGases.acube L ×ˢ Submission.BoseGases.acube L,
              A.indicator (fun _ => (1 : ℝ)) p.1
                * (A.indicator (fun _ => (1 : ℝ)) p.2 * w p.1 p.2)) := by
  -- Mirror of the one-slot proof (`boxPInd_sq_mul_comp`), with the two-slot peel
  -- `Work.BoseFixB1B.integral_abox_indep_mul_two_coords` in place of the one-slot peel.
  -- The normalisation is `volA⁻²`, not `volA⁻¹`: writing the inner projection as
  -- `boxPInd volA A j Φ y = volA⁻¹(∫_{z'∈A}Φ(update y j z'))·1_A(y j)` and substituting
  -- `y = update x i z` (so `y j = x j`, `j ≠ i`), the `z`-average of the inner `volA⁻¹` gives
  --     `boxPInd volA A i (boxPInd volA A j Φ) x
  --        = c x · (1_A(x_j)·1_A(x_i))`,   `c := volA⁻¹·(volA⁻¹·∫_A∫_A Φ(update (update x i z) j z'))`
  -- (constant pull-out `integral_const_mul`/`integral_mul_const`).  Then `c` is independent of
  -- both slots (`update (update x i z) j z' = update (update x j z') i z` for `i ≠ j`, plus the
  -- `z`-inner `i`-independence), `1_A² = 1_A`, and the two peels
  -- `(c², 1_A(·)·(1_A(·)·w · ·))` and `(c², 1_A(·)·1_A(·))` finish it by
  -- `mul_div_cancel_right₀` (the `|A|²`-cancellation is again a plain division).
  -- The abstract two-slot identity is proved in
  -- `Submission/Work/BoseFixB1B/boxPIndPairFactor.lean` (module imported above).
  exact Work.BoseFixB1B.boxPIndPairFactor hL hA hAc hvol hij
    hInt1 hInt2 hInt3 hInt4 hInt5 hApos

/-! ## 2b. The set-integral conversion of §10 Slot 1

`∫_{acube L} 1_A · F = ∫_A F` for a measurable `A ⊆ acube L` — the wiring that converts the
acube-indicator form of the two flat-part identities into the `∫_A F` / `|A|` form.  Purely
`setIntegral_indicator`; no integrability hypothesis is needed. -/

theorem setIntegral_indicator_acube {L : ℝ} {A : Set ℝ³} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube L) {F : ℝ³ → ℝ} :
    ∫ a in Submission.BoseGases.acube L, A.indicator (fun _ => (1 : ℝ)) a * F a
      = ∫ a in A, F a := by
  have h1 : (fun a : ℝ³ => A.indicator (fun _ => (1 : ℝ)) a * F a) = A.indicator F := by
    funext a
    by_cases ha : a ∈ A
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha, one_mul]
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha, zero_mul]
  rw [h1, MeasureTheory.setIntegral_indicator hA, Set.inter_eq_right.mpr hAc]

/-- **Slot 1 wiring** (§10): the flat-part chemical identity in the `∫_A F` / `|A|` form the
assembly consumes, obtained from `boxPInd_sq_mul_comp` (acube-indicator form) by the set-integral
conversion `setIntegral_indicator_acube`. -/
theorem boxPIndSqMulCompA {N : ℕ} {L : ℝ} (hL : 0 < L) {A : Set ℝ³} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube L) {volA : ℝ} (hvol : volA ≠ 0) (i : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} {F : ℝ³ → ℝ}
    (hInt1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        ((1 / volA) * (∫ z in A, Φ (Function.update x i z))) ^ 2
          * (A.indicator (fun _ => (1 : ℝ)) (x i) * F (x i)))
      (Submission.BoseGases.abox N L))
    (hInt2 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        ((1 / volA) * (∫ z in A, Φ (Function.update x i z))) ^ 2)
      (Submission.BoseGases.abox N L))
    (hInt3 : MeasureTheory.IntegrableOn
      (fun a : ℝ³ => A.indicator (fun _ => (1 : ℝ)) a * F a) (Submission.BoseGases.acube L))
    (hInt4 : MeasureTheory.IntegrableOn (A.indicator (fun _ => (1 : ℝ)))
      (Submission.BoseGases.acube L))
    (hInt5 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        ((1 / volA) * (∫ z in A, Φ (Function.update x i z))) ^ 2
          * A.indicator (fun _ => (1 : ℝ)) (x i))
      (Submission.BoseGases.abox N L))
    (hApos : 0 < ∫ a in Submission.BoseGases.acube L, A.indicator (fun _ => (1 : ℝ)) a) :
    ∫ x in Submission.BoseGases.abox N L,
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * F (x i)
      = ((∫ x in Submission.BoseGases.abox N L,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
            / (∫ a in A, (1 : ℝ)))
          * (∫ z in A, F z) := by
  rw [boxPInd_sq_mul_comp hL hA hAc hvol i hInt1 hInt2 hInt3 hInt4 hInt5 hApos]
  have h1 : (∫ a in Submission.BoseGases.acube L,
        A.indicator (fun _ => (1 : ℝ)) a * F a) = ∫ z in A, F z :=
    setIntegral_indicator_acube (L := L) hA hAc (F := F)
  have h2 : (∫ a in Submission.BoseGases.acube L, A.indicator (fun _ => (1 : ℝ)) a)
      = ∫ a in A, (1 : ℝ) := by
    simpa using setIntegral_indicator_acube (L := L) hA hAc (F := fun _ => (1 : ℝ))
  rw [h1, h2]

/-- **Slot 2 wiring** (§10): the flat-part pair identity in the `∬_{A×A}w` / `|A|²` form.
Both RHS integrals are converted from the acube-product form by the vanish-off-`A×A`
congruence: the integrands already carry the `1_A⊗1_A` factor, so each is `(A×ˢA).indicator …`,
and `MeasureTheory.setIntegral_indicator (hA.prod hA)` plus
`(A×ˢA) ∩ (acube L ×ˢ acube L) = A×ˢA` closes it. -/
theorem boxPIndPairFactorA {N : ℕ} {L : ℝ} (hL : 0 < L) {A : Set ℝ³} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube L) {volA : ℝ} (hvol : volA ≠ 0)
    {i j : Fin N} (hij : i ≠ j) {Φ : Submission.BoseGases.X N → ℝ} {w : ℝ³ → ℝ³ → ℝ}
    (hInt1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (((1 / volA) * ((1 / volA) * ∫ z in A, ∫ z' in A,
            Φ (Function.update (Function.update x i z) j z')))) ^ 2
          * (A.indicator (fun _ => (1 : ℝ)) (x i)
              * (A.indicator (fun _ => (1 : ℝ)) (x j) * w (x i) (x j))))
      (Submission.BoseGases.abox N L))
    (hInt2 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (((1 / volA) * ((1 / volA) * ∫ z in A, ∫ z' in A,
            Φ (Function.update (Function.update x i z) j z')))) ^ 2)
      (Submission.BoseGases.abox N L))
    (hInt3 : MeasureTheory.IntegrableOn (fun p : ℝ³ × ℝ³ =>
        A.indicator (fun _ => (1 : ℝ)) p.1
          * (A.indicator (fun _ => (1 : ℝ)) p.2 * w p.1 p.2))
      (Submission.BoseGases.acube L ×ˢ Submission.BoseGases.acube L))
    (hInt4 : MeasureTheory.IntegrableOn (fun p : ℝ³ × ℝ³ =>
        A.indicator (fun _ => (1 : ℝ)) p.1 * A.indicator (fun _ => (1 : ℝ)) p.2)
      (Submission.BoseGases.acube L ×ˢ Submission.BoseGases.acube L))
    (hInt5 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (((1 / volA) * ((1 / volA) * ∫ z in A, ∫ z' in A,
            Φ (Function.update (Function.update x i z) j z')))) ^ 2
          * (A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j)))
      (Submission.BoseGases.abox N L))
    (hApos : 0 < ∫ p in Submission.BoseGases.acube L ×ˢ Submission.BoseGases.acube L,
        A.indicator (fun _ => (1 : ℝ)) p.1 * A.indicator (fun _ => (1 : ℝ)) p.2) :
    ∫ x in Submission.BoseGases.abox N L,
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2
          * w (x i) (x j)
      = ((∫ x in Submission.BoseGases.abox N L,
              (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2)
            / ((∫ p in A ×ˢ A, (1 : ℝ))))
          * (∫ p in A ×ˢ A, w p.1 p.2) := by
  rw [boxPInd_pair_factor hL hA hAc hvol hij hInt1 hInt2 hInt3 hInt4 hInt5 hApos]
  have hsub : A ×ˢ A ⊆ Submission.BoseGases.acube L ×ˢ Submission.BoseGases.acube L :=
    Set.prod_mono hAc hAc
  have hw : (∫ p in Submission.BoseGases.acube L ×ˢ Submission.BoseGases.acube L,
        A.indicator (fun _ => (1 : ℝ)) p.1 * (A.indicator (fun _ => (1 : ℝ)) p.2 * w p.1 p.2))
      = ∫ p in A ×ˢ A, w p.1 p.2 := by
    have hpt : (fun p : ℝ³ × ℝ³ => A.indicator (fun _ => (1 : ℝ)) p.1
          * (A.indicator (fun _ => (1 : ℝ)) p.2 * w p.1 p.2))
        = fun p : ℝ³ × ℝ³ => (A ×ˢ A).indicator (fun q => w q.1 q.2) p := by
      funext p
      by_cases hp : p ∈ A ×ˢ A
      · have h1 : p.1 ∈ A := (Set.mem_prod.mp hp).1
        have h2 : p.2 ∈ A := (Set.mem_prod.mp hp).2
        simp [h1, h2, hp]
      · rw [Set.indicator_of_notMem hp]
        by_cases h1 : p.1 ∈ A
        · have h2 : p.2 ∉ A := fun h2 => hp (Set.mem_prod.mpr ⟨h1, h2⟩)
          simp [h2]
        · simp [h1]
    rw [hpt, MeasureTheory.setIntegral_indicator (hA.prod hA), Set.inter_eq_right.mpr hsub]
  have hc : (∫ p in Submission.BoseGases.acube L ×ˢ Submission.BoseGases.acube L,
        A.indicator (fun _ => (1 : ℝ)) p.1 * A.indicator (fun _ => (1 : ℝ)) p.2)
      = ∫ p in A ×ˢ A, (1 : ℝ) := by
    have hpt : (fun p : ℝ³ × ℝ³ => A.indicator (fun _ => (1 : ℝ)) p.1
          * A.indicator (fun _ => (1 : ℝ)) p.2)
        = fun p : ℝ³ × ℝ³ => (A ×ˢ A).indicator (fun _ => (1 : ℝ)) p := by
      funext p
      by_cases hp : p ∈ A ×ˢ A
      · have h1 : p.1 ∈ A := (Set.mem_prod.mp hp).1
        have h2 : p.2 ∈ A := (Set.mem_prod.mp hp).2
        simp [h1, h2, hp]
      · rw [Set.indicator_of_notMem hp]
        by_cases h1 : p.1 ∈ A
        · have h2 : p.2 ∉ A := fun h2 => hp (Set.mem_prod.mpr ⟨h1, h2⟩)
          simp [h2]
        · simp [h1]
    rw [hpt, MeasureTheory.setIntegral_indicator (hA.prod hA), Set.inter_eq_right.mpr hsub]
  rw [hw, hc]

/-! ## 3. The elementary arms of the crude per-box bound

The crude bound is assembled from three pieces, all at FS's parameters `ℓ = sideAt μ (a v)`,
`d = (paramsAt μ (a v)).d`, `M = (paramsAt μ (a v)).M = mValue`, `B = dlBox ℓ d u`:

* the **low-occupancy arm** (`lowArm`): below the threshold `K(μ·chiMass + 1)‖Φ‖²` the
  *integrated* fibre bound `fibSum ≤ K_av·(a v)·(χ-count)` (`Work.BoseFixB1.fibSum_le`)
  turns the chemical-potential line of `sbPot` into the allowance;
* the **excited arm** (`excitedArm`): if the box-indicator count of `B(u)` is at most twice the
  excited count `n₊`, the *definitional* gap payment `sbKin ≥ c'²μ(a v)n₊`
  (`Work.BoseFixB1.sbKin_ge_mu_av_cnPlus`, with `c'` as large as we like via
  `gapRegime_of_adm`) pays the fibre line, and `sbWord ≥ 0`;
* the **condensed arm** (`Work.BoseFixR.SlabCondensedHalf`, the paper's `lm:appinteractionestimate`
  at the sliding box): if `½·cnt ≤ n₀` and the occupancy is above the threshold, the
  flat-part completion of squares pays.

All three rest on the *proved* decomposition `sbPot = −μ·fibSum + pairSum`
(`Work.BoseFixB1.sbPot_split`, `Work.BoseFixB1.pairSum_nonneg`) and on the count identity
`cnt = n₀ + n₊` (`Work.BoseFixR.SlabCountSplit`). -/

/-- The constant of the integrated fibre bound `fibSum ≤ K_av · (a v) · χ-count`
(`Work.BoseFixB1.fibSum_le`), at FS's `M = mValue`. -/
noncomputable def kav : ℝ :=
  16 * Real.pi * chiSupAbs * chiSmallDecay Work.BoseBox.mValue
    / Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue

/-- `Cs M = chiSupAbs·chiSmallDecay M`, a uniform bound for `χ_{B(u)}`. -/
noncomputable def chiCs (M : ℕ) : ℝ := chiSupAbs * chiSmallDecay M

theorem kav_nonneg : 0 ≤ kav := by
  rw [kav]
  refine div_nonneg ?_ (le_of_lt (Work.SmallBoxSliding.smallConvLower_pos Work.BoseBox.mValue))
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 16) Real.pi_nonneg) chiSupAbs_nonneg)
    (chiSmallDecay_nonneg Work.BoseBox.mValue)

theorem chiCs_nonneg (M : ℕ) : 0 ≤ chiCs M := by
  rw [chiCs]
  exact mul_nonneg chiSupAbs_nonneg (chiSmallDecay_nonneg M)

/-- The cutoff `χ_{B(u)}` is dominated by its own box indicator. -/
theorem chiSmallB_le_indicator {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u z : EuclideanSpace ℝ (Fin 3)) :
    chiSmallB M ℓ d u z ≤ chiCs M * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) z := by
  rw [chiCs]
  by_cases hz : z ∈ dlBox ℓ d u
  · rw [Set.indicator_of_mem hz, mul_one]
    exact Work.BoseFixB1.chiSmallB_le_Cs hM u z
  · rw [Set.indicator_of_notMem hz, mul_zero]
    by_contra hcon
    exact hz (Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd
      (ne_of_gt (lt_of_not_ge hcon)))

/-- **The χ-count is dominated by the box-indicator count.**  Integrating the pointwise
domination `χ_{B(u)} ≤ Cs·1_{B(u)}`. -/
theorem chiSum_le_countCs {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) :
    Work.BoseFixB1.chiSum M ℓ d u Φ
      ≤ chiCs M * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)) := by
  classical
  set B : Set (EuclideanSpace ℝ (Fin 3)) := Submission.BoseGases.dlBox ℓ d u with hB
  have hBmeas : MeasurableSet B := by
    rw [hB]
    exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hBac : B ⊆ Submission.BoseGases.acube ℓ := by
    rw [hB]
    exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hsign : ∀ z : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.chiSmallB M ℓ d u z
        ≤ chiCs M * B.indicator (fun _ => (1 : ℝ)) z := by
    intro z
    rw [hB]
    exact chiSmallB_le_indicator hM hℓ hd u z
  have hstep : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        ∑ i : Fin n, chiCs M * B.indicator (fun _ => (1 : ℝ)) (x i) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _)
        (Finset.sum_nonneg fun i _ => Submission.BoseGases.chiSmallB_nonneg M ℓ d u (x i)))
      ?_ (Filter.Eventually.of_forall fun x => mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ => hsign (x i)) (sq_nonneg _))
    have hbase : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
        (Submission.BoseGases.abox n ℓ) (MeasureTheory.volume) :=
      Submission.BoseGases.integrableOn_abox_of_continuous hℓ (hΦc.pow 2)
    refine MeasureTheory.Integrable.mono' (hbase.const_mul ((n : ℝ) * chiCs M)) ?_ ?_
    · have hpt2 : (fun x : Submission.BoseGases.X n =>
          (Φ x) ^ 2 * ∑ i : Fin n, chiCs M * B.indicator (fun _ => (1 : ℝ)) (x i))
          = fun x : Submission.BoseGases.X n => ∑ i : Fin n,
              (Φ x) ^ 2 * (chiCs M * B.indicator (fun _ => (1 : ℝ)) (x i)) := by
        funext x
        rw [Finset.mul_sum]
      have hint : MeasureTheory.Integrable (fun a : Submission.BoseGases.X n =>
          ∑ i : Fin n, (Φ a) ^ 2 * (chiCs M * B.indicator (fun _ => (1 : ℝ)) (a i)))
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ)) :=
        integrable_finsetSum (s := Finset.univ)
          (f := fun i (x : Submission.BoseGases.X n) =>
            (Φ x) ^ 2 * (chiCs M * B.indicator (fun _ => (1 : ℝ)) (x i)))
          (fun i _ => Work.BoseFixB1S.integrableOn_phi_sq_indicator (c := chiCs M)
            hℓ hBmeas hBac i hΦc)
      rw [hpt2]
      exact hint.aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (Φ x))]
      have hbd : ∑ i : Fin n, chiCs M * B.indicator (fun _ => (1 : ℝ)) (x i)
          ≤ (n : ℝ) * chiCs M := by
        calc ∑ i : Fin n, chiCs M * B.indicator (fun _ => (1 : ℝ)) (x i)
            ≤ ∑ i : Fin n, chiCs M * 1 :=
              Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by
                by_cases hz : x i ∈ B
                · rw [Set.indicator_of_mem hz]
                · rw [Set.indicator_of_notMem hz]
                  norm_num) (chiCs_nonneg M)
          _ = (n : ℝ) * chiCs M := by simp
      have hnn : 0 ≤ ∑ i : Fin n, chiCs M * B.indicator (fun _ => (1 : ℝ)) (x i) :=
        Finset.sum_nonneg fun i _ => mul_nonneg (chiCs_nonneg M)
          (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      rw [abs_of_nonneg hnn]
      calc (Φ x) ^ 2 * (∑ i : Fin n, chiCs M * B.indicator (fun _ => (1 : ℝ)) (x i))
          ≤ (Φ x) ^ 2 * ((n : ℝ) * chiCs M) := mul_le_mul_of_nonneg_left hbd (sq_nonneg _)
        _ = (n : ℝ) * chiCs M * (Φ x) ^ 2 := by ring
  calc Work.BoseFixB1.chiSum M ℓ d u Φ
      = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
          ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) := rfl
    _ ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
          ∑ i : Fin n, chiCs M * B.indicator (fun _ => (1 : ℝ)) (x i) := hstep
    _ = chiCs M * ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * B.indicator (fun _ => (1 : ℝ)) (x i) := by
        have hpt : ∀ x : Submission.BoseGases.X n,
            (Φ x) ^ 2 * ∑ i : Fin n, chiCs M * B.indicator (fun _ => (1 : ℝ)) (x i)
              = chiCs M * ((Φ x) ^ 2 *
                  ∑ i : Fin n, B.indicator (fun _ => (1 : ℝ)) (x i)) := by
          intro x
          rw [Finset.mul_sum]
          conv_rhs => rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
          MeasureTheory.integral_const_mul]
        congr 1
        have h1 := MeasureTheory.integral_finset_sum
          (μ := (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ))
          (s := Finset.univ)
          (f := fun i (x : Submission.BoseGases.X n) =>
            (Φ x) ^ 2 * B.indicator (fun _ => (1 : ℝ)) (x i))
          (fun i _ => by
            simpa only [MeasureTheory.IntegrableOn, one_mul] using
              Work.BoseFixB1S.integrableOn_phi_sq_indicator (c := 1) hℓ hBmeas hBac i hΦc)
        simpa [Finset.mul_sum] using h1

/-- **The core inequality**: `sbWord ≥ c'²μ(a v)·n₊ − K_av·μ(a v)·(χ-count)`. -/
theorem sbCore {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (c' : ℝ) (hc' : 0 ≤ c') :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          c' ^ 2 * μ * (_root_.BoseGases.a v)
              * Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                  (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                  (Φ : Submission.BoseGases.X n → ℝ)
            - μ * kav * (_root_.BoseGases.a v)
              * Work.BoseFixB1.chiSum (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                  (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  classical
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  obtain ⟨εg, hεg, hgap⟩ := Work.BoseFixB1.gapRegime_of_adm (v := v) hav (c' := c') hc'
  refine ⟨min εr εg, lt_min hεr hεg, ?_⟩
  intro μ hAdm n Φ u
  have hAdmr : Work.BoseBoxFix.Adm v εr μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmg : Work.BoseBoxFix.Adm v εg μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have ha : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  have hMv : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M = Work.BoseBox.mValue :=
    Work.BoseFixB1.M_eq_mValue μ (_root_.BoseGases.a v)
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  obtain ⟨hR16, hRχ⟩ := hreg μ hμ (Work.BoseFixB1.adm_dilute hAdmr)
  have hsplit := Work.BoseFixB1.sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1
    hAdm hΦc u hR16 hRχ
  have hgap' : c' ^ 2 * μ * (_root_.BoseGases.a v)
      * Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          (Φ : Submission.BoseGases.X n → ℝ)
      ≤ Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
          (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseFixB1.sbKin_ge_mu_av_cnPlus (v := v) (M := (Work.BoseBox.paramsAt μ
        (_root_.BoseGases.a v)).M) (u := u) (Φ := (Φ : Submission.BoseGases.X n → ℝ))
      (c' := c') ha hμ.le hc' (mul_pos hd hℓ) (Work.BoseFixB1.adm_eT_pos hAdm)
      (hgap μ hAdmg) (Work.BoseFixB1.tBwordKinInd_nonneg _)
  have hfib : Work.BoseFixB1.fibSum h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)
      ≤ kav * (_root_.BoseGases.a v)
        * Work.BoseFixB1.chiSum (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          (Φ : Submission.BoseGases.X n → ℝ) := by
    have h0 := Work.BoseFixB1.fibSum_le (v := v) (h := h) hv hvrad hR hv_supp hM hℓ hd hR16 hRχ
      u hΦc
    have hk : (16 * Real.pi * chiSupAbs * chiSmallDecay (Work.BoseBox.paramsAt μ
          (_root_.BoseGases.a v)).M / Work.SmallBoxSliding.smallConvLower
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) = kav := by
      rw [kav, hMv]
    rw [hk] at h0
    exact h0
  have hpair : 0 ≤ Work.BoseFixB1.pairSum v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseFixB1.pairSum_nonneg (v := v) hv (M := (Work.BoseBox.paramsAt μ
      (_root_.BoseGases.a v)).M) (u := u) (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
      (Φ : Submission.BoseGases.X n → ℝ)
  rw [Work.BoseFixB1.sbWord, hsplit]
  nlinarith [hgap', mul_le_mul_of_nonneg_left hfib hμ.le, hpair]

/-- **The excited arm.**  If the box-indicator count of `B(u)` is at most twice the excited
count `n₊`, then `sbWord ≥ 0 ≥ −C(…)‖Φ‖²`. -/
theorem excitedArm {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          (1 / 2 : ℝ) * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u).indicator
                  (fun _ => (1 : ℝ)) (x i))
            ≤ Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Φ : Submission.BoseGases.X n → ℝ) →
          0 ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  classical
  set c' : ℝ := Real.sqrt (2 * kav * chiCs Work.BoseBox.mValue + 1) with hc'def
  have hc'0 : 0 ≤ c' := Real.sqrt_nonneg _
  have harg : 0 ≤ 2 * kav * chiCs Work.BoseBox.mValue + 1 := by
    have h1 : 0 ≤ 2 * kav * chiCs Work.BoseBox.mValue :=
      mul_nonneg (mul_nonneg (by norm_num) kav_nonneg) (chiCs_nonneg _)
    linarith
  have hc'2 : c' ^ 2 = 2 * kav * chiCs Work.BoseBox.mValue + 1 := Real.sq_sqrt harg
  obtain ⟨ε₀, hε₀, hcore⟩ := sbCore (v := v) h hv hv1 hvrad hR hv_supp hav c' hc'0
  refine ⟨ε₀, hε₀, ?_⟩
  intro μ hAdm n Φ u hex
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have ha : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  have hMv : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M = Work.BoseBox.mValue :=
    Work.BoseFixB1.M_eq_mValue μ (_root_.BoseGases.a v)
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  set Chi : ℝ := Work.BoseFixB1.chiSum (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      (Φ : Submission.BoseGases.X n → ℝ) with hChidef
  set Np : ℝ := Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Φ : Submission.BoseGases.X n → ℝ) with hNpdef
  set CNT : ℝ := ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
        (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u).indicator
          (fun _ => (1 : ℝ)) (x i) with hCNTdef
  have hcore' := hcore μ hAdm n Φ u
  rw [← hChidef, ← hNpdef] at hcore'
  have hcnt : Chi ≤ chiCs Work.BoseBox.mValue * CNT := by
    have h := chiSum_le_countCs (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
      hM hℓ hd u hΦc
    rw [← hChidef, ← hCNTdef] at h
    have hCs : chiCs (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        = chiCs Work.BoseBox.mValue := by rw [hMv]
    rwa [hCs] at h
  have hex' : (1 / 2 : ℝ) * CNT ≤ Np := hex
  have hCs0 : 0 ≤ chiCs Work.BoseBox.mValue := chiCs_nonneg _
  have hle2 : Chi ≤ 2 * chiCs Work.BoseBox.mValue * Np := by
    refine le_trans hcnt ?_
    calc chiCs Work.BoseBox.mValue * CNT
        ≤ chiCs Work.BoseBox.mValue * (2 * Np) :=
          mul_le_mul_of_nonneg_left (by linarith) hCs0
      _ = 2 * chiCs Work.BoseBox.mValue * Np := by ring
  have hNpnn : 0 ≤ Np := by
    rw [hNpdef, Work.UBBInputs8.cnPlusBoxInd]
    exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  have hkey := mul_le_mul_of_nonneg_left hle2
    (mul_nonneg (mul_nonneg (le_of_lt hμ) kav_nonneg) ha)
  nlinarith [hcore', hkey, hc'2, hNpnn,
    mul_nonneg (mul_nonneg (le_of_lt hμ) ha) hNpnn]

/-- **The low-occupancy arm.**  Below the threshold `K(μ·chiMass + 1)‖Φ‖²` the integrated
fibre bound alone pays the chemical-potential line of `sbPot`. -/
theorem lowArm {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 ≤ C ∧
        ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
          ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
            (u : EuclideanSpace ℝ (Fin 3)),
            Work.BoseFixB1.chiSum (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                (Φ : Submission.BoseGases.X n → ℝ)
              ≤ Work.BoseFixR.crudeThreshold v K μ
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                  (Φ : Submission.BoseGases.X n → ℝ) →
            -(C * (μ ^ 2 * (_root_.BoseGases.a v)
                    * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                  + μ * (_root_.BoseGases.a v)))
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  classical
  obtain ⟨ε₀, hε₀, hcore⟩ := sbCore (v := v) h hv hv1 hvrad hR hv_supp hav 0 (le_refl 0)
  refine ⟨ε₀, hε₀, ?_⟩
  intro K hK
  refine ⟨kav * K, mul_nonneg kav_nonneg hK, ?_⟩
  intro μ hAdm n Φ u hthr
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have ha : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  have hcore' := hcore μ hAdm n Φ u
  simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_mul, zero_sub] at hcore'
  set Chi : ℝ := Work.BoseFixB1.chiSum (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      (Φ : Submission.BoseGases.X n → ℝ) with hChidef
  set Chm : ℝ := Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u with hChmdef
  set J : ℝ := Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) with hJdef
  have hthr' : Chi ≤ K * (μ * Chm + 1) * J := by
    simpa only [Work.BoseFixR.crudeThreshold] using hthr
  have hkey : μ * kav * (_root_.BoseGases.a v) * Chi
      ≤ (kav * K) * (μ ^ 2 * (_root_.BoseGases.a v) * Chm + μ * (_root_.BoseGases.a v)) * J := by
    calc μ * kav * (_root_.BoseGases.a v) * Chi
        ≤ μ * kav * (_root_.BoseGases.a v) * (K * (μ * Chm + 1) * J) :=
          mul_le_mul_of_nonneg_left hthr'
            (mul_nonneg (mul_nonneg (le_of_lt hμ) kav_nonneg) ha)
      _ = (kav * K) * (μ ^ 2 * (_root_.BoseGases.a v) * Chm + μ * (_root_.BoseGases.a v)) * J := by
          ring
  rw [neg_mul]
  linarith [hcore', hkey]

/-! ## 4. The target -/

theorem perBoxCrudeLower {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          -(C * (μ ^ 2 * (_root_.BoseGases.a v)
                  * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                + μ * (_root_.BoseGases.a v)))
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  classical
  obtain ⟨εL, hεL, hlow⟩ := lowArm (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εA, hεA, harmA⟩ := excitedArm (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εB, KB, CB, hεB, hKB, hCB, harmB⟩ :=
    Work.BoseFixR.SlabCondensedHalf (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨CL, hCL, hlowK⟩ := hlow (max 1 KB) (le_trans zero_le_one (le_max_left _ _))
  refine ⟨min (min εL εA) εB, max CB CL, lt_min (lt_min hεL hεA) hεB,
    le_trans hCB (le_max_left _ _), ?_⟩
  intro μ hAdm n Φ u
  have hAdmL : Work.BoseBoxFix.Adm v εL μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hAdmA : Work.BoseBoxFix.Adm v εA μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hAdmB : Work.BoseBoxFix.Adm v εB μ :=
    Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have ha : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  set J : ℝ := Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) with hJdef
  set Chm : ℝ := Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u with hChmdef
  set XX : ℝ := μ ^ 2 * (_root_.BoseGases.a v) * Chm + μ * (_root_.BoseGases.a v) with hXXdef
  set N0 : ℝ := ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) i
        (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 with hN0def
  set Np : ℝ := Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Φ : Submission.BoseGases.X n → ℝ) with hNpdef
  set CNT : ℝ := ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
        (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u).indicator
          (fun _ => (1 : ℝ)) (x i) with hCNTdef
  have hsplit : CNT = N0 + Np := by
    rw [hCNTdef, hN0def, hNpdef]
    exact Work.BoseFixR.SlabCountSplit hℓ hd u hΦc
  have hXX0 : 0 ≤ XX := by
    rw [hXXdef, hChmdef]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (sq_nonneg μ) ha) (Work.SmallBoxSliding.chiMass_nonneg _ _ _ _))
      (mul_nonneg (le_of_lt hμ) ha)
  have hJ0 : 0 ≤ J := by
    rw [hJdef]
    exact Work.BoseFixB1.normB_nonneg _
  -- gluing: a smaller constant gives a smaller lower bound
  have hglue : ∀ {C' : ℝ}, C' ≤ max CB CL →
      -(C' * XX) * J ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) →
      -(max CB CL * XX) * J ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
    intro C' hC' hb
    have h1 : C' * XX * J ≤ max CB CL * XX * J :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC' hXX0) hJ0
    nlinarith [hb, h1]
  by_cases hex : (1 / 2 : ℝ) * CNT ≤ Np
  · -- excited arm: `sbWord ≥ 0`
    refine le_trans ?_ (harmA μ hAdmA n Φ u hex)
    have hmax0 : 0 ≤ max CB CL := le_trans hCB (le_max_left _ _)
    have h1 : 0 ≤ max CB CL * XX * J :=
      mul_nonneg (mul_nonneg hmax0 hXX0) hJ0
    nlinarith [h1]
  · -- condensed half: `n₀ ≥ cnt/2`
    have hnp : Np ≤ (1 / 2 : ℝ) * CNT := le_of_lt (not_le.mp hex)
    have hN0 : (1 / 2 : ℝ) * CNT ≤ N0 := by linarith [hsplit]
    by_cases hthr : Work.BoseFixR.crudeThreshold v (max 1 KB) μ
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ)
    · -- condensed arm (`lm:appinteractionestimate` at the sliding box)
      refine hglue (le_max_left _ _) (harmB μ hAdmB n Φ u ?_ hN0)
      refine le_trans ?_ hthr
      simp only [Work.BoseFixR.crudeThreshold]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right 1 KB) ?_) hJ0
      have hc0 : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ
          (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
        Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
      linarith [mul_nonneg (le_of_lt hμ) hc0]
    · -- low-occupancy arm
      refine hglue (le_max_right _ _) ?_
      refine hlowK μ hAdmL n Φ u ?_
      have hocc : Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.BoseFixR.crudeThreshold v (max 1 KB) μ
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              (Φ : Submission.BoseGases.X n → ℝ) := le_of_lt (not_le.mp hthr)
      simpa only [Work.BoseFixR.occChi, Work.BoseFixB1.chiSum] using hocc

end Work.BoseFixB1B
