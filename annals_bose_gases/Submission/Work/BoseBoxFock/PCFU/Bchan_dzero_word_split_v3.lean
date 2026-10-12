import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Submission.Work.BoseBoxFock.PCFU.Bchan_chiChatC_integrableOn
import Submission.Work.BoseBoxFock.PCFU.Bchan_dzero_split
import Submission.Work.BoseBoxFock.PCFU.Dchan_dzero_word_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# `Work.BoseBoxFock.PCFU.Bchan_dzero_word_split_v3`

The `(B)`-channel word split: the `d = 0` piece of the `(B)`-channel with the `KχfrU`-slit
replaced by the localised pair kernel `wLoc ℓ (g₀) 0` plus the `Ĉ`-remainder.

Writing `χ = chiLam ℓ`, `K = KχfrU v h μ fu N`, `P_i = aP ℓ i`, `Γ = lowSlot fc κ ℓ j (Q_jP_iΘ)`
and `Ĉ(z) = ∫_y χ(y)·W₁(y−z) dy`, the target identity is

    ∫_x Θ(x)·χ(x j)·K(x j)·Γ(x)
      = ℓ³·∫_{abox} (P_iΘ)(x)·wLoc ℓ (g₀) 0 (x i) (x j)·Γ(x)
        + ∫_x Θ(x)·χ(x j)·(K(x j) − Ĉ(x j))·Γ(x) .

The mathematical content is the **slot-mean transport identity**

    ℓ³·∫_{abox} (P_iΘ)(x)·χ(x i)·W₁(x i − x j)·χ(x j)·Γ(x) = ∫_{abox} Θ(x)·χ(x j)·Ĉ(x j)·Γ(x)

for an `i`-free `Γ` (here `Γ = Q_{L,j}Q_jP_iΘ` is `i`-free since `P_iΘ` is).  Its proof is the
`L¹`-self-adjointness of the slot mean `aP ℓ i` over the box (`PCFU.aP_sym_box_L1`) applied to
`Φ = Θ` and `Ψ(x) = χ(x i)W₁(x i−x j)χ(x j)Γ(x)`; the pointwise evaluation of `aP ℓ i Ψ` uses the
`i`-freeness of `Γ` and `supp χ ⊆ acube ℓ`.

The two integrability inputs on the box are the windowed pair kernel
(`PCFU.Bchan_pairWin_integrableOn`) and the windowed `Ĉ`-slit (`PCFU.Bchan_chiChatC_integrableOn`);
both rest on `PCFU.chiW1_integrable`, i.e. on the exact cancellation of the two window factors
against the renormalisation in `W₁ = g₀/(χ⋆χ)(·/ℓ)`.
-/

/-! ## §1  Elementary structural facts and `ℝ`/`ℂ` coercion helpers -/

/-- `‖↑r‖ = |r|` — a `rw`-friendly form (the generic `RCLike.norm_ofReal` does not rewrite
syntactically in this Mathlib). -/
private lemma norm_ofReal_v3 (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := RCLike.norm_ofReal r

/-- The coercion `ℝ → ℂ` commutes with the Bochner integral, in the `rw`-friendly direction. -/
private lemma integral_ofReal_v3 {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ} :
    (∫ x, ((f x : ℝ) : ℂ) ∂μ) = ((∫ x, f x ∂μ : ℝ) : ℂ) := integral_ofReal

/-- The `0`-translate of the bump is the corpus box bump: `χ_u` at `u = 0` is `χ_Λ`. -/
lemma chiU_zero_eq_chiLam_v3 (ℓ : ℝ) (x : E3) :
    Submission.BoseGases.chiU ℓ 0 x = Work.BoseK15.corpusBox.chiLam ℓ x := by
  simp [Submission.BoseGases.chiU, Work.BoseB4.BoxData.chiLam, Work.BoseK15.corpusBox_chi]

/-- The localised pair kernel at `u = 0` is `χ_Λ(x)·W₁(x−y)·χ_Λ(y)`. -/
lemma wLoc_g0_eq_v3 (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (ℓ : ℝ) (x y : E3) :
    Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 x y
      = Work.BoseK15.corpusBox.chiLam ℓ x * Work.BoseFixR.W1fun v h ℓ (x - y)
        * Work.BoseK15.corpusBox.chiLam ℓ y := by
  rw [Submission.BoseGases.wLoc, Work.BoseFixR.W1fun, Submission.BoseGases.wScaled,
    chiU_zero_eq_chiLam_v3, chiU_zero_eq_chiLam_v3]

/-- **`χ_Λ` is supported in the centred cube `acube ℓ`**: `χ_Λ(x) ≠ 0` forces `‖x‖_∞ ≤ ℓ/2`. -/
lemma chiLam_supp_acube_v3 {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Function.support (Work.BoseK15.corpusBox.chiLam ℓ) ⊆ Submission.BoseGases.acube ℓ := by
  intro x hx
  have hmem : (ℓ⁻¹) • x ∈ Work.BoseB4.unitCell := by
    refine Work.BoseK15.chi_support_subset_unitCell ?_
    simpa [Work.BoseB4.BoxData.chiLam, Work.BoseK15.corpusBox_chi] using hx
  intro m
  have h2 : |((ℓ⁻¹) • x) m| ≤ (1 / 2 : ℝ) := hmem m
  have h3 : |(ℓ⁻¹) * (x m)| ≤ (1 / 2 : ℝ) := by simpa using h2
  have h4 : |x m| ≤ ℓ / 2 := by
    have h5 : ℓ⁻¹ * |x m| ≤ 1 / 2 := by
      simpa [abs_mul, abs_of_pos (inv_pos.mpr hℓ)] using h3
    have h5' : |x m| / ℓ ≤ 1 / 2 := by
      rw [div_eq_mul_inv, mul_comm]
      exact h5
    have h8 := (div_le_iff₀ hℓ).mp h5'
    linarith
  exact ⟨by linarith [neg_abs_le (x m)], by linarith [le_abs_self (x m)]⟩

/-- **The uniform bound on the corpus window** (private copy of `PCFU.chiLam_abs_le`, whose module
does not sit in this import cone): `χ_Λ(z) = χ_base(z/ℓ)/√chiNormSq` with `|χ_base| ≤ 1`. -/
private lemma chiLam_norm_le_v3 (ℓ : ℝ) (z : E3) :
    ‖((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)‖
      ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ := by
  have hsqrt : 0 < Real.sqrt Submission.BoseGases.chiNormSq :=
    Real.sqrt_pos.mpr Submission.BoseGases.chiNormSq_pos
  have hval : Work.BoseK15.corpusBox.chiLam ℓ z
      = Submission.BoseGases.chiBase (ℓ⁻¹ • z) / Real.sqrt Submission.BoseGases.chiNormSq := by
    simp only [Work.BoseB4.BoxData.chiLam, Work.BoseK15.corpusBox_chi, Submission.BoseGases.chi]
  have hb : |Submission.BoseGases.chiBase (ℓ⁻¹ • z)| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [Submission.BoseGases.chiBase_nonneg (ℓ⁻¹ • z)],
      Submission.BoseGases.chiBase_le_one _⟩
  rw [norm_ofReal_v3, hval, abs_div, abs_of_pos hsqrt]
  rw [div_le_iff₀ hsqrt, inv_mul_cancel₀ (ne_of_gt hsqrt)]
  exact hb

/-- **The slot-`j` low-momentum lift of an `i`-free state is itself `i`-free** (`i ≠ j`):
replacing the `i`-th slot does not change `Γ_j ψ`. -/
lemma lowSlot_update_eq_of_free_v3 {n : ℕ} {ℓ κ : ℝ} {i j : Fin n} (hij : i ≠ j)
    (fc : Work.BoseBoxFix.LowCut) {ψ : Submission.BoseGases.X n → ℝ}
    (hψ : ∀ x y, ψ (Function.update x i y) = ψ x) (x : Submission.BoseGases.X n) (y : E3) :
    Work.BoseBoxFix.lowSlot fc κ ℓ j ψ (Function.update x i y)
      = Work.BoseBoxFix.lowSlot fc κ ℓ j ψ x := by
  have h1 : (Function.update x i y) j = x j := Function.update_of_ne hij.symm y x
  have h2 : (fun z : E3 => ψ (Function.update (Function.update x i y) j z))
      = fun z => ψ (Function.update x j z) := by
    funext z
    rw [Function.update_comm hij y z x]
    exact hψ (Function.update x j z) y
  simp only [Work.BoseBoxFix.lowSlot]
  rw [h1, h2]

/-! ## §2  The pointwise slot-mean identity -/

/-- **Pointwise evaluation of the `i`-slot mean of the windowed pair kernel.**  For an `i`-free
`Γ`, the slot-`i` mean of `χ(y i)W₁(y i − y j)χ(y j)Γ(y)` is `ℓ⁻³·χ(x j)·Ĉ(x j)·Γ(x)`, where
`Ĉ(z) = ∫_y χ(y)W₁(y−z)dy`. -/
lemma aP_transport_pointwise_v3 {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {ℓ : ℝ} {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hℓ : 0 < ℓ)
    {Γ : Submission.BoseGases.X n → ℝ} (hΓfree : ∀ x z, Γ (Function.update x i z) = Γ x)
    (x : Submission.BoseGases.X n) :
    Submission.BoseGases.aP ℓ i (fun y : Submission.BoseGases.X n =>
        Work.BoseK15.corpusBox.chiLam ℓ (y i) * Work.BoseFixR.W1fun v h ℓ (y i - y j)
          * Work.BoseK15.corpusBox.chiLam ℓ (y j) * Γ y) x
      = (1 / ℓ ^ 3) * (Work.BoseK15.corpusBox.chiLam ℓ (x j)
          * (∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
              * Work.BoseFixR.W1fun v h ℓ (y - x j))
          * Γ x) := by
  have hsupp : ∀ y : E3, y ∉ Submission.BoseGases.acube ℓ →
      Work.BoseK15.corpusBox.chiLam ℓ y = 0 := fun y hy => by
    by_contra hne
    exact hy (chiLam_supp_acube_v3 hℓ (Function.mem_support.mpr hne))
  simp only [Submission.BoseGases.aP]
  congr 1
  rw [show (∫ y in Submission.BoseGases.acube ℓ,
        Work.BoseK15.corpusBox.chiLam ℓ (Function.update x i y i)
          * Work.BoseFixR.W1fun v h ℓ (Function.update x i y i - Function.update x i y j)
          * Work.BoseK15.corpusBox.chiLam ℓ (Function.update x i y j)
          * Γ (Function.update x i y))
      = ∫ y in Submission.BoseGases.acube ℓ,
          (Work.BoseK15.corpusBox.chiLam ℓ y * Work.BoseFixR.W1fun v h ℓ (y - x j))
            * (Work.BoseK15.corpusBox.chiLam ℓ (x j) * Γ x) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => by
        simp only [Function.update_self, Function.update_of_ne hij.symm, hΓfree]
        ring))]
  rw [MeasureTheory.integral_mul_const]
  rw [show (∫ a in Submission.BoseGases.acube ℓ, Work.BoseK15.corpusBox.chiLam ℓ a
          * Work.BoseFixR.W1fun v h ℓ (a - x j))
      = ∫ a : E3, Work.BoseK15.corpusBox.chiLam ℓ a
          * Work.BoseFixR.W1fun v h ℓ (a - x j) from
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy => by rw [hsupp y hy, zero_mul])]
  ring

/-! ## §3  The real transport core -/

/-- **The `L¹` transport core of the `(B)`-channel word split.**  With `Γ` an `i`-free measurable
bounded state and the two windowed kernels integrable on the box, the `i`-slot mean of `Θ` may be
transported onto the `Ĉ`-slit at the price of the volume factor `ℓ³`. -/
private theorem Bchan_real_core_v3 {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {ℓ Cθ D : ℝ} (hℓ : 0 < ℓ)
    (hCθ : 0 ≤ Cθ) (hD : 0 ≤ D)
    {Θ : Submission.BoseGases.X n → ℝ} (hΘm : Measurable Θ)
    (hΘb : ∀ x, |Θ x| ≤ Cθ) (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ)
    {Γ : Submission.BoseGases.X n → ℝ} (hΓm : Measurable Γ) (hΓb : ∀ x, |Γ x| ≤ D)
    (hΓfree : ∀ x z, Γ (Function.update x i z) = Γ x)
    (hGint : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        Work.BoseK15.corpusBox.chiLam ℓ (x i) * Work.BoseFixR.W1fun v h ℓ (x i - x j)
          * Work.BoseK15.corpusBox.chiLam ℓ (x j)) (Submission.BoseGases.abox n ℓ) volume)
    (hChat : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        ((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ)
          * (((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
              * Work.BoseFixR.W1fun v h ℓ (y - x j)) : ℝ) : ℂ))
        (Submission.BoseGases.abox n ℓ) volume) :
    ℓ ^ 3 * (∫ x in Submission.BoseGases.abox n ℓ, Submission.BoseGases.aP ℓ i Θ x
        * (Work.BoseK15.corpusBox.chiLam ℓ (x i) * Work.BoseFixR.W1fun v h ℓ (x i - x j)
            * Work.BoseK15.corpusBox.chiLam ℓ (x j)) * Γ x)
      = ∫ x : Submission.BoseGases.X n, Θ x * Work.BoseK15.corpusBox.chiLam ℓ (x j)
          * (∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
              * Work.BoseFixR.W1fun v h ℓ (y - x j))
          * Γ x := by
  classical
  set G : Submission.BoseGases.X n → ℝ := fun x =>
      Work.BoseK15.corpusBox.chiLam ℓ (x i) * Work.BoseFixR.W1fun v h ℓ (x i - x j)
        * Work.BoseK15.corpusBox.chiLam ℓ (x j) with hGdef
  set Ψ : Submission.BoseGases.X n → ℝ := fun y => G y * Γ y with hΨdef
  set Ĉ : E3 → ℝ := fun z => ∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
      * Work.BoseFixR.W1fun v h ℓ (y - z) with hĈdef
  -- ### 1.  The pointwise value of `aP ℓ i Ψ`
  have hΨpt : ∀ x : Submission.BoseGases.X n, Submission.BoseGases.aP ℓ i Ψ x
      = (1 / ℓ ^ 3) * (Work.BoseK15.corpusBox.chiLam ℓ (x j) * Ĉ (x j) * Γ x) := by
    intro x
    have hh := aP_transport_pointwise_v3 (i := i) (j := j) hij (v := v) h hℓ
      (Γ := Γ) hΓfree x
    simpa only [hGdef, hΨdef, hĈdef] using hh
  -- ### 2.  The two `IntegrableOn` inputs of the self-adjointness
  have hGae : AEStronglyMeasurable G (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    (show MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
        Work.BoseK15.corpusBox.chiLam ℓ (x i) * Work.BoseFixR.W1fun v h ℓ (x i - x j)
          * Work.BoseK15.corpusBox.chiLam ℓ (x j))
        (volume.restrict (Submission.BoseGases.abox n ℓ)) from hGint).aestronglyMeasurable
  have hGl : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n => |G x|)
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    (show MeasureTheory.Integrable G (volume.restrict (Submission.BoseGases.abox n ℓ))
      from hGint).abs
  have h1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ i Θ x * Ψ x) (Submission.BoseGases.abox n ℓ) volume := by
    have hmaj : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
        Cθ * D * |G x|) (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
      hGl.const_mul (Cθ * D)
    refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
    · refine ((Work.BoseBoxFock.Weak.aP_measurable i hΘm).aestronglyMeasurable).mul ?_
      exact (hGae.mul hΓm.aestronglyMeasurable).congr
        (Filter.Eventually.of_forall (fun x => rfl))
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have hp : |Submission.BoseGases.aP ℓ i Θ x| ≤ Cθ :=
        Work.BoseBoxFock.Weak.aP_abs_le hℓ i hCθ hΘb x
      have hΨabs : |Ψ x| ≤ |G x| * D := by
        change |G x * Γ x| ≤ |G x| * D
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hΓb x) (abs_nonneg _)
      calc ‖Submission.BoseGases.aP ℓ i Θ x * Ψ x‖
          = |Submission.BoseGases.aP ℓ i Θ x * Ψ x| := Real.norm_eq_abs _
        _ = |Submission.BoseGases.aP ℓ i Θ x| * |Ψ x| := abs_mul _ _
        _ ≤ Cθ * (|G x| * D) := mul_le_mul hp hΨabs (abs_nonneg _) hCθ
        _ = Cθ * D * |G x| := by ring
  have h2 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Θ x * Submission.BoseGases.aP ℓ i Ψ x) (Submission.BoseGases.abox n ℓ) volume := by
    -- the `Ĉ`-slit is `L¹` on the box, in the casted complex form
    have hchatC : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
        ((Work.BoseK15.corpusBox.chiLam ℓ (x j) * Ĉ (x j) : ℝ) : ℂ))
        (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
      (show MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
          ((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ)
            * (((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
                * Work.BoseFixR.W1fun v h ℓ (y - x j)) : ℝ) : ℂ))
          (volume.restrict (Submission.BoseGases.abox n ℓ)) from hChat).congr
        (Filter.Eventually.of_forall (fun x => by
          simp only [hĈdef]
          rw [Complex.ofReal_mul]))
    -- the bounded factor `ℓ⁻³ΘΓ`
    have hfbdd : ∀ x : Submission.BoseGases.X n,
        ‖(fun x : Submission.BoseGases.X n =>
          ((1 / ℓ ^ 3 : ℝ) : ℂ) * ((Θ x : ℝ) : ℂ) * ((Γ x : ℝ) : ℂ)) x‖
          ≤ (1 / ℓ ^ 3) * Cθ * D := by
      intro x
      simp only []
      rw [norm_mul, norm_mul, norm_ofReal_v3, norm_ofReal_v3, norm_ofReal_v3]
      have h1' : (0 : ℝ) ≤ 1 / ℓ ^ 3 := by positivity
      rw [abs_of_nonneg h1']
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hΘb x) h1') (hΓb x) (abs_nonneg _)
        (mul_nonneg h1' hCθ)
    have hfae : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
        ((1 / ℓ ^ 3 : ℝ) : ℂ) * ((Θ x : ℝ) : ℂ) * ((Γ x : ℝ) : ℂ))
        (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
      (aestronglyMeasurable_const.mul
        (Complex.continuous_ofReal.comp_aestronglyMeasurable hΘm.aestronglyMeasurable)).mul
        (Complex.continuous_ofReal.comp_aestronglyMeasurable hΓm.aestronglyMeasurable)
    have hprod := MeasureTheory.Integrable.bdd_mul hchatC hfae
      (Filter.Eventually.of_forall hfbdd)
    -- identify the product with the casted integrand of `h2`
    have hcp : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
        ((Θ x * Submission.BoseGases.aP ℓ i Ψ x : ℝ) : ℂ))
        (volume.restrict (Submission.BoseGases.abox n ℓ)) := by
      refine hprod.congr (Filter.Eventually.of_forall (fun x => ?_))
      simp only []
      rw [hΨpt x]
      push_cast
      ring
    have hre := hcp.re
    refine hre.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp
  -- ### 3.  Self-adjointness of the slot mean over the box
  have hsym := aP_sym_box_L1 (n := n) hℓ i h1 h2
  -- ### 4.  Rewrite both sides and conclude
  have hL : (∫ x in Submission.BoseGases.abox n ℓ, Submission.BoseGases.aP ℓ i Θ x * Ψ x)
      = ∫ x in Submission.BoseGases.abox n ℓ, Submission.BoseGases.aP ℓ i Θ x
          * (Work.BoseK15.corpusBox.chiLam ℓ (x i) * Work.BoseFixR.W1fun v h ℓ (x i - x j)
              * Work.BoseK15.corpusBox.chiLam ℓ (x j)) * Γ x := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [hΨdef, hGdef]
    ring
  have hR : (∫ x in Submission.BoseGases.abox n ℓ, Θ x * Submission.BoseGases.aP ℓ i Ψ x)
      = (1 / ℓ ^ 3) * (∫ x : Submission.BoseGases.X n, Θ x
          * Work.BoseK15.corpusBox.chiLam ℓ (x j) * Ĉ (x j) * Γ x) := by
    have hpt : ∀ x : Submission.BoseGases.X n, Θ x * Submission.BoseGases.aP ℓ i Ψ x
        = (1 / ℓ ^ 3) * (Θ x * (Work.BoseK15.corpusBox.chiLam ℓ (x j) * Ĉ (x j) * Γ x)) := by
      intro x
      rw [hΨpt x]
      ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_const_mul]
    congr 1
    rw [show (∫ x : Submission.BoseGases.X n,
          Θ x * Work.BoseK15.corpusBox.chiLam ℓ (x j) * Ĉ (x j) * Γ x)
        = ∫ x : Submission.BoseGases.X n,
          Θ x * (Work.BoseK15.corpusBox.chiLam ℓ (x j) * Ĉ (x j) * Γ x) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))]
    exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have h0 : Θ x = 0 := by
        by_contra hne
        exact hx (hΘs (Function.mem_support.mpr hne))
      rw [h0, zero_mul])
  rw [hL] at hsym
  rw [hR] at hsym
  have hℓ3 : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
  have hfin : ℓ ^ 3 * ((1 / ℓ ^ 3) * (∫ x : Submission.BoseGases.X n, Θ x
        * Work.BoseK15.corpusBox.chiLam ℓ (x j) * Ĉ (x j) * Γ x))
      = ∫ x : Submission.BoseGases.X n, Θ x
        * Work.BoseK15.corpusBox.chiLam ℓ (x j) * Ĉ (x j) * Γ x := by
    field_simp
  calc ℓ ^ 3 * (∫ x in Submission.BoseGases.abox n ℓ, Submission.BoseGases.aP ℓ i Θ x
        * (Work.BoseK15.corpusBox.chiLam ℓ (x i) * Work.BoseFixR.W1fun v h ℓ (x i - x j)
            * Work.BoseK15.corpusBox.chiLam ℓ (x j)) * Γ x)
      = ℓ ^ 3 * ((1 / ℓ ^ 3) * (∫ x : Submission.BoseGases.X n, Θ x
          * Work.BoseK15.corpusBox.chiLam ℓ (x j) * Ĉ (x j) * Γ x)) := by rw [hsym]
    _ = ∫ x : Submission.BoseGases.X n, Θ x
          * Work.BoseK15.corpusBox.chiLam ℓ (x j) * Ĉ (x j) * Γ x := hfin

/-! ## §4  Bounded measurable functions with support in a finite-measure set are integrable -/

/-- A measurable function that is bounded and supported in a set of finite measure is
integrable. -/
private theorem integrable_of_bounded_support_v3 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : μ s < ⊤) {f : α → ℂ} (hm : Measurable f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (hsup : Function.support f ⊆ s) :
    MeasureTheory.Integrable f μ := by
  obtain ⟨C, hC⟩ := hb
  refine (MeasureTheory.integrableOn_iff_integrable_of_support_subset (μ := μ) (s := s)
    (f := f) hsup).mp ?_
  exact MeasureTheory.IntegrableOn.of_bound hs hm.aestronglyMeasurable.restrict
    (max C 0) (Filter.Eventually.of_forall fun x => le_trans (hC x) (le_max_left _ _))

/-! ## §5  The target -/

theorem Bchan_dzero_word_split_v3 {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ)
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hκ : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘ : Submission.BoseGases.PermInvariant n Θ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) :
    (∫ x : Submission.BoseGases.X n,
        ((Θ x : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
          * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j)
          * ((Work.BoseBoxFix.lowSlot fc
                (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                  * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                (Work.BoseBoxFock.ellH v μ) j
                (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                  (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)) x : ℝ) : ℂ))
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
              ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ x : ℝ) : ℂ)
                * ((Submission.BoseGases.wLoc (Work.BoseBoxFock.ellH v μ)
                      (Submission.BoseGases.g0 v h) 0 (x i) (x j) : ℝ) : ℂ)
                * ((Work.BoseBoxFix.lowSlot fc
                      (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                      (Work.BoseBoxFock.ellH v μ) j
                      (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                        (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)) x : ℝ) : ℂ))
        + (∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
                * (Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j)
                    - (∫ y : EuclideanSpace ℝ (Fin 3),
                        ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) y : ℝ) : ℂ)
                          * ((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)
                              (y - x j) : ℝ) : ℂ)))
                * ((Work.BoseBoxFix.lowSlot fc
                      (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                      (Work.BoseBoxFock.ellH v μ) j
                      (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                        (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)) x : ℝ) : ℂ)) := by
  classical
  obtain ⟨Cθ, hCθ⟩ := hΘb
  have hCθ0 : (0 : ℝ) ≤ Cθ := le_trans (abs_nonneg (Θ 0)) (hCθ 0)
  set ℓ : ℝ := Work.BoseBoxFock.ellH v μ with hℓdef
  set κ : ℝ := ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ with hκdef
  have hℓpos : 0 < ℓ := hℓ
  have hκpos : 0 < κ := hκ
  have hΘs' : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ := hΘs
  -- the state `ψ = Q_jP_iΘ` and its low-momentum lift `Γ`
  set ψ : Submission.BoseGases.X n → ℝ :=
    Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) with hψdef
  set Γ : Submission.BoseGases.X n → ℝ :=
    fun x => Work.BoseBoxFix.lowSlot fc κ ℓ j ψ x with hΓdef
  have hψfree : ∀ x z, ψ (Function.update x i z) = ψ x := by
    intro x z
    rw [hψdef]
    exact aQ_aP_update_invariant (i := i) (j := j) hij x z
  have hΓfree : ∀ x z, Γ (Function.update x i z) = Γ x := by
    intro x z
    have hh := lowSlot_update_eq_of_free_v3 (i := i) (j := j) hij fc (κ := κ) (ℓ := ℓ)
      (ψ := ψ) hψfree x z
    simpa only [hΓdef] using hh
  obtain ⟨hΓm, D, hD0, hΓb⟩ := lowSlot_aQ_aP_measurable_bounded (n := n) (fc := fc)
    (μ := μ) (ℓ := ℓ) (κ := κ) (Cθ := Cθ) hℓpos hκpos hCθ0 (i := i) (j := j) hΘm hCθ
  -- ### the windowed pair kernel is integrable on the box
  have hGint : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Work.BoseK15.corpusBox.chiLam ℓ (x i) * Work.BoseFixR.W1fun v h ℓ (x i - x j)
        * Work.BoseK15.corpusBox.chiLam ℓ (x j)) (Submission.BoseGases.abox n ℓ) volume := by
    have hglob : MeasureTheory.Integrable (fun p : E3 × E3 =>
        Submission.BoseGases.chiScale ℓ p.1 * Work.BoseFixR.W1fun v h ℓ (p.1 - p.2)
          * Submission.BoseGases.chiScale ℓ p.2)
        ((volume : Measure E3).prod (volume : Measure E3)) :=
      Work.BoseBoxFock.PCFU.chiW1_integrable h hℓpos
    have hres : MeasureTheory.Integrable (fun p : E3 × E3 =>
        Submission.BoseGases.chiScale ℓ p.1 * Work.BoseFixR.W1fun v h ℓ (p.1 - p.2)
          * Submission.BoseGases.chiScale ℓ p.2)
        ((volume.restrict (Submission.BoseGases.acube ℓ)).prod
          (volume.restrict (Submission.BoseGases.acube ℓ))) := by
      rw [Measure.prod_restrict]
      exact hglob.integrableOn
    refine (show MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.chiScale ℓ (x i) * Work.BoseFixR.W1fun v h ℓ (x i - x j)
          * Submission.BoseGases.chiScale ℓ (x j))
        (volume.restrict (Submission.BoseGases.abox n ℓ)) from
      integrableOn_pair_pullback_abox hℓpos hij hres).congr
      (Filter.Eventually.of_forall (fun x => by
        simp only [wsc_chiLam_eq_chiScale]))
  -- ### the `Ĉ`-slit is integrable on the box (delegated brick)
  have hcast : ∀ z : E3, (∫ y : E3, ((Work.BoseK15.corpusBox.chiLam ℓ y : ℝ) : ℂ)
        * ((Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℂ))
      = ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
          * Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℂ) := by
    intro z
    rw [show (∫ y : E3, ((Work.BoseK15.corpusBox.chiLam ℓ y : ℝ) : ℂ)
          * ((Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℂ))
        = ∫ y : E3, ((Work.BoseK15.corpusBox.chiLam ℓ y
            * Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℂ) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => by
        push_cast
        ring))]
    exact integral_ofReal_v3
  have hChatC : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      ((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ)
        * (∫ y : E3, ((Work.BoseK15.corpusBox.chiLam ℓ y : ℝ) : ℂ)
            * ((Work.BoseFixR.W1fun v h ℓ (y - x j) : ℝ) : ℂ)))
      (Submission.BoseGases.abox n ℓ) volume :=
    Bchan_chiChatC_integrableOn (n := n) (j := j) v h (ℓ := ℓ) hℓpos
  have hChat : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      ((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ)
        * (((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
            * Work.BoseFixR.W1fun v h ℓ (y - x j)) : ℝ) : ℂ))
      (Submission.BoseGases.abox n ℓ) volume :=
    (show MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
        ((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ)
          * (∫ y : E3, ((Work.BoseK15.corpusBox.chiLam ℓ y : ℝ) : ℂ)
              * ((Work.BoseFixR.W1fun v h ℓ (y - x j) : ℝ) : ℂ)))
        (volume.restrict (Submission.BoseGases.abox n ℓ)) from hChatC).congr
      (Filter.Eventually.of_forall (fun x => by
        simp only []
        rw [hcast (x j)]))
  -- ### the real transport identity
  have hcore := Bchan_real_core_v3 (i := i) (j := j) hij (v := v) h (ℓ := ℓ) (Cθ := Cθ)
    (D := D) hℓpos hCθ0 hD0 hΘm hCθ hΘs' hΓm hΓb hΓfree hGint hChat
  -- the same identity, written with the local abbreviation `Γ`
  have hcore' : ℓ ^ 3 * (∫ x in Submission.BoseGases.abox n ℓ, Submission.BoseGases.aP ℓ i Θ x
        * (Work.BoseK15.corpusBox.chiLam ℓ (x i) * Work.BoseFixR.W1fun v h ℓ (x i - x j)
            * Work.BoseK15.corpusBox.chiLam ℓ (x j)) * Γ x)
      = ∫ x : Submission.BoseGases.X n, Θ x * Work.BoseK15.corpusBox.chiLam ℓ (x j)
          * (∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
              * Work.BoseFixR.W1fun v h ℓ (y - x j))
          * Γ x := by
    simp only [hΓdef, hψdef]
    exact hcore
  -- ### the complex bookkeeping
  set Kc : E3 → ℂ := fun z => Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z with hKcdef
  set Ĉc : E3 → ℂ := fun z => ∫ y : E3, ((Work.BoseK15.corpusBox.chiLam ℓ y : ℝ) : ℂ)
      * ((Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℂ) with hĈcdef
  set Ĉ : E3 → ℝ := fun z => ∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
      * Work.BoseFixR.W1fun v h ℓ (y - z) with hĈdef
  set Γc : Submission.BoseGases.X n → ℂ := fun x => ((Γ x : ℝ) : ℂ) with hΓcdef
  set W1c : Submission.BoseGases.X n → ℂ := fun x => ((Θ x : ℝ) : ℂ)
      * ((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ) * Kc (x j) * Γc x with hW1cdef
  set W2c : Submission.BoseGases.X n → ℂ := fun x => ((Θ x : ℝ) : ℂ)
      * ((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ) * (Kc (x j) - Ĉc (x j)) * Γc x
    with hW2cdef
  set W3c : Submission.BoseGases.X n → ℂ := fun x => ((Θ x : ℝ) : ℂ)
      * ((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ) * Ĉc (x j) * Γc x with hW3cdef
  change (∫ x : Submission.BoseGases.X n, W1c x)
      = ((ℓ : ℂ)) ^ 3 * (∫ x in Submission.BoseGases.abox n ℓ,
            ((Submission.BoseGases.aP ℓ i Θ x : ℝ) : ℂ)
              * ((Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j) : ℝ) : ℂ)
              * Γc x)
        + (∫ x : Submission.BoseGases.X n, W2c x)
  -- the `Ĉc`-slit is the cast of the real one
  have hĈcc : ∀ z : E3, Ĉc z = ((Ĉ z : ℝ) : ℂ) := by
    intro z
    simp only [hĈcdef, hĈdef, hcast z]
  -- (i) `W1c` is integrable (bounded, supported in the box)
  have hW1bound : ∃ C : ℝ, ∀ x : Submission.BoseGases.X n, ‖W1c x‖ ≤ C := by
    refine ⟨Cθ * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
      * (∑ k : Work.BoseBoxFock.Lab N,
          |Work.BoseBoxFock.W1h v h μ fu N k * Work.BoseBoxFock.hatChih v μ N k|) * D, ?_⟩
    intro x
    simp only [hW1cdef, hKcdef, hΓcdef]
    have hχb : ‖((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ)‖
        ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ := chiLam_norm_le_v3 ℓ (x j)
    have hKb := Work.BoseBoxFock.PCFU.norm_KχfrU_le v h μ fu N (x j)
    have hΘn : ‖((Θ x : ℝ) : ℂ)‖ ≤ Cθ := by
      rw [norm_ofReal_v3]
      exact hCθ x
    have hΓn : ‖((Γ x : ℝ) : ℂ)‖ ≤ D := by
      rw [norm_ofReal_v3]
      exact hΓb x
    rw [norm_mul, norm_mul, norm_mul]
    have h0a : (0 : ℝ) ≤ Cθ := hCθ0
    have h0c : (0 : ℝ) ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ :=
      inv_nonneg.mpr (Real.sqrt_nonneg _)
    have h0s : (0 : ℝ) ≤ ∑ k : Work.BoseBoxFock.Lab N,
        |Work.BoseBoxFock.W1h v h μ fu N k * Work.BoseBoxFock.hatChih v μ N k| :=
      Finset.sum_nonneg (fun k _ => abs_nonneg _)
    exact mul_le_mul (mul_le_mul (mul_le_mul hΘn hχb (norm_nonneg _) h0a) hKb
      (norm_nonneg _) (mul_nonneg h0a h0c)) hΓn (norm_nonneg _)
      (mul_nonneg (mul_nonneg h0a h0c) h0s)
  have hW1int : MeasureTheory.Integrable W1c (volume : Measure (Submission.BoseGases.X n)) := by
    refine integrable_of_bounded_support_v3 (μ := (volume : Measure (Submission.BoseGases.X n)))
      (s := Submission.BoseGases.abox n ℓ) (Submission.BoseGases.abox_lt_top n ℓ hℓpos.le)
      ?_ hW1bound ?_
    · rw [hW1cdef]
      exact (((Complex.measurable_ofReal.comp hΘm).mul
        (Complex.measurable_ofReal.comp
          (((Work.BoseB4.BoxData.chiLam_cont Work.BoseK15.corpusBox ℓ).measurable).comp
            (measurable_pi_apply j)))).mul
        (((continuous_KχfrU v h μ fu N).measurable).comp (measurable_pi_apply j))).mul
        (Complex.measurable_ofReal.comp hΓm)
    · intro x hx
      rw [Function.mem_support] at hx
      by_contra hcon
      have h0 : Θ x = 0 := by
        by_contra hne
        exact hcon (hΘs (Function.mem_support.mpr hne))
      exact hx (by simp only [hW1cdef, hΓcdef, h0]; simp)
  -- (ii) `W3c` is integrable (`Ĉc`-slit on the box, times the bounded factors)
  have hW3int : MeasureTheory.Integrable W3c (volume : Measure (Submission.BoseGases.X n)) := by
    have hbox : MeasureTheory.IntegrableOn W3c (Submission.BoseGases.abox n ℓ) volume := by
      have hchC : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
          ((Work.BoseK15.corpusBox.chiLam ℓ (x j) * Ĉ (x j) : ℝ) : ℂ))
          (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
        (show MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
            ((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ)
              * (∫ y : E3, ((Work.BoseK15.corpusBox.chiLam ℓ y : ℝ) : ℂ)
                  * ((Work.BoseFixR.W1fun v h ℓ (y - x j) : ℝ) : ℂ)))
            (volume.restrict (Submission.BoseGases.abox n ℓ)) from hChatC).congr
          (Filter.Eventually.of_forall (fun x => by
            simp only [hĈdef]
            rw [hcast (x j), Complex.ofReal_mul]))
      have hfbdd : ∀ x : Submission.BoseGases.X n,
          ‖(fun x : Submission.BoseGases.X n =>
            ((Θ x : ℝ) : ℂ) * ((Γ x : ℝ) : ℂ)) x‖ ≤ Cθ * D := by
        intro x
        simp only []
        rw [norm_mul, norm_ofReal_v3, norm_ofReal_v3]
        exact mul_le_mul (hCθ x) (hΓb x) (abs_nonneg _) hCθ0
      have hfae : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
          ((Θ x : ℝ) : ℂ) * ((Γ x : ℝ) : ℂ))
          (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
        (Complex.continuous_ofReal.comp_aestronglyMeasurable hΘm.aestronglyMeasurable).mul
          (Complex.continuous_ofReal.comp_aestronglyMeasurable hΓm.aestronglyMeasurable)
      have hprod := MeasureTheory.Integrable.bdd_mul hchC hfae
        (Filter.Eventually.of_forall hfbdd)
      refine hprod.congr (Filter.Eventually.of_forall (fun x => ?_))
      simp only [hW3cdef, hΓcdef, hĈcc]
      push_cast
      ring
    refine (MeasureTheory.integrableOn_iff_integrable_of_support_subset (μ :=
      (volume : Measure (Submission.BoseGases.X n))) (s := Submission.BoseGases.abox n ℓ)
      ?_).mp hbox
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hcon
    have h0 : Θ x = 0 := by
      by_contra hne
      exact hcon (hΘs (Function.mem_support.mpr hne))
    exact hx (by simp only [hW3cdef, hΓcdef, h0]; simp)
  have hW2int : MeasureTheory.Integrable W2c (volume : Measure (Submission.BoseGases.X n)) := by
    have hsub : W2c = W1c - W3c := by
      funext x
      simp only [hW1cdef, hW2cdef, hW3cdef, Pi.sub_apply]
      ring
    rw [hsub]
    exact hW1int.sub hW3int
  -- (iii) the split `∫W1c = ∫W2c + ∫W3c`
  have hsplit : (∫ x : Submission.BoseGases.X n, W1c x)
      = (∫ x : Submission.BoseGases.X n, W2c x)
        + (∫ x : Submission.BoseGases.X n, W3c x) := by
    have hpt : ∀ x : Submission.BoseGases.X n, W1c x = W2c x + W3c x := by
      intro x
      simp only [hW1cdef, hW2cdef, hW3cdef]
      ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact MeasureTheory.integral_add hW2int hW3int
  -- (iv) the transport identity in the casted complex form
  have hW3eq : (∫ x : Submission.BoseGases.X n, W3c x)
      = ((ℓ : ℂ)) ^ 3 * (∫ x in Submission.BoseGases.abox n ℓ,
            ((Submission.BoseGases.aP ℓ i Θ x : ℝ) : ℂ)
              * ((Work.BoseK15.corpusBox.chiLam ℓ (x i) * Work.BoseFixR.W1fun v h ℓ (x i - x j)
                  * Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ)
              * Γc x) := by
    have h1 : (∫ x : Submission.BoseGases.X n, W3c x)
        = ((∫ x : Submission.BoseGases.X n, Θ x * Work.BoseK15.corpusBox.chiLam ℓ (x j)
            * Ĉ (x j) * Γ x : ℝ) : ℂ) := by
      rw [show (∫ x : Submission.BoseGases.X n, W3c x)
          = (∫ x : Submission.BoseGases.X n, ((Θ x * Work.BoseK15.corpusBox.chiLam ℓ (x j)
              * Ĉ (x j) * Γ x : ℝ) : ℂ)) from
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by
          simp only [hW3cdef, hĈcc, hΓcdef]
          push_cast
          ring))]
      exact integral_ofReal_v3
    have h2 : ((∫ x : Submission.BoseGases.X n, Θ x * Work.BoseK15.corpusBox.chiLam ℓ (x j)
            * Ĉ (x j) * Γ x : ℝ) : ℂ)
        = ((ℓ ^ 3 * (∫ x in Submission.BoseGases.abox n ℓ, Submission.BoseGases.aP ℓ i Θ x
              * (Work.BoseK15.corpusBox.chiLam ℓ (x i) * Work.BoseFixR.W1fun v h ℓ (x i - x j)
                  * Work.BoseK15.corpusBox.chiLam ℓ (x j)) * Γ x) : ℝ) : ℂ) := by
      rw [hcore']
    have h3 : ((ℓ ^ 3 * (∫ x in Submission.BoseGases.abox n ℓ, Submission.BoseGases.aP ℓ i Θ x
              * (Work.BoseK15.corpusBox.chiLam ℓ (x i) * Work.BoseFixR.W1fun v h ℓ (x i - x j)
                  * Work.BoseK15.corpusBox.chiLam ℓ (x j)) * Γ x) : ℝ) : ℂ)
        = ((ℓ : ℂ)) ^ 3 * (∫ x in Submission.BoseGases.abox n ℓ,
              ((Submission.BoseGases.aP ℓ i Θ x : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.chiLam ℓ (x i) * Work.BoseFixR.W1fun v h ℓ (x i - x j)
                    * Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ)
                * Γc x) := by
      rw [show ((ℓ ^ 3 * (∫ x in Submission.BoseGases.abox n ℓ,
              Submission.BoseGases.aP ℓ i Θ x
              * (Work.BoseK15.corpusBox.chiLam ℓ (x i) * Work.BoseFixR.W1fun v h ℓ (x i - x j)
                  * Work.BoseK15.corpusBox.chiLam ℓ (x j)) * Γ x) : ℝ) : ℂ)
          = ((ℓ : ℂ)) ^ 3 * (((∫ x in Submission.BoseGases.abox n ℓ,
              Submission.BoseGases.aP ℓ i Θ x
              * (Work.BoseK15.corpusBox.chiLam ℓ (x i) * Work.BoseFixR.W1fun v h ℓ (x i - x j)
                  * Work.BoseK15.corpusBox.chiLam ℓ (x j)) * Γ x) : ℝ) : ℂ) from by
        push_cast
        ring]
      congr 1
      rw [show (((∫ x in Submission.BoseGases.abox n ℓ, Submission.BoseGases.aP ℓ i Θ x
              * (Work.BoseK15.corpusBox.chiLam ℓ (x i) * Work.BoseFixR.W1fun v h ℓ (x i - x j)
                  * Work.BoseK15.corpusBox.chiLam ℓ (x j)) * Γ x) : ℝ) : ℂ)
          = ∫ x in Submission.BoseGases.abox n ℓ,
              ((Submission.BoseGases.aP ℓ i Θ x
                  * (Work.BoseK15.corpusBox.chiLam ℓ (x i) * Work.BoseFixR.W1fun v h ℓ (x i - x j)
                      * Work.BoseK15.corpusBox.chiLam ℓ (x j)) * Γ x : ℝ) : ℂ) from
        integral_ofReal_v3.symm]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      simp only [hΓcdef]
      push_cast
      ring
    rw [h1, h2, h3]
  -- (v) rewrite the `wLoc` factor as the product window
  have hwLoc : (∫ x in Submission.BoseGases.abox n ℓ,
        ((Submission.BoseGases.aP ℓ i Θ x : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.chiLam ℓ (x i) * Work.BoseFixR.W1fun v h ℓ (x i - x j)
              * Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ)
          * Γc x)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          ((Submission.BoseGases.aP ℓ i Θ x : ℝ) : ℂ)
            * ((Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j) : ℝ) : ℂ)
            * Γc x := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only []
    rw [show ((Work.BoseK15.corpusBox.chiLam ℓ (x i) * Work.BoseFixR.W1fun v h ℓ (x i - x j)
          * Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ)
        = ((Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j) : ℝ) : ℂ) from by
      rw [wLoc_g0_eq_v3]]
  rw [hsplit, hW3eq, hwLoc]
  exact add_comm _ _

end Work.BoseBoxFock.PCFU
