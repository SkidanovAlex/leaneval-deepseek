import Mathlib
import Submission.Work.BW.measurePreservingOrthogonal
import Submission.Work.BW.orthogonalParameterization
import Submission.Work.BW.isometricAux.lintegral_comp_mulVec_add
import Submission.Work.BW.isometricAux.ofReal_gauss_factor_mulVec
import Submission.Work.BW.isometricAux.slab_convex_symm_closed

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The isometric change of variables behind the Baker–Wüstholz peaked inequality

Let `B : Fin n × Fin k` and `Bp : Fin n × Fin (n-k)` have orthonormal columns, mutually
orthogonal, so that `(x, y) ↦ B.mulVec x + Bp.mulVec y` is a linear isometry of
`ℝᵏ × ℝⁿ⁻ᵏ` onto `ℝⁿ`.  Writing `U = {z | |(Bpᵀ z) l| ≤ δ/2}` for the slab whose coordinate
section is the box `∏ Icc (-δ/2) (δ/2)`, the peaked inequality
`∫_U ∏ 𝟙_{[-1/2,1/2]} ≥ ∫_U ∏ exp (-π ·²)` (hypothesis `hpeak`) turns into the claim that the
product of the one-dimensional Gaussian integrals over the box is bounded by the iterated
integrals of the indicator of the unit cube.
-/

namespace Work.BW

open MeasureTheory Matrix
open scoped ENNReal

/-! ## Elementary helpers -/

/-- The product of the indicators of `[-1/2,1/2]` is the indicator of the unit cube. -/
private lemma prod_Icc_indicator_eq_ite {ι : Type*} [Fintype ι] (z : ι → ℝ) :
    (∏ i, (Set.Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1:ENNReal)) (z i))
      = if (∀ i, |z i| ≤ 1/2) then 1 else 0 := by
  by_cases h : ∀ i, |z i| ≤ 1/2
  · rw [if_pos h]
    refine Finset.prod_eq_one (fun i _ => ?_)
    rw [Set.indicator_apply, if_pos]
    exact Set.mem_Icc.mpr ⟨(abs_le.mp (h i)).1, (abs_le.mp (h i)).2⟩
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [Set.indicator_apply, if_neg]
    exact fun hmem => hi (abs_le.mpr (Set.mem_Icc.mp hmem))

/-- The product of indicators is measurable. -/
private lemma measurable_prod_indicator {ι : Type*} [Fintype ι] :
    Measurable fun z : ι → ℝ =>
      ∏ i, (Set.Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1:ENNReal)) (z i) := by
  refine Finset.measurable_prod _ (fun i _ => ?_)
  exact (measurable_const.indicator measurableSet_Icc).comp (measurable_pi_apply i)

/-- One Gaussian factor is measurable. -/
private lemma measurable_gauss_factor {ι : Type*} (l : ι) :
    Measurable fun y : ι → ℝ => ENNReal.ofReal (Real.exp (- Real.pi * (y l)^2)) := by
  have hid : Measurable fun t : ℝ => t := measurable_id
  have hmul : Measurable fun t : ℝ => t * t := hid.mul hid
  have hc : Measurable fun _ : ℝ => (-Real.pi) := measurable_const
  have h2 : Measurable fun t : ℝ => (-Real.pi) * (t * t) := hc.mul hmul
  have h3 : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp ((-Real.pi) * (t * t))) :=
    (Real.measurable_exp.comp h2).ennreal_ofReal
  have h4 : Measurable fun y : ι → ℝ =>
      ENNReal.ofReal (Real.exp ((-Real.pi) * (y l * y l))) :=
    h3.comp (measurable_pi_apply l)
  have hgoal : (fun y : ι → ℝ => ENNReal.ofReal (Real.exp (- Real.pi * (y l)^2)))
      = (fun y : ι → ℝ => ENNReal.ofReal (Real.exp ((-Real.pi) * (y l * y l)))) := by
    funext y
    rw [pow_two]
  rw [hgoal]
  exact h4

/-- Membership in `Icc (-b) b` is `|a| ≤ b`. -/
private lemma mem_Icc_neg_abs {a b : ℝ} : a ∈ Set.Icc (-b) b ↔ |a| ≤ b := by
  rw [Set.mem_Icc, abs_le]

/-- Tonelli for a product of nonnegative integrable functions of one coordinate each. -/
private lemma lintegral_pi_prod_eq_prod {ι : Type*} [Fintype ι] {μ : ι → Measure ℝ}
    [∀ i, SigmaFinite (μ i)] (f : ι → ℝ → ℝ) (hnn : ∀ i x, 0 ≤ f i x)
    (hint : ∀ i, Integrable (f i) (μ i)) :
    ∫⁻ x : ι → ℝ, ∏ i, ENNReal.ofReal (f i (x i)) ∂(Measure.pi μ)
      = ∏ i, ENNReal.ofReal (∫ x, f i x ∂(μ i)) := by
  have hfun : (fun x : ι → ℝ => ∏ i, ENNReal.ofReal (f i (x i)))
      = (fun x : ι → ℝ => ENNReal.ofReal (∏ i, f i (x i))) := by
    funext x
    rw [ENNReal.ofReal_prod_of_nonneg]
    exact fun i _ => hnn i (x i)
  rw [hfun, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (Integrable.fintype_prod hint)
      (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => hnn i (x i)))),
    MeasureTheory.integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x => hnn i x))]

private lemma integrable_gauss : Integrable (fun t : ℝ => Real.exp (- Real.pi * t^2)) :=
  integrable_exp_neg_mul_sq (b := Real.pi) Real.pi_pos

private lemma integral_gauss : ∫ t : ℝ, Real.exp (- Real.pi * t^2) = 1 := by
  have h := integral_gaussian Real.pi
  rw [div_self (ne_of_gt Real.pi_pos), Real.sqrt_one] at h
  simpa using h

/-! ## The main theorem -/

theorem isometricDelta {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ) (hB : B.transpose * B = 1)
    (Bp : Matrix (Fin n) (Fin (n - k)) ℝ) (hBp : Bp.transpose * Bp = 1) (hBBp : B.transpose * Bp = 0)
    (hk : k ≤ n)
    (hpeak : ∀ (U : Set (Fin n → ℝ)), Convex ℝ U → U = -U → IsClosed U →
      ∫⁻ u in U, (∏ i, (Set.Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1:ENNReal)) (u i))
        ≥ ∫⁻ u in U, (∏ i, ENNReal.ofReal (Real.exp (- Real.pi * (u i)^2))))
    {δ : ℝ} (hδ : 0 < δ) :
    (∏ l : Fin (n-k), ∫ t in Set.Icc (-(δ/2)) (δ/2), Real.exp (- Real.pi * t^2))
      ≤ ∫ x : Fin k → ℝ, ∫ y in Set.pi Set.univ (fun _ : Fin (n-k) => Set.Icc (-(δ/2)) (δ/2)),
          (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then (1:ℝ) else 0) := by
  classical
  -- ## Notation
  set box : Set (Fin (n-k) → ℝ) :=
    Set.pi Set.univ (fun _ : Fin (n-k) => Set.Icc (-(δ/2)) (δ/2)) with hboxdef
  set U : Set (Fin n → ℝ) := {z | ∀ l : Fin (n-k), |(Bp.transpose.mulVec z) l| ≤ δ/2} with hUdef
  -- ## The slab is convex, symmetric and closed
  obtain ⟨hcU0, hsU0, hclU0⟩ := isometricAux.slab_convex_symm_closed (m := n-k) Bp (δ := δ) hδ
  have hcU : Convex ℝ U := by rw [hUdef]; exact hcU0
  have hsU : U = -U := by rw [hUdef]; exact hsU0
  have hclU : IsClosed U := by rw [hUdef]; exact hclU0
  have hUmeas : MeasurableSet U := hclU.measurableSet
  have hboxmeas : MeasurableSet box := by
    rw [hboxdef]
    exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  -- ## The unit cube is closed
  have hcle : IsClosed {z : Fin n → ℝ | ∀ i, |z i| ≤ 1/2} := by
    have hset : {z : Fin n → ℝ | ∀ i, |z i| ≤ 1/2}
        = ⋂ i : Fin n, (fun z : Fin n → ℝ => z i) ⁻¹' (Set.Icc (-(1/2:ℝ)) (1/2)) := by
      ext z
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq, mem_Icc_neg_abs]
    rw [hset]
    exact isClosed_iInter (fun i => isClosed_Icc.preimage (continuous_apply i))
  -- ## Matrix identities
  have hBpB : Bp.transpose * B = 0 := by
    have h := congrArg Matrix.transpose hBBp
    simpa [Matrix.transpose_mul] using h
  have hmv : ∀ (x : Fin k → ℝ) (y : Fin (n-k) → ℝ),
      Bp.transpose.mulVec (B.mulVec x + Bp.mulVec y) = y := by
    intro x y
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBpB, hBp,
      Matrix.zero_mulVec, Matrix.one_mulVec, zero_add]
  have hmem : ∀ (x : Fin k → ℝ) (y : Fin (n-k) → ℝ),
      (B.mulVec x + Bp.mulVec y ∈ U) ↔ y ∈ box := by
    intro x y
    have hb : y ∈ box ↔ ∀ l, -(δ/2) ≤ y l ∧ y l ≤ δ/2 := by
      rw [hboxdef]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    rw [hb]
    simp only [hUdef, Set.mem_setOf_eq, hmv x y]
    exact ⟨fun h l => abs_le.mp (h l), fun h l => abs_le.mpr (h l)⟩
  -- ## Continuity of the parametrisation
  have hcB : Continuous fun x : Fin k → ℝ => B.mulVec x := by
    rw [show (fun x : Fin k → ℝ => B.mulVec x) =
        (⇑(Matrix.toLin' B) : (Fin k → ℝ) → (Fin n → ℝ)) from by
      funext x; rw [Matrix.toLin'_apply]]
    exact LinearMap.continuous_of_finiteDimensional _
  have hcBp : Continuous fun y : Fin (n-k) → ℝ => Bp.mulVec y := by
    rw [show (fun y : Fin (n-k) → ℝ => Bp.mulVec y) =
        (⇑(Matrix.toLin' Bp) : (Fin (n-k) → ℝ) → (Fin n → ℝ)) from by
      funext y; rw [Matrix.toLin'_apply]]
    exact LinearMap.continuous_of_finiteDimensional _
  have hcont : Continuous fun p : (Fin k → ℝ) × (Fin (n-k) → ℝ) =>
      B.mulVec p.1 + Bp.mulVec p.2 := (hcB.comp continuous_fst).add (hcBp.comp continuous_snd)
  -- ## The peaked inequality
  have hpeakU := hpeak U hcU hsU hclU
  -- ## The set `S` of pairs whose image lies in the unit cube, over the box
  set S : Set ((Fin k → ℝ) × (Fin (n-k) → ℝ)) :=
    {p | p.2 ∈ box ∧ ∀ i, |(B.mulVec p.1 + Bp.mulVec p.2) i| ≤ 1/2} with hSdef
  have hSmeas : MeasurableSet S := by
    rw [hSdef]
    refine MeasurableSet.inter ?_ ?_
    · exact hboxmeas.preimage continuous_snd.measurable
    · exact (hcle.preimage hcont).measurableSet
  -- ## The inner function `H`
  set H : (Fin k → ℝ) → ENNReal := fun x =>
    ∫⁻ y in box, ENNReal.ofReal (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then (1:ℝ) else 0)
    with hHdef
  -- ## `H x` is the real inner integral
  have hHval : ∀ x : Fin k → ℝ,
      (H x).toReal = ∫ y in box,
        (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then (1:ℝ) else 0) := by
    intro x
    set T : Set (Fin (n-k) → ℝ) := {y | ∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2} with hTdef
    have hTmeas : MeasurableSet T := (hcle.preimage (continuous_const.add hcBp)).measurableSet
    have hHx : H x = (volume : Measure (Fin (n-k) → ℝ)) (box ∩ T) := by
      show (∫⁻ y in box, ENNReal.ofReal (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2)
            then (1:ℝ) else 0)) = (volume : Measure (Fin (n-k) → ℝ)) (box ∩ T)
      have h1 : (fun y : Fin (n-k) → ℝ =>
            ENNReal.ofReal (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then (1:ℝ) else 0))
          = T.indicator (fun _ => (1:ENNReal)) := by
        funext y
        by_cases h : (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2)
        · rw [if_pos h, Set.indicator_of_mem (show y ∈ T from by rw [hTdef]; exact h),
            ENNReal.ofReal_one]
        · rw [if_neg h, Set.indicator_of_notMem (show y ∉ T from fun hy => h hy),
            ENNReal.ofReal_zero]
      rw [h1, ← lintegral_indicator hboxmeas]
      rw [show (fun y => box.indicator (T.indicator (fun _ => (1:ENNReal))) y)
            = (box ∩ T).indicator (fun _ => (1:ENNReal)) from by
          funext y; by_cases hy : y ∈ box <;> by_cases hz : y ∈ T <;>
            simp [Set.indicator_apply, hy, hz]]
      exact lintegral_indicator_one (hboxmeas.inter hTmeas)
    have hRx : (∫ y in box,
          (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then (1:ℝ) else 0))
        = (volume : Measure (Fin (n-k) → ℝ)).real (box ∩ T) := by
      have h1 : (fun y : Fin (n-k) → ℝ =>
            (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then (1:ℝ) else 0))
          = T.indicator (fun _ => (1:ℝ)) := by
        funext y
        by_cases h : (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2)
        · rw [if_pos h, Set.indicator_of_mem (show y ∈ T from by rw [hTdef]; exact h)]
        · rw [if_neg h, Set.indicator_of_notMem (show y ∉ T from fun hy => h hy)]
      rw [h1, ← integral_indicator hboxmeas]
      rw [show (fun y => box.indicator (T.indicator (fun _ => (1:ℝ))) y)
            = (box ∩ T).indicator (fun _ => (1:ℝ)) from by
          funext y; by_cases hy : y ∈ box <;> by_cases hz : y ∈ T <;>
            simp [Set.indicator_apply, hy, hz]]
      exact integral_indicator_one (hboxmeas.inter hTmeas)
    rw [hHx, hRx, Measure.real_def]
  -- ## `H` is measurable
  have hHmeas : AEMeasurable H (volume : Measure (Fin k → ℝ)) := by
    have hmain : Measurable fun x : Fin k → ℝ =>
        ∫⁻ y, S.indicator (fun _ => (1:ENNReal)) (x, y) :=
      Measurable.lintegral_prod_right' (measurable_const.indicator hSmeas :
        Measurable (S.indicator (fun _ => (1:ENNReal))))
    have hEq : H = fun x : Fin k → ℝ => ∫⁻ y, S.indicator (fun _ => (1:ENNReal)) (x, y) := by
      funext x
      show (∫⁻ y in box, ENNReal.ofReal (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2)
            then (1:ℝ) else 0)) = ∫⁻ y, S.indicator (fun _ => (1:ENNReal)) (x, y)
      rw [← lintegral_indicator hboxmeas (f := fun y => ENNReal.ofReal
        (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then (1:ℝ) else 0))]
      refine lintegral_congr (fun y => ?_)
      by_cases hy : y ∈ box <;> by_cases hc : (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2)
      · rw [Set.indicator_of_mem hy, if_pos hc,
          Set.indicator_of_mem (show (x, y) ∈ S from by rw [hSdef]; exact ⟨hy, hc⟩)]
        simp
      · rw [Set.indicator_of_mem hy, if_neg hc,
          Set.indicator_of_notMem (show (x, y) ∉ S from fun h => hc h.2)]
        simp
      · rw [Set.indicator_of_notMem hy,
          Set.indicator_of_notMem (show (x, y) ∉ S from fun h => hy h.1)]
      · rw [Set.indicator_of_notMem hy,
          Set.indicator_of_notMem (show (x, y) ∉ S from fun h => hy h.1)]
    rw [hEq]
    exact hmain.aemeasurable
  -- ## The box has finite volume
  have hbox_lt : (volume : Measure (Fin (n-k) → ℝ)) box < ⊤ := by
    rw [hboxdef]
    exact (isCompact_univ_pi (fun _ : Fin (n-k) => isCompact_Icc)).measure_lt_top
  -- ## `H` is finite
  have hHfin : ∀ᵐ x ∂(volume : Measure (Fin k → ℝ)), H x < ⊤ := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    show (∫⁻ y in box, ENNReal.ofReal (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2)
          then (1:ℝ) else 0)) < ⊤
    have hle : (∫⁻ y in box, ENNReal.ofReal (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2)
          then (1:ℝ) else 0)) ≤ ∫⁻ y in box, (1 : ENNReal) := by
      refine lintegral_mono (fun y => ?_)
      rw [apply_ite ENNReal.ofReal]
      split_ifs <;> simp
    refine lt_of_le_of_lt hle ?_
    have : (∫⁻ y in box, (1 : ENNReal)) = (volume : Measure (Fin (n-k) → ℝ)) box :=
      (lintegral_indicator hboxmeas (fun _ => 1)).symm.trans (lintegral_indicator_one hboxmeas)
    rw [this]
    exact hbox_lt
  -- ## The real RHS is the `toReal` of `∫⁻ x, H x`
  have hconv : (∫ x : Fin k → ℝ, ∫ y in box,
        (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then (1:ℝ) else 0))
      = (∫⁻ x : Fin k → ℝ, H x).toReal := by
    have h1 : (∫ x : Fin k → ℝ, ∫ y in box,
          (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then (1:ℝ) else 0))
        = ∫ x : Fin k → ℝ, (H x).toReal :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => (hHval x).symm))
    rw [h1]
    exact integral_toReal hHmeas hHfin
  -- ## Pointwise identification of the two indicator integrands
  have hpoint1 : ∀ (x : Fin k → ℝ) (y : Fin (n-k) → ℝ),
      (U.indicator (fun u => ∏ i, (Set.Icc (-(1/2:ℝ)) (1/2)).indicator
          (fun _ => (1:ENNReal)) (u i)) (B.mulVec x + Bp.mulVec y))
      = S.indicator (fun _ => (1:ENNReal)) (x, y) := by
    intro x y
    by_cases hy : y ∈ box
    · have hUy : B.mulVec x + Bp.mulVec y ∈ U := (hmem x y).mpr hy
      rw [Set.indicator_of_mem hUy, prod_Icc_indicator_eq_ite]
      by_cases hc : ∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2
      · rw [if_pos hc, Set.indicator_of_mem (show (x, y) ∈ S from by rw [hSdef]; exact ⟨hy, hc⟩)]
      · rw [if_neg hc, Set.indicator_of_notMem]
        intro hcon; exact hc hcon.2
    · have hUy : B.mulVec x + Bp.mulVec y ∉ U := fun h => hy ((hmem x y).mp h)
      rw [Set.indicator_of_notMem hUy, Set.indicator_of_notMem]
      intro hcon; exact hy hcon.1
  have hstep1 : ∫⁻ u in U,
        (∏ i, (Set.Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1:ENNReal)) (u i))
      = ∫⁻ x : Fin k → ℝ, H x := by
    calc ∫⁻ u in U, (∏ i, (Set.Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1:ENNReal)) (u i))
        = ∫⁻ u, U.indicator (fun u => ∏ i, (Set.Icc (-(1/2 : ℝ)) (1/2)).indicator
              (fun _ => (1:ENNReal)) (u i)) u :=
          (lintegral_indicator hUmeas _).symm
      _ = ∫⁻ x : Fin k → ℝ, ∫⁻ y : Fin (n-k) → ℝ,
            U.indicator (fun u => ∏ i, (Set.Icc (-(1/2 : ℝ)) (1/2)).indicator
              (fun _ => (1:ENNReal)) (u i)) (B.mulVec x + Bp.mulVec y) :=
          isometricAux.lintegral_comp_mulVec_add hk B Bp hB hBp hBBp _
            ((measurable_prod_indicator (ι := Fin n)).indicator hUmeas)
      _ = ∫⁻ x : Fin k → ℝ, ∫⁻ y : Fin (n-k) → ℝ,
            S.indicator (fun _ => (1:ENNReal)) (x, y) :=
          lintegral_congr (fun x => lintegral_congr (fun y => hpoint1 x y))
      _ = ∫⁻ x : Fin k → ℝ, H x := by
          refine lintegral_congr (fun x => ?_)
          show (∫⁻ y, S.indicator (fun _ => (1:ENNReal)) (x, y))
            = ∫⁻ y in box, ENNReal.ofReal (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2)
                then (1:ℝ) else 0)
          rw [← lintegral_indicator hboxmeas (f := fun y => ENNReal.ofReal
            (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then (1:ℝ) else 0))]
          refine lintegral_congr (fun y => ?_)
          by_cases hy : y ∈ box <;> by_cases hc : (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2)
          · rw [Set.indicator_of_mem (show (x, y) ∈ S from by rw [hSdef]; exact ⟨hy, hc⟩),
              Set.indicator_of_mem hy, if_pos hc]
            simp
          · rw [Set.indicator_of_notMem (show (x, y) ∉ S from fun h => hc h.2),
              Set.indicator_of_mem hy, if_neg hc]
            simp
          · rw [Set.indicator_of_notMem (show (x, y) ∉ S from fun h => hy h.1),
              Set.indicator_of_notMem hy]
          · rw [Set.indicator_of_notMem (show (x, y) ∉ S from fun h => hy h.1),
              Set.indicator_of_notMem hy]
  -- ## `∫⁻_U` of the cube-indicator is finite
  have hPNlt : ∫⁻ u in U,
        (∏ i, (Set.Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1:ENNReal)) (u i)) < ⊤ := by
    have hle : (∫⁻ u in U,
          (∏ i, (Set.Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1:ENNReal)) (u i)))
        ≤ ∫⁻ u : Fin n → ℝ,
          (∏ i, (Set.Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1:ENNReal)) (u i)) := by
      rw [← lintegral_indicator hUmeas]
      exact lintegral_mono (fun u => by
        by_cases h : u ∈ U
        · rw [Set.indicator_of_mem h]
        · rw [Set.indicator_of_notMem h]; simp)
    refine lt_of_le_of_lt hle ?_
    have hfun : (fun u : Fin n → ℝ =>
          ∏ i, (Set.Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1:ENNReal)) (u i))
        = (Set.pi Set.univ (fun _ : Fin n => Set.Icc (-(1/2 : ℝ)) (1/2))).indicator
            (fun _ => (1:ENNReal)) := by
      funext u
      rw [prod_Icc_indicator_eq_ite, Set.indicator_apply, Set.mem_univ_pi]
      simp only [Set.mem_Icc, abs_le]
    have hcube : (∫⁻ u : Fin n → ℝ,
          (∏ i, (Set.Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1:ENNReal)) (u i))) = 1 := by
      have hmeas_cube : MeasurableSet
          (Set.pi Set.univ (fun _ : Fin n => Set.Icc (-(1/2:ℝ)) (1/2))) :=
        MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
      have hlint : (∫⁻ u : Fin n → ℝ,
            (Set.pi Set.univ (fun _ : Fin n => Set.Icc (-(1/2:ℝ)) (1/2))).indicator
              (fun _ => (1:ENNReal)) u)
          = (volume : Measure (Fin n → ℝ))
              (Set.pi Set.univ (fun _ : Fin n => Set.Icc (-(1/2:ℝ)) (1/2))) :=
        lintegral_indicator_one hmeas_cube
      rw [hfun, hlint, MeasureTheory.volume_pi_pi]
      calc (∏ i : Fin n, (volume : Measure ℝ) (Set.Icc (-(1/2:ℝ)) (1/2)))
          = ∏ _i : Fin n, (1 : ENNReal) :=
            Finset.prod_congr rfl (fun i _ => by
              rw [Real.volume_Icc, show (1/2:ℝ) - (-(1/2)) = 1 by norm_num,
                ENNReal.ofReal_one])
        _ = 1 := Finset.prod_const_one
    rw [hcube]
    exact ENNReal.one_lt_top
  have hHlt : (∫⁻ x : Fin k → ℝ, H x) < ⊤ := by rw [← hstep1]; exact hPNlt
  -- ## The two sides
  have hPN : (∫⁻ u in U,
        (∏ i, (Set.Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1:ENNReal)) (u i)))
      = ENNReal.ofReal (∫ x : Fin k → ℝ, ∫ y in box,
          (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then (1:ℝ) else 0)) := by
    rw [hstep1, hconv]
    exact (ENNReal.ofReal_toReal (ne_top_of_lt hHlt)).symm
  have hGN : (∫⁻ u in U, (∏ i, ENNReal.ofReal (Real.exp (- Real.pi * (u i)^2))))
      = ENNReal.ofReal (∏ l : Fin (n-k),
          ∫ t in Set.Icc (-(δ/2)) (δ/2), Real.exp (- Real.pi * t^2)) := by
    have hxint : (∫⁻ x : Fin k → ℝ,
          (∏ i : Fin k, ENNReal.ofReal (Real.exp (- Real.pi * (x i)^2)))) = 1 := by
      have h := lintegral_pi_prod_eq_prod (μ := fun _ : Fin k => (volume : Measure ℝ))
        (f := fun _ (t : ℝ) => Real.exp (- Real.pi * t^2))
        (fun _ t => Real.exp_nonneg _) (fun _ => integrable_gauss)
      simp only [integral_gauss] at h
      simpa [← MeasureTheory.volume_pi] using h
    have hyint : (∫⁻ y in box,
          (∏ l : Fin (n-k), ENNReal.ofReal (Real.exp (- Real.pi * (y l)^2))))
        = ∏ l : Fin (n-k), ENNReal.ofReal
            (∫ t in Set.Icc (-(δ/2)) (δ/2), Real.exp (- Real.pi * t^2)) := by
      have hmeas : (volume : Measure (Fin (n-k) → ℝ)).restrict box
          = Measure.pi (fun _ : Fin (n-k) =>
              (volume : Measure ℝ).restrict (Set.Icc (-(δ/2)) (δ/2))) := by
        rw [hboxdef, ← Measure.restrict_pi_pi (fun _ : Fin (n-k) => (volume : Measure ℝ))
            (fun _ : Fin (n-k) => Set.Icc (-(δ/2)) (δ/2)), MeasureTheory.volume_pi]
      rw [hmeas]
      have h := lintegral_pi_prod_eq_prod
        (μ := fun _ : Fin (n-k) => (volume : Measure ℝ).restrict (Set.Icc (-(δ/2)) (δ/2)))
        (f := fun _ (t : ℝ) => Real.exp (- Real.pi * t^2))
        (fun _ t => Real.exp_nonneg _) (fun _ => integrable_gauss.integrableOn)
      exact h
    calc (∫⁻ u in U, (∏ i, ENNReal.ofReal (Real.exp (- Real.pi * (u i)^2))))
        = ∫⁻ u, U.indicator (fun u => ∏ i, ENNReal.ofReal (Real.exp (- Real.pi * (u i)^2))) u :=
          (lintegral_indicator hUmeas _).symm
      _ = ∫⁻ x : Fin k → ℝ, ∫⁻ y : Fin (n-k) → ℝ,
            U.indicator (fun u => ∏ i, ENNReal.ofReal (Real.exp (- Real.pi * (u i)^2)))
              (B.mulVec x + Bp.mulVec y) :=
          isometricAux.lintegral_comp_mulVec_add hk B Bp hB hBp hBBp _
            ((Finset.measurable_prod _ (fun i _ => measurable_gauss_factor i)).indicator hUmeas)
      _ = ∫⁻ x : Fin k → ℝ, ∫⁻ y in box,
            (∏ i, ENNReal.ofReal (Real.exp (- Real.pi * ((B.mulVec x + Bp.mulVec y) i)^2))) := by
          refine lintegral_congr (fun x => ?_)
          rw [← lintegral_indicator hboxmeas (f := fun y => ∏ i, ENNReal.ofReal
            (Real.exp (- Real.pi * ((B.mulVec x + Bp.mulVec y) i)^2)))]
          refine lintegral_congr (fun y => ?_)
          by_cases h : y ∈ box
          · rw [Set.indicator_of_mem ((hmem x y).mpr h), Set.indicator_of_mem h]
          · rw [Set.indicator_of_notMem (fun hc => h ((hmem x y).mp hc)),
              Set.indicator_of_notMem h]
      _ = ∫⁻ x : Fin k → ℝ, ∫⁻ y in box,
            (∏ i : Fin k, ENNReal.ofReal (Real.exp (- Real.pi * (x i)^2)))
              * (∏ l : Fin (n-k), ENNReal.ofReal (Real.exp (- Real.pi * (y l)^2))) :=
          lintegral_congr (fun x => lintegral_congr (fun y =>
            isometricAux.ofReal_gauss_factor_mulVec B Bp hB hBp hBBp x y))
      _ = ∫⁻ x : Fin k → ℝ, (∏ i : Fin k, ENNReal.ofReal (Real.exp (- Real.pi * (x i)^2)))
            * (∫⁻ y in box,
                (∏ l : Fin (n-k), ENNReal.ofReal (Real.exp (- Real.pi * (y l)^2)))) := by
          refine lintegral_congr (fun x => ?_)
          exact lintegral_const_mul _ (Finset.measurable_prod _ (fun l _ => measurable_gauss_factor l))
      _ = (∫⁻ x : Fin k → ℝ, (∏ i : Fin k, ENNReal.ofReal (Real.exp (- Real.pi * (x i)^2))))
            * (∫⁻ y in box,
                (∏ l : Fin (n-k), ENNReal.ofReal (Real.exp (- Real.pi * (y l)^2)))) :=
          lintegral_mul_const _ (Finset.measurable_prod _ (fun i _ => measurable_gauss_factor i))
      _ = 1 * (∏ l : Fin (n-k), ENNReal.ofReal
            (∫ t in Set.Icc (-(δ/2)) (δ/2), Real.exp (- Real.pi * t^2))) := by
          rw [hxint, hyint]
      _ = ENNReal.ofReal (∏ l : Fin (n-k),
            ∫ t in Set.Icc (-(δ/2)) (δ/2), Real.exp (- Real.pi * t^2)) := by
          rw [one_mul, ← ENNReal.ofReal_prod_of_nonneg
            (fun l _ => setIntegral_nonneg measurableSet_Icc (fun t _ => Real.exp_nonneg _))]
  -- ## Conclusion
  have hLHSnn : 0 ≤ ∏ l : Fin (n-k),
      ∫ t in Set.Icc (-(δ/2)) (δ/2), Real.exp (- Real.pi * t^2) :=
    Finset.prod_nonneg (fun l _ =>
      setIntegral_nonneg measurableSet_Icc (fun t _ => Real.exp_nonneg _))
  have hRHSnn : 0 ≤ ∫ x : Fin k → ℝ, ∫ y in box,
      (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then (1:ℝ) else 0) :=
    integral_nonneg (fun x => integral_nonneg (fun y => by
      split_ifs <;> norm_num))
  have hmono := ENNReal.toReal_mono (ne_top_of_lt hPNlt) hpeakU
  rw [hGN, hPN] at hmono
  rw [ENNReal.toReal_ofReal hLHSnn, ENNReal.toReal_ofReal hRHSnn] at hmono
  simpa only [hboxdef] using hmono

end Work.BW
