import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The divergence theorem for a compactly supported `C¹` vector field on `ℝ³`

`Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt`: if `G : ℝ³ → ℝ³` is continuous with
compact support, differentiable *everywhere* with derivative `fderiv ℝ G`, and its divergence
`div G = trace (fderiv ℝ G ·)` is integrable, then `∫ x, div G x = 0`.

The proof is the classical one.

* The trace of `fderiv ℝ G x` in the standard basis is the sum of the partial derivatives of the
  components, `∑ i, ∂ᵢGᵢ`;
* putting `G` inside the box `[-R,R]³` large enough to contain its support, Mathlib's Bochner
  divergence theorem on a box (`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`)
  identifies the integral of the divergence with the sum of the six face integrals — all of which
  vanish, the faces lying outside the support;
* `div G` vanishes off the box because `G` is *locally zero* there, so the box integral is the
  integral over `ℝ³`.

Everything is transported along the linear isometry `WithLp.toLp 2 : (Fin 3 → ℝ) ≃ᵢ ℝ³`.

This lemma is the input that turns a distributionally divergence-free, compactly supported,
`C¹` field into a pointwise divergence-free one in the pressure reconstruction
(`Work.FTS.PressureOn`); it is the "Weyl/Liouville" step of the classical route.
-/

noncomputable section

open FiniteTimeSingularity Set MeasureTheory

open scoped Topology

namespace Work.FTS.PressureOn

/-! ## The canonical linear isometries `(Fin 3 → ℝ) ≃ ℝ³` -/

/-- The continuous linear equivalence `(Fin 3 → ℝ) ≃L[ℝ] ℝ³` whose underlying map is
`WithLp.toLp 2`. -/
def toLpCLE : (Fin 3 → ℝ) ≃L[ℝ] R3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm

@[simp] lemma toLpCLE_apply (x : Fin 3 → ℝ) : toLpCLE x = WithLp.toLp 2 x := rfl

lemma toLpCLE_measurableEmbedding : MeasurableEmbedding (⇑toLpCLE) :=
  toLpCLE.toHomeomorph.measurableEmbedding

lemma toLpCLE_measurePreserving : MeasurePreserving (⇑toLpCLE) volume volume :=
  PiLp.volume_preserving_toLp (Fin 3)

/-- `WithLp.toLp 2` as a continuous linear map. -/
def toLpCLM : (Fin 3 → ℝ) →L[ℝ] R3 := toLpCLE.toContinuousLinearMap

@[simp] lemma toLpCLM_apply (x : Fin 3 → ℝ) : toLpCLM x = WithLp.toLp 2 x := rfl

/-- `WithLp.ofLp` as a continuous linear map. -/
def ofLpCLM : R3 →L[ℝ] (Fin 3 → ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ))

@[simp] lemma ofLpCLM_apply (x : R3) : ofLpCLM x = WithLp.ofLp x := rfl

/-! ## The trace of an endomorphism of `ℝ³` in the standard basis -/

/-- The trace of an endomorphism of `ℝ³` is the sum of the diagonal entries of its matrix in the
standard (orthonormal) basis. -/
lemma trace_eq_sum_single (f : R3 →L[ℝ] R3) :
    f.trace ℝ R3 = ∑ i, (f (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) i := by
  rw [show f.trace ℝ R3 = (f : R3 →ₗ[ℝ] R3).trace ℝ R3 from rfl]
  rw [LinearMap.trace_eq_sum_inner (f : R3 →ₗ[ℝ] R3) (EuclideanSpace.basisFun (Fin 3) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.basisFun_apply]
  simp [PiLp.inner_apply]

/-- The divergence of `G` at `y` is the sum of the diagonal entries of the Jacobian of `G` at `y`
in the standard basis. -/
lemma div_eq_sum_single (G : R3 → R3) (y : R3) :
    div G y = ∑ i, (fderiv ℝ G y (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) i := by
  rw [div, trace_eq_sum_single]

/-! ## The transport of a field to the coordinate space `Fin 3 → ℝ` -/

/-- The transport of `G : ℝ³ → ℝ³` to a vector field on the coordinate space `Fin 3 → ℝ`. -/
def transport (G : R3 → R3) : (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  fun x => WithLp.ofLp (G (WithLp.toLp 2 x))

@[simp] lemma transport_apply (G : R3 → R3) (x : Fin 3 → ℝ) :
    transport G x = WithLp.ofLp (G (WithLp.toLp 2 x)) := rfl

@[simp] lemma transport_apply_coord (G : R3 → R3) (x : Fin 3 → ℝ) (i : Fin 3) :
    transport G x i = (G (WithLp.toLp 2 x)) i := rfl

lemma continuous_transport (G : R3 → R3) (h : Continuous G) : Continuous (transport G) :=
  ofLpCLM.continuous.comp (h.comp toLpCLM.continuous)

/-- The candidate derivative of the transported field at `x`: the Jacobian of `G` at `toLp x`,
conjugated by the isometry. -/
def fderivTransport (G : R3 → R3) (x : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ofLpCLM.comp ((fderiv ℝ G (toLpCLM x)).comp toLpCLM)

lemma hasFDerivAt_transport {G : R3 → R3} {x : Fin 3 → ℝ}
    (h : HasFDerivAt G (fderiv ℝ G (toLpCLM x)) (toLpCLM x)) :
    HasFDerivAt (transport G) (fderivTransport G x) x := by
  have h1 : HasFDerivAt (fun x : Fin 3 → ℝ => G (toLpCLM x))
      ((fderiv ℝ G (toLpCLM x)).comp toLpCLM) x :=
    h.comp x (ContinuousLinearMap.hasFDerivAt toLpCLM)
  have h2 := (ContinuousLinearMap.hasFDerivAt ofLpCLM).comp x h1
  simpa [fderivTransport, transport, Function.comp_def] using h2

lemma sum_fderivTransport (G : R3 → R3) (x : Fin 3 → ℝ) :
    ∑ i, fderivTransport G x (Pi.single i (1 : ℝ)) i = div G (toLpCLM x) := by
  rw [div_eq_sum_single]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [fderivTransport, ContinuousLinearMap.comp_apply, toLpCLM_apply]

lemma integrable_div_transport (G : R3 → R3) (h : Integrable (div G)) :
    Integrable (fun x : Fin 3 → ℝ => div G (toLpCLM x)) := by
  have hiff := toLpCLE_measurePreserving.integrable_comp_emb toLpCLE_measurableEmbedding
    (g := div G)
  refine hiff.mpr ?_ |>.congr ?_
  · exact h
  · filter_upwards with x
    simp

lemma integral_div_transport (G : R3 → R3) :
    (∫ x : Fin 3 → ℝ, div G (toLpCLM x)) = ∫ y : R3, div G y := by
  have h := toLpCLE_measurePreserving.integral_comp toLpCLE_measurableEmbedding
    (g := div G)
  simpa [Function.comp_def] using h

/-! ## The support bound -/

/-- Off a large ball both `G` and its divergence vanish, and `G` is *locally* zero there, so its
derivative — hence the trace of its derivative — vanishes as well. -/
lemma exists_norm_supp_bound (G : R3 → R3) (hcs : HasCompactSupport G) :
    ∃ R : ℝ, 0 < R ∧ ∀ y : R3, R ≤ ‖y‖ → G y = 0 ∧ div G y = 0 := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hcs.isBounded
  refine ⟨|C| + 1, by positivity, fun y hy => ?_⟩
  have hnotmem : y ∉ tsupport G := fun hmem => by
    have h1 : ‖y‖ ≤ C := hC y hmem
    have h2 : C ≤ |C| := le_abs_self C
    linarith
  refine ⟨image_eq_zero_of_notMem_tsupport hnotmem, ?_⟩
  have hG0 : G =ᶠ[𝓝 y] 0 := by
    have hopen : IsOpen (tsupport G)ᶜ := (isClosed_tsupport G).isOpen_compl
    filter_upwards [hopen.mem_nhds hnotmem] with z hz
    exact image_eq_zero_of_notMem_tsupport hz
  have hzero : fderiv ℝ G y = 0 := by
    rw [← hG0.symm.fderiv_eq]
    simp
  simp [div, hzero]

lemma transport_coord_eq_zero (G : R3 → R3) {R : ℝ}
    (hR : ∀ y : R3, R ≤ ‖y‖ → G y = 0) (y : Fin 3 → ℝ) (i : Fin 3) (hy : R ≤ |y i|) :
    transport G y i = 0 := by
  have h1 : G (WithLp.toLp 2 y) = 0 := by
    apply hR
    have h2 : ‖(WithLp.ofLp (WithLp.toLp 2 y)) i‖ ≤ ‖(WithLp.toLp 2 y : R3)‖ :=
      PiLp.norm_apply_le (WithLp.toLp 2 y : R3) i
    simpa using le_trans hy (by simpa using h2)
  simp [transport, h1]

/-- The face integral of `G` over the hyperplane `{x i = c}` with `|c| ≥ R` vanishes, since the
face lies outside the support of `G`. -/
lemma face_integral_zero (G : R3 → R3) {R c : ℝ}
    (hR : ∀ y : R3, R ≤ ‖y‖ → G y = 0) (hc : R ≤ |c|)
    (i : Fin 3) (s : Set (Fin 2 → ℝ)) :
    (∫ x : Fin 2 → ℝ in s, transport G (i.insertNth c x) i) = 0 := by
  have h : ∀ x : Fin 2 → ℝ, transport G (i.insertNth c x) i = 0 := by
    intro x
    apply transport_coord_eq_zero G hR
    rw [Fin.insertNth_apply_same]
    exact hc
  rw [show (fun x : Fin 2 → ℝ => transport G (i.insertNth c x) i) = fun _ => 0 from funext h]
  simp

/-! ## The divergence theorem on one box -/

/-- The divergence theorem of Mathlib, specialised to the transported field, on a box whose
interior contains the support of `G`. -/
lemma box_identity {G : R3 → R3} (hcont : Continuous G)
    (hdiff : ∀ y : R3, HasFDerivAt G (fderiv ℝ G y) y)
    (hint : Integrable (div G))
    (a b : Fin 3 → ℝ) (hle : a ≤ b) :
    (∫ x in Set.Icc a b, div G (toLpCLM x)) =
      ∑ i, ((∫ x : Fin 2 → ℝ in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
              transport G (i.insertNth (b i) x) i) -
            (∫ x : Fin 2 → ℝ in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
              transport G (i.insertNth (a i) x) i)) := by
  have hfun : (fun x : Fin 3 → ℝ => ∑ i, fderivTransport G x (Pi.single i (1 : ℝ)) i)
      = fun x => div G (toLpCLM x) := funext (sum_fderivTransport G)
  have hInt : IntegrableOn
      (fun x : Fin 3 → ℝ => ∑ i, fderivTransport G x (Pi.single i (1 : ℝ)) i) (Set.Icc a b) := by
    rw [hfun]
    exact (integrable_div_transport G hint).integrableOn
  have hbox := MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable (n := 2) a b hle
    (transport G) (fderivTransport G) (∅ : Set (Fin 3 → ℝ)) Set.countable_empty
    (continuous_transport G hcont).continuousOn
    (fun x _ => hasFDerivAt_transport (hdiff (toLpCLM x)))
    hInt
  rw [hfun] at hbox
  exact hbox

/-! ## The main theorem -/

theorem integral_div_eq_zero_of_hasFDerivAt (G : R3 → R3) (hcs : HasCompactSupport G)
    (hcont : Continuous G) (hdiff : ∀ x : R3, HasFDerivAt G (fderiv ℝ G x) x)
    (hint : MeasureTheory.Integrable (FiniteTimeSingularity.div G)) :
    ∫ x : R3, FiniteTimeSingularity.div G x = 0 := by
  obtain ⟨R, hRpos, hR⟩ := exists_norm_supp_bound G hcs
  have hRsupp : ∀ y : R3, R ≤ ‖y‖ → G y = 0 := fun y hy => (hR y hy).1
  have hRdiv : ∀ y : R3, R ≤ ‖y‖ → div G y = 0 := fun y hy => (hR y hy).2
  have hInt : Integrable (fun x : Fin 3 → ℝ => div G (toLpCLM x)) :=
    integrable_div_transport G hint
  -- the box `[-R,R]³`
  let a : Fin 3 → ℝ := fun _ => -R
  let b : Fin 3 → ℝ := fun _ => R
  have hle : a ≤ b := by
    intro i
    show -R ≤ R
    linarith [hRpos]
  have hmem : ∀ x : Fin 3 → ℝ, (x ∈ Set.Icc a b ↔ ∀ i, -R ≤ x i ∧ x i ≤ R) := by
    intro x
    rw [Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩ i
      rw [Pi.le_def] at h1 h2
      exact ⟨h1 i, h2 i⟩
    · intro h
      refine ⟨?_, ?_⟩
      · rw [Pi.le_def]; intro i; exact (h i).1
      · rw [Pi.le_def]; intro i; exact (h i).2
  -- all six faces vanish
  have hface : ∀ i : Fin 3, R ≤ |b i| ∧ R ≤ |a i| := by
    intro i
    constructor
    · show R ≤ |R|
      rw [abs_of_nonneg hRpos.le]
    · show R ≤ |-R|
      rw [abs_neg, abs_of_nonneg hRpos.le]
  -- the divergence vanishes outside the box
  have hcompl : ∀ x : Fin 3 → ℝ, x ∉ Set.Icc a b → div G (toLpCLM x) = 0 := by
    intro x hx
    apply hRdiv
    by_contra hlt
    simp only [not_le] at hlt
    apply hx
    rw [hmem]
    intro i
    have h1 : |x i| ≤ ‖toLpCLM x‖ := by
      have h2 := PiLp.norm_apply_le (toLpCLM x) i
      simpa using h2
    have h3 : |x i| < R := lt_of_le_of_lt h1 hlt
    obtain ⟨h4, h5⟩ := abs_lt.mp h3
    exact ⟨by linarith, by linarith⟩
  have hbox := box_identity hcont hdiff hint a b hle
  have hsum : (∑ i : Fin 3,
      ((∫ x : Fin 2 → ℝ in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          transport G (i.insertNth (b i) x) i) -
        (∫ x : Fin 2 → ℝ in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          transport G (i.insertNth (a i) x) i))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [face_integral_zero G hRsupp (hface i).1 i _, 
      face_integral_zero G hRsupp (hface i).2 i _, sub_zero]
  have hzero : (∫ x in Set.Icc a b, div G (toLpCLM x)) = 0 := by
    rw [hbox, hsum]
  have hfull : (∫ x in Set.Icc a b, div G (toLpCLM x))
      = ∫ x : Fin 3 → ℝ, div G (toLpCLM x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hcompl
  rw [hfull, integral_div_transport G] at hzero
  exact hzero

end Work.FTS.PressureOn
