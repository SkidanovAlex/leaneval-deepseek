import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
import Submission.Work.FTS.H2.Whz_Wm_sq
import Submission.Work.Elliptic.DivSinFactor
import Submission.Work.FTS.EllipticEst.RPFresh.DivSinOpen.Defs
import Submission.Work.FTS.EllSol.hkMem_slots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Bridging lemmas: two-variable `D_θ`-iterates versus one-dimensional ones -/

/-- The `θ`-slice at a fixed `z` of the two-variable iterate `D_θ^i` agrees with the
one-dimensional iterate `Dth1Iter i` of the slice. -/
theorem DthIter_slice_eq (X : ℝ → ℝ → ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i X z θ = Work.Elliptic.Dth1Iter i (fun t => X z t) θ := by
  induction i generalizing z θ with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, Work.Elliptic.Dth1Iter_succ]
      have h : (fun θ' => Work.Spaces.DthIter n X z θ')
          = fun θ' => Work.Elliptic.Dth1Iter n (fun t => X z t) θ' := by
        funext θ'
        exact ih z θ'
      simp only [Work.Spaces.Dth, Work.Elliptic.Dth1, Work.Spaces.pth]
      rw [h]

/-- `D_z` commutes with the division by a factor depending on `θ` only. -/
theorem Dz_div_const (Y : ℝ → ℝ → ℝ) (g : ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => Y z θ / g θ)
      = fun z θ => Work.Spaces.Dz Y z θ / g θ := by
  funext z θ
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [deriv_div_const, mul_div_assoc]

/-- Every iterate `D_z^j` commutes with the division by a factor depending on `θ` only. -/
theorem DzIter_div_const (Y : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ => Y z θ / g θ)
      = fun z θ => Work.Spaces.DzIter j Y z θ / g θ := by
  induction j with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      exact Dz_div_const (Work.Spaces.DzIter n Y) g

/-- **Clairaut on the open quadrant**: the `θ`-derivative of the slice of `D_z^j Φ` is the
slice of `D_z^j (∂_θΦ)`. -/
theorem deriv_DzIter_slice {Φ : ℝ → ℝ → ℝ} (hSO : Work.FTS.EllipticEst.SmoothOpen Φ)
    (j : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t => Work.Spaces.DzIter j Φ z t) θ
      = Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ := by
  have hsm : ∀ n : ℕ, ContDiffOn ℝ (↑n) (Function.uncurry Φ)
      Work.FTS.EllipticEst.Q0 := (Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mp hSO
  have hEq : Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j Φ)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth Φ)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 hsm j
  have hx : ((z, θ) : ℝ × ℝ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  simpa only [Function.uncurry, Work.Spaces.pth] using hEq hx

/-- The mixed summand of the quotient `Φ/sin 2θ` is the `D_θ`-iterate of the quotient of the
slice: `D_z^j D_θ^i (Φ/sin 2θ) = D_θ^i ((D_z^j Φ)/sin 2θ)`. -/
theorem mixed_div_eq {Φ : ℝ → ℝ → ℝ} (hSO : Work.FTS.EllipticEst.SmoothOpen Φ)
    (j i : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.mixed j i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
      = Work.Elliptic.Dth1Iter i (Work.Elliptic.SinQ (fun t => Work.Spaces.DzIter j Φ z t)) θ := by
  have hdiv : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Φ z θ / Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.RPFresh.smoothOpen_div_sin hSO
  have hsm : ∀ n : ℕ, ContDiffOn ℝ (↑n) (Function.uncurry (fun z θ => Φ z θ / Real.sin (2 * θ)))
      Work.FTS.EllipticEst.Q0 := (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hdiv
  have hEq : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i
        (Work.Spaces.DzIter j (fun z θ => Φ z θ / Real.sin (2 * θ)))))
      (Function.uncurry (Work.Spaces.mixed j i (fun z θ => Φ z θ / Real.sin (2 * θ))))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 hsm j i
  have hx : ((z, θ) : ℝ × ℝ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have h' : Work.Spaces.mixed j i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
      = Work.Spaces.DthIter i
          (Work.Spaces.DzIter j (fun z θ => Φ z θ / Real.sin (2 * θ))) z θ := (hEq hx).symm
  rw [h', DthIter_slice_eq]
  refine congrArg (fun f => Work.Elliptic.Dth1Iter i f θ) ?_
  funext t
  simp only [Work.Elliptic.SinQ]
  exact congrFun (congrFun (DzIter_div_const Φ (fun θ => Real.sin (2 * θ)) j) z) t

/-- The mixed summand of `∂_θΦ` is the `D_θ`-iterate of the slice of `D_z^j (∂_θΦ)`. -/
theorem mixed_pth_eq {Φ : ℝ → ℝ → ℝ} (hSO : Work.FTS.EllipticEst.SmoothOpen Φ)
    (j m : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
      = Work.Elliptic.Dth1Iter m (fun t => Work.Spaces.DzIter j (Work.Spaces.pth Φ) z t) θ := by
  have hsm : ∀ n : ℕ, ContDiffOn ℝ (↑n) (Function.uncurry (Work.Spaces.pth Φ))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hSO.pth
  have hEq : Set.EqOn (Function.uncurry (Work.Spaces.DthIter m
        (Work.Spaces.DzIter j (Work.Spaces.pth Φ))))
      (Function.uncurry (Work.Spaces.mixed j m (Work.Spaces.pth Φ)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 hsm j m
  have hx : ((z, θ) : ℝ × ℝ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have h' : Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
      = Work.Spaces.DthIter m (Work.Spaces.DzIter j (Work.Spaces.pth Φ)) z θ := (hEq hx).symm
  rw [h', DthIter_slice_eq]

/-! ## Elementary angular facts -/

/-- A property holding on `(0,π/2)` holds a.e. on `Iθ`. -/
lemma ae_Iθ_of_forall_Ioo {p : ℝ → Prop}
    (h : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), p θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), p θ := by
  have hμ : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
        (b := Real.pi / 2)).symm
  rw [hμ]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo h

/-- `Dth1Iter` respects equality on the open interval. -/
lemma Dth1Iter_congr_of_Ioo {g g' : ℝ → ℝ}
    (h : Set.EqOn g g' (Set.Ioo 0 (Real.pi / 2))) (m : ℕ) :
    Set.EqOn (Work.Elliptic.Dth1Iter m g) (Work.Elliptic.Dth1Iter m g')
      (Set.Ioo 0 (Real.pi / 2)) := by
  induction m with
  | zero => exact h
  | succ j ih =>
      intro θ hθ
      have hnb : Set.Ioo 0 (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
      have hev : (Work.Elliptic.Dth1Iter j g) =ᶠ[𝓝 θ] (Work.Elliptic.Dth1Iter j g') := by
        filter_upwards [hnb] with θ' hθ'
        exact ih hθ'
      rw [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1,
        Work.Elliptic.Dth1, hev.deriv_eq]

/-- Integrability is transported along an equality that holds on the open interval only. -/
lemma integrableOn_congr_of_EqOn_Ioo {f g : ℝ → ℝ}
    (h : Set.EqOn f g (Set.Ioo 0 (Real.pi / 2)))
    (hf : MeasureTheory.IntegrableOn f Work.Spaces.Iθ) : MeasureTheory.IntegrableOn g Work.Spaces.Iθ := by
  have hμ : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
        (b := Real.pi / 2)).symm
  refine hf.congr ?_
  rw [hμ]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => h hθ)

/-! ## The weight and slot identities -/

lemma wdivsin_sq (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  rw [← Work.FTS.H2.Whz_eq]
  exact (Work.FTS.H2.Whz_Wm_sq 1 zero_lt_one z θ hθ).1

lemma Wt_sq_E (α : ℝ) (hα : 0 < α) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [← Work.FTS.H2.Wm_eq]
  exact (Work.FTS.H2.Whz_Wm_sq α hα z θ hθ).2

/-- The pure-`D_z` summand of the quotient integrand, in terms of the data integrand. -/
lemma Pslot_eq (b : ℕ) (Φ : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.DzIter b (fun z' θ' => Φ z' θ' / Real.sin (2 * θ')) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 *
        ((Work.Spaces.DzIter b Φ z θ / Real.sin (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  rw [Work.Elliptic.DivSinFactor Φ b z θ hθ, mul_pow,
    wdivsin_sq z θ ⟨hθ.1.le, hθ.2.le⟩]
  ring

/-- The mixed summand of the quotient integrand, in terms of the angular data integrand. -/
lemma Mslot_eq (α : ℝ) (hα : 0 < α) (i j : ℕ) (Φ : ℝ → ℝ → ℝ)
    (hSO : Work.FTS.EllipticEst.SmoothOpen Φ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.mixed j i (fun z' θ' => Φ z' θ' / Real.sin (2 * θ')) z θ
        * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 *
        ((Work.Elliptic.Dth1Iter i
            (fun θ' => Work.Spaces.DzIter j Φ z θ' / Real.sin (2 * θ')) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
  rw [mixed_div_eq hSO j i hz hθ,
    show Work.Elliptic.SinQ (fun t => Work.Spaces.DzIter j Φ z t)
      = (fun θ' => Work.Spaces.DzIter j Φ z θ' / Real.sin (2 * θ')) from rfl,
    mul_pow, Wt_sq_E α hα z θ ⟨hθ.1.le, hθ.2.le⟩]
  ring

/-- The `η`-weighted data integrand of the slice `D_z^j Φ` is `w^{-2}` times the `j`-th pure
summand of `HkIntegrand α k (∂_θΦ)`. -/
lemma Zdata_eq (j : ℕ) (Φ : ℝ → ℝ → ℝ)
    (hSO : Work.FTS.EllipticEst.SmoothOpen Φ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hwz : Work.Spaces.w z ≠ 0) :
    (deriv (fun θ' : ℝ => Work.Spaces.DzIter j Φ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      = ((Work.Spaces.w z) ^ 2)⁻¹ *
        (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [deriv_DzIter_slice hSO j hz hθ, mul_pow,
    wdivsin_sq z θ ⟨hθ.1.le, hθ.2.le⟩]
  field_simp

/-- The `γ`-weighted data integrand of the slice `D_z^j Φ` is `w^{-2}` times the corresponding
mixed summand of `HkIntegrand α k (∂_θΦ)`. -/
lemma Mdata_eq (α : ℝ) (hα : 0 < α) (m j : ℕ) (Φ : ℝ → ℝ → ℝ)
    (hSO : Work.FTS.EllipticEst.SmoothOpen Φ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hwz : Work.Spaces.w z ≠ 0) :
    (Work.Elliptic.Dth1Iter m
        (fun θ' => deriv (fun θ'' : ℝ => Work.Spaces.DzIter j Φ z θ'') θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = ((Work.Spaces.w z) ^ 2)⁻¹ *
        (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2 := by
  have hEqOn : Set.EqOn (fun θ' : ℝ => deriv (fun θ'' : ℝ => Work.Spaces.DzIter j Φ z θ'') θ')
      (fun θ' : ℝ => Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ')
      (Set.Ioo 0 (Real.pi / 2)) := fun θ' hθ' => deriv_DzIter_slice hSO j hz hθ'
  rw [Dth1Iter_congr_of_Ioo hEqOn m hθ, ← mixed_pth_eq hSO j m hz hθ, mul_pow,
    Wt_sq_E α hα z θ ⟨hθ.1.le, hθ.2.le⟩]
  field_simp

/-! ## The per-slice hypotheses -/

/-- **The slice data**: for `z > 0` and `j ≤ k` the slice `θ ↦ D_z^j Φ z θ` is `C^∞` on the open
interval, vanishes at both endpoints and its `η`- and `γ`-weighted data integrals are honest. -/
theorem sliceData {k : ℕ} {α : ℝ} {Φ : ℝ → ℝ → ℝ} (hSO : Work.FTS.EllipticEst.SmoothOpen Φ)
    (hsl : ∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ) (Set.Ioo 0 (Real.pi / 2)))
    (ht0 : ∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → Filter.Tendsto
      (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (ht1 : ∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → Filter.Tendsto
      (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.pth Φ)) (hα : 0 < α)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) (hzpos : 0 < z) :
    ∀ j : ℕ, j ≤ k →
      ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ)
          (Set.Ioo 0 (Real.pi / 2)) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) ∧
        MeasureTheory.IntegrableOn
          (fun θ : ℝ => (deriv (fun θ' : ℝ => Work.Spaces.DzIter j Φ z θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ ∧
        (∀ m : ℕ, 1 ≤ m → m ≤ k - j → MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (fun θ' : ℝ =>
              deriv (fun θ'' : ℝ => Work.Spaces.DzIter j Φ z θ'') θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ) := by
  intro j hj
  have hsmj : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    simpa only [Work.Stability.smoothOrder] using hsl z hzpos j hj
  have h1 := (hkMem_slots α k hSO hmem hz hzpos hα).1 j hj
  have h1' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun θ' : ℝ => Work.Spaces.DzIter j Φ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
    refine h1.congr ?_
    filter_upwards [ae_Iθ_of_forall_Ioo
      (fun θ hθ => deriv_DzIter_slice hSO j hzpos hθ)] with θ hθ
    show (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      = (deriv (fun θ' : ℝ => Work.Spaces.DzIter j Φ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    rw [← hθ]
  refine ⟨hsmj, ht0 z hzpos j hj, ht1 z hzpos j hj, h1', fun m hm1 hmkj => ?_⟩
  have hmj : m + j ≤ k := by omega
  have h2 := (hkMem_slots α k hSO hmem hz hzpos hα).2 m j hm1 hmj
  have hEqOn : Set.EqOn (fun θ' : ℝ => deriv (fun θ'' : ℝ => Work.Spaces.DzIter j Φ z θ'') θ')
      (fun θ' : ℝ => Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ')
      (Set.Ioo 0 (Real.pi / 2)) := fun θ' hθ' => deriv_DzIter_slice hSO j hzpos hθ'
  refine integrableOn_congr_of_EqOn_Ioo ?_ h2
  intro θ hθ
  show (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = (Work.Elliptic.Dth1Iter m (fun θ' : ℝ => deriv (fun θ'' : ℝ =>
          Work.Spaces.DzIter j Φ z θ'') θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
  rw [Dth1Iter_congr_of_Ioo hEqOn m hθ, ← mixed_pth_eq hSO j m hzpos hθ]

end Work.FTS.EllSol
