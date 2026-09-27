import Mathlib
import Submission.Work.Drive.N2Lead.twistDefs
import Submission.Work.Drive.N2C.defs

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Function

noncomputable section

/-! ## The supporting lemmas -/

abbrev tpTop : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### The rotations of `ℝ³` -/

theorem contDiff_rot02 : ContDiff ℝ tpTop (Function.uncurry rot02) := by
  have h : ContDiff ℝ tpTop (fun p : ℝ × E3 => (fun i : Fin 3 => rot02 p.1 p.2 i)) := by
    rw [contDiff_pi]
    intro i
    fin_cases i <;> · simp [rot02]; fun_prop
  convert ((EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff).comp h using 1
  ext p : 1
  rw [Function.uncurry_apply_pair]
  simp [EuclideanSpace.equiv, WithLp.toLp_ofLp]

theorem contDiff_rot12 : ContDiff ℝ tpTop (Function.uncurry rot12) := by
  have h : ContDiff ℝ tpTop (fun p : ℝ × E3 => (fun i : Fin 3 => rot12 p.1 p.2 i)) := by
    rw [contDiff_pi]
    intro i
    fin_cases i <;> · simp [rot12]; fun_prop
  convert ((EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff).comp h using 1
  ext p : 1
  rw [Function.uncurry_apply_pair]
  simp [EuclideanSpace.equiv, WithLp.toLp_ofLp]

@[simp] theorem rot02_zero (v : E3) : rot02 0 v = v := by
  ext i; fin_cases i <;> simp [rot02]

@[simp] theorem rot12_zero (v : E3) : rot12 0 v = v := by
  ext i; fin_cases i <;> simp [rot12]

theorem rot02_add (t t' : ℝ) (v : E3) : rot02 t (rot02 t' v) = rot02 (t + t') v := by
  ext i; fin_cases i <;> simp [rot02, Real.cos_add, Real.sin_add] <;> ring

theorem rot12_add (t t' : ℝ) (v : E3) : rot12 t (rot12 t' v) = rot12 (t + t') v := by
  ext i; fin_cases i <;> simp [rot12, Real.cos_add, Real.sin_add] <;> ring

@[simp] theorem rot02_second (t : ℝ) (v : E3) : (rot02 t v) 1 = v 1 := by simp [rot02]

@[simp] theorem rot12_first (t : ℝ) (v : E3) : (rot12 t v) 0 = v 0 := by simp [rot12]

theorem rot02_pi (v : E3) : rot02 Real.pi v = WithLp.toLp 2 ![-v 0, v 1, -v 2] := by
  ext i; fin_cases i <;> simp [rot02, Real.cos_pi, Real.sin_pi]

theorem rot12_neg_pi (v : E3) : rot12 (-Real.pi) v = WithLp.toLp 2 ![v 0, -v 1, -v 2] := by
  ext i; fin_cases i <;> simp [rot12, Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi]

/-! ### The slab twists -/

/-- The angle of the horizontal slab twist. -/
def twistAngleY (a : ℝ) (v : E3) : ℝ := Real.pi * Real.smoothTransition ((a - v 1) / (2 * a))

/-- The angle of the vertical slab twist. -/
def twistAngleX (ε : ℝ) (v : E3) : ℝ := Real.pi * Real.smoothTransition ((v 0 + ε) / (2 * ε))

theorem twistY_eq (a s : ℝ) (v : E3) : twistY a s v = rot02 (s * twistAngleY a v) v := by
  show rot02 (s * Real.pi * Real.smoothTransition ((a - v 1) / (2 * a))) v
      = rot02 (s * (Real.pi * Real.smoothTransition ((a - v 1) / (2 * a)))) v
  rw [mul_assoc]

theorem twistX_eq (ε s : ℝ) (v : E3) : twistX ε s v = rot12 (s * twistAngleX ε v) v := by
  show rot12 (s * Real.pi * Real.smoothTransition ((v 0 + ε) / (2 * ε))) v
      = rot12 (s * (Real.pi * Real.smoothTransition ((v 0 + ε) / (2 * ε)))) v
  rw [mul_assoc]

@[simp] theorem twistY_first (a s : ℝ) (v : E3) : (twistY a s v) 1 = v 1 := by
  rw [twistY_eq]; simp

@[simp] theorem twistX_first (ε s : ℝ) (v : E3) : (twistX ε s v) 0 = v 0 := by
  rw [twistX_eq]; simp

@[simp] theorem twistY_zero (a : ℝ) (v : E3) : twistY a 0 v = v := by
  rw [twistY_eq]; simp

@[simp] theorem twistX_zero (ε : ℝ) (v : E3) : twistX ε 0 v = v := by
  rw [twistX_eq]; simp

theorem twistY_comp (a s s' : ℝ) (v : E3) : twistY a s (twistY a s' v) = twistY a (s + s') v := by
  have h2 : twistAngleY a (twistY a s' v) = twistAngleY a v := by simp [twistAngleY]
  rw [twistY_eq a s (twistY a s' v), h2, twistY_eq a s' v, rot02_add, twistY_eq a (s + s') v]
  congr 1
  ring

theorem twistX_comp (ε s s' : ℝ) (v : E3) : twistX ε s (twistX ε s' v) = twistX ε (s + s') v := by
  have h2 : twistAngleX ε (twistX ε s' v) = twistAngleX ε v := by simp [twistAngleX]
  rw [twistX_eq ε s (twistX ε s' v), h2, twistX_eq ε s' v, rot12_add, twistX_eq ε (s + s') v]
  congr 1
  ring

theorem twistY_eq_self_of_le {a s : ℝ} (ha : 0 < a) {v : E3} (hv : a ≤ v 1) : twistY a s v = v := by
  have h : (a - v 1) / (2 * a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hst : Real.smoothTransition ((a - v 1) / (2 * a)) = 0 := Real.smoothTransition.zero_of_nonpos h
  rw [twistY_eq, show twistAngleY a v = 0 by simp [twistAngleY, hst]]
  simp

theorem twistY_one_of_le {a : ℝ} (ha : 0 < a) {v : E3} (hv : v 1 ≤ -a) :
    twistY a 1 v = WithLp.toLp 2 ![-v 0, v 1, -v 2] := by
  have h : 1 ≤ (a - v 1) / (2 * a) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hst : Real.smoothTransition ((a - v 1) / (2 * a)) = 1 := Real.smoothTransition.one_of_one_le h
  rw [twistY_eq, show twistAngleY a v = Real.pi by simp [twistAngleY, hst], one_mul, rot02_pi]

theorem twistX_eq_self_of_le {ε s : ℝ} (hε : 0 < ε) {v : E3} (hv : v 0 ≤ -ε) : twistX ε s v = v := by
  have h : (v 0 + ε) / (2 * ε) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hst : Real.smoothTransition ((v 0 + ε) / (2 * ε)) = 0 := Real.smoothTransition.zero_of_nonpos h
  rw [twistX_eq, show twistAngleX ε v = 0 by simp [twistAngleX, hst]]
  simp

theorem twistX_neg_one_of_le {ε : ℝ} (hε : 0 < ε) {v : E3} (hv : ε ≤ v 0) :
    twistX ε (-1) v = WithLp.toLp 2 ![v 0, -v 1, -v 2] := by
  have h : 1 ≤ (v 0 + ε) / (2 * ε) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hst : Real.smoothTransition ((v 0 + ε) / (2 * ε)) = 1 := Real.smoothTransition.one_of_one_le h
  rw [twistX_eq, show twistAngleX ε v = Real.pi by simp [twistAngleX, hst], neg_one_mul,
    rot12_neg_pi]

/-! ### Smoothness of the twists -/

theorem contDiff_twistY_neg (a : ℝ) : ContDiff ℝ tpTop (fun p : ℝ × E3 => twistY a (-p.1) p.2) := by
  have h : ContDiff ℝ tpTop (fun p : ℝ × E3 => (fun i : Fin 3 => twistY a (-p.1) p.2 i)) := by
    rw [contDiff_pi]
    intro i
    fin_cases i <;> · simp [twistY, rot02]; fun_prop
  convert ((EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff).comp h using 1
  ext p : 1
  simp [EuclideanSpace.equiv, WithLp.toLp_ofLp]

theorem contDiff_twistY (a : ℝ) : ContDiff ℝ tpTop (fun p : ℝ × E3 => twistY a p.1 p.2) := by
  have h : ContDiff ℝ tpTop (fun p : ℝ × E3 => (fun i : Fin 3 => twistY a p.1 p.2 i)) := by
    rw [contDiff_pi]
    intro i
    fin_cases i <;> · simp [twistY, rot02]; fun_prop
  convert ((EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff).comp h using 1
  ext p : 1
  simp [EuclideanSpace.equiv, WithLp.toLp_ofLp]

theorem contDiff_twistX_neg (ε : ℝ) : ContDiff ℝ tpTop (fun p : ℝ × E3 => twistX ε (-p.1) p.2) := by
  have h : ContDiff ℝ tpTop (fun p : ℝ × E3 => (fun i : Fin 3 => twistX ε (-p.1) p.2 i)) := by
    rw [contDiff_pi]
    intro i
    fin_cases i <;> · simp [twistX, rot12]; fun_prop
  convert ((EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff).comp h using 1
  ext p : 1
  simp [EuclideanSpace.equiv, WithLp.toLp_ofLp]

theorem contDiff_twistX (ε : ℝ) : ContDiff ℝ tpTop (fun p : ℝ × E3 => twistX ε p.1 p.2) := by
  have h : ContDiff ℝ tpTop (fun p : ℝ × E3 => (fun i : Fin 3 => twistX ε p.1 p.2 i)) := by
    rw [contDiff_pi]
    intro i
    fin_cases i <;> · simp [twistX, rot12]; fun_prop
  convert ((EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff).comp h using 1
  ext p : 1
  simp [EuclideanSpace.equiv, WithLp.toLp_ofLp]

/-! ### Ambient paths -/

/-- A slice each of whose derivatives is injective follows from a smooth *left* inverse, by the
chain rule. -/
theorem AmbientPath.of_leftInverse {F G : ℝ → E3 → E3}
    (hF : ContDiff ℝ tpTop (Function.uncurry F)) (hG : ContDiff ℝ tpTop (Function.uncurry G))
    (hGF : ∀ s v, G s (F s v) = v) (h0 : ∀ v, F 0 v = v) : AmbientPath F where
  smooth := hF
  inj := fun s v w hvw => by simpa [hGF] using congrArg (G s) hvw
  imm := fun s w => by
    have hFd : DifferentiableAt ℝ (F s) w := by
      have hd : DifferentiableAt ℝ (Function.uncurry F) (s, w) :=
        hF.differentiable (by simp) (s, w)
      have hin : DifferentiableAt ℝ (fun v : E3 => (s, v)) w := by fun_prop
      have := hd.comp w hin
      simpa [Function.uncurry, Function.comp_def] using this
    have hGd : DifferentiableAt ℝ (G s) (F s w) := by
      have hd : DifferentiableAt ℝ (Function.uncurry G) (s, F s w) :=
        hG.differentiable (by simp) (s, F s w)
      have hin : DifferentiableAt ℝ (fun v : E3 => (s, v)) (F s w) := by fun_prop
      have := hd.comp (F s w) hin
      simpa [Function.uncurry, Function.comp_def] using this
    have hid : ((fderiv ℝ (G s) (F s w)).comp (fderiv ℝ (F s) w)) = ContinuousLinearMap.id ℝ E3 := by
      have h1 : (fun v : E3 => G s (F s v)) = fun v => v := funext (hGF s)
      have h2 : fderiv ℝ (fun v : E3 => G s (F s v)) w
          = (fderiv ℝ (G s) (F s w)).comp (fderiv ℝ (F s) w) := fderiv_comp w hGd hFd
      rw [← h2, h1]
      simp
    intro u u' huu
    have key : ∀ u : E3, (fderiv ℝ (F s) w) u = 0 → u = 0 := by
      intro u hu
      calc u = (ContinuousLinearMap.id ℝ E3) u := rfl
        _ = ((fderiv ℝ (G s) (F s w)).comp (fderiv ℝ (F s) w)) u := by rw [hid]
        _ = (fderiv ℝ (G s) (F s w)) ((fderiv ℝ (F s) w) u) := rfl
        _ = (fderiv ℝ (G s) (F s w)) 0 := by rw [hu]
        _ = 0 := map_zero _
    have hsub : (fderiv ℝ (F s) w) (u - u') = 0 := by rw [map_sub, huu, sub_self]
    exact sub_eq_zero.mp (key (u - u') hsub)
  zero := h0

theorem ambientPath_twistY (a : ℝ) : AmbientPath (fun s => twistY a (-s)) :=
  AmbientPath.of_leftInverse (F := fun s => twistY a (-s)) (G := fun s => twistY a s)
    (contDiff_twistY_neg a) (contDiff_twistY a)
    (fun s v => by rw [twistY_comp, add_neg_cancel, twistY_zero])
    (fun v => by simp)

theorem ambientPath_twistX (ε : ℝ) : AmbientPath (fun s => twistX ε (-s)) :=
  AmbientPath.of_leftInverse (F := fun s => twistX ε (-s)) (G := fun s => twistX ε s)
    (contDiff_twistX_neg ε) (contDiff_twistX ε)
    (fun s v => by rw [twistX_comp, add_neg_cancel, twistX_zero])
    (fun v => by simp)

/-! ### The vertical push -/

/-- The vertical profile of the push, one-dimensional: `y ↦ y + st s · D · (2 st ((y+ε)/(2ε)) − 1)`. -/
def pushProf (D ε s : ℝ) (y : ℝ) : ℝ :=
  y + Real.smoothTransition s * D * (2 * Real.smoothTransition ((y + ε) / (2 * ε)) - 1)

theorem pushY_eq_prof (D ε s : ℝ) (v : E3) :
    pushY D ε s v = WithLp.toLp 2 ![v 0, pushProf D ε s (v 1), v 2] := rfl

@[simp] theorem pushY_apply_zero (D ε s : ℝ) (v : E3) : (pushY D ε s v) 0 = v 0 := by
  rw [pushY_eq_prof]; simp

@[simp] theorem pushY_apply_one (D ε s : ℝ) (v : E3) : (pushY D ε s v) 1 = pushProf D ε s (v 1) := by
  rw [pushY_eq_prof]; simp

@[simp] theorem pushY_apply_two (D ε s : ℝ) (v : E3) : (pushY D ε s v) 2 = v 2 := by
  rw [pushY_eq_prof]; simp

theorem pushProf_sub_mono (D ε s : ℝ) (hε : 0 < ε) (hD : 0 ≤ D) :
    Monotone fun y : ℝ => pushProf D ε s y - y := by
  have hτ : 0 ≤ Real.smoothTransition s * D := mul_nonneg (Real.smoothTransition.nonneg s) hD
  have hfun : (fun y : ℝ => pushProf D ε s y - y)
      = fun y : ℝ => Real.smoothTransition s * D *
          (2 * Real.smoothTransition ((y + ε) / (2 * ε)) - 1) := by
    funext y; simp [pushProf]
  rw [hfun]
  intro y y' hyy
  have h2ε : (0:ℝ) < 2 * ε := by linarith
  have harg : ((y + ε) / (2 * ε)) ≤ ((y' + ε) / (2 * ε)) :=
    div_le_div_of_nonneg_right (by linarith) h2ε.le
  have hst : Real.smoothTransition ((y + ε) / (2 * ε))
      ≤ Real.smoothTransition ((y' + ε) / (2 * ε)) := Real.smoothTransition.monotone harg
  have h2 : 2 * Real.smoothTransition ((y + ε) / (2 * ε)) - 1
      ≤ 2 * Real.smoothTransition ((y' + ε) / (2 * ε)) - 1 := by linarith
  exact mul_le_mul_of_nonneg_left h2 hτ

theorem pushProf_sub_le (D ε s : ℝ) (hε : 0 < ε) (hD : 0 ≤ D) {y y' : ℝ} (h : y ≤ y') :
    y' - y ≤ pushProf D ε s y' - pushProf D ε s y := by
  have hmono := pushProf_sub_mono D ε s hε hD h
  linarith

theorem strictMono_pushProf (D ε s : ℝ) (hε : 0 < ε) (hD : 0 ≤ D) :
    StrictMono (pushProf D ε s) := by
  intro y y' hyy
  have := pushProf_sub_le D ε s hε hD hyy.le
  linarith

theorem differentiable_pushProf (D ε s : ℝ) (y : ℝ) : DifferentiableAt ℝ (pushProf D ε s) y := by
  unfold pushProf
  fun_prop

theorem deriv_pushProf_ge_one (D ε s : ℝ) (hε : 0 < ε) (hD : 0 ≤ D) (y : ℝ) :
    1 ≤ deriv (pushProf D ε s) y := by
  have hmono : Monotone (fun z : ℝ => pushProf D ε s z - z) := pushProf_sub_mono D ε s hε hD
  have hle : 0 ≤ deriv (fun z : ℝ => pushProf D ε s z - z) y := Monotone.deriv_nonneg hmono
  have hd : deriv (pushProf D ε s) y = 1 + deriv (fun z : ℝ => pushProf D ε s z - z) y := by
    have hHd : DifferentiableAt ℝ (fun z : ℝ => pushProf D ε s z - z) y :=
      (differentiable_pushProf D ε s y).sub (differentiableAt_id)
    have h1 : HasDerivAt (fun z : ℝ => z + (pushProf D ε s z - z))
        (1 + deriv (fun z : ℝ => pushProf D ε s z - z) y) y :=
      (hasDerivAt_id y).add hHd.hasDerivAt
    have hcongr : (fun z : ℝ => z + (pushProf D ε s z - z)) = pushProf D ε s := by
      funext z; ring
    rw [hcongr] at h1
    exact h1.deriv
  linarith

theorem eq_of_apply_eq {u u' : E3} (h : ∀ i : Fin 3, u i = u' i) : u = u' := by
  rw [← WithLp.toLp_ofLp 2 u, ← WithLp.toLp_ofLp 2 u']
  congr 1
  funext i
  exact h i

theorem pushY_injective (D ε s : ℝ) (hε : 0 < ε) (hD : 0 ≤ D) :
    Function.Injective (pushY D ε s) := by
  intro v v' hv
  have h0 : v 0 = v' 0 := by simpa using congrArg (fun w : E3 => w 0) hv
  have h2 : v 2 = v' 2 := by simpa using congrArg (fun w : E3 => w 2) hv
  have hm : pushProf D ε s (v 1) = pushProf D ε s (v' 1) := by
    simpa using congrArg (fun w : E3 => w 1) hv
  have h1 : v 1 = v' 1 := (strictMono_pushProf D ε s hε hD).injective hm
  exact eq_of_apply_eq (fun i => by fin_cases i <;> assumption)

theorem contDiff_pushY (D ε : ℝ) : ContDiff ℝ tpTop (Function.uncurry (pushY D ε)) := by
  have h : ContDiff ℝ tpTop (fun p : ℝ × E3 => (fun i : Fin 3 => pushY D ε p.1 p.2 i)) := by
    rw [contDiff_pi]
    intro i
    fin_cases i <;> · simp [pushY]; fun_prop
  convert ((EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff).comp h using 1
  ext p : 1
  rw [Function.uncurry_apply_pair]
  simp [EuclideanSpace.equiv, WithLp.toLp_ofLp]

theorem pushY_zero (D ε : ℝ) (v : E3) : pushY D ε 0 v = v := by
  apply eq_of_apply_eq
  intro i
  fin_cases i <;> simp [pushProf, Real.smoothTransition.zero]

/-! ### The derivative of the push -/

/-- The linear assembly `(f₀, f₁, f₂) ↦ (w ↦ (f₀ w, f₁ w, f₂ w))` of three linear forms. -/
def tripleCLM (f0 f1 f2 : E3 →L[ℝ] ℝ) : E3 →L[ℝ] E3 :=
  ((EuclideanSpace.equiv (Fin 3) ℝ).symm : (Fin 3 → ℝ) →L[ℝ] E3) ∘L
    ContinuousLinearMap.pi ![f0, f1, f2]

theorem tripleCLM_apply (f0 f1 f2 : E3 →L[ℝ] ℝ) (w : E3) :
    tripleCLM f0 f1 f2 w = WithLp.toLp 2 ![f0 w, f1 w, f2 w] := by
  have hpi : (ContinuousLinearMap.pi ![f0, f1, f2]) w = ![f0 w, f1 w, f2 w] := by
    ext i; fin_cases i <;> simp [ContinuousLinearMap.pi_apply]
  show (((EuclideanSpace.equiv (Fin 3) ℝ).symm : (Fin 3 → ℝ) →L[ℝ] E3) ∘L
      ContinuousLinearMap.pi ![f0, f1, f2]) w = _
  rw [ContinuousLinearMap.comp_apply, hpi]
  exact rfl

theorem hasFDerivAt_pushY (D ε s : ℝ) (v : E3) :
    HasFDerivAt (pushY D ε s)
      (tripleCLM (EuclideanSpace.proj (0 : Fin 3))
        ((fderiv ℝ (pushProf D ε s) (v 1)).comp (EuclideanSpace.proj (1 : Fin 3)))
        (EuclideanSpace.proj (2 : Fin 3))) v := by
  have h0 : HasFDerivAt (fun w : E3 => (fun i : Fin 3 => ![w 0, pushProf D ε s (w 1), w 2] i))
      (ContinuousLinearMap.pi ![(EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ),
        (fderiv ℝ (pushProf D ε s) (v 1)).comp (EuclideanSpace.proj (1 : Fin 3)),
        (EuclideanSpace.proj (2 : Fin 3) : E3 →L[ℝ] ℝ)]) v := by
    rw [hasFDerivAt_pi]
    intro i
    fin_cases i
    · simpa using (EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ).hasFDerivAt (x := v)
    · have houter : HasFDerivAt (pushProf D ε s) (fderiv ℝ (pushProf D ε s) (v 1))
          ((EuclideanSpace.proj (1 : Fin 3)) v) :=
        (differentiable_pushProf D ε s (v 1)).hasFDerivAt
      have hinner : HasFDerivAt (fun w : E3 => (EuclideanSpace.proj (1 : Fin 3)) w)
          ((EuclideanSpace.proj (1 : Fin 3)) : E3 →L[ℝ] ℝ) v :=
        ((EuclideanSpace.proj (1 : Fin 3)) : E3 →L[ℝ] ℝ).hasFDerivAt
      simpa [Function.comp_def] using houter.comp v hinner
    · simpa using (EuclideanSpace.proj (2 : Fin 3) : E3 →L[ℝ] ℝ).hasFDerivAt (x := v)
  exact ((EuclideanSpace.equiv (Fin 3) ℝ).symm : (Fin 3 → ℝ) →L[ℝ] E3).hasFDerivAt.comp v h0

theorem fderiv_pushY (D ε s : ℝ) (v : E3) :
    fderiv ℝ (pushY D ε s) v
      = tripleCLM (EuclideanSpace.proj (0 : Fin 3))
          ((fderiv ℝ (pushProf D ε s) (v 1)).comp (EuclideanSpace.proj (1 : Fin 3)))
          (EuclideanSpace.proj (2 : Fin 3)) :=
  (hasFDerivAt_pushY D ε s v).fderiv

theorem injective_fderiv_pushY (D ε s : ℝ) (hε : 0 < ε) (hD : 0 ≤ D) (v : E3) :
    Function.Injective (fderiv ℝ (pushY D ε s) v) := by
  have hderiv : deriv (pushProf D ε s) (v 1) ≠ 0 := by
    have h := deriv_pushProf_ge_one D ε s hε hD (v 1)
    linarith
  intro u u' huu
  have hker : (fderiv ℝ (pushY D ε s) v) (u - u') = 0 := by rw [map_sub, huu, sub_self]
  rw [fderiv_pushY D ε s v, tripleCLM_apply] at hker
  have h0 : (u - u') 0 = 0 := by
    have := congrArg (fun x : E3 => x 0) hker
    simpa using this
  have h2 : (u - u') 2 = 0 := by
    have := congrArg (fun x : E3 => x 2) hker
    simpa using this
  have h1 : (u - u') 1 = 0 := by
    have hm : (fderiv ℝ (pushProf D ε s) (v 1)) ((u - u') 1) = 0 := by
      have := congrArg (fun x : E3 => x 1) hker
      simpa using this
    rw [fderiv_eq_smul_deriv] at hm
    rcases smul_eq_zero.mp hm with h | h
    · exact h
    · exact absurd h hderiv
  have hsub : u - u' = 0 := eq_of_apply_eq (fun i => by fin_cases i <;> assumption)
  exact sub_eq_zero.mp hsub

theorem ambientPath_pushY (D ε : ℝ) (hε : 0 < ε) (hD : 0 ≤ D) : AmbientPath (pushY D ε) where
  smooth := contDiff_pushY D ε
  inj := fun s => pushY_injective D ε s hε hD
  imm := fun s v => injective_fderiv_pushY D ε s hε hD v
  zero := pushY_zero D ε

/-! ### The rigid translation off the band -/

theorem pushProf_eq_of_one_le {D ε s : ℝ} (hε : 0 < ε) {y : ℝ} (hy : ε ≤ y) :
    pushProf D ε s y = y + Real.smoothTransition s * D := by
  have h : 1 ≤ (y + ε) / (2 * ε) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hst : Real.smoothTransition ((y + ε) / (2 * ε)) = 1 := Real.smoothTransition.one_of_one_le h
  simp only [pushProf, hst]
  ring

theorem pushProf_eq_of_nonpos {D ε s : ℝ} (hε : 0 < ε) {y : ℝ} (hy : y ≤ -ε) :
    pushProf D ε s y = y - Real.smoothTransition s * D := by
  have h : (y + ε) / (2 * ε) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hst : Real.smoothTransition ((y + ε) / (2 * ε)) = 0 := Real.smoothTransition.zero_of_nonpos h
  simp only [pushProf, hst]
  ring

theorem pushY_eq_of_le {D ε s : ℝ} (hε : 0 < ε) {v : E3} (hv : ε ≤ v 1) :
    pushY D ε s v = WithLp.toLp 2 ![v 0, v 1 + Real.smoothTransition s * D, v 2] := by
  rw [pushY_eq_prof, pushProf_eq_of_one_le hε hv]

theorem pushY_eq_of_nonpos {D ε s : ℝ} (hε : 0 < ε) {v : E3} (hv : v 1 ≤ -ε) :
    pushY D ε s v = WithLp.toLp 2 ![v 0, v 1 - Real.smoothTransition s * D, v 2] := by
  rw [pushY_eq_prof, pushProf_eq_of_nonpos hε hv]


open scoped Manifold ContDiff Topology in
/-- **The twist toolkit of the Möbius saddle certificate** (§4 `D2d.1` of
`Submission/Work/Drive/N2Lead/NOTES_LEAD_mobiusSaddle.md`; the definitions are in
`Submission/Work/Drive/N2Lead/twistDefs.lean`).  For a slab half-width `a > 0`, a vertical slab
half-width `ε > 0` and a push amplitude `D ≥ 0`:

* the reversed slab twists `s ↦ twistY a (-s)` and `s ↦ twistX ε (-s)` and the push path
  `s ↦ pushY D ε s` are `AmbientPath`s, i.e. jointly smooth in `(s, v)`, each slice is injective with
  injective derivative, and the slice at `s = 0` is the identity (the inverse of `twistY a s` is
  `twistY a (-s)` because the twist angle is invariant under the rotation, and `pushY` is
  triangular with `∂_y ≥ 1` for `D ≥ 0`);
* the twists are the identity on the far side of their slab (`a ≤ v 1`, resp. `v 0 ≤ -ε`) and the
  half-turns `(x, y, z) ↦ (-x, y, -z)`, resp. `(x, y, z) ↦ (x, -y, -z)`, on the near side
  (`v 1 ≤ -a` for the angle `s = 1`, resp. `ε ≤ v 0` for the angle `s = -1`);
* the push is the rigid translation by `± smoothTransition s * D` off the band `|y| ≥ ε`. -/
theorem twistToolkit {a ε D : ℝ} (ha : 0 < a) (hε : 0 < ε) (hD : 0 ≤ D) :
    Work.Drive.N2Lead.AmbientPath (fun s : ℝ => Work.Drive.N2Lead.twistY a (-s)) ∧
    Work.Drive.N2Lead.AmbientPath (fun s : ℝ => Work.Drive.N2Lead.twistX ε (-s)) ∧
    Work.Drive.N2Lead.AmbientPath (Work.Drive.N2Lead.pushY D ε) ∧
    (∀ (s : ℝ) (v : EuclideanSpace ℝ (Fin 3)), a ≤ v 1 →
      Work.Drive.N2Lead.twistY a s v = v) ∧
    (∀ v : EuclideanSpace ℝ (Fin 3), v 1 ≤ -a →
      Work.Drive.N2Lead.twistY a 1 v = WithLp.toLp 2 ![-v 0, v 1, -v 2]) ∧
    (∀ (s : ℝ) (v : EuclideanSpace ℝ (Fin 3)), v 0 ≤ -ε →
      Work.Drive.N2Lead.twistX ε s v = v) ∧
    (∀ v : EuclideanSpace ℝ (Fin 3), ε ≤ v 0 →
      Work.Drive.N2Lead.twistX ε (-1) v = WithLp.toLp 2 ![v 0, -v 1, -v 2]) ∧
    (∀ (s : ℝ) (v : EuclideanSpace ℝ (Fin 3)), ε ≤ v 1 →
      Work.Drive.N2Lead.pushY D ε s v
        = WithLp.toLp 2 ![v 0, v 1 + Real.smoothTransition s * D, v 2]) ∧
    (∀ (s : ℝ) (v : EuclideanSpace ℝ (Fin 3)), v 1 ≤ -ε →
      Work.Drive.N2Lead.pushY D ε s v
        = WithLp.toLp 2 ![v 0, v 1 - Real.smoothTransition s * D, v 2]) := by
  refine ⟨ambientPath_twistY a, ambientPath_twistX ε, ambientPath_pushY D ε hε hD, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro s v hv
    exact twistY_eq_self_of_le ha hv
  · intro v hv
    exact twistY_one_of_le ha hv
  · intro s v hv
    exact twistX_eq_self_of_le hε hv
  · intro v hv
    exact twistX_neg_one_of_le hε hv
  · intro s v hv
    exact pushY_eq_of_le hε hv
  · intro s v hv
    exact pushY_eq_of_nonpos hε hv

end

end Work.Drive.N2Lead
