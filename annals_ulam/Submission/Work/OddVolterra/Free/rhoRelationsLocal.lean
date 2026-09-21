import Mathlib
import Submission.Work.OddCurve.Free.rhoMulRelation
import Submission.Work.OddCurve.Free.rhoSecondOrder

open Set Filter
open scoped Topology

namespace Work.OddVolterra.Free

/-- **First-order relation, local form.**  Differentiating
`ρ v * √(1 - v²) = f (ρ v * v)` at `u` and eliminating the square root gives a polynomial
relation between `ρ u`, `ρ' u`, `f (ρ u * u)` and `f' (ρ u * u)`.  Unlike the global
version, the smoothness of `f` is only used at the single point `ρ u * u`
(hypothesis `|ρ u * u| < 1`). -/
private lemma rho_local_first {ρ f : ℝ → ℝ} {u : ℝ}
    (hρ : ContDiffOn ℝ 2 ρ (Set.Ioo (-1 : ℝ) 1))
    (hf : ContDiffOn ℝ 2 f (Set.Ioo (-1 : ℝ) 1))
    (hu : |u| < 1) (hx : |ρ u * u| < 1)
    (heq : ∀ v ∈ Set.Ioo (-1 : ℝ) 1, ρ v * Real.sqrt (1 - v ^ 2) = f (ρ v * v)) :
    deriv ρ u * (Real.sqrt (1 - u ^ 2)) ^ 2 - ρ u * u =
      deriv f (ρ u * u) * (deriv ρ u * u + ρ u) * Real.sqrt (1 - u ^ 2) := by
  obtain ⟨hu1, hu2⟩ := abs_lt.mp hu
  obtain ⟨hx1, hx2⟩ := abs_lt.mp hx
  have hmem : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 u := Ioo_mem_nhds hu1 hu2
  have hwmem' : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (ρ u * u) := Ioo_mem_nhds hx1 hx2
  have hu2pos : (0 : ℝ) < 1 - u ^ 2 := by nlinarith
  have hu2lt : u ^ 2 < 1 := by nlinarith
  have hρd : HasDerivAt ρ (deriv ρ u) u :=
    ((hρ.contDiffAt hmem).differentiableAt (by norm_num)).hasDerivAt
  have hfd : HasDerivAt f (deriv f (ρ u * u)) (ρ u * u) :=
    ((hf.contDiffAt hwmem').differentiableAt (by norm_num)).hasDerivAt
  have hsd : HasDerivAt (fun v : ℝ => Real.sqrt (1 - v ^ 2))
      (-(u / Real.sqrt (1 - u ^ 2))) u :=
    Work.OddCurve.Free.hasDerivAt_sqrt_one_sub_sq hu2lt
  have hA : HasDerivAt (fun v : ℝ => ρ v * Real.sqrt (1 - v ^ 2))
      (deriv ρ u * Real.sqrt (1 - u ^ 2) + ρ u * (-(u / Real.sqrt (1 - u ^ 2)))) u :=
    hρd.mul hsd
  have hGd : HasDerivAt (fun v : ℝ => ρ v * v) (deriv ρ u * u + ρ u) u := by
    have h := hρd.mul (hasDerivAt_id u)
    convert h using 2 <;> try rfl
    ring
  have hB : HasDerivAt (fun v : ℝ => f (ρ v * v))
      (deriv f (ρ u * u) * (deriv ρ u * u + ρ u)) u := by
    have h := HasDerivAt.comp (h := fun v : ℝ => ρ v * v) u hfd hGd
    simpa [Function.comp_def] using h
  have hS : HasDerivAt (fun v : ℝ => ρ v * Real.sqrt (1 - v ^ 2) - f (ρ v * v))
      (deriv ρ u * Real.sqrt (1 - u ^ 2) + ρ u * (-(u / Real.sqrt (1 - u ^ 2))) -
        deriv f (ρ u * u) * (deriv ρ u * u + ρ u)) u := hA.sub hB
  have hS0 : (fun v : ℝ => ρ v * Real.sqrt (1 - v ^ 2) - f (ρ v * v)) =ᶠ[𝓝 u] (0 : ℝ → ℝ) := by
    filter_upwards [hmem] with v hv
    rw [heq v hv, sub_self]
    simp
  have hder : deriv ρ u * Real.sqrt (1 - u ^ 2) + ρ u * (-(u / Real.sqrt (1 - u ^ 2)))
      = deriv f (ρ u * u) * (deriv ρ u * u + ρ u) := by
    have h1 := hS.deriv
    have h2 : deriv (fun v : ℝ => ρ v * Real.sqrt (1 - v ^ 2) - f (ρ v * v)) u = 0 := by
      rw [hS0.deriv_eq]
      simp
    rw [h2] at h1
    exact sub_eq_zero.mp h1.symm
  rw [← hder]
  field_simp
  ring

/-- **Second-order relation, local form.**  Differentiating
`ρ v * √(1 - v²) = f (ρ v * v)` twice at `u` and eliminating the square root gives a
polynomial relation between `ρ u`, `ρ' u`, `ρ'' u`, `f (ρ u * u)`, `f' (ρ u * u)` and
`f'' (ρ u * u)`.  Smoothness of `f` is used only near `ρ u * u` (hypothesis `|ρ u * u| < 1`),
and `ρ` only near `u`. -/
private lemma rho_local_second {ρ f : ℝ → ℝ} {u : ℝ}
    (hρ : ContDiffOn ℝ 2 ρ (Set.Ioo (-1 : ℝ) 1))
    (hf : ContDiffOn ℝ 2 f (Set.Ioo (-1 : ℝ) 1))
    (hu : |u| < 1) (hx : |ρ u * u| < 1)
    (heq : ∀ v ∈ Set.Ioo (-1 : ℝ) 1, ρ v * Real.sqrt (1 - v ^ 2) = f (ρ v * v)) :
    deriv (deriv ρ) u * (Real.sqrt (1 - u ^ 2) - u * deriv f (ρ u * u)) =
      2 * deriv ρ u * u / Real.sqrt (1 - u ^ 2) +
        ρ u / (Real.sqrt (1 - u ^ 2)) ^ 3 +
        deriv (deriv f) (ρ u * u) * (deriv ρ u * u + ρ u) ^ 2 +
        2 * deriv f (ρ u * u) * deriv ρ u := by
  obtain ⟨hu1, hu2⟩ := abs_lt.mp hu
  obtain ⟨hx1, hx2⟩ := abs_lt.mp hx
  have hmem : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 u := Ioo_mem_nhds hu1 hu2
  have hwmem' : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (ρ u * u) := Ioo_mem_nhds hx1 hx2
  -- `ρ` is continuous at `u`, hence `v ↦ ρ v * v` stays inside `(-1,1)` near `u`
  have hcont : ContinuousAt (fun v : ℝ => ρ v * v) u :=
    ((hρ.contDiffAt hmem).continuousAt).mul continuousAt_id
  have hev : ∀ᶠ v in 𝓝 u, ρ v * v ∈ Set.Ioo (-1 : ℝ) 1 :=
    hcont.preimage_mem_nhds hwmem'
  have hu2pos : (0 : ℝ) < 1 - u ^ 2 := by nlinarith
  have hu2lt : u ^ 2 < 1 := by nlinarith
  have hwne : Real.sqrt (1 - u ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hu2pos)
  have hw2 : Real.sqrt (1 - u ^ 2) ^ 2 = 1 - u ^ 2 := Real.sq_sqrt hu2pos.le
  -- differentiability facts at `u`
  have hρd : HasDerivAt ρ (deriv ρ u) u :=
    ((hρ.contDiffAt hmem).differentiableAt (by norm_num)).hasDerivAt
  have hρd' : HasDerivAt (deriv ρ) (deriv (deriv ρ) u) u :=
    (((hρ.contDiffAt hmem).derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt
  have hfd : HasDerivAt f (deriv f (ρ u * u)) (ρ u * u) :=
    ((hf.contDiffAt hwmem').differentiableAt (by norm_num)).hasDerivAt
  have hfd' : HasDerivAt (deriv f) (deriv (deriv f) (ρ u * u)) (ρ u * u) :=
    (((hf.contDiffAt hwmem').derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt
  have hsd : HasDerivAt (fun v : ℝ => Real.sqrt (1 - v ^ 2))
      (-(u / Real.sqrt (1 - u ^ 2))) u :=
    Work.OddCurve.Free.hasDerivAt_sqrt_one_sub_sq hu2lt
  have hGd : HasDerivAt (fun v : ℝ => ρ v * v) (deriv ρ u * u + ρ u) u := by
    have h := hρd.mul (hasDerivAt_id u)
    convert h using 2 <;> try rfl
    ring
  have hG'd : HasDerivAt (fun v : ℝ => deriv ρ v * v + ρ v)
      (deriv (deriv ρ) u * u + 2 * deriv ρ u) u := by
    have h1 : HasDerivAt (fun v : ℝ => deriv ρ v * v) (deriv (deriv ρ) u * u + deriv ρ u) u := by
      have h := hρd'.mul (hasDerivAt_id u)
      convert h using 2 <;> try rfl
      ring
    have h2 : HasDerivAt (fun v : ℝ => deriv ρ v * v + ρ v)
        (deriv (deriv ρ) u * u + deriv ρ u + deriv ρ u) u := by
      have h := h1.add hρd
      convert h using 2 <;> try rfl
    convert h2 using 1
    ring
  -- the defining relation, as a function which vanishes near `u`
  have hH0 : (fun v : ℝ => ρ v * Real.sqrt (1 - v ^ 2) - f (ρ v * v)) =ᶠ[𝓝 u] (0 : ℝ → ℝ) := by
    filter_upwards [hmem] with v hv
    rw [heq v hv, sub_self]
    rfl
  have hHd0 : deriv (deriv (fun v : ℝ => ρ v * Real.sqrt (1 - v ^ 2) - f (ρ v * v))) u = 0 := by
    have h0 : deriv (0 : ℝ → ℝ) = (0 : ℝ → ℝ) := by funext x; simp
    have h1 : deriv (fun v : ℝ => ρ v * Real.sqrt (1 - v ^ 2) - f (ρ v * v)) =ᶠ[𝓝 u] (0 : ℝ → ℝ) := by
      have h := hH0.deriv
      rwa [h0] at h
    rw [h1.deriv_eq]
    simp
  -- the first derivative of the defining relation, as an explicit function `ψ`
  set ψ : ℝ → ℝ := fun v =>
    deriv ρ v * Real.sqrt (1 - v ^ 2) - ρ v * v / Real.sqrt (1 - v ^ 2) -
      deriv f (ρ v * v) * (deriv ρ v * v + ρ v) with hψdef
  have hψ : deriv (fun v : ℝ => ρ v * Real.sqrt (1 - v ^ 2) - f (ρ v * v)) =ᶠ[𝓝 u] ψ := by
    filter_upwards [hmem, hev] with v hv hwv
    obtain ⟨hv1, hv2⟩ := hv
    have hv2lt : v ^ 2 < 1 := by nlinarith
    have hmemv : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 v := Ioo_mem_nhds hv1 hv2
    have hρv : HasDerivAt ρ (deriv ρ v) v :=
      ((hρ.contDiffAt hmemv).differentiableAt (by norm_num)).hasDerivAt
    have hfv : HasDerivAt f (deriv f (ρ v * v)) (ρ v * v) :=
      ((hf.contDiffAt (Ioo_mem_nhds hwv.1 hwv.2)).differentiableAt (by norm_num)).hasDerivAt
    have hsv : HasDerivAt (fun w : ℝ => Real.sqrt (1 - w ^ 2))
        (-(v / Real.sqrt (1 - v ^ 2))) v :=
      Work.OddCurve.Free.hasDerivAt_sqrt_one_sub_sq hv2lt
    have hGv : HasDerivAt (fun w : ℝ => ρ w * w) (deriv ρ v * v + ρ v) v := by
      have h := hρv.mul (hasDerivAt_id v)
      convert h using 2 <;> try rfl
      ring
    have hA : HasDerivAt (fun w : ℝ => ρ w * Real.sqrt (1 - w ^ 2))
        (deriv ρ v * Real.sqrt (1 - v ^ 2) + ρ v * (-(v / Real.sqrt (1 - v ^ 2)))) v :=
      hρv.mul hsv
    have hB : HasDerivAt (fun w : ℝ => f (ρ w * w))
        (deriv f (ρ v * v) * (deriv ρ v * v + ρ v)) v := by
      have h := HasDerivAt.comp (h := fun w : ℝ => ρ w * w) v hfv hGv
      simpa [Function.comp_def] using h
    have hAB : HasDerivAt (fun w : ℝ => ρ w * Real.sqrt (1 - w ^ 2) - f (ρ w * w))
        (deriv ρ v * Real.sqrt (1 - v ^ 2) + ρ v * (-(v / Real.sqrt (1 - v ^ 2))) -
          deriv f (ρ v * v) * (deriv ρ v * v + ρ v)) v := by
      have h := hA.sub hB
      convert h using 1 <;> try rfl
    have hder := hAB.deriv
    rw [hψdef]
    simp only
    rw [hder]
    ring
  have hψ0 : deriv ψ u = 0 := by
    rw [← hψ.deriv_eq]
    exact hHd0
  -- `ψ` at `u`, computed by the product/quotient rules
  have hP1 : HasDerivAt (fun v : ℝ => deriv ρ v * Real.sqrt (1 - v ^ 2))
      (deriv (deriv ρ) u * Real.sqrt (1 - u ^ 2) +
        deriv ρ u * (-(u / Real.sqrt (1 - u ^ 2)))) u := by
    have h := hρd'.mul hsd
    convert h using 1 <;> try rfl
  have hP2 : HasDerivAt (fun v : ℝ => ρ v * v / Real.sqrt (1 - v ^ 2))
      (((deriv ρ u * u + ρ u) * Real.sqrt (1 - u ^ 2) -
          (ρ u * u) * (-(u / Real.sqrt (1 - u ^ 2)))) /
        (Real.sqrt (1 - u ^ 2)) ^ 2) u := by
    have h := hGd.div hsd hwne
    convert h using 1 <;> try rfl
  have hcompf : HasDerivAt (fun v : ℝ => deriv f (ρ v * v))
      (deriv (deriv f) (ρ u * u) * (deriv ρ u * u + ρ u)) u := by
    have h := HasDerivAt.comp (h := fun v : ℝ => ρ v * v) u hfd' hGd
    simpa [Function.comp_def] using h
  have hP3 : HasDerivAt (fun v : ℝ => deriv f (ρ v * v) * (deriv ρ v * v + ρ v))
      ((deriv (deriv f) (ρ u * u) * (deriv ρ u * u + ρ u)) * (deriv ρ u * u + ρ u) +
        deriv f (ρ u * u) * (deriv (deriv ρ) u * u + 2 * deriv ρ u)) u := by
    have h := hcompf.mul hG'd
    convert h using 1 <;> try rfl
  have hDψ : HasDerivAt ψ
      (deriv (deriv ρ) u * Real.sqrt (1 - u ^ 2) +
          deriv ρ u * (-(u / Real.sqrt (1 - u ^ 2))) -
        (((deriv ρ u * u + ρ u) * Real.sqrt (1 - u ^ 2) -
            (ρ u * u) * (-(u / Real.sqrt (1 - u ^ 2)))) /
          (Real.sqrt (1 - u ^ 2)) ^ 2) -
        ((deriv (deriv f) (ρ u * u) * (deriv ρ u * u + ρ u)) * (deriv ρ u * u + ρ u) +
          deriv f (ρ u * u) * (deriv (deriv ρ) u * u + 2 * deriv ρ u))) u := by
    rw [hψdef]
    convert (hP1.sub hP2).sub hP3 using 1 <;> try rfl
  -- the second-order relation, in raw form
  have hDval : deriv (deriv ρ) u * Real.sqrt (1 - u ^ 2) +
          deriv ρ u * (-(u / Real.sqrt (1 - u ^ 2))) -
        (((deriv ρ u * u + ρ u) * Real.sqrt (1 - u ^ 2) -
            (ρ u * u) * (-(u / Real.sqrt (1 - u ^ 2)))) /
          (Real.sqrt (1 - u ^ 2)) ^ 2) -
        ((deriv (deriv f) (ρ u * u) * (deriv ρ u * u + ρ u)) * (deriv ρ u * u + ρ u) +
          deriv f (ρ u * u) * (deriv (deriv ρ) u * u + 2 * deriv ρ u)) = 0 :=
    hDψ.deriv.symm.trans hψ0
  -- cleared form of the second-order relation
  have hstar : deriv (deriv ρ) u * (Real.sqrt (1 - u ^ 2) - u * deriv f (ρ u * u)) =
      2 * deriv ρ u * u / Real.sqrt (1 - u ^ 2) + ρ u / (Real.sqrt (1 - u ^ 2)) ^ 3 +
        deriv (deriv f) (ρ u * u) * (deriv ρ u * u + ρ u) ^ 2 +
        2 * deriv f (ρ u * u) * deriv ρ u := by
    have h := hDval
    field_simp at h ⊢
    linear_combination h + (ρ u) * hw2
  exact hstar

theorem rhoRelationsLocal {f ρ : ℝ → ℝ} {u : ℝ}
    (hρ : ContDiffOn ℝ 2 ρ (Set.Ioo (-1 : ℝ) 1))
    (hf : ContDiffOn ℝ 2 f (Set.Ioo (-1 : ℝ) 1))
    (hu : |u| < 1) (hx : |ρ u * u| < 1)
    (heq : ∀ v ∈ Set.Ioo (-1 : ℝ) 1, ρ v * Real.sqrt (1 - v ^ 2) = f (ρ v * v)) :
    deriv ρ u * (f (ρ u * u) * (f (ρ u * u) - (ρ u * u) * deriv f (ρ u * u))) =
        (ρ u) ^ 2 * (ρ u * u + f (ρ u * u) * deriv f (ρ u * u)) ∧
      deriv (deriv ρ) u * (f (ρ u * u) - (ρ u * u) * deriv f (ρ u * u)) =
        ρ u * (2 * deriv ρ u * u / Real.sqrt (1 - u ^ 2) +
          ρ u / (Real.sqrt (1 - u ^ 2)) ^ 3 +
          deriv (deriv f) (ρ u * u) * (deriv ρ u * u + ρ u) ^ 2 +
          2 * deriv f (ρ u * u) * deriv ρ u) := by
  have hu' : u ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hu
  have hFs : f (ρ u * u) = ρ u * Real.sqrt (1 - u ^ 2) := (heq u hu').symm
  have h1 := rho_local_first hρ hf hu hx heq
  have h2 := rho_local_second hρ hf hu hx heq
  constructor
  · rw [hFs]
    linear_combination (ρ u) ^ 2 * h1
  · rw [hFs]
    linear_combination (ρ u) * h2

end Work.OddVolterra.Free
