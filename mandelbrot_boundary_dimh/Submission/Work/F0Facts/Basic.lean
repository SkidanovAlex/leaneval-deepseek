import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.FatouCoord.Main
import Submission.Work.FatouCoord.Repelling
import Submission.Work.Normal.montel_omits_three

/-!
# AREA F0FACTS — foundations

Elementary facts about `f₀(z) = z + z²` used by the proof of `F0FactsStatement`:

* `isParabolicGerm_f0`, `parabolicBounds_f0`: the quantitative hypotheses of the `FatouCoord`
  chapter are met by `f₀` (with `h ≡ 1`, parameter `a = 0`);
* `finv`: the local inverse branch `w ↦ (-1 + √(1+4w))/2` of `f₀` at `0`, with
  `f0_finv : f₀ (finv w) = w`, `finv_eq_zero_iff`, `finv_eq_neg_half_iff`;
* `w3`: a root of `z² + z + 1` with `f0 w3 = -1` and `w3 ∉ ℝ`;
* `Basin := ParabolicBasin f0 univ`: `isOpen_Basin`, the complete invariance
  `basin_preimage : f0 ⁻¹' Basin = Basin`, and surjectivity of `f₀`.
-/

namespace Work.F0Facts

open MandelDim Filter Set Metric Topology
open scoped Topology

noncomputable section

/-! ## The germ `f₀` -/

@[simp] lemma f0_eq (z : ℂ) : f0 z = z + z ^ 2 := rfl

lemma deriv_f0 : deriv f0 = fun z : ℂ => 1 + 2 * z := by
  funext x
  have h : (fun z : ℂ => z + z ^ 2) = (fun z : ℂ => z) + (fun z : ℂ => z) ^ 2 := by
    funext z; simp
  show deriv (fun z : ℂ => z + z ^ 2) x = 1 + 2 * x
  rw [h, deriv_add differentiableAt_id (differentiableAt_id.pow 2),
    deriv_pow differentiableAt_id, deriv_id'']
  norm_num

lemma differentiableOn_f0 : DifferentiableOn ℂ f0 univ := by
  have hfun : (fun z : ℂ => z + z ^ 2) = (fun z : ℂ => z) + (fun z : ℂ => z) ^ 2 := by
    funext z; simp
  intro z _
  show DifferentiableWithinAt ℂ (fun z : ℂ => z + z ^ 2) univ z
  rw [hfun]
  exact (differentiableAt_id.add (differentiableAt_id.pow 2)).differentiableWithinAt

lemma continuous_f0 : Continuous f0 := by
  have hfun : (fun z : ℂ => z + z ^ 2) = (fun z : ℂ => z) + (fun z : ℂ => z) ^ 2 := by
    funext z; simp
  have : Continuous fun z : ℂ => z + z ^ 2 := by
    rw [hfun]; fun_prop
  exact this

lemma isParabolicGerm_f0 : IsParabolicGerm f0 univ := by
  have hderiv : deriv (fun z : ℂ => z + z ^ 2) = fun x => 1 + 2 * x := by
    funext x
    have h : (fun z : ℂ => z + z ^ 2) = (fun z : ℂ => z) + (fun z : ℂ => z) ^ 2 := by
      funext z; simp
    rw [h, deriv_add differentiableAt_id (differentiableAt_id.pow 2),
      deriv_pow differentiableAt_id, deriv_id'']
    norm_num
  have hlin : ∀ x : ℂ, HasDerivAt (fun y : ℂ => 1 + 2 * y) 2 x := by
    intro x
    have h1 : HasDerivAt (fun y : ℂ => y) 1 x := hasDerivAt_id x
    have h2 : HasDerivAt (fun y : ℂ => 2 * y) 2 x := by simpa using h1.const_mul (2 : ℂ)
    simpa using h2.const_add (1 : ℂ)
  refine ⟨isOpen_univ, trivial, differentiableOn_f0, ?_, ?_, ?_⟩
  · simp [f0]
  · show deriv (fun z : ℂ => z + z ^ 2) 0 = 1
    rw [hderiv]; norm_num
  · show deriv (deriv (fun z : ℂ => z + z ^ 2)) 0 = 2
    rw [hderiv]
    exact (hlin 0).deriv

lemma parabolicBounds_f0 {r : ℝ} (hr : 0 < r) :
    Work.FatouCoord.ParabolicBounds f0 (fun _ : ℂ => 1) 0 r 0 0 := by
  refine ⟨hr, le_refl 0, le_refl 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro z _; simp [f0]
  · exact differentiableOn_const 1
  · intro z _; simp
  · intro z _; norm_num
  · intro z _; simp

/-! ## The local inverse branch -/

/-- The local inverse branch of `f₀` at `0`: `w ↦ (-1 + √(1+4w))/2` with the principal root. -/
def finv (w : ℂ) : ℂ := (-1 + Complex.sqrt (1 + 4 * w)) / 2

lemma sqrt_sq (z : ℂ) : (Complex.sqrt z) ^ 2 = z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [sqrt_eq_exp hz, sq, ← Complex.exp_add,
      show Complex.log z / 2 + Complex.log z / 2 = Complex.log z by ring, Complex.exp_log hz]

lemma finv_sq (w : ℂ) : finv w + (finv w) ^ 2 = w := by
  have h := sqrt_sq (1 + 4 * w)
  simp only [finv]
  linear_combination h / 4

lemma f0_finv (w : ℂ) : f0 (finv w) = w := by
  rw [f0_eq, finv_sq]

lemma finv_zero : finv 0 = 0 := by simp [finv]

lemma finv_eq_zero_iff (w : ℂ) : finv w = 0 ↔ w = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h, finv_zero]⟩
  have h' : finv w + (finv w) ^ 2 = w := finv_sq w
  rw [h] at h'
  simp at h'
  exact h'.symm

lemma finv_ne_zero_iff {w : ℂ} : finv w ≠ 0 ↔ w ≠ 0 :=
  not_congr (finv_eq_zero_iff w)

/-- `finv w = -1/2 ↔ w = -1/4`. -/
lemma finv_eq_neg_half_iff (w : ℂ) : finv w = -1 / 2 ↔ w = -1 / 4 := by
  constructor
  · intro h
    have h' : finv w + (finv w) ^ 2 = w := finv_sq w
    rw [h] at h'
    norm_num at h'
    have hw : w = -(1 / 4) := h'.symm
    rw [hw]; norm_num
  · intro h
    rw [h]
    have : 1 + 4 * (-1 / 4 : ℂ) = 0 := by norm_num
    simp [finv, this]

/-! ## The point `ω = (-1 + √3 i)/2` -/

/-- A primitive cube root of unity, in rectangular coordinates. -/
def w3 : ℂ := (-1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2

lemma w3_im : w3.im = Real.sqrt 3 / 2 := by
  simp [w3]

lemma sqrt_three_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

lemma w3_not_real : w3.im ≠ 0 := by
  rw [w3_im]
  positivity

lemma f0_w3 : f0 w3 = -1 := by
  have h3 : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
  have hI : Complex.I ^ 2 = -1 := by rw [sq]; exact Complex.I_mul_I
  have hexp : w3 = (-1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2 := rfl
  have hs : (Complex.I * (Real.sqrt 3 : ℂ)) ^ 2 = -3 := by
    rw [mul_pow, hI, h3]; norm_num
  have hsq : ((-1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2) ^ 2
      = (1 - 2 * (Complex.I * (Real.sqrt 3 : ℂ)) + (-3)) / 4 := by
    rw [div_pow]
    rw [show (-1 + Complex.I * (Real.sqrt 3 : ℂ)) ^ 2
        = 1 - 2 * (Complex.I * (Real.sqrt 3 : ℂ)) + (Complex.I * (Real.sqrt 3 : ℂ)) ^ 2
        by ring]
    rw [hs]
    norm_num
  rw [f0_eq, hexp, hsq]
  ring

lemma w3_ne_zero : w3 ≠ 0 := by
  intro h
  have h2 := w3_im
  rw [h] at h2
  norm_num at h2
  have := sqrt_three_pos
  linarith

/-! ## The basin of `0` -/

/-- The parabolic basin of `0` for `f₀`, in the sense of the contract. -/
abbrev Basin : Set ℂ := ParabolicBasin f0 univ

lemma isOpen_Basin : IsOpen Basin := by
  refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
  obtain ⟨U, hU, hmap, hunif⟩ := hz
  obtain ⟨V, hVU, hVopen, hzV⟩ := _root_.mem_nhds_iff.mp hU
  refine Filter.mem_of_superset (hVopen.mem_nhds hzV) fun y hy => ?_
  exact ⟨V, hVopen.mem_nhds hy, fun n x _ => trivial, hunif.mono hVU⟩

/-- The basin is invariant backwards under `f₀`: `f₀ z ∈ Basin → z ∈ Basin`. -/
lemma mem_Basin_of_f0_mem {z : ℂ} (hz : f0 z ∈ Basin) : z ∈ Basin := by
  obtain ⟨U, hU, hmap, hunif⟩ := hz
  have hpre : f0 ⁻¹' U ∈ 𝓝 z := continuous_f0.continuousAt.preimage_mem_nhds hU
  refine ⟨f0 ⁻¹' U, hpre, fun n x _ => trivial, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff] at hunif ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hunif ε hε)
  refine Filter.eventually_atTop.mpr ⟨N + 1, fun n hn y hy => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hthis := hN m (by omega) (f0 y) hy
  simpa only [Function.iterate_succ_apply] using hthis

lemma isOpenMap_f0 : IsOpenMap f0 := by
  have hana : AnalyticOnNhd ℂ f0 univ := fun z _ =>
    differentiableOn_f0.analyticAt Filter.univ_mem
  rcases AnalyticOnNhd.is_constant_or_isOpenMap hana with ⟨c, hc⟩ | h
  · have h0 : c = 0 := by rw [← hc 0]; simp [f0]
    have h1 : c = 2 := by rw [← hc 1]; norm_num [f0]
    exact absurd (h0.symm.trans h1) (by norm_num)
  · exact h

lemma f0_mem_Basin {z : ℂ} (hz : z ∈ Basin) : f0 z ∈ Basin := by
  obtain ⟨U, hU, hmap, hunif⟩ := hz
  obtain ⟨V, hVU, hVopen, hzV⟩ := _root_.mem_nhds_iff.mp hU
  have hopen : IsOpen (f0 '' V) := isOpenMap_f0 V hVopen
  refine ⟨f0 '' V, hopen.mem_nhds ⟨z, hzV, rfl⟩, fun n x _ => trivial, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff] at hunif ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hunif ε hε)
  refine Filter.eventually_atTop.mpr ⟨N, fun n hn y hy => ?_⟩
  obtain ⟨x, hx, rfl⟩ := hy
  have hthis := hN (n + 1) (by omega) x (hVU hx)
  simpa only [Function.iterate_succ_apply] using hthis

lemma basin_preimage : f0 ⁻¹' Basin = Basin := by
  ext z
  exact ⟨fun h => mem_Basin_of_f0_mem h, fun h => f0_mem_Basin h⟩

lemma f0_surjective : Function.Surjective f0 := fun w => ⟨finv w, f0_finv w⟩

end
end Work.F0Facts
