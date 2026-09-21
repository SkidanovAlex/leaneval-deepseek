import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddEnvelope.Defs
import Submission.Work.OddVolterra.Existence.glue_cutoff_defs

open Set Filter
open scoped Topology ContDiff

namespace Work.OddVolterra.Existence

lemma comp_diff {Z : ℝ → Work.OddVolterra.St} {x : ℝ} (hx : 0 < x) (i : Fin 4)
    (hZsm : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (0 : ℝ))) :
    DifferentiableAt ℝ (fun u : ℝ => Z u i) x := by
  have hZx : DifferentiableAt ℝ Z x :=
    ((hZsm.differentiableOn (by norm_num)) x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)
  exact (by fun_prop : DifferentiableAt ℝ (fun f : Work.OddVolterra.St => f i) (Z x)).comp x hZx

lemma profX_diff (x : ℝ) : DifferentiableAt ℝ Commons.Geometry.Ulam.profileX x := by
  have h : Commons.Geometry.Ulam.profileX = fun s : ℝ => 1 / Real.sqrt (1 + s ^ 2) := rfl
  rw [h]
  fun_prop (disch := positivity)

lemma hasDerivAt_profileX (s : ℝ) :
    HasDerivAt Commons.Geometry.Ulam.profileX
      (-s * Commons.Geometry.Ulam.profileX s ^ 3) s := by
  have hne : Real.sqrt (1 + s^2) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun x : ℝ => 1 + x^2) (2*s) s := by
    simpa using ((hasDerivAt_pow 2 s).const_add 1)
  have h2 : HasDerivAt (fun x : ℝ => Real.sqrt (1 + x^2)) (s / Real.sqrt (1+s^2)) s := by
    have h := h1.sqrt (by positivity : (1:ℝ) + s^2 ≠ 0)
    exact h.congr_deriv (by field_simp)
  have h3 : HasDerivAt (fun x : ℝ => (Real.sqrt (1 + x^2))⁻¹)
      (-(s / Real.sqrt (1+s^2)) / (Real.sqrt (1+s^2))^2) s := h2.inv hne
  have h4 : Commons.Geometry.Ulam.profileX = fun x : ℝ => (Real.sqrt (1 + x^2))⁻¹ := by
    funext x; simp [Commons.Geometry.Ulam.profileX, one_div]
  rw [h4]
  refine h3.congr_deriv ?_
  simp only
  rw [inv_pow]
  field_simp

lemma deriv_profileX_eq (x : ℝ) :
    deriv Commons.Geometry.Ulam.profileX x = -x * Commons.Geometry.Ulam.profileX x ^ 3 :=
  (hasDerivAt_profileX x).deriv

lemma deriv_profX_diff (x : ℝ) :
    DifferentiableAt ℝ (deriv Commons.Geometry.Ulam.profileX) x := by
  have h : deriv Commons.Geometry.Ulam.profileX =
      fun y : ℝ => -y * (1 / Real.sqrt (1 + y ^ 2)) ^ 3 := by
    funext y
    rw [deriv_profileX_eq]
    simp [Commons.Geometry.Ulam.profileX]
  rw [h]
  fun_prop (disch := positivity)

@[simp] lemma baseState_zero (s : ℝ) : (Work.OddVolterra.baseState s) 0 = Commons.Geometry.Ulam.profileX s := rfl
@[simp] lemma baseState_one (s : ℝ) : (Work.OddVolterra.baseState s) 1 = Commons.Geometry.Ulam.profileX s := rfl
@[simp] lemma baseState_two (s : ℝ) : (Work.OddVolterra.baseState s) 2 = deriv Commons.Geometry.Ulam.profileX s := rfl
@[simp] lemma baseState_three (s : ℝ) : (Work.OddVolterra.baseState s) 3 = deriv Commons.Geometry.Ulam.profileX s := rfl

/-- The deviation of the component `i` of a window solution from the semicircle profile. -/
noncomputable def dev (Z : ℝ → Work.OddVolterra.St) (i : Fin 4) (s : ℝ) : ℝ :=
  Z s i - Commons.Geometry.Ulam.profileX s

lemma dev_tail {Z : ℝ → Work.OddVolterra.St} (i : Fin 4) (hi : i = 0 ∨ i = 1)
    (htail : ∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → Z s = Work.OddVolterra.baseState s) :
    ∀ x : ℝ, 1 - Work.OddVolterra.tau ≤ x → dev Z i x = 0 := by
  intro x hx
  have h1 : (Z x) i = Commons.Geometry.Ulam.profileX x := by
    have h := htail x hx
    rw [h]
    rcases hi with rfl | rfl <;> simp
  unfold dev
  rw [h1, sub_self]

lemma dev_ident1 {Z : ℝ → Work.OddVolterra.St} {x : ℝ} (hx : 1/4 < x) (i j : Fin 4)
    (hderiv : ∀ s : ℝ, 1/4 ≤ s → deriv (fun u : ℝ => Z u i) s = Z s j)
    (hZsm : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (0 : ℝ))) :
    deriv (dev Z i) x = Z x j - deriv Commons.Geometry.Ulam.profileX x := by
  have hsub : dev Z i = (fun u : ℝ => Z u i) - Commons.Geometry.Ulam.profileX := rfl
  rw [hsub, deriv_sub (comp_diff (by linarith) i hZsm) (profX_diff x)]
  rw [hderiv x (le_of_lt hx)]

lemma dev_ident2 {Z : ℝ → Work.OddVolterra.St} {x : ℝ} (hx : 1/4 < x) (i j : Fin 4)
    (hderiv : ∀ s : ℝ, 1/4 ≤ s → deriv (fun u : ℝ => Z u i) s = Z s j)
    (hZsm : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (0 : ℝ))) :
    deriv (deriv (dev Z i)) x =
      deriv (fun u : ℝ => Z u j) x - deriv (deriv Commons.Geometry.Ulam.profileX) x := by
  have hev : deriv (dev Z i) =ᶠ[𝓝 x]
      (fun y : ℝ => Z y j - deriv Commons.Geometry.Ulam.profileX y) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show (1/4:ℝ) < x from hx)] with y hy
    exact dev_ident1 hy i j hderiv hZsm
  rw [hev.deriv_eq]
  exact deriv_sub (comp_diff (by linarith) j hZsm) (deriv_profX_diff x)

lemma dev_bounds {Z : ℝ → Work.OddVolterra.St} (i j : Fin 4) (hi : i = 0 ∨ i = 1) (hj : j = 2 ∨ j = 3)
    (hZsm : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (0 : ℝ)))
    (htail : ∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → Z s = Work.OddVolterra.baseState s)
    (hval : ∀ s : ℝ, 1 / 4 ≤ s → |Z s i - Commons.Geometry.Ulam.profileX s| ≤ 1 / 1000)
    (hderiv : ∀ s : ℝ, 1/4 ≤ s → deriv (fun u : ℝ => Z u i) s = Z s j)
    (hdd : ∀ s : ℝ, 1 / 4 ≤ s →
      |deriv (fun u : ℝ => Z u j) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 1000) :
    ∀ x : ℝ, 1 / 4 < x →
      |dev Z i x| ≤ 1 / 1000 ∧
      |deriv (dev Z i) x| ≤ 1 / 1000 * max 0 (9 / 10 - x) ∧
      |deriv (deriv (dev Z i)) x| ≤ 1 / 1000 := by
  intro x hx
  have hx4 : (1/4 : ℝ) ≤ x := le_of_lt hx
  have h2 : |deriv (deriv (dev Z i)) x| ≤ 1/1000 := by
    rw [dev_ident2 hx i j hderiv hZsm]
    exact hdd x hx4
  refine ⟨?_, ?_, h2⟩
  · unfold dev
    exact hval x hx4
  · by_cases hx9 : x < 9/10
    · have hdiff : ∀ y ∈ Set.Icc x (9/10), DifferentiableAt ℝ (deriv (dev Z i)) y := by
        intro y hy
        have hy4 : (1/4 : ℝ) < y := lt_of_lt_of_le hx hy.1
        have hev : deriv (dev Z i) =ᶠ[𝓝 y]
            (fun z : ℝ => Z z j - deriv Commons.Geometry.Ulam.profileX z) := by
          filter_upwards [isOpen_Ioi.mem_nhds hy4] with z hz
          exact dev_ident1 hz i j hderiv hZsm
        rw [hev.differentiableAt_iff]
        exact (comp_diff (by linarith) j hZsm).sub (deriv_profX_diff y)
      have h9 : deriv (dev Z i) (9/10) = 0 := by
        rw [dev_ident1 (by norm_num) i j hderiv hZsm]
        have hb : Z (9/10) = Work.OddVolterra.baseState (9/10) :=
          htail (9/10) (by norm_num [Work.OddVolterra.tau])
        rw [hb]
        rcases hj with rfl | rfl <;> simp [baseState_two, baseState_three]
      have hmvt : ‖deriv (dev Z i) (9/10) - deriv (dev Z i) x‖ ≤ 1/1000 * (9/10 - x) := by
        refine norm_image_sub_le_of_norm_deriv_le_segment'
          (f := deriv (dev Z i)) (f' := deriv (deriv (dev Z i)))
          (a := x) (b := 9/10) ?_ ?_ (9/10) (right_mem_Icc.mpr (le_of_lt hx9))
        · intro y hy
          exact ((hdiff y hy).hasDerivAt).hasDerivWithinAt
        · intro y hy
          have hy4 : (1/4 : ℝ) < y := lt_of_lt_of_le hx hy.1
          have hb := hdd y (le_of_lt hy4)
          rw [dev_ident2 hy4 i j hderiv hZsm]
          simpa [Real.norm_eq_abs] using hb
      rw [Real.norm_eq_abs, h9, zero_sub, abs_neg] at hmvt
      calc |deriv (dev Z i) x| ≤ 1/1000 * (9/10 - x) := hmvt
        _ = 1/1000 * max 0 (9/10 - x) := by
              rw [max_eq_right (by linarith : (0:ℝ) ≤ 9/10 - x)]
    · push Not at hx9
      have h0 : deriv (dev Z i) x = 0 := by
        rcases eq_or_lt_of_le hx9 with h | h
        · rw [← h, dev_ident1 (by norm_num) i j hderiv hZsm]
          have hb : Z (9/10) = Work.OddVolterra.baseState (9/10) :=
            htail (9/10) (by norm_num [Work.OddVolterra.tau])
          rw [hb]
          rcases hj with rfl | rfl <;> simp [baseState_two, baseState_three]
        · have hev : dev Z i =ᶠ[𝓝 x] 0 := by
            filter_upwards [isOpen_Ioi.mem_nhds h] with y hy
            have hy' : (9/10 : ℝ) ≤ y := le_of_lt hy
            refine dev_tail i hi htail y ?_
            have ht : (1 : ℝ) - Work.OddVolterra.tau = 9/10 := by norm_num [Work.OddVolterra.tau]
            rw [ht]; exact hy'
          rw [hev.deriv_eq]
          exact deriv_const x 0
      rw [h0, abs_zero]
      have hmax : max 0 (9/10 - x) = 0 := max_eq_left (by linarith)
      rw [hmax, mul_zero]

end Work.OddVolterra.Existence
