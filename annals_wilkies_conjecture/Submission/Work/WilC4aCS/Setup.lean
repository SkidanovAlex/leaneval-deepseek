/-
  WilC4aCS.Setup: the simultaneous real Weierstrass preparation of the family `{F} ∪ {gⱼ}`, with all
  the neighbourhood data (identity, nonvanishing units, stable signs, degree ≥ 1) gathered into one
  radius.  This is the first half of the `F ≢ 0` case of the curve-selection induction step.
-/
import Submission.Work.WilC4aCS.Defs

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators
open WilkiesConjecture WilkiesDesign WilkiesDesign.CG

namespace Work.WilC4aCS

open WilkiesDesign.CG.C4a
open WilkiesDesign.E

/-- The family combining the equation with the inequalities: index `0` is `F`, index `j.succ` is
`g j`. -/
def combineFam {l : ℕ} {α : Type*} (F : α) (g : Fin l → α) : Fin (l + 1) → α :=
  Fin.cases F g

@[simp] theorem combineFam_zero {l : ℕ} {α : Type*} (F : α) (g : Fin l → α) :
    combineFam F g 0 = F := rfl

@[simp] theorem combineFam_succ {l : ℕ} {α : Type*} (F : α) (g : Fin l → α) (j : Fin l) :
    combineFam F g (Fin.succ j) = g j := rfl

/-- The output of simultaneous real Weierstrass preparation applied to `{F} ∪ {gⱼ}` at the origin,
together with a radius on which all its consequences hold.  `d 0 ≥ 1` because `F 0 = 0` and `F` is
not identically zero. -/
structure WSetup {n l : ℕ} (F : (Fin (n + 1) → ℝ) → ℝ)
    (g : Fin l → (Fin (n + 1) → ℝ) → ℝ) where
  L : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ)
  d : Fin (l + 1) → ℕ
  a : ∀ i, Fin (d i) → (Fin n → ℝ) → ℝ
  u : Fin (l + 1) → (Fin (n + 1) → ℝ) → ℝ
  δ : ℝ
  hδ : 0 < δ
  hid : ∀ x, ‖x‖ < δ → ∀ i, combineFam F g i (L x) = u i x * wpoly (a i) x
  hu : ∀ x, ‖x‖ < δ → ∀ i, u i x ≠ 0
  hus : ∀ x, ‖x‖ < δ → ∀ i, SignType.sign (u i x) = SignType.sign (u i 0)
  han : ∀ i j, AnalyticAt ℝ (a i j) 0
  han0 : ∀ i j, a i j 0 = 0
  hu0 : ∀ i, u i 0 ≠ 0
  hd0 : 1 ≤ d 0

/-- **Weierstrass setup.**  If `F` and the `gⱼ` are analytic at the origin, vanish there, and are not
identically zero as germs, then `RealWeierstrass` produces the prepared family. -/
theorem wsetup_exists {n l : ℕ} (F : (Fin (n + 1) → ℝ) → ℝ)
    (g : Fin l → (Fin (n + 1) → ℝ) → ℝ) (hF : AnalyticAt ℝ F 0)
    (hg : ∀ j, AnalyticAt ℝ (g j) 0) (hF0 : F 0 = 0) (hg0 : ∀ j, g j 0 = 0)
    (hFnz : ¬ (F =ᶠ[𝓝 0] 0)) (hgnz : ∀ j, ¬ (g j =ᶠ[𝓝 0] 0))
    (hW : RealWeierstrass) : Nonempty (WSetup F g) := by
  have hAnal : ∀ i : Fin (l + 1), AnalyticAt ℝ (combineFam F g i) 0 := fun i =>
    Fin.cases (motive := fun i => AnalyticAt ℝ (combineFam F g i) 0) hF (fun j => hg j) i
  have hZero : ∀ i : Fin (l + 1), combineFam F g i 0 = 0 := fun i =>
    Fin.cases (motive := fun i => combineFam F g i 0 = 0) hF0 (fun j => hg0 j) i
  have hNz : ∀ i : Fin (l + 1),
      ¬ (combineFam F g i =ᶠ[𝓝 0] fun _ : Fin (n + 1) → ℝ => (0 : ℝ)) := fun i =>
    Fin.cases (motive := fun i => ¬ (combineFam F g i =ᶠ[𝓝 0] fun _ => (0 : ℝ))) hFnz
      (fun j => hgnz j) i
  obtain ⟨L, d, a, u, han, hu, hident⟩ := hW n (l + 1) (combineFam F g) hAnal hZero hNz
  -- (a) a radius on which the prepared identity holds
  obtain ⟨δ₁, hδ₁, hid₁⟩ : ∃ δ > (0 : ℝ),
      ∀ x, ‖x‖ < δ → ∀ i, combineFam F g i (L x) = u i x * wpoly (a i) x := by
    rcases Metric.eventually_nhds_iff.mp hident with ⟨ε, hε, hε'⟩
    exact ⟨ε, hε, fun x hx i => hε' (by simpa [dist_zero_right] using hx) i⟩
  -- (b) a radius on which the units are nonzero with constant sign
  have hev : ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℝ), ∀ i : Fin (l + 1),
      u i x ≠ 0 ∧ SignType.sign (u i x) = SignType.sign (u i 0) := by
    rw [Filter.eventually_all]
    intro i
    rcases lt_or_gt_of_ne (hu i).2.symm with hpos | hneg
    · have h1 : ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℝ), 0 < u i x :=
        (hu i).1.continuousAt.tendsto.eventually_mem (isOpen_Ioi.mem_nhds hpos)
      filter_upwards [h1] with x hx
      exact ⟨ne_of_gt hx, by rw [sign_pos hx, sign_pos hpos]⟩
    · have h1 : ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℝ), u i x < 0 :=
        (hu i).1.continuousAt.tendsto.eventually_mem (isOpen_Iio.mem_nhds hneg)
      filter_upwards [h1] with x hx
      exact ⟨ne_of_lt hx, by rw [sign_neg hx, sign_neg hneg]⟩
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.eventually_nhds_iff.mp hev
  -- (c) the degree of the equation is positive
  have hd0 : 1 ≤ d 0 := by
    have h0 := hid₁ 0 (by simpa using hδ₁) 0
    rw [map_zero, hZero 0] at h0
    have hwp : wpoly (a 0) (0 : Fin (n + 1) → ℝ) = 0 ^ (d 0) := by
      have hinit : Fin.init (0 : Fin (n + 1) → ℝ) = 0 := by ext j; rfl
      simp only [wpoly, Pi.zero_apply, hinit]
      rw [Finset.sum_eq_zero (fun i _ => by rw [(han 0 i).2, zero_mul])]
      rw [add_zero]
    have h0' : (0 : ℝ) ^ (d 0) = 0 := by
      have h1 : u 0 0 * wpoly (a 0) 0 = 0 := h0.symm
      rw [hwp] at h1
      exact (mul_eq_zero.mp h1).resolve_left (hu 0).2
    by_contra hlt
    have hd : d 0 = 0 := Nat.lt_one_iff.mp (Nat.lt_of_not_le hlt)
    rw [hd, pow_zero] at h0'
    exact one_ne_zero h0'
  refine ⟨⟨L, d, a, u, min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_, ?_, ?_, ?_, ?_, ?_, hd0⟩⟩
  · intro x hx i
    exact hid₁ x (lt_of_lt_of_le hx (min_le_left _ _)) i
  · intro x hx i
    exact (hδ₂' (by simpa [dist_zero_right] using lt_of_lt_of_le hx (min_le_right _ _)) i).1
  · intro x hx i
    exact (hδ₂' (by simpa [dist_zero_right] using lt_of_lt_of_le hx (min_le_right _ _)) i).2
  · exact fun i j => (han i j).1
  · exact fun i j => (han i j).2
  · exact fun i => (hu i).2

end Work.WilC4aCS
