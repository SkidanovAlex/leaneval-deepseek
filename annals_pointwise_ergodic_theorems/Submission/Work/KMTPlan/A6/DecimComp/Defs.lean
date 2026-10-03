/-
# The decimation fibre `Q^{-1}ℤ/ℤ` and the dyadic circle bump

This module fixes the two geometric objects in terms of which the KMSZ (6.22) decimation identity

  `kmtProj ρ l₁ (-(m₀+n)) = D_{Q}(η_{≤-(m₀+n)}) ∘ kmtProj ρ l₁ (-C₀)`,  `Q = iwQl ρ l₁`,

is phrased:

* `torsFinset Q = {a/Q : a < Q} ⊆ 𝕋 = ℝ/ℤ` — the `Q`-torsion subgroup of the circle, as a `Finset`
  (the "coarse arc set" of the KMSZ weight factor `Σ_{a<Q} 1_{ξ ≈ a/Q}`);
* `bump L = periodize (η_{≤ -L}) = η(2^L ·)` read on the circle — the dyadic bump of radius
  `2^{-L}` around `0`, equal to `1` on the arc of radius `2^{-L-1}`.

The elementary facts collected here are the ones used by the symbol identity
(`Work.KMTPlan.A6.DecimComp.symbolIdentity`) and the kernel identity
(`Work.KMTPlan.A6.DecimComp.iwKernel_torsFinset_bump`):

* `mem_torsFinset`, `arcPt_mem_torsFinset` — membership;
* `injOn_arcPt` — `a ↦ a/Q` is injective on `{0,…,Q-1}`;
* `norm_arcPt_sub_ge` and `norm_le_of_ne_mem_torsFinset` — **two distinct `Q`-torsion points are
  `1/Q`-separated** (the sharp separation fact which, combined with the narrowness `3Q < 2^{C₀}`,
  makes the level-`C₀` bumps around the torsion points pairwise disjoint);
* `mem_torsFinset_of_mem_iwArithFreqs` — every Ionescu–Wainger frequency of height `≤ l` is a
  `iwQl ρ l`-torsion point (because every `q ∈ iwP ρ l` divides `iwQl ρ l = lcm (iwP ρ l)`).
-/
import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ZModArcs
import Submission.Work.KMTPlan.A6.continuous_periodize_of_hasCompactSupport
import Submission.Work.KMTContract.etaCutRegular
import Submission.Work.BourgainPlan.Thm52.decimatedKernel_lp

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6.DecimComp

noncomputable section

open Finset
open scoped BigOperators

/-- Abbreviation for the Ionescu–Wainger circle, the same type as the Bourgain-plan circle. -/
local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- **The `Q`-torsion points `{a/Q : a < Q}` of the circle `𝕋 = ℝ/ℤ`.**  This is the coarse arc
set of the KMSZ (6.22) decimation weight factor. -/
def torsFinset (Q : ℕ) : Finset Circ :=
  (Finset.range Q).image (fun a : ℕ => Work.BourgainPlan.IonescuWainger.arcPt Q (a : ℤ))

/-- Membership in `torsFinset Q`. -/
theorem mem_torsFinset {Q : ℕ} {γ : Circ} :
    γ ∈ torsFinset Q
      ↔ ∃ a ∈ Finset.range Q, Work.BourgainPlan.IonescuWainger.arcPt Q (a : ℤ) = γ :=
  Finset.mem_image

/-- The torsion point `a/Q` lies in `torsFinset Q` when `a < Q`. -/
theorem arcPt_mem_torsFinset (Q a : ℕ) (ha : a < Q) :
    Work.BourgainPlan.IonescuWainger.arcPt Q (a : ℤ) ∈ torsFinset Q :=
  Finset.mem_image.mpr ⟨a, Finset.mem_range.mpr ha, rfl⟩

/-- The `Q`-torsion points are the `Finset.image` of `{0,…,Q-1}` under `a ↦ a/Q`. -/
theorem torsFinset_eq_image (Q : ℕ) :
    torsFinset Q = (Finset.range Q).image
      (fun a : ℕ => Work.BourgainPlan.IonescuWainger.arcPt Q (a : ℤ)) := rfl

/-- Every element of `torsFinset Q` is killed by `Q` (as a ℤ-multiple). -/
theorem zsmul_eq_zero_of_mem_torsFinset {Q : ℕ} {γ : Circ} (h : γ ∈ torsFinset Q) :
    (Q : ℤ) • γ = 0 := by
  have hQ : Q ≠ 0 := by
    rintro rfl
    obtain ⟨a, ha, -⟩ := mem_torsFinset.mp h
    rw [Finset.mem_range] at ha
    omega
  obtain ⟨a, -, rfl⟩ := mem_torsFinset.mp h
  exact Work.BourgainPlan.IonescuWainger.zsmul_arcPt_eq_zero hQ (dvd_refl Q)

/-- **Injectivity of `a ↦ a/Q` on `{0, …, Q-1}`** (for `Q ≥ 1`). -/
theorem injOn_arcPt {Q : ℕ} (hQ : 1 ≤ Q) :
    Set.InjOn (fun a : ℕ => Work.BourgainPlan.IonescuWainger.arcPt Q (a : ℤ))
      (Finset.range Q) := by
  intro a ha b hb hab
  rw [Finset.mem_coe] at ha hb
  rw [Finset.mem_range] at ha hb
  have hQ0 : Q ≠ 0 := by omega
  have hdvd : (Q : ℤ) ∣ ((a : ℤ) - (b : ℤ)) :=
    (Work.BourgainPlan.IonescuWainger.arcPt_eq_arcPt_iff_dvd hQ0 (a : ℤ) (b : ℤ)).mp hab
  have hlt : |(a : ℤ) - (b : ℤ)| < (Q : ℤ) := by
    rw [abs_lt]; constructor <;> omega
  have h0 : (a : ℤ) - (b : ℤ) = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  omega

/-- **Distinct `Q`-torsion points of the form `a/Q`, `b/Q` with `a, b < Q` are `1/Q`-separated.** -/
theorem norm_arcPt_sub_ge {Q : ℕ} (hQ : 1 ≤ Q) {a b : ℕ} (ha : a < Q) (hb : b < Q)
    (hne : a ≠ b) :
    1 / (Q : ℝ) ≤ ‖Work.BourgainPlan.IonescuWainger.arcPt Q (a : ℤ)
      - Work.BourgainPlan.IonescuWainger.arcPt Q (b : ℤ)‖ := by
  have hQ0 : Q ≠ 0 := by omega
  rw [Work.BourgainPlan.IonescuWainger.arcPt_sub_same]
  refine Work.BourgainPlan.IonescuWainger.norm_arcPt_ge hQ ?_
  intro hzero
  have hdvd : (Q : ℤ) ∣ ((a : ℤ) - (b : ℤ)) :=
    (Work.BourgainPlan.IonescuWainger.arcPt_eq_zero_iff_dvd hQ0 _).mp hzero
  have hlt : |(a : ℤ) - (b : ℤ)| < (Q : ℤ) := by
    rw [abs_lt]; constructor <;> omega
  have h0 : (a : ℤ) - (b : ℤ) = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  exact hne (by omega)

/-- **Two distinct elements of `torsFinset Q` are `1/Q`-separated.** -/
theorem norm_le_of_ne_mem_torsFinset {Q : ℕ} (hQ : 1 ≤ Q) {x y : Circ}
    (hx : x ∈ torsFinset Q) (hy : y ∈ torsFinset Q) (hne : x ≠ y) :
    1 / (Q : ℝ) ≤ ‖x - y‖ := by
  obtain ⟨a, ha, rfl⟩ := mem_torsFinset.mp hx
  obtain ⟨b, hb, rfl⟩ := mem_torsFinset.mp hy
  rw [Finset.mem_range] at ha hb
  refine norm_arcPt_sub_ge hQ ha hb ?_
  intro hab
  exact hne (by rw [hab])

/-- **Every Ionescu–Wainger frequency of height `≤ l` is a `iwQl ρ l`-torsion point.** -/
theorem mem_torsFinset_of_mem_iwArithFreqs {ρ : ℝ} {l : ℕ}
    {α : Circ} (h : α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l) :
    α ∈ torsFinset (Work.Analysis.IonescuWainger.iwQl ρ l) := by
  obtain ⟨a, ha, hcoe⟩ :=
    Work.Analysis.IonescuWainger.eq_div_of_nsmul_eq_zero
      (Work.Analysis.IonescuWainger.iwQl_pos (ρ := ρ) (l := l))
      (Work.Analysis.IonescuWainger.iwQl_nsmul_eq_zero h)
  refine Finset.mem_image.mpr ⟨a, ha, ?_⟩
  rw [Work.BourgainPlan.IonescuWainger.arcPt]
  exact hcoe

/-! ## The dyadic circle bump -/

/-- **The dyadic bump `bump L = η_{≤ -L} = η(2^L ·)` on the circle.**  It is supported in the arc
of radius `2^{-L}` around `0` and equals `1` on the arc of radius `2^{-L-1}`. -/
def bump (L : ℕ) : Circ → ℂ :=
  Work.Analysis.IonescuWainger.periodize
    (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ)))

@[simp] theorem bump_apply (L : ℕ) (ξ : Circ) :
    bump L ξ = Work.Analysis.IonescuWainger.periodize
      (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))) ξ := rfl

/-- `bump L` is the periodisation of the rescaled cutoff `η_{≤ -L}`. -/
theorem bump_eq (L : ℕ) :
    bump L = Work.Analysis.IonescuWainger.periodize
      (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))) := rfl

/-- The rescaled cutoff `η_{≤ -L}` has compact support. -/
theorem hasCompactSupport_etaCut (L : ℕ) :
    HasCompactSupport (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-((2 : ℝ) ^ (-(L : ℤ)))) ((2 : ℝ) ^ (-(L : ℤ)))) isCompact_Icc ?_
  intro x hx
  have h : ¬ ((2 : ℝ) ^ (-(L : ℤ)) ≤ |x|) :=
    fun hh => hx ((Work.KMTContract.etaCutRegular (-(L : ℤ))).2.2 x hh)
  rw [not_le, abs_lt] at h
  exact ⟨le_of_lt h.1, le_of_lt h.2⟩

/-- `bump L` is continuous. -/
theorem continuous_bump (L : ℕ) : Continuous (bump L) := by
  rw [bump_eq]
  exact Work.KMTPlan.A6.continuous_periodize_of_hasCompactSupport _
    ((Work.KMTContract.etaCutRegular (-(L : ℤ))).1.continuous) (hasCompactSupport_etaCut L)


end

end Work.KMTPlan.A6.DecimComp
