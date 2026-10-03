/-
# The canonical lift, the periodisation of a narrow bump, and the collapse of the
Ionescu--Wainger symbols

Elementary support lemmas used by `Work.KMTAreas.A7.smallKernelMass_le` (the §6 kernel-mass bound
of Area A7): they are the input to the collapse identity
`Σ₁ − Σ₂ = ∑_α Φ₁(θ₁-α₁)Φ₂(θ₂-α₂)·M0(α, ξ)` of the docstring of that file.

* `lift` — the canonical representative in `[-1/2, 1/2)` of an element of `𝕋 = ℝ/ℤ`;
* `periodize_eq_lift` — if `φ` is supported in `[-w,w]` with `w < 1/2`, then
  `periodize φ γ = φ (lift γ)`;
* `iwSymbolSet_eq_of_nonAliasing`, `sum_weighted_eq_of_nonAliasing` — over a non-aliasing
  frequency set `A` at scale `k`, only the term with `α = β` of `∑_{α∈A} c α · Φ (θ - α)` survives.

They are kept in this separate module so that they can be verified independently of
`A7/SmallModApprox.lean` (which a concurrent agent temporarily put into an import cycle).
-/
import Mathlib
import Submission.Work.Analysis.IonescuWainger.EtaCut
import Submission.Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing
import Submission.Work.Analysis.IonescuWainger.iwQl_le
import Submission.Work.Analysis.IonescuWainger.iw_height_card_le
import Submission.Work.Analysis.IonescuWainger.memLp_periodize
import Submission.Work.Analysis.IonescuWainger.multiplier_add
import Submission.Work.Analysis.IonescuWainger.multiplier_comp
import Submission.Work.Analysis.IonescuWainger.norm_iwOpSet_le
import Submission.Work.Analysis.IonescuWainger.one_div_le_norm_of_ne
import Submission.Work.Analysis.IonescuWainger.supportedInArc_periodize

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Finset
open scoped BigOperators
open Work.Analysis.IonescuWainger

/-! ## The canonical lift, the periodisation of a narrow bump, and the collapse of the
Ionescu--Wainger symbols

These are the elementary facts on which the collapse `Σ₁ - Σ₂ = ∑_α (spike at α)` rests. -/

/-- The canonical representative of `γ : 𝕋 = ℝ/ℤ` in `[-1/2, 1/2)`. -/
noncomputable def lift (γ : AddCircle (1 : ℝ)) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) (-(1/2)) γ).val

theorem lift_mem (γ : AddCircle (1 : ℝ)) : lift γ ∈ Set.Ico (-(1/2) : ℝ) (1/2) := by
  unfold lift
  rw [Set.mem_Ico]
  have h := (AddCircle.equivIco (1 : ℝ) (-(1/2)) γ).prop
  rw [Set.mem_Ico] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  have : (-(1/2) : ℝ) + 1 = 1/2 := by norm_num
  linarith

theorem lift_coe (γ : AddCircle (1 : ℝ)) : ((lift γ : ℝ) : AddCircle (1 : ℝ)) = γ := by
  simpa only [lift] using AddCircle.coe_equivIco (p := (1 : ℝ)) (a := -(1/2)) (y := γ)

/-- **The periodisation of a bump of half-width `< 1/2` is the bump itself, evaluated at the
canonical lift**: for `φ` supported in `[-w, w]` with `w < 1/2` and `γ : 𝕋`,
`periodize φ γ = φ (lift γ)`. -/
theorem periodize_eq_lift {φ : ℝ → ℂ} {w : ℝ} (hw : w < 1/2)
    (hφ : ∀ x : ℝ, φ x ≠ 0 → |x| ≤ w) (γ : AddCircle (1 : ℝ)) :
    periodize φ γ = φ (lift γ) := by
  set x : ℝ := (AddCircle.equivIco (1 : ℝ) 0 γ).val with hx
  have hxmem : x ∈ Set.Ico (0 : ℝ) 1 := by
    have h := (AddCircle.equivIco (1 : ℝ) 0 γ).prop
    simpa only [hx, Set.mem_Ico, zero_add] using h
  have hx1 : (0 : ℝ) ≤ x := hxmem.1
  have hx2 : x < 1 := hxmem.2
  have hxc : ((x : ℝ) : AddCircle (1 : ℝ)) = γ := by
    simpa only [hx] using AddCircle.coe_equivIco (p := (1 : ℝ)) (a := 0) (y := γ)
  -- every term with `m ∉ {0, -1}` vanishes
  have hzero : ∀ m : ℤ, m ≠ 0 → m ≠ -1 → φ (x + m) = 0 := by
    intro m hm0 hm1
    by_contra hc
    have habs := hφ _ hc
    have hm : (m : ℝ) ≤ -2 ∨ 1 ≤ (m : ℝ) := by
      have h : m ≤ -2 ∨ 1 ≤ m := by omega
      rcases h with h | h
      · exact Or.inl (by exact_mod_cast h)
      · exact Or.inr (by exact_mod_cast h)
    rcases hm with hm | hm
    · have h1 : x + (m : ℝ) ≤ -1 := by linarith
      have h2 : (1 : ℝ) ≤ |x + m| := by
        rw [abs_of_nonpos (by linarith)]; linarith
      linarith
    · have h1 : (1 : ℝ) ≤ x + m := by linarith
      have h2 : (1 : ℝ) ≤ |x + m| := le_trans h1 (le_abs_self _)
      linarith
  have hout : ∀ m : ℤ, m ∉ ({0, -1} : Finset ℤ) → φ (x + m) = 0 := by
    intro m hm
    exact hzero m (fun h => hm (by simp [h])) (fun h => hm (by simp [h]))
  have hsum : (∑' m : ℤ, φ (x + m)) = φ x + φ (x + (-1)) := by
    rw [tsum_eq_sum (s := ({0, -1} : Finset ℤ)) hout]
    rw [Finset.sum_insert (by simp : (0 : ℤ) ∉ ({(-1 : ℤ)} : Finset ℤ)),
      Finset.sum_singleton]
    simp
  rw [periodize, hsum]
  by_cases hxhalf : x < 1/2
  · -- the canonical lift is `x`, and `φ (x - 1) = 0`
    have hlift : lift γ = x := by
      have hmem : x ∈ Set.Ico (-(1/2) : ℝ) (-(1/2) + 1) :=
        ⟨by linarith, by linarith⟩
      have h := AddCircle.equivIco_coe_of_mem (p := (1 : ℝ)) (a := -(1/2)) (y := x) hmem
      rw [← hxc, lift]
      exact h
    have hzero2 : φ (x + (-1)) = 0 := by
      by_contra hc
      have habs := hφ _ hc
      have : w < |x + (-1)| := by
        rw [abs_of_neg (by linarith)]
        linarith
      linarith
    rw [hlift, hzero2, add_zero]
  · -- `1/2 ≤ x`: the canonical lift is `x - 1`, and `φ x = 0`
    have hxge : (1/2 : ℝ) ≤ x := not_lt.mp hxhalf
    have hlift : lift γ = x + (-1) := by
      have hmem : x + (-1) ∈ Set.Ico (-(1/2) : ℝ) (-(1/2) + 1) :=
        ⟨by linarith, by linarith⟩
      have hcoe : (((x + (-1) : ℝ)) : AddCircle (1 : ℝ)) = γ := by
        rw [AddCircle.coe_add, hxc]
        simp
      have h := AddCircle.equivIco_coe_of_mem (p := (1 : ℝ)) (a := -(1/2)) (y := x + (-1)) hmem
      rw [← hcoe, lift]
      exact h
    have hzero2 : φ x = 0 := by
      by_contra hc
      have habs := hφ _ hc
      have : w < |x| := by rw [abs_of_nonneg hx1]; linarith
      linarith
    rw [hlift, hzero2, zero_add]

/-- A bump supported in `[-w,w]` with `w < 1/2` vanishes at `x + m` unless `m ∈ {0, -1}`
(where `x ∈ [0,1)`). -/
theorem hzero_aux {φ : ℝ → ℂ} {w : ℝ} (hφ : ∀ x : ℝ, φ x ≠ 0 → |x| ≤ w)
    {x : ℝ} (hx1 : 0 ≤ x) (hx2 : x < 1) (hw : w < 1/2) : ∀ m : ℤ, m ≠ 0 → m ≠ -1 →
      φ (x + m) = 0 := by
  intro m hm0 hm1
  by_contra hc
  have habs := hφ _ hc
  have hm : (m : ℝ) ≤ -2 ∨ 1 ≤ (m : ℝ) := by
    have h : m ≤ -2 ∨ 1 ≤ m := by omega
    rcases h with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  rcases hm with hm | hm
  · have h1 : x + (m : ℝ) ≤ -1 := by linarith
    have h2 : (1 : ℝ) ≤ |x + m| := by
      rw [abs_of_nonpos (by linarith)]; linarith
    linarith
  · have h1 : (1 : ℝ) ≤ x + m := by linarith
    have h2 : (1 : ℝ) ≤ |x + m| := le_trans h1 (le_abs_self _)
    linarith

/-- The canonical lift of `γ = ↑x` for `x ∈ [0, 1/2)` is `x`. -/
theorem lift_eq_of_lt {x : ℝ} {γ : AddCircle (1 : ℝ)} (hxc : ((x : ℝ) : AddCircle (1 : ℝ)) = γ)
    (hx1 : 0 ≤ x) (hxhalf : x < 1/2) : lift γ = x := by
  have hmem : x ∈ Set.Ico (-(1/2) : ℝ) (-(1/2) + 1) := ⟨by linarith, by linarith⟩
  have h := AddCircle.equivIco_coe_of_mem (p := (1 : ℝ)) (a := -(1/2)) (y := x) hmem
  rw [← hxc, lift]
  exact h

/-- The canonical lift of `γ = ↑x` for `x ∈ [1/2, 1)` is `x - 1`. -/
theorem lift_eq_of_ge {x : ℝ} {γ : AddCircle (1 : ℝ)} (hxc : ((x : ℝ) : AddCircle (1 : ℝ)) = γ)
    (hx2 : x < 1) (hxge : (1/2 : ℝ) ≤ x) : lift γ = x + (-1) := by
  have hmem : x + (-1) ∈ Set.Ico (-(1/2) : ℝ) (-(1/2) + 1) := ⟨by linarith, by linarith⟩
  have hcoe : (((x + (-1) : ℝ)) : AddCircle (1 : ℝ)) = γ := by
    rw [AddCircle.coe_add, hxc]
    simp
  have h := AddCircle.equivIco_coe_of_mem (p := (1 : ℝ)) (a := -(1/2)) (y := x + (-1)) hmem
  rw [← hcoe, lift]
  exact h

/-- **The periodisation of a narrow bump times an arbitrary factor.**  If `φ` is supported in
`[-w, w]` with `w < 1/2`, then `periodize (φ · f) γ = φ (lift γ) · f (lift γ)` for any `f`. -/
theorem periodize_mul_eq_lift {φ f : ℝ → ℂ} {w : ℝ} (hw : w < 1/2)
    (hφ : ∀ x : ℝ, φ x ≠ 0 → |x| ≤ w) (γ : AddCircle (1 : ℝ)) :
    periodize (fun x : ℝ => φ x * f x) γ = φ (lift γ) * f (lift γ) :=
  periodize_eq_lift hw (fun x hx => hφ x (fun hc => hx (by rw [hc, zero_mul]))) γ

/-- **The periodisation of a modulated narrow bump.**  If `φ` is supported in `[-w, w]` with
`w < 1/2`, then for every `c : ℝ` and `γ : 𝕋`,
`periodize (fun x => φ x * ee (c * x)) γ = φ (lift γ) * ee (c * lift γ)`.  This is the shape of
the modulated bumps `varphiNt N k t = varphiN N k · ee ((N t) ·)`, `varphitildeNt …`. -/
theorem periodize_mul_ee_eq_lift {φ : ℝ → ℂ} {w c : ℝ} (hw : w < 1/2)
    (hφ : ∀ x : ℝ, φ x ≠ 0 → |x| ≤ w) (γ : AddCircle (1 : ℝ)) :
    periodize (fun x : ℝ => φ x * Complex.exp (2 * Real.pi * Complex.I * ((c * x : ℝ) : ℂ))) γ
      = φ (lift γ) * Complex.exp (2 * Real.pi * Complex.I * ((c * lift γ : ℝ) : ℂ)) :=
  periodize_mul_eq_lift hw hφ γ

/-- **Collapse of the Ionescu--Wainger symbol over a non-aliasing frequency set.**  If `A` is
non-aliasing at scale `k`, `Φ` is supported in the arc `ℝ_{≤k}`, `β ∈ A` and `θ - β ∈ ℝ_{≤k}`,
then the only term of `iwSymbolSet A Φ θ = ∑_{α ∈ A} Φ (θ - α)` that survives is `α = β`. -/
theorem iwSymbolSet_eq_of_nonAliasing {k : ℤ}
    {A : Finset Work.Analysis.IonescuWainger.Circle}
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hNA : NonAliasing k A) (hΦ : SupportedInArc k Φ)
    {β : Work.Analysis.IonescuWainger.Circle} (hβ : β ∈ A)
    {θ : Work.Analysis.IonescuWainger.Circle}
    (hθ : ∃ y ∈ realArc k,
      ((y : ℝ) : Work.Analysis.IonescuWainger.Circle) = θ - β) :
    iwSymbolSet A Φ θ = Φ (θ - β) := by
  obtain ⟨x₀, hx₀, hx₀θ⟩ := hθ
  rw [iwSymbolSet_apply]
  refine Finset.sum_eq_single_of_mem β hβ fun α hα hne => ?_
  by_contra hc
  obtain ⟨x, hx, hxθ⟩ := hΦ (θ - α) hc
  have h1 : α + ((x : ℝ) : Work.Analysis.IonescuWainger.Circle) = θ := by
    rw [hxθ]; abel
  have h2 : β + ((x₀ : ℝ) : Work.Analysis.IonescuWainger.Circle) = θ := by
    rw [hx₀θ]; abel
  exact hne (hNA α hα β hβ x hx x₀ hx₀ (h1.trans h2.symm)).1

/-- The weighted version of `iwSymbolSet_eq_of_nonAliasing`: with arbitrary weights `c` on the
frequency set, only the term `α = β` survives. -/
theorem sum_weighted_eq_of_nonAliasing {k : ℤ}
    {A : Finset Work.Analysis.IonescuWainger.Circle}
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ}
    {c : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hNA : NonAliasing k A) (hΦ : SupportedInArc k Φ)
    {β : Work.Analysis.IonescuWainger.Circle} (hβ : β ∈ A)
    {θ : Work.Analysis.IonescuWainger.Circle}
    (hθ : ∃ y ∈ realArc k,
      ((y : ℝ) : Work.Analysis.IonescuWainger.Circle) = θ - β) :
    (∑ α ∈ A, c α * Φ (θ - α)) = c β * Φ (θ - β) := by
  obtain ⟨x₀, hx₀, hx₀θ⟩ := hθ
  refine Finset.sum_eq_single_of_mem β hβ fun α hα hne => ?_
  by_contra hc
  have hne' : Φ (θ - α) ≠ 0 := fun h => hc (by rw [h, mul_zero])
  obtain ⟨x, hx, hxθ⟩ := hΦ (θ - α) hne'
  have h1 : α + ((x : ℝ) : Work.Analysis.IonescuWainger.Circle) = θ := by
    rw [hxθ]; abel
  have h2 : β + ((x₀ : ℝ) : Work.Analysis.IonescuWainger.Circle) = θ := by
    rw [hx₀θ]; abel
  exact hne (hNA α hα β hβ x hx x₀ hx₀ (h1.trans h2.symm)).1


end

end Work.KMTAreas.A7
