import Mathlib
import Submission.Work.KMTAreas.A7.kernComp_arith_factor_gen

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- **The algebraic collapse step.**  Given the factorisation of `kernComp` over the *mixed*
frequency sets (the kernel summed over `A₁ × A₂`, the two composed kernels carrying the frequency
sums over `B₁`, `B₂`) together with the two one-variable collapse identities `hcol₁`, `hcol₂`, the
outer double sum over `A₁ × A₂` is forced onto the diagonal: every term with `α ≠ α₁` (or
`β ≠ β₁`) vanishes, so `α ∈ B₁` (resp. `β ∈ B₂`) survives and the outer sum restricts to the inner
sets — which is where the inclusions `hB₁`, `hB₂` are used. -/
private theorem kernCompArithCollapse_of_factor
    {A₁ B₁ A₂ B₂ : Finset Circ} (hB₁ : B₁ ⊆ A₁) (hB₂ : B₂ ⊆ A₂)
    (W : Circ → Circ → ℂ) (m₁ m₂ f g : ℝ → ℂ) (a b : ℤ)
    (hcol₁ : ∀ α ∈ A₁, ∀ α₁ ∈ B₁,
      (∑' j : ℤ, cw m₁ j * fourier (T := 1) (-j) (α - α₁) * cw f (a - j))
        = if α = α₁ then cw (fun x => m₁ x * f x) a else 0)
    (hcol₂ : ∀ β ∈ A₂, ∀ β₁ ∈ B₂,
      (∑' j : ℤ, cw m₂ j * fourier (T := 1) (-j) (β - β₁) * cw g (b - j))
        = if β = β₁ then cw (fun x => m₂ x * g x) b else 0)
    (hfac : kernComp
        (fun j₁ j₂ => (∑ α ∈ A₁, ∑ β ∈ A₂,
              W α β * fourier (T := 1) (-j₁) α * fourier (T := 1) (-j₂) β)
            * cw m₁ j₁ * cw m₂ j₂)
        (fun j => (∑ α ∈ B₁, fourier (T := 1) (-j) α) * cw f j)
        (fun j => (∑ β ∈ B₂, fourier (T := 1) (-j) β) * cw g j) a b
      = ∑ α ∈ A₁, ∑ β ∈ A₂, W α β *
          ∑ α₁ ∈ B₁, ∑ β₁ ∈ B₂,
            fourier (T := 1) (-a) α₁ * fourier (T := 1) (-b) β₁
            * (∑' j : ℤ, cw m₁ j * fourier (T := 1) (-j) (α - α₁) * cw f (a - j))
            * (∑' j : ℤ, cw m₂ j * fourier (T := 1) (-j) (β - β₁) * cw g (b - j))) :
    kernComp
        (fun j₁ j₂ => (∑ α ∈ A₁, ∑ β ∈ A₂,
              W α β * fourier (T := 1) (-j₁) α * fourier (T := 1) (-j₂) β)
            * cw m₁ j₁ * cw m₂ j₂)
        (fun j => (∑ α ∈ B₁, fourier (T := 1) (-j) α) * cw f j)
        (fun j => (∑ β ∈ B₂, fourier (T := 1) (-j) β) * cw g j) a b
      = ∑ α ∈ B₁, ∑ β ∈ B₂, fourier (T := 1) (-a) α * fourier (T := 1) (-b) β * W α β
          * cw (fun x => m₁ x * f x) a
          * cw (fun x => m₂ x * g x) b := by
  rw [hfac]
  -- **Step 1.**  Each pair of inner double sums collapses, by `hcol₁`, `hcol₂`, to the product
  -- of the two diagonal terms.
  have hkey : ∀ α ∈ A₁, ∀ β ∈ A₂,
      (∑ α₁ ∈ B₁, ∑ β₁ ∈ B₂, fourier (T := 1) (-a) α₁ * fourier (T := 1) (-b) β₁
          * (∑' j : ℤ, cw m₁ j * fourier (T := 1) (-j) (α - α₁) * cw f (a - j))
          * (∑' j : ℤ, cw m₂ j * fourier (T := 1) (-j) (β - β₁) * cw g (b - j)))
        = (if α ∈ B₁ then fourier (T := 1) (-a) α * cw (fun x => m₁ x * f x) a else 0)
          * (if β ∈ B₂ then fourier (T := 1) (-b) β * cw (fun x => m₂ x * g x) b else 0) := by
    intro α hα β hβ
    have h1 : (∑ α₁ ∈ B₁, ∑ β₁ ∈ B₂, fourier (T := 1) (-a) α₁ * fourier (T := 1) (-b) β₁
          * (∑' j : ℤ, cw m₁ j * fourier (T := 1) (-j) (α - α₁) * cw f (a - j))
          * (∑' j : ℤ, cw m₂ j * fourier (T := 1) (-j) (β - β₁) * cw g (b - j)))
        = (∑ α₁ ∈ B₁, fourier (T := 1) (-a) α₁
              * (∑' j : ℤ, cw m₁ j * fourier (T := 1) (-j) (α - α₁) * cw f (a - j)))
          * (∑ β₁ ∈ B₂, fourier (T := 1) (-b) β₁
              * (∑' j : ℤ, cw m₂ j * fourier (T := 1) (-j) (β - β₁) * cw g (b - j))) := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun α₁ _ => Finset.sum_congr rfl (fun β₁ _ => ?_))
      ring
    have h2 : (∑ α₁ ∈ B₁, fourier (T := 1) (-a) α₁
          * (∑' j : ℤ, cw m₁ j * fourier (T := 1) (-j) (α - α₁) * cw f (a - j)))
        = (if α ∈ B₁ then fourier (T := 1) (-a) α * cw (fun x => m₁ x * f x) a else 0) := by
      rw [show (∑ α₁ ∈ B₁, fourier (T := 1) (-a) α₁
            * (∑' j : ℤ, cw m₁ j * fourier (T := 1) (-j) (α - α₁) * cw f (a - j)))
          = ∑ α₁ ∈ B₁, (if α = α₁ then fourier (T := 1) (-a) α₁
              * cw (fun x => m₁ x * f x) a else 0) from
        Finset.sum_congr rfl (fun α₁ hα₁ => by
          rw [hcol₁ α hα α₁ hα₁]
          split_ifs <;> ring)]
      rw [Finset.sum_ite_eq]
    have h3 : (∑ β₁ ∈ B₂, fourier (T := 1) (-b) β₁
          * (∑' j : ℤ, cw m₂ j * fourier (T := 1) (-j) (β - β₁) * cw g (b - j)))
        = (if β ∈ B₂ then fourier (T := 1) (-b) β * cw (fun x => m₂ x * g x) b else 0) := by
      rw [show (∑ β₁ ∈ B₂, fourier (T := 1) (-b) β₁
            * (∑' j : ℤ, cw m₂ j * fourier (T := 1) (-j) (β - β₁) * cw g (b - j)))
          = ∑ β₁ ∈ B₂, (if β = β₁ then fourier (T := 1) (-b) β₁
              * cw (fun x => m₂ x * g x) b else 0) from
        Finset.sum_congr rfl (fun β₁ hβ₁ => by
          rw [hcol₂ β hβ β₁ hβ₁]
          split_ifs <;> ring)]
      rw [Finset.sum_ite_eq]
    rw [h1, h2, h3]
  -- **Step 2.**  The outer sum over `A₁ × A₂` restricts to `B₁ × B₂`.
  have hA : ∀ α ∈ A₁, (∑ β ∈ A₂, W α β *
        ((if α ∈ B₁ then fourier (T := 1) (-a) α * cw (fun x => m₁ x * f x) a else 0)
          * (if β ∈ B₂ then fourier (T := 1) (-b) β * cw (fun x => m₂ x * g x) b else 0)))
      = (if α ∈ B₁ then ∑ β ∈ B₂, W α β * fourier (T := 1) (-a) α
            * cw (fun x => m₁ x * f x) a * fourier (T := 1) (-b) β
            * cw (fun x => m₂ x * g x) b else 0) := by
    intro α hα
    trans (∑ β ∈ A₂, (if β ∈ B₂ then (if α ∈ B₁ then W α β * fourier (T := 1) (-a) α
            * cw (fun x => m₁ x * f x) a * fourier (T := 1) (-b) β
            * cw (fun x => m₂ x * g x) b else 0) else 0))
    · refine Finset.sum_congr rfl (fun β _ => ?_)
      by_cases hαB : α ∈ B₁ <;> by_cases hβB : β ∈ B₂ <;> simp [hαB, hβB] <;> ring
    · by_cases hαB : α ∈ B₁
      · simp only [if_pos hαB]
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hB₂]
      · simp only [if_neg hαB]
        refine Finset.sum_eq_zero (fun β _ => ?_)
        by_cases hβB : β ∈ B₂ <;> simp [hβB]
  trans (∑ α ∈ A₁, ∑ β ∈ A₂, W α β *
      ((if α ∈ B₁ then fourier (T := 1) (-a) α * cw (fun x => m₁ x * f x) a else 0)
        * (if β ∈ B₂ then fourier (T := 1) (-b) β * cw (fun x => m₂ x * g x) b else 0)))
  · exact Finset.sum_congr rfl (fun α hα => Finset.sum_congr rfl (fun β hβ => by
      rw [hkey α hα β hβ]))
  trans (∑ α ∈ A₁, (if α ∈ B₁ then ∑ β ∈ B₂, W α β * fourier (T := 1) (-a) α
        * cw (fun x => m₁ x * f x) a * fourier (T := 1) (-b) β
        * cw (fun x => m₂ x * g x) b else 0))
  · exact Finset.sum_congr rfl (fun α hα => hA α hα)
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hB₁]
  refine Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun β _ => ?_))
  ring

/-- **The two-variable collapse of `kernComp` for arithmetic kernels, with the inner frequency
sets strictly contained in the outer ones.**

Template: `Work.KMTAreas.A7.kernComp_arith_factor_aux` (in
`Submission/Work/KMTAreas/A7/HiKmodNAux.lean`, ~line 507) together with its collapse companion
`Work.KMTAreas.A7.kernComp_arith_collapse_derived` (in
`Submission/Work/KMTAreas/A7/hiKmodN_fibre.lean`, ~line 167, currently `private`); the private
helpers `dist_arith`, `one_var_ident`, `tsum_one_var`, `tsum_one_var_single`, `double_tsum_single`,
`summable_ker_factor`, `tsum_cw_sub` of those two files are the pieces to copy or re-derive.

**The only mathematical difference from `kernComp_arith_collapse_derived`**: the arithmetic kernel
is still summed over the *outer* sets `A₁`, `A₂`, but the frequency factors of the *collapsed* side
are summed over the *inner* sets `B₁ ⊆ A₁`, `B₂ ⊆ A₂`.  With `S m f a η := ∑' j, cw m j *
fourier (T := 1) (-j) η * cw f (a - j)` the rearrangement part gives
`kernComp (kernel over A₁ × A₂) (κ over B₁) (κ' over B₂) a b
  = ∑_{α ∈ A₁} ∑_{β ∈ A₂} W α β * ∑_{α₁ ∈ B₁} ∑_{β₁ ∈ B₂}
      e(-aα₁) e(-bβ₁) · S m₁ f a (α-α₁) · S m₂ g b (β-β₁)`,
and the two collapse hypotheses `hcol₁`, `hcol₂` (stated for `α ∈ A₁`, `α₁ ∈ B₁`) kill every term
with `α ≠ α₁`, `β ≠ β₁`.  The surviving terms satisfy `α ∈ B₁`, which restricts the outer double
sum: this is where the inclusions `hB₁`, `hB₂` are used. -/
theorem kernCompArithCollapseGen
    {A₁ B₁ A₂ B₂ : Finset Work.Analysis.IonescuWainger.Circle} (hB₁ : B₁ ⊆ A₁) (hB₂ : B₂ ⊆ A₂)
    (W : Work.Analysis.IonescuWainger.Circle → Work.Analysis.IonescuWainger.Circle → ℂ)
    (m₁ m₂ f g : ℝ → ℂ) (a b : ℤ)
    (hs₁ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₁ j‖)
    (hs₂ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₂ j‖)
    (hf : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw f j‖)
    (hg : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw g j‖)
    (hcol₁ : ∀ α ∈ A₁, ∀ α₁ ∈ B₁,
      (∑' j : ℤ, Work.KMTAreas.A7.cw m₁ j * fourier (T := 1) (-j) (α - α₁)
          * Work.KMTAreas.A7.cw f (a - j))
        = if α = α₁ then Work.KMTAreas.A7.cw (fun x => m₁ x * f x) a else 0)
    (hcol₂ : ∀ β ∈ A₂, ∀ β₁ ∈ B₂,
      (∑' j : ℤ, Work.KMTAreas.A7.cw m₂ j * fourier (T := 1) (-j) (β - β₁)
          * Work.KMTAreas.A7.cw g (b - j))
        = if β = β₁ then Work.KMTAreas.A7.cw (fun x => m₂ x * g x) b else 0) :
    Work.KMTAreas.A7.kernComp
        (fun j₁ j₂ => (∑ α ∈ A₁, ∑ β ∈ A₂,
              W α β * fourier (T := 1) (-j₁) α * fourier (T := 1) (-j₂) β)
            * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂)
        (fun j => (∑ α ∈ B₁, fourier (T := 1) (-j) α) * Work.KMTAreas.A7.cw f j)
        (fun j => (∑ β ∈ B₂, fourier (T := 1) (-j) β) * Work.KMTAreas.A7.cw g j) a b
      = ∑ α ∈ B₁, ∑ β ∈ B₂, fourier (T := 1) (-a) α * fourier (T := 1) (-b) β * W α β
          * Work.KMTAreas.A7.cw (fun x => m₁ x * f x) a
          * Work.KMTAreas.A7.cw (fun x => m₂ x * g x) b := by
  exact kernCompArithCollapse_of_factor hB₁ hB₂ W m₁ m₂ f g a b hcol₁ hcol₂
    (kernComp_arith_factor_gen W m₁ m₂ f g a b hs₁ hs₂ hf hg)

end

end Work.KMTAreas.A7
