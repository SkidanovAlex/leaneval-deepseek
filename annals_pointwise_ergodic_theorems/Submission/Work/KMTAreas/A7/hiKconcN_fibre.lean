/-
# The fibre form of the kernel `hiKconcN` of the concrete §5 column (Area A7)

This module proves `Work.KMTAreas.A7.hiKconcN_fibre`: the bilinear kernel

`hiKconcN ρ P N l₁ l₂ k₁ k₂ = kernComp (khalf N P) (hiKer ρ l₁ (varphiN N k₁))
                                          (hiKer ρ l₂ (varphitildeN P.natDegree N k₂))`

of the concrete column (`ModelApproxHiKernels.lean`) is the double Fourier integral

`∑_{α ∈ (ℚ/ℤ)_{l₁}} ∑_{β ∈ (ℚ/ℤ)_{l₂}} e(-j₁α) e(-j₂β)
   ∫∫ φ_N(θ₁) φ̃_N(θ₂) weylAvg P N α β θ₁ θ₂ e(-j₁θ₁-j₂θ₂) dθ₁dθ₂`

of the two bumps and the discrete average `weylAvg` of §6 of Krause--Mirek--Tao.

The two ingredients are

* the collapse of the composed kernel with the halved average
  (`Work.KMTAreas.A7.smallKconc_coeff`, itself `kernComp_khalf` + `tmKernel_coeff`), which
  turns `hiKconcN` into `N⁻¹ ∑_{n ∈ Ioc (N/2) N}` of the products of the two arithmetic
  character sums and the two coefficient kernels `cw`;
* the evaluation of the `θ₁θ₂`-integral of `weylAvg` against the two bumps
  (`Work.KMTAreas.A7.theta_double_cw`), which produces exactly the same finite sum;

the remaining step is the elementary sum rearrangement that reorders the double sum over
`(ℚ/ℤ)_{l₁} × (ℚ/ℤ)_{l₂}` and the finite sum over `n`, using the character identity
`fourier (-j) α * fourier n α = fourier (n - j) α` (`fourier_add`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxHiKernels
import Submission.Work.KMTAreas.A7.smallKconc_coeff
import Submission.Work.KMTAreas.A7.theta_double_cw

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-! ## Elementary finite-sum rearrangements -/

/-- Factorisation of a double sum of products: `∑_x ∑_y p x * q y = (∑_x p x)(∑_y q y)`. -/
private lemma sum_sum_mul {ι κ : Type*} (s : Finset ι) (t : Finset κ) (p : ι → ℂ) (q : κ → ℂ) :
    (∑ x ∈ s, ∑ y ∈ t, p x * q y) = (∑ x ∈ s, p x) * (∑ y ∈ t, q y) := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun x _ => (Finset.mul_sum t q (p x)).symm)

/-- Exchange of the outer and the inner index of a triple sum. -/
private lemma sum_comm₃ {ι κ μ : Type*} (s : Finset ι) (t : Finset κ) (u : Finset μ)
    (f : ι → κ → μ → ℂ) :
    (∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, f x y z) = ∑ z ∈ u, ∑ x ∈ s, ∑ y ∈ t, f x y z := by
  have h1 : (∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, f x y z) = ∑ x ∈ s, ∑ z ∈ u, ∑ y ∈ t, f x y z := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_comm]
  rw [h1, Finset.sum_comm]

/-- **Extraction of a constant from an iterated sum over the `n`-index.**  The double sum over
`(x,y)`, whose summand is a product of `a x`, `b y` with the inner sum `∑_z X x y z` prefixed by
the constant `Ninv`, equals `Ninv` times the triple sum in the order `z, x, y`. -/
private lemma fibre_sum_eq {ι κ μ : Type*} (s₁ : Finset ι) (s₂ : Finset κ) (s₃ : Finset μ)
    (Ninv : ℂ) (a : ι → ℂ) (b : κ → ℂ) (X : ι → κ → μ → ℂ) :
    (∑ x ∈ s₁, ∑ y ∈ s₂, a x * b y * (Ninv * ∑ z ∈ s₃, X x y z))
      = Ninv * ∑ z ∈ s₃, ∑ x ∈ s₁, ∑ y ∈ s₂, a x * b y * X x y z := by
  have h1 : ∀ x : ι, (∑ y ∈ s₂, a x * b y * (Ninv * (∑ z ∈ s₃, X x y z)))
      = Ninv * (∑ y ∈ s₂, a x * b y * (∑ z ∈ s₃, X x y z)) := by
    intro x
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun y _ => by ring)
  calc (∑ x ∈ s₁, ∑ y ∈ s₂, a x * b y * (Ninv * ∑ z ∈ s₃, X x y z))
      = ∑ x ∈ s₁, Ninv * (∑ y ∈ s₂, a x * b y * (∑ z ∈ s₃, X x y z)) :=
        Finset.sum_congr rfl (fun x _ => h1 x)
    _ = Ninv * (∑ x ∈ s₁, ∑ y ∈ s₂, a x * b y * (∑ z ∈ s₃, X x y z)) := by
        rw [Finset.mul_sum]
    _ = Ninv * ∑ z ∈ s₃, ∑ x ∈ s₁, ∑ y ∈ s₂, a x * b y * X x y z := by
        congr 1
        have h2 : ∀ x y, a x * b y * (∑ z ∈ s₃, X x y z) = ∑ z ∈ s₃, a x * b y * X x y z :=
          fun x y => Finset.mul_sum s₃ (fun z => X x y z) (a x * b y)
        simp only [h2]
        exact sum_comm₃ s₁ s₂ s₃ (fun x y z => a x * b y * X x y z)

/-- **The characteristic identity of the two arithmetic character sums, at a fixed scale `m`.**
The double sum over `(ℚ/ℤ)_{l₁} × (ℚ/ℤ)_{l₂}` of the two characters `e(-j₁α)`, `e(-j₂β)` times
the `m`-th summand of the fibre form of `hiKconcN` factors, by `fourier_add`, as the product of
the two closed character sums against the two coefficient kernels `cw`. -/
private lemma per_m_identity (P : Polynomial ℤ) (N k₁ k₂ : ℕ) (j₁ j₂ : ℤ)
    (F₁ F₂ : Finset Work.Analysis.IonescuWainger.Circle) (m : ℕ) :
    (∑ α ∈ F₁, ∑ β ∈ F₂,
        fourier (T := 1) (-j₁) α * fourier (T := 1) (-j₂) β
          * (fourier (T := 1) (m : ℤ) α * fourier (T := 1) (Polynomial.eval (m : ℤ) P) β
              * cw (varphiN N k₁) (j₁ - (m : ℤ))
              * cw (varphitildeN P.natDegree N k₂) (j₂ - Polynomial.eval (m : ℤ) P)))
      = ((∑ α ∈ F₁, fourier (T := 1) (-(j₁ - (m : ℤ))) α) * cw (varphiN N k₁) (j₁ - (m : ℤ)))
        * ((∑ β ∈ F₂, fourier (T := 1) (-(j₂ - Polynomial.eval (m : ℤ) P)) β)
            * cw (varphitildeN P.natDegree N k₂) (j₂ - Polynomial.eval (m : ℤ) P)) := by
  set cwf : ℂ := cw (varphiN N k₁) (j₁ - (m : ℤ)) with hcwf
  set cwψ : ℂ := cw (varphitildeN P.natDegree N k₂) (j₂ - Polynomial.eval (m : ℤ) P) with hcwψ
  set Am : ℂ := ∑ α ∈ F₁, fourier (T := 1) (-(j₁ - (m : ℤ))) α with hAdef
  set Bm : ℂ := ∑ β ∈ F₂, fourier (T := 1) (-(j₂ - Polynomial.eval (m : ℤ) P)) β with hBdef
  have hstep0 : (∑ α ∈ F₁, ∑ β ∈ F₂,
        fourier (T := 1) (-j₁) α * fourier (T := 1) (-j₂) β
          * (fourier (T := 1) (m : ℤ) α * fourier (T := 1) (Polynomial.eval (m : ℤ) P) β
              * cwf * cwψ))
      = ∑ α ∈ F₁, ∑ β ∈ F₂,
          (fourier (T := 1) (-j₁) α * fourier (T := 1) (m : ℤ) α * cwf)
            * (fourier (T := 1) (-j₂) β * fourier (T := 1) (Polynomial.eval (m : ℤ) P) β * cwψ) := by
    refine Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun β _ => ?_))
    ring
  rw [hstep0, sum_sum_mul F₁ F₂
        (fun α => fourier (T := 1) (-j₁) α * fourier (T := 1) (m : ℤ) α * cwf)
        (fun β => fourier (T := 1) (-j₂) β * fourier (T := 1) (Polynomial.eval (m : ℤ) P) β * cwψ)]
  have hAm : (∑ α ∈ F₁, fourier (T := 1) (-j₁) α * fourier (T := 1) (m : ℤ) α * cwf)
      = Am * cwf := by
    have h1 : (∑ α ∈ F₁, fourier (T := 1) (-j₁) α * fourier (T := 1) (m : ℤ) α * cwf)
        = (∑ α ∈ F₁, fourier (T := 1) (-j₁) α * fourier (T := 1) (m : ℤ) α) * cwf :=
      (Finset.sum_mul F₁ (fun α => fourier (T := 1) (-j₁) α * fourier (T := 1) (m : ℤ) α) cwf).symm
    have h2 : (∑ α ∈ F₁, fourier (T := 1) (-j₁) α * fourier (T := 1) (m : ℤ) α) = Am := by
      rw [hAdef]
      refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [show -(j₁ - (m : ℤ)) = (m : ℤ) + (-j₁) by ring, fourier_add]
      ring
    rw [h1, h2]
  have hBm : (∑ β ∈ F₂, fourier (T := 1) (-j₂) β * fourier (T := 1) (Polynomial.eval (m : ℤ) P) β * cwψ)
      = Bm * cwψ := by
    have h1 : (∑ β ∈ F₂, fourier (T := 1) (-j₂) β * fourier (T := 1) (Polynomial.eval (m : ℤ) P) β * cwψ)
        = (∑ β ∈ F₂, fourier (T := 1) (-j₂) β
            * fourier (T := 1) (Polynomial.eval (m : ℤ) P) β) * cwψ :=
      (Finset.sum_mul F₂ (fun β => fourier (T := 1) (-j₂) β
        * fourier (T := 1) (Polynomial.eval (m : ℤ) P) β) cwψ).symm
    have h2 : (∑ β ∈ F₂, fourier (T := 1) (-j₂) β
        * fourier (T := 1) (Polynomial.eval (m : ℤ) P) β) = Bm := by
      rw [hBdef]
      refine Finset.sum_congr rfl (fun β _ => ?_)
      rw [show -(j₂ - Polynomial.eval (m : ℤ) P) = Polynomial.eval (m : ℤ) P + (-j₂) by ring,
        fourier_add]
      ring
    rw [h1, h2]
  rw [hAm, hBm]

/-! ## The fibre identity -/

theorem hiKconcN_fibre (ρ : ℝ) (P : Polynomial ℤ) (N : ℕ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) :
    Work.KMTAreas.A7.hiKconcN ρ P N l₁ l₂ k₁ k₂ j₁ j₂
      = ∑ p ∈ (Work.KMTAreas.A7.diffFreqs ρ l₁).product (Work.KMTAreas.A7.diffFreqs ρ l₂),
          fourier (T := 1) (-j₁) p.1 * fourier (T := 1) (-j₂) p.2
            * (∫ θ₁ : ℝ, ∫ θ₂ : ℝ,
                Work.KMTAreas.A7.varphiN N k₁ θ₁
                * Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ θ₂
                * Work.KMTAreas.A7.weylAvg P N p.1 p.2 θ₁ θ₂
                * Work.KMTAreas.A7.ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂))) := by
  -- `hiKconcN` is the kernel `smallKconc` of the concrete column, and `smallKconc_coeff`
  -- evaluates it in exactly the form produced by the `θ₁θ₂`-integral.
  change Work.KMTAreas.A7.smallKconc ρ P l₁ l₂ k₁ k₂ N j₁ j₂ = _
  rw [Work.KMTAreas.A7.smallKconc_coeff]
  set F₁ : Finset Work.Analysis.IonescuWainger.Circle := Work.KMTAreas.A7.diffFreqs ρ l₁ with hF₁
  set F₂ : Finset Work.Analysis.IonescuWainger.Circle := Work.KMTAreas.A7.diffFreqs ρ l₂ with hF₂
  have hRHS : (∑ p ∈ F₁.product F₂,
          fourier (T := 1) (-j₁) p.1 * fourier (T := 1) (-j₂) p.2
            * (∫ θ₁ : ℝ, ∫ θ₂ : ℝ,
                Work.KMTAreas.A7.varphiN N k₁ θ₁
                * Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ θ₂
                * Work.KMTAreas.A7.weylAvg P N p.1 p.2 θ₁ θ₂
                * Work.KMTAreas.A7.ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂))))
      = ((N : ℂ))⁻¹ * ∑ m ∈ Finset.Ioc (N / 2) N,
          ((∑ α ∈ F₁, fourier (T := 1) (-(j₁ - (m : ℤ))) α)
              * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphiN N k₁) (j₁ - (m : ℤ)))
            * ((∑ α ∈ F₂, fourier (T := 1) (-(j₂ - Polynomial.eval (m : ℤ) P)) α)
                * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphitildeN P.natDegree N k₂)
                    (j₂ - Polynomial.eval (m : ℤ) P)) := by
    rw [show F₁.product F₂ = F₁ ×ˢ F₂ from rfl, Finset.sum_product]
    -- the evaluation of the `θ₁θ₂`-integral (`theta_double_cw`)
    have hJ : ∀ (α β : Work.Analysis.IonescuWainger.Circle),
        (∫ θ₁ : ℝ, ∫ θ₂ : ℝ,
            Work.KMTAreas.A7.varphiN N k₁ θ₁
              * Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ θ₂
              * Work.KMTAreas.A7.weylAvg P N α β θ₁ θ₂
              * Work.KMTAreas.A7.ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂)))
          = ((N : ℂ))⁻¹ * ∑ m ∈ Finset.Ioc (N / 2) N,
              fourier (T := 1) (m : ℤ) α * fourier (T := 1) (Polynomial.eval (m : ℤ) P) β
                * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphiN N k₁) (j₁ - (m : ℤ))
                * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphitildeN P.natDegree N k₂)
                    (j₂ - Polynomial.eval (m : ℤ) P) :=
      fun α β => theta_double_cw P N j₁ j₂ (Work.KMTAreas.A7.integrable_varphiN N k₁)
        (Work.KMTAreas.A7.integrable_varphitildeN_aux P.natDegree N k₂) α β
    simp only [hJ]
    -- extract `N⁻¹` and exchange the finite sum over `m` with the arithmetic sums
    rw [fibre_sum_eq F₁ F₂ (Finset.Ioc (N / 2) N) ((N : ℂ))⁻¹
          (fun α => fourier (T := 1) (-j₁) α) (fun β => fourier (T := 1) (-j₂) β)
          (fun α β m => fourier (T := 1) (m : ℤ) α
            * fourier (T := 1) (Polynomial.eval (m : ℤ) P) β
            * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphiN N k₁) (j₁ - (m : ℤ))
            * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphitildeN P.natDegree N k₂)
                (j₂ - Polynomial.eval (m : ℤ) P))]
    congr 1
    refine Finset.sum_congr rfl (fun m _ => ?_)
    -- the `m`-th summand, by the character identity `fourier_add`
    exact per_m_identity P N k₁ k₂ j₁ j₂ F₁ F₂ m
  rw [hRHS]

end

end Work.KMTAreas.A7
