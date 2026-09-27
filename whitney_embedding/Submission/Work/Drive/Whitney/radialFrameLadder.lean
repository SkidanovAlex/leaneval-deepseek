import Mathlib
import Submission.Work.Whitney.CutPush.transport_of_plane_family

/-!
# The radial ladder: a global smooth frame of a smooth idempotent family over `ℝ²`

Target of this module: given a smooth family `P : ℝ → ℝ → E →L[ℝ] E` of idempotents of constant rank
`k`, build a smooth family of orthonormal frames of the ranges over the whole plane.

The device is the *radial ladder*: the plane is split into the concentric shells
`A n = {x | n ≤ ‖x‖ ≤ n+1}`; on each shell the plane family is transported back to the inner
boundary by the marching construction (`Work.Drive.Whitney.marchingTransportParam`, the
`z`-parametrised version of `Work.Whitney.CutPush.exists_transport_of_plane_family`), the
"transverse" parameter being the direction; the interface frames are then chained and consecutive
shells are bonded with a smooth radial weight, the two frames agreeing exactly on the interface
circle.

## Contents
* `contDiff_gramSchmidt_gen` : Gram–Schmidt smoothness for a family over an arbitrary normed
  domain (the two-variable version of `Work.Whitney.CutPush.contDiff_gramSchmidt`).
* the polar family `polarP` and its smoothness / periodicity / idempotency / rank.
-/

open scoped ContDiff
open InnerProductSpace

namespace Work.Drive.Whitney

/-! ### Gram–Schmidt smoothness over a general normed domain -/

/-- **Smoothness of Gram–Schmidt**, for a family indexed by an arbitrary real normed space. -/
theorem contDiff_gramSchmidt_gen {k : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] (v : Z → Fin (k + 1) → E)
    (hv : ∀ i : Fin (k + 1), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Z => v z i))
    (hli : ∀ z : Z, LinearIndependent ℝ (v z)) (n : Fin (k + 1)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Z => InnerProductSpace.gramSchmidt ℝ (v z) n) := by
  have key : ∀ m : ℕ, ∀ hm : m < k + 1,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : Z => InnerProductSpace.gramSchmidt ℝ (v z) ⟨m, hm⟩) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      have hstep : (fun z : Z => InnerProductSpace.gramSchmidt ℝ (v z) ⟨m, hm⟩)
          = fun z : Z => v z ⟨m, hm⟩ - ∑ i ∈ Finset.Iio (⟨m, hm⟩ : Fin (k + 1)),
              (inner ℝ (InnerProductSpace.gramSchmidt ℝ (v z) i) (v z ⟨m, hm⟩)
                / (‖InnerProductSpace.gramSchmidt ℝ (v z) i‖ : ℝ) ^ 2)
              • InnerProductSpace.gramSchmidt ℝ (v z) i := by
        funext z
        rw [eq_sub_iff_add_eq]
        exact (InnerProductSpace.gramSchmidt_def'' ℝ (v z) ⟨m, hm⟩).symm
      rw [hstep]
      refine (hv ⟨m, hm⟩).sub ?_
      refine ContDiff.sum fun i hi => ?_
      have hi' : (i : ℕ) < m := by
        have h : i < (⟨m, hm⟩ : Fin (k + 1)) := Finset.mem_Iio.mp hi
        exact h
      have hig : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z : Z => InnerProductSpace.gramSchmidt ℝ (v z) i) := ih (i : ℕ) hi' i.isLt
      have hne : ∀ z : Z, InnerProductSpace.gramSchmidt ℝ (v z) i ≠ 0 :=
        fun z => InnerProductSpace.gramSchmidt_ne_zero i (hli z)
      have hden : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z : Z => (‖InnerProductSpace.gramSchmidt ℝ (v z) i‖ : ℝ) ^ 2) :=
        ((ContDiff.norm ℝ hig fun z => hne z).pow 2)
      have hnum : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z : Z => inner ℝ (InnerProductSpace.gramSchmidt ℝ (v z) i) (v z ⟨m, hm⟩)) :=
        (isBoundedBilinearMap_inner (𝕜 := ℝ) (E := E)).contDiff.comp
          (hig.prodMk (hv ⟨m, hm⟩))
      have hden_ne : ∀ z : Z, (‖InnerProductSpace.gramSchmidt ℝ (v z) i‖ : ℝ) ^ 2 ≠ 0 :=
        fun z => pow_ne_zero 2 (by exact_mod_cast norm_ne_zero_iff.mpr (hne z))
      exact (hnum.div hden hden_ne).smul hig
  exact key n.val n.isLt

/-- **Smoothness of normalised Gram–Schmidt** over a general normed domain. -/
theorem contDiff_gramSchmidtNormed_gen {k : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] (v : Z → Fin (k + 1) → E)
    (hv : ∀ i : Fin (k + 1), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Z => v z i))
    (hli : ∀ z : Z, LinearIndependent ℝ (v z)) (n : Fin (k + 1)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Z => InnerProductSpace.gramSchmidtNormed (𝕜 := ℝ) (v z) n) := by
  have hgs := contDiff_gramSchmidt_gen v hv hli n
  have hne : ∀ z : Z, InnerProductSpace.gramSchmidt ℝ (v z) n ≠ 0 :=
    fun z => InnerProductSpace.gramSchmidt_ne_zero n (hli z)
  have hnorm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Z => ‖InnerProductSpace.gramSchmidt ℝ (v z) n‖) :=
    ContDiff.norm ℝ hgs hne
  have hinv := hnorm.inv fun z => norm_ne_zero_iff.mpr (hne z)
  have hfun : (fun z : Z => InnerProductSpace.gramSchmidtNormed (𝕜 := ℝ) (v z) n)
      = fun z : Z => (‖InnerProductSpace.gramSchmidt ℝ (v z) n‖)⁻¹
          • InnerProductSpace.gramSchmidt ℝ (v z) n := by
    funext z
    simp [InnerProductSpace.gramSchmidtNormed]
  rw [hfun]
  exact hinv.smul hgs

/-! ### The polar family -/

/-- The plane family read in polar coordinates: `(r, θ) ↦ P (r cos θ) (r sin θ)`. -/
noncomputable def polarP {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ℝ → ℝ → E →L[ℝ] E) (r θ : ℝ) : E →L[ℝ] E :=
  P (r * Real.cos θ) (r * Real.sin θ)

theorem polarP_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ℝ → ℝ → E →L[ℝ] E) (r θ : ℝ) (y : E) :
    polarP P r θ y = P (r * Real.cos θ) (r * Real.sin θ) y := rfl

/-- Smoothness of the polar family in `(r, θ)`, operator-valued form. -/
theorem contDiff_polarP_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (P : ℝ → ℝ → E →L[ℝ] E)
    (hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : (ℝ × ℝ) × E => P p.1.1 p.1.2 p.2)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => polarP P q.1 q.2) := by
  have hfun : (fun q : ℝ × ℝ => polarP P q.1 q.2)
      = fun q : ℝ × ℝ => P (q.1 * Real.cos q.2) (q.1 * Real.sin q.2) := by
    funext q; rfl
  rw [hfun, contDiff_clm_apply_iff]
  intro y
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => (((q.1 * Real.cos q.2, q.1 * Real.sin q.2) : ℝ × ℝ), y)) := by
    fun_prop
  exact hP.comp h2

/-- Smoothness of the polar family in `(r, θ)`, evaluated form. -/
theorem contDiff_polarP {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (P : ℝ → ℝ → E →L[ℝ] E)
    (hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : (ℝ × ℝ) × E => P p.1.1 p.1.2 p.2)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℝ × ℝ) × E => polarP P q.1.1 q.1.2 q.2) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℝ × ℝ) × E => ((q.1.1, q.1.2) : ℝ × ℝ)) :=
    (contDiff_fst.comp contDiff_fst).prodMk (contDiff_snd.comp contDiff_fst)
  exact ((contDiff_polarP_clm P hP).comp h1).clm_apply contDiff_snd

theorem polarP_idem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ℝ → ℝ → E →L[ℝ] E) (hidem : ∀ a b, P a b * P a b = P a b) (r θ : ℝ) :
    polarP P r θ * polarP P r θ = polarP P r θ :=
  hidem _ _

theorem polarP_rank {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (P : ℝ → ℝ → E →L[ℝ] E)
    (hrank : ∀ a b, Module.finrank ℝ (LinearMap.range (P a b).toLinearMap) = k)
    (r θ : ℝ) :
    Module.finrank ℝ (LinearMap.range (polarP P r θ).toLinearMap) = k :=
  hrank _ _

/-- The polar family is `2π`-periodic in the angle. -/
theorem polarP_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ℝ → ℝ → E →L[ℝ] E) (r θ : ℝ) :
    polarP P r (θ + 2 * Real.pi) = polarP P r θ := by
  have hc : Real.cos (θ + 2 * Real.pi) = Real.cos θ := Real.cos_add_two_pi θ
  have hs : Real.sin (θ + 2 * Real.pi) = Real.sin θ := Real.sin_add_two_pi θ
  simp only [polarP, hc, hs]

end Work.Drive.Whitney
