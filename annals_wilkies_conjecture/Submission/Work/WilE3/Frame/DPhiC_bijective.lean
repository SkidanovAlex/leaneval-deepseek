/-
  annals_wilkies_conjecture, AREA E3, frame step: the derivative of the straightening map
  `PhiC c h ι z = (uCoord k ι z, fun a => eaEvalC c (h a) z)` at a real base point is a bijection
  as soon as the `ι`-Jacobian of `h` is invertible there.

  Writing `M a i = eaEvalC c (eaD c i (h a)) z` for the linearised `ι`-Jacobian, the derivative is
  the block map

      `v ↦ (v|_{ιᶜ}, fun a => ∑ i, M a i * v i)`,

  a `U k ι`-block which is just the projection and a `Fin j`-block which is the row matrix `M`.
  Since `hd` forces `ι` injective, `Fin k` is the disjoint union of `range ι` and its complement
  `U k ι`, so the domain splits accordingly: after the coordinate splitting `σ v = (v|_{ιᶜ}, v ∘ ι)`
  (a bijection) the map becomes the *triangular* map

      `T (u, w) = (u, A *ᵥ w + B *ᵥ u)`,

  where `A a b = M a (ι b)` is the (`j × j`) `ι`-Jacobian and `B a i = M a i.1`.  `A` is invertible
  by hypothesis, so `T` is a bijection (its diagonal blocks are `id` and `A`), and hence so is
  `DPhiC`: injectivity from the trivial kernel of `A`, surjectivity from `w = A⁻¹ *ᵥ (y - B *ᵥ u)`.
-/
import Mathlib
import Submission.Work.WilE3.Frame.straighteningDefs
import Submission.Work.WilE3.Frame.sum_univ_split_iota

namespace Work.WilE3.Frame

set_option maxHeartbeats 1600000
noncomputable section
open Classical Topology Matrix
open WilkiesDesign.E

variable {k r j : ℕ}

/-! ## §1. Splitting `Fin k` along an injective `ι`

The combinatorial input `sum_univ_split_iota` (image plus complement) is proved in
`Frame/sum_univ_split_iota.lean`; the coordinate splitting itself is `split_map_bij` below. -/

/-- Splitting a vector `v : Fin k → ℂ` into its restriction to the `ι`-complement coordinates
`U k ι` and its restriction to the image of `ι` is a bijection. -/
lemma split_map_bij {k j : ℕ} (ι : Fin j → Fin k) (hι : Function.Injective ι) :
    Function.Bijective (fun v : Fin k → ℂ =>
      (fun i : U k ι => v i.1, fun b : Fin j => v (ι b))) := by
  classical
  constructor
  · rintro v w hvw
    have h1 : (fun i : U k ι => v i.1) = (fun i : U k ι => w i.1) := congrArg Prod.fst hvw
    have h2 : (fun b : Fin j => v (ι b)) = (fun b : Fin j => w (ι b)) := congrArg Prod.snd hvw
    funext i
    by_cases hi : i ∈ Set.range ι
    · obtain ⟨b, rfl⟩ := hi
      exact congrFun h2 b
    · exact congrFun h1 ⟨i, hi⟩
  · rintro ⟨u, w⟩
    refine ⟨fun i => if h : i ∈ Set.range ι then w (Set.mem_range.mp h).choose else u ⟨i, h⟩, ?_⟩
    refine Prod.ext ?_ ?_
    · funext i
      dsimp only
      exact dite_eq_right i.2
    · funext b
      dsimp only
      rw [dite_eq_left (Set.mem_range_self b)]
      exact congrArg w (hι (Set.mem_range.mp (Set.mem_range_self b)).choose_spec)

/-! ## §2. The derivative of the straightening map at a real base point -/

/-- The derivative `DPhiC c h ι (toC x)` of the straightening map `PhiC` at the real base point `x`
is a bijection, provided the `ι`-Jacobian of `h` is invertible at `x`.  (`hd` also forces `ι`
injective, so the two sides have the same dimension `k`.) -/
theorem DPhiC_bijective {k r j : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (h : Fin j → WilkiesDesign.E.EAPoly k r) (ι : Fin j → Fin k) (x : Fin k → ℝ)
    (hd : (Matrix.of fun a b =>
      Work.WilE3.eaEvalC c (WilkiesDesign.E.eaD c (ι b) (h a))
        (Work.WilE3.Frame.toC x)).det ≠ 0) :
    Function.Bijective (Work.WilE3.Frame.DPhiC c h ι (Work.WilE3.Frame.toC x)) := by
  classical
  -- `hd` forces `ι` injective: two equal columns kill the determinant.
  have hι : Function.Injective ι := by
    intro a b hab
    by_contra hne
    exact hd (Matrix.det_zero_of_column_eq hne (fun k => by simp [hab]))
  -- abbreviations: the linearised Jacobian `M`, its `ι`-block `A` and its complement block `B`
  set M : Fin j → Fin k → ℂ := fun a i => eaEvalC c (eaD c i (h a)) (toC x) with hM
  set A : Matrix (Fin j) (Fin j) ℂ := Matrix.of fun a b => M a (ι b) with hA
  set B : Matrix (Fin j) (U k ι) ℂ := Matrix.of fun a i => M a i.1 with hB
  have hAdet : A.det ≠ 0 := by
    rw [hA, hM]
    exact hd
  have hAinj : Function.Injective A.mulVec :=
    (Matrix.mulVec_injective_iff_isUnit (A := A)).mpr
      ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hAdet))
  -- the triangular map on the split coordinates
  set T : (U k ι → ℂ) × (Fin j → ℂ) → (U k ι → ℂ) × (Fin j → ℂ) :=
    fun p => (p.1, A *ᵥ p.2 + B *ᵥ p.1) with hT
  have hT_bij : Function.Bijective T := by
    constructor
    · rintro ⟨u₁, w₁⟩ ⟨u₂, w₂⟩ hEq
      rw [hT] at hEq
      have h1 : u₁ = u₂ := congrArg Prod.fst hEq
      have h2 : A *ᵥ w₁ + B *ᵥ u₁ = A *ᵥ w₂ + B *ᵥ u₂ := congrArg Prod.snd hEq
      have h3 : A *ᵥ w₁ = A *ᵥ w₂ := by
        rw [h1] at h2
        exact add_right_cancel h2
      rw [h1, hAinj h3]
    · rintro ⟨u, y⟩
      refine ⟨(u, A⁻¹ *ᵥ (y - B *ᵥ u)), ?_⟩
      rw [hT]
      show (u, A *ᵥ (A⁻¹ *ᵥ (y - B *ᵥ u)) + B *ᵥ u) = (u, y)
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hAdet),
        Matrix.one_mulVec]
      simp
  -- the two blocks, applied to a vector
  have hsumA : ∀ (a : Fin j) (w : Fin j → ℂ), (A *ᵥ w) a = ∑ b, M a (ι b) * w b := by
    intro a w
    rw [hA, Matrix.mulVec_apply]
    simp only [dotProduct, Matrix.row, Matrix.of_apply]
  have hsumB : ∀ (a : Fin j) (u : U k ι → ℂ), (B *ᵥ u) a = ∑ i : U k ι, M a i.1 * u i := by
    intro a u
    rw [hB, Matrix.mulVec_apply]
    simp only [dotProduct, Matrix.row, Matrix.of_apply]
  -- `DPhiC` is `T` after the coordinate splitting
  have hcomp : (fun v : Fin k → ℂ => (fun i : U k ι => v i.1, fun a => ∑ i, M a i * v i))
      = T ∘ (fun v : Fin k → ℂ => (fun i : U k ι => v i.1, fun b : Fin j => v (ι b))) := by
    funext v
    rw [hT]
    refine Prod.ext rfl ?_
    funext a
    show (∑ i : Fin k, M a i * v i) =
      (A *ᵥ (fun b : Fin j => v (ι b))) a + (B *ᵥ (fun i : U k ι => v i.1)) a
    rw [hsumA, hsumB]
    exact sum_univ_split_iota ι hι (fun i => M a i * v i)
  have hblock : Function.Bijective
      (fun v : Fin k → ℂ => (fun i : U k ι => v i.1, fun a => ∑ i, M a i * v i)) := by
    rw [hcomp]
    exact hT_bij.comp (split_map_bij ι hι)
  -- and it is the derivative
  have hfun : (DPhiC c h ι (toC x) : (Fin k → ℂ) → ((U k ι → ℂ) × (Fin j → ℂ)))
      = (fun v : Fin k → ℂ => (fun i : U k ι => v i.1, fun a => ∑ i, M a i * v i)) := by
    funext v
    apply Prod.ext
    · exact DPhiC_fst c h ι (toC x) v
    · funext a
      rw [DPhiC_snd]
  rw [hfun]
  exact hblock

end

end Work.WilE3.Frame
