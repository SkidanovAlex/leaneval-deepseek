import Mathlib
import Submission.Grassmann.Restriction
import Submission.Grassmann.HybridLaplacian
import Submission.Grassmann.RestrictionFourier
import Submission.Commons.LinearAlgebra.finrank_comap_eq

/-!
# The algebra of restrictions and shifts (composition lemmas)

Prerequisites for composing derivatives `D_{V₁,W₁,T}` in `L(V,W)` (arXiv:2209.04243, §7,
`prop:increasing order derivatives`): the composition of two restrictions is a restriction, a
shift of a restriction is the restriction of a shift, and two shifts compose.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-- **Composition of restrictions**: restricting twice is restricting by the composite pair. -/
lemma restr_restr {m n m₁ n₁ m₂ n₂ : ℕ}
    (Q₁ : Matrix (Fin n₁) (Fin n) 𝔽₂) (ι₁ : Matrix (Fin m) (Fin m₁) 𝔽₂)
    (Q₂ : Matrix (Fin n₂) (Fin n₁) 𝔽₂) (ι₂ : Matrix (Fin m₁) (Fin m₂) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    restr Q₂ ι₂ (restr Q₁ ι₁ f) = restr (Q₂ * Q₁) (ι₁ * ι₂) f := by
  funext A
  simp only [restr]
  congr 1
  rw [Matrix.mul_assoc ι₁ ι₂ A, Matrix.mul_assoc ι₁ (ι₂ * A) (Q₂ * Q₁),
    Matrix.mul_assoc ι₁ ((ι₂ * A) * Q₂) Q₁, Matrix.mul_assoc (ι₂ * A) Q₂ Q₁]

/-- **Composition of shifts**: `shift T₂ (shift T₁ f) = shift (T₁ + T₂) f`. -/
lemma shift_shift {m n : ℕ} (T₁ T₂ : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    shift T₂ (shift T₁ f) = shift (T₁ + T₂) f := by
  funext A
  simp only [shift]
  rw [add_assoc, add_comm T₂ T₁, ← add_assoc]

/-- **A shift of a restriction is the restriction of a shift.** -/
lemma shift_restr {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (T : Matrix (Fin m') (Fin n') 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    shift T (restr Q ι f) = restr Q ι (shift (ι * T * Q) f) := by
  funext A
  simp only [restr, shift]
  rw [Matrix.mul_add, Matrix.add_mul]

/-! ## The order-one hybrid predicate composes -/

/-- With `W₁ = W` (i.e. `ι = 1`) the hybrid predicate is just `ker Q ⊆ range X`. -/
lemma hybridPred_one_iff {m n n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    hybridPred Q (1 : Matrix (Fin m) (Fin m) 𝔽₂) X ↔
      LinearMap.ker Q.mulVecLin ≤ LinearMap.range X.mulVecLin := by
  have htop : LinearMap.range (1 : Matrix (Fin m) (Fin m) 𝔽₂).mulVecLin = ⊤ := by
    rw [Matrix.mulVecLin_one, LinearMap.range_id]
  simp only [hybridPred]
  rw [htop]
  exact ⟨fun h => h.1, fun h => ⟨h, fun w _ => Submodule.mem_top⟩⟩

/-- **Composition of the order-one predicates**: for a surjective `Q₁`,
`ker (Q₂ Q₁) ⊆ range X` iff `ker Q₁ ⊆ range X` and `ker Q₂ ⊆ range (Q₁ X)`. -/
lemma ker_mul_le_range_iff {m n n₁ n₂ : ℕ} (Q₁ : Matrix (Fin n₁) (Fin n) 𝔽₂)
    (Q₂ : Matrix (Fin n₂) (Fin n₁) 𝔽₂) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (hQ₁ : LinearMap.range Q₁.mulVecLin = ⊤) :
    LinearMap.ker (Q₂ * Q₁).mulVecLin ≤ LinearMap.range X.mulVecLin ↔
      LinearMap.ker Q₁.mulVecLin ≤ LinearMap.range X.mulVecLin ∧
        LinearMap.ker Q₂.mulVecLin ≤ LinearMap.range (Q₁ * X).mulVecLin := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro v hv
      exact h (by rw [Matrix.mulVecLin_mul, LinearMap.mem_ker, LinearMap.comp_apply, hv, map_zero])
    · rw [Matrix.mulVecLin_mul, LinearMap.range_comp]
      intro u hu
      rw [Submodule.mem_map]
      have hu' : u ∈ (⊤ : Submodule 𝔽₂ (Fin n₁ → 𝔽₂)) := Submodule.mem_top
      rw [← hQ₁] at hu'
      obtain ⟨v, hv⟩ := hu'
      refine ⟨v, h (by rw [Matrix.mulVecLin_mul, LinearMap.mem_ker, LinearMap.comp_apply, hv, hu]), hv⟩
  · rintro ⟨h₁, h₂⟩ v hv
    rw [Matrix.mulVecLin_mul, LinearMap.mem_ker, LinearMap.comp_apply] at hv
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp] at h₂
    obtain ⟨u, hu, huv⟩ := h₂ hv
    have hvu : v - u ∈ LinearMap.ker Q₁.mulVecLin := by
      rw [LinearMap.mem_ker, map_sub, huv, sub_self]
    rw [show v = (v - u) + u by abel]
    exact Submodule.add_mem _ (h₁ hvu) hu

/-- **The order-one hybrid predicates compose** (the Fourier-multiplier version of
`D_{V₁,W₁,T} = D_{V₁/U,W₁} ∘ D_{U,W,T}`). -/
lemma hybridPred_mul_self {m n n₁ n₂ : ℕ} (Q₁ : Matrix (Fin n₁) (Fin n) 𝔽₂)
    (Q₂ : Matrix (Fin n₂) (Fin n₁) 𝔽₂) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (hQ₁ : LinearMap.range Q₁.mulVecLin = ⊤) :
    hybridPred (Q₂ * Q₁) (1 : Matrix (Fin m) (Fin m) 𝔽₂) X ↔
      hybridPred Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂) X ∧
        hybridPred Q₂ (1 : Matrix (Fin m) (Fin m) 𝔽₂) (Q₁ * X) := by
  rw [hybridPred_one_iff, hybridPred_one_iff, hybridPred_one_iff]
  exact ker_mul_le_range_iff Q₁ Q₂ X hQ₁

/-- **Additivity of the order under composition.** -/
lemma hybridOrder_mul_self {m n n₁ n₂ : ℕ} (Q₁ : Matrix (Fin n₁) (Fin n) 𝔽₂)
    (Q₂ : Matrix (Fin n₂) (Fin n₁) 𝔽₂)
    (hQ₁ : LinearMap.range Q₁.mulVecLin = ⊤) :
    hybridOrder (Q₂ * Q₁) (1 : Matrix (Fin m) (Fin m) 𝔽₂) =
      hybridOrder Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂) +
        hybridOrder Q₂ (1 : Matrix (Fin m) (Fin m) 𝔽₂) := by
  have htop : LinearMap.range (1 : Matrix (Fin m) (Fin m) 𝔽₂).mulVecLin = ⊤ := by
    rw [Matrix.mulVecLin_one, LinearMap.range_id]
  have hker : LinearMap.ker (Q₂ * Q₁).mulVecLin =
      Submodule.comap Q₁.mulVecLin (LinearMap.ker Q₂.mulVecLin) := by
    rw [Matrix.mulVecLin_mul, LinearMap.ker_comp]
  have hfr : Module.finrank 𝔽₂ ↥(LinearMap.ker (Q₂ * Q₁).mulVecLin) =
      Module.finrank 𝔽₂ ↥(LinearMap.ker Q₁.mulVecLin) +
        Module.finrank 𝔽₂ ↥(LinearMap.ker Q₂.mulVecLin) := by
    rw [hker, Commons.LinearAlgebra.finrank_comap_eq Q₁.mulVecLin (LinearMap.ker Q₂.mulVecLin)]
    have : LinearMap.ker Q₂.mulVecLin ⊓ LinearMap.range Q₁.mulVecLin =
        LinearMap.ker Q₂.mulVecLin := by
      rw [hQ₁, inf_top_eq]
    rw [this]
  have hfin1 : Module.finrank 𝔽₂ ↥(LinearMap.range (1 : Matrix (Fin m) (Fin m) 𝔽₂).mulVecLin) = m := by
    rw [htop, finrank_top, Module.finrank_pi]
    simp
  rw [hybridOrder, hybridOrder, hybridOrder, hfin1, hfr]
  omega

/-- **The general order-one composition of hybrid predicates**: for a surjective `Q₁` and any
`ι₂`, the hybrid predicate of `Q₂ * Q₁` factors through `Q₁`.  (The `ker ⊆ range` part is
`ker_mul_le_range_iff`; the "`∀ w`" part is literally the same condition on both sides.) -/
lemma hybridPred_mul {m n n₁ n₂ m₂ : ℕ} (Q₁ : Matrix (Fin n₁) (Fin n) 𝔽₂)
    (Q₂ : Matrix (Fin n₂) (Fin n₁) 𝔽₂) (ι₂ : Matrix (Fin m) (Fin m₂) 𝔽₂)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) (hQ₁ : LinearMap.range Q₁.mulVecLin = ⊤) :
    hybridPred (Q₂ * Q₁) ι₂ X ↔
      hybridPred Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂) X ∧ hybridPred Q₂ ι₂ (Q₁ * X) := by
  have htop : LinearMap.range (1 : Matrix (Fin m) (Fin m) 𝔽₂).mulVecLin = ⊤ := by
    rw [Matrix.mulVecLin_one, LinearMap.range_id]
  have hsame : ∀ w : Fin m → 𝔽₂,
      (X.mulVec w ∈ LinearMap.ker (Q₂ * Q₁).mulVecLin) ↔
        ((Q₁ * X).mulVec w ∈ LinearMap.ker Q₂.mulVecLin) := by
    intro w
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_mul, LinearMap.comp_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  simp only [hybridPred]
  rw [htop]
  constructor
  · intro h
    obtain ⟨hA, hB⟩ := (ker_mul_le_range_iff Q₁ Q₂ X hQ₁).mp h.1
    exact ⟨⟨hA, fun w _ => Submodule.mem_top⟩, hB,
      fun w hw => h.2 w ((hsame w).mpr hw)⟩
  · rintro ⟨⟨h₁, _⟩, h₂, h₃⟩
    exact ⟨(ker_mul_le_range_iff Q₁ Q₂ X hQ₁).mpr ⟨h₁, h₂⟩,
      fun w hw => h₃ w ((hsame w).mp hw)⟩

/-- **The Fourier-multiplier composition of the order-one derivatives** (the identity behind
`D_{V₁,W₁,T} = D_{V₁/U,W₁} ∘ D_{U,W,T}`): restricting and shifting commutes with the
factorisation of the hybrid Laplacian `L_{V₁,W₁} = L_{V₁/U,W₁} ∘ L_{U,W}`.  Note that the shift
`T` stays in the *big* space on both sides. -/
theorem restr_shift_lapMulN_mul {m n n₁ n₂ m₂ : ℕ}
    (Q₁ : Matrix (Fin n₁) (Fin n) 𝔽₂) (Q₂ : Matrix (Fin n₂) (Fin n₁) 𝔽₂)
    (ι₂ : Matrix (Fin m) (Fin m₂) 𝔽₂) (hQ₁ : LinearMap.range Q₁.mulVecLin = ⊤)
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    restr Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂)
        (shift T (lapMulN (hybridPred (Q₂ * Q₁) ι₂) g)) =
      lapMulN (hybridPred Q₂ ι₂)
        (restr Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂)
          (shift T (lapMulN (hybridPred Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂)) g))) := by
  classical
  refine eq_of_fcoeff_eq fun Y => ?_
  have hL : fcoeff (restr Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂)
        (shift T (lapMulN (hybridPred (Q₂ * Q₁) ι₂) g))) Y =
      ∑ X ∈ Finset.univ.filter (fun X : Matrix (Fin n) (Fin m) 𝔽₂ => Q₁ * X * (1 : Matrix (Fin m) (Fin m) 𝔽₂) = Y),
        (if hybridPred (Q₂ * Q₁) ι₂ X then 1 else 0) * fcoeff g X * mchar X T := by
    rw [fcoeff_restr_shift]
    exact Finset.sum_congr rfl fun X _ => by rw [fcoeff_lapMulN]
  have hR : fcoeff (lapMulN (hybridPred Q₂ ι₂)
        (restr Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂)
          (shift T (lapMulN (hybridPred Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂)) g)))) Y =
      (if hybridPred Q₂ ι₂ Y then 1 else 0) *
        ∑ X ∈ Finset.univ.filter (fun X : Matrix (Fin n) (Fin m) 𝔽₂ => Q₁ * X * (1 : Matrix (Fin m) (Fin m) 𝔽₂) = Y),
          (if hybridPred Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂) X then 1 else 0) *
            fcoeff g X * mchar X T := by
    rw [fcoeff_lapMulN, fcoeff_restr_shift]
    congr 1
    exact Finset.sum_congr rfl fun X _ => by rw [fcoeff_lapMulN]
  rw [hL, hR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun X hX => ?_
  rw [Finset.mem_filter] at hX
  have hX' : Q₁ * X = Y := by rw [← hX.2, Matrix.mul_one]
  by_cases hP : hybridPred (Q₂ * Q₁) ι₂ X
  · have hPQ := (hybridPred_mul Q₁ Q₂ ι₂ X hQ₁).mp hP
    rw [if_pos hP, if_pos hPQ.1, if_pos (by rw [← hX']; exact hPQ.2)]
    ring
  · rw [if_neg hP]
    have hnot : ¬ (hybridPred Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂) X ∧
        hybridPred Q₂ ι₂ (Q₁ * X)) := fun hh => hP ((hybridPred_mul Q₁ Q₂ ι₂ X hQ₁).mpr hh)
    by_cases h1 : hybridPred Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂) X
    · have h2 : ¬ hybridPred Q₂ ι₂ Y := by
        rw [← hX']
        exact fun hh => hnot ⟨h1, hh⟩
      rw [if_pos h1, if_neg h2]
      ring
    · rw [if_neg h1]
      ring

end

end Submission.Grassmann
