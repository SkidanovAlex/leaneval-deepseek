import Mathlib
import Submission.Work.BW.BWGradedBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The colon/sup dimension identity for the multigraded Hilbert function

With `R = MR N = ℂ[X_{i,j}]` graded by `wZ N` (both variables of the `i`-th factor having
weight the basis vector `e_i`), `J` a multihomogeneous ideal and `x` homogeneous of
`ℕ`-multidegree `d`, multiplication by `x` fits into the exact sequence of graded vector spaces

`(R/J : x)(-d) --x--> R/J --> R/(J + (x)) --> 0`.

Taking dimensions in degree `u` gives

`hilbIdeal N J u = hilbIdeal N (colonSpan J x) (u - castF d) + hilbIdeal N (J ⊔ (x)) u`.

The crucial graded input is that every element of `(R/J)_u` lying in `(J + (x))/J` is the image
of multiplication by `x` on `(R/J)_{u - d}` (`exists_sub_mul_mem_of_mem`, a consequence of the
multiplicativity of the weighted homogeneous components `comp_mul_of_mem`).
-/

set_option linter.style.haveILetI false

namespace Work.BW

open MvPolynomial

variable {N : ℕ}

/-- Multiplication by an element homogeneous of `ℕ`-multidegree `d` maps the `ℤ`-graded piece
`u - castF d` into the piece `u`. -/
theorem mul_mem_pieceZ {d : Fin (N + 1) →₀ ℕ} {x : MR N}
    (hx : x ∈ homPiece N d) (u : Fin (N + 1) →₀ ℤ) {p : MR N}
    (hp : p ∈ pieceZ N (u - castF d)) : x * p ∈ pieceZ N u := by
  have hxZ : x ∈ pieceZ N (castF d) := by rwa [homPiece_eq_pieceZ] at hx
  have h1 : x * p ∈ pieceZ N (castF d) * pieceZ N (u - castF d) :=
    Submodule.mul_mem_mul hxZ hp
  have h2 := pieceZ_mul (N := N) (castF d) (u - castF d) h1
  rwa [add_sub_cancel] at h2

/-- **Key step.**  If `y` lies in the graded piece of degree `u` and in `J ⊔ (x)`, then `y` is
congruent modulo `J` to `x * p` for some `p` in the graded piece of degree `u - deg x`. -/
theorem exists_sub_mul_mem_of_mem (J : Ideal (MR N)) (hJ : MultiHomZ N J)
    (d : Fin (N + 1) →₀ ℕ) {x : MR N} (hx : x ∈ homPiece N d) (u : Fin (N + 1) →₀ ℤ)
    {y : MR N} (hyA : y ∈ pieceZ N u) (hyJ : y ∈ J ⊔ Ideal.span {x}) :
    ∃ p : MR N, p ∈ pieceZ N (u - castF d) ∧ y - x * p ∈ J := by
  have hxZ : x ∈ pieceZ N (castF d) := by rwa [homPiece_eq_pieceZ] at hx
  obtain ⟨i, hi, s, hs, his⟩ := Submodule.mem_sup.mp hyJ
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hs
  refine ⟨MvPolynomial.weightedHomogeneousComponent (wZ N) (u - castF d) r,
    MvPolynomial.weightedHomogeneousComponent_mem (wZ N) r _, ?_⟩
  have hy : y = i + x * r := his.symm
  have hcomp := comp_mul_of_mem hxZ r u
  have hπy : MvPolynomial.weightedHomogeneousComponent (wZ N) u y = y :=
    MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same hyA
  have hy' : y = MvPolynomial.weightedHomogeneousComponent (wZ N) u i +
      x * MvPolynomial.weightedHomogeneousComponent (wZ N) (u - castF d) r := by
    rw [hπy.symm, hy, map_add, hcomp]
  have hsub : y - x * MvPolynomial.weightedHomogeneousComponent (wZ N) (u - castF d) r =
      MvPolynomial.weightedHomogeneousComponent (wZ N) u i := by
    rw [hy']; abel
  rw [hsub]
  exact hJ i hi u

theorem hilbIdeal_colon_add {N : ℕ} (J : Ideal (MR N)) (hJ : MultiHomZ N J)
    (d : Fin (N + 1) →₀ ℕ) (x : MR N) (hx : x ∈ homPiece N d) (u : Fin (N + 1) →₀ ℤ) :
    hilbIdeal N J u = hilbIdeal N (colonSpan J x) (u - castF d)
      + hilbIdeal N (J ⊔ Ideal.span {x}) u := by
  classical
  have hxZ : x ∈ pieceZ N (castF d) := by rwa [homPiece_eq_pieceZ] at hx
  haveI : Module.Finite ℂ ↥(pieceZ N u) := finite_pieceZ u
  simp only [hilbIdeal]
  set A : Submodule ℂ (MR N) := pieceZ N u with hA
  set B : Submodule ℂ (MR N) := pieceZ N (u - castF d) with hB
  set P : Submodule ℂ ↥A := Submodule.comap A.subtype (J.restrictScalars ℂ) with hP
  set Q : Submodule ℂ ↥A :=
    Submodule.comap A.subtype ((J ⊔ Ideal.span {x}).restrictScalars ℂ) with hQ
  set P' : Submodule ℂ ↥B :=
    Submodule.comap B.subtype ((colonSpan J x).restrictScalars ℂ) with hP'
  have hle : P ≤ Q := by
    intro z hz
    rw [hP, Submodule.mem_comap, Submodule.restrictScalars_mem] at hz
    rw [hQ, Submodule.mem_comap, Submodule.restrictScalars_mem]
    exact Submodule.mem_sup_left hz
  have hmul : ∀ b : ↥B, (x * (b : MR N)) ∈ A := by
    intro b
    rw [hA]
    exact mul_mem_pieceZ hx u b.2
  let mulX : ↥B →ₗ[ℂ] ↥A :=
    LinearMap.codRestrict A ((LinearMap.mulLeft ℂ x).comp B.subtype) hmul
  have hmulX_apply : ∀ b : ↥B, ((mulX b : ↥A) : MR N) = x * (b : MR N) := fun b => rfl
  set ψ : ↥B →ₗ[ℂ] (↥A ⧸ P) := P.mkQ.comp mulX with hψ
  -- the kernel of `ψ` is `(J : x) ∩ B`
  have hker : ψ.ker = P' := by
    rw [hψ, hP', hP]
    ext b
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.restrictScalars_mem, hmulX_apply]
    rw [mem_colonSpan]
    constructor
    · intro h; rwa [mul_comm] at h
    · intro h; rwa [mul_comm]
  -- the range of `ψ` is `((J + (x)) ∩ A) / (J ∩ A)`
  have hrange : ψ.range = Submodule.map P.mkQ Q := by
    rw [hψ, LinearMap.range_comp]
    refine le_antisymm ?_ ?_
    · apply Submodule.map_mono
      intro z hz
      rw [LinearMap.mem_range] at hz
      obtain ⟨b, rfl⟩ := hz
      rw [hQ, Submodule.mem_comap, Submodule.restrictScalars_mem]
      simp only [Submodule.subtype_apply]
      rw [hmulX_apply]
      exact Submodule.mem_sup_right (Ideal.mem_span_singleton.mpr ⟨b, rfl⟩)
    · intro z hz
      obtain ⟨y, hyQ, hyz⟩ := Submodule.mem_map.mp hz
      rw [← hyz]
      have hyJ : (y : MR N) ∈ J ⊔ Ideal.span {x} := by
        rw [hQ, Submodule.mem_comap, Submodule.restrictScalars_mem] at hyQ
        exact hyQ
      have hyA : (y : MR N) ∈ pieceZ N u := by rw [← hA]; exact y.2
      obtain ⟨p, hpA, hpJ⟩ := exists_sub_mul_mem_of_mem J hJ d hx u hyA hyJ
      have hpB : p ∈ B := by rw [hB]; exact hpA
      refine Submodule.mem_map.mpr ⟨mulX (⟨p, hpB⟩ : ↥B),
        LinearMap.mem_range.mpr ⟨(⟨p, hpB⟩ : ↥B), rfl⟩, ?_⟩
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hP,
        Submodule.mem_comap, Submodule.restrictScalars_mem, Submodule.subtype_apply]
      have h' : x * p - y ∈ J := by
        have := neg_mem hpJ
        rwa [neg_sub] at this
      simpa [hmulX_apply] using h'
  have key1 : Module.finrank ℂ (↥A ⧸ P) =
      Module.finrank ℂ (↥A ⧸ Q) + Module.finrank ℂ (Submodule.map P.mkQ Q) := by
    rw [← Submodule.finrank_quotient_add_finrank (Q.map P.mkQ),
      LinearEquiv.finrank_eq (Submodule.quotientQuotientEquivQuotient P Q hle)]
  have key2 : Module.finrank ℂ (Submodule.map P.mkQ Q) =
      Module.finrank ℂ (↥B ⧸ P') := by
    rw [← hrange, ← hker]
    exact (LinearEquiv.finrank_eq ψ.quotKerEquivRange).symm
  rw [key1, key2]
  exact add_comm _ _

end Work.BW
