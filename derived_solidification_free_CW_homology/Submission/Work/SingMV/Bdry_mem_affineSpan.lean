import Mathlib
import Submission.Work.SINGMV.Defs
import Submission.Work.SingMV.SdAux
import Submission.Work.SingMV.sddeg_aux

/-!
# `Bdry n` is an integral combination of affine simplices

`Bdry n = Σᵢ (-1)ⁱ (δᵢ)∗ (Sd n)` is the subdivision of the boundary of `Δⁿ⁺¹`, as a chain in
`C_n(Δⁿ⁺¹)`.  This file proves that it lies in `affineSpan (n+1) n`, the submodule generated
by the *affine* `n`-simplices of `Δⁿ⁺¹`.

The proof rests on two facts about `affineSpan` which are already available in the library:

* the barycentric subdivision `Sd n` of the fundamental `n`-simplex is an integral combination
  of affine `n`-simplices of `Δⁿ`, i.e. `Sd n ∈ affineSpan n n` (`Sd_mem_affineSpan` below).
  Since `Sd (n+1)` is a scalar multiple of the cone over the chain `SdBdry n (Sd n)`, and the
  cone (like the pushforward along any map) sends *every* chain of `Δᵏ` to a combination of
  affine `(k+1)`-simplices, this is an induction on `n`; the cone input at the inductive step is
  `Bdry n ∈ affineSpan (n+1) n`, which is exactly the statement being assembled.
* the pushforward along a coface `δᵢ : Δⁿ ⟶ Δⁿ⁺¹` preserves `affineSpan`
  (`coface_mem_affineSpan`), and `affineSpan` is a submodule, so the alternating sum of the
  pushforwards of `Sd n` lies in `affineSpan (n+1) n`.

The two implications are mutually recursive: `Bdry n` is a sum of pushforwards of `Sd n`, and
`Sd (n+1)` is a cone over `Bdry n`.  We therefore split the argument into the two lemmas
`Bdry_mem_affineSpan_of` and `Sd_mem_affineSpan` and run the induction on `n`.
-/

open CategoryTheory Limits
open scoped BigOperators Simplicial

noncomputable section

namespace Work.SingMV

/-- Bridging lemma for the two `ℤ`-actions on a `ℤ`-module: on an abelian group the scalar
multiplication coming from the `ℤ`-module structure and the one coming from `ZSMul` differ only
by a proof (`Int.cast_smul_eq_zsmul`), so `ZSMul`-multiples of elements of a submodule again
lie in it. -/
lemma smul_mem_int {M : Type*} [AddCommGroup M] [Module ℤ M] {S : Submodule ℤ M} {x : M}
    (hx : x ∈ S) (c : ℤ) : c • x ∈ S := by
  rw [← int_smul_eq_zsmul (inferInstance : Module ℤ M) c x]
  exact Submodule.smul_mem S c hx

/-- The subdivision of the boundary of `Δⁿ⁺¹` is a combination of affine `n`-simplices of
`Δⁿ⁺¹`, as soon as the subdivision `Sd n` of `Δⁿ` is a combination of affine `n`-simplices
of `Δⁿ`.  Indeed `Bdry n = SdBdry n (Sd n)` is the alternating sum of the pushforwards of
`Sd n` along the coface inclusions, and each of those preserves `affineSpan`. -/
lemma Bdry_mem_affineSpan_of (n : ℕ) (h : Sd n ∈ affineSpan n n) :
    Bdry n ∈ affineSpan (n+1) n := by
  show (phi n).f n (Sd n) ∈ affineSpan (n+1) n
  rw [(SdBdry_eq_phi n (Sd n)).symm]
  rw [show SdBdry n (Sd n) = ∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) •
      (((Submission.Blueprint.singC).map (coface n i)).f n (Sd n)) from rfl]
  refine (affineSpan (n+1) n).sum_mem (fun i _ => ?_)
  exact smul_mem_int (coface_mem_affineSpan n n i h) ((-1 : ℤ) ^ (i : ℕ))

/-- `Sd 0` is the generator of the identity simplex of `Δ⁰`, an affine `0`-simplex. -/
lemma Sd_zero_mem_affineSpan : Sd 0 ∈ affineSpan 0 0 := by
  rw [show Sd 0 = gen (tSplx 0) 0 (ContinuousMap.id _) from rfl]
  rw [← affineSimplex_eq_id 0]
  exact gen_affineSimplex_mem 0 0 _

/-- **The barycentric subdivision of the fundamental simplex is a combination of affine
simplices.**  Since `Sd (n+1)` is a scalar multiple of the cone over `SdBdry n (Sd n)`
with the barycenter as apex, and the cone maps *every* chain of `Δᵏ` into the span of the
affine `(k+1)`-simplices, this follows by induction from `Bdry_mem_affineSpan_of`. -/
lemma Sd_mem_affineSpan (n : ℕ) : Sd n ∈ affineSpan n n := by
  induction n with
  | zero => exact Sd_zero_mem_affineSpan
  | succ n ih =>
      rw [show Sd (n+1) = (-1 : ℤ) ^ (n+1) • coneChain (n+1)
          (unif (Finset.univ : Finset (Fin (n+2))) Finset.univ_nonempty) n
          (SdBdry n (Sd n)) from rfl]
      rw [show SdBdry n (Sd n) = Bdry n from SdBdry_eq_phi n (Sd n)]
      exact smul_mem_int
        (coneChain_mem_affineSpan (n+1) n _ (Bdry_mem_affineSpan_of n ih)) _

/-- **The subdivision of the boundary of `Δⁿ⁺¹` is a combination of affine `n`-simplices of
`Δⁿ⁺¹`.** -/
theorem Bdry_mem_affineSpan (n : ℕ) :
    Work.SingMV.Bdry n ∈ Work.SingMV.affineSpan (n+1) n := by
  exact Bdry_mem_affineSpan_of n (Sd_mem_affineSpan n)

end Work.SingMV
