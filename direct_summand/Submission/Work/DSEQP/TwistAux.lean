import Mathlib
import Submission.Work.DSMap.Gaps
import Submission.Work.DSEQP.TwistDefs

/-!
# `modSplit_twist` — the two auxiliary steps

* `twistLevel_large`: the (finitely generated) image of an `A`-linear map into the perfection `W`
  lies in a single level `W_N = ψW(B)^{1/p^N}`.
* `twistBeta_exists`: the level-`N` transfer map `W_N → S`, `ψW(b)^{1/p^N} ↦ ψS(φ b)^{1/p^N}`.
-/

open CategoryTheory
open scoped TensorProduct

namespace Work.DSEQP

universe a

/-- The image of a finitely generated module under an `A`-linear map into `W = ⋃_n W_n` lies in a
single level `W_N`, for some `N ≥ k`. -/
theorem twistLevel_large {A B W : Type a} [CommRing A] [CommRing B] [Algebra A B] [CommRing W]
    [Algebra A W] (p : ℕ) [Fact p.Prime] [CharP W p] [PerfectRing W p] (ψW : B →+* W)
    (hAW : algebraMap A W = ψW.comp (algebraMap A B))
    (hW : ∀ w : W, ∃ (n : ℕ) (x : B), w = ((frobeniusEquiv W p).symm^[n]) (ψW x))
    (M : Type a) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (t : M →ₗ[A] W) (k : ℕ) :
    ∃ N : ℕ, k ≤ N ∧ ∀ x : M, t x ∈ twistLevel p ψW hAW N := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  have hg : ∀ i : Fin n, ∃ N : ℕ, t (s i) ∈ twistLevel p ψW hAW N := by
    intro i
    obtain ⟨m, x, hx⟩ := hW (t (s i))
    exact ⟨m, by rw [hx]; exact ⟨x, iterateFrobeniusEquiv_symm_pow p m (ψW x)⟩⟩
  choose nf hnf using hg
  refine ⟨max k (Finset.univ.sup nf), le_max_left _ _, ?_⟩
  intro x
  have hle : Submodule.span A (Set.range s) ≤
      (twistLevel p ψW hAW (max k (Finset.univ.sup nf))).comap t := by
    rw [Submodule.span_le]
    rintro y ⟨i, rfl⟩
    exact twistLevel_mono p ψW hAW
      (le_trans (Finset.le_sup (Finset.mem_univ i)) (le_max_right _ _)) (hnf i)
  exact hle (by rw [hs]; trivial)

/-- **The transfer map.**  On the level `W_N = ψW(B)^{1/p^N}`, the assignment
`ψW(b)^{1/p^N} ↦ ψS(φ b)^{1/p^N}` (well defined because `ψW` is injective, and where the root is
taken in the perfect ring `S`) is `A`-linear. -/
theorem twistBeta_exists {A B W S : Type a} [CommRing A] [CommRing B] [Algebra A B] [CommRing W]
    [Algebra A W] [CommRing S] [Algebra A S] (p : ℕ) [Fact p.Prime] [CharP W p] [CharP S p]
    [PerfectRing S p] (ψW : B →+* W) (hAW : algebraMap A W = ψW.comp (algebraMap A B))
    (hψW : Function.Injective ψW) (ψS : A →+* S) (hAS : algebraMap A S = ψS)
    (φ : B →ₗ[A] A) (N : ℕ) :
    ∃ β : twistLevel p ψW hAW N →ₗ[A] S,
      ∀ (w : twistLevel p ψW hAW N) (b : B), (w : W) ^ (p ^ N) = ψW b →
        β w = (iterateFrobeniusEquiv S p N).symm (ψS (φ b)) := by
  classical
  let bOf : twistLevel p ψW hAW N → B := fun w => Classical.choose w.2
  have bOf_spec : ∀ w : twistLevel p ψW hAW N, (w : W) ^ (p ^ N) = ψW (bOf w) :=
    fun w => Classical.choose_spec w.2
  have bOf_eq : ∀ (w : twistLevel p ψW hAW N) (b : B),
      (w : W) ^ (p ^ N) = ψW b → bOf w = b :=
    fun w b hb => hψW ((bOf_spec w).symm.trans hb)
  refine ⟨{ toFun := fun w => (iterateFrobeniusEquiv S p N).symm (ψS (φ (bOf w)))
            map_add' := ?_
            map_smul' := ?_ }, ?_⟩
  · intro w w'
    have hb : bOf (w + w') = bOf w + bOf w' := by
      apply bOf_eq
      rw [Submodule.coe_add, add_pow_char_pow, bOf_spec w, bOf_spec w', ← map_add]
    simp only [hb, map_add]
  · intro a w
    have hb : bOf (a • w) = (algebraMap A B a) ^ (p ^ N) * bOf w := by
      apply bOf_eq
      rw [Submodule.coe_smul, Algebra.smul_def, mul_pow, bOf_spec w]
      rw [show algebraMap A W a = ψW (algebraMap A B a) from by rw [hAW]; rfl]
      rw [map_mul, map_pow]
    rw [hb, ← map_pow (algebraMap A B) a (p ^ N), apply_algebraMap_mul φ (a ^ (p ^ N)) (bOf w),
      map_mul ψS, map_pow ψS, map_mul (iterateFrobeniusEquiv S p N).symm,
      iterateFrobeniusEquiv_symm_apply_pow, Algebra.smul_def, hAS]
    simp
  · intro w b hb
    show (iterateFrobeniusEquiv S p N).symm (ψS (φ (bOf w))) =
      (iterateFrobeniusEquiv S p N).symm (ψS (φ b))
    rw [bOf_eq w b hb]

end Work.DSEQP
