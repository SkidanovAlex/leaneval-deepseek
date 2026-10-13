import Mathlib
import Submission.Work.DSG4a.Present
import Submission.Work.DSG4a.one_mem_splitIdeal_map_present
import Submission.Work.DSG4a.LocalGlobal

namespace Work.DSG4a

universe u

/-- **Local-to-global for unimodularity of a presented class, in the form needed by the
derived direct summand argument.**

Let `D : Fin m → Fin n → A` present the module `A^m ⧸ im D` and let `e : Fin m → A` be a
lift of an element of it.  Suppose that for every maximal ideal `𝔪` there is a flat local
`A`-algebra `ψ : A → A'` lying over `𝔪` (i.e. `(maximalIdeal A').comap ψ = 𝔪`) such that
the base changed class `presentMk D' e'` is unimodular over `A'`.  Then the original class
`presentMk D e` was already unimodular over `A`.

The proof is the two-step local-to-global argument of subproject DSG4a:

1. `one_mem_splitIdeal_map_present` (flat base change of the splitting ideal) turns
   unimodularity over the flat `A'` into `1 ∈ (splitIdeal A (presentMk D e)).map ψ`;
2. `one_mem_ideal_of_forall_maximal` promotes this to `1 ∈ splitIdeal A (presentMk D e)`
   using only flatness and lying over at every maximal ideal,
and `one_mem_splitIdeal_iff` converts the latter back into `Module.IsUnimodular`. -/
theorem isUnimodular_presentMk_of_forall_maximal {A : Type u} [CommRing A] {m n : ℕ}
    (D : Fin m → Fin n → A) (e : Fin m → A)
    (h : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → ∃ (A' : Type u) (_ : CommRing A') (_ : IsLocalRing A')
      (ψ : A →+* A'), ψ.Flat ∧ (IsLocalRing.maximalIdeal A').comap ψ = 𝔪 ∧
      (letI : Algebra A A' := ψ.toAlgebra
       Module.IsUnimodular A' (Work.DSG4a.presentMk (fun i j => algebraMap A A' (D i j))
         (fun i => algebraMap A A' (e i))))) :
    Module.IsUnimodular A (Work.DSG4a.presentMk D e) := by
  rw [← one_mem_splitIdeal_iff]
  refine one_mem_ideal_of_forall_maximal (splitIdeal A (presentMk D e)) ?_
  intro 𝔪 h𝔪
  obtain ⟨A', hA'c, hA'l, ψ, hψflat, hcomap, hunimod⟩ := h 𝔪 h𝔪
  refine ⟨A', hA'c, hA'l, ψ, hψflat, hcomap, ?_⟩
  let _ : Algebra A A' := ψ.toAlgebra
  have hflat : Module.Flat A A' := hψflat
  have hu : Module.IsUnimodular A' (presentMk (fun i j => algebraMap A A' (D i j))
      (fun i => algebraMap A A' (e i))) := hunimod
  have key := one_mem_splitIdeal_map_present D e hflat hu
  rw [RingHom.algebraMap_toAlgebra ψ] at key
  exact key

end Work.DSG4a
