import Mathlib
import Submission.Work.WilE8.Basic

namespace Work.WilE8.StarR

open WilkiesDesign WilkiesDesign.E

/-- `StarR`-sets are preimages under `psiV` of `Star`-sets.  Pulling an intersection of
`StarR`-sets back to an intersection of `Star`-sets only produces `Zᵢ`'s: the `⋂ᵢ Zᵢ` we obtain
does not know that it lives in the cube, but `psiV` always lands in `cubeC n`, so
`psiV ⁻¹' (cubeC n ∩ ⋂ᵢ Zᵢ) = ⋂ᵢ psiV ⁻¹' Zᵢ`. -/
lemma psiV_preimage_inter {n k : ℕ} {X : Fin k → Set (Fin n → ℝ)} {Z : Fin k → Set (Fin n → ℝ)}
    (hX : ∀ i, X i = psiV ⁻¹' Z i) :
    (⋂ i, X i) = psiV ⁻¹' (cubeC n ∩ ⋂ i, Z i) := by
  ext x
  constructor
  · intro hx
    refine ⟨psiV_mem_cube x, ?_⟩
    refine Set.mem_iInter.mpr fun i => ?_
    have h : x ∈ X i := Set.mem_iInter.mp hx i
    rwa [hX i] at h
  · intro hx
    refine Set.mem_iInter.mpr fun i => ?_
    have h : psiV x ∈ Z i := Set.mem_iInter.mp hx.2 i
    rw [hX i]
    exact h

theorem inter
    (hE7 : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), ∀ (k : ℕ) (D : Fin k → ℕ)
      (Y : Fin k → Set (Fin n → ℝ)), (∀ i, WilkiesDesign.E.Star F (D i) n (Y i)) →
      WilkiesDesign.E.Star a (p.eval (∑ i, D i)) n (WilkiesDesign.E.cubeC n ∩ ⋂ i, Y i))
    (a0 n : ℕ) :
    ∃ (a : ℕ) (p : Polynomial ℕ), ∀ (k : ℕ) (D : Fin k → ℕ) (X : Fin k → Set (Fin n → ℝ)),
      (∀ i, WilkiesDesign.E.StarR a0 (D i) n (X i)) →
      WilkiesDesign.E.StarR a (p.eval (∑ i, D i)) n (⋂ i, X i) := by
  classical
  obtain ⟨a, p, h⟩ := hE7 a0 n
  refine ⟨a, p, ?_⟩
  intro k D X hX
  choose Z hZ hXeq using hX
  refine ⟨WilkiesDesign.E.cubeC n ∩ ⋂ i, Z i, h k D Z hZ, ?_⟩
  exact psiV_preimage_inter hXeq

end Work.WilE8.StarR
