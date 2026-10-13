import Submission.Work.DSM2p.ker_algebraMap_quot_le_maximal_assembly
import Submission.Work.DSM2p.exists_model_field_of_prime

/-!
# `Work.DSM2p.ker_algebraMap_quot_le_maximal_via_model`

The kernel estimate `ker (A → A' ⧸ J) ≤ 𝔪` for `A` perfectoid and `𝔪` maximal with `p ∈ 𝔪`,
obtained by combining

* `Work.DSM2p.nilp_prime_le_maximal` (a prime `𝔮 ⊆ 𝔪` avoiding the non-zero-divisor `p`),
* `Work.DSM2p.exists_model_field_of_prime` (an algebraically closed model field over `A ⧸ 𝔮` in
  which `ϖ` is a unit and every `F ∈ 𝒫⁺` has a compatible system of `p`-power roots),
* `Work.DSM2p.ker_le_of_model_field` (the construction of `Λ[1/ϖ] → K` killing `J`).
-/

open scoped Classical

namespace Work.DSM2p

universe u

/-- **The kernel estimate.**  This is `Work.DSM2p.ker_algebraMap_quot_le_maximal_aux` proved via
the model field. -/
theorem ker_algebraMap_quot_le_maximal_via_model (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A]
    (P : DSMap.PerfectoidData p A) (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) (hp : (p : A) ∈ 𝔪) :
    RingHom.ker (algebraMap A
      (↥(CSIntegralClosurePos A p (P.ϖ 0)) ⧸ CSIdealPosExt A p (P.ϖ 0))) ≤ 𝔪 := by
  haveI : 𝔪.IsMaximal := h𝔪
  obtain ⟨𝔮, h𝔮prime, h𝔮le, hp𝔮⟩ := nilp_prime_le_maximal 𝔪 hp P.torsionFree
  obtain ⟨K, hKfield, hKalg, hkerK, hϖunit, hroots⟩ :=
    exists_model_field_of_prime p A P 𝔮 h𝔮prime hp𝔮
  exact @ker_le_of_model_field p (inferInstance : Fact p.Prime) A (inferInstance : CommRing A) P
    𝔪 h𝔪 hp 𝔮 h𝔮le K hKfield hKalg hkerK hϖunit hroots

end Work.DSM2p
