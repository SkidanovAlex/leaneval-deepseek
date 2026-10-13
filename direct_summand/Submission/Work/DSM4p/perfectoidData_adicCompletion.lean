import Mathlib
import Submission.Work.DSM4p.Completion
import Submission.Work.DSM4p.chartComp_modPow
import Submission.Work.DSM4p.chartComp_isAdicComplete
import Submission.Work.DSM2p.adicCompletion_isSMulRegular
import Submission.Work.DSM4p.adicCompletion_frobSurj
import Submission.Work.DSM4p.adicCompletion_frobInj

/-!
# DSM4p — `PerfectoidData` on the `p`-adic completion of a perfectoid-mod-`p` algebra

Given a perfectoid `B` (`Q : DSMap.PerfectoidData p B`) and a `B`-algebra `E` which is
`p`-torsion-free, perfect modulo `p` (`hsurj`: every element is a `p`-th power modulo `p`) and
Frobenius-injective modulo `ϖ₀` (`hinj`), the `p`-adic completion
`Ê = AdicCompletion (Ideal.span {p}) E` again carries the structure of a perfectoid ring: the
pseudo-uniformizer is the image of `Q.ϖ`, and all seven fields of `DSMap.PerfectoidData` are
inherited from `E`.

* `ϖ` and `root`: images of `Q.ϖ`, using `Q.root`;
* `unit`: `Q.unit` pushed through `algebraMap B E` (a unit maps to a unit);
* `torsionFree`: `Work.DSM2p.adicCompletion_isSMulRegular`;
* `complete`: `AdicCompletion.isAdicComplete`, transported along
  `(Ideal.span {p}).map (algebraMap E Ê) = Ideal.span {p}`;
* `frobSurj`: `Work.DSM4p.adicCompletion_frobSurj` (Frobenius is surjective modulo `p` on the
  completion because the completion does not change the reduction modulo `p`);
* `frobInj`: `Work.DSM4p.adicCompletion_frobInj`, applied to the mod-`p` statement on `E`
  derived from `hinj` by lifting along `E ⧸ (p)`.

No Noetherianness or flatness hypothesis is needed; the only input is that the `p`-adic
completion of `E` still sees the same reduction modulo `p`.
-/

open CategoryTheory AlgebraicGeometry IsLocalRing Limits

namespace Work.DSM4p

universe a

theorem perfectoidData_adicCompletion {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    (Q : DSMap.PerfectoidData p B) {E : Type a} [CommRing E] [Algebra B E]
    (htf : IsSMulRegular E (p : E))
    (hsurj : ∀ x : E, ∃ y, x - y ^ p ∈ Ideal.span {((p : E))})
    (hinj : ∀ y : E, y ^ p ∈ Ideal.span {((p : E))} →
      y ∈ Ideal.span {(algebraMap B E (Q.ϖ 0))}) :
    ∃ QD : DSMap.PerfectoidData p (AdicCompletion (Ideal.span {((p : E))}) E),
      ∀ k, QD.ϖ k = algebraMap B (AdicCompletion (Ideal.span {((p : E))}) E) (Q.ϖ k) := by
  have hFG : (Ideal.span {(p : E)}).FG := Submodule.fg_span_singleton _
  -- the ideal `(p)` of the completion is the image of the ideal `(p)` of `E`
  have hmap : Ideal.span {(p : AdicCompletion (Ideal.span {(p : E)}) E)}
      = (Ideal.span {(p : E)}).map
          (algebraMap E (AdicCompletion (Ideal.span {(p : E)}) E)) := by
    rw [Ideal.map_span, Set.image_singleton, ← map_natCast
      (algebraMap E (AdicCompletion (Ideal.span {(p : E)}) E)) p]
  -- completeness
  have hcomp : IsAdicComplete (Ideal.span {(p : AdicCompletion (Ideal.span {(p : E)}) E)})
      (AdicCompletion (Ideal.span {(p : E)}) E) := by
    rw [hmap]
    exact (IsAdicComplete.map_algebraMap_iff _ _).mpr (AdicCompletion.isAdicComplete hFG)
  -- `p`-torsion-freeness
  have htf' : IsSMulRegular (AdicCompletion (Ideal.span {(p : E)}) E)
      (p : AdicCompletion (Ideal.span {(p : E)}) E) :=
    Work.DSM2p.adicCompletion_isSMulRegular htf
  -- the two structure maps agree: `algebraMap B Ê = algebraMap E Ê ∘ algebraMap B E`
  have hcompAlgebraMap : algebraMap B (AdicCompletion (Ideal.span {(p : E)}) E) (Q.ϖ 0)
      = algebraMap E (AdicCompletion (Ideal.span {(p : E)}) E) (algebraMap B E (Q.ϖ 0)) := by
    rw [AdicCompletion.algebraMap_apply]
    rfl
  -- `ϖ₀ ^ p = p · unit` for the image of `Q.ϖ 0`
  have hunit : ∃ v : Eˣ, (algebraMap B E (Q.ϖ 0)) ^ p = (p : E) * (v : E) := by
    obtain ⟨u, hu⟩ := Q.unit
    refine ⟨Units.map (algebraMap B E) u, ?_⟩
    rw [← map_pow, hu, map_mul, map_natCast]
    exact congrArg (fun x => (p : E) * x) (Units.coe_map _ u).symm
  -- the mod-`p` statement on `E`, obtained from `hinj`
  have hmodp : ∀ u : E ⧸ Ideal.span {(p : E)},
      u ^ p = 0 → u ∈ Ideal.span
        {(Ideal.Quotient.mk (Ideal.span {(p : E)}) (algebraMap B E (Q.ϖ 0)))} := by
    intro u hu
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective u
    have hw : w ^ p ∈ Ideal.span {(p : E)} := by
      have := Ideal.Quotient.eq_zero_iff_mem.mp hu
      simpa using this
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hinj w hw)
    exact Ideal.mem_span_singleton'.mpr
      ⟨Ideal.Quotient.mk (Ideal.span {(p : E)}) c, by rw [← map_mul, hc]⟩
  -- Frobenius injectivity for the completion
  have hfinj : ∀ y : AdicCompletion (Ideal.span {(p : E)}) E,
      y ^ p ∈ Ideal.span {(p : AdicCompletion (Ideal.span {(p : E)}) E)} →
        y ∈ Ideal.span {algebraMap B (AdicCompletion (Ideal.span {(p : E)}) E) (Q.ϖ 0)} := by
    intro y hy
    have h := adicCompletion_frobInj (p := p) (algebraMap B E (Q.ϖ 0)) hunit hmodp y hy
    rw [hcompAlgebraMap]
    exact h
  -- Frobenius surjectivity for the completion
  have hfsurj : ∀ x : AdicCompletion (Ideal.span {(p : E)}) E,
      ∃ y, x - y ^ p ∈ Ideal.span {(p : AdicCompletion (Ideal.span {(p : E)}) E)} :=
    adicCompletion_frobSurj p hsurj
  refine ⟨⟨fun k => algebraMap B (AdicCompletion (Ideal.span {(p : E)}) E) (Q.ϖ k),
      ?_, ?_, htf', hcomp, hfsurj, hfinj⟩, fun k => rfl⟩
  · intro k
    rw [← map_pow, Q.root k]
  · obtain ⟨u, hu⟩ := Q.unit
    refine ⟨Units.map (algebraMap B (AdicCompletion (Ideal.span {(p : E)}) E)) u, ?_⟩
    rw [← map_pow, hu, map_mul, map_natCast]
    exact congrArg (fun x => (p : AdicCompletion (Ideal.span {(p : E)}) E) * x)
      (Units.coe_map _ u).symm

end Work.DSM4p
