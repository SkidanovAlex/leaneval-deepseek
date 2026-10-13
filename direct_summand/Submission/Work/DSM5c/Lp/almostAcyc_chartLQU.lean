import Mathlib
import Submission.Work.DSM5c.Lp.chartDToLp_exists
import Submission.Work.DSM5c.Eta.exists_chartMap
import Submission.Work.DSM5c.CharP
import Submission.Work.DSM5c.CharPChart
import Submission.Work.DSM5c.Lp.ThetaCoord
import Submission.Work.DSM5c.Lp.Theta_dU
import Submission.Work.DSM5c.Lp.Theta_smulU
import Submission.Work.DSM5c.Lp.Theta_coaugU
import Submission.Work.DSM5c.Lp.chartLQ_smul_top_botU
import Submission.Work.DSM5c.Lp.chartLpR_smul_top_botU
import Submission.Work.DSM5c.Lp.smul_mem_span_pU
import Submission.Work.DSM5c.Lp.chartLpRU

namespace Work.DSM5c.Lp

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe u

/-- **Universe-polymorphic version of transport steps 3–4** (the characteristic-`p` input
`area_M5b` on the mod-`p` chart complex, in the shape the transport consumes), at an arbitrary
universe so that the assembly in `Submission/Work/DSM5c/Main.lean` can use it.

Note the explicit universe instance `Work.DSM5c.M5bInterface.{u}` on the hypothesis: `M5bInterface`
carries its own universe parameter, and without the ascription Lean would introduce an unrelated
fresh one, leaving the hypothesis useless for `PreTilt W p : Type u`.

Content: from `hM5b` read at the tilted chart datum (`Work.DSM5c.m5bInput_chartTiltGen`,
`T := Work.DSM5c.tiltVarpi Q`), produce `eL : W → Č(chartLQ)^0` with
`AlmostAcyc Q.ϖ (span{p}) (Č chartLQ) eL` and the pinning equation
`(Č chartLQEta).f 0 ((Č η).f 0 ((chartCoaugW t) w)) = eL.hom w` — exactly the `he` of
`Work.DSM5c.Devissage.almostAcyc_of_surjective_kernel_v2`.  Note that some of the ingredients of
the `Type 0` sibling (`Lp/almostAcyc_tiltGen.lean`, `Lp/almostAcyc_chartLpR.lean`) are themselves
`Type 0` and will need their binders loosened in turn. -/
theorem almostAcyc_chartLQU {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W] [Fact ¬IsUnit (p : W)]
    [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type u} [Finite ι] [DecidableEq ι]
    (hM5b : Work.DSM5c.M5bInterface.{u}) (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (η : DSMap.Mix2.chartPresheaf t ⟶
      Work.DSM5c.chartD (p := p) (W := W) Q hθ t tr htr0 htr j₀ e)
    (hη : ∀ (S : (Finset ι)ᵒᵖᵒᵖ) (w : W),
      letI := Work.DSM5c.chartDAlg (p := p) (W := W) Q hθ t tr htr0 htr j₀ e S.unop.unop
      η.app S (algebraMap W (DSMap.Mix2.chartRing t S.unop.unop) w) =
        w • (1 : Work.DSM5c.untiltOf (p := p) (W := W)
          (Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e S.unop.unop)
          (Work.DSM5c.chartPhi Q t tr htr0 htr j₀ e S.unop.unop))) :
    ∃ eL : ModuleCat.of W W ⟶ ((cechComplexFunctor (chartIdx ι)).obj
        (Work.DSM5c.Lp.chartLQ (p := p) (W := W) Q hθ t tr htr0 htr j₀ e)).X 0,
      DSMap.Mix2.AlmostAcyc Q.ϖ (Ideal.span {(p : W)})
        ((cechComplexFunctor (chartIdx ι)).obj
          (Work.DSM5c.Lp.chartLQ (p := p) (W := W) Q hθ t tr htr0 htr j₀ e)) eL ∧
      (∀ w : W,
        (((cechComplexFunctor (chartIdx ι)).map
            (Work.DSM5c.Lp.chartLQEta (p := p) (W := W) Q hθ t tr htr0 htr j₀ e)).f 0).hom
          (((cechComplexFunctor (chartIdx ι)).map η).f 0
            ((chartCoaugW t).hom w)) = eL.hom w) := by
  -- the characteristic-`p` input at the tilted chart datum, then its mod-`p` chart form over `W♭`
  have hM5bT : Work.DSM5c.M5bInput p (PreTilt W p)
      (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) (Work.DSM5c.tiltVarpi Q) :=
    Work.DSM5c.m5bInput_chartTiltGen (p := p) (W := W) (ι := ι) hM5b Q t tr htr0 htr j₀ e
  have hK := almostAcyc_chartLpRU Q t tr htr0 htr j₀ e hM5bT
  -- the diagonal mod-`p` chart coaugmentation
  let eL : ModuleCat.of W W ⟶ ((cechComplexFunctor (chartIdx ι)).obj
      (chartLQ Q hθ t tr htr0 htr j₀ e)).X 0 :=
    (chartCoaugW t) ≫ ((cechComplexFunctor (chartIdx ι)).map η).f 0 ≫
      ((cechComplexFunctor (chartIdx ι)).map
        (chartLQEta Q hθ t tr htr0 htr j₀ e)).f 0
  refine ⟨eL, ?_, ?_⟩
  · -- the three clauses of `AlmostAcyc` are transported along the elementwise transport `Θ`
    -- (`Work.DSM5c.Lp.Theta`), using that `(p) • ⊤ = ⊥` on `Č(chartLQ)` and `((ϖ♭)^p) • ⊤ = ⊥`
    -- on `Č(chartLpR)`.
    refine ⟨?_, ?_, ?_⟩
    · -- clause (1): almost injectivity of the coaugmentation on `H⁰`
      intro w hw k
      have hw0 : eL.hom w = 0 := by
        have h := hw
        rw [chartLQ_smul_top_botU Q hθ t tr htr0 htr j₀ e 0,
          Submodule.mem_bot] at h
        exact h
      obtain ⟨x, hx⟩ : ∃ x : PreTilt W p,
          Ideal.Quotient.mk (Ideal.span {Work.DSM5c.tiltVarpi Q ^ p}) x =
            Work.DSM5c.pb2Equiv Q (Ideal.Quotient.mk (Ideal.span {(p : W)}) w) :=
        Ideal.Quotient.mk_surjective
          (Work.DSM5c.pb2Equiv Q (Ideal.Quotient.mk (Ideal.span {(p : W)}) w))
      have hcoaug : Theta Q hθ t tr htr0 htr j₀ e 0 (eL.hom w) =
          (chartLpRCoaug Q t tr htr0 htr j₀ e).hom x :=
        Theta_coaugU Q hθ t tr htr0 htr j₀ e η hη w x hx
      have hKmem : (chartLpRCoaug Q t tr htr0 htr j₀ e).hom x ∈
          Ideal.span {(Work.DSM5c.tiltVarpi Q) ^ p} •
            (⊤ : Submodule (PreTilt W p)
              (((cechComplexFunctor (chartIdx ι)).obj
                (chartLpR Q t tr htr0 htr j₀ e)).X 0)) := by
        rw [chartLpR_smul_top_botU Q t tr htr0 htr j₀ e 0, Submodule.mem_bot,
          ← hcoaug, hw0]
        exact Theta_zero Q hθ t tr htr0 htr j₀ e 0
      exact smul_mem_span_pU Q w x hx (hK.1 x hKmem) k
    · -- clause (2): almost surjectivity of the coaugmentation on `H⁰`
      intro z hz k
      have hz0 : (((cechComplexFunctor (chartIdx ι)).obj
          (chartLQ Q hθ t tr htr0 htr j₀ e)).d 0 1).hom z = 0 := by
        have h := hz
        rw [chartLQ_smul_top_botU Q hθ t tr htr0 htr j₀ e 1,
          Submodule.mem_bot] at h
        exact h
      have hKmem : (((cechComplexFunctor (chartIdx ι)).obj
          (chartLpR Q t tr htr0 htr j₀ e)).d 0 1).hom
          (Theta Q hθ t tr htr0 htr j₀ e 0 z) ∈
          Ideal.span {(Work.DSM5c.tiltVarpi Q) ^ p} •
            (⊤ : Submodule (PreTilt W p)
              (((cechComplexFunctor (chartIdx ι)).obj
                (chartLpR Q t tr htr0 htr j₀ e)).X 1)) := by
        rw [chartLpR_smul_top_botU Q t tr htr0 htr j₀ e 1, Submodule.mem_bot,
          ← Theta_dU Q hθ t tr htr0 htr j₀ e 0 z, hz0,
          Theta_zero Q hθ t tr htr0 htr j₀ e 1]
      obtain ⟨x, hx⟩ := hK.2.1 (Theta Q hθ t tr htr0 htr j₀ e 0 z) hKmem k
      have hx0 : ((frobeniusEquiv (PreTilt W p) p).symm^[k] (Work.DSM5c.tiltVarpi Q)) •
          (Theta Q hθ t tr htr0 htr j₀ e 0 z) =
          (chartLpRCoaug Q t tr htr0 htr j₀ e).hom x := by
        have h := hx
        rw [chartLpR_smul_top_botU Q t tr htr0 htr j₀ e 0, Submodule.mem_bot] at h
        exact sub_eq_zero.mp h
      refine ⟨PreTilt.untilt x, ?_⟩
      have hcoaug : Theta Q hθ t tr htr0 htr j₀ e 0 (eL.hom (PreTilt.untilt x)) =
          (chartLpRCoaug Q t tr htr0 htr j₀ e).hom x :=
        Theta_coaugU Q hθ t tr htr0 htr j₀ e η hη (PreTilt.untilt x) x
          (Work.DSM5c.pb2Equiv_mk_untilt Q x).symm
      rw [chartLQ_smul_top_botU Q hθ t tr htr0 htr j₀ e 0, Submodule.mem_bot]
      refine sub_eq_zero.mpr (Theta_injective Q hθ t tr htr0 htr j₀ e 0 ?_)
      rw [Theta_smulU Q hθ t tr htr0 htr j₀ e 0 k z, hx0, hcoaug]
    · -- clause (3): almost exactness in positive degrees
      intro q z hz k
      have hz0 : (((cechComplexFunctor (chartIdx ι)).obj
          (chartLQ Q hθ t tr htr0 htr j₀ e)).d (q + 1) (q + 2)).hom z = 0 := by
        have h := hz
        rw [chartLQ_smul_top_botU Q hθ t tr htr0 htr j₀ e (q + 2),
          Submodule.mem_bot] at h
        exact h
      have hKmem : (((cechComplexFunctor (chartIdx ι)).obj
          (chartLpR Q t tr htr0 htr j₀ e)).d (q + 1) (q + 2)).hom
          (Theta Q hθ t tr htr0 htr j₀ e (q + 1) z) ∈
          Ideal.span {(Work.DSM5c.tiltVarpi Q) ^ p} •
            (⊤ : Submodule (PreTilt W p)
              (((cechComplexFunctor (chartIdx ι)).obj
                (chartLpR Q t tr htr0 htr j₀ e)).X (q + 2))) := by
        rw [chartLpR_smul_top_botU Q t tr htr0 htr j₀ e (q + 2), Submodule.mem_bot,
          ← Theta_dU Q hθ t tr htr0 htr j₀ e (q + 1) z, hz0,
          Theta_zero Q hθ t tr htr0 htr j₀ e (q + 2)]
      obtain ⟨y', hy'⟩ := hK.2.2 q (Theta Q hθ t tr htr0 htr j₀ e (q + 1) z) hKmem k
      have hy0 : ((frobeniusEquiv (PreTilt W p) p).symm^[k] (Work.DSM5c.tiltVarpi Q)) •
          (Theta Q hθ t tr htr0 htr j₀ e (q + 1) z) =
          (((cechComplexFunctor (chartIdx ι)).obj
            (chartLpR Q t tr htr0 htr j₀ e)).d q (q + 1)).hom y' := by
        have h := hy'
        rw [chartLpR_smul_top_botU Q t tr htr0 htr j₀ e (q + 1),
          Submodule.mem_bot] at h
        exact sub_eq_zero.mp h
      obtain ⟨y, hy⟩ := Theta_surjective Q hθ t tr htr0 htr j₀ e q y'
      refine ⟨y, ?_⟩
      rw [chartLQ_smul_top_botU Q hθ t tr htr0 htr j₀ e (q + 1), Submodule.mem_bot]
      refine sub_eq_zero.mpr (Theta_injective Q hθ t tr htr0 htr j₀ e (q + 1) ?_)
      rw [Theta_smulU Q hθ t tr htr0 htr j₀ e (q + 1) k z, hy0, ← hy]
      exact (Theta_dU Q hθ t tr htr0 htr j₀ e q y).symm
  · -- the pinning equation is the definition of `eL`
    intro w
    rfl

end Work.DSM5c.Lp
