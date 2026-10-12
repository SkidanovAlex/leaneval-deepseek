import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SboxEB
import Submission.Work.SmallBoxA0.Final
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory

/-! ## Auxiliary: the product-set integral over `acube s ×ˢ acube s` as an iterated integral

For a continuous `f` on the square `acube s ×ˢ acube s` the set integral over the square may be
computed as the iterated integral with the *second* coordinate outermost.  The proof is the
measure-preserving swap of the two cube factors (`MeasureTheory.setIntegral_prod_swap`) followed
by Fubini (`MeasureTheory.setIntegral_prod`). -/
lemma setIntegral_prod_acube_swap {s : ℝ} (hs : 0 < s)
    {f : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Continuous f) :
    (∫ q in Submission.BoseGases.acube s ×ˢ Submission.BoseGases.acube s, f q)
      = ∫ z in Submission.BoseGases.acube s, ∫ y in Submission.BoseGases.acube s, f (y, z) := by
  have hA : IsCompact (Submission.BoseGases.acube s ×ˢ Submission.BoseGases.acube s) :=
    (Submission.BoseGases.acube_compact hs).prod (Submission.BoseGases.acube_compact hs)
  have hgc : Continuous (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => f q.swap) :=
    hf.comp continuous_swap
  have hgi : IntegrableOn
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => f q.swap)
      (Submission.BoseGases.acube s ×ˢ Submission.BoseGases.acube s)
      (volume.prod volume) :=
    hgc.continuousOn.integrableOn_compact hA
  rw [Measure.volume_eq_prod (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))]
  rw [← setIntegral_prod_swap (Submission.BoseGases.acube s) (Submission.BoseGases.acube s) f]
  exact setIntegral_prod (fun q => f q.swap) hgi

lemma peel_fibre_sq {p : ℕ} {s : ℝ} (hs : 0 < s) (i : Fin (p + 2)) (j' : Fin (p + 1))
    {B : Submission.BoseGases.X (p + 2) → ℝ} (hB : Continuous B) :
    MeasureTheory.Integrable (fun r2 : Submission.BoseGases.X p =>
        ∫ q in Submission.BoseGases.acube s ×ˢ Submission.BoseGases.acube s,
          (B (Submission.BoseGases.ins2 i j' q.1 q.2 r2)) ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X p)).restrict (Submission.BoseGases.abox p s)) ∧
    (∫ x in Submission.BoseGases.abox (p + 2) s, (B x) ^ 2)
      = ∫ r2 in Submission.BoseGases.abox p s,
          ∫ q in Submission.BoseGases.acube s ×ˢ Submission.BoseGases.acube s,
            (B (Submission.BoseGases.ins2 i j' q.1 q.2 r2)) ^ 2 := by
  -- `B ^ 2` is integrable on the box, `abox` being compact.
  have hFint : IntegrableOn (fun x : Submission.BoseGases.X (p + 2) => (B x) ^ 2)
      (Submission.BoseGases.abox (p + 2) s) volume :=
    (hB.pow 2).continuousOn.integrableOn_compact
      (Submission.BoseGases.abox_compact (p + 2) hs)
  -- continuity of the fibre integrand, uniformly in `r2`
  have hcont : ∀ r2 : Submission.BoseGases.X p,
      Continuous (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        (B (Submission.BoseGases.ins2 i j' q.1 q.2 r2)) ^ 2) := by
    intro r2
    refine Continuous.pow ?_ 2
    simp only [Submission.BoseGases.ins2]
    exact hB.comp ((Submission.BoseGases.kcInsN_cont (n := p + 1) i).comp
      (Continuous.prodMk continuous_fst ((Submission.BoseGases.kcInsN_cont (n := p) j').comp
        (Continuous.prodMk continuous_snd continuous_const))))
  -- the pointwise identification of the two-slot fibre integral with the square integral
  have hinner : ∀ r2 : Submission.BoseGases.X p,
      (∫ z in Submission.BoseGases.acube s, ∫ y in Submission.BoseGases.acube s,
        (B (Submission.BoseGases.kcInsN (p + 1) i
          (y, Submission.BoseGases.kcInsN p j' (z, r2)))) ^ 2)
      = ∫ q in Submission.BoseGases.acube s ×ˢ Submission.BoseGases.acube s,
          (B (Submission.BoseGases.ins2 i j' q.1 q.2 r2)) ^ 2 := by
    intro r2
    exact (setIntegral_prod_acube_swap hs (hcont r2)).symm
  -- integrability of the peeled fibres, twice
  have h1 : Integrable (fun r : Submission.BoseGases.X (p + 1) =>
      ∫ y in Submission.BoseGases.acube s, (B (Submission.BoseGases.kcInsN (p + 1) i (y, r))) ^ 2)
      ((volume : Measure (Submission.BoseGases.X (p + 1))).restrict
        (Submission.BoseGases.abox (p + 1) s)) :=
    Submission.BoseGases.abox_peel_inner_integrable (n := p + 1) (i := i)
      (F := fun x : Submission.BoseGases.X (p + 2) => (B x) ^ 2) hFint
  have h2 : Integrable (fun r2 : Submission.BoseGases.X p =>
      ∫ z in Submission.BoseGases.acube s, ∫ y in Submission.BoseGases.acube s,
        (B (Submission.BoseGases.kcInsN (p + 1) i
          (y, Submission.BoseGases.kcInsN p j' (z, r2)))) ^ 2)
      ((volume : Measure (Submission.BoseGases.X p)).restrict (Submission.BoseGases.abox p s)) :=
    Submission.BoseGases.abox_peel_inner_integrable (n := p) (i := j')
      (F := fun r : Submission.BoseGases.X (p + 1) =>
        ∫ y in Submission.BoseGases.acube s, (B (Submission.BoseGases.kcInsN (p + 1) i (y, r))) ^ 2) h1
  refine ⟨h2.congr (Filter.Eventually.of_forall fun r2 => hinner r2), ?_⟩
  -- the double peel, then the pointwise rewriting of the fibre integral
  have hpeel := Submission.BoseGases.abox_integral_peel2 (p := p) (ℓ := s) i j'
    (fun x : Submission.BoseGases.X (p + 2) => (B x) ^ 2) hFint
  exact hpeel.trans (integral_congr_ae (Filter.Eventually.of_forall fun r2 => hinner r2))

end Work.SmallBoxA0
