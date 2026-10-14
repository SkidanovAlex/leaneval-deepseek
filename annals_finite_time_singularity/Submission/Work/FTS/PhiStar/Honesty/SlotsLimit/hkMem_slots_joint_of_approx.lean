import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.slot_aPriori_smooth
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.weighted_le_of_limit
import Submission.Work.FTS.PhiStar.Honesty.ellEstUnif_diff
import Submission.Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.Spaces.mixed_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

/-- **The limit-passage (a.e.-in-`z` / joint) part of `Work.FTS.PhiStar.Honesty.hkMem_slots_of_approx`.**

The approximants `psiSeries α (G n)` are honest solutions of `bslOp α · = G n` at level `k+1`
(`EllWeakPos`), `G n → F` in `HkSq α (k+1)`, and they converge to `Φ` in `L²(Q0)`, while
`Φ` solves `bslOp α Φ = F`.  Conclusion: the level-`k` `HkIntegrand` of each of the three slots
`z²∂_z²Φ`, `∂_θ²Φ`, `z∂_z∂_θ²Φ` is jointly integrable over `Q0`; equivalently (Tonelli) its
`θ`-slice is integrable for a.e. `z ∈ Iz` and the outer integral converges.

Route (all pieces in the tree): for each active pair `p ∈ HkActivePairs k` and each `r : Fin 3`
instantiate `SlotsLimit.weighted_le_of_limit` with `T := subSlot r p.1 p.2`,
`Tstar := subSlotStar r p.1 p.2`, `ρ := termWeight α p.2`; the IBP hypothesis is
`SlotsLimit.IBP_subSlot`; the bound/Cauchy data come from `SlotsLimit.slot_aPriori_smooth`
(level `k+1`) and `SlotsLimit.term_integral_le_HkSq`; the integrability hypotheses for
`T (psiSeries α (G n))` come from `SlotsLimit.integrableOn_term` (+ `mixed_sub_eqOn` for the
differences); `hL2`/`hL2t` are the own `hL2`/`hL2t` of this statement.  Then sum over the
finitely many `p` using `SlotsLimit.HkActivePairs_spec` (the identity of `HkIntegrand` with the
`HkActivePairs`-sum).  Conjuncts (2) and (3) are Tonelli consequences of conjunct (1). -/
theorem hkMem_slots_joint_of_approx (k : ℕ) (hk : 2 ≤ k) {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {F : ℝ → ℝ → ℝ} (hsmF : Work.FTS.EllipticEst.SmoothOpen F)
    (hF : Work.Spaces.HkMem α (k + 1) F)
    (G : ℕ → ℝ → ℝ → ℝ) (hsmG : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n))
    (hGn : ∀ n : ℕ, Work.Spaces.HkMem α (k + 1) (G n))
    (hEll : ∀ n : ℕ, Work.FTS.EllipticEst.TT.EllWeakPos α (k + 1) (G n)
      (Work.FTS.PhiStar.Series.psiSeries α (G n)))
    (hconv : Filter.Tendsto (fun n : ℕ => Work.Spaces.HkSq α (k + 1)
      (fun z θ => G n z θ - F z θ)) Filter.atTop (nhds 0))
    {Φ : ℝ → ℝ → ℝ} (hsmΦ : Work.FTS.EllipticEst.SmoothOpen Φ)
    (hEqΦ : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Φ z θ = F z θ)
    (hL2 : ∀ n : ℕ, MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.FTS.PhiStar.Series.psiSeries α (G n) p.1 p.2 - Φ p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0)
    (hL2t : Filter.Tendsto (fun n : ℕ => ∫ p in Work.FTS.EllipticEst.Q0,
        (Work.FTS.PhiStar.Series.psiSeries α (G n) p.1 p.2 - Φ p.1 p.2) ^ 2)
      Filter.atTop (nhds 0)) :
    (∀ r : Fin 3, MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        Work.Spaces.HkIntegrand α k
          (Work.FTS.PhiStar.Honesty.SlotsLimit.slot r.1 Φ) p.1 p.2)
      Work.FTS.EllipticEst.Q0) ∧
    (∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), ∀ r : Fin 3,
      MeasureTheory.IntegrableOn (fun θ : ℝ =>
        Work.Spaces.HkIntegrand α k
          (Work.FTS.PhiStar.Honesty.SlotsLimit.slot r.1 Φ) z θ) Work.Spaces.Iθ) ∧
    (∀ r : Fin 3, MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k
          (Work.FTS.PhiStar.Honesty.SlotsLimit.slot r.1 Φ) z θ) Work.Spaces.Iz) := by
  classical
  -- The family of approximants.
  let ψ : ℕ → ℝ → ℝ → ℝ := fun n => Work.FTS.PhiStar.Series.psiSeries α (G n)
  have hsmψ : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (ψ n) := fun n =>
    Work.FTS.EllipticEst.smoothOpen_of_forall ((hEll n).smooth)
  -- The a priori data at level `k`: honesty, the uniform bound `B` and the Cauchy property of
  -- the three slots of the approximants (`slot_aPriori_smooth`, level `k + 1`).
  obtain ⟨B, _hB, hmemB, hsqB, hmemD, hcauchyB⟩ :=
    slot_aPriori_smooth k (by omega) hα hα4 hsmG hGn hsmF hF hEll hconv
  -- ### Integrability of the squared difference of two bounded families
  have hsubsq : ∀ {ρ a b : ℝ → ℝ → ℝ},
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (a p.1 p.2) ^ 2 * (ρ p.1 p.2) ^ 2)
        Work.FTS.EllipticEst.Q0 →
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (b p.1 p.2) ^ 2 * (ρ p.1 p.2) ^ 2)
        Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => (a p.1 p.2 - b p.1 p.2) ^ 2 * (ρ p.1 p.2) ^ 2)
        (MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0) →
      MeasureTheory.IntegrableOn
        (fun p : ℝ × ℝ => (a p.1 p.2 - b p.1 p.2) ^ 2 * (ρ p.1 p.2) ^ 2)
        Work.FTS.EllipticEst.Q0 := by
    intro ρ a b ha hb hae
    have h2 : MeasureTheory.Integrable
        (fun p : ℝ × ℝ => (a p.1 p.2) ^ 2 * (ρ p.1 p.2) ^ 2
          + (b p.1 p.2) ^ 2 * (ρ p.1 p.2) ^ 2)
        (MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0) := ha.add hb
    refine (h2.const_mul 2).mono' hae (Filter.Eventually.of_forall fun p => ?_)
    have hkey : (a p.1 p.2 - b p.1 p.2) ^ 2 * (ρ p.1 p.2) ^ 2
        ≤ 2 * ((a p.1 p.2) ^ 2 * (ρ p.1 p.2) ^ 2
          + (b p.1 p.2) ^ 2 * (ρ p.1 p.2) ^ 2) := by
      have e1 : (a p.1 p.2 - b p.1 p.2) ^ 2 * (ρ p.1 p.2) ^ 2
          = (a p.1 p.2 * ρ p.1 p.2 - b p.1 p.2 * ρ p.1 p.2) ^ 2 := by ring
      rw [e1]
      nlinarith [sq_nonneg (a p.1 p.2 * ρ p.1 p.2 + b p.1 p.2 * ρ p.1 p.2)]
    simpa only [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))] using hkey
  -- ### The per-sub-slot limit passage
  have hterm : ∀ (r : Fin 3) (p : ℕ × ℕ), p ∈ HkActivePairs k →
      MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
        (Work.Spaces.mixed p.1 p.2 (slot r.1 Φ) q.1 q.2 * termWeight α p.2 q.1 q.2) ^ 2)
        Work.FTS.EllipticEst.Q0 := by
    intro r p hp
    obtain ⟨hρpos0, hρcont⟩ :=
      Joint.termWeight_pos_and_continuousOn_Q0 α p.2
    have hρpos : ∀ q ∈ Work.FTS.EllipticEst.Q0, 0 < termWeight α p.2 q.1 q.2 := by
      intro q hq
      obtain ⟨h1, h2, h3⟩ := Work.FTS.EllipticEst.mem_Q0.mp hq
      exact hρpos0 q.1 q.2 h1 h2 h3
    -- the index guard of `HkActivePairs k`, in the shape the term lemmas use
    have hguard : (p.2 = 0 ∧ p.1 ≤ k) ∨ (1 ≤ p.2 ∧ p.2 + p.1 ≤ k) := by
      rcases (HkActivePairs_mem k p).1 hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
    have hslotψ : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (slot r.1 (ψ n)) :=
      fun n => smoothOpen_slot (hsmψ n) r.1
    have hslotΦ : Work.FTS.EllipticEst.SmoothOpen (slot r.1 Φ) := smoothOpen_slot hsmΦ r.1
    have hTsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (subSlot r.1 p.1 p.2 (ψ n)) :=
      fun n => (hslotψ n).mixed p.1 p.2
    have hTΦsm : Work.FTS.EllipticEst.SmoothOpen (subSlot r.1 p.1 p.2 Φ) :=
      hslotΦ.mixed p.1 p.2
    -- integrability of the `(j,i)`-term of the approximants
    have hint : ∀ n : ℕ, MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
        (subSlot r.1 p.1 p.2 (ψ n) q.1 q.2) ^ 2 * (termWeight α p.2 q.1 q.2) ^ 2)
        Work.FTS.EllipticEst.Q0 := by
      intro n
      have h := integrableOn_term α k (hslotψ n) (hmemB r n) p.1 p.2 hguard
      simpa only [subSlot, mul_pow] using h
    -- the same for the differences
    have hint2 : ∀ n m : ℕ, MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
        (subSlot r.1 p.1 p.2 (ψ n) q.1 q.2 - subSlot r.1 p.1 p.2 (ψ m) q.1 q.2) ^ 2
          * (termWeight α p.2 q.1 q.2) ^ 2) Work.FTS.EllipticEst.Q0 := by
      intro n m
      refine hsubsq (ρ := termWeight α p.2) (a := subSlot r.1 p.1 p.2 (ψ n))
        (b := subSlot r.1 p.1 p.2 (ψ m)) (hint n) (hint m) ?_
      have h1 : ContinuousOn (fun q : ℝ × ℝ =>
          subSlot r.1 p.1 p.2 (ψ n) q.1 q.2) Work.FTS.EllipticEst.Q0 :=
        (hTsm n).continuousOn
      have h2 : ContinuousOn (fun q : ℝ × ℝ =>
          subSlot r.1 p.1 p.2 (ψ m) q.1 q.2) Work.FTS.EllipticEst.Q0 :=
        (hTsm m).continuousOn
      have h3 : ContinuousOn (fun q : ℝ × ℝ => termWeight α p.2 q.1 q.2)
          Work.FTS.EllipticEst.Q0 := hρcont
      exact (((h1.sub h2).pow 2).mul (h3.pow 2)).aestronglyMeasurable
        Work.FTS.EllipticEst.isOpen_Q0.measurableSet
    -- the uniform bound
    have hb : ∀ n : ℕ, ∫ q in Work.FTS.EllipticEst.Q0,
        (subSlot r.1 p.1 p.2 (ψ n) q.1 q.2) ^ 2 * (termWeight α p.2 q.1 q.2) ^ 2 ≤ B := by
      intro n
      have h := term_integral_le_HkSq α k (hslotψ n) (hmemB r n) p.1 p.2 hguard
      have heq : (fun q : ℝ × ℝ => (subSlot r.1 p.1 p.2 (ψ n) q.1 q.2) ^ 2
            * (termWeight α p.2 q.1 q.2) ^ 2)
          = fun q : ℝ × ℝ => (Work.Spaces.mixed p.1 p.2 (slot r.1 (ψ n)) q.1 q.2
            * termWeight α p.2 q.1 q.2) ^ 2 := by
        funext q
        simp only [subSlot]
        ring
      rw [heq]
      exact le_trans h (hsqB r n)
    -- the Cauchy property
    have hcauchy : Filter.Tendsto (fun nm : ℕ × ℕ => ∫ q in Work.FTS.EllipticEst.Q0,
        (subSlot r.1 p.1 p.2 (ψ nm.1) q.1 q.2 - subSlot r.1 p.1 p.2 (ψ nm.2) q.1 q.2) ^ 2
          * (termWeight α p.2 q.1 q.2) ^ 2)
        (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
      have h := Joint.tendsto_term_integral_of_tendsto_HkSq (α := α) (k := k)
        (A := fun n => slot r.1 (ψ n)) p.1 p.2 hguard hslotψ (fun n m => hmemD r n m)
        (hcauchyB r)
      simpa only [subSlot] using h
    -- the limit passage
    obtain ⟨hfin, _⟩ := weighted_le_of_limit (B := B) (ρ := termWeight α p.2)
      (T := subSlot r.1 p.1 p.2) (Tstar := subSlotStar r.1 p.1 p.2) (ψ := ψ) (Φ := Φ)
      hρpos hρcont (fun {f φ} hf hφ => IBP_subSlot r.1 p.1 p.2 hf hφ)
      hsmψ hsmΦ hTsm hTΦsm hL2 hL2t hint hint2 hb hcauchy
    simpa only [subSlot, mul_pow] using hfin
  -- ### Conjunct 1: the joint integrability of the `ℋ^k`-integrand of each slot
  have hconj1 : ∀ r : Fin 3, MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α k (slot r.1 Φ) q.1 q.2) Work.FTS.EllipticEst.Q0 := by
    intro r
    have hsum : (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k (slot r.1 Φ) q.1 q.2)
        = fun q : ℝ × ℝ => ∑ p ∈ HkActivePairs k,
            (Work.Spaces.mixed p.1 p.2 (slot r.1 Φ) q.1 q.2
              * termWeight α p.2 q.1 q.2) ^ 2 := by
      funext q
      exact (HkActivePairs_spec k).2 α (slot r.1 Φ) q.1 q.2
    rw [hsum]
    exact MeasureTheory.integrable_finsetSum (HkActivePairs k) (fun p hp => hterm r p hp)
  -- ### Conjuncts 2 and 3: the Tonelli consequences of conjunct 1
  have hconj2 : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), ∀ r : Fin 3,
      MeasureTheory.IntegrableOn (fun θ : ℝ =>
        Work.Spaces.HkIntegrand α k (slot r.1 Φ) z θ) Work.Spaces.Iθ := by
    rw [Filter.eventually_all]
    intro r
    exact (Joint.tonelli_slices_of_integrableOn_Q0
      (g := fun z θ => Work.Spaces.HkIntegrand α k (slot r.1 Φ) z θ)
      (hint := hconj1 r)).1
  have hconj3 : ∀ r : Fin 3, MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (slot r.1 Φ) z θ) Work.Spaces.Iz := by
    intro r
    exact (Joint.tonelli_slices_of_integrableOn_Q0
      (g := fun z θ => Work.Spaces.HkIntegrand α k (slot r.1 Φ) z θ)
      (hint := hconj1 r)).2
  exact ⟨hconj1, hconj2, hconj3⟩

end Work.FTS.PhiStar.Honesty.SlotsLimit
