import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Peeling one position slot out of the centred box (the `kcInsN` Fubini step)

`Submission.BoseGases.kcInsN n i : kcE3 × X n ≃ᵐ X (n+1)` inserts a one-particle position `y`
into the `i`-th slot of an `n`-particle configuration `r`.  Its preimage of the centred
`(n+1)`-particle box is the product of the one-particle centred cube and the `n`-particle
box, so a `y`-independent integrand can be peeled:

    (s³)⁻¹ ∫_{abox (n+1) s} H = ∫_{abox n s} H (kcInsN n i (0, r))

whenever `H (kcInsN n i (y,r))` does not depend on `y`.  The factor `(s³)⁻¹` is the
normalisation by the volume `volume (acube s) = s³` of the peeled slot.
-/

namespace Work.SmallBoxBridge.Fourier

theorem peel_slot_abox {n : ℕ} {s : ℝ} (hs : 0 < s) (i : Fin (n + 1))
    {H : (Fin (n + 1) → EuclideanSpace ℝ (Fin 3)) → ℝ} (hH : Continuous H)
    (hind : ∀ (r : Fin n → EuclideanSpace ℝ (Fin 3)) (y y' : EuclideanSpace ℝ (Fin 3)),
      H (Submission.BoseGases.kcInsN n i (y, r)) = H (Submission.BoseGases.kcInsN n i (y', r))) :
    (s ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) s, H x
      = ∫ r in Submission.BoseGases.abox n s, H (Submission.BoseGases.kcInsN n i (0, r)) := by
  -- The `kcInsN`-preimage of the `(n+1)`-particle box is the product box.
  have hpre : (Submission.BoseGases.kcInsN n i) ⁻¹' (Submission.BoseGases.abox (n + 1) s)
      = Submission.BoseGases.acube s ×ˢ Submission.BoseGases.abox n s := by
    ext p
    obtain ⟨y, r⟩ := p
    simp only [Set.mem_preimage, Set.mem_prod, Submission.BoseGases.mem_abox_iff]
    constructor
    · intro hp
      exact ⟨by simpa [Submission.BoseGases.kc_insN_apply_same] using hp i,
        fun j => by simpa [Submission.BoseGases.kc_insN_apply_succ] using hp (i.succAbove j)⟩
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj
        simpa [Submission.BoseGases.kc_insN_apply_same] using h1
      · rcases Fin.exists_succAbove_eq hj with ⟨j', hj'⟩
        rw [← hj']
        simpa [Submission.BoseGases.kc_insN_apply_succ] using h2 j'
  -- The restriction of the product volume is the product of the restricted volumes.
  have hvol : (MeasureTheory.volume :
        MeasureTheory.Measure (Submission.BoseGases.kcE3 × Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.acube s ×ˢ Submission.BoseGases.abox n s)
      = (MeasureTheory.volume.restrict (Submission.BoseGases.acube s)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox n s)) := by
    rw [MeasureTheory.Measure.volume_eq_prod (Submission.BoseGases.kcE3) (Submission.BoseGases.X n),
      ← MeasureTheory.Measure.prod_restrict]
  -- Measure preserving restriction of `kcInsN` and its inverse.
  have h1 := (Submission.BoseGases.kc_mp_insN n i).restrict_preimage_emb
      (Submission.BoseGases.kcInsN n i).measurableEmbedding (Submission.BoseGases.abox (n + 1) s)
  have h2 : MeasureTheory.MeasurePreserving (⇑(Submission.BoseGases.kcInsN n i).symm)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (n + 1))).restrict
        (Submission.BoseGases.abox (n + 1) s))
      ((MeasureTheory.volume.restrict (Submission.BoseGases.acube s)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox n s))) := by
    rw [hpre, hvol] at h1
    exact MeasureTheory.MeasurePreserving.symm (Submission.BoseGases.kcInsN n i) h1
  -- Change of variables: the box integral becomes a product integral of `H ∘ kcInsN`.
  have hchange : (∫ x in Submission.BoseGases.abox (n + 1) s, H x)
      = ∫ p : Submission.BoseGases.kcE3 × Submission.BoseGases.X n,
          H (Submission.BoseGases.kcInsN n i p)
        ∂((MeasureTheory.volume.restrict (Submission.BoseGases.acube s)).prod
          (MeasureTheory.volume.restrict (Submission.BoseGases.abox n s))) := by
    have hc := h2.integral_comp (Submission.BoseGases.kcInsN n i).symm.measurableEmbedding
      (fun p : Submission.BoseGases.kcE3 × Submission.BoseGases.X n =>
        H (Submission.BoseGases.kcInsN n i p))
    simpa using hc
  -- The `y`-independence of the integrand.
  have hrew : (∫ p : Submission.BoseGases.kcE3 × Submission.BoseGases.X n,
        H (Submission.BoseGases.kcInsN n i p)
      ∂((MeasureTheory.volume.restrict (Submission.BoseGases.acube s)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox n s))))
      = ∫ p : Submission.BoseGases.kcE3 × Submission.BoseGases.X n,
          H (Submission.BoseGases.kcInsN n i (0, p.2))
        ∂((MeasureTheory.volume.restrict (Submission.BoseGases.acube s)).prod
          (MeasureTheory.volume.restrict (Submission.BoseGases.abox n s))) := by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall (fun p => hind p.2 p.1 0)
  -- Fubini, and the inner `y`-integral of a constant.
  have hprod : (∫ p : Submission.BoseGases.kcE3 × Submission.BoseGases.X n,
          H (Submission.BoseGases.kcInsN n i (0, p.2))
        ∂((MeasureTheory.volume.restrict (Submission.BoseGases.acube s)).prod
          (MeasureTheory.volume.restrict (Submission.BoseGases.abox n s))))
      = (∫ y : Submission.BoseGases.kcE3, (1 : ℝ)
          ∂(MeasureTheory.volume.restrict (Submission.BoseGases.acube s)))
        * (∫ r : Submission.BoseGases.X n, H (Submission.BoseGases.kcInsN n i (0, r))
          ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n s))) := by
    have h := MeasureTheory.integral_prod_mul
      (μ := MeasureTheory.volume.restrict (Submission.BoseGases.acube s))
      (ν := MeasureTheory.volume.restrict (Submission.BoseGases.abox n s))
      (f := fun _ : Submission.BoseGases.kcE3 => (1 : ℝ))
      (g := fun r : Submission.BoseGases.X n => H (Submission.BoseGases.kcInsN n i (0, r)))
    simpa using h
  -- `volume (acube s) = s³`.
  have hint1 : (∫ y : Submission.BoseGases.kcE3, (1 : ℝ)
      ∂(MeasureTheory.volume.restrict (Submission.BoseGases.acube s))) = s ^ 3 := by
    rw [MeasureTheory.integral_const, MeasureTheory.Measure.real,
      MeasureTheory.Measure.restrict_apply_univ,
      Submission.BoseGases.acube_volume s hs.le, ENNReal.toReal_ofReal (by positivity)]
    simp
  rw [hchange, hrew, hprod, hint1, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hs)),
    one_mul]

end Work.SmallBoxBridge.Fourier
