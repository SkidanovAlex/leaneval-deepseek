import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Fourier.peel_slot_abox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Peeling the slot-`i` fibre out of the centred box integral (unconditional form)

`Submission.BoseGases.kcInsN n i : kcE3 × X n ≃ᵐ X (n+1)` inserts a one-particle position `y`
into the `i`-th slot of an `n`-particle configuration `r`.  Its preimage of the centred
`(n+1)`-particle box is the product of the one-particle centred cube and the `n`-particle box,
and the two measures correspond under the (measure-preserving) equivalence.  Hence for an
**arbitrary** integrand `g` the box integral is the corresponding product integral:

    ∫_{abox (n+1) s} g = ∫_{acube s × abox n s} g ∘ kcInsN .

No regularity, integrability or slot-independence of `g` is assumed: the identity is the
"junk-value compatible" change of variables `MeasureTheory.MeasurePreserving.integral_comp'`
(applied to the restriction of `kcInsN` to the preimage box), which needs neither.
-/

namespace Work.BoseBoxFock.PCFU

theorem peel_abox_integral {n : ℕ} {s : ℝ} (hs : 0 < s) (i : Fin (n + 1))
    (g : Submission.BoseGases.X (n + 1) → ℝ) :
    (∫ x in Submission.BoseGases.abox (n + 1) s, g x)
      = ∫ p : Submission.BoseGases.kcE3 × Submission.BoseGases.X n,
          g (Submission.BoseGases.kcInsN n i p)
          ∂((MeasureTheory.volume.restrict (Submission.BoseGases.acube s)).prod
            (MeasureTheory.volume.restrict (Submission.BoseGases.abox n s))) := by
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
  -- The restriction of the measure-preserving equivalence to the preimage box.
  have h1 := (Submission.BoseGases.kc_mp_insN n i).restrict_preimage_emb
      (Submission.BoseGases.kcInsN n i).measurableEmbedding (Submission.BoseGases.abox (n + 1) s)
  rw [hpre, hvol] at h1
  -- Change of variables (no integrability hypothesis needed).
  exact (h1.integral_comp' g).symm

end Work.BoseBoxFock.PCFU
