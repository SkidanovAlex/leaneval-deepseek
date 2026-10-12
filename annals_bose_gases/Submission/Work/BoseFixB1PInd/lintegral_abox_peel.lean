import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPIndFlat
import Submission.Work.BoseFixB1S.BoxQIndCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Peeling one position slot out of the centred box, `lintegral` form

`Submission.BoseGases.kcInsN n i : kcE3 × X n ≃ᵐ X (n+1)` inserts a one-particle position into
the `i`-th slot of an `n`-particle configuration, and is measure preserving.  Its preimage of the
centred `(n+1)`-particle box is the product of the one-particle centred cube with the `n`-particle
box,

  `(kcInsN n i) ⁻¹' abox (n+1) ℓ = acube ℓ ×ˢ abox n ℓ`,

so for any measurable `g` on the `(n+1)`-particle box,

  `∫⁻ x in abox (n+1) ℓ, g x = ∫⁻ q, g (kcInsN n i q) ∂ (volume↾acube ℓ).prod (volume↾abox n ℓ)`.

This is the `lintegral` companion of `Work.SmallBoxBridge.Fourier.peel_slot_abox` (which handles
the normalized real-valued integral with a slot-independent integrand).
-/

namespace Work.BoseFixB1PInd

open MeasureTheory
open scoped ENNReal

theorem lintegral_abox_peel {n : ℕ} {ℓ : ℝ} (i : Fin (n + 1)) {g : Submission.BoseGases.X (n + 1) → ENNReal}
    (hg : Measurable g) :
    ∫⁻ x in Submission.BoseGases.abox (n + 1) ℓ, g x =
      ∫⁻ q : Submission.BoseGases.kcE3 × Submission.BoseGases.X n,
          g ((Submission.BoseGases.kcInsN n i) q) ∂
        (((MeasureTheory.volume : MeasureTheory.Measure Submission.BoseGases.kcE3).restrict
            (Submission.BoseGases.acube ℓ)).prod
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ))) := by
  -- The `kcInsN`-preimage of the `(n+1)`-particle box is the product box.
  have hpre : (Submission.BoseGases.kcInsN n i) ⁻¹' (Submission.BoseGases.abox (n + 1) ℓ)
      = Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.abox n ℓ := by
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
        (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.abox n ℓ)
      = (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) := by
    rw [MeasureTheory.Measure.volume_eq_prod (Submission.BoseGases.kcE3) (Submission.BoseGases.X n),
      ← MeasureTheory.Measure.prod_restrict]
  -- Measure preservation of `kcInsN` on the peeled restrictions.
  have hmp : MeasureTheory.MeasurePreserving (⇑(Submission.BoseGases.kcInsN n i))
      ((MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (n + 1))).restrict
        (Submission.BoseGases.abox (n + 1) ℓ)) := by
    have h1 := (Submission.BoseGases.kc_mp_insN n i).restrict_preimage_emb
      (Submission.BoseGases.kcInsN n i).measurableEmbedding (Submission.BoseGases.abox (n + 1) ℓ)
    rw [hpre, hvol] at h1
    exact h1
  -- Change of variables for the Lebesgue integral of `g` against the restricted measures.
  exact (hmp.lintegral_comp hg).symm

end Work.BoseFixB1PInd
