import Mathlib
import Submission.Work.Whitney.ArcFraming
import Submission.Work.Whitney.exists_isArcChain
import Submission.Work.Whitney.exists_addDoublePoint_both_signs_chart_like
import Submission.Work.Whitney.pairDet_ne_zero_iff
import Submission.Work.Whitney.SignCompare

/-!
# `OppositeType` from an insertion of an opposite-signed double point

The Whitney cancellation needs, for a *pair of arcs* `γ₁ : p₁ → p'`, `γ₂ : p₂ → q'` and two
immersions `fp`, `fm` that agree with a common `f` near the pre-existing double point `(p₁, p₂)` of
`f` and whose inserted double point `(p', q')` has *opposite* nonzero signs in one chart `c`, the
conclusion that one of `fp`, `fm` makes the two double points `(p₁,p₂)` and `(p',q')` have opposite
type along the pair of arcs.

The proof is a sign count.

* Along `γ₁` (from `p₁` to `p'`) and `γ₂` (from `p₂` to `q'`) the two arcs are covered by chart
  chains ending in the *same* chart `c` containing both `p'` and `q'`
  (`Work.Whitney.exists_isArcChain`); the starting charts `c₁`, `c₂` of the two chains then contain
  `p₁`, `p₂`.
* The factor `pairDet fp c₁ c₂ p₁ p₂` (resp. `pairDet fm c₁ c₂ p₁ p₂`) only sees the germ of `fp`
  (resp. `fm`) at `p₁, p₂` (`Work.Whitney.pairDet_congr`), so both equal `pairDet f c₁ c₂ p₁ p₂`,
  which is nonzero by transversality of `f` at `(p₁, p₂)` (`Work.Whitney.pairDet_ne_zero_iff` and
  the hypothesis `hspan`).
* The factor at `(p', q')` is read in the single chart `c`, so it is `doubleDetC fp c p' q'` resp.
  `doubleDetC fm c p' q' = - doubleDetC fp c p' q'`.

Since both factors at `(p₁,p₂)` and at `(p',q')` are nonzero for `fp`, the product for `fp` is either
negative — and then `fp` witnesses `OppositeType` — or positive, in which case the sign flip
`hsign` makes the product for `fm` negative. -/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology Filter

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- The starting point `γ 0` of an arc chain `γ` from `c` to `c'` lies in `c.source`. -/
theorem isArcChain_zero_mem {γ : ℝ → M}
    {c c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (h : IsArcChain γ c c') : γ 0 ∈ c.source := by
  obtain ⟨N, hN, d, t, ht0, ht1, hmono, hd0, hdN, hg0, hg1, hsm, hsub, hpos⟩ := h
  exact hg0

theorem exists_oppositeType_of_insertion {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f fp fm : M → EuclideanSpace ℝ (Fin (2 * n))}
    {p₁ p₂ p' q' : M} {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {γ₁ γ₂ : ℝ → M}
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hfpS : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) fp)
    (hfmS : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) fm)
    (hγ₁ : Continuous γ₁) (hγ₂ : Continuous γ₂)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = p') (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q')
    (hc : Work.Whitney.IsSmoothChart c) (hp'c : p' ∈ c.source) (hq'c : q' ∈ c.source)
    (hp₁p₂ : p₁ ≠ p₂) (hp'q' : p' ≠ q')
    (hfp' : fp p' = fp q') (hfm' : fm p' = fm q')
    (heq₁ : fp =ᶠ[nhds p₁] f) (heq₂ : fp =ᶠ[nhds p₂] f)
    (heq₁' : fm =ᶠ[nhds p₁] f) (heq₂' : fm =ᶠ[nhds p₂] f)
    (hspan : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).range = ⊤)
    (hdet : Work.Whitney.doubleDetC fp c p' q' ≠ 0)
    (hsign : Work.Whitney.doubleDetC fm c p' q' = - Work.Whitney.doubleDetC fp c p' q') :
    Work.Whitney.OppositeType fp γ₁ γ₂ p₁ p₂ p' q' ∨
      Work.Whitney.OppositeType fm γ₁ γ₂ p₁ p₂ p' q' := by
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  -- Chart chains along `γ₁` and `γ₂`, both ending in the insertion chart `c`.
  have hγ₁c : γ₁ 1 ∈ c.source := by rw [hγ₁1]; exact hp'c
  have hγ₂c : γ₂ 1 ∈ c.source := by rw [hγ₂1]; exact hq'c
  obtain ⟨c₁, hc₁sm, hch₁⟩ := exists_isArcChain γ₁ hγ₁ c hc hγ₁c
  obtain ⟨c₂, hc₂sm, hch₂⟩ := exists_isArcChain γ₂ hγ₂ c hc hγ₂c
  have hp₁c₁ : p₁ ∈ c₁.source := by rw [← hγ₁0]; exact isArcChain_zero_mem hch₁
  have hp₂c₂ : p₂ ∈ c₂.source := by rw [← hγ₂0]; exact isArcChain_zero_mem hch₂
  -- Smoothness of the four charts and their inverses at the relevant points.
  have hc₁md : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c₁ p₁ :=
    (hc₁sm.1.contMDiffAt (c₁.open_source.mem_nhds hp₁c₁)).mdifferentiableAt htop
  have hc₂md : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c₂ p₂ :=
    (hc₂sm.1.contMDiffAt (c₂.open_source.mem_nhds hp₂c₂)).mdifferentiableAt htop
  have hs₁md : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c₁.symm (c₁ p₁) :=
    (hc₁sm.2.contMDiffAt (c₁.open_target.mem_nhds (c₁.map_source hp₁c₁))).mdifferentiableAt htop
  have hs₂md : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c₂.symm (c₂ p₂) :=
    (hc₂sm.2.contMDiffAt (c₂.open_target.mem_nhds (c₂.map_source hp₂c₂))).mdifferentiableAt htop
  have hf₁md : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁ := hf.mdifferentiableAt htop
  have hf₂md : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂ := hf.mdifferentiableAt htop
  -- The determinant at the pre-existing double point is nonzero, and only sees the germ of `f`.
  have hAne : pairDet f c₁ c₂ p₁ p₂ ≠ 0 :=
    (pairDet_ne_zero_iff f c₁ c₂ p₁ p₂ hp₁c₁ hp₂c₂
      hc₁md hc₂md hs₁md hs₂md hf₁md hf₂md).mpr hspan
  have e1 : pairDet fp c₁ c₂ p₁ p₂ = pairDet f c₁ c₂ p₁ p₂ :=
    pairDet_congr c₁ c₂ p₁ p₂ hp₁c₁ hp₂c₂ heq₁ heq₂
  have e2 : pairDet fm c₁ c₂ p₁ p₂ = pairDet f c₁ c₂ p₁ p₂ :=
    pairDet_congr c₁ c₂ p₁ p₂ hp₁c₁ hp₂c₂ heq₁' heq₂'
  -- Exactly one of the two products is negative.
  rcases lt_or_gt_of_ne (mul_ne_zero hAne hdet) with h | h
  · left
    unfold OppositeType
    exact ⟨hγ₁0, hγ₁1, hγ₂0, hγ₂1, c₁, c₂, c, c, hp₁c₁, hp₂c₂, hp'c, hq'c, hch₁, hch₂,
      by rw [e1, pairDet_self]; exact h⟩
  · right
    unfold OppositeType
    exact ⟨hγ₁0, hγ₁1, hγ₂0, hγ₂1, c₁, c₂, c, c, hp₁c₁, hp₂c₂, hp'c, hq'c, hch₁, hch₂,
      by rw [e2, pairDet_self, hsign, mul_neg]; linarith⟩

end Work.Whitney
