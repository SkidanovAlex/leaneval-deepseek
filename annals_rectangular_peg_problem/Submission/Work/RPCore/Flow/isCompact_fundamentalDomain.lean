import Mathlib
import Submission.Work.RPV.Defs

open Real

namespace Work.RPCore.Flow

/-- The "fundamental domain" of the flow: in coordinates `z = (t, ((q₁,q₂),(p₁,p₂)))` it is the
closed set `{|t| ≤ B, |q₁|+|p₁|+|p₂| ≤ R, 0 ≤ q₂ ≤ 2π}`.  It is a closed subset of the compact box
`[-B,B] × ([-R,R] × [0,2π]) × ([-R,R] × [-R,R])`, hence compact. -/
theorem isCompact_fundamentalDomain (B R : ℝ) :
    IsCompact {z : ℝ × Work.RPV.PS |
      |z.1| ≤ B ∧ |z.2.1.1| + |z.2.2.1| + |z.2.2.2| ≤ R ∧ 0 ≤ z.2.1.2 ∧ z.2.1.2 ≤ 2 * π} := by
  -- The enclosing compact box.
  have hK : IsCompact (Set.Icc (-B) B ×ˢ
      ((Set.Icc (-R) R ×ˢ Set.Icc (0 : ℝ) (2 * π)) ×ˢ
        (Set.Icc (-R) R ×ˢ Set.Icc (-R) R)) : Set (ℝ × Work.RPV.PS)) := by
    exact (isCompact_Icc.prod ((isCompact_Icc.prod isCompact_Icc).prod
      (isCompact_Icc.prod isCompact_Icc)))
  refine hK.of_isClosed_subset ?hclosed ?hsub
  · -- Closedness: intersection of four closed coordinate conditions.
    have h1 : IsClosed {z : ℝ × Work.RPV.PS | |z.1| ≤ B} :=
      isClosed_le (continuous_abs.comp continuous_fst) continuous_const
    have h2 : IsClosed {z : ℝ × Work.RPV.PS |
        |z.2.1.1| + |z.2.2.1| + |z.2.2.2| ≤ R} :=
      isClosed_le (((continuous_snd.fst.fst).abs.add (continuous_snd.snd.fst).abs).add
        (continuous_snd.snd.snd).abs) continuous_const
    have h3 : IsClosed {z : ℝ × Work.RPV.PS | 0 ≤ z.2.1.2} :=
      isClosed_le continuous_const continuous_snd.fst.snd
    have h4 : IsClosed {z : ℝ × Work.RPV.PS | z.2.1.2 ≤ 2 * π} :=
      isClosed_le continuous_snd.fst.snd continuous_const
    convert h1.inter (h2.inter (h3.inter h4)) using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  · -- The set is contained in the box: the sum bound forces each coordinate bound.
    intro z hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    have hq1 : |z.2.1.1| ≤ R := by
      have a := abs_nonneg z.2.2.1; have b := abs_nonneg z.2.2.2; linarith
    have hp1 : |z.2.2.1| ≤ R := by
      have a := abs_nonneg z.2.1.1; have b := abs_nonneg z.2.2.2; linarith
    have hp2 : |z.2.2.2| ≤ R := by
      have a := abs_nonneg z.2.1.1; have b := abs_nonneg z.2.2.1; linarith
    refine Set.mem_prod.mpr ⟨Set.mem_Icc.mpr (abs_le.mp h1), ?_⟩
    refine Set.mem_prod.mpr ⟨Set.mem_prod.mpr ⟨Set.mem_Icc.mpr (abs_le.mp hq1),
      Set.mem_Icc.mpr ⟨h3, h4⟩⟩, ?_⟩
    exact Set.mem_prod.mpr ⟨Set.mem_Icc.mpr (abs_le.mp hp1), Set.mem_Icc.mpr (abs_le.mp hp2)⟩

end Work.RPCore.Flow
