import Mathlib
import Submission.Work.WilG4a.LipChartsDefs
import Submission.Work.WilG4a.ImgSetDefs
import Submission.Work.WilG4a.imgSet_mem_Omega
import Submission.Work.WilG4a.sInf_sSup_fibre_graph_mem_noStrip

namespace Work.WilG4a

theorem lipschitz_endpoints_junk (S : WilkiesDesign.SOMin) (p F0 Fκ : ℕ)
    (bκ : MvPolynomial (Fin 2) ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D : ℕ) (f : (Fin p → ℝ) → ℝ → ℝ) (κ : Set (Fin (p+1) → ℝ)),
        Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        κ ∈ S.Ω Fκ (MvPolynomial.eval ![D, 1] bκ) (p + 1) →
        WilkiesDesign.graphOf (Work.WilG4a.Aend κ f) ∈ S.Ω a (MvPolynomial.eval ![D, 1] b) (p + 1) ∧
        WilkiesDesign.graphOf (Work.WilG4a.Bend κ f) ∈ S.Ω a (MvPolynomial.eval ![D, 1] b) (p + 1) := by
  -- `Z = imgSet p κ f` is the `Ω`-set whose fibre over `l` is the image of the fibre of `κ`;
  -- its format/degree bound is affine in `D` and in `eval ![D,1] bκ`.
  obtain ⟨A, C, hA⟩ := imgSet_mem_Omega S p F0 Fκ bκ
  -- the pointwise infimum/supremum of the fibres of an `Ω`-set are `Ω`-definable, with a
  -- format depending on the input format `A` only and a degree affine in the input degree.
  obtain ⟨a, c, c', hB⟩ := sInf_sSup_fibre_graph_mem_noStrip S p A
  -- the degree polynomial: `eval ![D,1] b = c * (D + eval ![D,1] bκ + C) + c'`.
  refine ⟨a, MvPolynomial.C (c * C + c') + MvPolynomial.C c * MvPolynomial.X 0
    + MvPolynomial.C c * bκ, ?_⟩
  intro D f κ hf hκ
  have hZ : imgSet p κ f ∈ S.Ω A (D + MvPolynomial.eval ![D, 1] bκ + C) (p + 1) := hA D f κ hf hκ
  have hDeval :
      MvPolynomial.eval ![D, 1] (MvPolynomial.C (c * C + c') + MvPolynomial.C c * MvPolynomial.X 0
        + MvPolynomial.C c * bκ) = c * (D + MvPolynomial.eval ![D, 1] bκ + C) + c' := by
    simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X, Matrix.cons_val_zero]
    ring
  obtain ⟨hlo, hhi⟩ := hB (D + MvPolynomial.eval ![D, 1] bκ + C) (imgSet p κ f) hZ
  -- `Aend`/`Bend` are the infimum/supremum of the fibre of `imgSet p κ f`.
  have hAend : Aend κ f = fun l : Fin p → ℝ => sInf {x : ℝ | Fin.snoc l x ∈ imgSet p κ f} := by
    funext l
    show sInf (imgFibre κ f l) = sInf {x : ℝ | Fin.snoc l x ∈ imgSet p κ f}
    rw [imgFibre_eq]
  have hBend : Bend κ f = fun l : Fin p → ℝ => sSup {x : ℝ | Fin.snoc l x ∈ imgSet p κ f} := by
    funext l
    show sSup (imgFibre κ f l) = sSup {x : ℝ | Fin.snoc l x ∈ imgSet p κ f}
    rw [imgFibre_eq]
  constructor
  · rw [hAend, hDeval]; exact hlo
  · rw [hBend, hDeval]; exact hhi

end Work.WilG4a
