import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.LatticeParsevalDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatticeParsevalGram` — the Gram matrix of the lattice characters

The characters `labChar ℓ N k x = e^{i⟪kmomLab ℓ N k, x⟫}` of the box lattice
`(2π/ℓ)ℤ³` restricted to the cube `Lab N` are orthogonal on the box
`boxL ℓ = {y | ∀ i, |y i| ≤ ℓ/2}`, with weight the volume `ℓ³`:

`∫_{boxL ℓ} labChar k · conj(labChar k') = ℓ³ · δ_{k,k'}`.

Proof: the product is the character of the difference momentum
(`Complex.exp_add`), which is additive in the integer labels
(`kmomLab_sub`), and the integral of a box character vanishes unless the label
is zero (`box_exp_orthogonal`); finally `labVec` is injective (`labVec_injective`).
-/

namespace Work.BoseFixR

theorem LatticeParsevalGram {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (k k' : Work.BoseBoxFock.Lab N) :
    ∫ x in Work.BoseFixR.boxL ℓ,
        Work.BoseFixR.labChar ℓ N k x * star (Work.BoseFixR.labChar ℓ N k' x)
      = if k = k' then ((ℓ : ℂ) ^ 3) else 0 := by
  -- the product of the two characters is the character of the difference of the momenta
  have hpt : ∀ x : EuclideanSpace ℝ (Fin 3),
      Work.BoseFixR.labChar ℓ N k x * star (Work.BoseFixR.labChar ℓ N k' x)
      = Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k
          - Work.BoseBoxFock.kmomLab ℓ N k') x : ℂ)) := by
    intro x
    rw [Work.BoseFixR.labChar_apply, Work.BoseFixR.labChar_apply, Complex.star_def,
      ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    rw [inner_sub_left]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_sub]
    ring
  rw [MeasureTheory.setIntegral_congr_fun (Work.BoseFixR.measurableSet_boxL ℓ)
    (fun x _ => hpt x)]
  rw [show Work.BoseFixR.boxL ℓ
      = {y : EuclideanSpace ℝ (Fin 3) | ∀ i, |y i| ≤ ℓ / 2} from rfl]
  rw [Work.BoseFixR.kmomLab_sub ℓ N k k']
  rw [Work.BoseFixR.box_exp_orthogonal hℓ
    (Work.BoseBoxFock.labVec N k - Work.BoseBoxFock.labVec N k')]
  by_cases hkk : k = k'
  · subst hkk; simp
  · rw [if_neg hkk,
      if_neg fun hm => hkk (Work.BoseFixR.labVec_injective N (sub_eq_zero.mp hm))]

end Work.BoseFixR
