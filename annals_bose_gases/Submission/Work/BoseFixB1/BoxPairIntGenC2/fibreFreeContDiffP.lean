import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxPairIntGenC2.Defs
import Submission.Work.BoseFixB1.contDiff_setIntegral_subset_isCompact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.BoxPairIntGenC2

open MeasureTheory
open scoped ContDiff Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Smoothness of the slot mean `x ↦ volA⁻¹ ∫_{A} Ψ (x with slot `i` replaced by `z`)` for a
smooth `Ψ` and a measurable `A` contained in a compact set `K`. -/
lemma contDiff_boxIndMean_of_subset {M : ℕ} {volA : ℝ} {A : Set E3}
    (hA : MeasurableSet A) {K : Set E3} (hK : IsCompact K) (hAK : A ⊆ K)
    (i : Fin M) {Ψ : Submission.BoseGases.X M → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB1.boxIndMean volA A i Ψ) := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (fun x : Submission.BoseGases.X M =>
      fun y : E3 => Ψ (Function.update x i y))) := by
    simpa only [Function.uncurry_def, Function.comp_def] using
      hΨ.comp (Submission.BoseGases.contDiff_update_coord i)
  have h := Work.BoseFixB1.contDiff_setIntegral_subset_isCompact (n := ⊤) hA hK hAK hF
  have hgoal : Work.BoseFixB1.boxIndMean volA A i Ψ
      = fun x : Submission.BoseGases.X M => (1 / volA) * ∫ y in A, Ψ (Function.update x i y) := by
    funext x
    rfl
  rw [hgoal]
  simpa only [smul_eq_mul] using h.const_smul (1 / volA)

theorem fibreFreeContDiffP {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (i : Fin (N + 2)) (j' : Fin (N + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (fun y z : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseFixB1.BoxPairIntGenC2.boxPairFibreFree volA ℓ A Φ i j' y z)) := by
  have hK : IsCompact (Submission.BoseGases.acube ℓ) := Submission.BoseGases.acube_compact hℓ
  have hMi : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB1.boxIndMean volA A i Φ) :=
    contDiff_boxIndMean_of_subset hA hK hAc i hΦ
  have hMj : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB1.boxIndMean volA A (i.succAbove j') Φ) :=
    contDiff_boxIndMean_of_subset hA hK hAc (i.succAbove j') hΦ
  have hMij : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB1.boxIndMean volA A i
      (Work.BoseFixB1.boxIndMean volA A (i.succAbove j') Φ)) :=
    contDiff_boxIndMean_of_subset hA hK hAc i hMj
  have hMji : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB1.boxIndMean volA A (i.succAbove j')
      (Work.BoseFixB1.boxIndMean volA A i Φ)) :=
    contDiff_boxIndMean_of_subset hA hK hAc (i.succAbove j') hMi
  have hins2 : ContDiff ℝ (⊤ : ℕ∞) (fun q : (E3 × E3) × Submission.BoseGases.X N =>
      Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2) := Submission.BoseGases.contDiff_ins2 i j'
  have hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (fun (q : E3 × E3)
      (r2 : Submission.BoseGases.X N) =>
        Work.BoseFixB1.boxIndMean volA A i (Work.BoseFixB1.boxIndMean volA A (i.succAbove j') Φ)
            (Submission.BoseGases.ins2 i j' q.1 q.2 r2)
          * (Φ (Submission.BoseGases.ins2 i j' q.1 q.2 r2)
              - Work.BoseFixB1.boxIndMean volA A (i.succAbove j') Φ
                  (Submission.BoseGases.ins2 i j' q.1 q.2 r2)
              - Work.BoseFixB1.boxIndMean volA A i Φ
                  (Submission.BoseGases.ins2 i j' q.1 q.2 r2)
              + Work.BoseFixB1.boxIndMean volA A (i.succAbove j')
                  (Work.BoseFixB1.boxIndMean volA A i Φ)
                  (Submission.BoseGases.ins2 i j' q.1 q.2 r2)))) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun q : (E3 × E3) × Submission.BoseGases.X N =>
        Work.BoseFixB1.boxIndMean volA A i (Work.BoseFixB1.boxIndMean volA A (i.succAbove j') Φ)
          (Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2)) := hMij.comp hins2
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun q : (E3 × E3) × Submission.BoseGases.X N =>
        Φ (Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2)
          - Work.BoseFixB1.boxIndMean volA A (i.succAbove j') Φ
              (Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2)
          - Work.BoseFixB1.boxIndMean volA A i Φ
              (Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2)
          + Work.BoseFixB1.boxIndMean volA A (i.succAbove j') (Work.BoseFixB1.boxIndMean volA A i Φ)
              (Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2)) :=
      (((hΦ.comp hins2).sub (hMj.comp hins2)).sub (hMi.comp hins2)).add (hMji.comp hins2)
    simpa only [Function.uncurry_def] using h1.mul h2
  have hmain : ContDiff ℝ (⊤ : ℕ∞) (fun q : E3 × E3 =>
      ∫ r2 in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1.boxIndMean volA A i (Work.BoseFixB1.boxIndMean volA A (i.succAbove j') Φ)
            (Submission.BoseGases.ins2 i j' q.1 q.2 r2)
          * (Φ (Submission.BoseGases.ins2 i j' q.1 q.2 r2)
              - Work.BoseFixB1.boxIndMean volA A (i.succAbove j') Φ
                  (Submission.BoseGases.ins2 i j' q.1 q.2 r2)
              - Work.BoseFixB1.boxIndMean volA A i Φ
                  (Submission.BoseGases.ins2 i j' q.1 q.2 r2)
              + Work.BoseFixB1.boxIndMean volA A (i.succAbove j')
                  (Work.BoseFixB1.boxIndMean volA A i Φ)
                  (Submission.BoseGases.ins2 i j' q.1 q.2 r2))) :=
    Commons.Analysis.Calculus.contDiff_setIntegral_isCompact_pi (d := N) (m := ⊤)
      (Submission.BoseGases.abox_compact N hℓ) hG
  have hgoal : (Function.uncurry (fun y z : E3 =>
      Work.BoseFixB1.BoxPairIntGenC2.boxPairFibreFree volA ℓ A Φ i j' y z))
      = fun q : E3 × E3 =>
          ∫ r2 in Submission.BoseGases.abox N ℓ,
            Work.BoseFixB1.boxIndMean volA A i
                (Work.BoseFixB1.boxIndMean volA A (i.succAbove j') Φ)
                (Submission.BoseGases.ins2 i j' q.1 q.2 r2)
              * (Φ (Submission.BoseGases.ins2 i j' q.1 q.2 r2)
                  - Work.BoseFixB1.boxIndMean volA A (i.succAbove j') Φ
                      (Submission.BoseGases.ins2 i j' q.1 q.2 r2)
                  - Work.BoseFixB1.boxIndMean volA A i Φ
                      (Submission.BoseGases.ins2 i j' q.1 q.2 r2)
                  + Work.BoseFixB1.boxIndMean volA A (i.succAbove j')
                      (Work.BoseFixB1.boxIndMean volA A i Φ)
                      (Submission.BoseGases.ins2 i j' q.1 q.2 r2)) := by
    funext q
    simp only [Function.uncurry_def, Work.BoseFixB1.BoxPairIntGenC2.boxPairFibreFree]
  rw [hgoal]
  exact hmain

end Work.BoseFixB1.BoxPairIntGenC2
