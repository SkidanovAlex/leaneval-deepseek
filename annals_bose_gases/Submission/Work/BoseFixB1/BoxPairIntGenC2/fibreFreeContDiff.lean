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

/-!
# `Work.BoseFixB1.BoxPairIntGenC2.fibreFreeContDiff`

The indicator-free peeled box pair fibre `boxPairFibreFree volA ℓ A Φ i j'` is a parametric
integral over the compact box `abox N ℓ` of a function which is jointly smooth in the two
distinguished coordinates `(y,z)` and in the box variable `r2`; hence it is smooth in `(y,z)`.

The joint smoothness of the integrand is reduced to the smoothness of the *slot mean*
`boxIndMean volA A k` (Lemma `contDiff_boxIndMean_priv` below, an instance of the corpus's
`Work.BoseFixB1.contDiff_setIntegral_subset_isCompact`) composed with the double insertion
`ins2` (`Submission.BoseGases.contDiff_ins2`), and then the `r2`-integral is differentiated
under the integral sign with `Commons.Analysis.Calculus.contDiff_setIntegral_isCompact_pi`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1.BoxPairIntGenC2

set_option autoImplicit false

/-- **Smoothness of the slot mean.**  For `A` a measurable subset of a compact set `K`, the slot
mean `boxIndMean volA A i Ψ` of a smooth `Ψ` is smooth.  (The constant `volA` is irrelevant; the
mean is the parametric integral `(1/volA)∫_{z∈A} Ψ(·[i := z])` over the bounded region `A ⊆ K`.) -/
private lemma contDiff_boxIndMean_priv {M : ℕ} {K : Set (EuclideanSpace ℝ (Fin 3))} {volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hK : IsCompact K) (hAK : A ⊆ K)
    (i : Fin M) {Ψ : Submission.BoseGases.X M → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB1.boxIndMean volA A i Ψ) := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry
      (fun (x : Submission.BoseGases.X M) (z : EuclideanSpace ℝ (Fin 3)) =>
        Ψ (Function.update x i z))) :=
    hΨ.comp (Submission.BoseGases.contDiff_update_coord i)
  have h := Work.BoseFixB1.contDiff_setIntegral_subset_isCompact
    (P := Submission.BoseGases.X M) (A := A) (K := K) (n := (⊤ : ℕ∞))
    (F := fun (x : Submission.BoseGases.X M) (z : EuclideanSpace ℝ (Fin 3)) =>
      Ψ (Function.update x i z)) hA hK hAK hF
  have hgoal : Work.BoseFixB1.boxIndMean volA A i Ψ
      = fun x => (1 / volA) • ∫ z in A, Ψ (Function.update x i z) := rfl
  rw [hgoal]
  exact h.const_smul (1 / volA)

theorem fibreFreeContDiff {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (i : Fin (N + 2)) (j' : Fin (N + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (fun y z : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseFixB1.BoxPairIntGenC2.boxPairFibreFree volA ℓ A Φ i j' y z)) := by
  have hK : IsCompact (Submission.BoseGases.acube ℓ) := Submission.BoseGases.acube_compact hℓ
  -- the five smooth slot functions
  have hMi : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB1.boxIndMean volA A i Φ) :=
    contDiff_boxIndMean_priv hA hK hAc i hΦ
  have hMj : ContDiff ℝ (⊤ : ℕ∞)
      (Work.BoseFixB1.boxIndMean volA A (i.succAbove j') Φ) :=
    contDiff_boxIndMean_priv hA hK hAc (i.succAbove j') hΦ
  have hMjMi : ContDiff ℝ (⊤ : ℕ∞)
      (Work.BoseFixB1.boxIndMean volA A (i.succAbove j')
        (Work.BoseFixB1.boxIndMean volA A i Φ)) :=
    contDiff_boxIndMean_priv hA hK hAc (i.succAbove j') hMi
  have hMiMj : ContDiff ℝ (⊤ : ℕ∞)
      (Work.BoseFixB1.boxIndMean volA A i
        (Work.BoseFixB1.boxIndMean volA A (i.succAbove j') Φ)) :=
    contDiff_boxIndMean_priv hA hK hAc i hMj
  -- the double insertion is smooth in all its variables
  have hpath : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) ×
          Submission.BoseGases.X N =>
        Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2) :=
    Submission.BoseGases.contDiff_ins2 i j'
  -- joint smoothness of the integrand
  have hint : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) ×
          Submission.BoseGases.X N =>
        Work.BoseFixB1.boxIndMean volA A i (Work.BoseFixB1.boxIndMean volA A (i.succAbove j') Φ)
            (Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2)
          * (Φ (Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2)
             - Work.BoseFixB1.boxIndMean volA A (i.succAbove j') Φ
                 (Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2)
             - Work.BoseFixB1.boxIndMean volA A i Φ
                 (Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2)
             + Work.BoseFixB1.boxIndMean volA A (i.succAbove j')
                 (Work.BoseFixB1.boxIndMean volA A i Φ)
                 (Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2))) :=
    (hMiMj.comp hpath).mul
      ((((hΦ.comp hpath).sub (hMj.comp hpath)).sub (hMi.comp hpath)).add
        (hMjMi.comp hpath))
  -- integration over the compact box `abox N ℓ`
  have hmain : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ∫ r2 in Submission.BoseGases.abox N ℓ,
          Work.BoseFixB1.boxIndMean volA A i
              (Work.BoseFixB1.boxIndMean volA A (i.succAbove j') Φ)
              (Submission.BoseGases.ins2 i j' p.1 p.2 r2)
            * (Φ (Submission.BoseGases.ins2 i j' p.1 p.2 r2)
               - Work.BoseFixB1.boxIndMean volA A (i.succAbove j') Φ
                   (Submission.BoseGases.ins2 i j' p.1 p.2 r2)
               - Work.BoseFixB1.boxIndMean volA A i Φ
                   (Submission.BoseGases.ins2 i j' p.1 p.2 r2)
               + Work.BoseFixB1.boxIndMean volA A (i.succAbove j')
                   (Work.BoseFixB1.boxIndMean volA A i Φ)
                   (Submission.BoseGases.ins2 i j' p.1 p.2 r2))) :=
    Commons.Analysis.Calculus.contDiff_setIntegral_isCompact_pi (d := N)
      (P := EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
      (k := Submission.BoseGases.abox N ℓ)
      (F := fun (p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
              (r2 : Submission.BoseGases.X N) =>
        Work.BoseFixB1.boxIndMean volA A i
            (Work.BoseFixB1.boxIndMean volA A (i.succAbove j') Φ)
            (Submission.BoseGases.ins2 i j' p.1 p.2 r2)
          * (Φ (Submission.BoseGases.ins2 i j' p.1 p.2 r2)
             - Work.BoseFixB1.boxIndMean volA A (i.succAbove j') Φ
                 (Submission.BoseGases.ins2 i j' p.1 p.2 r2)
             - Work.BoseFixB1.boxIndMean volA A i Φ
                 (Submission.BoseGases.ins2 i j' p.1 p.2 r2)
             + Work.BoseFixB1.boxIndMean volA A (i.succAbove j')
                 (Work.BoseFixB1.boxIndMean volA A i Φ)
                 (Submission.BoseGases.ins2 i j' p.1 p.2 r2)))
      (m := (⊤ : ℕ∞)) (Submission.BoseGases.abox_compact N hℓ) hint
  have hfun : Function.uncurry (fun y z : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixB1.BoxPairIntGenC2.boxPairFibreFree volA ℓ A Φ i j' y z)
      = fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          ∫ r2 in Submission.BoseGases.abox N ℓ,
            Work.BoseFixB1.boxIndMean volA A i
                (Work.BoseFixB1.boxIndMean volA A (i.succAbove j') Φ)
                (Submission.BoseGases.ins2 i j' p.1 p.2 r2)
              * (Φ (Submission.BoseGases.ins2 i j' p.1 p.2 r2)
                 - Work.BoseFixB1.boxIndMean volA A (i.succAbove j') Φ
                     (Submission.BoseGases.ins2 i j' p.1 p.2 r2)
                 - Work.BoseFixB1.boxIndMean volA A i Φ
                     (Submission.BoseGases.ins2 i j' p.1 p.2 r2)
                 + Work.BoseFixB1.boxIndMean volA A (i.succAbove j')
                     (Work.BoseFixB1.boxIndMean volA A i Φ)
                     (Submission.BoseGases.ins2 i j' p.1 p.2 r2)) := by
    funext p
    obtain ⟨y, z⟩ := p
    rfl
  rw [hfun]
  exact hmain

end Work.BoseFixB1.BoxPairIntGenC2
