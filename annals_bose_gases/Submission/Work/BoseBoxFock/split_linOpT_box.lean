import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseBoxFock.KzOpC
import Submission.Work.BoseBoxFock.split_sandwiches
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.split_linOpT_box` — the dictionary at FS's linear term `𝒬₁^ex`

`Work.BoseB7A.TildeData.linOpT` (FS's linear word `ρ_z z Ŵ₁ω(0) Σ_s χ̂²(sℓ)(ã_s†+ã_s)`)
is the weighted sum `c • Σ_{s∈excited} χ̂²_s • (ã_s† + ã_s)` of the one-body words
`ã_s†`, `ã_s`; its spectator form `Work.BoseBoxFock.linOpTC` (the `𝒬₁^ex` of
FS `eq:Kz`) is the same weighted sum with `ã_s ↦ annOfE (g s)`, `ã_s† ↦ creOfE (g s)`.

Every word of `linOpT` decomposes as `monoOp 0 0`-free one-body pieces, so the
dictionary transports it *pointwise*: the hypothesis `hTa`/`hTaDag` on the single
modes (`split∘ã_s = lift(a_s^C)∘split`) is lifted to the whole sum by
`ss_lift_weighted`, and the outer real scalar `c = ρ z Ŵ₁ω(0)` is pushed through
`split` (real linearity) and `lift` (`lift_smul`, with `r • z = (r:ℂ) • z` the
`RCLike.real_smul_eq_coe_smul` bridge on the ℂ-module).

Assembly note (the corpus's instance trap): the operators `T.ta s` live on
`F.H = (boxFockData …).H`, a field of the `FockData` structure, which is only
*definitionally* `RealFock m`; `rw`-matching refuses to unify the two at its
transparency level, so every arithmetic step below is stated as an explicit
`have`/`calc` step proved with `exact`-style terms (`LinearMap.add_apply`,
`map_add`, `map_smul`, `LinearMap.smul_apply`) rather than by rewriting with the
generic patterns.
-/

namespace Work.BoseBoxFock

open Work.BoseB4

theorem split_linOpT_box {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (B : Work.BoseB4.BoxData) {ℓ : ℝ} (kmom : Mode → EuclideanSpace ℝ (Fin 3))
    (hkmom : ∀ i : Mode, kmom (-i) = -kmom i) (f g : Mode → Fin m → ℝ)
    (hf : ∀ i j : Mode, Work.BoseB4.gram (f i) (f j)
      = Work.BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j))
    (T : Work.BoseB7A.TildeData (Work.BoseB4.boxFockData B kmom hkmom m f hf))
    (hTa : ∀ s : Mode, s ≠ 0 → ∀ y : Work.BoseB4.RealFock m,
      Work.BoseB4.split (T.ta s y) = Work.BoseB4.lift (Work.BoseBoxFock.annOfE (g s)) (Work.BoseB4.split y))
    (hTaDag : ∀ s : Mode, s ≠ 0 → ∀ y : Work.BoseB4.RealFock m,
      Work.BoseB4.split (T.taDag s y) = Work.BoseB4.lift (Work.BoseBoxFock.creOfE (g s)) (Work.BoseB4.split y))
    (E : Work.BoseB7.Q3Env Mode) :
    ∀ y : Work.BoseB4.RealFock m,
      Work.BoseB4.split (T.linOpT E y)
        = Work.BoseB4.lift (Work.BoseBoxFock.linOpTC g E) (Work.BoseB4.split y) := by
  intro y
  -- Step 1: the dictionary for the one-body words `ã_s† + ã_s`, for `s ≠ 0`.
  have hbase : ∀ s ∈ Work.BoseB7.excited Mode, ∀ y : Work.BoseB4.RealFock m,
      Work.BoseB4.split ((T.taDag s + T.ta s) y)
        = Work.BoseB4.lift (Work.BoseBoxFock.creOfE (g s) + Work.BoseBoxFock.annOfE (g s))
            (Work.BoseB4.split y) := by
    intro s hs y
    have hs0 : s ≠ 0 := (Finset.mem_erase.mp hs).1
    have hadd : (T.taDag s + T.ta s) y = T.taDag s y + T.ta s y := LinearMap.add_apply _ _ _
    have hsplit : Work.BoseB4.split (T.taDag s y + T.ta s y)
        = Work.BoseB4.split (T.taDag s y) + Work.BoseB4.split (T.ta s y) := map_add _ _ _
    have hl : Work.BoseB4.lift (Work.BoseBoxFock.creOfE (g s) + Work.BoseBoxFock.annOfE (g s))
          (Work.BoseB4.split y)
        = Work.BoseB4.lift (Work.BoseBoxFock.creOfE (g s)) (Work.BoseB4.split y)
          + Work.BoseB4.lift (Work.BoseBoxFock.annOfE (g s)) (Work.BoseB4.split y) :=
      (congrArg (fun f => f (Work.BoseB4.split y))
        (Work.BoseB4.lift_add (Work.BoseBoxFock.creOfE (g s))
          (Work.BoseBoxFock.annOfE (g s)))).trans
      (LinearMap.add_apply _ _ _)
    calc Work.BoseB4.split ((T.taDag s + T.ta s) y)
        = Work.BoseB4.split (T.taDag s y + T.ta s y) := congrArg _ hadd
      _ = Work.BoseB4.split (T.taDag s y) + Work.BoseB4.split (T.ta s y) := hsplit
      _ = Work.BoseB4.lift (Work.BoseBoxFock.creOfE (g s)) (Work.BoseB4.split y)
            + Work.BoseB4.lift (Work.BoseBoxFock.annOfE (g s)) (Work.BoseB4.split y) := by
          rw [hTaDag s hs0 y, hTa s hs0 y]
      _ = Work.BoseB4.lift (Work.BoseBoxFock.creOfE (g s) + Work.BoseBoxFock.annOfE (g s))
            (Work.BoseB4.split y) := hl.symm
  -- Step 2: the weighted sum, by `ss_lift_weighted`.
  have hsum := Work.BoseBoxFock.ss_lift_weighted (m := m) (s := Work.BoseB7.excited Mode)
      (c := fun s => E.hatChiSq s)
      (A := fun s => T.taDag s + T.ta s)
      (B := fun s => Work.BoseBoxFock.creOfE (g s) + Work.BoseBoxFock.annOfE (g s)) hbase y
  -- Step 3: pull out the outer scalar `ρ z Ŵ₁ω(0)`.
  have hsmul : T.linOpT E y = (E.rho * E.z * E.W1omega0) •
      ((∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s • (T.taDag s + T.ta s)) y) :=
    LinearMap.smul_apply _ _ _
  have hmap : Work.BoseB4.split ((E.rho * E.z * E.W1omega0) •
      ((∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s • (T.taDag s + T.ta s)) y))
      = (E.rho * E.z * E.W1omega0) •
        Work.BoseB4.split ((∑ s ∈ Work.BoseB7.excited Mode,
          E.hatChiSq s • (T.taDag s + T.ta s)) y) :=
    map_smul _ _ _
  have hlinC : Work.BoseBoxFock.linOpTC g E
      = ((E.rho * E.z * E.W1omega0 : ℝ) : ℂ) •
        ∑ s ∈ Work.BoseB7.excited Mode, ((E.hatChiSq s : ℝ) : ℂ) •
          (Work.BoseBoxFock.creOfE (g s) + Work.BoseBoxFock.annOfE (g s)) := rfl
  calc Work.BoseB4.split (T.linOpT E y)
      = Work.BoseB4.split ((E.rho * E.z * E.W1omega0) •
          ((∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s • (T.taDag s + T.ta s)) y)) :=
        congrArg Work.BoseB4.split hsmul
    _ = (E.rho * E.z * E.W1omega0) •
          (Work.BoseB4.split ((∑ s ∈ Work.BoseB7.excited Mode,
            E.hatChiSq s • (T.taDag s + T.ta s)) y)) := hmap
    _ = (E.rho * E.z * E.W1omega0) •
          (Work.BoseB4.lift (∑ s ∈ Work.BoseB7.excited Mode,
            ((E.hatChiSq s : ℝ) : ℂ) •
            (Work.BoseBoxFock.creOfE (g s) + Work.BoseBoxFock.annOfE (g s)))
              (Work.BoseB4.split y)) :=
        congrArg (fun z => (E.rho * E.z * E.W1omega0) • z) hsum
    _ = ((E.rho * E.z * E.W1omega0 : ℝ) : ℂ) •
          (Work.BoseB4.lift (∑ s ∈ Work.BoseB7.excited Mode,
            ((E.hatChiSq s : ℝ) : ℂ) •
            (Work.BoseBoxFock.creOfE (g s) + Work.BoseBoxFock.annOfE (g s)))
              (Work.BoseB4.split y)) :=
        RCLike.real_smul_eq_coe_smul (K := ℂ) _ _
    _ = (((E.rho * E.z * E.W1omega0 : ℝ) : ℂ) •
          (Work.BoseB4.lift (∑ s ∈ Work.BoseB7.excited Mode,
            ((E.hatChiSq s : ℝ) : ℂ) •
            (Work.BoseBoxFock.creOfE (g s) + Work.BoseBoxFock.annOfE (g s)))))
              (Work.BoseB4.split y) :=
        (LinearMap.smul_apply _ _ _).symm
    _ = (Work.BoseB4.lift (((E.rho * E.z * E.W1omega0 : ℝ) : ℂ) •
          (∑ s ∈ Work.BoseB7.excited Mode, ((E.hatChiSq s : ℝ) : ℂ) •
            (Work.BoseBoxFock.creOfE (g s) + Work.BoseBoxFock.annOfE (g s)))))
              (Work.BoseB4.split y) :=
        congrArg (fun f => f (Work.BoseB4.split y)) (Work.BoseB4.lift_smul _ _).symm
    _ = Work.BoseB4.lift (Work.BoseBoxFock.linOpTC g E) (Work.BoseB4.split y) := by
        rw [hlinC]

end Work.BoseBoxFock
