import Mathlib
import Submission.Work.ATOM.ZS.HFour.Defs
import Submission.Work.ANALYTIC.EA_shift

namespace Work.ATOM.ZS

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open OnePoint

noncomputable section

/-- `id × tProj : (ℕ∪∞) × T' ⟶ (ℕ∪∞) × (ℕ∪∞)`, as a map of light profinite sets. -/
private abbrev h4p (S : LightProfinite.{0}) [Infinite S] :
    (ℕ∪{∞}) ⊗ T' S ⟶ NS2 :=
  MonoidalCategory.whiskerLeft (ℕ∪{∞}) (tProj S)

/-- `shift × id` on `(ℕ∪∞) × (ℕ∪∞)`, as a map of light profinite sets. -/
private abbrev h4g : NS2 ⟶ NS2 :=
  MonoidalCategory.whiskerRight LightProfinite.shift (ℕ∪{∞})

/-- **The right hand side of `h₄` on the cover `(ℕ∪∞) × T'`**, with `hFourPull`, `hFourQ1` and
`hFourQ2` unfolded.  This is the form in which the proof is carried out. -/
private theorem hFour_RED_R_aux (S : LightProfinite.{0}) [Infinite S] :
    Work.ATOM.zmap (h4p S) ≫ Work.ATOM.EApp ≫ Work.ATOM.preShiftP ≫ Work.ATOM.FP S =
      (Work.ATOM.zmap (h4p S ≫ Work.ATOM.phiP S) -
        Work.ATOM.zmap (h4p S ≫ (h4g ≫ Work.ATOM.phiP S))) ≫
          LightCondensed.P_proj := by
  have hEA1 : Work.ATOM.EA (ℕ∪{∞}) ≫ (LightCondensed.P ◁ LightCondensed.P_proj) =
      Work.ATOM.EApp := by
    rw [Work.ATOM.EApp, Work.ATOM.EA, Category.assoc]
  have hEA : Work.ATOM.EApp ≫ Work.ATOM.preShiftP =
      (𝟙 (Work.ATOM.zfree NS2) - Work.ATOM.zmap (h4g)) ≫ Work.ATOM.EApp := by
    have hsh := Work.ANALYTIC.EA_shift (LightProfinite.NatUnionInfty)
    have hex := MonoidalCategory.whisker_exchange LightCondensed.oneMinusShift
      LightCondensed.P_proj
    calc Work.ATOM.EApp ≫ Work.ATOM.preShiftP
        = (Work.ATOM.EA (ℕ∪{∞}) ≫ (LightCondensed.P ◁ LightCondensed.P_proj)) ≫
            Work.ATOM.preShiftP := by rw [hEA1]
      _ = Work.ATOM.EA (ℕ∪{∞}) ≫
            ((LightCondensed.P ◁ LightCondensed.P_proj) ≫ Work.ATOM.preShiftP) :=
            Category.assoc _ _ _
      _ = Work.ATOM.EA (ℕ∪{∞}) ≫
            ((LightCondensed.oneMinusShift ▷ Work.ATOM.zfree (ℕ∪{∞})) ≫
              (LightCondensed.P ◁ LightCondensed.P_proj)) := by
            rw [show Work.ATOM.preShiftP =
              (LightCondensed.oneMinusShift ▷ LightCondensed.P) from rfl, hex]
      _ = (Work.ATOM.EA (ℕ∪{∞}) ≫
            (LightCondensed.oneMinusShift ▷ Work.ATOM.zfree (ℕ∪{∞}))) ≫
              (LightCondensed.P ◁ LightCondensed.P_proj) := (Category.assoc _ _ _).symm
      _ = ((𝟙 (Work.ATOM.zfree NS2) - Work.ATOM.zmap (h4g)) ≫
            Work.ATOM.EA (ℕ∪{∞})) ≫ (LightCondensed.P ◁ LightCondensed.P_proj) := by
            rw [hsh]
      _ = (𝟙 (Work.ATOM.zfree NS2) - Work.ATOM.zmap (h4g)) ≫
            (Work.ATOM.EA (ℕ∪{∞}) ≫ (LightCondensed.P ◁ LightCondensed.P_proj)) :=
            Category.assoc _ _ _
      _ = (𝟙 (Work.ATOM.zfree NS2) - Work.ATOM.zmap (h4g)) ≫ Work.ATOM.EApp := by
            rw [hEA1]
  have hA : ∀ {Y : LightCondAb}
      (c : Work.ATOM.tmul LightCondensed.P LightCondensed.P ⟶ Y),
      Work.ATOM.EApp ≫ Work.ATOM.preShiftP ≫ c =
        (𝟙 (Work.ATOM.zfree NS2) - Work.ATOM.zmap (h4g)) ≫ Work.ATOM.EApp ≫ c := by
    intro Y c
    calc Work.ATOM.EApp ≫ Work.ATOM.preShiftP ≫ c
        = (Work.ATOM.EApp ≫ Work.ATOM.preShiftP) ≫ c := (Category.assoc _ _ _).symm
      _ = ((𝟙 (Work.ATOM.zfree NS2) - Work.ATOM.zmap (h4g)) ≫ Work.ATOM.EApp) ≫
            c := by rw [hEA]
      _ = (𝟙 (Work.ATOM.zfree NS2) - Work.ATOM.zmap (h4g)) ≫
            Work.ATOM.EApp ≫ c := Category.assoc _ _ _
  have hFS : Work.ATOM.EApp ≫ Work.ATOM.FP S =
      Work.ATOM.zmap (Work.ATOM.phiP S) ≫ LightCondensed.P_proj := by
    rw [Work.ATOM.FP_spec, Work.ATOM.FPsection]
  have hB : ∀ {Y : LightCondAb}
      (c : Work.ATOM.zfree NS2 ⟶ Y),
      Work.ATOM.zmap (h4p S) ≫
          (𝟙 (Work.ATOM.zfree NS2) - Work.ATOM.zmap (h4g)) ≫ c =
        (Work.ATOM.zmap (h4p S) - Work.ATOM.zmap (h4p S ≫ h4g)) ≫ c := by
    intro Y c
    calc Work.ATOM.zmap (h4p S) ≫
          (𝟙 (Work.ATOM.zfree NS2) - Work.ATOM.zmap (h4g)) ≫ c
        = (Work.ATOM.zmap (h4p S) ≫
            (𝟙 (Work.ATOM.zfree NS2) - Work.ATOM.zmap (h4g))) ≫ c :=
            (Category.assoc _ _ _).symm
      _ = (Work.ATOM.zmap (h4p S) -
            Work.ATOM.zmap (h4p S) ≫ Work.ATOM.zmap (h4g)) ≫ c := by
            rw [Preadditive.comp_sub, Category.comp_id]
      _ = (Work.ATOM.zmap (h4p S) - Work.ATOM.zmap (h4p S ≫ h4g)) ≫ c := by
            rw [← zmap_comp (h4p S) h4g]
  have hC : (Work.ATOM.zmap (h4p S) - Work.ATOM.zmap (h4p S ≫ h4g)) ≫
        (Work.ATOM.zmap (Work.ATOM.phiP S) ≫ LightCondensed.P_proj) =
      (Work.ATOM.zmap (h4p S ≫ Work.ATOM.phiP S) -
        Work.ATOM.zmap (h4p S ≫ (h4g ≫ Work.ATOM.phiP S))) ≫
          LightCondensed.P_proj := by
    calc (Work.ATOM.zmap (h4p S) - Work.ATOM.zmap (h4p S ≫ h4g)) ≫
          (Work.ATOM.zmap (Work.ATOM.phiP S) ≫ LightCondensed.P_proj)
        = Work.ATOM.zmap (h4p S) ≫ (Work.ATOM.zmap (Work.ATOM.phiP S) ≫
              LightCondensed.P_proj) -
            Work.ATOM.zmap (h4p S ≫ h4g) ≫ (Work.ATOM.zmap (Work.ATOM.phiP S) ≫
              LightCondensed.P_proj) := Preadditive.sub_comp _ _ _
      _ = (Work.ATOM.zmap (h4p S) ≫ Work.ATOM.zmap (Work.ATOM.phiP S)) ≫
              LightCondensed.P_proj -
            (Work.ATOM.zmap (h4p S ≫ h4g) ≫ Work.ATOM.zmap (Work.ATOM.phiP S)) ≫
              LightCondensed.P_proj := by
            rw [← Category.assoc (Work.ATOM.zmap (h4p S))
                  (Work.ATOM.zmap (Work.ATOM.phiP S)) LightCondensed.P_proj,
                ← Category.assoc (Work.ATOM.zmap (h4p S ≫ h4g))
                  (Work.ATOM.zmap (Work.ATOM.phiP S)) LightCondensed.P_proj]
      _ = Work.ATOM.zmap (h4p S ≫ Work.ATOM.phiP S) ≫ LightCondensed.P_proj -
            Work.ATOM.zmap ((h4p S ≫ h4g) ≫ Work.ATOM.phiP S) ≫
              LightCondensed.P_proj := by
            rw [← zmap_comp (h4p S) (Work.ATOM.phiP S),
                ← zmap_comp (h4p S ≫ h4g) (Work.ATOM.phiP S)]
      _ = Work.ATOM.zmap (h4p S ≫ Work.ATOM.phiP S) ≫ LightCondensed.P_proj -
            Work.ATOM.zmap (h4p S ≫ (h4g ≫ Work.ATOM.phiP S)) ≫
              LightCondensed.P_proj := by
            rw [Category.assoc (h4p S) (h4g) (Work.ATOM.phiP S)]
      _ = (Work.ATOM.zmap (h4p S ≫ Work.ATOM.phiP S) -
            Work.ATOM.zmap (h4p S ≫ (h4g ≫ Work.ATOM.phiP S))) ≫
              LightCondensed.P_proj := (Preadditive.sub_comp _ _ _).symm
  rw [hA (Work.ATOM.FP S), hFS,
    hB (Work.ATOM.zmap (Work.ATOM.phiP S) ≫ LightCondensed.P_proj), hC]

/-- **The right hand side of `h₄` on the cover `(ℕ∪∞) × T'`.**

`Work.ATOM.ZS.hFourPull S : (ℕ∪∞) ⊗ T' S ⟶ NS2` is `id × tProj` (a surjection), so pulling the
`P ⊗ P`-identity `h₄` back to the cover `(ℕ∪∞) × T'` and cancelling `Work.ATOM.EApp` turns the
right hand side `Work.ATOM.preShiftP ≫ Work.ATOM.FP S = ((1-S) ⊗ id_P) ≫ F_P` into the
`zmap`-combination `(zmap hFourQ1 - zmap hFourQ2) ≫ P_proj`, where
`hFourQ1(k,t) = φ_P(k, tProj t)` and `hFourQ2(k,t) = φ_P(k+1, tProj t) = φ_P(shift k, tProj t)`.

Route (all steps are rewrites, no covers):
1. `EApp ≫ preShiftP = (𝟙 (zfree (ℕ∪∞ ⊗ ℕ∪∞)) - zmap (whiskerRight shift (ℕ∪∞))) ≫ EApp`
   — combine `Work.ANALYTIC.EA_shift (ℕ∪∞)` (which says
   `EA (ℕ∪∞) ≫ (oneMinusShift ▷ zfree (ℕ∪∞)) = (𝟙 _ - zmap (shift ▷ ℕ∪∞)) ≫ EA (ℕ∪∞)`) with
   `EApp = EA (ℕ∪∞) ≫ (P ◁ P_proj)` (definitional) and
   `MonoidalCategory.whisker_exchange oneMinusShift P_proj`, which gives
   `(P ◁ P_proj) ≫ (oneMinusShift ▷ P) = (oneMinusShift ▷ zfree (ℕ∪∞)) ≫ (P ◁ P_proj)`.
2. `zmap (hFourPull S) ≫ (𝟙 _ - zmap (whiskerRight shift (ℕ∪∞)))` is
   `zmap (hFourPull S) - zmap (hFourPull S ≫ whiskerRight shift (ℕ∪∞))`, using
   `Preadditive.comp_sub`, `Category.comp_id` and functoriality of `zmap`
   (`CategoryTheory.Functor.map_comp`).
3. `EApp ≫ FP S = zmap (phiP S) ≫ P_proj` (`Work.ATOM.FP_spec` and
   `Work.ATOM.FPsection = zmap (phiP S) ≫ P_proj`).
4. Distribute `(a - b) ≫ c = a ≫ c - b ≫ c` (`Preadditive.sub_comp`), combine the `zmap`s with
   `Functor.map_comp`, and identify with `hFourQ1`/`hFourQ2` (`Work.ATOM.ZS.hFourQ1`,
   `hFourQ2` — note `hFourQ2` is `hFourPull ≫ whiskerRight shift (ℕ∪∞) ≫ phiP`). -/
theorem hFour_RED_R (S : LightProfinite.{0}) [Infinite S] :
    Work.ATOM.zmap (Work.ATOM.ZS.hFourPull S) ≫ Work.ATOM.EApp ≫ Work.ATOM.preShiftP ≫
        Work.ATOM.FP S =
      (Work.ATOM.zmap (Work.ATOM.ZS.hFourQ1 S) - Work.ATOM.zmap (Work.ATOM.ZS.hFourQ2 S)) ≫
        LightCondensed.P_proj := by
  simpa only [Work.ATOM.ZS.hFourPull, Work.ATOM.ZS.hFourQ1, Work.ATOM.ZS.hFourQ2]
    using hFour_RED_R_aux S

end

end Work.ATOM.ZS
