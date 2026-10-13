/-
  WilG4c — `ChartsOfPYLipOn`.

  The F-lemma (`Work.WilkG4c.FLemP`) at dimension `n+1` with the `1`-Lipschitz hypothesis
  `PYLip` is available as `hP1`.  Here we read off a version in which the family
  hypotheses (`YBound`, `LipOnCube`) are only imposed on a parameter set `P` which is itself
  `Ω`-definable at format `aΛ` and degree `eval ![D,r] dΛ`, and in which the Lipschitz
  constant is allowed to be any `C ≥ 1`.

  The proof is a "λ-uniformity" argument:

  * `Work.WilG4c.LipRescale` already upgrades `FLemP (PYLip)` to the `C`-Lipschitz setting
    (by subdividing the cube into tiles whose pullback has Lipschitz constant `1`), so it
    suffices to localise the hypotheses to `P`;
  * localisation is done by patching the family outside `P` with the constant `1/2`
    (`Work.WilkG4c.iteFamPYLipOn` for the analytic hypotheses, `Work.WilG4c.IteFamGraphMem`
    for the `Ω`-definability of the patched graph);
  * the charts produced for the patched family are then read back on `P`, where the two
    families agree (`ChartsOK_congr`, `Covers_congr`);
  * the degree `D` fed to `LipRescale` is the polynomial expression `D + 2·eval ![D,r] dΛ + 5`
    in the inputs of the statement, which is accounted for by the substitution lemmas
    `Work.WilkG4c.PolySubstFirst` / `Work.WilkG4c.PolySubstFirst4`.
-/
import Mathlib
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilG4c.LipRescale
import Submission.Work.WilG4c.StepLipAux
import Submission.Work.WilG4c.StepLipR0Aux1
import Submission.Work.WilG4c.IteFamGraphMem
import Submission.Work.WilG4c.PolySubstFirst
import Submission.Work.WilG4c.PolySubstFirst4

namespace Work.WilG4c

open Classical
open WilkiesDesign WilkiesDesign.CG
open Work.WilkG4c

/-- `ChartsOK` only involves the values of the family on the parameter set `Λ`; replacing the
family by another one that agrees with it there does not change the property. -/
theorem ChartsOK_congr {S : SOMin} {p n k a Dg r : ℕ} {Λ : Set (Fin p → ℝ)}
    {F G : Family k p n} {Φ : Finset (ChartTuple p n)}
    (h : ∀ i l, l ∈ Λ → ∀ t, G i l t = F i l t)
    (hOK : ChartsOK S a Dg r Λ G Φ) : ChartsOK S a Dg r Λ F Φ := by
  intro φ hφ
  obtain ⟨hmem, hrest⟩ := hOK φ hφ
  refine ⟨hmem, ?_⟩
  intro l hl
  obtain ⟨hcube, hsmooth⟩ := hrest l hl
  refine ⟨hcube, ?_⟩
  intro i
  obtain ⟨hcd, hder⟩ := hsmooth i
  have hfun : (fun t => F i l (fun j => φ j l t)) = (fun t => G i l (fun j => φ j l t)) := by
    funext t
    exact (h i l hl (fun j => φ j l t)).symm
  exact ⟨by rw [hfun]; exact hcd, fun m hm t ht => by rw [hfun]; exact hder m hm t ht⟩

/-- Same for `Covers`. -/
theorem Covers_congr {p n k : ℕ} {Λ : Set (Fin p → ℝ)} {F G : Family k p n}
    {Φ : Finset (ChartTuple p n)} {ε : ℝ}
    (h : ∀ i l, l ∈ Λ → ∀ t, G i l t = F i l t)
    (hC : Covers Λ G Φ ε) : Covers Λ F Φ ε := by
  intro l hl x hx
  obtain ⟨φ, hφ, t, ht, hlt⟩ := hC l hl x hx
  exact ⟨φ, hφ, t, ht, fun i => by
    rw [← h i l hl (fun j => φ j l t), ← h i l hl x]
    exact hlt i⟩

theorem ChartsOfPYLipOn (S : WilkiesDesign.SOMin) (n p : ℕ)
    (hP1 : Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PYLip p n)) (C : ℝ) (hC : 1 ≤ C) :
    ∀ (F0 aΛ : ℕ) (dΛ : MvPolynomial (Fin 2) ℕ),
      ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
      ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
      ∀ (P : Set (Fin p → ℝ)) (F : Work.WilkG4c.Family k p (n + 1)),
        P ∈ S.Ω aΛ (MvPolynomial.eval ![D, r] dΛ) p →
        (∀ i, WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 D (p + (n + 1) + 1)) →
        (∀ i, ∀ l ∈ P, ∀ x ∈ Work.WilkG4c.I, ∀ m, m ≤ r → ∀ y ∈ WilkiesDesign.openCube n,
          ‖iteratedFDeriv ℝ m (Work.WilkG4c.slice (F i l) x) y‖ ≤ 1) →
        (∀ i, ∀ l ∈ P, ∀ z ∈ WilkiesDesign.openCube (n + 1),
          ∀ z' ∈ WilkiesDesign.openCube (n + 1),
          |F i l z - F i l z'| ≤ C * dist z z') →
        Work.WilkG4c.ValuesIn01 P F →
        ∃ Φ : Finset (Work.WilkG4c.ChartTuple p (n + 1)),
          (Φ.card : ℝ) ≤
              MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
            Work.WilkG4c.ChartsOK S a (MvPolynomial.eval ![D, r] b) r P F Φ ∧
            Work.WilkG4c.Covers P F Φ ε := by
  intro F0 aΛ dΛ
  -- `LipRescale` turns the `1`-Lipschitz F-lemma into a `C`-Lipschitz one.
  have hLR := (LipRescale S n p hP1) C hC
  rw [FLemP_iff] at hLR
  -- the format of the patched graph; the degree fed to `hLR` is `D' = D + 2·eval ![D,r] dΛ + 5`
  obtain ⟨a', b', c', hmain⟩ := hLR (F0 + aΛ + 3 * (p + (n + 1) + 1) + 3 * p + 6)
  -- account for the polynomial expression `D ↦ D + 2·eval ![D,r] dΛ + 5` in the witnesses
  obtain ⟨b, hb⟩ := PolySubstFirst (MvPolynomial.X 0 + 2 * dΛ + MvPolynomial.C 5) b'
  obtain ⟨c, hc⟩ := PolySubstFirst4 (MvPolynomial.X 0 + 2 * dΛ + MvPolynomial.C 5) c'
  refine ⟨a', b, c, ?_⟩
  intro D r k ε hε0 hε1 P F hPmem hΩg hY hLip hval
  -- the family patched by the constant `1/2` outside the parameter set `P`
  set G : Work.WilkG4c.Family k p (n + 1) :=
    fun i l t => if l ∈ P then F i l t else (1 / 2 : ℝ) with hGdef
  set D' : ℕ := D + 2 * MvPolynomial.eval ![D, r] dΛ + 5 with hD'def
  have hq : MvPolynomial.eval ![D, r]
      (MvPolynomial.X 0 + 2 * dΛ + MvPolynomial.C 5) = D' := by
    rw [hD'def]
    simp
  have hG_mem : ∀ i l t, l ∈ P → G i l t = F i l t := by
    intro i l t hl
    simp only [hGdef]
    rw [if_pos hl]
  have hG_notmem : ∀ i l t, l ∉ P → G i l t = (1 / 2 : ℝ) := by
    intro i l t hl
    simp only [hGdef]
    rw [if_neg hl]
  -- the graph of the patched family is still `Ω`-definable
  have hΩG : ∀ i, WilkiesDesign.CG.famGraph (G i) ∈
      S.Ω (F0 + aΛ + 3 * (p + (n + 1) + 1) + 3 * p + 6) D' (p + (n + 1) + 1) := by
    intro i
    have h := IteFamGraphMem S P (1 / 2 : ℝ) F G i aΛ (MvPolynomial.eval ![D, r] dΛ) F0 D
      hPmem (hΩg i) (fun l t hl => hG_mem i l t hl) (fun l t hl => hG_notmem i l t hl)
    rw [hD'def]
    exact h
  -- the patched family satisfies the analytic hypotheses of the F-lemma
  have hPYG : Work.WilkG4c.YBound G r ∧ Work.WilkG4c.LipOnCube G C ∧
      Work.WilkG4c.ValuesIn01 P G :=
    Work.WilkG4c.iteFamPYLipOn P F G (1 / 2 : ℝ) (by norm_num) r C
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) hC)
      (fun i l hl => hY i l hl) (fun i l hl z z' hz hz' => hLip i l hl z hz z' hz') hval
      (fun i l t hl => hG_mem i l t hl) (fun i l t hl => hG_notmem i l t hl)
  obtain ⟨Φ, hcard, hOK, hcov⟩ :=
    hmain D' r k ε hε0 hε1 P G ⟨hPYG.1, hPYG.2.1⟩ hΩG hPYG.2.2
  refine ⟨Φ, ?_, ?_, ?_⟩
  · -- the counting bound: substitute `D ↦ D'` in the polynomial `c'`
    have heq : MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c
        = MvPolynomial.eval ![((D' : ℕ) : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c' := by
      rw [hc D r k (-Real.log ε), hq]
    rw [heq]
    exact hcard
  · -- the chart conditions: read the charts of `G` back on `P`, where `G = F`
    have hOK' : Work.WilkG4c.ChartsOK S a' (MvPolynomial.eval ![D', r] b') r P F Φ :=
      ChartsOK_congr (fun i l hl t => hG_mem i l t hl) hOK
    rw [hb D r, hq]
    exact hOK'
  · -- the covering condition
    exact Covers_congr (fun i l hl t => hG_mem i l t hl) hcov

end Work.WilG4c
