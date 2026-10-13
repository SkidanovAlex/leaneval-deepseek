/-
  WilG4c — `CurveFamAlpha_list`: the `γ`-selection of BNZ §5.4 indexed by an *arbitrary*
  cube multiindex `L : List (Fin (n+1))` with `|L| ≤ r`, rather than by the canonical split
  `(j, M)` of `CurveFamAlpha`.

  Nothing new has to be proved analytically.  `CurveFamAlphaDefs` and the `Alpha.*` lemmas set
  up the whole selection machinery (`AlDgList`, `AlViol`, `AlZset`) for an *arbitrary* list of
  ambient directions, and `AlDgList_mem_sharp` (hence `AlphaViolMem`, `AlphaZsetMem`) is stated
  for an arbitrary list too.  The only change with respect to `CurveFamAlpha` is that the
  multiindex is the ambient lift

      `liftDir L = L.map (Fin.natAdd p)`

  of the cube multiindex, whose length is `L.length`; so the same proof goes through verbatim
  with `midx p n j M` replaced by `liftDir L`, and `midx_length` (the only place the shape of
  the multiindex was ever used) replaced by `liftDir_length`.

  The threshold alternative obtained from `mem_AlZset_iff` for the list `liftDir L` is, by
  `mem_AlZset_liftDir_iff` below, *literally* `threshAltL p n f L E`, which is the alternative
  the statement of `CurveFamAlpha_list` asks for.
-/
import Mathlib
import Submission.Work.WilG4c.StepHigherDefs
import Submission.Work.WilG4c.CurveFamAlpha
import Submission.Work.WilG4c.Hyps
import Submission.Work.WilG4c.CurveFamDefs

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilkG4c
open Work.WilG5

/-! ## 0. The length of the lifted list -/

/-- The lift `liftDir` preserves the length of the multiindex (`p` is explicit because it is
not determined by the argument list alone). -/
@[simp] theorem liftDir_length (p : ℕ) {n : ℕ} (L : List (Fin (n + 1))) :
    (liftDir (p := p) L).length = L.length := by simp [liftDir]

/-! ## 1. Membership in `AlZset` for the lifted list, in `threshAltL` form -/

/-- The `liftDir` form of `mem_AlZset_midx_iff`: membership of `xPt l x y` in
`AlZset p n f (liftDir L) E` is exactly the shape used by `CurveFamAlpha_list`, namely cube
membership, the `C^{|L|}`-locus condition at `xPt l x y`, and the threshold alternative
`threshAltL`. -/
theorem mem_AlZset_liftDir_iff {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (n + 1))) (E : ℝ) (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ)
    (hV : ∀ u : Fin (p + (n + 1)) → ℝ,
      (u ∈ AlViol p n f (liftDir L) ↔ AlViolProp p n f (liftDir L) u)) :
    xPt l x y ∈ AlZset p n f (liftDir L) E ↔ y ∈ openCube n ∧
      xPt l x y ∈ interior {z | ContDiffAt ℝ L.length (famFunHat f) z} ∧
      threshAltL p n f L E l x y := by
  rw [mem_AlZset_iff hV, threshAltL]
  rw [liftDir_length p]
  simp only [zPt_xPt, xPt_yIdx, AlLoc]

/-! ## 2. The list form of `CurveFamAlpha` -/

/-- **`CurveFamAlpha` for an arbitrary multiindex list `L`.** Same statement and same proof as
`CurveFamAlpha`, with `midx p n j M` (whose only role was `midx_length = j + |M|`) replaced by
the lift `liftDir L` of the cube multiindex `L` (whose only role is `liftDir_length = |L|`). -/
theorem CurveFamAlpha_list (S : WilkiesDesign.SOMin) (hder : WilkiesDesign.SOMin.SharpDeriv S)
    (hchoice : Work.WilkG4c.ChoiceHyp S) (p n : ℕ) :
    ∀ F0 : ℕ, ∃ (A : ℕ) (B : MvPolynomial (Fin 2) ℕ),
      ∀ (D r : ℕ) (E : ℝ), 0 < E →
      ∀ (Λ : Set (Fin p → ℝ)) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
        WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
        ∀ (L : List (Fin (n + 1))), L.length ≤ r →
          ∃ γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ),
            (∀ i : Fin n, WilkiesDesign.graphOf (fun w : Fin (p + 1) → ℝ =>
                γ (fun k => w (Fin.castSucc k)) (w (Fin.last p)) i)
              ∈ S.Ω A (MvPolynomial.eval ![D, r] B) (p + 1 + 1)) ∧
            (∀ l ∈ Λ, ∀ x : ℝ,
              (∃ y : Fin n → ℝ, y ∈ WilkiesDesign.openCube n ∧
                Work.WilkG4c.xPt l x y ∈ interior {z | ContDiffAt ℝ L.length
                  (Work.WilkG4c.famFunHat f) z} ∧
                Work.WilkG4c.threshAltL p n f L E l x y) →
              γ l x ∈ WilkiesDesign.openCube n ∧
              Work.WilkG4c.xPt l x (γ l x) ∈ interior {z | ContDiffAt ℝ L.length
                (Work.WilkG4c.famFunHat f) z} ∧
              Work.WilkG4c.threshAltL p n f L E l x (γ l x)) := by
  intro F0
  obtain ⟨a1, b1, hAlDg⟩ := AlDgList_mem_sharp S hder F0 p n
  obtain ⟨aC, bC, hC⟩ := hchoice (AlFzs p n a1) (p + 1) n
  refine ⟨AlA p n aC, AlB p n b1 bC, ?_⟩
  intro D r E hE Λ f hΩ L hL
  have hPL : p + (n + 1) = (p + 1) + n := by omega
  have hgraph : graphOf (famFunHat f) ∈ S.Ω F0 D (p + (n + 1) + 1) := by
    rw [← famGraph_eq_graphOf_famFunHat]
    exact hΩ
  have hLlen : (liftDir (p := p) L).length = L.length := liftDir_length p L
  have hDg := hAlDg D f (liftDir L) hgraph
  rw [hLlen] at hDg
  have hViol := Alpha.AlphaViolMem (f := f) (liftDir L) hDg
  have hZs := Alpha.AlphaZsetMem (E := E) (f := f) (liftDir L) hDg hViol
  have hZs' := omega_ndrec hPL hZs
  obtain ⟨fsel, hsel, hGmem⟩ := hC
    (AlDzs p n (MvPolynomial.eval ![D, L.length] b1))
    (hPL ▸ AlZset p n f (liftDir L) E) hZs'
  -- the degree inequality: this is the only place where `r` enters the picture
  have hβ : MvPolynomial.eval ![D, L.length] b1 ≤ MvPolynomial.eval ![D, r] b1 :=
    AlphaEvalMono b1 hL
  have hK1 : AlDzs p n (MvPolynomial.eval ![D, L.length] b1) ≤
      AlK1 p n + AlK2 * MvPolynomial.eval ![D, r] b1 := by
    dsimp only [AlDzs, AlDu, AlDalt, AlDviol, AlK1, AlK2]
    omega
  have hmono : bC.eval (AlDzs p n (MvPolynomial.eval ![D, L.length] b1)) ≤
      bC.eval (AlK1 p n + AlK2 * MvPolynomial.eval ![D, r] b1) :=
    Work.WilG1.Polynomial.eval_mono hK1
  have hdeg : bC.eval (AlDzs p n (MvPolynomial.eval ![D, L.length] b1)) +
      (32 * (((p + 1) + n) + (p + 1 + 1)) + 32) ≤
      MvPolynomial.eval ![D, r] (AlB p n b1 bC) := by
    rw [eval_AlB]
    have hK3 : 32 * (((p + 1) + n) + (p + 1 + 1)) + 32 ≤ AlK3 p n := by
      dsimp only [AlK3, AlK1]
      omega
    omega
  refine ⟨fun l x => fsel (Fin.snoc l x), ?_, ?_⟩
  · intro i
    have hmem := coordImage_mem (S := S)
      (ι := Fin.snoc (fun k : Fin (p + 1) => Fin.castAdd n k) (Fin.natAdd (p + 1) i)) hGmem
    have hge : graphOf (fun w : Fin (p + 1) → ℝ =>
          fsel (Fin.snoc (Fin.init w) (w (Fin.last p))) i) =
        coordImage (Fin.snoc (fun k : Fin (p + 1) => Fin.castAdd n k) (Fin.natAdd (p + 1) i))
          {z : Fin ((p + 1) + n) → ℝ | ∀ k : Fin n,
            z (Fin.natAdd (p + 1) k) = fsel (fun k' => z (Fin.castAdd n k')) k} :=
      CurveFam.graphOf_sel_eq_coordImage fsel i
    have hfun : (fun w : Fin (p + 1) → ℝ =>
          (fun l x => fsel (Fin.snoc l x)) (fun k => w (Fin.castSucc k)) (w (Fin.last p)) i)
        = (fun w : Fin (p + 1) → ℝ =>
          fsel (Fin.snoc (Fin.init w) (w (Fin.last p))) i) := rfl
    rw [hfun, hge]
    exact mem_mono hmem (AlA p n aC) (MvPolynomial.eval ![D, r] (AlB p n b1 bC)) le_rfl hdeg
  · intro l hl x hx
    obtain ⟨y, hyc, hyl, hth⟩ := hx
    have hV : ∀ u : Fin (p + (n + 1)) → ℝ,
        (u ∈ AlViol p n f (liftDir L) ↔ AlViolProp p n f (liftDir L) u) :=
      fun u => Alpha.AlphaViolIff f (liftDir L) u
    have hwit : Fin.append (Fin.snoc l x) y ∈ (hPL ▸ AlZset p n f (liftDir L) E) := by
      rw [mem_ndrec, cast_snoc_append_xPt hPL]
      exact (mem_AlZset_liftDir_iff f L E l x y hV).mpr ⟨hyc, hyl, hth⟩
    have hsel' := hsel (Fin.snoc l x) ⟨y, hwit⟩
    have hZs2 : xPt l x (fsel (Fin.snoc l x)) ∈ AlZset p n f (liftDir L) E := by
      have h := (mem_ndrec hPL (AlZset p n f (liftDir L) E)
        (Fin.append (Fin.snoc l x) (fsel (Fin.snoc l x)))).mp hsel'
      rwa [cast_snoc_append_xPt hPL] at h
    exact (mem_AlZset_liftDir_iff f L E l x (fsel (Fin.snoc l x)) hV).mp hZs2

end Work.WilG4c
