/-
  WilG4c — `CurveFamAlpha_list_pure`: the *pure* near-maximising `γ`-selection for the
  order-`|L|` directional derivative, i.e. BNZ's `S_{i,α} = {|∂^α| ≥ ½ sup}`.

  This is `CurveFamAlpha_list` with the two threshold disjuncts `AlAlt1`, `AlAlt2` dropped from
  the selection set: the set

      `AlZsetPure p n f L = coordPre (yIdx p n) (openCube n) ∩ AlLoc p n f L.length ∩ (AlViol p n f L)ᶜ`

  (cube membership, the interior of the `C^{|L|}`-locus, and the near-maximality disjunct of
  `threshAltL` alone).  The conclusion is an implication whose hypothesis supplies the
  nonemptiness of the fibre of `AlZsetPure` over `(l,x)`, so that, exactly as in
  `CurveFamAlpha_list`, defining choice (`ChoiceHyp`) applied to the `Ω`-set `AlZsetPure` gives
  the selector `γ`.

  Nothing new is analytic: `AlDgList` is `Ω`-definable by `SharpDeriv`, `AlViol` is `Ω`-definable
  (`AlphaViolMem`), and `AlZsetPure` is the `Ω`-combination `cube ∩ locus ∩ (violation)ᶜ` with the
  same loose bounds `AlFzs`, `AlDzs` as `AlZset` (which dominate).  The membership lemmas
  `mem_AlZsetPure_iff` / `mem_AlZsetPure_liftDir_iff` unfold `AlZsetPure` into exactly the
  hypothesis/conclusion of the statement.
-/
import Mathlib
import Submission.Work.WilG4c.CurveFamAlphaDefs
import Submission.Work.WilG4c.CurveFamAlpha_list
import Submission.Work.WilG4c.Alpha.AlphaViolIff
import Submission.Work.WilG4c.Alpha.AlphaViolMem

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilkG4c
open Work.WilG5

/-! ## 1. The pure selection set -/

/-- `AlZsetPure p n f L`: the selection set of the *pure* near-maximising curve choice — the
`w = (l,x,y)` with `y ∈ openCube n`, `w` in the interior of the `C^{|L|}`-locus and `w` not
beaten by any cube point of the fibre.  This is `AlZset p n f L E` with the two threshold
disjuncts `AlAlt1`, `AlAlt2` deleted. -/
def AlZsetPure (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (p + (n + 1)))) : Set (Fin (p + (n + 1)) → ℝ) :=
  coordPre (yIdx p n) (openCube n) ∩ AlLoc p n f L.length ∩ (AlViol p n f L)ᶜ

/-- The unfolding of `AlZsetPure` into the cube condition, the `C^{|L|}`-locus condition and the
near-maximality condition (the complement of `AlViol`, described by `AlphaViolIff`). -/
theorem mem_AlZsetPure_iff {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {L : List (Fin (p + (n + 1)))} {w : Fin (p + (n + 1)) → ℝ} :
    w ∈ AlZsetPure p n f L ↔ (fun j : Fin n => w (yIdx p n j)) ∈ openCube n ∧
      w ∈ AlLoc p n f L.length ∧
      ∀ y' : Fin n → ℝ, y' ∈ openCube n → zPt p n w y' ∈ AlLoc p n f L.length →
        |iterDir L (famFunHat f) (zPt p n w y')| ≤ 2 * |iterDir L (famFunHat f) w| := by
  simp only [AlZsetPure, Set.mem_inter_iff, coordPre, Set.mem_ofPred_eq, Set.mem_compl_iff]
  rw [Alpha.AlphaViolIff f L w]
  constructor
  · rintro ⟨⟨hyc, hl⟩, hnv⟩
    refine ⟨hyc, hl, ?_⟩
    intro y' hy' hl'
    by_contra hcon
    exact hnv ⟨hl, y', hy', hl', lt_of_not_ge hcon⟩
  · rintro ⟨hyc, hl, hmax⟩
    refine ⟨⟨hyc, hl⟩, ?_⟩
    rintro ⟨-, y', hy', hl', hlt⟩
    exact absurd (hmax y' hy' hl') (not_le.mpr hlt)

/-- `AlZsetPure p n f L` is an `Ω`-set with the same (loose) format/degree bounds `AlFzs`, `AlDzs`
as `AlZset`, given the `Ω`-membership of the derivative graph `AlDgList` and of the violation set
`AlViol`. -/
theorem AlZsetPureMem {S : WilkiesDesign.SOMin} {p n a1 β : ℕ}
    {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ} (L : List (Fin (p + (n + 1))))
    (hDg : AlDgList p n f L ∈ S.Ω a1 β (p + (n + 1) + 1))
    (hViol : AlViol p n f L ∈ S.Ω (AlFviol p n a1) (AlDviol p n β) (p + (n + 1))) :
    AlZsetPure p n f L ∈ S.Ω (AlFzs p n a1) (AlDzs p n β) (p + (n + 1)) := by
  -- the common format at which the three conjuncts are intersected
  let F3 : ℕ := max ((4 * n + 24) + 64 * ((p + (n + 1)) + n) + 64)
    (max (a1 + 1) (AlFu p n a1))
  -- the `C^{|L|}`-locus, as the projection of the derivative graph `AlDgList`
  have hloc : AlLoc p n f L.length ∈ S.Ω (a1 + 1) β (p + (n + 1)) := by
    rw [← Work.WilkG4c.projLast_AlDgList f L]
    exact S.proj hDg
  -- the cube coordinates
  have hcube : coordPre (yIdx p n) (openCube n) ∈
      S.Ω ((4 * n + 24) + 64 * ((p + (n + 1)) + n) + 64)
        ((16 * n + 16) + 32 * ((p + (n + 1)) + n) + 32) (p + (n + 1)) :=
    Work.WilG5.coordPre_mem (S := S) (m := n) (N := p + (n + 1)) (F := 4 * n + 24)
      (D := 16 * n + 16) (ι := yIdx p n) (Work.WilG5.openCube_mem (S := S) (n := n))
  -- the near-maximality disjunct
  have hcomp : (AlViol p n f L)ᶜ ∈
      S.Ω (AlFviol p n a1 + 1) (AlDviol p n β) (p + (n + 1)) := S.compl hViol
  have hcomp' : (AlViol p n f L)ᶜ ∈ S.Ω (AlFu p n a1) (AlDviol p n β) (p + (n + 1)) :=
    Work.WilG5.mem_mono (S := S) hcomp (AlFu p n a1) (AlDviol p n β)
      (by simp only [AlFu]; omega) le_rfl
  -- raise everything to the common format `F3`
  have hcube' : coordPre (yIdx p n) (openCube n) ∈
      S.Ω F3 ((16 * n + 16) + 32 * ((p + (n + 1)) + n) + 32) (p + (n + 1)) :=
    Work.WilG5.mem_mono (S := S) hcube F3 _ (by dsimp only [F3]; omega) le_rfl
  have hloc' : AlLoc p n f L.length ∈ S.Ω F3 β (p + (n + 1)) :=
    Work.WilG5.mem_mono (S := S) hloc F3 β (by dsimp only [F3]; omega) le_rfl
  have hcomp'' : (AlViol p n f L)ᶜ ∈ S.Ω F3 (AlDviol p n β) (p + (n + 1)) :=
    Work.WilG5.mem_mono (S := S) hcomp' F3 (AlDviol p n β) (by dsimp only [F3]; omega) le_rfl
  -- the threefold intersection
  have h3 := S.inter (F := F3) (n := p + (n + 1)) (k := 3)
    (fun i : Fin 3 => ![(16 * n + 16) + 32 * ((p + (n + 1)) + n) + 32, β, AlDviol p n β] i)
    (fun i : Fin 3 => ![coordPre (yIdx p n) (openCube n), AlLoc p n f L.length,
      (AlViol p n f L)ᶜ] i)
    (by intro i; fin_cases i
        · simpa using hcube'
        · simpa using hloc'
        · simpa using hcomp'')
  rw [show (∑ i : Fin 3,
      ![(16 * n + 16) + 32 * ((p + (n + 1)) + n) + 32, β, AlDviol p n β] i)
      = ((16 * n + 16) + 32 * ((p + (n + 1)) + n) + 32) + β + AlDviol p n β from by
    simp [Fin.sum_univ_three]] at h3
  rw [Work.WilkG4c.iInter_fin_three (coordPre (yIdx p n) (openCube n))
    (AlLoc p n f L.length) ((AlViol p n f L)ᶜ)] at h3
  refine Work.WilG5.mem_mono (S := S) h3 (AlFzs p n a1) (AlDzs p n β) ?_ ?_
  · dsimp only [F3]; simp only [AlFzs]; omega
  · simp only [AlDzs, AlDu]; omega

/-- Membership of `xPt l x y` in `AlZsetPure p n f (liftDir L)`: cube membership, the
`C^{|L|}`-locus condition at `xPt l x y`, and the near-maximality of `|∂^{L}|` at `xPt l x y`
over the cube points of the fibre that lie in the locus. -/
theorem mem_AlZsetPure_liftDir_iff {p n : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1)))
    (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ) :
    xPt l x y ∈ AlZsetPure p n f (liftDir L) ↔ y ∈ openCube n ∧
      xPt l x y ∈ interior {z | ContDiffAt ℝ L.length (famFunHat f) z} ∧
      ∀ y' : Fin n → ℝ, y' ∈ openCube n →
        xPt l x y' ∈ interior {z | ContDiffAt ℝ L.length (famFunHat f) z} →
        |iterDir (liftDir L) (famFunHat f) (xPt l x y')| ≤
          2 * |iterDir (liftDir L) (famFunHat f) (xPt l x y)| := by
  have hy : (fun j : Fin n => xPt l x y (yIdx p n j)) = y := by
    funext j; rw [xPt_yIdx]
  have hloc : AlLoc p n f (liftDir (p := p) L).length =
      interior {z | ContDiffAt ℝ L.length (famFunHat f) z} := by
    simp only [AlLoc, liftDir_length]
  rw [mem_AlZsetPure_iff, hy, hloc]
  simp only [zPt_xPt]

/-! ## 2. The pure list form of `CurveFamAlpha` -/

/-- Definable choice of a *pure* near-maximising curve for the order-`|L|` directional derivative,
with no threshold alternative: this is BNZ's `S_{i,α}` (the set `{|∂^α| ≥ ½ sup}`) in the
`CurveFamAlpha`/`CurveFam` vocabulary.  The conclusion is an implication whose hypothesis
(existence of a near-maximiser in the fibre) is supplied by the caller, so the selector is
unconstrained on fibres where no near-maximiser exists (BNZ: "for `x` where the supremum is
infinite the condition is vacuous").  This is `CurveFamAlpha_list` with `AlAlt1`/`AlAlt2` dropped
from the selection set, i.e. with `AlZset` replaced by
`coordPre (yIdx p n) (openCube n) ∩ AlLoc p n f L.length ∩ (AlViol p n f L)ᶜ`. -/
theorem CurveFamAlpha_list_pure (S : WilkiesDesign.SOMin) (hder : WilkiesDesign.SOMin.SharpDeriv S)
    (hchoice : Work.WilkG4c.ChoiceHyp S) (p n : ℕ) :
    ∀ F0 : ℕ, ∃ (A : ℕ) (B : MvPolynomial (Fin 2) ℕ),
      ∀ (D r : ℕ) (Λ : Set (Fin p → ℝ)) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
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
                ∀ y' : Fin n → ℝ, y' ∈ WilkiesDesign.openCube n →
                  Work.WilkG4c.xPt l x y' ∈ interior {z | ContDiffAt ℝ L.length
                    (Work.WilkG4c.famFunHat f) z} →
                  |Work.WilkG4c.iterDir (Work.WilkG4c.liftDir L) (Work.WilkG4c.famFunHat f)
                    (Work.WilkG4c.xPt l x y')| ≤
                    2 * |Work.WilkG4c.iterDir (Work.WilkG4c.liftDir L)
                      (Work.WilkG4c.famFunHat f) (Work.WilkG4c.xPt l x y)|) →
              γ l x ∈ WilkiesDesign.openCube n ∧
              Work.WilkG4c.xPt l x (γ l x) ∈ interior {z | ContDiffAt ℝ L.length
                (Work.WilkG4c.famFunHat f) z} ∧
              ∀ y' : Fin n → ℝ, y' ∈ WilkiesDesign.openCube n →
                Work.WilkG4c.xPt l x y' ∈ interior {z | ContDiffAt ℝ L.length
                  (Work.WilkG4c.famFunHat f) z} →
                |Work.WilkG4c.iterDir (Work.WilkG4c.liftDir L) (Work.WilkG4c.famFunHat f)
                  (Work.WilkG4c.xPt l x y')| ≤
                  2 * |Work.WilkG4c.iterDir (Work.WilkG4c.liftDir L) (Work.WilkG4c.famFunHat f)
                    (Work.WilkG4c.xPt l x (γ l x))|) := by
  intro F0
  obtain ⟨a1, b1, hAlDg⟩ := AlDgList_mem_sharp S hder F0 p n
  obtain ⟨aC, bC, hC⟩ := hchoice (AlFzs p n a1) (p + 1) n
  refine ⟨AlA p n aC, AlB p n b1 bC, ?_⟩
  intro D r Λ f hΩ L hL
  have hPL : p + (n + 1) = (p + 1) + n := by omega
  have hgraph : graphOf (famFunHat f) ∈ S.Ω F0 D (p + (n + 1) + 1) := by
    rw [← famGraph_eq_graphOf_famFunHat]
    exact hΩ
  have hLlen : (liftDir (p := p) L).length = L.length := liftDir_length p L
  have hDg := hAlDg D f (liftDir L) hgraph
  rw [hLlen] at hDg
  have hViol := Alpha.AlphaViolMem (f := f) (liftDir L) hDg
  have hZs := AlZsetPureMem (L := liftDir L) hDg hViol
  have hZs' := omega_ndrec hPL hZs
  obtain ⟨fsel, hsel, hGmem⟩ := hC
    (AlDzs p n (MvPolynomial.eval ![D, L.length] b1))
    (hPL ▸ AlZsetPure p n f (liftDir L)) hZs'
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
    obtain ⟨y, hyc, hyl, hmax⟩ := hx
    have hwit : Fin.append (Fin.snoc l x) y ∈ (hPL ▸ AlZsetPure p n f (liftDir L)) := by
      rw [mem_ndrec, cast_snoc_append_xPt hPL]
      exact (mem_AlZsetPure_liftDir_iff f L l x y).mpr ⟨hyc, hyl, hmax⟩
    have hsel' := hsel (Fin.snoc l x) ⟨y, hwit⟩
    have hZs2 : xPt l x (fsel (Fin.snoc l x)) ∈ AlZsetPure p n f (liftDir L) := by
      have h := (mem_ndrec hPL (AlZsetPure p n f (liftDir L))
        (Fin.append (Fin.snoc l x) (fsel (Fin.snoc l x)))).mp hsel'
      rwa [cast_snoc_append_xPt hPL] at h
    exact (mem_AlZsetPure_liftDir_iff f L l x (fsel (Fin.snoc l x))).mp hZs2

end Work.WilG4c
