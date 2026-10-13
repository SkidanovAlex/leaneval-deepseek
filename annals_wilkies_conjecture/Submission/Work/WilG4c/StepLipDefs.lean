import Mathlib
import Submission.Work.WilG4c.CurveFam
import Submission.Work.WilG4c.LipRescale
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilG4c.CellSmooth
import Submission.Work.WilG4c.Pullback

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG5

/-!
# BNZ §5.3, the `r ≥ 1` slice: `StepLipHigh`

This file develops the vocabulary of the reduction `PY ⟶ PYLip` of BNZ §5.3 (the
"Reduction to `1`-Lipschitz") in the form used by the rest of the `WilG4c` area, and
assembles the proof of `Work.WilkG4c.StepLipHigh`.

The reduction rests on the near-maximising curves produced by `Work.WilkG4c.CurveFam`.  For a
family member `f` and a point `(l,x)` of the parameter space, the *near-maximiser condition*
`NearMax f l x` says that some point of the fibre (inside the open cube and the interior of
the `C¹` locus) dominates all other such points, up to the factor `2`, in absolute value of
the `x`-derivative.  `CurveFam` provides a definable curve `γ` which, *wherever* the
condition holds, is itself such a near-maximiser; the complement `badCurve f` is the
exceptional set of the reduction.

## Coordinates

A family member is `f : (Fin p → ℝ) → (Fin (n+1) → ℝ) → ℝ`; points of `ℝ^{p+(n+1)}` are
written `xPt l x y` (`l` the parameter, `x` the distinguished coordinate, `y` the remaining
`n` coordinates), as in `Work.WilkG4c.LipDefs`.
-/

variable {p n : ℕ}

/-! ## 1. The near-maximiser condition and the bad set -/

/-- The near-maximiser condition of BNZ §5.3 at `(l,x)`: the fibre of `f` over `(l,x)`
contains a point of the open cube, inside the interior of the `C¹` locus, whose
`x`-derivative dominates, up to the factor `2`, the `x`-derivative at every other such point
of the fibre. -/
def NearMax (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (l : Fin p → ℝ) (x : ℝ) : Prop :=
  ∃ y : Fin n → ℝ, y ∈ openCube n ∧
    xPt l x y ∈ interior {z | ContDiffAt ℝ 1 (famFunHat f) z} ∧
    ∀ y' : Fin n → ℝ, y' ∈ openCube n →
      xPt l x y' ∈ interior {z | ContDiffAt ℝ 1 (famFunHat f) z} →
      |xDeriv f l x y'| ≤ 2 * |xDeriv f l x y|

/-- The exceptional set of the §5.3 reduction: the `(l,x)` at which no near-maximiser
exists. -/
def badCurve (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) : Set (Fin (p + 1) → ℝ) :=
  {w | ¬ NearMax f (fun i => w (Fin.castSucc i)) (w (Fin.last p))}

/-- The reindexing `(l, x | y₁ … yₙ) ↦ (l, x, y₁ … yₙ)`: it turns a point of
`ℝ^{p+(n+1)}` (in the coordinate order of `xPt`) into a point of `ℝ^{(p+1)+n}` (in the
coordinate order of `Fin.append`). -/
def reidx (p n : ℕ) : Fin (p + (n + 1)) → Fin ((p + 1) + n) :=
  fun k => Fin.addCases (m := p) (n := n + 1)
    (fun i => Fin.castAdd n (Fin.castSucc i))
    (fun j => Fin.cases (Fin.castAdd n (Fin.last p)) (fun j' => Fin.natAdd (p + 1) j') j)
    k

/-- The reindexing `reidx` expressed on the `xPt`-coordinates. -/
theorem append_comp_reidx (u : Fin (p + 1) → ℝ) (y : Fin n → ℝ) :
    (Fin.append u y) ∘ (reidx p n) =
      xPt (fun i : Fin p => u (Fin.castSucc i)) (u (Fin.last p)) y := by
  funext k
  refine Fin.addCases (m := p) (n := n + 1) ?_ ?_ k
  · intro i
    simp only [Function.comp_apply, reidx, Fin.addCases_left,
      xPt, Fin.append_left, Fin.castSucc_castAdd, Fin.snoc_castSucc]
  · intro j
    refine Fin.cases ?_ ?_ j
    · simp only [Function.comp_apply, reidx, Fin.addCases_right, Fin.cases_zero,
        xPt, Fin.append_left, Fin.append_right, Fin.cons_zero, Fin.snoc_last]
    · intro j'
      simp only [Function.comp_apply, reidx, Fin.addCases_right, Fin.cases_succ,
        xPt, Fin.append_left, Fin.append_right, Fin.cons_succ, Fin.snoc_castSucc]

/-- The complement of the bad set, as the projection of the selection set `Xset` of
`CurveFam`. -/
def goodCurve (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) : Set (Fin (p + 1) → ℝ) :=
  projN n (coordPre (reidx p n) (Xset p n f))

/-- The near-maximiser condition is exactly the non-emptiness of the fibre of `Xset`. -/
theorem nearMax_iff_exists_mem_Xset (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (l : Fin p → ℝ) (x : ℝ) :
    NearMax f l x ↔ ∃ y : Fin n → ℝ, xPt l x y ∈ Xset p n f := by
  constructor
  · rintro ⟨y, hy, hloc, hmax⟩
    refine ⟨y, ?_⟩
    rw [mem_Xset_iff (Work.WilG4c.CurveFam.mem_badSet_iff f) (xPt l x y)]
    refine ⟨?_, hloc, ?_⟩
    · have hy' : (fun j : Fin n => xPt l x y (yIdx p n j)) = y := by
        funext j; rw [xPt_yIdx]
      rw [hy']; exact hy
    · intro y' hy' hz
      rw [zPt_xPt] at hz ⊢
      rw [xDer_xPt, xDer_xPt]
      exact hmax y' hy' hz
  · rintro ⟨y, hy⟩
    have h := (mem_Xset_iff (Work.WilG4c.CurveFam.mem_badSet_iff f) (xPt l x y)).mp hy
    obtain ⟨hycube, hloc, hmax⟩ := h
    have hy' : y ∈ openCube n := by
      have hy'' : (fun j : Fin n => xPt l x y (yIdx p n j)) = y := by
        funext j; rw [xPt_yIdx]
      rwa [hy''] at hycube
    refine ⟨y, hy', hloc, ?_⟩
    intro y' hy' hz
    have hzz : zPt p n (xPt l x y) y' ∈ LocSet p n f := by
      rw [zPt_xPt]; exact hz
    have h'' := hmax y' hy' hzz
    rwa [zPt_xPt, xDer_xPt, xDer_xPt] at h''

/-- Membership in `goodCurve`, in the coordinates `(l,x)` of the parameter space. -/
theorem mem_goodCurve_iff (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (u : Fin (p + 1) → ℝ) :
    u ∈ goodCurve f ↔ NearMax f (fun i => u (Fin.castSucc i)) (u (Fin.last p)) := by
  rw [goodCurve, projN, Set.mem_ofPred_eq, nearMax_iff_exists_mem_Xset]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have h := hy
    rw [coordPre, Set.mem_ofPred_eq] at h
    rwa [append_comp_reidx] at h
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [coordPre, Set.mem_ofPred_eq, append_comp_reidx]; exact hy⟩

/-- The bad set is the complement of `goodCurve`. -/
theorem badCurve_eq_compl (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    badCurve f = (goodCurve f)ᶜ := by
  ext u
  rw [badCurve, Set.mem_ofPred_eq, Set.mem_compl_iff, mem_goodCurve_iff]

/-! ## 1bis. The transfer of the near-maximiser bound

The two elementary consequences of `NearMax` that the §5.3 assembly consumes: at a
near-maximiser, the `x`-derivative of `f` at the *curve point* bounds, up to the factor `2`,
the `x`-derivative at every point of the fibre that lies in the interior of the `C¹` locus;
and this transfers a `/any` bound `|xDeriv f l x (γ l x)| ≤ C` to `2 * C`. -/

/-- At a near-maximiser `γ l x`, every `C¹`-fibre point has `|xDeriv| ≤ 2 |xDeriv (γ l x)|`. -/
theorem xDeriv_le_two_mul_gamma (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)) (l : Fin p → ℝ) (x : ℝ)
    (hγ : γ l x ∈ openCube n ∧
      xPt l x (γ l x) ∈ interior {z | ContDiffAt ℝ 1 (famFunHat f) z} ∧
      ∀ y' : Fin n → ℝ, y' ∈ openCube n →
        xPt l x y' ∈ interior {z | ContDiffAt ℝ 1 (famFunHat f) z} →
        |xDeriv f l x y'| ≤ 2 * |xDeriv f l x (γ l x)|) :
    ∀ y' : Fin n → ℝ, y' ∈ openCube n →
      xPt l x y' ∈ interior {z | ContDiffAt ℝ 1 (famFunHat f) z} →
      |xDeriv f l x y'| ≤ 2 * |xDeriv f l x (γ l x)| :=
  hγ.2.2

/-- Transfer of a numerical bound at the near-maximiser to the whole fibre. -/
theorem xDeriv_le_of_gamma_le (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)) (l : Fin p → ℝ) (x C : ℝ)
    (hγ : γ l x ∈ openCube n ∧
      xPt l x (γ l x) ∈ interior {z | ContDiffAt ℝ 1 (famFunHat f) z} ∧
      ∀ y' : Fin n → ℝ, y' ∈ openCube n →
        xPt l x y' ∈ interior {z | ContDiffAt ℝ 1 (famFunHat f) z} →
        |xDeriv f l x y'| ≤ 2 * |xDeriv f l x (γ l x)|)
    (hC : |xDeriv f l x (γ l x)| ≤ C) :
    ∀ y' : Fin n → ℝ, y' ∈ openCube n →
      xPt l x y' ∈ interior {z | ContDiffAt ℝ 1 (famFunHat f) z} →
      |xDeriv f l x y'| ≤ 2 * C := by
  intro y' hy' hz
  exact le_trans (xDeriv_le_two_mul_gamma f γ l x hγ y' hy' hz)
    (by linarith)

/-! ## 2. The `Ω`-membership of the bad set -/

/-- `badCurve f` is `Ω`-bounded, with a format independent of `D` and a degree linear in `D`.
The bounds are those of `Xset_mem`, `coordPre_mem` and `projN_mem`. -/
theorem badCurve_mem {S : SOMin} {p n a1 L : ℕ}
    {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    (hDg : DgSet p n f ∈ S.Ω a1 L (p + (n + 1) + 1)) :
    badCurve f ∈ S.Ω (Fx p n a1 + 64 * ((p + 1) + n + (p + (n + 1))) + 64 + n + 1)
      (Dx p n L + 32 * ((p + 1) + n + (p + (n + 1))) + 32) (p + 1) := by
  have hX : Xset p n f ∈ S.Ω (Fx p n a1) (Dx p n L) (p + (n + 1)) := Xset_mem hDg
  have hσ : coordPre (reidx p n) (Xset p n f) ∈
      S.Ω (Fx p n a1 + 64 * ((p + 1) + n + (p + (n + 1))) + 64)
        (Dx p n L + 32 * ((p + 1) + n + (p + (n + 1))) + 32) ((p + 1) + n) :=
    coordPre_mem (S := S) hX
  have hproj := projN_mem (S := S) n _ _ hσ
  rw [badCurve_eq_compl]
  exact mem_mono (S.compl hproj) _ _ (by omega) (by omega)
