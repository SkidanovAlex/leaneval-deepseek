/-
  WilG4c / StepLipHighAux — the glue that the assembly of `Work.WilkG4c.StepLipHigh` needs.

  Two things live here (both used by the per-cell engine `PiecePYLipOfChart` and by the
  cell decomposition of the assembly):

  * `C1All f` — the set of parameter points `(l,s) ∈ ℝ^{p+1}` whose *whole fibre over the cube*
    lies in the interior of the joint `C¹` locus of `famFunHat f`.  On a cell contained in
    `C1All f`, `CurveFam`'s near-maximality (which is stated over the interior of the joint `C¹`
    locus) upgrades to the "for *every* `y` of the cube" domination, which is the `hmax`
    hypothesis of the §5.3 per-cell engine.
  * the chain rule along the distinguished `x`-line: at a point where the joint function is `C¹`,
    the junk value `xDeriv f l s u` *is* the derivative of the unary slice
    `s' ↦ f l (Fin.cons s' u)`.  This is what converts the junk bounds produced by
    `CurveFam`/`ChartsH1` into honest one-dimensional derivative bounds, i.e. what makes the
    mean-value argument of the Lipschitz step legitimate.

  Nothing here is specific to a particular family; the file is `sorry`-free.
-/
import Mathlib
import Submission.Work.WilG4c.StepLipDefs
import Submission.Work.WilG4c.SliceLipInX
import Submission.Work.WilkG4c.YPullbackGraph

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- **`C1All f`**: the set of `(l,s) ∈ ℝ^{p+1}` such that the joint function `famFunHat f` is `C¹`
at `(l,s,y)` for *every* `y` in the open cube.  (The point is that `CurveFam`'s near-maximality
is stated only over the interior of the joint `C¹` locus; on `C1All f`, that locus covers the
whole fibre, so the near-maximality becomes a statement about every `y` of the cube.) -/
def C1All {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) : Set (Fin (p + 1) → ℝ) :=
  {w | ∀ y : Fin n → ℝ, y ∈ openCube n →
    xPt (fun i : Fin p => w (Fin.castSucc i)) (w (Fin.last p)) y ∈
      interior {z | ContDiffAt ℝ 1 (famFunHat f) z}}

theorem mem_C1All {p : ℕ} {l : Fin p → ℝ} {s : ℝ} :
    (fun i : Fin p => (Fin.snoc l s : Fin (p + 1) → ℝ) (Fin.castSucc i)) = l := by
  funext i
  simp

theorem c1All_iff {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (l : Fin p → ℝ) (s : ℝ) :
    (Fin.snoc l s : Fin (p + 1) → ℝ) ∈ C1All f ↔
      ∀ y : Fin n → ℝ, y ∈ openCube n →
        xPt l s y ∈ interior {z | ContDiffAt ℝ 1 (famFunHat f) z} := by
  rw [C1All, Set.mem_ofPred_eq]
  constructor
  · intro h y hy
    simpa [mem_C1All] using h y hy
  · intro h y hy
    simpa [mem_C1All] using h y hy

/-- **The junk `x`-derivative is the unary derivative at a `C¹` point.**  If the joint function
`famFunHat f` is `C¹` at `(l,s,u)`, then the unary slice `s' ↦ f l (Fin.cons s' u)` has at `s` the
derivative `xDeriv f l s u`.  (This is the chain rule along the affine line `s' ↦ xPt l s' u`.) -/
theorem xDeriv_eq_hasDerivAt_of_contDiffAt {p n : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (l : Fin p → ℝ) (s : ℝ) (u : Fin n → ℝ)
    (h : ContDiffAt ℝ 1 (famFunHat f) (xPt l s u)) :
    HasDerivAt (fun s' : ℝ => f l (Fin.cons s' u)) (xDeriv f l s u) s := by
  have hd : HasFDerivAt (famFunHat f) (fderiv ℝ (famFunHat f) (xPt l s u)) (xPt l s u) :=
    h.differentiableAt_one.hasFDerivAt
  have hcurve : HasDerivAt (fun s' : ℝ => xPt l s' u) (Pi.single (xDirHat p n) (1 : ℝ)) s :=
    hasDerivAt_xPt l s u
  have hcomp : HasDerivAt (fun s' : ℝ => famFunHat f (xPt l s' u))
      ((fderiv ℝ (famFunHat f) (xPt l s u)) (Pi.single (xDirHat p n) 1)) s := by
    simpa only [Function.comp_def] using hd.comp_hasDerivAt (x := s) hcurve
  have hfun : (fun s' : ℝ => famFunHat f (xPt l s' u)) = fun s' : ℝ => f l (Fin.cons s' u) := by
    funext s'
    exact famFunHat_xPt f l s' u
  rw [hfun] at hcomp
  simpa [xDeriv] using hcomp

/-- **The "for every `y` of the cube" near-maximality on a `C1All` fibre.**  `CurveFam`'s
conclusion gives the domination only over the interior of the joint `C¹` locus; on a point of
`C1All f` the whole fibre lies there, so the domination is available at every cube point.  This is
exactly the `hmax` hypothesis of `PiecePYLipOfChart`. -/
theorem xDeriv_le_two_mul_of_c1All {p n : ℕ}
    {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)} {l : Fin p → ℝ} {s : ℝ}
    (hγ : xPt l s (γ l s) ∈ interior {z | ContDiffAt ℝ 1 (famFunHat f) z} ∧
      ∀ y' : Fin n → ℝ, y' ∈ openCube n →
        xPt l s y' ∈ interior {z | ContDiffAt ℝ 1 (famFunHat f) z} →
        |xDeriv f l s y'| ≤ 2 * |xDeriv f l s (γ l s)|)
    (hC1All : ∀ y' : Fin n → ℝ, y' ∈ openCube n →
      xPt l s y' ∈ interior {z | ContDiffAt ℝ 1 (famFunHat f) z}) :
    ∀ y' ∈ openCube n, |xDeriv f l s y'| ≤ 2 * |xDeriv f l s (γ l s)| :=
  fun y' hy' => hγ.2 y' hy' (hC1All y' hy')

end Work.WilkG4c

/-! ## The `Ω`-bookkeeping of the `y`-pullback, with the increments fixed in advance -/

/-- **Quantifier-flipped form of `Work.WilkG4c.YPullbackGraph`.**  There the format/degree
increments `a, c` are existentially quantified *after* the family and the chart, so they cannot be
used by a statement whose witnesses have to be fixed before `D`.  The increments produced by the
proof of `YPullbackGraph` are absolute constants (`phiPtCoordGraph`'s and
`famGraph_comp_single`'s), so the same proof gives this uniform form, in which the degrees are
literal polynomials in `D` and in the chart's degree `Dg₁`. -/
theorem YPullbackGraphUniform (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ (a : ℕ) (c : ℕ), ∀ {k : ℕ} (F0 D a₁ Dg₁ : ℕ)
      (F : Work.WilkG4c.Family k p (n + 1)) (φ : Work.WilkG4c.ChartTuple (p + 1) n),
      (∀ i, WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 D (p + (n + 1) + 1)) →
      (∀ j, WilkiesDesign.CG.famGraph (φ j) ∈ S.Ω a₁ Dg₁ ((p + 1) + n + 1)) →
      (∀ j : Fin (n + 1), WilkiesDesign.CG.famGraph
          (fun l z => Work.WilkG4c.pullbackMap φ l z j) ∈
          S.Ω (a₁ + a) (Dg₁ + c) (p + (n + 1) + 1)) ∧
      ∀ i, WilkiesDesign.CG.famGraph (Work.WilkG4c.yPullback F φ i) ∈
        S.Ω (F0 + a₁ + a) (D + (p + (n + 1)) * (Dg₁ + c) + c) (p + (n + 1) + 1) := by
  obtain ⟨aphi, cphi, hphi⟩ := Work.WilG4c.phiPtCoordGraph S p n
  obtain ⟨acomp, ccomp, hcomp⟩ := Work.WilkG4c.famGraph_comp_single S p (n + 1)
  refine ⟨aphi + acomp, max cphi ccomp, ?_⟩
  intro k F0 D a₁ Dg₁ F φ hF hφ
  have hχ : ∀ j : Fin (n + 1),
      WilkiesDesign.CG.famGraph (fun l z => Work.WilkG4c.pullbackMap φ l z j) ∈
        S.Ω (a₁ + aphi) (Dg₁ + cphi) (p + (n + 1) + 1) := by
    intro j
    have h := hphi a₁ Dg₁ φ hφ j
    have hfun : (fun (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) => Work.WilkG4c.pullbackMap φ l z j)
        = (fun (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) =>
            Fin.cases (z 0) (fun i : Fin n => φ i (Fin.snoc l (z 0)) (Fin.tail z)) j) := by
      funext l z
      exact Work.WilkG4c.pullbackMap_eq_cases φ l z j
    rw [hfun]
    exact h
  constructor
  · intro j
    exact Work.WilkG4c.Omega_mono_le S (by omega) (by omega) (hχ j)
  · intro i
    have hmain := hcomp F0 (a₁ + aphi) D (Dg₁ + cphi) (F i)
      (fun j l z => Work.WilkG4c.pullbackMap φ l z j) (hF i) hχ
    rw [show (fun (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) =>
          F i l (fun j => Work.WilkG4c.pullbackMap φ l z j))
        = Work.WilkG4c.yPullback F φ i from rfl] at hmain
    refine Work.WilkG4c.Omega_mono_le S (by omega) ?_ hmain
    have h1 : Dg₁ + cphi ≤ Dg₁ + max cphi ccomp := by omega
    have h3 := Nat.mul_le_mul_left (p + (n + 1)) h1
    omega
