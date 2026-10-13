/-
  WilG4c — `StepEngAux2`: the *near-maximality transfer* from the original member to the affine
  `x`-pullback, i.e. BNZ's observation that the affine chart `φ_η` contributes only the factor
  `(φ_η')^{α₁}` to `F^{(α)}` — a factor which cancels in the ratio of the near-maximality
  inequality (BNZ eq. `Gamma-i-alpha-cond`).

  The mechanism: for the direction list `L = replicate j 0 ++ M.map Fin.succ`,
  `Work.WilG4c.iterDir_pullX` gives
  `iterDir L (pullX f) (pt x y) = β ^ (xcount L) * iterDir L f (pt (α + β * x) y)`
  both at the point `(x,y)` and at the curve point `(x, γ j M (α + β * x))`; since
  `xcount L = j` the two factors `β ^ j` are equal and positive, so the near-maximality of `f`
  in its own coordinates transports to the pullback, with the curve transported from the
  `f`-coordinate `α + β x` to the pullback coordinate `x`.
-/
import Mathlib
import Submission.Work.WilG4c.StepEngAux
import Submission.Work.WilG4c.iterDir_pullX
import Submission.Work.WilG4c.contDiffAt_affine_pullback_iff
import Submission.Work.WilG4c.iterDir_perm
import Submission.Work.WilG4c.StepHigherDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- The number of `x`-directions in `replicate j 0 ++ M.map Fin.succ` is `j`. -/
theorem xcount_replicate_map {n j : ℕ} (M : List (Fin n)) :
    xcount (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) = j := by
  have hnil : List.filter (fun i => decide (i = (0 : Fin (n + 1)))) (M.map Fin.succ) = [] := by
    rw [List.filter_eq_nil_iff]
    intro b hb
    rw [List.mem_map] at hb
    obtain ⟨c, _, rfl⟩ := hb
    simp [Fin.succ_ne_zero]
  rw [xcount, List.filter_append, List.filter_replicate, hnil, List.length_append,
    List.length_nil, Nat.add_zero]
  simp [List.length_replicate]

/-- **The near-maximality transfer from a member to its affine `x`-pullback.**  If `f` is
near-maximised (up to the factor `2`) along the curves `γ j M` on the fibre, off a finite bad
set `B` of `x`-coordinates, then the pullback `u ↦ f (α + β u 0, tail u)` is near-maximised
along the *transported* curves `x ↦ γ j M (α + β x)`, off the transported bad set
(`α + β x ∉ B`).

The chart conditions `0 < β`, `0 ≤ α`, `α + β ≤ 1` are what keep the transported good
`x`-coordinates inside `I`; `hγsm` is the smoothness of `f` at the curve points (supplied by the
sliced choice lemma), and `β ≠ 0` is needed to transport `ContDiffAt` through the affine chart
(`Work.WilG4c.contDiffAt_affine_pullback_iff`). -/
theorem hmax_pullback {n r : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (α β : ℝ)
    (hβ0 : 0 < β) (hα0 : 0 ≤ α) (hαβ : α + β ≤ 1) (B : Finset ℝ)
    (γ : (j : ℕ) → List (Fin n) → ℝ → Fin n → ℝ)
    (hmaxf : ∀ (j : ℕ) (M : List (Fin n)) (x : ℝ) (y : Fin n → ℝ), j + M.length ≤ r →
      x ∈ I → x ∉ (B : Set ℝ) → y ∈ openCube n →
      ContDiffAt ℝ (j + M.length) f (pt x y) →
      |iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) f (pt x y)| ≤
        2 * |iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) f
              (curveFun (γ j M) x)|)
    (hγsm : ∀ (j : ℕ) (M : List (Fin n)) (x : ℝ), j + M.length ≤ r → x ∈ I →
      x ∉ (B : Set ℝ) →
      ContDiffAt ℝ (j + M.length) f (pt x (γ j M x))) :
    ∀ (j : ℕ) (M : List (Fin n)) (x : ℝ) (y : Fin n → ℝ), j + M.length ≤ r → x ∈ I →
      α + β * x ∉ (B : Set ℝ) → y ∈ openCube n →
      ContDiffAt ℝ (j + M.length)
        (fun u : Fin (n + 1) → ℝ => f (pt (α + β * u 0) (Fin.tail u))) (pt x y) →
      |iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ)
          (fun u : Fin (n + 1) → ℝ => f (pt (α + β * u 0) (Fin.tail u))) (pt x y)| ≤
        2 * |iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ)
          (fun u : Fin (n + 1) → ℝ => f (pt (α + β * u 0) (Fin.tail u)))
          (curveFun (fun s : ℝ => γ j M (α + β * s)) x)| := by
  intro j M x y hjm hx hxB hy hG
  set L : List (Fin (n + 1)) := List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ with hL
  set Gp : (Fin (n + 1) → ℝ) → ℝ :=
    fun u : Fin (n + 1) → ℝ => f (pt (α + β * u 0) (Fin.tail u)) with hGp
  have hlen : L.length = j + M.length := by
    rw [hL, List.length_append, List.length_replicate, List.length_map]
  have hxc : xcount L = j := by rw [hL]; exact xcount_replicate_map M
  -- the transported `x`-coordinate stays inside `I`
  have hx' : α + β * x ∈ I := by
    have hx1 : 0 < x := hx.1
    have hx2 : x < 1 := hx.2
    have hβx : β * x < β := by simpa using mul_lt_mul_of_pos_left hx2 hβ0
    exact ⟨by nlinarith, by nlinarith⟩
  -- smoothness of `f` at the two image points
  have hβne : β ≠ 0 := ne_of_gt hβ0
  have hcast : ((L.length : ℕ) : WithTop ℕ∞)
      = ((j : WithTop ℕ∞) + (M.length : WithTop ℕ∞)) := by
    rw [hlen, Nat.cast_add]
  have hG' : ContDiffAt ℝ L.length Gp (pt x y) := hcast ▸ hG
  have hGf : ContDiffAt ℝ L.length f (pt (α + β * x) y) := by
    refine (Work.WilG4c.contDiffAt_affine_pullback_iff f α β hβne (pt x y)).mp ?_
    rw [hGp] at hG'
    exact hG'
  have hGfj : ContDiffAt ℝ (j + M.length) f (pt (α + β * x) y) := hcast.symm ▸ hGf
  have hGfc : ContDiffAt ℝ L.length f (pt (α + β * x) (γ j M (α + β * x))) :=
    hcast ▸ hγsm j M (α + β * x) (by omega) hx' hxB
  -- the two applications of the affine transport
  have hLHS : iterDir L Gp (pt x y) = β ^ j * iterDir L f (pt (α + β * x) y) := by
    rw [Work.WilG4c.iterDir_pullX f α β x y L hGf, hxc]
  have hRHS : iterDir L Gp (curveFun (fun s : ℝ => γ j M (α + β * s)) x)
      = β ^ j * iterDir L f (pt (α + β * x) (γ j M (α + β * x))) := by
    have hpt : curveFun (fun s : ℝ => γ j M (α + β * s)) x = pt x (γ j M (α + β * x)) := rfl
    rw [hpt]
    rw [Work.WilG4c.iterDir_pullX f α β x (γ j M (α + β * x)) L hGfc, hxc]
  rw [hLHS, hRHS]
  -- the near-maximality of `f` in its own coordinates, and the cancellation of `β ^ j`
  have hmain := hmaxf j M (α + β * x) y (by omega) hx' hxB hy hGfj
  have hpos : (0 : ℝ) < β ^ j := pow_pos hβ0 j
  have h2 : β ^ j * |iterDir L f (pt (α + β * x) y)|
      ≤ 2 * (β ^ j * |iterDir L f (pt (α + β * x) (γ j M (α + β * x)))|) := by
    have hcurve : curveFun (γ j M) (α + β * x) = pt (α + β * x) (γ j M (α + β * x)) := rfl
    rw [hcurve] at hmain
    calc β ^ j * |iterDir L f (pt (α + β * x) y)|
        ≤ β ^ j * (2 * |iterDir L f (pt (α + β * x) (γ j M (α + β * x)))|) :=
          mul_le_mul_of_nonneg_left hmain hpos.le
      _ = 2 * (β ^ j * |iterDir L f (pt (α + β * x) (γ j M (α + β * x)))|) := by ring
  simpa only [abs_mul, abs_of_pos hpos] using h2

end Work.WilkG4c
