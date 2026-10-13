import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4c.NormIteratedFDerivCompLinearGeneral

/-!
# Pulling a unit-jet `C^r` function back along `Fin.tail`

`Fin.tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ)` is the linear projection forgetting the first
coordinate.  Composing with it preserves `C^r` on the open cube, and it cannot increase the
operator norm of an iterated derivative: the `m`-th derivative of `f ∘ Fin.tail` at `t` is the
`m`-th derivative of `f` at `Fin.tail t` composed with `Fin.tail` in each variable
(`Work.WilG4c.NormIteratedFDerivCompLinearGeneral`), and `‖Fin.tail‖ ≤ 1`.
-/

namespace Work.WilkG4c

noncomputable section

/-- The open cube of `ℝ^N` is open.  (A local copy of the same three-line lemma that appears in
`Submission.Work.WilG4c.EngineCover`, kept here to avoid importing the per-cell engine.) -/
private theorem isOpen_openCube_tail (N : ℕ) : IsOpen (WilkiesDesign.openCube N) := by
  have h : WilkiesDesign.openCube N
      = Set.pi Set.univ (fun _ : Fin N => Set.Ioo (0 : ℝ) 1) := by
    ext t
    simp [WilkiesDesign.openCube]
  rw [h]
  exact isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)

/-! ### `Fin.tail` as a continuous linear map -/

/-- `Fin.tail` (forget the first coordinate of a tuple) as a continuous linear map. -/
private def tailL (n : ℕ) : (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin n =>
    (ContinuousLinearMap.proj i.succ : (Fin (n + 1) → ℝ) →L[ℝ] ℝ)

private theorem tailL_apply_point (n : ℕ) (x : Fin (n + 1) → ℝ) (i : Fin n) :
    tailL n x i = x i.succ := by
  simp [tailL]

private theorem tailL_apply (n : ℕ) (x : Fin (n + 1) → ℝ) : tailL n x = Fin.tail x := by
  funext i
  rw [tailL_apply_point]
  rfl

/-- The operator norm of `Fin.tail` is at most `1`. -/
private theorem norm_tailL_le (n : ℕ) : ‖tailL n‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  intro i
  rw [tailL_apply_point]
  exact norm_le_pi_norm x i.succ

/-- The tail of a point of the open `(n+1)`-cube lies in the open `n`-cube. -/
private theorem tail_mem_openCube {n : ℕ} {x : Fin (n + 1) → ℝ}
    (hx : x ∈ WilkiesDesign.openCube (n + 1)) : Fin.tail x ∈ WilkiesDesign.openCube n :=
  fun i => hx i.succ

private theorem tailL_mem (n : ℕ) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ WilkiesDesign.openCube (n + 1)) : tailL n x ∈ WilkiesDesign.openCube n := by
  rw [tailL_apply]
  exact tail_mem_openCube hx

theorem TailPullbackNorm {n r : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hc : ContDiffOn ℝ r f (WilkiesDesign.openCube n))
    (hn : ∀ m, m ≤ r → ∀ u ∈ WilkiesDesign.openCube n, ‖iteratedFDeriv ℝ m f u‖ ≤ 1) :
    ContDiffOn ℝ r (fun t : Fin (n + 1) → ℝ => f (Fin.tail t)) (WilkiesDesign.openCube (n + 1)) ∧
      ∀ m, m ≤ r → ∀ t ∈ WilkiesDesign.openCube (n + 1),
        ‖iteratedFDeriv ℝ m (fun t : Fin (n + 1) → ℝ => f (Fin.tail t)) t‖ ≤ 1 := by
  have hmono : WilkiesDesign.openCube (n + 1) ⊆ (tailL n) ⁻¹' WilkiesDesign.openCube n :=
    fun x hx => tailL_mem n hx
  refine ⟨?_, ?_⟩
  · have h : ContDiffOn ℝ r (f ∘ ⇑(tailL n)) (WilkiesDesign.openCube (n + 1)) :=
      (hc.comp_continuousLinearMap (tailL n)).mono hmono
    have hfe : (fun t : Fin (n + 1) → ℝ => f (Fin.tail t)) = (f ∘ ⇑(tailL n)) := by
      funext y
      rw [Function.comp_apply, tailL_apply]
    rw [hfe]
    exact h
  · intro m hm t ht
    have hLt : Fin.tail t ∈ WilkiesDesign.openCube n := tail_mem_openCube ht
    have hfun : (fun t : Fin (n + 1) → ℝ => f (Fin.tail t))
        = fun y : Fin (n + 1) → ℝ => f (tailL n y) := by
      funext y
      rw [tailL_apply]
    have hAt : ContDiffAt ℝ m f (tailL n t) := by
      rw [tailL_apply]
      exact (hc.of_le (by exact_mod_cast hm)).contDiffAt
        ((isOpen_openCube_tail n).mem_nhds hLt)
    have h := Work.WilG4c.NormIteratedFDerivCompLinearGeneral (tailL n) f t m hAt
    rw [hfun]
    calc ‖iteratedFDeriv ℝ m (fun y : Fin (n + 1) → ℝ => f (tailL n y)) t‖
        ≤ ‖iteratedFDeriv ℝ m f (tailL n t)‖ * ‖tailL n‖ ^ m := h
      _ ≤ 1 * 1 := mul_le_mul (by rw [tailL_apply]; exact hn m hm (Fin.tail t) hLt)
            (pow_le_one₀ (norm_nonneg _) (norm_tailL_le n)) (by positivity) (by norm_num)
      _ = 1 := one_mul 1

end

end Work.WilkG4c
