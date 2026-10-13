import Mathlib
import Submission.Work.WilG4c.StepLipPieces

namespace Work.WilkG4c

/-- If `F` is `C¹` at every point of a set `s`, then for any direction `v` the directional
derivative `w ↦ fderiv ℝ F w v` is continuous on `s`.  (`fderiv ℝ F` is continuous on `s` by
`ContDiffAt.continuousAt_fderiv`, and evaluation at `v` is a continuous linear map.) -/
theorem continuousOn_fderiv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {s : Set E} (h : ∀ w ∈ s, ContDiffAt ℝ 1 F w) (v : E) :
    ContinuousOn (fun w => fderiv ℝ F w v) s := by
  have hfd : ContinuousOn (fderiv ℝ F) s :=
    fun x hx => ((h x hx).continuousAt_fderiv (by norm_num)).continuousWithinAt
  exact (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp_continuousOn hfd

/-- **From the comparison dichotomy on a cell to a dominating member.**  Let `C` be a finite
family of subsets of `ℝ^{p+1}` (in the intended use: the cells of a cylindrical decomposition of
`ℝ^{p+1}`), all cells preconnected and nonempty, `T` a tuple of `k ≥ 1` one-variable families
over `Fin p → ℝ`, all `C¹` on every cell, and suppose that for every pair `a b` and every cell
`κ`, `κ` is either contained in the comparison set `{|∂_s T_a| = |∂_s T_b|}` or disjoint from it
(this is the dichotomy that `S.SharpCD` produces when `C` refines those sets).  Then on each
cell there is an index `i` whose `s`-derivative dominates the absolute values of the
`s`-derivatives of all the members, at every point of the cell.

The argument: for a pair `a b` with `κ` disjoint from the comparison set, the function
`w ↦ |∂_s T_a(w)| − |∂_s T_b(w)|` is continuous on the preconnected cell (the derivatives are
continuous there because the members are `C¹`) and never vanishes, hence has constant sign; if
`κ` is contained in the comparison set, the two absolute values agree on `κ`.  Picking at one
point of the cell an index maximising `|∂_s|` and comparing it with every other index gives the
claim. -/
theorem DominatingCell (S : WilkiesDesign.SOMin) (p k : ℕ) (hk : 1 ≤ k) :
    ∀ (C : Finset (Set (Fin (p + 1) → ℝ)))
        (T : Fin k → (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ),
        (∀ κ ∈ C, IsPreconnected κ) →
        (∀ κ ∈ C, κ.Nonempty) →
        (∀ κ ∈ C, ∀ i : Fin k, ∀ w ∈ κ, ContDiffAt ℝ 1 (fun z : Fin (p + 1) → ℝ =>
            T i (Fin.init z) (fun _ : Fin 1 => z (Fin.last p))) w) →
        (∀ a b : Fin k, ∀ κ ∈ C,
            κ ⊆ {w : Fin (p + 1) → ℝ |
                |fderiv ℝ (fun z : Fin (p + 1) → ℝ =>
                    T a (Fin.init z) (fun _ : Fin 1 => z (Fin.last p))) w
                  (Pi.single (Fin.last p) 1)|
              = |fderiv ℝ (fun z : Fin (p + 1) → ℝ =>
                    T b (Fin.init z) (fun _ : Fin 1 => z (Fin.last p))) w
                  (Pi.single (Fin.last p) 1)|}
            ∨ Disjoint κ {w : Fin (p + 1) → ℝ |
                |fderiv ℝ (fun z : Fin (p + 1) → ℝ =>
                    T a (Fin.init z) (fun _ : Fin 1 => z (Fin.last p))) w
                  (Pi.single (Fin.last p) 1)|
              = |fderiv ℝ (fun z : Fin (p + 1) → ℝ =>
                    T b (Fin.init z) (fun _ : Fin 1 => z (Fin.last p))) w
                  (Pi.single (Fin.last p) 1)|}) →
        ∀ κ ∈ C, ∃ i : Fin k, ∀ a : Fin k, ∀ w ∈ κ,
            |fderiv ℝ (fun z : Fin (p + 1) → ℝ =>
                T a (Fin.init z) (fun _ : Fin 1 => z (Fin.last p))) w
              (Pi.single (Fin.last p) 1)|
          ≤ |fderiv ℝ (fun z : Fin (p + 1) → ℝ =>
                T i (Fin.init z) (fun _ : Fin 1 => z (Fin.last p))) w
              (Pi.single (Fin.last p) 1)| := by
  intro C T hconn hne hC1 hdich κ hκC
  -- Abbreviation for the `s`-directional derivative of the `a`-th family.
  let D : Fin k → (Fin (p + 1) → ℝ) → ℝ := fun a w =>
    fderiv ℝ (fun z : Fin (p + 1) → ℝ =>
        T a (Fin.init z) (fun _ : Fin 1 => z (Fin.last p))) w (Pi.single (Fin.last p) 1)
  -- A point of the (nonempty) cell, and an index maximising `|D ·|` there.
  obtain ⟨w0, hw0⟩ := hne κ hκC
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin k)) (fun a => |D a w0|)
      ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  refine ⟨i, ?_⟩
  intro a w hw
  -- The directional derivatives are continuous on the cell.
  have hDa : ContinuousOn (fun w => D a w) κ :=
    continuousOn_fderiv_apply (s := κ)
      (F := fun z : Fin (p + 1) → ℝ =>
        T a (Fin.init z) (fun _ : Fin 1 => z (Fin.last p)))
      (fun w hw => hC1 κ hκC a w hw) (Pi.single (Fin.last p) 1)
  have hDi : ContinuousOn (fun w => D i w) κ :=
    continuousOn_fderiv_apply (s := κ)
      (F := fun z : Fin (p + 1) → ℝ =>
        T i (Fin.init z) (fun _ : Fin 1 => z (Fin.last p)))
      (fun w hw => hC1 κ hκC i w hw) (Pi.single (Fin.last p) 1)
  rcases hdich a i κ hκC with hsub | hdisj
  · -- The cell is contained in the comparison set: the two absolute values agree there.
    exact le_of_eq (hsub hw)
  · -- The cell is disjoint from the comparison set: the difference never vanishes ...
    have hne0 : ∀ x ∈ κ, (|D a x| - |D i x|) ≠ 0 := by
      intro x hx h0
      exact (Set.disjoint_left.mp hdisj) hx (sub_eq_zero.mp h0)
    -- ... hence, by preconnectedness, has constant sign on the cell.
    rcases (hconn κ hκC).mapsTo_Ioi_or_Iio (hDa.abs.sub hDi.abs) hne0 with hpos | hneg
    · -- Positive sign: at `w0` this contradicts the maximality of `i`.
      exfalso
      have h1 : 0 < |D a w0| - |D i w0| := hpos hw0
      have h2 : |D a w0| ≤ |D i w0| := hi a (Finset.mem_univ a)
      linarith
    · -- Negative sign: `i` dominates `a` on the whole cell.
      have h1 : |D a w| - |D i w| < 0 := hneg hw
      linarith

end Work.WilkG4c
