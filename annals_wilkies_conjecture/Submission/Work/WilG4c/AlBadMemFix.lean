/-
  WilG4c / `AlBadMemFix` — the degenerate ("bad") region `AlBad` of BNZ §5.2/§5.4 is
  `Ω`-definable, with a format independent of `D` and `|L|` and a degree polynomial in `D` and
  `|L|`; likewise for its projection `AlBadPar` to the parameter coordinates.

  This is `Work.WilkG4c.AlBadMem` with the (unused) hypothesis `S.SharpCD` dropped, and with the
  projection step `AlBadPar = projLastIter p (n+2) AlBad` proved here rather than imported.

  ## The inputs

  * `StepBadLoc` (proved, `Submission/Work/WilG4c/StepBadLoc.lean`): for a family whose graph is
    `Ω F0 D`, the complement `badLoc f m` of the interior of the joint `C^m`-locus of the family
    member is `Ω`-definable with a format `a0` *uniform in the order `m`* and degree
    `b0.eval ![D, r]` for any `r ≥ m`.  This is `SOMin.SharpDeriv` read through the projection
    dropping the value coordinate (`projLast_dgSet`); `jBad = badLoc`.
  * `FibreBallMem` (proved, `Submission/Work/WilkG4c/FibreBallMem.lean`): for any `Ω`-set
    `V ⊆ ℝ^{p+(n+1)}` there are constants `A, C` with
    `{z | ∃ y₀ ε, 0 < ε ∧ ∀ y, dist y y₀ < ε → fibPt (Fin.init z) y ∈ V} ∈ Ω (F+A) (D+C)`.
    This is the "a whole fibre ball is contained in `V`" localisation, coded by the usual
    `∃`/`∀`-to-projection/complement translation inside the auxiliary space `(z, ε, y₀, y)`.

  ## The proof

  `AlBad p n f L = ⋃ k : Fin (|L|+1), AlBadK p n f k`, and `AlBadK p n f k` is the `FibreBallMem`
  set at `V = jBad p n f k`.  For each `k ≤ |L|`, `StepBadLoc` gives `jBad p n f k ∈ Ω a0
  (b0.eval ![D, |L|])` — the *same* format `a0` and the *same* degree for every `k ≤ |L|` — so the
  union over the `|L|+1` pieces costs only a factor `|L|+1` in the degree, absorbed by the
  polynomial `(X 1 + 1) * (b0 + C)` evaluated at `![D, |L|]`.  The projection to `AlBadPar` then
  costs `n+2` in the format and nothing in the degree.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4c.AlSliceBase
import Submission.Work.WilG4c.StepBadLoc
import Submission.Work.WilG1.Basic
import Submission.Work.WilG4c.FibreBallMem
import Submission.Work.WilG4c.FibreLimitPiBasic
import Submission.Work.WilG0.projLastIter_mem

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-! ## The parameter projection is the iterated projection -/

/-- `AlBadPar` is the iterated projection `projLastIter p (n+2)` of `AlBad`: the latter drops
the cube point (`n+1` coordinates) and the value coordinate. -/
theorem AlBadPar_eq_projLastIter (p n : ℕ)
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))) :
    Work.WilkG4c.AlBadPar p n f L =
      Work.WilG0.projLastIter p (n + 2) (Work.WilkG4c.AlBad p n f L) := by
  rw [Work.WilG0.projLastIter_eq]
  ext l
  constructor
  · rintro ⟨u, s, h⟩
    refine ⟨Fin.snoc u s, ?_⟩
    rwa [Work.WilG4c.snocIt_append, Fin.append_snoc]
  · rintro ⟨x, hx⟩
    rw [Work.WilG4c.snocIt_append] at hx
    refine ⟨Fin.init x, x (Fin.last (n + 1)), ?_⟩
    rwa [← Fin.append_snoc, Fin.snoc_init_self]

/-! ## The main theorem -/

theorem AlBadMemFix (S : WilkiesDesign.SOMin) (hder : WilkiesDesign.SOMin.SharpDeriv S)
    (p n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))),
        WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
        (Work.WilkG4c.AlBad p n f L ∈ S.Ω a (MvPolynomial.eval ![D, L.length] b) (p + (n + 1) + 1)) ∧
        (Work.WilkG4c.AlBadPar p n f L ∈ S.Ω a (MvPolynomial.eval ![D, L.length] b) p) := by
  obtain ⟨a0, b0, hBad⟩ := StepBadLoc S hder p (n + 1) F0
  obtain ⟨A, C, hBall'⟩ := Work.WilkG4c.FibreBallMem S p n
  refine ⟨a0 + A + (n + 2) + p, (MvPolynomial.X 1 + 1) * (b0 + MvPolynomial.C C),
    fun D f L hf => ?_⟩
  -- each order `k ≤ |L|` contributes the same format `a0 + A` and the same degree
  have hK : ∀ i : Fin (L.length + 1), Work.WilkG4c.AlBadK p n f i.val ∈
      S.Ω (a0 + A) (MvPolynomial.eval ![D, L.length] b0 + C) (p + (n + 1) + 1) := by
    intro i
    have hb := hBad D L.length f hf i.val (by omega)
    exact hBall' a0 (MvPolynomial.eval ![D, L.length] b0) (Work.WilkG4c.jBad p n f i.val) hb
  -- the union over the `|L| + 1` orders
  have hAlBad : Work.WilkG4c.AlBad p n f L ∈
      S.Ω (a0 + A) (∑ _i : Fin (L.length + 1), (MvPolynomial.eval ![D, L.length] b0 + C))
        (p + (n + 1) + 1) :=
    S.union (F := a0 + A)
      (D := fun _ : Fin (L.length + 1) => MvPolynomial.eval ![D, L.length] b0 + C)
      (A := fun i : Fin (L.length + 1) => Work.WilkG4c.AlBadK p n f i.val) hK
  -- the degree of the union, as the value of the chosen degree polynomial at `![D, |L|]`
  have hb_eval : MvPolynomial.eval ![D, L.length]
      ((MvPolynomial.X 1 + 1) * (b0 + MvPolynomial.C C))
      = (L.length + 1) * (MvPolynomial.eval ![D, L.length] b0 + C) := by
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_add, MvPolynomial.eval_add,
      MvPolynomial.eval_X, MvPolynomial.eval_C]
    norm_num
  have hsum_eq : (∑ _i : Fin (L.length + 1), (MvPolynomial.eval ![D, L.length] b0 + C))
      = (L.length + 1) * (MvPolynomial.eval ![D, L.length] b0 + C) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp
  have hAlBad' : Work.WilkG4c.AlBad p n f L ∈ S.Ω (a0 + A)
      (MvPolynomial.eval ![D, L.length]
        ((MvPolynomial.X 1 + 1) * (b0 + MvPolynomial.C C))) (p + (n + 1) + 1) :=
    Work.WilG1.Omega.mono hAlBad le_rfl (Nat.le_of_eq (by rw [hb_eval, hsum_eq]))
  -- the parameter projection
  have hP := Work.WilG0.projLastIter_mem S p (n + 2) (a0 + A)
      (MvPolynomial.eval ![D, L.length] ((MvPolynomial.X 1 + 1) * (b0 + MvPolynomial.C C)))
      (Work.WilkG4c.AlBad p n f L) hAlBad'
  rw [← AlBadPar_eq_projLastIter p n f L] at hP
  exact ⟨Work.WilG1.Omega.mono hAlBad' (by omega) le_rfl,
    Work.WilG1.Omega.mono hP (by omega) le_rfl⟩

end Work.WilG4c
