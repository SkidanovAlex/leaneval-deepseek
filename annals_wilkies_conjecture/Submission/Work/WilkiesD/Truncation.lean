import Submission.Work.WilkiesD.Basic
import Submission.Work.WilkiesD.Proj
import Submission.Work.WilkiesD.Omg.projFst_mem_Omega
import Submission.Work.WilkiesD.Cover.projFst_boxZero_subset
import Submission.Work.WilkiesD.Cover.exists_M_cover
import Submission.Work.WilkiesD.Poly.eval_subst_first_const

/-!
# Area D — truncation and bookkeeping

This file contains the main theorem of area D, `D_truncation_proved`, together with the
intermediate three-variable form `truncation_three_var`.  The four auxiliary lemmas it uses are
proved in `Submission/Work/WilkiesD/Omg`, `.../Cover` and `.../Poly`:

* `Omg.projFst_mem_Omega` — the `m`-fold projection `projFst` adds `m` to the format counter and
  leaves the degree counter alone,
* `Cover.projFst_boxZero_subset` — `projFst m (boxZero M P) ⊆ X` (the `X_M ⊆ X` half),
* `Cover.exists_M_cover` — one `M` covers the witnesses of a whole finite set `T ⊆ X`,
* `Poly.eval_subst_first_const` — fixing the first variable of a three-variable polynomial.

The argument.  Let `X = {x | ∃ y, expPolyEval P (Fin.append x y) = 0}` be the witness
presentation of an `ExpExist` set and let `F, D` be the format and degree of `boxZero M P`
in `S.Ω`, which by `hbox` do not depend on `M`.  For a finite set `T ⊆ degreeHeightLE X.trans g H`
we choose a single `M` large enough to contain a witness of every point of `T`, and put
`X_M := projFst m (boxZero M P)`.  Then `X_M ⊆ X`, `X_M ∈ S.Ω (F + m) D n` with `F + m` and `D`
independent of `M`, and monotonicity of `Set.alg` (`alg_mono`, through
`subset_degreeHeightLE_trans`) gives `T ⊆ degreeHeightLE X_M.trans g H`.  The counting
hypothesis `hcount` therefore bounds `T.card` by a polynomial in `D, g, log H` with `D` fixed,
and fixing the first variable of that three-variable polynomial yields the two-variable
polynomial of the statement.  If `degreeHeightLE X.trans g H` is infinite instead, `Nat.card`
is `0`, while the right-hand side is nonnegative because `hcount` may be applied to `T = ∅`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilkiesD
open WilkiesDesign WilkiesConjecture

/-- **Area D, three-variable form.**  Under the truncation hypothesis `hbox` (area E) and the
counting hypothesis `hcount` (area H), the number of points of `X.trans(g,H)` is bounded by a
single three-variable polynomial `q` evaluated at `(D, g, log H)`, where `D` is the degree of the
truncated zero sets.  Both `D` and `q` are independent of `g` and `H`. -/
theorem truncation_three_var (S : SOMin)
    (hbox : ∀ N d : ℕ, ∃ F D : ℕ, ∀ (M : ℝ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ),
      P.totalDegree ≤ d → boxZero M P ∈ S.Ω F D N)
    (hcount : ∀ F n : ℕ, CountBound S F n)
    {n : ℕ} (X : Set (Fin n → ℝ)) (hX : ExpExist X) :
    ∃ (D : ℕ) (q : MvPolynomial (Fin 3) ℝ), ∀ (g H : ℕ),
      (Nat.card (degreeHeightLE X.trans g H) : ℝ) ≤ q.eval ![(D : ℝ), (g : ℝ), Real.log H] := by
  obtain ⟨m, P, hPX⟩ := hX
  obtain ⟨F, D, hboxF⟩ := hbox (n + m) P.totalDegree
  obtain ⟨q, hq⟩ := hcount (F + m) n
  -- `X_M := projFst m (boxZero M P)` has format `F + m` and degree `D` for every `M`, and
  -- it lies in `X`.
  have hmem : ∀ M : ℝ, projFst m (boxZero M P) ∈ S.Ω (F + m) D n := fun M =>
    Omg.projFst_mem_Omega m F D _ (hboxF M P le_rfl)
  have hsub : ∀ M : ℝ, projFst m (boxZero M P) ⊆ X := fun M =>
    Cover.projFst_boxZero_subset hPX M
  refine ⟨D, q, fun g H => ?_⟩
  -- The right-hand side is nonnegative, by applying the count to the empty set.
  have hnonneg : 0 ≤ q.eval ![(D : ℝ), (g : ℝ), Real.log H] := by
    have h0 := hq D (projFst m (boxZero 0 P)) (hmem 0) g H ∅ (by simp)
    simpa using h0
  rcases Set.finite_or_infinite (degreeHeightLE X.trans g H) with hfin | hinf
  · -- finite case: bound the witnesses of all points of `T` at once
    have hTA : (↑(hfin.toFinset) : Set (Fin n → ℝ)) = degreeHeightLE X.trans g H :=
      hfin.coe_toFinset
    have hTX : (↑(hfin.toFinset) : Set (Fin n → ℝ)) ⊆ X := by
      intro x hx
      rw [hTA] at hx
      exact trans_subset hx.1
    obtain ⟨M, hM⟩ := Cover.exists_M_cover hPX hfin.toFinset hTX
    have hTbound : (↑(hfin.toFinset) : Set (Fin n → ℝ)) ⊆
        degreeHeightLE (projFst m (boxZero M P)).trans g H :=
      subset_degreeHeightLE_trans (hsub M) (le_of_eq hTA) hM
    have hc := hq D (projFst m (boxZero M P)) (hmem M) g H hfin.toFinset hTbound
    rw [Nat.card_eq_card_finite_toFinset hfin]
    exact hc
  · -- infinite case: `Nat.card` vanishes and the right-hand side is nonnegative
    rw [hinf.card_eq_zero]
    simpa using hnonneg

/-- **Area D (truncation and polynomial bookkeeping).**  The counting bound for
`X.trans(g,H)`, with the degree `D` of the truncated zero sets substituted into the polynomial,
in the exact two-variable form required by the challenge statement. -/
theorem D_truncation_proved (S : SOMin)
    (hbox : ∀ N d : ℕ, ∃ F D : ℕ, ∀ (M : ℝ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ),
      P.totalDegree ≤ d → boxZero M P ∈ S.Ω F D N)
    (hcount : ∀ F n : ℕ, CountBound S F n)
    {n : ℕ} (X : Set (Fin n → ℝ)) (hX : ExpExist X) :
    ∃ f : MvPolynomial (Fin 2) ℝ, ∀ (g H : ℕ),
      Nat.card (degreeHeightLE X.trans g H) ≤ f.eval ![(g : ℝ), Real.log H] := by
  obtain ⟨D, q, hq⟩ := truncation_three_var S hbox hcount X hX
  obtain ⟨f, hf⟩ := Poly.eval_subst_first_const D q
  refine ⟨f, fun g H => ?_⟩
  rw [hf (g : ℝ) (Real.log H)]
  exact hq g H

end Work.WilkiesD
