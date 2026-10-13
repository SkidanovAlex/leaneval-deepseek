import Mathlib
import Submission.Work.WilkiesH.Count.Interface
import Submission.Work.WilkiesH.Count.Defs
import Submission.Work.WilkiesH.Strat.Defs
import Submission.Work.WilkiesH.Dim.dimLE_mono
import Submission.Work.WilkiesH.Count.poly_bookkeeping_strat_max

/-!
# Area H (counting) — the dimension induction step

This is the restated step of the counting induction of BNZ §6.  It replaces the earlier
`Count/countBoundDimCube_step` (retired in this directory, see `ARCHITECTURE.md` §7.8/§7.9),
which split the cells of a sharp cell decomposition on `CellDimLE`; that split is invalid
(`CellDimLE` does not imply `DimLE`, a Peano-curve cell being the counterexample), and the
block input had to be replaced by the stratification input.

The step now has only two inputs:

* the interpolation step in the form `ChartCover S F n` (area (I));
* the stratification input `StratInput S` (BNZ §2.3, area (B)).

No sharp cell decomposition is used: the dimension bookkeeping is done by `DimLE` alone, and
the stratification input carries the "regular strata vs. thin remainder" content.

Given a set `X ∈ S.Ω F D n`, `X ⊆ cube01 n`, `DimLE X μ`, and points
`T ⊆ degreeHeightLE X.trans g H`, the argument is:

1. with `ν = min μ n` (so that charts `I^ν → X` exist, as `ChartCover` requires `ν ≤ n`),
   `ChartCover` produces `mv ≤ p(D,g,log H)` semialgebraic `Ω`-sets `V i` of dimension `≤ ν`,
   of degree index `d ≤ q(D,g,log H)`, covering `T`;
2. a point of `T` lies in `X.trans` and in `X ∩ V i`, hence in `(X ∩ V i) \ X.alg`, so
   `StratInput` covers it by one of `mi` pieces `W i j`, each of dimension `≤ ν - 1 ≤ μ - 1`,
   each contained in `X` and each of format `a₀` and degree index `c.eval (D + d)`;
3. each piece is counted by the induction hypothesis at `μ - 1` (a point of `T` in a piece
   `W` is in `W.trans`, since `W.alg ⊆ X.alg` does not contain it);
4. the sum `∑ᵢ mᵢ ≤ mv · pm(D+d, n+1)` times the induction bound at degree `c.eval (D + d)`
   is a polynomial in `(D, g, log H)` by `poly_bookkeeping_strat_max`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical

namespace Work.WilkiesH.Count

open WilkiesDesign WilkiesConjecture

/-- **The dimension induction step of BNZ §6.** -/
theorem countBoundDimCube_step {S : SOMin} (hstr : StratInput S) {F n μ : ℕ}
    (IH : ∀ F' : ℕ, CountBoundDimCube S F' n (μ - 1))
    (hI : ChartCover S F n) : CountBoundDimCube S F n μ := by
  obtain ⟨a, p, q, hI'⟩ := hI
  -- `StratInput` is applied at the format `max F a`, so that both `X` (format `F`) and the
  -- interpolation sets `V i` (format `a`) are available to it, by monotonicity in the format.
  obtain ⟨a₀, pm, c, hstr'⟩ := hstr (max F a) n
  rcases Nat.eq_zero_or_pos μ with h0 | hpos
  · subst h0
    exact IH F
  obtain ⟨fIH, hfIH⟩ := IH a₀
  obtain ⟨Ffin, hFfin⟩ := poly_bookkeeping_strat_max (n := n) pm c p q fIH
  refine ⟨Ffin, fun D X hX hcube hdim g H T hT => ?_⟩
  set ν : ℕ := min μ n with hνdef
  have hνn : ν ≤ n := Nat.min_le_right μ n
  have hνμ : ν ≤ μ := Nat.min_le_left μ n
  have hdimν : DimLE X ν := by
    rcases le_total μ n with hle | hle
    · rw [hνdef, Nat.min_eq_left hle]; exact hdim
    · rw [hνdef, Nat.min_eq_right hle]; exact Work.WilkiesH.dimLE_top X
  have hTX : (↑T : Set (Fin n → ℝ)) ⊆ X := fun x hx => Work.WilkiesH.trans_subset X (hT hx).1
  have hTdeg : (↑T : Set (Fin n → ℝ)) ⊆ degreeHeightLE X g H := fun x hx =>
    Work.WilkiesH.degreeHeightLE_mono (Work.WilkiesH.trans_subset X) g H (hT hx)
  obtain ⟨mv, V, d, hmv, hd, hVΩ, hVdim, hVsem, hcover⟩ :=
    hI' D X ν hνn hX hcube hdimν g H T hTX hTdeg
  -- (2) the stratification of each `V i`
  have key : ∀ i : Fin mv, ∃ (mi : ℕ) (W : Fin mi → Set (Fin n → ℝ)),
      mi ≤ MvPolynomial.eval ![(D + d : ℕ), (n + 1 : ℕ)] pm ∧
      (∀ j, W j ∈ S.Ω a₀ (c.eval (D + d)) n) ∧
      (∀ j, DimLE (W j) (μ - 1)) ∧ (∀ j, W j ⊆ X) ∧
      ((X ∩ V i) \ X.alg) ⊆ ⋃ j, W j := by
    intro i
    obtain ⟨mi, W, hmi, hWΩ, hWdim, hWX, hWc⟩ :=
      hstr' ν D d X (V i)
        (Work.WilG5.mem_mono hX (max F a) D (le_max_left F a) (le_refl D))
        (Work.WilG5.mem_mono (hVΩ i) (max F a) d (le_max_right F a) (le_refl d))
        (hVsem i) (hVdim i)
    exact ⟨mi, W, hmi, hWΩ, fun j => Work.WilkiesH.Dim.dimLE_mono (hWdim j) (by omega),
      hWX, hWc⟩
  choose mi W hmi hWΩ hWdim hWX hWc using key
  -- (1)+(2) every point of `T` lands in one of the pieces
  have hcover2 : ∀ x ∈ T, ∃ (i : Fin mv) (j : Fin (mi i)), x ∈ W i j := by
    intro x hx
    have hxX : x ∈ X := hTX hx
    have hxnc : x ∉ X.alg := (hT hx).1.2
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (Finset.mem_coe.mpr hx))
    have hx' : x ∈ (X ∩ V i) \ X.alg := ⟨⟨hxX, hi⟩, hxnc⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hWc i hx')
    exact ⟨i, j, hj⟩
  -- (3) each piece is counted by the induction hypothesis
  have hpiece : ∀ (i : Fin mv) (j : Fin (mi i)),
      ((T.filter (fun x => x ∈ W i j)).card : ℝ) ≤ max 0 (MvPolynomial.eval
        ![((c.eval (D + d) : ℕ) : ℝ), (g : ℝ), Real.log H] fIH) := by
    intro i j
    have h1 : ((T.filter (fun x => x ∈ W i j)).card : ℝ) ≤
        MvPolynomial.eval ![((c.eval (D + d) : ℕ) : ℝ), (g : ℝ), Real.log H] fIH := by
      refine hfIH (c.eval (D + d)) (W i j) (hWΩ i j) (fun x hx => hcube (hWX i j hx))
        (hWdim i j) g H (T.filter (fun x => x ∈ W i j)) ?_
      intro x hx
      rw [Finset.mem_coe, Finset.mem_filter] at hx
      obtain ⟨hxT, hxW⟩ := hx
      refine ⟨⟨hxW, ?_⟩, (hT hxT).2⟩
      intro halg
      exact (hT hxT).1.2 (Work.WilkiesH.alg_mono (hWX i j) halg)
    exact h1.trans (le_max_right 0 _)
  -- (4) the sum over the pieces
  have hsum1 : T.card ≤ ∑ i : Fin mv, ∑ j : Fin (mi i),
      (T.filter (fun x => x ∈ W i j)).card := by
    set U := Finset.univ.biUnion (fun i : Fin mv => Finset.univ.biUnion
      (fun j : Fin (mi i) => T.filter (fun x => x ∈ W i j))) with hU
    have hsub : T ⊆ U := by
      intro x hx
      obtain ⟨i, j, hj⟩ := hcover2 x hx
      rw [hU]
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
        Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hx, hj⟩⟩⟩
    calc T.card ≤ U.card := Finset.card_le_card hsub
      _ ≤ ∑ i : Fin mv, (Finset.univ.biUnion (fun j : Fin (mi i) =>
            T.filter (fun x => x ∈ W i j))).card := by
          rw [hU]; exact Finset.card_biUnion_le
      _ ≤ ∑ i : Fin mv, ∑ j : Fin (mi i),
            (T.filter (fun x => x ∈ W i j)).card :=
          Finset.sum_le_sum (fun i _ => Finset.card_biUnion_le)
  have hsum2 : (∑ i : Fin mv, ∑ j : Fin (mi i),
        (((T.filter (fun x => x ∈ W i j)).card : ℕ) : ℝ)) ≤
      ((∑ i : Fin mv, mi i : ℕ) : ℝ) *
        max 0 (MvPolynomial.eval ![((c.eval (D + d) : ℕ) : ℝ), (g : ℝ), Real.log H] fIH) := by
    set A := max 0 (MvPolynomial.eval
      ![((c.eval (D + d) : ℕ) : ℝ), (g : ℝ), Real.log H] fIH) with hA
    have h2 : (∑ i : Fin mv, ∑ j : Fin (mi i),
          (((T.filter (fun x => x ∈ W i j)).card : ℕ) : ℝ)) ≤
        ∑ i : Fin mv, (mi i : ℝ) * A := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      calc (∑ j : Fin (mi i), (((T.filter (fun x => x ∈ W i j)).card : ℕ) : ℝ))
          ≤ ∑ _j : Fin (mi i), A := Finset.sum_le_sum (fun j _ => hpiece i j)
        _ = (mi i : ℝ) * A := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc (∑ i : Fin mv, ∑ j : Fin (mi i),
            (((T.filter (fun x => x ∈ W i j)).card : ℕ) : ℝ))
        ≤ ∑ i : Fin mv, (mi i : ℝ) * A := h2
      _ = (∑ i : Fin mv, (mi i : ℝ)) * A := by rw [Finset.sum_mul]
      _ = ((∑ i : Fin mv, mi i : ℕ) : ℝ) * A := by rw [Nat.cast_sum]
  have hsigma : ((∑ i : Fin mv, mi i : ℕ) : ℝ) ≤
      (mv : ℝ) * (MvPolynomial.eval ![(D + d : ℕ), (n + 1 : ℕ)] pm : ℕ) := by
    rw [Nat.cast_sum]
    calc (∑ i : Fin mv, (mi i : ℝ))
        ≤ ∑ _i : Fin mv,
            ((MvPolynomial.eval ![(D + d : ℕ), (n + 1 : ℕ)] pm : ℕ) : ℝ) :=
          Finset.sum_le_sum (fun i _ => by exact_mod_cast hmi i)
      _ = (mv : ℝ) * ((MvPolynomial.eval ![(D + d : ℕ), (n + 1 : ℕ)] pm : ℕ) : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hle := hFfin D g H mv d hmv hd
  calc (T.card : ℝ) ≤ ∑ i : Fin mv, ∑ j : Fin (mi i),
        (((T.filter (fun x => x ∈ W i j)).card : ℕ) : ℝ) := by
        exact_mod_cast hsum1
    _ ≤ ((∑ i : Fin mv, mi i : ℕ) : ℝ) * max 0 (MvPolynomial.eval
          ![((c.eval (D + d) : ℕ) : ℝ), (g : ℝ), Real.log H] fIH) := hsum2
    _ ≤ (mv : ℝ) * (MvPolynomial.eval ![(D + d : ℕ), (n + 1 : ℕ)] pm : ℕ) *
          max 0 (MvPolynomial.eval ![((c.eval (D + d) : ℕ) : ℝ), (g : ℝ), Real.log H] fIH) :=
        mul_le_mul_of_nonneg_right hsigma (le_max_left 0 _)
    _ ≤ MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] Ffin := hle

end Work.WilkiesH.Count
