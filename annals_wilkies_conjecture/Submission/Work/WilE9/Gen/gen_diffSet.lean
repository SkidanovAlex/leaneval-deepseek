/-
  Work.WilE9.Gen.gen_diffSet

  The derivative graph of a `Gen`-graph is `Gen` (BNZ §3, the differentiability half).

  ## The construction

  Fix `n`, `i : Fin n`, `G ⊆ ℝ^{n+1}` (a `Gen`-set).  The ε-δ definition of "`f` is
  differentiable at `x` in the direction `i` with derivative `d`", where `G` is the graph of
  `f`, is the nested quantifier formula

      ∀ ε > 0, ∃ δ > 0, ∀ h, 0 < |h| → |h| < δ →
        ∀ x', x' = Fin.init v + h·eᵢ → ∀ y₀, Fin.snoc (Fin.init v) y₀ ∈ G →
          ∀ v', Fin.snoc x' v' ∈ G → |vₙ - (v' - y₀)/h| < ε.

  The quantified coordinates are laid out in the order in which the quantifiers are nested,

      (v, ε, δ, h, x', y₀, v') ∈ ℝ^{dd0 n},

  so that eliminating them (innermost first) removes the *last* coordinates of the successive
  ambients `ℝ^{dd0 n} ⊇ ℝ^{dd1 n} ⊇ … ⊇ ℝ^{dd5 n} ⊇ ℝ^{n+1}`.  `∀` is the complement of a
  projection (`Gen.compl`, `Gen.proj`, `Work.WilG0.projLastIter`), `∃` is a projection, and
  each hypothesis is coded as a union with the complement of the corresponding atom.  The two
  atoms mentioning `G` (`Fin.snoc x' v' ∈ G` and `Fin.snoc (Fin.init v) y₀ ∈ G`) are pullbacks
  along coordinate selections (`Work.WilE9.Glue.subst_mem`), which cost `2` in the degree; the
  remaining atoms are semialgebraic (`Work.WilE9.Glue.pos_poly`).  Hence the degree budget is
  `2·D + c` and the format budget is constant in `D`.
-/
import Mathlib
import Submission.Work.WilE9.Defs
import Submission.Work.WilE9.Gen.gen_diff_mem
import Submission.Work.WilE9.Glue.projLastIter_mem

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical Topology
open WilkiesDesign
namespace Work.WilE9.Gen

/-- **The derivative graph of a `Gen`-graph is `Gen`.**  Let `G ⊆ ℝⁿ⁺¹` be a `Gen`-set
(thought of as the graph of a function `f`: a point `Fin.snoc x y ∈ G` means `y = f x`).  Then
the set of pairs `(x, d) ∈ ℝⁿ⁺¹` such that `f` is differentiable at `x` in the coordinate
direction `i` with derivative `d` is again `Gen`, with a *constant* format budget and a
*polynomial* degree budget.  The definition is the difference-quotient one; the last coordinate
of the argument is the derivative candidate `d`, while the value `f x` is read off from `G` as a
separate witness `y₀`.  Neighbourhoods are taken in the sup-metric so that the atoms are
semialgebraic (`|h| < δ`), which is legitimate because the sup-metric balls are a neighbourhood
basis of `ℝⁿ`.

Recipe: lift `G` twice, to the variables `(v,ε,δ,h,x',y₀,v')` (each lift by `Gen.prod_*`, format
only), intersect with the semialgebraic atoms `0 < ε`, `0 < δ`, `0 < |h|`, `|h| < δ`,
`x' j = Fin.init v j + h * (if j = i then 1 else 0)` and `|v (last n) - (v' - y₀)/h| < ε`, then
eliminate the quantifiers by `Gen.compl`/`Gen.proj` (`∀` is complement-of-projection) — each
costs one format and *no* degree — and finally project out `ε`.  Only the two intersections with
(`lifts of`) `G` add degrees, so `b` can be taken linear. -/
theorem gen_diffSet (F n : ℕ) : ∃ (a : ℕ) (b : Polynomial ℕ),
    ∀ (D : ℕ) (G : Set (Fin (n + 1) → ℝ)) (i : Fin n),
      WilkiesDesign.E.Gen F D (n + 1) G → WilkiesDesign.E.Gen a (b.eval D) (n + 1)
        {v : Fin (n + 1) → ℝ |
          ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < |h| → |h| < δ →
            ∀ x' : Fin n → ℝ,
              (∀ j : Fin n, x' j = Fin.init v j + h * (if j = i then 1 else 0)) →
              ∀ y₀ : ℝ, Fin.snoc (Fin.init v) y₀ ∈ G →
              ∀ v' : ℝ, Fin.snoc x' v' ∈ G →
                |v (Fin.last n) - (v' - y₀) / h| < ε} := by
  classical
  refine ⟨8 * F + 40 * n + 400,
    Polynomial.C 2 * Polynomial.X + Polynomial.C (n + 60), ?_⟩
  intro D G i hG
  -- the eight atoms
  have hGB := DiffSet.dGB_gen hG
  have hGA := DiffSet.dGA_gen hG
  have hA7 := DiffSet.dA7_gen n
  have hA5 := DiffSet.dA5_gen n i
  have hA3 := DiffSet.dA3_gen n
  have hA4 := DiffSet.dA4_gen n
  have hA2 := DiffSet.dA2_gen n
  have hA1 := DiffSet.dA1_gen n
  -- the chain
  have hD1 : WilkiesDesign.E.Gen (DiffSet.fD1 F n) ((D + 2) + 15) (DiffSet.dd0 n)
      (DiffSet.dD1 n G) := by
    have h1 : WilkiesDesign.E.Gen (DiffSet.fGB F n + 1) (D + 2) (DiffSet.dd0 n)
        ((DiffSet.dGB n G)ᶜ) := WilkiesDesign.E.Gen.compl hGB
    have h3 := union₂ h1 hA7
    refine monoF ?_ h3
    exact le_trans (DiffSet.max_le_add (DiffSet.fGB F n + 1) (DiffSet.dd0 n + 8))
      (le_of_eq rfl)
  have hE1 : WilkiesDesign.E.Gen (DiffSet.fE1 F n) (DiffSet.gD1 D) (DiffSet.dd1 n)
      (DiffSet.dE1 n G) := by
    have h1 : WilkiesDesign.E.Gen (DiffSet.fD1 F n + 1) (DiffSet.gD1 D) (DiffSet.dd0 n)
        ((DiffSet.dD1 n G)ᶜ) := WilkiesDesign.E.Gen.compl hD1
    have h2 : WilkiesDesign.E.Gen (DiffSet.fD1 F n + 1 + 1) (DiffSet.gD1 D) (DiffSet.dd1 n)
        (projLast ((DiffSet.dD1 n G)ᶜ)) := WilkiesDesign.E.Gen.proj h1
    have h3 : WilkiesDesign.E.Gen (DiffSet.fD1 F n + 1 + 1 + 1) (DiffSet.gD1 D)
        (DiffSet.dd1 n) (DiffSet.dE1 n G) := WilkiesDesign.E.Gen.compl h2
    exact monoF (le_of_eq rfl) h3
  have hD2 : WilkiesDesign.E.Gen (DiffSet.fD2 F n) ((D + 2) + DiffSet.gD1 D) (DiffSet.dd1 n)
      (DiffSet.dD2 n G) := by
    have h1 : WilkiesDesign.E.Gen (DiffSet.fGA F n + 1) (D + 2) (DiffSet.dd1 n)
        ((DiffSet.dGA n G)ᶜ) := WilkiesDesign.E.Gen.compl hGA
    have h3 := union₂ h1 hE1
    refine monoF ?_ h3
    exact le_trans (DiffSet.max_le_add (DiffSet.fGA F n + 1) (DiffSet.fE1 F n))
      (le_of_eq rfl)
  have hE2 : WilkiesDesign.E.Gen (DiffSet.fE2 F n) (DiffSet.gE2 D) (DiffSet.dd2 n)
      (DiffSet.dE2 n G) := by
    have h1 : WilkiesDesign.E.Gen (DiffSet.fD2 F n + 1) (DiffSet.gD2 D) (DiffSet.dd1 n)
        ((DiffSet.dD2 n G)ᶜ) := WilkiesDesign.E.Gen.compl hD2
    have h2 : WilkiesDesign.E.Gen (DiffSet.fD2 F n + 1 + 1) (DiffSet.gD2 D) (DiffSet.dd2 n)
        (projLast ((DiffSet.dD2 n G)ᶜ)) := WilkiesDesign.E.Gen.proj h1
    have h3 : WilkiesDesign.E.Gen (DiffSet.fD2 F n + 1 + 1 + 1) (DiffSet.gD2 D)
        (DiffSet.dd2 n) (DiffSet.dE2 n G) := WilkiesDesign.E.Gen.compl h2
    exact monoF (le_of_eq rfl) h3
  have hD3 : WilkiesDesign.E.Gen (DiffSet.fD3 F n) (n + DiffSet.gE2 D) (DiffSet.dd2 n)
      (DiffSet.dD3 n i G) := by
    have h1 : WilkiesDesign.E.Gen ((DiffSet.dd2 n + 1) + 1) n (DiffSet.dd2 n)
        ((DiffSet.dA5 n i)ᶜ) := WilkiesDesign.E.Gen.compl hA5
    have h3 := union₂ h1 hE2
    refine monoF ?_ h3
    exact le_trans (DiffSet.max_le_add ((DiffSet.dd2 n + 1) + 1) (DiffSet.fE2 F n))
      (le_of_eq rfl)
  have hE3 : WilkiesDesign.E.Gen (DiffSet.fE3 F n) (DiffSet.gD3 n D) (DiffSet.dd3 n)
      (DiffSet.dE3 n i G) := by
    have h1 : WilkiesDesign.E.Gen (DiffSet.fD3 F n + 1) (DiffSet.gD3 n D) (DiffSet.dd2 n)
        ((DiffSet.dD3 n i G)ᶜ) := WilkiesDesign.E.Gen.compl hD3
    have h2 := Glue.projLastIter_mem (n := DiffSet.dd3 n) (m := n)
      (X := (DiffSet.dD3 n i G)ᶜ) h1
    have h3 : WilkiesDesign.E.Gen (DiffSet.fD3 F n + 1 + n + 1) (DiffSet.gD3 n D)
        (DiffSet.dd3 n) (DiffSet.dE3 n i G) := WilkiesDesign.E.Gen.compl h2
    exact monoF (le_of_eq rfl) h3
  have hD4 : WilkiesDesign.E.Gen (DiffSet.fD4 F n) (1 + (6 + DiffSet.gE3 n D)) (DiffSet.dd3 n)
      (DiffSet.dD4 n i G) := by
    have h1 : WilkiesDesign.E.Gen ((DiffSet.dd3 n + 1) + 1) 1 (DiffSet.dd3 n)
        ((DiffSet.dA3 n)ᶜ) := WilkiesDesign.E.Gen.compl hA3
    have h2 : WilkiesDesign.E.Gen ((DiffSet.dd3 n + 4) + 1) 6 (DiffSet.dd3 n)
        ((DiffSet.dA4 n)ᶜ) := WilkiesDesign.E.Gen.compl hA4
    have h3 : WilkiesDesign.E.Gen (((DiffSet.dd3 n + 4) + 1) + DiffSet.fE3 F n)
        (6 + DiffSet.gE3 n D) (DiffSet.dd3 n)
        ((DiffSet.dA4 n)ᶜ ∪ (DiffSet.dE3 n i G)) := by
      have h := union₂ h2 hE3
      exact monoF
        (le_trans (DiffSet.max_le_add ((DiffSet.dd3 n + 4) + 1) (DiffSet.fE3 F n))
          (le_of_eq rfl)) h
    have h4 : WilkiesDesign.E.Gen (((DiffSet.dd3 n + 1) + 1) +
        (((DiffSet.dd3 n + 4) + 1) + DiffSet.fE3 F n)) (1 + (6 + DiffSet.gE3 n D))
        (DiffSet.dd3 n) (DiffSet.dD4 n i G) := by
      have h := union₂ h1 h3
      exact monoF
        (le_trans (DiffSet.max_le_add ((DiffSet.dd3 n + 1) + 1)
          (((DiffSet.dd3 n + 4) + 1) + DiffSet.fE3 F n)) (le_of_eq rfl)) h
    exact monoF (le_of_eq rfl) h4
  have hE4 : WilkiesDesign.E.Gen (DiffSet.fE4 F n) (DiffSet.gE4 n D) (DiffSet.dd4 n)
      (DiffSet.dE4 n i G) := by
    have h1 : WilkiesDesign.E.Gen (DiffSet.fD4 F n + 1) (DiffSet.gD4 n D) (DiffSet.dd3 n)
        ((DiffSet.dD4 n i G)ᶜ) := WilkiesDesign.E.Gen.compl hD4
    have h2 : WilkiesDesign.E.Gen (DiffSet.fD4 F n + 1 + 1) (DiffSet.gD4 n D) (DiffSet.dd4 n)
        (projLast ((DiffSet.dD4 n i G)ᶜ)) := WilkiesDesign.E.Gen.proj h1
    have h3 : WilkiesDesign.E.Gen (DiffSet.fD4 F n + 1 + 1 + 1) (DiffSet.gD4 n D)
        (DiffSet.dd4 n) (DiffSet.dE4 n i G) := WilkiesDesign.E.Gen.compl h2
    exact monoF (le_of_eq rfl) h3
  have hE5 : WilkiesDesign.E.Gen (DiffSet.fE5 F n) (3 + DiffSet.gE4 n D) (DiffSet.dd5 n)
      (DiffSet.dE5 n i G) := by
    have h3 : WilkiesDesign.E.Gen (((DiffSet.dd4 n + 2) + DiffSet.fE4 F n) + 1)
        (3 + DiffSet.gE4 n D) (DiffSet.dd4 n)
        ((DiffSet.dA2 n) ∩ (DiffSet.dE4 n i G)) := by
      have h := inter₂ hA2 hE4
      refine monoF ?_ h
      exact le_trans (Nat.add_le_add_right (DiffSet.max_le_add (DiffSet.dd4 n + 2)
        (DiffSet.fE4 F n)) 1) (le_of_eq rfl)
    exact monoF (le_of_eq rfl) (WilkiesDesign.E.Gen.proj h3)
  have hE6 : WilkiesDesign.E.Gen (DiffSet.fE6 F n) (DiffSet.gD6 n D) (n + 1)
      (DiffSet.dE6 n i G) := by
    have h1 : WilkiesDesign.E.Gen ((DiffSet.dd5 n + 2) + 1) 3 (DiffSet.dd5 n)
        ((DiffSet.dA1 n)ᶜ) := WilkiesDesign.E.Gen.compl hA1
    have h3 : WilkiesDesign.E.Gen (DiffSet.fD6 F n) (3 + DiffSet.gE5 n D) (DiffSet.dd5 n)
        ((DiffSet.dA1 n)ᶜ ∪ (DiffSet.dE5 n i G)) := by
      have h := union₂ h1 hE5
      refine monoF ?_ h
      exact le_trans (DiffSet.max_le_add ((DiffSet.dd5 n + 2) + 1) (DiffSet.fE5 F n))
        (le_of_eq rfl)
    have h5 : WilkiesDesign.E.Gen (DiffSet.fD6 F n + 1) (3 + DiffSet.gE5 n D) (DiffSet.dd5 n)
        (((DiffSet.dA1 n)ᶜ ∪ (DiffSet.dE5 n i G))ᶜ) :=
      WilkiesDesign.E.Gen.compl h3
    have h6 : WilkiesDesign.E.Gen (DiffSet.fD6 F n + 1 + 1) (3 + DiffSet.gE5 n D) (n + 1)
        (projLast (((DiffSet.dA1 n)ᶜ ∪ (DiffSet.dE5 n i G))ᶜ)) :=
      WilkiesDesign.E.Gen.proj h5
    have h7 : WilkiesDesign.E.Gen (DiffSet.fD6 F n + 1 + 1 + 1) (3 + DiffSet.gE5 n D)
        (n + 1) (DiffSet.dE6 n i G) := WilkiesDesign.E.Gen.compl h6
    exact monoD (le_of_eq rfl) h7
  -- the target set
  have hset : DiffSet.dE6 n i G = {v : Fin (n + 1) → ℝ |
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < |h| → |h| < δ →
        ∀ x' : Fin n → ℝ,
          (∀ j : Fin n, x' j = Fin.init v j + h * (if j = i then 1 else 0)) →
          ∀ y₀ : ℝ, Fin.snoc (Fin.init v) y₀ ∈ G →
          ∀ v' : ℝ, Fin.snoc x' v' ∈ G →
            |v (Fin.last n) - (v' - y₀) / h| < ε} := by
    ext w
    rw [DiffSet.mem_E6_iff]
    constructor
    · intro H ε hε
      have H1 : Fin.snoc w ε ∈ DiffSet.dE5 n i G := H ε hε
      obtain ⟨δ, hδ, H2⟩ := (DiffSet.mem_E5_iff n i G).mp H1
      refine ⟨δ, hδ, fun h hpos hlt => ?_⟩
      have hlt' : |h| < (Fin.snoc (Fin.snoc w ε) δ : Fin (DiffSet.dd4 n) → ℝ)
          (DiffSet.ddI4 n) := by
        rw [DiffSet.acc4_ddI4]; exact hlt
      have H3 : Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h ∈ DiffSet.dE3 n i G :=
        (DiffSet.mem_E4_iff n i G).mp H2 h hpos hlt'
      intro u hu
      have H4 : Work.WilG0.snocIt (DiffSet.dd3 n) n
          (Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h) u ∈ DiffSet.dE2 n G := by
        refine (DiffSet.mem_E3_iff n i G).mp H3 u ?_
        intro j
        rw [hu j, DiffSet.acc3_vI3 n w ε δ h j, DiffSet.acc3_hI3 n w ε δ h]
      intro y hy
      have H5 : Fin.snoc (Work.WilG0.snocIt (DiffSet.dd3 n) n
          (Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h) u) y ∈ DiffSet.dE1 n G := by
        refine (DiffSet.mem_E2_iff n i G).mp H4 y ?_
        have hfun : (fun j : Fin n => (Work.WilG0.snocIt (DiffSet.dd3 n) n
            (Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h) u) (DiffSet.dvI2 n (Fin.castSucc j)))
            = Fin.init w := by
          funext j
          exact DiffSet.acc2_vI2 n w ε δ h u j
        rw [hfun]
        exact hy
      intro v' hv
      have hfun : (fun j : Fin n => (Fin.snoc (Work.WilG0.snocIt (DiffSet.dd3 n) n
          (Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h) u) y : Fin (DiffSet.dd1 n) → ℝ)
            (DiffSet.dxI1 n j)) = u := by
        funext j
        exact DiffSet.acc1_xI1 n w ε δ h u y j
      have hgoal := (DiffSet.mem_E1_iff n i G).mp H5 v' (by rw [hfun]; exact hv)
      rw [DiffSet.acc1_vI1 n w ε δ h u y (Fin.last n), DiffSet.acc1_yI1 n w ε δ h u y,
        DiffSet.acc1_hI1 n w ε δ h u y, DiffSet.acc1_eI1 n w ε δ h u y] at hgoal
      exact hgoal
    · intro H ε hε
      obtain ⟨δ, hδ, H'⟩ := H ε hε
      refine (DiffSet.mem_E5_iff n i G).mpr ⟨δ, hδ, ?_⟩
      refine (DiffSet.mem_E4_iff n i G).mpr ?_
      intro h hpos hlt
      have hlt' : |h| < δ := by
        rw [DiffSet.acc4_ddI4] at hlt; exact hlt
      refine (DiffSet.mem_E3_iff n i G).mpr ?_
      intro u hu
      have hu' : ∀ j : Fin n, u j = Fin.init w j + h * (if j = i then 1 else 0) := by
        intro j
        have hj := hu j
        rwa [DiffSet.acc3_vI3 n w ε δ h j, DiffSet.acc3_hI3 n w ε δ h] at hj
      refine (DiffSet.mem_E2_iff n i G).mpr ?_
      intro y hy
      have hy' : Fin.snoc (Fin.init w) y ∈ G := by
        have hfun : (fun j : Fin n => (Work.WilG0.snocIt (DiffSet.dd3 n) n
            (Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h) u) (DiffSet.dvI2 n (Fin.castSucc j)))
            = Fin.init w := by
          funext j
          exact DiffSet.acc2_vI2 n w ε δ h u j
        rwa [hfun] at hy
      refine (DiffSet.mem_E1_iff n i G).mpr ?_
      intro v' hv
      have hfun : (fun j : Fin n => (Fin.snoc (Work.WilG0.snocIt (DiffSet.dd3 n) n
          (Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h) u) y : Fin (DiffSet.dd1 n) → ℝ)
            (DiffSet.dxI1 n j)) = u := by
        funext j
        exact DiffSet.acc1_xI1 n w ε δ h u y j
      have hv' : Fin.snoc u v' ∈ G := by rwa [hfun] at hv
      have hgoal := H' h hpos hlt' u hu' y hy' v' hv'
      rwa [DiffSet.acc1_vI1 n w ε δ h u y (Fin.last n), DiffSet.acc1_yI1 n w ε δ h u y,
        DiffSet.acc1_hI1 n w ε δ h u y, DiffSet.acc1_eI1 n w ε δ h u y]
  rw [← hset]
  refine mono ?_ ?_ hE6
  · -- the format budget
    simp only [DiffSet.fE6, DiffSet.fD6, DiffSet.fE5, DiffSet.fE4, DiffSet.fD4,
      DiffSet.fE3, DiffSet.fD3, DiffSet.fE2, DiffSet.fD2, DiffSet.fE1, DiffSet.fD1,
      DiffSet.fGB, DiffSet.fGA, DiffSet.dd0, DiffSet.dd1, DiffSet.dd2, DiffSet.dd3,
      DiffSet.dd4, DiffSet.dd5]
    omega
  · -- the degree budget
    simp only [DiffSet.gE6, DiffSet.gD6, DiffSet.gE5, DiffSet.gE4, DiffSet.gD4,
      DiffSet.gE3, DiffSet.gD3, DiffSet.gE2, DiffSet.gD2, DiffSet.gE1, DiffSet.gD1,
      DiffSet.gGB, DiffSet.gGA, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C]
    omega

end Work.WilE9.Gen