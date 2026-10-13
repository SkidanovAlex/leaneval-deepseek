/-
  WilG4c — bookkeeping API for the frozen `FLem` / `FLemP` conclusion.

  `FLemP S p n P` concludes, for each family, the existence of a `Finset` `Φ` of chart tuples
  together with (i) a cardinality bound, (ii) the *per-chart* conditions (graphs in `Ω`,
  charts mapping the cube into itself, unit `C^r` norms of the composites) and (iii) the
  `ε`-cover of the image.  This file names the two inner predicates `ChartsOK` and `Covers`
  (definitionally equal to the corresponding sub-formulas of `FLemP`) and records the
  elementary closure properties the reductions of BNZ §§5.2–5.5 use:

  * `ChartsOK` and `Covers` are closed under `Finset` unions (the number of charts grows, the
    format/degree `a`,`Dg` and the parameter set `Λ` do not change),
  * `Covers` is monotone in `ε` and transfers from an `ε`-cover of the *domain* whenever the
    family is Lipschitz (BNZ's remark after Lemma 5.1).
-/
import Submission.Work.WilG4c.Defs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- The per-chart conditions in the conclusion of `FLemP`: each chart tuple has `Ω`-bounded
coordinate graphs, maps the open cube into itself for every parameter in `Λ`, and the
composite of every family member with (the point map of) the chart has unit `C^r`-norm. -/
def ChartsOK (S : SOMin) {p n k : ℕ} (a Dg r : ℕ) (Λ : Set (Fin p → ℝ))
    (F : Family k p n) (Φ : Finset (ChartTuple p n)) : Prop :=
  ∀ φ ∈ Φ, (∀ j, famGraph (φ j) ∈ S.Ω a Dg (p + n + 1)) ∧
    ∀ l ∈ Λ, (∀ t ∈ openCube n, (fun j => φ j l t) ∈ openCube n) ∧
      ∀ i, ContDiffOn ℝ r (fun t => F i l (fun j => φ j l t)) (openCube n) ∧
        ∀ m ≤ r, ∀ t ∈ openCube n,
          ‖iteratedFDeriv ℝ m (fun t => F i l (fun j => φ j l t)) t‖ ≤ 1

/-- The `ε`-cover condition in the conclusion of `FLemP`. -/
def Covers {p n k : ℕ} (Λ : Set (Fin p → ℝ)) (F : Family k p n)
    (Φ : Finset (ChartTuple p n)) (ε : ℝ) : Prop :=
  ∀ l ∈ Λ, ∀ x ∈ openCube n, ∃ φ ∈ Φ, ∃ t ∈ openCube n,
    ∀ i, |F i l (fun j => φ j l t) - F i l x| < ε

/-- `FLemP` restated through `ChartsOK` and `Covers`; the two are definitionally the inner
conjuncts of the conclusion, so this is just a change of spelling. -/
theorem FLemP_iff (S : SOMin) (p n : ℕ) (P : ℕ → ∀ k, Family k p n → Prop) :
    FLemP S p n P ↔
      ∀ F0 : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
        ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∀ (Λ : Set (Fin p → ℝ)) (F : Family k p n),
          P r k F → (∀ i, famGraph (F i) ∈ S.Ω F0 D (p + n + 1)) → ValuesIn01 Λ F →
          ∃ Φ : Finset (ChartTuple p n),
            (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
            ChartsOK S a (MvPolynomial.eval ![D, r] b) r Λ F Φ ∧ Covers Λ F Φ ε :=
  Iff.rfl

theorem ChartsOK.subset {S : SOMin} {p n k a Dg r : ℕ} {Λ : Set (Fin p → ℝ)}
    {F : Family k p n} {Φ Ψ : Finset (ChartTuple p n)} (h : ChartsOK S a Dg r Λ F Φ)
    (hΨ : Ψ ⊆ Φ) : ChartsOK S a Dg r Λ F Ψ :=
  fun φ hφ => h φ (hΨ hφ)

theorem ChartsOK.union {S : SOMin} {p n k a Dg r : ℕ} {Λ : Set (Fin p → ℝ)}
    {F : Family k p n} {Φ Ψ : Finset (ChartTuple p n)} (hΦ : ChartsOK S a Dg r Λ F Φ)
    (hΨ : ChartsOK S a Dg r Λ F Ψ) : ChartsOK S a Dg r Λ F (Φ ∪ Ψ) := by
  intro φ hφ
  rcases Finset.mem_union.mp hφ with h | h
  · exact hΦ φ h
  · exact hΨ φ h

theorem Covers.union {p n k : ℕ} {Λ : Set (Fin p → ℝ)} {F : Family k p n}
    {Φ Ψ : Finset (ChartTuple p n)} {ε : ℝ} (hΦ : Covers Λ F Φ ε) (hΨ : Covers Λ F Ψ ε) :
    Covers Λ F (Φ ∪ Ψ) ε := by
  intro l hl x hx
  obtain ⟨φ, hφ, t, ht, h⟩ := hΦ l hl x hx
  exact ⟨φ, Finset.mem_union_left _ hφ, t, ht, h⟩

theorem Covers.mono_eps {p n k : ℕ} {Λ : Set (Fin p → ℝ)} {F : Family k p n}
    {Φ : Finset (ChartTuple p n)} {ε ε' : ℝ} (h : Covers Λ F Φ ε) (hε : ε ≤ ε') :
    Covers Λ F Φ ε' := by
  intro l hl x hx
  obtain ⟨φ, hφ, t, ht, hlt⟩ := h l hl x hx
  exact ⟨φ, hφ, t, ht, fun i => lt_of_lt_of_le (hlt i) hε⟩

/-- **BNZ's remark after Lemma 5.1.**  If every member of the family is `C`-Lipschitz on the
cube (`0 < C`), then an `ε`-cover of the *domain* cube by charts whose images lie in the cube
gives a `C·ε`-cover of the *image* of the family.  This is what lets one replace the covering
condition in `FLem` by a covering condition on `I^n` after a Lipschitz preparation step. -/
theorem Covers.of_domain_cover {p n k : ℕ} {Λ : Set (Fin p → ℝ)} {F : Family k p n}
    {Φ : Finset (ChartTuple p n)} {ε C : ℝ} (hC : 0 < C) (hlip : LipOnCube F C)
    (hcube : ∀ φ ∈ Φ, ∀ l ∈ Λ, ∀ t ∈ openCube n, (fun j => φ j l t) ∈ openCube n)
    (hdom : ∀ l ∈ Λ, ∀ z ∈ openCube n, ∃ φ ∈ Φ, ∃ t ∈ openCube n,
      dist (fun j => φ j l t) z < ε) :
    Covers Λ F Φ (C * ε) := by
  intro l hl x hx
  obtain ⟨φ, hφ, t, ht, hdist⟩ := hdom l hl x hx
  refine ⟨φ, hφ, t, ht, fun i => ?_⟩
  have h1 : (fun j => φ j l t) ∈ openCube n := hcube φ hφ l hl t ht
  calc |F i l (fun j => φ j l t) - F i l x| ≤ C * dist (fun j => φ j l t) x := hlip i l _ x h1 hx
    _ < C * ε := mul_lt_mul_of_pos_left hdist hC

end Work.WilkG4c
