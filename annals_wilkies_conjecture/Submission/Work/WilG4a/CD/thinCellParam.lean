import Mathlib
import Submission.Work.WilG4a.CD.fibDerivDefs
import Submission.Work.WilkiesH.Strat.cellData
import Submission.Work.WilG1.Main
import Submission.Work.WilG4a.subst_mem

set_option maxHeartbeats 4000000

noncomputable section
open Classical

namespace Work.WilG4a.CD

open WilkiesDesign

/-! ## Auxiliary diagonal sets

A cell `C` with empty interior is a graph over `k < p` of its coordinates `e : Fin k ↪ Fin p`.
To run effective choice over the set of pairs `(u, v)` with `v ∈ C` and `v ∘ e = u` we need
the "diagonal" condition `v ∘ e = u` to be `Ω`-definable; it is the zero set of the sum of
squares `∑_i (x_{e i} - x_{p + i})²`, of total degree `≤ 2`. -/

/-- `Σ_i (X_{σ i} - X_{k+i})²` in `ℝ^{k+p}`: the polynomial whose zero set says that the
`e`-coordinates of the last `p` coordinates equal the first `k` coordinates. -/
private def diagPoly2 (k p : ℕ) (e : Fin k → Fin p) : MvPolynomial (Fin (k + p)) ℝ :=
  ∑ i : Fin k, (MvPolynomial.X (Fin.castAdd p i) - MvPolynomial.X (Fin.natAdd k (e i))) *
    (MvPolynomial.X (Fin.castAdd p i) - MvPolynomial.X (Fin.natAdd k (e i)))

/-- The zero set of `diagPoly2` is the coordinate-equality set. -/
private theorem diagSet2_eq (k p : ℕ) (e : Fin k → Fin p) :
    {z : Fin (k + p) → ℝ | ∀ i : Fin k, z (Fin.castAdd p i) = z (Fin.natAdd k (e i))} =
      {z : Fin (k + p) → ℝ | MvPolynomial.eval z (diagPoly2 k p e) = 0} := by
  ext z
  simp only [diagPoly2, map_sum, MvPolynomial.eval_sub, MvPolynomial.eval_X,
    MvPolynomial.eval_mul]
  constructor
  · intro h
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [h i, sub_self, mul_zero]
  · intro h i
    have hnn : ∀ j ∈ (Finset.univ : Finset (Fin k)),
        0 ≤ (z (Fin.castAdd p j) - z (Fin.natAdd k (e j))) *
          (z (Fin.castAdd p j) - z (Fin.natAdd k (e j))) := fun j _ => mul_self_nonneg _
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h i (Finset.mem_univ i)
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h0)

/-- `diagPoly2` has total degree at most `2`, so the diagonal set has degree `2`. -/
private theorem diagPoly2_deg_le_two (k p : ℕ) (e : Fin k → Fin p) :
    (diagPoly2 k p e).totalDegree ≤ 2 := by
  rw [diagPoly2]
  refine le_trans (MvPolynomial.totalDegree_finsetSum Finset.univ
    (fun i : Fin k => (MvPolynomial.X (Fin.castAdd p i) - MvPolynomial.X (Fin.natAdd k (e i))) *
      (MvPolynomial.X (Fin.castAdd p i) - MvPolynomial.X (Fin.natAdd k (e i))))) ?_
  rw [Finset.sup_le_iff]
  intro i _
  have h1 : MvPolynomial.totalDegree
      ((MvPolynomial.X (Fin.castAdd p i) - MvPolynomial.X (Fin.natAdd k (e i)) :
        MvPolynomial (Fin (k + p)) ℝ)) ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
    omega
  have h2 := MvPolynomial.totalDegree_mul
    ((MvPolynomial.X (Fin.castAdd p i) - MvPolynomial.X (Fin.natAdd k (e i)) :
      MvPolynomial (Fin (k + p)) ℝ))
    ((MvPolynomial.X (Fin.castAdd p i) - MvPolynomial.X (Fin.natAdd k (e i)) :
      MvPolynomial (Fin (k + p)) ℝ))
  linarith

/-- Binary intersections in the `Ω`-calculus: the format is the maximum plus one step for the
intersection axiom, the degree is the sum. -/
private theorem inter_mem_two {S : WilkiesDesign.SOMin} {n F F' D D' : ℕ}
    {X Y : Set (Fin n → ℝ)} (hX : X ∈ S.Ω F D n) (hY : Y ∈ S.Ω F' D' n) :
    X ∩ Y ∈ S.Ω (max F F' + 1) (D + D') n := by
  have hX' : X ∈ S.Ω (max F F') D n := Work.WilG4a.mem_mono hX (le_max_left _ _) le_rfl
  have hY' : Y ∈ S.Ω (max F F') D' n := Work.WilG4a.mem_mono hY (le_max_right _ _) le_rfl
  have hmain := S.inter (fun i : Fin 2 => if i = 0 then D else D')
    (fun i : Fin 2 => if i = 0 then X else Y)
    (by
      intro i
      fin_cases i
      · simpa using hX'
      · simpa using hY')
  have hsum : (∑ i : Fin 2, (if i = 0 then D else D')) = D + D' := by
    rw [Fin.sum_univ_two]
    norm_num
  rw [hsum] at hmain
  rwa [Work.WilG4a.iInter_fin_two] at hmain

/-- Every `Ω`-definable cell `C ⊆ ℝ^p` with empty interior is the graph of an `Ω`-definable parametrisation `Ψ : ℝ^k → ℝ^p` over its projection to `k < p` coordinates: with `e : Fin k ↪ Fin p`, every `l ∈ C` satisfies `Ψ (l ∘ e) = l`. The construction is `Work.WilkiesH.Strat.cellData_of_isCell` (which provides the section `Φ` and `k ≤ p`, and `k = p → (interior C).Nonempty`) combined with `WilkiesDesign.CG.G1_choice_proved` applied to the `Ω`-set `{(u,v) ∈ ℝ^{k+p} : v ∈ C ∧ v ∘ e = u}`. Because the `Ω`-bounds from `G1_choice_proved` depend on `k`, the format is the maximum and the degree polynomial the sum over the finitely many `k < p`. -/
theorem thinCellParam (S : WilkiesDesign.SOMin) (hcd : WilkiesDesign.SOMin.SharpCD S) (p F0 : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ),
      ∀ (D : ℕ) (C : Set (Fin p → ℝ)), C ∈ S.Ω F0 D p → WilkiesDesign.IsCell p C →
        interior C = ∅ →
        ∃ (k : ℕ) (hk : k < p) (e : Fin k ↪ Fin p) (Ψ : (Fin k → ℝ) → (Fin p → ℝ)),
          (∀ l ∈ C, Ψ (l ∘ e) = l) ∧
          Work.WilG4a.CD.paramGraph Ψ ∈ S.Ω A (B.eval D) (k + p) := by
  -- The uniform format fed to effective choice: large enough for every `k < p`.
  set F' : ℕ := max (F0 + 6 * p) (2 * p) + 1 with hF'def
  have hG1 : ∀ k : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) (X : Set (Fin (k + p) → ℝ)), X ∈ S.Ω F' D (k + p) →
        ∃ f : (Fin k → ℝ) → (Fin p → ℝ),
          (∀ l : Fin k → ℝ, (∃ y, Fin.append l y ∈ X) → Fin.append l (f l) ∈ X) ∧
          paramGraph f ∈ S.Ω a (b.eval D) (k + p) := by
    intro k
    obtain ⟨a, b, hab⟩ := WilkiesDesign.CG.G1_choice_proved S hcd F' k p
    exact ⟨a, b, fun D X hX => hab D X hX⟩
  choose a b hab using hG1
  refine ⟨Finset.sup (Finset.range p) a,
    ∑ k ∈ Finset.range p, (b k).comp (Polynomial.X + Polynomial.C 4), ?_⟩
  intro D C hCΩ hCell hInt
  -- The cell dimension datum: `k ≤ p`, a section `Φ` of `x ↦ x ∘ e`, and `k = p` forcing
  -- nonempty interior.
  obtain ⟨k, e, Φ, hcdim, hsec, hle, hint⟩ := Work.WilkiesH.Strat.cellData_of_isCell hCell
  have hkp : k < p := by
    have hne : k ≠ p := fun h => by
      obtain ⟨x, hx⟩ := hint h
      rw [hInt] at hx
      exact hx
    exact lt_of_le_of_ne hle hne
  -- The diagonal condition `v ∘ e = u` is `Ω`-definable with degree `2`.
  have hD0mem : {z : Fin (k + p) → ℝ | ∀ i : Fin k,
      z (Fin.castAdd p i) = z (Fin.natAdd k (e i))} ∈ S.Ω (k + p) 2 (k + p) := by
    have h := S.hyp (k + p) (diagPoly2 k p e)
    rw [← diagSet2_eq k p e] at h
    exact Work.WilG4a.mem_mono h le_rfl (diagPoly2_deg_le_two k p e)
  -- The pullback of `C` along `z ↦ z ∘ Fin.natAdd k` (the substitution atom).
  have hX1 : {z : Fin (k + p) → ℝ | z ∘ Fin.natAdd k ∈ C} ∈
      S.Ω (F0 + 2 * ((k + p) + p) + 1) (D + 2) (k + p) :=
    Work.WilG4a.subst_mem S (Fin.natAdd k) hCΩ
  set F1 : ℕ := max (F0 + 2 * ((k + p) + p) + 1) (k + p) with hF1def
  have hX1' : {z : Fin (k + p) → ℝ | z ∘ Fin.natAdd k ∈ C} ∈ S.Ω F1 (D + 2) (k + p) :=
    Work.WilG4a.mem_mono hX1 (le_max_left _ _) le_rfl
  have hD0' : {z : Fin (k + p) → ℝ | ∀ i : Fin k,
      z (Fin.castAdd p i) = z (Fin.natAdd k (e i))} ∈ S.Ω F1 2 (k + p) :=
    Work.WilG4a.mem_mono hD0mem (le_max_right _ _) le_rfl
  have hinter := inter_mem_two hX1' hD0'
  -- The `Ω`-set of pairs `(u,v)` with `v ∈ C` and `v ∘ e = u`.
  set X : Set (Fin (k + p) → ℝ) :=
    {z | (fun j : Fin p => z (Fin.natAdd k j)) ∈ C ∧
      ∀ i : Fin k, z (Fin.castAdd p i) = z (Fin.natAdd k (e i))} with hXdef
  have hXeq : ({z : Fin (k + p) → ℝ | z ∘ Fin.natAdd k ∈ C} ∩
      {z : Fin (k + p) → ℝ | ∀ i : Fin k,
        z (Fin.castAdd p i) = z (Fin.natAdd k (e i))}) = X := by
    rw [hXdef]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.comp_def]
  have hXmem : X ∈ S.Ω F' (D + 4) (k + p) := by
    rw [← hXeq]
    refine Work.WilG4a.mem_mono hinter ?_ ?_
    · rw [hF'def, max_self]
      have hF1le : F1 ≤ max (F0 + 6 * p) (2 * p) := by
        rw [hF1def]
        exact max_le (by omega) (by omega)
      omega
    · omega
  -- Effective choice on `X`: the choosing function is the parametrisation.
  obtain ⟨f, hsel, hfmem⟩ := hab k (D + 4) X hXmem
  have hsecf : ∀ l ∈ C, f (l ∘ e) = l := by
    intro l hl
    have hmemX : Fin.append (l ∘ e) l ∈ X := by
      rw [hXdef]
      refine ⟨?_, ?_⟩
      · have heq : (fun j : Fin p => Fin.append (l ∘ e) l (Fin.natAdd k j)) = l := by
          funext j
          rw [Fin.append_right]
        rw [heq]
        exact hl
      · intro i
        rw [Fin.append_left, Fin.append_right]
        rfl
    have hsel2 := hsel (l ∘ e) ⟨l, hmemX⟩
    rw [hXdef] at hsel2
    obtain ⟨hfC, hfd⟩ := hsel2
    -- The chosen point again lies in `C`, with the same `e`-coordinates as `l`.
    have hfC' : f (l ∘ e) ∈ C := by
      have heq : (fun j : Fin p => Fin.append (l ∘ e) (f (l ∘ e)) (Fin.natAdd k j)) =
          f (l ∘ e) := by
        funext j
        rw [Fin.append_right]
      exact heq ▸ hfC
    have hfe : (f (l ∘ e)) ∘ e = l ∘ e := by
      funext i
      have hi := hfd i
      rw [Fin.append_left, Fin.append_right] at hi
      exact hi.symm
    -- The section `Φ` of `x ↦ x ∘ e` is injective on `C`.
    rw [← hsec (f (l ∘ e)) hfC', hfe, hsec l hl]
  refine ⟨k, hkp, e, f, hsecf, ?_⟩
  -- The degree polynomial: the sum over `k < p` of the shifted bounds `b k`, so that the
  -- uniform degree offset `+4` is absorbed.
  have hBeval : (∑ i ∈ Finset.range p,
      (b i).comp (Polynomial.X + Polynomial.C 4)).eval D =
      ∑ i ∈ Finset.range p, (b i).eval (D + 4) := by
    rw [Polynomial.eval_finsetSum]
    simp [Polynomial.eval_comp]
  have hle : (b k).eval (D + 4) ≤
      (∑ i ∈ Finset.range p, (b i).comp (Polynomial.X + Polynomial.C 4)).eval D := by
    rw [hBeval]
    rw [← Finset.sum_erase_add (Finset.range p) (fun i => (b i).eval (D + 4))
      (Finset.mem_range.mpr hkp)]
    omega
  exact Work.WilG4a.mem_mono hfmem
    (Finset.le_sup (f := a) (Finset.mem_range.mpr hkp)) hle

end Work.WilG4a.CD
