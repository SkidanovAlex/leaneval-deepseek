/-
  WilG4c — `SurrogateSliceFamGraphMem`: the graph of the *fibre* (sliced) surrogate of BNZ §5.4
  is `Ω`-bounded.

  `Work.WilkG4c.surrogateSlice p n f γ M l x` is `(∂_M (slice (f l) x) (γ l x) + 2)/4` where the
  slice `y ↦ f l (x, y)` is `C^{|M|}` at `γ l x`, and the fallback `1/2` elsewhere; here `M` is a
  list of `y`-directions of length `≤ r`.  The proof has three inputs:

  * `Work.WilkG4c.AlDgListSliceMem` (the area's crux): the fibre (`l`-pinned) derivative graph is
    `Ω`-definable with a format uniform in the order and degree `b.eval ![D, |L|]`;
  * `Work.WilkG4c.padFam_famGraph_mem` and `Work.WilkG4c.pinDg_eq_coordPre_AlDgListSlice`: the
    pinned slice graph `pinDg p n f M` of the layout `(l, x, y, s)` is the `AlDgListSlice` of the
    *padded pinned* family `padFam p n f` (cube dimension `n+1`, one ignored coordinate) pulled
    back along `delDummy`, so the crux applies at parameters `(p+1, n)` to the graph of `padFam`,
    whose `Ω`-bound is that of `famGraph f` up to constants;
  * `Work.WilG4c.SurComp.surrogateCompSelf`: the `Ω`-bookkeeping of the two-branch set obtained by
    reading the graph of the surrogate along the curve `γ` (cost `n * Da` in degree, `n * Fa` in
    format, one factor `2` on the degree of the derivative graph).

  The degree of the derivative graph enters the surrogate set with coefficient `2`, hence the
  final polynomial `B` is `2 * b` up to the shift of the first variable by the constant `C'`
  introduced by `padFam_famGraph_mem` (`eval_bind_shiftFst`).

  NOTE on namespaces: this module's path is `Submission.Work.WilG4c.SurrogateSliceFamGraphMem`,
  so the lemma is `Work.WilG4c.SurrogateSliceFamGraphMem`; the area's own definitions (its
  `surrogateSlice`, `AlDgListSlice`, `pinDg`, `padFam`, `delDummy`, …) live in the *different*
  namespace `Work.WilkG4c` and are always written qualified here.
-/
import Mathlib
import Submission.Work.WilG4c.SlicedSurrogateDefs
import Submission.Work.WilG4c.SlicedDerivDefs
import Submission.Work.WilG4c.GraphOfComp
import Submission.Work.WilG4c.AlDgListSliceMem
import Submission.Work.WilG4c.SlicePinnedDefs
import Submission.Work.WilG4c.surrogateCompSelf
import Submission.Work.WilG4c.padFam_famGraph_mem
import Submission.Work.WilG4c.pinDg_eq_coordPre_AlDgListSlice
import Submission.Work.WilG4c.surrogateSliceGraph_eq
import Submission.Work.WilG4c.famGraph_gam_eq_graphOf
import Submission.Work.WilG4a.badLocus_derivZeroSet_uniform

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. Absorbing the shift of the *first* variable of a `ℕ`-polynomial -/

/-- Substituting `X 0 ↦ X 0 + c` turns the evaluation point `![D, r]` into `![D + c, r]`. -/
theorem eval_bind_shiftFst (b : MvPolynomial (Fin 2) ℕ) (c D r : ℕ) :
    MvPolynomial.eval ![D, r]
        (MvPolynomial.bind₁ ![MvPolynomial.X 0 + MvPolynomial.C c, MvPolynomial.X 1] b) =
      MvPolynomial.eval ![D + c, r] b := by
  have h : ∀ i : Fin 2,
      MvPolynomial.eval ![D, r]
        (![MvPolynomial.X 0 + MvPolynomial.C c, MvPolynomial.X 1] i) = ![D + c, r] i := by
    intro i
    fin_cases i <;> simp [MvPolynomial.eval_add]
  rw [Work.WilG4a.eval_bind₁_fin2, funext h]

/-! ## 2. The pinned slice derivative graph is `Ω`-definable -/

/-- Local name for the area's crux — the `Ω`-definability of the fibre (`l`-pinned) derivative
graph `AlDgListSlice` — so that this file's dependency on it is a *single* place.  If the crux is
proved under another name or module instead (the same statement lives in
`Submission/Work/WilG4c/AlDgListSliceMem.lean` — `Work.WilkG4c.AlDgListSliceMem` —, in
`…/AlDgListSlice_mem.lean` and in `…/SliceDerivGraphMem.lean`), only one line has to change. -/
theorem cruxAlDgListSliceMem (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (p n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      Work.WilkG4c.AlDgListSlice p n f L ∈
        S.Ω a (MvPolynomial.eval ![D, L.length] b) (p + (n + 1) + 1) :=
  Work.WilkG4c.AlDgListSliceMem S hcd hder p n F0

/-- **The pinned slice derivative graph.**  For a family `f` whose graph is `Ω`-bounded with
format `F0` and degree `D`, the graph of the `|M|`-th directional derivative of the slice
`y ↦ f l (x, y)` (in the directions `M`) over the locus where that slice is `C^{|M|}` is
`Ω`-bounded with a format `a` independent of `|M| ≤ r` and degree `b.eval ![D, |M|]`.

This is the crux input (`cruxAlDgListSliceMem`) transported from the *padded pinned* family
`padFam p n f` (cube dimension `n + 1`, so that the crux applies at parameters `(p+1, n)`) back
to the layout `(l, x, y, s)`. -/
theorem pinDg_mem (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (p n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (M : List (Fin n)),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      Work.WilkG4c.pinDg p n f M ∈
        S.Ω a (MvPolynomial.eval ![D, M.length] b) (p + (n + 1) + 1) := by
  obtain ⟨C, C', hpad⟩ := Work.WilG4c.padFam_famGraph_mem S p n
  obtain ⟨aa, bb, hcrux⟩ := cruxAlDgListSliceMem S hcd hder (p + 1) n (F0 + C)
  refine ⟨aa + 2 * (((p + 1) + (n + 1) + 1) + (p + (n + 1) + 1)) + 1,
    MvPolynomial.bind₁ ![MvPolynomial.X 0 + MvPolynomial.C C', MvPolynomial.X 1] bb
      + MvPolynomial.C 2, ?_⟩
  intro D f M hf
  -- the padded family's graph, and the crux applied to it
  have hbig := hcrux (D + C') (Work.WilkG4c.padFam p n f) (M.map Fin.castSucc)
    (hpad F0 D f hf)
  -- pull back along `delDummy`
  have hsub := Work.WilG4c.GraphComp.subst_mem S (Work.WilkG4c.delDummy p n) hbig
  have heq : MvPolynomial.eval ![D, M.length]
      (MvPolynomial.bind₁ ![MvPolynomial.X 0 + MvPolynomial.C C', MvPolynomial.X 1] bb
        + MvPolynomial.C 2) =
      MvPolynomial.eval ![D + C', (M.map Fin.castSucc).length] bb + 2 := by
    rw [MvPolynomial.eval_add, MvPolynomial.eval_C, eval_bind_shiftFst, List.length_map]
  rw [Work.WilG4c.pinDg_eq_coordPre_AlDgListSlice, heq]
  exact Work.WilG5.mem_mono hsub _ _ (by omega) le_rfl

/-! ## 3. The main theorem -/

theorem SurrogateSliceFamGraphMem (S : WilkiesDesign.SOMin) (hcd : S.SharpCD)
    (hder : S.SharpDeriv) (p n : ℕ) :
    ∀ F0 : ℕ, ∃ (A : ℕ) (B : MvPolynomial (Fin 2) ℕ) (K : ℕ),
      ∀ (Fa Da D r : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
        (γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)) (M : List (Fin n)),
        WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
        (∀ j : Fin n, WilkiesDesign.CG.famGraph (fun (l : Fin p → ℝ) (x : Fin 1 → ℝ) =>
            γ l (x 0) j) ∈ S.Ω Fa Da (p + 1 + 1)) →
        M.length ≤ r →
        WilkiesDesign.CG.famGraph (fun (l : Fin p → ℝ) (x : Fin 1 → ℝ) =>
            Work.WilkG4c.surrogateSlice p n f γ M l (x 0))
          ∈ S.Ω (A + n * Fa) (MvPolynomial.eval ![D, r] B + n * Da + K) (p + 1 + 1) := by
  intro F0
  -- the derivative graph of the slice, and the composition with the curve
  obtain ⟨a1, b1, hpin⟩ := pinDg_mem S hcd hder p n F0
  obtain ⟨C₁, C₂, hComp⟩ := Work.WilG4c.SurComp.surrogateCompSelf S p n
  refine ⟨a1 + C₁ + 4000, MvPolynomial.C 2 * b1 + MvPolynomial.C (C₂ + 4000),
    C₂ + 4000, ?_⟩
  intro Fa Da D r f γ M hf hγ hlen
  have hpin' := hpin D f M hf
  -- the curve coordinates, as graphs of functions of `Fin (p+1) → ℝ`
  have hγ' : ∀ j : Fin n, graphOf (fun u : Fin (p + 1) → ℝ =>
      γ (fun i : Fin p => u (Fin.castSucc i)) (u (Fin.last p)) j) ∈ S.Ω Fa Da (p + 1 + 1) :=
    fun j => by
      rw [← Work.WilG4c.famGraph_gam_eq_graphOf p n γ j]
      exact hγ j
  -- for `n = 0` the curve hypotheses are vacuous, so the format may drop `Fa`
  have hφF : ∀ j : Fin n, graphOf (fun u : Fin (p + 1) → ℝ =>
      γ (fun i : Fin p => u (Fin.castSucc i)) (u (Fin.last p)) j)
      ∈ S.Ω (if n = 0 then 0 else Fa) Da (p + 1 + 1) := by
    intro j
    by_cases hn : n = 0
    · exact Fin.elim0 (hn ▸ j)
    · simpa [hn] using hγ' j
  have hmem := hComp a1 (if n = 0 then 0 else Fa) (MvPolynomial.eval ![D, M.length] b1) Da
    (Work.WilkG4c.pinDg p n f M)
    (fun (u : Fin (p + 1) → ℝ) (j : Fin n) =>
      γ (fun i : Fin p => u (Fin.castSucc i)) (u (Fin.last p)) j) hpin' hφF
  rw [Work.WilG4c.surrogateSliceGraph_eq p n f γ M]
  refine Work.WilG5.mem_mono hmem _ _ ?_ ?_
  · -- format: `a1 + (if n = 0 then 0 else Fa) + C₁ ≤ (a1 + C₁ + 4000) + n * Fa`
    by_cases hn : n = 0
    · rw [ite_eq_left hn, hn]
      omega
    · rw [ite_eq_right hn]
      have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
      have hFa : Fa ≤ n * Fa := by
        calc Fa = 1 * Fa := (one_mul Fa).symm
          _ ≤ n * Fa := Nat.mul_le_mul_right Fa hn1
      omega
  · -- degree: `2 * eval ![D,|M|] b1 + n * Da + C₂ ≤ eval ![D,r] B + n * Da + (C₂ + 4000)`
    have hD1 : MvPolynomial.eval ![D, M.length] b1 ≤ MvPolynomial.eval ![D, r] b1 :=
      Work.WilG4a.evalFin2_mono b1 hlen
    have hB : MvPolynomial.eval ![D, r]
        (MvPolynomial.C 2 * b1 + MvPolynomial.C (C₂ + 4000))
        = 2 * MvPolynomial.eval ![D, r] b1 + (C₂ + 4000) := by
      rw [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C,
        MvPolynomial.eval_C]
    rw [hB]
    omega

end Work.WilG4c
