/-
  WilG4cR / `AlDgListSliceMem` — a **clean** copy of `Work.WilkG4c.AlDgListSlice_mem`
  (`Submission/Work/WilG4c/AlDgListSlice_mem.lean`), i.e. the `Ω`-definability of the *slice*
  (fibre) derivative graph with a format that is uniform in the order `|L|` and a degree that is
  a polynomial in `(D, |L|)`.

  The original assembly uses the `sorry`-tainted `Work.WilkG4c.CritFixMem` (whose chain runs
  through `CritAux.hypoRaw_mem` and `CritFixAux.finset_inter_mem`) and the non-building
  `Work.WilkG4c.CritFixGoodMem`.  The copy below uses the clean `Work.WilG4cR.CritFixMem` and
  `Work.WilG4cR.CritFixGoodMemR2`, and the `sorry`-free recursion half
  `Work.WilG4c.AlDgListSliceBadMem` (with `Work.WilG4c.AlBadMemFix` for the thin parameter
  projections), the degenerate cases `Work.WilkG4c.AlDgListSliceNil` (`L = []`) and
  `Work.WilkG4c.AlDgListSliceZero` (`p = 0`), and a strong induction on the number of parameters
  `p`.

  This is the ingredient that `Submission/Work/WilG4c/FibreBadCoresR.lean` consumes: the fibre
  `C^r`-locus `SliceLocus p n f r` is the projection of the slice derivative graph, hence — its
  complement — is `Ω`-definable with an `r`-independent format and a degree polynomial in
  `(D, r)`, and its fibres have empty interior by generic smoothness.
-/
import Mathlib
import Submission.Work.WilG4c.SlicedDerivDefs
import Submission.Work.WilG4c.AlSliceBase
import Submission.Work.WilG4c.AlDgListSliceNil
import Submission.Work.WilG4c.AlDgListSliceZero
import Submission.Work.WilG4c.CritFixDefs
import Submission.Work.WilG4c.AlBadMemFix
import Submission.Work.WilG4c.AlDgListSliceBadMem
import Submission.Work.WilG4cR.CritFixMem
import Submission.Work.WilG4cR.CritFixAuxFill

set_option autoImplicit false
noncomputable section

open Classical

namespace Work.WilG4cR

/-- Polynomial bookkeeping for the degenerate length: replacing the second variable of a
two-variable polynomial by `0` rewrites the constant degree `b.eval ![D, 0]` as the value at
`![D, k]` of a polynomial in the two variables `D` and `k`. -/
theorem eval_bind_zero (D k : ℕ) (b : MvPolynomial (Fin 2) ℕ) :
    MvPolynomial.eval ![D, k]
        (MvPolynomial.bind₁ (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0
          else MvPolynomial.C 0) b)
      = MvPolynomial.eval ![D, 0] b := by
  change MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, k]
      (MvPolynomial.bind₁ (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0
        else MvPolynomial.C 0) b) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  have hf : (fun i : Fin 2 => (MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, k])
      (if i = 0 then MvPolynomial.X 0 else MvPolynomial.C 0)) = ![D, 0] := by
    funext i
    fin_cases i <;> simp
  rw [hf]
  rfl

/-- The statement of the target, by strong induction on the number of parameters `p`. -/
theorem AlDgListSlice_mem_aux (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) :
    ∀ (p : ℕ) (n F0 : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))),
        WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
        Work.WilkG4c.AlDgListSlice p n f L ∈
          S.Ω a (MvPolynomial.eval ![D, L.length] b) (p + (n + 1) + 1) := by
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
    intro n F0
    by_cases hp : p = 0
    · -- the zero-parameter case (`L ≠ []` is `AlDgListSliceZero`, `L = []` is `AlDgListSliceNil`)
      subst hp
      obtain ⟨aN, bN, hN⟩ := Work.WilkG4c.AlDgListSliceNil S hcd hder 0 n F0
      obtain ⟨aZ, bZ, hZ⟩ := Work.WilkG4c.AlDgListSliceZero S hcd hder n F0
      refine ⟨max aZ aN, MvPolynomial.bind₁ (fun i : Fin 2 =>
        if i = 0 then MvPolynomial.X 0 else MvPolynomial.C 0) bN + bZ, ?_⟩
      intro D f L hf
      by_cases hL : L = []
      · subst hL
        refine Work.WilG1.Omega.mono (hN D f hf) (le_max_right _ _) ?_
        rw [MvPolynomial.eval_add, eval_bind_zero]
        exact Nat.le_add_right _ _
      · refine Work.WilG1.Omega.mono (hZ D f L hL hf) (le_max_left _ _) ?_
        rw [MvPolynomial.eval_add]
        exact Nat.le_add_left _ _
    · -- the recursion step
      obtain ⟨aN, bN, hN⟩ := Work.WilkG4c.AlDgListSliceNil S hcd hder p n F0
      obtain ⟨aC, bC, hC⟩ := Work.WilG4cR.CritFixMem S hder p n F0
      obtain ⟨aBd, bBd, hBd⟩ := Work.WilG4c.AlBadMemFix S hder p n F0
      obtain ⟨aB, bB, hB⟩ := Work.WilG4c.AlDgListSliceBadMem S hcd hder n p
        (fun F0' => by
          obtain ⟨a0, b0, h0⟩ := Work.WilG4c.AlBadMemFix S hder p n F0'
          exact ⟨a0, b0, fun D f L hf => (h0 D f L hf).2⟩)
        (fun p' hp' F0' => ih p' hp' n F0') F0
      -- the `AlGood` piece: `CritFix ∩ AlGood` is `Ω`-definable
      have hGood : ∀ (D : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
          (L : List (Fin (n + 1))),
          WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
          Work.WilkG4c.CritFix p n f L ∩ Work.WilkG4c.AlGood p n f L ∈
            S.Ω (max aC (aBd + 1) + 1)
              (MvPolynomial.eval ![D, L.length] (bC + bBd)) (p + (n + 1) + 1) := by
        intro D f L hf
        have h1 : Work.WilkG4c.CritFix p n f L ∈
            S.Ω (max aC (aBd + 1)) (MvPolynomial.eval ![D, L.length] bC)
              (p + (n + 1) + 1) :=
          Work.WilG0.Omega_mono_FD (le_max_left _ _) le_rfl (hC D f L hf)
        have h2 : Work.WilkG4c.AlGood p n f L ∈
            S.Ω (max aC (aBd + 1)) (MvPolynomial.eval ![D, L.length] bBd)
              (p + (n + 1) + 1) :=
          Work.WilG0.Omega_mono_FD (le_max_right _ _) le_rfl
            (S.compl (hBd D f L hf).1)
        have hinter := Work.WilG0.Omega_inter2 h1 h2
        refine Work.WilG0.Omega_mono_FD le_rfl ?_ hinter
        rw [MvPolynomial.eval_add]
      refine ⟨max (max (max aC (aBd + 1) + 1) aB) aN,
        MvPolynomial.bind₁ (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0
          else MvPolynomial.C 0) bN + (bC + bBd + bB), ?_⟩
      intro D f L hf
      by_cases hL : L = []
      · subst hL
        refine Work.WilG1.Omega.mono (hN D f hf) (le_max_right _ _) ?_
        rw [MvPolynomial.eval_add, eval_bind_zero]
        exact Nat.le_add_right _ _
      · -- the split `AlDgListSlice = (CritFix ∩ AlGood) ∪ (AlDgListSlice ∩ AlBad)`
        have heq := Work.WilG4cR.CritFixGoodMemR2 S hcd hder p n F0 D f L hf
        have hsplit : Work.WilkG4c.AlDgListSlice p n f L =
            (Work.WilkG4c.CritFix p n f L ∩ Work.WilkG4c.AlGood p n f L) ∪
              (Work.WilkG4c.AlDgListSlice p n f L ∩ Work.WilkG4c.AlBad p n f L) := by
          rw [← heq]
          ext z
          constructor
          · intro hz
            by_cases hb : z ∈ Work.WilkG4c.AlBad p n f L
            · exact Or.inr ⟨hz, hb⟩
            · exact Or.inl ⟨hz, by rw [Work.WilkG4c.mem_AlGood]; exact hb⟩
          · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
        rw [hsplit]
        have h1 : Work.WilkG4c.CritFix p n f L ∩ Work.WilkG4c.AlGood p n f L ∈
            S.Ω (max (max aC (aBd + 1) + 1) aB)
              (MvPolynomial.eval ![D, L.length] (bC + bBd)) (p + (n + 1) + 1) :=
          Work.WilG0.Omega_mono_FD (le_max_left _ _) le_rfl (hGood D f L hf)
        have h2 : Work.WilkG4c.AlDgListSlice p n f L ∩ Work.WilkG4c.AlBad p n f L ∈
            S.Ω (max (max aC (aBd + 1) + 1) aB)
              (MvPolynomial.eval ![D, L.length] bB) (p + (n + 1) + 1) :=
          Work.WilG0.Omega_mono_FD (le_max_right _ _) le_rfl (hB D f L hf)
        have hun := Work.WilG0.Omega_union2 h1 h2
        refine Work.WilG1.Omega.mono hun (le_max_left _ _) ?_
        simp only [MvPolynomial.eval_add, eval_bind_zero]
        exact Nat.le_add_left _ _

/-- **The slice (fibre) derivative graph is `Ω`-definable**, with format uniform in the order
`|L|` and degree a polynomial in `(D, |L|)`. -/
theorem AlDgListSlice_mem (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (p n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      Work.WilkG4c.AlDgListSlice p n f L ∈
        S.Ω a (MvPolynomial.eval ![D, L.length] b) (p + (n + 1) + 1) :=
  AlDgListSlice_mem_aux S hcd hder p n F0

end Work.WilG4cR
