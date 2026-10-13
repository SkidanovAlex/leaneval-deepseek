/-
  WilG4c — the fibre (slice) derivative graph `AlDgListSlice` is `Ω`-definable, with format
  uniform in the order `|L|` and degree a polynomial in `D` and `|L|`.

  ## The shape of the proof

  Strong induction on the number `p` of parameters (and on the input format `F0`).  For fixed
  `p`, let

    `Bad := AlBad p n f L`,  `Good := AlGood p n f L = Badᶜ`,  `T := AlDgListSlice p n f L`.

  Then `T = (T ∩ Good) ∪ (T ∩ Bad)` (as sets), and the two halves are handled by the library:

  * `CritFixGoodMem` identifies `T ∩ Good = CritFix ∩ Good`, where `CritFix` is the corrected
    punctured-limit criterion; its `Ω`-bound is `CritFixOmega` for `CritFix`, intersected with
    the complement of `Bad` (whose `Ω`-bound is `AlBadMem`).

  * `AlDgListSliceBadMem` bounds `T ∩ Bad`: over the *thin* parameter projection `AlBadPar`
    (`AlBadParThin`) a sharp cell decomposition, the thin-cell parametrisation `thinCellParam`,
    the pull-back `PullFamGraphMem` and the slice transport `SliceLift` reduce it to the
    induction hypothesis at the (fewer) parameters of each cell.

  All format bounds are constants of `p, n, F0`, and the degrees are polynomials in `D` and
  `|L|`; the final `(a, b)` is assembled by `Omega_mono_FD` and `Omega_inter2`/`Omega_union2`.
-/
import Mathlib
import Submission.Work.WilG4c.AlSliceBase
import Submission.Work.WilG4c.SlicedDerivDefs
import Submission.Work.WilG4c.CritFixDefs
import Submission.Work.WilG4c.CritFixGoodMem
import Submission.Work.WilG4c.CritFixOmega
import Submission.Work.WilG4c.AlBadMem
import Submission.Work.WilG4c.AlDgListSliceBadMem
import Submission.Work.WilG0.API

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

theorem AlDgListSliceMem (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (p n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      Work.WilkG4c.AlDgListSlice p n f L ∈
        S.Ω a (MvPolynomial.eval ![D, L.length] b) (p + (n + 1) + 1) := by
  suffices H : ∀ p : ℕ, ∀ F0 : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      Work.WilkG4c.AlDgListSlice p n f L ∈
        S.Ω a (MvPolynomial.eval ![D, L.length] b) (p + (n + 1) + 1) from H p F0
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
    intro F0
    -- the criterion (`AlGood`) half
    obtain ⟨aG, bG, hG⟩ := Work.WilG4c.CritFixOmega S hder p n F0
    -- the bad locus
    obtain ⟨aBP, bBP, hBP⟩ := Work.WilG4c.AlBadMem S hcd hder p n F0
    -- the recursion (`AlBad`) half
    obtain ⟨aR, bR, hR⟩ :=
      Work.WilG4c.AlDgListSliceBadMem S hcd hder n p
        (fun F0' => by
          obtain ⟨a, b, hab⟩ := Work.WilG4c.AlBadMem S hcd hder p n F0'
          exact ⟨a, b, fun D f L hf => (hab D f L hf).2⟩)
        (fun p' hp' F0' => ih p' hp' F0') F0
    refine ⟨max (max aG (aBP + 1)) aR + 2, (bG + bBP + bR) + (bG + bBP + bR), ?_⟩
    intro D f L hf
    -- degree bookkeeping
    have hbG : MvPolynomial.eval ![D, L.length] bG ≤
        MvPolynomial.eval ![D, L.length] (bG + bBP + bR) := by
      simp only [MvPolynomial.eval_add]; omega
    have hbBP : MvPolynomial.eval ![D, L.length] bBP ≤
        MvPolynomial.eval ![D, L.length] (bG + bBP + bR) := by
      simp only [MvPolynomial.eval_add]; omega
    have hbR : MvPolynomial.eval ![D, L.length] bR ≤
        MvPolynomial.eval ![D, L.length] (bG + bBP + bR) := by
      simp only [MvPolynomial.eval_add]; omega
    have hbGBP : MvPolynomial.eval ![D, L.length] (bG + bBP) ≤
        MvPolynomial.eval ![D, L.length] (bG + bBP + bR) := by
      simp only [MvPolynomial.eval_add]; omega
    -- the `AlGood` half agrees with the criterion
    have hgoodEq := Work.WilkG4c.CritFixGoodMem S hcd hder p n F0 D f L hf
    have hgood : Work.WilkG4c.AlDgListSlice p n f L ∩ Work.WilkG4c.AlGood p n f L ∈
        S.Ω (max (max aG (aBP + 1)) aR + 2)
          (MvPolynomial.eval ![D, L.length] (bG + bBP + bR)) (p + (n + 1) + 1) := by
      rw [hgoodEq]
      have hc : Work.WilkG4c.CritFix p n f L ∈
          S.Ω (max (max aG (aBP + 1)) aR + 1) (MvPolynomial.eval ![D, L.length] bG)
            (p + (n + 1) + 1) :=
        Work.WilG0.Omega_mono_FD (by omega) le_rfl (hG D f L hf)
      have hb : Work.WilkG4c.AlBad p n f L ∈
          S.Ω (max (max aG (aBP + 1)) aR) (MvPolynomial.eval ![D, L.length] bBP)
            (p + (n + 1) + 1) :=
        Work.WilG0.Omega_mono_FD (by omega) le_rfl (hBP D f L hf).1
      have hgc : Work.WilkG4c.AlGood p n f L ∈
          S.Ω (max (max aG (aBP + 1)) aR + 1) (MvPolynomial.eval ![D, L.length] bBP)
            (p + (n + 1) + 1) :=
        S.compl hb
      have hinter := Work.WilG0.Omega_inter2 hc hgc
      refine Work.WilG0.Omega_mono_FD le_rfl ?_ hinter
      simp only [MvPolynomial.eval_add]
      omega
    -- the `AlBad` half
    have hbad : Work.WilkG4c.AlDgListSlice p n f L ∩ Work.WilkG4c.AlBad p n f L ∈
        S.Ω (max (max aG (aBP + 1)) aR + 2)
          (MvPolynomial.eval ![D, L.length] (bG + bBP + bR)) (p + (n + 1) + 1) :=
      Work.WilG0.Omega_mono_FD (by omega) hbR (hR D f L hf)
    -- assemble
    have hsplit : Work.WilkG4c.AlDgListSlice p n f L =
        (Work.WilkG4c.AlDgListSlice p n f L ∩ Work.WilkG4c.AlGood p n f L) ∪
          (Work.WilkG4c.AlDgListSlice p n f L ∩ Work.WilkG4c.AlBad p n f L) := by
      rw [Work.WilkG4c.AlGood]
      ext z
      by_cases h : z ∈ Work.WilkG4c.AlBad p n f L <;> simp [h]
    rw [hsplit, MvPolynomial.eval_add]
    exact Work.WilG0.Omega_union2 hgood hbad

end Work.WilkG4c

/-! The directory-induced name `Work.WilG4c` of the same theorem (the convention used by the
sibling modules of this area, cf. e.g. `AlDgListSliceNil`, `AlDgListSliceZero`). -/
namespace Work.WilG4c

theorem AlDgListSliceMem (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (p n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      Work.WilkG4c.AlDgListSlice p n f L ∈
        S.Ω a (MvPolynomial.eval ![D, L.length] b) (p + (n + 1) + 1) :=
  Work.WilkG4c.AlDgListSliceMem S hcd hder p n F0

end Work.WilG4c
