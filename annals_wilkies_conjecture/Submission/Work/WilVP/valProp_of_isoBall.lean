import Mathlib
import Submission.Work.WilVP.Defs
import Submission.Work.WilC5.ValProp
import Submission.Work.WilC5.ValArith
import Submission.Work.WilVP.exists_bdd_family
import Submission.Work.WilVP.fibre_value_mem
import Submission.Work.WilVP.finite_fibre_mem
import Submission.Work.WilC4.dcl_elementary
import Submission.Work.WilC4.definableElt_of_mem_left
import Submission.Work.WilC4.elementary_valBase
import Submission.Work.WilC4.valBase_of_dcl_closed
import Submission.Work.WilC4.dcl_add
import Submission.Work.WilC4.dcl_neg

namespace Work.WilVP

open FirstOrder FirstOrder.Language

/-! ## Helpers: the carrier of an elementary substructure as a field -/

section Helpers

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
  [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
  [(FirstOrder.Language.constantsOn ℝ).Structure M]

/-- An elementary substructure of a model of `TR` is `dcl`-closed, in the elementwise form used
below. -/
private theorem dclClosure (S : WilkiesDesign.CG.LRc.ElementarySubstructure M) :
    ∀ x : M, Work.WilC4.DefinableElt (S : Set M) ∅ x ↔ x ∈ (S : Set M) :=
  fun x => Set.ext_iff.mp (Work.WilC4.dcl_elementary S) x

/-- `0` lies in the carrier of an elementary substructure: `0 = 1 + (-1)`, and the definable
closure is closed under addition and negation. -/
private theorem zero_mem_elemSub (S : WilkiesDesign.CG.LRc.ElementarySubstructure M) :
    (0 : M) ∈ (S : Set M) := by
  have hSdcl := dclClosure S
  have h1 : (1 : M) ∈ (S : Set M) := Work.WilC4.one_mem_of_dcl_closed hSdcl
  have hz : (1 : M) + (-1 : M) ∈ Work.WilC4.Dcl (S : Set M) ∅ :=
    Work.WilC4.dcl_add ((hSdcl 1).mpr h1) (Work.WilC4.dcl_neg ((hSdcl 1).mpr h1))
  have hz' : (0 : M) ∈ Work.WilC4.Dcl (S : Set M) ∅ := by simpa using hz
  exact (hSdcl 0).mp hz'

/-- The carrier of an elementary substructure is closed under addition. -/
private theorem add_mem_elemSub (S : WilkiesDesign.CG.LRc.ElementarySubstructure M) {x y : M}
    (hx : x ∈ (S : Set M)) (hy : y ∈ (S : Set M)) : x + y ∈ (S : Set M) := by
  have hSdcl := dclClosure S
  exact (hSdcl _).mp (Work.WilC4.dcl_add ((hSdcl x).mpr hx) ((hSdcl y).mpr hy))

/-- The natural constants lie in the carrier of an elementary substructure. -/
private theorem natCast_mem_elemSub (S : WilkiesDesign.CG.LRc.ElementarySubstructure M)
    (n : ℕ) : ((n : M)) ∈ (S : Set M) := by
  have h1 : (1 : M) ∈ (S : Set M) := (Work.WilC4.elementary_valBase S).1
  induction n with
  | zero => simpa using zero_mem_elemSub S
  | succ n ih =>
      have : ((Nat.succ n : ℕ) : M) = (n : M) + 1 := by push_cast; ring
      rw [this]
      exact add_mem_elemSub S ih h1

/-- **A bound in `S`.**  If `c ∈ S` and `c * z` is a unit, then `z` is dominated by an element of
`S`: `|z| ≤ (N+1)·|c⁻¹|` from `IsUnitVal (c*z)`, and `|c⁻¹| ≤ c⁻² + 1`
(`|c⁻¹|² - 2|c⁻¹| + 1 = (|c⁻¹| - 1)² ≥ 0`), so `R := (N+1)·(c⁻² + 1) ∈ S` works. -/
private theorem bound_mem_of_unit (S : WilkiesDesign.CG.LRc.ElementarySubstructure M) {z c : M}
    (hc : c ∈ (S : Set M)) (hu : WilkiesDesign.CG.IsUnitVal (c * z)) :
    ∃ R ∈ (S : Set M), |z| ≤ R := by
  obtain ⟨N, hlow, hhigh⟩ := hu
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_mul, abs_zero] at hlow
    have hpos : (0 : M) < ((N : M) + 1)⁻¹ := by positivity
    linarith
  have hvc := Work.WilC4.elementary_valBase S
  have h1 : (1 : M) ∈ (S : Set M) := hvc.1
  have hinv : c⁻¹ ∈ (S : Set M) := hvc.2.1 c hc hc0
  refine ⟨((N : M) + 1) * (c⁻¹ * c⁻¹ + 1), ?_, ?_⟩
  · have hd2 : c⁻¹ * c⁻¹ ∈ (S : Set M) := hvc.2.2 _ hinv _ hinv
    exact hvc.2.2 _ (add_mem_elemSub S (natCast_mem_elemSub S N) h1) _
      (add_mem_elemSub S hd2 h1)
  · have hNpos : (0 : M) < (N : M) + 1 := by positivity
    have hcabs : 0 < |c| := abs_pos.mpr hc0
    have hle1 : |z| ≤ ((N : M) + 1) * |c⁻¹| := by
      have key : |c| * |z| = |c * z| := (abs_mul c z).symm
      have hle : |c| * |z| ≤ (N : M) + 1 := by rw [key]; exact hhigh
      have hcc : |c| * |c⁻¹| = 1 := by rw [abs_inv, mul_inv_cancel₀ (ne_of_gt hcabs)]
      calc |z| = |z| * (|c| * |c⁻¹|) := by rw [hcc, mul_one]
        _ = (|c| * |z|) * |c⁻¹| := by ring
        _ ≤ ((N : M) + 1) * |c⁻¹| := mul_le_mul_of_nonneg_right hle (abs_nonneg _)
    have hdle : |c⁻¹| ≤ c⁻¹ * c⁻¹ + 1 := by
      nlinarith [sq_nonneg (|c⁻¹| - 1), abs_nonneg (c⁻¹), sq_abs (c⁻¹)]
    calc |z| ≤ ((N : M) + 1) * |c⁻¹| := hle1
      _ ≤ ((N : M) + 1) * (c⁻¹ * c⁻¹ + 1) :=
          mul_le_mul_of_nonneg_left hdle (le_of_lt hNpos)

end Helpers

/-- **The valuation property from uniform iso-balls in all models.**
`hcloser` is `Work.WilVP.exists_closer_translate` (packaged as a hypothesis so that this file need
not import `Submission.Work.WilC5.stdPart`); `h` is `Work.WilVP.IsoBallProp` in every model of
`TR`.
Proof (contradiction): fix `M ⊨ TR`, `S`, `z`, `w ≠ 0` with `w` definable from `S ∪ {z}` and
every `c ∈ S` failing to make `cw` a unit.
1. `z ∉ S`: otherwise `w ∈ S` (definable from `S ∪ {z} = S`; `Work.WilC4.dcl_elementary` says
   `Dcl S ∅ = S`, or use `S.meetsDefinable`), and `c := w⁻¹` makes `cw = 1` a unit.  Facts about
   `S` (membership of `0`, `1`, the real constants, inverse, products) come from
   `Substructure.fun_mem` applied to the `LRc` function symbols
   (`Ring.zeroFunc`, `Ring.oneFunc`, `Ring.addFunc`, `Ring.mulFunc`, `Ring.invFunc`, the constant
   symbol `Sum.inr r`), or from `Work.WilC4.dcl_elementary` plus definability.
2. Hence every `a ∈ S` has `z - a ≠ 0`, and the negation of the goal is
   `∀ a ∈ S, ∃ c ∈ S, IsUnitVal (c * (z - a))`; in particular `a = 0` gives `c₀ ∈ S` with
   `IsUnitVal (c₀ z)`, so `c₀ ≠ 0` and `|z| ≤ R := (N₀+1) * |c₀⁻¹| ∈ S`.
3. `Work.WilVP.exists_bdd_family` gives `k, c, Y`; `IsoBallProp M` (i.e. `h M hM`) applied to `Y`
   gives `N, P`; every point of the `c`-fibre of `P` lies in `S`
   (`Work.WilVP.finite_fibre_mem`), and `z ∉ P_c`.  If `P_c = ∅` take `a := 0 ∈ S`; otherwise
   take `p* ∈ P_c` nearest to `z` (finite nonempty set), so `|z - p*| ≤ |z - p|` for all
   `p ∈ P_c`.
4. `hcloser` at `p*` (with `hold` from step 2, `z - p* ≠ 0` from `z ∉ S`) gives `a ∈ S` with
   `(N:M) * |z - a| < |z - p*| ≤ |z - p|`, so the hypothesis of `IsoBallProp` holds at
   `(x,y₀,y) = (z,w,a)`.
5. `IsoBallProp` gives `y₁` with `(a,y₁,c) ∈ Y`, `|y₁| ≤ N|w|`, `|w| ≤ N|y₁|`.  Then
   `y₁ ∈ S` (`Work.WilVP.fibre_value_mem`), `y₁ ≠ 0`, and `y₁⁻¹ ∈ S` makes `y₁⁻¹ w` a unit,
   contradicting the hypothesis. -/
theorem valProp_of_isoBall
    (hcloser : ∀ (M : Type) [Field M] [LinearOrder M] [IsStrictOrderedRing M]
      [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
      [(FirstOrder.Language.constantsOn ℝ).Structure M]
      [FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR]
      (S : WilkiesDesign.CG.LRc.ElementarySubstructure M) {z p : M} (hp : p ∈ (S : Set M))
      (hzp : z - p ≠ 0)
      (hold : ∃ c ∈ (S : Set M), WilkiesDesign.CG.IsUnitVal (c * (z - p))) (K : ℕ),
      ∃ a ∈ (S : Set M), (K : M) * |z - a| < |z - p|)
    (h : ∀ (M : Type) [Field M] [LinearOrder M] [IsStrictOrderedRing M]
      [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
      [(FirstOrder.Language.constantsOn ℝ).Structure M],
      FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR → Work.WilVP.IsoBallProp M) :
    Work.WilC5.ValProp := by
  intro M _ _ _ _ _ _ hM S z w hw0 hwdef hnotunit
  classical
  by_contra hgoal
  -- ### Step 1: `z ∉ S`
  have hzS : z ∉ (S : Set M) := by
    intro hz
    have hwS : w ∈ (S : Set M) := by
      have hsub : (S : Set M) ∪ {z} = (S : Set M) := by
        rw [Set.union_eq_left]
        exact Set.singleton_subset_iff.mpr hz
      have hd' : (S : Set M).Definable WilkiesDesign.CG.LRc {fun _ : Fin 1 => w} := by
        have h2 := hwdef
        rwa [hsub] at h2
      have hdE : Work.WilC4.DefinableElt (S : Set M) ∅ w := by
        rw [Work.WilC4.DefinableElt, Set.union_empty]
        exact hd'
      have hD : w ∈ Work.WilC4.Dcl (S : Set M) ∅ := hdE
      rwa [Work.WilC4.dcl_elementary S] at hD
    have hwinv : w⁻¹ ∈ (S : Set M) := (Work.WilC4.elementary_valBase S).2.1 w hwS hw0
    refine hnotunit w⁻¹ hwinv ?_
    rw [inv_mul_cancel₀ hw0]
    exact Work.WilC5.IsUnitVal_one
  -- ### Step 2: every translate is a unit multiple, and `z` has a bound in `S`
  have hold_all : ∀ a ∈ (S : Set M),
      ∃ c ∈ (S : Set M), WilkiesDesign.CG.IsUnitVal (c * (z - a)) := by
    intro a ha
    by_contra hcon
    apply hgoal
    refine ⟨a, ha, ?_, ?_⟩
    · intro hza
      exact hzS (sub_eq_zero.mp hza ▸ ha)
    · intro c hc hcu
      exact hcon ⟨c, hc, hcu⟩
  obtain ⟨c₀, hc₀S, hc₀unit⟩ := hold_all 0 (zero_mem_elemSub S)
  have hc₀unit' : WilkiesDesign.CG.IsUnitVal (c₀ * z) := by simpa using hc₀unit
  obtain ⟨R, hRS, hzR⟩ := bound_mem_of_unit S hc₀S hc₀unit'
  -- ### Step 3: the bounded family and the iso-ball data
  obtain ⟨k, c, Y, hc, hYdef, hYfun, hYbdd, hzY⟩ :=
    Work.WilVP.exists_bdd_family S hRS hzR hwdef
  obtain ⟨N, _hN, P, _hPdef, hP⟩ := h M hM k Y hYdef hYfun hYbdd
  -- ### Step 4: a point `a ∈ S` outside the ball of radius `|z - p|/N` around `z`
  have hmain : ∃ a ∈ (S : Set M),
      ∀ p : M, Fin.cons p c ∈ P → (N : M) * |a - z| < |z - p| := by
    by_cases hne : ({x : M | Fin.cons x c ∈ P} : Set M).Nonempty
    · have hfin : ({x : M | Fin.cons x c ∈ P} : Set M).Finite := by
        rw [← Set.encard_lt_top_iff]
        exact lt_of_le_of_lt (hP c).1 (ENat.natCast_lt_top N)
      obtain ⟨pstar, hpstarP, hpstar_min⟩ :=
        Set.exists_min_image {x : M | Fin.cons x c ∈ P} (fun q => |z - q|) hfin hne
      have hpstarS : pstar ∈ (S : Set M) :=
        Work.WilVP.finite_fibre_mem S hc _hPdef (hP c).1 hpstarP
      have hzps : z - pstar ≠ 0 := by
        intro h
        exact hzS (sub_eq_zero.mp h ▸ hpstarS)
      obtain ⟨a, haS, ha_lt⟩ :=
        hcloser M S hpstarS hzps (hold_all pstar hpstarS) N
      refine ⟨a, haS, ?_⟩
      intro p hp
      calc (N : M) * |a - z| = (N : M) * |z - a| := by rw [abs_sub_comm]
        _ < |z - pstar| := ha_lt
        _ ≤ |z - p| := hpstar_min p hp
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      refine ⟨0, zero_mem_elemSub S, ?_⟩
      intro p hp
      exact absurd (hne ▸ hp : p ∈ (∅ : Set M)) (Set.notMem_empty p)
  obtain ⟨a, haS, hball⟩ := hmain
  -- ### Step 5: the iso-ball at `(x, y₀, y) = (z, w, a)` gives the contradiction
  obtain ⟨y₁, hy₁Y, hy₁le, hle₁⟩ := (hP c).2 z w a hzY hw0 hball
  have hy₁S : y₁ ∈ (S : Set M) :=
    Work.WilVP.fibre_value_mem S hc hYdef (fun x y y' h1 h2 => hYfun c x y y' h1 h2) haS hy₁Y
  have hy₁0 : y₁ ≠ 0 := by
    intro h
    rw [h, abs_zero, mul_zero] at hle₁
    exact hw0 (abs_eq_zero.mp (le_antisymm hle₁ (abs_nonneg w)))
  have hy₁invS : y₁⁻¹ ∈ (S : Set M) := (Work.WilC4.elementary_valBase S).2.1 y₁ hy₁S hy₁0
  have hunit : WilkiesDesign.CG.IsUnitVal (y₁⁻¹ * w) := by
    have hsa : Work.WilC5.SameArch w y₁ := by
      refine ⟨N, ?_, ?_⟩
      · exact le_trans hle₁
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (abs_nonneg y₁))
      · exact le_trans hy₁le
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (abs_nonneg w))
    have h := (Work.WilC5.SameArch_iff_IsUnitVal_mul_inv hy₁0).mp hsa
    rwa [mul_comm] at h
  exact hnotunit y₁⁻¹ hy₁invS hunit

end Work.WilVP
