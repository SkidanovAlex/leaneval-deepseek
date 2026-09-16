import ChallengeDeps
import Submission.Commons.FieldTheory.Polynomial.finite_monic_le
import Submission.ZagierHoffmanProof.Summability

-- The deprecated alias instance `FunctionField.valuedFqtInfty` duplicates the canonical
-- `Valued (CompletionAtInfty F) ℤᵐ⁰` instance and confuses typeclass search here.
attribute [-instance] FunctionField.valuedFqtInfty

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial RatFunc
open scoped WithZero Topology BigOperators
open WithZero

/-!
# Block decomposition of multiple zeta values

Every monic tuple of length `r ≥ 1` has a leading polynomial (the one of largest degree,
at index `0`).  Grouping tuples by the degree of the leading polynomial splits the
multiple-zeta sum into a sum over `d : ℕ` of "power sums" `S_d(𝔰)` (each a finite sum
over the degree-`d` block).  This file defines those blocks and proves the blocks are
finite; the decomposition `ζ_A = ∑'_d S_d` is the next step.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- One summand of the multiple-zeta sum of index `𝔰` (the polynomial factors embedded
through `RatFunc` into the completion). -/
noncomputable def zetaTerm {r : ℕ} (𝔰 : Fin r → ℕ+) (a : monicStrictAntiNatDegree F r) :
    RatFunc.CompletionAtInfty F :=
  (∏ i : Fin r, ((a.val i : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (𝔰 i : ℕ))⁻¹

/-- Tuples of length `r ≥ 1` whose leading polynomial has degree `d`. -/
def blockSet (r : ℕ) (hr : 0 < r) (d : ℕ) : Set (monicStrictAntiNatDegree F r) :=
  {a | (a.val ⟨0, hr⟩).natDegree = d}

/-- The degree-`d` block is finite: every polynomial in the tuple is then monic of degree
at most `d`. -/
theorem finite_block {r : ℕ} (hr : 0 < r) (d : ℕ) :
    Set.Finite (blockSet F r hr d) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  haveI hcod : Finite {p : F[X] // p.Monic ∧ p.natDegree ≤ d} := by
    simpa using (Commons.FieldTheory.Polynomial.finite_monic_le F d)
  let S : Set (monicStrictAntiNatDegree F r) := blockSet F r hr d
  have hbound : ∀ (a : monicStrictAntiNatDegree F r), a ∈ S →
      ∀ i : Fin r, (a.val i).natDegree ≤ d := by
    intro a ha i
    have hdeg0 : (a.val ⟨0, hr⟩).natDegree = d := by simpa [S, blockSet] using ha
    by_cases hi0 : (i : ℕ) = 0
    · have hi : i = ⟨0, hr⟩ := Fin.ext (by simpa using hi0)
      rw [hi]
      rw [hdeg0]
    · have h0i : (⟨0, hr⟩ : Fin r) < i :=
        (Fin.mk_lt_mk).2 (Nat.pos_of_ne_zero hi0)
      have hlt : (a.val i).natDegree < (a.val ⟨0, hr⟩).natDegree := by
        simpa using a.2.1 h0i
      rw [hdeg0] at hlt
      exact le_of_lt hlt
  let f : S → Fin r → {p : F[X] // p.Monic ∧ p.natDegree ≤ d} := fun a i =>
    ⟨a.val.1 i, a.val.2.2 i, hbound a.1 a.2 i⟩
  have hinj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    funext i
    simpa using congrArg Subtype.val (congrFun h i)
  have hfinS : Finite S := Finite.of_injective f hinj
  exact hfinS

/-- The degree-`d` power sum `S_d(𝔰)`: sum of the zeta summands over the degree-`d` block
(a finite sum; `Finite` shown by `finite_block`). -/
noncomputable def S (r : ℕ) (hr : 0 < r) (𝔰 : Fin r → ℕ+) (d : ℕ) :
    RatFunc.CompletionAtInfty F :=
  ∑' a : {a : monicStrictAntiNatDegree F r // a ∈ blockSet F r hr d}, zetaTerm F 𝔰 a.1



/-- The summand family of `ζ_A`, exactly as it appears in its definition. -/
noncomputable def zetaTermAux {r : ℕ} (𝔰 : Fin r → ℕ+) (a : monicStrictAntiNatDegree F r) :
    RatFunc.CompletionAtInfty F :=
  (∏ i : Fin r, a.val i ^ (𝔰 i : ℕ))⁻¹

/-- `zetaTerm` (factors embedded through `RatFunc`) is the same summand as the one used in
the definition of `ζ_A`. -/
lemma zetaTerm_eq_zetaTermAux {r : ℕ} (𝔰 : Fin r → ℕ+) (a : monicStrictAntiNatDegree F r) :
    zetaTerm F 𝔰 a = zetaTermAux F 𝔰 a := by
  rfl

/-- `ζ_A` is the tsum of `zetaTermAux` (i.e. of `zetaTerm`), by definition. -/
lemma ζ_A_eq_tsum_zetaTerm {r : ℕ} (𝔰 : Fin r → ℕ+) :
    ζ_A F 𝔰 = ∑' a : monicStrictAntiNatDegree F r, zetaTermAux F 𝔰 a := by
  rfl

/-- The `ζ_A` summand family is summable (depth `r ≥ 1`). -/
lemma summable_zetaTermAux {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) :
    Summable (fun a : monicStrictAntiNatDegree F r => zetaTermAux F 𝔰 a) := by
  rw [show (fun a : monicStrictAntiNatDegree F r => zetaTermAux F 𝔰 a) =
      fun a => zetaTerm F 𝔰 a from by
        funext a
        exact zetaTerm_eq_zetaTermAux F 𝔰 a]
  exact summable_zeta_term F (r := r) hr 𝔰

/-- Block decomposition: `ζ_A(𝔰)` is the sum over `d` of the degree-`d` power sums
`S_d(𝔰)`.  (Depth `r ≥ 1`.) -/
lemma zeta_eq_tsum_block {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) :
    ζ_A F 𝔰 = ∑' d : ℕ, S F r hr 𝔰 d := by
  classical
  let g : monicStrictAntiNatDegree F r → ℕ := fun a => (a.val ⟨0, hr⟩).natDegree
  let e : ((d : ℕ) × {a : monicStrictAntiNatDegree F r // g a = d}) ≃
      monicStrictAntiNatDegree F r := Equiv.sigmaFiberEquiv g
  -- step 1: ζ_A = ∑ over whole type of zetaTerm
  have h_zeta : ζ_A F 𝔰 = ∑' a : monicStrictAntiNatDegree F r, zetaTerm F 𝔰 a := by
    rw [ζ_A_eq_tsum_zetaTerm F 𝔰]
    exact tsum_congr (fun a => zetaTerm_eq_zetaTermAux F 𝔰 a)
  -- step 2: whole-type tsum = sigma-type tsum
  have h_step2 : (∑' a : monicStrictAntiNatDegree F r, zetaTerm F 𝔰 a) =
      ∑' p : (d : ℕ) × {a : monicStrictAntiNatDegree F r // g a = d},
        zetaTerm F 𝔰 p.2.1 := by
    have hts := Equiv.tsum_eq e (fun a : monicStrictAntiNatDegree F r => zetaTerm F 𝔰 a)
    -- hts : ∑' c, zetaTerm F 𝔰 (e c) = ∑' a, zetaTerm F 𝔰 a ; e c = c.2.1
    calc
      (∑' a : monicStrictAntiNatDegree F r, zetaTerm F 𝔰 a)
          = ∑' c : (d : ℕ) × {a : monicStrictAntiNatDegree F r // g a = d},
              zetaTerm F 𝔰 (e c) := hts.symm
      _ = ∑' p : (d : ℕ) × {a : monicStrictAntiNatDegree F r // g a = d},
              zetaTerm F 𝔰 p.2.1 := by
            apply tsum_congr
            intro p
            congr
  -- step 3: sigma tsum splits over d (Fubini)
  have h_step3 : (∑' p : (d : ℕ) × {a : monicStrictAntiNatDegree F r // g a = d},
        zetaTerm F 𝔰 p.2.1) =
      ∑' d : ℕ, S F r hr 𝔰 d := by
    have hz : Summable (fun a : monicStrictAntiNatDegree F r => zetaTerm F 𝔰 a) :=
      summable_zeta_term F (r := r) hr 𝔰
    have hσsum : Summable (fun p : (d : ℕ) × {a : monicStrictAntiNatDegree F r // g a = d} =>
        zetaTerm F 𝔰 p.2.1) := by
      have hss : Summable (fun p : (d : ℕ) × {a : monicStrictAntiNatDegree F r // g a = d} =>
          zetaTerm F 𝔰 (e p)) := (Equiv.summable_iff e).mpr hz
      refine Summable.congr hss ?_
      intro p
      congr
    have hfiber : ∀ d : ℕ, Summable (fun c : {a : monicStrictAntiNatDegree F r // g a = d} =>
        zetaTerm F 𝔰 c.1) := by
      intro d
      have hfin : Finite {a : monicStrictAntiNatDegree F r // a ∈ blockSet F r hr d} :=
        finite_block F hr d
      -- {a // g a = d} is definitionally the same subtype as {a // a ∈ blockSet F r hr d}
      change Finite {a : monicStrictAntiNatDegree F r // g a = d} at hfin
      exact Summable.of_finite (f := fun c : {a : monicStrictAntiNatDegree F r // g a = d} =>
        zetaTerm F 𝔰 c.1)
    have hts := Summable.tsum_sigma' (β := ℕ)
      (γ := fun d : ℕ => {a : monicStrictAntiNatDegree F r // g a = d}) hfiber hσsum
    rw [hts]
    apply tsum_congr
    intro d
    -- inner sum = S d
    change (∑' c : {a : monicStrictAntiNatDegree F r // a ∈ blockSet F r hr d},
        zetaTerm F 𝔰 c.1) = S F r hr 𝔰 d
    rfl
  exact h_zeta.trans (h_step2.trans h_step3)

end ZagierHoffmanPositiveChar
