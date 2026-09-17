import Submission.E8FreudenthalGen
import Submission.E8Star
import Submission.E8Rec
import Submission.E8Character
import Submission.E8ConstChar
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_wact_small_height_length

/-!
# The Kostant candidate: the Casimir eigenvalue is invariant under the dot action

The route to the Weyl character formula for the *constituents* of the tensor square
(see the roadmap in `Submission.lean`, SESSION 32 §5) runs through the "Kostant candidate"

  `S_x = A_{x+ρ}/A_ρ = Σ_{w∈W} ε(w)·chM(w·x)`,   `w·x := w(x+ρ) - ρ`,

the Euler characteristic of Verma modules: its coefficient function `m_x` satisfies the
hypotheses (a)–(d) of `Submission.E8Character.eq_of_freudenthal`, whence (by `eq_of_freudenthal`
applied to `Mnu x`) `m_x = Mtab (x, ·)`.

The decisive input is that the Casimir eigenvalue of the Verma module `M(w·x)` does not depend on
`w`:

  **`casOf (w·x) = casOf x`**,

because (this file) `casOf ν = (1/60)·(⟪ν+ρ,ν+ρ⟫ - ⟪ρ,ρ⟫)` is a function of `qq (ν + ρ)` alone,
and `qq` is `W`-invariant (so `qq (w(x+ρ)) = qq (x+ρ)` and `(w·x) + ρ = w(x+ρ)`).

This file also packages `eq_of_freudenthal` with the four hypotheses for the c-table `Mnu`, so that
whoever proves (a)–(d) for `m_x` obtains `m_x = Mtab (x, ·)` immediately (see `eq_of_MnuQ`).
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

noncomputable section
open scoped BigOperators

namespace Submission.E8Kostant

open Submission.E8Character Submission.E8Freudenthal Submission.E8FreudenthalGen
open Submission.E8Numerics
open Submission.E8Extract (ord40get)
open Submission.E8Casimir (pR)
open Submission.E8Character (posCon Bint brk htOf dc)
open Submission.WeylReflect (Dominant)
open UniversalEnvelopingAlgebra

/-- The Weyl vector `ρ = (1,…,1)`. -/
abbrev rhoV : Fin 8 → ℤ := Submission.E8Freudenthal.rhoZ
open Commons.LinearAlgebra.Matrix.Cartan (wact qZ_wact)

/-- `Bint` is `qq` shifted by `ρ`. -/
lemma Bint_eq_qq (ν : Fin 8 → ℤ) : Bint ν = qq (ν + rhoV) := by
  have hsum : qq (ν + rhoV) = ∑ i, ∑ j, (ν + rhoV) i * E8inv i j * (ν + rhoV) j := rfl
  rw [Bint, hsum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : (ν + rhoV) i = ν i + 1 := by rw [Pi.add_apply]; rfl
  have h2 : (ν + rhoV) j = ν j + 1 := by rw [Pi.add_apply]; rfl
  rw [h1, h2]

/-- **The Casimir eigenvalue as a function of `qq (ν+ρ)` only.** -/
theorem casOf_eq_bil (ν : Fin 8 → ℤ) :
    casOf ν = (1 / 60) * (((qq (ν + rhoV) - qq rhoV : ℤ)) : ℂ) := by
  have h0 : Bint (0 : Fin 8 → ℤ) = qq rhoV := by
    rw [Bint_eq_qq]
    simp
  rw [casOf, cnu_eq_gen, Bint_eq_qq, h0]

/-- The dot action `w · x = w(x+ρ) - ρ`. -/
def dotact (L : List (Fin 8)) (x : Fin 8 → ℤ) : Fin 8 → ℤ := wact L (x + rhoV) - rhoV

/-- `(w · x) + ρ = w (x + ρ)`. -/
lemma dotact_add_rho (L : List (Fin 8)) (x : Fin 8 → ℤ) :
    dotact L x + rhoV = wact L (x + rhoV) := by
  rw [dotact]; abel

/-- ⭐ **The Casimir eigenvalue is invariant under the dot action.** -/
theorem casOf_dotact (L : List (Fin 8)) (x : Fin 8 → ℤ) :
    casOf (dotact L x) = casOf x := by
  rw [casOf_eq_bil, casOf_eq_bil, dotact_add_rho]
  rw [show qq (wact L (x + rhoV)) = qq (x + rhoV) from qZ_wact L (x + rhoV)]

/-! ## Packaging `eq_of_freudenthal` with the c-table

The four hypotheses (a)–(d) for the candidate function `Mnu i` are `Mnu_top`, `Mnu_support`,
`Mnu_dc` (`Submission/E8Star.lean`) and `Mnu_freud` (`Submission/E8Rec.lean`).  Consequently *any*
function satisfying (a)–(d) with top weight `ord40get i` is `Mnu i` — in particular the coefficient
function `m_x` of the Kostant candidate `S_x = A_{x+ρ}/A_ρ` (the missing input there is (d), the
Freudenthal recursion, which follows from `casOf_dotact`; see the roadmap). -/

/-- ⭐ **Uniqueness, packaged for the c-table.**  A function satisfying the four hypotheses of
`eq_of_freudenthal` at the top weight `ord40get i` is the candidate character `Mnu i`. -/
theorem eq_of_MnuQ (i : Fin 40) {m : (Fin 8 → ℤ) → ℚ}
    (ha : m (ord40get i) = 1)
    (hb : ∀ v, m v ≠ 0 → ord40get i - v = 0 ∨ posCon (ord40get i - v))
    (hc : ∀ v, m (dc v) = m v)
    (hd : ∀ ν, Dominant ν → ord40get i - ν ≠ 0 → posCon (ord40get i - ν) →
      (Bint (ord40get i) - Bint ν) * m ν
        = 2 * ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (ord40get i - ν)).toNat,
            (brk (ν + k • pR j) j : ℚ) * m (ν + k • pR j)) :
    ∀ v, m v = (Submission.E8Cert.Mnu i v : ℚ) := by
  have h := eq_of_freudenthal (lam := ord40get i) (Submission.E8Star.ord40_dom i)
    ha (Submission.E8ConstChar.MnuQ_top i) hb (fun v hv => Submission.E8ConstChar.MnuQ_support i hv)
    hc (Submission.E8ConstChar.MnuQ_dc i) hd
    (fun ν hν _ hcon => Submission.E8ConstChar.MnuQ_freud i hν hcon)
  intro v
  have := h v
  simpa [Submission.E8ConstChar.MnuQ] using this

/-! ## The Kostant partition function

`KostantP γ` is the number of ways of writing `γ` as a sum of the `120` positive roots `pR j` with
multiplicities.  It is the coefficient of `e^γ` in `∏_{α>0}(1-e^{-α})^{-1}`, hence (after the shift
by `ρ`) the coefficient of `e^γ` in `1/A_ρ = e^{-ρ}∏_{α>0}(1-e^{-α})^{-1}`, and it is the weight
multiplicity `dim M(ν)_{ν+γ}` of the Verma module.  Only `KostantP` (not the module) is needed to
state the multiplicities of the Kostant candidate `S_x = Σ_w ε(w)·chM(w·x)`; the construction below
uses the "free commutative monoid" form (a multiplicity function `Fin 120 → ℕ`), bounded by the
height. -/

lemma htOf_sum' {ι : Type*} (s : Finset ι) (g : ι → Fin 8 → ℤ) :
    htOf (∑ i ∈ s, g i) = ∑ i ∈ s, htOf (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [htOf_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, htOf_add, ih]

/-- The finite set of multiplicity functions all of whose entries are at most `N`. -/
def multFinset (N : ℕ) : Finset (Fin 120 → ℕ) :=
  Fintype.piFinset (fun _ : Fin 120 => Finset.range (N + 1))

lemma mem_multFinset {N : ℕ} {f : Fin 120 → ℕ} :
    f ∈ multFinset N ↔ ∀ j, f j ≤ N := by
  simp only [multFinset, Fintype.mem_piFinset, Finset.mem_range]
  exact ⟨fun h j => Nat.lt_succ_iff.mp (h j), fun h j => Nat.lt_succ_iff.mpr (h j)⟩

/-- **The Kostant partition function**: the number of multisets of positive roots summing to `γ`. -/
noncomputable def KostantP (γ : Fin 8 → ℤ) : ℕ :=
  ((multFinset (htOf γ).toNat).filter
    (fun f => ∑ j, (f j : ℤ) • pR j = γ)).card

/-- Every multiplicity function summing to `γ` has total height `htOf γ`. -/
lemma KostantP_eq_height {γ : Fin 8 → ℤ} (f : Fin 120 → ℕ)
    (hf : ∑ j, (f j : ℤ) • pR j = γ) :
    ∑ j, (f j : ℤ) * htOf (pR j) = htOf γ := by
  rw [← hf, htOf_sum']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [htOf_smul_int]

/-- **`KostantP 0 = 1`**: only the empty multiset sums to `0`. -/
theorem KostantP_zero : KostantP (0 : Fin 8 → ℤ) = 1 := by
  classical
  have hff : (fun _ : Fin 120 => 0) ∈ multFinset (htOf (0 : Fin 8 → ℤ)).toNat := by
    rw [mem_multFinset]; intro j; simp
  have hfilter : (multFinset (htOf (0 : Fin 8 → ℤ)).toNat).filter
      (fun f => ∑ j, (f j : ℤ) • pR j = 0) = {(fun _ : Fin 120 => 0)} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
    · simp only [Finset.mem_filter]
      exact ⟨hff, by simp⟩
    · intro f hf
      simp only [Finset.mem_filter] at hf
      funext j
      by_contra hj
      have hpos : 0 < f j := Nat.pos_of_ne_zero hj
      have hsum : (f j : ℤ) * htOf (pR j) ≤ ∑ i, (f i : ℤ) * htOf (pR i) :=
        Finset.single_le_sum (f := fun i => (f i : ℤ) * htOf (pR i))
          (fun i _ => mul_nonneg (Nat.cast_nonneg _) (le_of_lt (htOf_pR_pos i)))
          (Finset.mem_univ j)
      have h1 := KostantP_eq_height f hf.2
      rw [h1, htOf_zero] at hsum
      have h2 : (1 : ℤ) ≤ (f j : ℤ) * htOf (pR j) := by
        have h3 := htOf_pR j
        nlinarith [hpos]
      omega
  rw [KostantP, hfilter, Finset.card_singleton]

/-- A finite sum of cone elements is a cone element. -/
lemma posCon_sum {ι : Type*} (s : Finset ι) (g : ι → Fin 8 → ℤ)
    (h : ∀ i ∈ s, posCon (g i)) : posCon (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using posCon_zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact posCon_add (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **The support of the Kostant partition function**: nothing outside the positive cone. -/
theorem KostantP_eq_zero_of_not_posCon (γ : Fin 8 → ℤ) (h : ¬ posCon γ) : KostantP γ = 0 := by
  classical
  rw [KostantP, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro f _ hf
  exact h (by
    rw [← hf]
    refine posCon_sum _ _ fun j _ => ?_
    exact posCon_smul_nonneg (Int.natCast_nonneg _) (posCon_pR j))

/-- `KostantP` is monotone for the cone order: a cone element has no larger support. -/
theorem KostantP_eq_zero_of_not_conj {γ δ : Fin 8 → ℤ} (h : ¬ posCon (γ - δ)) :
    KostantP (γ - δ) = 0 :=
  KostantP_eq_zero_of_not_posCon _ h

end Submission.E8Kostant
