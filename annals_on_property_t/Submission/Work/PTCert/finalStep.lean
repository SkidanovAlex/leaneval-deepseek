import Mathlib
import Submission.Work.PTCert.Glue3
import Submission.Work.PTCert.gramSOS
import Submission.Work.PTCert.residualAbsorption
import Submission.Work.PTCert.sigmaGroupFacts

/-!
# `finalStep` — the last glue step of the property (T) certificate

Given the two mathematical hypotheses `OrbitKeys` (row-orbit decomposition of the Gram
form of `Pmat pv`) and `LabelIdentity` (exact class sums + residual symmetry), and the data
fact `ClassSem` (canonical class words have length `4` and letters `< 81`), the `FinalStep`
of the certificate chain holds: a positive semidefinite `Pmat pv`, exact class sums and the
absorbed residual give `IsSOS T` for `T = targetSum q Dq + c • Δ₅`.

The proof is the composition described in `finalStep.lean`'s original docstring:
* the element `Z = (1/SCv) • gramForm fE (Pmat pv) + (c • Δ₅ + residualSum res (SCv·Dq))`
  is a sum of hermitian squares: `gramSOS` for the PSD Gram matrix (scaled by the
  nonnegative `1/SCv`, `IsSOS.smul`), and `residualAbsorption 5` for the bracket;
* `conjAvg Sg` is linear (`conjAvg_add`, `conjAvg_sub`, `conjAvg_smul`), `OrbitKeys`
  replaces `conjAvg (gramForm …)` by the key sum, and `LabelIdentity` says the corrected
  key sum vanishes; hence `conjAvg Sg Z = conjAvg Sg (targetSum q Dq + c • Δ₅) = conjAvg Sg T`;
* `avgPrinciple` with the `Sg`-invariance of `T` concludes.
-/

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G
open Submission.RouteB
open scoped BigOperators

/-- `conjAvg` is additive in its second argument. -/
lemma conjAvg_add {G : Type} [Group G] (Sg : Finset G) (x y : MonoidAlgebra ℝ G) :
    conjAvg Sg (x + y) = conjAvg Sg x + conjAvg Sg y := by
  unfold conjAvg
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun s _ => by rw [mul_add, add_mul])

/-- `conjAvg` is `ℝ`-homogeneous in its second argument. -/
lemma conjAvg_smul {G : Type} [Group G] (Sg : Finset G) (r : ℝ) (x : MonoidAlgebra ℝ G) :
    conjAvg Sg (r • x) = r • conjAvg Sg x := by
  unfold conjAvg
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun s _ => by rw [mul_smul_comm, smul_mul_assoc])

/-- `conjAvg` commutes with negation. -/
lemma conjAvg_neg {G : Type} [Group G] (Sg : Finset G) (x : MonoidAlgebra ℝ G) :
    conjAvg Sg (-x) = -conjAvg Sg x := by
  unfold conjAvg
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun s _ => by rw [mul_neg, neg_mul])

/-- `conjAvg` commutes with subtraction. -/
lemma conjAvg_sub {G : Type} [Group G] (Sg : Finset G) (x y : MonoidAlgebra ℝ G) :
    conjAvg Sg (x - y) = conjAvg Sg x - conjAvg Sg y := by
  rw [sub_eq_add_neg, conjAvg_add, conjAvg_neg, sub_eq_add_neg]

/-- Conjugating a hermitian square by `of s` again gives a hermitian square. -/
theorem conj_of_star_mul_self {G : Type} [Group G] (s : G) (y : MonoidAlgebra ℝ G) :
    MonoidAlgebra.of ℝ G s * (star y * y) * MonoidAlgebra.of ℝ G s⁻¹
      = star (y * MonoidAlgebra.of ℝ G s⁻¹) * (y * MonoidAlgebra.of ℝ G s⁻¹) := by
  rw [star_mul, Submission.Helpers.star_of, inv_inv]
  simp only [mul_assoc]

/-- Conjugation by a group element sends sums of hermitian squares to sums of hermitian
squares. -/
theorem isSOS_conj_of {G : Type} [Group G] [DecidableEq G] (s : G) {x : MonoidAlgebra ℝ G}
    (hx : IsSOS x) : IsSOS (MonoidAlgebra.of ℝ G s * x * MonoidAlgebra.of ℝ G s⁻¹) := by
  obtain ⟨ξ, hξ⟩ := hx
  have h : MonoidAlgebra.of ℝ G s * x * MonoidAlgebra.of ℝ G s⁻¹
      = ∑ y ∈ ξ, star (y * MonoidAlgebra.of ℝ G s⁻¹) * (y * MonoidAlgebra.of ℝ G s⁻¹) := by
    rw [hξ, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun y _ => conj_of_star_mul_self s y)
  rw [h]
  exact IsSOS.finset_sum ξ (fun y _ => isSOS_star_mul_self (y * MonoidAlgebra.of ℝ G s⁻¹))

/-- **(P1) Averaging principle** (local copy of `Work.PTCert.avgPrinciple`; the module
`Submission.Work.PTCert.avgPrinciple` is not importable together with
`Submission.Work.PTCert.residualAbsorption` because both define `isSOS_star_mul_self`). -/
theorem avgPrincipleLocal : AvgPrinciple := by
  unfold AvgPrinciple
  intro G _ _ Sg hSg T Z hT hZ hAvg
  have hTA : conjAvg Sg T = (Sg.card : ℝ) • T := by
    rw [conjAvg]
    rw [Finset.sum_congr rfl (fun s hs => hT s hs)]
    rw [Finset.sum_const, Nat.cast_smul_eq_nsmul ℝ]
  have hSOSavg : IsSOS (conjAvg Sg Z) := by
    unfold conjAvg
    exact IsSOS.finset_sum Sg (fun s hs => isSOS_conj_of s hZ)
  have hcard : 0 < Sg.card := Finset.card_pos.mpr ⟨1, hSg.1⟩
  have hcardR : (0 : ℝ) < (Sg.card : ℝ) := by exact_mod_cast hcard
  have hne : (Sg.card : ℝ) ≠ 0 := ne_of_gt hcardR
  have hTeq : T = (1 / (Sg.card : ℝ)) • conjAvg Sg Z := by
    rw [hAvg, hTA, smul_smul,
      show (1 / (Sg.card : ℝ)) * (Sg.card : ℝ) = 1 by rw [one_div, inv_mul_cancel₀ hne]]
    exact (one_smul ℝ T).symm
  rw [hTeq]
  exact IsSOS.smul (div_nonneg (by norm_num) (le_of_lt hcardR)) hSOSavg

theorem finalStep (hOK : OrbitKeys) (hLI : LabelIdentity) (hC : ClassSem) : FinalStep := by
  intro pv q res Dq SCv T c hDq hSCv hPSD hcls hresinv hressum habs hTinv hTeq
  have hOK' := hOK pv
  have hLI' := hLI pv q res Dq SCv hDq hSCv hcls hresinv
  set K : MonoidAlgebra ℝ G5 := ∑ r ∈ Finset.range 18, ∑ g ∈ Finset.range (ngE r),
      ((multE (keyOf r g) : ℝ) * (pv (keyOf r g) : ℝ)) • MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r g)) with hK
  set Ct : MonoidAlgebra ℝ G5 := targetSum q Dq with hCt
  set R : MonoidAlgebra ℝ G5 := residualSum res ((SCv : ℝ) * (Dq : ℝ)) with hR
  set A : MonoidAlgebra ℝ G5 := gramForm fE (Pmat pv) with hA
  set Dl : MonoidAlgebra ℝ G5 := Edge.deltaSub 5 5 with hDl
  -- positivity of the denominator
  have hSCvR : (0 : ℝ) < (SCv : ℝ) := by exact_mod_cast hSCv
  have hDqR : (0 : ℝ) < (Dq : ℝ) := by exact_mod_cast hDq
  have hdenpos : (0 : ℝ) < (SCv : ℝ) * (Dq : ℝ) := mul_pos hSCvR hDqR
  -- (2) the vanishing of the corrected key sum
  have hkey : (1 / (SCv : ℝ)) • conjAvg Sg K + conjAvg Sg R = conjAvg Sg Ct := by
    have h := hLI'
    rw [conjAvg_add, conjAvg_sub, conjAvg_smul] at h
    have h2 : (1 / (SCv : ℝ)) • conjAvg Sg K + conjAvg Sg R - conjAvg Sg Ct = 0 := by
      rw [← h]; abel
    exact sub_eq_zero.mp h2
  -- (1) `Z` is a sum of hermitian squares
  have hSOSA : IsSOS ((1 / (SCv : ℝ)) • A) := by
    rw [hA]
    exact IsSOS.smul (le_of_lt (div_pos one_pos hSCvR)) (gramSOS G5 fE (Pmat pv) hPSD)
  have hSOSres : IsSOS (c • Dl + R) := by
    rw [hDl, hR]
    unfold residualSum
    refine residualAbsorption 5 (I := Finset.range ncls) (ks := canonW)
      (w := fun cl => (res cl : ℝ) / ((SCv : ℝ) * (Dq : ℝ))) (c := c) ?_ ?_ ?_
    · intro t ht
      have htlt : t < ncls := Finset.mem_range.mp ht
      obtain ⟨hlen, hlt81⟩ := hC.1 t htlt
      have hNB : NB1 5 = 81 := by norm_num [NB1]
      refine ⟨?_, ?_⟩
      · omega
      · intro k hk
        rw [hNB]
        exact hlt81 k hk
    · rw [← Finset.sum_div, ← Int.cast_sum, hressum, Int.cast_zero, zero_div]
    · have habs' : 16 * ∑ t ∈ Finset.range ncls, |(res t : ℝ)|
          ≤ c * ((SCv : ℝ) * (Dq : ℝ)) := by
        nlinarith [habs]
      have hterm : ∀ t, |(res t : ℝ) / ((SCv : ℝ) * (Dq : ℝ))|
          = |(res t : ℝ)| / ((SCv : ℝ) * (Dq : ℝ)) := by
        intro t; rw [abs_div, abs_of_pos hdenpos]
      rw [show (∑ t ∈ Finset.range ncls, |(res t : ℝ) / ((SCv : ℝ) * (Dq : ℝ))|)
            = ∑ t ∈ Finset.range ncls, |(res t : ℝ)| / ((SCv : ℝ) * (Dq : ℝ)) from
          Finset.sum_congr rfl (fun t _ => hterm t)]
      rw [← Finset.sum_div, ← mul_div_assoc, div_le_iff₀ hdenpos]
      exact habs'
  have hSOSW : IsSOS ((1 / (SCv : ℝ)) • A + (c • Dl + R)) := hSOSA.add hSOSres
  -- (2) the conjugation averages agree
  have hstep1 : conjAvg Sg ((1 / (SCv : ℝ)) • A + (c • Dl + R))
      = c • conjAvg Sg Dl + ((1 / (SCv : ℝ)) • conjAvg Sg K + conjAvg Sg R) := by
    rw [conjAvg_add, conjAvg_add, conjAvg_smul, conjAvg_smul, hOK']
    abel
  have hZavg : conjAvg Sg ((1 / (SCv : ℝ)) • A + (c • Dl + R)) = conjAvg Sg T := by
    rw [hstep1, hTeq, conjAvg_add, conjAvg_smul, hkey]
    abel
  -- (3) the averaging principle
  exact avgPrincipleLocal G5 Sg (sigmaGroupFacts 5).1 T ((1 / (SCv : ℝ)) • A + (c • Dl + R))
    hTinv hSOSW hZavg

end Work.PTCert
