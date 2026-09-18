import Submission.DS.Structure
import Submission.DS.Reduce
import Submission.DS.Summability
import Submission.DS.Measure
set_option maxRecDepth 10000
set_option maxRecDepth 10000

open scoped Nat ENNReal NNReal
open Set
open DuffinSchaefferConjecture

/-!
# Catlin's reduction: 𝒦 ψ is contained in the reduced-fraction limsup up to rationals

We prove: under the convergence hypothesis, every `α ∈ 𝒦 ψ` lies either in the set of
points belonging to infinitely many of the reduced-fraction sets `Cq (rho ψ) q`, or is
rational.  Here `Cq ρ q` consists of points within `ρ q` of a reduced fraction `a/q`
(with `a ≤ q`).
-/

namespace Submission.DS

/-- The set of points within `ρ q` of some reduced fraction with denominator `q`. -/
def Cq (ρ : ℕ+ → ℝ≥0) (q : ℕ+) : Set ℝ :=
  {x | ∃ a : ℕ, a ≤ (q : ℕ) ∧ Nat.Coprime a (q : ℕ) ∧
    |x - (a : ℝ) / (q : ℝ)| ≤ (ρ q : ℝ)}


/-- The solution set of `x` (pairs, not reduced). -/
def SolSet (ψ : ℕ+ → ℝ≥0) (x : ℝ) : Set (ℕ × ℕ+) :=
  {(a, q) | (a : ℕ) ≤ ((q : ℕ+) : ℕ) ∧ inequality_1_7 ψ x a q}

/-- Reduction of a pair to lowest terms. -/
def redPair (a : ℕ) (q : ℕ+) : ℕ × ℕ+ := (numRed a q, denRed a q)
/-- The image of the solution set under reduction to lowest terms. -/
def redImg (ψ : ℕ+ → ℝ≥0) (x : ℝ) : Set (ℕ × ℕ+) :=
  {(a', q') | ∃ (a : ℕ) (q : ℕ+), a ≤ (q : ℕ) ∧ inequality_1_7 ψ x a q ∧
    redPair a q = (a', q')}

/-- Every reduced solution pair has numerator `≤` denominator and coprime. -/
lemma mem_redImg_coprime_le (ψ : ℕ+ → ℝ≥0) (x : ℝ) {a' : ℕ} {q' : ℕ+}
    (h : (a', q') ∈ redImg ψ x) : Nat.Coprime a' (q' : ℕ) ∧ a' ≤ (q' : ℕ) := by
  rcases h with ⟨a, q, hleq, _hineq, hred⟩
  cases hred
  exact ⟨numRed_coprime_denRed a q, numRed_le_denRed a q hleq⟩

/-- A reduced solution pair: `|x - a'/q'| ≤ rho q'`. -/
lemma reduced_value_bound (ψ : ℕ+ → ℝ≥0) (hψ : Conv ψ) (x : ℝ) {a' : ℕ} {q' : ℕ+}
    (h : (a', q') ∈ redImg ψ x) :
    |x - (a' : ℝ) / (q' : ℝ)| ≤ (rho ψ q' : ℝ) := by
  rcases h with ⟨a, q, hleq, hineq, hred⟩
  cases hred
  have hb1 : |x - (a : ℝ) / (q : ℝ)| ≤ ((ψ q / q : ℝ≥0) : ℝ) := hineq
  rw [← reduced_value_eq a q] at hb1
  have hle : (ψ q / q : ℝ≥0) ≤ rho ψ (denRed a q) :=
    self_le_rho_of_dvd hψ (denRed a q) q (denRed_dvd_pnat a q)
  exact hb1.trans (by exact_mod_cast hle)

/-- Reduced solution pairs give points of the reduced-fraction sets. -/
lemma mem_Cq_of_mem_redImg (ψ : ℕ+ → ℝ≥0) (hψ : Conv ψ) (x : ℝ) {a' : ℕ} {q' : ℕ+}
    (h : (a', q') ∈ redImg ψ x) : x ∈ Cq (rho ψ) q' := by
  rcases mem_redImg_coprime_le ψ x h with ⟨hc, hle⟩
  exact ⟨a', hle, hc, reduced_value_bound ψ hψ x h⟩

/-- Numerators of reduced pairs are bounded by their denominator. -/
lemma redImg_fib_finite (ψ : ℕ+ → ℝ≥0) (x : ℝ) (q' : ℕ+) :
    ({a' : ℕ | (a', q') ∈ redImg ψ x}).Finite := by
  have hsub : {a' : ℕ | (a', q') ∈ redImg ψ x} ⊆ Set.Icc 0 (q' : ℕ) := by
    intro a' ha'
    exact ⟨Nat.zero_le a', (mem_redImg_coprime_le ψ x ha').2⟩
  exact (Set.finite_Icc 0 (q' : ℕ)).subset hsub

/-- If infinitely many reduced pairs occur, then `x` is in the reduced limsup. -/
lemma limsup_of_redImg_infinite (ψ : ℕ+ → ℝ≥0) (hψ : Conv ψ) (x : ℝ)
    (h : (redImg ψ x).Infinite) : x ∈ limsupDenoms (Cq (rho ψ)) := by
  let sol : ℕ+ → Set ℕ := fun q' => {a' | (a', q') ∈ redImg ψ x}
  have hfin : ∀ q', (sol q').Finite := fun q' => by
    simpa [sol] using redImg_fib_finite ψ x q'
  have hPair : pairSet sol = redImg ψ x := by
    ext p
    simp [pairSet, sol]
  have hDen : (denomSet sol).Infinite := by
    exact (infinite_pairs_iff_infinite_denoms sol hfin).1 (by simpa [hPair] using h)
  unfold limsupDenoms
  refine Set.Infinite.mono ?h hDen
  intro q' hq'
  rcases hq' with ⟨a', ha'⟩
  exact mem_Cq_of_mem_redImg ψ hψ x ha'


/-- Infinite sets of pairs with bounded numerators have infinitely many denominators. -/
lemma denom_infinite_of_pair_infinite {F : Set (ℕ × ℕ+)}
    (hb : ∀ {a q}, (a, q) ∈ F → a ≤ (q : ℕ)) (hF : F.Infinite) :
    ({q : ℕ+ | ∃ a : ℕ, (a, q) ∈ F}).Infinite := by
  let fib : ℕ+ → Set ℕ := fun q => {a | (a, q) ∈ F}
  have hfib : ∀ q, (fib q).Finite := by
    intro q
    have hsub : fib q ⊆ Set.Icc 0 (q : ℕ) := by
      intro a ha
      exact ⟨Nat.zero_le a, hb ha⟩
    exact (Set.finite_Icc 0 (q : ℕ)).subset hsub
  have hP : pairSet fib = F := by
    ext p
    simp [pairSet, fib]
  exact (infinite_pairs_iff_infinite_denoms fib hfib).1 (by simpa [hP] using hF)

/-- If `x` has infinitely many solutions but only finitely many reduced pairs, then `x` is
rational. -/
lemma rational_of_redImg_finite (ψ : ℕ+ → ℝ≥0) (hψ : Conv ψ) (x : ℝ)
    (hx : x ∈ 𝒦 ψ) (h : ¬ (redImg ψ x).Infinite) : x ∈ ratSet := by
  classical
  by_contra hxRat
  have hRedF : (redImg ψ x).Finite := by
    exact (not_not.mp h)
  have hSol : (SolSet ψ x).Infinite := by
    change ({(p : ℕ × ℕ+) | (p.1 : ℕ) ≤ ((p.2 : ℕ+) : ℕ) ∧ inequality_1_7 ψ x p.1 p.2}).Infinite
    exact hx.2
  let red : ℕ × ℕ+ → ℕ × ℕ+ := fun p => redPair p.1 p.2
  have hRedImg_eq : redImg ψ x = red '' SolSet ψ x := by
    ext p
    constructor
    · intro hp
      rcases hp with ⟨a, q, hle, hineq, hred⟩
      exact ⟨(a, q), by simpa [SolSet] using ⟨hle, hineq⟩, hred⟩
    · rintro ⟨s, hs, hps⟩
      rcases s with ⟨a, q⟩
      have hmem : a ≤ (q : ℕ) ∧ inequality_1_7 ψ x a q := by simpa [SolSet] using hs
      exact ⟨a, q, hmem.1, hmem.2, hps⟩
  have hSolSub : SolSet ψ x ⊆ ⋃ p ∈ redImg ψ x, {s | s ∈ SolSet ψ x ∧ red s = p} := by
    intro s hs
    have hp : red s ∈ redImg ψ x := by
      rw [hRedImg_eq]
      exact ⟨s, hs, rfl⟩
    exact mem_iUnion₂.mpr ⟨red s, hp, hs, rfl⟩
  by_cases hall : ∀ p ∈ redImg ψ x, ({s | s ∈ SolSet ψ x ∧ red s = p}).Finite
  · have hSolFin : (SolSet ψ x).Finite := by
      refine (hRedF.biUnion (fun p hp => hall p hp)).subset ?_
      exact hSolSub
    exact hSol hSolFin
  · push_neg at hall
    rcases hall with ⟨p0, hp0, hfiber⟩
    rcases p0 with ⟨a', q'⟩
    have hne : x ≠ (a' : ℝ) / (q' : ℝ) := by
      intro hxeq
      apply hxRat
      refine ⟨(a' : ℚ) / (q' : ℚ), ?_⟩
      norm_num [hxeq]
    let δ : ℝ := |x - (a' : ℝ) / (q' : ℝ)|
    have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hne)
    let F : Set (ℕ × ℕ+) := {s | s ∈ SolSet ψ x ∧ red s = (a', q')}
    have hFinF : F.Infinite := by simpa [F] using hfiber
    have hbF : ∀ {a q}, (a, q) ∈ F → a ≤ (q : ℕ) := by
      intro a q hF
      have hm : a ≤ (q : ℕ) ∧ inequality_1_7 ψ x a q := by simpa [F, SolSet] using hF.1
      exact hm.1
    have hFD : ({q : ℕ+ | ∃ a : ℕ, (a, q) ∈ F}).Infinite :=
      denom_infinite_of_pair_infinite hbF hFinF
    have hGfin : ({q : ℕ+ | δ ≤ ((ψ q / q : ℝ≥0) : ℝ)}).Finite :=
      finite_above_self hψ δ hδ
    have hFDsub : ({q : ℕ+ | ∃ a : ℕ, (a, q) ∈ F}) ⊆ {q : ℕ+ | δ ≤ ((ψ q / q : ℝ≥0) : ℝ)} := by
      intro q hq
      rcases hq with ⟨a, hF⟩
      have hs : (a, q) ∈ SolSet ψ x := hF.1
      have hmem : a ≤ (q : ℕ) ∧ inequality_1_7 ψ x a q := by simpa [SolSet] using hs
      have hb1 : |x - (a : ℝ) / (q : ℝ)| ≤ ((ψ q / q : ℝ≥0) : ℝ) := hmem.2
      have hrv := reduced_value_eq a q
      rw [← hrv] at hb1
      have hpair : redPair a q = (a', q') := by simpa [red] using hF.2
      have hnum : numRed a q = a' := congrArg Prod.fst hpair
      have hden : denRed a q = q' := congrArg Prod.snd hpair
      have hb2 : |x - (a' : ℝ) / (q' : ℝ)| ≤ ((ψ q / q : ℝ≥0) : ℝ) := by
        simpa [hnum, hden] using hb1
      have hbδ : δ ≤ ((ψ q / q : ℝ≥0) : ℝ) := by simpa [δ] using hb2
      exact hbδ
    exact hFD (hGfin.subset hFDsub)

/-- **Catlin reduction**: `𝒦 ψ ⊆ (reduced limsup) ∪ ℚ`. -/
lemma K_subset_limsupC_union_rat (ψ : ℕ+ → ℝ≥0) (hψ : Conv ψ) :
    𝒦 ψ ⊆ limsupDenoms (Cq (rho ψ)) ∪ ratSet := by
  intro x hx
  by_cases hr : (redImg ψ x).Infinite
  · exact Or.inl (limsup_of_redImg_infinite ψ hψ x hr)
  · exact Or.inr (rational_of_redImg_finite ψ hψ x hx hr)

end Submission.DS
