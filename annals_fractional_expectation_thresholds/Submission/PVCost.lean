import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.Prob
import Submission.PVCore
import Submission.PVAPI

open ProbabilityTheory MeasureTheory unitInterval Set
open scoped ENNReal NNReal BigOperators unitInterval ProbabilityTheory
open FractionalExpectationThresholds
open Submission.PVC
open Submission.PVAPI

attribute [local instance] Classical.propDecidable

namespace Submission
namespace PVCost

universe u
variable {X : Type u} [Fintype X]

/-- Bernoulli `p` probability mass under parameter `p`. -/
noncomputable def bmass (p : ℝ) (W : Set X) : ℝ :=
  (p : ℝ) ^ W.ncard * (1 - p) ^ (Fintype.card X - W.ncard)

/-! ## Elementary analytic facts -/

/-- `(1-q)^L·(1+Lq) ≤ 1` for `0 ≤ q ≤ 1`. -/
lemma one_minus_pow_mul_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : ∀ L : ℕ,
    (1 - q) ^ L * (1 + L * q) ≤ 1 := by
  intro L
  induction L with
  | zero => norm_num
  | succ L ih =>
    have hnonneg : 0 ≤ (1 - q) ^ L := pow_nonneg (by linarith) L
    have hqsq : 0 ≤ (q : ℝ) ^ 2 := sq_nonneg q
    have hL1 : 0 ≤ ((L : ℝ) + 1) := by positivity
    have hA : 0 ≤ 1 - (1 - q) ^ L * (1 + L * q) := sub_nonneg.mpr ih
    have hB : 0 ≤ (1 - q) ^ L * (q ^ 2 * (L + 1)) := by
      exact mul_nonneg hnonneg (mul_nonneg hqsq hL1)
    have hnon : 0 ≤ (1 - (1 - q) ^ L * (1 + L * q)) + (1 - q) ^ L * (q ^ 2 * (L + 1)) := by
      nlinarith
    have hXeq : (1 - q) ^ (L + 1) * (1 + (L + 1) * q) =
        1 - ((1 - (1 - q) ^ L * (1 + L * q)) + (1 - q) ^ L * (q ^ 2 * (L + 1))) := by
      ring
    have hcast : 1 + (L + 1 : ℕ) * q = 1 + ((L : ℝ) + 1) * q := by
      push_cast
      ring
    rw [hcast]
    rw [hXeq]
    linarith [hnon]

/-- `L·q·(1-q)^L ≤ 1 - (1-q)^L` for `0 ≤ q ≤ 1`. -/
lemma mul_pow_sub_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (L : ℕ) :
    L * q * (1 - q) ^ L ≤ 1 - (1 - q) ^ L := by
  have h := one_minus_pow_mul_le hq0 hq1 L
  nlinarith

/-! ## Facts about the Bernoulli parameter `p` and the ratio `δ` -/

/-- `p = 1 - (1-q0)^L` is positive when `0 < q0 ≤ 1` and `1 ≤ L`. -/
lemma p_pos {q0 : ℝ} (hq0 : 0 < q0) (hq1 : q0 ≤ 1) {L : ℕ} (hL : 1 ≤ L) :
    0 < 1 - (1 - q0) ^ L := by
  have h1 : 0 ≤ 1 - q0 := by linarith
  have h2 : 1 - q0 < 1 := by linarith
  have hpow : (1 - q0) ^ L < 1 := pow_lt_one₀ h1 h2 (by omega)
  linarith

/-- `p = 1 - (1-q0)^L` is at most 1. -/
lemma p_le_one {q0 : ℝ} (hq1 : q0 ≤ 1) (L : ℕ) : 1 - (1 - q0) ^ L ≤ 1 := by
  have h : 0 ≤ (1 - q0) ^ L := pow_nonneg (by linarith) L
  linarith

/-- the complement of `p` is `(1-q0)^L`. -/
lemma one_sub_p {q0 : ℝ} (L : ℕ) : 1 - (1 - (1 - q0) ^ L) = (1 - q0) ^ L := by ring

/-- the mass ratio `δ = q0·(1-q0)^L/p`. -/
noncomputable def delta (q0 : ℝ) (L : ℕ) : ℝ :=
  q0 * (1 - q0) ^ L / (1 - (1 - q0) ^ L)

/-- `δ ≥ 0`. -/
lemma delta_nonneg {q0 : ℝ} (hq0 : 0 ≤ q0) (hq1 : q0 ≤ 1) {L : ℕ} (hL : 1 ≤ L) :
    0 ≤ delta q0 L := by
  by_cases hz : q0 = 0
  · simp [delta, hz]
  · have hq0pos : 0 < q0 := lt_of_le_of_ne hq0 (fun h => hz h.symm)
    unfold delta
    have hp : 0 < 1 - (1 - q0) ^ L := p_pos hq0pos hq1 hL
    exact div_nonneg (mul_nonneg (le_of_lt hq0pos) (pow_nonneg (by linarith) L)) (le_of_lt hp)

/-- `δ ≤ 1/L`. -/
lemma delta_le_invL {q0 : ℝ} (hq0 : 0 < q0) (hq1 : q0 ≤ 1) {L : ℕ} (hL : 1 ≤ L) :
    delta q0 L ≤ (1 : ℝ) / L := by
  have hp : 0 < 1 - (1 - q0) ^ L := p_pos hq0 hq1 hL
  have hc : (L : ℝ) * q0 * (1 - q0) ^ L ≤ 1 - (1 - q0) ^ L :=
    mul_pow_sub_le (le_of_lt hq0) hq1 L
  have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
  unfold delta
  field_simp [hp.ne', hLne]
  nlinarith

/-! ## The mass product identity -/

/-- expanding `bmass` at `Z \ T` after multiplying by `q0^|T|·p^|T|`. -/
lemma bmass_mul_pow {p q0 : ℝ} {Z T : Set X} (hT : T ⊆ Z) :
    bmass p (Z \ T) * q0 ^ T.ncard * p ^ T.ncard = bmass p Z * (q0 * (1 - p)) ^ T.ncard := by
  classical
  have hcard : (Z \ T).ncard + T.ncard = Z.ncard :=
    Set.ncard_sdiff_add_ncard_of_subset hT (by simpa using (Z.toFinite))
  have hcard2 : Fintype.card X - (Z \ T).ncard = (Fintype.card X - Z.ncard) + T.ncard := by
    have hZn : Z.ncard ≤ Fintype.card X := by
      simpa using (Set.ncard_le_ncard (s := Z) (t := (Set.univ : Set X)) (by intro x hx; simp) (by simp))
    omega
  calc
    bmass p (Z \ T) * q0 ^ T.ncard * p ^ T.ncard
        = p ^ (Z \ T).ncard * p ^ T.ncard * q0 ^ T.ncard * (1 - p) ^ (Fintype.card X - (Z \ T).ncard) := by
          unfold bmass
          ring
    _ = p ^ ((Z \ T).ncard + T.ncard) * q0 ^ T.ncard * (1 - p) ^ (Fintype.card X - (Z \ T).ncard) := by
          rw [← pow_add]
    _ = p ^ Z.ncard * q0 ^ T.ncard * (1 - p) ^ ((Fintype.card X - Z.ncard) + T.ncard) := by
          rw [hcard]
          rw [hcard2]
    _ = p ^ Z.ncard * (1 - p) ^ (Fintype.card X - Z.ncard) * ((1 - p) ^ T.ncard * q0 ^ T.ncard) := by
          rw [pow_add]
          ring
    _ = p ^ Z.ncard * (1 - p) ^ (Fintype.card X - Z.ncard) * (q0 * (1 - p)) ^ T.ncard := by
          rw [← mul_pow]
          ring
    _ = bmass p Z * (q0 * (1 - p)) ^ T.ncard := by
          unfold bmass
          ring

/-- `bmass (Z\T)·q0^|T| = bmass Z·δ^|T|` for `T ⊆ Z`. -/
lemma bmass_sdiff_delta {q0 : ℝ} {L : ℕ} {Z T : Set X} (hT : T ⊆ Z)
    (hp : 1 - (1 - q0) ^ L ≠ 0) :
    bmass (1 - (1 - q0) ^ L) (Z \ T) * q0 ^ T.ncard
      = bmass (1 - (1 - q0) ^ L) Z * delta q0 L ^ T.ncard := by
  classical
  let p : ℝ := 1 - (1 - q0) ^ L
  have hmain := bmass_mul_pow (p := p) (q0 := q0) (Z := Z) (T := T) hT
  have hpT : p ^ T.ncard ≠ 0 := pow_ne_zero _ hp
  have hdelta : (q0 * (1 - p)) / p = delta q0 L := by
    unfold delta
    have h1p : 1 - p = (1 - q0) ^ L := by
      dsimp [p]
      ring
    rw [h1p]
  calc
    bmass p (Z \ T) * q0 ^ T.ncard
        = (bmass p (Z \ T) * q0 ^ T.ncard * p ^ T.ncard) / p ^ T.ncard := by
          field_simp [hpT]
    _ = (bmass p Z * (q0 * (1 - p)) ^ T.ncard) / p ^ T.ncard := by
          rw [hmain]
    _ = bmass p Z * (((q0 * (1 - p)) ^ T.ncard) / p ^ T.ncard) := by
          field_simp [hpT]
    _ = bmass p Z * ((q0 * (1 - p)) / p) ^ T.ncard := by
          rw [div_pow]
    _ = bmass p Z * delta q0 L ^ T.ncard := by
          rw [hdelta]
    _ = bmass (1 - (1 - q0) ^ L) Z * delta q0 L ^ T.ncard := by
          rfl

/-! ## Counting subsets by cardinality -/

open Finset

/-- summing an indicator over a fintype gives the cardinality (as a real). -/
lemma indicator_sum_ncard {α : Type*} [Fintype α] (A : Set α) :
    (∑ x : α, if x ∈ A then (1 : ℝ) else 0) = (A.ncard : ℝ) := by
  classical
  have hf : A.toFinset = (Finset.univ : Finset α).filter (fun x => x ∈ A) := by
    ext x
    by_cases hx : x ∈ A <;> simp [hx]
  calc
    (∑ x : α, if x ∈ A then (1 : ℝ) else 0)
        = ((Finset.univ : Finset α).filter (fun x => x ∈ A)).card := by
          rw [← Finset.sum_filter]
          simp
    _ = (A.ncard : ℝ) := by
          rw [← hf]
          rw [Set.ncard_eq_toFinset_card]
          simp

/-- the number of subsets of `s` with `ncard = j` is `s.ncard.choose j`. -/
lemma subset_slice_count (s : Set X) (j : ℕ) :
    (∑ T : Set X, if T ⊆ s ∧ T.ncard = j then (1 : ℝ) else 0) = (s.ncard.choose j : ℝ) := by
  classical
  have hsFin : s.Finite := s.toFinite
  have hf : {T : Set X | T ⊆ s ∧ T.ncard = j}.toFinset =
      (Finset.univ : Finset (Set X)).filter (fun T => T ⊆ s ∧ T.ncard = j) := by
    ext T
    by_cases h : T ⊆ s ∧ T.ncard = j <;> simp [h]
  calc
    (∑ T : Set X, if T ⊆ s ∧ T.ncard = j then (1 : ℝ) else 0)
        = ((Finset.univ : Finset (Set X)).filter (fun T => T ⊆ s ∧ T.ncard = j)).card := by
          rw [← Finset.sum_filter]
          simp
    _ = ({T : Set X | T ⊆ s ∧ T.ncard = j}.ncard : ℝ) := by
          rw [← hf]
          rw [Set.ncard_eq_toFinset_card]
          simp
    _ = (s.ncard.choose j : ℝ) := by
          rw [Set.ncard_powerset_ncard hsFin j]

/-- indicator sum over an interval. -/
lemma Icc_indicator_sum {m ℓ t : ℕ} (d : ℝ) :
    (∑ j ∈ Finset.Icc m ℓ, if t = j then d ^ j else 0)
      = (if m ≤ t ∧ t ≤ ℓ then d ^ t else 0) := by
  classical
  rw [Finset.sum_ite_eq (s := Finset.Icc m ℓ) (a := t) (b := fun j => d ^ j)]
  by_cases hmem : t ∈ Finset.Icc m ℓ
  · have ht : m ≤ t ∧ t ≤ ℓ := Finset.mem_Icc.mp hmem
    simp [hmem, ht]
  · have ht : ¬ (m ≤ t ∧ t ≤ ℓ) := by
      intro hh
      exact hmem (Finset.mem_Icc.mpr hh)
    simp [hmem, ht]

/-- For fixed `T ⊆ s` with `|T| ≤ ℓ`, the inner sum slices. -/
private lemma inner_slice_value {s : Set X} {m ℓ : ℕ} (d : ℝ) (T : Set X)
    (hsub : T ⊆ s) (hℓT : T.ncard ≤ ℓ) :
    (∑ j ∈ Finset.Icc m ℓ, if T ⊆ s ∧ T.ncard = j then d ^ j else 0)
      = (if m ≤ T.ncard then d ^ T.ncard else 0) := by
  classical
  have hrew : (∑ j ∈ Finset.Icc m ℓ, if T ⊆ s ∧ T.ncard = j then d ^ j else 0)
      = (∑ j ∈ Finset.Icc m ℓ, if T.ncard = j then d ^ j else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : T.ncard = j <;> simp [h, hsub]
  rw [hrew]
  have hind := Icc_indicator_sum (m := m) (ℓ := ℓ) (t := T.ncard) d
  rw [hind]
  by_cases hm : m ≤ T.ncard
  · simp [hm, hℓT]
  · simp [hm]

/-- slicing a subset sum by cardinality. -/
lemma subset_sum_eq {s : Set X} {m ℓ : ℕ} (haℓ : s.ncard ≤ ℓ) (d : ℝ) :
    (∑ T : Set X, if T ⊆ s ∧ m ≤ T.ncard then d ^ T.ncard else 0)
      = (∑ j ∈ Finset.Icc m ℓ, ((s.ncard.choose j : ℝ) * d ^ j)) := by
  classical
  calc
    (∑ T : Set X, if T ⊆ s ∧ m ≤ T.ncard then d ^ T.ncard else 0)
        = (∑ T ∈ (Finset.univ : Finset (Set X)), ∑ j ∈ Finset.Icc m ℓ,
            if T ⊆ s ∧ T.ncard = j then d ^ j else 0) := by
          apply Finset.sum_congr rfl
          intro T hT
          by_cases hsub : T ⊆ s
          · have hℓT : T.ncard ≤ ℓ := by
              have hle : T.ncard ≤ s.ncard := Set.ncard_le_ncard hsub (by simpa using s.toFinite)
              omega
            rw [inner_slice_value (s := s) (m := m) (ℓ := ℓ) d T hsub hℓT]
            simp [hsub]
          · have hL0 : (if T ⊆ s ∧ m ≤ T.ncard then d ^ T.ncard else 0) = 0 := by
              simp [hsub]
            have hz : (∑ j ∈ Finset.Icc m ℓ, if T ⊆ s ∧ T.ncard = j then d ^ j else 0) = 0 := by
              apply Finset.sum_eq_zero
              intro j hj
              simp [hsub]
            rw [hL0, hz]
    _ = (∑ j ∈ Finset.Icc m ℓ, ∑ T ∈ (Finset.univ : Finset (Set X)),
            if T ⊆ s ∧ T.ncard = j then d ^ j else 0) := by
          rw [Finset.sum_comm]
    _ = (∑ j ∈ Finset.Icc m ℓ, ((s.ncard.choose j : ℝ) * d ^ j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hcount := subset_slice_count s j
          calc
            (∑ T : Set X, if T ⊆ s ∧ T.ncard = j then d ^ j else 0)
                = (∑ T : Set X, d ^ j * (if T ⊆ s ∧ T.ncard = j then (1 : ℝ) else 0)) := by
                  apply Finset.sum_congr rfl
                  intro T hT
                  by_cases h : T ⊆ s ∧ T.ncard = j <;> simp [h]
            _ = d ^ j * (∑ T : Set X, if T ⊆ s ∧ T.ncard = j then (1 : ℝ) else 0) := by
                  rw [Finset.mul_sum]
            _ = d ^ j * (s.ncard.choose j : ℝ) := by rw [hcount]
            _ = (s.ncard.choose j : ℝ) * d ^ j := by ring

/-- replacing `a.choose` by `ℓ.choose` in a nonnegative sum. -/
lemma choose_sum_le {a ℓ : ℕ} (haℓ : a ≤ ℓ) {m : ℕ} {d : ℝ} (hd0 : 0 ≤ d) :
    (∑ j ∈ Finset.Icc m ℓ, (a.choose j : ℝ) * d ^ j) ≤
    (∑ j ∈ Finset.Icc m ℓ, (ℓ.choose j : ℝ) * d ^ j) := by
  apply Finset.sum_le_sum
  intro j hj
  have hle : a.choose j ≤ ℓ.choose j := Nat.choose_le_choose j haℓ
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (pow_nonneg hd0 j)

/-- the full subset bound used in the per-`Z` estimate. -/
lemma subset_pow_sum_le {s : Set X} {m ℓ : ℕ} (haℓ : s.ncard ≤ ℓ) {d : ℝ} (hd0 : 0 ≤ d) :
    (∑ T : Set X, if T ⊆ s ∧ m ≤ T.ncard then d ^ T.ncard else 0) ≤
    (∑ j ∈ Finset.Icc m ℓ, (ℓ.choose j : ℝ) * d ^ j) := by
  rw [subset_sum_eq (s := s) haℓ d]
  exact choose_sum_le haℓ hd0

/-! ## Fragments: the inner per-`Z` estimates -/

/-- a fragment is disjoint from `W`. -/
lemma frag_disjoint {H : Set (Set X)} {W T : Set X} (hT : T ∈ Frag H W) : Disjoint T W := by
  rcases (mem_Frag.mp hT) with ⟨S, hS, hT'⟩
  rw [hT']
  exact Set.disjoint_sdiff_left

/-- membership in large fragments forces `T ∩ W = ∅`. -/
lemma Lm_disjoint {H : Set (Set X)} {W T : Set X} {m : ℕ} (hT : T ∈ Lm H W m) :
    Disjoint T W := frag_disjoint hT.1.1

/-- if `T ∈ Lm H (Z\T) m` and `T ⊆ Z` then `Z ∈ Up H`. -/
lemma Up_of_Lm {H : Set (Set X)} {Z T : Set X} {m : ℕ} (hTZ : T ⊆ Z)
    (hT : T ∈ Lm H (Z \ T) m) : Z ∈ Up H := by
  classical
  rcases (mem_Frag.mp hT.1.1) with ⟨S, hS, hT'⟩
  refine (mem_Up.mpr ⟨S, hS, ?_⟩)
  -- S ⊆ Z
  have hS : S ⊆ T ∪ (Z \ T) := by
    intro x hx
    by_cases hx1 : x ∈ Z \ T
    · exact Or.inr hx1
    · have hx2 : x ∈ S \ (Z \ T) := ⟨hx, hx1⟩
      rw [← hT'] at hx2
      exact Or.inl hx2
  have hTZ2 : T ∪ (Z \ T) ⊆ Z := by
    intro x hx
    rcases hx with hxT | hxZT
    · exact hTZ hxT
    · exact hxZT.1
  exact subset_trans hS hTZ2

/-- a minimal fragment contained in a member of `H` must be inside any chosen member. -/
lemma Lm_subset_choose {H : Set (Set X)} {Z T : Set X} {m : ℕ}
    (hZ : ∃ S ∈ H, S ⊆ Z) (hTZ : T ⊆ Z) (hT : T ∈ Lm H (Z \ T) m) :
    T ⊆ Classical.choose hZ := by
  classical
  let TZ : Set X := Classical.choose hZ
  have hTZ₁ : TZ ∈ H := (Classical.choose_spec hZ).1
  have hTZ₂ : TZ ⊆ Z := (Classical.choose_spec hZ).2
  have hF : IsMinFrag H (Z \ T) T := hT.1
  have hGfrag : TZ ∩ T ∈ Frag H (Z \ T) := by
    rw [mem_Frag]
    refine ⟨TZ, hTZ₁, ?_⟩
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxTZ, hxT⟩
      exact ⟨hxTZ, by
        intro hxZT
        exact hxZT.2 hxT⟩
    · intro hx
      rcases hx with ⟨hxTZ, hxnot⟩
      exact ⟨hxTZ, by
        by_contra hxT
        apply hxnot
        exact ⟨hTZ₂ hxTZ, hxT⟩⟩
  have hGsub : TZ ∩ T ⊆ T := Set.inter_subset_right
  have hGT : TZ ∩ T = T := hF.2 (TZ ∩ T) hGfrag hGsub
  intro x hx
  have hx' : x ∈ TZ ∩ T := by
    rw [hGT]
    exact hx
  exact hx'.1

/-- inner sum over `Z` is zero outside `Up H`. -/
lemma innerSum_zero {H : Set (Set X)} {Z : Set X} {m : ℕ} {δ : ℝ}
    (hZ : Z ∉ Up H) :
    (∑ T : Set X, if T ⊆ Z ∧ T ∈ Lm H (Z \ T) m then δ ^ T.ncard else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro T hT
  have hnot : ¬ (T ⊆ Z ∧ T ∈ Lm H (Z \ T) m) := by
    intro hh
    exact hZ (Up_of_Lm hh.1 hh.2)
  simp [hnot]

/-- `(1/L) ≥ 0`. -/
lemma invL_nonneg {L : ℕ} (hL : 1 ≤ L) : 0 ≤ (1 : ℝ) / L := by
  have hLz : (0 : ℝ) < L := by exact_mod_cast hL
  exact div_nonneg (by norm_num) (le_of_lt hLz)

/-- the inner sum bound for `Z ∈ Up H`. -/
lemma innerSum_le {H : Set (Set X)} {ℓ m : ℕ} (hℓb : Bounded H ℓ) {Z : Set X}
    (hZ : Z ∈ Up H) {δ : ℝ} (hδ0 : 0 ≤ δ) {L : ℕ} (hL : 1 ≤ L)
    (hδ1 : δ ≤ (1 : ℝ) / L) :
    (∑ T : Set X, if T ⊆ Z ∧ T ∈ Lm H (Z \ T) m then δ ^ T.ncard else 0) ≤
      (∑ j ∈ Finset.Icc m ℓ, ((ℓ.choose j : ℝ) * (1 / L : ℝ) ^ j)) := by
  classical
  have hZ' : ∃ S ∈ H, S ⊆ Z := mem_Up.mp hZ
  let TZ : Set X := Classical.choose hZ'
  have hTZ₁ : TZ ∈ H := (Classical.choose_spec hZ').1
  have hTZ₂ : TZ ⊆ Z := (Classical.choose_spec hZ').2
  have hTZcard : TZ.ncard ≤ ℓ := hℓb TZ hTZ₁
  have hL0 : 0 ≤ (1 : ℝ) / L := invL_nonneg hL
  calc
    (∑ T : Set X, if T ⊆ Z ∧ T ∈ Lm H (Z \ T) m then δ ^ T.ncard else 0)
        ≤ (∑ T : Set X, if T ⊆ TZ ∧ m ≤ T.ncard then δ ^ T.ncard else 0) := by
          apply Finset.sum_le_sum
          intro T hT
          by_cases h : T ⊆ Z ∧ T ∈ Lm H (Z \ T) m
          · have hTsub : T ⊆ TZ := by
              exact Lm_subset_choose (Z := Z) hZ' h.1 h.2
            have hmT : m ≤ T.ncard := h.2.2
            have hTZc : T.ncard ≤ TZ.ncard := by
              simpa using (Set.ncard_le_ncard hTsub (by simpa using (TZ.toFinite)))
            simp [h, hTsub, hmT]
          · have hz : (if T ⊆ Z ∧ T ∈ Lm H (Z \ T) m then δ ^ T.ncard else 0) = 0 := by
              simp [h]
            rw [hz]
            by_cases h2 : T ⊆ TZ ∧ m ≤ T.ncard
            · simp [h2, pow_nonneg hδ0]
            · simp [h2]
    _ ≤ (∑ T : Set X, if T ⊆ TZ ∧ m ≤ T.ncard then (1 / L : ℝ) ^ T.ncard else 0) := by
          apply Finset.sum_le_sum
          intro T hT
          by_cases h : T ⊆ TZ ∧ m ≤ T.ncard
          · have hR : (if T ⊆ TZ ∧ m ≤ T.ncard then (1 / L : ℝ) ^ T.ncard else 0) = (1 / L : ℝ) ^ T.ncard := by
              simp [h]
            rw [hR]
            simpa [h] using pow_le_pow_left₀ hδ0 hδ1 T.ncard
          · have hL : (if T ⊆ TZ ∧ m ≤ T.ncard then δ ^ T.ncard else 0) = 0 := by
              simp [h]
            rw [hL]
            simp [h]
    _ ≤ (∑ j ∈ Finset.Icc m ℓ, ((ℓ.choose j : ℝ) * (1 / L : ℝ) ^ j)) := by
          exact subset_pow_sum_le (s := TZ) hTZcard (d := (1 / L : ℝ)) hL0

/-! ## The double-counting reindex -/

/-- for disjoint `s, t`, `(s ∪ t) \ t = s`. -/
lemma union_sdiff_of_disjoint {s t : Set X} (hd : Disjoint s t) : (s ∪ t) \ t = s := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hx12, hxT⟩
    simp at hx12
    rcases hx12 with hx1 | hx2
    · exact hx1
    · exact (hxT hx2).elim
  · intro hx
    constructor
    · exact Or.inl hx
    · intro hxT
      exact (Set.disjoint_left.mp hd) hx hxT

/-- the reindexing of a disjoint-pair sum into a subset-pair sum. -/
lemma pair_reindex (g : Set X → Set X → ℝ) :
    (∑ W : Set X, ∑ T : Set X, if Disjoint W T then g W T else 0)
    = (∑ Z : Set X, ∑ T : Set X, if T ⊆ Z then g (Z \ T) T else 0) := by
  classical
  calc
    (∑ W : Set X, ∑ T : Set X, if Disjoint W T then g W T else 0)
        = (∑ T : Set X, ∑ W : Set X, if Disjoint W T then g W T else 0) := by
          rw [Finset.sum_comm]
    _ = (∑ T : Set X, ∑ Z : Set X, if T ⊆ Z then g (Z \ T) T else 0) := by
          apply Finset.sum_congr rfl
          intro T hT
          have hperT : (∑ W : Set X, if Disjoint W T then g W T else 0)
                     = (∑ Z : Set X, if T ⊆ Z then g (Z \ T) T else 0) := by
            calc
              (∑ W : Set X, if Disjoint W T then g W T else 0)
                  = (∑ W ∈ (Finset.univ : Finset (Set X)).filter (fun W => Disjoint W T), g W T) := by
                    rw [← Finset.sum_filter]
              _ = (∑ Z ∈ (Finset.univ : Finset (Set X)).filter (fun Z => T ⊆ Z), g (Z \ T) T) := by
                    refine Finset.sum_bij
                      (s := (Finset.univ : Finset (Set X)).filter (fun W => Disjoint W T))
                      (t := (Finset.univ : Finset (Set X)).filter (fun Z => T ⊆ Z))
                      (i := fun (W : Set X) (_ : W ∈ (Finset.univ : Finset (Set X)).filter (fun W => Disjoint W T)) => W ∪ T)
                      ?hi ?inj ?surj ?hval
                    · intro W hW
                      have hdisj : Disjoint W T := (Finset.mem_filter.mp hW).2
                      rw [Finset.mem_filter]
                      exact ⟨by simp, by intro x hx; exact Or.inr hx⟩
                    · intro W₁ hW₁ W₂ hW₂ h
                      have hd1 : Disjoint W₁ T := (Finset.mem_filter.mp hW₁).2
                      have hd2 : Disjoint W₂ T := (Finset.mem_filter.mp hW₂).2
                      have h' := congrArg (fun s : Set X => s \ T) h
                      have h1 : (W₁ ∪ T) \ T = W₁ := union_sdiff_of_disjoint hd1
                      have h2 : (W₂ ∪ T) \ T = W₂ := union_sdiff_of_disjoint hd2
                      rw [h1, h2] at h'
                      exact h'
                    · intro Z hZ
                      have hTZ : T ⊆ Z := (Finset.mem_filter.mp hZ).2
                      refine ⟨Z \ T, ?mem, ?eq⟩
                      · rw [Finset.mem_filter]
                        exact ⟨by simp, Set.disjoint_sdiff_left⟩
                      · simpa using (Set.sdiff_union_of_subset (s := Z) (t := T) hTZ)
                    · intro W hW
                      have hdisj : Disjoint W T := (Finset.mem_filter.mp hW).2
                      have hc : (W ∪ T) \ T = W := union_sdiff_of_disjoint hdisj
                      rw [hc]
              _ = (∑ Z : Set X, if T ⊆ Z then g (Z \ T) T else 0) := by
                    rw [Finset.sum_filter]
          exact hperT
    _ = (∑ Z : Set X, ∑ T : Set X, if T ⊆ Z then g (Z \ T) T else 0) := by
          rw [Finset.sum_comm]
/-- The q-cost lemma. -/
theorem pvCostLemma {H : Set (Set X)} {ℓ : ℕ} (hℓb : Bounded H ℓ)
    {q0 : ℝ} (hq0 : 0 < q0) (hq1 : q0 ≤ 1) (L : ℕ) (hL : 1 ≤ L)
    {m : ℕ} (hm1 : 1 ≤ m) (hmℓ : m ≤ ℓ) :
    let p := 1 - (1 - q0) ^ L
    (∑ W : Set X, bmass p W * ccost q0 (Lm H W m)) ≤
      (∑ W : Set X, bmass p W * (if W ∈ Up H then 1 else 0)) *
      (∑ j ∈ Finset.Icc m ℓ, ((ℓ.choose j : ℝ) * (1 / L) ^ j)) := by
  classical
  let p : ℝ := 1 - (1 - q0) ^ L
  change (∑ W : Set X, bmass p W * ccost q0 (Lm H W m)) ≤
      (∑ W : Set X, bmass p W * (if W ∈ Up H then 1 else 0)) *
      (∑ j ∈ Finset.Icc m ℓ, ((ℓ.choose j : ℝ) * (1 / L : ℝ) ^ j))
  let C : ℝ := ∑ j ∈ Finset.Icc m ℓ, ((ℓ.choose j : ℝ) * (1 / L : ℝ) ^ j)
  have hq00 : 0 ≤ q0 := le_of_lt hq0
  have hp : 0 < p := by
    dsimp [p]
    exact p_pos hq0 hq1 hL
  have hpne : p ≠ 0 := ne_of_gt hp
  have hp0' : 0 ≤ p := le_of_lt hp
  have hple : p ≤ 1 := by
    dsimp [p]
    exact p_le_one hq1 L
  have h1mp : 0 ≤ 1 - p := sub_nonneg.mpr hple
  have hδ0 : 0 ≤ delta q0 L := delta_nonneg hq00 hq1 hL
  have hδ1 : delta q0 L ≤ (1 : ℝ) / L := delta_le_invL hq0 hq1 hL
  have hL0 : 0 ≤ (1 : ℝ) / L := invL_nonneg hL
  have hbm : ∀ W : Set X, 0 ≤ bmass p W := by
    intro W
    unfold bmass
    exact mul_nonneg (pow_nonneg hp0' _) (pow_nonneg h1mp _)
  let innerSum : Set X → ℝ := fun Z =>
    (∑ T : Set X, if T ⊆ Z ∧ T ∈ Lm H (Z \ T) m then delta q0 L ^ T.ncard else 0)
  have hccost : ∀ W : Set X, ccost q0 (Lm H W m) ≤ ecost q0 (Lm H W m) := by
    intro W
    exact ccost_le_ecost (covers_self (Lm H W m))
  -- step 1: replace ccost by ecost
  have hstep1 :
      (∑ W : Set X, bmass p W * ccost q0 (Lm H W m)) ≤
      (∑ W : Set X, bmass p W * ecost q0 (Lm H W m)) := by
    apply Finset.sum_le_sum
    intro W hW
    exact mul_le_mul_of_nonneg_left (hccost W) (hbm W)
  -- step 2: expand ecost
  have hS1 :
      (∑ W : Set X, bmass p W * ecost q0 (Lm H W m))
        = (∑ W : Set X, ∑ T : Set X,
            if T ∈ Lm H W m then bmass p W * q0 ^ T.ncard else 0) := by
    calc
      (∑ W : Set X, bmass p W * ecost q0 (Lm H W m))
          = (∑ W : Set X, bmass p W * (∑ T : Set X,
              if T ∈ Lm H W m then q0 ^ T.ncard else 0)) := by
                rfl
      _ = (∑ W : Set X, ∑ T : Set X,
              bmass p W * (if T ∈ Lm H W m then q0 ^ T.ncard else 0)) := by
                apply Finset.sum_congr rfl
                intro W hW
                rw [Finset.mul_sum]
      _ = (∑ W : Set X, ∑ T : Set X,
              if T ∈ Lm H W m then bmass p W * q0 ^ T.ncard else 0) := by
                apply Finset.sum_congr rfl
                intro W hW
                apply Finset.sum_congr rfl
                intro T hT
                by_cases h : T ∈ Lm H W m <;> simp [h]
  -- step 3: cut to disjoint pairs
  have hS2 :
      (∑ W : Set X, ∑ T : Set X, if T ∈ Lm H W m then bmass p W * q0 ^ T.ncard else 0)
        = (∑ W : Set X, ∑ T : Set X,
            if Disjoint W T then (if T ∈ Lm H W m then bmass p W * q0 ^ T.ncard else 0) else 0) := by
    apply Finset.sum_congr rfl
    intro W hW
    apply Finset.sum_congr rfl
    intro T hT
    by_cases h : T ∈ Lm H W m
    · have hdisj' : Disjoint W T := (Lm_disjoint h).symm
      simp [h, hdisj']
    · simp [h]
  -- step 4: reindex to (Z, T) with T ⊆ Z
  have hS3 :
      (∑ W : Set X, ∑ T : Set X,
        if Disjoint W T then (if T ∈ Lm H W m then bmass p W * q0 ^ T.ncard else 0) else 0)
        = (∑ Z : Set X, ∑ T : Set X,
            if T ⊆ Z ∧ T ∈ Lm H (Z \ T) m then bmass p (Z \ T) * q0 ^ T.ncard else 0) := by
    calc
      (∑ W : Set X, ∑ T : Set X,
        if Disjoint W T then (if T ∈ Lm H W m then bmass p W * q0 ^ T.ncard else 0) else 0)
          = (∑ Z : Set X, ∑ T : Set X,
              if T ⊆ Z then (if T ∈ Lm H (Z \ T) m then bmass p (Z \ T) * q0 ^ T.ncard else 0) else 0) := by
                exact pair_reindex (fun W T => if T ∈ Lm H W m then bmass p W * q0 ^ T.ncard else 0)
      _ = (∑ Z : Set X, ∑ T : Set X,
            if T ⊆ Z ∧ T ∈ Lm H (Z \ T) m then bmass p (Z \ T) * q0 ^ T.ncard else 0) := by
                apply Finset.sum_congr rfl
                intro Z hZ
                apply Finset.sum_congr rfl
                intro T hT
                by_cases h1 : T ⊆ Z
                · by_cases h2 : T ∈ Lm H (Z \ T) m <;> simp [h1, h2]
                · simp [h1]
  -- step 5: factor the mass identity
  have hS4 :
      (∑ Z : Set X, ∑ T : Set X,
            if T ⊆ Z ∧ T ∈ Lm H (Z \ T) m then bmass p (Z \ T) * q0 ^ T.ncard else 0)
        = (∑ Z : Set X, bmass p Z * innerSum Z) := by
    apply Finset.sum_congr rfl
    intro Z hZ
    calc
      (∑ T : Set X, if T ⊆ Z ∧ T ∈ Lm H (Z \ T) m then bmass p (Z \ T) * q0 ^ T.ncard else 0)
          = (∑ T : Set X, bmass p Z * (if T ⊆ Z ∧ T ∈ Lm H (Z \ T) m then delta q0 L ^ T.ncard else 0)) := by
                apply Finset.sum_congr rfl
                intro T hT
                by_cases h : T ⊆ Z ∧ T ∈ Lm H (Z \ T) m
                · have hEq : bmass p (Z \ T) * q0 ^ T.ncard = bmass p Z * delta q0 L ^ T.ncard := by
                    have hEq' := bmass_sdiff_delta (Z := Z) (T := T) h.1 hpne
                    simpa [p] using hEq'
                  simp [h, hEq]
                · simp [h]
      _ = bmass p Z * (∑ T : Set X, if T ⊆ Z ∧ T ∈ Lm H (Z \ T) m then delta q0 L ^ T.ncard else 0) := by
                rw [Finset.mul_sum]

  -- step 6: pointwise bound via the per-`Z` estimate
  have hC0 : 0 ≤ C := by
    dsimp [C]
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (by exact_mod_cast Nat.zero_le _) (pow_nonneg hL0 j)
  have hinnerZ : ∀ Z : Set X, bmass p Z * innerSum Z ≤ bmass p Z * (if Z ∈ Up H then C else 0) := by
    intro Z
    by_cases hZ : Z ∈ Up H
    · have hb := innerSum_le (H := H) (ℓ := ℓ) (m := m) hℓb hZ (δ := delta q0 L) hδ0 (L := L) hL hδ1
      have hle : innerSum Z ≤ C := by
        simpa [innerSum, C] using hb
      have hif : (if Z ∈ Up H then C else 0) = C := if_pos hZ
      rw [hif]
      exact mul_le_mul_of_nonneg_left hle (hbm Z)
    · have hz : innerSum Z = 0 := by
        simpa [innerSum] using (innerSum_zero (H := H) (Z := Z) (δ := delta q0 L) hZ)
      have hif : (if Z ∈ Up H then C else 0) = 0 := if_neg hZ
      rw [hz, hif]
  have hstep2 : (∑ Z : Set X, bmass p Z * innerSum Z) ≤
      (∑ Z : Set X, bmass p Z * (if Z ∈ Up H then C else 0)) := by
    apply Finset.sum_le_sum
    intro Z hZ
    exact hinnerZ Z
  have hstep3 :
      (∑ Z : Set X, bmass p Z * (if Z ∈ Up H then C else 0))
        = C * (∑ Z : Set X, bmass p Z * (if Z ∈ Up H then 1 else 0)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Z hZ
    by_cases h : Z ∈ Up H
    · simp [h]
      ring
    · simp [h]
  -- assemble
  calc
    (∑ W : Set X, bmass p W * ccost q0 (Lm H W m))
        ≤ (∑ W : Set X, bmass p W * ecost q0 (Lm H W m)) := hstep1
    _ = (∑ W : Set X, ∑ T : Set X,
            if T ∈ Lm H W m then bmass p W * q0 ^ T.ncard else 0) := hS1
    _ = (∑ W : Set X, ∑ T : Set X,
            if Disjoint W T then (if T ∈ Lm H W m then bmass p W * q0 ^ T.ncard else 0) else 0) := hS2
    _ = (∑ Z : Set X, ∑ T : Set X,
            if T ⊆ Z ∧ T ∈ Lm H (Z \ T) m then bmass p (Z \ T) * q0 ^ T.ncard else 0) := hS3
    _ = (∑ Z : Set X, bmass p Z * innerSum Z) := hS4
    _ ≤ (∑ Z : Set X, bmass p Z * (if Z ∈ Up H then C else 0)) := hstep2
    _ = C * (∑ Z : Set X, bmass p Z * (if Z ∈ Up H then 1 else 0)) := hstep3
    _ = (∑ Z : Set X, bmass p Z * (if Z ∈ Up H then 1 else 0)) * C := by ring
    _ = (∑ W : Set X, bmass p W * (if W ∈ Up H then 1 else 0)) *
        (∑ j ∈ Finset.Icc m ℓ, ((ℓ.choose j : ℝ) * (1 / L : ℝ) ^ j)) := by
          rfl
