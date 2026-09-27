import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.H0_structure

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/EQ/DESIGN.md, DESIGN_CORE.md and PAPER_PROOFS.md (the lead's full paper proofs for the sketched Rychlik steps; follow them). Defs: Submission/Work/EQ/Defs.lean + DefsCore.lean (namespace Work.EQ; do NOT edit; IsPuncturedChart now carries a scale κ). Proved UNIFORMIZATION library in this workspace (Submission.UnifMain etc.). With UnifMain imported write `open _root_.Topology`.

# exists_regular_of_family: analytic family ⇒ regular component (2–4k; READY as stated)

**Proof.** `PAPER_PROOFS.md` §0 (F1, F2) and §3. Rychlik's residue argument is **not** needed.
1. F1: in rectangular coordinates, `RegPair(P,Q) ⇔ EqRelC(P,Q) ∧ P ≠ O₂ ∧ Q ≠ O₁`. (If `v ≠ 0` is
   isotropic, no unit `e ∥ v` exists.)
2. F2: an entry that is identically `O₂` (resp. `O₁`) forces all earlier (resp. later) entries to be
   constant. That makes the unstable (resp. stable) tail constant, contradicting `u`, `v = c/u`
   nonconstant. So the non-regular set is a discrete zero set.
3. At a regular `z₀` with `u'(z₀) ≠ 0`, invert `u` to get a `ψ₁`-section, hence a point of `H0`.
   `ψ ≡ c` on an open set, so on the whole component (identity theorem in `ψ₁`-charts,
   `H0_structure`).
-/

namespace Work.EQ

open Complex Filter _root_.Topology
open scoped Topology

lemma eqLam_pos_aux {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < eqLam a := by
  rw [eqLam]; exact div_pos (by linarith) (by linarith)

lemma eqLam_lt_one_aux {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : eqLam a < 1 := by
  rw [eqLam, div_lt_one (by linarith)]; linarith

/-! ## Part 1: coordinates, the relation, and the two singular points -/

/-- `O₁ = (-a/2, 0)`: the unstable fixed point of the equichordal half-map. -/
noncomputable def ptO1 (a : ℝ) : ℂ × ℂ := (((-(a / 2) : ℝ) : ℂ), 0)

/-- `O₂ = (a/2, 0)`: the stable fixed point of the equichordal half-map. -/
noncomputable def ptO2 (a : ℝ) : ℂ × ℂ := (((a / 2 : ℝ) : ℂ), 0)

lemma ptO1_ne_ptO2 {a : ℝ} (ha : a ≠ 0) : ptO1 a ≠ ptO2 a := by
  intro h
  have h1 : ((-(a / 2) : ℝ) : ℂ) = ((a / 2 : ℝ) : ℂ) := congrArg Prod.fst h
  have h2 : -(a / 2) = a / 2 := Complex.ofReal_injective h1
  exact ha (by linarith)

/-- A complex number `d` whose square is the negative of a square is one of the two isotropic
directions. -/
lemma iso_sq {d y : ℂ} (h : d ^ 2 + y ^ 2 = 0) : d = Complex.I * y ∨ d = -(Complex.I * y) := by
  have hI : (Complex.I * y) ^ 2 = -y ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
  have h2 : d ^ 2 = (Complex.I * y) ^ 2 := by rw [hI]; linear_combination h
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h2

/-- The relation `EqRelC` is symmetric in the following form: if `e = P + Q` is a unit vector
parallel to `P - O₂`, then it is also parallel to `Q - O₁`. -/
lemma eqRelC_par {a : ℝ} {P Q : ℂ × ℂ} (h : EqRelC a P Q) :
    (Q.1 + P.1) * Q.2 = (Q.2 + P.2) * (Q.1 + ((a / 2 : ℝ) : ℂ)) := by
  obtain ⟨h1, h2⟩ := h
  linear_combination -h2

/-- **F1, first half.** If `(P - O₂)² ` vanishes with the complex bilinear square, then `P = O₂`. -/
lemma eqRelC_fst_ne {a : ℝ} {P Q : ℂ × ℂ} (h : EqRelC a P Q)
    (hd : (P.1 - ((a / 2 : ℝ) : ℂ)) ^ 2 + P.2 ^ 2 = 0) : P = ptO2 a := by
  obtain ⟨h1, h2⟩ := h
  rcases iso_sq hd with hI | hI
  · have hkey : P.2 * (Q.1 + P.1 - Complex.I * (Q.2 + P.2)) = 0 := by
      linear_combination h2 + (Q.2 + P.2) * hI
    rcases mul_eq_zero.mp hkey with hy | hq
    · have hx : P.1 = ((a / 2 : ℝ) : ℂ) := by linear_combination hI + Complex.I * hy
      rw [show ptO2 a = (((a / 2 : ℝ) : ℂ), 0) from rfl]; exact Prod.ext hx hy
    · have hz : (Q.1 + P.1) ^ 2 + (Q.2 + P.2) ^ 2 = 0 := by
        rw [show Q.1 + P.1 = Complex.I * (Q.2 + P.2) by linear_combination hq]
        ring_nf; rw [Complex.I_sq]; ring
      rw [hz] at h1; exact absurd h1 zero_ne_one
  · have hkey : P.2 * (Q.1 + P.1 + Complex.I * (Q.2 + P.2)) = 0 := by
      linear_combination h2 + (Q.2 + P.2) * hI
    rcases mul_eq_zero.mp hkey with hy | hq
    · have hx : P.1 = ((a / 2 : ℝ) : ℂ) := by linear_combination hI - Complex.I * hy
      rw [show ptO2 a = (((a / 2 : ℝ) : ℂ), 0) from rfl]; exact Prod.ext hx hy
    · have hz : (Q.1 + P.1) ^ 2 + (Q.2 + P.2) ^ 2 = 0 := by
        rw [show Q.1 + P.1 = -(Complex.I * (Q.2 + P.2)) by linear_combination hq]
        ring_nf; rw [Complex.I_sq]; ring
      rw [hz] at h1; exact absurd h1 zero_ne_one

/-- **F1, second half.** If `(Q - O₁)² ` vanishes with the complex bilinear square, then `Q = O₁`. -/
lemma eqRelC_snd_ne {a : ℝ} {P Q : ℂ × ℂ} (h : EqRelC a P Q)
    (hd : (Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2 = 0) : Q = ptO1 a := by
  have hpar := eqRelC_par h
  obtain ⟨h1, h2⟩ := h
  rcases iso_sq hd with hI | hI
  · have hkey : Q.2 * (Q.1 + P.1 - Complex.I * (Q.2 + P.2)) = 0 := by
      linear_combination hpar + (Q.2 + P.2) * hI
    rcases mul_eq_zero.mp hkey with hy | hq
    · have hx : Q.1 = ((-(a / 2) : ℝ) : ℂ) := by
        have h1' : ((-(a / 2) : ℝ) : ℂ) = -((a / 2 : ℝ) : ℂ) := by push_cast; ring
        rw [h1']; linear_combination hI + Complex.I * hy
      rw [show ptO1 a = (((-(a / 2) : ℝ) : ℂ), 0) from rfl]; exact Prod.ext hx hy
    · have hz : (Q.1 + P.1) ^ 2 + (Q.2 + P.2) ^ 2 = 0 := by
        rw [show Q.1 + P.1 = Complex.I * (Q.2 + P.2) by linear_combination hq]
        ring_nf; rw [Complex.I_sq]; ring
      rw [hz] at h1; exact absurd h1 zero_ne_one
  · have hkey : Q.2 * (Q.1 + P.1 + Complex.I * (Q.2 + P.2)) = 0 := by
      linear_combination hpar + (Q.2 + P.2) * hI
    rcases mul_eq_zero.mp hkey with hy | hq
    · have hx : Q.1 = ((-(a / 2) : ℝ) : ℂ) := by
        have h1' : ((-(a / 2) : ℝ) : ℂ) = -((a / 2 : ℝ) : ℂ) := by push_cast; ring
        rw [h1']; linear_combination hI - Complex.I * hy
      rw [show ptO1 a = (((-(a / 2) : ℝ) : ℂ), 0) from rfl]; exact Prod.ext hx hy
    · have hz : (Q.1 + P.1) ^ 2 + (Q.2 + P.2) ^ 2 = 0 := by
        rw [show Q.1 + P.1 = -(Complex.I * (Q.2 + P.2)) by linear_combination hq]
        ring_nf; rw [Complex.I_sq]; ring
      rw [hz] at h1; exact absurd h1 zero_ne_one

/-- **F1.** A pair of the equichordal relation is regular exactly when it avoids `O₂` (as first
point) and `O₁` (as second point). -/
lemma regPair_iff {a : ℝ} {P Q : ℂ × ℂ} :
    RegPair a P Q ↔ EqRelC a P Q ∧ P ≠ ptO2 a ∧ Q ≠ ptO1 a := by
  constructor
  · rintro ⟨hE, hP, hQ⟩
    refine ⟨hE, ?_, ?_⟩
    · intro hc; exact hP (by rw [hc]; simp [ptO2])
    · intro hc; exact hQ (by rw [hc]; simp [ptO1])
  · rintro ⟨hE, hP, hQ⟩
    refine ⟨hE, ?_, ?_⟩
    · intro hd; exact hP (eqRelC_fst_ne hE hd)
    · intro hd; exact hQ (eqRelC_snd_ne hE hd)

/-- Consecutive points of the relation, on the real axis: the successor is one of the two
reflected values. -/
lemma eqRelC_succ_axis {a : ℝ} {x : ℝ} {Q : ℂ × ℂ}
    (h : EqRelC a (((x : ℝ) : ℂ), 0) Q) (hx : x ≠ a / 2) :
    Q = (((1 - x : ℝ) : ℂ), 0) ∨ Q = (((-1 - x : ℝ) : ℂ), 0) := by
  obtain ⟨h1, h2⟩ := h
  have hxc : ((x : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ) ≠ 0 := by
    intro hc
    refine hx ?_
    have h1' : x - a / 2 = 0 := by
      have := congrArg Complex.re hc
      simpa using this
    linarith
  have hy : Q.2 = 0 := by
    have hq : Q.2 * (((x : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)) = 0 := by linear_combination -h2
    exact (mul_eq_zero.mp hq).resolve_right hxc
  have hx1 : (Q.1 + ((x : ℝ) : ℂ)) ^ 2 = 1 := by linear_combination h1 - hy * Q.2
  rcases sq_eq_one_iff.mp hx1 with hq | hq
  · left; refine Prod.ext ?_ hy; push_cast; linear_combination hq
  · right; refine Prod.ext ?_ hy; push_cast; linear_combination hq

/-- Consecutive points of the relation, on the real axis: the predecessor is one of the two
reflected values. -/
lemma eqRelC_pred_axis {a : ℝ} {x : ℝ} {P : ℂ × ℂ}
    (h : EqRelC a P (((x : ℝ) : ℂ), 0)) (hx : x ≠ -(a / 2)) :
    P = (((1 - x : ℝ) : ℂ), 0) ∨ P = (((-1 - x : ℝ) : ℂ), 0) := by
  have hpar := eqRelC_par h
  obtain ⟨h1, h2⟩ := h
  have hxc : ((x : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ) ≠ 0 := by
    intro hc
    refine hx ?_
    have h1' : x + a / 2 = 0 := by
      have := congrArg Complex.re hc
      simpa using this
    linarith
  have hy : P.2 = 0 := by
    have hq : P.2 * (((x : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)) = 0 := by linear_combination -hpar
    exact (mul_eq_zero.mp hq).resolve_right hxc
  have hx1 : (P.1 + ((x : ℝ) : ℂ)) ^ 2 = 1 := by linear_combination h1 - hy * P.2
  rcases sq_eq_one_iff.mp hx1 with hq | hq
  · left; refine Prod.ext ?_ hy; push_cast; linear_combination hq
  · right; refine Prod.ext ?_ hy; push_cast; linear_combination hq

/-- The bisector reflection maps the relation to its inverse (Rychlik's reversibility
`U⁻¹ = M U M`). -/
lemma eqRelC_mirror_swap {a : ℝ} {P Q : ℂ × ℂ} (h : EqRelC a P Q) :
    EqRelC a (eqMirror Q) (eqMirror P) := by
  obtain ⟨h1, h2⟩ := h
  have hpar := eqRelC_par ⟨h1, h2⟩
  constructor
  · simp only [eqMirror]; linear_combination h1
  · simp only [eqMirror]; linear_combination -hpar

lemma regPair_mirror {a : ℝ} {P Q : ℂ × ℂ} (h : RegPair a P Q) :
    RegPair a (eqMirror Q) (eqMirror P) := by
  obtain ⟨hE, hP, hQ⟩ := h
  refine ⟨eqRelC_mirror_swap hE, ?_, ?_⟩
  · simp only [eqMirror]; intro hc; exact hQ (by linear_combination hc)
  · simp only [eqMirror]; intro hc; exact hP (by linear_combination hc)

/-! ## Part 2: the two reflection orbits on the real axis -/

/-- The orbit of `a/2` under the two reflection maps `x ↦ 1 - x`, `x ↦ -1 - x`. -/
def orbA (a : ℝ) : Set ℝ := {x | ∃ k : ℤ, x = a / 2 + 2 * k ∨ x = 1 - a / 2 + 2 * k}

/-- The orbit of `-a/2` under the two reflection maps `x ↦ 1 - x`, `x ↦ -1 - x`. -/
def orbB (a : ℝ) : Set ℝ := {x | ∃ k : ℤ, x = -(a / 2) + 2 * k ∨ x = 1 + a / 2 + 2 * k}

lemma orbA_self {a : ℝ} : a / 2 ∈ orbA a := ⟨0, by norm_num⟩

lemma orbB_self {a : ℝ} : -(a / 2) ∈ orbB a := ⟨0, by norm_num⟩

lemma orbA_sub {a : ℝ} {x : ℝ} (h : x ∈ orbA a) : 1 - x ∈ orbA a := by
  obtain ⟨k, hk | hk⟩ := h
  · exact ⟨-k, Or.inr (by rw [hk]; push_cast; ring)⟩
  · exact ⟨-k, Or.inl (by rw [hk]; push_cast; ring)⟩

lemma orbA_neg_sub {a : ℝ} {x : ℝ} (h : x ∈ orbA a) : -1 - x ∈ orbA a := by
  obtain ⟨k, hk | hk⟩ := h
  · exact ⟨-1 - k, Or.inr (by rw [hk]; push_cast; ring)⟩
  · exact ⟨-1 - k, Or.inl (by rw [hk]; push_cast; ring)⟩

lemma orbB_sub {a : ℝ} {x : ℝ} (h : x ∈ orbB a) : 1 - x ∈ orbB a := by
  obtain ⟨k, hk | hk⟩ := h
  · exact ⟨-k, Or.inr (by rw [hk]; push_cast; ring)⟩
  · exact ⟨-k, Or.inl (by rw [hk]; push_cast; ring)⟩

lemma orbB_neg_sub {a : ℝ} {x : ℝ} (h : x ∈ orbB a) : -1 - x ∈ orbB a := by
  obtain ⟨k, hk | hk⟩ := h
  · exact ⟨-1 - k, Or.inr (by rw [hk]; push_cast; ring)⟩
  · exact ⟨-1 - k, Or.inl (by rw [hk]; push_cast; ring)⟩

lemma int_not_unit_interval {m : ℤ} (h1 : 0 < (m : ℝ)) (h2 : (m : ℝ) < 1) : False := by
  have hm1 : 1 ≤ m := by
    by_contra hcon
    have hm0 : m ≤ 0 := by omega
    have : (m : ℝ) ≤ 0 := by exact_mod_cast hm0
    linarith
  have hm2 : m ≤ 0 := by
    by_contra hcon
    have h1m : 1 ≤ m := by omega
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1m
    linarith
  omega

lemma int_not_neg_unit_interval {m : ℤ} (h1 : -1 < (m : ℝ)) (h2 : (m : ℝ) < 0) : False := by
  have hm1 : m ≤ -1 := by
    by_contra hcon
    have hm0 : 0 ≤ m := by omega
    have : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm0
    linarith
  have hm2 : 0 ≤ m := by
    by_contra hcon
    have h1m : m ≤ -1 := by omega
    have : (m : ℝ) ≤ -1 := by exact_mod_cast h1m
    linarith
  omega

lemma orbB_not_half {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : a / 2 ∉ orbB a := by
  rintro ⟨k, hk | hk⟩
  · have hEq : ((2 * k : ℤ) : ℝ) = a := by
      have h' : a / 2 = -(a / 2) + 2 * (k : ℝ) := hk
      push_cast; linarith
    exact int_not_unit_interval (by rw [hEq]; exact ha0) (by rw [hEq]; exact ha1)
  · have hEq : ((2 * k : ℤ) : ℝ) = -1 := by
      have h' : a / 2 = 1 + a / 2 + 2 * (k : ℝ) := hk
      push_cast; linarith
    have h2 : (2 * k : ℤ) = -1 := by exact_mod_cast hEq
    omega

lemma orbA_not_neg {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : -(a / 2) ∉ orbA a := by
  rintro ⟨k, hk | hk⟩
  · have hEq : ((2 * k : ℤ) : ℝ) = -a := by
      have h' : -(a / 2) = a / 2 + 2 * (k : ℝ) := hk
      push_cast; linarith
    exact int_not_neg_unit_interval (by rw [hEq]; linarith) (by rw [hEq]; linarith)
  · have hEq : ((2 * k : ℤ) : ℝ) = -1 := by
      have h' : -(a / 2) = 1 - a / 2 + 2 * (k : ℝ) := hk
      push_cast; linarith
    have h2 : (2 * k : ℤ) = -1 := by exact_mod_cast hEq
    omega

/-! ## Part 3: constancy propagation (F2) -/

/-- A continuous function on a preconnected set with at most two values is constant. -/
lemma const_of_two {U : Set ℂ} (hU : IsPreconnected U) {f : ℂ → ℂ × ℂ} (hf : ContinuousOn f U)
    {c1 c2 : ℂ × ℂ} (h12 : c1 ≠ c2) (hv : ∀ z ∈ U, f z = c1 ∨ f z = c2) :
    (∀ z ∈ U, f z = c1) ∨ (∀ z ∈ U, f z = c2) := by
  haveI : PreconnectedSpace U := Subtype.preconnectedSpace hU
  have hcont : Continuous (fun x : U => f x.1) := hf.domRestrict
  set A : Set U := {x | f x.1 = c1} with hA
  set B : Set U := {x | f x.1 = c2} with hB
  have hAc : IsClosed A := isClosed_singleton.preimage hcont
  have hBc : IsClosed B := isClosed_singleton.preimage hcont
  have hcov : (Set.univ : Set U) ⊆ A ∪ B := by
    intro x _
    rcases hv x.1 x.2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hdis : (Set.univ : Set U) ∩ (A ∩ B) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨-, hxA, hxB⟩
    exact h12 (by rw [← hxA, hxB])
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp isPreconnected_univ A B hAc hBc hcov
    hdis) with h | h
  · left; intro z hz; exact h (Set.mem_univ ⟨z, hz⟩)
  · right; intro z hz; exact h (Set.mem_univ ⟨z, hz⟩)

/-- **F2 (backward).** If one entry of an analytic family of `EqRelC`-chains is identically `O₂`,
then every earlier entry is a real point of the reflection orbit of `O₂`. -/
lemma const_backward_of_O2 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {m : ℂ → ℤ → ℂ × ℂ} {U : Set ℂ}
    (hU : IsPreconnected U) (hm : ∀ n : ℤ, ContinuousOn (fun z => m z n) U)
    (hrel : ∀ z ∈ U, ∀ n : ℤ, EqRelC a (m z n) (m z (n + 1))) {j0 : ℤ}
    (h0 : ∀ z ∈ U, m z j0 = ptO2 a) :
    ∀ n : ℕ, ∃ x ∈ orbA a, ∀ z ∈ U, m z (j0 - (n : ℤ)) = (((x : ℝ) : ℂ), (0 : ℂ)) := by
  intro n
  induction n with
  | zero => exact ⟨a / 2, orbA_self, by simpa [ptO2] using h0⟩
  | succ n ih =>
    obtain ⟨x, hx, hxl⟩ := ih
    have hxne : x ≠ -(a / 2) := fun hc => orbA_not_neg ha0 ha1 (hc ▸ hx)
    have hcases : ∀ z ∈ U, m z (j0 - ((n : ℤ) + 1)) = (((1 - x : ℝ) : ℂ), (0 : ℂ)) ∨
        m z (j0 - ((n : ℤ) + 1)) = (((-1 - x : ℝ) : ℂ), (0 : ℂ)) := by
      intro z hz
      have hrel' := hrel z hz (j0 - ((n : ℤ) + 1))
      rw [show j0 - ((n : ℤ) + 1) + 1 = j0 - (n : ℤ) by ring, hxl z hz] at hrel'
      have := eqRelC_pred_axis (a := a) hrel' hxne
      simpa using this
    have hcont : ContinuousOn (fun z => m z (j0 - ((n : ℤ) + 1))) U := hm _
    have h12 : (((1 - x : ℝ) : ℂ), (0 : ℂ)) ≠ (((-1 - x : ℝ) : ℂ), (0 : ℂ)) := by
      intro hc
      have h1 : ((1 - x : ℝ) : ℂ) = ((-1 - x : ℝ) : ℂ) := congrArg Prod.fst hc
      have : (1 : ℝ) - x = -1 - x := Complex.ofReal_injective h1
      linarith
    rcases const_of_two hU hcont h12 hcases with h | h
    · exact ⟨1 - x, orbA_sub hx, h⟩
    · exact ⟨-1 - x, orbA_neg_sub hx, h⟩

/-- **F2 (forward).** If one entry of an analytic family of `EqRelC`-chains is identically `O₁`,
then every later entry is a real point of the reflection orbit of `O₁`. -/
lemma const_forward_of_O1 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {m : ℂ → ℤ → ℂ × ℂ} {U : Set ℂ}
    (hU : IsPreconnected U) (hm : ∀ n : ℤ, ContinuousOn (fun z => m z n) U)
    (hrel : ∀ z ∈ U, ∀ n : ℤ, EqRelC a (m z n) (m z (n + 1))) {j0 : ℤ}
    (h0 : ∀ z ∈ U, m z j0 = ptO1 a) :
    ∀ n : ℕ, ∃ x ∈ orbB a, ∀ z ∈ U, m z (j0 + (n : ℤ)) = (((x : ℝ) : ℂ), (0 : ℂ)) := by
  intro n
  induction n with
  | zero => exact ⟨-(a / 2), orbB_self, by simpa [ptO1] using h0⟩
  | succ n ih =>
    obtain ⟨x, hx, hxl⟩ := ih
    have hxne : x ≠ a / 2 := fun hc => orbB_not_half ha0 ha1 (hc ▸ hx)
    have hcases : ∀ z ∈ U, m z (j0 + ((n : ℤ) + 1)) = (((1 - x : ℝ) : ℂ), (0 : ℂ)) ∨
        m z (j0 + ((n : ℤ) + 1)) = (((-1 - x : ℝ) : ℂ), (0 : ℂ)) := by
      intro z hz
      have hrel' := hrel z hz (j0 + (n : ℤ))
      rw [hxl z hz] at hrel'
      have := eqRelC_succ_axis (a := a) hrel' hxne
      simpa [add_assoc] using this
    have hcont : ContinuousOn (fun z => m z (j0 + ((n : ℤ) + 1))) U := hm _
    have h12 : (((1 - x : ℝ) : ℂ), (0 : ℂ)) ≠ (((-1 - x : ℝ) : ℂ), (0 : ℂ)) := by
      intro hc
      have h1 : ((1 - x : ℝ) : ℂ) = ((-1 - x : ℝ) : ℂ) := congrArg Prod.fst hc
      have : (1 : ℝ) - x = -1 - x := Complex.ofReal_injective h1
      linarith
    rcases const_of_two hU hcont h12 hcases with h | h
    · exact ⟨1 - x, orbB_sub hx, h⟩
    · exact ⟨-1 - x, orbB_neg_sub hx, h⟩

/-! ## Part 4: avoiding thin sets and forcing the tails -/

/-- A finite family of closed subsets of a nonempty space, each with empty interior, cannot cover
the space: some point avoids all of them. -/
lemma exists_notMem_finset_of_isClosed_of_interior_eq_empty {X : Type*} [TopologicalSpace X]
    [Nonempty X] {ι : Type*} [DecidableEq ι] (A : ι → Set X) (s : Finset ι)
    (hcl : ∀ i ∈ s, IsClosed (A i)) (hint : ∀ i ∈ s, interior (A i) = ∅) :
    ∃ x : X, ∀ i ∈ s, x ∉ A i := by
  suffices h : ∃ O : Set X, IsOpen O ∧ O.Nonempty ∧ ∀ i ∈ s, ∀ x ∈ O, x ∉ A i by
    obtain ⟨O, _, ⟨x, hx⟩, hdis⟩ := h
    exact ⟨x, fun i hi => hdis i hi x hx⟩
  induction s using Finset.induction with
  | empty => exact ⟨Set.univ, isOpen_univ, ⟨Classical.arbitrary X, trivial⟩, by simp⟩
  | insert a t ha ih =>
    obtain ⟨O, hO, hOne, hdis⟩ := ih (fun i hi => hcl i (Finset.mem_insert_of_mem hi))
      (fun i hi => hint i (Finset.mem_insert_of_mem hi))
    have haint : interior (A a) = ∅ := hint a (Finset.mem_insert_self a t)
    have hcl' : IsClosed (A a) := hcl a (Finset.mem_insert_self a t)
    have hOnot : ¬ O ⊆ A a := by
      intro hsub
      have hsub' : O ⊆ interior (A a) := hO.subset_interior_iff.mpr hsub
      rw [haint] at hsub'
      obtain ⟨y, hy⟩ := hOne
      exact hsub' hy
    obtain ⟨y, hyO, hya⟩ := Set.not_subset.mp hOnot
    refine ⟨O ∩ (A a)ᶜ, hO.inter hcl'.isOpen_compl, ⟨y, hyO, hya⟩, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · intro x hx; exact fun hxa => hx.2 hxa
    · intro x hx; exact hdis i hi' x hx.1

/-- The tails of the family lie in the ball where the germ facts hold. -/
lemma tail_mem_ball {l r ρ₀ : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {w : ℂ → ℂ} {U : Set ℂ}
    {N K : ℕ} (hsmall : ∀ z ∈ U, ‖(l : ℂ) ^ N * w z‖ < r) (hK : l ^ K * r < ρ₀) :
    ∀ z ∈ U, ∀ n : ℕ, N + K ≤ n → (l : ℂ) ^ n * w z ∈ Metric.ball (0 : ℂ) ρ₀ := by
  intro z hz n hn
  have hnN : N ≤ n := by omega
  have hnorm : ‖(l : ℂ) ^ n * w z‖ < ρ₀ := by
    have hnormpow : ∀ m : ℕ, ‖(l : ℂ) ^ m‖ = l ^ m := by
      intro m
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl0.le]
    have hsplit : (l : ℂ) ^ n * w z = (l : ℂ) ^ (n - N) * ((l : ℂ) ^ N * w z) := by
      conv_lhs => rw [show n = (n - N) + N by omega]
      rw [pow_add]; ring
    rw [hsplit, norm_mul, hnormpow]
    have hmono : l ^ (n - N) ≤ l ^ K := pow_le_pow_of_le_one hl0.le (le_of_lt hl1) (by omega)
    have hle := mul_le_mul hmono (le_of_lt (hsmall z hz)) (norm_nonneg _) (pow_nonneg hl0.le K)
    linarith [hK, hle]
  simpa [Metric.mem_ball, dist_eq_norm] using hnorm

/-- On a preconnected domain, a ball contained in the zero set of an analytic function forces the
function to vanish identically. -/
lemma not_ball_subset_zeroSet {U : Set ℂ} (hUc : IsPreconnected U) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hnz : ∃ z ∈ U, f z ≠ 0) {z : ℂ} (hz : z ∈ U) {ρ : ℝ}
    (hρ : 0 < ρ) (hsub : Metric.ball z ρ ⊆ {w | w ∈ U ∧ f w = 0}) : False := by
  have heq : f =ᶠ[𝓝 z] 0 := by
    filter_upwards [Metric.ball_mem_nhds z hρ] with w hw
    exact (hsub hw).2
  have hEqOn := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hf hUc hz heq
  obtain ⟨z', hz', hz'ne⟩ := hnz
  exact hz'ne (hEqOn hz')

/-- **F2, backward.** An entry identically `O₂` forces the backward tail to be constant, which
contradicts the non-constancy of the unstable parameter. -/
lemma not_const_O2 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {ρ₀ : ℝ}
    (hinj : Set.InjOn (fun w => (germC a h w).2) (Metric.ball (0 : ℂ) ρ₀))
    {m : ℂ → ℤ → ℂ × ℂ} {U : Set ℂ} {v : ℂ → ℂ}
    (hU : IsPreconnected U) (hm : ∀ n : ℤ, ContinuousOn (fun z => m z n) U)
    (hrel : ∀ z ∈ U, ∀ n : ℤ, EqRelC a (m z n) (m z (n + 1)))
    {j₀ : ℤ} (h0 : ∀ z ∈ U, m z j₀ = ptO2 a) {n₀ : ℕ} (hn₀ : -((n₀ : ℤ)) ≤ j₀)
    (htail : ∀ z ∈ U, m z (-(n₀ : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ n₀ * v z))
    (hvρ : ∀ z ∈ U, (eqLam a : ℂ) ^ n₀ * v z ∈ Metric.ball (0 : ℂ) ρ₀)
    (hvnc : ∃ z₁ ∈ U, ∃ z₂ ∈ U, v z₁ ≠ v z₂) : False := by
  have hlam_ne : (eqLam a : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (eqLam_pos_aux ha0 ha1))
  obtain ⟨x, -, hx⟩ := const_backward_of_O2 ha0 ha1 hU hm hrel h0 ((j₀ + n₀).toNat)
  have hidx : j₀ - (((j₀ + (n₀ : ℤ)).toNat : ℕ) : ℤ) = -(n₀ : ℤ) := by
    have : (((j₀ + (n₀ : ℤ)).toNat : ℕ) : ℤ) = j₀ + (n₀ : ℤ) := by omega
    rw [this]; ring
  have hconst : ∀ z ∈ U, (germC a h ((eqLam a : ℂ) ^ n₀ * v z)).2 = (0 : ℂ) := by
    intro z hz
    have h1 : (m z (-(n₀ : ℤ))).2 = (0 : ℂ) := by
      rw [← hidx]
      exact congrArg Prod.snd (hx z hz)
    rw [htail z hz] at h1
    simpa [ugermC, eqMirror] using h1
  obtain ⟨z₁, hz₁, z₂, hz₂, hne⟩ := hvnc
  refine hne ?_
  have h2 : ((eqLam a : ℂ) ^ n₀ * v z₁) = ((eqLam a : ℂ) ^ n₀ * v z₂) := by
    apply hinj (hvρ z₁ hz₁) (hvρ z₂ hz₂)
    show (germC a h ((eqLam a : ℂ) ^ n₀ * v z₁)).2 =
      (germC a h ((eqLam a : ℂ) ^ n₀ * v z₂)).2
    rw [hconst z₁ hz₁, hconst z₂ hz₂]
  exact mul_left_cancel₀ (pow_ne_zero n₀ hlam_ne) h2

/-- **F2, forward.** An entry identically `O₁` forces the forward tail to be constant, which
contradicts the non-constancy of the stable parameter. -/
lemma not_const_O1 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {ρ₀ : ℝ}
    (hinj : Set.InjOn (fun w => (germC a h w).2) (Metric.ball (0 : ℂ) ρ₀))
    {m : ℂ → ℤ → ℂ × ℂ} {U : Set ℂ} {u : ℂ → ℂ}
    (hU : IsPreconnected U) (hm : ∀ n : ℤ, ContinuousOn (fun z => m z n) U)
    (hrel : ∀ z ∈ U, ∀ n : ℤ, EqRelC a (m z n) (m z (n + 1)))
    {j₀ : ℤ} (h0 : ∀ z ∈ U, m z j₀ = ptO1 a) {n₀ : ℕ} (hn₀ : j₀ ≤ (n₀ : ℤ))
    (htail : ∀ z ∈ U, m z (n₀ : ℤ) = germC a h ((eqLam a : ℂ) ^ n₀ * u z))
    (huρ : ∀ z ∈ U, (eqLam a : ℂ) ^ n₀ * u z ∈ Metric.ball (0 : ℂ) ρ₀)
    (hunc : ∃ z₁ ∈ U, ∃ z₂ ∈ U, u z₁ ≠ u z₂) : False := by
  have hlam_ne : (eqLam a : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (eqLam_pos_aux ha0 ha1))
  obtain ⟨x, -, hx⟩ := const_forward_of_O1 ha0 ha1 hU hm hrel h0 ((n₀ - j₀).toNat)
  have hidx : j₀ + (((n₀ - j₀).toNat : ℕ) : ℤ) = (n₀ : ℤ) := by
    have : (((n₀ - j₀).toNat : ℕ) : ℤ) = (n₀ : ℤ) - j₀ := by omega
    rw [this]; ring
  have hconst : ∀ z ∈ U, germC a h ((eqLam a : ℂ) ^ n₀ * u z) = (((x : ℝ) : ℂ), (0 : ℂ)) := by
    intro z hz
    rw [← htail z hz, ← hidx]
    exact hx z hz
  obtain ⟨z₁, hz₁, z₂, hz₂, hne⟩ := hunc
  refine hne ?_
  have h2 : ((eqLam a : ℂ) ^ n₀ * u z₁) = ((eqLam a : ℂ) ^ n₀ * u z₂) := by
    apply hinj (huρ z₁ hz₁) (huρ z₂ hz₂)
    show (germC a h ((eqLam a : ℂ) ^ n₀ * u z₁)).2 =
      (germC a h ((eqLam a : ℂ) ^ n₀ * u z₂)).2
    rw [hconst z₁ hz₁, hconst z₂ hz₂]
  exact mul_left_cancel₀ (pow_ne_zero n₀ hlam_ne) h2

/-- The image of a smaller ball under a local chart is still a neighbourhood of the base point. -/
lemma chart_image_nbd {a : ℝ} {h : ℂ → ℂ} {q : ChainData} (hq : q ∈ H0 a h) {ρ : ℝ}
    (hρ : 0 < ρ) {f : ℂ → ChainData} (hf : f q.2.1 = q)
    (hmem : ∀ u ∈ Metric.ball q.2.1 ρ, f u ∈ H0 a h ∧ (f u).2.1 = u)
    (hnbd : Subtype.val ⁻¹' (f '' Metric.ball q.2.1 ρ) ∈ 𝓝 (⟨q, hq⟩ : H0 a h))
    {δ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) :
    Subtype.val ⁻¹' (f '' Metric.ball q.2.1 δ) ∈ 𝓝 (⟨q, hq⟩ : H0 a h) := by
  have hproj : Continuous (fun x : H0 a h => (x : ChainData).2.1) :=
    (continuous_fst.comp continuous_snd).comp continuous_subtype_val
  have hEq : Subtype.val ⁻¹' (f '' Metric.ball q.2.1 δ) =
      (Subtype.val ⁻¹' (f '' Metric.ball q.2.1 ρ)) ∩
        {x : H0 a h | (x : ChainData).2.1 ∈ Metric.ball q.2.1 δ} := by
    ext x
    constructor
    · intro hx
      obtain ⟨w, hw, hwx⟩ := hx
      refine ⟨⟨w, lt_of_lt_of_le hw hδρ, hwx⟩, ?_⟩
      simp only [Set.mem_ofPred_eq]
      have h2 : (f w).2.1 = w := (hmem w (lt_of_lt_of_le hw hδρ)).2
      rw [← hwx, h2]
      exact hw
    · rintro ⟨⟨w, hw, hwx⟩, hx2⟩
      refine ⟨w, ?_, hwx⟩
      simp only [Set.mem_ofPred_eq] at hx2
      have h2 : (f w).2.1 = w := (hmem w hw).2
      rw [← hwx, h2] at hx2
      exact hx2
  rw [hEq]
  refine Filter.inter_mem hnbd ?_
  have hmem' : {x : H0 a h | (x : ChainData).2.1 ∈ Metric.ball q.2.1 δ} ∈ 𝓝 (⟨q, hq⟩ : H0 a h) := by
    have h1 : Metric.ball q.2.1 δ ∈ 𝓝 (q.2.1) := Metric.ball_mem_nhds _ hδ
    exact (hproj.continuousAt.preimage_mem_nhds h1)
  exact hmem'

/-- **Propagation of `ψ₁ψ₂ = c` along a component of `⁰H`.** If the local sections of `⁰H` are
analytic in `ψ₁` (the content of `H0_structure`) and `ψ₁ψ₂ = c` holds near `p ∈ H0`, then it holds
on the whole component of `p`: the zero set of the analytic function `ψ - c` in the
`ψ₁`-coordinate is open and closed in the component. -/
lemma component_const_of_nbd {a : ℝ} {h : ℂ → ℂ} {c : ℂ}
    (hchart : ∀ p ∈ H0 a h, ∃ ρ : ℝ, 0 < ρ ∧ ∃ f : ℂ → ChainData, f p.2.1 = p ∧
      (∀ u ∈ Metric.ball p.2.1 ρ, f u ∈ H0 a h ∧ (f u).2.1 = u) ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ (fun u => (f u).1 n) (Metric.ball p.2.1 ρ)) ∧
      AnalyticOnNhd ℂ (fun u => (f u).2.2) (Metric.ball p.2.1 ρ) ∧
      f '' Metric.ball p.2.1 ρ ∈ 𝓝[H0 a h] p)
    {p : ChainData} (hp : p ∈ H0 a h)
    (hnbd : {q : H0 a h | (q : ChainData).2.1 * (q : ChainData).2.2 = c} ∈ 𝓝 (⟨p, hp⟩ : H0 a h)) :
    ∀ q ∈ connectedComponentIn (H0 a h) p, q.2.1 * q.2.2 = c := by
  have hproj : Continuous (fun q : H0 a h => (q : ChainData).2.1) :=
    (continuous_fst.comp continuous_snd).comp continuous_subtype_val
  set Ω : Set (H0 a h) := {q | (q : ChainData).2.1 * (q : ChainData).2.2 = c} with hΩ
  have hΩclosed : IsClosed Ω := by
    refine isClosed_eq ?_ continuous_const
    exact hproj.mul ((continuous_snd.comp continuous_snd).comp continuous_subtype_val)
  set A : Set (H0 a h) := interior Ω with hA
  have hAopen : IsOpen A := isOpen_interior
  have hpA : (⟨p, hp⟩ : H0 a h) ∈ A := mem_interior_iff_mem_nhds.mpr hnbd
  have hAclosed : IsClosed A := by
    rw [← closure_subset_iff_isClosed]
    intro q hq
    obtain ⟨ρq, hρq, fq, hfq0, hfqmem, -, hfqan, hfqnbd⟩ := hchart q.1 q.2
    have hfqnbdX : Subtype.val ⁻¹' (fq '' Metric.ball q.1.2.1 ρq) ∈ 𝓝 q := by
      rw [nhdsWithin_eq_map_subtype_coe q.2, Filter.mem_map] at hfqnbd
      exact hfqnbd
    set G : ℂ → ℂ := fun w => w * (fq w).2.2 with hG
    have hGan : AnalyticOnNhd ℂ G (Metric.ball q.1.2.1 ρq) :=
      AnalyticOnNhd.mul analyticOnNhd_id hfqan
    have hGat : AnalyticAt ℂ (fun w => G w - c) q.1.2.1 :=
      (hGan.sub analyticOnNhd_const) q.1.2.1 (Metric.mem_ball_self hρq)
    rcases hGat.eventually_eq_zero_or_eventually_ne_zero with h0 | hne
    · -- the parameter function vanishes near `ψ₁ q`
      obtain ⟨δ, hδ, hδsub⟩ : ∃ δ > 0, ∀ w, dist w q.1.2.1 < δ → G w - c = 0 := by
        obtain ⟨t, ht, htsub⟩ := Metric.mem_nhds_iff.mp h0
        exact ⟨t, ht, fun w hw => htsub (by simpa [Metric.mem_ball] using hw)⟩
      set δ' : ℝ := min δ ρq with hδ'def
      have hδ'pos : 0 < δ' := lt_min hδ hρq
      have hδ'le : δ' ≤ ρq := min_le_right _ _
      have hsubΩ : Subtype.val ⁻¹' (fq '' Metric.ball q.1.2.1 δ') ⊆ Ω := by
        rintro x ⟨w, hw, hwx⟩
        have hwρ : w ∈ Metric.ball q.1.2.1 ρq := lt_of_lt_of_le hw hδ'le
        have hmem := hfqmem w hwρ
        have hc0 : G w - c = 0 := hδsub w (lt_of_lt_of_le hw (min_le_left _ _))
        have hc1 : w * (fq w).2.2 - c = 0 := by simpa [hG] using hc0
        have hwc : w * (fq w).2.2 = c := sub_eq_zero.mp hc1
        show (x : ChainData).2.1 * (x : ChainData).2.2 = c
        rw [← hwx, hmem.2]
        exact hwc
      have hnb := chart_image_nbd (a := a) (h := h) q.2 hρq hfq0 hfqmem hfqnbdX hδ'pos hδ'le
      exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hnb hsubΩ)
    · -- the parameter function is nonzero on a punctured neighbourhood
      have hne' : ∀ᶠ w in 𝓝 q.1.2.1, w ≠ q.1.2.1 → G w - c ≠ 0 :=
        eventually_nhdsWithin_iff.mp hne
      obtain ⟨δ₀, hδ₀, hδ₀ne⟩ : ∃ δ₀ > 0, ∀ w, dist w q.1.2.1 < δ₀ → w ≠ q.1.2.1 →
          G w - c ≠ 0 := by
        obtain ⟨t, ht, htsub⟩ := Metric.mem_nhds_iff.mp hne'
        exact ⟨t, ht, fun w hw hwne => htsub (by simpa [Metric.mem_ball] using hw) hwne⟩
      set δ₁ : ℝ := min δ₀ ρq with hδ₁def
      have hδ₁pos : 0 < δ₁ := lt_min hδ₀ hρq
      have hδ₁le : δ₁ ≤ ρq := min_le_right _ _
      have hnb := chart_image_nbd (a := a) (h := h) q.2 hρq hfq0 hfqmem hfqnbdX hδ₁pos hδ₁le
      obtain ⟨O, hOsub, hOopen, hqO⟩ := mem_nhds_iff.mp hnb
      obtain ⟨x, hxO, hxA⟩ := mem_closure_iff.mp hq O hOopen hqO
      have hximg : (x : ChainData) ∈ fq '' Metric.ball q.1.2.1 δ₁ := hOsub hxO
      obtain ⟨w, hw, hwx⟩ := hximg
      have hxΩ : (x : ChainData).2.1 * (x : ChainData).2.2 = c := by
        have h1 : x ∈ Ω := interior_subset hxA
        simpa [hΩ] using h1
      have hwρ : w ∈ Metric.ball q.1.2.1 ρq := lt_of_lt_of_le hw hδ₁le
      have hwm : (fq w).2.1 = w := (hfqmem w hwρ).2
      have hGw : G w = c := by
        have h1 := hxΩ
        rw [← hwx, hwm] at h1
        simpa [hG] using h1
      by_cases hwq : w = q.1.2.1
      · have hxq : x = q := by
          apply Subtype.ext
          rw [← hwx, hwq, hfq0]
        rw [← hxq]
        exact hxA
      · have h1 : G w - c ≠ 0 := hδ₀ne w (lt_of_lt_of_le hw (min_le_left _ _)) hwq
        have h2 : G w - c = 0 := by rw [hGw]; ring
        exact absurd h2 h1
  have hsub : connectedComponent (⟨p, hp⟩ : H0 a h) ⊆ Ω := by
    have hcl : IsClopen A := ⟨hAclosed, hAopen⟩
    have hsubA : connectedComponent (⟨p, hp⟩ : H0 a h) ⊆ A :=
      isPreconnected_connectedComponent.subset_isClopen hcl
        ⟨⟨p, hp⟩, mem_connectedComponent, hpA⟩
    exact Set.Subset.trans hsubA interior_subset
  rw [connectedComponentIn_eq_image hp]
  rintro y ⟨q, hq, rfl⟩
  exact hsub hq


/-! ## Part 6: the theorem -/

/-- **An analytic family of (possibly singular) chains with constant invariant parameter
yields a regular component (Rychlik Thm 6 non-degeneracy + the step (136) ⇒ `M^(∞)` of
Thms 8 and 11).** -/
theorem exists_regular_of_family {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {U : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    {m : ℂ → ℤ → ℂ × ℂ} {u v : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hm : ∀ n : ℤ, AnalyticOnNhd ℂ (fun z => m z n) U) (hu : AnalyticOnNhd ℂ u U)
    (hu0 : ∀ z ∈ U, u z ≠ 0) (huv : ∀ z ∈ U, u z * v z = c)
    (hnc : ∃ z₁ ∈ U, ∃ z₂ ∈ U, u z₁ ≠ u z₂)
    (hrel : ∀ z ∈ U, ∀ n : ℤ, EqRelC a (m z n) (m z (n + 1))) {N : ℕ}
    (hsmall : ∀ z ∈ U, ‖(eqLam a : ℂ) ^ N * u z‖ < r ∧ ‖(eqLam a : ℂ) ^ N * v z‖ < r)
    (hs : ∀ z ∈ U, ∀ n : ℕ, N ≤ n → m z n = germC a h ((eqLam a : ℂ) ^ n * u z))
    (hus : ∀ z ∈ U, ∀ n : ℕ, N ≤ n → m z (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ n * v z)) :
    ∃ p ∈ H0 a h, ∀ q ∈ connectedComponentIn (H0 a h) p, q.2.1 * q.2.2 = c := by
  classical
  have ha_ne : a ≠ 0 := ne_of_gt ha0
  have hr : 0 < r := hh.1
  have hlam0 : 0 < eqLam a := eqLam_pos_aux ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one_aux ha0 ha1
  have hlam_ne : (eqLam a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlam0)
  have hpre : IsPreconnected U := hUc.isPreconnected
  -- `u` and `v` are not constant
  have hvnc : ∃ z₁ ∈ U, ∃ z₂ ∈ U, v z₁ ≠ v z₂ := by
    obtain ⟨z₁, hz₁, z₂, hz₂, hne⟩ := hnc
    refine ⟨z₁, hz₁, z₂, hz₂, fun hcon => hne ?_⟩
    have h1 := huv z₁ hz₁
    have h2 := huv z₂ hz₂
    rw [hcon] at h1
    by_cases hw : v z₂ = 0
    · have hzero : c = 0 := by rw [← h2, hw, mul_zero]
      exact absurd hzero hc
    · exact mul_right_cancel₀ hw (by rw [h1, h2])
  -- the derivative of `u` does not vanish identically
  have hderiv_nz : ∃ z ∈ U, deriv u z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨z₁, hz₁, z₂, hz₂, hne⟩ := hnc
    exact hne (hU.is_const_of_deriv_eq_zero hpre hu.differentiableOn
      (fun z hz => hcon z hz) hz₁ hz₂)
  -- the local germ facts
  obtain ⟨ρ₀, hρ₀, hgerm_an, hgerm_zero, hgerm_reg, hgerm_inj, -⟩ := germC_facts ha0 ha1 hh
  -- the tail threshold
  obtain ⟨K, hK⟩ : ∃ K : ℕ, eqLam a ^ K * r < ρ₀ := by
    have htend : Tendsto (fun k : ℕ => eqLam a ^ k * r) atTop (𝓝 0) := by
      have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0.le hlam1).mul_const r
      simpa using h1
    exact (htend.eventually (isOpen_Iio.mem_nhds (show (0 : ℝ) < ρ₀ from hρ₀))).exists
  set M : ℕ := N + K with hM
  have hNM : N ≤ M := by omega
  have htailu : ∀ z ∈ U, ∀ n : ℕ, M ≤ n → (eqLam a : ℂ) ^ n * u z ∈ Metric.ball (0 : ℂ) ρ₀ := by
    intro z hz n hn
    exact tail_mem_ball hlam0 hlam1 (fun z hz => (hsmall z hz).1) hK z hz n (by omega)
  have htailv : ∀ z ∈ U, ∀ n : ℕ, M ≤ n → (eqLam a : ℂ) ^ n * v z ∈ Metric.ball (0 : ℂ) ρ₀ := by
    intro z hz n hn
    exact tail_mem_ball hlam0 hlam1 (fun z hz => (hsmall z hz).2) hK z hz n (by omega)
  -- no entry is identically `O₁` or `O₂`
  have hnoO1 : ∀ j : ℤ, ¬ ∀ z ∈ U, m z j = ptO1 a := by
    intro j h0
    obtain ⟨n, hnNK, hjn⟩ : ∃ n : ℕ, N + K ≤ n ∧ j ≤ (n : ℤ) :=
      ⟨max (N + K) (j.toNat + 1), le_max_left _ _, by
        have h1 : j ≤ ((j.toNat : ℕ) : ℤ) + 1 := by omega
        have h2 : (((j.toNat : ℕ) : ℤ) + 1) ≤ ((max (N + K) (j.toNat + 1) : ℕ) : ℤ) := by
          exact_mod_cast le_max_right (N + K) (j.toNat + 1)
        linarith⟩
    exact not_const_O1 ha0 ha1 (h := h) (ρ₀ := ρ₀) hgerm_inj hpre
      (fun n => (hm n).continuousOn) hrel h0 hjn
      (fun z hz => hs z hz n (by omega)) (fun z hz => htailu z hz n (by omega)) hnc
  have hnoO2 : ∀ j : ℤ, ¬ ∀ z ∈ U, m z j = ptO2 a := by
    intro j h0
    obtain ⟨n, hnNK, hjn⟩ : ∃ n : ℕ, N + K ≤ n ∧ -((n : ℤ)) ≤ j :=
      ⟨max (N + K) ((-j).toNat + 1), le_max_left _ _, by
        have h1 : (-j : ℤ) ≤ (((-j).toNat : ℕ) : ℤ) + 1 := by omega
        have h2 : ((((-j).toNat : ℕ) : ℤ) + 1) ≤
            ((max (N + K) ((-j).toNat + 1) : ℕ) : ℤ) := by
          exact_mod_cast le_max_right (N + K) ((-j).toNat + 1)
        linarith⟩
    exact not_const_O2 ha0 ha1 (h := h) (ρ₀ := ρ₀) hgerm_inj hpre
      (fun n => (hm n).continuousOn) hrel h0 hjn
      (fun z hz => hus z hz n (by omega)) (fun z hz => htailv z hz n (by omega)) hvnc
  -- the middle index range, and the bad sets in the domain `U`
  set I : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ) with hI
  have hUne : Nonempty U := by
    obtain ⟨z, hz⟩ := hUc.nonempty
    exact ⟨⟨z, hz⟩⟩
  set bad : ℤ → Set U := fun j => {x : U | m x.1 j = ptO1 a ∨ m x.1 j = ptO2 a} with hbad
  set crit : Set U := {x : U | deriv u x.1 = 0} with hcrit
  have hbad_closed : ∀ j : ℤ, IsClosed (bad j) := by
    intro j
    have hcont : Continuous (fun x : U => m x.1 j) := (hm j).continuousOn.domRestrict
    have hset : bad j = (fun x : U => m x.1 j) ⁻¹' (({ptO1 a} ∪ {ptO2 a}) : Set (ℂ × ℂ)) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_singleton_iff, hbad, Set.mem_ofPred_eq]
    rw [hset]
    exact (isClosed_singleton.union isClosed_singleton).preimage hcont
  have hcrit_closed : IsClosed crit := by
    have hcont : Continuous (fun x : U => deriv u x.1) := (hu.deriv).continuousOn.domRestrict
    have hset : crit = (fun x : U => deriv u x.1) ⁻¹' ({0} : Set ℂ) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hcrit, Set.mem_ofPred_eq]
    rw [hset]
    exact isClosed_singleton.preimage hcont
  have hbad_interior : ∀ j : ℤ, interior (bad j) = ∅ := by
    intro j
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x hxint
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp isOpen_interior x hxint
    obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.isOpen_iff.mp hU x.1 x.2
    set r₂ : ℝ := min r₁ r with hr₂def
    have hr₂ : 0 < r₂ := lt_min hr₁ hr
    have htwo : ∀ w ∈ Metric.ball x.1 r₂, m w j = ptO1 a ∨ m w j = ptO2 a := by
      intro w hw
      have hwU : w ∈ U := hr₁sub (Metric.mem_ball.mpr (lt_of_lt_of_le hw (min_le_left _ _)))
      have hmem : (⟨w, hwU⟩ : U) ∈ Metric.ball x r := by
        rw [Metric.mem_ball, Subtype.dist_eq]
        exact lt_of_lt_of_le hw (min_le_right _ _)
      have h1 : (⟨w, hwU⟩ : U) ∈ bad j := interior_subset (hrsub hmem)
      simpa [hbad] using h1
    have hcont : ContinuousOn (fun w => m w j) (Metric.ball x.1 r₂) :=
      ((hm j).continuousOn).mono (fun w hw => hr₁sub (Metric.mem_ball.mpr (lt_of_lt_of_le hw (min_le_left _ _))))
    rcases const_of_two (U := Metric.ball x.1 r₂) Metric.isPreconnected_ball hcont
      (ptO1_ne_ptO2 ha_ne) htwo with h | h
    · refine hnoO1 j ?_
      intro z hz
      have hev : (fun w => m w j) =ᶠ[𝓝 x.1] (fun _ => ptO1 a) := by
        filter_upwards [Metric.ball_mem_nhds x.1 hr₂] with w hw
        exact h w hw
      exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hm j) analyticOnNhd_const
        hpre x.2 hev) hz
    · refine hnoO2 j ?_
      intro z hz
      have hev : (fun w => m w j) =ᶠ[𝓝 x.1] (fun _ => ptO2 a) := by
        filter_upwards [Metric.ball_mem_nhds x.1 hr₂] with w hw
        exact h w hw
      exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hm j) analyticOnNhd_const
        hpre x.2 hev) hz
  have hcrit_interior : interior crit = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x hxint
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp isOpen_interior x hxint
    obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.isOpen_iff.mp hU x.1 x.2
    set r₂ : ℝ := min r₁ r with hr₂def
    have hr₂ : 0 < r₂ := lt_min hr₁ hr
    refine not_ball_subset_zeroSet (f := deriv u) hpre hu.deriv hderiv_nz x.2 hr₂ ?_
    intro w hw
    refine ⟨hr₁sub (Metric.mem_ball.mpr (lt_of_lt_of_le hw (min_le_left _ _))), ?_⟩
    have hmem : (⟨w, hr₁sub (Metric.mem_ball.mpr (lt_of_lt_of_le hw (min_le_left _ _)))⟩ : U) ∈
        Metric.ball x r := by
      rw [Metric.mem_ball, Subtype.dist_eq]
      exact lt_of_lt_of_le hw (min_le_right _ _)
    have h1 := interior_subset (hrsub hmem)
    simpa [hcrit] using h1
  -- a point avoiding all the bad sets and the critical set
  set A : Option ℤ → Set U :=
    (fun i => match i with | none => crit | some j => bad j) with hAdef
  have hA_closed : ∀ i ∈ (insert none (I.image some) : Finset (Option ℤ)), IsClosed (A i) := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · show IsClosed (A none); simp only [hAdef]; exact hcrit_closed
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi'
      show IsClosed (A (some j)); simp only [hAdef]; exact hbad_closed j
  have hA_interior : ∀ i ∈ (insert none (I.image some) : Finset (Option ℤ)), interior (A i) = ∅ := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · show interior (A none) = ∅; simp only [hAdef]; exact hcrit_interior
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi'
      show interior (A (some j)) = ∅; simp only [hAdef]; exact hbad_interior j
  obtain ⟨x₀, hx₀⟩ :=
    exists_notMem_finset_of_isClosed_of_interior_eq_empty A _ hA_closed hA_interior
  have hz₀U : x₀.1 ∈ U := x₀.2
  have hz₀deriv : deriv u x₀.1 ≠ 0 := by
    have h := hx₀ none (Finset.mem_insert_self none _)
    simp only [hAdef, hcrit] at h
    exact h
  have hz₀bad : ∀ j ∈ I, m x₀.1 j ≠ ptO1 a ∧ m x₀.1 j ≠ ptO2 a := by
    intro j hj
    have hmem : (some j) ∈ (insert none (I.image some) : Finset (Option ℤ)) :=
      Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
    have h := hx₀ (some j) hmem
    simp only [hAdef, hbad, Set.mem_ofPred_eq, not_or] at h
    exact h
  have hx₀_notmem : x₀ ∉ (crit ∪ ⋃ j ∈ I, bad j) := by
    intro hcon
    rcases hcon with hc | hc
    · exact hx₀ none (Finset.mem_insert_self none _) (by simp only [hAdef]; exact hc)
    · rw [Set.mem_iUnion] at hc
      obtain ⟨j, hc⟩ := hc
      rw [Set.mem_iUnion] at hc
      obtain ⟨hj, hc⟩ := hc
      exact hx₀ (some j) (Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨j, hj, rfl⟩)))
        (by simp only [hAdef]; exact hc)
  have hunion_closed : IsClosed (crit ∪ ⋃ j ∈ I, bad j) :=
    hcrit_closed.union (isClosed_biUnion_finset (fun j _ => hbad_closed j))
  obtain ⟨r₃, hr₃, hr₃sub⟩ :
      ∃ r₃ > 0, ∀ y : U, dist y x₀ < r₃ → y ∉ (crit ∪ ⋃ j ∈ I, bad j) := by
    have hopen : IsOpen ((crit ∪ ⋃ j ∈ I, bad j)ᶜ) := hunion_closed.isOpen_compl
    obtain ⟨r₃, hr₃, hr₃sub⟩ := Metric.isOpen_iff.mp hopen x₀ (by simpa using hx₀_notmem)
    exact ⟨r₃, hr₃, fun y hy => hr₃sub (by simpa [Metric.mem_ball] using hy)⟩
  obtain ⟨r₄, hr₄, hr₄sub⟩ : ∃ r₄ > 0, Metric.ball x₀.1 r₄ ⊆ U :=
    Metric.isOpen_iff.mp hU x₀.1 x₀.2
  set r' : ℝ := min r₄ r₃ with hr'def
  have hr' : 0 < r' := lt_min hr₄ hr₃
  have hkey : ∀ w : ℂ, dist w x₀.1 < r' → w ∈ U ∧
      (∀ j ∈ I, m w j ≠ ptO1 a ∧ m w j ≠ ptO2 a) ∧ deriv u w ≠ 0 := by
    intro w hw
    have hwU : w ∈ U := hr₄sub (Metric.mem_ball.mpr (lt_of_lt_of_le hw (min_le_left _ _)))
    have hdist : dist (⟨w, hwU⟩ : U) x₀ < r₃ := by
      rw [Subtype.dist_eq]
      exact lt_of_lt_of_le hw (min_le_right _ _)
    have hnone := hr₃sub ⟨w, hwU⟩ hdist
    refine ⟨hwU, ?_, ?_⟩
    · intro j hj
      have h1 : (⟨w, hwU⟩ : U) ∉ bad j :=
        fun hcon => hnone (Or.inr (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, hcon⟩⟩))
      simp only [hbad, Set.mem_ofPred_eq, not_or] at h1
      exact h1
    · have h1 : (⟨w, hwU⟩ : U) ∉ crit := fun hcon => hnone (Or.inl hcon)
      simpa [hcrit] using h1
  -- the local inverse of `u` at `x₀`
  have huan : AnalyticAt ℂ u x₀.1 := hu x₀.1 x₀.2
  have hsderiv : HasStrictDerivAt u (deriv u x₀.1) x₀.1 := huan.hasStrictDerivAt
  set g : ℂ → ℂ := hsderiv.localInverse u (deriv u x₀.1) x₀.1 hz₀deriv with hgdef
  have hg0 : g (u x₀.1) = x₀.1 := by
    rw [hgdef]
    exact HasStrictFDerivAt.localInverse_apply_image ..
  have hgan : AnalyticAt ℂ g (u x₀.1) := by
    rw [hgdef]
    exact huan.analyticAt_localInverse hz₀deriv
  have hgright : ∀ᶠ w in 𝓝 (u x₀.1), u (g w) = w := by
    rw [hgdef]
    exact hsderiv.eventually_right_inverse hz₀deriv
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ : ∃ ρ₁ > 0, Metric.ball (u x₀.1) ρ₁ ⊆ {w | u (g w) = w} := by
    obtain ⟨t, ht, htsub⟩ := Metric.mem_nhds_iff.mp hgright
    exact ⟨t, ht, htsub⟩
  obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ : ∃ ρ₂ > 0, ∀ w, dist w (u x₀.1) < ρ₂ → dist (g w) x₀.1 < r' := by
    have hcont : ContinuousAt g (u x₀.1) := hgan.continuousAt
    have hmem : Metric.ball x₀.1 r' ∈ 𝓝 (g (u x₀.1)) := by
      rw [hg0]
      exact Metric.ball_mem_nhds x₀.1 hr'
    obtain ⟨t, ht, htsub⟩ := Metric.mem_nhds_iff.mp (hcont.preimage_mem_nhds hmem)
    exact ⟨t, ht, fun w hw => htsub (by simpa [Metric.mem_ball] using hw)⟩
  obtain ⟨ρ₃, hρ₃, hρ₃an⟩ : ∃ ρ₃ > 0, ∀ y ∈ Metric.ball (u x₀.1) ρ₃, AnalyticAt ℂ g y := by
    obtain ⟨t, ht, htsub⟩ := Metric.mem_nhds_iff.mp hgan.eventually_analyticAt
    exact ⟨t, ht, fun y hy => htsub (by simpa [Metric.mem_ball] using hy)⟩
  have huz : 0 < ‖u x₀.1‖ := norm_pos_iff.mpr (hu0 x₀.1 x₀.2)
  set ρ : ℝ := min ρ₃ (min ρ₁ (min ρ₂ ‖u x₀.1‖)) with hρdef
  have hρpos : 0 < ρ := lt_min hρ₃ (lt_min hρ₁ (lt_min hρ₂ huz))
  have hρρ₃ : ρ ≤ ρ₃ := min_le_left _ _
  have hρρ₁ : ρ ≤ ρ₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρρ₂ : ρ ≤ ρ₂ := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρuz : ρ ≤ ‖u x₀.1‖ :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hgcontOn : ContinuousOn g (Metric.ball (u x₀.1) ρ) := by
    refine fun y hy => ?_
    exact (hρ₃an y (lt_of_lt_of_le hy hρρ₃)).continuousAt.continuousWithinAt
  -- the section
  set fsec : ℂ → ChainData := fun w => ((fun n : ℤ => m (g w) n), w, c / w) with hfsec
  have hsec_mem : ∀ w ∈ Metric.ball (u x₀.1) ρ, IsChain a h (fsec w) ∧ (fsec w).2.1 = w := by
    intro w hw
    have hw₁ : dist w (u x₀.1) < ρ₁ := lt_of_lt_of_le hw hρρ₁
    have hw₂ : dist w (u x₀.1) < ρ₂ := lt_of_lt_of_le hw hρρ₂
    have hw₃ : dist w (u x₀.1) < ‖u x₀.1‖ := lt_of_lt_of_le hw hρuz
    have hgw : dist (g w) x₀.1 < r' := hρ₂sub w hw₂
    obtain ⟨hgwU, hgwbad, -⟩ := hkey (g w) hgw
    have huw : u (g w) = w := hρ₁sub (by simpa [Metric.mem_ball] using hw₁)
    have hwne : w ≠ 0 := by
      intro h0
      rw [h0, dist_zero_left] at hw₃
      exact absurd hw₃ (lt_irrefl _)
    have hvw : v (g w) = c / w := by
      have h1 := huv (g w) hgwU
      rw [huw] at h1
      rw [eq_div_iff hwne, mul_comm]
      exact h1
    refine ⟨?_, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- regularity at every step
      intro n
      rcases lt_or_ge n (M : ℤ) with hn | hn
      · rcases lt_or_ge n (-(M : ℤ)) with hn' | hn'
        · -- the backward tail: `n < -(M : ℤ)`
          obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -((k : ℤ)) := ⟨(-n).toNat, by omega⟩
          have hkM : M + 1 ≤ k := by omega
          have hkN : N ≤ k := by omega
          have hidx : -((k : ℤ)) + 1 = -(((k - 1 : ℕ)) : ℤ) := by omega
          have hmemk : (eqLam a : ℂ) ^ (k - 1) * v (g w) ∈ Metric.ball 0 ρ₀ :=
            htailv (g w) hgwU (k - 1) (by omega)
          have hsucc : (eqLam a : ℂ) ^ k * v (g w) =
              (eqLam a : ℂ) * ((eqLam a : ℂ) ^ (k - 1) * v (g w)) := by
            conv_lhs => rw [show k = (k - 1) + 1 by omega]
            rw [pow_succ]; ring
          simp only [hfsec]
          rw [hidx, hus (g w) hgwU k hkN, hus (g w) hgwU (k - 1) (by omega), hsucc]
          exact regPair_mirror (hgerm_reg _ hmemk).1
        · -- the middle: `-(M : ℤ) ≤ n < M`
          have hPn : m (g w) n ≠ ptO2 a :=
            (hgwbad n (Finset.mem_Icc.mpr ⟨hn', le_of_lt hn⟩)).2
          have hPn1 : m (g w) (n + 1) ≠ ptO1 a :=
            (hgwbad (n + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).1
          simp only [hfsec]
          exact regPair_iff.mpr ⟨hrel (g w) hgwU n, hPn, hPn1⟩
      · -- the forward tail: `M ≤ n`
        obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.toNat, by omega⟩
        have hkM : M ≤ k := by omega
        have hkN : N ≤ k := by omega
        have hmemk : (eqLam a : ℂ) ^ k * u (g w) ∈ Metric.ball 0 ρ₀ := htailu (g w) hgwU k hkM
        have hsucc : (eqLam a : ℂ) ^ (k + 1) * u (g w) =
            (eqLam a : ℂ) * ((eqLam a : ℂ) ^ k * u (g w)) := by
          rw [pow_succ]; ring
        have hidx : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
        simp only [hfsec]
        rw [hs (g w) hgwU k hkN, ← hidx, hs (g w) hgwU (k + 1) (by omega), hsucc]
        exact (hgerm_reg _ hmemk).1
    · simp only [hfsec]; exact hwne
    · simp only [hfsec]; exact div_ne_zero hc hwne
    · rw [Filter.eventually_atTop]
      refine ⟨M, fun n hn => ?_⟩
      simp only [hfsec]
      rw [hs (g w) hgwU n (le_trans hNM hn), huw]
    · rw [Filter.eventually_atTop]
      refine ⟨M, fun n hn => ?_⟩
      simp only [hfsec]
      rw [hus (g w) hgwU n (le_trans hNM hn), hvw]
  have hcont_fsec : ContinuousOn fsec (Metric.ball (u x₀.1) ρ) := by
    rw [hfsec]
    refine ContinuousOn.prodMk ?_ (ContinuousOn.prodMk continuousOn_id ?_)
    · rw [continuousOn_pi]
      intro n
      refine ((hm n).continuousOn).comp hgcontOn ?_
      intro y hy
      have hy₂ : dist y (u x₀.1) < ρ₂ :=
        lt_of_lt_of_le (by simpa [Metric.mem_ball] using hy) hρρ₂
      exact (hkey (g y) (hρ₂sub y hy₂)).1
    · refine continuousOn_const.div continuousOn_id ?_
      intro y hy
      have hy₃ : dist y (u x₀.1) < ‖u x₀.1‖ :=
        lt_of_lt_of_le (by simpa [Metric.mem_ball] using hy) hρuz
      intro h0
      rw [h0, dist_zero_left] at hy₃
      exact absurd hy₃ (lt_irrefl _)
  -- membership in `H0`
  have hp : fsec (u x₀.1) ∈ H0 a h :=
    ⟨ρ, hρpos, fsec, hcont_fsec, rfl, fun u hu => hsec_mem u hu⟩
  -- the neighbourhood of the base point
  have hmem' : ∀ w ∈ Metric.ball (u x₀.1) ρ, fsec w ∈ H0 a h := by
    intro w hw
    have hε : 0 < ρ - dist w (u x₀.1) := sub_pos.mpr (by simpa [Metric.mem_ball] using hw)
    have hsub : Metric.ball w (ρ - dist w (u x₀.1)) ⊆ Metric.ball (u x₀.1) ρ := by
      intro y hy
      rw [Metric.mem_ball] at hy ⊢
      calc dist y (u x₀.1) ≤ dist y w + dist w (u x₀.1) := dist_triangle _ _ _
        _ < (ρ - dist w (u x₀.1)) + dist w (u x₀.1) := by linarith
        _ = ρ := by ring
    exact ⟨ρ - dist w (u x₀.1), hε, fsec, hcont_fsec.mono hsub, rfl,
      fun u hu => hsec_mem u (hsub hu)⟩
  set pX : H0 a h := ⟨fsec (u x₀.1), hp⟩ with hpXdef
  obtain ⟨e, he_mem, he_eq⟩ := (H0_structure ha0 ha1 hh).1 pX
  have hproj : Continuous (fun q : H0 a h => (q : ChainData).2.1) :=
    (continuous_fst.comp continuous_snd).comp continuous_subtype_val
  set G : ℂ → H0 a h := fun w => if hw : w ∈ Metric.ball (u x₀.1) ρ
      then ⟨fsec w, hmem' w hw⟩ else pX with hGdef
  have hGvalgen : ∀ w (hw : w ∈ Metric.ball (u x₀.1) ρ),
      ((G w : H0 a h) : ChainData) = fsec w := by
    intro w hw
    simp only [hGdef]
    rw [dif_pos hw]
  have hEqG : fsec =ᶠ[𝓝 (u x₀.1)] (fun w => (G w : ChainData)) := by
    filter_upwards [Metric.ball_mem_nhds (u x₀.1) hρpos] with w hw
    simp only [hGdef]
    rw [dif_pos hw]
  have hGtend : Tendsto G (𝓝 (u x₀.1)) (𝓝 pX) := by
    rw [tendsto_subtype_rng]
    refine Filter.Tendsto.congr' hEqG ?_
    exact (hcont_fsec.continuousWithinAt (Metric.mem_ball_self hρpos)).continuousAt
      (Metric.ball_mem_nhds _ hρpos)
  obtain ⟨δ₀, hδ₀, hδ₀sub⟩ : ∃ δ₀ > 0, ∀ w, dist w (u x₀.1) < δ₀ → G w ∈ e.source := by
    have hgevent : ∀ᶠ w in 𝓝 (u x₀.1), G w ∈ e.source :=
      hGtend.eventually (e.open_source.mem_nhds he_mem)
    obtain ⟨t, ht, htsub⟩ := Metric.mem_nhds_iff.mp hgevent
    exact ⟨t, ht, fun w hw => htsub (by simpa [Metric.mem_ball] using hw)⟩
  set δ : ℝ := min δ₀ (min ρ ‖u x₀.1‖) with hδdef
  have hδpos : 0 < δ := lt_min hδ₀ (lt_min hρpos huz)
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδρ : δ ≤ ρ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδuz : δ ≤ ‖u x₀.1‖ := le_trans (min_le_right _ _) (min_le_right _ _)
  have hnb : e.source ∩ {q : H0 a h | (q : ChainData).2.1 ∈ Metric.ball (u x₀.1) δ} ∈ 𝓝 pX := by
    refine Filter.inter_mem (e.open_source.mem_nhds he_mem) ?_
    have h1 : Metric.ball (u x₀.1) δ ∈ 𝓝 ((pX : ChainData).2.1) := Metric.ball_mem_nhds _ hδpos
    exact hproj.continuousAt.preimage_mem_nhds h1
  have hnbd : {q : H0 a h | (q : ChainData).2.1 * (q : ChainData).2.2 = c} ∈ 𝓝 pX := by
    refine Filter.mem_of_superset hnb ?_
    rintro q ⟨hqe, hqw⟩
    have hqw' : dist ((q : ChainData).2.1) (u x₀.1) < δ := by
      simpa [Metric.mem_ball] using hqw
    have hqdist : dist ((q : ChainData).2.1) (u x₀.1) < ρ := lt_of_lt_of_le hqw' hδρ
    have hqdist₀ : dist ((q : ChainData).2.1) (u x₀.1) < δ₀ := lt_of_lt_of_le hqw' hδδ₀
    have hGmem : G ((q : ChainData).2.1) ∈ e.source := hδ₀sub _ hqdist₀
    have hpsi : (((G ((q : ChainData).2.1)) : H0 a h) : ChainData).2.1 = (q : ChainData).2.1 := by
      rw [hGvalgen _ hqdist]
    have he1 : e q = (q : ChainData).2.1 := (congrFun he_eq q).symm
    have he2 : e (G ((q : ChainData).2.1)) =
        (((G ((q : ChainData).2.1)) : H0 a h) : ChainData).2.1 := (congrFun he_eq _).symm
    have hqeq : q = G ((q : ChainData).2.1) := by
      refine e.injOn hqe hGmem ?_
      rw [he1, he2, hpsi]
    have hzw : (q : ChainData).2.1 ≠ 0 := by
      have h1 : dist ((q : ChainData).2.1) (u x₀.1) < ‖u x₀.1‖ := lt_of_lt_of_le hqw' hδuz
      intro h0
      rw [h0, dist_zero_left] at h1
      exact absurd h1 (lt_irrefl _)
    have h1 : (fsec ((q : ChainData).2.1)).2.1 = (q : ChainData).2.1 := (hsec_mem _ hqdist).2
    have h2 : (fsec ((q : ChainData).2.1)).2.2 = c / (q : ChainData).2.1 := rfl
    change (q : ChainData).2.1 * (q : ChainData).2.2 = c
    rw [hqeq, hGvalgen _ hqdist, h1, h2]
    exact mul_div_cancel₀ c hzw
  refine ⟨fsec (u x₀.1), hp, ?_⟩
  exact component_const_of_nbd (a := a) (h := h) (c := c)
    (H0_structure ha0 ha1 hh).2.1 hp hnbd

end Work.EQ
