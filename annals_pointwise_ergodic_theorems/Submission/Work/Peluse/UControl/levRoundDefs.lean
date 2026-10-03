import Mathlib
import Submission.Work.Peluse.UControl.levCubeDefs

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

attribute [local instance] Classical.propDecidable

/-!
# The dictionary of a level round (`LevRound`)

A `LevCube`-state of degree `D` has live slots the punctured cube `cubeSet L A f₀ \ {f₀}`, with
slot polynomials of degree `D` whose leading coefficient is the atom sum `Σ_{s ∈ ω} atoms s` of the
history.  This file sets up the dictionary used by the round of Peluse's Lemma 4.8
(`levRoundHolds`):

* `histOf A f₀ ω` — the history of the subset `ω ⊆ A` (the function `[i ∈ ω]` on `A`, `f₀` off `A`);
* `subSum A atoms ω` — the atom sum `Σ_{s ∈ ω ∩ A} atoms s`;
* `slotHist h₀ r w` — the history of a slot after `r` steps, obtained from the input history `h₀`
  by appending the `ε`-history `w : Fin r → Bool` of the steps (recursively, via `Fin.snoc`, which
  is exactly the way `HistData.step` appends the new Boolean parameter).
-/

variable {d D L : ℕ}

/-- The history attached to a subset `ω` of `A`: `[i ∈ ω]` on `A`, `f₀` off `A`. -/
def histOf (A : Finset (Fin L)) (f₀ : Fin L → Bool) (ω : Finset (Fin L)) : Fin L → Bool :=
  fun i => if i ∈ A then decide (i ∈ ω) else f₀ i

/-- The "atom sum" of a subset of `A`: `Σ_{s ∈ ω ∩ A} atoms s`. -/
def subSum (A : Finset (Fin L)) (atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ)
    (ω : Finset (Fin L)) : MvPolynomial (Fin L) ℤ :=
  ∑ s : {s // s ∈ A}, if (s.1 ∈ ω) then atoms s else 0

/-- The canonical history of a slot of the round: the input history `h₀`, extended by the
`ε`-history `w` of the steps performed so far. -/
def slotHist {L : ℕ} (h₀ : Fin L → Bool) : (r : ℕ) → (Fin r → Bool) → Fin (L + r) → Bool
  | 0, _ => h₀
  | r + 1, w => Fin.snoc (slotHist h₀ r (Fin.init w)) (w (Fin.last r))

lemma histOf_mem_cube {A : Finset (Fin L)} {f₀ : Fin L → Bool} (ω : Finset (Fin L)) :
    histOf A f₀ ω ∈ cubeSet L A f₀ := by
  rw [cubeSet, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, fun i hi => by simp [histOf, hi]⟩

lemma histOf_apply {A : Finset (Fin L)} {f₀ : Fin L → Bool} {ω : Finset (Fin L)}
    {i : Fin L} (hi : i ∈ A) : histOf A f₀ ω i = decide (i ∈ ω) := by
  simp [histOf, hi]

lemma histOf_inj {A : Finset (Fin L)} {f₀ : Fin L → Bool} {ω ω' : Finset (Fin L)}
    (hω : ω ⊆ A) (hω' : ω' ⊆ A) (h : histOf A f₀ ω = histOf A f₀ ω') : ω = ω' := by
  ext i
  by_cases hi : i ∈ A
  · have h1 : decide (i ∈ ω) = decide (i ∈ ω') := by
      simpa [histOf, hi] using congrFun h i
    constructor
    · intro hmem
      have h2 : decide (i ∈ ω') = true := by rw [← h1]; exact decide_eq_true hmem
      exact of_decide_eq_true h2
    · intro hmem
      have h2 : decide (i ∈ ω) = true := by rw [h1]; exact decide_eq_true hmem
      exact of_decide_eq_true h2
  · exact ⟨fun h1 => absurd (hω h1) hi, fun h1 => absurd (hω' h1) hi⟩

lemma histOf_eq_zero_iff {A : Finset (Fin L)} {f₀ : Fin L → Bool}
    (h0 : ∀ i ∈ A, f₀ i = false) {ω : Finset (Fin L)} (hω : ω ⊆ A) :
    histOf A f₀ ω = f₀ ↔ ω = ∅ := by
  constructor
  · intro h
    have hmem : ∀ i, i ∉ ω := by
      intro i hi
      have hiA : i ∈ A := hω hi
      have h1 : decide (i ∈ ω) = f₀ i := by
        simpa [histOf, hiA] using congrFun h i
      have h2 : decide (i ∈ ω) = true := decide_eq_true hi
      rw [h2] at h1
      have h3 : f₀ i = false := h0 i hiA
      rw [h3] at h1
      exact Bool.noConfusion h1
    ext i
    simp [hmem i]
  · intro h
    rw [h]
    funext i
    by_cases hi : i ∈ A
    · simp [histOf, hi, h0 i hi]
    · simp [histOf, hi]

lemma subSum_eq_atomSum (A : Finset (Fin L)) (atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ)
    {f₀ : Fin L → Bool} (ω : Finset (Fin L)) :
    atomSum A atoms (histOf A f₀ ω) = subSum A atoms ω := by
  rw [atomSum, subSum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h : histOf A f₀ ω s.1 = decide (s.1 ∈ ω) := by simp [histOf, s.2]
  rw [h]
  by_cases hmem : s.1 ∈ ω <;> simp [hmem]

lemma subSum_sub {A : Finset (Fin L)} {atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ}
    {ω ω' : Finset (Fin L)} (h : ω' ⊆ ω) :
    subSum A atoms ω - subSum A atoms ω' = subSum A atoms (ω \ ω') := by
  rw [subSum, subSum, subSum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h1 : s.1 ∈ ω'
  · have h2 : s.1 ∈ ω := h h1
    have h3 : s.1 ∉ ω \ ω' := fun hc => (Finset.mem_sdiff.mp hc).2 h1
    simp [h1, h2, h3]
  · by_cases h2 : s.1 ∈ ω
    · have h3 : s.1 ∈ ω \ ω' := Finset.mem_sdiff.mpr ⟨h2, h1⟩
      simp [h1, h2, h3]
    · have h3 : s.1 ∉ ω \ ω' := fun hc => h2 (Finset.mem_sdiff.mp hc).1
      simp [h1, h2, h3]

lemma slotHist_snoc {L r : ℕ} (h₀ : Fin L → Bool) (w : Fin r → Bool) (ε : Bool) :
    slotHist h₀ (r + 1) (Fin.snoc w ε) = Fin.snoc (slotHist h₀ r w) ε := by
  simp only [slotHist, Fin.init_snoc, Fin.snoc_last]

lemma slotHist_castAdd {L r : ℕ} (h₀ : Fin L → Bool) (w : Fin r → Bool) (i : Fin L) :
    slotHist h₀ r w (Fin.castAdd r i) = h₀ i := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [slotHist, Fin.snoc_castAdd]
    exact ih (Fin.init w)

/-! ## The invariant of the round -/

/-- The atom sum `subSum A atoms ω`, renamed into the parameter ring of a state with `r` new
parameters. -/
def liftSub {L : ℕ} (A : Finset (Fin L)) (atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ)
    (r : ℕ) (ω : Finset (Fin L)) : MvPolynomial (Fin (L + r)) ℤ :=
  MvPolynomial.rename (Fin.castLE (Nat.le_add_right L r)) (subSum A atoms ω)

/-- **The invariant of one round of Peluse's Lemma 4.8.**  `K` is the set of *alive classes*
(nonempty subsets of `A`, described by their histories `histOf A f₀ ω`), `σ j` is the "shift" of the
classes at time `j` (the shift is the atom sum of the class killed at the last class-reduction step
before time `j`; `σ 0 = ∅`).  The live slots of degree `D` are exactly the slots
`slotHist (histOf A f₀ ω) r w` with `ω ∈ K`, their leading coefficients are
`subSum ω - subSum (σ r)`, and the degree-`(D-1)` coefficients of the surviving class `A` satisfy the
ε-recursion of the round. -/
structure LevInv (d D : ℕ) (A : Finset (Fin L)) (f₀ : Fin L → Bool)
    (atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ)
    (r : ℕ) (K : Finset (Finset (Fin L))) (σ : Fin (r + 1) → Finset (Fin L))
    (X : HistData d (L + r)) : Prop where
  subK : ∀ ω ∈ K, ω ⊆ A
  nonemptyK : ∀ ω ∈ K, ω.Nonempty
  memA : A ∈ K
  sigma_zero : σ 0 = ∅
  sigma_sub : ∀ j, σ j ⊆ A
  sigma_ne : ∀ j, σ j ≠ A
  degLe : ∀ x ∈ X.H, (X.Q x.1 x.2).natDegree ≤ D
  top_mem : ∀ ω ∈ K, ∀ w : Fin r → Bool,
    ((Sum.inr 0 : InitIdx d), slotHist (histOf A f₀ ω) r w) ∈ X.H ∧
    (X.Q (Sum.inr 0) (slotHist (histOf A f₀ ω) r w)).natDegree = D ∧
    (X.Q (Sum.inr 0) (slotHist (histOf A f₀ ω) r w)).leadingCoeff
      = liftSub A atoms r ω - liftSub A atoms r (σ (Fin.last r))
  top_only : ∀ x ∈ X.H, D ≤ (X.Q x.1 x.2).natDegree →
    x.1 = (Sum.inr 0 : InitIdx d) ∧ ∃ ω ∈ K, ∃ w : Fin r → Bool,
      x.2 = slotHist (histOf A f₀ ω) r w
  coeff_diff : ∀ w : Fin r → Bool,
    (X.Q (Sum.inr 0) (slotHist (histOf A f₀ A) r w)).coeff (D - 1)
      - (X.Q (Sum.inr 0) (slotHist (histOf A f₀ A) r 0)).coeff (D - 1)
    = ∑ j : Fin r, D • ((liftSub A atoms r A - liftSub A atoms r (σ (Fin.castSucc j)))
        * MvPolynomial.X (Fin.natAdd L j)
        * (if w j then (1 : MvPolynomial (Fin (L + r)) ℤ) else 0))

end

end Work.Peluse.UControl
