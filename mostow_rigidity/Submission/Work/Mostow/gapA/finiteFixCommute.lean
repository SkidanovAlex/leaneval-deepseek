import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.Margulis.engel_frobenius_orthogonal
import Submission.Work.Mostow.bieberbachDefs
import Submission.Work.Mostow.frobeniusCommute

/-!
# `finiteFixCommute`: small elements of a finite point group commute

Let `H ≤ PO n 1` be a **finite** subgroup all of whose elements fix the base point `0`, and let
`a c ∈ H` be represented in the chart by the linear isometries `A`, `C` (`a • u = A u`,
`c • u = C u`).  If `A` and `C` are within `1/4` of the identity in operator norm
(`mOf A = ‖A - 1‖ ≤ 1/4`, same for `C`), then `a` and `c` commute.

The proof is the *Engel/Frobenius* argument (`Margulis.engel_frobenius_orthogonal`): if two
isometries `A`, `B` are within `1/2` of the identity and `A` commutes with the commutator
`[A,B]`, then `A B = B A`.  Iterating the commutator construction

`E₀ = c`, `E_{i+1} = [a, E_i]`  (so `B₀ = C`, `B_{i+1} = [A, B_i]`)

gives elements `E_i ∈ H` whose matrices `B_i` satisfy `mOf B_i ≤ 2^{-(i+2)}` (Buser's
commutator estimate `mOf_commutator`).  Since `H` is finite the set `{B_i}` is finite, so it
has a positive gap at the identity and the sequence must reach `1`; then the Engel–Frobenius
lemma is applied downwards, `B_{i+2} = 1 ⇒ B_{i+1} = 1`, giving `B₁ = [A,C] = 1`, i.e.
`A C = C A`, and therefore `a c = c a`.
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## The Engel sequence and its matrices -/

/-- The Engel sequence `E₀ = c`, `E_{i+1} = a E_i a⁻¹ E_i⁻¹` inside a subgroup. -/
def engelSeq (H : Subgroup (PO n 1)) (a c : PO n 1) (ha : a ∈ H) (hc : c ∈ H) : ℕ → H :=
  fun i => Nat.rec (⟨c, hc⟩ : H)
    (fun _ e => ⟨a * (e : PO n 1) * a⁻¹ * (e : PO n 1)⁻¹,
      H.mul_mem (H.mul_mem (H.mul_mem ha e.2) (H.inv_mem ha)) (H.inv_mem e.2)⟩) i

/-- The corresponding sequence of linear parts: `B₀ = C`, `B_{i+1} = [A, B_i]`. -/
def engelMat (A C : E n ≃ₗᵢ[ℝ] E n) : ℕ → (E n ≃ₗᵢ[ℝ] E n) :=
  fun i => Nat.rec C (fun _ B => A * B * A⁻¹ * B⁻¹) i

/-! ## Elementary action facts -/

/-- The inverse of an element acts by the inverse of the matrix. -/
lemma action_inv {g : PO n 1} {B : E n ≃ₗᵢ[ℝ] E n} (hA : POActionProp n)
    (h : ∀ u : E n, g • u = B u) : ∀ u : E n, g⁻¹ • u = B⁻¹ u := by
  intro u
  have h1 : B (g⁻¹ • u) = u := by
    rw [← h (g⁻¹ • u), (hA.2.2.2.2.1 g g⁻¹ u).symm, mul_inv_cancel, hA.2.2.2.1]
  calc g⁻¹ • u = B⁻¹ (B (g⁻¹ • u)) := (B.symm_apply_apply _).symm
    _ = B⁻¹ u := by rw [h1]

/-- Products act by products of matrices. -/
lemma action_mul {g h : PO n 1} {B D : E n ≃ₗᵢ[ℝ] E n} (hA : POActionProp n)
    (hg : ∀ u : E n, g • u = B u) (hh : ∀ u : E n, h • u = D u) :
    ∀ u : E n, (g * h) • u = (B * D) u := by
  intro u
  rw [hA.2.2.2.2.1 g h u, hh u]
  exact hg (D u)

/-- The action on the chart separates points of `PO n 1`. -/
lemma eq_of_action_eq (hA : POActionProp n) {g h : PO n 1} (hgh : ∀ u : E n, g • u = h • u) :
    g = h := by
  have h2 : g * h⁻¹ = 1 := by
    apply hA.2.2.2.2.2.1
    intro u
    calc (g * h⁻¹) • u = g • (h⁻¹ • u) := hA.2.2.2.2.1 g h⁻¹ u
      _ = h • (h⁻¹ • u) := hgh (h⁻¹ • u)
      _ = (h * h⁻¹) • u := (hA.2.2.2.2.1 h h⁻¹ u).symm
      _ = (1 : PO n 1) • u := by rw [mul_inv_cancel]
      _ = u := hA.2.2.2.1 u
  calc g = g * 1 := (mul_one g).symm
    _ = g * (h⁻¹ * h) := by rw [inv_mul_cancel]
    _ = (g * h⁻¹) * h := by rw [mul_assoc]
    _ = 1 * h := by rw [h2]
    _ = h := one_mul h

/-! ## The matrices of the Engel sequence -/

/-- `E_i` acts through its matrix `B_i`. -/
lemma engelSeq_action (hA : POActionProp n) {a c : PO n 1} {A C : E n ≃ₗᵢ[ℝ] E n}
    (ha : ∀ u : E n, a • u = A u) (hc : ∀ u : E n, c • u = C u)
    (H : Subgroup (PO n 1)) (hm : a ∈ H) (hmc : c ∈ H) :
    ∀ (i : ℕ) (u : E n), ((engelSeq H a c hm hmc i : H) : PO n 1) • u = engelMat A C i u := by
  intro i
  induction i with
  | zero => intro u; exact hc u
  | succ i ih =>
    intro u
    have hstep : ((engelSeq H a c hm hmc (i+1) : H) : PO n 1)
        = ((a * ((engelSeq H a c hm hmc i : H) : PO n 1)) * a⁻¹)
            * ((engelSeq H a c hm hmc i : H) : PO n 1)⁻¹ := rfl
    rw [hstep]
    have hx := action_mul hA ha ih
    have hy := action_mul hA hx (action_inv hA ha)
    have hz := action_mul hA hy (action_inv hA ih)
    exact hz u

/-- Two equal elements of the Engel sequence have the same matrix. -/
lemma engelMat_eq_of_seq_eq (hA : POActionProp n) {a c : PO n 1} {A C : E n ≃ₗᵢ[ℝ] E n}
    (ha : ∀ u : E n, a • u = A u) (hc : ∀ u : E n, c • u = C u)
    (H : Subgroup (PO n 1)) (hm : a ∈ H) (hmc : c ∈ H) {i j : ℕ}
    (h : engelSeq H a c hm hmc i = engelSeq H a c hm hmc j) : engelMat A C i = engelMat A C j := by
  ext u
  rw [← engelSeq_action hA ha hc H hm hmc i u, ← engelSeq_action hA ha hc H hm hmc j u, h]

/-- The set of matrices of the Engel sequence is finite (it is an image of the finite group `H`). -/
lemma range_engelMat_finite (hA : POActionProp n) {a c : PO n 1} {A C : E n ≃ₗᵢ[ℝ] E n}
    (ha : ∀ u : E n, a • u = A u) (hc : ∀ u : E n, c • u = C u)
    (H : Subgroup (PO n 1)) (hm : a ∈ H) (hmc : c ∈ H) (hH : Finite H) :
    (Set.range (engelMat A C)).Finite := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  let pick : H → ℕ := fun h => if hh : ∃ i, engelSeq H a c hm hmc i = h then Nat.find hh else 0
  have hpick : ∀ h : H, (∃ i, engelSeq H a c hm hmc i = h) →
      engelSeq H a c hm hmc (pick h) = h := by
    intro h hh
    simp only [pick]
    rw [dite_eq_left hh]
    exact Nat.find_spec hh
  refine Set.Finite.subset (Finset.finite_toSet
    (Finset.univ.image (fun h : H => engelMat A C (pick h)))) ?_
  rintro x ⟨i, rfl⟩
  refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨engelSeq H a c hm hmc i, Finset.mem_univ _, ?_⟩)
  exact (engelMat_eq_of_seq_eq hA ha hc H hm hmc (hpick _ ⟨i, rfl⟩))

/-! ## The matrices shrink (Buser's commutator estimate) -/

/-- `mOf (B_i) ≤ 2^{-(i+2)}`. -/
lemma engelMat_mOf_le {A C : E n ≃ₗᵢ[ℝ] E n} (hAn : mOf A ≤ 1/4) (hCn : mOf C ≤ 1/4) :
    ∀ i : ℕ, mOf (engelMat A C i) ≤ (1/2 : ℝ) ^ (i + 2) := by
  intro i
  induction i with
  | zero =>
    have h : (1/2 : ℝ) ^ (0 + 2) = 1/4 := by norm_num
    rw [h]; exact hCn
  | succ i ih =>
    have h1 : mOf (engelMat A C (i+1)) ≤ 2 * mOf A * mOf (engelMat A C i) := by
      rw [show engelMat A C (i+1) = A * engelMat A C i * A⁻¹ * (engelMat A C i)⁻¹ from rfl]
      exact mOf_commutator A (engelMat A C i)
    have h2 : 2 * mOf A * mOf (engelMat A C i) ≤ (1/2 : ℝ) ^ (i + 3) := by
      have hle : 2 * mOf A ≤ 2 * (1/4) := by linarith
      have h2' : 2 * mOf A * mOf (engelMat A C i) ≤ (2 * (1/4)) * (1/2 : ℝ) ^ (i + 2) :=
        mul_le_mul hle ih (mOf_nonneg _) (by norm_num)
      calc 2 * mOf A * mOf (engelMat A C i) ≤ 2 * (1/4) * (1/2 : ℝ) ^ (i + 2) := by
            simpa using h2'
        _ = (1/2 : ℝ) ^ (i + 3) := by rw [pow_succ]; ring
    linarith [h1, h2]

/-! ## The Engel sequence reaches the identity -/

/-- Some term of the Engel sequence is the identity. -/
lemma exists_engelMat_eq_one (hA : POActionProp n) {a c : PO n 1} {A C : E n ≃ₗᵢ[ℝ] E n}
    (ha : ∀ u : E n, a • u = A u) (hc : ∀ u : E n, c • u = C u)
    (H : Subgroup (PO n 1)) (hm : a ∈ H) (hmc : c ∈ H) (hH : Finite H)
    (hAn : mOf A ≤ 1/4) (hCn : mOf C ≤ 1/4) : ∃ i : ℕ, engelMat A C i = 1 := by
  classical
  have hfin := range_engelMat_finite hA ha hc H hm hmc hH
  by_cases h0 : engelMat A C 0 = 1
  · exact ⟨0, h0⟩
  · have hmem : engelMat A C 0 ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]; exact ⟨0, rfl⟩
    let s : Finset (E n ≃ₗᵢ[ℝ] E n) := hfin.toFinset.filter (fun x => x ≠ 1)
    have hsne : s.Nonempty := ⟨_, Finset.mem_filter.mpr ⟨hmem, h0⟩⟩
    obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image s mOf hsne
    have hxne : x ≠ 1 := (Finset.mem_filter.mp hx).2
    have hdpos : 0 < mOf x := by
      rcases eq_or_lt_of_le (mOf_nonneg x) with h | h
      · exact absurd (mOf_eq_zero_iff.mp h.symm) hxne
      · exact h
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hdpos (by norm_num : (1:ℝ)/2 < 1)
    refine ⟨N, ?_⟩
    by_contra hBN
    have hBNmem : engelMat A C N ∈ s :=
      Finset.mem_filter.mpr ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨N, rfl⟩, hBN⟩
    have h1 : mOf x ≤ mOf (engelMat A C N) := hmin _ hBNmem
    have h2 : mOf (engelMat A C N) ≤ (1/2 : ℝ) ^ (N + 2) := engelMat_mOf_le hAn hCn N
    have h3 : (1/2 : ℝ) ^ (N + 2) ≤ (1/2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith

/-! ## The Engel–Frobenius descent -/

/-- **The one-step descent.**  If `B_{i+2} = 1` then `B_{i+1} = 1`, because `B_{i+1} = 1` says
that `A` commutes with `[A, B_i]` and both `A` and `B_i` are within `1/2` of the identity. -/
lemma engelMat_step {A C : E n ≃ₗᵢ[ℝ] E n} (hAn : mOf A ≤ 1/4) (hCn : mOf C ≤ 1/4) :
    ∀ i : ℕ, engelMat A C (i + 2) = 1 → engelMat A C (i + 1) = 1 := by
  intro i h
  have hBi : mOf (engelMat A C i) ≤ 1/2 := by
    have h1 := engelMat_mOf_le hAn hCn i
    have h2 : (1/2 : ℝ) ^ (i + 2) ≤ 1/2 := by
      have h3 : (1/2 : ℝ) ^ (i + 2) ≤ (1/2 : ℝ) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 ≤ 1)
          (by omega)
      rwa [pow_one] at h3
    linarith
  have hA1 : ‖(A : E n →L[ℝ] E n) - 1‖ ≤ (1:ℝ)/2 := by
    have h : ‖(A : E n →L[ℝ] E n) - 1‖ = mOf A := rfl
    rw [h]; linarith
  have hB1 : ‖(engelMat A C i : E n →L[ℝ] E n) - 1‖ ≤ (1:ℝ)/2 := by
    have h : ‖(engelMat A C i : E n →L[ℝ] E n) - 1‖ = mOf (engelMat A C i) := rfl
    rw [h]; exact hBi
  have hcomm : A * (A * engelMat A C i * A⁻¹ * (engelMat A C i)⁻¹)
      = (A * engelMat A C i * A⁻¹ * (engelMat A C i)⁻¹) * A := by
    have h1 : A * engelMat A C (i+1) = engelMat A C (i+1) * A := by
      have h2 : A * engelMat A C (i+1) * A⁻¹ * (engelMat A C (i+1))⁻¹ = 1 := by
        rw [show A * engelMat A C (i+1) * A⁻¹ * (engelMat A C (i+1))⁻¹
            = engelMat A C (i+2) from rfl]
        exact h
      calc A * engelMat A C (i+1)
          = (A * engelMat A C (i+1) * A⁻¹ * (engelMat A C (i+1))⁻¹)
              * (engelMat A C (i+1) * A) := by group
        _ = 1 * (engelMat A C (i+1) * A) := by rw [h2]
        _ = engelMat A C (i+1) * A := one_mul _
    have h2 : engelMat A C (i+1) = A * engelMat A C i * A⁻¹ * (engelMat A C i)⁻¹ := rfl
    rw [← h2]; exact h1
  have hEF := Margulis.engel_frobenius_orthogonal A (engelMat A C i) hA1 hB1 hcomm
  rw [show engelMat A C (i+1) = A * engelMat A C i * A⁻¹ * (engelMat A C i)⁻¹ from rfl, hEF]
  group

/-! ## The main theorem -/

theorem finiteFixCommute (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (H : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hH : Finite H)
    (h0 : ∀ h ∈ H, h • (0 : Submission.Mostow.E n) = 0)
    (a c : LeanEval.Geometry.MostowRigidity.PO n 1) (haH : a ∈ H) (hcH : c ∈ H)
    (A C : Submission.Mostow.E n ≃ₗᵢ[ℝ] Submission.Mostow.E n)
    (hAact : ∀ u : Submission.Mostow.E n, a • u = A u)
    (hCact : ∀ u : Submission.Mostow.E n, c • u = C u)
    (hAn : Work.Mostow.mOf A ≤ 1/4) (hCn : Work.Mostow.mOf C ≤ 1/4) :
    a * c = c * a := by
  classical
  have hex : ∃ i : ℕ, engelMat A C i = 1 :=
    exists_engelMat_eq_one hA hAact hCact H haH hcH hH hAn hCn
  have hB1 : engelMat A C 1 = 1 := by
    let i₀ := Nat.find hex
    have hi₀ : engelMat A C i₀ = 1 := Nat.find_spec hex
    have hmin : ∀ j : ℕ, j < i₀ → engelMat A C j ≠ 1 := fun j hj => Nat.find_min hex hj
    rcases Nat.eq_zero_or_pos i₀ with h | h
    · have hC0 : engelMat A C 0 = 1 := h ▸ hi₀
      have hC1 : C = 1 := hC0
      rw [show engelMat A C 1 = A * C * A⁻¹ * C⁻¹ from rfl, hC1]; group
    · rcases eq_or_lt_of_le (show 1 ≤ i₀ from h) with h1 | h2
      · exact h1.symm ▸ hi₀
      · obtain ⟨j, hj⟩ : ∃ j, i₀ = j + 2 := ⟨i₀ - 2, by omega⟩
        exact absurd (engelMat_step hAn hCn j (hj ▸ hi₀)) (hmin (j+1) (by omega))
  have hAC : A * C = C * A := by
    have h1 : A * C * A⁻¹ * C⁻¹ = 1 := hB1
    calc A * C = (A * C * A⁻¹ * C⁻¹) * (C * A) := by group
      _ = 1 * (C * A) := by rw [h1]
      _ = C * A := one_mul _
  exact eq_of_action_eq hA (fun u => by
    rw [action_mul hA hAact hCact u, action_mul hA hCact hAact u, hAC])

end

end Work.Mostow.gapA
