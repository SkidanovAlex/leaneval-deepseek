import Mathlib
import Submission.Mostow.GapADefs
import Submission.Work.Mostow.Margulis.engel_frobenius_orthogonal

/-! Guidance from the project lead (the requester):

# orthFrobenius (lead): near-identity elements of a FINITE group of linear isometries commute (Frobenius/Jordan step).
# Pure linear algebra on E m; no hyperbolic geometry. rotN R = operator norm of (R - id) (GeodDefs).
1. Commutator contraction: for orthogonal A, B: ‖[A,B] − 1‖ = ‖(A−1)(B−1) − (B−1)(A−1)‖ ≤ 2‖A−1‖‖B−1‖
   (A⁻¹, B⁻¹ have norm 1). Also ‖[A,B]‖... all in the group, all orthogonal.
2. b₀ := b, b_{k+1} := [a, b_k] ∈ F. ‖b_{k+1} − 1‖ ≤ 2·(1/4)·‖b_k − 1‖ = ½‖b_k − 1‖ → 0. F finite ⇒ the positive values
   ‖f − 1‖ (f ∈ F, f ≠ 1) have a positive minimum ⇒ b_N = 1 for some N.
3. Frobenius lemma: if A orthogonal with ‖A − 1‖ ≤ 1/4 and A commutes with [A, B] (B orthogonal), then A commutes with B.
   ...
4. Backward induction from b_N = 1 with step 3 gives [a, b] = 1.
   Never use `λ` as a variable name.

## How the proof below is organised

The step 3 used below is the *repaired* Frobenius lemma
`Work.Mostow.Margulis.engel_frobenius_orthogonal` (already in the workspace): if `A`, `B` are linear
isometries of a finite-dimensional real inner product space with `‖A - 1‖, ‖B - 1‖ ≤ 1/2` and `A`
commutes with the commutator `A B A⁻¹ B⁻¹`, then `A B = B A`.  (Both elements must be close to `1`;
with only `A` close to `1` the statement is false — a rotation by a small angle and a reflection in
the dihedral group give `A B A⁻¹ B⁻¹ = A²`, which commutes with `A`, while `A B ≠ B A`.)  In the
descent all the `b_k` satisfy `rotN b_k ≤ 1/4`, so the extra hypothesis is available.

* `orth_rotN_commutator_le`: `rotN (A B A⁻¹ B⁻¹) ≤ 2 rotN A rotN B` (step 1), proved at the level of
  continuous linear maps, using `‖A⁻¹‖ = ‖B⁻¹‖ = 1`.
* `orth_exists_min_rotN`: finiteness of `F` gives a positive minimum of `rotN` on `F \ {1}` (step 2).
* `orth_seqC`: the iterated commutator sequence `b_0 = b`, `b_{k+1} = [a, b_k]`, contracting by `1/2`.
* the final descent applies the Engel–Frobenius lemma to the pair `(a, b_{k-1})`.
-/

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

set_option linter.style.haveILetI false

namespace Work.Mostow

noncomputable section

variable {m : ℕ}

/-- The coercion of a product of linear isometries to continuous linear maps is the product of the
coercions. -/
lemma orth_coe_mul_clm (S T : E m ≃ₗᵢ[ℝ] E m) :
    ((S * T : E m ≃ₗᵢ[ℝ] E m) : E m →L[ℝ] E m)
      = (S : E m →L[ℝ] E m) * (T : E m →L[ℝ] E m) := by
  ext x; rfl

/-- `rotN` is exactly the operator norm of `R - 1` (definitional). -/
lemma orth_rotN_eq (R : E m ≃ₗᵢ[ℝ] E m) : rotN R = ‖(R : E m →L[ℝ] E m) - 1‖ := rfl

/-- A linear isometry at `rotN`-distance `0` from the identity is the identity. -/
lemma orth_eq_one_of_rotN_eq_zero (R : E m ≃ₗᵢ[ℝ] E m) (h : rotN R = 0) : R = 1 := by
  have h2 : (R : E m →L[ℝ] E m) - 1 = 0 := norm_eq_zero.mp h
  have h3 : (R : E m →L[ℝ] E m) = 1 := sub_eq_zero.mp h2
  refine LinearIsometryEquiv.ext fun x => ?_
  have h4 : (R : E m →L[ℝ] E m) x = (1 : E m →L[ℝ] E m) x := by rw [h3]
  simpa using h4

/-- `rotN` is strictly positive away from the identity. -/
lemma orth_rotN_pos_of_ne_one (R : E m ≃ₗᵢ[ℝ] E m) (h : R ≠ 1) : 0 < rotN R := by
  have h0 : (0 : ℝ) ≤ rotN R := by rw [orth_rotN_eq]; exact norm_nonneg _
  exact lt_of_le_of_ne h0 (Ne.symm (fun hz => h (orth_eq_one_of_rotN_eq_zero R hz)))

/-- The elementary expansion of the additive commutator `x y - y x` in a ring. -/
lemma orth_sub_mul_sub_comm (x y : E m →L[ℝ] E m) :
    (x - 1) * (y - 1) - (y - 1) * (x - 1) = x * y - y * x := by
  rw [sub_mul, mul_sub, one_mul, mul_one, sub_mul, mul_sub, one_mul, mul_one]
  abel

/-- If `x * xi = 1` and `y * yi = 1` then the multiplicative commutator satisfies
`x y xi yi - 1 = ((x - 1)(y - 1) - (y - 1)(x - 1)) (xi yi)`. -/
lemma orth_clm_commutator_sub_one (x y xi yi : E m →L[ℝ] E m) (hx : x * xi = 1)
    (hy : y * yi = 1) :
    x * y * xi * yi - 1 = ((x - 1) * (y - 1) - (y - 1) * (x - 1)) * (xi * yi) := by
  have hBA : (y * x) * (xi * yi) = 1 := by
    rw [mul_assoc, ← mul_assoc x xi yi, hx, one_mul, hy]
  rw [orth_sub_mul_sub_comm x y, sub_mul, hBA, mul_assoc]

/-- Contraction of the multiplicative commutator: for `x, y` in a normed ring with right inverses
`xi`, `yi` of norm at most `1`,
`‖x y xi yi - 1‖ ≤ 2 ‖x - 1‖ ‖y - 1‖`. -/
lemma orth_clm_commutator_norm_le (x y xi yi : E m →L[ℝ] E m) (hx : x * xi = 1)
    (hy : y * yi = 1) (hxi : ‖xi‖ ≤ 1) (hyi : ‖yi‖ ≤ 1) :
    ‖x * y * xi * yi - 1‖ ≤ 2 * ‖x - 1‖ * ‖y - 1‖ := by
  rw [orth_clm_commutator_sub_one x y xi yi hx hy]
  have h1 : ‖(x - 1) * (y - 1) - (y - 1) * (x - 1)‖
      ≤ ‖x - 1‖ * ‖y - 1‖ + ‖y - 1‖ * ‖x - 1‖ :=
    le_trans (norm_sub_le _ _) (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
  have h2 : ‖xi * yi‖ ≤ 1 := by
    refine le_trans (norm_mul_le _ _) ?_
    simpa using mul_le_mul hxi hyi (norm_nonneg yi) (by norm_num : (0 : ℝ) ≤ 1)
  calc ‖((x - 1) * (y - 1) - (y - 1) * (x - 1)) * (xi * yi)‖
      ≤ ‖(x - 1) * (y - 1) - (y - 1) * (x - 1)‖ * ‖xi * yi‖ := norm_mul_le _ _
    _ ≤ (‖x - 1‖ * ‖y - 1‖ + ‖y - 1‖ * ‖x - 1‖) * 1 :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = 2 * ‖x - 1‖ * ‖y - 1‖ := by ring

/-- **Commutator contraction for linear isometries**: `rotN (A B A⁻¹ B⁻¹) ≤ 2 (rotN A)(rotN B)`. -/
lemma orth_rotN_commutator_le (A B : E m ≃ₗᵢ[ℝ] E m) :
    rotN (A * B * A⁻¹ * B⁻¹) ≤ 2 * rotN A * rotN B := by
  have hA : (A : E m →L[ℝ] E m) * ((A⁻¹ : E m ≃ₗᵢ[ℝ] E m) : E m →L[ℝ] E m) = 1 := by
    rw [← orth_coe_mul_clm, mul_inv_cancel]
    rfl
  have hB : (B : E m →L[ℝ] E m) * ((B⁻¹ : E m ≃ₗᵢ[ℝ] E m) : E m →L[ℝ] E m) = 1 := by
    rw [← orth_coe_mul_clm, mul_inv_cancel]
    rfl
  have hmain := orth_clm_commutator_norm_le (A : E m →L[ℝ] E m) (B : E m →L[ℝ] E m)
    ((A⁻¹ : E m ≃ₗᵢ[ℝ] E m) : E m →L[ℝ] E m) ((B⁻¹ : E m ≃ₗᵢ[ℝ] E m) : E m →L[ℝ] E m)
    hA hB (Margulis.norm_coe_le_one _) (Margulis.norm_coe_le_one _)
  have hcoe : ((A * B * A⁻¹ * B⁻¹ : E m ≃ₗᵢ[ℝ] E m) : E m →L[ℝ] E m)
      = (A : E m →L[ℝ] E m) * (B : E m →L[ℝ] E m)
        * ((A⁻¹ : E m ≃ₗᵢ[ℝ] E m) : E m →L[ℝ] E m)
        * ((B⁻¹ : E m ≃ₗᵢ[ℝ] E m) : E m →L[ℝ] E m) := by
    rw [orth_coe_mul_clm, orth_coe_mul_clm, orth_coe_mul_clm]
  rw [orth_rotN_eq, orth_rotN_eq, orth_rotN_eq, hcoe]
  exact hmain

/-- In a group, `a * s * a⁻¹ * s⁻¹ = 1` means that `a` and `s` commute. -/
lemma orth_commute_of_mul_inv_eq_one {G : Type*} [Group G] (a s : G)
    (h : a * s * a⁻¹ * s⁻¹ = 1) : a * s = s * a := by
  have h2 : a * s * a⁻¹ = s := by
    have h3 : a * s * a⁻¹ * s⁻¹ * s = 1 * s := congrArg (fun t => t * s) h
    rw [mul_assoc (a * s * a⁻¹) s⁻¹ s, inv_mul_cancel, mul_one, one_mul] at h3
    exact h3
  calc a * s = a * s * a⁻¹ * a := by group
    _ = s * a := by rw [h2]

/-- The iterated commutator sequence `b_0 = b`, `b_{k+1} = a b_k a⁻¹ b_k⁻¹`. -/
def orth_seqC (a b : E m ≃ₗᵢ[ℝ] E m) : ℕ → E m ≃ₗᵢ[ℝ] E m
  | 0 => b
  | (k + 1) => a * orth_seqC a b k * a⁻¹ * (orth_seqC a b k)⁻¹

@[simp] lemma orth_seqC_zero (a b : E m ≃ₗᵢ[ℝ] E m) : orth_seqC a b 0 = b := rfl
@[simp] lemma orth_seqC_succ (a b : E m ≃ₗᵢ[ℝ] E m) (k : ℕ) :
    orth_seqC a b (k + 1) = a * orth_seqC a b k * a⁻¹ * (orth_seqC a b k)⁻¹ := rfl

/-- In a finite subgroup of the isometries, `rotN` has a positive minimum away from the identity:
there is `δ > 0` with `δ ≤ rotN f` for every `f ∈ F`, `f ≠ 1`. -/
lemma orth_exists_min_rotN (F : Subgroup (E m ≃ₗᵢ[ℝ] E m)) [Finite F] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : F, ((f : E m ≃ₗᵢ[ℝ] E m)) ≠ 1 →
      δ ≤ rotN (f : E m ≃ₗᵢ[ℝ] E m) := by
  classical
  by_cases hex : ∃ f : F, (f : E m ≃ₗᵢ[ℝ] E m) ≠ 1
  · obtain ⟨f0, hf0⟩ := hex
    haveI : Fintype F := Fintype.ofFinite F
    set T : Finset ℝ := (Finset.univ.filter (fun f : F => (f : E m ≃ₗᵢ[ℝ] E m) ≠ 1)).image
        (fun f : F => rotN (f : E m ≃ₗᵢ[ℝ] E m)) with hT
    have hTne : T.Nonempty :=
      ⟨rotN (f0 : E m ≃ₗᵢ[ℝ] E m),
        Finset.mem_image.mpr ⟨f0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf0⟩, rfl⟩⟩
    refine ⟨T.min' hTne, ?_, ?_⟩
    · rw [Finset.lt_min'_iff]
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨f, hf, rfl⟩
      exact orth_rotN_pos_of_ne_one _ (Finset.mem_filter.mp hf).2
    · intro f hf
      exact Finset.min'_le T _ (Finset.mem_image.mpr
        ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩, rfl⟩)
  · push Not at hex
    exact ⟨1, one_pos, fun f hf => absurd (hex f) hf⟩

/-- **Frobenius / Jordan step.** In a finite group `F` of linear isometries of `E m`, two elements
that are both within operator-norm `1/4` of the identity commute. -/
theorem orthFrobenius (m : ℕ) (F : Subgroup (E m ≃ₗᵢ[ℝ] E m)) [Finite F] :
    ∀ a ∈ F, ∀ b ∈ F, rotN a ≤ 1 / 4 → rotN b ≤ 1 / 4 → a * b = b * a := by
  intro a ha b hb ha4 hb4
  classical
  -- Step 2: a positive gap for `rotN` on `F \ {1}`.
  obtain ⟨δ, hδpos, hδ⟩ := orth_exists_min_rotN F
  -- The iterated commutators stay in `F`.
  have hmem : ∀ k : ℕ, orth_seqC a b k ∈ F := by
    intro k
    induction k with
    | zero => simpa using hb
    | succ k ih =>
      rw [orth_seqC_succ]
      exact F.mul_mem (F.mul_mem (F.mul_mem ha ih) (F.inv_mem ha)) (F.inv_mem ih)
  -- Step 1: the commutators contract by the factor `1/2` at each step.
  have hcontr : ∀ k : ℕ, rotN (orth_seqC a b k) ≤ (1 / 2 : ℝ) ^ k * rotN b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : rotN (orth_seqC a b (k + 1)) ≤ 2 * rotN a * rotN (orth_seqC a b k) := by
        rw [orth_seqC_succ]; exact orth_rotN_commutator_le a (orth_seqC a b k)
      have h2 : 2 * rotN a * rotN (orth_seqC a b k)
          ≤ (1 / 2 : ℝ) * rotN (orth_seqC a b k) := by
        have h3 : (0 : ℝ) ≤ rotN (orth_seqC a b k) := by
          rw [orth_rotN_eq]; exact norm_nonneg _
        nlinarith [ha4, h3]
      have h4 : (1 / 2 : ℝ) * rotN (orth_seqC a b k)
          ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ k * rotN b) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      have h5 : (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ k * rotN b)
          = (1 / 2 : ℝ) ^ (k + 1) * rotN b := by
        rw [pow_succ]; ring
      linarith [h1, h2, h4, h5.le, h5.ge]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / 2 : ℝ) ^ N * (1 / 4) < δ := by
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 4 * δ by linarith)
      (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨N, by nlinarith [hN]⟩
  -- The sequence reaches the identity.
  have hNseq : orth_seqC a b N = 1 := by
    by_contra hne
    have hle := hδ ⟨orth_seqC a b N, hmem N⟩ hne
    have hlt : rotN (orth_seqC a b N) < δ := by
      have h2 := hcontr N
      have h3 : (1 / 2 : ℝ) ^ N * rotN b ≤ (1 / 2 : ℝ) ^ N * (1 / 4) :=
        mul_le_mul_of_nonneg_left hb4 (by positivity)
      linarith
    linarith
  -- Step 3: Engel–Frobenius descent, one step at a time.
  have hstep : ∀ k : ℕ, 1 ≤ k → orth_seqC a b (k + 1) = 1 → orth_seqC a b k = 1 := by
    intro k hk h1
    have h1' : a * orth_seqC a b k * a⁻¹ * (orth_seqC a b k)⁻¹ = 1 := by
      have htmp := h1; rw [orth_seqC_succ] at htmp; exact htmp
    have hcomm : a * orth_seqC a b k = orth_seqC a b k * a :=
      orth_commute_of_mul_inv_eq_one a (orth_seqC a b k) h1'
    have hBk : orth_seqC a b k
        = a * orth_seqC a b (k - 1) * a⁻¹ * (orth_seqC a b (k - 1))⁻¹ := by
      have htmp := orth_seqC_succ a b (k - 1)
      rwa [Nat.sub_add_cancel hk] at htmp
    have hrotB : rotN (orth_seqC a b (k - 1)) ≤ 1 / 4 := by
      have h2 := hcontr (k - 1)
      have h3 : (1 / 2 : ℝ) ^ (k - 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have h4 : (0 : ℝ) ≤ rotN b := by rw [orth_rotN_eq]; exact norm_nonneg _
      have h5 : (1 / 2 : ℝ) ^ (k - 1) * rotN b ≤ 1 * rotN b :=
        mul_le_mul_of_nonneg_right h3 h4
      linarith
    have hEngel := Margulis.engel_frobenius_orthogonal a (orth_seqC a b (k - 1))
      (by have h := ha4; rw [orth_rotN_eq] at h; linarith)
      (by have h := hrotB; rw [orth_rotN_eq] at h; linarith)
      (by rw [← hBk]; exact hcomm)
    rw [hBk, hEngel]
    group
  -- Descend from `b_N = 1` to `b_1 = [a,b] = 1`.
  have hdesc : ∀ j : ℕ, j ≤ N - 1 → orth_seqC a b (N - j) = 1 := by
    intro j
    induction j with
    | zero => intro _; simpa using hNseq
    | succ i ih =>
      intro hi
      have hprev : orth_seqC a b (N - i) = 1 := ih (by omega)
      have hres := hstep (N - i - 1) (by omega) (by
        have hk : N - i - 1 + 1 = N - i := by omega
        rw [hk]; exact hprev)
      have heq : N - i - 1 = N - (i + 1) := by omega
      rwa [heq] at hres
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · have hb1 : b = 1 := by rw [hN0] at hNseq; simpa using hNseq
    rw [hb1, mul_one, one_mul]
  · have h1 : orth_seqC a b 1 = 1 := by
      have hkey : N - (N - 1) = 1 := by omega
      have hres := hdesc (N - 1) (by omega)
      rwa [hkey] at hres
    have h2 : a * b * a⁻¹ * b⁻¹ = 1 := by
      have htmp := h1; rw [orth_seqC_succ, orth_seqC_zero] at htmp; exact htmp
    exact orth_commute_of_mul_inv_eq_one a b h2

end

end Work.Mostow
