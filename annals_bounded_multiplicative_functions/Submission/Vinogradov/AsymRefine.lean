/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.AsymBilinear
import Submission.Vinogradov.SymFromAsym

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Refining a level-`m` block: GLYZ Lemma 3.8 and Lemma 3.9

GLYZ (arXiv:1912.09798) §3.4 introduces the *lower degree decoupling* step.  Lemma 3.8 says
that the left hand side of the asymmetric bilinear inequality (3.1) at the coarse pair of levels
`(a, b)` is bounded by the `ℓ²`-sum, over the *finer* level `b' = (k-l+1)b/l` on the `I`-side, of
the same bilinear expressions at `(b', b)`.  Lemma 3.9 then converts this into the purely
"asymmetric-to-asymmetric" statement

  `B_{l,a,b}(δ) ≲ δ^{-bε} B_{l,(k-l+1)b/l,b}(δ)`   for `a ≤ (k-l+1)b/l`.

This module implements the **level bookkeeping and the mechanical conversion** (Lemma 3.9);
the analytic content (Lemma 3.8) is the hypothesis `AsymDecFine`.

* `subBlkLvl m m'' q` — the level-`m''` blocks inside the level-`m` block `q`;
* `biUnion_subBlkLvl`, `sum_subBlkLvl` — they partition `q`, so sums over `q` split into sums
  over the refinement (this is what makes the `ℓ²`-telescoping work);
* `sepLevel_of_subBlkLvl` — the separation condition `dist(I,I') ≥ 1/4` is inherited by the
  refinement (a sub-interval is at least as far from `I'` as its parent);
* `refLvl l k m'` — the finer level `b' = (k-l+1)b/l` in integer form (a floor);
* `asymLHS`, `AsymDecFine` — the statement of (3.10) in dyadic form;
* **`asymDec_of_fine`** — Lemma 3.9: `AsymDec` at the refined level implies `AsymDec` at the
  coarse level, with the constant `C₁ · C₂^{p_l/p_k}`.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-! ## 1. The level-`m''` blocks inside a level-`m` block -/

/-- The level-`m''` blocks contained in the level-`m` block `q`. -/
def subBlkLvl (m m'' : ℕ) (q : Fin (2 ^ m)) : Finset (Fin (2 ^ m'')) :=
  Finset.univ.filter (fun q'' : Fin (2 ^ m'') => (q'' : ℕ) / 2 ^ (m'' - m) = (q : ℕ))

lemma mem_subBlkLvl {m m'' : ℕ} {q : Fin (2 ^ m)} {q'' : Fin (2 ^ m'')} :
    q'' ∈ subBlkLvl m m'' q ↔ (q'' : ℕ) / 2 ^ (m'' - m) = (q : ℕ) := by
  simp [subBlkLvl]

/-- The index arithmetic of the refinement: dividing by the finer power first. -/
lemma div_pow_sub {N m m'' : ℕ} (hm : m ≤ m'') (hmN : m'' ≤ N) (i : ℕ) :
    i / 2 ^ (N - m) = i / 2 ^ (N - m'') / 2 ^ (m'' - m) := by
  have h : N - m'' + (m'' - m) = N - m := by omega
  rw [Nat.div_div_eq_div_mul, ← pow_add, h]

lemma subBlkLvl_disjoint {N m'' : ℕ} (hmN : m'' ≤ N) {a b : Fin (2 ^ m'')} (h : a ≠ b) :
    Disjoint (blkFin N m'' a) (blkFin N m'' b) := by
  rw [Finset.disjoint_iff_ne]
  intro i hi i' hi' heq
  exact h (Fin.ext (by rw [← mem_blkFin.mp hi, ← mem_blkFin.mp hi', heq]))

lemma pairwiseDisjoint_subBlkLvl {N m m'' : ℕ} (hmN : m'' ≤ N) (q : Fin (2 ^ m)) :
    (subBlkLvl m m'' q : Set (Fin (2 ^ m''))).PairwiseDisjoint (fun q'' => blkFin N m'' q'') :=
  fun a _ b _ hne => subBlkLvl_disjoint hmN hne

theorem biUnion_subBlkLvl {N m m'' : ℕ} (hm : m ≤ m'') (hmN : m'' ≤ N) (q : Fin (2 ^ m)) :
    (subBlkLvl m m'' q).biUnion (fun q'' => blkFin N m'' q'') = blkFin N m q := by
  ext i
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨q'', hq'', hi⟩
    rw [mem_blkFin] at hi ⊢
    rw [div_pow_sub hm hmN, hi, mem_subBlkLvl.mp hq'']
  · intro hi
    rw [mem_blkFin] at hi
    have hlt : (i : ℕ) / 2 ^ (N - m'') < 2 ^ m'' := by
      have h1 : (i : ℕ) < 2 ^ (N - m'') * 2 ^ m'' := by
        rw [← pow_add, show N - m'' + m'' = N from by omega]
        exact i.isLt
      exact Nat.div_lt_of_lt_mul h1
    refine ⟨⟨(i : ℕ) / 2 ^ (N - m''), hlt⟩, ?_, ?_⟩
    · rw [mem_subBlkLvl]
      show (i : ℕ) / 2 ^ (N - m'') / 2 ^ (m'' - m) = (q : ℕ)
      rw [← div_pow_sub hm hmN]
      exact hi
    · rw [mem_blkFin]

/-- **The refinement of a block**: sums over a level-`m` block split into sums over the
level-`m''` blocks it contains. -/
theorem sum_subBlkLvl {N m m'' : ℕ} (hm : m ≤ m'') (hmN : m'' ≤ N) (q : Fin (2 ^ m))
    {α : Type*} [AddCommMonoid α] (G : Fin (2 ^ N) → α) :
    ∑ i ∈ blkFin N m q, G i
      = ∑ q'' ∈ subBlkLvl m m'' q, ∑ i ∈ blkFin N m'' q'', G i := by
  rw [← Finset.sum_biUnion (pairwiseDisjoint_subBlkLvl hmN q),
    biUnion_subBlkLvl hm hmN q]

/-! ## 2. The separation condition is inherited by the refinement -/

/-- The right endpoint of the `j`-th piece of the `2^m`-fold partition. -/
lemma pieceCenter_add_plateHalf (m : ℕ) (q : Fin (2 ^ m)) :
    pieceCenter (2 ^ m) q + plateHalf m = (((q : ℕ) : ℝ) + 1) / (2 : ℝ) ^ m := by
  rw [pieceCenter, plateHalf, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
  field_simp
  ring

/-- The left endpoint of the `j`-th piece of the `2^m`-fold partition. -/
lemma pieceCenter_sub_plateHalf (m : ℕ) (q : Fin (2 ^ m)) :
    pieceCenter (2 ^ m) q - plateHalf m = ((q : ℕ) : ℝ) / (2 : ℝ) ^ m := by
  rw [pieceCenter, plateHalf, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
  field_simp
  ring

/-- The centre of a refined block stays within the parent block. -/
lemma abs_pieceCenter_subBlkLvl_sub_le {m m'' : ℕ} (hm : m ≤ m'') {q : Fin (2 ^ m)}
    {q'' : Fin (2 ^ m'')} (hq : q'' ∈ subBlkLvl m m'' q) :
    |pieceCenter (2 ^ m'') q'' - pieceCenter (2 ^ m) q|
      ≤ plateHalf m - plateHalf m'' := by
  set d : ℕ := m'' - m with hddef
  have hpow : (2 : ℝ) ^ m'' = (2 : ℝ) ^ m * (2 : ℝ) ^ d := by
    rw [← pow_add]; congr 1; simp only [hddef]; omega
  have hP0 : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hP1 : (0 : ℝ) < (2 : ℝ) ^ m'' := by positivity
  have hdiv : (q'' : ℕ) / 2 ^ d = (q : ℕ) := by
    rw [hddef]; exact mem_subBlkLvl.mp hq
  have hdecomp : (q'' : ℕ) = (q : ℕ) * 2 ^ d + (q'' : ℕ) % 2 ^ d := by
    have h := Nat.div_add_mod (q'' : ℕ) (2 ^ d)
    rw [hdiv, Nat.mul_comm (2 ^ d) (q : ℕ)] at h
    exact h.symm
  have hj1 : (q'' : ℕ) % 2 ^ d + 1 ≤ 2 ^ d := by
    have h := Nat.mod_lt (q'' : ℕ) (pow_pos (by norm_num : (0:ℕ) < 2) d)
    omega
  -- the two endpoint comparisons
  have hA : pieceCenter (2 ^ m) q - plateHalf m ≤ pieceCenter (2 ^ m'') q'' - plateHalf m'' := by
    rw [pieceCenter_sub_plateHalf, pieceCenter_sub_plateHalf]
    rw [div_le_div_iff₀ hP0 hP1]
    have hcast : ((q : ℕ) : ℝ) * (2 : ℝ) ^ m'' ≤ ((q'' : ℕ) : ℝ) * (2 : ℝ) ^ m := by
      rw [hpow, hdecomp]
      push_cast
      have hj0 : (0 : ℝ) ≤ (((q'' : ℕ) % 2 ^ d : ℕ) : ℝ) := by positivity
      nlinarith [sq_nonneg (((q : ℕ) : ℝ) * (2 : ℝ) ^ m * (2 : ℝ) ^ d)]
    linarith [hcast]
  have hB : pieceCenter (2 ^ m'') q'' + plateHalf m'' ≤ pieceCenter (2 ^ m) q + plateHalf m := by
    rw [pieceCenter_add_plateHalf, pieceCenter_add_plateHalf]
    rw [div_le_div_iff₀ hP1 hP0]
    have hcast : (((q'' : ℕ) : ℝ) + 1) * (2 : ℝ) ^ m ≤ (((q : ℕ) : ℝ) + 1) * (2 : ℝ) ^ m'' := by
      rw [hpow, hdecomp]
      push_cast
      have hj : (((q'' : ℕ) % 2 ^ d : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ d := by
        have := hj1
        exact_mod_cast this
      nlinarith [mul_nonneg (le_of_lt hP0) (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) d)]
    linarith [hcast]
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- **The separation condition is inherited by the refinement.** -/
lemma sepLevel_of_subBlkLvl {m m' m'' : ℕ} {q : Fin (2 ^ m)} {q'' : Fin (2 ^ m'')}
    {q' : Fin (2 ^ m')} (hm : m ≤ m'') (hq'' : q'' ∈ subBlkLvl m m'' q)
    (hsep : sepLevel m m' q q') : sepLevel m'' m' q'' q' := by
  have h1 := abs_pieceCenter_subBlkLvl_sub_le (m'' := m'') hm hq''
  have h4 : |pieceCenter (2 ^ m'') q'' - pieceCenter (2 ^ m') q'|
      ≥ |pieceCenter (2 ^ m) q - pieceCenter (2 ^ m') q'|
        - |pieceCenter (2 ^ m'') q'' - pieceCenter (2 ^ m) q| := by
    have h5 : |pieceCenter (2 ^ m) q - pieceCenter (2 ^ m') q'|
        ≤ |pieceCenter (2 ^ m) q - pieceCenter (2 ^ m'') q''|
          + |pieceCenter (2 ^ m'') q'' - pieceCenter (2 ^ m') q'| := abs_sub_le _ _ _
    rw [abs_sub_comm (pieceCenter (2 ^ m) q) (pieceCenter (2 ^ m'') q'')] at h5
    linarith
  simp only [sepLevel, plateHalf] at *
  linarith

/-! ## 3. The refined level `b' = (k-l+1)b/l` -/

/-- The finer level `b' = (k-l+1)b/l` in integer form (a floor):  the refinement of the
`I`-side used by GLYZ Lemma 3.8. -/
def refLvl (l k m' : ℕ) : ℕ := ((k - l + 1) * m') / l

/-- The left hand side of the asymmetric bilinear inequality (3.1) at the pair of levels
`(m, m')`. -/
noncomputable def asymLHS (k : ℕ) (hk : 1 ≤ k) (l N m m' : ℕ) (q : Fin (2 ^ m))
    (q' : Fin (2 ^ m')) (f : Fin (2 ^ N) → E k → ℂ) : ℝ≥0∞ :=
  ∫⁻ x, convPow k (plExp l) (fun x => ∑ i ∈ blkFin N m q, f i x)
        (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)) x
      * convPow k (pkExp k - plExp l) (fun x => ∑ i ∈ blkFin N m' q', f i x)
        (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x

lemma asymDec_iff (k : ℕ) (hk : 1 ≤ k) (l N m m' : ℕ) (C : ℝ≥0∞) :
    AsymDec k hk l N m m' C ↔
      ∀ (q : Fin (2 ^ m)) (q' : Fin (2 ^ m')), sepLevel m m' q q' →
      ∀ f : Fin (2 ^ N) → E k → ℂ,
        (∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) →
        asymLHS k hk l N m m' q q' f ≤ C ^ (pkExp k)
          * (l2Of (blkFin N m q) (fun i => lpNorm k (pE k) (f i))) ^ (plExp l)
          * (l2Of (blkFin N m' q') (fun i => lpNorm k (pE k) (f i))) ^ (pkExp k - plExp l) :=
  Iff.rfl

/-- **GLYZ (3.10) (Lemma 3.8) in dyadic form**: the bilinear expression at the coarse level `m`
is bounded by the `ℓ²`-sum, over the refined level `refLvl l k m'`, of the bilinear expressions
at that level (the `I'`-side stays at level `m'`). -/
def AsymDecFine (k : ℕ) (hk : 1 ≤ k) (l N m m' : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ (q : Fin (2 ^ m)) (q' : Fin (2 ^ m')), sepLevel m m' q q' →
  ∀ f : Fin (2 ^ N) → E k → ℂ,
    (∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) →
    asymLHS k hk l N m m' q q' f ≤ C ^ (plExp l)
      * (∑ q'' ∈ subBlkLvl m (refLvl l k m') q,
          (asymLHS k hk l N (refLvl l k m') m' q'' q' f) ^ (2 / plExp l)) ^ (plExp l / 2)

lemma plExp_pos {l : ℕ} (hl : 1 ≤ l) : 0 < plExp l := by
  rw [plExp]; positivity

/-! ## 4. The `ℓ²` bookkeeping lemmas -/

lemma rpow_mul_rpow {x : ℝ≥0∞} {a b : ℝ} : (x ^ a) ^ b = x ^ (a * b) :=
  (ENNReal.rpow_mul x a b).symm

/-- Reordering the product of powers with an exponent. -/
lemma mul_rpow_three (a b c : ℝ≥0∞) {r : ℝ} (hr : 0 ≤ r) :
    (a * b * c) ^ r = a ^ r * b ^ r * c ^ r := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ hr, ENNReal.mul_rpow_of_nonneg _ _ hr]

/-- **GLYZ Lemma 3.9** (the mechanical step): the asymmetric bilinear inequality at the coarse
level `a ≤ (k-l+1)b/l` follows from the one at the refined level `(k-l+1)b/l`, at the price of
the constant factor `C₂^{p_l/p_k}`. -/
theorem asymDec_of_fine {k l N m m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k - 1)
    (hm : m ≤ refLvl l k m') (href : refLvl l k m' ≤ N)
    {C₁ C₂ : ℝ≥0∞}
    (hbig : AsymDec k hk l N (refLvl l k m') m' C₁)
    (hfine : AsymDecFine k hk l N m m' C₂) :
    AsymDec k hk l N m m' (C₁ * C₂ ^ (plExp l / pkExp k)) := by
  rw [asymDec_iff] at hbig ⊢
  intro q q' hsep f hf
  set M : ℕ := refLvl l k m' with hM
  set T : Finset (Fin (2 ^ M)) := subBlkLvl m M q with hT
  set A : Fin (2 ^ N) → ℝ≥0∞ := fun i => lpNorm k (pE k) (f i) with hAdef
  set Y : Fin (2 ^ M) → ℝ≥0∞ := fun q'' => l2Of (blkFin N M q'') A with hY
  set B : ℝ≥0∞ := (l2Of (blkFin N m' q') A) ^ (pkExp k - plExp l) with hBdef
  have hpl : 0 < plExp l := plExp_pos hl
  have hpk : 0 < pkExp k := by rw [pkExp]; positivity
  have h2pl : 0 < 2 / plExp l := by positivity
  have hhalf : 0 < plExp l / 2 := by positivity
  -- Step 1: the refined bound, summed
  have hstep : ∑ q'' ∈ T, (asymLHS k hk l N M m' q'' q' f) ^ (2 / plExp l)
      ≤ ∑ q'' ∈ T, (C₁ ^ (pkExp k) * (Y q'') ^ (plExp l) * B) ^ (2 / plExp l) := by
    refine Finset.sum_le_sum (fun q'' hq'' => ?_)
    have hsep' : sepLevel M m' q'' q' :=
      sepLevel_of_subBlkLvl (m := m) (m'' := M) hm hq'' hsep
    have h := hbig q'' q' hsep' f hf
    have h' : asymLHS k hk l N M m' q'' q' f
        ≤ C₁ ^ (pkExp k) * (Y q'') ^ (plExp l) * B := by
      simpa only [Y, B, hAdef, hM] using h
    exact ENNReal.rpow_le_rpow h' h2pl.le
  -- Step 2: expand each summand
  have hexp : ∀ a b c : ℝ≥0∞, 0 ≤ (2 / plExp l) →
      (a * b * c) ^ (2 / plExp l) = a ^ (2 / plExp l) * b ^ (2 / plExp l) * c ^ (2 / plExp l) :=
    fun a b c hr => mul_rpow_three a b c hr
  have hY2 : ∀ q'' : Fin (2 ^ M), ((Y q'') ^ (plExp l)) ^ (2 / plExp l) = (Y q'') ^ (2 : ℝ) := by
    intro q''
    rw [rpow_mul_rpow]
    congr 1
    field_simp
  have hC1 : ((C₁ ^ (pkExp k)) ^ (2 / plExp l)) = C₁ ^ (pkExp k * (2 / plExp l)) :=
    rpow_mul_rpow
  have hsum2 : ∑ q'' ∈ T, (C₁ ^ (pkExp k) * (Y q'') ^ (plExp l) * B) ^ (2 / plExp l)
      = C₁ ^ (pkExp k * (2 / plExp l)) * B ^ (2 / plExp l) * ∑ q'' ∈ T, (Y q'') ^ (2 : ℝ) := by
    rw [Finset.sum_congr rfl (fun q'' _ => by
      rw [mul_rpow_three _ _ _ h2pl.le, hY2 q'', hC1])]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  -- Step 3: the `ℓ²` telescoping
  have htel : ∑ q'' ∈ T, (Y q'') ^ (2 : ℝ) = sqSum (blkFin N m q) A := by
    have h1 : ∀ q'' : Fin (2 ^ M), (Y q'') ^ (2 : ℝ) = sqSum (blkFin N M q'') A := by
      intro q''
      rw [hY]; exact l2Of_sq _ _
    rw [Finset.sum_congr rfl (fun q'' _ => h1 q'')]
    simp only [sqSum]
    exact (sum_subBlkLvl hm href q (fun i => A i ^ (2 : ℝ))).symm
  -- Step 4: assemble
  have hfinal : (∑ q'' ∈ T, (asymLHS k hk l N M m' q'' q' f) ^ (2 / plExp l)) ^ (plExp l / 2)
      ≤ C₁ ^ (pkExp k) * (l2Of (blkFin N m q) A) ^ (plExp l) * B := by
    refine le_trans (ENNReal.rpow_le_rpow hstep hhalf.le) ?_
    rw [hsum2, htel]
    rw [mul_rpow_three _ _ _ hhalf.le]
    rw [rpow_mul_rpow, rpow_mul_rpow]
    have hsq : (sqSum (blkFin N m q) A) ^ (plExp l / 2)
        = (l2Of (blkFin N m q) A) ^ (plExp l) := by
      simp only [l2Of]
      rw [rpow_mul_rpow]
      congr 1
      ring
    rw [hsq]
    have e1 : pkExp k * (2 / plExp l) * (plExp l / 2) = pkExp k := by field_simp
    have e2 : (2 / plExp l) * (plExp l / 2) = 1 := by field_simp
    rw [e1, e2, ENNReal.rpow_one]
    exact le_of_eq (by ring)
  -- Step 5: combine with the outer factor and the constant
  refine le_trans (hfine q q' hsep f hf) ?_
  refine le_trans (mul_le_mul' le_rfl hfinal) ?_
  have hCf : (C₁ * C₂ ^ (plExp l / pkExp k)) ^ (pkExp k)
      = C₁ ^ (pkExp k) * C₂ ^ (plExp l) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hpk.le, rpow_mul_rpow]
    congr 2
    field_simp
  rw [hCf]
  exact le_of_eq (by ring)

end Submission.Vinogradov
