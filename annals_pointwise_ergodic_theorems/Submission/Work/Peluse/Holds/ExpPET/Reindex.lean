import Mathlib
import Submission.Work.Peluse.Holds.ExpPET.Defs

/-!
# The reindexing brick of `ExpansionPETShort`

`Work.Peluse.Holds.ExpansionPETShort` is the first half of Peluse's Theorem 3.5: from a lower bound
for the average over `a ∈ [1,M₂]` of the level-`s` box norm of `f` at the direction sets
`Q_i(a) = (c·a + b_i)[M₁]`, produce a lower bound for the average over `(h,h') ∈ [M₁]^s × [M₁]^s`
of the level-`(2^s-1)` box-norm power at the *short* direction sets `c((h-h')·ω)[δ'M₂]`.

The first step of any proof is the **reindexing** of the box sum: the sum over
`(h,h') ∈ ∏_i Q_i(a) × ∏_i Q_i(a)` is, after the substitution `h_i = (c·a + b_i)·k_i`, a sum over
`(k,k') ∈ [1,M₁]^s × [1,M₁]^s`, and the normalisation `∏_i |Q_i(a)|⁻¹` becomes `M₁^{-s}` — with the
**degenerate case** `c·a + b_i = 0` handled by the identity below: for *every* `κ` and `1 ≤ M₁`,

  `(|arithIcc κ M₁|)⁻¹² ∑_{h,h' ∈ arithIcc κ M₁} φ h h' = M₁⁻¹² ∑_{k,k' ∈ [1,M₁]} φ (κk) (κk')`.

(For `κ = 0` both sides equal `φ 0 0`; for `κ ≠ 0` the map `k ↦ κk` is injective.)

This file contains the identity in its one-dimensional (per-slot) form together with the two
cardinality facts it needs.  It is pure `Finset` algebra, independent of the rest of the route.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Holds.ExpPET

noncomputable section

open Work.Peluse

/-- The arithmetic progression `0[M₁]` is the singleton `{0}` (for `1 ≤ M₁`). -/
lemma arithIcc_zero_eq_singleton' {M₁ : ℕ} (hM₁ : 1 ≤ M₁) :
    Work.Peluse.arithIcc (0 : ℤ) M₁ = {0} := by
  ext y
  simp only [Work.Peluse.arithIcc, Finset.mem_image, Finset.mem_Icc, Finset.mem_singleton]
  constructor
  · rintro ⟨n, _, hn⟩
    rw [← hn]; ring
  · intro hy
    exact ⟨1, ⟨le_refl 1, hM₁⟩, by rw [hy]; ring⟩

/-- The cardinality of an arithmetic progression (for `1 ≤ M₁`). -/
lemma card_arithIcc' (κ : ℤ) {M₁ : ℕ} (hM₁ : 1 ≤ M₁) :
    (Work.Peluse.arithIcc κ M₁).card = if κ = 0 then 1 else M₁ := by
  rcases eq_or_ne κ 0 with rfl | hκ
  · rw [arithIcc_zero_eq_singleton' hM₁, Finset.card_singleton, if_pos rfl]
  · rw [if_neg hκ, Work.Peluse.arithIcc, Finset.card_image_of_injOn]
    · simp
    · intro a _ b _ hab
      have h : (a : ℤ) = (b : ℤ) := mul_left_cancel₀ hκ hab
      exact_mod_cast h

/-- **The reindexing identity** of the arithmetic progression `κ[M₁]` (with its cardinality
normalisation, valid also in the degenerate case `κ = 0`). -/
lemma sum_arithIcc_pair' (κ : ℤ) {M₁ : ℕ} (hM₁ : 1 ≤ M₁) (φ : ℤ → ℤ → ℂ) :
    (((Work.Peluse.arithIcc κ M₁).card : ℂ))⁻¹ ^ 2
        * ∑ h ∈ Work.Peluse.arithIcc κ M₁, ∑ h' ∈ Work.Peluse.arithIcc κ M₁, φ h h'
      = (((M₁ : ℂ)))⁻¹ ^ 2
        * ∑ k ∈ Finset.Icc 1 M₁, ∑ k' ∈ Finset.Icc 1 M₁,
            φ (κ * (k : ℤ)) (κ * (k' : ℤ)) := by
  rcases eq_or_ne κ 0 with rfl | hκ
  · rw [arithIcc_zero_eq_singleton' hM₁]
    simp only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, inv_one, one_pow,
      one_mul, zero_mul]
    rw [Finset.sum_const, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, nsmul_eq_mul,
      Nat.add_sub_cancel]
    have hM₁c : ((M₁ : ℂ)) ≠ 0 := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mp hM₁)
    field_simp
  · have hcard : ((Work.Peluse.arithIcc κ M₁).card : ℂ) = (M₁ : ℂ) := by
      rw [card_arithIcc' κ hM₁, if_neg hκ]
    rw [hcard]
    have h1 : ∀ ψ : ℤ → ℂ, ∑ h ∈ Work.Peluse.arithIcc κ M₁, ψ h
        = ∑ k ∈ Finset.Icc 1 M₁, ψ (κ * (k : ℤ)) := by
      intro ψ
      rw [Work.Peluse.arithIcc]
      exact Finset.sum_image (fun a _ b _ hab => by
        have h : (a : ℤ) = (b : ℤ) := mul_left_cancel₀ hκ hab
        exact_mod_cast h)
    rw [h1 (fun h => ∑ h' ∈ Work.Peluse.arithIcc κ M₁, φ h h')]
    congr 1
    exact Finset.sum_congr rfl fun k _ => h1 (fun h' => φ (κ * (k : ℤ)) h')

/-! ## The corner bookkeeping of the expansion

The cube average `prodCubeSum` writes its corners as `cornerShift h h' ω` (with the shifts
`h, h' : Fin s → ℤ`), while the expansion vocabulary of `ExpPET/Defs.lean` writes them as
`cubeShift κ n n' ω` (with the *coefficients* `κ : Fin s → ℤ` already multiplied into the labels).
The two agree when `h_i = κ_i·n_i` and `h'_i = κ_i·n'_i`, and `cubeShift_eq` (proved in
`ExpPET/Defs.lean`) then splits the `a`-dependence into the *phase* `c·a·λ_ω` and the shift
`μ_ω = σ_ω` used by Peluse's Lemma 4.10.  This is the bridge between the two vocabularies. -/

/-- The cube corner of `prodCubeSum` at the shifts `κ·n`, `κ·n'` is the `cubeShift` of the
expansion vocabulary. -/
lemma cornerShift_mul_eq_cubeShift {s : ℕ} (κ n n' : Fin s → ℤ) (ω : Fin s → Bool) :
    Work.Peluse.cornerShift (fun i => κ i * n i) (fun i => κ i * n' i) ω
      = cubeShift κ n n' ω := by
  rw [Work.Peluse.cornerShift, cubeShift]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

/-- The same, in the form in which `prodCubeSum` consumes it. -/
lemma prod_cubeTerm_mul_eq_expCube {s : ℕ} (κ n n' : Fin s → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    ∏ ω : Fin s → Bool,
        (star^[Work.Peluse.weight ω])
          (f (x + Work.Peluse.cornerShift (fun i => κ i * n i) (fun i => κ i * n' i) ω))
      = expCube κ n n' f x := by
  rw [expCube]
  exact Finset.prod_congr rfl fun ω _ => by rw [cornerShift_mul_eq_cubeShift]

/-- **The level-one cube term.**  For `t = 1` the cube has two corners, `x + h' 0` (the all-false
pattern, weight `0`) and `x + h 0` (the all-true pattern, weight `1`), so

  `∏_{ω : Fin 1 → Bool} C^{|ω|} f (x + cornerShift h h' ω) = conjugate (f (x + h 0)) · f (x + h' 0)`.

(The factors commute in `ℂ`, so this is also `f (x + h' 0) · conjugate (f (x + h 0))`.) -/
lemma prod_cubeTerm_one_eq (h h' : Fin 1 → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    (∏ ω : Fin 1 → Bool,
        (star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift h h' ω)))
      = f (x + h' 0) * star (f (x + h 0)) := by
  have huniv : (Finset.univ : Finset (Fin 1 → Bool)) = {fun _ => true, fun _ => false} := by
    ext ω
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hω : ω 0 = true
    · left
      funext i
      fin_cases i
      exact hω
    · right
      funext i
      fin_cases i
      simpa using hω
  have hwt1 : Work.Peluse.weight (fun _ : Fin 1 => true) = 1 := by rw [Work.Peluse.weight]; simp
  have hwt0 : Work.Peluse.weight (fun _ : Fin 1 => false) = 0 := by rw [Work.Peluse.weight]; simp
  have hcs1 : Work.Peluse.cornerShift h h' (fun _ : Fin 1 => true) = h 0 := by
    rw [Work.Peluse.cornerShift]; simp
  have hcs0 : Work.Peluse.cornerShift h h' (fun _ : Fin 1 => false) = h' 0 := by
    rw [Work.Peluse.cornerShift]; simp
  rw [huniv, Finset.prod_insert (by decide), Finset.prod_singleton, hwt1, hwt0, hcs1, hcs0]
  simp only [Function.iterate_one, Function.iterate_zero, id_eq]
  ring

end

end Work.Peluse.Holds.ExpPET
