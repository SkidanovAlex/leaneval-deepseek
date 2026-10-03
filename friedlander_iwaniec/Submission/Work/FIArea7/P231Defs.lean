/-
# `Work.FIArea7.P231Defs` — the vocabulary of the reduction Prop. 21.4 ⟹ Prop. 23.1

This module fixes the small extra vocabulary that the reduction of *FI* §23 (Prop. 23.1) from
*FI* Prop. 21.4 needs, namely the **coprimality restricted** bilinear form in the Jacobi–Kubota
symbol,

* (21.12) `K*(M,N) = ∑∑_{(w,z)=1} α_w β_z [wz]`  (`KBilinStar`),

together with the statement `KStarBound` of the corresponding bound (the paper derives it inside the
proof of Prop. 21.4 by Möbius inversion from the unrestricted `K(M,N)`; the reduction of §23 needs
it *directly*, so it is repeated here).

The objects `JKSym`, `KBilin` and `Prop214` are the ones of
`Submission/Work/FIArea7/Classical172Defs.lean`; `GaussCoprime` is
`Work.FIPlan.GaussCoprime z₁ z₂ = IsCoprime z₁ z₂`.
-/
import Mathlib
import Submission.Work.FIArea7.Classical172Defs

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **(21.12)**: the coprimality restricted bilinear form in the Jacobi–Kubota symbol,
`K*(M,N) = ∑_{w ∈ gBox Rw} ∑_{z ∈ gBox Rz} 1[(w,z)=1] α_w β_z [wz]`. -/
def KBilinStar (Rw Rz : ℤ) (α β : GaussianInt → ℂ) : ℂ :=
  ∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
    (if Work.FIPlan.GaussCoprime w z then α w * β z * JKSym (w * z) else 0)

/-- **(21.13) for the restricted form.**  The bilinear form `K*(M,N)` satisfies the same bound as
`K(M,N)`: for coefficients `α` supported on primary *primitive* `w` with `|w|² ≤ M` and `β`
supported on primary `z` with `|z|² ≤ N`, both bounded by `1`,

  `‖K*(M,N)‖ ≤ C·(M+N)^{1/12}·(MN)^{11/12}·(log(MN+2))^A`.

This is the form of Prop. 21.4 that *FI* §23 consumes (the paper derives it from `K(M,N)` by
Möbius inversion inside the proof of Prop. 21.4; the derivation is repeated in
`Submission/Work/FIArea7/P231/kstar_from_prop214.lean`). -/
def KStarBound : Prop :=
  ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
    ∀ (M N : ℝ) (Rw Rz : ℤ) (α β : GaussianInt → ℂ),
      1 ≤ M → 1 ≤ N →
      (∀ w, ‖α w‖ ≤ 1) → (∀ z, ‖β z‖ ≤ 1) →
      (∀ w, α w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
        (Work.FIPlan.gnorm w : ℝ) ≤ M) →
      (∀ z, β z ≠ 0 → Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ N) →
      ‖KBilinStar Rw Rz α β‖
        ≤ C * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)
            * (Real.log (M * N + 2)) ^ A

/-! ## 2. The two intermediate forms of the reduction

*FI*'s proof of Prop. 23.1 goes in three steps: the *reduced* case `(c,mn) = 1`, `(m,n) = 1`
(`ReducedBound`), then removal of the support condition `(mn,c) = 1` (`CoprimeBound`), then removal
of `(m,n) = 1` (which is `Prop231` itself).  The two intermediate `Prop`s are fixed here so that the
reduction steps can be delegated and assembled separately. -/

/-- **The reduced case of (23.8)**: `L*(M,N)` for coefficients `α, β` supported on integers coprime
to `c` (so that `λ(cmn)` factorises over the primary divisors of `c`, `m`, `n`).  As in the paper the
sum over the primary `e` with `eē = c` contributes a factor `τ(c)`. -/
def ReducedBound : Prop :=
  ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
    ∀ (M N c : ℕ) (k : ℤ) (χ : GaussianInt → ℂ) (α β : ℕ → ℂ),
      1 ≤ c → 1 ≤ M → 1 ≤ N →
      (∀ z, ‖χ z‖ ≤ 1) →
      (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → χ (z1 * z2) = χ z1 * χ z2) →
      (∀ m, m ∈ Finset.Icc 1 M → ‖α m‖ ≤ 1) →
      (∀ m, m ∈ Finset.Icc 1 M → α m ≠ 0 → Nat.Coprime m c) →
      (∀ n, n ∈ Finset.Icc 1 N → ‖β n‖ ≤ 1) →
      (∀ n, n ∈ Finset.Icc 1 N → β n ≠ 0 → Nat.Coprime n c) →
      ‖LBilinStar M N c (grossenChar χ k) α β‖
        ≤ C * ((c.divisors.card : ℝ)) * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)
            * (Real.log (M * N + 2)) ^ A

/-- **The coprime case of (23.8)**: `L*(M,N)` for arbitrary bounded coefficients (the support
condition `(mn,c) = 1` removed, at the cost of the factor `τ(c)`). -/
def CoprimeBound : Prop :=
  ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
    ∀ (M N c : ℕ) (k : ℤ) (χ : GaussianInt → ℂ) (α β : ℕ → ℂ),
      1 ≤ c → 1 ≤ M → 1 ≤ N →
      (∀ z, ‖χ z‖ ≤ 1) →
      (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → χ (z1 * z2) = χ z1 * χ z2) →
      (∀ m, m ∈ Finset.Icc 1 M → ‖α m‖ ≤ 1) →
      (∀ n, n ∈ Finset.Icc 1 N → ‖β n‖ ≤ 1) →
      ‖LBilinStar M N c (grossenChar χ k) α β‖
        ≤ C * ((c.divisors.card : ℝ)) * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)
            * (Real.log (M * N + 2)) ^ A

/-- The primary Gaussian integers of norm exactly `N`, as a finite set (they all lie in the box
`gBox N`, by `Work.FIArea7.mem_gBox_of_gnorm_eq`).  Used to state the factorisation (23.1) of the
eigenvalue without any decidability side conditions in the statement. -/
def primaryNormSet (N : ℕ) : Finset GaussianInt :=
  (Work.FIPlan.gBox (N : ℤ)).filter (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = N)

@[simp] lemma mem_primaryNormSet {N : ℕ} {z : GaussianInt} :
    z ∈ primaryNormSet N ↔ Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = N := by
  simp only [primaryNormSet, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Work.FIArea7.mem_gBox_of_gnorm_eq h.2, h⟩⟩

/-- The summand of the `ε`-form of §23: for a fixed primary `σ` and coefficients `A`, `B`, the
product `A_w B_z ε(σ,wz) [wz]` (restricted to Gauss-coprime pairs).  Bundling the `if` into a
definition keeps the decidability side condition out of the statements that use it. -/
def epsSummand (σ : GaussianInt) (A B : GaussianInt → ℂ) (w z : GaussianInt) : ℂ :=
  if Work.FIPlan.GaussCoprime w z then
    A w * B z * ((MultEps σ (w * z) : ℂ) * JKSym (w * z)) else 0

/-- The primary Gaussian integers of norm `≤ M` (contained in the box `gBox M`). -/
def primaryDisc (M : ℕ) : Finset GaussianInt :=
  (Work.FIPlan.gBox (M : ℤ)).filter (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z ≤ M)

@[simp] lemma mem_primaryDisc {M : ℕ} {z : GaussianInt} :
    z ∈ primaryDisc M ↔ Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z ≤ M := by
  refine ⟨fun h => (Finset.mem_filter.mp h).2, fun h => ?_⟩
  refine Finset.mem_filter.mpr ⟨?_, h⟩
  have hre : z.re.natAbs ≤ M := by
    refine Work.FIArea7.natAbs_le_of_sq_le ?_
    have h2 : z.re ^ 2 ≤ (Work.FIPlan.gnorm z : ℤ) := by
      have h3 := Work.FIArea7.norm_eq z
      nlinarith [sq_nonneg z.im]
    exact le_trans h2 (by exact_mod_cast h.2)
  have him : z.im.natAbs ≤ M := by
    refine Work.FIArea7.natAbs_le_of_sq_le ?_
    have h2 : z.im ^ 2 ≤ (Work.FIPlan.gnorm z : ℤ) := by
      have h3 := Work.FIArea7.norm_eq z
      nlinarith [sq_nonneg z.re]
    exact le_trans h2 (by exact_mod_cast h.2)
  have key : ∀ a : ℤ, a.natAbs ≤ M → -(M : ℤ) ≤ a ∧ a ≤ (M : ℤ) := by
    intro a ha
    have hcast : (a.natAbs : ℤ) ≤ (M : ℤ) := by exact_mod_cast ha
    rcases Int.natAbs_eq a with hh | hh <;> rw [hh] at hcast ⊢ <;> constructor <;> omega
  have h1 := key z.re hre
  have h2 := key z.im him
  rw [Work.FIPlan.gBox, Finset.mem_image]
  exact ⟨(z.re, z.im), Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr h1, Finset.mem_Icc.mpr h2⟩, rfl⟩

/-- The primary *primitive* Gaussian integers of norm exactly `c`.  (Non-primitive `e` contribute
nothing to the §23 sums, because then `[e·w·z] = 0`.) -/
def primaryPrimSet (c : ℕ) : Finset GaussianInt :=
  (Work.FIPlan.gBox (c : ℤ)).filter
    (fun e => Work.FIPlan.IsPrimary e ∧ Work.FIPlan.gnorm e = c ∧ IsCoprime e.re e.im)

@[simp] lemma mem_primaryPrimSet {c : ℕ} {e : GaussianInt} :
    e ∈ primaryPrimSet c ↔
      Work.FIPlan.IsPrimary e ∧ Work.FIPlan.gnorm e = c ∧ IsCoprime e.re e.im := by
  refine ⟨fun h => (Finset.mem_filter.mp h).2, fun h => ?_⟩
  exact Finset.mem_filter.mpr ⟨Work.FIArea7.mem_gBox_of_gnorm_eq h.2.1, h⟩

/-! ## 4. The three analytic inputs of the §23 reduction

These bundle the statements of the delegated lemmas (`multEps_expansion`, `card_strip_le`,
`multEps_uniform`) so that the assembly can be written against a single name. -/

/-- The separation of the multiplier sign `ε(σ,wz)` on the pairs with room (FI (20.15)+(20.19)). -/
def EpsExpansionProp : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (σ : GaussianInt) (R : ℕ), 2 ≤ R →
    Work.FIPlan.IsPrimary σ → IsCoprime σ.re σ.im → σ.im ≠ 0 →
    ∃ ĉ : ℤ → ℂ, (∀ s : Finset ℤ, ∑ k ∈ s, ‖ĉ k‖ ≤ C * (Real.log (2 * R)) ^ 4) ∧
    ∀ w z : GaussianInt, Work.FIPlan.IsPrimary w → Work.FIPlan.IsPrimary z →
      w ≠ 0 → z ≠ 0 →
      ‖σ.toComplex‖ * ‖(w * z).toComplex‖ ≤ (R : ℝ) * |(((σ * (w * z)).re : ℤ) : ℝ)| →
      ‖w.toComplex‖ * ‖z.toComplex‖ ≤ (R : ℝ) * |(((w * z).re : ℤ) : ℝ)| →
      HasSum (fun k : ℤ => ĉ k * ((w.toComplex / (‖w.toComplex‖ : ℂ)) ^ k
                                * (z.toComplex / (‖z.toComplex‖ : ℂ)) ^ k))
        (2 * (MultEps σ (w * z) : ℂ) * (HilbertInf σ.re σ.im : ℂ))

/-- The lattice-point count for the pairs on which the room condition fails. -/
def StripCountProp : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (W : GaussianInt), 1 ≤ R → 1 ≤ N → W ≠ 0 →
    ((((Work.FIPlan.gBox ((N : ℤ))).filter (fun z => Work.FIPlan.gnorm z ≤ N ∧
       ((W * z).re) ^ 2 * (R : ℤ) ^ 2 < (Work.FIPlan.gnorm W : ℤ) * (N : ℤ))).card : ℝ))
      ≤ C * (Real.sqrt (N : ℝ) + (N : ℝ) / (R : ℝ))

/-- The `ε`-step: for a fixed primary primitive `σ`, the `ε`-form is bounded by the `K*`-bound for
the corresponding bilinear form plus the cost of the exceptional pairs. -/
def EpsStepProp : Prop :=
  ∀ Cexp Ccard : ℝ, 0 < Cexp → 0 < Ccard →
    ∃ C : ℝ, 0 < C ∧
      ∀ {M N : ℝ}, 1 ≤ M → 1 ≤ N → ∀ {Bound : ℝ}, 0 ≤ Bound →
      (∀ (Rw Rz : ℤ) (A B : GaussianInt → ℂ),
         (∀ w, ‖A w‖ ≤ 1) → (∀ z, ‖B z‖ ≤ 1) →
         (∀ w, A w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
            (Work.FIPlan.gnorm w : ℝ) ≤ M) →
         (∀ z, B z ≠ 0 → Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ N) →
         ‖KBilinStar Rw Rz A B‖ ≤ Bound) →
      (∀ (σ : GaussianInt) (R : ℕ), 2 ≤ R → Work.FIPlan.IsPrimary σ →
         IsCoprime σ.re σ.im → σ.im ≠ 0 → ∃ ĉ : ℤ → ℂ,
         (∀ s : Finset ℤ, ∑ k ∈ s, ‖ĉ k‖ ≤ Cexp * (Real.log (2 * R)) ^ 4) ∧
         ∀ w z : GaussianInt, Work.FIPlan.IsPrimary w → Work.FIPlan.IsPrimary z →
           w ≠ 0 → z ≠ 0 →
           ‖σ.toComplex‖ * ‖(w * z).toComplex‖ ≤ (R : ℝ) * |(((σ * (w * z)).re : ℤ) : ℝ)| →
           ‖w.toComplex‖ * ‖z.toComplex‖ ≤ (R : ℝ) * |(((w * z).re : ℤ) : ℝ)| →
           HasSum (fun k : ℤ => ĉ k * ((w.toComplex / (‖w.toComplex‖ : ℂ)) ^ k
                                     * (z.toComplex / (‖z.toComplex‖ : ℂ)) ^ k))
             (2 * (MultEps σ (w * z) : ℂ) * (HilbertInf σ.re σ.im : ℂ))) →
      (∀ (N' R : ℕ) (W : GaussianInt), 1 ≤ R → 1 ≤ N' → W ≠ 0 →
         ((((Work.FIPlan.gBox ((N' : ℤ))).filter (fun z => Work.FIPlan.gnorm z ≤ N' ∧
            ((W * z).re) ^ 2 * (R : ℤ) ^ 2 < (Work.FIPlan.gnorm W : ℤ) * (N' : ℤ))).card : ℝ))
          ≤ Ccard * (Real.sqrt (N' : ℝ) + (N' : ℝ) / (R : ℝ))) →
      ∀ {σ : GaussianInt}, Work.FIPlan.IsPrimary σ → IsCoprime σ.re σ.im → σ.im ≠ 0 →
      ∀ (Rw Rz : ℤ) (A B : GaussianInt → ℂ),
        (∀ w, ‖A w‖ ≤ 1) → (∀ z, ‖B z‖ ≤ 1) →
        (∀ w, A w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
           (Work.FIPlan.gnorm w : ℝ) ≤ M) →
        (∀ z, B z ≠ 0 → Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ N) →
        ‖∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz, epsSummand σ A B w z‖
          ≤ C * (Real.log (M * N + 2)) ^ 8 * (Bound + M * Real.sqrt N + Real.sqrt (M * N))
/-- The §23 rewriting of `L*(M,N)` as the `ε`-form: the statement proved in
`Submission/Work/FIArea7/P231/LBilinStar_eq_epsSums.lean`. -/
def ReducedIdentityProp : Prop :=
  ∀ {M N c : ℕ}, 1 ≤ c → 1 ≤ M → 1 ≤ N → ∀ (k : ℤ) (χ : GaussianInt → ℂ),
    (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → χ (z1 * z2) = χ z1 * χ z2) →
    ∀ (α β : ℕ → ℂ),
    (∀ m, m ∈ Finset.Icc 1 M → α m ≠ 0 → Nat.Coprime m c) →
    (∀ n, n ∈ Finset.Icc 1 N → β n ≠ 0 → Nat.Coprime n c) →
    LBilinStar M N c (grossenChar χ k) α β
      = ∑ e ∈ primaryPrimSet c,
          grossenChar χ k e * JKSym e *
            (∑ w ∈ primaryDisc M, ∑ z ∈ primaryDisc N,
              epsSummand e
                (fun w => (α (Work.FIPlan.gnorm w)) * grossenChar χ k w
                  * ((DirichletSym e w : ℤ) : ℂ))
                (fun z => (β (Work.FIPlan.gnorm z)) * grossenChar χ k z
                  * ((DirichletSym e z : ℤ) : ℂ))
                w z)
end

end Work.FIArea7
