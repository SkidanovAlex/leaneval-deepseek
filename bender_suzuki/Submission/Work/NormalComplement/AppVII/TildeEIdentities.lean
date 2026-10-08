import Mathlib
import Submission.Work.NormalComplement.AppVII.TildeEAux
import Submission.Work.NormalComplement.AppVII.TildeEScalar

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The identities satisfied by the central idempotents of `ℂ[A]`

Let `A` be a finite group and `V = ℂ[A]`.  For `χ : A → ℂ` let
`zℂ χ = ∑ g, χ g⁻¹ • single g 1` and `Eℂ χ = irrDeg χ • zℂ χ = |A| • e_χ`.

This file proves, for irreducible `χ, ψ`:

* `Eℂ χ` is central;
* `Eℂ χ * Eℂ χ = |A| • Eℂ χ`;
* `Eℂ χ * Eℂ ψ = 0` for `χ ≠ ψ`;
* `∑ χ ∈ Irr A, Eℂ χ = |A| • 1`;
* `Eℂ χ * single z 1 = Eℂ χ` whenever `χ z = χ 1`.

The main tools are the scalar action of a central element on a simple submodule
(`Work.NormalComplement.AppVII.central_acts_scalar`), the resulting scalar action of `Eℂ χ`
(`Eℂ_mul_apply`) and the orthogonality relation `zC_pairing`.
-/

set_option maxHeartbeats 4000000

noncomputable section

open Classical

open scoped BigOperators MonoidAlgebra

namespace Work.NormalComplement.AppVII

variable {A : Type*} [Group A] [Fintype A]

/-! ### The zero criterion -/

/-- If a *central* element of `ℂ[A]` annihilates every simple submodule of the regular
module, then it is zero: the kernel of left multiplication by `u` is a `ℂ[A]`-submodule
containing all the simple submodules, hence all of `ℂ[A]`, so it contains `1`. -/
theorem eq_zero_of_central_mul_eq_zero (u : MonoidAlgebra ℂ A)
    (hu : ∀ a : MonoidAlgebra ℂ A, u * a = a * u)
    (h : ∀ (N : Submodule (MonoidAlgebra ℂ A) (MonoidAlgebra ℂ A)),
      N ∈ Work.CharCore.irrSubmodules A → ∀ x ∈ N, u * x = 0) : u = 0 := by
  classical
  let K : Submodule (MonoidAlgebra ℂ A) (MonoidAlgebra ℂ A) :=
    { carrier := {x | u * x = 0}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        show u * (x + y) = 0
        rw [mul_add, hx, hy, add_zero]
      smul_mem' := by
        intro a x hx
        show u * (a • x) = 0
        rw [smul_eq_mul, ← mul_assoc, hu a, mul_assoc, hx, mul_zero] }
  have hle : (⊤ : Submodule (MonoidAlgebra ℂ A) (MonoidAlgebra ℂ A)) ≤ K := by
    rw [← Work.CharCore.sSup_irrSubmodules A]
    exact sSup_le fun N hN => fun x hx => h N hN x hx
  have h1 : u * 1 = 0 := hle trivial
  simpa using h1

/-! ### The character of a simple submodule -/

/-- The character of the simple submodule `N` of the regular module. -/
abbrev charOf (N : Submodule (MonoidAlgebra ℂ A) (MonoidAlgebra ℂ A)) : A → ℂ :=
  (Work.CharCore.submoduleRep N).character

theorem charOf_mem_Irr (N : Submodule (MonoidAlgebra ℂ A) (MonoidAlgebra ℂ A))
    (hN : N ∈ Work.CharCore.irrSubmodules A) : charOf N ∈ Work.CharCore.Irr A :=
  (Work.CharCore.mem_Irr_iff_exists _).mpr ⟨N, hN, rfl⟩

theorem irrDeg_charOf (N : Submodule (MonoidAlgebra ℂ A) (MonoidAlgebra ℂ A))
    (hN : N ∈ Work.CharCore.irrSubmodules A) :
    Work.CharCore.irrDeg (charOf N) = Module.finrank ℂ N :=
  Work.CharCore.irrDeg_eq_finrank (charOf_mem_Irr N hN) hN rfl

/-! ### Linear algebra helpers for products of class sums -/

/-- The action of a product of class sums, given the actions of the factors. -/
theorem zC_mul_zC_mul_apply {χ ψ : A → ℂ} {x : MonoidAlgebra ℂ A} {cχ cψ : ℂ}
    (hχx : zℂ χ * x = cχ • x) (hψx : zℂ ψ * x = cψ • x) :
    (zℂ χ * zℂ ψ) * x = (cψ * cχ) • x := by
  rw [mul_assoc, hψx, mul_smul_comm, hχx, smul_smul]

/-- The action of a scalar multiple of a class sum. -/
theorem smul_zC_mul_apply {χ : A → ℂ} {x : MonoidAlgebra ℂ A} {cχ : ℂ} (c : ℂ)
    (hχx : zℂ χ * x = cχ • x) : (c • zℂ χ) * x = (c * cχ) • x := by
  rw [smul_mul_assoc, hχx, smul_smul]

/-! ### Centrality of combinations of central elements -/

theorem central_mul' {u v : MonoidAlgebra ℂ A} (hu : ∀ a, u * a = a * u)
    (hv : ∀ a, v * a = a * v) : ∀ a, (u * v) * a = a * (u * v) := by
  intro a
  rw [mul_assoc, hv a, ← mul_assoc, hu a, mul_assoc]

theorem central_smul' {u : MonoidAlgebra ℂ A} (hu : ∀ a, u * a = a * u) (c : ℂ) :
    ∀ a, (c • u) * a = a * (c • u) := by
  intro a
  rw [smul_mul_assoc, hu a, mul_smul_comm]

theorem central_sub' {u v : MonoidAlgebra ℂ A} (hu : ∀ a, u * a = a * u)
    (hv : ∀ a, v * a = a * v) : ∀ a, (u - v) * a = a * (u - v) := by
  intro a
  rw [sub_mul, mul_sub, hu a, hv a]

/-- Centrality of `zℂ χ` in the form `zℂ χ * a = a * zℂ χ`. -/
theorem zℂ_central' {χ : A → ℂ} (hχ : χ ∈ Work.CharCore.Irr A) :
    ∀ a, zℂ χ * a = a * zℂ χ :=
  fun a => (zℂ_central hχ a).symm

/-- Centrality of `Eℂ χ` in the form `Eℂ χ * a = a * Eℂ χ`. -/
theorem Eℂ_central' {χ : A → ℂ} (hχ : χ ∈ Work.CharCore.Irr A) :
    ∀ a, Work.Hering.AppVII.Eℂ χ * a = a * Work.Hering.AppVII.Eℂ χ :=
  fun a => (Eℂ_central hχ a).symm

/-! ### The scalar action of the class sums -/

/-- The class sum `zℂ χ` acts on a simple submodule with character `χ` by the scalar
`|A| / irrDeg χ`, and by `0` on the other simple submodules. -/
theorem zC_mul_eq {χ : A → ℂ} (hχ : χ ∈ Work.CharCore.Irr A)
    {N : Submodule (MonoidAlgebra ℂ A) (MonoidAlgebra ℂ A)}
    (hN : N ∈ Work.CharCore.irrSubmodules A) {x : MonoidAlgebra ℂ A} (hx : x ∈ N) :
    zℂ χ * x = ((Nat.card A : ℂ) * (if χ = charOf N then 1 else 0) /
      (Work.CharCore.irrDeg (charOf N) : ℂ)) • x := by
  have hν : charOf N ∈ Work.CharCore.Irr A := charOf_mem_Irr N hN
  have h1 := central_acts_scalar (zℂ χ) (zℂ_central' hχ) N hN hx
  have h2 := zC_pairing χ hχ (charOf N) hν
  rw [h1, h2, ← irrDeg_charOf N hN]

/-- **The scalar action of `Eℂ χ`.**  `Eℂ χ = |A| • e_χ` acts on a simple submodule with
character `χ` as `|A|` (the scalar of the idempotent `e_χ` being `1`), and as `0` on the
other simple submodules. -/
theorem Eℂ_mul_apply {χ : A → ℂ} (hχ : χ ∈ Work.CharCore.Irr A)
    {N : Submodule (MonoidAlgebra ℂ A) (MonoidAlgebra ℂ A)}
    (hN : N ∈ Work.CharCore.irrSubmodules A) {x : MonoidAlgebra ℂ A} (hx : x ∈ N) :
    Work.Hering.AppVII.Eℂ χ * x =
      ((Nat.card A : ℂ) * (if χ = charOf N then 1 else 0)) • x := by
  rw [Eℂ_eq_zℂ]
  have hd : (Work.CharCore.irrDeg χ : ℂ) ≠ 0 := by
    exact_mod_cast (Work.CharCore.irrDeg_pos hχ).ne'
  by_cases h : χ = charOf N
  · have hzx : zℂ χ * x = ((Nat.card A : ℂ) / (Work.CharCore.irrDeg χ : ℂ)) • x := by
      rw [zC_mul_eq hχ hN hx, if_pos h, mul_one, ← h]
    rw [smul_zC_mul_apply _ hzx, if_pos h, mul_one]
    have hq : (Work.CharCore.irrDeg χ : ℂ) *
        ((Nat.card A : ℂ) / (Work.CharCore.irrDeg χ : ℂ)) = (Nat.card A : ℂ) := by
      field_simp
    rw [hq]
  · have hzx : zℂ χ * x = (0 : ℂ) • x := by
      rw [zC_mul_eq hχ hN hx, if_neg h]
      simp
    rw [smul_zC_mul_apply _ hzx]
    simp [h]

/-! ### The identities -/

/-- `Eℂ χ` is a `|A|`-idempotent: `Eℂ χ * Eℂ χ = |A| • Eℂ χ`. -/
theorem Eℂ_mul_self {χ : A → ℂ} (hχ : χ ∈ Work.CharCore.Irr A) :
    Work.Hering.AppVII.Eℂ χ * Work.Hering.AppVII.Eℂ χ =
      (Nat.card A : ℂ) • Work.Hering.AppVII.Eℂ χ := by
  refine sub_eq_zero.mp (eq_zero_of_central_mul_eq_zero
    (Work.Hering.AppVII.Eℂ χ * Work.Hering.AppVII.Eℂ χ -
      (Nat.card A : ℂ) • Work.Hering.AppVII.Eℂ χ)
    (central_sub' (central_mul' (Eℂ_central' hχ) (Eℂ_central' hχ))
      (central_smul' (Eℂ_central' hχ) _)) ?_)
  intro N hN x hx
  have hz := Eℂ_mul_apply hχ hN hx
  have hcoef : ((Nat.card A : ℂ) * (if χ = charOf N then 1 else 0)) *
      ((Nat.card A : ℂ) * (if χ = charOf N then 1 else 0)) -
      (Nat.card A : ℂ) * ((Nat.card A : ℂ) * (if χ = charOf N then 1 else 0)) = 0 := by
    by_cases h : χ = charOf N
    · rw [if_pos h, mul_one]
      ring
    · rw [if_neg h]
      ring
  rw [sub_mul, mul_assoc, hz, mul_smul_comm, hz, smul_smul, smul_mul_assoc, hz, smul_smul,
    ← sub_smul, hcoef, zero_smul]

/-- Distinct `Eℂ χ`, `Eℂ ψ` are orthogonal. -/
theorem Eℂ_mul_eq_zero {χ ψ : A → ℂ} (hχ : χ ∈ Work.CharCore.Irr A)
    (hψ : ψ ∈ Work.CharCore.Irr A) (hne : χ ≠ ψ) :
    Work.Hering.AppVII.Eℂ χ * Work.Hering.AppVII.Eℂ ψ = 0 := by
  refine eq_zero_of_central_mul_eq_zero
    (Work.Hering.AppVII.Eℂ χ * Work.Hering.AppVII.Eℂ ψ)
    (central_mul' (Eℂ_central' hχ) (Eℂ_central' hψ)) ?_
  intro N hN x hx
  have hcoef : ((Nat.card A : ℂ) * (if ψ = charOf N then 1 else 0)) *
      ((Nat.card A : ℂ) * (if χ = charOf N then 1 else 0)) = 0 := by
    by_cases h : ψ = charOf N
    · rw [if_pos h, mul_one, if_neg (fun hh => hne (hh.trans h.symm))]
      ring
    · rw [if_neg h]
      ring
  rw [mul_assoc, Eℂ_mul_apply hψ hN hx, mul_smul_comm, Eℂ_mul_apply hχ hN hx, smul_smul,
    hcoef, zero_smul]

/-- The `Eℂ χ` sum to `|A|`. -/
theorem sum_Eℂ :
    (∑ χ ∈ Work.CharCore.Irr A, Work.Hering.AppVII.Eℂ χ) =
      (Nat.card A : ℂ) • (1 : MonoidAlgebra ℂ A) := by
  refine sub_eq_zero.mp (eq_zero_of_central_mul_eq_zero
    ((∑ χ ∈ Work.CharCore.Irr A, Work.Hering.AppVII.Eℂ χ) -
      (Nat.card A : ℂ) • (1 : MonoidAlgebra ℂ A)) ?_ ?_)
  · intro a
    have hsum : (∑ χ ∈ Work.CharCore.Irr A, Work.Hering.AppVII.Eℂ χ) * a =
        a * (∑ χ ∈ Work.CharCore.Irr A, Work.Hering.AppVII.Eℂ χ) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun χ hχ => Eℂ_central' hχ a
    have hsm : ((Nat.card A : ℂ) • (1 : MonoidAlgebra ℂ A)) * a =
        a * ((Nat.card A : ℂ) • (1 : MonoidAlgebra ℂ A)) := by
      rw [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    rw [sub_mul, mul_sub, hsum, hsm]
  · intro N hN x hx
    have hsum : (∑ χ ∈ Work.CharCore.Irr A, (Nat.card A : ℂ) *
        (if χ = charOf N then 1 else 0)) = (Nat.card A : ℂ) := by
      rw [Finset.sum_eq_single (charOf N)]
      · rw [if_pos rfl, mul_one]
      · intro b _ hbne
        rw [if_neg hbne, mul_zero]
      · intro hnot
        exact absurd (charOf_mem_Irr N hN) hnot
    have hcongr : (∑ χ ∈ Work.CharCore.Irr A,
          Work.Hering.AppVII.Eℂ χ * x) =
        ∑ χ ∈ Work.CharCore.Irr A,
          ((Nat.card A : ℂ) * (if χ = charOf N then 1 else 0)) • x :=
      Finset.sum_congr rfl fun χ hχ => Eℂ_mul_apply hχ hN hx
    rw [sub_mul, Finset.sum_mul, smul_mul_assoc, one_mul, hcongr, ← Finset.sum_smul, hsum,
      sub_self]

/-- `χ (z * k) = χ k` for `z` in the kernel of the irreducible character `χ`. -/
theorem character_apply_mul_eq {χ : A → ℂ} (hχ : χ ∈ Work.CharCore.Irr A) {z : A}
    (hz : χ z = χ 1) (k : A) : χ (z * k) = χ k := by
  obtain ⟨N, hN, hNχ⟩ := Work.CharCore.exists_mem_irrSubmodules_of_mem_Irr hχ
  have hρ : (Work.CharCore.submoduleRep N) z = 1 := by
    refine Work.CharCore.eq_one_of_character_eq_degree _
      (Work.Clifford.submoduleRep_isIrreducible hN) z ?_
    rw [hNχ]
    exact hz
  have htr : (Work.CharCore.submoduleRep N).character (z * k) =
      (Work.CharCore.submoduleRep N).character k := by
    rw [show (Work.CharCore.submoduleRep N).character (z * k) =
        (Work.CharCore.submoduleRep N).character (z * k) from rfl,
      Representation.character, Representation.character, map_mul, hρ, one_mul]
  rw [← hNχ, htr, hNχ]

/-- The coefficients of `Eℂ χ`: `(Eℂ χ).coeff g = irrDeg χ * χ g⁻¹`. -/
theorem coeff_Eℂ {χ : A → ℂ} (g : A) :
    (Work.Hering.AppVII.Eℂ χ).coeff g = (Work.CharCore.irrDeg χ : ℂ) * χ (g⁻¹) := by
  rw [Eℂ_eq_zℂ, MonoidAlgebra.coeff_smul_apply, coeff_zℂ, smul_eq_mul]

/-- `Eℂ χ · z = Eℂ χ` for `z` in the kernel of the irreducible character `χ`. -/
theorem Eℂ_mul_single {χ : A → ℂ} (hχ : χ ∈ Work.CharCore.Irr A) {z : A}
    (hz : χ z = χ 1) :
    Work.Hering.AppVII.Eℂ χ * MonoidAlgebra.single z (1 : ℂ) =
      Work.Hering.AppVII.Eℂ χ := by
  ext g
  rw [MonoidAlgebra.coeff_mul_single_apply, mul_one, coeff_Eℂ, coeff_Eℂ,
    show (g * z⁻¹)⁻¹ = z * g⁻¹ from by group, character_apply_mul_eq hχ hz]

end Work.NormalComplement.AppVII
