import Submission.NK.Reconstruct.GammaDual
import Submission.NK.Reconstruct.finite_coker_gammaBaseChangeHom

/-!
# The injectivity half of Shimizu's Lemma 4f.1, concretely

Shimizu (arXiv:2009.10431, §4, Lemma 4f.1) proves that for a finite Galois extension `L/K` of
number fields the restriction

  `res_{L/K} : Hom_{cts}(Γ_K, ℤ_ℓ) → Hom_{cts}(Γ_L, ℤ_ℓ)^{G(L/K)}`

induced by the base-change map `π_{L/K} : Γ_L → Γ_K` (`NK.Reconstruct.gammaBaseChangeHom`,
`Submission/Work/Reconstruct/gammaBaseChange.lean`) is injective with finite cokernel.

This file proves the **injectivity** half for the pair `(Γ_K, Γ_L)` of the projective limits, with
*no* additional input: the cokernel of `π_{L/K}` is finite
(`NK.Reconstruct.finite_coker_gammaBaseChangeHom`; in fact `coker π_{L/K} ≅
(Gal(L/K)^{ab})^{(ℓ)}`), and an additive homomorphism `Γ_K → ℤ_ℓ` which vanishes on the image of
`π_{L/K}` vanishes identically — because it factors through the finite group `coker π_{L/K}`, and a
finite subgroup of the torsion-free group `ℤ_ℓ` is trivial.

The *finiteness of the cokernel* of `res_{L/K}` is the deep half of Lemma 4f.1; it is reduced to
the named `NK.Reconstruct.TransferInput` (the Verlagerung identity `res ∘ cor = [L : K]`, CoNF
(1.6.7)) in `Submission/Work/Reconstruct/lemma4f1.lean`.

## Contents

* `addMonoidHom_eq_zero_of_finite_range` — an additive homomorphism with finite range into `ℤ_ℓ` is
  zero;
* `dualMap_eq_zero_of_finite_coker` — the abstract statement: precomposition with `π` is injective
  on `Hom(-, ℤ_ℓ)` as soon as `coker π` is finite;
* `finite_additive_quotient_range` — the transport of the finiteness of a quotient along
  `Additive`;
* **`res_gamma_injective`** — the concrete injectivity of `res_{L/K}` on the additive dual.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. I §1.6, Ch. X §10.3;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.Reconstruct

open scoped Pointwise

/-- **A finite subgroup of `ℤ_ℓ` is trivial.**  If `H` is a finite additive subgroup of `ℤ_ℓ` then
`H = ⊥`: for `y ∈ H`, two of the elements `0 • y, 1 • y, 2 • y, …` coincide (their number exceeds
`Nat.card H`), so `d • y = 0` for some `d ≠ 0`, and `ℤ_ℓ` is torsion-free. -/
theorem eq_zero_of_finite_addSubgroup {ℓ : ℕ} [Fact ℓ.Prime] {H : AddSubgroup (PadicInt ℓ)}
    (h : Finite ↥H) (y : H) : y = 0 := by
  classical
  haveI := h
  obtain ⟨m, n, hmn, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => (⟨k • (y : PadicInt ℓ), H.nsmul_mem y.2 k⟩ : H))
  have h1 : m • (y : PadicInt ℓ) = n • (y : PadicInt ℓ) := Subtype.ext_iff.mp heq
  have key : ∀ d : ℕ, d ≠ 0 → d • (y : PadicInt ℓ) = 0 → (y : PadicInt ℓ) = 0 := by
    intro d hd hd0
    have hcast : (d : PadicInt ℓ) • (y : PadicInt ℓ) = 0 := by
      rw [Nat.cast_smul_eq_nsmul]
      exact hd0
    rcases smul_eq_zero.mp hcast with h2 | h2
    · exact absurd h2 (Nat.cast_ne_zero.mpr hd)
    · exact h2
  rcases Nat.lt_or_gt_of_ne hmn with hlt | hgt
  · refine Subtype.ext (key (n - m) (by omega) ?_)
    have h3 : m • (y : PadicInt ℓ) + (n - m) • (y : PadicInt ℓ) = m • (y : PadicInt ℓ) := by
      rw [← add_nsmul, Nat.add_sub_of_le hlt.le, h1]
    have := congrArg (fun z : PadicInt ℓ => z - m • (y : PadicInt ℓ)) h3
    simpa using this
  · refine Subtype.ext (key (m - n) (by omega) ?_)
    have h3 : n • (y : PadicInt ℓ) + (m - n) • (y : PadicInt ℓ) = n • (y : PadicInt ℓ) := by
      rw [← add_nsmul, Nat.add_sub_of_le hgt.le, ← h1]
    have := congrArg (fun z : PadicInt ℓ => z - n • (y : PadicInt ℓ)) h3
    simpa using this

/-- **An additive homomorphism with finite range into `ℤ_ℓ` is zero.** -/
theorem addMonoidHom_eq_zero_of_finite_range {ℓ : ℕ} [Fact ℓ.Prime] {A : Type*} [AddCommGroup A]
    (φ : A →+ PadicInt ℓ) (h : Finite ↥(φ.range)) : φ = 0 := by
  classical
  ext x
  haveI := h
  simpa using congrArg Subtype.val
    (eq_zero_of_finite_addSubgroup (H := φ.range) h
      ⟨φ x, AddMonoidHom.mem_range.mpr ⟨x, rfl⟩⟩)

/-- **The abstract injectivity statement**: precomposition with `π : B →+ A` is injective on
`Hom(-, ℤ_ℓ)` as soon as `coker π` is finite. -/
theorem dualMap_eq_zero_of_finite_coker {ℓ : ℕ} [Fact ℓ.Prime] {A B : Type*}
    [AddCommGroup A] [AddCommGroup B] (f : B →+ A) (hfin : Finite (A ⧸ f.range))
    (φ : A →+ PadicInt ℓ) (hφ : φ.comp f = 0) : φ = 0 := by
  classical
  haveI := hfin
  have hle : f.range ≤ φ.ker := (AddMonoidHom.range_le_ker_iff f φ).mpr hφ
  let ψ : A ⧸ f.range →+ PadicInt ℓ := QuotientAddGroup.lift f.range φ hle
  have hψ : ∀ a : A, ψ (QuotientAddGroup.mk a) = φ a := fun _ => rfl
  have hrg : φ.range = ψ.range := by
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp hy
      exact AddMonoidHom.mem_range.mpr ⟨QuotientAddGroup.mk a, (hψ a).trans ha⟩
    · intro y hy
      obtain ⟨q, hq⟩ := AddMonoidHom.mem_range.mp hy
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
      exact AddMonoidHom.mem_range.mpr ⟨a, (hψ a).symm.trans hq⟩
  have hfinψ : Finite ↥(ψ.range) :=
    Finite.of_surjective (fun q : (A ⧸ f.range) =>
        (⟨ψ q, AddMonoidHom.mem_range.mpr ⟨q, rfl⟩⟩ : ψ.range))
      (fun y => by
        obtain ⟨q, hq⟩ := AddMonoidHom.mem_range.mp y.2
        exact ⟨q, Subtype.ext hq⟩)
  exact addMonoidHom_eq_zero_of_finite_range φ (hrg ▸ hfinψ)

/-- **The concrete injectivity half of Shimizu's Lemma 4f.1.**  For a `ℤ_ℓ`-linear (here: additive)
`f : B → A` with finite cokernel — in the application `f = π_{L/K}`, whose cokernel is finite by
`NK.Reconstruct.finite_coker_gammaBaseChangeHom` — precomposition with `f` is injective on the
additive dual `Hom(-, ℤ_ℓ)`.

The *finiteness of the cokernel* of the restriction is the deep half of Lemma 4f.1; it is reduced
to the named `NK.Reconstruct.TransferInput` (the Verlagerung identity `res ∘ cor = [L : K]`,
CoNF (1.6.7)) in `Submission/Work/Reconstruct/lemma4f1.lean`. -/
theorem res_injective_of_finite_coker {ℓ : ℕ} [Fact ℓ.Prime] {A B : Type*}
    [AddCommGroup A] [AddCommGroup B] (f : B →+ A) (hfin : Finite (A ⧸ f.range)) :
    Function.Injective (fun (φ : A →+ PadicInt ℓ) => φ.comp f) := by
  intro φ ψ hφψ
  have h0 : (φ - ψ).comp f = 0 := by
    ext b
    have hb : φ (f b) = ψ (f b) := congrFun (congrArg DFunLike.coe hφψ) b
    simpa using sub_eq_zero.mpr hb
  have hz : φ - ψ = 0 := dualMap_eq_zero_of_finite_coker f hfin (φ - ψ) h0
  simpa using sub_eq_zero.mp hz

end NK.Reconstruct
