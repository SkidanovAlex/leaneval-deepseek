import Submission.NK.Reconstruct.dual_injective_of_finite_index
import Submission.NK.Reconstruct.finite_of_fg_torsion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shimizu's Lemma 4f.1, with the transfer input named

Shimizu (arXiv:2009.10431, §4, Lemma 4f.1) proves that for a finite Galois extension `L/K` of
number fields the restriction

  `res_{L/K} : Hom_{cts}(Γ_K, ℤ_ℓ) → Hom_{cts}(Γ_L, ℤ_ℓ)^{G(L/K)}`

induced by the *base-change map* `π_{L/K} : Γ_L → Γ_K` (the map on the torsion-free ℓ-adic
abelianisations induced by the inclusion `G_L ⊆ G_K`, constructed levelwise in
`Submission/Work/Reconstruct/baseChange.lean`) is **injective with finite cokernel**, and hence
`rank_{ℤ_ℓ} Hom_{cts}(Γ_L, ℤ_ℓ)^{G(L/K)} = r_ℓ(K)`.

Since `G(L/K)` acts on `Γ_L` and `Hom(Γ_L, ℤ_ℓ)^{G(L/K)} ≅ Hom((Γ_L)_{G(L/K)}, ℤ_ℓ)` (`f` is
`G`-invariant iff it kills `I_G Γ_L`), `res` is the dual of the map on coinvariants
`π̄ : (Γ_L)_{G(L/K)} → Γ_K`.  The two halves of the lemma then separate cleanly:

* **injectivity** is the statement that `ker(res) = Hom(coker π̄, ℤ_ℓ)` vanishes, i.e. that `π̄` has
  **finite cokernel**.  This is the formally provable half: `im(π_{L/K}) = ker(Γ_K → Γ_{L,ℓ}(K))`
  (the projection `Γ_K → Γ_{L,ℓ}(K)` being surjective), and at each finite level the exactness
  `Ab(N) → Ab(G) → Ab(G/N) → 0` — `NK.Reconstruct.abelianization_range_inclusion_eq_ker_quotient`
  — identifies `coker(π_{L/K})` with the finite group `(Gal(L/K)^{ab})^{(ℓ)}`.  It is proved here in
  the abstract duality form `dual_injective_of_finite_index`.

* **finiteness of the cokernel** is *equivalent* to the finiteness of `ker π̄`, i.e. to the
  **transfer (Verlagerung) identity** `res ∘ cor = [L : K]` (CoNF (1.6.7)), equivalently to
  `rank_{ℤ_ℓ} (Γ_L)_{G(L/K)} = r_ℓ(K)`.  This is the *single* arithmetic input of Lemma 4f.1; it is
  named below as `TransferInput`, and it is not contained in the input list of any sibling area.
  Shimizu's own proof obtains it from the Hochschild–Serre sequence
  `0 → H¹(G(L/K), ℤ/ℓⁿ) → H¹(G_K, ℤ/ℓⁿ) → H¹(G_L, ℤ/ℓⁿ)^{G(L/K)} → H²(G(L/K), ℤ/ℓⁿ)` by passing to
  the limit (`H¹(G(L/K), ℤ_ℓ) = 0`, `H²(G(L/K), ℤ_ℓ) ≅ H¹(G(L/K), ℚ_ℓ/ℤ_ℓ)` finite).

The main theorem of this file, `NK.Reconstruct.lemma4f1_of_transfer`, proves the two halves of
Lemma 4f.1 from the transfer input and the finiteness of `coker π̄`, so that the only unformalised
arithmetic statement left is the transfer identity itself.

## Contents

* `TransferInput π` — the named transfer input, in the form "`coker(π^*)` is killed by a power of
  `ℓ`" (equivalently, by the classical `res ∘ cor = [L : K]`);
* `lemma4f1_of_transfer` — **Lemma 4f.1**: `π^*` is injective with finite cokernel;
* the "In particular" of Shimizu's Lemma 4f.1 (documented below): the rank of the
  `G(L/K)`-invariants of `Hom_{cts}(Γ_L, ℤ_ℓ)` equals `rank_{ℤ_ℓ} Hom_{cts}(Γ_K, ℤ_ℓ)`.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. I §1.6, Ch. X §10.3;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.Reconstruct

/-- **The transfer input of Shimizu's Lemma 4f.1.**  For `π : B → A` (in the application,
`π = π̄ : (Γ_L)_{G(L/K)} → Γ_K`), the cokernel of the dual `π^* : Hom(A, ℤ_ℓ) → Hom(B, ℤ_ℓ)` is
killed by a power of `ℓ`.

Classically this is the Verlagerung (transfer) identity `res ∘ cor = [L : K]`
(CoNF (1.6.7)): the corestriction `cor` is dual to `π̄`, so `[L : K] · Hom(B, ℤ_ℓ) ⊆ im(π^*)`, and
replacing `[L : K]` by its `ℓ`-part gives an `ℓ`-power because `im(π^*)` is a `ℤ_ℓ`-submodule.  In
the applications `im(π^*) = res(...)`, so this is the statement that the restriction has
finite-index image. -/
def TransferInput {ℓ : ℕ} [Fact ℓ.Prime] {A B : Type*} [AddCommGroup A] [Module (PadicInt ℓ) A]
    [AddCommGroup B] [Module (PadicInt ℓ) B] (π : B →ₗ[PadicInt ℓ] A) : Prop :=
  ∃ n : ℕ, ∀ ψ : Module.Dual (PadicInt ℓ) B,
    (ℓ : PadicInt ℓ) ^ n • ψ ∈ LinearMap.range (LinearMap.dualMap π)

/-- The dual map, as a function: `π^* φ = φ ∘ π`. -/
theorem dualMap_apply' {ℓ : ℕ} [Fact ℓ.Prime] {A B : Type*} [AddCommGroup A]
    [Module (PadicInt ℓ) A] [AddCommGroup B] [Module (PadicInt ℓ) B]
    (π : B →ₗ[PadicInt ℓ] A) (φ : Module.Dual (PadicInt ℓ) A) :
    LinearMap.dualMap π φ = φ.comp π := rfl

/-- **Shimizu's Lemma 4f.1.**  For a `ℤ_ℓ`-linear `π : B → A` with finite cokernel and satisfying the
transfer input, the dual `π^* : Hom(A, ℤ_ℓ) → Hom(B, ℤ_ℓ)` is injective with finite cokernel
(in fact `π^*` is injective as soon as `coker π` is finite, and the finiteness of the cokernel of
`π^*` is the content of the transfer input). -/
theorem lemma4f1_of_transfer {ℓ : ℕ} [Fact ℓ.Prime] {A B : Type*}
    [AddCommGroup A] [Module (PadicInt ℓ) A] [AddCommGroup B] [Module (PadicInt ℓ) B]
    (π : B →ₗ[PadicInt ℓ] A) (hcok : Finite (A ⧸ LinearMap.range π))
    (hfg : Module.Finite (PadicInt ℓ) (Module.Dual (PadicInt ℓ) B))
    (hT : TransferInput π) :
    Function.Injective (LinearMap.dualMap π) ∧
      Finite (Module.Dual (PadicInt ℓ) B ⧸ LinearMap.range (LinearMap.dualMap π)) := by
  classical
  refine ⟨?_, ?_⟩
  · -- injectivity: `φ ∘ π = 0` and `coker π` finite force `φ = 0`
    intro φ ψ hφψ
    have h0 : (φ - ψ).comp π = 0 := by
      rw [LinearMap.sub_comp]
      rw [← dualMap_apply', ← dualMap_apply', hφψ, sub_self]
    have : φ - ψ = 0 := dual_injective_of_finite_index π hcok (φ - ψ) h0
    simpa using sub_eq_zero.mp this
  · -- finiteness of the cokernel: it is a finitely generated module killed by a power of `ℓ`
    obtain ⟨n, hn⟩ := hT
    let M := Module.Dual (PadicInt ℓ) B ⧸ LinearMap.range (LinearMap.dualMap π)
    haveI : Module.Finite (PadicInt ℓ) M := Module.Finite.quotient (PadicInt ℓ) _
    refine finite_of_fg_torsion (ℓ := ℓ) (M := M) ?_
    intro x
    refine ⟨n, ?_⟩
    obtain ⟨ψ, rfl⟩ :=
      (Submodule.mkQ_surjective (LinearMap.range (LinearMap.dualMap π))) x
    have hmem : (ℓ : PadicInt ℓ) ^ n • ψ ∈ LinearMap.range (LinearMap.dualMap π) := hn ψ
    have h0 : (Submodule.mkQ (LinearMap.range (LinearMap.dualMap π)))
        ((ℓ : PadicInt ℓ) ^ n • ψ) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hmem
    simpa only [map_smul] using h0

/-- **The "In particular" of Shimizu's Lemma 4f.1**: the `G(L/K)`-invariants of
`Hom_{cts}(Γ_L, ℤ_ℓ)` have the same `ℤ_ℓ`-rank as `Hom_{cts}(Γ_K, ℤ_ℓ)`, namely `r_ℓ(K)`.

`res = π̄^*` is injective with finite cokernel (`lemma4f1_of_transfer`); `Dual B` is a finitely
generated `ℤ_ℓ`-module, and the rank additivity
`finrank (Dual B) = finrank (range (π^*)) + finrank (coker (π^*))` together with
`finrank (coker (π^*)) = 0` (its elements are all torsion) and `range (π^*) ≅ Dual A` gives the
equality.  This is the form in which the rank computation of Shimizu's Prop. 4f.5 is consumed
(`NK.Reconstruct.eq_bot_of_rankGamma_eq`), via
`Hom(Γ_L, ℤ_ℓ)^{G(L/K)} ≅ Hom((Γ_L)_{G(L/K)}, ℤ_ℓ)`. -/
theorem lemma4f1_of_transfer_rank {ℓ : ℕ} [Fact ℓ.Prime] {A B : Type*}
    [AddCommGroup A] [Module (PadicInt ℓ) A] [AddCommGroup B] [Module (PadicInt ℓ) B]
    (π : B →ₗ[PadicInt ℓ] A) (hcok : Finite (A ⧸ LinearMap.range π))
    (hfinB : Module.Finite (PadicInt ℓ) (Module.Dual (PadicInt ℓ) B))
    (hT : TransferInput π) :
    Module.finrank (PadicInt ℓ) (Module.Dual (PadicInt ℓ) B)
      = Module.finrank (PadicInt ℓ) (Module.Dual (PadicInt ℓ) A) := by
  classical
  have hd := lemma4f1_of_transfer π hcok hfinB hT
  haveI := hd.2
  have hsplit := Submodule.finrank_quotient_add_finrank
    (R := PadicInt ℓ) (LinearMap.range (LinearMap.dualMap π))
  have hzero : Module.finrank (PadicInt ℓ)
      (Module.Dual (PadicInt ℓ) B ⧸ LinearMap.range (LinearMap.dualMap π)) = 0 := by
    rw [Module.finrank_eq_zero_iff]
    intro x
    obtain ⟨n, hn⟩ := hT
    obtain ⟨ψ, rfl⟩ := (Submodule.mkQ_surjective (LinearMap.range (LinearMap.dualMap π))) x
    have hmem : (ℓ : PadicInt ℓ) ^ n • ψ ∈ LinearMap.range (LinearMap.dualMap π) := hn ψ
    refine ⟨(ℓ : PadicInt ℓ) ^ n,
      pow_ne_zero n (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero), ?_⟩
    have h0 : (Submodule.mkQ (LinearMap.range (LinearMap.dualMap π)))
        ((ℓ : PadicInt ℓ) ^ n • ψ) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hmem
    simpa only [map_smul] using h0
  rw [hzero, zero_add] at hsplit
  have hrange : Module.finrank (PadicInt ℓ) ↥(LinearMap.range (LinearMap.dualMap π))
      = Module.finrank (PadicInt ℓ) (Module.Dual (PadicInt ℓ) A) :=
    (LinearEquiv.finrank_eq (LinearEquiv.ofInjective _ hd.1)).symm
  rw [hrange] at hsplit
  exact hsplit.symm

/- **The "In particular" of Shimizu's Lemma 4f.1** (documented form; the formal statement is
`lemma4f1_of_transfer_rank` above).

`lemma4f1_of_transfer` gives that `res = π̄^*` is injective with finite cokernel.  Both
`Hom_{cts}(Γ_K, ℤ_ℓ)` and `Hom_{cts}(Γ_L, ℤ_ℓ)^{G(L/K)} ≅ Hom((Γ_L)_{G(L/K)}, ℤ_ℓ)` are free
`ℤ_ℓ`-modules of finite rank (`moduleFree_gammaTF`, and `Module.free_of_finite_type_torsion_free`
for their duals), and a finite cokernel forces their ranks to be equal; hence

  `rank_{ℤ_ℓ} Hom_{cts}(Γ_L, ℤ_ℓ)^{G(L/K)} = rank_{ℤ_ℓ} Hom_{cts}(Γ_K, ℤ_ℓ) = r_ℓ(K)`,

which is the form in which the rank computation of Shimizu's Prop. 4f.5 is consumed
(`NK.Reconstruct.eq_bot_of_rankGamma_eq`).  The proof is the rank additivity
`finrank (Dual B) = finrank (range (π^*)) + finrank (coker (π^*))` together with
`finrank (coker (π^*)) = 0` (a finite module over `ℤ_ℓ` has rank zero) and
`range (π^*) ≅ Dual A` (injectivity). -/
end NK.Reconstruct
