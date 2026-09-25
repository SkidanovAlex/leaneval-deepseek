import Mathlib
import Submission.NK.Reconstruct.torsionFreeGamma
import Submission.NK.Reconstruct.not_isOpen_ker_of_infinite_range
import Submission.NK.Reconstruct.not_finite_range_of_ne_zero

/-!
# The kernel of a non-zero continuous additive map out of `Γ_K` is not open

`NK.Reconstruct.GammaTF K K' ℓ` is Shimizu's `Γ_K = (G_K^{ab,(ℓ)})/tor`, the torsion-free
quotient of the ℓ-adic abelianisation of `G_K`, realised as the quotient
`Additive (Gamma K K' ℓ) ⧸ GammaTorsion K K' ℓ` of a *compact* group by its torsion submodule.

The point of this file is the following elementary, but essential, gap-filling fact for the
reconstruction: a non-zero additive homomorphism `φ : Γ_K →+ N` landing in a torsion-free
`ℤ_ℓ`-module `N` cannot have an **open** kernel.

Mathematically: `Γ_K` is a quotient of the compact group `Γ_K^{ab,(ℓ)} = Gamma K K' ℓ`; the group
`Gamma K K' ℓ` is a closed subgroup of a product of finite discrete groups, hence compact and
Hausdorff.  The torsion-free module `N` has infinite `ℤ`-orbits: for `x` with `φ x ≠ 0` the map
`n ↦ n • (φ x)` (`n : ℤ`) is injective, because `(n - m) • φ x = 0` forces `((n-m) : ℤ_ℓ) = 0`
and `ℤ_ℓ` has no zero divisors.  So `φ` has infinite range.  If `ker φ` were open in `Γ_K`, its
preimage under the quotient map `q : Gamma K K' ℓ → Γ_K` would be an open additive subgroup of the
compact group `Gamma K K' ℓ`, hence of finite index; the first isomorphism theorem would then make
`range φ = range (φ ∘ q)` finite.  Contradiction.

Note that no continuity of `φ` is used (only the quotient map's continuity and the compactness of
the limit), so the statement is proved in the strength requested.

## Contents

* `not_finite_range_of_ne_zero_add` — the additive form of
  `NK.Reconstruct.not_finite_range_of_ne_zero`: a non-zero additive homomorphism into a
  torsion-free `ℤ_ℓ`-module has infinite range (the existing lemma is stated for `ℤ_ℓ`-linear maps
  and is therefore not directly applicable here, where `φ` is only assumed additive);
* `not_isOpen_ker_gammaTF_addHom` — the requested statement.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. X §10.3, Ch. XII §12.1–2;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.Reconstruct

/-- **A non-zero additive homomorphism into a torsion-free `ℤ_ℓ`-module has infinite range.**

If `f x ≠ 0`, the `ℤ`-orbit `n ↦ n • f x` is injective: `(n - m) • f x = 0` implies
`((n - m) : ℤ_ℓ) • f x = 0`, hence `((n - m) : ℤ_ℓ) = 0` by torsion-freeness, hence `n = m`.
The orbit is contained in the range of `f`, and `ℤ` is infinite.

This is the additive counterpart of `NK.Reconstruct.not_finite_range_of_ne_zero`, which is
stated for `ℤ_ℓ`-linear maps; `f` here is only additive. -/
theorem not_finite_range_of_ne_zero_add {ℓ : ℕ} [Fact ℓ.Prime] {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Module (PadicInt ℓ) B] [Module.IsTorsionFree (PadicInt ℓ) B]
    (f : A →+ B) (hf : f ≠ 0) : ¬ Finite (f.range : AddSubgroup B) := by
  intro hfin
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hf
  simp only [AddMonoidHom.zero_apply] at hx
  -- the `ℤ`-orbit of `f x` is injective, since `B` is torsion-free over `ℤ_ℓ`
  have hg : Function.Injective (fun n : ℤ => n • f x) := by
    intro n m hnm
    have hnm' : n • f x = m • f x := hnm
    have h : (n - m) • f x = 0 := by rw [sub_smul, hnm', sub_self]
    have h3 : ((n - m : ℤ) : PadicInt ℓ) • f x = 0 := by
      rw [Int.cast_smul_eq_zsmul]; exact h
    have h2 : ((n - m : ℤ) : PadicInt ℓ) = 0 := by
      rcases smul_eq_zero.mp h3 with h' | h'
      · exact h'
      · exact absurd h' hx
    exact sub_eq_zero.mp (Int.cast_injective h2)
  -- hence the range of `f`, which contains the orbit, is infinite
  have hinj : Function.Injective
      (fun n : ℤ => (⟨n • f x, ⟨n • x, map_zsmul f n x⟩⟩ : f.range)) :=
    fun n m h => hg (Subtype.ext_iff.mp h)
  exact (Infinite.of_injective _ hinj).not_finite hfin

/-- **The kernel of a non-zero additive homomorphism out of `Γ_K` into a torsion-free
`ℤ_ℓ`-module is not open.**  See the module docstring for the argument. -/
theorem not_isOpen_ker_gammaTF_addHom {K : Type*} [Field K] [NumberField K] {K' : Type*}
    [Field K'] [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) [Fact ℓ.Prime] {N : Type*}
    [AddCommGroup N] [Module (PadicInt ℓ) N] [Module.IsTorsionFree (PadicInt ℓ) N]
    [TopologicalSpace N] [T1Space N] (φ : GammaTF (K := K) (K' := K') ℓ →+ N) (hcont : Continuous φ)
    (hφ : φ ≠ 0) :
    ¬ IsOpen ((φ.ker : AddSubgroup (GammaTF (K := K) (K' := K') ℓ)) :
      Set (GammaTF (K := K) (K' := K') ℓ)) := by
  -- `φ` has infinite range because `N` is torsion-free over the domain `ℤ_ℓ`
  have hinf : ¬ Finite (φ.range : AddSubgroup N) :=
    not_finite_range_of_ne_zero_add (ℓ := ℓ) φ hφ
  intro hopen
  -- `Γ_K` is the quotient of the compact group `Gamma K K' ℓ` by its torsion submodule
  set S : Submodule (PadicInt ℓ) (Additive (Gamma K K' ℓ)) := GammaTorsion (K := K) (K' := K') ℓ
    with hS
  have hqsurj :
      Function.Surjective (S.mkQ : Additive (Gamma K K' ℓ) → Additive (Gamma K K' ℓ) ⧸ S) :=
    S.mkQ_surjective
  have hqcont : Continuous (S.mkQ : Additive (Gamma K K' ℓ) → Additive (Gamma K K' ℓ) ⧸ S) :=
    Submodule.continuous_mkQ S
  -- the kernel of the composite is the preimage of the kernel of `φ`
  have hker : (((φ.comp S.mkQ.toAddMonoidHom).ker : AddSubgroup (Additive (Gamma K K' ℓ))) :
      Set (Additive (Gamma K K' ℓ)))
      = (S.mkQ : Additive (Gamma K K' ℓ) → _) ⁻¹'
          ((φ.ker : AddSubgroup (GammaTF (K := K) (K' := K') ℓ)) :
            Set (GammaTF (K := K) (K' := K') ℓ)) := by
    ext x
    simp [AddMonoidHom.mem_ker]
  -- so an open kernel of `φ` would give an open additive subgroup of the compact group
  have hopen' : IsOpen (((φ.comp S.mkQ.toAddMonoidHom).ker :
      AddSubgroup (Additive (Gamma K K' ℓ))) : Set (Additive (Gamma K K' ℓ))) := by
    rw [hker]
    exact hopen.preimage hqcont
  -- an open additive subgroup of a compact group has finite index, so the quotient is finite
  haveI : DiscreteTopology (Additive (Gamma K K' ℓ) ⧸ (φ.comp S.mkQ.toAddMonoidHom).ker) :=
    QuotientAddGroup.discreteTopology hopen'
  have hfinQ : Finite (Additive (Gamma K K' ℓ) ⧸ (φ.comp S.mkQ.toAddMonoidHom).ker) :=
    finite_of_compact_of_discrete
  -- and the first isomorphism theorem transfers finiteness to the range of the composite
  have hfinrange : Finite ((φ.comp S.mkQ.toAddMonoidHom).range : AddSubgroup N) :=
    (QuotientAddGroup.quotientKerEquivRange (φ.comp S.mkQ.toAddMonoidHom)).finite_iff.mp hfinQ
  -- the range of the composite is the range of `φ`, since the quotient map is surjective
  have hrange : ((φ.comp S.mkQ.toAddMonoidHom).range : AddSubgroup N) = φ.range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨S.mkQ y, rfl⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨y, rfl⟩ := hqsurj z
      exact ⟨y, rfl⟩
  rw [hrange] at hfinrange
  exact hinf hfinrange

end NK.Reconstruct
