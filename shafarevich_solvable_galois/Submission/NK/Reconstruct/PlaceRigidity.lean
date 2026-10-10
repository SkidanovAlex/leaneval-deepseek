import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.NK.Reconstruct.InnerTwist
import Submission.NK.Reconstruct.comap_placeMap_eq_of_realizesPlaceMap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The honest remaining input of the reconstruction: place-preserving automorphisms come from field
automorphisms

The reconstruction step asks for `σ : K₂' ≃+* K₁'` with `MapsBase` and `Conjugates σ ϕ` (equivalently,
by `NK.Reconstruct.exists_realizing_sigma_of_conj_normal`, hypothesis (d) of
`Submission.NeukirchUchida.exists_sigma_of_reconstruction`).

Given the **σ-free local correspondence** `a : LocalCorrespondence ϕ` (input (a)) and *some*
`MapsBase` isomorphism `σ₀ : K₂' ≃+* K₁'` (the *weak* half of Neukirch–Uchida: the base fields are
isomorphic), the content of the reconstruction is the *obstruction*
`β := Φ_{σ₀} ∘ ϕ⁻¹ ∈ Aut(Gal(K₂'/K₂))`, `Φ_{σ₀} := conjHomEquiv hσ₀` (`InnerTwist.lean`).  This
file proves that

* `β` **preserves the place system**: the image of every decomposition group of a place over a
  finite prime is again the decomposition group of such a place
  (`NK.Reconstruct.exists_decompositionGroup_map_eq`);
* hence the reconstruction follows from the rigidity of the place system in its *correct* form:

  `NK.Reconstruct.PlaceRigidity K K'` — *every automorphism `ψ` of the absolute Galois group
  `Gal(K'/K)` which maps the family of decomposition groups of the places over the finite primes of
  `K` to itself is of the form `conjHomEquiv h_c` for some field automorphism `c : K' ≃+* K'` which
  preserves the embedded copy of `K` (`MapsBase`)*.

**Attribution of the correction.**  The *inner* form of the rigidity statement is **false**: for any
number field `K` with `Aut(K) ≠ 1` (e.g. `K = ℚ(i)`), lift a nontrivial automorphism to
`c : K' ≃+* K'`; then `conjHomEquiv h_c` preserves the place family (by
`map_conjHomEquiv_decompositionGroup`), but it is not inner, because if `conjHomEquiv h_c = MulAut.conj x`
with `x ∈ Gal(K'/K)` then `c` and `x` are two solutions of `Conjugates · (conjHomEquiv h_c)` and hence
equal by `Submission.NeukirchUchida.unique_sigma` (`centralizer_trivial`), contradicting that `c` moves
`K` while `x` fixes it.  The statement above is the correct (and still sufficient) form: the *field*
automorphism part is genuinely needed, and it cancels in the twist of `σ₀` below.

Reference: M. Jarden, J. Ritter, *On the characterization of local fields by their absolute Galois
groups*; J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, XII §12.1–§12.2.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace NK.Reconstruct

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The obstruction `β = Φ_{σ₀} ∘ ϕ⁻¹` preserves the place system of `K₂'`.**

For every place `B` of `K₂'` over a finite prime of `K₂` there is a place `B'` of `K₂'` over a finite
prime of `K₂` with `β(D_B) = D_{B'}`.

The proof is the place correspondence (a): write `B = a(A)`; then `ϕ⁻¹(D_B) = D_A`, and
`Φ_{σ₀}(D_A) = D_{A.comap σ₀}`. -/
theorem exists_decompositionGroup_map_eq {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (a : LocalCorrespondence ϕ) {σ₀ : K₂' ≃+* K₁'}
    (hσ₀ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ₀)
    (B : FinitePlaceOf K₂ K₂') :
    ∃ B' : FinitePlaceOf K₂ K₂',
      (Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B.1).map
        (((ϕ.symm.trans (Submission.NeukirchUchida.conjHomEquiv hσ₀) :
          Gal(K₂'/K₂) ≃* Gal(K₂'/K₂))) : Gal(K₂'/K₂) →* Gal(K₂'/K₂)) =
      Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B'.1 := by
  obtain ⟨A, rfl⟩ := a.placeMap.surjective B
  refine ⟨⟨A.1.comap (σ₀ : K₂' →+* K₁'), comap_sigma_comap_ne_top hσ₀ A.2⟩, ?_⟩
  have hcomp : (((ϕ.symm.trans (Submission.NeukirchUchida.conjHomEquiv hσ₀) :
        Gal(K₂'/K₂) ≃* Gal(K₂'/K₂))) : Gal(K₂'/K₂) →* Gal(K₂'/K₂)) =
      ((Submission.NeukirchUchida.conjHomEquiv hσ₀) : Gal(K₁'/K₁) →* Gal(K₂'/K₂)).comp
        (ϕ.symm : Gal(K₂'/K₂) →* Gal(K₁'/K₁)) := rfl
  rw [hcomp, ← Subgroup.map_map]
  have h1 : (Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂')
        (a.placeMap A).1).map (ϕ.symm : Gal(K₂'/K₂) →* Gal(K₁'/K₁)) =
      Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A.1 :=
    Submission.NeukirchUchida.map_symm_map_eq (a.map_decomp A)
  rw [h1, map_conjHomEquiv_decompositionGroup hσ₀ A.1]

/-- **Right composition with a `K₂`-preserving automorphism of `K₂'` preserves `MapsBase`.**

This is the generalisation of `NK.Reconstruct.mapsBase_trans` from elements of `Gal(K₂'/K₂)` to
arbitrary field automorphisms carrying the embedded copy of `K₂` to itself. -/
theorem mapsBase_trans_mapsBase (c : K₂' ≃+* K₂')
    (hc : Submission.NeukirchUchida.MapsBase (algebraMap K₂ K₂') (algebraMap K₂ K₂') c)
    (σ₀ : K₂' ≃+* K₁')
    (hσ₀ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ₀) :
    Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂')
      (c.symm.trans σ₀) := by
  rw [Submission.NeukirchUchida.MapsBase] at hσ₀ hc ⊢
  have hcs : (algebraMap K₂ K₂').range.map (c.symm : K₂' →+* K₂') =
      (algebraMap K₂ K₂').range :=
    Submission.NeukirchUchida.mapsBase_symm (algebraMap K₂ K₂') (algebraMap K₂ K₂') hc
  ext y
  constructor
  · intro hy
    rcases Subring.mem_map.mp hy with ⟨x, hx, hxy⟩
    have hx' : c.symm x ∈ (algebraMap K₂ K₂').range := by
      rw [← hcs]
      exact Subring.mem_map.mpr ⟨x, hx, rfl⟩
    have hxy' : σ₀ (c.symm x) = y := by
      change (c.symm.trans σ₀) x = y at hxy
      rwa [RingEquiv.trans_apply] at hxy
    rw [← hxy', ← hσ₀]
    exact Subring.mem_map.mpr ⟨c.symm x, hx', rfl⟩
  · intro hy
    rw [← hσ₀] at hy
    rcases Subring.mem_map.mp hy with ⟨z, hz, hzy⟩
    have hz' : c z ∈ (algebraMap K₂ K₂').range := by
      rw [← hc]
      exact Subring.mem_map.mpr ⟨z, hz, rfl⟩
    refine Subring.mem_map.mpr ⟨c z, hz', ?_⟩
    change (c.symm.trans σ₀) (c z) = y
    rw [RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
    exact hzy

/-- **The rigidity of the place system** — the honest remaining input of the reconstruction.

Every automorphism `ψ` of `Gal(K'/K)` carrying the family of decomposition groups of the places of
`K'` over the finite primes of `K` to itself is *induced by a field automorphism* of `K'` preserving
the embedded copy of `K`: `ψ = conjHomEquiv h_c` for some `c : K' ≃+* K'` with
`MapsBase (algebraMap K K') (algebraMap K K') c`.

(It is **not** true — and this is essential — that such a `ψ` is necessarily *inner*: for
`K = ℚ(i)` the conjugation by a lift of the nontrivial automorphism of `K` preserves the place
system but is not an inner automorphism of `Gal(K'/K)`; see the module docstring.)  With the weak
half `K₁ ≅ K₂`, this statement yields the realizing `σ` outright
(`exists_conjugates_of_placeRigidity`). -/
def PlaceRigidity (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K']
    [Algebra K K'] [IsSepClosure K K'] : Prop :=
  ∀ ψ : Gal(K'/K) ≃* Gal(K'/K),
    (∀ B : ValuationSubring K', B.comap (algebraMap K K') ≠ ⊤ →
      ∃ B' : ValuationSubring K', B'.comap (algebraMap K K') ≠ ⊤ ∧
        (Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') B).map
          (ψ : Gal(K'/K) →* Gal(K'/K)) =
        Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') B') →
    ∃ (c : K' ≃+* K') (hc : Submission.NeukirchUchida.MapsBase (algebraMap K K') (algebraMap K K') c),
      ψ = Submission.NeukirchUchida.conjHomEquiv hc

/-- **The reconstruction from the weak half plus the rigidity of the place system.**

Given the σ-free local correspondence `a : LocalCorrespondence ϕ` (input (a)) and *some* base-field
mapping isomorphism `σ₀ : K₂' ≃+* K₁'` (the *weak* half of Neukirch–Uchida: `K₁ ≅ K₂`), the
rigidity of the place system of `K₂'` produces a field isomorphism inducing `ϕ`:

  `∃ σ : K₂' ≃+* K₁', Conjugates σ ϕ`.

No Čebotarev input, no abelianised/rank input and no homeomorphism hypothesis is used.  The proof:
the obstruction `Φ_{σ₀} ∘ ϕ⁻¹` preserves the place system (`exists_decompositionGroup_map_eq`), so by
`PlaceRigidity` it is `conjHomEquiv h_c` for some `K₂`-preserving `c : K₂' ≃+* K₂'`; then
`σ := σ₀ ∘ c⁻¹` is `MapsBase` (`mapsBase_trans_mapsBase`) and
`Φ_σ(g) = c Φ_{σ₀}(g) c⁻¹ = c (c⁻¹ ∘ ϕ g ∘ c) c⁻¹ = ϕ g`, so `Conjugates σ ϕ`. -/
theorem exists_conjugates_of_placeRigidity {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (a : LocalCorrespondence ϕ) {σ₀ : K₂' ≃+* K₁'}
    (hσ₀ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ₀)
    (hrig : PlaceRigidity K₂ K₂') :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  have hpres : ∀ B : ValuationSubring K₂', B.comap (algebraMap K₂ K₂') ≠ ⊤ →
      ∃ B' : ValuationSubring K₂', B'.comap (algebraMap K₂ K₂') ≠ ⊤ ∧
        (Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B).map
          ((ϕ.symm.trans (Submission.NeukirchUchida.conjHomEquiv hσ₀) :
            Gal(K₂'/K₂) ≃* Gal(K₂'/K₂)) : Gal(K₂'/K₂) →* Gal(K₂'/K₂)) =
        Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B' := by
    intro B hB
    obtain ⟨B', hB'⟩ := exists_decompositionGroup_map_eq a hσ₀ ⟨B, hB⟩
    exact ⟨B'.1, B'.2, hB'⟩
  obtain ⟨c, hc, hψ⟩ := hrig _ hpres
  refine ⟨c.symm.trans σ₀, mapsBase_trans_mapsBase c hc σ₀ hσ₀, fun g => ?_⟩
  -- pointwise form of `hψ`: `Φ_{σ₀}(ϕ⁻¹ u) = conjHomEquiv hc u`
  have hpt : ∀ u : Gal(K₂'/K₂),
      Submission.NeukirchUchida.conjHomEquiv hσ₀ (ϕ.symm u) =
        Submission.NeukirchUchida.conjHomEquiv hc u := by
    intro u
    have := DFunLike.congr_fun hψ u
    simpa [MulEquiv.trans_apply] using this
  have hg : Submission.NeukirchUchida.conjHomEquiv hσ₀ g =
      Submission.NeukirchUchida.conjHomEquiv hc (ϕ g) := by
    simpa using hpt (ϕ g)
  have key : ∀ y : K₂', (Submission.NeukirchUchida.conjHomEquiv hσ₀ g) (c.symm y)
      = c.symm ((ϕ g) y) := by
    intro y
    rw [hg]
    change (Submission.NeukirchUchida.conj hc (ϕ g)) (c.symm y) = c.symm ((ϕ g) y)
    rw [Submission.NeukirchUchida.conj_apply]
    simp
  ext x
  have hmain : ((c.symm.trans σ₀).trans (g.toRingEquiv.trans (c.symm.trans σ₀).symm)) x
      = (ϕ g : K₂' ≃+* K₂') x := by
    calc ((c.symm.trans σ₀).trans (g.toRingEquiv.trans (c.symm.trans σ₀).symm)) x
        = c ((Submission.NeukirchUchida.conjHomEquiv hσ₀ g) (c.symm x)) := by
          simp only [RingEquiv.trans_apply, RingEquiv.symm_trans_apply, AlgEquiv.coe_ringEquiv,
            AlgEquiv.toRingEquiv_symm]
          rfl
      _ = (ϕ g) x := by
          rw [key]
          exact c.apply_symm_apply ((ϕ g) x)
  exact hmain.symm

end NK.Reconstruct
