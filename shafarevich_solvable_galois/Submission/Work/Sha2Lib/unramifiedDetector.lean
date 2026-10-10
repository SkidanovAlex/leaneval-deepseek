import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.Sha2Lib.unramifiedDetectorProved
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The unramified detector (node `C6`) for a general `p`-torsion module

**Status: closed.**  This file wires in the assembled proof of the node, which lives in
`Submission/Work/Sha2Lib/unramifiedDetectorProved.lean`
(`Work.Sha2Lib.unramifiedDetectorProved`, sorry-free, same statement).

The assembly is the chain of `_lead_design/ssg_pt_design_1002/DESIGN.md` §2 ("induce from the normal
closure of the inertia") together with the `ζ_p`-adjoin base change:

* `PTdualControl.IsUnramifiedDetector.of_baseChange` with `K' = K⟮ζ_p⟯` (so `[K' : K] ∣ p - 1`)
  reduces the node for an arbitrary `K` to the case `μ_p ⊆ K`;
* `Sha2Lib.unramifiedDetector_of_indNormal` reduces it, for `N` = the normal closure of the inertia
  at `q` (which acts trivially on `M` and fixes `ζ_p`), to the induced module
  `Ind_N^{Gal(K/k)}(res_N M)`;
* `Sha2Lib.unramifiedDetector_indNormal_of_rankOne` descends from the rank-one case `W = 𝔽_p` to an
  arbitrary trivial `p`-torsion `N`-module;
* `Work.Sha2Lib.rankOneDetectorCore` is the rank-one arithmetic crux (Grünwald over `K^N` plus the
  Shapiro–Frobenius telescope).

Contributions made from this node into that chain (all sorry-free, `declare_proven`-checked), and why
two of them have the forms they do:

* the NK entry point's two `sorry`s, now covered by sorry-free bricks:
  `Sha2Lib.residueField_cyclotomic_generated`, `Sha2Lib.inertiaDeg_cyclotomic_level`, and their
  consumer `Sha2Lib.exists_galois_unramified_extension_inertiaDeg` (a finite Galois level with a
  place of prescribed unramified inertia degree);
* `Sha2Lib.ext_comp_mk0_ne_zero_of_surjective` — the pullback of a nonzero `Ext¹(·,ℤ)` class along a
  surjection is nonzero; this is what lets detection move from the cover `Ind_N^Γ(res_N M)` to `M`
  without a splitting (the counit is not split for general `N`);
* `Sha2Lib.indRes_counit_surjective` — the counit of `Ind_N^G ⊣ res_N` is onto (`ε ⟦1 ⊗ m⟧ = m`);
* `Sha2Lib.isUnramifiedDetector_of_ind` — the transfer of the detector from `Ind_N^G(res_N M)` to `M`
  for *any* finite-index `N` (subsumes the on-disk `isUnramifiedDetector_of_induced`, the `N = D_w`
  case);
* `Sha2Lib.normalClosure_inertia_acts_trivially` — the normal closure of the inertia acts trivially
  on `M`, making `res_N M` a trivial `N`-module;
* `Sha2Lib.exists_twisted_unramified_class` — the χ-twisted unramified class (class half, rank one).
  **Its first statement was refuted in review**: χ must be trivial on the whole decomposition group
  `D_w`, not merely on the inertia — if `a = χ(Frob_q) ≠ 1` then `h|_{D_{q'}}` is inflated from
  `H¹(ℤ/f, M_a) = ker(N)/((a-1)M) = 0` for every level.  The target's own case analysis explains the
  obstruction: when `a ≠ 1` every `D_w`-equivariant functional `𝔽_p(χ) ⟶ ℚ/ℤ` vanishes, so
  `Ext¹ = 0` and the detector holds vacuously; the corrected brick is the way-station.

Two findings worth keeping:

* `SSGRoute/PING_C6_looks_false_case_B.md` is **refuted** (see
  `Submission/Work/Sha2Lib/NOTE_unramifiedDetector_analysis.md` §2): the Shapiro value formula is
  `h(δ)(x) = y(x⁻¹ δ x)`, whose commutator terms survive at non-abelian levels even when
  `p ∣ [G : D_w]`.  Explicit `D₄` witness: `k = ℚ`, `K = ℚ(i)`, `p = 2`, `q = 5`,
  `M = Ind_1^G 𝔽₂`, `L = ℚ(i,√2,√(1+i))`, where `[Frob₅, c] = τ_{1+i} ≠ 1` forces detection value
  `½ ≠ 0`, so the Case-B functional *is* detected and the only published argument against `C6` fails.
* `Submission/Work/Sha2Lib/PING_indNormal_needs_mu_p_in_K.md`: the dispatched
  `unramifiedDetector_indNormal` first stated required `ζ : K` with `IsPrimitiveRoot ζ p`, which the
  target does not supply and which is unsatisfiable for odd `p` when `ζ_p ∉ K`; the `of_baseChange`
  step of the assembled chain is what closes that gap.
-/

namespace Work.Sha2Lib

theorem unramifiedDetector (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m) :
    Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq M :=
  Work.Sha2Lib.unramifiedDetectorProved p k K Ω w q hwq hpq M hM hI

end Work.Sha2Lib
