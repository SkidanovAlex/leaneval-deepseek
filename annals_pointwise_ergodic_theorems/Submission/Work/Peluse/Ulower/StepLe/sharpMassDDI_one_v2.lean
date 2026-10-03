import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.ddiSharp.ddiSharp_one

namespace Work.Peluse.Ulower.StepLe

/-
**The `σ = 1` base case of the mass form of the interchange** (`SharpMassDDI 1`,
`StepLe/ddiSharp/Defs.lean`), i.e. the Gram/energy ("Frobenius") argument in the `B`-normalisation:
there is `C > 0` with

  `C⁻¹ (hypoMass 1 B G H φ)² / D ≤ concMass 1 D B G H φ`

for every `1 ≤ L, 1 ≤ D, L + 1 * D ≤ B`, every `1`-bounded translate-supported family
`G : Z → ℤ → ℂ` and every phase `φ` on the shift pairs of `H ⊆ [1,D]²`.

**This is now the ONLY missing piece of the mass-form route to the target
`Work.Peluse.Ulower.degree_lowering_v2`**: the dimension step
`Work.Peluse.Ulower.StepLe.sharpMassDDI_step` is PROVED (axiom-clean), so
`SharpMassDDI 1` + that step give `SharpMassDDI σ` for all `σ ≥ 1`, hence (through
`StepLe/hasInterchangeL_of_sharpMass.lean`) `HasInterchangeL P`, hence `StepLe.blindConvertK2`,
hence the target.

## Route of the proof

The statement is proved in full in the module `StepLe/ddiSharp/ddiSharp_one.lean` (theorem
`Work.Peluse.Ulower.StepLe.ddiSharp.ddiSharp_one`), whose dependency chain
`StepLe/ddiSharp/one/{Defs, hypoMass_eq_sum, concMass_eq_sum, rowGram_local, tsum_avgNormSq_le}`
is complete and axiom-clean; the present theorem is that proof, re-exported under the name
requested by the mass-form route, so that
`StepLe/hasInterchangeL_of_sharpMass.lean` can import the base case from either name.

For the record, the argument carried out there is:

* decompose `H = ⊔_{a ∈ [1,D]} {a} × R_a` with `R_a = thetaFibre D H a`
  (`hypoMass 1 B G H φ = Σ_a Σ_{q ∈ R_a}‖B⁻¹Σ_x e(φ(a,q)x)·(E_zG_z)(x+a)·(E_zG_z)(x+q)‖²`), and
  `concMass 1 D B G H φ = Σ_a Σ_{q,q' ∈ R_a×R_a}‖B⁻¹Σ_x e((φ(a,q)-φ(a,q'))x)·
  E_z[G z (x+q)·star (G z (x+q'))]‖²` (`ThetaSet 1 D H = ⊔_a {a}×R_a×R_a`);
  these are the resummations `hypoMass_eq_sum` / `concMass_eq_sum`;
* per row `a`, the energy inequality `(Σ_{q∈R_a}‖c_q‖²)² ≤ (Σ_{q,q'∈R_a²}‖g_{q,q'}‖²)·‖W_a‖⁴` with
  `c_q = ⟨u_q, W_a⟩` (`absorption_identity`); it is the content of
  `Work.Peluse.Ulower.rowGram_bound` (`Ulower/rowGram_bound.lean`, PROVED — stated in exactly this
  `∑'`/`star`/`M⁻¹` vocabulary) and of its `ℓ²(Z × ℤ)`-form `rowGram_local`, with the test vector
  `W_a = star ((E_zG_z)(·+a))`, whose norm is the averaged `B⁻²Σ_x‖(E_zG_z)(x+a)‖²` and is bounded
  by `2L + 1 ≤ 3B` (support in `symIcc L`, `1`-boundedness of the slices, `B ≥ L + D`), i.e.
  `tsum_avgNormSq_le`;
* Cauchy–Schwarz over the rows: `(Σ_a m_a)² ≤ D·Σ_a m_a²` (at most `D` rows), giving
  `(hypoMass)² ≤ 9 D concMass`, i.e. `C = 9` and `d₁ = 1`;
* the only normalisation change relative to `Ulower/dualDiffInterchange_one.lean` (the same
  statement in the `L`-normalisation, PROVED) is `L⁻¹ → B⁻¹` throughout, which is where the
  `‖W_a‖² ≤ 2L+1 ≤ 3B` bound on the test vector is used.
-/
theorem sharpMassDDI_one_v2 : Work.Peluse.Ulower.StepLe.SharpMassDDI 1 :=
  Work.Peluse.Ulower.StepLe.ddiSharp.ddiSharp_one

end Work.Peluse.Ulower.StepLe
