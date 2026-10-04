import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-- **Smoothness of the product of a cutoff composed with a projection and a function that is smooth
on the corresponding open set.**

For a normed space `P`, a smooth projection `pr : P → (Fin n → ℝ)`, a smooth cutoff
`χ : (Fin n → ℝ) → ℝ` whose `tsupport` lies in an open set `U`, and a function `ψ : P → ℂ` that is
`C^∞` on the open set `pr ⁻¹' U`, the product `p ↦ (χ (pr p) : ℂ) * ψ p` is `C^∞` on all of `P`.

ROUTE (both reviewers' version).  `rw [contDiff_iff_contDiffAt]`, fix `p`.
* If `χ (pr p) ≠ 0` (equivalently `pr p ∈ Function.support χ ⊆ U`), then
  `pr ⁻¹' U ∈ 𝓝 p` (continuity of `pr`), so both factors are `ContDiffAt` at `p` and so is the
  product (`ContDiffAt.mul`; write the two factors with explicit types if elaboration struggles).
* Otherwise `pr p ∉ U`.  If `pr p ∈ closure (Function.support χ) = tsupport χ ⊆ U` we are in the
  first case, so `pr p ∉ tsupport χ`; the complement of the closed set `tsupport χ` is a
  neighbourhood of `pr p`, hence (by continuity of `pr`) a neighbourhood of `p` on which
  `χ ∘ pr = 0`, so the product is eventually `0` and `ContDiffAt.congr_of_eventuallyEq` with
  `contDiffAt_const` closes the goal.

A real-valued version of this is `Work.Diff.STE.B3.contDiff_mul_of_tsupport_subset`
(`Submission/Work/Diff/STE/B3/transport_exists_A.lean`) — do not import that module (it drags a file
under construction); reprove here or use
`Work.Diff.STE.Lead.Gal.contDiff_ofReal_mul_of_contDiffOn` if it is importable. -/
theorem contDiff_mul_cutoff {n : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (pr : P → (Fin n → ℝ)) (hpr : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) pr)
    (χ : (Fin n → ℝ) → ℝ) (hχsm : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) χ)
    (ψ : P → ℂ) {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    (hψ : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) ψ (pr ⁻¹' U))
    (hsupp : tsupport χ ⊆ U) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun p : P => (χ (pr p) : ℂ) * ψ p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : pr p ∈ U
  · -- `pr p ∈ U`, so `pr ⁻¹' U` is a neighbourhood of `p`: both factors are smooth at `p`.
    have hnhds : pr ⁻¹' U ∈ nhds p :=
      hpr.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hp)
    have hψ' : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) ψ p := hψ.contDiffAt hnhds
    have hχ' : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) (fun q : P => (χ (pr q) : ℂ)) p :=
      (Complex.ofRealCLM.contDiff.contDiffAt).comp p (hχsm.contDiffAt.comp p hpr.contDiffAt)
    exact hχ'.mul hψ'
  · -- `pr p ∉ U ⊇ tsupport χ`, so the first factor vanishes on a neighbourhood of `p`.
    have hnotin : pr p ∉ tsupport χ := fun h => hp (hsupp h)
    have hopen : IsOpen (tsupport χ)ᶜ := isClosed_closure.isOpen_compl
    have hnhds : pr ⁻¹' (tsupport χ)ᶜ ∈ nhds p :=
      hpr.continuous.continuousAt.preimage_mem_nhds (hopen.mem_nhds hnotin)
    refine ContDiffAt.congr_of_eventuallyEq (f := fun _ : P => (0 : ℂ)) contDiffAt_const ?_
    refine Filter.eventually_of_mem hnhds ?_
    intro q hq
    simp only [Set.mem_preimage, Set.mem_compl_iff] at hq
    show (χ (pr q) : ℂ) * ψ q = (0 : ℂ)
    rw [image_eq_zero_of_notMem_tsupport hq, Complex.ofReal_zero, zero_mul]

end Work.Diff.STE.B3
