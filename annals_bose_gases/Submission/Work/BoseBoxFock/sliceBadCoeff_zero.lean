import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.SliceBadCoeffAux
import Submission.Work.BoseBoxFock.sector_XSpow_width_holds_kf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

/-- **`ExcWindow`, step 6 of the BF3c pipeline: the slice has no "bad" monomials.**
`sliceF e S (Φ:ℂ) y` is the slice of the `V`-sector `slotExact e S Φ` at the complement
configuration `y` (a function of the `S.card` `S`-slots).  Its expansion in the symmetric mode
products `M_α = modeProd e S.card α` has coefficient `∫_u conj (M_α u) · slice_y u`; the statement
says this coefficient vanishes, *in `L²(dy)`*, for every multi-index of total degree `S.card`
whose *excited slot count* `S.card − α 0` (the number of slots carrying a mode `≠ e 0`) exceeds
`⌊M⌋₊`.

Proof route (verified by hand; `FINDING_BF3c_selection_s9.md` §2 has the derivation; the
`ℂ`-valued slot mean `aPC` and its API are already in `slotCountsComplex.lean`):

* **(E1) the pinning + the labelling count.**  `hc` gives `e 0 = c·θ_Λ` (`|c|² = ℓ⁻³`), so the
  slot mean `aP_i` (`Submission.BoseGases.aP`, the mean over the cube) *is* the `e 0`-slot
  projection `|e 0⟩⟨e 0|_i`.  Every labelling `σ : Fin d → Fin m` with `modeMult σ = α` has
  exactly `α 0` zero slots, so **summing over the slots** gives
  `(Σ_{i : Fin d} aPC ℓ i) M_α = α 0 · M_α`, i.e. `X_d M_α = (d − α 0) M_α` for
  `X_d := d − Σ_i aPC ℓ i`.  ⚠ The *per-slot* identity `aP_i M_α = (α 0/d)M_α` is **FALSE**
  (`d = 2`, `α = e_0+e_1`); do not try to prove it.
* **(E2) the sector operator bound.**  On the `S`-sector, `X_S := Σ_{i∈S} (1 − aP_i)` equals
  `n₊ − (n − d)` (the complement slots are in `W = V^⊥ ⊥ θ`, hence all excited).  The sibling
  `Work.BoseBoxFock.jointProj_vanish` (in flight; the `ha` step of `thetaSector_vanish.lean`)
  kills every joint `θ`-sector with `|W| > M`, and the `V`-sector projection is a contraction
  (`slotExact_comp` + `slotExact_orth_gen`), so `∫ Θ X_S^k Θ ≤ M^k ∫ |Θ|²` for every `k` at
  `Θ = slotExact e S Φ`.  (The corpus's `Work.BoseFixB2.jointProj` is stated for `X n → ℝ`; use
  the pointwise real/imaginary parts of `Θ`, on which the real joint projections act, or a
  `ℂ`-valued twin.)
* **(E3) Fubini over the complement configuration** — the analogue of
  `slotSum_sectorPointwise` (whose proof is the template: `update_pairCoord` +
  `integral_pairCoord_split` + linearity): `X_S^k` acts on the `S`-slots only, so its form at `Θ`
  is `∫_y (the form at slice_y)`.
* **(E4) the geometric limit.**  With `ν_bad(y)` the mass of the spectral part of `slice_y` with
  `X_d`-eigenvalue `≥ ⌊M⌋₊ + 1 > M`, (E2)+(E3) give `(⌊M⌋₊+1)^k ∫ν_bad ≤ M^k ∫ν` for every `k`,
  hence `∫_y ν_bad = 0`: the bad part vanishes a.e.
* **(E5) conclusion.**  `X_d` is diagonal with eigenvalue `d − α 0` in the (cIPn-orthogonal,
  `modeProd_cIPn`) monomial basis, so `∫_y ν_bad = 0` is exactly the claim.

No symmetry hypothesis on `Φ` is needed (do **not** route through `sliceF_symm` /
`exists_boxRealiseC_eq_sliceF`, which require `∀σ, Φ ∘ σ = Φ`). -/
theorem sliceBadCoeff_zero (ℓ : ℝ) (hℓ : 0 < ℓ) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : Continuous Φ) (hΦc : tsupport Φ ⊆ Submission.BoseGases.abox n ℓ)
    {M : ℝ} (hM : 0 ≤ M) (hmom : Work.BoseBox.SpectralNPlusLe ℓ M Φ)
    {m : ℕ} [NeZero m] {e : Fin m → Work.BoseDict.Sp → ℂ}
    (he : ∀ l l', (∫ x : Work.BoseDict.Sp, (starRingEnd ℂ) (e l x) * e l' x)
      = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
        e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    (S : Finset (Fin n)) (α : Fin m →₀ ℕ)
    (hdeg : α.sum (fun _ k => k) = S.card)
    (hbad : ((S.card - α 0 : ℕ) : ℝ) > (⌊M⌋₊ : ℝ)) :
    ∫ y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3),
      ‖∫ u : Fin S.card → EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
          * sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y u‖ ^ 2 = 0 := by
  refine sliceBadCoeff_zero_aux ℓ hℓ hΦ hΦc hM he hbdd hsupp hc S α hbad
    (Bval := ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
    (integral_nonneg (fun x => sq_nonneg (Φ x))) ?_
  intro j
  exact sector_XSpow_width_holds_kf ℓ hℓ S hΦ hΦc hM hmom he hbdd hsupp hc j

end Work.BoseBoxFock
