/-
# Corollary `FirstDerivativeCoercivity`: the base case of the `ℋ¹` coercivity

Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the incompressible
Euler equations on `ℝ³`*, Annals of Math. **194** (2021), Corollary
`FirstDerivativeCoercivity`: for `α < 10⁻¹⁴`,

  `(𝓛_Γ^T f, f)_{ℋ¹} ≥ |f|²_{ℋ¹}`,

i.e. `Eztheta1 α f ≤ H1IP α (LGammaT α f) f`, where `|f|²_{ℋ¹} = E_{z,θ}¹(f)` is
`Eztheta1` (`Eztheta1_eq_HkSq_one`) and `(·,·)_{ℋ¹}` is `H1IP`.  This is the base case of
the paper's inductive construction of the inner products `(·,·)_{ℋ^k}`
(`Work.Coercivity.HkShape`).

## The proof

The `ℋ¹` inner product has the four pairings

  `10 (D_z𝓛_Γ^T f, D_z f w²/sin^η) + 10¹⁰ (𝓛_Γ^T f, f w²/sin^η)
     + 10¹⁷ (𝓛_Γ^T f, f w²) + 10²¹ (D_θ𝓛_Γ^T f, D_θ f w²/sin^γ)`,

and the corresponding coercivity estimates of the chapter are

* `dzCoercivityAux` below (the paper's `D_z`-estimate, reproduced here from
  `zDerivative.lean`; see the remark on `Z3Clean` below),
* `L2CoercivityTransportEta` (the `sin(2θ)^{-η}`-weighted `L²` estimate),
* `L2TransportSharp` (the plain `L²` estimate — a *sharpened* version of
  `L2CoercivityTransport`, whose error constant `10⁴` is too large for this bookkeeping;
  `L2TransportSharp` proves the constant `1000`),
* `thetaDerivative` (the `D_θ`-estimate),

together with `EL12z_le` (`|z⁻¹L₁₂f|² ≤ 16|fw|²`) and `EDthW_le_EDth`.  Multiplying them
by `10, 10¹⁰, 10¹⁷, 10²¹` respectively and adding, the resulting coefficients
`5/2, 10⁹, 2.9·10¹⁵, 1` on `EDz`, `EfEta`, `Ef` and `EDth` all dominate the corresponding
coefficients of `|f|²_{ℋ¹}`; this is `firstDerivativeAssembly`, and the only place where
`α ≤ 10⁻¹⁴` is used is to absorb `10²¹α ≤ 10⁷` and `10²⁸α ≤ 10³` (the `α`-error of
`thetaDerivative`).

## Remarks on the workspace

* `zZ3.lean` (which proves the `Z₃` bound consumed by the `D_z`-estimate) cannot be
  imported here: it clashes with `L2CoercivityTransportEta` on `aesm_L12f` — and, even once
  that is fixed, with `bound_Z5.lean` and `T4aux.lean` on `Pzθ` and `measurable_w`.  The
  module `Work.Coercivity.Z3Clean` is a copy of `zZ3.lean` in the fresh namespace
  `Work.Coercivity.Z3Clean`, which sidesteps all three clashes; its `Z3_bound` is the input
  `hZ3` of `dzCoercivityAux`.
* `zQuad.lean` clashes with `thetaDerivative.lean` on `wip_congr_ae`, so the two
  `wip`-lemmas of `zQuad` needed here are reproduced below as `wip_int_add_aux` and
  `ae_quad_pos_mem` (using `wip_add_left` of `wip_Aop_ge.lean` and the `wip_congr_ae` of
  `thetaDerivative.lean` in place of the `zQuad` versions).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.firstTransportCoercivity
import Submission.Work.Coercivity.Eztheta1_eq_HkSq_one
import Submission.Work.Coercivity.EL12z_le
import Submission.Work.Coercivity.HardyWeight
import Submission.Work.Coercivity.L2CoercivityTransportEta
import Submission.Work.Coercivity.thetaDerivative
import Submission.Work.Coercivity.f_sq_w_sq_integrable
import Submission.Work.Coercivity.Ef_le_EfEta
import Submission.Work.Coercivity.zAux
import Submission.Work.Coercivity.Dz_LGammaT_decomp
import Submission.Work.Coercivity.bd0_Dz
import Submission.Work.Coercivity.coerc_LZ6_Dz
import Submission.Work.Coercivity.bound_Z2
import Submission.Work.Coercivity.bound_Z4
import Submission.Work.Coercivity.bound_Z5
import Submission.Work.Coercivity.bound_Z7
import Submission.Work.Coercivity.C0_sq_le4
import Submission.Work.Coercivity.Z3Clean
import Submission.Work.Coercivity.L2TransportSharp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Nonnegativity of the energies -/

theorem edz_nonneg_aux (f : ℝ → ℝ → ℝ) : 0 ≤ EDz f := by
  rw [EDz, Spaces.L2Sq]
  exact integral_nonneg (fun z => integral_nonneg (fun θ => sq_nonneg _))

theorem edth_nonneg_aux (α : ℝ) (f : ℝ → ℝ → ℝ) : 0 ≤ EDth α f := by
  rw [EDth, Spaces.L2Sq]
  exact integral_nonneg (fun z => integral_nonneg (fun θ => sq_nonneg _))

theorem efeta_nonneg_aux (f : ℝ → ℝ → ℝ) : 0 ≤ EfEta f := by
  rw [EfEta, Spaces.L2Sq]
  exact integral_nonneg (fun z => integral_nonneg (fun θ => sq_nonneg _))

theorem ef_nonneg_aux (f : ℝ → ℝ → ℝ) : 0 ≤ Ef f := by
  rw [Ef, Spaces.L2Sq]
  exact integral_nonneg (fun z => integral_nonneg (fun θ => sq_nonneg _))


/-! ## The two elementary `IntegrableOn`/`wip` lemmas of `zQuad`

`Submission/Work/Coercivity/zQuad.lean` proves the additivity lemmas for `wip` that the
`D_z`-estimate uses, but it also declares a `wip_congr_ae` whose name clashes with the
one of `thetaDerivative.lean`; the two modules can therefore not be imported together.
The two lemmas needed here are reproduced under fresh names (with `wip_add_left` of
`wip_Aop_ge.lean` in place of `zQuad`'s `wip_add`). -/

/-- Additivity of `IntegrableOn` for the `wip` integrands. -/
theorem wip_int_add_aux (ρ A B g : ℝ → ℝ → ℝ)
    (hA : IntegrableOn
      (Function.uncurry (fun z θ => A z θ * g z θ * ρ z θ)) (Spaces.Iz ×ˢ Spaces.Iθ))
    (hB : IntegrableOn
      (Function.uncurry (fun z θ => B z θ * g z θ * ρ z θ)) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    IntegrableOn
      (Function.uncurry (fun z θ => (A z θ + B z θ) * g z θ * ρ z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
  refine (hA.add hB).congr (Filter.Eventually.of_forall (fun p => ?_))
  simp only [Function.uncurry_def, Pi.add_apply]
  ring

/-- Almost every point of the quadrant (with respect to the restricted measure on
`Iz ×ˢ Iθ`) has positive first coordinate and second coordinate in `Iθ`. -/
theorem ae_quad_pos_mem :
    ∀ᵐ p ∂(volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)),
      0 < p.1 ∧ p.2 ∈ Spaces.Iθ := by
  have hvol : volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)
      = (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict _ _).symm
  rw [hvol]
  filter_upwards [ae_prod_quadrant, ae_prod_pos] with p hp hpos
  exact ⟨hpos, hp.2⟩

/-! ## The `D_z`-coercivity estimate -/

/-- The paper's Proposition "`L²` coercivity for `𝓛_Γ^T` with one `z`-derivative":

  `(1/4)·|D_z f · w/√sin(2θ)^η|² - 10⁸·E_θ¹ ≤ (D_z𝓛_Γ^T f, D_z f · w²/sin(2θ)^η)_{L²}`.

The proof expands `D_z(𝓛_Γ^T f)` into the seven terms `Z₁,…,Z₇` of `zAux` and estimates
each one: the coercive pair `Z₁ + Z₆` (`coerc_LZ6_Dz`), `Z₂` (`bound_Z2`), `Z₃` (the
hypothesis `hZ3`, which is `Z3Clean.Z3_bound`), `Z₄`, `Z₅` and `Z₇`.  It is the argument of
`Submission/Work/Coercivity/zDerivative.lean`, restated here with the `Z₃` bound as an
explicit argument so that this file does not have to import `zZ3.lean` (which does not
currently build). -/
theorem dzCoercivityAux (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : IBP f) (hfH : HardyHyp f) (hi : CoerciveData α f)
    (hZ3 : MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Z3 α f z θ * Spaces.Dz f z θ * Weta z θ))
        (Spaces.Iz ×ˢ Spaces.Iθ)
      ∧ wip Weta (Z3 α f) (Spaces.Dz f) ≥ -((1 / 32) * EDz f + 10 ^ 6 * Ef f)) :
    (1 / 4) * EDz f - 10 ^ 8 * Etheta1 α f
      ≤ wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
          (Spaces.Dz (LGammaT α f)) (Spaces.Dz f) := by
  -- ## integrability data
  have hFw : IntegrableOn (Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    refine (f_sq_w_sq_integrable α f hi).congr ?_
    filter_upwards with p
    simp only [Function.uncurry_def]; ring
  have hC0 : (C0 f) ^ 2 ≤ 32 * Ef f := by
    have h4 : (C0 f) ^ 2 ≤ 4 * Ef f := C0_sq_le4 f hf.smooth hFw
    linarith [h4, ef_nonneg_aux f]
  have hdec : ∀ z θ, 0 < z → θ ∈ Spaces.Iθ →
      Spaces.Dz (LGammaT α f) z θ = SumI α f z θ := Dz_LGammaT_decomp α f hf.smooth hfH
  have hG2 : IntegrableOn (Function.uncurry (fun z θ =>
      (Spaces.Dz f z θ * Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    refine hi.intDz.congr ?_
    filter_upwards with p
    simp only [Function.uncurry_def]; ring
  -- ## the individual bounds
  obtain ⟨hZ2i, hZ2⟩ := bound_Z2 α f hi
  obtain ⟨hZ3i, hZ3⟩ := hZ3
  obtain ⟨hZ4i, hZ4⟩ := bound_Z4 α hα hα1 f hfH hi
  obtain ⟨hZ5i, hZ5⟩ := bound_Z5 α hα hα1 f hi
  obtain ⟨hZ7i, hZ7⟩ := bound_Z7 α hα hα1 f hi hC0
  -- ## a.e. positivity of `z` and interiority of `θ`
  have hz_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Spaces.Iz), 0 < z := by
    rw [Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici, MeasureTheory.ae_iff]
    have hset : {z : ℝ | ¬ (z ∈ Set.Ici (0 : ℝ) → 0 < z)} = {0} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_Ici, Set.mem_singleton_iff, not_imp]
      constructor
      · rintro ⟨h1, h2⟩; exact le_antisymm (not_lt.mp h2) h1
      · rintro rfl; exact ⟨le_refl 0, lt_irrefl 0⟩
    rw [hset, Real.volume_singleton]
  have hθ_ae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
    rw [Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
    have hset : {θ : ℝ | ¬ (θ ∈ Set.Icc (0 : ℝ) (π / 2) → θ ∈ Set.Ioo 0 (π / 2))}
        = ({0} : Set ℝ) ∪ {π / 2} := by
      ext θ
      simp only [Set.mem_setOf_eq, Set.mem_Icc, Set.mem_Ioo, Set.mem_union,
        Set.mem_singleton_iff, not_imp]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        rcases not_and_or.mp h3 with h | h
        · left; exact le_antisymm (not_lt.mp h) h1
        · right; exact le_antisymm h2 (not_lt.mp h)
      · rintro (rfl | rfl)
        · exact ⟨⟨le_refl 0, by positivity⟩, by simp⟩
        · exact ⟨⟨by positivity, le_refl _⟩, by simp⟩
    rw [hset]
    exact MeasureTheory.measure_union_null (by rw [Real.volume_singleton])
      (by rw [Real.volume_singleton])
  -- ## integrability of the partial sums
  have hZ57 : IntegrableOn (Function.uncurry (fun z θ =>
      (Z5 f z θ + Z7 α f z θ) * Spaces.Dz f z θ * Weta z θ)) (Spaces.Iz ×ˢ Spaces.Iθ) :=
    wip_int_add_aux Weta (Z5 f) (Z7 α f) (Spaces.Dz f) hZ5i hZ7i
  have hZ457 : IntegrableOn (Function.uncurry (fun z θ =>
      (Z4 α f z θ + (Z5 f z θ + Z7 α f z θ)) * Spaces.Dz f z θ * Weta z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ) :=
    wip_int_add_aux Weta (Z4 α f) (fun z θ => Z5 f z θ + Z7 α f z θ) (Spaces.Dz f) hZ4i hZ57
  have hZ3457 : IntegrableOn (Function.uncurry (fun z θ =>
      (Z3 α f z θ + (Z4 α f z θ + (Z5 f z θ + Z7 α f z θ))) * Spaces.Dz f z θ * Weta z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ) :=
    wip_int_add_aux Weta (Z3 α f) (fun z θ => Z4 α f z θ + (Z5 f z θ + Z7 α f z θ))
      (Spaces.Dz f) hZ3i hZ457
  have hZ23457 : IntegrableOn (Function.uncurry (fun z θ =>
      (Z2 f z θ + (Z3 α f z θ + (Z4 α f z θ + (Z5 f z θ + Z7 α f z θ))))
        * Spaces.Dz f z θ * Weta z θ)) (Spaces.Iz ×ˢ Spaces.Iθ) :=
    wip_int_add_aux Weta (Z2 f) (fun z θ => Z3 α f z θ + (Z4 α f z θ + (Z5 f z θ + Z7 α f z θ)))
      (Spaces.Dz f) hZ2i hZ3457
  have hSumI : IntegrableOn (Function.uncurry (fun z θ =>
      SumI α f z θ * Spaces.Dz f z θ * Weta z θ)) (Spaces.Iz ×ˢ Spaces.Iθ) := by
    refine hi.intDzDz.congr ?_
    filter_upwards [ae_quad_pos_mem] with p hp
    simp only [Function.uncurry_def, Weta]
    rw [hdec p.1 p.2 hp.1 hp.2]
    ring
  have hZ16 : IntegrableOn (Function.uncurry (fun z θ =>
      Z16 f z θ * Spaces.Dz f z θ * Weta z θ)) (Spaces.Iz ×ˢ Spaces.Iθ) := by
    refine (hSumI.sub hZ23457).congr (Filter.Eventually.of_forall (fun p => ?_))
    simp only [Function.uncurry_def, Pi.sub_apply]
    have h : SumI α f p.1 p.2 = Z16 f p.1 p.2
        + (Z2 f p.1 p.2 + (Z3 α f p.1 p.2 + (Z4 α f p.1 p.2
          + (Z5 f p.1 p.2 + Z7 α f p.1 p.2)))) := by
      simp only [SumI, Z16]; ring
    rw [h]; ring
  -- ## the coercive part
  have hcoerc : (47 / 100) * EDz f ≤ wip Weta (Z16 f) (Spaces.Dz f) :=
    coerc_LZ6_Dz f hf.smooth (bd0_Dz f hf) hZ16 hG2
  -- ## splitting the sum
  have hsplit : wip Weta (SumI α f) (Spaces.Dz f)
      = wip Weta (Z16 f) (Spaces.Dz f) + wip Weta (Z2 f) (Spaces.Dz f)
        + wip Weta (Z3 α f) (Spaces.Dz f) + wip Weta (Z4 α f) (Spaces.Dz f)
        + wip Weta (Z5 f) (Spaces.Dz f) + wip Weta (Z7 α f) (Spaces.Dz f) := by
    rw [wip_congr_ae (ρ := Weta) (g₁ := SumI α f)
          (g₁' := fun z θ => Z16 f z θ
            + (Z2 f z θ + (Z3 α f z θ + (Z4 α f z θ + (Z5 f z θ + Z7 α f z θ)))))
          (g₂ := Spaces.Dz f)
          (Filter.Eventually.of_forall (fun _ => Filter.Eventually.of_forall (fun _ =>
            by simp only [SumI, Z16]; ring)))]
    rw [wip_add_left (ρ := Weta) (g := Z16 f) (k := Spaces.Dz f)
          (h := fun z θ => Z2 f z θ
            + (Z3 α f z θ + (Z4 α f z θ + (Z5 f z θ + Z7 α f z θ)))) hZ16 hZ23457]
    rw [wip_add_left (ρ := Weta) (g := Z2 f) (k := Spaces.Dz f)
          (h := fun z θ => Z3 α f z θ
            + (Z4 α f z θ + (Z5 f z θ + Z7 α f z θ))) hZ2i hZ3457]
    rw [wip_add_left (ρ := Weta) (g := Z3 α f) (k := Spaces.Dz f)
          (h := fun z θ => Z4 α f z θ + (Z5 f z θ + Z7 α f z θ)) hZ3i hZ457]
    rw [wip_add_left (ρ := Weta) (g := Z4 α f) (k := Spaces.Dz f)
          (h := fun z θ => Z5 f z θ + Z7 α f z θ) hZ4i hZ57]
    rw [wip_add_left (ρ := Weta) (g := Z5 f) (k := Spaces.Dz f) (h := Z7 α f) hZ5i hZ7i]
    ring
  -- ## arithmetic
  have hbound : (47 / 100 - 1 / 64 - 1 / 32 - 1 / 32 - 1 / 32 - 1 / 32) * EDz f
        - (4 * EfEta f + (10 ^ 6 + 10 ^ 7 + 10 ^ 7) * Ef f + 10 * EDth α f)
      ≤ wip Weta (SumI α f) (Spaces.Dz f) := by
    rw [hsplit]
    linarith [hcoerc, hZ2, hZ3, hZ4, hZ5, hZ7]
  have hfinal : (1 / 4) * EDz f - 10 ^ 8 * Etheta1 α f
      ≤ (47 / 100 - 1 / 64 - 1 / 32 - 1 / 32 - 1 / 32 - 1 / 32) * EDz f
        - (4 * EfEta f + (10 ^ 6 + 10 ^ 7 + 10 ^ 7) * Ef f + 10 * EDth α f) := by
    rw [Etheta1_eq]
    have hEf : Ef f ≤ EfEta f := Ef_le_EfEta α f hi
    have hEDz := edz_nonneg_aux f
    have hEDth := edth_nonneg_aux α f
    nlinarith [hEf, hEDz, hEDth]
  calc (1 / 4) * EDz f - 10 ^ 8 * Etheta1 α f
      ≤ (47 / 100 - 1 / 64 - 1 / 32 - 1 / 32 - 1 / 32 - 1 / 32) * EDz f
        - (4 * EfEta f + (10 ^ 6 + 10 ^ 7 + 10 ^ 7) * Ef f + 10 * EDth α f) := hfinal
    _ ≤ wip Weta (SumI α f) (Spaces.Dz f) := hbound
    _ = wip Weta (Spaces.Dz (LGammaT α f)) (Spaces.Dz f) := by
      refine wip_congr_ae (ρ := Weta) (g₁ := SumI α f)
        (g₁' := Spaces.Dz (LGammaT α f)) (g₂ := Spaces.Dz f) ?_
      filter_upwards [hz_ae] with z hz
      filter_upwards [hθ_ae] with θ hθ
      exact (hdec z θ hz ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩).symm

/-! ## The numerical bookkeeping -/

/-- **The numerical bookkeeping of Corollary `FirstDerivativeCoercivity`.**

Given the four coercivity estimates of the chapter for the four pairings occurring in
the paper's `ℋ¹` inner product — the `D_z`-estimate (`dzCoercivityAux`), the
`sin(2θ)^{-η}`-weighted `L²` estimate (`L2CoercivityTransportEta`), the plain `L²`
estimate in its sharpened form with error constant `10³` (`L2TransportSharp`) and the
`D_θ`-estimate (`thetaDerivative`) — together with the two finite-dimensional inputs
`EL12z_le`, `EDthW_le_EDth`, the `ℋ¹` energy is dominated by `(𝓛_Γ^T f, f)_{ℋ¹}`.

The bookkeeping: multiplying the four estimates by the coefficients `10`, `10¹⁰`, `10¹⁷`
and `10²¹` of `H1IP` gives a lower bound for the right-hand side whose coefficients are

* `10·(1/4) = 5/2 ≥ 1` on `EDz` (against the errors `10⁹(EDth + EfEta)` of `hP`),
* `10¹⁰·(1/5) - 10⁹ = 10⁹ ≥ 1` on `EfEta`,
* `10²¹·(1/4) - 10⁹ - 10¹⁵ - 10²⁰ ≥ 1` on `EDth` (the errors `10⁹`, `10¹⁵`, `10²⁰` come
  from `hP`, from the `EDthW`-error of `hQ` and from the sharpened `EDthW`-error of `hR`,
  the latter through `EDthW ≤ EDth`), using only `α ≤ 10⁻¹⁴` to absorb `10²¹α ≤ 10⁷` and
  `10²⁸α ≤ 10¹⁴`,
* `10¹⁷·(1/5) - 10¹⁵·16 - 10¹⁵ - 10¹⁴ = 2.9·10¹⁵ ≥ 0` on `Ef` (the errors `10¹⁵·16`
  and `10¹⁵` come from the `EL12z`- and `Ef`-errors of `hQ`, and `10¹⁴` from the
  `α`-error of `hS`). -/
theorem firstDerivativeAssembly (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hP : (1 / 4) * EDz f - 10 ^ 8 * Etheta1 α f
      ≤ wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
          (Spaces.Dz (LGammaT α f)) (Spaces.Dz f))
    (hQ : (1 / 5) * EfEta f - 100000 * (EL12z f + EDthW f + Ef f)
      ≤ wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
          (LGammaT α f) f)
    (hR : (1 / 5) * Ef f - 1000 * EDthW f
      ≤ wip (fun z _ => Spaces.w z ^ 2) (LGammaT α f) f)
    (hS : (1 / 4 - α) * EDth α f - 10 ^ 7 * α * Ef f
      ≤ wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
          (Spaces.Dth (LGammaT α f)) (Spaces.Dth f))
    (hEL : EL12z f ≤ 16 * Ef f) (hED : EDthW f ≤ EDth α f)
    (hα1 : α ≤ 1 / 10 ^ 14) (hTn : 0 ≤ EDth α f) (hFn : 0 ≤ Ef f)
    (hDn : 0 ≤ EDz f) (hThn : 0 ≤ EfEta f) :
    Eztheta1 α f ≤ H1IP α (LGammaT α f) f := by
  rw [H1IP, Eztheta1]
  -- name the four pairings of `H1IP`
  set P := wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (Spaces.Dz (LGammaT α f)) (Spaces.Dz f) with hPdef
  set Q := wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (LGammaT α f) f with hQdef
  set Rr := wip (fun z _ => Spaces.w z ^ 2) (LGammaT α f) f with hRrdef
  set S := wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
      (Spaces.Dth (LGammaT α f)) (Spaces.Dth f) with hSdef
  -- ## the four estimates, rescaled to the coefficients of `H1IP`
  have h1 : (5 / 2) * EDz f - 10 ^ 9 * EDth α f - 10 ^ 9 * EfEta f ≤ 10 * P := by
    have h := mul_le_mul_of_nonneg_left hP (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)
    have key : (10 : ℝ) * ((1 / 4) * EDz f - 10 ^ 8 * Etheta1 α f)
        = (5 / 2) * EDz f - 10 ^ 9 * Etheta1 α f := by ring
    rw [key, Etheta1_eq] at h
    linarith
  have h2 : 2 * 10 ^ 9 * EfEta f - 10 ^ 15 * EL12z f - 10 ^ 15 * EDthW f - 10 ^ 15 * Ef f
      ≤ (10 : ℝ) ^ 10 * Q := by
    have h := mul_le_mul_of_nonneg_left hQ (show (0 : ℝ) ≤ (10 : ℝ) ^ 10 by norm_num)
    have key : (10 : ℝ) ^ 10 * ((1 / 5) * EfEta f - 100000 * (EL12z f + EDthW f + Ef f))
        = 2 * 10 ^ 9 * EfEta f - 10 ^ 15 * EL12z f - 10 ^ 15 * EDthW f - 10 ^ 15 * Ef f := by
      ring
    rw [key] at h
    exact h
  have h3 : 2 * 10 ^ 16 * Ef f - 10 ^ 20 * EDthW f ≤ (10 : ℝ) ^ 17 * Rr := by
    have h := mul_le_mul_of_nonneg_left hR (show (0 : ℝ) ≤ (10 : ℝ) ^ 17 by norm_num)
    have key : (10 : ℝ) ^ 17 * ((1 / 5) * Ef f - 1000 * EDthW f)
        = 2 * 10 ^ 16 * Ef f - 10 ^ 20 * EDthW f := by ring
    rw [key] at h
    exact h
  have h4 : (10 : ℝ) ^ 21 * ((1 / 4 - α) * EDth α f) - 10 ^ 28 * α * Ef f
      ≤ (10 : ℝ) ^ 21 * S := by
    have h := mul_le_mul_of_nonneg_left hS (show (0 : ℝ) ≤ (10 : ℝ) ^ 21 by norm_num)
    have key : (10 : ℝ) ^ 21 * ((1 / 4 - α) * EDth α f - 10 ^ 7 * α * Ef f)
        = (10 : ℝ) ^ 21 * ((1 / 4 - α) * EDth α f) - 10 ^ 28 * α * Ef f := by ring
    rw [key] at h
    exact h
  -- ## the finite-dimensional inputs, rescaled
  have h5 : 10 ^ 15 * EL12z f ≤ 10 ^ 15 * 16 * Ef f := by
    have h := mul_le_mul_of_nonneg_left hEL (show (0 : ℝ) ≤ (10 : ℝ) ^ 15 by norm_num)
    nlinarith [h]
  have h6 : 10 ^ 15 * EDthW f ≤ 10 ^ 15 * EDth α f := by
    have h := mul_le_mul_of_nonneg_left hED (show (0 : ℝ) ≤ (10 : ℝ) ^ 15 by norm_num)
    nlinarith [h]
  have h7 : 10 ^ 20 * EDthW f ≤ 10 ^ 20 * EDth α f := by
    have h := mul_le_mul_of_nonneg_left hED (show (0 : ℝ) ≤ (10 : ℝ) ^ 20 by norm_num)
    nlinarith [h]
  -- ## the two constants coming from `α ≤ 10⁻¹⁴`
  have hαp : 10 ^ 21 * α ≤ 10 ^ 7 := by
    have h := mul_le_mul_of_nonneg_left hα1 (show (0 : ℝ) ≤ (10 : ℝ) ^ 21 by norm_num)
    have h2 : (10 : ℝ) ^ 21 * (1 / 10 ^ 14) = 10 ^ 7 := by norm_num
    linarith [h, h2]
  have hαq : 10 ^ 28 * α ≤ 10 ^ 14 := by
    have h := mul_le_mul_of_nonneg_left hα1 (show (0 : ℝ) ≤ (10 : ℝ) ^ 28 by norm_num)
    have h2 : (10 : ℝ) ^ 28 * (1 / 10 ^ 14) = 10 ^ 14 := by norm_num
    linarith [h, h2]
  have hTcoef : (10 : ℝ) ^ 9 + 10 ^ 15 + 10 ^ 20 + 1
      ≤ (10 : ℝ) ^ 21 * (1 / 4 - α) := by
    nlinarith [hαp]
  have hTscaled : ((10 : ℝ) ^ 9 + 10 ^ 15 + 10 ^ 20 + 1) * EDth α f
      ≤ (10 : ℝ) ^ 21 * ((1 / 4 - α) * EDth α f) := by
    have h := mul_le_mul_of_nonneg_right hTcoef hTn
    have he : ((10 : ℝ) ^ 21 * (1 / 4 - α)) * EDth α f
        = (10 : ℝ) ^ 21 * ((1 / 4 - α) * EDth α f) := by ring
    linarith [h, he]
  have hFscaled : 10 ^ 28 * α * Ef f ≤ 10 ^ 14 * Ef f := by
    have h := mul_le_mul_of_nonneg_right hαq hFn
    nlinarith [h]
  -- ## assembly
  have htot : (5 / 2) * EDz f + 10 ^ 9 * EfEta f + 2.9 * 10 ^ 15 * Ef f + EDth α f
      ≤ 10 * P + (10 : ℝ) ^ 10 * Q + (10 : ℝ) ^ 17 * Rr + (10 : ℝ) ^ 21 * S := by
    linarith
  linarith [htot, hDn, hThn, hFn]

/-! ## The base case of the `ℋ¹` coercivity -/

/-- **Corollary `FirstDerivativeCoercivity` of the paper**: the `ℋ¹` inner product of
`𝓛_Γ^T f` with `f` dominates the `ℋ¹` energy of `f`, `|f|²_{ℋ¹} = E_{z,θ}¹(f)`.

It is the bookkeeping of `firstDerivativeAssembly`, fed with

* the `D_z`-estimate `dzCoercivityAux` (whose `Z₃`-input is `Z3Clean.Z3_bound`),
* the `sin(2θ)^{-η}`-weighted `L²` estimate `L2CoercivityTransportEta`,
* the plain `L²` estimate in its sharpened form `L2TransportSharp`,
* the `D_θ`-estimate `thetaDerivative`,
* and the finite-dimensional inputs `EL12z_le` and `EDthW_le_EDth`. -/
theorem FirstDerivativeCoercivity (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14) (f : ℝ → ℝ → ℝ)
    (hf : IBP f) (hfH : HardyHyp f) (hΓ : GammaL2Bnd α) (hΓ2 : GammaPointwiseBnd α)
    (hi : CoerciveData α f) (hmem : Spaces.HkMem α 1 f) (hs : Spaces.SmoothNbhd f) :
    Eztheta1 α f ≤ H1IP α (LGammaT α f) f := by
  have hα1' : α ≤ 1 := le_trans hα1 (by norm_num)
  have hfw : IntegrableOn (Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    refine (f_sq_w_sq_integrable α f hi).congr ?_
    filter_upwards with p
    simp only [Function.uncurry_def]; ring
  have hEL : EL12z f ≤ 16 * Ef f := EL12z_le f hfH hfw
  have hED : EDthW f ≤ EDth α f := EDthW_le_EDth α hα f hi
  have hP := dzCoercivityAux α hα hα1' f hf hfH hi (Z3Clean.Z3_bound α hα hα1' f hfH hi)
  have hQ := L2CoercivityTransportEta α hα hα1' f hf hfH hΓ hi
  have hR := L2TransportSharp α hα hα1' f hf hfH hΓ hi
  have hS := thetaDerivative α hα hα1' f hf hfH hΓ hΓ2 hi
  exact firstDerivativeAssembly α f hP hQ hR hS hEL hED hα1
    (edth_nonneg_aux α f) (ef_nonneg_aux f) (edz_nonneg_aux f) (efeta_nonneg_aux f)

end Work.Coercivity
