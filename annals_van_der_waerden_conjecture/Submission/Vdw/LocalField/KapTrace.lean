import Submission.Vdw.LocalField.TraceResidue
open Classical
open scoped NumberField WithZero Valued Polynomial
set_option autoImplicit false
set_option linter.style.haveILetI false
open scoped NumberField WithZero Valued Polynomial
set_option autoImplicit false
set_option linter.style.haveILetI false
/-!
# KapTrace — residue-side trace of the Teichmüller generator

Second lemma-family of the residue-trace reduction (stone-4 follow-up):

* `kapPowerBasis` — a power basis of `κ := kap p P` over `𝔽_p` with
  generator `α` (from the linear independence of the first `f` powers of a
  generator `α` of `κ^×`, `f = P.inertiaDeg ℤ`);
* `kap_trace_gen_eq_neg_nextCoeff` — `Tr_{κ/𝔽_p}(α) = -(nextCoeff m)` for
  `m = minpoly (ZMod p) α`;
* `minpoly_reduction_eq_map` — `m = g.map (qpReductionHom p)` with
  `g = teichMinpolyInt p P α` (both monic irreducible of degree `f`);
* `kap_trace_eq_reduction` — **RT1**: `Tr_{κ/𝔽_p}(α) = φ(-(nextCoeff g))`,
  the mod-`p` reduction (by `φ = qpReductionHom p` on the integral
  representative `-g.nextCoeff`) of the integer trace of `ζ`
  (cf. `TraceResidue.tr_zeta_int`, which identifies
  `Tr_{W/ℚ_p}(ζ) = -(g.nextCoeff : QpAdic p)`).

All statements: axioms = propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw.LocalField
noncomputable section
universe u
variable {K : Type u} [Field K] [NumberField K]

/-- power basis of κ over ZMod p with gen = α, dim = f. -/
noncomputable def kapPowerBasis (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    PowerBasis (ZMod p) (kap p P) := by
  classical
  let f : ℕ := P.inertiaDeg ℤ
  let v : Fin f → kap p P := fun i => α ^ (i : ℕ)
  have hli : LinearIndependent (ZMod p) v := by
    dsimp [v]
    exact kap_generator_powers_linearIndependent (p := p) (P := P) (α := α) hα hgen
  haveI : Module.Finite (ZMod p) (kap p P) := Module.Finite.of_finite
  have hspan_card : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range v)) = f := by
    simpa [v] using (finrank_span_eq_card hli)
  have hfinK : Module.finrank (ZMod p) (kap p P) = f := by
    simpa [f] using (kap_finrank (p := p) (P := P))
  have hspan_top : Submodule.span (ZMod p) (Set.range v) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hspan_card]
    exact hfinK.symm
  let B : Module.Basis (Fin f) (ZMod p) (kap p P) :=
    Module.Basis.mk hli (by simp [hspan_top])
  exact {
    gen := α
    dim := f
    basis := B
    basis_eq_pow := by
      intro i
      change B i = α ^ (i : ℕ)
      simp [B, v, Module.Basis.mk_apply]
  }

/-- trace of the generator α of κ^× over 𝔽_p: -(nextCoeff minpoly α). -/
theorem kap_trace_gen_eq_neg_nextCoeff (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    Algebra.trace (ZMod p) (kap p P) α = -((minpoly (ZMod p) α).nextCoeff) := by
  classical
  let pb : PowerBasis (ZMod p) (kap p P) := kapPowerBasis p P hα hgen
  have ht := PowerBasis.trace_gen_eq_nextCoeff_minpoly pb
  simpa [pb, kapPowerBasis] using ht

/-- minimal polynomial of α over 𝔽_p equals the reduction of the ℤ_[p]-minimal
polynomial of ζ. -/
theorem minpoly_reduction_eq_map (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    minpoly (ZMod p) α = (teichMinpolyInt p P α).map (qpReductionHom p) := by
  classical
  let m : Polynomial (ZMod p) := minpoly (ZMod p) α
  let g : Polynomial (ZMod p) := (teichMinpolyInt p P α).map (qpReductionHom p)
  haveI : Module.Finite (ZMod p) (kap p P) := Module.Finite.of_finite
  have hm_mon : m.Monic := minpoly.monic (IsIntegral.of_finite (ZMod p) α)
  have hg_mon : g.Monic := (teichMinpolyInt_monic p P hα).map (qpReductionHom p)
  have hdvd : m ∣ g := by
    dsimp [m, g]
    exact minpoly_dvd_reduction (p := p) (P := P) (α := α) hα hgen
  have hgdeg : g.natDegree = P.inertiaDeg ℤ := by
    dsimp [g]
    calc
      (Polynomial.map (qpReductionHom p) (teichMinpolyInt p P α)).natDegree =
          (teichMinpolyInt p P α).natDegree :=
        (teichMinpolyInt_monic p P hα).natDegree_map (qpReductionHom p)
      _ = (minpoly (QpAdic p) (((teich p P α : kpInt p P) : kpAdic p P))).natDegree := by
        rw [teich_minpoly_eq_field_map p P hα]
        exact ((teichMinpolyInt_monic p P hα).natDegree_map (algebraMap (QpInt p) (QpAdic p))).symm
      _ = P.inertiaDeg ℤ := teich_minpoly_natDegree_eq_inertiaDeg (p := p) (P := P) (α := α) hα hgen
  have hmdeg : m.natDegree = P.inertiaDeg ℤ := by
    dsimp [m]
    exact kap_minpoly_natDegree_of_generator (p := p) (P := P) (α := α) hα hgen
  have hdeg : g.natDegree ≤ m.natDegree := by
    rw [hgdeg, hmdeg]
  have heq : g = m := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hm_mon hg_mon hdvd hdeg
  exact heq.symm

/-- κ-side trace = the mod-p reduction of the integral trace of ζ:
`Tr_{κ/𝔽_p}(α) = φ(-(nextCoeff g))`, `g = teichMinpolyInt`, `φ = qpReductionHom`. -/
theorem kap_trace_eq_reduction (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    Algebra.trace (ZMod p) (kap p P) α =
      qpReductionHom p (-((teichMinpolyInt p P α).nextCoeff)) := by
  classical
  calc
    Algebra.trace (ZMod p) (kap p P) α
        = -((minpoly (ZMod p) α).nextCoeff) :=
          kap_trace_gen_eq_neg_nextCoeff p P hα hgen
    _ = -(((teichMinpolyInt p P α).map (qpReductionHom p)).nextCoeff) := by
          rw [minpoly_reduction_eq_map p P hα hgen]
    _ = qpReductionHom p (-((teichMinpolyInt p P α).nextCoeff)) := by
          have hnc : ((teichMinpolyInt p P α).map (qpReductionHom p)).nextCoeff =
              qpReductionHom p ((teichMinpolyInt p P α).nextCoeff) :=
            Polynomial.nextCoeff_map_eq_of_isUnit_leadingCoeff (qpReductionHom p)
              (by simp [Polynomial.Monic.leadingCoeff (teichMinpolyInt_monic p P hα)])
          rw [hnc]
          exact (map_neg (qpReductionHom p) ((teichMinpolyInt p P α).nextCoeff)).symm


/-- **Residue–trace reduction (RT2)**: with `ζ ∈ 𝒪_W` the Teichmüller
generator whose residue is `α` (`OWBasic.resOW_hom_zeta`) and whose
`W/ℚ_p`-trace is the integral element `-g.nextCoeff ∈ QpInt`
(`TraceResidue.tr_zeta_int`), the trace over the residue field `κ` of the
residue of `ζ` equals the mod-`p` reduction of the integral trace of `ζ`:
`Tr_{κ/𝔽_p}(resOW ζ) = φ(-(nextCoeff g))` (`φ = qpReductionHom p`). -/
theorem trace_reduction_zeta (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    Algebra.trace (ZMod p) (kap p P) (resOW_hom p P α (zetaOW p P α)) =
      qpReductionHom p (-((teichMinpolyInt p P α).nextCoeff)) := by
  rw [resOW_hom_zeta p P α]
  exact kap_trace_eq_reduction p P hα hgen

end
end Submission.Vdw.LocalField
