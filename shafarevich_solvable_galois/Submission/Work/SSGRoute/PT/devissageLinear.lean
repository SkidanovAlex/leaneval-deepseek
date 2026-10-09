import Mathlib
import Submission.Work.SSGRoute.PT.akSESLinear
import Submission.Work.SSGRoute.PT.DevissageSESFinal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `𝔽_p`-linearity of the dévissage short exact sequence

`PT/DevissageSESFinal.devissageSES` produces the short exact sequence
`0 → M →^{ι} Coind^G_U M →^{π} M₁ → 0` of Milne's dévissage.  The `𝔽_p`-linearity machinery of
`PT/akZmodLinear.lean` / `PT/akSESLinear.lean` (the `ebot` block, and `δm`-linearity via
`delta_smul`) needs:

* a `𝔽_p`-module structure on `Coind^G_U M` and on the cokernel `M₁` (neither exists in the tree —
  the same situation as for `Z¹_c` before `PTembedding.instModuleZ1c`), and
* `𝔽_p`-linearity of `devissageIota` and `devissagePi`.

This file supplies all four, so that `AKZmodLin.exact_transpMapH1_of_zmod`,
`exact_transpDelta_delta` and `exact_transpInvariants_delta` apply to `devissageSES`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open Classical

namespace Work.SSGRoute.PT

namespace AKZmodLin

universe u

section CoindModule

variable {G : Type u} [Group G] {U : Subgroup G} {p : ℕ}
  {M : Type u} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
  [SMulCommClass G (ZMod p) M]

/-- **The `𝔽_p`-module structure on `Coind^G_U M`** (pointwise), the analogue of
`PTembedding.instModuleZ1c` for the coinduced module. -/
noncomputable instance instModuleCoind : Module (ZMod p) (Coind G U M) where
  smul c f := ⟨c • (f : G → M), fun g u => by
    rw [Pi.smul_apply, Pi.smul_apply, f.2 g u]
    exact (smul_comm (((u : U) : G)⁻¹) c (f g)).symm⟩
  one_smul f := Subtype.ext (one_smul (ZMod p) (f : G → M))
  mul_smul c d f := Subtype.ext (mul_smul c d (f : G → M))
  smul_zero c := Subtype.ext (smul_zero c)
  smul_add c f g := Subtype.ext (smul_add c (f : G → M) (g : G → M))
  add_smul c d f := Subtype.ext (add_smul c d (f : G → M))
  zero_smul f := Subtype.ext (zero_smul (ZMod p) (f : G → M))

/-- The scalar action of `instModuleCoind` is pointwise. -/
@[simp] theorem instModuleCoind_coe_smul (c : ZMod p) (f : Coind G U M) :
    ((c • f : Coind G U M) : G → M) = c • (f : G → M) := rfl

/-- The value of the dévissage inclusion. -/
@[simp] theorem devissageIota_apply (m : M) (x : G) :
    ((devissageIota U m : Coind G U M) : G → M) x = x⁻¹ • m := rfl

/-- **`devissageIota` is `𝔽_p`-linear.** -/
theorem devissageIota_smul (c : ZMod p) (m : M) :
    devissageIota U (c • m) = c • devissageIota U m := by
  refine Subtype.ext (funext fun x => ?_)
  simp only [instModuleCoind_coe_smul, Pi.smul_apply, devissageIota_apply]
  exact smul_comm x⁻¹ c m

/-- The `G`-action and the `𝔽_p`-action on `Coind^G_U M` commute. -/
noncomputable instance instSMulCommClassCoind : SMulCommClass G (ZMod p) (Coind G U M) where
  smul_comm g c f := by
    refine Subtype.ext (funext fun x => ?_)
    simp only [Work.SSGRoute.PT.AKZmodLin.instModuleCoind_coe_smul, Pi.smul_apply,
      Coind.smul_apply]

end CoindModule

section QuotModule

variable {G : Type u} [Group G] {U : Subgroup G} {p : ℕ}
  {M : Type u} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
  [SMulCommClass G (ZMod p) M]

/-- The `𝔽_p`-scalar action on the cokernel `M₁ = Coind^G_U M ⧸ range ι`, by `Quotient.liftOn`
along the stability of `range ι` (`devissageIota_smul`) — the `ZMod p`-analogue of the
`instSMulQuot` of `PT/DevissageSESQuot.lean`. -/
noncomputable instance instSMulZModM1 : SMul (ZMod p) (devissageM1 (M := M) U) where
  smul c q := Quotient.liftOn q
    (fun f => QuotientAddGroup.mk' (devissageIota U).range (c • f)) (by
      intro f f' h
      have h' : -f + f' ∈ (devissageIota U).range := QuotientAddGroup.leftRel_apply.mp h
      obtain ⟨m, hm⟩ := h'
      refine (QuotientAddGroup.eq (s := (devissageIota U).range)).mpr ?_
      exact ⟨c • m, by rw [devissageIota_smul, hm, smul_add, smul_neg]⟩)

/-- **The `𝔽_p`-module structure on the cokernel `M₁` of the dévissage.** -/
noncomputable instance instModuleM1 : Module (ZMod p) (devissageM1 (M := M) U) where
  one_smul q := by
    refine QuotientAddGroup.induction_on q (fun f => ?_)
    show QuotientAddGroup.mk' (devissageIota U).range ((1 : ZMod p) • f)
      = QuotientAddGroup.mk' (devissageIota U).range f
    rw [one_smul]
  mul_smul c d q := by
    refine QuotientAddGroup.induction_on q (fun f => ?_)
    show QuotientAddGroup.mk' (devissageIota U).range ((c * d) • f)
      = QuotientAddGroup.mk' (devissageIota U).range (c • (d • f))
    rw [mul_smul]
  smul_zero c := by
    show QuotientAddGroup.mk' (devissageIota U).range (c • (0 : Coind G U M))
      = QuotientAddGroup.mk' (devissageIota U).range (0 : Coind G U M)
    rw [smul_zero]
  smul_add c q r := by
    refine QuotientAddGroup.induction_on q (fun f => ?_)
    refine QuotientAddGroup.induction_on r (fun f' => ?_)
    show QuotientAddGroup.mk' (devissageIota U).range (c • (f + f'))
      = QuotientAddGroup.mk' (devissageIota U).range (c • f)
        + QuotientAddGroup.mk' (devissageIota U).range (c • f')
    rw [smul_add, map_add]
  add_smul c d q := by
    refine QuotientAddGroup.induction_on q (fun f => ?_)
    show QuotientAddGroup.mk' (devissageIota U).range ((c + d) • f)
      = QuotientAddGroup.mk' (devissageIota U).range (c • f)
        + QuotientAddGroup.mk' (devissageIota U).range (d • f)
    rw [add_smul, map_add]
  zero_smul q := by
    refine QuotientAddGroup.induction_on q (fun f => ?_)
    show QuotientAddGroup.mk' (devissageIota U).range ((0 : ZMod p) • f)
      = QuotientAddGroup.mk' (devissageIota U).range (0 : Coind G U M)
    rw [zero_smul, map_zero]

/-- **`devissagePi` is `𝔽_p`-linear.** -/
theorem devissagePi_smul (c : ZMod p) (f : Coind G U M) :
    devissagePi U (c • f) = c • devissagePi U f := rfl


/-- The `G`-action and the `𝔽_p`-action on the cokernel `M₁` commute. -/
noncomputable instance instSMulCommClassM1 : SMulCommClass G (ZMod p) (devissageM1 (M := M) U) where
  smul_comm g c q := by
    refine QuotientAddGroup.induction_on q (fun f => ?_)
    show QuotientAddGroup.mk' (devissageIota U).range (g • (c • f))
      = QuotientAddGroup.mk' (devissageIota U).range (c • (g • f))
    rw [smul_comm g c f]

end QuotModule


/-! ## The dévissage short exact sequence, transparently

`PT.devissageSES` returns a `Nonempty (ShortExactSeq …)`, and `Classical.choice` of a `Prop` makes
its `iota`/`pi` opaque, so the linearity lemmas above cannot be applied to it.  The `def` below is
the same layout with the structure literal exposed, so that `(devissageSESDef …).iota` and `.pi`
*are* `devissageIota U` / `devissagePi U` (up to `rfl`). -/

section SESDef

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type u} [AddCommGroup M] [DistribMulAction G M]

/-- **The dévissage short exact sequence** `0 → M → Coind^G_U M → M₁ → 0`, as a `def` (so that its
maps are the transparent `devissageIota`/`devissagePi`). -/
noncomputable def devissageSESDef (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
    (hM : Work.AbsoluteKummer.IsDiscreteModule G M)
    (hMU : Work.AbsoluteKummer.IsDiscreteModule U M) :
    Work.AbsoluteKummer.ShortExactSeq G M (Coind G U M) (devissageM1 (M := M) U) :=
  { iota := devissageIota U
    pi := devissagePi U
    iota_equivariant := devissageIota_equivariant U
    pi_equivariant := devissagePi_equivariant U
    iota_injective := devissageIota_injective U
    pi_surjective := QuotientAddGroup.mk'_surjective _
    range_iota_eq_ker_pi := devissage_range_iota_eq_ker_pi U
    isDiscreteM := hM
    isDiscreteN := isDiscreteModule_coind U hU hMU
    isDiscreteP := devissage_isDiscreteModule_m1 U (isDiscreteModule_coind U hU hMU) }

@[simp] theorem devissageSESDef_iota_eq (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
    (hM : Work.AbsoluteKummer.IsDiscreteModule G M)
    (hMU : Work.AbsoluteKummer.IsDiscreteModule U M) :
    (devissageSESDef (M := M) U hU hM hMU).iota = devissageIota U := rfl

@[simp] theorem devissageSESDef_pi_eq (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
    (hM : Work.AbsoluteKummer.IsDiscreteModule G M)
    (hMU : Work.AbsoluteKummer.IsDiscreteModule U M) :
    (devissageSESDef (M := M) U hU hM hMU).pi = devissagePi U := rfl

end SESDef


section SESDefLinear

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction G M] [SMulCommClass G (ZMod p) M]

/-- The dévissage inclusion of `devissageSESDef` is `𝔽_p`-linear, in the form
(`∀ c m, S.iota (c • m) = c • S.iota m`) consumed by the descent. -/
theorem devissageSESDef_iota_smul (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
    (hM : Work.AbsoluteKummer.IsDiscreteModule G M)
    (hMU : Work.AbsoluteKummer.IsDiscreteModule U M) (c : ZMod p) (m : M) :
    (devissageSESDef (M := M) U hU hM hMU).iota (c • m)
      = c • (devissageSESDef (M := M) U hU hM hMU).iota m := by
  refine Subtype.ext (funext fun x => ?_)
  simp only [devissageSESDef_iota_eq, devissageIota_apply,
    Work.SSGRoute.PT.AKZmodLin.instModuleCoind_coe_smul, Pi.smul_apply]
  exact smul_comm x⁻¹ c m

/-- The dévissage projection of `devissageSESDef` is `𝔽_p`-linear. -/
theorem devissageSESDef_pi_smul (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
    (hM : Work.AbsoluteKummer.IsDiscreteModule G M)
    (hMU : Work.AbsoluteKummer.IsDiscreteModule U M) (c : ZMod p) (f : Coind G U M) :
    (devissageSESDef (M := M) U hU hM hMU).pi (c • f)
      = c • (devissageSESDef (M := M) U hU hM hMU).pi f :=
  rfl

/-- **The connecting map of the dévissage is `𝔽_p`-linear**, ready to be used as `hlinδm` in the
`ebot` block with `δm := (devissageSESDef …).delta`. -/
theorem devissageSESDef_delta_smul (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
    (hM : Work.AbsoluteKummer.IsDiscreteModule G M)
    (hMU : Work.AbsoluteKummer.IsDiscreteModule U M) (c : ZMod p)
    (q : Work.AbsoluteKummer.H0 G (devissageM1 (M := M) U)) :
    (devissageSESDef (M := M) U hU hM hMU).delta (c • q)
      = c • (devissageSESDef (M := M) U hU hM hMU).delta q :=
  delta_smul (devissageSESDef (M := M) U hU hM hMU)
    (fun c m => devissageSESDef_iota_smul U hU hM hMU c m)
    (fun c f => devissageSESDef_pi_smul U hU hM hMU c f) c q

end SESDefLinear

end AKZmodLin

end Work.SSGRoute.PT
