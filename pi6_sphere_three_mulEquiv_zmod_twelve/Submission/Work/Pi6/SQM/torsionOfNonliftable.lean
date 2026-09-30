import Mathlib
import Submission.Work.Pi6.SQM.RedDefs
import Submission.Work.Pi6.SQM.redChainKernel
import Submission.Work.Pi6.SQM.redChain_surjective
import Submission.Work.Pi6.SQM.redChain_d
import Submission.Work.Pi6.SQM.cochainClassEqZero
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-! Guidance from the project lead (the requester):

SQM piece. Read REFS/NOTES_LEAD_SQM.md §4 (complete proof). Pure chain/cochain arithmetic with 0/1 lifts plus field
duality (Work.Cohomology.kronH_bijective_field) and the Kronecker pairing (kronecker_coboundary_cycle,
kronecker_cocycle_boundary in Cohomology/Kronecker.lean). The element a is the class of ã = (∂ũ)/2.

## The argument

`y` is a mod-2 `n`-cocycle that is not the reduction of a `ℤ/4`-cocycle.  Lift it to a 0/1 integral
cochain `yZ = liftZ y`; since `redC (δ yZ) = δ y = 0`, the coboundary `δ yZ` is even and equals
`2 • bZ` for the generatorwise half `bZ`.  Then `b := redC bZ` is a mod-2 `(n+1)`-cocycle and
`¬ Liftable4 [y]` forces `[b] ≠ 0`: if `b = δ v`, then `red4 (yZ - 2 • ṽ)` (for `ṽ` a 0/1 lift of
`v`) is a `ℤ/4`-cocycle reducing to `y`.

Field duality then produces a mod-2 `(n+1)`-cycle `z` with `b z = 1`; lift it to an integral chain
`u` with `redChain u = z`.  Since `redChain` is a chain map, `redChain (∂u) = ∂z = 0`, so
`∂u = 2 • aZ` for an integral `n`-chain `aZ` (the kernel of the reduction is `2·C`), and `aZ` is a
cycle.  Its class `a` satisfies `2a = 0` since `2 • aZ = ∂u` is a boundary.

Finally `a` is not divisible by `2`: `yZ aZ = bZ u` (because `2(yZ aZ) = yZ(∂u) = (δyZ)u = 2(bZ u)`)
and `bZ u` is odd since `⟨bZ, u⟩ ≡ ⟨b, z⟩ = 1` mod 2.  If `2b' = a` for some class `b'`, then
`aZ - 2 • β` (for `β` a cycle with class `b'`) is a boundary `∂w`, whence
`yZ aZ = 2(yZ β) + (δyZ) w = 2(yZ β) + 2(bZ w)` is even — a contradiction.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff cohomologyClassOf cocycleOf chainC cochainC
  genElt genEval_ext genEval_add genEval_smul SSetCochainComplex)

/-- The coboundary of a coboundary of a cochain vanishes. -/
theorem cochainDiff_cochainDiff' {R : Type} [CommRing R] {Y : SSet} {k : ℕ}
    (α : Cochain R Y k) : cochainDiff R Y (cochainDiff R Y α) = 0 := by
  rw [cochainDiff, cochainDiff, LinearMap.comp_assoc]
  have h : (((Y.chainComplex (ModuleCat.of R R)).d (k + 1) k).hom.comp
      ((Y.chainComplex (ModuleCat.of R R)).d (k + 2) (k + 1)).hom) = 0 := by
    rw [← ModuleCat.hom_comp, HomologicalComplex.d_comp_d, ModuleCat.hom_zero]
  rw [h, LinearMap.comp_zero]

theorem torsionOfNonliftable : Work.Pi6.SQM.TorsionOfNonliftable := by
  intro X _inst n y hy hnot
  -- ## Step 1: the `0/1` lift `yZ` of `y` and half of its coboundary
  let yZ : Cochain ℤ (SX X) n := liftZ (SX X) n y
  have hyZ : redC (SX X) n yZ = y := redC_liftZ (SX X) n y
  have heven : ∀ σ : (SX X) _⦋n + 1⦌,
      (2 : ℤ) ∣ genEval ℤ (SX X) (cochainDiff ℤ (SX X) yZ) σ := by
    intro σ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (by
      simpa using intCast_genEval_coboundary_liftZ (SX X) n y hy σ)
  let bZ : Cochain ℤ (SX X) (n + 1) :=
    halfCochain (SX X) (n + 1) (cochainDiff ℤ (SX X) yZ)
  have hbZ : cochainDiff ℤ (SX X) yZ = (2 : ℤ) • bZ :=
    (two_smul_halfCochain (SX X) (n + 1) _ heven).symm
  let b : Cochain F2 (SX X) (n + 1) := redC (SX X) (n + 1) bZ
  have hb : redC (SX X) (n + 1) bZ = b := rfl
  have hbZcyc : cochainDiff ℤ (SX X) bZ = 0 := by
    apply two_smul_cochain_eq_zero
    rw [← cochainDiff_smul, ← hbZ, cochainDiff_cochainDiff']
  have hb' : cochainDiff F2 (SX X) b = 0 := by
    rw [← hb, ← redC_cochainDiff (SX X) (n + 1) bZ, hbZcyc]
    exact (redCLM (SX X) (n + 2)).map_zero
  -- ## Step 2: `[b] ≠ 0`
  have hbne : cls b hb' ≠ 0 := by
    intro hcls
    obtain ⟨v, hv⟩ := Work.Pi6.SQM.exists_cochainDiff_eq_of_class_eq_zero b hb' hcls
    let vZ : Cochain ℤ (SX X) n := liftZ (SX X) n v
    have hvZ : redC (SX X) n vZ = v := redC_liftZ (SX X) n v
    have h2v : (2 : ℤ) • v = 0 := by
      rw [← Int.cast_smul_eq_zsmul F2 2,
        show ((2 : ℤ) : F2) = 0 from by decide, zero_smul]
    have hred : redC (SX X) n (yZ - (2 : ℤ) • vZ) = y := by
      rw [← redCLM_apply, map_sub, map_smul, redCLM_apply, redCLM_apply, hyZ, hvZ, h2v,
        sub_zero]
    have hρ : redC (SX X) (n + 1) (bZ - cochainDiff ℤ (SX X) vZ) = 0 := by
      rw [← redCLM_apply, map_sub, redCLM_apply, redCLM_apply, hb, redC_cochainDiff, hvZ, hv,
        sub_self]
    have hsub : cochainDiff ℤ (SX X) (yZ - (2 : ℤ) • vZ)
        = (2 : ℤ) • (bZ - cochainDiff ℤ (SX X) vZ) := by
      rw [cochainDiff_sub, cochainDiff_smul, hbZ, smul_sub]
    let Y4 : Cochain (ZMod 4) (SX X) n := red4 (SX X) n (yZ - (2 : ℤ) • vZ)
    refine hnot ⟨Y4, ?_, y, hy, rfl, ?_⟩
    · change cochainDiff (ZMod 4) (SX X) (red4 (SX X) n (yZ - (2 : ℤ) • vZ)) = 0
      rw [← red4_cochainDiff, hsub, ← red4LM_apply, map_smul]
      exact two_smul_red4_eq_zero _ hρ
    · intro σ
      change r42 (genEval (ZMod 4) (SX X) (red4 (SX X) n (yZ - (2 : ℤ) • vZ)) σ)
        = genEval F2 (SX X) y σ
      rw [r42_genEval_red4, hred]
  -- ## Step 3: duality: a mod-2 cycle pairing to `1` with `b`
  obtain ⟨z, hzcyc, hbz⟩ : ∃ z : ↥((chainC F2 (SX X)).X (n + 1)),
      ((chainC F2 (SX X)).d (n + 1) n).hom z = 0 ∧ b z = 1 := by
    have hk : Work.Cohomology.kronH F2 (SX X) (n + 1) (cls b hb') ≠ 0 := by
      intro h0
      exact hbne (Work.Cohomology.kronH_injective_field F2 (SX X) (n + 1)
        (by rw [h0, map_zero]))
    have hex : ∃ c, Work.Cohomology.kronH F2 (SX X) (n + 1) (cls b hb') c ≠ 0 := by
      by_contra h
      exact hk (LinearMap.ext (fun c => by simpa using not_exists.mp h c))
    obtain ⟨c, hc⟩ := hex
    obtain ⟨zc, hzc⟩ := (ModuleCat.epi_iff_surjective
      ((chainC F2 (SX X)).homologyπ (n + 1))).mp inferInstance c
    have hzc' : ((chainC F2 (SX X)).homologyπ (n + 1)).hom zc = c := hzc
    refine ⟨((chainC F2 (SX X)).iCycles (n + 1)) zc, ?_, ?_⟩
    · have h := congrArg (fun (g : (chainC F2 (SX X)).cycles (n + 1) ⟶
          (chainC F2 (SX X)).X n) => g.hom zc)
        (HomologicalComplex.iCycles_d (chainC F2 (SX X)) (n + 1) n)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] using h
    · have h1 := Work.Cohomology.kronH_apply F2 (SX X) b hb' zc
      have h2 : b (((chainC F2 (SX X)).iCycles (n + 1)) zc) ≠ 0 := by
        rw [← h1, hzc']
        exact hc
      exact (by decide : ∀ x : F2, x ≠ 0 → x = 1) _ h2
  -- ## Step 4: lift the cycle and halve its boundary
  obtain ⟨u, hu⟩ := Work.Pi6.SQM.redChain_surjective (SX X) (n + 1) z
  have hred : redChain (SX X) n (((chainC ℤ (SX X)).d (n + 1) n).hom u) = 0 := by
    rw [Work.Pi6.SQM.redChain_d (SX X) n u, hu, hzcyc]
  obtain ⟨aZ, haZ⟩ := (redChainKernel (Y := SX X) n).1 _ hred
  have hacyc : ((chainC ℤ (SX X)).d n ((ComplexShape.down ℕ).next n)).hom aZ = 0 := by
    have h2 : (2 : ℤ) • (((chainC ℤ (SX X)).d n ((ComplexShape.down ℕ).next n)).hom aZ) = 0 := by
      rw [← map_zsmul, haZ]
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.d_comp_d,
        ModuleCat.hom_zero, LinearMap.zero_apply]
    exact (redChainKernel (Y := SX X) ((ComplexShape.down ℕ).next n)).2
      (((chainC ℤ (SX X)).d n ((ComplexShape.down ℕ).next n)).hom aZ) h2
  let α : (chainC ℤ (SX X)).cycles n :=
    (chainC ℤ (SX X)).cyclesMk aZ ((ComplexShape.down ℕ).next n) rfl hacyc
  have hiα : ((chainC ℤ (SX X)).iCycles n).hom α = aZ :=
    HomologicalComplex.i_cyclesMk (K := chainC ℤ (SX X)) aZ ((ComplexShape.down ℕ).next n) rfl
      hacyc
  refine ⟨((chainC ℤ (SX X)).homologyπ n).hom α, ?_, ?_⟩
  · -- `2 • a = 0`
    have h2α : (2 : ℤ) • α = ((chainC ℤ (SX X)).toCycles (n + 1) n) u := by
      apply (ModuleCat.mono_iff_injective ((chainC ℤ (SX X)).iCycles n)).mp inferInstance
      rw [map_zsmul, hiα, haZ]
      have hti := congrArg (fun (g : (chainC ℤ (SX X)).X (n + 1) ⟶
          (chainC ℤ (SX X)).X n) => g.hom u)
        (HomologicalComplex.toCycles_i (chainC ℤ (SX X)) (n + 1) n)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hti.symm
    calc (2 : ℤ) • ((chainC ℤ (SX X)).homologyπ n).hom α
        = ((chainC ℤ (SX X)).homologyπ n).hom ((2 : ℤ) • α) :=
          (map_zsmul ((chainC ℤ (SX X)).homologyπ n).hom (2 : ℤ) α).symm
      _ = ((chainC ℤ (SX X)).homologyπ n).hom (((chainC ℤ (SX X)).toCycles (n + 1) n) u) := by
          rw [h2α]
      _ = 0 := by
          have h := congrArg (fun (g : (chainC ℤ (SX X)).X (n + 1) ⟶
              (chainC ℤ (SX X)).homology n) => g.hom u)
            (HomologicalComplex.toCycles_comp_homologyπ (chainC ℤ (SX X)) (n + 1) n)
          simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
            LinearMap.zero_apply] using h
  · -- `a` is not divisible by `2`
    intro b' hb'a
    obtain ⟨β, hβ⟩ := (ModuleCat.epi_iff_surjective
      ((chainC ℤ (SX X)).homologyπ n)).mp inferInstance b'
    have hβ' : ((chainC ℤ (SX X)).homologyπ n).hom β = b' := hβ
    have hzero : ((chainC ℤ (SX X)).homologyπ n).hom (α - (2 : ℤ) • β) = 0 := by
      rw [map_sub, map_zsmul, hβ', ← hb'a]
      exact sub_self _
    obtain ⟨w, hw⟩ :=
      (Work.SSS.E2Zero.homologypi_eq_zero_iff n (α - (2 : ℤ) • β)).mp hzero
    have hodd : ¬ (2 : ℤ) ∣ yZ aZ := by
      have h1 : yZ aZ = bZ u := by
        refine mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num) ?_
        calc (2 : ℤ) * (yZ aZ) = yZ ((2 : ℤ) • aZ) := (cochain_apply_zsmul yZ 2 aZ).symm
          _ = yZ (((chainC ℤ (SX X)).d (n + 1) n).hom u) := by rw [haZ]
          _ = (cochainDiff ℤ (SX X) yZ) u := rfl
          _ = ((2 : ℤ) • bZ) u := by rw [hbZ]
          _ = 2 * (bZ u) := by rw [LinearMap.smul_apply, Int.zsmul_eq_mul]
      have h2 : ¬ (2 : ℤ) ∣ bZ u := by
        intro hd
        have h3 : ((bZ u : ℤ) : F2) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd (bZ u) 2).mpr hd
        have h4 : ((bZ u : ℤ) : F2) = 1 := by
          rw [pairingRedC (SX X) (n + 1) bZ u, hb, hu, hbz]
        rw [h3] at h4
        exact zero_ne_one h4
      rwa [h1]
    have heven2 : (2 : ℤ) ∣ yZ aZ := by
      have hα : ((chainC ℤ (SX X)).iCycles n).hom α
          = (2 : ℤ) • ((chainC ℤ (SX X)).iCycles n).hom β
            + ((chainC ℤ (SX X)).d (n + 1) n).hom w := by
        rw [← sub_eq_iff_eq_add']
        rw [← map_zsmul, ← map_sub]
        exact hw.symm
      have h3 : yZ aZ = 2 * (yZ (((chainC ℤ (SX X)).iCycles n).hom β)) + 2 * (bZ w) := by
        calc yZ aZ = yZ (((chainC ℤ (SX X)).iCycles n).hom α) := by rw [hiα]
          _ = yZ ((2 : ℤ) • ((chainC ℤ (SX X)).iCycles n).hom β
                + ((chainC ℤ (SX X)).d (n + 1) n).hom w) := by rw [hα]
          _ = 2 * (yZ (((chainC ℤ (SX X)).iCycles n).hom β))
                + (cochainDiff ℤ (SX X) yZ) w := by
              rw [map_add, cochain_apply_zsmul]
              simp only [cochainDiff, LinearMap.comp_apply]
          _ = 2 * (yZ (((chainC ℤ (SX X)).iCycles n).hom β)) + 2 * (bZ w) := by
              rw [hbZ, LinearMap.smul_apply, Int.zsmul_eq_mul]
      rw [h3]
      exact ⟨yZ (((chainC ℤ (SX X)).iCycles n).hom β) + bZ w, by ring⟩
    exact hodd heven2

end

end Work.Pi6.SQM
