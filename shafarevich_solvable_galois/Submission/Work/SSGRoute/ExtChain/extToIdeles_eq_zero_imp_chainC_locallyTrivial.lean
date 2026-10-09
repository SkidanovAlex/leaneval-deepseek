import Mathlib
import Submission.Work.SSGRoute.PT.e1a_beta_can
import Submission.Work.SSGRoute.PT.sha2_range_iff
import Submission.Work.SSGRoute.PT.e1a_localComparison_bricks
import Submission.Work.SSGRoute.SSGStage.e1aLandingFinCompat
import Submission.Work.SSGRoute.ExtChain.deltaH2_restrictSES_e1aSES_injective
import Submission.Work.SSGRoute.ExtChain.deltaH2_restriction
import Submission.Work.SSGRoute.E1aClean.Transport
import Submission.Work.SSGRoute.E1aClean.LocalData
import Submission.Work.SSGRoute.PT.e1cDelta_beta_relation_gen
import Submission.Work.SSGRoute.ExtChain.carrier_hact
import Submission.Work.SSGRoute.localGaloisEquiv_coInAdjoin_compat_general
import Submission.Work.SSGRoute.ExtChain.extLoc_extToIdeles_e1aSyzShift_eq_zero_imp
import Submission.Work.SSGRoute.ExtChain.subsingletonH1_homCoind_of_le_ker
import Submission.Work.SSGRoute.ExtChain.subsingletonH1_homCoind_of_trivial_action
import Submission.Work.SSGRoute.PT.delta_restrictSES
import Submission.Work.SSGRoute.PTdualControl.extExact
import Submission.Work.SSGRoute.ExtChain.himgLeafCore
import Submission.Work.SSGRoute.hasseExt1_C2_lattice_leaf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `himg` half of the chain--localisation comparison `(C')` — the leaf file

This file carries **one** declaration, the target

    extToIdeles y = 0  →  ∃ c ∈ Z2loc,  H2π (Z2ofZ2loc c) = e1aChainC y            (`himg`),

of the node `Work.SSGRoute.ext_sha2_bridge`.  Its *assembly* half (the reduction of the target to
the two per-family inputs, and the extension criterion) is in the **lower** module
`Submission.Work.SSGRoute.ExtChain.himgLeafCore`, which this file imports:
`himg_reduction`, `himg_reduction'`, `himg_reduction''`, `himg_of_extDelta_input`,
`himg_of_ideles_input`, `resH1_e1cMap_eq_zero_of_extension`,
`resH1_e1cMap_eq_zero_of_le_ker`, `resH1_zpowers_eq_zero_of_res_eq_one`,
`resH1_e1cMap_eq_zero_of_trivial_action`, `resH1_zpowers_eq_zero_of_rho_eq_one`.

## Why the file was split (2026-10-05)

The file must sit *above* the `himgIdelesInput_*` lanes (they are its children), but until this
session those lanes imported the leaf file for the lemmas listed above — a cycle which made the
leaf's `sorry` structurally unclosable (a child whose statement is the leaf's content could not be
cited from the leaf).  Moving the lemmas to `himgLeafCore` (below the leaf) removes the incoming
edges.  See `PING_himgLeafCore_available_repoint_leaf_imports.md` at the workspace root.

## The wiring, once a finite-place clause is available below this file

    exact himg_of_ideles_input (k := k) (Ω := Ω) (K := K) p ζ hζ hζK T hT E
      (fun z hz A hA hns => <finite-place clause> p k Ω K ζ hζ hζK T hT E z hz A hA hns)
      (fun z hz σ hσ hnt =>
        Work.SSGRoute.ExtChain.himgIdelesInput_inf_clean p k Ω K ζ hζ hζK T hT E z hz σ hσ hnt)

with `himgIdelesInput_inf_clean` (`Submission/Work/SSGRoute/hasseExt1_C2_lattice_leaf.lean`,
sorry-free, axiom-clean, already below this file) the proved involution clause, and the
finite-place clause requested as `SSGRoute/ExtChain/himgIdelesInput_fin_leaf`.  The assembly shape
is verified: with the two clauses as hypotheses, the proof above produces exactly the statement
below.
-/

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 2000000

attribute [local instance] Work.SSGRoute.freeCoverSES_finite

noncomputable section
/-- **The `⟹` half of the chain--localisation comparison `(C')`** (the "himg" direction of
`Work.SSGRoute.ext_sha2_bridge`'s image clause): if the idèle localisation of
`y ∈ Ext²_{Gal(K/k)}(E^∨(1), Kˣ)` vanishes, then the canonical chain class
`e1aChainC y ∈ H²_c(G_k, E)` is the class of a *locally trivial* continuous `2`-cocycle, i.e. it
lies in the range of the `Ш²`-bridge `sha2_to_H2AK`.

STATUS (2026-10-05, after the split; earlier history in the module doc of `himgLeafCore`).  By
`himg_of_ideles_input` (in `ExtChain.himgLeafCore`) the target follows from two per-family inputs,
both of the shape "`extToIdeles (e1aSyzShift N z) = 0` ⟹ `resH1_D (e1cMap R z) = 0`":

* (involution family) `D = ⟨σ⟩`, `σ² = 1`, `res k K σ ≠ 1`: **proved** as
  `Work.SSGRoute.ExtChain.himgIdelesInput_inf_clean`
  (`Submission/Work/SSGRoute/hasseExt1_C2_lattice_leaf.lean`, sorry-free, below this file);
* (finite places) `D = decomp k A`, `¬ (decomp k A ≤ ker (res k K))`: requested as
  `SSGRoute/ExtChain/himgIdelesInput_fin_leaf`, whose statement is exactly
  `ExtChain.himgIdelesInput_fin`.

So the remaining arithmetic content of this file is precisely the finite-place clause.  Its
route (project lead's `_lead_design/flags_0030/NOTE.md` §4) is: base-change the `E1c` class to the
decomposition field `k^h = Ω^{D_A}` (`(BC)`), where `e1cMap` is injective and the connecting map
`δ` is injective, so that it suffices that the image of the class in
`Ext²_D(E^∨(1),(K^h)ˣ)` vanishes; the `(PUSH)` isomorphism
`Ext^i_D(E^∨(1),(K^h)ˣ) ≅ Ext^i_D(E^∨(1),K_qˣ)` (unique `p`-divisibility of `K_qˣ/(K^h)ˣ`, formal
half in `ExtChain.ext_push_engine`) then identifies the class with
`extLoc_q (extToIdeles (e1aSyzShift N z))`, which is `0` by the hypothesis.  The older lattice-Hasse
framing of this clause is *dropped*: it would ask for `extRes_{D_q} z = 0` in the `Kˣ`-coefficient —
a Hasse principle for a torus split by `K`, which fails for non-cyclic `D_q` (norm-one tori of
biquadratic extensions).

The equivalence of the two forms: by
`PTdualControl.exists_extDelta_eq_of_extToIdeles_eq_zero` (formal, from the long exact sequence of
the class formation) `extToIdeles y = 0` for `y ∈ Ext²_G(E^∨(1),Kˣ)` is exactly the statement that
`y = extDelta x` for some `x ∈ Ext¹_G(E^∨(1),C_K)`; so the whole arithmetic content of the target
is the vanishing of the composite

    Ext¹_G(E^∨(1),C_K) --extDelta--> Ext²_G(E^∨(1),Kˣ) --(e1aSyzShift N)⁻¹--> Ext¹_G(R,Kˣ)
      --e1cMap--> H¹(Γ, Hom_ℤ(R.V,Ωˣ)) --resH1_D--> H¹(D, Hom_ℤ(R.V,Ωˣ))

for `D = decomp k A` (finite places, not completely split) and `D = ⟨σ⟩` (`σ² = 1`,
`res k K σ ≠ 1`).  Everything *except* this input is proved here or on disk
(`himg_reduction`, `himg_reduction'`, `resH1_e1cMap_eq_zero_of_le_ker`,
`resH1_zpowers_eq_zero_of_res_eq_one`, `extLoc_extToIdeles_e1aSyzShift_eq_zero_imp`).

Two *refuted* attempts are recorded in the module doc ("Correction (session 11), sharpened
(session 13)"): the *per-place* form of the input (quaternion class `(−1,−1)` over `ℚ(i)`), and the
description of `resH1_D (e1cMap R z) = 0` as `extRes_D z = 0` (coefficient fields `K·Ω^D` vs `K`).
Session 13's §2 pinpoints the mechanism: the sharp per-place form is
`resH1_{D_A}(e1cMap R z) = 0 ⟺ cc_{K·Ω^{D_A}}(res_{D_q} z) = 0` (coefficients in the *algebraic*
decomposition compositum), while `z_w = 0` is the same statement for the *completion* `K_wˣ`, a
strictly weaker coefficient condition whose gap is the local `Ш²`.  So the honest input is global
(see `ExtChain/NOTE_himg_extDelta_session13.md`). -/
theorem extToIdeles_eq_zero_imp_chainC_locallyTrivial (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      SSGRoute.PTExt.extToIdeles (k := k) y = 0 →
        ∃ c : ↥(SSGRoute.Z2loc p k Ω K E),
          @Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
            (DistribMulAction.compHom E (SSGRoute.res k K))
            (Work.SSGRoute.PT.Z2ofZ2loc p k Ω K E c) =
          Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y := by
  sorry

end

end Work.SSGRoute.ExtChain
