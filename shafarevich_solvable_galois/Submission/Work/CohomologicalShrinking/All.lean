/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Work.CohomologicalShrinking`: umbrella import

The chapter **cohomological shrinking** — Definition 3, Lemma 4, Proposition 5, Proposition 6 and
Proposition 7 of A. Schmidt and K. Wingberg, *Šafarevič's theorem on solvable groups as Galois
groups* (arXiv:math/9809211), §2 — in the form in which the paper's Theorem 15 uses them.

Import this module to get the whole chapter (namespace `Work.CohomologicalShrinking`).
See `Submission/Work/CohomologicalShrinking/NOTES.md` for the dictionary with the paper, for
the exact status (proved / assumed) of every statement, and for what is missing.

## The main interface

All statements are in the paper's own "there is `m₀ ≥ n` such that for all `m ≥ m₀`" form, so the
level `m` is at the user's disposal.

### The paper's own group and its group homology (the concrete chapter)

* `Work.CohomologicalShrinking.flowGroup p G m i j` — the group `F(m)/F(m)^{(i,j)} ⋊ G` built from
  the discrete free `G`-operator group `F(m) = FreeGroup (Fin m × G)`;
  `flowNormal`, `flowQuotEquiv : Γ ⧸ N ≃* G`, `flowQuotMap`, `flowGroupMap` (rank change).
* `Work.CohomologicalShrinking.flowRep p G m i j T` — the coefficient module `E(m,τ) ⊗ T` as a
  representation of `Γ`, trivial on `N` (`flowRep_isTrivial`).
* `Work.CohomologicalShrinking.universalCoefficient.h1AddEquivPQuotientSub` — the universal
  coefficient formula `H₁(S, A) ≅ A ⊗_{𝔽_p} S/(Sᵖ[S,S])`.
* `Work.CohomologicalShrinking.flow.flowNormalSquareEquiv` — `(F(m)/ν)/(F(m)/ν)² ≅ F(m)/F(m)²`
  for `ν ≥ (2,1)`.
* `Work.CohomologicalShrinking.hochschildSerre.flowHSExact` /
  `…flowQuotH1Equiv` — the homological Hochschild–Serre sequence for `N ◁ Γ` and the
  identification of `H₁(Γ ⧸ N, E⊗T)` with `H₁(G, E⊗T)`.
* `Work.CohomologicalShrinking.flowZMap` (with `flow.flowZMap_comp`) — the map induced by an
  operator map on `H₁(Γ_m, E(m,τ) ⊗ T)`.
* `Work.CohomologicalShrinking.flowAlpha` / `flowAlpha_range` — the paper's `α`, and the fact
  that its image is the image of the corestriction.
* `Work.CohomologicalShrinking.semidirectShrinkingData_of` — the Hochschild–Serre data
  `SemidirectShrinkingData` for `Z m := H₁(Γ_m, E(m,τ) ⊗ T)`, with the exactness, the
  surjectivity of `β` and the functoriality of `zMap` **proved**; the remaining inputs are the
  naturality in the rank of `α` and `β` and the paper's recalled `H^{-2} = H₁`
  (`exists_bridge`).
* `Work.CohomologicalShrinking.exists_bridge` — the paper's recalled `H^{-2} = H₁`, i.e. the
  natural dimension shift `H₁(G, X) ≅ Ĥ⁻²(G, X) = Ĥ⁻¹(G, X ⊗ I_G)`.
* `Work.CohomologicalShrinking.exists_natural_alpha` — the paper's `α` (universal coefficient
  formula + Proposition 5) with its image and its naturality in the rank.
* `Work.CohomologicalShrinking.exists_shrinking_H1_semidirect_concrete` — **Proposition 7 (i)**
  for the paper's own group and classes, taking the maps `α`, `γ` as explicit parameters;
  `exists_shrinking_H1_semidirect_of_alpha` discharges `γ`, and
  `exists_shrinking_H1_semidirect_paper` discharges everything except `Prop5Data`.

### The abstract shrinking statements

* `Work.CohomologicalShrinking.Prop5Data` — **Proposition 5** of the paper, isolated as a
  structure (unproved; its trivially true case `τ = (1,1)` *is* proved:
  `Work.CohomologicalShrinking.nonempty_prop5Data_one_one`).
* `Work.CohomologicalShrinking.exists_shrinking_Hm1` — **Proposition 6**, `k = -1`.
* `Work.CohomologicalShrinking.exists_shrinking_H2IG` — **Proposition 6**, `k = 2`
  (in the paper's model `Ĥ²(G,X) ≅ Ĥ⁻¹(G, X ⊗ A₂)`, `A₂ = I_G^{-3}`).
* `Work.CohomologicalShrinking.exists_shrinking_Hm2IG` — **Proposition 6**, `k = -2`
  (in the paper's model `Ĥ⁻²(G,X) ≅ Ĥ⁻¹(G, X ⊗ I_G)`).
* `Work.CohomologicalShrinking.exists_shrinking_H2_tate` / `…Hm2_tate` — the same two degrees
  over the cohomology groups `GroupCohomology.H2` and `Work.Tate.Hm2` of the workspace.
* `Work.CohomologicalShrinking.exists_shrinking_H1` — **Proposition 7 (ii)**.
* `Work.CohomologicalShrinking.exists_shrinking_H1_semidirect` — **Proposition 7 (i)**, from the
  Hochschild–Serre data `Work.CohomologicalShrinking.SemidirectShrinkingData`.
* `Work.CohomologicalShrinking.exists_shrinking_Hm1_one_one`,
  `Work.CohomologicalShrinking.exists_shrinking_H1_one_one` — the unconditional case `τ = (1,1)`.
* `Work.CohomologicalShrinking.OperatorMap` — the surjective `G`-operator homomorphisms
  `F(m) ⇢ F(n)` produced by the shrinking lemmas, with the induced maps `OperatorMap.hm1Map`,
  `.hm2Map`, `.h2Map`, `.h1Map` and their composition laws.
* `Work.CohomologicalShrinking.SmokeTest` — a separate module (it imports `All`, not the
  other way round) containing examples showing how a consumer uses the interface.

## Guide to the files

* `Defs.lean` — the refined `p`-central filtration `refinedTerm p P i j = (P_i ∩ P^j)P_{i+1}`,
  the successor `tauSucc` on the index pairs, the graded pieces `E p G d i j` and the quotient
  `squareQuotient p G d = F(d)/F(d)^2`.
* `Refined.lean` — the graded pieces are elementary abelian `p`-groups and, with the descended
  action of `G`, `𝔽_p[G]`-modules (Lemma 4 of the paper, in the form needed).
* `ModSquare.lean` — the canonical map `F(d)/F(d)^2 → 𝔽_p[G]^d` and the model of `𝔽_p[G]^d`.
* `Functorial.lean`, `functorial/` — the maps induced by a surjective `G`-operator homomorphism
  on the graded pieces (`gradedMapLin`) and on `F(d)/F(d)^2` (`quotMapLin`), their equivariance
  and their functoriality.
* `Prop5.lean` — **Proposition 5** of the paper, isolated as the structure `Prop5Data`.
* `Shrinking.lean` — **Proposition 6** for `k = -1` at the levels `r·n`
  (`exists_shrinking_Hm1_of_mult`), derived from `Prop5Data` and Proposition 2 of the paper.
* `OperatorMap.lean` — the category structure on the surjective `G`-operator homomorphisms
  (`comp`, `id`, and `ofLe`/`exists_operatorMap_of_le`: `F(m) ⇢ F(n)` for `n ≤ m`).
* `Levels.lean` — the same shrinking statements at **every** level `m ≥ m₀` (the paper's form).
* `Models.lean` — the augmentation ideal `I_G` as a f.g. `𝔽_p[G]`-module, its dual, the paper's
  `A₂ = I_G^{-3}`, and the cases `k = -2`, `k = 2` of Proposition 6 in these models.
* `Prop7.lean`, `Prop7Uncond.lean`, `prop7/exists_h1Sigma.lean` — **Proposition 7 (ii)**.
* `Prop7i.lean` — **Proposition 7 (i)** and the Hochschild–Serre data
  `SemidirectShrinkingData`.
* `Corollaries.lean` — the `k = ±2` cases with a *generic* dimension-shifting isomorphism as an
  explicit hypothesis (`exists_shrinking_Hm2_of_shift`, `exists_shrinking_H2_of_shift`).
* `Coind.lean` — `coindSMulCommClass`: the coinduced module `G → A` as an `𝔽_p[G]`-module (the
  case `T = Ind 𝔽_p` of step 1 of Theorem 15).
* `OneOne.lean`, `nonempty_prop5Data_one_one.lean` — the unconditional case `τ = (1,1)`.

Every file is `sorry`-free.  The one remaining unproved mathematical input of the chapter is
`Prop5Data` (Proposition 5 of the paper, whose proof needs the commutator calculus of Lemma 4);
it is always taken as an explicit argument, never as `sorry` or `axiom`.  Everything else the
paper's §2 uses — the semidirect product `F(m)/F(m)^{(ν)} ⋊ G`, the coefficient module
`E(m,τ) ⊗ T`, the universal coefficient formula `H₁(P, M) ≅ P/P² ⊗ M`, the homological
Hochschild–Serre sequence with its exactness and the surjectivity of the coinflation, the paper's
`α`, and the recalled `H^{-2} = H₁` — is proved here.  In particular
`exists_shrinking_H1_semidirect_paper` is Proposition 7 (i) for the paper's own group and classes
with `Prop5Data` as the only input.  See `NOTES.md` §3 and §9.
-/

import Submission.Work.CohomologicalShrinking.Coind
import Submission.Work.CohomologicalShrinking.FlowGroupMap
import Submission.Work.CohomologicalShrinking.FlowMap
import Submission.Work.CohomologicalShrinking.FlowRep
import Submission.Work.CohomologicalShrinking.Corollaries
import Submission.Work.CohomologicalShrinking.Defs
import Submission.Work.CohomologicalShrinking.Functorial
import Submission.Work.CohomologicalShrinking.Levels
import Submission.Work.CohomologicalShrinking.ModSquare
import Submission.Work.CohomologicalShrinking.Models
import Submission.Work.CohomologicalShrinking.OneOne
import Submission.Work.CohomologicalShrinking.OperatorMap
import Submission.Work.CohomologicalShrinking.Prop5
import Submission.Work.CohomologicalShrinking.Prop7
import Submission.Work.CohomologicalShrinking.Prop7Uncond
import Submission.Work.CohomologicalShrinking.Prop7i
import Submission.Work.CohomologicalShrinking.Prop7iConcrete
import Submission.Work.CohomologicalShrinking.Refined
import Submission.Work.CohomologicalShrinking.Semidirect
import Submission.Work.CohomologicalShrinking.SemidirectData
import Submission.Work.CohomologicalShrinking.Shrinking
import Submission.Work.CohomologicalShrinking.TateShifts
import Submission.Work.CohomologicalShrinking.augIdeal_coeff_sum
import Submission.Work.CohomologicalShrinking.coeff_smul_monoidAlgebra
import Submission.Work.CohomologicalShrinking.coindShiftAddEquivTensor
import Submission.Work.CohomologicalShrinking.coindUpAddEquivTensor
import Submission.Work.CohomologicalShrinking.eq_sum_coeff_smul_single
import Submission.Work.CohomologicalShrinking.exists_bridge
import Submission.Work.CohomologicalShrinking.exists_natural_alpha
import Submission.Work.CohomologicalShrinking.exists_shrinking_Hm2_tate
import Submission.Work.CohomologicalShrinking.nonempty_prop5Data_one_one
import Submission.Work.CohomologicalShrinking.shiftH2Family
import Submission.Work.CohomologicalShrinking.functorial.gradedMapAdd_smul
import Submission.Work.CohomologicalShrinking.functorial.gradedMapLin_comp
import Submission.Work.CohomologicalShrinking.functorial.quotMapAdd_smul
import Submission.Work.CohomologicalShrinking.functorial.quotMapLin_comp
import Submission.Work.CohomologicalShrinking.shrinking.rTensor_map_foldMap_smul
import Submission.Work.CohomologicalShrinking.tate.Hm1Map_comp
import Submission.Work.CohomologicalShrinking.tate.Hm2Map_comp
import Submission.Work.CohomologicalShrinking.tate.deltaH1_natural_shortExact
import Submission.Work.CohomologicalShrinking.tate.dimensionShiftCoind_natural
import Submission.Work.CohomologicalShrinking.tate.dimensionShiftH1H0_natural
import Submission.Work.CohomologicalShrinking.tate.dimensionShiftH2H1_natural
import Submission.Work.CohomologicalShrinking.shiftTensor.assocTripleTensorGen
import Submission.Work.CohomologicalShrinking.shiftTensor.coindShiftTensorEquiv
import Submission.Work.CohomologicalShrinking.operator.exists_foldOperator
import Submission.Work.CohomologicalShrinking.operator.exists_foldOperator_of_basis
import Submission.Work.CohomologicalShrinking.operator.h1Map_comp
import Submission.Work.CohomologicalShrinking.operator.h2Map_comp
import Submission.Work.CohomologicalShrinking.operator.hm1Map_comp
import Submission.Work.CohomologicalShrinking.operator.hm2Map_comp
import Submission.Work.CohomologicalShrinking.modsquare.squareQuotientToFun_bijective
import Submission.Work.CohomologicalShrinking.modsquare.squareQuotientToFun_smul
import Submission.Work.CohomologicalShrinking.group.commutator_sup_le_of_le
import Submission.Work.CohomologicalShrinking.group.pow_mul_mem_of_commutator_mem
import Submission.Work.CohomologicalShrinking.group.pow_sup_le_of_le
import Submission.Work.CohomologicalShrinking.prop7.exists_h1Sigma
import Submission.Work.CohomologicalShrinking.flow.finite_refinedQuotient
import Submission.Work.CohomologicalShrinking.flow.flowGroupMap_comp
import Submission.Work.CohomologicalShrinking.flow.flowNormalMap_smul
import Submission.Work.CohomologicalShrinking.flow.flowNormalSquareEquiv
import Submission.Work.CohomologicalShrinking.flow.flowQuotMap_smul
import Submission.Work.CohomologicalShrinking.flow.flowRepMap_comp
import Submission.Work.CohomologicalShrinking.flow.flowZMap_comp
import Submission.Work.CohomologicalShrinking.flow.pCentralQuotientZeroMap
import Submission.Work.CohomologicalShrinking.hochschildSerre.flowHSExact
import Submission.Work.CohomologicalShrinking.hochschildSerre.flowQuotH1Equiv
import Submission.Work.CohomologicalShrinking.universalCoefficient.h1AddEquivPQuotientSub
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
