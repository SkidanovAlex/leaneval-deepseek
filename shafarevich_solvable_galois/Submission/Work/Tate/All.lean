/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tate cohomology of a finite group: the whole chapter

Convenience aggregator: import this module to get the entire `Work.Tate` development.

* `Work.Tate.Basic` : `fixedSubgroup`, `norm`, `augmentation`, `Ĥ⁰`, `Ĥ⁻¹`, functoriality
* `Work.Tate.CoindModule` : the coinduced module `G → R` and its `SMul` laws
* `Work.Tate.coind_*` : vanishing of `Ĥ⁰` and `Ĥ⁻¹` on coinduced modules
* `Work.Tate.CoindPi` : vanishing on finite products of coinduced modules
* `Work.Tate.SES` : short exact sequences of `G`-modules
* `Work.Tate.Delta` : the connecting map `δ : Ĥ⁻¹(G, C) → Ĥ⁰(G, A)`
* `Work.Tate.*` exactness lemmas : the six-term exact sequence in degrees `-1, 0`
* `Work.Tate.Shift` : the shifted module `A^* = Coind(A)/A` and the sequence `0 → A → Coind(A) → A^* → 0`
* `Work.Tate.DimensionShift` : dimension shifting, abstract and concrete (degree 0 → -1)
* `Work.Tate.CoindUp` : the `I_G`-twist `A^♯ ≅ A ⊗ I_G`, the sequence `0 → A^♯ → Coind A → A → 0`,
  the upward shift `Ĥ⁻¹(G,A) ≃+ Ĥ⁰(G, A^♯)`, and the degree `-2` group `Hm2`
* `Work.Tate.Delta0` / `Delta0Map` : the connecting map `δ₀ : Ĥ⁰(G,C) →+ H¹(G,A)`
* `Work.Tate.DimensionShiftH` : dimension shifting in degrees 2 → 1 → 0 → -1
  (`H²(G,A) ≃+ Ĥ¹(G,A^*)`, `H¹(G,A) ≃+ Ĥ⁰(G,A^*)`, `Ĥ²(G,A) ≃+ Ĥ⁻¹(G, A^{***})`)
* `Work.Tate.Coinvariants` : the Tate sequence `0 → Ĥ⁻¹ → A_G → A^G → Ĥ⁰ → 0`
-/
import Submission.Work.Tate.Basic
import Submission.Work.Tate.CoindModule
import Submission.Work.Tate.coind_norm_eq_const
import Submission.Work.Tate.coind_fixed_iff_const
import Submission.Work.Tate.coind_augmentation_eq_ker_norm
import Submission.Work.Tate.coind_H0_subsingleton
import Submission.Work.Tate.coind_Hm1_subsingleton
import Submission.Work.Tate.H0_pi_subsingleton
import Submission.Work.Tate.Hm1_pi_subsingleton
import Submission.Work.Tate.CoindPi
import Submission.Work.Tate.SES
import Submission.Work.Tate.Delta
import Submission.Work.Tate.deltaLiftFun_zero
import Submission.Work.Tate.deltaLiftFun_add
import Submission.Work.Tate.deltaLiftFun_eq_zero_of_mem_augmentation
import Submission.Work.Tate.map_augmentation_eq_of_surjective
import Submission.Work.Tate.ker_Hm1g_eq_range_Hm1f
import Submission.Work.Tate.ker_H0g_eq_range_H0f
import Submission.Work.Tate.ker_delta_eq_range_Hm1g
import Submission.Work.Tate.range_delta_eq_ker_H0f
import Submission.Work.Tate.Shift
import Submission.Work.Tate.DimensionShift
import Submission.Work.Tate.Coinvariants
import Submission.Work.Tate.range_normCoinv_eq_ker_H0pi
import Submission.Work.Tate.range_Hm1ToCoinv_eq_ker_normCoinv
import Submission.Work.Tate.Hm1ToCoinv_injective
import Submission.Work.Tate.H0Map_id
import Submission.Work.Tate.Hm1Map_id
import Submission.Work.Tate.H0Map_bijective
import Submission.Work.Tate.Hm1Map_bijective
import Submission.Work.Tate.Equivs
import Submission.Work.Tate.CoindUp
import Submission.Work.Tate.Delta0
import Submission.Work.Tate.delta0CocycleOf_mem_Z1
import Submission.Work.Tate.delta0CocycleOf_sub_eq
import Submission.Work.Tate.delta0CocycleOf_add
import Submission.Work.Tate.delta0Cocycle_eq_coboundary_of_eq_norm
import Submission.Work.Tate.Delta0Map
import Submission.Work.Tate.ker_delta0_eq_range_H0g
import Submission.Work.Tate.range_delta0_eq_ker_mapH1
import Submission.Work.Tate.ker_deltaH1_eq_range_mapH1
import Submission.Work.Tate.range_deltaH1_eq_ker_mapH2
import Submission.Work.Tate.DimensionShiftH
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
