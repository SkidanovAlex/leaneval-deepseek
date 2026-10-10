import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localUnits_iff_localAlgebraMapUnits
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.HassePrinciple.ideleInclusion_smul_of_restrict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open NumberField IsDedekindDomain

theorem unitsMap_mem_localUnits {K : Type} [Field K] [NumberField K] (u : Kˣ) {m : ℕ}
    (hm : m ≠ 0) (hu : u ^ m = 1) (v : NK.GlobalCFT.Place K) :
    Units.map (algebraMap K (NK.GlobalCFT.Place.localField K v)) u ∈
      NK.GlobalCFT.Place.localUnits K v := by
  rcases v with w | q
  · rw [NK.GlobalCFT.Place.localUnits_ofInfinite]
    exact Subgroup.mem_top _
  · rw [NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one]
    rw [Units.coe_map]
    change Valued.v (algebraMap K (q.adicCompletion K) (↑u : K)) = 1
    rw [show algebraMap K (q.adicCompletion K) (↑u : K) = ((↑u : K) : q.adicCompletion K) from
      congrFun (IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion
        (v := q) (S := K) (K := K)) (↑u : K)]
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have huK : (↑u : K) ^ m = 1 := by
      rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
    have hpow : (q.valuation K (↑u : K)) ^ m = 1 := by
      rw [← map_pow, huK, map_one]
    exact (pow_eq_one_iff_left hm).mp hpow

end Work.SSGRoute
