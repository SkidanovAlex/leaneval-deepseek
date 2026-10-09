/-
Work of the Neukirch–Uchida team: the analytic input of Čebotarev's theorem.

An aggregate module importing every module of the `NK.HeckeL` chapter (other than this one and
the smoke test `Usage`).  See `README.md` in this directory for the map of definitions and main
results.
-/
import Submission.NK.HeckeL.Artin
import Submission.NK.HeckeL.Basic
import Submission.NK.HeckeL.Basic.classOfIdeal_mul
import Submission.NK.HeckeL.Basic.finite_setOf_not_isUnramifiedIn
import Submission.NK.HeckeL.Basic.ideal_eq_prod_finsupp
import Submission.NK.HeckeL.Basic.ideleOfFun_add
import Submission.NK.HeckeL.Basic.ideleOfIdeal_mul
import Submission.NK.HeckeL.Basic.rayChar_atIdeal_mul
import Submission.NK.HeckeL.Consequences.abelianLFunctions
import Submission.NK.HeckeL.Consequences.exists_primeClass_eq
import Submission.NK.HeckeL.Consequences.exists_prime_isFrobAtPrime_outside
import Submission.NK.HeckeL.Consequences.heckeLRegular_value_ne_zero
import Submission.NK.HeckeL.Consequences.infinite_isFrobAtPrime
import Submission.NK.HeckeL.Consequences.primeSum_isBigO
import Submission.NK.HeckeL.Dictionary
import Submission.NK.HeckeL.Nonvanishing.artinLSeries_value_ne_zero
import Submission.NK.HeckeL.Nonvanishing.artinPrimeSum_isBigO
import Submission.NK.HeckeL.Nonvanishing.exists_tendsto_zetaUnramified_div_ne_zero
import Submission.NK.HeckeL.Nonvanishing.fiberProduct
import Submission.NK.HeckeL.Nonvanishing.primeFiber
import Submission.NK.HeckeL.Nonvanishing.prod_artinLSeries_eq_zetaUnramified
import Submission.NK.HeckeL.Nonvanishing.tendsto_dedekindZeta_re_div
import Submission.NK.HeckeL.Nonvanishing.zetaUnramifiedK_eq_dedekindZeta_mul
import Submission.NK.HeckeL.Nonvanishing.zetaUnramified_eq_dedekindZeta_mul
import Submission.NK.HeckeL.Nonvanishing.zetaUnramified_eq_dedekindZeta_mul_of_liesOver
import Submission.NK.HeckeL.Nonvanishing.zetaUnramified_eq_tprod_primesOver
import Submission.NK.HeckeL.Product.artinLSeries_one
import Submission.NK.HeckeL.Product.dedekindZeta_eulerProduct
import Submission.NK.HeckeL.Product.prod_artinLSeries_eq
import Submission.NK.HeckeL.Product.prod_artinLSeries_eq_aux
import Submission.NK.HeckeL.Product.prod_comp_eq_pow_card_ker
import Submission.NK.HeckeL.Product.prod_monoidHom_one_sub_mul
import Submission.NK.HeckeL.Product.prod_nthRootsFinset_one_sub_mul
import Submission.NK.HeckeL.Product.prod_zpowers_monoidHom_one_sub_mul
import Submission.NK.HeckeL.Product.tendsto_zetaUnramified_div
import Submission.NK.HeckeL.Product.zetaUnramified_eq_tprod_fiber
import Submission.NK.HeckeL.Product.zeta_eulerFactor_liesOver
import Submission.NK.HeckeL.Series.artinPrimeSum_sub_artinLogEulerProduct_isBigO
import Submission.NK.HeckeL.Series.charPrimeSum_eq_sum_add_artinPrimeSum
import Submission.NK.HeckeL.Series.continuousOn_artinLSeries
import Submission.NK.HeckeL.Series.continuousOn_artinLogEulerProduct
import Submission.NK.HeckeL.Series.exists_units_factor_ne_one
import Submission.NK.HeckeL.Series.exp_artinLogEulerProduct
import Submission.NK.HeckeL.Series.hasProd_artinEulerFactor
import Submission.NK.HeckeL.Series.heckeLSeries_eq_heckeEulerProduct
import Submission.NK.HeckeL.Series.isBigO_of_continuous_exp_eq
import Submission.NK.HeckeL.Series.log_norm_artinLSeries_eq_tsum
import Submission.NK.HeckeL.Series.re_artinPrimeSum_sub_log_isBigO
import Submission.NK.HeckeL.Series.summable_finsupp_prod_pow
import Submission.NK.HeckeL.Series.tendsto_tsum_subtype_of_cofinal
import Submission.NK.HeckeL.Series.tsum_finsupp_support_subset_prod
import Submission.NK.HeckeL.Zeta
import Submission.NK.HeckeL.artinLSeries_tendsto_of_hecke
import Submission.NK.HeckeL.heckeEulerProduct_eq_artinLSeries
import Submission.NK.HeckeL.heckeLSeries_tendsto_of_artin
import Submission.NK.HeckeL.primeSum_eq_artinPrimeSum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
