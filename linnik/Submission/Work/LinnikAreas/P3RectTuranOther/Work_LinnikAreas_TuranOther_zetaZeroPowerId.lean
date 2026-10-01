import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_XiAux
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_ZSBase
import Submission.Work.LinnikAreas.PrincipalZeroCount
import Submission.Work.LinnikAreas.tendsto_finsum_divisor_closedBall_mero
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_FarRepel_xiDerivPF
import Submission.Work.LinnikAreas.FarRepel.digammaDerivSeries
import Submission.Work.LinnikAreas.FarRepel.digammaDerivSeriesSummable
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_FarRepel_iteratedDeriv_logDeriv_Xi
import Submission.Work.LinnikAreas.xiCZeroInvSqTailBound
import Submission.Commons.Analysis.InfiniteSum.summable_of_finset_tail_bound
import Submission.Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole
import Submission.Work.LinnikAreas.P3RectTuranOther.Work_LinnikAreas_TuranOther_orderXi_eq_orderLambda
import Submission.Work.LinnikAreas.TuranOther.orderZeta_eq_orderLambda_add_invGammaR
import Submission.Work.LinnikAreas.TuranOther.orderInvGammaR_eq_indicator
import Submission.Work.LinnikAreas.TuranOther.iteratedDeriv_logDeriv_GammaR
import Submission.Work.LinnikAreas.P3RectTuranOther.Work_LinnikAreas_TuranOther_xiDerivZeroSum

open scoped Classical BigOperators Topology
open Filter

noncomputable section

namespace Work.LinnikAreas.TuranOther

/-- The set `{-2n : n : ℕ}` of the trivial zeros of the Riemann zeta function, equivalently the
pole set of `Γℝ`. -/
def trivZerosSet : Set ℂ := Set.range (fun n : ℕ => -((2 * n : ℕ) : ℂ))

/-- The multiplicity of `u` as a *trivial* zero of `ζ`: `1` on `trivZerosSet`, `0` elsewhere. -/
def trivMult (u : ℂ) : ℕ := trivZerosSet.indicator (fun _ => 1) u

lemma trivMult_apply (u : ℂ) :
    trivMult u = trivZerosSet.indicator (fun _ => (1 : ℕ)) u := rfl

lemma trivMult_eq_one_of_mem {u : ℂ} (hu : u ∈ trivZerosSet) : trivMult u = 1 :=
  Set.indicator_of_mem hu 1

lemma trivMult_eq_zero_of_notMem {u : ℂ} (hu : u ∉ trivZerosSet) : trivMult u = 0 :=
  Set.indicator_of_notMem hu 1

lemma zero_mem_trivZerosSet : (0 : ℂ) ∈ trivZerosSet := ⟨0, by simp⟩

lemma neg_two_mul_mem_trivZerosSet (n : ℕ) :
    -((2 * n : ℕ) : ℂ) ∈ trivZerosSet := ⟨n, rfl⟩

/-- Reindexing a family carried by `trivZerosSet` by the bijection `n ↦ -2n`. -/
lemma hasSum_trivMult_mul_iff (w : ℂ → ℂ) (L : ℂ) :
    HasSum (fun u : ℂ => (trivMult u : ℂ) * w u) L ↔
      HasSum (fun n : ℕ => w (-((2 * n : ℕ) : ℂ))) L := by
  classical
  refine hasSum_iff_hasSum_of_ne_zero_bij
    (i := fun n : ↑(Function.support (fun n : ℕ => w (-((2 * n : ℕ) : ℂ)))) =>
      -((2 * (n : ℕ) : ℕ) : ℂ)) ?_ ?_ ?_
  · intro a b hab
    have hab' : ((2 * (a : ℕ) : ℕ) : ℂ) = ((2 * (b : ℕ) : ℕ) : ℂ) := by
      simpa using neg_inj.mp hab
    have h : 2 * (a : ℕ) = 2 * (b : ℕ) := Nat.cast_injective hab'
    exact Subtype.ext (Nat.mul_left_cancel (by norm_num) h)
  · intro u hu
    rw [Function.mem_support] at hu
    have ht : trivMult u ≠ 0 := fun h => hu (by rw [h, Nat.cast_zero, zero_mul])
    have hu' : u ∈ trivZerosSet := by
      by_contra h
      exact ht (trivMult_eq_zero_of_notMem h)
    obtain ⟨n, hn⟩ := hu'
    refine ⟨⟨n, ?_⟩, ?_⟩
    · rw [Function.mem_support]
      have hwu : w u ≠ 0 := fun h => hu (by rw [h, mul_zero])
      rwa [← hn] at hwu
    · exact hn
  · intro x
    show (trivMult (-((2 * ((x : ℕ)) : ℕ) : ℂ)) : ℂ) * w (-((2 * ((x : ℕ)) : ℕ) : ℂ))
      = w (-((2 * ((x : ℕ)) : ℕ) : ℂ))
    rw [trivMult_eq_one_of_mem (neg_two_mul_mem_trivZerosSet (x : ℕ)), Nat.cast_one, one_mul]

lemma summable_trivMult_mul_iff (w : ℂ → ℂ) :
    Summable (fun u : ℂ => (trivMult u : ℂ) * w u) ↔
      Summable (fun n : ℕ => w (-((2 * n : ℕ) : ℂ))) :=
  ⟨fun h => (hasSum_trivMult_mul_iff w (∑' u : ℂ, (trivMult u : ℂ) * w u)).mp h.hasSum |>.summable,
   fun h => (hasSum_trivMult_mul_iff w (∑' n : ℕ, w (-((2 * n : ℕ) : ℂ)))).mpr h.hasSum |>.summable⟩

/-- The series `∑_n (s + 2n)^{-(k+1)}` converges for `k ≥ 1`. -/
lemma summable_inv_add_two_mul (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1)) := by
  have hk1 : 1 < k + 1 := by omega
  have hg : Summable (fun n : ℕ => (1 / (n : ℝ)) ^ (k + 1)) := by
    rw [show (fun n : ℕ => (1 / (n : ℝ)) ^ (k + 1))
        = fun n : ℕ => 1 / (n : ℝ) ^ (k + 1) from funext (fun n => one_div_pow _ _)]
    exact (Real.summable_one_div_nat_pow (p := k + 1)).mpr hk1
  refine Summable.of_norm_bounded_eventually hg ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (⌈‖s‖⌉₊ + 1)] with n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : (⌈‖s‖⌉₊ : ℕ) + 1 ≤ n := hn
    exact_mod_cast (by omega : 1 ≤ n)
  have hnorm : (n : ℝ) ≤ ‖s + ((2 * n : ℕ) : ℂ)‖ := by
    have hcast : ‖((2 * n : ℕ) : ℂ)‖ = 2 * (n : ℝ) := by
      rw [Complex.norm_natCast]; push_cast; ring
    have h2 : (2 : ℝ) * n - ‖s‖ ≤ ‖s + ((2 * n : ℕ) : ℂ)‖ := by
      have h := norm_sub_le (s + ((2 * n : ℕ) : ℂ)) s
      simp only [add_sub_cancel_left] at h
      rw [hcast] at h
      linarith
    have h3 : ‖s‖ ≤ (n : ℝ) := by
      have h4 : ‖s‖ ≤ (⌈‖s‖⌉₊ : ℝ) := Nat.le_ceil ‖s‖
      have h5 : (⌈‖s‖⌉₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    linarith
  rw [norm_pow, norm_div, norm_one]
  exact pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le (by linarith) hnorm) (k + 1)

/-- The `trivZerosSet`-supported family is summable, and its total is the `ℕ`-indexed series. -/
lemma summable_trivMult_weight (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun u : ℂ => (trivMult u : ℂ) * (1 / (s - u)) ^ (k + 1)) := by
  rw [summable_trivMult_mul_iff]
  simpa only [sub_neg_eq_add] using summable_inv_add_two_mul k hk hs

lemma tsum_trivMult_weight (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    (∑' u : ℂ, (trivMult u : ℂ) * (1 / (s - u)) ^ (k + 1))
      = ∑' n : ℕ, (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1) := by
  have h := hasSum_trivMult_mul_iff (fun u : ℂ => (1 / (s - u)) ^ (k + 1))
    (∑' n : ℕ, (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1))
  have hg : HasSum (fun n : ℕ => (1 / (s - (-((2 * n : ℕ) : ℂ)))) ^ (k + 1))
      (∑' n : ℕ, (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1)) := by
    simpa only [sub_neg_eq_add] using (summable_inv_add_two_mul k hk hs).hasSum
  exact (h.mpr hg).tsum_eq

/-! ## 2. Placeholders for the delegated auxiliary results (replaced by imports at the end) -/

private theorem orderInvGammaR_eq_indicator_aux (u : ℂ) :
    analyticOrderNatAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) u
      = trivZerosSet.indicator (fun _ => (1 : ℕ)) u := by
  rw [trivZerosSet]
  exact Work.LinnikAreas.TuranOther.orderInvGammaR_eq_indicator u

/-! ## 3. Multiplicities -/

/-- The vanishing multiplicity of `u` as a zero of `ζ` is the multiplicity as a zero of the
entire completion `Ξ`, plus one at the trivial zeros `-2n`, minus one at `u = 0` (where
`ζ(0) = -1/2 ≠ 0` although `Λ` has a pole and `(Γℝ)⁻¹` a simple zero). -/
theorem mult_zeta_eq_mult_xi_add (u : ℂ) :
    (analyticOrderNatAt riemannZeta u : ℂ)
      = (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ) + (trivMult u : ℂ)
        - (if u = 0 then (1 : ℂ) else 0) := by
  rcases eq_or_ne u 0 with rfl | hu
  · have hζ : analyticOrderNatAt riemannZeta 0 = 0 := by
      have h : analyticOrderAt riemannZeta 0 = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr (by rw [riemannZeta_zero]; norm_num))
      simp [analyticOrderNatAt, h]
    have hΞ : analyticOrderNatAt Work.LinnikAreas.DhK.Xi 0 = 0 := by
      have h : analyticOrderAt Work.LinnikAreas.DhK.Xi 0 = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr Work.LinnikAreas.DhK.Xi_zero_ne)
      simp [analyticOrderNatAt, h]
    have ht : trivMult (0 : ℂ) = 1 := trivMult_eq_one_of_mem zero_mem_trivZerosSet
    rw [hζ, hΞ, ht]
    norm_num
  · have h1 := orderXi_eq_orderLambda u
    have h2 := orderZeta_eq_orderLambda_add_invGammaR u hu
    have h3 := orderInvGammaR_eq_indicator_aux u
    have hnat : analyticOrderNatAt riemannZeta u
        = analyticOrderNatAt Work.LinnikAreas.DhK.Xi u + trivMult u := by
      rw [h2, ← h1, h3, trivMult_apply]
    rw [hnat]
    push_cast
    simp [hu]

/-! ## 4. The multiplicity-weighted power sum over the zeros of `ζ` -/

lemma summable_indicator_zero (k : ℕ) (s : ℂ) :
    Summable (fun u : ℂ => (if u = 0 then (1 : ℂ) else 0) * (1 / (s - u)) ^ (k + 1)) :=
  (hasSum_single (0 : ℂ) (fun b hb => by simp [hb])).summable

lemma pointwise_mult_split (k : ℕ) (s : ℂ) (u : ℂ) :
    (analyticOrderNatAt riemannZeta u : ℂ) * (1 / (s - u)) ^ (k + 1)
      = (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ) * (1 / (s - u)) ^ (k + 1)
        + (trivMult u : ℂ) * (1 / (s - u)) ^ (k + 1)
        - (if u = 0 then (1 : ℂ) else 0) * (1 / (s - u)) ^ (k + 1) := by
  rw [mult_zeta_eq_mult_xi_add u]
  ring

lemma summable_zeta_weight (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun u : ℂ => (analyticOrderNatAt riemannZeta u : ℂ) * (1 / (s - u)) ^ (k + 1)) := by
  obtain ⟨hsumΞ, -⟩ := xiDerivZeroSum k hk hs
  have hsumTriv := summable_trivMult_weight k hk hs
  have hsumInd := summable_indicator_zero k s
  exact ((hsumΞ.add hsumTriv).sub hsumInd).congr
    (fun u => (pointwise_mult_split k s u).symm)

/-- The `ζ`-power sum is the `Ξ`-power sum, plus the trivial-zero series, minus the `u = 0` term. -/
lemma tsum_zeta_eq (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    (∑' u : ℂ, (analyticOrderNatAt riemannZeta u : ℂ) * (1 / (s - u)) ^ (k + 1))
      = (∑' u : ℂ, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ) * (1 / (s - u)) ^ (k + 1))
        + (∑' n : ℕ, (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1))
        - (1 / s) ^ (k + 1) := by
  obtain ⟨hsumΞ, -⟩ := xiDerivZeroSum k hk hs
  have hsumTriv := summable_trivMult_weight k hk hs
  have hsumInd := summable_indicator_zero k s
  have hsplit : (∑' u : ℂ, (analyticOrderNatAt riemannZeta u : ℂ) * (1 / (s - u)) ^ (k + 1))
      = (∑' u : ℂ, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ) * (1 / (s - u)) ^ (k + 1))
        + (∑' u : ℂ, (trivMult u : ℂ) * (1 / (s - u)) ^ (k + 1))
        - (∑' u : ℂ, (if u = 0 then (1 : ℂ) else 0) * (1 / (s - u)) ^ (k + 1)) := by
    rw [tsum_congr (fun u => pointwise_mult_split k s u),
      Summable.tsum_sub (hsumΞ.add hsumTriv) hsumInd,
      Summable.tsum_add hsumΞ hsumTriv]
  have hind : (∑' u : ℂ, (if u = 0 then (1 : ℂ) else 0) * (1 / (s - u)) ^ (k + 1))
      = (1 / s) ^ (k + 1) := by
    rw [tsum_eq_single (0 : ℂ) (fun b hb => by simp [hb])]
    simp
  rw [hsplit, hind, tsum_trivMult_weight k hk hs]

/-- The final algebraic rearrangement: clearing the factor `1/k!` against `k!`, with the
trivial-zero series `B` moved to the other side of the difference. -/
lemma final_identity (A B : ℂ) (k : ℕ) (s : ℂ) :
    (A + B - (1 / s) ^ (k + 1)) - 1 / (s - 1) ^ (k + 1)
      = -(1 / ((k.factorial : ℕ) : ℂ)) * (-1 * ((k.factorial : ℕ) : ℂ)
          * (A - (1 / s) ^ (k + 1) - (1 / (s - 1)) ^ (k + 1) + B)) := by
  rw [← one_div_pow]
  have h : ((k.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [neg_mul, one_div]
  field_simp
  abel

/-! ## 5. The main theorem -/

theorem zetaZeroPowerId (j : ℕ) (hj : 1 ≤ j) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun u : ℂ => ((analyticOrderNatAt riemannZeta u : ℕ) : ℂ) * (1 / (s - u)) ^ (2 * j)) ∧
    (∑' u : ℂ, ((analyticOrderNatAt riemannZeta u : ℕ) : ℂ) * (1 / (s - u)) ^ (2 * j))
      - (1 / (s - 1) ^ (2 * j))
      = - (1 / (((2 * j - 1).factorial : ℕ) : ℂ)) *
          iteratedDeriv (2 * j - 1) (logDeriv riemannZeta) s := by
  classical
  set k : ℕ := 2 * j - 1 with hkdef
  have hk : 1 ≤ k := by omega
  have hk1 : k + 1 = 2 * j := by omega
  have hodd : Odd k := ⟨j - 1, by omega⟩
  have hneg : (-1 : ℂ) ^ k = -1 := hodd.neg_one_pow
  obtain ⟨hsumΞ, hidΞ⟩ := xiDerivZeroSum k hk hs
  have hΓ := iteratedDeriv_logDeriv_GammaR k hk hs
  have hdec := Work.LinnikAreas.FarRepel.iteratedDeriv_logDeriv_Xi k hk hs
  set ZΞ : ℂ := ∑' u : ℂ, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ) * (1 / (s - u)) ^ (k + 1)
    with hZΞ
  set G : ℂ := ∑' n : ℕ, (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1) with hG
  -- the `Ξ`- and `Γℝ`-derivative identities in terms of `ZΞ`, `G`
  have h1 : iteratedDeriv k (logDeriv Work.LinnikAreas.DhK.Xi) s
      = (-1 : ℂ) ^ k * (k.factorial : ℂ) * ZΞ := by
    rw [hidΞ, hZΞ]
  have h2 : iteratedDeriv k (logDeriv Complex.Gammaℝ) s
      = (-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ) * G := by
    rw [hΓ, hG]
  -- the derivative of `logDeriv ζ`
  have hDζ : iteratedDeriv k (logDeriv riemannZeta) s
      = (-1 : ℂ) ^ k * (k.factorial : ℂ)
          * (ZΞ - (1 / s) ^ (k + 1) - (1 / (s - 1)) ^ (k + 1) + G) := by
    have h3 := hdec
    rw [h1, h2] at h3
    have hp : (-1 : ℂ) ^ (k + 1) = -((-1 : ℂ) ^ k) := by
      rw [pow_succ]; ring
    rw [hp] at h3
    rw [show (-1 : ℂ) ^ k * (k.factorial : ℂ) * (ZΞ - (1 / s) ^ (k + 1) - (1 / (s - 1)) ^ (k + 1) + G)
        = (-1 : ℂ) ^ k * (k.factorial : ℂ) * ZΞ
          - (-1 : ℂ) ^ k * (k.factorial : ℂ) * (1 / s) ^ (k + 1)
          - (-1 : ℂ) ^ k * (k.factorial : ℂ) * (1 / (s - 1)) ^ (k + 1)
          + (-1 : ℂ) ^ k * (k.factorial : ℂ) * G by ring]
    rw [h3]
    ring
  -- the `ζ`-power sum
  have hZ := tsum_zeta_eq k hk hs
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hs1 : s - 1 ≠ 0 := fun h => by
    have : s = 1 := sub_eq_zero.mp h
    rw [this] at hs; norm_num at hs
  have hZ' : (∑' u : ℂ, (analyticOrderNatAt riemannZeta u : ℂ) * (1 / (s - u)) ^ (k + 1))
      = ZΞ + G - (1 / s) ^ (k + 1) := by
    rw [hZ, ← hZΞ, ← hG]
  rw [← hk1]
  refine ⟨summable_zeta_weight k hk hs, ?_⟩
  rw [hZ', hDζ, hneg]
  exact final_identity ZΞ G k s

end Work.LinnikAreas.TuranOther
