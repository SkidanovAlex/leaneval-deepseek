import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.Commons.Topology.Algebra.Valued.exp_ball_mem_nhds_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField WithZero
open IsDedekindDomain
open Filter Set Topology

set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

namespace Commons.NumberTheory.NumberField.Completion

/-!
# The ring of integers is dense in the ring of integers of the completion

For a number field `K` and a height-one prime `v` of its ring of integers, every element of the
ring of integers `v.adicCompletionIntegers K` of the `v`-adic completion of `K` lies in the
closure (inside the completion) of the image of the ring of integers `𝓞 K`.

The proof is analytic in spirit:

1. (reduction) in the completion, the `exp`-balls `{y | v (y - x) < exp n}` (`n : ℤ`) form a
   neighbourhood base of `x`, so `x` belongs to the closure of a set `S` as soon as for every
   `n : ℤ` there is `y ∈ S` with `v (y - x) < exp n`;
2. given such an `n`, either `n ≥ 1`, in which case `0 : 𝓞 K` is close enough to `x`
   (because `v x ≤ 1 < exp n`), or `n ≤ 0`: we first use density of `K` in its completion to
   find `t ∈ K` with `v (t - x) < exp (n - 1)`, which is integral (`v (t) ≤ 1`) by the
   ultrametric inequality since `v x ≤ 1` and `exp (n-1) ≤ 1`; then we use the fact
   (`HeightOneSpectrum.exists_valuation_sub_lt_of_integer`) that every integral element of `K`
   is arbitrarily well approximated by elements of `𝓞 K` to find `r : 𝓞 K` with
   `v (r - t) < exp (n - 1)`; the ultrametric inequality applied twice gives
   `v (r - x) < exp n`.
-/

variable {K : Type*} [Field K] [NumberField K]

/-- Reduction: if for every `n : ℤ` there is an element of `S` whose distance from `x` (measured
by the valuation) is `< exp n`, then `x` lies in the closure of `S`. -/
lemma mem_closure_of_forall_exp_ball (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) (S : Set (v.adicCompletion K))
    (h : ∀ n : ℤ, ∃ y ∈ S,
      Valued.v (y - x) < WithZero.exp n) :
    x ∈ closure S := by
  rw [mem_closure_iff_nhds]
  intro V hV
  rcases (Valued.mem_nhds.mp hV) with ⟨γ, hγ⟩
  let g : ℤᵐ⁰ := MonoidWithZeroHom.ValueGroup₀.embedding
    (γ : MonoidWithZeroHom.ValueGroup₀ ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) : v.adicCompletion K →*₀ ℤᵐ⁰))
  have hg0 : g ≠ 0 := by
    intro hg0
    have hγ0 : (γ : MonoidWithZeroHom.ValueGroup₀ ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) : v.adicCompletion K →*₀ ℤᵐ⁰)) ≠ 0 := Units.ne_zero γ
    apply hγ0
    exact (MonoidWithZeroHom.ValueGroup₀.embedding_inj.mp hg0)
  let n0 : ℤ := WithZero.log g
  have hexp : WithZero.exp n0 = g := WithZero.exp_log hg0
  rcases h n0 with ⟨y, hyS, hy⟩
  refine ⟨y, hγ ?_, hyS⟩
  change Valued.v.restrict (y - x) <
    (γ : MonoidWithZeroHom.ValueGroup₀ ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) : v.adicCompletion K →*₀ ℤᵐ⁰))
  rw [Valuation.restrict_lt_iff_lt_embedding (v := Valued.v)]
  change Valued.v (y - x) < g
  simpa [n0, hexp] using hy

/-- The `exp`-balls around `x` in the completion are neighbourhoods of `x`. -/
lemma exp_ball_nhds (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) (n : ℤ) :
    {y : v.adicCompletion K | Valued.v (y - x) < WithZero.exp n} ∈ 𝓝 x := by
  have hf : Continuous (fun y : v.adicCompletion K => y - x) := continuous_sub_right x
  have hball0 : {z : v.adicCompletion K | Valued.v z < WithZero.exp n} ∈ 𝓝 (0 : v.adicCompletion K) := by
    exact (Commons.Topology.Algebra.Valued.exp_ball_mem_nhds_zero (K := v.adicCompletion K) n)
  have htr : {z : v.adicCompletion K | Valued.v z < WithZero.exp n} ∈ 𝓝 (x - x) := by
    simpa using hball0
  simpa [Set.preimage] using (hf.continuousAt.preimage_mem_nhds htr)

/-- Density of `K` in its completion: every `exp`-ball around `x` contains an element of `K`. -/
lemma exists_algebraMap_mem_exp_ball (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) (n : ℤ) :
    ∃ t : K, Valued.v (algebraMap K (v.adicCompletion K) t - x) < WithZero.exp n := by
  have hx : x ∈ closure (Set.range (algebraMap K (v.adicCompletion K))) := by
    have hd : Dense (Set.range (algebraMap K (v.adicCompletion K))) :=
      (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) K v)
    rw [hd.closure_eq]
    trivial
  rcases (mem_closure_iff_nhds.mp hx) {y : v.adicCompletion K |
      Valued.v (y - x) < WithZero.exp n} (exp_ball_nhds v x n) with ⟨y, hyb, hyr⟩
  rcases hyr with ⟨t, rfl⟩
  exact ⟨t, hyb⟩

/-- The embedding of `K` into its completion preserves the valuation. -/
lemma valued_alg_eq (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (t : K) :
    Valued.v (algebraMap K (v.adicCompletion K) t) = v.valuation K t := by
  calc
    Valued.v (algebraMap K (v.adicCompletion K) t)
        = Valued.v (t : v.adicCompletion K) := by
          rw [show algebraMap K (v.adicCompletion K) t = (t : v.adicCompletion K) from rfl]
    _ = v.valuation K t :=
          IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
            (R := 𝓞 K) (v := v) t

/-- Ultrametric inequality for the valuation of the completion. -/
lemma val_add_le_max (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (a b : v.adicCompletion K) :
    Valued.v (a + b) ≤ max (Valued.v a) (Valued.v b) := by
  exact (Valuation.map_add_le_max' (self := Valued.v) a b)

/-- The ring of integers of a number field is dense in the ring of integers of the completion. -/
theorem ringOfIntegers_dense_in_adicIntegers (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : v.adicCompletionIntegers K) :
    (x : v.adicCompletion K) ∈ closure
      {y : v.adicCompletion K | ∃ r : 𝓞 K, (algebraMap K (v.adicCompletion K) (r : K)) = y} := by
  have hxle : Valued.v (x : v.adicCompletion K) ≤ (1 : ℤᵐ⁰) := by
    exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).mp x.2
  apply mem_closure_of_forall_exp_ball v (x : v.adicCompletion K)
    {y : v.adicCompletion K | ∃ r : 𝓞 K, (algebraMap K (v.adicCompletion K) (r : K)) = y}
  intro n0
  by_cases hn0 : n0 ≤ 0
  · -- approximation at level `exp (n0 - 1)` in two steps
    let m : ℤ := n0 - 1
    have hmn : m < n0 := by omega
    have hm0 : m ≤ 0 := by omega
    have hexpm1 : WithZero.exp m ≤ (1 : ℤᵐ⁰) := by
      simpa using (WithZero.exp_le_exp).mpr hm0
    obtain ⟨t, ht⟩ := exists_algebraMap_mem_exp_ball v (x : v.adicCompletion K) m
    have htle : Valued.v (algebraMap K (v.adicCompletion K) t - (x : v.adicCompletion K))
        ≤ (1 : ℤᵐ⁰) :=
      le_of_lt (lt_of_lt_of_le ht hexpm1)
    have htvle : Valued.v (algebraMap K (v.adicCompletion K) t) ≤ (1 : ℤᵐ⁰) := by
      have hsplit : algebraMap K (v.adicCompletion K) t =
          (algebraMap K (v.adicCompletion K) t - (x : v.adicCompletion K)) + (x : v.adicCompletion K) := by
        abel
      rw [hsplit]
      exact le_trans (val_add_le_max v _ _) (max_le htle hxle)
    have hwt : v.valuation K t ≤ (1 : ℤᵐ⁰) := by
      rwa [valued_alg_eq v t] at htvle
    obtain ⟨a, ha⟩ :=
      IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer (R := 𝓞 K) v
        hwt (WithZero.expEquiv m)
    have ha_exp : v.valuation K ((a : K) - t) < WithZero.exp m := by
      have ha' : v.valuation K (algebraMap (𝓞 K) K a - t) < WithZero.exp m := by
        simpa [WithZero.coe_expEquiv_apply] using ha
      simpa using ha'
    have hva_exp : Valued.v
        (algebraMap K (v.adicCompletion K) (a : K) - algebraMap K (v.adicCompletion K) t) <
          WithZero.exp m := by
      rw [← map_sub]
      rw [valued_alg_eq v ((a : K) - t)]
      exact ha_exp
    refine ⟨algebraMap K (v.adicCompletion K) (a : K), ⟨a, rfl⟩, ?_⟩
    have hmain : Valued.v
        (algebraMap K (v.adicCompletion K) (a : K) - (x : v.adicCompletion K)) <
          WithZero.exp m := by
      have hsplit : algebraMap K (v.adicCompletion K) (a : K) - (x : v.adicCompletion K) =
          (algebraMap K (v.adicCompletion K) (a : K) - algebraMap K (v.adicCompletion K) t) +
            (algebraMap K (v.adicCompletion K) t - (x : v.adicCompletion K)) := by
        abel
      rw [hsplit]
      exact lt_of_le_of_lt (val_add_le_max v _ _) (max_lt hva_exp ht)
    exact lt_trans hmain ((WithZero.exp_lt_exp).mpr hmn)
  · have hn0pos : (0 : ℤ) < n0 := by omega
    have h1lt : (1 : ℤᵐ⁰) < WithZero.exp n0 := by
      simpa using (WithZero.exp_lt_exp).mpr hn0pos
    refine ⟨algebraMap K (v.adicCompletion K) ((0 : 𝓞 K) : K), ⟨0, rfl⟩, ?_⟩
    have hxlt : Valued.v (x : v.adicCompletion K) < WithZero.exp n0 := lt_of_le_of_lt hxle h1lt
    have hy : algebraMap K (v.adicCompletion K) ((0 : 𝓞 K) : K) - (x : v.adicCompletion K) =
        -(x : v.adicCompletion K) := by
      simp
    rw [hy, Valuation.map_neg]
    exact hxlt

end Commons.NumberTheory.NumberField.Completion