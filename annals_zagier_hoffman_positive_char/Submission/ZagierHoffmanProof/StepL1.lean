import Submission.ZagierHoffmanProof.Block
import Submission.ZagierHoffmanProof.StepB8
import Submission.Commons.Topology.InfiniteSum.fin_sum_tsum
import Submission.Commons.Topology.InfiniteSum.tsum_shift_one
import Submission.Commons.Topology.InfiniteSum.summable_fin_sum
import Mathlib.Topology.Algebra.InfiniteSum.Ring

set_option autoImplicit false
set_option maxHeartbeats 100000000
open scoped BigOperators

/-!
# Step L1: the ζ-level bridge from level-wise power-sum relations (paper §2.2/Remark 2.4)

§2.2–3 of the paper works with *binary relations*: K-linear identities between the
level-`d` power sums `S_d(s)` that hold for *every* level `d` (e.g. R1 = (2.8)):
`Σ_i a_i·S_d(s_i) + Σ_i b_i·S_{d+1}(t_i) = 0` for all `d`.  Remark 2.4 passes such an
identity to the ζ-level by summing over `d`.  This file provides that bridge
(`zeta_fixed_bridge` / `zeta_mixed_bridge`) plus the two analytic facts it needs:
the level-family `d ↦ S_d(𝔰)` is summable, and the level-0 block of any tuple of depth
`≥ 2` is empty (`S_0(𝔰) = 0`).

Coefficients live in `K = RatFunc F` and act on `K∞ = RatFunc.CompletionAtInfty F` by
ring multiplication with their image under the algebra map.  Index families are finite
(`Fintype`), with per-element depths `dep`, positivity proofs `hdep` and exponent tuples
`c : ∀ i, Fin (dep i) → ℕ+` — the same carrier shape as `P1Data`/`P2Data` (StepI).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

-- The S-family over levels d is summable.
lemma summable_S {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) :
    Summable (fun d : ℕ => S F r hr 𝔰 d) := by
  classical
  let g : monicStrictAntiNatDegree F r → ℕ := fun a => (a.val ⟨0, hr⟩).natDegree
  let e : ((d : ℕ) × {a : monicStrictAntiNatDegree F r // g a = d}) ≃
      monicStrictAntiNatDegree F r := Equiv.sigmaFiberEquiv g
  have hz : Summable (fun a : monicStrictAntiNatDegree F r => zetaTerm F 𝔰 a) :=
    summable_zeta_term F (r := r) hr 𝔰
  have hσsum : Summable (fun p : (d : ℕ) × {a : monicStrictAntiNatDegree F r // g a = d} =>
      zetaTerm F 𝔰 p.2.1) := by
    have hss : Summable (fun p : (d : ℕ) × {a : monicStrictAntiNatDegree F r // g a = d} =>
        zetaTerm F 𝔰 (e p)) := (Equiv.summable_iff e).mpr hz
    refine Summable.congr hss ?_
    intro p
    congr
  have hfiber : ∀ d : ℕ, Summable (fun c : {a : monicStrictAntiNatDegree F r // g a = d} =>
      zetaTerm F 𝔰 c.1) := by
    intro d
    have hfin : Finite {a : monicStrictAntiNatDegree F r // a ∈ blockSet F r hr d} :=
      finite_block F hr d
    change Finite {a : monicStrictAntiNatDegree F r // g a = d} at hfin
    exact Summable.of_finite (f := fun c : {a : monicStrictAntiNatDegree F r // g a = d} =>
      zetaTerm F 𝔰 c.1)
  have hm := Summable.sigma' (β := ℕ)
      (γ := fun d : ℕ => {a : monicStrictAntiNatDegree F r // g a = d}) hσsum hfiber
  rw [show (fun d : ℕ => S F r hr 𝔰 d) =
      fun d => ∑' c : {a : monicStrictAntiNatDegree F r // g a = d}, zetaTerm F 𝔰 c.1 from by
        funext d
        rfl]
  exact hm

-- Level-0 blocks of depth ≥ 2 are empty ⇒ S at level 0 vanishes.
lemma S_zero_of_depth_ge_two {r : ℕ} (hr : 0 < r) (hbig : 1 < r) (𝔰 : Fin r → ℕ+) :
    S F r hr 𝔰 0 = 0 := by
  classical
  let A := {a : monicStrictAntiNatDegree F r // a ∈ blockSet F r hr 0}
  have hBempty : ∀ a : A, False := by
    intro a
    have hdeg0 : (a.1.val ⟨0, hr⟩).natDegree = 0 := by
      exact a.2
    have hs := a.1.2.1
    have h01 : (⟨0, hr⟩ : Fin r) < ⟨1, hbig⟩ := by
      change (0 : ℕ) < 1
      omega
    have hlt := hs h01
    change (a.1.val ⟨1, hbig⟩).natDegree < (a.1.val ⟨0, hr⟩).natDegree at hlt
    rw [hdeg0] at hlt
    omega
  haveI hfin : Finite A := by
    dsimp [A]
    exact finite_block F hr 0
  letI : Fintype A := Fintype.ofFinite (α := A)
  change (∑' a : A, zetaTerm F 𝔰 a.1) = 0
  rw [tsum_fintype]
  apply Finset.sum_eq_zero
  intro a ha
  exact False.elim (hBempty a)

-- FIXED relation ζ-bridge: ∀ d, Σ_i a_i·S_d(u_i) = 0  ⇒  Σ_i a_i·ζ_A(u_i) = 0
theorem zeta_fixed_bridge {ι : Type*} [Fintype ι]
    (dep : ι → ℕ) (hdep : ∀ i, 0 < dep i) (c : ∀ i, Fin (dep i) → ℕ+)
    (a : ι → RatFunc F)
    (h : ∀ d : ℕ, ∑ i, ((a i : RatFunc.CompletionAtInfty F) *
        S F (dep i) (hdep i) (c i) d) = 0) :
    ∑ i, ((a i : RatFunc.CompletionAtInfty F) * ζ_A F (c i)) = 0 := by
  classical
  let K := RatFunc.CompletionAtInfty F
  have hsum : ∀ i : ι, Summable (fun d : ℕ =>
      (a i : K) * S F (dep i) (hdep i) (c i) d) := by
    intro i
    exact (summable_S F (hdep i) (c i)).mul_left (a i : K)
  calc
    (∑ i : ι, ((a i : K) * ζ_A F (c i)))
        = ∑ i : ι, ∑' d : ℕ, ((a i : K) * S F (dep i) (hdep i) (c i) d) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [zeta_eq_tsum_block F (hdep i) (c i)]
          rw [← tsum_mul_left]
    _ = ∑' d : ℕ, (∑ i : ι, (a i : K) * S F (dep i) (hdep i) (c i) d) := by
          exact Commons.Topology.InfiniteSum.fin_sum_tsum
            (fun i d => (a i : K) * S F (dep i) (hdep i) (c i) d) hsum
    _ = 0 := by
          have hz : (fun d : ℕ => ∑ i : ι, (a i : K) * S F (dep i) (hdep i) (c i) d) = fun _ : ℕ => 0 := by
            funext d
            exact h d
          rw [hz]
          simp

-- MIXED relation ζ-bridge: ∀ d, Σ_i aA_i·S_d(u_i) + Σ_j aB_j·S_{d+1}(v_j) = 0, with
-- S_0(v_j) = 0,  ⇒  Σ_i aA_i·ζ_A(u_i) + Σ_j aB_j·ζ_A(v_j) = 0.
theorem zeta_mixed_bridge {ιA : Type*} [Fintype ιA] {ιB : Type*} [Fintype ιB]
    (depA : ιA → ℕ) (hdepA : ∀ i, 0 < depA i) (cA : ∀ i, Fin (depA i) → ℕ+)
    (aA : ιA → RatFunc F)
    (depB : ιB → ℕ) (hdepB : ∀ j, 0 < depB j) (cB : ∀ j, Fin (depB j) → ℕ+)
    (aB : ιB → RatFunc F)
    (h0B : ∀ j, S F (depB j) (hdepB j) (cB j) 0 = 0)
    (h : ∀ d : ℕ,
      (∑ i : ιA, ((aA i : RatFunc.CompletionAtInfty F) *
        S F (depA i) (hdepA i) (cA i) d)) +
      (∑ j : ιB, ((aB j : RatFunc.CompletionAtInfty F) *
        S F (depB j) (hdepB j) (cB j) (d + 1))) = 0) :
    (∑ i : ιA, ((aA i : RatFunc.CompletionAtInfty F) * ζ_A F (cA i))) +
    (∑ j : ιB, ((aB j : RatFunc.CompletionAtInfty F) * ζ_A F (cB j))) = 0 := by
  classical
  let K := RatFunc.CompletionAtInfty F
  let gA : ℕ → K := fun d => ∑ i : ιA, (aA i : K) * S F (depA i) (hdepA i) (cA i) d
  let gB : ℕ → K := fun d => ∑ j : ιB, (aB j : K) * S F (depB j) (hdepB j) (cB j) d
  have hA0 : (∑ i : ιA, (aA i : K) * ζ_A F (cA i)) = ∑' d : ℕ, gA d := by
    calc
      (∑ i : ιA, (aA i : K) * ζ_A F (cA i))
          = ∑ i : ιA, ∑' d : ℕ, (aA i : K) * S F (depA i) (hdepA i) (cA i) d := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [zeta_eq_tsum_block F (hdepA i) (cA i)]
            rw [← tsum_mul_left]
      _ = ∑' d : ℕ, gA d := by
            exact Commons.Topology.InfiniteSum.fin_sum_tsum
              (fun i d => (aA i : K) * S F (depA i) (hdepA i) (cA i) d) (by
                intro i
                exact (summable_S F (hdepA i) (cA i)).mul_left (aA i : K))
  have hB0 : (∑ j : ιB, (aB j : K) * ζ_A F (cB j)) = ∑' d : ℕ, gB d := by
    calc
      (∑ j : ιB, (aB j : K) * ζ_A F (cB j))
          = ∑ j : ιB, ∑' d : ℕ, (aB j : K) * S F (depB j) (hdepB j) (cB j) d := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [zeta_eq_tsum_block F (hdepB j) (cB j)]
            rw [← tsum_mul_left]
      _ = ∑' d : ℕ, gB d := by
            exact Commons.Topology.InfiniteSum.fin_sum_tsum
              (fun j d => (aB j : K) * S F (depB j) (hdepB j) (cB j) d) (by
                intro j
                exact (summable_S F (hdepB j) (cB j)).mul_left (aB j : K))
  have hgB : Summable gB := by
    have hper : ∀ j : ιB, Summable (fun d : ℕ => (aB j : K) * S F (depB j) (hdepB j) (cB j) d) := by
      intro j
      exact (summable_S F (hdepB j) (cB j)).mul_left (aB j : K)
    exact Commons.Topology.InfiniteSum.summable_fin_sum
      (fun j d => (aB j : K) * S F (depB j) (hdepB j) (cB j) d) hper
  have hshift : (∑' d : ℕ, gB (d + 1)) = (∑' d : ℕ, gB d) - gB 0 := by
    exact Commons.Topology.InfiniteSum.tsum_shift_one hgB
  have hgA : Summable gA := by
    have hper : ∀ i : ιA, Summable (fun d : ℕ => (aA i : K) * S F (depA i) (hdepA i) (cA i) d) := by
      intro i
      exact (summable_S F (hdepA i) (cA i)).mul_left (aA i : K)
    exact Commons.Topology.InfiniteSum.summable_fin_sum
      (fun i d => (aA i : K) * S F (depA i) (hdepA i) (cA i) d) hper
  have hsum0 : (∑' d : ℕ, gA d) + (∑' d : ℕ, gB (d + 1)) = 0 := by
    have hconv : (fun d : ℕ => gA d + gB (d + 1)) = fun _ : ℕ => 0 := by
      funext d
      exact h d
    calc
      (∑' d : ℕ, gA d) + (∑' d : ℕ, gB (d + 1))
          = ∑' d : ℕ, (gA d + gB (d + 1)) := by
            exact (Summable.tsum_add hgA (Summable.comp_injective hgB (fun {a b} h => Nat.succ.inj h))).symm
      _ = 0 := by
            rw [hconv]
            simp
  have hgB0 : gB 0 = 0 := by
    dsimp [gB]
    apply Finset.sum_eq_zero
    intro j hj
    rw [h0B j]
    simp
  have hB : (∑' d : ℕ, gB d) = (∑' d : ℕ, gB (d + 1)) + gB 0 := by
    rw [hshift]
    abel
  calc
    (∑ i : ιA, (aA i : K) * ζ_A F (cA i)) + (∑ j : ιB, (aB j : K) * ζ_A F (cB j))
        = (∑' d : ℕ, gA d) + (∑' d : ℕ, gB d) := by rw [hA0, hB0]
    _ = (∑' d : ℕ, gA d) + ((∑' d : ℕ, gB (d + 1)) + gB 0) := by rw [hB]
    _ = ((∑' d : ℕ, gA d) + (∑' d : ℕ, gB (d + 1))) + gB 0 := by abel
    _ = 0 + gB 0 := by rw [hsum0]
    _ = 0 := by rw [hgB0]; simp


-- Cor 2.6-style prepend for FIXED relations (paper §2.2): a fixed relation that holds at
-- every level d stays fixed when a singleton exponent `x` is prepended to each tuple.
theorem fixed_rel_prepend {ι : Type*} [Fintype ι]
    (dep : ι → ℕ) (hdep : ∀ i, 0 < dep i) (c : ∀ i, Fin (dep i) → ℕ+)
    (a : ι → RatFunc F) (x : ℕ+)
    (h : ∀ d : ℕ, (∑ i, ((a i : RatFunc.CompletionAtInfty F) *
        S F (dep i) (hdep i) (c i) d)) = 0) :
    ∀ d : ℕ, (∑ i, ((a i : RatFunc.CompletionAtInfty F) *
        S F (dep i + 1) (by omega : 0 < dep i + 1) (consVec x (c i)) d)) = 0 := by
  intro d
  let K := RatFunc.CompletionAtInfty F
  have hrew (i : ι) :
      S F (dep i + 1) (by omega : 0 < dep i + 1) (consVec x (c i)) d =
        P F d x * S_lt F (dep i) (hdep i) (c i) d := by
    exact (S_prepend F d x (hdep i) (c i)).symm
  have h1 : (∑ i : ι, (a i : K) *
        S F (dep i + 1) (by omega : 0 < dep i + 1) (consVec x (c i)) d) =
      (∑ i : ι, (a i : K) * (P F d x * S_lt F (dep i) (hdep i) (c i) d)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hrew i]
  have h2 : (∑ i : ι, (a i : K) * (P F d x * S_lt F (dep i) (hdep i) (c i) d)) =
      (P F d x) * (∑ i : ι, (a i : K) * S_lt F (dep i) (hdep i) (c i) d) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have h3 : (P F d x) * (∑ i : ι, (a i : K) * S_lt F (dep i) (hdep i) (c i) d) =
      (P F d x) * (∑ i : ι, (a i : K) *
        (∑ j ∈ Finset.range d, S F (dep i) (hdep i) (c i) j)) := by
    apply congrArg (fun t : K => P F d x * t)
    apply Finset.sum_congr rfl
    intro i hi
    rw [S_lt_eq_sum_levels F (dep i) (hdep i) (c i) d]
  have h4 : (∑ i : ι, (a i : K) *
        (∑ j ∈ Finset.range d, S F (dep i) (hdep i) (c i) j)) =
      (∑ j ∈ Finset.range d, (∑ i : ι, (a i : K) * S F (dep i) (hdep i) (c i) j)) := by
    calc
      (∑ i : ι, (a i : K) * (∑ j ∈ Finset.range d, S F (dep i) (hdep i) (c i) j))
          = ∑ i : ι, (∑ j ∈ Finset.range d, (a i : K) * S F (dep i) (hdep i) (c i) j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
      _ = ∑ j ∈ Finset.range d, (∑ i : ι, (a i : K) * S F (dep i) (hdep i) (c i) j) := by
            rw [Finset.sum_comm]
  have h5 : (∑ j ∈ Finset.range d, (∑ i : ι, (a i : K) * S F (dep i) (hdep i) (c i) j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact h j
  calc
    (∑ i : ι, (a i : K) * S F (dep i + 1) (by omega : 0 < dep i + 1) (consVec x (c i)) d)
        = ∑ i : ι, (a i : K) * (P F d x * S_lt F (dep i) (hdep i) (c i) d) := h1
    _ = (P F d x) * (∑ i : ι, (a i : K) * S_lt F (dep i) (hdep i) (c i) d) := h2
    _ = (P F d x) * (∑ i : ι, (a i : K) *
          (∑ j ∈ Finset.range d, S F (dep i) (hdep i) (c i) j)) := h3
    _ = (P F d x) * (∑ j ∈ Finset.range d,
          (∑ i : ι, (a i : K) * S F (dep i) (hdep i) (c i) j)) := by
          rw [h4]
    _ = (P F d x) * 0 := by rw [h5]
    _ = 0 := by simp


/-- The image of `1 ∈ K` in the completion `K∞` is `1`. -/
@[simp] lemma completion_coe_one :
    ((1 : RatFunc F) : RatFunc.CompletionAtInfty F) = 1 := by
  exact map_one (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F))

end ZagierHoffmanPositiveChar
