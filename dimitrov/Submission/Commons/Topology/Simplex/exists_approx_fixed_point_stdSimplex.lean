import Mathlib
import Submission.Commons.Topology.Simplex.sperner_grid_nat
open Finset Filter
open scoped BigOperators Topology

namespace Commons.Topology.Simplex

/-- Grid points of the standard `d`-simplex of mesh `m`: the compositions of `m` into `d+1` parts. -/
private abbrev afpGrid (d m : ℕ) := {x : Fin (d+1) → Fin (m+1) // ∑ j, (x j : ℕ) = m}

/-- The point of the standard simplex associated with a grid point. -/
private noncomputable def afpToSmplx {d m : ℕ} (_hm : 0 < m) (v : afpGrid d m) : Fin (d+1) → ℝ :=
  fun i => (v.1 i : ℝ) / (m : ℝ)

private lemma afpToSmplx_mem {d m : ℕ} (hm : 0 < m) (v : afpGrid d m) :
    (∀ i, 0 ≤ afpToSmplx hm v i) ∧ ∑ i, afpToSmplx hm v i = 1 := by
  constructor
  · intro i; simp only [afpToSmplx]; positivity
  · simp only [afpToSmplx]
    rw [← Finset.sum_div, ← Nat.cast_sum, v.2]
    exact div_self (Nat.cast_ne_zero.mpr (ne_of_gt hm))

private lemma afpExistsLabel {d m : ℕ} (hm : 0 < m) (f : (Fin (d+1) → ℝ) → (Fin (d+1) → ℝ))
    (hmaps : ∀ x : Fin (d+1) → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i = 1) →
      (∀ i, 0 ≤ f x i) ∧ (∑ i, f x i) = 1)
    (v : afpGrid d m) :
    ∃ i, (v.1 i : ℕ) ≠ 0 ∧ f (afpToSmplx hm v) i ≤ afpToSmplx hm v i := by
  by_contra h
  push Not at h
  have hmem := afpToSmplx_mem hm v
  obtain ⟨hfnn, hfsum⟩ := hmaps (afpToSmplx hm v) hmem.1 hmem.2
  set S : Finset (Fin (d+1)) := univ.filter (fun i => (v.1 i : ℕ) ≠ 0) with hS
  have hzero : ∀ i ∉ S, afpToSmplx hm v i = 0 := by
    intro i hi
    simp only [hS, mem_filter, mem_univ, true_and, not_not] at hi
    simp only [afpToSmplx, hi, Nat.cast_zero, zero_div]
  have hSsum : ∑ i ∈ S, afpToSmplx hm v i = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hzero i hi)]
    exact hmem.2
  have hlt : ∀ i ∈ S, afpToSmplx hm v i < f (afpToSmplx hm v) i := by
    intro i hi
    simp only [hS, mem_filter, mem_univ, true_and] at hi
    exact h i hi
  have hSne : S.Nonempty := by
    rcases Finset.eq_empty_or_nonempty S with hE | hN
    · rw [hE] at hSsum; simp at hSsum
    · exact hN
  obtain ⟨i0, hi0⟩ := hSne
  have hsumlt : ∑ i ∈ S, afpToSmplx hm v i < ∑ i ∈ S, f (afpToSmplx hm v) i :=
    Finset.sum_lt_sum (fun i hi => le_of_lt (hlt i hi)) ⟨i0, hi0, hlt i0 hi0⟩
  have hle : ∑ i ∈ S, f (afpToSmplx hm v) i ≤ 1 := by
    rw [← hfsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ => hfnn i)
  linarith

/-- The label of a grid point: the least index in the support at which `f` does not increase. -/
private noncomputable def afpLab {d m : ℕ} (hm : 0 < m) (f : (Fin (d+1) → ℝ) → (Fin (d+1) → ℝ))
    (hmaps : ∀ x : Fin (d+1) → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i = 1) →
      (∀ i, 0 ≤ f x i) ∧ (∑ i, f x i) = 1)
    (v : afpGrid d m) : Fin (d+1) :=
  (univ.filter (fun i => (v.1 i : ℕ) ≠ 0 ∧ f (afpToSmplx hm v) i ≤ afpToSmplx hm v i)).min'
    (by
      obtain ⟨i, hi⟩ := afpExistsLabel hm f hmaps v
      exact ⟨i, by simp only [mem_filter, mem_univ, true_and]; exact hi⟩)

private lemma afpLab_spec {d m : ℕ} (hm : 0 < m) (f : (Fin (d+1) → ℝ) → (Fin (d+1) → ℝ))
    (hmaps : ∀ x : Fin (d+1) → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i = 1) →
      (∀ i, 0 ≤ f x i) ∧ (∑ i, f x i) = 1)
    (v : afpGrid d m) :
    (v.1 (afpLab hm f hmaps v) : ℕ) ≠ 0 ∧
      f (afpToSmplx hm v) (afpLab hm f hmaps v) ≤ afpToSmplx hm v (afpLab hm f hmaps v) := by
  have h := Finset.min'_mem
    (univ.filter (fun i => (v.1 i : ℕ) ≠ 0 ∧ f (afpToSmplx hm v) i ≤ afpToSmplx hm v i))
    (by
      obtain ⟨i, hi⟩ := afpExistsLabel hm f hmaps v
      exact ⟨i, by simp only [mem_filter, mem_univ, true_and]; exact hi⟩)
  simpa only [afpLab, mem_filter, mem_univ, true_and] using h

private lemma afpInvNatAddTendstoZero (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    Tendsto (fun t : ℕ => (((φ t : ℝ) + 1)⁻¹)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℕ => ((φ t : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
  have h2 : Tendsto (fun t : ℕ => (φ t : ℝ) + 1) atTop atTop :=
    h1.atTop_add tendsto_const_nhds
  exact tendsto_inv_atTop_zero.comp h2

/-- The approximate fixed point theorem for the standard simplex, deduced from a
Sperner-type combinatorial lemma (with `ℕ`-coerced coordinates). -/
private theorem afp_of_sperner (n : ℕ) (hn : 0 < n) (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf : Continuous f)
    (hmaps : ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i = 1) →
      (∀ i, 0 ≤ f x i) ∧ (∑ i, f x i) = 1)
    (ε : ℝ) (hε : 0 < ε)
    (hS : ∀ (d m : ℕ), 0 < m → (ℓ : afpGrid d m → Fin (d+1)) →
      (∀ v : afpGrid d m, ((v.1 (ℓ v) : ℕ) ≠ 0)) →
      ∃ v : Fin (d+1) → afpGrid d m, Function.Injective (fun t => ℓ (v t)) ∧
        ∀ s t j, ((v s).1 j : ℕ) ≤ ((v t).1 j : ℕ) + 1) :
    ∃ x : Fin n → ℝ, (∀ i, 0 ≤ x i) ∧ (∑ i, x i = 1) ∧ ∀ i, f x i ≤ x i + ε := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
  have sper : ∀ t : ℕ, ∃ v : Fin (k+1) → afpGrid k (t+1),
      Function.Injective (fun s => afpLab (Nat.succ_pos t) f hmaps (v s)) ∧
      ∀ s t' j, ((v s).1 j : ℕ) ≤ ((v t').1 j : ℕ) + 1 := by
    intro t
    exact hS k (t+1) (Nat.succ_pos t) (afpLab (Nat.succ_pos t) f hmaps)
      (fun v => (afpLab_spec (Nat.succ_pos t) f hmaps v).1)
  choose vs hvs using sper
  have hinj : ∀ t, Function.Injective (fun s => afpLab (Nat.succ_pos t) f hmaps (vs t s)) :=
    fun t => (hvs t).1
  have hcl : ∀ t s t' j, ((vs t s).1 j : ℕ) ≤ ((vs t t').1 j : ℕ) + 1 := fun t => (hvs t).2
  have hJ : ∀ t (i : Fin (k+1)), ∃ s, afpLab (Nat.succ_pos t) f hmaps (vs t s) = i :=
    fun t i => Finite.injective_iff_surjective.mp (hinj t) i
  choose jOf hjOf using hJ
  let q : ℕ → Fin (k+1) → ℝ := fun t => afpToSmplx (Nat.succ_pos t) (vs t (jOf t 0))
  obtain ⟨x, _hxIcc, φ, hφmono, hφtend⟩ := IsCompact.tendsto_subseq
    (isCompact_Icc (a := (0 : Fin (k+1) → ℝ)) (b := (1 : Fin (k+1) → ℝ)))
    (fun t => stdSimplex_subset_Icc ℝ (afpToSmplx_mem (Nat.succ_pos t) (vs t (jOf t 0))))
  have hxS : x ∈ stdSimplex ℝ (Fin (k+1)) :=
    (isClosed_stdSimplex ℝ (Fin (k+1))).mem_of_tendsto hφtend
      (Eventually.of_forall fun t =>
        afpToSmplx_mem (Nat.succ_pos (φ t)) (vs (φ t) (jOf (φ t) 0)))
  have hmain : ∀ i : Fin (k+1), f x i ≤ x i := by
    intro i
    have hineq : ∀ t, f (afpToSmplx (Nat.succ_pos (φ t)) (vs (φ t) (jOf (φ t) i))) i ≤
        afpToSmplx (Nat.succ_pos (φ t)) (vs (φ t) (jOf (φ t) i)) i := by
      intro t
      have h := (afpLab_spec (Nat.succ_pos (φ t)) f hmaps (vs (φ t) (jOf (φ t) i))).2
      rwa [hjOf (φ t) i] at h
    have hd1 : Tendsto (fun t => dist (afpToSmplx (Nat.succ_pos (φ t))
        (vs (φ t) (jOf (φ t) i))) (q (φ t))) atTop (𝓝 0) := by
      apply squeeze_zero (fun t => dist_nonneg)
      · intro t
        rw [dist_pi_le_iff (by positivity : (0:ℝ) ≤ (((φ t : ℝ) + 1)⁻¹))]
        intro j
        have hbd : |((vs (φ t) (jOf (φ t) i)).1 j : ℝ) - ((vs (φ t) (jOf (φ t) 0)).1 j : ℝ)| ≤ 1 := by
          have h1 : ((vs (φ t) (jOf (φ t) i)).1 j : ℝ) ≤ ((vs (φ t) (jOf (φ t) 0)).1 j : ℝ) + 1 := by
            exact_mod_cast hcl (φ t) (jOf (φ t) i) (jOf (φ t) 0) j
          have h2 : ((vs (φ t) (jOf (φ t) 0)).1 j : ℝ) ≤ ((vs (φ t) (jOf (φ t) i)).1 j : ℝ) + 1 := by
            exact_mod_cast hcl (φ t) (jOf (φ t) 0) (jOf (φ t) i) j
          rw [abs_sub_le_iff]
          exact ⟨by linarith, by linarith⟩
        rw [Real.dist_eq]
        have hrw : afpToSmplx (Nat.succ_pos (φ t)) (vs (φ t) (jOf (φ t) i)) j - q (φ t) j
            = (((vs (φ t) (jOf (φ t) i)).1 j : ℝ) - ((vs (φ t) (jOf (φ t) 0)).1 j : ℝ))
                / ((φ t : ℝ) + 1) := by
          simp only [afpToSmplx, q]
          push_cast
          ring
        rw [hrw, abs_div, abs_of_pos (by positivity : (0:ℝ) < (φ t : ℝ) + 1)]
        rw [div_eq_mul_inv]
        simpa using mul_le_mul_of_nonneg_right hbd
          (by positivity : (0:ℝ) ≤ (((φ t : ℝ) + 1)⁻¹))
      · exact afpInvNatAddTendstoZero φ hφmono
    have hconv0 : Tendsto (fun t => q (φ t)) atTop (𝓝 x) := hφtend
    have hconv : Tendsto (fun t => afpToSmplx (Nat.succ_pos (φ t)) (vs (φ t) (jOf (φ t) i)))
        atTop (𝓝 x) := by
      rw [tendsto_iff_dist_tendsto_zero] at hconv0 ⊢
      refine squeeze_zero (fun t => dist_nonneg) (fun t => ?_) (by simpa using hd1.add hconv0)
      exact dist_triangle _ _ _
    have hconv_i : Tendsto (fun t => afpToSmplx (Nat.succ_pos (φ t)) (vs (φ t) (jOf (φ t) i)) i)
        atTop (𝓝 (x i)) := ((continuous_apply i).tendsto x).comp hconv
    exact le_of_tendsto_of_tendsto
      (((continuous_apply i).comp hf).tendsto x |>.comp hconv) hconv_i
      (Eventually.of_forall hineq)
  refine ⟨x, hxS.1, hxS.2, fun i => ?_⟩
  calc f x i ≤ x i := hmain i
    _ ≤ x i + ε := le_add_of_nonneg_right hε.le

end Commons.Topology.Simplex

namespace Commons.Topology.Simplex

/-- **Approximate fixed point theorem for the standard simplex.** A continuous self-map of the
standard `(n-1)`-simplex `Δ = {x : Fin n → ℝ | x ≥ 0, ∑ x = 1}` has, for every `ε > 0`, a point
`x ∈ Δ` with `f x i ≤ x i + ε` for all `i`.

This is obtained by a Sperner-type argument: for each mesh `m` one labels the grid points of `Δ`
of mesh `m` by an index `i` in the support at which `f` does not increase, applies Sperner's
lemma to produce `n` nearby grid points carrying pairwise distinct labels, and passes to the
limit along a convergent subsequence (`Commons.Topology.Simplex.sperner_grid_nat`). -/
theorem exists_approx_fixed_point_stdSimplex (n : ℕ) (hn : 0 < n)
    (f : (Fin n → ℝ) → (Fin n → ℝ)) (hf : Continuous f)
    (hmaps : ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i = 1) →
      (∀ i, 0 ≤ f x i) ∧ (∑ i, f x i) = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ x : Fin n → ℝ, (∀ i, 0 ≤ x i) ∧ (∑ i, x i = 1) ∧ ∀ i, f x i ≤ x i + ε :=
  afp_of_sperner n hn f hf hmaps ε hε
    (fun d m hm ℓ hℓ => Commons.Topology.Simplex.sperner_grid_nat d m hm ℓ hℓ)

end Commons.Topology.Simplex
