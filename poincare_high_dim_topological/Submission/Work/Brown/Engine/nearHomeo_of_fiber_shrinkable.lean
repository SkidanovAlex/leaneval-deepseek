import Mathlib
import Submission.Work.Brown.Basic

/-!
# Bing's shrinking criterion (the "if" direction)

A surjective map `f : X → Y` of compact metric spaces is *shrinkable* if for every `ε > 0`
there is a homeomorphism `h` of `X` which moves points by less than `ε` in the metric of the
range (`dist (f (h x)) (f x) < ε`) and which shrinks every point inverse `f ⁻¹' {y}` to a set of
diameter `< ε` (`dist (h x) (h y) < ε` whenever `f x = f y`).  Bing's shrinking criterion says
that such a map is a uniform limit of homeomorphisms, i.e. a *near homeomorphism*.

This file proves the criterion in the self-map case `X = Y = S` needed for the engulfing proof
of the generalized Poincaré conjecture: `nearHomeo_of_fiber_shrinkable`.

The proof follows M. Ferry, *Geometric topology notes*, §2 ("Bing Shrinking").  One constructs
a sequence of homeomorphisms `h_n : S ≃ₜ S` with
`diam (h_n (f ⁻¹' {y})) < 2 ^ (-n)` and `dist (h_n x) (h_{n+1} x) < 2 ^ (-n)`, and also
`dist (f (h_n⁻¹ x)) (f (h_{n+1}⁻¹ x)) < 2 ^ (-n)`.  The last two bounds make `h_n` and
`p_n := f ∘ h_n⁻¹` uniformly convergent, with limits `q` and `q'`; the first shows that `q`
has the same point inverses as `f` (`q x = q y ↔ f x = f y`).  Hence `f' := f ∘ q⁻¹` is a
homeomorphism, and the homeomorphisms `f' ∘ h_n` converge uniformly to `f' ∘ q = f`, which is
the required approximation.

The mechanism forcing `dist (h_n x) (h_{n+1} x)` to be small is Ferry's Exercise 2.10: a map
whose fibres are small can only be moved by maps which are small on the nose
(`exists_delta_of_fiber_small`).  It is applied to `p_{n-1} = f ∘ h_{n-1}⁻¹`, whose fibres are
`h_{n-1} (f ⁻¹' {y})` and hence have diameter `< 2 ^ (-(n-1))`.

## Main result

* `Work.Brown.Engine.nearHomeo_of_fiber_shrinkable`
-/

open Set Metric Function Filter
open scoped Topology

namespace Work.Brown.Engine

section Helpers

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- Ferry's Exercise 2.10: if the point inverses of a (continuous) self-map `p` of a compact
metric space are all of diameter `< ε`, then any map `g` which is close to `p` in the sense
`dist (p (g x)) (p x) < δ` must move points by less than `ε` (for a suitable `δ > 0`).

We state and use the equivalent form: there is `δ > 0` with `dist (p x) (p y) < δ ⟹
dist x y < ε`. -/
lemma exists_delta_of_fiber_small {p : S → S} (hp : Continuous p) {ε : ℝ}
    (hfib : ∀ x y, p x = p y → dist x y < ε) :
    ∃ δ > 0, ∀ x y, dist (p x) (p y) < δ → dist x y < ε := by
  by_cases hem : ∃ z : S × S, ε ≤ dist z.1 z.2
  · obtain ⟨z₀, hz₀⟩ := hem
    set K : Set (S × S) := {z | ε ≤ dist z.1 z.2}
    have hKne : K.Nonempty := ⟨z₀, hz₀⟩
    have hKcl : IsClosed K := by
      have h1 : K = (fun z : S × S => dist z.1 z.2) ⁻¹' (Set.Ici ε) := rfl
      rw [h1]
      exact IsClosed.preimage
        (continuous_dist.comp (continuous_fst.prodMk continuous_snd)) isClosed_Ici
    have hKcomp : IsCompact K :=
      IsCompact.of_isClosed_subset isCompact_univ hKcl (subset_univ K)
    have hcont : ContinuousOn (fun z : S × S => dist (p z.1) (p z.2)) K :=
      (continuous_dist.comp ((hp.comp continuous_fst).prodMk (hp.comp continuous_snd))).continuousOn
    obtain ⟨z₁, hz₁K, hz₁min⟩ := hKcomp.exists_isMinOn hKne hcont
    have hz₁ : ε ≤ dist z₁.1 z₁.2 := hz₁K
    have hpos : 0 < dist (p z₁.1) (p z₁.2) := by
      rcases lt_or_eq_of_le (dist_nonneg : (0:ℝ) ≤ dist (p z₁.1) (p z₁.2)) with h | h
      · exact h
      · exfalso
        have hpeq : p z₁.1 = p z₁.2 := dist_eq_zero.mp h.symm
        have hlt := hfib z₁.1 z₁.2 hpeq
        linarith
    refine ⟨dist (p z₁.1) (p z₁.2), hpos, ?_⟩
    intro x y hxy
    by_contra hcon
    rw [not_lt] at hcon
    have hmem : (x, y) ∈ K := hcon
    have hle : dist (p z₁.1) (p z₁.2) ≤ dist (p x) (p y) := hz₁min hmem
    linarith
  · rw [not_exists] at hem
    refine ⟨1, one_pos, fun x y _ => ?_⟩
    exact lt_of_not_ge fun h => hem (x, y) h

/-- The state of the iterative shrinking construction: a homeomorphism `h` together with a
positive bound `c` on the diameter of the images of the point inverses of `f`. -/
structure ShrinkStep (f : S → S) where
  c : ℝ
  hc : 0 < c
  h : S ≃ₜ S
  hfib : ∀ x y, f x = f y → dist (h x) (h y) < c

/-- One step of the construction.  Given a homeomorphism shrinking the fibres of `f` by `c`, we
produce a homeomorphism which shrinks them by `c / 2`, moves points by less than `c`, and changes
`f ∘ h⁻¹` by less than `c`. -/
lemma exists_next_shrinkStep {f : S → S} (hf : Continuous f)
    (hshrink : ∀ ε > 0, ∃ h : S ≃ₜ S,
      (∀ x, dist (f (h x)) (f x) < ε) ∧ (∀ x y, f x = f y → dist (h x) (h y) < ε))
    (s : ShrinkStep f) :
    ∃ s' : ShrinkStep f, s'.c = s.c / 2 ∧
      (∀ x, dist (s.h x) (s'.h x) < s.c) ∧
      (∀ x, dist (f (s.h.symm x)) (f (s'.h.symm x)) < s.c) := by
  -- Ferry's Exercise 2.10 applied to `p = f ∘ h⁻¹`.
  obtain ⟨δ, hδpos, hδ⟩ := exists_delta_of_fiber_small (p := f ∘ s.h.symm)
    (hf.comp s.h.symm.continuous)
    (fun x y hxy => by
      have h2 := s.hfib (s.h.symm x) (s.h.symm y) hxy
      simpa using h2)
  -- a uniform-continuity modulus for `h` (to control diameters of images)
  obtain ⟨η₁, hη₁pos, hη₁⟩ :
      ∃ η₁ > 0, ∀ a b, dist a b < η₁ → dist (s.h a) (s.h b) < s.c / 2 := by
    have hu := CompactSpace.uniformContinuous_of_continuous s.h.continuous
    rcases (Metric.uniformContinuous_iff.mp hu) (s.c / 2) (by linarith [s.hc]) with
      ⟨η₁, hη₁pos, hη₁⟩
    exact ⟨η₁, hη₁pos, hη₁⟩
  have hminpos : 0 < min (min δ η₁) s.c := lt_min (lt_min hδpos hη₁pos) s.hc
  -- a shrinking homeomorphism for `f` with a small parameter
  obtain ⟨j, hj1, hj2⟩ :=
    hshrink (min (min δ η₁) s.c / 2) (div_pos hminpos (by norm_num))
  have hηδ : min (min δ η₁) s.c / 2 < δ := by
    nlinarith [min_le_left (min δ η₁) s.c, min_le_left δ η₁]
  have hηη₁ : min (min δ η₁) s.c / 2 < η₁ := by
    nlinarith [min_le_left (min δ η₁) s.c, min_le_right δ η₁]
  have hηc : min (min δ η₁) s.c / 2 < s.c := by
    nlinarith [min_le_right (min δ η₁) s.c]
  refine ⟨⟨s.c / 2, by linarith [s.hc], j.trans s.h, ?_⟩, rfl, ?_, ?_⟩
  · -- the fibres are shrunk by `c / 2`
    intro x y hxy
    have h1 : dist (j x) (j y) < min (min δ η₁) s.c / 2 := hj2 x y hxy
    have h2 : dist (j x) (j y) < η₁ := lt_trans h1 hηη₁
    have h3 := hη₁ (j x) (j y) h2
    simpa [Homeomorph.trans_apply] using h3
  · -- the new homeomorphism is `c`-close to the old one
    intro x
    have hfac : ∀ z, dist ((f ∘ s.h.symm) (s.h (j (s.h.symm z))))
        ((f ∘ s.h.symm) z) < δ := by
      intro z
      have h1 := hj1 (s.h.symm z)
      have h2 : s.h.symm (s.h (j (s.h.symm z))) = j (s.h.symm z) := by simp
      simp only [Function.comp_apply, h2]
      exact lt_trans h1 hηδ
    have hg : ∀ z, dist (s.h (j (s.h.symm z))) z < s.c := fun z => hδ _ _ (hfac z)
    have := hg (s.h x)
    have h2 : s.h.symm (s.h x) = x := by simp
    simpa [h2, Homeomorph.trans_apply, dist_comm] using this
  · -- `f ∘ h⁻¹` changes by at most `c`
    intro x
    have h3 : (j.trans s.h).symm x = j.symm (s.h.symm x) := by
      apply (j.trans s.h).injective
      rw [Homeomorph.apply_symm_apply]
      simp [Homeomorph.trans_apply]
    rw [h3]
    have h1 := hj1 (j.symm (s.h.symm x))
    have h2 : j (j.symm (s.h.symm x)) = s.h.symm x := by simp
    rw [h2] at h1
    exact lt_trans h1 hηc

/-- A uniformly Cauchy sequence of functions `u n : S → S` whose successive distances are
bounded by `2 ^ (-n)` has a continuous uniform limit `q` with `dist (u n x) (q x) ≤ 2 ^ (-n)`
and `u n x → q x` for every `x`. -/
lemma exists_uniform_limit {u : ℕ → S → S} (hcont : ∀ n, Continuous (u n))
    (hmot : ∀ n x, dist (u n x) (u (n+1) x) < (1/2 : ℝ) ^ n) :
    ∃ q : S → S, Continuous q ∧ (∀ n x, dist (u n x) (q x) ≤ 2 * (1/2 : ℝ) ^ n) ∧
      (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (q x))) := by
  haveI : CompleteSpace S := completeSpace_iff_isComplete_univ.mpr isCompact_univ.isComplete
  have hbound : ∀ n k x, dist (u n x) (u (n + k) x) ≤ 2 * (1/2:ℝ)^n - 2 * (1/2:ℝ)^(n+k) := by
    intro n k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      have h1 := ih x
      have h2 : dist (u (n+k) x) (u (n+k+1) x) < (1/2:ℝ)^(n+k) := hmot (n+k) x
      have hpow : 2 * (1/2:ℝ)^(n+(k+1)) = (1/2:ℝ)^(n+k) := by
        rw [show n + (k+1) = (n+k)+1 from by omega, pow_succ]; ring
      calc dist (u n x) (u (n + (k+1)) x)
          ≤ dist (u n x) (u (n+k) x) + dist (u (n+k) x) (u (n+k+1) x) := by
            rw [show n + (k+1) = n + k + 1 from by omega]
            exact dist_triangle _ _ _
        _ ≤ (2 * (1/2:ℝ)^n - 2 * (1/2:ℝ)^(n+k)) + (1/2:ℝ)^(n+k) :=
            add_le_add h1 (le_of_lt h2)
        _ = 2 * (1/2:ℝ)^n - 2 * (1/2:ℝ)^(n+(k+1)) := by rw [hpow]; ring
  have hcau : ∀ x, CauchySeq (fun n => u n x) := by
    intro x
    rw [cauchySeq_iff_le_tendsto_0]
    refine ⟨fun N => 2*(1/2:ℝ)^N, fun N => by positivity, ?_, ?_⟩
    · intro n m N hn hm
      have hle : (1/2:ℝ)^n ≤ (1/2:ℝ)^N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
      have hle' : (1/2:ℝ)^m ≤ (1/2:ℝ)^N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      rcases le_total n m with hnm | hmn
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
        calc dist (u n x) (u (n+k) x) ≤ 2*(1/2:ℝ)^n - 2*(1/2:ℝ)^(n+k) := hbound n k x
          _ ≤ 2*(1/2:ℝ)^n := by
              have hh : 0 ≤ 2*(1/2:ℝ)^(n+k) := by positivity
              linarith
          _ ≤ 2*(1/2:ℝ)^N := by linarith [hle]
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
        calc dist (u (m+k) x) (u m x) = dist (u m x) (u (m+k) x) := dist_comm _ _
          _ ≤ 2*(1/2:ℝ)^m - 2*(1/2:ℝ)^(m+k) := hbound m k x
          _ ≤ 2*(1/2:ℝ)^m := by
              have hh : 0 ≤ 2*(1/2:ℝ)^(m+k) := by positivity
              linarith
          _ ≤ 2*(1/2:ℝ)^N := by linarith [hle']
    · have h0 : Tendsto (fun N : ℕ => (1/2:ℝ)^N) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      simpa using h0.const_mul (2:ℝ)
  let q : S → S := fun x => Classical.choose (cauchySeq_tendsto_of_complete (hcau x))
  have hq : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (q x)) :=
    fun x => Classical.choose_spec (cauchySeq_tendsto_of_complete (hcau x))
  have hbdd : ∀ n x, dist (u n x) (q x) ≤ 2*(1/2:ℝ)^n := by
    intro n x
    have ht : Tendsto (fun m => dist (u m x) (u n x)) atTop (𝓝 (dist (q x) (u n x))) :=
      (hq x).dist tendsto_const_nhds
    have hle : dist (q x) (u n x) ≤ 2*(1/2:ℝ)^n := by
      refine le_of_tendsto ht ?_
      filter_upwards [Filter.eventually_ge_atTop n] with m hm
      rw [← Nat.add_sub_of_le hm, dist_comm]
      calc dist (u n x) (u (n + (m-n)) x) ≤ 2*(1/2:ℝ)^n - 2*(1/2:ℝ)^(n+(m-n)) := hbound n (m-n) x
        _ ≤ 2*(1/2:ℝ)^n := by
            have hh : 0 ≤ 2*(1/2:ℝ)^(n+(m-n)) := by positivity
            linarith
    rwa [dist_comm] at hle
  have hcontq : Continuous q := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < ε/8 by linarith)
      (show (1/2:ℝ) < 1 by norm_num)
    have hNδ : 2*(1/2:ℝ)^N < ε/4 := by linarith
    have hcontN : ContinuousAt (u N) x := (hcont N).continuousAt
    rw [Metric.continuousAt_iff] at hcontN
    obtain ⟨δ, hδpos, hδ⟩ := hcontN (ε/2) (by linarith)
    refine ⟨δ, hδpos, fun y hy => ?_⟩
    calc dist (q y) (q x)
        ≤ dist (q y) (u N y) + dist (u N y) (q x) := dist_triangle _ _ _
      _ ≤ 2*(1/2:ℝ)^N + (ε/2 + 2*(1/2:ℝ)^N) := by
            gcongr
            · rw [dist_comm]; exact hbdd N y
            · calc dist (u N y) (q x) ≤ dist (u N y) (u N x) + dist (u N x) (q x) := dist_triangle _ _ _
                _ ≤ ε/2 + 2*(1/2:ℝ)^N := add_le_add (le_of_lt (hδ hy)) (hbdd N x)
      _ < ε := by linarith
  exact ⟨q, hcontq, hbdd, hq⟩

/-- A uniform limit `u n → q` (with the explicit bound `2 ^ (-n)`) composed with a convergent
sequence converges to the composition of the limits. -/
lemma tendsto_comp_of_uniform {u : ℕ → S → S} {v : S → S} (hv : Continuous v)
    (huv : ∀ n x, dist (u n x) (v x) ≤ 2*(1/2:ℝ)^n) {x : ℕ → S} {a : S}
    (hx : Tendsto x atTop (𝓝 a)) :
    Tendsto (fun n => u n (x n)) atTop (𝓝 (v a)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by linarith : (0:ℝ) < δ/4)
    (by norm_num : (1/2:ℝ) < 1)
  have hcont : ContinuousAt v a := hv.continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨η, hηpos, hη⟩ := hcont (δ/2) (by linarith)
  rw [Metric.tendsto_atTop] at hx
  obtain ⟨M, hM⟩ := hx η hηpos
  refine ⟨max N M, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnM : M ≤ n := le_trans (le_max_right _ _) hn
  have hpow : 2*(1/2:ℝ)^n ≤ 2*(1/2:ℝ)^N := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hnN
  calc dist (u n (x n)) (v a) ≤ dist (u n (x n)) (v (x n)) + dist (v (x n)) (v a) :=
        dist_triangle _ _ _
    _ ≤ 2*(1/2:ℝ)^n + δ/2 := add_le_add (huv n (x n)) (le_of_lt (hη (hM n hnM)))
    _ < δ := by linarith [hpow, hN]

end Helpers

/-- **Bing's shrinking criterion** (the "if" direction), in the self-map form needed for the
engulfing proof of the generalized Poincaré conjecture: a surjective map `f : S → S` of a
compact metric space which is shrinkable is a uniform limit of homeomorphisms. -/
theorem nearHomeo_of_fiber_shrinkable {S : Type*} [MetricSpace S] [CompactSpace S]
    (f : S → S) (hf : Continuous f) (hsurj : Function.Surjective f)
    (hshrink : ∀ ε > 0, ∃ h : S ≃ₜ S,
      (∀ x, dist (f (h x)) (f x) < ε) ∧ (∀ x y, f x = f y → dist (h x) (h y) < ε)) :
    Work.Brown.IsNearHomeo f := by
  intro ε hε
  -- the initial state
  obtain ⟨h0, -, h0fib⟩ := hshrink 1 one_pos
  let s0 : ShrinkStep f := ⟨1, one_pos, h0, h0fib⟩
  -- the iteration
  let nxt : ShrinkStep f → ShrinkStep f := fun s => (exists_next_shrinkStep hf hshrink s).choose
  have nxt_c : ∀ s, (nxt s).c = s.c / 2 :=
    fun s => (exists_next_shrinkStep hf hshrink s).choose_spec.1
  have nxt_h : ∀ s x, dist (s.h x) ((nxt s).h x) < s.c :=
    fun s => (exists_next_shrinkStep hf hshrink s).choose_spec.2.1
  have nxt_p : ∀ s x, dist (f (s.h.symm x)) (f ((nxt s).h.symm x)) < s.c :=
    fun s => (exists_next_shrinkStep hf hshrink s).choose_spec.2.2
  let st : ℕ → ShrinkStep f := fun n => nxt^[n] s0
  have st_succ : ∀ n, st (n+1) = nxt (st n) := fun n => Function.iterate_succ_apply' nxt n s0
  let H : ℕ → S ≃ₜ S := fun n => (st n).h
  have c_eq : ∀ n, (st n).c = (1/2:ℝ)^n := by
    intro n
    induction n with
    | zero => simp [st, s0]
    | succ n ih => rw [st_succ, nxt_c, ih, pow_succ]; ring
  have Hmotion : ∀ n x, dist (H n x) (H (n+1) x) < (1/2:ℝ)^n := by
    intro n x
    have hs : H (n+1) = (nxt (st n)).h := by
      show (st (n+1)).h = (nxt (st n)).h; rw [st_succ]
    rw [hs]
    have h1 := nxt_h (st n) x
    rwa [c_eq n] at h1
  have Pmotion : ∀ n x, dist (f ((H n).symm x)) (f ((H (n+1)).symm x)) < (1/2:ℝ)^n := by
    intro n x
    have hs : H (n+1) = (nxt (st n)).h := by
      show (st (n+1)).h = (nxt (st n)).h; rw [st_succ]
    rw [hs]
    have h1 := nxt_p (st n) x
    rwa [c_eq n] at h1
  -- the two uniform limits
  obtain ⟨q, hqcont, hqbd, hqtend⟩ :=
    exists_uniform_limit (u := fun n => (H n : S → S)) (fun n => (H n).continuous) Hmotion
  let P : ℕ → S → S := fun n => fun x => f ((H n).symm x)
  obtain ⟨q', hq'cont, hq'bd, -⟩ :=
    exists_uniform_limit (u := P) (fun n => hf.comp (H n).symm.continuous) Pmotion
  -- `q` has the same point inverses as `f`
  have hFiber : ∀ x y, f x = f y → q x = q y := by
    intro x y hxy
    refine eq_of_forall_dist_le ?_
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by linarith : (0:ℝ) < δ/5)
      (by norm_num : (1/2:ℝ) < 1)
    have h1 : dist (q x) (H N x) ≤ 2*(1/2:ℝ)^N := by rw [dist_comm]; exact hqbd N x
    have h2 : dist (H N x) (H N y) < (1/2:ℝ)^N := by
      have := (st N).hfib x y hxy; rwa [c_eq N] at this
    have h3 : dist (H N y) (q y) ≤ 2*(1/2:ℝ)^N := hqbd N y
    have ht1 : dist (q x) (q y) ≤ dist (q x) (H N x) + dist (H N x) (q y) := dist_triangle _ _ _
    have ht2 : dist (H N x) (q y) ≤ dist (H N x) (H N y) + dist (H N y) (q y) :=
      dist_triangle _ _ _
    linarith [ht1, ht2, h1, h2, h3, hN]
  have hkey : ∀ x, q' (q x) = f x := by
    intro x
    have ht1 := tendsto_comp_of_uniform hq'cont hq'bd (hqtend x)
    have hconst : (fun n => P n (H n x)) = fun _ => f x := by
      funext n
      show f ((H n).symm (H n x)) = f x
      rw [Homeomorph.symm_apply_apply]
    rw [hconst] at ht1
    exact tendsto_nhds_unique ht1 tendsto_const_nhds
  have hqinj : ∀ x y, q x = q y → f x = f y := by
    intro x y h
    rw [← hkey x, ← hkey y, h]
  -- `q` is onto
  have hqsurj : Surjective q := by
    intro w
    choose x hx using fun n => (H n).surjective w
    obtain ⟨a, φ, hφ, htend⟩ := CompactSpace.tendsto_subseq x
    have h1 : Tendsto (fun n => H (φ n) (x (φ n))) atTop (𝓝 (q a)) := by
      apply tendsto_comp_of_uniform hqcont (v := q) ?_ htend
      intro n y
      have hb := hqbd (φ n) y
      have hle : (1/2:ℝ)^(φ n) ≤ (1/2:ℝ)^n :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (hφ.id_le n)
      linarith
    have h2 : (fun n => H (φ n) (x (φ n))) = fun _ => w := by
      funext n; exact hx (φ n)
    rw [h2] at h1
    exact ⟨a, tendsto_nhds_unique h1 tendsto_const_nhds⟩
  -- the induced map `f' = f ∘ q⁻¹`
  let f' : S → S := fun w => f (Classical.choose (hqsurj w))
  have hf'q : ∀ y, f' (q y) = f y := by
    intro y
    show f (Classical.choose (hqsurj (q y))) = f y
    exact hqinj _ _ (Classical.choose_spec (hqsurj (q y)))
  have hqquot : Topology.IsQuotientMap q :=
    hqcont.isClosedMap.isQuotientMap hqcont hqsurj
  have hf'cont : Continuous f' := by
    refine (hqquot.continuous_iff).mpr ?_
    have hcomp : f' ∘ q = f := funext hf'q
    rw [hcomp]; exact hf
  have hf'inj : Injective f' := by
    intro w1 w2 hw
    obtain ⟨y1, rfl⟩ := hqsurj w1
    obtain ⟨y2, rfl⟩ := hqsurj w2
    rw [hf'q y1, hf'q y2] at hw
    exact hFiber y1 y2 hw
  have hf'surj : Surjective f' := by
    intro t
    obtain ⟨y, rfl⟩ := hsurj t
    exact ⟨q y, hf'q y⟩
  have hbij : Function.Bijective f' := ⟨hf'inj, hf'surj⟩
  let e : S ≃ S := Equiv.ofBijective f' hbij
  have hecont : Continuous (e : S → S) := by
    have hcoe : (e : S → S) = f' := funext fun w => Equiv.ofBijective_apply f' hbij w
    rw [hcoe]; exact hf'cont
  let F : S ≃ₜ S := Continuous.homeoOfEquivCompactToT2 (f := e) hecont
  have hFf' : ∀ w, F w = f' w := fun w => Equiv.ofBijective_apply f' hbij w
  -- the approximating homeomorphisms `F ∘ H N` converge to `F ∘ q = f`
  obtain ⟨δF, hδFpos, hδF⟩ : ∃ δF > 0, ∀ a b, dist a b < δF → dist (F a) (F b) < ε := by
    have hu := CompactSpace.uniformContinuous_of_continuous F.continuous
    exact (Metric.uniformContinuous_iff.mp hu) ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by linarith : (0:ℝ) < δF/2)
    (by norm_num : (1/2:ℝ) < 1)
  refine ⟨(H N).trans F, fun x => ?_⟩
  rw [Homeomorph.trans_apply]
  have hb := hqbd N x
  have hclose : dist (H N x) (q x) < δF := by linarith
  have h3 := hδF (H N x) (q x) hclose
  have hqx : F (q x) = f x := by rw [hFf' (q x), hf'q x]
  rw [show f x = F (q x) from hqx.symm]
  exact h3

end Work.Brown.Engine
