import Mathlib
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.same_period_defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Classical

namespace Work.LandLeaves

/-- **`σ^[P]` fixes all of `K` as soon as it fixes one point** (abstract form).

Let `f` be a self-map of a set `K ⊆ [0,1)` which is injective and `ccBet`-order preserving on `K`,
and suppose every point of `K` has a positive period under `f`.  If `f^[P]` fixes some `x ∈ K` with
`P > 0`, then `f^[P]` fixes every point of `K`.

The set `S = {f^[i] x : i < P} ∪ {f^[j] y : j < Q}` (`Q` a positive period of `y`) is a finite
subset of `K` on which `f^[P]` acts as an order-preserving self-map fixing `x`, so the
combinatorial lemma `Work.LandLeaves.fixed_point_id` applies. -/
theorem iterate_fixes_all_of_ccBet_aux {f : ℝ → ℝ} {K : Set ℝ}
    (hsub : ∀ x ∈ K, 0 ≤ x ∧ x < 1)
    (hmap : ∀ x ∈ K, f x ∈ K)
    (hinj : ∀ x ∈ K, ∀ y ∈ K, f x = f y → x = y)
    (hord : ∀ a ∈ K, ∀ b ∈ K, ∀ x ∈ K, ccBet a b x → ccBet (f a) (f b) (f x))
    (hper : ∀ a ∈ K, ∃ m : ℕ, 0 < m ∧ f^[m] a = a)
    {P : ℕ} (hP : 0 < P) {x : ℝ} (hx : x ∈ K) (hxP : f^[P] x = x) :
    ∀ y ∈ K, f^[P] y = y := by
  -- iterates of `f` stay in `K`
  have hK_f : ∀ n : ℕ, ∀ z ∈ K, f^[n] z ∈ K := by
    intro n
    induction n with
    | zero => intro z hz; rwa [Function.iterate_zero_apply]
    | succ n ih => intro z hz; rw [Function.iterate_succ_apply']; exact hmap _ (ih z hz)
  -- iterates of `f` are injective on `K`
  have hK_inj : ∀ n : ℕ, ∀ u ∈ K, ∀ v ∈ K, f^[n] u = f^[n] v → u = v := by
    intro n
    induction n with
    | zero => intro u hu v hv h; simpa using h
    | succ n ih =>
        intro u hu v hv h
        simp only [Function.iterate_succ_apply'] at h
        exact ih u hu v hv (hinj _ (hK_f n u hu) _ (hK_f n v hv) h)
  -- iterates of `f` preserve `ccBet` on `K`
  have hK_ord : ∀ n : ℕ, ∀ a ∈ K, ∀ b ∈ K, ∀ z ∈ K, ccBet a b z →
      ccBet (f^[n] a) (f^[n] b) (f^[n] z) := by
    intro n
    induction n with
    | zero => intro a ha b hb z hz h; simpa using h
    | succ n ih =>
        intro a ha b hb z hz h
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply']
        exact hord _ (hK_f n a ha) _ (hK_f n b hb) _ (hK_f n z hz) (ih a ha b hb z hz h)
  -- a period reduces exponents modulo it
  have hiter_mod : ∀ {n : ℕ} {a : ℝ}, f^[n] a = a → ∀ m : ℕ, f^[m] a = f^[m % n] a := by
    intro n a ha m
    have hmul : ∀ k : ℕ, f^[n * k] a = a := by
      intro k
      rw [Function.iterate_mul]
      induction k with
      | zero => rw [Function.iterate_zero_apply]
      | succ k ih => rw [Function.iterate_succ_apply' (f^[n]) k a, ih, ha]
    have hdec : m % n + n * (m / n) = m := by rw [Nat.add_comm, Nat.div_add_mod]
    calc f^[m] a = f^[m % n + n * (m / n)] a := by rw [hdec]
      _ = f^[m % n] (f^[n * (m / n)] a) :=
            Function.iterate_add_apply f (m % n) (n * (m / n)) a
      _ = f^[m % n] a := by rw [hmul (m / n)]
  intro y hy
  obtain ⟨Q, hQ, hyQ⟩ := hper y hy
  -- the finite set `S` on which `f^[P]` will be shown to act
  let S : Set ℝ := Set.range (fun i : Fin P => f^[i.val] x) ∪
      Set.range (fun j : Fin Q => f^[j.val] y)
  have hSfin : S.Finite := (Set.finite_range _).union (Set.finite_range _)
  -- every element of `S` is a suitable iterate
  have hxS : ∀ i : ℕ, f^[i] x ∈ S := by
    intro i
    refine Or.inl ⟨⟨i % P, Nat.mod_lt i hP⟩, ?_⟩
    exact (hiter_mod hxP i).symm
  have hyS : ∀ j : ℕ, f^[j] y ∈ S := by
    intro j
    refine Or.inr ⟨⟨j % Q, Nat.mod_lt j hQ⟩, ?_⟩
    exact (hiter_mod hyQ j).symm
  -- elements of `S` lie in `K`, hence in `[0,1)`
  have hmemK : ∀ z ∈ S, z ∈ K := by
    intro z hz
    rcases hz with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact hK_f i.val x hx
    · exact hK_f j.val y hy
  have hs01 : ∀ z ∈ hSfin.toFinset, z ∈ Set.Ico 0 1 := by
    intro z hz
    rw [Set.Finite.mem_toFinset hSfin] at hz
    exact hsub z (hmemK z hz)
  -- `f^[P]` maps `S` into itself
  have hmem_f : ∀ z ∈ hSfin.toFinset, f^[P] z ∈ hSfin.toFinset := by
    intro z hz
    rw [Set.Finite.mem_toFinset hSfin] at hz ⊢
    rcases hz with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · refine Or.inl ⟨⟨i.val, i.isLt⟩, ?_⟩
      rw [← Function.iterate_add_apply f P i.val x, Nat.add_comm,
        Function.iterate_add_apply f i.val P x, hxP]
    · refine Or.inr ⟨⟨(P + j.val) % Q, Nat.mod_lt _ hQ⟩, ?_⟩
      rw [← Function.iterate_add_apply f P j.val y]
      exact (hiter_mod hyQ (P + j.val)).symm
  -- `f^[P]` is injective on `S`
  have hinj_f : ∀ u ∈ hSfin.toFinset, ∀ v ∈ hSfin.toFinset, f^[P] u = f^[P] v → u = v := by
    intro u hu v hv h
    rw [Set.Finite.mem_toFinset hSfin] at hu hv
    exact hK_inj P u (hmemK u hu) v (hmemK v hv) h
  -- `f^[P]` preserves `ccBet` on `S`
  have hord_f : ∀ a ∈ hSfin.toFinset, ∀ b ∈ hSfin.toFinset, ∀ z ∈ hSfin.toFinset,
      ccBet a b z → ccBet (f^[P] a) (f^[P] b) (f^[P] z) := by
    intro a ha b hb z hz h
    rw [Set.Finite.mem_toFinset hSfin] at ha hb hz
    exact hK_ord P a (hmemK a ha) b (hmemK b hb) z (hmemK z hz) h
  have hx_s : x ∈ hSfin.toFinset := by
    rw [Set.Finite.mem_toFinset hSfin]
    simpa using hxS 0
  have hy_s : y ∈ hSfin.toFinset := by
    rw [Set.Finite.mem_toFinset hSfin]
    simpa using hyS 0
  exact fixed_point_id hs01 hmem_f hinj_f hord_f hx_s hxP y hy_s

/-- **`σ^[P]` fixes all of `K` as soon as it fixes one point.**

Let `d ≥ 2`, `σ x = Int.fract (d * x)`, and `K ⊆ [0,1)` invariant under `σ`, with `σ` injective and
`ccBet`-order-preserving on `K`.  Assume every point of `K` has a positive period under `σ`.  If
`x ∈ K` and `σ^[P] x = x` with `P > 0`, then `σ^[P] y = y` for every `y ∈ K`.

Proof sketch: `S = {σ^[i] x : i < P} ∪ {σ^[i] y : i < Q}` (`Q` a positive period of `y`) is a finite
subset of `K` on which `h = σ^[P]` acts as an order-preserving bijection fixing `x`.  The
combinatorial lemma `Work.LandLeaves.fixed_point_id` (finite cyclically ordered set: an
order-preserving bijection fixing one point is the identity) gives `σ^[P] y = y`. -/
theorem iterate_fixes_all_of_ccBet {d : ℕ} (hd : 2 ≤ d) {K : Set ℝ}
    (hsub : ∀ x ∈ K, 0 ≤ x ∧ x < 1)
    (hmap : ∀ x ∈ K, Int.fract ((d : ℝ) * x) ∈ K)
    (hinj : ∀ x ∈ K, ∀ y ∈ K, Int.fract ((d : ℝ) * x) = Int.fract ((d : ℝ) * y) → x = y)
    (hord : ∀ a ∈ K, ∀ b ∈ K, ∀ x ∈ K, Work.LandLeaves.ccBet a b x →
      Work.LandLeaves.ccBet (Int.fract ((d : ℝ) * a)) (Int.fract ((d : ℝ) * b))
        (Int.fract ((d : ℝ) * x)))
    (hper : ∀ a ∈ K, ∃ m : ℕ, 0 < m ∧ (fun x : ℝ => Int.fract ((d : ℝ) * x))^[m] a = a)
    {P : ℕ} (hP : 0 < P) {x : ℝ} (hx : x ∈ K)
    (hxP : (fun z : ℝ => Int.fract ((d : ℝ) * z))^[P] x = x) :
    ∀ y ∈ K, (fun z : ℝ => Int.fract ((d : ℝ) * z))^[P] y = y := by
  exact iterate_fixes_all_of_ccBet_aux hsub hmap hinj hord hper hP hx hxP

end Work.LandLeaves
