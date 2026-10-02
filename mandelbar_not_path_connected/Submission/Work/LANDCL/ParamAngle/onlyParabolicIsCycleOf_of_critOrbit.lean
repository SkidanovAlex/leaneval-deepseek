import Mathlib
import Submission.Work.LANDCL.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Uniqueness of the parabolic cycle from Fatou's theorem on the critical orbit

This file proves `Work.LANDCL.OnlyParabolicIsCycleOf c z₁` from the two classical inputs

* `Work.LANDCL.ParabolicCycleInOmegaLimit c` — **Fatou's theorem on parabolic cycles**: every
  parabolic point is an `ω`-limit point of the critical orbit, hence lies in the closure of the
  range of `n ↦ (T_c)^[n] c`;
* the **convergence of the critical orbit to the characteristic point** `z₁`, in the form in
  which the root-parabolic data of the tricorn provides it
  (`Work.EL.RootParabolic.crit`): `(F c)^[n] c → z₁` with `F = (T_c)^[10] = (Tsq c)^[5]`
  (`Work.EL.F`, see `EL_F_eq_tantibar_iterate` below).

The mathematical content is the following.  A parabolic point `z` is periodic of some period `m`
for `T_c`, and it lies in `closure (range (T_c^[·] c))`.  The critical orbit is not assumed to
converge: only its subsequence in the steps `10 k` does.  Splitting the orbit into its ten residue
classes modulo `10`,

`range (T_c^[·] c) = ⋃_{r < 10} range (k ↦ (T_c)^[10k + r] c)`,

the `r`-th residue class converges to `(T_c)^[r] z₁` (continuity of `T_c^[r]`).  If `z` lies in
the closure of that residue class, then either it *is* the limit `(T_c)^[r] z₁`
(`closure_range_subset_range_union_singleton_of_tendsto`), or it is a term
`z = (T_c)^[10k + r] c` of the class; in the second case the tail of the class is periodic with
period `m` and the sub-subsequence `t ↦ (T_c)^[10(k + tm) + r] c` is constantly `z`, so again
`z = (T_c)^[r] z₁` by uniqueness of limits.  Finally `(T_c)^[5] z₁ = z₁` reduces the exponent
`r < 10` modulo `5` (`iterate_mod_eq_of_period`), which is the claimed form of the cycle.

The hypothesis `T_c z₁ ≠ z₁` is a hypothesis of the conclusion (the characteristic point is of
exact period `5`) and is used only as the corresponding conjunct of `OnlyParabolicIsCycleOf`.
-/

namespace Work.LANDCL.ParamAngle

open Filter
open scoped Topology

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## Elementary facts about the iterates of `T_c` -/

/-- `Tsq c` is the second iterate of the antiholomorphic quadratic `T_c`
(`Work.Landing.Tsq c = (T_c)^[2]`). -/
lemma Tantibar_iterate_two (c : ℂ) : (Tantibar c)^[2] = Work.Landing.Tsq c := by
  funext z
  simp [Work.Landing.Tsq, LeanEval.ComplexAnalysis.Tantibar, Function.iterate_succ]

/-- The map `F = (Tsq c)^[5]` of the EL areas is the **tenth** iterate of `T_c`. -/
lemma EL_F_eq_tantibar_iterate (c : ℂ) : Work.EL.F c = (Tantibar c)^[10] := by
  rw [Work.EL.F, ← Tantibar_iterate_two c, ← Function.iterate_mul]

/-- The iterates of `F c` on the critical point are the iterates of `T_c` in the steps `10`: the
critical orbit of `F` is the subsequence at the multiples of `10` of the critical orbit of
`T_c`. -/
lemma EL_F_iterate_apply (c : ℂ) (n : ℕ) :
    (Work.EL.F c)^[n] c = (Tantibar c)^[10 * n] c := by
  rw [EL_F_eq_tantibar_iterate, ← Function.iterate_mul]

/-- If `f^[d] x = x`, then the `t`-th iterate of `f^[d]` fixes `x`. -/
lemma iterate_self_of_period {f : ℂ → ℂ} {x : ℂ} {d : ℕ} (hd : f^[d] x = x) (t : ℕ) :
    (f^[d])^[t] x = x := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, hd]

/-- If `x` is periodic of period `d` for `f`, then the iterates of `x` depend on the exponent
only modulo `d`. -/
lemma iterate_mod_eq_of_period {f : ℂ → ℂ} {x : ℂ} {d : ℕ} (hd : f^[d] x = x) (k : ℕ) :
    f^[k] x = f^[k % d] x := by
  have hk : k = k % d + d * (k / d) := by
    rw [add_comm]; exact (Nat.div_add_mod k d).symm
  conv_lhs => rw [hk]
  rw [Function.iterate_add_apply, Function.iterate_mul, iterate_self_of_period hd]

/-! ## The orbit split into its residue classes modulo `10` -/

/-- The orbit of `c` under `f` is the union of its ten residue classes modulo `10`. -/
lemma range_iterate_eq_iUnion_residue (f : ℂ → ℂ) (c : ℂ) :
    Set.range (fun n : ℕ => f^[n] c)
      = ⋃ r : Fin 10, Set.range (fun k : ℕ => f^[10 * k + r.val] c) := by
  ext y
  simp only [Set.mem_range, Set.mem_iUnion]
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨⟨n % 10, Nat.mod_lt n (by norm_num)⟩, n / 10, ?_⟩
    have h : 10 * (n / 10) + n % 10 = n := Nat.div_add_mod n 10
    rw [h]
  · rintro ⟨r, k, rfl⟩
    exact ⟨10 * k + r.val, rfl⟩

/-- The closure of the range of a sequence converging at infinity to `a` is contained in the
range together with the limit `a`: the only accumulation point of the values of a convergent
sequence is its limit.

Indeed, if `x` were a further point of the closure, then (choosing `N` so that all later terms
are `dist x a / 2`-close to `a`) the closed ball of radius `dist x a / 2` around `a` covers all
terms with index `≥ N`, while the finitely many earlier terms together with `x` are separated
from the closed ball. -/
lemma closure_range_subset_range_union_singleton_of_tendsto {u : ℕ → ℂ} {a : ℂ}
    (hu : Tendsto u atTop (𝓝 a)) : closure (Set.range u) ⊆ Set.range u ∪ {a} := by
  intro x hx
  by_cases hxr : x ∈ Set.range u
  · exact Or.inl hxr
  · refine Or.inr ?_
    by_contra hne
    have hd : 0 < dist x a := dist_pos.mpr hne
    rw [Metric.tendsto_atTop] at hu
    obtain ⟨N, hN⟩ := hu (dist x a / 2) (by linarith)
    have hsub : Set.range u ⊆ u '' {n : ℕ | n < N} ∪ Set.range (fun n : ℕ => u (n + N)) := by
      rintro y ⟨n, rfl⟩
      rcases lt_or_ge n N with h | h
      · exact Or.inl ⟨n, h, rfl⟩
      · refine Or.inr ⟨n - N, ?_⟩
        show u (n - N + N) = u n
        rw [Nat.sub_add_cancel h]
    have hAf : (u '' {n : ℕ | n < N}).Finite := (Set.finite_Iio N).image u
    have hB : closure (Set.range (fun n : ℕ => u (n + N)))
        ⊆ Metric.closedBall a (dist x a / 2) := by
      refine closure_minimal ?_ Metric.isClosed_closedBall
      rintro y ⟨n, rfl⟩
      exact Metric.mem_closedBall.mpr (le_of_lt (hN (n + N) (by omega)))
    have hcl : closure (Set.range u)
        ⊆ u '' {n : ℕ | n < N} ∪ Metric.closedBall a (dist x a / 2) := by
      calc closure (Set.range u)
          ⊆ closure (u '' {n : ℕ | n < N} ∪ Set.range (fun n : ℕ => u (n + N))) :=
            closure_mono hsub
        _ = closure (u '' {n : ℕ | n < N}) ∪ closure (Set.range (fun n : ℕ => u (n + N))) :=
            closure_union
        _ = u '' {n : ℕ | n < N} ∪ closure (Set.range (fun n : ℕ => u (n + N))) := by
            rw [hAf.isClosed.closure_eq]
        _ ⊆ u '' {n : ℕ | n < N} ∪ Metric.closedBall a (dist x a / 2) :=
            Set.union_subset_union_right _ hB
    rcases hcl hx with hy | hy
    · obtain ⟨n, _, hn⟩ := hy
      exact hxr ⟨n, hn⟩
    · rw [Metric.mem_closedBall] at hy
      linarith

/-! ## The theorem -/

/-- **The uniqueness of the parabolic cycle at the root-parabolic parameter** (from Fatou's
theorem): if every parabolic point of `T_c` is an `ω`-limit point of the critical orbit
(`Work.LANDCL.ParabolicCycleInOmegaLimit`) and the critical orbit of the tenth iterate `F c`
converges to `z₁`, a point of exact period `5` for `T_c`, then the parabolic points of `T_c` are
exactly the five points of the cycle of `z₁` — i.e. `Work.LANDCL.OnlyParabolicIsCycleOf c z₁`.

The proof is the residue-class argument of the module docstring: a parabolic point `z` lies in
the closure of one of the ten residue classes of the critical orbit; that class converges to
`(T_c)^[r] z₁`, so `z = (T_c)^[r] z₁` with `r < 10` either as the limit or because the class is
eventually periodic with the period of `z`; and `(T_c)^[5] z₁ = z₁` reduces `r` modulo `5`. -/
theorem onlyParabolicIsCycleOf_of_critOrbit {c z₁ : ℂ} (h : Work.LANDCL.ParabolicCycleInOmegaLimit c)
    (h5 : (LeanEval.ComplexAnalysis.Tantibar c)^[5] z₁ = z₁)
    (hne : LeanEval.ComplexAnalysis.Tantibar c z₁ ≠ z₁)
    (hcrit : Filter.Tendsto (fun n : ℕ => (Work.EL.F c)^[n] c) Filter.atTop (nhds z₁)) :
    Work.LANDCL.OnlyParabolicIsCycleOf c z₁ := by
  refine ⟨h5, hne, ?_⟩
  intro z hz
  obtain ⟨m, hmpar⟩ := hz
  obtain ⟨hmpos, hmfix⟩ := hmpar.1
  -- `z` is in the closure of the critical orbit (Fatou)
  have hzcl : z ∈ closure (Set.range (fun n : ℕ => (Tantibar c)^[n] c)) := h z ⟨m, hmpar⟩
  rw [range_iterate_eq_iUnion_residue (Tantibar c) c, closure_iUnion_of_finite] at hzcl
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hzcl
  -- the critical orbit of `F c` is the subsequence of the critical orbit of `T_c` in the steps 10
  have hcrit' : Tendsto (fun n : ℕ => (Tantibar c)^[10 * n] c) atTop (𝓝 z₁) := by
    have hfun : (fun n : ℕ => (Work.EL.F c)^[n] c) = fun n : ℕ => (Tantibar c)^[10 * n] c :=
      funext (EL_F_iterate_apply c)
    rw [← hfun]
    exact hcrit
  -- hence the `r`-th residue class of the critical orbit converges to `(T_c)^[r] z₁`
  have hb : Tendsto (fun k : ℕ => (Tantibar c)^[10 * k + r.val] c) atTop
      (𝓝 ((Tantibar c)^[r.val] z₁)) := by
    have hiter : ∀ k : ℕ, (Tantibar c)^[10 * k + r.val] c
        = (Tantibar c)^[r.val] ((Tantibar c)^[10 * k] c) := by
      intro k
      rw [Nat.add_comm, Function.iterate_add_apply]
    have hfun : (fun k : ℕ => (Tantibar c)^[10 * k + r.val] c)
        = fun k : ℕ => (Tantibar c)^[r.val] ((Tantibar c)^[10 * k] c) := funext hiter
    rw [hfun]
    exact ((Work.Landing.Family.tantibar_continuous c).iterate r.val).tendsto z₁ |>.comp hcrit'
  -- `z` is either the limit of that class or a term of it
  have hzr := closure_range_subset_range_union_singleton_of_tendsto hb hr
  have hzeq : z = (Tantibar c)^[r.val] z₁ := by
    rcases hzr with hzrange | hzsing
    · obtain ⟨k, hk⟩ := hzrange
      have hk' : (Tantibar c)^[10 * k + r.val] c = z := hk
      -- the class is periodic with the period `m` of `z` from the index `k` on
      have hconst : ∀ t : ℕ, (Tantibar c)^[10 * (k + t * m) + r.val] c = z := by
        intro t
        have hidx : 10 * (k + t * m) + r.val = 10 * t * m + (10 * k + r.val) := by ring
        rw [hidx, Function.iterate_add_apply, hk']
        rw [show 10 * t * m = m * (10 * t) from by ring, Function.iterate_mul]
        exact iterate_self_of_period hmfix (10 * t)
      have hφ : Tendsto (fun t : ℕ => k + t * m) atTop atTop := by
        rw [Filter.tendsto_atTop_atTop]
        intro B
        exact ⟨B, fun t ht => by
          have h1 : t ≤ t * m := Nat.le_mul_of_pos_right t hmpos
          omega⟩
      have h1 : Tendsto (fun t : ℕ => (Tantibar c)^[10 * (k + t * m) + r.val] c) atTop (𝓝 z) := by
        rw [show (fun t : ℕ => (Tantibar c)^[10 * (k + t * m) + r.val] c) = fun _ => z
          from funext hconst]
        exact tendsto_const_nhds
      have h2 : Tendsto (fun t : ℕ => (Tantibar c)^[10 * (k + t * m) + r.val] c) atTop
          (𝓝 ((Tantibar c)^[r.val] z₁)) := hb.comp hφ
      exact tendsto_nhds_unique h1 h2
    · simpa using hzsing
  -- `(T_c)^[5] z₁ = z₁` reduces the exponent `r < 10` modulo `5`
  exact ⟨r.val % 5, Nat.mod_lt _ (by norm_num),
    by rw [hzeq, iterate_mod_eq_of_period h5 r.val]⟩

end Work.LANDCL.ParamAngle
