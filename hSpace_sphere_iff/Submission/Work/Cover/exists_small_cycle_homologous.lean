import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.Cover
import Submission.Work.Cohomology.sdFun_chainMap
import Submission.Work.Cohomology.tFun_homotopy
import Submission.Work.Cover.chainIn_sdFun_pow_of_cover
import Submission.Work.Cover.sdFun_mem_chainIn
import Submission.Work.Cover.tFun_mem_chainIn

namespace Work.Cover

open CategoryTheory Simplicial Opposite

open Submission.Cohomology

noncomputable section

/-! ## The small-cycle lemma for an open cover by two sets

For a topological space `X` with `X = U ∪ V`, `U`, `V` open, every singular cycle `c` is
homologous to a cycle lying in the "small chains" `chainIn X U n ⊔ chainIn X V n`: the cells of
which `c` is made are cut up by the cover only finitely often, so some iterate of the barycentric
subdivision lands in the small chains, and the iterated subdivision is chain homotopic to the
identity (the homotopy being `tFun` iterated).

The proof has three independent layers, each isolated below:

* the small chains are stable under subdivision (`sdFun_mem_sup`, `mem_iterate_sdFun_sup`);
* for every chain some iterate of the subdivision is small (`exists_iterate_sdFun_mem_sup`),
  which combines `chainIn_sdFun_pow_of_cover` (Lebesgue number) with linearity;
* for every cycle `c` of positive degree and every `N`, `Sd^N c - c` is a boundary
  (`exists_sbdry_iterate_sub_cycle`), which telescopes the chain homotopy `tFun_homotopy`
  using that the subdivision is a chain map.
-/

/-! ### The small chains are stable under the subdivision -/

/-- The submodule of chains lying in `U` or in `V` is stable under the subdivision. -/
private lemma sdFun_mem_sup (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    (chainIn X U n ⊔ chainIn X V n).map (sdFun X n) ≤ chainIn X U n ⊔ chainIn X V n := by
  rw [Submodule.map_sup]
  exact sup_le ((sdFun_mem_chainIn X U n).trans le_sup_left)
    ((sdFun_mem_chainIn X V n).trans le_sup_right)

/-- Membership form of `sdFun_mem_sup`. -/
private lemma mem_iterate_sdFun_sup {X : TopCat.{0}} {U V : Set X} {n : ℕ} (k : ℕ)
    {x : SChain (TopCat.toSSet.obj X) ℚ n} (hx : x ∈ chainIn X U n ⊔ chainIn X V n) :
    Nat.iterate (sdFun X n) k x ∈ chainIn X U n ⊔ chainIn X V n := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact Submodule.map_le_iff_le_comap.mp (sdFun_mem_sup X U V n) ih

/-! ### Linearity of the iterated subdivision -/

private lemma iterate_sdFun_add (X : TopCat.{0}) (n k : ℕ)
    (x y : SChain (TopCat.toSSet.obj X) ℚ n) :
    Nat.iterate (sdFun X n) k (x + y)
      = Nat.iterate (sdFun X n) k x + Nat.iterate (sdFun X n) k y := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, map_add]

private lemma iterate_sdFun_smul (X : TopCat.{0}) (n k : ℕ) (r : ℚ)
    (x : SChain (TopCat.toSSet.obj X) ℚ n) :
    Nat.iterate (sdFun X n) k (r • x) = r • Nat.iterate (sdFun X n) k x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_smul]

/-! ### Some iterate of the subdivision of any chain is small -/

private lemma exists_iterate_sdFun_mem_sup (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U)
    (hV : IsOpen V) (hUV : ∀ x, x ∈ U ∨ x ∈ V) (n : ℕ)
    (c : SChain (TopCat.toSSet.obj X) ℚ n) :
    ∃ N : ℕ, Nat.iterate (sdFun X n) N c ∈ chainIn X U n ⊔ chainIn X V n := by
  induction c using Finsupp.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
      obtain ⟨Nx, hxN⟩ := hx
      obtain ⟨Ny, hyN⟩ := hy
      refine ⟨max Nx Ny, ?_⟩
      have h1 : Nat.iterate (sdFun X n) (max Nx Ny) x ∈ chainIn X U n ⊔ chainIn X V n := by
        rw [← Nat.sub_add_cancel (le_max_left Nx Ny), Function.iterate_add_apply]
        exact mem_iterate_sdFun_sup _ hxN
      have h2 : Nat.iterate (sdFun X n) (max Nx Ny) y ∈ chainIn X U n ⊔ chainIn X V n := by
        rw [← Nat.sub_add_cancel (le_max_right Nx Ny), Function.iterate_add_apply]
        exact mem_iterate_sdFun_sup _ hyN
      rw [iterate_sdFun_add]
      exact Submodule.add_mem _ h1 h2
  | single σ r =>
      obtain ⟨N, hN⟩ := chainIn_sdFun_pow_of_cover X U V hU hV hUV n σ
      refine ⟨N, ?_⟩
      have hr : (Finsupp.single σ r : SChain (TopCat.toSSet.obj X) ℚ n)
          = r • Finsupp.single σ (1 : ℚ) := by
        rw [Finsupp.smul_single]; simp
      rw [hr, iterate_sdFun_smul]
      exact Submodule.smul_mem _ r hN

/-! ### The telescoped chain homotopy `Sd^N - id` is a boundary -/

/-- **The telescoping step.**  For a cycle `c` of degree `m+1`, the `k`-th iterate of the
subdivision applied to the homotopy chain `T c` has boundary `Sd^k c - Sd^{k+1} c`. -/
private lemma sbdry_iterate_sdFun_tFun (X : TopCat.{0}) (m : ℕ)
    (c : SChain (TopCat.toSSet.obj X) ℚ (m+1))
    (hc : sbdry (TopCat.toSSet.obj X) ℚ m c = 0) (k : ℕ) :
    sbdry (TopCat.toSSet.obj X) ℚ (m+1)
        (Nat.iterate (sdFun X (m+2)) k (tFun X (m+1) c))
      = Nat.iterate (sdFun X (m+1)) k c - Nat.iterate (sdFun X (m+1)) (k+1) c := by
  induction k with
  | zero =>
      rw [Function.iterate_zero_apply, Function.iterate_one]
      have h := Work.Cohomology.tFun_homotopy X m c
      rw [hc, map_zero, add_zero] at h
      exact h
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ← Work.Cohomology.sdFun_chainMap X (m+1), ih, map_sub]

/-- Summing the telescoping step: the boundary of the iterated homotopy chain `Σ_{k<N} Sd^k (T c)`
is `c - Sd^N c`. -/
private lemma sbdry_sum_iterate_tFun (X : TopCat.{0}) (m N : ℕ)
    (c : SChain (TopCat.toSSet.obj X) ℚ (m+1))
    (hc : sbdry (TopCat.toSSet.obj X) ℚ m c = 0) :
    sbdry (TopCat.toSSet.obj X) ℚ (m+1)
        (∑ k ∈ Finset.range N, Nat.iterate (sdFun X (m+2)) k (tFun X (m+1) c))
      = c - Nat.iterate (sdFun X (m+1)) N c := by
  rw [map_sum]
  rw [Finset.sum_congr rfl (fun k _ => sbdry_iterate_sdFun_tFun X m c hc k)]
  rw [Finset.sum_range_sub' (fun k => Nat.iterate (sdFun X (m+1)) k c) N,
    Function.iterate_zero_apply]

/-- Every iterate `Sd^N` of the subdivision differs from the identity on a cycle by a boundary. -/
private lemma exists_sbdry_iterate_sub_cycle (X : TopCat.{0}) (m : ℕ)
    (c : SChain (TopCat.toSSet.obj X) ℚ (m+1))
    (hc : c ∈ chainCycles (TopCat.toSSet.obj X) ℚ (m+1)) (N : ℕ) :
    ∃ d : SChain (TopCat.toSSet.obj X) ℚ (m+2),
      sbdry (TopCat.toSSet.obj X) ℚ (m+1) d
        = Nat.iterate (sdFun X (m+1)) N c - c := by
  refine ⟨-(∑ k ∈ Finset.range N, Nat.iterate (sdFun X (m+2)) k (tFun X (m+1) c)), ?_⟩
  rw [map_neg, sbdry_sum_iterate_tFun X m N c (mem_chainCycles_succ.mp hc)]
  abel

/-! ### Degree zero -/

/-- In degree zero the small chains are all the chains: every point of `X` lies in `U` or in
`V`, and a singular `0`-simplex is a point. -/
private lemma mem_sup_zero (X : TopCat.{0}) (U V : Set X) (hUV : ∀ x, x ∈ U ∨ x ∈ V)
    (c : SChain (TopCat.toSSet.obj X) ℚ 0) : c ∈ chainIn X U 0 ⊔ chainIn X V 0 := by
  induction c using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | single σ r =>
      have hpt := hUV (((TopCat.toSSetObjEquivT X (Opposite.op (SimplexCategory.mk 0))) σ)
        (Submission.Cohomology.vert 0))
      have hr : (Finsupp.single σ r : SChain (TopCat.toSSet.obj X) ℚ 0)
          = r • Finsupp.single σ (1 : ℚ) := by
        rw [Finsupp.smul_single]; simp
      rw [hr]
      refine Submodule.smul_mem _ r ?_
      rcases hpt with h | h
      · exact Submodule.mem_sup_left (single_mem_chainIn σ (fun t => by
          rw [Subsingleton.elim (α := stdSimplex ℝ (Fin 1)) t (Submission.Cohomology.vert 0)]; exact h))
      · exact Submodule.mem_sup_right (single_mem_chainIn σ (fun t => by
          rw [Subsingleton.elim (α := stdSimplex ℝ (Fin 1)) t (Submission.Cohomology.vert 0)]; exact h))

/-! ### The small-cycle lemma -/

theorem exists_small_cycle_homologous (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U)
    (hV : IsOpen V) (hUV : ∀ x, x ∈ U ∨ x ∈ V) (n : ℕ)
    (c : Submission.Cohomology.SChain (TopCat.toSSet.obj X) ℚ n)
    (hc : c ∈ Submission.Cohomology.chainCycles (TopCat.toSSet.obj X) ℚ n) :
    ∃ c' ∈ Submission.Cohomology.chainIn X U n ⊔ Submission.Cohomology.chainIn X V n,
      ∃ d : Submission.Cohomology.SChain (TopCat.toSSet.obj X) ℚ (n+1),
        Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ n d = c' - c := by
  cases n with
  | zero => exact ⟨c, mem_sup_zero X U V hUV c, 0, by simp⟩
  | succ m =>
      obtain ⟨N, hN⟩ := exists_iterate_sdFun_mem_sup X U V hU hV hUV (m+1) c
      obtain ⟨d, hd⟩ := exists_sbdry_iterate_sub_cycle X m c hc N
      exact ⟨Nat.iterate (sdFun X (m+1)) N c, hN, d, hd⟩

end

end Work.Cover
