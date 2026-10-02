import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A diagonal subsequence converging locally uniformly from an exhaustion

This is the diagonal extraction used to deduce Montel's theorem from a
"uniform convergence on every member of a compact exhaustion" input.

Suppose `U ⊆ ℂ` is open, `K : ℕ → Set ℂ` is a family whose members eventually
contain every compact subset of `U` (`hcover`), and suppose that every
subsequence of `v : ℕ → ℂ → ℂ` has a further subsequence converging uniformly on
each `K n` (`hsub`).  Then `v` has a subsequence converging *locally uniformly*
on all of `U`.

The proof is the classical nested-subsequence diagonal: build `ψ 0 = id`,
`ψ (n+1) = ψ n ∘ σ n` with `v ∘ ψ (n+1)` uniformly convergent on `K n`, and set
`φ k = ψ k k`.  The tail `k ≥ n+1` of `φ` is a subsequence of `ψ (n+1)`, hence
`v ∘ φ` converges uniformly on `K n`.  The limit functions on the various `K n`
agree on overlaps, so they glue to a single `g : ℂ → ℂ`.
-/

namespace Work.Normal

open Filter Set Topology Function
open scoped Topology

/-- A uniform limit on `s` persists under reindexing by a map tending to infinity. -/
lemma tendstoUniformlyOn_comp_index_tendsto {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {s : Set ℂ}
    (h : TendstoUniformlyOn F f atTop s) {τ : ℕ → ℕ} (hτ : Tendsto τ atTop atTop) :
    TendstoUniformlyOn (fun k => F (τ k)) f atTop s := by
  intro u hu
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h u hu)
  rw [Filter.tendsto_atTop_atTop] at hτ
  obtain ⟨a, ha⟩ := hτ N
  exact Filter.eventually_atTop.mpr ⟨a, fun k hk => hN (τ k) (ha k hk)⟩

lemma exists_subseq_tendstoLocallyUniformlyOn_of_exhaustion
    {U : Set ℂ} (hU : IsOpen U) (v : ℕ → ℂ → ℂ) (K : ℕ → Set ℂ)
    (hcover : ∀ K' : Set ℂ, K' ⊆ U → IsCompact K' → ∃ n, K' ⊆ K n)
    (hsub : ∀ (ψ : ℕ → ℕ), StrictMono ψ → ∀ n : ℕ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∃ g : ℂ → ℂ, TendstoUniformlyOn (fun k => v (ψ (σ k))) g atTop (K n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ,
      TendstoLocallyUniformlyOn (fun k => v (φ k)) g atTop U := by
  classical
  -- Nested subsequences: `tower n = ψ n` with `ψ 0 = id` and `ψ (n+1) = ψ n ∘ sig n`,
  -- where `sig n` is chosen so that `v ∘ ψ (n+1)` converges uniformly on `K n`.
  let tower : ℕ → {ψ : ℕ → ℕ // StrictMono ψ} :=
    fun n => Nat.rec (motive := fun _ => {ψ : ℕ → ℕ // StrictMono ψ})
      ⟨id, strictMono_id⟩
      (fun m ih => ⟨ih.1 ∘ Classical.choose (hsub ih.1 ih.2 m),
        ih.2.comp (Classical.choose_spec (hsub ih.1 ih.2 m)).1⟩) n
  let sig : ℕ → ℕ → ℕ := fun n => Classical.choose (hsub (tower n).1 (tower n).2 n)
  let gg : ℕ → ℂ → ℂ := fun n =>
    Classical.choose (Classical.choose_spec (hsub (tower n).1 (tower n).2 n)).2
  have hsig : ∀ n, StrictMono (sig n) := fun n =>
    (Classical.choose_spec (hsub (tower n).1 (tower n).2 n)).1
  have hstep : ∀ n, (tower (n+1)).1 = (tower n).1 ∘ sig n := fun n => rfl
  have hconv : ∀ n, TendstoUniformlyOn (fun k => v ((tower (n+1)).1 k)) (gg n) atTop (K n) :=
    fun n => Classical.choose_spec (Classical.choose_spec (hsub (tower n).1 (tower n).2 n)).2
  -- `C n j = sig n ∘ sig (n+1) ∘ ⋯ ∘ sig (n+j-1)`, so that `ψ (n+j) = ψ n ∘ C n j`.
  let C : ℕ → ℕ → (ℕ → ℕ) := fun n =>
    fun j => Nat.rec (motive := fun _ => ℕ → ℕ) id (fun j ih => ih ∘ sig (n + j)) j
  have hC : ∀ n j, (tower (n+j)).1 = (tower n).1 ∘ C n j := by
    intro n j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [show C n (j+1) = C n j ∘ sig (n+j) from rfl, ← Function.comp_assoc, ← ih]
      rw [show n + (j+1) = (n+j) + 1 from Nat.add_succ n j]
  have hCmono : ∀ n j, StrictMono (C n j) := by
    intro n j
    induction j with
    | zero => exact strictMono_id
    | succ j ih =>
      rw [show C n (j+1) = C n j ∘ sig (n+j) from rfl]
      exact ih.comp (hsig (n+j))
  -- The diagonal.
  let φ : ℕ → ℕ := fun k => (tower k).1 k
  have hφ : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro k
    show (tower k).1 k < (tower (k+1)).1 (k+1)
    rw [hstep k]
    change (tower k).1 k < (tower k).1 (sig k (k + 1))
    exact (tower k).2 (lt_of_le_of_lt ((hsig k).id_le k) ((hsig k) (Nat.lt_succ_self k)))
  -- For `k ≥ n+1`, `φ k = ψ (n+1) (C (n+1) (k-(n+1)) k)`.
  have hτ_tendsto : ∀ n, Tendsto (fun k => C (n+1) (k - (n+1)) k) atTop atTop := by
    intro n
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨max b (n+1), fun k hk => ?_⟩
    exact le_trans (le_trans (le_max_left b (n+1)) hk) ((hCmono (n+1) (k-(n+1))).id_le k)
  have hτ_eq : ∀ n k, n+1 ≤ k → (tower (n+1)).1 (C (n+1) (k-(n+1)) k) = (tower k).1 k := by
    intro n k hk
    have h := hC (n+1) (k-(n+1))
    have hk' : (n+1) + (k-(n+1)) = k := by omega
    rw [hk'] at h
    exact (congrFun h k).symm
  -- Convergence of the diagonal on each `K n`.
  have hconv_n : ∀ n, TendstoUniformlyOn (fun k => v (φ k)) (gg n) atTop (K n) := by
    intro n
    have h1 := tendstoUniformlyOn_comp_index_tendsto (hconv n) (hτ_tendsto n)
    refine h1.congr ?_
    rw [Filter.eventually_atTop]
    refine ⟨n+1, fun k hk x hx => ?_⟩
    show v ((tower (n+1)).1 (C (n+1) (k - (n+1)) k)) x = v (φ k) x
    rw [hτ_eq n k hk]
  -- The limits on the various `K n` are compatible on overlaps.
  have hcompat : ∀ i j, Set.EqOn (gg i) (gg j) (K i ∩ K j) := by
    intro i j x hx
    exact tendsto_nhds_unique ((hconv_n i).tendsto_at hx.1) ((hconv_n j).tendsto_at hx.2)
  -- Glue the limits into a single function.
  let g : ℂ → ℂ := fun x => if h : ∃ n, x ∈ K n then gg (Classical.choose h) x else 0
  have hg_eq : ∀ n, Set.EqOn g (gg n) (K n) := by
    intro n x hx
    have h : ∃ m, x ∈ K m := ⟨n, hx⟩
    simp only [g, dite_eq_left h]
    exact hcompat (Classical.choose h) n ⟨Classical.choose_spec h, hx⟩
  have hconvg : ∀ n, TendstoUniformlyOn (fun k => v (φ k)) g atTop (K n) :=
    fun n => (hconv_n n).congr_right (hg_eq n).symm
  refine ⟨φ, hφ, g, ?_⟩
  -- Local uniform convergence = uniform convergence on compacta for open `U`.
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K' hK'U hK'c
  obtain ⟨n, hn⟩ := hcover K' hK'U hK'c
  exact (hconvg n).mono hn

end Work.Normal
