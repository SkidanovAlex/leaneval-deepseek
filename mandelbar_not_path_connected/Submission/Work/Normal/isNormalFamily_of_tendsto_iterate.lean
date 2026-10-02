import Mathlib
import Submission.Work.Normal.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Normal families from locally uniform convergence of the iterates

If the sequence of iterates `f^[n]` of a self-map `f : ℂ → ℂ` converges locally uniformly on a set
`U` to a limit function `g`, then the family of iterates `{f^[n]}` is normal on `U`.  Indeed, every
sequence of members of `iterateFamily f` is a sequence of iterates `f^[k n]`; extract a strictly
monotone subsequence of the index sequence along which either `k` tends to `∞` (in which case the
corresponding iterates converge to `g` locally uniformly) or `k` is constant (in which case the
corresponding iterates are constant, hence convergent).

This is the elementary input that a locally uniform limit of the iterates is a normal family; it
does not use any holomorphicity.
-/

namespace Work.Normal

open Filter Set Topology Function
open scoped Topology

/-- **Reindexing.** Locally uniform convergence is preserved by composing with a strictly increasing
reindexing `φ : ℕ → ℕ` (equivalently, by a map tending to `atTop`). -/
theorem TendstoLocallyUniformlyOn.comp_strictMono_atTop {α : Type*} [TopologicalSpace α]
    {β : Type*} [UniformSpace β] {F : ℕ → α → β} {f : α → β} {U : Set α} {φ : ℕ → ℕ}
    (h : TendstoLocallyUniformlyOn F f atTop U) (hφ : Tendsto φ atTop atTop) :
    TendstoLocallyUniformlyOn (fun n => F (φ n)) f atTop U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at h ⊢
  intro x hx
  exact (h x hx).comp (hφ.prodMap (tendsto_id : Tendsto (id : α → α) _ _))

/-- A constant sequence of functions converges locally uniformly to that function. -/
theorem tendstoLocallyUniformlyOn_const_fun {α β : Type*} [TopologicalSpace α] [UniformSpace β]
    (c : α → β) (U : Set α) :
    TendstoLocallyUniformlyOn (fun _ : ℕ => c) c atTop U := by
  intro u hu x hx
  exact ⟨univ, univ_mem, Eventually.of_forall fun n y _ => refl_mem_uniformity hu⟩

theorem isNormalFamily_of_tendsto_iterate {f g : ℂ → ℂ} {U : Set ℂ}
    (h : TendstoLocallyUniformlyOn (fun n : ℕ => f^[n]) g Filter.atTop U) :
    IsNormalFamily (iterateFamily f) U := by
  classical
  intro u hu
  -- Every member of the iterate family is an iterate `f^[k n]`.
  choose k hk using fun n => hu n
  have hk' : ∀ n, f^[k n] = u n := fun n => hk n
  by_cases hk_top : Tendsto k atTop atTop
  · -- The index sequence already escapes to infinity: the subsequence converges to `g`.
    refine ⟨id, strictMono_id, Or.inl ⟨g, ?_⟩⟩
    have h1 : TendstoLocallyUniformlyOn (fun n => f^[k n]) g atTop U :=
      TendstoLocallyUniformlyOn.comp_strictMono_atTop h hk_top
    have h2 : TendstoLocallyUniformlyOn (fun n => u n) g atTop U :=
      TendstoLocallyUniformlyOn.congr h1 fun n z _ => by rw [hk' n]
    simpa using h2
  · -- Otherwise some value `m` is taken infinitely often, and a constant subsequence converges.
    rw [tendsto_atTop] at hk_top
    simp only [not_forall, not_eventually, not_le] at hk_top
    obtain ⟨M, hM⟩ := hk_top
    -- Pigeonhole: some `m < M` is attained frequently.
    have hex : ∃ m : Fin M, ∃ᶠ n in atTop, k n = (m : ℕ) := by
      by_contra hc
      simp only [not_exists, not_frequently] at hc
      have h1 : ∀ᶠ n in atTop, ∀ m : Fin M, k n ≠ (m : ℕ) := Filter.eventually_all.mpr hc
      obtain ⟨n, hn1, hn2⟩ := (h1.and_frequently hM).exists
      exact hn1 ⟨k n, hn2⟩ rfl
    obtain ⟨m, hm⟩ := hex
    obtain ⟨φ, hφ, hφk⟩ := extraction_of_frequently_atTop hm
    refine ⟨φ, hφ, Or.inl ⟨f^[m], ?_⟩⟩
    have hbase : TendstoLocallyUniformlyOn (fun _ : ℕ => (f^[m] : ℂ → ℂ)) (f^[m]) atTop U :=
      tendstoLocallyUniformlyOn_const_fun (f^[m]) U
    refine TendstoLocallyUniformlyOn.congr hbase fun n z _ => ?_
    show (f^[m]) z = u (φ n) z
    rw [← hk' (φ n), hφk n]

end Work.Normal
