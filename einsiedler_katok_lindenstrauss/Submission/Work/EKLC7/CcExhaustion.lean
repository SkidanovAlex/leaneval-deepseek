import Mathlib

/-!
# An increasing sequence of compactly supported continuous functions tending to `1`

On a locally compact, σ-compact Hausdorff space `X` there is an increasing sequence
`φ n : C_c(X, ℝ)` with `0 ≤ φ n ≤ 1` pointwise which converges pointwise to `1`
(in fact `φ n x = 1` for all large `n`).

The construction is the standard one: take a compact exhaustion `K n` of `X`
(`K n ⊆ interior (K (n+1))`, `⋃ K n = X`), use Urysohn's lemma to produce a compactly
supported `f n` which is `1` on `K n` and `0` off `interior (K (n+1))`, and let `φ n` be the
pointwise maximum of `f 0, …, f n`.

This is used to extend an integral identity from `C_c(X, ℝ)` to bounded continuous functions.
-/

namespace Work.EKLC7

theorem CcExhaustion {X : Type*} [TopologicalSpace X] [T2Space X] [RegularSpace X] [LocallyCompactSpace X] [SigmaCompactSpace X] : ∃ φ : ℕ → CompactlySupportedContinuousMap X ℝ, (∀ n x, 0 ≤ φ n x) ∧ (∀ n x, φ n x ≤ 1) ∧ (∀ n m, n ≤ m → ∀ x, φ n x ≤ φ m x) ∧ (∀ x, ∃ N, ∀ n, N ≤ n → φ n x = 1) := by
  classical
  -- an exhaustion of `X` by compact sets
  let K : CompactExhaustion X := default
  -- Urysohn functions: `f n` is `1` on `K n` and `0` off `interior (K (n+1))`
  have hK : ∀ n, ∃ f : ContinuousMap X ℝ,
      Set.EqOn (⇑f) 1 (K n) ∧ Set.EqOn (⇑f) 0 ((interior (K (n + 1)))ᶜ)
        ∧ HasCompactSupport (⇑f) ∧ ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := by
    intro n
    exact exists_continuous_one_zero_of_isCompact (K.isCompact n)
      isOpen_interior.isClosed_compl
      (Set.disjoint_compl_right_iff_subset.mpr (K.subset_interior_succ n))
  choose f hf_one hf_zero hf_supp hf_range using hK
  -- these as compactly supported continuous maps
  let ψ : ℕ → CompactlySupportedContinuousMap X ℝ := fun n => ⟨f n, hf_supp n⟩
  have hψ_apply : ∀ n x, ψ n x = f n x := fun n x => rfl
  -- `φ n` is the pointwise maximum of `ψ 0, …, ψ n`
  let φ : ℕ → CompactlySupportedContinuousMap X ℝ :=
    fun n => Nat.rec (ψ 0) (fun k acc => acc ⊔ ψ (k + 1)) n
  have hφ_succ : ∀ n, φ (n + 1) = φ n ⊔ ψ (n + 1) := fun n => rfl
  have hφ_mono_succ : ∀ n, φ n ≤ φ (n + 1) := by
    intro n
    rw [hφ_succ n]
    exact le_sup_left
  have hψ_le_φ : ∀ n, ψ n ≤ φ n := by
    intro n
    induction n with
    | zero => exact le_of_eq rfl
    | succ n _ =>
      rw [hφ_succ n]
      exact le_sup_right
  have h0 : ∀ n x, 0 ≤ φ n x := by
    intro n
    induction n with
    | zero => intro x; exact (hf_range 0 x).1
    | succ n ih =>
      intro x
      rw [hφ_succ n, CompactlySupportedContinuousMap.sup_apply]
      exact le_trans (ih x) le_sup_left
  have h1 : ∀ n x, φ n x ≤ 1 := by
    intro n
    induction n with
    | zero => intro x; exact (hf_range 0 x).2
    | succ n ih =>
      intro x
      rw [hφ_succ n, CompactlySupportedContinuousMap.sup_apply]
      exact sup_le (ih x) (hf_range (n + 1) x).2
  have hmono : ∀ n m, n ≤ m → ∀ x, φ n x ≤ φ m x :=
    fun n m hnm x => (CompactlySupportedContinuousMap.le_def.mp
      (monotone_nat_of_le_succ hφ_mono_succ hnm)) x
  have htop : ∀ x, ∃ N, ∀ n, N ≤ n → φ n x = 1 := by
    intro x
    refine ⟨K.find x, fun n hn => ?_⟩
    have hxK : x ∈ K n := K.subset hn (K.mem_find x)
    have hψx : ψ n x = 1 := by rw [hψ_apply n x]; exact hf_one n hxK
    have hle : ψ n x ≤ φ n x := (CompactlySupportedContinuousMap.le_def.mp (hψ_le_φ n)) x
    exact le_antisymm (h1 n x) (hψx ▸ hle)
  exact ⟨φ, h0, h1, hmono, htop⟩

end Work.EKLC7
