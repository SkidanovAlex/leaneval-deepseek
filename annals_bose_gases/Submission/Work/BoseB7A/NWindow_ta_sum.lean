import Mathlib.Analysis.Normed.Field.Basic
import Submission.Work.BoseB7A.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.NWindow_ta_sum`

The window bound for a finite family of θ-modes:

```
∑_{s ∈ S} ⟨ã_s Φ, ã_s Φ⟩ ≤ 𝓜 ‖Φ‖²     for  Φ ∈ Ran 1_{[0,𝓜]}(n₊),  S ∌ 0.
```

This is the standard FS §6 consequence of the localisation
`Φ = 1_{[0,𝓜]}(n₊)Φ` (`eq:LocalizedAftercNumber`) used by *every* estimate of
§10: a single mode `ã_s` lowers `n₊` by one (`N_ta`), so `ã_s Φ` still lives in
the window, and

`∑_{s∈S} ⟨ã_sΦ,ã_sΦ⟩ = ⟨(∑_{s∈S} ã_s†ã_s)Φ, Φ⟩ ≤ ⟨n₊Φ, Φ⟩ ≤ 𝓜⟨Φ,Φ⟩`,

the middle step being `TildeData.ta_le_N` (a finite orthonormal family of
θ-modes counts at most `n₊` particles) and the last the numerical content of the
window: writing `Φ = ∑_{m ≤ ⌊𝓜⌋₊} φ_m` with `n₊φ_m = m φ_m`, the `φ_m` are
pairwise orthogonal because `n₊` is self-adjoint (`TildeData.N_symm`), so both
`⟨n₊Φ,Φ⟩` and `‖Φ‖²` are the diagonal sums `∑_m m‖φ_m‖²` and `∑_m ‖φ_m‖²`
(with `m = 0` contributing nothing), and `m ≤ ⌊𝓜⌋₊ ≤ 𝓜` termwise.

The two ingredients are proved here as the generic lemmas `bp_sum_sum` (the
expansion of a bilinear form on sums) and `bp_window_le` (the window bound for
an abstract self-adjoint operator with a `ℕ`-graded eigenfamily); the target
theorem is then an immediate application.  Nothing about `Mode`, `F`, `T`
beyond the fields of `FockData`/`TildeData` is used.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

open Work.BoseB7

variable {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- Expansion of a bilinear form `B` on sums:
`B (∑_{i∈s} u i) (∑_{j∈t} v j) = ∑_{i∈s} ∑_{j∈t} B (u i) (v j)`. -/
private theorem bp_sum_sum (B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (u : ι → H) (v : κ → H) :
    B (∑ i ∈ s, u i) (∑ j ∈ t, v j) = ∑ i ∈ s, ∑ j ∈ t, B (u i) (v j) := by
  have h1 : B (∑ i ∈ s, u i) = ∑ i ∈ s, B (u i) := map_sum B u s
  rw [h1, LinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => map_sum (B (u i)) v t)

/-- **The numerical content of the window** `Φ ∈ Ran 1_{[0,𝓜]}(n₊)`, for an
abstract self-adjoint operator `N` on a space with a positive semidefinite
symmetric form `B`: if `Φ = ∑_{m ≤ ⌊𝓜⌋₊} φ_m` with `Nφ_m = mφ_m`, then
`B (NΦ) Φ ≤ 𝓜 B Φ Φ`. -/
private theorem bp_window_le (B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (N : H →ₗ[ℝ] H)
    (hNsymm : ∀ f g, B (N f) g = B f (N g)) (hpos : ∀ f, 0 ≤ B f f)
    {M : ℝ} (hM : 0 ≤ M) (φ : ℕ → H) (hφ : ∀ m, N (φ m) = (m : ℝ) • φ m) :
    B (N (∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m)) (∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m)
      ≤ M * B (∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m) (∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m) := by
  set I := Finset.range (⌊M⌋₊ + 1)
  -- eigenvectors of distinct eigenvalues are orthogonal (`N` is self-adjoint)
  have hcross : ∀ i j : ℕ, i ≠ j → B (φ i) (φ j) = 0 := by
    intro i j hij
    have h1 : B (N (φ i)) (φ j) = (i : ℝ) * B (φ i) (φ j) := by
      simp only [hφ i, map_smul, LinearMap.smul_apply, smul_eq_mul]
    have h2 : B (φ i) (N (φ j)) = (j : ℝ) * B (φ i) (φ j) := by
      simp only [hφ j, map_smul, smul_eq_mul]
    have h3 := hNsymm (φ i) (φ j)
    have h : ((i : ℝ) - (j : ℝ)) * B (φ i) (φ j) = 0 := by linarith
    have hne : ((i : ℝ) - (j : ℝ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hij)
    exact (mul_eq_zero.mp h).resolve_left hne
  have hNsum : N (∑ m ∈ I, φ m) = ∑ m ∈ I, (m : ℝ) • φ m := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => hφ m
  have hinner : ∀ m ∈ I, ∑ n ∈ I, B ((m : ℝ) • φ m) (φ n) = (m : ℝ) * B (φ m) (φ m) := by
    intro m hm
    have e1 : ∀ n, B ((m : ℝ) • φ m) (φ n) = (m : ℝ) * B (φ m) (φ n) := fun n => by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun n _ => e1 n), ← Finset.mul_sum]
    congr 1
    exact Finset.sum_eq_single m (fun b _ hbm => hcross m b hbm.symm) (fun h => absurd hm h)
  have hnorm : B (∑ m ∈ I, φ m) (∑ m ∈ I, φ m) = ∑ m ∈ I, B (φ m) (φ m) := by
    rw [bp_sum_sum]
    exact Finset.sum_congr rfl fun m hm =>
      Finset.sum_eq_single m (fun b _ hbm => hcross m b hbm.symm) (fun h => absurd hm h)
  calc B (N (∑ m ∈ I, φ m)) (∑ m ∈ I, φ m)
      = B (∑ m ∈ I, (m : ℝ) • φ m) (∑ n ∈ I, φ n) := by rw [hNsum]
    _ = ∑ m ∈ I, ∑ n ∈ I, B ((m : ℝ) • φ m) (φ n) := bp_sum_sum B I I _ _
    _ = ∑ m ∈ I, (m : ℝ) * B (φ m) (φ m) := Finset.sum_congr rfl hinner
    _ ≤ ∑ m ∈ I, M * B (φ m) (φ m) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hmM : (m : ℝ) ≤ M := by
          have h1 : m ≤ ⌊M⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
          have h2 : (m : ℝ) ≤ (⌊M⌋₊ : ℝ) := Nat.cast_le.mpr h1
          linarith [Nat.floor_le hM]
        exact mul_le_mul_of_nonneg_right hmM (hpos (φ m))
    _ = M * ∑ m ∈ I, B (φ m) (φ m) := (Finset.mul_sum I _ M).symm
    _ = M * B (∑ m ∈ I, φ m) (∑ m ∈ I, φ m) := by rw [hnorm]

/-- **The window bound for a finite family of θ-modes.**  For a state
`Φ = 1_{[0,𝓜]}(n₊)Φ` (`TildeData.NWindow M Φ`), the total weight of the modes
`ã_s`, `s ∈ S ∌ 0`, is at most `𝓜‖Φ‖²` — the finite-mode form of
`∑_s ã_s†ã_s ≤ n₊`. -/
theorem NWindow_ta_sum {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) {M : ℝ} (hM : 0 ≤ M)
    {Ψ : F.H} (hΨ : T.NWindow M Ψ) (S : Finset Mode) (hS : ∀ s ∈ S, s ≠ 0) :
    ∑ s ∈ S, F.bp (T.ta s Ψ) (T.ta s Ψ) ≤ M * F.normSq Ψ := by
  obtain ⟨φ, hφ, rfl⟩ := hΨ
  -- `∑_s ⟨ã_sΦ, ã_sΦ⟩ = ⟨(∑_s ã_s†ã_s)Φ, Φ⟩` by ℓ²-adjointness of the θ-modes
  have key : F.bp ((∑ s ∈ S, T.taDag s ∘ₗ T.ta s) (∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m))
        (∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m)
      = ∑ s ∈ S, F.bp (T.ta s (∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m))
          (T.ta s (∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m)) := by
    calc F.bp ((∑ s ∈ S, T.taDag s ∘ₗ T.ta s) (∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m))
          (∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m)
        = F.bp (∑ s ∈ S, (T.taDag s ∘ₗ T.ta s) (∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m))
            (∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m) := by
            rw [LinearMap.sum_apply S (fun s => T.taDag s ∘ₗ T.ta s)
              (∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m)]
      _ = ∑ s ∈ S, F.bp ((T.taDag s ∘ₗ T.ta s) (∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m))
            (∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m) := by
            have hh : F.bp (∑ s ∈ S, (T.taDag s ∘ₗ T.ta s) (∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m))
                = ∑ s ∈ S, F.bp ((T.taDag s ∘ₗ T.ta s) (∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m)) :=
              map_sum F.bp _ S
            rw [hh, LinearMap.sum_apply]
      _ = ∑ s ∈ S, F.bp (T.ta s (∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m))
            (T.ta s (∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m)) :=
            Finset.sum_congr rfl (fun s _ => by
              simp only [LinearMap.comp_apply]
              exact T.taDag_adjoint s (T.ta s (∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m))
                (∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m))
  rw [← key]
  refine le_trans (T.ta_le_N S hS _) ?_
  rw [Work.BoseB7.FockData.normSq]
  exact bp_window_le F.bp T.N (fun f g => T.N_symm f g) (fun f => F.bp_nonneg f) hM φ hφ

end Work.BoseB7A
