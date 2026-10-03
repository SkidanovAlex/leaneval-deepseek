import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.basin_facts

/-!
# `Work.HornCov.critOrbit_injective`

For `f₀ ∈ 𝓕₀` with immediate basin `B` and (unique) critical point `c ∈ B`, the forward critical
orbit `k ↦ f₀^[k] c` is injective on `k ≥ 1`.

The proof is elementary and rests on two facts about the parabolic basin already available in the
workspace:

* `Work.Horn.BasinAux.tendsto_zero`: every orbit in `ParabolicBasin f₀ D₀` converges to `0`;
* `Work.Horn.BasinAux.zero_not_mem`: `0 ∉ ParabolicBasin f₀ D₀` (equivalently `0` is a *repelling*
  fixed point: no neighbourhood converges uniformly to it).

Since `c ∈ B ⊆ ParabolicBasin` and `f₀^[k] c ∈ B` for every `k`, no iterate of `c` can be `0`.
If now `f₀^[a] c = f₀^[b] c` with `a < b`, then `w = f₀^[a] c` is fixed by `f₀^[b-a]`, so the
subsequence `n ↦ f₀^[a + n(b-a)] c` is constantly `w` while (being a subsequence of the
convergent orbit) it tends to `0`; hence `w = 0 ∈ B`, contradiction.
-/

namespace Work.HornCov

open MandelDim Filter Topology Set

theorem critOrbit_injective (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ)
    (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) :
    ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → f₀^[a] c = f₀^[b] c → a = b := by
  obtain ⟨hopenD, h0D, hdiff, hfix, hderiv0, -⟩ := hsetup.1
  obtain ⟨-, -, hbas, -, hmaps, -, -⟩ := hsetup.2.1
  have hcB : c ∈ B := hsetup.2.2.1
  -- `0` is not in the immediate basin
  have hzeroB : (0 : ℂ) ∉ B :=
    fun h => Work.Horn.BasinAux.zero_not_mem hopenD h0D hdiff hfix hderiv0 (hbas h)
  -- the whole critical orbit converges to `0`
  have htend : Tendsto (fun n : ℕ => f₀^[n] c) atTop (𝓝 0) :=
    Work.Horn.BasinAux.tendsto_zero (hbas hcB)
  -- `a < b` is impossible
  have key : ∀ a b : ℕ, f₀^[a] c = f₀^[b] c → ¬ (a < b) := by
    intro a b hab hlt
    set p : ℕ := b - a with hpdef
    have hp : 0 < p := by omega
    have hper : f₀^[p] (f₀^[a] c) = f₀^[a] c := by
      rw [← Function.iterate_add_apply f₀ p a c]
      rw [show p + a = b by omega]
      exact hab.symm
    have hnper : ∀ n : ℕ, f₀^[n * p] (f₀^[a] c) = f₀^[a] c := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
          rw [show (k + 1) * p = k * p + p by ring,
            Function.iterate_add_apply f₀ (k * p) p (f₀^[a] c), hper, ih]
    have hconst : (fun n : ℕ => f₀^[a + n * p] c) = fun _ => f₀^[a] c := by
      funext n
      rw [show a + n * p = n * p + a by ring, Function.iterate_add_apply f₀ (n * p) a c]
      exact hnper n
    have hψ : Tendsto (fun n : ℕ => a + n * p) atTop atTop :=
      Filter.tendsto_atTop_atTop.mpr fun m => ⟨m, fun n hn => by
        have h1 : n ≤ n * p := Nat.le_mul_of_pos_right n hp
        have h2 : n * p ≤ a + n * p := Nat.le_add_left _ _
        omega⟩
    have hsub : Tendsto (fun n : ℕ => f₀^[a + n * p] c) atTop (𝓝 0) := htend.comp hψ
    have h0 : f₀^[a] c = 0 := by
      have hc : Tendsto (fun _ : ℕ => f₀^[a] c) atTop (𝓝 0) := by simpa [hconst] using hsub
      exact tendsto_nhds_unique tendsto_const_nhds hc
    exact hzeroB (h0 ▸ MapsTo.iterate hmaps a hcB)
  intro a b _ _ hab
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact absurd h (key a b hab)
  · exact h
  · exact absurd h (key b a hab.symm)

end Work.HornCov
