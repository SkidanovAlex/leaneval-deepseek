import Mathlib
import Submission.Work.WilC4aAL.Defs
import Submission.Work.WilC4aAL.Basic

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilC4aAL
open WilkiesDesign.CG.C4a

/--
**AL.1 (Puiseux gives a *common* branch cover).**

`PuiseuxReal` applied to each coefficient family `c i` separately produces, for each `i`,
a ramification exponent `N i`, a finite family of branches `ζ i ·` analytic at `0`, and a
radius `R0 i` such that for `0 < r < R0 i` the real roots of `mpoly (c i) (r ^ (N i)) ·`
are exactly the branch values `ζ i j r`.

To obtain a *single* ramification for all `i` at once, put `N := ∏ i, N i` and
`M i := N / N i` (so that `M i * N i = N`, hence `((r) ^ (M i)) ^ (N i) = r ^ N`), and
transport the `i`-th Puiseux statement from the parameter `r ^ (M i)` to the parameter `r`.
Since `M i ≥ 1`, `r ↦ r ^ (M i)` maps `(0, min 1 (min i, R0 i))` into `(0, R0 i)`, so the
cover of the `i`-th zero set is inherited verbatim.
-/
theorem puiseux_root_cover (hP : WilkiesDesign.CG.C4a.PuiseuxReal) {k : ℕ} {d : Fin k → ℕ}
    {c : ∀ i, Fin (d i) → ℝ → ℝ} (hc : ∀ i j, AnalyticAt ℝ (c i j) 0) :
    ∃ N > (0 : ℕ), ∃ m : Fin k → ℕ, ∃ ζ : ∀ i, Fin (m i) → ℝ → ℝ,
      AnalyticBranches m ζ ∧ BranchCover (fun i j r => c i j (r ^ N)) m ζ := by
  classical
  -- Puiseux data for each coefficient family, chosen independently.
  have h := fun i : Fin k => hP (d i) (c i) (hc i)
  choose Nf m ζ hh using h
  have hNfpos : ∀ i, 0 < Nf i := fun i => (hh i).1
  have hζan : ∀ i j, AnalyticAt ℝ (ζ i j) 0 := fun i => (hh i).2.1
  have hR0 : ∀ i, ∃ r0 : ℝ, r0 > (0 : ℝ) ∧ ∀ r ∈ Set.Ioo (0 : ℝ) r0, ∀ z : ℝ,
      (mpoly (c i) (r ^ Nf i) z = 0 ↔ ∃ j, z = ζ i j r) := fun i => (hh i).2.2
  choose R0 hR0pos hR0root using hR0
  -- Common ramification exponent.
  set N : ℕ := ∏ i : Fin k, Nf i with hNdef
  have hNpos : 0 < N := by rw [hNdef]; exact Finset.prod_pos (fun i _ => hNfpos i)
  have hdvd : ∀ i, Nf i ∣ N := by
    intro i; rw [hNdef]; exact Finset.dvd_prod_of_mem Nf (Finset.mem_univ i)
  have hMN : ∀ i, (N / Nf i) * Nf i = N := fun i => Nat.div_mul_cancel (hdvd i)
  have hMpos : ∀ i, 0 < N / Nf i := fun i => Nat.pos_of_ne_zero (fun h0 => by
    have hc0 := hMN i; rw [h0, zero_mul] at hc0; exact hNpos.ne' hc0.symm)
  refine ⟨N, hNpos, m, fun i j r => ζ i j (r ^ (N / Nf i)), ?_, ?_⟩
  · -- Each branch `r ↦ ζ i j (r ^ (N / Nf i))` is analytic at `0`.
    intro i j
    exact analyticAt_comp_pow (hζan i j) (hMpos i)
  · -- Branch cover: transport the `i`-th statement along `r ↦ r ^ (N / Nf i)`.
    by_cases hk : (Finset.univ : Finset (Fin k)).Nonempty
    · refine ⟨min 1 (Finset.univ.inf' hk R0), lt_min one_pos ?_, ?_⟩
      · exact (Finset.lt_inf'_iff hk).mpr (fun i _ => hR0pos i)
      · intro r hr i z hz
        set r' := r ^ (N / Nf i) with hr'def
        have hr1 : r < 1 := lt_of_lt_of_le hr.2 (min_le_left _ _)
        have hrR0 : r < R0 i := lt_of_lt_of_le hr.2
          (le_trans (min_le_right _ _) (Finset.inf'_le R0 (Finset.mem_univ i)))
        have hr'le : r' ≤ r := by
          rw [hr'def]; exact pow_le_of_le_one hr.1.le hr1.le (hMpos i).ne'
        have hr'pos : 0 < r' := by rw [hr'def]; exact pow_pos hr.1 _
        have hin : r' ∈ Set.Ioo (0 : ℝ) (R0 i) := ⟨hr'pos, lt_of_le_of_lt hr'le hrR0⟩
        have hpow : r' ^ Nf i = r ^ N := by rw [hr'def, ← pow_mul, hMN i]
        have hz' : mpoly (c i) (r' ^ Nf i) z = 0 := by rw [hpow]; exact hz
        exact (hR0root i r' hin z).mp hz'
    · -- `Fin k` is empty: the cover condition is vacuous.
      have hempty : ∀ i : Fin k, False := by
        intro i
        have h1 : (Finset.univ : Finset (Fin k)) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hk
        have h2 : i ∈ (∅ : Finset (Fin k)) := h1 ▸ Finset.mem_univ i
        exact Finset.notMem_empty i h2
      exact ⟨1, one_pos, fun r _ i => (hempty i).elim⟩

end Work.WilC4aAL
