/-
# Continuity of the delay profiles `profC` on their recursion domains

`APSwitchUpper.profC` is the delay-difference family of the Rosser–Iwaniec linear sieve.  Each
member is a *piecewise* function whose nontrivial piece is an integral with a parameter in the
integration bound, so continuity is not immediate.  The classical regularity statement is

* `profC k` is continuous on `[1, ∞)` for **even** `k`;
* `profC k` is continuous on `[2, ∞)` for **odd** `k`;

(the asymmetry is exactly the parity of the clamp `max s 3` in `profC_succ`: an even recursion
index — an odd successor — clamps at `3`, so the lower limit of the inner integral is bounded
below by `2`; an odd recursion index has lower limit `s ≥ 2` and integrates `profC k` on
`[1, ∞)`).  This is the statement proved here.

The two ingredients are

* `continuousOn_primitive_Ici`: the primitive `x ↦ ∫_a^x f` of a function continuous on
  `[a, ∞)` is continuous there (gluing `intervalIntegral.continuousOn_primitive_interval'`
  over the compacts `[a, N]` with `N → ∞`);
* the `u`-form of the recursion (`APSwitchUpper.profC_eq_integral_even/odd`), which turns
  `profC (k+1) s` into `(1/s)·∫_{ℓ(s)}^{k+3} profC k` with `ℓ(s) = max (s-1) 2` (odd `k`) or
  `ℓ(s) = s - 1` (even `k`), an expression that is manifestly continuous in `s` once
  `profC k` is.
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_intervalIntegrable
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_integral_form

open MeasureTheory
open scoped Topology

namespace Work.NumberTheory.Chen.ApSumTenth

open Work.NumberTheory.Chen.APSwitchUpper

noncomputable section

/-- **Primitive of a function continuous on a half-line.**  If `f` is continuous on `[a, ∞)`,
so is `x ↦ ∫_a^x f`.  Proof: on each `[a, N]` this is Mathlib's
`intervalIntegral.continuousOn_primitive_interval'`; the sets `[a, N]` exhaust `[a, ∞)` and
each is a neighbourhood of its points *relative to* `[a, ∞)`. -/
private lemma continuousOn_primitive_Ici {a : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ici a)) :
    ContinuousOn (fun x : ℝ => ∫ t in a..x, f t) (Set.Ici a) := by
  intro x hx
  have hax : a ≤ x := hx
  obtain ⟨N, hN⟩ := exists_nat_gt x
  have haN : a ≤ (N : ℝ) := le_trans hax (le_of_lt hN)
  have hfIcc : ContinuousOn f (Set.Icc a (N : ℝ)) := hf.mono (fun y hy => hy.1)
  have hfuIcc : ContinuousOn f (Set.uIcc a (N : ℝ)) := by
    rw [Set.uIcc_of_le haN]; exact hfIcc
  have hInt : IntervalIntegrable f volume a (N : ℝ) := hfuIcc.intervalIntegrable
  have hcont : ContinuousOn (fun y : ℝ => ∫ t in a..y, f t) (Set.uIcc a (N : ℝ)) :=
    intervalIntegral.continuousOn_primitive_interval' hInt (by
      rw [Set.uIcc_of_le haN]; exact ⟨le_rfl, haN⟩)
  have hxmem : x ∈ Set.uIcc a (N : ℝ) := by
    rw [Set.uIcc_of_le haN]; exact ⟨hax, le_of_lt hN⟩
  have hmem : Set.uIcc a (N : ℝ) ∈ 𝓝[Set.Ici a] x := by
    have hIic : Set.Iic (N : ℝ) ∈ 𝓝 x := by
      rw [← mem_interior_iff_mem_nhds, interior_Iic]; exact hN
    have hset : Set.uIcc a (N : ℝ) = Set.Ici a ∩ Set.Iic (N : ℝ) := by
      rw [Set.uIcc_of_le haN]
      ext y; simp [Set.mem_Icc, Set.mem_Ici, Set.mem_Iic]
    rw [hset]
    exact inter_mem_nhdsWithin _ hIic
  exact (hcont x hxmem).mono_of_mem_nhdsWithin hmem

/-- Base case: `profC 0 s = (3 − s)/s` on `[1,3]` and `0` on `[3,∞)` — the two pieces agree
at `s = 3`, so `profC 0` is continuous on `[1, ∞)`. -/
private theorem profC_zero_continuousOn :
    ContinuousOn (fun s : ℝ => profC 0 s) (Set.Ici (1 : ℝ)) := by
  have h1 : ContinuousOn (fun s : ℝ => profC 0 s) (Set.Icc (1 : ℝ) 3) :=
    ContinuousOn.congr (f := fun s : ℝ => (3 - s) / s)
      ((continuousOn_const.sub continuousOn_id).div continuousOn_id
        (fun s hs => by linarith [hs.1]))
      (fun s hs => by rw [profC_zero, if_pos ⟨hs.1, hs.2⟩])
  have h2 : ContinuousOn (fun s : ℝ => profC 0 s) (Set.Ici (3 : ℝ)) :=
    ContinuousOn.congr (f := fun _ : ℝ => (0 : ℝ)) continuousOn_const
      (fun s hs => by
        rw [profC_zero]
        by_cases h : 1 ≤ s ∧ s ≤ 3
        · rw [if_pos h]
          have hs3 : s = 3 := le_antisymm h.2 hs
          rw [hs3]; norm_num
        · rw [if_neg h])
  have hglue := ContinuousOn.union_of_isClosed h1 h2 isClosed_Icc isClosed_Ici
  have hunion : Set.Icc (1 : ℝ) 3 ∪ Set.Ici (3 : ℝ) = Set.Ici (1 : ℝ) := by
    rw [Set.Icc_union_Ici (show (3 : ℝ) ≤ max 1 3 by norm_num)]
    norm_num
  simpa [hunion] using hglue

/-- **Induction step, even successor.**  If `k` is odd and `profC k` is continuous on `[2, ∞)`,
then `profC (k+1)` is continuous on `[1, ∞)`: on `[1,∞)` it is
`(1/s)·∫_{max (s−1) 2}^{k+3} profC k`, i.e. a constant minus the primitive of `profC k`
evaluated at the continuous function `s ↦ max (s−1) 2`, divided by `s`. -/
private theorem profC_succ_continuousOn_of_odd {k : ℕ} (hk : k % 2 = 1)
    (h : ContinuousOn (fun u : ℝ => profC k u) (Set.Ici (2 : ℝ))) :
    ContinuousOn (fun s : ℝ => profC (k + 1) s) (Set.Ici (1 : ℝ)) := by
  have hF : ContinuousOn (fun x : ℝ => ∫ t in (2 : ℝ)..x, profC k t) (Set.Ici (2 : ℝ)) :=
    continuousOn_primitive_Ici h
  have hmax : ContinuousOn (fun s : ℝ => max (s - 1) 2) (Set.Ici (1 : ℝ)) :=
    ((continuous_id.sub continuous_const).max continuous_const).continuousOn
  have hmaps : Set.MapsTo (fun s : ℝ => max (s - 1) 2) (Set.Ici (1 : ℝ)) (Set.Ici (2 : ℝ)) :=
    fun s _ => by rw [Set.mem_Ici]; exact le_max_right _ _
  have hcomp : ContinuousOn (fun s : ℝ => ∫ t in (2 : ℝ)..max (s - 1) 2, profC k t)
      (Set.Ici (1 : ℝ)) := hF.comp hmax hmaps
  have hG : ContinuousOn
      (fun s : ℝ =>
        ((∫ t in (2 : ℝ)..((k : ℝ) + 3), profC k t)
          - ∫ t in (2 : ℝ)..max (s - 1) 2, profC k t) / s)
      (Set.Ici (1 : ℝ)) :=
    (continuousOn_const.sub hcomp).div continuousOn_id
      (fun s hs => by have h1s : (1 : ℝ) ≤ s := hs; linarith)
  refine hG.congr ?_
  intro s hs
  dsimp only
  have hs1 : (1 : ℝ) ≤ s := hs
  rw [profC_eq_integral_even k hk s hs1]
  congr 1
  exact (intervalIntegral.integral_interval_sub_left (profC_intervalIntegrable k 2 ((k : ℝ) + 3))
    (profC_intervalIntegrable k 2 (max (s - 1) 2))).symm

/-- **Induction step, odd successor.**  If `k` is even and `profC k` is continuous on `[1, ∞)`,
then `profC (k+1)` is continuous on `[2, ∞)`: on `[2,∞)` it is
`(1/s)·∫_{s−1}^{k+3} profC k`, i.e. a constant minus the primitive of `profC k` at `s − 1`,
divided by `s`. -/
private theorem profC_succ_continuousOn_of_even {k : ℕ} (hk : k % 2 = 0)
    (h : ContinuousOn (fun u : ℝ => profC k u) (Set.Ici (1 : ℝ))) :
    ContinuousOn (fun s : ℝ => profC (k + 1) s) (Set.Ici (2 : ℝ)) := by
  have hF : ContinuousOn (fun x : ℝ => ∫ t in (1 : ℝ)..x, profC k t) (Set.Ici (1 : ℝ)) :=
    continuousOn_primitive_Ici h
  have hsub : ContinuousOn (fun s : ℝ => s - 1) (Set.Ici (2 : ℝ)) :=
    (continuous_id.sub continuous_const).continuousOn
  have hmaps : Set.MapsTo (fun s : ℝ => s - 1) (Set.Ici (2 : ℝ)) (Set.Ici (1 : ℝ)) :=
    fun s hs => by have h2s : (2 : ℝ) ≤ s := hs; rw [Set.mem_Ici]; linarith
  have hcomp : ContinuousOn (fun s : ℝ => ∫ t in (1 : ℝ)..(s - 1), profC k t)
      (Set.Ici (2 : ℝ)) := hF.comp hsub hmaps
  have hG : ContinuousOn
      (fun s : ℝ =>
        ((∫ t in (1 : ℝ)..((k : ℝ) + 3), profC k t)
          - ∫ t in (1 : ℝ)..(s - 1), profC k t) / s)
      (Set.Ici (2 : ℝ)) :=
    (continuousOn_const.sub hcomp).div continuousOn_id
      (fun s hs => by have h2s : (2 : ℝ) ≤ s := hs; linarith)
  refine hG.congr ?_
  intro s hs
  dsimp only
  have hs2 : (2 : ℝ) ≤ s := hs
  rw [profC_eq_integral_odd k hk s hs2]
  congr 1
  exact (intervalIntegral.integral_interval_sub_left (profC_intervalIntegrable k 1 ((k : ℝ) + 3))
    (profC_intervalIntegrable k 1 (s - 1))).symm

theorem profC_continuousOn :
    (∀ k : ℕ, k % 2 = 0 →
      ContinuousOn (fun u : ℝ => Work.NumberTheory.Chen.APSwitchUpper.profC k u)
        (Set.Ici (1 : ℝ))) ∧
    (∀ k : ℕ, k % 2 = 1 →
      ContinuousOn (fun u : ℝ => Work.NumberTheory.Chen.APSwitchUpper.profC k u)
        (Set.Ici (2 : ℝ))) := by
  have key : ∀ k : ℕ,
      (k % 2 = 0 → ContinuousOn (fun u : ℝ => profC k u) (Set.Ici (1 : ℝ))) ∧
      (k % 2 = 1 → ContinuousOn (fun u : ℝ => profC k u) (Set.Ici (2 : ℝ))) := by
    intro k
    induction k with
    | zero => exact ⟨fun _ => profC_zero_continuousOn, fun h => absurd h (by norm_num)⟩
    | succ k ih =>
        refine ⟨?_, ?_⟩
        · intro hk
          have hk1 : k % 2 = 1 := by omega
          exact profC_succ_continuousOn_of_odd hk1 (ih.2 hk1)
        · intro hk
          have hk0 : k % 2 = 0 := by omega
          exact profC_succ_continuousOn_of_even hk0 (ih.1 hk0)
  exact ⟨fun k hk => (key k).1 hk, fun k hk => (key k).2 hk⟩

end

end Work.NumberTheory.Chen.ApSumTenth
