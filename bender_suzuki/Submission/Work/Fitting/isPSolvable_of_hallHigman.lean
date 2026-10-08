import Mathlib
import Submission.Work.HallHigman.Basic
import Submission.Work.Fitting.isPSolvable_subgroup
import Submission.Work.Fitting.pCoreSeries_mono

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

open Classical

set_option linter.style.haveILetI false

namespace Work.Fitting

variable {G : Type*} [Group G] {p : ℕ}

/-- At an even index the `π`-set `stepPi p n` selects the `p'`-numbers. -/
lemma stepPi_even (p n : ℕ) : stepPi p (2 * n) = (fun q => q ≠ p) := by
  funext q
  simp only [stepPi]
  rw [ite_eq_left (even_two_mul n)]

/-- At an odd index the `π`-set `stepPi p n` selects the `p`-numbers. -/
lemma stepPi_odd (p n : ℕ) : stepPi p (2 * n + 1) = (fun q => q = p) := by
  funext q
  simp only [stepPi]
  rw [ite_eq_right]
  rintro ⟨k, hk⟩
  omega

/-- `p`-solvability in the sense of `Work.HallHigman` (existence of a normal series whose
factors are `p`-groups or `p'`-groups, `Work.HallHigman.IsPSolvable`) implies `p`-solvability in
the sense of `Work.Fitting` (the class `Work.Fitting.IsPSolvable`, i.e. the upper `p`-series
`1 ≤ O_{p'}(G) ≤ O_{p',p}(G) ≤ ...` reaching `G`).

Proof sketch. Let `⊥ = f 0, f 1, ..., f n = ⊤` be the `Work.HallHigman` series (`f i` normal in
`G` for all `i`), and write `G_k = Work.Fitting.pCoreSeries p G k`. Prove by induction on
`i : Fin (n+1)` that `f i ≤ G_{2 * i.val}`. In the step, put `N = f i.castSucc ⊓ f i.succ` and
`M = f i.succ`; the hypothesis on the `i`-th factor says that the index of `N` in `M`, which is
`((f i.castSucc).subgroupOf (f i.succ)).index = N.relIndex M` (using that `Subgroup.relIndex`
*is defined* as `(H.subgroupOf K).index`, together with `Subgroup.inf_relIndex_right`), is
either coprime to `p` or a power of `p`. In the coprime case apply
`Work.Fitting.le_pCoreSeries_succ` at index `2 * i.val` (where
`Work.Fitting.stepPi p (2*i) = (· ≠ p)`, the `IsPiNat` hypothesis being `¬ p ∣ N.relIndex M`)
to get `M ≤ G_{2i+1}` and then `M ≤ G_{2i+2}` by `Work.Fitting.pCoreSeries_le_succ`; in the
`p`-power case apply the same result at index `2 * i.val + 1` (where
`Work.Fitting.stepPi p (2i+1) = (· = p)`, using `Work.Fitting.isPiNat_prime_iff hp`) with
`N ≤ f i.castSucc ≤ G_{2i} ≤ G_{2i+1}`. At `i = Fin.last n` this gives `⊤ ≤ G_{2n}`.

Note the Hall-Higman series need not be a chain; passing `N ⊓ M` instead of `N` to
`Work.Fitting.le_pCoreSeries_succ` (whose `N ≤ M` hypothesis is unused) restores it, and
`Subgroup.inf_relIndex_right` shows the relative index is unchanged. -/
theorem isPSolvable_of_hallHigman {p : ℕ} {G : Type*} [Group G] [Finite G] (hp : p.Prime)
    (h : Work.HallHigman.IsPSolvable p G) : Work.Fitting.IsPSolvable p G := by
  obtain ⟨n, f, hbot, htop, hnorm, hstep⟩ := h
  -- The relative index of the `i`-th factor of the Hall-Higman series, computed inside
  -- the chain `f i.castSucc ⊓ f i.succ ≤ f i.succ`.
  have hrel : ∀ i : Fin n,
      (f i.castSucc ⊓ f i.succ).relIndex (f i.succ) =
        ((f i.castSucc).subgroupOf (f i.succ)).index := by
    intro i
    rw [Subgroup.inf_relIndex_right]
    rfl
  -- `f i ≤ O_{2i}(G)` for every `i`.
  have key : ∀ i : Fin (n + 1), f i ≤ pCoreSeries p G (2 * i.val) := by
    refine Fin.induction (n := n) (motive := fun i => f i ≤ pCoreSeries p G (2 * i.val))
      ?_ ?_
    · have hf0 : f (0 : Fin (n + 1)) = ⊥ := by simpa using hbot
      rw [hf0]
      exact bot_le
    · intro i ih
      haveI : (f i.castSucc).Normal := hnorm i.castSucc
      haveI : (f i.succ).Normal := hnorm i.succ
      have hNn : (f i.castSucc ⊓ f i.succ).Normal := inferInstance
      rcases hstep i with hcop | ⟨k, hk⟩
      · -- the `i`-th factor has order prime to `p`
        have hpi : IsPiNat (stepPi p (2 * i.val))
            ((f i.castSucc ⊓ f i.succ).relIndex (f i.succ)) := by
          rw [stepPi_even]
          intro q hq hd hqp
          exact hcop (by rw [← hrel i]; simpa [hqp] using hd)
        have hle1 : f i.succ ≤ pCoreSeries p G (2 * i.val + 1) :=
          le_pCoreSeries_succ p G (2 * i.val) hNn (hnorm i.succ) inf_le_right
            (le_trans inf_le_left ih) hpi
        calc f i.succ ≤ pCoreSeries p G (2 * i.val + 1) := hle1
          _ ≤ pCoreSeries p G (2 * i.val + 1 + 1) := pCoreSeries_le_succ p G (2 * i.val + 1)
          _ = pCoreSeries p G (2 * ↑i.succ) := by
              rw [Fin.val_succ,
                show 2 * ↑i + 1 + 1 = 2 * (↑i + 1) from by ring]
      · -- the `i`-th factor is a `p`-group
        have hpi : IsPiNat (stepPi p (2 * i.val + 1))
            ((f i.castSucc ⊓ f i.succ).relIndex (f i.succ)) := by
          rw [stepPi_odd]
          exact (isPiNat_prime_iff hp).mpr ⟨k, by rw [hrel i]; exact hk⟩
        have hle1 : f i.succ ≤ pCoreSeries p G (2 * i.val + 1 + 1) :=
          le_pCoreSeries_succ p G (2 * i.val + 1) hNn (hnorm i.succ) inf_le_right
            (le_trans inf_le_left
              (le_trans ih (pCoreSeries_le_succ p G (2 * i.val)))) hpi
        calc f i.succ ≤ pCoreSeries p G (2 * i.val + 1 + 1) := hle1
          _ = pCoreSeries p G (2 * ↑i.succ) := by
              rw [Fin.val_succ,
                show 2 * ↑i + 1 + 1 = 2 * (↑i + 1) from by ring]
  have hlast := key (Fin.last n)
  rw [Fin.val_last, htop] at hlast
  exact ⟨2 * n, top_le_iff.mp hlast⟩

end Work.Fitting
