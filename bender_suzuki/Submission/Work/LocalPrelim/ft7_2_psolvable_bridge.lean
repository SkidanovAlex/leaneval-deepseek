import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.pCoreSeries_two
import Submission.Work.Fitting.piCore_isPiNat
import Submission.Work.Fitting.isPSolvable_subgroup
import Submission.Work.HallHigman.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Bridge between the two notions of `p`-solvability

`Work.Fitting.IsPSolvable p G` says that the upper `p`-series
`1 ≤ O_{p'}(G) ≤ O_{p',p}(G) ≤ ...` of `G` reaches `G`.
`Work.HallHigman.IsPSolvable p G` says that `G` possesses *some* normal series all of whose
factors are `p`-groups or `p'`-groups.

The upper `p`-series is such a series: its `n`-th factor is
`O_{π_n}(G/O_{π_0..π_{n-1}}(G))` where `π_n` is `p'` for even `n` and `p` for odd `n`, hence a
`p'`-group (even `n`) or a `p`-group (odd `n`).  So the Fitting notion implies the Hall–Higman
notion; the converse is `Work.Fitting.isPSolvable_of_hallHigman`.

The one fact proved here is that the factor `O_{n+1}(G)/O_n(G)` of the upper `p`-series is a
`π_n`-group (`pCoreSeries_factor_index_isPiNat`); the two notions of `p`-solvability then agree
by taking the upper `p`-series as the normal series witnessing `Work.HallHigman.IsPSolvable`.
-/

set_option linter.style.haveILetI false

noncomputable section

open Classical

namespace Work.LocalPrelim

/-- **The factors of the upper `p`-series are `π`-groups.**  The quotient
`O_{n+1}(G)/O_n(G)` has order a `π`-number, where `π = stepPi p n` is `(· ≠ p)` for even `n`
and `(· = p)` for odd `n`.

Indeed `O_{n+1}(G)` is the preimage in `G` of `O_π(G/O_n(G))` (`pCoreSeries_succ`), and pulling
this back along the quotient map `G →* G/O_n(G)` restricted to `O_{n+1}(G)` identifies the
factor with `O_π(G/O_n(G))` (first isomorphism theorem), which is a `π`-group by
`piCore_isPiNat`. -/
theorem pCoreSeries_factor_index_isPiNat (p : ℕ) (G : Type*) [Group G] [Finite G] (n : ℕ) :
    Work.Fitting.IsPiNat (Work.Fitting.stepPi p n)
      ((Work.Fitting.pCoreSeries p G n).subgroupOf
        (Work.Fitting.pCoreSeries p G (n + 1))).index := by
  haveI : (Work.Fitting.pCoreSeries p G n).Normal := Work.Fitting.pCoreSeries_normal p G n
  -- The restriction of the quotient map `G →* G ⧸ O_n(G)` to the factor `O_{n+1}(G)`.
  set φ : ↥(Work.Fitting.pCoreSeries p G (n + 1)) →* (G ⧸ Work.Fitting.pCoreSeries p G n) :=
    (QuotientGroup.mk' (Work.Fitting.pCoreSeries p G n)).comp
      (Work.Fitting.pCoreSeries p G (n + 1)).subtype with hφdef
  -- Its image is `O_π(G ⧸ O_n(G))`: the definition of `O_{n+1}(G)` makes `O_{n+1}(G)` the
  -- preimage of `O_π(G ⧸ O_n(G))`, and `Subgroup.map_comap_eq_self_of_surjective` removes the
  -- preimage.
  have hφrange : φ.range =
      Work.Fitting.piCore (Work.Fitting.stepPi p n) (G ⧸ Work.Fitting.pCoreSeries p G n) := by
    rw [hφdef, MonoidHom.range_comp, Subgroup.range_subtype, Work.Fitting.pCoreSeries_succ,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
    rfl
  -- Its kernel is the factor itself.
  have hker : φ.ker = (Work.Fitting.pCoreSeries p G n).subgroupOf
      (Work.Fitting.pCoreSeries p G (n + 1)) := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφdef, MonoidHom.comp_apply,
      Subgroup.coe_subtype, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  -- Hence the index of the factor is the order of `O_π(G ⧸ O_n(G))`.
  have hcard : ((Work.Fitting.pCoreSeries p G n).subgroupOf
      (Work.Fitting.pCoreSeries p G (n + 1))).index =
      Nat.card ↥(Work.Fitting.piCore (Work.Fitting.stepPi p n)
        (G ⧸ Work.Fitting.pCoreSeries p G n)) := by
    rw [← hker]
    calc (φ.ker).index
        = Nat.card (↥(Work.Fitting.pCoreSeries p G (n + 1)) ⧸ φ.ker) :=
          Subgroup.index_eq_card _
      _ = Nat.card ↥φ.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
      _ = Nat.card ↥(Work.Fitting.piCore (Work.Fitting.stepPi p n)
            (G ⧸ Work.Fitting.pCoreSeries p G n)) := by rw [hφrange]
  rw [hcard]
  exact Work.Fitting.piCore_isPiNat _ (Work.Fitting.stepPi p n)

/-- `p`-solvability in the sense of `Work.Fitting` (the upper `p`-series reaching `G`) implies
`p`-solvability in the sense of `Work.HallHigman` (existence of a normal series whose factors
are `p`-groups or `p'`-groups).

The witnessing series is the upper `p`-series itself; the factor conditions are exactly the
statement that its factors are `π`-groups, whence the index of every factor is prime to `p`
(for even steps) or a power of `p` (for odd steps). -/
theorem ft7_2_psolvable_bridge {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    (h : Work.Fitting.IsPSolvable p G) : Work.HallHigman.IsPSolvable p G := by
  obtain ⟨N, hN⟩ := h.out
  refine ⟨N, fun i : Fin (N + 1) => Work.Fitting.pCoreSeries p G i.val, ?_, ?_, ?_, ?_⟩
  · -- the series starts at `⊥`
    show Work.Fitting.pCoreSeries p G (⟨0, Nat.succ_pos N⟩ : Fin (N + 1)).val = ⊥
    rw [Work.Fitting.pCoreSeries_zero]
  · -- the series ends at `⊤`
    show Work.Fitting.pCoreSeries p G (Fin.last N).val = ⊤
    rw [Fin.val_last]
    exact hN
  · -- every term is normal
    intro i
    exact Work.Fitting.pCoreSeries_normal p G i.val
  · -- the index of each factor is prime to `p`, or a power of `p`
    intro i
    have hpi := pCoreSeries_factor_index_isPiNat p G i.val
    simp only [Fin.val_castSucc, Fin.val_succ]
    by_cases hev : Even i.val
    · -- even step: `π = (· ≠ p)`, so the index is not divisible by `p`
      left
      intro hpd
      have hstep : Work.Fitting.stepPi p i.val = (fun q => q ≠ p) := by
        funext q
        simp only [Work.Fitting.stepPi]
        rw [ite_eq_left hev]
      rw [hstep] at hpi
      exact (hpi p hp hpd) rfl
    · -- odd step: `π = (· = p)`, so the index is a power of `p`
      right
      have hstep : Work.Fitting.stepPi p i.val = (fun q => q = p) := by
        funext q
        simp only [Work.Fitting.stepPi]
        rw [ite_eq_right hev]
      rw [hstep] at hpi
      exact (Work.Fitting.isPiNat_prime_iff hp).mp hpi

end Work.LocalPrelim
