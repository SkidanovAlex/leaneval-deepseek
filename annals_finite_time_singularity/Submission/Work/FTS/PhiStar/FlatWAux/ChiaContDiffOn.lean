import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.MomentChia
import Submission.Work.FTS.PhiStar.FlatWAux.MomentChiaAux.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.MomentChiaAux.CoefSummable
import Submission.Work.FTS.PhiStar.FlatWAux.MomentChiaAux.SeriesOde
import Submission.Work.FTS.PhiStar.FlatWAux.MomentChiaAux.LzeroBootstrap
import Submission.Work.FTS.PhiStar.FlatWAux.MomentChiaAux.BmodeExpansionSelf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

open scoped Real Topology BigOperators ContDiff
open MeasureTheory Set Filter

/-- **The `Lzero`-identity of two consecutive angular profiles.**

`Work.Elliptic.Lzero (fun _ θ' => f θ') 0 θ = -f''(θ) + (tan θ·f)'(θ) - 6 f(θ)`, and on
`(0, π/2)` one has

  `Lzero (chia ψ (j+1)) = chia ψ j`,

i.e. the resummed angular profiles are successively the `Lzero`-images of one another.  This is
the identity that lets `MomentChiaAux.LzeroBootstrap` upgrade the (finitely many) angular
derivatives of `MomentChia` to derivatives of every order.

The proof is the one used in `MomentChia`: on `(0, π/2)` the profile `chia ψ (j+1)` is the
`eFam`-series with coefficients `bco ψ (j+1) m = bmode m ψ·λ_m^{-(j+1)}`
(`MomentChiaAux.chia_eq_tsum_bco`), `Lzero` acts on that series as
`MomentChiaAux.SeriesOde` describes, and the resulting source series
`Σ_m (bco ψ (j+1) m · λ_m) e_m` is `chia ψ j` because `bco ψ (j+1) m·λ_m = bco ψ j m` for
`m ≥ 1` (`MomentChiaAux.bco_succ_mul_lam`) while the `m = 0` term vanishes on both sides
(`λ_0 = 0`, resp. `bmode 0 ψ = 0` from the vanishing moment); for `j = 0` the source is `ψ`
itself, by the expansion `MomentChiaAux.BmodeExpansionSelf`. -/
lemma chia_Lzero_succ (ψ : ℝ → ℝ)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * (2 * (m : ℝ) + 1))
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioo 0 (Real.pi / 2)))
    (hbdd : ∃ M : ℝ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |ψ θ| ≤ M)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0) :
    ∀ j : ℕ, j + 1 ≤ J → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Elliptic.Lzero (fun _ θ' => chia ψ (j + 1) θ') 0 θ = chia ψ j θ := by
  intro j _ θ hθ
  have hj1 : 1 ≤ j + 1 := by omega
  obtain ⟨hcs, hds⟩ := MomentChiaAux.CoefSummable ψ hdec (j + 1) hj1
  obtain ⟨-, hLzero⟩ := MomentChiaAux.SeriesOde (MomentChiaAux.bco ψ (j + 1))
    (fun m => MomentChiaAux.bco ψ (j + 1) m * Work.FTS.PhiStar.Gegenbauer.lam m)
    (fun m => rfl) hcs hds
  have hEqOn : ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
      chia ψ (j + 1) θ' = ∑' m : ℕ,
        MomentChiaAux.bco ψ (j + 1) m * Work.FTS.PhiStar.Gegenbauer.eFam m θ' :=
    fun θ' hθ' => MomentChiaAux.chia_eq_tsum_bco ψ hj1 hθ'
  have hL : Work.Elliptic.Lzero (fun _ θ' => chia ψ (j + 1) θ') 0 θ
      = ∑' m : ℕ, (MomentChiaAux.bco ψ (j + 1) m * Work.FTS.PhiStar.Gegenbauer.lam m)
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
    refine (MomentChiaAux.Lzero_congr_of_eventuallyEq ?_).trans (hLzero θ hθ)
    exact Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨Set.Ioo 0 (Real.pi / 2), isOpen_Ioo.mem_nhds hθ, fun θ' hθ' => hEqOn θ' hθ'⟩
  rw [hL]
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    have hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0 :=
      MomentChiaAux.bmode_zero_of_moment' hmom
    have htsum : (∑' m : ℕ, (MomentChiaAux.bco ψ 1 m * Work.FTS.PhiStar.Gegenbauer.lam m)
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        = ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
      refine tsum_congr (fun m => ?_)
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simp only [MomentChiaAux.bco_apply_zero ψ le_rfl, zero_mul, hb0]
      · rw [MomentChiaAux.bco_one_mul_lam (ψ := ψ) hm]
    rw [htsum]
    exact (MomentChiaAux.BmodeExpansionSelf ψ hdec hgr (hsm 0).continuousOn hbdd hmom θ hθ).trans
      (chia_zero (MomentChiaAux.s2_ne_zero_of_mem_Ioo hθ)).symm
  · have htsum : (∑' m : ℕ, (MomentChiaAux.bco ψ (j + 1) m * Work.FTS.PhiStar.Gegenbauer.lam m)
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        = ∑' m : ℕ, MomentChiaAux.bco ψ j m * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
      refine tsum_congr (fun m => ?_)
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simp only [MomentChiaAux.bco_apply_zero ψ hj1, zero_mul,
          MomentChiaAux.bco_apply_zero ψ hjpos]
      · rw [MomentChiaAux.bco_succ_mul_lam (ψ := ψ) (j := j) hm]
    rw [htsum, ← MomentChiaAux.chia_eq_tsum_bco ψ hjpos hθ]

theorem ChiaContDiffOn (ψ : ℝ → ℝ)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * (2 * (m : ℝ) + 1))
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioo 0 (Real.pi / 2)))
    (hbdd : ∃ M : ℝ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |ψ θ| ≤ M)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0) :
    ∀ (j : ℕ), j ≤ Work.FTS.PhiStar.FlatWAux.J → ∀ (n : ℕ),
      ContDiffOn ℝ n (Work.FTS.PhiStar.FlatWAux.chia ψ j) (Set.Ioo 0 (Real.pi / 2)) := by
  -- `MomentChia` already gives `C^8`, which furnishes all the low orders
  obtain ⟨hC8, -, -⟩ := MomentChia ψ hdec hgr hsm hbdd hmom
  have hOde := chia_Lzero_succ ψ hdec hgr hsm hbdd hmom
  -- and the ODE `Lzero (chia ψ (j+1)) = chia ψ j` unlocks `LzeroBootstrap`
  have main : ∀ n : ℕ, ∀ j : ℕ, j ≤ J →
      ContDiffOn ℝ n (chia ψ j) (Set.Ioo 0 (Real.pi / 2)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro j hjJ
      by_cases hn : n ≤ 8
      · exact (hC8 j hjJ).of_le (by exact_mod_cast hn)
      · rcases Nat.eq_zero_or_pos j with hj0 | hjpos
        · -- `j = 0`: `chia ψ 0 = ψ` on the open interval
          subst hj0
          exact (hsm n).congr
            (fun θ hθ => chia_zero (MomentChiaAux.s2_ne_zero_of_mem_Ioo hθ))
        · -- `j = j' + 1`: one more derivative from the ODE
          obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
          have hj'J : j' + 1 ≤ J := by omega
          have hf : ContDiffOn ℝ (n - 1) (chia ψ (j' + 1)) (Set.Ioo 0 (Real.pi / 2)) :=
            ih (n - 1) (by omega) (j' + 1) (by omega)
          have hh : ContDiffOn ℝ ((n - 1) - 1) (chia ψ j') (Set.Ioo 0 (Real.pi / 2)) :=
            ih ((n - 1) - 1) (by omega) j' (by omega)
          have hb := MomentChiaAux.LzeroBootstrap (m := n - 1) (by omega) hf hh
            (fun θ hθ => hOde j' hj'J θ hθ)
          have hcast : (((n - 1 : ℕ)) : ℕ∞ω) + 1 = (n : ℕ∞ω) := by
            have h : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
            exact_mod_cast h
          rw [← hcast]
          exact hb
  intro j hjJ n
  exact main n j hjJ

end Work.FTS.PhiStar.FlatWAux
