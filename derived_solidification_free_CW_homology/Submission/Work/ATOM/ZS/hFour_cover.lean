import Mathlib
import Submission.Work.ATOM.ZS.HFour.Defs
import Submission.Work.ATOM.ZS.HFour.Helpers
import Submission.Work.ATOM.ZS.HFour.hFourCA_of_lt
import Submission.Work.ATOM.ZS.HFour.hFourCB_of_eq
import Submission.Work.ATOM.ZS.HFour.hFourCA_of_gt

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open OnePoint

namespace Work.ATOM.ZS

/-! ## The two degenerate cases of the cover -/

/-- **The case `tProj t = ∞` of the cover.**  If the point `t : T'` lies over `∞` then
`β t = pr₂ t` (`Work.ATOM.betaT_eq_pr₂T_of_infty`), so the two `ψ`-terms agree, and both
`φ`-terms are `∞` (`Work.ATOM.ZS.phiPFun_infty_right`): the point lies in `hFourCA S`. -/
lemma hFourCA_of_proj_infty (S : LightProfinite.{0}) [Infinite S] (w : ↥(hFourW S))
    (h : tProj S w.2 = (∞ : ℕ∪{∞})) : w ∈ hFourCA S := by
  have hb : betaT S w.2 = pr₂T S w.2 := betaT_eq_pr₂T_of_infty S w.2 h
  change psiFun S (w.1, pr₂T S w.2) = psiFun S (w.1, betaT S w.2) ∧
    phiPFun S (w.1, tProj S w.2) = phiPFun S (LightProfinite.shift w.1, tProj S w.2)
  refine ⟨?_, ?_⟩
  · rw [hb]
  · rw [h, phiPFun_infty_right, phiPFun_infty_right]

/-- **The case `k = ∞` of the cover.**  If the first coordinate of `w` is `∞` then both `ψ`-terms
are `∞` (`Work.ATOM.psiFun_infty`) and both `φ`-terms are `∞` (`shift ∞ = ∞`,
`Work.ATOM.phiPFun_infty_left`): the point lies in `hFourCA S`. -/
lemma hFourCA_of_k_infty (S : LightProfinite.{0}) [Infinite S] (w : ↥(hFourW S))
    (h : w.1 = (∞ : ℕ∪{∞})) : w ∈ hFourCA S := by
  change psiFun S (w.1, pr₂T S w.2) = psiFun S (w.1, betaT S w.2) ∧
    phiPFun S (w.1, tProj S w.2) = phiPFun S (LightProfinite.shift w.1, tProj S w.2)
  refine ⟨?_, ?_⟩
  · rw [h, psiFun_infty, psiFun_infty]
  · rw [h, shift_infty, phiPFun_infty_left]

/-- **The two closed pieces cover the space `(ℕ∪∞) × T'`.**

`Work.ATOM.ZS.hFourW S = (ℕ∪∞) ⊗ T' S` is the source of the closed-cover comparison for the
identity `h₄` (`Work.ATOM.m S ≫ Work.ATOM.G S = Work.ATOM.preShiftP ≫ Work.ATOM.FP S`), see
`Submission/Work/ATOM/ZS/HFour/Defs.lean`.  A point of `hFourW S` is a pair `(k,t)` with
`k : ℕ∪∞` and `t : T' = {(j,a_j) : j ∈ ℕ} ∪ {∞} × S`.

A point lies in `hFourCA S` iff `ψ₁ = ψ₂` and `φ₁ = φ₂`, and in `hFourCB S` iff `ψ₁ = φ₁` and
`ψ₂ = φ₂`, where `ψ₁(k,t) = ψ(k, pr₂ t)`, `ψ₂(k,t) = ψ(k, β t)`, `φ₁(k,t) = φ_P(k, tProj t)`,
`φ₂(k,t) = φ_P(k+1, tProj t)` (`Work.ATOM.ZS.hFourPsi1/2`, `hFourQ1/2`), `n(j) = lvl S j`.

Case analysis (`Work.ATOM.ZS.hFourPsi1_apply` etc. unfold the maps on a point):
* `tProj t = ∞` (so `t = (∞,u)`, `β t = pr₂ t = u`): `ψ₁ = ψ₂` and `φ₁ = φ₂ = ∞`
  (`Work.ATOM.phiPFun_infty_left`), so `hFourCA`;
* `k = ∞`: `ψ₁ = ψ₂ = ∞` (`Work.ATOM.psiFun_infty`), `φ₁ = φ₂ = ∞` (`shift ∞ = ∞`), so `hFourCA`;
* `tProj t = j ∈ ℕ`, so `t = (j, a_j)` (`Work.ATOM.mem_tSet_iff`, `Work.ATOM.tSet_second_eq`) and
  `β t = e_{n(j)-1} a_j` (if `n(j) ≥ 1`) or `s₀` (if `n(j) = 0`) (`Work.ATOM.betaFun_lvl`).
  Writing `n = lvl S j`:
  - `k < n`: `e_k (e_{n-1} a_j) = e_k a_j` (`Work.ATOM.e_comp`), so `ψ₁ = ψ₂`
    (`Work.ATOM.ZS.psiFun_dep`); `φ₁ = φ₂ = j` (`Work.ATOM.phiPFun_some_some_of_le`). `hFourCA`.
  - `k = n`: `ψ₁ = j` (`Work.ATOM.psiFun_some_eq` with `Work.ATOM.LevelData.e_lvl_a`) and
    `ψ₂ = ∞` (either `e_n (e_{n-1}a_j) = e_{n-1}a_j` has level `< n`, or `n = 0` and
    `β t = s₀ ∉ range a`; both via `Work.ATOM.psiFun_some_eq_infty`); `φ₁ = j`, `φ₂ = ∞`
    (`Work.ATOM.phiPFun_some_some_of_le`, `..._of_lt`). `hFourCB`.
  - `k > n`: `e_k a_j = a_j` has level `n ≠ k`, and `e_k (e_{n-1}a_j) = e_{n-1}a_j` has level
    `< k`, so `ψ₁ = ψ₂ = ∞` (`Work.ATOM.ZS.e_fix_of_mem_A_of_le`,
    `Work.ATOM.LevelData.lv_mem`, `Work.ATOM.LevelData.lv_le`, `Work.ATOM.psiFun_some_eq_infty`);
    `φ₁ = φ₂ = ∞` (`Work.ATOM.phiPFun_some_some_of_lt`). `hFourCA`. -/
theorem hFour_cover (S : LightProfinite.{0}) [Infinite S] :
    ∀ w : ↥(Work.ATOM.ZS.hFourW S),
      w ∈ Work.ATOM.ZS.hFourCA S ∨ w ∈ Work.ATOM.ZS.hFourCB S := by
  intro w
  -- the fibre of `tProj` over `∞` or over a finite index `j`
  rcases eq_or_ne (tProj S w.2) (∞ : ℕ∪{∞}) with hinf | hfin
  · exact Or.inl (hFourCA_of_proj_infty S w hinf)
  · obtain ⟨j, hj⟩ := OnePoint.ne_infty_iff_exists.mp hfin
    have hj' : tProj S w.2 = ((j : ℕ) : ℕ∪{∞}) := hj.symm
    -- the first coordinate `k` is `∞` or a finite `m`
    rcases eq_or_ne w.1 (∞ : ℕ∪{∞}) with hkinf | hkfin
    · exact Or.inl (hFourCA_of_k_infty S w hkinf)
    · obtain ⟨m, hm⟩ := OnePoint.ne_infty_iff_exists.mp hkfin
      have hm' : w.1 = ((m : ℕ) : ℕ∪{∞}) := hm.symm
      -- compare `k = m` with `n(j)`
      rcases lt_trichotomy m (lvl S j) with hlt | heq | hgt
      · exact Or.inl (HFour.hFourCA_of_lt S w hm' hj' hlt)
      · exact Or.inr (HFour.hFourCB_of_eq S w hm' hj' heq)
      · exact Or.inl (HFour.hFourCA_of_gt S w hm' hj' hgt)

end Work.ATOM.ZS
