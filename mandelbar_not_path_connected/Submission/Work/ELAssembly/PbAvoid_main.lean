import Mathlib
import Submission.Work.ELAssembly.PbAvoid_core
import Submission.Work.ELAssembly.PbAvoid_portrait
import Submission.Work.ELAssembly.PbAvoid_arithQ
import Submission.Work.ELAssembly.PbAvoid_arithD
import Submission.Work.ELAssembly.PbAvoid_cycle
import Submission.Work.ELAssembly.Qmem_of
import Submission.Work.ELAssembly.Dmem_of
import Submission.Work.ELAssembly.Qne_of
import Submission.Work.ELAssembly.armChainInputs_of
import Submission.Work.ELAssembly.Z1
import Submission.Work.ELAssembly.Defs
import Submission.Work.ELNest.Setup
import Submission.Work.FinalFix.Nonreal
import Submission.Work.ELTop.RigInput

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## Arithmetic of the cyclic arc length -/

/-- The cyclic length `arcLen a b` only depends on `b - a` modulo `1`, in particular
`arcLen a (b + 1) = arcLen a b`. -/
private lemma arcLen_succ_right (a b : ℝ) :
    Work.EL.arcLen a (b + 1) = Work.EL.arcLen a b := by
  rw [Work.EL.arcLen, Work.EL.arcLen]
  have h : b + 1 - a = (b - a) + ((1 : ℤ) : ℝ) := by push_cast; ring
  rw [h, Int.fract_add_intCast]

/-! ## The level-`0` arm angles against the wake angles -/

private lemma armA1_zero_wakeLo : Work.ELNest.armA1 0 = Work.EL.wakeLo 0 := by
  rw [armA1_zero_angle]; rfl

private lemma armA2_zero_wakeHi : Work.ELNest.armA2 0 = Work.EL.wakeHi 0 := by
  rw [armA2_zero_angle]; rfl

private lemma armB1_zero_wakeLo : Work.ELNest.armB1 0 = Work.EL.wakeLo 2 := by
  rw [armB1_zero_angle]; rfl

private lemma armB2_zero_wakeHi : Work.ELNest.armB2 0 = Work.EL.wakeHi 2 := by
  rw [armB2_zero_angle]; rfl

private lemma armC1_zero_wakeLo : Work.ELNest.armC1 0 = Work.EL.wakeLo 4 := by
  rw [armC1_zero_angle]; rfl

private lemma armC2_zero_succ_wakeHi : Work.ELNest.armC2 0 + 1 = Work.EL.wakeHi 4 := by
  rw [armC2_zero_angle]; norm_num [Work.EL.wakeHi]

/-! ## (WS) and (WS=) in the form used below -/

/-- **(WS)**, `PbAvoid_core` fed with the portrait of `PbAvoid_portrait`: if the wake arc `W_j`
lies in the far arc of a pair `Q` which shares no angle with the portrait pair `P_j`, then the
wake side `X_j` lies in the far side of `Q`. -/
private lemma wakeSide_sub_of_arith {c : ℂ} (d : Work.EL.RootParabolic c)
    (hzero : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
      (Work.EL.LandsN d.hN θ d.z₁ ↔ θ = Work.EL.alpha1 ∨ θ = Work.EL.alpha2))
    (hcount : Work.ELPull.PortraitCount (hNcanOf d))
    (j : ℕ) (hj5 : j < 5) (Q : Work.EL.CoPair d.hN)
    (hW : ∀ θ : ℝ, Work.EL.InArc θ (Work.EL.wakeLo j) (Work.EL.wakeHi j) →
      Work.EL.InArc θ Q.a Q.b)
    (hna : Int.fract Q.a ≠ Work.EL.T^[j] Work.EL.alpha1 ∧
      Int.fract Q.a ≠ Work.EL.T^[j] Work.EL.alpha2)
    (hnb : Int.fract Q.b ≠ Work.EL.T^[j] Work.EL.alpha1 ∧
      Int.fract Q.b ≠ Work.EL.T^[j] Work.EL.alpha2) :
    Work.EL.wakeSide d.hN d.z₁ j ⊆ Work.EL.pairSide Q :=
  (PbAvoid_core d j hj5).1
    (PbAvoid_portrait d hzero hcount (PbAvoid_cycle d).1 j hj5) Q hW hna hnb

/-- **(WS=)**: if the pair `Q` *is* the cycle pair `(wakeLo j, wakeHi j)`, then the wake side
`X_j` lies in the far side of `Q`. -/
private lemma wakeSide_sub_of_eq {c : ℂ} (d : Work.EL.RootParabolic c)
    (j : ℕ) (hj5 : j < 5) (Q : Work.EL.CoPair d.hN)
    (ha : Q.a = Work.EL.wakeLo j) (hb : Q.b = Work.EL.wakeHi j) :
    Work.EL.wakeSide d.hN d.z₁ j ⊆ Work.EL.pairSide Q := by
  have h := (PbAvoid_core d j hj5).2 Q ha hb
  intro x hx
  rw [h] at hx
  exact hx

/-- **Separation.**  If the `k`-th point of the critical orbit lies in the wake side `X_j` (with
`j = (k-1) % 5`), `X_j` lies in the far side of a non-degenerate pair `Q`, and `S` lies in the
near side of `Q`, then the orbit point is not in `S`. -/
private lemma sep_of {c : ℂ} (d : Work.EL.RootParabolic c)
    (Q : Work.EL.CoPair d.hN) (hnd : Work.EL.arcLen Q.a Q.b ≠ 0)
    (hJ : Work.Top.JordanForm) {j k : ℕ} (hjEq : (k - 1) % 5 = j) (hk1 : 1 ≤ k)
    (hsub : Work.EL.wakeSide d.hN d.z₁ j ⊆ Work.EL.pairSide Q)
    {S : Set ℂ} (hS : S ⊆ Work.EL.pairSideNear Q) :
    (Tantibar c)^[k] 0 ∉ S := by
  intro hxS
  have hw : (Tantibar c)^[k] 0 ∈ Work.EL.wakeSide d.hN d.z₁ j := by
    have h := d.wake k hk1
    rwa [hjEq] at h
  have hfar : (Tantibar c)^[k] 0 ∈ Work.EL.pairSide Q := hsub hw
  have hnear : (Tantibar c)^[k] 0 ∈ Work.EL.pairSideNear Q := hS hxS
  exact (Set.disjoint_left.mp (Work.ELTop.pairSides d.hN hJ Q hnd).disjoint hfar) hnear

-- Shell: `namespace Work.ELAssembly` (area `Submission/Work/ELAssembly/`), `open LeanEval.ComplexAnalysis (Tantibar)`.
/-- **The critical orbit avoids both pull-back regions** (`NOTES_LEAD_mandelbar_pbavoid.md` §1 and
§3.5): the conjunction of `critOrbit_notMem_Qregion` (`(Tantibar c)^[k] 0` is outside
`polyRegion [alphaPairOf d, N.Qp n] (Qlev L n)` for `k = 1..10`) and `critOrbit_notMem_Dregion`
(outside `polyRegion [N.Za n, N.Zb n, N.Zc n] (Dlev L n)` for `k = 1..6`).

Method.  `d.wake k` puts `(Tantibar c)^[k] 0` in the wake side `X_j`, `j = (k-1) % 5`, and
`Qmem_of` (resp. `Dmem_of`) writes the region as an intersection of near sides and a potential
sublevel set.  It remains to exhibit one pair `Q` of the region's list with `X_j ⊆ pairSide Q`
(SEP then contradicts the near-side factor via `(Work.ELTop.pairSides d.hN hJ Q hnd).disjoint`).

* Q-nest: `k = 1, 6` (`j = 0`) use `Q = alphaPairOf d` via
  `Work.FinalFix.wakeSide_zero_eq_pairSide d _ rfl rfl rfl`; the other eight use `Q = N.Qp n` via
  (WS) — `PbAvoid_core` fed with `PbAvoid_portrait d hzero hcount j _` (the `(PJ)` portrait at
  `T^j z₁`, from the `(C1)` landings of `PbAvoid_cycle`), the wake-arc inclusion and the
  non-degeneracy from `PbAvoid_arithQ` rewritten by `N.Qpa`/`N.Qpb`.
* D-nest: `k = 1, 6` (`j = 0`) use `Za n`; `k = 3` (`j = 2`) uses `Zb n`; `k = 5` (`j = 4`) uses
  `Zc n` — for `n = 0` these are degenerate (`Za 0 = P_0`, `Zb 0 = P_2`, `Zc 0 = P_4`, from the
  zero-angle lemmas of `Work.ELAssembly.armChainInputs_of`) and handled by (WS=) with the same
  angles; for `n ≥ 1` by (WS) with `PbAvoid_arithD`.  `k = 2` (`j = 1`) and `k = 4` (`j = 3`) use
  `Zc n` at every level by (WS) with `PbAvoid_arithD`.
  The `hnd` inputs of `Dmem_of` are `Work.ELAssembly.armChainInputs_of d` (rewritten by
  `N.Zca`/`N.Zcb` and `Work.EL.arcLen_add_one`-style shifts); those of `Qmem_of` are
  `Work.ELAssembly.Qne_of d N hzero` and `Work.ELAssembly.arcLen_bAng_ne_zero`.

This is what removes `hcvQ`/`hcvD` from the bundle. -/
theorem PbAvoid_main {c : ℂ} (d : Work.EL.RootParabolic c)
    (hzero : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
      (Work.EL.LandsN d.hN θ d.z₁ ↔ θ = Work.EL.alpha1 ∨ θ = Work.EL.alpha2))
    (hcount : Work.ELPull.PortraitCount (hNcanOf d))
    (N : NestPairs d) {L : ℝ} (hL : 1 < L)
    (hadm : ∀ n : ℕ, Work.EL.PolyAdmissible [N.Za n, N.Zb n, N.Zc n]) :
    (∀ n : ℕ, ∀ k ∈ Finset.Icc 1 10, (LeanEval.ComplexAnalysis.Tantibar c)^[k] 0 ∉
      Work.EL.polyRegion [alphaPairOf d, N.Qp n] (Work.ELNest.Qlev L n)) ∧
    (∀ n : ℕ, ∀ k ∈ Finset.Icc 1 6, (LeanEval.ComplexAnalysis.Tantibar c)^[k] 0 ∉
      Work.EL.polyRegion [N.Za n, N.Zb n, N.Zc n] (Work.ELNest.Dlev L n)) := by
  obtain ⟨_, _, _, hQW, hQND⟩ := PbAvoid_arithQ
  obtain ⟨hW0, hW2, hWC, hNDA, hNDB, hNDC1, hNDC3, hNDC4⟩ := PbAvoid_arithD
  have hJ : Work.Top.JordanForm := Work.TopJordan.jordanForm
  have hQne : ∀ n : ℕ, (N.Qp n).y ≠ d.z₁ := Qne_of d N hzero
  -- the non-degeneracy of the three arm pairs
  have hndZa : ∀ n : ℕ, Work.EL.arcLen (N.Za n).a (N.Za n).b ≠ 0 := fun n => by
    rw [N.Zaa n, N.Zab n]
    exact (armChainInputs_of d).2.1 n
  have hndZb : ∀ n : ℕ, Work.EL.arcLen (N.Zb n).a (N.Zb n).b ≠ 0 := fun n => by
    rw [N.Zba n, N.Zbb n]
    exact (armChainInputs_of d).2.2.1 n
  have hndZc : ∀ n : ℕ, Work.EL.arcLen (N.Zc n).a (N.Zc n).b ≠ 0 := fun n => by
    rw [N.Zca n, N.Zcb n, arcLen_succ_right]
    exact (armChainInputs_of d).2.2.2 n
  -- the region containments (near sides)
  have hS0 : ∀ n : ℕ, Work.EL.polyRegion [alphaPairOf d, N.Qp n] (Work.ELNest.Qlev L n) ⊆
      Work.EL.pairSideNear (alphaPairOf d) := fun n => by
    rw [Qmem_of d N hQne hL n]
    intro z hz
    exact hz.1.1
  have hSQ : ∀ n : ℕ, Work.EL.polyRegion [alphaPairOf d, N.Qp n] (Work.ELNest.Qlev L n) ⊆
      Work.EL.pairSideNear (N.Qp n) := fun n => by
    rw [Qmem_of d N hQne hL n]
    intro z hz
    exact hz.1.2
  have hSZb : ∀ n : ℕ, Work.EL.polyRegion [N.Za n, N.Zb n, N.Zc n] (Work.ELNest.Dlev L n) ⊆
      Work.EL.pairSideNear (N.Zb n) := fun n => by
    rw [Dmem_of d N hL hadm hndZa hndZb hndZc n]
    intro z hz
    exact hz.1.1.2
  have hSZa : ∀ n : ℕ, Work.EL.polyRegion [N.Za n, N.Zb n, N.Zc n] (Work.ELNest.Dlev L n) ⊆
      Work.EL.pairSideNear (N.Za n) := fun n => by
    rw [Dmem_of d N hL hadm hndZa hndZb hndZc n]
    intro z hz
    exact hz.1.1.1
  have hSZc : ∀ n : ℕ, Work.EL.polyRegion [N.Za n, N.Zb n, N.Zc n] (Work.ELNest.Dlev L n) ⊆
      Work.EL.pairSideNear (N.Zc n) := fun n => by
    rw [Dmem_of d N hL hadm hndZa hndZb hndZc n]
    intro z hz
    exact hz.1.2
  constructor
  · -- ## the `z₁`-nest: `k = 1..10`
    intro n k hk
    obtain ⟨hk1, -⟩ := Finset.mem_Icc.mp hk
    have hjcases : (k - 1) % 5 = 0 ∨ (k - 1) % 5 = 1 ∨ (k - 1) % 5 = 2 ∨
        (k - 1) % 5 = 3 ∨ (k - 1) % 5 = 4 := by omega
    rcases hjcases with h0 | h1 | h2 | h3 | h4
    · -- `j = 0`: the `α`-pair itself
      exact sep_of d (alphaPairOf d) arcLen_alpha_ne_zero hJ h0 hk1
        (wakeSide_sub_of_eq d 0 (by norm_num) (alphaPairOf d) rfl rfl) (hS0 n)
    · -- `j = 1`
      exact sep_of d (N.Qp n)
        (by rw [N.Qpa n, N.Qpb n]; exact arcLen_bAng_ne_zero n) hJ h1 hk1
        (wakeSide_sub_of_arith d hzero hcount 1 (by norm_num) (N.Qp n)
          (fun θ hθ => by
            rw [N.Qpa n, N.Qpb n]
            exact hQW n 1 (by norm_num) (by norm_num) θ hθ)
          (by rw [N.Qpa n]; exact (hQND n 1 (by norm_num) (by norm_num)).1)
          (by rw [N.Qpb n]; exact (hQND n 1 (by norm_num) (by norm_num)).2))
        (hSQ n)
    · -- `j = 2`
      exact sep_of d (N.Qp n)
        (by rw [N.Qpa n, N.Qpb n]; exact arcLen_bAng_ne_zero n) hJ h2 hk1
        (wakeSide_sub_of_arith d hzero hcount 2 (by norm_num) (N.Qp n)
          (fun θ hθ => by
            rw [N.Qpa n, N.Qpb n]
            exact hQW n 2 (by norm_num) (by norm_num) θ hθ)
          (by rw [N.Qpa n]; exact (hQND n 2 (by norm_num) (by norm_num)).1)
          (by rw [N.Qpb n]; exact (hQND n 2 (by norm_num) (by norm_num)).2))
        (hSQ n)
    · -- `j = 3`
      exact sep_of d (N.Qp n)
        (by rw [N.Qpa n, N.Qpb n]; exact arcLen_bAng_ne_zero n) hJ h3 hk1
        (wakeSide_sub_of_arith d hzero hcount 3 (by norm_num) (N.Qp n)
          (fun θ hθ => by
            rw [N.Qpa n, N.Qpb n]
            exact hQW n 3 (by norm_num) (by norm_num) θ hθ)
          (by rw [N.Qpa n]; exact (hQND n 3 (by norm_num) (by norm_num)).1)
          (by rw [N.Qpb n]; exact (hQND n 3 (by norm_num) (by norm_num)).2))
        (hSQ n)
    · -- `j = 4`
      exact sep_of d (N.Qp n)
        (by rw [N.Qpa n, N.Qpb n]; exact arcLen_bAng_ne_zero n) hJ h4 hk1
        (wakeSide_sub_of_arith d hzero hcount 4 (by norm_num) (N.Qp n)
          (fun θ hθ => by
            rw [N.Qpa n, N.Qpb n]
            exact hQW n 4 (by norm_num) (by norm_num) θ hθ)
          (by rw [N.Qpa n]; exact (hQND n 4 (by norm_num) (by norm_num)).1)
          (by rw [N.Qpb n]; exact (hQND n 4 (by norm_num) (by norm_num)).2))
        (hSQ n)
  · -- ## the `b₂`-nest: `k = 1..6`
    intro n k hk
    obtain ⟨hk1, -⟩ := Finset.mem_Icc.mp hk
    have hjcases : (k - 1) % 5 = 0 ∨ (k - 1) % 5 = 1 ∨ (k - 1) % 5 = 2 ∨
        (k - 1) % 5 = 3 ∨ (k - 1) % 5 = 4 := by omega
    rcases hjcases with h0 | h1 | h2 | h3 | h4
    · -- `j = 0`: `Za n`
      rcases Nat.eq_zero_or_pos n with hn0 | hn
      · subst hn0
        exact sep_of d (N.Za 0) (hndZa 0) hJ h0 hk1
          (wakeSide_sub_of_eq d 0 (by norm_num) (N.Za 0)
            (by rw [N.Zaa 0]; exact armA1_zero_wakeLo)
            (by rw [N.Zab 0]; exact armA2_zero_wakeHi))
          (hSZa 0)
      · exact sep_of d (N.Za n) (hndZa n) hJ h0 hk1
          (wakeSide_sub_of_arith d hzero hcount 0 (by norm_num) (N.Za n)
            (fun θ hθ => by
              rw [N.Zaa n, N.Zab n]
              exact hW0 n θ hθ)
            (by rw [N.Zaa n]; exact ⟨(hNDA n hn).1, (hNDA n hn).2.1⟩)
            (by rw [N.Zab n]; exact ⟨(hNDA n hn).2.2.1, (hNDA n hn).2.2.2⟩))
          (hSZa n)
    · -- `j = 1`: `Zc n`, all levels
      exact sep_of d (N.Zc n) (hndZc n) hJ h1 hk1
        (wakeSide_sub_of_arith d hzero hcount 1 (by norm_num) (N.Zc n)
          (fun θ hθ => by
            rw [N.Zca n, N.Zcb n]
            exact hWC n 1 (Or.inl rfl) θ hθ)
          (by rw [N.Zca n]; exact ⟨(hNDC1 n).1, (hNDC1 n).2.1⟩)
          (by rw [N.Zcb n]; exact ⟨(hNDC1 n).2.2.1, (hNDC1 n).2.2.2⟩))
        (hSZc n)
    · -- `j = 2`: `Zb n`
      rcases Nat.eq_zero_or_pos n with hn0 | hn
      · subst hn0
        exact sep_of d (N.Zb 0) (hndZb 0) hJ h2 hk1
          (wakeSide_sub_of_eq d 2 (by norm_num) (N.Zb 0)
            (by rw [N.Zba 0]; exact armB1_zero_wakeLo)
            (by rw [N.Zbb 0]; exact armB2_zero_wakeHi))
          (hSZb 0)
      · exact sep_of d (N.Zb n) (hndZb n) hJ h2 hk1
          (wakeSide_sub_of_arith d hzero hcount 2 (by norm_num) (N.Zb n)
            (fun θ hθ => by
              rw [N.Zba n, N.Zbb n]
              exact hW2 n θ hθ)
            (by rw [N.Zba n]; exact ⟨(hNDB n hn).1, (hNDB n hn).2.1⟩)
            (by rw [N.Zbb n]; exact ⟨(hNDB n hn).2.2.1, (hNDB n hn).2.2.2⟩))
          (hSZb n)
    · -- `j = 3`: `Zc n`, all levels
      exact sep_of d (N.Zc n) (hndZc n) hJ h3 hk1
        (wakeSide_sub_of_arith d hzero hcount 3 (by norm_num) (N.Zc n)
          (fun θ hθ => by
            rw [N.Zca n, N.Zcb n]
            exact hWC n 3 (Or.inr (Or.inl rfl)) θ hθ)
          (by rw [N.Zca n]; exact ⟨(hNDC3 n).1, (hNDC3 n).2.1⟩)
          (by rw [N.Zcb n]; exact ⟨(hNDC3 n).2.2.1, (hNDC3 n).2.2.2⟩))
        (hSZc n)
    · -- `j = 4`: `Zc n`
      rcases Nat.eq_zero_or_pos n with hn0 | hn
      · subst hn0
        exact sep_of d (N.Zc 0) (hndZc 0) hJ h4 hk1
          (wakeSide_sub_of_eq d 4 (by norm_num) (N.Zc 0)
            (by rw [N.Zca 0]; exact armC1_zero_wakeLo)
            (by rw [N.Zcb 0]; exact armC2_zero_succ_wakeHi))
          (hSZc 0)
      · exact sep_of d (N.Zc n) (hndZc n) hJ h4 hk1
          (wakeSide_sub_of_arith d hzero hcount 4 (by norm_num) (N.Zc n)
            (fun θ hθ => by
              rw [N.Zca n, N.Zcb n]
              exact hWC n 4 (Or.inr (Or.inr rfl)) θ hθ)
            (by rw [N.Zca n]; exact ⟨(hNDC4 n hn).1, (hNDC4 n hn).2.1⟩)
            (by rw [N.Zcb n]; exact ⟨(hNDC4 n hn).2.2.1, (hNDC4 n hn).2.2.2⟩))
          (hSZc n)

end Work.ELAssembly
