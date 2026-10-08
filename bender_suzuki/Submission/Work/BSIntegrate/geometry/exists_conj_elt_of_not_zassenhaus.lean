import Mathlib
import Submission.Work.RankOneUniqueness.rankOneUniqueness
import Submission.Work.ZassenhausTwoGroup.isTI_Q

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A non-Zassenhaus split rank-one datum has a non-trivial `D`-fixed point of `Q#`

Peterfalvi II, p. 236: a split rank-one group `G` on `Ω = G ⧸ H` (so `H = Q ⋊ D` with
`D = twoPoint H t = H ⊓ Hᵗ`, `Q` regular on `Ω ∖ {∞}`) is a Zassenhaus group — the pointwise
stabiliser of three points is trivial — **iff** `D` acts fixed-point-freely on `Q#`, i.e.
`C_Q(d) = 1` for every `d ∈ D ∖ {1}`.

This file proves the contrapositive, in the form needed by the `PSU₃`/`ThmG` route:

> if `IsSplitRankOne H Q t` holds and `H` is *not* Zassenhaus, then some `d ∈ D = H ⊓ Hᵗ`,
> `d ≠ 1`, centralises a non-identity `q ∈ Q`.

The argument is purely geometric (no finiteness).

* `¬ IsZassenhaus H` gives three distinct points `a, b, c` of `Ω` and `g ≠ 1` fixing all
  three.  By 2-transitivity (`IsSplitRankOne.twoTransitive`) some `x` carries the ordered pair
  `(a, b)` to `(∞, t • ∞)`; the conjugate `d = x g x⁻¹ ≠ 1` then fixes `∞`, `t • ∞` and the
  third point `c' = x • c ≠ ∞, t • ∞`.  Fixing `∞` and `t • ∞` means exactly `d ∈ D`
  (`Work.RankOneUniqueness.smul_pt_iff`, `Work.ZassenhausTwoGroup.IsTIQ.mem_twoPoint_iff_smul`).
* The points of `Ω ∖ {∞}` are exactly the `q • (t • ∞)` with `q ∈ Q`
  (`Work.RankOneUniqueness.qPt_surjective`), so `c' = q • (t • ∞)` with `q ∈ Q`; and `q ≠ 1`
  because otherwise `c' = t • ∞`.
* Finally, `d` fixes `t • ∞` (so does `d⁻¹`) and fixes `c' = q • (t • ∞)`, hence
  `d q d⁻¹` and `q` move `t • ∞` to the same point, i.e. `(d q d⁻¹)⁻¹ q` fixes `t • ∞`.
  Since `d ∈ H` normalises `Q`, both `d q d⁻¹` and `q` lie in `Q`; `Q` acts freely on
  `Ω ∖ {∞}` (`Work.ZassenhausTwoGroup.IsTIQ.Q_smul_eq_self`), so `(d q d⁻¹)⁻¹ q = 1`,
  i.e. `d q d⁻¹ = q`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint

namespace Work.BSIntegrate.geometry

theorem exists_conj_elt_of_not_zassenhaus {G : Type*} [Group G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hz : ¬ Submission.Blueprint.IsZassenhaus H) :
    ∃ d ∈ Submission.Blueprint.twoPoint H t, d ≠ 1 ∧
      ∃ q ∈ Q, q ≠ 1 ∧ d * q * d⁻¹ = q := by
  classical
  -- ## 1. Unfold the negation of the Zassenhaus condition
  rw [Submission.Blueprint.IsZassenhaus] at hz
  push Not at hz
  obtain ⟨a, b, c, hab, hac, hbc, g, hga, hgb, hgc, hg1⟩ := hz
  -- ## 2. Bring the ordered pair `(a, b)` to `(∞, t • ∞)` by 2-transitivity
  have h2t : MulAction.IsMultiplyPretransitive G (G ⧸ H) 2 := h.twoTransitive
  rw [MulAction.is_two_pretransitive_iff] at h2t
  have htne : t • Work.RankOneUniqueness.pt H ≠ Work.RankOneUniqueness.pt H :=
    Work.RankOneUniqueness.t_smul_pt_ne h
  obtain ⟨x, hxa, hxb⟩ := h2t hab htne.symm
  -- the conjugate `d = x g x⁻¹` and the third point `c' = x • c`
  set c' : G ⧸ H := x • c with hc'def
  set d : G := x * g * x⁻¹ with hddef
  have hd_pt : d • Work.RankOneUniqueness.pt H = Work.RankOneUniqueness.pt H := by
    rw [hddef, ← hxa]
    calc (x * g * x⁻¹) • (x • a) = ((x * g * x⁻¹) * x) • a :=
          (mul_smul (x * g * x⁻¹) x a).symm
      _ = (x * g) • a := by rw [show x * g * x⁻¹ * x = x * g from by group]
      _ = x • (g • a) := mul_smul x g a
      _ = x • a := by rw [hga]
  have hd_tpt : d • (t • Work.RankOneUniqueness.pt H) = t • Work.RankOneUniqueness.pt H := by
    rw [hddef, ← hxb]
    calc (x * g * x⁻¹) • (x • b) = ((x * g * x⁻¹) * x) • b :=
          (mul_smul (x * g * x⁻¹) x b).symm
      _ = (x * g) • b := by rw [show x * g * x⁻¹ * x = x * g from by group]
      _ = x • (g • b) := mul_smul x g b
      _ = x • b := by rw [hgb]
  have hd_c' : d • c' = c' := by
    rw [hc'def, hddef]
    calc (x * g * x⁻¹) • (x • c) = ((x * g * x⁻¹) * x) • c :=
          (mul_smul (x * g * x⁻¹) x c).symm
      _ = (x * g) • c := by rw [show x * g * x⁻¹ * x = x * g from by group]
      _ = x • (g • c) := mul_smul x g c
      _ = x • c := by rw [hgc]
  -- `c'` is a third point, distinct from `∞` and from `t • ∞`
  have hc'_ne_pt : c' ≠ Work.RankOneUniqueness.pt H := by
    intro hcon
    rw [hc'def] at hcon
    have h1 : x⁻¹ • (x • c) = x⁻¹ • (x • a) := by rw [hcon, hxa]
    rw [inv_smul_smul, inv_smul_smul] at h1
    exact hac h1.symm
  have hc'_ne_tpt : c' ≠ t • Work.RankOneUniqueness.pt H := by
    intro hcon
    rw [hc'def] at hcon
    have h1 : x⁻¹ • (x • c) = x⁻¹ • (x • b) := by rw [hcon, hxb]
    rw [inv_smul_smul, inv_smul_smul] at h1
    exact hbc h1.symm
  have hd_ne_one : d ≠ 1 := by
    intro h1
    apply hg1
    have h2 : x * g * x⁻¹ = 1 := by rw [← hddef]; exact h1
    have h3 := congrArg (fun z : G => x⁻¹ * z * x) h2
    simpa [mul_assoc] using h3
  have hd_ptH : d ∈ H := (Work.RankOneUniqueness.smul_pt_iff H d).mp hd_pt
  have hd_memD : d ∈ Submission.Blueprint.twoPoint H t :=
    (Work.ZassenhausTwoGroup.IsTIQ.mem_twoPoint_iff_smul H t d).mpr
      ⟨hd_ptH, by rw [← Work.RankOneUniqueness.smul_pt H t]; exact hd_tpt⟩
  -- ## 3. The third fixed point is `q • (t • ∞)` with `q ∈ Q ∖ {1}`
  -- (`H` is transitive on `Ω ∖ {∞}`, and `H = Q · D`, the `D`-part fixing `t • ∞`)
  obtain ⟨g₁, hg₁H, hg₁⟩ := Work.ZassenhausTwoGroup.IsTIQ.h_transitive h
    (t • Work.RankOneUniqueness.pt H) c' htne hc'_ne_pt
  obtain ⟨q, hqQ, e, heD, hqe⟩ := Work.RankOneUniqueness.fact_exists h hg₁H
  have he_tpt : e • (t • Work.RankOneUniqueness.pt H) = t • Work.RankOneUniqueness.pt H := by
    have h1 : e • (t : G ⧸ H) = (t : G ⧸ H) :=
      ((Work.ZassenhausTwoGroup.IsTIQ.mem_twoPoint_iff_smul H t e).mp heD).2
    simpa only [Work.RankOneUniqueness.smul_pt] using h1
  have hq_smul : q • (t • Work.RankOneUniqueness.pt H) = c' := by
    calc q • (t • Work.RankOneUniqueness.pt H)
        = q • (e • (t • Work.RankOneUniqueness.pt H)) := by rw [he_tpt]
      _ = (q * e) • (t • Work.RankOneUniqueness.pt H) :=
          (mul_smul q e (t • Work.RankOneUniqueness.pt H)).symm
      _ = g₁ • (t • Work.RankOneUniqueness.pt H) := by rw [hqe]
      _ = c' := hg₁
  have hq_ne_one : q ≠ 1 := by
    intro hq1
    rw [hq1, one_smul] at hq_smul
    exact hc'_ne_tpt hq_smul.symm
  -- ## 4. `d` normalises `Q` and fixes both `t • ∞` and `c' = q • (t • ∞)`
  have hd_inv_tpt : d⁻¹ • (t • Work.RankOneUniqueness.pt H) = t • Work.RankOneUniqueness.pt H := by
    have h1 : d⁻¹ ∈ Submission.Blueprint.twoPoint H t :=
      (Submission.Blueprint.twoPoint H t).inv_mem hd_memD
    have h2 := (Work.ZassenhausTwoGroup.IsTIQ.mem_twoPoint_iff_smul H t d⁻¹).mp h1
    rw [← Work.RankOneUniqueness.smul_pt H t] at h2
    exact h2.2
  -- hence `d q d⁻¹` and `q` agree on `t • ∞`, and both lie in `Q`
  have hdq_conj : d * q * d⁻¹ = q := by
    have h1 : (d * q * d⁻¹) • (t • Work.RankOneUniqueness.pt H)
        = q • (t • Work.RankOneUniqueness.pt H) := by
      calc (d * q * d⁻¹) • (t • Work.RankOneUniqueness.pt H)
          = d • (q • (d⁻¹ • (t • Work.RankOneUniqueness.pt H))) := by
            rw [mul_smul, mul_smul]
        _ = d • (q • (t • Work.RankOneUniqueness.pt H)) := by rw [hd_inv_tpt]
        _ = d • c' := by rw [hq_smul]
        _ = c' := hd_c'
        _ = q • (t • Work.RankOneUniqueness.pt H) := hq_smul.symm
    have hmem : d * q * d⁻¹ ∈ Q := Work.RankOneUniqueness.conj_mem_of_mem h hd_ptH hqQ
    have hfix : ((d * q * d⁻¹)⁻¹ * q) • (t • Work.RankOneUniqueness.pt H)
        = t • Work.RankOneUniqueness.pt H := by
      rw [mul_smul, ← h1, inv_smul_smul]
    have hone : (d * q * d⁻¹)⁻¹ * q = 1 :=
      Work.ZassenhausTwoGroup.IsTIQ.Q_smul_eq_self h
        (Q.mul_mem (Q.inv_mem hmem) hqQ) hfix htne
    exact inv_mul_eq_one.mp hone
  exact ⟨d, hd_memD, hd_ne_one, q, hqQ, hq_ne_one, hdq_conj⟩

end Work.BSIntegrate.geometry
