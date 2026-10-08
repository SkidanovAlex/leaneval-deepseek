import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q
import Submission.Work.CharCore.Defs
import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# F0c: `C_G(x) = Q` for `x ∈ Q#`

In the split rank-one Zassenhaus configuration `(H, Q, t)` with `Q` abelian, the centraliser
of every nontrivial element of the regular normal subgroup `Q` is exactly `Q`.

The proof has two halves, both purely geometric (no character theory).

* **`C_G(x) ≤ H`.**  Every element outside `H` is uniquely `a * t * q` with `a ∈ H`, `q ∈ Q`
  (`ZassenhausPSL2.exists_unique_decomp`, from 2-transitivity).  If such an element `g`
  centralised `x`, then `t (q x q⁻¹) t = a⁻¹ x a`; the right hand side lies in `Q ≤ H`, so
  `q x q⁻¹ ∈ H ∩ H^t = D` and hence `q x q⁻¹ = 1` by `Q ∩ D = 1`, forcing `x = 1`.

* **`C_H(x) = Q`.**  Write `h ∈ H` as `d * q` with `d ∈ D`, `q ∈ Q`
  (`ZassenhausPSL2.mem_eq_dStab_mul_Q`).  If `h x h⁻¹ = x` then `d x d⁻¹ = x` because `Q` is
  abelian, and `D` acts fixed point freely on `Q#` (`ZData.dStab_fpf_on_Q`, the three-point
  condition), so `d = 1` and `h = q ∈ Q`.
-/

set_option autoImplicit false

namespace Work.ZassenhausPSL2.Feit

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]
variable {H Q : Subgroup G} {t : G}

/-- **First half.** Any element commuting with a nontrivial `x ∈ Q` lies in `H`
(a coset of `H t Q = G ∖ H` centralises no nontrivial element of `Q`). -/
theorem mem_H_of_commute {x : G} (h : IsSplitRankOne H Q t) {g : G} (hx : x ∈ Q)
    (hx1 : x ≠ 1) (hgx : g * x = x * g) : g ∈ H := by
  by_contra hgH
  obtain ⟨p, hp, -⟩ := Work.ZassenhausPSL2.exists_unique_decomp h hgH
  have haH : (p.1 : G) ∈ H := p.1.2
  have hqQ : (p.2 : G) ∈ Q := p.2.2
  have hp' : (p.1 : G) * t * (p.2 : G) = g := hp
  -- the conjugating identity `t (q x q⁻¹) t = a⁻¹ x a`
  have hconj : t * ((p.2 : G) * x * (p.2 : G)⁻¹) * t
      = (p.1 : G)⁻¹ * x * (p.1 : G) := by
    have h1 : (p.1 : G) * t * (p.2 : G) * x = x * ((p.1 : G) * t * (p.2 : G)) := by
      rw [hp', hgx]
    calc t * ((p.2 : G) * x * (p.2 : G)⁻¹) * t
        = (p.1 : G)⁻¹ * ((p.1 : G) * t * (p.2 : G) * x) * (p.2 : G)⁻¹ * t := by group
      _ = (p.1 : G)⁻¹ * (x * ((p.1 : G) * t * (p.2 : G))) * (p.2 : G)⁻¹ * t := by rw [h1]
      _ = (p.1 : G)⁻¹ * x * (p.1 : G) * (t * t) := by group
      _ = (p.1 : G)⁻¹ * x * (p.1 : G) := by
            rw [Work.ZassenhausPSL2.t_mul_t h, mul_one]
  have hyQ : (p.2 : G) * x * (p.2 : G)⁻¹ ∈ Q :=
    mul_mem (mul_mem hqQ hx) (inv_mem hqQ)
  have hzQ : (p.1 : G)⁻¹ * x * (p.1 : G) ∈ Q := by
    simpa using (Subgroup.le_normalizer_iff.mp h.normal) (p.1 : G)⁻¹ (H.inv_mem haH) x hx
  -- so `q x q⁻¹` lies in `H` and in `H^t`, hence in `Q ∩ D = 1`
  have hy_conj : (p.2 : G) * x * (p.2 : G)⁻¹ ∈ conj t H := by
    rw [conj, Subgroup.mem_map]
    refine ⟨(p.1 : G)⁻¹ * x * (p.1 : G), h.le hzQ, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [Work.ZassenhausPSL2.t_inv h, ← hconj]
    exact Work.ZassenhausPSL2.t_conj_invol h ((p.2 : G) * x * (p.2 : G)⁻¹)
  have hy_bot : (p.2 : G) * x * (p.2 : G)⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [← h.inf_eq]
    exact ⟨hyQ, h.le hyQ, hy_conj⟩
  have hy1 : (p.2 : G) * x * (p.2 : G)⁻¹ = 1 := by simpa using hy_bot
  exact hx1 (by
    calc x = (p.2 : G)⁻¹ * ((p.2 : G) * x * (p.2 : G)⁻¹) * (p.2 : G) := by group
      _ = 1 := by rw [hy1]; group)

/-- **Second half.** An element of `H` commuting with a nontrivial `x ∈ Q` lies in `Q`
(the `D`-part of `H = Q ⋊ D` acts fixed point freely on `Q#`). -/
theorem mem_Q_of_mem_H_of_commute {x : G} (h : IsSplitRankOne H Q t)
    (hz : IsZassenhaus H) (hab : IsAbelianSubgroup Q) (hx : x ∈ Q) (hx1 : x ≠ 1)
    {g : G} (hgH : g ∈ H) (hgx : g * x = x * g) : g ∈ Q := by
  obtain ⟨d, q, hdq⟩ := Work.ZassenhausPSL2.mem_eq_dStab_mul_Q h ⟨g, hgH⟩
  have hdq' : (d : G) * (q : G) = g := hdq
  have hqcomm : (q : G) * x = x * (q : G) := hab (q : G) q.2 x hx
  have hd_eq : (d : G) = g * (q : G)⁻¹ := by rw [← hdq']; group
  have hqinv : (q : G)⁻¹ * x * (q : G) = x := by
    calc (q : G)⁻¹ * x * (q : G) = (q : G)⁻¹ * (x * (q : G)) := by group
      _ = (q : G)⁻¹ * ((q : G) * x) := by rw [← hqcomm]
      _ = x := by group
  have hdx : (d : G) * x * (d : G)⁻¹ = x := by
    rw [hd_eq]
    calc (g * (q : G)⁻¹) * x * (g * (q : G)⁻¹)⁻¹
        = g * ((q : G)⁻¹ * x * (q : G)) * g⁻¹ := by group
      _ = g * x * g⁻¹ := by rw [hqinv]
      _ = x := by rw [hgx, mul_assoc, mul_inv_cancel, mul_one]
  have hd1 : (d : G) = 1 := by
    by_contra hne
    exact hx1 (Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q H Q t h hz (d : G) d.2 hne x hx hdx)
  rw [← hdq', hd1, one_mul]
  exact q.2

/-- **F0c.** `C_G(x) = Q` for `1 ≠ x ∈ Q` (`Q` abelian, three-point condition). -/
theorem centralizer_eq_Q {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (hab : Submission.Blueprint.IsAbelianSubgroup Q) {x : G} (hx : x ∈ Q) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) = Q := by
  refine le_antisymm ?_ ?_
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    exact mem_Q_of_mem_H_of_commute h hz hab hx hx1
      (mem_H_of_commute h hx hx1 hg) hg
  · intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hab q hq x hx

end Work.ZassenhausPSL2.Feit
