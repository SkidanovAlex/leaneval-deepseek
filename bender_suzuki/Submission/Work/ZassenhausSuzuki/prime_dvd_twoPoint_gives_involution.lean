import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.twoPoint_inverted
import Submission.Work.ZassenhausSuzuki.QSZ_invH_le_centerQ
import Submission.Work.ThmF.ChV12.lemma4

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Every prime divisor of `|D|` is the order of some `w * t` with `w` an involution of `Q`

Let `G` be a finite group with a Zassenhaus split rank-one configuration `H = Q ⋊ D`
(`Submission.Blueprint.IsSplitRankOne H Q t`, `D = H ∩ Hᵗ = twoPoint H t`,
`Submission.Blueprint.IsZassenhaus H`) whose root group `Q` is a `2`-group.  Then for every
prime `p` dividing the order of the two-point stabiliser `D = twoPoint H t` there is an
involution `w ∈ Q` with `orderOf (w * t) = p` (Suzuki 1962, Prop. 13: the strongly real
elements `π τ`, `π ∈ Inv(Q)`, realize all the orders occurring in the torus `D`).

The argument is the "strongly real" half of Peterfalvi II, Ch. V §2 Lemma 4, already available
in the workspace as `Work.ThmF.ChV12.exists_conj_eq_inv_mul_t`:

* `p ∣ |D|` with `p` prime gives, by Cauchy's theorem, an element `α ∈ D` with `orderOf α = p`
  (and `p` is odd, since `|D|` is odd by strong embeddedness — so `α² ≠ 1`);
* `t` inverts `D` (`twoPoint_inverted`), so `t α t = α⁻¹`; hence `t` and `t * α` are involutions
  with `t * (t * α) = α`, i.e. `α` is **strongly real**;
* `exists_conj_eq_inv_mul_t` — whose only extra input is that the involutions of every conjugate
  of `H` commute pairwise — conjugates `α` to `u * t` for some `u ∈ Q₀ H ∖ {1}`;
* `u ≠ 1` forces `u` to be an involution of `H`, and involutions of `H` lie in `Z(Q)`
  (`QSZ_invH_le_centerQ`); conjugacy preserves orders, so `orderOf (u * t) = orderOf α = p`.

The commutativity input is `prime_dvd_invH_commute` below: the involutions of `H` commute
because they lie in the centre of `Q` (`QSZ_invH_le_centerQ`), transported to conjugates by
`Work.ThmF.ChV12.involution_commute_conj`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ZassenhausSuzuki

/-- In split rank-one data with `Q` a `2`-group, the involutions of `H` commute pairwise: by
Peterfalvi II Ch. V §1 Prop. 1 (c) (`QSZ_invH_le_centerQ`) they all lie in `Z(Q)`. -/
theorem prime_dvd_invH_commute {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (h2 : IsPGroup 2 Q) :
    ∀ u ∈ involutions (H : Set G), ∀ v ∈ involutions (H : Set G), u * v = v * u := by
  intro u hu v hv
  have hu' := Work.ThmF.mem_centerOf.mp (QSZ_invH_le_centerQ h h2 u hu)
  have hv' := Work.ThmF.mem_centerOf.mp (QSZ_invH_le_centerQ h h2 v hv)
  exact hu'.2 v hv'.1

theorem prime_dvd_twoPoint_gives_involution {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G} (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hZ : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (p : ℕ) (hp : p.Prime) (hpd : p ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t)) :
    ∃ w : G, w ∈ Q ∧ orderOf w = 2 ∧ orderOf (w * t) = p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- `t` is an involution
  have ht2 : t * t = 1 := by
    have hh : t ^ 2 = 1 := by simpa [h.invol] using pow_orderOf_eq_one t
    simpa [pow_two] using hh
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  -- `|D|` is odd, so `p ≠ 2`
  have hDodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) :=
    Work.ThmF.split_odd_card_twoPoint h
  have hp2 : p ≠ 2 := by
    intro h2p
    rw [h2p] at hpd
    exact (Nat.not_even_iff_odd.mpr hDodd) (even_iff_two_dvd.mpr hpd)
  -- Cauchy: an element `α ∈ D` of order `p`
  obtain ⟨α, hαmem, hαord⟩ : ∃ α : G, α ∈ Submission.Blueprint.twoPoint H t ∧ orderOf α = p := by
    obtain ⟨x, hx⟩ :=
      exists_prime_orderOf_dvd_card' (G := ↥(Submission.Blueprint.twoPoint H t)) p hpd
    exact ⟨(x : G), x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩
  -- `Q ≠ ⊥` (`|H| = |Q| · |D|` with `|H|` even and `|D|` odd), so `t` inverts `D`
  have hQne : Q ≠ ⊥ := by
    intro hbot
    have hcard := Work.ThmF.split_card_H h
    rw [hbot, Subgroup.card_bot, one_mul] at hcard
    exact (Nat.not_odd_iff_even.mpr (Work.ThmF.split_even_card_H h)) (hcard ▸ hDodd)
  have htα : t * α * t = α⁻¹ := by
    have hh := twoPoint_inverted h hZ hQne h2 α hαmem
    rwa [htinv] at hh
  -- `α` is strongly real: `α = t * (t * α)` with `t`, `t * α` involutions, and `α * α ≠ 1`
  have hαα : α * α ≠ 1 := by
    intro hcon
    have hdvd : p ∣ 2 := by
      have h1 : orderOf α ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
      rwa [hαord] at h1
    exact hp2 (le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) hp.two_le)
  have hb2 : (t * α) * (t * α) = 1 := by
    rw [show (t * α) * (t * α) = (t * α * t) * α by group, htα, inv_mul_cancel]
  have hab : t * (t * α) = α := by rw [← mul_assoc, ht2, one_mul]
  -- the involutions of every conjugate of `H` commute
  have hcomm : ∀ g : G, ∀ u ∈ involutions (Submission.Blueprint.conj g H : Set G),
      ∀ v ∈ involutions (Submission.Blueprint.conj g H : Set G), u * v = v * u :=
    Work.ThmF.ChV12.involution_commute_conj (G := G) (H := H)
      (prime_dvd_invH_commute h h2)
  -- Ch. V §2 Lemma 4 (strongly real elements): `α` is conjugate to `u * t`, `u ∈ Q₀ H ∖ {1}`
  obtain ⟨u, huQ0, hu1, g, hg⟩ :=
    Work.ThmF.ChV12.exists_conj_eq_inv_mul_t (G := G) h.stronglyEmbedded h.twoTransitive
      h.invol h.not_mem hcomm hαα ⟨t, t * α, ht2, hb2, hab⟩
  -- `u` is an involution of `H`, hence lies in `Q`
  have huInv : u ∈ involutions (H : Set G) := by
    rw [Work.ThmF.mem_Q0_iff] at huQ0
    rcases huQ0 with hu | h1
    · exact hu
    · exact absurd h1 hu1
  have huQ : u ∈ Q := (Work.ThmF.mem_centerOf.mp (QSZ_invH_le_centerQ h h2 u huInv)).1
  refine ⟨u, huQ, huInv.2, ?_⟩
  rw [← hg, Work.ThmF.Bender.orderOf_conj_eq g α, hαord]

end Work.ZassenhausSuzuki
