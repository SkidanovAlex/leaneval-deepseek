/-
# Peterfalvi, Appendix I (5)(b)

This file proves `Work.NormalComplement.appI_five_b`, the statement "`K = Kapp t X` is a normal
complement of `V = C_X(t)` in `X`" of Peterfalvi, *Le théorème de Bender–Suzuki I*, Appendix I
(5)(b) (p. 201): with `d` prime, `t ∈ G` of order `d`, `X` a finite solvable subgroup normalised
by `t` with `|X|` prime to `d`, and `K = {t⁻¹x⁻¹tx | x ∈ X}`, if `|K|` is coprime to the order of
the Fitting subgroup `F(V)` of `V = C_G(t) ⊓ X`, then there is a subgroup `K' ≤ X` with underlying
set `Kapp t X` which is a normal complement of `V` in `X` (i.e. `K' ∩ V = 1` and `K'V = X`).

Route (following the source, with the pieces in their own modules):

* `coprime_ncard_closure_kapp` (App. I (5)(a), `appI_five_a`) turns the coprimality hypothesis on
  `|K| = |Kapp t X|` into a coprimality hypothesis on `|⟨K⟩| = |Nat.card ↥(closure (Kapp t X))|`:
  the two numbers have the same prime divisors.
* `eq_bot_of_coprime_fitting` (Fitting's theorem `Work.Fitting.centralizer_fitting_le`) then gives
  `V ⊓ ⟨K⟩ = ⊥`: this subgroup is normalised by `V`, its order is coprime to `|F(V)|`, so it is
  trivial (a normal subgroup of `V` commuting with `F(V)` lies in `F(V)`).
* `exists_normalComplement_of_inf_eq_bot` (App. I (4), `appI_four`) converts `⟨K⟩ ⊓ V = ⊥` into the
  conclusion: `|⟨K⟩| = |K| · |V ⊓ ⟨K⟩| = |K|`, so `K` is the underlying set of the subgroup `⟨K⟩`,
  which by App. I (4) satisfies `⟨K⟩ ≤ X`, `X ≤ N(⟨K⟩)` and `⟨K⟩V = X`.
-/
import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.appI_one
import Submission.Work.NormalComplement.appI_four
import Submission.Work.NormalComplement.appI_five_a
import Submission.Work.Fitting.centralizer_fitting_le
import Submission.Work.NormalComplement.coprime_ncard_closure_kapp
import Submission.Work.NormalComplement.eq_bot_of_coprime_fitting
import Submission.Work.NormalComplement.exists_normalComplement_of_inf_eq_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open Classical
open scoped Pointwise

namespace Work.NormalComplement

theorem appI_five_b {G : Type*} [Group G] [Finite G] {d : ℕ} (hd : d.Prime) {t : G}
    (ht : orderOf t = d) {X : Subgroup G} (htX : Work.NormalComplement.NormalizedBy t X)
    (hdX : Nat.Coprime (Nat.card X) d) (hsolv : Group.IsSolvable X)
    (hcop : Nat.Coprime (Work.NormalComplement.Kapp t X).ncard
      (Nat.card ↥(Work.Fitting.fitting ↥(Subgroup.centralizer ({t} : Set G) ⊓ X)))) :
    ∃ K : Subgroup G, (K : Set G) = Work.NormalComplement.Kapp t X ∧
      Work.NormalComplement.IsNormalComplementOf K (Subgroup.centralizer ({t} : Set G) ⊓ X) X := by
  classical
  -- `V = C_X(t)` and `N = ⟨Kapp t X⟩`.
  let V : Subgroup G := Subgroup.centralizer ({t} : Set G) ⊓ X
  let N : Subgroup G := Subgroup.closure (Kapp t X)
  -- `V`, a subgroup of the solvable group `X`, is solvable.
  haveI hsolvX : Group.IsSolvable ↥X := hsolv
  haveI hsolvV : Group.IsSolvable ↥V :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (show V ≤ X from inf_le_right))
      (Subgroup.inclusion_injective (show V ≤ X from inf_le_right))
  -- App. I (5)(a): `|⟨K⟩|` is coprime to `|F(V)|`.
  have hcopC : Nat.Coprime (Nat.card ↥(Subgroup.closure (Kapp t X)))
      (Nat.card ↥(Work.Fitting.fitting ↥(Subgroup.centralizer ({t} : Set G) ⊓ X))) :=
    coprime_ncard_closure_kapp hd ht htX hdX hsolv hcop
  -- App. I (4): `X` normalises `⟨K⟩`.
  obtain ⟨-, -, hXnorm, -, -, -, -⟩ := appI_four hd ht htX hdX
  -- `V ⊓ N` is normalised by `V`.
  have hnorm : ∀ v ∈ V, ∀ m ∈ V ⊓ N, v * m * v⁻¹ ∈ V ⊓ N := by
    intro v hv m hm
    refine ⟨⟨(Subgroup.centralizer ({t} : Set G)).mul_mem
        ((Subgroup.centralizer ({t} : Set G)).mul_mem hv.1 hm.1.1)
        ((Subgroup.centralizer ({t} : Set G)).inv_mem hv.1),
      X.mul_mem (X.mul_mem hv.2 hm.1.2) (X.inv_mem hv.2)⟩, hXnorm v hv.2 m hm.2⟩
  -- `|V ⊓ N|` is coprime to `|F(V)|` as well.
  have hcopM : Nat.Coprime (Nat.card ↥(V ⊓ N))
      (Nat.card ↥(Work.Fitting.fitting ↥V)) :=
    hcopC.coprime_dvd_left (Subgroup.card_dvd_of_le (inf_le_right : V ⊓ N ≤ N))
  -- Fitting's theorem: a `V`-normal subgroup of order coprime to `|F(V)|` is trivial.
  have hM : V ⊓ N = ⊥ :=
    eq_bot_of_coprime_fitting V (V ⊓ N) hsolvV inf_le_left hnorm hcopM
  -- App. I (4) turns `⟨K⟩ ⊓ V = 1` into the normal complement.
  refine exists_normalComplement_of_inf_eq_bot hd ht htX hdX ?_
  rw [inf_comm]
  exact hM

end Work.NormalComplement
