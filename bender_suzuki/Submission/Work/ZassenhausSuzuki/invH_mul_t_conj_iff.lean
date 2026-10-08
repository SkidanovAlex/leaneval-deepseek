import Mathlib
import Submission.Work.ThmF.ChV12.lemma4
import Submission.Work.ZassenhausSuzuki.centralizer_abelian_of_strongly_real
import Submission.Work.ZassenhausSuzuki.SzSetting
import Submission.Work.ZassenhausPSL2.ZData.t_conj_eq_inv
import Submission.Work.Reductions.stronglyEmbedded_normalizer_eq
import Submission.Work.ThmF.Bender.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

open LeanEval.GroupTheory.Defs Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}

/-! ## Elementary helpers -/

/-- An element of order two is an involution. -/
private lemma sq_eq_one_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) : x * x = 1 := by
  have h := pow_orderOf_eq_one x
  rw [hx] at h
  simpa [pow_two] using h

/-- **`H ⊓ C_G(t) = 1`.**  An element of `H` commuting with `t` lies in `twoPoint H t` (it is
fixed by `t`), and `centD H t = twoPoint H t ⊓ C_G(t) = 1` by the Zassenhaus condition. -/
theorem H_inf_centralizer_t_eq_bot (h : SzHyp H Q t s) :
    H ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ := by
  have hV : centD H t = ⊥ :=
    Work.ZassenhausPSL2.ZData.centD_eq_bot_aux H Q t h.split h.zass
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
  have hcomm : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
  have htt : t * t = 1 := sq_eq_one_of_orderOf_eq_two h.split.invol
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hmem : x ∈ centD H t := by
    rw [Work.ThreePoints.mem_centD]
    refine ⟨hxH, ?_, hcomm⟩
    have hxt : t * x * t = x := by
      rw [← hcomm]
      calc x * t * t = x * (t * t) := by rw [mul_assoc]
        _ = x := by rw [htt, mul_one]
    rw [htinv, hxt]
    exact hxH
  rw [hV] at hmem
  exact Subgroup.mem_bot.mp hmem

/-- **`(u * t)² ≠ 1` for an involution `u ∈ H`.**  If `(u t)² = 1` then `u` commutes with `t`,
so `u ∈ H ⊓ H^t = twoPoint H t` is an involution in a group of odd order. -/
theorem mul_t_sq_ne_one (h : SzHyp H Q t s) {u : G}
    (hu : u ∈ Submission.Blueprint.involutions (H : Set G)) :
    (u * t) * (u * t) ≠ 1 := by
  intro hsq
  obtain ⟨huH, hu2⟩ := hu
  have huu : u * u = 1 := sq_eq_one_of_orderOf_eq_two hu2
  have htt : t * t = 1 := sq_eq_one_of_orderOf_eq_two h.split.invol
  have hcomm : u * t = t * u := by
    have h1 : (u * t)⁻¹ = u * t := inv_eq_of_mul_eq_one_right hsq
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right huu, inv_eq_of_mul_eq_one_right htt] at h1
    exact h1.symm
  have hu_eq : u = t * u * t := by
    calc u = u * (t * t) := by rw [htt, mul_one]
      _ = (u * t) * t := by group
      _ = (t * u) * t := by rw [hcomm]
  have hmem : u ∈ Submission.Blueprint.conj t H := by
    rw [Work.ThreePoints.mem_conj_iff']
    exact ⟨u, huH, by rw [inv_eq_of_mul_eq_one_right htt]; exact hu_eq⟩
  have hodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) :=
    h.split.stronglyEmbedded.2.2 t h.split.not_mem
  have hmem2 : u ∈ Submission.Blueprint.twoPoint H t :=
    Subgroup.mem_inf.mpr ⟨huH, hmem⟩
  have hdvd : 2 ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
    have h2 := Subgroup.orderOf_dvd_natCard _ hmem2
    rwa [hu2] at h2
  exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hdvd)

/-- **`C_G(u * t)` is abelian of odd order and inverted by `t`.**  Since `t` inverts `u * t`
and `(u * t)² ≠ 1`, the involution `t` acts on the odd-order group `C_G(u * t)`; the action is
fixed-point-free (a fixed point commutes with `u`, hence lies in `H ⊓ C_G(t) = 1`), so it is
inversion (Burnside). -/
theorem centralizer_mul_t_inv (h : SzHyp H Q t s) {u : G}
    (hu : u ∈ Submission.Blueprint.involutions (H : Set G)) :
    (∀ x ∈ Subgroup.centralizer ({u * t} : Set G), t * x * t⁻¹ = x⁻¹) ∧
      IsMulCommutative ↥(Subgroup.centralizer ({u * t} : Set G)) ∧
      Odd (Nat.card ↥(Subgroup.centralizer ({u * t} : Set G))) := by
  obtain ⟨huH, hu2⟩ := hu
  have htt : t * t = 1 := sq_eq_one_of_orderOf_eq_two h.split.invol
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hu_inv : u * u = 1 := sq_eq_one_of_orderOf_eq_two hu2
  have htα : t * (u * t) * t⁻¹ = (u * t)⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right htt]
    calc t * (u * t) * t = t * u * (t * t) := by group
      _ = t * u := by rw [htt, mul_one]
      _ = (u * t)⁻¹ := by
            rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hu_inv,
              inv_eq_of_mul_eq_one_right htt]
  have hfpf : ∀ y : G, y ∈ Subgroup.centralizer ({u * t} : Set G) →
      t * y * t⁻¹ = y → y = 1 := by
    intro y hy hfix
    have hycomm : y * (u * t) = (u * t) * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    have hyt : y * t = t * y := by
      have h' : t * y = y * t := by
        have hfix' : t * y * t = y := by
          rw [htinv] at hfix
          exact hfix
        calc t * y = (t * y) * (t * t) := by rw [htt, mul_one]
          _ = (t * y * t) * t := by group
          _ = y * t := by rw [hfix']
      exact h'.symm
    have hyu : y * u = u * y := by
      have h1 : (u * t) * t = u := by rw [mul_assoc, htt, mul_one]
      have s1 : y * ((u * t) * t) = (y * (u * t)) * t := by group
      have s2 : (y * (u * t)) * t = ((u * t) * y) * t := by rw [hycomm]
      have s3 : ((u * t) * y) * t = (u * t) * (y * t) := by group
      have s4 : (u * t) * (y * t) = (u * t) * (t * y) := by rw [hyt]
      have s5 : (u * t) * (t * y) = ((u * t) * t) * y := by group
      have s6 : ((u * t) * t) * y = u * y := by rw [h1]
      calc y * u = y * ((u * t) * t) := by rw [h1]
        _ = (y * (u * t)) * t := s1
        _ = ((u * t) * y) * t := s2
        _ = (u * t) * (y * t) := s3
        _ = (u * t) * (t * y) := s4
        _ = ((u * t) * t) * y := s5
        _ = u * y := s6
    have hyH : y ∈ H :=
      Work.ThmF.centralizer_involution_le h.split.stronglyEmbedded huH hu2
        (Subgroup.mem_centralizer_singleton_iff.mpr hyu)
    have hybot : y ∈ H ⊓ Subgroup.centralizer ({t} : Set G) :=
      ⟨hyH, Subgroup.mem_centralizer_singleton_iff.mpr hyt⟩
    rw [H_inf_centralizer_t_eq_bot h] at hybot
    exact Subgroup.mem_bot.mp hybot
  have hα2 : (u * t) * (u * t) ≠ 1 := mul_t_sq_ne_one h ⟨huH, hu2⟩
  refine ⟨(inv_of_involution_of_fpf htt htα hfpf).1,
    (inv_of_involution_of_fpf htt htα hfpf).2, ?_⟩
  exact (centralizer_abelian_of_strongly_real h.split h.zass h.two hα2
    ⟨u, t, hu_inv, htt, rfl⟩).2.1

/-! ## The main statement -/

/-- **Suzuki 1962, Proposition 13 (second half).**

If `u, u'` are involutions of `H` and `u * t` is conjugate to `u' * t`, then `u = u'`.
Equivalently the map `u ↦` (class of `u * t`) is injective on `Inv(H)`; combined with
`Work.ThmF.ChV12.exists_conj_eq_inv_mul_t` (every strongly real `x` with `x * x ≠ 1` is conjugate
to some `u * t`) this says that the strongly real elements `≠ 1` of `G` fall into exactly
`1 + #Inv(H)` conjugacy classes, which is the count input of Suzuki 1962 §8.

(Quantifying over `involutions (H)` rather than `involutions (Q)` is harmless:
`QSZ_invH_le_centerQ` gives `Inv(H) ⊆ Q`, and `Q ≤ H` gives the converse.)

Route (Suzuki's proof; the Sylow step needs the rank-one structure, not just oddness).
`u` inverts `u * t`, so `⟨u, t⟩ ≤ N_G(⟨u * t⟩)` is dihedral; `u * t` has odd order (if
`(u t)² = 1` then `u` commutes with `t`, giving an involution in `H ⊓ Hᵗ`, contradicting strong
embedding) and `C_G(u * t)` has odd order
(`Work.ZassenhausSuzuki.centralizer_abelian_of_strongly_real`).  With the (ZT)-structure this
makes `{t}` a Sylow `2`-subgroup of `N_G(⟨u * t⟩)`, so a `G`-conjugacy `u * t ~ u' * t` is
realised in `C_G(t)`; that element conjugates `u ∈ H` to `u' ∈ H`, hence lies in `H` (strong
embedding), while `C_G(t) ⊓ H = 1` (a `2`-element of `H` lies in `Q`, and
`Q ⊓ twoPoint H t = ⊥`).

Useful ingredients already in the workspace: `Work.ThmF.Bender.centralizer_involution_le`
(`C_G` of an involution of `H` lies in `H`), `Work.ZassenhausSuzuki.isPGroup_centralizer_involution`
(in `singer_centralizer_eq.lean`: `C_G` of *any* involution is a `2`-group), and
`Work.ZassenhausSuzuki.SzHyp.hcomm`. -/
theorem invH_mul_t_conj_iff {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (h : Work.ZassenhausSuzuki.SzHyp H Q t s) :
    ∀ u u' : G, u ∈ Submission.Blueprint.involutions (H : Set G) →
      u' ∈ Submission.Blueprint.involutions (H : Set G) →
      (∃ g : G, g * (u * t) * g⁻¹ = u' * t) → u = u' := by
  intro u u' hu hu' ⟨g, hg⟩
  obtain ⟨huH, hu2⟩ := hu
  obtain ⟨hu'H, hu'2⟩ := hu'
  have huu : u * u = 1 := sq_eq_one_of_orderOf_eq_two hu2
  have hu'u' : u' * u' = 1 := sq_eq_one_of_orderOf_eq_two hu'2
  have htt : t * t = 1 := sq_eq_one_of_orderOf_eq_two h.split.invol
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨hαinv, hαabel, hαodd⟩ := centralizer_mul_t_inv h ⟨huH, hu2⟩
  -- `w := g⁻¹ u' g` inverts `u * t`
  set w : G := g⁻¹ * u' * g with hwdef
  have hu'β : u' * (u' * t) * u'⁻¹ = (u' * t)⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right hu'u', mul_inv_rev,
      inv_eq_of_mul_eq_one_right hu'u', inv_eq_of_mul_eq_one_right htt]
    calc u' * (u' * t) * u' = (u' * u') * t * u' := by group
      _ = (1 : G) * t * u' := by rw [hu'u']
      _ = t * u' := by rw [one_mul]
  have hginv : g * (u * t)⁻¹ * g⁻¹ = (u' * t)⁻¹ := by
    have hc : (g * (u * t) * g⁻¹)⁻¹ = (u' * t)⁻¹ := congrArg Inv.inv hg
    calc g * (u * t)⁻¹ * g⁻¹ = (g * (u * t) * g⁻¹)⁻¹ := by group
      _ = (u' * t)⁻¹ := hc
  have hwinv : w * (u * t) * w⁻¹ = (u * t)⁻¹ := by
    rw [hwdef]
    calc (g⁻¹ * u' * g) * (u * t) * (g⁻¹ * u' * g)⁻¹
        = g⁻¹ * (u' * (g * (u * t) * g⁻¹) * u'⁻¹) * g := by group
      _ = g⁻¹ * (u' * (u' * t) * u'⁻¹) * g := by rw [hg]
      _ = g⁻¹ * (u' * t)⁻¹ * g := by rw [hu'β]
      _ = (u * t)⁻¹ := by rw [← hginv]; group
  -- `u` lies in the generalized centralizer of `u * t` too
  have huinv : u * (u * t) * u⁻¹ = (u * t)⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right huu, mul_inv_rev,
      inv_eq_of_mul_eq_one_right huu, inv_eq_of_mul_eq_one_right htt]
    calc u * (u * t) * u = (u * u) * t * u := by group
      _ = (1 : G) * t * u := by rw [huu]
      _ = t * u := by rw [one_mul]
  -- the two "reflections" `t * u` and `t * w` of `C*(u * t)`
  let A : Subgroup G := Subgroup.centralizer ({u * t} : Set G)
  have hcu_mem : t * u ∈ A := by
    show (t * u) ∈ Subgroup.centralizer ({u * t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : (t * u) * (u * t) = 1 := by
      calc (t * u) * (u * t) = t * (u * u) * t := by group
        _ = t * (1 : G) * t := by rw [huu]
        _ = 1 := by rw [mul_one, htt]
    have h2 : (u * t) * (t * u) = 1 := by
      calc (u * t) * (t * u) = u * (t * t) * u := by group
        _ = u * (1 : G) * u := by rw [htt]
        _ = 1 := by rw [mul_one, huu]
    rw [h1, h2]
  have hcommA : ∀ x y : G, x ∈ A → y ∈ A → x * y = y * x := by
    intro x y hx hy
    haveI : IsMulCommutative ↥A := hαabel
    have hh := mul_comm' (M := ↥A) ⟨x, hx⟩ ⟨y, hy⟩
    simpa using congrArg Subtype.val hh
  have htwα : (t * w) * (u * t) * (t * w)⁻¹ = u * t := by
    have htα : t * (u * t) * t⁻¹ = (u * t)⁻¹ := by
      rw [inv_eq_of_mul_eq_one_right htt]
      calc t * (u * t) * t = t * u * (t * t) := by group
        _ = t * u := by rw [htt, mul_one]
        _ = (u * t)⁻¹ := by
              rw [mul_inv_rev, inv_eq_of_mul_eq_one_right huu,
                inv_eq_of_mul_eq_one_right htt]
    have htαinv : t * (u * t)⁻¹ * t⁻¹ = u * t := by
      rw [← htα]
      calc t * (t * (u * t) * t⁻¹) * t⁻¹ = (t * t) * (u * t) * (t⁻¹ * t⁻¹) := by group
        _ = (1 : G) * (u * t) * (1 : G) := by
              rw [htt]
              have h2 : t⁻¹ * t⁻¹ = 1 := by rw [htinv, htt]
              rw [h2]
        _ = u * t := by rw [one_mul, mul_one]
    calc (t * w) * (u * t) * (t * w)⁻¹
        = t * (w * (u * t) * w⁻¹) * t⁻¹ := by group
      _ = t * (u * t)⁻¹ * t⁻¹ := by rw [hwinv]
      _ = u * t := htαinv
  have hcw_mem : t * w ∈ A := by
    show (t * w) ∈ Subgroup.centralizer ({u * t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (t * w) * (u * t) = ((t * w) * (u * t) * (t * w)⁻¹) * (t * w) := by group
      _ = (u * t) * (t * w) := by rw [htwα]
  -- `e ∈ A` with `e² = (t * u) * (t * w)⁻¹`
  set di : G := (t * u) * (t * w)⁻¹ with hdi
  have hdi_mem : di ∈ A := A.mul_mem hcu_mem (A.inv_mem hcw_mem)
  have hdi_odd : Odd (orderOf di) := hαodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard A hdi_mem)
  obtain ⟨k, hk⟩ := hdi_odd
  set e : G := di ^ (k + 1) with he
  have he_mem : e ∈ A := Subgroup.pow_mem A hdi_mem (k + 1)
  have he_sq : e * e = di := by
    rw [he]
    calc di ^ (k + 1) * di ^ (k + 1) = di ^ ((k + 1) + (k + 1)) := by rw [← pow_add]
      _ = di ^ ((2 * k + 1) + 1) := by
            rw [show (k + 1) + (k + 1) = (2 * k + 1) + 1 by ring]
      _ = di ^ (2 * k + 1) * di := by rw [pow_succ]
      _ = di ^ (orderOf di) * di := by rw [← hk]
      _ = 1 * di := by rw [pow_orderOf_eq_one]
      _ = di := by rw [one_mul]
  -- `e` conjugates `u` to `w`
  have het : e * t = t * e⁻¹ := by
    have he_inv : t * e * t⁻¹ = e⁻¹ := hαinv e he_mem
    have h1 : t * e * t = e⁻¹ := by rwa [htinv] at he_inv
    have h2 : (e * t) * (e * t) = 1 := by
      calc (e * t) * (e * t) = e * (t * e * t) := by group
        _ = e * e⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel e
    have h3 : (e * t)⁻¹ = e * t := inv_eq_of_mul_eq_one_right h2
    rw [mul_inv_rev, htinv] at h3
    exact h3.symm
  have heu : e * u * e⁻¹ = w := by
    have hcu_eq : u = t * (t * u) := by rw [← mul_assoc, htt, one_mul]
    have hw_eq : w = t * (t * w) := by rw [← mul_assoc, htt, one_mul]
    have hee : e⁻¹ * e⁻¹ = di⁻¹ := by rw [← mul_inv_rev, he_sq]
    have hcudi : (t * u) * di⁻¹ = t * w := by
      have h1 : di⁻¹ = (t * w) * (t * u)⁻¹ := by rw [hdi, mul_inv_rev, inv_inv]
      rw [h1]
      calc (t * u) * ((t * w) * (t * u)⁻¹) = ((t * u) * (t * w)) * (t * u)⁻¹ := by group
        _ = ((t * w) * (t * u)) * (t * u)⁻¹ := by rw [hcommA (t * u) (t * w) hcu_mem hcw_mem]
        _ = (t * w) * ((t * u) * (t * u)⁻¹) := by group
        _ = (t * w) * 1 := by rw [mul_inv_cancel]
        _ = t * w := by rw [mul_one]
    calc e * u * e⁻¹
        = e * (t * (t * u)) * e⁻¹ := by conv_lhs => rw [hcu_eq]
      _ = (e * t) * ((t * u) * e⁻¹) := by group
      _ = (t * e⁻¹) * ((t * u) * e⁻¹) := by rw [het]
      _ = t * (e⁻¹ * ((t * u) * e⁻¹)) := by group
      _ = t * ((e⁻¹ * (t * u)) * e⁻¹) := by group
      _ = t * (((t * u) * e⁻¹) * e⁻¹) := by
            rw [hcommA e⁻¹ (t * u) (A.inv_mem he_mem) hcu_mem]
      _ = t * ((t * u) * (e⁻¹ * e⁻¹)) := by group
      _ = t * ((t * u) * di⁻¹) := by rw [hee]
      _ = t * (t * w) := by rw [hcudi]
      _ = w := by rw [← hw_eq]
  -- `c₀ := g * e` centralizes `t` and conjugates `u` to `u'`, so lies in `H` and is `1`
  set c₀ : G := g * e with hc0
  have hc0u : c₀ * u * c₀⁻¹ = u' := by
    rw [hc0]
    calc (g * e) * u * (g * e)⁻¹ = g * (e * u * e⁻¹) * g⁻¹ := by group
      _ = g * w * g⁻¹ := by rw [heu]
      _ = u' := by rw [hwdef]; group
  have hc0α : c₀ * (u * t) * c₀⁻¹ = u' * t := by
    have hec : e * (u * t) * e⁻¹ = u * t := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp he_mem]
      group
    rw [hc0]
    calc (g * e) * (u * t) * (g * e)⁻¹ = g * (e * (u * t) * e⁻¹) * g⁻¹ := by group
      _ = g * (u * t) * g⁻¹ := by rw [hec]
      _ = u' * t := hg
  have hc0t : c₀ * t * c₀⁻¹ = t := by
    have h1 : c₀ * (u * t) * c₀⁻¹ = (c₀ * u * c₀⁻¹) * (c₀ * t * c₀⁻¹) := by group
    rw [hc0u, hc0α] at h1
    exact (mul_left_cancel h1).symm
  have hc0C : c₀ ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c₀ * t = (c₀ * t * c₀⁻¹) * c₀ := by group
      _ = t * c₀ := by rw [hc0t]
  have hc0H : c₀ ∈ H := by
    have hmem : u' ∈ Submission.Blueprint.conj c₀ H := by
      rw [Work.ThreePoints.mem_conj_iff']
      exact ⟨u, huH, by rw [← hc0u]⟩
    have hconj :=
      Work.ThmF.conj_eq_self_of_involution_mem h.split.stronglyEmbedded hu'H hu'2 hmem
    have hnorm : c₀ ∈ Subgroup.normalizer (H : Set G) :=
      Work.Models.mem_normalizer_of_conj_eq hconj
    rwa [Work.Reductions.stronglyEmbedded_normalizer_eq h.split.stronglyEmbedded] at hnorm
  have hc0bot : c₀ ∈ H ⊓ Subgroup.centralizer ({t} : Set G) := ⟨hc0H, hc0C⟩
  rw [H_inf_centralizer_t_eq_bot h] at hc0bot
  have hc0one : c₀ = 1 := Subgroup.mem_bot.mp hc0bot
  rw [hc0one, one_mul, inv_one, mul_one] at hc0u
  exact hc0u

end Work.ZassenhausSuzuki
