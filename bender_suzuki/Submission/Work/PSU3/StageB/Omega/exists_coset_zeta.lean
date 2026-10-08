import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.coset_sep
import Submission.Work.PSU3.StageB.Omega.fcan_eq_qconj
import Submission.Work.PSU3.StageB.Omega.fcan_mul_eq_qconj
import Submission.Work.PSU3.StageB.Omega.count_le
import Submission.Work.PSU3.StageB.Omega.count_le_self
import Submission.Work.PSU3.StageB.Omega.orbE_card
import Submission.Work.PSU3.StageB.Omega.hcan_pow_m_eq_one
import Submission.Work.PSU3.StageB.fixedUnits_card
import Submission.Work.PSU3.GaloisField.fixedField_card

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.Omega

open Work.ThmF
open Submission.Blueprint

section Cardinalities

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- `Q₀` is in bijection with the fixed field of `σE`, via `zc`. -/
noncomputable def zcEquiv (fr : CoarseFrame H Q t n) : ↥fr.Q0 ≃ {y : E n // σE y = y} where
  toFun z := ⟨frameZcPreimage fr z.1 z.2, frameZcPreimage_fixed fr z.2⟩
  invFun y := ⟨fr.zc y.1, fr.zc_mem y.1 y.2⟩
  left_inv z := Subtype.ext (zc_frameZcPreimage fr z.2)
  right_inv y := Subtype.ext
    (fr.zc_inj (frameZcPreimage fr (fr.zc y.1) (fr.zc_mem y.1 y.2)) y.1
      (frameZcPreimage_fixed fr (fr.zc_mem y.1 y.2)) y.2
      (zc_frameZcPreimage fr (fr.zc_mem y.1 y.2)))

/-- `|Q₀| = 2ⁿ`. -/
theorem card_Q0_eq (hn : 1 ≤ n) (fr : CoarseFrame H Q t n) : Nat.card ↥fr.Q0 = 2 ^ n := by
  rw [Nat.card_congr (zcEquiv fr)]
  exact Work.PSU3.GaloisField.fixedField_card n hn

/-- `κ` restricts to a bijection `KW ∩ Ksub → F*`, so `|KW ∩ Ksub| = 2ⁿ - 1`. -/
theorem card_KWcapKsub_eq (hn : 1 ≤ n) (fr : CoarseFrame H Q t n) :
    Nat.card ↥((Ksub H t).comap fr.KW.subtype) = 2 ^ n - 1 := by
  have hFX : Nat.card ↥(FX n) = 2 ^ n - 1 := fixedUnits_card n hn
  rw [← hFX]
  refine Nat.card_congr (Equiv.ofBijective (fun k : ↥((Ksub H t).comap fr.KW.subtype) =>
    (⟨fr.κ k.1, (fr.mem_K_iff k.1).mp k.2⟩ : ↥(FX n))) ⟨?_, ?_⟩)
  · intro k l hkl
    exact Subtype.ext (fr.κ_injective (Subtype.ext_iff.mp hkl))
  · intro u
    obtain ⟨d, hd⟩ := fr.K_surj u.1 u.2
    exact ⟨⟨d, (fr.mem_K_iff d).mpr (by rw [hd]; exact u.2)⟩, Subtype.ext hd⟩

/-- `|Ksub| = 2ⁿ - 1`. -/
theorem card_Ksub_eq (hn : 1 ≤ n) (fr : CoarseFrame H Q t n) :
    Nat.card ↥(Ksub H t) = 2 ^ n - 1 := by
  rw [← card_KWcapKsub_eq hn fr, Subgroup.comap_subtype]
  exact Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (H := Ksub H t) (K := fr.KW) (fr.K_le)).toEquiv.symm

/-- The bundled cardinality facts used by the counting arguments. -/
theorem omega_card_facts (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) :
    1 ≤ n ∧ Nat.card ↥fr.Q0 = 2 ^ n ∧
    Nat.card fr.KW = (2 ^ n - 1) * orderOf fr.ζ ∧
    Nat.card ↥(Ksub H t) = 2 ^ n - 1 ∧
    Nat.card fr.KW / Nat.card ↥(Ksub H t) = orderOf fr.ζ := by
  have hn : 1 ≤ n := frame_one_le_n fr
  have hQ0 : Nat.card ↥fr.Q0 = 2 ^ n := card_Q0_eq hn fr
  have hFX : Nat.card ↥(FX n) = 2 ^ n - 1 := fixedUnits_card n hn
  have hKW : Nat.card fr.KW = (2 ^ n - 1) * orderOf fr.ζ := orbE_card_KW fr hFX
  have hKsub : Nat.card ↥(Ksub H t) = 2 ^ n - 1 := card_Ksub_eq hn fr
  have hpos : 0 < 2 ^ n - 1 := by
    have h2 : 2 ≤ 2 ^ n := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  refine ⟨hn, hQ0, hKW, hKsub, ?_⟩
  rw [hKW, hKsub, Nat.mul_div_right _ hpos]

end Cardinalities

section CosetZeta

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- The counting equality of Peterfalvi §2 (8) for the self-orbit, together with §2 (5)/(7), forces
the coset `ζK` to be realised: there are `x, z ∈ Q₀` and `k ∈ K` with `f(ω x) = (ω z)^{kζ}`. -/
theorem coset_zeta_of_count (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    (hdiv : Nat.card fr.KW / Nat.card ↥(Ksub H t) = orderOf fr.ζ)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0)
    (hcount : Nat.card {x : ↥Q // (x : G) ∈ fr.Q0 ∧ ∃ d : fr.KW, ∃ y : ↥Q, (y : G) ∈ fr.Q0 ∧
        fcan hS.split (ω * x) =
          qconj hS.split
            (⟨(d : G), fr.KW_le d.2⟩ : ↥(twoPoint H t)) (ω * y)}
      = orderOf fr.ζ - 1) :
    ∃ x z : ↥Q, (x : G) ∈ fr.Q0 ∧ (z : G) ∈ fr.Q0 ∧
      ∃ k : fr.KW, ((k : G) ∈ Ksub H t) ∧
        fcan hS.split (ω * x) =
          qconj hS.split
            (⟨((k * fr.ζ : fr.KW) : G), fr.KW_le (k * fr.ζ).2⟩ :
              ↥(twoPoint H t)) (ω * z) := by
  classical
  let S : Type := {x : ↥Q // (x : G) ∈ fr.Q0 ∧ ∃ d : fr.KW, ∃ y : ↥Q, (y : G) ∈ fr.Q0 ∧
      fcan hS.split (ω * x) =
        qconj hS.split
          (⟨(d : G), fr.KW_le d.2⟩ : ↥(twoPoint H t)) (ω * y)}
  have hS_card : Nat.card S = orderOf fr.ζ - 1 := hcount
  let W : S → fr.KW := fun s => Classical.choose s.2.2
  let Y : S → ↥Q := fun s => Classical.choose (Classical.choose_spec s.2.2)
  have hY : ∀ s : S, (Y s : G) ∈ fr.Q0 :=
    fun s => (Classical.choose_spec (Classical.choose_spec s.2.2)).1
  have hW_eq : ∀ s : S, fcan hS.split (ω * s.1) =
      qconj hS.split (⟨(W s : G), fr.KW_le (W s).2⟩ : ↥(twoPoint H t)) (ω * Y s) :=
    fun s => (Classical.choose_spec (Classical.choose_spec s.2.2)).2
  let K0 : Subgroup fr.KW := (Ksub H t).comap fr.KW.subtype
  have hKm : ∀ d : fr.KW, d ∈ K0 ↔ (d : G) ∈ Ksub H t := fun d => Subgroup.mem_comap
  have hK0card : Nat.card ↥K0 = Nat.card ↥(Ksub H t) := by
    rw [show K0 = (Ksub H t).comap fr.KW.subtype from rfl, Subgroup.comap_subtype]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := Ksub H t) (K := fr.KW) (fr.K_le)).toEquiv
  have hidx : Nat.card fr.KW / Nat.card ↥(Ksub H t) = K0.index := by
    have h := Subgroup.card_mul_index K0
    rw [hK0card] at h
    rw [← h, Nat.mul_div_right K0.index Nat.card_pos]
  have htarget : Nat.card {c : fr.KW ⧸ K0 // c ≠ QuotientGroup.mk (1 : fr.KW)}
      = orderOf fr.ζ - 1 := by
    rw [natCard_subtype_ne, ← Subgroup.index_eq_card, ← hidx, hdiv]
  -- §2 (5): the trivial coset `K` is never occupied
  have hW_notin : ∀ s : S, W s ∉ K0 := by
    intro s hs
    have hmem : ((W s : fr.KW) : G) ∈ Ksub H t := (hKm (W s)).mp hs
    have hz : ((s.1⁻¹ * Y s : ↥Q) : G) ∈ fr.Q0 := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (fr.Q0).mul_mem ((fr.Q0).inv_mem s.2.1) (hY s)
    have heq : fcan hS.split (ω * s.1) =
        qconj hS.split (⟨((W s : fr.KW) : G), fr.KW_le (W s).2⟩ : ↥(twoPoint H t))
          ((ω * s.1) * (s.1⁻¹ * Y s)) := by
      rw [hW_eq s]
      refine congrArg (fun z : ↥Q => qconj hS.split
        (⟨((W s : fr.KW) : G), fr.KW_le (W s).2⟩ : ↥(twoPoint H t)) z) ?_
      apply Subtype.ext
      show ((ω : G) * (Y s : G)) = ((ω : G) * (s.1 : G)) * ((s.1 : G)⁻¹ * (Y s : G))
      group
    have hbase : ((ω * s.1 : ↥Q) : G) ∉ fr.Q0 := by
      intro hc
      have hbar : fr.bar (ω * s.1) = 1 := (fr.bar_eq_one_iff (ω * s.1)).mpr hc
      rw [map_mul, bar_eq_one_of_mem_Q0 fr s.2.1, mul_one] at hbar
      exact bar_ne_one_of_not_mem_Q0 fr hω hbar
    exact (fcan_eq_qconj hS fr hbase hz heq).2 hmem
  -- §2 (7): distinct `x`'s give distinct cosets of `K` in `KW`
  have hcoset_inj : Function.Injective (fun s : S => (QuotientGroup.mk (W s) : fr.KW ⧸ K0)) := by
    intro s1 s2 h
    by_contra hne
    have hne1 : (s1 : ↥Q) ≠ (s2 : ↥Q) := fun hh => hne (Subtype.ext hh)
    have hmem : (W s1)⁻¹ * (W s2) ∈ K0 := QuotientGroup.eq.mp h
    have hmemK : ((W s1 : fr.KW) : G)⁻¹ * ((W s2 : fr.KW) : G) ∈ Ksub H t := by
      have hh := (hKm ((W s1)⁻¹ * (W s2))).mp hmem
      simpa using hh
    exact coset_sep_KW hS fr hω hω s1.2.1 s2.2.1 hne1 (hY s1) (hY s2)
      (hW_eq s1) (hW_eq s2) hmemK
  let ψ : S → {c : fr.KW ⧸ K0 // c ≠ QuotientGroup.mk (1 : fr.KW)} :=
    fun s => ⟨QuotientGroup.mk (W s), by
      intro h
      refine hW_notin s ((Subgroup.inv_mem_iff K0).mp ?_)
      simpa using (QuotientGroup.eq.mp h)⟩
  have hψ_inj : Function.Injective ψ := by
    intro s1 s2 h
    exact hcoset_inj (congrArg Subtype.val h)
  haveI : Finite {c : fr.KW ⧸ K0 // c ≠ QuotientGroup.mk (1 : fr.KW)} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hcard_ψ : Nat.card S
      = Nat.card {c : fr.KW ⧸ K0 // c ≠ QuotientGroup.mk (1 : fr.KW)} := by
    rw [hS_card, htarget]
  have hsurj : Function.Surjective ψ :=
    ((Nat.bijective_iff_injective_and_card ψ).mpr ⟨hψ_inj, hcard_ψ⟩).2
  -- `ζ ∉ K`, so `ζK` is a nontrivial coset of `K` in `KW`
  have hzeta_notin : fr.ζ ∉ K0 := by
    intro h
    have hmem : ((fr.ζ : fr.KW) : G) ∈ Ksub H t := (hKm fr.ζ).mp h
    have hσ : σE ((fr.κ fr.ζ : (E n)ˣ) : E n) = ((fr.κ fr.ζ : (E n)ˣ) : E n) :=
      (fr.mem_K_iff fr.ζ).mp hmem
    have hone : ((fr.κ fr.ζ : (E n)ˣ) : E n) * ((fr.κ fr.ζ : (E n)ˣ) : E n) = 1 := by
      have := fr.ζ_norm
      rwa [hσ] at this
    have h1 : fr.κ fr.ζ = 1 := Units.ext (orbE_eq_one_of_mul_self_eq_one hone)
    exact fr.ζ_ne_one (fr.κ_injective (by rw [h1, map_one]))
  have hζne : (QuotientGroup.mk fr.ζ : fr.KW ⧸ K0) ≠ QuotientGroup.mk (1 : fr.KW) := by
    intro h
    exact hzeta_notin ((Subgroup.inv_mem_iff K0).mp (by simpa using (QuotientGroup.eq.mp h)))
  obtain ⟨s, hs⟩ := hsurj ⟨QuotientGroup.mk fr.ζ, hζne⟩
  have heq_mk : (QuotientGroup.mk (W s) : fr.KW ⧸ K0) = QuotientGroup.mk fr.ζ :=
    congrArg Subtype.val hs
  have hmem : (W s)⁻¹ * fr.ζ ∈ K0 := QuotientGroup.eq.mp heq_mk
  set k : fr.KW := ((W s)⁻¹ * fr.ζ)⁻¹ with hk
  have hk_mem : k ∈ K0 := K0.inv_mem hmem
  have hk_eq : k * fr.ζ = W s := by
    apply Subtype.ext
    show (((W s)⁻¹ * fr.ζ : fr.KW) : G)⁻¹ * (fr.ζ : G) = (W s : G)
    have hcomm : (W s : G) * (fr.ζ : G) = (fr.ζ : G) * (W s : G) := KW_comm fr (W s) fr.ζ
    have hcoe : (((W s)⁻¹ * fr.ζ : fr.KW) : G) = (W s : G)⁻¹ * (fr.ζ : G) := rfl
    rw [hcoe, mul_inv_rev, inv_inv]
    calc (fr.ζ : G)⁻¹ * (W s : G) * (fr.ζ : G)
        = (fr.ζ : G)⁻¹ * ((W s : G) * (fr.ζ : G)) := by group
      _ = (fr.ζ : G)⁻¹ * ((fr.ζ : G) * (W s : G)) := by rw [hcomm]
      _ = (W s : G) := by group
  refine ⟨s.1, Y s, s.2.1, hY s, k, (hKm k).mp hk_mem, ?_⟩
  rw [hk_eq]
  exact hW_eq s

end CosetZeta

section CountSelfAux

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- `qconj a` is multiplicative. -/
lemma qconj_mul_eq (hS : PSU3Hyp H Q t) (a : ↥(twoPoint H t)) (x y : ↥Q) :
    qconj hS.split a (x * y) = qconj hS.split a x * qconj hS.split a y := by
  apply Subtype.ext
  simp only [qconj_coe, Subgroup.coe_mul]
  group

/-- `qconj a⁻¹` inverts `qconj a`. -/
lemma qconj_conj_inv (hS : PSU3Hyp H Q t) (a : ↥(twoPoint H t)) (x : ↥Q) :
    qconj hS.split a (qconj hS.split a⁻¹ x) = x := by
  apply Subtype.ext
  simp only [qconj_coe, Subgroup.coe_inv]
  group

/-- The image of `qconj ⟨d⟩` in `E`: multiplication by `κ d`. -/
lemma qconj_toAdd_bar (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    (d : fr.KW) (x : ↥Q) :
    Multiplicative.toAdd (fr.bar (qconj hS.split
        (⟨(d : G), fr.KW_le d.2⟩ : ↥(twoPoint H t)) x))
      = (fr.κ d : E n) * Multiplicative.toAdd (fr.bar x) :=
  fr.act_bar d x _ (by simp [qconj_coe])

/-- The forward half of §2 (8): a witness `d, y` for `f(ω x) = (ω' y)^d` exhibits
`bar(f(ω x))` in the `KW`-orbit of `bar ω'`. -/
theorem orbE_of_cntSet (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω ω' : ↥Q} {x : ↥Q} (hx : (x : G) ∈ fr.Q0)
    {d : fr.KW} {y : ↥Q} (hy : (y : G) ∈ fr.Q0)
    (heq : fcan hS.split (ω * x) = qconj hS.split
      (⟨(d : G), fr.KW_le d.2⟩ : ↥(twoPoint H t)) (ω' * y)) :
    Multiplicative.toAdd (fr.bar (fcan hS.split (ω * x))) ∈
      orbE fr (Multiplicative.toAdd (fr.bar ω')) := by
  refine ⟨d, ?_⟩
  have hbar : fr.bar (ω' * y) = fr.bar ω' := by
    rw [map_mul, bar_eq_one_of_mem_Q0 fr hy, mul_one]
  rw [heq, qconj_toAdd_bar hS fr d (ω' * y), hbar]

/-- The backward half of §2 (8): if `bar(f(ω x))` lies in the `KW`-orbit of `bar ω'`, then
`f(ω x) = (ω' y)^d` for some `d ∈ KW`, `y ∈ Q₀`. -/
theorem cntSet_of_orbE (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω ω' : ↥Q} {x : ↥Q}
    (hb : Multiplicative.toAdd (fr.bar (fcan hS.split (ω * x))) ∈
      orbE fr (Multiplicative.toAdd (fr.bar ω'))) :
    ∃ d : fr.KW, ∃ y : ↥Q, (y : G) ∈ fr.Q0 ∧
      fcan hS.split (ω * x) = qconj hS.split
        (⟨(d : G), fr.KW_le d.2⟩ : ↥(twoPoint H t)) (ω' * y) := by
  rw [mem_orbE_iff] at hb
  obtain ⟨d, hd⟩ := hb
  refine ⟨d, qconj hS.split (⟨(d : G), fr.KW_le d.2⟩ : ↥(twoPoint H t))⁻¹
    ((fcan hS.split (ω * x))⁻¹ * qconj hS.split
      (⟨(d : G), fr.KW_le d.2⟩ : ↥(twoPoint H t)) ω')⁻¹, ?_, ?_⟩
  · have hbe : fr.bar (fcan hS.split (ω * x)) = fr.bar (qconj hS.split
        (⟨(d : G), fr.KW_le d.2⟩ : ↥(twoPoint H t)) ω') :=
      Multiplicative.toAdd.injective (by rw [hd, qconj_toAdd_bar hS fr d ω'])
    have hmem : (((fcan hS.split (ω * x))⁻¹ * qconj hS.split
        (⟨(d : G), fr.KW_le d.2⟩ : ↥(twoPoint H t)) ω' : ↥Q) : G) ∈ fr.Q0 :=
      mul_mem_Q0_of_bar_eq fr hbe
    have hmem' : ((((fcan hS.split (ω * x))⁻¹ * qconj hS.split
        (⟨(d : G), fr.KW_le d.2⟩ : ↥(twoPoint H t)) ω')⁻¹ : ↥Q) : G) ∈ fr.Q0 :=
      (fr.Q0).inv_mem hmem
    have hconj := conj_mem_Q0_of_mem_D hS fr (fr.KW_le d.2) hmem'
    simpa [qconj_coe, Subgroup.coe_inv] using hconj
  · rw [qconj_mul_eq hS, qconj_conj_inv hS]
    calc fcan hS.split (ω * x)
        = fcan hS.split (ω * x) * ((fcan hS.split (ω * x))⁻¹ * qconj hS.split
            (⟨(d : G), fr.KW_le d.2⟩ : ↥(twoPoint H t)) ω')
            * ((fcan hS.split (ω * x))⁻¹ * qconj hS.split
            (⟨(d : G), fr.KW_le d.2⟩ : ↥(twoPoint H t)) ω')⁻¹ := by group
      _ = qconj hS.split (⟨(d : G), fr.KW_le d.2⟩ : ↥(twoPoint H t)) ω'
            * ((fcan hS.split (ω * x))⁻¹ * qconj hS.split
            (⟨(d : G), fr.KW_le d.2⟩ : ↥(twoPoint H t)) ω')⁻¹ := by group

/-- **§2 (8), set identity.**  For `ω' ∉ Q₀` and `x : ↥Q`, the datum
`f(ω x) = (ω' y)^{d}` with `d ∈ KW`, `y ∈ Q₀` is equivalent to
`x ∈ Q₀` together with `bar(f(ω x))` lying in the `KW`-orbit of `bar ω'`. -/
theorem mem_cntSet_iff_orbE (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω ω' : ↥Q} (x : ↥Q) :
    ((x : G) ∈ fr.Q0 ∧ ∃ d : fr.KW, ∃ y : ↥Q, (y : G) ∈ fr.Q0 ∧
        fcan hS.split (ω * x) = qconj hS.split
          (⟨(d : G), fr.KW_le d.2⟩ : ↥(twoPoint H t)) (ω' * y))
      ↔ ((x : G) ∈ fr.Q0 ∧
          Multiplicative.toAdd (fr.bar (fcan hS.split (ω * x))) ∈
            orbE fr (Multiplicative.toAdd (fr.bar ω'))) := by
  constructor
  · rintro ⟨hx, d, y, hy, heq⟩
    exact ⟨hx, orbE_of_cntSet hS fr hx hy heq⟩
  · rintro ⟨hx, hb⟩
    exact ⟨hx, cntSet_of_orbE hS fr hb⟩

end CountSelfAux

section CountSelf

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- **Peterfalvi II Ch. VII §2 (8), self-orbit.**  The number of `x ∈ Q₀` for which
`bar(f(ω x))` lies in the `KW`-orbit of `bar ω` is exactly `|W| - 1 = orderOf ζ - 1`. -/
theorem count_self_eq_aux (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    (hcard : Nat.card ↥fr.Q0 = 2 ^ n)
    (hdiv : Nat.card fr.KW / Nat.card ↥(Ksub H t) = orderOf fr.ζ)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) :
    Nat.card {x : ↥Q // (x : G) ∈ fr.Q0 ∧ ∃ d : fr.KW, ∃ y : ↥Q, (y : G) ∈ fr.Q0 ∧
        fcan hS.split (ω * x) = qconj hS.split
          (⟨(d : G), fr.KW_le d.2⟩ : ↥(twoPoint H t)) (ω * y)}
      = orderOf fr.ζ - 1 := by
  classical
  let Ox : Type := {O : Set (E n) // ∃ a : E n, a ≠ 0 ∧ O = orbE fr a}
  haveI : Finite Ox := Finite.of_surjective
    (fun a : {a : E n // a ≠ 0} => (⟨orbE fr a.1, ⟨a.1, a.2, rfl⟩⟩ : Ox)) (by
      rintro ⟨O, a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩)
  haveI : Fintype Ox := Fintype.ofFinite Ox
  let zQ : ↥fr.Q0 → ↥Q := fun z => ⟨z.1, fr.Q0_le z.2⟩
  let g : ↥fr.Q0 → E n := fun z =>
    Multiplicative.toAdd (fr.bar (fcan hS.split (ω * zQ z)))
  have hbase_ne : ∀ z : ↥fr.Q0, ((ω * zQ z : ↥Q) : G) ∉ fr.Q0 := by
    intro z hc
    refine hω ?_
    have h2 : (ω : G) = ((ω * zQ z : ↥Q) : G) * (zQ z : G)⁻¹ := by
      rw [Subgroup.coe_mul]; group
    rw [h2]
    exact (fr.Q0).mul_mem hc ((fr.Q0).inv_mem z.2)
  have hg_ne : ∀ z : ↥fr.Q0, g z ≠ 0 := by
    intro z h
    have hbar : fr.bar (fcan hS.split (ω * zQ z)) = 1 :=
      toAdd_eq_zero.mp h
    have hmem : ((fcan hS.split (ω * zQ z) : ↥Q) : G) ∈ fr.Q0 :=
      (fr.bar_eq_one_iff (fcan hS.split (ω * zQ z))).mp hbar
    exact hbase_ne z ((fcan_mem_Q0_iff hS fr (ω * zQ z)).mp hmem)
  let ψ : ↥fr.Q0 → Ox := fun z => ⟨orbE fr (g z), ⟨g z, hg_ne z, rfl⟩⟩
  have hωbar_ne : Multiplicative.toAdd (fr.bar ω) ≠ 0 := by
    intro h
    exact bar_ne_one_of_not_mem_Q0 fr hω (toAdd_eq_zero.mp h)
  let Oω : Ox := ⟨orbE fr (Multiplicative.toAdd (fr.bar ω)), ⟨_, hωbar_ne, rfl⟩⟩
  let repOf : Ox → E n := fun O => Classical.choose O.2
  have repOf_ne : ∀ O, repOf O ≠ 0 := fun O => (Classical.choose_spec O.2).1
  have repOf_eq : ∀ O, O.1 = orbE fr (repOf O) := fun O => (Classical.choose_spec O.2).2
  let ωOf : Ox → ↥Q := fun O =>
    Classical.choose (fr.bar_surjective (Multiplicative.ofAdd (repOf O)))
  have ωOf_bar : ∀ O, fr.bar (ωOf O) = Multiplicative.ofAdd (repOf O) :=
    fun O => Classical.choose_spec (fr.bar_surjective (Multiplicative.ofAdd (repOf O)))
  have ωOf_ne : ∀ O, (ωOf O : G) ∉ fr.Q0 := by
    intro O hc
    have hbar : fr.bar (ωOf O) = 1 := (fr.bar_eq_one_iff (ωOf O)).mpr hc
    rw [ωOf_bar O] at hbar
    exact repOf_ne O (ofAdd_eq_one.mp hbar)
  have ωOf_orbit : ∀ O, O.1 = orbE fr (Multiplicative.toAdd (fr.bar (ωOf O))) := by
    intro O
    rw [ωOf_bar O]
    simpa using repOf_eq O
  have hψ_iff : ∀ (O : Ox) (z : ↥fr.Q0), ψ z = O ↔ g z ∈ O.1 := by
    intro O z
    constructor
    · intro h
      rw [← h]
      exact orbE_refl fr (g z)
    · intro h
      apply Subtype.ext
      rw [repOf_eq O] at h ⊢
      exact orbE_eq_of_mem fr h
  -- The fibre over an orbit is the counted set for a representative `ω'`.
  have fib_equiv : ∀ (O : Ox) (ω' : ↥Q),
      O.1 = orbE fr (Multiplicative.toAdd (fr.bar ω')) →
      Nat.card {z : ↥fr.Q0 // ψ z = O} = Nat.card {x : ↥Q //
        (x : G) ∈ fr.Q0 ∧ ∃ d : fr.KW, ∃ y : ↥Q, (y : G) ∈ fr.Q0 ∧
          fcan hS.split (ω * x) = qconj hS.split
            (⟨(d : G), fr.KW_le d.2⟩ : ↥(twoPoint H t)) (ω' * y)} := by
    intro O ω' hO
    refine Nat.card_congr (Equiv.ofBijective (fun z : {z : ↥fr.Q0 // ψ z = O} =>
      (⟨zQ z.1, ?_⟩ : {x : ↥Q // (x : G) ∈ fr.Q0 ∧ ∃ d : fr.KW, ∃ y : ↥Q,
        (y : G) ∈ fr.Q0 ∧ fcan hS.split (ω * x) = qconj hS.split
          (⟨(d : G), fr.KW_le d.2⟩ : ↥(twoPoint H t)) (ω' * y)})) ⟨?_, ?_⟩)
    · refine (mem_cntSet_iff_orbE hS fr (zQ z.1)).mpr ⟨z.1.2, ?_⟩
      have h := (hψ_iff O z.1).mp z.2
      rwa [hO] at h
    · intro z w hzw
      have h1 : zQ z.1 = zQ w.1 := Subtype.ext_iff.mp hzw
      have h2 : (z.1 : G) = (w.1 : G) := congrArg (fun x : ↥Q => (x : G)) h1
      exact Subtype.ext (Subtype.ext h2)
    · intro x
      refine ⟨⟨⟨x.1, ((mem_cntSet_iff_orbE hS fr x.1).mp x.2).1⟩, ?_⟩, ?_⟩
      · apply (hψ_iff O ⟨x.1, ((mem_cntSet_iff_orbE hS fr x.1).mp x.2).1⟩).mpr
        have h := ((mem_cntSet_iff_orbE hS fr x.1).mp x.2).2
        rwa [← hO] at h
      · apply Subtype.ext
        apply Subtype.ext
        rfl
  have hfib_le : ∀ O : Ox, Nat.card {z : ↥fr.Q0 // ψ z = O} ≤
      (if O = Oω then orderOf fr.ζ - 1 else orderOf fr.ζ) := by
    intro O
    by_cases hO : O = Oω
    · subst hO
      rw [if_pos rfl, fib_equiv Oω ω rfl, ← hdiv]
      exact count_le_self hS fr hω
    · rw [if_neg hO, fib_equiv O (ωOf O) (ωOf_orbit O), ← hdiv]
      exact count_le hS fr hω (ωOf_ne O)
  have hsum : Nat.card ↥fr.Q0
      = ∑ O : Ox, Nat.card {z : ↥fr.Q0 // ψ z = O} := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv ψ), Nat.card_sigma]
  have hm1 : 1 ≤ orderOf fr.ζ := orderOf_pos fr.ζ
  have hdelta : (∑ O : Ox, (if O = Oω then (1 : ℕ) else 0)) = 1 := by
    rw [Finset.sum_ite_eq']
    simp
  have hSsum : (∑ O : Ox, (if O = Oω then orderOf fr.ζ - 1 else orderOf fr.ζ)) = 2 ^ n := by
    have hite : ∀ O : Ox, (if O = Oω then orderOf fr.ζ - 1 else orderOf fr.ζ)
        = orderOf fr.ζ - (if O = Oω then 1 else 0) := by
      intro O
      by_cases h : O = Oω <;> simp [h]
    rw [Finset.sum_congr rfl (fun O _ => hite O)]
    rw [Finset.sum_tsub_distrib (Finset.univ) (f := fun _ : Ox => orderOf fr.ζ)
      (g := fun O : Ox => if O = Oω then 1 else 0) (fun O _ => by
        by_cases h : O = Oω <;> simp [h, hm1])]
    rw [hdelta, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      ← Nat.card_eq_fintype_card,
      show Nat.card Ox * orderOf fr.ζ = 2 ^ n + 1 from (orbE_card hS fr).2]
    omega
  have hfinal : Nat.card {z : ↥fr.Q0 // ψ z = Oω} = orderOf fr.ζ - 1 := by
    have h1 : (∑ O : Ox, Nat.card {z : ↥fr.Q0 // ψ z = O})
        = ∑ O : Ox, (if O = Oω then orderOf fr.ζ - 1 else orderOf fr.ζ) := by
      rw [← hsum, hcard, hSsum]
    have h2 := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := fun O : Ox => Nat.card {z : ↥fr.Q0 // ψ z = O})
      (g := fun O : Ox => if O = Oω then orderOf fr.ζ - 1 else orderOf fr.ζ)
      (fun O _ => hfib_le O)).mp h1
    have h3 := h2 Oω (Finset.mem_univ Oω)
    simpa using h3
  rw [← fib_equiv Oω ω rfl]
  exact hfinal

end CountSelf

theorem exists_coset_zeta {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) :
    ∃ x z : ↥Q, (x : G) ∈ fr.Q0 ∧ (z : G) ∈ fr.Q0 ∧
      ∃ k : fr.KW, ((k : G) ∈ Work.ThmF.Ksub H t) ∧
        Work.PSU3.StageB.fcan hS.split (ω * x) =
          Work.PSU3.StageB.qconj hS.split
            (⟨((k * fr.ζ : fr.KW) : G), fr.KW_le (k * fr.ζ).2⟩ :
              ↥(Submission.Blueprint.twoPoint H t)) (ω * z) := by
  obtain ⟨_hn, hQ0, _hKW, _hKsub, hdiv⟩ := omega_card_facts hS fr
  exact coset_zeta_of_count hS fr hdiv hω (count_self_eq_aux hS fr hQ0 hdiv hω)

end Work.PSU3.StageB.Omega
