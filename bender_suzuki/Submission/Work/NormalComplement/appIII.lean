import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.appIII_inv
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore
import Submission.Work.BrauerSuzuki.OddCore.le_of_normal_odd
import Submission.Work.Fitting.exists_isMinimalNormal_le
import Submission.Work.Hall.MinimalNormal.hall_minimalNormal_isElementaryAbelian
import Submission.Work.Frobenius.Complement.isPGroup_isCyclic_of_no_basicGroup
import Submission.Work.Frobenius.Complement.isPGroup_abelian_fpf_isCyclic
import Submission.Work.DoubleTransitivity.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Classical
open scoped Pointwise
open LeanEval.GroupTheory.Defs

namespace Work.NormalComplement

/-! ## Auxiliary lemmas for Peterfalvi I Appendix III (2)–(5) -/

/-- `C_p × C_p` is not cyclic. -/
theorem not_isCyclic_zmod_prod {p : ℕ} (hp : p.Prime) :
    ¬ IsCyclic (Multiplicative (ZMod p × ZMod p)) := by
  rw [show IsCyclic (Multiplicative (ZMod p × ZMod p)) ↔
      IsCyclic (Multiplicative (ZMod p) × Multiplicative (ZMod p)) from Iff.rfl]
  rw [Group.isCyclic_prod_iff]
  rintro ⟨-, -, hcop⟩
  rw [show Nat.card (Multiplicative (ZMod p)) = p from Nat.card_zmod p] at hcop
  exact hp.ne_one (Nat.coprime_self p |>.mp hcop)

/-- **A nontrivial normal subgroup of odd order has an elementary abelian normal subgroup of
prime exponent.**  Used for App. III (2): `O_{2'}(F) ≠ 1` has odd order, hence is solvable by
Feit–Thompson, and a minimal normal subgroup of `F` inside it is abelian of exponent a prime. -/
theorem exists_elementary_abelian_normal {F : Type} [Group F] [Finite F] {O : Subgroup F}
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hOn : O.Normal) (hOne : O ≠ ⊥) (hOodd : Odd (Nat.card ↥O)) :
    ∃ (f : ℕ) (Q : Subgroup F), f.Prime ∧ Q.Normal ∧ Q ≠ ⊥ ∧ Q ≤ O ∧
      (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) ∧ (∀ x ∈ Q, x ^ f = 1) := by
  obtain ⟨M, hMmin, hMle⟩ := Work.Fitting.exists_isMinimalNormal_le F hOn hOne
  obtain ⟨hMn, hMne, hMmin'⟩ := hMmin
  have hModd : Odd (Nat.card ↥M) := Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le hMle)
  haveI : Group.IsSolvable ↥M := hFT ↥M hModd
  have hHall : Work.Hall.IsMinimalNormal M :=
    ⟨hMn, hMne, fun N hNn hNle hNne => le_of_eq (hMmin' N hNn hNle hNne).symm⟩
  obtain ⟨f, hfp, hEA⟩ :=
    Work.Hall.MinimalNormal.hall_minimalNormal_isElementaryAbelian hHall inferInstance
  refine ⟨f, M, hfp, hMn, hMne, hMle, ?_, ?_⟩
  · haveI : IsMulCommutative ↥M := hEA.1
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥M) ⟨y, hy⟩)
  · intro x hx
    exact congrArg Subtype.val (hEA.2 (⟨x, hx⟩ : ↥M))

/-- **A `p`-group (`p` odd) acting fixed-point-freely on a nontrivial normal subgroup is cyclic**
(Peterfalvi App. III (5); Huppert V.8.7).  The proof reduces to the two classical facts
`isPGroup_abelian_fpf_isCyclic` (an abelian `p`-group acting fixed-point-freely is cyclic) and
`isPGroup_isCyclic_of_no_basicGroup` (a `p`-group of odd order without a `C_p × C_p` is
cyclic). -/
theorem isCyclic_of_isPGroup_fpf {F : Type*} [Group F] [Finite F] {Q R : Subgroup F}
    (hQn : Q.Normal) (hQne : Q ≠ ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hRp : IsPGroup p R)
    (hfpf : ∀ r ∈ R, r ≠ 1 → ∀ x ∈ Q, r * x * r⁻¹ = x → x = 1) :
    IsCyclic R := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hQN : Q.Normal := hQn
  haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQne
  refine Work.Frobenius.Complement.isPGroup_isCyclic_of_no_basicGroup hp hp2 hRp ?_
  rintro V ⟨e⟩
  -- `V ≅ C_p × C_p` is an abelian `p`-group acting fixed-point-freely on `Q`, hence cyclic
  have hcard : Nat.card ↥V = p ^ 2 := by
    rw [Nat.card_congr e.toEquiv,
      show Nat.card (Multiplicative (ZMod p × ZMod p)) =
        Nat.card (ZMod p × ZMod p) from rfl, Nat.card_prod, Nat.card_zmod]
    ring
  have hVp : IsPGroup p ↥V := IsPGroup.of_card hcard
  haveI : IsMulCommutative ↥V := by
    rw [isMulCommutative_iff]
    intro a b
    exact e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
  have hfp : ∀ a : ↥V, a ≠ 1 → ∀ n : ↥Q,
      ((MulAut.conjNormal (H := Q)).comp (R.subtype.comp V.subtype)) a n = n → n = 1 := by
    intro a ha n hn
    have h1 : (((V.subtype a : ↥R)) : F) * (n : F) * (((V.subtype a : ↥R)) : F)⁻¹ = (n : F) := by
      have := congrArg (fun x : ↥Q => (x : F)) hn
      simpa [MulAut.conjNormal_apply] using this
    have hane : ((V.subtype a : ↥R) : F) ≠ 1 := by
      intro h
      exact ha (V.subtype_injective (Subtype.ext h))
    exact Subtype.ext (hfpf _ (V.subtype a).2 hane _ n.2 h1)
  have hcyc : IsCyclic ↥V :=
    Work.Frobenius.Complement.isPGroup_abelian_fpf_isCyclic hp hVp _ hfp
  exact not_isCyclic_zmod_prod hp ((MulEquiv.isCyclic e).mp hcyc)

/-- **The block argument of App. III (2).**  If a normal abelian `Q ⊄ F_a` and `F_a` is a maximal
subgroup, then `F = Q ⋊ F_a` (`Q` transitive on the points, `Q ⊓ F_a = 1`), and `F_a`
centralises nothing of `Q`. -/
theorem block_facts {F : Type*} [Group F] {α : Type*} [MulAction F α] (a : α)
    (htrans : MulAction.IsPretransitive F α)
    (hfaith : ∀ g : F, (∀ x : α, g • x = x) → g = 1)
    {Q : Subgroup F} (hQn : Q.Normal)
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hQnle : ¬ Q ≤ MulAction.stabilizer F a)
    (hHmax : IsCoatom (MulAction.stabilizer F a)) :
    (∀ b : α, ∃ q ∈ Q, q • a = b) ∧
      MulAction.stabilizer F a ⊓ Subgroup.centralizer (Q : Set F) = ⊥ ∧
      Q ⊓ MulAction.stabilizer F a = ⊥ ∧ Q ⊔ MulAction.stabilizer F a = ⊤ := by
  haveI hQN : Q.Normal := hQn
  haveI : MulAction.IsPretransitive F α := htrans
  -- `Q ⊔ F_a = ⊤`, since `Q` is not contained in the maximal subgroup `F_a`
  have hsup : Q ⊔ MulAction.stabilizer F a = ⊤ := by
    obtain ⟨q, hqQ, hqH⟩ := SetLike.not_le_iff_exists.mp hQnle
    exact (SetLike.isCoatom_iff.mp hHmax).2 (Q ⊔ MulAction.stabilizer F a) q
      le_sup_right hqH (Subgroup.mem_sup_left hqQ)
  -- `Q` is transitive
  have htransQ : ∀ b : α, ∃ q ∈ Q, q • a = b := by
    intro b
    obtain ⟨f, hf⟩ := MulAction.IsPretransitive.exists_smul_eq (M := F) a b
    obtain ⟨q, hq, h, hh, hqh⟩ := Subgroup.mem_sup_of_normal_left.mp
      ((le_of_eq hsup.symm) (Subgroup.mem_top f))
    refine ⟨q, hq, ?_⟩
    calc q • a = q • (h • a) := by rw [MulAction.mem_stabilizer_iff.mp hh]
      _ = (q * h) • a := (mul_smul q h a).symm
      _ = f • a := by rw [hqh]
      _ = b := hf
  -- `F_a` centralises nothing of `Q`
  have hHCQ : MulAction.stabilizer F a ⊓ Subgroup.centralizer (Q : Set F) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    refine hfaith x ?_
    intro b
    obtain ⟨q, hq, hqb⟩ := htransQ b
    have hxH : x ∈ MulAction.stabilizer F a := (Subgroup.mem_inf.mp hx).1
    have hxC : x ∈ Subgroup.centralizer (Q : Set F) := (Subgroup.mem_inf.mp hx).2
    have hcomm : x * q = q * x := ((Subgroup.mem_centralizer_iff.mp hxC) q hq).symm
    calc x • b = x • (q • a) := by rw [← hqb]
      _ = (x * q) • a := (mul_smul x q a).symm
      _ = (q * x) • a := by rw [hcomm]
      _ = q • (x • a) := mul_smul q x a
      _ = q • a := by rw [MulAction.mem_stabilizer_iff.mp hxH]
      _ = b := hqb
  -- `Q ⊓ F_a = ⊥`, since `Q` is abelian
  have hQH : Q ⊓ MulAction.stabilizer F a = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : x ∈ MulAction.stabilizer F a ⊓ Subgroup.centralizer (Q : Set F) := by
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hQab x (Subgroup.mem_inf.mp hx).1 y hy).symm
    rw [hHCQ] at hx'
    exact Subgroup.mem_bot.mp hx'
  exact ⟨htransQ, hHCQ, hQH, hsup⟩

/-- **Two-point stabilisers of a 2-transitive action have the same order.** -/
theorem stabilizer_inf_card_eq {F : Type*} [Group F] {α : Type*} [MulAction F α]
    (h2 : MulAction.IsMultiplyPretransitive F α 2)
    {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) :
    Nat.card ↥(MulAction.stabilizer F a ⊓ MulAction.stabilizer F b) =
      Nat.card ↥(MulAction.stabilizer F c ⊓ MulAction.stabilizer F d) := by
  obtain ⟨g, hga, hgb⟩ := MulAction.is_two_pretransitive_iff.mp h2 hab hcd
  set φ : F →* F := (MulAut.conj g).toMonoidHom with hφ
  have hφinj : Function.Injective φ := fun x y h => (MulAut.conj g).injective h
  have hmap : Subgroup.map φ (MulAction.stabilizer F a ⊓ MulAction.stabilizer F b)
      = MulAction.stabilizer F c ⊓ MulAction.stabilizer F d := by
    rw [Subgroup.map_inf_eq _ _ φ hφinj]
    refine congrArg₂ (· ⊓ ·) ?_ ?_
    · rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj g a, hga]
    · rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj g b, hgb]
  rw [← hmap, Subgroup.card_map_of_injective hφinj]

/-- **App. III (5), fixed-point-freeness part.**  In a 2-transitive action with point stabiliser
`F_a`, a `p`-subgroup `R ≤ F_a` acts fixed-point-freely on a normal subgroup `Q` meeting `F_a`
trivially, provided `p` does not divide the order of any two-point stabiliser. -/
theorem fpf_on_of_not_dvd {F : Type*} [Group F] [Finite F] {α : Type*} [MulAction F α] (a : α)
    {p : ℕ} (hp : p.Prime)
    (hpdvd : ∀ c d : α, c ≠ d →
      ¬ p ∣ Nat.card ↥(MulAction.stabilizer F c ⊓ MulAction.stabilizer F d))
    {Q : Subgroup F} (hQinf : Q ⊓ MulAction.stabilizer F a = ⊥)
    (R : Subgroup F) (hR : R ≤ MulAction.stabilizer F a) (hRp : IsPGroup p R) :
    ∀ r ∈ R, r ≠ 1 → ∀ x ∈ Q, r * x * r⁻¹ = x → x = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro r hr hr1 x hx hfix
  by_contra hx1
  -- `x ∉ F_a`
  have hxa : x ∉ MulAction.stabilizer F a := by
    intro hxs
    have : x ∈ Q ⊓ MulAction.stabilizer F a := Subgroup.mem_inf.mpr ⟨hx, hxs⟩
    rw [hQinf] at this
    exact hx1 (Subgroup.mem_bot.mp this)
  have hbne : x • a ≠ a := fun h => hxa (MulAction.mem_stabilizer_iff.mpr h)
  -- `r` commutes with `x`
  have hcomm : r * x = x * r := by
    calc r * x = r * x * r⁻¹ * r := by group
      _ = x * r := by rw [hfix]
  -- `r ≠ 1` lies in the two-point stabiliser of `(a, x • a)`
  have hrmem : r ∈ MulAction.stabilizer F a ⊓ MulAction.stabilizer F (x • a) := by
    refine Subgroup.mem_inf.mpr ⟨hR hr, ?_⟩
    rw [MulAction.mem_stabilizer_iff, smul_smul, hcomm, ← smul_smul,
      MulAction.mem_stabilizer_iff.mp (hR hr)]
  -- whose order is prime to `p`, whereas `p ∣ orderOf r`
  obtain ⟨k, hk⟩ := hRp (⟨r, hr⟩ : ↥R)
  have hkF : r ^ (p ^ k) = 1 := by
    have := congrArg (fun y : ↥R => (y : F)) hk
    simpa using this
  have horddvd' : orderOf r ∣ p ^ k := orderOf_dvd_iff_pow_eq_one.mpr hkF
  have hordne : orderOf r ≠ 1 := fun h => hr1 (orderOf_eq_one_iff.mp h)
  have hpdvdr : p ∣ orderOf r := by
    obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow hp).mp horddvd'
    have hine : i ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hieq
      exact hordne hieq
    rw [hieq]
    exact dvd_pow_self p hine
  have hpdvdcard : p ∣ Nat.card ↥(MulAction.stabilizer F a ⊓ MulAction.stabilizer F (x • a)) :=
    dvd_trans hpdvdr (Subgroup.orderOf_dvd_natCard _ hrmem)
  exact hpdvd a (x • a) (Ne.symm hbne) hpdvdcard

/-- **A normal subgroup lying in a point stabiliser of a transitive faithful action is
trivial.** -/
theorem eq_bot_of_normal_le_stabilizer {F : Type*} [Group F] {α : Type*} [MulAction F α] (a : α)
    (htrans : MulAction.IsPretransitive F α)
    (hfaith : ∀ g : F, (∀ x : α, g • x = x) → g = 1)
    {Q : Subgroup F} (hQn : Q.Normal) (hle : Q ≤ MulAction.stabilizer F a) :
    Q = ⊥ := by
  haveI : MulAction.IsPretransitive F α := htrans
  rw [Subgroup.eq_bot_iff_forall]
  intro q hq
  refine hfaith q ?_
  intro y
  obtain ⟨f, hf⟩ := MulAction.IsPretransitive.exists_smul_eq (M := F) a y
  rw [← hf]
  have hmem : f⁻¹ * q * f ∈ MulAction.stabilizer F a :=
    hle (by simpa using hQn.conj_mem q hq f⁻¹)
  calc q • (f • a) = (q * f) • a := (mul_smul q f a).symm
    _ = (f * (f⁻¹ * q * f)) • a := by rw [show q * f = f * (f⁻¹ * q * f) by group]
    _ = f • ((f⁻¹ * q * f) • a) := mul_smul f _ a
    _ = f • a := by rw [MulAction.mem_stabilizer_iff.mp hmem]

/-- **Peterfalvi I Appendix III (2)–(5)** (pp. 206–207), as the `Prop`
`Work.NormalComplement.AppIIIProp`, proved from `BrauerSuzukiProp` and `FeitThompsonProp`.

Route: (2) Brauer–Suzuki gives `F = O_{2'}(F)·C_F(u)` for an involution `u`; since `C_F(u) ≤ F_a`
and `F ≠ F_a`, the odd-order subgroup `O_{2'}(F)` (solvable by Feit–Thompson) has a characteristic
elementary abelian `Q ≠ 1` normal in `F`, with `Q ⊄ F_a`, so `F = F_a Q` (maximality) and
`C_{F_a}(Q) = 1`, and `Q` is a minimal normal `f`-subgroup; (3) a second involution `v ∈ F_a` would
have `C_Q(v) = 1`, and since `Q` is inverted by `u` one gets `uv ∈ C_{F_a}(Q) = 1`; (4) distinct
involutions `u ≠ v` have `uv ∈ Q` with order `f` (as `F/Q` has a unique involution), and `Q` is
inverted by `u` with no nontrivial fixed point; (5) for `R ≤ F_a` a `p`-subgroup with
`p ∤ |F_a ∩ F_b|`, every `x ∈ R^#` is outside every conjugate of `F_a ∩ F_b`, so `C_F(x) ≤ F_a` and
`C_Q(x) = 1`; `R` cyclic for `p` odd. -/
theorem appIII (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hFT : Submission.Blueprint.FeitThompsonProp) :
    Work.NormalComplement.AppIIIProp := by
  intro F instG instF α instM a htrans hfaith hnfour hSE hcoat
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- the strongly embedded subgroup is a Bender subgroup for `2`
  have hBender : Work.DoubleTransitivity.IsBenderFor 2 (MulAction.stabilizer F a) :=
    ((Work.DoubleTransitivity.isStronglyEmbedded_iff _).mp hSE).2
  -- an involution `u ∈ F_a`
  obtain ⟨u, huH, hu2⟩ : ∃ u : F, u ∈ MulAction.stabilizer F a ∧ orderOf u = 2 := by
    have h2dvd : 2 ∣ Nat.card ↥(MulAction.stabilizer F a) := even_iff_two_dvd.mp hSE.2.1
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(MulAction.stabilizer F a)) 2 h2dvd
    exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩
  have hu2u : u * u = 1 := by
    rw [← pow_two, ← hu2]
    exact pow_orderOf_eq_one u
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2u
  -- `C_F(u) ≤ F_a`
  have huC : Subgroup.centralizer ({u} : Set F) ≤ MulAction.stabilizer F a :=
    Work.DoubleTransitivity.IsBenderFor.centralizer_le hBender huH (by rw [hu2])
  -- Brauer–Suzuki: `F = O_{2'}(F)·F_a`
  have hBS := hBrSz F hnfour u hu2
  have hOH : Submission.Blueprint.oddCore F ⊔ MulAction.stabilizer F a = ⊤ := by
    have hle : Submission.Blueprint.oddCore F ⊔ Subgroup.centralizer ({u} : Set F) ≤
        Submission.Blueprint.oddCore F ⊔ MulAction.stabilizer F a :=
      sup_le_sup_left huC _
    rw [hBS] at hle
    exact le_antisymm le_top hle
  have hOne : Submission.Blueprint.oddCore F ≠ ⊥ := by
    intro hbot
    rw [hbot, bot_sup_eq] at hOH
    exact hSE.1 hOH
  -- `O_{2'}(F)` is normal of odd order, hence solvable (Feit–Thompson)
  have hOnorm : (Submission.Blueprint.oddCore F).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨N, hNn, hNo, hxN⟩ := Work.BrauerSuzuki.OddCore.exists_normal_odd_of_mem_oddCore hx
    exact Work.BrauerSuzuki.OddCore.le_of_normal_odd hNn hNo (hNn.conj_mem x hxN g)
  have hOodd : Odd (Nat.card ↥(Submission.Blueprint.oddCore F)) :=
    Work.BrauerSuzuki.OddCore.oddCard_oddCore
  obtain ⟨f, Q, hfp, hQn, hQne, hQle, hQab, hQexp⟩ :=
    exists_elementary_abelian_normal hFT hOnorm hOne hOodd
  haveI hQN : Q.Normal := hQn
  have hQodd : Odd (Nat.card ↥Q) := Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le hQle)
  -- `Q ⊄ F_a`, maximality gives `F = Q·F_a`, `Q` is transitive and `C_{F_a}(Q) = 1`
  have hQnle : ¬ Q ≤ MulAction.stabilizer F a := by
    intro hle
    exact hQne (eq_bot_of_normal_le_stabilizer a htrans hfaith hQn hle)
  obtain ⟨hQtrans, hHCQ, hQinfH, hQsupH⟩ :=
    block_facts a htrans hfaith hQn hQab hQnle hcoat
  -- (3) `C_Q(u) = 1`, so `u` inverts `Q`
  have hQu : ∀ x ∈ Q, u * x * u⁻¹ = x → x = 1 := by
    intro x hx hfix
    have hxC : x ∈ Subgroup.centralizer ({u} : Set F) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      calc u * x = (u * x * u⁻¹) * u := by group
        _ = x * u := by rw [hfix]
    have hxH : x ∈ MulAction.stabilizer F a := huC hxC
    have : x ∈ Q ⊓ MulAction.stabilizer F a := Subgroup.mem_inf.mpr ⟨hx, hxH⟩
    rw [hQinfH] at this
    exact Subgroup.mem_bot.mp this
  have hQinv : ∀ x ∈ Q, u * x * u⁻¹ = x⁻¹ :=
    appIII_inv hQab hQodd hu2u (fun x hx => hQn.conj_mem x hx u) hQu
  -- (3) `F_a` has a unique involution
  have huniq : ∀ v : F, v ∈ MulAction.stabilizer F a → orderOf v = 2 → v = u := by
    intro v hvH hv2
    have hv2v : v * v = 1 := by
      rw [← pow_two, ← hv2]
      exact pow_orderOf_eq_one v
    have hvC : Subgroup.centralizer ({v} : Set F) ≤ MulAction.stabilizer F a :=
      Work.DoubleTransitivity.IsBenderFor.centralizer_le hBender hvH (by rw [hv2])
    have hQv : ∀ x ∈ Q, v * x * v⁻¹ = x → x = 1 := by
      intro x hx hfix
      have hxC : x ∈ Subgroup.centralizer ({v} : Set F) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        calc v * x = (v * x * v⁻¹) * v := by group
          _ = x * v := by rw [hfix]
      have hxH : x ∈ MulAction.stabilizer F a := hvC hxC
      have : x ∈ Q ⊓ MulAction.stabilizer F a := Subgroup.mem_inf.mpr ⟨hx, hxH⟩
      rw [hQinfH] at this
      exact Subgroup.mem_bot.mp this
    have hQvinv : ∀ x ∈ Q, v * x * v⁻¹ = x⁻¹ :=
      appIII_inv hQab hQodd hv2v (fun x hx => hQn.conj_mem x hx v) hQv
    have huvC : u * v ∈ MulAction.stabilizer F a ⊓ Subgroup.centralizer (Q : Set F) := by
      refine Subgroup.mem_inf.mpr ⟨(MulAction.stabilizer F a).mul_mem huH hvH, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hux : u * x⁻¹ = x * u := by
        calc u * x⁻¹ = u * (u * x * u⁻¹) := by rw [← hQinv x hx]
          _ = (u * u) * x * u⁻¹ := by group
          _ = x * u := by rw [hu2u, one_mul, hu_inv]
      have hvx : v * x = x⁻¹ * v := by
        calc v * x = (v * x * v⁻¹) * v := by group
          _ = x⁻¹ * v := by rw [hQvinv x hx]
      have key : (u * v) * x = x * (u * v) := by
        calc (u * v) * x = u * (v * x) := by group
          _ = u * (x⁻¹ * v) := by rw [hvx]
          _ = (u * x⁻¹) * v := by group
          _ = (x * u) * v := by rw [hux]
          _ = x * (u * v) := by group
      exact key.symm
    have huv1 : u * v = 1 := by
      have hmem := huvC
      rw [hHCQ] at hmem
      exact Subgroup.mem_bot.mp hmem
    calc v = u⁻¹ * (u * v) := by group
      _ = u⁻¹ := by rw [huv1, mul_one]
      _ = u := hu_inv
  -- (4) every involution of `F` is a `Q`-translate of `u`
  have hinvMem : ∀ w : F, orderOf w = 2 → ∃ z ∈ Q, w = z * u := by
    intro w hw2
    have hw2w : w * w = 1 := by
      rw [← pow_two, ← hw2]
      exact pow_orderOf_eq_one w
    obtain ⟨z, hz, h, hh, hzh⟩ := Subgroup.mem_sup_of_normal_left.mp
      ((le_of_eq hQsupH.symm) (Subgroup.mem_top w))
    have h0 : z * h * z * h = 1 := by
      calc z * h * z * h = (z * h) * (z * h) := by group
        _ = w * w := by rw [hzh]
        _ = 1 := hw2w
    have key : h * z * h = z⁻¹ := by
      calc h * z * h = z⁻¹ * (z * h * z * h) := by group
        _ = z⁻¹ * 1 := by rw [h0]
        _ = z⁻¹ := by rw [mul_one]
    have hh2Q : h * h ∈ Q := by
      have hsplit : h * h = (h * z * h⁻¹)⁻¹ * z⁻¹ := by
        calc h * h = (h * z * h⁻¹)⁻¹ * (h * z * h⁻¹ * (h * h)) := by group
          _ = (h * z * h⁻¹)⁻¹ * (h * z * h) := by group
          _ = (h * z * h⁻¹)⁻¹ * z⁻¹ := by rw [key]
      rw [hsplit]
      exact Q.mul_mem (Q.inv_mem (hQn.conj_mem z hz h)) (Q.inv_mem hz)
    have hh2 : h * h = 1 := by
      have : h * h ∈ Q ⊓ MulAction.stabilizer F a :=
        Subgroup.mem_inf.mpr ⟨hh2Q, (MulAction.stabilizer F a).mul_mem hh hh⟩
      rw [hQinfH] at this
      exact Subgroup.mem_bot.mp this
    rcases eq_or_ne h 1 with h1 | h1
    · rw [h1, mul_one] at hzh
      exfalso
      have hzord : orderOf z = 2 := by rw [hzh]; exact hw2
      have h2dvdQ : 2 ∣ Nat.card ↥Q := by
        rw [← hzord]
        exact Subgroup.orderOf_dvd_natCard Q hz
      exact (Nat.not_even_iff_odd.mpr hQodd) (even_iff_two_dvd.mpr h2dvdQ)
    · have hh2' : orderOf h = 2 := by
        rw [orderOf_eq_prime_iff]
        exact ⟨by rwa [pow_two], h1⟩
      exact ⟨z, hz, by rw [← hzh, huniq h hh hh2']⟩
  -- (4) distinct involutions multiply into `Q` with order `f`
  have h4a : ∀ u' v' : F, orderOf u' = 2 → orderOf v' = 2 → u' ≠ v' →
      u' * v' ∈ Q ∧ orderOf (u' * v') = f := by
    intro u' v' hu' hv' hne
    obtain ⟨z, hz, rfl⟩ := hinvMem u' hu'
    obtain ⟨y, hy, rfl⟩ := hinvMem v' hv'
    have hzy : (z * u) * (y * u) = z * y⁻¹ := by
      calc (z * u) * (y * u) = z * (u * y * u⁻¹) * (u * u) := by group
        _ = z * y⁻¹ * 1 := by rw [hQinv y hy, hu2u]
        _ = z * y⁻¹ := by rw [mul_one]
    have hmem : z * y⁻¹ ∈ Q := Q.mul_mem hz (Q.inv_mem hy)
    have hne1 : z * y⁻¹ ≠ 1 := by
      intro h
      apply hne
      have hzy' : z = y := by
        calc z = z * y⁻¹ * y := by group
          _ = y := by rw [h, one_mul]
      rw [hzy']
    refine ⟨by rw [hzy]; exact hmem, ?_⟩
    rw [hzy]
    have hdvd : orderOf (z * y⁻¹) ∣ f := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact hQexp _ hmem
    rcases hfp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hne1
    · exact h1
  -- (4) odd-order elements inverted by an involution lie in `Q`
  have h4b : ∀ u' : F, orderOf u' = 2 → ∀ x : F, Odd (orderOf x) →
      u' * x * u'⁻¹ = x⁻¹ → x ∈ Q := by
    intro u' hu' x hxodd hinvx
    rcases eq_or_ne x 1 with h1 | h1
    · rw [h1]; exact Q.one_mem
    · have hu'u : u' * u' = 1 := by
        rw [← pow_two, ← hu']
        exact pow_orderOf_eq_one u'
      have hu'inv : u'⁻¹ = u' := inv_eq_of_mul_eq_one_right hu'u
      have hsq : (u' * x) * (u' * x) = 1 := by
        calc (u' * x) * (u' * x) = (u' * x * u') * x := by group
          _ = ((u' * x * u'⁻¹) * (u' * u')) * x := by group
          _ = (x⁻¹ * 1) * x := by rw [hinvx, hu'u]
          _ = 1 := by group
      have huxne : u' * x ≠ 1 := by
        intro h
        have hxeq : x = u' := by
          calc x = u'⁻¹ * (u' * x) := by group
            _ = u'⁻¹ := by rw [h, mul_one]
            _ = u' := hu'inv
        rw [hxeq, hu'] at hxodd
        exact (by norm_num : ¬ Odd 2) hxodd
      have hord : orderOf (u' * x) = 2 := by
        rw [orderOf_eq_prime_iff]
        exact ⟨by rwa [pow_two], huxne⟩
      obtain ⟨z, hz, hzux⟩ := hinvMem (u' * x) hord
      obtain ⟨z', hz', hzu'⟩ := hinvMem u' hu'
      have huinv' : u'⁻¹ = u⁻¹ * z'⁻¹ := by rw [hzu', mul_inv_rev]
      have hxeq : x = u * (z'⁻¹ * z) * u⁻¹ := by
        calc x = u'⁻¹ * (u' * x) := by group
          _ = u'⁻¹ * (z * u) := by rw [hzux]
          _ = u * (z'⁻¹ * z) * u⁻¹ := by rw [huinv', hu_inv]; group
      have hmem : u * (z'⁻¹ * z) * u⁻¹ ∈ Q := by
        rw [hQinv (z'⁻¹ * z) (Q.mul_mem (Q.inv_mem hz') hz)]
        exact Q.inv_mem (Q.mul_mem (Q.inv_mem hz') hz)
      rwa [hxeq]
  refine ⟨f, Q, hfp, hQn, hQne, hQab, hQexp, hQinfH, hQsupH,
    ⟨u, ⟨huH, hu2⟩, fun v hv => huniq v hv.1 hv.2⟩, h4a, h4b, ?_⟩
  -- (5)
  intro h2 p hp b hb hpdvd R hR hRp
  have hall : ∀ c d : α, c ≠ d →
      ¬ p ∣ Nat.card ↥(MulAction.stabilizer F c ⊓ MulAction.stabilizer F d) := by
    intro c d hcd
    rw [← stabilizer_inf_card_eq (a := a) (b := b) (c := c) (d := d) h2 (Ne.symm hb) hcd]
    exact hpdvd
  have hfpf := fpf_on_of_not_dvd a hp hall hQinfH R hR hRp
  exact ⟨hfpf, fun hp2 => isCyclic_of_isPGroup_fpf hQn hQne hp hp2 hRp hfpf⟩

end Work.NormalComplement
