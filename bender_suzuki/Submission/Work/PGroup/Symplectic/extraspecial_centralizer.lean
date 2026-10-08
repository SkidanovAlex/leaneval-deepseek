import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.card_extraspecial
import Submission.Work.PGroup.center_eq_frattini_of_isExtraspecial
import Submission.Work.PGroup.isPGroup_of_isExtraspecial
import Submission.Work.PGroup.frattini_eq_agemo_sup_commutator

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# An extraspecial subgroup acting by central automorphisms is self-centralizing up to itself

Let `C ≤ X` be an extraspecial `p`-group inside a finite group `X`, and suppose that
`[X, C] ≤ Z(C)`, i.e. every element of `X` acts on `C` by an automorphism which is trivial on
`C / Z(C)`.  The claim of this file is

`C ⊔ C_X(C) = X`,

i.e. the image of `X` in `Aut(C)` is the group of inner automorphisms of `C`.

The mathematical content is the classical fact that the central automorphisms of an extraspecial
group are inner.  For a finite group `H` of nilpotency class two with `|Z(H)| = p` prime (and
`H^p ≤ Z(H)`, `[H,H] ≤ Z(H)`), the commutator map descends to a non-degenerate pairing

`Q × Q → Z(H)`,  `Q = H / Z(H)`,

i.e. an injective homomorphism `δ : Q →* (Q →* Z(H))`, `q ↦ (q' ↦ ⁅q, q'⁆)`.  Since `Q` is a
finite elementary abelian `p`-group and `|Z(H)| = p`, duality of finite abelian groups gives
`|Q →* Z(H)| = |Q|` (`natCard_monoidHom_eq_natCard`), so `δ` is bijective; this is
`exists_commutator_eq_of_center_prime`.  Applying it with `H = C` and `f` the homomorphism
`c ↦ ⁅x, c⁆` produced by `[X, C] ≤ Z(C)` gives, for every `x : X`, an element `d ∈ C` with
`⁅x, c⁆ = ⁅d, c⁆` for all `c ∈ C`; equivalently `d⁻¹x` centralizes `C`, so `x ∈ C · C_X(C)`.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical Pointwise commutatorElement IsMulCommutative
open Subgroup

namespace Work.PGroup.Symplectic

noncomputable section

/-! ### Duality of finite elementary abelian `p`-groups -/

/-- **Duality for finite elementary abelian `p`-groups.**  If `Q` is a finite commutative group
all of whose elements have order dividing the prime `p`, and `Z` is a finite group of order `p`,
then `Q` and its group of homomorphisms to `Z` have the same cardinality. -/
theorem natCard_monoidHom_eq_natCard {Q Z : Type*} [CommGroup Q] [Finite Q] [CommGroup Z]
    [Finite Z] {p : ℕ} (hp : p.Prime) (hexp : ∀ q : Q, q ^ p = 1) (hZ : Nat.card Z = p) :
    Nat.card (Q →* Z) = Nat.card Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcard : Nat.card (ZMod p) = p := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hpowZ : ∀ z : Z, z ^ p = 1 := by
    intro z
    have h : orderOf z ∣ Nat.card Z := orderOf_dvd_natCard z
    rw [hZ] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hsmulQ : ∀ x : Additive Q, p • x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := Additive.ofMul.surjective x
    rw [← ofMul_pow, hexp y, ofMul_one]
  haveI hmodQ : Module (ZMod p) (Additive Q) := AddCommGroup.zmodModule hsmulQ
  have hsmulZ : ∀ z : Additive Z, p • z = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := Additive.ofMul.surjective x
    rw [← ofMul_pow, hpowZ y, ofMul_one]
  haveI hmodZ : Module (ZMod p) (Additive Z) := AddCommGroup.zmodModule hsmulZ
  haveI hfinZ : Module.Finite (ZMod p) (Additive Z) := Module.Finite.of_finite
  haveI hfreeZ : Module.Free (ZMod p) (Additive Z) := Module.Free.of_divisionRing _ _
  haveI hfinQ : Module.Finite (ZMod p) (Additive Q) := Module.Finite.of_finite
  haveI hfreeQ : Module.Free (ZMod p) (Additive Q) := Module.Free.of_divisionRing _ _
  have hfinrankZ : Module.finrank (ZMod p) (Additive Z) = 1 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive Z)
    rw [(Nat.card_congr (Additive.ofMul : Z ≃ Additive Z)).symm, hZ, hcard] at h
    exact Nat.pow_right_injective hp.two_le (by simpa using h.symm)
  have h1 : Nat.card (Q →* Z) = Nat.card (Additive Q →ₗ[ZMod p] Additive Z) :=
    Nat.card_congr (MonoidHom.toAdditive.trans (AddMonoidHom.toZModLinearMapEquiv p).toEquiv)
  have h2 : Nat.card (Additive Q →ₗ[ZMod p] Additive Z) = Nat.card (Additive Q) := by
    haveI : Finite (Additive Q →ₗ[ZMod p] Additive Z) :=
      Finite.of_injective _ (fun f g h => by ext x; exact congrFun h x)
    haveI : Module.Finite (ZMod p) (Additive Q →ₗ[ZMod p] Additive Z) := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive Q →ₗ[ZMod p] Additive Z),
        Module.finrank_linearMap, hfinrankZ, mul_one,
        ← Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive Q)]
  rw [h1, h2, Nat.card_congr (Additive.ofMul : Q ≃ Additive Q).symm]

/-! ### Central automorphisms of a class-two group with centre of prime order -/

/-- **Central automorphisms of a group of class two with centre of prime order.**

Let `H` be a finite group with `[H,H] ≤ Z(H)`, `Nat.card Z(H) = p` a prime, and
`H ^ p ≤ Z(H)`, so that `Q = H / Z(H)` is a finite elementary abelian `p`-group.  Then every
homomorphism `f : H →* Z(H)` which vanishes on `Z(H)` is of the form `c ↦ ⁅d, c⁆` for some
`d : H`.  Equivalently: the commutator pairing on `Q` is a bijection `Q → Hom(Q, Z(H))`. -/
theorem exists_commutator_eq_of_center_prime {H : Type*} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) (hZcard : Nat.card (Subgroup.center H) = p)
    (hcomm : ⁅(⊤ : Subgroup H), ⊤⁆ ≤ Subgroup.center H)
    (hexp : ∀ x : H, x ^ p ∈ Subgroup.center H) (f : H →* Subgroup.center H)
    (hf : ∀ z : Subgroup.center H, f z = 1) :
    ∃ d : H, ∀ c : H, (f c : H) = ⁅d, c⁆ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcommpt : ∀ a b : H, ⁅a, b⁆ ∈ Subgroup.center H :=
    fun a b => Subgroup.commutator_le.mp hcomm a trivial b trivial
  -- the two-variable commutator map
  let phi : H → H →* Subgroup.center H := fun d =>
    { toFun := fun c => ⟨⁅d, c⁆, hcommpt d c⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        ext
        show ⁅d, a * b⁆ = ⁅d, a⁆ * ⁅d, b⁆
        rw [commutatorElement_mul_right_eq_mul_conj]
        have h1 : a * ⁅d, b⁆ * a⁻¹ = ⁅d, b⁆ := by
          rw [Subgroup.mem_center_iff.mp (hcommpt d b) a]; group
        rw [show ⁅d, a⁆ * a * ⁅d, b⁆ * a⁻¹ = ⁅d, a⁆ * (a * ⁅d, b⁆ * a⁻¹) from by group, h1] }
  have hker : ∀ d : H, Subgroup.center H ≤ (phi d).ker := by
    intro d z hz
    rw [MonoidHom.mem_ker]
    ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz d)
  -- the descended pairing `H / Z(H) →* (H / Z(H) →* Z(H))`
  let Q := H ⧸ Subgroup.center H
  haveI hQcomm : IsMulCommutative Q :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
  let δ : H →* (Q →* Subgroup.center H) :=
    { toFun := fun d => QuotientGroup.lift (Subgroup.center H) (phi d) (hker d)
      map_one' := by
        refine MonoidHom.ext (fun q => ?_)
        refine QuotientGroup.induction_on q (fun z => ?_)
        rw [QuotientGroup.lift_mk', MonoidHom.one_apply]
        apply Subtype.ext
        dsimp only [phi]
        simp
      map_mul' := fun d₁ d₂ => by
        refine MonoidHom.ext (fun q => ?_)
        refine QuotientGroup.induction_on q (fun z => ?_)
        rw [QuotientGroup.lift_mk', MonoidHom.mul_apply, QuotientGroup.lift_mk',
          QuotientGroup.lift_mk']
        apply Subtype.ext
        dsimp only [phi]
        show ⁅d₁ * d₂, z⁆ = ⁅d₁, z⁆ * ⁅d₂, z⁆
        rw [commutatorElement_mul_left_eq_conj_mul]
        have h1 : d₁ * ⁅d₂, z⁆ * d₁⁻¹ = ⁅d₂, z⁆ := by
          rw [Subgroup.mem_center_iff.mp (hcommpt d₂ z) d₁]; group
        rw [h1]
        exact Subgroup.mem_center_iff.mp (hcommpt d₁ z) ⁅d₂, z⁆ }
  -- the kernel of `δ` is exactly the centre
  have hδker : δ.ker = Subgroup.center H := by
    refine le_antisymm (fun d hd => ?_) (fun z hz => ?_)
    · rw [MonoidHom.mem_ker] at hd
      rw [Subgroup.mem_center_iff]
      intro c
      have h1 : (δ d) (QuotientGroup.mk' (Subgroup.center H) c) = 1 := by
        rw [hd, MonoidHom.one_apply]
      have h2 : phi d c = 1 := by
        simp only [δ] at h1
        exact h1
      have h3 : ⁅d, c⁆ = 1 := by
        have h := congrArg (fun g : Subgroup.center H => (g : H)) h2
        dsimp only [phi] at h
        simpa using h
      exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
    · rw [MonoidHom.mem_ker]
      refine MonoidHom.ext (fun q => ?_)
      refine QuotientGroup.induction_on q (fun c => ?_)
      simp only [δ, MonoidHom.one_apply]
      apply Subtype.ext
      dsimp only [phi]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz c).symm
  have hQexp : ∀ q : Q, q ^ p = 1 := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center H) q
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hexp g
  -- duality: `δ` has as many values as there are elements in `Q`
  have hcard : Nat.card (Q →* Subgroup.center H) = Nat.card Q :=
    natCard_monoidHom_eq_natCard hp hQexp hZcard
  have hcardrange : Nat.card ↥(δ.range) = Nat.card Q := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv, hδker]
  haveI hfinrange : Finite ↥(δ.range) :=
    Finite.of_injective
      (fun x : ↥(δ.range) => ((x : Q →* Subgroup.center H) : Q → Subgroup.center H))
      (fun x y h => Subtype.ext (MonoidHom.ext (fun q => congrFun h q)))
  have hrange : δ.range = ⊤ := by
    refine Subgroup.eq_top_of_card_eq δ.range ?_
    rw [hcardrange, ← hcard]
  -- the given homomorphism factors through `Q`
  have hfker : Subgroup.center H ≤ f.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    exact hf ⟨z, hz⟩
  let fbar : Q →* Subgroup.center H := QuotientGroup.lift (Subgroup.center H) f hfker
  have hmem : fbar ∈ δ.range := by rw [hrange]; trivial
  obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp hmem
  refine ⟨d, fun c => ?_⟩
  have h1 : (δ d) (QuotientGroup.mk' (Subgroup.center H) c)
      = fbar (QuotientGroup.mk' (Subgroup.center H) c) := by rw [hd]
  have h2 : phi d c = f c := by
    simp only [δ, fbar] at h1
    exact h1
  have h3 : ((phi d c : Subgroup.center H) : H) = (f c : H) := congrArg _ h2
  simpa [phi] using h3.symm

/-! ### Bridge lemmas for `IsExtraspecial` -/

/-- Membership in `Work.PGroup.centerIn C` translated to the group `↥C`. -/
theorem mem_center_subtype {G : Type*} [Group G] {C : Subgroup G} {z : G}
    (h : z ∈ Work.PGroup.centerIn C) :
    (⟨z, Work.PGroup.centerIn_le C h⟩ : ↥C) ∈ Subgroup.center ↥C := by
  obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.mp h
  have hwz : w = (⟨z, Work.PGroup.centerIn_le C h⟩ : ↥C) := Subtype.ext hwe
  rw [← hwz]
  exact hw

/-- The `p`-th powers of an extraspecial `p`-subgroup lie in its centre. -/
theorem pow_mem_center_subtype {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (C : Subgroup G)
    [Finite C] (hC : Work.PGroup.IsExtraspecial p C) :
    ∀ x : ↥C, x ^ p ∈ Subgroup.center ↥C := by
  intro x
  have hisp := Work.PGroup.isPGroup_of_isExtraspecial C hC
  have hfr := Work.PGroup.frattini_eq_agemo_sup_commutator hp C hisp
  have hcf := Work.PGroup.center_eq_frattini_of_isExtraspecial C hC
  have hmem : ((x : G)) ^ p ∈ Work.PGroup.centerIn C := by
    have h1 : ((x : G)) ^ p ∈ Work.PGroup.agemo p 1 C := by
      simpa using Work.PGroup.pow_mem_agemo (p := p) (i := 1) x.2
    have h2 : ((x : G)) ^ p ∈ Work.PGroup.frattiniIn C := hfr ▸ Subgroup.mem_sup_left h1
    exact hcf ▸ h2
  have h := mem_center_subtype (C := C) hmem
  have heq : (⟨((x : G)) ^ p, Work.PGroup.centerIn_le C hmem⟩ : ↥C) = x ^ p :=
    Subtype.ext (by simp)
  rwa [heq] at h

/-! ### The main theorem -/

theorem extraspecial_centralizer {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (C : Subgroup X) (hC : Work.PGroup.IsExtraspecial p C)
    (hcomm : ⁅(⊤ : Subgroup X), C⁆ ≤ Work.PGroup.centerIn C) :
    C ⊔ Subgroup.centralizer (C : Set X) = ⊤ := by
  haveI : Finite ↥C := inferInstance
  have hZcard : Nat.card (Subgroup.center ↥C) = p := Work.PGroup.card_center_subtype C hC
  have hcommH : ⁅(⊤ : Subgroup ↥C), ⊤⁆ ≤ Subgroup.center ↥C := by
    rw [Work.PGroup.center_subtype_eq_commutator C hC]
  have hexpH := pow_mem_center_subtype hp C hC
  refine eq_top_iff.mpr (fun x _ => ?_)
  -- for `x : X` the map `c ↦ ⁅x, c⁆` is a homomorphism `↥C →* Z(↥C)` vanishing on `Z(↥C)`
  have hxmem : ∀ c : ↥C, ⁅x, (c : X)⁆ ∈ Work.PGroup.centerIn C :=
    fun c => Subgroup.commutator_le.mp hcomm x trivial (c : X) c.2
  let F : ↥C →* Subgroup.center ↥C :=
    { toFun := fun c =>
        ⟨⟨⁅x, (c : X)⁆, Work.PGroup.centerIn_le C (hxmem c)⟩, mem_center_subtype (hxmem c)⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_mul' := fun c₁ c₂ => by
        apply Subtype.ext
        apply Subtype.ext
        show ⁅x, ((c₁ : X) * (c₂ : X))⁆ = ⁅x, (c₁ : X)⁆ * ⁅x, (c₂ : X)⁆
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hc : (c₁ : X) * ⁅x, (c₂ : X)⁆ = ⁅x, (c₂ : X)⁆ * (c₁ : X) := by
          have h := Subgroup.mem_center_iff.mp (mem_center_subtype (C := C) (hxmem c₂)) c₁
          exact congrArg Subtype.val h
        rw [show ⁅x, (c₁ : X)⁆ * (c₁ : X) * ⁅x, (c₂ : X)⁆ * (c₁ : X)⁻¹
              = ⁅x, (c₁ : X)⁆ * ((c₁ : X) * ⁅x, (c₂ : X)⁆ * (c₁ : X)⁻¹) from by group, hc]
        group }
  -- `F` vanishes on `Z(↥C) = [↥C, ↥C]` because its target is abelian
  have hFker : ∀ z : Subgroup.center ↥C, F z = 1 := by
    have hcommle : ⁅(⊤ : Subgroup ↥C), ⊤⁆ ≤ F.ker := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker]
      have hmap : F ⁅a, b⁆ = ⁅F a, F b⁆ := by
        simp only [commutatorElement_def, MonoidHom.map_mul, MonoidHom.map_inv]
      rw [hmap, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm (F a) (F b)
    intro z
    rw [← MonoidHom.mem_ker]
    exact hcommle ((Work.PGroup.center_subtype_eq_commutator C hC) ▸ z.2)
  obtain ⟨d, hd⟩ := exists_commutator_eq_of_center_prime hp hZcard hcommH hexpH F hFker
  -- hence `d⁻¹ x` centralizes `C`
  have key : ∀ c : ↥C, ⁅x, (c : X)⁆ = ⁅(d : X), (c : X)⁆ := by
    intro c
    have h : ((F c : ↥C) : X) = ((⁅d, c⁆ : ↥C) : X) := congrArg (fun g : ↥C => (g : X)) (hd c)
    have h1 : ((F c : ↥C) : X) = ⁅x, (c : X)⁆ := rfl
    have h2 : ((⁅d, c⁆ : ↥C) : X) = ⁅(d : X), (c : X)⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h1, h2] at h
    exact h
  have hy : (d : X)⁻¹ * x ∈ Subgroup.centralizer (C : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have h1 : x * c * x⁻¹ = (d : X) * c * (d : X)⁻¹ := by
      have h2 : x * c * x⁻¹ * c⁻¹ = (d : X) * c * (d : X)⁻¹ * c⁻¹ := key ⟨c, hc⟩
      exact mul_right_cancel h2
    calc c * ((d : X)⁻¹ * x) = (d : X)⁻¹ * ((d : X) * c * (d : X)⁻¹) * x := by group
      _ = (d : X)⁻¹ * (x * c * x⁻¹) * x := by rw [← h1]
      _ = (d : X)⁻¹ * x * c := by group
  have hxd : (d : X) * ((d : X)⁻¹ * x) = x := by group
  rw [← hxd]
  exact (C ⊔ Subgroup.centralizer (C : Set X)).mul_mem (Subgroup.mem_sup_left d.2)
    (Subgroup.mem_sup_right hy)

end

end Work.PGroup.Symplectic
