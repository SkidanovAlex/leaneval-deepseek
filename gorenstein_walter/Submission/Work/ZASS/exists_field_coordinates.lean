import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.Zassenhaus.Basic
import Submission.OddOrder.GroupTheory.RepresentationTheory.SingerField
import Submission.OddOrder.BG.Ch1_Preliminary.OperatorMaschke
import Submission.Work.ZASSF.card_dvd_card_sub_one
import Submission.Work.ZASSF.mem_iff_exists_sq_of_index_two
import Submission.Work.ZASSF.eq_of_dvd_pow_sub_one

open scoped IsMulCommutative

namespace Work.ZASS

open Work.Zassenhaus

section Conj

variable {G : Type} [Group G] {X : Type} [MulAction G X] {inf zero : X} {U : Subgroup G}

/-- `G_{∞0} ≤ N_G(U)` when `U ⊴ G_∞` and `U ≤ G_∞`. -/
theorem pairStab_le_normalizer (hUB : U ≤ Work.Zassenhaus.borel G inf)
    (hN : (U.subgroupOf (Work.Zassenhaus.borel G inf)).Normal) :
    Work.Zassenhaus.pairStab G inf zero ≤ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro h hh k hk
  exact mem_conjBy_of_subgroupOf_normal hUB hN (pairStab_le_borel inf zero hh) hk

/-- The conjugation action of `G_{∞0}` on `U`, as a monoid hom into `MulAut U`. -/
noncomputable def conjAut (hUB : U ≤ Work.Zassenhaus.borel G inf)
    (hN : (U.subgroupOf (Work.Zassenhaus.borel G inf)).Normal) :
    ↥(Work.Zassenhaus.pairStab G inf zero) →* MulAut ↥U :=
  (Subgroup.normalizerMonoidHom (H := U)).comp
    (Subgroup.inclusion (pairStab_le_normalizer hUB hN))

theorem conjAut_apply (hUB : U ≤ Work.Zassenhaus.borel G inf)
    (hN : (U.subgroupOf (Work.Zassenhaus.borel G inf)).Normal)
    (c : ↥(Work.Zassenhaus.pairStab G inf zero)) (u : ↥U) :
    ((conjAut hUB hN c) u : G) = conjBy (c : G) (u : G) := by
  simp only [conjAut, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom,
    MulDistribMulAction.toMulAut, Equiv.coe_fn_mk, conjBy]
  rfl

end Conj

section Mod

variable {G : Type} [Group G] {X : Type} [MulAction G X] {inf zero : X} {U : Subgroup G} {p k : ℕ}

theorem isElementaryAbelian_of (hcomm : IsMulCommutative U) (hexp : ∀ u ∈ U, u ^ p = 1) :
    OddOrder.GroupTheory.IsElementaryAbelian p ↥U :=
  ⟨fun x y => hcomm.is_comm.comm x y, fun x => Subtype.ext (by simpa using hexp (x : G) x.2)⟩

theorem p_nsmul_eq_zero (hE : OddOrder.GroupTheory.IsElementaryAbelian p ↥U)
    (x : Additive ↥U) : p • x = 0 := by
  apply Additive.toMul.injective
  rw [toMul_nsmul, toMul_zero]
  exact hE.pow_eq_one x.toMul

/-- The conjugation action of `G_{∞0}` on the `𝔽_p`-vector space `Additive U`. -/
noncomputable def conjRep (hUB : U ≤ Work.Zassenhaus.borel G inf)
    (hN : (U.subgroupOf (Work.Zassenhaus.borel G inf)).Normal)
    (hcomm : IsMulCommutative U) (hZ : Module (ZMod p) (Additive ↥U)) :
    Representation (ZMod p) ↥(Work.Zassenhaus.pairStab G inf zero) (Additive ↥U) :=
  letI := hcomm
  letI := hZ
  (OddOrder.BG.Ch1_Preliminary.mulAutToEnd ↥U p).comp (conjAut hUB hN)

/-- The `𝔽_p[G_{∞0}]`-module structure on `Additive U` induced by conjugation. -/
noncomputable def conjModule (hUB : U ≤ Work.Zassenhaus.borel G inf)
    (hN : (U.subgroupOf (Work.Zassenhaus.borel G inf)).Normal)
    (hcomm : IsMulCommutative U) (hZ : Module (ZMod p) (Additive ↥U)) :
    Module (MonoidAlgebra (ZMod p) ↥(Work.Zassenhaus.pairStab G inf zero)) (Additive ↥U) :=
  Module.compHom (Additive ↥U) ((conjRep hUB hN hcomm hZ).asAlgebraHom).toRingHom

theorem of_smul_apply (hUB : U ≤ Work.Zassenhaus.borel G inf)
    (hN : (U.subgroupOf (Work.Zassenhaus.borel G inf)).Normal)
    (hcomm : IsMulCommutative U) (hZ : Module (ZMod p) (Additive ↥U))
    (c : ↥(Work.Zassenhaus.pairStab G inf zero)) (a : Additive ↥U) :
    (letI : Module (MonoidAlgebra (ZMod p) ↥(Work.Zassenhaus.pairStab G inf zero)) (Additive ↥U) :=
      conjModule hUB hN hcomm hZ
     MonoidAlgebra.of (ZMod p) ↥(Work.Zassenhaus.pairStab G inf zero) c • a)
      = conjAut hUB hN c a := by
  change ((conjRep hUB hN hcomm hZ).asAlgebraHom
    (MonoidAlgebra.of (ZMod p) ↥(Work.Zassenhaus.pairStab G inf zero) c)) a = _
  rw [Representation.asAlgebraHom_of]
  rfl

/-- The conjugation action on `U` is faithful, given fixed-point-freeness and `|U| ≠ 1`. -/
theorem conjAut_injective (hUB : U ≤ Work.Zassenhaus.borel G inf)
    (hN : (U.subgroupOf (Work.Zassenhaus.borel G inf)).Normal)
    (hfix : FixedPointFreeConj U (Work.Zassenhaus.pairStab G inf zero))
    (hcard : Nat.card ↥U = p ^ k) (hp : 1 < p) (hk : 1 ≤ k) :
    Function.Injective (conjAut (U := U) (inf := inf) (zero := zero) hUB hN) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  by_contra hcne
  have hUbot : (U : Subgroup G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    refine hfix (c : G) c.2 (fun hc1 => hcne (Subtype.ext hc1)) u hu ?_
    have h2 : conjAut hUB hN c (⟨u, hu⟩ : ↥U) = ⟨u, hu⟩ := by
      have := congrArg (fun f : MulAut ↥U => f ⟨u, hu⟩) hc
      simpa using this
    have h3 := congrArg (fun z : ↥U => (z : G)) h2
    simpa [conjAut_apply, conjBy] using h3
  have h1 : Nat.card ↥U = 1 := by rw [hUbot]; exact Subgroup.card_bot
  rw [hcard] at h1
  have hlt : 1 < p ^ k := Nat.one_lt_pow (by omega) hp
  omega

end Mod

section Irred

variable {G : Type} [Group G] [Finite G] {X : Type} [MulAction G X] {inf zero : X}
  {U : Subgroup G} {p k : ℕ}

/-- **Z5** (blueprint §ZASS): a nontrivial `H`-invariant subgroup of `U` is `U`. -/
theorem eq_top_of_isConjInvariant_of_dvd (hp : p.Prime) (hpodd : Odd p) (hk : 1 ≤ k)
    (hcardU : Nat.card ↥U = p ^ k) {W : Subgroup G} (hWU : W ≤ U) (hWne : W ≠ ⊥)
    (hdvd : (p ^ k - 1) / 2 ∣ Nat.card ↥W - 1) : W = U := by
  have hcardmap : Nat.card ↥(W.subgroupOf U) = Nat.card ↥W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWU).toEquiv
  have hdvdU : Nat.card ↥W ∣ p ^ k := by
    rw [← hcardmap, ← hcardU]
    exact Subgroup.card_subgroup_dvd_card (W.subgroupOf U)
  obtain ⟨m, hmk, hm⟩ := (Nat.dvd_prime_pow hp).mp hdvdU
  have h2 : 1 < Nat.card ↥W := by
    rw [Finite.one_lt_card_iff_nontrivial]
    exact (Subgroup.nontrivial_iff_ne_bot W).mpr hWne
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h
    · rw [h0, pow_zero] at hm; omega
    · exact h
  have hdvd' : (p ^ k - 1) / 2 ∣ p ^ m - 1 := by rw [← hm]; exact hdvd
  have hmk' : m = k := Work.ZASSF.eq_of_dvd_pow_sub_one hp hpodd hk hm1 hmk hdvd'
  refine Subgroup.eq_of_le_of_card_ge hWU ?_
  rw [hcardU, hm, hmk']

/-- Additive form of Z5: a nonzero `H`-invariant additive subgroup of `Additive U` is
everything. -/
theorem eq_top_of_addSubgroup (hUB : U ≤ Work.Zassenhaus.borel G inf)
    (hN : (U.subgroupOf (Work.Zassenhaus.borel G inf)).Normal)
    (hp : p.Prime) (hpodd : Odd p) (hk : 1 ≤ k) (hcardU : Nat.card ↥U = p ^ k)
    (hcardH : Nat.card ↥(Work.Zassenhaus.pairStab G inf zero) = (p ^ k - 1) / 2)
    (hfix : FixedPointFreeConj U (Work.Zassenhaus.pairStab G inf zero))
    {F : AddSubgroup (Additive ↥U)} (hF : F ≠ ⊥)
    (hFinv : ∀ (h : ↥(Work.Zassenhaus.pairStab G inf zero)) (x : Additive ↥U), x ∈ F →
      Additive.ofMul (conjAut hUB hN h (Additive.toMul x)) ∈ F) :
    F = ⊤ := by
  let W' : Subgroup ↥U := AddSubgroup.toSubgroup' F
  let W : Subgroup G := W'.map (Subgroup.subtype U)
  have hcardFW : Nat.card ↥F = Nat.card ↥W := by
    have h1 : Nat.card ↥F = Nat.card ↥W' :=
      Nat.card_congr (Equiv.subtypeEquiv Additive.toMul (fun a => by
        show a ∈ F ↔ Additive.toMul a ∈ AddSubgroup.toSubgroup' F
        rw [AddSubgroup.mem_toSubgroup']
        exact Iff.rfl))
    have h2 : Nat.card ↥W' = Nat.card ↥W :=
      (Subgroup.card_map_of_injective (Subgroup.subtype_injective U)).symm
    rw [h1, h2]
  have hWU : W ≤ U := Subgroup.map_subtype_le W'
  have hWne : W ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥W = 1 := by rw [hbot]; exact Subgroup.card_bot
    have h2 : 1 < Nat.card ↥F := by
      rw [Finite.one_lt_card_iff_nontrivial]
      exact (AddSubgroup.nontrivial_iff_ne_bot F).mpr hF
    omega
  have hWinv : IsConjInvariant (Work.Zassenhaus.pairStab G inf zero) W := by
    intro h hh w hw
    obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.mp hw
    have hmem : Additive.ofMul w' ∈ F := (AddSubgroup.mem_toSubgroup' F w').mp hw'
    have h1 : Additive.ofMul (conjAut hUB hN ⟨h, hh⟩ w') ∈ F := by
      have := hFinv ⟨h, hh⟩ (Additive.ofMul w') hmem
      simpa using this
    have h2 : conjAut hUB hN ⟨h, hh⟩ w' ∈ W' := (AddSubgroup.mem_toSubgroup' F _).mpr h1
    refine Subgroup.mem_map.mpr ⟨conjAut hUB hN ⟨h, hh⟩ w', h2, ?_⟩
    exact conjAut_apply hUB hN ⟨h, hh⟩ w'
  have hirr : W = U := eq_top_of_isConjInvariant_of_dvd hp hpodd hk hcardU hWU hWne (by
    have hd := Work.ZASSF.card_dvd_card_sub_one (U := U) (H := Work.Zassenhaus.pairStab G inf zero)
      (W := W) hWU hfix hWne hWinv
    rwa [hcardH] at hd)
  have hcardFU : Nat.card ↥F = Nat.card (Additive ↥U) := by
    rw [hcardFW, hirr]
    exact Nat.card_congr Additive.ofMul
  exact AddSubgroup.eq_top_of_card_eq F hcardFU

end Irred

section Simple

variable {G : Type} [Group G] [Finite G] {X : Type} [MulAction G X] {inf zero : X}
  {U : Subgroup G} {p k : ℕ}

/-- The `𝔽_p[G_{∞0}]`-module `Additive U` is simple, by Z5. -/
theorem isSimpleModule_conjModule (hUB : U ≤ Work.Zassenhaus.borel G inf)
    (hN : (U.subgroupOf (Work.Zassenhaus.borel G inf)).Normal)
    (hcomm : IsMulCommutative U) (hZ : Module (ZMod p) (Additive ↥U))
    (hp : p.Prime) (hpodd : Odd p) (hk : 1 ≤ k) (hcardU : Nat.card ↥U = p ^ k)
    (hcardH : Nat.card ↥(Work.Zassenhaus.pairStab G inf zero) = (p ^ k - 1) / 2)
    (hfix : FixedPointFreeConj U (Work.Zassenhaus.pairStab G inf zero)) :
    (letI : Module (MonoidAlgebra (ZMod p) ↥(Work.Zassenhaus.pairStab G inf zero)) (Additive ↥U) :=
       conjModule hUB hN hcomm hZ
     IsSimpleModule (MonoidAlgebra (ZMod p) ↥(Work.Zassenhaus.pairStab G inf zero)) (Additive ↥U)) := by
  letI : Module (MonoidAlgebra (ZMod p) ↥(Work.Zassenhaus.pairStab G inf zero)) (Additive ↥U) :=
    conjModule hUB hN hcomm hZ
  rw [isSimpleModule_iff]
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have h1 : Subsingleton (Additive ↥U) := by
      constructor
      intro x y
      have hx : x ∈ (⊥ : Submodule (MonoidAlgebra (ZMod p) ↥(Work.Zassenhaus.pairStab G inf zero))
          (Additive ↥U)) := by rw [h]; trivial
      have hy : y ∈ (⊥ : Submodule (MonoidAlgebra (ZMod p) ↥(Work.Zassenhaus.pairStab G inf zero))
          (Additive ↥U)) := by rw [h]; trivial
      rw [Submodule.mem_bot] at hx hy
      rw [hx, hy]
    have h3 : Nat.card ↥U = 1 := Nat.card_eq_one_iff_unique.mpr ⟨h1, ⟨1⟩⟩
    have h4 : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  · by_cases hS : S = ⊥
    · exact Or.inl hS
    · refine Or.inr ?_
      have hF : S.toAddSubgroup ≠ ⊥ := by
        intro hbot
        exact hS (by
          rw [Submodule.eq_bot_iff]
          intro x hx
          have hx' : x ∈ S.toAddSubgroup := hx
          rw [hbot] at hx'
          simpa using (AddSubgroup.mem_bot.mp hx'))
      have hFinv : ∀ (h : ↥(Work.Zassenhaus.pairStab G inf zero)) (x : Additive ↥U),
          x ∈ S.toAddSubgroup →
          Additive.ofMul (conjAut hUB hN h (Additive.toMul x)) ∈ S.toAddSubgroup := by
        intro h x hx
        have h1 := S.smul_mem (MonoidAlgebra.of (ZMod p)
          ↥(Work.Zassenhaus.pairStab G inf zero) h) hx
        rw [of_smul_apply] at h1
        exact h1
      have htop : S.toAddSubgroup = ⊤ :=
        eq_top_of_addSubgroup hUB hN hp hpodd hk hcardU hcardH hfix hF hFinv
      rwa [Submodule.toAddSubgroup_eq_top] at htop

end Simple

section Main

/-- **Z5 (blueprint §ZASS).** Field coordinates on the unipotent group (REVISED after review:
the order `|G_{∞0}| = (p^k-1)/2` of the point stabilizer is now an explicit hypothesis, since
the conclusion's `φ.range = (Eˣ)²` forces it).  If `U ≤ B` is normal in `B` with `|U| = p^k`,
abelian, of exponent `p`, and `H = G_{∞0}` is cyclic of order `(p^k-1)/2` acting
fixed-point-freely on `U`, then there are a field `E` of characteristic `p` with `|E| = p^k`,
an isomorphism `Φ : U ≃* Multiplicative E` of the additive group of `E`, and an injective
`φ : H →* Eˣ` with image `(Eˣ)²` (the squares), such that `Φ` intertwines the conjugation
action of `H` on `U` with multiplication by `φ`.
Route: `ZASS/eq_top_of_isConjInvariant` makes `U` irreducible under `H`, so `E`, the
`𝔽_p`-span of the images of a generator of `H` in `End(U)`, is a finite commutative ring with
no zero divisors, hence a field of order `p^k`, and `U` is one-dimensional over it. -/
theorem exists_field_coordinates {G X : Type} [Group G] [Finite G] [MulAction G X]
    {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hk : 1 ≤ k) {q : ℕ} (hq : q = p ^ k)
    {inf zero : X} (hne : inf ≠ zero)
    {U : Subgroup G} (hUB : U ≤ Work.Zassenhaus.borel G inf) (hcardU : Nat.card U = p ^ k)
    (hcardH : Nat.card (Work.Zassenhaus.pairStab G inf zero) = (q - 1) / 2)
    (hN : (U.subgroupOf (Work.Zassenhaus.borel G inf)).Normal)
    (hcomm : IsMulCommutative U) (hexp : ∀ u ∈ U, u ^ p = 1)
    (hcyc : IsCyclic (Work.Zassenhaus.pairStab G inf zero))
    (hfix : Work.ZASS.FixedPointFreeConj U (Work.Zassenhaus.pairStab G inf zero)) :
    ∃ (E : Type) (_ : Field E) (_ : Fintype E) (_ : CharP E p)
      (Φ : U ≃* Multiplicative E) (φ : Work.Zassenhaus.pairStab G inf zero →* Eˣ),
      Nat.card E = p ^ k ∧ Function.Injective φ ∧
        (∀ e : Eˣ, e ∈ φ.range ↔ ∃ f : Eˣ, f ^ 2 = e) ∧
        (∀ (hh : G) (hhm : hh ∈ Work.Zassenhaus.pairStab G inf zero) (u : G) (hu : u ∈ U),
          Φ ⟨Work.ZASS.conjBy hh u,
              Work.ZASS.mem_conjBy_of_subgroupOf_normal hUB hN hhm.2 hu⟩ =
            Multiplicative.ofAdd ((φ ⟨hh, hhm⟩ : E) * Multiplicative.toAdd (Φ ⟨u, hu⟩))) := by
  classical
  have hp' : p.Prime := Fact.out
  have hcardH' : Nat.card ↥(Work.Zassenhaus.pairStab G inf zero) = (p ^ k - 1) / 2 := by
    rw [hcardH, hq]
  have hE := isElementaryAbelian_of hcomm hexp
  let hZ : Module (ZMod p) (Additive ↥U) :=
    AddCommGroup.zmodModule (fun x => p_nsmul_eq_zero hE x)
  haveI : Module (ZMod p) (Additive ↥U) := hZ
  have hHcomm : ∀ a b : ↥(Work.Zassenhaus.pairStab G inf zero), a * b = b * a := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(Work.Zassenhaus.pairStab G inf zero))
    intro a b
    have ha : a ∈ Subgroup.zpowers g := hg a
    have hb : b ∈ Subgroup.zpowers g := hg b
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact zpow_mul_comm g m n
  letI : CommGroup ↥(Work.Zassenhaus.pairStab G inf zero) :=
    { (inferInstance : Group ↥(Work.Zassenhaus.pairStab G inf zero)) with mul_comm := hHcomm }
  letI : Module (MonoidAlgebra (ZMod p) ↥(Work.Zassenhaus.pairStab G inf zero)) (Additive ↥U) :=
    conjModule hUB hN hcomm hZ
  haveI : IsSimpleModule (MonoidAlgebra (ZMod p) ↥(Work.Zassenhaus.pairStab G inf zero))
      (Additive ↥U) :=
    isSimpleModule_conjModule hUB hN hcomm hZ hp' hp hk hcardU hcardH' hfix
  have hfaith : ∀ c : ↥(Work.Zassenhaus.pairStab G inf zero),
      (∀ x : Additive ↥U,
        MonoidAlgebra.of (ZMod p) ↥(Work.Zassenhaus.pairStab G inf zero) c • x = x) → c = 1 := by
    intro c hc
    have hinj := conjAut_injective (U := U) (inf := inf) (zero := zero) hUB hN hfix hcardU
      hp'.one_lt hk
    have hc1 : conjAut hUB hN c = 1 := by
      refine MulEquiv.ext (fun x => ?_)
      have hx := hc (Additive.ofMul x)
      rw [of_smul_apply] at hx
      exact hx
    exact (injective_iff_map_eq_one (conjAut hUB hN)).mp hinj c hc1
  have hcardM : Nat.card (Additive ↥U) = p ^ k := by
    rw [← hcardU]
    exact Nat.card_congr Additive.ofMul
  obtain ⟨e, μ, hμinj, hcompat⟩ :=
    OddOrder.RepresentationTheory.exists_galoisField_repr_of_faithful_irreducible
      (p := p) (C := ↥(Work.Zassenhaus.pairStab G inf zero)) (M := Additive ↥U) (q := k)
      (by omega) hcardM hfaith
  let Φ : ↥U ≃* Multiplicative (GaloisField p k) := e.toMultiplicative
  refine ⟨GaloisField p k, inferInstance, Fintype.ofFinite _, inferInstance, Φ, μ,
    GaloisField.card p k (by omega), hμinj, ?_, ?_⟩
  · have hcard_range : Nat.card ↥μ.range = (p ^ k - 1) / 2 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hμinj).toEquiv]
      exact hcardH'
    have hunits : Nat.card ((GaloisField p k)ˣ) = p ^ k - 1 := by
      rw [Nat.card_units, GaloisField.card p k (by omega)]
    have hindex : μ.range.index = 2 := by
      have h := Subgroup.index_mul_card μ.range
      rw [hcard_range, hunits] at h
      have hodd : Odd (p ^ k) := hp.pow
      obtain ⟨m, hm⟩ := hodd
      have h2dvd : 2 ∣ p ^ k - 1 := ⟨m, by omega⟩
      have hA : 2 * ((p ^ k - 1) / 2) = p ^ k - 1 := by
        rw [mul_comm]; exact Nat.div_mul_cancel h2dvd
      have hpos : 0 < (p ^ k - 1) / 2 := by
        have h1 : 1 < p ^ k := Nat.one_lt_pow (by omega) hp'.one_lt
        omega
      have h' : μ.range.index * ((p ^ k - 1) / 2) = 2 * ((p ^ k - 1) / 2) := by
        rw [hA]
        exact h
      exact Nat.eq_of_mul_eq_mul_right hpos h'
    exact Work.ZASSF.mem_iff_exists_sq_of_index_two hindex
  · intro hh hhm u hu
    have h1 := hcompat ⟨hh, hhm⟩ (Additive.ofMul ⟨u, hu⟩)
    rw [of_smul_apply] at h1
    have h2 : Φ ⟨Work.ZASS.conjBy hh u,
          Work.ZASS.mem_conjBy_of_subgroupOf_normal hUB hN hhm.2 hu⟩
        = Multiplicative.ofAdd (e (Additive.ofMul ⟨Work.ZASS.conjBy hh u,
            Work.ZASS.mem_conjBy_of_subgroupOf_normal hUB hN hhm.2 hu⟩)) := rfl
    have h3 : e (Additive.ofMul ⟨Work.ZASS.conjBy hh u,
          Work.ZASS.mem_conjBy_of_subgroupOf_normal hUB hN hhm.2 hu⟩)
        = e (conjAut hUB hN ⟨hh, hhm⟩ (Additive.ofMul ⟨u, hu⟩)) := by
      congr 2
    have h4 : Φ ⟨u, hu⟩ = Multiplicative.ofAdd (e (Additive.ofMul ⟨u, hu⟩)) := rfl
    have h5 : Multiplicative.toAdd (Multiplicative.ofAdd (e (Additive.ofMul ⟨u, hu⟩)))
        = e (Additive.ofMul ⟨u, hu⟩) := rfl
    rw [h2, h3, h1, h4, h5]

end Main

end Work.ZASS
