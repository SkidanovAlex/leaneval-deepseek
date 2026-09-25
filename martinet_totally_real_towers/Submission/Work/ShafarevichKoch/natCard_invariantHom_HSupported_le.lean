import Mathlib
import Submission.Work.ShafarevichKoch.SupportedComparison
import Submission.Work.ShafarevichKoch.SupportedSubextensions
import Submission.Work.ShafarevichKoch.SupportedLevel
import Submission.Work.ShafarevichKoch.InertiaCount
import Submission.Work.ShafarevichKoch.natCard_invariantHom_le_of_quotients
import Submission.Work.ShafarevichKoch.isCyclic_inertia_of_tame
import Submission.Work.HopfGaschutz.card_conjInvariantZ1
import Submission.Work.ShafarevichKoch.differentIdeal_eq_top_of_le_kEmpty
import Submission.Work.ShafarevichKoch.lift_le_kEmpty_of_isGalois_differentIdeal_eq_top
import Submission.Work.ShafarevichKoch.isCyclic_inertia_of_le_kSupported
import Submission.Work.ShafarevichKoch.finite_primesOver_finset

/-!
# `Work.ShafarevichKoch.natCard_invariantHom_HSupported_le`
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.ShafarevichKoch

open scoped commutatorElement
open Work.HopfGaschutz
open NumberField

section GroupTheory

variable {G : Type*} [Group G]

/-- The commutator of an element of a normal subgroup with an ambient element lies in the
subgroup. -/
theorem commutator_mem_of_normal (K : Subgroup G) [K.Normal] {x y : G} (hx : x ∈ K) :
    ⁅x, y⁆ ∈ K := by
  have h : y * x⁻¹ * y⁻¹ ∈ K := Subgroup.Normal.conj_mem ‹K.Normal› x⁻¹ (K.inv_mem hx) y
  have h2 : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
    rw [commutatorElement_def]; group
  rw [h2]
  exact K.mul_mem hx h

/-- Conjugation on a normal subgroup is multiplication by the commutator `⁅k⁻¹, g⁆`. -/
theorem conj_eq_mul_commutator (K : Subgroup G) (g : G) (k : K) :
    g * (k : G) * g⁻¹ = (k : G) * ⁅(k : G)⁻¹, g⁆ := by
  rw [commutatorElement_def]; group

/-- The conjugation defect `⁅k⁻¹, g⁆` lies in `K` (`K` normal). -/
theorem commutator_conj_mem (K : Subgroup G) [K.Normal] (g : G) (k : K) :
    ⁅(k : G)⁻¹, g⁆ ∈ K := by
  have h : g * (k : G) * g⁻¹ ∈ K :=
    Subgroup.Normal.conj_mem ‹K.Normal› (k : G) k.2 g
  have h2 : ⁅(k : G)⁻¹, g⁆ = (k : G)⁻¹ * (g * (k : G) * g⁻¹) := by
    rw [commutatorElement_def]; group
  rw [h2]
  exact K.mul_mem (K.inv_mem k.2) h

/-- The conjugation defect lies in the relation-Frattini subgroup `K²[K,G]`. -/
theorem commutator_conj_mem_relFrattiniIn (K : Subgroup G) [K.Normal] (g : G) (k : K) :
    (⟨⁅(k : G)⁻¹, g⁆, commutator_conj_mem K g k⟩ : K) ∈ relFrattiniIn 2 K := by
  rw [mem_relFrattiniIn]
  exact commutator_mem_relFrattini 2 K (K.inv_mem k.2)

/-- **Invariance under conjugation is vanishing on the relation-Frattini subgroup.** -/
theorem conjInvariant_iff_relFrattiniIn_le_ker (K : Subgroup G) [K.Normal]
    (f : K →* Multiplicative (ZMod 2)) :
    (∀ (g : G) (k : K),
        f ⟨g * (k : G) * g⁻¹, Subgroup.Normal.conj_mem ‹K.Normal› (k : G) k.2 g⟩ = f k) ↔
      relFrattiniIn 2 K ≤ f.ker := by
  constructor
  · intro hinv
    have hmap : relFrattini 2 K ≤ (f.ker).map (Subgroup.subtype K) := by
      refine sup_le ?_ ?_
      · rw [pPower, Subgroup.closure_le]
        rintro x ⟨k, hk, rfl⟩
        refine Subgroup.mem_map.mpr ⟨⟨k ^ 2, K.pow_mem hk 2⟩, ?_, rfl⟩
        rw [MonoidHom.mem_ker]
        have heq : (⟨k ^ 2, K.pow_mem hk 2⟩ : K) = (⟨k, hk⟩ : K) ^ 2 := Subtype.ext rfl
        rw [heq, map_pow, sq_eq_one_zmodTwo]
      · rw [Subgroup.commutator_le]
        intro a ha b _
        have hd : f (⟨⁅((⟨a⁻¹, K.inv_mem ha⟩ : K) : G)⁻¹, b⁆,
            commutator_conj_mem K b ⟨a⁻¹, K.inv_mem ha⟩⟩ : K) = 1 := by
          have hb := hinv b ⟨a⁻¹, K.inv_mem ha⟩
          have heq : (⟨b * ((⟨a⁻¹, K.inv_mem ha⟩ : K) : G) * b⁻¹,
                Subgroup.Normal.conj_mem ‹K.Normal› ((⟨a⁻¹, K.inv_mem ha⟩ : K) : G)
                  (⟨a⁻¹, K.inv_mem ha⟩ : K).2 b⟩ : K) =
              ⟨a⁻¹, K.inv_mem ha⟩ * ⟨⁅((⟨a⁻¹, K.inv_mem ha⟩ : K) : G)⁻¹, b⁆,
                commutator_conj_mem K b ⟨a⁻¹, K.inv_mem ha⟩⟩ := by
            apply Subtype.ext
            simp only [Subgroup.coe_mul]
            show b * ((⟨a⁻¹, K.inv_mem ha⟩ : K) : G) * b⁻¹ =
              ((⟨a⁻¹, K.inv_mem ha⟩ : K) : G) * ⁅((⟨a⁻¹, K.inv_mem ha⟩ : K) : G)⁻¹, b⁆
            rw [commutatorElement_def]
            group
          rw [heq, map_mul] at hb
          exact mul_left_cancel (by rw [hb, mul_one])
        have heq2 : (⟨⁅a, b⁆, commutator_mem_of_normal K ha⟩ : K) =
            ⟨⁅((⟨a⁻¹, K.inv_mem ha⟩ : K) : G)⁻¹, b⁆,
              commutator_conj_mem K b ⟨a⁻¹, K.inv_mem ha⟩⟩ := by
          apply Subtype.ext
          show ⁅a, b⁆ = ⁅((⟨a⁻¹, K.inv_mem ha⟩ : K) : G)⁻¹, b⁆
          congr 1
          simpa using (inv_inv a : (a⁻¹)⁻¹ = a)
        rw [← heq2] at hd
        exact Subgroup.mem_map.mpr ⟨_, MonoidHom.mem_ker.mpr hd, rfl⟩
    intro x hx
    rw [mem_relFrattiniIn] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hmap hx)
    have hxy : y = x := Subtype.ext hyx
    rw [← hxy]
    exact MonoidHom.mem_ker.mp hy
  · intro hle g k
    have hone : f ⟨⁅(k : G)⁻¹, g⁆, commutator_conj_mem K g k⟩ = 1 :=
      MonoidHom.mem_ker.mp (hle (commutator_conj_mem_relFrattiniIn K g k))
    have hconj : (⟨g * (k : G) * g⁻¹, Subgroup.Normal.conj_mem ‹K.Normal› (k : G) k.2 g⟩ : K)
        = k * ⟨⁅(k : G)⁻¹, g⁆, commutator_conj_mem K g k⟩ := by
      apply Subtype.ext
      show g * (k : G) * g⁻¹ = (k : G) * ⁅(k : G)⁻¹, g⁆
      rw [commutatorElement_def]
      group
    rw [hconj, map_mul, hone, mul_one]

/-- **Cardinality of the invariant characters = size of the relation-Frattini quotient.** -/
theorem natCard_conjInvariant_hom_eq_relFrattiniQuotient (K : Subgroup G) [K.Normal]
    [Fintype K] :
    Nat.card {f : K →* Multiplicative (ZMod 2) //
        ∀ (g : G) (k : K),
          f ⟨g * (k : G) * g⁻¹, Subgroup.Normal.conj_mem ‹K.Normal› (k : G) k.2 g⟩ = f k} =
      Nat.card (K ⧸ relFrattiniIn 2 K) := by
  classical
  haveI : IsMulCommutative (K ⧸ relFrattiniIn 2 K) := by
    rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
    change ⁅(⊤ : Subgroup K), ⊤⁆ ≤ relFrattiniIn 2 K
    rw [Subgroup.commutator_le]
    intro a _ b _
    show ((Subgroup.subtype K) ⁅a, b⁆) ∈ relFrattini 2 K
    rw [map_commutatorElement]
    exact Subgroup.mem_sup_right ((Subgroup.commutator_mono le_rfl le_top)
      (Subgroup.commutator_mem_commutator a.2 b.2))
  have h2 : ∀ v : K ⧸ relFrattiniIn 2 K, v * v = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | _ x =>
      show QuotientGroup.mk' (relFrattiniIn 2 K) (x * x) = 1
      refine (QuotientGroup.eq_one_iff (x * x)).mpr ?_
      show ((x * x : K) : G) ∈ relFrattini 2 K
      rw [Subgroup.coe_mul]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨(x : G), x.2, by rw [pow_two]⟩)
  have h := Nat.card_congr ((Equiv.subtypeEquiv (Equiv.refl (K →* Multiplicative (ZMod 2)))
      (fun f => conjInvariant_iff_relFrattiniIn_le_ker K f)).trans
      (Work.HopfGaschutz.quotientEquiv (relFrattiniIn 2 K)))
  rw [h]
  exact natCard_hom_zmodTwo_multiplicative h2

end GroupTheory

section Transfer

variable {G L : Type*} [Group G] [Group L]

/-- **Transfer of invariant characters along a surjection.**

Let `H ◁ G`, let `r : G →* L` be a surjective homomorphism with kernel `U = ker r`, and let
`K ≤ L` be a subgroup with `K = H.map r` (so that `K` is the image of `H` in the finite level).
Then the `G`-invariant characters of `H` vanishing on `U` are exactly the `L`-invariant
characters of `K`.

The map is `φ ↦ (k ↦ φ (c k))` for a chosen lift `c k ∈ H` of `k ∈ K` (well defined because two
lifts differ by an element of `U`, on which `φ` vanishes); its inverse is the pullback
`ψ ↦ ψ ∘ ρ`, where `ρ : H →* K` is the restriction of `r` to `H`. -/
noncomputable def equiv_invariantHom_transfer (H : Subgroup G) [H.Normal] (U : Subgroup G)
    [U.Normal] (r : G →* L) (hker : r.ker = U) (hsurj : Function.Surjective r)
    (K : Subgroup L) [K.Normal] (hK : K = H.map r) :
    {φ : H →* Multiplicative (ZMod 2) //
        (∀ (g : G) (n : H),
          φ ⟨g * (n : G) * g⁻¹, Subgroup.Normal.conj_mem ‹H.Normal› (n : G) n.2 g⟩ = φ n) ∧
        (∀ n : H, (n : G) ∈ U → φ n = 1)} ≃
      {ψ : K →* Multiplicative (ZMod 2) //
        ∀ (l : L) (k : K),
          ψ ⟨l * (k : L) * l⁻¹, Subgroup.Normal.conj_mem ‹K.Normal› (k : L) k.2 l⟩ = ψ k} := by
  classical
  -- the restriction of `r` to `H`, with values in `K`
  let ρ : H →* K := MonoidHom.codRestrict (r.comp H.subtype) K
    (fun x => hK.symm ▸ Subgroup.mem_map_of_mem r x.2)
  have hρker : ∀ x : H, x ∈ ρ.ker ↔ (x : G) ∈ U := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h : r (x : G) = 1 := by
        have := congrArg (fun y : K => (y : L)) hx
        simpa [ρ, MonoidHom.comp_apply] using this
      rw [← hker]
      exact MonoidHom.mem_ker.mpr h
    · intro hx
      apply Subtype.ext
      change r (x : G) = 1
      exact MonoidHom.mem_ker.mp (by rw [hker]; exact hx)
  have hρsurj : Function.Surjective ρ := by
    intro k
    have hmem : (k : L) ∈ H.map r := hK ▸ k.2
    obtain ⟨x, hx, hxk⟩ := Subgroup.mem_map.mp hmem
    exact ⟨⟨x, hx⟩, Subtype.ext hxk⟩
  let c : K → H := fun k => Classical.choose (hρsurj k)
  have hc : ∀ k : K, ρ (c k) = k := fun k => Classical.choose_spec (hρsurj k)
  have hwell : ∀ (φ : H →* Multiplicative (ZMod 2))
      (hvan : ∀ n : H, (n : G) ∈ U → φ n = 1)
      (k : K) (h : H), ρ h = k → φ h = φ (c k) := by
    intro φ hvan k h hh
    have hmem : (h * (c k)⁻¹ : H) ∈ ρ.ker := by
      rw [hρker]
      have : ρ (h * (c k)⁻¹) = 1 := by rw [map_mul, map_inv, hh, hc k, mul_inv_cancel]
      exact (hρker _).mp (MonoidHom.mem_ker.mpr this)
    have h1 := hvan (h * (c k)⁻¹) ((hρker _).mp (MonoidHom.mem_ker.mpr (by
      rw [map_mul, map_inv, hh, hc k, mul_inv_cancel])))
    have h2 : h = (h * (c k)⁻¹) * c k := by group
    rw [h2, map_mul, h1, one_mul]
  have hmap_mul : ∀ (φ : H →* Multiplicative (ZMod 2))
      (hvan : ∀ n : H, (n : G) ∈ U → φ n = 1) (a b : K),
      φ (c (a * b)) = φ (c a) * φ (c b) := by
    intro φ hvan a b
    have h := hwell φ hvan (a * b) (c a * c b) (by rw [map_mul, hc a, hc b])
    rw [← h, map_mul]
  have hinv : ∀ (φ : H →* Multiplicative (ZMod 2))
      (hinvφ : ∀ (g : G) (n : H),
          φ ⟨g * (n : G) * g⁻¹, Subgroup.Normal.conj_mem ‹H.Normal› (n : G) n.2 g⟩ = φ n)
      (hvan : ∀ n : H, (n : G) ∈ U → φ n = 1)
      (l : L) (k : K),
      φ (c ⟨l * (k : L) * l⁻¹, Subgroup.Normal.conj_mem ‹K.Normal› (k : L) k.2 l⟩)
        = φ (c k) := by
    intro φ hinvφ hvan l k
    obtain ⟨g, hg⟩ := hsurj l
    have hmemH : g * (c k : G) * g⁻¹ ∈ H :=
      Subgroup.Normal.conj_mem ‹H.Normal› (c k : G) (c k).2 g
    have hr : ρ ⟨g * (c k : G) * g⁻¹, hmemH⟩ =
        ⟨l * (k : L) * l⁻¹, Subgroup.Normal.conj_mem ‹K.Normal› (k : L) k.2 l⟩ := by
      apply Subtype.ext
      change r (g * (c k : G) * g⁻¹) = l * (k : L) * l⁻¹
      rw [map_mul, map_mul, map_inv, hg]
      have hh : r (c k : G) = (k : L) := congrArg (fun y : K => (y : L)) (hc k)
      rw [hh]
    have h := hwell φ hvan
      ⟨l * (k : L) * l⁻¹, Subgroup.Normal.conj_mem ‹K.Normal› (k : L) k.2 l⟩
      ⟨g * (c k : G) * g⁻¹, hmemH⟩ hr
    rw [← h]
    exact hinvφ g (c k)
  refine
    { toFun := fun φ => ⟨MonoidHom.mk' (fun k => φ.1 (c k)) (fun a b => hmap_mul φ.1 φ.2.2 a b),
        fun l k => hinv φ.1 φ.2.1 φ.2.2 l k⟩
      invFun := fun ψ => ⟨ψ.1.comp ρ, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro g n
    simp only [MonoidHom.comp_apply]
    have h : ρ (⟨g * (n : G) * g⁻¹,
        Subgroup.Normal.conj_mem ‹H.Normal› (n : G) n.2 g⟩ : H) =
        ⟨r g * (ρ n : L) * (r g)⁻¹,
          Subgroup.Normal.conj_mem ‹K.Normal› (ρ n : L) (ρ n).2 (r g)⟩ := by
      apply Subtype.ext
      change r (g * (n : G) * g⁻¹) = r g * (ρ n : L) * (r g)⁻¹
      rw [map_mul, map_mul, map_inv]
      rfl
    rw [h, ψ.2 (r g) (ρ n)]
  · intro n hn
    have h1 : ρ n = 1 := MonoidHom.mem_ker.mp ((hρker n).mpr hn)
    rw [MonoidHom.comp_apply, h1, map_one]
  · intro φ
    apply Subtype.ext
    apply MonoidHom.ext
    intro h
    show φ.1 (c (ρ h)) = φ.1 h
    exact (hwell φ.1 φ.2.2 (ρ h) h rfl).symm
  · intro ψ
    apply Subtype.ext
    apply MonoidHom.ext
    intro k
    show ψ.1 (ρ (c k)) = ψ.1 k
    rw [hc k]

end Transfer

section Cyclic

variable {X : Type*} [Group X]

/-- **A cyclic subgroup is generated by one element** (closure form, for `InertiaCount`). -/
theorem exists_closure_singleton_eq_of_isCyclic (I : Subgroup X) (hI : IsCyclic ↥I) :
    ∃ g : X, g ∈ I ∧ Subgroup.closure {g} = I := by
  obtain ⟨g, hg⟩ := hI.exists_generator
  refine ⟨(g : X), g.2, ?_⟩
  have htop : Subgroup.zpowers g = ⊤ := (Subgroup.eq_top_iff' _).mpr hg
  have hmem : Subgroup.zpowers ((g : ↥I) : X) = I := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.zpowers_le]; exact g.2
    · intro x hx
      have h1 : (⟨x, hx⟩ : ↥I) ∈ Subgroup.zpowers g := by rw [htop]; trivial
      rw [Subgroup.mem_zpowers_iff] at h1 ⊢
      obtain ⟨n, hn⟩ := h1
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  rw [Subgroup.zpowers_eq_closure] at hmem
  exact hmem

end Cyclic



section Main

/-- `H_S = Gal(k_S/k_∅)` really is the fixing subgroup of `k_∅` inside `k_S`. -/
theorem HSupported_eq_fixingSubgroup (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]
    (S : Finset ℕ) :
    HSupported F p S = (kEmptyInS F p S).fixingSubgroup := by
  ext σ
  show σ ∈ (restrictToEmpty F p S).ker ↔ σ ∈ (kEmptyInS F p S).fixingSubgroup
  rw [← IntermediateField.restrictNormalHom_ker (E := kEmptyInS F p S), MonoidHom.mem_ker]
  constructor
  · intro h
    refine (AlgEquiv.autCongr (kEmptyEquiv F p S)).injective ?_
    rw [map_one]
    exact h
  · intro h
    show (AlgEquiv.autCongr (kEmptyEquiv F p S))
        ((AlgEquiv.restrictNormalHom (K₁ := ↥(kSupported F p S)) ↥(kEmptyInS F p S)) σ) = 1
    rw [h, map_one]

/-- Every finite Galois level of `k_S` has pro-`2` Galois group. -/
theorem isPGroup_gal_of_intermediate {F : Type} [Field F] [NumberField F] {S : Finset ℕ}
    (L : IntermediateField F ↥(kSupported F 2 S)) [FiniteDimensional F L] [IsGalois F L]
    [NumberField ↥L] : IsPGroup 2 (↥L ≃ₐ[F] ↥L) := by
  have hfd' : FiniteDimensional F ↥(IntermediateField.lift L) :=
    (IntermediateField.liftAlgEquiv L).toLinearEquiv.finiteDimensional
  haveI : FiniteDimensional F ↥(IntermediateField.lift L) := hfd'
  have hgal' : IsGalois F ↥(IntermediateField.lift L) :=
    IsGalois.of_algEquiv (IntermediateField.liftAlgEquiv L)
  haveI : IsGalois F ↥(IntermediateField.lift L) := hgal'
  have hnum' : NumberField ↥(IntermediateField.lift L) :=
    NumberField.of_module_finite F ↥(IntermediateField.lift L)
  haveI : NumberField ↥(IntermediateField.lift L) := hnum'
  have h := (kSupported_supp_and_pGroup (F := F) (p := 2) S (IntermediateField.lift_le L)).1
  exact h.of_equiv (AlgEquiv.autCongr (IntermediateField.liftAlgEquiv L)).symm

/-- The relative different of a finite Galois level of `k_S` is supported on `S`. -/
theorem differentIdeal_supp_of_le_kSupported {F : Type} [Field F] [NumberField F] {S : Finset ℕ}
    (L : IntermediateField F ↥(kSupported F 2 S)) [FiniteDimensional F L] [IsGalois F L]
    [NumberField ↥L] :
    ∀ (P : Ideal (NumberField.RingOfIntegers ↥L)), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥L) →
        ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := by
  have hfd' : FiniteDimensional F ↥(IntermediateField.lift L) :=
    (IntermediateField.liftAlgEquiv L).toLinearEquiv.finiteDimensional
  haveI : FiniteDimensional F ↥(IntermediateField.lift L) := hfd'
  have hgal' : IsGalois F ↥(IntermediateField.lift L) :=
    IsGalois.of_algEquiv (IntermediateField.liftAlgEquiv L)
  haveI : IsGalois F ↥(IntermediateField.lift L) := hgal'
  have hnum' : NumberField ↥(IntermediateField.lift L) :=
    NumberField.of_module_finite F ↥(IntermediateField.lift L)
  haveI : NumberField ↥(IntermediateField.lift L) := hnum'
  have h := (kSupported_supp_and_pGroup (F := F) (p := 2) S (IntermediateField.lift_le L)).2
  exact Submission.NumberField.differentIdeal_supp_of_algEquiv (F := F) S
    (IntermediateField.liftAlgEquiv L).symm h

end Main

section Target

theorem natCard_invariantHom_HSupported_le {F : Type} [Field F] [NumberField F] (S : Finset ℕ)
    (hodd : ∀ q ∈ S, 2 < q) (s : ℕ)
    (hcard : Nat.card {𝔮 : Ideal (NumberField.RingOfIntegers F) // 𝔮.IsPrime ∧
      ∃ q ∈ S, 𝔮.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))} ≤ s) :
    Nat.card {φ : ↥(Work.ShafarevichKoch.HSupported F 2 S) →* Multiplicative (ZMod 2) //
      Continuous (φ : ↥(Work.ShafarevichKoch.HSupported F 2 S) → Multiplicative (ZMod 2)) ∧
      ∀ (g : ↥(Work.ShafarevichKoch.kSupported F 2 S) ≃ₐ[F]
            ↥(Work.ShafarevichKoch.kSupported F 2 S))
        (n : ↥(Work.ShafarevichKoch.HSupported F 2 S)),
        φ ⟨g * (n : ↥(Work.ShafarevichKoch.kSupported F 2 S) ≃ₐ[F]
              ↥(Work.ShafarevichKoch.kSupported F 2 S)) * g⁻¹,
            Subgroup.Normal.conj_mem (Work.ShafarevichKoch.normal_HSupported F 2 S)
              (n : ↥(Work.ShafarevichKoch.kSupported F 2 S) ≃ₐ[F]
                ↥(Work.ShafarevichKoch.kSupported F 2 S)) n.2 g⟩ = φ n} ≤ 2 ^ s := by
  classical
  haveI hGalKS : IsGalois F ↥(kSupported F 2 S) := isGalois_kSupported (F := F) (S := S)
  refine natCard_invariantHom_le_of_quotients (HSupported F 2 S) s ?_
  intro U hUnorm hUopen
  -- ## the finite level
  let L : IntermediateField F ↥(kSupported F 2 S) := IntermediateField.fixedField U
  have hUc : IsClosed (U : Set (↥(kSupported F 2 S) ≃ₐ[F] ↥(kSupported F 2 S))) :=
    Subgroup.isClosed_of_isOpen U hUopen
  have hfix : L.fixingSubgroup = U := InfiniteGalois.fixingSubgroup_fixedField ⟨U, hUc⟩
  haveI hfdL : FiniteDimensional F ↥L := by
    rw [← InfiniteGalois.isOpen_iff_finite L, hfix]
    exact hUopen
  haveI hgalL : IsGalois F ↥L := by
    rw [← InfiniteGalois.normal_iff_isGalois L, hfix]
    exact hUnorm
  haveI hnormL : Normal F ↥L := hgalL.to_normal
  haveI hnumL : NumberField ↥L := NumberField.of_module_finite F ↥L
  -- ## the restriction `Gal(k_S/F) →* Gal(L/F)`
  let r : (↥(kSupported F 2 S) ≃ₐ[F] ↥(kSupported F 2 S)) →* (↥L ≃ₐ[F] ↥L) :=
    AlgEquiv.restrictNormalHom (K₁ := ↥(kSupported F 2 S)) ↥L
  have hker : r.ker = U :=
    (IntermediateField.restrictNormalHom_ker (E := L)).trans hfix
  have hsurj : Function.Surjective r :=
    AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥L) (E := ↥(kSupported F 2 S))
  -- ## the unramified part of `L`
  let M : IntermediateField F ↥L := IntermediateField.fixedField ((HSupported F 2 S).map r)
  have hmapN : ((HSupported F 2 S).map r).Normal :=
    Subgroup.Normal.map (normal_HSupported F 2 S) r hsurj
  haveI : ((HSupported F 2 S).map r).Normal := hmapN
  have hMfix : M.fixingSubgroup = (HSupported F 2 S).map r :=
    IntermediateField.fixingSubgroup_fixedField _
  haveI hgalM : IsGalois F ↥M := inferInstance
  haveI hMnorm : (M.fixingSubgroup).Normal := (InfiniteGalois.normal_iff_isGalois M).mpr hgalM
  haveI hfdM : FiniteDimensional F ↥M := inferInstance
  haveI hnumM : NumberField ↥M := NumberField.of_module_finite F ↥M
  have hliftM : IntermediateField.lift M = kEmptyInS F 2 S ⊓ L := by
    have h1 : IntermediateField.fixedField (HSupported F 2 S) = kEmptyInS F 2 S := by
      rw [HSupported_eq_fixingSubgroup F 2 S]
      exact InfiniteGalois.fixedField_fixingSubgroup (kEmptyInS F 2 S)
    have h2 := InfiniteGalois.restrict_fixedField (k := F) (K := ↥(kSupported F 2 S))
      (H := HSupported F 2 S) L
    rw [h1] at h2
    exact h2.symm
  -- ## `M` is unramified over `F`
  have hMunr : differentIdeal (𝓞 F) (𝓞 ↥M) = ⊤ := by
    have hfd' : FiniteDimensional F ↥(IntermediateField.lift M) :=
      (IntermediateField.liftAlgEquiv M).toLinearEquiv.finiteDimensional
    haveI : FiniteDimensional F ↥(IntermediateField.lift M) := hfd'
    have hgal' : IsGalois F ↥(IntermediateField.lift M) :=
      IsGalois.of_algEquiv (IntermediateField.liftAlgEquiv M)
    haveI : IsGalois F ↥(IntermediateField.lift M) := hgal'
    have hnum' : NumberField ↥(IntermediateField.lift M) :=
      NumberField.of_module_finite F ↥(IntermediateField.lift M)
    haveI : NumberField ↥(IntermediateField.lift M) := hnum'
    have hMle : IntermediateField.lift M ≤ kEmptyInS F 2 S := by
      rw [hliftM]; exact inf_le_left
    exact Work.ClassFieldTower.differentIdeal_eq_top_of_algEquiv
      (IntermediateField.liftAlgEquiv M).symm
      (differentIdeal_eq_top_of_le_kEmpty (F := F) S (IntermediateField.lift M) hMle)
  -- ## maximality of `M`
  have hMmax : ∀ (K : IntermediateField F ↥L) [FiniteDimensional F ↥K] [IsGalois F ↥K]
      [NumberField ↥K], differentIdeal (𝓞 F) (𝓞 ↥K) = ⊤ → K ≤ M := by
    intro K hfdK hgalK hnumK hK
    haveI : FiniteDimensional F ↥K := hfdK
    haveI : IsGalois F ↥K := hgalK
    haveI : NumberField ↥K := hnumK
    haveI hnormK : Normal F ↥K := hgalK.to_normal
    haveI hpgK : IsPGroup 2 (↥K ≃ₐ[F] ↥K) :=
      (isPGroup_gal_of_intermediate L).of_surjective
        (AlgEquiv.restrictNormalHom (K₁ := ↥L) ↥K)
        (AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥K) (E := ↥L))
    have hKle : IntermediateField.lift K ≤ kEmptyInS F 2 S :=
      lift_le_kEmpty_of_isGalois_differentIdeal_eq_top K hpgK hK
    intro x hx
    have hxK : (↑x : ↥(kSupported F 2 S)) ∈ IntermediateField.lift K :=
      (IntermediateField.mem_lift x).mpr hx
    have hxE : (↑x : ↥(kSupported F 2 S)) ∈ kEmptyInS F 2 S := hKle hxK
    have hxM : (↑x : ↥(kSupported F 2 S)) ∈ IntermediateField.lift M := by
      rw [hliftM]; exact ⟨hxE, x.2⟩
    exact (IntermediateField.mem_lift x).mp hxM
  -- ## the index set and the inertia generators
  let ι := {𝔮 : Ideal (𝓞 F) // 𝔮.IsPrime ∧ ∃ q ∈ S, 𝔮.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))}
  haveI hιFinite : Finite ι := finite_primesOver_finset (F := F) S
  haveI hιfin : Fintype ι := Fintype.ofFinite ι
  have hQexist : ∀ i : ι, ∃ Q : Ideal (𝓞 ↥L), Q.IsPrime ∧ Q.LiesOver i.1 := by
    intro i
    haveI : i.1.IsPrime := i.2.1
    obtain ⟨Q, -, hQprime, hQunder⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral (R := 𝓞 F) (S := 𝓞 ↥L) i.1 ⊥ (by simp)
    exact ⟨Q, hQprime, ⟨hQunder.symm⟩⟩
  let Q : ι → Ideal (𝓞 ↥L) := fun i => Classical.choose (hQexist i)
  have hQprime : ∀ i, (Q i).IsPrime := fun i => (Classical.choose_spec (hQexist i)).1
  have hQlies : ∀ i, (Q i).LiesOver i.1 := fun i => (Classical.choose_spec (hQexist i)).2
  haveI hQprimeI : ∀ i, (Q i).IsPrime := hQprime
  haveI hQliesI : ∀ i, (Q i).LiesOver i.1 := hQlies
  have hQ : ∀ i, (Q i).IsPrime ∧ ∃ q ∈ S, (Q i).LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := by
    intro i
    obtain ⟨q, hqS, hq⟩ := i.2.2
    exact ⟨hQprime i, q, hqS, Ideal.LiesOver.trans (Q i) i.1 (Ideal.span ({(q : ℤ)} : Set ℤ))⟩
  have hcov : ∀ (P : Ideal (𝓞 ↥L)), P.IsPrime →
      (∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) →
        ∃ (i : ι) (σ : ↥L ≃ₐ[F] ↥L), P = conjIdeal σ (Q i) := by
    intro P hP hPS
    obtain ⟨q, hqS, hq⟩ := hPS
    haveI : P.IsPrime := hP
    haveI hPunder : (P.under (𝓞 F)).IsPrime := Ideal.IsPrime.under (𝓞 F) P
    have hmem : (P.under (𝓞 F)).IsPrime ∧ ∃ q ∈ S,
        (P.under (𝓞 F)).LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := by
      refine ⟨inferInstance, q, hqS, ?_⟩
      haveI : P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := hq
      exact Ideal.LiesOver.tower_bot P (P.under (𝓞 F)) (Ideal.span ({(q : ℤ)} : Set ℤ))
    let i0 : ι := ⟨P.under (𝓞 F), hmem⟩
    haveI hQli : (Q i0).LiesOver (P.under (𝓞 F)) := hQlies i0
    haveI hPli : P.LiesOver (P.under (𝓞 F)) := Ideal.LiesOver.mk rfl
    obtain ⟨σ, hσ⟩ := exists_conjIdeal_eq_of_liesOver (F := F) (L := ↥L)
      (P.under (𝓞 F)) (Q i0) P
    exact ⟨i0, σ, hσ⟩
  have hg_exists : ∀ i : ι, ∃ g : ↥L ≃ₐ[F] ↥L, g ∈ Ideal.inertia (↥L ≃ₐ[F] ↥L) (Q i) ∧
      Subgroup.closure {g} = Ideal.inertia (↥L ≃ₐ[F] ↥L) (Q i) := by
    intro i
    have hcyc : IsCyclic ↥(Ideal.inertia (↥L ≃ₐ[F] ↥L) (Q i)) :=
      isCyclic_inertia_of_le_kSupported (S := S) hodd L (isPGroup_gal_of_intermediate L) (Q i)
        (by obtain ⟨q, hqS, hq⟩ := i.2.2
            exact ⟨q, hqS, Ideal.LiesOver.trans (Q i) i.1 (Ideal.span ({(q : ℤ)} : Set ℤ))⟩)
    exact exists_closure_singleton_eq_of_isCyclic _ hcyc
  let g : ι → ↥L ≃ₐ[F] ↥L := fun i => Classical.choose (hg_exists i)
  have hg_mem : ∀ i, g i ∈ Ideal.inertia (↥L ≃ₐ[F] ↥L) (Q i) :=
    fun i => (Classical.choose_spec (hg_exists i)).1
  have hg_gen : ∀ i, Subgroup.closure {g i} = Ideal.inertia (↥L ≃ₐ[F] ↥L) (Q i) :=
    fun i => (Classical.choose_spec (hg_exists i)).2
  -- ## the finite level count
  have hkey : Nat.card (↥(M.fixingSubgroup) ⧸ relFrattiniIn 2 (M.fixingSubgroup)) ≤
      2 ^ Fintype.card ι :=
    card_relFrattiniQuotient_fixingSubgroup_le (F := F) (L := ↥L) S
      (differentIdeal_supp_of_le_kSupported L) M hMunr hMmax Q hQ hcov g hg_mem hg_gen
  -- ## the transfer and the dictionary
  have htrans := equiv_invariantHom_transfer (H := HSupported F 2 S) (U := U) (r := r)
    hker hsurj M.fixingSubgroup hMfix
  have hdict := natCard_conjInvariant_hom_eq_relFrattiniQuotient (G := ↥L ≃ₐ[F] ↥L)
    (K := M.fixingSubgroup)
  have hιs : Fintype.card ι ≤ s := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  haveI hfinK : Finite ↥(M.fixingSubgroup) := by
    haveI : Fintype (↥L ≃ₐ[F] ↥L) := AlgEquiv.fintype F ↥L
    infer_instance
  haveI hfinHom : Finite (↥(M.fixingSubgroup) →* Multiplicative (ZMod 2)) :=
    Finite.of_injective (fun f : ↥(M.fixingSubgroup) →* Multiplicative (ZMod 2) => fun k => f k)
      (fun f g h => MonoidHom.ext (congrFun h))
  haveI hfinA : Finite {φ : ↥(HSupported F 2 S) →* Multiplicative (ZMod 2) //
      (∀ (g : ↥(kSupported F 2 S) ≃ₐ[F] ↥(kSupported F 2 S))
        (n : ↥(HSupported F 2 S)),
        φ ⟨g * (n : ↥(kSupported F 2 S) ≃ₐ[F] ↥(kSupported F 2 S)) * g⁻¹,
            Subgroup.Normal.conj_mem (normal_HSupported F 2 S)
              (n : ↥(kSupported F 2 S) ≃ₐ[F] ↥(kSupported F 2 S)) n.2 g⟩ = φ n) ∧
      (∀ n : ↥(HSupported F 2 S), (n : ↥(kSupported F 2 S) ≃ₐ[F] ↥(kSupported F 2 S)) ∈ U →
        φ n = 1)} := by
    haveI hfinB : Finite {ψ : ↥(M.fixingSubgroup) →* Multiplicative (ZMod 2) //
        ∀ (l : ↥L ≃ₐ[F] ↥L) (k : ↥(M.fixingSubgroup)),
          ψ ⟨l * (k : ↥L ≃ₐ[F] ↥L) * l⁻¹,
            Subgroup.Normal.conj_mem ‹(M.fixingSubgroup).Normal› (k : ↥L ≃ₐ[F] ↥L) k.2 l⟩ =
            ψ k} :=
      Finite.of_injective Subtype.val Subtype.val_injective
    exact Finite.of_injective htrans.toFun htrans.injective
  refine ⟨hfinA, ?_⟩
  calc Nat.card {φ : ↥(HSupported F 2 S) →* Multiplicative (ZMod 2) //
        (∀ (g : ↥(kSupported F 2 S) ≃ₐ[F] ↥(kSupported F 2 S))
          (n : ↥(HSupported F 2 S)),
          φ ⟨g * (n : ↥(kSupported F 2 S) ≃ₐ[F] ↥(kSupported F 2 S)) * g⁻¹,
              Subgroup.Normal.conj_mem (normal_HSupported F 2 S)
                (n : ↥(kSupported F 2 S) ≃ₐ[F] ↥(kSupported F 2 S)) n.2 g⟩ = φ n) ∧
        (∀ n : ↥(HSupported F 2 S), (n : ↥(kSupported F 2 S) ≃ₐ[F] ↥(kSupported F 2 S)) ∈ U →
          φ n = 1)}
      = Nat.card {ψ : ↥(M.fixingSubgroup) →* Multiplicative (ZMod 2) //
          ∀ (l : ↥L ≃ₐ[F] ↥L) (k : ↥(M.fixingSubgroup)),
            ψ ⟨l * (k : ↥L ≃ₐ[F] ↥L) * l⁻¹,
              Subgroup.Normal.conj_mem ‹(M.fixingSubgroup).Normal› (k : ↥L ≃ₐ[F] ↥L) k.2 l⟩ =
              ψ k} := Nat.card_congr htrans
    _ = Nat.card (↥(M.fixingSubgroup) ⧸ relFrattiniIn 2 (M.fixingSubgroup)) := hdict
    _ ≤ 2 ^ Fintype.card ι := hkey
    _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hιs

end Target

end Work.ShafarevichKoch
