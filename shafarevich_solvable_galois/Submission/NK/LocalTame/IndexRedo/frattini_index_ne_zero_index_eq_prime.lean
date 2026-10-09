import Mathlib
import Submission.NK.LocalTame.IndexPrime.Basic
import Submission.NK.LocalTame.lFrattini_isOpen
import Submission.NK.LocalTame.cruxCompactExpPrimeFinite
import Submission.NK.LocalTame.IndexRedo.exists_hom_extend_of_index_prime
import Submission.NK.LocalTame.IndexRedo.frattini_index_ne_zero_of_sup_zpowers_commutator
import Submission.NK.LocalTame.IndexRedo.relIndex_sup_zpowers_ne_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finiteness of the `ℓ`-Frattini index of an open normal subgroup of index `ℓ`

Let `G` be a compact Hausdorff topological group, `ℓ` a prime number, and suppose that every
*normal* subgroup of `G` of index `ℓ` is open.  Let `M ⊴ G` be an open normal subgroup with
`[G : M] = ℓ`.  Then `M ^ ℓ · [M, M]` has finite index in `M`.

## Structure of the proof

Let `D` be the intersection of all normal subgroups of `G` of index `ℓ`; by
`NK.LocalTame.lFrattini_isOpen` it is open, so `D ∩ M` has finite index in `M`.

* **Containment.**  Choose `g ∉ M`.  For `x ∈ M` with `x ∉ K := M^ℓ·[M,M]·[⟨g⟩,M]·⟨g^ℓ⟩` one
  separates `x` from `K` by a character `χ : M → ZMod ℓ` (an abelian group of exponent `ℓ`),
  which is invariant under conjugation by `g` and satisfies `χ(g^ℓ) = 1`.  The extension lemma
  `exists_hom_extend_of_index_prime` extends `χ` to `G`, and the kernel of the extension is a
  normal subgroup of index `ℓ`, hence contains `D`.  Therefore `x ∉ D`, and `D ∩ M ⊆ K`.
* **Removing `⟨g^ℓ⟩`.**  Since `(g^ℓ)^ℓ ∈ M^ℓ ⊆ L := M^ℓ·[M,M]·[⟨g⟩,M]`, the cyclicity lemma
  `relIndex_sup_zpowers_ne_zero` shows that `L` has finite index in `K`.
* **Removing `[⟨g⟩,M]`.**  The Nakayama lemma `frattini_index_ne_zero_of_sup_zpowers_commutator`
  shows that `M^ℓ·[M,M]` has finite index in `M` as soon as `L` has finite index in `M`.
-/

open scoped Classical IsMulCommutative commutatorElement

namespace NK.LocalTame.IndexRedo

/-- **Characters separate points from subgroups** in an abelian group of exponent `ℓ`. -/
theorem exists_char_ne_one_of_notMem' {ℓ : ℕ} (hℓ : ℓ.Prime) {V : Type*} [CommGroup V]
    (hexp : ∀ v : V, v ^ ℓ = 1) {K : Subgroup V} {x : V} (hx : x ∉ K) :
    ∃ χ : V →* Multiplicative (ZMod ℓ), (∀ y ∈ K, χ y = 1) ∧ χ x ≠ 1 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI hKN : K.Normal := Subgroup.normal_of_isMulCommutative K
  let Q := V ⧸ K
  have hexpQ : ∀ q : Q, q ^ ℓ = 1 := by
    intro q
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective K q
    show (QuotientGroup.mk' K v) ^ ℓ = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hexp v]
    exact K.one_mem
  haveI hmod : Module (ZMod ℓ) (Additive Q) := AddCommGroup.zmodModule fun a => by
    induction a using Additive.rec with
    | ofMul q => simpa using congrArg Additive.ofMul (hexpQ q)
  have hxQ : (Additive.ofMul ((QuotientGroup.mk' K) x) : Additive Q) ≠ 0 := by
    have hiff : (Additive.ofMul ((QuotientGroup.mk' K) x) : Additive Q) = 0 ↔ x ∈ K := by
      rw [show (0 : Additive Q) = Additive.ofMul (1 : Q) from rfl, Additive.ofMul.injective.eq_iff,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact fun h => hx (hiff.mp h)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod ℓ) hxQ
  let χQ : Q →* Multiplicative (ZMod ℓ) :=
    { toFun := fun q => f (Additive.ofMul q)
      map_one' := f.map_zero
      map_mul' := fun a b => f.map_add (Additive.ofMul a) (Additive.ofMul b) }
  refine ⟨χQ.comp (QuotientGroup.mk' K), ?_, ?_⟩
  · intro y hy
    have hy1 : (QuotientGroup.mk' K) y = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hy
    show χQ ((QuotientGroup.mk' K) y) = 1
    rw [hy1, map_one]
  · intro hcontra
    have h0 : f (Additive.ofMul ((QuotientGroup.mk' K) x)) = 0 := hcontra
    rw [hf] at h0
    exact one_ne_zero h0

theorem frattini_index_ne_zero_index_eq_prime {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hopen : ∀ H : Subgroup G, H.index = ℓ → H.Normal → IsOpen (H : Set G))
    (M : Subgroup G) (hMN : M.Normal) (hMo : IsOpen (M : Set G)) (hMi : M.index = ℓ) :
    (IndexPrime.powSub ℓ M ⊔ commutator M).index ≠ 0 := by
  classical
  haveI hMN' : M.Normal := hMN
  -- the intersection of all normal subgroups of index `ℓ`
  let D : Subgroup G := ⨅ (H : {H : Subgroup G // H.index = ℓ ∧ H.Normal}), (H : Subgroup G)
  have hDinf : (D : Subgroup G) =
      ⨅ (H : {H : Subgroup G // H.index = ℓ ∧ H.Normal}), (H : Subgroup G) := rfl
  have hDopen : IsOpen (D : Set G) := by
    rw [hDinf, Subgroup.coe_iInf, ← Set.iInf_eq_iInter]
    exact lFrattini_isOpen hℓ hopen
  have hDnormal : D.Normal := by
    rw [hDinf]
    exact Subgroup.normal_iInf_normal fun H => H.2.2
  haveI hDsubM_normal : (D.subgroupOf M).Normal := hDnormal.subgroupOf M
  haveI hDsub_open : IsOpen ((D.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
    have h : (D.subgroupOf M : Set ↥M) = M.subtype ⁻¹' (D : Set G) := rfl
    rw [h]
    exact hDopen.preimage continuous_subtype_val
  have hfin1 : Finite (↥M ⧸ (D.subgroupOf M)) :=
    Subgroup.quotient_finite_of_isOpen' M (D.subgroupOf M) hMo hDsub_open
  have hidx1 : (D.subgroupOf M).index ≠ 0 :=
    (Subgroup.finiteIndex_of_finite_quotient (H := D.subgroupOf M)).index_ne_zero
  -- choose g outside M
  have hMne : M ≠ ⊤ := by
    intro h
    have h1 : M.index = 1 := by rw [h, Subgroup.index_top]
    rw [hMi] at h1
    exact absurd h1 (Nat.Prime.one_lt hℓ).ne'
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ M := by
    by_contra h
    push Not at h
    exact hMne (le_antisymm le_top fun x _ => h x)
  -- the subgroups of M
  let Φ : Subgroup ↥M := IndexPrime.powSub ℓ ↥M ⊔ commutator ↥M
  let CGM : Subgroup ↥M := (⁅Subgroup.zpowers g, M⁆).comap M.subtype
  let Cg : Subgroup ↥M := Subgroup.zpowers ⟨g ^ M.index, Subgroup.pow_index_mem M g⟩
  let L : Subgroup ↥M := Φ ⊔ CGM
  let K : Subgroup ↥M := L ⊔ Cg
  have hKcomm : commutator ↥M ≤ K :=
    fun _ hx => Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right hx))
  have hKN : K.Normal := Subgroup.Normal.of_commutator_le ↥M hKcomm
  -- the containment D ∩ M ⊆ K
  have hKD : D.subgroupOf M ≤ K := by
    intro x hx
    by_contra hxK
    have hxq : (QuotientGroup.mk' K) x ∉ (⊥ : Subgroup (↥M ⧸ K)) := by
      intro hbot
      refine hxK ?_
      have h1 : (QuotientGroup.mk' K) x = 1 := by simpa using hbot
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    haveI hcommKM : IsMulCommutative (↥M ⧸ K) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hKcomm
    have hexp : ∀ v : ↥M ⧸ K, v ^ ℓ = 1 := by
      intro v
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective K v
      show (QuotientGroup.mk' K m) ^ ℓ = 1
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left
        (IndexPrime.mem_powSub m)))
    obtain ⟨χ₀, -, hχ₀x⟩ :=
      exists_char_ne_one_of_notMem' hℓ hexp (K := ⊥) (x := (QuotientGroup.mk' K) x) hxq
    let χ : ↥M →* Multiplicative (ZMod ℓ) := χ₀.comp (QuotientGroup.mk' K)
    have hχK : ∀ y ∈ K, χ y = 1 := by
      intro y hy
      have hy1 : (QuotientGroup.mk' K) y = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hy
      show χ₀ ((QuotientGroup.mk' K) y) = 1
      rw [hy1, map_one]
    have hχx : χ x ≠ 1 := hχ₀x
    have hinv : ∀ m : ↥M, χ ⟨g * (m : G) * g⁻¹, hMN'.conj_mem (m : G) m.2 g⟩ = χ m := by
      intro m
      have hmem : ⁅g, (m : G)⁆ ∈ ⁅Subgroup.zpowers g, M⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers g) m.2
      have hmemM : ⁅g, (m : G)⁆ ∈ M :=
        M.mul_mem (hMN'.conj_mem (m : G) m.2 g) (M.inv_mem m.2)
      have hmemCGM : (⟨⁅g, (m : G)⁆, hmemM⟩ : ↥M) ∈ CGM := hmem
      have hcoe : (⟨g * (m : G) * g⁻¹, hMN'.conj_mem (m : G) m.2 g⟩ : ↥M) =
          (⟨⁅g, (m : G)⁆, hmemM⟩ : ↥M) * m := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [commutatorElement_def]
        group
      rw [hcoe, map_mul,
        hχK _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right hmemCGM)), one_mul]
    have hpow : χ ⟨g ^ M.index, Subgroup.pow_index_mem M g⟩ = 1 :=
      hχK _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    obtain ⟨ψ, hψ⟩ := exists_hom_extend_of_index_prime hℓ M hMi g hg χ hinv hpow
    have hψx : ψ (x : G) = χ x := by
      have h := congrArg (fun f : ↥M →* Multiplicative (ZMod ℓ) => f x) hψ
      simpa using h
    have hψne : ψ ≠ 1 := by
      intro h1
      exact hχx (by rw [← hψx, h1]; rfl)
    have hkeridx : ψ.ker.index = ℓ := by
      rw [Subgroup.index_ker]
      have hcard : Nat.card (Multiplicative (ZMod ℓ)) = ℓ := by
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
      haveI : Fact (Nat.Prime (Nat.card (Multiplicative (ZMod ℓ)))) := ⟨by rw [hcard]; exact hℓ⟩
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card ψ.range with hbot | htop
      · exfalso
        have h1 : ψ = 1 := by
          ext y
          have hy : ψ y ∈ ψ.range := MonoidHom.mem_range.mpr ⟨y, rfl⟩
          rw [hbot] at hy
          simpa using hy
        exact hψne h1
      · rw [htop, Subgroup.card_top, hcard]
    have hxD : (x : G) ∈ D := Subgroup.mem_subgroupOf.mp hx
    have hxker : (x : G) ∈ ψ.ker :=
      Subgroup.mem_iInf.mp (hDinf ▸ hxD) ⟨ψ.ker, ⟨hkeridx, inferInstance⟩⟩
    exact hχx (by rw [← hψx]; exact MonoidHom.mem_ker.mp hxker)
  -- index bookkeeping
  have hKdvd : K.index ∣ (D.subgroupOf M).index := Subgroup.index_dvd_of_le hKD
  have hKidx : K.index ≠ 0 := by
    have hpos : 0 < (D.subgroupOf M).index := Nat.pos_of_ne_zero hidx1
    exact (Nat.pos_of_dvd_of_pos hKdvd hpos).ne'
  have hCgmem : (⟨g ^ M.index, Subgroup.pow_index_mem M g⟩ : ↥M) ^ ℓ ∈ L :=
    Subgroup.mem_sup_left
      (Subgroup.mem_sup_left (IndexPrime.mem_powSub (⟨g ^ M.index, Subgroup.pow_index_mem M g⟩ : ↥M)))
  haveI hLnormal : L.Normal :=
    Subgroup.Normal.of_commutator_le ↥M
      (fun _ hx => Subgroup.mem_sup_left (Subgroup.mem_sup_right hx))
  have hrelL : L.relIndex K ≠ 0 := relIndex_sup_zpowers_ne_zero hℓ L _ hCgmem
  have hLidx : L.index ≠ 0 := by
    have hmul := Subgroup.relIndex_mul_index (H := L) (K := K)
      (show L ≤ K from le_sup_left)
    rw [← hmul]
    exact mul_ne_zero hrelL hKidx
  have hΦidx : Φ.index ≠ 0 :=
    frattini_index_ne_zero_of_sup_zpowers_commutator hℓ M hMi g hg hLidx
  exact hΦidx

end NK.LocalTame.IndexRedo
