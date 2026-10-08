import Mathlib
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.Sec4Extra
import Submission.Work.BG.hatInj
import Submission.Work.BG.modTwoIndep
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.Hat
import Submission.Work.BG.nOrb
import Submission.Work.BG.kappaExists
import Submission.Work.BG.invJCard
import Submission.Work.BG.thmCSmallAux
import Submission.Work.BG.hatInjCongruentEq
import Submission.Work.BG.splitglue.Split
import Submission.Work.BG.l41iii

/-!
# Area BG: `L41vProp` — BG 1981, Lemma 4.1 (v)

The lemma proved here is `Work.GW2.C23.L41vProp`: for `χ ∈ ±Irr(G)`, the set of hats
`{ν̂ : ν ∈ 𝒮'(χ)}` is `N_G(S)`-invariant.  Precisely, if `ν ∈ 𝒮'(χ) := bset' C β₂ χ`,
`HatOf D C ν θ`, `x ∈ N_G(S)` and `θ' = θ^x` (i.e. `ConjBy D x θ θ'`), then `θ'` is the hat of
some `μ ∈ 𝒮'(χ)`.

Route (BG p. 212, design pass 23 §B.0):

* `B = B₁ ⊓ B₂` is `N_G(S)`-invariant, so conjugation by `x` acts on the class functions of
  `B` (`Work.BG.conjCF`) and preserves irreducibility;
* **Lemma 4.1 (iii)** gives the congruence `χ ≡ Σ_{ν ∈ 𝒮'(χ)} ν̂ (mod 2)` on `B` for *any*
  choice of hats `ν̂`; evaluating it at the conjugate point `x⁻¹ b x` and using that `χ` is a
  class function gives the same congruence for the conjugated hats `ν̂^x`;
* the two families `ν ↦ ν̂` and `ν ↦ ν̂^x` are injective on `𝒮'(χ)` (HAT-INJ) and congruent
  modulo `2`; the multiplicity form of Lemma 1.8 turns the congruence into equality of fibres,
  so the hat `θ^x` of `ν` occurs among the hats of `𝒮'(χ)`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-! ## 0. Small generalities -/

/-- A `finsum` over a finite set is the sum over the subtype cut out by the corresponding
`Finset`. -/
theorem l41v_finsum_mem_eq_attach_sum {α β : Type*} [AddCommMonoid β] {s : Set α} (hs : s.Finite)
    (f : α → β) : (∑ᶠ x ∈ s, f x) = ∑ x : ↥hs.toFinset, f x.1 := by
  classical
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, Finset.univ_eq_attach]
  exact (Finset.sum_attach hs.toFinset f).symm

/-- Conjugation by an element normalising `B` is a surjective endomorphism of `B`. -/
theorem l41v_conjHom_surjective (D : BGData G) (x : G) (hx : ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B)
    (hx' : ∀ b ∈ D.B, x * b * x⁻¹ ∈ D.B) : Function.Surjective (conjHom D x hx) := by
  intro c
  refine ⟨⟨x * (c : G) * x⁻¹, hx' c c.2⟩, ?_⟩
  apply Subtype.ext
  simp only [conjHom_apply, Subgroup.coe_mk]
  group

/-- Conjugation preserves irreducibility on `B`. -/
theorem l41v_isIrreducibleCharacter_conjCF (D : BGData G) (x : G)
    (hx : ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B) (hx' : ∀ b ∈ D.B, x * b * x⁻¹ ∈ D.B)
    {θ : ClassFunction ↥D.B ℂ} (hθ : IsIrreducibleCharacter θ) :
    IsIrreducibleCharacter (conjCF D x hx θ) := by
  have := IsIrreducibleCharacter.compHom_of_surjective (l41v_conjHom_surjective D x hx hx') hθ
  simpa [conjCF] using this

/-- `conjCF D x` is injective. -/
theorem l41v_conjCF_injective (D : BGData G) (x : G) (hx : ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B)
    (hx' : ∀ b ∈ D.B, x * b * x⁻¹ ∈ D.B) {φ ψ : ClassFunction ↥D.B ℂ}
    (h : conjCF D x hx φ = conjCF D x hx ψ) : φ = ψ := by
  ext b
  have h1 := congrArg (fun η : ClassFunction ↥D.B ℂ => η ⟨x * (b : G) * x⁻¹, hx' b b.2⟩) h
  simp only [conjCF_apply] at h1
  convert h1 using 2 <;> apply Subtype.ext <;> group

/-- `|B|` is odd (`B ≤ U` and `|U|` is odd). -/
theorem l41v_odd_card_B (D : BGData G) : Odd (Nat.card ↥D.B) := by
  have hBU : D.B ≤ D.U := inf_le_left.trans inf_le_left
  have hcard : Nat.card ↥D.B = Nat.card ↥(D.B.subgroupOf D.U) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBU).toEquiv.symm
  rw [hcard]
  exact Odd.of_dvd_nat (odd_card_U D) (Subgroup.card_subgroup_dvd_card _)

/-! ## 0b. Two inputs proved here (independent of any delegated leaf) -/

theorem l41v_even_of_algIntModTwo_zero {m : ℤ} (h : AlgIntModTwo (m : ℂ) 0) : Even m := by
  obtain ⟨c, hc, hceq⟩ := h
  have h2 : (m : ℂ) = 2 * c := by linear_combination hceq
  have hq : c = (((m : ℚ) / 2 : ℚ) : ℂ) := by
    rw [show c = (m : ℂ) / 2 by rw [h2]; ring]
    push_cast
    ring
  have hqint : IsIntegral ℤ ((m : ℚ) / 2) := IsIntegral.ratCast_iff.mp (hq ▸ hc)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hqint
  refine ⟨y, ?_⟩
  have hy' : (((y : ℤ)) : ℚ) = (m : ℚ) / 2 := hy
  have h4 : m = 2 * y := by
    have h5 : (m : ℚ) = ((2 * y : ℤ) : ℚ) := by
      push_cast
      rw [hy']
      ring
    exact_mod_cast h5
  omega

/-- The multiplicity form of Lemma 1.8 (my own copy, used by `l41v`). -/

theorem l41v_modTwoIndepMult {K : Type} [Group K] [Fintype K] [Invertible (Nat.card K : ℂ)]
    (hodd : Odd (Nat.card K)) {ι : Type} [Fintype ι] (f g : ι → ClassFunction K ℂ)
    (hf : ∀ i, IsIrreducibleCharacter (f i)) (hg : ∀ i, IsIrreducibleCharacter (g i))
    (hfinj : Function.Injective f) (hginj : Function.Injective g)
    (hmod : ∀ k : K, AlgIntModTwo (∑ i, f i k) (∑ i, g i k)) :
    ∀ i₀ : ι, ∃ i : ι, f i = g i₀ := by
  classical
  let A : Finset (ClassFunction K ℂ) := Finset.univ.image f ∪ Finset.univ.image g
  let cF : ClassFunction K ℂ → ℕ := fun γ => (Finset.univ.filter fun i => f i = γ).card
  let cG : ClassFunction K ℂ → ℕ := fun γ => (Finset.univ.filter fun i => g i = γ).card
  have hF : ∀ k : K, (∑ γ ∈ A, (cF γ : ℂ) * γ k) = ∑ i, f i k := by
    intro k
    rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset ι)) (t := A) (g := f)
      (f := fun i => (f i) k)
      (fun i _ => Finset.mem_union_left _ (Finset.mem_image_of_mem f (Finset.mem_univ i)))]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]),
      Finset.sum_const, nsmul_eq_mul]
  have hG : ∀ k : K, (∑ γ ∈ A, (cG γ : ℂ) * γ k) = ∑ i, g i k := by
    intro k
    rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset ι)) (t := A) (g := g)
      (f := fun i => (g i) k)
      (fun i _ => Finset.mem_union_right _ (Finset.mem_image_of_mem g (Finset.mem_univ i)))]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]),
      Finset.sum_const, nsmul_eq_mul]
  have hmodA : ∀ k : K, AlgIntModTwo (∑ γ ∈ A, ((cF γ : ℂ) - (cG γ : ℂ)) * γ k) 0 := by
    intro k
    have h1 : (∑ γ ∈ A, ((cF γ : ℂ) - (cG γ : ℂ)) * γ k)
        = (∑ γ ∈ A, (cF γ : ℂ) * γ k) - (∑ γ ∈ A, (cG γ : ℂ) * γ k) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun γ _ => sub_mul _ _ _
    rw [h1, hF k, hG k]
    simpa only [AlgIntModTwo, sub_zero] using hmod k
  have hirr : ∀ γ : ↥A, IsIrreducibleCharacter (γ.1 : ClassFunction K ℂ) := by
    intro γ
    rcases Finset.mem_union.mp γ.2 with h | h
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
      rw [← hi]
      exact hf i
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
      rw [← hi]
      exact hg i
  have hinj : Function.Injective (fun γ : ↥A => (γ.1 : ClassFunction K ℂ)) :=
    fun a b h => Subtype.ext h
  have hsumA : ∀ k : K,
      (∑ γ : ↥A, ((cF γ.1 : ℂ) - (cG γ.1 : ℂ)) * γ.1 k)
        = ∑ γ ∈ A, ((cF γ : ℂ) - (cG γ : ℂ)) * γ k := by
    intro k
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach A (fun γ => ((cF γ : ℂ) - (cG γ : ℂ)) * γ k)
  have hzero : ∀ γ : ↥A, AlgIntModTwo ((cF γ.1 : ℂ) - (cG γ.1 : ℂ)) 0 :=
    modTwoIndepAux hodd (fun γ : ↥A => (γ.1 : ClassFunction K ℂ)) hirr hinj
      (fun γ : ↥A => (cF γ.1 : ℂ) - (cG γ.1 : ℂ))
      (fun γ => (isIntegral_natCast (cF γ.1)).sub (isIntegral_natCast (cG γ.1)))
      (fun k => by rw [hsumA k]; exact hmodA k)
  have hle1 : ∀ γ, cF γ ≤ 1 := fun γ => Finset.card_le_one.mpr fun a ha b hb =>
    hfinj ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  have hle2 : ∀ γ, cG γ ≤ 1 := fun γ => Finset.card_le_one.mpr fun a ha b hb =>
    hginj ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  have hfib : ∀ γ ∈ A, cF γ = cG γ := by
    intro γ hγ
    have hev : Even ((cF γ : ℤ) - (cG γ : ℤ)) :=
      l41v_even_of_algIntModTwo_zero (by simpa using hzero ⟨γ, hγ⟩)
    have hb1 : (cF γ : ℤ) ≤ 1 := by exact_mod_cast hle1 γ
    have hb2 : (cG γ : ℤ) ≤ 1 := by exact_mod_cast hle2 γ
    have hb3 : (0 : ℤ) ≤ (cF γ : ℤ) := Int.natCast_nonneg _
    have hb4 : (0 : ℤ) ≤ (cG γ : ℤ) := Int.natCast_nonneg _
    obtain ⟨y, hy⟩ := hev
    have h5 : (cF γ : ℤ) = (cG γ : ℤ) := by omega
    omega
  intro i₀
  have hmemA : g i₀ ∈ A := Finset.mem_union_right _ (Finset.mem_image_of_mem g (Finset.mem_univ i₀))
  have hpos : 0 < cF (g i₀) := by
    rw [hfib (g i₀) hmemA]
    exact Finset.card_pos.mpr ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, rfl⟩⟩
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  exact ⟨i, (Finset.mem_filter.mp hi).2⟩

theorem l41v_BInv_aux {G : Type} [Group G] [Finite G] [Fintype G] (D : BGData G) (hn : D.n = 2) :
    ∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G), ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B := by
  have hcomm : ∀ x ∈ (D.S : Subgroup G), x * D.t = D.t * x := by
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (S_le_H D hx) D.t (by simp)).symm
  have hUS : D.U ⊔ (D.S : Subgroup G) = D.H :=
    SplitGlue.centralizerSplitProp G D.S D.n D.two_le D.dih D.t (D.S0_le D.t_mem) D.t_order hcomm
  have hUleH : D.U ≤ D.H := by rw [← hUS]; exact le_sup_left
  have hSleH : (D.S : Subgroup G) ≤ D.H := by rw [← hUS]; exact le_sup_right
  have hUn : (D.U.subgroupOf D.H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUleH).mpr (H_le_normalizer_U D)
  -- the Sylow has order `4`
  have hcardS : Nat.card ↥(D.S : Subgroup G) = 4 := by
    obtain ⟨e⟩ := D.dih
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hn]
  set U' : Subgroup ↥D.H := D.U.subgroupOf D.H with hU'def
  set S' : Subgroup ↥D.H := (D.S : Subgroup G).subgroupOf D.H with hS'def
  haveI : U'.Normal := hUn
  have hsup : U' ⊔ S' = ⊤ := by
    have h1 : U' ⊔ S' = (D.U ⊔ (D.S : Subgroup G)).subgroupOf D.H := by
      rw [hU'def, hS'def]
      exact (Subgroup.subgroupOf_sup hUleH hSleH).symm
    rw [h1, hUS, Subgroup.subgroupOf_self]
  have hdisj : Disjoint U' S' := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    have hx1 : (x : ↥D.H).1 ∈ D.U ⊓ (D.S : Subgroup G) := ⟨hx.1, hx.2⟩
    rw [U_inf_S D] at hx1
    exact Subgroup.mem_bot.mpr (Subtype.ext (by simpa using hx1))
  have hmul : (↑U' : Set ↥D.H) * (↑S' : Set ↥D.H) = Set.univ := by
    have hN : S' ≤ Subgroup.normalizer (↑U' : Set ↥D.H) := by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left U' S' hN, hsup]
    rfl
  have hcompl : U'.IsComplement' S' :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
  have hcardS' : Nat.card ↥S' = 4 := by
    rw [hS'def]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSleH).toEquiv, hcardS]
  have hcardU' : Nat.card ↥U' = Nat.card ↥D.U := by
    rw [hU'def]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUleH).toEquiv
  -- the quotient `H/U` has order `4` (the image of `S'` is everything)
  have hquot : Nat.card (↥D.H ⧸ U') = 4 := by
    have hbij : Function.Bijective (fun s : ↥S' => QuotientGroup.mk' U' (s : ↥D.H)) := by
      constructor
      · intro s t hst
        have h1 : (s : ↥D.H)⁻¹ * (t : ↥D.H) ∈ U' := by
          rw [← QuotientGroup.ker_mk' U', MonoidHom.mem_ker, map_mul, map_inv]
          have hst' : QuotientGroup.mk' U' (s : ↥D.H) = QuotientGroup.mk' U' (t : ↥D.H) := hst
          rw [hst', inv_mul_cancel]
        have h2 : (s : ↥D.H)⁻¹ * (t : ↥D.H) ∈ S' := S'.mul_mem (S'.inv_mem s.2) t.2
        have h3 : (s : ↥D.H)⁻¹ * (t : ↥D.H) ∈ U' ⊓ S' := ⟨h1, h2⟩
        rw [disjoint_iff.mp hdisj] at h3
        have h4 : (s : ↥D.H)⁻¹ * (t : ↥D.H) = 1 := by simpa using h3
        exact Subtype.ext (inv_mul_eq_one.mp h4)
      · intro γ
        obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective U' γ
        obtain ⟨u, hu, s, hs, hus⟩ := Set.mem_mul.mp (show (h : ↥D.H) ∈ (↑U' : Set ↥D.H) * ↑S' by
          rw [hmul]; exact Set.mem_univ _)
        have hu1 : QuotientGroup.mk' U' u = 1 := by
          rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk' U']
          exact hu
        exact ⟨⟨s, hs⟩, by rw [← hus, map_mul, hu1, one_mul]⟩
    have hcard := Nat.card_congr (Equiv.ofBijective _ hbij)
    rw [← hcard, hcardS']
  -- odd-order elements of `H` lie in `U`
  have hkey : ∀ v ∈ D.H, Odd (orderOf v) → v ∈ D.U := by
    intro v hv hoddv
    set γ : ↥D.H ⧸ U' := QuotientGroup.mk' U' ⟨v, hv⟩ with hγdef
    have hdvd1 : orderOf γ ∣ orderOf v := by
      have := orderOf_map_dvd (QuotientGroup.mk' U') (⟨v, hv⟩ : ↥D.H)
      rwa [Subgroup.orderOf_mk] at this
    have hdvd2 : orderOf γ ∣ 4 := by
      have := orderOf_dvd_natCard (G := ↥D.H ⧸ U') γ
      rwa [hquot] at this
    have hoddγ : Odd (orderOf γ) := Odd.of_dvd_nat hoddv hdvd1
    have hone : orderOf γ = 1 := by
      have h1 : orderOf γ ∣ 2 :=
        (Nat.coprime_two_right.mpr hoddγ).dvd_of_dvd_mul_right (by simpa using hdvd2)
      exact Nat.dvd_one.mp ((Nat.coprime_two_right.mpr hoddγ).dvd_of_dvd_mul_right
        (by simpa using h1))
    have hmem : (⟨v, hv⟩ : ↥D.H) ∈ U' := by
      rw [← QuotientGroup.ker_mk' U', MonoidHom.mem_ker]
      exact orderOf_eq_one_iff.mp hone
    have hmem2 : ((⟨v, hv⟩ : ↥D.H) : G) ∈ D.U := by
      rw [hU'def] at hmem
      rwa [Subgroup.mem_subgroupOf] at hmem
    simpa using hmem2
  -- conclude
  have hmain : ∀ y ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G), ∀ b ∈ D.B,
      y * b * y⁻¹ ∈ D.B := by
    intro y hy b hb
    have hy' : y⁻¹ ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G) := inv_mem hy
    have hcC : y * b * y⁻¹ ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hvv
      have hv' : y⁻¹ * v * y ∈ (D.S : Subgroup G) := by
        simpa using (Subgroup.mem_normalizer_iff.mp hy' v).mp hvv
      have hbC := Subgroup.mem_centralizer_iff.mp (B_le_centralizer_S D hb) (y⁻¹ * v * y) hv'
      calc v * (y * b * y⁻¹) = y * ((y⁻¹ * v * y) * b) * y⁻¹ := by group
        _ = y * (b * (y⁻¹ * v * y)) * y⁻¹ := by rw [hbC]
        _ = (y * b * y⁻¹) * v := by group
    have hcH : y * b * y⁻¹ ∈ D.H :=
      Subgroup.centralizer_le (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact D.S0_le D.t_mem) hcC
    have hord : orderOf (y * b * y⁻¹) = orderOf b := by
      have hsemi : SemiconjBy y b (y * b * y⁻¹) := by simp [SemiconjBy, mul_assoc]
      exact (SemiconjBy.orderOf_eq y hsemi).symm
    have hbU : b ∈ D.U := hb.1.1
    have hoddB : Odd (orderOf b) := by
      have h1 : orderOf b ∣ Nat.card ↥D.U :=
        Subgroup.orderOf_dvd_natCard D.U hbU
      exact Odd.of_dvd_nat (odd_card_U D) h1
    have hcU : y * b * y⁻¹ ∈ D.U := hkey _ hcH (hord ▸ hoddB)
    -- and it lies in `B`
    have hcS : y * b * y⁻¹ ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G) := hcC
    have hc1 : y * b * y⁻¹ ∈ Subgroup.centralizer ({D.t1} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr D.t1_mem) hcS
    have hc2 : y * b * y⁻¹ ∈ Subgroup.centralizer ({D.t2} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr D.t2_mem) hcS
    exact ⟨⟨hcU, hc1⟩, hcU, hc2⟩
  intro x hx b hb
  simpa using hmain x⁻¹ (inv_mem hx) b hb

/-! ## 1. The core argument, from the three leaf statements -/

/-- **`L41vProp` from its three inputs.**  The arguments are Lemma 4.1 (iii)
(`Work.GW2.C23.L41iiiProp'`), the multiplicity form of Lemma 1.8 (`l41v_modTwoIndepMult`
below) and the `N_G(S)`-invariance of `B` (`l41v_BInv_aux` below). -/
theorem l41v_core {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hiii : L41iiiProp' D C)
    (hmult : ∀ {K : Type} [Group K] [Fintype K] [Invertible (Nat.card K : ℂ)],
      Odd (Nat.card K) → ∀ {ι : Type} [Fintype ι] (f g : ι → ClassFunction K ℂ),
      (∀ i, IsIrreducibleCharacter (f i)) → (∀ i, IsIrreducibleCharacter (g i)) →
      Function.Injective f → Function.Injective g →
      (∀ k : K, AlgIntModTwo (∑ i, f i k) (∑ i, g i k)) →
      ∀ i₀ : ι, ∃ i : ι, f i = g i₀)
    (hn : D.n = 2)
    (hBinv : ∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
      ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B) :
    Compat D C → ∀ β₂ : quotGroup C.P →* ℂˣ, β₂ ≠ 1 → ∀ χ : ClassFunction G ℂ,
      IsPmIrr χ → ∀ ν ∈ bset' C β₂ χ, ∀ θ, HatOf D C ν θ →
      ∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G), ∀ θ', ConjBy D x θ θ' →
        ∃ μ ∈ bset' C β₂ χ, HatOf D C μ θ' := by
  intro hc β₂ hβ χ hχ ν hν θ hθ x hx θ' hθ'
  classical
  -- (0) the index set `𝒮'(χ)`, its finiteness and non-emptiness
  have hTne : (bset' C β₂ χ).Nonempty := ⟨ν, hν⟩
  have hTfin : (bset' C β₂ χ).Finite := (hiii hc hn β₂ hβ χ hχ hTne).1
  have hcong := (hiii hc hn β₂ hβ χ hχ hTne).2
  -- (1) hats: existence and uniqueness (`HatProp`, proved in `BG/Hat.lean`)
  have hHat : HatProp D C := Hat D C
  have hhatEx : ∀ μ ∈ bset' C β₂ χ, ∃ θm, HatOf D C μ θm :=
    fun μ hμ => (hHat hc hn μ hμ.1).1
  -- a concrete family of hats, indexed by `(bset' C β₂ χ).toFinset`
  let θF : ↥hTfin.toFinset → ClassFunction ↥D.B ℂ :=
    fun μ => Classical.choose (hhatEx μ.1 (hTfin.mem_toFinset.mp μ.2))
  have hθF : ∀ μ : ↥hTfin.toFinset, HatOf D C μ.1 (θF μ) :=
    fun μ => Classical.choose_spec (hhatEx μ.1 (hTfin.mem_toFinset.mp μ.2))
  -- the same family, extended by `0` outside `𝒮'(χ)`, to feed Lemma 4.1 (iii)
  let fam : ClassFunction ↥C.P.H0 ℂ → ClassFunction ↥D.B ℂ := fun μ =>
    if h : μ ∈ bset' C β₂ χ then θF ⟨μ, hTfin.mem_toFinset.mpr h⟩ else 0
  have hfam : ∀ μ ∈ bset' C β₂ χ, HatOf D C μ (fam μ) := by
    intro μ hμ
    rw [show fam μ = θF ⟨μ, hTfin.mem_toFinset.mpr hμ⟩ from dite_eq_left hμ]
    exact hθF ⟨μ, hTfin.mem_toFinset.mpr hμ⟩
  -- (2) Lemma 4.1 (iii): `χ ≡ Σ_{ν ∈ 𝒮'(χ)} ν̂ (mod 2)` on `B`, in subtype form
  have hcong1 : ∀ b : ↥D.B,
      AlgIntModTwo (χ (b : G)) (∑ μ : ↥hTfin.toFinset, θF μ b) := by
    intro b
    have h := hcong fam hfam b
    rw [l41v_finsum_mem_eq_attach_sum hTfin (fun μ => fam μ b)] at h
    have h2 : (∑ μ : ↥hTfin.toFinset, fam μ.1 b) = ∑ μ : ↥hTfin.toFinset, θF μ b := by
      refine Finset.sum_congr rfl fun μ _ => ?_
      have hfm : fam μ.1
          = θF ⟨μ.1, hTfin.mem_toFinset.mpr (hTfin.mem_toFinset.mp μ.2)⟩ :=
        dite_eq_left (hTfin.mem_toFinset.mp μ.2)
      rw [hfm]
    rwa [h2] at h
  -- (3) `x` normalises `B`, in both directions
  have hxB : ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B := hBinv x hx
  have hx' : x⁻¹ ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G) := inv_mem hx
  have hxB' : ∀ b ∈ D.B, x * b * x⁻¹ ∈ D.B := by
    intro b hb
    have h := hBinv x⁻¹ hx' b hb
    simpa using h
  -- (4) the conjugated congruence: evaluate (iii) at `x⁻¹ b x`, use `χ (x⁻¹ b x) = χ b`
  have hcong2 : ∀ b : ↥D.B,
      AlgIntModTwo (∑ μ : ↥hTfin.toFinset, θF μ b)
        (∑ μ : ↥hTfin.toFinset, conjCF D x hxB (θF μ) b) := by
    intro b
    have h := hcong1 ⟨x⁻¹ * (b : G) * x, hxB b b.2⟩
    have hχb : χ (x⁻¹ * (b : G) * x) = χ (b : G) := by
      simpa using ClassFunction.conj_eq χ (b : G) x⁻¹
    have hsum : (∑ μ : ↥hTfin.toFinset, θF μ ⟨x⁻¹ * (b : G) * x, hxB b b.2⟩)
        = ∑ μ : ↥hTfin.toFinset, conjCF D x hxB (θF μ) b := by
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [conjCF_apply]
    rw [hχb, hsum] at h
    exact (hcong1 b).symm.trans h
  -- (5) the multiplicity form of Lemma 1.8
  have hf_inj : Function.Injective θF := by
    intro a b hab
    have hSa : a.1 ∈ S4Index C := (hTfin.mem_toFinset.mp a.2).1
    have hSb : b.1 ∈ S4Index C := (hTfin.mem_toFinset.mp b.2).1
    have h1 : a.1 = b.1 :=
      hatInj D C hc hn a.1 hSa b.1 hSb (θF a) (hθF a) (hab ▸ hθF b)
    exact Subtype.ext h1
  have hg_inj : Function.Injective (fun μ : ↥hTfin.toFinset => conjCF D x hxB (θF μ)) := by
    intro a b hab
    exact hf_inj (l41v_conjCF_injective D x hxB hxB' hab)
  have hmod : ∀ k : ↥D.B,
      AlgIntModTwo (∑ μ : ↥hTfin.toFinset, θF μ k)
        (∑ μ : ↥hTfin.toFinset, conjCF D x hxB (θF μ) k) := hcong2
  have hmult' := hmult (l41v_odd_card_B D) θF (fun μ => conjCF D x hxB (θF μ))
    (fun μ => (hθF μ).1)
    (fun μ => l41v_isIrreducibleCharacter_conjCF D x hxB hxB' (hθF μ).1)
    hf_inj hg_inj hmod
  -- (6) the hat of `ν` is the chosen one, and `θ' = θ^x`
  let ν₀ : ↥hTfin.toFinset := ⟨ν, hTfin.mem_toFinset.mpr hν⟩
  have hθν : fam ν = θF ν₀ := dite_eq_left hν
  have hθν' : θ = θF ν₀ := by
    have hS : ν ∈ S4Index C := hν.1
    exact (hHat hc hn ν hS).2 θ (θF ν₀) hθ (hθν ▸ hθF ν₀)
  have hθ'eq : θ' = conjCF D x hxB θ := eq_conjCF_of_conjBy D x hxB θ hθ'
  obtain ⟨μ₀, hμ₀⟩ := hmult' ν₀
  refine ⟨μ₀.1, hTfin.mem_toFinset.mp μ₀.2, ?_⟩
  have hgoal : θF μ₀ = θ' := by
    rw [hμ₀, ← hθν', hθ'eq]
  rw [← hgoal]
  exact hθF μ₀

end Work.BG

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 in
theorem l41v {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C23.L41vProp D C := by
  intro hc hn
  exact l41v_core D C (l41iii D C) l41v_modTwoIndepMult hn (l41v_BInv_aux D hn) hc

end Work.BG
