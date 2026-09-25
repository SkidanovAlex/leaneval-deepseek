import Mathlib
import Submission.Work.GolodShafarevich.Defs
import Submission.Work.GolodShafarevich.Setup

namespace Work.GolodShafarevich.RelatorAug

open scoped MonoidAlgebra
open Work.GolodShafarevich

/-! ## Auxiliary group-theoretic facts -/

section Frattini

/-- `K` is contained in the Frattini subgroup iff every maximal (coatom) subgroup contains it. -/
lemma le_frattini_iff {G : Type*} [Group G] {K : Subgroup G} :
    K ≤ frattini G ↔ ∀ M : Subgroup G, IsCoatom M → K ≤ M := by
  rw [frattini, Order.radical, le_iInf_iff]
  simp only [Set.mem_ofPred_eq, le_iInf_iff]

/-- Every maximal (coatom) subgroup of a finite `p`-group is normal. -/
lemma coatom_normal {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Fintype G]
    (hG : IsPGroup p G) {M : Subgroup G} (hM : IsCoatom M) : M.Normal := by
  haveI : Group.IsNilpotent G := hG.isNilpotent
  exact Subgroup.NormalizerCondition.normal_of_coatom M
    Group.normalizerCondition_of_isNilpotent hM

/-- The quotient of a group by a coatom (assumed normal) has only `⊥` and `⊤` as subgroups. -/
lemma subgroups_quotient_coatom {G : Type*} [Group G] {M : Subgroup G} [M.Normal]
    (hM : IsCoatom M) (H' : Subgroup (G ⧸ M)) : H' = ⊥ ∨ H' = ⊤ := by
  have hsurj : Function.Surjective (QuotientGroup.mk' M) := QuotientGroup.mk'_surjective M
  have hMle : M ≤ H'.comap (QuotientGroup.mk' M) := QuotientGroup.le_comap_mk' M H'
  have hkey : H' = (H'.comap (QuotientGroup.mk' M)).map (QuotientGroup.mk' M) :=
    (Subgroup.map_comap_eq_self_of_surjective hsurj H').symm
  rcases eq_or_lt_of_le hMle with hEq | hlt
  · left
    rw [hkey, ← hEq]
    exact (Subgroup.map_eq_bot_iff M).mpr (by rw [QuotientGroup.ker_mk'])
  · right
    rw [hkey, hM.2 _ hlt, Subgroup.map_top, MonoidHom.range_eq_top.mpr hsurj]

/-- For a finite `p`-group `G`, the derived subgroup is contained in the Frattini subgroup. -/
lemma commutator_le_frattini {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Fintype G]
    (hG : IsPGroup p G) : _root_.commutator G ≤ frattini G := by
  rw [le_frattini_iff]
  intro M hM
  have hMn : M.Normal := coatom_normal hG hM
  haveI := hMn
  rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
  have hsub := subgroups_quotient_coatom hM
  have hnt : Nontrivial (G ⧸ M) := by
    obtain ⟨g, hg⟩ : ∃ g, g ∉ M := by
      by_contra h; push_neg at h
      exact hM.1 ((Subgroup.eq_top_iff' M).mpr h)
    exact ⟨⟨QuotientGroup.mk' M g, 1, by
      intro h; exact hg ((QuotientGroup.eq_one_iff g).mp h)⟩⟩
  haveI : Finite (G ⧸ M) := Quotient.finite _
  have hcen : Subgroup.center (G ⧸ M) = ⊤ := by
    rcases hsub (Subgroup.center (G ⧸ M)) with h | h
    · exfalso
      haveI : Nontrivial (Subgroup.center (G ⧸ M)) :=
        IsPGroup.center_nontrivial (hG.to_quotient M)
      exact absurd h (Subgroup.nontrivial_iff_ne_bot _ |>.mp inferInstance)
    · exact h
  refine ⟨⟨fun a b => ?_⟩⟩
  have ha : a ∈ Subgroup.center (G ⧸ M) := by rw [hcen]; trivial
  exact (Subgroup.mem_center_iff.mp ha b).symm

end Frattini

/-! ## Exponent sums and the abelian quotient -/

/-- In a commutative group, a homomorphism out of a free group is determined on `w` by the
exponent sums of `w`. -/
lemma freegroup_map_eq_prod_expSum {d : ℕ} {V : Type*} [CommGroup V]
    (f : FreeGroup (Fin d) →* V) (w : FreeGroup (Fin d)) :
    f w = ∏ i : Fin d, f (FreeGroup.of i) ^ (expSum i w) := by
  induction w using FreeGroup.induction_on with
  | one =>
    rw [map_one, Finset.prod_eq_one]
    intro i _
    rw [expSum_one, zpow_zero]
  | of j =>
    rw [Finset.prod_eq_single j]
    · rw [expSum_of, if_pos rfl, zpow_one]
    · intro i _ hij
      rw [expSum_of, if_neg hij, zpow_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  | inv_of j ih =>
    rw [map_inv, ih, ← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [expSum_inv, zpow_neg]
  | mul x y ihx ihy =>
    rw [map_mul, ihx, ihy, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [expSum_mul, zpow_add]

/-- If `e` is coprime to `(p : ℤ)^k` and `v ^ e ∈ K`, while `orderOf v = p ^ k`, then `v ∈ K`. -/
lemma mem_of_zpow_mem {V : Type*} [Group V] {v : V} {K : Subgroup V} {p k : ℕ} {e : ℤ}
    (hord : orderOf v = p ^ k) (hcop : IsCoprime e ((p : ℤ) ^ k))
    (hve : v ^ e ∈ K) : v ∈ K := by
  obtain ⟨a, b, hab⟩ := hcop
  have hone : v ^ ((p : ℤ) ^ k) = 1 := by
    rw [← Nat.cast_pow, ← hord, zpow_natCast, pow_orderOf_eq_one]
  have hv : v = (v ^ e) ^ a := by
    calc v = v ^ (1 : ℤ) := (zpow_one v).symm
      _ = v ^ (a * e + b * ((p : ℤ) ^ k)) := by rw [hab]
      _ = v ^ (a * e) * v ^ (b * ((p : ℤ) ^ k)) := by rw [zpow_add]
      _ = (v ^ e) ^ a * (v ^ ((p : ℤ) ^ k)) ^ b := by rw [zpow_mul', zpow_mul']
      _ = (v ^ e) ^ a * (1 : V) ^ b := by rw [hone]
      _ = (v ^ e) ^ a := by rw [one_zpow, mul_one]
  rw [hv]
  exact Subgroup.zpow_mem K hve a

/-- If a prime `p` does not divide `e`, then `e` is coprime to `(p : ℤ) ^ k`. -/
lemma coprime_pow_of_not_dvd {p : ℕ} (hp : Nat.Prime p) (k : ℕ) {e : ℤ}
    (he : ¬ (p : ℤ) ∣ e) : IsCoprime e ((p : ℤ) ^ k) := by
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h1 : IsCoprime (p : ℤ) e := (Prime.coprime_iff_not_dvd hprime).mpr he
  exact (h1.symm).pow_right

/-- **Burnside basis step**: if the images in `G ⧸ frattini G` of `{φ(gᵢ) : i ∈ S}` generate
`G ⧸ frattini G`, then `{φ(gᵢ) : i ∈ S}` generates `G`; by minimality of `d`, `|S| ≥ d`. -/
lemma lifting {p d : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Fintype G]
    (hG : IsPGroup p G) (φ : FreeGroup (Fin d) →* G) (hφ : Function.Surjective φ)
    (hmin : ∀ (d' : ℕ) (ψ : FreeGroup (Fin d') →* G), Function.Surjective ψ → d ≤ d')
    (S : Finset (Fin d))
    (hS : Subgroup.closure ((fun i => QuotientGroup.mk' (frattini G) (φ (FreeGroup.of i)))
        '' (↑S : Set (Fin d))) = ⊤) :
    d ≤ S.card := by
  set K : Subgroup G := Subgroup.closure ((fun i => φ (FreeGroup.of i)) '' (↑S : Set (Fin d)))
    with hK
  have hqK : Subgroup.map (QuotientGroup.mk' (frattini G)) K = ⊤ := by
    rw [hK, MonoidHom.map_closure]
    have himg : (QuotientGroup.mk' (frattini G)) ''
        ((fun i => φ (FreeGroup.of i)) '' (↑S : Set (Fin d)))
        = (fun i => QuotientGroup.mk' (frattini G) (φ (FreeGroup.of i)))
            '' (↑S : Set (Fin d)) := by
      rw [Set.image_image]
    rw [himg]; exact hS
  have hsup : K ⊔ frattini G = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hmem : QuotientGroup.mk' (frattini G) g ∈
        Subgroup.map (QuotientGroup.mk' (frattini G)) K := by rw [hqK]; trivial
    obtain ⟨k, hk, hkg⟩ := hmem
    have hker : k⁻¹ * g ∈ frattini G := by
      rw [← QuotientGroup.ker_mk' (frattini G), MonoidHom.mem_ker]
      rw [map_mul, map_inv, hkg, inv_mul_cancel]
    have hgl : g = k * (k⁻¹ * g) := by group
    rw [hgl]
    exact Subgroup.mul_mem_sup hk hker
  have hKtop : K = ⊤ := frattini_nongenerating hsup
  have hgen : Subgroup.closure ((fun i => φ (FreeGroup.of i)) '' (↑S : Set (Fin d))) = ⊤ := by
    rw [← hK]; exact hKtop
  let e : Fin (Fintype.card ↥S) ≃ ↥S := (Fintype.equivFin ↥S).symm
  let g : Fin (Fintype.card ↥S) → G := fun t => φ (FreeGroup.of ((e t : ↥S) : Fin d))
  have hrange : Set.range g = (fun i => φ (FreeGroup.of i)) '' (↑S : Set (Fin d)) := by
    ext x; constructor
    · rintro ⟨t, rfl⟩
      exact ⟨(e t : ↥S), (e t).2, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨e.symm ⟨s, hs⟩, by simp [g]⟩
  have hcl : Subgroup.closure (Set.range g) = ⊤ := by rw [hrange]; exact hgen
  have hψsurj : Function.Surjective (FreeGroup.lift g) := by
    rw [FreeGroup.lift_surjective_iff_closure_range_eq_top]; exact hcl
  have := hmin (Fintype.card ↥S) (FreeGroup.lift g) hψsurj
  rwa [Fintype.card_coe] at this

/-! ## The main lemma -/

/-- If `w` lies in the kernel of a surjection `φ : F_d → G` with `G` a finite `p`-group and `d`
minimal, then all exponent sums of `w` are divisible by `p`. -/
theorem p_dvd_expSum_of_mem_ker {p d : ℕ} (hp : Nat.Prime p) {G : Type*} [Group G] [Fintype G]
    [Nontrivial G] (hG : IsPGroup p G) (φ : FreeGroup (Fin d) →* G)
    (hφ : Function.Surjective φ)
    (hmin : ∀ (d' : ℕ) (ψ : FreeGroup (Fin d') →* G), Function.Surjective ψ → d ≤ d')
    {w : FreeGroup (Fin d)} (hw : φ w = 1) (i : Fin d) :
    (p : ℤ) ∣ expSum i w := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcomm : _root_.commutator G ≤ frattini G := commutator_le_frattini hG
  have hVcomm : IsMulCommutative (G ⧸ frattini G) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
  letI : CommGroup (G ⧸ frattini G) :=
    { (inferInstance : Group (G ⧸ frattini G)) with
      mul_comm := fun a b => hVcomm.is_comm.comm a b }
  let q : G →* G ⧸ frattini G := QuotientGroup.mk' (frattini G)
  let v : Fin d → G ⧸ frattini G := fun i => q (φ (FreeGroup.of i))
  have hrel : ∏ i, v i ^ (expSum i w) = 1 := by
    have h := freegroup_map_eq_prod_expSum (f := q.comp φ) w
    rw [show (q.comp φ) w = 1 by rw [MonoidHom.comp_apply, hw, map_one]] at h
    rw [h]
    apply Finset.prod_congr rfl
    intro i _
    rw [MonoidHom.comp_apply]
  have hgen : Subgroup.closure (Set.range v) = ⊤ := by
    have hrange : Set.range v =
        (q.comp φ) '' Set.range (FreeGroup.of : Fin d → FreeGroup (Fin d)) := by
      have h : Set.range v =
          Set.range ((q.comp φ) ∘ (FreeGroup.of : Fin d → FreeGroup (Fin d))) := rfl
      rw [h, Set.range_comp]
    rw [hrange, ← MonoidHom.map_closure, FreeGroup.closure_range_of, Subgroup.map_top,
      MonoidHom.range_eq_top]
    exact (QuotientGroup.mk'_surjective (frattini G)).comp hφ
  by_contra hdiv
  set S : Finset (Fin d) := Finset.univ.erase i with hS_def
  have hdrop : v i ^ (expSum i w) ∈ Subgroup.closure (v '' (↑S : Set (Fin d))) := by
    have hsplit : v i ^ (expSum i w) * ∏ j ∈ S, v j ^ (expSum j w) = 1 := by
      rw [hS_def, ← hrel]
      exact Finset.mul_prod_erase Finset.univ (fun j => v j ^ (expSum j w))
        (Finset.mem_univ i)
    have hfeq : v i ^ (expSum i w) = (∏ j ∈ S, v j ^ (expSum j w))⁻¹ :=
      eq_inv_of_mul_eq_one_left hsplit
    rw [hfeq]
    exact Subgroup.inv_mem _ (Subgroup.prod_mem _
      (fun j hj => Subgroup.zpow_mem _
        (Subgroup.subset_closure (Set.mem_image_of_mem v hj)) _))
  have hord : orderOf (v i) = p ^ (Classical.choose
      (IsPGroup.iff_orderOf.mp (hG.to_quotient (frattini G)) (v i))) :=
    Classical.choose_spec (IsPGroup.iff_orderOf.mp (hG.to_quotient (frattini G)) (v i))
  have hvmem : v i ∈ Subgroup.closure (v '' (↑S : Set (Fin d))) :=
    mem_of_zpow_mem hord (coprime_pow_of_not_dvd hp _ hdiv) hdrop
  have hvS : Subgroup.closure (v '' (↑S : Set (Fin d))) = ⊤ := by
    refine top_unique ?_
    rw [← hgen, Subgroup.closure_le]
    intro x hx
    obtain ⟨j, rfl⟩ := hx
    by_cases hj : j = i
    · rw [hj]; exact hvmem
    · exact Subgroup.subset_closure (Set.mem_image_of_mem v (by
        rw [Finset.mem_coe, Finset.mem_erase]; exact ⟨hj, Finset.mem_univ j⟩))
  have hle : d ≤ S.card := lifting hG φ hφ hmin S hvS
  have hlt : S.card < d := by
    have hpos : 0 < d := by have := i.isLt; omega
    rw [hS_def, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  omega

/-! ## The requested lemma -/

theorem Vfun_relator_mem_augIdeal {p d r : ℕ} (hp : Nat.Prime p) {G : Type*} [Group G]
    [Fintype G] [Nontrivial G] (hG : IsPGroup p G) (φ : FreeGroup (Fin d) →* G)
    (hφ : Function.Surjective φ) (R : Fin r → FreeGroup (Fin d))
    (hR : φ.ker = Subgroup.normalClosure (Set.range R))
    (hmin : ∀ (d' : ℕ) (ψ : FreeGroup (Fin d') →* G), Function.Surjective ψ → d ≤ d')
    (j : Fin r) (i : Fin d) :
    Vfun (ZMod p) φ (R j) i ∈ augIdeal (ZMod p) G := by
  have hmem : R j ∈ φ.ker := by
    rw [hR]
    exact Subgroup.subset_normalClosure ⟨j, rfl⟩
  have hw : φ (R j) = 1 := MonoidHom.mem_ker.mp hmem
  have hdvd : (p : ℤ) ∣ expSum i (R j) := p_dvd_expSum_of_mem_ker hp hG φ hφ hmin hw i
  rw [mem_augIdeal_iff]
  have h2 : augAlgHom (ZMod p) G (Vfun (ZMod p) φ (R j) i) = ((expSum i (R j) : ℤ) : ZMod p) := by
    rw [Vfun_apply, augAlgHom_groupAlgMap, ← expSum_cast_eq_aug]
  rw [h2, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact_mod_cast hdvd

end Work.GolodShafarevich.RelatorAug
