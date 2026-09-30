import Mathlib
import Submission.Work.Pi6.HALG.defs
import Submission.Work.Pi6.HALG.fibrationSetup
import Submission.Work.Pi6.HALG.rangeInputsY
import Submission.Work.Pi6.HALG.card_le_of_rank_le
import Submission.Work.Pi6.SQASM.dualityNonzero
import Submission.Work.Cohomology.kronH_bijective_field
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Pi6.Interfaces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.HALG

noncomputable section

open Work.Pi6

/-! ## Auxiliary lemmas about the Bockstein data -/

/-- `mulTwo` is multiplication by `2`. -/
lemma mulTwo_apply_sb2 (M : ModuleCat ℤ) (x : ↥M) : (mulTwo M).hom x = (2 : ℤ) • x := by
  show (2 : ℤ) • x = (2 : ℤ) • x
  rfl

/-- A subsingleton module has trivial `2`-torsion. -/
lemma twoKer_subsingleton {M : ModuleCat ℤ} (h : Subsingleton ↥M) :
    Subsingleton ↥(twoKer M) :=
  Subsingleton.intro fun a b => Subtype.ext (h.elim (Subtype.val a) (Subtype.val b))

/-- A subsingleton module has trivial `M/2M`. -/
lemma twoCok_subsingleton {M : ModuleCat ℤ} (h : Subsingleton ↥M) :
    Subsingleton ↥(twoCok M) := by
  haveI := h
  exact (Submodule.Quotient.mk_surjective (p := LinearMap.range (mulTwo M).hom)).subsingleton

/-- **The middle term of the mod-2 Bockstein sequence vanishes when both ends do.** -/
theorem subsingleton_zmodTwo_of_bockstein (hB2 : BocksteinTwo) (X : Type) [TopologicalSpace X]
    (n : ℕ) (hA : Subsingleton ↥(twoCok (HR ℤ X (n + 1))))
    (hC : Subsingleton ↥(twoKer (HR ℤ X n))) :
    Subsingleton ↥(HR (ZMod 2) X (n + 1)) := by
  obtain ⟨i, p, hprop⟩ := hB2
  obtain ⟨-, hex, -⟩ := hprop X n
  refine ⟨fun a b => ?_⟩
  have key : ∀ a : ↥(HR (ZMod 2) X (n + 1)), a = 0 := by
    intro a
    have ha : a ∈ Set.range (i X n) := (hex a).mp (hC.elim (p X n a) 0)
    obtain ⟨c, hc⟩ := Set.mem_range.mp ha
    have hc0 : c = 0 := hA.elim c 0
    rw [hc0, map_zero] at hc
    exact hc.symm
  rw [key a, key b]

/-! ## Elementary cardinality lemmas -/

/-- **Cardinality multiplicativity for a short exact sequence of abelian groups**, with no
finiteness hypotheses (`Nat.card` is `0` on infinite types, so the degenerate cases are automatic:
if `B` is infinite then so is `A` or `C`). -/
theorem card_eq_mul_card_of_shortExact_general {A B C : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (f : A →+ B) (g : B →+ C) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hex : Function.Exact f g) :
    Nat.card B = Nat.card A * Nat.card C := by
  have hker : f.range = g.ker := (AddMonoidHom.exact_iff.mp hex).symm
  have h1 : Nat.card ↥g.ker = Nat.card A := by
    rw [← hker]
    exact (Nat.card_congr (AddEquiv.ofBijective f.rangeRestrict
      ⟨fun a b h => hf (Subtype.ext_iff.mp h), AddMonoidHom.rangeRestrict_surjective f⟩).toEquiv).symm
  have h2 : Nat.card (B ⧸ g.ker) = Nat.card C :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hg).toEquiv
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker, h2, h1, Nat.mul_comm]

/-- **`M/2M ≅ ℤ/2` when `M` is an abelian group of order two.** -/
theorem card_twoCok_of_addEquiv_zmod_two (M : ModuleCat ℤ) (e : ↥M ≃+ ZMod 2) :
    Nat.card ↥(twoCok M) = 2 := by
  have hrange : LinearMap.range (mulTwo M).hom = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_range] at hx
    obtain ⟨y, hy⟩ := hx
    rw [mulTwo_apply_sb2] at hy
    have hy0 : (2 : ℤ) • e y = 0 := by
      rw [zsmul_eq_mul, show ((2 : ℤ) : ZMod 2) = 0 from by decide, zero_mul]
    refine e.injective ?_
    rw [← hy, map_zsmul, hy0, map_zero]
  have h1 : Nat.card ↥(twoCok M) = Nat.card (↥M ⧸ (⊥ : Submodule ℤ ↥M)) := by
    show Nat.card (↥M ⧸ LinearMap.range (mulTwo M).hom) = Nat.card (↥M ⧸ (⊥ : Submodule ℤ ↥M))
    rw [hrange]
  have hbij : Function.Bijective (Submodule.mkQ (⊥ : Submodule ℤ ↥M)) := by
    refine ⟨fun x y h => ?_, Submodule.mkQ_surjective _⟩
    have h2 : (⊥ : Submodule ℤ ↥M).mkQ (x - y) = 0 := by rw [map_sub, h, sub_self]
    have h3 : x - y ∈ (⊥ : Submodule ℤ ↥M) :=
      (Submodule.Quotient.mk_eq_zero (⊥ : Submodule ℤ ↥M)).mp h2
    exact sub_eq_zero.mp ((Submodule.mem_bot ℤ).mp h3)
  rw [h1]
  calc Nat.card (↥M ⧸ (⊥ : Submodule ℤ ↥M)) = Nat.card ↥M :=
        (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
    _ = Nat.card (ZMod 2) := Nat.card_congr e.toEquiv
    _ = 2 := Nat.card_zmod 2

/-- **The `2`-torsion of an abelian group of order three is trivial.** -/
theorem subsingleton_twoKer_of_addEquiv_zmod_three (M : ModuleCat ℤ) (e : ↥M ≃+ ZMod 3) :
    Subsingleton ↥(twoKer M) := by
  change Subsingleton (LinearMap.ker (mulTwo M).hom)
  have key : ∀ z : ZMod 3, (2 : ℤ) • z = 0 → z = 0 := by
    intro z hz
    rw [zsmul_eq_mul] at hz
    have h2 : ((2 : ℤ) : ZMod 3) ≠ 0 := by decide
    exact (mul_eq_zero.mp hz).resolve_left h2
  refine Subsingleton.intro fun a b => Subtype.ext ?_
  have ha : (2 : ℤ) • (Subtype.val a) = 0 := by
    have h := a.2
    rw [LinearMap.mem_ker] at h
    rwa [mulTwo_apply_sb2] at h
  have hb : (2 : ℤ) • (Subtype.val b) = 0 := by
    have h := b.2
    rw [LinearMap.mem_ker] at h
    rwa [mulTwo_apply_sb2] at h
  refine e.injective ?_
  rw [key (e (Subtype.val a)) (by rw [← map_zsmul, ha, map_zero]),
    key (e (Subtype.val b)) (by rw [← map_zsmul, hb, map_zero])]

/-- **The `2`-torsion of a finite abelian group of order `6` has two elements.** -/
theorem card_twoKer_of_card_six (M : ModuleCat ℤ) (h : Nat.card ↥M = 6) :
    Nat.card ↥(twoKer M) = 2 := by
  haveI : Finite ↥M := Nat.finite_of_card_ne_zero (by omega)
  set K : AddSubgroup ↥M := (LinearMap.ker (mulTwo M).hom).toAddSubgroup with hK
  have hKmem : ∀ x : ↥M, x ∈ K ↔ (2 : ℤ) • x = 0 := by
    intro x
    rw [hK, Submodule.mem_toAddSubgroup, LinearMap.mem_ker, mulTwo_apply_sb2]
  have hgoal : Nat.card ↥K = 2 := by
    -- Lagrange: `|K|` divides `6`
    have hdvd : Nat.card ↥K ∣ 6 := by
      have hL : Nat.card (↥M ⧸ K) * Nat.card ↥K = 6 := by
        rw [← AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup K, h]
      exact ⟨Nat.card (↥M ⧸ K), by rw [Nat.mul_comm]; exact hL.symm⟩
    -- Cauchy: `M` has an element of order two, which lies in `K`
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := ↥M) 2 (by rw [h]; norm_num)
    have hxK : x ∈ K := by
      rw [hKmem]
      exact (addOrderOf_dvd_iff_zsmul_eq_zero (x := x) (i := 2)).mp (by rw [hx]; norm_num)
    have hxne : x ≠ 0 := by
      intro h0
      rw [h0, addOrderOf_zero] at hx
      norm_num at hx
    have hne1 : Nat.card ↥K ≠ 1 := by
      intro hc
      haveI : Subsingleton ↥K := (Nat.card_eq_one_iff_unique.mp hc).1
      have h1 : (⟨x, hxK⟩ : ↥K) = 0 := Subsingleton.elim _ _
      exact hxne (congrArg Subtype.val h1)
    -- no element of order three lies in `K`
    have hno3 : ¬ (3 ∣ Nat.card ↥K) := by
      intro hd3
      obtain ⟨y, hy⟩ := exists_prime_addOrderOf_dvd_card' (G := ↥K) 3 hd3
      have hyM : addOrderOf (Subtype.val y) = 3 := by
        rw [AddSubgroup.addOrderOf_coe]; exact hy
      have hmem : (2 : ℤ) • (Subtype.val y) = 0 := (hKmem _).mp y.2
      have hd2 : ((addOrderOf (Subtype.val y) : ℕ) : ℤ) ∣ 2 :=
        (addOrderOf_dvd_iff_zsmul_eq_zero (x := Subtype.val y) (i := 2)).mpr hmem
      rw [hyM] at hd2
      norm_num at hd2
    have hne3 : Nat.card ↥K ≠ 3 := fun hc => hno3 (by rw [hc])
    have hne6 : Nat.card ↥K ≠ 6 := fun hc => hno3 (by rw [hc]; norm_num)
    have hle : Nat.card ↥K ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card ↥K := Nat.card_pos
    interval_cases Nat.card ↥K
    · exact absurd rfl hne1
    · rfl
    · exact absurd rfl hne3
    · norm_num at hdvd
    · norm_num at hdvd
    · exact absurd rfl hne6
  exact hgoal

/-- **A map which is surjective on homology is injective on cohomology** (over a field): the
transpose of a surjection is injective, and over a field the Kronecker pairing identifies `f^*` with
the transpose of `f_*` (`Work.Pi6.SQASM.kronH_natural_commRing`,
`Work.Cohomology.kronH_bijective_field`). -/
theorem cmap_injective_of_hmap_surjective (F : Type) [Field F] {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (h : Function.Surjective (Work.Pi6.hmap F f n).hom) :
    Function.Injective (Work.Pi6.cmap F f n).hom := by
  have hnat : ∀ (α : Coh F Y n) (c : HR F X n),
      Work.Cohomology.kronH F (TopCat.toSSet.obj (TopCat.of Y)) n α ((hmap F f n).hom c)
        = Work.Cohomology.kronH F (TopCat.toSSet.obj (TopCat.of X)) n
            ((cmap F f n).hom α) c :=
    fun α c => Work.Pi6.SQASM.kronH_natural_commRing F (TopCat.of X) (TopCat.of Y)
      (TopCat.ofHom f) n α c
  intro α β hab
  have hzero : (cmap F f n).hom (α - β) = 0 := by rw [map_sub, hab, sub_self]
  have hzero2 : (Work.Cohomology.kronH F (TopCat.toSSet.obj (TopCat.of X)) n)
      (0 : Coh F X n) = 0 := map_zero _
  have hphi : Work.Cohomology.kronH F (TopCat.toSSet.obj (TopCat.of Y)) n (α - β) = 0 := by
    apply LinearMap.ext
    intro z
    obtain ⟨c, rfl⟩ := h z
    calc (Work.Cohomology.kronH F (TopCat.toSSet.obj (TopCat.of Y)) n (α - β))
          ((hmap F f n).hom c)
        = (Work.Cohomology.kronH F (TopCat.toSSet.obj (TopCat.of X)) n
            ((cmap F f n).hom (α - β))) c := hnat (α - β) c
      _ = 0 := by rw [hzero, hzero2]; exact LinearMap.zero_apply c
  have hker : α - β = 0 :=
    (Work.Cohomology.kronH_bijective_field F (TopCat.toSSet.obj (TopCat.of Y)) n).1
      (by rw [hphi]
          exact ((Work.Cohomology.kronH F (TopCat.toSSet.obj (TopCat.of Y)) n).map_zero).symm)
  exact sub_eq_zero.mp hker

/-! ## The main statement -/

/-- **HALG step 3: `|H₇(Y;𝔽₂)| = 2` and `H₇(Y;ℤ) = 2·H₇(Y;ℤ)`.** -/
theorem stageBmod2 (hB2 : Work.Pi6.HALG.BocksteinTwo) (hR : Work.Pi6.SerreRangeLES)
    (hE : Work.Pi6.EFacts) (hZt : Work.Pi6.EMTableZ) (hT : Work.Pi6.TowerPi)
    (P3 : Type) [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3))
    (h3 : Work.Pi6.PostnikovData 3 12 g3 Work.Pi6.s3)
    (P4 : Type) [TopologicalSpace P4] (g4 : C(Work.Pi6.Ecov g3, P4))
    (h4 : Work.Pi6.PostnikovData 4 12 g4 (Work.Pi6.e0 g3))
    (hK4 : Work.Serre.IsEMSpaceUpTo (ZMod 2) 4 (by norm_num) 12 P4 (g4 (Work.Pi6.e0 g3)))
    (h5Y : Nonempty (Work.Pi6.HR ℤ (Work.Pi6.Ycov g3 g4) 5 ≃ₗ[ℤ] ZMod 2))
    (h6Y : Nat.card ↥(Work.Pi6.HR ℤ (Work.Pi6.Ycov g3 g4) 6) = 6) :
    Nat.card ↥(Work.Pi6.HR (ZMod 2) (Work.Pi6.Ycov g3 g4) 7) = 2 ∧
      (∀ a : Work.Pi6.HR ℤ (Work.Pi6.Ycov g3 g4) 7, ∃ b, (2 : ℤ) • b = a) := by
  obtain ⟨bkI, bkP, bkProp⟩ := hB2
  -- Serre range inputs
  obtain ⟨hYvan, hYpi0, hP4pi⟩ := rangeInputsY hT P3 g3 h3 P4 g4 h4
  obtain ⟨inclM, bdM, hexM⟩ := rangeLES_four (ZMod 2) hR g3 g4 hP4pi hYpi0
    (fun j hj hj5 => hYvan j hj (by omega))
  -- the integral tables of `E`
  obtain ⟨hE4, hE5, hE6, hE7, hEsq⟩ := hE P3 g3 h3
  -- ## `H₃(Y;𝔽₂) = 0`
  have h3Y : Subsingleton ↥(HR (ZMod 2) (Ycov g3 g4) 3) :=
    subsingleton_zmodTwo_of_bockstein ⟨bkI, bkP, bkProp⟩ (Ycov g3 g4) 2
      (twoCok_subsingleton (ModuleCat.subsingleton_of_isZero (hYvan 3 (by norm_num) (by norm_num))))
      (twoKer_subsingleton (ModuleCat.subsingleton_of_isZero (hYvan 2 (by norm_num) (by norm_num))))
  -- ## `H₄(Y;𝔽₂) = 0`
  have h4Y : Subsingleton ↥(HR (ZMod 2) (Ycov g3 g4) 4) :=
    subsingleton_zmodTwo_of_bockstein ⟨bkI, bkP, bkProp⟩ (Ycov g3 g4) 3
      (twoCok_subsingleton (ModuleCat.subsingleton_of_isZero (hYvan 4 (by norm_num) (by norm_num))))
      (twoKer_subsingleton (ModuleCat.subsingleton_of_isZero (hYvan 3 (by norm_num) (by norm_num))))
  -- ## `H₇(E;𝔽₂) = 0`
  have h7E : Subsingleton ↥(HR (ZMod 2) (Ecov g3) 7) :=
    subsingleton_zmodTwo_of_bockstein ⟨bkI, bkP, bkProp⟩ (Ecov g3) 6
      (twoCok_subsingleton hE7)
      (subsingleton_twoKer_of_addEquiv_zmod_three (HR ℤ (Ecov g3) 6) hE6.some.toAddEquiv)
  -- ## `(g₄)_*` is injective and surjective in degree `4`
  obtain ⟨hEx3a, hEx3b, -⟩ := hexM 3 (by norm_num)
  have hsurj4 : Function.Surjective (hmap (ZMod 2) g4 4).hom := fun y =>
    Set.mem_range.mp ((hEx3b y).mp (h3Y.elim ((bdM 3).hom y) 0))
  have hinj4 : Function.Injective (hmap (ZMod 2) g4 4).hom := by
    intro x y hxy
    have h1 : (hmap (ZMod 2) g4 4).hom (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := Set.mem_range.mp ((hEx3a (x - y)).mp h1)
    have hz0 : z = 0 := h4Y.elim z 0
    rw [hz0, map_zero] at hz
    exact sub_eq_zero.mp hz.symm
  -- ## `H₄(E;𝔽₂) ≠ 0`, hence `H₄(P₄;𝔽₂) ≠ 0`
  have hcardCok : Nat.card ↥(twoCok (HR ℤ (Ecov g3) 4)) = 2 :=
    card_twoCok_of_addEquiv_zmod_two (HR ℤ (Ecov g3) 4) hE4.some.toAddEquiv
  obtain ⟨x4, hx4⟩ : ∃ x : ↥(twoCok (HR ℤ (Ecov g3) 4)), x ≠ 0 := by
    obtain ⟨x, y, hxy, -⟩ := Nat.card_eq_two_iff.mp hcardCok
    by_cases hx : x = 0
    · exact ⟨y, fun hy => hxy (by rw [hx, hy])⟩
    · exact ⟨x, hx⟩
  have hB4ne : (bkI (Ecov g3) 3 x4) ≠ 0 := by
    intro h0
    refine hx4 ((bkProp (Ecov g3) 3).1 ?_)
    rw [h0, map_zero]
  have hv4ne : (hmap (ZMod 2) g4 4).hom (bkI (Ecov g3) 3 x4) ≠ 0 :=
    fun h0 => hB4ne (hinj4 (h0.trans (map_zero _).symm))
  -- ## a non-zero class `ι ∈ H⁴(P₄;𝔽₂)`
  obtain ⟨ι, hιne⟩ : ∃ ι : Coh (ZMod 2) P4 4, ι ≠ 0 := by
    obtain ⟨φ, hφ⟩ : ∃ φ : (↥(HR (ZMod 2) P4 4)) →ₗ[ZMod 2] ZMod 2,
        φ ((hmap (ZMod 2) g4 4).hom (bkI (Ecov g3) 3 x4)) ≠ 0 := by
      by_contra h
      push Not at h
      exact hv4ne ((Module.forall_dual_apply_eq_zero_iff (ZMod 2)
        ((hmap (ZMod 2) g4 4).hom (bkI (Ecov g3) 3 x4))).mp h)
    obtain ⟨ι, hι⟩ := (Work.Cohomology.kronH_bijective_field (ZMod 2)
      (TopCat.toSSet.obj (TopCat.of P4)) 4).2 φ
    exact ⟨ι, fun h0 => hφ (by
      have hz : φ = 0 := by
        rw [← hι, h0]
        exact (Work.Cohomology.kronH (ZMod 2) (TopCat.toSSet.obj (TopCat.of P4)) 4).map_zero
      rw [hz, LinearMap.zero_apply])⟩
  -- ## `g₄^*(ι) ≠ 0`, so `g₄^*(ι²) = g₄^*(ι)² ≠ 0`
  have hcinj := cmap_injective_of_hmap_surjective (ZMod 2) g4 4 hsurj4
  have hune : (cmap (ZMod 2) g4 4).hom ι ≠ 0 :=
    fun h0 => hιne (hcinj (h0.trans (map_zero _).symm))
  have hnat : (cmap (ZMod 2) g4 8).hom (cup (ZMod 2) P4 4 4 ι ι)
      = cup (ZMod 2) (Ecov g3) 4 4 ((cmap (ZMod 2) g4 4).hom ι)
          ((cmap (ZMod 2) g4 4).hom ι) :=
    Work.Cohomology.cupNaturalH (ZMod 2) (TopCat.ofHom g4) 4 4 ι ι
  have hsqne : cup (ZMod 2) (Ecov g3) 4 4 ((cmap (ZMod 2) g4 4).hom ι)
      ((cmap (ZMod 2) g4 4).hom ι) ≠ 0 := hEsq _ hune
  have hcmap8ne : cmap (ZMod 2) g4 8 ≠ 0 := by
    intro h0
    refine hsqne ?_
    have h1 : (cmap (ZMod 2) g4 8).hom (cup (ZMod 2) P4 4 4 ι ι) = 0 := by
      rw [h0, ModuleCat.hom_zero]
      rfl
    rwa [hnat] at h1
  have hmap8ne : hmap (ZMod 2) g4 8 ≠ 0 :=
    (Work.Pi6.SQASM.dualityNonzero (ZMod 2) g4 8).mp hcmap8ne
  -- ## the upper bound `|H₇(Y;𝔽₂)| ≤ 2`
  have hcardM8 : Nat.card ↥(HR (ZMod 2) P4 8) ≤ 4 := by
    have hrank := (hZt.1 P4 (g4 (e0 g3)) 12 le_rfl hK4).2.2
    have h4 := card_le_of_rank_le (𝕜 := ZMod 2) (V := ↥(HR (ZMod 2) P4 8)) 2 hrank
    simpa [Nat.card_zmod] using h4
  obtain ⟨-, hEx7, hEx7'⟩ := hexM 7 (by norm_num)
  have hsurj7 : Function.Surjective (bdM 7).hom := fun y =>
    Set.mem_range.mp ((hEx7' y).mp (h7E.elim ((inclM 7).hom y) 0))
  have hiso : Nat.card (↥(HR (ZMod 2) P4 8) ⧸ (LinearMap.ker (bdM 7).hom).toAddSubgroup)
      = Nat.card ↥(HR (ZMod 2) (Ycov g3 g4) 7) :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective
      (bdM 7).hom.toAddMonoidHom hsurj7).toEquiv
  have hLag := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    ((LinearMap.ker (bdM 7).hom).toAddSubgroup)
  haveI : Finite ↥(HR (ZMod 2) P4 8) := by
    haveI : Module.Finite (ZMod 2) ↥(HR (ZMod 2) P4 8) := by
      rw [← Module.rank_lt_aleph0_iff]
      exact lt_of_le_of_lt (hZt.1 P4 (g4 (e0 g3)) 12 le_rfl hK4).2.2
        (Cardinal.natCast_lt_aleph0 (n := 2))
    exact Module.finite_of_finite (ZMod 2)
  have hfunne : (hmap (ZMod 2) g4 8).hom ≠ 0 := by
    intro hh
    refine hmap8ne (ModuleCat.hom_ext ?_)
    rw [hh, ModuleCat.hom_zero]
  have hKcard : 2 ≤ Nat.card ↥(LinearMap.ker (bdM 7).hom).toAddSubgroup := by
    obtain ⟨y, hy⟩ : ∃ y, (hmap (ZMod 2) g4 8).hom y ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hfunne (LinearMap.ext hcon)
    have hmem : (hmap (ZMod 2) g4 8).hom y
        ∈ (LinearMap.ker (bdM 7).hom).toAddSubgroup := by
      rw [Submodule.mem_toAddSubgroup, LinearMap.mem_ker]
      exact (hEx7 _).mpr (Set.mem_range.mpr ⟨y, rfl⟩)
    have h2 : 2 ≤ Nat.card ↥(LinearMap.ker (bdM 7).hom).toAddSubgroup := by
      haveI : Fintype ↥(LinearMap.ker (bdM 7).hom).toAddSubgroup := Fintype.ofFinite _
      have hne : (⟨(hmap (ZMod 2) g4 8).hom y, hmem⟩ :
          ↥(LinearMap.ker (bdM 7).hom).toAddSubgroup) ≠ 0 := by
        intro hh
        exact hy (by simpa using congrArg Subtype.val hh)
      have hnt : Nontrivial ↥(LinearMap.ker (bdM 7).hom).toAddSubgroup := ⟨⟨_, 0, hne⟩⟩
      have h1 : 1 < Fintype.card ↥(LinearMap.ker (bdM 7).hom).toAddSubgroup :=
        Fintype.one_lt_card_iff_nontrivial.mpr hnt
      rw [Nat.card_eq_fintype_card]
      omega
    exact h2
  have hBcard : Nat.card ↥(HR (ZMod 2) (Ycov g3 g4) 7)
      * Nat.card ↥(LinearMap.ker (bdM 7).hom).toAddSubgroup
      = Nat.card ↥(HR (ZMod 2) P4 8) := by
    rw [← hiso]
    exact hLag.symm
  have hBle : Nat.card ↥(HR (ZMod 2) (Ycov g3 g4) 7) ≤ 2 := by
    have h2 : Nat.card ↥(HR (ZMod 2) (Ycov g3 g4) 7) * 2
        ≤ Nat.card ↥(HR (ZMod 2) P4 8) := by
      rw [← hBcard]
      exact Nat.mul_le_mul_left _ hKcard
    omega
  -- ## the mod-2 Bockstein sequence of `Y` in degree 7, and the second conjunct
  obtain ⟨hkI, hkEx, hkSurj⟩ := bkProp (Ycov g3 g4) 6
  have hcardSES : Nat.card ↥(HR (ZMod 2) (Ycov g3 g4) 7)
      = Nat.card ↥(twoCok (HR ℤ (Ycov g3 g4) 7))
        * Nat.card ↥(twoKer (HR ℤ (Ycov g3 g4) 6)) :=
    card_eq_mul_card_of_shortExact_general (bkI (Ycov g3 g4) 6).toAddMonoidHom
      (bkP (Ycov g3 g4) 6).toAddMonoidHom hkI hkSurj hkEx
  have hcardC : Nat.card ↥(twoKer (HR ℤ (Ycov g3 g4) 6)) = 2 :=
    card_twoKer_of_card_six (HR ℤ (Ycov g3 g4) 6) h6Y
  have hcardA : Nat.card ↥(twoCok (HR ℤ (Ycov g3 g4) 7)) = 1 := by
    have h1 : Nat.card ↥(twoCok (HR ℤ (Ycov g3 g4) 7)) * 2
        = Nat.card ↥(HR (ZMod 2) (Ycov g3 g4) 7) := by rw [hcardSES, hcardC]
    have h2 : Nat.card ↥(twoCok (HR ℤ (Ycov g3 g4) 7)) * 2 ≤ 2 := by
      rw [h1]; exact hBle
    have h3 : Nat.card ↥(twoCok (HR ℤ (Ycov g3 g4) 7)) ≠ 0 := by
      intro hA0
      have hfinB : Finite ↥(HR (ZMod 2) (Ycov g3 g4) 7) :=
        Finite.of_surjective (bdM 7).hom hsurj7
      have hBpos : Nat.card ↥(HR (ZMod 2) (Ycov g3 g4) 7) ≠ 0 :=
        Nat.card_ne_zero.mpr ⟨⟨0⟩, hfinB⟩
      refine hBpos ?_
      rw [hcardSES, hA0, Nat.zero_mul]
    omega
  constructor
  · simp [hcardSES, hcardA, hcardC]
  · intro a
    have hsub : Subsingleton ↥(twoCok (HR ℤ (Ycov g3 g4) 7)) :=
      (Nat.card_eq_one_iff_unique.mp hcardA).1
    have hz : (Submodule.mkQ (LinearMap.range (mulTwo (HR ℤ (Ycov g3 g4) 7)).hom) a
        : ↥(twoCok (HR ℤ (Ycov g3 g4) 7))) = 0 := hsub.elim _ _
    have hmem : a ∈ LinearMap.range (mulTwo (HR ℤ (Ycov g3 g4) 7)).hom :=
      (Submodule.Quotient.mk_eq_zero (LinearMap.range (mulTwo (HR ℤ (Ycov g3 g4) 7)).hom)).mp hz
    obtain ⟨b, hb⟩ := LinearMap.mem_range.mp hmem
    exact ⟨b, by rw [← mulTwo_apply_sb2 _ b, hb]⟩

end

end Work.Pi6.HALG
