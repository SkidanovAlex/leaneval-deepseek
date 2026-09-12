import Mathlib
import Submission.Commons.PeriodicTiling.rigid_pair_data

open scoped Pointwise
open Set

namespace Commons.PeriodicTiling

noncomputable section


lemma zsmul_image2_add {d : ℕ} (N : ℕ) (A B : Set (V d)) :
    zimg N (A + B) = zimg N A + zimg N B := by
  ext x
  constructor
  · intro hx
    rw [mem_zimg] at hx
    rcases hx with ⟨z, hz, hfz⟩
    rcases Set.mem_add.mp hz with ⟨a, ha, b, hb, hzab⟩
    refine Set.mem_add.mpr ⟨(N : ℤ) • a, mem_zimg.mpr ⟨a, ha, rfl⟩,
      (N : ℤ) • b, mem_zimg.mpr ⟨b, hb, rfl⟩, ?_⟩
    calc
      (N : ℤ) • a + (N : ℤ) • b = (N : ℤ) • (a + b) := by rw [smul_add_pointwise]
      _ = (N : ℤ) • z := congrArg (fun y : V d => (N : ℤ) • y) hzab
      _ = x := hfz.symm
  · intro hx
    rcases Set.mem_add.mp hx with ⟨a', ha', b', hb', hx'⟩
    rw [mem_zimg] at ha' hb'
    rcases ha' with ⟨a0, ha0, rfl⟩
    rcases hb' with ⟨b0, hb0, rfl⟩
    rw [mem_zimg]
    refine ⟨a0 + b0, Set.mem_add.mpr ⟨a0, ha0, b0, hb0, rfl⟩, ?_⟩
    calc
      x = (N : ℤ) • a0 + (N : ℤ) • b0 := by simpa using hx'.symm
      _ = (N : ℤ) • (a0 + b0) := by rw [smul_add_pointwise]

lemma zimg_union {d : ℕ} (N : ℕ) (A B : Set (V d)) :
    zimg N (A ∪ B) = zimg N A ∪ zimg N B := by
  ext x
  constructor
  · intro hx
    rw [mem_zimg] at hx
    rcases hx with ⟨y, hy, hyeq⟩
    rcases hy with hy | hy
    · left
      exact mem_zimg.mpr ⟨y, hy, hyeq⟩
    · right
      exact mem_zimg.mpr ⟨y, hy, hyeq⟩
  · intro hx
    rcases hx with hx | hx
    · rw [mem_zimg] at hx
      rcases hx with ⟨y, hy, hyeq⟩
      exact mem_zimg.mpr ⟨y, Or.inl hy, hyeq⟩
    · rw [mem_zimg] at hx
      rcases hx with ⟨y, hy, hyeq⟩
      exact mem_zimg.mpr ⟨y, Or.inr hy, hyeq⟩

lemma zimg_singleton {d : ℕ} (N : ℕ) (x : V d) :
    zimg N ({x} : Set (V d)) = {((N : ℤ) • x)} := by
  ext y
  constructor
  · intro hy
    rw [mem_zimg] at hy
    rcases hy with ⟨z, hz, hyeq⟩
    have hzx : z = x := by simpa using hz
    subst z
    rw [hyeq]
    simp
  · intro hy
    have hy' : y = (N : ℤ) • x := by simpa using hy
    rw [hy']
    exact mem_zimg.mpr ⟨x, by simp, rfl⟩

lemma smul_injective_int {N : ℕ} (hN : 0 < N) :
    Function.Injective (fun x : ℤ => (N : ℤ) • x) := by
  intro a b h
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  exact mul_left_cancel₀ hN0 h

lemma zsmul_injective_pointwise {d : ℕ} {N : ℕ} (hN : 0 < N) :
    Function.Injective (fun x : V d => (N : ℤ) • x) := by
  intro a b h
  apply funext
  intro i
  have hi := congrFun h i
  simpa [Pi.smul_apply] using (smul_injective_int (N := N) hN hi)

lemma zimg_inter {d : ℕ} {N : ℕ} (hN : 0 < N) (A B : Set (V d)) :
    zimg N (A ∩ B) = zimg N A ∩ zimg N B := by
  ext x
  constructor
  · intro hx
    rw [mem_zimg] at hx
    rcases hx with ⟨a, ha, rfl⟩
    constructor
    · exact mem_zimg.mpr ⟨a, ha.1, rfl⟩
    · exact mem_zimg.mpr ⟨a, ha.2, rfl⟩
  · intro hx
    rcases hx with ⟨hx1, hx2⟩
    rw [mem_zimg] at hx1
    rcases hx1 with ⟨a, ha1, hxa⟩
    have ha2 : a ∈ B := by
      have hx2' : (N : ℤ) • a ∈ zimg N B := by
        rw [← hxa]
        exact hx2
      rw [mem_zimg] at hx2'
      rcases hx2' with ⟨b, hb, hb_eq⟩
      have hab : a = b := zsmul_injective_pointwise (N := N) hN hb_eq
      rwa [hab]
    exact mem_zimg.mpr ⟨a, ⟨ha1, ha2⟩, hxa⟩

lemma zimg_disjoint {d : ℕ} {N : ℕ} (hN : 0 < N) {A B : Set (V d)}
    (h : Disjoint A B) : Disjoint (zimg N A) (zimg N B) := by
  rw [disjoint_iff_inter_eq_empty] at h ⊢
  rw [← zimg_inter (N := N) hN]
  rw [h]
  exact zimg_empty (d := d) N

lemma mem_zimg_of_mem {d : ℕ} {N : ℕ} {A : Set (V d)} {a : V d} (ha : a ∈ A) :
    (N : ℤ) • a ∈ zimg N A := by
  exact mem_zimg.mpr ⟨a, ha, rfl⟩

-- image of IsComplement under injective scaling, "onto NV with unique decomp"
lemma image_IsComplement_unique {d N : ℕ} (hN : 0 < N) {S T : Set (V d)}
    (hST : AddSubgroup.IsComplement S T) :
    zimg N S + zimg N T = NV d N ∧
      ∀ u ∈ NV d N, ∃! p : (zimg N S) × (zimg N T), (p.1 : V d) + (p.2 : V d) = u := by
  constructor
  · calc
      zimg N S + zimg N T = zimg N (S + T) := by rw [zsmul_image2_add]
      _ = zimg N Set.univ := by rw [hST.add_eq]
      _ = NV d N := rfl
  · intro u hu
    rcases (mem_zimg.mp hu) with ⟨t0, ht0, hut0⟩
    rcases (hST.existsUnique t0) with ⟨p, hp, hp'⟩
    refine ⟨(⟨(N : ℤ) • (p.1 : V d), mem_zimg_of_mem (N := N) p.1.2⟩,
             ⟨(N : ℤ) • (p.2 : V d), mem_zimg_of_mem (N := N) p.2.2⟩), ?_, ?_⟩
    · change ((N : ℤ) • (p.1 : V d)) + ((N : ℤ) • (p.2 : V d)) = u
      calc
        (N : ℤ) • (p.1 : V d) + (N : ℤ) • (p.2 : V d) =
            (N : ℤ) • ((p.1 : V d) + (p.2 : V d)) := by rw [smul_add_pointwise]
        _ = (N : ℤ) • t0 := congrArg (fun y : V d => (N : ℤ) • y) hp
        _ = u := hut0.symm
    · intro q' hq'
      apply Prod.ext
      · apply Subtype.ext
        rcases (mem_zimg.mp q'.1.2) with ⟨s0, hs0, hs0_eq⟩
        rcases (mem_zimg.mp q'.2.2) with ⟨t1, ht1, ht1_eq⟩
        have hsum0 : (N : ℤ) • (s0 + t1) = (N : ℤ) • t0 := by
          rw [smul_add_pointwise]
          calc
            (N : ℤ) • s0 + (N : ℤ) • t1 = (q'.1 : V d) + (q'.2 : V d) := by rw [hs0_eq, ht1_eq]
            _ = u := hq'
            _ = (N : ℤ) • t0 := hut0
        have hsum : s0 + t1 = t0 := zsmul_injective_pointwise (N := N) hN hsum0
        have hpair : ((⟨s0, hs0⟩ : S), (⟨t1, ht1⟩ : T)) = p :=
          hp' (⟨s0, hs0⟩, ⟨t1, ht1⟩) hsum
        have hp1 : s0 = (p.1 : V d) := by
          have hf := congrArg (fun z : S × T => (z.1 : V d)) hpair
          simpa using hf
        calc
          (q'.1 : V d) = (N : ℤ) • s0 := by rw [hs0_eq]
          _ = (N : ℤ) • (p.1 : V d) := by rw [hp1]
      · apply Subtype.ext
        rcases (mem_zimg.mp q'.2.2) with ⟨t1, ht1, ht1_eq⟩
        rcases (mem_zimg.mp q'.1.2) with ⟨s0, hs0, hs0_eq⟩
        have hsum0 : (N : ℤ) • (s0 + t1) = (N : ℤ) • t0 := by
          rw [smul_add_pointwise]
          calc
            (N : ℤ) • s0 + (N : ℤ) • t1 = (q'.1 : V d) + (q'.2 : V d) := by rw [hs0_eq, ht1_eq]
            _ = u := hq'
            _ = (N : ℤ) • t0 := hut0
        have hsum : s0 + t1 = t0 := zsmul_injective_pointwise (N := N) hN hsum0
        have hpair : ((⟨s0, hs0⟩ : S), (⟨t1, ht1⟩ : T)) = p :=
          hp' (⟨s0, hs0⟩, ⟨t1, ht1⟩) hsum
        have hp2 : t1 = (p.2 : V d) := by
          have hf := congrArg (fun z : S × T => (z.2 : V d)) hpair
          simpa using hf
        calc
          (q'.2 : V d) = (N : ℤ) • t1 := by rw [ht1_eq]
          _ = (N : ℤ) • (p.2 : V d) := by rw [hp2]


-- ============================================================
-- PART B : transversal D for K = ker π
-- ============================================================

section PartB
variable {G : Type*} [AddCommGroup G] {d : ℕ}
variable (π : V d →+ G)

lemma ker_coe_mem_iff (x : V d) : x ∈ (π.ker : Set (V d)) ↔ π x = 0 := by
  simpa using (AddMonoidHom.mem_ker (f := π) (x := x))

lemma zero_mem_ker_set : (0 : V d) ∈ (π.ker : Set (V d)) := by
  exact zero_mem π.ker

/-- uniqueness of the transversal representative -/
lemma D_unique_of_pi_eq (D : Set (V d)) (hD : AddSubgroup.IsComplement D (π.ker : Set (V d)))
    {u₁ u₂ : V d} (hu₁ : u₁ ∈ D) (hu₂ : u₂ ∈ D) (hπ : π u₁ = π u₂) : u₁ = u₂ := by
  have hker : u₁ - u₂ ∈ (π.ker : Set (V d)) := by
    rw [ker_coe_mem_iff π]
    rw [map_sub, hπ]
    exact sub_self (π u₂)
  have hu := hD.existsUnique u₁
  rcases hu with ⟨p, hp, hp'⟩
  have h0 : (0 : V d) ∈ (π.ker : Set (V d)) := by exact zero_mem π.ker
  have p1 : ((⟨u₁, hu₁⟩ : D), (⟨0, h0⟩ : (π.ker : Set (V d)))) = p := by
    apply hp'
    change (u₁ : V d) + 0 = u₁
    simp
  have p2 : ((⟨u₂, hu₂⟩ : D), (⟨u₁ - u₂, hker⟩ : (π.ker : Set (V d)))) = p := by
    apply hp'
    change (u₂ : V d) + (u₁ - u₂) = u₁
    abel
  have hp1' : (⟨u₁, hu₁⟩ : D) = p.1 := congrArg Prod.fst p1
  have hp2' : (⟨u₂, hu₂⟩ : D) = p.1 := congrArg Prod.fst p2
  exact congrArg (fun z : D => (z : V d)) (hp1'.trans hp2'.symm)

/-- every element of G has a representative in D -/
lemma exists_D_of_pi (D : Set (V d)) (hD : AddSubgroup.IsComplement D (π.ker : Set (V d)))
    (hπ : Function.Surjective π) (g : G) : ∃ u : V d, u ∈ D ∧ π u = g := by
  rcases hπ g with ⟨v, hv⟩
  rcases (hD.existsUnique v) with ⟨p, hp, hp'⟩
  refine ⟨(p.1 : V d), p.1.2, ?_⟩
  have hk0 : π (p.2 : V d) = 0 := (ker_coe_mem_iff π (p.2 : V d)).mp p.2.2
  calc
    π (p.1 : V d) = π (p.1 : V d) + π (p.2 : V d) := by rw [hk0, add_zero]
    _ = π ((p.1 : V d) + (p.2 : V d)) := by rw [map_add]
    _ = π v := by rw [hp]
    _ = g := hv

/-- D ∩ ker is a singleton -/
lemma D_inter_ker_singleton (D : Set (V d))
    (hD : AddSubgroup.IsComplement D (π.ker : Set (V d)))
    (hπ : Function.Surjective π) :
    ∃ z : V d, (π ⁻¹' ({0} : Set G)) ∩ D = {z} := by
  rcases (hD.existsUnique 0) with ⟨p, hp, hp'⟩
  let z : V d := (p.1 : V d)
  refine ⟨z, ?_⟩
  have hzD : z ∈ D := by
    dsimp [z]
    exact p.1.2
  have hz0 : π z = 0 := by
    dsimp [z]
    have hk0 : π (p.2 : V d) = 0 := (ker_coe_mem_iff π (p.2 : V d)).mp p.2.2
    calc
      π (p.1 : V d) = π (p.1 : V d) + π (p.2 : V d) := by rw [hk0, add_zero]
      _ = π ((p.1 : V d) + (p.2 : V d)) := by rw [map_add]
      _ = π 0 := by rw [hp]
      _ = 0 := map_zero π
  ext x
  constructor
  · intro hx
    rw [Set.mem_inter_iff, Set.mem_preimage] at hx
    have hx0 : π x = 0 := by simpa using hx.1
    have hxz : x = z := D_unique_of_pi_eq π D hD hx.2 hzD (by
      calc
        π x = 0 := hx0
        _ = π z := hz0.symm)
    rw [hxz]
    simp
  · intro hx
    have hx' : x = z := by simpa using hx
    subst x
    rw [Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨by simpa using hz0, hzD⟩

/-- pullback preimage identity: π⁻¹(A + F) = π⁻¹A + (D ∩ π⁻¹F), for arbitrary sets -/
lemma preimage_add_eq (D : Set (V d)) (hD : AddSubgroup.IsComplement D (π.ker : Set (V d)))
    (hπ : Function.Surjective π) {A F : Set G} :
    π ⁻¹' (A + F) = π ⁻¹' A + ((π ⁻¹' F) ∩ D) := by
  ext v
  constructor
  · intro hv
    rw [Set.mem_preimage, Set.mem_add] at hv
    rcases hv with ⟨a, ha, f, hf, hsum⟩
    rcases (exists_D_of_pi π D hD hπ f) with ⟨e, heD, heπ⟩
    refine Set.mem_add.mpr ⟨v - e, ?_, e, ?_, ?_⟩
    · rw [Set.mem_preimage]
      rw [map_sub, heπ]
      have h : π v - f = a := by
        calc
          π v - f = (a + f) - f := by rw [← hsum]
          _ = a := by abel
      rwa [h]
    · rw [Set.mem_inter_iff]
      exact ⟨by rw [Set.mem_preimage]; exact heπ.symm ▸ hf, heD⟩
    · exact sub_add_cancel v e
  · intro hv
    rw [Set.mem_add] at hv
    rcases hv with ⟨a, ha, x, hx, hsum⟩
    rw [Set.mem_preimage, Set.mem_add]
    refine ⟨π a, ?_, π x, ?_, ?_⟩
    · rw [Set.mem_preimage] at ha
      exact ha
    · rw [Set.mem_inter_iff] at hx
      exact (Set.mem_preimage.mp hx.1)
    · rw [← map_add π a x, hsum]

/-- The pullback complement: if A ⊕ F = G then π⁻¹A ⊕ (π⁻¹F∩D) = V. -/
lemma pullback_IsComplement (D : Set (V d))
    (hD : AddSubgroup.IsComplement D (π.ker : Set (V d)))
    (hπ : Function.Surjective π)
    {A F : Set G} (hAF : AddSubgroup.IsComplement A F) :
    AddSubgroup.IsComplement (π ⁻¹' A) ((π ⁻¹' F) ∩ D) := by
  classical
  rw [AddSubgroup.isComplement_iff_existsUnique]
  intro v
  -- existence
  have hπv : π v ∈ A + F := by
    rw [hAF.add_eq]
    trivial
  rcases (Set.mem_add.mp hπv) with ⟨a, ha, f, hf, hπv_eq⟩
  let e : V d := Classical.choose (exists_D_of_pi π D hD hπ f)
  have heD : e ∈ D := (Classical.choose_spec (exists_D_of_pi π D hD hπ f)).1
  have heπ : π e = f := (Classical.choose_spec (exists_D_of_pi π D hD hπ f)).2
  let x0 : V d := v - e
  have hx0A : x0 ∈ π ⁻¹' A := by
    rw [Set.mem_preimage]
    rw [map_sub, heπ]
    have h : π v - f = a := by
      calc
        π v - f = (a + f) - f := by rw [← hπv_eq]
        _ = a := by abel
    rwa [h]
  have heF : e ∈ (π ⁻¹' F) ∩ D := by
    rw [Set.mem_inter_iff]
    exact ⟨by rw [Set.mem_preimage]; exact heπ.symm ▸ hf, heD⟩
  refine ⟨(⟨x0, hx0A⟩, ⟨e, heF⟩), ?_, ?_⟩
  · change x0 + e = v
    dsimp [x0]
    exact sub_add_cancel v e
  · intro y hy
    have hyA : (y.1 : V d) ∈ π ⁻¹' A := y.1.2
    have hyDmem : (y.2 : V d) ∈ (π ⁻¹' F) ∩ D := y.2.2
    rw [Set.mem_inter_iff] at hyDmem
    rcases hyDmem with ⟨hyF0, hyD⟩
    have hyA' : π (y.1 : V d) ∈ A := Set.mem_preimage.mp hyA
    have hx0A' : π x0 ∈ A := Set.mem_preimage.mp hx0A
    have hyF : π (y.2 : V d) ∈ F := Set.mem_preimage.mp hyF0
    have hdF : π e ∈ F := by rw [heπ]; exact hf
    have hsum_eq : (y.1 : V d) + (y.2 : V d) = x0 + e := by
      calc
        (y.1 : V d) + (y.2 : V d) = v := hy
        _ = x0 + e := by
          dsimp [x0]
          exact (sub_add_cancel v e).symm
    have hπsum : π (y.1 : V d) + π (y.2 : V d) = π x0 + π e := by
      rw [← map_add π (y.1 : V d) (y.2 : V d), ← map_add π x0 e, hsum_eq]
    have hpair := IsComplement_add_left_unique hAF hyA' hx0A' hyF hdF hπsum
    apply Prod.ext
    · apply Subtype.ext
      have he2 : (y.2 : V d) = e := D_unique_of_pi_eq π D hD hyD heD hpair.2
      calc
        (y.1 : V d) = (y.1 : V d) + (y.2 : V d) - e := by rw [he2]; abel
        _ = x0 + e - e := by rw [hsum_eq]
        _ = x0 := by abel
    · apply Subtype.ext
      exact D_unique_of_pi_eq π D hD hyD heD hpair.2
end PartB

-- ============================================================
-- PART C : NV decomposition of the pullback partition
-- ============================================================

section LevelC
variable {G : Type*} [AddCommGroup G] {d : ℕ}
variable (π : V d →+ G) (D : Set (V d))
variable (hD : AddSubgroup.IsComplement D (π.ker : Set (V d)))
variable (hπ : Function.Surjective π)

/-- subtraction distributes over the pointwise scalar -/
lemma zsmul_sub_pointwise {d : ℕ} (n : ℤ) (x y : V d) : n • (x - y) = n • x - n • y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, smul_add_pointwise, smul_neg_pointwise]

/-- π⁻¹A is ker-periodic: π⁻¹A + ker = π⁻¹A -/
lemma preimage_periodic_ker (A : Set G) : π ⁻¹' A + (π.ker : Set (V d)) = π ⁻¹' A := by
  apply le_antisymm
  · intro x hx
    rcases Set.mem_add.mp hx with ⟨a, ha, k, hk, hsum⟩
    rw [Set.mem_preimage]
    have hk0 : π k = 0 := (ker_coe_mem_iff π k).mp hk
    have hval : π x = π a := by
      calc
        π x = π (a + k) := by rw [hsum]
        _ = π a + π k := by rw [map_add]
        _ = π a := by rw [hk0, add_zero]
    rw [hval]
    exact Set.mem_preimage.mp ha
  · intro x hx
    refine Set.mem_add.mpr ⟨x, hx, 0, zero_mem_ker_set π, ?_⟩
    rw [add_zero]

/-- Ã := N·π⁻¹A is NL-periodic -/
lemma scaled_preimage_periodic (A : Set G) (N : ℕ) :
    zimg N (π ⁻¹' A) + NL d N π.ker = zimg N (π ⁻¹' A) := by
  calc
    zimg N (π ⁻¹' A) + NL d N π.ker
        = zimg N (π ⁻¹' A) + zimg N (π.ker : Set (V d)) := rfl
    _ = zimg N (π ⁻¹' A + (π.ker : Set (V d))) := by rw [zsmul_image2_add]
    _ = zimg N (π ⁻¹' A) := by rw [preimage_periodic_ker π A]

/-- scaling is a group-endomorphism over set subtraction -/
lemma zimg_sub {d : ℕ} (N : ℕ) (A B : Set (V d)) : zimg N (A - B) = zimg N A - zimg N B := by
  ext x
  constructor
  · intro hx
    rw [mem_zimg] at hx
    rcases hx with ⟨w, hw, rfl⟩
    rw [Set.mem_sub] at hw
    rcases hw with ⟨a, ha, b, hb, hsub⟩
    rw [Set.mem_sub]
    refine ⟨(N : ℤ) • a, mem_zimg.mpr ⟨a, ha, rfl⟩, (N : ℤ) • b, mem_zimg.mpr ⟨b, hb, rfl⟩, ?_⟩
    rw [← zsmul_sub_pointwise (N : ℤ) a b]
    exact congrArg (fun y : V d => (N : ℤ) • y) hsub
  · intro hx
    rw [Set.mem_sub] at hx
    rcases hx with ⟨a, ha, b, hb, hxeq⟩
    rw [mem_zimg] at ha hb
    rcases ha with ⟨a0, ha0, rfl⟩
    rcases hb with ⟨b0, hb0, rfl⟩
    rw [mem_zimg]
    refine ⟨a0 - b0, ?_, ?_⟩
    · rw [Set.mem_sub]
      exact ⟨a0, ha0, b0, hb0, rfl⟩
    · calc
        x = (N : ℤ) • a0 - (N : ℤ) • b0 := hxeq.symm
        _ = (N : ℤ) • (a0 - b0) := by rw [zsmul_sub_pointwise]

/-- if A ⊕ F = G then (A-A) ∩ (F-F) ⊆ {0} -/
lemma complement_AA_inter_FF {A F : Set G} (hAF : AddSubgroup.IsComplement A F) :
    (A - A) ∩ (F - F) ⊆ ({0} : Set G) := by
  intro w hw
  rcases hw with ⟨hw1, hw2⟩
  rw [Set.mem_sub] at hw1 hw2
  rcases hw1 with ⟨a₁, ha₁, a₂, ha₂, hw_a⟩
  rcases hw2 with ⟨f₁, hf₁, f₂, hf₂, hw_f⟩
  have hsum : a₁ + f₂ = a₂ + f₁ := by
    have hsum0 : (a₁ + f₂) - (a₂ + f₁) = 0 := by
      calc
        (a₁ + f₂) - (a₂ + f₁) = (a₁ - a₂) - (f₁ - f₂) := by abel
        _ = w - w := by rw [hw_a, hw_f]
        _ = 0 := sub_self w
    exact sub_eq_zero.mp hsum0
  have hpair := IsComplement_add_left_unique hAF ha₁ ha₂ hf₂ hf₁ hsum
  have hw0 : w = 0 := by
    calc
      w = a₁ - a₂ := hw_a.symm
      _ = a₂ - a₂ := by rw [hpair.1]
      _ = 0 := sub_self a₂
  simpa [hw0]

/-- if A ⊕ F = G and 0∈F then (A-A) ∩ (F∖{0}) = ∅ -/
lemma complement_AA_inter_F {A F : Set G} (hAF : AddSubgroup.IsComplement A F)
    (h0F : (0 : G) ∈ F) : Disjoint (A - A) (F \ {0}) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have hx2F : x ∈ F - F := by
    rcases hx2 with ⟨hxF, hx0⟩
    rw [Set.mem_sub]
    exact ⟨x, hxF, 0, h0F, by abel⟩
  have hsub : x ∈ ({0} : Set G) := complement_AA_inter_FF hAF ⟨hx1, hx2F⟩
  have hx0 : x = 0 := by simpa using hsub
  rw [Set.mem_sdiff] at hx2
  exact hx2.2 hx0

/-- preimage of F∖{0} ∩ D, disjoint from the zero-preimage part -/
lemma preimageF_split_disjoint (F : Set G) :
    Disjoint (π ⁻¹' (F \ {0}) ∩ D) (π ⁻¹' ({0} : Set G) ∩ D) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  rw [Set.mem_inter_iff] at hx1 hx2
  have h1 : π x ∈ F \ {0} := Set.mem_preimage.mp hx1.1
  have h2 : π x = 0 := by
    have h2' : π x ∈ ({0} : Set G) := Set.mem_preimage.mp hx2.1
    simpa using h2'
  rw [Set.mem_sdiff] at h1
  exact h1.2 h2

/-- if x is in the image of π⁻¹F∩D, then it is in X or in the zero-piece -/
lemma zimg_preimageF_mem_cases {F : Set G} (h0F : (0 : G) ∈ F) {N : ℕ} {x : V d}
    (hx : x ∈ zimg N ((π ⁻¹' F) ∩ D)) :
    x ∈ zimg N ((π ⁻¹' (F \ {0})) ∩ D) ∨
      x ∈ zimg N ((π ⁻¹' ({0} : Set G)) ∩ D) := by
  rw [mem_zimg] at hx
  rcases hx with ⟨w, hw, rfl⟩
  rw [Set.mem_inter_iff] at hw
  have hwF : π w ∈ F := Set.mem_preimage.mp hw.1
  by_cases hw0 : π w = 0
  · right
    exact mem_zimg.mpr ⟨w, by
      rw [Set.mem_inter_iff]
      exact ⟨by rw [Set.mem_preimage]; simpa using hw0, hw.2⟩, rfl⟩
  · left
    exact mem_zimg.mpr ⟨w, by
      rw [Set.mem_inter_iff]
      exact ⟨by rw [Set.mem_preimage]; exact ⟨hwF, hw0⟩, hw.2⟩, rfl⟩

end LevelC

-- ============================================================
-- PART D : regrouping lemma and forward direction
-- ============================================================

section LevelD

/-- uniqueness for the regrouping complement: uses joint injectivity and
  the directness of X⊕AA -/
private lemma regrouping_unique {d : ℕ} {T₁ T₂ X AA : Set (V d)}
    (hJoin : Function.Injective (jointSum (d := d) (X + AA) AA T₁ T₂))
    (hDirect : ∀ ⦃a b x y : V d⦄, a ∈ AA → b ∈ AA → x ∈ X → y ∈ X →
      a + x = b + y → a = b ∧ x = y)
    {a b f g : V d} (ha : a ∈ AA) (hb : b ∈ AA)
    (hf : f ∈ (X + T₁) ∪ T₂) (hg : g ∈ (X + T₁) ∪ T₂)
    (hsum : a + f = b + g) : a = b ∧ f = g := by
  classical
  rcases hf with hf1 | hf2
  · rcases hg with hg1 | hg2
    · rcases (Set.mem_add.mp hf1) with ⟨x, hx, t₁, ht₁, hft⟩
      rcases (Set.mem_add.mp hg1) with ⟨y, hy, t₁', ht₁', hgt⟩
      have hval : (a + x) + t₁ = (b + y) + t₁' := by
        calc
          (a + x) + t₁ = a + (x + t₁) := by abel
          _ = a + f := by rw [hft]
          _ = b + g := hsum
          _ = b + (y + t₁') := by rw [← hgt]
          _ = (b + y) + t₁' := by abel
      have hmem1 : a + x ∈ X + AA := Set.mem_add.mpr ⟨x, hx, a, ha, by abel⟩
      have hmem2 : b + y ∈ X + AA := Set.mem_add.mpr ⟨y, hy, b, hb, by abel⟩
      let z1 : Sum {p : V d × V d | p.1 ∈ X + AA ∧ p.2 ∈ T₁}
                   {p : V d × V d | p.1 ∈ AA ∧ p.2 ∈ T₂} :=
        Sum.inl ⟨((a + x), t₁), ⟨hmem1, ht₁⟩⟩
      let z2 : Sum {p : V d × V d | p.1 ∈ X + AA ∧ p.2 ∈ T₁}
                   {p : V d × V d | p.1 ∈ AA ∧ p.2 ∈ T₂} :=
        Sum.inl ⟨((b + y), t₁'), ⟨hmem2, ht₁'⟩⟩
      have hz1 : jointSum (d := d) (X + AA) AA T₁ T₂ z1 = (a + x) + t₁ := by
        dsimp [z1, jointSum]
      have hz2 : jointSum (d := d) (X + AA) AA T₁ T₂ z2 = (b + y) + t₁' := by
        dsimp [z2, jointSum]
      have hEqZ : z1 = z2 := hJoin (by rw [hz1, hz2]; exact hval)
      have hEqInl : (⟨((a + x), t₁), ⟨hmem1, ht₁⟩⟩ : {p : V d × V d | p.1 ∈ X + AA ∧ p.2 ∈ T₁})
          = ⟨((b + y), t₁'), ⟨hmem2, ht₁'⟩⟩ := Sum.inl.inj hEqZ
      have hcx : a + x = b + y := by
        have h := congrArg (fun q : {p : V d × V d | p.1 ∈ X + AA ∧ p.2 ∈ T₁} => (q : V d × V d).1) hEqInl
        simpa using h
      have hct : t₁ = t₁' := by
        have h := congrArg (fun q : {p : V d × V d | p.1 ∈ X + AA ∧ p.2 ∈ T₁} => (q : V d × V d).2) hEqInl
        simpa using h
      have hd := hDirect ha hb hx hy hcx
      constructor
      · exact hd.1
      · calc
          f = x + t₁ := hft.symm
          _ = y + t₁' := by rw [hd.2, hct]
          _ = g := hgt
    · rcases (Set.mem_add.mp hf1) with ⟨x, hx, t₁, ht₁, hft⟩
      have hval : (a + x) + t₁ = b + g := by
        calc
          (a + x) + t₁ = a + (x + t₁) := by abel
          _ = a + f := by rw [hft]
          _ = b + g := hsum
      have hmem1 : a + x ∈ X + AA := Set.mem_add.mpr ⟨x, hx, a, ha, by abel⟩
      let z1 : Sum {p : V d × V d | p.1 ∈ X + AA ∧ p.2 ∈ T₁}
                   {p : V d × V d | p.1 ∈ AA ∧ p.2 ∈ T₂} :=
        Sum.inl ⟨((a + x), t₁), ⟨hmem1, ht₁⟩⟩
      let z2 : Sum {p : V d × V d | p.1 ∈ X + AA ∧ p.2 ∈ T₁}
                   {p : V d × V d | p.1 ∈ AA ∧ p.2 ∈ T₂} :=
        Sum.inr ⟨(b, g), ⟨hb, hg2⟩⟩
      have hz1 : jointSum (d := d) (X + AA) AA T₁ T₂ z1 = (a + x) + t₁ := by
        dsimp [z1, jointSum]
      have hz2 : jointSum (d := d) (X + AA) AA T₁ T₂ z2 = b + g := by
        dsimp [z2, jointSum]
      have hEqZ : z1 = z2 := hJoin (by rw [hz1, hz2]; exact hval)
      nomatch hEqZ
  · rcases hg with hg1 | hg2
    · rcases (Set.mem_add.mp hg1) with ⟨y, hy, t₁', ht₁', hgt⟩
      have hval : a + f = (b + y) + t₁' := by
        calc
          a + f = b + g := hsum
          _ = b + (y + t₁') := by rw [← hgt]
          _ = (b + y) + t₁' := by abel
      have hmem2 : b + y ∈ X + AA := Set.mem_add.mpr ⟨y, hy, b, hb, by abel⟩
      let z1 : Sum {p : V d × V d | p.1 ∈ X + AA ∧ p.2 ∈ T₁}
                   {p : V d × V d | p.1 ∈ AA ∧ p.2 ∈ T₂} :=
        Sum.inr ⟨(a, f), ⟨ha, hf2⟩⟩
      let z2 : Sum {p : V d × V d | p.1 ∈ X + AA ∧ p.2 ∈ T₁}
                   {p : V d × V d | p.1 ∈ AA ∧ p.2 ∈ T₂} :=
        Sum.inl ⟨((b + y), t₁'), ⟨hmem2, ht₁'⟩⟩
      have hz1 : jointSum (d := d) (X + AA) AA T₁ T₂ z1 = a + f := by
        dsimp [z1, jointSum]
      have hz2 : jointSum (d := d) (X + AA) AA T₁ T₂ z2 = (b + y) + t₁' := by
        dsimp [z2, jointSum]
      have hEqZ : z1 = z2 := hJoin (by rw [hz1, hz2]; exact hval)
      nomatch hEqZ
    · have hval : a + f = b + g := hsum
      let z1 : Sum {p : V d × V d | p.1 ∈ X + AA ∧ p.2 ∈ T₁}
                   {p : V d × V d | p.1 ∈ AA ∧ p.2 ∈ T₂} :=
        Sum.inr ⟨(a, f), ⟨ha, hf2⟩⟩
      let z2 : Sum {p : V d × V d | p.1 ∈ X + AA ∧ p.2 ∈ T₁}
                   {p : V d × V d | p.1 ∈ AA ∧ p.2 ∈ T₂} :=
        Sum.inr ⟨(b, g), ⟨hb, hg2⟩⟩
      have hz1 : jointSum (d := d) (X + AA) AA T₁ T₂ z1 = a + f := by
        dsimp [z1, jointSum]
      have hz2 : jointSum (d := d) (X + AA) AA T₁ T₂ z2 = b + g := by
        dsimp [z2, jointSum]
      have hEqZ : z1 = z2 := hJoin (by rw [hz1, hz2]; exact hval)
      have hEqInr : (⟨(a, f), ⟨ha, hf2⟩⟩ : {p : V d × V d | p.1 ∈ AA ∧ p.2 ∈ T₂})
          = ⟨(b, g), ⟨hb, hg2⟩⟩ := Sum.inr.inj hEqZ
      have hca : a = b := by
        have h := congrArg (fun q : {p : V d × V d | p.1 ∈ AA ∧ p.2 ∈ T₂} => (q : V d × V d).1) hEqInr
        simpa using h
      have hcf : f = g := by
        have h := congrArg (fun q : {p : V d × V d | p.1 ∈ AA ∧ p.2 ∈ T₂} => (q : V d × V d).2) hEqInr
        simpa using h
      exact ⟨hca, hcf⟩

/-- Abstract regrouping: from a joint bijection of (X⊕AA, AA) with (T₁,T₂)
  and directness of X⊕AA, the tile (X+T₁)∪T₂ is complemented by AA. -/
lemma regrouping_IsComplement {d : ℕ} {T₁ T₂ X AA : Set (V d)}
    (hJoin : Function.Bijective (jointSum (d := d) (X + AA) AA T₁ T₂))
    (hDirect : ∀ ⦃a b x y : V d⦄, a ∈ AA → b ∈ AA → x ∈ X → y ∈ X →
      a + x = b + y → a = b ∧ x = y) :
    AddSubgroup.IsComplement AA ((X + T₁) ∪ T₂) := by
  classical
  rw [AddSubgroup.isComplement_iff_existsUnique]
  intro v
  rcases (hJoin.surjective v) with ⟨z, hz⟩
  cases z with
  | inl p =>
      have hpc : (p : V d × V d).1 ∈ X + AA := p.2.1
      have hpt : (p : V d × V d).2 ∈ T₁ := p.2.2
      have hzval : (p : V d × V d).1 + (p : V d × V d).2 = v := by
        simpa [jointSum] using hz
      rcases (Set.mem_add.mp hpc) with ⟨x0, hx0, a0, ha0, hxa0⟩
      let f0 : V d := x0 + (p : V d × V d).2
      have hf0 : f0 ∈ (X + T₁) ∪ T₂ := by
        rw [Set.mem_union]
        left
        exact Set.mem_add.mpr ⟨x0, hx0, (p : V d × V d).2, hpt, rfl⟩
      have hsum0 : a0 + f0 = v := by
        calc
          a0 + f0 = x0 + a0 + (p : V d × V d).2 := by dsimp [f0]; abel
          _ = (p : V d × V d).1 + (p : V d × V d).2 := by rw [hxa0]
          _ = v := hzval
      refine ⟨(⟨a0, ha0⟩, ⟨f0, hf0⟩), ?_, ?_⟩
      · change a0 + f0 = v
        exact hsum0
      · intro y hy
        apply Prod.ext
        · apply Subtype.ext
          have hsum : a0 + f0 = (y.1 : V d) + (y.2 : V d) := by
            calc
              a0 + f0 = v := hsum0
              _ = (y.1 : V d) + (y.2 : V d) := hy.symm
          have hpa := regrouping_unique (T₁ := T₁) (T₂ := T₂) hJoin.1 hDirect ha0 y.1.2 hf0 y.2.2 hsum
          exact hpa.1.symm
        · apply Subtype.ext
          have hsum : a0 + f0 = (y.1 : V d) + (y.2 : V d) := by
            calc
              a0 + f0 = v := hsum0
              _ = (y.1 : V d) + (y.2 : V d) := hy.symm
          have hpa := regrouping_unique (T₁ := T₁) (T₂ := T₂) hJoin.1 hDirect ha0 y.1.2 hf0 y.2.2 hsum
          exact hpa.2.symm
  | inr p =>
      have hpc : (p : V d × V d).1 ∈ AA := p.2.1
      have hpt : (p : V d × V d).2 ∈ T₂ := p.2.2
      have hzval : (p : V d × V d).1 + (p : V d × V d).2 = v := by
        simpa [jointSum] using hz
      let f0 : V d := (p : V d × V d).2
      have hf0 : f0 ∈ (X + T₁) ∪ T₂ := by
        rw [Set.mem_union]
        right
        exact hpt
      refine ⟨(⟨(p : V d × V d).1, hpc⟩, ⟨f0, hf0⟩), ?_, ?_⟩
      · change (p : V d × V d).1 + f0 = v
        exact hzval
      · intro y hy
        apply Prod.ext
        · apply Subtype.ext
          have hsum : (p : V d × V d).1 + f0 = (y.1 : V d) + (y.2 : V d) := by
            calc
              (p : V d × V d).1 + f0 = v := hzval
              _ = (y.1 : V d) + (y.2 : V d) := hy.symm
          have hpa := regrouping_unique (T₁ := T₁) (T₂ := T₂) hJoin.1 hDirect hpc y.1.2 hf0 y.2.2 hsum
          exact hpa.1.symm
        · apply Subtype.ext
          have hsum : (p : V d × V d).1 + f0 = (y.1 : V d) + (y.2 : V d) := by
            calc
              (p : V d × V d).1 + f0 = v := hzval
              _ = (y.1 : V d) + (y.2 : V d) := hy.symm
          have hpa := regrouping_unique (T₁ := T₁) (T₂ := T₂) hJoin.1 hDirect hpc y.1.2 hf0 y.2.2 hsum
          exact hpa.2.symm

end LevelD

-- ============================================================
-- PART E : forward direction (π-specific)
-- ============================================================

section LevelE
variable {G : Type*} [AddCommGroup G] {d : ℕ}
variable (π : V d →+ G) (D : Set (V d))
variable (hD : AddSubgroup.IsComplement D (π.ker : Set (V d)))
variable (hπ : Function.Surjective π)

/-- X ⊆ NV -/
lemma zimg_sub_NV {N : ℕ} (S : Set (V d)) : zimg N S ⊆ NV d N := by
  intro x hx
  rw [mem_zimg] at hx
  rcases hx with ⟨s, hs, rfl⟩
  exact smul_mem_NV s

/-- sum of two NV-subsets stays in NV -/
lemma add_sub_NV {N : ℕ} {S T : Set (V d)} (hS : S ⊆ NV d N) (hT : T ⊆ NV d N) :
    S + T ⊆ NV d N := by
  intro x hx
  rcases Set.mem_add.mp hx with ⟨s, hs, t, ht, rfl⟩
  have hs' : s ∈ (NV_subgroup d N : Set (V d)) := hS hs
  have ht' : t ∈ (NV_subgroup d N : Set (V d)) := hT ht
  exact (NV_subgroup d N).add_mem hs' ht'

/-- 0 ∈ Ã when 0 ∈ A -/
lemma zero_mem_scaled_preimage {N : ℕ} {A : Set G} (h0A : (0 : G) ∈ A) :
    (0 : V d) ∈ zimg N (π ⁻¹' A) := by
  exact mem_zimg.mpr ⟨0, by rw [Set.mem_preimage]; simpa using h0A, by simp⟩

/-- directness of X ⊕ AA (both scaled) -/
lemma scaled_preimage_add_direct {N : ℕ} (hN : 0 < N)
    (hD : AddSubgroup.IsComplement D (π.ker : Set (V d)))
    (hπ : Function.Surjective π) {A F : Set G}
    (hAF : AddSubgroup.IsComplement A F)
    ⦃a b x y : V d⦄ (ha : a ∈ zimg N (π ⁻¹' A)) (hb : b ∈ zimg N (π ⁻¹' A))
    (hx : x ∈ zimg N ((π ⁻¹' (F \ {0})) ∩ D))
    (hy : y ∈ zimg N ((π ⁻¹' (F \ {0})) ∩ D))
    (hsum : a + x = b + y) : a = b ∧ x = y := by
  rw [mem_zimg] at ha hb hx hy
  rcases ha with ⟨u, hu, hua⟩
  rcases hb with ⟨v, hv, hvb⟩
  rcases hx with ⟨p, hp, hxp⟩
  rcases hy with ⟨q, hq, hyq⟩
  rw [Set.mem_inter_iff] at hp hq
  have hpre : u + p = v + q := by
    apply zsmul_injective_pointwise (N := N) hN
    calc
      (N : ℤ) • (u + p) = (N : ℤ) • u + (N : ℤ) • p := by rw [smul_add_pointwise]
      _ = a + x := by rw [hua, hxp]
      _ = b + y := hsum
      _ = (N : ℤ) • v + (N : ℤ) • q := by rw [hvb, hyq]
      _ = (N : ℤ) • (v + q) := by rw [smul_add_pointwise]
  have hsub : u - v = q - p := by
    calc
      u - v = (u + p) - (v + p) := by abel
      _ = (v + q) - (v + p) := by rw [hpre]
      _ = q - p := by abel
  have hπin : π (u - v) ∈ (A - A) ∩ (F - F) := by
    constructor
    · rw [Set.mem_sub]
      exact Set.mem_sub.mpr ⟨π u, Set.mem_preimage.mp hu, π v, Set.mem_preimage.mp hv,
        (map_sub π u v).symm⟩
    · rw [Set.mem_sub]
      have hqF : π q ∈ F := ((Set.mem_sdiff (π q)).mp (Set.mem_preimage.mp hq.1)).1
      have hpF : π p ∈ F := ((Set.mem_sdiff (π p)).mp (Set.mem_preimage.mp hp.1)).1
      have heq : π q - π p = π (u - v) := by
        calc
          π q - π p = π (q - p) := (map_sub π q p).symm
          _ = π (u - v) := by rw [← hsub]
      exact Set.mem_sub.mpr ⟨π q, hqF, π p, hpF, heq⟩
  have hπ0 : π (u - v) = 0 := by
    have hmem := complement_AA_inter_FF hAF hπin
    simpa using hmem
  have hqpk : q - p ∈ (π.ker : Set (V d)) := by
    rw [ker_coe_mem_iff π]
    calc
      π (q - p) = π (u - v) := by rw [← hsub]
      _ = 0 := hπ0
  have hqp : q = p := by
    have hπpq : π p = π q := by
      have hπqpe : π (q - p) = 0 := (ker_coe_mem_iff π (q - p)).mp hqpk
      have hπ' : π q - π p = 0 := by
        rw [← map_sub π q p]
        exact hπqpe
      exact (sub_eq_zero.mp hπ').symm
    exact (D_unique_of_pi_eq (G := G) π D hD (u₁ := p) (u₂ := q) hp.2 hq.2 hπpq).symm
  have huv : u = v := by
    have hupvp : u + p = v + p := by rw [hpre, hqp]
    exact add_right_cancel hupvp
  constructor
  · calc
      a = (N : ℤ) • u := hua
      _ = (N : ℤ) • v := by rw [huv]
      _ = b := hvb.symm
  · calc
      x = (N : ℤ) • p := hxp
      _ = (N : ℤ) • q := by rw [hqp]
      _ = y := hyq.symm
end LevelE

section LevelE2
variable {G : Type*} [AddCommGroup G] {d : ℕ}
variable (π : V d →+ G) (D : Set (V d))
variable (hD : AddSubgroup.IsComplement D (π.ker : Set (V d)))
variable (hπ : Function.Surjective π)

/-- S0 = preimage of {0} in D, maps into NL -/
lemma zimg_zero_preimage_sub_NL {N : ℕ} :
    zimg N ((π ⁻¹' ({0} : Set G)) ∩ D) ⊆ NL d N π.ker := by
  intro x hx
  rw [mem_zimg] at hx
  rcases hx with ⟨w, hw, rfl⟩
  rw [Set.mem_inter_iff] at hw
  have hwker : w ∈ (π.ker : Set (V d)) := by
    rw [ker_coe_mem_iff π]
    have h : π w ∈ ({0} : Set G) := Set.mem_preimage.mp hw.1
    simpa using h
  rw [NL, mem_zimg]
  exact ⟨w, hwker, rfl⟩

/-- (X+AA) ∪ AA = NV -/
lemma partC_union {N : ℕ} (hN : 0 < N)
    (hD : AddSubgroup.IsComplement D (π.ker : Set (V d)))
    (hπ : Function.Surjective π)
    {A F : Set G} (hAF : AddSubgroup.IsComplement A F)
    (h0F : (0 : G) ∈ F) :
    (zimg N ((π ⁻¹' (F \ {0})) ∩ D) + zimg N (π ⁻¹' A)) ∪ zimg N (π ⁻¹' A) = NV d N := by
  apply le_antisymm
  · intro x hx
    rcases hx with hx | hx
    · rcases Set.mem_add.mp hx with ⟨x0, hx0, a, ha, hsum⟩
      have hx0NV : x0 ∈ NV d N := by
        rw [mem_zimg] at hx0
        rcases hx0 with ⟨s, hs, rfl⟩
        exact smul_mem_NV s
      have haNV : a ∈ NV d N := by
        rw [mem_zimg] at ha
        rcases ha with ⟨s, hs, rfl⟩
        exact smul_mem_NV s
      rw [← hsum]
      exact (NV_subgroup d N).add_mem hx0NV haNV
    · rw [mem_zimg] at hx
      rcases hx with ⟨s, hs, rfl⟩
      exact smul_mem_NV s
  · intro v hv
    have hdec := image_IsComplement_unique (d := d) (N := N) hN
      (pullback_IsComplement π D hD hπ hAF)
    have hv' : v ∈ zimg N (π ⁻¹' A) + zimg N ((π ⁻¹' F) ∩ D) := by
      rw [hdec.1]
      exact hv
    rcases (Set.mem_add.mp hv') with ⟨a, ha, w, hw, hsum⟩
    have hcase := zimg_preimageF_mem_cases π D h0F (N := N) (x := w) hw
    rcases hcase with hwX | hwZ
    · left
      exact Set.mem_add.mpr ⟨w, hwX, a, ha, by simpa [add_comm] using hsum⟩
    · right
      have hwNL : w ∈ NL d N π.ker := zimg_zero_preimage_sub_NL π D (N := N) hwZ
      have hav : a + w ∈ zimg N (π ⁻¹' A) := by
        have this : a + w ∈ zimg N (π ⁻¹' A) + NL d N π.ker :=
          Set.mem_add.mpr ⟨a, ha, w, hwNL, rfl⟩
        rwa [scaled_preimage_periodic π A N] at this
      rwa [← hsum]
/-- (X+AA) and AA are disjoint -/
lemma partC_disjoint {N : ℕ} (hN : 0 < N)
    (hD : AddSubgroup.IsComplement D (π.ker : Set (V d)))
    (hπ : Function.Surjective π)
    {A F : Set G} (hAF : AddSubgroup.IsComplement A F) (h0F : (0 : G) ∈ F) :
    Disjoint (zimg N ((π ⁻¹' (F \ {0})) ∩ D) + zimg N (π ⁻¹' A)) (zimg N (π ⁻¹' A)) := by
  rw [Set.disjoint_left]
  intro v hv1 hv2
  rcases Set.mem_add.mp hv1 with ⟨x, hxX, a, ha, hsum⟩
  have hx : x = v - a := by
    calc
      x = x + a - a := by abel
      _ = v - a := by rw [hsum]
  have hxAAsub : x ∈ zimg N (π ⁻¹' A - π ⁻¹' A) := by
    rw [hx]
    rw [zimg_sub N (π ⁻¹' A) (π ⁻¹' A)]
    rw [Set.mem_sub]
    exact Set.mem_sub.mpr ⟨v, hv2, a, ha, rfl⟩
  rw [mem_zimg] at hxAAsub hxX
  rcases hxAAsub with ⟨w1, hw1, hxw1⟩
  rcases hxX with ⟨w2, hw2, hxw2⟩
  have hww : w1 = w2 := zsmul_injective_pointwise (N := N) hN (hxw1.symm.trans hxw2)
  have hw2AA : w2 ∈ π ⁻¹' A - π ⁻¹' A := by
    rwa [hww] at hw1
  have hπwAA : π w2 ∈ A - A := by
    rw [Set.mem_sub] at hw2AA
    rcases hw2AA with ⟨u, hu, v', hv', hsum'⟩
    rw [Set.mem_sub]
    refine ⟨π u, ?_, π v', ?_, ?_⟩
    · exact Set.mem_preimage.mp hu
    · exact Set.mem_preimage.mp hv'
    · calc
        π u - π v' = π (u - v') := by rw [map_sub]
        _ = π w2 := by rw [← hsum']
  have hπwF : π w2 ∈ F \ {0} := by
    rw [Set.mem_inter_iff] at hw2
    exact Set.mem_preimage.mp hw2.1
  exact (Set.disjoint_left.mp (complement_AA_inter_F hAF h0F)) hπwAA hπwF
end LevelE2

/-- (X+AA) is NL-periodic -/
lemma partC_periodic {G : Type*} [AddCommGroup G] {d : ℕ}
    (π : V d →+ G) (D : Set (V d)) (N : ℕ) (A F : Set G) :
    (zimg N ((π ⁻¹' (F \ {0})) ∩ D) + zimg N (π ⁻¹' A)) + NL d N π.ker
        = zimg N ((π ⁻¹' (F \ {0})) ∩ D) + zimg N (π ⁻¹' A) := by
  calc
    (zimg N ((π ⁻¹' (F \ {0})) ∩ D) + zimg N (π ⁻¹' A)) + NL d N π.ker
        = zimg N ((π ⁻¹' (F \ {0})) ∩ D) + (zimg N (π ⁻¹' A) + NL d N π.ker) := by
            rw [add_assoc]
    _ = zimg N ((π ⁻¹' (F \ {0})) ∩ D) + zimg N (π ⁻¹' A) := by
            rw [scaled_preimage_periodic π A N]

section LevelF

/-- Forward: a complement of F in G lifts to a complement of F' in V. -/
lemma forward_tile {G : Type*} [AddCommGroup G] {d : ℕ}
    (π : V d →+ G) (hπ : Function.Surjective π)
    (D : Set (V d)) (hD : AddSubgroup.IsComplement D (π.ker : Set (V d)))
    {N : ℕ} (hN : 0 < N) {T₁ T₂ : Set (V d)}
    (hPair : ∀ C₁ C₂ : Set (V d),
      ((0 : V d) ∈ C₁ ∪ C₂ ∧ Function.Bijective (jointSum (d := d) C₁ C₂ T₁ T₂)) ↔
      (C₁ ∪ C₂ = NV d N ∧ Disjoint C₁ C₂ ∧ C₁ + NL d N π.ker = C₁ ∧ C₂ + NL d N π.ker = C₂))
    {A F : Set G} (hAF : AddSubgroup.IsComplement A F) (h0A : (0 : G) ∈ A)
    (h0F : (0 : G) ∈ F) :
    AddSubgroup.IsComplement (zimg N (π ⁻¹' A))
      ((zimg N ((π ⁻¹' (F \ {0})) ∩ D) + T₁) ∪ T₂) := by
  let X : Set (V d) := zimg N ((π ⁻¹' (F \ {0})) ∩ D)
  let AA : Set (V d) := zimg N (π ⁻¹' A)
  have hUn : X + AA ∪ AA = NV d N := by
    dsimp [X, AA]
    exact partC_union π D (N := N) hN hD hπ hAF h0F
  have hDisj : Disjoint (X + AA) AA := by
    dsimp [X, AA]
    exact partC_disjoint π D (N := N) hN hD hπ hAF h0F
  have hPer1 : (X + AA) + NL d N π.ker = X + AA := by
    dsimp [X, AA]
    exact partC_periodic π D N A F
  have hPer2 : AA + NL d N π.ker = AA := by
    dsimp [AA]
    exact scaled_preimage_periodic π A N
  have hPair12 := (hPair (X + AA) AA).mpr ⟨hUn, hDisj, hPer1, hPer2⟩
  have hJoin : Function.Bijective (jointSum (d := d) (X + AA) AA T₁ T₂) := hPair12.2
  have hDirect : ∀ ⦃a b x y : V d⦄, a ∈ AA → b ∈ AA → x ∈ X → y ∈ X →
      a + x = b + y → a = b ∧ x = y := by
    intro a b x y ha hb hx hy hsum
    dsimp [X, AA] at ha hb hx hy
    exact scaled_preimage_add_direct π D (N := N) hN hD hπ hAF (a := a) (b := b) (x := x) (y := y)
      ha hb hx hy hsum
  have hreg := regrouping_IsComplement (T₁ := T₁) (T₂ := T₂) (X := X) (AA := AA) hJoin hDirect
  simpa [X, AA] using hreg

end LevelF


/-!
# Geometric disjointness of the rigid-pair tooth tiles

The `tile0` (tiling reduction) argument needs, for the concrete rigid-pair
tiles `T_σ = toothTile w σ` with the common dilation `N = N0 d r`, the fact that
differences of cells of two such tiles that lie in `NV = N·ℤ^d` must in fact lie
in `NL = N·L`:

    (toothTile w σ − toothTile w σ') ∩ NV d N ⊆ NL d N L        (for all σ,σ')

Geometrically: every cell of every `toothTile` is a multiple of `N` plus a
canonical box remainder, and two cells congruent modulo `N` differ by `N` times
a difference of `L`-elements, hence lie in `NL`.

This is the missing geometric fact that lets the backward direction of the
tiling reduction go through (it guarantees that `X + T₁` is disjoint from `T₂`
and that `X + T₁` is collision-free for every `X = N·S_F ⊆ NV` with
`X ∩ NL = {0}`), independently of the forward direction.

Status: PROVEN. `geometric_disjointness` compiles (595 lines, no placeholders).
Proof: 3×3 case analysis over the body / basis-bump / extra-bump decomposition
(`toothTile_mem_cases`) of both cells, closing each square with the coordinate
helpers below; extra bumps use `toothDent_mem_box` / `toothDent_coord_ge_five'` /
`toothDent_disjoint_of_ne`, basis bumps use the xhole-coordinate profile, and the
dents of the σ-vs-σ' sides are split via the exclusion hypotheses of the body
cells (with `hwL` for the surviving ±N·w_l differences).
-/

/-- a multiple of N is zero when it lies strictly between −N and N -/
lemma eq_zero_of_dvd_of_lt_int {N : ℕ} {a : ℤ} (hNpos : 0 < N)
    (hdvd : (N : ℤ) ∣ a) (hlt : a < (N : ℤ)) (hnlt : -(N : ℤ) < a) : a = 0 := by
  rcases hdvd with ⟨k, hk⟩
  by_cases hk0 : k = 0
  · rw [hk, hk0]
    simp
  · exfalso
    have hkabs : 1 ≤ |k| := Int.one_le_abs hk0
    have hNnonneg : (0 : ℤ) ≤ (N : ℤ) := by exact_mod_cast (le_of_lt hNpos)
    have hNle : (N : ℤ) ≤ |k| * (N : ℤ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_of_nonneg_right hkabs hNnonneg)
    have hbound : |a| < (N : ℤ) := by
      rw [abs_lt]
      exact ⟨hnlt, hlt⟩
    have habs : |a| = |k| * (N : ℤ) := by
      rw [hk]
      rw [abs_mul, abs_of_nonneg hNnonneg]
      ring
    omega

/-- two box cells congruent modulo N are equal -/
lemma box_eq_of_mem_NV_diff {d N : ℕ} (hNpos : 0 < N) {x y : V d}
    (hx : x ∈ box d N) (hy : y ∈ box d N)
    (hNV : x - y ∈ NV d N) : x = y := by
  apply funext
  intro i
  have hdiv : (N : ℤ) ∣ x i - y i := by
    simpa using ((mem_NV_iff.mp hNV) i)
  have hx1 : (0 : ℤ) ≤ x i ∧ x i < (N : ℤ) := hx i
  have hy1 : (0 : ℤ) ≤ y i ∧ y i < (N : ℤ) := hy i
  have hlt : x i - y i < (N : ℤ) := by omega
  have hnlt : -(N : ℤ) < x i - y i := by omega
  have hz : x i - y i = 0 := eq_zero_of_dvd_of_lt_int hNpos hdiv hlt hnlt
  exact sub_eq_zero.mp hz

/-- N0 is positive -/
lemma N0_pos {d r : ℕ} : 0 < N0 d r := by
  have h := N0_ge_seven (d := d) (r := r)
  omega

/-- a tooth index forces a positive number of generators -/
lemma fin_pos {r : ℕ} (l : Fin r) : 0 < r := by
  by_contra h
  have hr0 : r = 0 := by omega
  subst r
  exact Fin.elim0 l

/-- coordinate of a basis bump cell -/
lemma bb_coord {d N : ℕ} {i : Fin d} {v : V d}
    (hv : v = (N : ℤ) • eb d i + xhole (d := d) i) (j : Fin d) :
    v j = (N : ℤ) * (if j = i then (1 : ℤ) else 0) + (if j = i then (2 : ℤ) else (4 : ℤ)) := by
  rw [hv]
  by_cases hji : j = i
  · subst j
    simp [Pi.add_apply, eb_apply, xhole_self]
  · have hij : i ≠ j := by
      intro h
      exact hji h.symm
    simp [Pi.add_apply, eb_apply_ne hij, xhole_other hij, hji]

/-- coordinate of a basis bump cell: own coordinate is N+2 -/
lemma bb_coord_self {d N : ℕ} {i : Fin d} {v : V d}
    (hv : v = (N : ℤ) • eb d i + xhole (d := d) i) : v i = (N : ℤ) + 2 := by
  rw [bb_coord (N := N) hv i]
  simp

/-- coordinate of a basis bump cell: other coordinates are 4 -/
lemma bb_coord_other {d N : ℕ} {i j : Fin d} (hij : i ≠ j) {v : V d}
    (hv : v = (N : ℤ) • eb d i + xhole (d := d) i) : v j = (4 : ℤ) := by
  have hji : ¬ j = i := by
    intro hj
    exact hij hj.symm
  rw [bb_coord (N := N) hv j]
  simp [hji]

/-- membership in a tooth bump gives its dent decomposition -/
lemma toothBump_mem_iff {d r : ℕ} (w : Fin r → V d) (σ : Fin 2) (l : Fin r) (v : V d) :
    v ∈ toothBump (d := d) w σ l ↔
      ∃ d0 : V d, d0 ∈ toothDent (d := d) (V0 d r) (sep r) r σ l ∧
        v = (N0 d r : ℤ) • w l + d0 := by
  constructor
  · intro hv
    rw [toothBump] at hv
    rw [Set.mem_image] at hv
    rcases hv with ⟨d0, hd, hvd⟩
    exact ⟨d0, hd, hvd.symm⟩
  · intro h
    rcases h with ⟨d0, hd, hvd⟩
    rw [toothBump]
    rw [Set.mem_image]
    exact ⟨d0, hd, hvd.symm⟩

/-- dent cells have coordinates in [0,N0) -/
lemma toothDent_coord_in_box {d r : ℕ} (σ : Fin 2) (l : Fin r) (x : V d)
    (hx : x ∈ toothDent (d := d) (V0 d r) (sep r) r σ l) (i : Fin d) :
    (0 : ℤ) ≤ x i ∧ x i < (N0 d r : ℤ) := by
  exact (toothDent_mem_box (fin_pos l) σ l x hx) i

/-- equal constants: `a = c` from `N ∣ a - c` under box bounds -/
lemma coord_eq_of_dvd_const {N : ℕ} (hN : 0 < N) {a : ℤ} {c : ℤ}
    (ha0 : 0 ≤ a) (hac : a < (N : ℤ)) (hc : a - c < (N : ℤ)) (hca : -(N : ℤ) < a - c)
    (hdvd : (N : ℤ) ∣ a - c) : a = c := by
  have hz : a - c = 0 := eq_zero_of_dvd_of_lt_int hN hdvd hc hca
  exact sub_eq_zero.mp hz

/-- dent coordinates are at least 5 -/
lemma toothDent_coord_ge_five' {d r : ℕ} (σ : Fin 2) (l : Fin r) (x : V d)
    (hx : x ∈ toothDent (d := d) (V0 d r) (sep r) r σ l) (i : Fin d) :
    (5 : ℤ) ≤ x i := by
  exact toothDent_coord_ge_five σ l x hx i

/-- xhole cells lie in the dent set -/
lemma xhole_mem_Dset {d : ℕ} (i : Fin d) : xhole (d := d) i ∈ (Dset d : Set (V d)) := by
  rw [Dset_mem]
  exact ⟨i, rfl⟩
/-! ### shared divisibility arithmetic -/

/-- N ∣ t − (N·w + d)  implies  N ∣ t − d  (cancel the N·w) -/
lemma dvd_of_dvd_sub_add_mul {N t d w : ℤ} (h : N ∣ t - (N * w + d)) : N ∣ t - d := by
  rcases h with ⟨k, hk⟩
  refine ⟨k + w, ?_⟩
  calc
    t - d = (t - (N * w + d)) + N * w := by ring
    _ = N * k + N * w := by rw [hk]
    _ = N * (k + w) := by ring

/-- N ∣ (N·w + d) − u  implies  N ∣ d − u  (cancel the N·w) -/
lemma dvd_of_dvd_add_mul_sub {N d u w : ℤ} (h : N ∣ N * w + d - u) : N ∣ d - u := by
  rcases h with ⟨k, hk⟩
  refine ⟨k - w, ?_⟩
  calc
    d - u = (N * w + d - u) - N * w := by ring
    _ = N * k - N * w := by rw [hk]
    _ = N * (k - w) := by ring

/-- xhole coordinate values are 2 or 4 -/
lemma xhole_two_or_four {d : ℕ} (i j : Fin d) :
    xhole (d := d) i j = (2 : ℤ) ∨ xhole (d := d) i j = (4 : ℤ) := by
  by_cases h : j = i
  · subst j
    left
    exact xhole_self i
  · right
    exact xhole_other (d := d) (by
      intro hj
      exact h hj.symm)

/-- a difference of two values from {2,4} divisible by N > 4 is zero -/
lemma two_four_sub_eq {N : ℕ} (hN : 4 < N) {a b : ℤ}
    (ha : a = 2 ∨ a = 4) (hb : b = 2 ∨ b = 4) (h : (N : ℤ) ∣ a - b) : a = b := by
  have hbnd : |a - b| ≤ (2 : ℤ) := by
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]
  have hless : |a - b| < (N : ℤ) := lt_of_le_of_lt hbnd (by
    have hN2 : (2 : ℕ) < N := by omega
    exact_mod_cast hN2)
  have hlt : a - b < (N : ℤ) := (abs_lt.mp hless).2
  have hnlt : -(N : ℤ) < a - b := (abs_lt.mp hless).1
  have hz : a - b = 0 := eq_zero_of_dvd_of_lt_int (by omega) h hlt hnlt
  exact sub_eq_zero.mp hz

/-- basis-bump cells congruent mod N have equal xhole remainders -/
lemma basisBump_dvd_xhole {d N : ℕ} (hN : 4 < N) {t u : V d} {i₁ i₂ : Fin d} (j : Fin d)
    (ht : t = (N : ℤ) • eb d i₁ + xhole (d := d) i₁)
    (hu : u = (N : ℤ) • eb d i₂ + xhole (d := d) i₂)
    (hdiv : (N : ℤ) ∣ (t - u) j) : xhole (d := d) i₁ j = xhole (d := d) i₂ j := by
  let a1 : ℤ := if j = i₁ then (1 : ℤ) else 0
  let a2 : ℤ := if j = i₂ then (1 : ℤ) else 0
  let x1 : ℤ := xhole (d := d) i₁ j
  let x2 : ℤ := xhole (d := d) i₂ j
  have htj : t j = (N : ℤ) * a1 + x1 := by
    dsimp [a1, x1]
    exact bb_coord (N := N) ht j
  have huj : u j = (N : ℤ) * a2 + x2 := by
    dsimp [a2, x2]
    exact bb_coord (N := N) hu j
  have hxdiv : (N : ℤ) ∣ x1 - x2 := by
    rcases hdiv with ⟨m, hm⟩
    refine ⟨m - a1 + a2, ?_⟩
    calc
      x1 - x2 = (t j - u j) - (N : ℤ) * (a1 - a2) := by
        rw [htj, huj]
        ring
      _ = (N : ℤ) * m - (N : ℤ) * (a1 - a2) := by
        have hm' : t j - u j = (N : ℤ) * m := by
          simpa using hm
        rw [hm']
      _ = (N : ℤ) * (m - a1 + a2) := by ring
  have hx : x1 = x2 := two_four_sub_eq hN (by dsimp [x1]; exact xhole_two_or_four i₁ j)
    (by dsimp [x2]; exact xhole_two_or_four i₂ j) (by simpa [x1, x2] using hxdiv)
  simpa [x1, x2] using hx

/-- (B,B): two basis-bump cells congruent mod N are equal; difference 0 ∈ NL -/
private lemma core_BB {d r : ℕ} {L : AddSubgroup (V d)} {t u : V d}
    (i₁ : Fin d) (ht : t = (N0 d r : ℤ) • eb d i₁ + xhole (d := d) i₁)
    (i₂ : Fin d) (hu : u = (N0 d r : ℤ) • eb d i₂ + xhole (d := d) i₂)
    (hNV : t - u ∈ NV d (N0 d r)) : t - u ∈ NL d (N0 d r) L := by
  have hN : 4 < N0 d r := by
    have h7 := N0_ge_seven (d := d) (r := r)
    omega
  have hEq : t = u := by
    apply funext
    intro j
    have hdiv : (N0 d r : ℤ) ∣ (t - u) j := (mem_NV_iff.mp hNV) j
    have hx := basisBump_dvd_xhole (N := N0 d r) hN (j := j) ht hu hdiv
    -- xhole i₁ j = xhole i₂ j for all j, so i₁ = i₂ and the cells agree at j
    have hi : i₁ = i₂ := xhole_injective (funext (fun k => basisBump_dvd_xhole (N := N0 d r) hN (j := k) ht hu
      ((mem_NV_iff.mp hNV) k)))
    subst i₂
    calc
      t j = (N0 d r : ℤ) * (if j = i₁ then (1 : ℤ) else 0) + (if j = i₁ then (2 : ℤ) else (4 : ℤ)) := by
        rw [bb_coord (N := N0 d r) ht j]
      _ = u j := by
        rw [bb_coord (N := N0 d r) hu j]
  have hz : t - u = 0 := by rw [hEq]; simp
  rw [hz]
  exact zero_mem_NL (N := N0 d r) L

/-- N ∣ N·w + a  implies  N ∣ a -/
lemma dvd_of_dvd_add_mul {N a w : ℤ} (h : N ∣ N * w + a) : N ∣ a := by
  rcases h with ⟨k, hk⟩
  refine ⟨k - w, ?_⟩
  calc
    a = (N * w + a) - N * w := by ring
    _ = N * k - N * w := by rw [hk]
    _ = N * (k - w) := by ring

/-- a body coordinate c (c ∈ {2,4}) is forced equal to its remainder -/
lemma body_dvd_const {d N : ℕ} (hN : 0 < N) {t : V d} (ht : t ∈ box d N) (j : Fin d)
    (c : ℤ) (hc : 0 ≤ c) (hc4 : c < (N : ℤ)) (hdiv : (N : ℤ) ∣ t j - c) : t j = c := by
  have ht1 : (0 : ℤ) ≤ t j ∧ t j < (N : ℤ) := ht j
  have hlt : t j - c < (N : ℤ) := by omega
  have hnlt : -(N : ℤ) < t j - c := by omega
  have hz : t j - c = 0 := eq_zero_of_dvd_of_lt_int hN hdiv hlt hnlt
  exact sub_eq_zero.mp hz

/-- N ≥ 5 bound for the concrete dilation -/
lemma N0_gt_four {d r : ℕ} : 4 < N0 d r := by
  have h7 := N0_ge_seven (d := d) (r := r)
  omega

/-- (A,A): two body cells congruent mod N are equal; difference 0 ∈ NL -/
private lemma core_AA {d r : ℕ} {L : AddSubgroup (V d)} {t u : V d}
    (ht : t ∈ box d (N0 d r)) (hu : u ∈ box d (N0 d r))
    (hNV : t - u ∈ NV d (N0 d r)) : t - u ∈ NL d (N0 d r) L := by
  have hEq : t = u := box_eq_of_mem_NV_diff (N := N0 d r) N0_pos ht hu hNV
  have hz : t - u = 0 := by rw [hEq]; simp
  rw [hz]
  exact zero_mem_NL (N := N0 d r) L

/-- (A,B): a body cell congruent to a basis-bump cell mod N is a basis hole -
  a contradiction (body cells avoid the dent set) -/
private lemma core_AB {d r : ℕ} {L : AddSubgroup (V d)} {t u : V d}
    (ht : t ∈ box d (N0 d r)) (htD : t ∉ (Dset d : Set (V d)))
    (i₁ : Fin d) (hu : u = (N0 d r : ℤ) • eb d i₁ + xhole (d := d) i₁)
    (hNV : t - u ∈ NV d (N0 d r)) : t - u ∈ NL d (N0 d r) L := by
  exfalso
  have hN4 : 4 < N0 d r := N0_gt_four (d := d) (r := r)
  have hEq : t = xhole (d := d) i₁ := by
    apply funext
    intro j
    by_cases hji : j = i₁
    · subst j
      have hdiv : (N0 d r : ℤ) ∣ (t - u) i₁ := (mem_NV_iff.mp hNV) i₁
      have hui : u i₁ = (N0 d r : ℤ) + 2 := bb_coord_self hu
      have hdiv' : (N0 d r : ℤ) ∣ t i₁ - (2 : ℤ) := by
        have hd : (N0 d r : ℤ) ∣ t i₁ - ((N0 d r : ℤ) + 2) := by simpa [hui] using hdiv
        exact dvd_of_dvd_sub_add_mul (N := (N0 d r : ℤ)) (t := t i₁) (d := (2 : ℤ)) (w := 1)
          (by simpa using hd)
      have htwo : t i₁ = (2 : ℤ) := body_dvd_const (N := N0 d r) N0_pos ht i₁ (2 : ℤ) (by norm_num)
        (by exact_mod_cast (by omega)) hdiv'
      simpa [htwo, xhole_self]
    · have hdiv : (N0 d r : ℤ) ∣ (t - u) j := (mem_NV_iff.mp hNV) j
      have huj : u j = (4 : ℤ) := bb_coord_other (by intro h; exact hji h.symm) hu
      have hdiv' : (N0 d r : ℤ) ∣ t j - (4 : ℤ) := by simpa [huj] using hdiv
      have hfour : t j = (4 : ℤ) := body_dvd_const (N := N0 d r) N0_pos ht j (4 : ℤ) (by norm_num)
        (by exact_mod_cast (by omega)) hdiv'
      simpa [hfour, xhole_other (by intro h; exact hji h.symm)]
  have htD' : t ∈ (Dset d : Set (V d)) := by
    rw [hEq]
    exact xhole_mem_Dset i₁
  exact htD htD'

/-- a ∣ b implies a ∣ -b -/
lemma dvd_neg_left {a b : ℤ} (h : a ∣ b) : a ∣ -b := by
  rcases h with ⟨k, hk⟩
  exact ⟨-k, by rw [hk]; ring⟩

/-- (B,A): symmetric to (A,B) -/
private lemma core_BA {d r : ℕ} {L : AddSubgroup (V d)} {t u : V d}
    (i₁ : Fin d) (ht : t = (N0 d r : ℤ) • eb d i₁ + xhole (d := d) i₁)
    (hu : u ∈ box d (N0 d r)) (huD : u ∉ (Dset d : Set (V d)))
    (hNV : t - u ∈ NV d (N0 d r)) : t - u ∈ NL d (N0 d r) L := by
  exfalso
  have hN4 : 4 < N0 d r := N0_gt_four (d := d) (r := r)
  have hEq : u = xhole (d := d) i₁ := by
    apply funext
    intro j
    by_cases hji : j = i₁
    · subst j
      have hdiv : (N0 d r : ℤ) ∣ (t - u) i₁ := (mem_NV_iff.mp hNV) i₁
      have hti : t i₁ = (N0 d r : ℤ) + 2 := bb_coord_self ht
      have hdiv' : (N0 d r : ℤ) ∣ u i₁ - (2 : ℤ) := by
        have hd : (N0 d r : ℤ) ∣ ((N0 d r : ℤ) + 2) - u i₁ := by simpa [hti] using hdiv
        have hdiv2 : (N0 d r : ℤ) ∣ 2 - u i₁ :=
          dvd_of_dvd_add_mul_sub (N := (N0 d r : ℤ)) (d := (2 : ℤ)) (u := u i₁) (w := 1)
          (by simpa using hd)
        have hdivneg : (N0 d r : ℤ) ∣ -(2 - u i₁) := dvd_neg_left hdiv2
        have hrw : -(2 - u i₁) = u i₁ - 2 := by ring
        simpa [hrw] using hdivneg
      have htwo : u i₁ = (2 : ℤ) := body_dvd_const (N := N0 d r) N0_pos hu i₁ (2 : ℤ) (by norm_num)
        (by exact_mod_cast (by omega)) hdiv'
      simpa [htwo, xhole_self]
    · have hdiv : (N0 d r : ℤ) ∣ (t - u) j := (mem_NV_iff.mp hNV) j
      have htj : t j = (4 : ℤ) := bb_coord_other (by intro h; exact hji h.symm) ht
      have hdiv' : (N0 d r : ℤ) ∣ u j - (4 : ℤ) := by
        have hd : (N0 d r : ℤ) ∣ (4 : ℤ) - u j := by simpa [htj] using hdiv
        have hdivneg : (N0 d r : ℤ) ∣ -(4 - u j) := dvd_neg_left hd
        have hrw : -(4 - u j) = u j - 4 := by ring
        simpa [hrw] using hdivneg
      have hfour : u j = (4 : ℤ) := body_dvd_const (N := N0 d r) N0_pos hu j (4 : ℤ) (by norm_num)
        (by exact_mod_cast (by omega)) hdiv'
      simpa [hfour, xhole_other (by intro h; exact hji h.symm)]
  have hu' : u ∈ (Dset d : Set (V d)) := by
    rw [hEq]
    exact xhole_mem_Dset i₁
  exact huD hu'

/-- (B,C): a basis bump cell cannot be congruent mod N to an extra bump cell -/
private lemma core_BC {d r : ℕ} {L : AddSubgroup (V d)} {t u : V d}
    (i₁ : Fin d) (ht : t = (N0 d r : ℤ) • eb d i₁ + xhole (d := d) i₁)
    (σ' : Fin 2) (l : Fin r) (w : Fin r → V d) (d0 : V d)
    (hu : u = (N0 d r : ℤ) • w l + d0)
    (hd0 : d0 ∈ toothDent (d := d) (V0 d r) (sep r) r σ' l)
    (hNV : t - u ∈ NV d (N0 d r)) : t - u ∈ NL d (N0 d r) L := by
  exfalso
  have hdiv : (N0 d r : ℤ) ∣ (t - u) i₁ := (mem_NV_iff.mp hNV) i₁
  have hti : t i₁ = (N0 d r : ℤ) + 2 := bb_coord_self ht
  have hui : u i₁ = (N0 d r : ℤ) * w l i₁ + d0 i₁ := by
    simp [hu, Pi.add_apply, Pi.smul_apply]
  have hd2 : (N0 d r : ℤ) ∣ (2 : ℤ) - d0 i₁ := by
    have hd' : (N0 d r : ℤ) ∣ ((N0 d r : ℤ) + 2) - ((N0 d r : ℤ) * w l i₁ + d0 i₁) := by
      simpa [hti, hui] using hdiv
    have hdd : (N0 d r : ℤ) ∣ (N0 d r : ℤ) * (1 - w l i₁) + (2 - d0 i₁) := by
      convert hd' using 1
      ring
    exact dvd_of_dvd_add_mul (N := (N0 d r : ℤ)) (a := 2 - d0 i₁) (w := 1 - w l i₁) hdd
  have h5 : (5 : ℤ) ≤ d0 i₁ := toothDent_coord_ge_five' σ' l d0 hd0 i₁
  have hbox : d0 i₁ < (N0 d r : ℤ) := (toothDent_coord_in_box σ' l d0 hd0 i₁).2
  have hz : (2 : ℤ) - d0 i₁ = 0 := eq_zero_of_dvd_of_lt_int N0_pos hd2
    (by omega) (by omega)
  have hEq2 : d0 i₁ = (2 : ℤ) := by omega
  omega

/-- (C,B): symmetric to (B,C) -/
private lemma core_CB {d r : ℕ} {L : AddSubgroup (V d)} {t u : V d}
    (σ : Fin 2) (l : Fin r) (w : Fin r → V d) (d0 : V d)
    (ht : t = (N0 d r : ℤ) • w l + d0)
    (hd0 : d0 ∈ toothDent (d := d) (V0 d r) (sep r) r σ l)
    (i₂ : Fin d) (hu : u = (N0 d r : ℤ) • eb d i₂ + xhole (d := d) i₂)
    (hNV : t - u ∈ NV d (N0 d r)) : t - u ∈ NL d (N0 d r) L := by
  exfalso
  have hdiv : (N0 d r : ℤ) ∣ (t - u) i₂ := (mem_NV_iff.mp hNV) i₂
  have hti : t i₂ = (N0 d r : ℤ) * w l i₂ + d0 i₂ := by
    simp [ht, Pi.add_apply, Pi.smul_apply]
  have hui : u i₂ = (N0 d r : ℤ) + 2 := bb_coord_self hu
  have hd2 : (N0 d r : ℤ) ∣ d0 i₂ - (2 : ℤ) := by
    have hd' : (N0 d r : ℤ) ∣ ((N0 d r : ℤ) * w l i₂ + d0 i₂) - ((N0 d r : ℤ) + 2) := by
      simpa [hti, hui] using hdiv
    have hdd : (N0 d r : ℤ) ∣ (N0 d r : ℤ) * (w l i₂ - 1) + (d0 i₂ - 2) := by
      convert hd' using 1
      ring
    exact dvd_of_dvd_add_mul (N := (N0 d r : ℤ)) (a := d0 i₂ - 2) (w := w l i₂ - 1) hdd
  have h5 : (5 : ℤ) ≤ d0 i₂ := toothDent_coord_ge_five' σ l d0 hd0 i₂
  have hbox : d0 i₂ < (N0 d r : ℤ) := (toothDent_coord_in_box σ l d0 hd0 i₂).2
  have hz : d0 i₂ - (2 : ℤ) = 0 := eq_zero_of_dvd_of_lt_int N0_pos hd2
    (by omega) (by omega)
  have hEq2 : d0 i₂ = (2 : ℤ) := by omega
  omega


/-- (A,C): a body cell congruent mod N to an extra bump cell equals its dent -/
private lemma core_AC {d r : ℕ} {L : AddSubgroup (V d)} {w : Fin r → V d}
    (hwL : ∀ l : Fin r, w l ∈ L) {t u : V d}
    (σ σ' : Fin 2) (l : Fin r)
    (htbox : t ∈ box d (N0 d r))
    (htD : ∀ l : Fin r, t ∉ toothDent (d := d) (V0 d r) (sep r) r σ l)
    (d0 : V d) (hu : u = (N0 d r : ℤ) • w l + d0)
    (hd0 : d0 ∈ toothDent (d := d) (V0 d r) (sep r) r σ' l)
    (hNV : t - u ∈ NV d (N0 d r)) : t - u ∈ NL d (N0 d r) L := by
  have hEq : t = d0 := by
    have htd : t - d0 ∈ NV d (N0 d r) := by
      rw [mem_NV_iff]
      intro j
      have hdiv : (N0 d r : ℤ) ∣ (t - u) j := (mem_NV_iff.mp hNV) j
      have huj : u j = (N0 d r : ℤ) * w l j + d0 j := by
        simp [hu, Pi.add_apply, Pi.smul_apply]
      exact dvd_of_dvd_sub_add_mul (N := (N0 d r : ℤ)) (t := t j) (d := d0 j) (w := w l j)
        (by simpa [huj] using hdiv)
    exact box_eq_of_mem_NV_diff (N := N0 d r) N0_pos htbox
      (toothDent_mem_box (fin_pos l) σ' l d0 hd0) htd
  by_cases hσσ' : σ = σ'
  · exfalso
    have hmem : t ∈ toothDent (d := d) (V0 d r) (sep r) r σ l := by
      rw [hEq]
      simpa [hσσ'] using hd0
    exact (htD l) hmem
  · have hx : t - u = -((N0 d r : ℤ) • w l) := by
      rw [hu, hEq]
      simp
    have hwl : w l ∈ L := hwL l
    have hneg : -w l ∈ L := L.neg_mem hwl
    rw [hx]
    rw [NL, mem_zimg]
    refine ⟨-w l, hneg, ?_⟩
    exact (smul_neg_pointwise (N0 d r : ℤ) (w l)).symm

/-- (C,A): symmetric to (A,C) -/
private lemma core_CA {d r : ℕ} {L : AddSubgroup (V d)} {w : Fin r → V d}
    (hwL : ∀ l : Fin r, w l ∈ L) {t u : V d}
    (σ σ' : Fin 2) (l : Fin r) (d0 : V d)
    (ht : t = (N0 d r : ℤ) • w l + d0)
    (hd0 : d0 ∈ toothDent (d := d) (V0 d r) (sep r) r σ l)
    (hubox : u ∈ box d (N0 d r))
    (huD : ∀ l : Fin r, u ∉ toothDent (d := d) (V0 d r) (sep r) r σ' l)
    (hNV : t - u ∈ NV d (N0 d r)) : t - u ∈ NL d (N0 d r) L := by
  have hEq : u = d0 := by
    have hdu : d0 - u ∈ NV d (N0 d r) := by
      rw [mem_NV_iff]
      intro j
      have hdiv : (N0 d r : ℤ) ∣ (t - u) j := (mem_NV_iff.mp hNV) j
      have htj : t j = (N0 d r : ℤ) * w l j + d0 j := by
        simp [ht, Pi.add_apply, Pi.smul_apply]
      have hd' : (N0 d r : ℤ) ∣ (N0 d r : ℤ) * w l j + d0 j - u j := by
        simpa [htj] using hdiv
      exact dvd_of_dvd_add_mul_sub (N := (N0 d r : ℤ)) (d := d0 j) (u := u j) (w := w l j) hd'
    exact (box_eq_of_mem_NV_diff (N := N0 d r) N0_pos
      (toothDent_mem_box (fin_pos l) σ l d0 hd0) hubox hdu).symm
  by_cases hσσ' : σ = σ'
  · exfalso
    have hmem : u ∈ toothDent (d := d) (V0 d r) (sep r) r σ' l := by
      rw [hEq]
      simpa [hσσ'] using hd0
    exact (huD l) hmem
  · have hx : t - u = (N0 d r : ℤ) • w l := by
      rw [ht, hEq]
      simp
    have hwl : w l ∈ L := hwL l
    rw [hx]
    rw [NL, mem_zimg]
    exact ⟨w l, hwl, rfl⟩

/-- (C,C): two extra bump cells congruent mod N have the same tooth and dent -/
private lemma core_CC {d r : ℕ} {L : AddSubgroup (V d)} {w : Fin r → V d} {t u : V d}
    (σ σ' : Fin 2) (l l' : Fin r) (d0 d0' : V d)
    (ht : t = (N0 d r : ℤ) • w l + d0)
    (hd0 : d0 ∈ toothDent (d := d) (V0 d r) (sep r) r σ l)
    (hu : u = (N0 d r : ℤ) • w l' + d0')
    (hd0' : d0' ∈ toothDent (d := d) (V0 d r) (sep r) r σ' l')
    (hNV : t - u ∈ NV d (N0 d r)) : t - u ∈ NL d (N0 d r) L := by
  have hEq : d0 = d0' := by
    have hdd : d0 - d0' ∈ NV d (N0 d r) := by
      rw [mem_NV_iff]
      intro j
      have hdiv : (N0 d r : ℤ) ∣ (t - u) j := (mem_NV_iff.mp hNV) j
      have ht' : t j = (N0 d r : ℤ) * w l j + d0 j := by
        simp [ht, Pi.add_apply, Pi.smul_apply]
      have hu' : u j = (N0 d r : ℤ) * w l' j + d0' j := by
        simp [hu, Pi.add_apply, Pi.smul_apply]
      have hd' : (N0 d r : ℤ) ∣ (N0 d r : ℤ) * (w l j - w l' j) + (d0 j - d0' j) := by
        rcases hdiv with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        calc
          (N0 d r : ℤ) * (w l j - w l' j) + (d0 j - d0' j) = t j - u j := by
            rw [ht', hu']
            ring
          _ = (N0 d r : ℤ) * k := by simpa using hk
      have hd'' : (N0 d r : ℤ) ∣ (N0 d r : ℤ) * (w l j - w l' j) + d0 j - d0' j := by
        rcases hd' with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        rw [← hk]
        ring
      exact dvd_of_dvd_add_mul_sub (N := (N0 d r : ℤ)) (d := d0 j) (u := d0' j)
        (w := w l j - w l' j) hd''
    exact box_eq_of_mem_NV_diff (d := d) (N := N0 d r) N0_pos
      (toothDent_mem_box (fin_pos l) σ l d0 hd0)
      (toothDent_mem_box (fin_pos l') σ' l' d0' hd0') hdd
  have hpair : (σ, l) = (σ', l') := by
    by_contra hne
    have hdisj := toothDent_disjoint_of_ne (d := d) σ σ' l l' hne
    exact (Set.disjoint_left.mp hdisj) hd0 (by rwa [← hEq] at hd0')
  have hll : l = l' := congrArg Prod.snd hpair
  have hw : w l = w l' := by rw [hll]
  have hz : t - u = 0 := by
    rw [ht, hu, hEq, hw]
    simp
  rw [hz]
  exact zero_mem_NL (N := N0 d r) L

/-- STATEMENT: differences of cells of two tooth tiles that lie in NV lie in NL.
  This is the geometric disjointness / collision-freeness fact needed by the
  backward direction of the tiling reduction. -/
lemma geometric_disjointness {d r : ℕ}
    (w : Fin r → V d) (L : AddSubgroup (V d))
    (hwL : ∀ l : Fin r, w l ∈ L) (σ σ' : Fin 2) :
    (toothTile w σ - toothTile w σ') ∩ NV d (N0 d r) ⊆ NL d (N0 d r) L := by
  intro x hx
  rcases hx with ⟨hxsub, hxNV⟩
  rw [Set.mem_sub] at hxsub
  rcases hxsub with ⟨t, ht, u, hu, htu⟩
  have hNV : t - u ∈ NV d (N0 d r) := by
    rw [htu]
    exact hxNV
  have hct := toothTile_mem_cases w σ t ht
  have hcu := toothTile_mem_cases w σ' u hu
  rcases hct with htb | htbB | htbE
  · rcases hcu with hub | hubB | hubE
    · -- (A,A)
      rw [← htu]
      exact core_AA htb.1 hub.1 hNV
    · -- (A,B)
      rcases hubB with ⟨i₂, huEq⟩
      rw [← htu]
      exact core_AB htb.1 htb.2.1 i₂ huEq hNV
    · -- (A,C)
      rcases hubE with ⟨l, hub⟩
      rcases (toothBump_mem_iff w σ' l u).mp hub with ⟨d0, hd0, huEq⟩
      rw [← htu]
      exact core_AC (w := w) hwL σ σ' l htb.1 htb.2.2 d0 huEq hd0 hNV
  · rcases htbB with ⟨i₁, htEq⟩
    rcases hcu with hub | hubB | hubE
    · -- (B,A)
      rw [← htu]
      exact core_BA i₁ htEq hub.1 hub.2.1 hNV
    · -- (B,B)
      rcases hubB with ⟨i₂, huEq⟩
      rw [← htu]
      exact core_BB i₁ htEq i₂ huEq hNV
    · -- (B,C)
      rcases hubE with ⟨l, hub⟩
      rcases (toothBump_mem_iff w σ' l u).mp hub with ⟨d0, hd0, huEq⟩
      rw [← htu]
      exact core_BC i₁ htEq σ' l w d0 huEq hd0 hNV
  · rcases htbE with ⟨l, htb⟩
    rcases (toothBump_mem_iff w σ l t).mp htb with ⟨d0, hd0, htEq⟩
    rcases hcu with hub | hubB | hubE
    · -- (C,A)
      rw [← htu]
      exact core_CA (w := w) hwL σ σ' l d0 htEq hd0 hub.1 hub.2.2 hNV
    · -- (C,B)
      rcases hubB with ⟨i₂, huEq⟩
      rw [← htu]
      exact core_CB σ l w d0 htEq hd0 i₂ huEq hNV
    · -- (C,C)
      rcases hubE with ⟨l', hub'⟩
      rcases (toothBump_mem_iff w σ' l' u).mp hub' with ⟨d0', hd0', huEq⟩
      rw [← htu]
      exact core_CC σ σ' l l' d0 d0' htEq hd0 huEq hd0' hNV


lemma rigid_pair_data_geo {d : ℕ} (L : AddSubgroup (Fin d → ℤ)) :
  ∃ (N : ℕ) (T T₁ T₂ : Set (Fin d → ℤ)),
    0 < N ∧ T.Finite ∧ T₁.Finite ∧ T₂.Finite ∧
    (0 : Fin d → ℤ) ∈ T ∧ (0 : Fin d → ℤ) ∈ T₁ ∧ (0 : Fin d → ℤ) ∈ T₂ ∧
    let NV : Set (Fin d → ℤ) := Set.image (fun x => (N : ℤ) • x) Set.univ
    let NL : Set (Fin d → ℤ) := Set.image (fun x => (N : ℤ) • x) (L : Set (Fin d → ℤ))
    AddSubgroup.IsComplement NV T ∧
    (∀ A : Set (Fin d → ℤ), AddSubgroup.IsComplement A T → (0 : Fin d → ℤ) ∈ A → A = NV) ∧
    Set.image2 Add.add T₁ NL = Set.image2 Add.add T NL ∧
    Set.image2 Add.add T₂ NL = Set.image2 Add.add T NL ∧
    (∀ C₁ C₂ : Set (Fin d → ℤ),
      ((0 : Fin d → ℤ) ∈ C₁ ∪ C₂ ∧
        Function.Bijective
          (fun x : Sum {p : (Fin d → ℤ) × (Fin d → ℤ) | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
                       {p : (Fin d → ℤ) × (Fin d → ℤ) | p.1 ∈ C₂ ∧ p.2 ∈ T₂} =>
            match x with
            | Sum.inl p => p.1.1 + p.1.2
            | Sum.inr p => p.1.1 + p.1.2)) ↔
      (C₁ ∪ C₂ = NV ∧ Disjoint C₁ C₂ ∧
        Set.image2 Add.add C₁ NL = C₁ ∧ Set.image2 Add.add C₂ NL = C₂)) ∧
    (T₁ - T₁) ∩ NV ⊆ NL ∧
    (T₂ - T₁) ∩ NV ⊆ NL ∧
    (T₁ - T₂) ∩ NV ⊆ NL ∧
    (T₂ - T₂) ∩ NV ⊆ NL := by
  classical
  by_cases hd : 1 ≤ d
  · have hd0 : 0 < d := by omega
    rcases (small_generating_family_int_subgroup d L) with ⟨r, hr, wgen, hwL, hw0, hwinj, hspan⟩
    refine ⟨N0 d r, basisTile d (N0 d r), toothTile wgen 0, toothTile wgen 1, ?_⟩
    dsimp
    constructor
    · have h7 := N0_ge_seven (d := d) (r := r)
      omega
    constructor
    · exact basisTile_finite d (N0 d r)
    constructor
    · exact toothTile_finite wgen 0
    constructor
    · exact toothTile_finite wgen 1
    constructor
    · exact zero_mem_basisTile (by have h7 := N0_ge_seven (d := d) (r := r); omega)
    constructor
    · exact zero_mem_toothTile hd0 wgen 0
    constructor
    · exact zero_mem_toothTile hd0 wgen 1
    · constructor
      · exact NV_IsComplement_basisTile (by have h7 := N0_ge_seven (d := d) (r := r); omega)
      constructor
      · exact basis_rigid hd (by have h7 := N0_ge_seven (d := d) (r := r); omega)
      constructor
      · change (toothTile wgen 0) + NL d (N0 d r) L = basisTile d (N0 d r) + NL d (N0 d r) L
        exact toothTile_add_NL L wgen hwL 0
      constructor
      · change (toothTile wgen 1) + NL d (N0 d r) L = basisTile d (N0 d r) + NL d (N0 d r) L
        exact toothTile_add_NL L wgen hwL 1
      constructor
      · intro C₁ C₂
        have hiff := rigid_pair_iff hd0 wgen L hwL hw0 hspan C₁ C₂
        constructor
        · intro h
          rcases h with ⟨h0C, hBij0⟩
          have hBijJ : Function.Bijective (jointSum (d := d) C₁ C₂ (toothTile wgen 0) (toothTile wgen 1)) := by
            convert hBij0 using 1
            funext x
            cases x <;> rfl
          have hR := hiff.mp ⟨h0C, hBijJ⟩
          rcases hR with ⟨hUn, hDisj, hC1, hC2⟩
          constructor
          · exact hUn
          constructor
          · exact hDisj
          constructor
          · rw [image2_add_add_eq]
            exact hC1
          · rw [image2_add_add_eq]
            exact hC2
        · intro h
          rcases h with ⟨hUn, hDisj, hC1, hC2⟩
          have hC1' : C₁ + NL d (N0 d r) L = C₁ := by
            rw [← image2_add_add_eq]
            exact hC1
          have hC2' : C₂ + NL d (N0 d r) L = C₂ := by
            rw [← image2_add_add_eq]
            exact hC2
          have hL0 := hiff.mpr ⟨hUn, hDisj, hC1', hC2'⟩
          constructor
          · exact hL0.1
          · convert hL0.2 using 1
            funext x
            cases x <;> rfl
      constructor
      · exact geometric_disjointness (d := d) (r := r) wgen L hwL 0 0
      constructor
      · exact geometric_disjointness (d := d) (r := r) wgen L hwL 1 0
      constructor
      · exact geometric_disjointness (d := d) (r := r) wgen L hwL 0 1
      · exact geometric_disjointness (d := d) (r := r) wgen L hwL 1 1
  · have hd0 : d = 0 := by omega
    subst d
    classical
    have hall0 : ∀ x : Fin 0 → ℤ, x = 0 := fun x => zero_unique rfl x
    have hNVuniv : NV 0 1 = (Set.univ : Set (Fin 0 → ℤ)) := by
      ext x
      constructor
      · intro hx
        trivial
      · intro hx
        rw [mem_NV_iff]
        intro i
        exact False.elim ((Nat.not_lt_zero i.val) i.isLt)
    have hNL0 : NL 0 1 L = ({0} : Set (Fin 0 → ℤ)) := by
      apply le_antisymm
      · intro x hx
        have hx0 : x = 0 := hall0 x
        rw [hx0]
        simp
      · intro x hx
        have hx0 : x = 0 := by simpa using hx
        rw [hx0]
        rw [NL, mem_zimg]
        exact ⟨0, zero_mem L, by simp⟩
    have hcompNV : AddSubgroup.IsComplement (NV 0 1) ({0} : Set (Fin 0 → ℤ)) := by
      rw [AddSubgroup.isComplement_iff_existsUnique]
      intro g
      have hg : g = 0 := hall0 g
      subst g
      refine ⟨(⟨0, by rw [hNVuniv]; trivial⟩, ⟨0, by simp⟩), ?_, ?_⟩
      · change (0 : Fin 0 → ℤ) + 0 = 0
        rw [zero_add]
      · intro y hy
        rcases y with ⟨⟨a, ha⟩, ⟨t, ht⟩⟩
        have ha0 : a = 0 := hall0 a
        have ht0 : t = 0 := by simpa using ht
        apply Prod.ext
        · apply Subtype.ext
          exact ha0
        · apply Subtype.ext
          exact ht0
    have hRigid : ∀ A : Set (Fin 0 → ℤ), AddSubgroup.IsComplement A ({0} : Set (Fin 0 → ℤ)) →
        (0 : Fin 0 → ℤ) ∈ A → A = NV 0 1 := by
      intro A hA h0A
      have hAuniv : A = Set.univ := by
        apply le_antisymm
        · intro x hx
          trivial
        · intro x hx
          rcases (hA.existsUnique x) with ⟨y, hy, hyu⟩
          have hax : (y.1 : Fin 0 → ℤ) = x := by
            rw [hall0 (y.1 : Fin 0 → ℤ), hall0 x]
          rw [← hax]
          exact y.1.2
      rw [hAuniv]
      exact hNVuniv.symm
    have hper : ∀ C : Set (Fin 0 → ℤ), C + NL 0 1 L = C := by
      intro C
      apply le_antisymm
      · intro x hx
        rcases Set.mem_add.mp hx with ⟨c, hc, n, hn, hx⟩
        have hn0 : n = 0 := hall0 n
        have hx0 : x = c := by
          rw [← hx]
          rw [hn0]
          rw [add_zero]
        rw [hx0]
        exact hc
      · intro x hx
        refine Set.mem_add.mpr ⟨x, hx, 0, ?_, ?_⟩
        · rw [hNL0]
          simp
        · rw [add_zero]
    refine ⟨1, ({0} : Set (Fin 0 → ℤ)), ({0} : Set (Fin 0 → ℤ)), ({0} : Set (Fin 0 → ℤ)), ?_⟩
    constructor
    · norm_num
    constructor
    · exact Set.finite_singleton 0
    constructor
    · exact Set.finite_singleton 0
    constructor
    · exact Set.finite_singleton 0
    constructor
    · simp
    constructor
    · simp
    constructor
    · simp
    · dsimp
      constructor
      · exact hcompNV
      constructor
      · intro A hA h0A
        change A = NV 0 1
        exact hRigid A hA h0A
      constructor
      · change ({0} : Set (Fin 0 → ℤ)) + NL 0 1 L = ({0} : Set (Fin 0 → ℤ)) + NL 0 1 L
        rfl
      constructor
      · change ({0} : Set (Fin 0 → ℤ)) + NL 0 1 L = ({0} : Set (Fin 0 → ℤ)) + NL 0 1 L
        rfl
      constructor
      · intro C₁ C₂
        have h01 : (0 : Fin 0 → ℤ) ∈ ({0} : Set (Fin 0 → ℤ)) := by simp
        have hper1 : C₁ + NL 0 1 L = C₁ := hper C₁
        have hper2 : C₂ + NL 0 1 L = C₂ := hper C₂
        have hT : ({0} : Set (Fin 0 → ℤ)) + NL 0 1 L = ({0} : Set (Fin 0 → ℤ)) + NL 0 1 L := rfl
        constructor
        · intro h
          rcases h with ⟨h0C, hBij⟩
          have hBijJ : Function.Bijective (jointSum (d := 0) C₁ C₂ ({0} : Set (Fin 0 → ℤ)) ({0} : Set (Fin 0 → ℤ))) := by
            convert hBij using 1
          rcases (pair_forced (d := 0) (N := 1) L h0C hBijJ hcompNV hRigid hT hT hper1 hper2 h01 h01)
            with ⟨hUn, hDisj, hC1, hC2⟩
          constructor
          · exact hUn
          constructor
          · exact hDisj
          constructor
          · change C₁ + NL 0 1 L = C₁
            exact hC1
          · change C₂ + NL 0 1 L = C₂
            exact hC2
        · intro h
          rcases h with ⟨hUn, hDisj, hC1, hC2⟩
          have hC1' : C₁ + NL 0 1 L = C₁ := by
            change Set.image2 Add.add C₁ (NL 0 1 L) = C₁
            exact hC1
          have hC2' : C₂ + NL 0 1 L = C₂ := by
            change Set.image2 Add.add C₂ (NL 0 1 L) = C₂
            exact hC2
          have hR := pair_solvable (d := 0) (N := 1) L hcompNV hcompNV hcompNV hT hT hUn hDisj hC1' hC2'
          constructor
          · exact hR.1
          · convert hR.2 using 1
      constructor
      · intro x hx
        rcases hx with ⟨hxsub, hxNV⟩
        rw [Set.mem_sub] at hxsub
        rcases hxsub with ⟨a, ha, b, hb, hxab⟩
        have ha0 : a = 0 := by simpa using ha
        have hb0 : b = 0 := by simpa using hb
        have hx0 : x = 0 := by rw [← hxab, ha0, hb0]; simp
        rw [hx0]
        rw [Set.mem_smul_set]
        exact ⟨0, zero_mem L, by simp⟩
      constructor
      · intro x hx
        rcases hx with ⟨hxsub, hxNV⟩
        rw [Set.mem_sub] at hxsub
        rcases hxsub with ⟨a, ha, b, hb, hxab⟩
        have ha0 : a = 0 := by simpa using ha
        have hb0 : b = 0 := by simpa using hb
        have hx0 : x = 0 := by rw [← hxab, ha0, hb0]; simp
        rw [hx0]
        rw [Set.mem_smul_set]
        exact ⟨0, zero_mem L, by simp⟩
      constructor
      · intro x hx
        rcases hx with ⟨hxsub, hxNV⟩
        rw [Set.mem_sub] at hxsub
        rcases hxsub with ⟨a, ha, b, hb, hxab⟩
        have ha0 : a = 0 := by simpa using ha
        have hb0 : b = 0 := by simpa using hb
        have hx0 : x = 0 := by rw [← hxab, ha0, hb0]; simp
        rw [hx0]
        rw [Set.mem_smul_set]
        exact ⟨0, zero_mem L, by simp⟩
      · intro x hx
        rcases hx with ⟨hxsub, hxNV⟩
        rw [Set.mem_sub] at hxsub
        rcases hxsub with ⟨a, ha, b, hb, hxab⟩
        have ha0 : a = 0 := by simpa using ha
        have hb0 : b = 0 := by simpa using hb
        have hx0 : x = 0 := by rw [← hxab, ha0, hb0]; simp
        rw [hx0]
        rw [Set.mem_smul_set]
        exact ⟨0, zero_mem L, by simp⟩


/-!
# Backward direction of the tiling reduction

Given the geometric rigid-pair data (`rigid_pair_data_geo (π.ker)`) and a
complement `A'` of `F' = (X + T₁) ∪ T₂` with `0 ∈ A'`, the goal is to force
`A' ⊆ NV` and `A' + NL = A'` (from which `A' = N·π⁻¹(A)` follows, and then
`A` is a complement of `F`).

The hinge is the *converse* of the regrouping lemma: `A' ⊕ F' = V` plus the
geometric disjointness facts (collision-freeness of `X ⊕ T₁` and disjointness
`(X + T₁) ∩ T₂ = ∅`, both consequences of G) imply that `(C₁,C₂) := (X⊕A', A')`
jointly tile by `(T₁,T₂)`; then the pair characterization (c) gives
`C₁ ∪ C₂ = NV` and both periodicity statements.
-/

section Xfacts
variable {G : Type*} [AddCommGroup G] {d : ℕ}

/-- the transversal part over F∖{0} avoids the kernel -/
lemma S_F_inter_ker_empty (π : V d →+ G) (D : Set (V d)) {F : Set G} :
    (((π ⁻¹' (F \ {0})) ∩ D) ∩ (π.ker : Set (V d))) = ∅ := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_inter_iff] at hx
    rcases hx with ⟨hx1, hx2⟩
    rw [Set.mem_inter_iff] at hx1
    have hxF : π x ∈ F \ {0} := Set.mem_preimage.mp hx1.1
    have hxk : π x = 0 := (ker_coe_mem_iff π x).mp hx2
    exact ((Set.mem_sdiff (π x)).mp hxF).2 hxk
  · intro hx
    simpa using hx

/-- X = N·S_F does not meet NL = N·K -/
lemma X_inter_NL_empty {N : ℕ} (hN : 0 < N)
    (π : V d →+ G) (D : Set (V d)) {F : Set G} :
    zimg N ((π ⁻¹' (F \ {0})) ∩ D) ∩ NL d N π.ker = ∅ := by
  change zimg N ((π ⁻¹' (F \ {0})) ∩ D) ∩ zimg N (π.ker : Set (V d)) = ∅
  rw [← zimg_inter (N := N) hN ((π ⁻¹' (F \ {0})) ∩ D) (π.ker : Set (V d))]
  rw [S_F_inter_ker_empty π D (F := F)]
  exact zimg_empty (d := d) N

/-- differences of transversal representatives over F∖{0} meet the kernel only at 0 -/
lemma S_F_sub_S_F_inter_ker_sub_zero (π : V d →+ G) (D : Set (V d))
    (hD : AddSubgroup.IsComplement D (π.ker : Set (V d))) {F : Set G} :
    ((((π ⁻¹' (F \ {0})) ∩ D) - ((π ⁻¹' (F \ {0})) ∩ D)) ∩ (π.ker : Set (V d)))
      ⊆ ({0} : Set (V d)) := by
  intro x hx
  rcases hx with ⟨hxsub, hxker⟩
  rw [Set.mem_sub] at hxsub
  rcases hxsub with ⟨s₁, hs₁, s₂, hs₂, hx⟩
  have hker : s₁ - s₂ ∈ (π.ker : Set (V d)) := by rwa [hx]
  have hπsub : π (s₁ - s₂) = 0 := (ker_coe_mem_iff π (s₁ - s₂)).mp hker
  have hπ : π s₁ = π s₂ := by
    have h : π s₁ - π s₂ = 0 := by simpa [map_sub] using hπsub
    exact sub_eq_zero.mp h
  rw [Set.mem_inter_iff] at hs₁ hs₂
  have hD1 : s₁ ∈ D := hs₁.2
  have hD2 : s₂ ∈ D := hs₂.2
  have hEq : s₁ = s₂ := D_unique_of_pi_eq (G := G) π D hD (u₁ := s₁) (u₂ := s₂) hD1 hD2 hπ
  have hx0 : x = 0 := by
    calc
      x = s₁ - s₂ := hx.symm
      _ = 0 := by rw [hEq]; simp
  simpa [hx0]

/-- (X − X) ∩ NL ⊆ {0} -/
lemma XX_inter_NL_sub_zero {N : ℕ} (hN : 0 < N)
    (π : V d →+ G) (D : Set (V d))
    (hD : AddSubgroup.IsComplement D (π.ker : Set (V d))) {F : Set G} :
    ((zimg N ((π ⁻¹' (F \ {0})) ∩ D)) - (zimg N ((π ⁻¹' (F \ {0})) ∩ D)))
      ∩ NL d N π.ker ⊆ ({0} : Set (V d)) := by
  intro x hx
  rcases hx with ⟨hxsub, hxNL⟩
  rw [Set.mem_sub] at hxsub
  rcases hxsub with ⟨a, ha, b, hb, hxab⟩
  rw [mem_zimg] at ha hb
  rcases ha with ⟨s₁, hs₁, hsa⟩
  rcases hb with ⟨s₂, hs₂, hsb⟩
  change x ∈ zimg N (π.ker : Set (V d)) at hxNL
  rw [mem_zimg] at hxNL
  rcases hxNL with ⟨k, hk, hxk⟩
  have hNlin : (N : ℤ) • (s₁ - s₂) = (N : ℤ) • k := by
    calc
      (N : ℤ) • (s₁ - s₂) = (N : ℤ) • s₁ - (N : ℤ) • s₂ := by rw [zsmul_sub_pointwise]
      _ = a - b := by rw [hsa, hsb]
      _ = x := hxab
      _ = (N : ℤ) • k := hxk
  have hsubk : s₁ - s₂ = k := zsmul_injective_pointwise (N := N) hN hNlin
  have hk' : s₁ - s₂ ∈ (π.ker : Set (V d)) := by rwa [hsubk]
  have hzero : s₁ - s₂ = 0 := by
    let hz : ((((π ⁻¹' (F \ {0})) ∩ D) - ((π ⁻¹' (F \ {0})) ∩ D)) ∩ (π.ker : Set (V d)))
        ⊆ ({0} : Set (V d)) := S_F_sub_S_F_inter_ker_sub_zero π D hD (F := F)
    have hmem : s₁ - s₂ ∈ (π ⁻¹' (F \ {0})) ∩ D - ((π ⁻¹' (F \ {0})) ∩ D) := by
      rw [Set.mem_sub]
      exact ⟨s₁, hs₁, s₂, hs₂, rfl⟩
    have hz0 : s₁ - s₂ ∈ ({0} : Set (V d)) := hz ⟨hmem, hk'⟩
    simpa using hz0
  have hx0 : x = 0 := by
    calc
      x = a - b := hxab.symm
      _ = (N : ℤ) • s₁ - (N : ℤ) • s₂ := by rw [hsa, hsb]
      _ = (N : ℤ) • (s₁ - s₂) := by rw [zsmul_sub_pointwise]
      _ = (N : ℤ) • 0 := by rw [hzero]
      _ = 0 := by simp
  simpa [hx0]

end Xfacts

section Corollaries

/-- collision-freeness of X ⊕ T₁ follows from G (differences in T₁−T₁ that are in NV
  are in NL) and the cleanliness of X -/
lemma X_T1_inj1_of_geom {d N : ℕ} {T₁ X : Set (V d)} (L : AddSubgroup (V d))
    (hXsubNV : X ⊆ NV d N)
    (hG11 : (T₁ - T₁) ∩ NV d N ⊆ NL d N L)
    (hXXNL : (X - X) ∩ NL d N L ⊆ ({0} : Set (V d))) :
    ∀ ⦃x y t₁ t₁' : V d⦄, x ∈ X → y ∈ X → t₁ ∈ T₁ → t₁' ∈ T₁ →
      x + t₁ = y + t₁' → x = y ∧ t₁ = t₁' := by
  intro x y t₁ t₁' hx hy ht₁ ht₁' hsum
  have hxyT : x - y ∈ (T₁ - T₁) ∩ NV d N := by
    constructor
    · rw [Set.mem_sub]
      refine ⟨t₁', ht₁', t₁, ht₁, ?_⟩
      calc
        t₁' - t₁ = (x + t₁) - (y + t₁) := by
          rw [hsum]
          abel
        _ = x - y := by abel
    · have hxNV : x ∈ NV d N := hXsubNV hx
      have hyNV : y ∈ NV d N := hXsubNV hy
      have hsub : x - y ∈ (NV_subgroup d N : Set (V d)) := (NV_subgroup d N).sub_mem hxNV hyNV
      exact hsub
  have hxyNL : x - y ∈ NL d N L := hG11 hxyT
  have hxyXX : x - y ∈ X - X := by
    rw [Set.mem_sub]
    exact ⟨x, hx, y, hy, rfl⟩
  have hxy0mem : x - y ∈ ({0} : Set (V d)) := hXXNL ⟨hxyXX, hxyNL⟩
  have hxy0 : x - y = 0 := by simpa using hxy0mem
  have hxy : x = y := sub_eq_zero.mp hxy0
  have ht : t₁ = t₁' := by
    have hsum' : x + t₁ = x + t₁' := by simpa [hxy] using hsum
    exact add_left_cancel hsum'
  exact ⟨hxy, ht⟩

/-- disjointness of X+T₁ and T₂ follows from G (differences in T₂−T₁ that are in NV
  are in NL) and X ∩ NL = ∅ -/
lemma X_T1_disjoint_T2_of_geom {d N : ℕ} {T₁ T₂ X : Set (V d)} (L : AddSubgroup (V d))
    (hXsubNV : X ⊆ NV d N)
    (hXNL : X ∩ NL d N L = ∅)
    (hG21 : (T₂ - T₁) ∩ NV d N ⊆ NL d N L) :
    (X + T₁) ∩ T₂ = ∅ := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hz1, hz2⟩
    rw [Set.mem_add] at hz1
    rcases hz1 with ⟨x, hx, t₁, ht₁, hsum⟩
    have hxT : x ∈ (T₂ - T₁) ∩ NV d N := by
      constructor
      · rw [Set.mem_sub]
        refine ⟨z, hz2, t₁, ht₁, ?_⟩
        calc
          z - t₁ = (x + t₁) - t₁ := by rw [hsum]
          _ = x := by abel
      · exact hXsubNV hx
    have hxNL : x ∈ NL d N L := hG21 hxT
    have hxXNL : x ∈ X ∩ NL d N L := ⟨hx, hxNL⟩
    rw [hXNL] at hxXNL
    exact hxXNL
  · intro hz
    simpa using hz

end Corollaries



section Converse

/-- Converse of regrouping: a complement of the union tile gives a joint bijection,
  provided `X ⊕ T₁` is collision-free and `(X+T₁) ∩ T₂ = ∅`. -/
lemma jointSum_bijective_of_IsComplement {d : ℕ} {T₁ T₂ X AA : Set (V d)}
    (h0AA : (0 : V d) ∈ AA)
    (hA : AddSubgroup.IsComplement AA ((X + T₁) ∪ T₂))
    (hInj1 : ∀ ⦃x y : V d⦄ ⦃t₁ t₁' : V d⦄, x ∈ X → y ∈ X → t₁ ∈ T₁ → t₁' ∈ T₁ →
      x + t₁ = y + t₁' → x = y ∧ t₁ = t₁')
    (hDisjP : (X + T₁) ∩ T₂ = ∅) :
    Function.Bijective (jointSum (d := d) (X + AA) AA T₁ T₂) := by
  constructor
  · -- injective
    intro z₁ z₂ hz
    cases z₁ with
    | inl p₁ =>
        cases z₂ with
        | inl p₂ =>
            have hc₁ : (p₁ : V d × V d).1 ∈ X + AA := p₁.2.1
            have hc₂ : (p₂ : V d × V d).1 ∈ X + AA := p₂.2.1
            have ht₁ : (p₁ : V d × V d).2 ∈ T₁ := p₁.2.2
            have ht₂ : (p₂ : V d × V d).2 ∈ T₁ := p₂.2.2
            have hsum : (p₁ : V d × V d).1 + (p₁ : V d × V d).2 =
                (p₂ : V d × V d).1 + (p₂ : V d × V d).2 := by
              simpa [jointSum] using hz
            rcases (Set.mem_add.mp hc₁) with ⟨x, hx, a, ha, hxa⟩
            rcases (Set.mem_add.mp hc₂) with ⟨y, hy, b, hb, hyb⟩
            have hAB : a + (x + (p₁ : V d × V d).2) = b + (y + (p₂ : V d × V d).2) := by
              calc
                a + (x + (p₁ : V d × V d).2) = (x + a) + (p₁ : V d × V d).2 := by abel
                _ = (p₁ : V d × V d).1 + (p₁ : V d × V d).2 := by rw [hxa]
                _ = (p₂ : V d × V d).1 + (p₂ : V d × V d).2 := hsum
                _ = (y + b) + (p₂ : V d × V d).2 := by rw [hyb]
                _ = b + (y + (p₂ : V d × V d).2) := by abel
            have hx1' : x + (p₁ : V d × V d).2 ∈ (X + T₁) ∪ T₂ := by
              rw [Set.mem_union]
              left
              exact Set.mem_add.mpr ⟨x, hx, (p₁ : V d × V d).2, ht₁, rfl⟩
            have hx2' : y + (p₂ : V d × V d).2 ∈ (X + T₁) ∪ T₂ := by
              rw [Set.mem_union]
              left
              exact Set.mem_add.mpr ⟨y, hy, (p₂ : V d × V d).2, ht₂, rfl⟩
            have hpair := IsComplement_add_left_unique hA ha hb hx1' hx2' hAB
            have hxt : x + (p₁ : V d × V d).2 = y + (p₂ : V d × V d).2 := hpair.2
            have hInj := hInj1 hx hy ht₁ ht₂ hxt
            apply congrArg Sum.inl
            apply Subtype.ext
            apply Prod.ext
            · calc
                (p₁ : V d × V d).1 = x + a := hxa.symm
                _ = y + b := by rw [hInj.1, hpair.1]
                _ = (p₂ : V d × V d).1 := hyb
            · calc
                (p₁ : V d × V d).2 = (p₂ : V d × V d).2 := hInj.2
        | inr p₂ =>
            exfalso
            have hc₁ : (p₁ : V d × V d).1 ∈ X + AA := p₁.2.1
            have hc₂ : (p₂ : V d × V d).1 ∈ AA := p₂.2.1
            have ht₁ : (p₁ : V d × V d).2 ∈ T₁ := p₁.2.2
            have ht₂ : (p₂ : V d × V d).2 ∈ T₂ := p₂.2.2
            have hsum : (p₁ : V d × V d).1 + (p₁ : V d × V d).2 =
                (p₂ : V d × V d).1 + (p₂ : V d × V d).2 := by
              simpa [jointSum] using hz
            rcases (Set.mem_add.mp hc₁) with ⟨x, hx, a, ha, hxa⟩
            have hAB : a + (x + (p₁ : V d × V d).2) = (p₂ : V d × V d).1 + (p₂ : V d × V d).2 := by
              calc
                a + (x + (p₁ : V d × V d).2) = (x + a) + (p₁ : V d × V d).2 := by abel
                _ = (p₁ : V d × V d).1 + (p₁ : V d × V d).2 := by rw [hxa]
                _ = (p₂ : V d × V d).1 + (p₂ : V d × V d).2 := hsum
            have hx1' : x + (p₁ : V d × V d).2 ∈ (X + T₁) ∪ T₂ := by
              rw [Set.mem_union]
              left
              exact Set.mem_add.mpr ⟨x, hx, (p₁ : V d × V d).2, ht₁, rfl⟩
            have ht2' : (p₂ : V d × V d).2 ∈ (X + T₁) ∪ T₂ := by
              rw [Set.mem_union]
              right
              exact ht₂
            have hpair := IsComplement_add_left_unique hA ha hc₂ hx1' ht2' hAB
            have hmem : x + (p₁ : V d × V d).2 ∈ (X + T₁) ∩ T₂ := by
              constructor
              · exact Set.mem_add.mpr ⟨x, hx, (p₁ : V d × V d).2, ht₁, rfl⟩
              · rwa [hpair.2]
            rw [hDisjP] at hmem
            exact hmem
    | inr p₁ =>
        cases z₂ with
        | inl p₂ =>
            exfalso
            have hc₁ : (p₁ : V d × V d).1 ∈ AA := p₁.2.1
            have hc₂ : (p₂ : V d × V d).1 ∈ X + AA := p₂.2.1
            have ht₁ : (p₁ : V d × V d).2 ∈ T₂ := p₁.2.2
            have ht₂ : (p₂ : V d × V d).2 ∈ T₁ := p₂.2.2
            have hsum : (p₁ : V d × V d).1 + (p₁ : V d × V d).2 =
                (p₂ : V d × V d).1 + (p₂ : V d × V d).2 := by
              simpa [jointSum] using hz
            rcases (Set.mem_add.mp hc₂) with ⟨y, hy, b, hb, hyb⟩
            have hAB : b + (y + (p₂ : V d × V d).2) = (p₁ : V d × V d).1 + (p₁ : V d × V d).2 := by
              calc
                b + (y + (p₂ : V d × V d).2) = (y + b) + (p₂ : V d × V d).2 := by abel
                _ = (p₂ : V d × V d).1 + (p₂ : V d × V d).2 := by rw [hyb]
                _ = (p₁ : V d × V d).1 + (p₁ : V d × V d).2 := hsum.symm
            have hy1' : y + (p₂ : V d × V d).2 ∈ (X + T₁) ∪ T₂ := by
              rw [Set.mem_union]
              left
              exact Set.mem_add.mpr ⟨y, hy, (p₂ : V d × V d).2, ht₂, rfl⟩
            have ht1' : (p₁ : V d × V d).2 ∈ (X + T₁) ∪ T₂ := by
              rw [Set.mem_union]
              right
              exact ht₁
            have hpair := IsComplement_add_left_unique hA hc₁ hb ht1' hy1' hAB.symm
            have hmem : y + (p₂ : V d × V d).2 ∈ (X + T₁) ∩ T₂ := by
              constructor
              · exact Set.mem_add.mpr ⟨y, hy, (p₂ : V d × V d).2, ht₂, rfl⟩
              · rw [hpair.2.symm]
                exact ht₁
            rw [hDisjP] at hmem
            exact hmem
        | inr p₂ =>
            have hc₁ : (p₁ : V d × V d).1 ∈ AA := p₁.2.1
            have hc₂ : (p₂ : V d × V d).1 ∈ AA := p₂.2.1
            have ht₁ : (p₁ : V d × V d).2 ∈ T₂ := p₁.2.2
            have ht₂ : (p₂ : V d × V d).2 ∈ T₂ := p₂.2.2
            have hsum : (p₁ : V d × V d).1 + (p₁ : V d × V d).2 =
                (p₂ : V d × V d).1 + (p₂ : V d × V d).2 := by
              simpa [jointSum] using hz
            have ht1' : (p₁ : V d × V d).2 ∈ (X + T₁) ∪ T₂ := by
              rw [Set.mem_union]
              right
              exact ht₁
            have ht2' : (p₂ : V d × V d).2 ∈ (X + T₁) ∪ T₂ := by
              rw [Set.mem_union]
              right
              exact ht₂
            have hpair := IsComplement_add_left_unique hA hc₁ hc₂ ht1' ht2' hsum
            apply congrArg Sum.inr
            apply Subtype.ext
            apply Prod.ext
            · exact hpair.1
            · exact hpair.2
  · -- surjective
    intro v
    rcases (hA.existsUnique v) with ⟨p, hp, hp'⟩
    let a : V d := (p.1 : V d)
    let f : V d := (p.2 : V d)
    have ha : a ∈ AA := p.1.2
    have hf : f ∈ (X + T₁) ∪ T₂ := p.2.2
    have hsum : a + f = v := hp
    rcases hf with hf1 | hf2
    · rcases (Set.mem_add.mp hf1) with ⟨x, hx, t₁, ht₁, hxt⟩
      -- c := x + a ∈ X + AA, v = c + t₁
      have hc : x + a ∈ X + AA := Set.mem_add.mpr ⟨x, hx, a, ha, rfl⟩
      refine ⟨Sum.inl ⟨((x + a), t₁), ⟨hc, ht₁⟩⟩, ?_⟩
      change (x + a) + t₁ = v
      calc
        (x + a) + t₁ = a + (x + t₁) := by abel
        _ = a + f := by rw [hxt]
        _ = v := hsum
    · have hc : a ∈ AA := ha
      refine ⟨Sum.inr ⟨(a, f), ⟨ha, hf2⟩⟩, ?_⟩
      change a + f = v
      exact hsum

end Converse

section Hinge

/-- Backward hinge: a complement A' of F' = (X+T₁)∪T₂ containing 0 is contained in
  NV and NL-periodic, provided the rigid-pair characterization (c) and the geometric
  facts G hold. -/
lemma backward_saturated {G : Type*} [AddCommGroup G] {d : ℕ}
    (π : V d →+ G) (hπ : Function.Surjective π)
    (D : Set (V d)) (hD : AddSubgroup.IsComplement D (π.ker : Set (V d)))
    {N : ℕ} (hNpos : 0 < N) {T₁ T₂ : Set (V d)}
    (hPair : ∀ C₁ C₂ : Set (V d),
      ((0 : V d) ∈ C₁ ∪ C₂ ∧ Function.Bijective (jointSum (d := d) C₁ C₂ T₁ T₂)) ↔
      (C₁ ∪ C₂ = NV d N ∧ Disjoint C₁ C₂ ∧
        C₁ + NL d N π.ker = C₁ ∧ C₂ + NL d N π.ker = C₂))
    (hG11 : (T₁ - T₁) ∩ NV d N ⊆ NL d N π.ker)
    (hG21 : (T₂ - T₁) ∩ NV d N ⊆ NL d N π.ker)
    {F : Set G} (h0F : (0 : G) ∈ F)
    {A' : Set (V d)}
    (hA' : AddSubgroup.IsComplement A'
      ((zimg N ((π ⁻¹' (F \ {0})) ∩ D) + T₁) ∪ T₂))
    (h0A' : (0 : V d) ∈ A') :
    A' ⊆ NV d N ∧ A' + NL d N π.ker = A' := by
  let X : Set (V d) := zimg N ((π ⁻¹' (F \ {0})) ∩ D)
  have hXsubNV : X ⊆ NV d N := by
    intro x hx
    dsimp [X] at hx
    rw [mem_zimg] at hx
    rcases hx with ⟨s, hs, rfl⟩
    exact smul_mem_NV s
  have hXXNL : (X - X) ∩ NL d N π.ker ⊆ ({0} : Set (V d)) := by
    dsimp [X]
    exact XX_inter_NL_sub_zero (N := N) hNpos π D hD (F := F)
  have hXNL : X ∩ NL d N π.ker = ∅ := by
    dsimp [X]
    exact X_inter_NL_empty (N := N) hNpos π D (F := F)
  have hInj1 := X_T1_inj1_of_geom (L := π.ker) (X := X) hXsubNV hG11 hXXNL
  have hDisjP : (X + T₁) ∩ T₂ = ∅ := by
    exact X_T1_disjoint_T2_of_geom (L := π.ker) (X := X) (T₁ := T₁) (T₂ := T₂)
      hXsubNV hXNL hG21
  have hA'X : AddSubgroup.IsComplement A' ((X + T₁) ∪ T₂) := by
    dsimp [X]
    exact hA'
  have hJoin : Function.Bijective (jointSum (d := d) (X + A') A' T₁ T₂) := by
    exact jointSum_bijective_of_IsComplement (X := X) (AA := A') h0A' hA'X hInj1 hDisjP
  have hLeft : (0 : V d) ∈ (X + A') ∪ A' ∧
      Function.Bijective (jointSum (d := d) (X + A') A' T₁ T₂) := ⟨Or.inr h0A', hJoin⟩
  have hRight := (hPair (X + A') A').mp hLeft
  rcases hRight with ⟨hUn, hDisj, hPer1, hPer2⟩
  constructor
  · intro a ha
    rw [← hUn]
    right
    exact ha
  · exact hPer2

end Hinge

section Reconstruction

/-- Reconstruction: if A' ⊆ NV and A' is NL-periodic then A' = N·π⁻¹(π E) with
  E := {v | N·v ∈ A'} (the fiber form). -/
lemma A'_eq_zimg_preimage {G : Type*} [AddCommGroup G] {d : ℕ}
    (π : V d →+ G) {N : ℕ}
    {A' : Set (V d)} (hA'sub : A' ⊆ NV d N)
    (hA'per : A' + NL d N π.ker = A') :
    zimg N (π ⁻¹' (π '' {v : V d | (N : ℤ) • v ∈ A'})) = A' := by
  let E : Set (V d) := {v : V d | (N : ℤ) • v ∈ A'}
  apply le_antisymm
  · -- zimg N (π⁻¹ A) ⊆ A'
    intro x hx
    rw [mem_zimg] at hx
    rcases hx with ⟨u, hu, hxu⟩
    have hπu : π u ∈ π '' E := Set.mem_preimage.mp hu
    rw [Set.mem_image] at hπu
    rcases hπu with ⟨e, heE, hπue⟩
    have hker : u - e ∈ (π.ker : Set (V d)) := by
      rw [ker_coe_mem_iff π]
      rw [map_sub, hπue]
      exact sub_self (π u)
    have hxe : (N : ℤ) • e ∈ A' := heE
    have hxnl : (N : ℤ) • (u - e) ∈ NL d N π.ker := by
      rw [NL, mem_zimg]
      exact ⟨u - e, hker, rfl⟩
    have hxmem : x ∈ A' + NL d N π.ker := by
      rw [Set.mem_add]
      refine ⟨(N : ℤ) • e, hxe, (N : ℤ) • (u - e), hxnl, ?_⟩
      calc
        (N : ℤ) • e + (N : ℤ) • (u - e) = (N : ℤ) • (e + (u - e)) := by rw [smul_add_pointwise]
        _ = (N : ℤ) • u := by congr 1; abel
        _ = x := hxu.symm
    rwa [hA'per] at hxmem
  · -- A' ⊆ zimg N (π⁻¹ A)
    intro a' ha'
    have haNV : a' ∈ NV d N := hA'sub ha'
    change a' ∈ zimg N Set.univ at haNV
    rw [mem_zimg] at haNV
    rcases haNV with ⟨t, ht, hat⟩
    have htE : t ∈ E := by
      dsimp [E]
      rw [← hat]
      exact ha'
    rw [mem_zimg]
    refine ⟨t, ?_, hat⟩
    rw [Set.mem_preimage]
    rw [Set.mem_image]
    exact ⟨t, htE, rfl⟩

end Reconstruction

section Descent

/-- Push-down: a preimage complement at the V level descends to a complement in G.
  If π⁻¹A ⊕ (π⁻¹F ∩ D) = V (D a transversal for ker π, π surjective) then A ⊕ F = G. -/
lemma complement_of_preimage_complement {G : Type*} [AddCommGroup G] {d : ℕ}
    (π : V d →+ G) (hπ : Function.Surjective π)
    (D : Set (V d)) (hD : AddSubgroup.IsComplement D (π.ker : Set (V d)))
    {A F : Set G}
    (hPF : AddSubgroup.IsComplement (π ⁻¹' A) ((π ⁻¹' F) ∩ D)) :
    AddSubgroup.IsComplement A F := by
  classical
  rw [AddSubgroup.isComplement_iff_existsUnique]
  intro g
  -- existence: pick v with πv = g and decompose via hPF
  rcases hπ g with ⟨v, hv⟩
  have hmem : v ∈ π ⁻¹' A + ((π ⁻¹' F) ∩ D) := by
    rw [hPF.add_eq]
    trivial
  rcases (Set.mem_add.mp hmem) with ⟨a0, ha0, d0, hd0, hsum0⟩
  rw [Set.mem_inter_iff] at hd0
  refine ⟨((⟨π a0, ?_⟩ : A), (⟨π d0, ?_⟩ : F)), ?_, ?_⟩
  · exact Set.mem_preimage.mp ha0
  · exact Set.mem_preimage.mp hd0.1
  · change π a0 + π d0 = g
    rw [← map_add, hsum0, hv]
  · -- uniqueness
    intro y hy
    rcases y with ⟨a', f'⟩
    have hy' : (a' : G) + (f' : G) = g := hy
    -- lift a, a', f, f' to V
    have hπa : ∃ a0v : V d, a0v ∈ π ⁻¹' A ∧ π a0v = π a0 := by
      refine ⟨a0, ha0, rfl⟩
    have hπa' : ∃ a1 : V d, a1 ∈ π ⁻¹' A ∧ π a1 = a' := by
      rcases hπ a' with ⟨a1, ha1⟩
      refine ⟨a1, ?_, ha1⟩
      rw [Set.mem_preimage]
      rw [ha1]
      exact a'.2
    have hπf : ∃ d0v : V d, d0v ∈ (π ⁻¹' F) ∩ D ∧ π d0v = π d0 := by
      refine ⟨d0, ?_, rfl⟩
      rw [Set.mem_inter_iff]
      exact ⟨hd0.1, hd0.2⟩
    have hπf' : ∃ d1 : V d, d1 ∈ (π ⁻¹' F) ∩ D ∧ π d1 = f' := by
      rcases (exists_D_of_pi π D hD hπ f') with ⟨d1, hd1D, hπd1⟩
      refine ⟨d1, ?_, hπd1⟩
      rw [Set.mem_inter_iff]
      constructor
      · rw [Set.mem_preimage, hπd1]
        exact f'.2
      · exact hd1D
    -- pair (a0,d0) with itself: just use the constructed representatives of a',f'
    rcases hπa with ⟨a0v, ha0v, hπa0v⟩
    rcases hπa' with ⟨a1, ha1, hπa1⟩
    rcases hπf with ⟨d0v, hd0v, hπd0v⟩
    rcases hπf' with ⟨d1, hd1, hπd1⟩
    have hπsum : π (a0v + d0v) = π (a1 + d1) := by
      calc
        π (a0v + d0v) = π a0 + π d0 := by rw [map_add, hπa0v, hπd0v]
        _ = g := by
          rw [← map_add π a0 d0, hsum0, hv]
        _ = a' + f' := hy'.symm
        _ = π (a1 + d1) := by rw [map_add, hπa1, hπd1]
    have hker : (a0v + d0v) - (a1 + d1) ∈ (π.ker : Set (V d)) := by
      rw [ker_coe_mem_iff π]
      rw [map_sub, hπsum]
      exact sub_self (π (a1 + d1))
    let a2 : V d := a0v - ((a0v + d0v) - (a1 + d1))
    have ha2 : a2 ∈ π ⁻¹' A := by
      have hπk : π ((a0v + d0v) - (a1 + d1)) = 0 := (ker_coe_mem_iff π _).mp hker
      have hπa2 : π a2 = π a0 := by
        dsimp [a2]
        calc
          π (a0v - ((a0v + d0v) - (a1 + d1))) = π a0v - π ((a0v + d0v) - (a1 + d1)) := by rw [map_sub]
          _ = π a0v := by rw [hπk, sub_zero]
          _ = π a0 := hπa0v
      rw [Set.mem_preimage]
      rw [hπa2]
      exact Set.mem_preimage.mp ha0
    have hsumEq : a2 + d0v = a1 + d1 := by
      dsimp [a2]
      abel
    have hpair := IsComplement_add_left_unique hPF ha2 ha1 hd0v hd1 hsumEq
    have hf_eq : π d0 = f' := by
      have hdd : d0v = d1 := hpair.2
      calc
        π d0 = π d0v := by rw [hπd0v]
        _ = π d1 := by rw [hdd]
        _ = f' := hπd1
    have hkk' : a0v - a1 = (a0v + d0v) - (a1 + d1) := by
      rw [hpair.2]
      abel
    have hker01 : π (a0v - a1) = 0 := by
      rw [hkk']
      exact (ker_coe_mem_iff π (a0v + d0v - (a1 + d1))).mp hker
    have hπa0a1 : π a0v = π a1 := by
      have h : π a0v - π a1 = 0 := by simpa [map_sub] using hker01
      exact sub_eq_zero.mp h
    have ha_eq : π a0 = a' := by
      calc
        π a0 = π a0v := hπa0v.symm
        _ = π a1 := hπa0a1
        _ = a' := hπa1
    apply Prod.ext
    · apply Subtype.ext
      exact ha_eq.symm
    · apply Subtype.ext
      exact hf_eq.symm

end Descent


/-- directness of X ⊕ A' from the complement A' of (X+T₁) ∪ T₂ (uses 0 ∈ T₁) -/
lemma X_add_A'_direct {d : ℕ} {T₁ T₂ X A' : Set (V d)}
    (h0T₁ : (0 : V d) ∈ T₁)
    (hA' : AddSubgroup.IsComplement A' ((X + T₁) ∪ T₂))
    {a b x y : V d} (ha : a ∈ A') (hb : b ∈ A') (hx : x ∈ X) (hy : y ∈ X)
    (hsum : a + x = b + y) : a = b ∧ x = y := by
  have hxmem : x ∈ (X + T₁) ∪ T₂ := by
    rw [Set.mem_union]
    left
    exact Set.mem_add.mpr ⟨x, hx, 0, h0T₁, by simp⟩
  have hymem : y ∈ (X + T₁) ∪ T₂ := by
    rw [Set.mem_union]
    left
    exact Set.mem_add.mpr ⟨y, hy, 0, h0T₁, by simp⟩
  exact IsComplement_add_left_unique hA' ha hb hxmem hymem hsum

/-- E := N⁻¹(A') is ker-periodic when A' is NL-periodic -/
lemma E_periodic_of_A'_periodic {G : Type*} [AddCommGroup G] {d : ℕ}
    (π : V d →+ G) {N : ℕ} {A' : Set (V d)}
    (hPer : A' + NL d N π.ker = A') :
    {v : V d | (N : ℤ) • v ∈ A'} + (π.ker : Set (V d)) =
      {v : V d | (N : ℤ) • v ∈ A'} := by
  classical
  apply le_antisymm
  · intro x hx
    rcases Set.mem_add.mp hx with ⟨e, he, k, hk, hsum⟩
    dsimp at he
    have hmema : (N : ℤ) • e + (N : ℤ) • k ∈ A' := by
      have hmem1 : (N : ℤ) • e + (N : ℤ) • k ∈ A' + NL d N π.ker := by
        rw [Set.mem_add]
        refine ⟨(N : ℤ) • e, he, (N : ℤ) • k, ?_, rfl⟩
        change (N : ℤ) • k ∈ zimg N (π.ker : Set (V d))
        exact mem_zimg.mpr ⟨k, hk, rfl⟩
      rwa [hPer] at hmem1
    have hEq : (N : ℤ) • x = (N : ℤ) • e + (N : ℤ) • k := by
      calc
        (N : ℤ) • x = (N : ℤ) • (e + k) := by rw [← hsum]
        _ = (N : ℤ) • e + (N : ℤ) • k := by rw [smul_add_pointwise]
    dsimp
    exact hEq.symm ▸ hmema
  · intro x hx
    dsimp at hx
    rw [Set.mem_add]
    refine ⟨x, hx, 0, ?_, ?_⟩
    · exact zero_mem_ker_set π
    · simp

/-- elements of M := (π⁻¹F) ∩ D are either in S_F or equal to the ker-representative z -/
lemma mem_M_cases {G : Type*} [AddCommGroup G] {d : ℕ}
    (π : V d →+ G) (D : Set (V d)) {F : Set G} {z : V d}
    (hz : (π ⁻¹' ({0} : Set G)) ∩ D = {z}) :
    ∀ m : V d, m ∈ (π ⁻¹' F) ∩ D →
      m ∈ (π ⁻¹' (F \ {0})) ∩ D ∨ m = z := by
  intro m hm
  rw [Set.mem_inter_iff] at hm
  rcases hm with ⟨hmF, hmD⟩
  rw [Set.mem_preimage] at hmF
  by_cases hm0 : π m = 0
  · right
    have hmm : m ∈ (π ⁻¹' ({0} : Set G)) ∩ D := by
      rw [Set.mem_inter_iff]
      exact ⟨by rw [Set.mem_preimage]; exact hm0, hmD⟩
    rw [hz] at hmm
    simpa using hmm
  · left
    rw [Set.mem_inter_iff]
    constructor
    · rw [Set.mem_preimage]
      rw [Set.mem_sdiff]
      exact ⟨hmF, hm0⟩
    · exact hmD

/-- descent: A' a complement of the lifted tile forces E := N⁻¹(A') to complement
  (π⁻¹F) ∩ D -/
lemma E_complement_M {G : Type*} [AddCommGroup G] {d : ℕ}
    (π : V d →+ G) (hπ : Function.Surjective π)
    (D : Set (V d)) (hD : AddSubgroup.IsComplement D (π.ker : Set (V d)))
    {N : ℕ} (hN : 0 < N) {T₁ T₂ : Set (V d)}
    (h0T₁ : (0 : V d) ∈ T₁) (h0T₂ : (0 : V d) ∈ T₂)
    {F : Set G} (h0F : (0 : G) ∈ F)
    {A' : Set (V d)}
    (hA' : AddSubgroup.IsComplement A'
      ((zimg N ((π ⁻¹' (F \ {0})) ∩ D) + T₁) ∪ T₂))
    (hSub : A' ⊆ NV d N)
    (hPer : A' + NL d N π.ker = A')
    (hUn : (zimg N ((π ⁻¹' (F \ {0})) ∩ D) + A') ∪ A' = NV d N)
    (hDisj : Disjoint (zimg N ((π ⁻¹' (F \ {0})) ∩ D) + A') A') :
    AddSubgroup.IsComplement {v : V d | (N : ℤ) • v ∈ A'} ((π ⁻¹' F) ∩ D) := by
  classical
  let E : Set (V d) := {v : V d | (N : ℤ) • v ∈ A'}
  have hEper : E + (π.ker : Set (V d)) = E := by
    dsimp [E]
    exact E_periodic_of_A'_periodic π hPer
  -- scaled-down disjointness: (S_F+E) ∩ E = ∅
  have hDE : (((π ⁻¹' (F \ {0})) ∩ D) + E) ∩ E = ∅ := by
    ext y
    constructor
    · intro hy
      rw [Set.mem_inter_iff] at hy
      rcases hy with ⟨hy1, hy2⟩
      rcases Set.mem_add.mp hy1 with ⟨s, hs, e, he, hse⟩
      have hmemX : (N : ℤ) • s ∈ zimg N ((π ⁻¹' (F \ {0})) ∩ D) := by
        exact mem_zimg.mpr ⟨s, hs, rfl⟩
      have hmemA : (N : ℤ) • e ∈ A' := by
        dsimp [E] at he
        exact he
      have hsum1 : (N : ℤ) • s + (N : ℤ) • e ∈
          zimg N ((π ⁻¹' (F \ {0})) ∩ D) + A' := by
        rw [Set.mem_add]
        exact ⟨(N : ℤ) • s, hmemX, (N : ℤ) • e, hmemA, rfl⟩
      have hNyeq : (N : ℤ) • s + (N : ℤ) • e = (N : ℤ) • y := by
        calc
          (N : ℤ) • s + (N : ℤ) • e = (N : ℤ) • (s + e) := by rw [smul_add_pointwise]
          _ = (N : ℤ) • y := congrArg (fun w : V d => (N : ℤ) • w) hse
      have hsum2 : (N : ℤ) • s + (N : ℤ) • e ∈ A' := by
        dsimp [E] at hy2
        rwa [hNyeq]
      have hmemC : (N : ℤ) • s + (N : ℤ) • e ∈
          (zimg N ((π ⁻¹' (F \ {0})) ∩ D) + A') ∩ A' := by
        rw [Set.mem_inter_iff]
        exact ⟨hsum1, hsum2⟩
      have hdisj' : (zimg N ((π ⁻¹' (F \ {0})) ∩ D) + A') ∩ A' = ∅ :=
        Set.disjoint_iff_inter_eq_empty.mp hDisj
      rw [hdisj'] at hmemC
      exact hmemC
    · intro hy
      exact False.elim hy
  rcases (D_inter_ker_singleton π D hD hπ) with ⟨z, hz⟩
  have hzmem : z ∈ (π ⁻¹' ({0} : Set G)) ∩ D := by
    rw [hz]
    simp
  rw [Set.mem_inter_iff] at hzmem
  have hzπ : π z = 0 := Set.mem_preimage.mp hzmem.1
  have hzD : z ∈ D := hzmem.2
  have hzker : z ∈ (π.ker : Set (V d)) := by
    rw [ker_coe_mem_iff π]
    exact hzπ
  have hzM : z ∈ (π ⁻¹' F) ∩ D := by
    rw [Set.mem_inter_iff]
    constructor
    · rw [Set.mem_preimage, hzπ]
      exact h0F
    · exact hzD
  -- uniqueness of the E ⊕ M decomposition
  have huniq : ∀ ⦃e e' m m' : V d⦄, e ∈ E → e' ∈ E →
      m ∈ (π ⁻¹' F) ∩ D → m' ∈ (π ⁻¹' F) ∩ D →
      e + m = e' + m' → e = e' ∧ m = m' := by
    intro e e' m m' he he' hm hm' hsum
    rcases mem_M_cases π D (F := F) (z := z) hz m hm with hmS | hmz
    · rcases mem_M_cases π D (F := F) (z := z) hz m' hm' with hm'S | hm'z
      · -- both in SF: directness of X ⊕ A'
        have hscaled : (N : ℤ) • e + (N : ℤ) • m = (N : ℤ) • e' + (N : ℤ) • m' := by
          calc
            (N : ℤ) • e + (N : ℤ) • m = (N : ℤ) • (e + m) := by rw [smul_add_pointwise]
            _ = (N : ℤ) • (e' + m') := congrArg (fun w : V d => (N : ℤ) • w) hsum
            _ = (N : ℤ) • e' + (N : ℤ) • m' := by rw [smul_add_pointwise]
        have heA : (N : ℤ) • e ∈ A' := by dsimp [E] at he; exact he
        have he'A : (N : ℤ) • e' ∈ A' := by dsimp [E] at he'; exact he'
        have hpair := X_add_A'_direct (T₁ := T₁) (T₂ := T₂)
          (X := zimg N ((π ⁻¹' (F \ {0})) ∩ D)) (A' := A') h0T₁ hA'
          heA he'A (mem_zimg.mpr ⟨m, hmS, rfl⟩) (mem_zimg.mpr ⟨m', hm'S, rfl⟩) hscaled
        constructor
        · exact (zsmul_injective_pointwise (N := N) hN) hpair.1
        · exact (zsmul_injective_pointwise (N := N) hN) hpair.2
      · -- m ∈ SF, m' = z : e+m = e'+z, and e'+z ∈ E but e+m ∈ SF+E: disjoint
        exfalso
        have hmem1 : e + m ∈ ((π ⁻¹' (F \ {0})) ∩ D) + E := by
          rw [Set.mem_add]
          exact ⟨m, hmS, e, he, by abel⟩
        have hez : e + m = e' + z := by
          rw [hm'z] at hsum
          exact hsum
        have hmem2 : e + m ∈ E := by
          rw [hez]
          rw [← hEper]
          rw [Set.mem_add]
          exact ⟨e', he', z, hzker, rfl⟩
        have hcon : e + m ∈ (((π ⁻¹' (F \ {0})) ∩ D) + E) ∩ E := by
          rw [Set.mem_inter_iff]
          exact ⟨hmem1, hmem2⟩
        rw [hDE] at hcon
        exact hcon
    · rcases mem_M_cases π D (F := F) (z := z) hz m' hm' with hm'S | hm'z
      · -- m = z, m' ∈ SF
        exfalso
        have hmem1 : e + m ∈ E := by
          rw [hmz]
          rw [← hEper]
          rw [Set.mem_add]
          exact ⟨e, he, z, hzker, rfl⟩
        have hmem2 : e + m ∈ ((π ⁻¹' (F \ {0})) ∩ D) + E := by
          rw [hsum]
          rw [Set.mem_add]
          exact ⟨m', hm'S, e', he', by abel⟩
        have hcon : e + m ∈ (((π ⁻¹' (F \ {0})) ∩ D) + E) ∩ E := by
          rw [Set.mem_inter_iff]
          exact ⟨hmem2, hmem1⟩
        rw [hDE] at hcon
        exact hcon
      · -- m = z, m' = z
        have hmm' : m = m' := by rw [hmz, hm'z]
        constructor
        · exact add_right_cancel (by rw [hmz, hm'z] at hsum; exact hsum)
        · exact hmm'
  -- coverage of the E ⊕ M decomposition
  rw [AddSubgroup.isComplement_iff_existsUnique]
  intro v
  have hNv : (N : ℤ) • v ∈ NV d N := by
    change (N : ℤ) • v ∈ zimg N (Set.univ : Set (V d))
    exact mem_zimg.mpr ⟨v, trivial, rfl⟩
  rw [← hUn] at hNv
  rcases hNv with hmemL | hmemR
  · rcases Set.mem_add.mp hmemL with ⟨x, hx, a, ha, hxsum⟩
    rcases (mem_zimg.mp hx) with ⟨s, hs, hxs⟩
    have haNV : a ∈ NV d N := hSub ha
    rcases (mem_zimg.mp haNV) with ⟨e, he0, hae⟩
    have heE : e ∈ E := by
      dsimp [E]
      rw [← hae]
      exact ha
    have hsM : s ∈ (π ⁻¹' F) ∩ D := by
      rw [Set.mem_inter_iff]
      constructor
      · rw [Set.mem_preimage]
        rw [Set.mem_inter_iff] at hs
        exact (Set.mem_sdiff (π s)).mp (Set.mem_preimage.mp hs.1) |>.1
      · rw [Set.mem_inter_iff] at hs
        exact hs.2
    have hEq : (N : ℤ) • (s + e) = (N : ℤ) • v := by
      calc
        (N : ℤ) • (s + e) = (N : ℤ) • s + (N : ℤ) • e := by rw [smul_add_pointwise]
        _ = x + a := by rw [hxs, hae]
        _ = (N : ℤ) • v := hxsum
    have hve : s + e = v := (zsmul_injective_pointwise (N := N) hN) hEq
    refine ⟨(⟨e, heE⟩, ⟨s, hsM⟩), ?_, ?_⟩
    · change e + s = v
      rw [add_comm]
      exact hve
    · intro y hy
      have hye : (y.1 : V d) ∈ E := y.1.2
      have hym : (y.2 : V d) ∈ (π ⁻¹' F) ∩ D := y.2.2
      have hsum' : (y.1 : V d) + (y.2 : V d) = e + s := by
        calc
          (y.1 : V d) + (y.2 : V d) = v := hy
          _ = e + s := by rw [add_comm, hve]
      have heq := huniq hye heE hym hsM hsum'
      apply Prod.ext
      · apply Subtype.ext
        exact heq.1
      · apply Subtype.ext
        exact heq.2
  · have heE : v ∈ E := by
      dsimp [E]
      exact hmemR
    have hEz : v - z ∈ E := by
      have hznegker : -z ∈ (π.ker : Set (V d)) := by
        rw [ker_coe_mem_iff π]
        simp [hzπ]
      have hmem1 : (N : ℤ) • (v - z) ∈ A' + NL d N π.ker := by
        rw [Set.mem_add]
        refine ⟨(N : ℤ) • v, hmemR, (N : ℤ) • (-z), ?_, ?_⟩
        · change (N : ℤ) • (-z) ∈ zimg N (π.ker : Set (V d))
          exact mem_zimg.mpr ⟨-z, hznegker, rfl⟩
        · change (N : ℤ) • v + (N : ℤ) • (-z) = (N : ℤ) • (v - z)
          rw [← smul_add_pointwise, sub_eq_add_neg]
      have hNvz : (N : ℤ) • (v - z) ∈ A' := by
        have h2 : (N : ℤ) • (v - z) ∈ A' := by
          rw [hPer] at hmem1
          exact hmem1
        exact h2
      dsimp [E]
      exact hNvz
    have hsumz : (v - z) + z = v := by abel
    refine ⟨(⟨v - z, hEz⟩, ⟨z, hzM⟩), ?_, ?_⟩
    · change (v - z) + z = v
      exact hsumz
    · intro y hy
      have hye : (y.1 : V d) ∈ E := y.1.2
      have hym : (y.2 : V d) ∈ (π ⁻¹' F) ∩ D := y.2.2
      have hsum' : (y.1 : V d) + (y.2 : V d) = (v - z) + z := by
        calc
          (y.1 : V d) + (y.2 : V d) = v := hy
          _ = (v - z) + z := hsumz.symm
      have heq := huniq hye hEz hym hzM hsum'
      apply Prod.ext
      · apply Subtype.ext
        exact heq.1
      · apply Subtype.ext
        exact heq.2



/-- hinge: complement A' of the lifted tile gives the NV-partition and periodicity -/
lemma backward_partition {G : Type*} [AddCommGroup G] {d : ℕ}
    (π : V d →+ G) (hπ : Function.Surjective π)
    (D : Set (V d)) (hD : AddSubgroup.IsComplement D (π.ker : Set (V d)))
    {N : ℕ} (hNpos : 0 < N) {T₁ T₂ : Set (V d)}
    (hPair : ∀ C₁ C₂ : Set (V d),
      ((0 : V d) ∈ C₁ ∪ C₂ ∧ Function.Bijective (jointSum (d := d) C₁ C₂ T₁ T₂)) ↔
      (C₁ ∪ C₂ = NV d N ∧ Disjoint C₁ C₂ ∧
        C₁ + NL d N π.ker = C₁ ∧ C₂ + NL d N π.ker = C₂))
    (hG11 : (T₁ - T₁) ∩ NV d N ⊆ NL d N π.ker)
    (hG21 : (T₂ - T₁) ∩ NV d N ⊆ NL d N π.ker)
    {F : Set G} (h0F : (0 : G) ∈ F)
    {A' : Set (V d)}
    (hA' : AddSubgroup.IsComplement A'
      ((zimg N ((π ⁻¹' (F \ {0})) ∩ D) + T₁) ∪ T₂))
    (h0A' : (0 : V d) ∈ A') :
    (zimg N ((π ⁻¹' (F \ {0})) ∩ D) + A') ∪ A' = NV d N ∧
    Disjoint (zimg N ((π ⁻¹' (F \ {0})) ∩ D) + A') A' ∧
    A' + NL d N π.ker = A' := by
  let X : Set (V d) := zimg N ((π ⁻¹' (F \ {0})) ∩ D)
  have hXsubNV : X ⊆ NV d N := by
    intro x hx
    dsimp [X] at hx
    rw [mem_zimg] at hx
    rcases hx with ⟨s, hs, rfl⟩
    exact smul_mem_NV s
  have hXXNL : (X - X) ∩ NL d N π.ker ⊆ ({0} : Set (V d)) := by
    dsimp [X]
    exact XX_inter_NL_sub_zero (N := N) hNpos π D hD (F := F)
  have hXNL : X ∩ NL d N π.ker = ∅ := by
    dsimp [X]
    exact X_inter_NL_empty (N := N) hNpos π D (F := F)
  have hInj1 := X_T1_inj1_of_geom (L := π.ker) (X := X) hXsubNV hG11 hXXNL
  have hDisjP : (X + T₁) ∩ T₂ = ∅ := by
    exact X_T1_disjoint_T2_of_geom (L := π.ker) (X := X) (T₁ := T₁) (T₂ := T₂)
      hXsubNV hXNL hG21
  have hA'X : AddSubgroup.IsComplement A' ((X + T₁) ∪ T₂) := by
    dsimp [X]
    exact hA'
  have hJoin : Function.Bijective (jointSum (d := d) (X + A') A' T₁ T₂) := by
    exact jointSum_bijective_of_IsComplement (X := X) (AA := A') h0A' hA'X hInj1 hDisjP
  have hLeft : (0 : V d) ∈ (X + A') ∪ A' ∧
      Function.Bijective (jointSum (d := d) (X + A') A' T₁ T₂) := ⟨Or.inr h0A', hJoin⟩
  have hRight := (hPair (X + A') A').mp hLeft
  rcases hRight with ⟨hUn, hDisj, hPer1, hPer2⟩
  dsimp [X] at hUn hDisj
  exact ⟨hUn, hDisj, hPer2⟩

/-- full backward direction of the tiling correspondence -/
lemma backward_descent {G : Type*} [AddCommGroup G] {d : ℕ}
    (π : V d →+ G) (hπ : Function.Surjective π)
    (D : Set (V d)) (hD : AddSubgroup.IsComplement D (π.ker : Set (V d)))
    {N : ℕ} (hNpos : 0 < N) {T₁ T₂ : Set (V d)}
    (hPair : ∀ C₁ C₂ : Set (V d),
      ((0 : V d) ∈ C₁ ∪ C₂ ∧ Function.Bijective (jointSum (d := d) C₁ C₂ T₁ T₂)) ↔
      (C₁ ∪ C₂ = NV d N ∧ Disjoint C₁ C₂ ∧
        C₁ + NL d N π.ker = C₁ ∧ C₂ + NL d N π.ker = C₂))
    (hG11 : (T₁ - T₁) ∩ NV d N ⊆ NL d N π.ker)
    (hG21 : (T₂ - T₁) ∩ NV d N ⊆ NL d N π.ker)
    (h0T₁ : (0 : V d) ∈ T₁) (h0T₂ : (0 : V d) ∈ T₂)
    {F : Set G} (h0F : (0 : G) ∈ F)
    {A' : Set (V d)}
    (hA' : AddSubgroup.IsComplement A'
      ((zimg N ((π ⁻¹' (F \ {0})) ∩ D) + T₁) ∪ T₂))
    (h0A' : (0 : V d) ∈ A') :
    ∃ A : Set G, AddSubgroup.IsComplement A F ∧ (0 : G) ∈ A ∧
      A' = zimg N (π ⁻¹' A) := by
  classical
  let E : Set (V d) := {v : V d | (N : ℤ) • v ∈ A'}
  have hP := backward_partition π hπ D hD hNpos hPair hG11 hG21 (F := F) h0F (A' := A') hA' h0A'
  rcases hP with ⟨hUn, hDisj, hPer⟩
  have hSub : A' ⊆ NV d N := by
    intro a ha
    rw [← hUn]
    right
    exact ha
  have hPF : AddSubgroup.IsComplement E ((π ⁻¹' F) ∩ D) := by
    dsimp [E]
    exact E_complement_M π hπ D hD (N := N) hNpos (T₁ := T₁) (T₂ := T₂) h0T₁ h0T₂
      (F := F) h0F (A' := A') hA' hSub hPer hUn hDisj
  let A : Set G := π '' E
  refine ⟨A, ?_, ?_, ?_⟩
  · -- IsComplement A F
    have hEper0 : E + (π.ker : Set (V d)) = E := by
      dsimp [E]
      exact E_periodic_of_A'_periodic π hPer
    have hpre : π ⁻¹' A = E := by
      dsimp [A]
      apply le_antisymm
      · intro x hx
        rw [Set.mem_preimage] at hx
        rw [Set.mem_image] at hx
        rcases hx with ⟨e, heE, hxe⟩
        have hker : x - e ∈ (π.ker : Set (V d)) := by
          rw [ker_coe_mem_iff π]
          rw [map_sub, hxe]
          exact sub_self (π x)
        have hmem : x ∈ E + (π.ker : Set (V d)) := by
          rw [Set.mem_add]
          refine ⟨e, heE, x - e, hker, ?_⟩
          abel
        rwa [hEper0] at hmem
      · intro x hx
        rw [Set.mem_preimage]
        rw [Set.mem_image]
        exact ⟨x, hx, rfl⟩
    have hPF' : AddSubgroup.IsComplement (π ⁻¹' A) ((π ⁻¹' F) ∩ D) := by
      rw [hpre]
      exact hPF
    exact complement_of_preimage_complement π hπ D hD (A := A) (F := F) hPF'
  · -- 0 ∈ A
    dsimp [A]
    rw [Set.mem_image]
    refine ⟨0, ?_, ?_⟩
    · dsimp [E]
      simpa using h0A'
    · simp
  · -- A' = zimg N (π⁻¹A)
    dsimp [A, E]
    exact (A'_eq_zimg_preimage π (A' := A') hSub hPer).symm



/-- the D-transversal part of the preimage of a finite set is finite -/
lemma preimage_transversal_finite {G : Type*} [AddCommGroup G] {d : ℕ}
    (π : V d →+ G) (D : Set (V d))
    (hD : AddSubgroup.IsComplement D (π.ker : Set (V d)))
    {F : Set G} (hF : F.Finite) : ((π ⁻¹' F) ∩ D).Finite := by
  refine Set.Finite.of_injOn (f := π) ?hm ?hi hF
  · intro x hx
    rw [Set.mem_inter_iff] at hx
    exact Set.mem_preimage.mp hx.1
  · intro x hx y hy hπ
    rw [Set.mem_inter_iff] at hx hy
    exact D_unique_of_pi_eq π D hD hx.2 hy.2 hπ


/-- canonical (def-form) rigid pair data, directly usable by the tiling reduction -/
lemma rigid_pair_data_geo' {d : ℕ} (L : AddSubgroup (V d)) :
  ∃ (N : ℕ) (T₁ T₂ : Set (V d)),
    0 < N ∧ T₁.Finite ∧ T₂.Finite ∧
    (0 : V d) ∈ T₁ ∧ (0 : V d) ∈ T₂ ∧
    (∀ C₁ C₂ : Set (V d),
      ((0 : V d) ∈ C₁ ∪ C₂ ∧ Function.Bijective (jointSum (d := d) C₁ C₂ T₁ T₂)) ↔
      (C₁ ∪ C₂ = NV d N ∧ Disjoint C₁ C₂ ∧
        C₁ + NL d N L = C₁ ∧ C₂ + NL d N L = C₂)) ∧
    (T₁ - T₁) ∩ NV d N ⊆ NL d N L ∧
    (T₂ - T₁) ∩ NV d N ⊆ NL d N L := by
  classical
  rcases rigid_pair_data_geo L with ⟨N, T, T₁, T₂,
    hNpos, hTfin, hT1fin, hT2fin, h0T, h0T1, h0T2, hR⟩
  rcases hR with ⟨hcompT, hrigidT, hT1NL, hT2NL, hPair, hG11, hG21, hG12, hG22⟩
  let rawf (C₁ C₂ : Set (V d)) :
      Sum {p : (Fin d → ℤ) × (Fin d → ℤ) | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
          {p : (Fin d → ℤ) × (Fin d → ℤ) | p.1 ∈ C₂ ∧ p.2 ∈ T₂} → Fin d → ℤ :=
    fun x => match x with
    | Sum.inl p => p.1.1 + p.1.2
    | Sum.inr p => p.1.1 + p.1.2
  refine ⟨N, T₁, T₂, hNpos, hT1fin, hT2fin, h0T1, h0T2, ?_, ?_, ?_⟩
  · intro C₁ C₂
    have hBijconv : Function.Bijective (jointSum (d := d) C₁ C₂ T₁ T₂) ↔
        Function.Bijective (rawf C₁ C₂) := by
      constructor <;> intro hbij <;> (convert hbij using 1; funext x; cases x <;> rfl)
    constructor
    · intro h
      rcases h with ⟨h0C, hBij⟩
      rcases (hPair C₁ C₂).mp ⟨h0C, (hBijconv.mp hBij)⟩ with ⟨hUn, hDisj, hC1, hC2⟩
      refine ⟨?_, hDisj, ?_, ?_⟩
      · simpa [NV, zimg] using hUn
      · simpa [NL, zimg, image2_add_add_eq] using hC1
      · simpa [NL, zimg, image2_add_add_eq] using hC2
    · intro h
      rcases h with ⟨hUn, hDisj, hC1, hC2⟩
      have hraw := (hPair C₁ C₂).mpr ⟨by simpa [NV, zimg] using hUn, hDisj,
        by simpa [NL, zimg, image2_add_add_eq] using hC1,
        by simpa [NL, zimg, image2_add_add_eq] using hC2⟩
      exact ⟨hraw.1, (hBijconv.mpr hraw.2)⟩
  · simpa [NV, NL, zimg] using hG11
  · simpa [NV, NL, zimg] using hG21

lemma tile0_from_rigid_pair
    {G : Type*} [AddCommGroup G] {d : ℕ}
    (π : (Fin d → ℤ) →+ G) (hπ : Function.Surjective π)
    (D : Set (Fin d → ℤ)) (hD : AddSubgroup.IsComplement D (π.ker : Set (Fin d → ℤ))) :
    ∃ (N : ℕ) (T₁ T₂ : Set (Fin d → ℤ)),
      T₁.Finite ∧ T₂.Finite ∧ (0 : Fin d → ℤ) ∈ T₂ ∧
      ∀ {F : Set G}, F.Finite → (0 : G) ∈ F →
        let F' : Set (Fin d → ℤ) :=
          (Set.image2 Add.add (Set.image (fun x : Fin d → ℤ => (N : ℤ) • x)
              ((π ⁻¹' (F \ {0})) ∩ D)) T₁) ∪ T₂
        F'.Finite ∧ F'.Nonempty ∧
        (∀ A : Set G, AddSubgroup.IsComplement A F → (0 : G) ∈ A →
          AddSubgroup.IsComplement
            (Set.image (fun x : Fin d → ℤ => (N : ℤ) • x) (π ⁻¹' A)) F') ∧
        (∀ A' : Set (Fin d → ℤ), AddSubgroup.IsComplement A' F' → (0 : Fin d → ℤ) ∈ A' →
          ∃ A : Set G, AddSubgroup.IsComplement A F ∧ (0 : G) ∈ A ∧
            A' = Set.image (fun x : Fin d → ℤ => (N : ℤ) • x) (π ⁻¹' A)) := by
  classical
  rcases rigid_pair_data_geo' (L := π.ker) with ⟨N, T₁, T₂,
    hNpos, hT1fin, hT2fin, h0T1, h0T2, hPair, hG11, hG21⟩
  refine ⟨N, T₁, T₂, hT1fin, hT2fin, h0T2, ?_⟩
  intro F hFfin h0F
  let F' : Set (Fin d → ℤ) :=
    (Set.image2 Add.add (Set.image (fun x : Fin d → ℤ => (N : ℤ) • x)
        ((π ⁻¹' (F \ {0})) ∩ D)) T₁) ∪ T₂
  constructor
  · -- F'.Finite
    have hSfin : ((π ⁻¹' (F \ {0})) ∩ D).Finite :=
      preimage_transversal_finite π D hD (F := F \ {0})
        (Set.Finite.subset hFfin (Set.diff_subset))
    have hzfin : (zimg N ((π ⁻¹' (F \ {0})) ∩ D)).Finite := zimg_finite hSfin
    have haddfin : (zimg N ((π ⁻¹' (F \ {0})) ∩ D) + T₁).Finite := Set.Finite.add hzfin hT1fin
    dsimp [F']
    change (((zimg N ((π ⁻¹' (F \ {0})) ∩ D)) + T₁) ∪ T₂).Finite
    exact Set.Finite.union haddfin hT2fin
  constructor
  · -- F'.Nonempty
    dsimp [F']
    rw [Set.nonempty_def]
    refine ⟨0, ?_⟩
    rw [Set.mem_union]
    exact Or.inr h0T2
  constructor
  · -- forward
    intro A hAF h0A
    have hmain := forward_tile π hπ D hD (N := N) hNpos (T₁ := T₁) (T₂ := T₂) hPair hAF h0A h0F
    dsimp [F']
    change AddSubgroup.IsComplement (zimg N (π ⁻¹' A))
      ((zimg N ((π ⁻¹' (F \ {0})) ∩ D) + T₁) ∪ T₂)
    exact hmain
  · -- backward
    intro A' hA'F' h0A'
    dsimp [F'] at hA'F'
    change AddSubgroup.IsComplement A'
      ((zimg N ((π ⁻¹' (F \ {0})) ∩ D) + T₁) ∪ T₂) at hA'F'
    rcases backward_descent π hπ D hD (N := N) hNpos (T₁ := T₁) (T₂ := T₂) hPair hG11 hG21
      h0T1 h0T2 (F := F) h0F (A' := A') hA'F' h0A' with ⟨A, hAF, h0A, hA'eq⟩
    refine ⟨A, hAF, h0A, ?_⟩
    change A' = zimg N (π ⁻¹' A)
    exact hA'eq
end
end Commons.PeriodicTiling
