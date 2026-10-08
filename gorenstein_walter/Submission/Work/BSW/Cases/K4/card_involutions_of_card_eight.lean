import Mathlib

namespace Work.BSW.Cases.K4

open scoped Pointwise

/-- A subgroup of order `4` is commutative (it is a group of order `p^2`). -/
private lemma comm_of_mem_card_four {S : Type*} [Group S] (W : Subgroup S)
    (hW : Nat.card ↥W = 4) : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
  haveI : IsMulCommutative ↥W :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hW]; norm_num)
  intro a ha b hb
  have := mul_comm' (⟨a, ha⟩ : W) (⟨b, hb⟩ : W)
  simpa using congr_arg Subtype.val this

/-- If `g` commutes with every element of a commutative `W ≤ S`, and every element of `S`
lies in `W` or in the coset `gW`, then `S` is commutative. -/
private lemma comm_of_comm_coset {S : Type*} [Group S] (W : Subgroup S) [W.Normal] (g : S)
    (hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hdecomp : ∀ x : S, x ∈ W ∨ ∃ w : W, x = g * (w : S))
    (hgc : ∀ w : W, g * (w : S) = (w : S) * g) :
    ∀ x y : S, x * y = y * x := by
  intro x y
  rcases hdecomp x with hx | ⟨a, rfl⟩
  · rcases hdecomp y with hy | ⟨b, rfl⟩
    · exact hWcomm x hx y hy
    · calc x * (g * (b : S)) = (x * g) * (b : S) := by group
        _ = (g * x) * (b : S) := by rw [(hgc ⟨x, hx⟩).symm]
        _ = g * (x * (b : S)) := by group
        _ = g * ((b : S) * x) := by rw [hWcomm x hx (b : S) b.2]
        _ = (g * (b : S)) * x := by group
  · rcases hdecomp y with hy | ⟨b, rfl⟩
    · calc (g * (a : S)) * y = g * ((a : S) * y) := by group
        _ = g * (y * (a : S)) := by rw [hWcomm (a : S) a.2 y hy]
        _ = (g * y) * (a : S) := by group
        _ = (y * g) * (a : S) := by rw [hgc ⟨y, hy⟩]
        _ = y * (g * (a : S)) := by group
    · calc (g * (a : S)) * (g * (b : S)) = g * ((a : S) * g) * (b : S) := by group
        _ = g * (g * (a : S)) * (b : S) := by rw [← hgc ⟨a, a.2⟩]
        _ = (g * (g * (a : S))) * (b : S) := by group
        _ = (g * g) * ((a : S) * (b : S)) := by group
        _ = (g * g) * ((b : S) * (a : S)) := by rw [hWcomm (a : S) a.2 (b : S) b.2]
        _ = (g * (g * (b : S))) * (a : S) := by group
        _ = g * ((b : S) * g) * (a : S) := by rw [hgc ⟨b, b.2⟩]
        _ = (g * (b : S)) * (g * (a : S)) := by group

/-- If conjugation by `g` is trivial on `W`, then `S` is commutative. -/
private lemma comm_of_conjNormal_eq_one {S : Type*} [Group S] (W : Subgroup S) [W.Normal]
    (g : S)
    (hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hdecomp : ∀ x : S, x ∈ W ∨ ∃ w : W, x = g * (w : S))
    (hcon : MulAut.conjNormal (H := W) g = 1) :
    ∀ x y : S, x * y = y * x := by
  have hgc : ∀ w : W, g * (w : S) = (w : S) * g := by
    intro w
    have h1 : MulAut.conjNormal (H := W) g w = w := by rw [hcon]; rfl
    have h2 : g * (w : S) * g⁻¹ = (w : S) := by
      have := congr_arg Subtype.val h1
      simpa only [MulAut.conjNormal_apply] using this
    calc g * (w : S) = (g * (w : S) * g⁻¹) * g := by group
      _ = (w : S) * g := by rw [h2]
  exact comm_of_comm_coset W g hWcomm hdecomp hgc

theorem card_involutions_of_card_eight {S : Type*} [Group S] [Finite S]
    (hcard : Nat.card S = 8) (hnonab : ¬ IsMulCommutative S)
    (W : Subgroup S) (hW : Nat.card ↥W = 4) (hWsq : ∀ w ∈ W, w * w = 1) :
    {x : S | orderOf x = 2}.ncard = 5 := by
  classical
  -- `W` has index two, hence is normal.
  have hidx : W.index = 2 := by
    have h := Subgroup.card_mul_index W
    rw [hW, hcard] at h
    omega
  haveI : W.Normal := Subgroup.normal_of_index_eq_two hidx
  -- Commutativity of `W`.
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := comm_of_mem_card_four W hW
  have hWsqW : ∀ w : W, w * w = 1 := fun w => by
    apply Subtype.ext; exact hWsq w w.2
  -- Pick `g ∉ W`.
  obtain ⟨g, hgW, hpart⟩ := Subgroup.index_eq_two_iff_exists_notMem_and'.mp hidx
  have hg2 : g * g ∈ W := Subgroup.mul_self_mem_of_index_two hidx g
  -- Every element lies in `W` or satisfies `g⁻¹·x ∈ W`.
  have hcover : ∀ x : S, x ∈ W ∨ g⁻¹ * x ∈ W := by
    intro x
    rcases hpart x with h | h
    · right
      have : g⁻¹ * x = (g * g)⁻¹ * (g * x) := by group
      rw [this]
      exact W.mul_mem (W.inv_mem hg2) h
    · exact Or.inl h
  have hdecomp : ∀ x : S, x ∈ W ∨ ∃ w : W, x = g * (w : S) := by
    intro x
    rcases hcover x with h | h
    · exact Or.inl h
    · exact Or.inr ⟨⟨g⁻¹ * x, h⟩, by simp⟩
  -- Conjugation by `g` on `W` is not the identity, else `S` would be commutative.
  have hphi_ne : MulAut.conjNormal (H := W) g ≠ 1 := by
    intro hcon
    exact hnonab (IsMulCommutative.of_comm (comm_of_conjNormal_eq_one W g hWcomm hdecomp hcon))
  -- Conjugation by `g` is an involution on `W`.
  have hphi2 : ∀ w : W, MulAut.conjNormal (H := W) g (MulAut.conjNormal (H := W) g w) = w := by
    intro w
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply]
    have h1 : g * (g * (w : S) * g⁻¹) * g⁻¹ = (g * g) * (w : S) * (g * g)⁻¹ := by group
    rw [h1, hWcomm (g * g) hg2 (w : S) w.2]
    group
  -- The map `ψ w = φ(w) · w`.
  haveI hWmc : IsMulCommutative W :=
    IsMulCommutative.of_comm (fun a b => by
      apply Subtype.ext; exact hWcomm a a.2 b b.2)
  let psi : W →* W :=
    { toFun := fun w => MulAut.conjNormal (H := W) g w * w
      map_one' := by simp
      map_mul' := by intro a b; simp only [map_mul]; ac_rfl }
  have psi_apply : ∀ w : W, psi w = MulAut.conjNormal (H := W) g w * w := fun w => rfl
  -- `t = g²`.
  let t : W := ⟨g * g, hg2⟩
  -- `ψ ∘ φ = ψ`.
  have hpsi_phi : ∀ w : W, psi (MulAut.conjNormal (H := W) g w) = psi w := by
    intro w
    simp only [psi_apply]
    rw [hphi2 w]
    exact mul_comm' _ _
  -- `ψ w` is an involution.
  have hpsi_sq : ∀ w : W, psi w * psi w = 1 := by
    intro w
    have h1 : MulAut.conjNormal (H := W) g w * MulAut.conjNormal (H := W) g w = 1 := by
      apply Subtype.ext; exact hWsq _ (MulAut.conjNormal (H := W) g w).2
    have h2 : w * w = 1 := hWsqW w
    rw [psi_apply]
    calc (MulAut.conjNormal (H := W) g w * w) * (MulAut.conjNormal (H := W) g w * w)
        = (MulAut.conjNormal (H := W) g w * MulAut.conjNormal (H := W) g w) * (w * w) := by ac_rfl
      _ = 1 := by rw [h1, h2, one_mul]
  -- The range of `ψ` lies in its kernel.
  have hrange_le_ker : psi.range ≤ psi.ker := by
    rintro x ⟨w, rfl⟩
    rw [MonoidHom.mem_ker]
    rw [show psi w = MulAut.conjNormal (H := W) g w * w from psi_apply w]
    rw [map_mul, hpsi_phi w]
    exact hpsi_sq w
  -- `ψ ≠ 1`.
  have hpsi_ne_one : psi ≠ 1 := by
    intro hpsi
    apply hphi_ne
    apply MulEquiv.ext
    intro w
    have h2 : MulAut.conjNormal (H := W) g w * w = 1 := by
      have h : psi w = 1 := by rw [hpsi]; exact MonoidHom.one_apply w
      rwa [psi_apply] at h
    have hw2 : w * w = 1 := hWsqW w
    calc MulAut.conjNormal (H := W) g w = MulAut.conjNormal (H := W) g w * 1 := (mul_one _).symm
      _ = MulAut.conjNormal (H := W) g w * (w * w) := by rw [hw2]
      _ = (MulAut.conjNormal (H := W) g w * w) * w := (mul_assoc _ _ _).symm
      _ = 1 * w := by rw [h2]
      _ = w := one_mul w
  have hker_ne_top : psi.ker ≠ ⊤ := by
    intro htop
    apply hpsi_ne_one
    refine MonoidHom.ext (fun w => ?_)
    have h : psi w = 1 := by
      have hk : w ∈ psi.ker := by rw [htop]; trivial
      rwa [MonoidHom.mem_ker] at hk
    rw [h, MonoidHom.one_apply]
  -- `|ker ψ| = |range ψ| = 2`.
  have hmul : Nat.card psi.ker * Nat.card psi.range = 4 := by
    have h := Subgroup.card_ker_mul_card_range psi
    rwa [hW] at h
  have hle : Nat.card psi.range ≤ Nat.card psi.ker := Subgroup.card_le_of_le hrange_le_ker
  have hne : Nat.card psi.ker ≠ 4 := by
    intro h4
    exact hker_ne_top ((Subgroup.card_eq_iff_eq_top psi.ker).mp (by rw [h4, hW]))
  have ha : 0 < Nat.card psi.ker := Nat.card_pos
  have hcardker : Nat.card psi.ker = 2 := by
    have hd : Nat.card psi.ker ∣ 4 := ⟨Nat.card psi.range, hmul.symm⟩
    have h4 : Nat.card psi.ker ≤ 4 := Nat.le_of_dvd (by norm_num) hd
    interval_cases h : Nat.card psi.ker
    all_goals omega
  have hcardrange : Nat.card psi.range = 2 := by
    rw [hcardker] at hmul; omega
  have hker_eq_range : psi.range = psi.ker :=
    Subgroup.eq_of_le_of_card_ge hrange_le_ker (by omega)
  -- `t ∈ ker ψ`.
  have hphi_t : MulAut.conjNormal (H := W) g t = t := by
    apply Subtype.ext
    show g * (g * g) * g⁻¹ = g * g
    group
  have htker : psi t = 1 := by
    rw [psi_apply, hphi_t]
    apply Subtype.ext
    exact hWsq (g * g) hg2
  have ht_range : t ∈ psi.range := by
    rw [hker_eq_range]; exact htker
  obtain ⟨w0, hw0⟩ := MonoidHom.mem_range.mp ht_range
  -- The fiber of `ψ` above `t` has two elements.
  have hfiber : {w : W | psi w = t}.ncard = 2 := by
    have hinj : Function.Injective (fun k : W => w0 * k) := fun a b h => mul_left_cancel h
    have hsetf : {w : W | psi w = t} = (fun k : W => w0 * k) '' (psi.ker : Set W) := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe]
      constructor
      · intro hw
        refine ⟨w0⁻¹ * w, ?_, ?_⟩
        · rw [MonoidHom.mem_ker, map_mul, map_inv, hw0, hw, inv_mul_cancel]
        · group
      · rintro ⟨k, hk, rfl⟩
        rw [MonoidHom.mem_ker] at hk
        rw [map_mul, hw0, hk, mul_one]
    rw [hsetf, Set.ncard_image_of_injective _ hinj]
    rw [show (psi.ker : Set W).ncard = Nat.card psi.ker from rfl, hcardker]
  -- `(g·w)² = t · ψ w` in `S`.
  have hsq : ∀ w : W, (g * (w : S)) * (g * (w : S)) = (t : S) * (psi w : S) := by
    intro w
    have hphi : (g * (w : S) * g⁻¹) = ((MulAut.conjNormal (H := W) g w : W) : S) := by
      rw [MulAut.conjNormal_apply]
    calc (g * (w : S)) * (g * (w : S)) = (g * (w : S) * g⁻¹) * (g * g) * (w : S) := by group
      _ = ((MulAut.conjNormal (H := W) g w : W) : S) * (g * g) * (w : S) := by rw [hphi]
      _ = (g * g) * (((MulAut.conjNormal (H := W) g w : W) : S) * (w : S)) := by
            rw [← hWcomm (g * g) hg2 ((MulAut.conjNormal (H := W) g w : W) : S)
              (MulAut.conjNormal (H := W) g w).2]
            group
      _ = ((⟨g * g, hg2⟩ : W) : S) * (psi w : S) := rfl
  -- The set of elements of order two.
  set E : Set S := {x : S | orderOf x = 2} with hE
  set cW : Set S := {x : S | g⁻¹ * x ∈ W} with hcW
  have huni : (W : Set S) ∪ cW = Set.univ := by
    ext x
    rw [hcW]
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact hcover x
  have hdisj : Disjoint (W : Set S) cW := by
    rw [Set.disjoint_left]
    intro x hx hcx
    rw [hcW] at hcx
    have hginv : g⁻¹ ∈ W := by
      have : g⁻¹ = (g⁻¹ * x) * x⁻¹ := by group
      rw [this]
      exact W.mul_mem hcx (W.inv_mem hx)
    exact hgW (by simpa using W.inv_mem hginv)
  have hE_part : E = (E ∩ (W : Set S)) ∪ (E ∩ cW) := by
    rw [← Set.inter_union_distrib_left, huni, Set.inter_univ]
  -- `|E ∩ W| = 3`.
  have horderW : ∀ x : S, x ∈ W → (orderOf x = 2 ↔ x ≠ 1) := by
    intro x hx
    constructor
    · intro h h1
      rw [h1, orderOf_one] at h
      exact absurd h (by norm_num)
    · intro hx1
      have hx2 : x * x = 1 := hWsq x hx
      have hdvd : orderOf x ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hx2)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact absurd (orderOf_eq_one_iff.mp h1) hx1
      · exact h2
  have hE1 : (E ∩ (W : Set S)).ncard = 3 := by
    have hset1 : E ∩ (W : Set S) = (W : Set S) \ {1} := by
      ext x
      rw [hE]
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hord, hxw⟩
        exact ⟨hxw, fun hx1 => by
          rw [hx1, orderOf_one] at hord; exact absurd hord (by norm_num)⟩
      · rintro ⟨hxw, hx1⟩
        exact ⟨(horderW x hxw).mpr hx1, hxw⟩
    rw [hset1, Set.ncard_sdiff_singleton_of_mem W.one_mem]
    have h4 : (W : Set S).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hW
    rw [h4]
  -- `|E ∩ cW| = 2` via the fiber of `ψ`.
  have hE2 : (E ∩ cW).ncard = 2 := by
    have hset2 : E ∩ cW = (fun w : W => g * (w : S)) '' {w : W | psi w = t} := by
      ext x
      rw [hE, hcW]
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_image]
      constructor
      · rintro ⟨hord, hgx⟩
        obtain ⟨w', hw'⟩ : ∃ w' : W, g * (w' : S) = x := ⟨⟨g⁻¹ * x, hgx⟩, by simp⟩
        refine ⟨w', ?_, hw'⟩
        have hx2 : x * x = 1 := by
          have h := pow_orderOf_eq_one x
          rw [hord, pow_two] at h; exact h
        have hx2' : (g * (w' : S)) * (g * (w' : S)) = 1 := by rw [hw']; exact hx2
        have h1 : (t : S) * (psi w' : S) = 1 := (hsq w').symm.trans hx2'
        have h2 : t * psi w' = 1 := by apply Subtype.ext; exact h1
        have htt : t * t = 1 := hWsqW t
        calc psi w' = 1 * psi w' := (one_mul _).symm
          _ = (t * t) * psi w' := by rw [htt]
          _ = t * (t * psi w') := by rw [mul_assoc]
          _ = t * 1 := by rw [h2]
          _ = t := mul_one t
      · rintro ⟨w, hw, rfl⟩
        refine ⟨?_, ?_⟩
        · have htt : (t : S) * (t : S) = 1 := congr_arg Subtype.val (hWsqW t)
          have hx2 : (g * (w : S)) * (g * (w : S)) = 1 := by
            rw [hsq w, hw, htt]
          have hdvd : orderOf (g * (w : S)) ∣ 2 :=
            orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hx2)
          rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
          · exfalso
            have hgw : g * (w : S) = 1 := orderOf_eq_one_iff.mp h1
            have hge : g = ((w : S))⁻¹ := by
              calc g = g * (w : S) * ((w : S))⁻¹ := by group
                _ = 1 * ((w : S))⁻¹ := by rw [hgw]
                _ = ((w : S))⁻¹ := one_mul _
            exact hgW (by rw [hge]; exact W.inv_mem w.2)
          · exact h2
        · show g⁻¹ * (g * (w : S)) ∈ W
          rw [show g⁻¹ * (g * (w : S)) = (w : S) from by group]
          exact w.2
    rw [hset2, Set.ncard_image_of_injective _
      (fun a b h => Subtype.ext (mul_left_cancel h))]
    exact hfiber
  have hcount : E.ncard = (E ∩ (W : Set S)).ncard + (E ∩ cW).ncard := by
    have hd : Disjoint (E ∩ (W : Set S)) (E ∩ cW) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact Set.disjoint_left.mp hdisj hx.2 hx'.2
    calc E.ncard = ((E ∩ (W : Set S)) ∪ (E ∩ cW)).ncard := by
          conv_lhs => rw [hE_part]
      _ = (E ∩ (W : Set S)).ncard + (E ∩ cW).ncard := Set.ncard_union_eq hd
  rw [hE1, hE2] at hcount
  omega

end Work.BSW.Cases.K4
