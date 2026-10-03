import Mathlib

namespace Work.ORBassSerre.FP

open Monoid Coprod Multiplicative

/-- An HNN extension of a finitely presented group along finitely generated associated
subgroups is finitely presented.

Indeed, `HNNExtension G A B φ` is the quotient of the free product `G ∗ ℤ` by the normal
closure of the relations `t * a * (φ a * t)⁻¹` for `a` ranging over a finite generating
set of `A`; the relations for all of `A` follow from those. -/
theorem hnn_isFinitelyPresented {G : Type*} [Group G] [Group.IsFinitelyPresented G]
    (A B : Subgroup G) [Group.FG A] [Group.FG B] (φ : A ≃* B) :
    Group.IsFinitelyPresented (HNNExtension G A B φ) := by
  obtain ⟨s, hs_closure, hs_fin⟩ := Group.fg_iff.1 (inferInstance : Group.FG A)
  let K := G ∗ Multiplicative ℤ
  let t : K := Coprod.inr (Multiplicative.ofAdd (1 : ℤ))
  let w : A → K := fun a => (t * Coprod.inl (a : G)) * (Coprod.inl (((φ a : B) : G)) * t)⁻¹
  let N : Subgroup K := Subgroup.normalClosure (w '' s)
  have hN : N.Normal := Subgroup.normalClosure_normal
  let q : K →* K ⧸ N := QuotientGroup.mk' N
  -- In the quotient by `N`, conjugation by `t` implements `φ` on all of `A`.
  have hx : ∀ a : A, q t * q (Coprod.inl (a : G)) = q (Coprod.inl (((φ a : B) : G))) * q t := by
    intro a
    have ha : a ∈ Subgroup.closure s := by rw [hs_closure]; exact Subgroup.mem_top a
    refine Subgroup.closure_induction (G := A) (k := s) (p := fun b _ =>
      q t * q (Coprod.inl (b : G)) = q (Coprod.inl (((φ b : B) : G))) * q t) ?_ ?_ ?_ ?_ ha
    · intro b hb
      have hmem : w b ∈ N := Subgroup.subset_normalClosure (Set.mem_image_of_mem w hb)
      have h1 : q (w b) = 1 := (QuotientGroup.eq_one_iff (w b)).2 hmem
      have h2 : q ((t * Coprod.inl (b : G)) * (Coprod.inl (((φ b : B) : G)) * t)⁻¹) = 1 := by
        simpa only [w] using h1
      rw [map_mul, map_inv] at h2
      have h3 : q (t * Coprod.inl (b : G)) = q (Coprod.inl (((φ b : B) : G)) * t) :=
        mul_inv_eq_one.1 h2
      rw [← map_mul, h3, map_mul]
    · simp
    · intro b c hb hc ihb ihc
      have hbc : q (Coprod.inl ((b * c : A) : G)) =
          q (Coprod.inl (b : G)) * q (Coprod.inl (c : G)) := by
        simp only [Subgroup.coe_mul, map_mul]
      have hphi : q (Coprod.inl (((φ (b * c) : B) : G))) =
          q (Coprod.inl (((φ b : B) : G))) * q (Coprod.inl (((φ c : B) : G))) := by
        simp only [map_mul, Subgroup.coe_mul]
      rw [hbc, hphi, ← mul_assoc, ihb, mul_assoc, ihc, mul_assoc]
    · intro b hb ihb
      have hbinv : q (Coprod.inl ((b⁻¹ : A) : G)) = (q (Coprod.inl (b : G)))⁻¹ := by
        simp only [Subgroup.coe_inv, map_inv]
      have hphi : q (Coprod.inl (((φ (b⁻¹) : B) : G))) =
          (q (Coprod.inl (((φ b : B) : G))))⁻¹ := by
        simp only [map_inv, Subgroup.coe_inv]
      have hb' : q (Coprod.inl (b : G)) =
          (q t)⁻¹ * q (Coprod.inl (((φ b : B) : G))) * q t := by
        calc q (Coprod.inl (b : G)) = (q t)⁻¹ * (q t * q (Coprod.inl (b : G))) := by group
          _ = (q t)⁻¹ * (q (Coprod.inl (((φ b : B) : G))) * q t) := by rw [ihb]
          _ = (q t)⁻¹ * q (Coprod.inl (((φ b : B) : G))) * q t := by group
      rw [hbinv, hphi, hb']
      group
  let g : HNNExtension G A B φ →* K ⧸ N := HNNExtension.lift (q.comp Coprod.inl) (q t) hx
  let f : K →* HNNExtension G A B φ := (HNNExtension.con G A B φ).mk'
  -- The coproduct lift defining `g` is exactly `q`.
  have hF : Coprod.lift (q.comp Coprod.inl) (zpowersHom (K ⧸ N) (q t)) = q := by
    apply Coprod.hom_ext
    · rw [Coprod.lift_comp_inl]
    · rw [Coprod.lift_comp_inr]
      apply MonoidHom.ext_mint
      simp [zpowersHom_apply, t]
  have hsurj : Function.Surjective f := Con.mk'_surjective (c := HNNExtension.con G A B φ)
  have hker_le : f.ker ≤ N := by
    intro y hy
    have hy1 : f y = 1 := MonoidHom.mem_ker.1 hy
    have h1 : g (f y) = Coprod.lift (q.comp Coprod.inl) (zpowersHom (K ⧸ N) (q t)) y :=
      Con.lift_mk' _ y
    have h2 : Coprod.lift (q.comp Coprod.inl) (zpowersHom (K ⧸ N) (q t)) y = 1 := by
      rw [← h1, hy1, map_one]
    have h3 : q y = 1 := by rw [← hF]; exact h2
    exact (QuotientGroup.eq_one_iff y).1 h3
  have hN_le : N ≤ f.ker := by
    show Subgroup.normalClosure (w '' s) ≤ f.ker
    apply Subgroup.normalClosure_le_normal
    rintro x ⟨a, ha, rfl⟩
    apply MonoidHom.mem_ker.2
    have hA : f (t * Coprod.inl (a : G)) = HNNExtension.t * HNNExtension.of (a : G) := by
      rw [map_mul]; rfl
    have hB : f (Coprod.inl (((φ a : B) : G)) * t) =
        HNNExtension.of (((φ a : B) : G)) * HNNExtension.t := by
      rw [map_mul]; rfl
    have hw : f (w a) =
        f (t * Coprod.inl (a : G)) * (f (Coprod.inl (((φ a : B) : G)) * t))⁻¹ := by
      rw [show w a = (t * Coprod.inl (a : G)) * (Coprod.inl (((φ a : B) : G)) * t)⁻¹
          from rfl, map_mul, map_inv]
    rw [hw, hA, hB, HNNExtension.t_mul_of a, mul_inv_cancel]
  have hker_eq : f.ker = N := le_antisymm hker_le hN_le
  have hker : f.ker.IsFinitelyNormallyGenerated := by
    refine ⟨w '' s, hs_fin.image w, ?_⟩
    rw [hker_eq]
  exact Group.IsFinitelyPresented.of_surjective f hsurj hker

end Work.ORBassSerre.FP
