import Mathlib

namespace Work.BMAX

theorem InvolutionInverts {G : Type} [Group G] (N : Subgroup G) (t : G)
    [Finite N] (ht : t * t = 1) (htN : t ∈ Subgroup.normalizer (N : Set G))
    (hfix : ∀ x ∈ N, t * x * t⁻¹ = x → x = 1) :
    ∀ x ∈ N, t * x * t⁻¹ = x⁻¹ := by
  -- The conjugation action of the involution `t` restricts to a fixed-point-free
  -- automorphism of `N`; a finite group with a fixed-point-free automorphism of
  -- order two is abelian and that automorphism is inversion.
  have hmem : ∀ x ∈ N, t * x * t⁻¹ ∈ N := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp htN x).mp hx
  -- `c` is conjugation by `t` on `G`.
  let c : MulAut G := MulAut.conj t
  have hc : ∀ y : G, c y = t * y * t⁻¹ := fun y => MulAut.conj_apply t y
  -- `t` is an involution, so `c` is an involution.
  have hcc : c * c = 1 := by
    simp only [c]
    rw [← map_mul, ht, map_one]
  have hcc_apply : ∀ y : G, c (c y) = y := by
    intro y
    have h := MulAut.mul_apply G c c y
    rw [hcc, MulAut.one_apply] at h
    exact h.symm
  -- `F` is the conjugation action of `t` on `N`.
  let F : N → N := fun x => ⟨c (x : G), by rw [hc]; exact hmem x x.2⟩
  -- `β x = x⁻¹ · xᵗ` is injective, because `β x = β y` forces `x y⁻¹` to be fixed by `c`.
  let β : N → N := fun x => x⁻¹ * F x
  have hβ_inj : Function.Injective β := by
    intro x y hxy
    have h1 : ((x : G))⁻¹ * c (x : G) = ((y : G))⁻¹ * c (y : G) := by
      have := congrArg (Subtype.val) hxy
      simpa [β, F] using this
    have h2 : c ((x : G) * (y : G)⁻¹) = (x : G) * (y : G)⁻¹ := by
      have h3 : c (x : G) = (x : G) * ((y : G)⁻¹ * c (y : G)) := by
        have := congrArg (fun w => (x : G) * w) h1
        simpa only [mul_inv_cancel_left] using this
      rw [map_mul, map_inv, h3]
      group
    have h4 : t * ((x : G) * (y : G)⁻¹) * t⁻¹ = (x : G) * (y : G)⁻¹ := by
      have := h2
      rwa [hc] at this
    have h5 : (x : G) * (y : G)⁻¹ = 1 :=
      hfix _ (mul_mem x.2 (inv_mem y.2)) h4
    have hxy' : (x : G) = (y : G) := by rwa [mul_inv_eq_one] at h5
    exact Subtype.ext hxy'
  have hβ_surj : Function.Surjective β :=
    (Finite.injective_iff_surjective).mp hβ_inj
  -- `F` inverts every element in the image of `β`.
  have hFβ : ∀ x : N, F (β x) = (β x)⁻¹ := by
    intro x
    apply Subtype.ext
    change c ((β x : N) : G) = (((β x : N) : G))⁻¹
    have hbx : ((β x : N) : G) = ((x : G))⁻¹ * c (x : G) := by simp [β, F]
    rw [hbx, map_mul, map_inv]
    rw [mul_inv_rev, inv_inv]
    rw [hcc_apply]
  -- Since `β` is surjective, `F` inverts everything.
  intro x hx
  let y : N := ⟨x, hx⟩
  obtain ⟨w, hw⟩ := hβ_surj y
  have hFy : F y = y⁻¹ := by rw [← hw]; exact hFβ w
  have hcy : c (y : G) = ((y : G))⁻¹ := by
    have := congrArg (Subtype.val) hFy
    simpa [F] using this
  rw [← hc x]
  simpa using hcy

end Work.BMAX
