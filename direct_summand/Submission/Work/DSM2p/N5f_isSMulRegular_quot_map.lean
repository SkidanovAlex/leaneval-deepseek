import Mathlib

namespace Work.DSM2p

theorem N5f_isSMulRegular_quot_map {C D : Type*} [CommRing C] [CommRing D] (φ : C →+* D)
    (π a : C)
    (hinj : ∀ c : C, φ c ∈ Ideal.span {φ π} → c ∈ Ideal.span {π})
    (hsurj : ∀ d : D, ∃ c : C, d - φ c ∈ Ideal.span {φ π})
    (ha : IsSMulRegular (C ⧸ Ideal.span {π}) (Ideal.Quotient.mk (Ideal.span {π}) a)) :
    IsSMulRegular (D ⧸ Ideal.span {φ π}) (Ideal.Quotient.mk (Ideal.span {φ π}) (φ a)) := by
  -- `φ` maps `span {π}` into `span {φ π}`, so it induces a ring hom on the quotients
  have hle : Ideal.span {π} ≤ Ideal.comap φ (Ideal.span {φ π}) := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    exact Ideal.subset_span (Set.mem_singleton _)
  let f : (C ⧸ Ideal.span {π}) →+* (D ⧸ Ideal.span {φ π}) :=
    Ideal.Quotient.lift (Ideal.span {π})
      ((Ideal.Quotient.mk (Ideal.span {φ π})).comp φ)
      (fun c hc => by
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact hle hc)
  have hf_mk : ∀ c : C, f (Ideal.Quotient.mk (Ideal.span {π}) c)
      = Ideal.Quotient.mk (Ideal.span {φ π}) (φ c) := by
    intro c
    rw [Ideal.Quotient.lift_mk]
    rfl
  have hf_inj : Function.Injective f := by
    intro x y hxy
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hf_mk, hf_mk] at hxy
    rw [Ideal.Quotient.eq] at hxy
    rw [← map_sub] at hxy
    exact Ideal.Quotient.eq.mpr (hinj (c - d) hxy)
  have hf_surj : Function.Surjective f := by
    intro d
    obtain ⟨d', rfl⟩ := Ideal.Quotient.mk_surjective d
    obtain ⟨c, hc⟩ := hsurj d'
    exact ⟨Ideal.Quotient.mk (Ideal.span {π}) c,
      by rw [hf_mk]; exact (Ideal.Quotient.eq.mpr hc).symm⟩
  -- hence the induced map is an equivalence of rings
  let e : (C ⧸ Ideal.span {π}) ≃ (D ⧸ Ideal.span {φ π}) := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have key : IsSMulRegular (C ⧸ Ideal.span {π}) (Ideal.Quotient.mk (Ideal.span {π}) a)
      ↔ IsSMulRegular (D ⧸ Ideal.span {φ π}) (Ideal.Quotient.mk (Ideal.span {φ π}) (φ a)) := by
    refine Equiv.isSMulRegular_congr (e := e) ?_
    intro x
    rw [smul_eq_mul, smul_eq_mul]
    change f (Ideal.Quotient.mk (Ideal.span {π}) a * x)
      = Ideal.Quotient.mk (Ideal.span {φ π}) (φ a) * f x
    rw [map_mul, hf_mk]
  exact key.mp ha

end Work.DSM2p
