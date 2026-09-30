import Mathlib
import Submission.Work.Pi6.SRANGE.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.SRANGE

/-- `Submodule.mapQ p q f h` is bijective iff `f` is injective modulo `p,q` and
surjective modulo `q`. -/
theorem bijective_mapQ_iff {R : Type} [CommRing R] {M M' : Type} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (p : Submodule R M) (q : Submodule R M') (f : M →ₗ[R] M')
    (h : p ≤ Submodule.comap f q) :
    Function.Bijective (Submodule.mapQ p q f h) ↔
      (∀ x y : M, f x - f y ∈ q → x - y ∈ p) ∧ (∀ w : M', ∃ x : M, f x - w ∈ q) := by
  constructor
  · intro hbij
    refine ⟨fun x y hxy => ?_, fun w => ?_⟩
    · have : (Submodule.mapQ p q f h) (Submodule.Quotient.mk x)
          = (Submodule.mapQ p q f h) (Submodule.Quotient.mk y) := by
        rw [Submodule.mapQ_apply, Submodule.mapQ_apply]
        exact (Submodule.Quotient.eq q).mpr hxy
      exact (Submodule.Quotient.eq p).mp (hbij.1 this)
    · obtain ⟨a, ha⟩ := hbij.2 (Submodule.Quotient.mk w : M' ⧸ q)
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective p a
      rw [Submodule.mapQ_apply] at ha
      exact ⟨x, (Submodule.Quotient.eq q).mp ha⟩
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun a b hab => ?_, fun c => ?_⟩
    · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective p a
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective p b
      rw [Submodule.mapQ_apply, Submodule.mapQ_apply] at hab
      exact (Submodule.Quotient.eq p).mpr (hinj x y ((Submodule.Quotient.eq q).mp hab))
    · obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective q c
      obtain ⟨x, hx⟩ := hsurj w
      exact ⟨Submodule.Quotient.mk x,
        by rw [Submodule.mapQ_apply]; exact (Submodule.Quotient.eq q).mpr hx⟩

end Work.Pi6.SRANGE
