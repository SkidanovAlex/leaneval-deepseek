import Mathlib
import Submission.Work.Tower.Unramified.MaxElemAb
import Submission.Work.Tower.Unramified.maxElemAbUnram3_isUnramified

/-!
# The maximal elementary abelian unramified `3`-extension has `3`-power degree

When `maxElemAbUnram3 F` is finite over `F`, it is Galois with every automorphism of order
dividing `3`; by Cauchy's theorem its Galois group is therefore a `3`-group, so its order (and
hence the degree `[maxElemAbUnram3 F : F]`) is a power of `3`.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work
namespace Tower
namespace Unramified

theorem finrank_maxElemAbUnram3_eq_pow_three (F : Type*) [Field F] [NumberField F]
    (hfin : FiniteDimensional F ↥(Work.Tower.maxElemAbUnram3 F)) :
    ∃ m : ℕ, Module.finrank F ↥(Work.Tower.maxElemAbUnram3 F) = 3 ^ m := by
  have h := maxElemAbUnram3_isElementaryAbelianThreeExtension F hfin
  haveI : IsGalois F ↥(Work.Tower.maxElemAbUnram3 F) := h.1
  have hpow : ∀ σ : Gal(↥(Work.Tower.maxElemAbUnram3 F)/F), σ ^ 3 = 1 := h.2
  have hexp : Monoid.exponent (Gal(↥(Work.Tower.maxElemAbUnram3 F)/F)) ∣ 3 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow
  have hpgrp : IsPGroup 3 (Gal(↥(Work.Tower.maxElemAbUnram3 F)/F)) :=
    IsPGroup.of_exponent_dvd_pow (n := 1) (by simpa using hexp)
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 3) (G := Gal(↥(Work.Tower.maxElemAbUnram3 F)/F))).mp
    hpgrp
  exact ⟨m, by rw [← IsGalois.card_aut_eq_finrank F ↥(Work.Tower.maxElemAbUnram3 F)]; exact hm⟩

end Unramified
end Tower
end Work
