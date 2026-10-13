import Mathlib
import Submission.Work.DSM2p.Basic

namespace Work.DSM2p

/-- The level-`1` reduction `AdicCompletion I E →ₐ E ⧸ I ^ 1` has the same kernel as the
canonical projection `evalOneₐ : AdicCompletion I E →ₐ E ⧸ I`.  The two maps differ only by the
quotient map `Ideal.Quotient.factor (I ^ 1 ≤ I)`, which is bijective since `I ^ 1 = I`; hence
they have equal kernels. -/
theorem ker_evalₐ_one_eq_ker_evalOneₐ {E : Type*} [CommRing E] (I : Ideal E) :
    RingHom.ker (AdicCompletion.evalₐ I 1).toRingHom =
      RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom := by
  ext x
  simp only [RingHom.mem_ker]
  change (AdicCompletion.evalₐ I 1) x = 0 ↔ (AdicCompletion.evalOneₐ I) x = 0
  constructor
  · intro hx
    have h := AdicCompletion.factorₐ_evalₐ_one I x
    simp only [hx, _root_.map_zero] at h
    exact h.symm
  · intro hx
    have h := AdicCompletion.factorₐ_evalₐ_one I x
    rw [hx] at h
    have hinj : Function.Injective (Ideal.Quotient.factor (show I ^ 1 ≤ I by simp)) := by
      rw [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
      exact Ideal.map_mk_eq_bot_of_le (le_of_eq (pow_one I).symm)
    exact hinj (h.trans (_root_.map_zero _).symm)

theorem adicCompletion_ker_eval_one {E : Type*} [CommRing E] {p : ℕ}
    (hp : IsSMulRegular E (p : E)) :
    RingHom.ker (AdicCompletion.evalₐ (Ideal.span {(p : E)}) 1).toRingHom =
      Ideal.span {(p : AdicCompletion (Ideal.span {(p : E)}) E)} := by
  set I : Ideal E := Ideal.span {(p : E)} with hI
  have hFG : I.FG := ⟨{(p : E)}, by simp [I]⟩
  have hmap : Ideal.map (algebraMap E (AdicCompletion I E)) I =
      Ideal.span {(p : AdicCompletion I E)} := by
    rw [hI, Ideal.map_span]
    simp only [Set.image_singleton]
    rw [map_natCast]
  rw [ker_evalₐ_one_eq_ker_evalOneₐ I, AdicCompletion.ker_evalOneₐ_eq_map I hFG, hmap]

end Work.DSM2p
