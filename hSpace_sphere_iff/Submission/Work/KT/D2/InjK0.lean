import Mathlib
import Submission.Work.KT.Basic
import Submission.Work.KT.D2.Basic
import Submission.Work.KT.D2.mZero
import Submission.Work.KT.D2.Inject
import Submission.Work.KT.D2.rankK0
import Submission.Work.KT.hk_k0_eq_diff

/-!
# `Work.KT.D2.InjK0` — the pair (rank, winding) is injective on `K₀(Kpair ℝ²)`

The rank at the boundary point and the winding invariant together separate classes: an element of
`K₀(Kpair ℝ²)` with vanishing augmented rank and vanishing winding invariant is zero.

Any element of `K₀` is a difference of the classes of two idempotent matrices of the same size
(`Work.KT.hk_k0_eq_diff`), so it suffices to compare two such idempotents: equal augmented rank
means equal rank of the boundary values, and equal winding invariant then gives equal classes by
`Work.KT.D2.cls_eq_of_rank_eq`.
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Work.KT.D2

open Matrix
open Classical

noncomputable section

/-- The rank homomorphism `K₀(ℂ) → ℤ`. -/
noncomputable def rankHom : K0 ℂ →+ ℤ := Classical.choose rankK0

theorem rankHom_cls (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (hM : M * M = M) :
    rankHom (cls (⟨n, M⟩ : Mat ℂ)) = (M.rank : ℤ) :=
  (Classical.choose_spec rankK0).1 n M hM

/-- **Injectivity.** An element of `K₀(Kpair ℝ²)` whose augmented rank and whose winding invariant
both vanish is zero. -/
theorem eq_zero_of_rank_mZero (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2))
    (m : K0 (Kpair (Euc 2)) →+ ℤ)
    (hm : ∀ P : Mat (Kpair (Euc 2)), m (cls P) = mZero y0 hy0 P) :
    ∀ z : K0 (Kpair (Euc 2)),
      rankHom (K0.mapA (augPair (Euc 2) y0) z) = 0 → m z = 0 → z = 0 := by
  intro z hrank hmz
  obtain ⟨n, P, Q, hP, hQ, hz⟩ := hk_k0_eq_diff (Kpair (Euc 2)) z
  have hmapP : K0.mapA (augPair (Euc 2) y0) (cls (⟨n, P⟩ : Mat (Kpair (Euc 2))))
      = cls (⟨n, bval n y0 P⟩ : Mat ℂ) := by
    rw [show K0.mapA (augPair (Euc 2) y0) (cls (⟨n, P⟩ : Mat (Kpair (Euc 2))))
        = K0.map (augPair (Euc 2) y0).toRingHom (cls (⟨n, P⟩ : Mat (Kpair (Euc 2))))
        from rfl]
    rw [mapCls_idem (augPair (Euc 2) y0).toRingHom (p := (⟨n, P⟩ : Mat (Kpair (Euc 2)))) hP]
    rfl
  have hmapQ : K0.mapA (augPair (Euc 2) y0) (cls (⟨n, Q⟩ : Mat (Kpair (Euc 2))))
      = cls (⟨n, bval n y0 Q⟩ : Mat ℂ) := by
    rw [show K0.mapA (augPair (Euc 2) y0) (cls (⟨n, Q⟩ : Mat (Kpair (Euc 2))))
        = K0.map (augPair (Euc 2) y0).toRingHom (cls (⟨n, Q⟩ : Mat (Kpair (Euc 2))))
        from rfl]
    rw [mapCls_idem (augPair (Euc 2) y0).toRingHom (p := (⟨n, Q⟩ : Mat (Kpair (Euc 2)))) hQ]
    rfl
  have hrank' : (bval n y0 P).rank = (bval n y0 Q).rank := by
    have h1 : rankHom (K0.mapA (augPair (Euc 2) y0) z)
        = (bval n y0 P).rank - (bval n y0 Q).rank := by
      rw [hz, map_sub, hmapP, hmapQ, map_sub,
        rankHom_cls n (bval n y0 P) (bval_idem n y0 P hP),
        rankHom_cls n (bval n y0 Q) (bval_idem n y0 Q hQ)]
    rw [h1] at hrank
    linarith
  have hmz' : mZero y0 hy0 (⟨n, P⟩ : Mat (Kpair (Euc 2)))
      = mZero y0 hy0 (⟨n, Q⟩ : Mat (Kpair (Euc 2))) := by
    have h1 : m z = mZero y0 hy0 (⟨n, P⟩ : Mat (Kpair (Euc 2)))
        - mZero y0 hy0 (⟨n, Q⟩ : Mat (Kpair (Euc 2))) := by
      rw [hz, map_sub, hm, hm]
    rw [h1] at hmz
    exact sub_eq_zero.mp hmz
  rw [hz, cls_eq_of_rank_eq hy0 P Q hP hQ hrank' hmz', sub_self]

end

end Work.KT.D2
