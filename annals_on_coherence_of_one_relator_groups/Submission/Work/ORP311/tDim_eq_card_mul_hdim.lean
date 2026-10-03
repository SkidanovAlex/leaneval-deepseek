import Mathlib
import Submission.Work.ORP311.LuckDim
import Submission.Work.ORP311.hdim_translate

namespace Work.ORP311

theorem tDim_eq_card_mul_hdim {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n : ℕ} (K : Submodule ℂ (Work.ORVonNeumann.Rep.HSum (G := G) n)) [K.HasOrthogonalProjection] (hK : Work.ORVonNeumann.Rep.Equivariant (G := G) K.starProjection) (s : Finset G) : Work.ORP311.tDim (G := G) n s K = (s.card : ℝ) * Work.ORVonNeumann.Rep.hdim (G := G) K := by
  rw [tDim_apply]
  -- Each summand is the von Neumann dimension, by translation invariance (`hdim_translate`).
  have h : (∑ g ∈ s, ∑ i : Fin n, ‖K.starProjection
      (Work.ORVonNeumann.Rep.hinclude (G := G) n i
        (Work.ORVonNeumann.Rep.deltaG g))‖ ^ 2)
      = ∑ g ∈ s, Work.ORVonNeumann.Rep.hdim (G := G) K :=
    Finset.sum_congr rfl (fun g _ => hdim_translate (G := G) K hK g)
  rw [h, Finset.sum_const, nsmul_eq_mul]

end Work.ORP311
