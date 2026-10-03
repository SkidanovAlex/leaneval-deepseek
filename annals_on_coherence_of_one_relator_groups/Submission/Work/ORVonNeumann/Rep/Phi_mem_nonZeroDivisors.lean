import Mathlib
import Submission.Work.ORVonNeumann.Rep.CosetData
import Submission.Work.ORVonNeumann.Rep.HilbertBasis
import Submission.Work.ORVonNeumann.Rep.DenseSpan
import Submission.Work.Rep.Ore.denseRange_of_injective
import Submission.Work.Rep.Ore.injective_of_mem_nonZeroDivisors
import Submission.Work.Rep.oreSet_nonZeroDivisors
import Submission.Work.ORVonNeumann.Ore.star_mem_nonZeroDivisors

namespace Work.ORVonNeumann.Rep

/-- **The coset diagonal embedding `N(H) → N(G)` sends non-zero-divisors to non-zero-divisors.**

Let `C` be a right-coset decomposition of `G` over `H` and `Φ : N(H) →ₐ[ℂ] N(G)` a `*`-algebra
map which acts on `ℓ²(G)` "cosetwise": `(Φ b) (C.e q y) = C.e q (b y)` for every coset
representative `q` and every `y ∈ ℓ²(H)` (`hΦform`), and is `*`-preserving (`hΦstar`).

If `s ∈ N(H)` is a non-zero-divisor then `s` acts injectively on `ℓ²(H)`
(`Work.Rep.Ore.injective_of_mem_nonZeroDivisors`).  We show that `Φ s` acts injectively on
`ℓ²(G)`: if `(Φ s) x = 0` then for each coset `q`, pairing the adjoint `(C.e q)† x` against
`ran(s†)` via
`⟪s ((C.e q)† x), y⟫ = ⟪(C.e q)† x, s† y⟫ = ⟪x, C.e q (s† y)⟫ = ⟪x, (Φ s†)(C.e q y)⟫
= ⟪(Φ s) x, C.e q y⟫ = 0`
shows `s ((C.e q)† x) = 0`, whence `(C.e q)† x = 0` by injectivity of `s`.  Hence `x` is
orthogonal to every `C.e q (ℓ²(H))`, in particular to every `δ_g = C.e (qpart g) (δ_{hpart g})`;
as `{δ_g}` has dense closed span (`Work.ORVonNeumann.Rep.tsum_expansion`), `x = 0`.  So `Φ s` is
injective, and therefore has dense range in the finite von Neumann algebra `N(G)`
(`Work.Rep.Ore.denseRange_of_injective`), which makes it a non-zero-divisor
(`Work.Rep.ore_mem_nonZeroDivisors_of_injective`). -/
theorem Phi_mem_nonZeroDivisors {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {H : Subgroup G} (C : Work.ORVonNeumann.Rep.CosetData G H) (Φ : ↥(Work.ORVonNeumann.groupVonNeumann ↥H) →ₐ[ℂ] ↥(Work.ORVonNeumann.groupVonNeumann G)) (hΦstar : ∀ b : ↥(Work.ORVonNeumann.groupVonNeumann ↥H), Φ (star b) = star (Φ b)) (hΦform : ∀ (b : ↥(Work.ORVonNeumann.groupVonNeumann ↥H)) (q : C.Q), ∀ y : Work.ORVonNeumann.l2 ↥H, (Φ b : Work.ORVonNeumann.boundedEnd G) (C.e q y) = C.e q ((b : Work.ORVonNeumann.boundedEnd ↥H) y)) {s : ↥(Work.ORVonNeumann.groupVonNeumann ↥H)} (hs : s ∈ nonZeroDivisors ↥(Work.ORVonNeumann.groupVonNeumann ↥H)) : Φ s ∈ nonZeroDivisors ↥(Work.ORVonNeumann.groupVonNeumann G) := by
  have hs_inj : Function.Injective (s : Work.ORVonNeumann.boundedEnd ↥H) :=
    Work.Rep.Ore.injective_of_mem_nonZeroDivisors s hs
  have hΦin : Function.Injective (Φ s : Work.ORVonNeumann.boundedEnd G) := by
    have hker : ∀ z : Work.ORVonNeumann.l2 G,
        (Φ s : Work.ORVonNeumann.boundedEnd G) z = 0 → z = 0 := by
      intro z hz
      have hw : ∀ q : C.Q,
          ContinuousLinearMap.adjoint (C.e q).toContinuousLinearMap z = 0 := by
        intro q
        have hsb : ((star s : ↥(Work.ORVonNeumann.groupVonNeumann ↥H)) :
            Work.ORVonNeumann.boundedEnd ↥H) = ContinuousLinearMap.adjoint
              (s : Work.ORVonNeumann.boundedEnd ↥H) := by
          rw [StarMemClass.coe_star, ContinuousLinearMap.star_eq_adjoint]
        have key : ∀ y : Work.ORVonNeumann.l2 ↥H,
            inner ℂ ((s : Work.ORVonNeumann.boundedEnd ↥H)
              (ContinuousLinearMap.adjoint (C.e q).toContinuousLinearMap z)) y = 0 := by
          intro y
          calc inner ℂ ((s : Work.ORVonNeumann.boundedEnd ↥H)
                (ContinuousLinearMap.adjoint (C.e q).toContinuousLinearMap z)) y
              = inner ℂ (ContinuousLinearMap.adjoint (C.e q).toContinuousLinearMap z)
                  (ContinuousLinearMap.adjoint (s : Work.ORVonNeumann.boundedEnd ↥H) y) :=
                (ContinuousLinearMap.adjoint_inner_right (s : Work.ORVonNeumann.boundedEnd ↥H) _ y).symm
            _ = inner ℂ (ContinuousLinearMap.adjoint (C.e q).toContinuousLinearMap z)
                  (((star s : ↥(Work.ORVonNeumann.groupVonNeumann ↥H)) :
                    Work.ORVonNeumann.boundedEnd ↥H) y) := by rw [hsb]
            _ = inner ℂ z ((C.e q).toContinuousLinearMap
                  (((star s : ↥(Work.ORVonNeumann.groupVonNeumann ↥H)) :
                    Work.ORVonNeumann.boundedEnd ↥H) y)) :=
                ContinuousLinearMap.adjoint_inner_left (C.e q).toContinuousLinearMap _ z
            _ = inner ℂ z (C.e q (((star s : ↥(Work.ORVonNeumann.groupVonNeumann ↥H)) :
                    Work.ORVonNeumann.boundedEnd ↥H) y)) := rfl
            _ = inner ℂ z ((Φ (star s) : Work.ORVonNeumann.boundedEnd G) (C.e q y)) := by
                rw [hΦform (star s) q y]
            _ = inner ℂ z (star ((Φ s) : Work.ORVonNeumann.boundedEnd G) (C.e q y)) := by
                rw [hΦstar s, StarMemClass.coe_star]
            _ = inner ℂ ((Φ s : Work.ORVonNeumann.boundedEnd G) z) (C.e q y) := by
                rw [ContinuousLinearMap.star_eq_adjoint]
                exact ContinuousLinearMap.adjoint_inner_right (Φ s : Work.ORVonNeumann.boundedEnd G) z (C.e q y)
            _ = 0 := by rw [hz, inner_zero_left]
        have hsz : (s : Work.ORVonNeumann.boundedEnd ↥H)
            (ContinuousLinearMap.adjoint (C.e q).toContinuousLinearMap z) = 0 := by
          have h1 := key ((s : Work.ORVonNeumann.boundedEnd ↥H)
            (ContinuousLinearMap.adjoint (C.e q).toContinuousLinearMap z))
          rwa [inner_self_eq_zero] at h1
        exact hs_inj (by rw [hsz, map_zero])
      have hz0 : ∀ g : G, inner ℂ z (Work.ORVonNeumann.Rep.deltaG g) = 0 := by
        intro g
        have h1 : Work.ORVonNeumann.Rep.deltaG g
            = C.e (C.qpart g) (Work.ORVonNeumann.Rep.deltaG (C.hpart g)) := by
          rw [C.e_delta, C.hpart_mul_qpart]
        calc inner ℂ z (Work.ORVonNeumann.Rep.deltaG g)
            = inner ℂ z (C.e (C.qpart g) (Work.ORVonNeumann.Rep.deltaG (C.hpart g))) := by rw [h1]
          _ = inner ℂ (ContinuousLinearMap.adjoint (C.e (C.qpart g)).toContinuousLinearMap z)
                (Work.ORVonNeumann.Rep.deltaG (C.hpart g)) :=
              (ContinuousLinearMap.adjoint_inner_left (C.e (C.qpart g)).toContinuousLinearMap _ z).symm
          _ = 0 := by rw [hw (C.qpart g), inner_zero_left]
      have hsum0 : (∑' g : G, inner ℂ (Work.ORVonNeumann.Rep.deltaG g) z •
          Work.ORVonNeumann.Rep.deltaG g) = 0 := by
        rw [tsum_congr (fun g => by
              rw [show inner ℂ (Work.ORVonNeumann.Rep.deltaG g) z = 0 by
                rw [← inner_conj_symm, hz0 g]; simp, zero_smul]), tsum_zero]
      rw [← Work.ORVonNeumann.Rep.tsum_expansion z, hsum0]
    intro x y hxy
    have h : (Φ s : Work.ORVonNeumann.boundedEnd G) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hker (x - y) h)
  have hdense : DenseRange (Φ s : Work.ORVonNeumann.boundedEnd G) :=
    Work.Rep.Ore.denseRange_of_injective (Φ s) hΦin
  exact Work.Rep.ore_mem_nonZeroDivisors_of_injective hΦin hdense

end Work.ORVonNeumann.Rep
