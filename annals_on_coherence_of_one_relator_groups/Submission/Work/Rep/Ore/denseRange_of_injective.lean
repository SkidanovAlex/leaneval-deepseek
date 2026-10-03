import Mathlib
import Submission.Work.ORVonNeumann.Rep.CountableVonNeumann
import Submission.Work.Rep.starProjection_ker_orthogonal_mem_groupVonNeumann
import Submission.Work.Rep.Ore.exists_continuousLinearMap_of_denseRange
import Submission.Work.Rep.Ore.mem_groupVonNeumann_of_mul_eq
import Submission.Work.Rep.Ore.star_mul_self_add_eq_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped InnerProductSpace

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.Rep.Ore

open Work.ORVonNeumann

set_option maxHeartbeats 1000000 in
/-- If an element `T` of the group von Neumann algebra `N(G) ⊆ B(ℓ²(G))` is injective, then it
has dense range.  (This is special to the finite von Neumann algebra setting: in `B(ℓ²)` there are
injective operators with non-dense range.)

Suggested route: put `A = star T * T`, `P = CFC.sqrt A`.  `P ∈ N(G)` because `N(G)` is a closed
`*`-subalgebra: get the real CFC via
`IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus (A := boundedEnd G)` (instance search
does not find it on its own, so introduce it with `haveI`/`letI`; note that a *statement* mentioning
`CFC.sqrt` also needs it, so declare it as a `noncomputable instance` in the file if you want to
state helper lemmas about `CFC.sqrt`), `StarModule ℝ (boundedEnd G)` via
`StarModule.complexToReal`, the closedness of the centralizer via `Set.isClosed_centralizer`
(recall `commutant S = StarSubalgebra.centralizer ℂ S`), and then use `cfcₙ_mem`
(`CFC.sqrt a = cfcₙ NNReal.sqrt a`, and `cfcₙ_nnreal_eq_real` converts to the real-valued form
which is the one `cfcₙ_mem` applies to).  Then `P*P = A` (`CFC.sqrt_mul_sqrt_self`), `star P = P`
(`CFC.sqrt_nonneg` together with `IsSelfAdjoint.of_nonneg`/`star_eq`), `P` is injective (since
`⟪A x, x⟫ = ‖T x‖²`) and hence has dense range (self-adjoint + injective: if `y ⊥ ran P` then
`⟪P y, P y⟫ = ⟪y, P (P y)⟫ = 0`).  Define `V (P x) = T x`, well defined and isometric because
`‖T x‖² = ⟪A x, x⟫ = ‖P x‖²`, and extend it with `LinearMap.extendOfNorm`; get `V * P = T`.
`V ∈ N(G)` (commuting with `ρ g` on the dense range of `P`).  Then `star V * V = 1` and
`Work.ORVonNeumann.Rep.directly_finite` gives `V * star V = 1`, so `V` is surjective and
`ran T = V '' ran P` is dense (`V` sends the dense set `ran P` onto a dense set).-/
theorem denseRange_of_injective {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (T : ↥(Work.ORVonNeumann.groupVonNeumann G)) (hT : Function.Injective (T : Work.ORVonNeumann.boundedEnd G)) : DenseRange (T : Work.ORVonNeumann.boundedEnd G) := by
  -- The real continuous functional calculus on `B(ℓ²(G))`; instance search does not find it.
  letI : NonUnitalContinuousFunctionalCalculus ℝ (boundedEnd G) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus (A := boundedEnd G)
  -- `N(G)` is closed in `B(ℓ²(G))`, being the centralizer of the range of `ρ`.
  have hNclosed : IsClosed ((groupVonNeumann G : StarSubalgebra ℂ (boundedEnd G)) :
      Set (boundedEnd G)) := by
    rw [groupVonNeumann, commutant, StarSubalgebra.coe_centralizer]
    exact Set.isClosed_centralizer _
  haveI := hNclosed
  let T' : boundedEnd G := (T : boundedEnd G)
  have hT'inj : Function.Injective T' := hT
  have hT'mem : T' ∈ groupVonNeumann G := T.2
  -- `A = T⋆T` and `P = √A`.
  set A : boundedEnd G := star T' * T' with hA_def
  have hA0 : 0 ≤ A := by rw [hA_def]; exact star_mul_self_nonneg T'
  have hAmem : A ∈ groupVonNeumann G := by
    rw [hA_def]; exact mul_mem (star_mem hT'mem) hT'mem
  set P : boundedEnd G := CFC.sqrt A with hP_def
  have hPmem : P ∈ groupVonNeumann G := by
    haveI : StarModule ℝ (boundedEnd G) := StarModule.complexToReal (E := boundedEnd G)
    rw [hP_def]
    unfold CFC.sqrt
    rw [cfcₙ_nnreal_eq_real NNReal.sqrt A hA0]
    exact cfcₙ_mem (𝕜' := ℂ) (S := StarSubalgebra ℂ (boundedEnd G)) (s := groupVonNeumann G)
      (fun x : ℝ => ↑(NNReal.sqrt x.toNNReal)) hAmem
  have hPP : P * P = A := by rw [hP_def]; exact CFC.sqrt_mul_sqrt_self A hA0
  have hPsa : star P = P := by
    rw [hP_def]; exact (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
  -- The pairings of `A` against `x` compute the norms of `P x` and `T' x`.
  have hpairP : ∀ z : l2 G, inner ℂ (A z) z = inner ℂ (P z) (P z) := by
    intro z
    have hAz : A z = (ContinuousLinearMap.adjoint P) (P z) := by
      rw [← hPP, mul_apply_eq_comp, ← ContinuousLinearMap.star_eq_adjoint, hPsa]
    rw [hAz]
    exact ContinuousLinearMap.adjoint_inner_left P z (P z)
  have hpairT : ∀ z : l2 G, inner ℂ (A z) z = inner ℂ (T' z) (T' z) := by
    intro z
    have hAz : A z = (ContinuousLinearMap.adjoint T') (T' z) := by
      rw [hA_def, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint]
    rw [hAz]
    exact ContinuousLinearMap.adjoint_inner_left T' z (T' z)
  have hPT_norm : ∀ z : l2 G, ‖P z‖ = ‖T' z‖ := by
    intro z
    have h : ‖P z‖ ^ 2 = ‖T' z‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (P z), ← hpairP z, hpairT z,
        inner_self_eq_norm_sq (𝕜 := ℂ) (T' z)]
    nlinarith [norm_nonneg (P z), norm_nonneg (T' z)]
  -- `P` is injective, since `⟪A x, x⟫ = ‖T x‖²`.
  have hPinj : Function.Injective P := by
    intro x y hxy
    have h0 : P (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h1 : ‖T' (x - y)‖ = 0 := by rw [← hPT_norm (x - y), h0, norm_zero]
    have h2 : T' (x - y) = 0 := norm_eq_zero.mp h1
    have h3 : T' (x - y) = T' 0 := by rw [h2, map_zero]
    exact sub_eq_zero.mp (hT'inj h3)
  -- A self-adjoint injective operator has dense range.
  have hP_orth : Submodule.orthogonal (LinearMap.range P.toLinearMap) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    rw [Submodule.mem_orthogonal] at hy
    have hkey : inner ℂ (P y) (P y) = 0 := by
      have h1 : inner ℂ (P (P y)) y = 0 :=
        hy (P (P y)) (LinearMap.mem_range.mpr ⟨P y, rfl⟩)
      have h2 : inner ℂ ((ContinuousLinearMap.adjoint P) (P y)) y = inner ℂ (P y) (P y) :=
        ContinuousLinearMap.adjoint_inner_left P y (P y)
      have h3 : (ContinuousLinearMap.adjoint P) (P y) = P (P y) := by
        rw [← ContinuousLinearMap.star_eq_adjoint, hPsa]
      rw [← h2, h3, h1]
    have hPy : P y = 0 := inner_self_eq_zero.mp hkey
    have h2 : P y = P 0 := by rw [hPy, map_zero]
    exact hPinj h2
  have hP_closure : (LinearMap.range P.toLinearMap).topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.mpr hP_orth
  have hP_dense : DenseRange P := by
    have h' : Dense (↑(LinearMap.range P.toLinearMap) : Set (l2 G)) :=
      Submodule.dense_iff_topologicalClosure_eq_top.mpr hP_closure
    rw [LinearMap.coe_range P.toLinearMap] at h'
    exact h'
  -- `V := T ∘ P⁻¹` on `ran P`, extended by continuity.
  obtain ⟨V, hVP⟩ := exists_continuousLinearMap_of_denseRange P T' hP_dense
    (fun x => (hPT_norm x).ge)
  have hVmem : V ∈ groupVonNeumann G :=
    mem_groupVonNeumann_of_mul_eq V P T' hPmem hT'mem hP_dense hVP
  -- `V` is an isometry, so `star V * V = 1`.
  have hVV : star V * V = 1 := by
    have h := star_mul_self_add_eq_one_aux P V 0 T' 0 hPsa hP_dense
      (by rw [star_zero, zero_mul, add_zero]; exact hPP) hVP (by rw [zero_mul])
    simpa using h
  have hX : (star (⟨V, hVmem⟩ : ↥(groupVonNeumann G))) *
      (⟨V, hVmem⟩ : ↥(groupVonNeumann G)) = 1 := by
    refine Subtype.ext ?_
    change star V * V = (1 : boundedEnd G)
    exact hVV
  -- Direct finiteness of `N(G)` upgrades this to `V * star V = 1`.
  have hX' : (⟨V, hVmem⟩ : ↥(groupVonNeumann G)) *
      star (⟨V, hVmem⟩ : ↥(groupVonNeumann G)) = 1 :=
    Work.ORVonNeumann.Rep.directly_finite _ _ hX
  have hVV' : V * star V = 1 := by
    have h := congrArg (fun x : ↥(groupVonNeumann G) => (x : boundedEnd G)) hX'
    change V * star V = (1 : boundedEnd G) at h
    exact h
  -- Hence `ran T` is dense: anything orthogonal to it is orthogonal to the dense `ran P`.
  have hrange : (LinearMap.range T'.toLinearMap).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff]
    rw [Submodule.eq_bot_iff]
    intro y hy
    rw [Submodule.mem_orthogonal] at hy
    have hk : star V y = 0 := by
      have hmem : star V y ∈ Submodule.orthogonal (LinearMap.range P.toLinearMap) := by
        rw [Submodule.mem_orthogonal]
        intro u hu
        obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hu
        calc inner ℂ (P z) (star V y)
            = inner ℂ (P z) ((ContinuousLinearMap.adjoint V) y) := by
              rw [ContinuousLinearMap.star_eq_adjoint V]
          _ = inner ℂ (V (P z)) y := ContinuousLinearMap.adjoint_inner_right V (P z) y
          _ = inner ℂ (T' z) y := by
              have h := congrArg (fun f : boundedEnd G => f z) hVP
              rw [mul_apply_eq_comp] at h
              rw [h]
          _ = 0 := hy (T' z) (LinearMap.mem_range.mpr ⟨z, rfl⟩)
      simpa only [hP_orth, Submodule.mem_bot] using hmem
    have h2 : V (star V y) = y := by
      have h := congrArg (fun f : boundedEnd G => f y) hVV'
      rw [mul_apply_eq_comp] at h
      simpa using h
    rw [hk, map_zero] at h2
    exact h2.symm
  have hgoal : DenseRange T' := by
    have h' : Dense (↑(LinearMap.range T'.toLinearMap) : Set (l2 G)) :=
      Submodule.dense_iff_topologicalClosure_eq_top.mpr hrange
    rw [LinearMap.coe_range T'.toLinearMap] at h'
    exact h'
  exact hgoal

end Work.Rep.Ore
