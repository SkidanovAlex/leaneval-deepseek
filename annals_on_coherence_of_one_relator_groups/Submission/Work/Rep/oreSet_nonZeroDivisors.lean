import Mathlib
import Submission.Work.ORVonNeumann.Rep.GroupVonNeumann
import Submission.Work.Rep.Ore.injective_of_mem_nonZeroDivisors
import Submission.Work.Rep.Ore.exists_sqrt_factorization

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

set_option autoImplicit false

namespace Work.Rep

open scoped nonZeroDivisors

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- The group von Neumann algebra `N(G)`, as a type. -/
abbrev oreGvN (G : Type*) [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] : Type _ :=
  ↥(Work.ORVonNeumann.groupVonNeumann G)

/-- The bounded operators on `ℓ²(G)`. -/
abbrev oreBE (G : Type*) [MeasurableSpace G] : Type _ := Work.ORVonNeumann.boundedEnd G

/-- `ℓ²(G)`. -/
abbrev oreL2 (G : Type*) [MeasurableSpace G] : Type _ := Work.ORVonNeumann.l2 G

/-- An element of `N(G)` that is injective with dense range is a non-zero-divisor of the ring
`↥N(G)`. -/
theorem ore_mem_nonZeroDivisors_of_injective {T : oreGvN G}
    (hinj : Function.Injective (T : oreBE G)) (hdense : DenseRange (T : oreBE G)) :
    T ∈ nonZeroDivisors (oreGvN G) := by
  rw [mem_nonZeroDivisors_iff]
  constructor
  · intro b hb
    have hb0 : (((T * b : oreGvN G)) : oreBE G) = 0 := by rw [hb]; rfl
    rw [Subalgebra.coe_mul] at hb0
    have hpt : ∀ z : oreL2 G, (b : oreBE G) z = 0 := by
      intro z
      have h : (T : oreBE G) ((b : oreBE G) z) = 0 := by
        have h' := congrArg (fun f : oreBE G => f z) hb0
        simpa [mul_apply_eq_comp] using h'
      exact hinj (show (T : oreBE G) ((b : oreBE G) z) = (T : oreBE G) 0 by simpa using h)
    refine Subtype.ext ?_
    apply ContinuousLinearMap.ext
    intro z
    simpa using hpt z
  · intro b hb
    have hb0 : (((b * T : oreGvN G)) : oreBE G) = 0 := by rw [hb]; rfl
    rw [Subalgebra.coe_mul] at hb0
    have hvanish : ∀ y : oreL2 G, (b : oreBE G) ((T : oreBE G) y) = 0 := by
      intro y
      have h' := congrArg (fun f : oreBE G => f y) hb0
      simpa [mul_apply_eq_comp] using h'
    have hfun : ⇑(b : oreBE G) = ⇑(0 : oreBE G) :=
      DenseRange.equalizer hdense (b : oreBE G).continuous continuous_const
        (funext fun x => by simpa using hvanish x)
    refine Subtype.ext ?_
    exact DFunLike.coe_injective hfun

-- The Ore condition at non-zero-divisors for N(G) (Berberian, Baer *-rings; Lück, L2-Invariants
-- Thm 8.22): in a finite Baer *-ring the non-zero-divisors form an Ore set.  Together with
-- exists_rangeProjection / exists_leftAnnihilatorProjection and directly_finite this is exactly
-- the input needed to form U(G) = OreLocalization (nonZeroDivisors N(G)) N(G).
theorem oreSet_nonZeroDivisors {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] : Nonempty (OreLocalization.OreSet (nonZeroDivisors (↥(Work.ORVonNeumann.groupVonNeumann G)))) := by
  refine OreLocalization.nonempty_oreSet_iff.mpr ⟨?_, ?_⟩
  · intro r₁ r₂ s hs
    refine ⟨1, ?_⟩
    rw [Submonoid.coe_one, one_mul, one_mul]
    have h : (r₁ - r₂) * (s : oreGvN G) = 0 := by rw [sub_mul, hs, sub_self]
    exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp s.2).2 (r₁ - r₂) h)
  · intro r s
    have hs_inj : Function.Injective ((s : oreGvN G) : oreBE G) :=
      Ore.injective_of_mem_nonZeroDivisors (s : oreGvN G) s.2
    obtain ⟨h, v₁, v₂, hh_inj, hh_dense, hv₁, hv₂, hsum, hv₂_inj⟩ :=
      Ore.exists_sqrt_factorization r (s : oreGvN G) hs_inj
    have hstar : star v₁ * v₁ = 1 - star v₂ * v₂ := by rw [← hsum, add_sub_cancel_right]
    have hstar2 : star v₂ * v₂ = 1 - star v₁ * v₁ := by rw [hstar, sub_sub_cancel]
    have hstep : (1 - v₁ * star v₁) * v₁ = v₁ * star v₂ * v₂ := by
      calc (1 - v₁ * star v₁) * v₁
          = v₁ - v₁ * (star v₁ * v₁) := by rw [sub_mul, one_mul, mul_assoc]
        _ = v₁ - v₁ * (1 - star v₂ * v₂) := by rw [hstar]
        _ = v₁ * star v₂ * v₂ := by rw [mul_sub, mul_one, sub_sub_cancel, mul_assoc]
    have e1 : (1 - v₁ * star v₁) * r = ((1 - v₁ * star v₁) * v₁) * h := by
      rw [← hv₁, ← mul_assoc]
    have e2 : (v₁ * star v₂) * (s : oreGvN G) = (v₁ * star v₂ * v₂) * h := by
      rw [← hv₂, ← mul_assoc]
    have hkey : (1 - v₁ * star v₁) * r = (v₁ * star v₂) * (s : oreGvN G) := by
      rw [e1, hstep, ← e2]
    -- `x := 1 - v₁ v₁⋆` is a non-zero-divisor
    set x : oreGvN G := 1 - v₁ * star v₁ with hxdef
    set y : oreGvN G := v₁ * star v₂ with hydef
    have hxcoeeq : (x : oreBE G) = (1 : oreBE G) - (v₁ : oreBE G) * (star v₁ : oreBE G) := by
      rw [hxdef]; simp
    have hker : ∀ z : oreL2 G, (x : oreBE G) z = 0 → z = 0 := by
      intro z hz
      have hz1 : z = (v₁ : oreBE G) ((star v₁ : oreBE G) z) := by
        have h : ((1 : oreBE G) - (v₁ : oreBE G) * (star v₁ : oreBE G)) z = 0 := by
          rw [← hxcoeeq]; exact hz
        rw [sub_apply, sub_eq_zero] at h
        simpa [mul_apply_eq_comp] using h
      set w : oreL2 G := (star v₁ : oreBE G) z with hw
      have hw1 : w = ((star v₁ : oreBE G) * (v₁ : oreBE G)) w := by
        rw [mul_apply_eq_comp, ← hz1, hw]
      have hw2 : ((star v₂ * v₂ : oreGvN G) : oreBE G) w = 0 := by
        have hzero : ((1 - star v₁ * v₁ : oreGvN G) : oreBE G) w = 0 := by
          have h2 : ((1 : oreBE G) - (star v₁ : oreBE G) * (v₁ : oreBE G)) w = 0 := by
            rw [sub_apply, sub_eq_zero]
            simpa using hw1
          simpa using h2
        rw [← hstar2] at hzero
        simpa using hzero
      have hv₂w : (v₂ : oreBE G) w = 0 := by
        have h0 : inner ℂ (((star v₂ : oreBE G) * (v₂ : oreBE G)) w) w = 0 := by
          have h2' : ((star v₂ : oreBE G) * (v₂ : oreBE G)) w = 0 := by simpa using hw2
          rw [h2', inner_zero_left]
        have hab : ((star v₂ : oreBE G) * (v₂ : oreBE G)) w =
            ContinuousLinearMap.adjoint (v₂ : oreBE G) ((v₂ : oreBE G) w) := by
          rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint]
        rw [hab, ContinuousLinearMap.adjoint_inner_left] at h0
        exact inner_self_eq_zero.mp h0
      have hw0 : w = 0 :=
        hv₂_inj (show (v₂ : oreBE G) w = (v₂ : oreBE G) 0 by simpa using hv₂w)
      rw [hz1, hw0]
      simp
    have hx_inj : Function.Injective (x : oreBE G) := by
      intro z w hzw
      have hz : (x : oreBE G) (z - w) = 0 := by rw [map_sub, hzw, sub_self]
      exact sub_eq_zero.mp (hker (z - w) hz)
    have hx_dense : DenseRange (x : oreBE G) := by
      have hd : (((x : oreBE G)).range).topologicalClosure = ⊤ := by
        rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
        intro w hw
        have hw0 : ∀ u : oreL2 G, inner ℂ w ((x : oreBE G) u) = 0 := by
          intro u
          exact (Submodule.mem_orthogonal' ((x : oreBE G)).range w).mp hw ((x : oreBE G) u)
            (LinearMap.mem_range_self (x : oreBE G).toLinearMap u)
        have hxstar : star (x : oreBE G) = (x : oreBE G) := by
          rw [hxcoeeq, star_sub (1 : oreBE G) _, star_one, star_mul, star_star]
        have hxadj : ContinuousLinearMap.adjoint (x : oreBE G) = (x : oreBE G) := by
          rw [← ContinuousLinearMap.star_eq_adjoint]
          exact hxstar
        have h2 : inner ℂ ((x : oreBE G) w) ((x : oreBE G) w) = 0 := by
          calc inner ℂ ((x : oreBE G) w) ((x : oreBE G) w)
              = inner ℂ (ContinuousLinearMap.adjoint (x : oreBE G) w) ((x : oreBE G) w) := by
                  rw [hxadj]
            _ = inner ℂ w ((x : oreBE G) ((x : oreBE G) w)) :=
                  ContinuousLinearMap.adjoint_inner_left _ _ _
            _ = 0 := hw0 ((x : oreBE G) w)
        exact hker w (inner_self_eq_zero.mp h2)
      have hrange : Set.range ⇑(x : oreBE G) = (((x : oreBE G)).range : Set (oreL2 G)) := by
        ext v
        exact Iff.rfl
      rw [DenseRange, hrange, dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, hd]
      simp
    have hx_nzd : x ∈ nonZeroDivisors (oreGvN G) :=
      ore_mem_nonZeroDivisors_of_injective hx_inj hx_dense
    refine ⟨y, ⟨x, hx_nzd⟩, ?_⟩
    show x * r = y * ↑s
    exact hkey

end Work.Rep
