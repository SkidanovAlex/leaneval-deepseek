import Submission.Work.Lattice.poissonDefs

/-!
# Basic properties of the periodization over `ℤⁿ`

Elementary facts about the unit cube, the lattice `ℤⁿ`, the section `(0,1] → ℝ/ℤ`
and the periodization: the cube is a fundamental domain, the periodization is invariant
under integer translations, and it descends to the torus.
-/

namespace Work.Lattice

open MeasureTheory Set
open scoped FourierTransform SchwartzMap

theorem circleSec_coe (t : UnitAddCircle) : ((circleSec t : ℝ) : UnitAddCircle) = t := by
  rw [circleSec]; exact AddCircle.coe_equivIoc

theorem circleSec_mem (t : UnitAddCircle) : circleSec t ∈ Ioc (0:ℝ) 1 := by
  rw [circleSec]; simpa using (AddCircle.equivIoc (1:ℝ) 0 t).2

theorem circleSec_eq_of_mem {x : ℝ} (hx : x ∈ Ioc (0:ℝ) 1) :
    circleSec ((x : ℝ) : UnitAddCircle) = x := by
  rw [circleSec, AddCircle.equivIoc_coe_eq (by simpa using hx)]

theorem sub_circleSec_mem (x : ℝ) :
    x - circleSec ((x : ℝ) : UnitAddCircle) ∈ AddSubgroup.zmultiples (1:ℝ) := by
  rw [AddSubgroup.mem_zmultiples_iff]
  have h : ((x - circleSec ((x:ℝ) : UnitAddCircle) : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, circleSec_coe, sub_self]
  rw [AddCircle.coe_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn⟩

/-- The unit cube is a fundamental domain for the lattice `ℤⁿ ⊆ ℝⁿ`. -/
theorem isAddFundamentalDomain_unitCube (n : ℕ) : IsAddFundamentalDomain (intVec n) (unitCube n)
    (volume : Measure (Fin n → ℝ)) := by
  classical
  refine IsAddFundamentalDomain.mk' ?_ ?_
  · exact (MeasurableSet.pi Set.countable_univ fun i _ => measurableSet_Ioc).nullMeasurableSet
  · intro x
    have hgmem : (fun i => (1:ℝ) - ⌈x i⌉) ∈ intVec n := by
      rw [mem_intVec]
      intro i
      exact ⟨1 - ⌈x i⌉, by norm_num⟩
    have hgIoc : ∀ i, ((1:ℝ) - ⌈x i⌉) + x i ∈ Ioc (0:ℝ) 1 := by
      intro i
      rw [Set.mem_Ioc]
      constructor
      · have := Int.ceil_lt_add_one (x i); linarith
      · have := Int.le_ceil (x i); linarith
    have hgx : (⟨fun i => (1:ℝ) - ⌈x i⌉, hgmem⟩ : intVec n) +ᵥ x ∈ unitCube n := by
      rw [mem_unitCube]
      intro i
      exact hgIoc i
    refine ⟨⟨fun i => (1:ℝ) - ⌈x i⌉, hgmem⟩, hgx, ?_⟩
    intro y hy
    have hyIoc : ∀ i, (y : Fin n → ℝ) i + x i ∈ Ioc (0:ℝ) 1 := by
      intro i
      have hmem := Set.mem_pi.mp hy i (Set.mem_univ i)
      exact hmem
    refine Subtype.ext (funext fun i => ?_)
    have hsub : (y : Fin n → ℝ) - (fun i => (1:ℝ) - ⌈x i⌉) ∈ intVec n :=
      AddSubgroup.sub_mem _ y.2 hgmem
    rw [mem_intVec] at hsub
    obtain ⟨m, hm⟩ := hsub i
    have h1 := hyIoc i
    have h2 := hgIoc i
    simp only [Set.mem_Ioc] at h1 h2
    have hmval : (m : ℝ) = (y : Fin n → ℝ) i - ((1:ℝ) - ⌈x i⌉) := hm.symm
    have hmrange : (m : ℝ) ∈ Set.Ioo (-1:ℝ) 1 := by
      rw [hmval]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hm0 : m = 0 := by
      have habs : |(m:ℝ)| < 1 := by rw [abs_lt]; exact ⟨hmrange.1, hmrange.2⟩
      have := Int.abs_lt_one_iff.mp (by exact_mod_cast habs)
      simpa using this
    have hygeq : (y : Fin n → ℝ) i - ((1:ℝ) - ⌈x i⌉) = 0 := by
      rw [← hmval, hm0]; simp
    linarith [hygeq]

/-- The periodization is invariant under translations by integer vectors. -/
theorem periodization_add {n : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (x : Fin n → ℝ) (v : Fin n → ℤ) :
    periodization f (x + intVecToReal v) = periodization f x := by
  have harg : ∀ v' : Fin n → ℤ,
      (x + intVecToReal v) + intVecToReal v' = x + intVecToReal (v + v') := by
    intro v'; ext i; simp only [Pi.add_apply, intVecToReal_apply]; push_cast; ring
  have step : periodization f (x + intVecToReal v)
      = ∑' v' : Fin n → ℤ, f (WithLp.toLp 2 (x + intVecToReal (v + v'))) := by
    rw [periodization]; simp_rw [harg]
  have step2 : (∑' v' : Fin n → ℤ, f (WithLp.toLp 2 (x + intVecToReal (v + v'))))
      = ∑' v' : Fin n → ℤ, f (WithLp.toLp 2 (x + intVecToReal v')) := by
    rw [show (fun v' : Fin n → ℤ => f (WithLp.toLp 2 (x + intVecToReal (v + v'))))
        = (fun v' => f (WithLp.toLp 2 (x + intVecToReal (v' + v)))) from by
          ext v'; rw [add_comm v v']]
    exact Equiv.tsum_eq (Equiv.addRight v) (fun c => f (WithLp.toLp 2 (x + intVecToReal c)))
  rw [step, step2, periodization]

/-- The periodization only depends on the class of `x` modulo `ℤⁿ`. -/
theorem periodization_eq_of_sub_mem {n : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    {x y : Fin n → ℝ} (h : y - x ∈ intVec n) : periodization f y = periodization f x := by
  have h' : ∀ i, ∃ m : ℤ, (y - x) i = (m : ℝ) := by
    rwa [mem_intVec] at h
  choose v hv using h'
  have hy : y = x + intVecToReal v := by
    ext i; have := hv i
    simp only [Pi.sub_apply, Pi.add_apply, intVecToReal_apply] at this ⊢; linarith
  rw [hy, periodization_add]

/-- The lift of the periodization to the torus agrees with the periodization on `ℝⁿ`. -/
theorem torusLift_apply {n : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (x : Fin n → ℝ) :
    torusLift f (fun i => (x i : UnitAddCircle)) = periodization f x := by
  rw [torusLift]
  apply periodization_eq_of_sub_mem
  rw [mem_intVec]
  intro i
  have h := sub_circleSec_mem (x i)
  rw [AddSubgroup.mem_zmultiples_iff] at h
  obtain ⟨m, hm⟩ := h
  have hm' : (m:ℝ) = x i - circleSec (x i : UnitAddCircle) := by simpa [zsmul_eq_mul] using hm
  refine ⟨-m, ?_⟩
  simp only [Pi.sub_apply]
  push_cast
  linarith

end Work.Lattice
