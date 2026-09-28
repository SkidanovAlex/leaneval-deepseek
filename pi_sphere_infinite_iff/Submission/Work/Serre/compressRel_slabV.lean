import Mathlib
import Submission.Work.Serre.E2dEngine
import Submission.Work.Serre.compressRel_slabU

/-!
# The compression property of the slab pair `(↥(slabV n), ↥(slabV n) ∩ ∂I^{n+1})`

`Work.Serre.compressRel_slabV` is the second half of the geometric input of the Mayer–Vietoris
step of the `E2(d)` computation of `Submission/Work/Serre/E2dEngine.lean`: the pair

  `(↥(slabV n), {x : ↥(slabV n) | (x : I^{n+1}) ∈ slabV n ∩ ∂I^{n+1}})`

has the compression property in every dimension.

Instead of repeating the radial deformation retraction of
`Submission/Work/Serre/compressRel_slabU.lean` for the reflected slab
`slabV n = {x ∈ I^{n+1} | 1/4 < x_last}`, we transport the result for `slabU` along the reflection
of the last coordinate of the cube,

  `ρ(u₀, …, u_{n}) = (u₀, …, u_{n-1}, 1 - u_n)`,

which is a homeomorphism of `I^{n+1}` carrying `slabV n` onto
`slabU n = {x | x_last < 3/4}` and preserving the boundary `∂I^{n+1}`.  The compression property is
invariant under a homeomorphism of the pair (`compressRel_of_homeo`), so
`Work.Serre.compressRel_slabU` yields `Work.Serre.compressRel_slabV`.
-/

open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-! ## The reflection of the unit interval -/

/-- The reflection `t ↦ 1 - t` of the unit interval. -/
def reflUnitInterval : unitInterval ≃ₜ unitInterval where
  toFun t := ⟨1 - (t : ℝ), by exact ⟨by linarith [t.2.2], by linarith [t.2.1]⟩⟩
  invFun t := ⟨1 - (t : ℝ), by exact ⟨by linarith [t.2.2], by linarith [t.2.1]⟩⟩
  left_inv t := Subtype.ext (by simp)
  right_inv t := Subtype.ext (by simp)
  continuous_toFun := (continuous_const.sub continuous_subtype_val).subtype_mk (fun t => by
    simp only [Pi.sub_apply, Set.mem_Icc]
    exact ⟨by linarith [t.2.2], by linarith [t.2.1]⟩)
  continuous_invFun := (continuous_const.sub continuous_subtype_val).subtype_mk (fun t => by
    simp only [Pi.sub_apply, Set.mem_Icc]
    exact ⟨by linarith [t.2.2], by linarith [t.2.1]⟩)

@[simp] theorem reflUnitInterval_coe (t : unitInterval) :
    ((reflUnitInterval t : unitInterval) : ℝ) = 1 - (t : ℝ) := rfl

@[simp] theorem reflUnitInterval_zero : reflUnitInterval 0 = 1 := by
  refine Subtype.ext ?_
  rw [reflUnitInterval_coe]
  norm_num

@[simp] theorem reflUnitInterval_one : reflUnitInterval 1 = 0 := by
  refine Subtype.ext ?_
  rw [reflUnitInterval_coe]
  norm_num

@[simp] theorem reflUnitInterval_involutive (t : unitInterval) :
    reflUnitInterval (reflUnitInterval t) = t :=
  reflUnitInterval.left_inv t

/-! ## The reflection of the last coordinate of the cube -/

/-- The reflection of the last coordinate of the cube `I^{n+1}`,
`(u₀, …, u_{n-1}, u_n) ↦ (u₀, …, u_{n-1}, 1 - u_n)`. -/
def reflLastFun (n : ℕ) (u : Work.Stems.Cubical.IC (n+1)) :
    Work.Stems.Cubical.IC (n+1) :=
  Fin.snoc (Fin.init u) (reflUnitInterval (u (Fin.last n)))

@[simp] theorem reflLastFun_castSucc (n : ℕ) (u : Work.Stems.Cubical.IC (n+1)) (j : Fin n) :
    reflLastFun n u (Fin.castSucc j) = u (Fin.castSucc j) := by
  rw [reflLastFun, Fin.snoc_castSucc]
  rfl

@[simp] theorem reflLastFun_last (n : ℕ) (u : Work.Stems.Cubical.IC (n+1)) :
    reflLastFun n u (Fin.last n) = reflUnitInterval (u (Fin.last n)) := by
  rw [reflLastFun, Fin.snoc_last]

theorem reflLastFun_involutive (n : ℕ) (u : Work.Stems.Cubical.IC (n+1)) :
    reflLastFun n (reflLastFun n u) = u := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [reflLastFun_castSucc, reflLastFun_castSucc]
  · rw [reflLastFun_last, reflLastFun_last, reflUnitInterval_involutive]

theorem continuous_reflLastFun (n : ℕ) : Continuous (reflLastFun n) := by
  rw [show reflLastFun n = fun u : Work.Stems.Cubical.IC (n+1) =>
      Fin.snoc (Fin.init u) (reflUnitInterval (u (Fin.last n))) from rfl]
  refine continuous_pi fun i => ?_
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · show Continuous fun u : Work.Stems.Cubical.IC (n+1) =>
      Fin.snoc (Fin.init u) (reflUnitInterval (u (Fin.last n))) (Fin.castSucc j)
    rw [show (fun u : Work.Stems.Cubical.IC (n+1) =>
        Fin.snoc (Fin.init u) (reflUnitInterval (u (Fin.last n))) (Fin.castSucc j))
        = fun u => u (Fin.castSucc j) from by
          funext u
          rw [Fin.snoc_castSucc]
          rfl]
    exact continuous_apply (Fin.castSucc j)
  · show Continuous fun u : Work.Stems.Cubical.IC (n+1) =>
      Fin.snoc (Fin.init u) (reflUnitInterval (u (Fin.last n))) (Fin.last n)
    rw [show (fun u : Work.Stems.Cubical.IC (n+1) =>
        Fin.snoc (Fin.init u) (reflUnitInterval (u (Fin.last n))) (Fin.last n))
        = fun u => reflUnitInterval (u (Fin.last n)) from by
          funext u
          rw [Fin.snoc_last]]
    exact reflUnitInterval.continuous.comp (continuous_apply (Fin.last n))

/-- The reflection of the last coordinate, as a homeomorphism of the cube `I^{n+1}`. -/
def reflLast (n : ℕ) : Work.Stems.Cubical.IC (n+1) ≃ₜ Work.Stems.Cubical.IC (n+1) where
  toFun := reflLastFun n
  invFun := reflLastFun n
  left_inv := reflLastFun_involutive n
  right_inv := reflLastFun_involutive n
  continuous_toFun := continuous_reflLastFun n
  continuous_invFun := continuous_reflLastFun n

/-! ## The reflection preserves the boundary of the cube -/

/-- The reflection of the last coordinate sends the boundary `∂I^{n+1}` into itself. -/
theorem reflLastFun_mem_cubeBdryS (n : ℕ) {u : Work.Stems.Cubical.IC (n+1)}
    (h : u ∈ cubeBdryS (n+1)) : reflLastFun n u ∈ cubeBdryS (n+1) := by
  rcases h with ⟨i, hi⟩
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · exact ⟨Fin.castSucc j, by rw [reflLastFun_castSucc]; exact hi⟩
  · rcases hi with h0 | h1
    · refine ⟨Fin.last n, Or.inr ?_⟩
      rw [reflLastFun_last, h0, reflUnitInterval_zero]
    · refine ⟨Fin.last n, Or.inl ?_⟩
      rw [reflLastFun_last, h1, reflUnitInterval_one]

/-- The reflection of the last coordinate preserves the boundary `∂I^{n+1}`. -/
theorem mem_cubeBdryS_reflLastFun (n : ℕ) (u : Work.Stems.Cubical.IC (n+1)) :
    u ∈ cubeBdryS (n+1) ↔ reflLastFun n u ∈ cubeBdryS (n+1) :=
  ⟨fun h => reflLastFun_mem_cubeBdryS n h, fun h => by
    have h' := reflLastFun_mem_cubeBdryS n h
    rw [reflLastFun_involutive] at h'
    exact h'⟩

/-! ## The reflection maps the slab `slabV` onto the slab `slabU` -/

@[simp] theorem lastCoord_reflLastFun (n : ℕ) (u : Work.Stems.Cubical.IC (n+1)) :
    lastCoord (reflLastFun n u) = 1 - lastCoord u := by
  rw [lastCoord, lastCoord, reflLastFun_last, reflUnitInterval_coe]

theorem mem_slabU_reflLastFun (n : ℕ) {u : Work.Stems.Cubical.IC (n+1)} (h : u ∈ slabV n) :
    reflLastFun n u ∈ slabU n := by
  have h' : (1:ℝ)/4 < lastCoord u := h
  have h2 : lastCoord (reflLastFun n u) = 1 - lastCoord u := lastCoord_reflLastFun n u
  show lastCoord (reflLastFun n u) < 3/4
  rw [h2]
  linarith

theorem mem_slabV_reflLastFun (n : ℕ) {u : Work.Stems.Cubical.IC (n+1)} (h : u ∈ slabU n) :
    reflLastFun n u ∈ slabV n := by
  have h' : lastCoord u < 3/4 := h
  have h2 : lastCoord (reflLastFun n u) = 1 - lastCoord u := lastCoord_reflLastFun n u
  show (1:ℝ)/4 < lastCoord (reflLastFun n u)
  rw [h2]
  linarith

/-! ## The induced homeomorphism of the slab pairs -/

/-- The reflection of the last coordinate, as a map `↥(slabV n) → ↥(slabU n)`. -/
def slabVToSlabU (n : ℕ) : ↥(slabV n) → ↥(slabU n) :=
  fun x => ⟨reflLastFun n x.1, mem_slabU_reflLastFun n x.2⟩

/-- The reflection of the last coordinate, as a map `↥(slabU n) → ↥(slabV n)`. -/
def slabUToSlabV (n : ℕ) : ↥(slabU n) → ↥(slabV n) :=
  fun y => ⟨reflLastFun n y.1, mem_slabV_reflLastFun n y.2⟩

@[simp] theorem slabVToSlabU_coe (n : ℕ) (x : ↥(slabV n)) :
    ((slabVToSlabU n x : ↥(slabU n)) : Work.Stems.Cubical.IC (n+1)) =
      reflLastFun n (x : Work.Stems.Cubical.IC (n+1)) := rfl

@[simp] theorem slabUToSlabV_coe (n : ℕ) (y : ↥(slabU n)) :
    ((slabUToSlabV n y : ↥(slabV n)) : Work.Stems.Cubical.IC (n+1)) =
      reflLastFun n (y : Work.Stems.Cubical.IC (n+1)) := rfl

theorem slabVToSlabU_left_inv (n : ℕ) (x : ↥(slabV n)) :
    slabUToSlabV n (slabVToSlabU n x) = x :=
  Subtype.ext (reflLastFun_involutive n x.1)

theorem slabVToSlabU_right_inv (n : ℕ) (y : ↥(slabU n)) :
    slabVToSlabU n (slabUToSlabV n y) = y :=
  Subtype.ext (reflLastFun_involutive n y.1)

theorem continuous_slabVToSlabU (n : ℕ) : Continuous (slabVToSlabU n) :=
  Continuous.subtype_mk ((continuous_reflLastFun n).comp continuous_subtype_val)
    (fun x => mem_slabU_reflLastFun n x.2)

theorem continuous_slabUToSlabV (n : ℕ) : Continuous (slabUToSlabV n) :=
  Continuous.subtype_mk ((continuous_reflLastFun n).comp continuous_subtype_val)
    (fun y => mem_slabV_reflLastFun n y.2)

/-- The reflection of the last coordinate, as a homeomorphism `↥(slabV n) ≃ₜ ↥(slabU n)`. -/
def slabVHomeoSlabU (n : ℕ) : ↥(slabV n) ≃ₜ ↥(slabU n) where
  toFun := slabVToSlabU n
  invFun := slabUToSlabV n
  left_inv := slabVToSlabU_left_inv n
  right_inv := slabVToSlabU_right_inv n
  continuous_toFun := continuous_slabVToSlabU n
  continuous_invFun := continuous_slabUToSlabV n

/-- The homeomorphism `↥(slabV n) ≃ₜ ↥(slabU n)` carries the boundary part of `slabV` onto the
boundary part of `slabU`. -/
theorem slabVHomeoSlabU_mem (n : ℕ) (y : ↥(slabV n)) :
    y ∈ {x : ↥(slabV n) |
        (x : Work.Stems.Cubical.IC (n+1)) ∈ slabV n ∩ cubeBdryS (n+1)} ↔
      slabVHomeoSlabU n y ∈ {x : ↥(slabU n) |
        (x : Work.Stems.Cubical.IC (n+1)) ∈ slabU n ∩ cubeBdryS (n+1)} := by
  change (y : Work.Stems.Cubical.IC (n+1)) ∈ slabV n ∩ cubeBdryS (n+1) ↔
    ((slabVHomeoSlabU n y : ↥(slabU n)) : Work.Stems.Cubical.IC (n+1)) ∈
      slabU n ∩ cubeBdryS (n+1)
  rw [Set.mem_inter_iff, Set.mem_inter_iff]
  constructor
  · intro h
    refine ⟨(slabVHomeoSlabU n y).2, ?_⟩
    exact (mem_cubeBdryS_reflLastFun n y.1).mp h.2
  · intro h
    refine ⟨y.2, ?_⟩
    exact (mem_cubeBdryS_reflLastFun n y.1).mpr h.2

/-! ## Compression is invariant under a homeomorphism of the pair -/

/-- The compression property of a pair is invariant under a homeomorphism of the pair: if
`e : Y → Y'` carries `A` onto `A'` then compression of `(Y', A')` implies compression of `(Y, A)`
in the same dimension. -/
theorem compressRel_of_homeo {Y Y' : Type} [TopologicalSpace Y] [TopologicalSpace Y']
    (e : Y ≃ₜ Y') {A : Set Y} {A' : Set Y'} (hA : ∀ y, y ∈ A ↔ e y ∈ A') (d : ℕ)
    (h : Work.RatHurewicz.CompressRel Y' A' d) :
    Work.RatHurewicz.CompressRel Y A d := by
  intro f hf
  have hf' : ∀ x, x ∈ Cube.boundary (Fin d) → e (f x) ∈ A' :=
    fun x hx => (hA (f x)).mp (hf x hx)
  obtain ⟨G, hG0, hGbd, hG1⟩ :=
    h ⟨fun x => e (f x), e.continuous.comp f.continuous⟩ hf'
  refine ⟨⟨fun z => e.symm (G z), e.symm.continuous.comp G.continuous⟩, ?_, ?_, ?_⟩
  · intro x
    show e.symm (G (x, 0)) = f x
    rw [hG0 x]
    exact e.symm_apply_apply (f x)
  · intro x hx t
    show e.symm (G (x, t)) = f x
    rw [hGbd x hx t]
    exact e.symm_apply_apply (f x)
  · intro x
    refine (hA (e.symm (G (x, 1)))).mpr ?_
    show e (e.symm (G (x, 1))) ∈ A'
    rw [e.apply_symm_apply]
    exact hG1 x

/-! ## The target theorem -/

theorem compressRel_slabV (n : ℕ) :
    ∀ d, Work.RatHurewicz.CompressRel ↥(Work.Serre.slabV n)
      {x : ↥(Work.Serre.slabV n) |
        (x : Work.Stems.Cubical.IC (n+1)) ∈ Work.Serre.slabV n ∩ Work.Serre.cubeBdryS (n+1)} d :=
  fun d => compressRel_of_homeo (slabVHomeoSlabU n) (slabVHomeoSlabU_mem n) d
    (compressRel_slabU n d)

end

end Work.Serre
