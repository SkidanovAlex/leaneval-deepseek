import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

/-!
# Covolume of a `ℤ`-lattice in a product, and the kernel/image decomposition

Let `E₁`, `E₂` be finite-dimensional real inner product spaces and `L ⊆ E₁ × E₂` a full
`ℤ`-lattice.  Let `Λ = {x | (x,0) ∈ L}` (the "kernel" of the second projection) and
`M = {y | ∃ x, (x,y) ∈ L}` (its "image"), both assumed to be full `ℤ`-lattices as well.  Then

  `covolume L = covolume Λ * covolume M`.

This is the multiplicativity of the covolume along the split short exact sequence
`0 → Λ → L → M → 0`.  The proof is geometric and explicit: if `D_Λ ⊆ E₁` and `D_M ⊆ E₂` are
fundamental domains of `Λ` and `M`, and `σ : M → E₁` is any section of the second projection
(`(σ m, m) ∈ L` for all `m ∈ M`), then `D_Λ ×ˢ D_M` is a fundamental domain of `L` in `E₁ × E₂`:
given `(x,y)` reduce `y` modulo `M`, then reduce `x - σ m₀` modulo `Λ`, and the representative is
unique.  Since the volume on `E₁ × E₂` is the product of the volumes, the covolume — being the
volume of a fundamental domain — factorises.
-/

namespace Work.BW

open MeasureTheory

/-- Pointwise uniqueness of the representative of `x` in the `ZSpan` fundamental domain attached
to a `ℤ`-basis `b` of a full `ℤ`-lattice `L`: for every `x : E` there is exactly one `v : L` with
`v +ᵥ x` in the fundamental domain of the basis `b` read off in `E`. -/
theorem existsUnique_vadd_mem_fundamentalDomain_ofZLatticeBasis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℤ L) (x : E) :
    ∃! v : L, v +ᵥ x ∈ ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ) := by
  have hspan : Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ)) = L :=
    Module.Basis.ofZLatticeBasis_span ℝ L b
  obtain ⟨v₀, hv₀, huniq⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ) x
  have hv0L : (v₀ : E) ∈ L := hspan.le v₀.2
  refine ⟨⟨v₀, hv0L⟩, ?_, ?_⟩
  · show (⟨(v₀ : E), hv0L⟩ : L) +ᵥ x ∈ ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)
    rw [Submodule.vadd_def]
    exact hv₀
  · rintro ⟨v, hvL⟩ hv
    have hv' : (v : E) ∈ Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ)) := hspan.ge hvL
    have h : (⟨v, hv'⟩ : Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ))) +ᵥ x
        ∈ ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ) := by
      rw [Submodule.vadd_def] at hv ⊢
      exact hv
    have this := huniq ⟨v, hv'⟩ h
    have h2 : (v : E) = (v₀ : E) :=
      congrArg (fun w : ↥(Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ))) => (w : E)) this
    exact Subtype.ext h2

theorem covolume_prod {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
      [MeasurableSpace E₁] [BorelSpace E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
      [MeasurableSpace E₂] [BorelSpace E₂]
    (L : Submodule ℤ (E₁ × E₂)) [DiscreteTopology ↥L] [IsZLattice ℝ L]
    (Λ : Submodule ℤ E₁) (hΛ : ∀ x : E₁, x ∈ Λ ↔ (x, 0) ∈ L) [DiscreteTopology ↥Λ]
      [IsZLattice ℝ Λ]
    (M : Submodule ℤ E₂) (hM : ∀ y : E₂, y ∈ M ↔ ∃ x : E₁, (x, y) ∈ L)
      [DiscreteTopology ↥M] [IsZLattice ℝ M] :
    ZLattice.covolume L = ZLattice.covolume Λ * ZLattice.covolume M := by
  classical
  -- `ℤ`-bases of the kernel and the image, and the associated fundamental domains.
  let bΛ := Module.Free.chooseBasis ℤ Λ
  let bM := Module.Free.chooseBasis ℤ M
  let DΛ : Set E₁ := ZSpan.fundamentalDomain (bΛ.ofZLatticeBasis ℝ)
  let DM : Set E₂ := ZSpan.fundamentalDomain (bM.ofZLatticeBasis ℝ)
  have huniqΛ : ∀ x : E₁, ∃! v : Λ, v +ᵥ x ∈ DΛ :=
    fun x => existsUnique_vadd_mem_fundamentalDomain_ofZLatticeBasis bΛ x
  have huniqM : ∀ y : E₂, ∃! v : M, v +ᵥ y ∈ DM :=
    fun y => existsUnique_vadd_mem_fundamentalDomain_ofZLatticeBasis bM y
  -- A section `σ` of the second projection `L → M`.
  let σ : M → E₁ := fun m => Classical.choose ((hM (m : E₂)).mp m.2)
  have hσ : ∀ m : M, (σ m, (m : E₂)) ∈ L :=
    fun m => Classical.choose_spec ((hM (m : E₂)).mp m.2)
  -- `DΛ ×ˢ DM` is a fundamental domain of `L`.
  have huniqL : ∀ z : E₁ × E₂, ∃! g : L, g +ᵥ z ∈ DΛ ×ˢ DM := by
    rintro ⟨x, y⟩
    obtain ⟨m₀, hm₀, huniq_m⟩ := huniqM y
    obtain ⟨l₀, hl₀, huniq_l⟩ := huniqΛ (σ m₀ + x)
    have hmem : (((l₀ : E₁) + σ m₀), (m₀ : E₂)) ∈ L := by
      have h1 : ((l₀ : E₁), (0 : E₂)) ∈ L := (hΛ (l₀ : E₁)).mp l₀.2
      have h2 : (σ m₀, (m₀ : E₂)) ∈ L := hσ m₀
      have := add_mem h1 h2
      simpa using this
    refine ⟨⟨((l₀ : E₁) + σ m₀, (m₀ : E₂)), hmem⟩, ?_, ?_⟩
    · show ((((l₀ : E₁) + σ m₀, (m₀ : E₂)) : E₁ × E₂) + (x, y)) ∈ DΛ ×ˢ DM
      rw [Set.mem_prod]
      constructor
      · show ((l₀ : E₁) + σ m₀) + x ∈ DΛ
        rw [add_assoc]; exact hl₀
      · exact hm₀
    · rintro ⟨⟨a, b⟩, hab⟩ hab_mem
      have hab' : ((a, b) : E₁ × E₂) + (x, y) ∈ DΛ ×ˢ DM := by
        rwa [Submodule.vadd_def] at hab_mem
      have h1 : a + x ∈ DΛ := hab'.1
      have h2 : b + y ∈ DM := hab'.2
      have hbM : b ∈ M := (hM b).mpr ⟨a, hab⟩
      have hb_eq : (⟨b, hbM⟩ : M) = m₀ := by
        apply huniq_m
        show (⟨b, hbM⟩ : M) +ᵥ y ∈ DM
        rw [Submodule.vadd_def]
        exact h2
      have hb : b = (m₀ : E₂) := congrArg (fun w : M => (w : E₂)) hb_eq
      have hker : a - σ m₀ ∈ Λ := by
        rw [hΛ]
        have hsub : (a - σ m₀, (0 : E₂)) = (a, b) - (σ m₀, (m₀ : E₂)) := by
          ext <;> simp [hb]
        rw [hsub]
        exact sub_mem hab (hσ m₀)
      have hl_eq : (⟨a - σ m₀, hker⟩ : Λ) = l₀ := by
        apply huniq_l
        show (a - σ m₀) + (σ m₀ + x) ∈ DΛ
        have h : a - σ m₀ + (σ m₀ + x) = a + x := by rw [← add_assoc, sub_add_cancel]
        rw [h]; exact h1
      have ha : a = (l₀ : E₁) + σ m₀ :=
        sub_eq_iff_eq_add.mp (congrArg (fun w : Λ => (w : E₁)) hl_eq)
      exact Subtype.ext (Prod.ext ha hb)
  haveI : Measure.IsAddHaarMeasure (volume : Measure (E₁ × E₂)) :=
    Measure.prod.instIsAddHaarMeasure volume volume
  have hmeasΛ : MeasurableSet DΛ := ZSpan.fundamentalDomain_measurableSet (bΛ.ofZLatticeBasis ℝ)
  have hmeasM : MeasurableSet DM := ZSpan.fundamentalDomain_measurableSet (bM.ofZLatticeBasis ℝ)
  have hmeas : MeasurableSet (DΛ ×ˢ DM) := hmeasΛ.prod hmeasM
  have hfundL : IsAddFundamentalDomain L (DΛ ×ˢ DM) volume :=
    IsAddFundamentalDomain.mk' hmeas.nullMeasurableSet huniqL
  have hfundΛ : IsAddFundamentalDomain Λ DΛ volume := ZLattice.isAddFundamentalDomain bΛ volume
  have hfundM : IsAddFundamentalDomain M DM volume := ZLattice.isAddFundamentalDomain bM volume
  -- The covolume is the volume of any fundamental domain.
  have hcovL : ZLattice.covolume L = volume.real (DΛ ×ˢ DM) :=
    ZLattice.covolume_eq_measure_fundamentalDomain L volume hfundL
  have hcovΛ : ZLattice.covolume Λ = volume.real DΛ :=
    ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hfundΛ
  have hcovM : ZLattice.covolume M = volume.real DM :=
    ZLattice.covolume_eq_measure_fundamentalDomain M volume hfundM
  -- The volume is multiplicative on products of sets.
  have hvol : volume.real (DΛ ×ˢ DM) = volume.real DΛ * volume.real DM := by
    rw [Measure.volume_eq_prod E₁ E₂, measureReal_prod_prod]
  rw [hcovL, hcovΛ, hcovM, hvol]

end Work.BW
