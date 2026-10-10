import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.Topology.Algebra.Group.Defs
import Submission.Work.AbsoluteKummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v w

namespace Work.AbsoluteKummer

open scoped Classical Topology
open Filter

noncomputable section

variable {G : Type u} {M : Type v} [TopologicalSpace G] [Group G] [AddCommGroup M]
variable [DistribMulAction G M]

/-! ## The open set `{g | g₀ * g fixes m}` -/

theorem isOpen_smul_stabilizer [IsTopologicalGroup G] (h : IsDiscreteModule G M) (g₀ : G) (m : M) :
    IsOpen {g : G | g₀⁻¹ * g ∈ MulAction.stabilizer G m} := by
  have hEq : {g : G | g₀⁻¹ * g ∈ MulAction.stabilizer G m} =
      (fun g : G => g₀⁻¹ * g) ⁻¹' (MulAction.stabilizer G m : Set G) := rfl
  rw [hEq]
  exact (h m).preimage (continuous_const.mul continuous_id)

theorem mem_self_smul_stabilizer (g₀ : G) (m : M) :
    g₀ ∈ {g : G | g₀⁻¹ * g ∈ MulAction.stabilizer G m} := by
  show g₀⁻¹ * g₀ ∈ MulAction.stabilizer G m
  simp

theorem smul_eq_of_mem_smul_stabilizer {g₀ g : G} {m : M}
    (hg : g ∈ {g : G | g₀⁻¹ * g ∈ MulAction.stabilizer G m}) : g • m = g₀ • m := by
  have hh : g₀⁻¹ • (g • m) = m := by
    rw [← mul_smul]
    exact MulAction.mem_stabilizer_iff.mp hg
  calc g • m = g₀ • (g₀⁻¹ • (g • m)) := (smul_inv_smul g₀ (g • m)).symm
    _ = g₀ • m := by rw [hh]

/-! ## Local constancy of the elementary maps -/

/-- Multiplication by `g` in the coefficient module is locally constant in `g`. -/
theorem isLocallyConstant_smul_of_isDiscreteModule [IsTopologicalGroup G]
    (h : IsDiscreteModule G M) (m : M) :
    IsLocallyConstant (fun g : G => g • m) :=
  fun g₀ => ⟨_, isOpen_smul_stabilizer h g₀ m, mem_self_smul_stabilizer g₀ m,
    fun _ hg => smul_eq_of_mem_smul_stabilizer hg⟩

/-- The function `(g, h) ↦ g • f h` is locally constant when `f` is. -/
theorem isLocallyConstant_smul_comp [IsTopologicalGroup G] (h : IsDiscreteModule G M) {f : G → M}
    (hf : IsLocallyConstant f) : IsLocallyConstant (fun p : G × G => p.1 • f p.2) := by
  intro p₀
  obtain ⟨g₀, h₀⟩ := p₀
  obtain ⟨W, hWo, hWmem, hWc⟩ := hf h₀
  refine ⟨{g : G | g₀⁻¹ * g ∈ MulAction.stabilizer G (f h₀)} ×ˢ W,
    (isOpen_smul_stabilizer h g₀ (f h₀)).prod hWo, ⟨mem_self_smul_stabilizer g₀ (f h₀), hWmem⟩, ?_⟩
  rintro ⟨g, h'⟩ ⟨hg, hh⟩
  have hfh : f h' = f h₀ := hWc h' hh
  change g • f h' = g₀ • f h₀
  rw [hfh]
  exact smul_eq_of_mem_smul_stabilizer hg

/-- `d⁰ a` is locally constant for a discrete module. -/
theorem isLocallyConstant_d0 [IsTopologicalGroup G] (h : IsDiscreteModule G M) (a : M) :
    IsLocallyConstant (Work.GroupCohomology.d0 G M a) := by
  show IsLocallyConstant (fun g : G => g • a - a)
  exact (isLocallyConstant_smul_of_isDiscreteModule h a).sub (isLocallyConstant_const a)

/-- `d¹ f` is locally constant when `f` is. -/
theorem isLocallyConstant_d1 [IsTopologicalGroup G] (h : IsDiscreteModule G M) {f : G → M}
    (hf : IsLocallyConstant f) : IsLocallyConstant (Work.GroupCohomology.d1 G M f) := by
  show IsLocallyConstant (fun p : G × G => p.1 • f p.2 - f (p.1 * p.2) + f p.1)
  exact ((isLocallyConstant_smul_comp h hf).sub
    (hf.comp (continuous_fst.mul continuous_snd))).add (hf.comp continuous_fst)

/-! ## `B¹ ≤ Z¹` and `B² ≤ Z²` -/

theorem isCrossedHom_of_mem_Z1 {f : G → M} (hf : f ∈ Z1 G M) :
    Work.GroupCohomology.IsCrossedHom G M f := ((mem_Z1_iff f).mp hf).1

theorem isLocallyConstant_of_mem_Z1 {f : G → M} (hf : f ∈ Z1 G M) : IsLocallyConstant f :=
  ((mem_Z1_iff f).mp hf).2

theorem mem_Z1_of {f : G → M} (h1 : Work.GroupCohomology.IsCrossedHom G M f)
    (h2 : IsLocallyConstant f) : f ∈ Z1 G M := (mem_Z1_iff f).mpr ⟨h1, h2⟩

/-- The continuous coboundaries are continuous cocycles, for a discrete module. -/
theorem B1_le_Z1 [IsTopologicalGroup G] (h : IsDiscreteModule G M) : B1 G M ≤ Z1 G M := by
  rintro f ⟨a, rfl⟩
  exact mem_Z1_of (Work.GroupCohomology.d0_mem_Z1 G M a) (isLocallyConstant_d0 h a)

/-- The continuous `2`-coboundaries are continuous `2`-cocycles, for a discrete module. -/
theorem B2_le_Z2 [IsTopologicalGroup G] (h : IsDiscreteModule G M) : B2 G M ≤ Z2 G M := by
  intro c hc
  rw [mem_B2_iff] at hc
  obtain ⟨f, hf, rfl⟩ := hc
  rw [mem_Z2_iff]
  exact ⟨Work.GroupCohomology.d1_mem_Z2 G M f, isLocallyConstant_d1 h (mem_C1c_iff f |>.mp hf)⟩

/-! ## The elementary `Z¹` API -/

theorem Z1.map_one (f : Z1 G M) : (f : G → M) 1 = 0 := by
  have hf := isCrossedHom_of_mem_Z1 f.2
  have h : (f : G → M) 1 = (f : G → M) 1 + (f : G → M) 1 := by simpa using hf 1 1
  exact (add_left_cancel (a := (f : G → M) 1) (by simpa using h)).symm

theorem Z1.map_inv (f : Z1 G M) (g : G) : g • (f : G → M) g⁻¹ = -(f : G → M) g := by
  have hf := isCrossedHom_of_mem_Z1 f.2
  have h : g • (f : G → M) g⁻¹ + (f : G → M) g = 0 := by
    have h2 := hf g g⁻¹
    rw [mul_inv_cancel] at h2
    rw [Z1.map_one f] at h2
    exact h2.symm
  exact sub_eq_zero.mp (by rw [sub_neg_eq_add]; exact h)

/-! ## Functoriality in the coefficients -/

section Map

variable {N : Type w} [AddCommGroup N] [DistribMulAction G N]

/-- The map `C¹_c(G,M) → C¹_c(G,N)` induced by `φ`. -/
def mapC1c (φ : M →+ N) : C1c G M →+ C1c G N where
  toFun f := ⟨fun g => φ ((f : G → M) g), IsLocallyConstant.map φ f.2⟩
  map_zero' := Subtype.ext (funext fun g => by simp)
  map_add' f f' := Subtype.ext (funext fun g => by simp)

@[simp] theorem mapC1c_apply (φ : M →+ N) (f : C1c G M) (g : G) :
    ((mapC1c φ f : C1c G N) : G → N) g = φ ((f : G → M) g) := rfl

/-- The map `Z¹_c(G,M) → Z¹_c(G,N)` induced by an equivariant `φ`. -/
def mapZ1 (φ : M →+ N) (hφ : Work.GroupCohomology.IsEquivariant G φ) : Z1 G M →+ Z1 G N where
  toFun f := ⟨fun g => φ ((f : G → M) g), by
    refine mem_Z1_of ?_ (IsLocallyConstant.map φ (isLocallyConstant_of_mem_Z1 f.2))
    intro g h
    show φ ((f : G → M) (g * h)) = g • φ ((f : G → M) h) + φ ((f : G → M) g)
    rw [isCrossedHom_of_mem_Z1 f.2 g h, map_add, hφ]⟩
  map_zero' := Subtype.ext (funext fun g => by simp)
  map_add' f f' := Subtype.ext (funext fun g => by simp)

@[simp] theorem mapZ1_apply (φ : M →+ N) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (f : Z1 G M) (g : G) : (mapZ1 φ hφ f : G → N) g = φ ((f : G → M) g) := rfl

theorem mapC1c_mem_B1 (φ : M →+ N) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    {f : G → M} (hf : f ∈ B1 G M) : (fun g => φ (f g)) ∈ B1 G N := by
  obtain ⟨a, rfl⟩ := (mem_B1_iff f).mp hf
  refine AddMonoidHom.mem_range.mpr ⟨φ a, ?_⟩
  funext g
  simp only [Work.GroupCohomology.d0_apply]
  rw [map_sub, hφ]

/-- The map `H¹(G,M) → H¹(G,N)` induced by an equivariant additive map of `G`-modules. -/
noncomputable def mapH1 (φ : M →+ N) (hφ : Work.GroupCohomology.IsEquivariant G φ) :
    H1 G M →+ H1 G N :=
  QuotientAddGroup.lift ((B1 G M).comap (Z1 G M).subtype) ((H1π G N).comp (mapZ1 φ hφ)) (by
    intro x hx
    have hx' : ((x : Z1 G M) : G → M) ∈ B1 G M := by
      simpa using (AddSubgroup.mem_comap.mp hx)
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, H1π_eq_zero_iff]
    exact mapC1c_mem_B1 φ hφ hx')

theorem mapH1_H1π (φ : M →+ N) (hφ : Work.GroupCohomology.IsEquivariant G φ) (f : Z1 G M) :
    mapH1 φ hφ (H1π G M f) = H1π G N (mapZ1 φ hφ f) :=
  QuotientAddGroup.lift_mk' _ _ f

/-- The map `C²_c(G,M) → C²_c(G,N)` induced by `φ`. -/
def mapC2c (φ : M →+ N) : C2c G M →+ C2c G N where
  toFun f := ⟨fun p => φ ((f : G × G → M) p), IsLocallyConstant.map φ f.2⟩
  map_zero' := by ext p; simp
  map_add' f f' := by ext p; simp [map_add]

/-- The map `Z²_c(G,M) → Z²_c(G,N)` induced by an equivariant `φ`. -/
def mapZ2 (φ : M →+ N) (hφ : Work.GroupCohomology.IsEquivariant G φ) : Z2 G M →+ Z2 G N where
  toFun c := ⟨fun p => φ ((c : G × G → M) p), by
    rw [mem_Z2_iff]
    refine ⟨?_, IsLocallyConstant.map φ ((mem_Z2_iff (c : G × G → M)).mp c.2).2⟩
    intro g h k
    have hc := ((mem_Z2_iff (c : G × G → M)).mp c.2).1 g h k
    rw [← map_add, hc, map_add, hφ]⟩
  map_zero' := by ext p; simp
  map_add' c c' := by ext p; simp [map_add]

@[simp] theorem mapZ2_apply (φ : M →+ N) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (c : Z2 G M) (p : G × G) : (mapZ2 φ hφ c : G × G → N) p = φ ((c : G × G → M) p) := rfl

theorem mapC1c_mem_B2 (φ : M →+ N) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    {c : G × G → M} (hc : c ∈ B2 G M) : (fun p => φ (c p)) ∈ B2 G N := by
  rw [mem_B2_iff] at hc
  obtain ⟨f, hf, rfl⟩ := hc
  rw [mem_B2_iff]
  refine ⟨fun g => φ ((f : G → M) g), IsLocallyConstant.map φ ((mem_C1c_iff f).mp hf), ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  simp only [Work.GroupCohomology.d1_apply, map_add, map_sub]
  rw [hφ]

/-- The map `H²(G,M) → H²(G,N)` induced by an equivariant additive map of `G`-modules. -/
noncomputable def mapH2 (φ : M →+ N) (hφ : Work.GroupCohomology.IsEquivariant G φ) :
    H2 G M →+ H2 G N :=
  QuotientAddGroup.lift ((B2 G M).comap (Z2 G M).subtype) ((H2π G N).comp (mapZ2 φ hφ)) (by
    intro x hx
    have hx' : ((x : Z2 G M) : G × G → M) ∈ B2 G M := by
      simpa using (AddSubgroup.mem_comap.mp hx)
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, H2π_eq_zero_iff]
    exact mapC1c_mem_B2 φ hφ hx')

theorem mapH2_H2π (φ : M →+ N) (hφ : Work.GroupCohomology.IsEquivariant G φ) (c : Z2 G M) :
    mapH2 φ hφ (H2π G M c) = H2π G N (mapZ2 φ hφ c) :=
  QuotientAddGroup.lift_mk' _ _ c

theorem mapH1_id_H1π (f : Z1 G M) :
    mapH1 (G := G) (M := M) (N := M) (AddMonoidHom.id M)
      (Work.GroupCohomology.isEquivariant_id (G := G) (A := M)) (H1π G M f) = H1π G M f := by
  rw [mapH1_H1π]
  exact congrArg (H1π G M) (Subtype.ext rfl)

theorem mapH1_comp_H1π {N : Type w} {P : Type u} [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G N] [DistribMulAction G P]
    (φ : M →+ N) (ψ : N →+ P) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hψ : Work.GroupCohomology.IsEquivariant G ψ) (f : Z1 G M) :
    mapH1 (ψ.comp φ) (hψ.comp hφ) (H1π G M f) =
      mapH1 ψ hψ (mapH1 φ hφ (H1π G M f)) := by
  rw [mapH1_H1π, mapH1_H1π, mapH1_H1π]
  exact congrArg (H1π G P) (Subtype.ext rfl)

end Map

/-! ## A locally constant function on a compact space has finite image -/

theorem IsLocallyConstant.isOpen_preimage_singleton {X : Type u} [TopologicalSpace X]
    {N : Type v} {f : X → N} (hf : IsLocallyConstant f) (m : N) :
    IsOpen (f ⁻¹' ({m} : Set N)) := by
  rw [isOpen_iff_mem_nhds]
  rintro x hx
  obtain ⟨U, hU, hxU, hfU⟩ := hf x
  have hsub : U ⊆ f ⁻¹' ({m} : Set N) := by
    intro y hy
    rw [Set.mem_preimage, Set.mem_singleton_iff, hfU y hy]
    exact hx
  exact Filter.mem_of_superset (hU.mem_nhds hxU) hsub

theorem finite_image_of_isLocallyConstant {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {N : Type v} {f : X → N} (hf : IsLocallyConstant f) : (Set.range f).Finite := by
  have hcover : (Set.univ : Set X) ⊆ ⋃ m : N, f ⁻¹' ({m} : Set N) := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨f x, rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun m : N => f ⁻¹' ({m} : Set N))
    (fun m => hf.isOpen_preimage_singleton m) hcover
  refine Set.Finite.subset t.finite_toSet ?_
  rintro m ⟨x, rfl⟩
  obtain ⟨m', hm't, hx'⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hx'
  exact hx' ▸ hm't

/-! ## Finite Hilbert 90 (Noether's form) -/

/-- **Hilbert's Theorem 90 (Noether's form, multiplicative).**  For a finite extension of fields
`L/K`, every crossed homomorphism `f : Gal(L/K) → Lˣ` is of the form `σ ↦ σ b / b`. -/
theorem exists_algEquiv_div_of_isCrossedHom {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (f : (L ≃ₐ[K] L) → Lˣ)
    (hf : ∀ σ τ : L ≃ₐ[K] L, f (σ * τ) = f σ * σ (f τ : L)) :
    ∃ b : Lˣ, ∀ σ : L ≃ₐ[K] L, (f σ : L) = σ (b : L) / (b : L) := by
  have hf' : groupCohomology.IsMulCocycle₁ f := fun σ τ => by
    rw [AlgEquiv.smul_units_def, Units.ext_iff, Units.val_mul, Units.coe_map, mul_comm]
    exact hf σ τ
  obtain ⟨b, hb⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf'
  refine ⟨b, fun σ => ?_⟩
  have h := hb σ
  rw [AlgEquiv.smul_units_def] at h
  have h' := congrArg (fun u : Lˣ => (u : L)) h
  rw [Units.val_div_eq_div_val, Units.coe_map] at h'
  exact h'.symm

end

end Work.AbsoluteKummer
