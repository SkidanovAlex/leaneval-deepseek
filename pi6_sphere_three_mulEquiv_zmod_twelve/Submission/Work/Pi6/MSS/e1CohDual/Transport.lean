import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Transport of indices in an `ℕ`-indexed chain complex

Bookkeeping lemmas for chain complexes `K : ChainComplex (ModuleCat 𝕜) ℕ`: the canonical
transports of the objects of the complex, of the cycles and of the homology along an equality of
degrees, and their compatibility with the differential, with chain maps, and with `homologyπ` and
`cyclesMap`.
-/

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {𝕜 : Type} [Field 𝕜]

noncomputable section

/-- The index transport of the objects of a chain complex. -/
noncomputable def Xcast (K : ChainComplex (ModuleCat 𝕜) ℕ) {a b : ℕ} (h : a = b) :
    K.X a →ₗ[𝕜] K.X b :=
  (CategoryTheory.eqToHom (congrArg (fun n => K.X n) h)).hom

/-- The index transport of the cycles. -/
noncomputable def CycCast (K : ChainComplex (ModuleCat 𝕜) ℕ) {a b : ℕ} (h : a = b) :
    K.cycles a →ₗ[𝕜] K.cycles b :=
  (CategoryTheory.eqToHom (congrArg (fun n => K.cycles n) h)).hom

/-- The index transport of the homology. -/
noncomputable def HomCast (K : ChainComplex (ModuleCat 𝕜) ℕ) {a b : ℕ} (h : a = b) :
    K.homology a →ₗ[𝕜] K.homology b :=
  (CategoryTheory.eqToHom (congrArg (fun n => K.homology n) h)).hom

@[simp] theorem Xcast_rfl (K : ChainComplex (ModuleCat 𝕜) ℕ) {a : ℕ} (x : K.X a) :
    Xcast K rfl x = x := rfl

@[simp] theorem CycCast_rfl (K : ChainComplex (ModuleCat 𝕜) ℕ) {a : ℕ} (z : K.cycles a) :
    CycCast K rfl z = z := rfl

@[simp] theorem HomCast_rfl (K : ChainComplex (ModuleCat 𝕜) ℕ) {a : ℕ} (z : K.homology a) :
    HomCast K rfl z = z := rfl

theorem Xcast_d (K : ChainComplex (ModuleCat 𝕜) ℕ) {a b j : ℕ} (h : a = b) (x : K.X a) :
    (K.d b j).hom (Xcast K h x) = (K.d a j).hom x := by
  cases h
  simp

theorem Xcast_symm (K : ChainComplex (ModuleCat 𝕜) ℕ) {a b : ℕ} (h : a = b) (x : K.X a) :
    Xcast K h.symm (Xcast K h x) = x := by
  cases h
  simp

theorem Xcast_symm' (K : ChainComplex (ModuleCat 𝕜) ℕ) {a b : ℕ} (h : a = b) (y : K.X b) :
    Xcast K h (Xcast K h.symm y) = y := by
  cases h
  simp

theorem map_Xcast {K L : ChainComplex (ModuleCat 𝕜) ℕ} (f : K ⟶ L) {a b : ℕ} (h : a = b)
    (x : K.X a) :
    (f.f b).hom (Xcast K h x) = Xcast L h ((f.f a).hom x) := by
  cases h
  simp

theorem HomCast_homologyπ (K : ChainComplex (ModuleCat 𝕜) ℕ) {a b : ℕ} (h : a = b)
    (z : K.cycles a) :
    HomCast K h ((K.homologyπ a).hom z) = (K.homologyπ b).hom (CycCast K h z) := by
  cases h
  simp

theorem iCycles_CycCast (K : ChainComplex (ModuleCat 𝕜) ℕ) {a b : ℕ} (h : a = b)
    (z : K.cycles a) :
    (K.iCycles b).hom (CycCast K h z) = Xcast K h ((K.iCycles a).hom z) := by
  cases h
  simp

theorem map_CycCast {K L : ChainComplex (ModuleCat 𝕜) ℕ} (f : K ⟶ L) {a b : ℕ} (h : a = b)
    (z : K.cycles a) :
    (cyclesMap f b) (CycCast K h z) = CycCast L h ((cyclesMap f a) z) := by
  cases h
  simp

theorem cyclesMk_iCycles (K : ChainComplex (ModuleCat 𝕜) ℕ) {a : ℕ} (z : K.cycles a) (j : ℕ)
    (hj : (ComplexShape.down ℕ).next a = j) (hz : (K.d a j).hom ((K.iCycles a).hom z) = 0) :
    K.cyclesMk ((K.iCycles a).hom z) j hj hz = z := by
  apply (ModuleCat.mono_iff_injective (K.iCycles a)).mp inferInstance
  simpa using HomologicalComplex.i_cyclesMk (K := K) (x := (K.iCycles a).hom z) (j := j)
    (hj := hj) (hx := hz)

theorem iCycles_cyclesMk (K : ChainComplex (ModuleCat 𝕜) ℕ) {a : ℕ} (x : K.X a) (j : ℕ)
    (hj : (ComplexShape.down ℕ).next a = j) (hx : (K.d a j).hom x = 0) :
    (K.iCycles a).hom (K.cyclesMk x j hj hx) = x := by
  simpa using HomologicalComplex.i_cyclesMk (K := K) (x := x) (j := j) (hj := hj) (hx := hx)

/-- Naturality of `homologyπ` under `homologyMap` (elementwise). -/
theorem homologyMap_homologyπ {K L : ChainComplex (ModuleCat 𝕜) ℕ} (φ : K ⟶ L) (i : ℕ)
    (z : K.cycles i) :
    (homologyMap φ i).hom ((K.homologyπ i).hom z) = (L.homologyπ i).hom (cyclesMap φ i z) := by
  have h := HomologicalComplex.homologyπ_naturality (φ := φ) (i := i)
  have h2 := congrArg (fun (g : K.cycles i ⟶ L.homology i) => (ModuleCat.Hom.hom g) z) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- The underlying chain of the `cyclesMap` of a cycle. -/
theorem iCycles_cyclesMap {K L : ChainComplex (ModuleCat 𝕜) ℕ} (φ : K ⟶ L) (i : ℕ)
    (z : K.cycles i) :
    (L.iCycles i).hom (cyclesMap φ i z) = (φ.f i).hom ((K.iCycles i).hom z) := by
  have h := HomologicalComplex.cyclesMap_i (φ := φ) (i := i)
  have h2 := congrArg (fun (g : K.cycles i ⟶ L.X i) => (ModuleCat.Hom.hom g) z) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

end

end Work.Pi6.MSS
