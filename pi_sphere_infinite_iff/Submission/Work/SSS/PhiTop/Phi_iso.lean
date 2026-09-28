import Mathlib
import Submission.Work.SSS.FibreColDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.SSS.PhiTop

attribute [-instance] AddCommGroup.toIntModule

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

/-! ## Elementary elementwise lemmas for chain complexes of `ℤ`-modules -/

lemma iCycles_inj (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    Function.Injective (C.iCycles n).hom :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

/-- Elementwise naturality of `homologyπ`. -/
lemma homologyMap_homologyπ_apply (C D : ChainComplex (ModuleCat ℤ) ℕ) (φ : C ⟶ D) (n : ℕ)
    (z : C.cycles n) :
    (HomologicalComplex.homologyMap φ n).hom ((C.homologyπ n).hom z)
      = (D.homologyπ n).hom ((C.cyclesMap φ n).hom z) := by
  have h := HomologicalComplex.homologyπ_naturality φ n
  have hh := congrArg (fun (g : C.cycles n ⟶ D.homology n) => (ModuleCat.Hom.hom g) z) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh

/-- Elementwise `cyclesMap_i`. -/
lemma cyclesMap_i_apply (C D : ChainComplex (ModuleCat ℤ) ℕ) (φ : C ⟶ D) (n : ℕ)
    (z : C.cycles n) :
    (D.iCycles n).hom ((C.cyclesMap φ n).hom z) = (φ.f n).hom ((C.iCycles n).hom z) := by
  have h := HomologicalComplex.cyclesMap_i φ n
  have hh := congrArg (fun (g : C.cycles n ⟶ D.X n) => (ModuleCat.Hom.hom g) z) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh

/-- Elementwise commutation of a chain map with the differential. -/
lemma chainMap_comm_apply' (A B : ChainComplex (ModuleCat ℤ) ℕ) (f : A ⟶ B) (i j : ℕ)
    (x : A.X i) :
    ((B.d i j).hom) ((f.f i).hom x) = ((f.f j).hom) (((A.d i j).hom) x) := by
  have h := HomologicalComplex.Hom.comm f i j
  have hh := congrArg (fun (g : A.X i ⟶ B.X j) => (ModuleCat.Hom.hom g) x) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh

/-- The underlying chain of a cycle is killed by the differential. -/
lemma iCycles_d_apply (C : ChainComplex (ModuleCat ℤ) ℕ) (i j : ℕ) (z : C.cycles i) :
    ((C.d i j).hom) ((C.iCycles i).hom z) = 0 := by
  have h := HomologicalComplex.iCycles_d C i j
  have hh := congrArg (fun (g : C.cycles i ⟶ C.X j) => (ModuleCat.Hom.hom g) z) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using hh

/-! ## The index identities `next t = t - 1`, `prev t = t + 1` -/

lemma next_eq (t : ℕ) : (ComplexShape.down ℕ).next t = t - 1 := by
  rcases t with _ | k <;> simp

lemma prev_eq (t : ℕ) : (ComplexShape.down ℕ).prev t = t + 1 := ChainComplex.prev ℕ t

/-- The kernel of the differential of `C` at `t` agrees with the kernel of the differential
entering the short complex `C.sc t`. -/
lemma mem_ker_g_iff (C : ChainComplex (ModuleCat ℤ) ℕ) (t : ℕ) (x : C.X t) :
    ((C.sc t).g.hom) x = 0 ↔ (dC C t (t-1)) x = 0 := by
  simp only [dC]
  have hnext := next_eq t
  have h := HomologicalComplex.d_comp_XIsoOfEq_hom C hnext t
  have h2 : ∀ y : C.X t, ((C.XIsoOfEq hnext).hom) (((C.d t ((ComplexShape.down ℕ).next t)).hom) y)
      = ((C.d t (t-1)).hom) y := by
    intro y
    have hh := congrArg (fun (g : C.X t ⟶ C.X (t-1)) => g.hom y) h
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  have hg : ((C.sc t).g.hom) x = ((C.d t ((ComplexShape.down ℕ).next t)).hom) x := rfl
  constructor
  · intro hx
    rw [hg] at hx
    rw [← h2 x, hx, map_zero]
  · intro hx
    have hinj : Function.Injective (C.XIsoOfEq hnext).hom :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    have hx' : ((C.d t ((ComplexShape.down ℕ).next t)).hom) x = 0 := by
      refine hinj ?_
      rw [h2 x, hx, map_zero]
    rw [hg]
    exact hx'

/-- Membership in `Zof ξ t`, unfolded. -/
lemma mem_Zof_iff {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C) (t : ℕ)
    (x : C.X t) :
    x ∈ Zof ξ t ↔ (dC C t (t-1)) x = 0 ∧ x ∈ Fch ξ 0 t := by
  rw [Zof, Submodule.mem_inf, LinearMap.mem_ker]

/-- `Z_t(F_0)` is contained in the cycles of the short complex `C.sc t`. -/
lemma Zof_le_ker_g {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C) (t : ℕ) :
    Zof ξ t ≤ LinearMap.ker ((C.sc t).g.hom) := by
  intro x hx
  rw [LinearMap.mem_ker]
  exact (mem_ker_g_iff C t x).mpr ((mem_Zof_iff ξ t x).mp hx).1

/-- Saturation: `F_n` contains every `n`-chain, so `Fch ξ n n = ⊤`. -/
lemma Fch_top {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C) (n : ℕ) :
    Fch ξ n n = ⊤ := by
  rw [Fch, LinearMap.range_eq_top]
  haveI : IsIso ((ξ.incl n).f n) := ξ.sat n
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- The range of the differential `F_{t+1} → C` of the short complex `C.sc t` is the range of
`dC C (t+1) t`. -/
lemma range_f_sc (C : ChainComplex (ModuleCat ℤ) ℕ) (t : ℕ) :
    LinearMap.range ((C.sc t).f.hom) = LinearMap.range (dC C (t+1) t) := by
  have hprev := prev_eq t
  have h := HomologicalComplex.XIsoOfEq_hom_comp_d C hprev t
  have hf : ((C.sc t).f).hom = ((C.XIsoOfEq hprev).hom ≫ C.d (t+1) t).hom := by
    rw [show ((C.sc t).f) = C.d ((ComplexShape.down ℕ).prev t) t from rfl, ← h]
  rw [hf, ModuleCat.hom_comp]
  simp only [dC]
  rw [LinearMap.range_comp]
  have htop : LinearMap.range ((C.XIsoOfEq hprev).hom).hom = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    refine ⟨(C.XIsoOfEq hprev).inv.hom y, ?_⟩
    have h2 := congrArg (fun (g : C.X (t+1) ⟶ C.X (t+1)) => g.hom y)
      (Iso.inv_hom_id (C.XIsoOfEq hprev))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] using h2
  rw [htop, Submodule.map_top]

/-! ## The concrete class map on the cycles of `C` -/

/-- `B_t = ∂(C_{t+1}) ∩ Z_t(C)` with the cycles of `C` computed as the kernel of `dC C t (t-1)`. -/
lemma mem_range_moduleCatToCycles (C : ChainComplex (ModuleCat ℤ) ℕ) (t : ℕ)
    (y : ↥(LinearMap.ker ((C.sc t).g.hom))) :
    y ∈ LinearMap.range ((C.sc t).moduleCatToCycles) ↔
      y.val ∈ LinearMap.range ((C.sc t).f.hom) := by
  rw [show ((C.sc t).moduleCatToCycles) =
      ((C.sc t).f.hom).codRestrict (LinearMap.ker ((C.sc t).g.hom)) _ from rfl]
  rw [LinearMap.range_codRestrict]
  simp only [Submodule.mem_comap, Submodule.subtype_apply]

/-- The underlying chain of the image of a cycle under the concrete cycles isomorphism. -/
lemma cyclesIso_hom_val (C : ChainComplex (ModuleCat ℤ) ℕ) (t : ℕ) (w : C.cycles t) :
    (((C.sc t).moduleCatCyclesIso.hom) w).val = (C.iCycles t).hom w := by
  have h := ShortComplex.moduleCatCyclesIso_hom_i (C.sc t)
  have hh := congrArg (fun (g : (C.sc t).cycles ⟶ (C.sc t).X₂) => (ModuleCat.Hom.hom g) w) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ShortComplex.moduleCatLeftHomologyData_i_hom] at hh
  rw [show ((C.sc t).iCycles) = C.iCycles t from rfl] at hh
  exact hh

lemma cyclesIso_hom_eq (C : ChainComplex (ModuleCat ℤ) ℕ) (t : ℕ) (w : C.cycles t)
    (h : (C.iCycles t).hom w ∈ LinearMap.ker ((C.sc t).g.hom)) :
    (C.sc t).moduleCatCyclesIso.hom w = ⟨(C.iCycles t).hom w, h⟩ :=
  Subtype.ext (cyclesIso_hom_val C t w)

/-- The class map on cycles, expressed via the concrete quotient model of `H_t(C)`. -/
lemma homologyπ_apply_repr (C : ChainComplex (ModuleCat ℤ) ℕ) (t : ℕ) (w : C.cycles t) :
    (C.homologyπ t).hom w
      = ((C.sc t).moduleCatHomologyIso.inv)
          (Submodule.mkQ (LinearMap.range (C.sc t).moduleCatToCycles)
            ((C.sc t).moduleCatCyclesIso.hom w)) := by
  have h := ShortComplex.π_moduleCatCyclesIso_hom (C.sc t)
  have hh := congrArg
    (fun (g : (C.sc t).cycles ⟶ (C.sc t).moduleCatLeftHomologyData.H) =>
      (ModuleCat.Hom.hom g) w) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ShortComplex.moduleCatLeftHomologyData_π_hom] at hh
  have key : ((C.sc t).moduleCatHomologyIso.inv)
        (((C.sc t).moduleCatHomologyIso.hom) (((C.sc t).homologyπ).hom w))
      = ((C.sc t).homologyπ).hom w := by
    have h2 := congrArg (fun (g : (C.sc t).homology ⟶ (C.sc t).homology) =>
      (ModuleCat.Hom.hom g) (((C.sc t).homologyπ).hom w))
      (Iso.hom_inv_id (C.sc t).moduleCatHomologyIso)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] using h2
  have hC : (C.homologyπ t).hom w = ((C.sc t).homologyπ).hom w := rfl
  exact hC.trans (key.symm.trans (congrArg ((C.sc t).moduleCatHomologyIso.inv) hh))

/-- The class map `Z_t(C) → H_t(C)` in the concrete model. -/
def cl (C : ChainComplex (ModuleCat ℤ) ℕ) (t : ℕ) :
    ↥(LinearMap.ker ((C.sc t).g.hom)) →ₗ[ℤ] C.homology t :=
  ((C.sc t).moduleCatHomologyIso.inv.hom).comp
    (Submodule.mkQ (LinearMap.range (C.sc t).moduleCatToCycles))

lemma cl_apply (C : ChainComplex (ModuleCat ℤ) ℕ) (t : ℕ)
    (y : ↥(LinearMap.ker ((C.sc t).g.hom))) :
    cl C t y = ((C.sc t).moduleCatHomologyIso.inv.hom)
        (Submodule.mkQ (LinearMap.range (C.sc t).moduleCatToCycles) y) := rfl

lemma cl_eq_zero_iff (C : ChainComplex (ModuleCat ℤ) ℕ) (t : ℕ)
    (y : ↥(LinearMap.ker ((C.sc t).g.hom))) :
    cl C t y = 0 ↔ y ∈ LinearMap.range ((C.sc t).moduleCatToCycles) := by
  rw [cl_apply]
  have hinj := (ModuleCat.mono_iff_injective
    ((C.sc t).moduleCatHomologyIso.inv)).mp inferInstance
  constructor
  · intro h
    have h1 : Submodule.mkQ (LinearMap.range (C.sc t).moduleCatToCycles) y = 0 :=
      hinj (by rw [h, map_zero])
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
  · intro hy
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hy, map_zero]

/-- The class map applied to a cycle of `C`. -/
lemma homologyπ_apply_cl (C : ChainComplex (ModuleCat ℤ) ℕ) (t : ℕ) (w : C.cycles t)
    (h : (C.iCycles t).hom w ∈ LinearMap.ker ((C.sc t).g.hom)) :
    (C.homologyπ t).hom w = cl C t ⟨(C.iCycles t).hom w, h⟩ := by
  rw [homologyπ_apply_repr, cyclesIso_hom_eq C t w h]
  rfl

/-! ## The map `Z_t(F_0) → H_t(C)` -/

/-- The linear map `Z_t(F_0) → H_t(C)` sending a cycle of the bottom filtration term to its
homology class. -/
def psi (C : ChainComplex (ModuleCat ℤ) ℕ) (ξ : Filtration C) (t : ℕ) :
    ↥(Zof ξ t) →ₗ[ℤ] C.homology t :=
  (cl C t).comp (Submodule.inclusion (Zof_le_ker_g ξ t))

lemma psi_apply (C : ChainComplex (ModuleCat ℤ) ℕ) (ξ : Filtration C) (t : ℕ)
    (x : ↥(Zof ξ t)) :
    psi C ξ t x = cl C t ⟨x.val, Zof_le_ker_g ξ t x.property⟩ := rfl

variable (ξ : Filtration C)

/-- The image in `C.X t` of a cycle of `F_0` is a cycle of `C` lying in `F_0`. -/
lemma Cincl_iCycles_mem_Zof (t : ℕ) (w : (ξ.F.obj 0).cycles t) :
    Cincl ξ 0 t (((ξ.F.obj 0).iCycles t) w) ∈ Zof ξ t := by
  rw [mem_Zof_iff]
  constructor
  · show ((C.d t (t-1)).hom) (((ξ.incl 0).f t).hom (((ξ.F.obj 0).iCycles t) w)) = 0
    rw [chainMap_comm_apply' (ξ.F.obj 0) C (ξ.incl 0) t (t-1) (((ξ.F.obj 0).iCycles t) w)]
    rw [iCycles_d_apply (ξ.F.obj 0) t (t-1) w, map_zero]
  · rw [Fch]
    exact LinearMap.mem_range.mpr ⟨_, rfl⟩

/-- The underlying chain of the image of a cycle of `F_0` under `cyclesMap (ξ.incl 0) t`. -/
lemma iCycles_cyclesMap_eq (t : ℕ) (w : (ξ.F.obj 0).cycles t) :
    (C.iCycles t).hom ((HomologicalComplex.cyclesMap (ξ.incl 0) t).hom w)
      = Cincl ξ 0 t (((ξ.F.obj 0).iCycles t).hom w) := by
  rw [cyclesMap_i_apply]
  rfl

/-- **The composite `Z_t(F_0) → H_t(F_0) → H_t(C)`.**  On the class of a cycle `w` of `F_0`, the
map induced by `ξ.incl 0` on homology is the class in `H_t(C)` of the image cycle. -/
lemma homologyMap_apply_eq_psi (t : ℕ) (w : (ξ.F.obj 0).cycles t) :
    (HomologicalComplex.homologyMap (ξ.incl 0) t).hom (((ξ.F.obj 0).homologyπ t).hom w)
      = psi C ξ t ⟨Cincl ξ 0 t (((ξ.F.obj 0).iCycles t) w),
          Cincl_iCycles_mem_Zof ξ t w⟩ := by
  rw [homologyMap_homologyπ_apply]
  have hker : (C.iCycles t).hom ((HomologicalComplex.cyclesMap (ξ.incl 0) t).hom w)
      ∈ LinearMap.ker ((C.sc t).g.hom) := by
    rw [cyclesMap_i_apply]
    exact Zof_le_ker_g ξ t (Cincl_iCycles_mem_Zof ξ t w)
  rw [homologyπ_apply_cl C t ((HomologicalComplex.cyclesMap (ξ.incl 0) t).hom w) hker,
    psi_apply]
  exact congrArg (cl C t) (Subtype.ext (iCycles_cyclesMap_eq ξ t w))

/-- Every `z ∈ Z_t(F_0)` (as defined inside `C`) is the image of a genuine cycle of `F_0`. -/
lemma exists_cycle (t : ℕ) (z : ↥(Zof ξ t)) :
    ∃ w : (ξ.F.obj 0).cycles t, Cincl ξ 0 t (((ξ.F.obj 0).iCycles t) w) = z.val := by
  have hz := (mem_Zof_iff ξ t z.val).mp z.property
  obtain ⟨u, hu⟩ : ∃ u : (ξ.F.obj 0).X t, Cincl ξ 0 t u = z.val := by
    rw [Fch] at hz
    exact LinearMap.mem_range.mp hz.2
  have hzc : ((C.d t (t-1)).hom) z.val = 0 := hz.1
  have huc : ((ξ.F.obj 0).sc t).g.hom u = 0 := by
    refine (mem_ker_g_iff (ξ.F.obj 0) t u).mpr ?_
    have hinj : Function.Injective (((ξ.incl 0).f (t-1)).hom) := by
      haveI := ξ.mono_incl 0
      exact (ModuleCat.mono_iff_injective _).mp inferInstance
    have hcomm := chainMap_comm_apply' (ξ.F.obj 0) C (ξ.incl 0) t (t-1) u
    have hu' : ((ξ.incl 0).f t).hom u = z.val := hu
    have hthis : ((ξ.incl 0).f (t-1)).hom (((ξ.F.obj 0).d t (t-1)).hom u) = 0 := by
      rw [← hcomm, hu', hzc]
    show ((ξ.F.obj 0).d t (t-1)).hom u = 0
    exact hinj (by rw [hthis, map_zero])
  refine ⟨HomologicalComplex.cyclesMk (ξ.F.obj 0) u ((ComplexShape.down ℕ).next t) rfl huc, ?_⟩
  have hw := HomologicalComplex.i_cyclesMk (ξ.F.obj 0) u ((ComplexShape.down ℕ).next t) rfl huc
  rw [show ((ξ.F.obj 0).iCycles t).hom
      (HomologicalComplex.cyclesMk (ξ.F.obj 0) u ((ComplexShape.down ℕ).next t) rfl huc) = u by
    simpa using hw, hu]

/-- **Kernel of the class map.**  A cycle of `F_0` maps to `0` in `H_t(C)` exactly when it is a
boundary of `C`, i.e. lies in `V_{t+1}`. -/
lemma psi_ker (t : ℕ) : (psi C ξ t).ker = VZ ξ t (t+1) := by
  have hVZ : ∀ z : ↥(Zof ξ t), (z ∈ VZ ξ t (t+1) ↔
      z.val ∈ LinearMap.range (dC C (t+1) t)) := by
    intro z
    rw [VZ, Submodule.mem_comap, Submodule.subtype_apply, V]
    constructor
    · intro h
      have h2 : z.val ∈ Submodule.map (dC C (t+1) t) (Fch ξ (t+1) (t+1)) :=
        (Submodule.mem_inf.mp h).1
      rwa [Fch_top, Submodule.map_top] at h2
    · intro h
      refine Submodule.mem_inf.mpr ⟨?_, z.property⟩
      rwa [Fch_top, Submodule.map_top]
  ext z
  rw [LinearMap.mem_ker, psi_apply, cl_eq_zero_iff, mem_range_moduleCatToCycles, range_f_sc]
  exact (hVZ z).symm

/-- **Range of the class map.**  The image of `Z_t(F_0)` in `H_t(C)` is the image filtration term
`Φ_t(0) = im(H_t(F_0) → H_t(C))`. -/
lemma psi_range (t : ℕ) : (psi C ξ t).range = Phi ξ t 0 := by
  have hPhi : Phi ξ t (0 : ℤ) = (HomologicalComplex.homologyMap (ξ.incl 0) t).hom.range := by
    rw [Phi]
    simp only [if_neg (by norm_num : ¬ ((0:ℤ) < 0)), Int.toNat_zero]
  rw [hPhi]
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := exists_cycle ξ t z
    refine ⟨((ξ.F.obj 0).homologyπ t).hom w, ?_⟩
    rw [homologyMap_apply_eq_psi]
    congr 1
    exact Subtype.ext hw
  · rintro x ⟨v, rfl⟩
    have hsurj : Function.Surjective (((ξ.F.obj 0).homologyπ t).hom) :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
    obtain ⟨w, hw⟩ := hsurj v
    refine ⟨⟨Cincl ξ 0 t (((ξ.F.obj 0).iCycles t) w), Cincl_iCycles_mem_Zof ξ t w⟩, ?_⟩
    rw [← hw, homologyMap_apply_eq_psi]

/-- **The left column converges to `Φ_t(0)`.**  `Z_t(F_0)/V_{t+1}` is isomorphic to the bottom piece
`Φ_t(0) = im(H_t(F_0) → H_t(C))` of the image filtration of the homology of `C`.

Roadmap.  Let `φ : ↥(Zof ξ t) →ₗ[ℤ] C.homology t` be the composite of the inclusion
`Zof ξ t ⊆ C.X t` (this submodule consists of the `t`-cycles of `C` that lie in `F_0`) with the
class map `C.cycles t → C.homology t` (Mathlib: `HomologicalComplex.homologyπ`).  Then
* `LinearMap.range φ = Phi ξ t 0 = (homologyMap (ξ.incl 0) t).hom.range`: a class in the range is
  the class of a cycle of `F_0`, and conversely `homologyMap (ξ.incl 0) t` is the map induced by
  `ξ.incl 0` on the cycles;
* `LinearMap.ker φ = VZ ξ t (t + 1) = V_{t+1} = ∂(F_{t+1}X_{t+1}) ∩ Z_t(F_0)`: a cycle of `F_0`
  becomes zero in `H_t(C)` exactly when it is the boundary of a `(t+1)`-chain of `C`, and by
  saturation (`ξ.sat (t+1)`) every `(t+1)`-chain of `C` lies in `F_{t+1}`.
Conclude with the first isomorphism theorem (`LinearMap.quotKerEquivRange`). -/
theorem Phi_iso {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C) (t : ℕ) :
    Nonempty ((↥(Zof ξ t) ⧸ VZ ξ t (t + 1)) ≃ₗ[ℤ] (↥(Phi ξ t 0))) := by
  refine ⟨?_⟩
  exact (Submodule.quotEquivOfEq _ _ (psi_ker ξ t).symm).trans
    ((LinearMap.quotKerEquivRange (psi C ξ t)).trans (LinearEquiv.ofEq _ _ (psi_range ξ t)))

end

end Work.SSS.PhiTop
