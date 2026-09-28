import Mathlib
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.uctDefs

/-!
# The dual universal coefficient theorem

For a chain complex `E` of `ℤ`-modules (indexed by `ℕ`) whose terms are projective and whose
homology modules are projective, the cohomology of the dual complex `Hom_ℤ(E, ℤ)` is the `ℤ`-dual
of the homology: `Hⁿ(Hom(E, ℤ)) ≅ Hom(Hₙ(E), ℤ)`.

This is the universal coefficient theorem in the (split) case where the `Ext`-term vanishes.  The
proof is the classical one: the comparison map

`Ψₙ : ker(dⁿ) ⟶ Hom(Zₙ ⧸ Bₙ, ℤ),  f ↦ (z ↦ f(z))`

has kernel the image of the transposed differential `dⁿ⁻¹` and is surjective, because `Eₙ`
retracts onto its cycles (as `B_{n-1}` is projective) and every functional on `B_n` extends to
`Eₙ`.  Those splitting statements are proved by induction on `n` from the projectivity of `Eₙ` and
of `Hₙ`.
-/

set_option backward.isDefEq.respectTransparency false

attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

open CategoryTheory CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

universe u

variable (E : ChainComplex (ModuleCat.{u, 0} ℤ) ℕ)

/-! ## The comparison map `Ψ` -/

lemma uctD_kill (n : ℕ) (f : ↥(LinearMap.ker ((dualComplex ℤ E).d n (n + 1)).hom)) :
    uctH E n ≤ LinearMap.ker ((dval E n f.1).comp (uctZ E n).subtype) := by
  intro x hx
  rw [LinearMap.mem_ker, LinearMap.comp_apply]
  change (dval E n f.1) ↑x = 0
  have hx' : (↑x : ↥(E.X n)) ∈ uctB E n := (mem_uctH E n x).1 hx
  obtain ⟨y, hy⟩ := hx'
  have h2 : (dval E n f.1) ((E.d (n + 1) n).hom y) = 0 := by
    have hf : ((dualComplex ℤ E).d n (n + 1)).hom f.1 = 0 := LinearMap.mem_ker.mp f.2
    rw [uct_d_apply] at hf
    exact LinearMap.congr_fun hf y
  rw [show (↑x : ↥(E.X n)) = (E.d (n + 1) n).hom y from hy.symm]
  exact h2

/-- The comparison map from the `n`-cocycles of the dual complex to the `ℤ`-dual of the
`n`-th homology of `E`. -/
def uctPsi (n : ℕ) :
    (↥(LinearMap.ker ((dualComplex ℤ E).d n (n + 1)).hom)) →ₗ[ℤ]
      ((↥(uctZ E n) ⧸ uctH E n) →ₗ[ℤ] ℤ) where
  toFun f := (uctH E n).liftQ ((dval E n f.1).comp (uctZ E n).subtype) (uctD_kill E n f)
  map_add' f g := by
    apply LinearMap.ext
    intro w
    obtain ⟨x, rfl⟩ := (uctH E n).mkQ_surjective w
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply, dval,
      Submodule.coe_add, Submodule.subtype_apply]
    rfl
  map_smul' a f := by
    apply LinearMap.ext
    intro w
    obtain ⟨x, rfl⟩ := (uctH E n).mkQ_surjective w
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply, dval,
      Submodule.coe_smul, Submodule.subtype_apply, RingHom.id_apply]
    rfl

lemma uctPsi_apply (n : ℕ) (f : ↥(LinearMap.ker ((dualComplex ℤ E).d n (n + 1)).hom))
    (x : ↥(uctZ E n)) :
    uctPsi E n f ((uctH E n).mkQ x) = (dval E n f.1) x := by
  show (uctH E n).liftQ ((dval E n f.1).comp (uctZ E n).subtype) _ ((uctH E n).mkQ x)
    = (dval E n f.1) x
  rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply]
  rfl

/-- `Ψ` is surjective: every functional on the homology extends to the cocycles. -/
theorem uctPsi_surj (n : ℕ)
    (hZ : ∃ ρ : ↥(E.X n) →ₗ[ℤ] ↥(uctZ E n), ρ ∘ₗ (uctZ E n).subtype = LinearMap.id) :
    Function.Surjective (uctPsi E n) := by
  obtain ⟨ρ, hρ⟩ := hZ
  intro g
  let f0 : ↥((dualComplex ℤ E).X n) := g.comp ((uctH E n).mkQ.comp ρ)
  have hf0 : ((dualComplex ℤ E).d n (n + 1)).hom f0 = 0 := by
    rw [uct_d_apply]
    apply LinearMap.ext
    intro y
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    show g ((uctH E n).mkQ (ρ ((E.d (n + 1) n).hom y))) = 0
    have hy : ((E.d (n + 1) n).hom y : ↥(E.X n)) ∈ uctB E n := ⟨y, rfl⟩
    have hz : ρ ((E.d (n + 1) n).hom y) = ⟨(E.d (n + 1) n).hom y, uctB_le_uctZ E n hy⟩ := by
      have h := congrArg (fun (φ : ↥(uctZ E n) →ₗ[ℤ] ↥(uctZ E n)) =>
        φ ⟨(E.d (n + 1) n).hom y, uctB_le_uctZ E n hy⟩) hρ
      simpa using h
    have hmem : (⟨(E.d (n + 1) n).hom y, uctB_le_uctZ E n hy⟩ : ↥(uctZ E n)) ∈ uctH E n :=
      (mem_uctH E n _).mpr hy
    rw [hz, show (uctH E n).mkQ ⟨(E.d (n + 1) n).hom y, uctB_le_uctZ E n hy⟩ = 0 from by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact hmem, map_zero]
  refine ⟨⟨f0, hf0⟩, ?_⟩
  apply LinearMap.ext
  intro w
  obtain ⟨z, rfl⟩ := (uctH E n).mkQ_surjective w
  rw [uctPsi_apply]
  have hz : ρ (z : ↥(E.X n)) = z := by
    have h := congrArg (fun (φ : ↥(uctZ E n) →ₗ[ℤ] ↥(uctZ E n)) => φ z) hρ
    simpa using h
  rw [show (dval E n f0) = g.comp ((uctH E n).mkQ.comp ρ) from rfl]
  simp only [LinearMap.comp_apply, hz]

/-- The kernel of the comparison map `Ψ` is the image of the transposed differential.  This is
where the extension of functionals from `B_{n-1}` to `E_{n-1}` is used. -/
theorem uctPsi_ker (n : ℕ)
    (hR : ∃ r : ↥(E.X (n - 1)) →ₗ[ℤ] ↥(uctR E n), r ∘ₗ (uctR E n).subtype = LinearMap.id) :
    LinearMap.ker (uctPsi E n) = uctPre E n := by
  obtain ⟨r, hr⟩ := hR
  apply le_antisymm
  · intro f hf
    rw [LinearMap.mem_ker] at hf
    have hkill : (dval E n f.1).comp (uctZ E n).subtype = 0 :=
      liftQ_eq_zero_imp (uctH E n) _ (uctD_kill E n f) hf
    have hkill' : ∀ x : ↥(E.X n), x ∈ uctZ E n → (dval E n f.1) x = 0 := by
      intro x hx
      have h := LinearMap.congr_fun hkill ⟨x, hx⟩
      simpa [LinearMap.comp_apply] using h
    let fbar : (↥(E.X n) ⧸ uctZ E n) →ₗ[ℤ] ℤ :=
      (uctZ E n).liftQ (dval E n f.1) (fun x hx => hkill' x hx)
    let e := (E.d n (n - 1)).hom.quotKerEquivRange
    let y : ↥((dualComplex ℤ E).X (n - 1)) :=
      (show ↥(E.X (n - 1)) →ₗ[ℤ] ℤ from (fbar.comp e.symm.toLinearMap).comp r)
    refine ⟨y, ?_⟩
    apply Subtype.ext
    show ((dualComplex ℤ E).d (n - 1) n).hom y = f.1
    rw [uct_d_pred_apply]
    apply LinearMap.ext
    intro x
    show fbar (e.symm (r ((E.d n (n - 1)).hom x))) = (dval E n f.1) x
    rw [show r ((E.d n (n - 1)).hom x) = ⟨(E.d n (n - 1)).hom x, ⟨x, rfl⟩⟩ from by
      have h := congrArg (fun (φ : ↥(uctR E n) →ₗ[ℤ] ↥(uctR E n)) =>
        φ ⟨(E.d n (n - 1)).hom x, ⟨x, rfl⟩⟩) hr
      simpa using h]
    show fbar (e.symm ⟨(E.d n (n - 1)).hom x, ⟨x, rfl⟩⟩) = (dval E n f.1) x
    rw [show e.symm ⟨(E.d n (n - 1)).hom x, ⟨x, rfl⟩⟩ = (uctZ E n).mkQ x from
      LinearMap.quotKerEquivRange_symm_apply_image _ x ⟨x, rfl⟩]
    show fbar ((uctZ E n).mkQ x) = (dval E n f.1) x
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
  · intro f hf
    rw [LinearMap.mem_ker]
    obtain ⟨y, hy⟩ := hf
    have hval : ((dualComplex ℤ E).d (n - 1) n).hom y = f.1 := by
      have h := congrArg Subtype.val hy
      simpa [LinearMap.codRestrict_apply] using h
    apply LinearMap.ext
    intro w
    obtain ⟨x, rfl⟩ := (uctH E n).mkQ_surjective w
    rw [uctPsi_apply, LinearMap.zero_apply, ← hval]
    show (dval E n (((dualComplex ℤ E).d (n - 1) n).hom y)) ↑x = 0
    rw [uct_d_pred_apply]
    show (dval E (n - 1) y) ((E.d n (n - 1)).hom (x : ↥(E.X n))) = 0
    rw [show (E.d n (n - 1)).hom (x : ↥(E.X n)) = 0 from LinearMap.mem_ker.mp x.2, map_zero]

/-- **The middle isomorphism**: the `n`-th cohomology of the dual complex is computed from the
cycles and boundaries. -/
noncomputable def uctMiddle (n : ℕ)
    (hZ : ∃ ρ : ↥(E.X n) →ₗ[ℤ] ↥(uctZ E n), ρ ∘ₗ (uctZ E n).subtype = LinearMap.id)
    (hR : ∃ r : ↥(E.X (n - 1)) →ₗ[ℤ] ↥(uctR E n), r ∘ₗ (uctR E n).subtype = LinearMap.id) :
    (↥(LinearMap.ker ((dualComplex ℤ E).d n (n + 1)).hom) ⧸ uctPre E n) ≃ₗ[ℤ]
      ((↥(uctZ E n) ⧸ uctH E n) →ₗ[ℤ] ℤ) :=
  (Submodule.quotEquivOfEq (uctPre E n) (LinearMap.ker (uctPsi E n))
      (uctPsi_ker E n hR).symm).trans
    (LinearMap.quotKerEquivOfSurjective (uctPsi E n) (uctPsi_surj E n hZ))

/-! ## The splitting hypotheses -/

/-- If `im dₙ` is projective then `Eₙ` retracts onto its cycles. -/
theorem exists_retraction_cycles (n : ℕ) (h : Module.Projective ℤ ↥(uctR E n)) :
    ∃ ρ : ↥(E.X n) →ₗ[ℤ] ↥(uctZ E n), ρ ∘ₗ (uctZ E n).subtype = LinearMap.id := by
  rcases n with _ | m
  · rw [uctZ_zero]
    refine ⟨(Submodule.topEquiv (R := ℤ) (M := ↥(E.X 0))).symm.toLinearMap, ?_⟩
    apply LinearMap.ext
    intro x
    exact Subtype.ext rfl
  · exact exists_retraction_ker (E.d (m + 1) m).hom h

/-- If `Hₙ = Zₙ ⧸ Bₙ` is projective then `Zₙ` retracts onto `Bₙ`. -/
theorem exists_retraction_cycle_bounds (n : ℕ)
    (h : Module.Projective ℤ (↥(uctZ E n) ⧸ uctH E n)) :
    ∃ r : ↥(uctZ E n) →ₗ[ℤ] ↥(uctB E n),
      ∀ x : ↥(uctB E n), r ⟨(x : ↥(E.X n)), uctB_le_uctZ E n x.2⟩ = x := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (uctH E n).mkQ
    (LinearMap.id : (↥(uctZ E n) ⧸ uctH E n) →ₗ[ℤ] (↥(uctZ E n) ⧸ uctH E n))
    (uctH E n).mkQ_surjective
  have hmem : ∀ x : ↥(uctZ E n),
      ((LinearMap.id : ↥(uctZ E n) →ₗ[ℤ] ↥(uctZ E n)) -
        s.comp (uctH E n).mkQ) x ∈ uctH E n := by
    intro x
    have h2 : (uctH E n).mkQ (s ((uctH E n).mkQ x)) = (uctH E n).mkQ x := by
      rw [← LinearMap.comp_apply, LinearMap.congr_fun hs ((uctH E n).mkQ x),
        LinearMap.id_apply]
    have h3 : (uctH E n).mkQ (((LinearMap.id : ↥(uctZ E n) →ₗ[ℤ] ↥(uctZ E n)) -
        s.comp (uctH E n).mkQ) x) = 0 := by
      rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h2, sub_self]
    rwa [← LinearMap.mem_ker, Submodule.ker_mkQ] at h3
  have hmemB : ∀ x : ↥(uctZ E n),
      ((uctZ E n).subtype.comp ((LinearMap.id : ↥(uctZ E n) →ₗ[ℤ] ↥(uctZ E n)) -
        s.comp (uctH E n).mkQ)) x ∈ uctB E n := by
    intro x
    exact (mem_uctH E n (((LinearMap.id : ↥(uctZ E n) →ₗ[ℤ] ↥(uctZ E n)) -
      s.comp (uctH E n).mkQ) x)).mp (hmem x)
  refine ⟨LinearMap.codRestrict (uctB E n)
      ((uctZ E n).subtype.comp ((LinearMap.id : ↥(uctZ E n) →ₗ[ℤ] ↥(uctZ E n)) -
        s.comp (uctH E n).mkQ)) hmemB, ?_⟩
  intro x
  apply Subtype.ext
  change (((LinearMap.id : ↥(uctZ E n) →ₗ[ℤ] ↥(uctZ E n)) - s.comp (uctH E n).mkQ)
    ⟨(x : ↥(E.X n)), uctB_le_uctZ E n x.2⟩ : ↥(E.X n)) = (x : ↥(E.X n))
  rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
  have hx : (uctH E n).mkQ ⟨(x : ↥(E.X n)), uctB_le_uctZ E n x.2⟩ = 0 := by
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    exact (mem_uctH E n _).mpr x.2
  rw [hx, map_zero, sub_zero]

/-- The retraction of `Eₙ` onto its boundaries. -/
theorem exists_retraction_bounds (n : ℕ)
    (hZ : Module.Projective ℤ ↥(uctR E n))
    (hH : Module.Projective ℤ (↥(uctZ E n) ⧸ uctH E n)) :
    ∃ r : ↥(E.X n) →ₗ[ℤ] ↥(uctB E n), r ∘ₗ (uctB E n).subtype = LinearMap.id := by
  obtain ⟨ρ, hρ⟩ := exists_retraction_cycles E n hZ
  obtain ⟨r', hr'⟩ := exists_retraction_cycle_bounds E n hH
  refine ⟨r'.comp ρ, ?_⟩
  ext x
  have h1 : ρ ((uctB E n).subtype x) = ⟨(x : ↥(E.X n)), uctB_le_uctZ E n x.2⟩ := by
    have h := congrArg (fun (φ : ↥(uctZ E n) →ₗ[ℤ] ↥(uctZ E n)) =>
      φ ⟨(x : ↥(E.X n)), uctB_le_uctZ E n x.2⟩) hρ
    simpa using h
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h1, hr' x, LinearMap.id_apply]

/-- Every functional on `im dₙ` extends to `E_{n-1}`. -/
theorem exists_retraction_R (n : ℕ)
    (hB : ∀ m, ∃ r : ↥(E.X m) →ₗ[ℤ] ↥(uctB E m), r ∘ₗ (uctB E m).subtype = LinearMap.id) :
    ∃ r : ↥(E.X (n - 1)) →ₗ[ℤ] ↥(uctR E n), r ∘ₗ (uctR E n).subtype = LinearMap.id := by
  rcases n with _ | m
  · rw [uctR_zero]
    exact exists_retraction_bot
  · exact hB m

/-- `im dₙ` is projective if the boundaries are. -/
theorem uctR_projective (hB : ∀ n, Module.Projective ℤ ↥(uctB E n)) (n : ℕ) :
    Module.Projective ℤ ↥(uctR E n) := by
  rcases n with _ | m
  · rw [uctR_zero]
    exact projective_bot
  · exact hB m

/-- **The boundaries of `E` are projective**, by induction. -/
theorem uctB_projective (hproj : ∀ n, Module.Projective ℤ ↥(E.X n))
    (hH : ∀ n, Module.Projective ℤ (↥(uctZ E n) ⧸ uctH E n)) :
    ∀ n, Module.Projective ℤ ↥(uctB E n) := by
  have key : ∀ n, (∃ ρ : ↥(E.X n) →ₗ[ℤ] ↥(uctZ E n),
      ρ ∘ₗ (uctZ E n).subtype = LinearMap.id) →
      Module.Projective ℤ ↥(uctB E n) := by
    intro n hZ
    obtain ⟨ρ, hρ⟩ := hZ
    obtain ⟨r, hr⟩ := exists_retraction_cycle_bounds E n (hH n)
    have hsplit : ∃ r'' : ↥(E.X n) →ₗ[ℤ] ↥(uctB E n),
        r'' ∘ₗ (uctB E n).subtype = LinearMap.id := by
      refine ⟨r.comp ρ, ?_⟩
      ext x
      have h1 : ρ ((uctB E n).subtype x) = ⟨(x : ↥(E.X n)), uctB_le_uctZ E n x.2⟩ := by
        have h := congrArg (fun (φ : ↥(uctZ E n) →ₗ[ℤ] ↥(uctZ E n)) =>
          φ ⟨(x : ↥(E.X n)), uctB_le_uctZ E n x.2⟩) hρ
        simpa using h
      rw [LinearMap.comp_apply, LinearMap.comp_apply, h1, hr x, LinearMap.id_apply]
    obtain ⟨r'', hr''⟩ := hsplit
    exact Module.Projective.of_split (uctB E n).subtype r'' hr''
  intro n
  induction n with
  | zero =>
    refine key 0 ?_
    rw [uctZ_zero]
    refine ⟨(Submodule.topEquiv (R := ℤ) (M := ↥(E.X 0))).symm.toLinearMap, ?_⟩
    apply LinearMap.ext
    intro x
    exact Subtype.ext rfl
  | succ m ih => exact key (m + 1) (exists_retraction_cycles E (m + 1) ih)

/-! ## The dual universal coefficient theorem -/

/-- **Dual universal coefficients**: for a `ℕ`-indexed chain complex `E` of `ℤ`-modules whose
terms are projective and whose homology is projective, the cohomology of the dual complex
`Hom_ℤ(E, ℤ)` is the `ℤ`-dual of the homology. -/
theorem uctDual (E : ChainComplex (ModuleCat ℤ) ℕ)
    (hproj : ∀ n, Module.Projective ℤ ↥(E.X n))
    (hfree : ∀ n, Module.Free ℤ ↥(E.homology n)) (n : ℕ) :
    Nonempty ((dualComplex ℤ E).homology n ≅
      ModuleCat.of ℤ (↥(E.homology n) →ₗ[ℤ] ℤ)) := by
  have hH : ∀ k, Module.Projective ℤ (↥(uctZ E k) ⧸ uctH E k) := by
    intro k
    obtain ⟨e⟩ := homology_iso_H E k
    haveI : Module.Free ℤ ↥(E.homology k) := hfree k
    exact Module.Projective.of_equiv' (uctIsoToLinearEquiv e)
  have hB : ∀ k, Module.Projective ℤ ↥(uctB E k) := uctB_projective E hproj hH
  have hR : ∀ k, Module.Projective ℤ ↥(uctR E k) := fun k => uctR_projective E hB k
  obtain ⟨eD⟩ := homology_dual_iso E n
  obtain ⟨eE⟩ := homology_iso_H E n
  refine ⟨eD ≪≫ LinearEquiv.toModuleIso (uctMiddle E n ?_ ?_) ≪≫
    (LinearEquiv.dualMap (uctIsoToLinearEquiv eE)).toModuleIso⟩
  · exact exists_retraction_cycles E n (hR n)
  · exact exists_retraction_R E n (fun m => exists_retraction_bounds E m (hR m) (hH m))

end

end Work.Cohomology
