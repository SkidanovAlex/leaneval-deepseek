import Mathlib
import Submission.Work.ThomBordism.relHomAux
import Submission.Work.ThomBordism.extUpToNat
import Submission.Work.ThomBordism.extendsTorsionFree
import Submission.Work.ThomBordism.freeOfDualInt

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Torsion in the kernel of the evaluation map, and integral homology from cohomology

Continuing `Submission.Work.ThomBordism.relHomAux`:

* `eCoh_ker_torsion` — every element of the kernel of the evaluation map `eCoh` is torsion;
* `isAddTorsionFree_quot_of_pure` — a quotient by a pure submodule is torsion free;
* `isTorsionFree_quot_of_isZero` — vanishing of `Hⁿ⁺¹` of the dual complex makes `Zₙ ⧸ Bₙ`
  torsion free;
* `homology_int_of_dual_int` — **the main theorem**: if `Hⁿ(dualComplex ℤ E) ≅ ℤ`,
  `Hⁿ⁺¹(dualComplex ℤ E) = 0` and the homology of `E` is finitely generated in every degree, then
  `Hₙ(E) ≅ ℤ`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

open CategoryTheory CategoryTheory.Limits

namespace Work.ThomBordism

open Work.Cohomology

noncomputable section

/-! ## Instances on a fixed abelian group agree -/

theorem free_congr {M : Type*} [AddCommGroup M] {i₁ i₂ : Module ℤ M}
    (h : @Module.Free ℤ M _ _ i₁) : @Module.Free ℤ M _ _ i₂ :=
  Eq.mp (congrArg (fun i => @Module.Free ℤ M _ _ i) (Subsingleton.elim i₁ i₂)) h

theorem finite_congr {M : Type*} [AddCommGroup M] {i₁ i₂ : Module ℤ M}
    (h : @Module.Finite ℤ M _ _ i₁) : @Module.Finite ℤ M _ _ i₂ :=
  Eq.mp (congrArg (fun i => @Module.Finite ℤ M _ _ i) (Subsingleton.elim i₁ i₂)) h

theorem isTorsionFree_congr {M : Type*} [AddCommGroup M] {i₁ i₂ : Module ℤ M}
    (h : @Module.IsTorsionFree ℤ M _ _ i₁) : @Module.IsTorsionFree ℤ M _ _ i₂ :=
  Eq.mp (congrArg (fun i => @Module.IsTorsionFree ℤ M _ _ i) (Subsingleton.elim i₁ i₂)) h

/-- The boundaries inside the cycles versus inside the chains, in the default instance flavour. -/
def uctH_uctB_iso' (E : ChainComplex (ModuleCat ℤ) ℕ) (m : ℕ) :
    ↥(uctH E m) ≃ₗ[ℤ] ↥(uctB E m) where
  toFun x := ⟨((x.1 : ↥(uctZ E m)) : ↥(E.X m)), (mem_uctH E m x.1).mp x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ⟨⟨(y.1 : ↥(E.X m)), uctB_le_uctZ E m y.2⟩, (mem_uctH E m _).mpr y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## A local copy of the purity lemma, in this file's instance flavour -/

private theorem zsmul_finset_sum_local {α : Type*} [AddCommGroup α] {γ : Type*} (s : Finset γ)
    (n : ℤ) (f : γ → α) : n • (∑ i ∈ s, f i) = ∑ i ∈ s, n • f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, zsmul_add, ih]

/-- **Purity of a free submodule along which every functional extends** (statement of
`Work.ThomBordism.extendsTorsionFree`, re-elaborated in the instance flavour of this file). -/
theorem extendsTorsionFree_local {Z : Type*} [AddCommGroup Z] [Module ℤ Z]
    [Module.IsTorsionFree ℤ Z] (B : Submodule ℤ Z) (hB : Module.Free ℤ ↥B)
    (hext : ∀ φ : B →ₗ[ℤ] ℤ, ∃ ψ : Z →ₗ[ℤ] ℤ, ∀ b : B, ψ (b : Z) = φ b)
    (z : Z) (N : ℕ) (hN : 0 < N) (hz : (N : ℤ) • z ∈ B) : z ∈ B := by
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ ↥B
  let b : Module.Basis ι ℤ ↥B := Module.Free.chooseBasis ℤ ↥B
  let bz : ↥B := ⟨(N : ℤ) • z, hz⟩
  let ψ : ι → (Z →ₗ[ℤ] ℤ) := fun i => Classical.choose (hext (b.coord i))
  have hψ : ∀ (i : ι) (x : ↥B), ψ i (x : Z) = b.coord i x :=
    fun i => Classical.choose_spec (hext (b.coord i))
  have hexp : bz = ∑ i ∈ (b.repr bz).support, (b.repr bz i) • b i := by
    conv_lhs => rw [← b.linearCombination_repr bz]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    exact Finset.sum_congr rfl
      (fun i _ => int_smul_eq_zsmul (Submodule.module B) (b.repr bz i) (b i))
  have hexpZ : (bz : Z) = ∑ i ∈ (b.repr bz).support, (b.repr bz i) • (b i : Z) := by
    have h := congrArg (fun x : ↥B => (x : Z)) hexp
    simpa using h
  have hcoord : ∀ i : ι, b.repr bz i = (N : ℤ) * ψ i z := by
    intro i
    have h1 : b.repr bz i = ψ i (bz : Z) := by
      rw [← Module.Basis.coord_apply b i bz]
      exact (hψ i bz).symm
    rw [h1]
    have h2 : (bz : Z) = (N : ℤ) • z := rfl
    rw [h2, map_zsmul, zsmul_eq_mul]
    simp
  let W : Z := ∑ i ∈ (b.repr bz).support, (ψ i z) • (b i : Z)
  have hWdef : W = ∑ i ∈ (b.repr bz).support, (ψ i z) • (b i : Z) := rfl
  have hkey : (N : ℤ) • z = (N : ℤ) • W := by
    rw [show (N : ℤ) • z = (bz : Z) from rfl, hexpZ, hWdef, zsmul_finset_sum_local]
    apply Finset.sum_congr rfl
    intro i _
    rw [hcoord i, mul_zsmul]
  have hAddTors : IsAddTorsionFree Z := IsAddTorsionFree.of_isTorsionFree ℤ Z
  have hne : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hzW : z = W := zsmul_right_injective hne hkey
  rw [hzW, hWdef]
  exact B.toAddSubgroup.sum_mem (fun i _ => (B.toAddSubgroup).zsmul_mem (b i).2 (ψ i z))

/-! ## The kernel of the evaluation map is torsion -/

/-- **Every element of the kernel of the evaluation map is torsion.** -/
theorem eCoh_ker_torsion (E : ChainComplex (ModuleCat ℤ) ℕ)
    (hfree : ∀ k, Module.Free ℤ ↥(E.X k))
    (hfin : ∀ k, Module.Finite ℤ ↥(E.homology k)) (n : ℕ)
    (α : ↥((dualComplex ℤ E).homology n)) (hα : eCoh E n α = 0) :
    ∃ N : ℕ, 0 < N ∧ N • α = 0 := by
  -- a cocycle representative of `α`
  obtain ⟨f, hf⟩ : ∃ f : ↥(LinearMap.ker ((dualComplex ℤ E).d n (n + 1)).hom),
      (uctIsoToLinearEquiv (homologyDualIso E n)) α = (uctPre E n).mkQ f :=
    (Submodule.mkQ_surjective (uctPre E n)
      ((uctIsoToLinearEquiv (homologyDualIso E n)) α)).imp (fun f hf => hf.symm)
  have hα' : α = (uctIsoToLinearEquiv (homologyDualIso E n)).symm ((uctPre E n).mkQ f) := by
    rw [← hf, LinearEquiv.symm_apply_apply]
  have hpsi : uctPsi E n f = 0 := by
    rw [hα'] at hα
    rwa [eCoh_mkQ] at hα
  -- `f` vanishes on the cycles
  have hkills : ∀ x : ↥(uctZ E n), (dval E n (f : ↥((dualComplex ℤ E).X n))) x = 0 := by
    intro x
    have h : (uctPsi E n f) ((uctH E n).mkQ x) = 0 := by rw [hpsi]; simp
    rwa [uctPsi_apply] at h
  rcases n with _ | m
  · -- degree zero: the cycles are everything, so `f = 0`
    refine ⟨1, one_pos, ?_⟩
    have hf0 : (f : ↥((dualComplex ℤ E).X 0)) = 0 := by
      apply LinearMap.ext
      intro x
      have hx : x ∈ uctZ E 0 := by rw [uctZ_zero]; trivial
      have h := hkills ⟨x, hx⟩
      simpa only [dval, LinearMap.zero_apply] using h
    have hfz : f = 0 := Subtype.ext hf0
    rw [hα', hfz, map_zero, map_zero, one_smul]
  · -- positive degree
    -- the functional `f` restricted to the boundaries, as a functional on `Eₘ ⧸ Zₘ`
    have hkerZ : uctZ E (m + 1) ≤
        LinearMap.ker (dval E (m + 1) (f : ↥((dualComplex ℤ E).X (m + 1)))) := by
      intro x hx
      rw [LinearMap.mem_ker]
      exact hkills ⟨x, hx⟩
    let φ0 : (↥(E.X (m + 1)) ⧸ uctZ E (m + 1)) →ₗ[ℤ] ℤ :=
      (uctZ E (m + 1)).liftQ (dval E (m + 1) (f : ↥((dualComplex ℤ E).X (m + 1)))) hkerZ
    let hB : ↥(uctB E m) →ₗ[ℤ] ℤ :=
      φ0.comp ((E.d (m + 1) m).hom.quotKerEquivRange).symm.toLinearMap
    have hhB : ∀ x : ↥(E.X (m + 1)),
        hB ⟨((E.d (m + 1) m).hom) x, ⟨x, rfl⟩⟩ = (dval E (m + 1) f) x := by
      intro x
      show φ0 (((E.d (m + 1) m).hom.quotKerEquivRange).symm ⟨_, ⟨x, rfl⟩⟩) = _
      rw [LinearMap.quotKerEquivRange_symm_apply_image]
      exact Submodule.liftQ_apply _ _ (h := hkerZ) x
    let φB := hB.comp (uctH_uctB_iso' E m).toLinearMap
    -- `Zₘ ⧸ Bₘ` is finitely generated
    have hfgS : Module.Finite ℤ (↥(uctZ E m) ⧸ uctH E m) := by
      haveI : Module.Finite ℤ ↥(E.homology m) := hfin m
      obtain ⟨iso⟩ := homology_iso_H E m
      exact finite_congr (Module.Finite.equiv (uctIsoToLinearEquiv iso))
    -- extend `φB` up to a positive multiple to the cycles
    obtain ⟨N, hNpos, ψ, hψ⟩ :=
      @extUpToNat ↥(uctZ E m) _ (Submodule.module (uctZ E m)) (uctH E m)
        (finite_congr hfgS) φB
    -- extend `ψ` to the chains
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥(E.X m) →ₗ[ℤ] ↥(uctZ E m),
        ρ.comp (uctZ E m).subtype = LinearMap.id := by
      convert exists_retract_cycles E hfree m using 1
      all_goals exact Subsingleton.elim _ _
    have hρid : ∀ y : ↥(uctZ E m), ρ y = y := by
      intro y
      have h := LinearMap.congr_fun hρ y
      simpa using h
    let g : ↥(E.X m) →ₗ[ℤ] ℤ := ψ.comp ρ
    -- the key identity `g ∘ ∂ = N • f`
    have hkey : ((dualComplex ℤ E).d m (m + 1)).hom g
        = N • (f : ↥((dualComplex ℤ E).X (m + 1))) := by
      rw [uct_d_apply]
      apply LinearMap.ext
      intro x
      rw [LinearMap.comp_apply, LinearMap.smul_apply]
      show (dval E m g) (((E.d (m + 1) m).hom) x) = N • (dval E (m + 1) f) x
      have hmemB : ((E.d (m + 1) m).hom) x ∈ uctB E m := ⟨x, rfl⟩
      have hmemZ : ((E.d (m + 1) m).hom) x ∈ uctZ E m := uctB_le_uctZ E m hmemB
      have hmemH : (⟨((E.d (m + 1) m).hom) x, hmemZ⟩ : ↥(uctZ E m)) ∈ uctH E m :=
        (mem_uctH E m _).mpr hmemB
      let bH : ↥(uctH E m) := ⟨⟨((E.d (m + 1) m).hom) x, hmemZ⟩, hmemH⟩
      have h1 : (dval E m g) (((E.d (m + 1) m).hom) x) = ψ (bH : ↥(uctZ E m)) := by
        show ψ (ρ (((E.d (m + 1) m).hom) x)) = ψ (bH : ↥(uctZ E m))
        rw [hρid ⟨((E.d (m + 1) m).hom) x, hmemZ⟩]
      have hz : ((uctH_uctB_iso' E m) bH : ↥(uctB E m)) =
          ⟨((E.d (m + 1) m).hom) x, ⟨x, rfl⟩⟩ := Subtype.ext rfl
      have h2 : (hB.comp (uctH_uctB_iso' E m).toLinearMap) bH = (dval E (m + 1) f) x :=
        (congrArg hB hz).trans (hhB x)
      have h3 : φB bH = (dval E (m + 1) f) x := h2
      have hA : (dval E m g) (((E.d (m + 1) m).hom) x) = N • φB bH := by
        rw [h1]
        exact hψ bH
      rw [hA, h3]
    -- `N • f` is a coboundary
    have hpre : N • f ∈ uctPre E (m + 1) := by
      refine ⟨g, ?_⟩
      apply Subtype.ext
      simpa using hkey
    refine ⟨N, hNpos, ?_⟩
    have hzero : (uctPre E (m + 1)).mkQ (N • f) = 0 := by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact hpre
    rw [hα', ← map_nsmul]
    rw [show N • ((uctPre E (m + 1)).mkQ f) = (uctPre E (m + 1)).mkQ (N • f) from
      (map_nsmul ((uctPre E (m + 1)).mkQ) N f).symm, hzero, map_zero]

/-! ## Purity makes the quotient torsion free -/

/-- **A quotient by a pure submodule is torsion free** (in the additive sense). -/
theorem isAddTorsionFree_quot_of_pure {Z : Type*} [AddCommGroup Z] [Module ℤ Z]
    (B : Submodule ℤ Z)
    (h : ∀ z : Z, ∀ N : ℕ, 0 < N → (N : ℤ) • z ∈ B → z ∈ B) :
    IsAddTorsionFree (Z ⧸ B) := by
  refine ⟨fun {k} hk a b hab => ?_⟩
  have hk' : 0 < k := Nat.pos_of_ne_zero hk
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective B a
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective B b
  have h1 : (B.mkQ (k • x) : Z ⧸ B) = B.mkQ (k • y) := by
    rw [map_nsmul, map_nsmul]; exact hab
  have hmem : k • (x - y) ∈ B := by
    have h0 : B.mkQ (k • (x - y)) = 0 := by rw [nsmul_sub, map_sub, h1, sub_self]
    simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using h0
  have h2 : (k : ℤ) • (x - y) ∈ B := by rwa [natCast_zsmul]
  have hxy : x - y ∈ B := h (x - y) k hk' h2
  have h0 : B.mkQ (x - y) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hxy
  rw [map_sub] at h0
  exact sub_eq_zero.mp h0

/-! ## Vanishing of `Hⁿ⁺¹` makes `Zₙ ⧸ Bₙ` torsion free -/

/-- **Vanishing of `Hⁿ⁺¹` of the dual complex makes `Zₙ ⧸ Bₙ` torsion free.** -/
theorem isTorsionFree_quot_of_isZero (E : ChainComplex (ModuleCat ℤ) ℕ)
    (hfree : ∀ k, Module.Free ℤ ↥(E.X k))
    (hfin : ∀ k, Module.Finite ℤ ↥(E.homology k)) (n : ℕ)
    (h : IsZero ((dualComplex ℤ E).homology (n + 1))) :
    Module.IsTorsionFree ℤ (↥(uctZ E n) ⧸ uctH E n) := by
  -- every functional on `uctH E n` extends to `uctZ E n`
  have hextL : ∀ φ : ↥(uctH E n) →ₗ[ℤ] ℤ, ∃ ψ : ↥(uctZ E n) →ₗ[ℤ] ℤ,
      ∀ b : ↥(uctH E n), ψ (b : ↥(uctZ E n)) = φ b := by
    intro φ
    let hBf : ↥(uctB E n) →ₗ[ℤ] ℤ := φ.comp (uctH_uctB_iso' E n).symm.toLinearMap
    obtain ⟨ψ', hψ'⟩ := forall_extends_of_isZero_dual E n h hBf
    refine ⟨ψ'.comp (uctZ E n).subtype, ?_⟩
    intro b
    have h1 : (ψ'.comp (uctB E n).subtype) ((uctH_uctB_iso' E n) b)
        = hBf ((uctH_uctB_iso' E n) b) :=
      LinearMap.congr_fun hψ' ((uctH_uctB_iso' E n) b)
    have h2 : ψ' (((uctH_uctB_iso' E n) b : ↥(uctB E n)) : ↥(E.X n))
        = hBf ((uctH_uctB_iso' E n) b) := by
      simpa only [LinearMap.comp_apply, Submodule.subtype_apply] using h1
    show ψ' ((b.1 : ↥(uctZ E n)) : ↥(E.X n)) = φ b
    have hcoe : (((uctH_uctB_iso' E n) b : ↥(uctB E n)) : ↥(E.X n))
        = ((b.1 : ↥(uctZ E n)) : ↥(E.X n)) := rfl
    rw [← hcoe, h2]
    show hBf ((uctH_uctB_iso' E n) b) = φ b
    simp only [hBf, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply]
  -- the purity of `uctH` inside `uctZ`
  haveI hfreeZ : Module.Free ℤ ↥(uctZ E n) := free_uctZ E hfree n
  haveI htfZ : Module.IsTorsionFree ℤ ↥(uctZ E n) := inferInstance
  have hfreeH : Module.Free ℤ ↥(uctH E n) := free_uctH E hfree n
  have hpure : ∀ (z : ↥(uctZ E n)) (N : ℕ), 0 < N → (N : ℤ) • z ∈ uctH E n →
      z ∈ uctH E n := by
    intro z N hN hz
    exact extendsTorsionFree_local (uctH E n) (free_congr hfreeH) hextL z N hN hz
  exact isTorsionFree_congr (Module.isTorsionFree_int_iff_isAddTorsionFree.mpr
    (isAddTorsionFree_quot_of_pure (uctH E n) hpure))

/-! ## The main theorem -/

/-- **Integral homology from the cohomology.** -/
theorem homology_int_of_dual_int (E : ChainComplex (ModuleCat ℤ) ℕ)
    (hfree : ∀ k, Module.Free ℤ ↥(E.X k))
    (hfin : ∀ k, Module.Finite ℤ ↥(E.homology k)) (n : ℕ)
    (hC : Nonempty ((dualComplex ℤ E).homology n ≅ ModuleCat.of ℤ ℤ))
    (hC0 : IsZero ((dualComplex ℤ E).homology (n + 1))) :
    Nonempty (E.homology n ≅ ModuleCat.of ℤ ℤ) := by
  -- the evaluation map is injective
  have hinj : Function.Injective (eCoh E n) := by
    intro α β hαβ
    have hker : eCoh E n (α - β) = 0 := by rw [map_sub, hαβ, sub_self]
    obtain ⟨N, hNpos, hN0⟩ := eCoh_ker_torsion E hfree hfin n (α - β) hker
    obtain ⟨e⟩ := hC
    let ê : ↥((dualComplex ℤ E).homology n) ≃ₗ[ℤ] ℤ := uctIsoToLinearEquiv e
    have hz : N • ê (α - β) = 0 := by rw [← map_nsmul, hN0, map_zero]
    have he0 : ê (α - β) = 0 := by
      have h := hz
      rw [nsmul_eq_mul] at h
      rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 (by exact_mod_cast hNpos.ne')
      · exact h1
    exact sub_eq_zero.mp (ê.injective (by rw [he0, map_zero]))
  have hbij : Function.Bijective (eCoh E n) := ⟨hinj, eCoh_surjective E hfree n⟩
  -- `Hom(Zₙ ⧸ Bₙ, ℤ) ≅ ℤ`, hence `Hom(Hₙ, ℤ) ≅ ℤ`
  obtain ⟨eC⟩ := hC
  have hDual : Nonempty (Module.Dual ℤ (↥(uctZ E n) ⧸ uctH E n) ≃ₗ[ℤ] ℤ) :=
    ⟨(LinearEquiv.ofBijective (eCoh E n) hbij).symm.trans (uctIsoToLinearEquiv eC)⟩
  obtain ⟨e2⟩ := hDual
  obtain ⟨eh⟩ := homology_iso_H E n
  have hDualH : Nonempty (Module.Dual ℤ ↥(E.homology n) ≃ₗ[ℤ] ℤ) :=
    ⟨(LinearEquiv.dualMap (R := ℤ) (uctIsoToLinearEquiv eh)).symm.trans e2⟩
  -- `Hₙ` is finitely generated and torsion free, hence free
  haveI hfin' : Module.Finite ℤ ↥(E.homology n) := hfin n
  haveI htfq : Module.IsTorsionFree ℤ (↥(uctZ E n) ⧸ uctH E n) :=
    isTorsionFree_quot_of_isZero E hfree hfin n hC0
  haveI htf : Module.IsTorsionFree ℤ ↥(E.homology n) := by
    obtain ⟨eh⟩ := homology_iso_H E n
    haveI htfq' : Module.IsTorsionFree ℤ
        ↥(ModuleCat.of ℤ (↥(uctZ E n) ⧸ uctH E n)) := isTorsionFree_congr htfq
    exact Function.Injective.moduleIsTorsionFree (⇑(uctIsoToLinearEquiv eh))
      (uctIsoToLinearEquiv eh).injective (fun r m => (uctIsoToLinearEquiv eh).map_smul r m)
  haveI hfreeH : Module.Free ℤ ↥(E.homology n) := Module.free_of_finite_type_torsion_free'
  obtain ⟨e3⟩ := freeOfDualInt hDualH
  exact ⟨e3.toModuleIso⟩

end

end Work.ThomBordism
