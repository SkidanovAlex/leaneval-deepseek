import Mathlib
import Submission.Work.SSS.Packet
import Submission.Work.SSS.fg_range_of_ker_le
import Submission.Work.SSS.phiTop
import Submission.Work.SSS.LESFacts
import Submission.Work.SSS.gradedField
import Submission.Work.SSS.baseRow
import Submission.Work.SSS.fibreColFree

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

/-- Transfer of finite generation of `im(H_n(F_a) → H_n(C))` across an equal degree. -/
theorem FG_range_homologyMap_eq {K L : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L) {i j : ℕ} (h : i = j)
    (hf : (LinearMap.range (HomologicalComplex.homologyMap f i).hom).FG) :
    (LinearMap.range (HomologicalComplex.homologyMap f j).hom).FG := by
  subst h; exact hf

theorem E1Complex_d (ξ : Filtration C) (t j : ℕ) : (E1Complex ξ t).d (j+1) j = d1 ξ j t :=
  ChainComplex.of_d (fun s => E1 ξ s t) (fun s => d1 ξ s t) j

theorem sc'_f (ξ : Filtration C) (t k : ℕ) :
    ((E1Complex ξ t).sc' (k+2) (k+1) k).f = d1 ξ (k+1) t := by
  show (E1Complex ξ t).d (k+2) (k+1) = _
  exact E1Complex_d ξ t (k+1)

theorem sc'_g (ξ : Filtration C) (t k : ℕ) :
    ((E1Complex ξ t).sc' (k+2) (k+1) k).g = d1 ξ k t := by
  show (E1Complex ξ t).d (k+1) k = _
  exact E1Complex_d ξ t k

theorem jF_comp_kF (ξ : Filtration C) (s t : ℕ) : jF ξ (s+1) t ≫ kF ξ s t = 0 :=
  ShortComplex.ShortExact.comp_δ (sesF_shortExact ξ s) ((s+1)+t) (s+t)
    (by simp [ComplexShape.down]; omega)

theorem jF_comp_d1 (ξ : Filtration C) (k t : ℕ) : jF ξ (k+1) t ≫ d1 ξ k t = 0 := by
  rw [d1, ← Category.assoc, jF_comp_kF, zero_comp]

theorem kF_comp_incl (ξ : Filtration C) (k t : ℕ) :
    kF ξ (k+1) t ≫ HomologicalComplex.homologyMap (ξ.incl (k+1)) ((k+1)+t) = 0 := by
  have h1 : kF ξ (k+1) t ≫ HomologicalComplex.homologyMap (incF ξ.F (k+1)) ((k+1)+t) = 0 :=
    ShortComplex.ShortExact.δ_comp (sesF_shortExact ξ (k+1)) ((k+1)+1+t) ((k+1)+t)
      (by simp [ComplexShape.down]; omega)
  have h2 : HomologicalComplex.homologyMap (ξ.incl (k+1)) ((k+1)+t) =
      HomologicalComplex.homologyMap (incF ξ.F (k+1)) ((k+1)+t) ≫
      HomologicalComplex.homologyMap (ξ.incl (k+2)) ((k+1)+t) := by
    conv_lhs => rw [show ξ.incl (k+1) = incF ξ.F (k+1) ≫ ξ.incl (k+2) from
      (ξ.compat (Nat.le_succ (k+1))).symm]
    rw [HomologicalComplex.homologyMap_comp]
  rw [h2, ← Category.assoc, h1, zero_comp]

theorem ker_jF_eq_range (ξ : Filtration C) (k t : ℕ) :
    (jF ξ (k+1) t).hom.ker =
      (HomologicalComplex.homologyMap (incF ξ.F k) ((k+1)+t)).hom.range :=
  (((sesF_shortExact ξ k).homology_exact₂ ((k+1)+t)).moduleCat_range_eq_ker).symm

/-- The map `H_{s+t}(F_s) → E²_{s,t}` of the spectral sequence of `ξ`, for `s = k+1`,
realised through the short complex computing `E²_{k+1,t}`. -/
noncomputable def e2Map (ξ : Filtration C) (k t : ℕ) :
    (ξ.F.obj (k+1)).homology ((k+1) + t) ⟶
      ((E1Complex ξ t).sc' (k+2) (k+1) k).homology :=
  ((E1Complex ξ t).sc' (k+2) (k+1) k).liftCycles (jF ξ (k+1) t)
      (by rw [sc'_g]; exact jF_comp_d1 ξ k t) ≫
    ((E1Complex ξ t).sc' (k+2) (k+1) k).homologyπ

/-- In `ModuleCat R`, an element is killed by the projection onto the cokernel of `f` iff it lies
in the range of `f`. -/
lemma coker_π_eq_zero_iff {R : Type*} [Ring R] {X Y : ModuleCat R} (f : X ⟶ Y) (y : Y) :
    (cokernel.π f) y = 0 ↔ y ∈ f.hom.range := by
  constructor
  · intro h
    have h2 : Submodule.Quotient.mk (p := f.hom.range) y = 0 := by
      rw [← ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom_apply f y, h, map_zero]
    exact (Submodule.Quotient.mk_eq_zero (f.hom.range)).mp h2
  · intro h
    obtain ⟨m, hm⟩ := h
    rw [← hm]
    exact cokernel.condition_apply f m

lemma ker_e2Map_sc {R : Type*} [Ring R] (S : ShortComplex (ModuleCat R)) [S.HasHomology]
    {A : ModuleCat R} (φ : A ⟶ S.X₂) (hφ : φ ≫ S.g = 0) (x : A)
    (hx : ((S.liftCycles φ hφ ≫ S.homologyπ).hom) x = 0) :
    (φ.hom) x ∈ (S.f).hom.range := by
  have hA : (((S.liftCycles φ hφ ≫ S.homologyπ) ≫ S.homologyι).hom) x = 0 := by
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, hx, map_zero]
  have hB : ((S.liftCycles φ hφ ≫ S.homologyπ) ≫ S.homologyι) = φ ≫ S.pOpcycles := by
    rw [Category.assoc, ShortComplex.homology_π_ι, ← Category.assoc, ShortComplex.liftCycles_i]
  have h1 : ((φ ≫ S.pOpcycles).hom) x = 0 := by rw [← hB]; exact hA
  have h2 : (S.pOpcycles.hom) ((φ.hom) x) = 0 := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h1
  have hcomp : S.pOpcycles ≫ S.opcyclesIsoCokernel.hom = cokernel.π S.f := by
    rw [ShortComplex.opcyclesIsoCokernel_hom]
    exact S.p_descOpcycles _ _
  have h3 : (cokernel.π S.f).hom ((φ.hom) x) = 0 := by
    have hh := congrArg (fun (g : S.X₂ ⟶ cokernel S.f) => g.hom ((φ.hom) x)) hcomp
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, h2, map_zero] at hh
    exact hh.symm
  have h4 : Submodule.Quotient.mk (p := (S.f).hom.range) ((φ.hom) x) = 0 := by
    rw [← ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom_apply S.f ((φ.hom) x), h3, map_zero]
  exact (Submodule.Quotient.mk_eq_zero ((S.f).hom.range)).mp h4

theorem ker_e2Map_le' (ξ : Filtration C) (k t : ℕ) :
    (e2Map ξ k t).hom.ker ≤
      (HomologicalComplex.homologyMap (incF ξ.F k) ((k+1)+t)).hom.range ⊔
      (HomologicalComplex.homologyMap (ξ.incl (k+1)) ((k+1)+t)).hom.ker := by
  intro x hx
  let S : ShortComplex (ModuleCat ℤ) := (E1Complex ξ t).sc' (k+2) (k+1) k
  let φ : (ξ.F.obj (k+1)).homology ((k+1)+t) ⟶ S.X₂ := jF ξ (k+1) t
  let κ : S.X₁ ⟶ (ξ.F.obj (k+1)).homology ((k+1)+t) := kF ξ (k+1) t
  have hφg : φ ≫ S.g = 0 := by
    show jF ξ (k+1) t ≫ ((E1Complex ξ t).sc' (k+2) (k+1) k).g = 0
    rw [sc'_g]; exact jF_comp_d1 ξ k t
  have hx' : ((S.liftCycles φ hφg ≫ S.homologyπ).hom) x = 0 := by
    show (ModuleCat.Hom.hom (S.liftCycles φ hφg ≫ S.homologyπ)) x = 0
    show (ModuleCat.Hom.hom (e2Map ξ k t)) x = 0
    exact hx
  have hmem : (φ.hom) x ∈ (S.f).hom.range := ker_e2Map_sc S φ hφg x hx'
  have hSf : S.f = κ ≫ φ := by
    show ((E1Complex ξ t).sc' (k+2) (k+1) k).f = kF ξ (k+1) t ≫ jF ξ (k+1) t
    rw [sc'_f]; rfl
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hmem
  have hy' : (φ.hom) (κ.hom y) = (φ.hom) x := by
    rw [← hy, hSf, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hmem2 : x ∈ φ.hom.ker ⊔ κ.hom.range := by
    refine Submodule.mem_sup.mpr ⟨x - κ.hom y, ?_, κ.hom y, ?_, sub_add_cancel x (κ.hom y)⟩
    · rw [LinearMap.mem_ker, map_sub, hy', sub_self]
    · exact LinearMap.mem_range.mpr ⟨y, rfl⟩
  have hrange_le : (kF ξ (k+1) t).hom.range ≤
      (HomologicalComplex.homologyMap (ξ.incl (k+1)) ((k+1)+t)).hom.ker := by
    rw [range_kF_eq_ker_incF ξ (k+1) t]
    intro z hz
    rw [LinearMap.mem_ker] at hz ⊢
    have hfac : ξ.incl (k+1) = incF ξ.F (k+1) ≫ ξ.incl (k+2) :=
      (ξ.compat (Nat.le_succ (k+1))).symm
    rw [hfac, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
      hz, map_zero]
  have hsub : φ.hom.ker ⊔ κ.hom.range ≤
      (HomologicalComplex.homologyMap (incF ξ.F k) ((k+1)+t)).hom.range ⊔
      (HomologicalComplex.homologyMap (ξ.incl (k+1)) ((k+1)+t)).hom.ker := by
    refine sup_le ?_ ?_
    · dsimp only [φ]
      exact le_trans (le_of_eq (ker_jF_eq_range ξ k t)) le_sup_left
    · dsimp only [κ]
      exact le_trans hrange_le le_sup_right
  exact hsub hmem2

theorem graded_succ' (ξ : Filtration C) (n k : ℕ) (hk : k + 1 ≤ n)
    (hE : Module.Finite ℤ (E2 ξ (k+1) (n - (k+1))))
    (hP : (Phi ξ n (k : ℤ)).FG) :
    (Phi ξ n (((k+1 : ℕ) : ℤ))).FG := by
  let t := n - (k+1)
  have ht : (k+1) + t = n := by dsimp only [t]; exact Nat.add_sub_of_le hk
  have hφfin : ((e2Map ξ k t).hom.range).FG := by
    have hKfin : Module.Finite ℤ (((E1Complex ξ t).sc' (k+2) (k+1) k).homology) :=
      haveI : Module.Finite ℤ ((E1Complex ξ t).homology (k+1)) := hE
      Module.Finite.equiv
        (((E1Complex ξ t).homologyIsoSc' (k+2) (k+1) k (by simp) (by simp)).toLinearEquiv)
    exact Submodule.FG.of_le (Module.finite_def.mp hKfin) le_top
  have hM : (Submodule.map (HomologicalComplex.homologyMap (ξ.incl (k+1)) ((k+1)+t)).hom
      (HomologicalComplex.homologyMap (incF ξ.F k) ((k+1)+t)).hom.range).FG := by
    rw [← LinearMap.range_comp]
    rw [show (HomologicalComplex.homologyMap (ξ.incl (k+1)) ((k+1)+t)).hom.comp
        (HomologicalComplex.homologyMap (incF ξ.F k) ((k+1)+t)).hom =
        (HomologicalComplex.homologyMap (ξ.incl k) ((k+1)+t)).hom from ?_]
    · exact FG_range_homologyMap_eq (ξ.incl k) ht.symm hP
    · rw [show (HomologicalComplex.homologyMap (ξ.incl (k+1)) ((k+1)+t)).hom.comp
          (HomologicalComplex.homologyMap (incF ξ.F k) ((k+1)+t)).hom =
          (HomologicalComplex.homologyMap (incF ξ.F k) ((k+1)+t) ≫
            HomologicalComplex.homologyMap (ξ.incl (k+1)) ((k+1)+t)).hom from rfl,
        ← HomologicalComplex.homologyMap_comp, ← ξ.compat (Nat.le_succ k)]
      rfl
  have hmain : ((HomologicalComplex.homologyMap (ξ.incl (k+1)) ((k+1)+t)).hom.range).FG :=
    fg_range_of_ker_le _ _ _ (ker_e2Map_le' ξ k t) hφfin hM
  have h1 : Phi ξ n (((k+1 : ℕ) : ℤ)) =
      (HomologicalComplex.homologyMap (ξ.incl (k+1)) n).hom.range := by
    unfold Phi
    rw [if_neg (by exact_mod_cast Nat.not_lt_zero (k+1))]
    simp only [Int.toNat_natCast]
  rw [h1]
  exact FG_range_homologyMap_eq (ξ.incl (k+1)) ht hmain




/-- **Convergence of the spectral sequence of a saturated filtration.**  For any saturated
filtration `ξ` of a chain complex `C` of `ℤ`-modules, the image filtration `Φ_s ⊆ H_n(C)` of the
E² page `E2 ξ` satisfies the convergence packet: `Φ` is increasing, vanishes below `0` and reaches
`H_n(C)` in degree `n`; each graded piece `Φ_s/Φ_{s-1}` is a subquotient of `E²_{s,n-s}` (read in
the Serre class of finitely generated groups: `E²_{s,n-s}` f.g. and `Φ_{s-1}` f.g. imply `Φ_s` f.g.);
the bottom row `E²_{n,0}` is f.g. if `H_n(C)` is and the E² terms `E²_{n-r,r-1}` (`2 ≤ r ≤ n`) are;
the left column `E²_{0,t}` is f.g. if `Φ_t(0)` and the E² terms `E²_{r,t+1-r}` (`2 ≤ r ≤ t+1`) are. -/
theorem packetOfFiltration (C : ChainComplex (ModuleCat ℤ) ℕ) (ξ : Work.SSS.Filtration C) :
    Work.SSS.SSPacket ξ := by
  refine ⟨fun n => Phi_mono ξ n, fun n s h => Phi_of_neg ξ n h, fun n => phiTop C ξ n, ?_, ?_, ?_⟩
  · intro n s hs hE hP
    exact gradedField C ξ n s hs hE hP
  · intro n hH hE
    exact baseRow C ξ n hH hE
  · intro t hE hP
    exact fibreColFree C ξ t hE hP

end

end Work.SSS
