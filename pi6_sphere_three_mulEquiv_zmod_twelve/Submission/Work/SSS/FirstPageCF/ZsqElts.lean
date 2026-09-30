import Mathlib
import Submission.Work.SSS.FibreColDefs
import Submission.Work.SSS.FirstPage.HomElts
import Submission.Work.SSS.LESFacts
import Submission.Work.SSS.FirstPageCF.E1ComplexD

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Chain-level lemmas about the model `Zsq ξ s n` of the first page

Elementary lemmas about the quotient maps `projQ`, the inclusions `Finc` and the model subgroup
`Zsq ξ s n` of `(F_s/F_{s-1})_n`, used for `Work.SSS.FirstPage.Zsq_quot_injects_E2`.
-/

set_option autoImplicit false
attribute [-instance] AddCommGroup.toIntModule

namespace Work.SSS.FirstPageCF

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

/-- `Finc` does not depend on the proof of the inequality. -/
lemma Finc_proof_irrel (ξ : Filtration C) (j s m : ℕ) (h1 h2 : j ≤ s) (y : (ξ.F.obj j).X m) :
    Finc ξ j s h1 m y = Finc ξ j s h2 m y := by
  show ((ξ.F.map (homOfLE h1)).f m).hom y = ((ξ.F.map (homOfLE h2)).f m).hom y
  congr 2

/-- `Finc` for consecutive indices is the inclusion `incF` of the filtration. -/
lemma Finc_eq_incF (ξ : Filtration C) (k m : ℕ) (h : k ≤ k+1) :
    Finc ξ k (k+1) h m = ModuleCat.Hom.hom ((incF ξ.F k).f m) := by
  show ModuleCat.Hom.hom ((ξ.F.map (homOfLE h)).f m) = ModuleCat.Hom.hom ((incF ξ.F k).f m)
  congr 2

/-- `Finc` is compatible with composition. -/
lemma Finc_comp (ξ : Filtration C) (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) (hac : a ≤ c)
    (m : ℕ) (y : (ξ.F.obj a).X m) :
    Finc ξ a c hac m y = Finc ξ b c hbc m (Finc ξ a b hab m y) := by
  have h : ξ.F.map (homOfLE hab) ≫ ξ.F.map (homOfLE hbc) = ξ.F.map (homOfLE hac) := by
    rw [← Functor.map_comp, homOfLE_comp]
  have h2 := congrArg (fun (g : ξ.F.obj a ⟶ ξ.F.obj c) => (g.f m).hom y) h.symm
  simpa only [Finc, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- The quotient map `F_s → F_s/F_{s-1}` is a chain map: it commutes with the differentials. -/
lemma projQ_d_comm (ξ : Filtration C) (k n : ℕ) (x : (ξ.F.obj (k+1)).X n) :
    ((grF ξ.F (k+1)).d n (n-1)).hom (projQ ξ (k+1) n x) =
      projQ ξ (k+1) (n-1) (dFs ξ (k+1) n (n-1) x) := by
  have h4 : ModuleCat.Hom.hom ((grF ξ.F (k+1)).d n (n-1))
        ∘ₗ ModuleCat.Hom.hom ((cokernel.π (incF ξ.F k)).f n)
      = ModuleCat.Hom.hom ((cokernel.π (incF ξ.F k)).f (n-1))
        ∘ₗ ModuleCat.Hom.hom ((ξ.F.obj (k+1)).d n (n-1)) := by
    have h := congrArg ModuleCat.Hom.hom
      (HomologicalComplex.Hom.comm (cokernel.π (incF ξ.F k)) n (n-1))
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
    exact h
  have h5 := congrArg (fun f => f x) h4
  simp only [LinearMap.comp_apply] at h5
  rw [projQ_succ]
  dsimp only [dFs]
  exact h5

/-- The composite `F_j → F_{k+1} → F_{k+1}/F_k` vanishes for `j ≤ k`. -/
lemma projQ_Finc_eq_zero (ξ : Filtration C) (j k m : ℕ) (h : j ≤ k) (h' : j ≤ k+1)
    (y : (ξ.F.obj j).X m) : projQ ξ (k+1) m (Finc ξ j (k+1) h' m y) = 0 := by
  rw [Finc_comp ξ j k (k+1) h (Nat.le_succ k) h' m y]
  rw [projQ_succ]
  rw [show Finc ξ k (k+1) (Nat.le_succ k) m (Finc ξ j k h m y)
      = (ModuleCat.Hom.hom ((incF ξ.F k).f m)) (Finc ξ j k h m y) from by
    rw [Finc_eq_incF]]
  show (ModuleCat.Hom.hom ((cokernel.π (incF ξ.F k)).f m))
      ((ModuleCat.Hom.hom ((incF ξ.F k).f m)) (Finc ξ j k h m y)) = 0
  have hc := congrArg (fun (g : ξ.F.obj k ⟶ cokernel (incF ξ.F k)) => g.f m)
    (cokernel.condition (incF ξ.F k))
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at hc
  have hc3 := congrArg (fun (g : (ξ.F.obj k).X m ⟶ (cokernel (incF ξ.F k)).X m) =>
    (ModuleCat.Hom.hom g) (Finc ξ j k h m y)) hc
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using hc3

/-- **Membership in the model `Zsq`.** -/
lemma mem_Zsq_iff (ξ : Filtration C) (s n : ℕ) (z : (grF ξ.F s).X n) :
    z ∈ Zsq ξ s n ↔ ∃ x : (ξ.F.obj s).X n, projQ ξ s n x = z ∧
      dFs ξ s n (n-1) x ∈ LinearMap.range (Finc ξ (s-2) s (Nat.sub_le s 2) (n-1)) := by
  rw [Zsq, Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, rfl, hx⟩
  · rintro ⟨x, rfl, hx⟩
    exact ⟨x, hx, rfl⟩

/-- **Elements of `Zsq` are cycles of the graded piece `grF ξ.F s`.** -/
lemma Zsq_d_eq_zero (ξ : Filtration C) (s n : ℕ) (hs : 2 ≤ s) (z : ↥(Zsq ξ s n)) :
    ((grF ξ.F s).d n (n-1)).hom (z : (grF ξ.F s).X n) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
  obtain ⟨x, hx, hxd⟩ := (mem_Zsq_iff ξ (k+2) n z).mp z.2
  obtain ⟨u, hu⟩ := hxd
  rw [← hx, projQ_d_comm, ← hu]
  exact projQ_Finc_eq_zero ξ k (k+1) (n-1) (by omega) (Nat.sub_le (k+2) 2) u

/-- `iCycles` of `liftCycles`. -/
lemma iCycles_liftCycles_C (K : ChainComplex (ModuleCat ℤ) ℕ) {A : ModuleCat ℤ} {n j : ℕ}
    (k : A ⟶ K.X n) (hj : (ComplexShape.down ℕ).next n = j) (hk : k ≫ K.d n j = 0) (a : A) :
    (K.iCycles n).hom ((K.liftCycles k j hj hk) a) = (ModuleCat.Hom.hom k) a := by
  have h := congrArg (fun (g : A ⟶ K.X n) => (ModuleCat.Hom.hom g) a)
    (K.liftCycles_i k j hj hk)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- **Membership in the model `Bsq`.** -/
lemma Bsq_mem_iff (ξ : Filtration C) (s n : ℕ) (z : (grF ξ.F s).X n) :
    z ∈ Bsq ξ s n ↔ ∃ x : (ξ.F.obj s).X n, projQ ξ s n x = z ∧
      ∃ e : (ξ.F.obj (s+1)).X (n+1),
        dFs ξ (s+1) (n+1) n e = Finc ξ s (s+1) (Nat.le_succ s) n x := by
  rw [Bsq, Submodule.mem_map]
  constructor
  · rintro ⟨x, hx1, hx2⟩
    rw [Submodule.mem_comap, Submodule.mem_map] at hx1
    obtain ⟨e, _he1, he2⟩ := hx1
    exact ⟨x, hx2, e, he2⟩
  · rintro ⟨x, hx2, e, he⟩
    refine ⟨x, ?_, hx2⟩
    rw [Submodule.mem_comap, Submodule.mem_map]
    refine ⟨e, ?_, he⟩
    rw [Submodule.mem_comap]
    exact ⟨x, he.symm⟩

/-- The cycle condition for the elements of `Zsq`, in the form of the short complex `K.sc n`. -/
lemma Zsq_sc_cycles (ξ : Filtration C) (s t : ℕ) (hs : 2 ≤ s) (z : ↥(Zsq ξ s (s+t))) :
    ((grF ξ.F s).sc (s+t)).g.hom (z : (grF ξ.F s).X (s+t)) = 0 := by
  show ((grF ξ.F s).d (s+t) ((ComplexShape.down ℕ).next (s+t))).hom
      (z : (grF ξ.F s).X (s+t)) = 0
  rw [next_down_eq_pred (s+t)]
  exact Zsq_d_eq_zero ξ s (s+t) hs z

/-- The class map to the concrete model `ker (d)/im (d)` of the homology of the graded piece. -/
noncomputable def psiConc (ξ : Filtration C) (s t : ℕ) (hs : 2 ≤ s) :
    ↥(Zsq ξ s (s+t)) →ₗ[ℤ] ((grF ξ.F s).sc (s+t)).moduleCatLeftHomologyData.H :=
  (Submodule.mkQ (LinearMap.range ((grF ξ.F s).sc (s+t)).moduleCatToCycles)) ∘ₗ
    ((Zsq ξ s (s+t)).subtype.codRestrict
      (LinearMap.ker (((grF ξ.F s).sc (s+t)).g.hom))
      (fun z => Zsq_sc_cycles ξ s t hs z))

/-- **The class map** `Zsq ξ s (s+t) → E¹_{s,t} = H_{s+t}(F_s/F_{s-1})`, the first-page model of
the map whose kernel on `Zsq` is `Bsq`. -/
noncomputable def psi (ξ : Filtration C) (s t : ℕ) (hs : 2 ≤ s) :
    ↥(Zsq ξ s (s+t)) →ₗ[ℤ] (E1 ξ s t) :=
  (((grF ξ.F s).sc (s+t)).moduleCatHomologyIso.inv).hom.comp (psiConc ξ s t hs)

/-- The class of `z` in `H_{s+t}(grF ξ.F s)` is the homology class of the cycle `z`. -/
lemma psi_apply (ξ : Filtration C) (s t : ℕ) (hs : 2 ≤ s) (z : ↥(Zsq ξ s (s+t))) :
    psi ξ s t hs z = ((grF ξ.F s).sc (s+t)).homologyπ
      (((grF ξ.F s).sc (s+t)).cyclesMk (z : (grF ξ.F s).X (s+t)) (Zsq_sc_cycles ξ s t hs z)) := by
  have h := moduleCatHomologyIso_hom_homologypi_cyclesMk_C ((grF ξ.F s).sc (s+t))
    (z : (grF ξ.F s).X (s+t)) (Zsq_sc_cycles ξ s t hs z)
  show (((grF ξ.F s).sc (s+t)).moduleCatHomologyIso.inv)
      (Submodule.mkQ (LinearMap.range ((grF ξ.F s).sc (s+t)).moduleCatToCycles)
        ⟨(z : (grF ξ.F s).X (s+t)), Zsq_sc_cycles ξ s t hs z⟩) = _
  exact (congrArg (((grF ξ.F s).sc (s+t)).moduleCatHomologyIso.inv) h).symm.trans
    (Iso.hom_inv_id_apply _ _)


/-- The relation of `ComplexShape.down ℕ` between consecutive degrees. -/
lemma rel_down_add (k t : ℕ) : (ComplexShape.down ℕ).Rel ((k+2)+t) ((k+1)+t) := by
  show ((k+1)+t) + 1 = (k+2)+t
  omega

/-- The value of `psi` on `z`, written with the cycles of the graded piece `grF ξ.F (k+2)`. -/
lemma psi_apply_cyclesMk (ξ : Filtration C) (k t : ℕ) (z : ↥(Zsq ξ (k+2) ((k+2)+t)))
    (hj : (ComplexShape.down ℕ).next ((k+2)+t) = ((k+2)+t)-1)
    (hz : ((grF ξ.F (k+2)).d ((k+2)+t) (((k+2)+t)-1)).hom (z : (grF ξ.F (k+2)).X ((k+2)+t)) = 0) :
    psi ξ (k+2) t (by omega) z
      = ((grF ξ.F (k+2)).homologyπ ((k+2)+t))
          (((grF ξ.F (k+2)).cyclesMk (z : (grF ξ.F (k+2)).X ((k+2)+t)) (((k+2)+t)-1) hj hz)) := by
  rw [psi_apply]
  change ((grF ξ.F (k+2)).sc ((k+2)+t)).homologyπ
      (((grF ξ.F (k+2)).sc ((k+2)+t)).cyclesMk (z : (grF ξ.F (k+2)).X ((k+2)+t))
        (Zsq_sc_cycles ξ (k+2) t (by omega) z))
    = ((grF ξ.F (k+2)).sc ((k+2)+t)).homologyπ
        (((grF ξ.F (k+2)).cyclesMk (z : (grF ξ.F (k+2)).X ((k+2)+t)) (((k+2)+t)-1) hj hz))
  rw [sc_cyclesMk_eq_C]

/-- The connecting map `kF ξ (k+1) t` sends the class of a relative cycle to the class of the
lift of its boundary. -/
lemma kF_apply (ξ : Filtration C) (k t : ℕ)
    (x₃ : (grF ξ.F (k+2)).X ((k+2)+t))
    (hx₃ : ((grF ξ.F (k+2)).d ((k+2)+t) ((k+1)+t)).hom x₃ = 0)
    (x₂ : (ξ.F.obj (k+2)).X ((k+2)+t)) (hx₂ : (projQ ξ (k+2) ((k+2)+t)) x₂ = x₃)
    (x₁ : (ξ.F.obj (k+1)).X ((k+1)+t))
    (hx₁ : (ModuleCat.Hom.hom ((incF ξ.F (k+1)).f ((k+1)+t))) x₁
      = (dFs ξ (k+2) ((k+2)+t) ((k+1)+t)) x₂)
    (hj : (ComplexShape.down ℕ).next ((k+2)+t) = (k+1)+t)
    (hj' : (ComplexShape.down ℕ).next ((k+1)+t) = ((k+1)+t)-1) :
    (kF ξ (k+1) t).hom
        (((grF ξ.F (k+2)).homologyπ ((k+2)+t))
          (((grF ξ.F (k+2)).cyclesMk x₃ ((k+1)+t) hj hx₃)))
      = ((ξ.F.obj (k+1)).homologyπ ((k+1)+t))
          (((ξ.F.obj (k+1)).cyclesMk x₁ (((k+1)+t)-1) hj'
            (ShortComplex.ShortExact.d_eq_zero_of_f_eq_d_apply (sesF_shortExact ξ (k+1))
              ((k+2)+t) ((k+1)+t) x₂ x₁ hx₁ (((k+1)+t)-1)))) := by
  have hS := sesF_shortExact ξ (k+1)
  have hδ := ShortComplex.ShortExact.δ_apply hS ((k+2)+t) ((k+1)+t) (rel_down_add k t)
    x₃ hx₃ x₂ hx₂ x₁ hx₁ (((k+1)+t)-1) hj'
  rw [show kF ξ (k+1) t = hS.δ ((k+2)+t) ((k+1)+t) (rel_down_add k t) from rfl]
  exact hδ


/-- If a cycle of `F_{k+1}` maps to `0` in the graded piece `grF ξ.F (k+1)`, then `jF` kills its
class. -/
lemma jF_eq_zero_of_projQ_eq_zero (ξ : Filtration C) (k t : ℕ)
    (x₁ : (ξ.F.obj (k+1)).X ((k+1)+t))
    (hj' : (ComplexShape.down ℕ).next ((k+1)+t) = ((k+1)+t)-1)
    (hx₁' : ((ξ.F.obj (k+1)).d ((k+1)+t) (((k+1)+t)-1)).hom x₁ = 0)
    (h0 : (projQ ξ (k+1) ((k+1)+t)) x₁ = 0) :
    (jF ξ (k+1) t).hom ((HomologicalComplex.homologyπ (ξ.F.obj (k+1)) ((k+1)+t))
        (HomologicalComplex.cyclesMk (ξ.F.obj (k+1)) x₁ (((k+1)+t)-1) hj' hx₁')) = 0 := by
  have hzero : (HomologicalComplex.cyclesMap (cokernel.π (incF ξ.F k)) ((k+1)+t)).hom
      (HomologicalComplex.cyclesMk (ξ.F.obj (k+1)) x₁ (((k+1)+t)-1) hj' hx₁') = 0 := by
    apply iCycles_injective_C
    rw [iCycles_cyclesMap_C, iCycles_cyclesMk_C, map_zero, ← projQ_succ]
    exact h0
  change (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (cokernel.π (incF ξ.F k)) ((k+1)+t)))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (ξ.F.obj (k+1)) ((k+1)+t)))
        (HomologicalComplex.cyclesMk (ξ.F.obj (k+1)) x₁ (((k+1)+t)-1) hj' hx₁')) = 0
  rw [homologyMap_homologypi_C, hzero, map_zero]

/-- **The first differential kills the class map**: an element of `Zsq`, regarded as a class in
`E¹_{s,t}`, is a cycle of the row complex (i.e. lies in the kernel of `d¹`). -/
lemma d1_sc_psi (ξ : Filtration C) (k t : ℕ) (z : ↥(Zsq ξ (k+2) ((k+2)+t))) :
    (((E1Complex ξ t).sc' (k+3) (k+2) (k+1)).g.hom) (psi ξ (k+2) t (by omega) z) = 0 := by
  have hg : (((E1Complex ξ t).sc' (k+3) (k+2) (k+1)).g.hom) = (d1 ξ (k+1) t).hom := by
    rw [show ((E1Complex ξ t).sc' (k+3) (k+2) (k+1)).g
        = (E1Complex ξ t).d (k+2) (k+1) from rfl]
    exact congrArg ModuleCat.Hom.hom (E1Complex_d ξ t (k+1))
  rw [hg, show (d1 ξ (k+1) t).hom
      = ((jF ξ (k+1) t).hom).comp ((kF ξ (k+1) t).hom) from rfl]
  show (ModuleCat.Hom.hom (jF ξ (k+1) t))
      ((ModuleCat.Hom.hom (kF ξ (k+1) t)) (psi ξ (k+2) t (by omega) z)) = 0
  obtain ⟨x, hxproj, hxd⟩ := (mem_Zsq_iff ξ (k+2) ((k+2)+t) z).mp z.2
  have he : ((k+2)+t) - 1 = (k+1) + t := by omega
  have hxd' : ∃ y : (ξ.F.obj k).X ((k+1)+t),
      (Finc ξ k (k+2) (Nat.sub_le (k+2) 2) ((k+1)+t)) y
        = (dFs ξ (k+2) ((k+2)+t) ((k+1)+t)) x :=
    eq_mp_of_eq_index he (fun j => ∃ y : (ξ.F.obj k).X j,
        (Finc ξ k (k+2) (Nat.sub_le (k+2) 2) j) y = (dFs ξ (k+2) ((k+2)+t) j) x)
      ((LinearMap.mem_range).mp hxd)
  obtain ⟨y, hy⟩ := hxd'
  have hz : ((grF ξ.F (k+2)).d ((k+2)+t) ((k+1)+t)).hom
      (z : (grF ξ.F (k+2)).X ((k+2)+t)) = 0 :=
    eq_mp_of_eq_index he
      (fun j => ((grF ξ.F (k+2)).d ((k+2)+t) j).hom (z : (grF ξ.F (k+2)).X ((k+2)+t)) = 0)
      (Zsq_d_eq_zero ξ (k+2) ((k+2)+t) (by omega) z)
  have hx₁ : (ModuleCat.Hom.hom ((incF ξ.F (k+1)).f ((k+1)+t)))
      ((Finc ξ k (k+1) (Nat.le_succ k) ((k+1)+t)) y)
      = (dFs ξ (k+2) ((k+2)+t) ((k+1)+t)) x := by
    rw [← Finc_eq_incF ξ (k+1) ((k+1)+t) (by omega)]
    rw [← Finc_comp ξ k (k+1) (k+2) (Nat.le_succ k) (by omega) (Nat.sub_le (k+2) 2)
      ((k+1)+t) y]
    exact hy
  have hz' : (((grF ξ.F (k+2)).sc ((k+2)+t)).g.hom)
      (z : (grF ξ.F (k+2)).X ((k+2)+t)) = 0 := Zsq_sc_cycles ξ (k+2) t (by omega) z
  have hj₂ : (ComplexShape.down ℕ).next ((k+2)+t) = (k+1)+t :=
    (next_down_eq_pred ((k+2)+t)).trans he
  have hbridge := sc_cyclesMk_eq_C (grF ξ.F (k+2)) ((k+2)+t)
    (z : (grF ξ.F (k+2)).X ((k+2)+t)) hz' ((k+1)+t) hj₂ hz
  rw [psi_apply, hbridge]
  change (ModuleCat.Hom.hom (jF ξ (k+1) t))
      ((ModuleCat.Hom.hom (kF ξ (k+1) t))
        ((HomologicalComplex.homologyπ (grF ξ.F (k+2)) ((k+2)+t))
          (HomologicalComplex.cyclesMk (grF ξ.F (k+2))
            (z : (grF ξ.F (k+2)).X ((k+2)+t)) ((k+1)+t) hj₂ hz))) = 0
  have hkf := kF_apply ξ k t (z : (grF ξ.F (k+2)).X ((k+2)+t)) hz x hxproj
    ((Finc ξ k (k+1) (Nat.le_succ k) ((k+1)+t)) y) hx₁ hj₂ (next_down_eq_pred ((k+1)+t))
  rw [hkf]
  exact jF_eq_zero_of_projQ_eq_zero ξ k t
    ((Finc ξ k (k+1) (Nat.le_succ k) ((k+1)+t)) y) (next_down_eq_pred ((k+1)+t)) _ 
    (projQ_Finc_eq_zero ξ k k ((k+1)+t) le_rfl (Nat.le_succ k) y)


/-- `jF` sends the class of a cycle `x` of `F_{k+1}` to the class of `z` in the graded piece,
whenever `z` is the image of `x` in `grF ξ.F (k+1)`. -/
lemma jF_apply_cyclesMk (ξ : Filtration C) (k t : ℕ)
    (x : (ξ.F.obj (k+1)).X ((k+1)+t))
    (z : (grF ξ.F (k+1)).X ((k+1)+t)) (hxproj : (projQ ξ (k+1) ((k+1)+t)) x = z)
    (hj : (ComplexShape.down ℕ).next ((k+1)+t) = ((k+1)+t)-1)
    (hx : ((ξ.F.obj (k+1)).d ((k+1)+t) (((k+1)+t)-1)).hom x = 0)
    (hj₂ : (ComplexShape.down ℕ).next ((k+1)+t) = ((k+1)+t)-1)
    (hz : ((grF ξ.F (k+1)).d ((k+1)+t) (((k+1)+t)-1)).hom z = 0) :
    (jF ξ (k+1) t).hom ((HomologicalComplex.homologyπ (ξ.F.obj (k+1)) ((k+1)+t))
        (HomologicalComplex.cyclesMk (ξ.F.obj (k+1)) x (((k+1)+t)-1) hj hx))
      = (HomologicalComplex.homologyπ (grF ξ.F (k+1)) ((k+1)+t))
        (HomologicalComplex.cyclesMk (grF ξ.F (k+1)) z (((k+1)+t)-1) hj₂ hz) := by
  have hgoal : (ModuleCat.Hom.hom (HomologicalComplex.iCycles (grF ξ.F (k+1)) ((k+1)+t)))
      (HomologicalComplex.cyclesMk (grF ξ.F (k+1)) z (((k+1)+t)-1) hj₂ hz) = z :=
    iCycles_cyclesMk_C (C := grF ξ.F (k+1)) (x := z) (hj := hj₂) (hx := hz)
  have hcyc : (ModuleCat.Hom.hom
        (HomologicalComplex.cyclesMap (cokernel.π (incF ξ.F k)) ((k+1)+t)))
      (HomologicalComplex.cyclesMk (ξ.F.obj (k+1)) x (((k+1)+t)-1) hj hx)
      = HomologicalComplex.cyclesMk (grF ξ.F (k+1)) z (((k+1)+t)-1) hj₂ hz := by
    apply iCycles_injective_C
    rw [iCycles_cyclesMap_C, iCycles_cyclesMk_C]
    change (ModuleCat.Hom.hom ((cokernel.π (incF ξ.F k)).f ((k+1)+t))) x
        = (ModuleCat.Hom.hom (HomologicalComplex.iCycles (grF ξ.F (k+1)) ((k+1)+t)))
          (HomologicalComplex.cyclesMk (grF ξ.F (k+1)) z (((k+1)+t)-1) hj₂ hz)
    rw [hgoal, ← projQ_succ]
    exact hxproj
  change (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (cokernel.π (incF ξ.F k)) ((k+1)+t)))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (ξ.F.obj (k+1)) ((k+1)+t)))
        (HomologicalComplex.cyclesMk (ξ.F.obj (k+1)) x (((k+1)+t)-1) hj hx)) = _
  rw [show (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (cokernel.π (incF ξ.F k)) ((k+1)+t)))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (ξ.F.obj (k+1)) ((k+1)+t)))
        (HomologicalComplex.cyclesMk (ξ.F.obj (k+1)) x (((k+1)+t)-1) hj hx))
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyπ (grF ξ.F (k+1)) ((k+1)+t)))
        ((ModuleCat.Hom.hom
          (HomologicalComplex.cyclesMap (cokernel.π (incF ξ.F k)) ((k+1)+t)))
          (HomologicalComplex.cyclesMk (ξ.F.obj (k+1)) x (((k+1)+t)-1) hj hx))
      from homologyMap_homologypi_C _ _ _ _ _]
  rw [hcyc]


/-- **`Bsq` is contained in the kernel of the class map followed by `d¹`**: an element of the model
`Bsq` maps into the image of `d¹ ξ (k+2) t` inside `E²`. -/
lemma Bsq_le_psi_range (ξ : Filtration C) (k t : ℕ) (z : ↥(Zsq ξ (k+2) ((k+2)+t)))
    (hz : (z : (grF ξ.F (k+2)).X ((k+2)+t)) ∈ Bsq ξ (k+2) ((k+2)+t)) :
    psi ξ (k+2) t (by omega) z ∈ LinearMap.range ((d1 ξ (k+2) t).hom) := by
  obtain ⟨x, hxproj, he0⟩ := (Bsq_mem_iff ξ (k+2) ((k+2)+t) (z : _)).mp hz
  have he0' : ∃ e : (ξ.F.obj (k+3)).X (((k+2)+t)+1),
      (dFs ξ (k+3) (((k+2)+t)+1) ((k+2)+t)) e
        = (Finc ξ (k+2) (k+3) (Nat.le_succ (k+2)) ((k+2)+t)) x := he0
  obtain ⟨e0, hee0⟩ := he0'
  have he : ∃ e : (ξ.F.obj (k+3)).X ((k+3)+t),
      (dFs ξ (k+3) ((k+3)+t) ((k+2)+t)) e
        = (Finc ξ (k+2) (k+3) (Nat.le_succ (k+2)) ((k+2)+t)) x :=
    eq_mp_of_eq_index (by omega : ((k+2)+t)+1 = (k+3)+t)
      (fun m => ∃ e : (ξ.F.obj (k+3)).X m,
        (dFs ξ (k+3) m ((k+2)+t)) e
          = (Finc ξ (k+2) (k+3) (Nat.le_succ (k+2)) ((k+2)+t)) x) he0
  obtain ⟨e, hee⟩ := he
  have hx₁' : (ModuleCat.Hom.hom ((incF ξ.F (k+2)).f ((k+2)+t))) x
      = ((ξ.F.obj (k+3)).d ((k+3)+t) ((k+2)+t)) e := hee.symm
  have hxc : ((ξ.F.obj (k+2)).d ((k+2)+t) (((k+2)+t)-1)).hom x = 0 :=
    ShortComplex.ShortExact.d_eq_zero_of_f_eq_d_apply (sesF_shortExact ξ (k+2))
      ((k+3)+t) ((k+2)+t) e x hx₁' (((k+2)+t)-1)
  have hzcyc : ((grF ξ.F (k+2)).d ((k+2)+t) (((k+2)+t)-1)).hom
      (z : (grF ξ.F (k+2)).X ((k+2)+t)) = 0 :=
    Zsq_d_eq_zero ξ (k+2) ((k+2)+t) (by omega) z
  have hxjf : psi ξ (k+2) t (by omega) z = (jF ξ (k+2) t).hom
      ((HomologicalComplex.homologyπ (ξ.F.obj (k+2)) ((k+2)+t))
        (HomologicalComplex.cyclesMk (ξ.F.obj (k+2)) x (((k+2)+t)-1)
          (next_down_eq_pred ((k+2)+t)) hxc)) := by
    rw [jF_apply_cyclesMk ξ (k+1) t x (z : (grF ξ.F (k+2)).X ((k+2)+t)) hxproj
      (next_down_eq_pred ((k+2)+t)) hxc (next_down_eq_pred ((k+2)+t)) hzcyc]
    exact psi_apply_cyclesMk ξ k t z (next_down_eq_pred ((k+2)+t)) hzcyc
  have hxker : (HomologicalComplex.homologyMap (incF ξ.F (k+2)) ((k+2)+t)).hom
      ((HomologicalComplex.homologyπ (ξ.F.obj (k+2)) ((k+2)+t))
        (HomologicalComplex.cyclesMk (ξ.F.obj (k+2)) x (((k+2)+t)-1)
          (next_down_eq_pred ((k+2)+t)) hxc)) = 0 := by
    have h2 : (HomologicalComplex.cyclesMap (incF ξ.F (k+2)) ((k+2)+t)).hom
        (HomologicalComplex.cyclesMk (ξ.F.obj (k+2)) x (((k+2)+t)-1)
          (next_down_eq_pred ((k+2)+t)) hxc)
        = HomologicalComplex.cyclesMk (ξ.F.obj (k+3))
            (((ξ.F.obj (k+3)).d ((k+3)+t) ((k+2)+t)) e) (((k+2)+t)-1)
            (next_down_eq_pred ((k+2)+t))
            (d_comp_d_apply_C (ξ.F.obj (k+3)) ((k+3)+t) ((k+2)+t) (((k+2)+t)-1) e) := by
      apply iCycles_injective_C
      rw [iCycles_cyclesMap_C, iCycles_cyclesMk_C, iCycles_cyclesMk_C]
      exact hx₁'
    rw [show (HomologicalComplex.homologyMap (incF ξ.F (k+2)) ((k+2)+t)).hom
        ((HomologicalComplex.homologyπ (ξ.F.obj (k+2)) ((k+2)+t))
          (HomologicalComplex.cyclesMk (ξ.F.obj (k+2)) x (((k+2)+t)-1)
            (next_down_eq_pred ((k+2)+t)) hxc))
        = (HomologicalComplex.homologyπ (ξ.F.obj (k+3)) ((k+2)+t))
          ((HomologicalComplex.cyclesMap (incF ξ.F (k+2)) ((k+2)+t)).hom
            (HomologicalComplex.cyclesMk (ξ.F.obj (k+2)) x (((k+2)+t)-1)
              (next_down_eq_pred ((k+2)+t)) hxc))
        from homologyMap_homologypi_C _ _ _ _ _]
    rw [h2]
    exact (d_eq_iCycles_iff_homologypi_eq_zero (ξ.F.obj (k+3)) ((k+2)+t)
      (HomologicalComplex.cyclesMk (ξ.F.obj (k+3))
        (((ξ.F.obj (k+3)).d ((k+3)+t) ((k+2)+t)) e) (((k+2)+t)-1)
        (next_down_eq_pred ((k+2)+t)) _)).mp
      ⟨e0, by rw [iCycles_cyclesMk_C]; exact hee0.trans hee.symm⟩
  have hxrange : (HomologicalComplex.homologyπ (ξ.F.obj (k+2)) ((k+2)+t))
      (HomologicalComplex.cyclesMk (ξ.F.obj (k+2)) x (((k+2)+t)-1)
        (next_down_eq_pred ((k+2)+t)) hxc)
      ∈ LinearMap.range ((kF ξ (k+2) t).hom) := by
    rw [range_kF_eq_ker_incF ξ (k+2) t]
    exact hxker
  obtain ⟨w, hw⟩ := hxrange
  refine ⟨w, ?_⟩
  rw [show (d1 ξ (k+2) t).hom
      = ((jF ξ (k+2) t).hom).comp ((kF ξ (k+2) t).hom) from rfl]
  show (ModuleCat.Hom.hom (jF ξ (k+2) t)) ((ModuleCat.Hom.hom (kF ξ (k+2) t)) w) = _
  rw [hw, ← hxjf]



end

end Work.SSS.FirstPageCF
