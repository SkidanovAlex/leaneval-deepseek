import Mathlib
import Submission.Work.ATOM.ZS.NullSeqMaps
import Submission.Work.ATOM.ZS.e_fix_of_mem_A_of_le
import Submission.Work.ATOM.Toolkit.MonoidalPreadditive

set_option linter.style.haveILetI false

namespace Work.ATOM.ZS

open CategoryTheory Limits MonoidalCategory LightCondensed OnePoint
open scoped LightProfinite

noncomputable section

variable (S : LightProfinite.{0})

/-! ## The categorical input

The identity `h₃` of REFS/03 §1 is `(id_P ⊗ g) ≫ F = F_P ≫ g̃`.  Both sides live on `P ⊗ P`, so
we first cancel the epimorphism `E_{A'} : ℤ[(ℕ∪∞)²] ⟶ P ⊗ P` (`Work.ATOM.EApp`) and compare the
two composites on `ℤ[(ℕ∪∞)²]`.  The right hand side is then a `zmap`-combination after
`Work.ATOM.FP_spec` and `Work.ATOM.g_spec`; for the left hand side one has to bring `g` into play,
which is *not* a combination of `zmap`s: one pulls back along `𝟙 ⊗ π : (ℕ∪∞) × T' ⟶ (ℕ∪∞)²` and
uses the descent property `Work.ATOM.gBig_spec` of `g` over `T'`. -/

/-- The epimorphism `E_{A'} : ℤ[(ℕ∪∞)²] ⟶ P ⊗ P`. -/
theorem epi_EApp : Epi (Work.ATOM.EApp :
    Work.ATOM.zfree Work.ATOM.NS2 ⟶ Work.ATOM.tmul LightCondensed.P LightCondensed.P) := by
  have hP : Epi LightCondensed.P_proj :=
    inferInstanceAs (Epi (cokernel.π LightCondensed.P_map))
  have h1 : Epi (LightCondensed.P_proj ▷ Work.ATOM.zfree LightProfinite.NatUnionInfty) := by
    haveI := hP
    exact Functor.map_epi (MonoidalCategory.tensorRight
      (Work.ATOM.zfree LightProfinite.NatUnionInfty)) LightCondensed.P_proj
  have h2 : Epi (LightCondensed.P ◁ LightCondensed.P_proj) := by
    haveI := hP
    exact Functor.map_epi (MonoidalCategory.tensorLeft LightCondensed.P) LightCondensed.P_proj
  rw [Work.ATOM.EApp]
  exact epi_comp _ _

/-- **The key interchange.**  For `f : Y ⟶ S` the projection `E_A` of `ℤ[(ℕ∪∞) × Y]` to
`P ⊗ ℤ[Y]` followed by `P ◁ ℤ[f]` is `ℤ[𝟙 ⊗ f]` followed by `E_A`.  This is how the `zmap`-level
computations on `(ℕ∪∞) × S` are transported to `P ⊗ ℤ[S]`. -/
theorem EA_whiskerLeft_zmap (Y : LightProfinite.{0}) (f : Y ⟶ S) :
    Work.ATOM.EA Y ≫ (LightCondensed.P ◁ Work.ATOM.zmap f) =
      Work.ATOM.zmap (LightProfinite.NatUnionInfty ◁ f) ≫ Work.ATOM.EA S := by
  have key : (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty Y).hom ≫
        Work.ATOM.zmap (LightProfinite.NatUnionInfty ◁ f) =
      (Work.ATOM.zfree LightProfinite.NatUnionInfty ◁ Work.ATOM.zmap f) ≫
        (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty S).hom := by
    have h := Work.ATOM.zfreeTensorIso_natural
      (X := LightProfinite.NatUnionInfty) (X' := LightProfinite.NatUnionInfty)
      (Y := Y) (Y' := S) (𝟙 LightProfinite.NatUnionInfty) f
    simpa using h
  have h1 : Work.ATOM.zmap (LightProfinite.NatUnionInfty ◁ f) =
      (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty Y).inv ≫
        (Work.ATOM.zfree LightProfinite.NatUnionInfty ◁ Work.ATOM.zmap f) ≫
        (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty S).hom := by
    calc Work.ATOM.zmap (LightProfinite.NatUnionInfty ◁ f)
        = (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty Y).inv ≫
            (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty Y).hom ≫
            Work.ATOM.zmap (LightProfinite.NatUnionInfty ◁ f) := by
          rw [Iso.inv_hom_id_assoc]
      _ = (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty Y).inv ≫
            ((Work.ATOM.zfree LightProfinite.NatUnionInfty ◁ Work.ATOM.zmap f) ≫
              (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty S).hom) := by
          rw [key]
      _ = _ := rfl
  have hnat : Work.ATOM.zmap (LightProfinite.NatUnionInfty ◁ f) ≫
        (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty S).inv =
      (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty Y).inv ≫
        (Work.ATOM.zfree LightProfinite.NatUnionInfty ◁ Work.ATOM.zmap f) := by
    rw [h1]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  calc Work.ATOM.EA Y ≫ (LightCondensed.P ◁ Work.ATOM.zmap f)
      = (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty Y).inv ≫
          ((LightCondensed.P_proj ▷ Work.ATOM.zfree Y) ≫
            (LightCondensed.P ◁ Work.ATOM.zmap f)) := by
        rw [Work.ATOM.EA, Category.assoc]
    _ = (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty Y).inv ≫
          ((Work.ATOM.zfree LightProfinite.NatUnionInfty ◁ Work.ATOM.zmap f) ≫
            (LightCondensed.P_proj ▷ Work.ATOM.zfree S)) := by
        rw [whisker_exchange LightCondensed.P_proj (Work.ATOM.zmap f)]
    _ = Work.ATOM.zmap (LightProfinite.NatUnionInfty ◁ f) ≫
          ((Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty S).inv ≫
            (LightCondensed.P_proj ▷ Work.ATOM.zfree S)) := by
        rw [← Category.assoc, ← hnat, Category.assoc]
    _ = Work.ATOM.zmap (LightProfinite.NatUnionInfty ◁ f) ≫ Work.ATOM.EA S := by
        rw [Work.ATOM.EA]

section HThree

variable [Infinite S]

/-- The space `(ℕ∪∞) × T'` on which the two sides of `h₃` are compared. -/
abbrev X : LightProfinite.{0} := Work.ATOM.NS (Work.ATOM.T' S)

/-! ## The map `Φ : (ℕ∪∞) × T' ⟶ T'`, `(k,(j,u)) ↦ (φ_P(k,j),u)` -/

/-- `φ_P(k,∞) = ∞` for every `k`. -/
lemma phiPFun_infty_right (k : ↥LightProfinite.NatUnionInfty) :
    Work.ATOM.phiPFun S (k, (∞ : ↥LightProfinite.NatUnionInfty)) = ∞ := by
  by_cases hk : k = ∞
  · rw [hk]; exact Work.ATOM.phiPFun_infty_left (S := S) _
  · obtain ⟨m, hm⟩ := OnePoint.ne_infty_iff_exists.mp hk
    rw [← hm]; exact Work.ATOM.phiPFun_some_infty m

/-- `φ_P(k,j) = j` whenever `φ_P(k,j) ≠ ∞`; in other words `φ_P(k,j)` is either `j` or `∞`. -/
lemma phiPFun_eq_self_of_ne_infty (k j : ↥LightProfinite.NatUnionInfty)
    (h : Work.ATOM.phiPFun S (k, j) ≠ ∞) : Work.ATOM.phiPFun S (k, j) = j := by
  by_cases hj : j = ∞
  · rw [hj] at h; exact absurd (phiPFun_infty_right S k) h
  · obtain ⟨l, hl⟩ := OnePoint.ne_infty_iff_exists.mp hj
    rw [← hl] at h ⊢
    by_cases hk : k = ∞
    · rw [hk] at h; exact absurd (Work.ATOM.phiPFun_infty_left (S := S) _) h
    · obtain ⟨m, hm⟩ := OnePoint.ne_infty_iff_exists.mp hk
      rw [← hm] at h ⊢
      rw [Work.ATOM.phiPFun_some_some] at h ⊢
      by_cases hle : m ≤ Work.ATOM.lvl S l
      · simp only [hle, ↓reduceIte] at h ⊢
      · simp only [hle, ↓reduceIte] at h ⊢; exact absurd rfl h

/-- `(φ_P(k,j), u)` is a point of `T'` whenever `(j,u)` is. -/
theorem phi_mem_tSet (k : ↥LightProfinite.NatUnionInfty) (p : ↥(Work.ATOM.T' S)) :
    Work.ATOM.mkNS S (Work.ATOM.phiPFun S (k, Work.ATOM.tProj S p)) (Work.ATOM.pr₂T S p)
      ∈ Work.ATOM.tSet S := by
  rw [Work.ATOM.mem_tSet_iff]
  by_cases hphi : Work.ATOM.phiPFun S (k, Work.ATOM.tProj S p) = ∞
  · exact Or.inl hphi
  · have hjne : Work.ATOM.tProj S p ≠ ∞ := by
      intro h
      exact hphi (by rw [h]; exact phiPFun_infty_right S k)
    obtain ⟨l, hl⟩ := OnePoint.ne_infty_iff_exists.mp hjne
    exact Or.inr ⟨l, (phiPFun_eq_self_of_ne_infty S k _ hphi).trans hl.symm,
      Work.ATOM.tSet_second_eq p.2 hl.symm⟩

/-- The underlying function of `Φ`. -/
def PhiFun (x : ↥(X S)) : ↥(Work.ATOM.T' S) :=
  ⟨Work.ATOM.mkNS S (Work.ATOM.phiPFun S (x.1, x.2.1.1)) x.2.1.2, phi_mem_tSet S x.1 x.2⟩

lemma PhiFun_continuous : Continuous (PhiFun S) := by
  have hpr : Continuous (fun x : ↥(X S) => (Work.ATOM.pr₂T S) x.2) :=
    (ConcreteCategory.hom (Work.ATOM.pr₂T S)).continuous_toFun.comp continuous_snd
  have htp : Continuous (fun x : ↥(X S) => (Work.ATOM.tProj S) x.2) :=
    (ConcreteCategory.hom (Work.ATOM.tProj S)).continuous_toFun.comp continuous_snd
  have hpair : Continuous (fun x : ↥(X S) => (x.1, (Work.ATOM.tProj S) x.2)) :=
    Continuous.prodMk continuous_fst htp
  have hphi : Continuous (fun x : ↥(X S) => Work.ATOM.phiPFun S (x.1, (Work.ATOM.tProj S) x.2)) :=
    (ConcreteCategory.hom (Work.ATOM.phiP S)).continuous_toFun.comp hpair
  have hval : Continuous (fun x : ↥(X S) =>
      Work.ATOM.mkNS S (Work.ATOM.phiPFun S (x.1, (Work.ATOM.tProj S) x.2))
        ((Work.ATOM.pr₂T S) x.2)) := Continuous.prodMk hphi hpr
  exact Continuous.subtype_mk hval (fun x => phi_mem_tSet S x.1 x.2)

/-- **The map `Φ : (ℕ∪∞) × T' ⟶ T'`**, `Φ(k,(j,u)) = (φ_P(k,j),u)`. -/
def Phi : X S ⟶ Work.ATOM.T' S :=
  ConcreteCategory.ofHom ⟨PhiFun S, PhiFun_continuous S⟩

/-- The first component of `Φ` is `φ_P` applied to the first two coordinates. -/
lemma Phi_tProj : Phi S ≫ Work.ATOM.tProj S =
    (LightProfinite.NatUnionInfty ◁ Work.ATOM.tProj S) ≫ Work.ATOM.phiP S := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- The second component of `Φ` is the second coordinate. -/
lemma Phi_pr₂T : Phi S ≫ Work.ATOM.pr₂T S =
    (LightProfinite.NatUnionInfty ◁ Work.ATOM.pr₂T S) ≫ Work.ATOM.pr₂N S := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-! ## The five maps on `(ℕ∪∞) × T'` -/

/-- `ψ₀(k,(j,u)) = u`. -/
def psi0 : X S ⟶ S := (LightProfinite.NatUnionInfty ◁ Work.ATOM.pr₂T S) ≫ Work.ATOM.pr₂N S

/-- `ψ₂(k,(j,u)) = ẽ(k,u)`. -/
def psi2 : X S ⟶ S := (LightProfinite.NatUnionInfty ◁ Work.ATOM.pr₂T S) ≫ Work.ATOM.ePred S

/-- `ψ₃(k,(j,u)) = β(j,u)`. -/
def psi3 : X S ⟶ S := (LightProfinite.NatUnionInfty ◁ Work.ATOM.betaT S) ≫ Work.ATOM.pr₂N S

/-- `ψ₁(k,(j,u)) = β(φ_P(k,j),u)`. -/
def psi1 : X S ⟶ S := Phi S ≫ Work.ATOM.betaT S

/-- `ψ₄(k,(j,u)) = ẽ(k,β(j,u))`. -/
def psi4 : X S ⟶ S := (LightProfinite.NatUnionInfty ◁ Work.ATOM.betaT S) ≫ Work.ATOM.ePred S

/-! ## The computational core

The proof of `h₃` factors as: `m ≫ F = FP ≫ g̃` iff `E ≫ m ≫ F = E ≫ FP ≫ g̃` (`E = EApp` is
epi) iff the two sides agree after pulling back along `c = 𝟙 ⊗ π`, which is checked by the two
computations below and the vanishing of the difference on the three pieces of the cover. -/

/-- `c = 𝟙 ⊗ π : (ℕ∪∞) × T' ⟶ (ℕ∪∞)²`, the map along which the comparison is made. -/
def cMap : X S ⟶ Work.ATOM.NS2 :=
  MonoidalCategory.whiskerLeft LightProfinite.NatUnionInfty (Work.ATOM.tProj S)

/-- **`E_{A'} ≫ (id_P ⊗ g) = E_A ≫ (id_P ⊗ gBig)`**:  the tensor product is right exact, so the
projection `E_{A'}` of `ℤ[(ℕ∪∞)²]` to `P ⊗ P` followed by `id_P ⊗ g` is the projection
`E_A` of `ℤ[(ℕ∪∞) × (ℕ∪∞)]` to `P ⊗ ℤ[ℕ∪∞]` followed by `id_P ⊗ gBig`. -/
theorem EApp_comp_m :
    Work.ATOM.EApp ≫ Work.ATOM.m S =
      Work.ATOM.EA LightProfinite.NatUnionInfty ≫ (LightCondensed.P ◁ Work.ATOM.gBig S) := by
  rw [Work.ATOM.EApp, Work.ATOM.m, Work.ATOM.EA]
  simp only [Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp, Work.ATOM.g_spec]

/-- `Work.ATOM.Fsection` unfolded: `(zmap pr₂N − zmap ePred) ≫ qred`. -/
private lemma h3pl_Fsection_eq :
    Work.ATOM.Fsection S =
      (Work.ATOM.zmap (Work.ATOM.pr₂N S) - Work.ATOM.zmap (Work.ATOM.ePred S)) ≫
        Work.ATOM.qred S (Work.ATOM.levelData S).s₀ := rfl

/-- Precomposing `Fsection` with `zmap (𝟙 ◁ pr₂T)` produces the two `ψ`-terms coming from the
second coordinate; this is `(zmap pr₂N − zmap ePred)` with the `zmap`s combined. -/
private lemma h3pl_hPr2 :
    Work.ATOM.zmap
        (MonoidalCategoryStruct.whiskerLeft LightProfinite.NatUnionInfty (Work.ATOM.pr₂T S)) ≫
        Work.ATOM.Fsection S =
      (Work.ATOM.zmap (psi0 S) - Work.ATOM.zmap (psi2 S)) ≫
        Work.ATOM.qred S (Work.ATOM.levelData S).s₀ := by
  rw [h3pl_Fsection_eq S, ← Category.assoc, Preadditive.comp_sub, ← zmap_comp, ← zmap_comp]
  simp only [psi0, psi2]

/-- The same for `β`: precomposing `Fsection` with `zmap (𝟙 ◁ betaT)` produces `ψ₃, ψ₄`. -/
private lemma h3pl_hBeta :
    Work.ATOM.zmap
        (MonoidalCategoryStruct.whiskerLeft LightProfinite.NatUnionInfty (Work.ATOM.betaT S)) ≫
        Work.ATOM.Fsection S =
      (Work.ATOM.zmap (psi3 S) - Work.ATOM.zmap (psi4 S)) ≫
        Work.ATOM.qred S (Work.ATOM.levelData S).s₀ := by
  rw [h3pl_Fsection_eq S, ← Category.assoc, Preadditive.comp_sub, ← zmap_comp, ← zmap_comp]
  simp only [psi3, psi4]

/-- The left half of the pullback: `EA (T' S) ≫ (P ◁ zmap pr₂T) ≫ F S` is
`(zmap ψ₀ − zmap ψ₂) ≫ qred`. -/
private lemma h3pl_hL :
    (Work.ATOM.EA (Work.ATOM.T' S) ≫
        (MonoidalCategoryStruct.whiskerLeft LightCondensed.P
          (Work.ATOM.zmap (Work.ATOM.pr₂T S)))) ≫ Work.ATOM.F S =
      (Work.ATOM.zmap (psi0 S) - Work.ATOM.zmap (psi2 S)) ≫
        Work.ATOM.qred S (Work.ATOM.levelData S).s₀ := by
  rw [EA_whiskerLeft_zmap S (Work.ATOM.T' S) (Work.ATOM.pr₂T S), Category.assoc,
    Work.ATOM.F_spec S]
  exact h3pl_hPr2 S

/-- The right half of the pullback. -/
private lemma h3pl_hR :
    (Work.ATOM.EA (Work.ATOM.T' S) ≫
        (MonoidalCategoryStruct.whiskerLeft LightCondensed.P
          (Work.ATOM.zmap (Work.ATOM.betaT S)))) ≫ Work.ATOM.F S =
      (Work.ATOM.zmap (psi3 S) - Work.ATOM.zmap (psi4 S)) ≫
        Work.ATOM.qred S (Work.ATOM.levelData S).s₀ := by
  rw [EA_whiskerLeft_zmap S (Work.ATOM.T' S) (Work.ATOM.betaT S), Category.assoc,
    Work.ATOM.F_spec S]
  exact h3pl_hBeta S

/-- The elementary rearrangement `(A − B) ≫ q − (C − D) ≫ q = (A − B − C + D) ≫ q`. -/
private lemma h3pl_sub_alg {C : Type*} [Category C] [Preadditive C] {W X Y : C}
    (A B D' E : W ⟶ X) (q : X ⟶ Y) :
    (A - B) ≫ q - (D' - E) ≫ q = (A - B - D' + E) ≫ q := by
  simp only [Preadditive.sub_comp, Preadditive.add_comp]
  abel

/-- The pullback of the left hand side.
(The proof is taken from `Submission/Work/ATOM/ZS/h3_pullback_left.lean`, supplied in parallel.) -/
theorem pullback_left :
    Work.ATOM.zmap (cMap S) ≫
        (Work.ATOM.EApp ≫ Work.ATOM.m S ≫ Work.ATOM.F S) =
      (Work.ATOM.zmap (psi0 S) - Work.ATOM.zmap (psi2 S) - Work.ATOM.zmap (psi3 S) +
        Work.ATOM.zmap (psi4 S)) ≫ Work.ATOM.qred S (Work.ATOM.levelData S).s₀ := by
  have hkey : Work.ATOM.zmap (cMap S) ≫ (Work.ATOM.EApp ≫ Work.ATOM.m S) =
      Work.ATOM.EA (Work.ATOM.T' S) ≫
        (MonoidalCategoryStruct.whiskerLeft LightCondensed.P
          (Work.ATOM.zmap (Work.ATOM.pr₂T S) - Work.ATOM.zmap (Work.ATOM.betaT S))) := by
    have hstep : Work.ATOM.zmap (cMap S) ≫
          Work.ATOM.EA LightProfinite.NatUnionInfty =
        Work.ATOM.EA (Work.ATOM.T' S) ≫
          (MonoidalCategoryStruct.whiskerLeft LightCondensed.P
            (Work.ATOM.zmap (Work.ATOM.tProj S))) :=
      (EA_whiskerLeft_zmap LightProfinite.NatUnionInfty (Work.ATOM.T' S) (Work.ATOM.tProj S)).symm
    calc Work.ATOM.zmap (cMap S) ≫ (Work.ATOM.EApp ≫ Work.ATOM.m S)
        = Work.ATOM.zmap (cMap S) ≫
            (Work.ATOM.EA LightProfinite.NatUnionInfty ≫
              (MonoidalCategoryStruct.whiskerLeft LightCondensed.P (Work.ATOM.gBig S))) := by
          rw [EApp_comp_m S]
      _ = (Work.ATOM.zmap (cMap S) ≫
              Work.ATOM.EA LightProfinite.NatUnionInfty) ≫
            (MonoidalCategoryStruct.whiskerLeft LightCondensed.P (Work.ATOM.gBig S)) := by
          simp only [Category.assoc]
      _ = (Work.ATOM.EA (Work.ATOM.T' S) ≫
            (MonoidalCategoryStruct.whiskerLeft LightCondensed.P
              (Work.ATOM.zmap (Work.ATOM.tProj S)))) ≫
            (MonoidalCategoryStruct.whiskerLeft LightCondensed.P (Work.ATOM.gBig S)) := by
          rw [hstep]
      _ = Work.ATOM.EA (Work.ATOM.T' S) ≫
            (MonoidalCategoryStruct.whiskerLeft LightCondensed.P
              (Work.ATOM.zmap (Work.ATOM.tProj S) ≫ Work.ATOM.gBig S)) := by
          rw [Category.assoc, ← MonoidalCategory.whiskerLeft_comp]
      _ = Work.ATOM.EA (Work.ATOM.T' S) ≫
            (MonoidalCategoryStruct.whiskerLeft LightCondensed.P (Work.ATOM.gHat S)) := by
          rw [Work.ATOM.gBig_spec S]
      _ = Work.ATOM.EA (Work.ATOM.T' S) ≫
            (MonoidalCategoryStruct.whiskerLeft LightCondensed.P
              (Work.ATOM.zmap (Work.ATOM.pr₂T S) - Work.ATOM.zmap (Work.ATOM.betaT S))) := by
          unfold Work.ATOM.gHat
          rfl
  calc Work.ATOM.zmap (cMap S) ≫
        (Work.ATOM.EApp ≫ Work.ATOM.m S ≫ Work.ATOM.F S)
      = (Work.ATOM.zmap (cMap S) ≫ (Work.ATOM.EApp ≫ Work.ATOM.m S)) ≫
          Work.ATOM.F S := by
        simp only [Category.assoc]
    _ = (Work.ATOM.EA (Work.ATOM.T' S) ≫
          (MonoidalCategoryStruct.whiskerLeft LightCondensed.P
            (Work.ATOM.zmap (Work.ATOM.pr₂T S) - Work.ATOM.zmap (Work.ATOM.betaT S)))) ≫
          Work.ATOM.F S := by
        rw [hkey]
    _ = (Work.ATOM.EA (Work.ATOM.T' S) ≫
          (MonoidalCategoryStruct.whiskerLeft LightCondensed.P
            (Work.ATOM.zmap (Work.ATOM.pr₂T S)))) ≫ Work.ATOM.F S -
        (Work.ATOM.EA (Work.ATOM.T' S) ≫
          (MonoidalCategoryStruct.whiskerLeft LightCondensed.P
            (Work.ATOM.zmap (Work.ATOM.betaT S)))) ≫ Work.ATOM.F S := by
        rw [Work.ATOM.Toolkit.whiskerLeft_sub, Preadditive.comp_sub, Preadditive.sub_comp]
    _ = (Work.ATOM.zmap (psi0 S) - Work.ATOM.zmap (psi2 S)) ≫
          Work.ATOM.qred S (Work.ATOM.levelData S).s₀ -
        (Work.ATOM.zmap (psi3 S) - Work.ATOM.zmap (psi4 S)) ≫
          Work.ATOM.qred S (Work.ATOM.levelData S).s₀ := by
        rw [h3pl_hL S, h3pl_hR S]
    _ = (Work.ATOM.zmap (psi0 S) - Work.ATOM.zmap (psi2 S) -
          Work.ATOM.zmap (psi3 S) + Work.ATOM.zmap (psi4 S)) ≫
          Work.ATOM.qred S (Work.ATOM.levelData S).s₀ :=
        h3pl_sub_alg _ _ _ _ _

/-- Functoriality of `zmap = ℤ[-]`, restated locally. -/
private lemma zmap_comp_local {A B C : LightProfinite.{0}} (f : A ⟶ B) (g : B ⟶ C) :
    Work.ATOM.zmap (f ≫ g) = Work.ATOM.zmap f ≫ Work.ATOM.zmap g := by
  simp only [Work.ATOM.zmap, Functor.comp_map, Functor.map_comp]

/-- **The pullback of the right hand side of `h₃`**, in the abstract form used by
`pullback_right`: `cM` is a map `(ℕ∪∞) × T' ⟶ (ℕ∪∞)²` playing the role of `𝟙 ⊗ π`, `Ph` a map
`(ℕ∪∞) × T' ⟶ T'` playing the role of `Φ`, and `p0`, `p1` maps `(ℕ∪∞) × T' ⟶ S` playing the roles
of `ψ₀ = Φ ≫ pr₂T` and `ψ₁ = Φ ≫ betaT`, subject to the characterising equations `hc`, `h0`, `h1`.
(The proof is taken from `Submission/Work/ATOM/ZS/h3_pullback_right.lean`, supplied in parallel.) -/
theorem pullback_right_gen
    (cM : Work.ATOM.NS (Work.ATOM.T' S) ⟶ Work.ATOM.NS2)
    (Ph : Work.ATOM.NS (Work.ATOM.T' S) ⟶ Work.ATOM.T' S)
    (p0 p1 : Work.ATOM.NS (Work.ATOM.T' S) ⟶ S)
    (hc : cM ≫ Work.ATOM.phiP S = Ph ≫ Work.ATOM.tProj S)
    (h0 : p0 = Ph ≫ Work.ATOM.pr₂T S)
    (h1 : p1 = Ph ≫ Work.ATOM.betaT S) :
    Work.ATOM.zmap cM ≫
        (Work.ATOM.EApp ≫ Work.ATOM.FP S ≫ Work.ATOM.gRed S) =
      (Work.ATOM.zmap p0 - Work.ATOM.zmap p1) ≫
        Work.ATOM.qred S (Work.ATOM.levelData S).s₀ := by
  have hFP : Work.ATOM.EApp ≫ Work.ATOM.FP S =
      Work.ATOM.zmap (Work.ATOM.phiP S) ≫ LightCondensed.P_proj := by
    rw [Work.ATOM.FP_spec, Work.ATOM.FPsection]
  have hz : Work.ATOM.zmap cM ≫ Work.ATOM.zmap (Work.ATOM.phiP S) =
      Work.ATOM.zmap (Ph ≫ Work.ATOM.tProj S) := by
    rw [← hc, ← zmap_comp_local]
  have hg : Work.ATOM.zmap (Ph ≫ Work.ATOM.tProj S) ≫ Work.ATOM.gBig S =
      Work.ATOM.zmap p0 - Work.ATOM.zmap p1 := by
    rw [zmap_comp_local, Category.assoc (Work.ATOM.zmap Ph) (Work.ATOM.zmap (Work.ATOM.tProj S))
      (Work.ATOM.gBig S), Work.ATOM.gBig_spec]
    change Work.ATOM.zmap Ph ≫
        (Work.ATOM.zmap (Work.ATOM.pr₂T S) - Work.ATOM.zmap (Work.ATOM.betaT S)) =
      Work.ATOM.zmap p0 - Work.ATOM.zmap p1
    rw [Preadditive.comp_sub, ← zmap_comp_local, ← zmap_comp_local, ← h0, ← h1]
  have key : Work.ATOM.zmap cM ≫
        (Work.ATOM.EApp ≫ (Work.ATOM.FP S ≫ Work.ATOM.g S)) =
      Work.ATOM.zmap p0 - Work.ATOM.zmap p1 := by
    calc Work.ATOM.zmap cM ≫ (Work.ATOM.EApp ≫ (Work.ATOM.FP S ≫ Work.ATOM.g S))
        = Work.ATOM.zmap cM ≫
            ((Work.ATOM.EApp ≫ Work.ATOM.FP S) ≫ Work.ATOM.g S) := by
          rw [← Category.assoc (Work.ATOM.EApp) (Work.ATOM.FP S) (Work.ATOM.g S)]
      _ = Work.ATOM.zmap cM ≫
            ((Work.ATOM.zmap (Work.ATOM.phiP S) ≫ LightCondensed.P_proj) ≫
              Work.ATOM.g S) := by
          rw [hFP]
      _ = Work.ATOM.zmap cM ≫ (Work.ATOM.zmap (Work.ATOM.phiP S) ≫
            (LightCondensed.P_proj ≫ Work.ATOM.g S)) := by
          rw [Category.assoc (Work.ATOM.zmap (Work.ATOM.phiP S)) LightCondensed.P_proj
            (Work.ATOM.g S)]
      _ = Work.ATOM.zmap cM ≫
            (Work.ATOM.zmap (Work.ATOM.phiP S) ≫ Work.ATOM.gBig S) := by
          rw [Work.ATOM.g_spec]
      _ = (Work.ATOM.zmap cM ≫ Work.ATOM.zmap (Work.ATOM.phiP S)) ≫
            Work.ATOM.gBig S := by
          rw [← Category.assoc (Work.ATOM.zmap cM) (Work.ATOM.zmap (Work.ATOM.phiP S))
            (Work.ATOM.gBig S)]
      _ = Work.ATOM.zmap (Ph ≫ Work.ATOM.tProj S) ≫ Work.ATOM.gBig S := by
          rw [hz]
      _ = Work.ATOM.zmap p0 - Work.ATOM.zmap p1 := hg
  calc Work.ATOM.zmap cM ≫ (Work.ATOM.EApp ≫ (Work.ATOM.FP S ≫ Work.ATOM.gRed S))
      = Work.ATOM.zmap cM ≫ (Work.ATOM.EApp ≫ (Work.ATOM.FP S ≫
          (Work.ATOM.g S ≫ Work.ATOM.qred S (Work.ATOM.levelData S).s₀))) := rfl
    _ = Work.ATOM.zmap cM ≫ (Work.ATOM.EApp ≫ ((Work.ATOM.FP S ≫ Work.ATOM.g S) ≫
          Work.ATOM.qred S (Work.ATOM.levelData S).s₀)) := by
          rw [← Category.assoc (Work.ATOM.FP S) (Work.ATOM.g S)
            (Work.ATOM.qred S (Work.ATOM.levelData S).s₀)]
    _ = Work.ATOM.zmap cM ≫ ((Work.ATOM.EApp ≫ (Work.ATOM.FP S ≫ Work.ATOM.g S)) ≫
          Work.ATOM.qred S (Work.ATOM.levelData S).s₀) := by
          rw [← Category.assoc (Work.ATOM.EApp) (Work.ATOM.FP S ≫ Work.ATOM.g S)
            (Work.ATOM.qred S (Work.ATOM.levelData S).s₀)]
    _ = (Work.ATOM.zmap cM ≫ (Work.ATOM.EApp ≫ (Work.ATOM.FP S ≫ Work.ATOM.g S))) ≫
          Work.ATOM.qred S (Work.ATOM.levelData S).s₀ := by
          rw [← Category.assoc (Work.ATOM.zmap cM)
            (Work.ATOM.EApp ≫ (Work.ATOM.FP S ≫ Work.ATOM.g S))
            (Work.ATOM.qred S (Work.ATOM.levelData S).s₀)]
    _ = (Work.ATOM.zmap p0 - Work.ATOM.zmap p1) ≫
          Work.ATOM.qred S (Work.ATOM.levelData S).s₀ := by
          rw [key]

/-- The pullback of the right hand side. -/
theorem pullback_right :
    Work.ATOM.zmap (cMap S) ≫
        (Work.ATOM.EApp ≫ Work.ATOM.FP S ≫ Work.ATOM.gRed S) =
      (Work.ATOM.zmap (psi0 S) - Work.ATOM.zmap (psi1 S)) ≫
        Work.ATOM.qred S (Work.ATOM.levelData S).s₀ :=
  pullback_right_gen S (cMap S) (Phi S) (psi0 S) (psi1 S)
    (Phi_tProj S).symm (Phi_pr₂T S).symm rfl

/-! ## The three pieces of the cover of `(ℕ∪∞) × T'` -/

/-- The piece where `ψ₁ = ψ₃` and `ψ₄ = ψ₂` (this contains the points with `φ_P(k,j) = j`). -/
def C1set : Set ↥(X S) := {x | psi1 S x = psi3 S x} ∩ {x | psi4 S x = psi2 S x}

/-- The piece where `ψ₂ = ψ₀ = ψ₁` and `ψ₄ = ψ₃` (the points with `φ_P(k,j) = ∞` and
`k > n(j)` finite, or `k = ∞`). -/
def C2set : Set ↥(X S) :=
  ({x | psi2 S x = psi0 S x} ∩ {x | psi4 S x = psi3 S x}) ∩ {x | psi1 S x = psi0 S x}

/-- The piece `{j = ∞} ⊆ (ℕ∪∞) × T'`. -/
def C3set : Set ↥(X S) := {x | (Work.ATOM.tProj S) x.2 = (∞ : ↥LightProfinite.NatUnionInfty)}

lemma isClosed_C1set : IsClosed (C1set S) := by
  have h1 : Continuous (fun x : ↥(X S) => psi1 S x) :=
    (ConcreteCategory.hom (psi1 S)).continuous_toFun
  have h2 : Continuous (fun x : ↥(X S) => psi3 S x) :=
    (ConcreteCategory.hom (psi3 S)).continuous_toFun
  have h3 : Continuous (fun x : ↥(X S) => psi4 S x) :=
    (ConcreteCategory.hom (psi4 S)).continuous_toFun
  have h4 : Continuous (fun x : ↥(X S) => psi2 S x) :=
    (ConcreteCategory.hom (psi2 S)).continuous_toFun
  exact (isClosed_eq h1 h2).inter (isClosed_eq h3 h4)

lemma isClosed_C2set : IsClosed (C2set S) := by
  have h1 : Continuous (fun x : ↥(X S) => psi2 S x) :=
    (ConcreteCategory.hom (psi2 S)).continuous_toFun
  have h0 : Continuous (fun x : ↥(X S) => psi0 S x) :=
    (ConcreteCategory.hom (psi0 S)).continuous_toFun
  have h3 : Continuous (fun x : ↥(X S) => psi3 S x) :=
    (ConcreteCategory.hom (psi3 S)).continuous_toFun
  have h4 : Continuous (fun x : ↥(X S) => psi4 S x) :=
    (ConcreteCategory.hom (psi4 S)).continuous_toFun
  have h1' : Continuous (fun x : ↥(X S) => psi1 S x) :=
    (ConcreteCategory.hom (psi1 S)).continuous_toFun
  exact ((isClosed_eq h1 h0).inter (isClosed_eq h4 h3)).inter (isClosed_eq h1' h0)

lemma isClosed_C3set : IsClosed (C3set S) := by
  show IsClosed ((fun x : ↥(X S) => (Work.ATOM.tProj S) x.2) ⁻¹'
    ({(∞ : ↥LightProfinite.NatUnionInfty)} : Set ↥LightProfinite.NatUnionInfty))
  exact IsClosed.preimage
    ((ConcreteCategory.hom (Work.ATOM.tProj S)).continuous_toFun.comp continuous_snd)
    isClosed_singleton

instance : CompactSpace ↥(C1set S) :=
  isCompact_iff_compactSpace.mp (isClosed_C1set S).isCompact
instance : CompactSpace ↥(C2set S) :=
  isCompact_iff_compactSpace.mp (isClosed_C2set S).isCompact
instance : CompactSpace ↥(C3set S) :=
  isCompact_iff_compactSpace.mp (isClosed_C3set S).isCompact

/-- The first piece of the cover. -/
def C1 : LightProfinite.{0} := LightProfinite.of ↥(C1set S)
/-- The second piece of the cover. -/
def C2 : LightProfinite.{0} := LightProfinite.of ↥(C2set S)
/-- The third piece of the cover. -/
def C3 : LightProfinite.{0} := LightProfinite.of ↥(C3set S)

/-- The inclusion of the first piece. -/
def c1 : C1 S ⟶ X S := ConcreteCategory.ofHom ⟨Subtype.val, continuous_subtype_val⟩
/-- The inclusion of the second piece. -/
def c2 : C2 S ⟶ X S := ConcreteCategory.ofHom ⟨Subtype.val, continuous_subtype_val⟩
/-- The inclusion of the third piece. -/
def c3 : C3 S ⟶ X S := ConcreteCategory.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-! ## The three pieces: pointwise helpers

The following lemmas are the content of `Submission/Work/ATOM/ZS/h3_cover_defs.lean`,
`h3_cover_c1.lean`, `h3_cover_c2_fin.lean` and `h3_cover_c2_infty.lean`, supplied in parallel; they
are reproduced here so that `h_three` depends on nothing but the arguments on this file's level. -/

/-- `ψ₀(k,(j,u)) = u`. -/
@[simp] lemma h3_psi0_apply {S : LightProfinite.{0}} [Infinite S] (x : ↥(X S)) :
    psi0 S x = x.2.1.2 := rfl

/-- `ψ₁(k,(j,u)) = β(φ_P(k,j), u)`. -/
@[simp] lemma h3_psi1_apply {S : LightProfinite.{0}} [Infinite S] (x : ↥(X S)) :
    psi1 S x = Work.ATOM.betaFun S (Work.ATOM.phiPFun S (x.1, x.2.1.1), x.2.1.2) := rfl

/-- `ψ₂(k,(j,u)) = ẽ(k,u)`. -/
@[simp] lemma h3_psi2_apply {S : LightProfinite.{0}} [Infinite S] (x : ↥(X S)) :
    psi2 S x = Work.ATOM.ePredFun S (x.1, x.2.1.2) := rfl

/-- `ψ₃(k,(j,u)) = β(j,u)`. -/
@[simp] lemma h3_psi3_apply {S : LightProfinite.{0}} [Infinite S] (x : ↥(X S)) :
    psi3 S x = Work.ATOM.betaFun S (x.2.1.1, x.2.1.2) := rfl

/-- `ψ₄(k,(j,u)) = ẽ(k,β(j,u))`. -/
@[simp] lemma h3_psi4_apply {S : LightProfinite.{0}} [Infinite S] (x : ↥(X S)) :
    psi4 S x = Work.ATOM.ePredFun S (x.1, Work.ATOM.betaFun S (x.2.1.1, x.2.1.2)) := rfl

/-- A point is in `C1set` iff `ψ₁ = ψ₃` and `ψ₄ = ψ₂` there. -/
lemma h3_mem_C1set_iff {S : LightProfinite.{0}} [Infinite S] (x : ↥(X S)) :
    x ∈ C1set S ↔ psi1 S x = psi3 S x ∧ psi4 S x = psi2 S x := Iff.rfl

/-- A point is in `C2set` iff `ψ₂ = ψ₀`, `ψ₄ = ψ₃` and `ψ₁ = ψ₀` there. -/
lemma h3_mem_C2set_iff {S : LightProfinite.{0}} [Infinite S] (x : ↥(X S)) :
    x ∈ C2set S ↔ (psi2 S x = psi0 S x ∧ psi4 S x = psi3 S x) ∧ psi1 S x = psi0 S x :=
  Iff.rfl

/-- A point is in `C3set` iff its `T'`-coordinate lies over `∞`. -/
lemma h3_mem_C3set_iff {S : LightProfinite.{0}} [Infinite S] (x : ↥(X S)) :
    x ∈ C3set S ↔ x.2.1.1 = (OnePoint.infty : ↥LightProfinite.NatUnionInfty) := Iff.rfl

/-- Membership in `C1set` gives membership in the range of the inclusion `c1`. -/
lemma h3_mem_range_c1 {S : LightProfinite.{0}} [Infinite S] {x : ↥(X S)} (h : x ∈ C1set S) :
    x ∈ Set.range (c1 S) := ⟨⟨x, h⟩, rfl⟩

/-- Membership in `C2set` gives membership in the range of the inclusion `c2`. -/
lemma h3_mem_range_c2 {S : LightProfinite.{0}} [Infinite S] {x : ↥(X S)} (h : x ∈ C2set S) :
    x ∈ Set.range (c2 S) := ⟨⟨x, h⟩, rfl⟩

/-- Membership in `C3set` gives membership in the range of the inclusion `c3`. -/
lemma h3_mem_range_c3 {S : LightProfinite.{0}} [Infinite S] {x : ↥(X S)} (h : x ∈ C3set S) :
    x ∈ Set.range (c3 S) := ⟨⟨x, h⟩, rfl⟩

/-- Element form of the composition rule `e_a ≫ e_b = e_{min a b}` of `LevelData.e_comp`:
`e_b (e_a x) = e_{min a b} x`. -/
lemma h3_e_comp_apply {S : LightProfinite.{0}} [Infinite S] (a b : ℕ) (x : ↥S) :
    Work.ATOM.e S b (Work.ATOM.e S a x) = Work.ATOM.e S (min a b) x := by
  have h := ConcreteCategory.congr_hom ((Work.ATOM.levelData S).e_comp a b) x
  rw [ConcreteCategory.comp_apply] at h
  exact h

/-- `e_m` fixes `a j` as soon as `n(j) ≤ m` (the image of `e_m` contains `A_{n(j)}`). -/
lemma h3_e_a_of_le {S : LightProfinite.{0}} [Infinite S] {j m : ℕ} (h : Work.ATOM.lvl S j ≤ m) :
    Work.ATOM.e S m ((Work.ATOM.levelData S).a j) = (Work.ATOM.levelData S).a j := by
  have hA : (Work.ATOM.levelData S).a j ∈ Work.ATOM.A S (Work.ATOM.lvl S j) :=
    (Work.ATOM.levelData S).lv_mem _ (Work.ATOM.levelData_a_mem j)
  exact e_fix_of_mem_A_of_le S h hA

/-- Every idempotent fixes the base point `s₀`. -/
lemma h3_e_s0 {S : LightProfinite.{0}} [Infinite S] (n : ℕ) :
    Work.ATOM.e S n ((Work.ATOM.levelData S).s₀) = (Work.ATOM.levelData S).s₀ :=
  (Work.ATOM.levelData S).e_fix n

/-- For a positive `m`, `ẽ(m,x) = e_{m-1} x`. -/
lemma h3_ePredFun_of_pos {S : LightProfinite.{0}} [Infinite S] (m : ℕ) (hm : 0 < m) (x : ↥S) :
    Work.ATOM.ePredFun S ((m : ℕ∪{∞}), x) = Work.ATOM.e S (m - 1) x := by
  rw [show ((m : ℕ∪{∞})) = (((m - 1 + 1 : ℕ)) : ℕ∪{∞}) by rw [Nat.sub_add_cancel hm]]
  rw [Work.ATOM.ePredFun_succ]

/-- `β(j, a j) = e_{n(j)-1} (a j)` when `n(j) ≠ 0`. -/
lemma h3_betaFun_a_of_ne_zero {S : LightProfinite.{0}} [Infinite S] (j : ℕ)
    (h : Work.ATOM.lvl S j ≠ 0) :
    Work.ATOM.betaFun S (((j : ℕ) : ℕ∪{∞}), (Work.ATOM.levelData S).a j) =
      Work.ATOM.e S (Work.ATOM.lvl S j - 1) ((Work.ATOM.levelData S).a j) := by
  rw [Work.ATOM.betaFun_lvl, if_neg h]

/-- `β(j, a j) = s₀` when `n(j) = 0`. -/
lemma h3_betaFun_a_of_eq_zero {S : LightProfinite.{0}} [Infinite S] (j : ℕ)
    (h : Work.ATOM.lvl S j = 0) :
    Work.ATOM.betaFun S (((j : ℕ) : ℕ∪{∞}), (Work.ATOM.levelData S).a j) =
      (Work.ATOM.levelData S).s₀ := by
  rw [Work.ATOM.betaFun_lvl, if_pos h]

/-- **The first piece of the cover: the points `x = (m,(l,u))` with `m ≤ n(l)`.** -/
theorem h3_cover_c1 (S : LightProfinite.{0}) [Infinite S] (x : ↥(X S)) (l m : ℕ)
    (hl : x.2.1.1 = ((l : ℕ) : ↥LightProfinite.NatUnionInfty))
    (hk : x.1 = ((m : ℕ) : ↥LightProfinite.NatUnionInfty)) (hm : m ≤ Work.ATOM.lvl S l) :
    x ∈ C1set S := by
  rw [h3_mem_C1set_iff]
  have hu : x.2.1.2 = (Work.ATOM.levelData S).a l :=
    Work.ATOM.tSet_second_eq (S := S) (j := l) x.2.2 hl
  constructor
  · rw [h3_psi1_apply, h3_psi3_apply, hk, hl, Work.ATOM.phiPFun_some_some_of_le hm]
  · rw [h3_psi4_apply, h3_psi2_apply, hk, hl, hu]
    by_cases hm0 : m = 0
    · subst hm0
      rw [Work.ATOM.ePredFun_zero, Work.ATOM.ePredFun_zero]
    · have hpos : 0 < m := Nat.pos_of_ne_zero hm0
      rw [h3_ePredFun_of_pos m hpos, h3_ePredFun_of_pos m hpos]
      have hlne : Work.ATOM.lvl S l ≠ 0 := by omega
      rw [h3_betaFun_a_of_ne_zero l hlne]
      rw [h3_e_comp_apply (Work.ATOM.lvl S l - 1) (m - 1) ((Work.ATOM.levelData S).a l),
        min_eq_right (by omega : m - 1 ≤ Work.ATOM.lvl S l - 1)]

/-- **The finite part of the second piece: `x = (m,(l,u))` with `n(l) < m`.** -/
theorem h3_cover_c2_fin (S : LightProfinite.{0}) [Infinite S] (x : ↥(X S)) (l m : ℕ)
    (hl : x.2.1.1 = ((l : ℕ) : ↥LightProfinite.NatUnionInfty))
    (hk : x.1 = ((m : ℕ) : ↥LightProfinite.NatUnionInfty)) (hm : Work.ATOM.lvl S l < m) :
    x ∈ C2set S := by
  rw [h3_mem_C2set_iff]
  have hu : x.2.1.2 = (Work.ATOM.levelData S).a l :=
    Work.ATOM.tSet_second_eq (S := S) x.2.2 hl
  have hlvl : Work.ATOM.lvl S l ≤ m - 1 := by omega
  have hlvl2 : Work.ATOM.lvl S l - 1 ≤ m - 1 := by omega
  have hm0 : 0 < m := by omega
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [h3_psi2_apply, h3_psi0_apply, hk, h3_ePredFun_of_pos m hm0, hu]
    exact h3_e_a_of_le hlvl
  · rw [h3_psi4_apply, h3_psi3_apply, hk, h3_ePredFun_of_pos m hm0, hl, hu]
    rcases eq_or_ne (Work.ATOM.lvl S l) 0 with h0 | h0
    · rw [h3_betaFun_a_of_eq_zero l h0, h3_e_s0 (m - 1)]
    · rw [h3_betaFun_a_of_ne_zero l h0,
        h3_e_comp_apply (Work.ATOM.lvl S l - 1) (m - 1) ((Work.ATOM.levelData S).a l),
        min_eq_left hlvl2]
  · rw [h3_psi1_apply, h3_psi0_apply, hk, hl, Work.ATOM.phiPFun_some_some_of_lt hm,
      Work.ATOM.betaFun_infty]

/-- **The `∞`-piece of the second case.** -/
theorem h3_cover_c2_infty (S : LightProfinite.{0}) [Infinite S] (x : ↥(X S))
    (hk : x.1 = OnePoint.infty) : x ∈ C2set S := by
  rw [h3_mem_C2set_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [h3_psi2_apply, h3_psi0_apply, hk, Work.ATOM.ePredFun_infty]
  · rw [h3_psi4_apply, h3_psi3_apply, hk, Work.ATOM.ePredFun_infty]
  · rw [h3_psi1_apply, h3_psi0_apply, hk, Work.ATOM.phiPFun_infty_left,
      Work.ATOM.betaFun_infty]

/-- **The cover of `(ℕ∪∞) × T'` by the three pieces.**  If `j = ∞` the point is in `C₃`; for
finite `j` we have either `k ≤ n(j)` (then `φ_P(k,j) = j` and the point is in `C₁`) or
`n(j) < k` (then `φ_P(k,j) = ∞` and the point is in `C₂`). -/
theorem cover_three : ∀ x : ↥(X S),
    x ∈ Set.range (c1 S) ∨ x ∈ Set.range (c2 S) ∨ x ∈ Set.range (c3 S) := by
  intro x
  by_cases hj : x.2.1.1 = (OnePoint.infty : ↥LightProfinite.NatUnionInfty)
  · exact Or.inr (Or.inr (h3_mem_range_c3 ((h3_mem_C3set_iff x).mpr hj)))
  · obtain ⟨l, hl⟩ := OnePoint.ne_infty_iff_exists.mp hj
    by_cases hk : x.1 = (OnePoint.infty : ↥LightProfinite.NatUnionInfty)
    · exact Or.inr (Or.inl (h3_mem_range_c2 (h3_cover_c2_infty S x hk)))
    · obtain ⟨m, hm⟩ := OnePoint.ne_infty_iff_exists.mp hk
      by_cases h : m ≤ Work.ATOM.lvl S l
      · exact Or.inl (h3_mem_range_c1 (h3_cover_c1 S x l m hl.symm hm.symm h))
      · exact Or.inr (Or.inl (h3_mem_range_c2
          (h3_cover_c2_fin S x l m hl.symm hm.symm (by omega))))

/-- **The algebraic normal form of the pulled-back combination.**  Precomposing the combination
`ψ₁ - ψ₂ - ψ₃ + ψ₄` with `zmap ι` and composing with `qred` is the same as taking the combination of
the four composites `ι ≫ ψᵢ` and composing with `qred`. -/
private lemma pullback_comb {Z : LightProfinite.{0}} (ι : Z ⟶ X S) :
    Work.ATOM.zmap ι ≫ ((Work.ATOM.zmap (psi1 S) - Work.ATOM.zmap (psi2 S) -
        Work.ATOM.zmap (psi3 S) + Work.ATOM.zmap (psi4 S)) ≫
          Work.ATOM.qred S (Work.ATOM.levelData S).s₀) =
      ((Work.ATOM.zmap (ι ≫ psi1 S) - Work.ATOM.zmap (ι ≫ psi2 S) -
        Work.ATOM.zmap (ι ≫ psi3 S) + Work.ATOM.zmap (ι ≫ psi4 S)) ≫
          Work.ATOM.qred S (Work.ATOM.levelData S).s₀) := by
  rw [← Category.assoc]
  congr 1
  rw [Preadditive.comp_add, Preadditive.comp_sub, Preadditive.comp_sub]
  rw [← zmap_comp, ← zmap_comp, ← zmap_comp, ← zmap_comp]

/-- The three pieces of the cover, as a `Fin 3`-indexed family. -/
def piece : Fin 3 → LightProfinite.{0}
  | 0 => C1 S
  | 1 => C2 S
  | 2 => C3 S

/-- The inclusions of the three pieces. -/
def incl : ∀ i : Fin 3, piece S i ⟶ X S
  | 0 => c1 S
  | 1 => c2 S
  | 2 => c3 S

/-- **The `∞`-piece identities.**  On any piece on which the `T'`-coordinate has `j = ∞`, we have
`ψ₁ = ψ₀`, `ψ₃ = ψ₀` and `ψ₄ = ψ₂`: `φ_P(k,∞) = ∞`, `ẽ(∞,u) = u` and `β(∞,u) = u`.
(The proof is taken from the file `Submission/Work/ATOM/ZS/h3_psi_eqs_of_infty.lean`, where it was
supplied in parallel.) -/
private lemma psi1_apply_eq_of_tProj_eq_infty (x : ↥(X S))
    (hx : (Work.ATOM.tProj S) x.2 = ∞) : psi1 S x = psi0 S x := by
  have htp : (Work.ATOM.tProj S) (Phi S x) = ∞ := by
    have h := congrArg (fun (f : X S ⟶ LightProfinite.NatUnionInfty) =>
      (ConcreteCategory.hom f) x) (Phi_tProj S)
    simp only [ConcreteCategory.comp_apply] at h
    rw [h]
    have hw : (LightProfinite.NatUnionInfty ◁ Work.ATOM.tProj S) x =
        (x.1, (Work.ATOM.tProj S) x.2) := rfl
    rw [hw]
    change Work.ATOM.phiPFun S (x.1, (Work.ATOM.tProj S) x.2) = ∞
    rw [hx]
    by_cases hk : x.1 = ∞
    · rw [hk, Work.ATOM.phiPFun_infty_left]
    · obtain ⟨k, hk'⟩ := OnePoint.ne_infty_iff_exists.mp hk
      rw [← hk', Work.ATOM.phiPFun_some_infty]
  have hpr2 : (Work.ATOM.pr₂T S) (Phi S x) = (Work.ATOM.pr₂T S) x.2 := by
    have h := congrArg (fun (f : X S ⟶ S) => (ConcreteCategory.hom f) x) (Phi_pr₂T S)
    simp only [ConcreteCategory.comp_apply] at h
    rw [h]
    have hw : (LightProfinite.NatUnionInfty ◁ Work.ATOM.pr₂T S) x =
        (x.1, (Work.ATOM.pr₂T S) x.2) := rfl
    rw [hw]
    change (x.1, (Work.ATOM.pr₂T S) x.2).2 = (Work.ATOM.pr₂T S) x.2
    rfl
  have hval : (Phi S x).1 = (∞, (Work.ATOM.pr₂T S) x.2) := by
    refine Prod.ext ?_ ?_
    · exact htp
    · exact hpr2
  change (ConcreteCategory.hom (Work.ATOM.betaT S)) (Phi S x) = psi0 S x
  change Work.ATOM.betaFun S (Phi S x).1 = (Work.ATOM.pr₂T S) x.2
  rw [hval, Work.ATOM.betaFun_infty]

/-- The underlying point of `x.2 ∈ T'` lies over `∞`, hence is `(∞, u)` with `u = pr₂T S x.2`. -/
private lemma val_eq_of_tProj_eq_infty (x : ↥(X S)) (hx : (Work.ATOM.tProj S) x.2 = ∞) :
    (x.2).1 = (∞, (Work.ATOM.pr₂T S) x.2) := by
  refine Prod.ext ?_ ?_
  · exact hx
  · rfl

/-- **`ψ₃ = ψ₀` over `j = ∞`.** -/
private lemma psi3_apply_eq_of_tProj_eq_infty (x : ↥(X S))
    (hx : (Work.ATOM.tProj S) x.2 = ∞) : psi3 S x = psi0 S x := by
  have hval := val_eq_of_tProj_eq_infty S x hx
  change (Work.ATOM.pr₂N S)
      ((x.1, (ConcreteCategory.hom (Work.ATOM.betaT S)) x.2) : ↥(Work.ATOM.NS S)) =
    (ConcreteCategory.hom (psi0 S)) x
  change (ConcreteCategory.hom (Work.ATOM.betaT S)) x.2 = (Work.ATOM.pr₂T S) x.2
  change Work.ATOM.betaFun S (x.2).1 = (Work.ATOM.pr₂T S) x.2
  rw [hval, Work.ATOM.betaFun_infty]

/-- **`ψ₄ = ψ₂` over `j = ∞`.** -/
private lemma psi4_apply_eq_of_tProj_eq_infty (x : ↥(X S))
    (hx : (Work.ATOM.tProj S) x.2 = ∞) : psi4 S x = psi2 S x := by
  have hval := val_eq_of_tProj_eq_infty S x hx
  have hbeta : Work.ATOM.betaFun S (x.2).1 = (Work.ATOM.pr₂T S) x.2 := by
    rw [hval, Work.ATOM.betaFun_infty]
  change (ConcreteCategory.hom (Work.ATOM.ePred S))
      ((x.1, Work.ATOM.betaFun S (x.2).1) : ↥(Work.ATOM.NS S)) =
    (ConcreteCategory.hom (Work.ATOM.ePred S))
      ((x.1, (Work.ATOM.pr₂T S) x.2) : ↥(Work.ATOM.NS S))
  rw [hbeta]

theorem psi_eqs_of_infty {Z : LightProfinite.{0}} (ι : Z ⟶ X S)
    (hι : ∀ z : ↥Z, (Work.ATOM.tProj S) (ι z).2 = (∞ : ↥LightProfinite.NatUnionInfty)) :
    ι ≫ psi1 S = ι ≫ psi0 S ∧ ι ≫ psi3 S = ι ≫ psi0 S ∧ ι ≫ psi4 S = ι ≫ psi2 S := by
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro z
    change psi1 S (ι z) = psi0 S (ι z)
    exact psi1_apply_eq_of_tProj_eq_infty S (ι z) (hι z)
  · apply ConcreteCategory.hom_ext
    intro z
    change psi3 S (ι z) = psi0 S (ι z)
    exact psi3_apply_eq_of_tProj_eq_infty S (ι z) (hι z)
  · apply ConcreteCategory.hom_ext
    intro z
    change psi4 S (ι z) = psi2 S (ι z)
    exact psi4_apply_eq_of_tProj_eq_infty S (ι z) (hι z)

/-- **Vanishing of the difference on the cover.** -/
theorem diff_eq_zero :
    (Work.ATOM.zmap (psi1 S) - Work.ATOM.zmap (psi2 S) - Work.ATOM.zmap (psi3 S) +
      Work.ATOM.zmap (psi4 S)) ≫ Work.ATOM.qred S (Work.ATOM.levelData S).s₀ = 0 := by
  have hcov := cover_three S
  refine zmap_ext_of_closed_cover _ _ 3 (piece S) (incl S) ?_ ?_
  · intro t
    rcases hcov t with h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  · intro i
    fin_cases i
    · -- the piece `C₁`: `ψ₁ = ψ₃` and `ψ₄ = ψ₂`
      change Work.ATOM.zmap (c1 S) ≫ ((Work.ATOM.zmap (psi1 S) - Work.ATOM.zmap (psi2 S) -
        Work.ATOM.zmap (psi3 S) + Work.ATOM.zmap (psi4 S)) ≫
          Work.ATOM.qred S (Work.ATOM.levelData S).s₀) = 0
      have e13 : c1 S ≫ psi1 S = c1 S ≫ psi3 S :=
        ConcreteCategory.hom_ext _ _ (fun y => y.2.1)
      have e42 : c1 S ≫ psi4 S = c1 S ≫ psi2 S :=
        ConcreteCategory.hom_ext _ _ (fun y => y.2.2)
      rw [pullback_comb S (c1 S), e13, e42, Preadditive.add_comp,
        Preadditive.sub_comp, Preadditive.sub_comp]
      abel
    · -- the piece `C₂`: `ψ₂ = ψ₀`, `ψ₄ = ψ₃` and `ψ₁ = ψ₀`
      change Work.ATOM.zmap (c2 S) ≫ ((Work.ATOM.zmap (psi1 S) - Work.ATOM.zmap (psi2 S) -
        Work.ATOM.zmap (psi3 S) + Work.ATOM.zmap (psi4 S)) ≫
          Work.ATOM.qred S (Work.ATOM.levelData S).s₀) = 0
      have e20 : c2 S ≫ psi2 S = c2 S ≫ psi0 S :=
        ConcreteCategory.hom_ext _ _ (fun y => y.2.1.1)
      have e43 : c2 S ≫ psi4 S = c2 S ≫ psi3 S :=
        ConcreteCategory.hom_ext _ _ (fun y => y.2.1.2)
      have e10 : c2 S ≫ psi1 S = c2 S ≫ psi0 S :=
        ConcreteCategory.hom_ext _ _ (fun y => y.2.2)
      rw [pullback_comb S (c2 S), e10, e20, e43, Preadditive.add_comp,
        Preadditive.sub_comp, Preadditive.sub_comp]
      abel
    · -- the piece `C₃`: `j = ∞`, so `ψ₁ = ψ₀`, `ψ₃ = ψ₀` and `ψ₄ = ψ₂`
      change Work.ATOM.zmap (c3 S) ≫ ((Work.ATOM.zmap (psi1 S) - Work.ATOM.zmap (psi2 S) -
        Work.ATOM.zmap (psi3 S) + Work.ATOM.zmap (psi4 S)) ≫
          Work.ATOM.qred S (Work.ATOM.levelData S).s₀) = 0
      have e10 : c3 S ≫ psi1 S = c3 S ≫ psi0 S := psi_eqs_of_infty S (c3 S) (fun y => y.2) |>.1
      have e30 : c3 S ≫ psi3 S = c3 S ≫ psi0 S := psi_eqs_of_infty S (c3 S) (fun y => y.2) |>.2.1
      have e42 : c3 S ≫ psi4 S = c3 S ≫ psi2 S := psi_eqs_of_infty S (c3 S) (fun y => y.2) |>.2.2
      rw [pullback_comb S (c3 S), e10, e30, e42, Preadditive.add_comp,
        Preadditive.sub_comp, Preadditive.sub_comp]
      abel

end HThree

/-- **Identity `h₃` of REFS/03 §1**: `(id_P ⊗ g) ≫ F = F_P ≫ g̃`, where
`Work.ATOM.m S = P ◁ g`.  On generators `(k, a_j)`: the left side is
`F(k, g(e_j)) = [a_j] - [e_{k-1} a_j] - [e_{n(j)-1}a_j] + [e_{k-1}e_{n(j)-1}a_j]` (using linearity of
`F` in the second variable), and the identity `e_{k-1} e_{n(j)-1} = e_{min(k-1,n(j)-1)}` together
with `Work.ATOM.ZS.e_fix_of_mem_A_of_le` (`e_{k-1} a_j = a_j` for `k > n(j)`) shows that this is
`[a_j] - [e_{n(j)-1}a_j]` when `k ≤ n(j)` and `0` when `k > n(j)`, which is
`F_P(k,j) ≫ g̃` by `Work.ATOM.phiP_some_some_of_le` / `Work.ATOM.phiP_some_some_of_lt`. -/
theorem h_three (S : LightProfinite.{0}) [Infinite S] :
    Work.ATOM.m S ≫ Work.ATOM.F S = Work.ATOM.FP S ≫ Work.ATOM.gRed S := by
  haveI hEpiE : Epi (Work.ATOM.EApp :
      Work.ATOM.zfree Work.ATOM.NS2 ⟶ Work.ATOM.tmul LightCondensed.P LightCondensed.P) :=
    epi_EApp
  haveI : Epi (Work.ATOM.tProj S) :=
    (LightProfinite.epi_iff_surjective _).mpr (Work.ATOM.tProj_surjective S)
  have hsurj : Function.Surjective (cMap S) := by
    rintro ⟨k, j⟩
    obtain ⟨p, hp⟩ := Work.ATOM.tProj_surjective S j
    exact ⟨(k, p), Prod.ext rfl hp⟩
  haveI : Epi (cMap S) := (LightProfinite.epi_iff_surjective _).mpr hsurj
  haveI : Epi (Work.ATOM.zmap (cMap S)) := inferInstance
  have hcancel : Work.ATOM.EApp ≫ (Work.ATOM.m S ≫ Work.ATOM.F S) =
      Work.ATOM.EApp ≫ (Work.ATOM.FP S ≫ Work.ATOM.gRed S) := by
    apply (cancel_epi (Work.ATOM.zmap (cMap S))).mp
    rw [pullback_left S, pullback_right S]
    have hsum : (Work.ATOM.zmap (psi0 S) - Work.ATOM.zmap (psi2 S) -
          Work.ATOM.zmap (psi3 S) + Work.ATOM.zmap (psi4 S)) =
        (Work.ATOM.zmap (psi0 S) - Work.ATOM.zmap (psi1 S)) +
          (Work.ATOM.zmap (psi1 S) - Work.ATOM.zmap (psi2 S) - Work.ATOM.zmap (psi3 S) +
            Work.ATOM.zmap (psi4 S)) := by abel
    rw [hsum, Preadditive.add_comp, diff_eq_zero S, add_zero]
  exact (cancel_epi (Work.ATOM.EApp)).mp hcancel

end

end Work.ATOM.ZS
